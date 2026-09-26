//! Running source text: top-level execution, `load`, packages, `eval`,
//! and error reporting.

use std::path::{Path, PathBuf};
use std::rc::Rc;

use calyx_syntax::ast::TypeExpr;
use calyx_syntax::{FileId, Span};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::compile::{Compiler, UnitOptions};
use crate::error::{ErrKind, ErrorInfo, RResult, RuntimeError};
use crate::interp::{Flow, Frame, Interp, Package};
use crate::intrinsics::{ArgSig, Imp, ParamSig, Signature};
use crate::ir::IntrinsicDefIR;
use crate::sym::Sym;
use crate::types::TypePat;
use crate::value::*;

/// Outcome of feeding source text to the interpreter.
pub enum ExecOutcome {
    Done,
    /// The text is an incomplete statement (more input needed).
    Incomplete,
    /// `quit` was executed.
    Quit(i32),
}

fn syntax_error(e: &calyx_syntax::ParseError) -> RuntimeError {
    // Magma reports every syntax error the same way; the parser's detail is
    // not shown (except for literals it rejects).
    let msg = if e.message == "Illegal zero denominator" { e.message.as_str() } else { "bad syntax" };
    ErrorInfo { kind: ErrKind::Syntax, span: Some(e.span), ..ErrorInfo::user(msg) }.into()
}

impl Interp {
    /// Parse and run source text at the top level, one statement at a time.
    /// With `allow_incomplete`, a truncated statement yields `Incomplete`
    /// instead of an error (for the REPL).
    pub fn execute(&mut self, src: &str, name: &str, allow_incomplete: bool) -> RResult<ExecOutcome> {
        self.execute_with(src, name, allow_incomplete, None)
    }

    /// Like `execute`, but an error in one statement is passed to `report`
    /// and the following statements still run, as at Magma's prompt (a
    /// syntax error still discards all of the text).
    pub fn execute_continuing(
        &mut self,
        src: &str,
        name: &str,
        allow_incomplete: bool,
        report: &mut dyn FnMut(&mut Interp, &RuntimeError),
    ) -> RResult<ExecOutcome> {
        self.execute_with(src, name, allow_incomplete, Some(report))
    }

    fn execute_with(
        &mut self,
        src: &str,
        name: &str,
        allow_incomplete: bool,
        mut report: Option<&mut dyn FnMut(&mut Interp, &RuntimeError)>,
    ) -> RResult<ExecOutcome> {
        let file = self.add_source(name, src);
        let (stmts, failed) = match calyx_syntax::parse_program(src, file) {
            Ok(s) => (s, None),
            Err(e) if e.incomplete && allow_incomplete => {
                self.sources.pop();
                return Ok(ExecOutcome::Incomplete);
            }
            // At top level the statements before a syntax error still run.
            Err(e) if report.is_some() => (calyx_syntax::parse_program_prefix(src, file).0, Some(e)),
            Err(e) => return Err(syntax_error(&e)),
        };
        for s in &stmts {
            self.check_package_updates()?;
            let r = self.run_top_statement(src, s);
            if let Some(c) = self.quit {
                return Ok(ExecOutcome::Quit(c));
            }
            if let Err(e) = r {
                match report.as_mut() {
                    Some(f) if !self.quit_on_error && e.kind != ErrKind::Interrupt => f(self, &e),
                    _ => return Err(e),
                }
            }
        }
        if let Some(e) = failed {
            return Err(syntax_error(&e));
        }
        Ok(ExecOutcome::Done)
    }

    fn run_top_statement(&mut self, src: &str, s: &calyx_syntax::ast::Stmt) -> RResult<()> {
        let code = {
            let forwards = self.forwards.clone();
            let compiler = Compiler::new(&forwards, src, UnitOptions::default());
            compiler.compile_unit(std::slice::from_ref(s), s.span).map_err(|e| RuntimeError::user(e.message).at(e.span))?
        };
        self.trace.clear();
        self.depth = 0;
        self.run_unit(&code).map(|_| ())
    }

    fn resolve_path(&self, name: &str) -> PathBuf {
        let expanded = expand_tilde(name);
        let p = Path::new(&expanded);
        if p.is_absolute() {
            return p.to_path_buf();
        }
        if let Some(cur) = self.file_stack.last() {
            if let Some(dir) = cur.parent() {
                let cand = dir.join(p);
                if cand.exists() {
                    return cand;
                }
            }
        }
        if p.exists() {
            return p.to_path_buf();
        }
        for dir in &self.search_path {
            let cand = dir.join(p);
            if cand.exists() {
                return cand;
            }
        }
        for dir in &self.libraries {
            let cand = self.library_root.join(dir).join(p);
            if cand.exists() {
                return cand;
            }
        }
        p.to_path_buf()
    }

    /// `load "file"`: run a file's statements at the top level.
    pub fn load_file(&mut self, name: &str) -> RResult<()> {
        let path = self.resolve_path(name);
        let text = std::fs::read_to_string(&path).map_err(|e| RuntimeError::runtime(format!("Could not open file \"{name}\": {e}")).in_context("load"))?;
        self.file_stack.push(path.clone());
        let saved_trace = std::mem::take(&mut self.trace);
        let saved_depth = self.depth;
        let r = self.execute(&text, &path.display().to_string(), false);
        self.trace = saved_trace;
        self.depth = saved_depth;
        self.file_stack.pop();
        match r? {
            ExecOutcome::Quit(c) => {
                self.quit = Some(c);
                Err(ErrorInfo { kind: ErrKind::Interrupt, ..ErrorInfo::runtime("quit") }.into())
            }
            _ => Ok(()),
        }
    }

    /// Attach a package file: its intrinsics become global.
    pub fn attach(&mut self, name: &str) -> RResult<()> {
        let path = self.resolve_path(name);
        let canon = path.canonicalize().unwrap_or(path.clone());
        self.intrinsics.remove_source(&canon);
        self.packages.retain(|p| p.path != canon);
        let text = std::fs::read_to_string(&canon).map_err(|e| RuntimeError::runtime(format!("Could not open package file \"{name}\": {e}")).in_context("Attach"))?;
        let mtime = std::fs::metadata(&canon).and_then(|m| m.modified()).ok();
        self.package_stack.push(FxHashMap::default());
        self.file_stack.push(canon.clone());
        let r = self.execute(&text, &canon.display().to_string(), false);
        self.file_stack.pop();
        let globals = self.package_stack.pop().unwrap_or_default();
        if let Err(e) = r {
            self.intrinsics.remove_source(&canon);
            return Err(e);
        }
        self.packages.push(Package { path: canon, globals, mtime });
        Ok(())
    }

    pub fn detach(&mut self, name: &str) -> RResult<()> {
        let path = self.resolve_path(name);
        let canon = path.canonicalize().unwrap_or(path);
        self.intrinsics.remove_source(&canon);
        self.packages.retain(|p| p.path != canon);
        Ok(())
    }

    /// Re-attach packages whose files changed since they were attached.
    fn check_package_updates(&mut self) -> RResult<()> {
        if !self.package_stack.is_empty() || self.packages.is_empty() {
            return Ok(());
        }
        let stale: Vec<PathBuf> = self
            .packages
            .iter()
            .filter(|p| {
                let now = std::fs::metadata(&p.path).and_then(|m| m.modified()).ok();
                now.is_some() && now != p.mtime
            })
            .map(|p| p.path.clone())
            .collect();
        for p in stale {
            self.attach(&p.display().to_string())?;
        }
        Ok(())
    }

    /// The globals of a package (attaching it if needed), for `import`.
    pub fn import_package(&mut self, name: &str) -> RResult<FxHashMap<Sym, Value>> {
        let path = self.resolve_path(name);
        let canon = path.canonicalize().unwrap_or(path);
        if !self.packages.iter().any(|p| p.path == canon) {
            self.attach(&canon.display().to_string())?;
        }
        Ok(self.packages.iter().find(|p| p.path == canon).map(|p| p.globals.clone()).unwrap_or_default())
    }

    /// Attach every package listed in a spec file.
    pub fn attach_spec(&mut self, name: &str, detach: bool) -> RResult<()> {
        let path = self.resolve_path(name);
        let text = std::fs::read_to_string(&path).map_err(|e| RuntimeError::runtime(format!("Could not open spec file \"{name}\": {e}")))?;
        let base = path.parent().map(|p| p.to_path_buf()).unwrap_or_default();
        let tokens: Vec<String> = text.replace('{', " { ").replace('}', " } ").split_whitespace().map(String::from).collect();
        let mut files = Vec::new();
        let mut i = 0;
        parse_spec(&tokens, &mut i, &base, &mut files, true)?;
        for f in files {
            let s = f.display().to_string();
            if let Some(spec) = s.strip_suffix("\u{1}") {
                self.attach_spec(spec, detach)?;
            } else if detach {
                self.detach(&s)?;
            } else {
                self.attach(&s)?;
            }
        }
        Ok(())
    }

    /// Run `eval` code: a lone expression, or statements ending in `return`.
    pub fn run_eval_source(&mut self, src: &str, mut readonly: FxHashSet<Sym>) -> RResult<Value> {
        // Global variables are visible to eval code but may not be assigned.
        readonly.extend(self.globals.iter().filter(|(_, v)| !v.is_undef()).map(|(k, _)| *k));
        // The code is shown in error reports ending with a semicolon; the
        // final statement may omit its own.
        let trimmed = src.trim_end();
        let shown = if trimmed.ends_with(';') { trimmed.to_string() } else { format!("{trimmed};") };
        let file = self.add_source("<eval>", &shown);
        // Mark errors as coming from eval code (the caller fills in where).
        let mark = |compile: bool| move |mut e: RuntimeError| {
            if e.eval_outer.is_none() && e.span.is_some_and(|s| s.file == file) {
                e.eval_outer = Some((Span::default(), compile));
            }
            e
        };
        if !trimmed.ends_with(';') {
            if let Ok(e) = calyx_syntax::parse_expression(trimmed, file) {
                let forwards = self.forwards.clone();
                let compiler = Compiler::new(&forwards, trimmed, UnitOptions { package: false, eval_readonly: Some(readonly) });
                let code = compiler.compile_expr_unit(&e).map_err(|e| RuntimeError::user(e.message).at(e.span)).map_err(mark(true))?;
                let saved = self.package_stack.len();
                let r = self.run_unit(&code).map_err(mark(false));
                self.package_stack.truncate(saved);
                return match r? {
                    Flow::Return(mut v) if !v.is_empty() => Ok(v.remove(0)),
                    _ => Err(RuntimeError::runtime("eval must return a value")),
                };
            }
        }
        let stmts = calyx_syntax::parse_program(&shown, file).map_err(|e| syntax_error(&e)).map_err(mark(true))?;
        let forwards = self.forwards.clone();
        let compiler = Compiler::new(&forwards, &shown, UnitOptions { package: false, eval_readonly: Some(readonly) });
        let span = Span::new(file, 0, shown.len());
        let code = compiler.compile_unit(&stmts, span).map_err(|e| RuntimeError::user(e.message).at(e.span)).map_err(mark(true))?;
        match self.run_unit(&code).map_err(mark(false))? {
            Flow::Return(mut v) if !v.is_empty() => Ok(v.remove(0)),
            _ => Err(RuntimeError::runtime("eval must return a value")),
        }
    }

    /// Register a user intrinsic from an `intrinsic` definition.
    pub fn define_intrinsic(&mut self, def: &Rc<IntrinsicDefIR>, f: &mut Frame) -> RResult<()> {
        let clo = match self.eval(&crate::ir::E { kind: crate::ir::Ex::Closure(def.code.clone(), def.captures.clone()), span: def.span }, f)? {
            Value::Func(c) => c,
            _ => unreachable!(),
        };
        let mut args = Vec::new();
        for ((ty, is_ref), p) in def.arg_types.iter().zip(&def.code.params) {
            let pat = match ty {
                Some(t) => self.type_expr_pat(t)?,
                None => TypePat::Any,
            };
            args.push(ArgSig { name: p.name.as_rc(), pat, is_ref: *is_ref, untyped: ty.is_none() && *is_ref });
        }
        let variadic = def.code.variadic;
        if variadic {
            // The last formal collects the extra arguments.
            args.pop();
        }
        let returns = match &def.returns {
            Some(rs) => {
                let mut v = Vec::new();
                for r in rs {
                    v.push(self.type_expr_pat(r)?);
                }
                Some(v)
            }
            None => None,
        };
        let params = def.code.opt_params.iter().map(|(n, _, _)| ParamSig { name: *n, default: Value::Undef, default_text: Rc::from("") }).collect();
        let doc = if &*def.doc == "\"" {
            // `{"}` repeats the previous intrinsic's comment.
            self.intrinsics.get(def.name).and_then(|v| v.last()).map(|s| s.doc.clone()).unwrap_or_default()
        } else {
            def.doc.clone()
        };
        let source = self.file_stack.last().cloned();
        let sig = Signature { args, variadic, returns, params, doc, imp: Imp::User(clo), generic: false, order: 0, source, package: true };
        self.intrinsics.add(def.name, sig);
        Ok(())
    }

    pub fn type_expr_pat(&self, t: &TypeExpr) -> RResult<TypePat> {
        let inner = |me: &Interp, x: &Option<Box<TypeExpr>>| -> RResult<Option<Box<TypePat>>> {
            match x {
                Some(b) => Ok(Some(Box::new(me.type_expr_pat(b)?))),
                None => Ok(None),
            }
        };
        let lookup = |n: &str| -> RResult<crate::types::TypeId> { self.types.lookup(n).ok_or_else(|| RuntimeError::user(format!("Unknown type '{n}'"))) };
        Ok(match t {
            TypeExpr::Any => TypePat::Any,
            TypeExpr::Named(n) => {
                let id = lookup(n)?;
                if id == crate::types::t::ANY { TypePat::Any } else { TypePat::Is(id) }
            }
            TypeExpr::Extended(n, ps) => {
                let mut v = Vec::new();
                for p in ps {
                    v.push(self.type_expr_pat(p)?);
                }
                TypePat::Ext(lookup(n)?, v)
            }
            TypeExpr::Seq(x) => TypePat::Seq(inner(self, x)?),
            TypeExpr::Set(x) => TypePat::Set(inner(self, x)?),
            TypeExpr::SetOrSeq(x) => TypePat::SetOrSeq(inner(self, x)?),
            TypeExpr::ISet(x) => TypePat::ISet(inner(self, x)?),
            TypeExpr::MSet(x) => TypePat::MSet(inner(self, x)?),
            TypeExpr::Tuple => TypePat::Tuple,
        })
    }

    /// `Name< ... | ... >` constructors other than the built-in ones.
    pub fn constructor(&mut self, name: Sym, left: Vec<Value>, right: Option<Vec<Value>>) -> RResult<Value> {
        let mut vals = self.constructor_multi(name, left, right, 1)?;
        Ok(vals.swap_remove(0))
    }

    /// A constructor with all its return values (`ideal< >` and `quo< >`
    /// also return a map); `nres` values are wanted (0 for all).
    pub fn constructor_multi(&mut self, name: Sym, left: Vec<Value>, right: Option<Vec<Value>>, nres: usize) -> RResult<Vec<Value>> {
        let rhs = right.clone().unwrap_or_default();
        let built_in = match (&*name.as_rc(), left.first()) {
            ("ideal", Some(base)) => self.ideal_constructor(base, &rhs)?,
            ("quo", Some(base)) => self.quo_constructor(base, &rhs, nres != 1)?,
            ("sub", Some(base)) => self.sub_constructor(base, &rhs)?,
            ("ext", Some(_)) => self.ext_constructor(&left, &rhs)?,
            ("ExtensionField", Some(_)) if left.len() == 1 => self.ext_constructor(&left, &rhs).map_err(|mut e| {
                if e.context.as_deref() == Some("ext< ... >") {
                    e.context = Some("ExtensionField< ... >".into());
                }
                e
            })?,
            _ => None,
        };
        if let Some(vals) = built_in {
            return Ok(vals);
        }
        match &*name.as_rc() {
            "__real_literal" => {
                let Some(Value::Str(s)) = left.first() else { unreachable!() };
                Ok(vec![crate::intrinsics::reals::real_literal(s)?])
            }
            "__affine_ring" => Ok(vec![self.call_intrinsic_named(Sym::new("PolynomialRing"), left)?]),
            "AffineAlgebra" if left.len() == 1 => Ok(vec![crate::intrinsics::poly_ideals::affine_algebra(self, &left[0], &rhs)?]),
            "__poly_var" => {
                let base = left.into_iter().next().unwrap_or_default();
                let p = self.call_intrinsic_named(Sym::new("PolynomialRing"), vec![base])?;
                Ok(vec![self.call_intrinsic_named(Sym::new("."), vec![p, Value::int(1)])?])
            }
            "sub" | "quo" | "ext" | "ideal" | "lideal" | "rideal" | "ncl" => {
                let ctor = match &*name.as_rc() {
                    "sub" => "SubConstructor",
                    "quo" => "QuoConstructor",
                    "ext" => "ExtConstructor",
                    _ => "IdealConstructor",
                };
                let Some(base) = left.first().cloned() else {
                    return Err(RuntimeError::runtime(format!("{name}< > needs a structure")));
                };
                let rest = Value::tuple(right.unwrap_or_default());
                let sym = Sym::new(ctor);
                if self.intrinsics.contains(sym) {
                    return Ok(vec![self.call_intrinsic_named(sym, vec![base, rest])?]);
                }
                Err(RuntimeError::runtime("No constructor provided for this type of object"))
            }
            _ => Err(RuntimeError::runtime(format!("Unknown constructor '{name}< >'"))),
        }
    }

    /// Render an error the way the REPL shows it: the source line with a
    /// caret, then the message.
    pub fn format_error(&self, e: &RuntimeError) -> String {
        use crate::error::ErrStyle;
        if e.kind == ErrKind::Interrupt {
            return "[Interrupted]\n".to_string();
        }
        if e.style == ErrStyle::Bare {
            return format!("{}\n", e.headline());
        }
        let mut out = String::new();
        if e.hidden {
            // An error in the code of a package intrinsic: the call frames,
            // and the package positions as the reference outputs hide them.
            out.push('\n');
            self.push_frames(&mut out, e);
            out.push_str("[Magma package traceback hidden]\n");
            out.push_str(&crate::print::wrap_text_output(&e.headline(), 0, 80));
            out.push('\n');
            if e.trailing_blank() {
                out.push('\n');
            }
            return out;
        }
        if let Some((outer, compile)) = e.eval_outer {
            // An error in eval code: where it is in that code, and where the
            // eval is.
            if compile {
                out.push_str(&self.location_block(outer, "", false));
                out.push('\n');
            } else {
                out.push('\n');
                self.push_frames(&mut out, e);
                out.push_str("[<string>:1](\n)\n");
            }
            if let Some(sp) = e.span {
                if let Some((line, col)) = self.source_line(sp.file, sp.lo as usize) {
                    out.push_str(&format!("In eval expression, line {}, column {}:\n", line + 1, col + 1));
                }
                out.push_str(&self.location_block(sp, "", false));
            }
            out.push_str("    Located in:\n");
            out.push_str(&self.location_block(outer, "    ", false));
            out.push_str(&crate::print::wrap_text_output(&e.headline(), 0, 80));
            out.push('\n');
            if compile || e.trailing_blank() {
                out.push('\n');
            }
            return out;
        }
        if e.style != ErrStyle::Object {
            out.push('\n');
        }
        self.push_frames(&mut out, e);
        if let Some(span) = e.span {
            out.push_str(&self.location_block(span, "", true));
        }
        out.push_str(&crate::print::wrap_text_output(&e.headline(), 0, 80));
        out.push('\n');
        if e.trailing_blank() {
            out.push('\n');
        }
        out
    }

    /// The active user functions, outermost first, with their arguments.
    fn push_frames(&self, out: &mut String, e: &RuntimeError) {
        for fr in e.trace.iter().rev() {
            let name = fr.name.as_rc();
            if name.is_empty() || name.starts_with('<') {
                continue;
            }
            out.push_str(&name);
            out.push_str("(\n");
            for (i, (n, v)) in fr.args.iter().enumerate() {
                out.push_str(&format!("    {n}: {v}"));
                out.push_str(if i + 1 < fr.args.len() { ",\n" } else { "\n" });
            }
            out.push_str(")\n");
        }
    }

    /// The source line of `span` (a window of it) with a caret under the
    /// position, each line starting with `indent`.
    pub(crate) fn location_block(&self, span: Span, indent: &str, with_file: bool) -> String {
        let mut out = String::new();
        let Some(src) = self.source(span.file) else { return out };
        let (line, col) = src.line_col(span.lo as usize);
        if with_file && !src.name.is_empty() && !src.name.starts_with('<') {
            out.push_str(&format!("{indent}In file \"{}\", line {}, column {}:\n", src.name, line + 1, col + 1));
        }
        let text = src.line_text(line);
        // A window of 75 characters of the line, moved right in steps of 55
        // until it contains the error position.
        let mut start = 0;
        while col >= start + 75 {
            start += 55;
        }
        let shown: String = text.chars().skip(start).take(75).collect();
        out.push_str(&format!("{indent}>> {shown}\n"));
        let caret_col: String = text.chars().skip(start).take(col - start).map(|c| if c == '\t' { '\t' } else { ' ' }).collect();
        out.push_str(&format!("{indent}   {caret_col}^\n"));
        out
    }

    pub fn source_line(&self, file: FileId, offset: usize) -> Option<(usize, usize)> {
        self.source(file).map(|s| s.line_col(offset))
    }
}

fn expand_tilde(s: &str) -> String {
    if let Some(rest) = s.strip_prefix("~/") {
        if let Ok(home) = std::env::var("HOME") {
            return format!("{home}/{rest}");
        }
    }
    s.to_string()
}

fn parse_spec(tokens: &[String], i: &mut usize, dir: &Path, out: &mut Vec<PathBuf>, top: bool) -> RResult<()> {
    if top {
        if tokens.get(*i).map(|s| s.as_str()) != Some("{") {
            return Err(RuntimeError::runtime("Spec file must start with '{'"));
        }
        *i += 1;
    }
    while *i < tokens.len() {
        let tok = tokens[*i].clone();
        *i += 1;
        match tok.as_str() {
            "}" => return Ok(()),
            "{" => return Err(RuntimeError::runtime("Unexpected '{' in spec file")),
            name => {
                if tokens.get(*i).map(|s| s.as_str()) == Some("{") {
                    *i += 1;
                    parse_spec(tokens, i, &dir.join(name), out, false)?;
                } else if let Some(spec) = name.strip_prefix('+') {
                    out.push(PathBuf::from(format!("{}\u{1}", dir.join(spec).display())));
                } else {
                    out.push(dir.join(name));
                }
            }
        }
    }
    Ok(())
}
