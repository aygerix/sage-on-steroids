//! Statement execution.

use std::rc::Rc;
use std::time::Instant;

use calyx_flint::Integer;

use super::{Flow, Frame, Interp};
use crate::error::{ErrKind, ErrorInfo, RResult, RuntimeError};
use crate::ir::*;
use crate::print::Level;
use crate::sym::Sym;
use crate::value::{ErrObj, Vals, Value};

impl Interp {
    pub fn exec_block(&mut self, stmts: &[S], f: &mut Frame) -> RResult<Flow> {
        for s in stmts {
            match self.exec(s, f)? {
                Flow::Normal => {}
                other => return Ok(other),
            }
        }
        Ok(Flow::Normal)
    }

    pub fn exec(&mut self, s: &S, f: &mut Frame) -> RResult<Flow> {
        self.exec_inner(s, f).map_err(|e| self.locate(e, s.span))
    }

    fn exec_inner(&mut self, s: &S, f: &mut Frame) -> RResult<Flow> {
        match &s.kind {
            St::Nop => {}
            St::Print(es, level, lone) => {
                let level = self.print_level(*level)?;
                let mut vals = Vec::with_capacity(es.len());
                // Every value returned by a call is printed (except trailing
                // unassigned ones).
                for e in es {
                    let mut vs = match &e.kind {
                        // As a statement of its own, an operation names its
                        // operator in errors, and a reduction does not.
                        Ex::Bin(op, a, b) if *lone && *op != calyx_syntax::ast::BinOp::Div => {
                            let (x, y) = (self.eval(a, f)?, self.eval(b, f)?);
                            vec![self.binop(*op, x, y).map_err(|err| crate::ops::op_error(*op, err, true).at(e.span))?]
                        }
                        // `x @ m;` names '@' when no map or intrinsic takes x.
                        Ex::Image(a, b) if *lone => {
                            let (x, m) = (self.eval(a, f)?, self.eval(b, f)?);
                            vec![self.image(&x, &m).map_err(|err| {
                                let bad = err.span.is_none() && err.context.is_none() && err.message.starts_with("Bad argument types");
                                (if bad { err.in_context("@") } else { err }).at(e.span)
                            })?]
                        }
                        // So is a failed requirement of `.`, as in `G.2;`.
                        Ex::Dot(a, b) if *lone => {
                            let (x, y) = (self.eval(a, f)?, self.eval(b, f)?);
                            vec![self.call_intrinsic_named(Sym::new("."), vec![x, y]).map_err(|mut err| {
                                if err.span.is_none() && err.require {
                                    err.context = Some(String::new());
                                }
                                err.at(e.span)
                            })?]
                        }
                        Ex::Reduce(op, a) if *lone => {
                            let v = self.eval(a, f)?;
                            let ctx = format!("&{}", op.intrinsic_name());
                            vec![self.reduce(*op, &v).map_err(|mut err| {
                                if err.span.is_none() && err.context.as_deref() == Some(&ctx) && err.message.starts_with("Operation not defined") {
                                    err.context = None;
                                }
                                err.at(e.span)
                            })?]
                        }
                        _ => self.eval_multi(e, f, 0)?,
                    };
                    while vs.len() > 1 && vs.last().is_some_and(|v| v.is_undef()) {
                        vs.pop();
                    }
                    vals.extend(vs);
                }
                self.print_values(&vals, level)?;
                self.push_previous(vals);
            }
            St::CallStmt(c, level) => {
                let level = self.print_level(*level)?;
                let results = self.call_expr(c, f, 0, true, s.span)?;
                if let Some(mut vals) = results {
                    while vals.len() > 1 && vals.last().is_some_and(|v| v.is_undef()) {
                        vals.pop();
                    }
                    self.print_values(&vals, level)?;
                    self.push_previous(vals.into_vec());
                }
            }
            St::Printf(es) => {
                let mut vals = Vec::new();
                for e in es {
                    vals.push(self.eval(e, f)?);
                }
                let text = self.sprintf(&vals)?;
                let text = crate::print::wrap_text_output(&text, 0, self.out.columns);
                self.out.write(&text);
            }
            St::Fprintf(file, es) => {
                let target = self.eval(file, f)?;
                let mut vals = Vec::new();
                for e in es {
                    vals.push(self.eval(e, f)?);
                }
                let text = self.sprintf(&vals)?;
                self.write_to_file_value(&target, &text)?;
            }
            St::Vprint(flag, level, es, is_printf) => {
                let need = match level {
                    Some(e) => self.eval_int_small(e, f)?,
                    None => 1,
                };
                if self.verbose_level(&flag.as_rc()) >= need {
                    let mut vals = Vec::new();
                    for e in es {
                        vals.push(self.eval(e, f)?);
                    }
                    if *is_printf {
                        let text = self.sprintf(&vals)?;
                        let text = crate::print::wrap_text_output(&text, 0, self.out.columns);
                        self.out.write(&text);
                    } else {
                        self.print_values(&vals, Level::Default)?;
                    }
                }
            }
            St::Assign(targets, value, at) => {
                if targets.len() == 1 {
                    let v = self.eval(value, f).map_err(|e| match &value.kind {
                        // Copying an unassigned local fails in the assignment.
                        Ex::Local(_, name) => RuntimeError::statement(":=", format!("Variable '{name}' has not been initialized")).at(*at),
                        _ => e,
                    })?;
                    if v.is_undef() {
                        return Err(RuntimeError::user("Right hand side of assignment has no value"));
                    }
                    self.assign(&targets[0], v, f).map_err(|e| e.at(lv_err_span(&targets[0])))?;
                } else {
                    let vals = self.eval_multi(value, f, targets.len())?;
                    if vals.len() < targets.len() {
                        let msg = format!("Expected to assign {} value(s) but only computed {} value(s)", targets.len(), vals.len());
                        return Err(RuntimeError::statement(":=", msg).at(*at));
                    }
                    for (t, v) in targets.iter().zip(vals) {
                        if v.is_undef() {
                            self.unassign(t, f)?;
                        } else {
                            self.assign(t, v, f)?;
                        }
                    }
                }
            }
            St::OpAssign(target, op, value, at) => {
                let rhs = self.eval(value, f)?;
                self.op_assign(target, *op, rhs, f, *at)?;
            }
            St::GenAssign(targets, value, at) => {
                if let [(target, Some(names))] = &targets[..] {
                    let v = self.eval(value, f)?;
                    self.gen_assign(target, names, v, f)?;
                } else {
                    let vals = self.eval_multi(value, f, targets.len())?;
                    if vals.len() < targets.len() {
                        let msg = format!("Expected to assign {} value(s) but only computed {} value(s)", targets.len(), vals.len());
                        return Err(RuntimeError::statement(":=", msg).at(*at));
                    }
                    for ((t, names), v) in targets.iter().zip(vals) {
                        match names {
                            _ if v.is_undef() => self.unassign(t, f)?,
                            Some(names) => self.gen_assign(t, names, v, f)?,
                            None => self.assign(t, v, f)?,
                        }
                    }
                }
            }
            St::If(branches, else_) => {
                for (c, body) in branches {
                    if self.eval_cond(c, f, "if")? {
                        return self.exec_block(body, f);
                    }
                }
                if let Some(b) = else_ {
                    return self.exec_block(b, f);
                }
            }
            St::Case(scrut, arms, else_) => {
                let v = self.eval(scrut, f)?;
                for (vals, body) in arms {
                    for ve in vals {
                        let w = self.eval(ve, f)?;
                        if self.values_equal(&v, &w)? {
                            return self.exec_block(body, f);
                        }
                    }
                }
                if let Some(b) = else_ {
                    return self.exec_block(b, f);
                }
            }
            St::ForRange { var, from, to, by, body } => return self.for_range(var, from, to, by.as_ref(), body, f),
            St::ForIn { var, index, domain, random, body, var_span } => return self.for_in(var, index.as_ref(), domain, *random, body, f, *var_span),
            St::While(c, body) => {
                while self.eval_cond(c, f, "while")? {
                    self.check_interrupt()?;
                    match self.exec_block(body, f)? {
                        Flow::Normal | Flow::Continue(None) => {}
                        Flow::Break(None) => break,
                        other => return Ok(other),
                    }
                }
            }
            St::Repeat(body, c) => loop {
                self.check_interrupt()?;
                match self.exec_block(body, f)? {
                    Flow::Normal | Flow::Continue(None) => {}
                    Flow::Break(None) => break,
                    other => return Ok(other),
                }
                if self.eval_bool(c, f)? {
                    break;
                }
            },
            St::Break(l) => return Ok(Flow::Break(*l)),
            St::Continue(l) => return Ok(Flow::Continue(*l)),
            St::Return(es) => {
                let mut vals = Vals::new();
                for e in es {
                    if es.len() == 1 {
                        vals.extend(self.eval_multi(e, f, f.nresults.max(1))?);
                    } else {
                        vals.push(self.eval(e, f)?);
                    }
                }
                return Ok(Flow::Return(vals));
            }
            St::Error(cond, es) => {
                if let Some(c) = cond {
                    if !self.eval_bool(c, f)? {
                        return Ok(Flow::Normal);
                    }
                }
                let mut vals = Vec::new();
                for e in es {
                    vals.push(self.eval(e, f)?);
                }
                return Err(self.raise_user(vals)?);
            }
            St::Assert(level, e) => {
                if self.assertions >= *level as i64 && !self.eval_cond(e, f, "assert")? {
                    return Err(RuntimeError::statement("assert", "Assertion failed"));
                }
            }
            St::Require(c, es) => {
                if !self.eval_bool(c, f)? {
                    let mut vals = Vec::new();
                    for e in es {
                        vals.push(self.eval(e, f)?);
                    }
                    let msg = self.format_print_list(&vals, Level::Default)?;
                    return Err(RuntimeError::runtime(msg).at_caller().in_context(self.current_function_name()));
                }
            }
            St::RequireRange(v, lo, hi, name) => {
                let x = self.eval(v, f)?;
                let lo = self.eval(lo, f)?;
                let hi = self.eval(hi, f)?;
                let (Value::Int(x), Value::Int(lo), Value::Int(hi)) = (&x, &lo, &hi) else {
                    return Err(RuntimeError::runtime(format!("Argument '{name}' must be an integer")).in_context(self.current_function_name()));
                };
                if x < lo || x > hi {
                    let msg = format!("Argument '{name}' ({x}) should be in the range [{lo}..{hi}]");
                    return Err(RuntimeError::runtime(msg).at_caller().in_context(self.current_function_name()));
                }
            }
            St::RequireGe(v, lo, name) => {
                let x = self.eval(v, f)?;
                let lo = self.eval(lo, f)?;
                let (Value::Int(x), Value::Int(lo)) = (&x, &lo) else {
                    return Err(RuntimeError::runtime(format!("Argument '{name}' must be an integer")).in_context(self.current_function_name()));
                };
                if x < lo {
                    let msg = format!("Argument '{name}' ({x}) should be at least {lo}");
                    return Err(RuntimeError::runtime(msg).at_caller().in_context(self.current_function_name()));
                }
            }
            St::Try(body, var, handler) => {
                let depth = self.trace.len();
                match self.exec_block(body, f) {
                    Ok(flow) => return Ok(flow),
                    Err(e) if e.kind == ErrKind::Interrupt => return Err(e),
                    Err(e) => {
                        self.trace.truncate(depth);
                        if let Some(p) = var {
                            let obj = self.error_object(&e);
                            self.assign_place(*p, obj, f)?;
                        }
                        return self.exec_block(handler, f);
                    }
                }
            }
            St::Time(inner) => {
                let t0 = Instant::now();
                let c0 = crate::intrinsics::env::cpu_time();
                let r = self.exec(inner, f);
                let secs = crate::intrinsics::env::cpu_time() - c0;
                let real = t0.elapsed().as_secs_f64();
                self.out.ensure_newline();
                let line = self.time_string(secs, real);
                self.out.write(&format!("Time: {line}\n"));
                return r;
            }
            St::Vtime(flag, level, inner) => {
                let need = match level {
                    Some(e) => self.eval_int_small(e, f)?,
                    None => 1,
                };
                if self.verbose_level(&flag.as_rc()) >= need {
                    let t0 = Instant::now();
                    let c0 = crate::intrinsics::env::cpu_time();
                    let r = self.exec(inner, f);
                    let secs = crate::intrinsics::env::cpu_time() - c0;
                    let line = self.time_string(secs, t0.elapsed().as_secs_f64());
                    self.out.ensure_newline();
                    self.out.write(&format!("Time: {line}\n"));
                    return r;
                }
                return self.exec(inner, f);
            }
            St::Load(e, _interactive) => {
                let name = self.eval(e, f)?;
                let Value::Str(path) = name else {
                    return Err(RuntimeError::runtime("load requires a string"));
                };
                self.load_file(&path)?;
            }
            St::Import(file, names) => {
                let fv = self.eval(file, f)?;
                let Value::Str(path) = fv else {
                    return Err(RuntimeError::runtime("import requires a string"));
                };
                let globals = self.import_package(&path)?;
                for (name, place) in names {
                    let Some(v) = globals.get(name).cloned() else {
                        return Err(RuntimeError::user(format!("Identifier '{name}' is not assigned in \"{path}\"")));
                    };
                    self.assign_place(*place, v, f)?;
                }
            }
            St::Forward(names) => {
                for n in names {
                    self.forwards.insert(*n);
                }
            }
            St::Delete(lv) => self.delete(lv, f)?,
            St::DeclareType(name, elt, parents) => {
                let mut ps = Vec::new();
                for p in parents {
                    let Some(id) = self.types.lookup(&p.as_rc()) else {
                        return Err(RuntimeError::user(format!("Unknown type '{p}'")));
                    };
                    ps.push(id);
                }
                let id = self.types.declare_user(&name.as_rc(), ps);
                if let Some(e) = elt {
                    let eid = self.types.declare_user(&e.as_rc(), Vec::new());
                    self.types.set_elt_type(id, eid);
                }
            }
            St::DeclareAttributes(cat, names) => {
                let Some(id) = self.types.lookup(&cat.as_rc()) else {
                    return Err(RuntimeError::user(format!("Unknown type '{cat}'")));
                };
                for n in names {
                    self.types.add_attribute(id, *n);
                }
            }
            St::DeclareVerbose(name, max) => {
                let m = self.eval_int_small(max, f)?;
                let key: Rc<str> = name.as_rc();
                let cur = self.verbose.get(&key).map(|v| v.0).unwrap_or(0);
                self.verbose.insert(key, (cur, m));
            }
            St::Intrinsic(def) => self.define_intrinsic(def, f)?,
            St::Read(lv, prompt, int) => {
                let p = match prompt {
                    Some(e) => match self.eval(e, f)? {
                        Value::Str(s) => s.to_string(),
                        other => self.to_string_default(&other)?,
                    },
                    None => String::new(),
                };
                let line = self.read_input_line(&p)?;
                let v = if *int {
                    match Integer::parse(line.trim()) {
                        Some(i) => Value::Int(i),
                        None => return Err(RuntimeError::runtime("readi: input is not an integer")),
                    }
                } else {
                    Value::str(&line)
                };
                self.assign(lv, v, f)?;
            }
            St::Quit(code) => {
                let c = match code {
                    Some(e) => self.eval_int_small(e, f)? as i32,
                    None => 0,
                };
                self.quit = Some(c);
                return Err(ErrorInfo { kind: ErrKind::Interrupt, ..ErrorInfo::runtime("quit") }.into());
            }
            St::Clear => {
                self.globals.clear();
            }
            St::Save(path) => {
                let Value::Str(path) = self.eval(path, f)? else { return Err(RuntimeError::runtime("save filename must be a string")) };
                crate::intrinsics::io::save_workspace(self, &path)?;
            }
            St::Restore(path) => {
                let Value::Str(path) = self.eval(path, f)? else { return Err(RuntimeError::runtime("restore filename must be a string")) };
                crate::intrinsics::io::restore_workspace(self, &path)?;
            }
            St::Freeze => {}
        }
        Ok(Flow::Normal)
    }

    fn print_level(&self, level: Option<Sym>) -> RResult<Level> {
        match level {
            None => Ok(Level::Default),
            Some(s) => Level::parse(&s.as_rc()).ok_or_else(|| RuntimeError::runtime(format!("Unknown print level '{s}'"))),
        }
    }

    pub fn verbose_level(&self, flag: &str) -> i64 {
        self.verbose.get(flag).map(|v| v.0).unwrap_or(0)
    }

    fn time_string(&self, cpu: f64, real: f64) -> String {
        let mut s = format!("{:.3}", cpu.max(0.0));
        if self.show_real_time {
            s = format!("{s} [{real:.3}r]");
        }
        s
    }

    pub fn current_function_name(&self) -> String {
        self.trace.last().map(|t| t.name.to_string()).unwrap_or_default()
    }

    /// Build the error for an `error` statement.
    fn raise_user(&mut self, vals: Vec<Value>) -> RResult<RuntimeError> {
        if vals.len() == 1 {
            if let Value::Err(e) = &vals[0] {
                let msg = match &e.object {
                    Value::Str(s) => s.to_string(),
                    o => self.to_string_default(o)?,
                };
                let kind = if &*e.kind == "Err" { ErrKind::Runtime } else { ErrKind::User };
                return Ok(ErrorInfo { kind, object: Some(e.object.clone()), style: crate::error::ErrStyle::Object, ..ErrorInfo::runtime(msg) }.into());
            }
        }
        let msg = self.format_print_list(&vals, Level::Default)?;
        let object = if vals.len() == 1 { vals[0].clone() } else { Value::str(&msg) };
        Ok(ErrorInfo { kind: ErrKind::User, object: Some(object), style: crate::error::ErrStyle::Bare, ..ErrorInfo::runtime(msg) }.into())
    }

    /// The `Err` object bound by `catch e`. A runtime error's object is its
    /// report line (`Runtime error in 'F': ...`), wrapped as Magma prints it,
    /// with the report's closing blank line if it has one.
    pub fn error_object(&mut self, e: &RuntimeError) -> Value {
        let object = match &e.object {
            Some(o) => o.clone(),
            None => {
                let mut s = crate::print::wrap_text_output(&e.headline(), 0, 80);
                if e.trailing_blank() {
                    s.push('\n');
                }
                Value::str(&s)
            }
        };
        let kind = if e.kind == ErrKind::User { "ErrUser" } else { "Err" };
        let position = e.span.map(|s| Rc::from(self.location_block(s, "", true).as_str()));
        let traceback = Some(Rc::from(self.format_trace(e).as_str()));
        let report = Some(Rc::from(self.format_error(e).as_str()));
        Value::Err(Rc::new(ErrObj { object, kind: Rc::from(kind), position, traceback, report }))
    }

    pub fn describe_position(&self, span: calyx_syntax::Span) -> String {
        match self.source(span.file) {
            Some(src) => {
                let (line, col) = src.line_col(span.lo as usize);
                if src.name.is_empty() || src.name.starts_with('<') {
                    format!("line {}, column {}", line + 1, col + 1)
                } else {
                    format!("In file \"{}\", line {}, column {}", src.name, line + 1, col + 1)
                }
            }
            None => String::new(),
        }
    }

    pub fn format_trace(&self, e: &RuntimeError) -> String {
        let mut out = String::new();
        for fr in &e.trace {
            out.push_str(&fr.name.as_rc());
            if let Some(sp) = fr.span {
                out.push_str(&format!(" ({})", self.describe_position(sp)));
            }
            out.push('\n');
        }
        out
    }

    pub(crate) fn eval_int_small(&mut self, e: &E, f: &mut Frame) -> RResult<i64> {
        match self.eval(e, f)? {
            Value::Int(i) => i.to_i64().ok_or_else(|| RuntimeError::runtime("Integer argument is too large")),
            Value::Bool(b) => Ok(b as i64),
            _ => Err(RuntimeError::runtime("Expected an integer")),
        }
    }

    pub fn read_input_line(&mut self, prompt: &str) -> RResult<String> {
        self.out.write(prompt);
        self.out.flush();
        if let Some(l) = self.input_lines.pop_front() {
            return Ok(l);
        }
        if let Some(hook) = &mut self.read_line_hook {
            if let Some(l) = hook(prompt) {
                return Ok(l);
            }
            return Err(RuntimeError::runtime("End of input"));
        }
        let mut s = String::new();
        match std::io::stdin().read_line(&mut s) {
            Ok(0) | Err(_) => Err(RuntimeError::runtime("End of input")),
            Ok(_) => {
                self.out.write("");
                Ok(s.trim_end_matches(['\n', '\r']).to_string())
            }
        }
    }
}

/// Where errors in assigning to `lv` are reported: at the bracket or
/// backquote of an indexed or attribute target.
fn lv_err_span(lv: &LV) -> calyx_syntax::Span {
    fn span(lv: &LV) -> calyx_syntax::Span {
        match lv {
            LV::Var(_, s) | LV::Index(_, _, s) | LV::Attr(_, _, s) | LV::AttrDyn(_, _, s) => *s,
            LV::Discard => calyx_syntax::Span::default(),
        }
    }
    match lv {
        LV::Index(b, _, s) | LV::Attr(b, _, s) | LV::AttrDyn(b, _, s) => calyx_syntax::Span { file: s.file, lo: span(b).hi, hi: s.hi },
        _ => span(lv),
    }
}
