//! Printing values at the Magma print levels, with line wrapping.

use std::rc::Rc;

use crate::error::{RResult, RuntimeError};
use crate::interp::Interp;
use crate::sym::Sym;
use crate::value::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Level {
    Minimal,
    Default,
    Maximal,
    Magma,
    /// Integers in base 16.
    Hex,
}

impl Level {
    pub fn parse(s: &str) -> Option<Level> {
        Some(match s {
            "Minimal" => Level::Minimal,
            "Default" => Level::Default,
            "Maximal" => Level::Maximal,
            "Magma" => Level::Magma,
            "Hex" => Level::Hex,
            _ => return None,
        })
    }

    pub fn name(self) -> &'static str {
        match self {
            Level::Minimal => "Minimal",
            Level::Default => "Default",
            Level::Maximal => "Maximal",
            Level::Magma => "Magma",
            Level::Hex => "Hex",
        }
    }
}

/// Accumulates output, wrapping lines as Magma does: a line that would
/// exceed the width is broken at its last space (which stays at the end of
/// the line) if the word after it starts in the second half of the line
/// (of the part after its indentation). A word that starts in the first
/// half fills the line instead, up to the column before the last, and
/// continues after a backslash. Continued lines start with the `cont`
/// spaces in force where their word started.
pub struct Printer {
    pub buf: String,
    pub col: usize,
    pub width: usize,
    pub level: Level,
    /// Indentation of lines continued by wrapping.
    pub cont: usize,
    /// Byte offset in `buf` where the text of the current line starts
    /// (after its indentation); spaces before it are not break points.
    line_start: usize,
    /// Indentation of the current line.
    line_indent: usize,
    /// No line breaking (`Sprint`, and inside quoted strings).
    pub no_wrap: bool,
    /// Lines start without indentation, as in `Sprint` and `Sprintf`.
    pub bare: bool,
    /// The `cont` in force where the word being written started; none
    /// between words.
    word_cont: Option<usize>,
}

impl Printer {
    pub fn new(col: usize, width: usize, level: Level) -> Printer {
        Printer { buf: String::new(), col, width: width.max(20), level, cont: 0, line_start: 0, line_indent: 0, no_wrap: false, bare: false, word_cont: None }
    }

    pub fn write(&mut self, s: &str) {
        for c in s.chars() {
            self.put(c);
        }
    }

    fn put(&mut self, c: char) {
        if c == '\n' {
            self.buf.push('\n');
            self.col = 0;
            self.line_start = self.buf.len();
            self.line_indent = 0;
            self.word_cont = None;
            return;
        }
        if c == ' ' {
            self.word_cont = None;
        } else if self.word_cont.is_none() {
            self.word_cont = Some(self.cont);
        }
        if self.col >= self.width && !self.no_wrap {
            if c == ' ' {
                // A space that does not fit becomes the line break.
                self.break_line();
                return;
            }
            match self.buf[self.line_start..].rfind(' ') {
                Some(j) => {
                    let tail = self.buf.split_off(self.line_start + j + 1);
                    self.break_line();
                    for t in tail.chars() {
                        self.put(t);
                    }
                }
                None => {
                    // No space to break at: continue after a backslash, as
                    // indented as any continued line.
                    let last = self.buf.pop();
                    self.buf.push('\\');
                    self.break_line();
                    if let Some(l) = last {
                        self.buf.push(l);
                        self.col += 1;
                    }
                }
            }
        } else if self.col + 1 == self.width && c != ' ' && !self.no_wrap && !self.late() {
            self.buf.push('\\');
            self.break_line();
        }
        self.buf.push(c);
        self.col += 1;
    }

    /// Whether the word being written (after the last space on the line)
    /// starts in the second half of the line.
    fn late(&self) -> bool {
        let w = self.buf[self.line_start..].rfind(' ').map_or(self.line_start, |j| self.line_start + j + 1);
        self.starts_late(self.col.saturating_sub(self.buf[w..].chars().count()))
    }

    /// Whether column `start` is in the second half of the part of the line
    /// after its indentation.
    fn starts_late(&self, start: usize) -> bool {
        start.saturating_sub(self.line_indent) > self.width.saturating_sub(self.line_indent) / 2
    }

    /// Continue on the next line, indented as where the word being written
    /// started (as `cont` between words).
    fn break_line(&mut self) {
        let indent = self.word_cont.unwrap_or(self.cont);
        self.buf.push('\n');
        for _ in 0..indent {
            self.buf.push(' ');
        }
        self.col = indent;
        self.line_start = self.buf.len();
        self.line_indent = indent;
    }

    pub fn newline(&mut self, indent: usize) {
        // Trim trailing spaces on the finished line.
        while self.buf.ends_with(' ') && self.buf.len() > self.line_start {
            self.buf.pop();
        }
        self.buf.push('\n');
        self.word_cont = None;
        let indent = if self.bare { 0 } else { indent };
        for _ in 0..indent {
            self.buf.push(' ');
        }
        self.col = indent;
        self.line_start = self.buf.len();
        self.line_indent = indent;
    }

    /// Write an atomic piece of text, such as an integer. The word it ends
    /// (after the last space on the line) may end in the last column if it
    /// starts in the second half of the line, and otherwise must end before
    /// it. One that does not fit moves to the next line if it starts in the
    /// second half; otherwise it is broken where it stands (with backslashes).
    pub fn atom(&mut self, s: &str, _breakable: bool) {
        let n = s.chars().count();
        if self.no_wrap || n == 0 {
            self.write(s);
            return;
        }
        self.word_cont.get_or_insert(self.cont);
        let space = self.buf[self.line_start..].rfind(' ').map(|j| self.line_start + j + 1);
        let late = self.starts_late(self.col.saturating_sub(self.buf[space.unwrap_or(self.line_start)..].chars().count()));
        if self.col + n < self.width + late as usize {
            self.write(s);
            return;
        }
        if let (true, Some(from)) = (late, space) {
            let tail = self.buf.split_off(from);
            self.break_line();
            self.write(&tail);
            if self.col + n < self.width {
                self.write(s);
                return;
            }
        }
        // Each line holds all it can but the backslash.
        self.line_start = self.buf.len();
        for c in s.chars() {
            if self.col + 1 >= self.width {
                self.buf.push('\\');
                self.break_line();
            }
            self.buf.push(c);
            self.col += 1;
        }
    }

    /// Write a quoted string. Magma never breaks one, and the line counts as
    /// empty after it.
    pub fn quoted(&mut self, s: &str) {
        let saved = self.no_wrap;
        self.no_wrap = true;
        self.write(s);
        self.no_wrap = saved;
        self.empty_line();
        self.line_start = self.buf.len();
        self.word_cont = None;
    }

    /// Count the line as empty from here on, as Magma does after quoted
    /// strings and some text its package code prints.
    pub fn empty_line(&mut self) {
        self.col = 0;
        self.line_indent = 0;
    }

    /// Write text that breaks at spaces, each word placed as an atom (a
    /// string's contents, error messages, `printf` output).
    pub fn text(&mut self, s: &str) {
        for (k, line) in s.split('\n').enumerate() {
            if k > 0 {
                self.put('\n');
            }
            for (i, w) in line.split(' ').enumerate() {
                if i > 0 {
                    self.put(' ');
                }
                self.atom(w, true);
            }
        }
    }
}

/// Whether an element prints on one line inside an aggregate.
fn is_simple(v: &Value) -> bool {
    match v {
        Value::Int(_) | Value::Rat(_) | Value::Real(_) | Value::Complex(_) | Value::Bool(_) | Value::Str(_) | Value::Cat(_) | Value::ECat(_) | Value::Undef | Value::Intr(_) | Value::Infinity(_) => true,
        Value::Tuple(t) => t.elems.iter().all(is_simple),
        Value::List(_) => true,
        Value::CopElt(c) => is_simple(&c.value),
        Value::Func(_) => true,
        Value::Elt(e) => !elt_is_compound(e),
        Value::Small(..) => true,
        _ => false,
    }
}

/// Values that aggregates set off by a blank line, and that make a tuple
/// print one element per line: abelian groups.
fn is_block(v: &Value) -> bool {
    matches!(v, Value::Struct(s) if matches!(s.kind, StructKind::AbGroup(_))) || is_matrix(v)
}

/// A matrix (not a vector) or an R-space, which a print list starts on a
/// line of its own.
fn is_matrix(v: &Value) -> bool {
    matches!(v, Value::Mat(m) if !m.is_vector()) || crate::intrinsics::matrices::is_rspace(v)
}

/// Ring elements that print as sums of terms (polynomials, and elements of
/// finite fields too large for Zech logarithms).
fn elt_is_compound(e: &crate::rings::Elt) -> bool {
    use crate::rings::RingKind;
    match &e.ring().kind {
        RingKind::UPoly { .. } | RingKind::MPoly { .. } | RingKind::UPolyRes { .. } | RingKind::MPolyRes { .. } => true,
        RingKind::Finite(f) => f.degree > 1 && !crate::rings::finite::is_small(&f.p, f.degree),
        _ => false,
    }
}

/// The name a structure was assigned to, or `$`.
fn group_name(s: &Struct) -> String {
    s.name.borrow().map(|n| n.to_string()).unwrap_or_else(|| "$".to_string())
}

/// An abelian group: its invariants and its relations, one per line.
fn fmt_abgroup(p: &mut Printer, s: &Struct, g: &crate::abgroups::AbGroup, indent: usize) {
    let n = g.ngens();
    let free = g.orders.iter().all(|o| o.is_zero());
    if p.level == Level::Magma {
        if free {
            p.write(&format!("FreeAbelianGroup({n})"));
            return;
        }
        let gens: Vec<String> = (1..=n).map(|i| format!("x{i}")).collect();
        let rels: Vec<String> =
            g.orders.iter().enumerate().filter(|(_, o)| !o.is_zero()).map(|(i, o)| if o.is_one() { format!("x{}", i + 1) } else { format!("{o}*x{}", i + 1) }).collect();
        p.write(&format!("AbelianGroup<{} | {}>", gens.join(", "), rels.join(", ")));
        return;
    }
    if g.order().is_some_and(|o| o.is_one()) {
        p.write("Abelian Group of order 1");
        if n == 0 {
            return;
        }
    } else {
        let parts: Vec<String> = g.invariants().iter().map(|d| if d.is_zero() { "Z".to_string() } else { format!("Z/{d}") }).collect();
        p.write(&format!("Abelian Group isomorphic to {}", parts.join(" + ")));
    }
    p.newline(indent);
    p.write(&format!("Defined on {n} generator{}", if n == 1 { "" } else { "s" }));
    if free {
        p.write(" (free)");
        return;
    }
    p.newline(indent);
    p.write("Relations:");
    let name = group_name(s);
    for (i, o) in g.orders.iter().enumerate().filter(|(_, o)| !o.is_zero()) {
        p.newline(indent + 4);
        let c = if o.is_one() { String::new() } else { format!("{o}*") };
        p.write(&format!("{c}{name}.{} = 0", i + 1));
    }
}

/// Whether the next value in a print list goes on a new line after `v`
/// (rather than after a space).
fn needs_newline(v: &Value) -> bool {
    match v {
        Value::Seq(_) | Value::Set(_) | Value::ISet(_) | Value::MSet(_) | Value::Struct(_) | Value::Rec(_) => true,
        Value::Elt(e) => elt_is_compound(e),
        Value::Perm(_) | Value::AbElt(_) | Value::Map(_) | Value::Nfd(_) | Value::Drch(_) | Value::Mat(_) => true,
        Value::Tuple(t) => t.elems.iter().any(needs_newline),
        _ => false,
    }
}

pub fn quote_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

impl Interp {
    /// Print values separated by spaces, followed by a newline.
    pub fn print_values(&mut self, vals: &[Value], level: Level) -> RResult<()> {
        // Like printf, print wraps from the start of its own output.
        let mut p = self.printer(level);
        self.fmt_print_list(&mut p, vals)?;
        let text = self.apply_indent(&(p.buf + "\n"));
        self.out.write(&text);
        Ok(())
    }

    /// A printer for the current line width. Without a limit
    /// (`SetColumns(0)`), Magma indents no lines at all.
    fn printer(&self, level: Level) -> Printer {
        let mut p = Printer::new(0, self.out.columns, level);
        p.bare = self.out.unlimited();
        p
    }

    fn apply_indent(&self, s: &str) -> String {
        if self.indent_level == 0 || self.out.unlimited() {
            return s.to_string();
        }
        let pad = " ".repeat(self.indent_level * self.indent_width);
        let mut out = String::new();
        let at_line_start = self.out.col() == 0;
        for (i, line) in s.split_inclusive('\n').enumerate() {
            if (i > 0 || at_line_start) && line != "\n" {
                out.push_str(&pad);
            }
            out.push_str(line);
        }
        out
    }

    /// Format values separated by spaces (no trailing newline).
    pub fn format_print_list(&mut self, vals: &[Value], level: Level) -> RResult<String> {
        let mut p = self.printer(level);
        self.fmt_print_list(&mut p, vals)?;
        Ok(p.buf)
    }

    /// Values separated by spaces, or by newlines after values that do not
    /// print on a single line.
    fn fmt_print_list(&mut self, p: &mut Printer, vals: &[Value]) -> RResult<()> {
        for (i, v) in vals.iter().enumerate() {
            if i > 0 {
                if needs_newline(&vals[i - 1]) {
                    p.newline(0);
                } else {
                    p.write(" ");
                }
                if is_matrix(v) {
                    p.write("\n");
                }
            }
            self.fmt(p, v, 0)?;
        }
        Ok(())
    }

    pub fn format_value(&mut self, v: &Value, level: Level) -> RResult<String> {
        let mut p = self.printer(level);
        self.fmt(&mut p, v, 0)?;
        Ok(p.buf)
    }

    /// `Sprint`: like printing, but without indenting nested lines or
    /// wrapping long ones (the string wraps only when it is printed).
    pub fn format_bare(&mut self, v: &Value, level: Level) -> RResult<String> {
        let mut p = Printer::new(0, self.out.columns, level);
        p.bare = true;
        p.no_wrap = true;
        self.fmt(&mut p, v, 0)?;
        Ok(p.buf)
    }

    /// Format without any line breaking (for inline contexts).
    pub fn format_flat(&mut self, v: &Value, level: Level) -> RResult<String> {
        let mut p = Printer::new(0, usize::MAX / 2, level);
        self.fmt(&mut p, v, 0)?;
        Ok(p.buf)
    }

    pub fn to_string_default(&mut self, v: &Value) -> RResult<String> {
        self.format_value(v, Level::Default)
    }

    /// Format `v` into the printer; `indent` is the current nesting indent.
    pub fn fmt(&mut self, p: &mut Printer, v: &Value, indent: usize) -> RResult<()> {
        match v {
            Value::Undef => p.write("undef"),
            Value::Bool(b) => p.write(if *b { "true" } else { "false" }),
            Value::Int(i) if p.level == Level::Hex => {
                let digits = i.abs().to_string_radix(16).to_uppercase();
                p.atom(&format!("{}0x{digits}", if i.sign() < 0 { "-" } else { "" }), true)
            }
            Value::Int(i) => p.atom(&i.to_string(), true),
            Value::Rat(q) => p.atom(&q.to_string(), true),
            Value::Real(r) => p.atom(&crate::intrinsics::reals::format_real(r, p.level), true),
            Value::Complex(c) => {
                let s = crate::intrinsics::complex::format_complex(self, c, p.level);
                p.write(&s);
            }
            Value::Str(s) => {
                if p.level == Level::Magma {
                    p.quoted(&quote_string(s));
                } else {
                    p.text(s);
                }
            }
            Value::Seq(s) => {
                if s.elems.is_empty() {
                    if p.level == Level::Magma {
                        if let Some(u) = &s.universe {
                            let u = u.clone();
                            p.write("[ ");
                            self.fmt(p, &u, indent)?;
                            p.write(" | ]");
                            return Ok(());
                        }
                    }
                    p.write("[]");
                } else if let Some((lo, hi, step)) = s.as_progression() {
                    let open = if p.level == Level::Magma { "\\[" } else { "[" };
                    if step.is_one() {
                        p.write(&format!("{open} {lo} .. {hi} ]"));
                    } else {
                        p.write(&format!("{open} {lo} .. {hi} by {step} ]"));
                    }
                } else {
                    let elems = s.elems.clone();
                    let open = self.agg_open(p, "[", &s.universe, true)?;
                    self.fmt_agg(p, &open, "]", &elems, indent, None)?;
                }
            }
            Value::Set(s) => {
                if s.is_empty() {
                    let open = self.agg_open(p, "{", &s.universe, false)?;
                    p.write(if open == "{" { "{}".to_string() } else { format!("{open} }}") }.as_str());
                } else if let SetRepr::Range { lo, step, len } = &s.repr {
                    let hi = lo + &(step * &calyx_flint::Integer::from_u64(len - 1));
                    if step.is_one() {
                        p.write(&format!("{{ {lo} .. {hi} }}"));
                    } else {
                        p.write(&format!("{{ {lo} .. {hi} by {step} }}"));
                    }
                } else {
                    let mut elems: Vec<Value> = s.iter().collect();
                    sort_values(&mut elems);
                    let open = self.agg_open(p, "{", &s.universe, false)?;
                    self.fmt_agg(p, &open, "}", &elems, indent, None)?;
                }
            }
            Value::ISet(s) => {
                let open = self.agg_open(p, "{@", &s.universe, false)?;
                if s.elems.is_empty() {
                    p.write(&format!("{open} @}}"));
                } else {
                    let elems: Vec<Value> = s.elems.iter().cloned().collect();
                    self.fmt_agg(p, &open, "@}", &elems, indent, None)?;
                }
            }
            Value::MSet(s) => {
                let open = self.agg_open(p, "{*", &s.universe, false)?;
                if s.elems.is_empty() {
                    p.write(&format!("{open} *}}"));
                } else {
                    let mut pairs: Vec<(Value, u64)> = s.elems.iter().map(|(v, n)| (v.clone(), *n)).collect();
                    let mut keys: Vec<Value> = pairs.iter().map(|p| p.0.clone()).collect();
                    if sort_values(&mut keys) {
                        let m: VMap<u64> = pairs.drain(..).collect();
                        pairs = keys.into_iter().map(|k| (k.clone(), m[&k])).collect();
                    }
                    let elems: Vec<Value> = pairs.iter().map(|x| x.0.clone()).collect();
                    let mults: Vec<u64> = pairs.iter().map(|x| x.1).collect();
                    self.fmt_agg(p, &open, "*}", &elems, indent, Some(&mults))?;
                }
            }
            Value::List(l) => {
                if l.is_empty() {
                    p.write("[* *]");
                } else if l.iter().all(is_simple) {
                    p.write("[* ");
                    for (i, e) in l.iter().enumerate() {
                        if i > 0 {
                            p.write(", ");
                        }
                        self.fmt(p, e, indent)?;
                    }
                    p.write(" *]");
                } else {
                    // Runs of simple elements share a line (the first run
                    // follows the bracket); other elements get a line each.
                    p.write("[*");
                    let saved = p.cont;
                    p.cont = indent + 4;
                    for (i, e) in l.iter().enumerate() {
                        let same_line = is_simple(e) && (i == 0 || is_simple(&l[i - 1]));
                        if same_line {
                            p.write(" ");
                        } else {
                            if i > 0 && is_block(e) {
                                p.newline(0);
                            }
                            p.newline(indent + 4);
                        }
                        self.fmt(p, e, indent + 4)?;
                        if i + 1 < l.len() {
                            p.write(",");
                        }
                    }
                    p.cont = saved;
                    p.newline(indent);
                    p.write("*]");
                }
            }
            Value::Tuple(t) if t.elems.iter().any(is_block) => {
                // One element per line, with blank lines between them.
                p.write("<");
                let saved = p.cont;
                p.cont = indent + 4;
                for (i, e) in t.elems.iter().enumerate() {
                    if i > 0 {
                        p.write(",");
                        p.newline(0);
                    }
                    p.newline(indent + 4);
                    self.fmt(p, e, indent + 4)?;
                }
                p.cont = saved;
                p.newline(indent);
                p.write(">");
            }
            Value::Tuple(t) => {
                p.write("<");
                for (i, e) in t.elems.iter().enumerate() {
                    if i > 0 {
                        p.write(", ");
                    }
                    // Strings in tuples print with quotes, except minimally.
                    match e {
                        Value::Str(s) if p.level != Level::Minimal => p.quoted(&quote_string(s)),
                        _ => self.fmt(p, e, indent)?,
                    }
                }
                p.write(">");
            }
            Value::Rec(r) => self.fmt_record(p, r, indent)?,
            Value::Assoc(a) => {
                p.write("Associative Array");
                if let Some(u) = &a.universe {
                    let u = u.clone();
                    p.write(" with index universe ");
                    self.fmt(p, &u, indent)?;
                }
            }
            Value::Func(c) => {
                let params: Vec<String> = c.code.params.iter().map(|ps| if ps.is_ref { format!("~{}", ps.name) } else { ps.name.to_string() }).collect();
                let params = params.join(", ");
                p.write(&if c.code.is_procedure { format!("procedure({params}) ... end procedure") } else { format!("function({params}) ... end function") });
            }
            Value::Intr(name) => {
                if p.level == Level::Minimal || indent > 0 {
                    p.write(&format!("Intrinsic '{name}'"));
                } else {
                    let text = self.describe_intrinsic(*name);
                    p.write(&text);
                }
            }
            Value::Map(m) => {
                let m = m.clone();
                // Maps given by rules print as mappings, even from hom< > and iso< >.
                let kind = match (m.kind, &m.imp) {
                    (MapKind::Map | MapKind::PMap, _) | (_, MapImpl::Rule { .. }) => "Mapping",
                    (MapKind::Hom | MapKind::Iso, _) => "Homomorphism",
                };
                p.write(&format!("{kind} from: "));
                // Domain and codomain print briefly (named structures by name).
                let saved = p.level;
                p.level = Level::Minimal;
                self.fmt_map_end(p, &m.domain, indent)?;
                p.write(" to ");
                self.fmt_map_end(p, &m.codomain, indent)?;
                p.level = saved;
                match &m.imp {
                    MapImpl::Rule { inv, .. } => {
                        p.write(if inv.is_some() { " given by a rule" } else { " given by a rule [no inverse]" });
                    }
                    MapImpl::Graph(g) => {
                        let pairs: Vec<(Value, Value)> = g.iter().map(|(x, y)| (x.clone(), y.clone())).collect();
                        self.fmt_map_graph(p, &pairs, indent)?;
                    }
                    MapImpl::Native(n) => {
                        if n.rule() {
                            p.write(" given by a rule [no inverse]");
                        } else if n.rule_with_inverse() {
                            p.write(" given by a rule");
                        }
                        if let Some(pairs) = n.graph(&m) {
                            self.fmt_map_graph(p, &pairs, indent)?;
                        }
                    }
                    MapImpl::Compose(ms) => {
                        p.newline(indent);
                        p.write(&format!("Composition of {} maps", ms.len()));
                    }
                    MapImpl::Reduction(m) => {
                        p.newline(indent);
                        p.write(&format!("modulo {m}"));
                    }
                    _ => {}
                }
            }
            Value::Struct(s) => self.fmt_struct(p, s, indent)?,
            Value::Cat(t) => p.write(&self.types.name(*t)),
            Value::ECat(t) => p.write(&t.display(&self.types).to_string()),
            Value::Err(e) => {
                let e = e.clone();
                match &e.report {
                    Some(r) => p.write(r.strip_suffix('\n').unwrap_or(r)),
                    None => {
                        p.write("Error: ");
                        self.fmt(p, &e.object, indent)?;
                    }
                }
            }
            Value::Obj(_) => self.fmt_user(p, v)?,
            Value::CopElt(c) => {
                let c = c.clone();
                self.fmt(p, &c.value, indent)?;
            }
            Value::Formal(f) => {
                p.write(if f.is_seq { "Formal sequence over " } else { "Formal set over " });
                let u = f.universe.clone();
                self.fmt(p, &u, indent)?;
            }
            Value::Io(io) => p.write(&format!("File \"{}\" (mode \"{}\")", io.name, io.mode)),
            // A Zech logarithm prints as the power of the generator it stands for.
            Value::Small(r, x) if r.zech().is_some() => {
                let e = crate::rings::small::to_elt(*r, *x);
                p.write(&crate::rings::format_ring_elt(self, &e, p.level)?);
            }
            Value::Small(_, x) => p.write(&x.to_string()),
            Value::AbElt(x) => p.write(&x.format()),
            // Magma's package code prints characters: the line counts as
            // empty after them, as after nearfields.
            Value::Drch(x) => {
                p.write(&crate::intrinsics::residue::dirichlet::format(x));
                p.empty_line();
            }
            // Magma prints nearfield elements as text: unlike field elements,
            // their continuation lines are not indented further, and the
            // field's generator goes by a name given with < > only, not by
            // the identifier the field is assigned to. As for nearfields,
            // the line counts as empty after the text.
            Value::Nfd(x) => {
                match crate::intrinsics::nearfields::as_field_value(x) {
                    Value::Elt(e) => {
                        let name = e.parent.name.take();
                        let s = crate::rings::format_ring_elt(self, &e, p.level);
                        *e.parent.name.borrow_mut() = name;
                        p.write(&s?);
                    }
                    v => self.fmt(p, &v, indent)?,
                }
                p.empty_line();
            }
            Value::Elt(e) => {
                let s = crate::rings::format_ring_elt(self, e, p.level)?;
                // Continuation lines of a sum are indented further.
                let saved = p.cont;
                if elt_is_compound(e) {
                    p.cont += 4;
                }
                p.write(&s);
                p.cont = saved;
            }
            Value::Mat(m) => {
                let m = m.clone();
                crate::intrinsics::matrices::fmt_matrix(self, p, &m, indent)?;
            }
            Value::Infinity(pos) => p.write(match (p.level == Level::Magma, *pos) {
                (false, true) => "Infinity",
                (false, false) => "-Infinity",
                (true, true) => "Infinity()",
                (true, false) => "MinusInfinity()",
            }),
            Value::Perm(pm) => {
                if p.level == Level::Magma {
                    // The images, without the `\[` of integer sequences.
                    let images: Vec<Value> = pm.images.iter().map(|&x| Value::Int(calyx_flint::Integer::from_u64(x as u64 + 1))).collect();
                    return self.fmt_agg(p, "[", "]", &images, indent, None);
                }
                let text = match pm.cycle_notation() {
                    Some(c) => c,
                    None => format!("Id({})", group_name(&pm.group)),
                };
                // Continuation lines of long cycles are indented further.
                let saved = p.cont;
                p.cont += 4;
                p.write(&text);
                p.cont = saved;
            }
        }
        Ok(())
    }

    /// The graph of a map, one pair `<x, y>` per line.
    fn fmt_map_graph(&mut self, p: &mut Printer, pairs: &[(Value, Value)], indent: usize) -> RResult<()> {
        for (x, y) in pairs {
            p.newline(indent + 4);
            p.write("<");
            self.fmt(p, x, indent + 4)?;
            p.write(", ");
            self.fmt(p, y, indent + 4)?;
            p.write(">");
        }
        Ok(())
    }

    /// The domain or codomain of a map: a named structure or aggregate by
    /// its category and name.
    fn fmt_map_end(&mut self, p: &mut Printer, v: &Value, indent: usize) -> RResult<()> {
        if let Some(n) = v.name_cell().and_then(|c| *c.borrow()) {
            let t = self.types.name(v.type_id());
            p.write(&format!("{t}: {n}"));
            return Ok(());
        }
        self.fmt(p, v, indent)
    }

    /// The opening bracket of an aggregate. At the Magma level it names the
    /// universe (`[ RationalField() |`), except that sequences of integers
    /// use the short form `\[`.
    fn agg_open(&mut self, p: &Printer, open: &str, universe: &Option<Value>, seq: bool) -> RResult<String> {
        match universe {
            Some(u) if p.level == Level::Magma => {
                if seq && u.is_integers() {
                    return Ok(format!("\\{open}"));
                }
                Ok(format!("{open} {} |", self.format_flat(u, Level::Magma)?))
            }
            _ => Ok(open.to_string()),
        }
    }

    /// Print an aggregate horizontally if all elements are simple,
    /// otherwise one element per line.
    fn fmt_agg(&mut self, p: &mut Printer, open: &str, close: &str, elems: &[Value], indent: usize, mults: Option<&[u64]>) -> RResult<()> {
        let vertical = !elems.iter().all(is_simple);
        if vertical {
            p.write(open);
            let saved = p.cont;
            p.cont = indent + 4;
            for (i, e) in elems.iter().enumerate() {
                if i > 0 && is_block(e) {
                    p.newline(0);
                }
                p.newline(indent + 4);
                self.fmt(p, e, indent + 4)?;
                if let Some(m) = mults {
                    if m[i] > 1 {
                        p.write(&format!("^^{}", m[i]));
                    }
                }
                if i + 1 < elems.len() {
                    // The comma ends the element's line: one that does not
                    // fit continues as the element does.
                    p.cont = indent + 8;
                    p.write(",");
                    p.cont = indent + 4;
                }
            }
            p.cont = saved;
            p.newline(indent);
            p.write(close);
            return Ok(());
        }
        p.write(open);
        p.write(" ");
        for (i, e) in elems.iter().enumerate() {
            self.fmt(p, e, indent)?;
            if let Some(m) = mults {
                if m[i] > 1 {
                    p.write(&format!("^^{}", m[i]));
                }
            }
            if i + 1 < elems.len() {
                p.write(", ");
            }
        }
        p.write(" ");
        p.write(close);
        Ok(())
    }

    fn fmt_record(&mut self, p: &mut Printer, r: &Rc<Record>, indent: usize) -> RResult<()> {
        let StructKind::RecFormat(rf) = &r.format.kind else { unreachable!() };
        p.write("rec<");
        let name = *r.format.name.borrow();
        match name {
            Some(n) => p.write(&n.to_string()),
            None => {
                let fmt = Value::Struct(r.format.clone());
                self.fmt(p, &fmt, indent)?;
            }
        }
        // One field per line; long values continue further indented.
        let fields: Vec<(Sym, Value)> = rf.names.iter().zip(&r.fields).filter(|(_, v)| !v.is_undef()).map(|(n, v)| (*n, v.clone())).collect();
        if fields.is_empty() {
            p.write(" | >");
            return Ok(());
        }
        // Minimally, the fields are left out.
        if p.level == Level::Minimal {
            p.write(" | ...>");
            return Ok(());
        }
        p.write(" |");
        let saved = p.cont;
        p.cont = indent + 8;
        for (i, (n, v)) in fields.iter().enumerate() {
            p.newline(indent + 4);
            p.write(&format!("{n} := "));
            self.fmt(p, v, indent + 4)?;
            if i + 1 < fields.len() {
                p.write(",");
            }
        }
        p.cont = saved;
        p.write(">");
        Ok(())
    }

    fn fmt_struct(&mut self, p: &mut Printer, s: &Rc<Struct>, indent: usize) -> RResult<()> {
        let opt = |me: &mut Interp, p: &mut Printer, u: &Option<Value>| -> RResult<()> {
            match u {
                Some(u) => me.fmt(p, u, indent),
                None => {
                    p.write("null");
                    Ok(())
                }
            }
        };
        // At the minimal level, a named composite structure prints as its
        // category and name.
        if p.level == Level::Minimal && matches!(s.kind, StructKind::Coproduct(_) | StructKind::Cartesian(_)) {
            if let Some(n) = *s.name.borrow() {
                let t = self.types.name(Value::Struct(s.clone()).type_id());
                p.write(&format!("{t}: {n}"));
                return Ok(());
            }
        }
        if p.level == Level::Magma {
            match &s.kind {
                StructKind::Integers => return Ok(p.write("IntegerRing()")),
                StructKind::Rationals => return Ok(p.write("RationalField()")),
                StructKind::Reals(b) => return Ok(p.write(&format!("RealField({})", calyx_flint::digits_for_bits(*b)))),
                StructKind::Booleans => return Ok(p.write("Booleans()")),
                StructKind::Strings => return Ok(p.write("Strings()")),
                StructKind::PowerSet(Some(u)) | StructKind::PowerSeq(Some(u)) | StructKind::PowerISet(Some(u)) | StructKind::PowerMSet(Some(u)) => {
                    let f = match &s.kind {
                        StructKind::PowerSet(_) => "PowerSet",
                        StructKind::PowerSeq(_) => "PowerSequence",
                        StructKind::PowerISet(_) => "PowerIndexedSet",
                        _ => "PowerMultiset",
                    };
                    p.write(&format!("{f}("));
                    let u = u.clone();
                    self.fmt(p, &u, indent)?;
                    p.write(")");
                    return Ok(());
                }
                StructKind::Cartesian(parts) => {
                    p.write("car<");
                    for (i, x) in parts.clone().iter().enumerate() {
                        if i > 0 {
                            p.write(", ");
                        }
                        self.fmt(p, x, indent)?;
                    }
                    p.write(">");
                    return Ok(());
                }
                _ => {}
            }
        }
        match &s.kind {
            StructKind::AbGroup(g) => fmt_abgroup(p, s, g, indent),
            // Magma's package code prints the group the same at every level,
            // and the line counts as empty after it.
            StructKind::DrchGroup(g) => {
                p.write(&format!("Group of Dirichlet characters of modulus {} over ", g.modulus));
                let (saved, ring) = (p.level, g.ring.clone());
                p.level = Level::Default;
                self.fmt(p, &ring, indent)?;
                p.level = saved;
                p.empty_line();
            }
            StructKind::Matrices(_) => crate::intrinsics::matrices::fmt_parent(self, p, s, indent)?,
            // Magma's package code prints nearfields (without the order at
            // the minimal level), and what it prints does not count toward
            // the width of the line: the line counts as empty after it.
            StructKind::Nearfield(_) => {
                let [kind, order] = crate::intrinsics::nearfields::describe(s);
                p.write(&kind);
                if p.level != Level::Minimal {
                    p.newline(indent);
                    p.write(&order);
                }
                p.empty_line();
            }
            StructKind::Integers => p.write("Integer Ring"),
            StructKind::Rationals => p.write("Rational Field"),
            // Real and complex fields print their name at the minimal level.
            StructKind::Reals(_) if p.level == Level::Minimal && s.name.borrow().is_some() => p.write(&group_name(s)),
            StructKind::Reals(b) if is_timing_reals(s) => {
                let digits = calyx_flint::digits_for_bits(*b);
                p.write(&format!("Real field of precision {digits} printing with {TIMING_DECIMALS} digits after the decimal point"))
            }
            StructKind::Reals(b) => p.write(&format!("Real field of precision {}", calyx_flint::digits_for_bits(*b))),
            StructKind::Booleans => p.write("Boolean Structure"),
            StructKind::Strings => p.write("String structure"),
            StructKind::PowerSet(u) => {
                p.write("Set of subsets of ");
                opt(self, p, u)?;
            }
            StructKind::PowerSeq(u) => {
                p.write("Set of sequences over ");
                opt(self, p, u)?;
            }
            StructKind::PowerISet(u) => {
                p.write("Set of indexed subsets of ");
                opt(self, p, u)?;
            }
            StructKind::PowerMSet(u) => {
                p.write("Set of multi subsets of ");
                opt(self, p, u)?;
            }
            StructKind::Cartesian(parts) => {
                p.write("Cartesian Product<");
                for (i, x) in parts.iter().enumerate() {
                    if i > 0 {
                        p.write(", ");
                    }
                    self.fmt(p, x, indent)?;
                }
                p.write(">");
            }
            StructKind::Coproduct(parts) => {
                p.write("Coproduct<");
                for (i, x) in parts.iter().enumerate() {
                    if i > 0 {
                        p.write(", ");
                    }
                    self.fmt(p, x, indent)?;
                }
                p.write(">");
            }
            StructKind::RecFormat(rf) => {
                p.write("recformat<");
                let saved = p.level;
                p.level = Level::Magma;
                for (i, (n, t)) in rf.names.iter().zip(&rf.types).enumerate() {
                    if i > 0 {
                        p.write(", ");
                    }
                    p.write(&n.to_string());
                    if let Some(t) = t {
                        p.write(": ");
                        self.fmt(p, t, indent)?;
                    }
                }
                p.level = saved;
                p.write(">");
            }
            StructKind::Maps(d, c) => {
                // Both ends print briefly, but not by name.
                let saved = p.level;
                p.level = Level::Minimal;
                p.write("Set of all maps from ");
                self.fmt(p, d, indent)?;
                p.write(" to ");
                self.fmt(p, c, indent)?;
                p.level = saved;
            }
            StructKind::PowerStructure(t) if *t == crate::types::t::RNG_INT_ELT_FACT => p.write("Set of integer factorization sequences"),
            StructKind::PowerStructure(t) if p.level == Level::Magma => p.write(&format!("PowerStructure({})", self.types.name(*t))),
            StructKind::PowerStructure(t) => p.write(&format!("Power Structure of {}", self.types.name(*t))),
            StructKind::Ring(r) if p.level == Level::Minimal && matches!(r.kind, crate::rings::RingKind::Complex(_)) && s.name.borrow().is_some() => p.write(&group_name(s)),
            StructKind::Ring(r) if matches!(r.kind, crate::rings::RingKind::MPolyRes { .. }) => crate::intrinsics::poly_ideals::fmt_affine(self, p, s, indent)?,
            StructKind::Ring(r) => {
                let lines = self.format_ring(r, p.level)?;
                // A multivariate ring's first line continues further indented.
                let saved = p.cont;
                if matches!(r.kind, crate::rings::RingKind::MPoly { .. }) {
                    p.cont += 4;
                }
                for (i, line) in lines.iter().enumerate() {
                    if i > 0 {
                        p.cont = saved;
                        p.newline(indent);
                    }
                    p.write(line);
                }
                p.cont = saved;
            }
            StructKind::IntIdeal(n) => p.write(&if p.level == Level::Magma { format!("ideal<IntegerRing() | {n}>") } else { format!("Ideal of Integer Ring generated by {n}") }),
            StructKind::ResIdeal(r, d) => {
                let m = crate::rings::ideals::residue_modulus(r);
                // The zero ideal is generated by 0 (by m at the Magma level).
                let g = if *d == m { calyx_flint::Integer::zero() } else { d.clone() };
                p.write(&if p.level == Level::Magma {
                    format!("ideal<IntegerRing({m}) | {d}>")
                } else {
                    format!("Ideal of residue class ring of integers modulo {m} generated by {g}")
                });
            }
            StructKind::UPolIdeal(g) => {
                let text = crate::intrinsics::upoly::format_ideal(self, g, p.level)?;
                let saved = p.cont;
                p.cont += 4;
                p.write(&text);
                p.cont = saved;
            }
            StructKind::MPolIdeal(id) => crate::intrinsics::poly_ideals::fmt_ideal(self, p, id, indent)?,
            StructKind::AffIdeal(id) => crate::intrinsics::poly_ideals::fmt_aff_ideal(self, p, id, indent)?,
            StructKind::ExtendedReals => p.write(if p.level == Level::Magma { "ExtendedReals()" } else { "Extended Reals" }),
            StructKind::Automorphisms(x) => {
                p.write("Set of all automorphisms of ");
                let saved = p.level;
                p.level = Level::Default;
                self.fmt(p, x, indent)?;
                p.level = saved;
            }
            StructKind::SymGroup(n) => {
                let n = *n as usize;
                let name = group_name(s);
                let fact = crate::perms::factorial_factorization(n);
                match p.level {
                    Level::Magma => p.write(&format!("Sym({n})")),
                    Level::Minimal => p.write(&format!("GrpPerm: {name}, Degree {n}, Order {fact}")),
                    _ => {
                        let named = s.name.borrow().map(|n| format!("{n} ")).unwrap_or_default();
                        p.write(&format!("Symmetric group {named}acting on a set of cardinality {n}"));
                        p.newline(indent);
                        let order = calyx_flint::Integer::factorial(n as u64).to_string();
                        p.write(&format!("Order = {order}"));
                        if fact != order {
                            p.write(&format!(" = {fact}"));
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// Print an object of a user type via its `Print` intrinsic.
    fn fmt_user(&mut self, p: &mut Printer, v: &Value) -> RResult<()> {
        let sym = Sym::new("Print");
        let level = Value::str(p.level.name());
        let with_level = [v.clone(), level.clone()];
        let use_level = self.select_signature(sym, &with_level, &[false, false], true).is_some_and(|s| !s.generic);
        let use_plain = !use_level && self.select_signature(sym, std::slice::from_ref(v), &[false], true).is_some_and(|s| !s.generic);
        if !use_level && !use_plain {
            let Value::Obj(o) = v else { unreachable!() };
            p.write(&format!("Object of type {}", self.types.name(o.ty)));
            return Ok(());
        }
        self.out.begin_capture();
        let mut args: Vec<Value> = if use_level { with_level.to_vec() } else { vec![v.clone()] };
        let mask = vec![false; args.len()];
        let r = self.call_intrinsic(sym, &mut args, &mask, Vec::new(), 0, true, calyx_syntax::Span::default(), None);
        let text = self.out.end_capture();
        r?;
        p.write(&text);
        Ok(())
    }

    /// `printf`-style formatting. `vals[0]` is the format string.
    pub fn sprintf(&mut self, vals: &[Value]) -> RResult<String> {
        let Some(Value::Str(fmt)) = vals.first() else {
            return Err(RuntimeError::runtime("The format must be a string").in_context("printf"));
        };
        let fmt = fmt.clone();
        let mut args = vals[1..].iter();
        let mut out = String::new();
        let chars: Vec<char> = fmt.chars().collect();
        let mut i = 0;
        // Each printf wraps as if it started a line: Magma does not carry
        // the column over from earlier output.
        let col_of = |out: &str| out.rsplit('\n').next().map_or(0, |l| l.chars().count());
        while i < chars.len() {
            let c = chars[i];
            if c != '%' {
                out.push(c);
                i += 1;
                continue;
            }
            i += 1;
            if i >= chars.len() {
                return Err(RuntimeError::runtime("Incomplete conversion specification").in_context("printf"));
            }
            if chars[i] == '%' {
                out.push('%');
                i += 1;
                continue;
            }
            // Width: digits, -digits, or *.
            let mut width: Option<i64> = None;
            if chars[i] == '*' {
                let w = args.next().ok_or_else(|| RuntimeError::runtime("Not enough arguments for the format").in_context("printf"))?;
                let Value::Int(w) = w else {
                    return Err(RuntimeError::runtime("Width argument must be an integer").in_context("printf"));
                };
                width = w.to_i64();
                i += 1;
            } else {
                let start = i;
                if chars[i] == '-' {
                    i += 1;
                }
                while i < chars.len() && chars[i].is_ascii_digit() {
                    i += 1;
                }
                if i > start {
                    let s: String = chars[start..i].iter().collect();
                    width = s.parse().ok();
                }
            }
            let mut precision: Option<usize> = None;
            if i < chars.len() && chars[i] == '.' {
                i += 1;
                let start = i;
                while i < chars.len() && chars[i].is_ascii_digit() {
                    i += 1;
                }
                precision = chars[start..i].iter().collect::<String>().parse().ok();
            }
            if i >= chars.len() {
                return Err(RuntimeError::runtime("Incomplete conversion specification").in_context("printf"));
            }
            let conv = chars[i];
            i += 1;
            let arg = args.next().ok_or_else(|| RuntimeError::runtime("Not enough arguments for the format").in_context("printf"))?.clone();
            let text = match conv {
                'o' => self.format_with_precision(&arg, Level::Default, precision, col_of(&out))?,
                'O' => {
                    let lvl = args.next().ok_or_else(|| RuntimeError::runtime("%O needs a print level argument").in_context("printf"))?;
                    let Value::Str(l) = lvl else {
                        return Err(RuntimeError::runtime("Print level must be a string").in_context("printf"));
                    };
                    let level = Level::parse(l).ok_or_else(|| RuntimeError::runtime(format!("Unknown print level '{l}'")).in_context("printf"))?;
                    self.format_with_precision(&arg, level, precision, col_of(&out))?
                }
                'm' => self.format_with_precision(&arg, Level::Magma, precision, col_of(&out))?,
                'h' => match &arg {
                    Value::Int(n) => {
                        let s = n.abs().to_string_radix(16).to_uppercase();
                        if n.sign() < 0 { format!("-0x{s}") } else { format!("0x{s}") }
                    }
                    _ => return Err(RuntimeError::runtime("%h requires an integer").in_context("printf")),
                },
                other => return Err(RuntimeError::runtime(format!("Unknown conversion specification '%{other}'")).in_context("printf")),
            };
            match width {
                Some(w) if w > 0 => {
                    let len = text.chars().count();
                    if len < w as usize {
                        out.push_str(&" ".repeat(w as usize - len));
                    }
                    out.push_str(&text);
                }
                Some(w) if w < 0 => {
                    let len = text.chars().count();
                    out.push_str(&text);
                    let w = (-w) as usize;
                    if len < w {
                        out.push_str(&" ".repeat(w - len));
                    }
                }
                _ => out.push_str(&text),
            }
        }
        if args.next().is_some() {
            return Err(RuntimeError::runtime("Too many arguments for the format").in_context("printf"));
        }
        Ok(out)
    }

    fn format_with_precision(&mut self, v: &Value, level: Level, precision: Option<usize>, col: usize) -> RResult<String> {
        if let Some(prec) = precision {
            if let Some(s) = crate::intrinsics::reals::format_with_digits(v, prec) {
                return Ok(s);
            }
        }
        // The whole printf output is wrapped afterwards.
        let _ = col;
        let mut p = Printer::new(0, usize::MAX / 2, level);
        p.bare = true;
        self.fmt(&mut p, v, 0)?;
        Ok(p.buf)
    }
}

/// Wrap text at `width` columns with the same rules as the printer.
pub fn wrap_text_output(text: &str, start_col: usize, width: usize) -> String {
    let mut p = Printer::new(start_col, width, Level::Default);
    p.text(text);
    p.buf
}

/// Drop trailing zeros (and a trailing point) from a real's digits.
pub fn trim_real(s: &str) -> String {
    let (mant, exp) = match s.find('E') {
        Some(i) => (&s[..i], &s[i..]),
        None => (s, ""),
    };
    if !mant.contains('.') {
        return s.to_string();
    }
    let m = mant.trim_end_matches('0').trim_end_matches('.');
    let m = if m.is_empty() || m == "-" { "0" } else { m };
    format!("{m}{exp}")
}

