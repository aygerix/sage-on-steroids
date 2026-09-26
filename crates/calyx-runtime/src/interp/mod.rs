//! The tree-walking interpreter.

pub mod assign;
mod call;
mod eval;
mod iter;
mod stmt;

use std::collections::VecDeque;
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;

use calyx_syntax::{FileId, SourceFile, Span};
use rustc_hash::{FxHashMap, FxHashSet};

pub use assign::seq_index;
pub use call::CallArgs;
pub use iter::ValueIter;

use crate::error::{RResult, RuntimeError, TraceFrame};
use crate::intrinsics::IntrinsicTable;
use crate::ir::{FuncCode, Slot};
use crate::output::Output;
use crate::random::Rng;
use crate::sym::Sym;
use crate::types::TypeRegistry;
use crate::value::{Vals, Value};

/// Control flow out of a statement.
pub enum Flow {
    Normal,
    Break(Option<Sym>),
    Continue(Option<Sym>),
    Return(Vals),
}

/// The activation record of a running function or top-level unit.
pub struct Frame {
    pub slots: Vec<Value>,
    pub captures: Rc<[Value]>,
    /// The closure being executed (for `$$`).
    pub self_fn: Option<Value>,
    pub code: Option<Rc<FuncCode>>,
    /// Number of results the caller asked for (for `Nresults`).
    pub nresults: usize,
}

impl Frame {
    pub fn new(n_slots: u32) -> Frame {
        Frame { slots: vec![Value::Undef; n_slots as usize], captures: Rc::from(Vec::new()), self_fn: None, code: None, nresults: 1 }
    }

    #[inline]
    pub fn get(&self, s: Slot) -> &Value {
        &self.slots[s as usize]
    }

    #[inline]
    pub fn set(&mut self, s: Slot, v: Value) {
        self.slots[s as usize] = v;
    }
}

/// A package file that has been attached (or imported).
pub struct Package {
    pub path: PathBuf,
    pub globals: FxHashMap<Sym, Value>,
    pub mtime: Option<std::time::SystemTime>,
}

/// The whole interpreter state.
pub struct Interp {
    pub types: TypeRegistry,
    pub globals: FxHashMap<Sym, Value>,
    /// The slot of each global in Magma's identifier table, whose order
    /// decides which global names a structure they share: a new global
    /// takes the lowest slot a deleted one freed, else a new last slot.
    global_slots: FxHashMap<Sym, u64>,
    free_slots: std::collections::BTreeSet<u64>,
    pub forwards: FxHashSet<Sym>,
    pub intrinsics: IntrinsicTable,
    pub out: Output,
    pub previous: VecDeque<Vec<Value>>,
    pub previous_size: usize,
    pub rng: Rng,
    /// Primes given to `StoreFactor`, tried first by `Factorization`.
    pub stored_factors: Vec<calyx_flint::Integer>,
    /// `RngInt`CunninghamStorageLimit`.
    pub cunningham_storage_limit: i64,
    pub verbose: FxHashMap<Rc<str>, (i64, i64)>,
    pub assertions: i64,
    pub sources: Vec<Rc<SourceFile>>,
    pub trace: Vec<TraceFrame>,
    pub depth: usize,
    pub max_depth: usize,
    /// Results requested from each active user function (for `Nresults`).
    pub nresults_stack: Vec<usize>,
    /// Partial results of enclosing sequence constructors (for `Self`).
    pub self_seqs: Vec<Vec<Value>>,
    /// Variables visible to `eval` code, innermost last.
    pub eval_env: Vec<FxHashMap<Sym, Value>>,
    pub interrupt: Arc<AtomicBool>,
    pub start: Instant,
    pub packages: Vec<Package>,
    /// Globals of the package currently being loaded, if any.
    pub package_stack: Vec<FxHashMap<Sym, Value>>,
    pub quit: Option<i32>,
    pub show_real_time: bool,
    pub indent_level: usize,
    pub indent_width: usize,
    pub search_path: Vec<PathBuf>,
    pub library_root: PathBuf,
    pub libraries: Vec<PathBuf>,
    pub temp_dir: PathBuf,
    pub echo_input: bool,
    pub quit_on_error: bool,
    pub script_args: Vec<String>,
    pub script_name: String,
    pub history: Vec<String>,
    pub history_size: usize,
    pub vi_mode: bool,
    pub prompt: String,
    pub file_stack: Vec<PathBuf>,
    pub profile: bool,
    pub warn_override: bool,
    /// Pending standard-input lines for `read` (used when not interactive).
    pub input_lines: VecDeque<String>,
    pub read_line_hook: Option<Box<dyn FnMut(&str) -> Option<String>>>,
    /// Canonical rings (residue class rings, finite fields, ...).
    pub rings: crate::rings::RingCache,
    /// The symmetric groups, one per degree.
    pub groups: crate::perms::GroupCache,
    /// Emptied vectors of finished calls (arguments and frame slots), for
    /// reuse.
    pub spare_vecs: Vec<Vec<Value>>,
    /// The lines of the main input before the statements being run, blank
    /// ones not counted (see `SourceFile::lines_before`).
    pub input_line: usize,
}

impl Interp {
    pub fn new() -> Interp {
        let types = TypeRegistry::new();
        let mut it = Interp {
            intrinsics: IntrinsicTable::new(),
            types,
            globals: FxHashMap::default(),
            global_slots: FxHashMap::default(),
            free_slots: Default::default(),
            forwards: FxHashSet::default(),
            out: Output::stdout(),
            previous: VecDeque::new(),
            previous_size: 3,
            rng: Rng::from_time(),
            stored_factors: Vec::new(),
            cunningham_storage_limit: 50,
            verbose: FxHashMap::default(),
            assertions: 1,
            sources: Vec::new(),
            trace: Vec::new(),
            depth: 0,
            max_depth: 20_000,
            nresults_stack: Vec::new(),
            self_seqs: Vec::new(),
            eval_env: Vec::new(),
            interrupt: Arc::new(AtomicBool::new(false)),
            start: Instant::now(),
            packages: Vec::new(),
            package_stack: Vec::new(),
            quit: None,
            show_real_time: false,
            indent_level: 0,
            indent_width: 4,
            search_path: Vec::new(),
            library_root: PathBuf::new(),
            libraries: Vec::new(),
            temp_dir: std::env::temp_dir(),
            echo_input: false,
            quit_on_error: false,
            script_args: Vec::new(),
            script_name: String::new(),
            history: Vec::new(),
            history_size: 10_000,
            vi_mode: false,
            prompt: "> ".to_string(),
            file_stack: Vec::new(),
            profile: false,
            warn_override: false,
            input_lines: VecDeque::new(),
            read_line_hook: None,
            rings: Default::default(),
            groups: Default::default(),
            spare_vecs: Vec::new(),
            input_line: 0,
        };
        crate::intrinsics::register_all(&mut it);
        it
    }

    /// Register a source text so spans into it can be reported.
    pub fn add_source(&mut self, name: &str, text: &str) -> FileId {
        let id = FileId(self.sources.len() as u32);
        let mut src = SourceFile::new(name, text);
        if name.is_empty() {
            src.lines_before = self.input_line;
        }
        self.sources.push(Rc::new(src));
        id
    }

    pub fn source(&self, id: FileId) -> Option<Rc<SourceFile>> {
        self.sources.get(id.0 as usize).cloned()
    }

    #[inline]
    pub fn check_interrupt(&self) -> RResult<()> {
        if self.interrupt.load(Ordering::Relaxed) {
            self.interrupt.store(false, Ordering::Relaxed);
            return Err(RuntimeError::interrupt());
        }
        Ok(())
    }

    /// The global value of `name`, falling back to intrinsics and types.
    pub fn lookup_global(&self, name: Sym) -> Option<Value> {
        for env in self.eval_env.iter().rev() {
            if let Some(v) = env.get(&name) {
                return Some(v.clone());
            }
        }
        if let Some(pkg) = self.package_stack.last() {
            if let Some(v) = pkg.get(&name) {
                return Some(v.clone());
            }
        }
        if let Some(v) = self.globals.get(&name) {
            if !v.is_undef() {
                return Some(v.clone());
            }
        }
        self.builtin_value(name)
    }

    /// The value an unassigned identifier denotes: an intrinsic or a type.
    pub fn builtin_value(&self, name: Sym) -> Option<Value> {
        if self.intrinsics.contains(name) {
            return Some(Value::Intr(name));
        }
        let s = name.as_rc();
        self.types.lookup(&s).map(Value::Cat)
    }

    pub fn set_global(&mut self, name: Sym, v: Value) {
        let old = match self.package_stack.last_mut() {
            Some(pkg) => pkg.insert(name, v),
            None => self.globals.insert(name, v),
        };
        if old.is_none() && !self.global_slots.contains_key(&name) {
            let slot = self.free_slots.pop_first().unwrap_or(self.global_slots.len() as u64 + self.free_slots.len() as u64);
            self.global_slots.insert(name, slot);
        }
        self.unbind_name(name, old);
    }

    /// Forget a global identifier, which then reads as undeclared.
    pub fn remove_global(&mut self, name: Sym) {
        let old = match self.package_stack.last_mut() {
            Some(pkg) => pkg.remove(&name),
            None => self.globals.remove(&name),
        };
        self.unbind_name(name, old);
        if let Some(slot) = self.global_slots.remove(&name) {
            self.free_slots.insert(slot);
        }
    }

    /// Replace all user globals after a workspace has been fully decoded.
    pub fn replace_globals(&mut self, values: Vec<(Sym, Value)>) {
        let old: Vec<Sym> = self.globals.keys().copied().collect();
        for name in old {
            self.remove_global(name);
        }
        for (name, value) in values {
            if let Some(cell) = value.name_cell() {
                *cell.borrow_mut() = Some(name);
            }
            self.set_global(name, value);
        }
    }

    /// The slot of a global (undeclared ones come last).
    fn slot(&self, name: Sym) -> u64 {
        self.global_slots.get(&name).copied().unwrap_or(u64::MAX)
    }

    /// Global `n` is assigned the named structure `s`, which goes by the
    /// global in the first slot of those holding it.
    pub fn name_struct(&self, s: &crate::value::Struct, n: Sym) {
        let Some(cur) = *s.name.borrow() else { return };
        if cur == n || s.aliases.borrow().contains(&n) {
            return;
        }
        if self.slot(n) < self.slot(cur) {
            *s.name.borrow_mut() = Some(n);
            s.aliases.borrow_mut().push(cur);
        } else {
            s.aliases.borrow_mut().push(n);
        }
    }

    /// A structure that `name` held no longer goes by it: of the other
    /// globals holding it, the one in the first slot names it, if any.
    fn unbind_name(&self, name: Sym, old: Option<Value>) {
        let Some(Value::Struct(s)) = old else { return };
        let holds = |n: &Sym| matches!(self.lookup_variable(*n), Some(Value::Struct(t)) if Rc::ptr_eq(&t, &s));
        if holds(&name) {
            return;
        }
        let mut aliases = s.aliases.borrow_mut();
        aliases.retain(|n| *n != name && holds(n));
        if *s.name.borrow() == Some(name) {
            let next = (0..aliases.len()).min_by_key(|&i| self.slot(aliases[i]));
            *s.name.borrow_mut() = next.map(|i| aliases.remove(i));
        }
    }

    pub fn unassigned_error(&self, name: Sym) -> RuntimeError {
        // $ outside a constructor.
        if &*name.as_rc() == "$" {
            return RuntimeError::runtime("Bad dollar structure");
        }
        let declared = self.package_stack.last().map_or(false, |p| p.contains_key(&name)) || self.globals.contains_key(&name);
        if declared {
            RuntimeError::user(format!("Identifier '{name}' has not been assigned"))
        } else {
            RuntimeError::user(format!("Identifier '{name}' has not been declared or assigned"))
        }
    }

    /// Record a value list in the previous-value buffer (`$1`, ...).
    pub fn push_previous(&mut self, vals: Vec<Value>) {
        if self.previous_size == 0 {
            return;
        }
        self.previous.push_front(vals);
        while self.previous.len() > self.previous_size {
            self.previous.pop_back();
        }
    }

    /// Run a compiled top-level unit.
    pub fn run_unit(&mut self, code: &Rc<FuncCode>) -> RResult<Flow> {
        let mut frame = Frame::new(code.n_slots);
        frame.code = Some(code.clone());
        match &code.body {
            crate::ir::Body::Block(stmts) => self.exec_block(stmts, &mut frame),
            crate::ir::Body::Expr(e) => {
                let v = self.eval(e, &mut frame)?;
                Ok(Flow::Return(vals![v]))
            }
        }
    }

    /// Attach the error position and a trace frame to an error.
    pub fn locate(&self, mut e: RuntimeError, span: Span) -> RuntimeError {
        if e.span.is_none() && !e.at_caller {
            e.span = Some(span);
        }
        e
    }

    pub fn user_error(msg: impl Into<String>) -> RuntimeError {
        RuntimeError::user(msg)
    }
}

impl Default for Interp {
    fn default() -> Self {
        Interp::new()
    }
}
