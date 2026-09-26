//! The `calyx` command-line interface.

mod build_info;
mod editor;
mod style;

use std::collections::VecDeque;
use std::io::{IsTerminal, Read};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use calyx_runtime::sym::Sym;
use calyx_runtime::{ExecOutcome, Interp, RuntimeError, Value};
use rustyline::config::{Configurer, EditMode};
use rustyline::error::ReadlineError;
use rustyline::history::{DefaultHistory, History as _};
use rustyline::{ColorMode, CompletionType, Editor, EventHandler, KeyCode, KeyEvent, Modifiers};

use editor::{CLOSER_KEYS, CalyxHelper, DedentHandler, EnterHandler, Rewrite};

// Scripts allocate many small values, which mimalloc serves faster than
// the system allocators.
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

const VERSION: &str = env!("CARGO_PKG_VERSION");

struct Options {
    banner: bool,
    seed: Option<(u64, u64)>,
    files: Vec<String>,
    eval: Vec<String>,
    assignments: Vec<(String, String)>,
    startup: Option<String>,
    no_startup: bool,
    color: bool,
    version: bool,
    verbose: bool,
}

struct HistoryEntry {
    number: usize,
    text: String,
    seed: (u64, u64),
}

struct SessionHistory {
    entries: VecDeque<HistoryEntry>,
    next: usize,
}

impl SessionHistory {
    fn new() -> SessionHistory {
        SessionHistory { entries: VecDeque::new(), next: 1 }
    }

    fn push(&mut self, text: String, seed: (u64, u64), limit: usize) {
        if text.trim().is_empty() {
            return;
        }
        let number = self.next;
        self.next += 1;
        if limit != 0 {
            self.entries.push_back(HistoryEntry { number, text, seed });
        }
        self.truncate(limit);
    }

    fn truncate(&mut self, limit: usize) {
        while self.entries.len() > limit {
            self.entries.pop_front();
        }
    }

    fn select(&self, range: Option<(usize, usize)>) -> Vec<&HistoryEntry> {
        match range {
            Some((lo, hi)) => self.entries.iter().filter(|e| lo <= e.number && e.number <= hi).collect(),
            None => self.entries.iter().collect(),
        }
    }

    fn selected_text(&self, range: Option<(usize, usize)>) -> Option<String> {
        let selected = match range {
            Some(r) => self.select(Some(r)),
            None => self.entries.back().map(|e| vec![e]).unwrap_or_default(),
        };
        (!selected.is_empty()).then(|| selected.iter().map(|e| e.text.as_str()).collect::<Vec<_>>().join("\n"))
    }
}

enum SpecialLine {
    Consumed,
    Execute(String),
}

fn usage() -> String {
    format!(
        "calyx {VERSION} - a free computer algebra system compatible with the Magma language

Usage: calyx [options] [name:=value ...] [file ...]

Options:
  -b            Do not print the banner or the exit summary
  -e statement  Execute the statement before any files
  -h            Show this help and exit
  -n            Do not run the startup file
  -s file       Run this startup file
  -S seed       Initial seed for the random number generator
  -V, --version Print the version and exit
  --verbose     With --version, print build and acceleration details
  --no-color    Do not use colours in the terminal (also set by NO_COLOR)

Environment:
  CALYX_STARTUP_FILE   Default startup file
  CALYX_PATH           Colon-separated file search path
  CALYX_LIBRARY_ROOT   Root containing library directories
  CALYX_LIBRARIES      Colon-separated directories below the library root
  CALYX_SYSTEM_SPEC    System package specification file
  CALYX_USER_SPEC      User package specification file
  CALYX_TEMP_DIR       Directory for temporary files

Files are run in order. Then, if standard input is a terminal, an
interactive session starts; otherwise statements are read from standard
input. name:=value assigns the string value to the identifier name."
    )
}

fn parse_args() -> Result<Options, String> {
    let mut o = Options {
        banner: true, seed: None, files: Vec::new(), eval: Vec::new(), assignments: Vec::new(), startup: None, no_startup: false, color: true,
        version: false, verbose: false,
    };
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        match a.as_str() {
            "-b" => o.banner = false,
            "-n" => o.no_startup = true,
            "--no-color" | "--no-colour" => o.color = false,
            "-h" | "--help" => {
                println!("{}", usage());
                std::process::exit(0);
            }
            "-V" | "--version" => o.version = true,
            "--verbose" => o.verbose = true,
            "-e" => o.eval.push(args.next().ok_or("-e needs a statement")?),
            "-s" => o.startup = Some(args.next().ok_or("-s needs a file name")?),
            "-S" => {
                let s = args.next().ok_or("-S needs a seed")?;
                let seed = s.parse().map_err(|_| format!("bad seed '{s}'"))?;
                o.seed = Some((seed, 0));
            }
            _ if a.starts_with('-') && a.len() > 1 => return Err(format!("unknown option '{a}'")),
            _ => {
                if let Some((name, value)) = a.split_once(":=") {
                    o.assignments.push((name.to_string(), value.to_string()));
                } else {
                    o.files.push(a);
                }
            }
        }
    }
    if o.verbose && !o.version {
        return Err("--verbose requires --version".into());
    }
    Ok(o)
}

fn main() {
    // FLINT and GMP still allocate with malloc. glibc raises its mmap
    // threshold when large blocks are freed, but Rust's no longer reach it,
    // so fix the threshold at its maximum: otherwise every large FLINT
    // matrix is a fresh mapping, faulted in page by page.
    #[cfg(all(target_os = "linux", target_env = "gnu"))]
    unsafe {
        libc::mallopt(libc::M_MMAP_THRESHOLD, 32 << 20);
        libc::mallopt(libc::M_TRIM_THRESHOLD, 64 << 20);
    }
    let opts = match parse_args() {
        Ok(o) => o,
        Err(e) => {
            eprintln!("calyx: {e}\n\n{}", usage());
            std::process::exit(2);
        }
    };
    if opts.version {
        if opts.verbose {
            println!("{}", build_info::verbose(VERSION));
        } else {
            println!("calyx {VERSION}");
        }
        return;
    }
    // Run on a thread with a large stack so deep recursion in user code works.
    let child = std::thread::Builder::new().stack_size(1 << 30).spawn(move || run(opts)).expect("failed to start interpreter thread");
    let code = child.join().unwrap_or(1);
    std::process::exit(code);
}

fn run(opts: Options) -> i32 {
    style::init(opts.color);
    let mut it = Interp::new();
    initialize_environment(&mut it);
    if let Some((s, c)) = opts.seed {
        it.rng.set_seed(s, c);
    }
    let flag = it.interrupt.clone();
    let _ = ctrlc::set_handler(move || flag.store(true, Ordering::SeqCst));
    it.script_args = opts.files.clone();
    if let Some(first) = opts.files.first() {
        it.script_name = first.clone();
    }
    for (name, value) in &opts.assignments {
        it.globals.insert(calyx_runtime::sym::Sym::new(name), Value::str(value));
    }

    let interactive = std::io::stdin().is_terminal();
    if opts.banner && interactive {
        let (seed, _) = it.rng.seed();
        print!("{}", style::banner(VERSION, seed));
    }

    for var in ["CALYX_SYSTEM_SPEC", "CALYX_USER_SPEC"] {
        if let Ok(spec) = std::env::var(var) {
            if let Err(e) = it.attach_spec(&spec, false) {
                report(&mut it, &e);
                return finish(&mut it, &opts, 1);
            }
        }
    }

    let startup = if opts.no_startup { None } else { opts.startup.clone().or_else(|| std::env::var("CALYX_STARTUP_FILE").ok()) };
    if let Some(f) = startup {
        if let Some(code) = run_file(&mut it, &f) {
            return finish(&mut it, &opts, code);
        }
    }
    for stmt in &opts.eval {
        if let Some(code) = run_text(&mut it, stmt, "<command line>") {
            return finish(&mut it, &opts, code);
        }
    }
    for f in &opts.files {
        if let Some(code) = run_file(&mut it, f) {
            return finish(&mut it, &opts, code);
        }
    }
    if !interactive {
        // As in Magma, output read from a pipe or file ends where the script's does.
        let code = run_stdin(&mut it);
        it.out.flush();
        return code;
    }
    let code = repl(&mut it);
    finish(&mut it, &opts, code)
}

fn initialize_environment(it: &mut Interp) {
    if let Ok(path) = std::env::var("CALYX_PATH") {
        it.search_path = split_path_list(&path);
    }
    if let Ok(root) = std::env::var("CALYX_LIBRARY_ROOT") {
        it.library_root = PathBuf::from(root);
    }
    if let Ok(libraries) = std::env::var("CALYX_LIBRARIES") {
        it.libraries = split_path_list(&libraries);
    }
    if let Ok(temp) = std::env::var("CALYX_TEMP_DIR") {
        it.temp_dir = PathBuf::from(temp);
    }
}

fn split_path_list(s: &str) -> Vec<PathBuf> {
    s.split(':').filter(|p| !p.is_empty()).map(PathBuf::from).collect()
}

fn finish(it: &mut Interp, opts: &Options, code: i32) -> i32 {
    it.out.ensure_newline();
    if opts.banner && std::io::stdin().is_terminal() {
        let secs = it.start.elapsed().as_secs_f64();
        println!("\n{}", style::dim(&format!("Total time: {secs:.3} seconds")));
    }
    it.out.flush();
    code
}

fn report(it: &mut Interp, e: &RuntimeError) {
    it.out.ensure_newline();
    let text = it.format_error(e);
    let styled = style::enabled().then(|| style::error(&text, &|w| it.intrinsics.contains(Sym::new(w))));
    it.out.write_styled(&text, styled.as_deref());
    it.out.flush();
}

/// Run a file; returns `Some(exit code)` if it executed `quit`.
fn run_file(it: &mut Interp, path: &str) -> Option<i32> {
    let resolved = resolve_file(it, path);
    let text = match std::fs::read_to_string(&resolved) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("calyx: cannot read {path}: {e}");
            return None;
        }
    };
    let abs = resolved.canonicalize().unwrap_or(resolved);
    it.file_stack.push(abs);
    let r = it.execute(&text, path, false);
    it.file_stack.pop();
    match r {
        Ok(ExecOutcome::Quit(c)) => Some(c),
        Ok(_) => None,
        Err(e) => {
            report(it, &e);
            if it.quit_on_error { Some(1) } else { None }
        }
    }
}

fn resolve_file(it: &Interp, name: &str) -> PathBuf {
    let path = Path::new(name);
    if path.is_absolute() || path.exists() {
        return path.to_path_buf();
    }
    for dir in &it.search_path {
        let candidate = dir.join(path);
        if candidate.exists() {
            return candidate;
        }
    }
    for dir in &it.libraries {
        let candidate = it.library_root.join(dir).join(path);
        if candidate.exists() {
            return candidate;
        }
    }
    path.to_path_buf()
}

fn run_text(it: &mut Interp, text: &str, name: &str) -> Option<i32> {
    match it.execute(text, name, false) {
        Ok(ExecOutcome::Quit(c)) => Some(c),
        Ok(_) => None,
        Err(e) => {
            report(it, &e);
            if it.quit_on_error { Some(1) } else { None }
        }
    }
}

/// Read statements from a non-terminal standard input, continuing after
/// errors the way an interactive session does.
fn run_stdin(it: &mut Interp) -> i32 {
    let mut text = String::new();
    if std::io::stdin().read_to_string(&mut text).is_err() {
        return 1;
    }
    let mut buf = String::new();
    let mut entry_seed = it.rng.seed();
    let mut history = SessionHistory::new();
    // Lines read so far, as Magma numbers them (see `Interp::input_line`).
    let mut counted = 0;
    for line in text.split_inclusive('\n') {
        history.truncate(it.history_size);
        if buf.is_empty() {
            it.input_line = counted;
        }
        counted += !line.trim().is_empty() as usize;
        let mut recalled = None;
        if buf.is_empty() {
            match special_line(it, &mut history, line) {
                Some(SpecialLine::Consumed) => continue,
                Some(SpecialLine::Execute(src)) => {
                    show_recalled(it, &src);
                    recalled = Some(src);
                }
                None => {}
            }
            entry_seed = it.rng.seed();
        }
        if let Some(src) = &recalled {
            buf.push_str(src);
            if !src.ends_with('\n') {
                buf.push('\n');
            }
        } else {
            buf.push_str(line);
        }
        match it.execute_continuing(&buf, "", true, &mut |it, e| {
            report(it, e);
            it.out.ensure_newline();
        }) {
            Ok(ExecOutcome::Incomplete) => continue,
            Ok(ExecOutcome::Quit(c)) => return c,
            Ok(ExecOutcome::Done) => {
                history.push(buf.trim_end().to_string(), entry_seed, it.history_size);
                buf.clear();
            }
            Err(e) => {
                report(it, &e);
                history.push(buf.trim_end().to_string(), entry_seed, it.history_size);
                buf.clear();
                if it.quit_on_error {
                    return 1;
                }
            }
        }
    }
    if !buf.trim().is_empty() {
        if let Err(e) = it.execute(&buf, "", false) {
            report(it, &e);
        }
        history.push(buf.trim_end().to_string(), entry_seed, it.history_size);
    }
    0
}

/// Handle `?` help and `%` history lines.
fn special_line(it: &mut Interp, history: &mut SessionHistory, line: &str) -> Option<SpecialLine> {
    let t = line.trim();
    if let Some(topic) = t.strip_prefix('?') {
        let text = help_text(it, topic.trim()) + "\n";
        let styled = style::enabled().then(|| style::help(&text));
        it.out.write_styled(&text, styled.as_deref());
        return Some(SpecialLine::Consumed);
    }
    let command = t.strip_prefix('%')?;
    if let Some(shell) = command.strip_prefix('!') {
        it.out.flush();
        let _ = std::process::Command::new("sh").arg("-c").arg(shell.trim_start()).status();
        return Some(SpecialLine::Consumed);
    }
    let (kind, range_text) = match command.chars().next() {
        Some(c @ ('p' | 'P' | 's' | 'S' | 'e')) => (Some(c), &command[c.len_utf8()..]),
        _ => (None, command),
    };
    let range = match parse_history_range(range_text) {
        Ok(r) => r,
        Err(()) => {
            it.out.write("Invalid history range\n");
            return Some(SpecialLine::Consumed);
        }
    };
    match kind {
        Some('p') | Some('P') | Some('s') | Some('S') => {
            let selected = history.select(range);
            let numbered = matches!(kind, Some('p'));
            let seeds = matches!(kind, Some('s') | Some('S'));
            let compact = matches!(kind, Some('S'));
            let full = range.is_none();
            write_history(it, &selected, numbered, seeds, compact, full);
            Some(SpecialLine::Consumed)
        }
        Some('e') => {
            let Some(text) = history.selected_text(range) else {
                it.out.write("History line not found\n");
                return Some(SpecialLine::Consumed);
            };
            edit_history(it, &text).map(SpecialLine::Execute).or(Some(SpecialLine::Consumed))
        }
        None => {
            let Some(text) = history.selected_text(range) else {
                it.out.write("History line not found\n");
                return Some(SpecialLine::Consumed);
            };
            Some(SpecialLine::Execute(text))
        }
        _ => Some(SpecialLine::Consumed),
    }
}

fn parse_history_range(s: &str) -> Result<Option<(usize, usize)>, ()> {
    let fields: Vec<&str> = s.split_whitespace().collect();
    match &fields[..] {
        [] => Ok(None),
        [n] => n.parse().map(|n| Some((n, n))).map_err(|_| ()),
        [lo, hi] => {
            let lo: usize = lo.parse().map_err(|_| ())?;
            let hi: usize = hi.parse().map_err(|_| ())?;
            if lo <= hi { Ok(Some((lo, hi))) } else { Err(()) }
        }
        _ => Err(()),
    }
}

fn write_history(it: &mut Interp, entries: &[&HistoryEntry], numbered: bool, seeds: bool, compact: bool, full: bool) {
    let mut last_seed = None;
    for e in entries {
        if numbered {
            let prefix = if full || entries.len() >= 3 { format!("/* {:>2} */   ", e.number) } else { format!("/* {} */   ", e.number) };
            it.out.write(&prefix);
        }
        if seeds && (!compact || last_seed != Some(e.seed)) {
            it.out.write(&format!("SetSeed({}, {}); ", e.seed.0, e.seed.1));
        }
        it.out.write(&e.text);
        if !e.text.ends_with('\n') {
            it.out.write("\n");
        }
        last_seed = Some(e.seed);
    }
}

fn show_recalled(it: &mut Interp, text: &str) {
    it.out.write(">> ");
    it.out.write(text);
    if !text.ends_with('\n') {
        it.out.write("\n");
    }
}

fn edit_history(it: &mut Interp, text: &str) -> Option<String> {
    let stamp = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).ok()?.as_nanos();
    let path = it.temp_dir.join(format!("calyx-history-{}-{stamp}.m", std::process::id()));
    if std::fs::write(&path, text).is_err() {
        it.out.write("Could not create history edit file\n");
        return None;
    }
    let editor = std::env::var("EDITOR").unwrap_or_else(|_| "/bin/ed".to_string());
    it.out.flush();
    let ok = std::process::Command::new(editor).arg(&path).status().is_ok_and(|s| s.success());
    let edited = ok.then(|| std::fs::read_to_string(&path).ok()).flatten();
    let _ = std::fs::remove_file(path);
    edited.filter(|s| s != text)
}

fn help_text(it: &Interp, topic: &str) -> String {
    if topic.is_empty() {
        return "\
Statements end with a semicolon; Enter on an unfinished statement starts a
new line. Type quit; or <Ctrl>-D to leave.

  ?Name      signatures of the intrinsic Name, e.g. ?Gcd
  Tab        complete the names of intrinsics, keywords and variables
             (and file names inside strings)
  Ctrl-R     search the history
  %p         list the history (%P omits line numbers)
  %n         reenter history line n (% repeats the last line)
  Ctrl-C     interrupt a computation or discard the current input"
            .to_string();
    }
    let sym = Sym::new(topic);
    if it.intrinsics.contains(sym) {
        return it.describe_intrinsic(sym);
    }
    let mut close: Vec<String> = it.intrinsics.names().map(|n| n.to_string()).filter(|n| n.to_lowercase().contains(&topic.to_lowercase())).collect();
    close.sort();
    close.truncate(40);
    if close.is_empty() {
        format!("No intrinsic named '{topic}'.")
    } else {
        format!("No intrinsic named '{topic}'. Similar names:\n  {}", close.join("\n  "))
    }
}

fn repl(it: &mut Interp) -> i32 {
    let color = style::enabled();
    let config = rustyline::Config::builder()
        .completion_type(CompletionType::List)
        .color_mode(if color { ColorMode::Enabled } else { ColorMode::Disabled })
        .edit_mode(if it.vi_mode { EditMode::Vi } else { EditMode::Emacs })
        .auto_add_history(false)
        .history_ignore_dups(true)
        .and_then(|c| c.max_history_size(it.history_size))
        .map(|c| c.build())
        .unwrap_or_default();
    let mut rl: Editor<CalyxHelper, DefaultHistory> = match Editor::with_config(config) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("calyx: cannot start line editor: {e}");
            return run_stdin(it);
        }
    };
    let rewrite = Rewrite::default();
    rl.set_helper(Some(CalyxHelper::new(color, rewrite.clone())));
    let prompt_width = Arc::new(AtomicUsize::new(0));
    rl.bind_sequence(KeyEvent(KeyCode::Enter, Modifiers::NONE), EventHandler::Conditional(Box::new(EnterHandler { prompt_width: prompt_width.clone() })));
    for &c in CLOSER_KEYS {
        let handler = DedentHandler { prompt_width: prompt_width.clone(), rewrite: rewrite.clone() };
        rl.bind_sequence(KeyEvent::from(c), EventHandler::Conditional(Box::new(handler)));
    }
    let history = std::env::var("HOME").map(|h| std::path::PathBuf::from(h).join(".calyx_history")).ok();
    if let Some(h) = &history {
        let _ = rl.load_history(h);
    }
    let mut session_history = SessionHistory::new();
    for entry in rl.history().iter() {
        session_history.push(entry.clone(), it.rng.seed(), it.history_size);
    }
    let mut applied_history_size = it.history_size;
    let mut applied_vi_mode = it.vi_mode;
    let mut buf = String::new();
    let mut entry_seed = it.rng.seed();
    let code = loop {
        if it.history_size != applied_history_size {
            session_history.truncate(it.history_size);
            let _ = rl.history_mut().set_max_len(it.history_size);
            applied_history_size = it.history_size;
        }
        if it.vi_mode != applied_vi_mode {
            rl.set_edit_mode(if it.vi_mode { EditMode::Vi } else { EditMode::Emacs });
            applied_vi_mode = it.vi_mode;
        }
        it.out.ensure_newline();
        it.out.flush();
        if let Some(h) = rl.helper_mut() {
            h.refresh(it);
        }
        // Input that the editor accepted although it was unfinished (for
        // example pasted text) continues on a blank prompt of the same width.
        let width = it.prompt.chars().count();
        prompt_width.store(width, Ordering::Relaxed);
        let prompt = if buf.is_empty() { it.prompt.clone() } else { " ".repeat(width) };
        match rl.readline(&prompt) {
            Ok(mut line) => {
                if buf.is_empty() {
                    match special_line(it, &mut session_history, &line) {
                        Some(SpecialLine::Consumed) => continue,
                        Some(SpecialLine::Execute(src)) => {
                            show_recalled(it, &src);
                            line = src;
                        }
                        None => {}
                    }
                    entry_seed = it.rng.seed();
                }
                buf.push_str(&line);
                buf.push('\n');
                it.interrupt.store(false, Ordering::SeqCst);
                match it.execute_continuing(&buf, "", true, &mut |it, e| {
                    report(it, e);
                    it.out.ensure_newline();
                }) {
                    Ok(ExecOutcome::Incomplete) => continue,
                    Ok(ExecOutcome::Quit(c)) => break c,
                    Ok(ExecOutcome::Done) => {}
                    Err(e) => report(it, &e),
                }
                let entry = buf.trim_end().to_string();
                session_history.push(entry.clone(), entry_seed, it.history_size);
                let _ = rl.add_history_entry(entry.as_str());
                buf.clear();
            }
            Err(ReadlineError::Interrupted) => {
                buf.clear();
            }
            Err(ReadlineError::Eof) => break 0,
            Err(e) => {
                eprintln!("calyx: {e}");
                break 1;
            }
        }
    };
    if let Some(h) = &history {
        let _ = rl.save_history(h);
    }
    code
}
