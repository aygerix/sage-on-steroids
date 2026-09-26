//! The `calyx` command-line interface.

mod editor;
mod style;

use std::io::{IsTerminal, Read};
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use calyx_runtime::sym::Sym;
use calyx_runtime::{ExecOutcome, Interp, RuntimeError, Value};
use rustyline::error::ReadlineError;
use rustyline::history::DefaultHistory;
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
  -V            Print the version and exit
  --no-color    Do not use colours in the terminal (also set by NO_COLOR)

Files are run in order. Then, if standard input is a terminal, an
interactive session starts; otherwise statements are read from standard
input. name:=value assigns the string value to the identifier name."
    )
}

fn parse_args() -> Result<Options, String> {
    let mut o = Options { banner: true, seed: None, files: Vec::new(), eval: Vec::new(), assignments: Vec::new(), startup: None, no_startup: false, color: true };
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
            "-V" | "--version" => {
                println!("calyx {VERSION}");
                std::process::exit(0);
            }
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
    // Run on a thread with a large stack so deep recursion in user code works.
    let child = std::thread::Builder::new().stack_size(1 << 30).spawn(move || run(opts)).expect("failed to start interpreter thread");
    let code = child.join().unwrap_or(1);
    std::process::exit(code);
}

fn run(opts: Options) -> i32 {
    style::init(opts.color);
    let mut it = Interp::new();
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
    let text = match std::fs::read_to_string(path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("calyx: cannot read {path}: {e}");
            return None;
        }
    };
    let abs = std::path::Path::new(path).canonicalize().unwrap_or_else(|_| path.into());
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
    // Lines read so far, as Magma numbers them (see `Interp::input_line`).
    let mut counted = 0;
    for line in text.split_inclusive('\n') {
        if buf.is_empty() {
            it.input_line = counted;
        }
        counted += !line.trim().is_empty() as usize;
        if buf.is_empty() {
            if let Some(code) = special_line(it, line) {
                if code >= 0 {
                    return code;
                }
                continue;
            }
        }
        buf.push_str(line);
        match it.execute_continuing(&buf, "", true, &mut |it, e| {
            report(it, e);
            it.out.ensure_newline();
        }) {
            Ok(ExecOutcome::Incomplete) => continue,
            Ok(ExecOutcome::Quit(c)) => return c,
            Ok(ExecOutcome::Done) => buf.clear(),
            Err(e) => {
                report(it, &e);
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
    }
    0
}

/// Handle `?` help and `%` history lines. Returns `Some(-1)` if the line
/// was consumed.
fn special_line(it: &mut Interp, line: &str) -> Option<i32> {
    let t = line.trim();
    if let Some(topic) = t.strip_prefix('?') {
        let text = help_text(it, topic.trim()) + "\n";
        let styled = style::enabled().then(|| style::help(&text));
        it.out.write_styled(&text, styled.as_deref());
        return Some(-1);
    }
    None
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
        .auto_add_history(false)
        .history_ignore_dups(true)
        .and_then(|c| c.max_history_size(10_000))
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
    let mut buf = String::new();
    let code = loop {
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
            Ok(line) => {
                if buf.is_empty() && special_line(it, &line).is_some() {
                    let _ = rl.add_history_entry(line.as_str());
                    continue;
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
