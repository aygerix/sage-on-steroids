//! Input and output intrinsics: files, pipes, redirection, loading.

use std::io::{Read as _, Write};
use std::rc::Rc;

use super::{boolv, none, one};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::print::Level;
use crate::value::*;

/// The string returned by `Gets` and friends at end of file.
pub const EOF_MARKER: &str = "\u{0}EOF";

impl Interp {
    /// Append text to a file named by a string, or write to an open file.
    pub fn write_to_file_value(&mut self, target: &Value, text: &str) -> RResult<()> {
        match target {
            Value::Str(name) => {
                let mut f = std::fs::OpenOptions::new().create(true).append(true).open(name.as_str()).map_err(|e| RuntimeError::runtime(format!("Could not open file \"{name}\": {e}")))?;
                f.write_all(text.as_bytes()).map_err(|e| RuntimeError::runtime(e.to_string()))
            }
            Value::Io(io) => match &mut *io.state.borrow_mut() {
                IoState::Writer(f) => f.write_all(text.as_bytes()).map_err(|e| RuntimeError::runtime(e.to_string())),
                IoState::PipeWriter { stdin: Some(f), .. } => f.write_all(text.as_bytes()).map_err(|e| RuntimeError::runtime(e.to_string())),
                _ => Err(RuntimeError::runtime("File is not open for writing")),
            },
            _ => Err(RuntimeError::runtime("Bad file argument")),
        }
    }
}

fn open_for_write(name: &str, overwrite: bool) -> RResult<std::fs::File> {
    let mut o = std::fs::OpenOptions::new();
    o.create(true);
    if overwrite {
        o.write(true).truncate(true);
    } else {
        o.append(true);
    }
    o.open(name).map_err(|e| RuntimeError::runtime(format!("Could not open file \"{name}\": {e}")))
}

fn print_file(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let name = a.str(0)?.to_string();
    let x = a.args[1].clone();
    let level = if a.args.len() > 2 {
        let l = a.str(2)?;
        Level::parse(l).ok_or_else(|| RuntimeError::runtime(format!("Unknown print level '{l}'")))?
    } else {
        Level::Default
    };
    let text = it.format_value(&x, level)?;
    let mut f = open_for_write(&name, a.param_bool("Overwrite")?)?;
    writeln!(f, "{text}").map_err(|e| RuntimeError::runtime(e.to_string()))?;
    none()
}

fn print_file_magma(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let name = a.str(0)?.to_string();
    let x = a.args[1].clone();
    let text = it.format_value(&x, Level::Magma)?;
    let mut f = open_for_write(&name, a.param_bool("Overwrite")?)?;
    writeln!(f, "{text}").map_err(|e| RuntimeError::runtime(e.to_string()))?;
    none()
}

fn set_output_file(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let f = open_for_write(a.str(0)?, a.param_bool("Overwrite")?)?;
    it.out.redirect_to_file(f);
    none()
}

fn unset_output_file(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    it.out.unredirect();
    none()
}

fn has_output_file(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    boolv(it.out.has_redirect())
}

fn set_log_file(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    it.out.log = Some(open_for_write(a.str(0)?, a.param_bool("Overwrite")?)?);
    none()
}

fn unset_log_file(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    it.out.log = None;
    none()
}

fn read_file(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let name = a.str(0)?;
    let text = std::fs::read_to_string(name).map_err(|e| RuntimeError::runtime(format!("Could not read file \"{name}\": {e}")))?;
    one(Value::str(&text))
}

fn read_binary(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let name = a.str(0)?;
    let data = std::fs::read(name).map_err(|e| RuntimeError::runtime(format!("Could not read file \"{name}\": {e}")))?;
    one(Value::bytes(data))
}

fn write_binary(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let name = a.str(0)?;
    let Value::BStr(data) = &a.args[1] else { unreachable!() };
    let mut f = open_for_write(name, a.param_bool("Overwrite")?)?;
    f.write_all(data).map_err(|e| RuntimeError::runtime(e.to_string()))?;
    none()
}

fn open(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let name = a.str(0)?.to_string();
    let mode = a.str(1)?.to_string();
    let state = open_state(&name, &mode)?;
    one(Value::Io(Rc::new(IoObj { name, mode, kind: IoKind::File, state: std::cell::RefCell::new(state) })))
}

fn open_state(name: &str, mode: &str) -> RResult<IoState> {
    Ok(match mode.chars().next() {
        Some('r') => IoState::Reader { data: std::fs::read(name).map_err(|e| RuntimeError::runtime(format!("Could not open file \"{name}\": {e}")))?, pos: 0 },
        Some('w') => IoState::Writer(open_for_write(name, true)?),
        Some('a') => IoState::Writer(open_for_write(name, false)?),
        _ => return Err(RuntimeError::runtime(format!("Bad mode \"{mode}\""))),
    })
}

fn open_test(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let name = a.str(0)?.to_string();
    let mode = a.str(1)?.to_string();
    match open_state(&name, &mode) {
        Ok(state) => Ok(vals![Value::Bool(true), Value::Io(Rc::new(IoObj { name, mode, kind: IoKind::File, state: std::cell::RefCell::new(state) }))]),
        Err(_) => Ok(vals![Value::Bool(false), Value::Undef]),
    }
}

fn io_arg(a: &CallArgs, i: usize) -> Rc<IoObj> {
    match &a.args[i] {
        Value::Io(io) => io.clone(),
        _ => unreachable!(),
    }
}

fn read_raw(io: &Rc<IoObj>, count: Option<usize>) -> RResult<Vec<u8>> {
    let mut st = io.state.borrow_mut();
    match &mut *st {
        IoState::Reader { data, pos } => {
            if *pos >= data.len() {
                return Ok(Vec::new());
            }
            let end = count.map_or(data.len(), |n| pos.saturating_add(n).min(data.len()));
            let out = data[*pos..end].to_vec();
            *pos = end;
            Ok(out)
        }
        IoState::PipeReader { child, stdout, eof } => {
            if *eof {
                return Ok(Vec::new());
            }
            let mut out = Vec::new();
            match count {
                Some(n) => {
                    out.resize(n, 0);
                    let mut got = 0;
                    while got < n {
                        match stdout.read(&mut out[got..]) {
                            Ok(0) => {
                                *eof = true;
                                break;
                            }
                            Ok(k) => got += k,
                            Err(e) => return Err(RuntimeError::runtime(e.to_string())),
                        }
                    }
                    out.truncate(got);
                }
                None => {
                    stdout.read_to_end(&mut out).map_err(|e| RuntimeError::runtime(e.to_string()))?;
                    *eof = true;
                }
            }
            if *eof {
                let _ = child.wait();
            }
            Ok(out)
        }
        _ => Err(RuntimeError::runtime("File is not open for reading")),
    }
}

fn read_io(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let io = io_arg(a, 0);
    let data = read_raw(&io, if a.args.len() > 1 { Some(a.usize(1)?) } else { None })?;
    if data.is_empty() {
        return one(Value::str(EOF_MARKER));
    }
    one(Value::str(&String::from_utf8_lossy(&data)))
}

fn gets(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let io = io_arg(a, 0);
    let mut line = Vec::new();
    let mut hit_eof = false;
    loop {
        let b = read_raw(&io, Some(1))?;
        if b.is_empty() {
            hit_eof = true;
            break;
        }
        if b[0] == b'\n' {
            break;
        }
        line.push(b[0]);
    }
    if line.is_empty() && hit_eof {
        return one(Value::str(EOF_MARKER));
    }
    one(Value::str(&String::from_utf8_lossy(&line)))
}

fn getc(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let io = io_arg(a, 0);
    let data = read_raw(&io, Some(1))?;
    if data.is_empty() {
        return one(Value::str(EOF_MARKER));
    }
    let c = data[0] as char;
    one(Value::str(&c.to_string()))
}

fn ungetc(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let io = io_arg(a, 0);
    match &mut *io.state.borrow_mut() {
        IoState::Reader { pos, .. } => *pos = pos.saturating_sub(1),
        _ => return Err(RuntimeError::runtime("Channel does not support Ungetc")),
    }
    none()
}

fn puts(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let text = format!("{}\n", a.str(1)?);
    let t = a.args[0].clone();
    it.write_to_file_value(&t, &text)?;
    none()
}

fn put(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let text = a.str(1)?.to_string();
    let t = a.args[0].clone();
    it.write_to_file_value(&t, &text)?;
    none()
}

fn flush(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    if let Some(Value::Io(io)) = a.args.first() {
        match &mut *io.state.borrow_mut() {
            IoState::Writer(f) => f.flush().map_err(|e| RuntimeError::runtime(e.to_string()))?,
            IoState::PipeWriter { stdin: Some(f), .. } => f.flush().map_err(|e| RuntimeError::runtime(e.to_string()))?,
            _ => {}
        }
    }
    it.out.flush();
    none()
}

fn tell(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let io = io_arg(a, 0);
    let p = match &mut *io.state.borrow_mut() {
        IoState::Reader { pos, .. } => *pos as i64,
        IoState::Writer(f) => std::io::Seek::stream_position(f).map(|p| p as i64).unwrap_or(0),
        IoState::PipeReader { .. } | IoState::PipeWriter { .. } | IoState::Closed => 0,
    };
    one(Value::int(p))
}

fn seek(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let io = io_arg(a, 0);
    let off = a.usize(1)?;
    if let IoState::Reader { pos, data } = &mut *io.state.borrow_mut() {
        *pos = off.min(data.len());
    }
    none()
}

fn rewind(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let io = io_arg(a, 0);
    if let IoState::Reader { pos, .. } = &mut *io.state.borrow_mut() {
        *pos = 0;
    }
    none()
}

fn eof(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::str(EOF_MARKER))
}

fn is_eof(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(a.str(0)? == EOF_MARKER)
}

fn at_eof(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let io = io_arg(a, 0);
    boolv(at_eof_value(&io))
}

fn at_eof_value(io: &IoObj) -> bool {
    match &*io.state.borrow() {
        IoState::Reader { data, pos } => *pos >= data.len(),
        IoState::PipeReader { eof, .. } => *eof,
        _ => true,
    }
}

fn io_type(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let io = io_arg(a, 0);
    one(Value::str(match io.kind {
        IoKind::File => "file",
        IoKind::Pipe => "pipe",
        IoKind::Socket => "socket",
    }))
}

fn popen(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let cmd = a.str(0)?.to_string();
    let mode = a.str(1)?.to_string();
    let mut command = std::process::Command::new("sh");
    command.arg("-c").arg(&cmd);
    let state = match mode.as_str() {
        "r" => {
            let mut child = command.stdin(std::process::Stdio::null()).stdout(std::process::Stdio::piped()).spawn().map_err(|e| RuntimeError::runtime(e.to_string()))?;
            let stdout = child.stdout.take().ok_or_else(|| RuntimeError::runtime("Could not open process output"))?;
            IoState::PipeReader { child, stdout, eof: false }
        }
        "w" => {
            let mut child = command.stdin(std::process::Stdio::piped()).spawn().map_err(|e| RuntimeError::runtime(e.to_string()))?;
            let stdin = child.stdin.take().ok_or_else(|| RuntimeError::runtime("Could not open process input"))?;
            IoState::PipeWriter { child, stdin: Some(stdin) }
        }
        _ => return Err(RuntimeError::runtime(format!("Bad mode \"{mode}\""))),
    };
    one(Value::Io(Rc::new(IoObj { name: cmd, mode, kind: IoKind::Pipe, state: std::cell::RefCell::new(state) })))
}

fn system(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    it.out.flush();
    let status = std::process::Command::new("sh").arg("-c").arg(a.str(0)?).status().map_err(|e| RuntimeError::runtime(e.to_string()))?;
    one(Value::int(status.code().unwrap_or(-1) as i64 * 256))
}

fn pipe(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let cmd = a.str(0)?.to_string();
    let input = a.str(1)?.to_string();
    let mut child = std::process::Command::new("sh")
        .arg("-c")
        .arg(&cmd)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .spawn()
        .map_err(|e| RuntimeError::runtime(e.to_string()))?;
    if let Some(mut stdin) = child.stdin.take() {
        let _ = stdin.write_all(input.as_bytes());
    }
    let out = child.wait_with_output().map_err(|e| RuntimeError::runtime(e.to_string()))?;
    one(Value::str(&String::from_utf8_lossy(&out.stdout)))
}

fn get_env(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::str(&std::env::var(a.str(0)?).unwrap_or_default()))
}

fn change_directory(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    std::env::set_current_dir(a.str(0)?).map_err(|e| RuntimeError::runtime(e.to_string()))?;
    none()
}

fn get_current_directory(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::str(&std::env::current_dir().map(|p| p.display().to_string()).unwrap_or_default()))
}

fn getpid(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::int(std::process::id() as i64))
}

fn getuid(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    unsafe extern "C" {
        fn getuid() -> u32;
    }
    one(Value::int(unsafe { getuid() } as i64))
}

fn tempname(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let prefix = a.str(0)?.to_string();
    let r = it.rng.next_u64();
    one(Value::str(&format!("{prefix}{:06x}{}", r & 0xffffff, std::process::id())))
}

fn load(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    match &a.args[0] {
        Value::Str(s) => {
            let s = s.to_string();
            it.load_file(&s)?;
        }
        Value::Seq(q) => {
            for f in q.elems.clone() {
                if let Value::Str(s) = f {
                    it.load_file(&s)?;
                }
            }
        }
        _ => unreachable!(),
    }
    none()
}

fn attach(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let s = a.str(0)?.to_string();
    it.attach(&s)?;
    none()
}

fn detach(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let s = a.str(0)?.to_string();
    it.detach(&s)?;
    none()
}

fn attach_spec(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let s = a.str(0)?.to_string();
    it.attach_spec(&s, false)?;
    none()
}

fn detach_spec(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let s = a.str(0)?.to_string();
    it.attach_spec(&s, true)?;
    none()
}

fn show_previous(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let entries: Vec<(usize, Vec<Value>)> = if a.args.is_empty() {
        it.previous.iter().cloned().enumerate().map(|(i, v)| (i + 1, v)).collect()
    } else {
        let i = a.usize(0)?;
        match it.previous.get(i.wrapping_sub(1)) {
            Some(v) => vec![(i, v.clone())],
            None => return Err(RuntimeError::runtime(format!("There is no previous value ${i}"))),
        }
    };
    for (i, vals) in entries {
        it.out.write(&format!("${i}: "));
        it.print_values(&vals, Level::Default)?;
    }
    none()
}

fn clear_previous(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    it.previous.clear();
    none()
}

fn set_previous_size(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    it.previous_size = a.usize(0)?;
    while it.previous.len() > it.previous_size {
        it.previous.pop_back();
    }
    none()
}

fn get_previous_size(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::int(it.previous_size as i64))
}

fn indent_push(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let c = if a.args.is_empty() { 1 } else { a.usize(0)? };
    it.indent_level += c;
    none()
}

fn indent_pop(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let c = if a.args.is_empty() { 1 } else { a.usize(0)? };
    if it.indent_level < c {
        return Err(RuntimeError::runtime("The indentation level is already zero"));
    }
    it.indent_level -= c;
    none()
}

fn set_echo_input(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    it.echo_input = a.bool(0)?;
    none()
}

pub fn register(it: &mut Interp) {
    let ow = [("Overwrite", Value::Bool(false))];
    for name in ["PrintFile", "Write"] {
        it.def_params(name, "F::MonStgElt, x::.", &ow, "Print x to the file F (appending unless Overwrite is true).", print_file);
        it.def_params(name, "F::MonStgElt, x::., L::MonStgElt", &ow, "Print x at print level L to the file F.", print_file);
    }
    it.def_params("PrintFileMagma", "F::MonStgElt, x::.", &ow, "Print x in Magma format to the file F.", print_file_magma);
    it.def_params("WriteBinary", "F::MonStgElt, s::BStgElt", &ow, "Write the bytes of s to the file F.", write_binary);
    it.def_params("SetOutputFile", "F::MonStgElt", &ow, "Redirect all output to the file F.", set_output_file);
    it.def("UnsetOutputFile", "", "Send output to standard output again.", unset_output_file);
    it.def("HasOutputFile", "-> BoolElt", "Whether output is redirected to a file.", has_output_file);
    it.def_params("SetLogFile", "F::MonStgElt", &ow, "Copy all input and output to the file F.", set_log_file);
    it.def("UnsetLogFile", "", "Stop logging.", unset_log_file);
    it.def("SetEchoInput", "b::BoolElt", "Whether to echo input read from files.", set_echo_input);
    it.def("Read", "F::MonStgElt -> MonStgElt", "The contents of the file F.", read_file);
    it.def("ReadBinary", "F::MonStgElt -> BStgElt", "The contents of the file F as a binary string.", read_binary);
    it.def("Open", "F::MonStgElt, M::MonStgElt -> IO", "Open the file F with mode \"r\", \"w\" or \"a\".", open);
    it.def("OpenTest", "F::MonStgElt, M::MonStgElt -> BoolElt, IO", "Try to open the file F; return whether this succeeded and the file.", open_test);
    it.def("POpen", "C::MonStgElt, M::MonStgElt -> IO", "Run C and open a one-way pipe with mode \"r\" or \"w\".", popen);
    it.def("Read", "I::IO -> MonStgElt", "The remaining contents of I.", read_io);
    it.def("Read", "I::IO, n::RngIntElt -> MonStgElt", "Up to n characters from I.", read_io);
    it.def("Gets", "I::IO -> MonStgElt", "The next line of I (without its newline).", gets);
    it.def("Getc", "I::IO -> MonStgElt", "The next character of I.", getc);
    it.def("Ungetc", "I::IO, c::MonStgElt", "Push back the last character read from I.", ungetc);
    it.def("Puts", "I::., s::MonStgElt", "Write s and a newline to I.", puts);
    it.def("Put", "I::., s::MonStgElt", "Write s to I.", put);
    it.def("Write", "I::IO, s::MonStgElt", "Write s to I.", put);
    it.def("Flush", "I::IO", "Flush buffered output of I.", flush);
    it.def("Flush", "", "Flush standard output.", flush);
    it.def("Tell", "I::IO -> RngIntElt", "The current position in I.", tell);
    it.def("Seek", "I::IO, n::RngIntElt", "Move to position n in I.", seek);
    it.def("Rewind", "I::IO", "Move to the start of I.", rewind);
    it.def("Eof", "-> MonStgElt", "The end-of-file marker returned by reading functions.", eof);
    it.def("IsEof", "S::MonStgElt -> BoolElt", "Whether S is the end-of-file marker.", is_eof);
    it.def("AtEof", "I::IO -> BoolElt", "Whether I is at end of file.", at_eof);
    it.def("IOType", "I::IO -> MonStgElt", "The kind of I/O object I is.", io_type);
    it.def("System", "C::MonStgElt -> RngIntElt", "Run the shell command C and return its status.", system);
    it.def("Pipe", "C::MonStgElt, S::MonStgElt -> MonStgElt", "Run the shell command C with input S and return its output.", pipe);
    it.def("GetEnv", "S::MonStgElt -> MonStgElt", "The value of the environment variable S.", get_env);
    it.def("GetEnvironmentValue", "S::MonStgElt -> MonStgElt", "The value of the environment variable S.", get_env);
    it.def("ChangeDirectory", "S::MonStgElt", "Change the working directory.", change_directory);
    it.def("GetCurrentDirectory", "-> MonStgElt", "The working directory.", get_current_directory);
    it.def("Getpid", "-> RngIntElt", "The process id.", getpid);
    it.def("Getuid", "-> RngIntElt", "The user id.", getuid);
    it.def("Tempname", "P::MonStgElt -> MonStgElt", "A new file name starting with P.", tempname);
    it.def("Load", "F::MonStgElt", "Run the statements in the file F.", load);
    it.def("Load", "F::[MonStgElt]", "Run the statements in each of the files.", load);
    it.def("Attach", "F::MonStgElt", "Attach the package file F.", attach);
    it.def("Detach", "F::MonStgElt", "Detach the package file F.", detach);
    it.def("AttachSpec", "S::MonStgElt", "Attach the packages listed in the spec file S.", attach_spec);
    it.def("DetachSpec", "S::MonStgElt", "Detach the packages listed in the spec file S.", detach_spec);
    it.def("ShowPrevious", "", "Show the previous values ($1, $2, ...).", show_previous);
    it.def("ShowPrevious", "i::RngIntElt", "Show the i-th previous value.", show_previous);
    it.def("ClearPrevious", "", "Forget the previous values.", clear_previous);
    it.def("SetPreviousSize", "n::RngIntElt", "Keep n previous values.", set_previous_size);
    it.def("GetPreviousSize", "-> RngIntElt", "The number of previous values kept.", get_previous_size);
    it.def("IndentPush", "", "Increase the output indentation level.", indent_push);
    it.def("IndentPush", "C::RngIntElt", "Increase the output indentation level by C.", indent_push);
    it.def("IndentPop", "", "Decrease the output indentation level.", indent_pop);
    it.def("IndentPop", "C::RngIntElt", "Decrease the output indentation level by C.", indent_pop);
}
