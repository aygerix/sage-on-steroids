//! Environment, timing, verbosity and session intrinsics.

use std::rc::Rc;

use super::reals::{timing_seconds, timing_value};
use super::{boolv, none, one};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::print::Level;
use crate::sym::Sym;
use crate::value::*;

/// CPU time used by this process, in seconds.
pub fn cpu_time() -> f64 {
    let mut ru: Rusage = unsafe { std::mem::zeroed() };
    unsafe { getrusage(0, &mut ru) };
    ru.ru_utime.tv_sec as f64 + ru.ru_utime.tv_usec as f64 / 1e6 + ru.ru_stime.tv_sec as f64 + ru.ru_stime.tv_usec as f64 / 1e6
}

/// Peak resident memory in bytes.
pub fn max_rss() -> i64 {
    let mut ru: Rusage = unsafe { std::mem::zeroed() };
    unsafe { getrusage(0, &mut ru) };
    if cfg!(target_os = "macos") { ru.ru_maxrss } else { ru.ru_maxrss * 1024 }
}

#[repr(C)]
struct Timeval {
    tv_sec: i64,
    tv_usec: i64,
}

#[repr(C)]
struct Rusage {
    ru_utime: Timeval,
    ru_stime: Timeval,
    ru_maxrss: i64,
    rest: [i64; 13],
}

unsafe extern "C" {
    fn getrusage(who: i32, usage: *mut Rusage) -> i32;
}

fn real_arg(v: &Value) -> RResult<f64> {
    match v {
        Value::Real(r) => Ok(r.x.to_f64()),
        Value::Int(i) => Ok(i.to_f64()),
        Value::Rat(q) => Ok(q.to_f64()),
        _ => Err(RuntimeError::runtime("Argument must be a real number")),
    }
}

fn cputime(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let now = timing_seconds(cpu_time());
    let t = if a.args.is_empty() { now } else { now - real_arg(&a.args[0])? };
    one(timing_value(t))
}

fn realtime(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let _ = it;
    let now = timing_seconds(std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs_f64()).unwrap_or(0.0));
    let t = if a.args.is_empty() { now } else { now - real_arg(&a.args[0])? };
    one(timing_value(t))
}

fn clock_cycles(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::int(it.start.elapsed().as_nanos() as i64))
}

fn time_start(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::str(&format!("{}", cpu_time())))
}

fn time_since(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let t0: f64 = a.str(0)?.parse().map_err(|_| RuntimeError::runtime("Argument must be a string returned by Time()"))?;
    one(Value::str(&format!("{:.3}", cpu_time() - t0)))
}

fn set_show_real_time(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    it.show_real_time = a.bool(0)?;
    none()
}

fn get_show_real_time(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    boolv(it.show_real_time)
}

fn set_verbose(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let flag: Rc<str> = Rc::from(a.str(0)?);
    let level = match &a.args[1] {
        Value::Int(i) => i.to_i64().unwrap_or(0),
        Value::Bool(b) => *b as i64,
        _ => return Err(RuntimeError::runtime("Level must be an integer or boolean")),
    };
    let max = it.verbose.get(&flag).map(|v| v.1).unwrap_or(i64::MAX);
    if level < 0 || level > max {
        return Err(RuntimeError::runtime(format!("Level for verbose flag {flag} must be in the range [0..{max}]")));
    }
    it.verbose.insert(flag, (level, max));
    none()
}

fn get_verbose(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::int(it.verbose_level(a.str(0)?)))
}

fn is_verbose(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let need = if a.args.len() > 1 { a.i64(1)? } else { 1 };
    boolv(it.verbose_level(a.str(0)?) >= need)
}

fn list_verbose(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    let mut flags: Vec<(Rc<str>, (i64, i64))> = it.verbose.iter().map(|(k, v)| (k.clone(), *v)).collect();
    flags.sort();
    for (k, (lvl, max)) in flags {
        let max = if max == i64::MAX { "?".to_string() } else { max.to_string() };
        it.out.write(&format!("{k:30} {lvl} (maximum {max})\n"));
    }
    none()
}

fn clear_verbose(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    for v in it.verbose.values_mut() {
        v.0 = 0;
    }
    none()
}

fn set_assertions(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    it.assertions = match &a.args[0] {
        Value::Int(i) => i.to_i64().unwrap_or(1),
        Value::Bool(b) => *b as i64,
        _ => return Err(RuntimeError::runtime("Argument must be an integer or boolean")),
    };
    none()
}

fn get_assertions(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::int(it.assertions))
}

fn set_columns(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.usize(0)?;
    it.out.columns = if n == 0 { usize::MAX / 4 } else { n.max(20) };
    none()
}

fn get_columns(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    let c = if it.out.unlimited() { 0 } else { it.out.columns };
    one(Value::int(c as i64))
}

fn set_auto_columns(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    it.out.auto_columns = a.bool(0)?;
    none()
}

fn get_auto_columns(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    boolv(it.out.auto_columns)
}

fn set_quit_on_error(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    it.quit_on_error = a.bool(0)?;
    none()
}

fn get_version(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    let v: Vec<i64> = env!("CARGO_PKG_VERSION").split('.').map(|p| p.parse().unwrap_or(0)).collect();
    Ok(v.into_iter().map(Value::int).collect())
}

fn get_script_filename(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    let name = it.file_stack.last().map(|p| p.display().to_string()).unwrap_or_else(|| it.script_name.clone());
    one(Value::str(&name))
}

fn get_script_arguments(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    let args: Vec<Value> = it.script_args.iter().skip(1).map(|s| Value::str(s)).collect();
    one(Value::seq(Some(Value::strings()), args))
}

fn set_indent(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    it.indent_width = a.usize(0)?;
    none()
}

fn get_indent(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::int(it.indent_width as i64))
}

fn set_prompt(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    it.prompt = a.str(0)?.to_string();
    none()
}

fn get_prompt(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::str(&it.prompt))
}

fn set_path(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    it.search_path = a.str(0)?.split(':').filter(|s| !s.is_empty()).map(std::path::PathBuf::from).collect();
    none()
}

fn get_path(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    let s: Vec<String> = it.search_path.iter().map(|p| p.display().to_string()).collect();
    one(Value::str(&s.join(":")))
}

fn set_library_root(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    it.library_root = std::path::PathBuf::from(a.str(0)?);
    none()
}

fn get_library_root(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::str(&it.library_root.display().to_string()))
}

fn set_libraries(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    it.libraries = a.str(0)?.split(':').filter(|s| !s.is_empty()).map(std::path::PathBuf::from).collect();
    none()
}

fn get_libraries(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    let s: Vec<String> = it.libraries.iter().map(|p| p.display().to_string()).collect();
    one(Value::str(&s.join(":")))
}

fn get_temp_dir(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::str(&it.temp_dir.display().to_string()))
}

fn set_history_size(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    it.history_size = a.usize(0)?;
    none()
}

fn get_history_size(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::int(it.history_size as i64))
}

fn set_vi_mode(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    it.vi_mode = a.bool(0)?;
    none()
}

fn get_vi_mode(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    boolv(it.vi_mode)
}

fn show_identifiers(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    let mut names: Vec<String> = it.globals.keys().map(|k| k.to_string()).collect();
    names.sort();
    for n in names {
        it.out.write(&format!("{n}\n"));
    }
    none()
}

fn show_values(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    let mut entries: Vec<(String, Value)> = it.globals.iter().map(|(k, v)| (k.to_string(), v.clone())).collect();
    entries.sort_by(|a, b| a.0.cmp(&b.0));
    for (n, v) in entries {
        let text = it.format_flat(&v, Level::Minimal)?;
        it.out.write(&format!("{n}: {text}\n"));
    }
    none()
}

fn show_memory_usage(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    let mb = max_rss() as f64 / (1024.0 * 1024.0);
    it.out.write(&format!("Memory usage: {mb:.2}MB\n"));
    none()
}

fn get_memory_usage(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::int(max_rss()))
}

fn traceback(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    let frames: Vec<String> = it.trace.iter().rev().map(|f| f.name.to_string()).collect();
    for f in frames {
        it.out.write(&format!("  {f}\n"));
    }
    none()
}

fn list_signatures(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let (only, cat) = match (&a.args[0], a.args.get(1)) {
        (Value::Intr(name), Some(Value::Cat(c))) => (Some(*name), *c),
        (Value::Cat(c), None) => (None, *c),
        _ => return Err(RuntimeError::runtime("Bad arguments")),
    };
    let mut lines = Vec::new();
    let mut names: Vec<Sym> = it.intrinsics.names().collect();
    names.sort_by_key(|n| n.as_str());
    for name in names {
        if only.is_some_and(|o| o != name) {
            continue;
        }
        for sig in it.intrinsics.get(name).cloned().unwrap_or_default() {
            if sig.generic {
                continue;
            }
            let mentions = sig.args.iter().any(|arg| match &arg.pat {
                crate::types::TypePat::Is(t) | crate::types::TypePat::Ext(t, _) => it.types.isa(cat, *t) && *t != crate::types::t::ANY,
                _ => false,
            });
            if mentions {
                lines.push(format!("{name}{}", it.signature_line(&sig)));
            }
        }
    }
    for l in lines {
        it.out.write(&format!("{l}\n"));
    }
    none()
}

fn list_categories(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    let mut names: Vec<String> = it.types.all().map(|(_, info)| info.name.to_string()).collect();
    names.sort();
    let mut line = String::new();
    let mut text = String::new();
    for n in names {
        if line.len() + n.len() + 1 > 78 {
            text.push_str(line.trim_end());
            text.push('\n');
            line.clear();
        }
        line.push_str(&n);
        line.push(' ');
    }
    text.push_str(line.trim_end());
    text.push('\n');
    it.out.write(&text);
    none()
}

fn no_op(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    none()
}

fn get_nthreads(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::int(1))
}

fn set_profile(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    it.profile = a.bool(0)?;
    none()
}

fn get_profile(it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    boolv(it.profile)
}

fn set_warn_override(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    it.warn_override = a.bool(0)?;
    none()
}

fn set_print_level(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let l = a.str(0)?;
    Level::parse(l).ok_or_else(|| RuntimeError::runtime(format!("Unknown print level '{l}'")))?;
    none()
}

pub fn register(it: &mut Interp) {
    it.def("Cputime", "-> FldReElt", "The CPU time used so far, in seconds.", cputime);
    it.def("Cputime", "t::FldReElt -> FldReElt", "The CPU time used since t.", cputime);
    it.def("Realtime", "-> FldReElt", "The number of seconds since 00:00:00 GMT, January 1, 1970.", realtime);
    it.def("Realtime", "t::FldReElt -> FldReElt", "The real time elapsed since t.", realtime);
    it.def("ClockCycles", "-> RngIntElt", "A count of clock ticks since startup.", clock_cycles);
    it.def("Time", "-> MonStgElt", "A marker to pass to Time(T) later.", time_start);
    it.def("Time", "T::MonStgElt -> MonStgElt", "The CPU time elapsed since the marker T was taken.", time_since);
    it.def("SetShowRealTime", "b::BoolElt", "Whether time statements also show real time.", set_show_real_time);
    it.def("GetShowRealTime", "-> BoolElt", "Whether time statements also show real time.", get_show_real_time);
    it.def("SetVerbose", "s::MonStgElt, i::RngIntElt", "Set the level of the verbose flag s.", set_verbose);
    it.def("SetVerbose", "s::MonStgElt, b::BoolElt", "Turn the verbose flag s on or off.", set_verbose);
    it.def("GetVerbose", "s::MonStgElt -> RngIntElt", "The level of the verbose flag s.", get_verbose);
    it.def("IsVerbose", "s::MonStgElt -> BoolElt", "Whether the verbose flag s is on.", is_verbose);
    it.def("IsVerbose", "s::MonStgElt, l::RngIntElt -> BoolElt", "Whether the verbose flag s is at level l or above.", is_verbose);
    it.def("ListVerbose", "", "List the verbose flags and their levels.", list_verbose);
    it.def("ClearVerbose", "", "Turn all verbose flags off.", clear_verbose);
    it.def("SetAssertions", "b::RngIntElt", "Set the assertion level (0 to 3).", set_assertions);
    it.def("SetAssertions", "b::BoolElt", "Turn assertions on or off.", set_assertions);
    it.def("GetAssertions", "-> RngIntElt", "The assertion level.", get_assertions);
    it.def("SetColumns", "n::RngIntElt", "Set the line width used for printing (0 for no limit).", set_columns);
    it.def("GetColumns", "-> RngIntElt", "The line width used for printing.", get_columns);
    it.def("SetAutoColumns", "b::BoolElt", "Whether to follow the terminal width.", set_auto_columns);
    it.def("GetAutoColumns", "-> BoolElt", "Whether the terminal width is followed.", get_auto_columns);
    it.def("SetQuitOnError", "b::BoolElt", "Whether to quit when an error occurs.", set_quit_on_error);
    it.def("GetVersion", "-> RngIntElt, RngIntElt, RngIntElt", "The version numbers of calyx.", get_version);
    it.def("GetScriptFilename", "-> MonStgElt", "The name of the file being run.", get_script_filename);
    it.def("GetScriptArguments", "-> [MonStgElt]", "The extra command-line arguments.", get_script_arguments);
    it.def("SetIndent", "n::RngIntElt", "Set the number of spaces per indentation level.", set_indent);
    it.def("GetIndent", "-> RngIntElt", "The number of spaces per indentation level.", get_indent);
    it.def("SetPrompt", "s::MonStgElt", "Set the interactive prompt.", set_prompt);
    it.def("GetPrompt", "-> MonStgElt", "The interactive prompt.", get_prompt);
    it.def("SetPath", "s::MonStgElt", "Set the directories searched by load and Attach.", set_path);
    it.def("GetPath", "-> MonStgElt", "The directories searched by load and Attach.", get_path);
    it.def("SetLibraryRoot", "s::MonStgElt", "Set the root directory containing libraries.", set_library_root);
    it.def("GetLibraryRoot", "-> MonStgElt", "The root directory containing libraries.", get_library_root);
    it.def("SetLibraries", "s::MonStgElt", "Set the library directories below the library root.", set_libraries);
    it.def("GetLibraries", "-> MonStgElt", "The library directories below the library root.", get_libraries);
    it.def("GetTempDir", "-> MonStgElt", "The directory used for temporary files.", get_temp_dir);
    it.def("SetHistorySize", "n::RngIntElt", "Set the number of interactive history entries kept.", set_history_size);
    it.def("GetHistorySize", "-> RngIntElt", "The number of interactive history entries kept.", get_history_size);
    it.def("SetViMode", "b::BoolElt", "Use vi rather than Emacs line editing.", set_vi_mode);
    it.def("GetViMode", "-> BoolElt", "Whether vi line editing is in use.", get_vi_mode);
    it.def("ShowIdentifiers", "", "List the assigned identifiers.", show_identifiers);
    it.def("ShowValues", "", "List the assigned identifiers with their values.", show_values);
    it.def("ShowMemoryUsage", "", "Show the memory used.", show_memory_usage);
    it.def("GetMemoryUsage", "-> RngIntElt", "The memory used, in bytes.", get_memory_usage);
    it.def("GetMaximumMemoryUsage", "-> RngIntElt", "The peak memory used, in bytes.", get_memory_usage);
    it.def("ResetMaximumMemoryUsage", "", "Reset the peak memory statistic.", no_op);
    it.def("Traceback", "", "Show the active function calls.", traceback);
    it.def("ListSignatures", "C::Cat", "List the intrinsic signatures involving the category C.", list_signatures);
    it.def("ListSignatures", "F::Intrinsic, C::Cat", "List the signatures of F involving the category C.", list_signatures);
    it.def("ListCategories", "", "List all categories.", list_categories);
    it.def("GetNthreads", "-> RngIntElt", "The number of threads used by algorithms.", get_nthreads);
    it.def("SetProfile", "b::BoolElt", "Turn profiling on or off.", set_profile);
    it.def("GetProfile", "-> BoolElt", "Whether profiling is on.", get_profile);
    it.def("ProfileReset", "", "Clear the profile data.", no_op);
    it.def("SetWarnIntrinsicOverride", "b::BoolElt", "Warn when user intrinsics override built-in ones.", set_warn_override);
    it.def("SetPrintLevel", "l::MonStgElt", "Set the default print level.", set_print_level);
    let bool_noops = [
        "SetAutoCompact",
        "SetBeep",
        "SetEchoInputFile",
        "SetExitSummary",
        "SetGPU",
        "SetIgnorePrompt",
        "SetIgnoreSpaces",
        "SetLineEditor",
        "SetTraceback",
        "SetDebugOnError",
        "SetHelpUseExternalBrowser",
        "SetHelpUseExternalSystem",
    ];
    for n in bool_noops {
        it.def(n, "b::BoolElt", "Accepted for compatibility; has no effect.", no_op);
    }
    for n in ["SetMemoryLimit", "SetNthreads", "SetRows", "Alarm"] {
        it.def(n, "n::RngIntElt", "Accepted for compatibility; has no effect.", no_op);
    }
    for n in ["SetHelpExternalSystem"] {
        it.def(n, "s::MonStgElt", "Accepted for compatibility; has no effect.", no_op);
    }
}
