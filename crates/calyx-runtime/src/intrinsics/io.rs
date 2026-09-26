//! Input and output intrinsics: files, pipes, redirection, loading.

use std::io::{Read as _, Write};
use std::rc::Rc;

use calyx_flint::{Integer, Real, Rational};
use calyx_syntax::ast::AggKind;

use super::{boolv, none, one};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::print::Level;
use crate::value::*;

/// The string returned by `Gets` and friends at end of file.
pub const EOF_MARKER: &str = "\u{0}EOF";

const OBJECT_MAGIC: &[u8; 8] = b"CALYXOBJ";
const OBJECT_VERSION: u16 = 1;
const OBJECT_HEADER: usize = 18;
const MAX_OBJECT_SIZE: usize = 256 * 1024 * 1024;
const MAX_OBJECT_DEPTH: usize = 128;
const WORKSPACE_MAGIC: &[u8; 8] = b"CALYXWS\0";

impl Interp {
    /// Append text to a file named by a string, or write to an open file.
    pub fn write_to_file_value(&mut self, target: &Value, text: &str) -> RResult<()> {
        match target {
            Value::Str(name) => {
                let mut f = std::fs::OpenOptions::new().create(true).append(true).open(name.as_str()).map_err(|e| RuntimeError::runtime(format!("Could not open file \"{name}\": {e}")))?;
                f.write_all(text.as_bytes()).map_err(|e| RuntimeError::runtime(e.to_string()))
            }
            Value::Io(io) => write_raw(io, text.as_bytes()),
            _ => Err(RuntimeError::runtime("Bad file argument")),
        }
    }
}

fn write_raw(io: &IoObj, data: &[u8]) -> RResult<()> {
    match &mut *io.state.borrow_mut() {
        IoState::Writer(f) => f.write_all(data).map_err(|e| RuntimeError::runtime(e.to_string())),
        IoState::PipeWriter { stdin: Some(f), .. } => f.write_all(data).map_err(|e| RuntimeError::runtime(e.to_string())),
        IoState::Socket { stream, .. } => stream.write_all(data).map_err(|e| RuntimeError::runtime(e.to_string())),
        _ => Err(RuntimeError::runtime("Channel is not open for writing")),
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
    one(Value::Io(IoObj::new(name, mode, IoKind::File, state)))
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
        Ok(state) => Ok(vals![Value::Bool(true), Value::Io(IoObj::new(name, mode, IoKind::File, state))]),
        Err(_) => Ok(vals![Value::Bool(false), Value::Undef]),
    }
}

fn io_arg(a: &CallArgs, i: usize) -> Rc<IoObj> {
    match &a.args[i] {
        Value::Io(io) => io.clone(),
        _ => unreachable!(),
    }
}

fn read_raw(io: &Rc<IoObj>, count: Option<usize>, exact: bool) -> RResult<Vec<u8>> {
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
            let stdout = stdout.as_mut().ok_or_else(|| RuntimeError::runtime("Process output is closed"))?;
            let mut out = Vec::new();
            match count {
                Some(n) => {
                    let mut got = 0;
                    let mut buf = [0u8; 8192];
                    while got < n {
                        let want = (n - got).min(buf.len());
                        match stdout.read(&mut buf[..want]) {
                            Ok(0) => {
                                *eof = true;
                                break;
                            }
                            Ok(k) => {
                                out.extend_from_slice(&buf[..k]);
                                got += k;
                                if !exact {
                                    break;
                                }
                            }
                            Err(e) => return Err(RuntimeError::runtime(e.to_string())),
                        }
                    }
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
        IoState::Socket { stream, eof } => {
            if *eof {
                return Ok(Vec::new());
            }
            let mut out = Vec::new();
            match count {
                Some(n) => {
                    let mut got = 0;
                    let mut buf = [0u8; 64 * 1024];
                    while got < n {
                        let want = (n - got).min(buf.len());
                        match stream.read(&mut buf[..want]) {
                            Ok(0) => {
                                *eof = true;
                                break;
                            }
                            Ok(k) => {
                                out.extend_from_slice(&buf[..k]);
                                got += k;
                                if !exact {
                                    break;
                                }
                            }
                            Err(e) => return Err(RuntimeError::runtime(e.to_string())),
                        }
                    }
                }
                None => {
                    let mut buf = [0u8; 8192];
                    let n = stream.read(&mut buf).map_err(|e| RuntimeError::runtime(e.to_string()))?;
                    if n == 0 {
                        *eof = true;
                    } else {
                        out.extend_from_slice(&buf[..n]);
                    }
                }
            }
            Ok(out)
        }
        _ => Err(RuntimeError::runtime("File is not open for reading")),
    }
}

fn take_async_result(io: &IoObj, kind: AsyncReadKind) -> RResult<Option<Vec<u8>>> {
    let mut state = io.async_io.borrow_mut();
    if let Some(result) = state.ready.take() {
        if result.kind != kind {
            state.ready = Some(result);
            return Err(RuntimeError::runtime("Queued asynchronous read has a different result type"));
        }
        return Ok(Some(result.data));
    }
    if state.read.is_some() {
        return Err(RuntimeError::runtime("Asynchronous read has not completed"));
    }
    Ok(None)
}

fn read_data(io: &Rc<IoObj>, kind: AsyncReadKind, count: Option<usize>, exact: bool) -> RResult<Vec<u8>> {
    if let Some(data) = take_async_result(io, kind)? {
        return Ok(data);
    }
    read_raw(io, count, exact)
}

fn read_count(a: &CallArgs) -> RResult<Option<usize>> {
    if a.args.len() > 1 {
        return Ok(Some(a.usize(1)?));
    }
    match a.param("Max") {
        Some(Value::Int(n)) if n.sign() > 0 => Ok(Some(n.to_u64().ok_or_else(|| RuntimeError::runtime("Max is too large"))? as usize)),
        Some(Value::Int(_)) | None => Ok(None),
        Some(_) => Err(RuntimeError::runtime("Parameter 'Max' must be an integer")),
    }
}

fn read_io(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let io = io_arg(a, 0);
    let count = read_count(a)?;
    let data = read_data(&io, AsyncReadKind::Text, count, a.args.len() > 1)?;
    if data.is_empty() && count != Some(0) {
        return one(Value::str(EOF_MARKER));
    }
    one(Value::str(&String::from_utf8_lossy(&data)))
}

fn read_check(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    match read_io(it, a) {
        Ok(mut v) => {
            let value = v.pop().unwrap_or(Value::Undef);
            Ok(vals![Value::Bool(true), value])
        }
        Err(_) => Ok(vals![Value::Bool(false), Value::Undef]),
    }
}

fn bytes_from_seq(a: &CallArgs, i: usize) -> RResult<Vec<u8>> {
    let s = a.seq(i)?;
    let mut out = Vec::with_capacity(s.elems.len());
    for v in &s.elems {
        let Value::Int(n) = v else { return Err(RuntimeError::runtime("Byte sequence entries must be integers")) };
        out.push(n.to_u64().filter(|n| *n <= 255).ok_or_else(|| RuntimeError::runtime("Byte sequence entries must be between 0 and 255"))? as u8);
    }
    Ok(out)
}

fn read_bytes(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let io = io_arg(a, 0);
    let data = read_data(&io, AsyncReadKind::Bytes, read_count(a)?, a.args.len() > 1)?;
    one(Value::int_seq(data.into_iter().map(|b| calyx_flint::Integer::from_u64(b as u64))))
}

fn read_bytes_check(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    match read_bytes(it, a) {
        Ok(mut v) => Ok(vals![Value::Bool(true), v.pop().unwrap_or(Value::Undef)]),
        Err(_) => Ok(vals![Value::Bool(false), Value::Undef]),
    }
}

fn write_bytes(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let io = io_arg(a, 0);
    write_raw(&io, &bytes_from_seq(a, 1)?)?;
    none()
}

fn write_check(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(put(it, a).is_ok())
}

fn write_bytes_check(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(write_bytes(it, a).is_ok())
}

fn object_error(s: impl Into<String>) -> RuntimeError {
    RuntimeError::runtime(format!("Invalid calyx object: {}", s.into()))
}

fn object_precision(bits: u64) -> RResult<u64> {
    if bits >= 2 && bits < 1 << 40 && calyx_flint::digits_for_bits(bits) < 1 << 38 {
        Ok(bits)
    } else {
        Err(object_error("precision is out of range"))
    }
}

fn put_u64(out: &mut Vec<u8>, n: u64) {
    out.extend_from_slice(&n.to_le_bytes());
}

fn put_blob(out: &mut Vec<u8>, data: &[u8]) {
    put_u64(out, data.len() as u64);
    out.extend_from_slice(data);
}

fn put_integer(out: &mut Vec<u8>, n: &Integer) {
    put_blob(out, n.to_string().as_bytes());
}

fn encode_real(out: &mut Vec<u8>, x: &Real) -> RResult<()> {
    if !x.is_finite() {
        return Err(RuntimeError::runtime("Non-finite real numbers cannot be written as calyx objects"));
    }
    put_u64(out, x.prec());
    let (m, e) = x.mantissa_exponent();
    put_integer(out, &m);
    out.extend_from_slice(&e.to_le_bytes());
    out.push((x.is_zero() && x.is_sign_negative()) as u8);
    Ok(())
}

fn encode_universe(it: &Interp, out: &mut Vec<u8>, universe: &Option<Value>) -> RResult<()> {
    match universe {
        Some(v) => {
            out.push(1);
            encode_value(it, out, v)
        }
        None => {
            out.push(0);
            Ok(())
        }
    }
}

fn encode_values<'a>(it: &Interp, out: &mut Vec<u8>, values: impl ExactSizeIterator<Item = &'a Value>) -> RResult<()> {
    put_u64(out, values.len() as u64);
    for v in values {
        encode_value(it, out, v)?;
    }
    Ok(())
}

fn encode_value(it: &Interp, out: &mut Vec<u8>, v: &Value) -> RResult<()> {
    match v {
        Value::Undef => out.push(0),
        Value::Bool(false) => out.push(1),
        Value::Bool(true) => out.push(2),
        Value::Int(n) => {
            out.push(3);
            put_integer(out, n);
        }
        Value::Rat(q) => {
            out.push(4);
            put_integer(out, &q.numerator());
            put_integer(out, &q.denominator());
        }
        Value::Real(x) => {
            out.push(5);
            encode_real(out, &x.x)?;
        }
        Value::Complex(x) => {
            out.push(6);
            encode_real(out, &x.re)?;
            encode_real(out, &x.im)?;
        }
        Value::Str(s) => {
            out.push(7);
            put_blob(out, s.as_bytes());
        }
        Value::BStr(s) => {
            out.push(8);
            put_blob(out, s);
        }
        Value::Seq(s) => {
            out.push(9);
            encode_universe(it, out, &s.universe)?;
            encode_values(it, out, s.elems.iter())?;
        }
        Value::Tuple(s) => {
            out.push(10);
            encode_values(it, out, s.elems.iter())?;
        }
        Value::List(s) => {
            out.push(11);
            encode_values(it, out, s.iter())?;
        }
        Value::Set(s) => {
            out.push(12);
            encode_universe(it, out, &s.universe)?;
            let values: Vec<Value> = s.iter().collect();
            encode_values(it, out, values.iter())?;
        }
        Value::ISet(s) => {
            out.push(13);
            encode_universe(it, out, &s.universe)?;
            encode_values(it, out, s.elems.iter())?;
        }
        Value::MSet(s) => {
            out.push(14);
            encode_universe(it, out, &s.universe)?;
            put_u64(out, s.elems.len() as u64);
            for (v, n) in &s.elems {
                encode_value(it, out, v)?;
                put_u64(out, *n);
            }
        }
        Value::Infinity(sign) => {
            out.push(15);
            out.push(*sign as u8);
        }
        Value::Struct(s) => match &s.kind {
            StructKind::Integers => out.push(16),
            StructKind::Rationals => out.push(17),
            StructKind::Reals(bits) => {
                out.push(18);
                put_u64(out, *bits);
            }
            StructKind::Booleans => out.push(19),
            StructKind::Strings => out.push(20),
            StructKind::Ring(r) => match &r.kind {
                crate::rings::RingKind::Complex(bits) => {
                    out.push(21);
                    put_u64(out, *bits);
                }
                _ => return Err(RuntimeError::runtime("This parent cannot be written as a calyx object")),
            },
            _ => return Err(RuntimeError::runtime("This parent cannot be written as a calyx object")),
        },
        Value::Mat(m) => {
            out.push(22);
            encode_value(it, out, m.ring())?;
            out.push(match m.info().shape {
                crate::intrinsics::matrices::Shape::Algebra => 0,
                crate::intrinsics::matrices::Shape::Space => 1,
                crate::intrinsics::matrices::Shape::Tuples => 2,
            });
            put_u64(out, m.m.nrows() as u64);
            put_u64(out, m.m.ncols() as u64);
            for i in 0..m.m.nrows() {
                for j in 0..m.m.ncols() {
                    encode_value(it, out, &crate::intrinsics::matrices::entry_value(it, m, i, j))?;
                }
            }
        }
        _ => return Err(RuntimeError::runtime("This value cannot be written as a calyx object")),
    }
    Ok(())
}

struct ObjectReader<'a> {
    data: &'a [u8],
    pos: usize,
}

impl<'a> ObjectReader<'a> {
    fn take(&mut self, n: usize) -> RResult<&'a [u8]> {
        let end = self.pos.checked_add(n).filter(|end| *end <= self.data.len()).ok_or_else(|| object_error("truncated data"))?;
        let result = &self.data[self.pos..end];
        self.pos = end;
        Ok(result)
    }

    fn byte(&mut self) -> RResult<u8> {
        Ok(self.take(1)?[0])
    }

    fn u64(&mut self) -> RResult<u64> {
        Ok(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
    }

    fn usize(&mut self) -> RResult<usize> {
        usize::try_from(self.u64()?).map_err(|_| object_error("length is too large"))
    }

    fn blob(&mut self) -> RResult<&'a [u8]> {
        let n = self.usize()?;
        self.take(n)
    }

    fn integer(&mut self) -> RResult<Integer> {
        let text = std::str::from_utf8(self.blob()?).map_err(|_| object_error("integer is not UTF-8"))?;
        Integer::parse(text).ok_or_else(|| object_error("bad integer"))
    }

    fn real(&mut self) -> RResult<Real> {
        let bits = object_precision(self.u64()?)?;
        let m = self.integer()?;
        let e = i64::from_le_bytes(self.take(8)?.try_into().unwrap());
        let negative_zero = self.byte()? != 0;
        if bits < 2 {
            return Err(object_error("bad real precision"));
        }
        Ok(if m.is_zero() && negative_zero { Real::signed_zero(bits, true) } else { Real::from_integer_2exp(&m, e, bits) })
    }

    fn universe(&mut self, it: &mut Interp, depth: usize) -> RResult<Option<Value>> {
        match self.byte()? {
            0 => Ok(None),
            1 => Ok(Some(self.value_at(it, depth + 1)?)),
            _ => Err(object_error("bad optional universe")),
        }
    }

    fn values(&mut self, it: &mut Interp, depth: usize) -> RResult<Vec<Value>> {
        let n = self.usize()?;
        if n > self.data.len() - self.pos {
            return Err(object_error("aggregate length exceeds the remaining payload"));
        }
        let mut values = Vec::with_capacity(n.min(1024));
        for _ in 0..n {
            values.push(self.value_at(it, depth + 1)?);
        }
        Ok(values)
    }

    fn value(&mut self, it: &mut Interp) -> RResult<Value> {
        self.value_at(it, 0)
    }

    fn value_at(&mut self, it: &mut Interp, depth: usize) -> RResult<Value> {
        if depth > MAX_OBJECT_DEPTH {
            return Err(object_error("nesting is too deep"));
        }
        Ok(match self.byte()? {
            0 => Value::Undef,
            1 => Value::Bool(false),
            2 => Value::Bool(true),
            3 => Value::Int(self.integer()?),
            4 => {
                let n = self.integer()?;
                let d = self.integer()?;
                Value::rat(Rational::new(&n, &d).ok_or_else(|| object_error("zero rational denominator"))?)
            }
            5 => Value::real(self.real()?),
            6 => Value::complex(self.real()?, self.real()?),
            7 => Value::string(String::from_utf8(self.blob()?.to_vec()).map_err(|_| object_error("string is not UTF-8"))?),
            8 => Value::bytes(self.blob()?.to_vec()),
            9 => {
                let universe = self.universe(it, depth)?;
                let values = self.values(it, depth)?;
                it.build_aggregate(AggKind::Seq, universe, values, false)?
            }
            10 => Value::tuple(self.values(it, depth)?),
            11 => Value::list(self.values(it, depth)?),
            12 => {
                let universe = self.universe(it, depth)?;
                let values = self.values(it, depth)?;
                it.build_aggregate(AggKind::Set, universe, values, false)?
            }
            13 => {
                let universe = self.universe(it, depth)?;
                let values = self.values(it, depth)?;
                it.build_aggregate(AggKind::ISet, universe, values, false)?
            }
            14 => {
                let universe = self.universe(it, depth)?;
                let n = self.usize()?;
                if n > (self.data.len() - self.pos) / 9 {
                    return Err(object_error("multiset length exceeds the remaining payload"));
                }
                let mut values = Vec::with_capacity(n.min(1024));
                let mut mults = Vec::with_capacity(n.min(1024));
                for _ in 0..n {
                    values.push(self.value_at(it, depth + 1)?);
                    mults.push(self.u64()?);
                }
                it.build_multiset(universe, values, mults)?
            }
            15 => match self.byte()? {
                0 => Value::Infinity(false),
                1 => Value::Infinity(true),
                _ => return Err(object_error("bad infinity sign")),
            },
            16 => Value::integers(),
            17 => Value::rationals(),
            18 => Value::reals(object_precision(self.u64()?)?),
            19 => Value::booleans(),
            20 => Value::strings(),
            21 => it.complex_field(object_precision(self.u64()?)?),
            22 => {
                let ring = self.value_at(it, depth + 1)?;
                let shape = match self.byte()? {
                    0 => crate::intrinsics::matrices::Shape::Algebra,
                    1 => crate::intrinsics::matrices::Shape::Space,
                    2 => crate::intrinsics::matrices::Shape::Tuples,
                    _ => return Err(object_error("bad matrix shape")),
                };
                let nrows = self.usize()?;
                let ncols = self.usize()?;
                if shape == crate::intrinsics::matrices::Shape::Tuples && nrows != 1 {
                    return Err(object_error("bad vector dimensions"));
                }
                if shape == crate::intrinsics::matrices::Shape::Algebra && nrows != ncols {
                    return Err(object_error("matrix algebra element is not square"));
                }
                let entries = nrows.checked_mul(ncols).ok_or_else(|| object_error("matrix dimensions are too large"))?;
                if entries > self.data.len() - self.pos {
                    return Err(object_error("matrix dimensions exceed the remaining payload"));
                }
                let ctx = crate::intrinsics::matrices::entry_ctx(it, &ring)?;
                let mut mat = calyx_flint::mat::Mat::zero(&ctx, nrows, ncols);
                for i in 0..nrows {
                    for j in 0..ncols {
                        let entry = self.value_at(it, depth + 1)?;
                        if !crate::intrinsics::matrices::set_entry(it, &ring, &mut mat, i, j, &entry)? {
                            return Err(object_error("matrix entry does not belong to its coefficient ring"));
                        }
                    }
                }
                let parent = crate::intrinsics::matrices::parent(it, &ring, nrows, ncols, shape)?;
                Value::Mat(Rc::new(crate::intrinsics::matrices::Mtrx { parent, m: mat }))
            }
            _ => return Err(object_error("unknown value tag")),
        })
    }
}

fn encode_object(it: &Interp, value: &Value) -> RResult<Vec<u8>> {
    let mut payload = Vec::new();
    encode_value(it, &mut payload, value)?;
    if payload.len() > MAX_OBJECT_SIZE {
        return Err(RuntimeError::runtime("Calyx object is too large"));
    }
    let mut data = Vec::with_capacity(OBJECT_HEADER + payload.len());
    data.extend_from_slice(OBJECT_MAGIC);
    data.extend_from_slice(&OBJECT_VERSION.to_le_bytes());
    put_u64(&mut data, payload.len() as u64);
    data.extend_from_slice(&payload);
    Ok(data)
}

fn object_frame_len(data: &[u8]) -> RResult<Option<usize>> {
    if data.len() < OBJECT_HEADER {
        return Ok(None);
    }
    if &data[..8] != OBJECT_MAGIC {
        return Err(object_error("bad format marker"));
    }
    let version = u16::from_le_bytes(data[8..10].try_into().unwrap());
    if version != OBJECT_VERSION {
        return Err(object_error(format!("unsupported version {version}")));
    }
    let payload = usize::try_from(u64::from_le_bytes(data[10..18].try_into().unwrap())).map_err(|_| object_error("length is too large"))?;
    if payload > MAX_OBJECT_SIZE {
        return Err(object_error("length is too large"));
    }
    Ok(Some(OBJECT_HEADER + payload))
}

fn decode_object(it: &mut Interp, data: &[u8]) -> RResult<Value> {
    let Some(n) = object_frame_len(data)? else { return Err(object_error("truncated header")) };
    if data.len() != n {
        return Err(object_error(if data.len() < n { "truncated payload" } else { "trailing data" }));
    }
    let mut reader = ObjectReader { data: &data[OBJECT_HEADER..], pos: 0 };
    let value = reader.value(it)?;
    if reader.pos != reader.data.len() {
        return Err(object_error("trailing payload data"));
    }
    Ok(value)
}

fn read_object_data(io: &Rc<IoObj>) -> RResult<Vec<u8>> {
    if let Some(data) = take_async_result(io, AsyncReadKind::Object)? {
        return Ok(data);
    }
    let header = read_raw(io, Some(OBJECT_HEADER), true)?;
    if header.len() != OBJECT_HEADER {
        return Err(object_error("input ended before the header was complete"));
    }
    let n = object_frame_len(&header)?.unwrap();
    let mut data = header;
    let payload = read_raw(io, Some(n - OBJECT_HEADER), true)?;
    if payload.len() != n - OBJECT_HEADER {
        return Err(object_error("input ended before the payload was complete"));
    }
    data.extend_from_slice(&payload);
    Ok(data)
}

fn read_object(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let io = io_arg(a, 0);
    one(decode_object(it, &read_object_data(&io)?)?)
}

fn read_object_check(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    match read_object(it, a) {
        Ok(mut values) => Ok(vals![Value::Bool(true), values.pop().unwrap_or(Value::Undef)]),
        Err(_) => Ok(vals![Value::Bool(false), Value::Undef]),
    }
}

fn write_object(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let io = io_arg(a, 0);
    write_raw(&io, &encode_object(it, &a.args[1])?)?;
    none()
}

fn write_object_check(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(write_object(it, a).is_ok())
}

/// Save user globals in calyx's own versioned workspace format.
pub fn save_workspace(it: &Interp, name: &str) -> RResult<()> {
    let mut globals: Vec<_> = it.globals.iter().collect();
    globals.sort_by_key(|(name, _)| name.as_str());
    let mut data = Vec::new();
    data.extend_from_slice(WORKSPACE_MAGIC);
    data.extend_from_slice(&OBJECT_VERSION.to_le_bytes());
    put_u64(&mut data, globals.len() as u64);
    for (name, value) in globals {
        put_blob(&mut data, name.as_str().as_bytes());
        data.extend_from_slice(&encode_object(it, value).map_err(|e| e.in_context(format!("saving global '{name}'")))?);
    }
    std::fs::write(name, data).map_err(|e| RuntimeError::runtime(format!("Could not save workspace to \"{name}\": {e}")))
}

/// Validate a complete calyx workspace before replacing the current globals.
pub fn restore_workspace(it: &mut Interp, name: &str) -> RResult<()> {
    let data = std::fs::read(name).map_err(|e| RuntimeError::runtime(format!("Could not restore workspace from \"{name}\": {e}")))?;
    if data.len() < OBJECT_HEADER || &data[..8] != WORKSPACE_MAGIC {
        return Err(RuntimeError::runtime("Invalid calyx workspace: bad or truncated format marker"));
    }
    let version = u16::from_le_bytes(data[8..10].try_into().unwrap());
    if version != OBJECT_VERSION {
        return Err(RuntimeError::runtime(format!("Invalid calyx workspace: unsupported version {version}")));
    }
    let count = usize::try_from(u64::from_le_bytes(data[10..18].try_into().unwrap())).map_err(|_| RuntimeError::runtime("Invalid calyx workspace: entry count is too large"))?;
    let mut pos = OBJECT_HEADER;
    let mut globals = Vec::with_capacity(count.min(1024));
    let mut names = std::collections::HashSet::new();
    for _ in 0..count {
        let mut reader = ObjectReader { data: &data[pos..], pos: 0 };
        let text = std::str::from_utf8(reader.blob()?).map_err(|_| RuntimeError::runtime("Invalid calyx workspace: global name is not UTF-8"))?;
        if !names.insert(text.to_string()) {
            return Err(RuntimeError::runtime(format!("Invalid calyx workspace: duplicate global '{text}'")));
        }
        pos += reader.pos;
        let n = object_frame_len(&data[pos..])?.ok_or_else(|| RuntimeError::runtime("Invalid calyx workspace: truncated object header"))?;
        if pos.checked_add(n).is_none_or(|end| end > data.len()) {
            return Err(RuntimeError::runtime("Invalid calyx workspace: truncated object"));
        }
        let value = decode_object(it, &data[pos..pos + n])?;
        globals.push((crate::sym::Sym::new(text), value));
        pos += n;
    }
    if pos != data.len() {
        return Err(RuntimeError::runtime("Invalid calyx workspace: trailing data"));
    }
    it.replace_globals(globals);
    Ok(())
}

fn gets(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let io = io_arg(a, 0);
    if let IoState::Reader { data, pos } = &mut *io.state.borrow_mut() {
        if *pos >= data.len() {
            return one(Value::str(EOF_MARKER));
        }
        let end = data[*pos..].iter().position(|b| *b == b'\n').map_or(data.len(), |n| *pos + n);
        let line = String::from_utf8_lossy(&data[*pos..end]).to_string();
        *pos = (end + 1).min(data.len());
        return one(Value::string(line));
    }
    let mut line = Vec::new();
    let mut hit_eof = false;
    loop {
        let b = read_raw(&io, Some(1), true)?;
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
    let data = read_raw(&io, Some(1), true)?;
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
            IoState::Socket { stream, .. } => stream.flush().map_err(|e| RuntimeError::runtime(e.to_string()))?,
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
        IoState::PipeReader { .. } | IoState::PipeWriter { .. } | IoState::ServerSocket { .. } | IoState::Socket { .. } | IoState::Closed => 0,
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
        IoState::Socket { eof, .. } => *eof,
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

fn socket_addr(v: &Value, name: &str) -> RResult<Option<String>> {
    match v {
        Value::Undef => Ok(None),
        Value::Str(s) => Ok(Some(s.to_string())),
        _ => Err(RuntimeError::runtime(format!("Parameter '{name}' must be a string"))),
    }
}

fn socket_port(v: &Value, name: &str) -> RResult<u16> {
    let Value::Int(n) = v else { return Err(RuntimeError::runtime(format!("{name} must be an integer"))) };
    n.to_u64().filter(|n| *n <= u16::MAX as u64).map(|n| n as u16).ok_or_else(|| RuntimeError::runtime(format!("{name} must be between 0 and 65535")))
}

fn socket(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    if a.args.is_empty() {
        let host = socket_addr(a.param("LocalHost").unwrap_or(&Value::Undef), "LocalHost")?.unwrap_or_else(|| "127.0.0.1".to_string());
        let port = socket_port(a.param("LocalPort").unwrap_or(&Value::int(0)), "LocalPort")?;
        let listener = std::net::TcpListener::bind((host.as_str(), port)).map_err(|e| RuntimeError::runtime(format!("Could not open server socket: {e}")))?;
        let name = listener.local_addr().map(|x| x.to_string()).unwrap_or_else(|_| format!("{host}:{port}"));
        return one(Value::Io(IoObj::new(name, "rw".to_string(), IoKind::Socket, IoState::ServerSocket { listener, pending: None })));
    }
    let host = a.str(0)?.to_string();
    let port = socket_port(&a.args[1], "Port")?;
    let local_host = socket_addr(a.param("LocalHost").unwrap_or(&Value::Undef), "LocalHost")?;
    let local_port = socket_port(a.param("LocalPort").unwrap_or(&Value::int(0)), "LocalPort")?;
    if local_host.is_some() || local_port != 0 {
        return Err(RuntimeError::runtime("Explicit local client socket addresses are not supported"));
    }
    let stream = std::net::TcpStream::connect((host.as_str(), port)).map_err(|e| RuntimeError::runtime(format!("Could not connect socket: {e}")))?;
    let _ = stream.set_nodelay(true);
    one(Value::Io(IoObj::new(format!("{host}:{port}"), "rw".to_string(), IoKind::Socket, IoState::Socket { stream, eof: false })))
}

fn wait_for_connection(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let server = io_arg(a, 0);
    let stream = match &mut *server.state.borrow_mut() {
        IoState::ServerSocket { listener, pending } => match pending.take() {
            Some(s) => s,
            None => {
                listener.set_nonblocking(true).map_err(|e| RuntimeError::runtime(e.to_string()))?;
                loop {
                    match listener.accept() {
                        Ok((stream, _)) => {
                            let _ = listener.set_nonblocking(false);
                            break stream;
                        }
                        Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                            if let Err(e) = it.check_interrupt() {
                                let _ = listener.set_nonblocking(false);
                                return Err(e);
                            }
                            std::thread::sleep(std::time::Duration::from_millis(1));
                        }
                        Err(e) => {
                            let _ = listener.set_nonblocking(false);
                            return Err(RuntimeError::runtime(format!("Could not accept socket connection: {e}")));
                        }
                    }
                }
            }
        },
        _ => return Err(RuntimeError::runtime("Argument is not a server socket")),
    };
    let _ = stream.set_nodelay(true);
    let name = stream.peer_addr().map(|x| x.to_string()).unwrap_or_else(|_| "socket".to_string());
    one(Value::Io(IoObj::new(name, "rw".to_string(), IoKind::Socket, IoState::Socket { stream, eof: false })))
}

fn addr_tuple(a: std::net::SocketAddr) -> Value {
    Value::tuple(vec![Value::str(&a.ip().to_string()), Value::int(a.port() as i64)])
}

fn socket_information(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let io = io_arg(a, 0);
    match &*io.state.borrow() {
        IoState::ServerSocket { listener, .. } => {
            let local = listener.local_addr().map_err(|e| RuntimeError::runtime(e.to_string()))?;
            Ok(vals![addr_tuple(local), Value::Undef])
        }
        IoState::Socket { stream, .. } => {
            let local = stream.local_addr().map_err(|e| RuntimeError::runtime(e.to_string()))?;
            let peer = stream.peer_addr().map_err(|e| RuntimeError::runtime(e.to_string()))?;
            Ok(vals![addr_tuple(local), addr_tuple(peer)])
        }
        _ => Err(RuntimeError::runtime("Argument is not a socket")),
    }
}

fn is_server_socket(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let io = io_arg(a, 0);
    boolv(matches!(&*io.state.borrow(), IoState::ServerSocket { .. }))
}

fn socket_readable(io: &IoObj) -> RResult<bool> {
    match &mut *io.state.borrow_mut() {
        IoState::ServerSocket { listener, pending } => {
            if pending.is_some() {
                return Ok(true);
            }
            listener.set_nonblocking(true).map_err(|e| RuntimeError::runtime(e.to_string()))?;
            let result = match listener.accept() {
                Ok((stream, _)) => {
                    *pending = Some(stream);
                    true
                }
                Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => false,
                Err(e) => {
                    let _ = listener.set_nonblocking(false);
                    return Err(RuntimeError::runtime(e.to_string()));
                }
            };
            listener.set_nonblocking(false).map_err(|e| RuntimeError::runtime(e.to_string()))?;
            Ok(result)
        }
        IoState::Socket { stream, .. } => {
            stream.set_nonblocking(true).map_err(|e| RuntimeError::runtime(e.to_string()))?;
            let mut byte = [0u8; 1];
            let result = match stream.peek(&mut byte) {
                Ok(_) => true,
                Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => false,
                Err(e) => {
                    let _ = stream.set_nonblocking(false);
                    return Err(RuntimeError::runtime(e.to_string()));
                }
            };
            stream.set_nonblocking(false).map_err(|e| RuntimeError::runtime(e.to_string()))?;
            Ok(result)
        }
        IoState::Reader { .. } | IoState::PipeReader { .. } => Ok(true),
        _ => Ok(false),
    }
}

fn queue_async_read(io: &Rc<IoObj>, kind: AsyncReadKind, count: Option<usize>, exact: bool) -> RResult<()> {
    if io.kind == IoKind::Pipe {
        return Err(RuntimeError::runtime("Asynchronous I/O on pipes is not supported"));
    }
    let mut state = io.async_io.borrow_mut();
    if state.read.is_some() || state.ready.is_some() {
        return Err(RuntimeError::runtime("An asynchronous read is already queued"));
    }
    state.read = Some(PendingRead { kind, count, exact, data: Vec::new() });
    drop(state);
    if io.kind == IoKind::File {
        advance_async(io)?;
    }
    Ok(())
}

fn queue_async_write(io: &Rc<IoObj>, data: Vec<u8>) -> RResult<()> {
    if io.kind == IoKind::Pipe {
        return Err(RuntimeError::runtime("Asynchronous I/O on pipes is not supported"));
    }
    if io.kind == IoKind::File {
        return write_raw(io, &data);
    }
    io.async_io.borrow_mut().writes.push_back(data);
    Ok(())
}

fn async_read_need(request: &PendingRead) -> RResult<Option<usize>> {
    if request.kind == AsyncReadKind::Object {
        return Ok(Some(match object_frame_len(&request.data)? {
            Some(n) => n.saturating_sub(request.data.len()),
            None => OBJECT_HEADER - request.data.len(),
        }));
    }
    Ok(request.count.map(|n| n.saturating_sub(request.data.len())))
}

fn advance_async(io: &Rc<IoObj>) -> RResult<()> {
    let writes: Vec<Vec<u8>> = io.async_io.borrow_mut().writes.drain(..).collect();
    for data in writes {
        write_raw(io, &data)?;
    }
    if io.async_io.borrow().read.is_none() || io.async_io.borrow().ready.is_some() {
        return Ok(());
    }
    if io.kind == IoKind::Socket && !socket_readable(io)? {
        return Ok(());
    }
    let mut async_io = io.async_io.borrow_mut();
    let request = async_io.read.as_mut().unwrap();
    let mut eof = false;
    match &mut *io.state.borrow_mut() {
        IoState::Socket { stream, eof: stream_eof } => {
            stream.set_nonblocking(true).map_err(|e| RuntimeError::runtime(e.to_string()))?;
            let need = async_read_need(request)?.unwrap_or(8192).max(1);
            let mut buf = vec![0u8; need.min(8192)];
            loop {
                match stream.read(&mut buf) {
                    Ok(0) => {
                        *stream_eof = true;
                        eof = true;
                        break;
                    }
                    Ok(n) => {
                        request.data.extend_from_slice(&buf[..n]);
                        let need = async_read_need(request)?;
                        if !request.exact || need == Some(0) {
                            break;
                        }
                        buf.resize(need.unwrap_or(8192).max(1).min(8192), 0);
                    }
                    Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => break,
                    Err(e) => {
                        let _ = stream.set_nonblocking(false);
                        return Err(RuntimeError::runtime(e.to_string()));
                    }
                }
            }
            stream.set_nonblocking(false).map_err(|e| RuntimeError::runtime(e.to_string()))?;
        }
        IoState::Reader { data, pos } => {
            loop {
                let need = async_read_need(request)?;
                let end = need.map_or(data.len(), |n| pos.saturating_add(n).min(data.len()));
                request.data.extend_from_slice(&data[*pos..end]);
                *pos = end;
                if request.kind != AsyncReadKind::Object || need == Some(0) || *pos >= data.len() {
                    break;
                }
            }
            eof = *pos >= data.len();
        }
        IoState::ServerSocket { .. } => return Err(RuntimeError::runtime("Cannot queue a data read on a server socket")),
        _ => return Err(RuntimeError::runtime("Channel is not open for asynchronous reading")),
    }
    let complete = eof || (!request.exact && !request.data.is_empty()) || async_read_need(request)? == Some(0);
    if complete {
        let request = async_io.read.take().unwrap();
        async_io.ready = Some(AsyncResult { kind: request.kind, data: request.data });
    }
    Ok(())
}

fn async_read(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let io = io_arg(a, 0);
    let count = read_count(a)?;
    queue_async_read(&io, AsyncReadKind::Text, count, a.args.len() > 1)?;
    none()
}

fn async_read_bytes(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let io = io_arg(a, 0);
    let count = read_count(a)?;
    queue_async_read(&io, AsyncReadKind::Bytes, count, a.args.len() > 1)?;
    none()
}

fn async_write(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let io = io_arg(a, 0);
    queue_async_write(&io, a.str(1)?.as_bytes().to_vec())?;
    none()
}

fn async_write_bytes(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let io = io_arg(a, 0);
    queue_async_write(&io, bytes_from_seq(a, 1)?)?;
    none()
}

fn async_read_object(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let io = io_arg(a, 0);
    queue_async_read(&io, AsyncReadKind::Object, None, true)?;
    none()
}

fn async_write_object(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let io = io_arg(a, 0);
    queue_async_write(&io, encode_object(it, &a.args[1])?)?;
    none()
}

fn time_limit(a: &CallArgs) -> RResult<Option<std::time::Duration>> {
    match a.param("TimeLimit") {
        Some(Value::Infinity(true)) | None => Ok(None),
        Some(Value::Int(n)) => Ok(Some(std::time::Duration::from_millis(n.to_u64().ok_or_else(|| RuntimeError::runtime("TimeLimit must be non-negative"))?))),
        _ => Err(RuntimeError::runtime("TimeLimit must be a non-negative integer or infinity")),
    }
}

fn wait_for_io(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let reads = a.seq(0)?.clone();
    let writes = if a.args.len() > 1 { Some(a.seq(1)?.clone()) } else { None };
    let limit = time_limit(a)?;
    let start = std::time::Instant::now();
    loop {
        it.check_interrupt()?;
        let mut ready_r = Vec::new();
        for value in &reads.elems {
            let Value::Io(io) = value else { return Err(RuntimeError::runtime("WaitForIO expects I/O objects")) };
            advance_async(io)?;
            if io.async_io.borrow().ready.is_some() || (io.async_io.borrow().read.is_none() && socket_readable(io)?) {
                ready_r.push(value.clone());
            }
        }
        let mut ready_w = Vec::new();
        if let Some(writes) = &writes {
            for value in &writes.elems {
                let Value::Io(io) = value else { return Err(RuntimeError::runtime("WaitForIO expects I/O objects")) };
                advance_async(io)?;
                if io.async_io.borrow().writes.is_empty() && matches!(&*io.state.borrow(), IoState::Writer(_) | IoState::Socket { .. }) {
                    ready_w.push(value.clone());
                }
            }
        }
        let expired = limit.is_some_and(|d| start.elapsed() >= d);
        if !ready_r.is_empty() || !ready_w.is_empty() || expired {
            let r = Value::seq(reads.universe.clone(), ready_r);
            return if let Some(w) = writes { Ok(vals![r, Value::seq(w.universe.clone(), ready_w)]) } else { one(r) };
        }
        let pause = limit.map(|d| d.saturating_sub(start.elapsed()).min(std::time::Duration::from_millis(1))).unwrap_or(std::time::Duration::from_millis(1));
        std::thread::sleep(pause);
    }
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
            IoState::PipeReader { child, stdout: Some(std::io::BufReader::new(stdout)), eof: false }
        }
        "w" => {
            let mut child = command.stdin(std::process::Stdio::piped()).spawn().map_err(|e| RuntimeError::runtime(e.to_string()))?;
            let stdin = child.stdin.take().ok_or_else(|| RuntimeError::runtime("Could not open process input"))?;
            IoState::PipeWriter { child, stdin: Some(stdin) }
        }
        _ => return Err(RuntimeError::runtime(format!("Bad mode \"{mode}\""))),
    };
    one(Value::Io(IoObj::new(cmd, mode, IoKind::Pipe, state)))
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
    let max = [("Max", Value::int(0))];
    it.def_params("Read", "I::IO -> MonStgElt", &max, "Data available from I, optionally limited to Max bytes.", read_io);
    it.def("Read", "I::IO, n::RngIntElt -> MonStgElt", "Up to n characters from I.", read_io);
    it.def_params("ReadCheck", "I::IO -> BoolElt, MonStgElt", &max, "Whether a read succeeded and its data.", read_check);
    it.def("ReadCheck", "I::IO, n::RngIntElt -> BoolElt, MonStgElt", "Whether an n-byte read succeeded and its data.", read_check);
    it.def_params("ReadBytes", "I::IO -> SeqEnum", &max, "Bytes available from I, optionally limited to Max bytes.", read_bytes);
    it.def("ReadBytes", "I::IO, n::RngIntElt -> SeqEnum", "Up to n bytes from I.", read_bytes);
    it.def_params("ReadBytesCheck", "I::IO -> BoolElt, SeqEnum", &max, "Whether a byte read succeeded and its data.", read_bytes_check);
    it.def("ReadBytesCheck", "I::IO, n::RngIntElt -> BoolElt, SeqEnum", "Whether an n-byte read succeeded and its data.", read_bytes_check);
    it.def("Gets", "I::IO -> MonStgElt", "The next line of I (without its newline).", gets);
    it.def("Getc", "I::IO -> MonStgElt", "The next character of I.", getc);
    it.def("Ungetc", "I::IO, c::MonStgElt", "Push back the last character read from I.", ungetc);
    it.def("Puts", "I::., s::MonStgElt", "Write s and a newline to I.", puts);
    it.def("Put", "I::., s::MonStgElt", "Write s to I.", put);
    it.def("Write", "I::IO, s::MonStgElt", "Write s to I.", put);
    it.def("WriteCheck", "I::IO, s::MonStgElt -> BoolElt", "Whether s was written to I.", write_check);
    it.def("WriteBytes", "I::IO, S::SeqEnum", "Write the bytes in S to I.", write_bytes);
    it.def("WriteBytesCheck", "I::IO, S::SeqEnum -> BoolElt", "Whether the bytes in S were written to I.", write_bytes_check);
    it.def("ReadObject", "I::IO -> .", "Read one value in the versioned calyx object format from I.", read_object);
    it.def("ReadObjectCheck", "I::IO -> BoolElt, .", "Whether a calyx object was read and its value.", read_object_check);
    it.def("WriteObject", "I::IO, x::.", "Write x in the versioned calyx object format to I.", write_object);
    it.def("WriteObjectCheck", "I::IO, x::. -> BoolElt", "Whether x was written as a calyx object.", write_object_check);
    it.def("Flush", "I::IO", "Flush buffered output of I.", flush);
    it.def("Flush", "", "Flush standard output.", flush);
    it.def("Tell", "I::IO -> RngIntElt", "The current position in I.", tell);
    it.def("Seek", "I::IO, n::RngIntElt", "Move to position n in I.", seek);
    it.def("Rewind", "I::IO", "Move to the start of I.", rewind);
    it.def("Eof", "-> MonStgElt", "The end-of-file marker returned by reading functions.", eof);
    it.def("IsEof", "S::MonStgElt -> BoolElt", "Whether S is the end-of-file marker.", is_eof);
    it.def("AtEof", "I::IO -> BoolElt", "Whether I is at end of file.", at_eof);
    it.def("IOType", "I::IO -> MonStgElt", "The kind of I/O object I is.", io_type);
    let socket_params = [("LocalHost", Value::Undef), ("LocalPort", Value::int(0))];
    it.def_params("Socket", "H::MonStgElt, P::RngIntElt -> IOSocket", &socket_params, "Connect a TCP socket to H and P.", socket);
    it.def_params("Socket", "-> IOSocket", &socket_params, "Open a TCP server socket.", socket);
    it.def("WaitForConnection", "S::IOSocket -> IO", "Accept a connection on server socket S.", wait_for_connection);
    it.def("SocketInformation", "S::IO -> Tup, Tup", "The local and remote addresses of S.", socket_information);
    it.def("IsServerSocket", "S::IO -> BoolElt", "Whether S is a server socket.", is_server_socket);
    let wait = [("TimeLimit", Value::Infinity(true))];
    it.def_params("WaitForIO", "R::SeqEnum -> SeqEnum", &wait, "Wait for readable channels in R.", wait_for_io);
    it.def_params("WaitForIO", "R::SeqEnum, W::SeqEnum -> SeqEnum, SeqEnum", &wait, "Wait for readable channels in R and writable channels in W.", wait_for_io);
    it.def_params("AsyncRead", "I::IO", &max, "Queue a string read from I.", async_read);
    it.def("AsyncRead", "I::IO, n::RngIntElt", "Queue an n-byte string read from I.", async_read);
    it.def("AsyncWrite", "I::IO, s::MonStgElt", "Queue a string write to I.", async_write);
    it.def_params("AsyncReadBytes", "I::IO", &max, "Queue a byte-sequence read from I.", async_read_bytes);
    it.def("AsyncReadBytes", "I::IO, n::RngIntElt", "Queue an n-byte sequence read from I.", async_read_bytes);
    it.def("AsyncWriteBytes", "I::IO, S::SeqEnum", "Queue a byte-sequence write to I.", async_write_bytes);
    it.def("AsyncReadObject", "I::IO", "Queue a calyx object read from I.", async_read_object);
    it.def("AsyncWriteObject", "I::IO, x::.", "Queue a calyx object write to I.", async_write_object);
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
