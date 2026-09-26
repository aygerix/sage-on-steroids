//! Character string intrinsics.

use calyx_flint::Integer;

use super::{boolv, intv, one};
use crate::error::{RResult, RuntimeError};
use crate::interp::{CallArgs, Interp};
use crate::print::Level;
use crate::value::*;

fn str_seq(v: Vec<String>) -> Value {
    Value::seq(Some(Value::strings()), v.into_iter().map(|s| Value::str(&s)).collect())
}

fn binary_string(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let bytes = match &a.args[0] {
        Value::Str(s) => s.as_bytes().to_vec(),
        Value::Seq(s) => {
            let mut out = Vec::with_capacity(s.elems.len());
            for v in &s.elems {
                let Value::Int(n) = v else { return Err(RuntimeError::runtime("Binary string entries must be integers")) };
                out.push(n.to_u64().filter(|n| *n <= 255).ok_or_else(|| RuntimeError::runtime("Binary string entries must be between 0 and 255"))? as u8);
            }
            out
        }
        _ => unreachable!(),
    };
    one(Value::bytes(bytes))
}

fn eltseq(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let s = a.str(0)?;
    one(str_seq(s.chars().map(|c| c.to_string()).collect()))
}

fn binary_eltseq(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::BStr(s) = &a.args[0] else { unreachable!() };
    one(Value::int_seq(s.iter().map(|b| Integer::from_u64(*b as u64))))
}

fn substring(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let s: Vec<char> = a.str(0)?.chars().collect();
    let n = a.i64(1)?;
    let k = a.i64(2)?;
    if n < 1 || k < 0 {
        return Err(RuntimeError::runtime("Position must be positive and length non-negative"));
    }
    let start = (n as usize - 1).min(s.len());
    let end = (start + k as usize).min(s.len());
    one(Value::str(&s[start..end].iter().collect::<String>()))
}

fn binary_substring(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let Value::BStr(s) = &a.args[0] else { unreachable!() };
    let n = a.i64(1)?;
    let k = a.i64(2)?;
    if n < 1 || k < 0 {
        return Err(RuntimeError::runtime("Position must be positive and length non-negative"));
    }
    let start = (n as usize - 1).min(s.len());
    let end = start.saturating_add(k as usize).min(s.len());
    one(Value::bytes(s[start..end].to_vec()))
}

fn position(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let s = a.str(0)?;
    let t = a.str(1)?;
    match s.find(t) {
        Some(byte) => one(Value::int(s[..byte].chars().count() as i64 + 1)),
        None => one(Value::int(0)),
    }
}

fn string_to_code(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    match a.str(0)?.chars().next() {
        Some(c) => one(Value::int(c as i64)),
        None => Err(RuntimeError::runtime("Argument must be a non-empty string")),
    }
}

fn code_to_string(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.i64(0)?;
    match u32::try_from(n).ok().and_then(char::from_u32) {
        Some(c) => one(Value::str(&c.to_string())),
        None => Err(RuntimeError::runtime("Invalid character code")),
    }
}

fn parse_int_in_base(s: &str, base: u32) -> RResult<Integer> {
    let t = s.trim();
    Integer::parse_radix(t, base).ok_or_else(|| RuntimeError::runtime(format!("\"{s}\" is not an integer in base {base}")))
}

fn string_to_integer(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let s = a.str(0)?;
    let base = if a.args.len() > 1 {
        match &a.args[1] {
            Value::Int(b) => b.to_u64().filter(|b| (2..=36).contains(b)).ok_or_else(|| RuntimeError::runtime("Base must be between 2 and 36"))? as u32,
            Value::Str(b) => b.trim().parse().map_err(|_| RuntimeError::runtime("Bad base"))?,
            _ => return Err(RuntimeError::runtime("Bad base")),
        }
    } else {
        10
    };
    intv(parse_int_in_base(s, base)?)
}

fn string_to_integer_sequence(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let s = a.str(0)?;
    let mut v = Vec::new();
    for w in s.split_whitespace() {
        v.push(parse_int_in_base(w, 10)?);
    }
    one(Value::int_seq(v))
}

fn integer_to_string(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let n = a.int(0)?;
    let base = if a.args.len() > 1 {
        let b = a.int(1)?;
        b.to_u64().filter(|b| (2..=36).contains(b)).ok_or_else(|| super::arg_range(2, b, 2, 36))? as u32
    } else {
        10
    };
    one(Value::str(&n.to_string_radix(base).to_uppercase()))
}

fn split(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let s = a.str(0)?.to_string();
    let delims: Vec<char> = if a.args.len() > 1 { a.str(1)?.chars().collect() } else { vec!['\n'] };
    let include_empty = a.param_bool("IncludeEmpty")?;
    if delims.is_empty() {
        return one(str_seq(vec![s]));
    }
    let mut parts: Vec<String> = s.split(|c| delims.contains(&c)).map(String::from).collect();
    if !include_empty {
        parts.retain(|p| !p.is_empty());
    } else if parts.last().is_some_and(|p| p.is_empty()) {
        parts.pop();
    }
    one(str_seq(parts))
}

fn regexp(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let pat = a.str(0)?;
    let s = a.str(1)?;
    let re = regex::Regex::new(pat).map_err(|e| RuntimeError::runtime(format!("Bad regular expression: {e}")))?;
    match re.captures(s) {
        Some(caps) => {
            let whole = caps.get(0).map(|m| m.as_str()).unwrap_or("").to_string();
            let groups: Vec<String> = (1..caps.len()).map(|i| caps.get(i).map(|m| m.as_str().to_string()).unwrap_or_default()).collect();
            Ok(vals![Value::Bool(true), Value::str(&whole), str_seq(groups)])
        }
        None => Ok(vals![Value::Bool(false), Value::Undef, Value::Undef]),
    }
}

fn sprint(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let v = a.args[0].clone();
    let level = if a.args.len() > 1 {
        let l = a.str(1)?;
        Level::parse(l).ok_or_else(|| RuntimeError::runtime(format!("Unknown print level '{l}'")))?
    } else {
        Level::Default
    };
    one(Value::str(&it.format_bare(&v, level)?))
}

fn sprintf(it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    let vals = a.args.clone();
    one(Value::str(&it.sprintf(&vals)?))
}

fn to_lower(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::str(&a.str(0)?.to_lowercase()))
}

fn to_upper(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::str(&a.str(0)?.to_uppercase()))
}

fn reverse_string(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    one(Value::str(&a.str(0)?.chars().rev().collect::<String>()))
}

fn is_empty_string(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    boolv(a.str(0)?.is_empty())
}

fn strings(_it: &mut Interp, _a: &mut CallArgs) -> RResult<Vals> {
    one(Value::strings())
}

fn int_from_string(_it: &mut Interp, a: &mut CallArgs) -> RResult<Vals> {
    intv(parse_int_in_base(a.str(0)?, 10)?)
}

pub fn register(it: &mut Interp) {
    for name in ["BinaryString", "BString"] {
        it.def(name, "s::MonStgElt -> BStgElt", "The bytes of s as a binary string.", binary_string);
        it.def(name, "s::SeqEnum -> BStgElt", "The integers in s as a binary string.", binary_string);
    }
    it.def("ElementToSequence", "s::MonStgElt -> [MonStgElt]", "The characters of s as a sequence of strings.", eltseq);
    it.def("Eltseq", "s::MonStgElt -> [MonStgElt]", "The characters of s as a sequence of strings.", eltseq);
    it.def("ElementToSequence", "s::BStgElt -> [RngIntElt]", "The bytes of s as a sequence of integers.", binary_eltseq);
    it.def("Eltseq", "s::BStgElt -> [RngIntElt]", "The bytes of s as a sequence of integers.", binary_eltseq);
    it.def("Substring", "s::MonStgElt, n::RngIntElt, k::RngIntElt -> MonStgElt", "The substring of s of length k starting at position n.", substring);
    it.def("Substring", "s::BStgElt, n::RngIntElt, k::RngIntElt -> BStgElt", "The binary substring of s of length k starting at position n.", binary_substring);
    it.def("Index", "s::MonStgElt, t::MonStgElt -> RngIntElt", "The position of the first occurrence of t in s, or 0.", position);
    it.def("Position", "s::MonStgElt, t::MonStgElt -> RngIntElt", "The position of the first occurrence of t in s, or 0.", position);
    it.def("StringToCode", "s::MonStgElt -> RngIntElt", "The character code of the first character of s.", string_to_code);
    it.def("CodeToString", "n::RngIntElt -> MonStgElt", "The one-character string with character code n.", code_to_string);
    it.def("StringToInteger", "s::MonStgElt -> RngIntElt", "The integer written in decimal in s.", string_to_integer);
    it.def("StringToInteger", "s::MonStgElt, b::RngIntElt -> RngIntElt", "The integer written in base b in s.", string_to_integer);
    it.def("StringToInteger", "s::MonStgElt, b::MonStgElt -> RngIntElt", "The integer written in base b in s.", string_to_integer);
    it.def("StringToIntegerSequence", "s::MonStgElt -> [RngIntElt]", "The integers written in s separated by spaces.", string_to_integer_sequence);
    it.def("IntegerToString", "n::RngIntElt -> MonStgElt", "The decimal representation of n.", integer_to_string);
    it.def("IntegerToString", "n::RngIntElt, b::RngIntElt -> MonStgElt", "The base b representation of n.", integer_to_string);
    it.def_params("Split", "S::MonStgElt, D::MonStgElt -> [MonStgElt]", &[("IncludeEmpty", Value::Bool(false))], "The fields of S separated by any of the characters in D.", split);
    it.def_params("Split", "S::MonStgElt -> [MonStgElt]", &[("IncludeEmpty", Value::Bool(false))], "The lines of S.", split);
    it.def("Regexp", "R::MonStgElt, S::MonStgElt -> BoolElt, MonStgElt, [MonStgElt]", "Whether S matches the regular expression R, the matching substring, and the parenthesised submatches.", regexp);
    it.def("Sprint", "x::. -> MonStgElt", "The string printed for x.", sprint);
    it.def("Sprint", "x::., L::MonStgElt -> MonStgElt", "The string printed for x at print level L.", sprint);
    it.def("Sprintf", "F::MonStgElt, ... -> MonStgElt", "The string produced by printf with format F and the remaining arguments.", sprintf);
    it.def("ToLower", "s::MonStgElt -> MonStgElt", "s in lower case.", to_lower);
    it.def("ToUpper", "s::MonStgElt -> MonStgElt", "s in upper case.", to_upper);
    it.def("Reverse", "s::MonStgElt -> MonStgElt", "s reversed.", reverse_string);
    it.def("IsEmpty", "s::MonStgElt -> BoolElt", "Whether s is the empty string.", is_empty_string);
    it.def("Strings", "-> MonStg", "The structure of all strings.", strings);
    it.def("Integer", "s::MonStgElt -> RngIntElt", "The integer written in decimal in s.", int_from_string);
}
