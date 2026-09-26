//! The calyx interpreter: values, types, evaluation and intrinsics.

/// The results of a call, like `vec!` but without allocating for one value.
macro_rules! vals {
    ($($x:tt)*) => { smallvec::smallvec![$($x)*] };
}

pub mod abgroups;
pub mod coerce;
pub mod compile;
pub mod error;
pub mod interp;
pub mod intrinsics;
pub mod ir;
pub mod ops;
pub mod output;
pub mod perms;
pub mod print;
pub mod random;
pub mod rings;
pub mod session;
pub mod sym;
pub mod types;
pub mod value;

pub use error::{ErrKind, ErrStyle, RResult, RuntimeError};
pub use interp::Interp;
pub use session::ExecOutcome;
pub use value::Value;

/// A short description of a value's kind, for messages that have no access
/// to the type registry.
pub fn value_kind(v: &Value) -> &'static str {
    match v {
        Value::Undef => "undefined",
        Value::Bool(_) => "BoolElt",
        Value::Int(_) => "RngIntElt",
        Value::Rat(_) => "FldRatElt",
        Value::Real(_) => "FldReElt",
        Value::Complex(_) => "FldComElt",
        Value::Str(_) => "MonStgElt",
        Value::Seq(_) => "SeqEnum",
        Value::Set(_) => "SetEnum",
        Value::ISet(_) => "SetIndx",
        Value::MSet(_) => "SetMulti",
        Value::Formal(_) => "SetFormal",
        Value::Tuple(_) => "Tup",
        Value::List(_) => "List",
        Value::Rec(_) => "Rec",
        Value::Assoc(_) => "Assoc",
        Value::Func(_) => "UserProgram",
        Value::Intr(_) => "Intrinsic",
        Value::Map(_) => "Map",
        Value::Struct(_) => "structure",
        Value::Cat(_) => "Cat",
        Value::ECat(_) => "ECat",
        Value::Err(_) => "Err",
        Value::Obj(_) => "object",
        Value::CopElt(_) => "CopElt",
        Value::Io(_) => "IO",
        Value::Elt(_) | Value::Small(..) => "RngElt",
        Value::Perm(_) => "GrpPermElt",
        Value::AbElt(_) => "GrpAbElt",
        Value::Nfd(_) => "NfdElt",
        Value::Drch(_) => "GrpDrchElt",
        Value::Mat(_) => "Mtrx",
        Value::Sparse(_) => "MtrxSprs",
        Value::Infinity(_) => "Infty",
    }
}
