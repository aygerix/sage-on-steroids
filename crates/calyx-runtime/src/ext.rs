//! The plug-in point for kinds of structures defined outside the core (#62).
//!
//! A structure of kind `StructKind::Ext` holds an [`ExtKind`], which is both
//! the structure's data and its behaviour, and its elements are
//! `Value::Ext`, each an [`ExtElt`]: its parent and its own data. What the
//! core needs from them (their types, equality, hashing, printing, coercion
//! and operators) goes through the trait, so a new kind lives in its own
//! module and touches no shared file, except types.rs for its type names.
//!
//! Only `struct_type`, `elt_type` and `fmt_struct` are required. A kind
//! whose structures have elements implements the element methods too; the
//! defaults suit a structure without elements of its own.

use std::any::Any;
use std::hash::Hasher;
use std::rc::Rc;

use calyx_syntax::ast::BinOp;

use crate::error::RResult;
use crate::interp::Interp;
use crate::print::Printer;
use crate::types::{TypeId, TypeVal};
use crate::value::{Struct, StructKind, Value};

/// The outcome of a coercion: the value, or failure with an optional reason.
pub type Coerced = Result<Value, Option<String>>;

/// A kind of structure. Each structure of the kind holds one, and the
/// core calls on it for the structure and for its elements.
pub trait ExtKind: Any {
    /// The type of the structure.
    fn struct_type(&self) -> TypeId;

    /// The type of its elements.
    fn elt_type(&self) -> TypeId;

    /// The element type as errors show it, with its type arguments (the
    /// base ring, say).
    fn elt_type_ext(&self) -> TypeVal {
        TypeVal::Cat(self.elt_type())
    }

    /// Whether the structure equals `other`, another structure of any kind.
    /// Each construction is a new structure by default.
    fn struct_eq(&self, _other: &dyn ExtKind) -> bool {
        false
    }

    /// A hash of the structure, consistent with `struct_eq`: by default its
    /// address.
    fn struct_hash(&self, state: &mut dyn Hasher) {
        state.write_usize((self as *const Self).cast::<()>() as usize);
    }

    /// The error `eq` raises between the structure and `other`, a different
    /// structure, or None when the core's rules apply.
    fn incomparable(&self, _other: &dyn ExtKind) -> Option<&'static str> {
        None
    }

    fn fmt_struct(&self, it: &mut Interp, p: &mut Printer, st: &Struct, indent: usize) -> RResult<()>;

    /// Whether x and y, elements of structures of this kind, are the same
    /// value, as sets and hashing see them.
    fn elt_same(&self, _x: &ExtElt, _y: &ExtElt) -> bool {
        false
    }

    /// A hash of an element, consistent with `elt_same`.
    fn elt_hash(&self, _x: &ExtElt, _state: &mut dyn Hasher) {}

    fn fmt_elt(&self, _it: &mut Interp, p: &mut Printer, _x: &ExtElt, _indent: usize) -> RResult<()> {
        p.write("<element>");
        Ok(())
    }

    /// Whether an element prints on one line inside an aggregate.
    fn elt_is_simple(&self, _x: &ExtElt) -> bool {
        true
    }

    /// `st ! x` (`strict`), or an attempt to coerce x into `st`, a structure
    /// of this kind. Only `!` reports the errors that `strict` asks for.
    fn coerce(&self, _it: &mut Interp, _st: &Rc<Struct>, _x: &Value, _strict: bool) -> RResult<Coerced> {
        Ok(Err(None))
    }

    /// `s ! x` for an element x of this kind and a structure s not of this
    /// kind.
    fn coerce_out(&self, _it: &mut Interp, _s: &Value, _x: &ExtElt) -> RResult<Coerced> {
        Ok(Err(None))
    }

    /// A binary operator with an element of this kind among the operands
    /// (`x in S` too, for any structure S), or None when the kind has no
    /// rule for it.
    fn binop(&self, _it: &mut Interp, _op: BinOp, _a: &Value, _b: &Value) -> RResult<Option<Value>> {
        Ok(None)
    }

    /// A binary operator with a structure of this kind among the operands
    /// and no element of an `ExtKind` (`L + M`, `n * L`, `L subset M`,
    /// `v in L`), or None to leave it to the core's rules.
    fn struct_binop(&self, _it: &mut Interp, _op: BinOp, _a: &Value, _b: &Value) -> RResult<Option<Value>> {
        Ok(None)
    }

    /// `-x`, or None to leave it to user-defined operators.
    fn negate(&self, _it: &mut Interp, _x: &ExtElt) -> RResult<Option<Value>> {
        Ok(None)
    }

    /// `a eq b` (`strict`) or `a cmpeq b` with an element of this kind among
    /// them, or None to leave it to the core's rules.
    fn compare_eq(&self, _it: &mut Interp, _a: &Value, _b: &Value, _strict: bool) -> RResult<Option<bool>> {
        Ok(None)
    }
}

/// An element of a structure of an `ExtKind`: its parent, and its data, of
/// a type the kind chooses.
pub struct ExtElt {
    pub parent: Rc<Struct>,
    data: Box<dyn Any>,
}

impl ExtElt {
    /// The kind of the element's parent.
    pub fn kind(&self) -> &dyn ExtKind {
        match &self.parent.kind {
            StructKind::Ext(k) => &**k,
            _ => unreachable!("the parent of an element of an Ext kind"),
        }
    }

    /// The element's data, of the type its kind stores.
    pub fn data<T: 'static>(&self) -> &T {
        self.data.downcast_ref().expect("the data type of the kind")
    }
}

/// A new structure of the kind k.
pub fn structure(k: impl ExtKind) -> Rc<Struct> {
    Struct::new(StructKind::Ext(Rc::new(k)))
}

/// A new element of `parent`, a structure of an `ExtKind`.
pub fn element<T: 'static>(parent: &Rc<Struct>, data: T) -> Value {
    debug_assert!(matches!(parent.kind, StructKind::Ext(_)));
    Value::Ext(Rc::new(ExtElt { parent: parent.clone(), data: Box::new(data) }))
}

/// The kind of a structure, if it is of an `ExtKind`.
pub fn kind(st: &Struct) -> Option<&dyn ExtKind> {
    match &st.kind {
        StructKind::Ext(k) => Some(&**k),
        _ => None,
    }
}

/// The kind of a structure, if it is of the kind K.
pub fn kind_of<K: ExtKind>(st: &Struct) -> Option<&K> {
    kind(st).and_then(|k| (k as &dyn Any).downcast_ref())
}

/// The kind of a structure of the kind K; a structure of another kind is a
/// bug in the caller (an intrinsic whose signature admits only K).
pub fn expect_kind<K: ExtKind>(st: &Struct) -> &K {
    kind_of(st).expect("a structure of the kind")
}

/// Whether a and b are of the same kind (the same type, not the same
/// structure).
pub fn same_kind(a: &dyn ExtKind, b: &dyn ExtKind) -> bool {
    (a as &dyn Any).type_id() == (b as &dyn Any).type_id()
}

/// Whether s is a structure of the same kind as k.
pub fn is_of_kind(s: &Value, k: &dyn ExtKind) -> bool {
    match s {
        Value::Struct(st) => kind(st).is_some_and(|j| same_kind(j, k)),
        _ => false,
    }
}

/// The kind of the first element of an `ExtKind` among a and b.
pub fn operand_kind<'a>(a: &'a Value, b: &'a Value) -> Option<&'a dyn ExtKind> {
    match (a, b) {
        (Value::Ext(x), _) | (_, Value::Ext(x)) => Some(x.kind()),
        _ => None,
    }
}

/// The kind of the first structure of an `ExtKind` among a and b.
pub fn struct_operand_kind<'a>(a: &'a Value, b: &'a Value) -> Option<&'a dyn ExtKind> {
    [a, b].into_iter().find_map(|v| match v {
        Value::Struct(st) => kind(st),
        _ => None,
    })
}
