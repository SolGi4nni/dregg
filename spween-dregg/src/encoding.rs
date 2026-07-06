//! Value ⇄ field encoding — the numeric projection of a spween [`Value`] into a
//! dregg cell slot.
//!
//! The cell holds an *unsigned big-endian* numeric projection of each variable
//! (the representation the executor's `FieldGte`/`FieldLte`/`FieldEquals` gates
//! compare on). Full-fidelity spween `Value`s (strings, floats, `Null`) live in the
//! handler's read-overlay; the slot carries the number the gate needs. Non-numeric
//! or negative values project to `0`.

use dregg_app_framework::{FieldElement, field_from_u64};
use spween::Value;

/// The unsigned projection of a [`Value`] used for the cell slot / executor gate.
pub fn value_to_u64(v: &Value) -> u64 {
    match v {
        Value::Int(n) if *n >= 0 => *n as u64,
        Value::Bool(b) => *b as u64,
        Value::Float(f) if *f >= 0.0 => *f as u64,
        // Null, String, and negatives carry no numeric slot meaning.
        _ => 0,
    }
}

/// Encode a [`Value`] as the cell's numeric field.
pub fn value_to_field(v: &Value) -> FieldElement {
    field_from_u64(value_to_u64(v))
}

/// Decode a cell field's last-8-bytes big-endian u64.
pub fn field_to_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}
