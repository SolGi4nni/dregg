//! The reflective object model — every dregg datum as an inspectable live
//! object behind ONE uniform interface.
//!
//! This is the Smalltalk-surpassing core: in Smalltalk every object is live and
//! inspectable; here EVERY dregg datum (cell, capability, receipt, the image
//! itself) is presented as an [`Inspectable`] — a uniform tree of typed
//! key/value [`Field`]s that any view (the inspector, the graph, the blocklace
//! browser) renders the same way, with the four dregg axes annotated inline
//! (ocap edges, verification status, provenance links, the image commitment).
//!
//! It reads the live `World` (the embedded executor's ledger + receipt log) and
//! projects it — it never copies the protocol types into a parallel wire schema,
//! so it can never drift from what the executor actually holds.

use dregg_cell::{Cell, CellId};
use dregg_turn::turn::TurnReceipt;

use crate::world::World;

/// A typed value in an inspectable object's field list. The view renders each
/// variant distinctly (an id is clickable → navigates; a `CapEdge` draws a
/// graph edge; a `Provenance` link navigates the blocklace).
#[derive(Clone, Debug)]
pub enum FieldValue {
    Text(String),
    /// A signed balance (issuer wells carry −supply — render distinctly).
    Balance(i64),
    Count(u64),
    Bool(bool),
    /// A 32-byte hex id that navigates to another object when clicked.
    Id([u8; 32]),
    /// A 32-byte hash (receipt/turn/state-commit) — provenance, navigable.
    Hash([u8; 32]),
    /// A capability edge (this object → target), the ocap-graph primitive.
    CapEdge { target: [u8; 32], slot: u32 },
    /// Raw field-element slot contents.
    FieldSlot { index: usize, hex: String },
}

/// One labeled field of an inspectable object.
#[derive(Clone, Debug)]
pub struct Field {
    pub key: String,
    pub value: FieldValue,
}

impl Field {
    pub fn text(key: impl Into<String>, v: impl Into<String>) -> Self {
        Field { key: key.into(), value: FieldValue::Text(v.into()) }
    }
    pub fn balance(key: impl Into<String>, v: i64) -> Self {
        Field { key: key.into(), value: FieldValue::Balance(v) }
    }
    pub fn count(key: impl Into<String>, v: u64) -> Self {
        Field { key: key.into(), value: FieldValue::Count(v) }
    }
    pub fn boolean(key: impl Into<String>, v: bool) -> Self {
        Field { key: key.into(), value: FieldValue::Bool(v) }
    }
    pub fn id(key: impl Into<String>, v: [u8; 32]) -> Self {
        Field { key: key.into(), value: FieldValue::Id(v) }
    }
    pub fn hash(key: impl Into<String>, v: [u8; 32]) -> Self {
        Field { key: key.into(), value: FieldValue::Hash(v) }
    }
}

/// What kind of dregg object this is (drives the view's icon/affordances).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ObjectKind {
    Cell,
    Capability,
    Receipt,
    Image,
}

/// The uniform reflective view of ANY dregg object. Every view consumes this;
/// no view knows the concrete protocol type.
#[derive(Clone, Debug)]
pub struct Inspectable {
    pub kind: ObjectKind,
    pub title: String,
    pub subtitle: String,
    pub fields: Vec<Field>,
}

/// Project a cell into the uniform reflective object.
pub fn reflect_cell(id: &CellId, cell: &Cell) -> Inspectable {
    let has_program = !matches!(cell.program, dregg_cell::CellProgram::None);
    let mut fields = vec![
        Field::id("id", *id.as_bytes()),
        Field::balance("balance", cell.state.balance()),
        Field::count("nonce", cell.state.nonce()),
        Field::id("public_key", *cell.public_key()),
        Field::id("token_id", *cell.token_id()),
        Field::count("capabilities", cell.capabilities.len() as u64),
        Field::boolean("has_delegate", cell.delegate.is_some()),
        Field::boolean("has_program", has_program),
        Field::text("lifecycle", format!("{:?}", cell.lifecycle)),
        Field::text("mode", format!("{:?}", cell.mode)),
        Field::text("delegation_epoch", cell.state.delegation_epoch().to_string()),
    ];
    if let Some(d) = &cell.delegate {
        fields.push(Field::id("delegate", *d.as_bytes()));
    }
    // The ocap graph: one CapEdge field per held capability.
    for cap in cell.capabilities.iter() {
        fields.push(Field {
            key: format!("cap[{}]", cap.slot),
            value: FieldValue::CapEdge {
                target: *cap.target.as_bytes(),
                slot: cap.slot,
            },
        });
    }
    // The 16 state-field slots (the cell's mutable state surface).
    for (i, fe) in cell.state.fields.iter().enumerate() {
        // Only surface non-zero slots to keep the inspector legible.
        if fe.iter().any(|b| *b != 0) {
            fields.push(Field {
                key: format!("state[{i}]"),
                value: FieldValue::FieldSlot {
                    index: i,
                    hex: hex::encode(fe),
                },
            });
        }
    }
    Inspectable {
        kind: ObjectKind::Cell,
        title: format!("Cell {}", short_hex(id.as_bytes())),
        subtitle: format!("{} computrons · {} caps", cell.state.balance(), cell.capabilities.len()),
        fields,
    }
}

/// Project a receipt into the uniform reflective object (the provenance node).
pub fn reflect_receipt(r: &TurnReceipt) -> Inspectable {
    let mut fields = vec![
        Field::hash("receipt_hash", r.receipt_hash()),
        Field::hash("turn_hash", r.turn_hash),
        Field::id("agent", *r.agent.as_bytes()),
        Field::hash("pre_state", r.pre_state_hash),
        Field::hash("post_state", r.post_state_hash),
        Field::count("computrons_used", r.computrons_used),
        Field::count("action_count", r.action_count as u64),
        Field::text("timestamp", r.timestamp.to_string()),
        Field::text("finality", format!("{:?}", r.finality)),
        Field::boolean("was_burn", r.was_burn),
        Field::boolean("was_encrypted", r.was_encrypted),
        Field::boolean("executor_signed", r.executor_signature.is_some()),
        Field::count("emitted_events", r.emitted_events.len() as u64),
        Field::count("consumed_caps", r.consumed_capabilities.len() as u64),
    ];
    if let Some(prev) = r.previous_receipt_hash {
        // The provenance link to the prior receipt (navigate the chain).
        fields.push(Field::hash("previous_receipt", prev));
    }
    Inspectable {
        kind: ObjectKind::Receipt,
        title: format!("Receipt {}", short_hex(&r.receipt_hash())),
        subtitle: format!(
            "agent {} · {} actions · {} computrons",
            short_hex(r.agent.as_bytes()),
            r.action_count,
            r.computrons_used
        ),
        fields,
    }
}

/// Project the whole image (the distribution axis) — the world's own object.
pub fn reflect_image(world: &World) -> Inspectable {
    Inspectable {
        kind: ObjectKind::Image,
        title: "This Image".into(),
        subtitle: format!(
            "{} cells · h{} · {} receipts",
            world.cell_count(),
            world.height(),
            world.receipts().len()
        ),
        fields: vec![
            Field::count("cells", world.cell_count() as u64),
            Field::count("height", world.height()),
            Field::count("receipts", world.receipts().len() as u64),
            Field::hash("state_root", world.state_root()),
            Field::text(
                "executor",
                "embedded verified (TurnExecutor)".to_string(),
            ),
        ],
    }
}

/// First 6 bytes of a 32-byte id, hex, as `abcdef…wxyz`.
pub fn short_hex(bytes: &[u8]) -> String {
    let h = hex::encode(bytes);
    short_hex_hexstr(&h)
}

/// Shorten an already-hex string to `abcdef…wxyz`.
pub fn short_hex_hexstr(h: &str) -> String {
    if h.len() <= 12 {
        h.to_string()
    } else {
        format!("{}…{}", &h[..6], &h[h.len() - 4..])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::{transfer, World};

    #[test]
    fn reflects_a_cell_with_its_fields() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 500);
        let cell = w.ledger().get(&a).unwrap();
        let obj = reflect_cell(&a, cell);
        assert_eq!(obj.kind, ObjectKind::Cell);
        // balance + nonce + id are always present.
        assert!(obj.fields.iter().any(|f| f.key == "balance"));
        assert!(obj.fields.iter().any(|f| f.key == "nonce"));
        assert!(obj.fields.iter().any(|f| matches!(f.value, FieldValue::Balance(500))));
    }

    #[test]
    fn reflects_a_receipt_after_a_commit() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 100);
        let b = w.genesis_cell(2, 0);
        let turn = w.turn(a, vec![transfer(a, b, 10)]);
        assert!(w.commit_turn(turn).is_committed());
        let r = &w.receipts()[0];
        let obj = reflect_receipt(r);
        assert_eq!(obj.kind, ObjectKind::Receipt);
        assert!(obj.fields.iter().any(|f| f.key == "receipt_hash"));
        assert!(obj.fields.iter().any(|f| f.key == "post_state"));
    }

    #[test]
    fn reflects_the_image() {
        let mut w = World::new();
        w.genesis_cell(1, 100);
        let obj = reflect_image(&w);
        assert_eq!(obj.kind, ObjectKind::Image);
        assert!(obj.fields.iter().any(|f| f.key == "state_root"));
    }
}
