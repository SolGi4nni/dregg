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

use dregg_cell::factory::FactoryDescriptor;
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
    CapEdge {
        target: [u8; 32],
        slot: u32,
    },
    /// Raw field-element slot contents.
    FieldSlot {
        index: usize,
        hex: String,
    },
}

/// One labeled field of an inspectable object.
#[derive(Clone, Debug)]
pub struct Field {
    pub key: String,
    pub value: FieldValue,
}

impl Field {
    pub fn text(key: impl Into<String>, v: impl Into<String>) -> Self {
        Field {
            key: key.into(),
            value: FieldValue::Text(v.into()),
        }
    }
    pub fn balance(key: impl Into<String>, v: i64) -> Self {
        Field {
            key: key.into(),
            value: FieldValue::Balance(v),
        }
    }
    pub fn count(key: impl Into<String>, v: u64) -> Self {
        Field {
            key: key.into(),
            value: FieldValue::Count(v),
        }
    }
    pub fn boolean(key: impl Into<String>, v: bool) -> Self {
        Field {
            key: key.into(),
            value: FieldValue::Bool(v),
        }
    }
    pub fn id(key: impl Into<String>, v: [u8; 32]) -> Self {
        Field {
            key: key.into(),
            value: FieldValue::Id(v),
        }
    }
    pub fn hash(key: impl Into<String>, v: [u8; 32]) -> Self {
        Field {
            key: key.into(),
            value: FieldValue::Hash(v),
        }
    }
}

/// What kind of dregg object this is (drives the view's icon/affordances).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ObjectKind {
    Cell,
    Capability,
    Receipt,
    Image,
    /// A turn's proof / verification status (the STARK axis).
    Proof,
    /// A deployed factory descriptor (the birth-template object).
    Factory,
    /// A consumed nullifier / spent-capability witness (the privacy axis).
    Nullifier,
    /// A literate document — the Pijul-shaped patch-theory object (`dregg_doc`):
    /// rendered content, patch history, conflict-as-state, provenance.
    Document,
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
        Field::text(
            "delegation_epoch",
            cell.state.delegation_epoch().to_string(),
        ),
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
        subtitle: format!(
            "{} computrons · {} caps",
            cell.state.balance(),
            cell.capabilities.len()
        ),
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
            Field::text("executor", "embedded verified (TurnExecutor)".to_string()),
        ],
    }
}

/// Project a turn's PROOF / VERIFICATION STATUS — the STARK axis as an
/// inspectable object. Reads the real [`TurnReceipt`]: whether the executor
/// signed it (the producer's attestation), its finality, and the in-band
/// disclosure flags (`was_burn` / `was_encrypted`) bound into `receipt_hash`.
///
/// In the embedded single-custody world the producer IS this process, so a
/// committed turn is verified-by-construction: the receipt's existence is the
/// proof that the whole-turn guarantees held. A federated node additionally
/// carries an explicit STARK (the `full_turn_proof` lane); this view surfaces
/// the attestation surface the receipt exposes either way.
pub fn reflect_proof_status(r: &TurnReceipt) -> Inspectable {
    let signed = r.executor_signature.is_some();
    let fields = vec![
        Field::hash("turn_hash", r.turn_hash),
        Field::hash("forest_hash", r.forest_hash),
        Field::hash("effects_hash", r.effects_hash),
        Field::hash("pre_state", r.pre_state_hash),
        Field::hash("post_state", r.post_state_hash),
        Field::boolean("executor_signed", signed),
        Field::text("finality", format!("{:?}", r.finality)),
        Field::boolean("burn_disclosed", r.was_burn),
        Field::boolean("encrypted", r.was_encrypted),
        Field::count("computrons", r.computrons_used),
        Field::text(
            "verification",
            if signed {
                "executor-signed (producer attested)".to_string()
            } else {
                "verified-by-construction (embedded executor)".to_string()
            },
        ),
    ];
    Inspectable {
        kind: ObjectKind::Proof,
        title: format!("Proof status · {}", short_hex(&r.receipt_hash())),
        subtitle: format!(
            "{} · {:?} · pre {} → post {}",
            if signed {
                "executor-signed"
            } else {
                "verified-by-construction"
            },
            r.finality,
            short_hex(&r.pre_state_hash),
            short_hex(&r.post_state_hash),
        ),
        fields,
    }
}

/// Project a deployed [`FactoryDescriptor`] — the birth-template object an
/// author deploys and `CreateCellFromFactory` instantiates. Reflects its
/// content-addressed identity, the child program it pins, the cap templates a
/// child may be granted, the perpetual slot caveats baked into every child, and
/// the per-epoch creation budget.
pub fn reflect_factory(f: &FactoryDescriptor) -> Inspectable {
    let mut fields = vec![
        Field::id("factory_vk", f.factory_vk),
        Field::hash("descriptor_hash", f.hash()),
        Field::boolean("child_program", f.child_program_vk.is_some()),
        Field::count("cap_templates", f.allowed_cap_templates.len() as u64),
        Field::count("slot_caveats", f.state_constraints.len() as u64),
        Field::count("field_constraints", f.field_constraints.len() as u64),
        Field::text("default_mode", format!("{:?}", f.default_mode)),
    ];
    if let Some(vk) = f.child_program_vk {
        fields.push(Field::id("child_program_vk", vk));
    }
    if let Some(budget) = f.creation_budget {
        fields.push(Field::count("creation_budget", budget));
    }
    Inspectable {
        kind: ObjectKind::Factory,
        title: format!("Factory {}", short_hex(&f.factory_vk)),
        subtitle: format!(
            "{} cap template(s) · {} perpetual caveat(s)",
            f.allowed_cap_templates.len(),
            f.state_constraints.len()
        ),
        fields,
    }
}

/// Catalog the NULLIFIERS / spent capabilities a committed turn consumed — the
/// privacy/double-spend-prevention axis. Each consumed-capability witness in a
/// receipt is a nullifier-shaped object (a one-time authority that cannot be
/// reused); this projects them as inspectable objects so the cockpit can show
/// "what was spent" in a turn.
pub fn reflect_nullifiers(r: &TurnReceipt) -> Vec<Inspectable> {
    r.consumed_capabilities
        .iter()
        .enumerate()
        .map(|(i, wit)| Inspectable {
            kind: ObjectKind::Nullifier,
            title: format!("Nullifier #{i} · {}", short_hex(&r.receipt_hash())),
            subtitle: format!(
                "holder {} · slot {} (one-time authority spent)",
                short_hex(wit.holder.as_bytes()),
                wit.slot
            ),
            fields: vec![
                Field::count("index", i as u64),
                Field::id("holder", *wit.holder.as_bytes()),
                Field::count("slot", wit.slot as u64),
                Field::count("cap_root", wit.cap_root as u64),
                Field::hash("in_receipt", r.receipt_hash()),
                Field::boolean("spent", true),
            ],
        })
        .collect()
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
        assert!(obj
            .fields
            .iter()
            .any(|f| matches!(f.value, FieldValue::Balance(500))));
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

    #[test]
    fn reflects_proof_status_of_a_committed_turn() {
        let mut w = World::new();
        let a = w.genesis_cell(1, 100);
        let b = w.genesis_cell(2, 0);
        let turn = w.turn(a, vec![transfer(a, b, 10)]);
        assert!(w.commit_turn(turn).is_committed());
        let r = &w.receipts()[0];
        let obj = reflect_proof_status(r);
        assert_eq!(obj.kind, ObjectKind::Proof);
        assert!(obj.fields.iter().any(|f| f.key == "verification"));
        assert!(obj.fields.iter().any(|f| f.key == "post_state"));
    }

    #[test]
    fn reflects_a_factory_descriptor() {
        use crate::edit::{FactoryBuilder, ProgramBuilder};
        use dregg_cell::factory::CapTarget;
        use dregg_cell::AuthRequired;
        let program = ProgramBuilder::new().monotonic(0).build();
        let f = FactoryBuilder::new([0xAB; 32])
            .child_program(&program)
            .allow_cap(CapTarget::SelfCell, AuthRequired::None, true)
            .creation_budget(5)
            .build();
        let obj = reflect_factory(&f);
        assert_eq!(obj.kind, ObjectKind::Factory);
        assert!(obj.fields.iter().any(|f| f.key == "factory_vk"));
        assert!(obj.fields.iter().any(|f| f.key == "creation_budget"));
        assert!(obj.fields.iter().any(|f| f.key == "slot_caveats"));
    }

    #[test]
    fn reflects_nullifiers_catalog_is_empty_for_a_plain_transfer() {
        // A plain Unchecked transfer consumes no capabilities → no nullifiers.
        let mut w = World::new();
        let a = w.genesis_cell(1, 100);
        let b = w.genesis_cell(2, 0);
        let turn = w.turn(a, vec![transfer(a, b, 10)]);
        assert!(w.commit_turn(turn).is_committed());
        let nulls = reflect_nullifiers(&w.receipts()[0]);
        assert!(
            nulls.is_empty(),
            "an Unchecked transfer spends no one-time authority"
        );
    }
}
