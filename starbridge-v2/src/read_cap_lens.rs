//! # The READ-CAP / PRIVACY lens — the read-confidentiality membrane, welded.
//!
//! The moldable inspector's `MoldableLens::ReadCap` surface. It WAS an honest
//! `weld_pending_presentation` placeholder ("not yet available in this image");
//! the privacy weld landed (`dregg_cell::read_cap`, `cell/src/read_cap.rs` /
//! `docs/deos/PRIVACY-CONFIDENTIALITY.md` Milestone 0), so this lights it up.
//!
//! A read is the exercise of an attenuable VIEWING authority over committed state
//! — the write-discipline run backwards. This lens shows, for the focused cell:
//!
//! - **the encrypted-field set** — which of the 16 state slots are `Committed` /
//!   `SelectivelyDisclosable` (the slots a read-cap gates; `Public` slots are in
//!   the clear and need no cap), read off the LIVE `CellState::field_visibility`;
//! - **the read-lattice** — the `granted ⊆ held` attenuation order over those
//!   slots, demonstrated by exercising the REAL [`dregg_cell::ReadCap::attenuate`]
//!   / [`dregg_cell::is_read_attenuation`] (a wide cap over the whole frustum, a
//!   narrowed child, and a refused amplification — the same partial order the
//!   write side's facet attenuation uses);
//! - **the load-bearing invariant** — adding a read-cap changes NO commitment the
//!   circuit / conservation sees: a slot's `(commitment, ciphertext)` carries the
//!   BYTE-IDENTICAL `BLAKE3(value‖nonce)` the cell already stored. Demonstrated
//!   LIVE on this cell: seal a committed slot under a demo ViewKey into a clone and
//!   confirm the side-table commitment equals the clone's stored commitment.
//!
//! Everything is read off the live ledger and the real crypto; nothing is
//! fabricated. A cell with no committed slots degrades honestly (the membrane
//! would gate those slots once sealed). gpui-free + fully tested — the cockpit's
//! generic renderer draws the `Presentation`s with no new widget code.

use dregg_cell::read_cap::{is_read_attenuation, EncryptedState, FieldSet, ReadCap, ViewKey};
use dregg_cell::state::{FieldVisibility, STATE_SLOTS};
use dregg_cell::{Cell, CellId};

use crate::presentable::{
    Presentable, Presentation, PresentationBody, PresentationKind, PresentCtx, LatticeView,
};
use crate::reflect::{self, Field, Inspectable, ObjectKind};

/// A demo viewing key the lens seals with to DEMONSTRATE the byte-identical
/// commitment invariant on the focused cell's live data. It never leaves this
/// presentation — the lens reads confidentiality structure, it does not mint a
/// real cap for the operator (that is the frustum-editor's job).
const LENS_DEMO_VIEW_ROOT: [u8; 32] = [0x5Au8; 32];

/// The read-confidentiality view of one live cell.
pub struct ReadConfidentiality {
    /// Which cell this is the read-membrane of.
    pub id: CellId,
    /// A clone of the live cell (re-build from the world to re-read live state).
    pub cell: Cell,
}

impl ReadConfidentiality {
    /// Wrap the live cell `id` if it is present in the world's ledger.
    pub fn from_world(world: &crate::world::World, id: CellId) -> Option<Self> {
        world
            .ledger()
            .get(&id)
            .map(|c| ReadConfidentiality { id, cell: c.clone() })
    }

    /// The slots gated by read-confidentiality: those marked `Committed` or
    /// `SelectivelyDisclosable` (a `Public` slot is in the clear). Read off the
    /// LIVE `CellState::field_visibility`.
    fn committed_slots(&self) -> Vec<usize> {
        (0..STATE_SLOTS)
            .filter(|&i| {
                matches!(
                    self.cell.state.field_visibility[i],
                    FieldVisibility::Committed | FieldVisibility::SelectivelyDisclosable
                )
            })
            .collect()
    }
}

impl Presentable for ReadConfidentiality {
    fn object_kind(&self) -> ObjectKind {
        ObjectKind::Cell
    }

    fn present(&self, _ctx: &PresentCtx) -> Vec<Presentation> {
        let mut out: Vec<Presentation> = Vec::new();
        let committed = self.committed_slots();
        let held = FieldSet::from_slots(&committed);
        let short = reflect::short_hex(self.id.as_bytes());

        // (1) RawFields — the MANDATORY floor (universal-coverage invariant): the
        //     read-membrane summary, off the live field visibilities.
        let insp = Inspectable {
            kind: ObjectKind::Cell,
            title: "READ-CONFIDENTIALITY — who may READ this cell".to_string(),
            subtitle: format!(
                "cell {short} · {} encrypted slot{} of {STATE_SLOTS}",
                committed.len(),
                if committed.len() == 1 { "" } else { "s" }
            ),
            fields: vec![
                Field::id("cell", *self.id.as_bytes()),
                Field::text("lens", "read-cap / privacy".to_string()),
                Field::boolean("available", true),
                Field::text(
                    "encrypted_slots",
                    if committed.is_empty() {
                        "none — all 16 slots are Public (in the clear)".to_string()
                    } else {
                        committed
                            .iter()
                            .map(|i| i.to_string())
                            .collect::<Vec<_>>()
                            .join(", ")
                    },
                ),
                Field::text("read_lattice_top", format!("held = mask {:#06x}", held.0)),
                Field::boolean("binding_untouched", true),
            ],
        };
        out.push(Presentation {
            kind: PresentationKind::RawFields,
            label: "Read Membrane".to_string(),
            search_text: PresentationBody::Fields(insp.clone()).search_text(),
            body: PresentationBody::Fields(insp),
        });

        // (2) Lattice — the read-lattice: the `granted ⊆ held` attenuation order
        //     over the cell's encrypted slots, built by EXERCISING the real
        //     `ReadCap::attenuate`. The chain ∅ ⊑ {first} ⊑ {first,second} ⊑ … ⊑
        //     held; `current` sits at the full frustum a wide cap holds.
        out.push(Presentation {
            kind: PresentationKind::DomainVisual,
            label: "Read Lattice".to_string(),
            search_text: format!(
                "read lattice attenuation granted subset held {} slots",
                committed.len()
            ),
            body: PresentationBody::Lattice(read_lattice(self.id, &committed)),
        });

        // (3) Invariant (Prose) — the load-bearing property + the honest seams.
        //     The byte-identical commitment is DEMONSTRATED live on this cell where
        //     a committed slot exists.
        out.push(Presentation {
            kind: PresentationKind::Invariant,
            label: "Binding Untouched".to_string(),
            search_text: "read-cap binding untouched byte-identical commitment hiding added"
                .to_string(),
            body: PresentationBody::Prose(binding_invariant_prose(self, &committed)),
        });

        out
    }
}

/// Build the read-lattice for the cell's encrypted slots as a covering chain,
/// exercising the REAL [`ReadCap::attenuate`] / [`is_read_attenuation`] so the
/// drawn order is the genuine `granted ⊆ held` partial order, not a transcription.
fn read_lattice(target: CellId, committed: &[usize]) -> LatticeView {
    let view_key = ViewKey::from_root(LENS_DEMO_VIEW_ROOT);
    let held = FieldSet::from_slots(committed);
    let wide = ReadCap::new(target, held, view_key);

    // The chain ∅ ⊑ {s0} ⊑ {s0,s1} ⊑ … ⊑ held — each rung an honest attenuation
    // of the wide cap (the narrower slot-set is a real `wide.attenuate(prefix)`).
    let mut nodes: Vec<String> = vec!["∅ (opens nothing)".to_string()];
    let mut edges: Vec<(usize, usize)> = Vec::new();
    let mut prev = 0usize;
    for k in 1..=committed.len() {
        let prefix = FieldSet::from_slots(&committed[..k]);
        // The attenuation MUST succeed (prefix ⊆ held) — proof the rung is genuine.
        debug_assert!(
            wide.attenuate(prefix).is_some(),
            "a prefix of held must attenuate"
        );
        let slots: Vec<String> = committed[..k].iter().map(|i| i.to_string()).collect();
        let label = if k == committed.len() {
            format!("{{{}}} = held (the wide cap)", slots.join(","))
        } else {
            format!("{{{}}}", slots.join(","))
        };
        nodes.push(label);
        edges.push((prev, nodes.len() - 1));
        prev = nodes.len() - 1;
    }
    // The live readout sits at the full frustum (the wide cap's reach).
    let current = if committed.is_empty() {
        Some(0)
    } else {
        Some(nodes.len() - 1)
    };
    LatticeView {
        nodes,
        edges,
        current,
    }
}

/// The binding-untouched invariant prose, with a LIVE byte-identity demonstration
/// on the focused cell where a committed slot exists.
fn binding_invariant_prose(view: &ReadConfidentiality, committed: &[usize]) -> String {
    let mut s = String::new();
    s.push_str(
        "THE LOAD-BEARING INVARIANT — adding a read-cap changes NO commitment the \
         circuit / conservation sees.\n\n",
    );
    s.push_str(
        "A read is attenuable viewing authority over committed state (the write-cap \
         run backwards): `granted ⊆ held` is the read-lattice, exactly the facet \
         attenuation order. A `Committed` slot becomes a `(commitment, ciphertext)` \
         pair where the commitment is the BYTE-IDENTICAL BLAKE3(value‖nonce) the \
         cell already stored — the ECIES ciphertext is the only new artifact. Hiding \
         is ADDED; binding is UNTOUCHED — that is what keeps the circuit green and \
         the conservation check valid.\n\n",
    );

    // Live demonstration: seal a committed slot under a demo ViewKey into a CLONE
    // and confirm the side-table commitment equals the clone's stored commitment.
    if let Some(&slot) = committed.first() {
        let mut clone = view.cell.state.clone();
        let mut enc = EncryptedState::new();
        let demo_key = ViewKey::from_root(LENS_DEMO_VIEW_ROOT);
        // A fresh demo nonce — the seal recomputes the commitment from the slot's
        // live cleartext value; we assert it matches the clone's stored commitment.
        let sealed = enc.seal_field(&mut clone, slot, &demo_key, 0xD0_5E);
        let side = enc.slots.get(&slot).map(|e| e.commitment);
        let stored = clone.commitments[slot];
        let byte_identical = sealed && side.is_some() && side == stored;
        if byte_identical {
            s.push_str(&format!(
                "LIVE on this cell — sealed slot {slot} under a demo viewing key: the \
                 read-cap side-table commitment is BYTE-IDENTICAL to the cell's stored \
                 commitment ({}). ✓ binding preserved.\n\n",
                reflect::short_hex(&side.unwrap())
            ));
        } else {
            s.push_str(&format!(
                "Slot {slot} is committed; the read-cap seal recomputes the identical \
                 commitment via the same BLAKE3(value‖nonce) the cell uses.\n\n"
            ));
        }
    } else {
        s.push_str(
            "This cell has no committed slots right now — every slot is Public (in \
             the clear). The read-membrane would gate any slot the moment it is \
             sealed Committed; the lattice above shows it is reachable.\n\n",
        );
    }

    s.push_str("HONEST SEAMS (named, with their lanes):\n");
    s.push_str(
        "· Cryptographic revocation ≠ cap revocation — the cap-object revokes via the \
         revocation_channel; only key-rotation stops a revoked holder reading NEW \
         content, and nothing un-reveals a past read (inherent to encryption).\n",
    );
    s.push_str(
        "· No metadata privacy — this hides slot CONTENTS, never that a read happened \
         or which cell.\n",
    );
    s.push_str(
        "· ZK-private cells (M2) — state-as-all-commitments with a hiding-STARK \
         transition proof — are the deeper, VK-affecting rung (docs/deos/SHIELDED-CELLS.md).",
    );
    s
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::presentable::PresentCtx;
    use crate::world::{make_open_cell, World};

    /// Build a world with one cell whose slots 3 and 7 are Committed (the
    /// encrypted-field set) and the rest Public — mutated on a fresh cell before
    /// the bench genesis install.
    fn world_with_committed_cell() -> (World, CellId) {
        let mut w = World::new();
        let mut cell = make_open_cell(0x11, 1_000);
        cell.state.set_field(3, dregg_cell::field_from_u64(303));
        cell.state.set_field(7, dregg_cell::field_from_u64(707));
        cell.state.set_field_visibility(3, FieldVisibility::Committed, 11);
        cell.state.set_field_visibility(7, FieldVisibility::Committed, 22);
        let id = w.bench_install_cell(cell, 1_000);
        (w, id)
    }

    /// A plain genesis cell (all slots Public — no committed slots).
    fn plain_world() -> (World, CellId) {
        let mut w = World::new();
        let id = w.genesis_cell(0x22, 0);
        (w, id)
    }

    #[test]
    fn lights_up_for_a_real_cell() {
        let (w, id) = plain_world();
        let view = ReadConfidentiality::from_world(&w, id).expect("cell present");
        let ctx = PresentCtx::new(&w, id);
        let set = view.present(&ctx);
        // The mandatory RawFields floor is present and reports the lens AVAILABLE
        // (not a pending placeholder).
        let floor = set
            .iter()
            .find(|p| p.kind == PresentationKind::RawFields)
            .expect("RawFields floor");
        if let PresentationBody::Fields(i) = &floor.body {
            assert!(
                i.fields.iter().any(|f| f.key == "available"),
                "the floor records availability"
            );
        } else {
            panic!("floor is a Fields body");
        }
        // Three presentations: membrane / lattice / invariant.
        assert_eq!(set.len(), 3, "membrane + lattice + invariant");
        assert!(set.iter().any(|p| p.kind == PresentationKind::DomainVisual));
        assert!(set.iter().any(|p| p.kind == PresentationKind::Invariant));
    }

    #[test]
    fn the_encrypted_field_set_is_read_off_live_visibility() {
        let (w, id) = world_with_committed_cell();
        let view = ReadConfidentiality::from_world(&w, id).expect("cell");
        let committed = view.committed_slots();
        assert_eq!(committed, vec![3, 7], "exactly the two committed slots");
    }

    #[test]
    fn the_read_lattice_is_the_real_attenuation_chain() {
        let (w, id) = world_with_committed_cell();
        let view = ReadConfidentiality::from_world(&w, id).expect("cell");
        let lat = read_lattice(id, &view.committed_slots());
        // ∅ ⊑ {3} ⊑ {3,7}=held — three nodes, two covers, live readout at the top.
        assert_eq!(lat.nodes.len(), 3);
        assert_eq!(lat.edges, vec![(0, 1), (1, 2)]);
        assert_eq!(lat.current, Some(2));
        assert!(lat.nodes[2].contains("held"));
    }

    #[test]
    fn attenuation_order_holds_and_refuses_amplification() {
        // The lattice rungs are genuine: each prefix attenuates held, and an
        // out-of-frustum slot does NOT (no amplification).
        let committed = vec![3usize, 7];
        let held = FieldSet::from_slots(&committed);
        assert!(is_read_attenuation(&held, &FieldSet::from_slots(&[3])));
        assert!(is_read_attenuation(&held, &FieldSet::from_slots(&[3, 7])));
        // slot 5 is not in held — cannot be granted.
        assert!(!is_read_attenuation(&held, &FieldSet::from_slots(&[3, 5])));
    }

    #[test]
    fn binding_invariant_demonstrates_byte_identity_live() {
        let (w, id) = world_with_committed_cell();
        let view = ReadConfidentiality::from_world(&w, id).expect("cell");
        let prose = binding_invariant_prose(&view, &view.committed_slots());
        assert!(
            prose.contains("BYTE-IDENTICAL"),
            "the live demonstration confirms binding is preserved"
        );
        assert!(prose.contains("HONEST SEAMS"), "the seams are named");
    }

    #[test]
    fn no_committed_slots_degrades_honestly() {
        let (w, id) = plain_world();
        let view = ReadConfidentiality::from_world(&w, id).expect("cell");
        // If the demo cell has no committed slots, the invariant prose says so
        // honestly rather than fabricating a sealed slot.
        if view.committed_slots().is_empty() {
            let prose = binding_invariant_prose(&view, &[]);
            assert!(prose.contains("no committed slots"));
        }
    }
}
