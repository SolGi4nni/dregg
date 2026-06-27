//! L5 — THE CELL-STATE DEEP INSPECTOR.
//!
//! `presentable.rs`'s [`ReflectedCell`](crate::presentable::ReflectedCell) (L1)
//! gives a live ledger cell a five-presentation floor: the `reflect_cell`
//! RawFields, the `inspect_act` Affordances, the receipt-log Provenance, the
//! ocap Graph, and a *basic* lifecycle DomainVisual. This module goes DEEP on
//! the cell's authority-bearing state surface (census slice 5) WITHOUT
//! duplicating that floor: [`DeepCell`] is a separate `impl Presentable` that
//! reads the SAME live cell and emits the richer lenses the basic view omits —
//!
//!   * **Heap** as a [`MerkleTree`](crate::presentable::PresentationBody::MerkleTree)
//!     — the real sorted-Poseidon2 `(collection, key) → value` map leaves and the
//!     committed `heap_root` (`dregg_cell::state`'s `compute_heap_root` /
//!     `empty_heap_root`), with each leaf labeled so the verifier gadgets (L9)
//!     can open membership against the published root.
//!   * **Permissions** as a [`Lattice`](crate::presentable::PresentationBody::Lattice)
//!     — the eight per-action [`AuthRequired`] tiers read off the real
//!     `Permissions`, placed on the `None ⊑ {Signature,Proof} ⊑ Either ⊑ …`
//!     authority order, with a per-action read of where each gate sits.
//!   * **Lifecycle** as a [`StateMachine`](crate::presentable::PresentationBody::StateMachine)
//!     — the five canonical states (Live/Sealed/Destroyed/Migrated/Archived) +
//!     the verb transitions, with the live `current` read off the real
//!     `CellLifecycle` AND the variant's payload (sealed-at height, death
//!     certificate, migration target) surfaced as a detail line.
//!   * **fields[16]** richly as a DomainVisual field-tree — every one of the 16
//!     slots with its `FieldVisibility` tier and its commitment status (so a
//!     Committed/SelectivelyDisclosable slot reads as hidden-with-commitment),
//!     plus the kernel roots (`fields_root` / `system_roots` / `swiss`/`refcount`)
//!     and `committed_height`.
//!   * **mode / delegate / epoch** as a DomainVisual readout — the Hosted/Sovereign
//!     mode, the delegate edge + delegation snapshot staleness, the delegation
//!     epoch.
//!   * **Commitment** as an [`Invariant`](crate::presentable::PresentationKind::Invariant)
//!     readout — what the canonical 8-felt state commitment
//!     (`dregg_cell::compute_canonical_state_commitment`) BINDS: the full
//!     authority residue (identity · mode · the 8 permission gates · VK · the
//!     delegate/delegation snapshot · program · the field/visibility/commitment
//!     arrays · the side-table + heap + cap roots · lifecycle), with the live
//!     32-byte canonical commitment shown.
//!
//! Everything is pure data, projected from the live `World` (the `reflect.rs`
//! invariant — never a parallel schema), proven by `cargo test` exactly as
//! `presentable.rs`'s tests are. The thin gpui layer renders these via the
//! SAME [`PresentationBody`] variants L1 already defines — this module adds NO
//! new render kind.
//!
//! ## Relation to `ReflectedCell`
//!
//! This is a COMPANION, not a replacement. `ReflectedCell` answers "what messages
//! does this cell understand and who points at whom?"; `DeepCell` answers "what
//! exactly is this cell's authority-bearing state, and what does its published
//! commitment bind?". The two share the RawFields floor (both emit the genuine
//! `reflect_cell` projection, satisfying the universal-coverage invariant) and
//! the lifecycle DomainVisual; `DeepCell`'s lifecycle SUPERSEDES the basic one by
//! also surfacing the live variant's payload. A registry would offer both
//! presentation sets for a `FocusTarget::Cell` (the cockpit merges them into one
//! tab strip); wiring `DeepCell` into `FocusTarget`/`Registry` is a one-arm L1
//! edit deferred per the touch-only-`cell_inspector.rs` rule (see the report).

use dregg_cell::state::{
    compute_heap_root, empty_heap_root, FieldVisibility, PublicFieldView, STATE_SLOTS,
};
use dregg_cell::{
    compute_canonical_state_commitment, AuthRequired, Cell, CellId, CellLifecycle, CellMode,
    Permissions,
};

use crate::presentable::{
    LatticeView, MerkleTreeView, PresentCtx, Presentable, Presentation, PresentationBody,
    PresentationKind, SmState, SmTransition, StateMachineView,
};
use crate::reflect::{self, Field, FieldValue, Inspectable, ObjectKind};
use crate::world::World;

// ===========================================================================
// DeepCell — the deep-inspection Presentable companion to ReflectedCell.
// ===========================================================================

/// A thin newtype wrapping a live ledger cell as a deep-inspection
/// [`Presentable`] — the established "reflect a foreign struct into a starbridge
/// view" pattern (`reflect.rs`'s `reflect_cell`, `presentable.rs`'s
/// `ReflectedCell`). The cell lives in the foreign `dregg_cell` crate, so we
/// register via this wrapper rather than `impl Presentable for Cell` directly.
#[derive(Clone, Debug)]
pub struct DeepCell {
    /// The cell's id (the navigable focus).
    pub id: CellId,
    /// A snapshot of the cell, cloned off the live ledger at build time. The
    /// presentations read it; the snapshot moves whenever a real turn mutates
    /// the live cell, so re-building from the world re-reads the live state.
    pub cell: Cell,
}

impl DeepCell {
    /// Wrap the live cell `id` if it is present in the world's ledger.
    pub fn from_world(world: &World, id: CellId) -> Option<Self> {
        world.ledger().get(&id).map(|c| DeepCell {
            id,
            cell: c.clone(),
        })
    }
}

impl Presentable for DeepCell {
    fn object_kind(&self) -> ObjectKind {
        ObjectKind::Cell
    }

    fn present(&self, _ctx: &PresentCtx) -> Vec<Presentation> {
        let mut out: Vec<Presentation> = Vec::new();

        // (1) RawFields — the MANDATORY floor (the universal-coverage invariant).
        //     The genuine reflect_cell projection, shared verbatim with the L1
        //     ReflectedCell so both companions satisfy the floor identically.
        let insp = reflect::reflect_cell(&self.id, &self.cell);
        out.push(Presentation {
            kind: PresentationKind::RawFields,
            label: "Cell State".to_string(),
            search_text: PresentationBody::Fields(insp.clone()).search_text(),
            body: PresentationBody::Fields(insp),
        });

        // (2) MerkleTree — the cell's HEAP: the real sorted-Poseidon2 leaves +
        //     the committed heap_root, off the live heap_map.
        let heap = heap_merkle_tree(&self.cell);
        out.push(Presentation {
            kind: PresentationKind::Graph,
            label: "Heap".to_string(),
            search_text: format!(
                "heap {} entr{} root {}",
                heap.leaves.len(),
                if heap.leaves.len() == 1 { "y" } else { "ies" },
                heap.label
            ),
            body: PresentationBody::MerkleTree(heap),
        });

        // (3) Lattice — the eight per-action PERMISSION tiers on the authority
        //     order, read off the real Permissions.
        let lat = permissions_lattice(&self.cell.permissions);
        out.push(Presentation {
            kind: PresentationKind::DomainVisual,
            label: "Permissions".to_string(),
            search_text: format!("permissions lattice {}", lat.nodes.join(" ")),
            body: PresentationBody::Lattice(lat),
        });

        // (4) StateMachine — the LIFECYCLE, superseding the L1 basic view by
        //     surfacing the live variant's payload as a detail.
        let sm = lifecycle_state_machine(&self.cell.lifecycle);
        out.push(Presentation {
            kind: PresentationKind::DomainVisual,
            label: "Lifecycle".to_string(),
            search_text: format!(
                "lifecycle {} {}",
                sm.current,
                lifecycle_detail(&self.cell.lifecycle)
            ),
            body: PresentationBody::StateMachine(sm),
        });

        // (5) DomainVisual (Fields body) — the 16 fields richly (each with its
        //     visibility tier + commitment status), the kernel roots, and the
        //     mode/delegate/epoch readout.
        let cart = field_cartography(&self.id, &self.cell);
        out.push(Presentation {
            kind: PresentationKind::DomainVisual,
            label: "Field Cartography".to_string(),
            search_text: PresentationBody::Fields(cart.clone()).search_text(),
            body: PresentationBody::Fields(cart),
        });

        // (6) Invariant (Prose) — what the canonical 8-felt state commitment
        //     binds, with the live commitment value.
        let prose = commitment_invariant(&self.cell);
        out.push(Presentation {
            kind: PresentationKind::Invariant,
            label: "State Commitment".to_string(),
            search_text: format!(
                "commitment authority binding {}",
                reflect::short_hex(&compute_canonical_state_commitment(&self.cell))
            ),
            body: PresentationBody::Prose(prose),
        });

        out
    }
}

// ===========================================================================
// Heap → MerkleTree (the real sorted-Poseidon2 heap map + root).
// ===========================================================================

/// Build the cell's HEAP as a [`MerkleTreeView`]: the live `heap_map` entries as
/// leaves (each `(collection, key) → value`) and the committed `heap_root` the
/// tree commits to. A no-heap-activity cell carries the fixed
/// [`empty_heap_root`] constant. The leaves are read in canonical
/// (`BTreeMap`-sorted) order so the view matches the sorted-Poseidon2 leaf order
/// `compute_heap_root` folds. The verifier gadgets (L9) recompute the root over
/// these leaves against the machinery.
fn heap_merkle_tree(cell: &Cell) -> MerkleTreeView {
    let st = &cell.state;
    let leaves: Vec<String> = st
        .heap_map
        .iter()
        .map(|((coll, key), value)| {
            format!("coll {coll} · key {key} → {}", reflect::short_hex(value))
        })
        .collect();
    // The committed root: the real `heap_root` register. We re-fold the live map
    // (the genuine `compute_heap_root`) and surface BOTH the committed root and a
    // consistency note if they ever diverge (a stale root the inspector reveals
    // honestly rather than papering over).
    let committed = st.heap_root;
    let recomputed = compute_heap_root(&st.heap_map);
    let label = if leaves.is_empty() {
        format!(
            "empty heap (root {})",
            reflect::short_hex(&empty_heap_root())
        )
    } else if committed == recomputed {
        format!("heap root {}", reflect::short_hex(&committed))
    } else {
        format!(
            "heap root {} (STALE — map folds to {})",
            reflect::short_hex(&committed),
            reflect::short_hex(&recomputed)
        )
    };
    MerkleTreeView {
        label,
        leaves,
        root: committed,
        // No specific membership path highlighted; a heap-entry gadget (L5 gadget
        // lane) would set this to a leaf→root opening.
        path: Vec::new(),
    }
}

// ===========================================================================
// Permissions → Lattice (the eight per-action AuthRequired tiers).
// ===========================================================================

/// The authority-order rank of an [`AuthRequired`] tier on the
/// `None ⊑ {Signature, Proof} ⊑ Either ⊑ Impossible` order (with `Custom` placed
/// beside the signature/proof rung as an app-defined gate). Lower = weaker
/// (more permissive); higher = stronger (more restrictive). Mirrors
/// `AuthRequired::is_narrower_or_equal` (Impossible most restrictive, None
/// least).
fn auth_rank(auth: &AuthRequired) -> usize {
    match auth {
        AuthRequired::None => 0,
        AuthRequired::Either => 1,
        AuthRequired::Signature | AuthRequired::Proof | AuthRequired::Custom { .. } => 2,
        AuthRequired::Impossible => 3,
    }
}

/// A short legible name for an [`AuthRequired`] tier.
fn auth_name(auth: &AuthRequired) -> String {
    match auth {
        AuthRequired::None => "None".to_string(),
        AuthRequired::Signature => "Signature".to_string(),
        AuthRequired::Proof => "Proof".to_string(),
        AuthRequired::Either => "Either".to_string(),
        AuthRequired::Impossible => "Impossible".to_string(),
        AuthRequired::Custom { vk_hash } => {
            format!("Custom({})", reflect::short_hex(vk_hash))
        }
    }
}

/// The eight cell actions, in canonical order, paired with the `Permissions`
/// field each gates. Mirrors the `hash_permissions_into` canonical order so the
/// Lattice rows line up with what the commitment binds.
fn permission_actions(perms: &Permissions) -> [(&'static str, &AuthRequired); 8] {
    [
        ("send", &perms.send),
        ("receive", &perms.receive),
        ("set_state", &perms.set_state),
        ("set_permissions", &perms.set_permissions),
        ("set_verification_key", &perms.set_verification_key),
        ("increment_nonce", &perms.increment_nonce),
        ("delegate", &perms.delegate),
        ("access", &perms.access),
    ]
}

/// Build the cell's PERMISSIONS as a [`LatticeView`]: the authority order
/// (`None ⊑ Either ⊑ {Signature,Proof,Custom} ⊑ Impossible`) as the lattice
/// spine, and each of the eight actions placed at the tier it requires. The
/// `nodes` are the four order rungs; each action's required tier reads off the
/// real `Permissions`. `current` marks the *strongest* gate on the cell (the
/// most restrictive action), since a lattice has one live readout — the per-
/// action detail is carried in the node labels.
fn permissions_lattice(perms: &Permissions) -> LatticeView {
    // The four authority rungs (weakest first), each annotated with which
    // actions sit at it (read off the live Permissions).
    let rung_names = ["None", "Either", "Signature/Proof/Custom", "Impossible"];
    let actions = permission_actions(perms);

    let mut nodes: Vec<String> = Vec::with_capacity(rung_names.len());
    for (rank, rname) in rung_names.iter().enumerate() {
        let at_rung: Vec<String> = actions
            .iter()
            .filter(|(_, auth)| auth_rank(auth) == rank)
            .map(|(name, auth)| format!("{name}={}", auth_name(auth)))
            .collect();
        if at_rung.is_empty() {
            nodes.push((*rname).to_string());
        } else {
            nodes.push(format!("{rname}: {}", at_rung.join(", ")));
        }
    }

    // The covering relations: each rung covers the one below it.
    let edges: Vec<(usize, usize)> = (0..rung_names.len() - 1).map(|i| (i, i + 1)).collect();

    // The live readout: the cell's STRONGEST gate (the most restrictive action's
    // tier) — what authority the cell demands at its tightest point.
    let current = actions.iter().map(|(_, auth)| auth_rank(auth)).max();

    LatticeView {
        nodes,
        edges,
        current,
    }
}

// ===========================================================================
// Lifecycle → StateMachine (richer than L1: the live variant's payload).
// ===========================================================================

/// The five canonical lifecycle states + the verb transitions, with the live
/// `current` read off the real `CellLifecycle`. The same canonical shape the L1
/// `ReflectedCell` lifecycle view carries; `DeepCell` SUPERSEDES it by also
/// folding the live variant's payload (sealed-at height, death certificate,
/// migration target) into the `current` readout via [`lifecycle_detail`].
fn lifecycle_state_machine(lc: &CellLifecycle) -> StateMachineView {
    let states = vec![
        SmState {
            name: "Live".to_string(),
            terminal: false,
        },
        SmState {
            name: "Sealed".to_string(),
            terminal: false,
        },
        SmState {
            name: "Destroyed".to_string(),
            terminal: true,
        },
        SmState {
            name: "Migrated".to_string(),
            terminal: true,
        },
        SmState {
            name: "Archived".to_string(),
            terminal: false,
        },
    ];
    let transitions = vec![
        SmTransition {
            from: "Live".to_string(),
            to: "Sealed".to_string(),
            verb: "Seal".to_string(),
        },
        SmTransition {
            from: "Sealed".to_string(),
            to: "Live".to_string(),
            verb: "Unseal".to_string(),
        },
        SmTransition {
            from: "Live".to_string(),
            to: "Destroyed".to_string(),
            verb: "Destroy".to_string(),
        },
        SmTransition {
            from: "Live".to_string(),
            to: "Migrated".to_string(),
            verb: "Migrate".to_string(),
        },
        SmTransition {
            from: "Live".to_string(),
            to: "Archived".to_string(),
            verb: "Archive".to_string(),
        },
    ];
    // The current state's NAME plus its payload detail — the deep view's lift
    // over the basic L1 lifecycle (which carries only the bare state name).
    let current = format!("{} {}", lifecycle_name(lc), lifecycle_detail(lc));
    StateMachineView {
        states,
        transitions,
        current: current.trim().to_string(),
    }
}

/// The bare canonical name of a lifecycle state (matches the SM state names).
fn lifecycle_name(lc: &CellLifecycle) -> &'static str {
    match lc {
        CellLifecycle::Live => "Live",
        CellLifecycle::Sealed { .. } => "Sealed",
        CellLifecycle::Destroyed { .. } => "Destroyed",
        CellLifecycle::Migrated { .. } => "Migrated",
        CellLifecycle::Archived { .. } => "Archived",
    }
}

/// The live variant's payload, surfaced as a detail line (empty for `Live`).
/// This is the deep-inspector lift over the basic lifecycle view: a Sealed cell
/// reads its seal height + reason commitment, a Destroyed cell its death
/// certificate + height, a Migrated cell its destination, an Archived cell its
/// checkpoint + archived-through height.
fn lifecycle_detail(lc: &CellLifecycle) -> String {
    match lc {
        CellLifecycle::Live => String::new(),
        CellLifecycle::Sealed {
            reason_hash,
            sealed_at,
        } => {
            format!(
                "· sealed at h{sealed_at} · reason {}",
                reflect::short_hex(reason_hash)
            )
        }
        CellLifecycle::Destroyed {
            death_certificate_hash,
            destroyed_at,
        } => {
            format!(
                "· destroyed at h{destroyed_at} · cert {}",
                reflect::short_hex(death_certificate_hash)
            )
        }
        CellLifecycle::Migrated {
            to,
            attestation,
            migrated_at,
        } => {
            format!(
                "· migrated at h{migrated_at} → {} · attest {}",
                reflect::short_hex(to.as_bytes()),
                reflect::short_hex(attestation)
            )
        }
        CellLifecycle::Archived {
            checkpoint_hash,
            archived_through,
        } => {
            format!(
                "· archived through h{archived_through} · checkpoint {}",
                reflect::short_hex(checkpoint_hash)
            )
        }
    }
}

// ===========================================================================
// fields[16] + roots + mode/delegate/epoch → DomainVisual field-tree.
// ===========================================================================

/// The Hosted/Sovereign mode as a legible string.
fn mode_name(mode: &CellMode) -> &'static str {
    match mode {
        CellMode::Hosted => "Hosted (federation stores full state)",
        CellMode::Sovereign => "Sovereign (federation stores only the commitment)",
    }
}

/// Build the deep FIELD CARTOGRAPHY as an [`Inspectable`] (rendered with the
/// existing RawFields field-tree widget — no new render kind). It surfaces what
/// the basic `reflect_cell` omits or compresses:
///
///   * every one of the 16 `fields[i]` slots WITH its `FieldVisibility` tier and
///     its commitment status (a Committed slot reads as hidden-with-commitment
///     via the real `get_field_public`), including the zero slots (the basic
///     view hides those for legibility);
///   * the kernel roots — `heap_root`, `fields_root`, the `system_roots` digest,
///     `swiss_table_root`, `refcount_table_root` — that fold the cell's whole
///     record + side-table state into the commitment;
///   * `committed_height` (the chain height the commitment is bound to), the
///     `proved_state` flag, the `delegation_epoch`, the `mode`, the `delegate`
///     edge, and the `delegation` snapshot staleness.
fn field_cartography(id: &CellId, cell: &Cell) -> Inspectable {
    let st = &cell.state;
    // ---- mode / identity-adjacent ----
    let mut fields: Vec<Field> = vec![
        Field::text("mode", mode_name(&cell.mode)),
        Field::boolean("proved_state", st.proved_state()),
        Field::count("committed_height", st.committed_height()),
        Field::count("delegation_epoch", st.delegation_epoch()),
    ];

    // ---- delegate edge + delegation snapshot staleness ----
    match &cell.delegate {
        Some(d) => fields.push(Field::id("delegate", *d.as_bytes())),
        None => fields.push(Field::text("delegate", "none")),
    }
    match &cell.delegation {
        Some(deleg) => {
            fields.push(Field::id("delegation.source", *deleg.source.as_bytes()));
            fields.push(Field::text(
                "delegation.snapshot",
                format!(
                    "{} cap(s) · epoch {} · refreshed h{} · max_staleness {}",
                    deleg.snapshot.len(),
                    deleg.delegation_epoch,
                    deleg.refreshed_at,
                    deleg.max_staleness,
                ),
            ));
        }
        None => fields.push(Field::text("delegation", "none")),
    }

    // ---- the kernel roots that fold the whole record into the commitment ----
    fields.push(Field::hash("heap_root", st.heap_root));
    fields.push(Field::hash("fields_root", st.fields_root));
    fields.push(Field::hash("system_roots_digest", st.system_roots_digest()));
    fields.push(Field::hash("swiss_table_root", st.swiss_table_root));
    fields.push(Field::hash("refcount_table_root", st.refcount_table_root));
    fields.push(Field::count(
        "fields_map_entries",
        st.fields_map.len() as u64,
    ));
    fields.push(Field::count("heap_map_entries", st.heap_map.len() as u64));

    // ---- every one of the 16 fixed slots with its visibility + commitment ----
    for i in 0..STATE_SLOTS {
        let vis = st.field_visibility[i];
        let vis_name = match vis {
            FieldVisibility::Public => "public",
            FieldVisibility::Committed => "committed",
            FieldVisibility::SelectivelyDisclosable => "selectively-disclosable",
        };
        let detail = match st.get_field_public(i) {
            // Public: show the raw slot bytes (or "zero" when empty).
            Some(PublicFieldView::Revealed(v)) => {
                if v.iter().all(|b| *b == 0) {
                    format!("[{vis_name}] zero")
                } else {
                    format!("[{vis_name}] {}", reflect::short_hex(&v))
                }
            }
            // Hidden behind a commitment: show the commitment hash, not the value.
            Some(PublicFieldView::Committed(h)) => {
                if h == [0u8; 32] {
                    format!("[{vis_name}] hidden (commitment stale — re-commit needed)")
                } else {
                    format!(
                        "[{vis_name}] hidden · commitment {}",
                        reflect::short_hex(&h)
                    )
                }
            }
            None => format!("[{vis_name}] (out of range)"),
        };
        fields.push(Field {
            key: format!("field[{i}]"),
            value: FieldValue::Text(detail),
        });
    }

    Inspectable {
        kind: ObjectKind::Cell,
        title: format!(
            "Field Cartography · Cell {}",
            reflect::short_hex(id.as_bytes())
        ),
        subtitle: format!(
            "16 slots · {} ext-field(s) · {} heap entr{} · {} mode",
            st.fields_map.len(),
            st.heap_map.len(),
            if st.heap_map.len() == 1 { "y" } else { "ies" },
            match cell.mode {
                CellMode::Hosted => "hosted",
                CellMode::Sovereign => "sovereign",
            },
        ),
        fields,
    }
}

// ===========================================================================
// Commitment → Invariant (what the canonical 8-felt commitment binds).
// ===========================================================================

/// Build the COMMITMENT INVARIANT prose: what the canonical state commitment
/// (`dregg_cell::compute_canonical_state_commitment`) BINDS, with the live
/// 32-byte commitment value. The text names the full authority residue the
/// commitment folds (the single source of truth for "what bytes commit to this
/// cell"), so an operator reading it understands that two cells with identical
/// balance/nonce/fields but different permissions or VK commit DIFFERENTLY — the
/// anti-omission tooth the whole canonical scheme exists to provide.
fn commitment_invariant(cell: &Cell) -> String {
    let commit = compute_canonical_state_commitment(cell);
    let st = &cell.state;
    let perms = permission_actions(&cell.permissions)
        .iter()
        .map(|(name, auth)| format!("{name}={}", auth_name(auth)))
        .collect::<Vec<_>>()
        .join(", ");
    let vk = match &cell.verification_key {
        Some(v) => format!("present (hash {})", reflect::short_hex(&v.hash)),
        None => "none".to_string(),
    };
    format!(
        "Canonical state commitment (8-felt / ~124-bit, dregg-cell:canonical-state-commitment):\n  \
         {}\n\n\
         This commitment BINDS the cell's full authority-bearing state — the single source of \
         truth for \"what bytes commit to this cell.\" Two cells with identical \
         balance/nonce/fields but different permissions, VK, lifecycle, or roots commit \
         DIFFERENTLY (the anti-omission tooth). It folds:\n\
         • identity: id · public_key · token_id\n\
         • mode: {}\n\
         • core state: nonce {} · balance {} · proved_state {} · delegation_epoch {} · committed_height {}\n\
         • the 16 fields + their visibility tiers + per-field commitments\n\
         • the 8 permission gates: {}\n\
         • verification_key: {}\n\
         • capability_root (sorted-Poseidon2, tombstone-deletion): {}\n\
         • delegate {} · delegation snapshot\n\
         • program · lifecycle ({})\n\
         • the record/side-table roots: heap_root {} · fields_root {} · system_roots {} · swiss {} · refcount {}",
        reflect::short_hex(&commit),
        mode_name(&cell.mode),
        st.nonce(),
        st.balance(),
        st.proved_state(),
        st.delegation_epoch(),
        st.committed_height(),
        perms,
        vk,
        reflect::short_hex(&dregg_cell::compute_canonical_capability_root(
            &cell.capabilities
        )),
        match &cell.delegate {
            Some(d) => reflect::short_hex(d.as_bytes()),
            None => "none".to_string(),
        },
        lifecycle_name(&cell.lifecycle),
        reflect::short_hex(&st.heap_root),
        reflect::short_hex(&st.fields_root),
        reflect::short_hex(&st.system_roots_digest()),
        reflect::short_hex(&st.swiss_table_root),
        reflect::short_hex(&st.refcount_table_root),
    )
}

// ===========================================================================
// TESTS — the model, proven gpui-free (exactly as presentable.rs's tests are).
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::world::{seal, set_field, transfer, unseal, World};

    /// A two-cell world: a treasury (1_000) and a sink (0), no turns yet.
    fn two_cell_world() -> (World, CellId, CellId) {
        let mut w = World::new();
        let treasury = w.genesis_cell(0x11, 1_000);
        let sink = w.genesis_cell(0x22, 0);
        (w, treasury, sink)
    }

    // ── the universal-coverage floor ────────────────────────────────────────

    #[test]
    fn deep_cell_yields_the_raw_fields_floor() {
        // DeepCell, like ReflectedCell, MUST emit the mandatory RawFields floor.
        let (w, treasury, _sink) = two_cell_world();
        let deep = DeepCell::from_world(&w, treasury).expect("the cell exists");
        let ctx = PresentCtx::new(&w, treasury);
        let set = deep.present(&ctx);
        let raw = set
            .iter()
            .find(|p| p.kind == PresentationKind::RawFields)
            .expect("the floor is present");
        match &raw.body {
            PresentationBody::Fields(i) => {
                assert!(i.fields.iter().any(|f| f.key == "balance"));
            }
            other => panic!("RawFields must carry a Fields body, got {other:?}"),
        }
    }

    #[test]
    fn deep_cell_offers_the_deep_presentation_set() {
        // The proof-of-shape: heap (MerkleTree), permissions (Lattice), lifecycle
        // (StateMachine), field cartography (Fields), commitment (Prose).
        let (w, treasury, _sink) = two_cell_world();
        let deep = DeepCell::from_world(&w, treasury).unwrap();
        let ctx = PresentCtx::new(&w, treasury);
        let set = deep.present(&ctx);

        assert!(
            set.iter()
                .any(|p| matches!(p.body, PresentationBody::MerkleTree(_))),
            "heap MerkleTree"
        );
        assert!(
            set.iter()
                .any(|p| matches!(p.body, PresentationBody::Lattice(_))),
            "permissions Lattice"
        );
        assert!(
            set.iter()
                .any(|p| matches!(p.body, PresentationBody::StateMachine(_))),
            "lifecycle SM"
        );
        assert!(
            set.iter().any(|p| p.label == "Field Cartography"),
            "field cartography"
        );
        assert!(
            set.iter().any(|p| p.kind == PresentationKind::Invariant),
            "commitment invariant"
        );
    }

    // ── the heap MerkleTree reflects real heap_map entries + root ────────────

    #[test]
    fn heap_merkle_tree_reflects_the_real_heap_map_and_root() {
        // A fresh cell carries the empty heap; a cell with real heap entries
        // (off the live CellState's genuine set_heap → compute_heap_root path)
        // reflects them as MerkleTree leaves + a moved root.
        let mut w = World::new();
        let empty_id = w.genesis_cell(0x33, 0);

        // Empty heap: no leaves, the fixed empty-heap root.
        {
            let deep = DeepCell::from_world(&w, empty_id).unwrap();
            let mt = match &deep
                .present(&PresentCtx::new(&w, empty_id))
                .into_iter()
                .find(|p| matches!(p.body, PresentationBody::MerkleTree(_)))
                .unwrap()
                .body
            {
                PresentationBody::MerkleTree(m) => m.clone(),
                _ => unreachable!(),
            };
            assert!(mt.leaves.is_empty(), "a fresh cell has an empty heap");
            assert_eq!(mt.root, empty_heap_root(), "the empty-heap root");
        }

        // Build a cell with two REAL heap entries (the genuine set_heap →
        // compute_heap_root path on the live CellState), then genesis-install it
        // so the live ledger carries the populated heap.
        let mut cell = crate::world::make_open_cell(0x66, 0);
        let fe = |b: u8| {
            let mut f = [0u8; 32];
            f[31] = b;
            f
        };
        assert!(cell.state.set_heap(1, 2, fe(42)));
        assert!(cell.state.set_heap(1, 3, fe(7)));
        let id = w.genesis_install(cell);

        let deep = DeepCell::from_world(&w, id).unwrap();
        let mt = match &deep
            .present(&PresentCtx::new(&w, id))
            .into_iter()
            .find(|p| matches!(p.body, PresentationBody::MerkleTree(_)))
            .unwrap()
            .body
        {
            PresentationBody::MerkleTree(m) => m.clone(),
            _ => unreachable!(),
        };
        assert_eq!(mt.leaves.len(), 2, "two heap entries appear as leaves");
        assert!(mt.leaves.iter().any(|l| l.contains("coll 1 · key 2")));
        assert_ne!(
            mt.root,
            empty_heap_root(),
            "a populated heap moves the root"
        );
        // The view's root is exactly the live committed heap_root, and re-folding
        // the live map agrees (no STALE annotation).
        let live_root = w.ledger().get(&id).unwrap().state.heap_root;
        assert_eq!(mt.root, live_root);
        assert!(!mt.label.contains("STALE"));
    }

    // ── permissions Lattice reads the real Permissions ──────────────────────

    #[test]
    fn permissions_lattice_reads_the_real_permissions() {
        // A frozen cell: every gate is Impossible (the strongest rung).
        let lat = permissions_lattice(&Permissions::frozen());
        assert_eq!(
            lat.current,
            Some(3),
            "frozen cells sit at the Impossible rung"
        );
        // The eight actions land on the Impossible node.
        let impossible = &lat.nodes[3];
        assert!(impossible.contains("send=Impossible"));
        assert!(impossible.contains("access=Impossible"));

        // A default-user cell: receive/access are None (weakest), the rest
        // Signature. The current (strongest) is the Signature/Proof/Custom rung.
        let lat = permissions_lattice(&Permissions::default_user());
        assert_eq!(
            lat.current,
            Some(2),
            "the strongest default-user gate is Signature"
        );
        assert!(
            lat.nodes[0].contains("receive=None"),
            "receive is None on the weakest rung"
        );
        assert!(lat.nodes[2].contains("send=Signature"));
        // The covering relations chain the four rungs.
        assert_eq!(lat.edges, vec![(0, 1), (1, 2), (2, 3)]);
    }

    // ── lifecycle StateMachine reads the real CellLifecycle ─────────────────

    #[test]
    fn lifecycle_state_machine_reads_the_real_lifecycle() {
        let (w, treasury, _sink) = two_cell_world();
        let deep = DeepCell::from_world(&w, treasury).unwrap();
        let ctx = PresentCtx::new(&w, treasury);
        let sm = match &deep
            .present(&ctx)
            .into_iter()
            .find(|p| matches!(p.body, PresentationBody::StateMachine(_)))
            .unwrap()
            .body
        {
            PresentationBody::StateMachine(s) => s.clone(),
            _ => unreachable!(),
        };
        assert_eq!(sm.current, "Live", "a fresh cell is Live (no payload)");
        assert!(sm
            .states
            .iter()
            .any(|s| s.name == "Destroyed" && s.terminal));
        assert!(sm.transitions.iter().any(|t| t.verb == "Seal"));
    }

    #[test]
    fn lifecycle_detail_surfaces_the_sealed_payload() {
        // The deep view's lift over the basic L1 lifecycle: a Sealed cell reads
        // its seal height + reason in the current readout.
        let sm = lifecycle_state_machine(&CellLifecycle::Sealed {
            reason_hash: [0xAB; 32],
            sealed_at: 99,
        });
        assert!(sm.current.starts_with("Sealed"));
        assert!(
            sm.current.contains("sealed at h99"),
            "the seal height is surfaced"
        );
    }

    // ── every presentation reflects the LIVE ledger (after a real turn) ──────

    #[test]
    fn the_deep_view_reflects_the_live_ledger_after_real_turns() {
        // A committed transfer moves the balance (RawFields + commitment); a
        // committed set_field moves a field slot (cartography + commitment); a
        // committed seal moves the lifecycle (StateMachine).
        let (mut w, treasury, sink) = two_cell_world();

        // Commitment BEFORE any turn.
        let commit_before = {
            let c = w.ledger().get(&treasury).unwrap();
            compute_canonical_state_commitment(c)
        };

        // (a) a real transfer.
        let t = w.turn(treasury, vec![transfer(treasury, sink, 250)]);
        assert!(w.commit_turn(t).is_committed());

        // (b) a real set_field on the treasury (slot 5).
        let t = w.turn(treasury, vec![set_field(treasury, 5, [9u8; 32])]);
        assert!(w.commit_turn(t).is_committed());

        // (c) a real seal of the sink — authorized by the sink itself (an agent
        //     drives lifecycle transitions on its OWN cell).
        let t = w.turn(sink, vec![seal(sink, "maintenance")]);
        assert!(w.commit_turn(t).is_committed());

        // The deep treasury view reflects the post-turn state.
        let deep = DeepCell::from_world(&w, treasury).unwrap();
        let ctx = PresentCtx::new(&w, treasury);
        let set = deep.present(&ctx);

        // RawFields balance moved to 750.
        let raw = set
            .iter()
            .find(|p| p.kind == PresentationKind::RawFields)
            .unwrap();
        match &raw.body {
            PresentationBody::Fields(i) => assert!(
                i.fields
                    .iter()
                    .any(|f| matches!(f.value, FieldValue::Balance(750))),
                "RawFields balance reflects the committed transfer"
            ),
            _ => unreachable!(),
        }

        // The field cartography shows the written slot[5].
        let cart = set.iter().find(|p| p.label == "Field Cartography").unwrap();
        match &cart.body {
            PresentationBody::Fields(i) => {
                let f5 = i
                    .fields
                    .iter()
                    .find(|f| f.key == "field[5]")
                    .expect("slot 5 surfaced");
                match &f5.value {
                    FieldValue::Text(t) => assert!(
                        t.contains("public") && !t.contains("zero"),
                        "slot 5 is now a non-zero public value: {t}"
                    ),
                    _ => unreachable!(),
                }
            }
            _ => unreachable!(),
        }

        // The commitment moved (the transfer + set_field both bind into it).
        let commit_after = compute_canonical_state_commitment(w.ledger().get(&treasury).unwrap());
        assert_ne!(
            commit_before, commit_after,
            "real turns move the canonical commitment"
        );

        // The SINK's deep view reflects its committed seal (the lifecycle SM).
        let sink_deep = DeepCell::from_world(&w, sink).unwrap();
        let sink_set = sink_deep.present(&PresentCtx::new(&w, sink));
        let sm = sink_set
            .iter()
            .find(|p| matches!(p.body, PresentationBody::StateMachine(_)))
            .unwrap();
        match &sm.body {
            PresentationBody::StateMachine(s) => {
                assert!(
                    s.current.starts_with("Sealed"),
                    "the sink committed a real seal: {}",
                    s.current
                );
                assert!(
                    s.current.contains("sealed at"),
                    "the seal payload is surfaced"
                );
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn unseal_returns_the_lifecycle_to_live() {
        // A seal then unseal round-trips the live lifecycle readout.
        let mut w = World::new();
        let id = w.genesis_cell(0x44, 100);
        assert!(w
            .commit_turn(w.turn(id, vec![seal(id, "pause")]))
            .is_committed());
        assert!(w.commit_turn(w.turn(id, vec![unseal(id)])).is_committed());

        let deep = DeepCell::from_world(&w, id).unwrap();
        let set = deep.present(&PresentCtx::new(&w, id));
        let sm = set
            .iter()
            .find(|p| matches!(p.body, PresentationBody::StateMachine(_)))
            .unwrap();
        match &sm.body {
            PresentationBody::StateMachine(s) => {
                assert_eq!(s.current, "Live", "unseal returns to Live")
            }
            _ => unreachable!(),
        }
    }

    // ── the commitment invariant names the authority binding ────────────────

    #[test]
    fn the_commitment_invariant_names_the_authority_residue() {
        let (w, treasury, _sink) = two_cell_world();
        let deep = DeepCell::from_world(&w, treasury).unwrap();
        let set = deep.present(&PresentCtx::new(&w, treasury));
        let inv = set
            .iter()
            .find(|p| p.kind == PresentationKind::Invariant)
            .unwrap();
        match &inv.body {
            PresentationBody::Prose(p) => {
                assert!(p.contains("the 8 permission gates"));
                assert!(p.contains("verification_key"));
                assert!(p.contains("capability_root"));
                assert!(p.contains("anti-omission"));
            }
            other => panic!("the commitment invariant should be Prose, got {other:?}"),
        }
    }

    #[test]
    fn distinct_permissions_yield_distinct_commitments() {
        // The anti-omission property the invariant prose names: two cells with
        // the SAME balance/nonce/fields but DIFFERENT permissions commit
        // differently (the commitment binds permissions).
        let mut a = crate::world::make_open_cell(0x55, 500);
        let mut b = a.clone();
        a.permissions = Permissions::default_user();
        b.permissions = Permissions::frozen();
        assert_ne!(
            compute_canonical_state_commitment(&a),
            compute_canonical_state_commitment(&b),
            "the commitment binds permissions (anti-omission)"
        );
    }
}
