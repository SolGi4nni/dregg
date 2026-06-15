//! # starbridge-storage-gateway-mandate
//!
//! Scaffold for the **Storage Gateway Mandate** starbridge-app, mapping
//! `metatheory/Dregg2/Apps/StorageGatewayMandate*.lean` onto dregg-native
//! primitives.
//!
//! The mandate cell carries:
//! - `object_key`, `last_op` (GET/PUT/LIST encoded as 0/1/2);
//! - `volume_spent` (monotonic Stingray debit tracker);
//! - immutable `commitment_anchor` and `volume_ceiling`.
//!
//! Predicate-layer admission mirrors Lean `sgmAdmitM`: op allowlist, prefix
//! authorization (PUT), clearance (GET), and volume-budget debits.

#![forbid(unsafe_code)]

use dregg_app_framework::{
    Action, AppCipherclerk, AuthRequired, CapTarget, CapTemplate, CellAffordance, CellId, CellMode,
    CellProgram, ChildVkStrategy, ConstantsModule, DeosApp, DeosCell, Effect, EmbeddedExecutor,
    Event, FactoryDescriptor, FireExecuteError, GatedAffordance, InspectorDescriptor,
    StarbridgeAppContext, StateConstraint, TransitionCase, TransitionGuard, TurnReceipt,
    canonical_program_vk, clearance_graph_root, field_from_u64, hex_encode_32, symbol,
};

// Re-export the field primitives so differential tests (and downstream callers) can build the
// same `FieldElement` corpus the admission predicates consume, without depending directly on
// `dregg-app-framework`.
pub use dregg_app_framework::{FieldElement, field_from_bytes};

// =============================================================================
// Storage domain (VFS ops)
// =============================================================================

/// Storage gateway operation (Lean `StorageOp`: GET / PUT / LIST).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StorageOp {
    /// Read — requires compartment clearance on `read_compartment`.
    Get,
    /// Write — requires key under mandated prefix.
    Put,
    /// List — op-allowlist + volume debit only.
    List,
}

impl StorageOp {
    /// Encode as an `Int` field value (Lean `StorageOp.toInt`).
    pub const fn to_field_value(self) -> u64 {
        match self {
            Self::Get => 0,
            Self::Put => 1,
            Self::List => 2,
        }
    }

    /// Decode from a field-encoded op (Lean `StorageOp.ofInt`).
    pub fn from_field_value(value: u64) -> Option<Self> {
        match value {
            0 => Some(Self::Get),
            1 => Some(Self::Put),
            2 => Some(Self::List),
            _ => None,
        }
    }

    /// Per-op Stingray volume debit (Lean `opCost`).
    pub const fn demo_cost(self) -> u64 {
        match self {
            Self::Get => 1,
            Self::Put => 5,
            Self::List => 2,
        }
    }
}

/// Default demo prefix (Lean `demoMandate.keyPrefix`).
pub const DEFAULT_KEY_PREFIX: &str = "uploads/";

/// Default Stingray volume ceiling (Lean `demoMandate.volumeBudget.ceiling`).
pub const DEFAULT_VOLUME_CEILING: u64 = 10;

/// Default commitment-anchor bucket tag (Lean `demoMandate.anchor`).
pub const DEFAULT_COMMITMENT_ANCHOR: u64 = 42;

/// Demo read-compartment label (Lean `readCompartment`).
pub const DEFAULT_READ_COMPARTMENT: &str = "storage-read";

// =============================================================================
// Slot layout (mandate cell)
// =============================================================================

/// Slot 0 — `object_key`. Content-addressed key hash for the last op.
pub const OBJECT_KEY_SLOT: u8 = 0;

/// Slot 1 — `last_op`. Encoded [`StorageOp`] (0/1/2).
pub const LAST_OP_SLOT: u8 = 1;

/// Slot 2 — `volume_spent`. Monotonic Stingray debit tracker.
pub const VOLUME_SPENT_SLOT: u8 = 2;

/// Slot 3 — `commitment_anchor`. Immutable bucket/compartment tag.
pub const COMMITMENT_ANCHOR_SLOT: u8 = 3;

/// Slot 4 — `volume_ceiling`. Immutable Stingray slice ceiling.
pub const VOLUME_CEILING_SLOT: u8 = 4;

/// Slot 5 — `key_prefix_hash`. Immutable authorized prefix commitment.
pub const KEY_PREFIX_HASH_SLOT: u8 = 5;

/// Slot 6 — `read_compartment_hash`. Immutable GET clearance label (the box label
/// a GET actor's clearance must dominate). Frozen by `init_gateway` (`WriteOnce`).
pub const READ_COMPARTMENT_SLOT: u8 = 6;

/// Slot 7 — `clearance_graph_root`. Immutable Merkle commitment over the
/// `(dominator, dominated)` clearance edges (Lean `demoGraph`). The executor's
/// [`StateConstraint::ClearanceDominates`] recomputes this from the carried edges
/// and refuses any GET whose graph does not match it (the stored root is
/// LOAD-BEARING). Frozen by `init_gateway` (`WriteOnce`).
pub const CLEARANCE_GRAPH_ROOT_SLOT: u8 = 7;

/// Slot 8 — `actor_clearance`. The GET actor's clearance label, materialized into
/// state by the GET turn so the executor's [`StateConstraint::ClearanceDominates`]
/// checks it dominates `READ_COMPARTMENT_SLOT` in the root-bound clearance graph.
/// Re-bound per GET (the acting reader presents their clearance).
pub const ACTOR_CLEARANCE_SLOT: u8 = 8;

// =============================================================================
// Factory configuration
// =============================================================================

/// The factory VK we publish for the storage-gateway mandate factory.
pub const SGM_FACTORY_VK: [u8; 32] = *b"starbridge-sgm-mandate-factory!!";

/// Default per-epoch creation budget.
pub const DEFAULT_CREATION_BUDGET: u64 = 512;

/// Hash an object key string for slot storage.
pub fn object_key_field(key: &str) -> FieldElement {
    field_from_bytes(key.as_bytes())
}

/// Hash the mandated key prefix.
pub fn key_prefix_field(prefix: &str) -> FieldElement {
    field_from_bytes(prefix.as_bytes())
}

/// Whether `op` is in the allowed set (Lean `opAllowed`).
pub fn op_allowed(op: StorageOp, allowed: &[StorageOp]) -> bool {
    allowed.contains(&op)
}

/// Object key lies under the mandated prefix (Lean `keyUnderPrefix` / `putPrefixOK`).
pub fn key_under_prefix(prefix: &str, key: &str) -> bool {
    key.starts_with(prefix)
}

/// The named `writer` clearance label of the demo clearance graph (Lean
/// `demoMandate.actorLabels`, `StorageGatewayMandate/Core.lean:331`). A writer's
/// clearance dominates `storage-read`, so a writer may GET.
pub fn writer_label() -> FieldElement {
    field_from_bytes(b"writer")
}
/// The named `guest` clearance label (Lean `guestMandate`): does NOT dominate
/// `storage-read`, so a guest's GET is refused. See [`writer_label`].
pub fn guest_label() -> FieldElement {
    field_from_bytes(b"guest")
}

/// **The demo clearance graph** — the `(dominator, dominated)` edge set of Lean
/// `demoGraph` (`StorageGatewayMandate/Core.lean:320`): `writer ⊐ storage-read`.
/// A writer's clearance dominates the read compartment (it may GET); a guest's
/// does not. Dominance is the reflexive-transitive closure of these edges (the
/// proved-sound `ClearanceGraph.dominatesD`). This IS the graph the cell commits
/// in `CLEARANCE_GRAPH_ROOT_SLOT` ([`clearance_root`]) and the executor's
/// [`StateConstraint::ClearanceDominates`] walks.
pub fn clearance_graph() -> Vec<(FieldElement, FieldElement)> {
    vec![(
        writer_label(),
        field_from_bytes(DEFAULT_READ_COMPARTMENT.as_bytes()),
    )]
}

/// The canonical commitment of the demo clearance graph — the value pinned in the
/// cell's `CLEARANCE_GRAPH_ROOT_SLOT`. The executor's `ClearanceDominates`
/// recomputes this from the carried edges and refuses any GET whose graph does not
/// match it (the stored root is LOAD-BEARING).
pub fn clearance_root() -> FieldElement {
    clearance_graph_root(&clearance_graph())
}

/// Fuel-bounded reflexive-transitive dominance over the clearance graph — the
/// hand-port of the proved-sound Lean `ClearanceGraph.dominatesD`/`dominatesFuel`
/// (`Authority/ClearanceGraph.lean:46,53`) over the felt-label substrate.
/// Reflexive (an actor holding exactly the box label is cleared). Mirrors the
/// executor's `dominates_closure` (`cell/src/program.rs`).
pub fn dominates(edges: &[(FieldElement, FieldElement)], a: FieldElement, b: FieldElement) -> bool {
    fn go(
        edges: &[(FieldElement, FieldElement)],
        a: FieldElement,
        b: FieldElement,
        fuel: usize,
    ) -> bool {
        if fuel == 0 {
            return false;
        }
        if a == b {
            return true;
        }
        edges
            .iter()
            .any(|(src, mid)| *src == a && go(edges, *mid, b, fuel - 1))
    }
    go(edges, a, b, edges.len() + 1)
}

/// **`get_clearance_ok`** — some held actor label DOMINATES the GET read
/// compartment in the demo clearance graph (Lean `getClearanceOK` =
/// `mayRead m.clearanceGraph m.actorLabels m.readCompartment`,
/// `StorageGatewayMandate/Core.lean:85`). NO LONGER a flat `contains` — it walks
/// the reflexive-transitive dominance closure of [`clearance_graph`], so a writer
/// (whose clearance dominates `storage-read`) is cleared while a guest is not.
/// This is the predicate-layer twin of the executor's
/// [`StateConstraint::ClearanceDominates`] tooth (both decide via [`dominates`]).
pub fn get_clearance_ok(actor_labels: &[FieldElement], read_compartment: FieldElement) -> bool {
    let edges = clearance_graph();
    actor_labels
        .iter()
        .any(|&a| dominates(&edges, a, read_compartment))
}

/// The root-bound clearance constraint the executor re-enforces on every GET: the
/// GET actor's clearance in `ACTOR_CLEARANCE_SLOT` dominates the read compartment
/// in `READ_COMPARTMENT_SLOT`, in the demo clearance graph whose canonical
/// commitment must equal `CLEARANCE_GRAPH_ROOT_SLOT`. The Rust twin of Lean
/// `getClearanceOK` made an inline executor tooth (`ClearanceGraph.dominatesD`,
/// soundness `dominates_of_dominatesD`), bound to the stored root so the slot is
/// LOAD-BEARING.
pub fn clearance_dominates_constraint() -> StateConstraint {
    StateConstraint::ClearanceDominates {
        actor_label_index: ACTOR_CLEARANCE_SLOT,
        box_index: READ_COMPARTMENT_SLOT,
        root_index: CLEARANCE_GRAPH_ROOT_SLOT,
        edges: clearance_graph(),
    }
}

/// Stingray volume debit admission (Lean `Slice.tryDebit`).
pub fn volume_debit_ok(spent: u64, cost: u64, ceiling: u64) -> bool {
    spent.saturating_add(cost) <= ceiling
}

/// Compute new spent after a successful debit.
pub fn volume_after_debit(spent: u64, cost: u64) -> Option<u64> {
    let new = spent.checked_add(cost)?;
    if new <= ceiling_for_demo() {
        Some(new)
    } else {
        None
    }
}

fn ceiling_for_demo() -> u64 {
    DEFAULT_VOLUME_CEILING
}

/// **`sgm_admit`** — predicate-level one-step admission (Lean `sgmAdmitM`).
pub fn sgm_admit(
    spent: u64,
    ceiling: u64,
    key: &str,
    prefix: &str,
    op: StorageOp,
    allowed: &[StorageOp],
    actor_labels: &[FieldElement],
    read_compartment: FieldElement,
) -> Option<u64> {
    if !op_allowed(op, allowed) {
        return None;
    }
    match op {
        StorageOp::Get => {
            if !get_clearance_ok(actor_labels, read_compartment) {
                return None;
            }
            let cost = op.demo_cost();
            if volume_debit_ok(spent, cost, ceiling) {
                Some(spent + cost)
            } else {
                None
            }
        }
        StorageOp::Put => {
            if !key_under_prefix(prefix, key) {
                return None;
            }
            let cost = op.demo_cost();
            if volume_debit_ok(spent, cost, ceiling) {
                Some(spent + cost)
            } else {
                None
            }
        }
        StorageOp::List => {
            let cost = op.demo_cost();
            if volume_debit_ok(spent, cost, ceiling) {
                Some(spent + cost)
            } else {
                None
            }
        }
    }
}

/// Cell-program skeleton: immutable anchor/ceiling/prefix + monotonic volume + bounded spend.
pub fn sgm_cell_program() -> CellProgram {
    CellProgram::Cases(vec![
        TransitionCase {
            guard: TransitionGuard::Always,
            constraints: vec![
                // `WriteOnce` (not `Immutable`): a factory-born gateway is empty,
                // so the bucket config slots are bound once by `init_mandate`
                // (from zero) and frozen thereafter — the birth-compatible form
                // of "fixed at creation".
                StateConstraint::WriteOnce {
                    index: COMMITMENT_ANCHOR_SLOT,
                },
                StateConstraint::WriteOnce {
                    index: VOLUME_CEILING_SLOT,
                },
                StateConstraint::WriteOnce {
                    index: KEY_PREFIX_HASH_SLOT,
                },
                StateConstraint::WriteOnce {
                    index: READ_COMPARTMENT_SLOT,
                },
                StateConstraint::FieldLteField {
                    left_index: VOLUME_SPENT_SLOT,
                    right_index: VOLUME_CEILING_SLOT,
                },
            ],
        },
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("storage_op"),
            },
            constraints: vec![StateConstraint::Monotonic {
                index: VOLUME_SPENT_SLOT,
            }],
        },
    ])
}

/// Canonical child program VK.
pub fn sgm_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&sgm_cell_program())
}

/// Build the `FactoryDescriptor` for storage-gateway mandate cells.
pub fn sgm_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: SGM_FACTORY_VK,
        child_program_vk: Some(sgm_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(sgm_child_program_vk()))),
        allowed_cap_templates: vec![CapTemplate {
            target: CapTarget::SelfCell,
            max_permissions: AuthRequired::Signature,
            attenuatable: true,
        }],
        // No creation-time `field_constraints`: a factory-born gateway cell is
        // born empty and its first `init_mandate` turn binds `COMMITMENT_ANCHOR`
        // + `VOLUME_CEILING` (`WriteOnce`, frozen after), THEN `storage_op` turns
        // debit `VOLUME_SPENT` (Monotonic, bounded by the ceiling). The birth
        // `NonZero`s validated against `params.initial_fields`, forcing the seed
        // path to mint placeholders — and a `1`-ceiling placeholder is a real
        // hazard (a one-byte storage budget). Mirror privacy-voting/bounty-board.
        field_constraints: vec![],
        state_constraints: vec![
            // Compartment tag + volume ceiling are bound ONCE by `init_mandate`
            // (from zero) and frozen thereafter.
            StateConstraint::WriteOnce {
                index: COMMITMENT_ANCHOR_SLOT,
            },
            StateConstraint::WriteOnce {
                index: VOLUME_CEILING_SLOT,
            },
            // The authorization scope commitments are equally one-shot: a
            // mutable prefix/compartment would let a later turn silently
            // re-point the mandate's PUT scope or GET clearance. The executor
            // installs these `state_constraints` as the born cell's program
            // (`apply_create_cell_from_factory`), so this is the binding that
            // actually bites on the live gateway cell.
            StateConstraint::WriteOnce {
                index: KEY_PREFIX_HASH_SLOT,
            },
            StateConstraint::WriteOnce {
                index: READ_COMPARTMENT_SLOT,
            },
            StateConstraint::Monotonic {
                index: VOLUME_SPENT_SLOT,
            },
            StateConstraint::FieldLteField {
                left_index: VOLUME_SPENT_SLOT,
                right_index: VOLUME_CEILING_SLOT,
            },
        ],
        default_mode: CellMode::Sovereign,
        creation_budget: Some(DEFAULT_CREATION_BUDGET),
    }
}

/// All factory descriptors this starbridge-app contributes.
pub fn factory_descriptors() -> Vec<FactoryDescriptor> {
    vec![sgm_factory_descriptor()]
}

// =============================================================================
// Turn builders
// =============================================================================

/// Build the on-ledger [`Action`] recording one storage op.
///
/// Effects (Lean `sgmStorageChain`):
/// 1. `SetField(OBJECT_KEY_SLOT, key_hash)`
/// 2. `SetField(LAST_OP_SLOT, op_code)`
/// 3. `SetField(VOLUME_SPENT_SLOT, new_spent)`
/// 4. `EmitEvent("storage-op", [op, key_hash, blob_hash, new_spent])`
pub fn build_storage_op_action(
    cipherclerk: &AppCipherclerk,
    mandate_cell: CellId,
    key: &str,
    op: StorageOp,
    new_volume_spent: u64,
    blob_hash: FieldElement,
) -> Action {
    let key_field = object_key_field(key);
    let op_field = field_from_u64(op.to_field_value());
    let spent_field = field_from_u64(new_volume_spent);

    let effects = vec![
        Effect::SetField {
            cell: mandate_cell,
            index: OBJECT_KEY_SLOT as usize,
            value: key_field,
        },
        Effect::SetField {
            cell: mandate_cell,
            index: LAST_OP_SLOT as usize,
            value: op_field,
        },
        Effect::SetField {
            cell: mandate_cell,
            index: VOLUME_SPENT_SLOT as usize,
            value: spent_field,
        },
        Effect::EmitEvent {
            cell: mandate_cell,
            event: Event::new(
                symbol("storage-op"),
                vec![op_field, key_field, blob_hash, spent_field],
            ),
        },
    ];

    cipherclerk.make_action(mandate_cell, "storage_op", effects)
}

/// Convenience wrappers mirroring GET / PUT / LIST turn-builder names.
pub fn build_storage_get_action(
    cipherclerk: &AppCipherclerk,
    mandate_cell: CellId,
    key: &str,
    new_volume_spent: u64,
) -> Action {
    build_storage_op_action(
        cipherclerk,
        mandate_cell,
        key,
        StorageOp::Get,
        new_volume_spent,
        field_from_u64(0),
    )
}

pub fn build_storage_put_action(
    cipherclerk: &AppCipherclerk,
    mandate_cell: CellId,
    key: &str,
    new_volume_spent: u64,
    blob_hash: FieldElement,
) -> Action {
    build_storage_op_action(
        cipherclerk,
        mandate_cell,
        key,
        StorageOp::Put,
        new_volume_spent,
        blob_hash,
    )
}

pub fn build_storage_list_action(
    cipherclerk: &AppCipherclerk,
    mandate_cell: CellId,
    key_prefix: &str,
    new_volume_spent: u64,
) -> Action {
    build_storage_op_action(
        cipherclerk,
        mandate_cell,
        key_prefix,
        StorageOp::List,
        new_volume_spent,
        field_from_u64(0),
    )
}

/// Build an initialization action pinning anchor, ceiling, prefix, and read compartment.
pub fn build_init_gateway_action(
    cipherclerk: &AppCipherclerk,
    mandate_cell: CellId,
    commitment_anchor: u64,
    volume_ceiling: u64,
    key_prefix: &str,
    read_compartment: &str,
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: mandate_cell,
            index: COMMITMENT_ANCHOR_SLOT as usize,
            value: field_from_u64(commitment_anchor),
        },
        Effect::SetField {
            cell: mandate_cell,
            index: VOLUME_CEILING_SLOT as usize,
            value: field_from_u64(volume_ceiling),
        },
        Effect::SetField {
            cell: mandate_cell,
            index: KEY_PREFIX_HASH_SLOT as usize,
            value: key_prefix_field(key_prefix),
        },
        Effect::SetField {
            cell: mandate_cell,
            index: READ_COMPARTMENT_SLOT as usize,
            value: field_from_bytes(read_compartment.as_bytes()),
        },
        Effect::EmitEvent {
            cell: mandate_cell,
            event: Event::new(
                symbol("storage-gateway-initialized"),
                vec![
                    field_from_u64(commitment_anchor),
                    field_from_u64(volume_ceiling),
                    key_prefix_field(key_prefix),
                    field_from_bytes(read_compartment.as_bytes()),
                ],
            ),
        },
    ];

    cipherclerk.make_action(mandate_cell, "init_gateway", effects)
}

// =============================================================================
// The deos-native surface — the GATEWAY as a composed `DeosApp`.
// =============================================================================
//
// `docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md`: the storage-gateway mandate should
// "actually mount at node startup" — its scaffold floor ([`sgm_cell_program`] /
// [`sgm_factory_descriptor`]) was executor-truth (the volume-budget caveats bite on a
// born cell) but had NO deos surface. This PROMOTES it: the three VFS operations are ONE
// [`DeosApp`] ([`gateway_app`] below); the framework wires the rest — per-viewer
// projection, web-of-cells publish (the GATEWAY cell IS a `dregg://` sturdyref),
// per-viewer rehydration, the generated `<dregg-affordance-surface>` component, and the
// manifest — none of which the floor scaffold had. `register(ctx)` now mounts it (see
// [`register_deos`]) — the census-flagged unblock (the node-startup wiring is a separate
// composition TODO; this makes the surface MOUNTABLE).
//
// **The seam is closed** — a TWO-TEMPO fire (mirror subscription / supply-chain). The
// state-advancing operation (`put`) is a [`GatedAffordance`] carrying a live-state
// PRECONDITION (budget remains — `VOLUME_SPENT < VOLUME_CEILING`); the FULL gateway
// invariants (the descriptor's flat `state_constraints`: `WriteOnce` anchor/ceiling/
// prefix/compartment, `Monotonic(VOLUME_SPENT)`, `FieldLteField(VOLUME_SPENT <=
// VOLUME_CEILING)`) are INSTALLED on the seeded gateway cell ([`seed_gateway`]) and
// RE-ENFORCED by the executor on every touching turn:
//
//   1. the deos PRECONDITION gate (the cap-gate `is_attenuation` AND the live-state
//      precondition `CellProgram::evaluate`) decides the button's verdict IN-BAND —
//      nothing submitted on a miss (anti-ghost; the htmx reactivity rides this);
//   2. [`fire_put`] then submits the FULL multi-effect `put` turn (reading the LIVE
//      `VOLUME_SPENT` and adding the object size), and the executor RE-ENFORCES the
//      installed invariants — so an OVER-BUDGET write (spend pushed past the ceiling,
//      `FieldLteField(VOLUME_SPENT <= VOLUME_CEILING)`) and a REWOUND meter (spend rolled
//      back to free budget, `Monotonic(VOLUME_SPENT)`) are REAL executor refusals in the
//      SUBMISSION path — the half the floor's predicate-only tests never exercised through
//      a real signed turn (see `tests/deos_seam.rs`).
//
// The volume budget as a LIVE GATE: each `put` is a metered write that debits the
// monotonic `VOLUME_SPENT` meter; the executor refuses a write that would exhaust the
// ceiling (the budget can never be over-spent) AND refuses a rewind that would forge free
// budget — the storage mandate's Stingray slice is enforced inline, not by app bookkeeping.

/// The storage rights tiers, ON THE REAL ATTENUATION LATTICE — these ARE the roles the
/// floor crate's cap-graph enforces:
///
///   - a READER holds [`AuthRequired::Signature`] — the narrow read tier: it can `get`
///     (read an object) and `list` (enumerate a prefix), nothing else;
///   - a WRITER holds [`AuthRequired::Either`] — it can `put` (a metered write that
///     debits the volume budget) AND read AND list;
///   - the MANDATE-HOLDER holds [`AuthRequired::None`]/root — it owns the gateway (it can
///     `init_gateway` / re-key on top of everything a writer can do).
///
/// So `Signature ⊂ Either ⊂ None` IS the reader ⊂ writer ⊂ mandate-holder ladder.
pub const READER_RIGHTS: AuthRequired = AuthRequired::Signature;
/// The writer rights tier (sig-or-proof — put + get + list). See [`READER_RIGHTS`].
pub const WRITER_RIGHTS: AuthRequired = AuthRequired::Either;
/// The mandate-holder rights tier (root — init/re-key + all). See [`READER_RIGHTS`].
pub const MANDATE_RIGHTS: AuthRequired = AuthRequired::None;

/// The **life-of-cell gateway invariants** the executor re-enforces on every touching
/// turn — exactly the factory descriptor's flat `state_constraints` (`WriteOnce`
/// anchor/ceiling/prefix/compartment, `Monotonic(VOLUME_SPENT)`, `FieldLteField(VOLUME_SPENT
/// <= VOLUME_CEILING)`). This is the FLAT predicate a factory-born gateway cell carries
/// FOR LIFE (the same one the floor's birth path installs on the born cell); the full
/// operation-scoped [`sgm_cell_program`] `Cases` shape is bound by the child program VK.
/// Installed by [`seed_gateway`] so the gated fires re-enforce it.
pub fn gateway_invariants_program() -> CellProgram {
    CellProgram::Predicate(sgm_factory_descriptor().state_constraints)
}

/// The **seeded gateway program** the deos fires re-enforce — the life-of-cell
/// invariants (an `Always` case carrying the flat [`gateway_invariants_program`]
/// constraints) PLUS the GET-clearance tooth (a `MethodIs("get")` case carrying
/// [`clearance_dominates_constraint`]). The deos surface's three operations —
/// `get` / `put` / `list` — are the dispatch cases (so the default-deny carve-out
/// admits exactly them, and the GET case adds the clearance check on top of the
/// universal invariants).
///
/// THE GET-CLEARANCE TOOTH (Lean `getClearanceOK`, root-bound): a GET turn
/// materializes the acting reader's clearance into `ACTOR_CLEARANCE_SLOT`; the
/// executor checks it DOMINATES the frozen `READ_COMPARTMENT_SLOT` box in the
/// clearance graph whose canonical commitment must equal `CLEARANCE_GRAPH_ROOT_SLOT`
/// — so a guest's GET (guest does not dominate `storage-read`) is a REAL executor
/// refusal, while a writer's GET is admitted; substitute an over-permissive graph
/// or tamper the root and it fails closed on the root check. `put` / `list` carry
/// no extra method-scoped teeth here (the `Always` invariants cover them).
pub fn gateway_program_with_clearance() -> CellProgram {
    let invariants = sgm_factory_descriptor().state_constraints;
    CellProgram::Cases(vec![
        TransitionCase {
            guard: TransitionGuard::Always,
            constraints: invariants,
        },
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("get"),
            },
            constraints: vec![clearance_dominates_constraint()],
        },
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("put"),
            },
            constraints: vec![],
        },
        TransitionCase {
            guard: TransitionGuard::MethodIs {
                method: symbol("list"),
            },
            constraints: vec![],
        },
    ])
}

/// The `put` **live-state precondition** — the gateway must have BUDGET REMAINING
/// (`VOLUME_SPENT < VOLUME_CEILING`, i.e. `VOLUME_SPENT <= VOLUME_CEILING - 1`). A real
/// [`CellProgram`] read against the cell's current state, so a `put` button is DARK on an
/// exhausted gateway (spend caught up to the ceiling) and LIT while budget remains (the
/// htmx tooth). This gates "may `put` fire now"; the budget INVARIANT
/// (`FieldLteField(VOLUME_SPENT <= VOLUME_CEILING)`, the spend never passes the ceiling) is
/// the installed [`gateway_invariants_program`] the executor re-enforces on the produced
/// transition.
pub fn budget_remaining_precondition() -> CellProgram {
    // `spent < ceiling` ≡ `spent <= ceiling - 1` ≡ `FieldLteOther { spent, ceiling, delta: -1 }`.
    CellProgram::Predicate(vec![StateConstraint::FieldLteOther {
        index: VOLUME_SPENT_SLOT,
        other: VOLUME_CEILING_SLOT,
        delta: -1,
    }])
}

/// **The storage GATEWAY as a composed [`DeosApp`]** — the whole interaction surface, on
/// the deos bones. The gateway cell is the agent's OWN cell (`cipherclerk.cell_id()`) so
/// fires execute against the seeded embedded ledger.
///
/// Three operations on the GATEWAY cell, on the reader ⊂ writer ⊂ mandate-holder rights
/// ladder:
///
///   - `get` — a cap-only affordance (a READER reads an object): `Signature`, an
///     `EmitEvent`;
///   - `list` — a cap-only affordance (a READER enumerates a prefix): `Signature`, an
///     `EmitEvent`;
///   - `put` — a [`GatedAffordance`] (a WRITER performs a metered write): `Either`, a
///     live-state PRECONDITION (budget remains, `VOLUME_SPENT < VOLUME_CEILING`); the real
///     fire ([`fire_put`]) submits the FULL `put` turn (reading the live spend + adding the
///     object size), re-enforced by the executor's installed invariants
///     (`FieldLteField(VOLUME_SPENT <= VOLUME_CEILING)` + `Monotonic(VOLUME_SPENT)`).
///
/// The gateway cell is published into the web-of-cells at the reader tier (a peer on
/// another federation reacquires the gateway across the membrane) and is discoverable
/// under `storage`.
///
/// Seed the cell's program + configured state with [`seed_gateway`] so the gated fires
/// have a live state and the executor re-enforces the invariants.
pub fn gateway_app(cipherclerk: &AppCipherclerk, executor: &EmbeddedExecutor) -> DeosApp {
    let gateway = cipherclerk.cell_id();

    // `get` — a READER reads an object (clearance-gated). A [`GatedAffordance`]: the cap
    // gate (`READER_RIGHTS`) AND a live-state PRECONDITION ([`budget_remaining_precondition`]:
    // budget headroom for the read) decide the button's verdict in-band. The real fire
    // ([`fire_get`]) submits the GET turn ([`get_effects`]) materializing the reader's
    // clearance, which the executor's `MethodIs("get")` [`clearance_dominates_constraint`]
    // re-enforces — so a GUEST's GET (guest does not dominate `storage-read` in the
    // root-bound clearance graph) is a REAL executor refusal, while a WRITER's is admitted.
    // The surface representative effect is the actor-clearance write (the decisive GET
    // effect); the real per-reader clearance is threaded by [`fire_get`].
    let get = GatedAffordance::new(
        CellAffordance::new(
            "get",
            READER_RIGHTS,
            Effect::SetField {
                cell: gateway,
                index: ACTOR_CLEARANCE_SLOT as usize,
                value: writer_label(),
            },
        ),
        budget_remaining_precondition(),
    );
    // `list` — a READER enumerates a prefix. Cap-only.
    let list = CellAffordance::new(
        "list",
        READER_RIGHTS,
        Effect::EmitEvent {
            cell: gateway,
            event: Event::new(symbol("storage-list"), vec![]),
        },
    );
    // `put` — a WRITER performs a metered write (recurring). The GatedAffordance carries
    // the DECISIVE effect (the `VOLUME_SPENT` debit) as its surface representative AND a
    // live-state PRECONDITION ([`budget_remaining_precondition`]: budget remains) — so the
    // button is dark when the budget is exhausted and lit while it remains, and the
    // cap∧state gate decides its verdict in-band. The actual fire ([`fire_put`]) submits
    // the FULL `put` turn ([`put_effects`]: key + op + new spend + event) reading the LIVE
    // spend, which the executor re-enforces the installed invariants on — so
    // `FieldLteField(VOLUME_SPENT <= VOLUME_CEILING)` BITES: an over-budget write is REFUSED.
    let put = GatedAffordance::new(
        CellAffordance::new(
            "put",
            WRITER_RIGHTS,
            Effect::SetField {
                cell: gateway,
                index: VOLUME_SPENT_SLOT as usize,
                value: field_from_u64(1),
            },
        ),
        budget_remaining_precondition(),
    );

    DeosApp::builder(
        "storage-gateway-mandate",
        cipherclerk.clone(),
        executor.clone(),
    )
    .discoverable(vec!["storage".into()])
    .cell(
        DeosCell::new(gateway, "gateway")
            .gated(get)
            .affordance(list)
            .gated(put)
            .publish(READER_RIGHTS),
    )
    .build()
}

/// **Seed the GATEWAY cell** so the gated fires have live state + the invariants bite:
/// install the gateway invariants ([`gateway_invariants_program`]) on the seeded gateway
/// cell (so the executor re-enforces them on every touching turn), then configure the
/// genesis state directly into the embedded ledger — bind `COMMITMENT_ANCHOR`,
/// `VOLUME_CEILING`, `KEY_PREFIX_HASH`, `READ_COMPARTMENT` (`WriteOnce`, frozen after) and
/// seed `VOLUME_SPENT = 0` (a fresh, fully-funded budget) so a real `(old, new)` baseline
/// exists against which `put` debits the meter.
///
/// After seeding, the gateway is configured with a `ceiling`-byte budget, all spent. A
/// caller passes a small `ceiling` to exercise the over-budget tooth quickly.
pub fn seed_gateway(
    executor: &EmbeddedExecutor,
    commitment_anchor: u64,
    volume_ceiling: u64,
    key_prefix: &str,
    read_compartment: &str,
) {
    let gateway = executor.cell_id();
    // Install the seeded program WITH the GET-clearance tooth (an `Always` invariants
    // case + a `MethodIs("get")` ClearanceDominates case), so the executor re-enforces
    // GET clearance on the fire path (a guest's GET is a REAL refusal).
    executor.install_program(gateway, gateway_program_with_clearance());
    executor.with_ledger_mut(|ledger| {
        if let Some(cell) = ledger.get_mut(&gateway) {
            cell.state.set_field(
                COMMITMENT_ANCHOR_SLOT as usize,
                field_from_u64(commitment_anchor),
            );
            cell.state
                .set_field(VOLUME_CEILING_SLOT as usize, field_from_u64(volume_ceiling));
            cell.state
                .set_field(KEY_PREFIX_HASH_SLOT as usize, key_prefix_field(key_prefix));
            cell.state.set_field(
                READ_COMPARTMENT_SLOT as usize,
                field_from_bytes(read_compartment.as_bytes()),
            );
            // The REAL clearance-graph commitment — so the executor's root-bound
            // ClearanceDominates admits a cleared writer's GET and refuses a guest's
            // (a bogus root would fail EVERY GET closed).
            cell.state
                .set_field(CLEARANCE_GRAPH_ROOT_SLOT as usize, clearance_root());
            // a fresh, fully-funded budget: nothing spent yet.
            cell.state
                .set_field(VOLUME_SPENT_SLOT as usize, field_from_u64(0));
        }
    });
}

/// **`put` effects** — the multi-effect metered-write body: write the object key into
/// `OBJECT_KEY`, record `LAST_OP = PUT`, advance the producer meter `VOLUME_SPENT` to
/// `new_spent` (`Monotonic` — never rewound, and `FieldLteField`-bounded by the ceiling),
/// and emit `storage-op`. This is the ONE coherent transition the installed invariants
/// admit (the spend advances, anchor/ceiling/prefix/compartment unchanged, `VOLUME_SPENT <=
/// VOLUME_CEILING` preserved). The deos `put` gated affordance is the cap∧state
/// PRECONDITION face; THIS is the turn [`fire_put`] submits.
pub fn put_effects(
    gateway: CellId,
    key: &str,
    new_spent: u64,
    blob_hash: FieldElement,
) -> Vec<Effect> {
    let key_field = object_key_field(key);
    let op_field = field_from_u64(StorageOp::Put.to_field_value());
    let spent_field = field_from_u64(new_spent);
    vec![
        Effect::SetField {
            cell: gateway,
            index: OBJECT_KEY_SLOT as usize,
            value: key_field,
        },
        Effect::SetField {
            cell: gateway,
            index: LAST_OP_SLOT as usize,
            value: op_field,
        },
        Effect::SetField {
            cell: gateway,
            index: VOLUME_SPENT_SLOT as usize,
            value: spent_field,
        },
        Effect::EmitEvent {
            cell: gateway,
            event: Event::new(
                symbol("storage-op"),
                vec![op_field, key_field, blob_hash, spent_field],
            ),
        },
    ]
}

/// **Fire `put`** — the deos cap∧state PRECONDITION gate (anti-ghost, in-band), then the
/// FULL metered-write turn the executor re-enforces the gateway invariants on. The
/// two-tempo bridge: the gated affordance decides the button's verdict (cap ⊇ Either AND
/// budget remains) WITHOUT touching the executor; on both passing, the complete
/// meter-advancing turn ([`put_effects`]) is submitted, and the executor's re-enforcement
/// of [`gateway_invariants_program`] is the SECOND, verified gate
/// (`FieldLteField(VOLUME_SPENT <= VOLUME_CEILING)` + `Monotonic(VOLUME_SPENT)` bite — an
/// over-budget write OR a rewound meter is REFUSED). Anti-ghost both ways: a precondition
/// miss never submits; an invariant violation is a real executor refusal.
///
/// The meter is read from the cell's live state (current `VOLUME_SPENT` + `object_size` ⇒
/// the new spend), so the caller threads only the key + size. Use [`seed_gateway`] first.
pub fn fire_put(
    app: &DeosApp,
    held: &AuthRequired,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
    key: &str,
    object_size: u64,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = &app.cells()[0];
    let gateway = cell.cell();
    // The metered-write turn, with the spend read from LIVE state: the cap∧state
    // PRECONDITION gate runs IN-BAND (nothing submitted on a miss — anti-ghost), then the
    // FULL `put` turn ([`put_effects`]) is submitted with `new_spent := live VOLUME_SPENT +
    // object_size`, and the executor re-enforces the installed invariants on the produced
    // transition (`FieldLteField(VOLUME_SPENT <= VOLUME_CEILING)` bites an over-budget write;
    // `Monotonic(VOLUME_SPENT)` bites a rewound meter).
    let key = key.to_string();
    let blob = field_from_bytes(key.as_bytes());
    cell.fire_gated_through_executor_with("put", held, cipherclerk, executor, move |live| {
        let live_spent = field_to_u64(&live.fields[VOLUME_SPENT_SLOT as usize]);
        put_effects(gateway, &key, live_spent + object_size, blob)
    })
}

/// **`get` effects** — the GET turn body: MATERIALIZE the acting reader's clearance
/// label into `ACTOR_CLEARANCE_SLOT` (so the executor's [`clearance_dominates_constraint`]
/// reads it), record `LAST_OP = GET`, and emit `storage-op`. Leaves `VOLUME_SPENT`
/// unchanged (`Monotonic` admits the no-change; the GET-clearance demo isolates the
/// dominance tooth — the budget tooth is exercised by `put`). This is the turn
/// [`fire_get`] submits; the executor's `MethodIs("get")` case then checks the
/// presented clearance DOMINATES the frozen read compartment in the root-bound graph.
pub fn get_effects(gateway: CellId, key: &str, actor_clearance: FieldElement) -> Vec<Effect> {
    let key_field = object_key_field(key);
    let op_field = field_from_u64(StorageOp::Get.to_field_value());
    vec![
        Effect::SetField {
            cell: gateway,
            index: OBJECT_KEY_SLOT as usize,
            value: key_field,
        },
        Effect::SetField {
            cell: gateway,
            index: LAST_OP_SLOT as usize,
            value: op_field,
        },
        // The reader presents their clearance label — the executor's ClearanceDominates
        // checks it dominates the frozen READ_COMPARTMENT_SLOT box.
        Effect::SetField {
            cell: gateway,
            index: ACTOR_CLEARANCE_SLOT as usize,
            value: actor_clearance,
        },
        Effect::EmitEvent {
            cell: gateway,
            event: Event::new(
                symbol("storage-op"),
                vec![op_field, key_field, field_from_u64(0), actor_clearance],
            ),
        },
    ]
}

/// **Fire `get`** — the deos cap∧state PRECONDITION gate (anti-ghost, in-band), then a
/// real verified GET turn through the executor, presenting `actor_clearance` as the
/// acting reader's clearance label. The two-tempo bridge: the gated `get` affordance
/// decides the button's verdict (cap ⊇ `READER_RIGHTS` AND budget remains) WITHOUT
/// touching the executor; on both passing, the GET turn ([`get_effects`]) materializes
/// the reader's clearance, and the executor's `MethodIs("get")`
/// [`clearance_dominates_constraint`] is the SECOND, verified tooth — a reader whose
/// clearance DOMINATES the frozen read compartment in the root-bound clearance graph is
/// ADMITTED; a guest (does not dominate `storage-read`) is a REAL executor refusal;
/// substitute an over-permissive graph or tamper the root and it fails closed. Use
/// [`seed_gateway`] first.
pub fn fire_get(
    app: &DeosApp,
    held: &AuthRequired,
    actor_clearance: FieldElement,
    cipherclerk: &AppCipherclerk,
    executor: &EmbeddedExecutor,
    key: &str,
) -> Result<TurnReceipt, FireExecuteError> {
    let cell = &app.cells()[0];
    let gateway = cell.cell();
    let key = key.to_string();
    cell.fire_gated_through_executor_with("get", held, cipherclerk, executor, move |_live| {
        get_effects(gateway, &key, actor_clearance)
    })
}

/// Read a `u64` from the last 8 big-endian bytes of a field element (the inverse of
/// [`field_from_u64`] for the volume meter the gateway stores).
fn field_to_u64(f: &FieldElement) -> u64 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&f[24..32]);
    u64::from_be_bytes(b)
}

/// **Mount the deos-native surface** ([`gateway_app`]) on a shared context: build the
/// composed [`DeosApp`] from the context's cipherclerk + executor, seed the gateway cell's
/// program + configured state (so the gated fires bite), and fold the app into the
/// context's affordance registry ([`DeosApp::register`]). Returns the live [`DeosApp`] (so
/// a host can also [`DeosApp::mount`] its axum router / [`DeosApp::publish_all`] into the
/// web-of-cells). This is the census unblock: the storage-gateway now MOUNTS a DeosApp
/// from `src/` (the node-startup composition is a separate TODO).
pub fn register_deos(ctx: &StarbridgeAppContext) -> DeosApp {
    let app = gateway_app(ctx.cipherclerk(), ctx.executor());
    // Seed the gateway cell so the gated `put` fire has a live `(old, new)` and the gateway
    // invariants (installed here) are re-enforced by the executor on every touching turn.
    seed_gateway(
        ctx.executor(),
        DEFAULT_COMMITMENT_ANCHOR,
        DEFAULT_VOLUME_CEILING,
        DEFAULT_KEY_PREFIX,
        DEFAULT_READ_COMPARTMENT,
    );
    app.register(ctx);
    app
}

// =============================================================================
// StarbridgeAppContext mount
// =============================================================================

/// The canonical web-constants module — the single source of truth the
/// `pages/constants.generated.js` is rendered from (slot layout + the two
/// storage event topics + the factory-vk hex).
pub fn web_constants() -> ConstantsModule {
    ConstantsModule::new("storage-gateway-mandate")
        .slot("OBJECT_KEY_SLOT", OBJECT_KEY_SLOT as u64)
        .slot("LAST_OP_SLOT", LAST_OP_SLOT as u64)
        .slot("VOLUME_SPENT_SLOT", VOLUME_SPENT_SLOT as u64)
        .slot("COMMITMENT_ANCHOR_SLOT", COMMITMENT_ANCHOR_SLOT as u64)
        .slot("VOLUME_CEILING_SLOT", VOLUME_CEILING_SLOT as u64)
        .slot("KEY_PREFIX_HASH_SLOT", KEY_PREFIX_HASH_SLOT as u64)
        .slot("READ_COMPARTMENT_SLOT", READ_COMPARTMENT_SLOT as u64)
        .slot(
            "CLEARANCE_GRAPH_ROOT_SLOT",
            CLEARANCE_GRAPH_ROOT_SLOT as u64,
        )
        .slot("ACTOR_CLEARANCE_SLOT", ACTOR_CLEARANCE_SLOT as u64)
        .string("FACTORY_VK_HEX", hex_encode_32(&SGM_FACTORY_VK))
        .topic("INITIALIZED", "storage-gateway-initialized")
        .topic("OP", "storage-op")
}

/// Register the storage-gateway-mandate starbridge-app on a shared context.
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    let factory_vk = ctx.register_factory(sgm_factory_descriptor());

    ctx.register_inspector(InspectorDescriptor {
        kind: "sgm-gateway".into(),
        descriptor: serde_json::json!({
            "component": "dregg-sgm-gateway",
            "module": "/starbridge-apps/storage-gateway-mandate/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "summary_fields": ["object_key", "last_op", "volume_spent", "commitment_anchor"],
            "slot_layout": {
                "object_key": OBJECT_KEY_SLOT,
                "last_op": LAST_OP_SLOT,
                "volume_spent": VOLUME_SPENT_SLOT,
                "commitment_anchor": COMMITMENT_ANCHOR_SLOT,
                "volume_ceiling": VOLUME_CEILING_SLOT,
                "key_prefix_hash": KEY_PREFIX_HASH_SLOT,
                "read_compartment": READ_COMPARTMENT_SLOT,
            },
            "factory_vk_hex": hex_encode_32(&factory_vk),
            "child_program_vk_hex": hex_encode_32(&sgm_child_program_vk()),
            "storage_ops": ["GET", "PUT", "LIST"],
        }),
    });

    ctx.register_inspector_with("sgm-storage-form", || {
        serde_json::json!({
            "component": "dregg-sgm-storage-form",
            "module": "/starbridge-apps/storage-gateway-mandate/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "builders_module": "/starbridge-apps/storage-gateway-mandate/turn-builders.js",
            "methods": [
                "storage_get",
                "storage_put",
                "storage_list",
                "init_gateway"
            ],
        })
    });

    // Mount the deos-native composition surface (the `DeosApp`) on the SAME context — the
    // census unblock: the storage-gateway now mounts a `DeosApp` from `src/`. The factory +
    // inspectors are where SOUNDNESS lives (an over-budget write is a real executor refusal
    // on the born cell); the deos surface is the composition skin (per-viewer projection,
    // the cap∧state gated `put` fire, the `dregg://` publish, the rehydratable snapshot, the
    // manifest).
    register_deos(ctx);

    factory_vk
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::{AgentCipherclerk, Authorization, EmbeddedExecutor};

    fn test_cipherclerk() -> AppCipherclerk {
        AppCipherclerk::new(AgentCipherclerk::new(), [42u8; 32])
    }

    fn test_context() -> StarbridgeAppContext {
        let cipherclerk = test_cipherclerk();
        let executor = EmbeddedExecutor::new(&cipherclerk, "default");
        StarbridgeAppContext::new(cipherclerk, executor)
    }

    fn test_cell() -> CellId {
        CellId::from_bytes([9u8; 32])
    }

    const ALLOWED: [StorageOp; 3] = [StorageOp::Put, StorageOp::Get, StorageOp::List];

    #[test]
    fn factory_descriptor_is_stable() {
        let h1 = sgm_factory_descriptor().hash();
        let h2 = sgm_factory_descriptor().hash();
        assert_eq!(h1, h2);
    }

    #[test]
    fn storage_op_round_trip_encoding() {
        assert_eq!(StorageOp::from_field_value(0), Some(StorageOp::Get));
        assert_eq!(StorageOp::from_field_value(1), Some(StorageOp::Put));
        assert_eq!(StorageOp::from_field_value(2), Some(StorageOp::List));
        assert_eq!(StorageOp::Get.to_field_value(), 0);
    }

    #[test]
    fn sgm_admit_matches_lean_demo_guards() {
        let writer = field_from_bytes(b"writer");
        let read_comp = field_from_bytes(DEFAULT_READ_COMPARTMENT.as_bytes());
        let labels = [writer];

        // PUT under prefix succeeds.
        assert_eq!(
            sgm_admit(
                0,
                DEFAULT_VOLUME_CEILING,
                "uploads/doc.txt",
                DEFAULT_KEY_PREFIX,
                StorageOp::Put,
                &ALLOWED,
                &labels,
                read_comp,
            ),
            Some(5)
        );

        // PUT outside prefix rejected.
        assert_eq!(
            sgm_admit(
                0,
                DEFAULT_VOLUME_CEILING,
                "secret/doc.txt",
                DEFAULT_KEY_PREFIX,
                StorageOp::Put,
                &ALLOWED,
                &labels,
                read_comp,
            ),
            None
        );

        // GET without read clearance rejected.
        let guest = field_from_bytes(b"guest");
        assert_eq!(
            sgm_admit(
                0,
                DEFAULT_VOLUME_CEILING,
                "uploads/doc.txt",
                DEFAULT_KEY_PREFIX,
                StorageOp::Get,
                &ALLOWED,
                &[guest],
                read_comp,
            ),
            None
        );

        // Over-debit rejected (three PUTs at cost 5 exhaust ceiling 10).
        assert_eq!(
            sgm_admit(
                10,
                DEFAULT_VOLUME_CEILING,
                "uploads/a.txt",
                DEFAULT_KEY_PREFIX,
                StorageOp::Put,
                &ALLOWED,
                &labels,
                read_comp,
            ),
            None
        );
    }

    #[test]
    fn storage_op_action_writes_slots_and_emits_event() {
        let cipherclerk = test_cipherclerk();
        let blob = field_from_u64(0xdeadbeef);
        let action = build_storage_put_action(&cipherclerk, test_cell(), "uploads/x.txt", 5, blob);
        assert_eq!(action.effects.len(), 4);
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, .. } if *index == OBJECT_KEY_SLOT as usize
        ));
        assert!(matches!(
            &action.effects[1],
            Effect::SetField { index, .. } if *index == LAST_OP_SLOT as usize
        ));
        assert!(matches!(
            &action.effects[2],
            Effect::SetField { index, .. } if *index == VOLUME_SPENT_SLOT as usize
        ));
        assert!(matches!(&action.effects[3], Effect::EmitEvent { .. }));
    }

    #[test]
    fn storage_action_carries_real_signature() {
        let cipherclerk = test_cipherclerk();
        let action = build_storage_get_action(&cipherclerk, test_cell(), "uploads/y.txt", 1);
        match action.authorization {
            Authorization::Signature(a, b) => {
                assert!(a != [0u8; 32] || b != [0u8; 32]);
            }
            other => panic!("expected Signature, got {other:?}"),
        }
    }

    #[test]
    fn register_installs_factory_and_inspectors() {
        let ctx = test_context();
        let vk = register(&ctx);
        assert_eq!(vk, SGM_FACTORY_VK);
        assert_eq!(ctx.factory_registry().len(), 1);
        assert!(ctx.inspector_registry().get("sgm-gateway").is_some());
        assert!(ctx.inspector_registry().get("sgm-storage-form").is_some());
    }
}
