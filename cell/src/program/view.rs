use super::*;

// ============================================================================
// Live-view projection (StateConstraintView) — the self-describing surface
// ============================================================================
//
// A live cell must be able to SHOW its own program. The node's cell endpoint
// (`node/src/api.rs` `get_cell_detail`) and the wasm runtime's
// `get_cell_state` both project `CellProgram` through these view types so JS
// inspectors (e.g. the Studio polis inspector) can switch on `kind` without
// decoding postcard bytes.
//
// TOTAL BY CONSTRUCTION: the `to_view` matches carry no wildcard arm, so
// adding a `StateConstraint` / `SimpleStateConstraint` / `TransitionGuard`
// variant without a view projection is a COMPILE ERROR — the live-view seam
// cannot silently reopen. (`tests::view_projection_is_total_and_kind_tagged`
// additionally pins the serialized `kind` tag per variant.)
//
// Wire shape: `{ "kind": "<VariantName>", ...semantic payload }`. Field
// names and hex encodings are wire-compatible with the original wasm-only
// views; 32-byte values are lowercase 64-hex strings; u64-lane scalars
// (`MemberOf` sets, `Reachable` edges, affine coefficients…) are plain JSON
// numbers.

fn view_hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// Top-level view of a cell's program.
#[derive(Clone, Debug, PartialEq, Serialize)]
#[serde(tag = "kind")]
pub enum CellProgramView {
    /// No program — any authorized state change is valid.
    None,
    /// Predicate program: a list of slot-caveat constraints (implicit AND).
    Predicate {
        constraints: Vec<StateConstraintView>,
    },
    /// Cases program: operation-scoped cases with guards.
    Cases { cases: Vec<TransitionCaseView> },
    /// Circuit program: an AIR/R1CS circuit identified by its VK hash.
    Circuit { circuit_hash: String },
}

/// Per-case view in a Cases program.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct TransitionCaseView {
    pub guard: TransitionGuardView,
    pub constraints: Vec<StateConstraintView>,
}

/// [`TransitionGuard`] view.
#[derive(Clone, Debug, PartialEq, Serialize)]
#[serde(tag = "kind")]
pub enum TransitionGuardView {
    Always,
    MethodIs { method: String },
    EffectKindIs { mask: u32 },
    SlotChanged { index: u8 },
    AnyOf { children: Vec<TransitionGuardView> },
    AllOf { children: Vec<TransitionGuardView> },
}

/// Per-variant view for each [`StateConstraint`] (plus `Not`, which only
/// occurs inside `AnyOf`/`AllOf` via [`SimpleStateConstraint`]). Uses a
/// tagged-union shape so JS can switch on `kind`.
#[derive(Clone, Debug, PartialEq, Serialize)]
#[serde(tag = "kind")]
pub enum StateConstraintView {
    FieldEquals {
        index: u8,
        value: String,
    },
    FieldGte {
        index: u8,
        value: String,
    },
    FieldLte {
        index: u8,
        value: String,
    },
    FieldLteField {
        left_index: u8,
        right_index: u8,
    },
    /// `new[index] <= new[other] + delta` (signed; u64 lane).
    FieldLteOther {
        index: u8,
        other: u8,
        delta: i64,
    },
    SumEquals {
        indices: Vec<u8>,
        value: String,
    },
    WriteOnce {
        index: u8,
    },
    Immutable {
        index: u8,
    },
    Monotonic {
        index: u8,
    },
    StrictMonotonic {
        index: u8,
    },
    BoundedBy {
        index: u8,
        witness_index: u8,
    },
    FieldDelta {
        index: u8,
        delta: String,
    },
    FieldDeltaInRange {
        index: u8,
        min_delta: String,
        max_delta: String,
    },
    FieldGteHeight {
        index: u8,
        offset: i64,
    },
    FieldLteHeight {
        index: u8,
        offset: i64,
    },
    SumEqualsAcross {
        input_fields: Vec<u8>,
        output_fields: Vec<u8>,
    },
    SenderAuthorized {
        set_kind: String,
        commitment: String,
    },
    CapabilityUniqueness {
        cap_set_root_slot: u8,
    },
    RateLimit {
        max_per_epoch: u32,
        epoch_duration: u64,
    },
    RateLimitBySum {
        slot_index: u8,
        max_sum_per_epoch: u64,
        epoch_duration: u64,
    },
    TemporalGate {
        not_before: Option<u64>,
        not_after: Option<u64>,
    },
    /// "stayed under k": pre-state counter register `< k`.
    RateBound {
        counter_index: u8,
        k: u64,
    },
    /// "only after it cooled": `staged_at + period <= block_height`.
    CooledSince {
        staged_at: u64,
        period: u64,
    },
    /// "P until Y": admit while the event register reads 0 (U operator).
    UntilEvent {
        flag_index: u8,
    },
    /// "since the event": admit once the event register is set (S operator).
    SinceEvent {
        flag_index: u8,
    },
    /// Optimistic settlement: window elapsed AND no challenge filed.
    ChallengeWindow {
        challenge_index: u8,
        staged_at: u64,
        period: u64,
    },
    PreimageGate {
        commitment_index: u8,
        hash_kind: String,
    },
    MonotonicSequence {
        seq_index: u8,
    },
    AllowedTransitions {
        slot_index: u8,
        /// Allowed `(old_value, new_value)` pairs, each 64-hex.
        allowed: Vec<(String, String)>,
    },
    TemporalPredicate {
        witness_index: u8,
        dsl_hash: String,
    },
    BoundDelta {
        local_slot: u8,
        peer_cell: String,
        peer_slot: u8,
        delta_relation: String,
    },
    AnyOf {
        variants: Vec<StateConstraintView>,
    },
    Witnessed {
        predicate_kind: String,
        commitment: String,
        input_ref: String,
        proof_witness_index: usize,
    },
    Renounced {
        set_kind: String,
        commitment: String,
    },
    /// `new[index]` must be one of `set` (u64 lane).
    MemberOf {
        index: u8,
        set: Vec<u64>,
    },
    /// The scalar path read from `seg_indices` must start with `prefix`.
    PrefixOf {
        seg_indices: Vec<u8>,
        prefix: Vec<u64>,
    },
    /// `lo <= new[index] <= hi` (u64 lane).
    InRangeTwoSided {
        index: u8,
        lo: u64,
        hi: u64,
    },
    /// `|new[index] - old[index]| <= d` (u64 lane).
    DeltaBounded {
        index: u8,
        d: u64,
    },
    /// `Σ kᵢ·new[slotᵢ] <= c` — `terms` are `(coefficient, slot)` pairs.
    AffineLe {
        terms: Vec<(i64, u8)>,
        c: i64,
    },
    /// `Σ kᵢ·new[slotᵢ] = c` — `terms` are `(coefficient, slot)` pairs.
    AffineEq {
        terms: Vec<(i64, u8)>,
        c: i64,
    },
    /// Label at `new[from_index]` must reach `to_label` through `edges`
    /// (`(dominator, dominated)` pairs, reflexive-transitive closure).
    Reachable {
        from_index: u8,
        to_label: u64,
        edges: Vec<(u64, u64)>,
    },
    AllOf {
        variants: Vec<StateConstraintView>,
    },
    /// Negation (inside `AnyOf`/`AllOf` only): accept iff `inner` rejects.
    Not {
        inner: Box<StateConstraintView>,
    },
    Custom {
        ir_hash: String,
        descriptor_debug: String,
    },
    /// Turn sender must equal the bound public key (64-hex).
    SenderIs {
        pk: String,
    },
    /// Turn sender must equal the identity held in `new[index]`.
    SenderInSlot {
        index: u8,
    },
    /// The cell's own post-turn balance must be `>= min`.
    BalanceGte {
        min: u64,
    },
    /// The cell's own post-turn balance must be `<= max`.
    BalanceLte {
        max: u64,
    },
    /// KERI-shaped pre-rotation gate: rotating the `digest_slot` register
    /// demands the preimage of the OLD committed digest, installs it into
    /// `current_slot`, re-commits fresh, and waits `cooling_period` blocks
    /// since `last_rotated_slot`.
    KeyRotationGate {
        digest_slot: u8,
        current_slot: u8,
        last_rotated_slot: u8,
        cooling_period: u64,
        hash_kind: String,
    },
    /// Heap-keyed atom lifted over heap key `key` (the rotation's
    /// app-state lane; `key >= STATE_SLOTS` lives in `fields_map`).
    HeapField {
        key: u64,
        atom: HeapAtomView,
    },
    /// `new[index]` ≡ the cell's own post-turn `delegation_epoch` (the
    /// channels closure lane — a live group cell self-describes that its
    /// epoch slot IS the capability-freshness counter).
    DelegationEpochEquals {
        index: u8,
    },
    /// Witness-exhibited distinct-count ≥ `threshold` bound to the set
    /// commitment in `new[set_commitment_slot]` (in-program M-of-N).
    CountGe {
        threshold: u32,
        set_commitment_slot: u8,
    },
    /// Turn sender must be one of the bound public keys (each 64-hex) —
    /// the multi-admin actor binding (apps gap 3).
    SenderMemberOf {
        members: Vec<String>,
    },
    /// The cell's per-turn balance change must be `<= max` (signed; apps
    /// gap 4 rate ceiling).
    BalanceDeltaLte {
        max: i64,
    },
    /// The cell's per-turn balance change must be `>= min` (signed; apps
    /// gap 4 rate floor).
    BalanceDeltaGte {
        min: i64,
    },
    /// `Σ kᵢ·(new[slotᵢ] − old[slotᵢ]) <= c` — multi-field delta gate;
    /// `terms` are `(coefficient, slot)` pairs (apps gap 2).
    AffineDeltaLe {
        terms: Vec<(i64, u8)>,
        c: i64,
    },
    /// `new[local_field]` ≡ the FINALIZED value of `source_field` on peer
    /// `source_cell` at `at_root` (§11.2 cross-cell verified observation —
    /// a market reading an oracle's finalized price; cells are 64-hex).
    ObservedFieldEquals {
        local_field: u8,
        source_cell: String,
        source_field: u8,
        at_root: String,
        proof_witness_index: usize,
    },
    /// Aggregate over a named heap collection (the heap/layout rung —
    /// arbitrary-N M-of-N councils, treasury sum-caps, ∀/∃ over collection
    /// data). `pred` is the self-describing aggregate.
    CollectionAggregate {
        collection_id: u32,
        stride: u32,
        fuel: u32,
        pred: CollPredView,
    },
    /// Aggregate over a named collection in the executor-reachable user-field
    /// MAP (`fields_map`) — the executor-writable twin of `CollectionAggregate`
    /// (`_RECORD-LAYER-UPGRADE.md`). Same self-describing aggregate; `base` is
    /// the first user-map key (`>= STATE_SLOTS`) the element run starts at.
    FieldsCollectionAggregate {
        base: u64,
        stride: u32,
        fuel: u32,
        pred: CollPredView,
    },
    /// Witnessed branches under disjunction (§11.3 — the `AnyOfBound` rung).
    /// Admits IFF some branch admits; each [`BoundBranchView`] surfaces whether
    /// it is the cheap no-proof leg or a witnessed cross-cell read naming its
    /// own proof blob.
    AnyOfBound {
        branches: Vec<BoundBranchView>,
    },
    /// `field_to_u64(new[index]) == sym` — the symbol-lane identity equality.
    SymEq {
        index: u8,
        sym: u64,
    },
    /// `field_to_u64(new[index]) ∈ set` — enum membership over the symbol lane.
    SymMemberOf {
        index: u8,
        set: Vec<u64>,
    },
    /// `new[index] == digest` (full 32-byte field) — digest equality. `digest`
    /// is surfaced hex-encoded like every other [`FieldElement`] view.
    DigEq {
        index: u8,
        digest: String,
    },
    /// `new[left_index] == new[right_index]` (full 32-byte fields) — the
    /// digest cross-slot equality (owner-match).
    DigFieldEq {
        left_index: u8,
        right_index: u8,
    },
    /// The actor's clearance label in `new[actor_label_index]` dominates the
    /// compartment label in `new[box_index]` in the graph `edges`, which must
    /// commit to the root stored in `new[root_index]`. Edge labels are lowercase
    /// 64-hex strings.
    ClearanceDominates {
        actor_label_index: u8,
        box_index: u8,
        root_index: u8,
        edges: Vec<(String, String)>,
    },
    /// The sealed-escrow atomic-swap gate: both leg-status slots must read
    /// `Deposited` before and `Consumed` after (the Lean `SettleGate`). Surfaces
    /// the two field-mirrored leg-status slots.
    SettleEscrow {
        leg_a_index: u8,
        leg_b_index: u8,
    },
    /// The standing-obligation per-period discharge gate: the discharge must be due
    /// (height ≥ due slot), the cursor advance by one period, and the total advance
    /// by the schedule amount (the Lean `DischargeGate`). Surfaces the three
    /// field-mirrored schedule slots and the period/amount constants.
    DischargeObligation {
        cursor_slot: u8,
        due_slot: u8,
        amount_slot: u8,
        period: u32,
        amount: u32,
    },
    /// The share-vault no-dilution deposit gate: across the transition the committed
    /// `total_assets` must advance by the deposit, the committed `total_shares` by the
    /// minted count (positive — the inflation tooth), with no existing holder diluted
    /// (the Lean `VaultDepositGate`). Surfaces the two field-mirrored counter slots.
    VaultDeposit {
        assets_slot: u8,
        shares_slot: u8,
    },
    /// Cross-KEY heap relation: `new[heap key] <= new[heap other_key] + delta`
    /// (signed). Surfaces the two heap keys + the signed offset (the heap-keyed
    /// twin of `FieldLteOther`, fail-closed on an absent key).
    HeapFieldLteOther {
        key: u64,
        other_key: u64,
        delta: i64,
    },
}

/// [`BoundBranch`] view (nested in [`StateConstraintView::AnyOfBound`]). The
/// cheap leg projects its inner [`SimpleStateConstraint`] view; the witnessed
/// leg surfaces the cross-cell read it names (peer cell / field / finalized
/// root / proof index, cells & roots as 64-hex).
#[derive(Clone, Debug, PartialEq, Serialize)]
#[serde(tag = "branch")]
pub enum BoundBranchView {
    Simple {
        constraint: Box<StateConstraintView>,
    },
    Witnessed {
        local_field: u8,
        source_cell: String,
        source_field: u8,
        at_root: String,
        proof_witness_index: usize,
    },
}

impl BoundBranch {
    /// Project this `AnyOfBound` branch to its serving view. TOTAL: no wildcard.
    pub fn to_view(&self) -> BoundBranchView {
        match self {
            BoundBranch::Simple(c) => BoundBranchView::Simple {
                constraint: Box::new(c.to_view()),
            },
            BoundBranch::Witnessed {
                local_field,
                source_cell,
                source_field,
                at_root,
                proof_witness_index,
            } => BoundBranchView::Witnessed {
                local_field: *local_field,
                source_cell: view_hex(source_cell),
                source_field: *source_field,
                at_root: view_hex(at_root),
                proof_witness_index: *proof_witness_index,
            },
        }
    }
}

/// [`ElemPredAtom`] view (nested in [`CollPredView`]). 32-byte values are
/// 64-hex strings; u64-lane sets are JSON numbers; `offset` is the
/// element-relative field offset.
#[derive(Clone, Debug, PartialEq, Serialize)]
#[serde(tag = "kind")]
pub enum ElemPredAtomView {
    FieldEquals { offset: u32, value: String },
    FieldGte { offset: u32, value: String },
    FieldLte { offset: u32, value: String },
    FieldInSet { offset: u32, set: Vec<u64> },
}

impl ElemPredAtom {
    /// Project this per-element atom to its serving view. TOTAL.
    pub fn to_view(&self) -> ElemPredAtomView {
        match self {
            ElemPredAtom::FieldEquals { offset, value } => ElemPredAtomView::FieldEquals {
                offset: *offset,
                value: view_hex(value),
            },
            ElemPredAtom::FieldGte { offset, value } => ElemPredAtomView::FieldGte {
                offset: *offset,
                value: view_hex(value),
            },
            ElemPredAtom::FieldLte { offset, value } => ElemPredAtomView::FieldLte {
                offset: *offset,
                value: view_hex(value),
            },
            ElemPredAtom::FieldInSet { offset, set } => ElemPredAtomView::FieldInSet {
                offset: *offset,
                set: set.clone(),
            },
        }
    }
}

/// [`CollPred`] view, nested inside [`StateConstraintView::CollectionAggregate`].
/// The council surfaces its own threshold `m` (the `AffineLe`-projection
/// precedent: a live council shows its quorum).
#[derive(Clone, Debug, PartialEq, Serialize)]
#[serde(tag = "kind")]
pub enum CollPredView {
    CountSatGe {
        m: u32,
        p: ElemPredAtomView,
    },
    SumOfLe {
        offset: u32,
        bound: i64,
    },
    SumOfGe {
        offset: u32,
        bound: i64,
    },
    AllMembers {
        p: ElemPredAtomView,
    },
    ExistsMember {
        p: ElemPredAtomView,
    },
    MOfNDistinct {
        m: u32,
        key_offset: u32,
        approved: ElemPredAtomView,
    },
}

impl CollPred {
    /// Project this aggregate to its serving view. TOTAL.
    pub fn to_view(&self) -> CollPredView {
        match self {
            CollPred::CountSatGe { m, p } => CollPredView::CountSatGe {
                m: *m,
                p: p.to_view(),
            },
            CollPred::SumOfLe { offset, bound } => CollPredView::SumOfLe {
                offset: *offset,
                bound: *bound,
            },
            CollPred::SumOfGe { offset, bound } => CollPredView::SumOfGe {
                offset: *offset,
                bound: *bound,
            },
            CollPred::AllMembers { p } => CollPredView::AllMembers { p: p.to_view() },
            CollPred::ExistsMember { p } => CollPredView::ExistsMember { p: p.to_view() },
            CollPred::MOfNDistinct {
                m,
                key_offset,
                approved,
            } => CollPredView::MOfNDistinct {
                m: *m,
                key_offset: *key_offset,
                approved: approved.to_view(),
            },
        }
    }
}

/// [`HeapAtom`] view, nested inside [`StateConstraintView::HeapField`].
/// 32-byte values are 64-hex strings; u64-lane scalars are JSON numbers.
#[derive(Clone, Debug, PartialEq, Serialize)]
#[serde(tag = "kind")]
pub enum HeapAtomView {
    Equals { value: String },
    Gte { value: String },
    Lte { value: String },
    Immutable,
    WriteOnce,
    Monotonic,
    StrictMonotonic,
    MemberOf { set: Vec<u64> },
    InRangeTwoSided { lo: u64, hi: u64 },
    DeltaBounded { d: u64 },
    DeltaEquals { d: i64 },
}

impl HeapAtom {
    /// Project this heap atom to its serving view. TOTAL: no wildcard arm.
    pub fn to_view(&self) -> HeapAtomView {
        match self {
            HeapAtom::Equals { value } => HeapAtomView::Equals {
                value: view_hex(value),
            },
            HeapAtom::Gte { value } => HeapAtomView::Gte {
                value: view_hex(value),
            },
            HeapAtom::Lte { value } => HeapAtomView::Lte {
                value: view_hex(value),
            },
            HeapAtom::Immutable => HeapAtomView::Immutable,
            HeapAtom::WriteOnce => HeapAtomView::WriteOnce,
            HeapAtom::Monotonic => HeapAtomView::Monotonic,
            HeapAtom::StrictMonotonic => HeapAtomView::StrictMonotonic,
            HeapAtom::MemberOf { set } => HeapAtomView::MemberOf { set: set.clone() },
            HeapAtom::InRangeTwoSided { lo, hi } => {
                HeapAtomView::InRangeTwoSided { lo: *lo, hi: *hi }
            }
            HeapAtom::DeltaBounded { d } => HeapAtomView::DeltaBounded { d: *d },
            HeapAtom::DeltaEquals { d } => HeapAtomView::DeltaEquals { d: *d },
        }
    }
}

impl CellProgram {
    /// Project this program to its serving view. Total over all variants.
    pub fn to_view(&self) -> CellProgramView {
        match self {
            CellProgram::None => CellProgramView::None,
            CellProgram::Predicate(constraints) => CellProgramView::Predicate {
                constraints: constraints.iter().map(StateConstraint::to_view).collect(),
            },
            CellProgram::Cases(cases) => CellProgramView::Cases {
                cases: cases.iter().map(TransitionCase::to_view).collect(),
            },
            CellProgram::Circuit { circuit_hash } => CellProgramView::Circuit {
                circuit_hash: view_hex(circuit_hash),
            },
        }
    }
}

impl TransitionCase {
    /// Project this case to its serving view.
    pub fn to_view(&self) -> TransitionCaseView {
        TransitionCaseView {
            guard: self.guard.to_view(),
            constraints: self
                .constraints
                .iter()
                .map(StateConstraint::to_view)
                .collect(),
        }
    }
}

impl TransitionGuard {
    /// Project this guard to its serving view. Total over all variants.
    pub fn to_view(&self) -> TransitionGuardView {
        match self {
            TransitionGuard::Always => TransitionGuardView::Always,
            TransitionGuard::MethodIs { method } => TransitionGuardView::MethodIs {
                method: view_hex(method),
            },
            TransitionGuard::EffectKindIs { mask } => {
                TransitionGuardView::EffectKindIs { mask: *mask }
            }
            TransitionGuard::SlotChanged { index } => {
                TransitionGuardView::SlotChanged { index: *index }
            }
            TransitionGuard::AnyOf(children) => TransitionGuardView::AnyOf {
                children: children.iter().map(TransitionGuard::to_view).collect(),
            },
            TransitionGuard::AllOf(children) => TransitionGuardView::AllOf {
                children: children.iter().map(TransitionGuard::to_view).collect(),
            },
        }
    }
}

fn authorized_set_view(set: &AuthorizedSet) -> (String, String) {
    match set {
        AuthorizedSet::PublicRoot { set_root_index } => (
            format!("PublicRoot(slot={set_root_index})"),
            "from_slot".to_string(),
        ),
        AuthorizedSet::BlindedSet { commitment } => {
            ("BlindedSet".to_string(), view_hex(commitment))
        }
        AuthorizedSet::CredentialSet {
            issuer_cell,
            credential_schema_id,
        } => (
            "CredentialSet".to_string(),
            format!(
                "issuer={} schema={}",
                &view_hex(issuer_cell)[..8],
                &view_hex(credential_schema_id)[..8]
            ),
        ),
    }
}

fn renounced_set_view(set: &RenouncedSet) -> (String, String) {
    match set {
        RenouncedSet::PublicRoot { set_root_index } => (
            format!("PublicRoot(slot={set_root_index})"),
            "from_slot".to_string(),
        ),
        RenouncedSet::BlindedSet { commitment } => ("BlindedSet".to_string(), view_hex(commitment)),
    }
}

fn witnessed_predicate_kind_view(kind: &crate::predicate::WitnessedPredicateKind) -> String {
    use crate::predicate::WitnessedPredicateKind;
    match kind {
        WitnessedPredicateKind::Dfa => "Dfa".to_string(),
        WitnessedPredicateKind::Temporal => "Temporal".to_string(),
        WitnessedPredicateKind::MerkleMembership => "MerkleMembership".to_string(),
        WitnessedPredicateKind::NonMembership => "NonMembership".to_string(),
        WitnessedPredicateKind::BlindedSet => "BlindedSet".to_string(),
        WitnessedPredicateKind::BridgePredicate => "BridgePredicate".to_string(),
        WitnessedPredicateKind::PedersenEquality => "PedersenEquality".to_string(),
        WitnessedPredicateKind::Custom { vk_hash } => {
            format!("Custom({})", &view_hex(vk_hash)[..8])
        }
    }
}

fn input_ref_view(ir: &crate::predicate::InputRef) -> String {
    use crate::predicate::InputRef;
    match ir {
        InputRef::Slot { index } => format!("Slot({index})"),
        InputRef::Witness { index } => format!("Witness({index})"),
        InputRef::PublicInput { pi_index } => format!("PublicInput({pi_index})"),
        InputRef::Sender => "Sender".to_string(),
        InputRef::SigningMessage => "SigningMessage".to_string(),
    }
}

impl StateConstraint {
    /// Project this constraint to its serving view, carrying the full
    /// semantic payload. TOTAL: no wildcard arm — adding a variant without
    /// a projection breaks the build.
    pub fn to_view(&self) -> StateConstraintView {
        match self {
            StateConstraint::FieldEquals { index, value } => StateConstraintView::FieldEquals {
                index: *index,
                value: view_hex(value),
            },
            StateConstraint::FieldGte { index, value } => StateConstraintView::FieldGte {
                index: *index,
                value: view_hex(value),
            },
            StateConstraint::FieldLte { index, value } => StateConstraintView::FieldLte {
                index: *index,
                value: view_hex(value),
            },
            StateConstraint::FieldLteField {
                left_index,
                right_index,
            } => StateConstraintView::FieldLteField {
                left_index: *left_index,
                right_index: *right_index,
            },
            StateConstraint::FieldLteOther {
                index,
                other,
                delta,
            } => StateConstraintView::FieldLteOther {
                index: *index,
                other: *other,
                delta: *delta,
            },
            StateConstraint::SumEquals { indices, value } => StateConstraintView::SumEquals {
                indices: indices.clone(),
                value: view_hex(value),
            },
            StateConstraint::WriteOnce { index } => {
                StateConstraintView::WriteOnce { index: *index }
            }
            StateConstraint::Immutable { index } => {
                StateConstraintView::Immutable { index: *index }
            }
            StateConstraint::Monotonic { index } => {
                StateConstraintView::Monotonic { index: *index }
            }
            StateConstraint::StrictMonotonic { index } => {
                StateConstraintView::StrictMonotonic { index: *index }
            }
            StateConstraint::BoundedBy {
                index,
                witness_index,
            } => StateConstraintView::BoundedBy {
                index: *index,
                witness_index: *witness_index,
            },
            StateConstraint::FieldDelta { index, delta } => StateConstraintView::FieldDelta {
                index: *index,
                delta: view_hex(delta),
            },
            StateConstraint::FieldDeltaInRange {
                index,
                min_delta,
                max_delta,
            } => StateConstraintView::FieldDeltaInRange {
                index: *index,
                min_delta: view_hex(min_delta),
                max_delta: view_hex(max_delta),
            },
            StateConstraint::FieldGteHeight { index, offset } => {
                StateConstraintView::FieldGteHeight {
                    index: *index,
                    offset: *offset,
                }
            }
            StateConstraint::FieldLteHeight { index, offset } => {
                StateConstraintView::FieldLteHeight {
                    index: *index,
                    offset: *offset,
                }
            }
            StateConstraint::SumEqualsAcross {
                input_fields,
                output_fields,
            } => StateConstraintView::SumEqualsAcross {
                input_fields: input_fields.clone(),
                output_fields: output_fields.clone(),
            },
            StateConstraint::SenderAuthorized { set } => {
                let (set_kind, commitment) = authorized_set_view(set);
                StateConstraintView::SenderAuthorized {
                    set_kind,
                    commitment,
                }
            }
            StateConstraint::CapabilityUniqueness { cap_set_root_slot } => {
                StateConstraintView::CapabilityUniqueness {
                    cap_set_root_slot: *cap_set_root_slot,
                }
            }
            StateConstraint::RateLimit {
                max_per_epoch,
                epoch_duration,
            } => StateConstraintView::RateLimit {
                max_per_epoch: *max_per_epoch,
                epoch_duration: *epoch_duration,
            },
            StateConstraint::RateLimitBySum {
                slot_index,
                max_sum_per_epoch,
                epoch_duration,
            } => StateConstraintView::RateLimitBySum {
                slot_index: *slot_index,
                max_sum_per_epoch: *max_sum_per_epoch,
                epoch_duration: *epoch_duration,
            },
            StateConstraint::TemporalGate {
                not_before,
                not_after,
            } => StateConstraintView::TemporalGate {
                not_before: *not_before,
                not_after: *not_after,
            },
            StateConstraint::RateBound { counter_index, k } => StateConstraintView::RateBound {
                counter_index: *counter_index,
                k: *k,
            },
            StateConstraint::CooledSince { staged_at, period } => {
                StateConstraintView::CooledSince {
                    staged_at: *staged_at,
                    period: *period,
                }
            }
            StateConstraint::UntilEvent { flag_index } => StateConstraintView::UntilEvent {
                flag_index: *flag_index,
            },
            StateConstraint::SinceEvent { flag_index } => StateConstraintView::SinceEvent {
                flag_index: *flag_index,
            },
            StateConstraint::ChallengeWindow {
                challenge_index,
                staged_at,
                period,
            } => StateConstraintView::ChallengeWindow {
                challenge_index: *challenge_index,
                staged_at: *staged_at,
                period: *period,
            },
            StateConstraint::PreimageGate {
                commitment_index,
                hash_kind,
            } => StateConstraintView::PreimageGate {
                commitment_index: *commitment_index,
                hash_kind: match hash_kind {
                    HashKind::Poseidon2 => "Poseidon2".to_string(),
                    HashKind::Blake3 => "Blake3".to_string(),
                },
            },
            StateConstraint::MonotonicSequence { seq_index } => {
                StateConstraintView::MonotonicSequence {
                    seq_index: *seq_index,
                }
            }
            StateConstraint::AllowedTransitions {
                slot_index,
                allowed,
            } => StateConstraintView::AllowedTransitions {
                slot_index: *slot_index,
                allowed: allowed
                    .iter()
                    .map(|(old, new)| (view_hex(old), view_hex(new)))
                    .collect(),
            },
            StateConstraint::TemporalPredicate {
                witness_index,
                dsl_hash,
            } => StateConstraintView::TemporalPredicate {
                witness_index: *witness_index,
                dsl_hash: view_hex(dsl_hash),
            },
            StateConstraint::BoundDelta {
                local_slot,
                peer_cell,
                peer_slot,
                delta_relation,
            } => StateConstraintView::BoundDelta {
                local_slot: *local_slot,
                peer_cell: view_hex(&peer_cell.0),
                peer_slot: *peer_slot,
                delta_relation: format!("{delta_relation:?}"),
            },
            StateConstraint::AnyOf { variants } => StateConstraintView::AnyOf {
                variants: variants
                    .iter()
                    .map(SimpleStateConstraint::to_view)
                    .collect(),
            },
            StateConstraint::Witnessed { wp } => StateConstraintView::Witnessed {
                predicate_kind: witnessed_predicate_kind_view(&wp.kind),
                commitment: view_hex(&wp.commitment),
                input_ref: input_ref_view(&wp.input_ref),
                proof_witness_index: wp.proof_witness_index,
            },
            StateConstraint::Renounced { set } => {
                let (set_kind, commitment) = renounced_set_view(set);
                StateConstraintView::Renounced {
                    set_kind,
                    commitment,
                }
            }
            StateConstraint::MemberOf { index, set } => StateConstraintView::MemberOf {
                index: *index,
                set: set.clone(),
            },
            StateConstraint::PrefixOf {
                seg_indices,
                prefix,
            } => StateConstraintView::PrefixOf {
                seg_indices: seg_indices.clone(),
                prefix: prefix.clone(),
            },
            StateConstraint::InRangeTwoSided { index, lo, hi } => {
                StateConstraintView::InRangeTwoSided {
                    index: *index,
                    lo: *lo,
                    hi: *hi,
                }
            }
            StateConstraint::DeltaBounded { index, d } => StateConstraintView::DeltaBounded {
                index: *index,
                d: *d,
            },
            StateConstraint::AffineLe { terms, c } => StateConstraintView::AffineLe {
                terms: terms.clone(),
                c: *c,
            },
            StateConstraint::AffineEq { terms, c } => StateConstraintView::AffineEq {
                terms: terms.clone(),
                c: *c,
            },
            StateConstraint::Reachable {
                from_index,
                to_label,
                edges,
            } => StateConstraintView::Reachable {
                from_index: *from_index,
                to_label: *to_label,
                edges: edges.clone(),
            },
            StateConstraint::AllOf { variants } => StateConstraintView::AllOf {
                variants: variants
                    .iter()
                    .map(SimpleStateConstraint::to_view)
                    .collect(),
            },
            StateConstraint::Custom {
                ir_hash,
                descriptor,
                reads: _,
            } => StateConstraintView::Custom {
                ir_hash: view_hex(ir_hash),
                descriptor_debug: format!("{descriptor:?}"),
            },
            StateConstraint::SenderIs { pk } => StateConstraintView::SenderIs { pk: view_hex(pk) },
            StateConstraint::SenderInSlot { index } => {
                StateConstraintView::SenderInSlot { index: *index }
            }
            StateConstraint::BalanceGte { min } => StateConstraintView::BalanceGte { min: *min },
            StateConstraint::BalanceLte { max } => StateConstraintView::BalanceLte { max: *max },
            StateConstraint::KeyRotationGate {
                digest_slot,
                current_slot,
                last_rotated_slot,
                cooling_period,
                hash_kind,
            } => StateConstraintView::KeyRotationGate {
                digest_slot: *digest_slot,
                current_slot: *current_slot,
                last_rotated_slot: *last_rotated_slot,
                cooling_period: *cooling_period,
                hash_kind: match hash_kind {
                    HashKind::Poseidon2 => "Poseidon2".to_string(),
                    HashKind::Blake3 => "Blake3".to_string(),
                },
            },
            StateConstraint::HeapField { key, atom } => StateConstraintView::HeapField {
                key: *key,
                atom: atom.to_view(),
            },
            StateConstraint::DelegationEpochEquals { index } => {
                StateConstraintView::DelegationEpochEquals { index: *index }
            }
            StateConstraint::CountGe {
                threshold,
                set_commitment_slot,
            } => StateConstraintView::CountGe {
                threshold: *threshold,
                set_commitment_slot: *set_commitment_slot,
            },
            StateConstraint::SenderMemberOf { members } => StateConstraintView::SenderMemberOf {
                members: members.iter().map(|m| view_hex(m)).collect(),
            },
            StateConstraint::BalanceDeltaLte { max } => {
                StateConstraintView::BalanceDeltaLte { max: *max }
            }
            StateConstraint::BalanceDeltaGte { min } => {
                StateConstraintView::BalanceDeltaGte { min: *min }
            }
            StateConstraint::AffineDeltaLe { terms, c } => StateConstraintView::AffineDeltaLe {
                terms: terms.clone(),
                c: *c,
            },
            StateConstraint::ObservedFieldEquals {
                local_field,
                source_cell,
                source_field,
                at_root,
                proof_witness_index,
            } => StateConstraintView::ObservedFieldEquals {
                local_field: *local_field,
                source_cell: view_hex(source_cell),
                source_field: *source_field,
                at_root: view_hex(at_root),
                proof_witness_index: *proof_witness_index,
            },
            StateConstraint::CollectionAggregate {
                collection_id,
                stride,
                fuel,
                pred,
            } => StateConstraintView::CollectionAggregate {
                collection_id: *collection_id,
                stride: *stride,
                fuel: *fuel,
                pred: pred.to_view(),
            },
            StateConstraint::FieldsCollectionAggregate {
                base,
                stride,
                fuel,
                pred,
            } => StateConstraintView::FieldsCollectionAggregate {
                base: *base,
                stride: *stride,
                fuel: *fuel,
                pred: pred.to_view(),
            },
            StateConstraint::AnyOfBound { branches } => StateConstraintView::AnyOfBound {
                branches: branches.iter().map(|b| b.to_view()).collect(),
            },
            StateConstraint::SymEq { index, sym } => StateConstraintView::SymEq {
                index: *index,
                sym: *sym,
            },
            StateConstraint::SymMemberOf { index, set } => StateConstraintView::SymMemberOf {
                index: *index,
                set: set.clone(),
            },
            StateConstraint::DigEq { index, digest } => StateConstraintView::DigEq {
                index: *index,
                digest: view_hex(digest),
            },
            StateConstraint::DigFieldEq {
                left_index,
                right_index,
            } => StateConstraintView::DigFieldEq {
                left_index: *left_index,
                right_index: *right_index,
            },
            StateConstraint::ClearanceDominates {
                actor_label_index,
                box_index,
                root_index,
                edges,
            } => StateConstraintView::ClearanceDominates {
                actor_label_index: *actor_label_index,
                box_index: *box_index,
                root_index: *root_index,
                edges: edges
                    .iter()
                    .map(|(hi, lo)| (view_hex(hi), view_hex(lo)))
                    .collect(),
            },
            StateConstraint::SettleEscrow {
                leg_a_index,
                leg_b_index,
            } => StateConstraintView::SettleEscrow {
                leg_a_index: *leg_a_index,
                leg_b_index: *leg_b_index,
            },
            StateConstraint::DischargeObligation {
                cursor_slot,
                due_slot,
                amount_slot,
                period,
                amount,
            } => StateConstraintView::DischargeObligation {
                cursor_slot: *cursor_slot,
                due_slot: *due_slot,
                amount_slot: *amount_slot,
                period: *period,
                amount: *amount,
            },
            StateConstraint::VaultDeposit {
                assets_slot,
                shares_slot,
            } => StateConstraintView::VaultDeposit {
                assets_slot: *assets_slot,
                shares_slot: *shares_slot,
            },
            StateConstraint::HeapFieldLteOther {
                key,
                other_key,
                delta,
            } => StateConstraintView::HeapFieldLteOther {
                key: *key,
                other_key: *other_key,
                delta: *delta,
            },
        }
    }
}

impl SimpleStateConstraint {
    /// Project this simple constraint (the `AnyOf`/`AllOf` element type) to
    /// its serving view. TOTAL: no wildcard arm.
    pub fn to_view(&self) -> StateConstraintView {
        match self {
            SimpleStateConstraint::FieldEquals { index, value } => {
                StateConstraintView::FieldEquals {
                    index: *index,
                    value: view_hex(value),
                }
            }
            SimpleStateConstraint::FieldGte { index, value } => StateConstraintView::FieldGte {
                index: *index,
                value: view_hex(value),
            },
            SimpleStateConstraint::FieldLte { index, value } => StateConstraintView::FieldLte {
                index: *index,
                value: view_hex(value),
            },
            SimpleStateConstraint::WriteOnce { index } => {
                StateConstraintView::WriteOnce { index: *index }
            }
            SimpleStateConstraint::Immutable { index } => {
                StateConstraintView::Immutable { index: *index }
            }
            SimpleStateConstraint::Monotonic { index } => {
                StateConstraintView::Monotonic { index: *index }
            }
            SimpleStateConstraint::StrictMonotonic { index } => {
                StateConstraintView::StrictMonotonic { index: *index }
            }
            SimpleStateConstraint::BoundedBy {
                index,
                witness_index,
            } => StateConstraintView::BoundedBy {
                index: *index,
                witness_index: *witness_index,
            },
            SimpleStateConstraint::FieldGteHeight { index, offset } => {
                StateConstraintView::FieldGteHeight {
                    index: *index,
                    offset: *offset,
                }
            }
            SimpleStateConstraint::FieldLteHeight { index, offset } => {
                StateConstraintView::FieldLteHeight {
                    index: *index,
                    offset: *offset,
                }
            }
            SimpleStateConstraint::TemporalGate {
                not_before,
                not_after,
            } => StateConstraintView::TemporalGate {
                not_before: *not_before,
                not_after: *not_after,
            },
            SimpleStateConstraint::Not(inner) => StateConstraintView::Not {
                inner: Box::new(inner.to_view()),
            },
            SimpleStateConstraint::SenderIs { pk } => {
                StateConstraintView::SenderIs { pk: view_hex(pk) }
            }
            SimpleStateConstraint::SenderInSlot { index } => {
                StateConstraintView::SenderInSlot { index: *index }
            }
            SimpleStateConstraint::BalanceGte { min } => {
                StateConstraintView::BalanceGte { min: *min }
            }
            SimpleStateConstraint::BalanceLte { max } => {
                StateConstraintView::BalanceLte { max: *max }
            }
            SimpleStateConstraint::PreimageGate {
                commitment_index,
                hash_kind,
            } => StateConstraintView::PreimageGate {
                commitment_index: *commitment_index,
                hash_kind: match hash_kind {
                    HashKind::Poseidon2 => "Poseidon2".to_string(),
                    HashKind::Blake3 => "Blake3".to_string(),
                },
            },
            SimpleStateConstraint::HeapField { key, atom } => StateConstraintView::HeapField {
                key: *key,
                atom: atom.to_view(),
            },
            SimpleStateConstraint::DelegationEpochEquals { index } => {
                StateConstraintView::DelegationEpochEquals { index: *index }
            }
            SimpleStateConstraint::CountGe {
                threshold,
                set_commitment_slot,
            } => StateConstraintView::CountGe {
                threshold: *threshold,
                set_commitment_slot: *set_commitment_slot,
            },
            SimpleStateConstraint::SenderMemberOf { members } => {
                StateConstraintView::SenderMemberOf {
                    members: members.iter().map(|m| view_hex(m)).collect(),
                }
            }
            SimpleStateConstraint::BalanceDeltaLte { max } => {
                StateConstraintView::BalanceDeltaLte { max: *max }
            }
            SimpleStateConstraint::BalanceDeltaGte { min } => {
                StateConstraintView::BalanceDeltaGte { min: *min }
            }
        }
    }
}

// ============================================================================
// Tests
// ============================================================================
