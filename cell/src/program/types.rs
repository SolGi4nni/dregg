use super::*;

/// A cell program defines valid state transitions.
/// The executor checks the program's constraints on every state-modifying action.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CellProgram {
    /// No program — any authorized state change is valid (current behavior).
    None,

    /// Predicate program: a set of conditions that must hold after transition.
    /// Expressed as a list of constraints over the 16 field slots. All constraints
    /// must hold (implicit conjunction). For disjunction, use
    /// [`StateConstraint::AnyOf`].
    ///
    /// **Legacy shape** (Cav-Codex Block 4). Semantically equivalent to
    /// `Cases(vec![TransitionCase { guard: TransitionGuard::Always,
    /// constraints: <these> }])`. The shape is preserved during the
    /// substrate-correctness migration; new programs should prefer
    /// `Cases { .. }` since it can scope constraints to specific
    /// transitions (e.g. `send` vs `dequeue` on a `CapInbox`).
    Predicate(Vec<StateConstraint>),

    /// Operation-scoped cases (Cav-Codex Block 4). Each
    /// [`TransitionCase`] declares a guard naming which transitions it
    /// applies to and the constraints that must hold on those
    /// transitions. Multiple cases may match a single transition; all
    /// matching cases' constraints AND together.
    ///
    /// If **no** case matches a transition, the program **default-denies**
    /// (the action's effects on this cell are rejected). This means a
    /// `Cases([])` program rejects every transition; to allow arbitrary
    /// transitions add an `Always`-guarded case with no constraints.
    ///
    /// Use cases:
    /// - A `CapInbox` cell with separate cases for `send` (head advances
    ///   by 1, tail unchanged) and `dequeue` (tail advances by 1, head
    ///   unchanged).
    /// - A factory cell that allows mint-style transitions on one method
    ///   and burn-style on another.
    /// - A state-machine cell whose allowed transitions depend on the
    ///   action's method symbol.
    Cases(Vec<TransitionCase>),

    /// Circuit program: an AIR/R1CS circuit that defines the valid state transition function.
    /// The proof in the Action's authorization MUST satisfy this circuit.
    Circuit {
        /// Hash of the circuit (for lookup/verification).
        circuit_hash: [u8; 32],
    },
}

/// A single operation-scoped case in a [`CellProgram::Cases`] program.
///
/// Each case declares a *guard* (what transitions does this case apply
/// to?) and a *constraint list* (when this case applies, all these
/// constraints must hold).
///
/// Per Cav-Codex Block 4: when multiple cases match a single transition,
/// their constraints are ANDed together. When **no** case matches, the
/// program default-denies.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransitionCase {
    /// When does this case apply?
    pub guard: TransitionGuard,
    /// Constraints that must hold when the guard matches.
    pub constraints: Vec<StateConstraint>,
}

/// Guard for a [`TransitionCase`]: names which transitions a case
/// applies to.
///
/// Guards compose via `AnyOf` / `AllOf`. A transition matches a guard
/// when:
/// - `Always` — every transition (legacy `Predicate` shape lowers to
///   this).
/// - `MethodIs { method }` — the action's method symbol equals
///   `method`.
/// - `EffectKindIs { mask }` — at least one effect in the action's
///   effect list has its `effect_kind_mask()` intersecting `mask`.
/// - `SlotChanged { index }` — slot `index` of the cell's state changed
///   on this transition (`new[index] != old[index]`).
/// - `AnyOf` / `AllOf` — boolean composition.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum TransitionGuard {
    /// Always matches; the case's constraints apply to every transition.
    /// Used to lift the legacy `Predicate(...)` shape into a single case.
    Always,
    /// Match when the action's method symbol equals `method` (the
    /// 32-byte BLAKE3 hash of the method name).
    MethodIs { method: [u8; 32] },
    /// Match when the action carries an effect whose
    /// `effect_kind_mask()` intersects `mask` (i.e. at least one effect
    /// is of a kind in the mask).
    EffectKindIs { mask: u32 },
    /// Match when `new_state[index] != old_state[index]` (slot `index`
    /// changed during this transition).
    SlotChanged { index: u8 },
    /// Disjunction — match if any child matches.
    AnyOf(Vec<TransitionGuard>),
    /// Conjunction — match if every child matches.
    AllOf(Vec<TransitionGuard>),
}

/// A single witness payload bound by index inside a [`WitnessBundle`].
///
/// Per Cav-Codex Block 3: identifies a kind-tag plus an opaque byte
/// payload. Concrete shapes live in `dregg_turn::action::WitnessKind /
/// WitnessBlob`; this cell-side mirror exists so the program evaluator
/// can dispatch witnesses without depending on the turn crate.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum WitnessKindTag {
    Preimage32,
    MerklePath,
    RateLimitCount,
    ProofBytes,
    Cleartext,
}

/// A view into an [`crate::Action`]-equivalent witness blob, kept
/// behind a borrowed slice to avoid copies through the evaluator.
#[derive(Clone, Copy, Debug)]
pub struct WitnessBlobView<'a> {
    pub kind: WitnessKindTag,
    pub bytes: &'a [u8],
}

/// A bundle of witness blobs the executor passes alongside the action
/// when evaluating a `CellProgram`.
#[derive(Clone, Copy, Default)]
pub struct WitnessBundle<'a> {
    /// The witness blobs the action carries (indexed).
    pub blobs: &'a [WitnessBlobView<'a>],
    /// Registered verifiers for witnessed-predicate dispatch.
    pub registry: Option<&'a WitnessedPredicateRegistry>,
    /// Host channel resolving a peer cell's FINALIZED field value for the
    /// cross-cell verified-observation atom
    /// ([`StateConstraint::ObservedFieldEquals`]). `None` ⇒ every
    /// `ObservedFieldEquals` fails closed (no channel to the peer's real
    /// finalized roots — the cross-cell self-fabrication forge stays closed,
    /// exactly as a missing [`crate::predicate::IssuerRootAuthority`] rejects
    /// every BlindedSet proof). Appended additively; existing constructions
    /// default it to `None`.
    pub finalized_roots: Option<&'a dyn crate::predicate::FinalizedRootAuthority>,
}

impl<'a> WitnessBundle<'a> {
    pub fn empty() -> Self {
        Self {
            blobs: &[],
            registry: None,
            finalized_roots: None,
        }
    }

    pub fn blob(&self, idx: usize) -> Option<&'a WitnessBlobView<'a>> {
        self.blobs.get(idx)
    }
}

/// Per-transition context evaluated against [`TransitionGuard`]s.
///
/// Built by the executor for each (cell, action) pair before evaluating
/// the cell's `CellProgram`. Holds the action-level signals (method,
/// effect mask, sender) plus the (old, new) state pair from which slot
/// deltas are derived.
#[derive(Clone, Debug)]
pub struct TransitionMeta {
    /// The action's method symbol (BLAKE3 hash of method name).
    pub method: [u8; 32],
    /// Bitwise-OR of every effect's `effect_kind_mask()`.
    pub effects_mask: u32,
    /// The TOUCHED cell's own post-turn `delegation_epoch`
    /// (`CellState::delegation_epoch()` — the R7 capability-freshness
    /// counter, sealed P0-1). Supplied PER CELL by the executor's
    /// program-check loop (`execute_tree.rs`), read by
    /// [`StateConstraint::DelegationEpochEquals`]. `None` (the
    /// `new`/`wildcard` default, and every legacy caller) FAILS CLOSED:
    /// the atom surfaces `MissingContextField`. Lives here rather than
    /// on `EvalContext` because the epoch is per-touched-cell (the meta
    /// is rebuilt per cell in the check loop) while `EvalContext` is
    /// per-action — and `EvalContext` is constructed by struct literal
    /// across many crates (incl. the sp1 guest), so this carrier keeps
    /// the wire-visible context struct untouched.
    pub delegation_epoch: Option<u64>,
}

impl TransitionMeta {
    /// Construct a context with explicit method and effects mask.
    pub fn new(method: [u8; 32], effects_mask: u32) -> Self {
        Self {
            method,
            effects_mask,
            delegation_epoch: None,
        }
    }
    /// A wildcard meta — matches `Always` only; useful for tests.
    pub fn wildcard() -> Self {
        Self {
            method: [0u8; 32],
            effects_mask: 0,
            delegation_epoch: None,
        }
    }
    /// Stamp the touched cell's post-turn `delegation_epoch` onto this
    /// meta (the executor's per-cell program-check loop does this for
    /// every evaluated cell; see [`StateConstraint::DelegationEpochEquals`]).
    pub fn with_delegation_epoch(mut self, epoch: u64) -> Self {
        self.delegation_epoch = Some(epoch);
        self
    }
}

impl TransitionGuard {
    /// Evaluate this guard against a transition.
    pub fn matches(
        &self,
        meta: &TransitionMeta,
        old_state: Option<&CellState>,
        new_state: &CellState,
    ) -> bool {
        match self {
            TransitionGuard::Always => true,
            TransitionGuard::MethodIs { method } => meta.method == *method,
            TransitionGuard::EffectKindIs { mask } => meta.effects_mask & *mask != 0,
            TransitionGuard::SlotChanged { index } => {
                let idx = *index as usize;
                if idx >= STATE_SLOTS {
                    return false;
                }
                match old_state {
                    Some(old) => new_state.fields[idx] != old.fields[idx],
                    None => new_state.fields[idx] != FIELD_ZERO,
                }
            }
            TransitionGuard::AnyOf(children) => children
                .iter()
                .any(|g| g.matches(meta, old_state, new_state)),
            TransitionGuard::AllOf(children) => children
                .iter()
                .all(|g| g.matches(meta, old_state, new_state)),
        }
    }

    /// Returns `true` if this guard discriminates on the action's
    /// *method or effect dispatch* (i.e., is operation-binding rather
    /// than a pure state invariant).
    ///
    /// Cav-Codex Block 4 default-deny: when a `CellProgram::Cases` value
    /// has at least one operation-binding case, the executor must treat
    /// an action whose method matches *none* of them as
    /// `NoTransitionCaseMatched` — even if a separate `Always`-guarded
    /// invariants case still matches. Without this distinction the
    /// `Always` case silently absorbs unknown methods (and only the
    /// invariants get checked), which is exactly the
    /// `unknown_method_default_denied` shape the
    /// `starbridge-subscription` / `starbridge-governed-namespace` /
    /// `dregg-storage-templates::cap_inbox` tests assert against.
    pub fn is_method_dispatching(&self) -> bool {
        match self {
            TransitionGuard::Always => false,
            TransitionGuard::MethodIs { .. } => true,
            TransitionGuard::EffectKindIs { .. } => true,
            TransitionGuard::SlotChanged { .. } => false,
            TransitionGuard::AnyOf(children) | TransitionGuard::AllOf(children) => {
                children.iter().any(|g| g.is_method_dispatching())
            }
        }
    }
}

impl Default for CellProgram {
    fn default() -> Self {
        CellProgram::None
    }
}

/// Cryptographic hash kind used by `PreimageGate`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum HashKind {
    /// BLAKE3 keyed-mode (default for non-circuit commitments).
    Blake3,
    /// Poseidon2 — preferred for in-circuit verification.
    Poseidon2,
}

impl Default for HashKind {
    fn default() -> Self {
        HashKind::Blake3
    }
}

/// Source for `SenderAuthorized`'s sender-set membership check.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AuthorizedSet {
    /// Public Merkle root of authorized sender keys, sourced from slot
    /// `set_root_index`. The witness side carries a Merkle-membership proof.
    PublicRoot { set_root_index: u8 },
    /// Blinded set (per `SLOT-CAVEATS-EVALUATION.md` §4.8): the cell only
    /// knows a Poseidon2 commitment to the membership set. The witness side
    /// carries a non-revocation proof against the commitment.
    BlindedSet { commitment: [u8; 32] },
    /// Cross-app: senders authorized by holding a credential issued from a
    /// known identity-issuer cell against a pinned schema commitment.
    ///
    /// The witness side carries a `ProofBytes` blob whose contents are a
    /// `dregg_credentials::Presentation` (or its proof bytes) that the
    /// registered `WitnessedPredicateKind::BlindedSet` verifier accepts:
    /// the verifier reads the issuer cell's `REVOCATION_ROOT_SLOT` and
    /// `SCHEMA_COMMITMENT_SLOT` out-of-band, confirms the schema commitment
    /// matches `credential_schema_id`, and validates non-revocation
    /// against the issuer's published revocation root. The on-cell
    /// `commitment` baked here is `blake3("dregg-credential-set-v1" ||
    /// issuer_cell || credential_schema_id)` — a stable identifier
    /// derived from the (issuer, schema) pair so two distinct issuer
    /// cells (or two distinct schemas) produce distinct commitments
    /// and a verifier can dispatch deterministically.
    ///
    /// This variant is the substrate primitive that powers
    /// `starbridge-governed-namespace`'s credential-gated voting and
    /// `starbridge-nameservice`'s identity-attested tier — composing
    /// the identity app with namespace + nameservice without inventing
    /// a domain-specific `Effect::PresentCredential` or similar.
    CredentialSet {
        /// The identity-issuer cell ID (the cell whose
        /// `SCHEMA_COMMITMENT_SLOT` and `REVOCATION_ROOT_SLOT` the
        /// verifier reads out-of-band).
        issuer_cell: [u8; 32],
        /// The credential schema commitment the verifier insists matches
        /// the issuer cell's pinned schema. Mirrors
        /// `starbridge_identity::schema_commitment(&schema)`.
        credential_schema_id: [u8; 32],
    },
}

impl AuthorizedSet {
    /// Compute the stable 32-byte commitment under which a
    /// [`AuthorizedSet::CredentialSet`] dispatches to the
    /// `WitnessedPredicateKind::BlindedSet` verifier registered in the
    /// executor's `WitnessedPredicateRegistry`.
    ///
    /// `blake3_derive_key("dregg-credential-set-v1") || issuer_cell ||
    /// credential_schema_id`. Stable across builds; replay-safe across
    /// distinct (issuer, schema) pairs.
    ///
    /// Public so cross-app code (`starbridge-governed-namespace`'s
    /// credential-gated voting, `starbridge-nameservice`'s
    /// identity-attested tier, etc.) can reproduce the value the
    /// executor sees on dispatch without depending on the cell crate's
    /// private hashing routines.
    pub fn credential_set_commitment(
        issuer_cell: &[u8; 32],
        credential_schema_id: &[u8; 32],
    ) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-credential-set-v1");
        hasher.update(issuer_cell);
        hasher.update(credential_schema_id);
        *hasher.finalize().as_bytes()
    }
}

/// Source for [`StateConstraint::Renounced`]'s sender-non-membership
/// check. Mirrors [`AuthorizedSet`] but the predicate is *negative* —
/// the sender's identity must verifiably NOT be in the named sorted
/// leaf set. See `CROSS-CELL-CATEGORICAL-ANALYSIS.md §3.2`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RenouncedSet {
    /// Public Merkle root of the *unheld* sorted leaf set, sourced from
    /// slot `set_root_index`. The action's witness side carries a
    /// non-membership neighbor-witness proof against the root.
    PublicRoot { set_root_index: u8 },
    /// Blinded sorted-set commitment. The witness side carries a
    /// non-membership neighbor-witness against the commitment.
    BlindedSet { commitment: [u8; 32] },
}

/// Delta-relation kind for `BoundDelta` cross-cell binding.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum DeltaRelation {
    /// This cell's slot delta equals the peer's slot delta exactly.
    Equal,
    /// This cell adds, peer subtracts (paired atomic swap / bilateral
    /// conservation).
    EqualAndOpposite,
}

/// Declared read-set for a `Custom` predicate — what slots / context fields
/// the DSL-authored predicate touches. Lets audit tools and (eventually)
/// AIR enforcement reason about a custom predicate's structural footprint
/// without executing it.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReadSet {
    /// Slot indices the predicate reads from `new_state`.
    pub new_slots: Vec<u8>,
    /// Slot indices the predicate reads from `old_state`.
    pub old_slots: Vec<u8>,
    /// Whether the predicate reads `ctx.block_height`.
    pub reads_height: bool,
    /// Whether the predicate reads `ctx.current_epoch`.
    pub reads_epoch: bool,
    /// Whether the predicate reads `ctx.sender`.
    pub reads_sender: bool,
    /// Whether the predicate reads `ctx.revealed_preimage`.
    pub reads_preimage: bool,
}

/// Structured human/version descriptor for `Custom`. Replaces free-form
/// `description: String` per `SLOT-CAVEATS-EVALUATION.md` §5.4(d).
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CustomDescriptor {
    /// Human-readable name, e.g. `"escrow_release_predicate"`.
    pub human_name: String,
    /// Semantic version string, e.g. `"v3.1.0"`.
    pub semver: String,
    /// Authoring package reference, e.g. `"starbridge-apps/escrow"`.
    pub authoring_package: String,
}

/// The index-free heap-atom vocabulary, lifted over a heap key by
/// [`SimpleStateConstraint::HeapField`] / [`StateConstraint::HeapField`].
///
/// THE ROTATION's app-state lane: "registers are the L1; apps live in the
/// heap". The executor already admits heap writes (`SetField` with index
/// `>= STATE_SLOTS` routes into [`CellState::fields_map`], commit
/// `b133354fc`); these atoms let a cell program CONSTRAIN those heap
/// fields. One lifting variant + this small atom enum instead of ~20 heap
/// twins of the slot vocabulary.
///
/// **Lean twin (the semantics — law #1):** `Dregg2.Exec.HeapAtom` +
/// `HeapAtom.lift` + `evalHeap` (`metatheory/Dregg2/Exec/Program.lean`,
/// the "Heap-keyed constraint atoms" section). There the record substrate
/// is already name-keyed and `Option`-valued, so the lift is pure
/// instantiation at the canonical heap field name `heapKey k`
/// (= `FieldsMap.userKey`, welded by `userKey_eq_heapKey`), and every
/// existing admit-characterization transports verbatim
/// (`evalHeap_*_iff`). Here the heap is the `Option`-valued
/// [`CellState::get_field_ext`] read, mirroring `Value.scalar` exactly.
///
/// **Absence semantics (each clause is a THEOREM in the Lean twin, not a
/// comment):** the heap is partial where slots are total —
///
/// * post-state atoms (`Equals`/`Gte`/`Lte`/`MemberOf`/`InRangeTwoSided`)
///   FAIL CLOSED on an absent post-state key (`evalHeap_*_absent_refuses`);
///   on the heap, absent ≠ present-zero (`Equals{value: 0}` REFUSES an
///   absent key, unlike an all-zero slot);
/// * relational atoms (`Monotonic`/`StrictMonotonic`/`DeltaBounded`) FAIL
///   CLOSED on an absent key on EITHER side — there is deliberately NO
///   `(old_state = None, nonce = 0)` init escape on the heap (the slot
///   twins' carve-out does not apply; the Lean record substrate's empty
///   record IS the missing old state);
/// * `Immutable` admits the FIRST write (absent-old,
///   `evalHeap_immutable_absent_old_admits`), then pins the key — flips
///   AND erasure refused (`evalHeap_immutable_pinned` /
///   `_erase_refused`);
/// * `WriteOnce` admits on absent-old or zero-old, then freezes
///   (`evalHeap_writeOnce_absent_admits` / `_zero_admits` / `_frozen`).
///
/// Deliberately NOT recursive: negation/disjunction come from lifting
/// into the existing Heyting fragment —
/// `SimpleStateConstraint::Not(Box::new(HeapField { .. }))`,
/// `AnyOf[HeapField { .. }, SenderIs { .. }]` (the per-HEAP-field actor
/// binding, `heapActorBound_flip_requires_sender` in the Lean twin).
///
/// Numeric lanes mirror the slot twins (`StrictMonotonic` precedent
/// `0c57aac80`): `Equals`/`Gte`/`Lte` compare full [`FieldElement`]s
/// big-endian; `MemberOf`/`InRangeTwoSided`/`DeltaBounded` read the u64
/// lane, exactly like their slot counterparts.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum HeapAtom {
    /// `new[heap key] == value` (absent ⇒ refuse, even for `value == 0`).
    Equals { value: FieldElement },
    /// `new[heap key] >= value` (big-endian; absent ⇒ refuse).
    Gte { value: FieldElement },
    /// `new[heap key] <= value` (big-endian; absent ⇒ refuse).
    Lte { value: FieldElement },
    /// First write free (absent-old admits), then pinned; erasure refused.
    Immutable,
    /// Absent-old or zero-old admits anything; a nonzero old freezes the key.
    WriteOnce,
    /// `old[heap key] <= new[heap key]`, BOTH present (no heap init escape).
    Monotonic,
    /// `old[heap key] < new[heap key]`, both present.
    StrictMonotonic,
    /// `new[heap key] ∈ set` (u64 lane; absent ⇒ refuse).
    MemberOf { set: Vec<u64> },
    /// `lo <= new[heap key] <= hi` (u64 lane; absent ⇒ refuse).
    InRangeTwoSided { lo: u64, hi: u64 },
    /// `|new[heap key] - old[heap key]| <= d` (u64 lane; both present).
    DeltaBounded { d: u64 },
}

/// Simple (non-recursive) constraint set permitted inside `AnyOf`.
///
/// Per `SLOT-CAVEATS-EVALUATION.md` §4.3 we bound `AnyOf` to a single
/// level of disjunction: no nested `AnyOf` and no nested `Custom`. Apps
/// that need deeper composition fall back to a `Custom` predicate that
/// internally evaluates the disjunction.
///
/// # Heyting fragment — `Not`
///
/// Per `CROSS-CELL-CATEGORICAL-ANALYSIS.md` §3.1 + §9.1.1, the predicate
/// algebra is lifted from a *distributive lattice* (conjunction via
/// `Vec`, disjunction via [`StateConstraint::AnyOf`]) to a *Heyting
/// algebra* by admitting a `Not` constructor. The inner is restricted
/// to a non-`Not` `SimpleStateConstraint` so the variant cannot nest
/// without bound (every Heyting-shaped predicate an app needs decomposes
/// into single-level negation + composition under `AnyOf` /
/// `Vec<StateConstraint>`).
///
/// Implication `P ⇒ Q` is derived rather than added as a variant:
/// `Implies(P, Q) == AnyOf(vec![Not(P), Q])`. See
/// [`SimpleStateConstraint::implies`] and
/// [`StateConstraint::implies`].
///
/// **Semantics under failure:** `Not` short-circuits on the *acceptance
/// bit* of the inner constraint. If the inner evaluator surfaces a
/// structural error (`MissingContextField`, `InvalidFieldIndex`,
/// `TransitionCheckRequiresOldState`, etc.) the `Not` evaluator
/// propagates the **error** rather than treating it as a rejection-to-
/// negate. This preserves fail-closed behavior — negating an unevaluable
/// predicate is itself unevaluable, not vacuously satisfied.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SimpleStateConstraint {
    FieldEquals {
        index: u8,
        value: FieldElement,
    },
    FieldGte {
        index: u8,
        value: FieldElement,
    },
    FieldLte {
        index: u8,
        value: FieldElement,
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
    FieldGteHeight {
        index: u8,
        offset: i64,
    },
    FieldLteHeight {
        index: u8,
        offset: i64,
    },
    TemporalGate {
        not_before: Option<u64>,
        not_after: Option<u64>,
    },
    /// Negation — accept iff the inner constraint *rejects*. Per
    /// `CROSS-CELL-CATEGORICAL-ANALYSIS.md` §3.1 / §9.1.1: the missing
    /// initial-object / exponential operator that lifts the predicate
    /// algebra from distributive lattice to Heyting algebra.
    ///
    /// The inner is `Box<SimpleStateConstraint>` (not `StateConstraint`)
    /// so the variant cannot nest into the witness-attached / cross-cell
    /// shapes (`Witnessed`, `BoundDelta`, `Custom`, `TemporalPredicate`).
    /// Apps that need non-membership against a blinded set get it via
    /// the existing `circuit::non_membership` AIR through a `Custom`
    /// predicate; `Not` is the structural surface for the static /
    /// transition / contextual subset.
    ///
    /// **Acceptance:** `inner` evaluates to a structural error → `Not`
    /// surfaces the same error (fail-closed). `inner` evaluates to
    /// `Ok(())` (accept) → `Not` rejects. `inner` evaluates to
    /// `Err(ConstraintViolated)` (reject) → `Not` accepts.
    ///
    /// **Double-negation:** `Not(Not(c))` is *not* representable
    /// because the inner is unboxed `SimpleStateConstraint` (and `Not`
    /// itself is a `SimpleStateConstraint` variant). The plan
    /// deliberately blocks this; double-negation reduces to the original
    /// constraint definitionally and offers no expressive power.
    /// Re-using a wrapper for "obvious tautology" violates the
    /// short-circuit / fail-closed invariants above, so the type system
    /// shapes against it.
    Not(Box<SimpleStateConstraint>),

    // ─── Turn-context atoms (CELL-PROGRAM-LANGUAGE.md §3) ───
    //
    // The executor evaluates every cell program with an `EvalContext`
    // carrying the turn's sender (the acting parent cell's public key)
    // and with the full post-state `CellState` (which carries the
    // cell's own balance). These atoms make that already-plumbed
    // context PROGRAM-READABLE. They live in `SimpleStateConstraint`
    // (not only the outer enum) so they compose under `AnyOf` / `Not`
    // / `Implies` — the per-slot actor binding the polis council needs
    // is literally `AnyOf[Immutable{slot_i}, SenderIs{member_i}]`.
    //
    // NEW VARIANTS ARE APPEND-ONLY: postcard encodes the enum by
    // variant index, so existing serialized programs (and their
    // content addresses) are untouched by these additions.
    /// **Sender binding (literal):** the turn's sender (the acting
    /// cell's public key, from `EvalContext::sender`) must equal `pk`.
    /// Fail-closed: a missing sender (system turn / no context) is
    /// `MissingContextField`, not a pass. Under `AnyOf` with an
    /// `Immutable{slot}` guard this is the per-slot actor binding
    /// (polis gap 5).
    SenderIs {
        pk: [u8; 32],
    },
    /// **Sender binding (slot-held):** the turn's sender must equal the
    /// 32-byte identity stored in `new[index]`. The dynamic-owner
    /// variant of [`Self::SenderIs`]: bind the slot with `Immutable` /
    /// `WriteOnce` and the cell carries its own controller identity.
    SenderInSlot {
        index: u8,
    },
    /// **Own-balance floor:** the cell's post-turn balance (the sealed
    /// `CellState::balance`, NOT one of the 16 slots) must be
    /// `>= min`. Dissolves the "programs can't see their own balance"
    /// gap (blueprint gap 2): solvency floors, fee-reserve guards.
    BalanceGte {
        min: u64,
    },
    /// **Own-balance ceiling:** the cell's post-turn balance must be
    /// `<= max`. `BalanceLte { max: 0 }` under a terminal-state guard
    /// is the "resolve drains the full balance" tooth — program-
    /// enforced, not builder-shape.
    BalanceLte {
        max: u64,
    },
    /// **Composable preimage gate** (blueprint gap 1): identical
    /// semantics to [`StateConstraint::PreimageGate`], admitted here so
    /// the knowledge gate can sit under `AnyOf` / `Implies` — e.g. the
    /// committed-escrow `state == RELEASED ⇒ reveal(preimage of
    /// slot[commitment])`.
    PreimageGate {
        commitment_index: u8,
        hash_kind: HashKind,
    },
    /// **Heap-keyed atom (THE ROTATION's app-state lane):** the lift of
    /// [`HeapAtom`] over heap key `key` (a felt key into
    /// [`CellState::fields_map`]; keys `< STATE_SLOTS` resolve to the
    /// fixed registers under the same encoding). Lives in
    /// `SimpleStateConstraint` so heap constraints compose under
    /// `AnyOf`/`Not` exactly like the Lean lift lands in
    /// `SimpleConstraint`. See [`HeapAtom`] for the full semantics +
    /// Lean theorem names. APPEND-ONLY (postcard variant indices).
    HeapField {
        key: u64,
        atom: HeapAtom,
    },
    /// **Program-readable `delegation_epoch` (the channels closure
    /// lane):** the post-state slot `new[index]` must equal the touched
    /// cell's own post-turn `delegation_epoch` (the R7
    /// capability-freshness counter, [`TransitionMeta::delegation_epoch`],
    /// stamped per cell by the executor's program-check loop). This is
    /// the atom that DISCHARGES the channel-group `DelegationEpochTie`
    /// premise (`metatheory/Dregg2/Apps/ChannelGroup.lean`): with
    /// `DelegationEpochEquals { index: CH_EPOCH_SLOT }` installed, the
    /// group's epoch slot ≡ `delegation_epoch` is PROGRAM-ENFORCED on
    /// every admitted turn — forward-key darkness and R7 capability
    /// staleness are tied IN the program, not only by the canonical
    /// builders' fail-closed checks (which remain as defense-in-depth).
    /// Comparison is full 32-byte (`field_from_u64(epoch)`), not a low-
    /// limb projection. Fail-closed: a meta without the stamp (legacy
    /// `evaluate*` entrypoints, wildcard metas) surfaces
    /// `MissingContextField { field: "delegation_epoch" }`.
    /// Lean twin: `SimpleConstraint.delegationEpochEquals` +
    /// `evalSimpleCtx_delegationEpochEquals_iff`
    /// (`metatheory/Dregg2/Exec/Program.lean`). Lives in
    /// `SimpleStateConstraint` so it composes under `AnyOf`/`Not`.
    /// APPEND-ONLY (postcard variant indices).
    DelegationEpochEquals {
        index: u8,
    },
    /// **Count-≥ / order-statistic atom (in-program M-of-N):** the turn
    /// must EXHIBIT, in its witness blobs (the unique `Cleartext` blob,
    /// postcard `Vec<[u8; 32]>`), a set of at least `threshold` DISTINCT
    /// 32-byte elements whose canonical sorted-set commitment
    /// ([`count_ge_set_commitment`]) equals the commitment held in
    /// `new[set_commitment_slot]`.
    ///
    /// WHY THIS SHAPE (and not the polis `AffineLe`-over-flag-slots
    /// trick, which FAILED on unbounded counters): a sum over flag slots
    /// can be faked by inflating ONE slot to `M`. Here nothing
    /// accumulates in state — the witness RE-EXHIBITS the full element
    /// set on every turn, distinctness is structural (`BTreeSet`), and
    /// the set is bound to the slot commitment, so `M` cannot be
    /// counterfeited by arithmetic aliasing.
    ///
    /// HONEST SCOPE (what the runtime can and cannot discharge today):
    /// the atom discharges "the committed set opens and has ≥ M distinct
    /// elements". It does NOT verify that each element is a live council
    /// member who APPROVED this turn — per-element signatures are not in
    /// the scalar evaluator; the approval binding stays the polis
    /// actor-bound approval-slot ceremony (`AnyOf[Immutable{slot_i},
    /// SenderIs{member_i}]`), whose slots feed the committed set. The
    /// commitment slot itself MUST be governance-written (actor-bound /
    /// admin-gated), else whoever can write the slot mints quorums —
    /// which is why the deployed channel program keeps `SenderIs{admin}`
    /// and the council point ships as a blueprint-test shape
    /// (`council_count_ge_shape` in `blueprint.rs`).
    ///
    /// Fail-closed: missing blob ⇒ `MissingContextField`; ambiguous
    /// (multiple Cleartext blobs) or undecodable blob ⇒
    /// `WitnessedPredicateRejected`; commitment mismatch or
    /// distinct-count < threshold ⇒ `ConstraintViolated`.
    /// Lean twin: `SimpleConstraint.countGe` +
    /// `evalSimpleCtx_countGe_iff` (`metatheory/Dregg2/Exec/Program.lean`).
    /// APPEND-ONLY (postcard variant indices).
    CountGe {
        threshold: u32,
        set_commitment_slot: u8,
    },

    // ─── Turn-context atoms (apps gaps 3/4) — the Lean twins that
    //     LANDED axiom-clean in `metatheory/Dregg2/Exec/Program.lean`
    //     (`senderMemberOf` / `balanceDeltaLe` / `balanceDeltaGe`), their
    //     Rust evaluator arms APPENDED here. APPEND-ONLY: postcard encodes
    //     by variant index, so prior serialized programs / factory VKs /
    //     content addresses are byte-identical. ───
    /// **Sender membership (multi-admin actor binding):** the turn's
    /// sender (the acting cell's public key, from `EvalContext::sender`)
    /// must be one of `members`. The CLEAN form of the
    /// `AnyOf[SenderIs{a}, SenderIs{b}, …]` idiom a multi-admin board
    /// needs — one atom instead of a hand-enumerated disjunction that an
    /// N-member board would have to widen by hand each time a member
    /// joins. Composing it under `AnyOf` with an `Immutable{slot}` guard
    /// gives the multi-admin per-slot binding
    /// (`AnyOf[Immutable{slot}, SenderMemberOf{board}]`: the slot flips
    /// only in a turn sent by SOMEONE on the board), the natural
    /// generalization of the single-key `SenderIs` polis tooth.
    ///
    /// Fail-closed: a missing sender (system turn / no context) surfaces
    /// `MissingContextField { field: "sender" }`, not a pass; a sender
    /// not on the board is `ConstraintViolated`. COST (§8): FREE /
    /// i-confluent — a predicate over the single turn's own context with
    /// no cross-turn invariant (exactly the `SenderIs` classification).
    ///
    /// Lean twin: `SimpleConstraint.senderMemberOf` +
    /// `evalSimpleCtx_senderMemberOf_iff`
    /// (`metatheory/Dregg2/Exec/Program.lean`). Lives in
    /// `SimpleStateConstraint` so it composes under `AnyOf`/`Not`.
    /// APPEND-ONLY (postcard variant indices).
    SenderMemberOf {
        members: Vec<[u8; 32]>,
    },
    /// **Per-turn balance rate ceiling:** the cell's per-turn change in
    /// its OWN sealed kernel balance is at most `max` —
    /// `new.balance − old.balance <= max` (the delta twin of the absolute
    /// [`Self::BalanceLte`]). The pre-turn balance is the executor's
    /// `old_state` (`CellState::balance` BEFORE the effect applied), the
    /// already-plumbed `balanceBefore`; the post is `new_state`. A
    /// withdrawal-rate / spend-cap gate ("this cell may not GAIN more
    /// than `max` per turn"); paired with [`Self::BalanceDeltaGte`] it
    /// bounds per-turn movement in both directions. `max` is SIGNED
    /// (mirrors the Lean `Int` bound): `max < 0` requires the cell to
    /// LOSE at least `−max` each turn.
    ///
    /// Fail-closed: an absent pre-state (no `old_state`, e.g. a legacy
    /// init-only evaluation on a nonzero-nonce cell) surfaces
    /// `TransitionCheckRequiresOldState` (a rate gate cannot be satisfied
    /// without both endpoints). COST (§8): the BOUNDED / ordering pole —
    /// a rate-bound on a DECREMENTABLE quantity (the balance) is the
    /// `bounded_resource_not_iconfluent` case the moment concurrent
    /// debits exist; single-cell serial execution makes it safe today
    /// (n=1 collapses the bound), n>1 forces ordering on the cell. NOT
    /// i-confluent.
    ///
    /// Lean twin: `SimpleConstraint.balanceDeltaLe` +
    /// `evalSimpleCtx_balanceDeltaLe_iff`
    /// (`metatheory/Dregg2/Exec/Program.lean`). Lives in
    /// `SimpleStateConstraint` so it composes under `AnyOf`/`Not`.
    /// APPEND-ONLY (postcard variant indices).
    BalanceDeltaLte {
        max: i64,
    },
    /// **Per-turn balance rate floor:** the cell's per-turn change in its
    /// OWN sealed kernel balance is at least `min` —
    /// `new.balance − old.balance >= min` (the delta twin of the absolute
    /// [`Self::BalanceGte`]). Reads `old_state.balance()` (pre) and
    /// `new_state.balance()` (post). The lower-bound rate gate ("may not
    /// LOSE more than `−min` per turn" when `min < 0`; "must GAIN at
    /// least `min`" when `min > 0`). `min` is SIGNED (mirrors the Lean
    /// `Int` bound).
    ///
    /// Fail-closed: an absent pre-state surfaces
    /// `TransitionCheckRequiresOldState`. COST (§8): the BOUNDED /
    /// ordering pole, same as [`Self::BalanceDeltaLte`] — i-confluent
    /// only under the single serializer (n=1). NOT i-confluent.
    ///
    /// Lean twin: `SimpleConstraint.balanceDeltaGe` +
    /// `evalSimpleCtx_balanceDeltaGe_iff`
    /// (`metatheory/Dregg2/Exec/Program.lean`). Lives in
    /// `SimpleStateConstraint` so it composes under `AnyOf`/`Not`.
    /// APPEND-ONLY (postcard variant indices).
    BalanceDeltaGte {
        min: i64,
    },
}

impl SimpleStateConstraint {
    /// Sugar: build `Implies(self, consequent)` as `AnyOf(Not(self),
    /// consequent)`. Per `CROSS-CELL-CATEGORICAL-ANALYSIS.md` §3.1 the
    /// Heyting implication is derived rather than added as a new
    /// variant; this helper yields the canonical encoding so authors
    /// don't open-code it (and so the evaluator stays simple).
    ///
    /// Returns a `StateConstraint::AnyOf { variants }` rather than a
    /// `SimpleStateConstraint` because the conventional flattening
    /// lives at the outer enum (it composes naturally with the rest of
    /// the slot caveat list).
    pub fn implies(self, consequent: SimpleStateConstraint) -> StateConstraint {
        StateConstraint::AnyOf {
            variants: vec![SimpleStateConstraint::Not(Box::new(self)), consequent],
        }
    }
}

impl StateConstraint {
    /// Sugar: `P ⇒ Q == AnyOf(Not(P), Q)` lifted into the outer enum.
    ///
    /// Restricts both sides to [`SimpleStateConstraint`] so the
    /// derived encoding nests inside the existing `AnyOf` shape (which
    /// per `SLOT-CAVEATS-EVALUATION.md` §4.3 only accepts simples).
    /// Apps wanting implication over witnessed / cross-cell predicates
    /// must go through a `Custom` predicate.
    pub fn implies(antecedent: SimpleStateConstraint, consequent: SimpleStateConstraint) -> Self {
        antecedent.implies(consequent)
    }
}

/// A constraint on cell state (for Predicate programs).
///
/// **21 variants total** per `SLOT-CAVEATS-EVALUATION.md` §7.6:
/// - 4 static post-state: `FieldEquals`, `FieldGte`, `FieldLte`, `SumEquals`
/// - 2 cross-slot post-state: `FieldLteField`, `FieldLteOther`
/// - 3 immutability/once: `Immutable`, `WriteOnce`, `StrictMonotonic`
/// - 3 transition: `Monotonic`, `FieldDelta`, `FieldDeltaInRange`
/// - 2 height-bound: `FieldGteHeight`, `FieldLteHeight`
/// - 1 cross-slot witness: `BoundedBy`
/// - 1 conservation (intra-cell): `SumEqualsAcross`
/// - 2 sender-bound: `SenderAuthorized`, `CapabilityUniqueness`
/// - 2 rate/temporal: `RateLimit`, `RateLimitBySum`, `TemporalGate`
/// - 1 preimage: `PreimageGate`
/// - 1 pre-rotation: `KeyRotationGate` (preimage exhibit against the OLD
///   digest register + install + fresh re-commit + cooling — the identity
///   rider, `metatheory/Dregg2/Apps/PreRotation.lean`)
/// - 1 sequence: `MonotonicSequence`
/// - 1 state-machine: `AllowedTransitions`
/// - 1 witness-attached: `TemporalPredicate`
/// - 1 cross-cell: `BoundDelta`
/// - 1 composition: `AnyOf`
/// - 1 escape: `Custom`
///
/// ### Replay semantics (eval finding 3)
///
/// For `SenderAuthorized` (with a slot-held Merkle root) and
/// `FieldGteHeight` / `FieldLteHeight`, the constraint depends on
/// **external state** (the set root, the current height). To keep
/// `WitnessedReceipt` scope-2 replay deterministic, the executor
/// **snapshots** the relevant external state at *receipt-time* and
/// carries it on the receipt. Replays re-evaluate against the snapshotted
/// state, **not** against the replayer's current chain view. The
/// `EvalContext` passed at replay time should be reconstructed from the
/// receipt, not from the replayer's live ledger.
/// A single branch of an [`StateConstraint::AnyOfBound`] disjunction
/// (`docs/CELL-PROGRAM-LANGUAGE.md` §11.3). The branch shape that lets a
/// WITNESSED (proof-bearing) leaf sit beside a CHEAP (no-proof) leaf under
/// `⊔` WITHOUT the proof-stripping unsoundness §4 warns of: each witnessed
/// branch names its OWN proof carrier (`proof_witness_index`), so "this
/// branch needs a proof" is STRUCTURAL, and a stripped/absent proof makes
/// that branch FAIL (it cannot masquerade as a no-proof branch — the
/// anti-strip tooth).
///
/// Lean twin (LAW #1, the source of truth): `Dregg2.Exec.BoundBranch`
/// (`metatheory/Dregg2/Exec/Program.lean`), whose `witnessed` arm IS the
/// `observedFieldEquals` cross-cell read. The Rust evaluator never authors
/// new semantics — each arm CALLS the evaluator the executor already owns
/// (`evaluate_simple_constraint` for the cheap leg; the existing
/// `ObservedFieldEquals` verification for the witnessed leg).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum BoundBranch {
    /// The cheap, no-proof leg: a plain [`SimpleStateConstraint`] (a timeout,
    /// a state guard, a sender binding). Evaluated by the EXISTING
    /// [`evaluate_simple_constraint`]. THIS is the "cheaper branch" §4 says a
    /// submitter would try to slide down by stripping a proof. Lean twin
    /// `BoundBranch.simple`.
    Simple(SimpleStateConstraint),
    /// The proof-bearing leg: the cross-cell verified-observation read — admits
    /// IFF the host [`crate::predicate::FinalizedRootAuthority`] opens a
    /// genuinely-FINALIZED `source_field` on peer `source_cell` at `at_root` to
    /// a value `v` AND `new[local_field] == v`. The SAME proven
    /// [`StateConstraint::ObservedFieldEquals`] semantics, now as a disjunction
    /// branch: the witnessed branch names its OWN Merkle-open proof blob via
    /// `proof_witness_index` (the audit-item-4 binding stays — a stripped proof
    /// CLOSES this branch). Lean twin `BoundBranch.witnessed localField
    /// sourceCell sourceField`; the anti-strip tooth
    /// `anyOfBound_stripped_proof_branch_fails` reduces to
    /// `evalConstraintCtx_observedFieldEquals_absent_proof_refuses`.
    Witnessed {
        local_field: u8,
        source_cell: [u8; 32],
        source_field: u8,
        at_root: [u8; 32],
        proof_witness_index: usize,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum StateConstraint {
    // ─── Static post-state predicates (existing) ───
    /// Field at index must equal value.
    FieldEquals { index: u8, value: FieldElement },
    /// Field at index must be >= value (unsigned big-endian comparison).
    FieldGte { index: u8, value: FieldElement },
    /// Field at index must be <= value (unsigned big-endian comparison).
    FieldLte { index: u8, value: FieldElement },
    /// Field at `left_index` must be <= field at `right_index` in the same
    /// post-state. Queue-like programs use this to enforce tail <= head.
    FieldLteField { left_index: u8, right_index: u8 },
    /// Field at `index` must be `<= field at `other` + delta` in the same
    /// post-state (`new[index] <= new[other] + delta`, signed). The
    /// `+delta` generalization of [`Self::FieldLteField`]: the queue /
    /// inbox / pubsub *capacity* and *no-underflow* cross-slot bounds.
    ///
    /// - `FieldLteOther { index: head, other: cap, delta: tail }` ≡ the
    ///   CAPACITY bound `head − tail ≤ cap`.
    /// - `FieldLteOther { index: tail, other: head, delta: 0 }` ≡ the
    ///   NO-UNDERFLOW bound `tail ≤ head`.
    ///
    /// Slots read as big-endian u64 lifted to i128, with `delta` added on
    /// the right (so a negative `delta` tightens the bound). Mirrors the
    /// verified Lean atom `Dregg2.Exec.RelationalCaveat.RelCaveat.fieldLteOther`.
    FieldLteOther { index: u8, other: u8, delta: i64 },
    /// Sum of fields at indices must equal value (intra-cell conservation).
    /// Fields are interpreted as big-endian u64 in the last 8 bytes.
    SumEquals {
        indices: Vec<u8>,
        value: FieldElement,
    },

    // ─── Transition predicates over (old, new) ───
    /// Slot must transition only from `FIELD_ZERO` to any non-zero value;
    /// after the first write, the slot is frozen. Generalizes `Immutable`
    /// for the common "register once, then read-only" pattern.
    WriteOnce { index: u8 },

    /// Slot value is read-only after initialization. `new[i] == old[i]`
    /// for any non-fresh cell; on init (nonce==0, old_state==None) the
    /// first write is permitted.
    Immutable { index: u8 },

    /// `new[i] >= old[i]` (unsigned big-endian). Covers expiry extensions,
    /// nullifier-root growth, append-only counters.
    Monotonic { index: u8 },

    /// `new[i] > old[i]` strictly. Auction bids, strictly-increasing
    /// sequence numbers. Added per eval §4 finding 2.
    StrictMonotonic { index: u8 },

    /// `slot[index]` may only be set (i.e. transition non-trivially) if
    /// `slot[witness_index]` is non-zero. Composable see-then-set.
    BoundedBy { index: u8, witness_index: u8 },

    /// `new[index] == old[index] + delta` (modular field arithmetic).
    ///
    /// **Note**: for decrements, encode `delta` as the additive-inverse in
    /// the field (e.g. for a u64 decrement of N, pick `delta` such that
    /// `u64_lo(old) + delta == u64_lo(old) - N` mod 2^64). See
    /// `SLOT-CAVEATS-EVALUATION.md` §8 open question 6.
    FieldDelta { index: u8, delta: FieldElement },

    /// `new[index] in [old[index] + min_delta, old[index] + max_delta]`.
    /// Anti-sniping deadline extensions, bounded growth.
    FieldDeltaInRange {
        index: u8,
        min_delta: FieldElement,
        max_delta: FieldElement,
    },

    /// `new[index] >= ctx.block_height + offset`. Replay-stable when the
    /// receipt carries the snapshot of the height at receipt-time.
    FieldGteHeight { index: u8, offset: i64 },

    /// `new[index] <= ctx.block_height + offset`. Replay-stable as above.
    FieldLteHeight { index: u8, offset: i64 },

    /// Intra-cell conservation across the transition:
    /// `sum(new[input_fields]) == sum(old[input_fields]) + sum(new[output_fields])`.
    /// Per eval finding 4: this is **intra-cell only**. Cross-cell
    /// conservation lives in [`StateConstraint::BoundDelta`].
    SumEqualsAcross {
        input_fields: Vec<u8>,
        output_fields: Vec<u8>,
    },

    // ─── Sender-bound predicates (use EvalContext) ───
    /// The turn's sender must be in an authorized set. The set may be
    /// published as a Merkle root sourced from a slot
    /// ([`AuthorizedSet::PublicRoot`]) or as a Poseidon2 blinded commitment
    /// ([`AuthorizedSet::BlindedSet`]).
    SenderAuthorized { set: AuthorizedSet },

    /// `slot[cap_set_root_slot]` is a per-cell capability-set root and
    /// must encode at most one live capability of the named kind.
    /// NFT-shape "exactly one owner cap" enforcement. Per eval §7.2 #5.
    /// Executor-side enforcement is a structural check on the cap-set
    /// root commitment; the variant exists so the constraint declaration
    /// is first-class.
    CapabilityUniqueness { cap_set_root_slot: u8 },

    // ─── Rate / temporal predicates ───
    /// Sender may mutate this cell at most `max_per_epoch` times per
    /// `epoch_duration` blocks. Backed by an executor-side counter keyed
    /// on `(cell, sender, epoch)`.
    RateLimit {
        max_per_epoch: u32,
        epoch_duration: u64,
    },

    /// Sum-based rate limit: the *value* added to `slot_index` over a
    /// window of `epoch_duration` blocks cannot exceed `max_sum_per_epoch`.
    /// Per eval §4.5 (renamed from `WindowedSum`). Backed by an
    /// executor-side per-(cell, slot, window) running sum.
    RateLimitBySum {
        slot_index: u8,
        max_sum_per_epoch: u64,
        epoch_duration: u64,
    },

    /// Mutation is rejected unless `ctx.block_height` is in
    /// `[not_before, not_after]`. Auction commit/reveal windows.
    TemporalGate {
        not_before: Option<u64>,
        not_after: Option<u64>,
    },

    // ─── Register-reading temporal atoms (the proven-but-was-unwired
    //     `TemporalAlgebra` family, now deployable). Each mirrors a
    //     `#assert_axioms`-clean Lean atom whose soundness is discharged by
    //     `temporalStateStepGuarded` / `temporalAtomsAdmit`
    //     (`metatheory/Dregg2/Authority/TemporalAlgebra{,2}.lean`). They read
    //     the COMMITTED PRE-state register the way the Lean atoms read the
    //     target cell's pre-state record (absent register ⇒ `FIELD_ZERO` ⇒ 0).
    //     See `docs/deos/TEMPORAL-LOGIC-STATUS.md` §3. ───
    /// **"stayed under k":** admit iff the cell's committed PRE-state
    /// admission COUNTER register `new`/`old[counter_index]` reads `< k`. The
    /// running-rate gate — at most `k` admissions per window (the program bumps
    /// the counter on each admission and rotates it at window boundaries, e.g.
    /// a [`Self::MonotonicSequence`] caveat on the counter slot). Mirrors Lean
    /// `TemporalAtom.rateBound`. Reads the OLD register (one-cell pre-state
    /// read; the bound is exact within the cell's serialized history).
    RateBound { counter_index: u8, k: u64 },

    /// **"only after it cooled":** admit iff `staged_at + period <=
    /// ctx.block_height` — the staged object (amendment, recovery, parameter
    /// change) has COOLED for at least `period` since it was staged at
    /// `staged_at`. THE polis cooling primitive, generalized. Height-only:
    /// definitionally `afterHeight (staged_at + period)`, lowered to a
    /// one-sided [`Self::TemporalGate`] for the AIR. Mirrors Lean
    /// `TemporalAtom.cooledSince` (`cooledSince_eq_afterHeight`).
    CooledSince { staged_at: u64, period: u64 },

    /// **"P until Y":** admit WHILE the event register `[flag_index]` reads `0`
    /// (the event has not happened) — the temporal **U** operator over history
    /// ("bids are admitted UNTIL the auction closes"). Reads the OLD register
    /// (absent ⇒ 0 ⇒ admits). Exact complement of [`Self::SinceEvent`]. Mirrors
    /// Lean `EventAtom.untilEvent` (`until_holds_EU_flip`: U is the in-tree lfp
    /// `EU`).
    UntilEvent { flag_index: u8 },

    /// **"since the event":** admit only ONCE the event register `[flag_index]`
    /// is set (`≠ 0`) — the temporal **S** operator ("payout is admitted only
    /// SINCE the auction closed"). Reads the OLD register (absent ⇒ 0 ⇒
    /// refuses, fail-closed). Mirrors Lean `EventAtom.sinceEvent`
    /// (`sinceEvent_iff_AG`: once set, set on every future).
    SinceEvent { flag_index: u8 },

    /// **The optimistic-rollup / fraud-proof settlement gate:** admit iff the
    /// challenge window has ELAPSED (`staged_at + period <= ctx.block_height`)
    /// AND no challenge has been filed (the challenge register `[challenge_index]`
    /// reads `0`). Anyone may file a challenge during the window (a write
    /// setting the register non-zero); settlement is admissible only after a
    /// challenge-free window. Reads the OLD challenge register (absent ⇒ 0).
    /// Mirrors Lean `TemporalAtom.challengeWindow`.
    ChallengeWindow {
        challenge_index: u8,
        staged_at: u64,
        period: u64,
    },

    /// The action must reveal a preimage whose hash equals
    /// `slot[commitment_index]`. `hash_kind` selects Poseidon2 vs BLAKE3.
    PreimageGate {
        commitment_index: u8,
        hash_kind: HashKind,
    },

    /// `slot[seq_index] == old[seq_index] + 1`. Replay-safe sequencing.
    MonotonicSequence { seq_index: u8 },

    // ─── State-machine / witness-attached / cross-cell ───
    /// `(old[slot_index], new[slot_index])` must appear in the explicit
    /// allow-list `allowed`. Encodes a bounded state machine (Open →
    /// Claimed → Delivered → Paid, etc.). Per eval §7.1 #1.
    AllowedTransitions {
        slot_index: u8,
        /// Allowed `(old_value, new_value)` pairs.
        allowed: Vec<(FieldElement, FieldElement)>,
    },

    /// Witness-attached temporal-predicate proof. The action must carry a
    /// `TemporalPredicateProof` whose verifying key is referenced by
    /// `dsl_hash` and whose witness slot is `witness_index`. Per eval
    /// §1.3 + §7.2 #4. The executor invokes
    /// `circuit::temporal_predicate_dsl::verify_temporal_predicate` against
    /// the attached witness; this variant only *declares* the requirement.
    TemporalPredicate {
        witness_index: u8,
        dsl_hash: [u8; 32],
    },

    /// Cross-cell binding pair to γ.2: this cell's `local_slot` delta must
    /// match `peer_cell`'s `peer_slot` delta under the named
    /// [`DeltaRelation`]. The aggregate γ.2 match loop verifies the
    /// bilateral identity; this variant declares the per-cell half. Per
    /// eval §3.5 + §7.1 #3.
    BoundDelta {
        local_slot: u8,
        peer_cell: crate::id::CellId,
        peer_slot: u8,
        delta_relation: DeltaRelation,
    },

    /// Single-level disjunction: at least one of `variants` must hold.
    /// `variants` is restricted to [`SimpleStateConstraint`] (no nested
    /// `AnyOf`, no `Custom`). Per eval §4.3.
    AnyOf {
        variants: Vec<SimpleStateConstraint>,
    },

    // ─── Witness-attached unification (PREDICATE-INVENTORY §3) ───
    /// A witness-attached predicate (DFA classification, temporal-DSL
    /// proof, blinded-set non-revocation, bridge predicate, custom
    /// AIR…). Per PREDICATE-INVENTORY §3 / §7, this is the unified
    /// shape that subsumes the typed
    /// [`StateConstraint::TemporalPredicate`] variant (which is kept
    /// as a typed convenience but is structurally a `Witnessed { wp:
    /// WitnessedPredicate { kind: Temporal, … } }`).
    ///
    /// The executor evaluates by:
    /// 1. Resolving `wp.input_ref` against the cell state / action
    ///    witness / sender pk.
    /// 2. Reading the proof bytes from
    ///    `action.witness_blobs[wp.proof_witness_index]`.
    /// 3. Calling the registry's verifier for `wp.kind`.
    ///
    /// Replay: per PREDICATE-INVENTORY §6.3, the receipt snapshots the
    /// commitment at receipt-time so scope-2 replay is deterministic.
    Witnessed { wp: WitnessedPredicate },

    /// **Categorical dual of [`Self::SenderAuthorized`]: proof of
    /// non-holding / non-membership.** A *renunciation* slot caveat —
    /// the action's sender must verifiably *NOT* be in the
    /// `set`'s sorted Merkle leaf set. Implemented as a typed shim
    /// that dispatches through the
    /// [`crate::predicate::WitnessedPredicateKind::NonMembership`]
    /// verifier in the registry, using the sender pk as the candidate
    /// input and the commitment carried in `set`.
    ///
    /// Per `CROSS-CELL-CATEGORICAL-ANALYSIS.md §3.2 / §9.2.1`:
    /// `Renunciation` is the initial-object dual of `Authorization`.
    /// `SenderAuthorized` says "I prove I have authority"; `Renounced`
    /// says "I prove I lack authority over THIS set." App drivers:
    /// *governance recusal* ("I attest I do not hold a conflicting-
    /// interest cap before voting"), *compliance attestation* ("the
    /// sender is not on the blacklist"), *revocation lookups* (the
    /// sender's identity is not in the revocation set), *selective
    /// non-disclosure* ("the sender is not in the under-18 set").
    ///
    /// The variant exists as a structurally separate slot caveat from
    /// `Witnessed { wp: WitnessedPredicate { kind: NonMembership, … } }`
    /// so audit tooling can clearly distinguish "this cell requires
    /// the sender to *be* in a set" (positive auth) from "this cell
    /// requires the sender to *not* be in a set" (renunciation). The
    /// underlying gadget is shared.
    ///
    /// Replay: like `SenderAuthorized`, replay is deterministic once
    /// the commitment (or its slot snapshot) is carried in the receipt.
    Renounced {
        /// The sorted-set commitment the sender must *not* be in.
        /// Either a slot-borne public root or a fixed blinded
        /// commitment (mirrors [`AuthorizedSet`]).
        set: RenouncedSet,
    },

    // ─── Policy-combinator core (the orthogonal atom set mirrored from
    //     the Lean `Exec.Program` algebra, `metatheory/Dregg2/Exec/Program.lean`).
    //     These close the value-set / structure / arithmetic / DAG gaps the
    //     legacy catalog could not express; fields read as big-endian u64. ───
    /// **Value allowlist:** `new[index]` must be one of `set` (the one-sided
    /// value membership the pair-table `AllowedTransitions` cannot express).
    /// Mirrors Lean `SimpleConstraint.memberOf`. Fields compared as big-endian u64.
    MemberOf { index: u8, set: Vec<u64> },

    /// **Namespace / path prefix containment:** the ordered scalar path read from
    /// `seg_indices` (each a slot read as big-endian u64) must START WITH `prefix`.
    /// The canonical nameservice "register a subdomain only under an owned
    /// namespace" policy. Mirrors Lean `SimpleConstraint.prefixOf`. Fail-closed:
    /// a path shorter than `prefix` is rejected.
    PrefixOf {
        seg_indices: Vec<u8>,
        prefix: Vec<u64>,
    },

    /// **Two-sided absolute band:** `lo <= new[index] <= hi` (the ABSOLUTE
    /// counterpart to the RELATIVE `FieldDeltaInRange`). Mirrors Lean
    /// `SimpleConstraint.inRangeTwoSided`. Fields compared as big-endian u64.
    InRangeTwoSided { index: u8, lo: u64, hi: u64 },

    /// **Real two-sided delta:** `|new[index] - old[index]| <= d` (symmetric;
    /// the legacy delta variants are one-sided or relative-range). Mirrors Lean
    /// `SimpleConstraint.deltaBounded`. Requires old state (transition predicate).
    DeltaBounded { index: u8, d: u64 },

    /// **Affine inequality:** `Σ kᵢ·new[fᵢ] <= c` over named slots
    /// (`terms : Vec<(i64 coefficient, u8 slot)>`). The general multi-field
    /// arithmetic relation; subsumes `FieldLteField` and gives price-band /
    /// `a+b <= c` invariants. Mirrors Lean `StateConstraint.affineLe`. Maps to a
    /// PLONK linear gate. Slots read as big-endian u64, lifted to i128 for the sum.
    AffineLe { terms: Vec<(i64, u8)>, c: i64 },

    /// **Affine equation:** `Σ kᵢ·new[fᵢ] = c`. Subsumes `SumEquals` and
    /// re-expresses conservation. Mirrors Lean `StateConstraint.affineEq`.
    AffineEq { terms: Vec<(i64, u8)>, c: i64 },

    /// **DAG reachability / prerequisite:** the label read from `new[from_index]`
    /// must reach `to_label` in the reachability `edges` (reflexive-transitive
    /// closure). The workflow-prerequisite predicate (CWM advance / SGM admit).
    /// Mirrors Lean `StateConstraint.reachable` (the `ClearanceGraph.dominatesD`
    /// fuel-bounded search). `edges : Vec<(u64, u64)>` are `(dominator, dominated)`.
    Reachable {
        from_index: u8,
        to_label: u64,
        edges: Vec<(u64, u64)>,
    },

    /// **n-ary conjunction** over `SimpleStateConstraint`s — the `allOf` the
    /// legacy 2-level grammar lacked (it had only single-level `AnyOf`). Mirrors
    /// the Lean `Pred.allOf` Boolean layer. Empty `AllOf` admits (vacuous AND).
    AllOf {
        variants: Vec<SimpleStateConstraint>,
    },

    // ─── Escape hatch ───
    /// DSL-authored predicate. The executor evaluates by hash lookup in
    /// the dregg-dsl runtime expression table. Per eval §5.4 the variant
    /// carries a declared `reads` set (what slots/ctx fields the
    /// predicate touches) and a structured `descriptor`.
    Custom {
        /// Hash of the canonical DSL IR.
        ir_hash: [u8; 32],
        /// Structured human/version descriptor.
        descriptor: CustomDescriptor,
        /// Declared read-set — what the predicate touches.
        reads: ReadSet,
    },

    // ─── Turn-context atoms (CELL-PROGRAM-LANGUAGE.md §3) — the
    //     top-level lifts of the `SimpleStateConstraint` context atoms.
    //     APPEND-ONLY: postcard variant indices of all prior variants
    //     are preserved. ───
    /// The turn's sender (acting cell's public key) must equal `pk`.
    /// See [`SimpleStateConstraint::SenderIs`].
    SenderIs { pk: [u8; 32] },
    /// The turn's sender must equal the identity held in `new[index]`.
    /// See [`SimpleStateConstraint::SenderInSlot`].
    SenderInSlot { index: u8 },
    /// The cell's own post-turn balance must be `>= min`.
    /// See [`SimpleStateConstraint::BalanceGte`].
    BalanceGte { min: u64 },
    /// The cell's own post-turn balance must be `<= max`.
    /// See [`SimpleStateConstraint::BalanceLte`].
    BalanceLte { max: u64 },

    /// **Pre-rotation gate (KERI-shaped)** — the identity rider
    /// (`docs/ORGANS.md` "Identity rider"; kernel semantics proven in
    /// `metatheory/Dregg2/Apps/PreRotation.lean`, the `rotateWriteCooled`
    /// production shape).
    ///
    /// `digest_slot` is the `next_keys_digest` register: the commitment to
    /// the NEXT, unexposed key set, committed BEFORE exposure.
    /// `current_slot` publishes the installed (current) key-set commitment.
    /// `last_rotated_slot` is the cooling anchor (block height of the last
    /// rotation event).
    ///
    /// Semantics, fail-closed:
    ///
    /// * **No-op turn** — all three slots unchanged: admitted (the gate only
    ///   guards the rotation registers).
    /// * **Inception** — `old[digest_slot] == 0` and the register is being
    ///   written: the FIRST pre-commitment may be installed without a
    ///   preimage (nothing was committed yet — KERI `icp`). The new digest
    ///   must be nonzero; `current_slot` freely declares the birth key-set
    ///   commitment; a nonzero `last_rotated_slot` stamp must not be
    ///   future-dated.
    /// * **Rotation** — `old[digest_slot] != 0` and any of the three slots
    ///   changes (KERI `rot`). Admitted ONLY when:
    ///   1. the action carries a `Preimage32` witness (the presented new
    ///      key-set commitment) with `hash(preimage) == old[digest_slot]`
    ///      — the preimage EXHIBIT against the PRE-state register (Lean
    ///      `rotateWrite_exhibits_preimage`; note this deliberately differs
    ///      from [`StateConstraint::PreimageGate`], which checks the
    ///      POST-state slot and therefore cannot express pre-rotation);
    ///   2. `new[current_slot] == preimage` — the presented set is
    ///      INSTALLED (`rotate_installs`);
    ///   3. `new[digest_slot] != 0` — the fresh next-commitment is written
    ///      in the SAME turn (the forward chain,
    ///      `rotateWrite_commits_fresh` / `rotChain_pinned_by_commitments`);
    ///   4. `old[last_rotated_slot] + cooling_period <= ctx.block_height`
    ///      — the cooling window (Lean `TemporalAtom.cooledSince`;
    ///      `rotateWriteCooled_refuses_inside`);
    ///   5. `new[last_rotated_slot] == ctx.block_height` — the rotation
    ///      stamps its own height (the next window's anchor).
    ///
    /// The guard NEVER reads `old[current_slot]` — the current (exposed,
    /// possibly stolen) keys contribute nothing toward admission. This is
    /// the structural half of compromise resistance, the Rust mirror of the
    /// `rfl` theorem `rotate_current_keys_irrelevant`; under hash collision
    /// resistance any presented set other than the pre-committed one is
    /// refused (`rotate_compromise_resistant` — an admitted forgery would
    /// BE a collision).
    KeyRotationGate {
        /// The `next_keys_digest` register slot.
        digest_slot: u8,
        /// The installed (current) key-set commitment slot.
        current_slot: u8,
        /// The cooling anchor: height of the last rotation event.
        last_rotated_slot: u8,
        /// Blocks a rotation must wait after the previous one (the
        /// recovery cooling window, visible to the council).
        cooling_period: u64,
        /// Hash binding the digest register to its preimage.
        hash_kind: HashKind,
    },

    /// **Heap-keyed atom (THE ROTATION's app-state lane)** — the
    /// top-level lift of [`HeapAtom`] over heap key `key`, the twin of
    /// [`SimpleStateConstraint::HeapField`] (both surfaces share ONE
    /// evaluator arm, like the `SenderIs`/`BalanceGte` precedent).
    /// Constrains the unbounded [`CellState::fields_map`] state the
    /// executor admits via `SetField index >= STATE_SLOTS`
    /// (commit `b133354fc`). Reads are `Option`-valued
    /// ([`CellState::get_field_ext`]) and every absence case is
    /// fail-closed-coherent per the Lean theorems on [`HeapAtom`]'s
    /// docstring. APPEND-ONLY (postcard variant indices).
    HeapField { key: u64, atom: HeapAtom },

    /// `new[index]` must equal the touched cell's post-turn
    /// `delegation_epoch`. Top-level twin of
    /// [`SimpleStateConstraint::DelegationEpochEquals`] (ONE evaluator
    /// arm, the `SenderIs`/`HeapField` precedent). APPEND-ONLY.
    DelegationEpochEquals { index: u8 },

    /// The witness must exhibit ≥ `threshold` distinct elements opening
    /// the commitment in `new[set_commitment_slot]`. Top-level twin of
    /// [`SimpleStateConstraint::CountGe`] (ONE evaluator arm).
    /// APPEND-ONLY.
    CountGe {
        threshold: u32,
        set_commitment_slot: u8,
    },

    // ─── Turn-context atoms (apps gaps 3/4) — top-level twins of the
    //     `SimpleStateConstraint` context atoms + the StateConstraint-only
    //     `AffineDeltaLe`. APPEND-ONLY: postcard variant indices of all
    //     prior variants are preserved (factory VKs / content addresses
    //     byte-identical, CELL-PROGRAM-LANGUAGE §2). ───
    /// The turn's sender must be one of `members`. Top-level twin of
    /// [`SimpleStateConstraint::SenderMemberOf`] (ONE evaluator arm, the
    /// `SenderIs`/`BalanceGte` precedent). APPEND-ONLY.
    SenderMemberOf { members: Vec<[u8; 32]> },

    /// The cell's per-turn balance change is `<= max`. Top-level twin of
    /// [`SimpleStateConstraint::BalanceDeltaLte`] (ONE evaluator arm).
    /// APPEND-ONLY.
    BalanceDeltaLte { max: i64 },

    /// The cell's per-turn balance change is `>= min`. Top-level twin of
    /// [`SimpleStateConstraint::BalanceDeltaGte`] (ONE evaluator arm).
    /// APPEND-ONLY.
    BalanceDeltaGte { min: i64 },

    /// **Multi-field delta gate:** `Σ kᵢ·(new[fᵢ] − old[fᵢ]) <= c` over
    /// named slots (`terms : Vec<(i64 coefficient, u8 slot)>`). The genuine
    /// multi-field rate gate the single-field [`Self::DeltaBounded`] /
    /// [`StateConstraint::FieldDelta`] cannot express: a treasury cell with
    /// two spend slots `out_a`, `out_b` bounds the COMBINED outflow per turn
    /// (`[(1, out_a), (1, out_b)] <= budget` over the deltas), or a weighted
    /// basket `2·Δprice − Δindex <= k`. Distinct from the post-state-only
    /// [`Self::AffineLe`] (a band on the new state) and from
    /// [`StateConstraint::SumEqualsAcross`] (an intra-cell conservation
    /// equation): this is a one-sided affine inequality on the DIFFERENCES.
    /// Maps to a PLONK linear gate over the `(old, new)` wire pair.
    ///
    /// Fail-closed: an absent pre-state (no `old_state`) surfaces
    /// `TransitionCheckRequiresOldState` (the delta is not evaluable
    /// without both sides); a bad slot index is `InvalidFieldIndex`. COST
    /// (§8): the BOUNDED / ordering pole — a bound on per-turn CHANGE of
    /// (generally decrementable) quantities is the
    /// `bounded_resource_not_iconfluent` case under concurrent writers;
    /// single-cell serial execution keeps it safe today (n=1), n>1 forces
    /// ordering. NOT i-confluent.
    ///
    /// Lean twin: `StateConstraint.affineDeltaLe` +
    /// `evalConstraint_affineDeltaLe_iff`
    /// (`metatheory/Dregg2/Exec/Program.lean`). A `StateConstraint`-only
    /// atom (it reads BOTH sides, so it does not lift into the
    /// post-state-local `SimpleStateConstraint` fragment), exactly as in
    /// Lean. APPEND-ONLY.
    AffineDeltaLe { terms: Vec<(i64, u8)>, c: i64 },

    /// **Cross-cell verified observation** (`docs/CELL-PROGRAM-LANGUAGE.md`
    /// §11.2): `new[local_field]` must equal the value `source_field` held by
    /// the PEER cell `source_cell` at the FINALIZED state-commitment root
    /// `at_root`. THE rung that makes a real app natural — a market cell
    /// gating on an oracle cell's finalized price, a governance cell on a
    /// constitution cell's finalized membership ("my threshold IS
    /// constitution v3's threshold, at height H" — live, amendable,
    /// verified, instead of a parameter copied and FROZEN at birth, polis
    /// gap 2 / the §8 `imports` pattern, now a program tooth).
    ///
    /// **This is a verified observation of FINALIZED state, NOT a live
    /// read.** A guard reading the peer's *current* state would make every
    /// turn on this cell order against every turn on that cell (the
    /// `relational_decided_by_merge` arm with a non-local relation —
    /// coordination, always; the same reason [`Self::BoundDelta`] is
    /// deferred), so a live cross-cell read stays OUT of the language. A
    /// **finalized** value is monotone (it never un-finalizes), the
    /// `monotone_terminal` confluence-keeping case, hence FREE — that
    /// distinction is exactly *why* this rung is admissible.
    ///
    /// Witnessed shape (joins the [`crate::predicate::WitnessedPredicate`]
    /// family in spirit — `proof_witness_index` names its Merkle-open proof
    /// blob), deliberately a `StateConstraint`, NOT a
    /// [`SimpleStateConstraint`]: proof-bearing shapes do not survive naive
    /// disjunction (the §4 discipline — an `AnyOf` branch that fails to open
    /// a proof must be distinguishable from one that needs none), so it does
    /// not lift into the composable simple fragment.
    ///
    /// Fail-closed: admits IFF the host
    /// [`crate::predicate::FinalizedRootAuthority`] confirms `at_root` is
    /// `source_cell`'s genuine finalized commitment AND opens `source_field`
    /// in it to a value `v`, AND `new[local_field] == v`. When no authority
    /// is installed (no channel to the peer's real roots) it REJECTS — the
    /// cross-cell self-fabrication forge stays closed exactly as a missing
    /// [`crate::predicate::IssuerRootAuthority`] rejects every BlindedSet
    /// proof; `proof_witness_index` out of range / absent `local_field` /
    /// forged `at_root` all reject. Lean twin:
    /// `StateConstraint.observedFieldEquals` +
    /// `evalConstraintCtx_observedFieldEquals_iff`
    /// (`metatheory/Dregg2/Exec/Program.lean`), reading the
    /// `TurnCtx.observedFields` portal carrier (the opened
    /// `(source_cell, source_field, v)` triples — the host Merkle-open +
    /// root-authenticity check lives in the portal, the ordering law is
    /// proved there). APPEND-ONLY (postcard variant indices preserved —
    /// factory VKs / content addresses byte-identical, §2).
    ObservedFieldEquals {
        local_field: u8,
        source_cell: [u8; 32],
        source_field: u8,
        at_root: [u8; 32],
        proof_witness_index: usize,
    },

    /// **Aggregate-over-a-collection gate** (`docs/CELL-PROGRAM-LANGUAGE.md`
    /// gaps 7/11.1 — the heap/layout rung, the documented "lamesauce"
    /// N≤3 fixed-slot cap *lifted*). Predicates over a NAMED COLLECTION
    /// living in the cell's openable `(collection_id, key) → value` heap
    /// ([`CellState::heap_map`], the sorted-Poseidon2 [`CellState::heap_root`]
    /// — the same `cap_root` collection-commitment home as the channel
    /// membership root). Where [`Self::CountGe`] re-exhibits an external
    /// witnessed SET, this aggregates over the cell's OWN named collection
    /// data, read by name end-to-end.
    ///
    /// A collection is a contiguous run of element records in `heap_map`
    /// under `collection_id`: element `i` occupies the heap stride
    /// `[i*stride .. i*stride + stride)`, and element `i`'s field at offset
    /// `f` is `heap[(collection_id, i*stride + f)]` — the felt realization
    /// of the Lean index-keyed sub-record (`Value.collectionField` reading
    /// `"0"`,`"1"`,… element records, `elemScalar`/`elemSym` reading each
    /// element's fields by name). The collection is the contiguous prefix
    /// whose ANCHOR field (`pred`'s key offset, or offset 0) is present,
    /// truncating at the first absent index (the `readIndexed` fail-closed
    /// truncation: a collection has no phantom tail beyond a gap), bounded
    /// by `fuel` (an upper element count — no element index exceeds it).
    ///
    /// **THE COUNCIL LIFT** rides [`CollPred::MOfNDistinct`]: arbitrary-N
    /// M-of-N over the collection, distinctness-enforced. A naive
    /// `CountSatGe` would be FOOLED by a duplicate-padded forge (the same
    /// approver listed `m` times, raw count `m` from ONE real approval);
    /// `MOfNDistinct` counts DISTINCT identity keys (`BTreeSet` dedup, the
    /// `eraseDups` mirror), so a duplicate-padded forge collapses to ONE
    /// key and REFUSES; an unbound forge (a padding element that does not
    /// satisfy `approved`) is filtered before the count. Both biting teeth.
    ///
    /// Fail-closed: an absent collection (anchor of element 0 not present)
    /// REJECTS (`collectionAggregate_absent_refuses` /
    /// `collectionCouncil_absent_refuses`) — an aggregate over an absent
    /// collection is unevaluable.
    ///
    /// Lean twin (LAW #1, the source of truth):
    /// `Dregg2.Exec.Collections.collectionAggregate` /
    /// `collectionCouncil` + `mOfNDistinct` (the council keystone), proved
    /// `mOfNDistinct_iff` / `mOfNDistinct_le_countSat` (the duplicate-pad
    /// tooth) / `collectionCouncil_iff`
    /// (`metatheory/Dregg2/Exec/Collections.lean`). A `StateConstraint`
    /// (it reads only post-state heap, but is proof/data-bearing over a
    /// committed map — not a post-state-local scalar — so it does not lift
    /// into the composable `SimpleStateConstraint` fragment, like
    /// [`Self::CountGe`]). APPEND-ONLY (postcard variant indices preserved).
    CollectionAggregate {
        /// The `collection_id` lane in the cell's `(collection_id, key)`
        /// heap under which the element run lives.
        collection_id: u32,
        /// The per-element heap-key stride (the element record's width —
        /// how many heap keys one element occupies). Must be `>= 1`.
        stride: u32,
        /// An upper bound on the element count (the `readIndexed` fuel: no
        /// element index is read beyond it). The collection is the
        /// contiguous present prefix, at most `fuel` long.
        fuel: u32,
        /// The aggregate predicate over the read-out collection.
        pred: CollPred,
    },

    /// **Witnessed branches under disjunction** (`docs/CELL-PROGRAM-LANGUAGE.md`
    /// §11.3 — the `AnyOfBound` rung) — admits IFF SOME `branches` element
    /// admits. The rung that lets a real escrow/governance ceremony express
    /// "release if EITHER the timeout passed OR a finalized-read proof
    /// verifies" — a WITNESSED branch beside a CHEAP branch — which the plain
    /// [`Self::AnyOf`] ([`SimpleStateConstraint`]-only) cannot, because
    /// proof-bearing leaves do not survive a naive lift (§4: an `AnyOf` branch
    /// that fails to open a proof must be DISTINGUISHABLE from one that needs
    /// none, or a submitter strips the proof and slides down the cheap branch).
    ///
    /// THE SOUNDNESS CORE: a [`BoundBranch::Witnessed`] branch whose proof is
    /// absent/invalid (no Merkle-open blob at its `proof_witness_index`, or the
    /// host [`crate::predicate::FinalizedRootAuthority`] rejected `at_root`)
    /// does NOT admit. It cannot masquerade as a no-proof branch: the witnessed
    /// branch STRUCTURALLY names its own blob, exactly as the standalone
    /// [`Self::ObservedFieldEquals`] does, and the global unique-blob scan
    /// (audit item 4) stays for the legacy witnessed shapes. A proof-strip
    /// therefore CLOSES the witnessed branch rather than opening a cheaper
    /// path; the only branches a stripped turn can take are the genuinely-cheap
    /// [`BoundBranch::Simple`] ones.
    ///
    /// The evaluator arm CALLS the executor's existing evaluators — the cheap
    /// leg through [`evaluate_simple_constraint`], the witnessed leg through the
    /// same `ObservedFieldEquals` verification — so NO new semantics are
    /// authored (LAW #1). COST (§5/§8): the MAX of the branch costs — a
    /// disjunction is as coordinated as its most-coordinated TAKEN branch (a
    /// cheap `Simple` branch is free; a `Witnessed` finalized-read branch is the
    /// FREE finalized-read class; an ordering-pole simple branch makes the whole
    /// gate ordering when taken); disclosure is the union of what the taken
    /// branch reveals.
    ///
    /// Lean twin (LAW #1, the source of truth — APPENDED last, after the Lean
    /// was green): `Dregg2.Exec.StateConstraint.anyOfBound`
    /// (`metatheory/Dregg2/Exec/Program.lean`), admit-char
    /// `evalConstraint_anyOfBound_iff`, anti-strip tooth
    /// `anyOfBound_stripped_proof_branch_fails`. APPEND-ONLY (postcard variant
    /// indices preserved — factory VKs / content addresses byte-identical, §2).
    AnyOfBound { branches: Vec<BoundBranch> },

    // ─── TYPED dig/sym FIELD ATOMS (the identity / ownership / enum rung,
    //     mirroring the Lean `PredAlgebra` typed atoms `symEq`/`symMemberOf`/
    //     `digEq`/`digFieldEq`, `metatheory/Dregg2/Exec/PredAlgebra.lean`).
    //
    //     THE TYPE-ERASURE SEAM (honest): the Lean `Value` model distinguishes
    //     three leaves — `.int` (a scalar), `.sym` (an interned identity / enum
    //     case), `.dig` (a digest / cell-reference) — and these atoms read a
    //     field BY PROPER TYPE so an ownership-by-digest policy cannot be fooled
    //     by a coincident scalar word. The dregg1 8-slot substrate here has NO
    //     such distinction: every slot is one untyped `FieldElement` ([u8;32]).
    //     So in THIS model a `sym` IS the u64 lane (`field_to_u64`, exactly what
    //     `MemberOf` already reads) and a `dig` IS the full 32-byte field
    //     (exactly what `FieldEquals`/`Immutable` already compare). The typed
    //     atoms therefore carry the Lean atom's INTENT (which leaf the policy
    //     author means) and the lane the read uses; where the lane already
    //     coincides with an existing untyped atom the evaluation is identical
    //     (documented per-variant). The one GENUINELY-NEW capability the untyped
    //     catalog lacked is `DigFieldEq` — a FULL 32-byte cross-slot equality
    //     (owner-match), which `FieldLteField` (a u64-lane ORDERING) cannot
    //     express. APPEND-ONLY (postcard variant indices of all prior variants
    //     preserved — factory VKs / content addresses byte-identical, §2). ───
    /// **`SymEq`** — `field_to_u64(new[index]) == sym`: the field's interned
    /// identity (the u64 lane) equals `sym`. Mirrors Lean `Pred.symEq`. In the
    /// untyped substrate this reads the SAME u64 lane as [`Self::MemberOf`] over a
    /// singleton; it names the SYMBOL intent (an identity / enum case, not an
    /// orderable scalar). Admit-char (Lean): `Pred.symEq_iff`.
    SymEq { index: u8, sym: u64 },

    /// **`SymMemberOf`** — `field_to_u64(new[index]) ∈ set`: enum membership by
    /// the symbol lane ("`status ∈ {Draft, Active, Frozen}`"). Mirrors Lean
    /// `Pred.symMemberOf`. Reads the SAME u64 lane as [`Self::MemberOf`]; the
    /// distinct variant records that the values are interned ENUM CASES (a
    /// symbol set), which is what the toy-gap fix is about — an enum over
    /// identities, not coercible integers. Admit-char (Lean): `Pred.symMemberOf_iff`.
    SymMemberOf { index: u8, set: Vec<u64> },

    /// **`DigEq`** — `new[index] == digest` as a FULL 32-byte field: the field's
    /// digest / cell-reference equals `digest`. Mirrors Lean `Pred.digEq`. In the
    /// untyped substrate this is the full-field compare [`Self::FieldEquals`]
    /// already performs; the distinct variant names the DIGEST intent (a
    /// commitment / cell-ref pinned by its whole hash, not its low word).
    /// Admit-char (Lean): `Pred.digEq_iff`.
    DigEq { index: u8, digest: FieldElement },

    /// **`DigFieldEq`** — `new[left_index] == new[right_index]` as FULL 32-byte
    /// fields: two digest slots are equal. THE owner-match tooth (`DigFieldEq {
    /// left = sender_slot, right = owner_slot }` is "only the owner may act"); a
    /// surrounding [`SimpleStateConstraint::Not`]/disjunction gives the
    /// no-self-transfer "from ≠ to". Mirrors Lean `Pred.digFieldEq`. THIS is the
    /// genuinely-new capability the untyped catalog lacked: [`Self::FieldLteField`]
    /// compares slots as a u64-lane ORDERING (`<=`), never as a full-digest
    /// EQUALITY. Admit-char (Lean): `Pred.digFieldEq_iff`.
    DigFieldEq { left_index: u8, right_index: u8 },

    /// **Clearance-graph dominance (the SGM/CWM mandate tooth, root-bound)** —
    /// admits IFF the actor's clearance label read from `new[actor_label_index]`
    /// (a full 32-byte field label) DOMINATES the required compartment label read
    /// from `new[box_index]` in the dominance graph `edges`, AND that graph's
    /// canonical commitment equals the root stored in `new[root_index]`.
    ///
    /// This is the Rust realization of the Lean `Pred.clearanceGe` /
    /// `stepClearanceOK` admission (`metatheory/Dregg2/Exec/Program.lean`,
    /// `Apps/CompartmentWorkflowMandate/Core.lean`): the dominance walk is the
    /// proved-sound reflexive-transitive closure of `ClearanceGraph.dominatesD`
    /// (`Authority/ClearanceGraph.lean:53`, soundness `dominates_of_dominatesD
    /// :92`), realised over the untyped felt substrate (a `Label` is a 32-byte
    /// field, exactly as the `SymEq`/`DigEq` type-erasure note above documents —
    /// `Label.id`/`Label.named` both land as one `FieldElement`). BOTH labels are
    /// slot-borne: reading the box from `box_index` (rather than baking it in)
    /// lets ONE static constraint enforce a PER-STEP clearance (CWM: the
    /// advancing turn materializes the entered step's compartment into the box
    /// slot) AND a FIXED-compartment clearance (SGM: `box_index` points at the
    /// frozen `read_compartment` slot). It is STRONGER than the bare Lean atom in
    /// ONE way the apps need: it also binds the graph to a STORED root, so the
    /// `clearance_graph_root` slot a mandate cell pins at birth (`WriteOnce`,
    /// frozen) is LOAD-BEARING — a turn that walks a different (e.g.
    /// over-permissive) graph, or tampers the root slot, FAILS CLOSED on the root
    /// check before the dominance walk runs. Distinct from [`Self::Reachable`] (a
    /// u64-lane source field, inline edges, NO root binding): this reads two
    /// full-field label slots and is bound to a committed root.
    ///
    /// The canonical commitment is [`clearance_graph_root`]: a domain-separated
    /// BLAKE3 hash over the LEX-SORTED, deduplicated `(dominator, dominated)`
    /// edge bytes (order-independent — the graph is a SET of edges), the same
    /// BLAKE3 family the apps hash their labels with (`field_from_bytes`).
    ///
    /// Fail-closed: a bad slot index is `InvalidFieldIndex`; a root mismatch or a
    /// non-dominating actor label is `ConstraintViolated`. A `StateConstraint`
    /// (it reads post-state + carries graph data, like [`Self::Reachable`]); it
    /// does not lift into the post-state-local [`SimpleStateConstraint`] fragment.
    /// APPEND-ONLY (postcard variant indices preserved — factory VKs / content
    /// addresses byte-identical, §2).
    ClearanceDominates {
        /// Slot holding the actor's clearance label (a full 32-byte field).
        actor_label_index: u8,
        /// Slot holding the required compartment/box label the actor must
        /// dominate (a full 32-byte field). Reading the box from state (not a
        /// baked constant) is what lets one constraint serve PER-STEP (CWM) and
        /// FIXED-compartment (SGM) clearance.
        box_index: u8,
        /// Slot holding the committed clearance-graph root
        /// ([`clearance_graph_root`] of `edges`). The binding that makes the
        /// stored root LOAD-BEARING.
        root_index: u8,
        /// The dominance graph as `(dominator, dominated)` edges. Dominance is
        /// the reflexive-transitive closure of these edges (Lean `dominatesD`).
        edges: Vec<(FieldElement, FieldElement)>,
    },

    /// **Aggregate over a named collection in the EXECUTOR-REACHABLE user-field
    /// MAP** (`_RECORD-LAYER-UPGRADE.md` §B — the `fields_root`/`fields_map`
    /// committed key→value map; the doc's actual deliverable). The
    /// executor-writable twin of [`Self::CollectionAggregate`]: where that
    /// reads the cell's `(collection_id, key) → value` HEAP ([`CellState::get_heap`],
    /// which has **no executor write effect**), this reads the **`fields_map`**
    /// ([`CellState::get_field_ext`]) — the map the executor's
    /// `SetField { index >= STATE_SLOTS }` effect already writes (committed by
    /// `fields_root`, folded into the canonical commitment v9, bridged to the
    /// circuit as `UKey::Field { slot: u64 }`). This is what makes the proven
    /// `MOfNDistinct` council lift reachable END-TO-END through a real turn.
    ///
    /// A collection is a contiguous run of element records laid out in
    /// `fields_map` starting at user key `base` (`base >= STATE_SLOTS`): element
    /// `i` occupies the key stride `[base + i*stride .. base + i*stride + stride)`,
    /// and element `i`'s field at element-relative offset `f` is the map value at
    /// key `base + i*stride + f`. The collection is the contiguous prefix whose
    /// ANCHOR field (`pred`'s key/read offset) is PRESENT, truncating at the
    /// first absent index (the `readIndexed` fail-closed truncation — no phantom
    /// tail beyond a gap), bounded by `fuel` (an upper element count).
    ///
    /// THE COUNCIL LIFT rides [`CollPred::MOfNDistinct`] exactly as
    /// [`Self::CollectionAggregate`] does — arbitrary-N M-of-N, distinctness
    /// enforced (a duplicate-padded forge collapses to ONE key; an unbound forge
    /// is filtered). The aggregate evaluator (`CollPred::eval`) is REUSED
    /// verbatim; only the read source differs (`fields_map` vs heap), so the
    /// duplicate-pad / sub-quorum / unbound-forge / absent-collection teeth all
    /// transport.
    ///
    /// Fail-closed: an absent collection (element 0's anchor not present, or a
    /// zero stride) REJECTS — an aggregate over an absent collection is
    /// unevaluable (mirrors `collectionAggregate_absent_refuses`).
    ///
    /// A `StateConstraint` (reads only post-state map, but is proof/data-bearing
    /// over a committed map — like [`Self::CollectionAggregate`] it does not lift
    /// into the post-state-local [`SimpleStateConstraint`] fragment). APPEND-ONLY
    /// (declared LAST so every existing postcard/serde variant index is
    /// preserved — factory VKs / content addresses byte-identical, §2).
    FieldsCollectionAggregate {
        /// The first user-map key the element run starts at. MUST be
        /// `>= STATE_SLOTS` (the map tail; lower keys are the fixed register
        /// file and are not read by this aggregate).
        base: u64,
        /// The per-element key stride (the element record's width — how many
        /// map keys one element occupies). Must be `>= 1`.
        stride: u32,
        /// An upper bound on the element count (the `readIndexed` fuel: no
        /// element index is read beyond it). The collection is the contiguous
        /// present prefix, at most `fuel` long.
        fuel: u32,
        /// The aggregate predicate over the read-out collection (the same
        /// [`CollPred`] vocabulary [`Self::CollectionAggregate`] uses).
        pred: CollPred,
    },

    /// **The sealed-escrow atomic-swap gate** (the sealed-escrow house-capacity
    /// in-circuit weld, `docs/deos/SETTLE-ESCROW-WELD-DESIGN.md`). Forces the
    /// 2-of-2 swap to settle ALL-OR-NOTHING: BOTH leg-status slots must read
    /// `Deposited` before the transition AND BOTH read `Consumed` after. A
    /// forged PARTIAL settle (one leg flipped, the other left `Deposited` — the
    /// half-open trade) is INEXPRESSIBLE: it fails this single conjunctive
    /// entry. This is the Lean `SettleGate` (`metatheory/Dregg2/Deos/
    /// SealedEscrow.lean` §6) lifted to a declared cell-program caveat — a SINGLE
    /// entry reading BOTH legs, which the per-slot-independent caveats
    /// (`AllowedTransitions`, `Monotonic`, …) cannot express (two independent
    /// `Deposited→Consumed` entries do not bind atomicity — a forge would present
    /// one and omit the other).
    ///
    /// The two named slots carry the **field-mirrored leg status** (the
    /// `LegStatus` code `cell/src/escrow_sealed.rs` writes into the committed
    /// heap, mirrored into a register slot for the AIR-teeth view — stage (a) of
    /// the weld design): `Empty = 0`, `Deposited = 1`, `Consumed = 2`. The
    /// executor evaluator (`evaluate_constraint_full`) enforces the gate over the
    /// (old, new) field-slot pair; the projection
    /// (`dregg_turn::executor::project_slot_caveat_manifest`) emits the tag-17
    /// `SLOT_CAVEAT_TAG_SETTLE_ESCROW` manifest entry, which a light client
    /// re-evaluates against the public-input-bound `state_before`/`state_after`
    /// views (`dregg_circuit::effect_vm::verify_slot_caveat_manifest`). The AIR
    /// constraint polynomials — hence the VK bytes — are UNCHANGED (manifest in
    /// public inputs + off-AIR re-evaluation, exactly the temporal-caveat
    /// vehicle): an old verifier rejects tag 17 as `unknown type_tag`, so
    /// adopting it is a verifier-code epoch, not a proving-key rotation.
    ///
    /// STAGED: no deployed cell declares this caveat yet (dead-by-default until a
    /// cell opts in at the sealed-escrow verifier epoch). Fail-closed: a transition
    /// with no `old_state` surfaces `TransitionCheckRequiresOldState`; a bad slot
    /// index is `InvalidFieldIndex`; any non-atomic leg state is
    /// `ConstraintViolated`. A `StateConstraint` (reads the (old, new) pair, does
    /// not lift into the post-state-local [`SimpleStateConstraint`] fragment).
    /// APPEND-ONLY (declared LAST so every existing postcard/serde variant index
    /// is preserved — factory VKs / content addresses byte-identical, §2).
    SettleEscrow {
        /// Register slot mirroring leg A's status code (`Empty`/`Deposited`/
        /// `Consumed` = 0/1/2).
        leg_a_index: u8,
        /// Register slot mirroring leg B's status code.
        leg_b_index: u8,
    },
}
