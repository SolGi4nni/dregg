//! Cell programs: state transition logic carried by cells.
//!
//! A cell program defines valid state transitions. The executor checks the program's
//! constraints on every state-modifying action. This turns cells from "accounts with
//! permissions" into "smart contracts with privacy."
//!
//! # Slot caveats (lifted-enum v1)
//!
//! `StateConstraint` is the **slot-caveat vocabulary**: a closed lifted enum that
//! authors compose to declare a cell's perpetual invariants. The lift is described
//! in `SLOT-CAVEATS-DESIGN.md` (Lane G) and refined by `SLOT-CAVEATS-EVALUATION.md`
//! (eval — adopted 21-variant set instead of 14).
//!
//! ## `Precondition` vs `StateConstraint`
//!
//! These are **distinct surfaces with overlapping atoms**.
//!
//! - **[`crate::Preconditions`]** are **per-Action**: one-shot "given the current
//!   state, is this Action valid to apply?" Carried in `Action::preconditions`,
//!   signed-over by the submitter, evaluated *before* effects run. Scope:
//!   per-action evaluation, see-then-set guard.
//! - **[`StateConstraint`]** is **per-CellProgram-slot**: perpetual "every
//!   transition of this slot must satisfy X." Carried in `Cell::program`,
//!   signed-over at cell creation, evaluated *after* state-modifying effects
//!   on every turn. Scope: per-slot lifetime invariant.
//!
//! They share the predicate-atom alphabet (slot-equals, height-bound,
//! sender-membership) and share [`crate::preconditions::EvalContext`], but the
//! wrapper enums stay distinct because they live in different signing contexts.
//!
//! # Use cases
//!
//! - **Private DEX order**: cell holds (asset, amount, price). The matching
//!   predicate is part of the cell. A filler proves they satisfy the predicate
//!   without seeing the full order details.
//! - **Sealed auction**: cell holds committed bid. On reveal, proves
//!   `bid > minimum` and bid was committed before deadline.
//! - **NFT with provenance**: cell holds ownership + history. Transfer proves
//!   valid chain without revealing full provenance to the public.

use serde::{Deserialize, Serialize};

use crate::preconditions::EvalContext;
use crate::predicate::{
    InputRef, PredicateInput, WitnessedPredicate, WitnessedPredicateError,
    WitnessedPredicateRegistry,
};
use crate::state::{CellState, FIELD_ZERO, FieldElement, STATE_SLOTS};

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
#[derive(Clone, Copy, Debug, Default)]
pub struct WitnessBundle<'a> {
    /// The witness blobs the action carries (indexed).
    pub blobs: &'a [WitnessBlobView<'a>],
    /// Registered verifiers for witnessed-predicate dispatch.
    pub registry: Option<&'a WitnessedPredicateRegistry>,
}

impl<'a> WitnessBundle<'a> {
    pub fn empty() -> Self {
        Self {
            blobs: &[],
            registry: None,
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
    HeapField { key: u64, atom: HeapAtom },
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
    DelegationEpochEquals { index: u8 },
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
}

/// Error from evaluating a cell program.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProgramError {
    /// A state constraint was violated.
    ConstraintViolated {
        constraint: StateConstraint,
        description: String,
    },
    /// A field index in a constraint is out of bounds.
    InvalidFieldIndex { index: u8 },
    /// A circuit proof is required but was not provided.
    CircuitProofRequired { circuit_hash: [u8; 32] },
    /// Custom constraint cannot be evaluated locally (no registered IR).
    CustomConstraintUnevaluable { ir_hash: [u8; 32] },
    /// Immutable / transition constraint cannot be verified without prior state.
    /// Fail-closed: if there is no old_state to compare against, the constraint
    /// cannot be satisfied (unless this is a fresh cell with nonce == 0).
    TransitionCheckRequiresOldState {
        constraint: StateConstraint,
        index: u8,
    },
    /// Replay-sensitive constraint missing context.
    MissingContextField { field: &'static str },
    /// Cross-cell binding (`BoundDelta`) requires γ.2 wiring that is not yet
    /// available at this evaluation site.
    BoundDeltaNotWired { peer_cell: crate::id::CellId },
    /// `TemporalPredicate` requires an attached witness proof.
    TemporalPredicateWitnessMissing { dsl_hash: [u8; 32] },
    /// A `Witnessed { wp }` constraint cannot be evaluated locally
    /// because the executor's per-action witness-binding pass has not
    /// run yet (the executor's witnessed-predicate registry verifies
    /// the proof; the static evaluator only declares the requirement).
    WitnessedPredicateRequiresExecutor { kind_name: &'static str },
    /// `CellProgram::Cases(_)` was evaluated against a transition where
    /// no case matched. Default-deny per Cav-Codex Block 4.
    NoTransitionCaseMatched,
    /// The witnessed-predicate registry returned a verifier rejection
    /// (proof was malformed or the verifier rejected the input).
    WitnessedPredicateRejected {
        kind_name: &'static str,
        reason: String,
    },
    /// `SenderAuthorized` requires a Merkle-membership witness blob but
    /// the action did not carry one at the expected index.
    SenderMembershipWitnessMissing,
    /// The action did not carry the `PreimageGate`'s expected preimage
    /// blob, or it was at the wrong witness index / wrong type.
    PreimageWitnessMissing,
    /// A `Custom { ir_hash }` predicate requires a registered custom
    /// program verifier; either the action did not carry a proof at
    /// the expected witness index or no verifier matched the
    /// declared vk hash.
    CustomProgramProofRejected { ir_hash: [u8; 32], reason: String },
    /// `CapabilityUniqueness` cannot be enforced by the scalar
    /// `(old_state, new_state)` evaluator: structural "exactly one /
    /// no-duplicate" enforcement needs the cell's actual
    /// [`crate::capability::CapabilitySet`], which is only reachable from
    /// the executor. The scalar evaluator fails **closed** with this
    /// sentinel so the constraint can never silently pass; the executor
    /// (`execute_tree::validate_capability_uniqueness`) performs the real
    /// check against the cap set and binds the declared cap-set-root slot
    /// to the canonical capability root.
    CapabilityUniquenessRequiresExecutor { cap_set_root_slot: u8 },
}

impl core::fmt::Display for ProgramError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ProgramError::ConstraintViolated { description, .. } => {
                write!(f, "program constraint violated: {description}")
            }
            ProgramError::InvalidFieldIndex { index } => {
                write!(f, "program references invalid field index: {index}")
            }
            ProgramError::CircuitProofRequired { .. } => {
                write!(
                    f,
                    "circuit program requires a proof in the action authorization"
                )
            }
            ProgramError::CustomConstraintUnevaluable { .. } => {
                write!(f, "custom constraint cannot be evaluated locally")
            }
            ProgramError::TransitionCheckRequiresOldState { index, .. } => {
                write!(
                    f,
                    "transition constraint on field[{index}] cannot be verified without prior state"
                )
            }
            ProgramError::MissingContextField { field } => {
                write!(f, "missing EvalContext field for slot caveat: {field}")
            }
            ProgramError::BoundDeltaNotWired { .. } => {
                write!(f, "BoundDelta peer-cell wiring is not yet available")
            }
            ProgramError::TemporalPredicateWitnessMissing { .. } => {
                write!(f, "TemporalPredicate requires an attached witness proof")
            }
            ProgramError::WitnessedPredicateRequiresExecutor { kind_name } => {
                write!(
                    f,
                    "witnessed predicate ({kind_name}) requires executor-side registry dispatch"
                )
            }
            ProgramError::NoTransitionCaseMatched => {
                write!(
                    f,
                    "Cases program: no transition case matched the action — default-deny"
                )
            }
            ProgramError::WitnessedPredicateRejected { kind_name, reason } => {
                write!(
                    f,
                    "witnessed predicate ({kind_name}) rejected by registered verifier: {reason}"
                )
            }
            ProgramError::SenderMembershipWitnessMissing => {
                write!(
                    f,
                    "SenderAuthorized requires a Merkle-membership witness blob; action did not carry one"
                )
            }
            ProgramError::PreimageWitnessMissing => {
                write!(
                    f,
                    "PreimageGate requires a 32-byte Preimage32 witness blob; action did not carry one"
                )
            }
            ProgramError::CustomProgramProofRejected { reason, .. } => {
                write!(f, "custom program proof rejected: {reason}")
            }
            ProgramError::CapabilityUniquenessRequiresExecutor { cap_set_root_slot } => {
                write!(
                    f,
                    "CapabilityUniqueness on slot {cap_set_root_slot} requires executor-side cap-set enforcement; the scalar state evaluator cannot verify structural uniqueness and fails closed"
                )
            }
        }
    }
}

impl std::error::Error for ProgramError {}

/// Backwards-compatible alias for the v0 error name (kept so existing match
/// arms in `turn::executor::handle_program_violation` keep compiling). The
/// new name is `TransitionCheckRequiresOldState` — semantically broader,
/// since the same shape applies to all `(old, new)` transition variants.
#[allow(non_upper_case_globals)]
impl ProgramError {
    /// Legacy constructor name preserved for backwards compatibility.
    #[doc(hidden)]
    pub fn immutable_check_requires_old_state(index: u8) -> Self {
        ProgramError::TransitionCheckRequiresOldState {
            constraint: StateConstraint::Immutable { index },
            index,
        }
    }
}

impl CellProgram {
    /// Evaluate the program's constraints against the new (post-transition) state.
    ///
    /// For transition variants (`Immutable`, `WriteOnce`, `Monotonic`,
    /// `StrictMonotonic`, `BoundedBy`, `FieldDelta`, `FieldDeltaInRange`,
    /// `SumEqualsAcross`, `MonotonicSequence`, `AllowedTransitions`),
    /// `old_state` is required to compare the field value before and after
    /// the transition. On the cell-initialization path (`old_state == None`
    /// AND `new_state.nonce == 0`), transition variants are permitted to
    /// initialize the field.
    ///
    /// For contextual variants (`FieldGteHeight`, `FieldLteHeight`,
    /// `TemporalGate`, `SenderAuthorized`, `RateLimit`, `RateLimitBySum`,
    /// `PreimageGate`, `TemporalPredicate`, `BoundDelta`), `ctx` supplies
    /// the runtime context. `ctx` may be omitted for purely static checks;
    /// in that case the contextual variants surface
    /// `ProgramError::MissingContextField`.
    pub fn evaluate(
        &self,
        new_state: &CellState,
        old_state: Option<&CellState>,
        ctx: Option<&EvalContext>,
    ) -> Result<(), ProgramError> {
        // Legacy entry-point: callers that don't have a TransitionMeta
        // fall through to a `wildcard` meta (matches only `Always`
        // guards). New `Cases` programs that depend on method or
        // effect-kind guards should use `evaluate_with_meta`.
        self.evaluate_with_meta(new_state, old_state, ctx, &TransitionMeta::wildcard())
    }

    /// Evaluate the program with a [`TransitionMeta`] in scope.
    ///
    /// Used by the executor for `Cases` programs: each case's guard is
    /// matched against the (cell, action) pair, and only the matching
    /// cases' constraints fire. When *no* case matches, the program
    /// default-denies; when multiple cases match, their constraints AND
    /// together.
    ///
    /// `Predicate(_)` and `None` programs are unaffected by `meta`
    /// (they ignore the action-level signals).
    pub fn evaluate_with_meta(
        &self,
        new_state: &CellState,
        old_state: Option<&CellState>,
        ctx: Option<&EvalContext>,
        meta: &TransitionMeta,
    ) -> Result<(), ProgramError> {
        self.evaluate_full(new_state, old_state, ctx, meta, &WitnessBundle::empty())
    }

    /// Full-fat evaluation: per-transition context + witness bundle.
    ///
    /// Used by the executor (Cav-Codex Block 2) to dispatch witnessed
    /// predicates through a registered verifier, populate
    /// `SenderAuthorized` Merkle-membership witnesses, resolve
    /// `PreimageGate` reveals, and surface `Custom` predicate proofs.
    ///
    /// Callers without a witness bundle should use
    /// [`Self::evaluate_with_meta`] (which forwards an empty bundle);
    /// callers without action-level meta and without witnesses can use
    /// [`Self::evaluate`].
    pub fn evaluate_full(
        &self,
        new_state: &CellState,
        old_state: Option<&CellState>,
        ctx: Option<&EvalContext>,
        meta: &TransitionMeta,
        witnesses: &WitnessBundle<'_>,
    ) -> Result<(), ProgramError> {
        match self {
            CellProgram::None => Ok(()),
            CellProgram::Predicate(constraints) => {
                for constraint in constraints {
                    evaluate_constraint_full(constraint, new_state, old_state, ctx, meta, witnesses)?;
                }
                Ok(())
            }
            CellProgram::Cases(cases) => {
                // Track matches separately for invariant cases (Always /
                // SlotChanged) and operation-binding cases (MethodIs /
                // EffectKindIs / boolean composition over those).
                //
                // Cav-Codex Block 4 default-deny: if the program defines
                // at least one operation-binding case, an action whose
                // dispatch matches NONE of them is rejected as
                // `NoTransitionCaseMatched`, even when invariant cases
                // still match. Without this carve-out, an `Always`
                // invariants case silently absorbs unknown methods —
                // the executor would only ever enforce the universal
                // invariants on a `cipherclerk_drain_funds` symbol and
                // the program's whole purpose (operation discrimination)
                // would erode. See the
                // `unknown_method_default_denied` tests in
                // `starbridge-subscription`,
                // `starbridge-governed-namespace`, and
                // `dregg-storage-templates::cap_inbox_tests`.
                let mut any_matched = false;
                let mut any_dispatch_case = false;
                let mut any_dispatch_matched = false;
                for case in cases {
                    let is_dispatch = case.guard.is_method_dispatching();
                    if is_dispatch {
                        any_dispatch_case = true;
                    }
                    if case.guard.matches(meta, old_state, new_state) {
                        any_matched = true;
                        if is_dispatch {
                            any_dispatch_matched = true;
                        }
                        for constraint in &case.constraints {
                            evaluate_constraint_full(
                                constraint, new_state, old_state, ctx, meta, witnesses,
                            )?;
                        }
                    }
                }
                if !any_matched {
                    // No case at all applied — pure default-deny.
                    return Err(ProgramError::NoTransitionCaseMatched);
                }
                if any_dispatch_case && !any_dispatch_matched {
                    // Program defines operation-binding cases but the
                    // action's dispatch matched none of them.
                    return Err(ProgramError::NoTransitionCaseMatched);
                }
                Ok(())
            }
            CellProgram::Circuit { circuit_hash } => Err(ProgramError::CircuitProofRequired {
                circuit_hash: *circuit_hash,
            }),
        }
    }

    /// Backwards-compatible two-arg evaluation: equivalent to
    /// `evaluate(new, old, None)`. Use the three-arg form to support
    /// contextual variants (`SenderAuthorized`, `TemporalGate`, etc.).
    pub fn evaluate_static(
        &self,
        new_state: &CellState,
        old_state: Option<&CellState>,
    ) -> Result<(), ProgramError> {
        self.evaluate(new_state, old_state, None)
    }

    /// Returns true if this program is `None` (backward-compatible no-op).
    pub fn is_none(&self) -> bool {
        matches!(self, CellProgram::None)
    }

    /// Returns true if this program requires proof authorization for state transitions.
    pub fn requires_proof(&self) -> bool {
        matches!(self, CellProgram::Circuit { .. })
    }

    /// Sugar: lift a list of constraints into a single `Always`-guarded
    /// case. Equivalent to `CellProgram::Predicate(constraints)` but
    /// uses the new `Cases` shape (so callers can mix in extra cases
    /// later without restructuring).
    pub fn always(constraints: Vec<StateConstraint>) -> Self {
        CellProgram::Cases(vec![TransitionCase {
            guard: TransitionGuard::Always,
            constraints,
        }])
    }
}

// ============================================================================
// Per-variant evaluators
// ============================================================================

fn check_index(index: u8) -> Result<usize, ProgramError> {
    let idx = index as usize;
    if idx >= STATE_SLOTS {
        return Err(ProgramError::InvalidFieldIndex { index });
    }
    Ok(idx)
}

/// Select the **unique** witness blob whose kind is in `kinds`.
///
/// SECURITY (audit item 4): the previous evaluator selected the *first*
/// blob of a matching kind (`witnesses.blobs.iter().find(..)`). When an
/// action carries several proofs of the same wire kind (e.g. two
/// `ProofBytes` blobs — one for a `Renounced` non-membership proof and
/// one for a `TemporalPredicate`), a first-of-kind scan can bind the
/// *wrong* proof to a predicate, letting a submitter cross-match a valid
/// proof for predicate A against predicate B.
///
/// The `StateConstraint` variants that need a proof
/// (`SenderAuthorized`, `Renounced`, `Custom`) do not carry an explicit
/// `proof_witness_index` field, so we cannot bind by index without a
/// schema/commitment break. Instead we bind by *uniqueness*: the action
/// must carry exactly one blob of the expected kind(s). Ambiguity (more
/// than one candidate) fails **closed** — there is no first-of-kind
/// cross-match window. Predicates that need to disambiguate multiple
/// same-kind proofs must migrate to the typed
/// [`StateConstraint::Witnessed`] variant, whose
/// [`crate::predicate::WitnessedPredicate::proof_witness_index`] names
/// the blob explicitly.
///
/// Returns the index of the unique blob and a reference to it.
fn unique_blob_of_kinds<'a>(
    witnesses: &WitnessBundle<'a>,
    kinds: &[WitnessKindTag],
) -> Result<(usize, &'a WitnessBlobView<'a>), UniqueBlobError> {
    let mut found: Option<(usize, &WitnessBlobView<'_>)> = None;
    for (i, b) in witnesses.blobs.iter().enumerate() {
        if kinds.contains(&b.kind) {
            if found.is_some() {
                return Err(UniqueBlobError::Ambiguous);
            }
            found = Some((i, b));
        }
    }
    found.ok_or(UniqueBlobError::Missing)
}

/// Outcome of [`unique_blob_of_kinds`].
enum UniqueBlobError {
    /// No blob of the requested kind(s) is present.
    Missing,
    /// More than one blob of the requested kind(s) is present — the
    /// binding is ambiguous and we fail closed rather than guess.
    Ambiguous,
}

/// Evaluate a single constraint with no witness bundle (legacy entry).
/// Forwards to [`evaluate_constraint_full`] with an empty bundle so
/// witness-dependent variants surface the same `WitnessedPredicateRequiresExecutor` /
/// `WitnessedPredicateWitnessMissing` sentinel as before.
///
/// Retained for backwards-compatibility with callers that hold a
/// constraint without a witness bundle; the `AnyOf` evaluator now goes
/// through [`evaluate_simple_constraint`] so the Heyting-fragment `Not`
/// short-circuit can fire.
#[allow(dead_code)]
fn evaluate_constraint(
    constraint: &StateConstraint,
    new_state: &CellState,
    old_state: Option<&CellState>,
    ctx: Option<&EvalContext>,
) -> Result<(), ProgramError> {
    evaluate_constraint_full(
        constraint,
        new_state,
        old_state,
        ctx,
        &TransitionMeta::wildcard(),
        &WitnessBundle::empty(),
    )
}

/// Evaluate a single constraint against the cell state with a witness
/// bundle in scope (Cav-Codex Block 2). When the bundle carries a
/// matching witness for `SenderAuthorized`, `PreimageGate`,
/// `RateLimit`, `Witnessed`, `TemporalPredicate`, or `Custom`, the
/// evaluator dispatches to the registered verifier or uses the
/// witness payload directly. Otherwise it falls through to the
/// legacy fail-closed sentinel.
fn evaluate_constraint_full(
    constraint: &StateConstraint,
    new_state: &CellState,
    old_state: Option<&CellState>,
    ctx: Option<&EvalContext>,
    meta: &TransitionMeta,
    witnesses: &WitnessBundle<'_>,
) -> Result<(), ProgramError> {
    match constraint {
        StateConstraint::FieldEquals { index, value } => {
            let idx = check_index(*index)?;
            if new_state.fields[idx] != *value {
                return violated(constraint, format!("field[{idx}] != expected value"));
            }
            Ok(())
        }
        StateConstraint::FieldGte { index, value } => {
            let idx = check_index(*index)?;
            if !field_gte(&new_state.fields[idx], value) {
                return violated(constraint, format!("field[{idx}] < minimum value"));
            }
            Ok(())
        }
        StateConstraint::FieldLte { index, value } => {
            let idx = check_index(*index)?;
            if !field_lte(&new_state.fields[idx], value) {
                return violated(constraint, format!("field[{idx}] > maximum value"));
            }
            Ok(())
        }
        StateConstraint::FieldLteField {
            left_index,
            right_index,
        } => {
            let left = check_index(*left_index)?;
            let right = check_index(*right_index)?;
            if !field_lte(&new_state.fields[left], &new_state.fields[right]) {
                return violated(
                    constraint,
                    format!("field[{left}] > field[{right}] in post-state"),
                );
            }
            Ok(())
        }
        StateConstraint::FieldLteOther {
            index,
            other,
            delta,
        } => {
            let i = check_index(*index)?;
            let o = check_index(*other)?;
            // `new[index] <= new[other] + delta`, signed: read both slots as
            // big-endian u64 lifted to i128 (mirrors Lean `fieldOf` + the
            // integration harness `field_i128`), add the signed `delta` on the
            // right. Fail-closed on violation.
            let lhs = field_to_u64(&new_state.fields[i]) as i128;
            let rhs = field_to_u64(&new_state.fields[o]) as i128 + *delta as i128;
            if lhs > rhs {
                return violated(
                    constraint,
                    format!("field[{i}] = {lhs} > field[{o}] + {delta} = {rhs} in post-state"),
                );
            }
            Ok(())
        }
        StateConstraint::SumEquals { indices, value } => {
            let mut sum: u64 = 0;
            for &idx in indices {
                let i = check_index(idx)?;
                sum = sum
                    .checked_add(field_to_u64(&new_state.fields[i]))
                    .ok_or_else(|| ProgramError::ConstraintViolated {
                        constraint: constraint.clone(),
                        description: format!(
                            "overflow computing sum of fields {indices:?}: u64 addition overflowed"
                        ),
                    })?;
            }
            let expected = field_to_u64(value);
            if sum != expected {
                return violated(
                    constraint,
                    format!("sum of fields {indices:?} = {sum}, expected {expected}"),
                );
            }
            Ok(())
        }

        StateConstraint::Immutable { index } => {
            let idx = check_index(*index)?;
            match old_state {
                Some(old) => {
                    if new_state.fields[idx] != old.fields[idx] {
                        return violated(
                            constraint,
                            format!("field[{idx}] was mutated but is marked immutable"),
                        );
                    }
                }
                None => {
                    if new_state.nonce != 0 {
                        return Err(ProgramError::TransitionCheckRequiresOldState {
                            constraint: constraint.clone(),
                            index: *index,
                        });
                    }
                }
            }
            Ok(())
        }

        StateConstraint::WriteOnce { index } => {
            let idx = check_index(*index)?;
            match old_state {
                Some(old) => {
                    // Permitted: old slot was zero (first write) OR
                    // new == old (no change).
                    let old_zero = old.fields[idx] == FIELD_ZERO;
                    let unchanged = new_state.fields[idx] == old.fields[idx];
                    if !(old_zero || unchanged) {
                        return violated(
                            constraint,
                            format!("field[{idx}] is write-once and was already set"),
                        );
                    }
                }
                None => {
                    if new_state.nonce != 0 {
                        return Err(ProgramError::TransitionCheckRequiresOldState {
                            constraint: constraint.clone(),
                            index: *index,
                        });
                    }
                }
            }
            Ok(())
        }

        StateConstraint::Monotonic { index } => {
            let idx = check_index(*index)?;
            match old_state {
                Some(old) => {
                    if !field_gte(&new_state.fields[idx], &old.fields[idx]) {
                        return violated(
                            constraint,
                            format!("field[{idx}] decreased; Monotonic requires new >= old"),
                        );
                    }
                }
                None => {
                    if new_state.nonce != 0 {
                        return Err(ProgramError::TransitionCheckRequiresOldState {
                            constraint: constraint.clone(),
                            index: *index,
                        });
                    }
                }
            }
            Ok(())
        }

        StateConstraint::StrictMonotonic { index } => {
            let idx = check_index(*index)?;
            match old_state {
                Some(old) => {
                    if !field_gt(&new_state.fields[idx], &old.fields[idx]) {
                        return violated(
                            constraint,
                            format!(
                                "field[{idx}] did not strictly increase; StrictMonotonic requires new > old"
                            ),
                        );
                    }
                }
                None => {
                    if new_state.nonce != 0 {
                        return Err(ProgramError::TransitionCheckRequiresOldState {
                            constraint: constraint.clone(),
                            index: *index,
                        });
                    }
                }
            }
            Ok(())
        }

        StateConstraint::BoundedBy {
            index,
            witness_index,
        } => {
            let idx = check_index(*index)?;
            let widx = check_index(*witness_index)?;
            let changed = match old_state {
                Some(old) => new_state.fields[idx] != old.fields[idx],
                None => new_state.fields[idx] != FIELD_ZERO,
            };
            if changed {
                let armed = new_state.fields[widx] != FIELD_ZERO;
                if !armed {
                    return violated(
                        constraint,
                        format!(
                            "field[{idx}] changed but witness field[{widx}] is zero (BoundedBy)"
                        ),
                    );
                }
            }
            Ok(())
        }

        StateConstraint::FieldDelta { index, delta } => {
            let idx = check_index(*index)?;
            match old_state {
                Some(old) => {
                    let expected = field_add(&old.fields[idx], delta);
                    if new_state.fields[idx] != expected {
                        return violated(constraint, format!("field[{idx}] != old + delta"));
                    }
                }
                None => {
                    if new_state.nonce != 0 {
                        return Err(ProgramError::TransitionCheckRequiresOldState {
                            constraint: constraint.clone(),
                            index: *index,
                        });
                    }
                }
            }
            Ok(())
        }

        StateConstraint::FieldDeltaInRange {
            index,
            min_delta,
            max_delta,
        } => {
            let idx = check_index(*index)?;
            match old_state {
                Some(old) => {
                    let lower = field_add(&old.fields[idx], min_delta);
                    let upper = field_add(&old.fields[idx], max_delta);
                    if !(field_gte(&new_state.fields[idx], &lower)
                        && field_lte(&new_state.fields[idx], &upper))
                    {
                        return violated(
                            constraint,
                            format!("field[{idx}] outside [old+min_delta, old+max_delta]"),
                        );
                    }
                }
                None => {
                    if new_state.nonce != 0 {
                        return Err(ProgramError::TransitionCheckRequiresOldState {
                            constraint: constraint.clone(),
                            index: *index,
                        });
                    }
                }
            }
            Ok(())
        }

        StateConstraint::FieldGteHeight { index, offset } => {
            let idx = check_index(*index)?;
            let ctx = ctx.ok_or(ProgramError::MissingContextField {
                field: "block_height",
            })?;
            let height = ctx.block_height as i128;
            let bound = (height + (*offset as i128)).max(0) as u64;
            let value = field_to_u64(&new_state.fields[idx]);
            if value < bound {
                return violated(
                    constraint,
                    format!(
                        "field[{idx}] = {value} < block_height({}) + {} = {bound}",
                        ctx.block_height, offset
                    ),
                );
            }
            Ok(())
        }

        StateConstraint::FieldLteHeight { index, offset } => {
            let idx = check_index(*index)?;
            let ctx = ctx.ok_or(ProgramError::MissingContextField {
                field: "block_height",
            })?;
            let height = ctx.block_height as i128;
            let bound = (height + (*offset as i128)).max(0) as u64;
            let value = field_to_u64(&new_state.fields[idx]);
            if value > bound {
                return violated(
                    constraint,
                    format!(
                        "field[{idx}] = {value} > block_height({}) + {} = {bound}",
                        ctx.block_height, offset
                    ),
                );
            }
            Ok(())
        }

        StateConstraint::SumEqualsAcross {
            input_fields,
            output_fields,
        } => {
            let old = match old_state {
                Some(o) => o,
                None => {
                    if new_state.nonce != 0 {
                        return Err(ProgramError::TransitionCheckRequiresOldState {
                            constraint: constraint.clone(),
                            index: 0,
                        });
                    }
                    return Ok(());
                }
            };
            let mut new_in: u64 = 0;
            let mut old_in: u64 = 0;
            let mut new_out: u64 = 0;
            for &idx in input_fields {
                let i = check_index(idx)?;
                new_in = new_in
                    .checked_add(field_to_u64(&new_state.fields[i]))
                    .ok_or_else(|| viol(constraint, "input sum overflow"))?;
                old_in = old_in
                    .checked_add(field_to_u64(&old.fields[i]))
                    .ok_or_else(|| viol(constraint, "input sum overflow"))?;
            }
            for &idx in output_fields {
                let i = check_index(idx)?;
                new_out = new_out
                    .checked_add(field_to_u64(&new_state.fields[i]))
                    .ok_or_else(|| viol(constraint, "output sum overflow"))?;
            }
            let rhs = old_in
                .checked_add(new_out)
                .ok_or_else(|| viol(constraint, "rhs overflow"))?;
            if new_in != rhs {
                return violated(
                    constraint,
                    format!(
                        "SumEqualsAcross: sum(new[in])={new_in} != sum(old[in])({old_in}) + sum(new[out])({new_out})"
                    ),
                );
            }
            Ok(())
        }

        StateConstraint::SenderAuthorized { set } => {
            let ctx = ctx.ok_or(ProgramError::MissingContextField { field: "sender" })?;
            let sender = ctx
                .sender
                .as_ref()
                .ok_or(ProgramError::MissingContextField { field: "sender" })?;
            // Cav-Codex Block 2: enforce membership by dispatching to the
            // witnessed-predicate registry against the appropriate
            // commitment (slot root or blinded commitment). The action
            // MUST carry a `MerklePath` (PublicRoot) or `ProofBytes`
            // (BlindedSet) witness blob.
            //
            // SECURITY (audit item 4): the blob is bound by *uniqueness*,
            // not first-of-kind — see `unique_blob_of_kinds`. If the
            // action carries more than one MerklePath/ProofBytes blob the
            // binding is ambiguous and we fail closed.
            let (commitment, kind) = match set {
                AuthorizedSet::PublicRoot { set_root_index } => {
                    let idx = check_index(*set_root_index)?;
                    (
                        new_state.fields[idx],
                        crate::predicate::WitnessedPredicateKind::MerkleMembership,
                    )
                }
                AuthorizedSet::BlindedSet { commitment } => (
                    *commitment,
                    crate::predicate::WitnessedPredicateKind::BlindedSet,
                ),
                AuthorizedSet::CredentialSet {
                    issuer_cell,
                    credential_schema_id,
                } => (
                    AuthorizedSet::credential_set_commitment(issuer_cell, credential_schema_id),
                    crate::predicate::WitnessedPredicateKind::BlindedSet,
                ),
            };
            // Require a witness blob and a registry. If neither is
            // present the constraint surfaces a structural sentinel so
            // tests / fail-closed callers can still match on the
            // `MissingContextField` shape, but real executor calls
            // MUST configure both.
            let Some(registry) = witnesses.registry else {
                return Err(ProgramError::SenderMembershipWitnessMissing);
            };
            // Bind the unique MerklePath / ProofBytes witness blob by
            // uniqueness. Ambiguity or absence fails closed.
            let (blob_idx, blob) = unique_blob_of_kinds(
                witnesses,
                &[WitnessKindTag::MerklePath, WitnessKindTag::ProofBytes],
            )
            .map_err(|e| match e {
                UniqueBlobError::Missing => ProgramError::SenderMembershipWitnessMissing,
                UniqueBlobError::Ambiguous => ProgramError::WitnessedPredicateRejected {
                    kind_name: "SenderAuthorized",
                    reason: "ambiguous membership witness: action carries more than one \
                             MerklePath/ProofBytes blob; bind explicitly via Witnessed { wp }"
                        .into(),
                },
            })?;
            // Build a placeholder WitnessedPredicate to feed the registry,
            // binding the explicit proof witness index we resolved.
            let wp = crate::predicate::WitnessedPredicate {
                kind,
                commitment,
                input_ref: InputRef::Sender,
                proof_witness_index: blob_idx,
            };
            let input = PredicateInput::Sender(sender);
            registry.verify(&wp, &input, blob.bytes).map_err(|e| {
                ProgramError::WitnessedPredicateRejected {
                    kind_name: match kind {
                        crate::predicate::WitnessedPredicateKind::MerkleMembership => {
                            "MerkleMembership"
                        }
                        crate::predicate::WitnessedPredicateKind::BlindedSet => "BlindedSet",
                        _ => "Witnessed",
                    },
                    reason: e.to_string(),
                }
            })?;
            Ok(())
        }

        StateConstraint::Renounced { set } => {
            // Dual of SenderAuthorized: verify the sender is *not* in
            // the named sorted-leaf set by dispatching the
            // NonMembership verifier.
            let ctx = ctx.ok_or(ProgramError::MissingContextField { field: "sender" })?;
            let sender = ctx
                .sender
                .as_ref()
                .ok_or(ProgramError::MissingContextField { field: "sender" })?;
            let commitment = match set {
                RenouncedSet::PublicRoot { set_root_index } => {
                    let idx = check_index(*set_root_index)?;
                    new_state.fields[idx]
                }
                RenouncedSet::BlindedSet { commitment } => *commitment,
            };
            let Some(registry) = witnesses.registry else {
                return Err(ProgramError::SenderMembershipWitnessMissing);
            };
            // The non-membership neighbor witness is a ProofBytes blob
            // (96 bytes — see `NonMembershipNeighborProof`). Bind by
            // uniqueness (audit item 4): ambiguity/absence fails closed.
            let (blob_idx, blob) = unique_blob_of_kinds(witnesses, &[WitnessKindTag::ProofBytes])
                .map_err(|e| match e {
                UniqueBlobError::Missing => ProgramError::SenderMembershipWitnessMissing,
                UniqueBlobError::Ambiguous => ProgramError::WitnessedPredicateRejected {
                    kind_name: "NonMembership",
                    reason: "ambiguous non-membership witness: action carries more than one \
                                 ProofBytes blob; bind explicitly via Witnessed { wp }"
                        .into(),
                },
            })?;
            let wp = crate::predicate::WitnessedPredicate {
                kind: crate::predicate::WitnessedPredicateKind::NonMembership,
                commitment,
                input_ref: InputRef::Sender,
                proof_witness_index: blob_idx,
            };
            let input = PredicateInput::Sender(sender);
            registry.verify(&wp, &input, blob.bytes).map_err(|e| {
                ProgramError::WitnessedPredicateRejected {
                    kind_name: "NonMembership",
                    reason: e.to_string(),
                }
            })?;
            Ok(())
        }

        StateConstraint::CapabilityUniqueness { cap_set_root_slot } => {
            let _ = check_index(*cap_set_root_slot)?;
            // SECURITY (audit item 1): structural "exactly one / no
            // duplicate live capability" cannot be decided from
            // `(old_state, new_state)` alone — the scalar evaluator only
            // sees the 16 state-slot field values, NOT the cell's actual
            // `CapabilitySet`. The cap-set root in
            // `slot[cap_set_root_slot]` is an opaque 32-byte commitment;
            // verifying that it encodes a unique cap requires the real
            // capability list, which is only reachable from the executor.
            //
            // The previous implementation bounds-checked the slot and
            // returned `Ok(())` — a silent no-op that let a cell *declare*
            // NFT-uniqueness while enforcing nothing. We now fail
            // **closed**: any caller that reaches this scalar path without
            // the executor's cap-set enforcement gets a rejection. The
            // executor (`execute_tree::validate_capability_uniqueness`)
            // is the only place this constraint is genuinely enforced; it
            // binds the declared root slot to
            // `compute_canonical_capability_root(&cell.capabilities)` and
            // rejects duplicate cap entries.
            Err(ProgramError::CapabilityUniquenessRequiresExecutor {
                cap_set_root_slot: *cap_set_root_slot,
            })
        }

        StateConstraint::RateLimit { max_per_epoch, .. } => {
            let ctx = ctx.ok_or(ProgramError::MissingContextField {
                field: "sender_epoch_count",
            })?;
            // SECURITY (audit item 2): the count MUST come from the
            // executor's authoritative per-(cell, sender, epoch) counter,
            // surfaced as `ctx.sender_epoch_count`. The executor wires
            // this in `execute_tree::state_constraint_context_count`.
            //
            // The previous implementation fell back to a `RateLimitCount`
            // witness blob carried by the action itself when the ctx
            // count was zero. That fallback was *bypassable*: the action's
            // own signer chose the value, so a submitter could attest
            // `count = 0` on every action and never trip the limit. The
            // self-attested fallback is removed — there is no submitter-
            // controlled path to the count. A `RateLimitCount` witness
            // blob (if present) is informational only and is NOT trusted
            // here.
            let count = ctx.sender_epoch_count;
            if count >= *max_per_epoch {
                return violated(
                    constraint,
                    format!(
                        "sender has {} mutations this epoch, max is {}",
                        count, max_per_epoch
                    ),
                );
            }
            Ok(())
        }

        StateConstraint::RateLimitBySum {
            slot_index,
            max_sum_per_epoch,
            ..
        } => {
            // Window-sum is supplied through the per-(cell, slot, window)
            // running sum tracked by the executor; that pre-aggregated
            // value comes in via `ctx.sender_epoch_count` repurposed as
            // the running per-window sum when the executor wires this
            // variant. Until then, evaluate the delta-bound directly: the
            // per-turn increment must not exceed the cap.
            let idx = check_index(*slot_index)?;
            let new_val = field_to_u64(&new_state.fields[idx]);
            let old_val = old_state.map(|o| field_to_u64(&o.fields[idx])).unwrap_or(0);
            let delta = new_val.saturating_sub(old_val);
            let prior_window_sum = ctx.map(|c| c.sender_epoch_count as u64).unwrap_or(0);
            let window_sum = prior_window_sum.saturating_add(delta);
            if window_sum > *max_sum_per_epoch {
                return violated(
                    constraint,
                    format!(
                        "slot[{idx}] window_sum={window_sum} (prior={prior_window_sum}, delta={delta}) exceeds max_sum_per_epoch={max_sum_per_epoch}"
                    ),
                );
            }
            Ok(())
        }

        StateConstraint::TemporalGate {
            not_before,
            not_after,
        } => {
            let ctx = ctx.ok_or(ProgramError::MissingContextField {
                field: "block_height",
            })?;
            if let Some(nb) = not_before {
                if ctx.block_height < *nb {
                    return violated(
                        constraint,
                        format!("height {} < not_before {nb}", ctx.block_height),
                    );
                }
            }
            if let Some(na) = not_after {
                if ctx.block_height > *na {
                    return violated(
                        constraint,
                        format!("height {} > not_after {na}", ctx.block_height),
                    );
                }
            }
            Ok(())
        }

        StateConstraint::PreimageGate {
            commitment_index,
            hash_kind,
        } => {
            let idx = check_index(*commitment_index)?;
            // Cav-Codex Block 2: prefer the witness blob over the
            // ctx-side preimage (the witness blob is the canonical
            // carrier). Fall back to `ctx.revealed_preimage` for
            // backwards compatibility with callers that haven't moved
            // to witness_blobs yet.
            let preimage = witnesses
                .blobs
                .iter()
                .find_map(|b| {
                    if b.kind == WitnessKindTag::Preimage32 && b.bytes.len() == 32 {
                        let mut buf = [0u8; 32];
                        buf.copy_from_slice(b.bytes);
                        Some(buf)
                    } else {
                        None
                    }
                })
                .or_else(|| ctx.and_then(|c| c.revealed_preimage))
                .ok_or(ProgramError::PreimageWitnessMissing)?;
            let expected = new_state.fields[idx];
            let hash = hash_preimage32(hash_kind, &preimage);
            if hash != expected {
                return violated(constraint, "preimage does not match commitment".into());
            }
            Ok(())
        }

        StateConstraint::KeyRotationGate {
            digest_slot,
            current_slot,
            last_rotated_slot,
            cooling_period,
            hash_kind,
        } => {
            let d = check_index(*digest_slot)?;
            let c = check_index(*current_slot)?;
            let r = check_index(*last_rotated_slot)?;
            // Resolve the pre-state rotation registers. A fresh cell
            // (init path: no old state, nonce == 0) reads as all-zero;
            // any other missing-old case is fail-closed.
            let zeros;
            let old_fields: &[FieldElement; STATE_SLOTS] = match old_state {
                Some(old) => &old.fields,
                None => {
                    if new_state.nonce != 0 {
                        return Err(ProgramError::TransitionCheckRequiresOldState {
                            constraint: constraint.clone(),
                            index: *digest_slot,
                        });
                    }
                    zeros = [FIELD_ZERO; STATE_SLOTS];
                    &zeros
                }
            };
            let unchanged = new_state.fields[d] == old_fields[d]
                && new_state.fields[c] == old_fields[c]
                && new_state.fields[r] == old_fields[r];
            if unchanged {
                // Not a rotation event: the gate only guards the
                // rotation registers.
                return Ok(());
            }
            if old_fields[d] == FIELD_ZERO {
                // INCEPTION (KERI `icp`): nothing was pre-committed yet, so
                // the first commitment is installed without a preimage. The
                // chain must START: a zero digest is the unborn sentinel.
                if new_state.fields[d] == FIELD_ZERO {
                    return violated(
                        constraint,
                        "inception must commit a nonzero next-keys digest".into(),
                    );
                }
                // A nonzero inception stamp must not be future-dated.
                if new_state.fields[r] != FIELD_ZERO {
                    let height = ctx
                        .ok_or(ProgramError::MissingContextField {
                            field: "block_height",
                        })?
                        .block_height;
                    let stamp = field_to_u64(&new_state.fields[r]);
                    if stamp > height {
                        return violated(
                            constraint,
                            format!("inception stamp {stamp} is future-dated (height {height})"),
                        );
                    }
                }
                return Ok(());
            }
            // ROTATION (KERI `rot`). NOTE: `old_fields[c]` — the current,
            // exposed key set — is deliberately never read here
            // (`rotate_current_keys_irrelevant`): holding the current keys
            // contributes nothing toward rotating.
            let height = ctx
                .ok_or(ProgramError::MissingContextField {
                    field: "block_height",
                })?
                .block_height;
            // 1. The preimage EXHIBIT against the PRE-state register.
            let preimage = witnesses
                .blobs
                .iter()
                .find_map(|b| {
                    if b.kind == WitnessKindTag::Preimage32 && b.bytes.len() == 32 {
                        let mut buf = [0u8; 32];
                        buf.copy_from_slice(b.bytes);
                        Some(buf)
                    } else {
                        None
                    }
                })
                .or_else(|| ctx.and_then(|c| c.revealed_preimage))
                .ok_or(ProgramError::PreimageWitnessMissing)?;
            if hash_preimage32(hash_kind, &preimage) != old_fields[d] {
                return violated(
                    constraint,
                    "rotation does not exhibit the preimage of the committed next-keys digest"
                        .into(),
                );
            }
            // 2. The presented key set is INSTALLED.
            if new_state.fields[c] != preimage {
                return violated(
                    constraint,
                    "rotation must install the exhibited key-set commitment as current".into(),
                );
            }
            // 3. The forward chain: the fresh next-commitment rides the
            //    same turn.
            if new_state.fields[d] == FIELD_ZERO {
                return violated(
                    constraint,
                    "rotation must commit a fresh nonzero next-keys digest (the chain)".into(),
                );
            }
            // 4. The cooling window (cooledSince lastRotatedAt period).
            let last = field_to_u64(&old_fields[r]);
            if last.saturating_add(*cooling_period) > height {
                return violated(
                    constraint,
                    format!(
                        "rotation inside the cooling window: last rotation at {last}, \
                         period {cooling_period}, height {height}"
                    ),
                );
            }
            // 5. The rotation stamps its own height (the next window's
            //    anchor).
            if field_to_u64(&new_state.fields[r]) != height
                || new_state.fields[r][..24] != [0u8; 24]
            {
                return violated(
                    constraint,
                    format!("rotation must stamp the current height {height}"),
                );
            }
            Ok(())
        }

        StateConstraint::MonotonicSequence { seq_index } => {
            let idx = check_index(*seq_index)?;
            match old_state {
                Some(old) => {
                    let old_seq = field_to_u64(&old.fields[idx]);
                    let new_seq = field_to_u64(&new_state.fields[idx]);
                    if new_seq != old_seq.wrapping_add(1) {
                        return violated(
                            constraint,
                            format!("seq[{idx}]: expected {} got {}", old_seq + 1, new_seq),
                        );
                    }
                }
                None => {
                    if new_state.nonce != 0 {
                        return Err(ProgramError::TransitionCheckRequiresOldState {
                            constraint: constraint.clone(),
                            index: *seq_index,
                        });
                    }
                }
            }
            Ok(())
        }

        StateConstraint::AllowedTransitions {
            slot_index,
            allowed,
        } => {
            let idx = check_index(*slot_index)?;
            let new_v = new_state.fields[idx];
            let old_v = old_state.map(|o| o.fields[idx]).unwrap_or(FIELD_ZERO);
            let ok = allowed.iter().any(|(o, n)| *o == old_v && *n == new_v);
            if !ok {
                return violated(
                    constraint,
                    format!("transition on slot[{idx}] is not in the allow-list"),
                );
            }
            Ok(())
        }

        StateConstraint::TemporalPredicate {
            dsl_hash,
            witness_index,
        } => {
            // Cav-Codex Block 2: dispatch through the witnessed-predicate
            // registry using the `Temporal` kind. The `witness_index`
            // names which witness blob is the input.
            //
            // SECURITY (audit item 4): the proof bytes are bound by an
            // *explicit* index — the blob immediately following the input
            // (`witness_index + 1`) — instead of a first-of-kind
            // ProofBytes scan. A first-of-kind scan could cross-match a
            // proof intended for a different predicate (e.g. a `Renounced`
            // ProofBytes blob) to this temporal predicate. The proof slot
            // is deterministic and must be ProofBytes, else we fail closed.
            let Some(registry) = witnesses.registry else {
                return Err(ProgramError::TemporalPredicateWitnessMissing {
                    dsl_hash: *dsl_hash,
                });
            };
            let input_idx = *witness_index as usize;
            let input_blob =
                witnesses
                    .blob(input_idx)
                    .ok_or(ProgramError::TemporalPredicateWitnessMissing {
                        dsl_hash: *dsl_hash,
                    })?;
            let proof_idx = input_idx + 1;
            let proof_blob = witnesses
                .blob(proof_idx)
                .filter(|b| b.kind == WitnessKindTag::ProofBytes)
                .ok_or(ProgramError::WitnessedPredicateRejected {
                    kind_name: "Temporal",
                    reason: "TemporalPredicate proof must be a ProofBytes blob at \
                         witness_index + 1 (explicit binding); none found"
                        .into(),
                })?;
            let wp = crate::predicate::WitnessedPredicate {
                kind: crate::predicate::WitnessedPredicateKind::Temporal,
                commitment: *dsl_hash,
                input_ref: InputRef::Witness { index: input_idx },
                proof_witness_index: proof_idx,
            };
            let input = PredicateInput::Bytes(input_blob.bytes);
            registry.verify(&wp, &input, proof_blob.bytes).map_err(|e| {
                ProgramError::WitnessedPredicateRejected {
                    kind_name: "Temporal",
                    reason: e.to_string(),
                }
            })
        }

        StateConstraint::BoundDelta { peer_cell, .. } => {
            // Cross-cell binding is verified by γ.2's cross-cell match
            // loop in the turn executor (post-effect, pre-commit). The
            // per-cell evaluator does not have peer-cell state in scope;
            // it surfaces a sentinel error the executor maps to the
            // cross-cell path.
            Err(ProgramError::BoundDeltaNotWired {
                peer_cell: *peer_cell,
            })
        }

        StateConstraint::AnyOf { variants } => {
            if variants.is_empty() {
                return violated(constraint, "AnyOf with no variants".into());
            }
            let mut last_err: Option<ProgramError> = None;
            for v in variants {
                match evaluate_simple_constraint(v, new_state, old_state, ctx, meta, witnesses) {
                    Ok(()) => return Ok(()),
                    Err(e) => last_err = Some(e),
                }
            }
            Err(
                last_err.unwrap_or_else(|| ProgramError::ConstraintViolated {
                    constraint: constraint.clone(),
                    description: "no AnyOf branch satisfied".into(),
                }),
            )
        }

        // ─── Policy-combinator core (mirrors Lean `Exec.Program`) ───
        StateConstraint::MemberOf { index, set } => {
            let idx = check_index(*index)?;
            let v = field_to_u64(&new_state.fields[idx]);
            if !set.contains(&v) {
                return violated(constraint, format!("field[{idx}] = {v} not in allowlist"));
            }
            Ok(())
        }

        StateConstraint::PrefixOf {
            seg_indices,
            prefix,
        } => {
            // Fail-closed: a path shorter than the queried prefix cannot match.
            if prefix.len() > seg_indices.len() {
                return violated(constraint, "path shorter than prefix".into());
            }
            for (k, want) in prefix.iter().enumerate() {
                let idx = check_index(seg_indices[k])?;
                let got = field_to_u64(&new_state.fields[idx]);
                if got != *want {
                    return violated(
                        constraint,
                        format!("path segment {k} = {got}, prefix wants {want}"),
                    );
                }
            }
            Ok(())
        }

        StateConstraint::InRangeTwoSided { index, lo, hi } => {
            let idx = check_index(*index)?;
            let v = field_to_u64(&new_state.fields[idx]);
            if !(v >= *lo && v <= *hi) {
                return violated(
                    constraint,
                    format!("field[{idx}] = {v} outside [{lo}, {hi}]"),
                );
            }
            Ok(())
        }

        StateConstraint::DeltaBounded { index, d } => {
            let idx = check_index(*index)?;
            match old_state {
                Some(old) => {
                    let delta = field_delta_i128(&old.fields[idx], &new_state.fields[idx]);
                    if delta.unsigned_abs() > (*d as u128) {
                        return violated(
                            constraint,
                            format!("|field[{idx}] delta| = {} > {d}", delta.unsigned_abs()),
                        );
                    }
                }
                None => {
                    if new_state.nonce != 0 {
                        return Err(ProgramError::TransitionCheckRequiresOldState {
                            constraint: constraint.clone(),
                            index: *index,
                        });
                    }
                }
            }
            Ok(())
        }

        StateConstraint::AffineLe { terms, c } => {
            let sum = affine_sum(terms, new_state)?;
            if sum > (*c as i128) {
                return violated(constraint, format!("affine sum {sum} > {c}"));
            }
            Ok(())
        }

        StateConstraint::AffineEq { terms, c } => {
            let sum = affine_sum(terms, new_state)?;
            if sum != (*c as i128) {
                return violated(constraint, format!("affine sum {sum} != {c}"));
            }
            Ok(())
        }

        StateConstraint::Reachable {
            from_index,
            to_label,
            edges,
        } => {
            let idx = check_index(*from_index)?;
            let from = field_to_u64(&new_state.fields[idx]);
            if !reachable_closure(edges, from, *to_label) {
                return violated(
                    constraint,
                    format!("label {from} does not reach {to_label} in DAG"),
                );
            }
            Ok(())
        }

        StateConstraint::AllOf { variants } => {
            for v in variants {
                evaluate_simple_constraint(v, new_state, old_state, ctx, meta, witnesses)?;
            }
            Ok(())
        }

        StateConstraint::Witnessed { wp } => {
            let kind_name: &'static str = match wp.kind {
                crate::predicate::WitnessedPredicateKind::Dfa => "Dfa",
                crate::predicate::WitnessedPredicateKind::Temporal => "Temporal",
                crate::predicate::WitnessedPredicateKind::MerkleMembership => "MerkleMembership",
                crate::predicate::WitnessedPredicateKind::NonMembership => "NonMembership",
                crate::predicate::WitnessedPredicateKind::BlindedSet => "BlindedSet",
                crate::predicate::WitnessedPredicateKind::BridgePredicate => "BridgePredicate",
                crate::predicate::WitnessedPredicateKind::PedersenEquality => "PedersenEquality",
                crate::predicate::WitnessedPredicateKind::Custom { .. } => "Custom",
            };
            // Cav-Codex Block 2: dispatch through the registry when one
            // is supplied. Resolve the InputRef to a PredicateInput and
            // read the proof bytes from `witnesses.blobs[wp.proof_witness_index]`.
            let Some(registry) = witnesses.registry else {
                return Err(ProgramError::WitnessedPredicateRequiresExecutor { kind_name });
            };
            let proof_blob = witnesses.blob(wp.proof_witness_index).ok_or(
                ProgramError::WitnessedPredicateRejected {
                    kind_name,
                    reason: format!(
                        "witness_blobs has no entry at proof_witness_index {}",
                        wp.proof_witness_index
                    ),
                },
            )?;
            // Resolve input ref. For Slot we hand a 32-byte slot value;
            // for Witness we hand the bytes; for Sender we hand the
            // sender pk; for PublicInput we cannot synthesize without
            // the proof's PI vec (caller must use a more specialized
            // path); for SigningMessage we fall through to Bytes.
            //
            // For Sender we need to extend the lifetime of the sender
            // pk reference; we resolve the sender outside the match
            // so the &[u8; 32] borrow is valid for the call.
            let sender_ref: Option<&[u8; 32]> = match &wp.input_ref {
                InputRef::Sender => Some(
                    ctx.ok_or(ProgramError::MissingContextField { field: "sender" })?
                        .sender
                        .as_ref()
                        .ok_or(ProgramError::MissingContextField { field: "sender" })?,
                ),
                _ => None,
            };
            let input: PredicateInput<'_> = match &wp.input_ref {
                InputRef::Slot { index } => {
                    let idx = check_index(*index)?;
                    PredicateInput::Slot(&new_state.fields[idx])
                }
                InputRef::Witness { index } => {
                    let b =
                        witnesses
                            .blob(*index)
                            .ok_or(ProgramError::WitnessedPredicateRejected {
                                kind_name,
                                reason: format!(
                                    "witness_blobs has no entry at input_ref index {index}"
                                ),
                            })?;
                    PredicateInput::Bytes(b.bytes)
                }
                InputRef::PublicInput { .. } => {
                    return Err(ProgramError::WitnessedPredicateRejected {
                        kind_name,
                        reason: "InputRef::PublicInput unsupported in cell-program evaluator"
                            .into(),
                    });
                }
                InputRef::Sender => PredicateInput::Sender(sender_ref.unwrap()),
                InputRef::SigningMessage => {
                    // Caller passes the signing message as a Cleartext
                    // blob; pick the first one.
                    let b = witnesses
                        .blobs
                        .iter()
                        .find(|b| b.kind == WitnessKindTag::Cleartext)
                        .ok_or(ProgramError::WitnessedPredicateRejected {
                            kind_name,
                            reason: "InputRef::SigningMessage needs a Cleartext witness blob"
                                .into(),
                        })?;
                    PredicateInput::Bytes(b.bytes)
                }
            };
            registry.verify(wp, &input, proof_blob.bytes).map_err(|e| {
                ProgramError::WitnessedPredicateRejected {
                    kind_name,
                    reason: e.to_string(),
                }
            })
        }

        StateConstraint::Custom { ir_hash, .. } => {
            // Cav-Codex Block 2: require an attached `custom_program_proof`
            // (a ProofBytes witness blob whose verifier is registered
            // against the declared `ir_hash` as a `Custom { vk_hash }`
            // kind). When no registry is supplied or no matching
            // verifier is registered, fall through to the legacy
            // fail-closed sentinel.
            let Some(registry) = witnesses.registry else {
                return Err(ProgramError::CustomConstraintUnevaluable { ir_hash: *ir_hash });
            };
            // SECURITY (audit item 4): bind the proof blob by uniqueness,
            // not first-of-kind. If the action carries more than one
            // ProofBytes blob the binding is ambiguous (a proof for some
            // other predicate could be cross-matched here) and we fail
            // closed. Apps needing multiple same-kind proofs migrate to
            // the typed `Witnessed { wp }` variant.
            let (proof_idx, proof_blob) =
                unique_blob_of_kinds(witnesses, &[WitnessKindTag::ProofBytes]).map_err(|e| {
                    ProgramError::CustomProgramProofRejected {
                        ir_hash: *ir_hash,
                        reason: match e {
                            UniqueBlobError::Missing => {
                                "no ProofBytes witness blob carried for Custom predicate".into()
                            }
                            UniqueBlobError::Ambiguous => {
                                "ambiguous Custom proof: action carries more than one ProofBytes \
                                 blob; bind explicitly via Witnessed { wp }"
                                    .to_string()
                            }
                        },
                    }
                })?;
            let wp = crate::predicate::WitnessedPredicate {
                kind: crate::predicate::WitnessedPredicateKind::Custom { vk_hash: *ir_hash },
                commitment: *ir_hash,
                input_ref: InputRef::Slot { index: 0 },
                proof_witness_index: proof_idx,
            };
            // Input: hand the entire new_state as Slot(0) reference;
            // custom verifiers are expected to fold whatever they need
            // out of the PI / proof itself.
            let input = PredicateInput::Slot(&new_state.fields[0]);
            registry.verify(&wp, &input, proof_blob.bytes).map_err(|e| {
                ProgramError::CustomProgramProofRejected {
                    ir_hash: *ir_hash,
                    reason: match e {
                        WitnessedPredicateError::KindNotRegistered { .. } => {
                            format!("no verifier registered for ir_hash {:02x?}", ir_hash)
                        }
                        other => other.to_string(),
                    },
                }
            })
        }

        // ─── Turn-context atoms (CELL-PROGRAM-LANGUAGE.md §3) ───
        StateConstraint::SenderIs { pk } => {
            let ctx = ctx.ok_or(ProgramError::MissingContextField { field: "sender" })?;
            let sender = ctx
                .sender
                .as_ref()
                .ok_or(ProgramError::MissingContextField { field: "sender" })?;
            if sender != pk {
                return violated(
                    constraint,
                    "turn sender is not the bound identity (SenderIs)".into(),
                );
            }
            Ok(())
        }

        StateConstraint::SenderInSlot { index } => {
            let idx = check_index(*index)?;
            let ctx = ctx.ok_or(ProgramError::MissingContextField { field: "sender" })?;
            let sender = ctx
                .sender
                .as_ref()
                .ok_or(ProgramError::MissingContextField { field: "sender" })?;
            if sender != &new_state.fields[idx] {
                return violated(
                    constraint,
                    format!("turn sender does not match the identity held in slot[{idx}]"),
                );
            }
            Ok(())
        }

        StateConstraint::BalanceGte { min } => {
            let bal = new_state.balance();
            // SIGNED balance (THE EPOCH §5): any negative balance is below
            // every u64 floor.
            if bal < 0 || (bal as u64) < *min {
                return violated(
                    constraint,
                    format!("cell balance {bal} < required minimum {min}"),
                );
            }
            Ok(())
        }

        StateConstraint::BalanceLte { max } => {
            let bal = new_state.balance();
            // A negative balance satisfies every u64 ceiling.
            if bal >= 0 && (bal as u64) > *max {
                return violated(
                    constraint,
                    format!("cell balance {bal} > allowed maximum {max}"),
                );
            }
            Ok(())
        }

        // ─── Turn-context atoms (apps gaps 3/4): the Lean twins
        //     `senderMemberOf` / `balanceDeltaLe` / `balanceDeltaGe` /
        //     `affineDeltaLe`. Each mirrors its admit-characterization in
        //     `metatheory/Dregg2/Exec/Program.lean`. ───
        StateConstraint::SenderMemberOf { members } => {
            // Mirrors `evalSimpleCtx_senderMemberOf_iff`: admits IFF the
            // context carries a sender AND that sender ∈ members. No sender
            // (system turn / no context) ⇒ MissingContextField (fail-closed);
            // a sender off the board ⇒ ConstraintViolated.
            let ctx = ctx.ok_or(ProgramError::MissingContextField { field: "sender" })?;
            let sender = ctx
                .sender
                .as_ref()
                .ok_or(ProgramError::MissingContextField { field: "sender" })?;
            if !members.contains(sender) {
                return violated(
                    constraint,
                    "turn sender is not a member of the bound id-set (SenderMemberOf)".into(),
                );
            }
            Ok(())
        }

        StateConstraint::BalanceDeltaLte { max } => {
            // Mirrors `evalSimpleCtx_balanceDeltaLe_iff`: admits IFF BOTH the
            // pre- and post-turn sealed balances are present AND
            // `new.balance − old.balance <= max`. The pre-turn balance is the
            // executor's `old_state` (the already-plumbed `balanceBefore`); an
            // absent pre-state fails closed (a rate gate needs both endpoints).
            // Balances are SIGNED i64 (THE EPOCH §5); the delta is computed in
            // i128 to avoid overflow, and `max` (signed) is compared in i128.
            let old = old_state.ok_or(ProgramError::TransitionCheckRequiresOldState {
                constraint: constraint.clone(),
                index: 0,
            })?;
            let delta = new_state.balance() as i128 - old.balance() as i128;
            if delta > (*max as i128) {
                return violated(
                    constraint,
                    format!("per-turn balance change {delta} > allowed maximum {max}"),
                );
            }
            Ok(())
        }

        StateConstraint::BalanceDeltaGte { min } => {
            // Mirrors `evalSimpleCtx_balanceDeltaGe_iff`: admits IFF BOTH the
            // pre- and post-turn sealed balances are present AND
            // `new.balance − old.balance >= min`. Absent pre-state ⇒ fail-closed.
            let old = old_state.ok_or(ProgramError::TransitionCheckRequiresOldState {
                constraint: constraint.clone(),
                index: 0,
            })?;
            let delta = new_state.balance() as i128 - old.balance() as i128;
            if delta < (*min as i128) {
                return violated(
                    constraint,
                    format!("per-turn balance change {delta} < required minimum {min}"),
                );
            }
            Ok(())
        }

        StateConstraint::AffineDeltaLe { terms, c } => {
            // Mirrors `evalConstraint_affineDeltaLe_iff`: admits IFF every
            // term-slot reads on BOTH old and new AND
            // `Σ kᵢ·(new[fᵢ] − old[fᵢ]) <= c`. Absent pre-state (no old_state)
            // ⇒ the delta is not evaluable ⇒ fail-closed; a bad slot index ⇒
            // InvalidFieldIndex (inside `affine_delta_sum`).
            let old = old_state.ok_or(ProgramError::TransitionCheckRequiresOldState {
                constraint: constraint.clone(),
                index: 0,
            })?;
            let sum = affine_delta_sum(terms, old, new_state)?;
            if sum > (*c as i128) {
                return violated(constraint, format!("affine delta sum {sum} > {c}"));
            }
            Ok(())
        }

        // ─── Heap-keyed atom (THE ROTATION's app-state lane) ───
        StateConstraint::HeapField { key, atom } => {
            evaluate_heap_atom(constraint, *key, atom, new_state, old_state)
        }

        // ─── Program-readable delegation_epoch (the channels closure lane) ───
        StateConstraint::DelegationEpochEquals { index } => {
            let idx = check_index(*index)?;
            // Fail-closed: only the executor's per-cell program-check loop
            // stamps the epoch (`TransitionMeta::with_delegation_epoch`);
            // every legacy/wildcard meta surfaces the sentinel.
            let epoch = meta
                .delegation_epoch
                .ok_or(ProgramError::MissingContextField {
                    field: "delegation_epoch",
                })?;
            // Full 32-byte equality against the canonical encoding — a slot
            // with garbage upper limbs and a matching low limb is refused.
            if new_state.fields[idx] != field_from_u64(epoch) {
                return violated(
                    constraint,
                    format!(
                        "slot[{idx}] != delegation_epoch ({epoch}): the epoch slot diverged \
                         from the capability-freshness counter (DelegationEpochEquals)"
                    ),
                );
            }
            Ok(())
        }

        // ─── Count-≥ / order-statistic atom (in-program M-of-N) ───
        StateConstraint::CountGe {
            threshold,
            set_commitment_slot,
        } => {
            let idx = check_index(*set_commitment_slot)?;
            // The witness re-exhibits the FULL element set every turn (the
            // anti-AffineLe design: nothing accumulates in state, so no
            // counter slot can fake M). Bind by uniqueness, fail closed on
            // ambiguity — the `unique_blob_of_kinds` discipline.
            let (_, blob) = unique_blob_of_kinds(witnesses, &[WitnessKindTag::Cleartext])
                .map_err(|e| match e {
                    UniqueBlobError::Missing => ProgramError::MissingContextField {
                        field: "count-ge set-exhibit witness (Cleartext)",
                    },
                    UniqueBlobError::Ambiguous => ProgramError::WitnessedPredicateRejected {
                        kind_name: "CountGe",
                        reason: "ambiguous: more than one Cleartext witness blob; \
                                 the set exhibit cannot be bound"
                            .to_string(),
                    },
                })?;
            let elements: Vec<[u8; 32]> = postcard::from_bytes(blob.bytes).map_err(|_| {
                ProgramError::WitnessedPredicateRejected {
                    kind_name: "CountGe",
                    reason: "set-exhibit blob is not a postcard Vec<[u8;32]>".to_string(),
                }
            })?;
            // Distinctness is structural: duplicates collapse in the set
            // (a duplicate-padded exhibit dedupes to the SAME committed set,
            // so the commitment still binds and the count stays honest).
            let set: std::collections::BTreeSet<[u8; 32]> = elements.into_iter().collect();
            let commitment = count_ge_set_commitment(&set);
            if new_state.fields[idx] != commitment {
                return violated(
                    constraint,
                    format!(
                        "exhibited set does not open the commitment in slot[{idx}] (CountGe)"
                    ),
                );
            }
            if (set.len() as u64) < (*threshold as u64) {
                return violated(
                    constraint,
                    format!(
                        "exhibited set has {} distinct element(s) < threshold {threshold} (CountGe)",
                        set.len()
                    ),
                );
            }
            Ok(())
        }
    }
}

/// Domain tag for [`count_ge_set_commitment`].
const COUNT_GE_SET_DOMAIN: &str = "dregg-countge-set-v1";

/// Canonical openable commitment over a `CountGe` element set: BLAKE3
/// (derive-key domain) over the length-prefixed SORTED 32-byte elements —
/// the same openable sorted-set shape as the channel membership root
/// (`blueprint::channel_member_root`) and the mailbox sender set. An empty
/// set commits to a nonzero value distinct from the all-zero unborn slot.
pub fn count_ge_set_commitment(elements: &std::collections::BTreeSet<[u8; 32]>) -> FieldElement {
    let mut hasher = blake3::Hasher::new_derive_key(COUNT_GE_SET_DOMAIN);
    hasher.update(&(elements.len() as u64).to_le_bytes());
    for e in elements {
        hasher.update(e);
    }
    *hasher.finalize().as_bytes()
}

/// Evaluate a [`HeapAtom`] lifted over heap `key` against the
/// `Option`-valued heap reads of `(old, new)`.
///
/// **Lean twin (the semantics):** `Dregg2.Exec.evalHeap` =
/// `evalSimple (HeapAtom.lift k a)` (`metatheory/Dregg2/Exec/Program.lean`);
/// the per-arm behavior below implements exactly the `evalHeap_*_iff`
/// characterizations and the `evalHeap_*_absent_*` /
/// `evalHeap_immutable_pinned` / `evalHeap_writeOnce_frozen` absence
/// theorems. A missing `old_state` is the Lean EMPTY RECORD: every old
/// key reads `None`. There is deliberately NO `(old_state = None,
/// nonce = 0)` init escape and NO `TransitionCheckRequiresOldState`
/// sentinel here — heap absence has total, fail-closed-coherent
/// semantics of its own (first-write-free where the theorem says so,
/// refuse everywhere else).
///
/// Reads go through [`CellState::get_field_ext`]: keys `< STATE_SLOTS`
/// resolve to the fixed registers (always present when a state exists),
/// keys `>= STATE_SLOTS` to the committed `fields_map` heap.
fn evaluate_heap_atom(
    constraint: &StateConstraint,
    key: u64,
    atom: &HeapAtom,
    new_state: &CellState,
    old_state: Option<&CellState>,
) -> Result<(), ProgramError> {
    let old_v: Option<FieldElement> = old_state.and_then(|s| s.get_field_ext(key));
    let new_v: Option<FieldElement> = new_state.get_field_ext(key);
    match atom {
        // ── post-state atoms: fail closed on an absent post-state key ──
        HeapAtom::Equals { value } => match new_v {
            Some(x) if x == *value => Ok(()),
            Some(_) => violated(constraint, format!("heap[{key}] != expected value")),
            // Absent ≠ present-zero on the heap (evalHeap_equals_absent_refuses).
            None => violated(constraint, format!("heap[{key}] absent post-state (Equals)")),
        },
        HeapAtom::Gte { value } => match new_v {
            Some(ref x) if field_gte(x, value) => Ok(()),
            Some(_) => violated(constraint, format!("heap[{key}] < minimum value")),
            None => violated(constraint, format!("heap[{key}] absent post-state (Gte)")),
        },
        HeapAtom::Lte { value } => match new_v {
            Some(ref x) if field_lte(x, value) => Ok(()),
            Some(_) => violated(constraint, format!("heap[{key}] > maximum value")),
            None => violated(constraint, format!("heap[{key}] absent post-state (Lte)")),
        },
        HeapAtom::MemberOf { set } => match new_v {
            Some(ref x) if set.contains(&field_to_u64(x)) => Ok(()),
            Some(ref x) => violated(
                constraint,
                format!("heap[{key}] = {} not in allowlist", field_to_u64(x)),
            ),
            None => violated(constraint, format!("heap[{key}] absent post-state (MemberOf)")),
        },
        HeapAtom::InRangeTwoSided { lo, hi } => match new_v {
            Some(ref x) => {
                let v = field_to_u64(x);
                if v >= *lo && v <= *hi {
                    Ok(())
                } else {
                    violated(constraint, format!("heap[{key}] = {v} outside [{lo}, {hi}]"))
                }
            }
            None => violated(
                constraint,
                format!("heap[{key}] absent post-state (InRangeTwoSided)"),
            ),
        },

        // ── immutable: first write free, then pinned (erasure refused) ──
        HeapAtom::Immutable => match old_v {
            // evalHeap_immutable_absent_old_admits: the first write is free.
            None => Ok(()),
            // evalHeap_immutable_pinned: admission ⇔ post-state holds the
            // SAME value — a flip OR an erasure (new absent) refuses
            // (evalHeap_immutable_erase_refused).
            Some(a) => {
                if new_v == Some(a) {
                    Ok(())
                } else {
                    violated(
                        constraint,
                        format!("heap[{key}] is pinned (Immutable) and was mutated or erased"),
                    )
                }
            }
        },

        // ── writeOnce: absent/zero-old free, nonzero freezes ──
        HeapAtom::WriteOnce => match old_v {
            // evalHeap_writeOnce_absent_admits / _zero_admits.
            None => Ok(()),
            Some(a) if a == FIELD_ZERO => Ok(()),
            // evalHeap_writeOnce_frozen: admission ⇔ unchanged.
            Some(a) => {
                if new_v == Some(a) {
                    Ok(())
                } else {
                    violated(
                        constraint,
                        format!("heap[{key}] is write-once and was already set"),
                    )
                }
            }
        },

        // ── relational atoms: BOTH sides must be present (no init escape) ──
        HeapAtom::Monotonic => match (old_v, new_v) {
            (Some(ref a), Some(ref b)) if field_gte(b, a) => Ok(()),
            (Some(_), Some(_)) => violated(
                constraint,
                format!("heap[{key}] decreased; Monotonic requires new >= old"),
            ),
            // evalHeap_monotonic_absent_old/new_refuses.
            _ => violated(
                constraint,
                format!("heap[{key}] absent pre- or post-state (Monotonic fails closed)"),
            ),
        },
        HeapAtom::StrictMonotonic => match (old_v, new_v) {
            (Some(ref a), Some(ref b)) if field_gt(b, a) => Ok(()),
            (Some(_), Some(_)) => violated(
                constraint,
                format!("heap[{key}] did not strictly increase (StrictMonotonic)"),
            ),
            _ => violated(
                constraint,
                format!("heap[{key}] absent pre- or post-state (StrictMonotonic fails closed)"),
            ),
        },
        HeapAtom::DeltaBounded { d } => match (old_v, new_v) {
            (Some(ref a), Some(ref b)) => {
                let delta = field_delta_i128(a, b);
                if delta.unsigned_abs() > (*d as u128) {
                    violated(
                        constraint,
                        format!("|heap[{key}] delta| = {} > {d}", delta.unsigned_abs()),
                    )
                } else {
                    Ok(())
                }
            }
            _ => violated(
                constraint,
                format!("heap[{key}] absent pre- or post-state (DeltaBounded fails closed)"),
            ),
        },
    }
}

fn violated(constraint: &StateConstraint, description: String) -> Result<(), ProgramError> {
    Err(ProgramError::ConstraintViolated {
        constraint: constraint.clone(),
        description,
    })
}

fn viol(constraint: &StateConstraint, description: &str) -> ProgramError {
    ProgramError::ConstraintViolated {
        constraint: constraint.clone(),
        description: description.to_string(),
    }
}

/// Lift a non-`Not` `SimpleStateConstraint` into the full
/// `StateConstraint` enum so the same evaluator can handle the lattice
/// of static / transition / contextual variants.
///
/// `Not` is *not* lifted: it has no corresponding `StateConstraint`
/// variant and is dispatched directly by
/// [`evaluate_simple_constraint`], which short-circuits on the inner
/// constraint's acceptance bit. Calling `lift_simple` on a `Not` is a
/// programming error and panics — callers must go through
/// [`evaluate_simple_constraint`] instead.
fn lift_simple(s: &SimpleStateConstraint) -> StateConstraint {
    match s {
        SimpleStateConstraint::FieldEquals { index, value } => StateConstraint::FieldEquals {
            index: *index,
            value: *value,
        },
        SimpleStateConstraint::FieldGte { index, value } => StateConstraint::FieldGte {
            index: *index,
            value: *value,
        },
        SimpleStateConstraint::FieldLte { index, value } => StateConstraint::FieldLte {
            index: *index,
            value: *value,
        },
        SimpleStateConstraint::WriteOnce { index } => StateConstraint::WriteOnce { index: *index },
        SimpleStateConstraint::Immutable { index } => StateConstraint::Immutable { index: *index },
        SimpleStateConstraint::Monotonic { index } => StateConstraint::Monotonic { index: *index },
        SimpleStateConstraint::StrictMonotonic { index } => {
            StateConstraint::StrictMonotonic { index: *index }
        }
        SimpleStateConstraint::BoundedBy {
            index,
            witness_index,
        } => StateConstraint::BoundedBy {
            index: *index,
            witness_index: *witness_index,
        },
        SimpleStateConstraint::FieldGteHeight { index, offset } => {
            StateConstraint::FieldGteHeight {
                index: *index,
                offset: *offset,
            }
        }
        SimpleStateConstraint::FieldLteHeight { index, offset } => {
            StateConstraint::FieldLteHeight {
                index: *index,
                offset: *offset,
            }
        }
        SimpleStateConstraint::TemporalGate {
            not_before,
            not_after,
        } => StateConstraint::TemporalGate {
            not_before: *not_before,
            not_after: *not_after,
        },
        SimpleStateConstraint::Not(_) => {
            // The Heyting-fragment Not has no equivalent
            // StateConstraint variant — it is dispatched inline by
            // evaluate_simple_constraint. lift_simple must not be
            // called on a Not.
            panic!(
                "lift_simple invoked on SimpleStateConstraint::Not; \
                 route through evaluate_simple_constraint instead"
            );
        }
        SimpleStateConstraint::SenderIs { pk } => StateConstraint::SenderIs { pk: *pk },
        SimpleStateConstraint::SenderInSlot { index } => {
            StateConstraint::SenderInSlot { index: *index }
        }
        SimpleStateConstraint::BalanceGte { min } => StateConstraint::BalanceGte { min: *min },
        SimpleStateConstraint::BalanceLte { max } => StateConstraint::BalanceLte { max: *max },
        SimpleStateConstraint::PreimageGate {
            commitment_index,
            hash_kind,
        } => StateConstraint::PreimageGate {
            commitment_index: *commitment_index,
            hash_kind: *hash_kind,
        },
        SimpleStateConstraint::HeapField { key, atom } => StateConstraint::HeapField {
            key: *key,
            atom: atom.clone(),
        },
        SimpleStateConstraint::DelegationEpochEquals { index } => {
            StateConstraint::DelegationEpochEquals { index: *index }
        }
        SimpleStateConstraint::CountGe {
            threshold,
            set_commitment_slot,
        } => StateConstraint::CountGe {
            threshold: *threshold,
            set_commitment_slot: *set_commitment_slot,
        },
        SimpleStateConstraint::SenderMemberOf { members } => StateConstraint::SenderMemberOf {
            members: members.clone(),
        },
        SimpleStateConstraint::BalanceDeltaLte { max } => {
            StateConstraint::BalanceDeltaLte { max: *max }
        }
        SimpleStateConstraint::BalanceDeltaGte { min } => {
            StateConstraint::BalanceDeltaGte { min: *min }
        }
    }
}

/// Evaluate a `SimpleStateConstraint` directly — handles the Heyting
/// `Not` short-circuit inline, falls back to `lift_simple` +
/// `evaluate_constraint_full` for the lattice variants.
///
/// **Acceptance semantics for `Not`:**
/// - Inner `Ok(())` (inner accepts) → `Not` rejects (returns
///   `ConstraintViolated`).
/// - Inner `Err(ProgramError::ConstraintViolated { .. })` (inner
///   rejects on its own terms) → `Not` accepts (`Ok(())`).
/// - Inner returns any other error (`MissingContextField`,
///   `InvalidFieldIndex`, `TransitionCheckRequiresOldState`,
///   `WitnessedPredicateRequiresExecutor`, etc.) → `Not` propagates
///   the same error. This preserves the fail-closed contract: an
///   unevaluable predicate is unevaluable under negation, not
///   vacuously satisfied.
fn evaluate_simple_constraint(
    s: &SimpleStateConstraint,
    new_state: &CellState,
    old_state: Option<&CellState>,
    ctx: Option<&EvalContext>,
    meta: &TransitionMeta,
    witnesses: &WitnessBundle<'_>,
) -> Result<(), ProgramError> {
    match s {
        SimpleStateConstraint::Not(inner) => {
            let lifted_inner = lift_simple(inner);
            match evaluate_constraint_full(&lifted_inner, new_state, old_state, ctx, meta, witnesses) {
                // Inner accepted ⇒ Not rejects.
                Ok(()) => Err(ProgramError::ConstraintViolated {
                    constraint: lifted_inner.clone(),
                    description: format!(
                        "Not({:?}): inner constraint accepted; negation rejects",
                        inner
                    ),
                }),
                // Inner rejected on its own terms ⇒ Not accepts.
                Err(ProgramError::ConstraintViolated { .. }) => Ok(()),
                // Inner unevaluable (missing ctx, bad index,
                // transition-needs-old-state, witness/registry
                // missing, …) ⇒ propagate, do NOT accept. Fail-closed.
                Err(other) => Err(other),
            }
        }
        other => {
            let lifted = lift_simple(other);
            evaluate_constraint_full(&lifted, new_state, old_state, ctx, meta, witnesses)
        }
    }
}

/// Hash a 32-byte preimage under the named [`HashKind`] — the shared
/// digest function behind [`StateConstraint::PreimageGate`] and
/// [`StateConstraint::KeyRotationGate`].
///
/// `Poseidon2` uses BLAKE3 of a domain-tagged preimage as a stand-in until
/// a Poseidon2-on-bytes helper is wired through here. Executor-side use
/// only; AIR enforcement will use the actual Poseidon2 gadget.
fn hash_preimage32(hash_kind: &HashKind, preimage: &[u8; 32]) -> [u8; 32] {
    match hash_kind {
        HashKind::Blake3 => *blake3::hash(preimage).as_bytes(),
        HashKind::Poseidon2 => {
            let mut tagged = Vec::with_capacity(47);
            tagged.extend_from_slice(b"poseidon2-stub:");
            tagged.extend_from_slice(preimage);
            *blake3::hash(&tagged).as_bytes()
        }
    }
}

// ============================================================================
// Field arithmetic / comparisons
// ============================================================================

/// Interpret a field element as a big-endian u64 (last 8 bytes).
fn field_to_u64(field: &FieldElement) -> u64 {
    let mut bytes = [0u8; 8];
    bytes.copy_from_slice(&field[24..32]);
    u64::from_be_bytes(bytes)
}

fn field_delta_i128(old: &FieldElement, new: &FieldElement) -> i128 {
    field_to_u64(new) as i128 - field_to_u64(old) as i128
}

/// Check one `BoundDelta` pair against concrete local and peer state snapshots.
///
/// The ordinary cell-side evaluator still returns `BoundDeltaNotWired` because
/// it does not have peer state in scope. The executor's multi-cell pass and
/// system-level tests use this helper once both old/new cell states are known.
pub fn bound_delta_pair_matches(
    local_old: &CellState,
    local_new: &CellState,
    local_slot: u8,
    peer_old: &CellState,
    peer_new: &CellState,
    peer_slot: u8,
    relation: DeltaRelation,
) -> Result<bool, ProgramError> {
    let local_idx = check_index(local_slot)?;
    let peer_idx = check_index(peer_slot)?;
    let local_delta = field_delta_i128(&local_old.fields[local_idx], &local_new.fields[local_idx]);
    let peer_delta = field_delta_i128(&peer_old.fields[peer_idx], &peer_new.fields[peer_idx]);
    Ok(match relation {
        DeltaRelation::Equal => local_delta == peer_delta,
        DeltaRelation::EqualAndOpposite => local_delta + peer_delta == 0,
    })
}

/// `Σ kᵢ·new[fᵢ]` over named slots (big-endian u64 lifted to i128). Fail-closed on a
/// bad slot index. Mirrors Lean `Exec.affineSum`.
fn affine_sum(terms: &[(i64, u8)], state: &CellState) -> Result<i128, ProgramError> {
    let mut sum: i128 = 0;
    for (k, idx) in terms {
        let i = check_index(*idx)?;
        let x = field_to_u64(&state.fields[i]) as i128;
        sum += (*k as i128) * x;
    }
    Ok(sum)
}

/// `Σ kᵢ·(new[fᵢ] − old[fᵢ])` over named slots — the affine combination of the per-field
/// DELTAS across the `(old, new)` transition (big-endian u64 lifted to i128 on each side).
/// Fail-closed on a bad slot index. Mirrors Lean `Exec.affineDeltaSum` (the reader behind
/// `affineDeltaLe`): the genuine multi-field rate gate the single-field `DeltaBounded` /
/// `FieldDelta` cannot express.
fn affine_delta_sum(
    terms: &[(i64, u8)],
    old_state: &CellState,
    new_state: &CellState,
) -> Result<i128, ProgramError> {
    let mut sum: i128 = 0;
    for (k, idx) in terms {
        let i = check_index(*idx)?;
        let delta = field_delta_i128(&old_state.fields[i], &new_state.fields[i]);
        sum += (*k as i128) * delta;
    }
    Ok(sum)
}

/// Fuel-bounded reflexive-transitive reachability over `(dominator, dominated)` edges
/// (`a` reaches `b`). Mirrors Lean `ClearanceGraph.dominatesFuel`/`dominatesD`: fuel =
/// `edges.len() + 1` bounds the search depth on a finite graph.
fn reachable_closure(edges: &[(u64, u64)], a: u64, b: u64) -> bool {
    fn go(edges: &[(u64, u64)], a: u64, b: u64, fuel: usize) -> bool {
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

/// Compare two field elements as unsigned big-endian: a >= b.
fn field_gte(a: &FieldElement, b: &FieldElement) -> bool {
    a >= b
}

/// Compare two field elements as unsigned big-endian: a <= b.
fn field_lte(a: &FieldElement, b: &FieldElement) -> bool {
    field_gte(b, a)
}

/// Compare two field elements as unsigned big-endian: a > b strictly.
fn field_gt(a: &FieldElement, b: &FieldElement) -> bool {
    a > b
}

/// Field addition modulo the byte-array representation (u64 lane in last 8
/// bytes). For decrements, encode `delta` as the additive inverse. See
/// `SLOT-CAVEATS-EVALUATION.md` §8 question 6.
fn field_add(a: &FieldElement, b: &FieldElement) -> FieldElement {
    let av = field_to_u64(a);
    let bv = field_to_u64(b);
    let s = av.wrapping_add(bv);
    let mut out = *a;
    out[24..32].copy_from_slice(&s.to_be_bytes());
    out
}

/// Helper: create a FieldElement from a u64 (big-endian in last 8 bytes).
pub fn field_from_u64(val: u64) -> FieldElement {
    let mut f = FIELD_ZERO;
    f[24..32].copy_from_slice(&val.to_be_bytes());
    f
}

/// Alias for `field_from_u64` — explicit big-endian naming for clarity at call sites.
pub fn field_from_u64_be(val: u64) -> FieldElement {
    field_from_u64(val)
}

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
    HeapField { key: u64, atom: HeapAtomView },
    /// `new[index]` ≡ the cell's own post-turn `delegation_epoch` (the
    /// channels closure lane — a live group cell self-describes that its
    /// epoch slot IS the capability-freshness counter).
    DelegationEpochEquals { index: u8 },
    /// Witness-exhibited distinct-count ≥ `threshold` bound to the set
    /// commitment in `new[set_commitment_slot]` (in-program M-of-N).
    CountGe {
        threshold: u32,
        set_commitment_slot: u8,
    },
    /// Turn sender must be one of the bound public keys (each 64-hex) —
    /// the multi-admin actor binding (apps gap 3).
    SenderMemberOf { members: Vec<String> },
    /// The cell's per-turn balance change must be `<= max` (signed; apps
    /// gap 4 rate ceiling).
    BalanceDeltaLte { max: i64 },
    /// The cell's per-turn balance change must be `>= min` (signed; apps
    /// gap 4 rate floor).
    BalanceDeltaGte { min: i64 },
    /// `Σ kᵢ·(new[slotᵢ] − old[slotᵢ]) <= c` — multi-field delta gate;
    /// `terms` are `(coefficient, slot)` pairs (apps gap 2).
    AffineDeltaLe { terms: Vec<(i64, u8)>, c: i64 },
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::preconditions::EvalContext;

    fn ctx_at(height: u64) -> EvalContext {
        EvalContext {
            block_height: height,
            ..Default::default()
        }
    }

    fn ctx_sender(sender: [u8; 32], epoch_count: u32) -> EvalContext {
        EvalContext {
            sender: Some(sender),
            sender_epoch_count: epoch_count,
            ..Default::default()
        }
    }

    /// Mock adjacency verifier for cell-side NonMembership program tests. The
    /// REAL Merkle-adjacency STARK lives in `dregg-circuit`/`dregg-turn`
    /// (`CircuitNeighborAdjacencyVerifier`, exercised end-to-end by
    /// `dregg_turn::executor::membership_verifier`'s
    /// `e2e_consecutive_non_membership_accepts`). Here we only need to drive the
    /// cell program's renunciation plumbing through a registry that HAS an
    /// adjacency verifier installed (the post-hardening positive path), so the
    /// mock accepts the canonical `b"ADJ-OK"` blob for any `lower < upper`.
    struct ProgramMockAdjacency;
    impl crate::predicate::NeighborAdjacencyVerifier for ProgramMockAdjacency {
        fn verify_adjacency(
            &self,
            _root: &[u8; 32],
            lower: &[u8; 32],
            upper: &[u8; 32],
            adjacency_proof: &[u8],
        ) -> Result<(), String> {
            if adjacency_proof != b"ADJ-OK" {
                return Err("mock: missing/invalid adjacency proof".into());
            }
            if lower >= upper {
                return Err("mock: lower !< upper".into());
            }
            Ok(())
        }
    }

    /// A stub registry with the mock adjacency verifier installed on
    /// NonMembership/BlindedSet — mirrors the production turn-layer wiring
    /// (`registry_with_real_verifiers`) so genuine renunciations verify.
    fn registry_with_mock_adjacency() -> crate::predicate::WitnessedPredicateRegistry {
        use crate::predicate::{
            CredentialSetMembershipVerifier, NeighborAdjacencyVerifier,
            SortedNeighborNonMembershipVerifier, WitnessedPredicateRegistry,
        };
        use std::sync::Arc;
        let mut r = WitnessedPredicateRegistry::with_stubs();
        let adj: Arc<dyn NeighborAdjacencyVerifier> = Arc::new(ProgramMockAdjacency);
        r.register_builtin(Arc::new(
            SortedNeighborNonMembershipVerifier::with_adjacency(adj.clone()),
        ));
        r.register_builtin(Arc::new(CredentialSetMembershipVerifier::with_adjacency(
            adj,
        )));
        r
    }

    /// Build a v2 non-membership proof carrying the mock-accepted adjacency
    /// blob, bound to `commitment`.
    fn honest_renunciation_v2(commitment: &[u8; 32], lower: [u8; 32], upper: [u8; 32]) -> Vec<u8> {
        crate::predicate::NonMembershipProofV2 {
            neighbor: crate::predicate::NonMembershipNeighborProof::new(commitment, lower, upper),
            adjacency_proof: b"ADJ-OK".to_vec(),
        }
        .to_bytes()
    }

    fn ctx_preimage(p: [u8; 32]) -> EvalContext {
        EvalContext {
            revealed_preimage: Some(p),
            ..Default::default()
        }
    }

    // ── Existing variants (regression) ───────────────────────────────────

    #[test]
    fn no_program_backward_compat() {
        let p = CellProgram::None;
        let s = CellState::new(100);
        assert!(p.evaluate(&s, None, None).is_ok());
    }

    #[test]
    fn field_equals_pass_and_fail() {
        let p = CellProgram::Predicate(vec![StateConstraint::FieldEquals {
            index: 0,
            value: field_from_u64(42),
        }]);
        let mut s = CellState::new(0);
        s.fields[0] = field_from_u64(42);
        assert!(p.evaluate(&s, None, None).is_ok());
        s.fields[0] = field_from_u64(99);
        assert!(p.evaluate(&s, None, None).is_err());
    }

    #[test]
    fn immutable_round_trip() {
        let p = CellProgram::Predicate(vec![StateConstraint::Immutable { index: 3 }]);
        let mut old = CellState::new(0);
        old.fields[3] = field_from_u64(77);
        let mut new_s = old.clone();
        assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
        new_s.fields[3] = field_from_u64(88);
        assert!(p.evaluate(&new_s, Some(&old), None).is_err());
    }

    #[test]
    fn immutable_no_old_state_init_path() {
        let p = CellProgram::Predicate(vec![StateConstraint::Immutable { index: 3 }]);
        let mut s = CellState::new(0);
        s.fields[3] = field_from_u64(77);
        assert!(p.evaluate(&s, None, None).is_ok());
    }

    #[test]
    fn immutable_no_old_state_with_history_fails_closed() {
        let p = CellProgram::Predicate(vec![StateConstraint::Immutable { index: 3 }]);
        let mut s = CellState::new(0);
        s.fields[3] = field_from_u64(77);
        s.set_nonce(5);
        let err = p.evaluate(&s, None, None).unwrap_err();
        assert!(matches!(
            err,
            ProgramError::TransitionCheckRequiresOldState { .. }
        ));
    }

    // ── Heap-keyed atoms (HeapField — THE ROTATION's app-state lane) ─────
    //
    // Per lifted atom: ADMIT + REFUSE + ABSENCE, mirroring the Lean
    // theorems in metatheory/Dregg2/Exec/Program.lean (evalHeap_*_iff,
    // evalHeap_*_absent_*, _pinned, _frozen). The heap key sits well above
    // STATE_SLOTS so every read goes through fields_map.

    const HK: u64 = 99;

    fn heap_prog(atom: HeapAtom) -> CellProgram {
        CellProgram::Predicate(vec![StateConstraint::HeapField { key: HK, atom }])
    }

    fn heap_state(v: Option<u64>) -> CellState {
        let mut s = CellState::new(0);
        if let Some(v) = v {
            assert!(s.set_field_ext(HK, field_from_u64(v)));
        }
        s
    }

    fn heap_eval(
        p: &CellProgram,
        new: &CellState,
        old: Option<&CellState>,
    ) -> Result<(), ProgramError> {
        p.evaluate_full(
            new,
            old,
            None,
            &TransitionMeta::wildcard(),
            &WitnessBundle::empty(),
        )
    }

    #[test]
    fn heap_equals_admit_refuse_absent() {
        let p = heap_prog(HeapAtom::Equals {
            value: field_from_u64(5),
        });
        assert!(heap_eval(&p, &heap_state(Some(5)), Some(&heap_state(None))).is_ok());
        assert!(heap_eval(&p, &heap_state(Some(6)), Some(&heap_state(None))).is_err());
        // Absent post-state refuses (evalHeap_equals_absent_refuses).
        assert!(heap_eval(&p, &heap_state(None), Some(&heap_state(None))).is_err());
        // Absent ≠ present-zero on the heap: Equals{0} still refuses absence.
        let p0 = heap_prog(HeapAtom::Equals { value: FIELD_ZERO });
        assert!(heap_eval(&p0, &heap_state(None), Some(&heap_state(None))).is_err());
        assert!(heap_eval(&p0, &heap_state(Some(0)), Some(&heap_state(None))).is_ok());
    }

    #[test]
    fn heap_gte_lte_admit_refuse_absent() {
        let ge = heap_prog(HeapAtom::Gte {
            value: field_from_u64(10),
        });
        assert!(heap_eval(&ge, &heap_state(Some(10)), None).is_ok());
        assert!(heap_eval(&ge, &heap_state(Some(9)), None).is_err());
        assert!(heap_eval(&ge, &heap_state(None), None).is_err());
        let le = heap_prog(HeapAtom::Lte {
            value: field_from_u64(10),
        });
        assert!(heap_eval(&le, &heap_state(Some(10)), None).is_ok());
        assert!(heap_eval(&le, &heap_state(Some(11)), None).is_err());
        assert!(heap_eval(&le, &heap_state(None), None).is_err());
    }

    #[test]
    fn heap_immutable_first_write_pin_erase() {
        let p = heap_prog(HeapAtom::Immutable);
        // Absent-old: the FIRST write is free (evalHeap_immutable_absent_old_admits)
        // — including via a missing old_state (the Lean empty record).
        assert!(heap_eval(&p, &heap_state(Some(7)), Some(&heap_state(None))).is_ok());
        assert!(heap_eval(&p, &heap_state(Some(7)), None).is_ok());
        // Present-old PINS (evalHeap_immutable_pinned): unchanged admits…
        assert!(heap_eval(&p, &heap_state(Some(7)), Some(&heap_state(Some(7)))).is_ok());
        // …a flip refuses…
        assert!(heap_eval(&p, &heap_state(Some(8)), Some(&heap_state(Some(7)))).is_err());
        // …and ERASURE refuses (evalHeap_immutable_erase_refused).
        assert!(heap_eval(&p, &heap_state(None), Some(&heap_state(Some(7)))).is_err());
    }

    #[test]
    fn heap_write_once_then_frozen() {
        let p = heap_prog(HeapAtom::WriteOnce);
        // Absent-old and zero-old admit (evalHeap_writeOnce_absent/zero_admits).
        assert!(heap_eval(&p, &heap_state(Some(9)), Some(&heap_state(None))).is_ok());
        assert!(heap_eval(&p, &heap_state(Some(9)), Some(&heap_state(Some(0)))).is_ok());
        // A written (nonzero) key freezes (evalHeap_writeOnce_frozen):
        assert!(heap_eval(&p, &heap_state(Some(9)), Some(&heap_state(Some(9)))).is_ok());
        assert!(heap_eval(&p, &heap_state(Some(1)), Some(&heap_state(Some(9)))).is_err());
        assert!(heap_eval(&p, &heap_state(None), Some(&heap_state(Some(9)))).is_err());
    }

    #[test]
    fn heap_monotonic_no_init_escape() {
        let p = heap_prog(HeapAtom::Monotonic);
        assert!(heap_eval(&p, &heap_state(Some(2)), Some(&heap_state(Some(1)))).is_ok());
        assert!(heap_eval(&p, &heap_state(Some(2)), Some(&heap_state(Some(2)))).is_ok());
        assert!(heap_eval(&p, &heap_state(Some(1)), Some(&heap_state(Some(2)))).is_err());
        // ABSENT-old refuses — deliberately NO init escape on the heap
        // (evalHeap_monotonic_absent_old_refuses), including a missing
        // old_state entirely (≠ the slot Monotonic nonce-0 carve-out).
        assert!(heap_eval(&p, &heap_state(Some(2)), Some(&heap_state(None))).is_err());
        assert!(heap_eval(&p, &heap_state(Some(2)), None).is_err());
        // Absent-new refuses (a monotone key cannot be erased).
        assert!(heap_eval(&p, &heap_state(None), Some(&heap_state(Some(1)))).is_err());
    }

    #[test]
    fn heap_strict_monotonic_admit_refuse_absent() {
        let p = heap_prog(HeapAtom::StrictMonotonic);
        assert!(heap_eval(&p, &heap_state(Some(2)), Some(&heap_state(Some(1)))).is_ok());
        // The equality edge Monotonic admits and StrictMonotonic refuses.
        assert!(heap_eval(&p, &heap_state(Some(2)), Some(&heap_state(Some(2)))).is_err());
        assert!(heap_eval(&p, &heap_state(Some(2)), Some(&heap_state(None))).is_err());
        assert!(heap_eval(&p, &heap_state(None), Some(&heap_state(Some(1)))).is_err());
    }

    #[test]
    fn heap_member_of_and_range_admit_refuse_absent() {
        let m = heap_prog(HeapAtom::MemberOf { set: vec![1, 2, 3] });
        assert!(heap_eval(&m, &heap_state(Some(2)), None).is_ok());
        assert!(heap_eval(&m, &heap_state(Some(9)), None).is_err());
        assert!(heap_eval(&m, &heap_state(None), None).is_err());
        let r = heap_prog(HeapAtom::InRangeTwoSided { lo: 100, hi: 200 });
        assert!(heap_eval(&r, &heap_state(Some(150)), None).is_ok());
        assert!(heap_eval(&r, &heap_state(Some(99)), None).is_err());
        assert!(heap_eval(&r, &heap_state(None), None).is_err());
    }

    #[test]
    fn heap_delta_bounded_admit_refuse_absent() {
        let p = heap_prog(HeapAtom::DeltaBounded { d: 5 });
        assert!(heap_eval(&p, &heap_state(Some(104)), Some(&heap_state(Some(100)))).is_ok());
        assert!(heap_eval(&p, &heap_state(Some(96)), Some(&heap_state(Some(100)))).is_ok());
        assert!(heap_eval(&p, &heap_state(Some(110)), Some(&heap_state(Some(100)))).is_err());
        assert!(heap_eval(&p, &heap_state(Some(90)), Some(&heap_state(Some(100)))).is_err());
        assert!(heap_eval(&p, &heap_state(Some(3)), Some(&heap_state(None))).is_err());
        assert!(heap_eval(&p, &heap_state(None), Some(&heap_state(Some(3)))).is_err());
    }

    #[test]
    fn heap_atom_composes_under_heyting_fragment() {
        // Not(HeapField) is the clean complement (heap atoms only ever emit
        // ConstraintViolated, never a structural error, so the Heyting Not
        // short-circuit applies): refuse-the-pin becomes admit.
        let not_eq = CellProgram::Predicate(vec![StateConstraint::AnyOf {
            variants: vec![SimpleStateConstraint::Not(Box::new(
                SimpleStateConstraint::HeapField {
                    key: HK,
                    atom: HeapAtom::Equals {
                        value: field_from_u64(5),
                    },
                },
            ))],
        }]);
        assert!(heap_eval(&not_eq, &heap_state(Some(6)), None).is_ok());
        assert!(heap_eval(&not_eq, &heap_state(Some(5)), None).is_err());
        // Absent inner ⇒ inner refuses ⇒ Not admits (the Lean !false).
        assert!(heap_eval(&not_eq, &heap_state(None), None).is_ok());

        // The per-HEAP-field actor binding: AnyOf[HeapField{Immutable},
        // SenderIs{pk}] — the heap twin of the polis approval-slot tooth
        // (Lean heapActorBound_flip_requires_sender).
        let bound_pk = [0xAB; 32];
        let bound = CellProgram::Predicate(vec![StateConstraint::AnyOf {
            variants: vec![
                SimpleStateConstraint::HeapField {
                    key: HK,
                    atom: HeapAtom::Immutable,
                },
                SimpleStateConstraint::SenderIs { pk: bound_pk },
            ],
        }]);
        let old = heap_state(Some(1));
        let flipped = heap_state(Some(2));
        // The bound sender flips the heap key: admitted.
        assert!(
            bound
                .evaluate_full(
                    &flipped,
                    Some(&old),
                    Some(&ctx_sender(bound_pk, 0)),
                    &TransitionMeta::wildcard(),
                    &WitnessBundle::empty(),
                )
                .is_ok()
        );
        // A stranger flipping the heap key: refused.
        assert!(
            bound
                .evaluate_full(
                    &flipped,
                    Some(&old),
                    Some(&ctx_sender([0x57; 32], 0)),
                    &TransitionMeta::wildcard(),
                    &WitnessBundle::empty(),
                )
                .is_err()
        );
        // A stranger leaving the key alone: admitted (the ceremony stays open).
        assert!(
            bound
                .evaluate_full(
                    &old,
                    Some(&old),
                    Some(&ctx_sender([0x57; 32], 0)),
                    &TransitionMeta::wildcard(),
                    &WitnessBundle::empty(),
                )
                .is_ok()
        );
    }

    #[test]
    fn heap_and_slot_constraints_coexist_in_one_program() {
        // One predicate carrying a SLOT tooth and a HEAP tooth — each bites
        // independently (the Lean mixedHeapProgram twin).
        let p = CellProgram::Predicate(vec![
            StateConstraint::Monotonic { index: 0 },
            StateConstraint::HeapField {
                key: HK,
                atom: HeapAtom::Monotonic,
            },
        ]);
        let mut old = heap_state(Some(5));
        old.fields[0] = field_from_u64(1);
        // Both advance: admitted.
        let mut good = heap_state(Some(9));
        good.fields[0] = field_from_u64(2);
        assert!(heap_eval(&p, &good, Some(&old)).is_ok());
        // Heap tooth bites (slot fine, heap decreases).
        let mut bad_heap = heap_state(Some(3));
        bad_heap.fields[0] = field_from_u64(2);
        assert!(heap_eval(&p, &bad_heap, Some(&old)).is_err());
        // Slot tooth still bites (heap fine, slot decreases). Slot 0 of
        // `old` is 1; new slot 0 = 0 < 1.
        let bad_slot = heap_state(Some(9));
        assert!(heap_eval(&p, &bad_slot, Some(&old)).is_err());
    }

    // ── New variants ──────────────────────────────────────────────────────

    #[test]
    fn write_once_first_write_then_frozen() {
        let p = CellProgram::Predicate(vec![StateConstraint::WriteOnce { index: 0 }]);
        // First write: old slot is zero, new is non-zero — allowed.
        let mut old = CellState::new(0);
        let mut new_s = CellState::new(0);
        new_s.fields[0] = field_from_u64(42);
        assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
        // Subsequent write attempt: old is non-zero, new differs — rejected.
        old.fields[0] = field_from_u64(42);
        let mut tampered = old.clone();
        tampered.fields[0] = field_from_u64(99);
        assert!(p.evaluate(&tampered, Some(&old), None).is_err());
        // Unchanged: allowed.
        assert!(p.evaluate(&old, Some(&old), None).is_ok());
    }

    #[test]
    fn monotonic_only_increases() {
        let p = CellProgram::Predicate(vec![StateConstraint::Monotonic { index: 1 }]);
        let mut old = CellState::new(0);
        old.fields[1] = field_from_u64(10);
        let mut new_s = old.clone();
        new_s.fields[1] = field_from_u64(20);
        assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
        new_s.fields[1] = field_from_u64(10);
        assert!(p.evaluate(&new_s, Some(&old), None).is_ok()); // equal allowed
        new_s.fields[1] = field_from_u64(5);
        assert!(p.evaluate(&new_s, Some(&old), None).is_err()); // decrease rejected
    }

    #[test]
    fn strict_monotonic_must_strictly_increase() {
        let p = CellProgram::Predicate(vec![StateConstraint::StrictMonotonic { index: 0 }]);
        let mut old = CellState::new(0);
        old.fields[0] = field_from_u64(10);
        let mut new_s = old.clone();
        new_s.fields[0] = field_from_u64(11);
        assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
        new_s.fields[0] = field_from_u64(10);
        assert!(p.evaluate(&new_s, Some(&old), None).is_err()); // equal rejected
        new_s.fields[0] = field_from_u64(9);
        assert!(p.evaluate(&new_s, Some(&old), None).is_err()); // decrease rejected
    }

    #[test]
    fn bounded_by_requires_witness_armed() {
        let p = CellProgram::Predicate(vec![StateConstraint::BoundedBy {
            index: 0,
            witness_index: 1,
        }]);
        let old = CellState::new(0);
        // Change slot 0 with witness zero → rejected.
        let mut new_s = CellState::new(0);
        new_s.fields[0] = field_from_u64(99);
        assert!(p.evaluate(&new_s, Some(&old), None).is_err());
        // Change slot 0 with witness non-zero → allowed.
        new_s.fields[1] = field_from_u64(1);
        assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
    }

    #[test]
    fn field_delta_exact_step() {
        let p = CellProgram::Predicate(vec![StateConstraint::FieldDelta {
            index: 0,
            delta: field_from_u64(100),
        }]);
        let mut old = CellState::new(0);
        old.fields[0] = field_from_u64(500);
        let mut new_s = old.clone();
        new_s.fields[0] = field_from_u64(600);
        assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
        new_s.fields[0] = field_from_u64(700);
        assert!(p.evaluate(&new_s, Some(&old), None).is_err());
    }

    #[test]
    fn field_delta_in_range() {
        let p = CellProgram::Predicate(vec![StateConstraint::FieldDeltaInRange {
            index: 0,
            min_delta: field_from_u64(0),
            max_delta: field_from_u64(10),
        }]);
        let mut old = CellState::new(0);
        old.fields[0] = field_from_u64(50);
        let mut new_s = old.clone();
        new_s.fields[0] = field_from_u64(55);
        assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
        new_s.fields[0] = field_from_u64(70);
        assert!(p.evaluate(&new_s, Some(&old), None).is_err());
    }

    #[test]
    fn field_gte_height_uses_ctx() {
        let p = CellProgram::Predicate(vec![StateConstraint::FieldGteHeight {
            index: 0,
            offset: 100,
        }]);
        let mut s = CellState::new(0);
        s.fields[0] = field_from_u64(250);
        // current_height=100, expiry=250, bound=100+100=200, 250>=200 → ok
        assert!(p.evaluate(&s, None, Some(&ctx_at(100))).is_ok());
        // bound=300 (height=200, offset=100): 250<300 → fail
        assert!(p.evaluate(&s, None, Some(&ctx_at(200))).is_err());
    }

    #[test]
    fn field_lte_height_uses_ctx() {
        let p = CellProgram::Predicate(vec![StateConstraint::FieldLteHeight {
            index: 0,
            offset: 100,
        }]);
        let mut s = CellState::new(0);
        s.fields[0] = field_from_u64(150);
        // bound = 100+100=200, 150<=200 → ok
        assert!(p.evaluate(&s, None, Some(&ctx_at(100))).is_ok());
        // bound = 50+100=150 with value 150 → still ok (equal)
        assert!(p.evaluate(&s, None, Some(&ctx_at(50))).is_ok());
        // bound = 49+100=149, 150>149 → fail
        assert!(p.evaluate(&s, None, Some(&ctx_at(49))).is_err());
    }

    #[test]
    fn sum_equals_across_intra_cell_conservation() {
        // sum(new[0,1]) == sum(old[0,1]) + sum(new[2,3])
        let p = CellProgram::Predicate(vec![StateConstraint::SumEqualsAcross {
            input_fields: vec![0, 1],
            output_fields: vec![2, 3],
        }]);
        let mut old = CellState::new(0);
        old.fields[0] = field_from_u64(100);
        old.fields[1] = field_from_u64(50);
        let mut new_s = old.clone();
        new_s.fields[0] = field_from_u64(160);
        new_s.fields[1] = field_from_u64(80);
        new_s.fields[2] = field_from_u64(60);
        new_s.fields[3] = field_from_u64(30);
        // sum(new in) = 240, sum(old in)=150, sum(new out)=90, 150+90=240 ✓
        assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
        new_s.fields[2] = field_from_u64(0);
        assert!(p.evaluate(&new_s, Some(&old), None).is_err());
    }

    #[test]
    fn sender_authorized_needs_sender_in_ctx() {
        let p = CellProgram::Predicate(vec![StateConstraint::SenderAuthorized {
            set: AuthorizedSet::PublicRoot { set_root_index: 7 },
        }]);
        let s = CellState::new(0);
        // No ctx → MissingContextField
        let err = p.evaluate(&s, None, None).unwrap_err();
        assert!(matches!(err, ProgramError::MissingContextField { .. }));
        // ctx with no sender → also missing
        let bare = EvalContext::default();
        let err = p.evaluate(&s, None, Some(&bare)).unwrap_err();
        assert!(matches!(err, ProgramError::MissingContextField { .. }));
        // ctx with sender but no registry → SenderMembershipWitnessMissing
        // (the registry + witness blob are also required for full verification)
        let err = p
            .evaluate(&s, None, Some(&ctx_sender([1u8; 32], 0)))
            .unwrap_err();
        assert!(matches!(err, ProgramError::SenderMembershipWitnessMissing));
    }

    #[test]
    fn rate_limit_enforces_per_epoch_cap() {
        let p = CellProgram::Predicate(vec![StateConstraint::RateLimit {
            max_per_epoch: 3,
            epoch_duration: 100,
        }]);
        let s = CellState::new(0);
        let sender = [9u8; 32];
        // 0 < 3 → ok
        assert!(p.evaluate(&s, None, Some(&ctx_sender(sender, 0))).is_ok());
        // 2 < 3 → ok
        assert!(p.evaluate(&s, None, Some(&ctx_sender(sender, 2))).is_ok());
        // 3 >= 3 → fail
        assert!(p.evaluate(&s, None, Some(&ctx_sender(sender, 3))).is_err());
    }

    #[test]
    fn rate_limit_by_sum_caps_delta() {
        let p = CellProgram::Predicate(vec![StateConstraint::RateLimitBySum {
            slot_index: 0,
            max_sum_per_epoch: 100,
            epoch_duration: 1000,
        }]);
        let mut old = CellState::new(0);
        old.fields[0] = field_from_u64(50);
        let mut new_s = old.clone();
        new_s.fields[0] = field_from_u64(140); // +90 < 100 → ok
        assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
        new_s.fields[0] = field_from_u64(200); // +150 > 100 → fail
        assert!(p.evaluate(&new_s, Some(&old), None).is_err());
    }

    #[test]
    fn temporal_gate_enforces_window() {
        let p = CellProgram::Predicate(vec![StateConstraint::TemporalGate {
            not_before: Some(100),
            not_after: Some(200),
        }]);
        let s = CellState::new(0);
        assert!(p.evaluate(&s, None, Some(&ctx_at(50))).is_err());
        assert!(p.evaluate(&s, None, Some(&ctx_at(150))).is_ok());
        assert!(p.evaluate(&s, None, Some(&ctx_at(250))).is_err());
    }

    #[test]
    fn preimage_gate_verifies_hash() {
        let preimage = [7u8; 32];
        let commitment = *blake3::hash(&preimage).as_bytes();
        let p = CellProgram::Predicate(vec![StateConstraint::PreimageGate {
            commitment_index: 0,
            hash_kind: HashKind::Blake3,
        }]);
        let mut s = CellState::new(0);
        s.fields[0] = commitment;
        // Correct preimage → ok
        assert!(p.evaluate(&s, None, Some(&ctx_preimage(preimage))).is_ok());
        // Wrong preimage → fail
        assert!(
            p.evaluate(&s, None, Some(&ctx_preimage([8u8; 32])))
                .is_err()
        );
        // No preimage in ctx → missing
        assert!(p.evaluate(&s, None, Some(&EvalContext::default())).is_err());
    }

    /// `KeyRotationGate`: the rotate verb as a guarded write — preimage
    /// exhibit against the OLD digest register, install, fresh re-commit,
    /// cooling. The full triangle lives in `starbridge_polis::identity`
    /// tests; this pins the constraint's own semantics.
    #[test]
    fn key_rotation_gate_semantics() {
        let gate = StateConstraint::KeyRotationGate {
            digest_slot: 1,
            current_slot: 2,
            last_rotated_slot: 3,
            cooling_period: 50,
            hash_kind: HashKind::Blake3,
        };
        let p = CellProgram::Predicate(vec![gate]);
        let next: [u8; 32] = [0xAB; 32]; // the pre-committed key-set commitment
        let digest = *blake3::hash(&next).as_bytes();

        let ctx = |height: u64, preimage: Option<[u8; 32]>| EvalContext {
            block_height: height,
            revealed_preimage: preimage,
            ..EvalContext::default()
        };

        // Committed state: digest register live, last rotation at 100.
        let mut old = CellState::new(0);
        old.nonce = 1;
        old.fields[1] = digest;
        old.fields[2] = [0x01; 32]; // current keys (must be irrelevant)
        old.fields[3] = field_from_u64(100);

        // No-op turn (registers untouched): admitted without a preimage.
        assert!(p.evaluate(&old, Some(&old), Some(&ctx(0, None))).is_ok());

        // Honest rotation at height 200 (cooled past 100 + 50): exhibit
        // `next`, install it, commit fresh, stamp 200.
        let mut rotated = old.clone();
        rotated.fields[1] = *blake3::hash(&[0xCD; 32]).as_bytes();
        rotated.fields[2] = next;
        rotated.fields[3] = field_from_u64(200);
        assert!(
            p.evaluate(&rotated, Some(&old), Some(&ctx(200, Some(next))))
                .is_ok()
        );
        // CURRENT KEYS ARE IRRELEVANT: the same rotation from a state with
        // ANY other current key set is decided identically (the structural
        // mirror of `rotate_current_keys_irrelevant`).
        let mut stolen = old.clone();
        stolen.fields[2] = [0xEE; 32];
        let mut rotated2 = rotated.clone();
        rotated2.fields[2] = next;
        assert!(
            p.evaluate(&rotated2, Some(&stolen), Some(&ctx(200, Some(next))))
                .is_ok()
        );

        // Wrong preimage (forged key set): refused.
        assert!(
            p.evaluate(&rotated, Some(&old), Some(&ctx(200, Some([0xEE; 32]))))
                .is_err()
        );
        // No preimage at all: refused even though the turn is well-formed.
        assert!(
            matches!(
                p.evaluate(&rotated, Some(&old), Some(&ctx(200, None))),
                Err(ProgramError::PreimageWitnessMissing)
            ),
            "rotation without the exhibit must surface PreimageWitnessMissing"
        );
        // Install mismatch: exhibiting the right preimage but installing a
        // different current commitment is refused.
        let mut misinstalled = rotated.clone();
        misinstalled.fields[2] = [0x99; 32];
        assert!(
            p.evaluate(&misinstalled, Some(&old), Some(&ctx(200, Some(next))))
                .is_err()
        );
        // Chain break: zeroing the register is refused.
        let mut chainless = rotated.clone();
        chainless.fields[1] = FIELD_ZERO;
        assert!(
            p.evaluate(&chainless, Some(&old), Some(&ctx(200, Some(next))))
                .is_err()
        );
        // Cooling: inside the window (100 + 50 > 149) even the honest
        // rotation is refused; the stamp must equal the height.
        let mut early = rotated.clone();
        early.fields[3] = field_from_u64(149);
        assert!(
            p.evaluate(&early, Some(&old), Some(&ctx(149, Some(next))))
                .is_err()
        );
        let mut misstamped = rotated.clone();
        misstamped.fields[3] = field_from_u64(150);
        assert!(
            p.evaluate(&misstamped, Some(&old), Some(&ctx(200, Some(next))))
                .is_err()
        );

        // Inception: from the unborn register (old digest == 0) the first
        // commitment installs without a preimage; a zero digest is refused.
        let born = CellState::new(0);
        let mut inducted = CellState::new(0);
        inducted.fields[1] = digest;
        inducted.fields[2] = [0x01; 32];
        assert!(
            p.evaluate(&inducted, Some(&born), Some(&ctx(0, None)))
                .is_ok()
        );
        let mut zeroed = inducted.clone();
        zeroed.fields[1] = FIELD_ZERO;
        assert!(
            p.evaluate(&zeroed, Some(&born), Some(&ctx(0, None)))
                .is_err()
        );
    }

    #[test]
    fn monotonic_sequence_increments_by_one() {
        let p = CellProgram::Predicate(vec![StateConstraint::MonotonicSequence { seq_index: 0 }]);
        let mut old = CellState::new(0);
        old.fields[0] = field_from_u64(5);
        let mut new_s = old.clone();
        new_s.fields[0] = field_from_u64(6);
        assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
        new_s.fields[0] = field_from_u64(7);
        assert!(p.evaluate(&new_s, Some(&old), None).is_err()); // skipped one
        new_s.fields[0] = field_from_u64(5);
        assert!(p.evaluate(&new_s, Some(&old), None).is_err()); // no increment
    }

    #[test]
    fn allowed_transitions_state_machine() {
        let open = field_from_u64(1);
        let claimed = field_from_u64(2);
        let paid = field_from_u64(3);
        let p = CellProgram::Predicate(vec![StateConstraint::AllowedTransitions {
            slot_index: 0,
            allowed: vec![(open, claimed), (claimed, paid)],
        }]);
        let mut old = CellState::new(0);
        old.fields[0] = open;
        let mut new_s = old.clone();
        new_s.fields[0] = claimed;
        assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
        new_s.fields[0] = paid;
        assert!(p.evaluate(&new_s, Some(&old), None).is_err()); // Open→Paid not allowed
    }

    #[test]
    fn temporal_predicate_requires_witness() {
        let p = CellProgram::Predicate(vec![StateConstraint::TemporalPredicate {
            witness_index: 0,
            dsl_hash: [0xAB; 32],
        }]);
        let s = CellState::new(0);
        let err = p.evaluate(&s, None, None).unwrap_err();
        assert!(matches!(
            err,
            ProgramError::TemporalPredicateWitnessMissing { .. }
        ));
    }

    #[test]
    fn bound_delta_surfaces_cross_cell_sentinel() {
        let peer = crate::id::CellId::from_bytes([7u8; 32]);
        let p = CellProgram::Predicate(vec![StateConstraint::BoundDelta {
            local_slot: 0,
            peer_cell: peer,
            peer_slot: 0,
            delta_relation: DeltaRelation::EqualAndOpposite,
        }]);
        let s = CellState::new(0);
        let err = p.evaluate(&s, None, None).unwrap_err();
        assert!(matches!(err, ProgramError::BoundDeltaNotWired { .. }));
    }

    #[test]
    fn any_of_one_branch_must_hold() {
        let p = CellProgram::Predicate(vec![StateConstraint::AnyOf {
            variants: vec![
                SimpleStateConstraint::FieldEquals {
                    index: 0,
                    value: field_from_u64(7),
                },
                SimpleStateConstraint::FieldEquals {
                    index: 0,
                    value: field_from_u64(9),
                },
            ],
        }]);
        let mut s = CellState::new(0);
        s.fields[0] = field_from_u64(7);
        assert!(p.evaluate(&s, None, None).is_ok());
        s.fields[0] = field_from_u64(9);
        assert!(p.evaluate(&s, None, None).is_ok());
        s.fields[0] = field_from_u64(11);
        assert!(p.evaluate(&s, None, None).is_err());
    }

    #[test]
    fn capability_uniqueness_index_bounds_checked() {
        let p = CellProgram::Predicate(vec![StateConstraint::CapabilityUniqueness {
            cap_set_root_slot: 200,
        }]);
        let s = CellState::new(0);
        assert!(matches!(
            p.evaluate(&s, None, None).unwrap_err(),
            ProgramError::InvalidFieldIndex { .. }
        ));
    }

    #[test]
    fn custom_remains_fail_closed_without_runtime() {
        let p = CellProgram::Predicate(vec![StateConstraint::Custom {
            ir_hash: [0u8; 32],
            descriptor: CustomDescriptor::default(),
            reads: ReadSet::default(),
        }]);
        let s = CellState::new(0);
        assert!(matches!(
            p.evaluate(&s, None, None).unwrap_err(),
            ProgramError::CustomConstraintUnevaluable { .. }
        ));
    }

    // ── Adversarial / multi-constraint ────────────────────────────────────

    #[test]
    fn multiple_constraints_all_must_pass() {
        let p = CellProgram::Predicate(vec![
            StateConstraint::FieldGte {
                index: 0,
                value: field_from_u64(10),
            },
            StateConstraint::FieldLte {
                index: 0,
                value: field_from_u64(100),
            },
        ]);
        let mut s = CellState::new(0);
        s.fields[0] = field_from_u64(50);
        assert!(p.evaluate(&s, None, None).is_ok());
        s.fields[0] = field_from_u64(5);
        assert!(p.evaluate(&s, None, None).is_err());
        s.fields[0] = field_from_u64(200);
        assert!(p.evaluate(&s, None, None).is_err());
    }

    #[test]
    fn invalid_field_index() {
        let p = CellProgram::Predicate(vec![StateConstraint::FieldEquals {
            index: 99,
            value: field_from_u64(1),
        }]);
        let s = CellState::new(0);
        assert!(matches!(
            p.evaluate(&s, None, None).unwrap_err(),
            ProgramError::InvalidFieldIndex { index: 99 }
        ));
    }

    // ── Heyting fragment — Not / Implies ─────────────────────────────────
    // CROSS-CELL-CATEGORICAL-ANALYSIS.md §3.1 + §9.1.1.

    #[test]
    fn not_field_equals_accepts_when_field_differs() {
        // Not(FieldEquals(0, 7)) accepts when field[0] != 7.
        let p = CellProgram::Predicate(vec![StateConstraint::AnyOf {
            variants: vec![SimpleStateConstraint::Not(Box::new(
                SimpleStateConstraint::FieldEquals {
                    index: 0,
                    value: field_from_u64(7),
                },
            ))],
        }]);
        let mut s = CellState::new(0);
        s.fields[0] = field_from_u64(99);
        assert!(p.evaluate(&s, None, None).is_ok());
        // and rejects when it matches.
        s.fields[0] = field_from_u64(7);
        assert!(p.evaluate(&s, None, None).is_err());
    }

    #[test]
    fn not_write_once_permits_overwriting() {
        // The app-driver case: Not(WriteOnce(0)) flips WriteOnce's
        // semantics — overwriting is now permitted; *not* writing
        // (or writing for the first time) is rejected.
        let p = CellProgram::Predicate(vec![StateConstraint::AnyOf {
            variants: vec![SimpleStateConstraint::Not(Box::new(
                SimpleStateConstraint::WriteOnce { index: 0 },
            ))],
        }]);
        // Old slot non-zero, new differs ⇒ WriteOnce rejects ⇒ Not accepts.
        let mut old = CellState::new(0);
        old.fields[0] = field_from_u64(42);
        let mut new_s = old.clone();
        new_s.fields[0] = field_from_u64(99);
        assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
        // Old slot zero, new non-zero ⇒ WriteOnce accepts ⇒ Not rejects.
        let old_zero = CellState::new(0);
        let mut fresh = old_zero.clone();
        fresh.fields[0] = field_from_u64(42);
        assert!(p.evaluate(&fresh, Some(&old_zero), None).is_err());
    }

    #[test]
    fn not_monotonic_permits_decrement() {
        // The app-driver case: Not(Monotonic(0)) accepts decrements;
        // rejects monotone non-decreases.
        let p = CellProgram::Predicate(vec![StateConstraint::AnyOf {
            variants: vec![SimpleStateConstraint::Not(Box::new(
                SimpleStateConstraint::Monotonic { index: 0 },
            ))],
        }]);
        let mut old = CellState::new(0);
        old.fields[0] = field_from_u64(50);
        let mut new_s = old.clone();
        // Decrement — Monotonic rejects, Not accepts.
        new_s.fields[0] = field_from_u64(40);
        assert!(p.evaluate(&new_s, Some(&old), None).is_ok());
        // Increase — Monotonic accepts, Not rejects.
        new_s.fields[0] = field_from_u64(60);
        assert!(p.evaluate(&new_s, Some(&old), None).is_err());
        // Equal — Monotonic accepts (>=), Not rejects.
        new_s.fields[0] = field_from_u64(50);
        assert!(p.evaluate(&new_s, Some(&old), None).is_err());
    }

    #[test]
    fn not_propagates_unevaluable_error() {
        // Not(Immutable(0)) with no old_state and nonce > 0:
        // inner Immutable surfaces TransitionCheckRequiresOldState; Not
        // propagates the same — fail-closed on unevaluable inputs.
        let p = CellProgram::Predicate(vec![StateConstraint::AnyOf {
            variants: vec![SimpleStateConstraint::Not(Box::new(
                SimpleStateConstraint::Immutable { index: 0 },
            ))],
        }]);
        let mut s = CellState::new(0);
        s.set_nonce(5);
        let err = p.evaluate(&s, None, None).unwrap_err();
        // The error surfaces *through* the AnyOf as the last-branch
        // error — and must NOT be a vacuous Ok. We assert non-Ok and
        // that the surfaced error is the transition-check shape.
        assert!(matches!(
            err,
            ProgramError::TransitionCheckRequiresOldState { .. }
                | ProgramError::ConstraintViolated { .. }
        ));
    }

    #[test]
    fn implies_accepts_when_antecedent_false() {
        // Implies(FieldEquals(0, 7), FieldEquals(1, 9)) — antecedent
        // false means the implication is vacuously satisfied; the
        // consequent need not hold.
        let p = CellProgram::Predicate(vec![StateConstraint::implies(
            SimpleStateConstraint::FieldEquals {
                index: 0,
                value: field_from_u64(7),
            },
            SimpleStateConstraint::FieldEquals {
                index: 1,
                value: field_from_u64(9),
            },
        )]);
        let mut s = CellState::new(0);
        // field[0] != 7 ⇒ antecedent false ⇒ Implies accepts regardless of slot 1.
        s.fields[0] = field_from_u64(123);
        s.fields[1] = field_from_u64(0);
        assert!(p.evaluate(&s, None, None).is_ok());
    }

    #[test]
    fn implies_accepts_when_consequent_true() {
        let p = CellProgram::Predicate(vec![StateConstraint::implies(
            SimpleStateConstraint::FieldEquals {
                index: 0,
                value: field_from_u64(7),
            },
            SimpleStateConstraint::FieldEquals {
                index: 1,
                value: field_from_u64(9),
            },
        )]);
        let mut s = CellState::new(0);
        // antecedent true AND consequent true — Implies accepts.
        s.fields[0] = field_from_u64(7);
        s.fields[1] = field_from_u64(9);
        assert!(p.evaluate(&s, None, None).is_ok());
    }

    #[test]
    fn implies_rejects_when_antecedent_true_consequent_false() {
        let p = CellProgram::Predicate(vec![StateConstraint::implies(
            SimpleStateConstraint::FieldEquals {
                index: 0,
                value: field_from_u64(7),
            },
            SimpleStateConstraint::FieldEquals {
                index: 1,
                value: field_from_u64(9),
            },
        )]);
        let mut s = CellState::new(0);
        // antecedent true, consequent false ⇒ Implies rejects.
        s.fields[0] = field_from_u64(7);
        s.fields[1] = field_from_u64(0);
        assert!(p.evaluate(&s, None, None).is_err());
    }

    #[test]
    fn implies_via_builder_method_equals_static_constructor() {
        let antec = SimpleStateConstraint::FieldEquals {
            index: 0,
            value: field_from_u64(1),
        };
        let conseq = SimpleStateConstraint::FieldGte {
            index: 1,
            value: field_from_u64(2),
        };
        let via_method = antec.clone().implies(conseq.clone());
        let via_static = StateConstraint::implies(antec, conseq);
        assert_eq!(via_method, via_static);
    }

    #[test]
    fn not_round_trips_serde() {
        let s = SimpleStateConstraint::Not(Box::new(SimpleStateConstraint::FieldEquals {
            index: 3,
            value: field_from_u64(42),
        }));
        let bytes = postcard::to_allocvec(&s).expect("serialize");
        let back: SimpleStateConstraint = postcard::from_bytes(&bytes).expect("deserialize");
        assert_eq!(back, s);
    }

    #[test]
    fn circuit_program_requires_proof() {
        let p = CellProgram::Circuit {
            circuit_hash: [0xAB; 32],
        };
        let s = CellState::new(0);
        assert!(matches!(
            p.evaluate(&s, None, None).unwrap_err(),
            ProgramError::CircuitProofRequired { .. }
        ));
    }

    // ── Renunciation — Tier 2 §3.2 / §9.2.1 ──────────────────────────────

    #[test]
    fn renounced_accepts_legal_non_membership() {
        // Sender 0x05 is between lower=0x04 and upper=0x06 → not in
        // the set → renunciation accepts. Post-hardening, the bare 96-byte
        // neighbor proof is rejected (wide-bracket forge closed); the positive
        // path now ships a `NonMembershipProofV2` with a real Merkle-adjacency
        // proof, verified against a registry that has an adjacency verifier
        // installed (mocked here; the production adjacency STARK is exercised
        // end-to-end in dregg-turn).
        let candidate = [0x05u8; 32];
        let proof_bytes = honest_renunciation_v2(&[0xAB; 32], [0x04u8; 32], [0x06u8; 32]);
        let registry = registry_with_mock_adjacency();
        let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
            kind: WitnessKindTag::ProofBytes,
            bytes: &proof_bytes,
        }];
        let bundle = WitnessBundle {
            blobs: &blobs,
            registry: Some(&registry),
        };

        let p = CellProgram::Predicate(vec![StateConstraint::Renounced {
            set: RenouncedSet::BlindedSet {
                commitment: [0xAB; 32],
            },
        }]);
        let s = CellState::new(0);
        let ctx = ctx_sender(candidate, 0);
        p.evaluate_full(&s, None, Some(&ctx), &TransitionMeta::wildcard(), &bundle)
            .expect("legal renunciation accepts");
    }

    #[test]
    fn renounced_rejects_when_prover_is_in_set() {
        // Adversarial: candidate == lower neighbor → the prover IS in
        // the set but is forging a renunciation. Must reject.
        let candidate = [0x05u8; 32];
        let proof = crate::predicate::NonMembershipNeighborProof::new(
            &[0xAB; 32],
            [0x05u8; 32], // candidate matches lower → in set
            [0x06u8; 32],
        );
        let proof_bytes = proof.to_bytes();
        let registry = crate::predicate::WitnessedPredicateRegistry::with_stubs();
        let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
            kind: WitnessKindTag::ProofBytes,
            bytes: &proof_bytes,
        }];
        let bundle = WitnessBundle {
            blobs: &blobs,
            registry: Some(&registry),
        };

        let p = CellProgram::Predicate(vec![StateConstraint::Renounced {
            set: RenouncedSet::BlindedSet {
                commitment: [0xAB; 32],
            },
        }]);
        let s = CellState::new(0);
        let ctx = ctx_sender(candidate, 0);
        let err = p
            .evaluate_full(&s, None, Some(&ctx), &TransitionMeta::wildcard(), &bundle)
            .unwrap_err();
        assert!(matches!(
            err,
            ProgramError::WitnessedPredicateRejected {
                kind_name: "NonMembership",
                ..
            }
        ));
    }

    #[test]
    fn renounced_rejects_forged_adjacency_tag() {
        let candidate = [0x05u8; 32];
        let proof = crate::predicate::NonMembershipNeighborProof {
            lower: [0x04u8; 32],
            upper: [0x06u8; 32],
            adjacency_tag: [0u8; 32], // forged (zero != commitment-keyed tag)
        };
        let proof_bytes = proof.to_bytes();
        let registry = crate::predicate::WitnessedPredicateRegistry::with_stubs();
        let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
            kind: WitnessKindTag::ProofBytes,
            bytes: &proof_bytes,
        }];
        let bundle = WitnessBundle {
            blobs: &blobs,
            registry: Some(&registry),
        };

        let p = CellProgram::Predicate(vec![StateConstraint::Renounced {
            set: RenouncedSet::BlindedSet {
                commitment: [0xAB; 32],
            },
        }]);
        let s = CellState::new(0);
        let ctx = ctx_sender(candidate, 0);
        let err = p
            .evaluate_full(&s, None, Some(&ctx), &TransitionMeta::wildcard(), &bundle)
            .unwrap_err();
        assert!(matches!(
            err,
            ProgramError::WitnessedPredicateRejected {
                kind_name: "NonMembership",
                ..
            }
        ));
    }

    #[test]
    fn renounced_requires_sender_in_ctx() {
        let registry = crate::predicate::WitnessedPredicateRegistry::with_stubs();
        let bundle = WitnessBundle {
            blobs: &[],
            registry: Some(&registry),
        };
        let p = CellProgram::Predicate(vec![StateConstraint::Renounced {
            set: RenouncedSet::BlindedSet {
                commitment: [0xAB; 32],
            },
        }]);
        let s = CellState::new(0);
        // No ctx at all.
        let err = p
            .evaluate_full(&s, None, None, &TransitionMeta::wildcard(), &bundle)
            .unwrap_err();
        assert!(matches!(err, ProgramError::MissingContextField { .. }));
        // Ctx without sender.
        let bare = EvalContext::default();
        let err = p
            .evaluate_full(&s, None, Some(&bare), &TransitionMeta::wildcard(), &bundle)
            .unwrap_err();
        assert!(matches!(err, ProgramError::MissingContextField { .. }));
    }

    #[test]
    fn renounced_public_root_reads_slot_commitment() {
        // PublicRoot variant pulls commitment from a state slot.
        let candidate = [0x05u8; 32];
        // Slot 3 carries the set root [0xCC; 32] (see below). Post-hardening
        // positive path: a NonMembershipProofV2 bound to that root, with a real
        // Merkle-adjacency proof (mocked here), verified against a registry that
        // has the adjacency verifier installed.
        let proof_bytes = honest_renunciation_v2(&[0xCC; 32], [0x04u8; 32], [0x06u8; 32]);
        let registry = registry_with_mock_adjacency();
        let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
            kind: WitnessKindTag::ProofBytes,
            bytes: &proof_bytes,
        }];
        let bundle = WitnessBundle {
            blobs: &blobs,
            registry: Some(&registry),
        };

        let p = CellProgram::Predicate(vec![StateConstraint::Renounced {
            set: RenouncedSet::PublicRoot { set_root_index: 3 },
        }]);
        let mut s = CellState::new(0);
        s.fields[3] = [0xCC; 32]; // set root from slot
        let ctx = ctx_sender(candidate, 0);
        p.evaluate_full(&s, None, Some(&ctx), &TransitionMeta::wildcard(), &bundle)
            .expect("legal renunciation via PublicRoot accepts");
    }

    // ─────────────────────────────────────────────────────────────────────
    // AUDIT adversarial tests (FAIL-before / PASS-after)
    // ─────────────────────────────────────────────────────────────────────

    // Item 2: RateLimit no longer trusts a self-attested `RateLimitCount`
    // witness blob. A submitter who attests count=0 while over the limit
    // must be rejected — the count comes ONLY from ctx.sender_epoch_count.
    #[test]
    fn rate_limit_ignores_self_attested_count_witness() {
        let p = CellProgram::Predicate(vec![StateConstraint::RateLimit {
            max_per_epoch: 3,
            epoch_duration: 100,
        }]);
        let s = CellState::new(0);
        let sender = [9u8; 32];

        // Adversary attests count=0 in the witness blob while the
        // authoritative ctx count is 5 (over the cap). Pre-fix this
        // accepted (ctx==0 fallthrough never happened, but a submitter
        // setting ctx-bypassing self-attest=0 on the FIRST action of an
        // epoch — when the real counter is 0 — would always pass).
        let zero = 0u32.to_le_bytes();
        let blobs: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
            kind: WitnessKindTag::RateLimitCount,
            bytes: &zero,
        }];
        let bundle = WitnessBundle {
            blobs: &blobs,
            registry: None,
        };
        // Authoritative ctx count is over the cap → MUST reject, the
        // self-attested 0 must be ignored.
        let over = ctx_sender(sender, 5);
        let err = p
            .evaluate_full(&s, None, Some(&over), &TransitionMeta::wildcard(), &bundle)
            .expect_err("over-cap ctx count must reject despite self-attested 0");
        assert!(matches!(err, ProgramError::ConstraintViolated { .. }));

        // And when ctx count is 0 (first action of the epoch), a witness
        // blob claiming a huge count must NOT be able to "use up" the
        // budget either — the witness is simply ignored, so it accepts.
        let huge = 999u32.to_le_bytes();
        let blobs2: [WitnessBlobView<'_>; 1] = [WitnessBlobView {
            kind: WitnessKindTag::RateLimitCount,
            bytes: &huge,
        }];
        let bundle2 = WitnessBundle {
            blobs: &blobs2,
            registry: None,
        };
        let zero_ctx = ctx_sender(sender, 0);
        p.evaluate_full(
            &s,
            None,
            Some(&zero_ctx),
            &TransitionMeta::wildcard(),
            &bundle2,
        )
        .expect("ctx count 0 accepts regardless of witness blob");
    }

    // Item 1: CapabilityUniqueness fails CLOSED in the scalar evaluator —
    // it can never silently pass. The real enforcement lives in the
    // executor (turn/tests covers the structural cap-set path).
    #[test]
    fn capability_uniqueness_scalar_fails_closed() {
        let p = CellProgram::Predicate(vec![StateConstraint::CapabilityUniqueness {
            cap_set_root_slot: 0,
        }]);
        let mut s = CellState::new(0);
        s.fields[0] = [0xAB; 32]; // non-zero root; still must fail closed
        let err = p.evaluate(&s, None, None).unwrap_err();
        assert!(
            matches!(
                err,
                ProgramError::CapabilityUniquenessRequiresExecutor { .. }
            ),
            "scalar CapabilityUniqueness must fail closed, got {err:?}"
        );
    }

    // Item 4: a mismatched / ambiguous witness must be rejected rather
    // than cross-matched. Two ProofBytes blobs make the binding ambiguous
    // for Renounced → fail closed (pre-fix the first-of-kind scan would
    // silently pick blob 0).
    #[test]
    fn renounced_ambiguous_witness_rejected() {
        let candidate = [0x05u8; 32];
        let proof = crate::predicate::NonMembershipNeighborProof::new(
            &[0xCC; 32],
            [0x04u8; 32],
            [0x06u8; 32],
        );
        let pb = proof.to_bytes();
        let registry = crate::predicate::WitnessedPredicateRegistry::with_stubs();
        // TWO ProofBytes blobs — ambiguous.
        let blobs: [WitnessBlobView<'_>; 2] = [
            WitnessBlobView {
                kind: WitnessKindTag::ProofBytes,
                bytes: &pb,
            },
            WitnessBlobView {
                kind: WitnessKindTag::ProofBytes,
                bytes: &pb,
            },
        ];
        let bundle = WitnessBundle {
            blobs: &blobs,
            registry: Some(&registry),
        };
        let p = CellProgram::Predicate(vec![StateConstraint::Renounced {
            set: RenouncedSet::PublicRoot { set_root_index: 3 },
        }]);
        let mut s = CellState::new(0);
        s.fields[3] = [0xCC; 32];
        let ctx = ctx_sender(candidate, 0);
        let err = p
            .evaluate_full(&s, None, Some(&ctx), &TransitionMeta::wildcard(), &bundle)
            .expect_err("ambiguous double-ProofBytes witness must reject");
        assert!(
            matches!(
                err,
                ProgramError::WitnessedPredicateRejected {
                    kind_name: "NonMembership",
                    ..
                }
            ),
            "expected ambiguity rejection, got {err:?}"
        );
    }

    // Item 4: TemporalPredicate binds its proof explicitly at
    // `witness_index + 1`. A proof placed elsewhere (or of the wrong
    // kind at that slot) must be rejected, not first-of-kind matched.
    #[test]
    fn temporal_predicate_proof_must_be_at_explicit_index() {
        let registry = crate::predicate::WitnessedPredicateRegistry::with_stubs();
        let input = [1u8; 8];
        let proof = [2u8; 64];
        // input at index 0, but proof placed at index 2 (not 1) — the
        // explicit slot (index 1) is the wrong kind.
        let wrong_kind = [9u8; 4];
        let blobs: [WitnessBlobView<'_>; 3] = [
            WitnessBlobView {
                kind: WitnessKindTag::Cleartext,
                bytes: &input,
            },
            WitnessBlobView {
                kind: WitnessKindTag::RateLimitCount,
                bytes: &wrong_kind,
            },
            WitnessBlobView {
                kind: WitnessKindTag::ProofBytes,
                bytes: &proof,
            },
        ];
        let bundle = WitnessBundle {
            blobs: &blobs,
            registry: Some(&registry),
        };
        let p = CellProgram::Predicate(vec![StateConstraint::TemporalPredicate {
            witness_index: 0,
            dsl_hash: [0xAB; 32],
        }]);
        let s = CellState::new(0);
        let err = p
            .evaluate_full(&s, None, None, &TransitionMeta::wildcard(), &bundle)
            .expect_err("proof not at witness_index+1 must reject");
        assert!(
            matches!(
                err,
                ProgramError::WitnessedPredicateRejected {
                    kind_name: "Temporal",
                    ..
                }
            ),
            "expected explicit-index rejection, got {err:?}"
        );

        // Now place the proof at the correct explicit slot (index 1) →
        // the Temporal stub verifier accepts.
        let blobs_ok: [WitnessBlobView<'_>; 2] = [
            WitnessBlobView {
                kind: WitnessKindTag::Cleartext,
                bytes: &input,
            },
            WitnessBlobView {
                kind: WitnessKindTag::ProofBytes,
                bytes: &proof,
            },
        ];
        let bundle_ok = WitnessBundle {
            blobs: &blobs_ok,
            registry: Some(&registry),
        };
        p.evaluate_full(&s, None, None, &TransitionMeta::wildcard(), &bundle_ok)
            .expect("proof at witness_index+1 accepts via stub verifier");
    }

    // ─── Turn-context atoms (CELL-PROGRAM-LANGUAGE.md §3) ───

    /// The polis council shape: "approval slot 3 may change only if the
    /// turn's sender is member A" — `AnyOf[Immutable{3}, SenderIs{a}]`.
    /// This is THE per-slot actor binding (polis gap 5) at the program
    /// level.
    #[test]
    fn sender_is_binds_slot_to_actor() {
        let member_a = [0xAAu8; 32];
        let member_b = [0xBBu8; 32];
        let program = CellProgram::Predicate(vec![StateConstraint::AnyOf {
            variants: vec![
                SimpleStateConstraint::Immutable { index: 3 },
                SimpleStateConstraint::SenderIs { pk: member_a },
            ],
        }]);
        let old = CellState::new(0);
        let mut flipped = old.clone();
        flipped.fields[3] = field_from_u64(1);

        // Member A flips their own slot: admitted.
        assert!(
            program
                .evaluate(&flipped, Some(&old), Some(&ctx_sender(member_a, 0)))
                .is_ok(),
            "the bound actor may flip the slot"
        );
        // Member B (a real key, a real capability — just NOT the bound
        // identity) flips A's slot: rejected.
        assert!(
            program
                .evaluate(&flipped, Some(&old), Some(&ctx_sender(member_b, 0)))
                .is_err(),
            "another actor cannot flip the bound slot"
        );
        // A turn by member B that does NOT touch the slot: admitted via
        // the Immutable disjunct (propose/certify/execute stay open).
        assert!(
            program
                .evaluate(&old, Some(&old), Some(&ctx_sender(member_b, 0)))
                .is_ok(),
            "untouched slot admits any sender"
        );
        // No sender in context while flipping: fail-closed.
        assert!(
            program
                .evaluate(&flipped, Some(&old), Some(&ctx_at(5)))
                .is_err(),
            "missing sender fails closed"
        );
    }

    #[test]
    fn sender_in_slot_binds_to_slot_held_identity() {
        let owner = [0x11u8; 32];
        let thief = [0x22u8; 32];
        let program = CellProgram::Predicate(vec![StateConstraint::SenderInSlot { index: 2 }]);
        let mut state = CellState::new(0);
        state.fields[2] = owner;
        assert!(
            program
                .evaluate(&state, None, Some(&ctx_sender(owner, 0)))
                .is_ok()
        );
        assert!(
            program
                .evaluate(&state, None, Some(&ctx_sender(thief, 0)))
                .is_err()
        );
        // Out-of-range slot: structural error, not a pass.
        let bad = CellProgram::Predicate(vec![StateConstraint::SenderInSlot { index: 99 }]);
        assert!(matches!(
            bad.evaluate(&state, None, Some(&ctx_sender(owner, 0))),
            Err(ProgramError::InvalidFieldIndex { index: 99 })
        ));
    }

    /// Balance atoms read the cell's own sealed balance — the
    /// "resolve drains the full balance" tooth becomes program-enforced:
    /// `state == RESOLVED ⇒ balance == 0` as
    /// `AnyOf[Not(state==RESOLVED), BalanceLte{0}]`.
    #[test]
    fn balance_atoms_see_own_balance() {
        let resolved = field_from_u64(2);
        let drain_tooth = CellProgram::Predicate(vec![StateConstraint::AnyOf {
            variants: vec![
                SimpleStateConstraint::Not(Box::new(SimpleStateConstraint::FieldEquals {
                    index: 0,
                    value: resolved,
                })),
                SimpleStateConstraint::BalanceLte { max: 0 },
            ],
        }]);
        // Resolved with a drained balance: admitted.
        let mut drained = CellState::new(0);
        drained.fields[0] = resolved;
        drained.set_balance(0);
        assert!(drain_tooth.evaluate(&drained, None, None).is_ok());
        // Resolved while still holding value: rejected (stranded /
        // partially-drained settlement cannot commit).
        let mut holding = drained.clone();
        holding.set_balance(40);
        assert!(drain_tooth.evaluate(&holding, None, None).is_err());
        // Not resolved: balance unconstrained.
        let mut open = CellState::new(0);
        open.fields[0] = field_from_u64(1);
        open.set_balance(40);
        assert!(drain_tooth.evaluate(&open, None, None).is_ok());

        // Solvency floor: BalanceGte.
        let floor = CellProgram::Predicate(vec![StateConstraint::BalanceGte { min: 10 }]);
        let mut funded = CellState::new(0);
        funded.set_balance(10);
        assert!(floor.evaluate(&funded, None, None).is_ok());
        funded.set_balance(9);
        assert!(floor.evaluate(&funded, None, None).is_err());
    }

    /// Apps gap 3 — the multi-admin actor binding. `SenderMemberOf` is the
    /// clean form of `AnyOf[SenderIs{a}, SenderIs{b}, …]`. Mirrors the Lean
    /// keystone `evalSimpleCtx_senderMemberOf_iff`: admits IFF a sender is in
    /// context AND on the board; off-board or no-context fail closed.
    #[test]
    fn sender_member_of_binds_multi_admin() {
        let alice = [0x11u8; 32];
        let bob = [0x22u8; 32];
        let mallory = [0x99u8; 32];
        let board = CellProgram::Predicate(vec![StateConstraint::SenderMemberOf {
            members: vec![alice, bob],
        }]);
        let st = CellState::new(0);
        // A board member is admitted.
        assert!(board
            .evaluate(&st, None, Some(&ctx_sender(alice, 0)))
            .is_ok());
        assert!(board.evaluate(&st, None, Some(&ctx_sender(bob, 0))).is_ok());
        // A non-member is rejected (ConstraintViolated, not a pass).
        assert!(matches!(
            board.evaluate(&st, None, Some(&ctx_sender(mallory, 0))),
            Err(ProgramError::ConstraintViolated { .. })
        ));
        // No sender in context ⇒ MissingContextField (fail-closed).
        assert!(matches!(
            board.evaluate(&st, None, Some(&ctx_at(7))),
            Err(ProgramError::MissingContextField { field: "sender" })
        ));
        // No context at all ⇒ MissingContextField.
        assert!(matches!(
            board.evaluate(&st, None, None),
            Err(ProgramError::MissingContextField { field: "sender" })
        ));

        // The multi-admin per-slot binding: slot 0 flips only for a board
        // member, but ANY sender may leave it alone (the council ceremony
        // stays open). `AnyOf[Immutable{0}, SenderMemberOf{board}]`.
        let bound = CellProgram::Predicate(vec![StateConstraint::AnyOf {
            variants: vec![
                SimpleStateConstraint::Immutable { index: 0 },
                SimpleStateConstraint::SenderMemberOf {
                    members: vec![alice, bob],
                },
            ],
        }]);
        let mut old = CellState::new(0);
        old.fields[0] = field_from_u64(5);
        let mut flipped = old.clone();
        flipped.fields[0] = field_from_u64(6);
        // Mallory leaving the slot ALONE is admitted (Immutable branch).
        assert!(bound
            .evaluate(&old, Some(&old), Some(&ctx_sender(mallory, 0)))
            .is_ok());
        // Mallory FLIPPING the slot is rejected (neither branch passes).
        assert!(bound
            .evaluate(&flipped, Some(&old), Some(&ctx_sender(mallory, 0)))
            .is_err());
        // Alice (a member) flipping the slot is admitted (member branch).
        assert!(bound
            .evaluate(&flipped, Some(&old), Some(&ctx_sender(alice, 0)))
            .is_ok());
    }

    /// Apps gap 4 — the per-turn balance RATE gates. `BalanceDeltaLte` /
    /// `BalanceDeltaGte` bound `new.balance − old.balance` (the pre-balance is
    /// the executor's `old_state`). Mirrors the Lean keystones
    /// `evalSimpleCtx_balanceDeltaLe_iff` / `_balanceDeltaGe_iff`. SIGNED
    /// bounds (a negative `max` forces a loss). Fail-closed without a pre-state.
    #[test]
    fn balance_delta_atoms_bound_the_rate() {
        // Ceiling: may gain at most 10 per turn.
        let ceil = CellProgram::Predicate(vec![StateConstraint::BalanceDeltaLte { max: 10 }]);
        let mut old = CellState::new(0);
        old.set_balance(100);
        let mut up5 = old.clone();
        up5.set_balance(105); // +5 ≤ 10 → admit
        assert!(ceil.evaluate(&up5, Some(&old), None).is_ok());
        let mut up20 = old.clone();
        up20.set_balance(120); // +20 > 10 → reject
        assert!(matches!(
            ceil.evaluate(&up20, Some(&old), None),
            Err(ProgramError::ConstraintViolated { .. })
        ));
        // A drain (negative delta) trivially satisfies a positive ceiling.
        let mut down = old.clone();
        down.set_balance(50); // −50 ≤ 10 → admit
        assert!(ceil.evaluate(&down, Some(&old), None).is_ok());

        // Floor: may LOSE at most 30 per turn (delta ≥ −30).
        let floor = CellProgram::Predicate(vec![StateConstraint::BalanceDeltaGte { min: -30 }]);
        let mut lose20 = old.clone();
        lose20.set_balance(80); // −20 ≥ −30 → admit
        assert!(floor.evaluate(&lose20, Some(&old), None).is_ok());
        let mut lose40 = old.clone();
        lose40.set_balance(60); // −40 < −30 → reject
        assert!(matches!(
            floor.evaluate(&lose40, Some(&old), None),
            Err(ProgramError::ConstraintViolated { .. })
        ));

        // Fail-closed: a rate gate without a pre-state (no old_state) cannot be
        // satisfied — TransitionCheckRequiresOldState (both endpoints needed).
        assert!(matches!(
            ceil.evaluate(&up5, None, None),
            Err(ProgramError::TransitionCheckRequiresOldState { .. })
        ));
    }

    /// Apps gap 2 — the multi-field delta gate. `AffineDeltaLe` bounds
    /// `Σ kᵢ·(new[fᵢ] − old[fᵢ]) ≤ c` (a treasury's COMBINED per-turn
    /// outflow across two spend slots). Mirrors the Lean keystone
    /// `evalConstraint_affineDeltaLe_iff`. Fail-closed without a pre-state.
    #[test]
    fn affine_delta_le_bounds_combined_outflow() {
        // out_a (slot 1) + out_b (slot 2) may grow by at most 50 per turn.
        let budget = CellProgram::Predicate(vec![StateConstraint::AffineDeltaLe {
            terms: vec![(1, 1), (1, 2)],
            c: 50,
        }]);
        let mut old = CellState::new(0);
        old.fields[1] = field_from_u64(10);
        old.fields[2] = field_from_u64(20);
        // Δout_a=15, Δout_b=20 ⇒ sum 35 ≤ 50 → admit.
        let mut within = old.clone();
        within.fields[1] = field_from_u64(25);
        within.fields[2] = field_from_u64(40);
        assert!(budget.evaluate(&within, Some(&old), None).is_ok());
        // Δout_a=30, Δout_b=30 ⇒ sum 60 > 50 → reject (combined cap, even
        // though neither single slot is obviously out of bounds).
        let mut over = old.clone();
        over.fields[1] = field_from_u64(40);
        over.fields[2] = field_from_u64(50);
        assert!(matches!(
            budget.evaluate(&over, Some(&old), None),
            Err(ProgramError::ConstraintViolated { .. })
        ));
        // Fail-closed without a pre-state.
        assert!(matches!(
            budget.evaluate(&within, None, None),
            Err(ProgramError::TransitionCheckRequiresOldState { .. })
        ));
    }

    /// Blueprint gap 1: the committed-value knowledge gate under a state
    /// guard — `state == RELEASED ⇒ PreimageGate` — now expressible
    /// because `PreimageGate` is a `SimpleStateConstraint`.
    #[test]
    fn preimage_gate_composes_under_state_guard() {
        let released = field_from_u64(2);
        let preimage = [0x5Au8; 32];
        let commitment = *blake3::hash(&preimage).as_bytes();
        let gate = CellProgram::Predicate(vec![StateConstraint::AnyOf {
            variants: vec![
                SimpleStateConstraint::Not(Box::new(SimpleStateConstraint::FieldEquals {
                    index: 0,
                    value: released,
                })),
                SimpleStateConstraint::PreimageGate {
                    commitment_index: 4,
                    hash_kind: HashKind::Blake3,
                },
            ],
        }]);
        let mut state = CellState::new(0);
        state.fields[0] = released;
        state.fields[4] = commitment;

        let blobs = [WitnessBlobView {
            kind: WitnessKindTag::Preimage32,
            bytes: &preimage,
        }];
        let with_reveal = WitnessBundle {
            blobs: &blobs,
            registry: None,
        };
        // Release with the correct reveal: admitted.
        assert!(
            gate.evaluate_full(
                &state,
                None,
                None,
                &TransitionMeta::wildcard(),
                &with_reveal
            )
            .is_ok()
        );
        // Release without a reveal: rejected (fail-closed inside AnyOf).
        assert!(
            gate.evaluate_full(
                &state,
                None,
                None,
                &TransitionMeta::wildcard(),
                &WitnessBundle::empty()
            )
            .is_err()
        );
        // Wrong preimage: rejected.
        let wrong = [0x66u8; 32];
        let blobs_wrong = [WitnessBlobView {
            kind: WitnessKindTag::Preimage32,
            bytes: &wrong,
        }];
        let with_wrong = WitnessBundle {
            blobs: &blobs_wrong,
            registry: None,
        };
        assert!(
            gate.evaluate_full(&state, None, None, &TransitionMeta::wildcard(), &with_wrong)
                .is_err()
        );
        // Not released: the gate is dormant, no reveal needed.
        let mut open = state.clone();
        open.fields[0] = field_from_u64(1);
        assert!(
            gate.evaluate_full(
                &open,
                None,
                None,
                &TransitionMeta::wildcard(),
                &WitnessBundle::empty()
            )
            .is_ok()
        );
    }

    /// VIEW-PROJECTION TOTALITY PIN — the live-view seam must never reopen.
    ///
    /// Constructs one instance of EVERY `StateConstraint` variant (and every
    /// `SimpleStateConstraint` variant), projects each through `to_view`,
    /// and pins the serialized `kind` tag. Two teeth:
    ///
    /// 1. The `to_view` match itself has no wildcard arm, so adding a
    ///    variant without a projection is a COMPILE error.
    /// 2. This test exhaustively matches over the same constructor list, so
    ///    a projection that maps a variant to the WRONG kind tag (or drops
    ///    its payload tag) fails here.
    #[test]
    fn view_projection_is_total_and_kind_tagged() {
        use crate::predicate::{InputRef, WitnessedPredicate, WitnessedPredicateKind};

        let fe = field_from_u64(7);
        let all: Vec<(StateConstraint, &str)> = vec![
            (
                StateConstraint::FieldEquals {
                    index: 0,
                    value: fe,
                },
                "FieldEquals",
            ),
            (
                StateConstraint::FieldGte {
                    index: 0,
                    value: fe,
                },
                "FieldGte",
            ),
            (
                StateConstraint::FieldLte {
                    index: 0,
                    value: fe,
                },
                "FieldLte",
            ),
            (
                StateConstraint::FieldLteField {
                    left_index: 0,
                    right_index: 1,
                },
                "FieldLteField",
            ),
            (
                StateConstraint::FieldLteOther {
                    index: 0,
                    other: 1,
                    delta: -3,
                },
                "FieldLteOther",
            ),
            (
                StateConstraint::SumEquals {
                    indices: vec![0, 1],
                    value: fe,
                },
                "SumEquals",
            ),
            (StateConstraint::WriteOnce { index: 1 }, "WriteOnce"),
            (StateConstraint::Immutable { index: 1 }, "Immutable"),
            (StateConstraint::Monotonic { index: 1 }, "Monotonic"),
            (
                StateConstraint::StrictMonotonic { index: 1 },
                "StrictMonotonic",
            ),
            (
                StateConstraint::BoundedBy {
                    index: 1,
                    witness_index: 2,
                },
                "BoundedBy",
            ),
            (
                StateConstraint::FieldDelta {
                    index: 1,
                    delta: fe,
                },
                "FieldDelta",
            ),
            (
                StateConstraint::FieldDeltaInRange {
                    index: 1,
                    min_delta: fe,
                    max_delta: fe,
                },
                "FieldDeltaInRange",
            ),
            (
                StateConstraint::FieldGteHeight {
                    index: 1,
                    offset: 0,
                },
                "FieldGteHeight",
            ),
            (
                StateConstraint::FieldLteHeight {
                    index: 1,
                    offset: 0,
                },
                "FieldLteHeight",
            ),
            (
                StateConstraint::SumEqualsAcross {
                    input_fields: vec![0],
                    output_fields: vec![1],
                },
                "SumEqualsAcross",
            ),
            (
                StateConstraint::SenderAuthorized {
                    set: AuthorizedSet::BlindedSet {
                        commitment: [9u8; 32],
                    },
                },
                "SenderAuthorized",
            ),
            (
                StateConstraint::CapabilityUniqueness {
                    cap_set_root_slot: 3,
                },
                "CapabilityUniqueness",
            ),
            (
                StateConstraint::RateLimit {
                    max_per_epoch: 4,
                    epoch_duration: 100,
                },
                "RateLimit",
            ),
            (
                StateConstraint::RateLimitBySum {
                    slot_index: 1,
                    max_sum_per_epoch: 10,
                    epoch_duration: 100,
                },
                "RateLimitBySum",
            ),
            (
                StateConstraint::TemporalGate {
                    not_before: Some(5),
                    not_after: None,
                },
                "TemporalGate",
            ),
            (
                StateConstraint::PreimageGate {
                    commitment_index: 2,
                    hash_kind: HashKind::Poseidon2,
                },
                "PreimageGate",
            ),
            (
                StateConstraint::MonotonicSequence { seq_index: 0 },
                "MonotonicSequence",
            ),
            (
                StateConstraint::AllowedTransitions {
                    slot_index: 0,
                    allowed: vec![(field_from_u64(0), field_from_u64(1))],
                },
                "AllowedTransitions",
            ),
            (
                StateConstraint::TemporalPredicate {
                    witness_index: 0,
                    dsl_hash: [1u8; 32],
                },
                "TemporalPredicate",
            ),
            (
                StateConstraint::BoundDelta {
                    local_slot: 0,
                    peer_cell: crate::id::CellId([2u8; 32]),
                    peer_slot: 1,
                    delta_relation: DeltaRelation::EqualAndOpposite,
                },
                "BoundDelta",
            ),
            (
                StateConstraint::AnyOf {
                    variants: vec![
                        SimpleStateConstraint::Monotonic { index: 0 },
                        SimpleStateConstraint::Not(Box::new(SimpleStateConstraint::FieldEquals {
                            index: 0,
                            value: fe,
                        })),
                    ],
                },
                "AnyOf",
            ),
            (
                StateConstraint::Witnessed {
                    wp: WitnessedPredicate {
                        kind: WitnessedPredicateKind::Dfa,
                        commitment: [3u8; 32],
                        input_ref: InputRef::Sender,
                        proof_witness_index: 0,
                    },
                },
                "Witnessed",
            ),
            (
                StateConstraint::Renounced {
                    set: RenouncedSet::BlindedSet {
                        commitment: [4u8; 32],
                    },
                },
                "Renounced",
            ),
            (
                StateConstraint::MemberOf {
                    index: 0,
                    set: vec![1, 2, 3],
                },
                "MemberOf",
            ),
            (
                StateConstraint::PrefixOf {
                    seg_indices: vec![0, 1],
                    prefix: vec![42],
                },
                "PrefixOf",
            ),
            (
                StateConstraint::InRangeTwoSided {
                    index: 0,
                    lo: 1,
                    hi: 9,
                },
                "InRangeTwoSided",
            ),
            (
                StateConstraint::DeltaBounded { index: 0, d: 5 },
                "DeltaBounded",
            ),
            (
                StateConstraint::AffineLe {
                    terms: vec![(2, 2), (-1, 3)],
                    c: 0,
                },
                "AffineLe",
            ),
            (
                StateConstraint::AffineEq {
                    terms: vec![(1, 0), (1, 1)],
                    c: 10,
                },
                "AffineEq",
            ),
            (
                StateConstraint::Reachable {
                    from_index: 0,
                    to_label: 9,
                    edges: vec![(1, 9)],
                },
                "Reachable",
            ),
            (
                StateConstraint::AllOf {
                    variants: vec![SimpleStateConstraint::WriteOnce { index: 0 }],
                },
                "AllOf",
            ),
            (
                StateConstraint::Custom {
                    ir_hash: [5u8; 32],
                    descriptor: CustomDescriptor::default(),
                    reads: ReadSet::default(),
                },
                "Custom",
            ),
            (StateConstraint::SenderIs { pk: [7u8; 32] }, "SenderIs"),
            (StateConstraint::SenderInSlot { index: 2 }, "SenderInSlot"),
            (StateConstraint::BalanceGte { min: 10 }, "BalanceGte"),
            (StateConstraint::BalanceLte { max: 0 }, "BalanceLte"),
            (
                StateConstraint::KeyRotationGate {
                    digest_slot: 1,
                    current_slot: 2,
                    last_rotated_slot: 3,
                    cooling_period: 50,
                    hash_kind: HashKind::Blake3,
                },
                "KeyRotationGate",
            ),
            (
                StateConstraint::HeapField {
                    key: 99,
                    atom: HeapAtom::Monotonic,
                },
                "HeapField",
            ),
            (
                StateConstraint::DelegationEpochEquals { index: 2 },
                "DelegationEpochEquals",
            ),
            (
                StateConstraint::CountGe {
                    threshold: 2,
                    set_commitment_slot: 5,
                },
                "CountGe",
            ),
            (
                StateConstraint::SenderMemberOf {
                    members: vec![[1u8; 32], [2u8; 32]],
                },
                "SenderMemberOf",
            ),
            (StateConstraint::BalanceDeltaLte { max: 10 }, "BalanceDeltaLte"),
            (StateConstraint::BalanceDeltaGte { min: -5 }, "BalanceDeltaGte"),
            (
                StateConstraint::AffineDeltaLe {
                    terms: vec![(1, 1), (1, 2)],
                    c: 50,
                },
                "AffineDeltaLe",
            ),
        ];

        // COVERAGE TOOTH: this match must name every variant exactly once.
        // Adding a `StateConstraint` variant forces an arm here AND a
        // projection arm in `to_view` (both are non-wildcard matches).
        for (sc, _) in &all {
            match sc {
                StateConstraint::FieldEquals { .. }
                | StateConstraint::FieldGte { .. }
                | StateConstraint::FieldLte { .. }
                | StateConstraint::FieldLteField { .. }
                | StateConstraint::FieldLteOther { .. }
                | StateConstraint::SumEquals { .. }
                | StateConstraint::WriteOnce { .. }
                | StateConstraint::Immutable { .. }
                | StateConstraint::Monotonic { .. }
                | StateConstraint::StrictMonotonic { .. }
                | StateConstraint::BoundedBy { .. }
                | StateConstraint::FieldDelta { .. }
                | StateConstraint::FieldDeltaInRange { .. }
                | StateConstraint::FieldGteHeight { .. }
                | StateConstraint::FieldLteHeight { .. }
                | StateConstraint::SumEqualsAcross { .. }
                | StateConstraint::SenderAuthorized { .. }
                | StateConstraint::CapabilityUniqueness { .. }
                | StateConstraint::RateLimit { .. }
                | StateConstraint::RateLimitBySum { .. }
                | StateConstraint::TemporalGate { .. }
                | StateConstraint::PreimageGate { .. }
                | StateConstraint::MonotonicSequence { .. }
                | StateConstraint::AllowedTransitions { .. }
                | StateConstraint::TemporalPredicate { .. }
                | StateConstraint::BoundDelta { .. }
                | StateConstraint::AnyOf { .. }
                | StateConstraint::Witnessed { .. }
                | StateConstraint::Renounced { .. }
                | StateConstraint::MemberOf { .. }
                | StateConstraint::PrefixOf { .. }
                | StateConstraint::InRangeTwoSided { .. }
                | StateConstraint::DeltaBounded { .. }
                | StateConstraint::AffineLe { .. }
                | StateConstraint::AffineEq { .. }
                | StateConstraint::Reachable { .. }
                | StateConstraint::AllOf { .. }
                | StateConstraint::Custom { .. }
                | StateConstraint::SenderIs { .. }
                | StateConstraint::SenderInSlot { .. }
                | StateConstraint::BalanceGte { .. }
                | StateConstraint::BalanceLte { .. }
                | StateConstraint::KeyRotationGate { .. }
                | StateConstraint::HeapField { .. }
                | StateConstraint::DelegationEpochEquals { .. }
                | StateConstraint::CountGe { .. }
                | StateConstraint::SenderMemberOf { .. }
                | StateConstraint::BalanceDeltaLte { .. }
                | StateConstraint::BalanceDeltaGte { .. }
                | StateConstraint::AffineDeltaLe { .. } => {}
            }
        }

        for (sc, expected_kind) in &all {
            let view = sc.to_view();
            let json = serde_json::to_value(&view).expect("view serializes");
            assert_eq!(
                json.get("kind").and_then(|k| k.as_str()),
                Some(*expected_kind),
                "view kind tag for {sc:?}"
            );
        }

        // Semantic-payload spot checks for the newly projected variants —
        // a live council cell must self-describe its threshold M.
        let affine = StateConstraint::AffineLe {
            terms: vec![(2, 2), (-1, 3), (-1, 4)],
            c: 0,
        };
        let j = serde_json::to_value(affine.to_view()).unwrap();
        assert_eq!(j["terms"][0][0], 2, "AffineLe view carries coefficients");
        assert_eq!(j["terms"][0][1], 2, "AffineLe view carries slot indices");
        assert_eq!(j["c"], 0, "AffineLe view carries the bound");

        let member = StateConstraint::MemberOf {
            index: 6,
            set: vec![10, 20],
        };
        let j = serde_json::to_value(member.to_view()).unwrap();
        assert_eq!(
            j["set"],
            serde_json::json!([10, 20]),
            "MemberOf view carries the allowed set"
        );

        // SimpleStateConstraint totality (incl. the structural Not view).
        let simples: Vec<(SimpleStateConstraint, &str)> = vec![
            (
                SimpleStateConstraint::FieldEquals {
                    index: 0,
                    value: fe,
                },
                "FieldEquals",
            ),
            (
                SimpleStateConstraint::FieldGte {
                    index: 0,
                    value: fe,
                },
                "FieldGte",
            ),
            (
                SimpleStateConstraint::FieldLte {
                    index: 0,
                    value: fe,
                },
                "FieldLte",
            ),
            (SimpleStateConstraint::WriteOnce { index: 0 }, "WriteOnce"),
            (SimpleStateConstraint::Immutable { index: 0 }, "Immutable"),
            (SimpleStateConstraint::Monotonic { index: 0 }, "Monotonic"),
            (
                SimpleStateConstraint::StrictMonotonic { index: 0 },
                "StrictMonotonic",
            ),
            (
                SimpleStateConstraint::BoundedBy {
                    index: 0,
                    witness_index: 1,
                },
                "BoundedBy",
            ),
            (
                SimpleStateConstraint::FieldGteHeight {
                    index: 0,
                    offset: 1,
                },
                "FieldGteHeight",
            ),
            (
                SimpleStateConstraint::FieldLteHeight {
                    index: 0,
                    offset: 1,
                },
                "FieldLteHeight",
            ),
            (
                SimpleStateConstraint::TemporalGate {
                    not_before: None,
                    not_after: Some(9),
                },
                "TemporalGate",
            ),
            (
                SimpleStateConstraint::Not(Box::new(SimpleStateConstraint::WriteOnce { index: 0 })),
                "Not",
            ),
            (
                SimpleStateConstraint::SenderIs { pk: [7u8; 32] },
                "SenderIs",
            ),
            (
                SimpleStateConstraint::SenderInSlot { index: 2 },
                "SenderInSlot",
            ),
            (SimpleStateConstraint::BalanceGte { min: 10 }, "BalanceGte"),
            (SimpleStateConstraint::BalanceLte { max: 0 }, "BalanceLte"),
            (
                SimpleStateConstraint::PreimageGate {
                    commitment_index: 4,
                    hash_kind: HashKind::Blake3,
                },
                "PreimageGate",
            ),
            (
                SimpleStateConstraint::HeapField {
                    key: 99,
                    atom: HeapAtom::Immutable,
                },
                "HeapField",
            ),
            (
                SimpleStateConstraint::DelegationEpochEquals { index: 2 },
                "DelegationEpochEquals",
            ),
            (
                SimpleStateConstraint::CountGe {
                    threshold: 2,
                    set_commitment_slot: 5,
                },
                "CountGe",
            ),
        ];
        for (sc, expected_kind) in &simples {
            match sc {
                SimpleStateConstraint::FieldEquals { .. }
                | SimpleStateConstraint::FieldGte { .. }
                | SimpleStateConstraint::FieldLte { .. }
                | SimpleStateConstraint::WriteOnce { .. }
                | SimpleStateConstraint::Immutable { .. }
                | SimpleStateConstraint::Monotonic { .. }
                | SimpleStateConstraint::StrictMonotonic { .. }
                | SimpleStateConstraint::BoundedBy { .. }
                | SimpleStateConstraint::FieldGteHeight { .. }
                | SimpleStateConstraint::FieldLteHeight { .. }
                | SimpleStateConstraint::TemporalGate { .. }
                | SimpleStateConstraint::Not(_)
                | SimpleStateConstraint::SenderIs { .. }
                | SimpleStateConstraint::SenderInSlot { .. }
                | SimpleStateConstraint::BalanceGte { .. }
                | SimpleStateConstraint::BalanceLte { .. }
                | SimpleStateConstraint::PreimageGate { .. }
                | SimpleStateConstraint::HeapField { .. }
                | SimpleStateConstraint::DelegationEpochEquals { .. }
                | SimpleStateConstraint::CountGe { .. }
                | SimpleStateConstraint::SenderMemberOf { .. }
                | SimpleStateConstraint::BalanceDeltaLte { .. }
                | SimpleStateConstraint::BalanceDeltaGte { .. } => {}
            }
            let json = serde_json::to_value(sc.to_view()).expect("simple view serializes");
            assert_eq!(
                json.get("kind").and_then(|k| k.as_str()),
                Some(*expected_kind),
                "simple view kind tag for {sc:?}"
            );
        }
        // Not carries its inner constraint structurally (not a debug hack).
        let not = SimpleStateConstraint::Not(Box::new(SimpleStateConstraint::FieldEquals {
            index: 0,
            value: fe,
        }));
        let j = serde_json::to_value(not.to_view()).unwrap();
        assert_eq!(
            j["inner"]["kind"], "FieldEquals",
            "Not view nests its inner view"
        );
    }
}
