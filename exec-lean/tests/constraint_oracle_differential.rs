//! DIFFERENTIAL GATE (game-proof LARP-audit, Step 2): the verified Lean deployed-constraint
//! evaluator (`dregg_constraint_admits`) and the deployed Rust evaluator (`cell/src/program/eval.rs`)
//! decide a shared corpus IDENTICALLY — INCLUDING the boundaries the audit found DIVERGENT
//! (unsigned-256 fieldGe near the top bit; first-write-free heap `Immutable`). This converts the prose
//! "mirror" into a checked correspondence: it would have caught both original bugs, and it fails if the
//! Lean source and the Rust guest-path evaluator ever drift on the subset.
//!
//! ## THE ANTI-MIRROR TOOTH
//!
//! The wire grammar is hand-authored on BOTH sides (`parseConstraint`/`parseCollPred` in Lean,
//! `encode_constraint`/`encode_coll_pred` here). What keeps them honest is [`variant_corpus`]:
//!
//! * it names EVERY `StateConstraint` variant (69 at HEAD) — [`corpus_is_exhaustive`] fails if the
//!   count drifts, so a new variant cannot slide in unexercised;
//! * every LEAN-ROUTED variant carries BOTH an ADMIT case and a REFUSE case. A drifted tag/arity
//!   makes the Lean parse fail CLOSED (`"1"` = violated), which contradicts that arm's ADMIT case —
//!   so ANY divergence in the codec turns this test red. A refuse-only corpus would NOT bite (a
//!   fail-closed parse looks like a correct refusal).
//!
//! NOTE: this test does NOT install the global oracle — so `CellProgram::evaluate` runs the RUST
//! evaluator, and the Lean side is read by calling `LeanConstraintOracle::admits` directly. That lets
//! us compare the two sources in one process.

use dregg_cell::preconditions::EvalContext;
use dregg_cell::program::{
    CellProgram, CollPred, ConstraintOracle, ElemPredAtom, HeapAtom, ProgramError,
    SimpleStateConstraint, StateConstraint, TransitionMeta,
};
use dregg_cell::state::CellState;
use dregg_cell::{StateConstraint as SC, field_from_u64};
use dregg_exec_lean::LeanConstraintOracle;

/// A 32-byte big-endian field element from a full 256-bit value given as a hex string.
fn field_hex(h: &str) -> [u8; 32] {
    let padded = format!("{:0>64}", h);
    let mut out = [0u8; 32];
    for i in 0..32 {
        out[i] = u8::from_str_radix(&padded[i * 2..i * 2 + 2], 16).unwrap();
    }
    out
}

/// Compare accept/reject AND (on reject) the error VARIANT — the soundness-relevant equality.
fn agree(lean: &Result<(), ProgramError>, rust: &Result<(), ProgramError>) -> bool {
    match (lean, rust) {
        (Ok(()), Ok(())) => true,
        (Err(a), Err(b)) => std::mem::discriminant(a) == std::mem::discriminant(b),
        _ => false,
    }
}

/// One differential case: a constraint, the `(old, new)` slice, and the context/meta in scope.
struct Case {
    c: StateConstraint,
    new: CellState,
    old: Option<CellState>,
    ctx: Option<EvalContext>,
    meta: TransitionMeta,
    /// What the RUST evaluator is expected to answer. Carrying it makes the corpus a real
    /// admit/refuse pair rather than "whatever both happen to say".
    admits: bool,
    /// A TRUSTED-RUST case: the point is only that it does NOT route through Lean. Its exact Rust
    /// admit bit is not pinned (many crypto arms admit or refuse on a representative input for
    /// reasons orthogonal to this gate), so `drive` skips the `admits` assertion.
    trusted: bool,
}

fn case(c: StateConstraint, new: CellState, admits: bool) -> Case {
    Case {
        c,
        new,
        old: None,
        ctx: None,
        meta: TransitionMeta::wildcard(),
        admits,
        trusted: false,
    }
}

impl Case {
    fn old(mut self, s: CellState) -> Self {
        self.old = Some(s);
        self
    }
    fn ctx(mut self, c: EvalContext) -> Self {
        self.ctx = Some(c);
        self
    }
    fn meta(mut self, m: TransitionMeta) -> Self {
        self.meta = m;
        self
    }
    /// This case is expected to be OUTSIDE the Lean-evaluated subset (the named trusted-Rust slot).
    fn trusted_rust(mut self) -> Self {
        self.trusted = true;
        self
    }
}

/// Run one case through BOTH evaluators and assert they agree (and that Rust answers as declared).
/// Returns `true` when the constraint ROUTED THROUGH LEAN.
fn drive(k: &Case) -> bool {
    let oracle = LeanConstraintOracle;
    // No oracle installed in this binary ⇒ `evaluate_with_meta` runs the RUST evaluator.
    let rust = CellProgram::Predicate(vec![k.c.clone()]).evaluate_with_meta(
        &k.new,
        k.old.as_ref(),
        k.ctx.as_ref(),
        &k.meta,
    );
    if !k.trusted {
        assert_eq!(
            rust.is_ok(),
            k.admits,
            "CORPUS DECLARATION WRONG: rust says {rust:?} for {:?}",
            k.c
        );
    }
    match oracle.admits(&k.c, &k.new, k.old.as_ref(), k.ctx.as_ref(), &k.meta) {
        None => false,
        Some(lean) => {
            assert!(
                !k.trusted,
                "TRUSTED-RUST arm {:?} unexpectedly ROUTED THROUGH LEAN",
                k.c
            );
            assert!(
                agree(&lean, &rust),
                "LEAN vs RUST DISAGREE on {:?}\n  lean={lean:?}\n  rust={rust:?}",
                k.c
            );
            true
        }
    }
}

fn reg(i: usize, v: u64) -> CellState {
    let mut s = CellState::default();
    s.fields[i] = field_from_u64(v);
    s
}

fn reg2(i: usize, a: u64, j: usize, b: u64) -> CellState {
    let mut s = CellState::default();
    s.fields[i] = field_from_u64(a);
    s.fields[j] = field_from_u64(b);
    s
}

const HEAP_KEY: u64 = 20; // >= STATE_SLOTS(16) ⇒ the unbounded field-map tail
const OTHER_KEY: u64 = 21;

fn heap(key: u64, v: u64) -> CellState {
    let mut s = CellState::default();
    s.set_field_ext(key, field_from_u64(v));
    s
}

fn ctx_at(height: u64) -> EvalContext {
    EvalContext {
        block_height: height,
        timestamp: 0,
        current_epoch: 0,
        sender: None,
        sender_epoch_count: 0,
        revealed_preimage: None,
    }
}

fn ctx_sender(pk: [u8; 32]) -> EvalContext {
    EvalContext {
        sender: Some(pk),
        ..ctx_at(0)
    }
}

fn ctx_count(n: u64) -> EvalContext {
    EvalContext {
        sender_epoch_count: n,
        ..ctx_at(0)
    }
}

fn meta_epoch(e: u64) -> TransitionMeta {
    let mut m = TransitionMeta::wildcard();
    m.delegation_epoch = Some(e);
    m
}

/// A state whose field-map tail carries a strided COLLECTION at `base`
/// (`FieldsCollectionAggregate` / `FieldsCountEquals` read this).
fn fields_coll(base: u64, elems: &[&[u64]]) -> CellState {
    let mut s = CellState::default();
    for (i, e) in elems.iter().enumerate() {
        for (f, v) in e.iter().enumerate() {
            s.set_field_ext(base + (i * e.len() + f) as u64, field_from_u64(*v));
        }
    }
    s
}

/// A state whose `(collection_id, key)` HEAP carries a strided collection
/// (`CollectionAggregate` reads this).
fn heap_coll(coll: u32, elems: &[&[u64]]) -> CellState {
    let mut s = CellState::default();
    for (i, e) in elems.iter().enumerate() {
        for (f, v) in e.iter().enumerate() {
            s.set_heap(coll, (i * e.len() + f) as u32, field_from_u64(*v));
        }
    }
    s
}

// ── THE CORPUS ──────────────────────────────────────────────────────────────────────────────────
//
// One block per `StateConstraint` variant, in the declaration order of
// `cell/src/program/types.rs::StateConstraint`. Lean-routed variants get an ADMIT case AND a REFUSE
// case; trusted-Rust variants get one case marked `.trusted_rust()`.

/// The number of `StateConstraint` variants at HEAD. Bump ONLY together with a new corpus block.
const STATE_CONSTRAINT_VARIANTS: usize = 69;

/// Every variant, by name, in declaration order — the exhaustiveness ledger.
const VARIANT_NAMES: [&str; STATE_CONSTRAINT_VARIANTS] = [
    "FieldEquals",
    "FieldGte",
    "FieldLte",
    "FieldLteField",
    "FieldLteOther",
    "SumEquals",
    "WriteOnce",
    "Immutable",
    "Monotonic",
    "StrictMonotonic",
    "BoundedBy",
    "FieldDelta",
    "FieldDeltaInRange",
    "FieldGteHeight",
    "FieldLteHeight",
    "SumEqualsAcross",
    "SenderAuthorized",
    "CapabilityUniqueness",
    "RateLimit",
    "RateLimitBySum",
    "TemporalGate",
    "RateBound",
    "CooledSince",
    "UntilEvent",
    "SinceEvent",
    "ChallengeWindow",
    "PreimageGate",
    "MonotonicSequence",
    "AllowedTransitions",
    "TemporalPredicate",
    "BoundDelta",
    "AnyOf",
    "Witnessed",
    "Renounced",
    "MemberOf",
    "PrefixOf",
    "InRangeTwoSided",
    "DeltaBounded",
    "AffineLe",
    "AffineEq",
    "Reachable",
    "AllOf",
    "Custom",
    "SenderIs",
    "SenderInSlot",
    "BalanceGte",
    "BalanceLte",
    "KeyRotationGate",
    "HeapField",
    "DelegationEpochEquals",
    "CountGe",
    "SenderMemberOf",
    "BalanceDeltaLte",
    "BalanceDeltaGte",
    "AffineDeltaLe",
    "ObservedFieldEquals",
    "CollectionAggregate",
    "AnyOfBound",
    "SymEq",
    "SymMemberOf",
    "DigEq",
    "DigFieldEq",
    "ClearanceDominates",
    "FieldsCollectionAggregate",
    "SettleEscrow",
    "DischargeObligation",
    "VaultDeposit",
    "HeapFieldLteOther",
    "FieldsCountEquals",
];

/// The variants that must ROUTE THROUGH LEAN. Everything else is the NAMED TRUSTED-RUST SLOT.
const LEAN_ROUTED: [&str; 58] = [
    "FieldEquals",
    "FieldGte",
    "FieldLte",
    "FieldLteField",
    "FieldLteOther",
    "SumEquals",
    "WriteOnce",
    "Immutable",
    "Monotonic",
    "StrictMonotonic",
    "BoundedBy",
    "FieldDelta",
    "FieldDeltaInRange",
    "FieldGteHeight",
    "FieldLteHeight",
    "SumEqualsAcross",
    "CapabilityUniqueness",
    "RateLimit",
    "RateLimitBySum",
    "TemporalGate",
    "RateBound",
    "CooledSince",
    "UntilEvent",
    "SinceEvent",
    "ChallengeWindow",
    "MonotonicSequence",
    "AllowedTransitions",
    "BoundDelta",
    "AnyOf",
    "MemberOf",
    "PrefixOf",
    "InRangeTwoSided",
    "DeltaBounded",
    "AffineLe",
    "AffineEq",
    "Reachable",
    "AllOf",
    "SenderIs",
    "SenderInSlot",
    "BalanceGte",
    "BalanceLte",
    "HeapField",
    "DelegationEpochEquals",
    "SenderMemberOf",
    "BalanceDeltaLte",
    "BalanceDeltaGte",
    "AffineDeltaLe",
    "CollectionAggregate",
    "SymEq",
    "SymMemberOf",
    "DigEq",
    "DigFieldEq",
    "FieldsCollectionAggregate",
    "SettleEscrow",
    "DischargeObligation",
    "VaultDeposit",
    "HeapFieldLteOther",
    "FieldsCountEquals",
];

/// `(variant name, cases)` — the whole corpus.
fn variant_corpus() -> Vec<(&'static str, Vec<Case>)> {
    let pk = field_hex("abcd");
    let big = field_hex("8000000000000000000000000000000000000000000000000000000000000000");
    let mut v: Vec<(&'static str, Vec<Case>)> = Vec::new();

    v.push((
        "FieldEquals",
        vec![
            case(
                SC::FieldEquals {
                    index: 0,
                    value: field_from_u64(5),
                },
                reg(0, 5),
                true,
            ),
            case(
                SC::FieldEquals {
                    index: 0,
                    value: field_from_u64(5),
                },
                reg(0, 6),
                false,
            ),
            // The `check_index` boundary.
            case(
                SC::FieldEquals {
                    index: 16,
                    value: field_from_u64(0),
                },
                reg(0, 0),
                false,
            ),
        ],
    ));
    v.push((
        "FieldGte",
        vec![
            // `>=` is NON-STRICT: equal admits. (This pair is the reality-gate canary's twin.)
            case(
                SC::FieldGte {
                    index: 0,
                    value: field_from_u64(5),
                },
                reg(0, 5),
                true,
            ),
            case(
                SC::FieldGte {
                    index: 0,
                    value: field_from_u64(5),
                },
                reg(0, 4),
                false,
            ),
            // ⚑ DIVERGENCE (b): the top bit set is a HUGE unsigned value, not a negative one.
            case(
                SC::FieldGte {
                    index: 0,
                    value: field_from_u64(1),
                },
                {
                    let mut s = CellState::default();
                    s.fields[0] = big;
                    s
                },
                true,
            ),
        ],
    ));
    v.push((
        "FieldLte",
        vec![
            case(
                SC::FieldLte {
                    index: 0,
                    value: field_from_u64(5),
                },
                reg(0, 5),
                true,
            ),
            case(
                SC::FieldLte {
                    index: 0,
                    value: field_from_u64(1),
                },
                {
                    let mut s = CellState::default();
                    s.fields[0] = big;
                    s
                },
                false,
            ),
        ],
    ));
    v.push((
        "FieldLteField",
        vec![
            case(
                SC::FieldLteField {
                    left_index: 0,
                    right_index: 1,
                },
                reg2(0, 3, 1, 4),
                true,
            ),
            case(
                SC::FieldLteField {
                    left_index: 0,
                    right_index: 1,
                },
                reg2(0, 5, 1, 4),
                false,
            ),
        ],
    ));
    v.push((
        "FieldLteOther",
        vec![
            case(
                SC::FieldLteOther {
                    index: 0,
                    other: 1,
                    delta: 2,
                },
                reg2(0, 6, 1, 4),
                true,
            ),
            case(
                SC::FieldLteOther {
                    index: 0,
                    other: 1,
                    delta: 2,
                },
                reg2(0, 7, 1, 4),
                false,
            ),
        ],
    ));
    v.push((
        "SumEquals",
        vec![
            case(
                SC::SumEquals {
                    indices: vec![0, 1],
                    value: field_from_u64(7),
                },
                reg2(0, 3, 1, 4),
                true,
            ),
            case(
                SC::SumEquals {
                    indices: vec![0, 1],
                    value: field_from_u64(8),
                },
                reg2(0, 3, 1, 4),
                false,
            ),
        ],
    ));
    v.push((
        "WriteOnce",
        vec![
            case(SC::WriteOnce { index: 0 }, reg(0, 9), true).old(reg(0, 0)),
            case(SC::WriteOnce { index: 0 }, reg(0, 9), false).old(reg(0, 7)),
        ],
    ));
    v.push((
        "Immutable",
        vec![
            case(SC::Immutable { index: 0 }, reg(0, 7), true).old(reg(0, 7)),
            case(SC::Immutable { index: 0 }, reg(0, 9), false).old(reg(0, 7)),
            // Old absent + nonce 0 ⇒ genesis escape; nonce != 0 ⇒ needsOld.
            case(SC::Immutable { index: 0 }, reg(0, 9), true),
            case(
                SC::Immutable { index: 0 },
                {
                    let mut s = reg(0, 9);
                    s.set_nonce(5);
                    s
                },
                false,
            ),
        ],
    ));
    v.push((
        "Monotonic",
        vec![
            case(SC::Monotonic { index: 0 }, reg(0, 9), true).old(reg(0, 7)),
            case(SC::Monotonic { index: 0 }, reg(0, 5), false).old(reg(0, 7)),
        ],
    ));
    v.push((
        "StrictMonotonic",
        vec![
            case(SC::StrictMonotonic { index: 0 }, reg(0, 9), true).old(reg(0, 7)),
            case(SC::StrictMonotonic { index: 0 }, reg(0, 7), false).old(reg(0, 7)),
        ],
    ));
    v.push((
        "BoundedBy",
        vec![
            case(
                SC::BoundedBy {
                    index: 0,
                    witness_index: 1,
                },
                reg2(0, 5, 1, 1),
                true,
            ),
            case(
                SC::BoundedBy {
                    index: 0,
                    witness_index: 1,
                },
                reg(0, 5),
                false,
            ),
        ],
    ));
    v.push((
        "FieldDelta",
        vec![
            case(
                SC::FieldDelta {
                    index: 0,
                    delta: field_from_u64(5),
                },
                reg(0, 15),
                true,
            )
            .old(reg(0, 10)),
            case(
                SC::FieldDelta {
                    index: 0,
                    delta: field_from_u64(5),
                },
                reg(0, 14),
                false,
            )
            .old(reg(0, 10)),
        ],
    ));
    v.push((
        "FieldDeltaInRange",
        vec![
            case(
                SC::FieldDeltaInRange {
                    index: 0,
                    min_delta: field_from_u64(1),
                    max_delta: field_from_u64(5),
                },
                reg(0, 13),
                true,
            )
            .old(reg(0, 10)),
            case(
                SC::FieldDeltaInRange {
                    index: 0,
                    min_delta: field_from_u64(1),
                    max_delta: field_from_u64(5),
                },
                reg(0, 20),
                false,
            )
            .old(reg(0, 10)),
        ],
    ));
    v.push((
        "FieldGteHeight",
        vec![
            case(
                SC::FieldGteHeight {
                    index: 0,
                    offset: 0,
                },
                reg(0, 100),
                true,
            )
            .ctx(ctx_at(100)),
            case(
                SC::FieldGteHeight {
                    index: 0,
                    offset: 0,
                },
                reg(0, 99),
                false,
            )
            .ctx(ctx_at(100)),
            // ⚑ FAIL-CLOSED: no context ⇒ MissingContextField, never a silent admit.
            case(
                SC::FieldGteHeight {
                    index: 0,
                    offset: 0,
                },
                reg(0, 100),
                false,
            ),
        ],
    ));
    v.push((
        "FieldLteHeight",
        vec![
            case(
                SC::FieldLteHeight {
                    index: 0,
                    offset: 0,
                },
                reg(0, 90),
                true,
            )
            .ctx(ctx_at(100)),
            case(
                SC::FieldLteHeight {
                    index: 0,
                    offset: 0,
                },
                reg(0, 101),
                false,
            )
            .ctx(ctx_at(100)),
        ],
    ));
    v.push((
        "SumEqualsAcross",
        vec![
            case(
                SC::SumEqualsAcross {
                    input_fields: vec![0],
                    output_fields: vec![1],
                },
                reg2(0, 3, 1, 2),
                true,
            )
            .old(reg(0, 1)),
            case(
                SC::SumEqualsAcross {
                    input_fields: vec![0],
                    output_fields: vec![1],
                },
                reg2(0, 4, 1, 2),
                false,
            )
            .old(reg(0, 1)),
        ],
    ));
    v.push((
        "SenderAuthorized",
        vec![
            case(
                SC::SenderAuthorized {
                    set: dregg_cell::program::AuthorizedSet::PublicRoot { set_root_index: 0 },
                },
                CellState::default(),
                false,
            )
            .trusted_rust(),
        ],
    ));
    v.push((
        "CapabilityUniqueness",
        vec![
            // NO admit case exists — the deployed arm is a TOTAL fail-closed refusal (the scalar
            // evaluator cannot see the cell's real `CapabilitySet`). Both branches refuse, with
            // DIFFERENT error variants, so the discriminant comparison still bites.
            case(
                SC::CapabilityUniqueness {
                    cap_set_root_slot: 0,
                },
                CellState::default(),
                false,
            ),
            case(
                SC::CapabilityUniqueness {
                    cap_set_root_slot: 16,
                },
                CellState::default(),
                false,
            ),
        ],
    ));
    v.push((
        "RateLimit",
        vec![
            case(
                SC::RateLimit {
                    max_per_epoch: 3,
                    epoch_duration: 10,
                },
                CellState::default(),
                true,
            )
            .ctx(ctx_count(2)),
            case(
                SC::RateLimit {
                    max_per_epoch: 3,
                    epoch_duration: 10,
                },
                CellState::default(),
                false,
            )
            .ctx(ctx_count(3)),
            // ⚑ FAIL-CLOSED: no context ⇒ MissingContextField("sender_epoch_count").
            case(
                SC::RateLimit {
                    max_per_epoch: 3,
                    epoch_duration: 10,
                },
                CellState::default(),
                false,
            ),
        ],
    ));
    v.push((
        "RateLimitBySum",
        vec![
            case(
                SC::RateLimitBySum {
                    slot_index: 0,
                    max_sum_per_epoch: 10,
                    epoch_duration: 10,
                },
                reg(0, 5),
                true,
            )
            .old(reg(0, 2))
            .ctx(ctx_count(0)),
            case(
                SC::RateLimitBySum {
                    slot_index: 0,
                    max_sum_per_epoch: 10,
                    epoch_duration: 10,
                },
                reg(0, 5),
                false,
            )
            .old(reg(0, 2))
            .ctx(ctx_count(8)),
            // A DECREASE saturates to delta 0 (never a negative credit).
            case(
                SC::RateLimitBySum {
                    slot_index: 0,
                    max_sum_per_epoch: 10,
                    epoch_duration: 10,
                },
                reg(0, 2),
                true,
            )
            .old(reg(0, 5))
            .ctx(ctx_count(10)),
        ],
    ));
    v.push((
        "TemporalGate",
        vec![
            case(
                SC::TemporalGate {
                    not_before: Some(10),
                    not_after: Some(20),
                },
                CellState::default(),
                true,
            )
            .ctx(ctx_at(15)),
            case(
                SC::TemporalGate {
                    not_before: Some(10),
                    not_after: Some(20),
                },
                CellState::default(),
                false,
            )
            .ctx(ctx_at(25)),
        ],
    ));
    v.push((
        "RateBound",
        vec![
            case(
                SC::RateBound {
                    counter_index: 0,
                    k: 3,
                },
                CellState::default(),
                true,
            )
            .old(reg(0, 2)),
            case(
                SC::RateBound {
                    counter_index: 0,
                    k: 3,
                },
                CellState::default(),
                false,
            )
            .old(reg(0, 3)),
        ],
    ));
    v.push((
        "CooledSince",
        vec![
            case(
                SC::CooledSince {
                    staged_at: 10,
                    period: 5,
                },
                CellState::default(),
                true,
            )
            .ctx(ctx_at(15)),
            case(
                SC::CooledSince {
                    staged_at: 10,
                    period: 5,
                },
                CellState::default(),
                false,
            )
            .ctx(ctx_at(14)),
        ],
    ));
    v.push((
        "UntilEvent",
        vec![
            case(SC::UntilEvent { flag_index: 0 }, CellState::default(), true),
            case(
                SC::UntilEvent { flag_index: 0 },
                CellState::default(),
                false,
            )
            .old(reg(0, 1)),
        ],
    ));
    v.push((
        "SinceEvent",
        vec![
            case(SC::SinceEvent { flag_index: 0 }, CellState::default(), true).old(reg(0, 1)),
            case(
                SC::SinceEvent { flag_index: 0 },
                CellState::default(),
                false,
            ),
        ],
    ));
    v.push((
        "ChallengeWindow",
        vec![
            case(
                SC::ChallengeWindow {
                    challenge_index: 0,
                    staged_at: 10,
                    period: 5,
                },
                CellState::default(),
                true,
            )
            .ctx(ctx_at(15)),
            case(
                SC::ChallengeWindow {
                    challenge_index: 0,
                    staged_at: 10,
                    period: 5,
                },
                CellState::default(),
                false,
            )
            .old(reg(0, 1))
            .ctx(ctx_at(15)),
        ],
    ));
    v.push((
        "PreimageGate",
        vec![
            case(
                SC::PreimageGate {
                    commitment_index: 0,
                    hash_kind: dregg_cell::program::HashKind::Blake3,
                },
                CellState::default(),
                false,
            )
            .trusted_rust(),
        ],
    ));
    v.push((
        "MonotonicSequence",
        vec![
            case(SC::MonotonicSequence { seq_index: 0 }, reg(0, 5), true).old(reg(0, 4)),
            case(SC::MonotonicSequence { seq_index: 0 }, reg(0, 7), false).old(reg(0, 4)),
        ],
    ));
    v.push((
        "AllowedTransitions",
        vec![
            case(
                SC::AllowedTransitions {
                    slot_index: 0,
                    allowed: vec![(field_from_u64(1), field_from_u64(2))],
                },
                reg(0, 2),
                true,
            )
            .old(reg(0, 1)),
            case(
                SC::AllowedTransitions {
                    slot_index: 0,
                    allowed: vec![(field_from_u64(1), field_from_u64(2))],
                },
                reg(0, 3),
                false,
            )
            .old(reg(0, 1)),
        ],
    ));
    v.push((
        "TemporalPredicate",
        vec![
            case(
                SC::TemporalPredicate {
                    witness_index: 0,
                    dsl_hash: [0u8; 32],
                },
                CellState::default(),
                false,
            )
            .trusted_rust(),
        ],
    ));
    v.push((
        "BoundDelta",
        vec![
            // Like `CapabilityUniqueness`: a TOTAL sentinel refusal (the executor's γ.2 cross-cell
            // loop is the only place this is enforced).
            case(
                SC::BoundDelta {
                    local_slot: 0,
                    peer_cell: dregg_cell::id::CellId([7u8; 32]),
                    peer_slot: 0,
                    delta_relation: dregg_cell::program::DeltaRelation::Equal,
                },
                CellState::default(),
                false,
            ),
        ],
    ));
    v.push((
        "AnyOf",
        vec![
            case(
                SC::AnyOf {
                    variants: vec![
                        SimpleStateConstraint::FieldEquals {
                            index: 0,
                            value: field_from_u64(5),
                        },
                        SimpleStateConstraint::FieldEquals {
                            index: 0,
                            value: field_from_u64(7),
                        },
                    ],
                },
                reg(0, 7),
                true,
            ),
            case(
                SC::AnyOf {
                    variants: vec![
                        SimpleStateConstraint::FieldEquals {
                            index: 0,
                            value: field_from_u64(5),
                        },
                        SimpleStateConstraint::FieldEquals {
                            index: 0,
                            value: field_from_u64(7),
                        },
                    ],
                },
                reg(0, 9),
                false,
            ),
            // The Heyting `Not` under the peeled parity.
            case(
                SC::AnyOf {
                    variants: vec![SimpleStateConstraint::Not(Box::new(
                        SimpleStateConstraint::FieldEquals {
                            index: 0,
                            value: field_from_u64(5),
                        },
                    ))],
                },
                reg(0, 7),
                true,
            ),
        ],
    ));
    v.push((
        "Witnessed",
        vec![
            case(
                SC::Witnessed {
                    wp: dregg_cell::predicate::WitnessedPredicate {
                        kind: dregg_cell::predicate::WitnessedPredicateKind::Dfa,
                        commitment: [0u8; 32],
                        input_ref: dregg_cell::predicate::InputRef::Slot { index: 0 },
                        proof_witness_index: 0,
                    },
                },
                CellState::default(),
                false,
            )
            .trusted_rust(),
        ],
    ));
    v.push((
        "Renounced",
        vec![
            case(
                SC::Renounced {
                    set: dregg_cell::program::RenouncedSet::PublicRoot { set_root_index: 0 },
                },
                CellState::default(),
                false,
            )
            .trusted_rust(),
        ],
    ));
    v.push((
        "MemberOf",
        vec![
            case(
                SC::MemberOf {
                    index: 0,
                    set: vec![5, 9],
                },
                reg(0, 5),
                true,
            ),
            case(
                SC::MemberOf {
                    index: 0,
                    set: vec![5, 9],
                },
                reg(0, 7),
                false,
            ),
        ],
    ));
    v.push((
        "PrefixOf",
        vec![
            case(
                SC::PrefixOf {
                    seg_indices: vec![0, 1],
                    prefix: vec![3],
                },
                reg2(0, 3, 1, 4),
                true,
            ),
            case(
                SC::PrefixOf {
                    seg_indices: vec![0, 1],
                    prefix: vec![4],
                },
                reg2(0, 3, 1, 4),
                false,
            ),
        ],
    ));
    v.push((
        "InRangeTwoSided",
        vec![
            case(
                SC::InRangeTwoSided {
                    index: 0,
                    lo: 5,
                    hi: 9,
                },
                reg(0, 7),
                true,
            ),
            case(
                SC::InRangeTwoSided {
                    index: 0,
                    lo: 8,
                    hi: 9,
                },
                reg(0, 7),
                false,
            ),
        ],
    ));
    v.push((
        "DeltaBounded",
        vec![
            case(SC::DeltaBounded { index: 0, d: 3 }, reg(0, 7), true).old(reg(0, 5)),
            case(SC::DeltaBounded { index: 0, d: 1 }, reg(0, 7), false).old(reg(0, 5)),
        ],
    ));
    v.push((
        "AffineLe",
        vec![
            case(
                SC::AffineLe {
                    terms: vec![(1, 0), (1, 1)],
                    c: 7,
                },
                reg2(0, 3, 1, 4),
                true,
            ),
            case(
                SC::AffineLe {
                    terms: vec![(1, 0), (1, 1)],
                    c: 6,
                },
                reg2(0, 3, 1, 4),
                false,
            ),
            // A NEGATIVE coefficient (the `i128` signed path).
            case(
                SC::AffineLe {
                    terms: vec![(-1, 0)],
                    c: 0,
                },
                reg(0, 3),
                true,
            ),
        ],
    ));
    v.push((
        "AffineEq",
        vec![
            case(
                SC::AffineEq {
                    terms: vec![(1, 0), (1, 1)],
                    c: 7,
                },
                reg2(0, 3, 1, 4),
                true,
            ),
            case(
                SC::AffineEq {
                    terms: vec![(1, 0), (1, 1)],
                    c: 8,
                },
                reg2(0, 3, 1, 4),
                false,
            ),
        ],
    ));
    v.push((
        "Reachable",
        vec![
            case(
                SC::Reachable {
                    from_index: 0,
                    to_label: 3,
                    edges: vec![(1, 2), (2, 3)],
                },
                reg(0, 1),
                true,
            ),
            case(
                SC::Reachable {
                    from_index: 0,
                    to_label: 4,
                    edges: vec![(1, 2), (2, 3)],
                },
                reg(0, 1),
                false,
            ),
        ],
    ));
    v.push((
        "AllOf",
        vec![
            case(
                SC::AllOf {
                    variants: vec![
                        SimpleStateConstraint::FieldGte {
                            index: 0,
                            value: field_from_u64(5),
                        },
                        SimpleStateConstraint::FieldLte {
                            index: 0,
                            value: field_from_u64(9),
                        },
                    ],
                },
                reg(0, 7),
                true,
            ),
            case(
                SC::AllOf {
                    variants: vec![
                        SimpleStateConstraint::FieldGte {
                            index: 0,
                            value: field_from_u64(5),
                        },
                        SimpleStateConstraint::FieldLte {
                            index: 0,
                            value: field_from_u64(9),
                        },
                    ],
                },
                reg(0, 3),
                false,
            ),
        ],
    ));
    v.push((
        "Custom",
        vec![
            case(
                SC::Custom {
                    ir_hash: [0u8; 32],
                    descriptor: Default::default(),
                    reads: Default::default(),
                },
                CellState::default(),
                false,
            )
            .trusted_rust(),
        ],
    ));
    v.push((
        "SenderIs",
        vec![
            case(SC::SenderIs { pk }, CellState::default(), true).ctx(ctx_sender(pk)),
            case(SC::SenderIs { pk }, CellState::default(), false).ctx(ctx_sender([9u8; 32])),
            // ⚑ FAIL-CLOSED: a context WITHOUT a sender.
            case(SC::SenderIs { pk }, CellState::default(), false).ctx(ctx_at(0)),
        ],
    ));
    v.push((
        "SenderInSlot",
        vec![
            case(
                SC::SenderInSlot { index: 0 },
                {
                    let mut s = CellState::default();
                    s.fields[0] = pk;
                    s
                },
                true,
            )
            .ctx(ctx_sender(pk)),
            case(SC::SenderInSlot { index: 0 }, CellState::default(), false).ctx(ctx_sender(pk)),
        ],
    ));
    v.push((
        "BalanceGte",
        vec![
            case(SC::BalanceGte { min: 5 }, bal(10), true),
            case(SC::BalanceGte { min: 20 }, bal(10), false),
            // A NEGATIVE balance is below every u64 floor.
            case(SC::BalanceGte { min: 0 }, bal(-3), false),
        ],
    ));
    v.push((
        "BalanceLte",
        vec![
            case(SC::BalanceLte { max: 20 }, bal(10), true),
            case(SC::BalanceLte { max: 5 }, bal(10), false),
        ],
    ));
    v.push((
        "KeyRotationGate",
        vec![
            case(
                SC::KeyRotationGate {
                    digest_slot: 0,
                    current_slot: 1,
                    last_rotated_slot: 2,
                    cooling_period: 0,
                    hash_kind: dregg_cell::program::HashKind::Blake3,
                },
                CellState::default(),
                false,
            )
            .trusted_rust(),
        ],
    ));
    v.push((
        "HeapField",
        vec![
            case(
                SC::HeapField {
                    key: HEAP_KEY,
                    atom: HeapAtom::Gte {
                        value: field_from_u64(3),
                    },
                },
                heap(HEAP_KEY, 5),
                true,
            ),
            case(
                SC::HeapField {
                    key: HEAP_KEY,
                    atom: HeapAtom::Gte {
                        value: field_from_u64(7),
                    },
                },
                heap(HEAP_KEY, 5),
                false,
            ),
            // ⚑ DIVERGENCE (a): the FIRST write is free (absent old); a flip afterwards freezes.
            case(
                SC::HeapField {
                    key: HEAP_KEY,
                    atom: HeapAtom::Immutable,
                },
                heap(HEAP_KEY, 7),
                true,
            ),
            case(
                SC::HeapField {
                    key: HEAP_KEY,
                    atom: HeapAtom::Immutable,
                },
                heap(HEAP_KEY, 9),
                false,
            )
            .old(heap(HEAP_KEY, 7)),
            case(
                SC::HeapField {
                    key: HEAP_KEY,
                    atom: HeapAtom::Monotonic,
                },
                heap(HEAP_KEY, 8),
                true,
            )
            .old(heap(HEAP_KEY, 5)),
            case(
                SC::HeapField {
                    key: HEAP_KEY,
                    atom: HeapAtom::DeltaEquals { d: 3 },
                },
                heap(HEAP_KEY, 8),
                true,
            )
            .old(heap(HEAP_KEY, 5)),
            case(
                SC::HeapField {
                    key: HEAP_KEY,
                    atom: HeapAtom::MemberOf { set: vec![5, 9] },
                },
                heap(HEAP_KEY, 5),
                true,
            ),
            case(
                SC::HeapField {
                    key: HEAP_KEY,
                    atom: HeapAtom::InRangeTwoSided { lo: 3, hi: 7 },
                },
                heap(HEAP_KEY, 5),
                true,
            ),
            case(
                SC::HeapField {
                    key: HEAP_KEY,
                    atom: HeapAtom::WriteOnce,
                },
                heap(HEAP_KEY, 9),
                false,
            )
            .old(heap(HEAP_KEY, 7)),
            case(
                SC::HeapField {
                    key: HEAP_KEY,
                    atom: HeapAtom::StrictMonotonic,
                },
                heap(HEAP_KEY, 8),
                true,
            )
            .old(heap(HEAP_KEY, 5)),
            case(
                SC::HeapField {
                    key: HEAP_KEY,
                    atom: HeapAtom::Lte {
                        value: field_from_u64(9),
                    },
                },
                heap(HEAP_KEY, 5),
                true,
            ),
            case(
                SC::HeapField {
                    key: HEAP_KEY,
                    atom: HeapAtom::Equals {
                        value: field_from_u64(5),
                    },
                },
                heap(HEAP_KEY, 5),
                true,
            ),
            case(
                SC::HeapField {
                    key: HEAP_KEY,
                    atom: HeapAtom::DeltaBounded { d: 3 },
                },
                heap(HEAP_KEY, 7),
                true,
            )
            .old(heap(HEAP_KEY, 5)),
        ],
    ));
    v.push((
        "DelegationEpochEquals",
        vec![
            case(SC::DelegationEpochEquals { index: 0 }, reg(0, 7), true).meta(meta_epoch(7)),
            case(SC::DelegationEpochEquals { index: 0 }, reg(0, 8), false).meta(meta_epoch(7)),
            // ⚑ FAIL-CLOSED: no stamped epoch.
            case(SC::DelegationEpochEquals { index: 0 }, reg(0, 7), false),
        ],
    ));
    v.push((
        "CountGe",
        vec![
            case(
                SC::CountGe {
                    threshold: 2,
                    set_commitment_slot: 0,
                },
                CellState::default(),
                false,
            )
            .trusted_rust(),
        ],
    ));
    v.push((
        "SenderMemberOf",
        vec![
            case(
                SC::SenderMemberOf {
                    members: vec![pk, [1u8; 32]],
                },
                CellState::default(),
                true,
            )
            .ctx(ctx_sender(pk)),
            case(
                SC::SenderMemberOf {
                    members: vec![[1u8; 32]],
                },
                CellState::default(),
                false,
            )
            .ctx(ctx_sender(pk)),
        ],
    ));
    v.push((
        "BalanceDeltaLte",
        vec![
            case(SC::BalanceDeltaLte { max: 6 }, bal(10), true).old(bal(4)),
            case(SC::BalanceDeltaLte { max: 5 }, bal(10), false).old(bal(4)),
        ],
    ));
    v.push((
        "BalanceDeltaGte",
        vec![
            case(SC::BalanceDeltaGte { min: 6 }, bal(10), true).old(bal(4)),
            case(SC::BalanceDeltaGte { min: 7 }, bal(10), false).old(bal(4)),
        ],
    ));
    v.push((
        "AffineDeltaLe",
        vec![
            case(
                SC::AffineDeltaLe {
                    terms: vec![(1, 0)],
                    c: 3,
                },
                reg(0, 5),
                true,
            )
            .old(reg(0, 2)),
            case(
                SC::AffineDeltaLe {
                    terms: vec![(1, 0)],
                    c: 2,
                },
                reg(0, 5),
                false,
            )
            .old(reg(0, 2)),
        ],
    ));
    v.push((
        "ObservedFieldEquals",
        vec![
            case(
                SC::ObservedFieldEquals {
                    local_field: 0,
                    source_cell: [7u8; 32],
                    source_field: 0,
                    at_root: [0u8; 32],
                    proof_witness_index: 0,
                },
                CellState::default(),
                false,
            )
            .trusted_rust(),
        ],
    ));
    // ── THE NEWLY-WIDENED AGGREGATES ───────────────────────────────────────────────────────────
    v.push((
        "CollectionAggregate",
        vec![
            // stride 2, fuel 3, `countSatGe 2 (elem[1] == 1)`; the anchor is offset 1, so the read
            // truncates at the first element whose cell `i*2+1` is absent.
            case(
                SC::CollectionAggregate {
                    collection_id: 4,
                    stride: 2,
                    fuel: 3,
                    pred: CollPred::CountSatGe {
                        m: 2,
                        p: ElemPredAtom::FieldEquals {
                            offset: 1,
                            value: field_from_u64(1),
                        },
                    },
                },
                heap_coll(4, &[&[0xaa, 1], &[0xbb, 1]]),
                true,
            ),
            case(
                SC::CollectionAggregate {
                    collection_id: 4,
                    stride: 2,
                    fuel: 3,
                    pred: CollPred::CountSatGe {
                        m: 2,
                        p: ElemPredAtom::FieldEquals {
                            offset: 1,
                            value: field_from_u64(1),
                        },
                    },
                },
                heap_coll(4, &[&[0xaa, 1], &[0xbb, 2]]),
                false,
            ),
            // ⚑ FAIL-CLOSED: an ABSENT collection refuses (never a vacuous ∀ / `count >= 0` admit).
            case(
                SC::CollectionAggregate {
                    collection_id: 4,
                    stride: 2,
                    fuel: 3,
                    pred: CollPred::AllMembers {
                        p: ElemPredAtom::FieldEquals {
                            offset: 1,
                            value: field_from_u64(1),
                        },
                    },
                },
                CellState::default(),
                false,
            ),
            // ⚑ THE COUNCIL TOOTH: `mOfNDistinct` — two DISTINCT approving keys admit…
            case(
                SC::CollectionAggregate {
                    collection_id: 4,
                    stride: 2,
                    fuel: 3,
                    pred: CollPred::MOfNDistinct {
                        m: 2,
                        key_offset: 0,
                        approved: ElemPredAtom::FieldEquals {
                            offset: 1,
                            value: field_from_u64(1),
                        },
                    },
                },
                heap_coll(4, &[&[7, 1], &[9, 1]]),
                true,
            ),
            // … while the DUPLICATE-PADDED FORGE (three approvals, ONE identity) refuses.
            case(
                SC::CollectionAggregate {
                    collection_id: 4,
                    stride: 2,
                    fuel: 3,
                    pred: CollPred::MOfNDistinct {
                        m: 2,
                        key_offset: 0,
                        approved: ElemPredAtom::FieldEquals {
                            offset: 1,
                            value: field_from_u64(1),
                        },
                    },
                },
                heap_coll(4, &[&[7, 1], &[7, 1], &[7, 1]]),
                false,
            ),
            // Σ over the low lane.
            case(
                SC::CollectionAggregate {
                    collection_id: 4,
                    stride: 1,
                    fuel: 3,
                    pred: CollPred::SumOfLe {
                        offset: 0,
                        bound: 12,
                    },
                },
                heap_coll(4, &[&[3], &[4], &[5]]),
                true,
            ),
            case(
                SC::CollectionAggregate {
                    collection_id: 4,
                    stride: 1,
                    fuel: 3,
                    pred: CollPred::SumOfLe {
                        offset: 0,
                        bound: 11,
                    },
                },
                heap_coll(4, &[&[3], &[4], &[5]]),
                false,
            ),
            case(
                SC::CollectionAggregate {
                    collection_id: 4,
                    stride: 1,
                    fuel: 3,
                    pred: CollPred::SumOfGe {
                        offset: 0,
                        bound: 12,
                    },
                },
                heap_coll(4, &[&[3], &[4], &[5]]),
                true,
            ),
            case(
                SC::CollectionAggregate {
                    collection_id: 4,
                    stride: 1,
                    fuel: 3,
                    pred: CollPred::ExistsMember {
                        p: ElemPredAtom::FieldGte {
                            offset: 0,
                            value: field_from_u64(5),
                        },
                    },
                },
                heap_coll(4, &[&[3], &[4], &[5]]),
                true,
            ),
            case(
                SC::CollectionAggregate {
                    collection_id: 4,
                    stride: 1,
                    fuel: 3,
                    pred: CollPred::AllMembers {
                        p: ElemPredAtom::FieldLte {
                            offset: 0,
                            value: field_from_u64(4),
                        },
                    },
                },
                heap_coll(4, &[&[3], &[4], &[5]]),
                false,
            ),
            case(
                SC::CollectionAggregate {
                    collection_id: 4,
                    stride: 1,
                    fuel: 2,
                    pred: CollPred::AllMembers {
                        p: ElemPredAtom::FieldInSet {
                            offset: 0,
                            set: vec![5, 9],
                        },
                    },
                },
                heap_coll(4, &[&[5], &[9]]),
                true,
            ),
        ],
    ));
    v.push((
        "AnyOfBound",
        vec![
            case(
                SC::AnyOfBound { branches: vec![] },
                CellState::default(),
                false,
            )
            .trusted_rust(),
        ],
    ));
    v.push((
        "SymEq",
        vec![
            case(SC::SymEq { index: 0, sym: 7 }, reg(0, 7), true),
            case(SC::SymEq { index: 0, sym: 8 }, reg(0, 7), false),
        ],
    ));
    v.push((
        "SymMemberOf",
        vec![
            case(
                SC::SymMemberOf {
                    index: 0,
                    set: vec![5, 7],
                },
                reg(0, 7),
                true,
            ),
            case(
                SC::SymMemberOf {
                    index: 0,
                    set: vec![5, 9],
                },
                reg(0, 7),
                false,
            ),
        ],
    ));
    v.push((
        "DigEq",
        vec![
            case(
                SC::DigEq {
                    index: 0,
                    digest: field_from_u64(7),
                },
                reg(0, 7),
                true,
            ),
            case(
                SC::DigEq {
                    index: 0,
                    digest: field_from_u64(8),
                },
                reg(0, 7),
                false,
            ),
        ],
    ));
    v.push((
        "DigFieldEq",
        vec![
            case(
                SC::DigFieldEq {
                    left_index: 0,
                    right_index: 1,
                },
                reg2(0, 7, 1, 7),
                true,
            ),
            case(
                SC::DigFieldEq {
                    left_index: 0,
                    right_index: 1,
                },
                reg2(0, 7, 1, 8),
                false,
            ),
        ],
    ));
    v.push((
        "ClearanceDominates",
        vec![
            case(
                SC::ClearanceDominates {
                    actor_label_index: 0,
                    box_index: 1,
                    root_index: 2,
                    edges: vec![],
                },
                CellState::default(),
                false,
            )
            .trusted_rust(),
        ],
    ));
    v.push((
        "FieldsCollectionAggregate",
        vec![
            // The `fields_map` twin: SAME Lean semantics, a different key-resolution source.
            case(
                SC::FieldsCollectionAggregate {
                    base: 32,
                    stride: 2,
                    fuel: 3,
                    pred: CollPred::CountSatGe {
                        m: 2,
                        p: ElemPredAtom::FieldEquals {
                            offset: 1,
                            value: field_from_u64(1),
                        },
                    },
                },
                fields_coll(32, &[&[0xaa, 1], &[0xbb, 1]]),
                true,
            ),
            case(
                SC::FieldsCollectionAggregate {
                    base: 32,
                    stride: 2,
                    fuel: 3,
                    pred: CollPred::CountSatGe {
                        m: 2,
                        p: ElemPredAtom::FieldEquals {
                            offset: 1,
                            value: field_from_u64(1),
                        },
                    },
                },
                fields_coll(32, &[&[0xaa, 1], &[0xbb, 2]]),
                false,
            ),
            case(
                SC::FieldsCollectionAggregate {
                    base: 32,
                    stride: 2,
                    fuel: 3,
                    pred: CollPred::MOfNDistinct {
                        m: 2,
                        key_offset: 0,
                        approved: ElemPredAtom::FieldEquals {
                            offset: 1,
                            value: field_from_u64(1),
                        },
                    },
                },
                fields_coll(32, &[&[7, 1], &[7, 1], &[7, 1]]),
                false,
            ),
        ],
    ));
    v.push((
        "SettleEscrow",
        vec![
            case(
                SC::SettleEscrow {
                    leg_a_index: 0,
                    leg_b_index: 1,
                },
                reg2(0, 2, 1, 2),
                true,
            )
            .old(reg2(0, 1, 1, 1)),
            // The HALF-OPEN settle (leg B left Deposited).
            case(
                SC::SettleEscrow {
                    leg_a_index: 0,
                    leg_b_index: 1,
                },
                reg2(0, 2, 1, 1),
                false,
            )
            .old(reg2(0, 1, 1, 1)),
        ],
    ));
    v.push((
        "DischargeObligation",
        vec![
            case(
                SC::DischargeObligation {
                    cursor_slot: 0,
                    due_slot: 1,
                    amount_slot: 2,
                    period: 5,
                    amount: 30,
                },
                {
                    let mut s = CellState::default();
                    s.fields[0] = field_from_u64(15);
                    s.fields[1] = field_from_u64(10);
                    s.fields[2] = field_from_u64(130);
                    s
                },
                true,
            )
            .old({
                let mut s = CellState::default();
                s.fields[0] = field_from_u64(10);
                s.fields[1] = field_from_u64(10);
                s.fields[2] = field_from_u64(100);
                s
            })
            .ctx(ctx_at(12)),
            // NOT YET DUE.
            case(
                SC::DischargeObligation {
                    cursor_slot: 0,
                    due_slot: 1,
                    amount_slot: 2,
                    period: 5,
                    amount: 30,
                },
                {
                    let mut s = CellState::default();
                    s.fields[0] = field_from_u64(15);
                    s.fields[1] = field_from_u64(10);
                    s.fields[2] = field_from_u64(130);
                    s
                },
                false,
            )
            .old({
                let mut s = CellState::default();
                s.fields[0] = field_from_u64(10);
                s.fields[1] = field_from_u64(10);
                s.fields[2] = field_from_u64(100);
                s
            })
            .ctx(ctx_at(9)),
        ],
    ));
    v.push((
        "VaultDeposit",
        vec![
            case(
                SC::VaultDeposit {
                    assets_slot: 0,
                    shares_slot: 1,
                },
                reg2(0, 110, 1, 110),
                true,
            )
            .old(reg2(0, 100, 1, 100)),
            // THE INFLATION TOOTH: a positive deposit that mints ZERO shares.
            case(
                SC::VaultDeposit {
                    assets_slot: 0,
                    shares_slot: 1,
                },
                reg2(0, 110, 1, 100),
                false,
            )
            .old(reg2(0, 100, 1, 100)),
        ],
    ));
    v.push((
        "HeapFieldLteOther",
        vec![
            case(
                SC::HeapFieldLteOther {
                    key: HEAP_KEY,
                    other_key: OTHER_KEY,
                    delta: 0,
                },
                {
                    let mut s = heap(HEAP_KEY, 3);
                    s.set_field_ext(OTHER_KEY, field_from_u64(5));
                    s
                },
                true,
            ),
            case(
                SC::HeapFieldLteOther {
                    key: HEAP_KEY,
                    other_key: OTHER_KEY,
                    delta: 0,
                },
                {
                    let mut s = heap(HEAP_KEY, 7);
                    s.set_field_ext(OTHER_KEY, field_from_u64(5));
                    s
                },
                false,
            ),
            // ⚑ FAIL-CLOSED: an absent `other_key` refuses even when the bound would hold.
            case(
                SC::HeapFieldLteOther {
                    key: HEAP_KEY,
                    other_key: OTHER_KEY,
                    delta: 0,
                },
                heap(HEAP_KEY, 3),
                false,
            ),
        ],
    ));
    v.push((
        "FieldsCountEquals",
        vec![
            // Three keys resolving to (5, 7, 5); the census of `value = 5` is 2.
            case(
                SC::FieldsCountEquals {
                    keys: vec![32, 33, 34],
                    value: field_from_u64(5),
                    count_index: 0,
                },
                {
                    let mut s = fields_coll(32, &[&[5, 7, 5]]);
                    s.fields[0] = field_from_u64(2);
                    s
                },
                true,
            ),
            case(
                SC::FieldsCountEquals {
                    keys: vec![32, 33, 34],
                    value: field_from_u64(5),
                    count_index: 0,
                },
                {
                    let mut s = fields_coll(32, &[&[5, 7, 5]]);
                    s.fields[0] = field_from_u64(3);
                    s
                },
                false,
            ),
            // ⚑ FAIL-CLOSED: an ABSENT key refuses (never counted as a non-match).
            case(
                SC::FieldsCountEquals {
                    keys: vec![32, 33, 99],
                    value: field_from_u64(5),
                    count_index: 0,
                },
                {
                    let mut s = fields_coll(32, &[&[5, 7, 5]]);
                    s.fields[0] = field_from_u64(1);
                    s
                },
                false,
            ),
        ],
    ));
    v
}

fn bal(v: i64) -> CellState {
    let mut s = CellState::default();
    s.set_balance(v);
    s
}

// ── THE TESTS ───────────────────────────────────────────────────────────────────────────────────

#[test]
fn corpus_is_exhaustive() {
    // Every `StateConstraint` variant is named; the count is pinned so a new variant fails here
    // until someone adds a corpus block AND classifies it in `encode_constraint`.
    assert_eq!(VARIANT_NAMES.len(), STATE_CONSTRAINT_VARIANTS);
    let corpus = variant_corpus();
    let covered: Vec<&str> = corpus.iter().map(|(n, _)| *n).collect();
    for name in VARIANT_NAMES {
        assert!(
            covered.contains(&name),
            "StateConstraint::{name} has NO differential corpus block"
        );
    }
    assert_eq!(
        covered.len(),
        STATE_CONSTRAINT_VARIANTS,
        "corpus block count drifted from the variant ledger"
    );
}

#[test]
fn lean_and_rust_agree_on_the_whole_corpus() {
    if !dregg_lean_ffi::constraint_admits_available() {
        eprintln!("SKIP: libdregg_lean.a lacks dregg_constraint_admits — rebuild the archive");
        return;
    }
    let corpus = variant_corpus();
    let mut routed: Vec<&str> = Vec::new();
    for (name, cases) in &corpus {
        let mut any_lean = false;
        for k in cases {
            if drive(k) {
                any_lean = true;
            }
        }
        if any_lean {
            routed.push(name);
        }
    }
    // The ROUTING LEDGER: exactly the declared set goes through Lean. A silently-narrowed subset
    // (an arm quietly declining to Rust) fails HERE, not in prose.
    for name in LEAN_ROUTED {
        assert!(
            routed.contains(&name),
            "StateConstraint::{name} is declared Lean-routed but did NOT route through Lean"
        );
    }
    for name in &routed {
        assert!(
            LEAN_ROUTED.contains(name),
            "StateConstraint::{name} routed through Lean but is NOT in the declared ledger"
        );
    }
    assert_eq!(routed.len(), LEAN_ROUTED.len());
}

#[test]
fn every_lean_routed_arm_has_an_admit_case() {
    // ⚑ THE ANTI-MIRROR TOOTH. A drifted wire tag makes the Lean parse fail CLOSED (`"1"` =
    // violated), which looks like a correct answer on a REFUSE case. Only an ADMIT case catches it.
    // The two EXECUTOR-ONLY sentinels are the honest exceptions: the deployed arm has NO admitting
    // input at all, so their bite is the error-DISCRIMINANT comparison in `agree` instead.
    const NO_ADMIT_CASE_EXISTS: [&str; 2] = ["CapabilityUniqueness", "BoundDelta"];
    for (name, cases) in variant_corpus() {
        if !LEAN_ROUTED.contains(&name) || NO_ADMIT_CASE_EXISTS.contains(&name) {
            continue;
        }
        assert!(
            cases.iter().any(|k| k.admits),
            "StateConstraint::{name} has no ADMIT case — a drifted wire tag would go undetected"
        );
        assert!(
            cases.iter().any(|k| !k.admits),
            "StateConstraint::{name} has no REFUSE case"
        );
    }
}
