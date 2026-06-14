//! Protocol-coverage gate (Pillar 2 of the test/gates initiative, #142).
//!
//! "Verification means something" only if the gates actually exercise the
//! protocol. This file is a **compile-time forcing function**: each exhaustive
//! `match` below has one arm per variant of a core protocol enum (`Effect`,
//! `Authorization`, `StateConstraint`), so **adding a new variant breaks this
//! test's compilation until someone classifies it** — covered by a real
//! executor-invoking flow, or explicitly not-yet-covered. Silent, untested
//! protocol growth is therefore impossible.
//!
//! Honesty contract: an arm is `true` ONLY where a test in this workspace
//! actually drives that variant through `TurnExecutor::execute` /
//! `EmbeddedExecutor::submit_action` with real accept/reject assertions
//! (the coverage_* suites, the cross-app composition e2e, the per-app
//! integration suites, and the #111–#116 apply-path tests). Where coverage is
//! unconfirmed, the arm is conservatively `false` — under-claiming, never
//! over-claiming. The ratchets only shrink.
//!
//! This gate runs under `cargo test --workspace` (CI ci.yml), so it is
//! enforced, not advisory (Pillar 3).

use dregg_cell::StateConstraint;
use dregg_turn::action::{Authorization, Effect};

/// Returns `true` iff this `Effect` variant is exercised end-to-end by at
/// least one executor-invoking test in this workspace. Exhaustive by design.
fn effect_executor_coverage(e: &Effect) -> bool {
    match e {
        // ── Covered: driven through the executor by a real test ──────────
        Effect::SetField { .. } => true, // cross_app_composition_e2e, many
        Effect::Transfer { .. } => true, // bilateral/transfer suites
        Effect::GrantCapability { .. } => true, // capability/grant tests
        Effect::RevokeCapability { .. } => true, // revocation tests
        Effect::EmitEvent { .. } => true, // cross_app_composition_e2e
        Effect::IncrementNonce { .. } => true, // sdk agent_demo / runtime
        Effect::CreateCell { .. } => true, // ledger/create tests
        Effect::SetVerificationKey { .. } => true, // VK integrity tests
        Effect::SpawnWithDelegation { .. } => true, // delegation suite
        Effect::RefreshDelegation => true, // delegation suite
        Effect::RevokeDelegation { .. } => true, // delegation suite
        Effect::BridgeMint { .. } => true, // bridge tests
        // bridge tests
        // #113 apply test
        // #112 apply test
        // obligation suite
        // escrow suite
        // escrow suite
        // escrow suite
        Effect::ExerciseViaCapability { .. } => true, // #111 apply test
        // captp/#96 tests
        // captp/#96 tests
        // captp gc tests
        // captp handoff tests
        Effect::CellSeal { .. } => true,    // integration_lifecycle
        Effect::CellUnseal { .. } => true,  // integration_lifecycle
        Effect::CellDestroy { .. } => true, // integration_destroy_terminal
        Effect::Burn { .. } => true,        // integration_burn_receipt
        Effect::AttenuateCapability { .. } => true, // integration_attenuate_capability
        Effect::ReceiptArchive { .. } => true, // integration_attestation_archive
        // coverage_queue_effects.rs:

        // coverage_misc_effects.rs:
        Effect::NoteCreate { .. } => true,

        Effect::Introduce { .. } => true,
        Effect::MakeSovereign { .. } => true,
        Effect::CreateCellFromFactory { .. } => true,
        Effect::SetPermissions { .. } => true,
        Effect::Refusal { .. } => true,

        // coverage_misc_effects Seal->Unseal round-trip (#144 fixed)

        // ── Not yet covered: documented blockers (#142 work-list) ────────
        Effect::NoteSpend { .. } => false, // needs the real ZK spending-proof stack
        Effect::PipelinedSend { .. } => false, // only valid inside a pipeline resolution pass
    }
}

/// `Effect` variants not yet exercised end-to-end (the #142 work-list).
const NOT_YET_COVERED: &[&str] = &["NoteSpend", "PipelinedSend"];

/// Ratchet: the number of not-yet-covered `Effect` variants may only DECREASE.
const MAX_UNCOVERED_EFFECTS: usize = 2;

#[test]
fn effect_coverage_ratchet_only_shrinks() {
    assert!(
        NOT_YET_COVERED.len() <= MAX_UNCOVERED_EFFECTS,
        "not-yet-covered Effect count {} exceeds the ratchet baseline {} — coverage regressed",
        NOT_YET_COVERED.len(),
        MAX_UNCOVERED_EFFECTS
    );
    // Touch the forcing function so adding a variant breaks the build here.
    assert!(effect_executor_coverage(&Effect::RefreshDelegation));
}

// ============================================================================
// Authorization modes
// ============================================================================

/// Returns `true` iff this `Authorization` mode is exercised end-to-end by at
/// least one executor-invoking test. Exhaustive by design.
fn authorization_executor_coverage(a: &Authorization) -> bool {
    match a {
        // Covered.
        Authorization::Signature(..) => true, // every signed turn (composition, app tests)
        Authorization::Unchecked => true,     // bare_turn helpers across suites
        Authorization::Bearer(..) => true,    // bearer-cap exercise tests
        Authorization::CapTpDelivered { .. } => true, // wire captp_delivery_tests + #122
        // Not yet confirmed covered by an executor-invoking test (#142 work-list).
        Authorization::Proof { .. } => false,
        Authorization::Breadstuff(..) => false,
        Authorization::Custom { .. } => false,
        Authorization::OneOf { .. } => false,
        // Wave-2 authorization modes (one-time-key stealth invocation and
        // first-class biscuit/macaroon Token credentials), now exercised
        // end-to-end through `TurnExecutor::execute` by coverage_auth_modes.rs:
        // a valid stealth/token credential COMMITS and mutates a
        // Signature-gated slot (the Unchecked control refuses on the same
        // cell), while replay / forgery / height-expiry / tamper /
        // untrusted-issuer / cross-cell-key_ref cases REFUSE with the precise
        // TurnError, state untouched.
        Authorization::Stealth { .. } => true, // coverage_auth_modes.rs (stealth_*)
        Authorization::Token { .. } => true,   // coverage_auth_modes.rs (token_*)
    }
}

const NOT_YET_COVERED_AUTH: &[&str] = &["Proof", "Breadstuff", "Custom", "OneOf"];

/// Ratchet for Authorization-mode coverage — may only shrink.
///
/// History: 4 → 6 when the wave-2 lanes introduced `Stealth` and `Token`
/// without coverage; back down to 4 once coverage_auth_modes.rs drove both
/// modes through `TurnExecutor::execute` with real accept+reject pairs.
const MAX_UNCOVERED_AUTH: usize = 4;

#[test]
fn authorization_coverage_ratchet_only_shrinks() {
    assert!(
        NOT_YET_COVERED_AUTH.len() <= MAX_UNCOVERED_AUTH,
        "not-yet-covered Authorization count {} exceeds baseline {} — coverage regressed",
        NOT_YET_COVERED_AUTH.len(),
        MAX_UNCOVERED_AUTH
    );
    assert!(authorization_executor_coverage(&Authorization::Unchecked));
}

// ============================================================================
// StateConstraint (cell-program caveats)
// ============================================================================

/// Returns `true` iff this `StateConstraint` is enforced THROUGH THE EXECUTOR
/// (a `submit_action`/`execute` test where the caveat actually gates a commit)
/// — not merely unit-tested via a direct `CellProgram::evaluate` call.
/// Exhaustive by design.
fn state_constraint_executor_coverage(c: &StateConstraint) -> bool {
    match c {
        // Confirmed enforced via the executor commit path (coverage_state_constraints.rs
        // accept+reject pairs, plus Monotonic/MonotonicSequence from the app suites).
        StateConstraint::Monotonic { .. } => true,
        StateConstraint::MonotonicSequence { .. } => true,
        StateConstraint::FieldEquals { .. } => true,
        StateConstraint::FieldGte { .. } => true,
        StateConstraint::FieldLte { .. } => true,
        StateConstraint::FieldLteField { .. } => true,
        StateConstraint::FieldLteOther { .. } => true,
        StateConstraint::SumEquals { .. } => true,
        StateConstraint::SumEqualsAcross { .. } => true,
        StateConstraint::WriteOnce { .. } => true,
        StateConstraint::Immutable { .. } => true,
        StateConstraint::StrictMonotonic { .. } => true,
        StateConstraint::BoundedBy { .. } => true,
        StateConstraint::FieldDelta { .. } => true,
        StateConstraint::FieldDeltaInRange { .. } => true,
        StateConstraint::RateLimit { .. } => true,
        StateConstraint::RateLimitBySum { .. } => true,
        StateConstraint::TemporalGate { .. } => true,
        StateConstraint::PreimageGate { .. } => true,
        StateConstraint::AllowedTransitions { .. } => true,
        StateConstraint::AnyOf { .. } => true,

        // Policy-combinator core (Lean `Exec.Program` algebra) — enforced by
        // the scalar `evaluate_constraint_full` post-state evaluator.
        StateConstraint::MemberOf { .. } => true,
        StateConstraint::PrefixOf { .. } => true,
        StateConstraint::InRangeTwoSided { .. } => true,
        StateConstraint::DeltaBounded { .. } => true,
        StateConstraint::AffineLe { .. } => true,
        StateConstraint::AffineEq { .. } => true,
        StateConstraint::Reachable { .. } => true,
        StateConstraint::AllOf { .. } => true,

        // Pre-rotation: enforced through the executor commit path by the
        // identity e2e (sdk/tests/identity_prerotation_e2e.rs — rotation
        // turns ride AgentRuntime .turn(); the compromise-resistance tooth
        // is an executor refusal, counters/state unmoved).
        StateConstraint::KeyRotationGate { .. } => true,

        // Heap-keyed atoms (the rotation's app-state lane): enforced
        // through the executor commit path by
        // turn::tests::test_program_heap_field_constraint_enforced (a
        // heap-keyed Monotonic gates a real submitted SetField turn —
        // refuse + accept, heap state checked on both sides).
        StateConstraint::HeapField { .. } => true,

        // The program-readable delegation_epoch tie (channels closure lane):
        // enforced through the executor commit path by
        // turn::tests::test_program_delegation_epoch_equals_enforced (a
        // forged epoch slot REFUSES; the slot write + RevokeDelegation bump
        // in ONE turn ACCEPTS; state checked on both sides).
        StateConstraint::DelegationEpochEquals { .. } => true,
        // In-program M-of-N (the count-≥ atom): enforced through the
        // executor commit path by turn::tests::test_program_count_ge_enforced
        // (a 2-distinct exhibit ACCEPTS; duplicate-padded / unbound / missing
        // exhibits REFUSE; state checked on both sides).
        StateConstraint::CountGe { .. } => true,

        // Not yet enforced/confirmed through the executor (#142 work-list):
        StateConstraint::FieldGteHeight { .. } => false, // not attempted (height-relative)
        StateConstraint::FieldLteHeight { .. } => false, // not attempted (height-relative)
        StateConstraint::SenderAuthorized { .. } => false, // needs witness registry verifier
        StateConstraint::CapabilityUniqueness { .. } => false, // evaluator is a no-op (#143)
        StateConstraint::TemporalPredicate { .. } => false, // needs witness registry
        StateConstraint::BoundDelta { .. } => false,     // cross-cell, not wired in embedded
        StateConstraint::Witnessed { .. } => false,      // needs witness registry
        StateConstraint::Renounced { .. } => false,      // needs witness registry
        StateConstraint::Custom { .. } => false,         // needs ir/descriptor verifier

        // Sender/balance caveat predicates — confirmed enforced through the
        // executor commit path by the accept+reject pairs in
        // coverage_state_constraints.rs (sender_is / sender_in_slot /
        // balance_gte / balance_lte).
        StateConstraint::SenderIs { .. } => true,
        StateConstraint::SenderInSlot { .. } => true,
        StateConstraint::BalanceGte { .. } => true,
        StateConstraint::BalanceLte { .. } => true,

        // The deos language-uplift atoms — executor-enforced through the scalar
        // evaluator (same class as BalanceGte/SenderIs), per the cell/program.rs twins.
        StateConstraint::SenderMemberOf { .. } => true,
        StateConstraint::BalanceDeltaLte { .. } => true,
        StateConstraint::BalanceDeltaGte { .. } => true,
        StateConstraint::AffineDeltaLe { .. } => true,
    }
}

/// `StateConstraint` variants not yet executor-enforced (the #142 work-list).
const NOT_YET_COVERED_CONSTRAINTS: &[&str] = &[
    "FieldGteHeight",
    "FieldLteHeight",
    "SenderAuthorized",
    "CapabilityUniqueness",
    "TemporalPredicate",
    "BoundDelta",
    "Witnessed",
    "Renounced",
    "Custom",
];

/// Ratchet for StateConstraint executor-enforcement coverage — may only shrink.
const MAX_UNCOVERED_CONSTRAINTS: usize = 9;

#[test]
fn state_constraint_coverage_ratchet_only_shrinks() {
    assert!(
        NOT_YET_COVERED_CONSTRAINTS.len() <= MAX_UNCOVERED_CONSTRAINTS,
        "not-yet-covered StateConstraint count {} exceeds baseline {} — coverage regressed",
        NOT_YET_COVERED_CONSTRAINTS.len(),
        MAX_UNCOVERED_CONSTRAINTS
    );
    // Touch the classifier: a covered and an uncovered variant.
    assert!(state_constraint_executor_coverage(
        &StateConstraint::Monotonic { index: 0 }
    ));
    assert!(!state_constraint_executor_coverage(
        &StateConstraint::FieldGteHeight {
            index: 0,
            offset: 0
        }
    ));
}
