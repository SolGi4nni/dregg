//! Witnessed-predicate dispatch wiring tests (Cav-Codex Block 3.5).
//!
//! Per CAVEAT-LAYER-COVERAGE.md §7 finding #5: the
//! `WitnessedPredicateRegistry` shape exists, stubs exist, real
//! verifiers exist, but "no call site dispatches through it" — every
//! `StateConstraint::Witnessed` / `Preconditions::Witnessed` evaluation
//! surfaced the legacy `WitnessedPredicateRequiresExecutor` sentinel
//! and the executor mapped it to `TurnError::ProgramViolation`.
//!
//! `TurnExecutor` defaults to a non-`None` witnessed registry on every
//! constructor (`new`, `with_budget_gate`, `with_proof_verifier`), and
//! the slot-caveat program-evaluator + the precondition checker both
//! consult `self.witnessed_registry` when they encounter a witnessed
//! clause.
//!
//! These tests exercise the dispatch surface, not the proof algebra.
//!
//! # Two distinct defaults — do not conflate them
//!
//! - `dregg_cell::WitnessedPredicateRegistry::default_builtins()` is the
//!   *cell-layer* default. The cell crate cannot link `dregg-circuit`
//!   (dependency cycle), so it installs `NotYetWiredVerifier` (fail-closed)
//!   for every kind whose real verifier lives in the circuit: Dfa, Temporal,
//!   MerkleMembership, BlindedSet, BridgePredicate, PedersenEquality. The
//!   `default_builtins_registry_*` tests below pin THAT contract and are
//!   unaffected by the executor default.
//! - `dregg-turn`'s `TurnExecutor` constructors default to
//!   `executor::registry_with_real_verifiers()` instead — because `dregg-turn`
//!   DOES link `dregg-circuit` and owns the real STARK verifiers. So a bare
//!   `TurnExecutor::new()` enforces the REAL MerkleMembership / NonMembership /
//!   BlindedSet / PedersenEquality verifiers (admits valid proofs, rejects
//!   forgeries at the STARK level). The three kinds that need host-trusted
//!   policy context — Dfa, Temporal, BridgePredicate — DELIBERATELY stay
//!   fail-closed in that default and are installed via
//!   `registry_with_real_verifiers_full(..)`. The `turn_executor_*` tests
//!   below pin THIS contract.
//!
//! For tests that previously relied on `default_builtins()` accepting
//! arbitrary non-empty proof bytes (the stub-verifier behavior), switch
//! to `WitnessedPredicateRegistry::with_stubs()` explicitly — that
//! constructor preserves the prior permissive shape under an honest
//! name and is kept for plumbing-only tests.

use dregg_cell::predicate::{
    InputRef, PredicateInput, WitnessedPredicate, WitnessedPredicateError, WitnessedPredicateKind,
    WitnessedPredicateRegistry,
};
use dregg_turn::ComputronCosts;
use dregg_turn::TurnExecutor;

// ─────────────────────────────────────────────────────────────────────
// Registry surface tests (default_builtins constructor)
// ─────────────────────────────────────────────────────────────────────

/// The default registry MUST reject Dfa proofs until a host installs the
/// real `dregg_circuit::dsl::circuit` adapter. Prior behavior was to
/// accept any non-empty proof bytes — a soundness loss caught by the
/// AIR audit.
#[test]
fn default_builtins_registry_rejects_dfa_until_host_wires_real_verifier() {
    let reg = WitnessedPredicateRegistry::default_builtins();
    let wp = WitnessedPredicate::dfa([1u8; 32], InputRef::Sender, 0);
    let pk = [0u8; 32];
    let input = PredicateInput::Sender(&pk);
    let err = reg.verify(&wp, &input, b"non-empty-proof").unwrap_err();
    assert!(
        matches!(err, WitnessedPredicateError::Rejected { .. }),
        "Dfa default must REJECT until host installs real verifier; got {err:?}"
    );
}

#[test]
fn default_builtins_registry_rejects_merkle_membership_until_host_wires_real_verifier() {
    let reg = WitnessedPredicateRegistry::default_builtins();
    let wp = WitnessedPredicate::merkle_membership([2u8; 32], InputRef::Sender, 0);
    let pk = [0u8; 32];
    let input = PredicateInput::Sender(&pk);
    let err = reg.verify(&wp, &input, b"non-empty-proof").unwrap_err();
    assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
}

#[test]
fn default_builtins_registry_rejects_blinded_set_until_host_wires_real_verifier() {
    let reg = WitnessedPredicateRegistry::default_builtins();
    let wp = WitnessedPredicate::blinded_set([3u8; 32], InputRef::Sender, 0);
    let pk = [0u8; 32];
    let err = reg
        .verify(&wp, &PredicateInput::Sender(&pk), b"non-empty-proof")
        .unwrap_err();
    assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
}

#[test]
fn default_builtins_registry_rejects_temporal_bridge_pedersen_until_host_wires_real_verifier() {
    let reg = WitnessedPredicateRegistry::default_builtins();
    for wp in [
        WitnessedPredicate::temporal([4u8; 32], 0, 0),
        WitnessedPredicate::bridge_predicate([5u8; 32], InputRef::PublicInput { pi_index: 0 }, 0),
        WitnessedPredicate::pedersen_equality([6u8; 32], InputRef::Slot { index: 0 }, 0),
    ] {
        let pk = [0u8; 32];
        let err = reg
            .verify(&wp, &PredicateInput::Sender(&pk), b"non-empty-proof")
            .unwrap_err();
        assert!(
            matches!(err, WitnessedPredicateError::Rejected { .. }),
            "default-builtin {:?} must reject until host installs real verifier; got {err:?}",
            wp.kind
        );
    }
}

/// The `with_stubs()` constructor preserves the *prior* permissive
/// behavior under an explicit, honest name — for plumbing-only tests.
#[test]
fn with_stubs_registry_still_accepts_nonempty_proof_for_plumbing_tests() {
    let reg = WitnessedPredicateRegistry::with_stubs();
    let wp = WitnessedPredicate::dfa([0u8; 32], InputRef::Sender, 0);
    let pk = [0u8; 32];
    reg.verify(&wp, &PredicateInput::Sender(&pk), b"non-empty-proof")
        .expect("with_stubs() preserves the prior permissive behavior for plumbing tests");
}

#[test]
fn default_builtins_registry_rejects_empty_proof() {
    let reg = WitnessedPredicateRegistry::default_builtins();
    let wp = WitnessedPredicate::dfa([0u8; 32], InputRef::Sender, 0);
    let pk = [0u8; 32];
    let err = reg
        .verify(&wp, &PredicateInput::Sender(&pk), b"")
        .unwrap_err();
    assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
}

#[test]
fn default_builtins_registry_unknown_custom_not_registered() {
    let reg = WitnessedPredicateRegistry::default_builtins();
    let wp = WitnessedPredicate::custom([99u8; 32], [0u8; 32], InputRef::Sender, 0);
    let pk = [0u8; 32];
    let err = reg
        .verify(&wp, &PredicateInput::Sender(&pk), b"proof")
        .unwrap_err();
    assert!(matches!(
        err,
        WitnessedPredicateError::KindNotRegistered {
            kind: WitnessedPredicateKind::Custom { .. }
        }
    ));
}

// ─────────────────────────────────────────────────────────────────────
// TurnExecutor wiring: the registry is now non-None by default.
// ─────────────────────────────────────────────────────────────────────

/// A bare `TurnExecutor::new()` defaults to the REAL-verifier registry
/// (`registry_with_real_verifiers`), NOT cell's fail-closed
/// `default_builtins`. The context-free crypto kinds get genuine STARK /
/// Bulletproof verifiers; the three context-dependent kinds deliberately stay
/// fail-closed until the host wires their policy authorities. (Both polarities
/// of the MerkleMembership default are proven end-to-end in
/// `dregg_turn::executor::membership_verifier`'s
/// `default_executor_admits_valid_membership_and_rejects_forge`.)
#[test]
fn turn_executor_new_defaults_to_real_verifier_registry() {
    let executor = TurnExecutor::new(ComputronCosts::zero());
    assert!(
        executor.witnessed_registry.is_some(),
        "TurnExecutor::new must default-equip the witnessed registry"
    );
    let reg = executor.witnessed_registry.as_ref().unwrap();

    // Every builtin kind is present (dispatch is always live).
    for kind in [
        WitnessedPredicateKind::Dfa,
        WitnessedPredicateKind::Temporal,
        WitnessedPredicateKind::MerkleMembership,
        WitnessedPredicateKind::NonMembership,
        WitnessedPredicateKind::BlindedSet,
        WitnessedPredicateKind::BridgePredicate,
        WitnessedPredicateKind::PedersenEquality,
    ] {
        assert!(reg.get(kind).is_some(), "{kind:?} must be registered");
    }

    // The context-free crypto kinds are the REAL verifiers by default —
    // this is what distinguishes the turn-layer default from cell's
    // fail-closed `default_builtins()`.
    assert_eq!(
        reg.get(WitnessedPredicateKind::MerkleMembership)
            .unwrap()
            .name(),
        "merkle-membership-stark",
        "bare-executor default must install the real MerkleMembership STARK verifier"
    );
    assert_eq!(
        reg.get(WitnessedPredicateKind::NonMembership).unwrap().name(),
        "sorted-neighbor-non-membership",
    );
    assert_eq!(
        reg.get(WitnessedPredicateKind::BlindedSet).unwrap().name(),
        "credential-set-membership",
    );

    // The DELIBERATE-DECISION half: kinds needing host-trusted policy
    // context stay fail-closed (NotYetWired) — they cannot have a safe
    // context-free default and are installed via
    // `registry_with_real_verifiers_full(..)`. A `non-empty-proof` against
    // them must be Rejected, not accepted.
    for wp in [
        WitnessedPredicate::dfa([1u8; 32], InputRef::Sender, 0),
        WitnessedPredicate::temporal([2u8; 32], 0, 0),
        WitnessedPredicate::bridge_predicate([3u8; 32], InputRef::PublicInput { pi_index: 0 }, 0),
    ] {
        let pk = [0u8; 32];
        let err = reg
            .verify(&wp, &PredicateInput::Sender(&pk), b"non-empty-proof")
            .unwrap_err();
        assert!(
            matches!(err, WitnessedPredicateError::Rejected { .. }),
            "context-dependent kind {:?} must stay fail-closed in the default; got {err:?}",
            wp.kind
        );
    }
}

#[test]
fn turn_executor_can_swap_registry() {
    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    // Custom-only registry.
    let mut custom_reg = WitnessedPredicateRegistry::empty();
    struct AcceptAll;
    impl dregg_cell::predicate::WitnessedPredicateVerifier for AcceptAll {
        fn name(&self) -> &'static str {
            "test-accept-all"
        }
        fn kind(&self) -> WitnessedPredicateKind {
            WitnessedPredicateKind::Custom {
                vk_hash: [0xAA; 32],
            }
        }
        fn verify(
            &self,
            _commitment: &[u8; 32],
            _input: &PredicateInput<'_>,
            _proof_bytes: &[u8],
        ) -> Result<(), WitnessedPredicateError> {
            Ok(())
        }
    }
    custom_reg.register_custom([0xAA; 32], std::sync::Arc::new(AcceptAll));
    executor.set_witnessed_registry(custom_reg);

    // The default builtins are now gone.
    let reg = executor.witnessed_registry.as_ref().unwrap();
    assert!(reg.get(WitnessedPredicateKind::Dfa).is_none());
    // The custom kind dispatches.
    let wp = WitnessedPredicate::custom([0xAA; 32], [0u8; 32], InputRef::Sender, 0);
    let pk = [0u8; 32];
    reg.verify(&wp, &PredicateInput::Sender(&pk), b"any-proof-even-empty")
        .expect("custom AcceptAll verifier should accept");
}

// ─────────────────────────────────────────────────────────────────────
// Tampered witness rejects: an empty Dfa proof routes through the
// fail-closed (NotYetWired) default-registry path.
// ─────────────────────────────────────────────────────────────────────

#[test]
fn tampered_empty_proof_rejects_through_executor_registry() {
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let reg = executor.witnessed_registry.as_ref().unwrap();
    // Dfa stays fail-closed in the bare-executor default (host-policy kind),
    // so any proof — empty or not — is Rejected.
    let wp = WitnessedPredicate::dfa([0u8; 32], InputRef::Sender, 0);
    let pk = [0u8; 32];
    let err = reg
        .verify(&wp, &PredicateInput::Sender(&pk), b"")
        .unwrap_err();
    assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
}

#[test]
fn unregistered_custom_yields_kind_not_registered_through_executor() {
    let executor = TurnExecutor::new(ComputronCosts::zero());
    let reg = executor.witnessed_registry.as_ref().unwrap();
    let wp = WitnessedPredicate::custom([0xFF; 32], [0u8; 32], InputRef::Sender, 0);
    let pk = [0u8; 32];
    let err = reg
        .verify(&wp, &PredicateInput::Sender(&pk), b"proof")
        .unwrap_err();
    assert!(matches!(
        err,
        WitnessedPredicateError::KindNotRegistered { .. }
    ));
}
