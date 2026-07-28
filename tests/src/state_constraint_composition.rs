//! Composition tests: multiple `StateConstraint` variants on one cell,
//! conjunction enforcement, and cross-cutting compositions with cap
//! caveats / `Authorization::Custom` / γ.2 binding.
//!
//! Each test in this file **explicitly notes** what variants / threats /
//! primitives it composes — composition tests are where the substrate
//! actually proves itself. Per the mandate: "atomicity" tests cover one
//! variant; "composition" tests cover the interactions that emerge when
//! multiple caveats fire on the same turn.
//!
//! Layer: cell-side evaluator + (where applicable) executor.
//!
//! ⚠ This header used to end "Tests that require pieces of the caveat-correctness
//! lane to land carry an `#[ignore = "..."]` with unblock label." As of
//! 2026-07-27 there are none: the last one
//! (`cross_federation_captp_delivered_with_sovereign_and_bilateral`) was waiting
//! on three lanes, two of which had been CANCELLED rather than completed. A
//! header that promises a quarantine which is not in force is the same defect as
//! a reason string that outlives its referent.

use std::collections::HashMap;
use std::sync::Arc;

use dregg_cell::predicate::{
    InputRef, PredicateInput, WitnessedPredicate, WitnessedPredicateError, WitnessedPredicateKind,
    WitnessedPredicateRegistry, WitnessedPredicateVerifier,
};
use dregg_cell::program::{
    SimpleStateConstraint, TransitionMeta, WitnessBlobView, WitnessBundle, WitnessKindTag,
};
use dregg_cell::{
    AuthRequired, Cell, CellId, CellProgram, CellState, EvalContext, Ledger, Permissions,
    ProgramError, StateConstraint, field_from_u64,
};
use dregg_turn::action::{
    Action, Authorization, CommitmentMode, DelegationMode, WitnessBlob, symbol,
};
use dregg_turn::{CallForest, ComputronCosts, Effect, Turn, TurnBuilder, TurnExecutor, TurnResult};

fn state_with(field_values: &[(usize, u64)]) -> CellState {
    let mut s = CellState::default();
    for (idx, val) in field_values {
        s.fields[*idx] = field_from_u64(*val);
    }
    s
}

struct ExactSlotVerifier {
    vk_hash: [u8; 32],
    expected_commitment: [u8; 32],
    expected_slot: dregg_cell::FieldElement,
    expected_proof: &'static [u8],
}

impl WitnessedPredicateVerifier for ExactSlotVerifier {
    fn name(&self) -> &'static str {
        "composition-exact-slot-verifier"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::Custom {
            vk_hash: self.vk_hash,
        }
    }

    fn verify(
        &self,
        commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        if commitment != &self.expected_commitment {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: "commitment mismatch".into(),
            });
        }
        match input {
            PredicateInput::Slot(slot) if **slot == self.expected_slot => {}
            PredicateInput::Slot(_) => {
                return Err(WitnessedPredicateError::Rejected {
                    kind_name: self.name(),
                    reason: "slot snapshot mismatch".into(),
                });
            }
            _ => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: self.name(),
                    expected: "Slot",
                    actual: "non-Slot",
                });
            }
        }
        if proof_bytes != self.expected_proof {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: "fresh witness proof mismatch".into(),
            });
        }
        Ok(())
    }
}

struct ExpectedCustomAuthVerifier {
    vk_hash: [u8; 32],
    expected_message: Vec<u8>,
    expected_proof: Vec<u8>,
}

impl WitnessedPredicateVerifier for ExpectedCustomAuthVerifier {
    fn name(&self) -> &'static str {
        "composition-expected-custom-auth-verifier"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::Custom {
            vk_hash: self.vk_hash,
        }
    }

    fn verify(
        &self,
        _commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        let bytes: &[u8] = match input {
            PredicateInput::AuthContext {
                signing_message, ..
            } => signing_message,
            PredicateInput::SigningMessage(bytes) => bytes,
            _ => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: self.name(),
                    expected: "AuthContext / SigningMessage",
                    actual: "non-SigningMessage",
                });
            }
        };
        if bytes != self.expected_message.as_slice() {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: "signing message mismatch".into(),
            });
        }
        if proof_bytes != self.expected_proof {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: self.name(),
                reason: "proof mismatch".into(),
            });
        }
        Ok(())
    }
}

fn make_custom_authorized_cell(seed: u8, vk_hash: [u8; 32], program: CellProgram) -> Cell {
    let mut public_key = [0u8; 32];
    public_key[0] = seed;
    let mut cell = Cell::with_balance(public_key, [0u8; 32], 1);
    cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::Custom { vk_hash },
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    cell.program = program;
    cell
}

fn make_open_programmed_cell(seed: u8, balance: u64, program: CellProgram) -> Cell {
    let mut public_key = [0u8; 32];
    public_key[0] = seed;
    public_key[31] = seed.wrapping_mul(7);
    let mut cell = Cell::with_balance(
        public_key,
        [0u8; 32],
        i64::try_from(balance).expect("balance fits i64"),
    );
    cell.permissions = Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    };
    cell.program = program;
    cell
}

fn set_fields_turn(agent: CellId, nonce: u64, effects: Vec<Effect>) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent,
        method: symbol("composition_set_fields"),
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    });
    Turn {
        agent,
        nonce,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

fn custom_set_field_action(
    target: CellId,
    predicate: WitnessedPredicate,
    proof: Vec<u8>,
) -> Action {
    Action {
        target,
        method: symbol("composition_custom_set_field"),
        args: vec![],
        authorization: Authorization::Custom { predicate },
        preconditions: Default::default(),
        effects: vec![Effect::SetField {
            cell: target,
            index: 0,
            value: field_from_u64(42),
        }],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![WitnessBlob::proof(proof)],
    }
}

// ===========================================================================
// Composition: Predicate(Vec<>) is a conjunction
// ===========================================================================

#[test]
fn predicate_vec_conjunction_all_must_hold() {
    // Composes: FieldEquals (slot 0 = 1) ∧ FieldGte (slot 1 ≥ 100) ∧ Immutable (slot 2).
    let constraints = vec![
        StateConstraint::FieldEquals {
            index: 0,
            value: field_from_u64(1),
        },
        StateConstraint::FieldGte {
            index: 1,
            value: field_from_u64(100),
        },
        StateConstraint::Immutable { index: 2 },
    ];
    let p = CellProgram::Predicate(constraints);

    let old = state_with(&[(2, 7)]);

    // Positive: all hold.
    let new = state_with(&[(0, 1), (1, 200), (2, 7)]);
    assert!(
        p.evaluate(&new, Some(&old), None).is_ok(),
        "all conjuncts hold"
    );

    // Negative: FieldEquals fails.
    let new = state_with(&[(0, 2), (1, 200), (2, 7)]);
    assert!(
        matches!(
            p.evaluate(&new, Some(&old), None),
            Err(ProgramError::ConstraintViolated { .. })
        ),
        "first conjunct must fail"
    );

    // Negative: Immutable fails.
    let new = state_with(&[(0, 1), (1, 200), (2, 8)]);
    assert!(
        matches!(
            p.evaluate(&new, Some(&old), None),
            Err(ProgramError::ConstraintViolated { .. })
        ),
        "last conjunct must fail"
    );
}

#[test]
fn predicate_vec_short_circuits_on_first_violation() {
    // Composes: FieldEquals (fails) + a sentinel-returning variant (TemporalPredicate).
    // If the conjunction short-circuits the first failure should win;
    // otherwise the sentinel may dominate. We allow either order — the
    // important thing is that the program rejects.
    let constraints = vec![
        StateConstraint::FieldEquals {
            index: 0,
            value: field_from_u64(1),
        },
        StateConstraint::TemporalPredicate {
            witness_index: 0,
            dsl_hash: [0u8; 32],
        },
    ];
    let p = CellProgram::Predicate(constraints);
    let new = state_with(&[(0, 9)]);
    assert!(p.evaluate(&new, None, None).is_err());
}

// ===========================================================================
// AnyOf composed with conjunction
// ===========================================================================

#[test]
fn any_of_inside_predicate_vec_works_as_or_inside_and() {
    // Composes: FieldEquals(0=1) ∧ (FieldEquals(1=2) ∨ FieldEquals(1=3)).
    let p = CellProgram::Predicate(vec![
        StateConstraint::FieldEquals {
            index: 0,
            value: field_from_u64(1),
        },
        StateConstraint::AnyOf {
            variants: vec![
                SimpleStateConstraint::FieldEquals {
                    index: 1,
                    value: field_from_u64(2),
                },
                SimpleStateConstraint::FieldEquals {
                    index: 1,
                    value: field_from_u64(3),
                },
            ],
        },
    ]);
    // Holds: slot0=1, slot1=2.
    assert!(
        p.evaluate(&state_with(&[(0, 1), (1, 2)]), None, None)
            .is_ok()
    );
    // Holds: slot0=1, slot1=3.
    assert!(
        p.evaluate(&state_with(&[(0, 1), (1, 3)]), None, None)
            .is_ok()
    );
    // Fails outer: slot0=2.
    assert!(
        p.evaluate(&state_with(&[(0, 2), (1, 2)]), None, None)
            .is_err()
    );
    // Fails AnyOf branch: slot0=1, slot1=4.
    assert!(
        p.evaluate(&state_with(&[(0, 1), (1, 4)]), None, None)
            .is_err()
    );
}

// ===========================================================================
// Mixed static + contextual + transition
// ===========================================================================

#[test]
fn mix_static_contextual_and_transition_constraints() {
    // Composes:
    //   FieldEquals(0=1)                    [static]
    //   TemporalGate(not_before=10)         [contextual]
    //   Monotonic(slot 1)                   [transition]
    let p = CellProgram::Predicate(vec![
        StateConstraint::FieldEquals {
            index: 0,
            value: field_from_u64(1),
        },
        StateConstraint::TemporalGate {
            not_before: Some(10),
            not_after: None,
        },
        StateConstraint::Monotonic { index: 1 },
    ]);
    let old = state_with(&[(1, 5)]);
    let new = state_with(&[(0, 1), (1, 7)]);
    let ctx = EvalContext::minimal(15, 0);
    assert!(p.evaluate(&new, Some(&old), Some(&ctx)).is_ok());

    // Block height below not_before → reject (TemporalGate fires).
    let ctx_early = EvalContext::minimal(5, 0);
    assert!(p.evaluate(&new, Some(&old), Some(&ctx_early)).is_err());

    // Slot 1 decreases → Monotonic fires.
    let new_bad = state_with(&[(0, 1), (1, 4)]);
    assert!(p.evaluate(&new_bad, Some(&old), Some(&ctx)).is_err());
}

// ===========================================================================
// Rate / window-sum composition
// ===========================================================================

#[test]
fn rate_limit_composes_with_temporal_gate_and_monotonic() {
    // Composes:
    //   TemporalGate(height in [10, 20])   [contextual]
    //   RateLimit(max 2 per epoch)         [contextual rate cap]
    //   Monotonic(slot 0)                  [transition]
    let p = CellProgram::Predicate(vec![
        StateConstraint::TemporalGate {
            not_before: Some(10),
            not_after: Some(20),
        },
        StateConstraint::RateLimit {
            max_per_epoch: 2,
            epoch_duration: 16,
        },
        StateConstraint::Monotonic { index: 0 },
    ]);
    let old = state_with(&[(0, 10)]);
    let new = state_with(&[(0, 11)]);

    let mut ctx = EvalContext::minimal(15, 0);
    ctx.sender = Some([7u8; 32]);
    ctx.sender_epoch_count = 1;
    assert!(
        p.evaluate(&new, Some(&old), Some(&ctx)).is_ok(),
        "inside window, under rate cap, and monotonic"
    );

    let mut at_cap = ctx.clone();
    at_cap.sender_epoch_count = 2;
    assert!(
        p.evaluate(&new, Some(&old), Some(&at_cap)).is_err(),
        "rate cap must reject even when temporal and monotonic constraints hold"
    );

    let decreasing = state_with(&[(0, 9)]);
    assert!(
        p.evaluate(&decreasing, Some(&old), Some(&ctx)).is_err(),
        "monotonic must reject even when temporal and rate constraints hold"
    );
}

#[test]
fn rate_limit_by_sum_composes_with_conservation() {
    // Composes:
    //   RateLimitBySum(slot 0 delta <= 25)         [window-sum approximation]
    //   SumEqualsAcross(input 0, output 1)         [intra-cell conservation]
    let p = CellProgram::Predicate(vec![
        StateConstraint::RateLimitBySum {
            slot_index: 0,
            max_sum_per_epoch: 25,
            epoch_duration: 64,
        },
        StateConstraint::SumEqualsAcross {
            input_fields: vec![0],
            output_fields: vec![1],
        },
    ]);
    let old = state_with(&[(0, 100), (1, 0)]);

    let balanced_under_cap = state_with(&[(0, 120), (1, 20)]);
    assert!(
        p.evaluate(&balanced_under_cap, Some(&old), None).is_ok(),
        "slot-0 delta is under cap and conservation holds"
    );

    let balanced_over_cap = state_with(&[(0, 140), (1, 40)]);
    assert!(
        p.evaluate(&balanced_over_cap, Some(&old), None).is_err(),
        "window-sum cap must reject even when conservation holds"
    );

    let unbalanced_under_cap = state_with(&[(0, 120), (1, 19)]);
    assert!(
        p.evaluate(&unbalanced_under_cap, Some(&old), None).is_err(),
        "conservation must reject even when the window-sum cap holds"
    );
}

// ===========================================================================
// Conservation + AllowedTransitions state-machine
// ===========================================================================

#[test]
fn conservation_with_state_machine_step() {
    // Composes: SumEqualsAcross (intra-cell conservation) + AllowedTransitions
    // (state field 7: open=1 → claimed=2 → delivered=3).
    let p = CellProgram::Predicate(vec![
        StateConstraint::SumEqualsAcross {
            input_fields: vec![0],
            output_fields: vec![1],
        },
        StateConstraint::AllowedTransitions {
            slot_index: 7,
            allowed: vec![
                (field_from_u64(1), field_from_u64(2)),
                (field_from_u64(2), field_from_u64(3)),
            ],
        },
    ]);
    let old = state_with(&[(0, 4), (1, 0), (7, 1)]);
    let new = state_with(&[(0, 10), (1, 6), (7, 2)]);
    assert!(
        p.evaluate(&new, Some(&old), None).is_ok(),
        "balanced + allowed transition"
    );

    // Conservation violated.
    let new_bad = state_with(&[(0, 10), (1, 5), (7, 2)]);
    assert!(
        p.evaluate(&new_bad, Some(&old), None).is_err(),
        "conservation breaks"
    );

    // State machine violated (skip to delivered without claiming).
    let new_bad2 = state_with(&[(0, 10), (1, 6), (7, 3)]);
    assert!(
        p.evaluate(&new_bad2, Some(&old), None).is_err(),
        "state machine skip"
    );
}

// ===========================================================================
// Cross-cutting: caveat-snapshot + fresh-witness predicate
// ===========================================================================

#[test]
fn caveat_snapshot_plus_fresh_witness_composition() {
    // Composes:
    //   - FieldEquals on slot 0 (stable slot snapshot)
    //   - Monotonic on slot 1 (transition caveat)
    //   - Witnessed(Custom) that reads slot 0 and consumes fresh proof bytes.
    let vk_hash = [0xA1u8; 32];
    let commitment = [0xC1u8; 32];
    let proof = b"fresh-proof";
    let mut registry = WitnessedPredicateRegistry::empty();
    registry.register_custom(
        vk_hash,
        Arc::new(ExactSlotVerifier {
            vk_hash,
            expected_commitment: commitment,
            expected_slot: field_from_u64(7),
            expected_proof: proof,
        }),
    );
    let blobs = [WitnessBlobView {
        kind: WitnessKindTag::ProofBytes,
        bytes: proof,
    }];
    let witnesses = WitnessBundle {
        blobs: &blobs,
        registry: Some(&registry),
        finalized_roots: None,
    };
    let program = CellProgram::Predicate(vec![
        StateConstraint::FieldEquals {
            index: 0,
            value: field_from_u64(7),
        },
        StateConstraint::Monotonic { index: 1 },
        StateConstraint::Witnessed {
            wp: WitnessedPredicate::custom(vk_hash, commitment, InputRef::Slot { index: 0 }, 0),
        },
    ]);
    let old = state_with(&[(1, 5)]);
    let new = state_with(&[(0, 7), (1, 6)]);
    program
        .evaluate_full(
            &new,
            Some(&old),
            None,
            &TransitionMeta::wildcard(),
            &witnesses,
        )
        .expect("slot caveats and fresh witnessed proof should compose");

    let stale_blobs = [WitnessBlobView {
        kind: WitnessKindTag::ProofBytes,
        bytes: b"stale-proof",
    }];
    let stale_witnesses = WitnessBundle {
        blobs: &stale_blobs,
        registry: Some(&registry),
        finalized_roots: None,
    };
    assert!(
        program
            .evaluate_full(
                &new,
                Some(&old),
                None,
                &TransitionMeta::wildcard(),
                &stale_witnesses,
            )
            .is_err(),
        "stale proof bytes must reject even when slot caveats pass"
    );
}

// ===========================================================================
// Cross-cutting: slot caveats + Auth::Custom
// ===========================================================================

#[test]
fn slot_caveats_plus_auth_custom_accepts() {
    // Executor-level composition for the currently-live layers:
    //   - slot caveats: Monotonic(0) ∧ TemporalGate(...),
    //   - Authorization::Custom over InputRef::SigningMessage.
    //
    // CapabilityCaveat enforcement is a separate layer and remains covered by
    // its own blocked workstream; this test avoids pretending that cap caveats
    // are enforced here.
    let vk_hash = [0xB1u8; 32];
    let federation_id = [0xF1u8; 32];
    let proof = b"valid-proof".to_vec();
    let program = CellProgram::Predicate(vec![
        StateConstraint::TemporalGate {
            not_before: Some(0),
            not_after: None,
        },
        StateConstraint::Monotonic { index: 0 },
    ]);
    let cell = make_custom_authorized_cell(41, vk_hash, program);
    let target = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let predicate = WitnessedPredicate::custom(vk_hash, [0u8; 32], InputRef::SigningMessage, 0);
    let action = custom_set_field_action(target, predicate.clone(), proof.clone());
    let expected_message =
        TurnExecutor::compute_custom_signing_message(&action, &predicate, 0, &federation_id, 0);
    let mut registry = WitnessedPredicateRegistry::empty();
    registry.register_custom(
        vk_hash,
        Arc::new(ExpectedCustomAuthVerifier {
            vk_hash,
            expected_message,
            expected_proof: proof,
        }),
    );
    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_local_federation_id(federation_id);
    executor.set_witnessed_registry(registry);
    let mut builder = TurnBuilder::new(target, 0);
    builder.add_action(action);
    let result = executor.execute(&builder.fee(0).build(), &mut ledger);
    assert!(
        result.is_committed(),
        "slot-caveat-valid Authorization::Custom turn should commit, got {result:?}"
    );
    assert_eq!(
        ledger.get(&target).unwrap().state.fields[0],
        field_from_u64(42)
    );
}

#[test]
fn tampered_auth_custom_rejected_even_when_slot_caveats_pass() {
    // Executor-level composition:
    //   - target cell requires Authorization::Custom for set_state,
    //   - target cell program enforces slot caveats,
    //   - Custom verifier rejects the proof while the slot caveats would pass.
    let vk_hash = [0xB2u8; 32];
    let federation_id = [0xF2u8; 32];
    let program = CellProgram::Predicate(vec![
        StateConstraint::TemporalGate {
            not_before: Some(0),
            not_after: None,
        },
        StateConstraint::Monotonic { index: 0 },
    ]);
    let cell = make_custom_authorized_cell(42, vk_hash, program);
    let target = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();

    let predicate = WitnessedPredicate::custom(vk_hash, [0u8; 32], InputRef::SigningMessage, 0);
    let action = custom_set_field_action(target, predicate.clone(), b"tampered-proof".to_vec());
    let expected_message =
        TurnExecutor::compute_custom_signing_message(&action, &predicate, 0, &federation_id, 0);
    let mut registry = WitnessedPredicateRegistry::empty();
    registry.register_custom(
        vk_hash,
        Arc::new(ExpectedCustomAuthVerifier {
            vk_hash,
            expected_message,
            expected_proof: b"valid-proof".to_vec(),
        }),
    );
    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_local_federation_id(federation_id);
    executor.set_witnessed_registry(registry);
    let mut builder = TurnBuilder::new(target, 0);
    builder.add_action(action);
    let result = executor.execute(&builder.fee(0).build(), &mut ledger);
    assert!(
        result.is_rejected(),
        "tampered Authorization::Custom proof must reject before committing slot-caveat-valid state"
    );
}

// ===========================================================================
// Cross-cutting: γ.2 bilateral binding + slot caveats on both cells
// ===========================================================================

#[test]
fn bilateral_transfer_with_slot_caveats_on_both_sides() {
    use dregg_cell::program::DeltaRelation;

    let mut sender = make_open_programmed_cell(0xA1, 1_000, CellProgram::None);
    let mut receiver = make_open_programmed_cell(0xB2, 1_000, CellProgram::None);
    let a_id = sender.id();
    let b_id = receiver.id();

    sender.program = CellProgram::Predicate(vec![
        StateConstraint::BoundDelta {
            local_slot: 0,
            peer_cell: b_id,
            peer_slot: 0,
            delta_relation: DeltaRelation::EqualAndOpposite,
        },
        StateConstraint::RateLimit {
            max_per_epoch: 3,
            epoch_duration: 16,
        },
    ]);
    receiver.program = CellProgram::Predicate(vec![
        StateConstraint::BoundDelta {
            local_slot: 0,
            peer_cell: a_id,
            peer_slot: 0,
            delta_relation: DeltaRelation::EqualAndOpposite,
        },
        StateConstraint::Monotonic { index: 0 },
    ]);

    sender.state.fields[0] = field_from_u64(100);
    receiver.state.fields[0] = field_from_u64(20);
    sender.capabilities.grant(b_id, AuthRequired::None).unwrap();

    let mut ledger = Ledger::new();
    ledger.insert_cell(sender).unwrap();
    ledger.insert_cell(receiver).unwrap();

    let turn = set_fields_turn(
        a_id,
        0,
        vec![
            Effect::SetField {
                cell: a_id,
                index: 0,
                value: field_from_u64(90),
            },
            Effect::SetField {
                cell: b_id,
                index: 0,
                value: field_from_u64(30),
            },
        ],
    );
    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        matches!(result, TurnResult::Committed { .. }),
        "matching bilateral BoundDelta plus sender RateLimit and receiver Monotonic must commit, got: {result:?}"
    );

    let mut bad_sender = make_open_programmed_cell(0xA1, 1_000, CellProgram::None);
    let mut bad_receiver = make_open_programmed_cell(0xB2, 1_000, CellProgram::None);
    bad_sender.program = CellProgram::Predicate(vec![
        StateConstraint::BoundDelta {
            local_slot: 0,
            peer_cell: b_id,
            peer_slot: 0,
            delta_relation: DeltaRelation::EqualAndOpposite,
        },
        StateConstraint::RateLimit {
            max_per_epoch: 3,
            epoch_duration: 16,
        },
    ]);
    bad_receiver.program = CellProgram::Predicate(vec![
        StateConstraint::BoundDelta {
            local_slot: 0,
            peer_cell: a_id,
            peer_slot: 0,
            delta_relation: DeltaRelation::EqualAndOpposite,
        },
        StateConstraint::Monotonic { index: 0 },
    ]);
    bad_sender.state.fields[0] = field_from_u64(100);
    bad_receiver.state.fields[0] = field_from_u64(20);
    bad_sender
        .capabilities
        .grant(b_id, AuthRequired::None)
        .unwrap();

    let mut bad_ledger = Ledger::new();
    bad_ledger.insert_cell(bad_sender).unwrap();
    bad_ledger.insert_cell(bad_receiver).unwrap();
    let bad_turn = set_fields_turn(
        a_id,
        0,
        vec![
            Effect::SetField {
                cell: a_id,
                index: 0,
                value: field_from_u64(110),
            },
            Effect::SetField {
                cell: b_id,
                index: 0,
                value: field_from_u64(10),
            },
        ],
    );
    let bad_result = TurnExecutor::new(ComputronCosts::zero()).execute(&bad_turn, &mut bad_ledger);
    assert!(
        matches!(bad_result, TurnResult::Rejected { .. }),
        "BoundDelta-valid transfer must still reject when receiver Monotonic fails, got: {bad_result:?}"
    );
}

// ===========================================================================
// Three-cell ring trade (Cav-Codex composition target)
// ===========================================================================

#[test]
fn three_cell_ring_trade_bound_delta() {
    use dregg_cell::program::DeltaRelation;

    let program_for = |peer_cell| {
        CellProgram::Predicate(vec![StateConstraint::BoundDelta {
            local_slot: 0,
            peer_cell,
            peer_slot: 0,
            delta_relation: DeltaRelation::Equal,
        }])
    };

    let mut cell_a = make_open_programmed_cell(0xA1, 1_000, CellProgram::None);
    let mut cell_b = make_open_programmed_cell(0xB2, 1_000, CellProgram::None);
    let mut cell_c = make_open_programmed_cell(0xC3, 1_000, CellProgram::None);
    let a = cell_a.id();
    let b = cell_b.id();
    let c = cell_c.id();
    cell_a.program = program_for(b);
    cell_b.program = program_for(c);
    cell_c.program = program_for(a);
    cell_a.state.fields[0] = field_from_u64(10);
    cell_b.state.fields[0] = field_from_u64(20);
    cell_c.state.fields[0] = field_from_u64(30);
    cell_a.capabilities.grant(b, AuthRequired::None).unwrap();
    cell_a.capabilities.grant(c, AuthRequired::None).unwrap();

    let mut ledger = Ledger::new();
    ledger.insert_cell(cell_a).unwrap();
    ledger.insert_cell(cell_b).unwrap();
    ledger.insert_cell(cell_c).unwrap();
    let result = TurnExecutor::new(ComputronCosts::zero()).execute(
        &set_fields_turn(
            a,
            0,
            vec![
                Effect::SetField {
                    cell: a,
                    index: 0,
                    value: field_from_u64(15),
                },
                Effect::SetField {
                    cell: b,
                    index: 0,
                    value: field_from_u64(25),
                },
                Effect::SetField {
                    cell: c,
                    index: 0,
                    value: field_from_u64(35),
                },
            ],
        ),
        &mut ledger,
    );
    assert!(
        matches!(result, TurnResult::Committed { .. }),
        "three-cell BoundDelta ring with all peer deltas paired must commit, got: {result:?}"
    );

    let mut bad_a = make_open_programmed_cell(0xA1, 1_000, CellProgram::None);
    let mut bad_b = make_open_programmed_cell(0xB2, 1_000, CellProgram::None);
    let mut bad_c = make_open_programmed_cell(0xC3, 1_000, CellProgram::None);
    bad_a.program = program_for(b);
    bad_b.program = program_for(c);
    bad_c.program = program_for(a);
    bad_a.state.fields[0] = field_from_u64(10);
    bad_b.state.fields[0] = field_from_u64(20);
    bad_c.state.fields[0] = field_from_u64(30);
    bad_a.capabilities.grant(b, AuthRequired::None).unwrap();
    bad_a.capabilities.grant(c, AuthRequired::None).unwrap();
    let mut bad_ledger = Ledger::new();
    bad_ledger.insert_cell(bad_a).unwrap();
    bad_ledger.insert_cell(bad_b).unwrap();
    bad_ledger.insert_cell(bad_c).unwrap();
    let bad_result = TurnExecutor::new(ComputronCosts::zero()).execute(
        &set_fields_turn(
            a,
            0,
            vec![
                Effect::SetField {
                    cell: a,
                    index: 0,
                    value: field_from_u64(15),
                },
                Effect::SetField {
                    cell: b,
                    index: 0,
                    value: field_from_u64(25),
                },
                Effect::SetField {
                    cell: c,
                    index: 0,
                    value: field_from_u64(34),
                },
            ],
        ),
        &mut bad_ledger,
    );
    assert!(
        matches!(bad_result, TurnResult::Rejected { .. }),
        "three-cell BoundDelta ring with one unpaired delta must reject, got: {bad_result:?}"
    );
}

// ===========================================================================
// Cross-federation composition: CapTpDelivered + sovereign witness + bilateral
// ===========================================================================

/// UNBLOCKED (2026-07-27). The `#[ignore]` cited three lanes; all three are
/// resolved, two of them by being cancelled:
///
///   * *caveat-correctness* — `CAVEAT-LAYER-COVERAGE.md`'s row 24 said the
///     executor "REJECTS `BoundDelta` unconditionally". Stale: the cross-cell
///     pass is wired (`execute_tree::validate_bound_delta_program`), and this
///     test uses the simpler `Monotonic`, which was never blocked at all.
///   * *γ.2 cross-federation* — the off-AIR verifier this file's siblings drive
///     is the whole γ.2 mechanism; the AIR sub-stage the reason waited for has a
///     RETIRED host (see the note on
///     `gamma2_bilateral_binding::coherent_two_sided_transfer_id_lie_…`).
///   * *sovereign-witness AIR teeth (SOVEREIGN-WITNESS-AIR-DESIGN.md)* — the
///     cited doc left the tree in May and is archived at
///     `.docs-history-noclaude/docs-old/`. Its Phase 1 landed as dead-zero PI
///     slots (no producer sets `EffectVmContext::is_sovereign_cell`) and its
///     Phase 2 is retired outright (`circuit/src/effect_vm/pi.rs:209`). The
///     sovereign teeth that actually bite are the EXECUTOR's.
///
/// ## Why this composition is worth a test and not just four tests
///
/// `CapTpDelivered` is the one authorization mode that **short-circuits the
/// permission lattice on purpose**. `executor/authorize.rs:124` verifies it
/// "holistically… regardless of the target cell's permission level" and
/// `return Ok(())`s before `check_single_auth_requirement` ever runs. That is
/// deliberate — the cert carries its own cryptographic provenance — but it makes
/// exactly one question urgent, and nothing in the tree asked it:
///
/// **does a valid CapTP delivery also short-circuit the gates that are NOT the
/// permission lattice?**
///
/// Three of them ride on the same turn here: the cell's slot caveat, the
/// sovereign witness, and the γ.2 cross-cell binding. An early `Ok` that
/// happened to skip past any of those would be a capability that confers
/// authority the introducer never held and the cell never agreed to.
///
/// ## The shape
///
/// One turn at FED_B whose action is authorized by an introducer-signed handoff
/// certificate issued for FED_B, targeting a cell that is SOVEREIGN at FED_B and
/// supplies its own witness, carrying a `Monotonic` slot caveat, and moving
/// value so the γ.2 schedule has something to bind. Then each gate is failed in
/// turn while the other three stay perfect.
#[test]
fn cross_federation_captp_delivered_with_sovereign_and_bilateral() {
    use dregg_captp::{FederationId, HandoffCertificate};
    use dregg_cell::Cell;
    use dregg_turn::action::Effect as Eff;
    use dregg_turn::{SovereignCellWitness, TurnError};
    use dregg_types::{SigningKey, sign};

    const FED_A: [u8; 32] = [0xAA; 32];
    const FED_B: [u8; 32] = [0u8; 32]; // the executor's default local federation
    const AMOUNT: u64 = 10;
    const SLOT_BEFORE: u64 = 10;
    const SLOT_AFTER: u64 = 20; // Monotonic ✓

    fn open_permissions() -> Permissions {
        Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        }
    }

    /// Bob: sovereign at FED_B, signs his own witness, carries a `Monotonic`
    /// caveat on slot 0. Because he carries a program, the implicit
    /// target-nonce bump never applies (`execute_tree.rs:1250`), so the hosted
    /// twin below is a faithful twin without adjustment.
    fn bob_cell() -> (Cell, SigningKey) {
        let key = SigningKey::from_bytes(&[0xB2; 32]);
        let mut cell = Cell::with_balance(*key.public_key().as_bytes(), [0u8; 32], 1_000);
        cell.permissions = open_permissions();
        cell.program = CellProgram::Predicate(vec![StateConstraint::Monotonic { index: 0 }]);
        cell.state.fields[0] = field_from_u64(SLOT_BEFORE);
        (cell, key)
    }

    fn plain_cell(seed: u8) -> Cell {
        let mut pk = [0u8; 32];
        pk[0] = seed;
        pk[31] = seed.wrapping_mul(29);
        let mut cell = Cell::with_balance(pk, [0u8; 32], 1_000);
        cell.permissions = open_permissions();
        cell
    }

    /// The turn: ONE action targeting bob, authorized by the CapTP delivery,
    /// carrying both the value movement (for γ.2) and the slot write (for the
    /// caveat).
    #[allow(clippy::too_many_arguments)]
    fn captp_turn(
        agent: CellId,
        bob_id: CellId,
        carol_id: CellId,
        local_fed: [u8; 32],
        cert: HandoffCertificate,
        introducer_pk: [u8; 32],
        recipient_key: &SigningKey,
        slot_value: u64,
        witnesses: HashMap<CellId, SovereignCellWitness>,
    ) -> Turn {
        let effects = vec![
            Eff::Transfer {
                from: bob_id,
                to: carol_id,
                amount: AMOUNT,
            },
            Eff::SetField {
                cell: bob_id,
                index: 0,
                value: field_from_u64(slot_value),
            },
        ];
        // The executor recomputes this message from the on-chain Turn using ITS
        // OWN federation id and `action.target` for both the agent and target
        // slots (`executor/authorize.rs:379`). Any divergence is a rejection,
        // which is what makes the FED_A replay leg below bite.
        let signing_msg = Authorization::captp_delivered_signing_message_for_federation(
            &local_fed,
            &cert.nonce,
            &bob_id,
            &bob_id,
            0,
            &effects,
        );
        let sender_signature = sign(recipient_key, &signing_msg).0;

        let mut call_forest = CallForest::new();
        call_forest.add_root(Action {
            target: bob_id,
            method: symbol("captp_mirror"),
            args: vec![],
            authorization: Authorization::CapTpDelivered {
                handoff_cert: cert,
                introducer_pk,
                sender_pk: *recipient_key.public_key().as_bytes(),
                sender_signature,
            },
            preconditions: Default::default(),
            effects,
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        });

        let mut turn = Turn {
            agent,
            nonce: 0,
            call_forest,
            fee: 0,
            memo: None,
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };
        turn.sovereign_witnesses = witnesses;
        turn
    }

    fn signed_witness(
        federation_id: &[u8; 32],
        cell: &Cell,
        key: &SigningKey,
        old_commitment: [u8; 32],
        new_commitment: [u8; 32],
        effects_hash: [u8; 32],
        sequence: u64,
    ) -> SovereignCellWitness {
        let cell_id = cell.id();
        let message = SovereignCellWitness::signing_message_for_federation(
            federation_id,
            &cell_id,
            &old_commitment,
            &new_commitment,
            &effects_hash,
            0,
            sequence,
        );
        SovereignCellWitness {
            cell_id,
            old_commitment,
            new_commitment,
            effects_hash,
            timestamp: 0,
            sequence,
            signature: sign(key, &message).0,
            cell_state: cell.clone(),
            transition_proof: None,
        }
    }

    // The introducer at FED_A: an untrusted-to-us key that signs the cert.
    let introducer_key = SigningKey::from_bytes(&[0x1D; 32]);
    let introducer_pk = *introducer_key.public_key().as_bytes();
    let (bob, bob_key) = bob_cell();
    let bob_id = bob.id();
    let carol = plain_cell(0xC3);
    let carol_id = carol.id();
    let agent = plain_cell(0x0A);
    let agent_id = agent.id();

    // A cert issued by FED_A's introducer, delegating authority over bob to
    // bob's own key, redeemable AT FED_B. `Signature` is strictly narrower than
    // bob's `None` floor, so the non-amplification gate is satisfied.
    let cert_for = |target_federation: [u8; 32]| {
        HandoffCertificate::create(
            &introducer_key,
            FederationId(FED_A),
            FederationId(target_federation),
            bob_id,
            *bob_key.public_key().as_bytes(),
            AuthRequired::Signature,
            None,
            None,
            None,
            [0u8; 32],
        )
    };

    let ledger_with = |bob_sovereign: bool| {
        let mut ledger = Ledger::new();
        let mut a = agent.clone();
        a.capabilities.grant(bob_id, AuthRequired::None).unwrap();
        a.capabilities.grant(carol_id, AuthRequired::None).unwrap();
        ledger.insert_cell(a).unwrap();
        ledger.insert_cell(carol.clone()).unwrap();
        if bob_sovereign {
            ledger
                .register_sovereign_cell(bob_id, bob.state_commitment())
                .unwrap();
        } else {
            ledger.insert_cell(bob.clone()).unwrap();
        }
        ledger
    };

    // ── The faithful twin: bob HOSTED, everything else identical. Bob carries a
    //    program, so the sovereign nonce exemption cannot make the two paths
    //    disagree, and this gives the exact post-state his witness must declare.
    let twin_turn = captp_turn(
        agent_id,
        bob_id,
        carol_id,
        FED_B,
        cert_for(FED_B),
        introducer_pk,
        &bob_key,
        SLOT_AFTER,
        HashMap::new(),
    );
    let mut twin_ledger = ledger_with(false);
    let twin = TurnExecutor::new(ComputronCosts::zero()).execute(&twin_turn, &mut twin_ledger);
    assert!(
        matches!(twin, TurnResult::Committed { .. }),
        "the HOSTED twin must commit — a CapTP delivery with no sovereign cell in \
         sight is the control for everything below: {twin:?}"
    );
    let bob_post = twin_ledger.get(&bob_id).unwrap().state_commitment();
    assert_ne!(
        bob_post,
        bob.state_commitment(),
        "anti-vacuity: the turn must actually move bob"
    );
    let bob_effects = twin_turn.sovereign_effects_hash(&bob_id);

    // ── LEG 1 (positive): cert ✓ + sovereign witness ✓ + Monotonic ✓ → commits,
    //    and the witness sequence is spent.
    let mut witnesses = HashMap::new();
    witnesses.insert(
        bob_id,
        signed_witness(
            &FED_B,
            &bob,
            &bob_key,
            bob.state_commitment(),
            bob_post,
            bob_effects,
            1,
        ),
    );
    let turn = captp_turn(
        agent_id,
        bob_id,
        carol_id,
        FED_B,
        cert_for(FED_B),
        introducer_pk,
        &bob_key,
        SLOT_AFTER,
        witnesses,
    );
    let mut ledger = ledger_with(true);
    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        matches!(&result, TurnResult::Committed { .. }),
        "a CapTP-delivered turn on a sovereign, caveat-bearing cell must commit \
         when all four gates are satisfied: {result:?}"
    );
    assert_eq!(
        ledger.last_sovereign_witness_sequence(&bob_id),
        1,
        "the CapTP path must not bypass the sovereign replay counter"
    );

    // ── LEG 2 (γ.2 over the same turn): the bilateral schedule binds the
    //    transfer, and a root tamper still rejects.
    let bundle = dregg_verifier::BilateralBundle {
        turn: turn.clone(),
        entries: [bob_id, carol_id]
            .iter()
            .map(|cell_id| dregg_verifier::BilateralEntry {
                cell_id: *cell_id,
                witnessed_receipt: dregg_verifier::fabricate_witnessed_receipt(
                    &turn,
                    cell_id,
                    captp_dummy_receipt(turn.agent),
                ),
            })
            .collect(),
        unilateral_attestations: std::collections::BTreeMap::new(),
    };
    let verdict = dregg_verifier::verify_bilateral_bundle(&bundle);
    assert!(
        verdict.verified,
        "γ.2 must bind the transfer a CapTP delivery carried: {verdict:?}"
    );
    assert_eq!(verdict.transfer_count, 1);

    let mut tampered = bundle;
    tampered.entries[1].witnessed_receipt.public_inputs
        [dregg_circuit::effect_vm::pi::INCOMING_TRANSFER_ROOT_BASE] ^= 1;
    assert!(
        !dregg_verifier::verify_bilateral_bundle(&tampered).verified,
        "the γ.2 tooth must survive the CapTP composition"
    );

    // ── LEG 3: THE SLOT CAVEAT. Cert perfect, witness perfect for the turn it
    //    rides — and the slot goes DOWN. The `Monotonic` caveat must refuse,
    //    which is the "does an early Ok skip the cell's own program?" question.
    let violating = 5u64; // SLOT_BEFORE = 10 → Monotonic ✗
    let twin_turn = captp_turn(
        agent_id,
        bob_id,
        carol_id,
        FED_B,
        cert_for(FED_B),
        introducer_pk,
        &bob_key,
        violating,
        HashMap::new(),
    );
    let mut witnesses = HashMap::new();
    witnesses.insert(
        bob_id,
        signed_witness(
            &FED_B,
            &bob,
            &bob_key,
            bob.state_commitment(),
            // The post-state a SUCCESSFUL apply would reach — so the witness is
            // not what is wrong here.
            {
                let mut post = bob.clone();
                post.state.set_field(0, field_from_u64(violating));
                post.state.set_balance(post.state.balance() - AMOUNT as i64);
                post.state_commitment()
            },
            twin_turn.sovereign_effects_hash(&bob_id),
            1,
        ),
    );
    let turn = captp_turn(
        agent_id,
        bob_id,
        carol_id,
        FED_B,
        cert_for(FED_B),
        introducer_pk,
        &bob_key,
        violating,
        witnesses,
    );
    let mut ledger = ledger_with(true);
    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: TurnError::ProgramViolation { .. },
                ..
            }
        ),
        "a CapTP handoff certificate must NOT confer the right to break the \
         target cell's own slot caveat: {result:?}"
    );
    assert_eq!(
        ledger.last_sovereign_witness_sequence(&bob_id),
        0,
        "a caveat rejection must not spend the sovereign sequence"
    );

    // ── LEG 4: THE SOVEREIGN WITNESS. Cert perfect, caveat satisfied, and the
    //    witness is signed for FED_A instead of FED_B. Valid signature, wrong
    //    federation — the cross-federation replay guard must refuse it even
    //    though the CERT is the thing that legitimately crossed federations.
    let mut witnesses = HashMap::new();
    witnesses.insert(
        bob_id,
        signed_witness(
            &FED_A,
            &bob,
            &bob_key,
            bob.state_commitment(),
            bob_post,
            bob_effects,
            1,
        ),
    );
    let turn = captp_turn(
        agent_id,
        bob_id,
        carol_id,
        FED_B,
        cert_for(FED_B),
        introducer_pk,
        &bob_key,
        SLOT_AFTER,
        witnesses,
    );
    let mut ledger = ledger_with(true);
    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: TurnError::InvalidEffect { reason },
                ..
            } if reason.contains("signature")
        ),
        "a cert that crossed federations does not license a witness that did: \
         {result:?}"
    );

    // ── LEG 5: THE CERT. Witness perfect, caveat satisfied, and the cert names
    //    FED_A as its target federation — i.e. it was issued for somewhere else
    //    and replayed here. `verify_captp_delivered` step 2 must refuse.
    let mut witnesses = HashMap::new();
    witnesses.insert(
        bob_id,
        signed_witness(
            &FED_B,
            &bob,
            &bob_key,
            bob.state_commitment(),
            bob_post,
            bob_effects,
            1,
        ),
    );
    let turn = captp_turn(
        agent_id,
        bob_id,
        carol_id,
        FED_B,
        cert_for(FED_A),
        introducer_pk,
        &bob_key,
        SLOT_AFTER,
        witnesses,
    );
    let mut ledger = ledger_with(true);
    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        matches!(
            &result,
            TurnResult::Rejected {
                reason: TurnError::InvalidAuthorization { reason },
                ..
            } if reason.contains("target_federation")
        ),
        "a handoff certificate issued for another federation must not redeem \
         here: {result:?}"
    );
}

/// A receipt shell for the γ.2 fabrication above. The bilateral verifier reads
/// the schedule out of the `Turn`, not out of the receipt, so the receipt only
/// has to exist.
fn captp_dummy_receipt(agent: CellId) -> dregg_turn::TurnReceipt {
    dregg_turn::TurnReceipt {
        turn_hash: [0u8; 32],
        forest_hash: [0u8; 32],
        pre_state_hash: [0u8; 32],
        post_state_hash: [0u8; 32],
        timestamp: 0,
        effects_hash: [0u8; 32],
        computrons_used: 0,
        action_count: 0,
        previous_receipt_hash: None,
        agent,
        federation_id: [0u8; 32],
        routing_directives: vec![],
        introduction_exports: vec![],
        derivation_records: vec![],
        emitted_events: vec![],
        executor_signature: None,
        finality: Default::default(),
        was_encrypted: false,
        was_burn: false,
        consumed_capabilities: vec![],
    }
}
