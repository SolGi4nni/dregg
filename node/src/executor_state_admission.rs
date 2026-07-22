//! Reconstruction and admission rules for short-lived node executors.
//!
//! A node constructs a fresh [`dregg_turn::TurnExecutor`] for each admission or
//! re-execution.  State which is not in the ledger therefore has to be restored
//! explicitly before `execute`: an empty executor side table is not a valid
//! synonym for an empty consensus history.
//!
//! This module owns the two fail-closed pieces that do not require changing the
//! executor's storage representation:
//!
//! - restore every agent-scoped receipt head from the already verified durable
//!   receipt log, rather than relying on individual ingress handlers to seed the
//!   one agent they happen to know about; and
//! - keep the staged exact FNSP-v3 route single-effect until the remaining
//!   executor side tables have one durable, shared owner.  In particular, an
//!   exact spend cannot currently be composed in the same turn with a second
//!   spend, a reward write, a bridge, or another stateful effect and still claim
//!   that the proof-local subreceipt covers the whole mutable executor frame.

use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fmt;

use dregg_cell::{CellId, CellProgram, Ledger, StateConstraint};
use dregg_turn::faithful_note_spend_exact_v3::{
    FAITHFUL_NOTE_SPEND_EXACT_V3_MAGIC, FAITHFUL_NOTE_SPEND_EXACT_V3_VERSION,
    FaithfulNoteSpendExactV3ProofCarrier,
};
use dregg_turn::{Effect, Turn, TurnExecutor, TurnReceipt};

/// A durable receipt log failed its per-agent causal-chain invariant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReceiptHeadRestoreError {
    pub(crate) log_index: usize,
    pub(crate) agent: CellId,
    pub(crate) expected: Option<[u8; 32]>,
    pub(crate) got: Option<[u8; 32]>,
}

impl fmt::Display for ReceiptHeadRestoreError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "receipt log index {} for agent {:?} names predecessor {:?}, expected {:?}",
            self.log_index, self.agent, self.got, self.expected
        )
    }
}

impl Error for ReceiptHeadRestoreError {}

/// Restore every agent-scoped receipt head into a fresh executor.
///
/// Validation is a separate first pass: a malformed suffix cannot partially
/// seed some heads and then fail.  `AgentCipherclerk::restore_receipt_chain`
/// already performs the same check at boot; repeating the inexpensive hash
/// walk here makes this constructor boundary independently fail closed and
/// keeps callers from accidentally passing an unverified log in the future.
pub(crate) fn restore_executor_receipt_heads(
    executor: &TurnExecutor,
    receipt_log: &[TurnReceipt],
) -> Result<usize, ReceiptHeadRestoreError> {
    let mut heads: HashMap<CellId, [u8; 32]> = HashMap::new();
    for (log_index, receipt) in receipt_log.iter().enumerate() {
        let expected = heads.get(&receipt.agent).copied();
        if receipt.previous_receipt_hash != expected {
            return Err(ReceiptHeadRestoreError {
                log_index,
                agent: receipt.agent,
                expected,
                got: receipt.previous_receipt_hash,
            });
        }
        heads.insert(receipt.agent, receipt.receipt_hash());
    }

    let restored = heads.len();
    for (agent, head) in heads {
        executor.set_last_receipt_hash(agent, head);
    }
    Ok(restored)
}

/// Why an exact FNSP-v3 route was refused before execution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ExactFnspV3RouteFenceError {
    MalformedCarrier {
        reason: String,
    },
    MultipleExactSpends {
        count: usize,
    },
    MixedEffects {
        exact_spends: usize,
        other_effects: usize,
    },
    UnsupportedForestShape,
    ExecutorRateConstraint {
        cell: CellId,
    },
}

impl fmt::Display for ExactFnspV3RouteFenceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MalformedCarrier { reason } => {
                write!(f, "exact FNSP-v3 carrier is malformed: {reason}")
            }
            Self::MultipleExactSpends { count } => write!(
                f,
                "exact FNSP-v3 route contains {count} exact spends; the staged receipt epoch admits exactly one"
            ),
            Self::MixedEffects {
                exact_spends,
                other_effects,
            } => write!(
                f,
                "exact FNSP-v3 route mixes {exact_spends} exact spend(s) with {other_effects} other effect(s); compose the proven spend and consequence as separately finalized turns"
            ),
            Self::UnsupportedForestShape => f.write_str(
                "exact FNSP-v3 route must be one root action with no child actions and one direct exact NoteSpend",
            ),
            Self::ExecutorRateConstraint { cell } => write!(
                f,
                "exact FNSP-v3 actor/target cell {cell:?} uses executor-local RateLimit or RateLimitBySum state"
            ),
        }
    }
}

impl Error for ExactFnspV3RouteFenceError {}

#[derive(Default)]
struct ExactRouteShape {
    exact_spends: usize,
    other_effects: usize,
    exact_targets: HashSet<CellId>,
}

fn is_exact_v3_carrier(bytes: &[u8]) -> bool {
    bytes.starts_with(&FAITHFUL_NOTE_SPEND_EXACT_V3_MAGIC)
        && bytes.get(FAITHFUL_NOTE_SPEND_EXACT_V3_MAGIC.len())
            == Some(&FAITHFUL_NOTE_SPEND_EXACT_V3_VERSION)
}

/// Whether `turn` has the one direct forest shape admitted by the staged exact
/// route. Callers must run [`validate_exact_fnsp_v3_route`] first; this helper
/// classifies producer selection and deliberately does not re-decode the proof.
pub(crate) fn is_strict_exact_fnsp_v3_route(turn: &Turn) -> bool {
    turn.call_forest.roots.len() == 1
        && turn.call_forest.roots[0].children.is_empty()
        && turn.call_forest.roots[0].action.effects.len() == 1
        && matches!(
            &turn.call_forest.roots[0].action.effects[0],
            Effect::NoteSpend { spending_proof, .. } if is_exact_v3_carrier(spending_proof)
        )
}

fn visit_effect(
    effect: &Effect,
    target: CellId,
    shape: &mut ExactRouteShape,
) -> Result<(), ExactFnspV3RouteFenceError> {
    // Inspect capability-wrapped leaves so embedding exact carrier bytes cannot
    // evade classification. The strict direct-shape check below then rejects
    // the wrapper before the executor can consume an installed exact token.
    if let Effect::ExerciseViaCapability { inner_effects, .. } = effect {
        for inner in inner_effects {
            visit_effect(inner, target, shape)?;
        }
        return Ok(());
    }

    if let Effect::NoteSpend { spending_proof, .. } = effect
        && is_exact_v3_carrier(spending_proof)
    {
        FaithfulNoteSpendExactV3ProofCarrier::decode(spending_proof).map_err(|error| {
            ExactFnspV3RouteFenceError::MalformedCarrier {
                reason: error.to_string(),
            }
        })?;
        shape.exact_spends += 1;
        shape.exact_targets.insert(target);
    } else {
        shape.other_effects += 1;
    }
    Ok(())
}

/// Fence unsupported exact-v3 composition before any executor side table or
/// ledger mutation.
///
/// Turns without an exact-v3 carrier are unaffected.  A canonical exact-v3
/// turn currently admits one semantic leaf: the accepted `NoteSpend`.  The
/// reward/game/bridge consequence must land through its own finalized outbox
/// turn, where it receives its own full receipt and durable exactly-once key.
fn program_uses_executor_rate_state(program: &CellProgram) -> bool {
    let has_rate_constraint = |constraint: &StateConstraint| {
        matches!(
            constraint,
            StateConstraint::RateLimit { .. } | StateConstraint::RateLimitBySum { .. }
        )
    };
    match program {
        CellProgram::Predicate(constraints) => constraints.iter().any(has_rate_constraint),
        CellProgram::Cases(cases) => cases
            .iter()
            .flat_map(|case| &case.constraints)
            .any(has_rate_constraint),
        CellProgram::None | CellProgram::Circuit { .. } => false,
    }
}

pub(crate) fn validate_exact_fnsp_v3_route(
    turn: &Turn,
    ledger: &Ledger,
) -> Result<(), ExactFnspV3RouteFenceError> {
    let mut shape = ExactRouteShape::default();
    for tree in turn.call_forest.iter_dfs() {
        for effect in &tree.action.effects {
            visit_effect(effect, tree.action.target, &mut shape)?;
        }
    }

    if shape.exact_spends > 1 {
        return Err(ExactFnspV3RouteFenceError::MultipleExactSpends {
            count: shape.exact_spends,
        });
    }
    if shape.exact_spends == 1 && shape.other_effects != 0 {
        return Err(ExactFnspV3RouteFenceError::MixedEffects {
            exact_spends: shape.exact_spends,
            other_effects: shape.other_effects,
        });
    }
    if shape.exact_spends == 1 {
        // Match the staged executor-authority carrier exactly. Keeping this
        // shape strict prevents an authorization wrapper, empty sibling action,
        // or NoteCreate output from acquiring semantics outside the one exact
        // proof-local transition. Widen only with the authority and durable
        // commitment-side state in the same protocol epoch.
        if !is_strict_exact_fnsp_v3_route(turn) {
            return Err(ExactFnspV3RouteFenceError::UnsupportedForestShape);
        }

        // Both the actor and the action target can carry a program. Direct
        // NoteSpend has no journal entry naming either cell, so today's rate
        // counter recorder would leave these constraints perpetually at zero.
        // Refuse the staged exact route rather than accept under an undercount.
        shape.exact_targets.insert(turn.agent);
        for cell_id in shape.exact_targets {
            if ledger
                .get(&cell_id)
                .is_some_and(|cell| program_uses_executor_rate_state(&cell.program))
            {
                return Err(ExactFnspV3RouteFenceError::ExecutorRateConstraint { cell: cell_id });
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::{AuthRequired, Preconditions};
    use dregg_turn::faithful_note_spend_exact_v3::FaithfulNoteSpendExactV3ProofCarrier;
    use dregg_turn::{
        Action, Authorization, CallForest, CommitmentMode, ComputronCosts, DelegationMode, Finality,
    };

    fn receipt(agent: CellId, marker: u8, previous: Option<[u8; 32]>) -> TurnReceipt {
        TurnReceipt {
            turn_hash: [marker; 32],
            forest_hash: [marker.wrapping_add(1); 32],
            pre_state_hash: [marker.wrapping_add(2); 32],
            post_state_hash: [marker.wrapping_add(3); 32],
            timestamp: i64::from(marker),
            effects_hash: [marker.wrapping_add(4); 32],
            computrons_used: u64::from(marker),
            action_count: 1,
            previous_receipt_hash: previous,
            agent,
            federation_id: [0xF0; 32],
            routing_directives: Vec::new(),
            introduction_exports: Vec::new(),
            derivation_records: Vec::new(),
            emitted_events: Vec::new(),
            executor_signature: None,
            finality: Finality::Final,
            was_encrypted: false,
            was_burn: false,
            consumed_capabilities: Vec::new(),
        }
    }

    fn action(effects: Vec<Effect>) -> Action {
        Action {
            target: CellId([0x31; 32]),
            method: [0x32; 32],
            args: Vec::new(),
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects,
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: Vec::new(),
        }
    }

    fn turn(effects: Vec<Effect>) -> Turn {
        let mut call_forest = CallForest::new();
        call_forest.add_root(action(effects));
        Turn {
            agent: CellId([0x31; 32]),
            nonce: 0,
            call_forest,
            fee: 0,
            memo: None,
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: Vec::new(),
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

    fn exact_spend(marker: u8) -> Effect {
        Effect::NoteSpend {
            nullifier: dregg_cell::note::Nullifier([marker; 32]),
            note_tree_root: [marker.wrapping_add(1); 32],
            spending_proof: FaithfulNoteSpendExactV3ProofCarrier::new(
                u64::from(marker),
                vec![marker, marker.wrapping_add(1)],
            )
            .unwrap()
            .encode(),
            value: u64::from(marker),
            asset_type: 0,
            value_commitment: None,
        }
    }

    #[test]
    fn interleaved_durable_log_restores_each_agents_own_head() {
        let agent_a = CellId([0xA1; 32]);
        let agent_b = CellId([0xB1; 32]);
        let a1 = receipt(agent_a, 1, None);
        let b1 = receipt(agent_b, 2, None);
        let a2 = receipt(agent_a, 3, Some(a1.receipt_hash()));
        let expected_a = a2.receipt_hash();
        let expected_b = b1.receipt_hash();
        let executor = TurnExecutor::new(ComputronCosts::zero());

        assert_eq!(
            restore_executor_receipt_heads(&executor, &[a1, b1, a2]).unwrap(),
            2
        );
        assert_eq!(executor.get_last_receipt_hash(&agent_a), Some(expected_a));
        assert_eq!(executor.get_last_receipt_hash(&agent_b), Some(expected_b));
    }

    #[test]
    fn malformed_log_refuses_without_partially_seeding_heads() {
        let agent_a = CellId([0xA2; 32]);
        let agent_b = CellId([0xB2; 32]);
        let a1 = receipt(agent_a, 1, None);
        let b1 = receipt(agent_b, 2, None);
        let forged = receipt(agent_a, 3, Some(b1.receipt_hash()));
        let executor = TurnExecutor::new(ComputronCosts::zero());

        assert!(restore_executor_receipt_heads(&executor, &[a1, b1, forged]).is_err());
        assert_eq!(executor.get_last_receipt_hash(&agent_a), None);
        assert_eq!(executor.get_last_receipt_hash(&agent_b), None);
    }

    #[test]
    fn signed_turn_predecessor_cannot_overwrite_restored_some_or_none() {
        let public_key = [0x61; 32];
        let token_id = [0x62; 32];
        let cell = dregg_cell::Cell::with_balance(public_key, token_id, 1_000);
        let agent = cell.id();
        let mut ledger = Ledger::new();
        ledger.insert_cell(cell).unwrap();

        let durable = receipt(agent, 9, None);
        let durable_hash = durable.receipt_hash();
        let executor = TurnExecutor::new(ComputronCosts::zero());
        restore_executor_receipt_heads(&executor, &[durable]).unwrap();
        let mut omitted = turn(Vec::new());
        omitted.agent = agent;
        omitted.call_forest.roots[0].action.target = agent;
        omitted.previous_receipt_hash = None;
        let (reason, _) = executor.execute(&omitted, &mut ledger).unwrap_rejected();
        assert!(matches!(
            reason,
            dregg_turn::TurnError::ReceiptChainMismatch {
                expected: Some(expected),
                got: None
            } if expected == durable_hash
        ));
        assert_eq!(executor.get_last_receipt_hash(&agent), Some(durable_hash));

        let genesis_executor = TurnExecutor::new(ComputronCosts::zero());
        let hostile_claim = [0xEE; 32];
        let mut invented = turn(Vec::new());
        invented.agent = agent;
        invented.call_forest.roots[0].action.target = agent;
        invented.previous_receipt_hash = Some(hostile_claim);
        let (reason, _) = genesis_executor
            .execute(&invented, &mut ledger)
            .unwrap_rejected();
        assert!(matches!(
            reason,
            dregg_turn::TurnError::ReceiptChainMismatch {
                expected: None,
                got: Some(got)
            } if got == hostile_claim
        ));
        assert_eq!(genesis_executor.get_last_receipt_hash(&agent), None);
    }

    #[test]
    fn exact_v3_route_is_single_semantic_effect_only() {
        let direct = turn(vec![exact_spend(7)]);
        validate_exact_fnsp_v3_route(&direct, &Ledger::new()).unwrap();
        assert!(is_strict_exact_fnsp_v3_route(&direct));

        let mixed = turn(vec![
            exact_spend(7),
            Effect::SetField {
                cell: CellId([0x44; 32]),
                index: 0,
                value: [1u8; 32],
            },
        ]);
        assert!(matches!(
            validate_exact_fnsp_v3_route(&mixed, &Ledger::new()),
            Err(ExactFnspV3RouteFenceError::MixedEffects {
                exact_spends: 1,
                other_effects: 1
            })
        ));

        assert!(matches!(
            validate_exact_fnsp_v3_route(
                &turn(vec![exact_spend(7), exact_spend(8)]),
                &Ledger::new()
            ),
            Err(ExactFnspV3RouteFenceError::MultipleExactSpends { count: 2 })
        ));
    }

    #[test]
    fn non_exact_turns_are_outside_the_staging_fence() {
        let ordinary = turn(vec![Effect::SetField {
            cell: CellId([0x55; 32]),
            index: 1,
            value: [2u8; 32],
        }]);
        validate_exact_fnsp_v3_route(&ordinary, &Ledger::new()).unwrap();
    }

    #[test]
    fn malformed_exact_v3_carrier_refuses_at_the_route_boundary() {
        let mut malformed = exact_spend(7);
        let Effect::NoteSpend { spending_proof, .. } = &mut malformed else {
            unreachable!()
        };
        spending_proof.truncate(7);
        assert!(matches!(
            validate_exact_fnsp_v3_route(&turn(vec![malformed]), &Ledger::new()),
            Err(ExactFnspV3RouteFenceError::MalformedCarrier { .. })
        ));
    }

    #[test]
    fn capability_wrapper_cannot_select_the_direct_exact_route() {
        let wrapped = turn(vec![Effect::ExerciseViaCapability {
            cap_slot: 0,
            inner_effects: vec![exact_spend(9)],
        }]);
        assert_eq!(
            validate_exact_fnsp_v3_route(&wrapped, &Ledger::new()),
            Err(ExactFnspV3RouteFenceError::UnsupportedForestShape)
        );
    }

    #[test]
    fn exact_route_refuses_actor_or_target_executor_rate_program() {
        let mut cell = dregg_cell::Cell::with_balance([0x71; 32], [0x72; 32], 10);
        cell.program = CellProgram::Predicate(vec![StateConstraint::RateLimit {
            max_per_epoch: 1,
            epoch_duration: 10,
        }]);
        let cell_id = cell.id();
        let mut ledger = Ledger::new();
        ledger.insert_cell(cell).unwrap();
        let mut exact = turn(vec![exact_spend(9)]);
        exact.agent = cell_id;

        assert!(matches!(
            validate_exact_fnsp_v3_route(&exact, &ledger),
            Err(ExactFnspV3RouteFenceError::ExecutorRateConstraint { cell }) if cell == cell_id
        ));

        let mut target = dregg_cell::Cell::with_balance([0x81; 32], [0x82; 32], 10);
        target.program = CellProgram::Predicate(vec![StateConstraint::RateLimitBySum {
            slot_index: 0,
            max_sum_per_epoch: 5,
            epoch_duration: 10,
        }]);
        let target_id = target.id();
        ledger.insert_cell(target).unwrap();
        let mut targeted = turn(vec![exact_spend(10)]);
        targeted.call_forest.roots[0].action.target = target_id;

        assert!(matches!(
            validate_exact_fnsp_v3_route(&targeted, &ledger),
            Err(ExactFnspV3RouteFenceError::ExecutorRateConstraint { cell }) if cell == target_id
        ));
    }

    // Keep the imported authorization vocabulary pinned: a future change that
    // makes the test action proof-authorized must not silently broaden it.
    const _: AuthRequired = AuthRequired::None;
}
