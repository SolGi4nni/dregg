//! Scripts — a recorded, replayable turn-sequence as a first-class value.
//!
//! A [`Script`] is the Tier-1 "macro": a named, content-addressed [`Pipeline`]
//! (the existing serializable turn-sequence carrier) that records a sequence of
//! turns and replays them through the REAL executor via [`execute_pipeline`].
//! No new kernel verb, no new circuit — it rides the proven pipeline machinery.
//!
//! This is the lean substrate under the Tier-2 design, where a (bounded) script
//! compiles to its OWN Custom verification key instead of a general zkVM (see
//! `docs/deos/MACRO-AS-CUSTOM-VK.md`): there is no `RunScript` effect — a script
//! is run via `Authorization::Custom { vk_hash = script_id }` over its pipeline,
//! the script's holes being the public inputs. Tier-1 gives the carrier + the
//! content-address; Tier-2 swaps the content hash for the compiled circuit VK.
//!
//! The macro/factory unification: a factory is the one-creation degenerate
//! script; a script is the factory generalized to a sequence. Both are "a
//! recorded intention, content-addressed, replayed verifiably."

use serde::{Deserialize, Serialize};

use crate::eventual::{Pipeline, PipelineError};
use crate::executor::{execute_pipeline, TurnExecutor};
use crate::turn::{Turn, TurnReceipt};
use dregg_cell::Ledger;

/// A recorded, replayable turn-sequence — the Tier-1 macro.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Script {
    /// An operator-legible name (not part of the content-address).
    pub name: String,
    /// The recorded turn-sequence + its dependency DAG (the proven carrier).
    pub pipeline: Pipeline,
}

impl Script {
    /// Record a LINEAR script from a sequence of turns (each depends on the
    /// previous — the order they were performed). Replaying re-applies them in
    /// that order through the real executor. Non-atomic by default; see
    /// [`Script::atomic`].
    pub fn record(name: impl Into<String>, turns: Vec<Turn>) -> Self {
        let mut pipeline = Pipeline::new();
        let mut prev: Option<usize> = None;
        for t in turns {
            let idx = pipeline.add_turn(t);
            if let Some(p) = prev {
                // (dependent, dependency) — this turn replays after the previous.
                pipeline.dependencies.push((idx, p));
            }
            prev = Some(idx);
        }
        Script { name: name.into(), pipeline }
    }

    /// Wrap an already-built [`Pipeline`] (e.g. one carrying holes / a non-linear
    /// dependency DAG) as a named script.
    pub fn from_pipeline(name: impl Into<String>, pipeline: Pipeline) -> Self {
        Script { name: name.into(), pipeline }
    }

    /// Make the replay ATOMIC — any turn failing rolls back the whole replay.
    pub fn atomic(mut self) -> Self {
        self.pipeline.atomic = true;
        self
    }

    pub fn len(&self) -> usize {
        self.pipeline.turns.len()
    }
    pub fn is_empty(&self) -> bool {
        self.pipeline.turns.is_empty()
    }

    /// The content-address of this script — `blake3` over the canonical bytes of
    /// its pipeline. This is the script's IDENTITY: the Tier-1 analog of a
    /// factory's VK hash and the placeholder for the future compiled Custom-VK
    /// hash. Two scripts with the same turn-sequence + dependencies share an id;
    /// the name is deliberately excluded (it is metadata, not identity).
    pub fn id(&self) -> [u8; 32] {
        let bytes = postcard::to_allocvec(&self.pipeline).unwrap_or_default();
        let mut h = blake3::Hasher::new_derive_key("dregg-script-v1");
        h.update(&bytes);
        *h.finalize().as_bytes()
    }

    /// Validate the underlying pipeline (acyclic dependency DAG, bounds).
    pub fn validate(&self) -> Result<(), PipelineError> {
        self.pipeline.validate()
    }

    /// REPLAY the script through the real executor — the same verified
    /// [`execute_pipeline`] the protocol already trusts, in topological order.
    /// Returns one result per turn (a committed [`TurnReceipt`] or the
    /// executor's refusal), so a replay is itself a verifiable turn-sequence.
    pub fn replay(
        &self,
        ledger: &mut Ledger,
        executor: &TurnExecutor,
    ) -> Vec<Result<TurnReceipt, PipelineError>> {
        execute_pipeline(self.pipeline.clone(), ledger, executor)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::action::{Action, Authorization, CommitmentMode, DelegationMode, Effect};
    use crate::executor::ComputronCosts;
    use crate::forest::CallForest;
    use crate::Preconditions;
    use dregg_cell::permissions::{AuthRequired, Permissions};
    use dregg_cell::CellId;

    fn make_test_turn(agent: CellId, nonce: u64, effects: Vec<Effect>) -> Turn {
        let action = Action {
            target: agent,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects,
            may_delegate: DelegationMode::ParentsOwn,
            commitment_mode: CommitmentMode::Full,
            balance_change: None,
            witness_blobs: vec![],
        };
        let mut forest = CallForest::new();
        forest.add_root(action);
        Turn {
            agent,
            nonce,
            call_forest: forest,
            fee: 10000,
            memo: None,
            valid_until: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
            previous_receipt_hash: None,
        }
    }

    fn make_open_cell(pk: [u8; 32], balance: i64) -> dregg_cell::Cell {
        let mut cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], balance);
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
        cell
    }

    fn two_nonce_turns() -> (CellId, Vec<Turn>) {
        let cell = make_open_cell([7u8; 32], 1_000_000);
        let id = cell.id();
        (id, vec![make_test_turn(id, 0, vec![]), make_test_turn(id, 1, vec![])])
    }

    #[test]
    fn record_builds_a_linear_pipeline() {
        let (_id, turns) = two_nonce_turns();
        let s = Script::record("nonce-twice", turns);
        assert_eq!(s.len(), 2);
        // turn 1 depends on turn 0 — the linear recording order.
        assert_eq!(s.pipeline.dependencies, vec![(1, 0)]);
        assert!(s.validate().is_ok());
        assert_eq!(s.name, "nonce-twice");
    }

    #[test]
    fn id_is_stable_and_distinct() {
        let (_a, ta) = two_nonce_turns();
        let (_b, tb) = two_nonce_turns();
        let s1 = Script::record("x", ta);
        let s2 = Script::record("y", tb); // same turns, different NAME
        assert_eq!(s1.id(), s2.id(), "id is content (pipeline) not name");
        let s3 = Script::record("z", vec![]); // empty — different content
        assert_ne!(s1.id(), s3.id());
    }

    #[test]
    fn serde_roundtrips() {
        let (_id, turns) = two_nonce_turns();
        let s = Script::record("rt", turns);
        let bytes = postcard::to_allocvec(&s).unwrap();
        let back: Script = postcard::from_bytes(&bytes).unwrap();
        assert_eq!(back.id(), s.id());
        assert_eq!(back.name, "rt");
    }

    #[test]
    fn replay_commits_through_the_real_executor() {
        let cell = make_open_cell([7u8; 32], 1_000_000);
        let id = cell.id();
        let mut ledger = Ledger::new();
        ledger.insert_cell(cell).unwrap();

        let script = Script::record(
            "nonce-twice",
            vec![make_test_turn(id, 0, vec![]), make_test_turn(id, 1, vec![])],
        );
        let executor = TurnExecutor::new(ComputronCosts::zero());
        let results = script.replay(&mut ledger, &executor);

        assert_eq!(results.len(), 2);
        assert!(results[0].is_ok(), "turn 0 should commit: {:?}", results[0]);
        assert!(results[1].is_ok(), "turn 1 should commit: {:?}", results[1]);
        // the agent's nonce advanced twice — the script genuinely ran.
        assert_eq!(ledger.get(&id).unwrap().state.nonce(), 2);
    }
}
