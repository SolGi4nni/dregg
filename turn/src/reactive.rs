//! Reactive effects: the first-class vocabulary for an agent's STANDING
//! COMMITMENTS and async coordination — `Promise` / `Notify` / `React`.
//!
//! # Why this module exists (the weld)
//!
//! Two halves of "an agent reacting to another" already existed in the tree,
//! disconnected:
//!
//!  * **The sound kernel** — [`crate::pending::PendingTurnRegistry`] (a registry
//!    of promise-holes awaiting resolution, with cascading + broken-promise
//!    propagation) and [`crate::conditional::resolve_condition`] (the proof gate
//!    that carries a REAL nullifier set, `used_proof_hashes`, against replay).
//!    Proven in Lean: `Await.commit_resumes_once`, `holeFill_binds_in_circuit`,
//!    `condTurn_dependency_sound`.
//!
//!  * **The live UI** — the starbridge swarm's `NotifyEdge` (A woke B by a
//!    committed `EmitEvent` deposited in B's inbox; B drains it in its own
//!    receipted turn). Ad-hoc: the inbox is a `Vec<NotifyEdge>` with no kernel
//!    backing and no one-shot proof beyond a `drained: bool` flag.
//!
//! This module is the FIRST-CLASS EFFECT that welds them. The 1:1
//! correspondence (`docs/deos/REACTIVE-EFFECTS.md`):
//!
//! | UI (ad-hoc)            | kernel (sound)                                 |
//! |-----------------------|------------------------------------------------|
//! | the inbox             | a cell's view of the [`PendingTurnRegistry`]   |
//! | a `NotifyEdge`        | a [`PendingEntry`] (a promise/wake)            |
//! | "drain / react"       | `resolve` → fire the awaiting turn             |
//! | `drained: bool`       | the entry's REMOVAL + the proof nullifier      |
//!
//! # The soundness gift (the keystone)
//!
//! A promise-hole IS a nullifier. To **react** is to **spend** the hole. One-shot
//! linearity — react exactly once — is the SAME double-spend non-membership the
//! circuit already enforces on `noteSpend`. So "react twice" = "double spend" =
//! ALREADY rejected, by construction. We do not re-implement the gate; we ride it.
//!
//! The [`ReactiveCoordinator`] enforces the one-shot property at TWO independent
//! teeth, so neither alone is load-bearing:
//!
//!  1. **Registry removal** — `resolve()` REMOVES the entry. A second react finds
//!     no entry: [`ReactError::AlreadyReacted`]. (The promise-hole is consumed.)
//!  2. **The proof nullifier** — the resolution proof's hash is inserted into the
//!     shared `used_proof_hashes` on success; a replayed proof is refused by
//!     `resolve_condition` with "proof already used". (The spend is one-shot even
//!     if the same hole-id were somehow re-presented.)
//!
//! Lean obligation named (NOT yet discharged for this exact ADT): the circuit
//! witness for a `React` effect — that a light client verifying a batch bearing a
//! `React` sees the promise-hole nullifier grow exactly as a `noteSpend` does.
//! That is the next slice (`docs/deos/REACTIVE-EFFECTS.md` §6). The Rust gate here
//! is the executor-side enforcement; the in-circuit witness is the lift.

use std::collections::HashSet;

use serde::{Deserialize, Serialize};

use crate::conditional::{
    resolve_condition, ConditionProof, ConditionalResult, ProofCondition, TrustedRoot,
    DEFAULT_MAX_ROOT_AGE,
};
use crate::pending::{PendingTurnRegistry, ResolutionCondition, ResolutionEvent, ResolutionOutcome};
use crate::turn::{Turn, TurnReceipt};

// ─── The first-class reactive-effect ADT ─────────────────────────────────────

/// A first-class REACTIVE EFFECT — the capacity an agent needs to make standing
/// commitments, wake peers, and react to wakes. Three constructors, each a thin
/// face onto the proven kernel:
///
///  * [`ReactiveEffect::Promise`] — "I commit to run `turn` once `condition`
///    holds": a promise-hole. Maps to `PendingTurnRegistry::submit_pending`.
///  * [`ReactiveEffect::Notify`] — "I wake `to` with a hole it may later react
///    to": deposits a [`PendingEntry`] in the recipient's registry. The
///    kernel-backed twin of the UI's `NotifyEdge`.
///  * [`ReactiveEffect::React`] — "I discharge the hole `pending_id` by presenting
///    `resolution_proof`": the one-shot spend. Maps to `resolve` + the nullifier.
///
/// [`PendingEntry`]: crate::pending::PendingEntry
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum ReactiveEffect {
    /// A standing commitment: run `turn` once `condition` is satisfied. The
    /// promise-hole. (`cell` is the cell whose registry holds it.)
    Promise {
        /// The cell whose pending registry holds this commitment.
        cell: [u8; 32],
        /// The condition under which the held turn fires.
        resolution_condition: ResolutionCondition,
    },
    /// A wake from `from` to `to`: deposit a promise-hole (a [`PendingEntry`]) in
    /// `to`'s registry that `to` may later react to. The kernel-backed `NotifyEdge`.
    Notify {
        /// The waking cell (the sender / provenance).
        from: [u8; 32],
        /// The woken cell (the recipient; holds the hole in its registry).
        to: [u8; 32],
        /// The turn the recipient commits to run when it reacts.
        wake: Box<Turn>,
        /// The condition the recipient must discharge to react.
        resolution_condition: ResolutionCondition,
    },
    /// React to a deposited hole: discharge `pending_id` by presenting the proof
    /// of its [`ProofCondition`]. The one-shot spend — the second react on the
    /// same `pending_id` is REFUSED.
    React {
        /// The hole being discharged (the [`PendingEntry`]'s turn hash).
        pending_id: [u8; 32],
        /// The condition the proof must satisfy (the hole's
        /// [`ProofCondition`] — the spend is gated on it).
        condition: ProofCondition,
        /// The proof discharging the condition (the witness for the spend).
        resolution_proof: ConditionProof,
    },
}

// ─── Errors ──────────────────────────────────────────────────────────────────

/// Why a reactive operation was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReactError {
    /// The `pending_id` named no hole in the registry. Either it was never
    /// notified, or — the one-shot tooth — it was ALREADY reacted to (the entry
    /// was removed on the first react). This is the promise-hole-as-nullifier
    /// double-spend refusal.
    AlreadyReacted {
        /// The hole that was named but is absent.
        pending_id: [u8; 32],
    },
    /// The hole exists but the presented proof did not discharge its condition
    /// (a genuine resolution failure — wrong proof, replayed proof, expired, …).
    /// Carries the kernel's typed reason.
    ProofRejected {
        /// The hole that remains unresolved.
        pending_id: [u8; 32],
        /// The `resolve_condition` verdict's reason string.
        reason: String,
    },
}

impl std::fmt::Display for ReactError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReactError::AlreadyReacted { pending_id } => write!(
                f,
                "REFUSED — no live hole {:02x}{:02x}…: never notified or already reacted (one-shot)",
                pending_id[0], pending_id[1]
            ),
            ReactError::ProofRejected { pending_id, reason } => write!(
                f,
                "REFUSED — hole {:02x}{:02x}… proof rejected: {reason}",
                pending_id[0], pending_id[1]
            ),
        }
    }
}

/// The outcome of a successful react: the hole was discharged once.
#[derive(Clone, Debug)]
pub struct ReactOutcome {
    /// The hole that was discharged (now consumed from the registry).
    pub pending_id: [u8; 32],
    /// The resolution events the registry emitted (the resolved turn + any
    /// cascading `ReadyToExecute` for dependents).
    pub events: Vec<ResolutionEvent>,
}

// ─── The coordinator (the weld) ──────────────────────────────────────────────

/// THE REACTIVE COORDINATOR — one cell's reactive face. Welds:
///
///  * a [`PendingTurnRegistry`] — the cell's promise-holes (its inbox, as
///    kernel-backed pending entries), and
///  * a shared `used_proof_hashes` nullifier set — the one-shot gate
///    [`resolve_condition`] writes to, the SAME structure the conditional-turn
///    machinery uses against replay.
///
/// `notify` deposits a hole; `react` spends it — exactly once. The one-shot
/// property is enforced by TWO teeth (registry removal AND the proof nullifier),
/// so this is not a single point that can silently regress.
#[derive(Clone, Debug, Default)]
pub struct ReactiveCoordinator {
    /// The promise-holes this cell holds (its kernel-backed inbox).
    registry: PendingTurnRegistry,
    /// The shared resolution-proof nullifier — the one-shot spend ledger. A
    /// proof hash present here has already discharged a hole; `resolve_condition`
    /// refuses its reuse. The promise-hole-as-nullifier set.
    used_proof_hashes: HashSet<[u8; 32]>,
    /// Trusted federation roots for `RemoteProof` resolution (empty = local-only).
    trusted_roots: Vec<TrustedRoot>,
    /// Trusted executor keys for `TurnExecuted`-receipt resolution.
    trusted_executor_keys: Vec<[u8; 32]>,
}

impl ReactiveCoordinator {
    /// A fresh coordinator with no holes and an empty nullifier set.
    pub fn new() -> Self {
        Self::default()
    }

    /// Install the trust anchors used when reacting against remote proofs /
    /// receipt conditions.
    pub fn with_trust(
        mut self,
        trusted_roots: Vec<TrustedRoot>,
        trusted_executor_keys: Vec<[u8; 32]>,
    ) -> Self {
        self.trusted_roots = trusted_roots;
        self.trusted_executor_keys = trusted_executor_keys;
        self
    }

    /// **NOTIFY** — deposit a promise-hole in this cell's registry. The
    /// kernel-backed `NotifyEdge`: a [`PendingEntry`] holding the `wake` turn the
    /// cell commits to run when it reacts, gated on `condition`. Returns the
    /// hole's id (the `wake` turn hash), the key a later [`Self::react`] names.
    ///
    /// [`PendingEntry`]: crate::pending::PendingEntry
    pub fn notify(
        &mut self,
        wake: Turn,
        condition: ResolutionCondition,
        timeout_height: u64,
        submitted_at: u64,
    ) -> [u8; 32] {
        self.registry
            .submit_pending_at(wake, condition, timeout_height, submitted_at)
    }

    /// **REACT** — discharge the hole `pending_id` by presenting a proof of
    /// `condition`. The ONE-SHOT SPEND.
    ///
    /// Two independent teeth enforce one-shotness:
    ///
    ///  1. If `pending_id` names no live hole (never notified, or already
    ///     reacted — `resolve` removed it on the first react), refuse with
    ///     [`ReactError::AlreadyReacted`]. THE promise-hole-as-nullifier refusal.
    ///  2. Else run [`resolve_condition`] against the SHARED nullifier. On success
    ///     the proof hash is recorded, so even a re-presented proof is refused
    ///     ("proof already used"). On failure the hole STAYS (a failed react does
    ///     not consume it) and we return [`ReactError::ProofRejected`].
    ///
    /// On success the hole is consumed (removed) and the registry's resolution
    /// events are returned.
    pub fn react(
        &mut self,
        pending_id: [u8; 32],
        condition: &ProofCondition,
        resolution_proof: &ConditionProof,
        current_height: u64,
    ) -> Result<ReactOutcome, ReactError> {
        // TOOTH 1 — the hole must be live. A consumed (already-reacted) or
        // never-notified hole is absent: the one-shot refusal.
        let Some(entry) = self.registry.get_pending(&pending_id).cloned() else {
            return Err(ReactError::AlreadyReacted { pending_id });
        };

        // TOOTH 2 — the proof must discharge the condition, gated on the shared
        // nullifier. `resolve_condition` refuses a replayed proof ("already
        // used") and only records the proof hash on success.
        let verdict = resolve_condition(
            condition,
            resolution_proof,
            current_height,
            entry.timeout_height,
            &self.trusted_roots,
            DEFAULT_MAX_ROOT_AGE,
            &mut self.used_proof_hashes,
            &self.trusted_executor_keys,
        );

        match verdict {
            ConditionalResult::Resolved => {
                // The spend lands: consume the hole (removes the entry) and
                // surface the resolution events. From here, a second react on the
                // same id hits TOOTH 1 (the entry is gone).
                let receipt = synthetic_resolution_receipt(&entry.turn);
                let events = self
                    .registry
                    .resolve(pending_id, ResolutionOutcome::Resolved(receipt));
                Ok(ReactOutcome { pending_id, events })
            }
            ConditionalResult::Pending => Err(ReactError::ProofRejected {
                pending_id,
                reason: "condition not yet satisfied".to_string(),
            }),
            ConditionalResult::Expired => Err(ReactError::ProofRejected {
                pending_id,
                reason: "hole expired (past its timeout height)".to_string(),
            }),
            ConditionalResult::InvalidProof(reason) => {
                Err(ReactError::ProofRejected { pending_id, reason })
            }
        }
    }

    /// How many live (un-reacted) holes this cell holds.
    pub fn pending_count(&self) -> usize {
        self.registry.len()
    }

    /// Whether `pending_id` names a live (un-reacted) hole.
    pub fn is_live(&self, pending_id: &[u8; 32]) -> bool {
        self.registry.get_pending(pending_id).is_some()
    }

    /// Whether a resolution proof has already been spent (is in the nullifier
    /// set) — the double-spend ledger, exposed for inspection / the panel.
    pub fn proof_spent(&self, proof: &ConditionProof) -> bool {
        let h = crate::conditional::compute_proof_hash(proof);
        self.used_proof_hashes.contains(&h)
    }

    /// Borrow the underlying registry (read-only) — the inbox view.
    pub fn registry(&self) -> &PendingTurnRegistry {
        &self.registry
    }
}

/// A resolution receipt for the discharged hole's turn. The hole's `wake` turn is
/// *committed to* by the notify; on react it is *resolved*, and the registry wants
/// a receipt to cascade to dependents. The real node would run the turn through
/// the executor and pass the genuine receipt to `registry.resolve`; this slice
/// records the resolution with a content-addressed receipt over the turn hash so
/// the cascade has a stable, non-fabricated provenance link. (Replacing this with
/// the real executor receipt is the effect-vocabulary lift — see the module doc.)
fn synthetic_resolution_receipt(turn: &Turn) -> TurnReceipt {
    let turn_hash = turn.hash();
    TurnReceipt {
        turn_hash,
        forest_hash: turn.call_forest.compute_hash(),
        pre_state_hash: [0u8; 32],
        post_state_hash: turn_hash, // content-addressed to the resolved hole
        timestamp: 0i64,
        effects_hash: [0u8; 32],
        computrons_used: 0,
        action_count: turn.call_forest.roots.len(),
        previous_receipt_hash: None,
        agent: turn.agent,
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

// ─── Tests — the forge-detector ──────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::action::{Action, Authorization, CommitmentMode, DelegationMode};
    use crate::forest::CallForest;
    use dregg_cell::{CellId, Preconditions};

    /// A minimal `wake` turn for a member cell (the turn the recipient commits to
    /// run when it reacts).
    fn wake_turn(cell_byte: u8, nonce: u64) -> Turn {
        let agent = CellId::from_bytes([cell_byte; 32]);
        let action = Action {
            target: agent,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![],
            may_delegate: DelegationMode::None,
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
            fee: 1000,
            memo: None,
            valid_until: None,
            depends_on: vec![],
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            previous_receipt_hash: None,
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        }
    }

    /// A hash-preimage condition + its discharging proof — the simplest genuine
    /// wake/react pair (B reacts by revealing the preimage A's notify committed to).
    fn preimage_wake() -> (ProofCondition, ConditionProof) {
        let preimage = [0x5Au8; 32];
        let hash = *blake3::hash(&preimage).as_bytes();
        (
            ProofCondition::HashPreimage { hash },
            ConditionProof::Preimage(preimage),
        )
    }

    // ── THE POSITIVE: a genuine notify → react resolves once and is recorded ──

    #[test]
    fn notify_then_react_resolves_once() {
        let mut coord = ReactiveCoordinator::new();
        let (condition, proof) = preimage_wake();

        // A notifies B: deposit a promise-hole holding B's wake turn.
        let wake = wake_turn(0xB0, 0);
        let pending_id = coord.notify(
            wake,
            // The registry's resolution-condition mirrors the proof gate; the
            // ProofCondition is what the react actually discharges.
            ResolutionCondition::AwaitCondition(condition.clone()),
            /* timeout_height */ 100,
            /* submitted_at  */ 10,
        );

        assert_eq!(coord.pending_count(), 1, "one live hole after notify");
        assert!(coord.is_live(&pending_id), "the hole is live");
        assert!(!coord.proof_spent(&proof), "proof not yet spent");

        // B reacts: discharge the hole with the genuine preimage proof.
        let outcome = coord
            .react(pending_id, &condition, &proof, /* height */ 50)
            .expect("a genuine react must resolve");

        assert_eq!(outcome.pending_id, pending_id);
        assert!(
            matches!(
                outcome.events.first(),
                Some(ResolutionEvent::Resolved { turn_hash, .. }) if *turn_hash == pending_id
            ),
            "the resolution is RECORDED as a Resolved event for the hole, got {:?}",
            outcome.events
        );

        // The hole is consumed and the proof is now spent (the nullifier grew).
        assert_eq!(coord.pending_count(), 0, "the hole is consumed");
        assert!(!coord.is_live(&pending_id), "the hole is no longer live");
        assert!(coord.proof_spent(&proof), "the proof is now in the nullifier");
    }

    // ── THE FORGE-DETECTOR: a SECOND react on the same hole is REJECTED ──────

    #[test]
    fn react_twice_rejected() {
        let mut coord = ReactiveCoordinator::new();
        let (condition, proof) = preimage_wake();

        let wake = wake_turn(0xB0, 0);
        let pending_id = coord.notify(
            wake,
            ResolutionCondition::AwaitCondition(condition.clone()),
            100,
            10,
        );

        // First react: succeeds (the genuine spend).
        let first = coord.react(pending_id, &condition, &proof, 50);
        assert!(first.is_ok(), "the first react resolves: {first:?}");

        // SECOND react on the SAME hole: REFUSED. The hole was consumed (removed
        // from the registry) on the first react — TOOTH 1, the
        // promise-hole-as-nullifier one-shot refusal. This is genuine: the entry
        // is gone, not an unconditional Err.
        let second = coord.react(pending_id, &condition, &proof, 50);
        assert_eq!(
            second.unwrap_err(),
            ReactError::AlreadyReacted { pending_id },
            "react-twice on the same hole MUST be rejected (one-shot linearity)"
        );

        // And the registry confirms: no live hole, exactly the one spend recorded.
        assert_eq!(coord.pending_count(), 0);
        assert!(!coord.is_live(&pending_id));
    }

    // ── The second tooth is ALSO genuine: a replayed PROOF (even on a fresh
    //    hole with the same condition) is refused by the shared nullifier. This
    //    proves the one-shot is enforced at the proof layer too, not only by the
    //    registry-removal tooth. ──

    #[test]
    fn replayed_proof_refused_by_nullifier_on_a_fresh_hole() {
        let mut coord = ReactiveCoordinator::new();
        let (condition, proof) = preimage_wake();

        // Hole 1 (B0) — react successfully, spending the proof.
        let id1 = coord.notify(
            wake_turn(0xB0, 0),
            ResolutionCondition::AwaitCondition(condition.clone()),
            100,
            10,
        );
        assert!(coord.react(id1, &condition, &proof, 50).is_ok());

        // Hole 2 (B1) — a DIFFERENT hole with the SAME condition. Replaying the
        // already-spent proof must be refused by the nullifier ("already used"),
        // even though the hole is live. The spend is one-shot at the proof layer.
        let id2 = coord.notify(
            wake_turn(0xB1, 0),
            ResolutionCondition::AwaitCondition(condition.clone()),
            100,
            10,
        );
        assert!(coord.is_live(&id2), "the second hole is genuinely live");
        let replay = coord.react(id2, &condition, &proof, 50);
        assert!(
            matches!(
                &replay,
                Err(ReactError::ProofRejected { reason, .. }) if reason.contains("already used")
            ),
            "a replayed proof must be refused by the shared nullifier, got {replay:?}"
        );
        // The replay did NOT consume hole 2 (a failed react leaves the hole live).
        assert!(coord.is_live(&id2), "a refused react does not consume the hole");
    }

    // ── A WRONG proof is rejected and does NOT consume the hole (fail-closed,
    //    the hole survives a bad react attempt). ──

    #[test]
    fn wrong_proof_rejected_hole_survives() {
        let mut coord = ReactiveCoordinator::new();
        let (condition, _good) = preimage_wake();
        let wrong = ConditionProof::Preimage([0xFFu8; 32]); // not the preimage

        let id = coord.notify(
            wake_turn(0xB0, 0),
            ResolutionCondition::AwaitCondition(condition.clone()),
            100,
            10,
        );

        let bad = coord.react(id, &condition, &wrong, 50);
        assert!(
            matches!(bad, Err(ReactError::ProofRejected { .. })),
            "a wrong proof is refused, got {bad:?}"
        );
        // Fail-closed: the hole is still live (an invalid react spends nothing).
        assert!(coord.is_live(&id), "the hole survives a refused react");
        assert_eq!(coord.pending_count(), 1);

        // And the GENUINE proof can still discharge it afterwards (the bad attempt
        // did not poison the nullifier — only successful spends are recorded).
        let (_c, good) = preimage_wake();
        assert!(coord.react(id, &condition, &good, 50).is_ok());
        assert_eq!(coord.pending_count(), 0);
    }

    // ── An expired hole refuses (the temporal tooth — past the timeout height). ──

    #[test]
    fn expired_hole_refuses() {
        let mut coord = ReactiveCoordinator::new();
        let (condition, proof) = preimage_wake();
        let id = coord.notify(
            wake_turn(0xB0, 0),
            ResolutionCondition::AwaitCondition(condition.clone()),
            /* timeout_height */ 100,
            10,
        );
        // React at height 101 (past the timeout): refused as expired.
        let r = coord.react(id, &condition, &proof, 101);
        assert!(
            matches!(&r, Err(ReactError::ProofRejected { reason, .. }) if reason.contains("expired")),
            "a react past the hole's timeout is refused, got {r:?}"
        );
        assert!(coord.is_live(&id), "an expired-refused hole stays (until timeout-swept)");
    }

    // ── Reacting to a NEVER-NOTIFIED id refuses (no hole to spend). ──

    #[test]
    fn react_to_unknown_hole_refused() {
        let mut coord = ReactiveCoordinator::new();
        let (condition, proof) = preimage_wake();
        let bogus = [0xDEu8; 32];
        let r = coord.react(bogus, &condition, &proof, 50);
        assert_eq!(
            r.unwrap_err(),
            ReactError::AlreadyReacted { pending_id: bogus },
            "reacting to a non-existent hole is refused"
        );
    }
}
