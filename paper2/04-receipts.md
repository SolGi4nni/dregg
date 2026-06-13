# 4 · Receipts, Q, and the light-client theorem

## 4.1 Q

A committed turn leaves **Q** — the receipt: the committed postcondition of
the step under one commitment scheme (sorted-Poseidon2 Merkle, for state,
capability lists, and aggregates alike). One object, every role: the witness
proves Q, the disclosure dial projects Q, aggregation folds Q, the light
client verifies only Q-chains.

Two coupled chains record the epistemic history:

* the **receipt chain** (per cell, `prev → hash`) — the append-only log of
  what was inferred; *the log is the truth, the database is a cache*;
* the **witness bundle**, bound into each receipt by its witness hash — the
  content that makes the inference replayable. Checkpoint, restore, replay,
  and time-travel are theorems, not features: re-seed the execution from a
  recorded witness and the same receipts fall out.

## 4.2 The receipt binds the whole post-state

The commitment is determined by — and, under collision-resistance, recovers —
every field of the post-state, including the frame the step did not touch.
Mechanized:

* `Argus.Receipt.argus_commits_to_one_receipt` — the circuit term commits to
  exactly one receipt, determined by the post-state;
* `Argus.Receipt.argus_circuit_executor_receipts_agree` — the circuit's
  receipt and the executor's receipt are the same judgment (one semantics,
  two readings);
* `CommitmentCrossBind.runnable_binds_same_system_roots` — equal commitment
  roots imply equal full state (cells *and* rest-of-state);
* `CommitmentCrossBind.chC_bad_not_bridge` — the teeth: a commitment that
  drops a field is rejected as a bridge, so the binding is non-vacuous.

Freshness is part of the same object: a committed spend's nullifier was
provably fresh and a repeat fails closed *at the term level*
(`noteSpendStmt_no_double_spend`, `noteSpendStmt_then_reject`,
`noteSpendStmt_replay_rejected`), with non-membership itself a witnessed
claim — a sorted-tree non-membership opening with a circuit gate
(`NonMembership.nonmembership_sound` / `_complete`).

## 4.3 Aggregation

Proofs fold. Each step's proof attests its own statement plus the proof
before it; the seam is pinned — step *i*'s post-root must be step *i+1*'s
pre-root (`HistoryAggregation.wellformed_attests_whole_history`,
`root_tooth_pins_state`). Aggregating witness hashes into one root is
incremental verifiable computation: the DAG of all knowledge compressed to a
single checkable claim.

Proofs are **additive attestation, not permission**: between parties that
trust each other's execution, turns flow as signed receipts and nobody waits
on a prover. The proof layer exists so that someone who was not there — a new
node, an auditor, a phone — can verify the whole past at the cost of one
check.

## 4.4 The light-client theorem

**`RecursiveAggregation.light_client_verifies_whole_history`.** A verifier
that checks only `verify agg.root` — re-witnessing nothing — learns that
every turn in the history executed correctly, in order, and that the final
root is a genuine fold of that history. The composed guarantees of §5 ride
along: the whole attested history conserves
(`attested_history_conserves`), and tampering is not merely detectable but
unprovable — a reordered chain forces the binding predicate false, so no
verifying aggregate exists (`tampered_aggregate_cannot_bind`;
`leaf_pairing_defeats_swap` rules out re-pointing a verifying leaf at a
different step).

The realization on the executable term IR is the Argus strand
(`Argus.Aggregate.argus_strand_light_client`,
`tampered_argus_strand_rejected`), and the one recursion obligation is the
named engine-soundness carrier (`EngineSound.recursive_sound`) on the
assumption floor (§5.2).
