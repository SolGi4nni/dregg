// =============================================================================
// Section 4: The descriptor circuit and the light client
// =============================================================================

#import "../defs.typ": lean
= Proofs: the descriptor circuit and the light client <sec-proofs>

== The descriptor circuit

The proof system is organized so the circuit is *derived*, not hand-built. No
constraint is authored in Rust. Each kernel statement carries a *descriptor* ---
the structured form of its semantics --- from which the executor reading
(`interp`) and the circuit reading (`compile`) are both obtained, with agreement
theorems welding them: #lean("Argus.Receipt.argus_circuit_executor_receipts_agree")
is the receipt-level weld, and the per-effect statements live in
`Circuit/Argus/Effects/`. One term has two provably-agreeing readings: the turn
is a proof term, the circuit is the logic's proof checker, a receipt is a
judgment, and the chain is one growing proof object.

The proving stack is a STARK over Plonky3 (BabyBear field, FRI) @plonky3 @fri,
with the commitment scheme of @sec-q inside the arithmetization (Poseidon2)
@poseidon2 and recursion folding receipts into the aggregate the light client
checks. Rust interprets only the Lean-emitted, byte-pinned descriptor artifacts;
a coverage gap is closed by emitting from a proved Lean module, never by
authoring a constraint by hand. The circuit layer adds exactly one assumption to
the floor of the assurance case --- the named engine-soundness carrier
#lean("EngineSound.recursive_sound") --- and no other.

== Q <sec-q>

A committed turn leaves *Q* --- the receipt: the committed postcondition of the
step under one commitment scheme. State, capability lists, and aggregates alike
commit under a sorted-Poseidon2 Merkle structure. One object serves every role:
the witness proves Q, the disclosure dial projects Q, aggregation folds Q, the
light client verifies only Q-chains.

Two coupled chains record the epistemic history. The *receipt chain*, per cell
($"prev" arrow.r "hash"$), is the append-only log of what was inferred --- the
log is the truth, the database is a cache. The *witness bundle*, bound into each
receipt by its witness hash, is the content that makes the inference replayable.
Checkpoint, restore, replay, and time-travel are theorems, not features:
re-seed the execution from a recorded witness and the same receipts fall out.

== The receipt binds the whole post-state

The commitment is determined by --- and, under collision-resistance, recovers
--- every field of the post-state, including the frame the step did not touch.
Mechanized:

- #lean("Argus.Receipt.argus_commits_to_one_receipt") --- the circuit term
  commits to exactly one receipt, determined by the post-state;
- #lean("Argus.Receipt.argus_circuit_executor_receipts_agree") --- the circuit's
  receipt and the executor's receipt are the same judgment (one semantics, two
  readings);
- #lean("CommitmentCrossBind.runnable_binds_same_system_roots") --- equal
  commitment roots imply equal full state (cells _and_ rest-of-state);
- #lean("CommitmentCrossBind.chC_bad_not_bridge") --- the teeth: a commitment
  that drops a field is rejected as a bridge, so the binding is non-vacuous.

Freshness is part of the same object: a committed spend's nullifier was provably
fresh and a repeat fails closed _at the term level_
(#lean("noteSpendStmt_no_double_spend"), #lean("noteSpendStmt_replay_rejected")),
with non-membership itself a witnessed claim --- a sorted-tree non-membership
opening with a circuit gate (#lean("NonMembership.nonmembership_sound") /
#lean("NonMembership.nonmembership_complete")). Freshness is checked by an
opening, never by a Merkle-path scan of the whole nullifier set.

== Aggregation

Proofs fold. Each step's proof attests its own statement plus the proof before
it; the seam is pinned --- step $i$'s post-root must be step $i+1$'s pre-root
(#lean("HistoryAggregation.wellformed_attests_whole_history"),
#lean("HistoryAggregation.root_tooth_pins_state")). Aggregating witness hashes
into one root is incremental verifiable computation @nova: the DAG of all
knowledge compressed to a single checkable claim.

Proofs are *additive attestation, not permission*. Between parties that trust
each other's execution, turns flow as signed receipts and nobody waits on a
prover. The proof layer exists so that someone who was not there --- a new node,
an auditor, a phone --- can verify the whole past at the cost of one check.

== The light-client theorem

The keystone is #lean("RecursiveAggregation.light_client_verifies_whole_history").
A verifier that checks only `verify agg.root` --- re-witnessing nothing --- learns
that every turn in the history executed correctly, in order, and that the final
root is a genuine fold of that history. The composed guarantees of the assurance case
ride along: the whole attested history conserves
(#lean("RecursiveAggregation.attested_history_conserves")), and tampering is not
merely detectable but *unprovable* --- a reordered chain forces the binding
predicate false, so no verifying aggregate exists
(#lean("RecursiveAggregation.tampered_aggregate_cannot_bind");
#lean("RecursiveAggregation.leaf_pairing_defeats_swap") rules out re-pointing a
verifying leaf at a different step).

The realization on the executable term IR is the Argus strand
(#lean("Argus.Aggregate.argus_strand_light_client"),
#lean("Argus.Aggregate.tampered_argus_strand_rejected")), and the one recursion
obligation is the named engine-soundness carrier #lean("EngineSound.recursive_sound")
on the assumption floor of the assurance case. This is unfoolability made precise: a
light client cannot be convinced of a history the protocol did not actually
produce.
