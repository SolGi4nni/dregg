// =============================================================================
// Section 6: Ordering and finality
// =============================================================================

#import "../defs.typ": lean
= Ordering and finality <sec-ordering>

The conservation logic of @sec-authority asks whether a step is allowed; the
ordering logic asks *when a fact is final*. It is the modal half of the step
logic: a finality lattice over a Merkle-CRDT DAG, gated on one named liveness
carrier. Safety is unconditional modulo the cryptographic floor; only liveness
rests on the carrier.

== The lace

Participants do not share a single linear log. Each keeps a *strand* --- an
append-only, signed log only its owner can extend --- and the strands together
form a cross-feed causal DAG, the *blocklace* @blocklace. A block is signed,
content-addressed, and carries a monotone per-creator sequence; equivocation is
a structurally detectable incomparable pair, and an honest finalization is
unforkable (#lean("StrandIntegrity.forked_strand_not_forkFree"),
#lean("Consensus.honest_finalization_unforkable")). Two replicas that merge the
same causally-closed blocks reach the same lace and therefore the same executed
state (#lean("LaceMerge.merge_convergence_to_state")) --- eventual consistency
upgraded to verified convergence.

== Finality as a lattice

Finality is not a boolean but a lattice of tiers over the DAG. An effect commits
at the join of the written cells' tiers and never downgrades; "a fact becomes
common knowledge" is the modal ascent up that lattice. The finalization rule is
deterministic and yields a single anchor per wave
(#lean("BlocklaceFinality.finalLeaders_one_per_wave"),
#lean("BlocklaceFinality.tauOrder_deterministic")), so two honest verifiers that
see the same finalized blocks compute the same order. An equivocator is repelled
from approval (#lean("Consensus.equivocator_repelled_from_approval")), and a
reconfiguration cannot rewrite already-finalized state
(#lean("Consensus.no_conflicting_finalized_state_reconfig")).

== Safety below the threshold; liveness above synchrony

The resilience analysis separates the safety threshold $t_S$ from the liveness
threshold $t_L$, with $t_L < t_S$. Safety holds below $t_S$
(#lean("Consensus.safety_holds_below_tS")), and the bound is real rather than
decorative: a negative theorem exhibits a safety break above it
(#lean("Consensus.safety_can_break_above_tS")). Liveness is reduced to a single
named assumption rather than asserted: under partial synchrony with an honest
supermajority, post-GST progress holds
(#lean("Consensus.leaderless_progress") from
#lean("Consensus.PostGSTProgress")). This is the one liveness carrier on the
assurance floor (@sec-assurance); the proofs do not diffuse it through the
safety arguments.

== What runs

This fabric runs as a four-validator federation: distinct Ed25519+ML-DSA
validator keys under one committee genesis, blocklace synchronization over
QUIC, and finality gated on a committee quorum rather than on any single node
(`docs/LOCAL-FEDERATION.md`). A turn submitted to one node is super-ratified by
the committee; its receipt and its finalized height then replicate identically
on every node. Committee size is where the threshold separation above becomes a
deployment choice. At $n = 3$ the supermajority threshold is unanimity, so a
single asymmetrically delivered block keeps waves from closing and the
finalized height plateaus; at $n = 4$ each wave-closing round tolerates one
laggard, and a committee spanning two machines on a real network streams
finality, the height climbing identically on all four nodes
(`docs/STAGE5-N4-RESULT.md`). Safety holds at both sizes; the change is a
deployment parameter, not code. With the verified ordering gate as the finality
authority, committed state is machine-independent: a Linux release build and a
Darwin debug build of the Lean executor commit byte-identical roots for the
same turns. The residual cost of that gate is performance, not safety: the
verified order is recomputed over the whole lace on each poll, so under
cross-machine catch-up churn committed-turn throughput can fall below block
production and finality crawls; the DAGs remain identical and no state is
corrupted (`docs/CROSS-MACHINE-FINALITY-FINDING.md`).

== Revocation is consensus-bound

The ordering logic is where revocation earns its meaning. Bumping a revocation
epoch is a state change like any other; it *takes effect* exactly when the
relevant views agree the epoch advanced, which is a finality fact, not a local
one. Revocation therefore needs consensus
(#lean("Liveness.revocation_needs_consensus")), and its dual ---
whether a capability is dead from a given partial view --- is undecidable
(#lean("Liveness.dead_undecidable")), pinned alongside to state the limit. A partitioned network stalls a revocation's finality; it cannot forge
the revocation, and it cannot un-revoke. Safety survives partition; liveness is
exactly as strong as the carrier.

== Sovereignty across the fabric

A hosted cell's full state lives with its host federation; a *sovereign* cell
publishes only a commitment and proves its own transitions, so a far federation
admits its turns knowing only how to check a proof, never how to re-run the
cell. Two sovereign cells can exchange signed transitions directly and reconcile
on reconnect --- the same `Pred` and the same receipt algebra, off the
consensus path until one party publishes. The ordering logic bounds where
coordination is *required*; @sec-guards's coordination dial is what tells a guard
whether it needs the lattice at all.
