// =============================================================================
// Section 15: Limitations
// =============================================================================

#import "../defs.typ": lean
= Limitations <sec-limitations>

Present-tense facts about the system as it stands. Each is a property a reader
can check, not a roadmap.

*The host-context seam.* The verified Lean producer is the default state
producer on the commit path, and its coverage is per effect kind. A turn that
touches any effect kind outside the covered set is produced by the host Rust
executor for that turn. For a further named set of effects the verified
producer installs its post-state while its reconstituted root diverges from the
Rust executor's reconstruction; the divergence is logged. The node reports the
exact split --- covered, uncovered, root-agreeing, and root-gap effect kinds ---
at `GET /api/node/producer` (`node/src/api.rs`). For turns the host arm
produces, the host implementation is in the trust base, and the running-entry
guarantee is stated over the verified entry, not over the host arms.

*The proof-system soundness carrier is quantified, and the deployed apex
evaluates near 58 bits.* The circuit layer's one recursion assumption is
#lean("RecursiveAggregation.EngineSound.recursive_sound"). Beneath it, the
mechanized reduction takes #lean("FriLdtExtractV3") --- everything FRI delivers
on an accepting run --- as a hypothesis, and the Lean development contains no
adversary or grinding model, so the figures that follow are evaluations of a
published bound at the deployed parameters, not an extraction theorem. At the
recursion apex, the artifact a light client verifies (log-blowup 6, 19 queries,
16 grinding bits, tables floored at $2^16$ rows, hence a $2^22$ evaluation
domain), the batched-FRI bound of Ben-Sasson, Carmon, Ishai, Kopparty, and
Saraf (2020), composed by the ethSTARK minimum rule, evaluates to 57.98 bits;
the 2025 successor bound by the same authors evaluates to about 70.9 at the
same apex, but its composition into a FRI soundness statement is unpublished.
The derivations and the pinned-source audit live in
`docs/reference/FRI-BOTH-WIN-LEVERS.md`. The shipped parameter ledger
(`FriKnobs`) carries no trace-height field, so it cannot express the
commit-phase term $epsilon_C$ that binds at the apex, where added queries and
added grinding buy zero bits; that the query ledger does not determine the
per-fold column is itself a theorem
(#lean("FriLedgerSound.query_ledger_does_not_determine_perFold")). At extension
degree eight the mechanized ledger exceeds 120 bits on every shipped
configuration (122.60 at log-blowup 6, 36 queries, 16 grinding bits;
`docs/reference/PROVEN-120-CONFIG.md`). That configuration is not deployed; cutting over
requires rewriting the degree-4 BN254 wrap and re-keying every verification
key.

*The post-quantum floor carries one FIPS hypothesis.* The quantum-aware chain
--- a one-way-to-hiding adversary, through the lattice primitive games, to the
hybrid keystone --- is Lean-checked. The deployed ML-DSA scheme's correctness
is conditioned on exactly one labeled hypothesis,
#lean("DreggPqRefinement.Fips204Correct"): that the `fips204` crate implements
the sign-then-verify round trip. #lean("DreggPqRefinement.dregg_pq_correct")
derives correctness from that hypothesis and nothing else. A verified FIPS 204
implementation would discharge it; none is linked here.

*Composition security is not machine-checked end-to-end in one system.* The
per-guarantee theorems are kernel-pinned, and the cross-corner welds (executor
$arrow.l.r$ circuit) are theorems. The core commitment-realization obligation
is discharged in Isabelle/HOL --- CryptHOL with the `Sigma_Commit_Crypto`
Pedersen development (`Crypto/UCBridge.lean`, `uc-crypthol/Dregg2_FCom.thy`)
--- which widens the trust base to a second proof kernel and to a human-checked
correspondence between the two systems' definitions. A
universal-composability statement for the protocol stack as a whole is not a
Lean artifact.

*The global-zero value law does not yet cover the deployed genesis or legacy
fees.* The kernel's conservation guarantee is global: on every state reachable
from a value-empty genesis, every asset's system-wide total --- issuer wells
included --- is identically zero
(#lean("AssuranceCase.conservation_guarantee"),
#lean("Exec.ReachableConservation.reachable_total_zero")), and no verb moves
any asset's sum (#lean("TurnExecutorFull.ledgerDeltaAsset_eq_zero")). Two
deployed paths sit outside the theorem's hypothesis and are not claimed by it:
the devnet genesis seeds positive balances with no issuer well carrying
negative supply (`node/src/genesis.rs`), and the legacy atomic-path fee
epilogue debits a fee with no crediting move (`turn/src/executor/atomic.rs`).
Until both are reshaped, the deployed chain's totals are offset by the genesis
seed and decremented by legacy fees.

*Guard expressibility has stated edges.* The installable first-party atoms
(#lean("Exec.StateConstraint"), closed under the executor's Boolean algebra)
are predicates over one proposed transition: the old and the new state. Causal
and temporal rules --- predicates over the receipt trace rather than one step
--- are not installable atoms; a trace-shaped statement enters the grammar only
through the witnessed branch, which defers it to the verify seam
(#lean("Spec.Guard.admits")).

*Liveness is exactly as strong as its carrier.* Safety guarantees are
unconditional modulo the cryptographic floor. Finality and
revocation-at-finality additionally rest on #lean("PostGSTProgress"), eventual
synchrony. A partitioned network stalls finality; it cannot forge it.

*The embedded database executor runs the verified step on a reconstructed
turn.* In pg-dregg the in-backend producer runs the verified executor and takes
its verdict and post-state as authoritative, but the extension does not link
the turn codec, so it cannot decode a submitter's signed-turn envelope; it
synthesizes a conserving wire turn instead, and the residual is stated at the
seam (`pg-dregg/src/lean_producer.rs`). The range-attestation surface decodes
the whole-chain proof transport in every build; the circuit verifier itself
links only under the off-by-default `tier-c` feature, and the default build
refuses rather than attesting (`pg-dregg/src/attest.rs`).
