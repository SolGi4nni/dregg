// =============================================================================
// Section 13: The assurance case
// =============================================================================

#import "../defs.typ": lean
= The assurance case <sec-assurance>

The system's guarantees are an artifact, not a narrative. `Dregg2/
AssuranceCase.lean` states them *by guarantee*, assembles under each the keystone
DAG that discharges it, and `#assert_axioms`-pins every name: the Lean build
fails unless each theorem's full axiom set is exactly the kernel triple
${"propext", "Classical.choice", "Quot.sound"}$ --- in particular, no `sorryAx`.
`Dregg2/Claims.lean` is the corpus-wide per-keystone pin net behind it. The
machine-readable form is the generated assurance catalog
(`studio/assurance-catalog.generated.json`); the paper states the guarantees and
defers the roster of record to it. Where a guarantee's substantive apex carries
long module-local frame hypotheses, the file uses a heading anchor and pins the
load-bearing keystone beneath it; the citations below name the keystone that
carries the content, not the anchor.

== The five guarantees and the running entry

*A --- Authority.* _Every state change is justified by an unforgeable,
non-amplified, fresh token chain._ The apex
#lean("AssuranceCase.authority_guarantee"): an introduction's conferred
capability is a genuine non-amplifying subset of the held one
(#lean("EffectsAuthority.introduce_non_amplifying")) *and* the predicate
discriminates --- an amplifying grant is rejected
(#lean("EffectsAuthority.amplifying_grant_rejected")). Keystones include the
per-mode admission soundness (#lean("AuthModes.captp_sound"),
#lean("AuthModes.bearer_sound"), #lean("AuthModes.token_sound")) and the
dispatcher gate #lean("AuthModes.captp_granted_le_held"). Floor: ed25519, HMAC,
Poseidon2-CR.

*B --- Conservation.* _Per asset, the resource sum is exactly zero across a turn
and a run._ The apex #lean("AssuranceCase.conservation_guarantee") over the
genuine multi-asset ledger: the moved asset's total is invariant
(#lean("RecordKernel.recTransferBal_sum_conserve_moved")) and every other asset
is pointwise untouched (#lean("RecordKernel.recTransferBal_untouched")), lifted
to the executor (#lean("RecordKernel.recKExec_conserves")) and to the abstract
monoid (#lean("Spec.conservation_over_monoid")), with
#lean("Spec.committed_iff_cleartext") proving the committed and cleartext
judgments agree. Floor: integer arithmetic only (Pedersen/DLog only when values
are committed).

*C --- Integrity.* _A receipt binds the whole post-state; a tampered input is
rejected._ The load-bearing apex is the cross-bind
#lean("CommitmentCrossBind.runnable_binds_same_system_roots"), with the
discriminating direction #lean("CommitmentCrossBind.chC_bad_not_bridge") (a
field-dropping commitment is not a faithful bridge) and the one-receipt welds
(#lean("Argus.Receipt.argus_commits_to_one_receipt"),
#lean("Argus.Receipt.argus_circuit_executor_receipts_agree")). Floor:
Poseidon2-permutation-CR --- a second preimage is exactly the only way to forge a
receipt for a different state.

*D --- Freshness.* _No replay or double-spend; revocation takes effect at
finality._ The apex #lean("AssuranceCase.freshness_guarantee"): a committed
spend's nullifier was fresh, is now present, and a repeat fails closed
(#lean("noteSpendStmt_no_double_spend"), #lean("noteSpendStmt_replay_rejected")),
with non-membership a witnessed opening
(#lean("NonMembership.nonmembership_sound") and
#lean("NonMembership.nonmembership_complete")), never a scan. Revocation is
consensus-bound (#lean("Liveness.revocation_needs_consensus")), with its
undecidable dual pinned alongside (#lean("Liveness.dead_undecidable")). Floor:
Poseidon2-CR; PostGSTProgress for the at-finality leg.

*E --- Unfoolability.* _A light client verifying a Q-chain learns A--D for the
whole history while re-witnessing nothing._ The apex
#lean("AssuranceCase.unfoolability_guarantee") conjoins whole-history
attestation (#lean("RecursiveAggregation.light_client_verifies_whole_history"),
@sec-proofs) with whole-history conservation derived from the verification bit
alone (#lean("RecursiveAggregation.conserves_from_verification")), with the
tamper-rejection direction pinned beside it
(#lean("RecursiveAggregation.tampered_aggregate_cannot_bind"),
#lean("RecursiveAggregation.leaf_pairing_defeats_swap")) and the strand
realization (#lean("Argus.Aggregate.argus_strand_light_client")). The whole
attested history conserves along the fold
(#lean("RecursiveAggregation.attested_history_conserves")).

The guarantee also holds in game form.
#lean("LightClientUC.unfoolable_of_floor") reduces light-client soundness to
exactly two floor carriers: STARK/Fiat-Shamir extractability (an accepting
proof yields a satisfying execution witness) and commitment binding (a
satisfying witness certifies the executor produced the state, itself sponge-CR).
Under those two, no environment can make the client accept a state the executor
did not produce. The contrapositive #lean("LightClientUC.fooling_breaks_floor")
extracts a concrete carrier break from any fooling attack: an environment that
fools the client exhibits an accepting proof with no satisfying witness --- a
win against the extraction game itself. A working attack on the light client is
therefore a working attack on a named floor row; there is no third option.
Floor: FRI/STARK soundness (#lean("EngineSound.recursive_sound")), Poseidon2-CR,
ed25519, PostGSTProgress.

*R --- The running entry.* _A, B, and C hold over what the node actually
invokes._ The five guarantees above are stated over the kernel; guarantee R
closes the gap to the deployment in one statement,
#lean("FullForestAuth.running_entry_sound"), about
#lean("FullForestAuth.execFullForestG") --- the body behind the
`dregg_exec_full_forest_auth` FFI export (@sec-realization): a committed gated
forest conserves per asset, every delegation edge is non-amplifying
(#lean("FullForestAuth.execFullForestG_no_amplify")), and every node at every
depth attests its gate (credential, caveats, capability-authority, and the
per-asset obligation). The gate strengthens rejection without weakening the
linear guarantees (#lean("FullForestAuth.execFullForestG_unauthorized_fails")).

== The assumption floor

Everything above is unconditional in the Lean-kernel sense *modulo* eight
carriers --- entering as `Prop`-portals (typeclass fields or hypotheses), never
as axioms; nothing else is load-bearing anywhere in the case.

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*carrier*], [*what it guards*], [*quantum posture*]),
    [Poseidon2-permutation CR], [sponge / Merkle / state commitments reduce to
      permutation collision-resistance], [generic speedups only],
    [BLAKE3 CR], [the out-of-circuit content / transcript hash],
      [generic speedups only],
    [ed25519 EUF-CMA], [turn and strand-block signatures],
      [*falls to Shor*],
    [HMAC (PRF/MAC) unforgeability], [macaroon caveat-chain tags],
      [generic speedups only],
    [AEAD confidentiality + integrity], [sealed-value / disclosure payloads],
      [generic speedups only],
    [discrete-log hardness], [Pedersen value commitments],
      [*falls to Shor*],
    [FRI / STARK soundness], [a verifying proof attests its statement
      (#lean("EngineSound.recursive_sound")); quantified below],
      [generic speedups only],
    [PostGSTProgress], [eventual synchrony after GST --- the consensus liveness
      carrier (@sec-ordering)], [not cryptographic],
  ),
  caption: [The eight-carrier floor. The first seven are cryptographic; the last
    is liveness. Safety rests on the cryptographic seven; liveness additionally
    on the eighth. The quantum column records structural quantum attacks;
    "generic speedups only" means no attack better than Grover-class search is
    known.],
)

The FRI/STARK row is the one carrier the case prices in bits, because it is not
at parity with the other six cryptographic rows and presenting it unqualified
beside ed25519 EUF-CMA would suggest otherwise. The deployed recursion apex ---
the proof a light client actually checks --- runs at extension degree 4 over
BabyBear, log-blowup 6, 19 queries, and 16 grinding bits, with running tables
floored at $2^16$ rows, so the initial evaluation domain is $2^22$. Composing
the batched-FRI theorem of Ben-Sasson--Carmon--Ishai--Kopparty--Saraf (2020)
through the ethSTARK min rule yields *57.98 bits* for that configuration; under
the same authors' 2025 successor bound, whose exception count is linear rather
than quadratic in the domain, the figure is *$approx 70.9$ bits*, but the
composition of that bound into a FRI soundness statement is not published ---
the calculation is this project's. Both figures bound the acceptance
probability of a supplied proof and omit the DEEP/ALI terms, so they are
optimistic upper bounds on a density claim; extraction --- that an accepting
proof yields a witness --- is the carrier itself, not a consequence of these
numbers. The two-column structure of the bound is mechanized:
#lean("FriLedgerSound.query_ledger_does_not_determine_perFold") proves that the
query ledger alone does not determine the per-fold proximity error, so the case
never multiplies the two into a single headline. At the deployed extension
degree the proven ceiling is 88.5 bits and 128 is unreachable at any query
count; at extension degree 8 the mechanized ledger reads 122.60 bits on every
shipped configuration (log-blowup 6, 36 queries, 16 grinding bits;
`docs/reference/PROVEN-120-CONFIG.md`), with higher-query rows reaching 129.9,
at the cost of rewriting the outer wrap and re-keying every verification key.
The parameter space, both bounds, and the cutover levers are treated in full in
@sec-proofs.

Two rows fall to Shor's algorithm: a quantum adversary recovers ed25519 signing
keys and breaks the binding of Pedersen commitments (hiding is unconditional,
and conservation over cleartext integers never touches the row). The proven
path off the brittle rows is hybrid. A hybrid ed25519 $and$ ML-DSA certificate
remains unforgeable when the classical half is replaced by an always-accepting
verifier --- a total classical break buys the adversary nothing against the
AND-composition (#lean("HybridQuorum.hybrid_survives_classical_break")) --- and
finalization safety survives a break of either half:
#lean("ConsensusSafety.consensus_safe_under_floor") derives that no two
conflicting blocks finalize under $n > 3f$ together with the disjunction of the
discrete-log and Module-SIS floors. The deployed `dregg-pq` signing surface
refines the modeled scheme
(#lean("DreggPqRefinement.dregg_pq_refines_sigscheme")); on the signature path
one hypothesis remains, named rather than laundered: that the `fips204` crate
implements FIPS 204 (#lean("DreggPqRefinement.Fips204Correct")). The
post-quantum development --- the quantum adversary model, the primitive games,
and the hybrid reductions --- has its own section; this table records only
which rows it protects.

In particular: there is no trusted executor, no out-of-band "this was
authorized" premise, and no field of the post-state left uncommitted.
