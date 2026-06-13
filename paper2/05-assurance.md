# 5 · The assurance case

The system's guarantees are an artifact, not a narrative:
`Dregg2/AssuranceCase.lean` states them **by guarantee**, assembles under
each the keystone DAG that discharges it, and `#assert_axioms`-pins every
name — the Lean build fails unless each theorem's full axiom set is exactly
the kernel triple `{propext, Classical.choice, Quot.sound}`. (The
machine-readable form is the generated assurance catalog; UI badges and the
docs embed it rather than restating it.) `Dregg2/Claims.lean` is the
corpus-wide per-keystone pin net behind this file.

## 5.1 The guarantees

**A — Authority.** *Every state change is justified by an unforgeable,
non-amplified, fresh token chain.* Apex `authority_guarantee`: an
introduction's conferred capability is a genuine non-amplifying subset of
the held one **and** the predicate discriminates — an amplifying grant is
rejected. Keystones: `introduce_non_amplifying`,
`amplifying_grant_rejected`, the per-mode admission soundness
(`captp_sound`, `bearer_sound`, `token_sound`), and the dispatcher gate
`captp_granted_le_held`. Floor: ed25519, HMAC, Poseidon2-CR.

**B — Conservation.** *Per asset, the resource sum is exactly zero across a
turn and a run.* Apex `conservation_guarantee` over the genuine multi-asset
ledger: the moved asset's total is invariant and every other asset is
pointwise untouched. Keystones: `recTransferBal_sum_conserve_moved`,
`recTransferBal_untouched`, `recKExec_conserves`,
`Spec.conservation_over_monoid`, with `committed_iff_cleartext` proving the
committed and cleartext judgments agree. Floor: none beyond integer
arithmetic (Pedersen/DLog only if values are committed).

**C — Integrity.** *A receipt binds the whole post-state; a tampered input
is rejected.* The apex is the cross-bind:
`runnable_binds_same_system_roots`, with the teeth `chC_bad_not_bridge` (a
field-dropping commitment is not a faithful bridge) and the one-receipt
welds (`argus_commits_to_one_receipt`,
`argus_circuit_executor_receipts_agree`). Floor: Poseidon2-permutation-CR —
a second preimage is exactly the only way to forge a receipt for a different
state.

**D — Freshness.** *No replay or double-spend; revocation takes effect at
finality.* Apex `freshness_guarantee`: a committed spend's nullifier was
fresh, is now present, and a repeat fails closed. Keystones: the noteSpend
term theorems, `nonmembership_sound`/`_complete`, and
`Liveness.revocation_needs_consensus` (revocation is consensus-bound — it
takes effect when and only when all relevant views agree the epoch
advanced; its dual `dead_undecidable` is pinned alongside). Floor:
Poseidon2-CR; PostGSTProgress for the at-finality leg.

**E — Unfoolability.** *A light client verifying a Q-chain learns A–D for
the whole history while re-witnessing nothing.* The apex is
`light_client_verifies_whole_history` (§4.4) with the anti-tamper teeth and
the strand realization. Floor: FRI/STARK soundness
(`EngineSound.recursive_sound`), Poseidon2-CR, ed25519, PostGSTProgress.

**R — The running entry.** *A, B, and C hold over what the node actually
invokes.* The five guarantees above are stated over the kernel; guarantee R
closes the gap to the deployment in one statement, `running_entry_sound`,
about `execFullForestG` — the body behind the `dregg_exec_full_forest_auth`
FFI export: a committed gated forest conserves per asset, every delegation
edge is non-amplifying, and every node at every depth attests its gate
(credential ∧ caveats ∧ capability-authority ∧ the per-asset obligation).
The gate adds teeth without weakening the linear guarantees
(`execFullForestG_unauthorized_fails`: any failing leg rejects the whole
forest).

## 5.2 The assumption floor

Everything above is unconditional in the Lean-kernel sense *modulo* eight
carriers — entering as `Prop`-portals (typeclass fields / hypotheses), never
as axioms; nothing else is load-bearing anywhere in the case:

1. **Poseidon2-permutation collision-resistance** — sponge/Merkle/state
   commitments reduce to permutation-CR;
2. **BLAKE3 collision-resistance** — the out-of-circuit content/transcript
   hash;
3. **ed25519 EUF-CMA** — turn / strand-block signatures;
4. **HMAC (PRF/MAC) unforgeability** — macaroon caveat-chain tags;
5. **AEAD confidentiality+integrity** — sealed-value / disclosure payloads;
6. **Discrete-log hardness** — Pedersen value commitments;
7. **FRI / STARK soundness** — a verifying proof attests its statement; the
   one recursion obligation `EngineSound.recursive_sound`;
8. **PostGSTProgress** — eventual synchrony after GST; the consensus
   liveness carrier.

In particular: there is no trusted executor, no out-of-band "this was
authorized" premise, and no field of the post-state left uncommitted.
