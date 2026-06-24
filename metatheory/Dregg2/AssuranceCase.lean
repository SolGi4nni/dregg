/-
# Dregg2.AssuranceCase — the assurance case as an artifact, organized BY GUARANTEE.

`Dregg2.Claims` is the chronological axiom-hygiene ledger: it re-pins every keystone the
corpus advertises, section by section, in roughly the order the work landed. That is the
right shape for a CI net but the wrong shape for *reading the case*. This file is the
complementary artifact — it states the FIVE top-level guarantees the system makes to a
light client, and under each one assembles exactly the keystones that discharge it, as a
small theorem-DAG. Read top-to-bottom it answers "why should I trust a Q-chain?", not
"what landed when?".

Like `Claims`, this proves *little* new mathematics: each guarantee is either a thin NEW
aggregation theorem that conjoins its existing keystones into one statement, or — where a
single existing theorem already IS the apex — a re-pin of that theorem under its guarantee
heading. Every keystone referenced here is imported transitively through the root `Dregg2`
and is independently `#assert_axioms`-clean in its home module; the per-guarantee pins below
re-certify that the WHOLE DAG feeding each guarantee rests only on the kernel triple
`{propext, Classical.choice, Quot.sound}` plus the named §8 cryptographic carriers (which,
entering as typeclass parameters / hypotheses, do not appear in `collectAxioms`).

## The assumption floor (EVERYTHING below rests on these, and NOTHING else)

The guarantees are unconditional in the Lean kernel sense *modulo* a small, explicit set of
cryptographic hardness / collision-resistance assumptions. These are the system's trust
boundary; they enter as `Prop`-portals (typeclass fields / hypotheses), never as `axiom`:

  1. **Poseidon2-permutation collision-resistance** — the arithmetization-friendly hash; the
     sponge/Merkle/state-commitment/MMR collision-resistance is reduced to permutation-CR
     (`Crypto.Poseidon2*`, `Crypto.Merkle`, the `recStateCommit` injectivity portal, the
     receipt-index `Lightclient.MMR.mroot_binds_position`, and the sorted-set/queue
     `Apps.QueueRoot.RootCR`/`LenBindCR` and identity-keyset `Apps.PreRotation.KeySetCR`
     carriers — every one a named CR `Prop` over a `Poseidon2`/`BLAKE3` image, NOT an `axiom`).
  2. **BLAKE3 collision-resistance** — the out-of-circuit content/transcript hash.
  3. **ed25519 EUF-CMA** — turn / strand-block signature unforgeability.
  4. **HMAC (PRF/MAC) unforgeability** — macaroon caveat-chain tags (`Authority.CaveatChain`).
  5. **AEAD confidentiality+integrity** — sealed-value / disclosure payloads.
  6. **Discrete-log hardness** — Pedersen value commitments (`Crypto.Pedersen`).
  7. **FRI / the STARK soundness chain** — a verifying proof attests its statement; the one
     recursion obligation `RecursiveAggregation.EngineSound.recursive_sound`.
  8. **PostGSTProgress** — the network is eventually synchronous (after GST); the consensus
     LIVENESS carrier (`World.gst_liveness`, derived from a DLS88/HotStuff `Pacemaker`).

No other assumption is load-bearing anywhere in the case below. In particular: there is no
trusted executor, no out-of-band "this turn was authorized" premise, and no field of the
post-state left uncommitted (see guarantee C). The DEPLOYMENT-side boundary — which prover
covers which turn shape, the host-fed admission inputs, and producer coverage — is named
explicitly in the **Named boundary seams** section after guarantee R (a seam the case does
not name is a seam the case launders).

## The five guarantees

  A. **Authority** — every state change is justified by an unforgeable, non-amplified,
     fresh token chain (no effect confers more authority than was held).
  B. **Conservation** — per asset, the resource sum is exactly zero across a turn (and a
     run): nothing is minted or burned outside the supply discipline.
  C. **Integrity** — a receipt binds the WHOLE post-state; a tampered input is rejected
     (the commitment is determined by, and recovers, every state field).
  D. **Freshness** — no replay / double-spend; a committed spend's nullifier was fresh, and
     a repeat is rejected; revocation takes effect at finality (consensus-bound).
  E. **Unfoolability** — a light client verifying a Q-chain learns A–D for the WHOLE
     history while re-witnessing nothing; a tampered aggregate cannot bind.

These five are not merely listed: the section **THE COMPOSED SECURITY THEOREM** (after guarantee R)
states `deployed_system_secure` — ONE theorem whose conclusion is the CONJUNCTION A ∧ B ∧ C ∧ D ∧ E,
with the integrity/authority/value legs (A ∧ B ∧ C, including the WHOLE-TURN memory program c2) all
over the SAME committed `execFullForestG` forest (a committed noteSpend for D, a verified recursion
aggregate for E), bodies the REAL keystones, so the guarantees are seen to CHAIN, not pile. Every
guarantee apex below carries CONTENT — none is a `True` anchor: `integrity_guarantee` states the
whole-post-state memory-program binding (per-verb, and `ForestMemoryProgram` composes it to the WHOLE
TURN), and `unfoolability_guarantee` states the whole-history attestation conjoined with conservation
DERIVED FROM VERIFICATION (no prover-supplied state-continuity hypothesis).
-/
-- The SPECIFIC keystone modules this assurance case references (NOT the root `Dregg2`
-- aggregator — that would be a circular import, since `Dregg2` imports this file).
import Dregg2.Conserve                       -- conservation: the shared sum_transfer_conserve library lemma
import Dregg2.Exec.RecordKernel              -- conservation (ExactConservation) + freshness (nullifiers/epochs)
import Dregg2.Exec.EffectsAuthority          -- authority: the per-effect non-amplification theorems
import Dregg2.Exec.AuthModes                 -- authority: the credential-gate admission modes
import Dregg2.Circuit.RecursiveAggregation   -- unfoolability: light_client_verifies_whole_history
import Dregg2.Crypto.LightClientUC           -- unfoolability: the GAME-BASED reduction (Unfoolable ⇐ STARK/FS extractability + sponge-CR binding)
import Dregg2.Distributed.HistoryAggregation -- unfoolability: the strand/history aggregation surface
import Dregg2.Crypto.NonMembership           -- freshness: nonmembership_sound/complete (no double-spend)
import Dregg2.Liveness                       -- freshness: revocation_needs_consensus
import Dregg2.Circuit.CommitmentCrossBind
import Dregg2.Circuit.Argus.Receipt
import Dregg2.Exec.UniversalBridge          -- integrity (STRENGTHENED): the executor IS a memory program (uproj = total post-state projection)
import Dregg2.Circuit.Argus.Aggregate
import Dregg2.Circuit.Argus.Effects.NoteSpend
import Dregg2.Exec.FullForestAuth          -- the RUNNING ENTRY: execFullForestG (the dregg_exec_full_forest_auth FFI)
import Dregg2.Exec.ForestMemoryProgram     -- integrity C(c2): the WHOLE-TURN memory program over the SAME forest (MEDIUM-7/8)
import Dregg2.Exec.ReachableConservation   -- conservation (W1): Σ=0 as a reachability invariant
import Dregg2.Exec.IssuerMove              -- conservation (W1): the issuer-move mechanism + the legacy-break tooth
import Dregg2.Circuit.Spec.supplycreation  -- authority (E2): mintA_authorized — the GENUINE iff over the independent MintASpec
import Dregg2.Apps.CapSlotFactory          -- freshness (R7): stored-cap retrieval-epoch gate + no-forge-from-storage

namespace Dregg2.AssuranceCase

open Dregg2.Exec
open Dregg2.Circuit
open Dregg2.Exec.EffectsAuthority (ECap IsNonAmplifying introduce_non_amplifying amplifying_grant_rejected)
open Dregg2.Authority (Auth capAuthConferred)
open Dregg2.Circuit.Argus (interp noteSpendStmt noteSpendStmt_no_double_spend noteSpendStmt_inserts
  noteSpendStmt_then_reject)

/-! ===========================================================================
## Guarantee A — AUTHORITY

*Every state change is justified by an unforgeable, non-amplified, fresh token chain.*

DAG:
  • `AuthModes.captp_granted_le_held` — the dispatcher GATE: when a CapTP-delivered handoff
    admits, `granted.rights ≤ held.rights`. This is the `is_attenuation(held, granted)`
    check dregg1's `verify_captp_delivered` FAILS to perform; the gate certifies it.
  • `AuthModes.captp_sound` / `bearer_sound` / `token_sound` — the per-mode soundness
    refinements: admission + the abstract premises discharge a Granovetter `Introduce` /
    delegation edge / discharged-token verify-seam.
  • `EffectsAuthority.introduce_non_amplifying` — the HEADLINE over the real `List Auth`
    attenuation lattice: a conferred cap is a genuine SUBSET of the held cap.
  • `EffectsAuthority.amplifying_grant_rejected` — the TEETH: a grant conferring authority
    the holder lacks is REJECTED (the predicate is two-valued, not `:= True`).
  • `Spec.introduce_non_amplifying` (the Spec-level capability graph) closes the loop.

COVERAGE (every authority-conferring path, post-reduction): the live verb set confers
authority through exactly these mouths, and each is pinned below —
  * `introduceA` (copy of a held cap)            — `execFullA_introduceA_non_amplifying`;
  * `delegateAttenA` (the EXECUTED narrowed grant)— `execFullA_delegateAttenA_non_amplifying`
    (+ the kernel-op face `recKDelegateAtten_non_amplifying`); forest delegation EDGES are the
    same op, covered for EVERY committed forest by `running_entry_sound` (guarantee R);
  * `attenuateA` / `refreshDelegationA`           — `execFullA_attenuateA_non_amplifying`,
    `EffectsAuthority.refresh_non_amplifying` (a refresh is a re-snapshot via attenuation);
  * `revokeDelegationA`                           — `revokeDelegation_non_amplifying` (only
    subtracts);
  * `exerciseA`                                   — `exercise_non_amplifying` (using a cap
    confers nothing new) + the R4 facet gate (an inner effect demanding a facet the held cap
    lacks ⇒ `none`);
  * `setPermissions`                              — `setPermissions_non_amplifying`;
  * STORED caps (caps-in-slots, the F3 seal/swiss/sturdyref replacement) — the storage
    round-trip confers nothing beyond the original grant: `CapSlotFactory.no_forge_from_storage`
    (store-mouth held-gated; retrieval = one survivor grant of the SAME payload);
  * PRODUCTION authority (mint) is not a cap-grant at all: it is gated on holding the ISSUER
    cell's cap (`Circuit.Spec.SupplyCreation.mintA_authorized`, pinned under guarantee B — the
    GENUINE binding: executor⟺spec over the independent `MintASpec`, not a gate-extract) — the
    constructive production law, never a recipient-shaped grant;
  * cell BIRTH (`createCellA` / factory create) grants the creator a cap to the NEW cell only —
    authority over a previously-nonexistent resource, not amplification of held authority.
There is no other cap-conferring constructor in `FullActionA`; the wire enum is reconciled
against the registry (`Substrate.VerbRegistry.classify`, exhaustive by the compiler).

The WHO leg: `credentialValid` is the §8 `AuthPortal` PORTAL (routed to
`CryptoKernel.verify` / `Credential.verify` — the named ed25519/HMAC carriers), NOT a proven
signature scheme. That is the same floor item 3/4 above, entering as a typeclass; the gate's
soundness statement (`captp_sound`/`token_sound`) is conditional on it, as stated.

Floor: ed25519 (signature on the handoff), HMAC (caveat-chain tags), Poseidon2-CR
(in-circuit cap-root openings). No trusted "this was authorized" premise survives.
=========================================================================== -/

/-- **`authority_guarantee` (NEW aggregation).** The authority headline over the REAL
`List Auth` attenuation lattice, in one statement: (1) an introduction's conferred cap is a
genuine non-amplifying SUBSET of the held cap (`introduce_non_amplifying`), AND (2) the
non-amplification predicate DISCRIMINATES — a grant conferring an authority the
holder lacks is rejected (`amplifying_grant_rejected`). So "no effect confers more authority
than was held" is proved AND shown to have teeth. The CapTP-handoff refinement that lands
this on the dispatcher gate is `AuthModes.captp_sound` / `captp_granted_le_held`, re-pinned
below. -/
theorem authority_guarantee
    (held granted : ECap) (keep : List Auth) (a : Auth)
    (hgranted : a ∈ capAuthConferred granted)
    (hheld : a ∉ capAuthConferred held) :
    IsNonAmplifying held (attenuate keep held)
      ∧ ¬ IsNonAmplifying held granted :=
  ⟨introduce_non_amplifying held keep,
   amplifying_grant_rejected held granted a hgranted hheld⟩

#assert_axioms authority_guarantee
-- the underlying keystones, re-pinned under Authority:
#assert_axioms Dregg2.Exec.AuthModes.captp_granted_le_held
#assert_axioms Dregg2.Exec.AuthModes.captp_sound
#assert_axioms Dregg2.Exec.AuthModes.bearer_sound
#assert_axioms Dregg2.Exec.AuthModes.token_sound
#assert_axioms Dregg2.Exec.EffectsAuthority.introduce_non_amplifying
#assert_axioms Dregg2.Exec.EffectsAuthority.introduce_grounded_and_non_amplifying
#assert_axioms Dregg2.Exec.EffectsAuthority.amplifying_grant_rejected
#assert_axioms Dregg2.Spec.introduce_non_amplifying
-- the per-mouth COVERAGE pins (every authority-conferring path, see the coverage note above):
#assert_axioms Dregg2.Exec.TurnExecutorFull.execFullA_introduceA_non_amplifying
#assert_axioms Dregg2.Exec.TurnExecutorFull.execFullA_attenuateA_non_amplifying
#assert_axioms Dregg2.Exec.TurnExecutorFull.execFullA_delegateAttenA_non_amplifying
#assert_axioms Dregg2.Exec.recKDelegateAtten_non_amplifying
#assert_axioms Dregg2.Exec.EffectsAuthority.revokeDelegation_non_amplifying
#assert_axioms Dregg2.Exec.EffectsAuthority.attenuate_non_amplifying
#assert_axioms Dregg2.Exec.EffectsAuthority.refresh_non_amplifying
#assert_axioms Dregg2.Exec.EffectsAuthority.exercise_non_amplifying
#assert_axioms Dregg2.Exec.EffectsAuthority.setPermissions_non_amplifying
#assert_axioms Dregg2.Apps.CapSlotFactory.no_forge_from_storage

/-! ===========================================================================
## Guarantee B — CONSERVATION

*Per asset, the resource sum is IDENTICALLY ZERO — on every reachable state, always.*

W1 (DREGG3 §2.2 — the value unification): `AssetId := CellId`. Every asset IS its issuer
cell; the issuer's own balance row (the WELL) carries −supply, mint/burn/bridgeMint are
ordinary moves against the negative-capable well, and NO verb in the kernel moves any
asset's sum (`ledgerDeltaAsset_eq_zero` — the delta family vanishes identically). So the
guarantee is no longer "the sum is invariant across a step": it is `∀ a, Σ_c bal c a = 0`
on every state reachable from a value-empty genesis — exactness, unconditionally, with NO
zero-net side condition and NO disclosed-non-conservation exemption (no modulo-burn, no
bridge-outflow, no supply-increment mint).

DAG:
  • `Exec.ReachableConservation.reachable_total_zero` — THE APEX: every reachable state
    satisfies `ExactConservation` (`∀ a, recTotalAsset k a = 0`).
  • `TurnExecutorFull.ledgerDeltaAsset_eq_zero` — the per-verb delta family vanishes:
    there is NO non-conserving verb (mint/burn/bridgeMint became issuer-moves).
  • `TurnExecutorFull.execFullA_conserves_exact` / `execFullTurnA_conserves_exact` — every
    committed action/transaction conserves EVERY asset exactly (unconditional).
  • `TurnExecutorFull.recKMintAsset_delta` / `recKBurnAsset_delta` — the reshaped supply
    verbs conserve (the issuer-debit and recipient-credit cancel inside the sum); their
    authority gate targets the ISSUER (`Circuit.Spec.SupplyCreation.mintA_authorized` — the
    production law E2, derived through `execMintA_iff_spec` over the INDEPENDENT `MintASpec`, not a
    bare gate-extract);
    `IssuerMove.recKMintAsset_breaks_exact` is the non-vacuity tooth (the LEGACY
    supply-increment law provably breaks the value law — the reshape is a repair).
  • `RecordKernel.recTransferBal_sum_conserve_moved` / `recTransferBal_untouched` — the
    transfer keystones every move (ordinary or issuer) instantiates: the moved column's
    debit/credit cancel; untouched assets are pointwise unchanged (no cross-asset leakage).
  • `Conserve.sum_transfer_conserve` — the shared library lemma the above rest on; with the
    honesty rail requiring `src ≠ dst`.

Floor: NONE beyond integer arithmetic. Conservation is a kernel theorem; the only crypto
that touches it is Pedersen (DLog) IF values are committed rather than cleartext, and the
case proves committed = cleartext via `Spec.committed_iff_cleartext`.

DEPLOYMENT CORRESPONDENCE (named, not closed — the theorem's hypothesis vs the running node):
`reachable_total_zero` quantifies over states reachable from a VALUE-EMPTY genesis
(`GenesisState`: `bal ≡ 0`; live cells may pre-exist, value may not). Two deployed paths are
TODAY outside that hypothesis, and this case does not claim them:
  1. **Devnet genesis seeding** — `node/src/genesis.rs` mints the faucet (1,000,000) and demo
     agents (alice/bob/carol) with positive balances and NO issuer well carrying −supply, so
     the deployed genesis is not value-empty in the model's sense. The W1-faithful fix is to
     seed via issuer-moves from a genesis issuer cell (then genesis Σ=0 holds by construction).
  2. **The legacy atomic-path fee epilogue** — `turn/src/executor/atomic.rs` (the fee deduct
     in `execute_atomic`) debits `atomic_turn.fee` from the agent with no crediting move: a
     burn OUTSIDE the issuer-move discipline (DREGG3 staged item: fees become moves to wells).
Until both are reshaped, `conservation_guarantee` is a theorem about the kernel the node RUNS
(`execFullTurnA` — every committed transaction preserves Σ exactly) but the deployed CHAIN's
Σ is offset by its genesis seed and decremented by legacy fees. Reported here so the spec
SAYS what it covers; the closure lane is the genesis/fee reshape, not a caveat to carry.
=========================================================================== -/

open Dregg2.Exec.ReachableConservation (Reachable reachable_total_zero) in
/-- **`conservation_guarantee` (W1: the sum is identically ZERO).** On every state reachable
from a value-empty genesis, EVERY asset's total — the issuer wells included — sums to
exactly `0`. Not invariant: zero. The issuer of each asset carries −(circulating supply) in
its own row, so the books close by construction and every committed transaction keeps them
closed (`execFullTurnA_conserves_exact`, no zero-net hypothesis — the delta family vanishes
identically). -/
theorem conservation_guarantee
    (s : Dregg2.Exec.RecChainedState) (h : Reachable s) :
    ∀ a : AssetId, recTotalAsset s.kernel a = 0 :=
  reachable_total_zero s h

/-- **`conservation_guarantee_step` (the per-move face).** A transfer of asset `a` from `src`
to `dst` (`src ≠ dst`) (1) leaves the total supply of `a` exactly invariant AND (2) leaves
every other asset `b` pointwise untouched. Σ unchanged per asset, no cross-asset leakage —
the keystone every move (ordinary transfer, mint-as-issuer-move, burn-as-return-to-well)
instantiates. -/
theorem conservation_guarantee_step
    (acc : Finset CellId) (bal : CellId → AssetId → ℤ)
    (src dst : CellId) (a : AssetId) (amt : ℤ)
    (hsrc : src ∈ acc) (hdst : dst ∈ acc) (hne : src ≠ dst) :
    (∑ c ∈ acc, recTransferBal bal src dst a amt c a) = (∑ c ∈ acc, bal c a)
      ∧ ∀ (b : AssetId), b ≠ a → ∀ c, recTransferBal bal src dst a amt c b = bal c b :=
  ⟨recTransferBal_sum_conserve_moved acc bal src dst a amt hsrc hdst hne,
   fun b hb c => recTransferBal_untouched bal src dst a b amt hb c⟩

#assert_axioms conservation_guarantee
#assert_axioms conservation_guarantee_step
-- the W1 keystones, re-pinned under Conservation:
#assert_axioms Dregg2.Exec.ReachableConservation.reachable_total_zero
#assert_axioms Dregg2.Exec.TurnExecutorFull.ledgerDeltaAsset_eq_zero
#assert_axioms Dregg2.Exec.TurnExecutorFull.execFullA_conserves_exact
#assert_axioms Dregg2.Exec.TurnExecutorFull.execFullTurnA_conserves_exact
#assert_axioms Dregg2.Exec.TurnExecutorFull.recKMintAsset_delta
#assert_axioms Dregg2.Exec.TurnExecutorFull.recKBurnAsset_delta
-- the production-authority law E2 (mint is gated on the ISSUER cap), as the GENUINE binding: derived
-- through `execMintA_iff_spec` over the INDEPENDENT `MintASpec` (linter-PASS: independent + non-vacuous
-- via `mintA_rejects_unauthorized`), NOT the bare `recKMintAsset_authorized` gate-extract.
#assert_axioms Dregg2.Circuit.Spec.SupplyCreation.mintA_authorized
#assert_axioms Dregg2.Circuit.Spec.SupplyCreation.execMintA_iff_spec
#assert_axioms Dregg2.Exec.TurnExecutorFull.recKMintAsset_requires_live_issuer
-- the non-vacuity tooth: the LEGACY supply-increment mint provably BREAKS the value law
-- (so the issuer-move reshape is a repair, not a relabeling):
#assert_axioms Dregg2.Exec.IssuerMove.recKMintAsset_breaks_exact
#assert_axioms Dregg2.Exec.IssuerMove.recKBurnAsset_breaks_exact
-- the underlying keystones, re-pinned under Conservation:
#assert_axioms Dregg2.Exec.recTransferBal_sum_conserve_moved
#assert_axioms Dregg2.Exec.recTransferBal_untouched
#assert_axioms Dregg2.Exec.recKExec_conserves
#assert_axioms Dregg2.Exec.recTransfer_balanceSum_conserve
#assert_axioms Dregg2.Spec.turnConserves_balance
#assert_axioms Dregg2.Spec.conservation_over_monoid
#assert_axioms Dregg2.Spec.committed_iff_cleartext
#assert_axioms Dregg2.Conserve.sum_transfer_conserve
-- the shared `Conserve` library lemmas the per-asset sums rest on:
#assert_axioms Dregg2.Conserve.sum_indicator
#assert_axioms Dregg2.Conserve.sum_pointUpdate
#assert_axioms Dregg2.Conserve.sum_conserve_of_deltas_zero

/-! ===========================================================================
## Guarantee C — INTEGRITY

*A receipt binds the WHOLE post-state; a tampered input is rejected.*

DAG:
  • `Circuit.Argus.Receipt.argus_commits_to_one_receipt` — THE connection keystone: the
    Argus circuit term commits to exactly one receipt, determined by the post-state.
  • `Circuit.Argus.Receipt.argus_circuit_executor_receipts_agree` — the cross-corner: the
    circuit's receipt and the executor's receipt AGREE (one semantics, two readings).
  • `Circuit.CommitmentCrossBind.runnable_binds_same_system_roots` — the state-commitment
    binds cells AND the rest-of-state: equal seam roots ⇒ equal full state.
  • `Circuit.CommitmentCrossBind.chC_bad_not_bridge` — the TEETH: a commitment that drops a
    field is NOT a faithful bridge (so the binding is not vacuous; a tampered field can be
    detected because the honest commitment recovers it).
  • `Circuit.Argus.Receipt.transfer_commits_to_one_receipt` — the transfer weld instance.

  STRENGTHENED (the §149 apex — the PI-binding hypothesis DISCHARGED onto the MMR):
  • `Circuit.Argus.Receipt.argus_published_index_pins_receipt` /
    `transfer_published_index_pins_receipt` — the §2 keystone carried the cross-AIR / cross-proof
    PI binding as a BARE hypothesis ("the circuit root and the executor receipt-chain root are
    pinned to the SAME published value"). That hypothesis is now DERIVED, not assumed: the receipt
    index the epoch publishes is an MMR (`Lightclient/MMR.lean`), history keys are dense positions,
    and `published_position_pins_value` (a thin lift of `MMR.mroot_binds_position`) proves —
    adversarial-server included (the prover's openings may be against its OWN log `L'`; CR forces
    `L' = L`) — that any two roots opening at the same dense position of the published index are
    EQUAL. So "both proofs bind their root to the same value" burns down to MMR openings under the
    ONE named `Poseidon2SpongeCR` floor; no out-of-band PI equation survives. The remaining protocol
    obligation is exactly MMR §6's `CommitBindsMMR` layout fact (the node writes both roots at their
    dense positions), discharged-by-construction at the flag-day layout (HORIZONLOG rotation rider).
  • THE EXECUTOR IS A MEMORY PROGRAM (`Exec.UniversalBridge`, the universal-map rotation's long
    pole): `gwrite_is_memory_program` / `move_is_memory_program` / `create_is_memory_program`
    prove that the TOTAL projection (`uproj`) of the executor's post-state — all 17 kernel fields
    + the receipt log onto the ONE domain-tagged universal address space — EQUALS the fold of the
    verb's emitted Blum trace over the pre-state projection, for the three compressed verbs against
    the LIVE executable steps (`stateStepGuarded` / `recCexec` / `createCellStep`). This is the
    constructive backbone under "a receipt binds the WHOLE post-state": every field has a universal
    address, the executor witnesses the memory program without peeking at its own post-state, and
    the boundary commitment is the sorted-map / MMR root of those cells (`index_boundary_mroot_derived`
    routes the receipt-index domain to the same MMR root, NO crypto — canonicity).

Floor: Poseidon2-permutation-CR (the `recStateCommit`/`cellCommit`/`stateCommit`
injectivity portals reduce to it; the MMR discharge rests on the SAME `Poseidon2SpongeCR`). A
second pre-image would be the only way to forge a receipt for a different state; that is exactly
the CR assumption.

THE HOSTILE-WITNESS CIRCUIT BACKBONE (what makes the binding hold against an ADVERSARIAL prover,
not just an honest one). The integrity guarantee is "a receipt binds the WHOLE post-state"; the
circuit-soundness side proves a forged proof cannot bind a post-state the kernel did not produce,
for every live effect:
  • THE COMMITMENT BINDS EVERY KERNEL WRITE. The deployed per-cell commitment absorbs a
    `record_digest` limb folding all authority-bearing fields the other limbs miss (permissions, VK,
    lifecycle, deathCert, delegate, delegation, mode, the side-table roots); two states differing in
    ANY kernel field commit differently (`cell/src/commitment.rs` `compute_authority_digest_felt`;
    test `record_digest_binds_commitment_p0_2`). This realizes the Lean `recStateCommit`'s
    whole-kernel injectivity (`RestHashIffFrame`).
  • HOSTILE-WITNESS EXTRACTION IS CLOSED FOR ALL 32 LIVE EFFECTS. `Circuit.CircuitOpenFronts`
    registers `countOpenFronts = 0`: every live effect has an `*_extract` theorem proving ANY
    public-input-bound satisfying witness — an arbitrary trace pinned only by the verifier's PI check,
    NO dead whole-trace `hEnc` — FORCES the genuine kernel step, with anti-ghost `*_extract_rejects_*`
    teeth refuting a forged component/frame/log.
  • THE VERIFIER ANCHORS. For the record-digest family (setPermissions/setVK/refusal +
    cellSeal/Unseal/Destroy/receiptArchive/makeSovereign) and the value-forced effects
    (transfer/burn/mint/bridgeMint/setField/incrementNonce), `proof_verify.rs` step 6b overrides the
    published limb to `compute_authority_digest_felt`/`lifecycle_felt_cell(trusted post-cell)`, so the
    gate forces `pubPost = digest(stepped pre)`, not `published == published` (both-polarity tests green).
  • THE EPOCH/SNAPSHOT MOVES — ALL FORCED AT THE ABSTRACT DESCRIPTOR (residual era closed). The three
    epoch/snapshot moves are bound in forced PRODUCT components, not carried residuals. All three are
    CROSS-CELL or whole-registry moves (the parent's epoch / the child's snapshot+stamp), so they are
    forced at the ABSTRACT per-effect descriptor (whose `view = chainView` commits over the WHOLE kernel),
    each via an injective `funcComponent` PRODUCT digest reading the stepped maps off the SAME before-kernel:
      – `spawnE` / `refreshDelegationE` bind `(delegations, delegationEpochAt)` to
        `spawnEpochAtMap`/`refreshEpochAtMap` (the birth/restore stamp = `before.delegationEpoch parent`);
        `spawn_circuit_refines_spec` yields `SpawnFullSpec` and `refreshDelegation_circuit_refines_spec`
        yields `RefreshDelegationFullSpec` DIRECTLY, a stale-stamp forge UNSAT
        (`refreshDelegation_full_sat_rejects_stale_stamp`).
      – `revokeDelegationFullE` (the DUAL descriptor, `Inst/revokeDelegationFullA.lean`) binds the second
        component `(delegationEpoch, delegations, delegationEpochAt)` to the full epoch step (parent `+1`,
        child snapshot cleared, stamp reset); `revokeDelegationFull_full_sound` yields the STRENGTHENED
        `RevokeDelegationFullSpec` DIRECTLY, a frozen-epoch forge UNSAT
        (`revokeDelegationFull_rejects_frozen_epoch`). This SUPERSEDES the prior within-row `epochBumpGate`
        partial-discharge (which forced only the parent bump, leaving the child clears commitment-bound):
        all three clauses are now PROVEN-forced, the `RevokeDelegationEpochResidual` conjunct dropped from
        every per-effect bridge (abstract `revokeDelegationCircuitStep`, emitted `revokeDelegationEmittedStep`,
        the `TurnEmit`/`TurnEffectRefinement` revoke arms).
    The digest is the SAME mechanism the `delegations` map already uses. VK-NOTE: the revoke descriptor
    gains a second committed component (the epoch-triple digest folds into the state-commit), so the deployed
    `revokeDelegationA` VK changes; spawn/refresh were already commitment-bound (VK-free move).
=========================================================================== -/

/-- **`integrity_guarantee` (NOW A REAL STATEMENT — the receipt binds the WHOLE post-state).**
The integrity apex, stated as an actual proposition rather than a `True` anchor: over the LIVE
executable move step (`recCexec`, the conserving transfer), the TOTAL projection (`uproj`) of the
executor's post-state — EVERY kernel field + the receipt log onto the ONE domain-tagged universal
address space — is EXACTLY the fold of the verb's emitted Blum trace over the pre-state projection.
So the post-state is determined field-by-field by a memory program the executor witnesses without
peeking at its own output; NOTHING is left off the universal address space, which is the constructive
content of "a receipt binds the whole post-state". This is the `UniversalBridge.move_is_memory_program`
keystone re-exposed as the integrity apex (no longer `True`); the cross-bind binding
(`runnable_binds_same_system_roots`), the published-MMR PI discharge, and the field-drop teeth
(`chC_bad_not_bridge`) are pinned below. -/
theorem integrity_guarantee
    (C : Dregg2.Exec.UniversalBridge.UCodec) {s s' : RecChainedState} {t : Turn}
    (h : recCexec s t = some s') :
    Dregg2.Exec.UniversalBridge.uproj C s'
      = (Dregg2.Exec.UniversalBridge.moveTrace C s t).foldl
          Dregg2.Crypto.MemoryChecking.step (Dregg2.Exec.UniversalBridge.uproj C s) :=
  Dregg2.Exec.UniversalBridge.move_is_memory_program C h

/-- **`integrity_guarantee_memory_program` (the explicit umem name — = `integrity_guarantee`).**
A re-pin of the integrity apex under its descriptive name (the §149/umem strengthening): the
executor-is-a-memory-program keystone IS the integrity guarantee, so this delegates to
`integrity_guarantee`. Retained as a named handle because the corpus references the memory-program
phrasing; the published-MMR discharge (`transfer_published_index_pins_receipt`, pinned below) turns
the cross-AIR PI-binding hypothesis the §2 apex carried into an MMR opening under the SAME
`Poseidon2SpongeCR` floor — no out-of-band root equation survives. -/
theorem integrity_guarantee_memory_program
    (C : Dregg2.Exec.UniversalBridge.UCodec) {s s' : RecChainedState} {t : Turn}
    (h : recCexec s t = some s') :
    Dregg2.Exec.UniversalBridge.uproj C s'
      = (Dregg2.Exec.UniversalBridge.moveTrace C s t).foldl
          Dregg2.Crypto.MemoryChecking.step (Dregg2.Exec.UniversalBridge.uproj C s) :=
  integrity_guarantee C h

#assert_axioms integrity_guarantee_memory_program

/-- **`integrity_guarantee_whole_turn` (THE WHOLE-TURN STRENGTHENING — MEDIUM-8).** The per-verb
memory-program binding of `integrity_guarantee` is COMPOSED to the WHOLE TURN: a committed gated
full-forest run `execFullForestG s f = some s'` — the body behind the `dregg_exec_full_forest_auth`
FFI, the SAME subject as `running_entry_sound` (A/B/c1) — is a memory program, i.e. the TOTAL
projection (`uproj`, every kernel field + the receipt log) of the post-state `s'` is the fold of the
CONCATENATED per-node Blum traces over the projection of the pre-state `s`. So "a receipt binds the
WHOLE post-state" holds over the ENTIRE turn, not just one verb. The per-step coverage hypothesis
`hcov` is the explicitly-named seam (each committing node is a memory program — DISCHARGEABLE on the
covered verb arms via `ForestMemoryProgram.eachStepMemProg_of_all_covered`, NOW covering BOTH the
field-write arm (`setFieldA`/gwrite) AND the headline value-transfer arm (`balanceA`/move — the live
`recCexecAsset` ledger move), non-vacuously). The composition is
`ForestMemoryProgram.execFullForestG_is_memory_program`: the per-verb keystones folded along the
gated linear lowering (`execFullTurnG`) and lifted to the tree (`execFullForestG_eq_execFullTurnG`) by
`List.foldl_append`. The fully-DISCHARGED sibling that carries NO `hcov` (deriving it from the
syntactic covered-language condition) is `integrity_guarantee_whole_turn_covered` below. -/
theorem integrity_guarantee_whole_turn
    {Digest Proof Request Stmt Wit CellId Rights Ctx Gateway Bytes Tag : Type}
    [DecidableEq CellId] [SemilatticeInf Rights] [OrderTop Rights] [DecidableLE Rights]
    [Dregg2.Laws.Verifiable Stmt Wit]
    [DecidableEq Tag] [Dregg2.Authority.CaveatChain.MacKernel
      (Dregg2.Authority.CaveatChain.Key Tag) Bytes Tag]
    [Dregg2.Exec.FullForestAuth.AuthPortal
      (Dregg2.Exec.FullForestAuth.Authorization Digest Proof) Ctx]
    (C : Dregg2.Exec.UniversalBridge.UCodec) (s s' : RecChainedState)
    (f : Dregg2.Exec.FullForestAuth.FullForestG (Digest := Digest) (Proof := Proof)
      (Request := Request) (Stmt := Stmt) (Wit := Wit) (CellId := CellId) (Rights := Rights)
      (Ctx := Ctx) (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag))
    (hcov : Dregg2.Exec.ForestMemoryProgram.EachStepMemProg C
      (Dregg2.Exec.FullForestAuth.lowerForestG f))
    (h : Dregg2.Exec.FullForestAuth.execFullForestG s f = some s') :
    Dregg2.Exec.ForestMemoryProgram.MemProgTrans C s s' :=
  Dregg2.Exec.ForestMemoryProgram.execFullForestG_is_memory_program C s s' f hcov h

#assert_axioms integrity_guarantee_whole_turn

/-- **`integrity_guarantee_whole_turn_covered` (THE SEAM CLOSED — `hcov` DERIVED, not carried).**
The whole-turn integrity binding with the per-step coverage seam DISCHARGED from a syntactic
covered-language condition, so the apex DERIVES the memory-program property instead of taking it as a
hypothesis. For a committed gated forest `execFullForestG s f = some s'` whose every pre-order node is
a COVERED verb — a field write (`setFieldA`/gwrite) OR a value transfer (`balanceA`/the live
`recCexecAsset` per-asset ledger move) — the WHOLE TURN is a memory program: `uproj C s'` is the fold
of the concatenated per-node Blum traces over `uproj C s`. The earlier `integrity_guarantee_whole_turn`
carried `hcov : EachStepMemProg …` as the named seam; HERE that seam is gone — `hcov` is replaced by
the decidable structural condition `∀ p ∈ lowerForestG f, IsCoveredPair p`, and
`ForestMemoryProgram.eachStepMemProg_of_all_covered` proves the memory-program coverage from it
(per-verb keystones: gwrite for the field write, the NEW `moveAsset_is_memory_program` for the
transfer). Non-vacuous: `forest_of_covered_is_memory_program` is a concrete forest language (field
writes + transfers) over which "a receipt binds the WHOLE post-state" holds with no out-of-band
premise — closing the MEDIUM-8 residual for the headline value-transfer arm. -/
theorem integrity_guarantee_whole_turn_covered
    {Digest Proof Request Stmt Wit CellId Rights Ctx Gateway Bytes Tag : Type}
    [DecidableEq CellId] [SemilatticeInf Rights] [OrderTop Rights] [DecidableLE Rights]
    [Dregg2.Laws.Verifiable Stmt Wit]
    [DecidableEq Tag] [Dregg2.Authority.CaveatChain.MacKernel
      (Dregg2.Authority.CaveatChain.Key Tag) Bytes Tag]
    [Dregg2.Exec.FullForestAuth.AuthPortal
      (Dregg2.Exec.FullForestAuth.Authorization Digest Proof) Ctx]
    (C : Dregg2.Exec.UniversalBridge.UCodec) (s s' : RecChainedState)
    (f : Dregg2.Exec.FullForestAuth.FullForestG (Digest := Digest) (Proof := Proof)
      (Request := Request) (Stmt := Stmt) (Wit := Wit) (CellId := CellId) (Rights := Rights)
      (Ctx := Ctx) (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag))
    (hcovered : ∀ p ∈ Dregg2.Exec.FullForestAuth.lowerForestG f,
      Dregg2.Exec.ForestMemoryProgram.IsCoveredPair (Digest := Digest) (Proof := Proof)
        (Request := Request) (Stmt := Stmt) (Wit := Wit) (CellId := CellId) (Rights := Rights)
        (Ctx := Ctx) (Gateway := Gateway) (Bytes := Bytes) (Tag := Tag) p)
    (h : Dregg2.Exec.FullForestAuth.execFullForestG s f = some s') :
    Dregg2.Exec.ForestMemoryProgram.MemProgTrans C s s' :=
  Dregg2.Exec.ForestMemoryProgram.forest_of_covered_is_memory_program C s s' f hcovered h

#assert_axioms integrity_guarantee_whole_turn_covered
-- the NEW per-asset MOVE keystone the discharge rests on (the live `.balanceA` arm = `recCexecAsset`),
-- and the WIDENED coverage discharge (gwrite ∨ move) that removes the bare `EachStepMemProg` seam:
#assert_axioms Dregg2.Exec.ForestMemoryProgram.moveAsset_is_memory_program
#assert_axioms Dregg2.Exec.ForestMemoryProgram.balanceA_step_memprog
#assert_axioms Dregg2.Exec.ForestMemoryProgram.eachStepMemProg_of_all_covered
#assert_axioms Dregg2.Exec.ForestMemoryProgram.forest_of_covered_is_memory_program

#assert_axioms integrity_guarantee
-- the underlying keystones, re-pinned under Integrity:
#assert_axioms Dregg2.Circuit.Argus.Receipt.argus_commits_to_one_receipt
#assert_axioms Dregg2.Circuit.Argus.Receipt.argus_circuit_executor_receipts_agree
#assert_axioms Dregg2.Circuit.Argus.Receipt.transfer_commits_to_one_receipt
#assert_axioms Dregg2.Circuit.Argus.Receipt.writeCell0_receipt_binds_tail
#assert_axioms Dregg2.Circuit.CommitmentCrossBind.runnable_binds_same_system_roots
#assert_axioms Dregg2.Circuit.CommitmentCrossBind.stateCommit_binds_cells_and_rest
#assert_axioms Dregg2.Circuit.CommitmentCrossBind.setFieldCommit_binds_cellCommit
#assert_axioms Dregg2.Circuit.CommitmentCrossBind.chC_bad_not_bridge
-- the §149 STRENGTHENING: the PI-binding hypothesis discharged onto the published MMR index
-- (the bare cross-AIR root equality is no longer carried — it is derived from MMR openings):
#assert_axioms Dregg2.Circuit.Argus.Receipt.published_position_pins_value
#assert_axioms Dregg2.Circuit.Argus.Receipt.argus_published_index_pins_receipt
#assert_axioms Dregg2.Circuit.Argus.Receipt.transfer_published_index_pins_receipt
-- THE EXECUTOR IS A MEMORY PROGRAM (the universal-map bridge): post-state projection = trace-fold
-- over the pre-state projection, for all three compressed verbs against the LIVE executable steps:
#assert_axioms Dregg2.Exec.UniversalBridge.gwrite_is_memory_program
#assert_axioms Dregg2.Exec.UniversalBridge.move_is_memory_program
#assert_axioms Dregg2.Exec.UniversalBridge.create_is_memory_program
#assert_axioms Dregg2.Exec.UniversalBridge.cap_leaf_value_codec
#assert_axioms Dregg2.Exec.UniversalBridge.index_boundary_mroot_derived

/-! ===========================================================================
## Guarantee D — FRESHNESS

*No replay / double-spend; a committed spend's nullifier was fresh; revocation at finality.*

DAG:
  • `Circuit.Argus.noteSpendStmt_no_double_spend` — IN THE TERM: if the noteSpend term
    COMMITS, the spent nullifier was NOT already in the set (`nf ∉ nullifiers`). The
    anti-replay is the primitive's own `interp`, not an out-of-band executor side table.
  • `Circuit.Argus.noteSpendStmt_then_reject` — the composed barrier: after a committed
    spend of `nf`, a second spend of the SAME `nf` fails closed.
  • `Circuit.Argus.noteSpendStmt_replay_rejected` — the TEETH (witness FALSE): a nullifier
    already present is REJECTED (`= none`); the gate is two-valued.
  • `Crypto.NonMembership.nonmembership_sound` / `_complete` — the freshness witness is a
    sorted-tree non-membership opening: `nf ∉ set` is a whole-set assertion with a circuit
    gate (closes the "in-memory only" gap).
  • `Liveness.revocation_needs_consensus` — revocation is consensus-bound: it takes effect
    when (and only when) all relevant views agree the epoch advanced (immediate AT finality,
    the negative-lifecycle dual of consensus-free GC).
  • `CapSlotFactory.{stored_cap_only_fresh_if_epoch_unrevoked, revoke_stales_stored_cap,
    store_then_revoke_refused}` — THE R7 RETRIEVAL-EPOCH RULE over STORED capabilities: a
    cap parked in a slot is stamped with the grantor's `delegationEpoch` at store time, and
    EVERY load+exercise refuses iff the grantor's epoch has advanced. This is the freshness
    leg for the ENTIRE surviving storage surface: post-F3 the seal/swiss/sturdyref verb
    family is GONE from the kernel (`VerbRegistry.no_live_factory_tags`) and caps-in-slots
    is the ONE storage pattern that replaces it, so covering `storeCap`/`retrieveCap` covers
    all stored-cap paths the kernel admits. A stored cap can no longer outlive its grantor's
    revocation (the dregg1 `apply_unseal`/`apply_exercise_via_capability` gap, closed).

Floor: Poseidon2-CR (the nullifier-set sorted-tree root openings). PostGSTProgress for the
revocation-at-finality leg (consensus terminates after GST).

KNOWN RESIDUAL (named, out-of-model): the node's MCP gateway binds biscuit-cap temporal
caveats to the live attested consensus height (`node/src/mcp.rs` `McpCapContext.block_height`)
— the height-expiry leg is real — but consults NO revocation registry for MCP-issued biscuit
caps (the gateway's own doc names this). An MCP cap dies only by expiry caveat, never by
explicit revocation, until a revocation feed is wired. That path is OUTSIDE this guarantee's
statement; it is listed here so the case says so rather than implying coverage.
=========================================================================== -/

/-- **`freshness_guarantee` (NEW aggregation).** The anti-replay case for noteSpend, in one
statement: if the noteSpend term of `nf` commits (`interp … = some k'`), then (1) `nf` was
NOT already spent (fresh) AND (2) `nf` IS now in the set, so (3) the SAME-nullifier spend on
the result fails closed — double-spend is impossible at the term level. -/
theorem freshness_guarantee {nf : Nat} {k k' : RecordKernelState}
    (h : interp (noteSpendStmt nf) k = some k') :
    nf ∉ k.nullifiers
      ∧ nf ∈ k'.nullifiers
      ∧ interp (noteSpendStmt nf) k' = none :=
  ⟨noteSpendStmt_no_double_spend h,
   noteSpendStmt_inserts h,
   noteSpendStmt_then_reject h⟩

#assert_axioms freshness_guarantee
-- the underlying keystones, re-pinned under Freshness:
#assert_axioms Dregg2.Circuit.Argus.noteSpendStmt_no_double_spend
#assert_axioms Dregg2.Circuit.Argus.noteSpendStmt_inserts
#assert_axioms Dregg2.Circuit.Argus.noteSpendStmt_then_reject
#assert_axioms Dregg2.Circuit.Argus.noteSpendStmt_replay_rejected
#assert_axioms Dregg2.Crypto.NonMembership.nonmembership_sound
#assert_axioms Dregg2.Crypto.NonMembership.nonmembership_complete
#assert_axioms Dregg2.Liveness.revocation_needs_consensus
-- the R7 stored-cap freshness keystones (caps-in-slots = the whole surviving storage surface):
#assert_axioms Dregg2.Apps.CapSlotFactory.stored_cap_only_fresh_if_epoch_unrevoked
#assert_axioms Dregg2.Apps.CapSlotFactory.revoke_stales_stored_cap
#assert_axioms Dregg2.Apps.CapSlotFactory.store_then_revoke_refused
-- the negative-lifecycle teeth: liveness/death is not decidable (consensus-bound, like revocation):
#assert_axioms Dregg2.Liveness.dead_undecidable

/-! ===========================================================================
## Guarantee E — UNFOOLABILITY

*A light client verifying a Q-chain learns A–D for the WHOLE history; re-witnessing nothing.*

This is the apex that COMPOSES A–D over an entire history and hands them to a verifier who
runs nothing but `verify agg.root`.

DAG:
  • `Circuit.RecursiveAggregation.light_client_verifies_whole_history` — THE headline:
    checking ONLY `verify agg.root` (re-witnessing NOTHING) ⇒ every turn executed correctly,
    correctly ordered, and the final root is a genuine fold. Proofs-as-additive-attestation.
  • `Circuit.RecursiveAggregation.attested_history_conserves` — the whole attested history
    conserves (guarantee B, lifted to the full run).
  • `Circuit.RecursiveAggregation.tampered_aggregate_cannot_bind` — the ANTI-GHOST: a
    reordered chain forces `ChainBound = False`, so no verifying aggregate exists.
  • `Circuit.RecursiveAggregation.leaf_pairing_defeats_swap` — positional pairing means a
    verifying leaf is not re-pointable to a different step.
  • `Distributed.HistoryAggregation.wellformed_attests_whole_history` — the IVC fold model:
    the seam tooth `new_root[i] = old_root[i+1]` pins the whole history.
  • `Distributed.HistoryAggregation.root_tooth_pins_kernel` — the STRENGTHENED CR recovery: a light
    client seeing only the matching roots learns the adjacent KERNELS coincide (state-equality, not
    merely commitment-equality), via `recStateCommit_binds_kernel` under the standard Poseidon CR set
    + the preserved `AccountsWF` invariant. This is what `root_tooth_pins_state` (commitment-equality
    only) could not deliver — the CRITICAL-3 fix.
  • `Circuit.RecursiveAggregation.conserves_from_verification` — THE CONSERVATION-OVER-HISTORY CLOSURE:
    conservation across the whole history follows from `verify agg.root` ALONE (the verified `ChainBound`
    tooth ⇒ kernel continuity ⇒ conservation), with NO prover-supplied `StateChained` hypothesis. The
    one `RecChainedState` component the §8 root does not bind is the receipt LOG; it blocks the full
    `Run` (which `attested_history_is_run` still takes `StateChained` for), never conservation — the
    exact, named residual.
  • `Circuit.Argus.Aggregate.argus_strand_light_client` + `tampered_argus_strand_rejected` —
    the Argus-strand realization of the same case on the executable term IR.

Floor: FRI / STARK soundness (`EngineSound.recursive_sound`, the ONE recursion obligation),
Poseidon2-CR (`recStateCommit` binds the seam roots), ed25519 (strand-block signatures),
PostGSTProgress (a FINALIZED — not merely valid — chain, via the finality-cert leg).
=========================================================================== -/

section UnfoolabilityApex
open Dregg2.Circuit.RecursiveAggregation
open Dregg2.Distributed.HistoryAggregation (ChainStep KernelGenesisPin SeamStruct lastStateOf)
open Dregg2.Circuit.StateCommit (compressInjective compressNInjective cellLeafInjective RestHashIffFrame)

variable {AProof : Type} (verify : AProof → Bool)
variable (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
variable (RH : Dregg2.Exec.RecordKernelState → ℤ)
variable (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)

/-- **`unfoolability_guarantee` (NOW A REAL STATEMENT — the whole-history headline, conjoined).**
The unfoolability apex, stated as an actual proposition rather than a `True` anchor: a light client
that checks ONLY `verify agg.root = true` (re-witnessing NOTHING) learns BOTH (1) `AggregateAttests`
— every turn executed correctly, the chain is correctly ordered (no reorder/drop/insert), and the
public final root is the genuine fold of the whole history — AND (2) the WHOLE history conserves value
(the endpoint ledger total equals genesis), DERIVED FROM VERIFICATION under the standard Poseidon CR
set + the genesis pin + the structural envelope, with NO prover-supplied `StateChained` hypothesis
(the CRITICAL-3 closure). So E genuinely COMPOSES A–D over the whole history handed to a
`verify agg.root`-only client. This conjoins `light_client_verifies_whole_history` with
`conserves_from_verification`; the game-based reduction (`LightClientUC.unfoolable_of_floor`) and the
anti-ghost teeth (`tampered_aggregate_cannot_bind`) are pinned below. -/
theorem unfoolability_guarantee
    (agg : Aggregate AProof) (g : RecChainedState) (steps : List ChainStep)
    (es : EngineSound AProof verify CH RH cmb compress compressN agg g steps)
    (hroot : verify agg.root = true)
    (hCmb : compressInjective cmb) (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (hRest : RestHashIffFrame RH)
    (hgen : KernelGenesisPin g steps) (hstruct : SeamStruct steps) :
    AggregateAttests AProof CH RH cmb compress compressN agg g steps
      ∧ recTotal (lastStateOf g steps).kernel = recTotal g.kernel :=
  ⟨light_client_verifies_whole_history AProof verify CH RH cmb compress compressN agg g steps es hroot,
   conserves_from_verification AProof verify CH RH cmb compress compressN
     hCmb hCompress hCompressN hLeaf hRest agg g steps es hroot hgen hstruct⟩

#assert_axioms unfoolability_guarantee

end UnfoolabilityApex
-- the underlying keystones, re-pinned under Unfoolability:
#assert_axioms Dregg2.Circuit.RecursiveAggregation.light_client_verifies_whole_history
#assert_axioms Dregg2.Circuit.RecursiveAggregation.attested_history_conserves
#assert_axioms Dregg2.Circuit.RecursiveAggregation.tampered_aggregate_cannot_bind
#assert_axioms Dregg2.Circuit.RecursiveAggregation.leaf_pairing_defeats_swap
#assert_axioms Dregg2.Circuit.RecursiveAggregation.real_engine_sound
#assert_axioms Dregg2.Distributed.HistoryAggregation.wellformed_attests_whole_history
#assert_axioms Dregg2.Distributed.HistoryAggregation.root_tooth_pins_state
#assert_axioms Dregg2.Distributed.HistoryAggregation.tooth_rejects_broken_order
-- the CRITICAL-3 closure (conservation-over-history DERIVED from verification, no StateChained):
#assert_axioms Dregg2.Distributed.HistoryAggregation.root_tooth_pins_kernel
#assert_axioms Dregg2.Distributed.HistoryAggregation.kernelChained_conserves
#assert_axioms Dregg2.Distributed.HistoryAggregation.verified_history_conserves
#assert_axioms Dregg2.Circuit.RecursiveAggregation.conserves_from_verification
#assert_axioms Dregg2.Circuit.Argus.Aggregate.argus_strand_light_client
#assert_axioms Dregg2.Circuit.Argus.Aggregate.argus_strand_conserves
#assert_axioms Dregg2.Circuit.Argus.Aggregate.tampered_argus_strand_rejected
-- the GAME-BASED unfoolability reduction (`Crypto.LightClientUC`): the soundness game `Foolable`
-- (a no-secret client accepts a state the executor did NOT produce) is IMPOSSIBLE under the floor —
-- `unfoolable_of_floor` REDUCES light-client soundness to STARK/Fiat-Shamir extractability + sponge-CR
-- binding, and `fooling_breaks_floor` extracts a concrete floor break from any fooling attack:
#assert_axioms Dregg2.Crypto.LightClientUC.unfoolable_of_floor
#assert_axioms Dregg2.Crypto.LightClientUC.fooling_breaks_floor
#assert_axioms Dregg2.Crypto.LightClientUC.unfoolable_iff_not_foolable
#assert_axioms Dregg2.Crypto.LightClientUC.SimAccepts
#assert_axioms Dregg2.Crypto.LightClientUC.Reference.refUnfoolable
#assert_axioms Dregg2.Crypto.LightClientUC.Reference.refFoolingBreaksFloor

/-! ===========================================================================
## Guarantee R — THE RUNNING ENTRY (A∧B∧C hold over what the node actually runs)

The five guarantees above are stated over the abstract kernel: the `List Auth` attenuation
lattice (A), the multi-asset ledger `recTransferBal` (B), the Argus term IR (C/D), the
aggregation fold (E). The honest question ember keeps pressing is: *do those guarantees hold
over the executor the deployed node INVOKES* — `execFullForestG`, the body behind the
`dregg_exec_full_forest_auth` FFI export (`Exec.FFI`), the one `produce_via_lean` /
`lean_shadow` call? They do, and this section proves it in ONE statement rather than leaving
it as a reader's inference.

`execFullForestG` is the credential-and-caveat-GATED whole-forest step. The gate is NOT a new
trust premise: it is discharged by `gateOK` (credential-valid ∧ cap-authority ∧
caveats-discharged), and the linear guarantees ride the `eraseG` bridge
(`execFullForestG_erases`) onto the EXISTING ungated `FullForest` theorems — so the gate ADDS
teeth (a forged credential / unauthorized cap / false caveat ⇒ `none`, the whole forest
rejects) without WEAKENING conservation or non-amplification. Floor: unchanged from A–C.
=========================================================================== -/

section RunningEntry
open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.FullForest
open Dregg2.Exec.TurnExecutorFull (turnLedgerDeltaAsset)
open Dregg2.Authority

variable {Digest Proof : Type}
variable {Request Stmt Wit CellId Rights Ctx Gateway : Type}
variable [DecidableEq CellId] [SemilatticeInf Rights] [OrderTop Rights] [DecidableLE Rights]
variable {Bytes Tag : Type}
variable [Dregg2.Laws.Verifiable Stmt Wit]
variable [DecidableEq Tag] [CaveatChain.MacKernel (CaveatChain.Key Tag) Bytes Tag]
variable [AuthPortal (Authorization Digest Proof) Ctx]

/-- **`running_entry_sound` (NEW aggregation, over the RUNNING entry).** For the gated
whole-forest step `execFullForestG` — the body behind the `dregg_exec_full_forest_auth` FFI
the node invokes — a single committed run discharges, in one statement, the three local
guarantees over the THING THAT RUNS:

  * **B (conservation, W1-strengthened):** EVERY asset's total supply (`recTotalAsset`) is
    exactly preserved across the gated forest — UNCONDITIONALLY (no zero-net hypothesis:
    the per-verb delta family vanishes identically; mint/burn/bridgeMint are issuer-moves).
    Conservation survives the credential+caveat gate, full stop.
  * **A (no amplification):** EVERY delegation edge of the forest is non-amplifying
    (`capAuthConferred (attenuate ·) ⊆ capAuthConferred ·`) — Granovetter survives the gate.
  * **C (per-node attestation):** every node, at every nesting depth, attests
    `gatedActionInvG` — credential passed the §8 oracle ∧ caveats discharged on its pre-state
    ∧ cap-authority ∧ the per-asset/chain/kind obligation. Credential-blindness eliminated.

The body is exactly the three `execFullForestG_*` keystones conjoined — no new mathematics,
the POINT is the subject: this is A/B/C over `execFullForestG`, not over the abstract kernel.
The fail-closed teeth (`execFullForestG_unauthorized_fails`: ANY failing gate leg ⇒ `none`)
are pinned below — the gate is two-valued, the attestation non-vacuous. -/
theorem running_entry_sound
    (s s' : RecChainedState)
    (f : FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag))
    (b : AssetId)
    (h : execFullForestG s f = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b
      -- ↓ THE CAP-AUTHORITY LEG (`granted ⊆ held`). GROUNDED IN TRANSCRIBED SEL4: this exact
      -- non-amplification shape is derived from seL4's OWN `derive_cap` semantics by
      -- `Dregg2.Firmament.SeL4Abstract.dregg_executor_cap_authority_grounded_in_seL4` (which composes
      -- the transcribed `seL4_derive_cap_non_amplifying`, l4v@e2f32e54 CSpace_A.thy:105-114, with an
      -- α-image-monotonicity helper) UNDER the named `SeL4DeriveNonAmpBridge` assumption
      -- (= SEL4-DERIVE-NONAMP-BRIDGE; embedding-faithfulness is a hypothesis, the α-projection a
      -- reported divergence). So this leg rests on transcribed seL4 text, not a black box.
      ∧ (∀ e ∈ forestEdgesG f, capAuthConferred (attenuate e.1 e.2) ⊆ capAuthConferred e.2)
      ∧ (∀ p ∈ lowerForestG f, ∃ sa sa',
          execFullAGated sa p.1 p.2 = some sa' ∧ gatedActionInvG sa p.1 p.2 sa') :=
  ⟨execFullForestG_conserves_exact s s' f b h,
   execFullForestG_no_amplify f,
   execFullForestG_each_attests s s' f h⟩

#assert_axioms running_entry_sound
-- the underlying keystones over the RUNNING entry, re-pinned:
#assert_axioms Dregg2.Exec.FullForestAuth.execFullForestG_conserves_per_asset
#assert_axioms Dregg2.Exec.FullForestAuth.execFullForestG_conserves_exact
#assert_axioms Dregg2.Exec.FullForestAuth.execFullForestG_ledger_per_asset
#assert_axioms Dregg2.Exec.FullForestAuth.execFullForestG_no_amplify
#assert_axioms Dregg2.Exec.FullForestAuth.execFullForestG_each_attests
#assert_axioms Dregg2.Exec.FullForestAuth.execFullForestG_root_attests
-- the fail-closed teeth (the gate is two-valued):
#assert_axioms Dregg2.Exec.FullForestAuth.execFullForestG_unauthorized_fails

end RunningEntry

/-! ===========================================================================
## THE COMPOSED SECURITY THEOREM — A ∧ B ∧ C ∧ D ∧ E, conjoined, over the deployed system.

The critique's CRITICAL-2: "five guarantees aggregated side-by-side, never conjoined; two of five
apexes are literally `:= trivial`." This section answers it with ONE theorem,
`deployed_system_secure`, whose conclusion is the CONJUNCTION of all five guarantees, and whose
subjects are the things the DEPLOYED node actually produces:

  * the per-turn core (A ∧ B ∧ C) — non-amplification, conservation, per-node attestation (c1), AND
    the WHOLE-TURN memory program (c2) — is over the SAME committed `execFullForestG s f = some s'`,
    the body behind the `dregg_exec_full_forest_auth` FFI the node invokes on every committed turn.
    The earlier subject-independence (MEDIUM-7: the c2 leg ran over a DIFFERENT, arbitrary `recCexec`
    move than the forest A/B bound) is CLOSED: c2 is now `execFullForestG_is_memory_program` over the
    very `(s, f, s')` of A/B/c1, so all four authority/value/integrity facts bind ONE turn;
  * the integrity backbone (C-c2) is strengthened to WHOLE-TURN — the per-verb memory programs folded
    along the gated linear lowering and lifted to the tree (`ForestMemoryProgram`), so "a receipt
    binds the WHOLE post-state" now holds over the ENTIRE turn (MEDIUM-8), not one verb; its per-step
    coverage hypothesis is the explicitly-named seam (dischargeable on the covered verb arms);
  * freshness (D) is the noteSpend anti-replay on the executable term IR;
  * unfoolability (E) is `light_client_verifies_whole_history` + `conserves_from_verification` over a
    published recursion aggregate the light client checks with ONE `verify agg.root` (the finalized
    published history — architecturally a distinct object from one node's local forest run).

Every leg is a PROVEN keystone (named below), discharged from the deployed-system inputs — not a
prose DAG, not a side-by-side pile, and not a `True`. The reader sees the guarantees CHAIN: a single
committed forest is simultaneously non-amplifying, conserving, and integrity-attesting; the same
verified history is fresh and unfoolable.
=========================================================================== -/

section Composed
open Dregg2.Exec.FullForestAuth
open Dregg2.Exec.FullForest
open Dregg2.Exec.ForestMemoryProgram (MemProgTrans EachStepMemProg execFullForestG_is_memory_program)
open Dregg2.Authority
open Dregg2.Circuit.RecursiveAggregation
open Dregg2.Distributed.HistoryAggregation (ChainStep KernelGenesisPin SeamStruct lastStateOf)
open Dregg2.Circuit.StateCommit (compressInjective compressNInjective cellLeafInjective RestHashIffFrame)

-- the forest's descriptor phantom types + the gate typeclasses (as in `RunningEntry`).
variable {Digest Proof : Type}
variable {Request Stmt Wit CellId Rights Ctx Gateway : Type}
variable [DecidableEq CellId] [SemilatticeInf Rights] [OrderTop Rights] [DecidableLE Rights]
variable {Bytes Tag : Type}
variable [Dregg2.Laws.Verifiable Stmt Wit]
variable [DecidableEq Tag] [CaveatChain.MacKernel (CaveatChain.Key Tag) Bytes Tag]
variable [AuthPortal (Authorization Digest Proof) Ctx]
-- the aggregate's proof carrier + verifier + the §8 commitment portal (the unfoolability layer).
variable {AProof : Type} (verify : AProof → Bool)
variable (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
variable (RH : Dregg2.Exec.RecordKernelState → ℤ)
variable (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)

/-- **`deployed_system_secure` (THE COMPOSED APEX — A ∧ B ∧ C ∧ D ∧ E, conjoined, over ONE TURN).**
For the deployed system's actual products — a committed running-entry forest `execFullForestG s f =
some s'`, a committed noteSpend, and a published recursion aggregate the light client verifies — ALL
FIVE guarantees hold AT ONCE, and crucially the INTEGRITY legs (c1 AND c2) are now over the SAME
forest `f` / SAME transition `s → s'` as A and B (the MEDIUM-7 subject-unification: the apex is a
statement about ONE committed turn, no longer a conjunction over independent subjects):

  * **A — AUTHORITY (non-amplification):** every delegation edge of the forest the node ran is
    non-amplifying (`execFullForestG_no_amplify`). No effect confers more authority than was held.
  * **B — CONSERVATION:** every asset's total supply is exactly preserved across that forest
    (`execFullForestG_conserves_exact`) — unconditionally (the delta family vanishes identically).
  * **C — INTEGRITY:** (c1) every node of the forest attests `gatedActionInvG` — credential checked,
    caveats discharged, cap-authority, the per-asset obligation (`execFullForestG_each_attests`); AND
    (c2) the WHOLE TURN is a memory program — the TOTAL projection (`uproj`, every kernel field + the
    receipt log) of the forest's POST-state `s'` equals the fold of the CONCATENATED per-node Blum
    traces over the projection of the PRE-state `s` (`execFullForestG_is_memory_program` over the SAME
    `(s, f, s')`), so the receipt binds the WHOLE post-state field-by-field across the ENTIRE turn —
    NOT just one verb (the MEDIUM-8 whole-turn composition). The per-step coverage hypothesis `hcov`
    (each committing node is a memory program) is the explicitly-named seam; it is DISCHARGEABLE on
    the covered verb arms (`eachStepMemProg_of_all_covered` — now BOTH the field-write `setFieldA`
    arm AND the headline value-transfer `balanceA` arm, the live `recCexecAsset` ledger move,
    non-vacuously). The fully-discharged covered-language apex carrying NO `hcov` is
    `integrity_guarantee_whole_turn_covered`.
  * **D — FRESHNESS:** the committed noteSpend's nullifier was fresh, is now spent, and a replay of
    the SAME nullifier fails closed (`noteSpendStmt_no_double_spend`/`_inserts`/`_then_reject`).
  * **E — UNFOOLABILITY:** a light client checking ONLY `verify agg.root` learns the WHOLE history
    executed correctly + is correctly ordered + ends at the genuine fold (`AggregateAttests`), AND
    conserves value over the whole history — DERIVED FROM VERIFICATION, with no `StateChained`
    hypothesis (`conserves_from_verification`, the CRITICAL-3 closure).

The legs are the REAL keystones, conjoined — `running_entry_sound`'s body (A∧B∧c1), the WHOLE-FOREST
memory-program composition (c2), the `Argus` noteSpend anti-replay (D), and the `RecursiveAggregation`
light-client headline + the verification-derived conservation (E). Floor: exactly the §8 carriers the
components carry (Poseidon2-CR for the commitment/aggregate, the credential oracle for the gate, FRI
for the recursion) — entering as the hypotheses below, never as `axiom`. This is the single composing
security theorem the assurance case previously lacked, now bound to ONE deployed turn end-to-end. -/
theorem deployed_system_secure
    -- A/B/C(c1+c2): the running-entry forest the node committed — the ONE subject of A, B and C.
    (s s' : RecChainedState)
    (f : FullForestG (Digest := Digest) (Proof := Proof) (Request := Request) (Stmt := Stmt)
      (Wit := Wit) (CellId := CellId) (Rights := Rights) (Ctx := Ctx) (Gateway := Gateway)
      (Bytes := Bytes) (Tag := Tag))
    (b : AssetId)
    (hrun : execFullForestG s f = some s')
    -- C(c2): the universal codec + the per-step coverage seam over the SAME forest `f` (each
    -- committing node of `f` is a memory program — discharged on the covered verb arms).
    (UC : Dregg2.Exec.UniversalBridge.UCodec)
    (hcov : EachStepMemProg UC (lowerForestG f))
    -- D: a committed noteSpend on the executable term IR.
    {nf : Nat} {k k' : RecordKernelState}
    (hspend : interp (noteSpendStmt nf) k = some k')
    -- E: a published recursion aggregate + its verified root + the named soundness/CR floor.
    (agg : Aggregate AProof) (g : RecChainedState) (steps : List ChainStep)
    (es : EngineSound AProof verify CH RH cmb compress compressN agg g steps)
    (hroot : verify agg.root = true)
    (hCmb : compressInjective cmb) (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (hRest : RestHashIffFrame RH)
    (hgen : KernelGenesisPin g steps) (hstruct : SeamStruct steps) :
    -- A:
    (∀ e ∈ forestEdgesG f, capAuthConferred (attenuate e.1 e.2) ⊆ capAuthConferred e.2)
    -- B:
    ∧ recTotalAsset s'.kernel b = recTotalAsset s.kernel b
    -- C(c1): per-node attestation
    ∧ (∀ p ∈ lowerForestG f, ∃ sa sa',
        execFullAGated sa p.1 p.2 = some sa' ∧ gatedActionInvG sa p.1 p.2 sa')
    -- C(c2): the WHOLE TURN is a memory program (whole-post-state binding over the SAME `s → s'`)
    ∧ MemProgTrans UC s s'
    -- D: freshness (no double-spend)
    ∧ (nf ∉ k.nullifiers ∧ nf ∈ k'.nullifiers ∧ interp (noteSpendStmt nf) k' = none)
    -- E: unfoolability — whole-history attestation + conservation FROM VERIFICATION
    ∧ AggregateAttests AProof CH RH cmb compress compressN agg g steps
    ∧ recTotal (lastStateOf g steps).kernel = recTotal g.kernel := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- A
    exact execFullForestG_no_amplify f
  · -- B
    exact execFullForestG_conserves_exact s s' f b hrun
  · -- C(c1)
    exact execFullForestG_each_attests s s' f hrun
  · -- C(c2): the WHOLE-FOREST memory program over the SAME `(s, f, s')` — MEDIUM-7/8.
    exact execFullForestG_is_memory_program UC s s' f hcov hrun
  · -- D: the noteSpend anti-replay triple.
    exact ⟨noteSpendStmt_no_double_spend hspend, noteSpendStmt_inserts hspend,
      noteSpendStmt_then_reject hspend⟩
  · -- E1: the light-client whole-history attestation.
    exact light_client_verifies_whole_history AProof verify CH RH cmb compress compressN
      agg g steps es hroot
  · -- E2: conservation-over-history DERIVED from `verify agg.root` (no StateChained).
    exact conserves_from_verification AProof verify CH RH cmb compress compressN
      hCmb hCompress hCompressN hLeaf hRest agg g steps es hroot hgen hstruct

#assert_axioms deployed_system_secure

end Composed

/-! ===========================================================================
## Named boundary seams (what the deployed node feeds the verified surface)

The guarantees above are kernel-unconditional modulo the §8 floor. Between the verified
surface and the deployed node there are, additionally, exactly THREE host-side seams. They
are not Lean hypotheses (nothing below `#assert_axioms`-rests on them); they are the
admission/coverage boundary of the RUNNING system, and the case is not honest unless it
names them:

  1. **The prover partition (which circuit attests which turn).** The descriptor prover —
     the Lean-emitted ONE-circuit constraint set (`EffectVmDescriptorAir`) — is the DEFAULT
     for the 17 graduated turn shapes (`sdk/src/full_turn_proof.rs` `CUTOVER_READY_SELECTORS`:
     transfer, noteSpend/Create, emitEvent, bridgeMint, burn, cellSeal/Destroy, refusal,
     setVk/setPerms, exercise, pipelinedSend, incrementNonce, refresh/revokeDelegation,
     introduce). Every OTHER turn shape falls back — LOGGED, never silent — to the legacy
     hand-written AIR (`circuit/src/effect_vm_p3_full_air.rs`). The hand-AIR enforces the
     same PI bindings and is adversarially tested (forged-commit/tamper suites), but its
     constraint set is NOT Lean-derived: for non-graduated shapes, circuit⟺kernel agreement
     is test-attested, not theorem-attested. The graduation lane closes this by emptying the
     fallback set. (The verifier side enforces the same partition: a descriptor proof must
     bind to exactly ONE graduated selector, else reject.)

  2. **The `ShadowHostCtx` host-fed admission inputs (the IF–THEN, now DISCHARGED).** The
     verified executor's admission check reads five values the HOST supplies
     (`turn/src/lean_shadow.rs` `ShadowHostCtx`): `block_height` (expiry caveats), the migration
     `frozen` set, the agent's `stored_head` receipt-chain head (anti-fork/replay), the silo
     `budget`, and `intro_lifetime`. The IF–THEN those values carry is no longer a bare comment:
     `Exec.HostCorrespondence` makes "the node's true values" an explicit `HostFacts` object,
     defines what it means for a deployed `AdmCtx` to FAITHFULLY REFLECT them (`Reflects`), and
     proves the **conditional soundness lemma** `admissible_sound_of_reflects` — a faithfully
     reflected context decides EXACTLY as the node's own admission would (`admissible ctx h s =
     admissibleFacts H h s`; the gate adds no error of its own), so every §3 fail-closed leg
     transports to the node's real receipt-chain head / silo budget / freeze-set
     (`reflects_rejects_true_fork` / `_over_budget` / `_frozen_agent`). The RESIDUAL host
     obligation is now stated PRECISELY and shown LOAD-BEARING as teeth: each unsafe under-report
     — omitting a truly-frozen referenced cell, advancing the stored head to a forked turn's
     `prev`, inflating the budget, retarding the clock — ADMITS a turn the true-facts gate REJECTS
     (`{stored_head, budget, freeze, clock}_obligation_teeth`). The FFI's freeze-set MARSHALLING
     fall-off is modeled (`marshalledFrozen` crosses only the truly-frozen cells the turn
     REFERENCES) and proven faithful on exactly the cells the gate reads, so the only deployment
     obligation is producer-coverage — every freeze-read cell (agent + write-set) must get a wire
     id — discharged end-to-end by `marshalled_admission_sound`. This residual is
     engineering- rather than cryptography-shaped; a host lying to itself about its own
     height/budget harms only admission, never the A–C invariants (which are proven over whatever
     state the executor actually runs on).

  3. **Producer coverage (which turns the verified executor PRODUCES).** By default
     (`DREGG_LEAN_PRODUCER` unset) the verified Lean executor is the authoritative state
     producer for the swap-safe covered set (`lean_shadow::producer_root_agreeing_effects`);
     turn shapes outside it are executed by the legacy Rust executor with the Lean verdict as
     a differential/veto. `running_entry_sound` quantifies over every forest the FFI is
     INVOKED on; this seam is about which turns route there. The honest partition
     (mappable = root-agreeing ∪ root-gap) is maintained in `lean_shadow.rs` and burns down
     toward total coverage.

Also named (low-severity circuit residual): the EffectVM layout still carries the F3-retired
field-seal `RESERVED` column. Every surviving effect PRESERVES it and no live verb can set a
sealed bit (the seal family's selectors are pinned to zero), but the column is NOT absorbed
into the in-circuit state commitment (`state_commit = H4(bal,nonce,fields,cap_root)` chain),
so its value is prover-chosen. No surviving semantics depends on it; the relayout lane that
regenerates descriptors against the compacted selector layout deletes it.

## THE ROTATION correspondence (REFINEMENT-DESIGN Decision 1 — what is bound today)

THE HEAP is in the kernel and in the case: `RecordKernelState.heaps` is a frame component
of every keystone (`Circuit.StateCommit.RestHashIffFrame` lists it; tampering it moves the
rest hash), the wire face `FullActionA.heapWriteA` routes through the SAME caveat-gated
`write`-verb step every register write uses (`Substrate.HeapKernel.heapStepGuardedW`:
authority + membership + lifecycle gates, fail-closed, balance-neutral exactly), and the
ONE deployed heap-root scheme is `circuit::heap_root` (the cap-root generalization with the
generic `hash[addr, value]` leaf; `heap_root_cell_circuit_differential.rs` pins it against
an independent rebuild, and the Lean gadget `Emit.EffectVmEmitHeapRoot` recomputes the SAME
arity-2 address/leaf images in-row with `heapRoot_binds_write` as the anti-ghost).

What the wire carries vs what the circuit forces, stated exactly (the cap Phase-A staging):
the turn carries `(addr, value, newRoot)` with `addr`/`newRoot` EXECUTOR-COMPUTED digests.
`heapStepGuardedW_honest` proves the honest instance IS the model step (`heapStepGuarded`);
the gadget forces `addr = hash[coll,key]`, `leaf = hash[addr,value]`, and the prepend
advance in-row — but the DEPLOYED EffectVM row does not yet carry a `heap_root` register
column of its own, the PI vector does not yet bind it, and the genuine sorted-TREE-update
gates (membership-open / leaf-update / bracketed insert, the revocation-circuit shape) are
the Phase-E lane. Until the rotation's relayout lands, `heap_root` is kernel-bound and
scheme-pinned but NOT yet circuit-committed: a heap write today is attested by the kernel
theorems, not by the per-turn proof.

THE EXECUTOR-STATE BRIDGE (the universal-map rotation's long pole, NOW LANDED — `Exec.UniversalBridge`):
the executor IS a memory program. `uproj` is the TOTAL projection of `RecordKernelState` (all 17 fields)
+ the receipt log onto the ONE domain-tagged `(Domain, key) ↦ Option ℤ` address space (registers EMPTY
by design — per-proof VM transients, never persistent state), and `gwrite/move/create_is_memory_program`
prove the post-projection equals the fold of the verb's emitted Blum trace over the pre-projection, for
the three compressed verbs against the LIVE executable steps. This is what makes "a receipt binds the
WHOLE post-state" (guarantee C) a constructive fact rather than a per-field inference: every executor
field has a universal address, and the boundary commitment is the sorted-map / MMR root of those cells.
The receipt-index domain rides the SAME MMR (`index_boundary_mroot_derived`), which is exactly the index
that DISCHARGES the §149 Receipt PI-binding hypothesis (`argus_published_index_pins_receipt`): the
cross-AIR root equality the Receipt apex once carried is now an MMR opening under the named CR floor.
This is the verified surface the rotation's relayout will bind in-circuit per turn; today it is bound by
the kernel theorems, scheme-pinned to the deployed `circuit::heap_root` / MMR layout.

THE EPOCH §5 deployment-correspondence legs are CLOSED on the deployed chain (these rode the
commitment `v5 → v6` bump): the Rust value model is a SIGNED well — `dregg_cell::CellState.balance`
is `i64`, encoded at every commitment/wire boundary as the biased two-limb LE encoding
(`balance_limbs` / `encode_balance_le`), matching the Lean kernel that already ran signed wells
(`reachable_total_zero`); value ENTERS only by genesis issuer-moves — `node::genesis::GenesisMove`
replays from an issuer well seeded `−total_issued`, so no balance is conjured (the W1
guarantee-B conservation gap that genesis previously punched is gone); and fees are MOVES, not
burns — `TurnExecutor::fee_well_cell` / `set_fee_well_cell` route the fee remainder to a fee well
that starts at zero and accumulates (`finalize.rs`, "fees as moves"), so the per-turn balance sum
is exactly neutral over the deployed executor. Guarantee B (conservation) therefore holds over the
deployed chain, not only the abstract kernel; the two conservation deployment caveats named under
guarantee B are discharged.

The remaining rotation legs ride ONE further VK/commitment epoch together (the descriptor IR-v2
flag-day, `docs/EPOCH-DESIGN.md`): registers 8→16 with the `FactoryDescriptor` fields declaration
· the `heap_root` register + PI v3 (committed-height column + rateBound/challengeWindow caveat tags)
· the RESERVED deletion + 54→29 selector compaction (the 186-column layout dies; the post-LogUp
main table is far thinner, so the 159 target is obsolete) · the descriptor IR-v2 regeneration
(`Dregg2.Circuit.DescriptorIR2.emitVmJson2` over the v2 registry → `circuit/descriptors/*.json` +
fingerprints, driving the multi-table batch-STARK interpreter `circuit::descriptor_ir2`). The
interpreter is authored and feature-gated (`recursion`); it does NOT yet sit on the live proving
path, which still rides the v1 `effect_vm_descriptors` registry through `lean_descriptor_air` /
`effect_vm_p3_full_air`. The IR-v2 emission + VK bump are deferred to that flag-day because pulling
them before the register relayout lands would orphan the live v1 path against unread v2-wire JSON.
=========================================================================== -/

/-! ===========================================================================
## Axiom-hygiene coverage note

This file is the *reading* artifact: it pins the FIVE guarantee apexes and the keystones
that directly discharge them, organized BY GUARANTEE. It deliberately imports only the
specific keystone modules each guarantee references (not the root `Dregg2`, which would be a
circular import since the root imports this file), so it is NOT — and is not intended to be —
the corpus-wide axiom-hygiene net.

The comprehensive corpus-wide `#assert_axioms` net (every keystone the corpus advertises,
re-pinned transitively through the root `Dregg2`) lives in `Dregg2.Claims`, which imports the
root and therefore can pin keystones in modules this file does not import. `Dregg2.Claims` is
RETIRED as a chronological journal (it is no longer the assurance artifact — this file is) but
RETAINED as that whole-corpus CI pin-net: its ~190 pins are the unique location of those
per-keystone kernel-clean certifications. Retiring it to a doc-only stub would silently drop
that coverage, so it is kept as a pure pin-ledger and re-headed to point here.

Division of labor:
  * **This file (`AssuranceCase`)** — the load-bearing assurance APEX, by guarantee. The five
    guarantee aggregations + their direct-DAG keystones, kernel-triple clean.
  * **`Claims`** — the comprehensive per-keystone CI net (corpus-wide), subordinate to this file.
  * **`scripts/axiom-hygiene-guard.sh`** — the textual whole-corpus open-hole grep.
=========================================================================== -/

end Dregg2.AssuranceCase
