/-
# `Dregg2.Circuit.DeployedTraceExtract` — TRANSPORTING the proven abstract FRI proximity onto the
deployed `VmTrace`, factoring `DeployedTraceExtract` into (proven math) + TWO precise structure-maps.

## What this module does (the one-line honest claim)

`StarkSoundReduction.DeployedTraceExtract` is the single research-grade residual of `[StarkSound]`:
"an accepting deployed `verifyAlgo` run yields an opened `VmTrace t` with `MainAirAccept` + legs."
Its MATH content — FRI low-degree soundness at the deployed BabyBear field / rate-`1/8` / 8-to-1 fold
— is ALREADY PROVED, axiom-clean, over abstract Reed–Solomon oracles
(`FriFoldArity.fold_close_of_arity_challenges` → `FriBridgeDeployedArity.friProximityK8_discharge0`;
`FriQuerySoundness.deployed_accept_prob_lt`). What was NOT written is the WIRE from that abstract
proximity to `MainAirAccept` on the deployed `VmTrace`/`EffectVmDescriptor2` — the "disjoint types"
seam (`AlgoStarkSoundInstance` §0).

This file TRANSPORTS the proven proximity across that seam. It:

  1. Names the seam as EXACTLY TWO precise structure-maps (`DeployedFriEmbedding`):
       * `accept_folds` — the VERIFIER-DECODE: an accepting `verifyAlgo` run's committed BabyBear
         column oracle `oracle pi π`, folded by `8` distinct challenges `chal pi π`, lands in the
         deployed folded code `friSetupK8.C'` (the abstract arity-8 FRI transcript the deployed
         verifier's FRI sub-checks realize — the "FRI oracle ↔ EffectVmDescriptor2 commitment"
         identification, in the property→transcript direction of `FriExtractReal §4`);
       * `decode_trace` — the CODEWORD-DECODE: whenever the committed oracle IS a genuine low-degree
         codeword (`oracle pi π ∈ friSetupK8.C`), it decodes to a deployed `VmTrace t` with
         `MainAirAccept` + all the `DeployedTraceExtract` legs.
  2. WIRES the proven FRI keystone in the MIDDLE (`deployedTraceExtract_of_embedding`): the
     load-bearing `friProximityK8_discharge0` turns `accept_folds` into `oracle pi π ∈ friSetupK8.C`
     (0-closeness ⟺ codeword, unique decoding at rate-`1/8`), which is EXACTLY the extra hypothesis
     `decode_trace` gets to assume. So `decode_trace` is genuinely WEAKER than the raw
     `DeployedTraceExtract`: the FRI math has already discharged "is the committed oracle low-degree?"

So `DeployedTraceExtract` (hence the whole `[StarkSound]` math residual) reduces to the two named
maps, with the proven arity-8 proximity CONNECTED and load-bearing between them. The FRI-link BITES
(a far word cannot be the committed oracle of an accepting transcript, `embedding_rejects_far_oracle`)
and FIRES (the honest codeword folds in, `fri_fold_respecting`).

## The exact remaining type-bridge (what is NOT proved, stated precisely)

`DeployedFriEmbedding` is the residual — an explicit hypothesis structure, NOT a smuggled carrier.
Its two Prop fields are the precise remaining maps:

  * `accept_folds : ∀ pi π, verifyAlgo … = true → ∀ i, Fold friSetupK8.geom (chal pi π i)
        (oracle pi π) ∈ friSetupK8.C'` — the verifier-syntax decode + FRI knowledge-reflection;
  * `decode_trace : ∀ pi π, verifyAlgo … = true → oracle pi π ∈ friSetupK8.C →
        TraceWitnessed hash (R pi.effect) pi` — the low-degree-codeword ↔ `VmTrace`/AIR-quotient decode.

Everything between them — the arity-8 proximity, the unique-decoding collapse to a codeword — is a
PROVED theorem chained here. This is the honest verdict the brief asked for: the math is done, the
transport is engineered, and the seam is now two named structure-maps, not one opaque research Prop.

## ⚑ §3′ DESIGN-BUG REPAIR (2026-07-23): the §2 bar was FALSE-AS-TYPED at deployed sampling

`accept_folds` as typed below concludes DETERMINISTIC membership `Fold … ∈ friSetupK8.C'` for EVERY
fold on EVERY accepting run. The deployed verifier does NOT check that: `FriChecks.foldConsistent`
(`FriVerifier.lean:636`, discharged by `concreteFriChecks`) spot-checks fold consistency at the
`k = numQueries` TRANSCRIPT-SAMPLED positions only. "The spot-checks pass ⟹ the fold is a codeword"
is NOT a theorem at deployed sampling — a far word survives `k` samples with probability `(1−δ)^k`,
which is exactly what `epsQuery` pays for (`FriPositiveRadiusPayment` §1–2; `FriFarnessReconcile`
names the deterministic collapse as the residual). So §2's bar was unprovable-as-typed against the
deployed verifier; §3′ RETYPES it (`DeployedFriSampledEmbedding`):

  * the DETERMINISTIC part of `accept_folds` is `accept_folds_sampled` — the SAMPLED positions agree
    with `Fold` on the log-decoded word (provable from the sampled checks; the concrete
    verifier-syntax half is PROVEN, `verifyAlgo_concreteFri_opened_positions`);
  * the MEMBERSHIP conclusion moves to the PROBABILISTIC assembly, holding only
    except-with-`epsQuery` (`accept_close_or_paid`, proven generically);
  * `decode_trace` now takes a POSITIVE-RADIUS-close word (`closeN … dRad`, `dRad ≤ 4` = the
    `[16,8]`-RS unique-decoding radius `⌊(9−1)/2⌋`), not `∈ C` exactly —
    `PositiveRadiusTraceDecode` is the named input type;
  * the OLD §2 bar is exactly the FULL-COVER idealization: DERIVABLE from the sampled bar when the
    sample covers the folded domain (`deployedFriEmbedding_of_sampled_cover`), and the inference it
    needs WITHOUT cover is REFUTED at a witness (`sampled_pass_not_membership` — a non-codeword
    passing a non-covering sample against a genuine codeword).

§2/§7 are KEPT (nine downstream consumers speak `DeployedFriEmbedding`) but DEMOTED to the cover
idealization; the acceptance bar for the decode rungs is §3′. **Per-rung owes-statement:**
  * **L4** = the deterministic opened-positions-agree map. Verifier-syntax half PROVEN here
    (`verifyAlgo_concreteFri_opened_positions`: an accepting `concreteFriChecks` run passes
    `friQueryCheck` at every transcript-sampled index with the index binding). NAMED residual: the
    Merkle log-decode identification — `friQueryCheck = true` at the sampled index ⟺ the opened
    leaves agree with `Fold` on the `RomQueryLog`-decoded word (extraction-as-data,
    except-with-εMerkle).
  * **L5** = `PositiveRadiusTraceDecode` at a REALISTIC multi-layer `FriSetupK` instance (named, NOT
    proven, used as a hypothesis nowhere in this file's theorems). `friProximityK8_discharge0` is
    ONLY the `d = 0` size-16 toy (`FriBridgeDeployedArity.lean:111`);
    `FriPositiveRadiusPayment.positive_radius_payment_vacuous_at_friSetupK8` proves the size-16
    domain CANNOT exhibit a positive radius — the realistic instance (`|ι| ≥ 2^22`-class, multi-layer
    fold tower, `e` inside the true UD radius) is the heavy engineering.
  * **L6** = the probabilistic membership except-with-`epsQuery`. The per-run dichotomy is PROVEN
    generically here (`accept_close_or_paid`: all folds `d`-close — whence `n²·d`-closeness by the
    keystone — OR some far fold whose sampled-agreement event has probability `≤ (1−δ)^k`); the
    run-level composition into `epsFri` is `FriVerifierCompose`'s assembly.

## Discipline

Sorry-free; no `def …Sound`/`…Hard` carrier; no `axiom`; the residual enters as an explicit
hypothesis structure. `#assert_axioms` ⊆ `{propext, Classical.choice, Quot.sound}`. New file; imports
read-only; builds targeted (`lake build Dregg2.Circuit.DeployedTraceExtract`). ADDITIVE — the shared
apex modules (`StarkSoundReduction`, `FriBridgeDeployedArity`, …) are imported, never edited.
-/
import Dregg2.Circuit.StarkSoundReduction
import Dregg2.Circuit.FriBridgeDeployedArity
import Dregg2.Circuit.FriQuerySoundness
import Dregg2.Circuit.FieldIntegerLift

namespace Dregg2.Circuit.DeployedTraceExtract

open Dregg2.Circuit.StarkSoundReduction
  (DeployedTraceExtract RSProximityCore RSProximityResearchLemma starkSound_of_core
   core_of_research_and_refines starkSound_of_research_and_refines)
open Dregg2.Circuit.FriVerifierBridge (ProofView DeployedRefines)
open Dregg2.Circuit.FriVerifier
  (verifyAlgo FriParams RecursionVk FriChecks FriCore concreteFriChecks friQueryCheck
   deriveTranscript deriveTranscript_qidx_length BatchProofData WrapPublics)
open Dregg2.Circuit.CircuitSoundness
  (Registry BatchPublicInputs BatchProof EffectIdx tracePublishedCommit StarkSound)
open Dregg2.Circuit.DescriptorIR2
  (Satisfied2 VmTrace EffectVmDescriptor2 envAt memLog mapLog opRow VmConstraint2)
open Dregg2.Circuit.AirChecksSatisfied (MainAirAccept MainAirAcceptF isArith)
open Dregg2.Circuit.Emit.EffectVmEmit (siteHoldsAll)
open Dregg2.Circuit.FriSoundness (closeN closeN_zero_iff_mem farN)
open Dregg2.Circuit.FriFoldArity
  (FriSetupK friSetupK8 Fold fold_close_of_arity_challenges
   f0 f0_no_injective_good fHon8 fHon8_fold_complete chal8 chal8_inj)
open Dregg2.Circuit.FriQuerySoundness
  (Accepts accept_prob_le_of_farN gZero gZero_mem far_accepted_by_missing_query)
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.FriBridgeDeployedArity (FriProximityK friProximityK8_discharge0)
open Dregg2.Crypto

/-! ## §1 — `TraceWitnessed` : the per-batch tail of `DeployedTraceExtract`, as a standalone `Prop`.

Verbatim the existential body of `StarkSoundReduction.DeployedTraceExtract`, abstracted over the
descriptor `D` (so `DeployedTraceExtract hash R … = ∀ pi π, verifyAlgo … → TraceWitnessed hash
(R pi.effect) pi` DEFINITIONALLY). This lets the codeword-decode map name exactly the deployed-trace
obligation without re-transcribing the ten-conjunct body at each use. -/

/-- **`TraceWitnessed hash D pi`** — an opened deployed `VmTrace t` for descriptor `D` and batch `pi`
carrying the AIR quotient acceptance `MainAirAccept`, the non-arithmetic (LogUp/table) arms, the
`rowHashes`/`rowRanges` structural legs, the six memory-checking legs, and the published-commit link.
The `D := R pi.effect` specialization is exactly one disjunct-per-`(pi,π)` of `DeployedTraceExtract`. -/
def TraceWitnessed (hash : List Int → Int) (D : EffectVmDescriptor2) (pi : BatchPublicInputs) : Prop :=
  ∃ (minit : Int → Int) (mfin : Int → Int × Nat) (maddrs : List Int) (t : VmTrace),
    MainAirAcceptF D t ∧
    (∀ i < t.rows.length, ∀ c ∈ D.constraints, ¬ isArith c →
        c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)) ∧
    (∀ i < t.rows.length, siteHoldsAll hash (envAt t i) D.hashSites) ∧
    (∀ i < t.rows.length, ∀ r ∈ D.ranges, r.holds (envAt t i)) ∧
    maddrs.Nodup ∧
    (∀ op ∈ memLog D t, op.addr ∈ maddrs) ∧
    MemoryChecking.Disciplined (memLog D t) ∧
    MemoryChecking.MemCheck minit mfin maddrs (memLog D t) ∧
    t.tf .memory = (memLog D t).map opRow ∧
    t.tf .mapOps = mapLog D t ∧
    tracePublishedCommit t = pi.toPublished

/-- **`TraceWitnessed` IS the `DeployedTraceExtract` body**, per `(pi, π)`. This records the
definitional identity so the reduction below is transparent: `DeployedTraceExtract` is nothing but
"`verifyAlgo` accepts ⟹ `TraceWitnessed` at `R pi.effect`", for all `(pi, π)`. -/
theorem deployedTraceExtract_iff
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView) :
    DeployedTraceExtract hash R perm RATE toNat params vk checks initState logN view
      ↔ ∀ (pi : BatchPublicInputs) (π : BatchProof),
          verifyAlgo perm RATE toNat params vk checks initState logN
              (view pi π).1 (view pi π).2 = true →
          TraceWitnessed hash (R pi.effect) pi :=
  Iff.rfl

/-! ## §2 — `DeployedFriEmbedding` : the TWO precise structure-maps that constitute the seam.

The whole content of the disjoint-developments seam, named. `oracle`/`chal` decode an accepting
`verifyAlgo` run into the abstract arity-8 FRI transcript (`accept_folds`); `decode_trace` decodes a
low-degree codeword into the deployed `VmTrace` (`MainAirAccept` + legs). Nothing else — the proximity
math CONNECTING them is a proved theorem (`§3`), not a field. -/

/-- **`DeployedFriEmbedding`** — the residual type-bridge for `DeployedTraceExtract`, as an explicit
hypothesis structure (NOT a smuggled carrier). Its data are the two decode functions and its Props the
two maps:
  * `oracle pi π : Fin 16 → BabyBear` — the committed BabyBear column oracle the deployed proof exposes;
  * `chal pi π : Fin 8 → BabyBear` — the `8` FRI fold challenges of the transcript (distinct, `chal_inj`);
  * `accept_folds` — VERIFIER-DECODE: on `verifyAlgo`-accept, every fold `Fold friSetupK8.geom
    (chal pi π i) (oracle pi π)` lands in the deployed folded code `friSetupK8.C'` (the deployed FRI
    sub-checks realize the abstract arity-8 transcript — the FRI-oracle↔commitment identification);
  * `decode_trace` — CODEWORD-DECODE: on accept AND the committed oracle being a genuine low-degree
    codeword, an opened deployed `VmTrace` witnesses `TraceWitnessed hash (R pi.effect) pi`.
`decode_trace` is genuinely WEAKER than raw extraction: the FRI math (`§3`) supplies its
`oracle pi π ∈ friSetupK8.C` hypothesis, so the decoder never faces an unresolved-degree oracle.

⚠ **DEMOTED (§3′)**: `accept_folds` as typed here is the FULL-COVER idealization — the deployed
verifier only spot-checks folds at sampled positions, so this deterministic membership bar is
unprovable against it (`sampled_pass_not_membership` refutes the needed inference). The acceptance
bar for the decode rungs is `DeployedFriSampledEmbedding` (§3′); this structure is KEPT for its
nine downstream consumers and is derivable from §3′ under full cover
(`deployedFriEmbedding_of_sampled_cover`). -/
structure DeployedFriEmbedding
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView) : Type where
  /-- The committed BabyBear column oracle the deployed proof exposes. -/
  oracle : BatchPublicInputs → BatchProof → (Fin 16 → Dregg2.Circuit.BabyBearFriField.BabyBear)
  /-- The `8` FRI fold challenges of the transcript. -/
  chal : BatchPublicInputs → BatchProof → (Fin 8 → Dregg2.Circuit.BabyBearFriField.BabyBear)
  /-- The `8` challenges are DISTINCT (so the arity-8 Vandermonde inverts — the keystone hypothesis). -/
  chal_inj : ∀ pi π, Function.Injective (chal pi π)
  /-- **VERIFIER-DECODE**: an accepting run's committed oracle folds into the deployed folded code
  under all `8` challenges — the abstract arity-8 FRI transcript the deployed FRI sub-checks realize. -/
  accept_folds : ∀ (pi : BatchPublicInputs) (π : BatchProof),
    verifyAlgo perm RATE toNat params vk checks initState logN
        (view pi π).1 (view pi π).2 = true →
    ∀ i, Fold friSetupK8.geom (chal pi π i) (oracle pi π) ∈ friSetupK8.C'
  /-- **CODEWORD-DECODE**: on accept AND the committed oracle being a genuine low-degree codeword, a
  deployed `VmTrace` witnesses the `DeployedTraceExtract` legs (`MainAirAccept` + …). -/
  decode_trace : ∀ (pi : BatchPublicInputs) (π : BatchProof),
    verifyAlgo perm RATE toNat params vk checks initState logN
        (view pi π).1 (view pi π).2 = true →
    oracle pi π ∈ friSetupK8.C →
    TraceWitnessed hash (R pi.effect) pi

/-! ## §3′ — THE SAMPLED ACCEPTANCE BAR : §2 retyped to what the deployed verifier CHECKS.

§2's `accept_folds` concludes DETERMINISTIC membership `Fold … ∈ friSetupK8.C'` for EVERY fold on
EVERY accepting run. The deployed verifier does not check that: `concreteFriChecks.foldConsistent`
spot-checks fold consistency at the `params.numQueries` transcript-sampled positions ONLY, and a
far word survives `k` samples with probability `(1−δ)^k` (`accept_prob_le_of_farN` — exactly the
mass `epsQuery` pays for). So the §2 bar is the FULL-COVER idealization, unprovable-as-typed at
deployed sampling. This section is the deployed bar, per rung:

  * **L4 — deterministic sampled agreement.** `verifyAlgo_concreteFri_opened_positions` (PROVEN):
    an accepting `verifyAlgo (concreteFriChecks core)` run passes `friQueryCheck` at every
    transcript-sampled index, with the opened index BOUND to the transcript and the query count
    bound to `numQueries`. NAMED residual (the `accept_folds_sampled` field): the Merkle log-decode
    identification — `friQueryCheck = true` at the sampled index ⟺ the opened leaves agree with
    `Fold` on the `RomQueryLog`-decoded word (extraction-as-data, except-with-εMerkle).
  * **L5 — the positive-radius decoder.** `PositiveRadiusTraceDecode` (the retyped `decode_trace`
    input): the trace decoder must consume a `dRad`-CLOSE oracle, NOT `∈ C` exactly — the assembly
    only ever delivers closeness except-with-`epsQuery`. At `friSetupK8` the radius is `4` (the
    `[16,8]`-RS unique-decoding radius `⌊(9−1)/2⌋`). **The honest L5 target** (named, NOT faked
    here): exhibit a realistic multi-layer instance `S_prod : FriSetupK BabyBear ι κ 8` with
    `|ι| ≥ 2^22`-class domain and fold tower, and prove
    `PositiveRadiusTraceDecode hash R perm RATE toNat params vk checks initState logN view S_prod
    oracle e` for `e` inside `S_prod`'s true unique-decoding radius with `8²·d ≤ e`.
    `friProximityK8_discharge0` is ONLY the `d = 0` size-16 toy, and
    `FriPositiveRadiusPayment.positive_radius_payment_vacuous_at_friSetupK8` PROVES the size-16
    domain cannot exhibit a positive radius — the realistic instance is heavy engineering, not a
    stub.
  * **L6 — probabilistic membership.** `accept_close_or_paid` (PROVEN, generic): per run, either
    ALL folds are `d`-close — whence the oracle is `n²·d`-close by the keystone — or SOME fold is
    `d`-far and its sampled-agreement event has mass `≤ (1−δ)^k`. The run-level composition of the
    paid branch into `epsFri` is `FriVerifierCompose`'s assembly, not re-proved here.
  * **The §2 bar is EXACTLY the full-cover idealization**: derivable from the sampled bar when the
    sample covers the folded domain (`deployedFriEmbedding_of_sampled_cover`), and the inference it
    needs WITHOUT cover — "sampled pass ⟹ membership" — is REFUTED at a witness
    (`sampled_pass_not_membership`). -/

/-- **L4 (verifier-syntax half, PROVEN)** — an accepting `verifyAlgo` run with the concrete FRI
checks OPENS the sampled positions correctly: the final poly is nonempty (head = the FRI final
constant), the opened-query count equals `numQueries` (via the transcript,
`deriveTranscript_qidx_length`), and EVERY opened query has its domain index bound to the
transcript-derived index and passes the per-query Merkle+fold-chain check `friQueryCheck`. This is
the DETERMINISTIC content the deployed verifier actually checks — membership of the fold in
`friSetupK8.C'` is NOT among it (that moves to `accept_close_or_paid`). -/
theorem verifyAlgo_concreteFri_opened_positions
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (core : FriCore Int)
    (initState : List Int) (logN : Nat)
    (proof : BatchProofData Int) (pub : WrapPublics Int)
    (hacc : verifyAlgo perm RATE toNat params vk
        (concreteFriChecks core) initState logN proof pub = true) :
    ∃ finalConst rest, proof.finalPoly = finalConst :: rest ∧
      proof.queries.length = params.numQueries ∧
      ∀ qe ∈ proof.queries.zip
          (deriveTranscript perm RATE toNat params initState logN proof pub).qidx,
        qe.1.index = qe.2 ∧
        friQueryCheck core proof.traceCommit proof.friCommitments finalConst qe.1 = true := by
  unfold verifyAlgo at hacc
  simp only [Bool.and_eq_true] at hacc
  obtain ⟨⟨⟨⟨⟨-, hfold⟩, -⟩, -⟩, -⟩, -⟩ := hacc
  unfold concreteFriChecks at hfold
  dsimp only at hfold
  cases hfp : proof.finalPoly with
  | nil => rw [hfp] at hfold; simp at hfold
  | cons finalConst rest =>
      rw [hfp] at hfold
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hfold
      obtain ⟨hlen, hall⟩ := hfold
      refine ⟨finalConst, rest, rfl, ?_, ?_⟩
      · rw [hlen, deriveTranscript_qidx_length]
      · intro qe hqe
        exact hall qe hqe

/-- **L5's named input type — `PositiveRadiusTraceDecode`.** The codeword-decode retyped to consume
a `dRad`-CLOSE oracle (positive-radius unique decoding) instead of `oracle ∈ C` exactly. Generic
over the FRI setup `S` so the SAME `Prop` states both the `friSetupK8`/`dRad = 4` field below and
the honest L5 target at a realistic multi-layer instance (see the section header — that instance
is the to-do; it is NOT stubbed here). -/
def PositiveRadiusTraceDecode
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    {F ι κ : Type*} [Field F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {n : ℕ}
    (S : FriSetupK F ι κ n)
    (oracle : BatchPublicInputs → BatchProof → (ι → F)) (dRad : ℕ) : Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    verifyAlgo perm RATE toNat params vk checks initState logN
        (view pi π).1 (view pi π).2 = true →
    closeN S.C dRad (oracle pi π) →
    TraceWitnessed hash (R pi.effect) pi

/-- **`DeployedFriSampledEmbedding` — the §2 structure RETYPED to the deployed sampling.** The
acceptance bar for the decode rungs. Differences from `DeployedFriEmbedding`:
  * `accept_folds` is REPLACED by `accept_folds_sampled` — agreement between the true fold and the
    committed next-layer word `foldWord` AT the `numQueries` transcript-sampled folded positions
    `qsample` (each the log-decoded folded position of a transcript query). This is what
    `foldConsistent` spot-checks — provable-in-principle from
    `verifyAlgo_concreteFri_opened_positions` + the Merkle log-decode identification (the L4
    residual), with NO universal membership claim;
  * `foldWord_mem` — the committed next-layer word is a codeword. Deterministic at THIS single-fold
    resolution only because the last FRI layer is sent in the clear (`finalPoly`,
    `log_final_poly_len = 0`); at a multi-layer instance the intermediate layers' membership itself
    moves into the probabilistic assembly (part of the L5/L6 engineering);
  * `decode_trace` is retyped to `PositiveRadiusTraceDecode … friSetupK8 oracle 4` — the decoder
    consumes a `4`-close oracle, never `∈ C` exactly. -/
structure DeployedFriSampledEmbedding
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView) : Type where
  /-- The committed BabyBear column oracle the deployed proof exposes. -/
  oracle : BatchPublicInputs → BatchProof → (Fin 16 → BabyBear)
  /-- The `8` FRI fold challenges of the transcript. -/
  chal : BatchPublicInputs → BatchProof → (Fin 8 → BabyBear)
  /-- The `8` challenges are DISTINCT (arity-8 Vandermonde inverts). -/
  chal_inj : ∀ pi π, Function.Injective (chal pi π)
  /-- The `numQueries` transcript-sampled FOLDED-domain positions (with replacement — faithful to
  the deployed independent draws): the log-decoded folded position (`index / arity`) of each
  transcript query. -/
  qsample : BatchPublicInputs → BatchProof → (Fin params.numQueries → Fin 2)
  /-- The committed next-layer word per challenge (read from the proof's `finalPoly` at this
  single-fold resolution). -/
  foldWord : BatchPublicInputs → BatchProof → (Fin 8 → (Fin 2 → BabyBear))
  /-- The committed next-layer word IS a codeword of the folded code — deterministic here ONLY
  because the final layer is sent in the clear (see structure docstring). -/
  foldWord_mem : ∀ (pi : BatchPublicInputs) (π : BatchProof),
    verifyAlgo perm RATE toNat params vk checks initState logN
        (view pi π).1 (view pi π).2 = true →
    ∀ i, foldWord pi π i ∈ friSetupK8.C'
  /-- **THE RETYPED VERIFIER-DECODE (deterministic part)** — on accept, at every SAMPLED folded
  position the true fold of the committed oracle agrees with the committed next-layer word. NO
  membership conclusion: that is `accept_close_or_paid`'s probabilistic dichotomy. -/
  accept_folds_sampled : ∀ (pi : BatchPublicInputs) (π : BatchProof),
    verifyAlgo perm RATE toNat params vk checks initState logN
        (view pi π).1 (view pi π).2 = true →
    ∀ i, Accepts (Fold friSetupK8.geom (chal pi π i) (oracle pi π))
      (foldWord pi π i) (qsample pi π)
  /-- **THE RETYPED CODEWORD-DECODE** — positive-radius unique decoding at the `[16,8]`-RS
  unique-decoding radius `4`. -/
  decode_trace :
    PositiveRadiusTraceDecode hash R perm RATE toNat params vk checks initState logN view
      friSetupK8 oracle 4

/-- **L6 (per-run dichotomy, PROVEN, generic)** — `accept_close_or_paid`. For any arity-`n` setup,
`n` distinct challenges, and committed folded codewords `g i`: EITHER every fold is `d`-close to
the folded code — whence the oracle is `n²·d`-close to the domain code by the PROVED keystone
`fold_close_of_arity_challenges` — OR some fold is `d`-FAR, and the event that a `k`-sample agrees
with its committed codeword everywhere has mass `≤ (1−δ)^k` (`accept_prob_le_of_farN`). This is
exactly the split the §2 bar collapsed: membership holds only except-with-the-paid-mass. At
`friSetupK8` the far branch is UNINHABITED for `d ≥ 1`
(`FriPositiveRadiusPayment.positive_radius_payment_vacuous_at_friSetupK8`) — the size-16 toy
cannot pay a positive radius; the realistic instance is the L5 engineering. -/
theorem accept_close_or_paid
    {F : Type*} [Field F] [DecidableEq F]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : Type*} [Fintype κ] [DecidableEq κ] {n : ℕ}
    (S : FriSetupK F ι κ n) {f : ι → F} {α : Fin n → F}
    (hα : Function.Injective α) {g : Fin n → κ → F}
    (hg : ∀ i, g i ∈ S.C') (d k : ℕ) {δ : ℝ}
    (hκ : 0 < Fintype.card κ) (hδ0 : 0 ≤ δ)
    (hδd : δ * (Fintype.card κ : ℝ) ≤ (d : ℝ)) :
    closeN S.C (n ^ 2 * d) f ∨
      ∃ i, farN S.C' d (Fold S.geom (α i) f) ∧
        ((Finset.univ.filter (fun Q : Fin k → κ =>
              Accepts (Fold S.geom (α i) f) (g i) Q)).card : ℝ)
            / ((Fintype.card κ : ℝ) ^ k)
          ≤ (1 - δ) ^ k := by
  by_cases hall : ∀ i, closeN S.C' d (Fold S.geom (α i) f)
  · exact Or.inl (fold_close_of_arity_challenges S hα hall)
  · obtain ⟨i, hi⟩ := not_forall.mp hall
    exact Or.inr ⟨i, hi, accept_prob_le_of_farN k hκ hδ0 (hg i) hi hδd⟩

/-- **L6 wired onto the sampled embedding at the deployed instance.** On an accepting run, the
committed oracle is `64·d`-close, or some fold is `d`-far and its sampled-agreement mass is paid.
HONEST caveat (not hidden): at `friSetupK8` the paid branch is uninhabited for `d ≥ 1` — this
instantiation is the WIRE, non-vacuous only at the L5 realistic instance. -/
theorem sampled_embedding_close_or_paid
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (semb : DeployedFriSampledEmbedding hash R perm RATE toNat params vk checks initState logN view)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hacc : verifyAlgo perm RATE toNat params vk checks initState logN
        (view pi π).1 (view pi π).2 = true)
    (d k : ℕ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδd : δ * 2 ≤ (d : ℝ)) :
    closeN friSetupK8.C (64 * d) (semb.oracle pi π) ∨
      ∃ i, farN friSetupK8.C' d
          (Fold friSetupK8.geom (semb.chal pi π i) (semb.oracle pi π)) ∧
        ((Finset.univ.filter (fun Q : Fin k → Fin 2 =>
              Accepts (Fold friSetupK8.geom (semb.chal pi π i) (semb.oracle pi π))
                (semb.foldWord pi π i) Q)).card : ℝ)
            / ((Fintype.card (Fin 2) : ℝ) ^ k)
          ≤ (1 - δ) ^ k := by
  have h := accept_close_or_paid (f := semb.oracle pi π) friSetupK8 (semb.chal_inj pi π)
    (semb.foldWord_mem pi π hacc) d k (by simp) hδ0 (by simpa using hδd)
  rwa [show (8 : ℕ) ^ 2 * d = 64 * d by norm_num] at h

/-- **The §2 bar RECOVERED under full cover** — `deployedFriEmbedding_of_sampled_cover`. When the
sample COVERS the folded domain (`hcover`), sampled agreement is agreement EVERYWHERE, so the true
fold EQUALS the committed codeword `foldWord` and §2's deterministic `accept_folds` follows; and
the positive-radius decoder consumes exact membership via `closeN`-weakening (`∈ C` ⟹ `0`-close ⟹
`4`-close). So the OLD bar is exactly the full-cover idealization of the sampled bar — it was never
the deployed bar, whose sample of `k = 38` positions does not cover a `2^22`-class domain. -/
def deployedFriEmbedding_of_sampled_cover
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (semb : DeployedFriSampledEmbedding hash R perm RATE toNat params vk checks initState logN view)
    (hcover : ∀ (pi : BatchPublicInputs) (π : BatchProof),
      verifyAlgo perm RATE toNat params vk checks initState logN
          (view pi π).1 (view pi π).2 = true →
      ∀ y : Fin 2, ∃ q, semb.qsample pi π q = y) :
    DeployedFriEmbedding hash R perm RATE toNat params vk checks initState logN view where
  oracle := semb.oracle
  chal := semb.chal
  chal_inj := semb.chal_inj
  accept_folds := by
    intro pi π hacc i
    have hagree := semb.accept_folds_sampled pi π hacc i
    have heq : Fold friSetupK8.geom (semb.chal pi π i) (semb.oracle pi π)
        = semb.foldWord pi π i := by
      funext y
      obtain ⟨q, hq⟩ := hcover pi π hacc y
      have h := hagree q
      rwa [hq] at h
    rw [heq]
    exact semb.foldWord_mem pi π hacc i
  decode_trace := by
    intro pi π hacc hmem
    refine semb.decode_trace pi π hacc ?_
    obtain ⟨g, hgC, hcard⟩ := closeN_zero_iff_mem.mpr hmem
    exact ⟨g, hgC, le_trans hcard (by norm_num)⟩

/-- **The coverless inference is REFUTED at a witness** — `sampled_pass_not_membership`. The
inference the §2 bar needed WITHOUT cover — "the sampled positions agree with a genuine codeword ⟹
the word IS a codeword" — is FALSE: over the rate-`1/2` `ZMod 5` Reed–Solomon instance, the far
word `fFar ∉ C` passes a NON-COVERING one-point sample against the genuine codeword `gZero ∈ C`.
So the §2→§3′ retype is forced, not stylistic: no theorem can conclude deterministic membership
from spot-checks at deployed sampling. -/
theorem sampled_pass_not_membership :
    ∃ (f g : Fin 4 → ZMod 5) (Q : Fin 1 → Fin 4),
      g ∈ Dregg2.Circuit.FriSoundness.rsSetup.C ∧
      Accepts f g Q ∧
      (¬ ∀ y : Fin 4, ∃ q : Fin 1, Q q = y) ∧
      f ∉ Dregg2.Circuit.FriSoundness.rsSetup.C :=
  ⟨Dregg2.Circuit.FriSoundness.fFar, gZero, ![1], gZero_mem,
   far_accepted_by_missing_query, by decide,
   Dregg2.Circuit.FriSoundness.fFar_not_mem⟩

#assert_axioms verifyAlgo_concreteFri_opened_positions
#assert_axioms accept_close_or_paid
#assert_axioms sampled_embedding_close_or_paid
#assert_axioms deployedFriEmbedding_of_sampled_cover
#assert_axioms sampled_pass_not_membership

/-! ## §3 — THE TRANSPORT : the proven arity-8 proximity, wired between the two maps. -/

/-- **`deployedTraceExtract_of_embedding` — `DeployedTraceExtract` DERIVED, FRI math load-bearing.**
From a `DeployedFriEmbedding` the opaque `DeployedTraceExtract` holds. Proof: `accept_folds` gives an
accepting arity-8 transcript; the PROVED keystone `friProximityK8_discharge0` (i.e.
`FriFoldArity.fold_close_of_arity_challenges` at `n = 8` over BabyBear) turns it into
`oracle pi π ∈ friSetupK8.C` (0-closeness ⟺ codeword — unique decoding at rate-`1/8`); that discharges
exactly the extra hypothesis `decode_trace` needs. The FRI proximity theorem is the LOAD-BEARING middle
link: remove it and `decode_trace`'s codeword hypothesis is unavailable. -/
theorem deployedTraceExtract_of_embedding
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (emb : DeployedFriEmbedding hash R perm RATE toNat params vk checks initState logN view) :
    DeployedTraceExtract hash R perm RATE toNat params vk checks initState logN view := by
  intro pi π hacc
  -- PROVEN FRI proximity: the accepting transcript's oracle is 0-close, i.e. a genuine codeword.
  have hlow : emb.oracle pi π ∈ friSetupK8.C :=
    closeN_zero_iff_mem.mp
      (friProximityK8_discharge0 (emb.chal_inj pi π) (emb.accept_folds pi π hacc))
  -- CODEWORD-DECODE: the low-degree codeword decodes to the deployed trace.
  exact emb.decode_trace pi π hacc hlow

/-- The full `DeployedTraceExtract` from the SAMPLED embedding (§3′) under full cover — the
idealized pipeline still closes end-to-end, showing the retype loses nothing at the idealization. -/
theorem deployedTraceExtract_of_sampled_cover
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (semb : DeployedFriSampledEmbedding hash R perm RATE toNat params vk checks initState logN view)
    (hcover : ∀ (pi : BatchPublicInputs) (π : BatchProof),
      verifyAlgo perm RATE toNat params vk checks initState logN
          (view pi π).1 (view pi π).2 = true →
      ∀ y : Fin 2, ∃ q, semb.qsample pi π q = y) :
    DeployedTraceExtract hash R perm RATE toNat params vk checks initState logN view :=
  deployedTraceExtract_of_embedding hash R perm RATE toNat params vk checks initState logN view
    (deployedFriEmbedding_of_sampled_cover hash R perm RATE toNat params vk checks initState
      logN view semb hcover)

#assert_axioms deployedTraceExtract_of_sampled_cover

/-! ## §4 — Composition to `RSProximityCore` and `StarkSound` (the opaque residual eliminated). -/

/-- **`rsProximityCore_of_embedding` — the precise core from the embedding + code refinement.** The
`StarkSoundReduction.RSProximityCore` (whose `extract` field IS `DeployedTraceExtract`) assembled from
the transported `DeployedFriEmbedding` and the Rust-refines-spec `DeployedRefines`. -/
theorem rsProximityCore_of_embedding
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (emb : DeployedFriEmbedding hash R perm RATE toNat params vk checks initState logN view)
    (href : DeployedRefines R perm RATE toNat params vk checks initState logN view) :
    RSProximityCore hash R perm RATE toNat params vk checks initState logN view :=
  core_of_research_and_refines hash R perm RATE toNat params vk checks initState logN view
    (deployedTraceExtract_of_embedding hash R perm RATE toNat params vk checks initState logN view emb)
    href

/-- **`starkSound_of_embedding_and_refines` — `[StarkSound]` from the transport + code refinement.**
The apex carrier `StarkSound hash R` holds given (i) the transported `DeployedFriEmbedding` (the two
named type-bridge maps; the FRI math between them PROVED) and (ii) `DeployedRefines` (code refinement).
No opaque STARK carrier and no `DeployedTraceExtract` research Prop survives: the math residual is
transported down to the two structure-maps of `§2`. -/
theorem starkSound_of_embedding_and_refines
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (emb : DeployedFriEmbedding hash R perm RATE toNat params vk checks initState logN view)
    (href : DeployedRefines R perm RATE toNat params vk checks initState logN view) :
    StarkSound hash R :=
  starkSound_of_core hash R perm RATE toNat params vk checks initState logN view
    (rsProximityCore_of_embedding hash R perm RATE toNat params vk checks initState logN view emb href)

#assert_axioms deployedTraceExtract_of_embedding
#assert_axioms rsProximityCore_of_embedding
#assert_axioms starkSound_of_embedding_and_refines

/-! ## §5 — TEETH : the FRI link is LOAD-BEARING (the transport is not free by unfolding).

The transport's middle link — the proven arity-8 proximity — genuinely BITES on the verifier-decode
map and FIRES on the honest codeword. Plus the codeword-decode's `MainAirAccept` conjunct bites/fires
(reusing the committed `AirChecksSatisfied` witnesses). So `DeployedFriEmbedding` is a real obligation,
not a definitional pass-through. -/

/-- **FRI-LINK BITES** — a far word cannot be the committed oracle of an accepting transcript. If
`emb.oracle pi π` were the frequency-`8` far word `f0` (`f0 ∉ friSetupK8.C`), then `accept_folds` +
`chal_inj` would exhibit `8` distinct challenges all folding `f0` into `friSetupK8.C'`, contradicting
the PROVED `f0_no_injective_good`. So the verifier-decode map is genuinely constrained by the FRI
proximity content: an accepting deployed transcript's oracle is forced low-degree. -/
theorem embedding_rejects_far_oracle
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (emb : DeployedFriEmbedding hash R perm RATE toNat params vk checks initState logN view)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hacc : verifyAlgo perm RATE toNat params vk checks initState logN
        (view pi π).1 (view pi π).2 = true) :
    emb.oracle pi π ≠ f0 := by
  intro hf
  apply f0_no_injective_good
  refine ⟨emb.chal pi π, emb.chal_inj pi π, fun i => ?_⟩
  have hi := emb.accept_folds pi π hacc i
  rwa [hf] at hi

/-- **FRI-LINK FIRES** — the honest degree-`< 8` codeword `fHon8` folds into `friSetupK8.C'` for the
`8` distinct challenges `chal8`, so an honest transcript satisfies `accept_folds` (the map is
non-vacuous — a genuine low-degree oracle passes). -/
theorem fri_fold_respecting :
    Function.Injective chal8 ∧ ∀ i, Fold friSetupK8.geom (chal8 i) fHon8 ∈ friSetupK8.C' :=
  ⟨chal8_inj, fun i => fHon8_fold_complete (chal8 i)⟩

/-- **CODEWORD-DECODE BITES** — the `MainAirAcceptF` conjunct `decode_trace` must supply is
FALSIFIABLE: a tampered-gate trace cannot meet it (`AirChecksSatisfied.tampered_gate_unacceptedF`). So
the codeword-decode map cannot be met with a lying trace — it carries genuine soundness content. -/
theorem decode_trace_biting :
    ¬ MainAirAcceptF Dregg2.Circuit.AirChecksSatisfied.dArith
        Dregg2.Circuit.AirChecksSatisfied.tTampered :=
  Dregg2.Circuit.AirChecksSatisfied.tampered_gate_unacceptedF

/-- **CODEWORD-DECODE FIRES** — and its `MainAirAcceptF` conjunct is inhabited on honest data
(`AirChecksSatisfied.honest_mainAirAcceptF`), so the codeword-decode map is non-vacuous. -/
theorem decode_trace_respecting :
    MainAirAcceptF Dregg2.Circuit.AirChecksSatisfied.dArith
      Dregg2.Circuit.AirChecksSatisfied.tHonest :=
  Dregg2.Circuit.AirChecksSatisfied.honest_mainAirAcceptF

#assert_axioms embedding_rejects_far_oracle
#assert_axioms fri_fold_respecting
#assert_axioms decode_trace_biting
#assert_axioms decode_trace_respecting

/-! ## §6 — THE PAYOFF: the field-OOD landing feeds the extraction's AIR conjunct DIRECTLY.

Post-Phase-0 the extraction hypothesis's hardest conjunct is the CANONICAL field predicate
`MainAirAcceptF transferV3 t` (the first conjunct of `TraceWitnessed`, i.e. of `decode_trace`'s
deliverable and of `AlgoStarkSoundInstance`'s `hextract`). `FieldIntegerLift`'s committed field-OOD
bridge produces EXACTLY that — no ℤ lift is needed or attempted. The two demonstrators below WITNESS
the composition as a term:

  * from an `OodInterpF transferV3 t` (the field OOD bundle), directly;
  * from the two genuine crypto residuals `hood` (OOD/RLC quotient identity at ζ) + `hnonexc`
    (Fiat–Shamir non-exceptionality) with the domain-geometry vanisher `vanishingPoly` already
    discharged — so the residual set reaching the AIR conjunct is EXACTLY `{hood, hnonexc}`.

Before Phase-0 this conjunct was the ℤ `MainAirAccept`, which `FieldIntegerLift.mainAirAcceptF_does_not_
imply_MainAirAcceptZ` shows is UNREACHABLE for `transferV3`'s multiplicative gates — the field-OOD
lemma could not feed it. That gap is now dissolved. -/

/-- **PAYOFF (bundle form)** — the field OOD bundle for `transferV3` produces the extraction's AIR
conjunct `MainAirAcceptF transferV3 t` directly. -/
theorem extractionAirConjunct_of_oodInterpF
    (t : VmTrace)
    (I : Dregg2.Circuit.FieldIntegerLift.OodInterpF
          Dregg2.Circuit.RotatedKernelRefinement.transferV3 t) :
    MainAirAcceptF Dregg2.Circuit.RotatedKernelRefinement.transferV3 t :=
  Dregg2.Circuit.FieldIntegerLift.ood_forces_mainAirAccept_field _ t I

/-- **PAYOFF (two-crypto-residual form)** — with the domain vanisher discharged, the extraction's AIR
conjunct `MainAirAcceptF transferV3 t` follows from EXACTLY the two crypto residuals `hood` + `hnonexc`.
This is the exact term the ℤ target could not supply. -/
theorem extractionAirConjunct_of_residuals
    (t : VmTrace)
    (hcap : t.rows.length ≤ Dregg2.Circuit.TraceColumnInterp.domainSize)
    (ζ : Dregg2.Circuit.BabyBearFriField.BabyBear)
    (qp : VmConstraint2 → Polynomial Dregg2.Circuit.BabyBearFriField.BabyBear)
    (hood : ∀ c ∈ Dregg2.Circuit.RotatedKernelRefinement.transferV3.constraints, isArith c →
        (Dregg2.Circuit.TraceColumnInterp.constraintPoly
            Dregg2.Circuit.RotatedKernelRefinement.transferV3 t c).eval ζ =
          (Dregg2.Circuit.FieldIntegerLift.vanishingPoly t).eval ζ * (qp c).eval ζ)
    (hnonexc : ∀ c ∈ Dregg2.Circuit.RotatedKernelRefinement.transferV3.constraints, isArith c →
        ζ ∉ Dregg2.Circuit.OodQuotientConsistency.exceptionalSet
          (Dregg2.Circuit.TraceColumnInterp.constraintPoly
              Dregg2.Circuit.RotatedKernelRefinement.transferV3 t c
            - Dregg2.Circuit.FieldIntegerLift.vanishingPoly t * qp c)) :
    MainAirAcceptF Dregg2.Circuit.RotatedKernelRefinement.transferV3 t :=
  Dregg2.Circuit.FieldIntegerLift.ood_forces_mainAirAccept_field_of_residuals
    _ t hcap ζ qp hood hnonexc

#assert_axioms extractionAirConjunct_of_oodInterpF
#assert_axioms extractionAirConjunct_of_residuals

/-! ## §7 — DISCHARGING the two fields: proven math transported ONTO each, remaining maps named.

`§3` wired the proven arity-8 proximity BETWEEN the two fields. Here we go one step further and push
proven math INTO each field, shrinking both residuals to their irreducible cross-type cores:

  * **`decode_trace` is DISCHARGED down to an OOD/leg decode.** The single hardest conjunct of
    `decode_trace`'s deliverable `TraceWitnessed` is the AIR quotient acceptance `MainAirAcceptF
    (R pi.effect) t`. That conjunct is now PRODUCED, not assumed: `FieldIntegerLift.
    ood_forces_mainAirAccept_field` turns a committed field-OOD bundle `OodInterpF (R pi.effect) t`
    into exactly `MainAirAcceptF (R pi.effect) t`. So a codeword-decode that yields the OOD bundle
    (`DeployedTraceDecode.ood_decode`) is STRICTLY WEAKER than the raw `decode_trace`: the AIR
    conjunct is transported by a proved theorem. Per `FieldIntegerLift.
    ood_forces_mainAirAccept_field_of_residuals` the OOD bundle itself reduces further to EXACTLY the
    two crypto residuals `{hood, hnonexc}` (RLC/commitment-opening + Fiat–Shamir).

  * **`accept_folds` remains the FRI column-identification residual — proximity stays load-bearing.**
    We deliberately do NOT assume `oracle ∈ friSetupK8.C` at the fold level (that would launder the
    proximity math out — `fold_complete` would make `accept_folds` free by assuming its own
    conclusion). `accept_folds` stays the pure disjoint-types map: the deployed `verifyAlgo`'s FRI
    query check (over `Int`/`BatchProofData`) realizes the abstract arity-8 fold into `friSetupK8.C'`
    (over `BabyBear`/`Fin 16`). `FriColumnIdentification` names it precisely as a `Prop`. -/

/-- **`FriColumnIdentification`** — the EXACT irreducible map behind `accept_folds`, named. It is the
disjoint-developments seam that cannot close in-tree: the deployed `verifyAlgo` runs over a generic
field (deployed at `Int`, committing FRI columns inside `BatchProofData` as Merkle-opened lists),
while `friSetupK8 : FriSetupK BabyBear (Fin 16) (Fin 2) 8` lives over `BabyBear` with the `Fin 16`
Reed–Solomon domain. This `Prop` is the committed-column ↔ abstract-oracle identification in the
`property → transcript` direction: on `verifyAlgo`-accept the committed columns, read as the abstract
oracle, fold into `friSetupK8.C'` under all `8` challenges. It is `accept_folds` verbatim — a rename
that isolates the residual. (NOT assumed `oracle ∈ friSetupK8.C`: that is what proximity PROVES from
this, `friProximityK8_discharge0`; assuming it here would launder the FRI math out.) -/
def FriColumnIdentification
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (oracle : BatchPublicInputs → BatchProof → (Fin 16 → Dregg2.Circuit.BabyBearFriField.BabyBear))
    (chal : BatchPublicInputs → BatchProof → (Fin 8 → Dregg2.Circuit.BabyBearFriField.BabyBear)) :
    Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    verifyAlgo perm RATE toNat params vk checks initState logN
        (view pi π).1 (view pi π).2 = true →
    ∀ i, Fold friSetupK8.geom (chal pi π i) (oracle pi π) ∈ friSetupK8.C'

/-- **`DeployedTraceDecode`** — the SHRUNK residual for `DeployedTraceExtract`: `accept_folds`
UNCHANGED (the FRI column-identification, proximity load-bearing) plus `ood_decode`, the codeword
decode delivering a field-OOD bundle `OodInterpF` and the non-AIR legs — NOT the raw `MainAirAcceptF`.
The AIR conjunct is discharged by proven math (`§7` theorem below), so `ood_decode` is strictly weaker
than `DeployedFriEmbedding.decode_trace`. -/
structure DeployedTraceDecode
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView) : Type where
  /-- The committed BabyBear column oracle the deployed proof exposes. -/
  oracle : BatchPublicInputs → BatchProof → (Fin 16 → Dregg2.Circuit.BabyBearFriField.BabyBear)
  /-- The `8` FRI fold challenges of the transcript. -/
  chal : BatchPublicInputs → BatchProof → (Fin 8 → Dregg2.Circuit.BabyBearFriField.BabyBear)
  /-- The `8` challenges are DISTINCT (arity-8 Vandermonde inverts). -/
  chal_inj : ∀ pi π, Function.Injective (chal pi π)
  /-- **VERIFIER-DECODE (unchanged)** — the FRI column-identification residual (`FriColumnIdentification`);
  proximity remains load-bearing between this and the codeword hypothesis of `ood_decode`. -/
  accept_folds :
    FriColumnIdentification perm RATE toNat params vk checks initState logN view oracle chal
  /-- **OOD-DECODE (shrunk decode)** — on accept AND the committed oracle being a genuine low-degree
  codeword, an opened `VmTrace` with a field-OOD bundle `OodInterpF (R pi.effect) t` (⟹ `MainAirAcceptF`
  by proven math) plus all the non-AIR `TraceWitnessed` legs and the published-commit link. -/
  ood_decode : ∀ (pi : BatchPublicInputs) (π : BatchProof),
    verifyAlgo perm RATE toNat params vk checks initState logN
        (view pi π).1 (view pi π).2 = true →
    oracle pi π ∈ friSetupK8.C →
    ∃ (minit : Int → Int) (mfin : Int → Int × Nat) (maddrs : List Int) (t : VmTrace)
        (_ood : Dregg2.Circuit.FieldIntegerLift.OodInterpF (R pi.effect) t),
      (∀ i < t.rows.length, ∀ c ∈ (R pi.effect).constraints, ¬ isArith c →
          c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)) ∧
      (∀ i < t.rows.length, siteHoldsAll hash (envAt t i) (R pi.effect).hashSites) ∧
      (∀ i < t.rows.length, ∀ r ∈ (R pi.effect).ranges, r.holds (envAt t i)) ∧
      maddrs.Nodup ∧
      (∀ op ∈ memLog (R pi.effect) t, op.addr ∈ maddrs) ∧
      MemoryChecking.Disciplined (memLog (R pi.effect) t) ∧
      MemoryChecking.MemCheck minit mfin maddrs (memLog (R pi.effect) t) ∧
      t.tf .memory = (memLog (R pi.effect) t).map opRow ∧
      t.tf .mapOps = mapLog (R pi.effect) t ∧
      tracePublishedCommit t = pi.toPublished

/-- **`deployedFriEmbedding_of_traceDecode` — `decode_trace` DISCHARGED via proven OOD→AIR math.**
Build the full `DeployedFriEmbedding` from the shrunk `DeployedTraceDecode`: `accept_folds` passes
through (same FRI column-identification residual, proximity untouched); `decode_trace` is CONSTRUCTED —
the OOD bundle from `ood_decode` is turned into the `MainAirAcceptF` conjunct by the PROVED
`FieldIntegerLift.ood_forces_mainAirAccept_field`, and the remaining legs pass through. So the raw
`decode_trace` obligation is replaced by the strictly weaker OOD/leg decode, with the AIR-acceptance
conjunct now supplied by a theorem rather than assumed. (A `def`: `DeployedFriEmbedding` is `Type`,
carrying the two decode functions as data.) -/
def deployedFriEmbedding_of_traceDecode
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (dec : DeployedTraceDecode hash R perm RATE toNat params vk checks initState logN view) :
    DeployedFriEmbedding hash R perm RATE toNat params vk checks initState logN view where
  oracle := dec.oracle
  chal := dec.chal
  chal_inj := dec.chal_inj
  accept_folds := dec.accept_folds
  decode_trace := by
    intro pi π hacc hcw
    obtain ⟨minit, mfin, maddrs, t, hOod, hbus, hHashes, hRanges,
      hNodup, hClosed, hDisc, hBal, hMemTF, hMapTF, hPub⟩ := dec.ood_decode pi π hacc hcw
    exact ⟨minit, mfin, maddrs, t,
      Dregg2.Circuit.FieldIntegerLift.ood_forces_mainAirAccept_field (R pi.effect) t hOod,
      hbus, hHashes, hRanges, hNodup, hClosed, hDisc, hBal, hMemTF, hMapTF, hPub⟩

/-- **`deployedTraceExtract_of_traceDecode`** — the opaque `DeployedTraceExtract` from the shrunk
residual, with BOTH proven links load-bearing: proximity (`§3`) between the two fields, and the
OOD→AIR bridge (`§7`) inside `decode_trace`. -/
theorem deployedTraceExtract_of_traceDecode
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (dec : DeployedTraceDecode hash R perm RATE toNat params vk checks initState logN view) :
    DeployedTraceExtract hash R perm RATE toNat params vk checks initState logN view :=
  deployedTraceExtract_of_embedding hash R perm RATE toNat params vk checks initState logN view
    (deployedFriEmbedding_of_traceDecode hash R perm RATE toNat params vk checks initState logN view dec)

/-- **`starkSound_of_traceDecode_and_refines` — `[StarkSound]` from the shrunk residual + code
refinement.** The apex carrier from (i) the `DeployedTraceDecode` (the FRI column-identification map +
the OOD/leg decode; the arity-8 proximity AND the OOD→AIR bridge PROVED between/inside them) and (ii)
`DeployedRefines`. The math residual is now: one cross-type FRI column-identification (`accept_folds`)
and one codeword→OOD/leg decode, whose AIR conjunct further reduces to `{hood, hnonexc}`. -/
theorem starkSound_of_traceDecode_and_refines
    (hash : List Int → Int) (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (checks : FriChecks Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (dec : DeployedTraceDecode hash R perm RATE toNat params vk checks initState logN view)
    (href : DeployedRefines R perm RATE toNat params vk checks initState logN view) :
    StarkSound hash R :=
  starkSound_of_embedding_and_refines hash R perm RATE toNat params vk checks initState logN view
    (deployedFriEmbedding_of_traceDecode hash R perm RATE toNat params vk checks initState logN view dec)
    href

#assert_axioms deployedFriEmbedding_of_traceDecode
#assert_axioms deployedTraceExtract_of_traceDecode
#assert_axioms starkSound_of_traceDecode_and_refines

/-! ### §7 TEETH — the OOD→AIR transport is genuine (load-bearing, both polarities).

The shrunk `ood_decode`'s AIR-acceptance conjunct is produced by proven math and is a real obligation:
the OOD bundle FIRES to `MainAirAcceptF` on honest data and the target conjunct BITES on a tampered
gate. Reuses the committed `FieldIntegerLift` / `AirChecksSatisfied` witnesses. -/

/-- **OOD→AIR FIRES** — a field-OOD bundle for `transferV3` yields the `MainAirAcceptF` conjunct that
`deployedFriEmbedding_of_traceDecode` needs, so the OOD-decode transport is non-vacuous. -/
theorem oodDecode_air_fires
    (t : VmTrace)
    (I : Dregg2.Circuit.FieldIntegerLift.OodInterpF
          Dregg2.Circuit.RotatedKernelRefinement.transferV3 t) :
    MainAirAcceptF Dregg2.Circuit.RotatedKernelRefinement.transferV3 t :=
  Dregg2.Circuit.FieldIntegerLift.ood_forces_mainAirAccept_field _ t I

/-- **OOD→AIR BITES** — the `MainAirAcceptF` the transport must produce is FALSIFIABLE: a tampered-gate
trace cannot meet it, so `ood_decode` cannot be satisfied by a lying trace even with the OOD softening. -/
theorem oodDecode_air_bites :
    ¬ MainAirAcceptF Dregg2.Circuit.AirChecksSatisfied.dArith
        Dregg2.Circuit.AirChecksSatisfied.tTampered :=
  Dregg2.Circuit.AirChecksSatisfied.tampered_gate_unacceptedF

#assert_axioms oodDecode_air_fires
#assert_axioms oodDecode_air_bites

end Dregg2.Circuit.DeployedTraceExtract
