/-
# `Dregg2.Circuit.FriLdtExtractDeployed` — the FRI-LDT extraction bundle over the verifier the
APEX ACTUALLY RUNS, with the singleton-OOD vacuity PROVED and REPAIRED.

## §A The defect this file proves and repairs (the OOD point is a 4-lane `Challenge`)

`AlgoStarkSoundTransferV3.FriLdtExtractV3` (`:143`) concludes, on every accepting run,

    (view pi π).1.oodPoint = [ood]      with `ood : ℤ` — ONE base felt.

The deployed verifier forces the opposite. `CircuitSoundness.verifyBatch` (`:449-453`) runs
`ExtFieldChallenge.verifyAlgoUnifiedFaithfulExt`, whose acceptance conjuncts include
`decide (params.extDeg = 4)` (`ExtFieldChallenge.lean:762`) and — through
`verifyAlgoUnifiedFaithful ⟹ verifyAlgoUnified ⟹ unifiedTranscriptChecks` — the OOD binding
`decide (proof.oodPoint = d.ζ)` (`FriChallengerUnified.lean:122`), where `d.ζ` is a
`Challenger.sampleExt … params.extDeg` squeeze, i.e. a list of EXACTLY `params.extDeg` base lanes
(`FriVerifier.lean:581` + `Challenger.sampleN_length`). So acceptance forces
`oodPoint.length = 4`, the bundle forces `oodPoint.length = 1`, and the two cannot both hold.

That is proved here, not asserted: `faithfulExt_forces_oodPoint_length` (§1) and
`singletonBundle_makes_deployed_verifier_accept_nothing` /
`friLdtExtractV3_makes_verifyBatch_reject_everything` (§2). The consequence is stated at the apex:
under the landed bundle at the deployed config, `verifyBatch` returns `reject` on EVERY input, so
any apex conditioned on that bundle is vacuously true. (⚑ 2026-07-25: every such apex has since been
CUT OVER — `StarkSoundFriLdt.starkSound_of_friLdtExtract_transferV3` now carries
`FriLdtExtractV3Faithful`; see §5 and `StarkSoundFriLdt`'s header.)

Root cause: the base-field-versus-quartic-extension modeling wound in its terminal form. `[ood]` with
`ood : BabyBear` is a single base felt standing in for a 4-lane `Challenge`. Same wound, still open
elsewhere: `AlgoStarkSoundGeneral.lean:147`, `FriVerifierFS.lean:112`,
`FriDecodedTraceWitness.lean:464`, `OodExtChallengeLayout.lean:617`, `OodColumnLayout.lean:229`,
`DeployedRefinesProof.lean:103`, `FriVerifierBridge.lean:185`.

## §B The repair

The verifier's own scalar restriction never wanted a singleton: `FriVerifier.batchTablesCheck`
(`:803-808`) matches `| ood :: _` and consumes the HEAD lane. Only the bundle demanded `[ood]`. So
the repair is entirely on the bundle side:

  * `FriLdtExtractV3Cons` (§3) — the bare-verifier bundle with `oodPoint = ood :: oodRest`. As of
    2026-07-28 it also carries the PER-RUN opening residual `¬ OpeningColl`, so it is NO LONGER
    implied by the landed `FriLdtExtractV3` (`friLdtExtractV3_imp_cons` DELETED, §3).
  * `FriLdtExtractV3Faithful` (§3) — the deployed-verifier bundle, concluding the OOD point IS the
    transcript's `d.ζ`, of length `params.extDeg` (= 4 on every accepting run), with `ood` its head lane.
  * §4 re-proves the OOD reduction chain at the `ood :: oodRest` shape
    (`batchTablesCheck`/`verifyAlgo`/`hood`/`MainAirAcceptF`); nothing in it ever needed a singleton.
  * §5 re-derives the apex `starkSound_of_friLdtExtractFaithful_transferV3` from the corrected
    bundle, and is the new home of `algoStarkSound_transferV3_cons` — the RELOCATED
    `AlgoStarkSoundTransferV3.algoStarkSound_transferV3`, which could not be corrected in place
    because its module defines `FriLdtExtractV3` and is upstream of this one (2026-07-25 cutover).

## §C Why the repair is not a second vacuity (§6)

  * `faithfulExt_accept_gives_cons_shape` — every accepting run SATISFIES the corrected shape. The
    added conjuncts can therefore never be the reason a premise is empty.
  * `friLdtExtractV3Faithful_iff_noOodShape` — the corrected bundle is EQUIVALENT to the bundle with
    the three OOD conjuncts deleted. The repair adds exactly zero strength.
  * `deployed_accepting_pole_nonempty` / `corrected_ood_shape_inhabited` — a concrete run the
    complete apex-facing predicate ACCEPTS (`decide`, not `#guard`), on which the corrected shape
    holds and the singleton shape is refuted.

What is NOT claimed: that the whole corrected bundle is satisfiable at the deployed config. Its
remaining conjuncts ARE the FRI-LDT floor, and `cfgPerm`/`cfgView`/… are `opaque`, so no accepting
run at deployed args can be exhibited by anyone. The claim proved here is narrower and exact: the
corrected bundle's OOD conjuncts are implied by acceptance, whereas the singleton one contradicts it.

## §D The verifier-index change (kept from the previous revision)

The bundle's antecedent is `verifyAlgoUnifiedFaithfulExt`, the predicate `verifyBatch` evaluates —
not the bare `verifyAlgo … (fullChecks …)` of the landed bundle, which is provably foolable on the
Fiat–Shamir data the bundle asserts things about (`fullChecks.batchTables` discards the transcript
betas, and `FriChallengerUnified.verifyAlgo_accepts_but_unified_rejects` exhibits a free-beta forgery
the bare path swallows). `bundles_are_not_interchangeable` (§7) quotes that separation.
-/
import Dregg2.Circuit.AlgoStarkSoundTransferV3
import Dregg2.Circuit.StarkSoundDischarge

namespace Dregg2.Circuit.FriLdtExtractDeployed

open Polynomial
open Dregg2.Circuit.FriVerifierBridge (AlgoStarkSound ProofView)
open Dregg2.Circuit.FriVerifier
  (verifyAlgo BatchProofData WrapPublics FriParams RecursionVk FriChecks FriCore FieldArith
   TableOpening LayerOpening fullChecks batchTablesCheck deriveTranscript)
open Dregg2.Circuit.CircuitSoundness
  (BatchPublicInputs BatchProof Registry StarkSound Verdict VerifyKey vkOfRegistry verifyBatch
   tracePublishedCommit cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA cfgExtCore cfgExtA
   cfgExtW cfgInitState cfgLogN cfgView cfgExtView cfgExtra cfgChecks)
open Dregg2.Circuit.DescriptorIR2 (VmTrace EffectVmDescriptor2 envAt VmConstraint2 Satisfied2)
open Dregg2.Circuit.AirChecksSatisfied (MainAirAcceptF isArith)
open Dregg2.Circuit.RotatedKernelRefinement (transferV3)
open Dregg2.Circuit.TraceColumnInterp (constraintPoly domainSize)
open Dregg2.Circuit.FieldIntegerLift (vanishingPoly ood_forces_mainAirAccept_field_of_residuals)
open Dregg2.Circuit.OodQuotientConsistency (exceptionalSet)
open Dregg2.Circuit.OodSoundnessGame (batchResidual rlc_debatch)
open Dregg2.Circuit.OodCommitmentBinding
  (merkleRecomputeZ OpeningColl commitmentOpening_binds_of_noColl openingColl_self_false)
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.AlgoStarkSoundTransferV3
  (Rfam arithList isArithB isArithB_iff FriLdtExtractV3 mainAirAcceptF_of_floor)
open Dregg2.Circuit.ExtFieldChallenge
  (ExtElem ExtFriCore ExtFriArith ExtLayerOpening ExtQueryOpening ExtSingleAirOpening
   ExtVerifierView extAdd extOfBase extFoldCombine babyBear babyBearFriArith
   verifyAlgoUnifiedFaithfulExt verifyAlgoUnifiedFaithfulExt_imp_verifyAlgoUnified)
open Dregg2.Circuit.FriChallengerUnified
  (verifyAlgoUnified unifiedTranscriptChecks verifyAlgoUnified_imp_verifyAlgo)

/-- The apex's extension-side view (`CircuitSoundness.cfgExtView`'s type): the serialized
extension rows / Merkle material and AIR-evaluated OOD values the quartic verifier walks.
Challenges, query indices, domain points, vanishing and inverses are NOT in it — the verifier
reconstructs those from the continued transcript. -/
abbrev ExtProofView := BatchPublicInputs → BatchProof → ExtVerifierView Int

/-! ## §1 — what the DEPLOYED verifier forces about `oodPoint`. -/

/-- The transcript's OOD squeeze has exactly `params.extDeg` base lanes. `deriveTranscript` binds
`ζ` as `Challenger.sampleExt perm RATE params.extDeg`, and `sampleExt = sampleN` has
`sampleN_length`. -/
theorem deriveTranscript_zeta_length {F : Type} [Inhabited F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F) :
    (deriveTranscript perm RATE toNat params initState logN proof pub).ζ.length
      = params.extDeg := by
  unfold deriveTranscript
  exact Dregg2.Circuit.FriVerifier.Challenger.sampleN_length perm RATE params.extDeg _

/-- Extension-faithful acceptance forces the DEPLOYED quartic width: `params.extDeg = 4`. -/
theorem faithfulExt_forces_extDeg {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (core : FriCore F) (A : FieldArith F)
    (extCore : ExtFriCore F) (extA : ExtFriArith F) (Wres : F)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F)
    (view : ExtVerifierView F)
    (hacc : verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core A extCore extA Wres
      initState logN proof pub view = true) :
    params.extDeg = 4 := by
  unfold verifyAlgoUnifiedFaithfulExt at hacc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hacc
  tauto

/-- Extension-faithful acceptance forces the OOD point to BE the continued transcript's `ζ`
(`unifiedTranscriptChecks`' opening conjunct `decide (proof.oodPoint = d.ζ)`). -/
theorem faithfulExt_forces_oodPoint_eq_zeta {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (core : FriCore F) (A : FieldArith F)
    (extCore : ExtFriCore F) (extA : ExtFriArith F) (Wres : F)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F)
    (view : ExtVerifierView F)
    (hacc : verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core A extCore extA Wres
      initState logN proof pub view = true) :
    proof.oodPoint = (Dregg2.Circuit.FriChallengerUnified.deriveTranscript perm RATE toNat
      params initState logN proof pub).ζ := by
  have h1 := verifyAlgoUnifiedFaithfulExt_imp_verifyAlgoUnified
      perm RATE toNat params vk core A extCore extA Wres initState logN proof pub view hacc
  unfold verifyAlgoUnified unifiedTranscriptChecks at h1
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  exact h1.2.1.1.1.1

/-- **The deployed OOD point has FOUR lanes.** Composition of the two conjuncts above with the
squeeze-length law. This is the fact the singleton bundle contradicts. -/
theorem faithfulExt_forces_oodPoint_length {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (core : FriCore F) (A : FieldArith F)
    (extCore : ExtFriCore F) (extA : ExtFriArith F) (Wres : F)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F)
    (view : ExtVerifierView F)
    (hacc : verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core A extCore extA Wres
      initState logN proof pub view = true) :
    proof.oodPoint.length = 4 := by
  rw [faithfulExt_forces_oodPoint_eq_zeta perm RATE toNat params vk core A extCore extA Wres
        initState logN proof pub view hacc]
  rw [show (Dregg2.Circuit.FriChallengerUnified.deriveTranscript perm RATE toNat params
        initState logN proof pub).ζ.length = params.extDeg from
      deriveTranscript_zeta_length perm RATE toNat params initState logN proof pub,
    faithfulExt_forces_extDeg perm RATE toNat params vk core A extCore extA Wres
      initState logN proof pub view hacc]

/-- **No accepting run has a singleton OOD point.** -/
theorem faithfulExt_forces_oodPoint_ne_singleton {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (core : FriCore F) (A : FieldArith F)
    (extCore : ExtFriCore F) (extA : ExtFriArith F) (Wres : F)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F)
    (view : ExtVerifierView F)
    (hacc : verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core A extCore extA Wres
      initState logN proof pub view = true) (ood : F) :
    proof.oodPoint ≠ [ood] := by
  intro hsing
  have := faithfulExt_forces_oodPoint_length perm RATE toNat params vk core A extCore extA Wres
    initState logN proof pub view hacc
  rw [hsing] at this
  simp at this

/-- **Every accepting run satisfies the CORRECTED shape** — the head lane, the transcript identity,
and the lane count, all delivered by acceptance itself. This is what makes the repair in §3 free of
strength (see `friLdtExtractV3Faithful_iff_noOodShape`). -/
theorem faithfulExt_accept_gives_cons_shape {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (core : FriCore F) (A : FieldArith F)
    (extCore : ExtFriCore F) (extA : ExtFriArith F) (Wres : F)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F)
    (view : ExtVerifierView F)
    (hacc : verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core A extCore extA Wres
      initState logN proof pub view = true) :
    ∃ (ood : F) (oodRest : List F),
      proof.oodPoint = ood :: oodRest
        ∧ ood :: oodRest = (Dregg2.Circuit.FriChallengerUnified.deriveTranscript perm RATE toNat
            params initState logN proof pub).ζ
        ∧ (ood :: oodRest).length = params.extDeg := by
  have hlen := faithfulExt_forces_oodPoint_length perm RATE toNat params vk core A extCore extA
    Wres initState logN proof pub view hacc
  have hzeta := faithfulExt_forces_oodPoint_eq_zeta perm RATE toNat params vk core A extCore extA
    Wres initState logN proof pub view hacc
  have hdeg := faithfulExt_forces_extDeg perm RATE toNat params vk core A extCore extA Wres
    initState logN proof pub view hacc
  have hne : proof.oodPoint ≠ [] := by intro h; rw [h] at hlen; simp at hlen
  obtain ⟨ood, oodRest, hcons⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨ood, oodRest, hcons, ?_, ?_⟩
  · rw [← hcons]; exact hzeta
  · rw [← hcons, hlen, hdeg]

/-! ## §2 — THE DEFECT, PROVED: the singleton bundle empties the deployed verifier. -/

/-- **The DEFECTIVE bundle shape, retained ONLY as the subject of the tooth below.** This is
`AlgoStarkSoundTransferV3.FriLdtExtractV3`'s body verbatim, moved onto the deployed verifier
`verifyAlgoUnifiedFaithfulExt` — including the singleton conjunct `oodPoint = [ood]`. It is defined
here so the vacuity is a machine-checked statement about a concrete object rather than a remark;
nothing downstream may consume it. -/
def FriLdtExtractV3FaithfulSingleton
    (sponge : List ℤ → ℤ) (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (extCore : ExtFriCore ℤ) (extA : ExtFriArith ℤ) (W : ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) (extView : ExtProofView) : Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core A extCore extA W
        initState logN (view pi π).1 (view pi π).2 (extView pi π) = true →
    ∃ (t : VmTrace) (ζ Λ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)
      (topen : TableOpening ℤ) (ood vCommitted root : ℤ) (idx : Nat) (siblings : List ℤ),
      t.rows.length ≤ domainSize ∧
      (view pi π).1.oodPoint = [ood] ∧
      topen ∈ (view pi π).1.tableOpenings ∧
      merkleRecomputeZ sponge idx vCommitted siblings = root ∧
      merkleRecomputeZ sponge idx topen.constraintEval siblings = root ∧
      (batchResidual (Rfam transferV3 t ζ qp)).eval Λ
        = ((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear) ∧
      Λ ∉ exceptionalSet (batchResidual (Rfam transferV3 t ζ qp)) ∧
      (∀ c ∈ transferV3.constraints, isArith c →
          ζ ∉ exceptionalSet (constraintPoly transferV3 t c - vanishingPoly t * qp c)) ∧
      (∀ i < t.rows.length, ∀ c ∈ transferV3.constraints, ¬ isArith c →
          c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)) ∧
      t.tf .memory = [] ∧ t.tf .mapOps = [] ∧
      tracePublishedCommit t = pi.toPublished

/-- **THE VACUITY, PROVED.** Assuming the singleton-shaped bundle, the deployed verifier accepts
NOTHING: for every `(pi, π)` the predicate `verifyBatch` evaluates returns `false`. The bundle would
have to produce a one-lane OOD point on a run whose acceptance forces four lanes. -/
theorem singletonBundle_makes_deployed_verifier_accept_nothing
    (sponge : List ℤ → ℤ) (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (extCore : ExtFriCore ℤ) (extA : ExtFriArith ℤ) (W : ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) (extView : ExtProofView)
    (h : FriLdtExtractV3FaithfulSingleton sponge hash perm RATE toNat params vk core A
      extCore extA W initState logN view extView)
    (pi : BatchPublicInputs) (π : BatchProof) :
    verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core A extCore extA W
      initState logN (view pi π).1 (view pi π).2 (extView pi π) = false := by
  rcases Bool.eq_false_or_eq_true
      (verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core A extCore extA W
        initState logN (view pi π).1 (view pi π).2 (extView pi π)) with hb | hb
  · obtain ⟨_, _, _, _, _, ood, _, _, _, _, _, hoodPt, _⟩ := h pi π hb
    exact absurd hoodPt
      (faithfulExt_forces_oodPoint_ne_singleton perm RATE toNat params vk core A extCore extA W
        initState logN (view pi π).1 (view pi π).2 (extView pi π) hb ood)
  · exact hb

/-- The LANDED bare-verifier bundle inherits the defect, because bare acceptance is IMPLIED by
deployed acceptance (`verifyAlgoUnifiedFaithfulExt ⟹ verifyAlgoUnified ⟹ verifyAlgo`), so
`FriLdtExtractV3` discharges the singleton-shaped deployed bundle. -/
theorem friLdtExtractV3_imp_faithfulSingleton
    (sponge : List ℤ → ℤ) (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (extCore : ExtFriCore ℤ) (extA : ExtFriArith ℤ) (W : ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) (extView : ExtProofView)
    (h : FriLdtExtractV3 sponge hash perm RATE toNat params vk core A initState logN view) :
    FriLdtExtractV3FaithfulSingleton sponge hash perm RATE toNat params vk core A extCore extA W
      initState logN view extView := by
  intro pi π hacc
  exact h pi π
    (verifyAlgoUnified_imp_verifyAlgo perm RATE toNat params vk core A initState logN
      (view pi π).1 (view pi π).2
      (verifyAlgoUnifiedFaithfulExt_imp_verifyAlgoUnified perm RATE toNat params vk core A
        extCore extA W initState logN (view pi π).1 (view pi π).2 (extView pi π) hacc))

/-- **The apex consequence, at the deployed config.** Under the LANDED `FriLdtExtractV3` at the
deployed `cfg*` arguments — the RETIRED hypothesis of
`StarkSoundFriLdt.starkSound_of_friLdtExtract_transferV3`, and of the deleted
`AlgoStarkSoundTransferV3.algoStarkSound_transferV3` — `CircuitSoundness.verifyBatch` returns
`Verdict.reject` on EVERY key/public-input/proof triple. Any `StarkSound`-shaped conclusion drawn
from that hypothesis therefore quantifies over an empty set of accepting batches. -/
theorem friLdtExtractV3_makes_verifyBatch_reject_everything
    (sponge : List ℤ → ℤ) (hash : List ℤ → ℤ)
    (h : FriLdtExtractV3 sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
      cfgInitState cfgLogN cfgView)
    (vkey : VerifyKey) (pi : BatchPublicInputs) (π : BatchProof) :
    verifyBatch vkey pi π = Verdict.reject := by
  have hrej := singletonBundle_makes_deployed_verifier_accept_nothing sponge hash cfgPerm cfgRATE
    cfgToNat cfgParams cfgVk cfgCore cfgA cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN cfgView
    cfgExtView
    (friLdtExtractV3_imp_faithfulSingleton sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk
      cfgCore cfgA cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN cfgView cfgExtView h)
    pi π
  simp [verifyBatch, hrej]

/-! ## §3 — the CORRECTED bundles. -/

/-- **`FriLdtExtractV3Cons` — the corrected BARE-verifier bundle**, added alongside the landed
`AlgoStarkSoundTransferV3.FriLdtExtractV3` (which is consumed by a dozen modules and is not edited).
Identical field-for-field except that the OOD conjunct is `oodPoint = ood :: oodRest`, the shape
`FriVerifier.batchTablesCheck` actually matches (`| ood :: _`, `FriVerifier.lean:805`). -/
def FriLdtExtractV3Cons
    (sponge : List ℤ → ℤ) (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) : Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
        initState logN (view pi π).1 (view pi π).2 = true →
    ∃ (t : VmTrace) (ζ Λ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)
      (topen : TableOpening ℤ) (ood vCommitted root : ℤ) (oodRest : List ℤ)
      (idx : Nat) (siblings : List ℤ),
      t.rows.length ≤ domainSize ∧
      (view pi π).1.oodPoint = ood :: oodRest ∧
      topen ∈ (view pi π).1.tableOpenings ∧
      merkleRecomputeZ sponge idx vCommitted siblings = root ∧
      merkleRecomputeZ sponge idx topen.constraintEval siblings = root ∧
      ¬ OpeningColl sponge idx topen.constraintEval vCommitted siblings ∧
      (batchResidual (Rfam transferV3 t ζ qp)).eval Λ
        = ((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear) ∧
      Λ ∉ exceptionalSet (batchResidual (Rfam transferV3 t ζ qp)) ∧
      (∀ c ∈ transferV3.constraints, isArith c →
          ζ ∉ exceptionalSet (constraintPoly transferV3 t c - vanishingPoly t * qp c)) ∧
      (∀ i < t.rows.length, ∀ c ∈ transferV3.constraints, ¬ isArith c →
          c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)) ∧
      t.tf .memory = [] ∧ t.tf .mapOps = [] ∧
      tracePublishedCommit t = pi.toPublished

/-! ⚑ **DELETED 2026-07-28 — `friLdtExtractV3_imp_cons`** (`FriLdtExtractV3 ⟹ FriLdtExtractV3Cons`).

The corrected bundle now carries the PER-RUN opening residual `¬ OpeningColl` — the honest
replacement for the refuted `Poseidon2SpongeCR` floor the whole reduction chain used to thread — and
the LANDED bundle never carried it, so the implication is no longer provable. It could only be
restored by assuming the residual at every opening reaching a common root, which is the global
Merkle-binding floor in disguise and is exactly the move this repair exists to stop.

WHAT WAS LOST, precisely: a free transport from `FriLdtExtractV3` — a premise this very module PROVES
makes `CircuitSoundness.verifyBatch` reject EVERY input at the deployed arguments
(`friLdtExtractV3_makes_verifyBatch_reject_everything`). It transported nothing, because there is
nothing on the other side of an empty premise to transport. Its four downstream receipts
(`StarkSoundReduce.retiredPremise_imp_reducePremise`, `StarkSoundFriLdt.retiredPremise_imp_apexPremise`,
`StarkSoundFriLdtCorrected.landedPremise_imp_correctedPremise` and
`.starkSound_of_friLdtExtract_transferV3_via_corrected`) are deleted with it and say the same there. -/

/-- **`FriLdtExtractV3Faithful` — the corrected bundle over the verifier the apex RUNS.**

Antecedent: `ExtFieldChallenge.verifyAlgoUnifiedFaithfulExt`, the predicate
`CircuitSoundness.verifyBatch` evaluates. Conclusion: the same extraction payload as the landed
bundle, with the OOD conjunct replaced by what the deployed verifier forces —

  * `oodPoint = ood :: oodRest` (`ood` is the head lane `batchTablesCheck` consumes),
  * `ood :: oodRest = d.ζ` — the OOD point IS the continued transcript's out-of-domain squeeze,
  * `(ood :: oodRest).length = params.extDeg` — four lanes on every accepting run.

Contains no `hood` and no `MainAirAcceptF`; those are derived in §5. -/
def FriLdtExtractV3Faithful
    (sponge : List ℤ → ℤ) (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (extCore : ExtFriCore ℤ) (extA : ExtFriArith ℤ) (W : ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) (extView : ExtProofView) : Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core A extCore extA W
        initState logN (view pi π).1 (view pi π).2 (extView pi π) = true →
    ∃ (t : VmTrace) (ζ Λ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)
      (topen : TableOpening ℤ) (ood vCommitted root : ℤ) (oodRest : List ℤ)
      (idx : Nat) (siblings : List ℤ),
      t.rows.length ≤ domainSize ∧
      (view pi π).1.oodPoint = ood :: oodRest ∧
      ood :: oodRest
        = (Dregg2.Circuit.FriChallengerUnified.deriveTranscript perm RATE toNat params initState
            logN (view pi π).1 (view pi π).2).ζ ∧
      (ood :: oodRest).length = params.extDeg ∧
      topen ∈ (view pi π).1.tableOpenings ∧
      merkleRecomputeZ sponge idx vCommitted siblings = root ∧
      merkleRecomputeZ sponge idx topen.constraintEval siblings = root ∧
      ¬ OpeningColl sponge idx topen.constraintEval vCommitted siblings ∧
      (batchResidual (Rfam transferV3 t ζ qp)).eval Λ
        = ((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear) ∧
      Λ ∉ exceptionalSet (batchResidual (Rfam transferV3 t ζ qp)) ∧
      (∀ c ∈ transferV3.constraints, isArith c →
          ζ ∉ exceptionalSet (constraintPoly transferV3 t c - vanishingPoly t * qp c)) ∧
      (∀ i < t.rows.length, ∀ c ∈ transferV3.constraints, ¬ isArith c →
          c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)) ∧
      t.tf .memory = [] ∧ t.tf .mapOps = [] ∧
      tracePublishedCommit t = pi.toPublished

/-- **The corrected transport**: the corrected bare bundle discharges the corrected deployed bundle.
Non-vacuous — the extra OOD conjuncts come from `faithfulExt_accept_gives_cons_shape`, i.e. from
acceptance, and the cons decomposition is transported by list-injectivity, not by contradiction. -/
theorem friLdtExtractV3Cons_imp_faithful
    (sponge : List ℤ → ℤ) (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (extCore : ExtFriCore ℤ) (extA : ExtFriArith ℤ) (W : ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) (extView : ExtProofView)
    (h : FriLdtExtractV3Cons sponge hash perm RATE toNat params vk core A initState logN view) :
    FriLdtExtractV3Faithful sponge hash perm RATE toNat params vk core A extCore extA W
      initState logN view extView := by
  intro pi π hacc
  have hbare : verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
      initState logN (view pi π).1 (view pi π).2 = true :=
    verifyAlgoUnified_imp_verifyAlgo perm RATE toNat params vk core A initState logN
      (view pi π).1 (view pi π).2
      (verifyAlgoUnifiedFaithfulExt_imp_verifyAlgoUnified perm RATE toNat params vk core A
        extCore extA W initState logN (view pi π).1 (view pi π).2 (extView pi π) hacc)
  obtain ⟨ood', oodRest', hcons', hzeta', hlen'⟩ :=
    faithfulExt_accept_gives_cons_shape perm RATE toNat params vk core A extCore extA W
      initState logN (view pi π).1 (view pi π).2 (extView pi π) hacc
  obtain ⟨t, ζ, Λ, qp, topen, ood, vCommitted, root, oodRest, idx, siblings,
    hcap, hoodPt, hmem, hCommitted, hOpened, hno, hlayout, hLam, hnonexc,
    hbus, hMem, hMap, hPub⟩ := h pi π hbare
  have hsame : ood :: oodRest = ood' :: oodRest' := by rw [← hoodPt, hcons']
  exact ⟨t, ζ, Λ, qp, topen, ood, vCommitted, root, oodRest, idx, siblings,
    hcap, hoodPt, by rw [hsame]; exact hzeta', by rw [hsame]; exact hlen',
    hmem, hCommitted, hOpened, hno, hlayout, hLam, hnonexc, hbus, hMem, hMap, hPub⟩

/-! ## §4 — the OOD reduction chain at the `ood :: oodRest` shape.

The landed chain (`FriVerifier.batchTablesCheck_rejects_tampered_quotient` →
`verifyAlgo_full_rejects_tampered_quotient` → `OodQuotientConsistency`'s
`verifyAlgo_accept_forces_table_identity` → `AlgoStarkSoundTransferV3`'s `hood_of_reductions` /
`mainAirAcceptF_of_floor`) carries `oodPoint = [ood]` through every link. Nothing in it uses the
singleton: `batchTablesCheck` matches `| ood :: _`. These are the same proofs at the general shape. -/

/-- `batchTablesCheck` rejects a tampered quotient at ANY nonempty OOD point. -/
theorem batchTablesCheck_rejects_tampered_quotient_cons {F : Type} [DecidableEq F]
    (A : FieldArith F) (proof : BatchProofData F) (ood : F) (oodRest : List F)
    (hood : proof.oodPoint = ood :: oodRest) (t : TableOpening F)
    (hmem : t ∈ proof.tableOpenings)
    (h : t.constraintEval ≠ A.mul t.vanishingAtZeta t.quotientAtZeta) :
    batchTablesCheck A proof = false := by
  unfold batchTablesCheck
  rw [hood]
  rw [Bool.and_eq_false_iff]; left
  rw [List.all_eq_false]
  exact ⟨t, hmem, by
    rw [Dregg2.Circuit.FriVerifier.tableOk_rejects_tampered_quotient A ood t h]; decide⟩

/-- The full `verifyAlgo` rejects a tampered quotient at ANY nonempty OOD point. -/
theorem verifyAlgo_full_rejects_tampered_quotient_cons {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat)
    (params : FriParams) (vk : RecursionVk F) (core : FriCore F) (A : FieldArith F)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F)
    (ood : F) (oodRest : List F) (hood : proof.oodPoint = ood :: oodRest)
    (t : TableOpening F) (hmem : t ∈ proof.tableOpenings)
    (h : t.constraintEval ≠ A.mul t.vanishingAtZeta t.quotientAtZeta) :
    verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
      initState logN proof pub = false := by
  have hbt : (fullChecks core A toNat params.powBits).batchTables proof
      (deriveTranscript perm RATE toNat params initState logN proof pub).betas = false :=
    batchTablesCheck_rejects_tampered_quotient_cons A proof ood oodRest hood t hmem h
  unfold verifyAlgo
  simp only [hbt, Bool.and_false, Bool.false_and]

/-- Acceptance forces the batched OOD table identity at ANY nonempty OOD point (the contrapositive
of the previous theorem) — the cons-shaped `OodQuotientConsistency.verifyAlgo_accept_forces_table_identity`. -/
theorem verifyAlgo_accept_forces_table_identity_cons {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat)
    (params : FriParams) (vk : RecursionVk F) (core : FriCore F) (A : FieldArith F)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F)
    (ood : F) (oodRest : List F) (hood : proof.oodPoint = ood :: oodRest)
    (topen : TableOpening F) (hmem : topen ∈ proof.tableOpenings)
    (h : verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
          initState logN proof pub = true) :
    topen.constraintEval = A.mul topen.vanishingAtZeta topen.quotientAtZeta := by
  by_contra hne
  have hrej := verifyAlgo_full_rejects_tampered_quotient_cons perm RATE toNat params vk core A
    initState logN proof pub ood oodRest hood topen hmem hne
  rw [hrej] at h
  exact absurd h (by decide)

/-- **`hood`, DISCHARGED at the corrected shape.** The cons-shaped
`AlgoStarkSoundTransferV3.hood_of_reductions`: table identity + Poseidon2 commitment binding +
transferV3 column layout + RLC de-batch at a non-exceptional `Λ`. -/
theorem hood_of_reductions_cons
    (d : EffectVmDescriptor2)
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat)
    (proof : BatchProofData ℤ) (pub : WrapPublics ℤ)
    (hacc : verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
        initState logN proof pub = true)
    (t : VmTrace) (ζ Λ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)
    (topen : TableOpening ℤ) (ood vCommitted root : ℤ) (oodRest : List ℤ)
    (idx : Nat) (siblings : List ℤ)
    (hoodPt : proof.oodPoint = ood :: oodRest)
    (hmem : topen ∈ proof.tableOpenings)
    (hCommitted : merkleRecomputeZ sponge idx vCommitted siblings = root)
    (hOpened : merkleRecomputeZ sponge idx topen.constraintEval siblings = root)
    (hno : ¬ OpeningColl sponge idx topen.constraintEval vCommitted siblings)
    (hlayout : (batchResidual (Rfam d t ζ qp)).eval Λ
        = ((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear))
    (hLam : Λ ∉ exceptionalSet (batchResidual (Rfam d t ζ qp))) :
    ∀ c ∈ d.constraints, isArith c →
      (constraintPoly d t c).eval ζ = (vanishingPoly t).eval ζ * (qp c).eval ζ := by
  have htable : topen.constraintEval = A.mul topen.vanishingAtZeta topen.quotientAtZeta :=
    verifyAlgo_accept_forces_table_identity_cons perm RATE toNat params vk core A initState logN
      proof pub ood oodRest hoodPt topen hmem hacc
  have hbind : topen.constraintEval = vCommitted :=
    commitmentOpening_binds_of_noColl sponge hno hCommitted hOpened
  have hvc : vCommitted = A.mul topen.vanishingAtZeta topen.quotientAtZeta :=
    hbind.symm.trans htable
  have heval : (batchResidual (Rfam d t ζ qp)).eval Λ = 0 := by
    rw [hlayout, hvc]; exact sub_self _
  have hRzero : ∀ j, Rfam d t ζ qp j = 0 := rlc_debatch (Rfam d t ζ qp) Λ heval hLam
  intro c hc harith
  have hcf : c ∈ arithList d := List.mem_filter.mpr ⟨hc, (isArithB_iff c).mpr harith⟩
  obtain ⟨i, hlt, hget⟩ := List.mem_iff_getElem.mp hcf
  have hj0 : Rfam d t ζ qp ⟨i, hlt⟩ = 0 := hRzero ⟨i, hlt⟩
  simp only [Rfam, List.get_eq_getElem, hget] at hj0
  exact sub_eq_zero.mp hj0

/-- **`MainAirAcceptF` from the honest floor at the corrected shape** — the cons-shaped
`AlgoStarkSoundTransferV3.mainAirAcceptF_of_floor`, descriptor-polymorphic exactly as the landed one. -/
theorem mainAirAcceptF_of_floor_cons
    (d : EffectVmDescriptor2)
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat)
    (proof : BatchProofData ℤ) (pub : WrapPublics ℤ)
    (hacc : verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
        initState logN proof pub = true)
    (t : VmTrace) (ζ Λ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)
    (topen : TableOpening ℤ) (ood vCommitted root : ℤ) (oodRest : List ℤ)
    (idx : Nat) (siblings : List ℤ)
    (hcap : t.rows.length ≤ domainSize)
    (hoodPt : proof.oodPoint = ood :: oodRest)
    (hmem : topen ∈ proof.tableOpenings)
    (hCommitted : merkleRecomputeZ sponge idx vCommitted siblings = root)
    (hOpened : merkleRecomputeZ sponge idx topen.constraintEval siblings = root)
    (hno : ¬ OpeningColl sponge idx topen.constraintEval vCommitted siblings)
    (hlayout : (batchResidual (Rfam d t ζ qp)).eval Λ
        = ((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear))
    (hLam : Λ ∉ exceptionalSet (batchResidual (Rfam d t ζ qp)))
    (hnonexc : ∀ c ∈ d.constraints, isArith c →
        ζ ∉ exceptionalSet (constraintPoly d t c - vanishingPoly t * qp c)) :
    MainAirAcceptF d t :=
  ood_forces_mainAirAccept_field_of_residuals d t hcap ζ qp
    (hood_of_reductions_cons d sponge perm RATE toNat params vk core A initState logN proof pub
      hacc t ζ Λ qp topen ood vCommitted root oodRest idx siblings hoodPt hmem hCommitted hOpened
      hno hlayout hLam)
    hnonexc

/-! ## §5 — the apex, RE-DERIVED from the corrected bundle. -/

/-- **`starkSound_of_friLdtExtractFaithful_transferV3` — `StarkSound` for the deployed `transferV3`
slice from the CORRECTED deployed-verifier extraction bundle.**

ONE honest premise, and it is no longer a refuted floor: the FRI-LDT extraction bundle, which now
carries the PER-RUN opening residual `¬ OpeningColl` in place of the global `Poseidon2SpongeCR` the
commitment binding used to thread. What changed besides: the bundle is indexed by the
verifier `verifyBatch` actually runs, and its OOD conjunct is the deployed 4-lane `d.ζ` rather than a
base-felt singleton — so, unlike the landed bundle, this premise does not force `verifyBatch` to
reject every input (§2, §6).

Per accepting batch: `verifyBatch` acceptance unfolds to `verifyAlgoUnifiedFaithfulExt` acceptance
(the bundle's antecedent) and, through the landed strengthening chain, to `verifyAlgo` acceptance,
which `mainAirAcceptF_of_floor_cons` consumes to DERIVE `MainAirAcceptF` from the bundle's
primitives. The aux legs come straight from the bundle and
`AirLegsDischarged.airAccept_forces_satisfied2_transferV3` closes `Satisfied2`. -/
theorem starkSound_of_friLdtExtractFaithful_transferV3
    (sponge : List Int → Int) (hash : List Int → Int)
    (hfri : FriLdtExtractV3Faithful sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore
      cfgA cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN cfgView cfgExtView) :
    StarkSound hash (fun _ => transferV3) where
  extract := by
    intro pi π hacc
    -- `verifyBatch` accepted ⇒ the deployed extension-faithful verifier returned `true`.
    have hboth :
        (verifyAlgoUnifiedFaithfulExt cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
              cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN
              (cfgView pi π).1 (cfgView pi π).2 (cfgExtView pi π)
          && cfgExtra (cfgView pi π).1 (cfgView pi π).2) = true := by
      unfold verifyBatch at hacc
      by_cases h :
          (verifyAlgoUnifiedFaithfulExt cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
                cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN
                (cfgView pi π).1 (cfgView pi π).2 (cfgExtView pi π)
            && cfgExtra (cfgView pi π).1 (cfgView pi π).2) = true
      · exact h
      · rw [if_neg h] at hacc
        exact absurd hacc (by decide)
    have hExt := (Bool.and_eq_true _ _).mp hboth |>.1
    -- …and therefore also `verifyAlgo` acceptance, through the landed strengthening chain.
    have hAlgo : verifyAlgo cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgChecks cfgInitState cfgLogN
        (cfgView pi π).1 (cfgView pi π).2 = true :=
      verifyAlgoUnified_imp_verifyAlgo cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
        cfgInitState cfgLogN (cfgView pi π).1 (cfgView pi π).2
        (verifyAlgoUnifiedFaithfulExt_imp_verifyAlgoUnified cfgPerm cfgRATE cfgToNat cfgParams
          cfgVk cfgCore cfgA cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN
          (cfgView pi π).1 (cfgView pi π).2 (cfgExtView pi π) hExt)
    obtain ⟨t, ζ, Λ, qp, topen, ood, vCommitted, root, oodRest, idx, siblings,
      hcap, hoodPt, _hzeta, _hlen, hmem, hCommitted, hOpened, hno, hlayout, hLam, hnonexc,
      hbus, hMem, hMap, hPub⟩ := hfri pi π hExt
    exact ⟨fun _ => 0, fun _ => (0, 0), [], t,
      Dregg2.Circuit.AirLegsDischarged.airAccept_forces_satisfied2_transferV3
        hash (fun _ => 0) (fun _ => (0, 0)) t
        (mainAirAcceptF_of_floor_cons transferV3 sponge cfgPerm cfgRATE cfgToNat cfgParams
          cfgVk cfgCore cfgA cfgInitState cfgLogN (cfgView pi π).1 (cfgView pi π).2 hAlgo
          t ζ Λ qp topen ood vCommitted root oodRest idx siblings
          hcap hoodPt hmem hCommitted hOpened hno hlayout hLam hnonexc)
        hbus hMem hMap,
      hPub⟩

/-- **`algoStarkSound_transferV3_cons` — the RELOCATED `AlgoStarkSoundTransferV3.algoStarkSound_transferV3`.**

⚑ WHY IT LIVES HERE. The landed theorem was stated in `AlgoStarkSoundTransferV3`, the module that
DEFINES `FriLdtExtractV3` and is therefore UPSTREAM of this one: the corrected bundle cannot be named
there without a cycle. So the theorem was relocated rather than restated in place — this is its only
home, and the upstream site carries a `⚑ DELETED` pointer, not a deprecated twin.

The statement is the landed one with `FriLdtExtractV3` replaced by `FriLdtExtractV3Cons`: same
conclusion, NO floor hypothesis at all, same generic arguments, and a premise differing in
exactly one conjunct (`oodPoint = ood :: oodRest` instead of `oodPoint = [ood]`) — the shape
`FriVerifier.batchTablesCheck` matches and the bundle's own antecedent forces. `MainAirAcceptF` is
DERIVED per accepting run by `mainAirAcceptF_of_floor_cons`, exactly as the landed proof derived it
by `mainAirAcceptF_of_floor`. -/
theorem algoStarkSound_transferV3_cons
    (sponge : List ℤ → ℤ)
    (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (hfri : FriLdtExtractV3Cons sponge hash perm RATE toNat params vk core A initState logN view) :
    AlgoStarkSound hash (fun _ => transferV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  Dregg2.Circuit.AlgoStarkSoundInstance.algoStarkSound_of_bricks_transferV3
    hash perm RATE toNat params vk (fullChecks core A toNat params.powBits) initState logN view
    (by
      intro pi π hacc
      obtain ⟨t, ζ, Λ, qp, topen, ood, vCommitted, root, oodRest, idx, siblings,
        hcap, hoodPt, hmem, hCommitted, hOpened, hno, hlayout, hLam, hnonexc,
        hbus, hMem, hMap, hPub⟩ := hfri pi π hacc
      exact ⟨t,
        mainAirAcceptF_of_floor_cons transferV3 sponge perm RATE toNat params vk core A
          initState logN (view pi π).1 (view pi π).2 hacc t ζ Λ qp topen ood vCommitted root
          oodRest idx siblings hcap hoodPt hmem hCommitted hOpened hno hlayout hLam hnonexc,
        hbus, hMem, hMap, hPub⟩)

/-! ## §6 — the repair is not a second vacuity. -/

/-- The corrected bundle with the three OOD conjuncts DELETED (`ood`/`oodRest` do not occur anywhere
else in the body). Used only to state the equivalence below. -/
def FriLdtExtractV3FaithfulNoOodShape
    (sponge : List ℤ → ℤ) (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (extCore : ExtFriCore ℤ) (extA : ExtFriArith ℤ) (W : ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) (extView : ExtProofView) : Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core A extCore extA W
        initState logN (view pi π).1 (view pi π).2 (extView pi π) = true →
    ∃ (t : VmTrace) (ζ Λ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)
      (topen : TableOpening ℤ) (vCommitted root : ℤ) (idx : Nat) (siblings : List ℤ),
      t.rows.length ≤ domainSize ∧
      topen ∈ (view pi π).1.tableOpenings ∧
      merkleRecomputeZ sponge idx vCommitted siblings = root ∧
      merkleRecomputeZ sponge idx topen.constraintEval siblings = root ∧
      ¬ OpeningColl sponge idx topen.constraintEval vCommitted siblings ∧
      (batchResidual (Rfam transferV3 t ζ qp)).eval Λ
        = ((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear) ∧
      Λ ∉ exceptionalSet (batchResidual (Rfam transferV3 t ζ qp)) ∧
      (∀ c ∈ transferV3.constraints, isArith c →
          ζ ∉ exceptionalSet (constraintPoly transferV3 t c - vanishingPoly t * qp c)) ∧
      (∀ i < t.rows.length, ∀ c ∈ transferV3.constraints, ¬ isArith c →
          c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)) ∧
      t.tf .memory = [] ∧ t.tf .mapOps = [] ∧
      tracePublishedCommit t = pi.toPublished

/-- **THE NON-VACUITY OF THE REPAIR.** The corrected bundle is EQUIVALENT to the bundle with its
three OOD conjuncts deleted: they are supplied by acceptance itself
(`faithfulExt_accept_gives_cons_shape`), so adding them cannot shrink the set of accepting runs the
premise must cover, and in particular cannot empty it. Contrast §2: the singleton conjunct is
CONTRADICTED by acceptance and empties it completely. -/
theorem friLdtExtractV3Faithful_iff_noOodShape
    (sponge : List ℤ → ℤ) (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (extCore : ExtFriCore ℤ) (extA : ExtFriArith ℤ) (W : ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) (extView : ExtProofView) :
    FriLdtExtractV3Faithful sponge hash perm RATE toNat params vk core A extCore extA W
        initState logN view extView
      ↔ FriLdtExtractV3FaithfulNoOodShape sponge hash perm RATE toNat params vk core A extCore
        extA W initState logN view extView := by
  constructor
  · intro h pi π hacc
    obtain ⟨t, ζ, Λ, qp, topen, _ood, vCommitted, root, _oodRest, idx, siblings,
      hcap, _hoodPt, _hzeta, _hlen, hmem, hCommitted, hOpened, hno, hlayout, hLam, hnonexc,
      hbus, hMem, hMap, hPub⟩ := h pi π hacc
    exact ⟨t, ζ, Λ, qp, topen, vCommitted, root, idx, siblings,
      hcap, hmem, hCommitted, hOpened, hno, hlayout, hLam, hnonexc, hbus, hMem, hMap, hPub⟩
  · intro h pi π hacc
    obtain ⟨ood, oodRest, hcons, hzeta, hlen⟩ :=
      faithfulExt_accept_gives_cons_shape perm RATE toNat params vk core A extCore extA W
        initState logN (view pi π).1 (view pi π).2 (extView pi π) hacc
    obtain ⟨t, ζ, Λ, qp, topen, vCommitted, root, idx, siblings,
      hcap, hmem, hCommitted, hOpened, hno, hlayout, hLam, hnonexc,
      hbus, hMem, hMap, hPub⟩ := h pi π hacc
    exact ⟨t, ζ, Λ, qp, topen, ood, vCommitted, root, oodRest, idx, siblings,
      hcap, hcons, hzeta, hlen, hmem, hCommitted, hOpened, hno, hlayout, hLam, hnonexc,
      hbus, hMem, hMap, hPub⟩

/-! ### The concrete accepting pole (the apex-facing predicate really does accept something).

`cfgPerm`/`cfgParams`/`cfgView`/… are `opaque`, so no accepting run at the DEPLOYED arguments can be
exhibited by anybody. The witness below is at concrete arguments, and it is what shows the corrected
OOD shape is realized on an actual accepting run while the singleton shape is refuted on it. The
fixture mirrors `ExtFieldChallenge`'s `#guard`ed one (its defs are `private` there); here it carries
a `decide` proof, so the acceptance is a theorem, not a command. -/

private def poleV : ExtElem Nat := ⟨[1, 1, 1, 1]⟩
private def poleNegV : ExtElem Nat :=
  ⟨[Dregg2.Circuit.ExtFieldChallenge.P - 1, Dregg2.Circuit.ExtFieldChallenge.P - 1,
    Dregg2.Circuit.ExtFieldChallenge.P - 1, Dregg2.Circuit.ExtFieldChallenge.P - 1]⟩
private def poleBeta : ExtElem Nat := ⟨[2, 1, 0, 0]⟩
private def poleX : ExtElem Nat := ⟨[1, 0, 0, 0]⟩

private def poleCore : ExtFriCore Nat :=
  { compress := fun a b => [a.headD 0 * 7 + b.headD 0 * 13 + 1]
    leafHash := fun e0 e1 => e0.lanes ++ e1.lanes
    domainPoint := fun _ _ => poleX
    domainPointInv := fun _ _ => poleX }

private def poleLayer : ExtLayerOpening Nat :=
  { beta := poleBeta, x := poleX, e0 := poleV, e1 := poleNegV,
    leaf := poleV.lanes ++ poleNegV.lanes, siblings := [] }

private def polePerm : List Nat → List Nat :=
  fun _ => [0, 0, 0, 0, 0, 0, 0, 2] ++ List.replicate 8 0
private def poleRate : Nat := 8
private def poleInit : List Nat := List.replicate 16 0
private def poleParams : FriParams :=
  { logBlowup := 1, numQueries := 1, powBits := 0, maxLogArity := 1,
    logFinalPolyLen := 0, extDeg := 4 }
private def poleVk : RecursionVk Nat := ⟨fun _ => true⟩
private def polePub : WrapPublics Nat := ⟨[7, 8, 9]⟩
private def poleScalarCore : FriCore Nat :=
  { compress := fun a b => [a.headD 0 * 7 + b.headD 0 * 13 + 1]
    foldCombine := fun beta _x e0 e1 => e0 + beta * e1 }

private def poleStub : BatchProofData Nat :=
  { degreeBitsPreamble := [1], baseDegreeBitsPreamble := [1],
    preprocessedWidthPreamble := [0], traceCommit := [91],
    friCommitments := [poleLayer.leaf], finalPoly := [0, 0, 0, 0], queries := [],
    exposedSegment := polePub.segment, quotientCommit := [6], openedEvaluations := [11, 12],
    friLogArities := [1], powWitness := [0] }

private def poleBetaDerived : ExtElem Nat :=
  ⟨(Dregg2.Circuit.FriChallengerUnified.deriveTranscript
    polePerm poleRate id poleParams poleInit 1 poleStub polePub).betas.headD []⟩

private def poleExtLayer : ExtLayerOpening Nat :=
  { poleLayer with beta := poleBetaDerived }

private def poleFinal : ExtElem Nat :=
  extFoldCombine babyBearFriArith Dregg2.Circuit.ExtFieldChallenge.W 4 poleBetaDerived poleX poleX
    poleV poleNegV

private def polePreProof : BatchProofData Nat :=
  { poleStub with
    finalPoly := poleFinal.lanes
    oodPoint := (Dregg2.Circuit.FriChallengerUnified.deriveTranscript
      polePerm poleRate id poleParams poleInit 1 poleStub polePub).ζ }

private def poleQidx : Nat :=
  (Dregg2.Circuit.FriChallengerUnified.deriveTranscript
    polePerm poleRate id poleParams poleInit 1 polePreProof polePub).qidx.headD 0

private def poleScalarL0 : LayerOpening Nat :=
  { beta := poleBetaDerived.lanes.headD 0, x := 1, e0 := poleFinal.lanes.headD 0, e1 := 0,
    leaf := polePreProof.traceCommit, siblings := [] }

private def poleScalarL1 : LayerOpening Nat :=
  { beta := 0, x := 1, e0 := poleFinal.lanes.headD 0, e1 := 0,
    leaf := poleExtLayer.leaf, siblings := [] }

private def polePowMod (m b : Nat) : Nat → Nat
  | 0 => 1 % m
  | n + 1 => (b * polePowMod m b n) % m

private def poleScalarArith : FieldArith Nat :=
  { add := fun a b => (a + b) % 17, mul := fun a b => (a * b) % 17,
    pow := polePowMod 17, zero := 0, one := 1 }

private def poleAlpha : Nat :=
  (Dregg2.Circuit.FriChallengerUnified.deriveTranscript
    polePerm poleRate id poleParams poleInit 1 polePreProof polePub).constraintAlpha.headD 0
private def poleZeta : Nat := polePreProof.oodPoint.headD 0
private def poleVanishing : Nat := (poleZeta % 17 + 16) % 17
private def poleInvVanishing : Nat := polePowMod 17 poleVanishing 15

private def poleAir : Dregg2.Circuit.BatchTablesSingleAir.SingleAirOpening Nat :=
  { zeta := poleZeta, degreeBits := 0, expectedDegreeBits := 0, alpha := poleAlpha,
    constraintEvals := [1], zps := [1], quotientChunks := [poleInvVanishing],
    vanishing := poleVanishing, invVanishing := poleInvVanishing, logupCumSum := 0 }

private def poleProof : BatchProofData Nat :=
  { polePreProof with
    queries := [{ index := poleQidx, layers := [poleScalarL0, poleScalarL1] }],
    singleAirOpenings := [poleAir] }

private def poleExtQuery : ExtQueryOpening Nat :=
  { index := poleQidx,
    initialEval := if poleQidx % 2 = 0 then poleV else poleNegV,
    layers := [poleExtLayer] }

private def poleAlphaExt : ExtElem Nat :=
  ⟨(Dregg2.Circuit.FriChallengerUnified.deriveTranscript
    polePerm poleRate id poleParams poleInit 1 poleProof polePub).constraintAlpha⟩

private def poleExtOne : ExtElem Nat := extOfBase babyBear 4 babyBear.one

private def poleExtAir : ExtSingleAirOpening Nat :=
  { degreeBits := 0, expectedDegreeBits := 0,
    constraintEvals := [poleExtOne, poleExtOne], zps := [poleExtOne],
    quotientChunks := [extAdd babyBear poleAlphaExt poleExtOne],
    logupCumSum := extOfBase babyBear 4 babyBear.zero }

private def poleExtView : ExtVerifierView Nat :=
  { queries := [poleExtQuery], singleAirOpenings := [poleExtAir] }

set_option maxRecDepth 100000 in
/-- **The complete apex-facing predicate ACCEPTS this run** — the continued transcript, the scalar
restriction, the genuine single-AIR quotient identity and the quartic fold all simultaneously. -/
theorem deployed_predicate_accepts_pole :
    verifyAlgoUnifiedFaithfulExt polePerm poleRate id poleParams poleVk poleScalarCore
      poleScalarArith poleCore babyBearFriArith Dregg2.Circuit.ExtFieldChallenge.W poleInit 1
      poleProof polePub poleExtView = true := by decide

/-- **The accepting pole is non-empty.** -/
theorem deployed_accepting_pole_nonempty :
    ∃ (perm : List Nat → List Nat) (RATE : Nat) (toNat : Nat → Nat) (params : FriParams)
      (vk : RecursionVk Nat) (core : FriCore Nat) (A : FieldArith Nat)
      (extCore : ExtFriCore Nat) (extA : ExtFriArith Nat) (Wres : Nat)
      (initState : List Nat) (logN : Nat) (proof : BatchProofData Nat) (pub : WrapPublics Nat)
      (view : ExtVerifierView Nat),
      verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core A extCore extA Wres
        initState logN proof pub view = true :=
  ⟨polePerm, poleRate, id, poleParams, poleVk, poleScalarCore, poleScalarArith, poleCore,
    babyBearFriArith, Dregg2.Circuit.ExtFieldChallenge.W, poleInit, 1, poleProof, polePub,
    poleExtView, deployed_predicate_accepts_pole⟩

/-- **THE INHABITABILITY WITNESS.** On an actual accepting run of the apex-facing predicate, the
CORRECTED OOD shape holds — head lane, transcript identity, `extDeg` lanes — and the SINGLETON shape
is refuted. So the repaired conjunct is realized where the defective one is impossible. -/
theorem corrected_ood_shape_inhabited :
    ∃ (perm : List Nat → List Nat) (RATE : Nat) (toNat : Nat → Nat) (params : FriParams)
      (vk : RecursionVk Nat) (core : FriCore Nat) (A : FieldArith Nat)
      (extCore : ExtFriCore Nat) (extA : ExtFriArith Nat) (Wres : Nat)
      (initState : List Nat) (logN : Nat) (proof : BatchProofData Nat) (pub : WrapPublics Nat)
      (view : ExtVerifierView Nat) (ood : Nat) (oodRest : List Nat),
      verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core A extCore extA Wres
          initState logN proof pub view = true
        ∧ proof.oodPoint = ood :: oodRest
        ∧ ood :: oodRest = (Dregg2.Circuit.FriChallengerUnified.deriveTranscript perm RATE toNat
            params initState logN proof pub).ζ
        ∧ (ood :: oodRest).length = params.extDeg
        ∧ (∀ o : Nat, proof.oodPoint ≠ [o]) := by
  obtain ⟨ood, oodRest, hcons, hzeta, hlen⟩ :=
    faithfulExt_accept_gives_cons_shape polePerm poleRate id poleParams poleVk poleScalarCore
      poleScalarArith poleCore babyBearFriArith Dregg2.Circuit.ExtFieldChallenge.W poleInit 1
      poleProof polePub poleExtView deployed_predicate_accepts_pole
  exact ⟨polePerm, poleRate, id, poleParams, poleVk, poleScalarCore, poleScalarArith, poleCore,
    babyBearFriArith, Dregg2.Circuit.ExtFieldChallenge.W, poleInit, 1, poleProof, polePub,
    poleExtView, ood, oodRest, deployed_predicate_accepts_pole, hcons, hzeta, hlen,
    fun o => faithfulExt_forces_oodPoint_ne_singleton polePerm poleRate id poleParams poleVk
      poleScalarCore poleScalarArith poleCore babyBearFriArith
      Dregg2.Circuit.ExtFieldChallenge.W poleInit 1 poleProof polePub poleExtView
      deployed_predicate_accepts_pole o⟩

/-- **⚑ THE RESIDUAL CAVEAT, AS A THEOREM RATHER THAN A DOC-COMMENT.** The one accepting run of the
apex-facing predicate exhibited anywhere in this tree carries NO table openings at all: `poleProof`
never sets `tableOpenings`, so it is `[]`. Every corrected bundle of this campaign
(`FriLdtExtractV3Cons`, `FriLdtExtractV3Faithful`, `ApexOodLaneRepair.FriLdtExtractCons`,
`FriFsDecodedOodRepair`'s and `OodSingletonRepair`'s `…Cons` forms) RETAINS the conjunct
`topen ∈ (view pi π).1.tableOpenings`. On THIS run that conjunct is refutable, so the corrected
bundles have no exhibited model here either — the same disease, one conjunct over. Exported so the
caveat is CONSUMED as a hypothesis (`PremiseInhabitabilitySweep` §2) instead of restated in prose. -/
theorem deployed_accepting_pole_has_no_tableOpenings :
    ∃ (perm : List Nat → List Nat) (RATE : Nat) (toNat : Nat → Nat) (params : FriParams)
      (vk : RecursionVk Nat) (core : FriCore Nat) (A : FieldArith Nat)
      (extCore : ExtFriCore Nat) (extA : ExtFriArith Nat) (Wres : Nat)
      (initState : List Nat) (logN : Nat) (proof : BatchProofData Nat) (pub : WrapPublics Nat)
      (view : ExtVerifierView Nat),
      verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core A extCore extA Wres
          initState logN proof pub view = true
        ∧ proof.tableOpenings = [] :=
  ⟨polePerm, poleRate, id, poleParams, poleVk, poleScalarCore, poleScalarArith, poleCore,
    babyBearFriArith, Dregg2.Circuit.ExtFieldChallenge.W, poleInit, 1, poleProof, polePub,
    poleExtView, deployed_predicate_accepts_pole, rfl⟩

/-! ## §7 — the separation that makes the verifier-index change one-directional. -/

/-- **The bare and deployed antecedents are NOT interchangeable.** There is a concrete proof the bare
`verifyAlgo` ACCEPTS and the unified (hence faithful, hence extension-faithful) verifier REJECTS —
the free-beta forgery of `FriChallengerUnified`. So a bundle indexed by the bare verifier carries
obligations on runs the deployed-verifier bundle never mentions, and the transports of §2/§3 cannot
be reversed by any acceptance-transport argument. -/
theorem bundles_are_not_interchangeable :
    ∃ (perm : List Nat → List Nat) (RATE : Nat) (toNat : Nat → Nat) (params : FriParams)
      (vk : RecursionVk Nat) (core : FriCore Nat) (A : FieldArith Nat)
      (initState : List Nat) (logN : Nat) (proof : BatchProofData Nat) (pub : WrapPublics Nat),
      verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
          initState logN proof pub = true
        ∧ Dregg2.Circuit.FriChallengerUnified.verifyAlgoUnified perm RATE toNat params vk core A
            initState logN proof pub = false :=
  Dregg2.Circuit.FriChallengerUnified.verifyAlgo_accepts_but_unified_rejects

#assert_axioms deriveTranscript_zeta_length
#assert_axioms faithfulExt_forces_extDeg
#assert_axioms faithfulExt_forces_oodPoint_eq_zeta
#assert_axioms faithfulExt_forces_oodPoint_length
#assert_axioms faithfulExt_forces_oodPoint_ne_singleton
#assert_axioms faithfulExt_accept_gives_cons_shape
#assert_axioms singletonBundle_makes_deployed_verifier_accept_nothing
#assert_axioms friLdtExtractV3_imp_faithfulSingleton
#assert_axioms friLdtExtractV3_makes_verifyBatch_reject_everything
#assert_axioms friLdtExtractV3Cons_imp_faithful
#assert_axioms batchTablesCheck_rejects_tampered_quotient_cons
#assert_axioms verifyAlgo_full_rejects_tampered_quotient_cons
#assert_axioms verifyAlgo_accept_forces_table_identity_cons
#assert_axioms hood_of_reductions_cons
#assert_axioms mainAirAcceptF_of_floor_cons
#assert_axioms starkSound_of_friLdtExtractFaithful_transferV3
#assert_axioms algoStarkSound_transferV3_cons
#assert_axioms friLdtExtractV3Faithful_iff_noOodShape
#assert_axioms deployed_predicate_accepts_pole
#assert_axioms deployed_accepting_pole_nonempty
#assert_axioms corrected_ood_shape_inhabited
#assert_axioms deployed_accepting_pole_has_no_tableOpenings
#assert_axioms bundles_are_not_interchangeable

end Dregg2.Circuit.FriLdtExtractDeployed
