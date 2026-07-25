/-
# `Dregg2.Circuit.ApexOodLaneRepair` — the singleton-OOD wound at the APEX / SOUNDNESS chain:
PROVED, REPAIRED, and shown not to be swapped for a second vacuity.

Three landed sites conclude — or require — that the out-of-domain point is a SINGLETON list of one
BabyBear base felt, `oodPoint = [ood]`:

  * `AlgoStarkSoundGeneral.lean:147` — the `∀ d` extraction bundle `FriLdtExtract`'s OOD conjunct.
    This is a HYPOTHESIS consumed by the general assembler `algoStarkSound_of_memoryLegs` and hence
    by `AlgoStarkSoundKernel`, `AlgoStarkSoundKernelAvail`, `AlgoStarkSoundFanoutMemFree`,
    `AlgoStarkSoundFanoutMemory`, `KernelConfigSoundness`, `KernelConfigSoundnessAvail`,
    `FriDecodedTraceWitness`. SEVERITY: apex-emptying (§2).
  * `DeployedRefinesProof.lean:103` — the `hood` hypothesis of `model_rejects_tampered_quotient`.
  * `FriVerifierBridge.lean:185` — the `hood` hypothesis of `deployed_rejects_tampered_quotient`,
    the file's own named witness that "the algorithm's tooth bites the deployed verifier".
    SEVERITY for the two teeth: claim-hollowing (§6, §7) — their hypothesis is satisfiable ONLY on
    proofs the deployed verifier rejects outright, so neither tooth constrains any deployed-accepting
    run.

The deployed verifier forces FOUR lanes: `CircuitSoundness.verifyBatch` (`:449`) runs
`ExtFieldChallenge.verifyAlgoUnifiedFaithfulExt`, whose conjuncts include `decide (params.extDeg = 4)`
and, through `unifiedTranscriptChecks` (`FriChallengerUnified.lean:122`), `decide (proof.oodPoint = d.ζ)`
with `d.ζ` a `Challenger.sampleExt … params.extDeg` squeeze of provably that length. That chain is the
already-landed `FriLdtExtractDeployed` §1, reused verbatim here.

## §A What is PROVED here about the landed objects (the vacuity, not asserted)

  * `friLdtExtract_makes_deployed_verifier_accept_nothing` — assuming the landed `∀ d` bundle
    `AlgoStarkSoundGeneral.FriLdtExtract`, the predicate `verifyBatch` evaluates returns `false` on
    EVERY input, at every extension instantiation.
  * `friLdtExtract_makes_verifyBatch_reject_everything` — the same at the deployed `cfg*` arguments:
    `verifyBatch vkey pi π = Verdict.reject` for every triple. So every apex conditioned on the
    landed `FriLdtExtract` at deployed args quantifies over an EMPTY accepting set.
  * `landed_bundle_conjunct_refuted_on_an_accepting_run` — sharper, and it does not even need the
    deployed extension verifier: there is a concrete run the bundle's OWN antecedent (the bare
    `verifyAlgo … (fullChecks …)`) ACCEPTS, on which `oodPoint = [ood]` is FALSE for every `ood`.
  * `singleton_oodPoint_forces_deployed_reject` / `singleton_tooth_only_bites_already_rejected` —
    the two teeth's hypothesis forces deployed rejection, i.e. the teeth carry no information about
    any deployed-accepting batch.

The landed definitions are NOT edited (seven modules consume `FriLdtExtract`); they are retained as
the SUBJECTS of the theorems above so the shape cannot be reintroduced silently.

## §B The repair

`FriVerifier.batchTablesCheck` (`:803-808`) matches `| ood :: _` and never wanted a singleton, so the
repair is entirely bundle/hypothesis side:

  * `FriLdtExtractCons` (§3) — the `∀ d` bundle with `oodPoint = ood :: oodRest`; implied by the
    landed `FriLdtExtract` (`friLdtExtract_imp_cons`, a real implication).
  * `hood_of_oodColumnLayout_cons`, `algoStarkSound_of_memoryLegs_cons`,
    `algoStarkSound_of_memoryFree_cons`, `algoStarkSound_transferV3_ofBusModels_cons` (§4) — the
    general assembler re-derived at the corrected shape. Every other input (`BusModelFamily`,
    `MemoryLegs`, `MemMapFree`, the graduated-shape legs) is unchanged and reused as landed.
  * `model_rejects_tampered_quotient_cons` (§6) and `deployed_rejects_tampered_quotient_cons` (§7) —
    the two teeth at ANY nonempty OOD point, with the landed statements re-derived as the
    `oodRest = []` instances.

## §C Why the repair is not a second vacuity (§5, §6, §7)

  * `acceptsFull_gives_cons_shape` — the bundle's OWN antecedent supplies the corrected shape:
    `batchTablesCheck` returns `false` on an empty `oodPoint`, so bare acceptance already forces
    `oodPoint = ood :: oodRest`. The corrected conjunct can therefore never be the reason a premise
    is empty.
  * `friLdtExtractCons_iff_noOodShape` — the corrected bundle is EQUIVALENT to the bundle with the
    OOD conjunct DELETED. The repair adds exactly zero strength.
  * `acceptsFull_cons_shape_inhabited` — a concrete run that the bare verifier really ACCEPTS
    (`decide`-backed, through `FriLdtExtractDeployed.deployed_accepting_pole_nonempty`), on which the
    corrected shape holds and the singleton shape is refuted.
  * For the two teeth (rejection lemmas, where weakening the hypothesis STRENGTHENS the statement)
    the corresponding obligation is that the repaired hypothesis is inhabited at the deployed shape:
    `cons_tooth_hypothesis_inhabited_at_deployed_shape`.

What is NOT claimed: that the whole corrected bundle is satisfiable at the deployed `cfg*` arguments.
Its remaining conjuncts ARE the FRI-LDT floor and `cfgPerm`/`cfgView`/… are `opaque`. The claim is
narrower and exact: the corrected OOD conjunct is IMPLIED by the bundle's antecedent, whereas the
singleton one is CONTRADICTED by it.
-/
import Dregg2.Circuit.AlgoStarkSoundGeneral
import Dregg2.Circuit.FriLdtExtractDeployed
import Dregg2.Circuit.DeployedRefinesProof

namespace Dregg2.Circuit.ApexOodLaneRepair

open Polynomial
open Dregg2.Circuit.FriVerifierBridge (AlgoStarkSound ProofView DeployedRefines)
open Dregg2.Circuit.FriVerifier
  (verifyAlgo BatchProofData WrapPublics FriParams RecursionVk FriCore FieldArith TableOpening
   fullChecks batchTablesCheck deriveTranscript)
open Dregg2.Circuit.CircuitSoundness
  (BatchPublicInputs BatchProof Registry Verdict VerifyKey vkOfRegistry verifyBatch
   tracePublishedCommit cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA cfgExtCore cfgExtA
   cfgExtW cfgInitState cfgLogN cfgView cfgExtView)
open Dregg2.Circuit.DescriptorIR2 (VmTrace EffectVmDescriptor2 envAt VmConstraint2 Lookup)
open Dregg2.Circuit.AirChecksSatisfied (MainAirAcceptF isArith)
open Dregg2.Circuit.RotatedKernelRefinement (transferV3)
open Dregg2.Circuit.TraceColumnInterp (constraintPoly domainSize)
open Dregg2.Circuit.FieldIntegerLift (vanishingPoly ood_forces_mainAirAccept_field_of_residuals)
open Dregg2.Circuit.OodQuotientConsistency (exceptionalSet)
open Dregg2.Circuit.OodCommitmentBinding (merkleRecomputeZ)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.OodColumnLayout (oodBatchResidual)
open Dregg2.Circuit.LogUpColumnLayout (BusModelOk)
open Dregg2.Circuit.AlgoStarkSoundGeneral
  (AcceptsFull FriLdtExtract BusModelFamily MemoryLegs MemMapFree nonArithArm_of_busModels
   memoryLegs_of_lookupShape)
open Dregg2.Circuit.Emit.EffectVmEmit (siteHoldsAll)
open Dregg2.Circuit.ExtFieldChallenge
  (ExtFriCore ExtFriArith ExtVerifierView verifyAlgoUnifiedFaithfulExt
   verifyAlgoUnifiedFaithfulExt_imp_verifyAlgoUnified)
open Dregg2.Circuit.FriChallengerUnified (verifyAlgoUnified_imp_verifyAlgo)
open Dregg2.Circuit.FriLdtExtractDeployed
  (ExtProofView faithfulExt_forces_oodPoint_ne_singleton hood_of_reductions_cons
   deployed_accepting_pole_nonempty corrected_ood_shape_inhabited
   FriLdtExtractV3Cons algoStarkSound_transferV3_cons
   friLdtExtractV3_makes_verifyBatch_reject_everything)
open Dregg2.Circuit.AlgoStarkSoundTransferV3 (Rfam FriLdtExtractV3)
open Dregg2.Circuit.OodSoundnessGame (batchResidual)

set_option autoImplicit false

/-! ## §1 — what the BARE verifier (the bundle's own antecedent) forces about `oodPoint`.

`fullChecks.batchTables` IS `batchTablesCheck` (`FriVerifier.lean:833`), which returns `false` on an
empty `oodPoint` (`FriVerifier.lean:808`). So the bundle's antecedent already delivers the corrected
`ood :: oodRest` shape — this is what makes the §3 repair strength-free. -/

/-- **Bare acceptance forces a NONEMPTY OOD point.** -/
theorem acceptsFull_forces_oodPoint_ne_nil {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat)
    (params : FriParams) (vk : RecursionVk F) (core : FriCore F) (A : FieldArith F)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F)
    (hacc : verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
        initState logN proof pub = true) :
    proof.oodPoint ≠ [] := by
  intro hnil
  have hbt : (fullChecks core A toNat params.powBits).batchTables proof
      (deriveTranscript perm RATE toNat params initState logN proof pub).betas = false := by
    show batchTablesCheck A proof = false
    unfold batchTablesCheck
    rw [hnil]
  rw [show verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
        initState logN proof pub = false by
      unfold verifyAlgo
      simp only [hbt, Bool.and_false, Bool.false_and]] at hacc
  exact absurd hacc (by decide)

/-- **Bare acceptance SUPPLIES the corrected shape.** The `ood :: oodRest` decomposition of the OOD
point is a CONSEQUENCE of the antecedent every bundle in this file quantifies over. -/
theorem acceptsFull_gives_cons_shape {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat)
    (params : FriParams) (vk : RecursionVk F) (core : FriCore F) (A : FieldArith F)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F)
    (hacc : verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
        initState logN proof pub = true) :
    ∃ (ood : F) (oodRest : List F), proof.oodPoint = ood :: oodRest :=
  List.exists_cons_of_ne_nil
    (acceptsFull_forces_oodPoint_ne_nil perm RATE toNat params vk core A initState logN proof pub
      hacc)

/-! ## §2 — SITE 1, THE DEFECT PROVED: the landed `∀ d` bundle empties the deployed verifier. -/

/-- **THE VACUITY AT `AlgoStarkSoundGeneral.lean:147`, PROVED.** Assuming the landed `∀ d`
extraction bundle `FriLdtExtract`, the predicate `verifyBatch` evaluates
(`verifyAlgoUnifiedFaithfulExt`) returns `false` on EVERY `(pi, π)`, at every extension
instantiation. The bundle would have to produce a one-lane OOD point on a run whose acceptance
forces four. -/
theorem friLdtExtract_makes_deployed_verifier_accept_nothing
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (extCore : ExtFriCore ℤ) (extA : ExtFriArith ℤ) (W : ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) (extView : ExtProofView)
    (tr : BatchPublicInputs → BatchProof → VmTrace) (d : EffectVmDescriptor2)
    (h : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr d)
    (pi : BatchPublicInputs) (π : BatchProof) :
    verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core A extCore extA W
      initState logN (view pi π).1 (view pi π).2 (extView pi π) = false := by
  rcases Bool.eq_false_or_eq_true
      (verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core A extCore extA W
        initState logN (view pi π).1 (view pi π).2 (extView pi π)) with hb | hb
  · have hbare : AcceptsFull perm RATE toNat params vk core A initState logN view pi π :=
      verifyAlgoUnified_imp_verifyAlgo perm RATE toNat params vk core A initState logN
        (view pi π).1 (view pi π).2
        (verifyAlgoUnifiedFaithfulExt_imp_verifyAlgoUnified perm RATE toNat params vk core A
          extCore extA W initState logN (view pi π).1 (view pi π).2 (extView pi π) hb)
    obtain ⟨_, _, _, _, ood, _, _, _, _, _, hoodPt, _⟩ := h pi π hbare
    exact absurd hoodPt
      (faithfulExt_forces_oodPoint_ne_singleton perm RATE toNat params vk core A extCore extA W
        initState logN (view pi π).1 (view pi π).2 (extView pi π) hb ood)
  · exact hb

/-- **The apex consequence at the deployed config.** Under the LANDED `FriLdtExtract` at the
deployed `cfg*` arguments — the hypothesis every consumer of `algoStarkSound_of_memoryLegs` /
`algoStarkSound_of_memoryFree` carries — `CircuitSoundness.verifyBatch` returns `Verdict.reject` on
EVERY key/public-input/proof triple, for EVERY descriptor and extracted-trace choice. Any
`AlgoStarkSound`- or `StarkSound`-shaped conclusion drawn from it quantifies over an empty set. -/
theorem friLdtExtract_makes_verifyBatch_reject_everything
    (sponge : List ℤ → ℤ)
    (tr : BatchPublicInputs → BatchProof → VmTrace) (d : EffectVmDescriptor2)
    (h : FriLdtExtract sponge cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
      cfgInitState cfgLogN cfgView tr d)
    (vkey : VerifyKey) (pi : BatchPublicInputs) (π : BatchProof) :
    verifyBatch vkey pi π = Verdict.reject := by
  have hrej := friLdtExtract_makes_deployed_verifier_accept_nothing sponge cfgPerm cfgRATE cfgToNat
    cfgParams cfgVk cfgCore cfgA cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN cfgView cfgExtView
    tr d h pi π
  simp [verifyBatch, hrej]

/-- **The defect does not even need the extension verifier.** There is a concrete run the bundle's
OWN antecedent — the bare `verifyAlgo` at `fullChecks`, `AcceptsFull`'s body — genuinely ACCEPTS, on
which the landed OOD conjunct `oodPoint = [ood]` is FALSE for every `ood`. So the singleton conjunct
is not "an unfaithful but harmless simplification": it is refuted on an inhabited accepting run. -/
theorem landed_bundle_conjunct_refuted_on_an_accepting_run :
    ∃ (perm : List Nat → List Nat) (RATE : Nat) (toNat : Nat → Nat) (params : FriParams)
      (vk : RecursionVk Nat) (core : FriCore Nat) (A : FieldArith Nat)
      (initState : List Nat) (logN : Nat) (proof : BatchProofData Nat) (pub : WrapPublics Nat),
      verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
          initState logN proof pub = true
        ∧ (∀ o : Nat, proof.oodPoint ≠ [o]) := by
  obtain ⟨perm, RATE, toNat, params, vk, core, A, extCore, extA, W, initState, logN, proof, pub,
    view, hacc⟩ := deployed_accepting_pole_nonempty
  refine ⟨perm, RATE, toNat, params, vk, core, A, initState, logN, proof, pub, ?_, ?_⟩
  · exact verifyAlgoUnified_imp_verifyAlgo perm RATE toNat params vk core A initState logN proof pub
      (verifyAlgoUnifiedFaithfulExt_imp_verifyAlgoUnified perm RATE toNat params vk core A
        extCore extA W initState logN proof pub view hacc)
  · exact fun o => faithfulExt_forces_oodPoint_ne_singleton perm RATE toNat params vk core A
      extCore extA W initState logN proof pub view hacc o

/-! ## §3 — SITE 1, THE CORRECTED BUNDLE. -/

/-- **`FriLdtExtractCons` — the corrected `∀ d` extraction bundle.** Added alongside the landed
`AlgoStarkSoundGeneral.FriLdtExtract` (seven modules consume that one; it is not edited). Identical
field-for-field except the OOD conjunct is `oodPoint = ood :: oodRest` — the shape
`FriVerifier.batchTablesCheck` actually matches (`| ood :: _`, `FriVerifier.lean:805`) and the shape
the bundle's own antecedent forces (§1). -/
def FriLdtExtractCons
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : BatchPublicInputs → BatchProof → VmTrace)
    (d : EffectVmDescriptor2) : Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    AcceptsFull perm RATE toNat params vk core A initState logN view pi π →
    ∃ (ζ Λ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)
      (topen : TableOpening ℤ) (ood vCommitted root : ℤ) (oodRest : List ℤ)
      (idx : Nat) (siblings : List ℤ),
      (tr pi π).rows.length ≤ domainSize ∧
      (view pi π).1.oodPoint = ood :: oodRest ∧
      topen ∈ (view pi π).1.tableOpenings ∧
      merkleRecomputeZ sponge idx vCommitted siblings = root ∧
      merkleRecomputeZ sponge idx topen.constraintEval siblings = root ∧
      (oodBatchResidual d (tr pi π) ζ qp).eval Λ
        = ((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear) ∧
      Λ ∉ exceptionalSet (oodBatchResidual d (tr pi π) ζ qp) ∧
      (∀ c ∈ d.constraints, isArith c →
          ζ ∉ exceptionalSet (constraintPoly d (tr pi π) c
                - vanishingPoly (tr pi π) * qp c)) ∧
      tracePublishedCommit (tr pi π) = pi.toPublished

/-- `FriLdtExtract ⟹ FriLdtExtractCons`, by `[ood] = ood :: []`. A real implication: no
contradiction is used, and it holds for every instantiation, including ones where both sides are
inhabited. -/
theorem friLdtExtract_imp_cons
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : BatchPublicInputs → BatchProof → VmTrace) (d : EffectVmDescriptor2)
    (h : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr d) :
    FriLdtExtractCons sponge perm RATE toNat params vk core A initState logN view tr d := by
  intro pi π hacc
  obtain ⟨ζ, Λ, qp, topen, ood, vCommitted, root, idx, siblings,
    hcap, hoodPt, hmem, hCommitted, hOpened, hlayout, hLam, hnonexc, hPub⟩ := h pi π hacc
  exact ⟨ζ, Λ, qp, topen, ood, vCommitted, root, [], idx, siblings,
    hcap, hoodPt, hmem, hCommitted, hOpened, hlayout, hLam, hnonexc, hPub⟩

/-! ## §4 — SITE 1, the assembler RE-DERIVED at the corrected shape. -/

/-- **The `∀ d` OOD modeler at the corrected shape** — the cons-shaped
`OodColumnLayout.hood_of_oodColumnLayout` (`:218`, whose `hoodPt` is the singleton at `:229`).
Nothing in the underlying reduction ever needed a singleton: it is
`FriLdtExtractDeployed.hood_of_reductions_cons` read through
`oodBatchResidual d = batchResidual (Rfam d …)` (definitional). -/
theorem hood_of_oodColumnLayout_cons
    (d : EffectVmDescriptor2)
    (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
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
    (hlayout : (oodBatchResidual d t ζ qp).eval Λ
        = ((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear))
    (hLam : Λ ∉ exceptionalSet (oodBatchResidual d t ζ qp)) :
    ∀ c ∈ d.constraints, isArith c →
      (constraintPoly d t c).eval ζ = (vanishingPoly t).eval ζ * (qp c).eval ζ :=
  hood_of_reductions_cons d sponge hCR perm RATE toNat params vk core A initState logN proof pub
    hacc t ζ Λ qp topen ood vCommitted root oodRest idx siblings hoodPt hmem hCommitted hOpened
    hlayout hLam

/-- **`algoStarkSound_of_memoryLegs_cons` — the `∀ d` assembler from the CORRECTED bundle.**
The exact statement of `AlgoStarkSoundGeneral.algoStarkSound_of_memoryLegs` with `FriLdtExtract`
replaced by `FriLdtExtractCons`. Every other input is the landed one, reused unchanged. -/
theorem algoStarkSound_of_memoryLegs_cons {F : Type*} [Field F] [DecidableEq F]
    (d : EffectVmDescriptor2)
    (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (hash : List ℤ → ℤ) (fp : List ℤ → F) (embed : ℤ → F)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : BatchPublicInputs → BatchProof → VmTrace)
    (hsites : d.hashSites = []) (hranges : d.ranges = [])
    (hfri : FriLdtExtractCons sponge perm RATE toNat params vk core A initState logN view tr d)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr d)
    (hlegs : MemoryLegs hash perm RATE toNat params vk core A initState logN view tr d) :
    AlgoStarkSound hash (fun _ => d) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  Dregg2.Circuit.AlgoStarkSoundInstance.algoStarkSound_of_bricks hash (fun _ => d)
    perm RATE toNat params vk (fullChecks core A toNat params.powBits) initState logN view
    (fun pi π hacc => by
      obtain ⟨ζ, Λ, qp, topen, ood, vCommitted, root, oodRest, idx, siblings,
        hcap, hoodPt, hmem, hCommitted, hOpened, hlayout, hLam, hnonexc, hPub⟩ :=
        hfri pi π hacc
      obtain ⟨minit, mfin, maddrs, hrest, hNodup, hClosed, hDisc, hBal, hMemTF, hMapTF⟩ :=
        hlegs pi π hacc
      have hAir : MainAirAcceptF d (tr pi π) :=
        ood_forces_mainAirAccept_field_of_residuals d (tr pi π) hcap ζ qp
          (hood_of_oodColumnLayout_cons d sponge hCR perm RATE toNat params vk core A initState
            logN (view pi π).1 (view pi π).2 hacc (tr pi π) ζ Λ qp topen ood vCommitted root
            oodRest idx siblings hoodPt hmem hCommitted hOpened hlayout hLam)
          hnonexc
      have harm : ∀ i < (tr pi π).rows.length, ∀ c ∈ d.constraints, ¬ isArith c →
          c.holdsAt hash (tr pi π).tf (envAt (tr pi π) i) (i == 0)
            (i + 1 == (tr pi π).rows.length) :=
        nonArithArm_of_busModels hash fp embed d (tr pi π) (hbusF pi π hacc) hrest
      have hH : ∀ i < (tr pi π).rows.length,
          siteHoldsAll hash (envAt (tr pi π) i) d.hashSites := by
        intro i _; rw [hsites]; trivial
      have hR : ∀ i < (tr pi π).rows.length, ∀ r ∈ d.ranges,
          r.holds (envAt (tr pi π) i) := by
        intro i _ r hr; rw [hranges] at hr; simp at hr
      exact ⟨minit, mfin, maddrs, tr pi π, hAir, harm, hH, hR,
        hNodup, hClosed, hDisc, hBal, hMemTF, hMapTF, hPub⟩)

/-- **`algoStarkSound_of_memoryFree_cons`** — the mem/map-free corollary at the corrected shape;
the exact statement of `AlgoStarkSoundGeneral.algoStarkSound_of_memoryFree` over
`FriLdtExtractCons`. -/
theorem algoStarkSound_of_memoryFree_cons {F : Type*} [Field F] [DecidableEq F]
    (d : EffectVmDescriptor2)
    (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (hash : List ℤ → ℤ) (fp : List ℤ → F) (embed : ℤ → F)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : BatchPublicInputs → BatchProof → VmTrace)
    (hshape : ∀ c ∈ d.constraints, ¬ isArith c → ∃ l : Lookup, c = VmConstraint2.lookup l)
    (hsites : d.hashSites = []) (hranges : d.ranges = [])
    (hfri : FriLdtExtractCons sponge perm RATE toNat params vk core A initState logN view tr d)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr d)
    (hmemfree : MemMapFree perm RATE toNat params vk core A initState logN view tr) :
    AlgoStarkSound hash (fun _ => d) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_of_memoryLegs_cons d sponge hCR hash fp embed perm RATE toNat params vk core A
    initState logN view tr hsites hranges hfri hbusF
    (memoryLegs_of_lookupShape hash perm RATE toNat params vk core A initState logN view tr d
      hshape hmemfree)

/-- **The corrected assembler AT the deployed `transferV3`** — the statement of
`AlgoStarkSoundGeneral.algoStarkSound_transferV3_ofBusModels` over the corrected bundle. -/
theorem algoStarkSound_transferV3_ofBusModels_cons {F : Type*} [Field F] [DecidableEq F]
    (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (hash : List ℤ → ℤ) (fp : List ℤ → F) (embed : ℤ → F)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : BatchPublicInputs → BatchProof → VmTrace)
    (hfri : FriLdtExtractCons sponge perm RATE toNat params vk core A initState logN view tr
        transferV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
        transferV3)
    (hmemfree : MemMapFree perm RATE toNat params vk core A initState logN view tr) :
    AlgoStarkSound hash (fun _ => transferV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_of_memoryFree_cons transferV3 sponge hCR hash fp embed perm RATE toNat params vk
    core A initState logN view tr
    Dregg2.Circuit.AirLegsDischarged.hbus_is_lookup
    Dregg2.Circuit.AirLegsDischarged.transferV3_hashSites
    Dregg2.Circuit.AirLegsDischarged.transferV3_ranges
    hfri hbusF hmemfree

/-! ## §5 — SITE 1: THE REPAIR IS NOT A SECOND VACUITY. -/

/-- The corrected bundle with the OOD-shape conjunct DELETED (`ood`/`oodRest` occur nowhere else in
the body). Used only to state the equivalence below. -/
def FriLdtExtractConsNoOodShape
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : BatchPublicInputs → BatchProof → VmTrace)
    (d : EffectVmDescriptor2) : Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    AcceptsFull perm RATE toNat params vk core A initState logN view pi π →
    ∃ (ζ Λ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)
      (topen : TableOpening ℤ) (vCommitted root : ℤ) (idx : Nat) (siblings : List ℤ),
      (tr pi π).rows.length ≤ domainSize ∧
      topen ∈ (view pi π).1.tableOpenings ∧
      merkleRecomputeZ sponge idx vCommitted siblings = root ∧
      merkleRecomputeZ sponge idx topen.constraintEval siblings = root ∧
      (oodBatchResidual d (tr pi π) ζ qp).eval Λ
        = ((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear) ∧
      Λ ∉ exceptionalSet (oodBatchResidual d (tr pi π) ζ qp) ∧
      (∀ c ∈ d.constraints, isArith c →
          ζ ∉ exceptionalSet (constraintPoly d (tr pi π) c
                - vanishingPoly (tr pi π) * qp c)) ∧
      tracePublishedCommit (tr pi π) = pi.toPublished

/-- **THE NON-VACUITY OF THE REPAIR.** The corrected bundle is EQUIVALENT to the bundle with its OOD
conjunct deleted: the conjunct is supplied by the bundle's own antecedent
(`acceptsFull_gives_cons_shape` — `batchTablesCheck` rejects an empty OOD point), so adding it cannot
shrink the set of accepting runs the premise must cover, and in particular cannot empty it. Contrast
§2: the singleton conjunct is CONTRADICTED on accepting runs and empties the premise completely. -/
theorem friLdtExtractCons_iff_noOodShape
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : BatchPublicInputs → BatchProof → VmTrace) (d : EffectVmDescriptor2) :
    FriLdtExtractCons sponge perm RATE toNat params vk core A initState logN view tr d
      ↔ FriLdtExtractConsNoOodShape sponge perm RATE toNat params vk core A initState logN view
        tr d := by
  constructor
  · intro h pi π hacc
    obtain ⟨ζ, Λ, qp, topen, _ood, vCommitted, root, _oodRest, idx, siblings,
      hcap, _hoodPt, hmem, hCommitted, hOpened, hlayout, hLam, hnonexc, hPub⟩ := h pi π hacc
    exact ⟨ζ, Λ, qp, topen, vCommitted, root, idx, siblings,
      hcap, hmem, hCommitted, hOpened, hlayout, hLam, hnonexc, hPub⟩
  · intro h pi π hacc
    obtain ⟨ood, oodRest, hcons⟩ :=
      acceptsFull_gives_cons_shape perm RATE toNat params vk core A initState logN
        (view pi π).1 (view pi π).2 hacc
    obtain ⟨ζ, Λ, qp, topen, vCommitted, root, idx, siblings,
      hcap, hmem, hCommitted, hOpened, hlayout, hLam, hnonexc, hPub⟩ := h pi π hacc
    exact ⟨ζ, Λ, qp, topen, ood, vCommitted, root, oodRest, idx, siblings,
      hcap, hcons, hmem, hCommitted, hOpened, hlayout, hLam, hnonexc, hPub⟩

/-- **THE CONCRETE INHABITABILITY WITNESS.** On a run the bundle's own antecedent (the bare
`verifyAlgo` at `fullChecks`) really ACCEPTS — obtained from the `decide`-backed accepting pole of
`FriLdtExtractDeployed` — the CORRECTED OOD shape holds and the SINGLETON shape is refuted. The
repaired conjunct is realized exactly where the defective one is impossible. -/
theorem acceptsFull_cons_shape_inhabited :
    ∃ (perm : List Nat → List Nat) (RATE : Nat) (toNat : Nat → Nat) (params : FriParams)
      (vk : RecursionVk Nat) (core : FriCore Nat) (A : FieldArith Nat)
      (initState : List Nat) (logN : Nat) (proof : BatchProofData Nat) (pub : WrapPublics Nat)
      (ood : Nat) (oodRest : List Nat),
      verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
          initState logN proof pub = true
        ∧ proof.oodPoint = ood :: oodRest
        ∧ (∀ o : Nat, proof.oodPoint ≠ [o]) := by
  obtain ⟨perm, RATE, toNat, params, vk, core, A, initState, logN, proof, pub, hbare, hne⟩ :=
    landed_bundle_conjunct_refuted_on_an_accepting_run
  obtain ⟨ood, oodRest, hcons⟩ :=
    acceptsFull_gives_cons_shape perm RATE toNat params vk core A initState logN proof pub hbare
  exact ⟨perm, RATE, toNat, params, vk, core, A, initState, logN, proof, pub, ood, oodRest,
    hbare, hcons, hne⟩

/-! ## §6 — SITE 2: `DeployedRefinesProof.model_rejects_tampered_quotient` (`:103`). -/

/-- **The hollowness of the landed teeth, PROVED.** A proof whose OOD point is a singleton is
REJECTED by the predicate `verifyBatch` evaluates, outright. Both landed teeth (`:103` and `:185`)
are hypothesised on exactly that shape, so neither of them constrains any deployed-accepting batch:
their applicability class is contained in the already-rejected set. -/
theorem singleton_oodPoint_forces_deployed_reject {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (core : FriCore F) (A : FieldArith F)
    (extCore : ExtFriCore F) (extA : ExtFriArith F) (W : F)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F)
    (view : ExtVerifierView F) (ood : F) (hood : proof.oodPoint = [ood]) :
    verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core A extCore extA W
      initState logN proof pub view = false := by
  rcases Bool.eq_false_or_eq_true
      (verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core A extCore extA W
        initState logN proof pub view) with hb | hb
  · exact absurd hood
      (faithfulExt_forces_oodPoint_ne_singleton perm RATE toNat params vk core A extCore extA W
        initState logN proof pub view hb ood)
  · exact hb

/-- **The landed teeth bite only what the deployed verifier already rejected**, at the deployed
`cfg*` arguments: on every batch satisfying their singleton hypothesis, `verifyBatch` returns
`Verdict.reject` with no appeal to the tooth at all. -/
theorem singleton_tooth_only_bites_already_rejected
    (vkey : VerifyKey) (pi : BatchPublicInputs) (π : BatchProof)
    (ood : ℤ) (hood : (cfgView pi π).1.oodPoint = [ood]) :
    verifyBatch vkey pi π = Verdict.reject := by
  have hrej := singleton_oodPoint_forces_deployed_reject cfgPerm cfgRATE cfgToNat cfgParams cfgVk
    cfgCore cfgA cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN (cfgView pi π).1 (cfgView pi π).2
    (cfgExtView pi π) ood hood
  simp [verifyBatch, hrej]

/-- **`model_rejects_tampered_quotient_cons` — SITE 2 REPAIRED.** The deployed-model rejection tooth
at ANY nonempty OOD point (the shape `batchTablesCheck` matches and the shape the deployed 4-lane
`ζ` has), rather than only at a base-felt singleton. Proof: the cons-shaped algorithm tooth
`FriLdtExtractDeployed.verifyAlgo_full_rejects_tampered_quotient_cons` + the model's `&&`. -/
theorem model_rejects_tampered_quotient_cons
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (core : FriCore Int) (A : FieldArith Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (extra : BatchProofData Int → WrapPublics Int → Bool)
    (vk0 : VerifyKey) (pi : BatchPublicInputs) (π : BatchProof)
    (ood : Int) (oodRest : List Int) (hood : (view pi π).1.oodPoint = ood :: oodRest)
    (t : TableOpening Int) (hmem : t ∈ (view pi π).1.tableOpenings)
    (htamper : t.constraintEval ≠ A.mul t.vanishingAtZeta t.quotientAtZeta) :
    Dregg2.Circuit.DeployedRefinesProof.verifyBatchModel perm RATE toNat params vk
        (fullChecks core A toNat params.powBits) initState logN view extra vk0 pi π
      = Verdict.reject := by
  have hrej := Dregg2.Circuit.FriLdtExtractDeployed.verifyAlgo_full_rejects_tampered_quotient_cons
    perm RATE toNat params vk core A initState logN (view pi π).1 (view pi π).2
    ood oodRest hood t hmem htamper
  unfold Dregg2.Circuit.DeployedRefinesProof.verifyBatchModel
  rw [hrej, Bool.false_and, if_neg (by decide)]

/-- The LANDED `model_rejects_tampered_quotient` is the `oodRest = []` instance of the repair — the
relation between the corrected variant and the landed one, in the direction that matters (the repair
is strictly more general; nothing is lost). -/
theorem model_rejects_tampered_quotient_is_instance_of_cons
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (core : FriCore Int) (A : FieldArith Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (extra : BatchProofData Int → WrapPublics Int → Bool)
    (vk0 : VerifyKey) (pi : BatchPublicInputs) (π : BatchProof)
    (ood : Int) (hood : (view pi π).1.oodPoint = [ood])
    (t : TableOpening Int) (hmem : t ∈ (view pi π).1.tableOpenings)
    (htamper : t.constraintEval ≠ A.mul t.vanishingAtZeta t.quotientAtZeta) :
    Dregg2.Circuit.DeployedRefinesProof.verifyBatchModel perm RATE toNat params vk
        (fullChecks core A toNat params.powBits) initState logN view extra vk0 pi π
      = Verdict.reject :=
  model_rejects_tampered_quotient_cons perm RATE toNat params vk core A initState logN view extra
    vk0 pi π ood [] hood t hmem htamper

/-! ## §7 — SITE 3: `FriVerifierBridge.deployed_rejects_tampered_quotient` (`:185`). -/

/-- **`deployed_rejects_tampered_quotient_cons` — SITE 3 REPAIRED.** The algorithm's tooth bites the
DEPLOYED verifier at ANY nonempty OOD point: with the deployed verifier refining the full specified
algorithm, a batch whose mapped proof carries a tampered quotient on some opened table cannot be
accepted — including at the deployed FOUR-LANE OOD shape, which the landed singleton-hypothesised
statement could never reach. -/
theorem deployed_rejects_tampered_quotient_cons
    (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (core : FriCore Int) (A : FieldArith Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (href : DeployedRefines R perm RATE toNat params vk
              (fullChecks core A toNat params.powBits) initState logN view)
    (pi : BatchPublicInputs) (π : BatchProof)
    (ood : Int) (oodRest : List Int) (hood : (view pi π).1.oodPoint = ood :: oodRest)
    (t : TableOpening Int) (hmem : t ∈ (view pi π).1.tableOpenings)
    (htamper : t.constraintEval ≠ A.mul t.vanishingAtZeta t.quotientAtZeta) :
    verifyBatch (vkOfRegistry R) pi π ≠ Verdict.accept := by
  intro hacc
  have halgo := href pi π hacc
  have hrej := Dregg2.Circuit.FriLdtExtractDeployed.verifyAlgo_full_rejects_tampered_quotient_cons
    perm RATE toNat params vk core A initState logN (view pi π).1 (view pi π).2
    ood oodRest hood t hmem htamper
  rw [hrej] at halgo
  exact Bool.noConfusion halgo

/-- The LANDED `deployed_rejects_tampered_quotient` is the `oodRest = []` instance of the repair. -/
theorem deployed_rejects_tampered_quotient_is_instance_of_cons
    (R : Registry)
    (perm : List Int → List Int) (RATE : Nat) (toNat : Int → Nat)
    (params : FriParams) (vk : RecursionVk Int) (core : FriCore Int) (A : FieldArith Int)
    (initState : List Int) (logN : Nat) (view : ProofView)
    (href : DeployedRefines R perm RATE toNat params vk
              (fullChecks core A toNat params.powBits) initState logN view)
    (pi : BatchPublicInputs) (π : BatchProof)
    (ood : Int) (hood : (view pi π).1.oodPoint = [ood])
    (t : TableOpening Int) (hmem : t ∈ (view pi π).1.tableOpenings)
    (htamper : t.constraintEval ≠ A.mul t.vanishingAtZeta t.quotientAtZeta) :
    verifyBatch (vkOfRegistry R) pi π ≠ Verdict.accept :=
  deployed_rejects_tampered_quotient_cons R perm RATE toNat params vk core A initState logN view
    href pi π ood [] hood t hmem htamper

/-- **THE INHABITABILITY OF THE REPAIRED TEETH.** For a rejection tooth, weakening the hypothesis
strengthens the theorem; the obligation is therefore that the repaired hypothesis is actually
REACHED at the deployed shape. It is: on a run the apex-facing predicate ACCEPTS, the OOD point is
`ood :: oodRest` with `params.extDeg` lanes and is NOT a singleton. So `…_cons` has non-empty
applicability exactly where the landed teeth have none. -/
theorem cons_tooth_hypothesis_inhabited_at_deployed_shape :
    ∃ (perm : List Nat → List Nat) (RATE : Nat) (toNat : Nat → Nat) (params : FriParams)
      (vk : RecursionVk Nat) (core : FriCore Nat) (A : FieldArith Nat)
      (extCore : ExtFriCore Nat) (extA : ExtFriArith Nat) (Wres : Nat)
      (initState : List Nat) (logN : Nat) (proof : BatchProofData Nat) (pub : WrapPublics Nat)
      (view : ExtVerifierView Nat) (ood : Nat) (oodRest : List Nat),
      verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core A extCore extA Wres
          initState logN proof pub view = true
        ∧ proof.oodPoint = ood :: oodRest
        ∧ (ood :: oodRest).length = params.extDeg
        ∧ (∀ o : Nat, proof.oodPoint ≠ [o]) := by
  obtain ⟨perm, RATE, toNat, params, vk, core, A, extCore, extA, Wres, initState, logN, proof, pub,
    view, ood, oodRest, hacc, hcons, _hzeta, hlen, hne⟩ := corrected_ood_shape_inhabited
  exact ⟨perm, RATE, toNat, params, vk, core, A, extCore, extA, Wres, initState, logN, proof, pub,
    view, ood, oodRest, hacc, hcons, hlen, hne⟩

/-! ## §8 — ⚑ THE RELOCATED `transferV3` ASSEMBLERS (2026-07-25 `FriLdtExtractV3` cutover).

Two landed theorems rode `AlgoStarkSoundTransferV3.FriLdtExtractV3`, a premise PROVED EMPTY at the
deployed configuration (`deleted_transferV3_assembler_premises_were_empty`, §8.3). NEITHER could be
corrected where it stood, because the corrected objects each needs live DOWNSTREAM of its module:

  * `AlgoStarkSoundTransferV3.algoStarkSound_transferV3` — that module DEFINES `FriLdtExtractV3` and
    is IMPORTED by `FriLdtExtractDeployed`, so `FriLdtExtractV3Cons` cannot be named there at all. It
    was relocated to `FriLdtExtractDeployed.algoStarkSound_transferV3_cons`; the non-emptiness
    receipts for it are §8.2/§8.3 below (they need `acceptsFull_gives_cons_shape`, which lives here).
  * `AlgoStarkSoundGeneral.algoStarkSound_transferV3_subsumed` — needs BOTH `FriLdtExtractV3Cons` and
    a cons-shaped `hood_of_oodColumnLayout`. The latter is §4's `hood_of_oodColumnLayout_cons`, and
    this file imports `AlgoStarkSoundGeneral`, so its relocation lands HERE (§8.1) — relocated rather
    than re-proved through the template's `hood_of_reductions` chain precisely so that "the ∀-d
    modeler subsumes the hand-wired chain" survives the cutover unchanged.

Neither is a deprecated twin: both landed statements are DELETED at their sites, with pointers here.

### §8.1 — the ∀-d-modeler assembler, at the corrected shape. -/

/-- **`algoStarkSound_transferV3_subsumed_cons` — the RELOCATED
`AlgoStarkSoundGeneral.algoStarkSound_transferV3_subsumed`.** The landed statement with
`FriLdtExtractV3` replaced by `FriLdtExtractV3Cons`: same conclusion, same `Poseidon2SpongeCR` floor,
same generic arguments, premise differing in exactly one conjunct (`oodPoint = ood :: oodRest`
instead of `oodPoint = [ood]`). The `hood`/`MainAirAcceptF` wiring is still the GENERAL ∀-d modeler,
now at the corrected shape (`hood_of_oodColumnLayout_cons`), and the bundle's hand-stated layout
equation still feeds it DEFINITIONALLY (`oodBatchResidual transferV3` is `batchResidual
(Rfam transferV3 …)`). The named bus-slot gap of the landed version is untouched by the relocation:
`FriLdtExtractV3Cons` still carries the POST-discharge LogUp arm. -/
theorem algoStarkSound_transferV3_subsumed_cons
    (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
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
        hcap, hoodPt, hmem, hCommitted, hOpened, hlayout, hLam, hnonexc,
        hbus, hMem, hMap, hPub⟩ := hfri pi π hacc
      refine ⟨t, ?_, hbus, hMem, hMap, hPub⟩
      exact ood_forces_mainAirAccept_field_of_residuals transferV3 t hcap ζ qp
        (hood_of_oodColumnLayout_cons transferV3 sponge hCR perm RATE toNat params vk core A
          initState logN (view pi π).1 (view pi π).2 hacc t ζ Λ qp topen ood vCommitted root
          oodRest idx siblings hoodPt hmem hCommitted hOpened hlayout hLam)
        hnonexc)

/-! ### §8.2 — THE MIGRATION OBLIGATION for both relocated assemblers. -/

/-- `FriLdtExtractV3Cons` with the OOD-shape conjunct DELETED (`ood`/`oodRest` occur nowhere else in
the body). Used only to state the equivalence below. -/
def FriLdtExtractV3ConsNoOodShape
    (sponge : List ℤ → ℤ) (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) : Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
        initState logN (view pi π).1 (view pi π).2 = true →
    ∃ (t : VmTrace) (ζ Λ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)
      (topen : TableOpening ℤ) (vCommitted root : ℤ) (idx : Nat) (siblings : List ℤ),
      t.rows.length ≤ domainSize ∧
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

/-- **THE CORRECTED PREMISE ADDS EXACTLY ZERO STRENGTH.** `FriLdtExtractV3Cons` is EQUIVALENT to
itself with the OOD-shape conjunct DELETED. The `mpr` direction is the whole point: the conjunct is
supplied by the bundle's OWN antecedent (`acceptsFull_gives_cons_shape` — `batchTablesCheck` returns
`false` on an empty `oodPoint`), so it can never shrink, let alone empty, the set of accepting runs
the premise must cover. Contrast the DELETED singleton conjunct, which acceptance CONTRADICTS
(`landed_bundle_conjunct_refuted_on_an_accepting_run`, §2). -/
theorem friLdtExtractV3Cons_iff_noOodShape
    (sponge : List ℤ → ℤ) (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) :
    FriLdtExtractV3Cons sponge hash perm RATE toNat params vk core A initState logN view
      ↔ FriLdtExtractV3ConsNoOodShape sponge hash perm RATE toNat params vk core A initState logN
        view := by
  constructor
  · intro h pi π hacc
    obtain ⟨t, ζ, Λ, qp, topen, _ood, vCommitted, root, _oodRest, idx, siblings,
      hcap, _hoodPt, hmem, hCommitted, hOpened, hlayout, hLam, hnonexc,
      hbus, hMem, hMap, hPub⟩ := h pi π hacc
    exact ⟨t, ζ, Λ, qp, topen, vCommitted, root, idx, siblings,
      hcap, hmem, hCommitted, hOpened, hlayout, hLam, hnonexc, hbus, hMem, hMap, hPub⟩
  · intro h pi π hacc
    obtain ⟨ood, oodRest, hcons⟩ :=
      acceptsFull_gives_cons_shape perm RATE toNat params vk core A initState logN
        (view pi π).1 (view pi π).2 hacc
    obtain ⟨t, ζ, Λ, qp, topen, vCommitted, root, idx, siblings,
      hcap, hmem, hCommitted, hOpened, hlayout, hLam, hnonexc,
      hbus, hMem, hMap, hPub⟩ := h pi π hacc
    exact ⟨t, ζ, Λ, qp, topen, ood, vCommitted, root, oodRest, idx, siblings,
      hcap, hcons, hmem, hCommitted, hOpened, hlayout, hLam, hnonexc, hbus, hMem, hMap, hPub⟩

/-- **★ SHARPER, for the relocated template assembler: NO OOD SHAPE IS NEEDED AT ALL.**
`FriLdtExtractDeployed.algoStarkSound_transferV3_cons`'s whole conclusion follows from a premise that
MENTIONS NO OOD-SHAPE CONJUNCT WHATSOEVER. A premise cannot be emptied by a conjunct it does not
contain, so the OOD repair contributes exactly none of whatever residual emptiness remains — all of
it is the FRI-LDT / Merkle / Fiat–Shamir floor. This and `algoStarkSound_transferV3_cons` are
INTERDERIVABLE through `friLdtExtractV3Cons_iff_noOodShape`. It does NOT say the premise is
inhabited; that is the separate, still-open question §8.4 records. -/
theorem algoStarkSound_transferV3_cons_noOodShape
    (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (hfri : FriLdtExtractV3ConsNoOodShape sponge hash perm RATE toNat params vk core A initState
      logN view) :
    AlgoStarkSound hash (fun _ => transferV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_transferV3_cons sponge hCR hash perm RATE toNat params vk core A initState logN
    view
    ((friLdtExtractV3Cons_iff_noOodShape sponge hash perm RATE toNat params vk core A initState
      logN view).mpr hfri)

/-- **★ The same sharper form for the relocated ∀-d-modeler assembler.** Same argument, same
`.mpr`, so `algoStarkSound_transferV3_subsumed_cons` likewise depends on NO OOD-shape conjunct. -/
theorem algoStarkSound_transferV3_subsumed_cons_noOodShape
    (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (hfri : FriLdtExtractV3ConsNoOodShape sponge hash perm RATE toNat params vk core A initState
      logN view) :
    AlgoStarkSound hash (fun _ => transferV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_transferV3_subsumed_cons sponge hCR hash perm RATE toNat params vk core A
    initState logN view
    ((friLdtExtractV3Cons_iff_noOodShape sponge hash perm RATE toNat params vk core A initState
      logN view).mpr hfri)

/-! ### §8.3 — THE RECEIPT for what the two deletions removed. -/

/-- **THE RECEIPT.** The premise BOTH deleted assemblers carried —
`AlgoStarkSoundTransferV3.FriLdtExtractV3` at the deployed `cfg*` arguments — forces
`CircuitSoundness.verifyBatch` to return `Verdict.reject` on EVERY key/public-input/proof triple. So
`AlgoStarkSoundTransferV3.algoStarkSound_transferV3` and
`AlgoStarkSoundGeneral.algoStarkSound_transferV3_subsumed` quantified over an EMPTY accepting set:
both were vacuously true at deployment. That is what the cutover removed, and why no deprecated twin
at the singleton shape is retained anywhere. -/
theorem deleted_transferV3_assembler_premises_were_empty
    (sponge : List ℤ → ℤ) (hash : List ℤ → ℤ)
    (h : FriLdtExtractV3 sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
      cfgInitState cfgLogN cfgView)
    (vkey : VerifyKey) (pi : BatchPublicInputs) (π : BatchProof) :
    verifyBatch vkey pi π = Verdict.reject :=
  friLdtExtractV3_makes_verifyBatch_reject_everything sponge hash h vkey pi π

/-! ### §8.4 — ⚠ THE CAVEAT THE RELOCATIONS INHERIT, AS A THEOREM RATHER THAN A NOTE. -/

/-- **⚠ `FriLdtExtractV3Cons` is refutable at an accepting run with no table openings.** It RETAINS
the conjunct `topen ∈ (view pi π).1.tableOpenings`, and acceptance does NOT supply it: at ANY
arguments admitting an accepting run whose mapped proof opens no table, the migrated premise of both
relocated assemblers is FALSE. The condition is not hypothetical —
`FriLdtExtractDeployed.deployed_accepting_pole_has_no_tableOpenings` exhibits a `decide`-backed
accepting run with `tableOpenings = []`.

That pole is `Nat`-typed at CONCRETE arguments while this premise is `ℤ`-typed and the deployed
instantiation is at the `opaque` `cfg*` ones, so what is refuted is the SCHEMA at the arguments where
anything is exhibitable — NOT the deployed instance, which nobody has decided in either direction.
The cutover therefore trades a premise empty EVERYWHERE for one whose emptiness is CONDITIONAL and
UNDECIDED: a strict improvement, not a closure. -/
theorem friLdtExtractV3Cons_false_of_accepting_run_without_tableOpenings
    (sponge : List ℤ → ℤ) (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hacc : verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
        initState logN (view pi π).1 (view pi π).2 = true)
    (hnil : (view pi π).1.tableOpenings = []) :
    ¬ FriLdtExtractV3Cons sponge hash perm RATE toNat params vk core A initState logN view := by
  intro h
  obtain ⟨_t, _ζ, _Λ, _qp, _topen, _ood, _vC, _root, _oodRest, _idx, _sib,
    _hcap, _hoodPt, hmem, _⟩ := h pi π hacc
  rw [hnil] at hmem
  simp at hmem

/-! ## Kernel-clean keystones. -/

#assert_axioms algoStarkSound_transferV3_subsumed_cons
#assert_axioms friLdtExtractV3Cons_iff_noOodShape
#assert_axioms algoStarkSound_transferV3_cons_noOodShape
#assert_axioms algoStarkSound_transferV3_subsumed_cons_noOodShape
#assert_axioms deleted_transferV3_assembler_premises_were_empty
#assert_axioms friLdtExtractV3Cons_false_of_accepting_run_without_tableOpenings
#assert_axioms acceptsFull_forces_oodPoint_ne_nil
#assert_axioms acceptsFull_gives_cons_shape
#assert_axioms friLdtExtract_makes_deployed_verifier_accept_nothing
#assert_axioms friLdtExtract_makes_verifyBatch_reject_everything
#assert_axioms landed_bundle_conjunct_refuted_on_an_accepting_run
#assert_axioms friLdtExtract_imp_cons
#assert_axioms hood_of_oodColumnLayout_cons
#assert_axioms algoStarkSound_of_memoryLegs_cons
#assert_axioms algoStarkSound_of_memoryFree_cons
#assert_axioms algoStarkSound_transferV3_ofBusModels_cons
#assert_axioms friLdtExtractCons_iff_noOodShape
#assert_axioms acceptsFull_cons_shape_inhabited
#assert_axioms singleton_oodPoint_forces_deployed_reject
#assert_axioms singleton_tooth_only_bites_already_rejected
#assert_axioms model_rejects_tampered_quotient_cons
#assert_axioms model_rejects_tampered_quotient_is_instance_of_cons
#assert_axioms deployed_rejects_tampered_quotient_cons
#assert_axioms deployed_rejects_tampered_quotient_is_instance_of_cons
#assert_axioms cons_tooth_hypothesis_inhabited_at_deployed_shape

end Dregg2.Circuit.ApexOodLaneRepair
