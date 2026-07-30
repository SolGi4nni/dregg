/-
# `Dregg2.Circuit.OodSingletonRepair` — the singleton-OOD wound at the OOD/COLUMN-LAYOUT layer:
diagnosed at both sites, repaired additively, with the repair's inhabitability PROVED.

Companion to `FriLdtExtractDeployed`, which proved the same wound at the STARK apex
(`FriLdtExtractV3` concludes `oodPoint = [ood]`; the deployed verifier forces four lanes; the apex
premise was therefore uninhabitable). This file discharges the two OOD-layer sites that file listed
as still open, and it is careful about a difference between them that matters:

## §A The two sites do NOT have the same polarity

* **`OodColumnLayout.lean:229`** — `hood_of_oodColumnLayout` carries `(hoodPt : proof.oodPoint =
  [ood])` as a **HYPOTHESIS**. A too-strong hypothesis does not make the theorem false or vacuous;
  it makes the tool **UNUSABLE**. Proved below (`hood_of_oodColumnLayout_unusable_at_deployed`): on
  any run the DEPLOYED verifier accepts, that hypothesis is refutable, so every consumer that tries
  to instantiate this lemma at a deployed accepting run must first prove `False`. The same holds of
  `OodExtChallengeLayout.lean:684` (`hood_of_oodColumnLayoutExt`), the extension-typed twin.
  What is NOT claimed: that `hood_of_oodColumnLayout`'s hypotheses are unsatisfiable outright. Its
  acceptance hypothesis is the BARE `verifyAlgo`, which does not pin the lane count.

* **`OodExtChallengeLayout.lean:617`** — `DecodedLdtLinkExt` concludes `(view pi π).1.oodPoint =
  [ood]` in the **CONCLUSION** of its per-batch existential. That is the apex's disease exactly:
  `decodedLdtLinkExt_forces_deployed_reject` proves that assuming `DecodedLdtLinkExt`, the deployed
  `verifyAlgoUnifiedFaithfulExt` returns `false` on every `ColsClose` batch, and
  `decodedLdtLinkExt_makes_verifyBatch_reject_everything` lands that at the deployed `cfg*` arguments:
  `CircuitSoundness.verifyBatch` rejects EVERYTHING. Any apex conditioned on the landed link is
  vacuously true.

Both landed statements are RETAINED verbatim as the subjects of those theorems (they are not edited
here and not edited there), so the shape cannot be reintroduced silently.

## §B What forces four lanes (quoted, not re-derived)

`FriLdtExtractDeployed.faithfulExt_forces_oodPoint_length`: extension-faithful acceptance forces
`proof.oodPoint = d.ζ` (`FriChallengerUnified.unifiedTranscriptChecks`, `:122`) and
`params.extDeg = 4` (`ExtFieldChallenge.lean:762`), with `d.ζ` a `Challenger.sampleExt` squeeze of
provably `params.extDeg` lanes — so `oodPoint.length = 4`, and `oodPoint = [ood]` is impossible.

## §C The repair, and why it is free

The verifier never wanted a singleton: `FriVerifier.batchTablesCheck` (`:803-808`) matches
`| ood :: _` and rejects only on `[]`. So:

  * `hood_of_oodColumnLayoutCons` / `hood_of_oodColumnLayoutExtCons` — the two tools at
    `ood :: oodRest`. Each STRICTLY GENERALIZES its landed form (`…_subsumes_landed`, at
    `oodRest := []`).
  * `hood_of_oodColumnLayout_noOod` / `hood_of_oodColumnLayoutExt_noOod` — the OOD hypothesis
    DELETED outright, because `fullChecks_accept_gives_cons_oodPoint` (§1) derives it from the
    acceptance hypothesis the tool already has. This is the strongest form of "the repair adds zero
    strength": the repaired hypothesis is not merely satisfiable, it is REDUNDANT.
  * `DecodedLdtLinkExtCons` — the corrected link, still delivering the consumer's conclusion
    (`mainAirAcceptF_of_decodedLdtLinkExtCons`). ⛑ 2026-07-30 it also carries the PER-RUN opening
    residual `¬ OpeningColl`, which is what let that consumer drop `Poseidon2SpongeCR`; the two
    transports out of the landed links (`decodedLdtLinkExt_imp_cons`,
    `decodedLdtLinkExtCons_of_decodedLdtLink`) are DELETED with it, since neither landed link
    carries the residual. The corrected link is reached from the corrected BASE link instead
    (`FriFsDecodedOodRepair.decodedLdtLinkExtCons_of_decodedLdtLinkCons`).

## §D THE INHABITABILITY RESULTS (§5) — the part that makes the repair worth anything

  * `decodedLdtLinkExtCons_iff_noOodShape` — the corrected link is EQUIVALENT to the link with its
    OOD conjunct DELETED (`ood` occurs nowhere else in the body), because bare acceptance SUPPLIES
    the cons shape. The repair therefore adds exactly zero strength and can never itself empty a
    premise. This is the analogue, at the same force, of
    `FriLdtExtractDeployed.friLdtExtractV3Faithful_iff_noOodShape`.
  * `bare_accepting_run_with_corrected_ood_shape` — a CONCRETE run, at concrete arguments, that the
    tools' own acceptance hypothesis (`verifyAlgo … (fullChecks …)`) genuinely ACCEPTS, on which the
    corrected `ood :: oodRest` hypothesis holds with `params.extDeg` lanes and the singleton
    hypothesis is REFUTED. So the repaired hypothesis is realized exactly where the defective one is
    impossible. (Transported from `FriLdtExtractDeployed.corrected_ood_shape_inhabited`, whose
    acceptance is a `decide`.)

What is NOT claimed: that any bundle is satisfiable at the DEPLOYED `cfg*` arguments. Those are
`opaque` and no accepting run at them can be exhibited by anyone; and the remaining conjuncts are the
FRI-LDT floor. The claim proved here is the exact one: the corrected shape is implied by acceptance,
the singleton shape contradicts it.

Sorry-free; no `axiom`; no landed definition edited; additive new file.
-/
import Dregg2.Circuit.OodExtChallengeLayout
import Dregg2.Circuit.FriLdtExtractDeployed
import Dregg2.Tactics

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Dregg2.Circuit.OodSingletonRepair

open Polynomial
open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.DescriptorIR2 (VmTrace EffectVmDescriptor2 VmConstraint2 TraceFamily)
open Dregg2.Circuit.AirChecksSatisfied (MainAirAcceptF isArith)
open Dregg2.Circuit.TraceColumnInterp (constraintPoly domainSize)
open Dregg2.Circuit.FieldIntegerLift (vanishingPoly)
open Dregg2.Circuit.OodQuotientConsistency (exceptionalSet)
open Dregg2.Circuit.OodCommitmentBinding
  (merkleRecomputeZ OpeningColl commitmentOpening_binds_of_noColl openingColl_refutes_poseidon2CR)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.FriVerifier
  (verifyAlgo BatchProofData WrapPublics FriParams RecursionVk FriCore FieldArith TableOpening
   fullChecks batchTablesCheck deriveTranscript)
open Dregg2.Circuit.FriVerifierBridge (ProofView)
open Dregg2.Circuit.CircuitSoundness
  (BatchPublicInputs BatchProof VerifyKey Verdict verifyBatch tracePublishedCommit
   cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA cfgExtCore cfgExtA cfgExtW cfgInitState
   cfgLogN cfgView cfgExtView)
open Dregg2.Circuit.OodColumnLayout (oodBatchResidual)
open Dregg2.Circuit.OodExtChallengeLayout
  (liftPoly oodBatchResidualExt oodLayoutExt_debatch mainAirAcceptF_of_oodLayoutExt
   DecodedLdtLinkExt decodedLdtLinkExt_of_decodedLdtLink)
open Dregg2.Circuit.AlgoStarkSoundGeneral (AcceptsFull)
open Dregg2.Circuit.ExtFieldChallenge
  (ExtFriCore ExtFriArith ExtVerifierView verifyAlgoUnifiedFaithfulExt
   verifyAlgoUnifiedFaithfulExt_imp_verifyAlgoUnified)
open Dregg2.Circuit.FriChallengerUnified (verifyAlgoUnified_imp_verifyAlgo)
open Dregg2.Circuit.FriLdtExtractDeployed
  (ExtProofView faithfulExt_forces_oodPoint_ne_singleton faithfulExt_forces_oodPoint_length
   hood_of_reductions_cons verifyAlgo_accept_forces_table_identity_cons
   corrected_ood_shape_inhabited)

/-! ## §1 — What the BARE verifier already forces about `oodPoint`: it is NONEMPTY.

`batchTablesCheck` (`FriVerifier.lean:803-808`) matches `| ood :: _` and returns `false` on `[]` —
"a missing OOD point is malformed and rejects". So the cons shape is not an extra demand on any
theorem that already assumes `verifyAlgo … (fullChecks …) = true`: it is a CONSEQUENCE of it. This
is what makes every repair below strength-free. -/

/-- `batchTablesCheck` rejects an EMPTY OOD point. -/
theorem batchTablesCheck_nil {F : Type} [DecidableEq F] (A : FieldArith F)
    (proof : BatchProofData F) (hnil : proof.oodPoint = []) :
    batchTablesCheck A proof = false := by
  unfold batchTablesCheck
  rw [hnil]

/-- **Bare acceptance forces a NONEMPTY out-of-domain point.** -/
theorem fullChecks_accept_forces_oodPoint_ne_nil {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat)
    (params : FriParams) (vk : RecursionVk F) (core : FriCore F) (A : FieldArith F)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F)
    (hacc : verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
        initState logN proof pub = true) :
    proof.oodPoint ≠ [] := by
  intro hnil
  have hbt : (fullChecks core A toNat params.powBits).batchTables proof
      (deriveTranscript perm RATE toNat params initState logN proof pub).betas = false :=
    batchTablesCheck_nil A proof hnil
  unfold verifyAlgo at hacc
  simp only [hbt, Bool.and_false, Bool.false_and] at hacc
  exact absurd hacc (by decide)

/-- **⚑ THE CONS SHAPE IS SUPPLIED BY ACCEPTANCE.** Every run the bare verifier accepts has an OOD
point of the form `ood :: oodRest`. Every `hoodPt : oodPoint = ood :: oodRest` hypothesis below is
therefore REDUNDANT given the acceptance hypothesis that already sits beside it. -/
theorem fullChecks_accept_gives_cons_oodPoint {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat)
    (params : FriParams) (vk : RecursionVk F) (core : FriCore F) (A : FieldArith F)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F)
    (hacc : verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
        initState logN proof pub = true) :
    ∃ (ood : F) (oodRest : List F), proof.oodPoint = ood :: oodRest :=
  List.exists_cons_of_ne_nil
    (fullChecks_accept_forces_oodPoint_ne_nil perm RATE toNat params vk core A initState logN
      proof pub hacc)

/-! ## §2 — SITE `OodColumnLayout.lean:229`: a HYPOTHESIS no deployed run can discharge. -/

/-- **THE DEFECT AT SITE 1, PROVED.** `OodColumnLayout.hood_of_oodColumnLayout` (`:229`) demands
`proof.oodPoint = [ood]`. On any run the DEPLOYED verifier accepts, that demand is REFUTABLE — so
instantiating the landed tool at a deployed accepting run requires proving `False` first. The tool is
unusable exactly where the apex needs it. (This is a usability defect, not a false theorem: the
landed statement's own acceptance hypothesis is the BARE `verifyAlgo`, which does not pin the lane
count, so no claim is made that its hypotheses are unsatisfiable outright.) -/
theorem hood_of_oodColumnLayout_unusable_at_deployed
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (extCore : ExtFriCore ℤ) (extA : ExtFriArith ℤ) (W : ℤ)
    (initState : List ℤ) (logN : Nat)
    (proof : BatchProofData ℤ) (pub : WrapPublics ℤ) (view : ExtVerifierView ℤ)
    (hdep : verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core A extCore extA W
        initState logN proof pub view = true)
    (ood : ℤ) (hoodPt : proof.oodPoint = [ood]) : False :=
  faithfulExt_forces_oodPoint_ne_singleton perm RATE toNat params vk core A extCore extA W
    initState logN proof pub view hdep ood hoodPt

/-- The same fact in lane-count form: a deployed accepting run's OOD point has FOUR lanes, so the
landed hypothesis is off by three. -/
theorem deployed_oodPoint_length_four
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (extCore : ExtFriCore ℤ) (extA : ExtFriArith ℤ) (W : ℤ)
    (initState : List ℤ) (logN : Nat)
    (proof : BatchProofData ℤ) (pub : WrapPublics ℤ) (view : ExtVerifierView ℤ)
    (hdep : verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core A extCore extA W
        initState logN proof pub view = true) :
    proof.oodPoint.length = 4 :=
  faithfulExt_forces_oodPoint_length perm RATE toNat params vk core A extCore extA W
    initState logN proof pub view hdep

/-- **THE REPAIR AT SITE 1** — `hood_of_oodColumnLayout` at the shape `batchTablesCheck` actually
matches. Identical hypotheses except `hoodPt : proof.oodPoint = ood :: oodRest`; identical
conclusion. The landed statement is the `oodRest := []` instance (`…_subsumes_landed`). -/
theorem hood_of_oodColumnLayoutCons
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
    (hlayout : (oodBatchResidual d t ζ qp).eval Λ
        = ((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear))
    (hLam : Λ ∉ exceptionalSet (oodBatchResidual d t ζ qp)) :
    ∀ c ∈ d.constraints, isArith c →
      (constraintPoly d t c).eval ζ = (vanishingPoly t).eval ζ * (qp c).eval ζ :=
  hood_of_reductions_cons d sponge perm RATE toNat params vk core A initState logN proof pub
    hacc t ζ Λ qp topen ood vCommitted root oodRest idx siblings hoodPt hmem hCommitted hOpened
    hno hlayout hLam

/-- **The corrected tool SUBSUMES the landed one**: `OodColumnLayout.hood_of_oodColumnLayout`'s
statement verbatim, re-proved as the `oodRest := []` instance of the repair. So nothing is lost by
consumers moving to the cons form, and the relation between landed and corrected is an equality of
instances, not a coincidence. -/
theorem hood_of_oodColumnLayoutCons_subsumes_landed
    (d : EffectVmDescriptor2)
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat)
    (proof : BatchProofData ℤ) (pub : WrapPublics ℤ)
    (hacc : verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
        initState logN proof pub = true)
    (t : VmTrace) (ζ Λ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)
    (topen : TableOpening ℤ) (ood vCommitted root : ℤ) (idx : Nat) (siblings : List ℤ)
    (hoodPt : proof.oodPoint = [ood])
    (hmem : topen ∈ proof.tableOpenings)
    (hCommitted : merkleRecomputeZ sponge idx vCommitted siblings = root)
    (hOpened : merkleRecomputeZ sponge idx topen.constraintEval siblings = root)
    (hno : ¬ OpeningColl sponge idx topen.constraintEval vCommitted siblings)
    (hlayout : (oodBatchResidual d t ζ qp).eval Λ
        = ((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear))
    (hLam : Λ ∉ exceptionalSet (oodBatchResidual d t ζ qp)) :
    ∀ c ∈ d.constraints, isArith c →
      (constraintPoly d t c).eval ζ = (vanishingPoly t).eval ζ * (qp c).eval ζ :=
  hood_of_oodColumnLayoutCons d sponge perm RATE toNat params vk core A initState logN proof pub
    hacc t ζ Λ qp topen ood vCommitted root [] idx siblings hoodPt hmem hCommitted hOpened
    hno hlayout hLam

/-- **⚑ THE STRONGEST FORM OF THE REPAIR AT SITE 1: the OOD hypothesis DELETED.** Nothing about the
OOD point's shape needs to be assumed at all — §1 derives the cons shape from the acceptance
hypothesis the tool already carries. A hypothesis that a theorem can prove for itself cannot be the
reason any premise is empty, so this form is unconditionally free of the wound. -/
theorem hood_of_oodColumnLayout_noOod
    (d : EffectVmDescriptor2)
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat)
    (proof : BatchProofData ℤ) (pub : WrapPublics ℤ)
    (hacc : verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
        initState logN proof pub = true)
    (t : VmTrace) (ζ Λ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)
    (topen : TableOpening ℤ) (vCommitted root : ℤ) (idx : Nat) (siblings : List ℤ)
    (hmem : topen ∈ proof.tableOpenings)
    (hCommitted : merkleRecomputeZ sponge idx vCommitted siblings = root)
    (hOpened : merkleRecomputeZ sponge idx topen.constraintEval siblings = root)
    (hno : ¬ OpeningColl sponge idx topen.constraintEval vCommitted siblings)
    (hlayout : (oodBatchResidual d t ζ qp).eval Λ
        = ((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear))
    (hLam : Λ ∉ exceptionalSet (oodBatchResidual d t ζ qp)) :
    ∀ c ∈ d.constraints, isArith c →
      (constraintPoly d t c).eval ζ = (vanishingPoly t).eval ζ * (qp c).eval ζ := by
  obtain ⟨ood, oodRest, hoodPt⟩ :=
    fullChecks_accept_gives_cons_oodPoint perm RATE toNat params vk core A initState logN
      proof pub hacc
  exact hood_of_oodColumnLayoutCons d sponge perm RATE toNat params vk core A initState logN
    proof pub hacc t ζ Λ qp topen ood vCommitted root oodRest idx siblings hoodPt hmem hCommitted
    hOpened hno hlayout hLam

/-! ## §3 — SITE `OodExtChallengeLayout.lean:684`: the extension-typed twin of §2. -/

/-- **THE REPAIR AT `hood_of_oodColumnLayoutExt`** — extension-typed challenges, cons-shaped OOD
point. Same crypto composition as the landed proof (table identity + Poseidon2-CR binding ⟹ the
layout right-hand side is `0` ⟹ de-batch over `E`), with the singleton demand removed. -/
theorem hood_of_oodColumnLayoutExtCons (E : Type*) [Field E] [Algebra BabyBear E] [DecidableEq E]
    (d : EffectVmDescriptor2)
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat)
    (proof : BatchProofData ℤ) (pub : WrapPublics ℤ)
    (hacc : verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
        initState logN proof pub = true)
    (t : VmTrace) (ζ Λ : E) (qp : VmConstraint2 → Polynomial E)
    (topen : TableOpening ℤ) (ood vCommitted root : ℤ) (oodRest : List ℤ)
    (idx : Nat) (siblings : List ℤ)
    (hoodPt : proof.oodPoint = ood :: oodRest)
    (hmem : topen ∈ proof.tableOpenings)
    (hCommitted : merkleRecomputeZ sponge idx vCommitted siblings = root)
    (hOpened : merkleRecomputeZ sponge idx topen.constraintEval siblings = root)
    (hno : ¬ OpeningColl sponge idx topen.constraintEval vCommitted siblings)
    (hlayout : (oodBatchResidualExt E d t ζ qp).eval Λ
        = algebraMap BabyBear E (((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear)))
    (hLam : Λ ∉ exceptionalSet (oodBatchResidualExt E d t ζ qp)) :
    ∀ c ∈ d.constraints, isArith c →
      (liftPoly E (constraintPoly d t c)).eval ζ
        = (liftPoly E (vanishingPoly t)).eval ζ * (qp c).eval ζ := by
  have htable : topen.constraintEval = A.mul topen.vanishingAtZeta topen.quotientAtZeta :=
    verifyAlgo_accept_forces_table_identity_cons perm RATE toNat params vk core A initState logN
      proof pub ood oodRest hoodPt topen hmem hacc
  have hbind : topen.constraintEval = vCommitted :=
    commitmentOpening_binds_of_noColl sponge hno hCommitted hOpened
  have hvc : vCommitted = A.mul topen.vanishingAtZeta topen.quotientAtZeta := hbind.symm.trans htable
  have heval : (oodBatchResidualExt E d t ζ qp).eval Λ = 0 := by
    rw [hlayout, hvc, sub_self, map_zero]
  exact oodLayoutExt_debatch d t ζ qp Λ heval hLam

/-- **The extension-typed OOD hypothesis, DELETED** — same argument as `hood_of_oodColumnLayout_noOod`:
acceptance supplies the shape. -/
theorem hood_of_oodColumnLayoutExt_noOod (E : Type*) [Field E] [Algebra BabyBear E] [DecidableEq E]
    (d : EffectVmDescriptor2)
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat)
    (proof : BatchProofData ℤ) (pub : WrapPublics ℤ)
    (hacc : verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
        initState logN proof pub = true)
    (t : VmTrace) (ζ Λ : E) (qp : VmConstraint2 → Polynomial E)
    (topen : TableOpening ℤ) (vCommitted root : ℤ) (idx : Nat) (siblings : List ℤ)
    (hmem : topen ∈ proof.tableOpenings)
    (hCommitted : merkleRecomputeZ sponge idx vCommitted siblings = root)
    (hOpened : merkleRecomputeZ sponge idx topen.constraintEval siblings = root)
    (hno : ¬ OpeningColl sponge idx topen.constraintEval vCommitted siblings)
    (hlayout : (oodBatchResidualExt E d t ζ qp).eval Λ
        = algebraMap BabyBear E (((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear)))
    (hLam : Λ ∉ exceptionalSet (oodBatchResidualExt E d t ζ qp)) :
    ∀ c ∈ d.constraints, isArith c →
      (liftPoly E (constraintPoly d t c)).eval ζ
        = (liftPoly E (vanishingPoly t)).eval ζ * (qp c).eval ζ := by
  obtain ⟨ood, oodRest, hoodPt⟩ :=
    fullChecks_accept_gives_cons_oodPoint perm RATE toNat params vk core A initState logN
      proof pub hacc
  exact hood_of_oodColumnLayoutExtCons E d sponge perm RATE toNat params vk core A initState
    logN proof pub hacc t ζ Λ qp topen ood vCommitted root oodRest idx siblings hoodPt hmem
    hCommitted hOpened hno hlayout hLam

/-! ## §4 — SITE `OodExtChallengeLayout.lean:617`: `DecodedLdtLinkExt`'s singleton CONCLUSION, and
the vacuity it causes. -/

section Link

open Dregg2.Circuit.FriBatchedOracle (MatrixOracle)
open Dregg2.Circuit.FriDeployedRateInstance (friSetupDeployed)
open Dregg2.Circuit.FriDecodedTraceWitness (decodedTr DecodedLdtLink decodedTr_rows_le)

/-- **THE VACUITY AT SITE 2, PROVED.** Assume the LANDED `DecodedLdtLinkExt` (whose per-batch
existential concludes `(view pi π).1.oodPoint = [ood]`, `OodExtChallengeLayout.lean:617`). Then on
every `ColsClose` batch the DEPLOYED verifier `verifyAlgoUnifiedFaithfulExt` returns `false`: its
acceptance would imply bare acceptance (`AcceptsFull`, the link's antecedent), the link would deliver
a one-lane OOD point, and acceptance forces four. -/
theorem decodedLdtLinkExt_forces_deployed_reject
    (E : Type*) [Field E] [Algebra BabyBear E] [DecidableEq E] {numCols : ℕ}
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (extCore : ExtFriCore ℤ) (extA : ExtFriArith ℤ) (W : ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) (extView : ExtProofView)
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (d : EffectVmDescriptor2)
    (h : DecodedLdtLinkExt E sponge perm RATE toNat params vk core A initState logN view
      oracle pubA tfam d)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hcols : MatrixOracle.ColsClose friSetupDeployed.C 7340032 (oracle pi π)) :
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
    obtain ⟨_, _, _, _, ood, _, _, _, _, hoodPt, _⟩ := h pi π hbare hcols
    exact absurd hoodPt
      (faithfulExt_forces_oodPoint_ne_singleton perm RATE toNat params vk core A extCore extA W
        initState logN (view pi π).1 (view pi π).2 (extView pi π) hb ood)
  · exact hb

/-- **The apex consequence at the DEPLOYED configuration.** Under the landed `DecodedLdtLinkExt` at
the deployed `cfg*` arguments, `CircuitSoundness.verifyBatch` returns `Verdict.reject` on every
key/public-input/proof triple whose committed matrix is `ColsClose`. Any `StarkSound`-shaped
conclusion drawn from that link therefore quantifies over an empty set of accepting batches. -/
theorem decodedLdtLinkExt_makes_verifyBatch_reject_everything
    (E : Type*) [Field E] [Algebra BabyBear E] [DecidableEq E] {numCols : ℕ}
    (sponge : List ℤ → ℤ)
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (d : EffectVmDescriptor2)
    (h : DecodedLdtLinkExt E sponge cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
      cfgInitState cfgLogN cfgView oracle pubA tfam d)
    (vkey : VerifyKey) (pi : BatchPublicInputs) (π : BatchProof)
    (hcols : MatrixOracle.ColsClose friSetupDeployed.C 7340032 (oracle pi π)) :
    verifyBatch vkey pi π = Verdict.reject := by
  have hrej := decodedLdtLinkExt_forces_deployed_reject E sponge cfgPerm cfgRATE cfgToNat cfgParams
    cfgVk cfgCore cfgA cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN cfgView cfgExtView
    oracle pubA tfam d h pi π hcols
  simp [verifyBatch, hrej]

/-- **`DecodedLdtLinkExtCons` — the CORRECTED link.** `OodExtChallengeLayout.DecodedLdtLinkExt`
conjunct-for-conjunct, with the single change that the OOD conjunct is `oodPoint = ood :: oodRest`
(the shape `FriVerifier.batchTablesCheck` matches, `:806`) instead of the base-felt singleton. The
challenge typing, the deployed single-felt opening/Merkle conjuncts, and the extension-typed
non-exceptionality conditions are unchanged — this file repairs the LANE COUNT, not the felt width
(which `OodExtChallengeLayout`'s header names as a separate open wound). -/
def DecodedLdtLinkExtCons (E : Type*) [Field E] [Algebra BabyBear E] [DecidableEq E] {numCols : ℕ}
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (d : EffectVmDescriptor2) : Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    AcceptsFull perm RATE toNat params vk core A initState logN view pi π →
    MatrixOracle.ColsClose friSetupDeployed.C 7340032 (oracle pi π) →
    ∃ (ζ Λ : E) (qp : VmConstraint2 → Polynomial E)
      (topen : TableOpening ℤ) (ood vCommitted root : ℤ) (oodRest : List ℤ)
      (idx : Nat) (siblings : List ℤ),
      (view pi π).1.oodPoint = ood :: oodRest ∧
      topen ∈ (view pi π).1.tableOpenings ∧
      merkleRecomputeZ sponge idx vCommitted siblings = root ∧
      merkleRecomputeZ sponge idx topen.constraintEval siblings = root ∧
      ¬ OpeningColl sponge idx topen.constraintEval vCommitted siblings ∧
      (oodBatchResidualExt E d (decodedTr oracle pubA tfam pi π) ζ qp).eval Λ
        = algebraMap BabyBear E (((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear)) ∧
      Λ ∉ exceptionalSet (oodBatchResidualExt E d (decodedTr oracle pubA tfam pi π) ζ qp) ∧
      (∀ c ∈ d.constraints, isArith c →
          ζ ∉ exceptionalSet
            (liftPoly E (constraintPoly d (decodedTr oracle pubA tfam pi π) c)
              - liftPoly E (vanishingPoly (decodedTr oracle pubA tfam pi π)) * qp c)) ∧
      tracePublishedCommit (decodedTr oracle pubA tfam pi π) = pi.toPublished

/-! ⚑ **DELETED 2026-07-30 — `decodedLdtLinkExt_imp_cons` and
`decodedLdtLinkExtCons_of_decodedLdtLink`.**

`DecodedLdtLinkExtCons` now carries the PER-RUN opening residual
`¬ OpeningColl sponge idx topen.constraintEval vCommitted siblings`, at the witnesses its own
existential produces — the honest replacement for the refuted `Poseidon2SpongeCR` floor that
`mainAirAcceptF_of_decodedLdtLinkExtCons` used to buy its Merkle binding with. Neither the landed
`DecodedLdtLinkExt` nor the base-typed `DecodedLdtLink` carries that conjunct, so neither implication
is provable any more, and restoring either would mean assuming non-collision at EVERY opening
reaching a common root — the global Merkle-binding floor under another name.

WHAT WAS LOST: transports out of two premises this file and its sibling PROVE force
`CircuitSoundness.verifyBatch` to reject every close run at the deployed arguments
(`decodedLdtLinkExt_makes_verifyBatch_reject_everything`,
`FriFsDecodedOodRepair.decodedLdtLink_makes_verifyBatch_reject_every_close_run`). The corrected link
is still REACHED, from the corrected base link, by
`FriFsDecodedOodRepair.decodedLdtLinkExtCons_of_decodedLdtLinkCons` — which now carries the residual
through instead of dropping it. -/

/-- **THE CONSUMER SURVIVES THE REPAIR.** The corrected link delivers exactly what the landed one
delivered: the base-field per-row AIR acceptance on the decoded trace. Same crypto composition, with
`verifyAlgo_accept_forces_table_identity_cons` in place of the singleton-shaped table lemma. -/
theorem mainAirAcceptF_of_decodedLdtLinkExtCons
    (E : Type*) [Field E] [Algebra BabyBear E] [DecidableEq E] {numCols : ℕ}
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (d : EffectVmDescriptor2)
    (hlink : DecodedLdtLinkExtCons E sponge perm RATE toNat params vk core A initState logN view
      oracle pubA tfam d)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hacc : AcceptsFull perm RATE toNat params vk core A initState logN view pi π)
    (hcols : MatrixOracle.ColsClose friSetupDeployed.C 7340032 (oracle pi π)) :
    MainAirAcceptF d (decodedTr oracle pubA tfam pi π) := by
  obtain ⟨ζ, Λ, qp, topen, ood, vCommitted, root, oodRest, idx, siblings,
    hoodPt, hmem, hCommitted, hOpened, hnoOpen, hlayout, hLam, hnonexc, -⟩ := hlink pi π hacc hcols
  have htable : topen.constraintEval = A.mul topen.vanishingAtZeta topen.quotientAtZeta :=
    verifyAlgo_accept_forces_table_identity_cons perm RATE toNat params vk core A initState logN
      (view pi π).1 (view pi π).2 ood oodRest hoodPt topen hmem hacc
  -- ⛑ PORTED 2026-07-30: the per-run residual comes OFF THE BUNDLE now, at the witnesses the
  -- bundle's own existential named. The inline `openingColl_refutes_poseidon2CR … hCR` bridge that
  -- stood here is gone, and with it the refuted floor binder.
  have hbind : topen.constraintEval = vCommitted :=
    commitmentOpening_binds_of_noColl sponge hnoOpen hCommitted hOpened
  have hvc : vCommitted = A.mul topen.vanishingAtZeta topen.quotientAtZeta := hbind.symm.trans htable
  have heval : (oodBatchResidualExt E d (decodedTr oracle pubA tfam pi π) ζ qp).eval Λ = 0 := by
    rw [hlayout, hvc, sub_self, map_zero]
  exact mainAirAcceptF_of_oodLayoutExt d _ (decodedTr_rows_le oracle pubA tfam pi π)
    ζ Λ qp heval hLam hnonexc

/-! ## §5 — ⚑ THE REPAIR IS NOT A SECOND VACUITY. -/

/-- `DecodedLdtLinkExtCons` with the OOD conjunct DELETED (`ood`/`oodRest` occur nowhere else in the
body — `vCommitted`, `root`, `idx`, `siblings` carry the Merkle conjuncts, and `ood` appeared only in
the deleted line). Used only to state the equivalence below. -/
def DecodedLdtLinkExtNoOodShape
    (E : Type*) [Field E] [Algebra BabyBear E] [DecidableEq E] {numCols : ℕ}
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (d : EffectVmDescriptor2) : Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    AcceptsFull perm RATE toNat params vk core A initState logN view pi π →
    MatrixOracle.ColsClose friSetupDeployed.C 7340032 (oracle pi π) →
    ∃ (ζ Λ : E) (qp : VmConstraint2 → Polynomial E)
      (topen : TableOpening ℤ) (vCommitted root : ℤ) (idx : Nat) (siblings : List ℤ),
      topen ∈ (view pi π).1.tableOpenings ∧
      merkleRecomputeZ sponge idx vCommitted siblings = root ∧
      merkleRecomputeZ sponge idx topen.constraintEval siblings = root ∧
      ¬ OpeningColl sponge idx topen.constraintEval vCommitted siblings ∧
      (oodBatchResidualExt E d (decodedTr oracle pubA tfam pi π) ζ qp).eval Λ
        = algebraMap BabyBear E (((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear)) ∧
      Λ ∉ exceptionalSet (oodBatchResidualExt E d (decodedTr oracle pubA tfam pi π) ζ qp) ∧
      (∀ c ∈ d.constraints, isArith c →
          ζ ∉ exceptionalSet
            (liftPoly E (constraintPoly d (decodedTr oracle pubA tfam pi π) c)
              - liftPoly E (vanishingPoly (decodedTr oracle pubA tfam pi π)) * qp c)) ∧
      tracePublishedCommit (decodedTr oracle pubA tfam pi π) = pi.toPublished

/-- **⚑ THE NON-VACUITY OF THE REPAIR.** The corrected link is EQUIVALENT to the link with its OOD
conjunct DELETED: the cons shape is supplied by the link's own antecedent (`AcceptsFull` ⟹
`fullChecks_accept_gives_cons_oodPoint`), so adding it cannot shrink the set of runs the premise must
cover, and in particular cannot empty it. Contrast §4: the singleton conjunct is CONTRADICTED by
deployed acceptance and empties it completely.

This is the exact analogue, at the same force, of
`FriLdtExtractDeployed.friLdtExtractV3Faithful_iff_noOodShape`. -/
theorem decodedLdtLinkExtCons_iff_noOodShape
    (E : Type*) [Field E] [Algebra BabyBear E] [DecidableEq E] {numCols : ℕ}
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (d : EffectVmDescriptor2) :
    DecodedLdtLinkExtCons E sponge perm RATE toNat params vk core A initState logN view
        oracle pubA tfam d
      ↔ DecodedLdtLinkExtNoOodShape E sponge perm RATE toNat params vk core A initState logN view
        oracle pubA tfam d := by
  constructor
  · intro h pi π hacc hcols
    obtain ⟨ζ, Λ, qp, topen, _ood, vCommitted, root, _oodRest, idx, siblings,
      _hoodPt, hmem, hCommitted, hOpened, hnoOpen, hlayout, hLam, hnonexc, hPub⟩ :=
      h pi π hacc hcols
    exact ⟨ζ, Λ, qp, topen, vCommitted, root, idx, siblings,
      hmem, hCommitted, hOpened, hnoOpen, hlayout, hLam, hnonexc, hPub⟩
  · intro h pi π hacc hcols
    obtain ⟨ood, oodRest, hoodPt⟩ :=
      fullChecks_accept_gives_cons_oodPoint perm RATE toNat params vk core A initState logN
        (view pi π).1 (view pi π).2 hacc
    obtain ⟨ζ, Λ, qp, topen, vCommitted, root, idx, siblings,
      hmem, hCommitted, hOpened, hnoOpen, hlayout, hLam, hnonexc, hPub⟩ := h pi π hacc hcols
    exact ⟨ζ, Λ, qp, topen, ood, vCommitted, root, oodRest, idx, siblings,
      hoodPt, hmem, hCommitted, hOpened, hnoOpen, hlayout, hLam, hnonexc, hPub⟩

end Link

/-! ### The concrete accepting run: the repaired hypothesis is REALIZED where the defective one is
impossible.

`cfgPerm`/`cfgParams`/`cfgView`/… are `opaque`, so no accepting run at the DEPLOYED arguments can be
exhibited by anyone. The witness below is at concrete arguments and is transported from
`FriLdtExtractDeployed.corrected_ood_shape_inhabited`, whose acceptance is a `decide` on the complete
apex-facing predicate. What it shows is precisely what the repair needs: the tools' own acceptance
hypothesis (`verifyAlgo … (fullChecks …) = true`) is satisfiable, and on a run satisfying it the
corrected `ood :: oodRest` hypothesis HOLDS with `params.extDeg` lanes while the landed singleton
hypothesis is REFUTED. -/

/-- **⚑ THE INHABITABILITY WITNESS FOR THE REPAIRED HYPOTHESIS.** -/
theorem bare_accepting_run_with_corrected_ood_shape :
    ∃ (perm : List Nat → List Nat) (RATE : Nat) (toNat : Nat → Nat) (params : FriParams)
      (vk : RecursionVk Nat) (core : FriCore Nat) (A : FieldArith Nat)
      (initState : List Nat) (logN : Nat) (proof : BatchProofData Nat) (pub : WrapPublics Nat)
      (ood : Nat) (oodRest : List Nat),
      verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
          initState logN proof pub = true
        ∧ proof.oodPoint = ood :: oodRest
        ∧ (ood :: oodRest).length = params.extDeg
        ∧ (∀ o : Nat, proof.oodPoint ≠ [o]) := by
  obtain ⟨perm, RATE, toNat, params, vk, core, A, extCore, extA, Wres, initState, logN, proof, pub,
    view, ood, oodRest, hacc, hcons, _hzeta, hlen, hnsing⟩ := corrected_ood_shape_inhabited
  exact ⟨perm, RATE, toNat, params, vk, core, A, initState, logN, proof, pub, ood, oodRest,
    verifyAlgoUnified_imp_verifyAlgo perm RATE toNat params vk core A initState logN proof pub
      (verifyAlgoUnifiedFaithfulExt_imp_verifyAlgoUnified perm RATE toNat params vk core A
        extCore extA Wres initState logN proof pub view hacc),
    hcons, hlen, hnsing⟩

/-- The same run, put where it bites: the corrected §2/§3 tools' OOD hypothesis is DISCHARGEABLE on a
run their acceptance hypothesis accepts, and the landed tools' OOD hypothesis is NOT. -/
theorem corrected_hypothesis_dischargeable_landed_is_not :
    ∃ (perm : List Nat → List Nat) (RATE : Nat) (toNat : Nat → Nat) (params : FriParams)
      (vk : RecursionVk Nat) (core : FriCore Nat) (A : FieldArith Nat)
      (initState : List Nat) (logN : Nat) (proof : BatchProofData Nat) (pub : WrapPublics Nat),
      verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
          initState logN proof pub = true
        ∧ (∃ (ood : Nat) (oodRest : List Nat), proof.oodPoint = ood :: oodRest)
        ∧ ¬ (∃ o : Nat, proof.oodPoint = [o]) := by
  obtain ⟨perm, RATE, toNat, params, vk, core, A, initState, logN, proof, pub, ood, oodRest,
    hacc, hcons, _hlen, hnsing⟩ := bare_accepting_run_with_corrected_ood_shape
  exact ⟨perm, RATE, toNat, params, vk, core, A, initState, logN, proof, pub, hacc,
    ⟨ood, oodRest, hcons⟩, fun ⟨o, ho⟩ => hnsing o ho⟩

/-! ## §6 — Axiom hygiene. -/

#assert_all_clean [
  batchTablesCheck_nil,
  fullChecks_accept_forces_oodPoint_ne_nil,
  fullChecks_accept_gives_cons_oodPoint,
  hood_of_oodColumnLayout_unusable_at_deployed,
  deployed_oodPoint_length_four,
  hood_of_oodColumnLayoutCons,
  hood_of_oodColumnLayoutCons_subsumes_landed,
  hood_of_oodColumnLayout_noOod
]

#assert_all_clean [
  hood_of_oodColumnLayoutExtCons,
  hood_of_oodColumnLayoutExt_noOod,
  decodedLdtLinkExt_forces_deployed_reject,
  decodedLdtLinkExt_makes_verifyBatch_reject_everything,
  mainAirAcceptF_of_decodedLdtLinkExtCons
]

#assert_all_clean [
  decodedLdtLinkExtCons_iff_noOodShape,
  bare_accepting_run_with_corrected_ood_shape,
  corrected_hypothesis_dischargeable_landed_is_not
]

end Dregg2.Circuit.OodSingletonRepair
