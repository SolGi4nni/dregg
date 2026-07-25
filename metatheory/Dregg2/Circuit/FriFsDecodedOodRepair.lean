/-
# `Dregg2.Circuit.FriFsDecodedOodRepair` — the singleton-OOD wound at the FS bundle and at the
DECODED-TRACE residual: PROVED, REPAIRED, and the repair PROVED not to be a second vacuity.

## §A The two sites

Both sites conclude, on every accepting run, that the out-of-domain point is a ONE-element list of
base felts:

  * `FriVerifierFS.ExtractBundleSansFS` (`FriVerifierFS.lean:112`)
        `(view pi π).1.oodPoint = [ood]`     with `ood : ℤ`
  * `FriDecodedTraceWitness.DecodedLdtLink` (`FriDecodedTraceWitness.lean:464`)
        `(view pi π).1.oodPoint = [ood]`     with `ood : ℤ`

`DecodedLdtLink` is the DEEP-ALI residual the whole R4b decode assembly reduces to
(`FriDecodedTraceWitness.positiveRadiusTraceDecode_decoded` / `…_transferV3`), so a wound there is a
wound in the residual the FRI extractor ladder terminates at.

Both bundles are indexed by the BARE verifier (`AlgoStarkSoundGeneral.AcceptsFull`, i.e.
`verifyAlgo … (fullChecks core A toNat params.powBits) …`). §1 below is the honest first finding:
against the BARE verifier the singleton is NOT self-contradictory — bare acceptance forces only
`oodPoint ≠ []` (`FriVerifier.batchTablesCheck` has `| [] => false`), never a lane count. What the
bare verifier forces is proved here as `acceptsFull_forces_oodPoint_ne_nil`.

## §B The vacuity, PROVED — at the verifier the apex actually runs

`CircuitSoundness.verifyBatch` (`CircuitSoundness.lean:449-453`) evaluates
`ExtFieldChallenge.verifyAlgoUnifiedFaithfulExt`, which carries `decide (params.extDeg = 4)`
(`ExtFieldChallenge.lean:762`) and, through `unifiedTranscriptChecks`, the OOD binding
`decide (proof.oodPoint = d.ζ)` (`FriChallengerUnified.lean:122`) where `d.ζ` is a
`Challenger.sampleExt … params.extDeg` squeeze of exactly `params.extDeg` base lanes
(`FriVerifier.Challenger.sampleN_length`, `FriVerifier.lean:139-146`). So deployed acceptance forces
`oodPoint.length = 4` — `FriLdtExtractDeployed.faithfulExt_forces_oodPoint_length`.

Deployed acceptance IMPLIES bare acceptance
(`verifyAlgoUnifiedFaithfulExt_imp_verifyAlgoUnified` ∘ `verifyAlgoUnified_imp_verifyAlgo`).
Therefore each of the two landed bundles, assumed at the deployed configuration, makes the deployed
verifier reject:

  * `extractBundleSansFS_makes_verifyBatch_reject_everything` (§2) — `verifyBatch` returns
    `Verdict.reject` on EVERY key/PI/proof triple.
  * `decodedLdtLink_makes_verifyBatch_reject_every_close_run` (§5) — `verifyBatch` returns
    `Verdict.reject` on every run whose committed matrix is `ColsClose`-close. That is EXACTLY the
    set of runs `PositiveRadiusTraceDecode` quantifies over, so
    `positiveRadiusTraceDecode_decoded`'s `TraceWitnessed` conclusion is delivered only on runs the
    deployed verifier rejects. **The DEEP-ALI residual is rendered inert by its own OOD conjunct.**

Both landed shapes are RETAINED as the subjects of those theorems, exactly as
`FriLdtExtractDeployed.FriLdtExtractV3FaithfulSingleton` is, so the shape cannot be reintroduced
silently.

## §C The repair

`FriVerifier.batchTablesCheck` matches `| ood :: _` (`FriVerifier.lean:803-808`) and never wanted a
singleton. The corrected bundles are added ALONGSIDE the landed ones (which many modules consume and
which are NOT edited):

  * `ExtractBundleSansFSCons` (§3), with `oodPoint = ood :: oodRest`. Implied by the landed
    `ExtractBundleSansFS` (`extractBundleSansFS_imp_cons`) and discharged by the corrected upstream
    bundle `FriLdtExtractDeployed.FriLdtExtractV3Cons` (`friLdtExtractV3Cons_imp_sansFSCons` — the
    same ten-conjunct audit gate `friLdtExtractV3_imp_sansFS` was — ⚑ that landed gate is DELETED as
    of 2026-07-25, and `friLdtExtractV3Cons_imp_sansFSCons` below is its sole replacement).
  * `DecodedLdtLinkCons` (§6), with `oodPoint = ood :: oodRest`. Implied by the landed
    `DecodedLdtLink` (`decodedLdtLink_imp_cons`), and — the point of the exercise — the ENTIRE L5·R4b
    assembly is re-derived from it: `positiveRadiusTraceDecode_decoded_cons` /
    `positiveRadiusTraceDecode_transferV3_cons`, via the sibling lane's cons-shaped
    `ApexOodLaneRepair.hood_of_oodColumnLayout_cons`. Nothing downstream needed the singleton.

## §D Why the repair is not a second vacuity (§4, §7)

  * `ApexOodLaneRepair.acceptsFull_gives_cons_shape` — the corrected conjunct is SUPPLIED by acceptance: the bare
    verifier already rejects an empty OOD point, so `∃ ood oodRest, oodPoint = ood :: oodRest` holds
    on every accepting run.
  * `extractBundleSansFSCons_iff_noOodShape` / `decodedLdtLinkCons_iff_noOodShape` — each corrected
    bundle is EQUIVALENT to itself with the OOD conjunct DELETED (`ood` occurs nowhere else in either
    body). The repair therefore adds exactly zero strength and can never empty a premise.
  * `cons_ood_shape_inhabited_at_bare_verifier` — a CONCRETE run the bare verifier accepts
    (transported from `FriLdtExtractDeployed.deployed_accepting_pole_nonempty`, an accepting run of
    the complete apex-facing predicate) on which the corrected shape holds with four lanes and the
    singleton shape is refuted for every `o`.

What is NOT claimed: that either corrected bundle is satisfiable at the deployed `cfg*` arguments.
Those are `opaque`; their remaining conjuncts ARE the FRI-LDT / DEEP-ALI floor. The exact claim is
the same narrow one the worked example makes: the corrected OOD conjunct is implied by acceptance,
whereas the singleton one is contradicted by deployed acceptance.

## §E Overlap with concurrent lanes — declared, not hidden

Two files written concurrently in this session (NEITHER of them reachable from `Dregg2.lean` at the
time of writing, so they are not imported here) cover adjacent ground:

  * `PremiseInhabitability.lean` §E3/§E4 proves the SAME vacuity for the same two bundles, through a
    `YieldsShape`/`Empties` abstraction (`extractBundleSansFS_makes_verifyBatch_reject_everything`
    there is literally the statement of §2 here; `decodedLdtLink_forbids_close_on_accepting` is §5's
    contrapositive). §2/§5 below were proved independently and are stated directly against
    `verifyBatch`; an integrator should keep ONE of the two, not both.
  * `OodSingletonRepair.lean` repairs `OodExtChallengeLayout.DecodedLdtLinkExt` — the EXTENSION-typed
    retyping of `DecodedLdtLink`, a different object from the base-typed `DecodedLdtLink` repaired
    here — and re-derives only its AIR leg (`mainAirAcceptF_of_decodedLdtLinkExtCons`), not the
    `PositiveRadiusTraceDecode` assembly.

NOT covered by either, and the substance of this file: the entire SITE-1 repair
(`ExtractBundleSansFSCons` and its three relations — nobody repaired the FS bundle), the base-typed
`DecodedLdtLinkCons`, both non-vacuity equivalences, and — the downstream payoff — the FULL L5·R4b
assembly re-derived at the corrected shape (`positiveRadiusTraceDecode_decoded_cons` /
`positiveRadiusTraceDecode_transferV3_cons`).

Additive file. Edits no landed definition. No `sorry`, no new `axiom`, no `native_decide`.
-/
import Dregg2.Circuit.FriVerifierFS
import Dregg2.Circuit.FriDecodedTraceWitness
import Dregg2.Circuit.FriLdtExtractDeployed
import Dregg2.Circuit.ApexOodLaneRepair
import Dregg2.Circuit.OodSingletonRepair
import Dregg2.Circuit.ExtChallengeLogUpSite
import Dregg2.Tactics

namespace Dregg2.Circuit.FriFsDecodedOodRepair

open Polynomial
open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.FriVerifierBridge (ProofView)
open Dregg2.Circuit.FriVerifier
  (verifyAlgo BatchProofData WrapPublics FriParams RecursionVk FriChecks FriCore FieldArith
   TableOpening fullChecks)
open Dregg2.Circuit.CircuitSoundness
  (BatchPublicInputs BatchProof Registry Verdict VerifyKey verifyBatch tracePublishedCommit
   cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA cfgExtCore cfgExtA cfgExtW cfgInitState
   cfgLogN cfgView cfgExtView)
open Dregg2.Circuit.DescriptorIR2
  (VmTrace EffectVmDescriptor2 envAt VmConstraint2 Lookup TraceFamily)
open Dregg2.Circuit.AirChecksSatisfied (MainAirAcceptF isArith)
open Dregg2.Circuit.RotatedKernelRefinement (transferV3)
open Dregg2.Circuit.TraceColumnInterp (constraintPoly domainSize)
open Dregg2.Circuit.FieldIntegerLift (vanishingPoly ood_forces_mainAirAccept_field_of_residuals)
open Dregg2.Circuit.OodQuotientConsistency (exceptionalSet)
open Dregg2.Circuit.OodSoundnessGame (batchResidual)
open Dregg2.Circuit.OodCommitmentBinding (merkleRecomputeZ)
open Dregg2.Circuit.OodColumnLayout (oodBatchResidual)
open Dregg2.Circuit.LogUpColumnLayout (BusModelOk)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.FriBatchedOracle (MatrixOracle)
open Dregg2.Circuit.FriDeployedRateInstance (friSetupDeployed)
open Dregg2.Circuit.DeployedTraceExtract (PositiveRadiusTraceDecode)
open Dregg2.Circuit.AlgoStarkSoundGeneral
  (AcceptsFull MemMapFree memoryLegs_of_lookupShape nonArithArm_of_busModels)
open Dregg2.Circuit.AlgoStarkSoundTransferV3 (Rfam FriLdtExtractV3)
open Dregg2.Circuit.FriVerifierFS (ExtractBundleSansFS)
open Dregg2.Circuit.FriDecodedTraceWitness
  (DecodedLdtLink DecodedBusLink decodedTr decodedTr_rows_le decodedTr_memMapFree)
open Dregg2.Circuit.ExtFieldChallenge
  (ExtFriCore ExtFriArith ExtVerifierView verifyAlgoUnifiedFaithfulExt
   verifyAlgoUnifiedFaithfulExt_imp_verifyAlgoUnified)
open Dregg2.Circuit.FriChallengerUnified (verifyAlgoUnified_imp_verifyAlgo)
open Dregg2.Circuit.FriLdtExtractDeployed
  (ExtProofView FriLdtExtractV3Cons faithfulExt_accept_gives_cons_shape
   faithfulExt_forces_oodPoint_ne_singleton deployed_accepting_pole_nonempty)
open Dregg2.Circuit.ApexOodLaneRepair
  (acceptsFull_forces_oodPoint_ne_nil acceptsFull_gives_cons_shape hood_of_oodColumnLayout_cons)
open Dregg2.Circuit.OodInterpFieldExt
  (BB4 liftPoly liftPoly_sub liftPoly_mul liftPoly_eval_base notMem_exceptionalSet_lift
   exists_nonbase_bb4 ood_forces_mainAirAccept_field_of_residuals_ext)
open Dregg2.Circuit.OodExtChallengeLayout
  (oodBatchResidualExt oodBatchResidualExt_lift oodBatchResidualExt_eval_lift
   notMem_exceptionalSet_constraint_lift)
open Dregg2.Circuit.OodSingletonRepair
  (DecodedLdtLinkExtCons hood_of_oodColumnLayoutExtCons)
open Dregg2.Circuit.ExtChallengeLogUpSite
  (BusModelOkAt logupChallengeExt logupChallengeExt_lift powerLanes embedVal
   busModelAt_forces_lookup_holds fire_busModelExt_nonbase)

set_option autoImplicit false

/-! ## §1 — what the BARE verifier actually forces about `oodPoint` (the honest scope of the wound).

`AcceptsFull` is `verifyAlgo … (fullChecks core A toNat params.powBits) …`. Its `batchTables` field
is `FriVerifier.batchTablesCheck`, which rejects an EMPTY out-of-domain point (`| [] => false`,
`FriVerifier.lean:807`) and otherwise consumes the HEAD lane. So the bare verifier forces
NON-EMPTINESS and nothing more — in particular it does NOT contradict a singleton. The singleton
bundles are not self-contradictory at their own antecedent; §2/§5 show they are fatal at the
verifier `verifyBatch` runs.

Those two facts are `ApexOodLaneRepair.acceptsFull_forces_oodPoint_ne_nil` and
`ApexOodLaneRepair.acceptsFull_gives_cons_shape`, proved by the sibling lane that repaired
`AlgoStarkSoundGeneral.lean:147`; they are REUSED here rather than re-proved, and so is that lane's
cons-shaped OOD reduction `ApexOodLaneRepair.hood_of_oodColumnLayout_cons` (§6). -/

/-! ## §2 — SITE 1 (`FriVerifierFS.lean:112`): THE VACUITY, PROVED. -/

/-- **THE VACUITY AT SITE 1.** Assuming the landed `ExtractBundleSansFS`, the DEPLOYED verifier —
`ExtFieldChallenge.verifyAlgoUnifiedFaithfulExt`, the predicate `CircuitSoundness.verifyBatch`
evaluates — accepts NOTHING. Deployed acceptance implies bare acceptance, which the bundle answers
with a one-lane OOD point, on a run whose acceptance forces four lanes. -/
theorem sansFS_makes_deployed_verifier_accept_nothing
    (sponge hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (extCore : ExtFriCore ℤ) (extA : ExtFriArith ℤ) (W : ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) (extView : ExtProofView)
    (h : ExtractBundleSansFS sponge hash perm RATE toNat params vk core A initState logN view)
    (pi : BatchPublicInputs) (π : BatchProof) :
    verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core A extCore extA W
      initState logN (view pi π).1 (view pi π).2 (extView pi π) = false := by
  rcases Bool.eq_false_or_eq_true
      (verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core A extCore extA W
        initState logN (view pi π).1 (view pi π).2 (extView pi π)) with hb | hb
  · have hbare : verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
        initState logN (view pi π).1 (view pi π).2 = true :=
      verifyAlgoUnified_imp_verifyAlgo perm RATE toNat params vk core A initState logN
        (view pi π).1 (view pi π).2
        (verifyAlgoUnifiedFaithfulExt_imp_verifyAlgoUnified perm RATE toNat params vk core A
          extCore extA W initState logN (view pi π).1 (view pi π).2 (extView pi π) hb)
    obtain ⟨_, _, _, _, _, ood, _, _, _, _, _, hoodPt, _⟩ := h pi π hbare
    exact absurd hoodPt
      (faithfulExt_forces_oodPoint_ne_singleton perm RATE toNat params vk core A extCore extA W
        initState logN (view pi π).1 (view pi π).2 (extView pi π) hb ood)
  · exact hb

/-- **The apex consequence at SITE 1.** Under the landed `ExtractBundleSansFS` at the deployed
`cfg*` arguments, `CircuitSoundness.verifyBatch` returns `Verdict.reject` on EVERY key / public-input
/ proof triple. Any conclusion conditioned on that bundle at the deployed config quantifies over an
empty set of accepting batches. -/
theorem extractBundleSansFS_makes_verifyBatch_reject_everything
    (sponge hash : List ℤ → ℤ)
    (h : ExtractBundleSansFS sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
      cfgInitState cfgLogN cfgView)
    (vkey : VerifyKey) (pi : BatchPublicInputs) (π : BatchProof) :
    verifyBatch vkey pi π = Verdict.reject := by
  have hrej := sansFS_makes_deployed_verifier_accept_nothing sponge hash cfgPerm cfgRATE cfgToNat
    cfgParams cfgVk cfgCore cfgA cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN cfgView cfgExtView
    h pi π
  simp [verifyBatch, hrej]

/-! ## §3 — SITE 1, the CORRECTED bundle. -/

/-- **`ExtractBundleSansFSCons`** — `FriVerifierFS.ExtractBundleSansFS` with the OOD conjunct at the
shape `FriVerifier.batchTablesCheck` actually matches (`| ood :: _`). The other nine conjuncts are
copied token-for-token; the landed definition is untouched. -/
def ExtractBundleSansFSCons
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
      (batchResidual (Rfam transferV3 t ζ qp)).eval Λ
        = ((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear) ∧
      (∀ i < t.rows.length, ∀ c ∈ transferV3.constraints, ¬ isArith c →
          c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)) ∧
      t.tf .memory = [] ∧ t.tf .mapOps = [] ∧
      tracePublishedCommit t = pi.toPublished

/-- The landed bundle implies the corrected one, by `[ood] = ood :: []`. A real implication: no
contradiction is used, and it holds at every instantiation, including ones where both sides are
inhabited. -/
theorem extractBundleSansFS_imp_cons
    (sponge hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (h : ExtractBundleSansFS sponge hash perm RATE toNat params vk core A initState logN view) :
    ExtractBundleSansFSCons sponge hash perm RATE toNat params vk core A initState logN view := by
  intro pi π hacc
  obtain ⟨t, ζ, Λ, qp, topen, ood, vCommitted, root, idx, siblings,
    hcap, hoodPt, hmem, hCommitted, hOpened, hlayout, hbus, hMem, hMap, hPub⟩ := h pi π hacc
  exact ⟨t, ζ, Λ, qp, topen, ood, vCommitted, root, [], idx, siblings,
    hcap, hoodPt, hmem, hCommitted, hOpened, hlayout, hbus, hMem, hMap, hPub⟩

/-- **The corrected ADVERSARIAL-AUDIT GATE** — ⚑ as of 2026-07-25 the SOLE audit gate: the landed
`FriVerifierFS.friLdtExtractV3_imp_sansFS` (empty premise ⟹ empty conclusion) is DELETED and this is
its replacement. The corrected upstream extraction bundle
`FriLdtExtractDeployed.FriLdtExtractV3Cons` discharges `ExtractBundleSansFSCons` purely by
destructuring its twelve conjuncts and reassembling ten of them, dropping exactly the two
Fiat–Shamir non-exceptionality conjuncts (`hLam`, `hnonexc`). This typechecks ONLY if the ten kept
conjuncts match token-for-token — the same mechanical check the landed gate performs, now at the
corrected OOD shape. -/
theorem friLdtExtractV3Cons_imp_sansFSCons
    (sponge hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (h : FriLdtExtractV3Cons sponge hash perm RATE toNat params vk core A initState logN view) :
    ExtractBundleSansFSCons sponge hash perm RATE toNat params vk core A initState logN view := by
  intro pi π hacc
  obtain ⟨t, ζ, Λ, qp, topen, ood, vCommitted, root, oodRest, idx, siblings,
    hcap, hoodPt, hmem, hCommitted, hOpened, hlayout, _hLam, _hnonexc,
    hbus, hMem, hMap, hPub⟩ := h pi π hacc
  exact ⟨t, ζ, Λ, qp, topen, ood, vCommitted, root, oodRest, idx, siblings,
    hcap, hoodPt, hmem, hCommitted, hOpened, hlayout, hbus, hMem, hMap, hPub⟩

/-! ## §4 — SITE 1: the repair is NOT a second vacuity. -/

/-- `ExtractBundleSansFSCons` with the OOD conjunct DELETED (`ood`/`oodRest` occur nowhere else in
the body). Used only to state the equivalence below. -/
def ExtractBundleSansFSNoOodShape
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
      (∀ i < t.rows.length, ∀ c ∈ transferV3.constraints, ¬ isArith c →
          c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)) ∧
      t.tf .memory = [] ∧ t.tf .mapOps = [] ∧
      tracePublishedCommit t = pi.toPublished

/-- **THE NON-VACUITY OF THE SITE-1 REPAIR.** `ExtractBundleSansFSCons` is EQUIVALENT to itself with
the OOD conjunct deleted: the conjunct is supplied by acceptance (`acceptsFull_gives_cons_shape`), so
it cannot shrink — let alone empty — the set of accepting runs the premise must cover. Contrast §2:
the singleton conjunct is CONTRADICTED by deployed acceptance and empties it completely. -/
theorem extractBundleSansFSCons_iff_noOodShape
    (sponge hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) :
    ExtractBundleSansFSCons sponge hash perm RATE toNat params vk core A initState logN view
      ↔ ExtractBundleSansFSNoOodShape sponge hash perm RATE toNat params vk core A initState logN
        view := by
  constructor
  · intro h pi π hacc
    obtain ⟨t, ζ, Λ, qp, topen, _ood, vCommitted, root, _oodRest, idx, siblings,
      hcap, _hoodPt, hmem, hCommitted, hOpened, hlayout, hbus, hMem, hMap, hPub⟩ := h pi π hacc
    exact ⟨t, ζ, Λ, qp, topen, vCommitted, root, idx, siblings,
      hcap, hmem, hCommitted, hOpened, hlayout, hbus, hMem, hMap, hPub⟩
  · intro h pi π hacc
    obtain ⟨ood, oodRest, hcons⟩ :=
      acceptsFull_gives_cons_shape perm RATE toNat params vk core A initState logN
        (view pi π).1 (view pi π).2 hacc
    obtain ⟨t, ζ, Λ, qp, topen, vCommitted, root, idx, siblings,
      hcap, hmem, hCommitted, hOpened, hlayout, hbus, hMem, hMap, hPub⟩ := h pi π hacc
    exact ⟨t, ζ, Λ, qp, topen, ood, vCommitted, root, oodRest, idx, siblings,
      hcap, hcons, hmem, hCommitted, hOpened, hlayout, hbus, hMem, hMap, hPub⟩

/-- **THE INHABITABILITY WITNESS (shared by both sites).** A CONCRETE run the bare verifier
`verifyAlgo … (fullChecks …)` accepts — transported from
`FriLdtExtractDeployed.deployed_accepting_pole_nonempty`, an accepting run of the complete
apex-facing predicate — on which the CORRECTED OOD shape holds with `params.extDeg` lanes, and the
SINGLETON shape is refuted for every `o`. Both corrected bundles' OOD conjunct is realized exactly
where the landed one is impossible.

Strengthens `ApexOodLaneRepair.acceptsFull_cons_shape_inhabited` with the LANE COUNT: the witnessed
run's OOD point does not merely decompose as `ood :: oodRest`, it has exactly `params.extDeg`
lanes — the deployed quartic width. -/
theorem cons_ood_shape_inhabited_at_bare_verifier :
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
    view, hacc⟩ := deployed_accepting_pole_nonempty
  have hbare : verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
      initState logN proof pub = true :=
    verifyAlgoUnified_imp_verifyAlgo perm RATE toNat params vk core A initState logN proof pub
      (verifyAlgoUnifiedFaithfulExt_imp_verifyAlgoUnified perm RATE toNat params vk core A
        extCore extA Wres initState logN proof pub view hacc)
  obtain ⟨ood, oodRest, hcons, _hzeta, hlen⟩ :=
    faithfulExt_accept_gives_cons_shape perm RATE toNat params vk core A extCore extA Wres
      initState logN proof pub view hacc
  exact ⟨perm, RATE, toNat, params, vk, core, A, initState, logN, proof, pub, ood, oodRest,
    hbare, hcons, hlen,
    fun o => faithfulExt_forces_oodPoint_ne_singleton perm RATE toNat params vk core A extCore
      extA Wres initState logN proof pub view hacc o⟩

/-! ## §5 — SITE 2 (`FriDecodedTraceWitness.lean:464`): THE VACUITY AT THE DEEP-ALI RESIDUAL. -/

/-- **THE VACUITY AT SITE 2.** Assuming the landed `DecodedLdtLink`, the DEPLOYED verifier rejects
every run whose committed matrix is `ColsClose`-close: the bundle answers such a run with a one-lane
OOD point, on a run whose deployed acceptance forces four. -/
theorem decodedLdtLink_makes_deployed_verifier_reject_close_runs {numCols : ℕ}
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (extCore : ExtFriCore ℤ) (extA : ExtFriArith ℤ) (W : ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) (extView : ExtProofView)
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (d : EffectVmDescriptor2)
    (h : DecodedLdtLink sponge perm RATE toNat params vk core A initState logN view
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

/-- **The apex consequence at SITE 2 — the DEEP-ALI residual is INERT as landed.** Under the landed
`DecodedLdtLink` at the deployed `cfg*` arguments, `CircuitSoundness.verifyBatch` returns
`Verdict.reject` on every `ColsClose`-close run. Those runs are EXACTLY the ones
`DeployedTraceExtract.PositiveRadiusTraceDecode` quantifies over, so the `TraceWitnessed` conclusion
of `FriDecodedTraceWitness.positiveRadiusTraceDecode_decoded` /
`…positiveRadiusTraceDecode_transferV3` is delivered only on runs the deployed verifier rejects: the
L5·R4b assembly's guarantee, at the deployed config, covers no accepted batch. -/
theorem decodedLdtLink_makes_verifyBatch_reject_every_close_run {numCols : ℕ}
    (sponge : List ℤ → ℤ)
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (d : EffectVmDescriptor2)
    (h : DecodedLdtLink sponge cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA cfgInitState
      cfgLogN cfgView oracle pubA tfam d)
    (vkey : VerifyKey) (pi : BatchPublicInputs) (π : BatchProof)
    (hcols : MatrixOracle.ColsClose friSetupDeployed.C 7340032 (oracle pi π)) :
    verifyBatch vkey pi π = Verdict.reject := by
  have hrej := decodedLdtLink_makes_deployed_verifier_reject_close_runs sponge cfgPerm cfgRATE
    cfgToNat cfgParams cfgVk cfgCore cfgA cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN cfgView
    cfgExtView oracle pubA tfam d h pi π hcols
  simp [verifyBatch, hrej]

/-! ## §6 — SITE 2, the CORRECTED residual, and the L5·R4b assembly RE-DERIVED from it. -/

/-- **`DecodedLdtLinkCons`** — `FriDecodedTraceWitness.DecodedLdtLink` with the OOD conjunct at the
shape `FriVerifier.batchTablesCheck` actually matches. The other seven conjuncts are copied
token-for-token; the landed definition is untouched. -/
def DecodedLdtLinkCons {numCols : ℕ}
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
    ∃ (ζ Λ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)
      (topen : TableOpening ℤ) (ood vCommitted root : ℤ) (oodRest : List ℤ)
      (idx : Nat) (siblings : List ℤ),
      (view pi π).1.oodPoint = ood :: oodRest ∧
      topen ∈ (view pi π).1.tableOpenings ∧
      merkleRecomputeZ sponge idx vCommitted siblings = root ∧
      merkleRecomputeZ sponge idx topen.constraintEval siblings = root ∧
      (oodBatchResidual d (decodedTr oracle pubA tfam pi π) ζ qp).eval Λ
        = ((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear) ∧
      Λ ∉ exceptionalSet (oodBatchResidual d (decodedTr oracle pubA tfam pi π) ζ qp) ∧
      (∀ c ∈ d.constraints, isArith c →
          ζ ∉ exceptionalSet (constraintPoly d (decodedTr oracle pubA tfam pi π) c
                - vanishingPoly (decodedTr oracle pubA tfam pi π) * qp c)) ∧
      tracePublishedCommit (decodedTr oracle pubA tfam pi π) = pi.toPublished

/-- The landed residual implies the corrected one, by `[ood] = ood :: []`. -/
theorem decodedLdtLink_imp_cons {numCols : ℕ}
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (d : EffectVmDescriptor2)
    (h : DecodedLdtLink sponge perm RATE toNat params vk core A initState logN view
      oracle pubA tfam d) :
    DecodedLdtLinkCons sponge perm RATE toNat params vk core A initState logN view
      oracle pubA tfam d := by
  intro pi π hacc hcols
  obtain ⟨ζ, Λ, qp, topen, ood, vCommitted, root, idx, siblings,
    hoodPt, hmem, hCommitted, hOpened, hlayout, hLam, hnonexc, hPub⟩ := h pi π hacc hcols
  exact ⟨ζ, Λ, qp, topen, ood, vCommitted, root, [], idx, siblings,
    hoodPt, hmem, hCommitted, hOpened, hlayout, hLam, hnonexc, hPub⟩

/-- **⚑ THE CONS-SHAPED ENTRY into `DecodedLdtLinkCons`** — the replacement for the DELETED
`FriDecodedTraceWitness.decodedLdtLink_of_friLdtExtract`, which routed the only supply of the
DEEP-ALI residual through `AlgoStarkSoundGeneral.FriLdtExtract`, the bundle PROVED to force
`CircuitSoundness.verifyBatch` to reject every input at the deployed `cfg*` args
(`ApexOodLaneRepair.friLdtExtract_makes_verifyBatch_reject_everything`). Composing
`decodedLdtLink_imp_cons` after the landed adapter would NOT have repaired anything: the entry
would still have been an empty hypothesis, so `DecodedLdtLinkCons` would have been reachable only
from a premise nothing satisfies.

Same content as the landed adapter otherwise: the `hcap` conjunct is dropped (`DecodedLdtLink`
discharges it) and the `ColsClose` antecedent is weakened away, so this is a REAL implication —
no contradiction is used and it holds at every instantiation, including inhabited ones. -/
theorem decodedLdtLinkCons_of_friLdtExtractCons {numCols : ℕ}
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (d : EffectVmDescriptor2)
    (hfri : Dregg2.Circuit.ApexOodLaneRepair.FriLdtExtractCons sponge perm RATE toNat params vk
      core A initState logN view (decodedTr oracle pubA tfam) d) :
    DecodedLdtLinkCons sponge perm RATE toNat params vk core A initState logN view
      oracle pubA tfam d := by
  intro pi π hacc _
  obtain ⟨ζ, Λ, qp, topen, ood, vCommitted, root, oodRest, idx, siblings,
    -, hoodPt, hmem, hCommitted, hOpened, hlayout, hLam, hnonexc, hPub⟩ := hfri pi π hacc
  exact ⟨ζ, Λ, qp, topen, ood, vCommitted, root, oodRest, idx, siblings,
    hoodPt, hmem, hCommitted, hOpened, hlayout, hLam, hnonexc, hPub⟩

/-! ## §6.5 — ⚑ THE CHALLENGE-TYPING CUTOVER: the L5·R4b assembly ON THE EXTENSION-TYPED LINK.

§6 repaired the LANE COUNT of the OOD conjunct. This section repairs the FIELD the challenges live
in, which is the deeper of the two wounds: the deployed `ζ`/`Λ` are QUARTIC-EXTENSION elements
(`ExtFieldChallenge.lean:8-15`), and a base-typed layout equation is not a restriction of the
deployed one but a DIFFERENT equation over a strictly smaller value space —
`OodExtChallengeLayout.extLayout_value_beyond_base` exhibits a deployed-shape layout value outside
`Set.range (algebraMap BabyBear BB4)` while `base_layout_value_mem_range` confines every base-typed
one to it, both fired at the real deployed descriptor `transferV3`
(`fire_extLayout_value_beyond_base`, `fire_extLayout_separation`); and the lane-0 rescue is refuted
for EVERY basis and EVERY lane (`coordFunctional_not_multiplicative`, fired at the deployed quartic
basis by `bb4_lane_not_multiplicative`).

So the assembly is re-derived from `OodSingletonRepair.DecodedLdtLinkExtCons` — the same conclusion,
at the same deployed instance, from a hypothesis the deployed verifier can actually supply — and the
base-typed `_cons` assembly is then routed THROUGH it (`decodedLdtLinkExtCons_of_decodedLdtLinkCons`)
so there is ONE chain and no silent twin. -/

/-- **The cons-shaped link LIFTS into the extension typing.** Every base-typed `DecodedLdtLinkCons`
witness embeds along `algebraMap BabyBear BB4`: the layout equation by `oodBatchResidualExt_eval_lift`,
the RLC non-exceptionality of `Λ` by `notMem_exceptionalSet_lift` after `oodBatchResidualExt_lift`,
and the per-constraint non-exceptionality of `ζ` by `notMem_exceptionalSet_constraint_lift`. So the
extension-typed link is a strictly WEAKER demand — nothing the base link supplied is lost. -/
theorem decodedLdtLinkExtCons_of_decodedLdtLinkCons {numCols : ℕ}
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (d : EffectVmDescriptor2)
    (h : DecodedLdtLinkCons sponge perm RATE toNat params vk core A initState logN view
      oracle pubA tfam d) :
    DecodedLdtLinkExtCons BB4 sponge perm RATE toNat params vk core A initState logN view
      oracle pubA tfam d := by
  intro pi π hacc hcols
  obtain ⟨ζ, Λ, qp, topen, ood, vCommitted, root, oodRest, idx, siblings,
    hoodPt, hmem, hCommitted, hOpened, hlayout, hLam, hnonexc, hPub⟩ := h pi π hacc hcols
  refine ⟨algebraMap BabyBear BB4 ζ, algebraMap BabyBear BB4 Λ,
    fun c => liftPoly BB4 (qp c), topen, ood, vCommitted, root, oodRest, idx, siblings,
    hoodPt, hmem, hCommitted, hOpened, ?_, ?_, ?_, hPub⟩
  · rw [oodBatchResidualExt_eval_lift, hlayout]
  · rw [oodBatchResidualExt_lift]
    exact notMem_exceptionalSet_lift hLam
  · intro c hc ha
    exact notMem_exceptionalSet_constraint_lift d _ ζ qp c (hnonexc c hc ha)

/-- **⚑ L5·R4b AT THE DEPLOYED CHALLENGE TYPING.** `positiveRadiusTraceDecode_decoded` with the
DEEP-ALI residual replaced by `DecodedLdtLinkExtCons BB4` — the OOD point, the RLC challenge and the
quotient family all drawn from the deployed quartic extension, the lane count corrected. The
conclusion is the IDENTICAL base-field `PositiveRadiusTraceDecode` at the identical deployed instance
(`friSetupDeployed`, UD radius `7340032`) from the identical three residuals: the ζ-Schwartz–Zippel
step now runs over `BB4` and lands the base-field per-row AIR acceptance through
`OodInterpFieldExt.ood_forces_mainAirAccept_field_of_residuals_ext`. Weaker hypothesis, same
conclusion. -/
theorem positiveRadiusTraceDecode_decoded_extCons {F : Type*} [Field F] [DecidableEq F]
    (d : EffectVmDescriptor2)
    (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (hash : List ℤ → ℤ) (fp : List ℤ → F) (embed : ℤ → F)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) {numCols : ℕ}
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (htfMem : ∀ pi π, tfam pi π .memory = []) (htfMap : ∀ pi π, tfam pi π .mapOps = [])
    (hshape : ∀ c ∈ d.constraints, ¬ isArith c → ∃ l : Lookup, c = VmConstraint2.lookup l)
    (hsites : d.hashSites = []) (hranges : d.ranges = [])
    (hlink : DecodedLdtLinkExtCons BB4 sponge perm RATE toNat params vk core A initState logN view
      oracle pubA tfam d)
    (hbusF : DecodedBusLink fp embed perm RATE toNat params vk core A initState logN view
      oracle pubA tfam d) :
    PositiveRadiusTraceDecode hash (fun _ => d) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view
      friSetupDeployed oracle 7340032 := by
  intro pi π hacc hcols
  obtain ⟨ζ, Λ, qp, topen, ood, vCommitted, root, oodRest, idx, siblings,
    hoodPt, hmem, hCommitted, hOpened, hlayout, hLam, hnonexc, hPub⟩ := hlink pi π hacc hcols
  have hAir : MainAirAcceptF d (decodedTr oracle pubA tfam pi π) :=
    ood_forces_mainAirAccept_field_of_residuals_ext BB4 d (decodedTr oracle pubA tfam pi π)
      (decodedTr_rows_le oracle pubA tfam pi π) ζ qp
      (hood_of_oodColumnLayoutExtCons BB4 d sponge hCR perm RATE toNat params vk core A initState
        logN (view pi π).1 (view pi π).2 hacc (decodedTr oracle pubA tfam pi π) ζ Λ qp topen
        ood vCommitted root oodRest idx siblings hoodPt hmem hCommitted hOpened hlayout hLam)
      hnonexc
  obtain ⟨minit, mfin, maddrs, hrest, hNodup, hClosed, hDisc, hBal, hMemTF, hMapTF⟩ :=
    memoryLegs_of_lookupShape hash perm RATE toNat params vk core A initState logN view
      (decodedTr oracle pubA tfam) d hshape
      (decodedTr_memMapFree oracle pubA tfam htfMem htfMap perm RATE toNat params vk core A
        initState logN view)
      pi π hacc
  have harm : ∀ i < (decodedTr oracle pubA tfam pi π).rows.length, ∀ c ∈ d.constraints,
      ¬ isArith c → c.holdsAt hash (decodedTr oracle pubA tfam pi π).tf
        (envAt (decodedTr oracle pubA tfam pi π) i) (i == 0)
        (i + 1 == (decodedTr oracle pubA tfam pi π).rows.length) :=
    nonArithArm_of_busModels hash fp embed d (decodedTr oracle pubA tfam pi π)
      (hbusF pi π hacc hcols) hrest
  refine ⟨minit, mfin, maddrs, decodedTr oracle pubA tfam pi π, hAir, harm, ?_, ?_,
    hNodup, hClosed, hDisc, hBal, hMemTF, hMapTF, hPub⟩
  · intro i _
    rw [hsites]
    trivial
  · intro i _ r hr
    rw [hranges] at hr
    simp at hr

/-- The deployed `transferV3` slice at the deployed challenge typing. Residual =
{`Poseidon2SpongeCR`, `DecodedLdtLinkExtCons BB4 @ transferV3`, `DecodedBusLink @ transferV3`}. -/
theorem positiveRadiusTraceDecode_transferV3_extCons {F : Type*} [Field F] [DecidableEq F]
    (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (hash : List ℤ → ℤ) (fp : List ℤ → F) (embed : ℤ → F)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) {numCols : ℕ}
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (htfMem : ∀ pi π, tfam pi π .memory = []) (htfMap : ∀ pi π, tfam pi π .mapOps = [])
    (hlink : DecodedLdtLinkExtCons BB4 sponge perm RATE toNat params vk core A initState logN view
      oracle pubA tfam transferV3)
    (hbusF : DecodedBusLink fp embed perm RATE toNat params vk core A initState logN view
      oracle pubA tfam transferV3) :
    PositiveRadiusTraceDecode hash (fun _ => transferV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view
      friSetupDeployed oracle 7340032 :=
  positiveRadiusTraceDecode_decoded_extCons transferV3 sponge hCR hash fp embed perm RATE toNat
    params vk core A initState logN view oracle pubA tfam htfMem htfMap
    Dregg2.Circuit.AirLegsDischarged.hbus_is_lookup
    Dregg2.Circuit.AirLegsDischarged.transferV3_hashSites
    Dregg2.Circuit.AirLegsDischarged.transferV3_ranges
    hlink hbusF

#assert_axioms decodedLdtLinkExtCons_of_decodedLdtLinkCons
#assert_axioms positiveRadiusTraceDecode_decoded_extCons
#assert_axioms positiveRadiusTraceDecode_transferV3_extCons

/-! ### §6.6 — ⚑ THE SECOND CHALLENGE FAMILY: the LogUp BUS challenge, at the deployed typing.

`DecodedBusLink` computes its bus challenge as `LogUpColumnLayout.logupChallenge embed d t`, which is
`embed (t.pub (challengeCol d))` — ONE public-column slot.  The deployed LogUp challenge is a
`Challenge`: four ordered `Val` lanes.  `BusModelOk.nonexceptional` is a Fiat–Shamir Schwartz–Zippel
event ABOUT that value, so this is load-bearing, not decorative.

⚑ Say the relation precisely, because it is NOT the same as the OOD one.  The OOD retyping was a
strict WEAKENING (base witnesses lift unconditionally).  Here the two are different READS of the same
public block: `ExtChallengeLogUpSite.logupChallengeExt_lift` shows the single-slot read is exactly the
four-lane read at `lanes 0 = 1` WITH THE THREE HIGHER SLOTS ZERO — so a base-typed bus witness lifts
only under that public-column condition, which is stated as a hypothesis and not smuggled.  What is
unconditional is the SEPARATION: `logupChallenge_deployed_mem_range` confines every single-slot read
to `Set.range (algebraMap BabyBear BB4)` while `logupChallengeExt_beyond_base` reaches outside it, and
`atMostOne_basis_mem_range` / `bb4Basis_lane_beyond_base` prove at most one of the four deployed lanes
can be a base value for ANY basis.  So a single-slot read cannot express the deployed challenge. -/

/-- **`DecodedBusLink` AT THE DEPLOYED FOUR-LANE BUS CHALLENGE.** Identical to `DecodedBusLink` except
that the bus challenge is the deployed four-lane read `logupChallengeExt BB4 lanes d t` rather than a
single public-column slot, carried as a `BusModelOkAt` (the challenge as a parameter, which is
`BusModelOk` at the constant embedding — every field says exactly what it said before). -/
def DecodedBusLinkExt {numCols : ℕ}
    (fp : List ℤ → BB4) (lanes : Fin 4 → BB4)
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
    ∀ l : Lookup, VmConstraint2.lookup l ∈ d.constraints →
      ∃ mult : List ℕ,
        BusModelOkAt fp (logupChallengeExt BB4 lanes d (decodedTr oracle pubA tfam pi π))
          d (decodedTr oracle pubA tfam pi π) l.table mult

/-- **⚑ L5·R4b WITH BOTH CHALLENGE FAMILIES AT THE DEPLOYED TYPING.** The OOD point, the
constraint-RLC challenge and the quotient family are drawn from `BB4` (via `DecodedLdtLinkExtCons`),
AND the LogUp bus challenge is the deployed four-lane read (via `DecodedBusLinkExt`). The conclusion
is the IDENTICAL base-field `PositiveRadiusTraceDecode` at the identical deployed instance — no field
element survives into it at all: `TraceWitnessed`'s legs are statements about ℤ tuples, the committed
trace and the memory log. This is the L5 assembly with NO base-typed challenge object left in its
hypotheses. -/
theorem positiveRadiusTraceDecode_decoded_extChallenges
    (d : EffectVmDescriptor2)
    (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (hash : List ℤ → ℤ) (fp : List ℤ → BB4) (lanes : Fin 4 → BB4)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) {numCols : ℕ}
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (htfMem : ∀ pi π, tfam pi π .memory = []) (htfMap : ∀ pi π, tfam pi π .mapOps = [])
    (hshape : ∀ c ∈ d.constraints, ¬ isArith c → ∃ l : Lookup, c = VmConstraint2.lookup l)
    (hsites : d.hashSites = []) (hranges : d.ranges = [])
    (hlink : DecodedLdtLinkExtCons BB4 sponge perm RATE toNat params vk core A initState logN view
      oracle pubA tfam d)
    (hbusExt : DecodedBusLinkExt fp lanes perm RATE toNat params vk core A initState logN view
      oracle pubA tfam d) :
    PositiveRadiusTraceDecode hash (fun _ => d) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view
      friSetupDeployed oracle 7340032 := by
  intro pi π hacc hcols
  obtain ⟨ζ, Λ, qp, topen, ood, vCommitted, root, oodRest, idx, siblings,
    hoodPt, hmem, hCommitted, hOpened, hlayout, hLam, hnonexc, hPub⟩ := hlink pi π hacc hcols
  have hAir : MainAirAcceptF d (decodedTr oracle pubA tfam pi π) :=
    ood_forces_mainAirAccept_field_of_residuals_ext BB4 d (decodedTr oracle pubA tfam pi π)
      (decodedTr_rows_le oracle pubA tfam pi π) ζ qp
      (hood_of_oodColumnLayoutExtCons BB4 d sponge hCR perm RATE toNat params vk core A initState
        logN (view pi π).1 (view pi π).2 hacc (decodedTr oracle pubA tfam pi π) ζ Λ qp topen
        ood vCommitted root oodRest idx siblings hoodPt hmem hCommitted hOpened hlayout hLam)
      hnonexc
  obtain ⟨minit, mfin, maddrs, hrest, hNodup, hClosed, hDisc, hBal, hMemTF, hMapTF⟩ :=
    memoryLegs_of_lookupShape hash perm RATE toNat params vk core A initState logN view
      (decodedTr oracle pubA tfam) d hshape
      (decodedTr_memMapFree oracle pubA tfam htfMem htfMap perm RATE toNat params vk core A
        initState logN view)
      pi π hacc
  have harm : ∀ i < (decodedTr oracle pubA tfam pi π).rows.length, ∀ c ∈ d.constraints,
      ¬ isArith c → c.holdsAt hash (decodedTr oracle pubA tfam pi π).tf
        (envAt (decodedTr oracle pubA tfam pi π) i) (i == 0)
        (i + 1 == (decodedTr oracle pubA tfam pi π).rows.length) :=
    nonArithArm_of_busModels hash fp
      (fun _ => logupChallengeExt BB4 lanes d (decodedTr oracle pubA tfam pi π)) d
      (decodedTr oracle pubA tfam pi π) (hbusExt pi π hacc hcols) hrest
  refine ⟨minit, mfin, maddrs, decodedTr oracle pubA tfam pi π, hAir, harm, ?_, ?_,
    hNodup, hClosed, hDisc, hBal, hMemTF, hMapTF, hPub⟩
  · intro i _
    rw [hsites]
    trivial
  · intro i _ r hr
    rw [hranges] at hr
    simp at hr

/-- **The deployed `transferV3` slice with BOTH challenge families at the deployed typing.** -/
theorem positiveRadiusTraceDecode_transferV3_extChallenges
    (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (hash : List ℤ → ℤ) (fp : List ℤ → BB4) (lanes : Fin 4 → BB4)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) {numCols : ℕ}
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (htfMem : ∀ pi π, tfam pi π .memory = []) (htfMap : ∀ pi π, tfam pi π .mapOps = [])
    (hlink : DecodedLdtLinkExtCons BB4 sponge perm RATE toNat params vk core A initState logN view
      oracle pubA tfam transferV3)
    (hbusExt : DecodedBusLinkExt fp lanes perm RATE toNat params vk core A initState logN view
      oracle pubA tfam transferV3) :
    PositiveRadiusTraceDecode hash (fun _ => transferV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view
      friSetupDeployed oracle 7340032 :=
  positiveRadiusTraceDecode_decoded_extChallenges transferV3 sponge hCR hash fp lanes perm RATE
    toNat params vk core A initState logN view oracle pubA tfam htfMem htfMap
    Dregg2.Circuit.AirLegsDischarged.hbus_is_lookup
    Dregg2.Circuit.AirLegsDischarged.transferV3_hashSites
    Dregg2.Circuit.AirLegsDischarged.transferV3_ranges
    hlink hbusExt

/-- **⚑ THE BUS RETYPING IS CONDITIONAL, AND THE CONDITION IS NAMED.** Unlike the OOD retyping —
which is an unconditional weakening — the four-lane bus read is a genuinely DIFFERENT read of the
public block. A bus sound at the SINGLE-SLOT challenge discharges the four-lane obligation exactly
when the lane family's constant term is `1` and the three higher challenge slots of the decoded
trace's public block read `0` (`ExtChallengeLogUpSite.logupChallengeExt_lift`). Both conditions are
hypotheses here; neither is smuggled. -/
theorem decodedBusLinkExt_of_singleSlot {numCols : ℕ}
    (fp : List ℤ → BB4) (lanes : Fin 4 → BB4) (hl0 : lanes 0 = 1)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (d : EffectVmDescriptor2)
    (hzero : ∀ pi π, ∀ i : Fin 4, i ≠ 0 →
      (decodedTr oracle pubA tfam pi π).pub
        (Dregg2.Circuit.LogUpColumnLayout.challengeCol d + (i : ℕ)) = 0)
    (hbus : ∀ (pi : BatchPublicInputs) (π : BatchProof),
      AcceptsFull perm RATE toNat params vk core A initState logN view pi π →
      MatrixOracle.ColsClose friSetupDeployed.C 7340032 (oracle pi π) →
      ∀ l : Lookup, VmConstraint2.lookup l ∈ d.constraints →
        ∃ mult : List ℕ,
          BusModelOkAt fp
            (algebraMap BabyBear BB4
              (Dregg2.Circuit.LogUpColumnLayout.logupChallenge embedVal d
                (decodedTr oracle pubA tfam pi π)))
            d (decodedTr oracle pubA tfam pi π) l.table mult) :
    DecodedBusLinkExt fp lanes perm RATE toNat params vk core A initState logN view
      oracle pubA tfam d := by
  intro pi π hacc hcols l hl
  rw [logupChallengeExt_lift lanes hl0 d (decodedTr oracle pubA tfam pi π) (hzero pi π)]
  exact hbus pi π hacc hcols l hl

/-- **⚑ THE FOUR-LANE BUS OBLIGATION IS NOT NEWLY EMPTY.** `ExtChallengeLogUpSite`'s
`fire_busModelExt_nonbase` exhibits a CONCRETE sound `BusModelOkAt` — the whole bundle, not just its
conclusion — at a challenge drawn from `BB4 ∖ image(BabyBear)`, i.e. exactly the regime no
single-slot read can reach, and the discharge runs to a real membership. So `DecodedBusLinkExt`'s
per-lookup obligation is satisfiable in the retyped regime. -/
theorem decodedBusLinkExt_obligation_inhabited_offbase :
    ∃ α : BB4, α ∉ Set.range (algebraMap BabyBear BB4) ∧
      BusModelOkAt Dregg2.Circuit.ExtChallengeLogUpSite.fpExt α
        Dregg2.Circuit.LogUpColumnLayout.toyD Dregg2.Circuit.LogUpColumnLayout.toyT
        .range Dregg2.Circuit.LogUpColumnLayout.toyMult := by
  obtain ⟨α, hα, hok, -⟩ := fire_busModelExt_nonbase
  exact ⟨α, hα, hok⟩

#assert_axioms positiveRadiusTraceDecode_decoded_extChallenges
#assert_axioms positiveRadiusTraceDecode_transferV3_extChallenges
#assert_axioms decodedBusLinkExt_of_singleSlot
#assert_axioms decodedBusLinkExt_obligation_inhabited_offbase

/-- **⚑ L5·R4b FROM THE CORRECTED BASE-TYPED RESIDUAL — now a COROLLARY of the extension-typed
assembly, not a second chain.** Same `TraceWitnessed` conclusion at the same realistic deployed
instance (`friSetupDeployed`, UD radius `7340032`) from the same three residuals; the base-typed link
reaches it by LIFTING into `DecodedLdtLinkExtCons BB4`
(`decodedLdtLinkExtCons_of_decodedLdtLinkCons`) and then running §6.5. Retained because the base
statement is still a real (stronger) hypothesis someone may hold — but it no longer carries its own
derivation, so the deployed-typed assembly is the single source and the two cannot drift. -/
theorem positiveRadiusTraceDecode_decoded_cons {F : Type*} [Field F] [DecidableEq F]
    (d : EffectVmDescriptor2)
    (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (hash : List ℤ → ℤ) (fp : List ℤ → F) (embed : ℤ → F)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) {numCols : ℕ}
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (htfMem : ∀ pi π, tfam pi π .memory = []) (htfMap : ∀ pi π, tfam pi π .mapOps = [])
    (hshape : ∀ c ∈ d.constraints, ¬ isArith c → ∃ l : Lookup, c = VmConstraint2.lookup l)
    (hsites : d.hashSites = []) (hranges : d.ranges = [])
    (hlink : DecodedLdtLinkCons sponge perm RATE toNat params vk core A initState logN view
      oracle pubA tfam d)
    (hbusF : DecodedBusLink fp embed perm RATE toNat params vk core A initState logN view
      oracle pubA tfam d) :
    PositiveRadiusTraceDecode hash (fun _ => d) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view
      friSetupDeployed oracle 7340032 :=
  positiveRadiusTraceDecode_decoded_extCons d sponge hCR hash fp embed perm RATE toNat params vk
    core A initState logN view oracle pubA tfam htfMem htfMap hshape hsites hranges
    (decodedLdtLinkExtCons_of_decodedLdtLinkCons sponge perm RATE toNat params vk core A initState
      logN view oracle pubA tfam d hlink)
    hbusF

/-- The deployed `transferV3` slice of the re-derived assembly. Residual =
{`Poseidon2SpongeCR`, `DecodedLdtLinkCons @ transferV3`, `DecodedBusLink @ transferV3`}. -/
theorem positiveRadiusTraceDecode_transferV3_cons {F : Type*} [Field F] [DecidableEq F]
    (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (hash : List ℤ → ℤ) (fp : List ℤ → F) (embed : ℤ → F)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) {numCols : ℕ}
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (htfMem : ∀ pi π, tfam pi π .memory = []) (htfMap : ∀ pi π, tfam pi π .mapOps = [])
    (hlink : DecodedLdtLinkCons sponge perm RATE toNat params vk core A initState logN view
      oracle pubA tfam transferV3)
    (hbusF : DecodedBusLink fp embed perm RATE toNat params vk core A initState logN view
      oracle pubA tfam transferV3) :
    PositiveRadiusTraceDecode hash (fun _ => transferV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view
      friSetupDeployed oracle 7340032 :=
  positiveRadiusTraceDecode_decoded_cons transferV3 sponge hCR hash fp embed perm RATE toNat
    params vk core A initState logN view oracle pubA tfam htfMem htfMap
    Dregg2.Circuit.AirLegsDischarged.hbus_is_lookup
    Dregg2.Circuit.AirLegsDischarged.transferV3_hashSites
    Dregg2.Circuit.AirLegsDischarged.transferV3_ranges
    hlink hbusF

/-! ## §7 — SITE 2: the repair is NOT a second vacuity. -/

/-- `DecodedLdtLinkCons` with the OOD conjunct DELETED (`ood`/`oodRest` occur nowhere else in the
body). Used only to state the equivalence below. -/
def DecodedLdtLinkNoOodShape {numCols : ℕ}
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
    ∃ (ζ Λ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)
      (topen : TableOpening ℤ) (vCommitted root : ℤ) (idx : Nat) (siblings : List ℤ),
      topen ∈ (view pi π).1.tableOpenings ∧
      merkleRecomputeZ sponge idx vCommitted siblings = root ∧
      merkleRecomputeZ sponge idx topen.constraintEval siblings = root ∧
      (oodBatchResidual d (decodedTr oracle pubA tfam pi π) ζ qp).eval Λ
        = ((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear) ∧
      Λ ∉ exceptionalSet (oodBatchResidual d (decodedTr oracle pubA tfam pi π) ζ qp) ∧
      (∀ c ∈ d.constraints, isArith c →
          ζ ∉ exceptionalSet (constraintPoly d (decodedTr oracle pubA tfam pi π) c
                - vanishingPoly (decodedTr oracle pubA tfam pi π) * qp c)) ∧
      tracePublishedCommit (decodedTr oracle pubA tfam pi π) = pi.toPublished

/-- **THE NON-VACUITY OF THE SITE-2 REPAIR.** `DecodedLdtLinkCons` is EQUIVALENT to itself with the
OOD conjunct deleted: acceptance supplies it (`acceptsFull_gives_cons_shape`, and `AcceptsFull`
unfolds to exactly the bare `verifyAlgo` acceptance that lemma consumes). The repaired DEEP-ALI
residual therefore carries exactly the strength of the landed one minus the impossible demand — it
cannot itself empty the close-and-accepting set. -/
theorem decodedLdtLinkCons_iff_noOodShape {numCols : ℕ}
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (oracle : BatchPublicInputs → BatchProof → MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily)
    (d : EffectVmDescriptor2) :
    DecodedLdtLinkCons sponge perm RATE toNat params vk core A initState logN view
        oracle pubA tfam d
      ↔ DecodedLdtLinkNoOodShape sponge perm RATE toNat params vk core A initState logN view
        oracle pubA tfam d := by
  constructor
  · intro h pi π hacc hcols
    obtain ⟨ζ, Λ, qp, topen, _ood, vCommitted, root, _oodRest, idx, siblings,
      _hoodPt, hmem, hCommitted, hOpened, hlayout, hLam, hnonexc, hPub⟩ := h pi π hacc hcols
    exact ⟨ζ, Λ, qp, topen, vCommitted, root, idx, siblings,
      hmem, hCommitted, hOpened, hlayout, hLam, hnonexc, hPub⟩
  · intro h pi π hacc hcols
    obtain ⟨ood, oodRest, hcons⟩ :=
      acceptsFull_gives_cons_shape perm RATE toNat params vk core A initState logN
        (view pi π).1 (view pi π).2 hacc
    obtain ⟨ζ, Λ, qp, topen, vCommitted, root, idx, siblings,
      hmem, hCommitted, hOpened, hlayout, hLam, hnonexc, hPub⟩ := h pi π hacc hcols
    exact ⟨ζ, Λ, qp, topen, ood, vCommitted, root, oodRest, idx, siblings,
      hcons, hmem, hCommitted, hOpened, hlayout, hLam, hnonexc, hPub⟩

/-! ## §8 — Axiom hygiene. -/

#assert_axioms sansFS_makes_deployed_verifier_accept_nothing
#assert_axioms extractBundleSansFS_makes_verifyBatch_reject_everything
#assert_axioms extractBundleSansFS_imp_cons
#assert_axioms friLdtExtractV3Cons_imp_sansFSCons
#assert_axioms extractBundleSansFSCons_iff_noOodShape
#assert_axioms cons_ood_shape_inhabited_at_bare_verifier
#assert_axioms decodedLdtLink_makes_deployed_verifier_reject_close_runs
#assert_axioms decodedLdtLink_makes_verifyBatch_reject_every_close_run
#assert_axioms decodedLdtLink_imp_cons
#assert_axioms decodedLdtLinkCons_of_friLdtExtractCons
#assert_axioms positiveRadiusTraceDecode_decoded_cons
#assert_axioms positiveRadiusTraceDecode_transferV3_cons
#assert_axioms decodedLdtLinkCons_iff_noOodShape

end Dregg2.Circuit.FriFsDecodedOodRepair
