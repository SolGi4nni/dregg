/-
# `Dregg2.Circuit.PremiseInhabitability` — THE INSTRUMENT for the EMPTIED-PREMISE wound class,
and the systematic sweep of the tree's soundness/extraction bundles against it.

## §A The wound class

A soundness class or extraction bundle has the shape

    P  :=  ∀ run, verifier accepts run → ∃ witness, Conclusion run witness

and is used as a HYPOTHESIS of an apex theorem. The wound is this: if the deployed acceptance
predicate FORCES something that `Conclusion` CONTRADICTS, then `P` forces the verifier to reject
every run. Every apex conditioned on `P` then quantifies over an EMPTY set of accepting runs and is
vacuously true — it proves nothing, for any conclusion whatsoever (`empties_proves_anything`).

The instance that motivated this module: `AlgoStarkSoundTransferV3.FriLdtExtractV3` (`:143`)
concludes `oodPoint = [ood]` with `ood : ℤ` — ONE base felt — while the deployed verifier
`ExtFieldChallenge.verifyAlgoUnifiedFaithfulExt` forces `oodPoint = d.ζ` of length
`params.extDeg = 4`. `FriLdtExtractDeployed.friLdtExtractV3_makes_verifyBatch_reject_everything`
proves the consequence: under that bundle at the deployed `cfg*` arguments, `verifyBatch` returns
`reject` on EVERY input.

## §B WHY `#assert_axioms` / `#print axioms` CANNOT SEE IT

The vacuous apex was kernel-clean, `sorry`-free, and TRUE. Axiom auditing answers "what did the
proof depend on"; this wound is entirely about WHAT THE STATEMENT QUANTIFIES OVER. A theorem
`∀ i, acc i = true → Q i` on an `acc` that is identically `false` is a perfectly honest theorem
with an empty subject. No axiom tool, no `sorry` scan, and no "the proof is short" heuristic
detects it. Only comparing the premise's CONCLUSION against what ACCEPTANCE FORCES detects it —
which is what this module mechanizes.

## §C HOW TO USE THE INSTRUMENT (the default check)

For a new or edited bundle `P` over acceptance `weak`, and the acceptance `strong` the deployed
verifier actually evaluates:

  1. Identify a `key : run → X` the bundle constrains (here: `oodPoint`) and the `shape : A → X`
     it forces it into (here: `fun ood => [ood]`). Prove `YieldsShape P weak key shape` — a
     three-line destructuring of the bundle.
  2. Prove `∀ i, strong i → ∀ a, key i ≠ shape a` — what acceptance forces, contradicting the shape.
  3. `empties_of_yieldsShape` then gives `Empties P strong`: the premise rejects everything.
     If step 2 FAILS to prove, that is the good outcome — the bundle survives the check.

## §D THE INHABITABILITY OBLIGATION ANY REPAIR MUST DISCHARGE

A repair that swaps one conclusion shape for another may swap one vacuity for another. The
obligation is discharged by showing the new conjuncts are SUPPLIED BY ACCEPTANCE:

  * `SuppliedByAcceptance acc S` — every accepting run already satisfies the added shape;
  * `extractsWith_iff_extracts` — the repaired bundle is then EQUIVALENT to the bundle with the
    added conjuncts DELETED, so it adds exactly zero strength;
  * `extractsWith_empties_iff` — hence the added conjuncts can NEVER be the reason a premise is
    empty.

`consShape_suppliedByAcceptance` / `consShape_adds_no_strength` (§6) instantiate this for the
landed repair, generically in the bundle's core payload; `FriLdtExtractDeployed`'s
`friLdtExtractV3Faithful_iff_noOodShape` is the concrete instance.

## §E THE SWEEP (§5 records the machine-checked entries; the table is in §7)

Five bundles are PROVED to empty the deployed acceptance predicate here; the rest of the sweep,
including the honestly-retired false positives and the UNKNOWN entries, is tabulated in §7.
-/
import Dregg2.Circuit.FriLdtExtractDeployed
import Dregg2.Circuit.FriVerifierFS
import Dregg2.Circuit.OodExtChallengeLayout

namespace Dregg2.Circuit.PremiseInhabitability

universe u v w

/-! ## §1 — THE GENERIC INSTRUMENT.

Nothing here mentions FRI, STARKs, or dregg: it is a small algebra of "acceptance predicate",
"premise", and "the premise empties the acceptance". -/

/-- An acceptance predicate on runs indexed by `ι`: `acc i` says "the verifier accepts run `i`".
Bool-valued verifiers embed via `ofBool`. -/
abbrev Acc (ι : Type u) : Type u := ι → Prop

/-- The verifier accepts NOTHING. -/
def RejectsAll {ι : Type u} (acc : Acc ι) : Prop := ∀ i, ¬ acc i

/-- The verifier accepts SOMETHING (an accepting pole exists). -/
def AcceptsSome {ι : Type u} (acc : Acc ι) : Prop := ∃ i, acc i

/-- A `Bool`-valued verifier as an acceptance predicate. -/
def ofBool {ι : Type u} (v : ι → Bool) : Acc ι := fun i => v i = true

theorem not_rejectsAll_of_acceptsSome {ι : Type u} {acc : Acc ι}
    (h : AcceptsSome acc) : ¬ RejectsAll acc := by
  obtain ⟨i, hi⟩ := h
  intro hr
  exact hr i hi

theorem rejectsAll_ofBool_iff {ι : Type u} (v : ι → Bool) :
    RejectsAll (ofBool v) ↔ ∀ i, v i = false := by
  constructor
  · intro h i
    rcases Bool.eq_false_or_eq_true (v i) with hb | hb
    · exact absurd (show ofBool v i from hb) (h i)
    · exact hb
  · intro h i hi
    have hv : v i = true := hi
    rw [h i] at hv
    exact Bool.noConfusion hv

/-- **`Empties P acc` — THE WOUND, STATED.** The premise `P` forces the acceptance predicate `acc`
to reject EVERY run. Any theorem of the form `P → ∀ i, acc i → Q i` is then vacuous. -/
def Empties {ι : Type u} (P : Prop) (acc : Acc ι) : Prop := P → RejectsAll acc

/-- **The generic extraction-bundle / soundness-class shape.** Every `StarkSound`-like class and
every `FriLdtExtract`-like bundle in the tree is an instance: acceptance implies existence. -/
def Extracts {ι : Type u} {W : ι → Type v} (acc : Acc ι) (C : ∀ i, W i → Prop) : Prop :=
  ∀ i, acc i → ∃ w : W i, C i w

/-- **The basic tooth.** If acceptance REFUTES every witness the bundle claims, the bundle empties
the verifier. -/
theorem empties_of_refuted {ι : Type u} {W : ι → Type v} (acc : Acc ι) (C : ∀ i, W i → Prop)
    (hrefute : ∀ i, acc i → ∀ w, ¬ C i w) :
    Empties (Extracts acc C) acc := by
  intro h i hi
  obtain ⟨w, hw⟩ := h i hi
  exact hrefute i hi w hw

/-- **The two-verifier tooth — the one the sweep actually needs.** A bundle stated over a WEAK
acceptance (`verifyAlgo`) empties the STRONG acceptance the deployed verifier evaluates
(`verifyAlgoUnifiedFaithfulExt`), as soon as the strong acceptance's own conjuncts refute the
bundle's conclusion. The bundle need not be self-contradictory: it is enough that it is
contradictory ON THE RUNS THE DEPLOYED VERIFIER ACCEPTS. -/
theorem empties_strong_of_extracts_weak {ι : Type u} {W : ι → Type v}
    (weak strong : Acc ι) (C : ∀ i, W i → Prop)
    (hle : ∀ i, strong i → weak i)
    (hrefute : ∀ i, strong i → ∀ w, ¬ C i w) :
    Empties (Extracts weak C) strong := by
  intro h i hi
  obtain ⟨w, hw⟩ := h i (hle i hi)
  exact hrefute i hi w hw

/-- **WHY IT MATTERS: an emptied premise proves ANYTHING.** For a premise that empties `acc`, the
apex-shaped statement `P → ∀ i, acc i → Q i` holds for an ARBITRARY `Q` — including `fun _ => False`
composed with anything, and including conclusions flatly contradicting the intended one. So an apex
conditioned on an emptying premise carries exactly zero information. -/
theorem empties_proves_anything {ι : Type u} {P : Prop} {acc : Acc ι}
    (h : Empties P acc) (Q : ι → Prop) : P → ∀ i, acc i → Q i :=
  fun hP i hi => absurd hi (h hP i)

/-- The sharpest form, available wherever an accepting pole is KNOWN: an emptying premise is not
merely uninformative, it is FALSE. -/
theorem not_of_empties_of_acceptsSome {ι : Type u} {P : Prop} {acc : Acc ι}
    (h : Empties P acc) (hsome : AcceptsSome acc) : ¬ P :=
  fun hP => not_rejectsAll_of_acceptsSome hsome (h hP)

/-- Emptying transports DOWN acceptance strength: if `acc'` is stronger than `acc`, a premise that
empties `acc` empties `acc'`. -/
theorem empties_mono {ι : Type u} {P : Prop} {acc acc' : Acc ι}
    (h : Empties P acc) (hle : ∀ i, acc' i → acc i) : Empties P acc' :=
  fun hP i hi => h hP i (hle i hi)

/-- Emptying transports UP premise strength. -/
theorem empties_of_imp {ι : Type u} {P Q : Prop} {acc : Acc ι}
    (hPQ : P → Q) (h : Empties Q acc) : Empties P acc :=
  fun hP => h (hPQ hP)

/-- **The NON-emptying criterion.** If the bundle's conclusion is realizable on every accepting run
and the verifier accepts something, the bundle is TRUE and empties nothing. This is the shape a
"this site is NOT wounded" verdict should take when it can be discharged. -/
theorem not_empties_of_realizable {ι : Type u} {W : ι → Type v} {acc : Acc ι}
    {C : ∀ i, W i → Prop}
    (hreal : ∀ i, acc i → ∃ w, C i w) (hsome : AcceptsSome acc) :
    ¬ Empties (Extracts acc C) acc :=
  fun h => not_rejectsAll_of_acceptsSome hsome (h hreal)

/-! ## §2 — THE FORM THE SWEEP USES: a bundle that forces a KEY into a SHAPE.

Every FRI-LDT bundle in this tree constrains ONE verifier-visible quantity (`oodPoint`) into ONE
shape (`[ood]`). `YieldsShape` names that pattern so each sweep entry is a three-line destructuring
plus one application of `empties_of_yieldsShape`. -/

/-- **`YieldsShape P weak key shape`** — on every `weak`-accepting run, the premise `P` produces a
value `a : A` with `key i = shape a`. -/
def YieldsShape {ι : Type u} {A : Type v} {X : Type w}
    (P : Prop) (weak : Acc ι) (key : ι → X) (shape : A → X) : Prop :=
  P → ∀ i, weak i → ∃ a : A, key i = shape a

/-- **THE INSTRUMENT, in sweep form.** A premise that forces `key` into `shape` on every
weak-accepting run empties any stronger acceptance whose own conjuncts pin `key` OUT of `shape`. -/
theorem empties_of_yieldsShape {ι : Type u} {A : Type v} {X : Type w}
    {P : Prop} {weak strong : Acc ι} {key : ι → X} {shape : A → X}
    (hy : YieldsShape P weak key shape)
    (hle : ∀ i, strong i → weak i)
    (hrefute : ∀ i, strong i → ∀ a : A, key i ≠ shape a) :
    Empties P strong := by
  intro hP i hi
  obtain ⟨a, ha⟩ := hy hP i (hle i hi)
  exact hrefute i hi a ha

/-! ## §3 — THE REPAIR OBLIGATION, GENERICALLY DISCHARGEABLE.

A repair replaces the refuted conjuncts with new ones. The obligation: prove the new ones are
SUPPLIED BY ACCEPTANCE, whence the repaired bundle is EQUIVALENT to the bundle with them deleted
and can never itself be the reason a premise is empty. -/

/-- **`SuppliedByAcceptance acc S`** — every accepting run already satisfies the shape `S`. -/
def SuppliedByAcceptance {ι : Type u} {V : ι → Type w} (acc : Acc ι) (S : ∀ i, V i → Prop) : Prop :=
  ∀ i, acc i → ∃ v, S i v

/-- A bundle whose conclusion is a CORE payload `C` conjoined with an added SHAPE `S`. -/
def ExtractsWith {ι : Type u} {W : ι → Type v} {V : ι → Type w} (acc : Acc ι)
    (C : ∀ i, W i → Prop) (S : ∀ i, V i → Prop) : Prop :=
  ∀ i, acc i → ∃ (w : W i) (v : V i), C i w ∧ S i v

/-- **THE REPAIR OBLIGATION, DISCHARGED.** If the added shape is supplied by acceptance, the
repaired bundle is EQUIVALENT to the bundle with the added conjuncts deleted: the repair adds
exactly zero strength. -/
theorem extractsWith_iff_extracts {ι : Type u} {W : ι → Type v} {V : ι → Type w}
    {acc : Acc ι} {C : ∀ i, W i → Prop} {S : ∀ i, V i → Prop}
    (hsupp : SuppliedByAcceptance acc S) :
    ExtractsWith acc C S ↔ Extracts acc C := by
  constructor
  · intro h i hi
    obtain ⟨w, _, hC, _⟩ := h i hi
    exact ⟨w, hC⟩
  · intro h i hi
    obtain ⟨w, hC⟩ := h i hi
    obtain ⟨v, hS⟩ := hsupp i hi
    exact ⟨w, v, hC, hS⟩

/-- **The added conjuncts are NEVER the reason a premise is empty.** Emptiness of the repaired
bundle is literally the same proposition as emptiness of the core bundle. -/
theorem extractsWith_empties_iff {ι : Type u} {W : ι → Type v} {V : ι → Type w}
    {acc : Acc ι} {C : ∀ i, W i → Prop} {S : ∀ i, V i → Prop}
    (hsupp : SuppliedByAcceptance acc S) :
    Empties (ExtractsWith acc C S) acc ↔ Empties (Extracts acc C) acc := by
  rw [propext (extractsWith_iff_extracts (C := C) hsupp)]

/-- A supplied shape can never be the refuted one (whenever an accepting pole exists) — the
`SuppliedByAcceptance` and `hrefute` hypotheses of the instrument are mutually exclusive. -/
theorem supplied_never_refuted {ι : Type u} {V : ι → Type w} {acc : Acc ι} {S : ∀ i, V i → Prop}
    (hsupp : SuppliedByAcceptance acc S) (hsome : AcceptsSome acc) :
    ¬ (∀ i, acc i → ∀ v, ¬ S i v) := by
  intro hrefute
  obtain ⟨i, hi⟩ := hsome
  obtain ⟨v, hv⟩ := hsupp i hi
  exact hrefute i hi v hv

/-! ## §4 — INSTANTIATION AT THE DEPLOYED FRI VERIFIER. -/

open Polynomial
open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.DescriptorIR2 (VmTrace EffectVmDescriptor2 VmConstraint2 TraceFamily)
open Dregg2.Circuit.FriVerifierBridge (ProofView)
open Dregg2.Circuit.FriBatchedOracle (MatrixOracle)
open Dregg2.Circuit.FriDeployedRateInstance (friSetupDeployed)
open Dregg2.Circuit.FriVerifier
  (verifyAlgo BatchProofData WrapPublics FriParams RecursionVk FriCore FieldArith TableOpening
   fullChecks)
open Dregg2.Circuit.CircuitSoundness
  (BatchPublicInputs BatchProof Verdict VerifyKey verifyBatch cfgPerm cfgRATE cfgToNat cfgParams
   cfgVk cfgCore cfgA cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN cfgView cfgExtView)
open Dregg2.Circuit.ExtFieldChallenge
  (ExtFriCore ExtFriArith ExtVerifierView verifyAlgoUnifiedFaithfulExt
   verifyAlgoUnifiedFaithfulExt_imp_verifyAlgoUnified)
open Dregg2.Circuit.FriChallengerUnified (verifyAlgoUnified_imp_verifyAlgo)
open Dregg2.Circuit.FriLdtExtractDeployed
  (ExtProofView faithfulExt_forces_oodPoint_ne_singleton faithfulExt_accept_gives_cons_shape
   deployed_accepting_pole_nonempty)

/-- The index type of a verifier run: the light client's `(public inputs, proof)` pair. -/
abbrev BatchRun := BatchPublicInputs × BatchProof

/-- **The DEPLOYED acceptance predicate** — the one `CircuitSoundness.verifyBatch` evaluates. -/
def deployedAcc
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (extCore : ExtFriCore ℤ) (extA : ExtFriArith ℤ) (W : ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) (extView : ExtProofView) : Acc BatchRun :=
  ofBool fun r =>
    verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core A extCore extA W initState logN
      (view r.1 r.2).1 (view r.1 r.2).2 (extView r.1 r.2)

/-- **The BARE acceptance predicate** — `verifyAlgo` at `fullChecks`, the antecedent every landed
FRI-LDT bundle is stated over (`AlgoStarkSoundGeneral.AcceptsFull`). -/
def bareAcc
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) : Acc BatchRun :=
  ofBool fun r =>
    verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits) initState logN
      (view r.1 r.2).1 (view r.1 r.2).2

/-- Deployed acceptance is STRONGER than bare acceptance (the landed strengthening chain
`verifyAlgoUnifiedFaithfulExt ⟹ verifyAlgoUnified ⟹ verifyAlgo`). -/
theorem deployedAcc_imp_bareAcc
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (extCore : ExtFriCore ℤ) (extA : ExtFriArith ℤ) (W : ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) (extView : ExtProofView) :
    ∀ r, deployedAcc perm RATE toNat params vk core A extCore extA W initState logN view extView r →
      bareAcc perm RATE toNat params vk core A initState logN view r := by
  intro r hr
  exact verifyAlgoUnified_imp_verifyAlgo perm RATE toNat params vk core A initState logN
    (view r.1 r.2).1 (view r.1 r.2).2
    (verifyAlgoUnifiedFaithfulExt_imp_verifyAlgoUnified perm RATE toNat params vk core A
      extCore extA W initState logN (view r.1 r.2).1 (view r.1 r.2).2 (extView r.1 r.2) hr)

/-- **THE REFUTER.** Deployed acceptance pins the OOD point to the four-lane transcript squeeze
`d.ζ`, so it refutes EVERY singleton claim. This is the `hrefute` input the whole sweep uses;
its content is `FriLdtExtractDeployed.faithfulExt_forces_oodPoint_ne_singleton`. -/
theorem deployedAcc_refutes_singleton
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (extCore : ExtFriCore ℤ) (extA : ExtFriArith ℤ) (W : ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) (extView : ExtProofView) :
    ∀ r, deployedAcc perm RATE toNat params vk core A extCore extA W initState logN view extView r →
      ∀ ood : ℤ, (view r.1 r.2).1.oodPoint ≠ [ood] := by
  intro r hr ood
  exact faithfulExt_forces_oodPoint_ne_singleton perm RATE toNat params vk core A extCore extA W
    initState logN (view r.1 r.2).1 (view r.1 r.2).2 (extView r.1 r.2) hr ood

/-- The apex consequence of any emptying premise, at the DEPLOYED `cfg*` arguments:
`verifyBatch` returns `reject` on every key/public-input/proof triple. -/
theorem verifyBatch_reject_of_empties_cfg {P : Prop}
    (h : Empties P (deployedAcc cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
      cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN cfgView cfgExtView))
    (hP : P) (vkey : VerifyKey) (pi : BatchPublicInputs) (π : BatchProof) :
    verifyBatch vkey pi π = Verdict.reject := by
  have hne := h hP (pi, π)
  have hfalse :
      verifyAlgoUnifiedFaithfulExt cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
        cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN (cfgView pi π).1 (cfgView pi π).2
        (cfgExtView pi π) = false := by
    rcases Bool.eq_false_or_eq_true
        (verifyAlgoUnifiedFaithfulExt cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
          cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN (cfgView pi π).1 (cfgView pi π).2
          (cfgExtView pi π)) with hb | hb
    · exact absurd
        (show deployedAcc cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA cfgExtCore
          cfgExtA cfgExtW cfgInitState cfgLogN cfgView cfgExtView (pi, π) from hb) hne
    · exact hb
  simp [verifyBatch, hfalse]

/-! ## §5 — THE SWEEP: five bundles PROVED to empty the deployed acceptance predicate.

Each entry is (a) a `YieldsShape` destructuring of the LANDED bundle — which typechecks only if the
bundle really does force the singleton — and (b) one application of `empties_of_yieldsShape`. The
landed definitions are READ, never edited. -/

/-! ### E1 — `AlgoStarkSoundTransferV3.FriLdtExtractV3` (`AlgoStarkSoundTransferV3.lean:131`,
singleton at `:143`). The originally-diagnosed site; re-derived here through the instrument to show
the instrument subsumes the hand-written proof
(`FriLdtExtractDeployed.friLdtExtractV3_makes_verifyBatch_reject_everything`). -/

theorem friLdtExtractV3_yieldsShape
    (sponge : List ℤ → ℤ) (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) :
    YieldsShape
      (Dregg2.Circuit.AlgoStarkSoundTransferV3.FriLdtExtractV3 sponge hash perm RATE toNat params
        vk core A initState logN view)
      (bareAcc perm RATE toNat params vk core A initState logN view)
      (fun r => (view r.1 r.2).1.oodPoint) (fun ood : ℤ => [ood]) := by
  intro h r hr
  obtain ⟨_, _, _, _, _, ood, _, _, _, _, _, hoodPt, _⟩ := h r.1 r.2 hr
  exact ⟨ood, hoodPt⟩

/-- **E1 TOOTH.** -/
theorem friLdtExtractV3_empties_deployed
    (sponge : List ℤ → ℤ) (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (extCore : ExtFriCore ℤ) (extA : ExtFriArith ℤ) (W : ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) (extView : ExtProofView) :
    Empties
      (Dregg2.Circuit.AlgoStarkSoundTransferV3.FriLdtExtractV3 sponge hash perm RATE toNat params
        vk core A initState logN view)
      (deployedAcc perm RATE toNat params vk core A extCore extA W initState logN view extView) :=
  empties_of_yieldsShape
    (friLdtExtractV3_yieldsShape sponge hash perm RATE toNat params vk core A initState logN view)
    (deployedAcc_imp_bareAcc perm RATE toNat params vk core A extCore extA W initState logN view
      extView)
    (deployedAcc_refutes_singleton perm RATE toNat params vk core A extCore extA W initState logN
      view extView)

/-! ### E2 — `AlgoStarkSoundGeneral.FriLdtExtract` (`AlgoStarkSoundGeneral.lean:134`, singleton at
`:147`). The ∀-descriptor form of E1, over the Skolemized extracted trace `tr`. Same wound. -/

theorem friLdtExtract_yieldsShape
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : BatchPublicInputs → BatchProof → VmTrace) (d : EffectVmDescriptor2) :
    YieldsShape
      (Dregg2.Circuit.AlgoStarkSoundGeneral.FriLdtExtract sponge perm RATE toNat params vk core A
        initState logN view tr d)
      (bareAcc perm RATE toNat params vk core A initState logN view)
      (fun r => (view r.1 r.2).1.oodPoint) (fun ood : ℤ => [ood]) := by
  intro h r hr
  obtain ⟨_, _, _, _, ood, _, _, _, _, _, hoodPt, _⟩ := h r.1 r.2 hr
  exact ⟨ood, hoodPt⟩

/-- **E2 TOOTH.** -/
theorem friLdtExtract_empties_deployed
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (extCore : ExtFriCore ℤ) (extA : ExtFriArith ℤ) (W : ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) (extView : ExtProofView)
    (tr : BatchPublicInputs → BatchProof → VmTrace) (d : EffectVmDescriptor2) :
    Empties
      (Dregg2.Circuit.AlgoStarkSoundGeneral.FriLdtExtract sponge perm RATE toNat params vk core A
        initState logN view tr d)
      (deployedAcc perm RATE toNat params vk core A extCore extA W initState logN view extView) :=
  empties_of_yieldsShape
    (friLdtExtract_yieldsShape sponge perm RATE toNat params vk core A initState logN view tr d)
    (deployedAcc_imp_bareAcc perm RATE toNat params vk core A extCore extA W initState logN view
      extView)
    (deployedAcc_refutes_singleton perm RATE toNat params vk core A extCore extA W initState logN
      view extView)

/-- **E2 APEX CONSEQUENCE**, at the deployed `cfg*` arguments: `verifyBatch` rejects everything. -/
theorem friLdtExtract_makes_verifyBatch_reject_everything
    (sponge : List ℤ → ℤ)
    (tr : BatchPublicInputs → BatchProof → VmTrace) (d : EffectVmDescriptor2)
    (h : Dregg2.Circuit.AlgoStarkSoundGeneral.FriLdtExtract sponge cfgPerm cfgRATE cfgToNat
      cfgParams cfgVk cfgCore cfgA cfgInitState cfgLogN cfgView tr d)
    (vkey : VerifyKey) (pi : BatchPublicInputs) (π : BatchProof) :
    verifyBatch vkey pi π = Verdict.reject :=
  verifyBatch_reject_of_empties_cfg
    (friLdtExtract_empties_deployed sponge cfgPerm cfgRATE cfgToNat cfgParams cfgVk cfgCore cfgA
      cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN cfgView cfgExtView tr d)
    h vkey pi π

/-! ### E3 — `FriVerifierFS.ExtractBundleSansFS` (`FriVerifierFS.lean:100`, singleton at `:112`).
The Stage-2 FS re-basing bundle: E1's body with the two Fiat–Shamir conjuncts deleted. Deleting the
FS conjuncts does not touch the OOD conjunct, so the wound is inherited verbatim. -/

theorem extractBundleSansFS_yieldsShape
    (sponge : List ℤ → ℤ) (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) :
    YieldsShape
      (Dregg2.Circuit.FriVerifierFS.ExtractBundleSansFS sponge hash perm RATE toNat params vk core
        A initState logN view)
      (bareAcc perm RATE toNat params vk core A initState logN view)
      (fun r => (view r.1 r.2).1.oodPoint) (fun ood : ℤ => [ood]) := by
  intro h r hr
  obtain ⟨_, _, _, _, _, ood, _, _, _, _, _, hoodPt, _⟩ := h r.1 r.2 hr
  exact ⟨ood, hoodPt⟩

/-- **E3 TOOTH.** -/
theorem extractBundleSansFS_empties_deployed
    (sponge : List ℤ → ℤ) (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (extCore : ExtFriCore ℤ) (extA : ExtFriArith ℤ) (W : ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) (extView : ExtProofView) :
    Empties
      (Dregg2.Circuit.FriVerifierFS.ExtractBundleSansFS sponge hash perm RATE toNat params vk core
        A initState logN view)
      (deployedAcc perm RATE toNat params vk core A extCore extA W initState logN view extView) :=
  empties_of_yieldsShape
    (extractBundleSansFS_yieldsShape sponge hash perm RATE toNat params vk core A initState logN
      view)
    (deployedAcc_imp_bareAcc perm RATE toNat params vk core A extCore extA W initState logN view
      extView)
    (deployedAcc_refutes_singleton perm RATE toNat params vk core A extCore extA W initState logN
      view extView)

/-- **E3 APEX CONSEQUENCE.** -/
theorem extractBundleSansFS_makes_verifyBatch_reject_everything
    (sponge : List ℤ → ℤ) (hash : List ℤ → ℤ)
    (h : Dregg2.Circuit.FriVerifierFS.ExtractBundleSansFS sponge hash cfgPerm cfgRATE cfgToNat
      cfgParams cfgVk cfgCore cfgA cfgInitState cfgLogN cfgView)
    (vkey : VerifyKey) (pi : BatchPublicInputs) (π : BatchProof) :
    verifyBatch vkey pi π = Verdict.reject :=
  verifyBatch_reject_of_empties_cfg
    (extractBundleSansFS_empties_deployed sponge hash cfgPerm cfgRATE cfgToNat cfgParams cfgVk
      cfgCore cfgA cfgExtCore cfgExtA cfgExtW cfgInitState cfgLogN cfgView cfgExtView)
    h vkey pi π

/-! ### E4/E5 — the DECODED links, which carry an EXTRA antecedent.

`FriDecodedTraceWitness.DecodedLdtLink` (`:450`, singleton at `:464`) and
`OodExtChallengeLayout.DecodedLdtLinkExt` (`:603`, singleton at `:617`) fire only on runs that are
BOTH accepting and `ColsClose` to the deployed RS code. So the honest tooth is not "the deployed
verifier rejects everything" but the sharper conjunction: under these bundles, NO deployed-accepting
run is `ColsClose` — the deep-ALI residual is stated about a set of runs it has itself emptied. -/

/-- Deployed acceptance CONJOINED with the decoder's proximity antecedent. -/
def deployedAccClose {numCols : ℕ}
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (extCore : ExtFriCore ℤ) (extA : ExtFriArith ℤ) (W : ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) (extView : ExtProofView)
    (oracle : BatchPublicInputs → BatchProof →
      MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear) : Acc BatchRun :=
  fun r =>
    deployedAcc perm RATE toNat params vk core A extCore extA W initState logN view extView r
      ∧ MatrixOracle.ColsClose friSetupDeployed.C 7340032 (oracle r.1 r.2)

/-- Bare acceptance conjoined with the same proximity antecedent — the bundles' actual antecedent. -/
def bareAccClose {numCols : ℕ}
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (oracle : BatchPublicInputs → BatchProof →
      MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear) : Acc BatchRun :=
  fun r =>
    bareAcc perm RATE toNat params vk core A initState logN view r
      ∧ MatrixOracle.ColsClose friSetupDeployed.C 7340032 (oracle r.1 r.2)

theorem deployedAccClose_imp_bareAccClose {numCols : ℕ}
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (extCore : ExtFriCore ℤ) (extA : ExtFriArith ℤ) (W : ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) (extView : ExtProofView)
    (oracle : BatchPublicInputs → BatchProof →
      MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear) :
    ∀ r, deployedAccClose perm RATE toNat params vk core A extCore extA W initState logN view
        extView oracle r →
      bareAccClose perm RATE toNat params vk core A initState logN view oracle r := by
  intro r hr
  exact ⟨deployedAcc_imp_bareAcc perm RATE toNat params vk core A extCore extA W initState logN
    view extView r hr.1, hr.2⟩

theorem deployedAccClose_refutes_singleton {numCols : ℕ}
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (extCore : ExtFriCore ℤ) (extA : ExtFriArith ℤ) (W : ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) (extView : ExtProofView)
    (oracle : BatchPublicInputs → BatchProof →
      MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear) :
    ∀ r, deployedAccClose perm RATE toNat params vk core A extCore extA W initState logN view
        extView oracle r →
      ∀ ood : ℤ, (view r.1 r.2).1.oodPoint ≠ [ood] := by
  intro r hr ood
  exact deployedAcc_refutes_singleton perm RATE toNat params vk core A extCore extA W initState
    logN view extView r hr.1 ood

theorem decodedLdtLink_yieldsShape {numCols : ℕ}
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (oracle : BatchPublicInputs → BatchProof →
      MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily) (d : EffectVmDescriptor2) :
    YieldsShape
      (Dregg2.Circuit.FriDecodedTraceWitness.DecodedLdtLink sponge perm RATE toNat params vk core A
        initState logN view oracle pubA tfam d)
      (bareAccClose perm RATE toNat params vk core A initState logN view oracle)
      (fun r => (view r.1 r.2).1.oodPoint) (fun ood : ℤ => [ood]) := by
  intro h r hr
  obtain ⟨_, _, _, _, ood, _, _, _, _, hoodPt, _⟩ := h r.1 r.2 hr.1 hr.2
  exact ⟨ood, hoodPt⟩

/-- **E4 TOOTH.** -/
theorem decodedLdtLink_empties_deployedClose {numCols : ℕ}
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (extCore : ExtFriCore ℤ) (extA : ExtFriArith ℤ) (W : ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) (extView : ExtProofView)
    (oracle : BatchPublicInputs → BatchProof →
      MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily) (d : EffectVmDescriptor2) :
    Empties
      (Dregg2.Circuit.FriDecodedTraceWitness.DecodedLdtLink sponge perm RATE toNat params vk core A
        initState logN view oracle pubA tfam d)
      (deployedAccClose perm RATE toNat params vk core A extCore extA W initState logN view
        extView oracle) :=
  empties_of_yieldsShape
    (decodedLdtLink_yieldsShape sponge perm RATE toNat params vk core A initState logN view oracle
      pubA tfam d)
    (deployedAccClose_imp_bareAccClose perm RATE toNat params vk core A extCore extA W initState
      logN view extView oracle)
    (deployedAccClose_refutes_singleton perm RATE toNat params vk core A extCore extA W initState
      logN view extView oracle)

/-- **E4, read out.** Under the decoded link, NO deployed-accepting run is `ColsClose` to the
deployed RS code — the proximity hypothesis and deployed acceptance are jointly impossible. -/
theorem decodedLdtLink_forbids_close_on_accepting {numCols : ℕ}
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (extCore : ExtFriCore ℤ) (extA : ExtFriArith ℤ) (W : ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) (extView : ExtProofView)
    (oracle : BatchPublicInputs → BatchProof →
      MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily) (d : EffectVmDescriptor2)
    (h : Dregg2.Circuit.FriDecodedTraceWitness.DecodedLdtLink sponge perm RATE toNat params vk core
      A initState logN view oracle pubA tfam d)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hacc : verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core A extCore extA W initState
      logN (view pi π).1 (view pi π).2 (extView pi π) = true) :
    ¬ MatrixOracle.ColsClose friSetupDeployed.C 7340032 (oracle pi π) := by
  intro hclose
  exact decodedLdtLink_empties_deployedClose sponge perm RATE toNat params vk core A extCore extA W
    initState logN view extView oracle pubA tfam d h (pi, π) ⟨hacc, hclose⟩

theorem decodedLdtLinkExt_yieldsShape (E : Type*) [Field E] [Algebra BabyBear E] [DecidableEq E]
    {numCols : ℕ}
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (oracle : BatchPublicInputs → BatchProof →
      MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily) (d : EffectVmDescriptor2) :
    YieldsShape
      (Dregg2.Circuit.OodExtChallengeLayout.DecodedLdtLinkExt E sponge perm RATE toNat params vk
        core A initState logN view oracle pubA tfam d)
      (bareAccClose perm RATE toNat params vk core A initState logN view oracle)
      (fun r => (view r.1 r.2).1.oodPoint) (fun ood : ℤ => [ood]) := by
  intro h r hr
  obtain ⟨_, _, _, _, ood, _, _, _, _, hoodPt, _⟩ := h r.1 r.2 hr.1 hr.2
  exact ⟨ood, hoodPt⟩

/-- **E5 TOOTH.** The extension-typed repair of `DecodedLdtLink` retyped `ζ`/`Λ` into the quartic
challenge field but LEFT the OOD point a base-felt singleton — so the challenge-typing repair did
NOT close this wound. -/
theorem decodedLdtLinkExt_empties_deployedClose (E : Type*) [Field E] [Algebra BabyBear E]
    [DecidableEq E] {numCols : ℕ}
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (extCore : ExtFriCore ℤ) (extA : ExtFriArith ℤ) (W : ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) (extView : ExtProofView)
    (oracle : BatchPublicInputs → BatchProof →
      MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (pubA : BatchPublicInputs → BatchProof → Assignment)
    (tfam : BatchPublicInputs → BatchProof → TraceFamily) (d : EffectVmDescriptor2) :
    Empties
      (Dregg2.Circuit.OodExtChallengeLayout.DecodedLdtLinkExt E sponge perm RATE toNat params vk
        core A initState logN view oracle pubA tfam d)
      (deployedAccClose perm RATE toNat params vk core A extCore extA W initState logN view
        extView oracle) :=
  empties_of_yieldsShape
    (decodedLdtLinkExt_yieldsShape E sponge perm RATE toNat params vk core A initState logN view
      oracle pubA tfam d)
    (deployedAccClose_imp_bareAccClose perm RATE toNat params vk core A extCore extA W initState
      logN view extView oracle)
    (deployedAccClose_refutes_singleton perm RATE toNat params vk core A extCore extA W initState
      logN view extView oracle)

/-! ## §6 — THE REPAIR OBLIGATION, FIRED ON THE LANDED REPAIR.

The corrected shape (`ood :: oodRest`, equal to the transcript's `ζ`, of length `params.extDeg`) is
SUPPLIED BY ACCEPTANCE. Hence, by `extractsWith_iff_extracts`, ANY bundle carrying it is equivalent
to the same bundle with those conjuncts deleted — for an ARBITRARY core payload. That is the
generic form of `FriLdtExtractDeployed.friLdtExtractV3Faithful_iff_noOodShape`, and it is what makes
the repair provably incapable of introducing a second vacuity. -/

/-- The corrected OOD shape, as a predicate on the run and the pair `(ood, oodRest)`. -/
def consShape
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (initState : List ℤ) (logN : Nat) (view : ProofView)
    (r : BatchRun) (p : ℤ × List ℤ) : Prop :=
  (view r.1 r.2).1.oodPoint = p.1 :: p.2
    ∧ p.1 :: p.2 = (Dregg2.Circuit.FriChallengerUnified.deriveTranscript perm RATE toNat params
        initState logN (view r.1 r.2).1 (view r.1 r.2).2).ζ
    ∧ (p.1 :: p.2).length = params.extDeg

/-- **THE INHABITABILITY RESULT, GENERIC.** The corrected shape is supplied by deployed acceptance. -/
theorem consShape_suppliedByAcceptance
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (extCore : ExtFriCore ℤ) (extA : ExtFriArith ℤ) (W : ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) (extView : ExtProofView) :
    SuppliedByAcceptance
      (deployedAcc perm RATE toNat params vk core A extCore extA W initState logN view extView)
      (fun r p => consShape perm RATE toNat params initState logN view r p) := by
  intro r hr
  obtain ⟨ood, oodRest, h1, h2, h3⟩ :=
    faithfulExt_accept_gives_cons_shape perm RATE toNat params vk core A extCore extA W initState
      logN (view r.1 r.2).1 (view r.1 r.2).2 (extView r.1 r.2) hr
  exact ⟨(ood, oodRest), h1, h2, h3⟩

/-- **THE REPAIR ADDS EXACTLY ZERO STRENGTH — for ANY core payload.** A bundle carrying the
corrected OOD shape is equivalent to the same bundle with those conjuncts deleted. So no repair
built on this shape can be the reason a premise is empty. -/
theorem consShape_adds_no_strength {W : BatchRun → Type v} (C : ∀ r, W r → Prop)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (extCore : ExtFriCore ℤ) (extA : ExtFriArith ℤ) (W' : ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) (extView : ExtProofView) :
    ExtractsWith
        (deployedAcc perm RATE toNat params vk core A extCore extA W' initState logN view extView)
        C (fun r p => consShape perm RATE toNat params initState logN view r p)
      ↔ Extracts
        (deployedAcc perm RATE toNat params vk core A extCore extA W' initState logN view extView)
        C :=
  extractsWith_iff_extracts
    (consShape_suppliedByAcceptance perm RATE toNat params vk core A extCore extA W' initState
      logN view extView)

/-- **THE CONTRAST, IN ONE STATEMENT.** The corrected shape can never be refuted by acceptance
(wherever an accepting pole exists), whereas the singleton shape is refuted on EVERY accepting run
(`deployedAcc_refutes_singleton`). That asymmetry is exactly the difference between the repair and
the wound. -/
theorem consShape_never_refuted
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (extCore : ExtFriCore ℤ) (extA : ExtFriArith ℤ) (W : ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) (extView : ExtProofView)
    (hsome : AcceptsSome
      (deployedAcc perm RATE toNat params vk core A extCore extA W initState logN view extView)) :
    ¬ (∀ r, deployedAcc perm RATE toNat params vk core A extCore extA W initState logN view
          extView r →
        ∀ p, ¬ consShape perm RATE toNat params initState logN view r p) :=
  supplied_never_refuted
    (consShape_suppliedByAcceptance perm RATE toNat params vk core A extCore extA W initState logN
      view extView) hsome

/-! ## §7 — THE SWEEP TABLE.

Verdicts: **EMPTIES** = machine-checked here that the premise forces the deployed acceptance
predicate to reject everything (and so any apex conditioned on it is vacuous). **NO CONTRADICTION
FOUND** = the conclusion constrains no quantity the deployed acceptance predicate pins, so step 2 of
the §C recipe has no candidate; recorded as a retired false positive, not as a proof of
inhabitability. **UNKNOWN** = parametric over an abstract acceptance predicate that is never
instantiated at deployed arguments, so the check cannot be run.

| # | class / bundle | file:line | verdict | evidence |
|---|---|---|---|---|
| E1 | `AlgoStarkSoundTransferV3.FriLdtExtractV3` | `AlgoStarkSoundTransferV3.lean:131` (singleton `:143`) | **EMPTIES** | `friLdtExtractV3_empties_deployed`; apex form `FriLdtExtractDeployed.friLdtExtractV3_makes_verifyBatch_reject_everything` |
| E2 | `AlgoStarkSoundGeneral.FriLdtExtract` | `AlgoStarkSoundGeneral.lean:134` (singleton `:147`) | **EMPTIES** | `friLdtExtract_empties_deployed`, `friLdtExtract_makes_verifyBatch_reject_everything` |
| E3 | `FriVerifierFS.ExtractBundleSansFS` | `FriVerifierFS.lean:100` (singleton `:112`) | **EMPTIES** | `extractBundleSansFS_empties_deployed`, `extractBundleSansFS_makes_verifyBatch_reject_everything` |
| E4 | `FriDecodedTraceWitness.DecodedLdtLink` | `FriDecodedTraceWitness.lean:450` (singleton `:464`) | **EMPTIES** (of accepting ∧ `ColsClose`) | `decodedLdtLink_empties_deployedClose`, `decodedLdtLink_forbids_close_on_accepting` |
| E5 | `OodExtChallengeLayout.DecodedLdtLinkExt` | `OodExtChallengeLayout.lean:603` (singleton `:617`) | **EMPTIES** (of accepting ∧ `ColsClose`) | `decodedLdtLinkExt_empties_deployedClose` — the challenge-retyping repair moved `ζ`/`Λ` into the quartic field but left `oodPoint` a base singleton |
| S1 | `CircuitSoundness.StarkSound` | `CircuitSoundness.lean:482` | NO CONTRADICTION FOUND | conclusion is `∃ minit mfin maddrs t, Satisfied2 hash (R pi.effect) … ∧ tracePublishedCommit t = pi.toPublished`; every conjunct is about the existentially-bound witness, and its only link to the run is through the `opaque tracePublishedCommit` (`CircuitSoundness.lean:~470`), which acceptance constrains in no way. No `key`/`shape` pair exists to run step 2 on. |
| S2 | `FriVerifierBridge.AlgoStarkSound` | `FriVerifierBridge.lean:75` | NO CONTRADICTION FOUND | same conclusion as S1 over the bare `verifyAlgo` antecedent; no verifier-forced quantity appears. NB the singleton DOES appear at `FriVerifierBridge.lean:185`, but as a HYPOTHESIS of a lemma, not a conclusion — see A1. |
| S3 | `StarkSoundReduction.DeployedTraceExtract` | `StarkSoundReduction.lean:92` | NO CONTRADICTION FOUND | conclusion is `MainAirAcceptF` + LogUp/range/memory legs + `tracePublishedCommit t = pi.toPublished`; no `oodPoint`, no transcript quantity. |
| S4 | `CircuitCompleteness.StarkComplete` | `CircuitCompleteness.lean:147` | N/A — DUAL DIRECTION | its premise is a `Satisfied2` witness, not verifier acceptance; the analogous wound would be "no witness satisfies the premise", a COMPLETENESS-side emptiness, not this class. Not checked here. |
| S5 | `AggAirSound.FriExtract` | `AggAirSound.lean:157` | UNKNOWN | quantified over an ABSTRACT `ChildVerifierSat`/`verify`; never instantiated at the deployed verifier in-tree, so there is no acceptance predicate to test against. |
| S6 | `GroundedApex.BindingExtract` | `GroundedApex.lean:93` | UNKNOWN | same shape: abstract `verify : Proof → Bool` on `agg.bindingProof`, no deployed instantiation. |
| S7 | `ShieldedMerkleRootPin.AccumulatorSound` | `ShieldedMerkleRootPin.lean:252` | NO CONTRADICTION FOUND | `∀ leaf path, foldPath H leaf path = committedRoot → IsCommitted leaf`; `IsCommitted` is an abstract predicate parameter, so nothing can refute the conclusion. |
| S8 | `FriVerifier.FriLowDegreeSound` | `FriVerifier.lean:995` | NO CONTRADICTION FOUND | conclusion `∃ w : GenuineWitness F, w.exists_ ∧ proof.exposedSegment = pub.segment`; the second conjunct IS verifier-visible but is exactly what `verifyAlgo`'s own segment check forces, so acceptance AGREES with it rather than refuting it. |
| S9 | `ClosureAll.ClosedLogExtract` | `ClosureAll.lean:1539` | N/A — no verifier antecedent | premise is `Satisfied2` + `StateDecodeLog`, not acceptance. |
| A1 | singleton as a LEMMA HYPOTHESIS: `AlgoStarkSoundTransferV3.lean:183,231`, `StarkSoundReduce.lean:93,137,170`, `OodColumnLayout.lean:229`, `FriVerifierBridge.lean:185`, `DeployedRefinesProof.lean:103`, `FriVerifierQuery.lean:339`, `OodQuotientConsistency.lean:201`, `FriVerifier.lean:863,875,917` | APPLICABILITY-DEAD at the deployed verifier | these are TRUE theorems, not vacuous ones; but `deployedAcc_refutes_singleton` shows their `hoodPt : oodPoint = [ood]` hypothesis is unsatisfiable on any deployed-accepting run, so they can never be applied on the deployed path. `FriLdtExtractDeployed` §4 already re-proves the load-bearing ones at the `ood :: oodRest` shape (`…_cons`). |

**Not claimed.** No entry above asserts that a bundle IS satisfiable at the deployed configuration.
`cfgPerm`/`cfgParams`/`cfgView`/… are `opaque`, so `AcceptsSome (deployedAcc cfg…)` is not provable
by anyone, and every "NO CONTRADICTION FOUND" is exactly that: the §C check found no candidate
`key`/`shape`, not a proof of inhabitability. The one place inhabitability IS proved is §6, and it
is proved where it matters — about the REPAIR's added conjuncts, which is the obligation a repair
must discharge. -/

/-! ## §8 — THE INSTRUMENT'S SHARPEST VERDICT IS REACHABLE (so the instrument is not itself vacuous).

Everything above is conditional on a premise. This section discharges the obvious objection — that
`Empties` might be an empty notion, or that `not_of_empties_of_acceptsSome` might have an
unsatisfiable hypothesis — by firing the sharp verdict at verifier arguments where the deployed
predicate PROVABLY accepts a run (`FriLdtExtractDeployed.deployed_accepting_pole_nonempty`, a
`decide` witness on the complete apex-facing predicate). At those arguments a singleton-forcing
premise is not merely vacuous: it is FALSE. -/

/-- The deployed predicate at FIXED verifier arguments, indexed by the proof / carried publics /
extension view triple. (`deployedAcc` above is the `ProofView`-mediated form the bundles use; this
is the same predicate with the run data taken directly, so a concrete pole can index it.) -/
def rawDeployedAcc {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (core : FriCore F) (A : FieldArith F)
    (extCore : ExtFriCore F) (extA : ExtFriArith F) (W : F)
    (initState : List F) (logN : Nat) :
    Acc (BatchProofData F × WrapPublics F × ExtVerifierView F) :=
  ofBool fun r =>
    verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core A extCore extA W initState logN
      r.1 r.2.1 r.2.2

theorem rawDeployedAcc_refutes_singleton {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (core : FriCore F) (A : FieldArith F)
    (extCore : ExtFriCore F) (extA : ExtFriArith F) (W : F)
    (initState : List F) (logN : Nat) :
    ∀ r, rawDeployedAcc perm RATE toNat params vk core A extCore extA W initState logN r →
      ∀ ood : F, r.1.oodPoint ≠ [ood] := by
  intro r hr ood
  exact faithfulExt_forces_oodPoint_ne_singleton perm RATE toNat params vk core A extCore extA W
    initState logN r.1 r.2.1 r.2.2 hr ood

/-- **The pole, as an `AcceptsSome`.** -/
theorem rawDeployedAcc_acceptsSome :
    ∃ (perm : List Nat → List Nat) (RATE : Nat) (toNat : Nat → Nat) (params : FriParams)
      (vk : RecursionVk Nat) (core : FriCore Nat) (A : FieldArith Nat)
      (extCore : ExtFriCore Nat) (extA : ExtFriArith Nat) (W : Nat)
      (initState : List Nat) (logN : Nat),
      AcceptsSome
        (rawDeployedAcc perm RATE toNat params vk core A extCore extA W initState logN) := by
  obtain ⟨perm, RATE, toNat, params, vk, core, A, extCore, extA, W, initState, logN, proof, pub,
    view, hacc⟩ := deployed_accepting_pole_nonempty
  exact ⟨perm, RATE, toNat, params, vk, core, A, extCore, extA, W, initState, logN,
    ⟨(proof, pub, view), hacc⟩⟩

/-- **THE SHARP VERDICT, FIRED ON A REAL POLE.** At verifier arguments where the deployed
extension-faithful predicate demonstrably accepts a run, EVERY premise that forces the singleton
OOD shape on that predicate is FALSE — not vacuously true, not merely uninformative. This is the
instrument at full strength, and it exhibits that `Empties`, `YieldsShape` and
`not_of_empties_of_acceptsSome` all have satisfiable hypotheses. -/
theorem singleton_forcing_premise_is_false_at_a_real_pole :
    ∃ (perm : List Nat → List Nat) (RATE : Nat) (toNat : Nat → Nat) (params : FriParams)
      (vk : RecursionVk Nat) (core : FriCore Nat) (A : FieldArith Nat)
      (extCore : ExtFriCore Nat) (extA : ExtFriArith Nat) (W : Nat)
      (initState : List Nat) (logN : Nat),
      ∀ P : Prop,
        YieldsShape P
            (rawDeployedAcc perm RATE toNat params vk core A extCore extA W initState logN)
            (fun r => r.1.oodPoint) (fun ood : Nat => [ood]) →
          ¬ P := by
  obtain ⟨perm, RATE, toNat, params, vk, core, A, extCore, extA, W, initState, logN, hsome⟩ :=
    rawDeployedAcc_acceptsSome
  refine ⟨perm, RATE, toNat, params, vk, core, A, extCore, extA, W, initState, logN, ?_⟩
  intro P hy
  exact not_of_empties_of_acceptsSome
    (empties_of_yieldsShape hy (fun _ hi => hi)
      (rawDeployedAcc_refutes_singleton perm RATE toNat params vk core A extCore extA W initState
        logN))
    hsome

#assert_axioms not_rejectsAll_of_acceptsSome
#assert_axioms rejectsAll_ofBool_iff
#assert_axioms empties_of_refuted
#assert_axioms empties_strong_of_extracts_weak
#assert_axioms empties_proves_anything
#assert_axioms not_of_empties_of_acceptsSome
#assert_axioms empties_mono
#assert_axioms empties_of_imp
#assert_axioms not_empties_of_realizable
#assert_axioms empties_of_yieldsShape
#assert_axioms extractsWith_iff_extracts
#assert_axioms extractsWith_empties_iff
#assert_axioms supplied_never_refuted
#assert_axioms deployedAcc_imp_bareAcc
#assert_axioms deployedAcc_refutes_singleton
#assert_axioms verifyBatch_reject_of_empties_cfg
#assert_axioms friLdtExtractV3_yieldsShape
#assert_axioms friLdtExtractV3_empties_deployed
#assert_axioms friLdtExtract_yieldsShape
#assert_axioms friLdtExtract_empties_deployed
#assert_axioms friLdtExtract_makes_verifyBatch_reject_everything
#assert_axioms extractBundleSansFS_yieldsShape
#assert_axioms extractBundleSansFS_empties_deployed
#assert_axioms extractBundleSansFS_makes_verifyBatch_reject_everything
#assert_axioms deployedAccClose_imp_bareAccClose
#assert_axioms deployedAccClose_refutes_singleton
#assert_axioms decodedLdtLink_yieldsShape
#assert_axioms decodedLdtLink_empties_deployedClose
#assert_axioms decodedLdtLink_forbids_close_on_accepting
#assert_axioms decodedLdtLinkExt_yieldsShape
#assert_axioms decodedLdtLinkExt_empties_deployedClose
#assert_axioms consShape_suppliedByAcceptance
#assert_axioms consShape_adds_no_strength
#assert_axioms consShape_never_refuted
#assert_axioms rawDeployedAcc_refutes_singleton
#assert_axioms rawDeployedAcc_acceptsSome
#assert_axioms singleton_forcing_premise_is_false_at_a_real_pole

end Dregg2.Circuit.PremiseInhabitability
