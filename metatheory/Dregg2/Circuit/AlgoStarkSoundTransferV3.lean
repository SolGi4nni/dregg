/-
# `Dregg2.Circuit.AlgoStarkSoundTransferV3` — the REAL `AlgoStarkSound` for `transferV3`,
with `hood`/`hnonexc` DISCHARGED, resting on ONLY `{Poseidon2SpongeCR, FRI-LDT@deployed}`.

## What this closes (the one-line honest claim)

`AlgoStarkSoundInstance.algoStarkSound_of_bricks_transferV3` assembled a real `AlgoStarkSound` for the
deployed `transferV3` slice, but took `MainAirAcceptF transferV3 t` (the FRI-proximity-onto-the-deployed
AIR) as an OPAQUE `hextract` premise. This module WIRES the four proven reductions so that
`MainAirAcceptF` is no longer assumed — it is DERIVED, per accepting run, from:

  * `verifyAlgo_accept_forces_table_identity`  (acceptance ⟹ the BATCHED OOD identity
        `topen.constraintEval = A.mul topen.vanishingAtZeta topen.quotientAtZeta`), a THEOREM;
  * `OodCommitmentBinding.commitmentOpening_binds_of_poseidon2CR`  (the opened `constraintEval` BINDS to
        the committed value, under the named `Poseidon2SpongeCR` floor) — `hood.b`, DERIVED;
  * the transferV3 COLUMN-LAYOUT law `hlayout` (§1) — the modeled map from the verifier's single batched
        opening onto `batchResidual` over `transferV3`'s ACTUAL per-arith-constraint residual family
        (`arithList transferV3 = transferV3.constraints.filter isArithB`), carrying the BabyBear→ℤ field bridge;
  * `OodSoundnessGame.rlc_debatch`  (the batched residual vanishing at a NON-exceptional Λ ⟹ every
        per-constraint residual is `0`) — `hood.a` RLC de-batch, a THEOREM (Schwartz–Zippel);
  * `FieldIntegerLift.ood_forces_mainAirAccept_field_of_residuals`  (`hood` + `hnonexc` ⟹
        `MainAirAcceptF`), a THEOREM (`hZrow`/`hCrow` already discharged in-tree).

`hnonexc` (Fiat–Shamir non-exceptionality of ζ) and the RLC challenge Λ's non-exceptionality are carried
as EXPLICIT FS-soundness hypotheses in the deployed-extraction bundle `FriLdtExtractV3` — the HONEST
form, since the escape is real and cannot be unconditional. Their honest bounded-advantage character is
exhibited by `OodSoundnessGame.ood_hnonexc_escape_prob_le` / `batchResidual_exceptionalSet_card_lt`
(ε ≤ deg/|F|), quoted in §4 as `hnonexc_is_bounded_fs_form` / `rlc_lambda_is_bounded_fs_form`.

## The residual floor (exactly two, both honest)

`algoStarkSound_transferV3` (§3) rests on:
  1. `Poseidon2SpongeCR sponge`  — the Merkle/commitment-opening hash floor (`hood.b`), GENUINELY USED
     (not re-assumed): `commitmentOpening_binds_of_poseidon2CR` is invoked on the bundle's recompute data.
  2. `FriLdtExtractV3 …`  — the FRI-LDT-@-deployed extraction bundle: FRI delivers, per accepting run, the
     opened deployed `VmTrace t`, the OOD point ζ, the per-constraint quotients `qp`, the RLC challenge Λ,
     the opened table `topen` with its Merkle recompute data, the transferV3 COLUMN-LAYOUT equation, the
     FS non-exceptionality of ζ and Λ (the honest ε-form), and the aux legs (LogUp `hbus`, the two
     aux-table-emptiness facts, the published-commit link). It contains NEITHER `hood` NOR
     `MainAirAcceptF` — those are DERIVED here from the primitives above.

## Discipline

Sorry-free; no `def …Sound` carrier; `Poseidon2SpongeCR` is a `Prop` hypothesis where used, never an
`axiom`. The transferV3 column layout is MODELED, not left vague: `arithList transferV3` is the descriptor's
actual arith-constraint list and `Rfam transferV3` its concrete per-constraint residual family feeding
`batchResidual`. New file; imports read-only; builds targeted
(`lake build Dregg2.Circuit.AlgoStarkSoundTransferV3`).
-/
import Dregg2.Circuit.AlgoStarkSoundInstance
import Dregg2.Circuit.OodSoundnessGame
import Dregg2.Circuit.OodCommitmentBinding

namespace Dregg2.Circuit.AlgoStarkSoundTransferV3

open Polynomial
open Dregg2.Circuit.FriVerifierBridge (AlgoStarkSound ProofView)
open Dregg2.Circuit.FriVerifier
  (verifyAlgo BatchProofData WrapPublics FriParams RecursionVk FriChecks FriCore FieldArith
   TableOpening fullChecks)
open Dregg2.Circuit.CircuitSoundness
  (BatchPublicInputs BatchProof tracePublishedCommit)
open Dregg2.Circuit.DescriptorIR2 (VmTrace EffectVmDescriptor2 envAt VmConstraint2)
open Dregg2.Circuit.AirChecksSatisfied (MainAirAcceptF isArith)
open Dregg2.Circuit.RotatedKernelRefinement (transferV3)
open Dregg2.Circuit.TraceColumnInterp (constraintPoly domainSize)
open Dregg2.Circuit.FieldIntegerLift (vanishingPoly ood_forces_mainAirAccept_field_of_residuals)
open Dregg2.Circuit.OodQuotientConsistency (exceptionalSet verifyAlgo_accept_forces_table_identity)
open Dregg2.Crypto.ProbCrypto (winProb)
open Dregg2.Circuit.OodSoundnessGame
  (batchResidual rlc_debatch batchResidual_exceptionalSet_card_lt oodNonExcAcc
   oodNonExc_soundness_error_babybear ood_hnonexc_escape_prob_le)
open Dregg2.Circuit.OodCommitmentBinding (merkleRecomputeZ commitmentOpening_binds_of_poseidon2CR)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.BabyBearFriField (BabyBear)

/-! ## §1 — THE transferV3 COLUMN LAYOUT: the descriptor's ACTUAL arith-constraint list feeding
`batchResidual`.

`verifyAlgo` folds every declared constraint into ONE `TableOpening.constraintEval` per table via the
Fiat–Shamir RLC challenge Λ. `MainAirAcceptF` wants the identity PER constraint. The layout that ties
them is: the batched residual is the random-linear-combination `Σ_c Λ^c · R_c` of the PER-arith-constraint
residuals `R_c := constraintPoly(ζ) − vanishingPoly(ζ)·qp_c(ζ)`. This section EXHIBITS the actual list. -/

/-- The Boolean mirror of `isArith` (so `List.filter` — which takes `α → Bool` — can select the arithmetic
constraints). `isArithB c = true ↔ isArith c` (`isArithB_iff`). -/
def isArithB : VmConstraint2 → Bool
  | .base _       => true
  | .windowGate _ => true
  | .lookup _     => false
  | .memOp _      => false
  | .mapOp _      => false
  | .umemOp _     => false
  | .proofBind _  => false

theorem isArithB_iff (c : VmConstraint2) : isArithB c = true ↔ isArith c := by
  cases c <;> simp [isArithB, isArith]

/-- **THE arith-constraint layout — the ACTUAL list feeding `batchResidual`, per descriptor.** Exactly the
arithmetic (main-table) constraints of a descriptor `d`; the interaction-bus arms are excluded (their
residual is the separate LogUp AIR). This is `d.constraints.filter isArithB` by definition — not an
abstract stand-in. For `transferV3` it is `arithList transferV3` (used by the instance below).

The `d`-parametricity is the automation punchline (see `docs/reference/STARK-COMPLETION-AUTOMATION.md`):
the whole derivation core below is descriptor-POLYMORPHIC; only the final assembler is per-effect. -/
def arithList (d : EffectVmDescriptor2) : List VmConstraint2 := d.constraints.filter isArithB

/-- `arithList d` IS the actual filtered constraint list of `d` (definitional). -/
theorem arithList_eq (d : EffectVmDescriptor2) : arithList d = d.constraints.filter isArithB := rfl

/-- **`Rfam` — a descriptor's PER-CONSTRAINT residual family**, indexed by its arith-constraint layout.
`Rfam d t ζ qp j = constraintPoly(ζ) − vanishingPoly(ζ)·qp_c(ζ)` for the `j`-th arith constraint. This is
the `R : Fin n → BabyBear` that `batchResidual` weights by `Λ^j` and `rlc_debatch` de-batches. -/
noncomputable def Rfam (d : EffectVmDescriptor2) (t : VmTrace) (ζ : BabyBear)
    (qp : VmConstraint2 → Polynomial BabyBear) : Fin (arithList d).length → BabyBear :=
  fun j => (constraintPoly d t ((arithList d).get j)).eval ζ
             - (vanishingPoly t).eval ζ * (qp ((arithList d).get j)).eval ζ

/-! ## §2 — THE DEPLOYED-EXTRACTION BUNDLE `FriLdtExtractV3` (the FRI-LDT@deployed floor).

Everything FRI delivers on an accepting run, stated over the deployed objects — but WITHOUT `hood` and
WITHOUT `MainAirAcceptF` (those are derived in §3). -/

/-- **`FriLdtExtractV3`** — the FRI-LDT-@-deployed extraction hypothesis for the `transferV3` slice.
For every batch the specified `verifyAlgo` (at `fullChecks core A …`) accepts, FRI opens a deployed
`VmTrace t`, an OOD point ζ, per-constraint quotients `qp`, the RLC challenge Λ, and the batched table
opening `topen`, together with: the Merkle recompute data binding `topen.constraintEval` and the committed
value `vCommitted` to a common root (feeds `Poseidon2SpongeCR`), the transferV3 COLUMN-LAYOUT equation
(feeds `rlc_debatch`, carries the BabyBear→ℤ bridge), the FS non-exceptionality of Λ and ζ (the honest
ε-form), and the aux legs. Contains NO `hood`/`MainAirAcceptF`. -/
def FriLdtExtractV3
    (sponge : List ℤ → ℤ) (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView) : Prop :=
  ∀ (pi : BatchPublicInputs) (π : BatchProof),
    verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
        initState logN (view pi π).1 (view pi π).2 = true →
    ∃ (t : VmTrace) (ζ Λ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)
      (topen : TableOpening ℤ) (ood vCommitted root : ℤ) (idx : Nat) (siblings : List ℤ),
      -- FRI geometry / opening structure:
      t.rows.length ≤ domainSize ∧
      (view pi π).1.oodPoint = [ood] ∧
      topen ∈ (view pi π).1.tableOpenings ∧
      -- commitment recompute data (proof structure; feeds the `Poseidon2SpongeCR` binding):
      merkleRecomputeZ sponge idx vCommitted siblings = root ∧
      merkleRecomputeZ sponge idx topen.constraintEval siblings = root ∧
      -- THE transferV3 COLUMN-LAYOUT law (+ BabyBear→ℤ bridge): the batched residual polynomial's value
      -- at Λ IS the cast difference between the committed batched constraint eval and the batched
      -- vanishing·quotient — the RLC of the per-arith-constraint residuals `Rfam transferV3`:
      (batchResidual (Rfam transferV3 t ζ qp)).eval Λ
        = ((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear) ∧
      -- FS non-exceptionality of the RLC challenge Λ (the honest ε-form; `rlc_debatch`'s precondition):
      Λ ∉ exceptionalSet (batchResidual (Rfam transferV3 t ζ qp)) ∧
      -- FS non-exceptionality of the OOD point ζ, per arith constraint (the honest ε-form of `hnonexc`):
      (∀ c ∈ transferV3.constraints, isArith c →
          ζ ∉ exceptionalSet (constraintPoly transferV3 t c - vanishingPoly t * qp c)) ∧
      -- aux legs (verbatim the `algoStarkSound_of_bricks_transferV3` non-`MainAirAccept` premises):
      (∀ i < t.rows.length, ∀ c ∈ transferV3.constraints, ¬ isArith c →
          c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)) ∧
      t.tf .memory = [] ∧ t.tf .mapOps = [] ∧
      tracePublishedCommit t = pi.toPublished

/-! ## §3 — THE WIRING: `MainAirAcceptF` DERIVED, then the real `AlgoStarkSound` instance. -/

/-- **`hood`, DISCHARGED.** From the batched table identity (`verifyAlgo_accept_forces_table_identity`),
the commitment binding (`commitmentOpening_binds_of_poseidon2CR`, under `Poseidon2SpongeCR`), the
transferV3 column layout `hlayout`, and RLC de-batch (`rlc_debatch`, at the non-exceptional Λ), the
per-constraint OOD identity holds for every arithmetic constraint of `transferV3`. This is `hood` DERIVED
— not re-assumed — from `{table-identity, Poseidon2SpongeCR, column-layout, Schwartz–Zippel}`. -/
theorem hood_of_reductions
    (d : EffectVmDescriptor2)
    (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
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
    (hlayout : (batchResidual (Rfam d t ζ qp)).eval Λ
        = ((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear))
    (hLam : Λ ∉ exceptionalSet (batchResidual (Rfam d t ζ qp))) :
    ∀ c ∈ d.constraints, isArith c →
      (constraintPoly d t c).eval ζ = (vanishingPoly t).eval ζ * (qp c).eval ζ := by
  -- (1) acceptance forces the batched OOD identity (THEOREM):
  have htable : topen.constraintEval = A.mul topen.vanishingAtZeta topen.quotientAtZeta :=
    verifyAlgo_accept_forces_table_identity perm RATE toNat params vk core A initState logN
      proof pub ood hoodPt topen hmem hacc
  -- (2) the opened value BINDS to the committed value (THEOREM, under Poseidon2SpongeCR) — hood.b:
  have hbind : topen.constraintEval = vCommitted :=
    commitmentOpening_binds_of_poseidon2CR sponge hCR hCommitted hOpened
  -- so `vCommitted = A.mul …`, hence the layout RHS casts to 0:
  have hvc : vCommitted = A.mul topen.vanishingAtZeta topen.quotientAtZeta := hbind.symm.trans htable
  have heval : (batchResidual (Rfam d t ζ qp)).eval Λ = 0 := by
    rw [hlayout, hvc]; exact sub_self _
  -- (3) RLC de-batch at the non-exceptional Λ forces every per-constraint residual to 0 (THEOREM) — hood.a:
  have hRzero : ∀ j, Rfam d t ζ qp j = 0 := rlc_debatch (Rfam d t ζ qp) Λ heval hLam
  -- (4) read off the per-constraint identity for every arithmetic constraint of `d`:
  intro c hc harith
  have hcf : c ∈ arithList d := List.mem_filter.mpr ⟨hc, (isArithB_iff c).mpr harith⟩
  obtain ⟨i, hlt, hget⟩ := List.mem_iff_getElem.mp hcf
  have hj0 : Rfam d t ζ qp ⟨i, hlt⟩ = 0 := hRzero ⟨i, hlt⟩
  simp only [Rfam, List.get_eq_getElem, hget] at hj0
  exact sub_eq_zero.mp hj0

/-- **`mainAirAcceptF_of_floor`** — `MainAirAcceptF d t` for ANY descriptor `d`, from the honest floor.
`hood` is DERIVED by `hood_of_reductions`; `hnonexc` is the carried FS non-exceptionality; the domain
axis `hZrow`/interpolation `hCrow` are the in-tree-discharged `vanishingPoly`/`constraintPoly` facts. This
theorem is descriptor-POLYMORPHIC — the entire crypto composition recurs identically for every effect;
the transferV3 instance below is just its specialization at `d := transferV3`. -/
theorem mainAirAcceptF_of_floor
    (d : EffectVmDescriptor2)
    (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat)
    (proof : BatchProofData ℤ) (pub : WrapPublics ℤ)
    (hacc : verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
        initState logN proof pub = true)
    (t : VmTrace) (ζ Λ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)
    (topen : TableOpening ℤ) (ood vCommitted root : ℤ) (idx : Nat) (siblings : List ℤ)
    (hcap : t.rows.length ≤ domainSize)
    (hoodPt : proof.oodPoint = [ood])
    (hmem : topen ∈ proof.tableOpenings)
    (hCommitted : merkleRecomputeZ sponge idx vCommitted siblings = root)
    (hOpened : merkleRecomputeZ sponge idx topen.constraintEval siblings = root)
    (hlayout : (batchResidual (Rfam d t ζ qp)).eval Λ
        = ((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear))
    (hLam : Λ ∉ exceptionalSet (batchResidual (Rfam d t ζ qp)))
    (hnonexc : ∀ c ∈ d.constraints, isArith c →
        ζ ∉ exceptionalSet (constraintPoly d t c - vanishingPoly t * qp c)) :
    MainAirAcceptF d t :=
  ood_forces_mainAirAccept_field_of_residuals d t hcap ζ qp
    (hood_of_reductions d sponge hCR perm RATE toNat params vk core A initState logN proof pub hacc
      t ζ Λ qp topen ood vCommitted root idx siblings hoodPt hmem hCommitted hOpened hlayout hLam)
    hnonexc

/-- **`algoStarkSound_transferV3` — the REAL `AlgoStarkSound` for the deployed `transferV3` slice, with
`hood`/`hnonexc` DISCHARGED, resting on ONLY `{Poseidon2SpongeCR, FRI-LDT@deployed}`.**

From the two honest floor hypotheses — `Poseidon2SpongeCR sponge` (genuinely used in the commitment
binding) and `FriLdtExtractV3` (the FRI-LDT-@-deployed extraction bundle, containing neither `hood` nor
`MainAirAcceptF`) — the full `AlgoStarkSound` class holds. Per accepting run,
`mainAirAcceptF_of_floor` DERIVES `MainAirAcceptF` from the bundle's primitives (table
identity + commitment binding + column layout + RLC de-batch), and the aux legs come straight from the
bundle; `algoStarkSound_of_bricks_transferV3` then closes the class. -/
theorem algoStarkSound_transferV3
    (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (hfri : FriLdtExtractV3 sponge hash perm RATE toNat params vk core A initState logN view) :
    AlgoStarkSound hash (fun _ => transferV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  Dregg2.Circuit.AlgoStarkSoundInstance.algoStarkSound_of_bricks_transferV3
    hash perm RATE toNat params vk (fullChecks core A toNat params.powBits) initState logN view
    (by
      intro pi π hacc
      obtain ⟨t, ζ, Λ, qp, topen, ood, vCommitted, root, idx, siblings,
        hcap, hoodPt, hmem, hCommitted, hOpened, hlayout, hLam, hnonexc,
        hbus, hMem, hMap, hPub⟩ := hfri pi π hacc
      exact ⟨t,
        mainAirAcceptF_of_floor transferV3 sponge hCR perm RATE toNat params vk core A initState logN
          (view pi π).1 (view pi π).2 hacc t ζ Λ qp topen ood vCommitted root idx siblings
          hcap hoodPt hmem hCommitted hOpened hlayout hLam hnonexc,
        hbus, hMem, hMap, hPub⟩)

/-! ## §4 — the FS residuals are the HONEST bounded-advantage form (ε ≤ deg/|F|), not free assumptions.

`hnonexc` (ζ) and Λ's non-exceptionality are carried in the bundle because the escape is REAL — but they
are the honest Fiat–Shamir ε-form: the probability a uniform challenge violates them is `≤ deg/|F|`, a
CONCRETE Schwartz–Zippel soundness error, quoted here from the OOD-game lane. -/

/-- The OOD `hnonexc` escape probability is `≤ deg(residual) / 2013265921` — the honest bounded-advantage
form of the carried ζ-non-exceptionality (`OodSoundnessGame.ood_hnonexc_escape_prob_le`). -/
theorem hnonexc_is_bounded_fs_form (t : VmTrace) (qp : VmConstraint2 → Polynomial BabyBear)
    (c : VmConstraint2) :
    winProb (oodNonExcAcc (constraintPoly transferV3 t c - vanishingPoly t * qp c))
      ≤ ((constraintPoly transferV3 t c - vanishingPoly t * qp c).natDegree : ℝ) / 2013265921 :=
  ood_hnonexc_escape_prob_le transferV3 t qp c

/-- The RLC challenge Λ's bad set (where `rlc_debatch`'s non-exceptionality fails) has fewer than
`#(arithList transferV3)` elements — so a uniform Λ misses it except with the honest ε_RLC ≤ (n−1)/|F|. Requires the
transferV3 arith layout to be nonempty. -/
theorem rlc_lambda_is_bounded_fs_form (t : VmTrace) (ζ : BabyBear)
    (qp : VmConstraint2 → Polynomial BabyBear) (hn : 0 < (arithList transferV3).length) :
    (exceptionalSet (batchResidual (Rfam transferV3 t ζ qp))).card < (arithList transferV3).length :=
  batchResidual_exceptionalSet_card_lt hn (Rfam transferV3 t ζ qp)

#assert_axioms isArithB_iff
#assert_axioms hood_of_reductions
#assert_axioms mainAirAcceptF_of_floor
#assert_axioms algoStarkSound_transferV3
#assert_axioms hnonexc_is_bounded_fs_form
#assert_axioms rlc_lambda_is_bounded_fs_form

end Dregg2.Circuit.AlgoStarkSoundTransferV3
