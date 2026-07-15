/-
# Market.AggregateBinding — aggregate binding as a proof-carrying MSIS obligation

**codex fhEgg Round-3 Q1, the linked `(ct, C, Π)` carrier.** Each order carries a BDLOP-family
*additive* lattice commitment `C_i = Com(m_i; r_i)` whose BINDING is Module-SIS. The batch
AGGREGATES commitments by native ring addition: `C_agg = Σ C_i`. codex's sharp point, honored
exactly here: the SIS witness extracted from a binding break is

        A·(r − r') + G·(m − m') = 0

— it **includes the message difference `m − m'`** — so the Module-SIS instance must be sized to the
**accepted-aggregate opening radius**, not to a single order. A forgotten radius bound is a break.

## What this file is (honest scope)

The first section records only the generic additive algebra.  The security floor below it is no
longer scalar: it uses the repository's genuine ML-DSA-65 negacyclic ring and module dimensions,
the existing Hermine product norm and augmented map, and the existing adversary-indexed
`ProbCrypto.MSISHardQuant` floor.  A finite parameter distribution samples `(A,G,β)` for each security
parameter; a resource model identifies uniform efficient adversaries and proves that subtraction
preserves efficiency.  The concrete production sampler and its parameter estimate remain explicit
crypto-build inputs, not theorems manufactured here.

## Proven vs assumed

  * PROVEN (pure algebra): `collision_yields_msis_witness` — two distinct openings of one commitment
    yield the message-difference-carrying kernel witness, nonzero.
  * PROVEN (reduction): `BDLOP.binding_break_yields_msis_solution` and
    `BDLOP.aggregate_binding_of_MSISHard` — a binding win becomes a real Module-SIS win with no loss in
    success probability, hence quantitative Module-SIS hardness implies aggregate binding.
  * CARRIED: the concrete parameter sampler/resource bound and its `BDLOP.MSISHard` estimate.  Hardness
    enters only as a theorem hypothesis; it is neither an axiom nor the false existence-refutation
    `Lattice.MSISHard`.
-/
import Market.MintSafeQuantization
import Dregg2.Crypto.Fips204CorrectReal
import Dregg2.Crypto.HermineSelfTargetMSIS
import Dregg2.Crypto.ProbCrypto
import Dregg2.Tactics
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Tactic.LinearCombination

namespace Market

universe u

variable {R : Type u} [CommRing R]

/-- The abstract additive/linear commitment shape: `Com A G r m = A·r + G·m`.

This generic lemma is retained for downstream additive algebra only; the security theorem below uses
the real ring/module construction rather than treating these scalars as a hardness instance. -/
def Com (A G r m : R) : R := A * r + G * m

@[simp] theorem Com_def (A G r m : R) : Com A G r m = A * r + G * m := rfl

/-- Native ring addition of two commitments is the commitment of the summed openings — the batch
`C_agg = Σ C_i` is honest precisely because `Com` is linear. -/
theorem Com_add (A G r₁ m₁ r₂ m₂ : R) :
    Com A G r₁ m₁ + Com A G r₂ m₂ = Com A G (r₁ + r₂) (m₁ + m₂) := by
  simp only [Com]; ring

/-- **The crux (PROVEN, pure algebra).** Two DISTINCT openings `(r, m) ≠ (r', m')` of the SAME
commitment `Com A G r m = Com A G r' m'` yield the Module-SIS witness

        A·(r − r') + G·(m − m') = 0

with `(r − r', m − m')` nonzero. The witness **carries the message difference `m − m'`** — codex's
sharp point: the radius that sizes MSIS must bound this whole pair, not just `r − r'`. -/
theorem collision_yields_msis_witness (A G r m r' m' : R)
    (hne : (r, m) ≠ (r', m'))
    (hcol : Com A G r m = Com A G r' m') :
    A * (r - r') + G * (m - m') = 0 ∧ (r - r' ≠ 0 ∨ m - m' ≠ 0) := by
  refine ⟨?_, ?_⟩
  · -- the kernel equation, by linearity of `Com`
    simp only [Com] at hcol
    linear_combination hcol
  · -- nonzero: else both differences vanish and the openings coincide, contradicting `hne`
    by_contra h
    simp only [not_or, not_not] at h
    obtain ⟨h1, h2⟩ := h
    exact hne (Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h2))

/-- **A proof-carrying aggregate opening.** The radius bound `radius : IsShort r m` is a REQUIRED
field: an `AggregateOpening` that never established its shortness/radius bound cannot be formed — a
forgotten radius is a *type error*, exactly codex's discipline. `opens` ties `(r, m)` to `C`. -/
structure AggregateOpening (A G : R) (IsShort : R → R → Prop) where
  /-- aggregate randomness `Σ rᵢ`. -/
  r : R
  /-- aggregate message `Σ mᵢ`. -/
  m : R
  /-- aggregate commitment `C_agg = Σ Cᵢ`. -/
  C : R
  /-- the opening relation `Com A G r m = C`. -/
  opens : Com A G r m = C
  /-- **REQUIRED radius field** — the aggregate opening's shortness bound, sized (per codex) to the
  whole `(r, m)` pair including the message. Omitting it makes the structure unconstructable. -/
  radius : IsShort r m

/-- **Aggregation by native ring addition.** Two aggregate openings combine into one whose randomness,
message, and commitment are the componentwise sums (`C_agg = Σ Cᵢ`). The combined radius bound
`hradius` must be SUPPLIED — you cannot mint the aggregate opening without proving its aggregate
radius. This is where a forgotten radius bound would be caught. -/
def AggregateOpening.combine (A G : R) (IsShort : R → R → Prop)
    (o₁ o₂ : AggregateOpening A G IsShort)
    (hradius : IsShort (o₁.r + o₂.r) (o₁.m + o₂.m)) :
    AggregateOpening A G IsShort where
  r := o₁.r + o₂.r
  m := o₁.m + o₂.m
  C := o₁.C + o₂.C
  opens := by
    have e := Com_add A G o₁.r o₁.m o₂.r o₂.m
    rw [o₁.opens, o₂.opens] at e
    exact e.symm
  radius := hradius

@[simp] theorem combine_r (A G : R) (IsShort : R → R → Prop)
    (o₁ o₂ : AggregateOpening A G IsShort) (h : IsShort (o₁.r + o₂.r) (o₁.m + o₂.m)) :
    (AggregateOpening.combine A G IsShort o₁ o₂ h).r = o₁.r + o₂.r := rfl

@[simp] theorem combine_m (A G : R) (IsShort : R → R → Prop)
    (o₁ o₂ : AggregateOpening A G IsShort) (h : IsShort (o₁.r + o₂.r) (o₁.m + o₂.m)) :
    (AggregateOpening.combine A G IsShort o₁ o₂ h).m = o₁.m + o₂.m := rfl

@[simp] theorem combine_C (A G : R) (IsShort : R → R → Prop)
    (o₁ o₂ : AggregateOpening A G IsShort) (h : IsShort (o₁.r + o₂.r) (o₁.m + o₂.m)) :
    (AggregateOpening.combine A G IsShort o₁ o₂ h).C = o₁.C + o₂.C := rfl

/-- The combined opening's radius field IS the aggregate radius that was supplied — the required
field is genuinely the aggregate bound, not a per-order one. -/
theorem combine_radius_is_aggregate (A G : R) (IsShort : R → R → Prop)
    (o₁ o₂ : AggregateOpening A G IsShort) (h : IsShort (o₁.r + o₂.r) (o₁.m + o₂.m)) :
    IsShort (AggregateOpening.combine A G IsShort o₁ o₂ h).r
            (AggregateOpening.combine A G IsShort o₁ o₂ h).m := by
  simpa using h

/-! ## The real BDLOP/Module-SIS floor

The scalar `[A | G] : R² → R` model ends here.  The construction below reuses the exact
`HermineSelfTargetMSIS.augmented` map and `Lattice.IsMSISSolution` relation over ML-DSA-65's genuine
negacyclic ring `R_q = Z_q[X]/(X^256+1)`.  Binding is computational: every resource-bounded binding
adversary has negligible advantage under the existing adversary-indexed `ProbCrypto.MSISHardQuant`
floor.  No second Module-SIS definition is introduced.
-/

namespace BDLOP

set_option maxRecDepth 20000

open Dregg2.Crypto.Lattice
open Dregg2.Crypto.ConcreteSecurity
open Dregg2.Crypto.ProbCrypto
open Dregg2.Crypto.HermineSelfTargetMSIS
open Dregg2.Crypto.Fips204CorrectReal
open Filter
open scoped BigOperators
open scoped Dregg2.Crypto.HermineSelfTargetMSIS

/-- The genuine ML-DSA-65 negacyclic ring, reused rather than redefined. -/
abbrev Rq := Dregg2.Crypto.Fips204CorrectReal.Rq

/-- BDLOP randomness module `R_q^5` (the real ML-DSA-65 source-module dimension). -/
abbrev Randomness := Dregg2.Crypto.Fips204CorrectReal.M

/-- BDLOP commitment module `R_q^6` (the real ML-DSA-65 target-module dimension). -/
abbrev Commitment := Dregg2.Crypto.Fips204CorrectReal.N

/-- The complete Module-SIS witness `(dr, dm)`; the message difference is a real ring coordinate. -/
abbrev Witness := Randomness × Rq

/-- Coefficient `ℓ₁` short norm on the real quotient ring, using centered `ZMod q` representatives. -/
noncomputable def coeffL1 (x : Rq) : Nat :=
  ∑ j : Fin pb.dim, (pb.basis.repr x j).valMinAbs.natAbs

/-- The centered coefficient norm is a `Hermine` `ShortNorm`: zero and negation laws plus the triangle
inequality all hold in the quotient ring. -/
noncomputable instance instShortNormRq : ShortNorm Rq where
  nrm := coeffL1
  nrm_zero := by simp [coeffL1, ZMod.valMinAbs_zero]
  nrm_neg x := by
    simp only [coeffL1, map_neg, Finsupp.neg_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact ZMod.natAbs_valMinAbs_neg _
  nrm_add_le x y := by
    simp only [coeffL1, map_add, Finsupp.add_apply]
    calc
      (∑ j : Fin pb.dim, ((pb.basis.repr x j) + (pb.basis.repr y j)).valMinAbs.natAbs)
          ≤ ∑ j : Fin pb.dim,
              ((pb.basis.repr x j).valMinAbs + (pb.basis.repr y j).valMinAbs).natAbs :=
        Finset.sum_le_sum fun j _ => ZMod.natAbs_valMinAbs_add_le _ _
      _ ≤ ∑ j : Fin pb.dim,
              ((pb.basis.repr x j).valMinAbs.natAbs +
                (pb.basis.repr y j).valMinAbs.natAbs) :=
        Finset.sum_le_sum fun j _ => Int.natAbs_add_le _ _
      _ = (∑ j : Fin pb.dim, (pb.basis.repr x j).valMinAbs.natAbs) +
            ∑ j : Fin pb.dim, (pb.basis.repr y j).valMinAbs.natAbs :=
        Finset.sum_add_distrib

/-- Coordinate-sum norm on `R_q^5`, matching Hermine's product/sum norm discipline. -/
noncomputable instance instShortNormRandomness : ShortNorm Randomness where
  nrm r := ∑ i, nrm (r i)
  nrm_zero := by simp [nrm_zero]
  nrm_neg r := by simp [nrm_neg]
  nrm_add_le r s := by
    calc
      (∑ i, nrm ((r + s) i)) = ∑ i, nrm (r i + s i) := rfl
      _ ≤ ∑ i, (nrm (r i) + nrm (s i)) :=
        Finset.sum_le_sum fun i _ => nrm_add_le _ _
      _ = (∑ i, nrm (r i)) + ∑ i, nrm (s i) := Finset.sum_add_distrib

/-- Reuse Hermine SelfTargetMSIS's coordinate-sum product norm for `(dr,dm)`. -/
noncomputable instance instShortNormWitness : ShortNorm Witness :=
  Dregg2.Crypto.HermineSelfTargetMSIS.instShortNormProd

/-- Public BDLOP parameters. `A` is the sampled `6×5` ring matrix, `G` the public message/gadget
column, and `beta` the accepted aggregate opening-difference radius.  The concrete sampler and its
parameter-security estimate remain the ordinary cryptographic build assumption. -/
structure PublicParameters where
  A : Randomness →ₗ[Rq] Commitment
  G : Commitment
  beta : Nat

/-- The exact `[A | G]` Module-SIS map, reused from Hermine SelfTargetMSIS. -/
noncomputable def PublicParameters.msisMap (P : PublicParameters) : Witness →ₗ[Rq] Commitment :=
  augmented P.A P.G

/-- The real BDLOP additive commitment `Com(m;r) = A·r + G·m`. -/
noncomputable def com (P : PublicParameters) (r : Randomness) (m : Rq) : Commitment :=
  P.msisMap (r, m)

theorem com_apply (P : PublicParameters) (r : Randomness) (m : Rq) :
    com P r m = P.A r + m • P.G := by
  simp [com, PublicParameters.msisMap, augmented_apply]

/-- Native ring/module addition aggregates commitments and openings exactly. -/
theorem com_add (P : PublicParameters) (r₁ r₂ : Randomness) (m₁ m₂ : Rq) :
    com P r₁ m₁ + com P r₂ m₂ = com P (r₁ + r₂) (m₁ + m₂) := by
  rw [com_apply, com_apply, com_apply]
  simp only [map_add, add_smul]
  abel

/-- A proof-carrying BDLOP opening.  The radius is on the complete `(r,m)` pair. -/
structure Opening (P : PublicParameters) where
  r : Randomness
  m : Rq
  C : Commitment
  opens : com P r m = C
  radius : nrm (r, m) ≤ P.beta

/-- Aggregating openings requires the aggregate radius explicitly; omitting it remains a type error. -/
noncomputable def Opening.combine (P : PublicParameters) (o₁ o₂ : Opening P)
    (hradius : nrm (o₁.r + o₂.r, o₁.m + o₂.m) ≤ P.beta) : Opening P where
  r := o₁.r + o₂.r
  m := o₁.m + o₂.m
  C := o₁.C + o₂.C
  opens := by rw [← com_add, o₁.opens, o₂.opens]
  radius := hradius

/-- Two candidate openings returned by a binding adversary. -/
structure OpeningPair where
  r : Randomness
  m : Rq
  r' : Randomness
  m' : Rq

/-- The extracted message-carrying Module-SIS witness `(r-r',m-m')`. -/
noncomputable def OpeningPair.diff (o : OpeningPair) : Witness := (o.r - o.r', o.m - o.m')

/-- A genuine binding break: distinct openings, short complete difference, same commitment. -/
def BindingBreak (P : PublicParameters) (o : OpeningPair) : Prop :=
  (o.r, o.m) ≠ (o.r', o.m') ∧
  nrm o.diff ≤ P.beta ∧
  com P o.r o.m = com P o.r' o.m'

/-- **The algebraic binding reduction.** A BDLOP collision yields the existing Hermine/Lattice
`IsMSISSolution` for the real `[A | G]` map.  The witness includes `dm = m-m'`. -/
theorem binding_break_yields_msis_solution (P : PublicParameters) (o : OpeningPair)
    (h : BindingBreak P o) :
    IsMSISSolution P.msisMap P.beta o.diff := by
  obtain ⟨hne, hshort, hcol⟩ := h
  refine ⟨?_, hshort, ?_⟩
  · intro hzero
    apply hne
    apply sub_eq_zero.mp
    simpa [OpeningPair.diff] using hzero
  · rw [show o.diff = (o.r, o.m) - (o.r', o.m') by rfl, map_sub]
    exact sub_eq_zero.mpr hcol

/-- A finite ensemble of real-ring BDLOP public parameters.  At security parameter `l`, `sample`
draws the full matrix/gadget/radius tuple `(A,G,β)`.  The production sampler is supplied by the
cryptographic build rather than replaced by a deterministic Lean toy. -/
structure ParameterDistribution where
  Coins : Nat → Type
  coinsFintype : ∀ l, Fintype (Coins l)
  sample : ∀ l, Coins l → PublicParameters

/-- A resource-bounded binding adversary, represented by a finite private coin space at each security
parameter.  It receives the sampled real-ring public parameters and returns two candidate openings. -/
structure BindingAdversary (D : ParameterDistribution) where
  Coins : Nat → Type
  coinsFintype : ∀ l, Fintype (Coins l)
  run : ∀ l, PublicParameters → Coins l → OpeningPair

/-- A resource-bounded Module-SIS solver for the same sampled real `[A | G]` instance. -/
structure MSISSolver (D : ParameterDistribution) where
  Coins : Nat → Type
  coinsFintype : ∀ l, Fintype (Coins l)
  run : ∀ l, PublicParameters → Coins l → Witness

/-- Binding-breaking advantage over both parameter sampling and adversary coins, as a real finite-game
probability ensemble. -/
noncomputable def bindingAdv (D : ParameterDistribution) (B : BindingAdversary D) : Ensemble := by
  classical
  exact fun l =>
    letI : Fintype (D.Coins l) := D.coinsFintype l
    letI : Fintype (B.Coins l) := B.coinsFintype l
    winProb (fun ω : D.Coins l × B.Coins l =>
      let P := D.sample l ω.1
      decide (BindingBreak P (B.run l P ω.2)))

/-- Module-SIS solving advantage over the identical public-parameter distribution and solver coins. -/
noncomputable def msisAdv (D : ParameterDistribution) (S : MSISSolver D) : Ensemble := by
  classical
  exact fun l =>
    letI : Fintype (D.Coins l) := D.coinsFintype l
    letI : Fintype (S.Coins l) := S.coinsFintype l
    winProb (fun ω : D.Coins l × S.Coins l =>
      let P := D.sample l ω.1
      decide (IsMSISSolution P.msisMap P.beta (S.run l P ω.2)))

/-- The deterministic collision-to-Module-SIS extractor, lifted to adversaries. -/
noncomputable def toMSISSolver (D : ParameterDistribution) (B : BindingAdversary D) : MSISSolver D where
  Coins := B.Coins
  coinsFintype := B.coinsFintype
  run := fun l P ω => (B.run l P ω).diff

/-- Monotonicity of finite winning probability under implication of winning events. -/
theorem winProb_mono {Ω : Type*} [Fintype Ω] (f g : Ω → Bool)
    (h : ∀ ω, f ω = true → g ω = true) : winProb f ≤ winProb g := by
  unfold winProb
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Finset.card_le_card (by
      intro ω hω
      simp only [Finset.mem_filter] at hω ⊢
      exact ⟨hω.1, h ω hω.2⟩)
  · positivity

/-- Every binding win is a Module-SIS win of the extracted solver, so the extractor loses no binding
success probability. -/
theorem bindingAdv_le_msisAdv (D : ParameterDistribution) (B : BindingAdversary D) (l : Nat) :
    bindingAdv D B l ≤ msisAdv D (toMSISSolver D B) l := by
  classical
  letI : Fintype (D.Coins l) := D.coinsFintype l
  letI : Fintype (B.Coins l) := B.coinsFintype l
  apply winProb_mono
  intro ω hwin
  simp only [decide_eq_true_eq] at hwin ⊢
  exact binding_break_yields_msis_solution (D.sample l ω.1)
    (B.run l (D.sample l ω.1) ω.2) hwin

theorem bindingAdv_nonneg (D : ParameterDistribution) (B : BindingAdversary D) (l : Nat) :
    0 ≤ bindingAdv D B l := by
  classical
  letI : Fintype (D.Coins l) := D.coinsFintype l
  letI : Fintype (B.Coins l) := B.coinsFintype l
  exact winProb_nonneg _

theorem msisAdv_nonneg (D : ParameterDistribution) (S : MSISSolver D) (l : Nat) :
    0 ≤ msisAdv D S l := by
  classical
  letI : Fintype (D.Coins l) := D.coinsFintype l
  letI : Fintype (S.Coins l) := S.coinsFintype l
  exact winProb_nonneg _

/-- The uniform resource model supplied by the cryptographic build.  It identifies the efficient
binding breakers and efficient Module-SIS solvers and records that the deterministic subtraction
extractor preserves efficiency.  This prevents non-uniform hardcoded solutions from being silently
quantified as “efficient” adversaries. -/
structure ResourceModel (D : ParameterDistribution) where
  bindingEfficient : BindingAdversary D → Prop
  msisEfficient : MSISSolver D → Prop
  /-- The binding security game is not made vacuous by declaring that no adversary is efficient. -/
  bindingNonempty : Nonempty {B : BindingAdversary D // bindingEfficient B}
  /-- The Module-SIS floor quantifies over a genuinely inhabited efficient-solver class. -/
  msisNonempty : Nonempty {S : MSISSolver D // msisEfficient S}
  extractionEfficient : ∀ B, bindingEfficient B → msisEfficient (toMSISSolver D B)

/-- The existing adversary-indexed quantitative Module-SIS floor, specialized to the efficient
solvers for this real instance. -/
abbrev MSISHard (D : ParameterDistribution) (M : ResourceModel D) : Prop :=
  MSISHardQuant (fun S : {S : MSISSolver D // M.msisEfficient S} => msisAdv D S.1)

/-- Computational aggregate binding: every efficient binding adversary has negligible advantage. -/
def AggregateBinding (D : ParameterDistribution) (M : ResourceModel D) : Prop :=
  ∀ B : BindingAdversary D, M.bindingEfficient B → Negl (bindingAdv D B)

/-- **The real floor.** Quantitative Module-SIS hardness of the genuine `[A | G]` ring/matrix instance
implies aggregate binding.  This is an advantage reduction, not an existence-refutation. -/
theorem aggregate_binding_of_MSISHard (D : ParameterDistribution) (M : ResourceModel D)
    (hard : MSISHard D M) : AggregateBinding D M := by
  intro B hEff
  let S : {S : MSISSolver D // M.msisEfficient S} :=
    ⟨toMSISSolver D B, M.extractionEfficient B hEff⟩
  have hsolver : Negl (msisAdv D (toMSISSolver D B)) := hard S
  refine negl_of_eventually_le (Eventually.of_forall (fun l => ?_)) hsolver
  rw [abs_of_nonneg (bindingAdv_nonneg D B l),
    abs_of_nonneg (msisAdv_nonneg D (toMSISSolver D B) l)]
  exact bindingAdv_le_msisAdv D B l

/-! ### A real-ring inhabited reference instance and anti-scalar teeth. -/

/-- Executable reference radius; not a claim about production distribution sizing. -/
def referenceBeta : Nat := 1

/-- Inhabited real-ring shape witness.  `A` and `G` have the genuine `6×5`/`6` ML-DSA module shape;
`beta = 1` is only the executable non-vacuity radius.  This deterministic correctness witness is
deliberately NOT installed as the security distribution: production BDLOP sampling and its concrete
security estimate remain carried crypto-build inputs. -/
noncomputable def realParameters : PublicParameters where
  A := honestA
  G := wVec
  beta := referenceBeta

theorem coeffL1_one : coeffL1 (1 : Rq) = 1 := by
  classical
  let j0 : Fin pb.dim := ⟨0, dim_pos⟩
  have hbasis : pb.basis j0 = (1 : Rq) := by rw [pb.basis_eq_pow]; simp [j0]
  have hre : pb.basis.repr (1 : Rq) = Finsupp.single j0 1 := by
    rw [← hbasis, pb.basis.repr_self]
  unfold coeffL1
  rw [hre]
  rw [Finset.sum_eq_single j0]
  · have hone : (1 : ZMod q).valMinAbs = 1 :=
      ZMod.valMinAbs_natCast_of_le_half (n := q) (a := 1) (by norm_num [q])
    rw [Finsupp.single_eq_same]
    rw [hone]
    norm_num
  · intro j _ hj
    simp [Finsupp.single_eq_of_ne hj]
  · simp

theorem coeffL1_neg_one : coeffL1 (-1 : Rq) = 1 := by
  calc
    coeffL1 (-1 : Rq) = coeffL1 (1 : Rq) := instShortNormRq.nrm_neg 1
    _ = 1 := coeffL1_one

theorem coeffL1_zero : coeffL1 (0 : Rq) = 0 := instShortNormRq.nrm_zero

/-- A nonzero opening of the real-ring reference instance: message `1`, randomness `0`, commitment `G`. -/
noncomputable def realOpening : Opening realParameters where
  r := 0
  m := 1
  C := wVec
  opens := by simp [com_apply, realParameters]
  radius := by
    change (∑ _ : Fin ell, coeffL1 0) + coeffL1 1 ≤ referenceBeta
    simp [coeffL1_zero, coeffL1_one, referenceBeta]

/-- The real-ring witness is inhabited by a nonzero commitment, not only the zero opening. -/
theorem realOpening_commitment_ne_zero : realOpening.C ≠ 0 := by
  intro hzero
  have hcoord := congrFun hzero (0 : Fin kk)
  have hrv := congrArg (fun x : Rq => rv x ⟨0, dim_pos⟩) hcoord
  simp [realOpening, wVec, gappedElt_rv, rv_zero] at hrv

/-- The real quotient-ring/module opening relation is inhabited by a nonzero commitment. -/
theorem real_ring_nonzero_opening_exists :
    ∃ o : Opening realParameters, o.C ≠ 0 :=
  ⟨realOpening, realOpening_commitment_ne_zero⟩

/-- The old scalar `(1,-1)` pattern, embedded faithfully in the real witness space: one randomness
basis coordinate is the ring unit and the message coordinate is `-1`. -/
noncomputable def scalarStyleBreak : Witness := (unitMask, -1)

/-- Its genuine Hermine coordinate-sum norm is two, not the scalar model's radius one. -/
theorem scalarStyleBreak_norm : nrm scalarStyleBreak = 2 := by
  change (∑ i : Fin ell, coeffL1 (unitMask i)) + coeffL1 (-1) = 2
  have hsum : (∑ i : Fin ell, coeffL1 (unitMask i)) = 1 := by
    rw [Finset.sum_eq_single (0 : Fin ell)]
    · simp [unitMask, coeffL1_one]
    · intro i _ hi
      simp [unitMask, hi, coeffL1_zero]
    · simp
  rw [hsum, coeffL1_neg_one]

/-- **Anti-scalar tooth:** the old scalar-style witness is not accepted by the real reference radius. -/
theorem scalarStyleBreak_not_short : ¬ nrm scalarStyleBreak ≤ realParameters.beta := by
  rw [scalarStyleBreak_norm]
  norm_num [realParameters, referenceBeta]

/-- The historical residual name now points to the positive distributed real-ring reduction. -/
theorem AggregateBindingScalarFloorResidual (D : ParameterDistribution) (M : ResourceModel D)
    (hard : MSISHard D M) : AggregateBinding D M :=
  aggregate_binding_of_MSISHard D M hard

#guard Dregg2.Crypto.Fips204CorrectReal.q == 8380417
#guard Dregg2.Crypto.Fips204CorrectReal.ell == 5
#guard Dregg2.Crypto.Fips204CorrectReal.kk == 6
#guard (2 : Nat) > referenceBeta

#assert_axioms coeffL1_one
#assert_axioms coeffL1_neg_one
#assert_axioms coeffL1_zero
#assert_axioms com_apply
#assert_axioms com_add
#assert_axioms binding_break_yields_msis_solution
#assert_axioms winProb_mono
#assert_axioms bindingAdv_le_msisAdv
#assert_axioms bindingAdv_nonneg
#assert_axioms msisAdv_nonneg
#assert_axioms aggregate_binding_of_MSISHard
#assert_axioms realOpening_commitment_ne_zero
#assert_axioms real_ring_nonzero_opening_exists
#assert_axioms scalarStyleBreak_norm
#assert_axioms scalarStyleBreak_not_short
#assert_axioms AggregateBindingScalarFloorResidual

end BDLOP

#assert_axioms Com_def
#assert_axioms Com_add
#assert_axioms collision_yields_msis_witness
#assert_axioms combine_r
#assert_axioms combine_m
#assert_axioms combine_C
#assert_axioms combine_radius_is_aggregate

end Market
