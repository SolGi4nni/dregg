/-
Mechanized refutation of a q-strong-DLOG assumption stated in ArkLib's own idiom.
NOT part of ArkLib. Scratch file supporting the qdlog-direct candidate writeup.

Claim proved here: if one states the natural "reduce KZG binding to q-DLOG" base
assumption -- recover the SRS trapdoor `τ` from the KZG power-SRS -- with the SAME
unrestricted adversary TYPE that ArkLib uses for `tSdhAssumption`
(`… → StateT unifSpec.QueryCache ProbComp (Option _)`, a free monad), then it is
ALSO vacuous: false for every error < 1, by the identical `Classical.choice`
trapdoor-extraction. So "reduce to q-DLOG" does not, by itself, escape the hole:
the base assumption must first be restated over a sound adversary class.
-/
import ArkLib.Commitments.Functional.KZG.HardnessAssumptions

open OracleSpec OracleComp
open scoped NNReal ENNReal

namespace ArkLibQDlogVacuity

section Dlog

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The choice-definable discrete logarithm base a nontrivial `g` in a prime-order group.
Not an algorithm: `Exists.choose` applied to ArkLib's `exists_zmod_power_of_generator`. -/
noncomputable def dlogOf {G : Type} [Group G] [PrimeOrderWith G p] {g : G} (hg : g ≠ 1)
    (x : G) : ZMod p :=
  (Groups.exists_zmod_power_of_generator (G := G) PrimeOrderWith.hCard hg
    (Groups.orderOf_eq_prime_of_ne_one g hg) x).choose

/-- `dlogOf` inverts exponentiation base a nontrivial element of a prime-order group. -/
lemma dlogOf_pow {G : Type} [Group G] [PrimeOrderWith G p] {g : G} (hg : g ≠ 1) (a : ZMod p) :
    dlogOf (p := p) hg (g ^ a.val) = a := by
  have hord : orderOf g = p := Groups.orderOf_eq_prime_of_ne_one g hg
  have hspec : g ^ a.val = g ^ (dlogOf (p := p) hg (g ^ a.val)).val :=
    (Groups.exists_zmod_power_of_generator (G := G) PrimeOrderWith.hCard hg hord
      (g ^ a.val)).choose_spec
  have hdiv : g ^ (dlogOf (p := p) hg (g ^ a.val) - a).val = 1 := by
    rw [← Groups.gpow_div_eq hord _ a, ← hspec, div_self']
  exact sub_eq_zero.mp (Groups.zmod_eq_zero_of_gpow_eq_one hord hdiv)

/-- Every value in the support of ArkLib's trapdoor sampler is nonzero. -/
lemma sampleNonzeroZMod_ne_zero {τ : ZMod p}
    (hτ : τ ∈ support (Groups.sampleNonzeroZMod (p := p))) : τ ≠ 0 := by
  have hp : 1 < p := Nat.Prime.one_lt Fact.out
  haveI : NeZero (p - 1) := ⟨Nat.pos_iff_ne_zero.mp (Nat.sub_pos_of_lt hp)⟩
  haveI : NeZero p := ⟨Nat.pos_iff_ne_zero.mp (Nat.zero_lt_of_lt hp)⟩
  rw [Groups.sampleNonzeroZMod, support_map] at hτ
  obtain ⟨i, -, rfl⟩ := hτ
  have hi := i.isLt
  have hlt : (i : ℕ) + 1 < p := by omega
  intro hzero
  simp only at hzero
  have hdvd : (((i : ℕ) + 1 : ℕ) : ZMod p) = 0 := by push_cast; exact hzero
  rw [ZMod.natCast_eq_zero_iff] at hdvd
  exact absurd (Nat.le_of_dvd (Nat.succ_pos _) hdvd) (not_le.mpr hlt)

/-- ArkLib's trapdoor sampler never fails. -/
lemma probFailure_sampleNonzeroZMod : Pr[⊥ | Groups.sampleNonzeroZMod (p := p)] = 0 := by
  rw [Groups.sampleNonzeroZMod]; simp

end Dlog

section QDlog

variable {p : ℕ} [Fact (Nat.Prime p)]
  {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] {g₁ : G₁}
  {G₂ : Type} [Group G₂] [PrimeOrderWith G₂ p] {g₂ : G₂}
  [∀ i, SampleableType (unifSpec.Range i)]

/-- A q-strong-DLOG adversary: receives the KZG power-SRS and returns a scalar (its guess
for the trapdoor `τ`). Deliberately the SAME adversary TYPE shape ArkLib uses for
`tSdhAdversary`: a plain function into `StateT unifSpec.QueryCache ProbComp`, i.e. a free
monad where pure computation is uncharged. -/
abbrev qDlogAdversary (D : ℕ) :=
  Vector G₁ (D + 1) × Vector G₂ 2 →
    StateT unifSpec.QueryCache ProbComp (Option (ZMod p))

/-- q-DLOG winning condition: the guess equals the true trapdoor. -/
abbrev qDlogCondition : (ZMod p × ZMod p) → Prop :=
  fun (τ, τ') => τ' = τ

/-- The q-DLOG game for a specific adversary, in ArkLib's exact SRS/sampler idiom. -/
abbrev qDlogGame {g₁ : G₁} {g₂ : G₂} (D : ℕ) (adversary : qDlogAdversary (G₁ := G₁) (G₂ := G₂) (p := p) D) :
    OptionT ProbComp (ZMod p × ZMod p) :=
  OptionT.mk (do
    let τ ← Groups.sampleNonzeroZMod (p := p)
    let srs := Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ
    let result ← (adversary srs).run' ∅
    pure (result.map (fun (τ' : ZMod p) => (τ, τ'))))

/-- The probability of breaking q-DLOG for a specific adversary. -/
noncomputable def qDlogExperiment {g₁ : G₁} {g₂ : G₂} (D : ℕ)
    (adversary : qDlogAdversary (G₁ := G₁) (G₂ := G₂) (p := p) D) : ℝ≥0∞ :=
  Pr[qDlogCondition (p := p) | qDlogGame (g₁ := g₁) (g₂ := g₂) D adversary]

/-- The q-DLOG assumption: bound every adversary's success probability by `error`.
Same universally-quantified-over-the-TYPE shape as `Groups.tSdhAssumption`. -/
def qDlogAssumption {g₁ : G₁} {g₂ : G₂} (D : ℕ) (error : ℝ≥0) : Prop :=
  ∀ (adversary : qDlogAdversary (G₁ := G₁) (G₂ := G₂) (p := p) D),
    qDlogExperiment (g₁ := g₁) (g₂ := g₂) D adversary ≤ (error : ℝ≥0∞)

/-- The winning q-DLOG adversary: reads `g₂ ^ τ` from the verifier leg of the SRS,
recovers `τ` by `Classical.choice`, and returns it. ZERO oracle queries. -/
noncomputable def trapdoorAdversary (hg₂ : g₂ ≠ 1) (D : ℕ) :
    qDlogAdversary (G₁ := G₁) (G₂ := G₂) (p := p) D :=
  fun srs => pure (some (dlogOf (p := p) hg₂ srs.2[1]))

/-- The q-DLOG game with the exhibited adversary collapses to a `map` over the trapdoor
sampler: the adversary has already recovered `τ`. -/
lemma qDlog_game_run_eq (hg₂ : g₂ ≠ 1) (D : ℕ) :
    (qDlogGame (g₁ := g₁) (g₂ := g₂) D
      (trapdoorAdversary (G₁ := G₁) (g₂ := g₂) (p := p) hg₂ D)).run
      = (fun τ : ZMod p => some (τ, τ)) <$> Groups.sampleNonzeroZMod := by
  simp [qDlogGame, trapdoorAdversary, Groups.PowerSrs.generate,
    Groups.PowerSrs.tower, dlogOf_pow hg₂]

/-- The exhibited adversary wins q-DLOG with probability exactly `1`. -/
theorem qDlogExperiment_trapdoorAdversary (hg₂ : g₂ ≠ 1) (D : ℕ) :
    qDlogExperiment (g₁ := g₁) (g₂ := g₂) D
      (trapdoorAdversary (G₁ := G₁) (g₂ := g₂) (p := p) hg₂ D) = 1 := by
  classical
  rw [qDlogExperiment, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, qDlog_game_run_eq (g₁ := g₁) hg₂ D, probFailure_map,
      probFailure_sampleNonzeroZMod]
    simp
  · intro x hx
    rw [OptionT.support_def, qDlog_game_run_eq (g₁ := g₁) hg₂ D, support_map] at hx
    obtain ⟨τ, hτ, hxτ⟩ := hx
    simp only [Option.some.injEq] at hxτ
    subst hxτ
    rfl

/-- **The refutation.** A q-strong-DLOG assumption stated with the unrestricted ArkLib
adversary type is FALSE for every error bound `< 1`, at every degree `D`, in every
prime-order group pair with a nontrivial `g₂`. Same `Classical.choice` extraction that
kills `tSdhAssumption`. -/
theorem not_qDlogAssumption (hg₂ : g₂ ≠ 1) (D : ℕ) (error : ℝ≥0) (herr : (error : ℝ≥0∞) < 1) :
    ¬ qDlogAssumption (p := p) (G₁ := G₁) (G₂ := G₂) (g₁ := g₁) (g₂ := g₂) D error := by
  intro h
  have hle := h (trapdoorAdversary (G₁ := G₁) (g₂ := g₂) (p := p) hg₂ D)
  rw [qDlogExperiment_trapdoorAdversary (g₁ := g₁) hg₂ D] at hle
  exact absurd (lt_of_le_of_lt hle herr) (lt_irrefl 1)

/-- The other regime: for `error ≥ 1` the assumption holds trivially. So `qDlogAssumption`
has NO content at ANY parameter — false below 1, vacuous at/above 1. -/
theorem qDlogAssumption_trivial_of_one_le (D : ℕ) (error : ℝ≥0)
    (herr : (1 : ℝ≥0∞) ≤ (error : ℝ≥0∞)) :
    qDlogAssumption (p := p) (G₁ := G₁) (G₂ := G₂) (g₁ := g₁) (g₂ := g₂) D error := by
  intro adversary
  refine le_trans ?_ herr
  rw [qDlogExperiment]
  exact probEvent_le_one

/-! ### Canary — the experiment discriminates -/

/-- An adversary that gives up. -/
def givingUpAdversary (D : ℕ) : qDlogAdversary (G₁ := G₁) (G₂ := G₂) (p := p) D :=
  fun _ => pure none

/-- CANARY: giving up loses with probability `1`, so `qDlogExperiment` is not constantly `1`. -/
theorem qDlogExperiment_givingUpAdversary (D : ℕ) :
    qDlogExperiment (g₁ := g₁) (g₂ := g₂) D
      (givingUpAdversary (G₁ := G₁) (G₂ := G₂) (p := p) D) = 0 := by
  classical
  rw [qDlogExperiment, probEvent_eq_zero_iff]
  intro x hx
  rw [OptionT.support_def] at hx
  simp [qDlogGame, givingUpAdversary] at hx

/-- CANARY: the two adversaries are genuinely separated by the experiment. -/
theorem experiment_discriminates (hg₂ : g₂ ≠ 1) (D : ℕ) :
    qDlogExperiment (g₁ := g₁) (g₂ := g₂) D
      (givingUpAdversary (G₁ := G₁) (G₂ := G₂) (p := p) D)
    ≠ qDlogExperiment (g₁ := g₁) (g₂ := g₂) D
      (trapdoorAdversary (G₁ := G₁) (g₂ := g₂) (p := p) hg₂ D) := by
  rw [qDlogExperiment_givingUpAdversary (g₁ := g₁) (g₂ := g₂) D,
    qDlogExperiment_trapdoorAdversary (g₁ := g₁) hg₂ D]
  exact zero_ne_one

end QDlog

end ArkLibQDlogVacuity
