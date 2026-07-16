/-
Mechanized refutation of ArkLib's `Groups.tSdhAssumption`.
NOT part of ArkLib. Scratch file supporting a disclosure note.
-/
import ArkLib.Commitments.Functional.KZG.Binding

open OracleSpec OracleComp
open scoped NNReal ENNReal

namespace ArkLibVacuity

section Dlog

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The choice-definable discrete logarithm base a nontrivial `g` in a prime-order group.
This is *not* an algorithm: it is `Exists.choose` applied to ArkLib's own
`Groups.exists_zmod_power_of_generator`. It is nevertheless a perfectly legal
inhabitant of `ZMod p`, and that is the whole point. -/
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

section Refutation

variable {p : ℕ} [Fact (Nat.Prime p)]
  {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] {g₁ : G₁}
  {G₂ : Type} [Group G₂] [PrimeOrderWith G₂ p] {g₂ : G₂}
  [∀ i, SampleableType (unifSpec.Range i)]

/-- The winning t-SDH adversary. It reads `g₂ ^ τ` out of the *verifier* leg of the SRS,
recovers `τ` by `Classical.choice`, and returns the t-SDH solution at offset `c = 0`.
It makes ZERO oracle queries: all of its work happens under `pure`, which the free monad
`ProbComp` does not charge for. -/
noncomputable def tauExtractingAdversary (hg₂ : g₂ ≠ 1) (D : ℕ) :
    Groups.tSdhAdversary (G₁ := G₁) (G₂ := G₂) (p := p) D :=
  fun srs => pure (some (0, g₁ ^ (1 / dlogOf (p := p) hg₂ srs.2[1]).val))

/-- The t-SDH game with the exhibited adversary collapses to a single `map` over the
trapdoor sampler: the adversary has already recovered `τ`. -/
lemma game_run_eq (hg₂ : g₂ ≠ 1) (D : ℕ) :
    (Groups.tSdhGame (g₁ := g₁) (g₂ := g₂) D
      (tauExtractingAdversary (G₁ := G₁) (g₁ := g₁) (g₂ := g₂) (p := p) hg₂ D)).run
      = (fun τ : ZMod p => some (τ, (0 : ZMod p), g₁ ^ (1 / τ).val))
          <$> Groups.sampleNonzeroZMod := by
  simp [Groups.tSdhGame, tauExtractingAdversary, Groups.PowerSrs.generate,
    Groups.PowerSrs.tower, dlogOf_pow hg₂]

/-- The exhibited adversary wins the t-SDH game with probability exactly `1`. -/
theorem tSdhExperiment_tauExtractingAdversary (hg₂ : g₂ ≠ 1) (D : ℕ) :
    Groups.tSdhExperiment (g₁ := g₁) (g₂ := g₂) D
      (tauExtractingAdversary (G₁ := G₁) (g₁ := g₁) (g₂ := g₂) (p := p) hg₂ D) = 1 := by
  classical
  rw [Groups.tSdhExperiment, probEvent_eq_one_iff]
  refine ⟨?_, ?_⟩
  · rw [OptionT.probFailure_eq, game_run_eq (g₁ := g₁) hg₂ D, probFailure_map,
      probFailure_sampleNonzeroZMod]
    simp
  · intro x hx
    rw [OptionT.support_def, game_run_eq (g₁ := g₁) hg₂ D, support_map] at hx
    obtain ⟨τ, hτ, hxτ⟩ := hx
    simp only [Option.some.injEq] at hxτ
    subst hxτ
    have hτ0 : τ ≠ 0 := sampleNonzeroZMod_ne_zero hτ
    exact ⟨by simpa using hτ0, by simp⟩

/-- **The refutation.** ArkLib's `tSdhAssumption` is FALSE for every error bound `< 1`,
at every degree `D`, in every prime-order group pair with a nontrivial `g₂`.
No hypothesis about the size of `p` is needed: this is not an asymptotic statement. -/
theorem not_tSdhAssumption (hg₂ : g₂ ≠ 1) (D : ℕ) (error : ℝ≥0) (herr : (error : ℝ≥0∞) < 1) :
    ¬ Groups.tSdhAssumption (p := p) (G₁ := G₁) (G₂ := G₂) (g₁ := g₁) (g₂ := g₂) D error := by
  intro h
  have hle := h (tauExtractingAdversary (G₁ := G₁) (g₁ := g₁) (g₂ := g₂) (p := p) hg₂ D)
  rw [tSdhExperiment_tauExtractingAdversary (g₁ := g₁) hg₂ D] at hle
  exact absurd (lt_of_le_of_lt hle herr) (lt_irrefl 1)

/-! ### Canary

A gate that accepts everything is a broken gate. The two lemmas below check that
`tSdhExperiment` is not *constantly* `1` — i.e. that the probability-1 theorem above is a
statement about the exhibited adversary and not an artifact of the probability machinery. -/

/-- An adversary that simply gives up. -/
def givingUpAdversary (D : ℕ) : Groups.tSdhAdversary (G₁ := G₁) (G₂ := G₂) (p := p) D :=
  fun _ => pure none

/-- CANARY: giving up loses with probability `1`, so `tSdhExperiment` discriminates. -/
theorem tSdhExperiment_givingUpAdversary (D : ℕ) :
    Groups.tSdhExperiment (g₁ := g₁) (g₂ := g₂) D
      (givingUpAdversary (G₁ := G₁) (G₂ := G₂) (p := p) D) = 0 := by
  classical
  rw [Groups.tSdhExperiment, probEvent_eq_zero_iff]
  intro x hx
  rw [OptionT.support_def] at hx
  simp [Groups.tSdhGame, givingUpAdversary] at hx

/-- CANARY: consequently the probability-1 result is not vacuous — the two adversaries
are genuinely separated by the experiment. -/
theorem experiment_discriminates (hg₂ : g₂ ≠ 1) (D : ℕ) :
    Groups.tSdhExperiment (g₁ := g₁) (g₂ := g₂) D
      (givingUpAdversary (G₁ := G₁) (G₂ := G₂) (p := p) D)
    ≠ Groups.tSdhExperiment (g₁ := g₁) (g₂ := g₂) D
      (tauExtractingAdversary (G₁ := G₁) (g₁ := g₁) (g₂ := g₂) (p := p) hg₂ D) := by
  rw [tSdhExperiment_givingUpAdversary (g₁ := g₁) (g₂ := g₂) D,
    tSdhExperiment_tauExtractingAdversary (g₁ := g₁) hg₂ D]
  exact zero_ne_one

end Refutation

section BindingIsVacuous

variable {p : ℕ} [Fact (Nat.Prime p)]
  {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] {g₁ : G₁}
  {G₂ : Type} [Group G₂] [PrimeOrderWith G₂ p] {g₂ : G₂}
  {Gₜ : Type} [Group Gₜ] [PrimeOrderWith Gₜ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)]
  [∀ i, SampleableType (unifSpec.Range i)]

/-- `binding`'s own pairing hypothesis forces the G₂ generator to be nontrivial,
because the pairing is `ZMod p`-bilinear and therefore kills the identity. -/
lemma g₂_ne_one_of_pairing_ne_zero
    (pairing : (Additive G₁) →ₗ[ZMod p] (Additive G₂) →ₗ[ZMod p] (Additive Gₜ))
    (hpair : pairing (Additive.ofMul g₁) (Additive.ofMul g₂) ≠ 0) : g₂ ≠ 1 := by
  intro h
  apply hpair
  rw [show (Additive.ofMul g₂) = 0 from congrArg Additive.ofMul h]
  exact map_zero _

/-- **`KZG.binding`'s hypotheses are jointly unsatisfiable at every meaningful error.**
The very pairing nondegeneracy that `binding` needs to run its reduction is what makes
its `t`-SDH premise false. So `binding` is only ever applicable with `tSdhError ≥ 1`,
where its conclusion is a triviality (a probability is always `≤ 1`). -/
theorem binding_hypotheses_unsatisfiable
    (pairing : (Additive G₁) →ₗ[ZMod p] (Additive G₂) →ₗ[ZMod p] (Additive Gₜ))
    (hpair : pairing (Additive.ofMul g₁) (Additive.ofMul g₂) ≠ 0)
    (n : ℕ) (tSdhError : ℝ≥0) (herr : (tSdhError : ℝ≥0∞) < 1) :
    ¬ Groups.tSdhAssumption (p := p) (G₁ := G₁) (G₂ := G₂) (g₁ := g₁) (g₂ := g₂) n tSdhError :=
  not_tSdhAssumption (g₁ := g₁) (g₂_ne_one_of_pairing_ne_zero pairing hpair) n tSdhError herr

end BindingIsVacuous

end ArkLibVacuity
