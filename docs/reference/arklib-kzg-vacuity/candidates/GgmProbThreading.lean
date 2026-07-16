/-
PROBABILITY THREADING: ArkLib's real `tSdhExperiment` (an `OptionT ProbComp` game whose
adversary lives in `StateT unifSpec.QueryCache ProbComp`) reduced to a plain
`Finset`-cardinality count `(winSet.card) / (p - 1)` in `ℝ≥0∞`.

NOT part of ArkLib. Scratch research file supporting
`docs/reference/arklib-kzg-vacuity/END-TO-END-PLAN.md` (task C). Built against ArkLib
@ `d72f8392` (Lean v4.31.0); imports ArkLib's REAL definitions
(`Groups.tSdhGame`, `Groups.tSdhExperiment`, `Groups.tSdhCondition`,
`Groups.sampleNonzeroZMod`) — nothing is restated.

THE GAP THIS FILE CLOSES (END-TO-END-PLAN §2c). ArkLib's hardness game is

    tSdhExperiment D A = Pr[tSdhCondition | tSdhGame D A]

with `tSdhGame D A = OptionT.mk (do τ ← sampleNonzeroZMod; …; (A srs).run' ∅; pure …)`
an `ℝ≥0∞` probability over the `OptionT`/`StateT`/`ProbComp` monad stack. The GGM/counting
bounds (`GgmAdaptive`, `GgmRandomEncoding`, `GgmArkLibTransport`) are all `ℚ`-cardinality
statements about a *set of winning trapdoors*. This file threads the two together for any
adversary that is deterministic-given-τ from an empty cache — exactly the shape that task D's
`embed` produces (`embed strat srs = pure (…)`, so `(embed strat srs).run' ∅ = pure result`):

  * `game_collapse` (c1): peel the game monad. With `(A (PowerSrs.generate D τ)).run' ∅
    = pure (resultOf τ)`, the whole `OptionT`/`StateT` game collapses to
    `OptionT.mk (do τ ← sampleNonzeroZMod; pure ((resultOf τ).map (τ, ·, ·)))`.

  * `experiment_eq_count` (c2): count the sampler. That probability equals
    `(winSet.card) / (p - 1)`, where `winSet` is the set of nonzero-trapdoor indices
    `i : Fin (p-1)` on which the deterministic adversary's output wins `tSdhCondition`.

TOOLS REUSED (all pre-existing; END-TO-END-PLAN §2c named them):
  * VCVio `probEvent_uniformSample` (`Pr[q | $ᵗ α] = (univ.filter q).card / card α`) and
    `probEvent_map` (`Pr[q | f <$> mx] = Pr[q ∘ f | mx]`).
  * VCVio `OptionT.probOutput_eq` / `probEvent_eq_tsum_subtype` for the `OptionT.mk` peel
    (the `none`-mass is handled by a subtype reindexing, no `ℝ≥0∞` subtraction).
  * ArkLib's `Binding.lean` is the precedent for the identical-shape
    `Pr[· | OptionT.mk (do τ ← sampleNonzeroZMod; …)]` reduction (it uses the same
    `OptionT.probEvent_eq_of_run_map_eq` / `probEvent_map` / `probEvent_mono` idioms).
-/

import ArkLib.Commitments.Functional.KZG.HardnessAssumptions

open OracleSpec OracleComp Groups
open scoped Classical NNReal ENNReal

namespace Ggm.ProbThreading

variable {p : ℕ} [Fact (Nat.Prime p)]
  [∀ i, SampleableType (unifSpec.Range i)]
  {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] {g₁ : G₁}
  {G₂ : Type} [Group G₂] [PrimeOrderWith G₂ p] {g₂ : G₂}

/-! ### The `OptionT.mk` peel

A generic lemma: the success probability of an event `P` under an `OptionT ProbComp`
computation built from `M : ProbComp (Option α)` equals, in the plain `ProbComp`, the
probability that the sampled `Option` is `some a` with `P a`. Failure (`none`) never counts
toward the event. Proven by reindexing the event subtype through `a ↦ some a`, so there is no
`ℝ≥0∞` subtraction of the failure mass. -/
omit [∀ i, SampleableType (unifSpec.Range i)] in
lemma probEvent_optionT_mk {α : Type} (M : ProbComp (Option α)) (P : α → Prop) :
    Pr[P | (OptionT.mk M : OptionT ProbComp α)]
      = Pr[fun o => ∃ a, o = some a ∧ P a | M] := by
  rw [probEvent_eq_tsum_subtype (OptionT.mk M) P,
      probEvent_eq_tsum_subtype M (fun o => ∃ a, o = some a ∧ P a)]
  simp only [OptionT.probOutput_eq, OptionT.run_mk]
  -- goal: ∑' x : {a // P a}, Pr[= some ↑x | M] = ∑' o : {o // ∃ a, o = some a ∧ P a}, Pr[= ↑o | M]
  let e : {a : α // P a} ≃ {o : Option α // ∃ a, o = some a ∧ P a} :=
    { toFun := fun x => ⟨some x.1, x.1, rfl, x.2⟩
      invFun := fun o => ⟨o.2.choose, o.2.choose_spec.2⟩
      left_inv := by
        intro x
        apply Subtype.ext
        have h := (Exists.choose_spec (⟨x.1, rfl, x.2⟩ : ∃ a, some x.1 = some a ∧ P a)).1
        exact (Option.some.inj h).symm
      right_inv := by
        intro o
        apply Subtype.ext
        exact (o.2.choose_spec).1.symm }
  exact Equiv.tsum_eq e (fun o => Pr[= (↑o : Option α) | M])

/-! ### (c1) The game collapse

For an adversary that is deterministic-given-τ from an empty cache, the whole
`OptionT`/`StateT`/`ProbComp` game monad collapses to the trapdoor sampler followed by a
pure deterministic tail. `resultOf τ` is the adversary's `Option (challenge, group elt)`
output on the SRS generated from `τ`. -/

/-- The collapsed game's underlying `ProbComp (Option _)`: sample the nonzero trapdoor, then
tag the deterministic output with it. -/
noncomputable def collapsedGameRun (resultOf : ZMod p → Option (ZMod p × G₁)) :
    ProbComp (Option (ZMod p × ZMod p × G₁)) :=
  sampleNonzeroZMod (p := p) >>= fun τ =>
    pure ((resultOf τ).map (fun ((c, h) : ZMod p × G₁) => (τ, c, h)))

omit [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] in
/-- **(c1) `game_collapse`.** Peel the game monad: with the adversary deterministic-given-τ
from the empty cache (`hdet`), `tSdhGame` equals `OptionT.mk` of the collapsed run. -/
theorem game_collapse (D : ℕ) (A : tSdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p))
    (resultOf : ZMod p → Option (ZMod p × G₁))
    (hdet : ∀ τ, (A (PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ)).run' ∅
      = pure (resultOf τ)) :
    tSdhGame (g₁ := g₁) (g₂ := g₂) D A
      = OptionT.mk (collapsedGameRun resultOf) := by
  unfold tSdhGame collapsedGameRun
  simp only [hdet, pure_bind]

/-! ### (c2) Count the sampler

The nonzero-trapdoor sampler is `(i ↦ (i+1 : ZMod p)) <$> $ᵗ(Fin (p-1))`, so any event over
it is `(filter).card / (p-1)` by `probEvent_map` + `probEvent_uniformSample`. -/

omit [∀ i, SampleableType (unifSpec.Range i)] in
/-- Every event over the nonzero-trapdoor sampler is a `Fin (p-1)` count over `p-1`.
`(i : Fin (p-1))` maps to trapdoor `(i+1 : ZMod p)`, ranging over the nonzero residues. -/
lemma probEvent_sampleNonzeroZMod (q : ZMod p → Prop) :
    Pr[q | (sampleNonzeroZMod (p := p))]
      = ((Finset.univ.filter (fun i : Fin (p - 1) => q ((i : ℕ) + 1))).card : ℝ≥0∞)
          / ((p - 1 : ℕ) : ℝ≥0∞) := by
  haveI : NeZero (p - 1) :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.sub_pos_of_lt (Nat.Prime.one_lt Fact.out))⟩
  unfold sampleNonzeroZMod
  rw [probEvent_map, probEvent_uniformSample, Fintype.card_fin]
  rfl

/-- The winning-trapdoor set: nonzero-trapdoor indices `i : Fin (p-1)` (trapdoor `i+1`) on
which the deterministic adversary outputs some `(c, h)` that satisfies ArkLib's
`tSdhCondition`. This is exactly the set whose cardinality the GGM/counting bounds bound. -/
def winPred (resultOf : ZMod p → Option (ZMod p × G₁)) (g₁ : G₁) :
    Fin (p - 1) → Prop :=
  fun i => ∃ ch : ZMod p × G₁,
    resultOf ((i : ℕ) + 1 : ZMod p) = some ch ∧
      tSdhCondition (p := p) (g₁ := g₁) (((i : ℕ) + 1 : ZMod p), ch.1, ch.2)

omit [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p] in
/-- **(c2) `experiment_eq_count`.** ArkLib's `tSdhExperiment` for a deterministic-given-τ
adversary equals the counting fraction `(winSet.card) / (p - 1)` in `ℝ≥0∞`. -/
theorem experiment_eq_count (D : ℕ) (A : tSdhAdversary D (G₁ := G₁) (G₂ := G₂) (p := p))
    (resultOf : ZMod p → Option (ZMod p × G₁))
    (hdet : ∀ τ, (A (PowerSrs.generate (g₁ := g₁) (g₂ := g₂) D τ)).run' ∅
      = pure (resultOf τ)) :
    tSdhExperiment (g₁ := g₁) (g₂ := g₂) D A
      = ((Finset.univ.filter (winPred (p := p) resultOf g₁)).card : ℝ≥0∞)
          / ((p - 1 : ℕ) : ℝ≥0∞) := by
  unfold tSdhExperiment
  rw [game_collapse (g₁ := g₁) (g₂ := g₂) D A resultOf hdet,
      probEvent_optionT_mk (collapsedGameRun resultOf)
        (tSdhCondition (p := p) (g₁ := g₁))]
  unfold collapsedGameRun
  rw [bind_pure_comp, probEvent_map]
  -- Rewrite the composed event to the clean per-trapdoor winning predicate BEFORE counting.
  -- (Doing it after `probEvent_sampleNonzeroZMod` would force a `DecidablePred` synthesis on the
  -- composed `∃ … Option.map … tSdhCondition …` predicate, which loops.)
  have hev :
      Pr[((fun o => ∃ a, o = some a ∧ tSdhCondition (p := p) (g₁ := g₁) a) ∘
            fun τ => (resultOf τ).map (fun ((c, h) : ZMod p × G₁) => (τ, c, h)))
        | sampleNonzeroZMod (p := p)]
      = Pr[(fun τ => ∃ ch : ZMod p × G₁, resultOf τ = some ch ∧
            tSdhCondition (p := p) (g₁ := g₁) (τ, ch.1, ch.2))
        | sampleNonzeroZMod (p := p)] := by
    apply probEvent_ext
    intro τ _
    simp only [Function.comp_apply]
    constructor
    · rintro ⟨t, ht, hcond⟩
      rcases hopt : resultOf τ with _ | ch
      · rw [hopt] at ht; simp at ht
      · rw [hopt] at ht
        simp only [Option.map_some, Option.some.injEq] at ht
        exact ⟨ch, rfl, ht ▸ hcond⟩
    · rintro ⟨ch, hch, hcond⟩
      exact ⟨(τ, ch.1, ch.2), by rw [hch]; rfl, hcond⟩
  rw [hev, probEvent_sampleNonzeroZMod]
  rfl

end Ggm.ProbThreading
