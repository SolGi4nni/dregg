/-
# Cashing the optimizer's cost certificate at the DESCRIPTOR

STATE THE SUBSTRATE OUT LOUD: this is Lean-authored AIR.  Every object here is
the descriptor emitted by `TypedLinearPredicateDescriptorIR2.descriptor` (and its
nonlinear twin `QuadProgram.descriptor`); nothing is hand-written in Rust.

## The gap this closes

`DirectLogicOptimizerCertificate` already proves a `∀`-statement about the
deterministic peephole optimizer:

* `optimize_holds_iff`        — the rewrite preserves the source predicate;
* `optimize_cost_nonincrease` — all five `BackendCost` coordinates of the
  rewritten formula are `≤` those of the original.

`TypedLinearPredicateDescriptorIR2` separately proves the exact closed form of
the emitted descriptor (`descriptor_exact_resources`), and
`DirectLogicBoolGraphDescriptorIR2` proves the two bridges that turn *symbolic*
`BackendCost` coordinates into *emitted* resources
(`witnessCount_eq_graphCost_witnesses`, `emittedMultiplications_eq_graphCost`).

Nothing composed them.  Every concrete cost fact in the peephole tree was a
`#guard`ed integer — compiled `Bool` evaluation, which proves **no** `Prop`.
This file performs the three rewrites and states the composition as theorems.
⚠ It does NOT thereby turn those `#guard`ed integers into theorems: on the two production programs the
optimizer fires nothing, so what lands is a theorem-backed BOUND (§6) plus one strict `∀`-saving (§5):

* `optimize_descriptor_cost_nonincrease` — for EVERY typed-predicate program,
  the optimized descriptor emits no more constraints, no wider trace, and no
  more nonlinear multiplications than the original;
* `optimizeProgram_holds_iff` / `optimized_sound` / `optimized_canonical_iff` —
  and it decides the SAME predicate, so the saving is not bought by breaking the
  circuit (an all-`.bot` "optimizer" would pass a cost bound alone);
* `descriptor_shareAnd_exact_saving` — the certified `factorAnd` rewrite has an
  EXACT symbolic saving at the descriptor: `f.graphCost.equations + 2` fewer
  constraints, `f.graphCost.witnesses + 1` fewer trace columns, and
  `f.graphCost.multiplications + 2` fewer nonlinear multiplications.  This is a
  strict decrease with no `decide` and no kernel reduction of any cost fold.

Both the affine (`Program`) and the bilinear (`QuadProgram`) stacks are covered:
the two bridge lemmas live on `Formula n`, so they are indifferent to whether an
atom residual is an `AffineTerm` or a `QuadTerm`.

## Honest scope

`emittedMultiplications` counts the multiplications of the materialized BOOLEAN
GRAPH only.  Optimizing `source` never touches `atomTerms`, so the atom-link
gates (degree 1 in the affine stack, degree 2 in the bilinear one) are identical
on both sides of every inequality below; the whole delta is in the Boolean graph.
`maxDegree` is likewise unchanged in kind — `descriptor_constraint_low_degree`
already pins every emitted constraint at degree ≤ 2 for both stacks.

Standalone and additive: no existing file is edited, no umbrella import changed.
-/

import Dregg2.Crypto.Arith.FieldDeltaRangePilot

namespace Dregg2.Metatheory.TypedLinearPredicateOptimizerCost

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2
open Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2
  (witnessCount emittedMultiplications witnessCount_eq_graphCost_witnesses
   emittedMultiplications_eq_graphCost)
open Dregg2.Metatheory.DirectLogicOptimizerCertificate
  (optimize optimize_cost_nonincrease optimize_holds_iff)

set_option autoImplicit false

/-! ## 1. Retargeting a program's source, and the optimized program -/

/-- Replace a program's Boolean source, keeping its affine atom registry.  The
registry is what fixes atom SEMANTICS, so every program in this file denotes its
predicate over the same atoms. -/
def withSource {pub sec atoms : Nat} (p : Program pub sec atoms)
    (s : Formula atoms) : Program pub sec atoms :=
  { atomTerms := p.atomTerms, source := s }

@[simp] theorem withSource_source {pub sec atoms : Nat} (p : Program pub sec atoms)
    (s : Formula atoms) : (withSource p s).source = s := rfl

@[simp] theorem withSource_atomTerms {pub sec atoms : Nat} (p : Program pub sec atoms)
    (s : Formula atoms) : (withSource p s).atomTerms = p.atomTerms := rfl

/-- The deterministic, checker-gated optimizer applied to a typed program. -/
def optimizeProgram {pub sec atoms : Nat} (p : Program pub sec atoms) :
    Program pub sec atoms :=
  withSource p (optimize p.source).1

@[simp] theorem optimizeProgram_source {pub sec atoms : Nat} (p : Program pub sec atoms) :
    (optimizeProgram p).source = (optimize p.source).1 := rfl

@[simp] theorem optimizeProgram_atomTerms {pub sec atoms : Nat} (p : Program pub sec atoms) :
    (optimizeProgram p).atomTerms = p.atomTerms := rfl

/-! ## 2. The optimizer decides the SAME predicate -/

/-- The optimized program denotes exactly the original predicate. -/
theorem optimizeProgram_holds_iff {pub sec atoms : Nat} (p : Program pub sec atoms)
    (input : Fin (pub + sec) -> BabyBear) :
    (optimizeProgram p).Holds input <-> p.Holds input :=
  (optimize_holds_iff (p.AtomTruth input) p.source).symm

/-- Arbitrary-trace soundness of the OPTIMIZED descriptor, stated against the
ORIGINAL predicate: a satisfying trace of the cheaper circuit still proves `p`. -/
theorem optimized_sound (hash : List Int -> Int) {pub sec atoms : Nat}
    (p : Program pub sec atoms) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (descriptor (optimizeProgram p)) (fun _ => 0)
      (fun _ => (0, 0)) [] t) :
    p.Holds (rowInput p t) :=
  (optimizeProgram_holds_iff p (rowInput p t)).mp
    (sound hash (optimizeProgram p) t hne hsat)

/-- Exact semantic equivalence of the OPTIMIZED descriptor on its canonical
trace, against the ORIGINAL predicate.  Together with the cost theorem below
this is the statement "cheaper, and the same circuit". -/
theorem optimized_canonical_iff (hash : List Int -> Int) {pub sec atoms : Nat}
    (p : Program pub sec atoms) (input : Fin (pub + sec) -> BabyBear) :
    Satisfied2 hash (descriptor (optimizeProgram p)) (fun _ => 0) (fun _ => (0, 0)) []
        (canonicalTrace (optimizeProgram p) input) <-> p.Holds input :=
  (canonical_iff hash (optimizeProgram p) input).trans
    (optimizeProgram_holds_iff p input)

/-! ## 3. THE COST COROLLARY (affine stack) -/

/-- **The uncashed theorem, cashed.**  For every typed-predicate program, the
optimizer's descriptor emits no more constraints, occupies no wider trace, and
performs no more nonlinear multiplications than the original's — and pins the
same number of public inputs.

Proof = `descriptor_exact_resources` twice (the emitted closed form),
`optimize_cost_nonincrease` (the `∀`-certificate on all five `BackendCost`
coordinates), and the two bridges `witnessCount_eq_graphCost_witnesses` /
`emittedMultiplications_eq_graphCost`. -/
theorem optimize_descriptor_cost_nonincrease {pub sec atoms : Nat}
    (p : Program pub sec atoms) :
    (descriptor (optimizeProgram p)).constraints.length ≤
        (descriptor p).constraints.length /\
      (descriptor (optimizeProgram p)).traceWidth ≤ (descriptor p).traceWidth /\
      emittedMultiplications (optimizeProgram p).source ≤
        emittedMultiplications p.source /\
      (descriptor (optimizeProgram p)).piCount = (descriptor p).piCount := by
  have hcost := optimize_cost_nonincrease p.source
  obtain ⟨hpi, htw, hcl, -⟩ := descriptor_exact_resources p
  obtain ⟨hpi', htw', hcl', -⟩ := descriptor_exact_resources (optimizeProgram p)
  rw [optimizeProgram_source] at htw' hcl'
  rw [witnessCount_eq_graphCost_witnesses] at htw htw'
  have heq := hcost.equations
  have hwit := hcost.witnesses
  have hmul := hcost.multiplications
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcl, hcl']; omega
  · rw [htw, htw']; omega
  · rw [optimizeProgram_source, emittedMultiplications_eq_graphCost,
      emittedMultiplications_eq_graphCost]
    exact hmul
  · rw [hpi, hpi']

/-! ## 4. The EXACT saving of the certified `factorAnd` rewrite

`Rule.factorAnd f g h` rewrites `(f ∧ g) ∨ (f ∧ h)` to `f ∧ (g ∨ h)`.  The
optimizer's checker accepts exactly this step; `DirectLogicOptimization`
computes its symbolic saving exactly.  Here that saving is transported to the
LIVE descriptor, with no `decide` and no kernel reduction of a cost fold. -/

private theorem graphCost_dup {n : Nat} (f g h : Formula n) :
    ((.or (.and f g) (.and f h) : Formula n)).graphCost =
      Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost
        (Dregg2.Metatheory.DirectLogicOptimization.CommonFactor.duplicatedAnd
          f.toGraph g.toGraph h.toGraph) := rfl

private theorem graphCost_shared {n : Nat} (f g h : Formula n) :
    ((.and f (.or g h) : Formula n)).graphCost =
      Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost
        (Dregg2.Metatheory.DirectLogicOptimization.CommonFactor.sharedAnd
          f.toGraph g.toGraph h.toGraph) := rfl

private theorem graphCost_self {n : Nat} (f : Formula n) :
    f.graphCost =
      Dregg2.Metatheory.ArithmetizationCost.BooleanGraph.cost f.toGraph := rfl

/-- Sharing a common conjunct is EXACTLY `f.graphCost.equations + 2` emitted
constraints, `f.graphCost.witnesses + 1` trace columns, and
`f.graphCost.multiplications + 2` nonlinear multiplications cheaper.  Strictly
cheaper for every `f`, since each saving is at least `1`. -/
theorem descriptor_shareAnd_exact_saving {pub sec atoms : Nat}
    (p : Program pub sec atoms) (f g h : Formula atoms) :
    (descriptor (withSource p (.or (.and f g) (.and f h)))).constraints.length =
        (descriptor (withSource p (.and f (.or g h)))).constraints.length +
          (f.graphCost.equations + 2) /\
      (descriptor (withSource p (.or (.and f g) (.and f h)))).traceWidth =
        (descriptor (withSource p (.and f (.or g h)))).traceWidth +
          (f.graphCost.witnesses + 1) /\
      emittedMultiplications ((.or (.and f g) (.and f h)) : Formula atoms) =
        emittedMultiplications ((.and f (.or g h)) : Formula atoms) +
          (f.graphCost.multiplications + 2) := by
  obtain ⟨he, hm, hw⟩ :=
    Dregg2.Metatheory.DirectLogicOptimization.CommonFactor.sharedAnd_exact_saving
      f.toGraph g.toGraph h.toGraph
  rw [← graphCost_dup f g h, ← graphCost_shared f g h, ← graphCost_self f] at he hm hw
  obtain ⟨-, htwD, hclD, -⟩ :=
    descriptor_exact_resources (withSource p ((.or (.and f g) (.and f h)) : Formula atoms))
  obtain ⟨-, htwS, hclS, -⟩ :=
    descriptor_exact_resources (withSource p ((.and f (.or g h)) : Formula atoms))
  rw [withSource_source] at htwD hclD htwS hclS
  rw [witnessCount_eq_graphCost_witnesses] at htwD htwS
  refine ⟨?_, ?_, ?_⟩
  · rw [hclD, hclS]; omega
  · rw [htwD, htwS]; omega
  · rw [emittedMultiplications_eq_graphCost, emittedMultiplications_eq_graphCost]
    exact hm

/-- …and the cheaper descriptor decides the same predicate, so the saving above
is real rather than an artifact of weakening the circuit. -/
theorem shareAnd_holds_iff {pub sec atoms : Nat} (p : Program pub sec atoms)
    (f g h : Formula atoms) (input : Fin (pub + sec) -> BabyBear) :
    (withSource p ((.and f (.or g h)) : Formula atoms)).Holds input <->
      (withSource p ((.or (.and f g) (.and f h)) : Formula atoms)).Holds input :=
  (Dregg2.Metatheory.DirectLogicOptimizerCertificate.Rule.sound
    (p.AtomTruth input) (.factorAnd f g h) trivial).symm

/-! ## 5. THE COST COROLLARY (bilinear `QuadProgram` stack)

The Quad side DOES have the analogous bridges: `QuadProgram.descriptor_exact_resources`
states the same closed form, and both bridge lemmas are `Formula n`-level, so they
apply verbatim.  What the Quad side lacks (and this file does NOT claim) is a
canonical-trace completeness theorem — `canonicalTrace`/`canonical_iff` exist only
for the affine stack — so the Quad payoff is cost + soundness, not `↔`. -/

def quadWithSource {pub sec atoms : Nat} (p : QuadProgram pub sec atoms)
    (s : Formula atoms) : QuadProgram pub sec atoms :=
  { atomTerms := p.atomTerms, source := s }

def optimizeQuadProgram {pub sec atoms : Nat} (p : QuadProgram pub sec atoms) :
    QuadProgram pub sec atoms :=
  quadWithSource p (optimize p.source).1

@[simp] theorem optimizeQuadProgram_source {pub sec atoms : Nat}
    (p : QuadProgram pub sec atoms) :
    (optimizeQuadProgram p).source = (optimize p.source).1 := rfl

theorem optimizeQuadProgram_holds_iff {pub sec atoms : Nat}
    (p : QuadProgram pub sec atoms) (input : Fin (pub + sec) -> BabyBear) :
    (optimizeQuadProgram p).Holds input <-> p.Holds input :=
  (optimize_holds_iff (p.AtomTruth input) p.source).symm

theorem optimized_quad_sound (hash : List Int -> Int) {pub sec atoms : Nat}
    (p : QuadProgram pub sec atoms) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (QuadProgram.descriptor (optimizeQuadProgram p))
      (fun _ => 0) (fun _ => (0, 0)) [] t) :
    p.Holds (QuadProgram.rowInput p t) :=
  (optimizeQuadProgram_holds_iff p (QuadProgram.rowInput p t)).mp
    (QuadProgram.sound hash (optimizeQuadProgram p) t hne hsat)

/-- The same cost corollary for the bilinear stack.  The atom links are degree-2
`QuadTerm` residuals and are IDENTICAL on both sides (the registry is untouched);
the entire delta is the Boolean graph. -/
theorem optimize_quad_descriptor_cost_nonincrease {pub sec atoms : Nat}
    (p : QuadProgram pub sec atoms) :
    (QuadProgram.descriptor (optimizeQuadProgram p)).constraints.length ≤
        (QuadProgram.descriptor p).constraints.length /\
      (QuadProgram.descriptor (optimizeQuadProgram p)).traceWidth ≤
        (QuadProgram.descriptor p).traceWidth /\
      emittedMultiplications (optimizeQuadProgram p).source ≤
        emittedMultiplications p.source /\
      (QuadProgram.descriptor (optimizeQuadProgram p)).piCount =
        (QuadProgram.descriptor p).piCount := by
  have hcost := optimize_cost_nonincrease p.source
  obtain ⟨hpi, htw, hcl⟩ := QuadProgram.descriptor_exact_resources p
  obtain ⟨hpi', htw', hcl'⟩ :=
    QuadProgram.descriptor_exact_resources (optimizeQuadProgram p)
  rw [optimizeQuadProgram_source] at htw' hcl'
  rw [witnessCount_eq_graphCost_witnesses] at htw htw'
  have heq := hcost.equations
  have hwit := hcost.witnesses
  have hmul := hcost.multiplications
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hcl, hcl']; omega
  · rw [htw, htw']; omega
  · rw [optimizeQuadProgram_source, emittedMultiplications_eq_graphCost,
      emittedMultiplications_eq_graphCost]
    exact hmul
  · rw [hpi, hpi']

/-! ## 6. PAYOFF — theorem-backed cost BOUNDS at the live programs

⚠ READ THE SCOPE (an adversarial verify corrected an earlier overstatement here): NO previously
`#guard`ed cost fact becomes a theorem below. The deterministic proposer fires NO rewrite on either
production source — `#guard (optimize prog.source).1 == prog.source` passes for BOTH
`FieldDeltaRangePilot.prog` and `QuantifiedAbsence.program` — so at those two programs the `∀`-corollary's
`≤` is attained with EQUALITY. What the instantiations below give is a THEOREM-BACKED UPPER BOUND in the
closed form (≤ pub + atoms + graphCost.equations + 1, etc.), not a demonstrated shrink.

The genuinely STRICT result is `descriptor_shareAnd_exact_saving` (§5): a `∀`-theorem with a symbolic
magnitude, whose saving constant is load-bearing (a mutation canary confirms `+2 → +3` breaks the proof).
Making the pilot actually shrink needs a proposer rule matching its `⋀_j (b_j=0 ∨ b_j=1)` shape — then
this same corollary converts it into a descriptor shrink for free. -/

namespace Pilot

open Dregg2.Crypto.Arith.FieldDeltaRangePilot (prog)

/-- Instance of the `∀`-corollary at the live `field-delta-result-range` pilot
(`Program 3 30 62`, the FIRST descriptor re-derived through the fragment). -/
theorem pilot_optimize_cost_nonincrease :
    (descriptor (optimizeProgram prog)).constraints.length ≤
        (descriptor prog).constraints.length /\
      (descriptor (optimizeProgram prog)).traceWidth ≤ (descriptor prog).traceWidth /\
      emittedMultiplications (optimizeProgram prog).source ≤
        emittedMultiplications prog.source /\
      (descriptor (optimizeProgram prog)).piCount = (descriptor prog).piCount :=
  optimize_descriptor_cost_nonincrease prog

/-- The pilot's measured numbers, previously only `#guard`ed, now bound the
OPTIMIZED descriptor as a THEOREM via the proven closed form:
`traceWidth ≤ 62 + (3+30) + witnessCount prog.source` (measured 280) and
`constraints.length ≤ 3 + 62 + prog.source.graphCost.equations + 1`
(measured 374). -/
theorem pilot_optimized_within_closed_form :
    (descriptor (optimizeProgram prog)).constraints.length ≤
        3 + 62 + prog.source.graphCost.equations + 1 /\
      (descriptor (optimizeProgram prog)).traceWidth ≤
        62 + (3 + 30) + witnessCount prog.source /\
      (descriptor (optimizeProgram prog)).piCount = 3 := by
  obtain ⟨hpi, htw, hcl, -⟩ := descriptor_exact_resources prog
  obtain ⟨hle, htwle, -, hpieq⟩ := optimize_descriptor_cost_nonincrease prog
  exact ⟨hle.trans hcl.le, htwle.trans htw.le, hpieq.trans hpi⟩

/-- And the optimized pilot descriptor still decides the pilot predicate. -/
theorem pilot_optimized_canonical_iff (hash : List Int -> Int)
    (input : Fin (3 + 30) -> BabyBear) :
    Satisfied2 hash (descriptor (optimizeProgram prog)) (fun _ => 0) (fun _ => (0, 0)) []
        (canonicalTrace (optimizeProgram prog) input) <-> prog.Holds input :=
  optimized_canonical_iff hash prog input

/-- A STRICT, symbolically-sized saving on the pilot's own 62-atom affine
registry: guarding two branches by the whole pilot predicate and then sharing
that factor removes exactly `prog.source.graphCost.equations + 2` constraints
and `witnessCount prog.source + 1` trace columns.  Measured (`#guard` below):
`308 + 2 = 310` constraints and `185 + 1 = 186` columns. -/
theorem pilot_share_saving (g h : Formula 62) :
    (descriptor (withSource prog (.or (.and prog.source g) (.and prog.source h)))).constraints.length =
        (descriptor (withSource prog (.and prog.source (.or g h)))).constraints.length +
          (prog.source.graphCost.equations + 2) /\
      (descriptor (withSource prog (.or (.and prog.source g) (.and prog.source h)))).traceWidth =
        (descriptor (withSource prog (.and prog.source (.or g h)))).traceWidth +
          (prog.source.graphCost.witnesses + 1) /\
      emittedMultiplications ((.or (.and prog.source g) (.and prog.source h)) : Formula 62) =
        emittedMultiplications ((.and prog.source (.or g h)) : Formula 62) +
          (prog.source.graphCost.multiplications + 2) :=
  descriptor_shareAnd_exact_saving prog prog.source g h

-- MEASUREMENTS (compiled `Bool` evaluation; these prove no `Prop` — the
-- load-bearing statements are the theorems above).
#guard prog.source.graphCost.equations == 308
#guard prog.source.graphCost.witnesses == 185
#guard witnessCount prog.source == 185
-- The pilot source contains no rewrite site the deterministic proposer matches,
-- so `optimize` is the identity here and the bounds above are attained:
#guard (optimize prog.source).1 == prog.source

end Pilot

/-! ## 7. PAYOFF — the bilinear quantified-absence program -/

namespace QuantifiedAbsencePayoff

open Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2.QuantifiedAbsence (program)

/-- Instance of the bilinear cost corollary at the compiled quantified-absence
descriptor (`QuadProgram 8 24 16`, the BabyBear⁴ multiply re-derivation). -/
theorem quantified_absence_optimize_cost_nonincrease :
    (QuadProgram.descriptor (optimizeQuadProgram program)).constraints.length ≤
        (QuadProgram.descriptor program).constraints.length /\
      (QuadProgram.descriptor (optimizeQuadProgram program)).traceWidth ≤
        (QuadProgram.descriptor program).traceWidth /\
      emittedMultiplications (optimizeQuadProgram program).source ≤
        emittedMultiplications program.source /\
      (QuadProgram.descriptor (optimizeQuadProgram program)).piCount =
        (QuadProgram.descriptor program).piCount :=
  optimize_quad_descriptor_cost_nonincrease program

/-- The optimized bilinear descriptor still proves the sixteen limb relations. -/
theorem quantified_absence_optimized_sound (hash : List Int -> Int) (t : VmTrace)
    (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (QuadProgram.descriptor (optimizeQuadProgram program))
      (fun _ => 0) (fun _ => (0, 0)) [] t) :
    program.Holds (QuadProgram.rowInput program t) :=
  optimized_quad_sound hash program t hne hsat

/-- The measured resources of the compiled bilinear descriptor now bound the
OPTIMIZED one as a theorem (measured: `traceWidth 95`, `103 constraints`). -/
theorem quantified_absence_optimized_within_closed_form :
    (QuadProgram.descriptor (optimizeQuadProgram program)).constraints.length ≤
        8 + 16 + program.source.graphCost.equations + 1 /\
      (QuadProgram.descriptor (optimizeQuadProgram program)).traceWidth ≤
        16 + (8 + 24) + witnessCount program.source /\
      (QuadProgram.descriptor (optimizeQuadProgram program)).piCount = 8 := by
  obtain ⟨hpi, htw, hcl⟩ := QuadProgram.descriptor_exact_resources program
  obtain ⟨hle, htwle, -, hpieq⟩ :=
    optimize_quad_descriptor_cost_nonincrease program
  exact ⟨hle.trans hcl.le, htwle.trans htw.le, hpieq.trans hpi⟩

#guard program.source.graphCost.equations == 78
#guard witnessCount program.source == 47
#guard (optimize program.source).1 == program.source

end QuantifiedAbsencePayoff

#assert_all_clean [
  withSource_source,
  withSource_atomTerms,
  optimizeProgram_source,
  optimizeProgram_atomTerms,
  optimizeProgram_holds_iff,
  optimized_sound,
  optimized_canonical_iff,
  optimize_descriptor_cost_nonincrease,
  descriptor_shareAnd_exact_saving,
  shareAnd_holds_iff,
  optimizeQuadProgram_holds_iff,
  optimized_quad_sound,
  optimize_quad_descriptor_cost_nonincrease,
  Pilot.pilot_optimize_cost_nonincrease,
  Pilot.pilot_optimized_within_closed_form,
  Pilot.pilot_optimized_canonical_iff,
  Pilot.pilot_share_saving,
  QuantifiedAbsencePayoff.quantified_absence_optimize_cost_nonincrease,
  QuantifiedAbsencePayoff.quantified_absence_optimized_sound,
  QuantifiedAbsencePayoff.quantified_absence_optimized_within_closed_form
]

end Dregg2.Metatheory.TypedLinearPredicateOptimizerCost
