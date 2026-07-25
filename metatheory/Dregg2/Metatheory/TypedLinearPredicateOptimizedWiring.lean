/-
# Dregg2.Metatheory.TypedLinearPredicateOptimizedWiring — the certified optimizer, WIRED.

STATE THE SUBSTRATE OUT LOUD: this is Lean-authored AIR. Every constraint discussed here is
emitted by the Lean function `TypedLinearPredicateDescriptorIR2.descriptor`; no Rust hand-writes
any of it, and every theorem below is about that emitted `EffectVmDescriptor2`.

## The gap this closes

`DirectLogicOptimizerCertificate` carries a proof-producing optimizer — `optimize` emits a
checker-gated `Certificate`, and `optimize_holds_iff` / `optimize_cost_nonincrease` prove semantic
preservation and five-coordinate cost nonincrease. `TypedLinearPredicateDescriptorIR2.descriptor`
is the LIVE arithmetizer's target. They were sitting next to each other and `descriptor` NEVER
CALLED `optimize`: the live path emitted UNOPTIMIZED descriptors while the certified optimizer sat
unused beside it.

This module wires them together, ADDITIVELY. `descriptor`'s existing behaviour is untouched (the
peephole recognizers and every downstream module depend on the current lowering geometry); what is
added is `Program.optimized` and the transport of the compiler's OWN guarantees onto it:

* `optimized_holds_iff`  — the optimized program has the same predicate (via `optimize_holds_iff`);
* `optimized_sound`      — a trace of `descriptor p.optimized` proves the ORIGINAL `p.Holds`;
* `optimized_public_sound`, `optimized_canonical_iff` — the same for the other two guarantees;
* `optimized_spec_sound` / `optimized_spec_exact` — the arithmetizer's CALLER BRIDGE, written
  against the unoptimized program, discharges the optimized descriptor unchanged;
* `optimized_descriptor_cost_le` — the emitted descriptor's `piCount` is unchanged and its
  `traceWidth`, `constraints.length` and multiplication count are ≤ the unoptimized ones.

The atom registry is what makes this compose at all: `optimize` rewrites only the Boolean AST over
`Fin atoms`, never renumbering or introducing atoms (every `Rule` payload is built from existing
subformulas, and `Formula.atom a` is a fixed point of `optimize`). So `p.optimized.atomTerms` is
`p.atomTerms` by `rfl` and `p.optimized.AtomTruth = p.AtomTruth` definitionally — no registry
remapping is needed, and none is smuggled in.

## HONEST RESOLUTION CAP — inherited, not repaired here

`Satisfied2` is the descriptor-level constraint-satisfaction predicate. `optimized_sound` says "any
satisfying trace of the OPTIMIZED descriptor witnesses the original program's predicate"; it does
NOT say the deployed prover/verifier is sound, and it inherits the undischarged FRI/STARK floor and
the witness-generator perimeter exactly as every other descriptor-level theorem in this tree does.

Standalone and additive: imports the fragment and the pilot, changes nothing in either.
-/
import Dregg2.Crypto.Arith.FieldDeltaRangePilot

namespace Dregg2.Metatheory.TypedLinearPredicateOptimizedWiring

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Metatheory.DirectLogicOptimizerCertificate
open Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2
  (witnessCount witnessCount_eq_graphCost_witnesses fieldAssignment
   emittedMultiplications emittedMultiplications_eq_graphCost)
open Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2

set_option autoImplicit false

-- NOTE on naming: both `TypedLinearPredicateDescriptorIR2` and `DirectLogicOptimizerCertificate`
-- are opened, and both export `Formula` (the former as an `abbrev` for the latter). The bare name
-- is therefore ambiguous in this file and is never written; qualified paths are used instead.

variable {pub sec atoms : Nat}

/-! ## 1. The optimized program — one field rewritten by the certified optimizer. -/

/-- Run the checker-gated optimizer on the program's Boolean source, keeping the affine atom
registry byte-for-byte. Defined into the compiler's own namespace so it reads as `p.optimized` at
every call site. -/
def _root_.Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2.Program.optimized
    {pub sec atoms : Nat} (p : Program pub sec atoms) : Program pub sec atoms :=
  { p with source := (optimize p.source).1 }

@[simp] theorem optimized_atomTerms (p : Program pub sec atoms) :
    p.optimized.atomTerms = p.atomTerms := rfl

@[simp] theorem optimized_source (p : Program pub sec atoms) :
    p.optimized.source = (optimize p.source).1 := rfl

/-- The registry is genuinely shared: atom semantics is unchanged, definitionally. -/
theorem optimized_atomTruth (p : Program pub sec atoms)
    (input : Fin (pub + sec) → BabyBear) :
    p.optimized.AtomTruth input = p.AtomTruth input := rfl

/-! ## 2. Semantic preservation, lifted from the Formula level to the typed Program level. -/

/-- **Deliverable (2).** The optimized program decides exactly the same predicate. This is
`optimize_holds_iff` transported across the atom registry, which the optimizer leaves fixed. -/
theorem optimized_holds_iff (p : Program pub sec atoms)
    (input : Fin (pub + sec) → BabyBear) :
    p.optimized.Holds input ↔ p.Holds input :=
  (optimize_holds_iff (p.AtomTruth input) p.source).symm

theorem optimized_publicHolds_iff (p : Program pub sec atoms)
    (publicInput : Fin pub → BabyBear) :
    p.optimized.PublicHolds publicInput ↔ p.PublicHolds publicInput := by
  constructor
  · rintro ⟨input, hpin, hholds⟩
    exact ⟨input, hpin, (optimized_holds_iff p input).mp hholds⟩
  · rintro ⟨input, hpin, hholds⟩
    exact ⟨input, hpin, (optimized_holds_iff p input).mpr hholds⟩

/-! ## 3. Transport of the three live guarantees onto the OPTIMIZED descriptor.

Each theorem's descriptor is `descriptor p.optimized` while its conclusion is about the ORIGINAL
program `p`. That asymmetry is the whole content: it is what lets a caller emit the cheaper
descriptor and keep the specification it already wrote. -/

/-- **Deliverable (3a): `sound`.** Any nonempty trace satisfying the descriptor emitted from the
OPTIMIZED program proves the ORIGINAL program's predicate on the descriptor's own typed row-input
columns. -/
theorem optimized_sound (hash : List Int → Int) (p : Program pub sec atoms) (t : VmTrace)
    (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (descriptor p.optimized) (fun _ => 0) (fun _ => (0, 0)) [] t) :
    p.Holds (rowInput p t) := by
  have h := sound hash p.optimized t hne hsat
  have hrow : rowInput p.optimized t = rowInput p t := rfl
  rw [hrow] at h
  exact (optimized_holds_iff p (rowInput p t)).mp h

/-- **Deliverable (3b): `public_sound`.** Statement soundness survives the rewrite: the public
prefix is verifier-bound and the secret suffix is existentially witnessed, for the ORIGINAL
program. -/
theorem optimized_public_sound (hash : List Int → Int) (p : Program pub sec atoms) (t : VmTrace)
    (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (descriptor p.optimized) (fun _ => 0) (fun _ => (0, 0)) [] t) :
    p.PublicHolds (fun i => fieldAssignment t.pub i.val) :=
  (optimized_publicHolds_iff p _).mp (public_sound hash p.optimized t hne hsat)

/-- **Deliverable (3c): `canonical_iff`.** Exact semantics on the optimized compiler's canonical
trace, stated against the ORIGINAL program's predicate — soundness AND constructive completeness. -/
theorem optimized_canonical_iff (hash : List Int → Int) (p : Program pub sec atoms)
    (input : Fin (pub + sec) → BabyBear) :
    Satisfied2 hash (descriptor p.optimized) (fun _ => 0) (fun _ => (0, 0)) []
        (canonicalTrace p.optimized input) ↔ p.Holds input :=
  (canonical_iff hash p.optimized input).trans (optimized_holds_iff p input)

/-- The payoff for `#arithmetizeTypedRefinement` callers: the program-level bridge they already
wrote for `p` discharges the OPTIMIZED descriptor with no change. The bridge mentions no
descriptor, no trace and no felts, so it cannot notice the rewrite. -/
theorem optimized_spec_sound (hash : List Int → Int) (p : Program pub sec atoms)
    (Spec : (Fin (pub + sec) → BabyBear) → Prop)
    (bridge : ∀ input, p.Holds input ↔ Spec input)
    (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash (descriptor p.optimized) (fun _ => 0) (fun _ => (0, 0)) [] t) :
    Spec (rowInput p t) :=
  (bridge (rowInput p t)).mp (optimized_sound hash p t hne hsat)

theorem optimized_spec_exact (hash : List Int → Int) (p : Program pub sec atoms)
    (Spec : (Fin (pub + sec) → BabyBear) → Prop)
    (bridge : ∀ input, p.Holds input ↔ Spec input)
    (input : Fin (pub + sec) → BabyBear) :
    Satisfied2 hash (descriptor p.optimized) (fun _ => 0) (fun _ => (0, 0)) []
        (canonicalTrace p.optimized input) ↔ Spec input :=
  (optimized_canonical_iff hash p input).trans (bridge input)

/-! ## 4. Cost: the optimizer's five-coordinate guarantee, read on the EMITTED descriptor. -/

/-- The Formula-level guarantee, at the Program level. -/
theorem optimized_costLE (p : Program pub sec atoms) :
    Dregg2.Metatheory.DirectLogicOptimizerCertificate.Formula.CostLE
      p.optimized.source p.source :=
  optimize_cost_nonincrease p.source

/-- **Deliverable (4), the symbolic half.** The optimized descriptor pins the SAME number of public
inputs and is no larger in any emitted resource: trace columns, constraint equations, or nonlinear
multiplications. Proven for EVERY program from `descriptor_exact_resources` (the compiler's closed
form) composed with `optimize_cost_nonincrease` — no evaluation, no `decide`. -/
theorem optimized_descriptor_cost_le (p : Program pub sec atoms) :
    (descriptor p.optimized).piCount = (descriptor p).piCount ∧
    (descriptor p.optimized).traceWidth ≤ (descriptor p).traceWidth ∧
    (descriptor p.optimized).constraints.length ≤ (descriptor p).constraints.length ∧
    (layoutOf p.optimized).nonlinearMultiplications ≤
      (layoutOf p).nonlinearMultiplications := by
  obtain ⟨hpi, htw, hcon, -⟩ := descriptor_exact_resources p
  obtain ⟨hpi', htw', hcon', -⟩ := descriptor_exact_resources p.optimized
  have hcost := optimized_costLE p
  have hwit : witnessCount p.optimized.source ≤ witnessCount p.source := by
    rw [witnessCount_eq_graphCost_witnesses, witnessCount_eq_graphCost_witnesses]
    exact hcost.witnesses
  have hmul : (layoutOf p.optimized).nonlinearMultiplications =
      p.optimized.source.graphCost.multiplications :=
    emittedMultiplications_eq_graphCost p.optimized.source
  have hmul' : (layoutOf p).nonlinearMultiplications =
      p.source.graphCost.multiplications :=
    emittedMultiplications_eq_graphCost p.source
  refine ⟨by rw [hpi, hpi'], ?_, ?_, ?_⟩
  · rw [htw, htw']
    omega
  · rw [hcon, hcon']
    have := hcost.equations
    omega
  · rw [hmul, hmul']
    exact hcost.multiplications

/-! ## 5. Reusable `Prop` combinators, in the shape `ArithmetizeTypedPredicate`'s `Live*` bundle
uses, so a generator can emit these theorems per program. Each one names BOTH `p.optimized` (in the
descriptor) and `p` (in the conclusion); neither is `P → P`. -/

/-- The headline: the descriptor emitted from the OPTIMIZED program refines the ORIGINAL program's
predicate on arbitrary nonempty traces. -/
def LiveOptimizedRefines (p : Program pub sec atoms) : Prop :=
  ∀ (hash : List Int → Int) (t : VmTrace), t.rows ≠ [] →
    Satisfied2 hash (descriptor p.optimized) (fun _ => 0) (fun _ => (0, 0)) [] t →
      p.Holds (rowInput p t)

theorem liveOptimizedRefinesOf (p : Program pub sec atoms) : LiveOptimizedRefines p :=
  fun hash t hne hsat => optimized_sound hash p t hne hsat

def LiveOptimizedCanonicalIff (p : Program pub sec atoms) : Prop :=
  ∀ (hash : List Int → Int) (input : Fin (pub + sec) → BabyBear),
    Satisfied2 hash (descriptor p.optimized) (fun _ => 0) (fun _ => (0, 0)) []
        (canonicalTrace p.optimized input) ↔ p.Holds input

theorem liveOptimizedCanonicalIffOf (p : Program pub sec atoms) :
    LiveOptimizedCanonicalIff p :=
  fun hash input => optimized_canonical_iff hash p input

def LiveOptimizedCostLE (p : Program pub sec atoms) : Prop :=
  (descriptor p.optimized).piCount = (descriptor p).piCount ∧
  (descriptor p.optimized).traceWidth ≤ (descriptor p).traceWidth ∧
  (descriptor p.optimized).constraints.length ≤ (descriptor p).constraints.length ∧
  (layoutOf p.optimized).nonlinearMultiplications ≤ (layoutOf p).nonlinearMultiplications

theorem liveOptimizedCostLEOf (p : Program pub sec atoms) : LiveOptimizedCostLE p :=
  optimized_descriptor_cost_le p

/-! ## 6. THE PILOT — `FieldDeltaRangePilot.prog`, the live 62-atom range-decomposition program.

Two demonstrations, both on the REAL pilot program (`Dregg2.Crypto.Arith.FieldDeltaRangePilot.prog`,
`Program 3 30 62`), not a reconstruction of it. -/

namespace Pilot

open Dregg2.Crypto.Arith.FieldDeltaRangePilot (prog boolAtom)

/-! ### 6a. The pilot itself: the optimized descriptor is real, sound, and no larger. -/

/-- The pilot's OPTIMIZED live descriptor. This is an `EffectVmDescriptor2` produced by the same
`descriptor` function the arithmetizer calls. -/
def pilotOptimizedDescriptor : EffectVmDescriptor2 := descriptor prog.optimized

theorem pilotOptimizedDescriptor_eq :
    pilotOptimizedDescriptor = descriptor prog.optimized := rfl

/-- Arbitrary-trace soundness of the pilot's OPTIMIZED descriptor, against the ORIGINAL pilot
predicate (`new = old + delta`, 30 booleanity bits, `new = Σ 2^j b_j`). -/
theorem pilot_optimized_sound : LiveOptimizedRefines prog := liveOptimizedRefinesOf prog

/-- Exactness on the optimized canonical trace, against the ORIGINAL pilot predicate. -/
theorem pilot_optimized_canonical_iff : LiveOptimizedCanonicalIff prog :=
  liveOptimizedCanonicalIffOf prog

/-- The pilot's optimized descriptor costs no more than the unoptimized one. -/
theorem pilot_optimized_cost_le : LiveOptimizedCostLE prog := liveOptimizedCostLEOf prog

/-- The optimized pilot descriptor's bytes, pinned to `emitVmJson2` of the emitted object. -/
def pilotOptimizedArtifact : Artifact prog.optimized := certify prog.optimized

def pilotOptimizedJson : String := pilotOptimizedArtifact.descriptorBytes

theorem pilotOptimizedJson_exact :
    pilotOptimizedJson = emitVmJson2 (descriptor prog.optimized) :=
  (checkArtifact_spec pilotOptimizedArtifact |>.mp (checkArtifact_certify prog.optimized)).2.2

/- MEASURE — and the honest finding. `optimize` is the IDENTITY on this pilot's source: the source
is a right-nested `andAll` of two atoms and thirty `.or`-of-two-atoms booleanity clauses, so no
`proposeRoot` pattern fires (no `.top`/`.bot` leaves; the only `.and` of two `.or`s is
`boolAtom 28 ∧ boolAtom 29`, whose left-hand atoms differ, so `factorOr` is correctly refused). The
cost bound above therefore holds with EQUALITY here — 280 columns and 374 constraints either way.
That is a real result about this pilot, not a win: the pilot's redundancy is in the FRAGMENT's
zero-test lowering (3 constraints + 2 witness columns per affine equality), which is a peephole /
lowering-geometry problem, not a Boolean-algebra one. §6b exercises the case the optimizer is for.

These `#guard`s are COMPILED evaluation and prove no `Prop`; the load-bearing statements are the
theorems above. -/
#guard prog.optimized.source == prog.source
#guard pilotOptimizedDescriptor.piCount == 3
#guard pilotOptimizedDescriptor.traceWidth == 280
#guard pilotOptimizedDescriptor.constraints.length == 374

/-! ### 6b. The case the optimizer exists for — a DUPLICATING lowering of the same pilot.

A front end that lowers `A ∧ (B ∨ C)` by distributing (which naive DNF-ward lowerings do) emits
`(A ∧ B) ∨ (A ∧ C)` — duplicating the ENTIRE graph of `A`. Here `A` is the pilot's whole
range-decomposition source and `B`, `C` are two of its booleanity clauses. This is exactly
`Formula.duplicatedAndMany`, and the wired optimizer recovers `Formula.sharedAndMany`. -/

/-- The duplicating lowering, over the pilot's OWN atom registry. -/
def duplicatedSource :=
  Dregg2.Metatheory.DirectLogicOptimizerCertificate.Formula.duplicatedAndMany
    prog.source [boolAtom 0, boolAtom 1]

/-- The same 62-atom registry, the duplicating source. -/
def duplicatedProgram : Program 3 30 62 := { prog with source := duplicatedSource }

/-- The LIVE descriptor emitted from the duplicating program, unoptimized. -/
def duplicatedDescriptor : EffectVmDescriptor2 := descriptor duplicatedProgram

/-- The LIVE descriptor emitted from the OPTIMIZED duplicating program. -/
def duplicatedOptimizedDescriptor : EffectVmDescriptor2 := descriptor duplicatedProgram.optimized

theorem duplicatedOptimizedDescriptor_eq :
    duplicatedOptimizedDescriptor = descriptor duplicatedProgram.optimized := rfl

/-- **Deliverable (4), on a real emitted descriptor.** Every nonempty trace satisfying the OPTIMIZED
descriptor proves the ORIGINAL duplicating program's predicate. -/
theorem duplicated_optimized_sound : LiveOptimizedRefines duplicatedProgram :=
  liveOptimizedRefinesOf duplicatedProgram

theorem duplicated_optimized_canonical_iff : LiveOptimizedCanonicalIff duplicatedProgram :=
  liveOptimizedCanonicalIffOf duplicatedProgram

/-- ...and it costs no more. (The MEASURED numbers below show the inequality is strict here:
704 → 394 constraints, 478 → 292 trace columns, 638 → 328 multiplications.) -/
theorem duplicated_optimized_cost_le : LiveOptimizedCostLE duplicatedProgram :=
  liveOptimizedCostLEOf duplicatedProgram

def duplicatedOptimizedArtifact : Artifact duplicatedProgram.optimized :=
  certify duplicatedProgram.optimized

def duplicatedOptimizedJson : String := duplicatedOptimizedArtifact.descriptorBytes

theorem duplicatedOptimizedJson_exact :
    duplicatedOptimizedJson = emitVmJson2 (descriptor duplicatedProgram.optimized) :=
  (checkArtifact_spec duplicatedOptimizedArtifact |>.mp
    (checkArtifact_certify duplicatedProgram.optimized)).2.2

/- MEASURE — the strict win on the LIVE emitted descriptors. Compiled evaluation, no kernel
reduction, proves no `Prop`; `duplicated_optimized_cost_le` is the proven (symbolic) statement. The
optimizer's own certificate checker accepts the rewrite, and the result is exactly the shared
form. -/
-- NON-VACUITY, armed at build time: the wiring is NOT the identity here. If `Program.optimized`
-- ever degenerated to `p` (making `optimized_holds_iff` a `P ↔ P` and every transport hollow),
-- this guard would go RED.
#guard duplicatedProgram.optimized.source != duplicatedProgram.source
#guard duplicatedDescriptor.constraints.length != duplicatedOptimizedDescriptor.constraints.length
#guard (optimize duplicatedSource).2.check
#guard (optimize duplicatedSource).1 ==
  Dregg2.Metatheory.DirectLogicOptimizerCertificate.Formula.sharedAndMany
    prog.source [boolAtom 0, boolAtom 1]
#guard duplicatedDescriptor.traceWidth == 478
#guard duplicatedDescriptor.constraints.length == 704
#guard duplicatedOptimizedDescriptor.traceWidth == 292
#guard duplicatedOptimizedDescriptor.constraints.length == 394
#guard duplicatedDescriptor.piCount == duplicatedOptimizedDescriptor.piCount
#guard duplicatedSource.graphCost.multiplications == 638
#guard ((optimize duplicatedSource).1).graphCost.multiplications == 328

end Pilot

/-! Every wiring theorem and every pilot instantiation is kernel-clean. -/
#assert_all_clean [
  optimized_atomTruth,
  optimized_holds_iff,
  optimized_publicHolds_iff,
  optimized_sound,
  optimized_public_sound,
  optimized_canonical_iff,
  optimized_spec_sound,
  optimized_spec_exact,
  optimized_costLE,
  optimized_descriptor_cost_le,
  liveOptimizedRefinesOf,
  liveOptimizedCanonicalIffOf,
  liveOptimizedCostLEOf,
  Pilot.pilotOptimizedDescriptor_eq,
  Pilot.pilot_optimized_sound,
  Pilot.pilot_optimized_canonical_iff,
  Pilot.pilot_optimized_cost_le,
  Pilot.pilotOptimizedJson_exact,
  Pilot.duplicatedOptimizedDescriptor_eq,
  Pilot.duplicated_optimized_sound,
  Pilot.duplicated_optimized_canonical_iff,
  Pilot.duplicated_optimized_cost_le,
  Pilot.duplicatedOptimizedJson_exact
]

/-! ## 7. Canaries — the pilot theorems are LOAD-BEARING on the REAL pilot program and on the
optimizer, not on a local reconstruction of either. -/
#assert_depends_on Pilot.pilot_optimized_sound [Dregg2.Crypto.Arith.FieldDeltaRangePilot.prog]
#assert_depends_on Pilot.duplicated_optimized_sound
  [Dregg2.Metatheory.DirectLogicOptimizerCertificate.optimize]
#assert_depends_on optimized_holds_iff
  [Dregg2.Metatheory.DirectLogicOptimizerCertificate.optimize_holds_iff]

end Dregg2.Metatheory.TypedLinearPredicateOptimizedWiring
