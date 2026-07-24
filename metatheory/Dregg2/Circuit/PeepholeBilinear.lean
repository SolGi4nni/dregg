/-
# Dregg2.Circuit.PeepholeBilinear — the certified batch peephole, carried onto the BILINEAR fragment.

STATE THE SUBSTRATE OUT LOUD: this is Lean-authored AIR.  Nothing here hand-writes a constraint.  The
optimizer READS the constraint list that the `QuadProgram` compiler EMITTED for the quantified-absence
descriptor (`Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2.QuantifiedAbsence.program`) and drops
the redundant ones; the security argument is `PeepholeGeneralBatch`'s machine-checked polynomial
identity over the emitted gate bodies, instantiated at this descriptor.

## What this extends

`PeepholeGeneralBatch.generalBatchPeephole` is a program-INDEPENDENT (`∀ d`) pass that elides every
materialized zero-test's REDUNDANT booleanity gate `out·(out−1)=0`, because that gate is a field
consequence of the SAME node's two companion gates
    out·(out−1)  =  out·(x·inv + out − 1)  −  inv·(x·out).
Its soundness (`general_batch_preservation`) is proven over EVERY descriptor, in BOTH directions, with
the identity trace map.  The affine field-delta lane already fired it (62 sites on that pilot).

This file carries that SAME proven pass onto the BILINEAR fragment: the quantified-absence
`QuadProgram`, whose atoms include the four degree-2 `prodAtom*` limbs of the BabyBear⁴ multiply.  The
peephole rules are shape-determined, so the presence of degree-2 atom-LINK gates changes nothing about
the recognizer — a materialized `zeroTest` over a bilinear atom residual emits the identical
booleanity/product/inverse triple as one over an affine residual.  The 16 atom zero-tests are all
recognized; their bit gates are elided; the four bilinear MULTIPLY gates themselves are untouched.

## The measured result (vs the hand AIR's 28 columns / 20 constraints)

The compiled `QuadProgram` descriptor for `QuantifiedAbsence.program`:
  `piCount 8`, `traceWidth 95`, `103 constraints`, of which `78` are the materialized Boolean graph.
After the certified batch peephole (16 recognized zero-tests ⇒ 16 redundant booleanity gates elided):
  `103 → 87 constraints`; `78 → 62` nonlinear graph multiplications; `traceWidth 95` unchanged.

So the proven, program-independent, both-directions optimization removes `16/103 ≈ 15.5%` of the
constraints.  It does NOT reach parity with the hand descriptor (`20` constraints), and it CANNOT, by
this rule alone — see the residual below.

## Named residual (no `sorry`, no stand-in) — WHY parity is not reachable here

Two distinct populations remain, and they are NOT the same kind of thing:

1. THE IRREDUCIBLE BILINEAR CORE.  The four `prodAtom*` atom-link gates ARE the extension-field
   multiply: term-for-term the `w_j·d_k` products of `ExtElem::mul` mod (X⁴−11), 16 scalar
   multiplications across the four degree-2 limbs.  These compute the value; no peephole can elide
   them.  With the 12 affine atom links (C1 `diff`, C3 `sum`, boundary), the 8 public pins and the 1
   accept gate, this is the genuine floor of the computation — it is what the hand AIR spends its 20
   constraints on.

2. THE GENERALITY OVERHEAD (the graph the hand AIR never builds).  The general front end MATERIALIZES a
   Boolean decision graph — a `zeroTest` (with an inverse witness) per atom, and a left-folded and-tree
   of 15 `and` nodes — so that "the predicate holds" becomes a single `output = 1` wire.  The batch
   peephole removes the REDUNDANT part of that graph (the 16 booleanity gates) but not the graph
   itself: the 16 surviving zero-test product+inverse gates (32) and the 15 and-node gates (30, half of
   them and-output booleanity) stay.  Collapsing THOSE to the hand's flat conjunction is
   program-DEPENDENT — it is sound only because THIS source is a pure conjunction whose accept path
   forces every atom's residual to zero, so each `zeroTest`+bit could be replaced by a direct
   `residual = 0` assertion.  That is the accept-reachability FRONTIER SCAN (sibling lane
   `PeepholeFrontierScan`, not yet built), NOT the program-independent redundant-elision.  It is
   deliberately NOT asserted here: firing it would need this descriptor's own accept-forces-out=1
   argument, which the general batch pass does not carry.

A measured 103→87 reduction with the irreducible 16-multiply bilinear core named, and the remaining gap
attributed to the (program-dependent) Boolean-graph materialization rather than to the computation, is
the honest result.

Standalone and additive: imports the certified batch pass and the bilinear compiler; changes neither.
-/
import Dregg2.Circuit.PeepholeGeneralBatch
import Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2

namespace Dregg2.Circuit.PeepholeBilinear

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.PassiveDescriptorOptimization
open Dregg2.Circuit.PeepholeGeneralBatch
open Dregg2.Metatheory.DirectLogicBoolGraphDescriptorIR2 (gate exprDegree)
open Dregg2.Metatheory.TypedLinearPredicateDescriptorIR2

set_option autoImplicit false

/-! ## 1. The bilinear descriptor under optimization, and its peepholed form. -/

/-- The compiled nonlinear `QuadProgram` descriptor for quantified-absence: the same object
`QuantifiedAbsence.program_sound` certifies, with the four bilinear `prodAtom*` limbs.  Computable —
the descriptor emitter is pure list/`QuadTerm` construction, so the `#guard` measurements evaluate. -/
def qaDesc : EffectVmDescriptor2 :=
  QuadProgram.descriptor QuantifiedAbsence.program

/-- The certified program-independent batch peephole APPLIED to the bilinear descriptor. -/
def qaPeeled : EffectVmDescriptor2 := generalBatchPeephole qaDesc

/-! ## 2. Soundness — the SAME `∀ d` certificate, instantiated at the bilinear descriptor.

No new soundness argument: `general_batch_preservation` is proved over every descriptor, so it applies
verbatim to `qaDesc`, whose atom links happen to be degree-2.  The batch pass drops only booleanity
gates that are field consequences of surviving companion gates; the bilinear multiply gates are never
among the dropped set. -/

/-- Both legs, at the bilinear descriptor: the peephole is a genuine equisatisfiability-preserving
passive pass on `qaDesc`. -/
theorem qa_batch_preservation :
    SatisfiabilityPreservation (generalBatchPass qaDesc) :=
  general_batch_preservation qaDesc

/-- The equisatisfiability corollary: `qaDesc` has a satisfying witness iff its peepholed form does. -/
theorem qa_batch_satisfiable_iff
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) :
    (∃ s, Satisfied2 hash qaDesc minit mfin maddrs s) ↔
      (∃ u, Satisfied2 hash qaPeeled minit mfin maddrs u) :=
  general_batch_satisfiable_iff qaDesc hash minit mfin maddrs

/-- The public ABI is untouched by the peephole (piCount preserved). -/
theorem qa_peeled_piCount : qaPeeled.piCount = qaDesc.piCount :=
  piCount_general qaDesc

/-- The low-degree envelope is INHERITED: every surviving constraint of the peepholed bilinear
descriptor is still a linear public pin or a degree-≤2 window gate — the pass only DROPS constraints,
so it cannot raise any degree, and the bilinear multiply gates stay at degree 2. -/
theorem qa_peeled_low_degree (c : VmConstraint2) (hc : c ∈ qaPeeled.constraints) :
    (∃ row col pi, c = .base (.piBinding row col pi)) ∨
      (∃ body, c = gate body ∧ exprDegree body ≤ 2) := by
  have hmem : c ∈ qaDesc.constraints :=
    List.mem_of_mem_filter (by simpa [qaPeeled, generalBatchPeephole] using hc)
  exact QuadProgram.descriptor_constraint_low_degree QuantifiedAbsence.program c hmem

/-! ## 3. MEASURE — concrete generated resources (compiled `Bool`, no kernel `decide`).

These are MEASUREMENTS, not load-bearing proofs.  The load-bearing statements are
`qa_batch_preservation` (soundness, both directions) and `qa_peeled_low_degree` (degree envelope),
which are symbolic and program-independent at their core.  The integers below are read off by COMPILED
`==` (`#guard`), which does not force any kernel whnf reduction of the Boolean-graph fold. -/

-- Baseline (the hand descriptor, for reference, is traceWidth 28 / 20 constraints / piCount 8):
#guard qaDesc.piCount == 8
#guard qaDesc.traceWidth == 95
#guard qaDesc.constraints.length == 103

-- The pass recognizes exactly the 16 atom zero-tests (one redundant booleanity gate each).  This count
-- is ALSO the nonlinear-multiplication reduction: each elided `out·(out−1)` gate is one multiply.
#guard (confirmedOuts qaDesc.constraints).length == 16

-- Post-peephole: 16 redundant booleanity gates elided, 103 → 87.  traceWidth and piCount unchanged.
#guard qaPeeled.constraints.length == 87
#guard qaPeeled.constraints.length + 16 == qaDesc.constraints.length
#guard qaPeeled.traceWidth == 95
#guard qaPeeled.piCount == 8

-- The materialized Boolean graph is 78 of the 103 constraints; the peephole trims 16 of those to 62.
#guard QuantifiedAbsence.program.source.graphCost.equations == 78

#assert_all_clean [
  qa_batch_preservation,
  qa_batch_satisfiable_iff,
  qa_peeled_piCount,
  qa_peeled_low_degree
]

end Dregg2.Circuit.PeepholeBilinear
