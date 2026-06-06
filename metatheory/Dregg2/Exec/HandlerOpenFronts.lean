/-
# Dregg2.Exec.HandlerOpenFronts — explicit handler-executor open-front registry (Wave 7+).

POLICY: **no lurking holes**. Every unfinished `handler_refines_execFullA_*` / queue-defer front is
named here with an explicit `sorry` theorem (or a tracked `HoleStatus`). Silent strengthening gaps
are forbidden — use these portals instead.

Run `#eval countOpenFronts` after each wave to watch the frontier shrink.
-/
import Dregg2.Exec.HandlerExecutor
import Dregg2.Circuit.Inst.ExerciseInnerTurn

namespace Dregg2.Exec.HandlerOpenFronts

open Dregg2.Exec.HandlerExecutor
open Dregg2.Circuit.Inst.ExerciseInnerTurn
open Dregg2.Exec.TurnExecutorFull

/-! ## §0 — front metadata. -/

inductive HoleWave
  | w6_queue_defer
  | w7_flag_alignment
  | w7_exercise_r4
  | w7_spawn_metadata
  deriving Repr, DecidableEq

structure OpenFront where
  id       : String
  wave     : HoleWave
  action?  : Option String
  note     : String
  deriving Repr

/-! ## §1 — inventory (every named handler gap; shrink this list). -/

def openFronts : List OpenFront := [
  -- Wave 7: flag-write field alignment (handler stateWriteH vs execFullA distinct semantics)
  ⟨"handler_makeSovereign", .w7_flag_alignment, some "makeSovereignA",
    "handler sovereignField vs makeSovereignStep commitment-rebind"⟩
  , ⟨"handler_receiptArchive", .w7_flag_alignment, some "receiptArchiveA",
    "handler receipt_archive vs lifecycleField write"⟩
  -- Wave 7: exercise inner turn + R4 facet mask
  , ⟨"exercise_inner_turn_witness", .w7_exercise_r4, some "exerciseA",
    "inner List FullActionA emitted fold from hold post-state"⟩
  , ⟨"exercise_r4_facet_mask", .w7_exercise_r4, some "exerciseA",
    "facetedOf Auth.control alignment vs execInnerA"⟩
  -- Wave 6/7 queue defer: actor ≠ cell owner alignment
  , ⟨"queue_actor_ne_cell", .w6_queue_defer, none,
    "queueAllocate/queueEnqueue when actor ≠ cell — owner metadata mismatch"⟩
  -- Wave 7: spawn/factory metadata beyond born-empty createCell core
  , ⟨"spawn_factory_metadata", .w7_spawn_metadata, some "spawnA",
    "spawnChainA/createCellFromFactoryChainA metadata beyond createCellH core"⟩
]

def countOpenFronts : Nat := openFronts.length

/-! ## §2 — explicit sorry portals (re-exported from keystones; FAIL `#assert_axioms` until proved). -/

section HolePortals

variable {s s' : RecChainedState}

/-- HOLE: `makeSovereignA` handler ⊑ `execFullA` (field alignment). -/
theorem portal_handler_makeSovereign
    (actor cell : CellId) (hmem : cell ∈ s.kernel.accounts)
    (h : execHandlerOne (.makeSovereignA actor cell) s = some s') :
    ∃ s'', execFullA s (.makeSovereignA actor cell) = some s'' ∧ s''.kernel = s'.kernel :=
  handler_refines_execFullA_makeSovereign s s' actor cell hmem h

/-- HOLE: `receiptArchiveA` handler ⊑ `execFullA` (field alignment). -/
theorem portal_handler_receiptArchive
    (actor cell : CellId) (hmem : cell ∈ s.kernel.accounts)
    (h : execHandlerOne (.receiptArchiveA actor cell) s = some s') :
    ∃ s'', execFullA s (.receiptArchiveA actor cell) = some s'' ∧ s''.kernel = s'.kernel :=
  handler_refines_execFullA_receiptArchive s s' actor cell hmem h

/-- HOLE §6.6: queue allocate when `actor ≠ cell`. -/
theorem portal_queue_actor_ne_cell (id : Nat) (actor cell : CellId) (cap : Nat)
    (hne : actor ≠ cell)
    (h : execHandlerOne (.queueAllocateA id actor cell cap) s = some s') :
    ∃ s'', execFullA s (.queueAllocateA id actor cell cap) = some s'' ∧ s''.kernel = s'.kernel :=
  hole_queue_actor_ne_cell s s' id actor cell cap hne h

/-- HOLE W7: exercise inner emitted fold ⊑ `turnSpec`. -/
theorem portal_exercise_inner_turn
    (lookup : Dregg2.Circuit.TurnEmit.DescriptorLookup)
    (compress : ℤ → ℤ → ℤ) (stepRoot : Dregg2.Circuit.TurnWitness.StepWitness → ℤ)
    (hstep :
      ∀ (sw : Dregg2.Circuit.TurnWitness.StepWitness) (st st' : RecChainedState) (fa : FullActionA),
        Dregg2.Circuit.TurnEmit.stepEmittedSat lookup sw st st' fa →
          Dregg2.Circuit.ActionDispatch.fullActionStep st fa st')
    (holdPost post : RecChainedState) (inner : List FullActionA)
    (w : exerciseInnerTurnWitness lookup compress stepRoot holdPost post inner) :
    Dregg2.Circuit.ActionDispatch.turnSpec holdPost inner post :=
  exercise_inner_emitted_refines_turnSpec lookup compress stepRoot hstep holdPost post inner w

/-- HOLE W7: R4 facet-mask handler vs bare inner executor alignment. -/
theorem portal_exercise_r4_facet_mask (actor target : CellId) (inner : List FullActionA)
    (h : execHandlerOne (.exerciseA actor target inner) s = some s') :
    ∃ s'', execFullA s (.exerciseA actor target inner) = some s'' ∧ s''.kernel = s'.kernel :=
  hole_exercise_r4_facet_mask s s' actor target inner h

end HolePortals

#guard countOpenFronts == 6

end Dregg2.Exec.HandlerOpenFronts