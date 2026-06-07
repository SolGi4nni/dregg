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

-- CLOSED (this wave): `handler_makeSovereign` (handler ALIGNED to the `makeSovereignKernel`
-- commitment-rebind), `handler_receiptArchive` (ALIGNED to the `"lifecycle"` field write), and the
-- queue-allocate `actor ≠ cell` front (handler now stores owner = `actor`, so kernel agreement is
-- UNCONDITIONAL). Their `hole_*` theorems in `HandlerExecutor` are now genuine proofs (no `sorry`),
-- and the `portal_*` re-exports below delegate to them. Removed from the open inventory.
-- CLOSED (this wave): `exercise_inner_turn_witness` — the inner `List FullActionA` emitted fold from
-- the hold post-state now refines `turnSpec` via `ExerciseInnerTurn.exercise_inner_emitted_refines_turnSpec`
-- (sorry-free; the `portal_exercise_inner_turn` re-export below delegates to it). Removed from the
-- open inventory. The two GENUINELY-open R4/queue/spawn fronts remain.
-- CLOSED (P2 canonical-semantics): `exercise_r4_facet_mask` — `execFullA`'s `exerciseA` now ENFORCES
-- the R4 facet mask (`innerFacetsAdmittedA`) and the handler bridge tags each inner with its REAL
-- `requiredFacetA fa` (not blanket `Auth.control`), so the two facet gates are the SAME check. The
-- facet front is discharged (`ExerciseInnerTurn.exercise_r4_facet_mask`, no `sorry`); only the
-- ORTHOGONAL inner-turn fold remains, carried as an explicit `hinner` hypothesis there.
def openFronts : List OpenFront := [
  -- Wave 6/7 queue defer: actor ≠ cell owner alignment — REMAINS for queue ENQUEUE only
  ⟨"queue_enqueue_actor_ne_cell", .w6_queue_defer, none,
    "queueEnqueue when actor ≠ cell — owner metadata mismatch (allocate is now CLOSED)"⟩
  -- Wave 7: spawn/factory metadata beyond born-empty createCell core
  , ⟨"spawn_factory_metadata", .w7_spawn_metadata, some "spawnA",
    "spawnChainA/createCellFromFactoryChainA metadata beyond createCellH core"⟩
]

def countOpenFronts : Nat := openFronts.length

/-! ## §2 — explicit sorry portals (re-exported from keystones; FAIL `#assert_axioms` until proved). -/

section HolePortals

variable {s s' : RecChainedState}

/-- CLOSED: `makeSovereignA` handler ⊑ `execFullA` (commitment-rebind ALIGNED; proved). -/
theorem portal_handler_makeSovereign
    (actor cell : CellId) (hmem : cell ∈ s.kernel.accounts)
    (h : execHandlerOne (.makeSovereignA actor cell) s = some s') :
    ∃ s'', execFullA s (.makeSovereignA actor cell) = some s'' ∧ s''.kernel = s'.kernel :=
  handler_refines_execFullA_makeSovereign s s' actor cell hmem h

/-- CLOSED: `receiptArchiveA` handler ⊑ `execFullA` (`"lifecycle"` field ALIGNED; proved). -/
theorem portal_handler_receiptArchive
    (actor cell : CellId) (hmem : cell ∈ s.kernel.accounts)
    (h : execHandlerOne (.receiptArchiveA actor cell) s = some s') :
    ∃ s'', execFullA s (.receiptArchiveA actor cell) = some s'' ∧ s''.kernel = s'.kernel :=
  handler_refines_execFullA_receiptArchive s s' actor cell hmem h

/-- CLOSED §6.6: queue allocate when `actor ≠ cell` (handler stores owner = `actor`; proved). -/
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

/-- **R4 facet-mask CLOSED** (P2 canonical-semantics): `execFullA`'s `exerciseA` now enforces the same
facet mask the handler bridge tags, so a handler-committed exercise refines `execFullA` on the same
kernel — given the orthogonal inner-turn fold (`hinner`). Delegates to the now-`sorry`-free
`ExerciseInnerTurn.exercise_r4_facet_mask`. -/
theorem portal_exercise_r4_facet_mask (actor target : CellId) (inner : List FullActionA)
    (hinner : ∃ s₁, execInnerA (Dregg2.Exec.HandlerExecutor.exerciseHoldState s actor) inner = some s₁ ∧
        s₁.kernel = s'.kernel)
    (h : execHandlerOne (.exerciseA actor target inner) s = some s') :
    ∃ s'', execFullA s (.exerciseA actor target inner) = some s'' ∧ s''.kernel = s'.kernel :=
  Dregg2.Exec.HandlerExecutor.handler_refines_execFullA_exercise s s' actor target inner hinner h

end HolePortals

-- The frontier has exactly TWO GENUINELY-open handler fronts (drift-free: `countOpenFronts`
-- IS `openFronts.length`, so this catches any future add/remove). Non-vacuity: the registry is
-- non-empty (open work remains) yet bounded. Down from 3 — the R4 facet-mask front is now CLOSED
-- (the facet mask is enforced on `execFullA`, the canonical semantics; `portal_exercise_r4_facet_mask`).
#guard countOpenFronts == openFronts.length
#guard countOpenFronts == 2
#guard ¬ openFronts.isEmpty
-- The closed `exercise_inner_turn_witness` AND `exercise_r4_facet_mask` fronts are no longer listed.
#guard (openFronts.filter (fun f => f.id == "exercise_inner_turn_witness")).isEmpty

end Dregg2.Exec.HandlerOpenFronts