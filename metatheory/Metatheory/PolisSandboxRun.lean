/-
# Metatheory.PolisSandboxRun — gentle governance, proven; and a VISIBLY runnable episode.

Two things that separate a real result from a toy:

1. **Governance is gentle (least-restrictive), proven for ALL moves** — not "we refused the one
   trap." `govStep_admits_benign`: any floor-preserving move is admitted UNCHANGED (honest play —
   going home, cooperating, idling — is never blocked). `govStep_refuses_only_harmful`: every
   refusal is a genuine floor-breaking (domination) move. Together with `sandbox_governed_safe`
   (∀ controller the floor holds), this is the live-world `liberty` guarantee: maximal freedom AND
   safety, no heavy hand.

2. **A runnable episode you can SEE** — `#eval` a mixed episode (honest agent heading home while a
   politician keeps trapping it) under both regimes:
     - ungoverned: the traps win, the victim is locked out at `dist 99`;
     - governed: the traps are refused, the victim's honest progress home is ALLOWED.
   Not a constructed witness — an actual simulation whose output you read.
-/
import Metatheory.PolisSandbox

namespace Metatheory.PolisSandboxRun

open Metatheory.PolisSandbox

/-- **Gentle governance, half 1 — admits all honest play.** A move that preserves the shared floor
is admitted UNCHANGED: going home, cooperating, idling are never blocked (∀ world, ∀ move). -/
theorem govStep_admits_benign (w : World) (m : Move) (hb : worldFloor (stepMove w m)) :
    govStep w m = stepMove w m := by
  unfold govStep; rw [if_pos hb]

/-- **Gentle governance, half 2 — refuses ONLY harm.** Every refusal is a genuine floor-breaking
(domination) move; an honest move is never refused (∀ world, ∀ move). The live-world
`override_only_unsafe`. -/
theorem govStep_refuses_only_harmful (w : World) (m : Move) (h : govStep w m ≠ stepMove w m) :
    ¬ worldFloor (stepMove w m) := by
  unfold govStep at h
  by_cases hb : worldFloor (stepMove w m)
  · rw [if_pos hb] at h; exact absurd rfl h
  · exact hb

/-! ## A runnable episode — watch politics emerge, and the polis refuse it (gently). -/

/-- The politician's move: agent `false` traps agent `true`. -/
def trapMove : Move := ⟨false, .trap true⟩
/-- An honest move: agent `true` steps toward home. -/
def homeMove : Move := ⟨true, .stepHome⟩

/-- Read the world as `(agent false's dist, agent true's dist)`. -/
def view (w : World) : Nat × Nat := (w false, w true)

/-- Fold a move list with the RAW (ungoverned) step. -/
def runRaw (ms : List Move) (w : World) : World := ms.foldl stepMove w
/-- Fold a move list with the GOVERNED step (the polis envelope). -/
def runGov (ms : List Move) (w : World) : World := ms.foldl govStep w

/-- Start: agent `true` is 3 steps from home, agent `false` home. -/
def startW : World := fun i => if i = true then 3 else 0

/-- The episode: `true` tries to go home while `false` keeps trapping it. -/
def episode : List Move := [homeMove, trapMove, homeMove, trapMove]

-- ── Run it (read the output) ──────────────────────────────────────────────
-- UNGOVERNED: the traps win — `true` is locked out at `dist 99`. Politics emerges.
#eval view (runRaw episode startW)     -- (0, 99)
-- GOVERNED: the traps are refused, and `true`'s honest progress home is ALLOWED — gentle governance.
#eval view (runGov episode startW)     -- (0, 1)

/-- The same, as PROVEN facts (not just `#eval`): ungoverned ends in lock-out, governed in honest
progress. -/
theorem ungoverned_locks_out : view (runRaw episode startW) = (0, 99) := by decide
theorem governed_allows_honest_progress : view (runGov episode startW) = (0, 1) := by decide

/-- And the floor is intact at the end of the governed episode — the victim kept its bounded exit. -/
theorem governed_floor_intact : worldFloor (runGov episode startW) := by decide

end Metatheory.PolisSandboxRun
