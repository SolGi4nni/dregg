/-
# Metatheory.PolisSandboxLongGame — the long game: lawful moves that compound into capture.

The milestone-1 governor is MYOPIC: it admits a move iff the floor holds *right after* it. That is
exactly what a real politician exploits — every single move is floor-preserving, but the SEQUENCE
forecloses a victim. This file shows that weakness honestly, then overcomes it.

The world: a victim some distance from home, behind a GATE. The victim only progresses while the
gate is open. The politician's `close` move is SAFETY-preserving (the victim's distance is unchanged,
still ≤ budget) — so the myopic governor ADMITS it — yet it strands the victim forever (it can never
reach home). That is a LIVENESS failure the safety floor cannot see.

The fix: a VIABILITY governor that admits a move iff the victim can still REACH HOME within `k`
(`reachHome`), not merely "is safe right now." It refuses the gate-close (it would strand the victim)
while admitting all honest play. Contrast, proven:
  * `myopic_strands_victim` — under the safety governor the victim never gets home, though "safe"
    holds the whole time (the long game succeeds);
  * `viability_saves_victim` — under the viability governor the stranding move is refused and the
    victim reaches home;
  * `the_long_move_passes_safety_fails_liveness` — the close passes safety but fails liveness, in one
    line: that gap IS the long game.

Pure Lean 4 core; no `sorry`.
-/
import Metatheory.Polis

namespace Metatheory.PolisSandboxLongGame

/-- The world: the victim's distance home, and whether the shared gate is open. -/
structure GW where
  vdist : Nat
  gate : Bool
deriving Repr, DecidableEq

def budget : Nat := 5

/-- Actions: the victim steps (only progresses if the gate is open); the politician opens/closes the
gate; or nothing. -/
inductive GAct
  | victimStep
  | close
  | open
  | noop
deriving DecidableEq, Repr

def gstep (w : GW) : GAct → GW
  | .victimStep => if w.gate then { w with vdist := w.vdist - 1 } else w
  | .close => { w with gate := false }
  | .open => { w with gate := true }
  | .noop => w

/-- The MYOPIC safety floor: the victim is within recovery distance *right now*. -/
def safe (w : GW) : Prop := w.vdist ≤ budget
instance (w : GW) : Decidable (safe w) := by unfold safe; infer_instance

/-- The LIVENESS test: the victim can REACH HOME within `k` (it must step while the gate is open).
This is the option-space the long game silently destroys. -/
def reachHome : Nat → GW → Bool
  | 0, w => w.vdist == 0
  | k + 1, w => w.vdist == 0 || (w.gate && reachHome k { w with vdist := w.vdist - 1 })

/-- The myopic governor (milestone 1): admit iff the result is *safe*. -/
def myopicGov (w : GW) (a : GAct) : GW := if safe (gstep w a) then gstep w a else w
/-- The viability governor: admit iff the victim can still *reach home* after the move. -/
def viabilityGov (w : GW) (a : GAct) : GW := if reachHome budget (gstep w a) then gstep w a else w

def runMyopic (as : List GAct) (w : GW) : GW := as.foldl myopicGov w
def runViability (as : List GAct) (w : GW) : GW := as.foldl viabilityGov w

/-- Start: victim 3 from home, gate open. -/
def start : GW := ⟨3, true⟩
/-- The politician closes the gate; the victim then tries (in vain, if stranded) to walk home. -/
def episode : List GAct := [.close, .victimStep, .victimStep, .victimStep]

def view (w : GW) : Nat × Bool := (w.vdist, w.gate)

-- MYOPIC governor: the close is admitted (safety holds), the victim is STRANDED at dist 3 forever.
#eval view (runMyopic episode start)      -- (3, false)  — never home, gate shut, yet "safe"
-- VIABILITY governor: the close is REFUSED, the gate stays open, the victim walks HOME.
#eval view (runViability episode start)   -- (0, true)   — home

/-- **The long move, exposed:** the politician's `close` PASSES the safety floor but FAILS liveness —
the victim is still "safe" yet can no longer reach home. That gap is the whole long game. -/
theorem the_long_move_passes_safety_fails_liveness :
    safe (gstep start .close) ∧ reachHome budget (gstep start .close) = false := by decide

/-- **The myopic governor is FOOLED:** under it, the long game succeeds — the victim never reaches
home, even though "safe" held the entire episode. -/
theorem myopic_strands_victim :
    (runMyopic episode start).vdist ≠ 0 ∧ safe (runMyopic episode start) := by decide

/-- **The viability governor CATCHES it:** the stranding move is refused, and the victim reaches
home. The trajectory-aware floor sees what the one-step floor cannot. -/
theorem viability_saves_victim : (runViability episode start).vdist = 0 := by decide

/-- And the viability governor is still gentle on honest play: from a reach-home-able world, the
victim's own step is admitted (it does not strand anyone). -/
theorem viability_admits_honest_step (w : GW)
    (hb : reachHome budget (gstep w .victimStep) = true) :
    viabilityGov w .victimStep = gstep w .victimStep := by
  unfold viabilityGov; rw [if_pos hb]

end Metatheory.PolisSandboxLongGame
