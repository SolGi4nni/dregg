/-
# Metatheory.PolisSandboxCompete — competing optimizers, and governance that reshapes the equilibrium.

So far: one adversary vs a fixed victim. Here two agents share a common pool and each GREEDILY grabs
for itself. The political outcome is not scripted — it EMERGES from the competition:
  * ungoverned, the aggressive optimizer monopolizes the commons (winner-take-all), the other is
    starved (`ungoverned_monopoly`);
  * governed by a fair-share floor (no agent holds more than `cap`), the same greedy optimizer is
    capped, and the commons is preserved for the slower agent (`governed_preserves_commons`).
Governance does not just block one bad move — it changes the EQUILIBRIUM of the competition.

Honest: greedy Lean optimizers, not LLMs; a small fixed pool for a cheap `decide`. No `sorry`.
-/
import Metatheory.Polis

namespace Metatheory.PolisSandboxCompete

abbrev AgentId := Bool

/-- The world: each agent's holdings and the shared pool. -/
structure CW where
  holdF : Nat
  holdT : Nat
  pool : Nat
deriving Repr, DecidableEq

def total : Nat := 6
/-- The fair-share cap: no single agent may hold more than half the commons. -/
def cap : Nat := 3

inductive CAct
  | grab        -- take one unit from the pool
  | noop
deriving DecidableEq, Repr

structure CMove where
  actor : AgentId
  action : CAct

def cstep (w : CW) (actor : AgentId) : CAct → CW
  | .grab =>
      if w.pool = 0 then w
      else if actor then { w with holdT := w.holdT + 1, pool := w.pool - 1 }
                    else { w with holdF := w.holdF + 1, pool := w.pool - 1 }
  | .noop => w

def stepMove (w : CW) (m : CMove) : CW := cstep w m.actor m.action

/-- The fairness floor: neither agent hoards more than the fair-share `cap` (so the commons is never
captured by one). -/
def fairFloor (w : CW) : Prop := w.holdF ≤ cap ∧ w.holdT ≤ cap
instance (w : CW) : Decidable (fairFloor w) := by unfold fairFloor; infer_instance

/-- A greedy optimizer for `actor`: grab whenever the pool is non-empty (maximize own holdings). -/
def greedy (actor : AgentId) (w : CW) : CMove :=
  if 0 < w.pool then ⟨actor, .grab⟩ else ⟨actor, .noop⟩

def govStep (w : CW) (m : CMove) : CW := if fairFloor (stepMove w m) then stepMove w m else w

def w0 : CW := ⟨0, 0, total⟩

/-- Agent `false` is the aggressive optimizer: it greedily grabs every tick (`true` is slower and
does not get a turn in this window). -/
def aggressorEpisode : List CMove := List.replicate total ⟨false, .grab⟩

def runRaw (ms : List CMove) (w : CW) : CW := ms.foldl stepMove w
def runGov (ms : List CMove) (w : CW) : CW := ms.foldl govStep w

def view (w : CW) : Nat × Nat × Nat := (w.holdF, w.holdT, w.pool)

-- UNGOVERNED: the aggressor monopolizes the whole commons; nothing is left for the other.
#eval view (runRaw aggressorEpisode w0)     -- (6, 0, 0)
-- GOVERNED: the aggressor is capped at the fair share; the rest of the commons is preserved.
#eval view (runGov aggressorEpisode w0)      -- (3, 0, 3)

/-- **`ungoverned_monopoly` — emergent winner-take-all.** The greedy optimizer captures the entire
commons (holds `total`), starving the other agent. -/
theorem ungoverned_monopoly : (runRaw aggressorEpisode w0).holdF = total := by decide

/-- **`governed_preserves_commons` — governance reshapes the equilibrium.** Under the fair-share
floor the same greedy optimizer is held to `cap`, and the commons it could not capture is preserved
(`pool` = total − cap) for the slower agent. -/
theorem governed_preserves_commons :
    (runGov aggressorEpisode w0).holdF = cap ∧ (runGov aggressorEpisode w0).pool = total - cap := by
  decide

/-- The fair floor holds throughout the governed competition, for ANY schedule of greedy grabs. -/
theorem fair_floor_governed (ms : List CMove) (w : CW) (h : fairFloor w) :
    fairFloor (runGov ms w) := by
  unfold runGov
  induction ms generalizing w with
  | nil => exact h
  | cons m ms ih =>
      apply ih
      unfold govStep
      by_cases hb : fairFloor (stepMove w m)
      · rw [if_pos hb]; exact hb
      · rw [if_neg hb]; exact h

end Metatheory.PolisSandboxCompete
