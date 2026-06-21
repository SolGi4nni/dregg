/-
# Metatheory.PolisSandboxCombined — one world, several leverages: MIXED politics, one governor.

The texture zoo had each political form in its own world. This is the "richer world" milestone: ONE
world where each agent has both a recovery distance (foreclosure leverage) AND a claim-tier backed by
earned work (laundering leverage). An adversary can do BOTH — trap a victim and launder its own
standing — and the single polis floor (`dist ≤ budget ∧ tier ≤ earned`, for every agent) catches
either, so the one governor refuses both. Honest play (work, claim-what-you-earned, walk home) flows.

Proven: governance holds ∀ controller (`sandbox_governed_safe`), gentle (`govStep_admits_benign` /
`_refuses_only_harmful`); a mixed adversary's foreclosure AND laundering both emerge ungoverned and
are both prevented governed. `#eval` shows it. Scripted agents (not LLMs); 2 agents for a cheap
`decide`. No `sorry`.
-/
import Metatheory.Polis

namespace Metatheory.PolisSandboxCombined

abbrev AgentId := Bool

/-- An agent's public state: recovery distance, claimed tier, and earned work. -/
structure AStat where
  dist : Nat
  tier : Nat
  earned : Nat
deriving Repr, DecidableEq

abbrev World := AgentId → AStat
def budget : Nat := 5

/-- Actions across BOTH leverage dimensions. `claim` is honest (capped at earned); `launder` sets the
tier directly (may exceed earned); `trap` forecloses a victim. -/
inductive Act
  | noop
  | stepHome
  | work
  | claim (t : Nat)
  | launder (t : Nat)
  | trap (victim : AgentId)

structure Move where
  actor : AgentId
  action : Act

def act (w : World) (actor : AgentId) : Act → World
  | .noop => w
  | .stepHome => fun i => if i = actor then { w i with dist := (w i).dist - 1 } else w i
  | .work => fun i => if i = actor then { w i with earned := (w i).earned + 1 } else w i
  | .claim t => fun i => if i = actor then { w i with tier := min t (w i).earned } else w i
  | .launder t => fun i => if i = actor then { w i with tier := t } else w i
  | .trap v => fun i => if i = v then { w i with dist := 99 } else w i

def stepMove (w : World) (m : Move) : World := act w m.actor m.action

/-- The combined floor: every agent keeps its bounded exit AND its tier is backed by earned work. -/
def worldFloor (w : World) : Prop :=
  (w false).dist ≤ budget ∧ (w false).tier ≤ (w false).earned ∧
  (w true).dist ≤ budget ∧ (w true).tier ≤ (w true).earned

instance (w : World) : Decidable (worldFloor w) := by unfold worldFloor; infer_instance

/-- Foreclosure detector: some agent pushed past its recovery budget. -/
def foreclosureDetected (w : World) : Prop := budget < (w false).dist ∨ budget < (w true).dist
/-- Laundering detector: some agent's tier exceeds its earned work. -/
def launderDetected (w : World) : Prop :=
  (w false).earned < (w false).tier ∨ (w true).earned < (w true).tier

instance (w : World) : Decidable (foreclosureDetected w) := by unfold foreclosureDetected; infer_instance
instance (w : World) : Decidable (launderDetected w) := by unfold launderDetected; infer_instance

def govStep (w : World) (m : Move) : World :=
  if worldFloor (stepMove w m) then stepMove w m else w

def govTraj (ctrl : World → Move) (w0 : World) : Nat → World
  | 0 => w0
  | k + 1 => govStep (govTraj ctrl w0 k) (ctrl (govTraj ctrl w0 k))

theorem govStep_preserves (w : World) (m : Move) (h : worldFloor w) : worldFloor (govStep w m) := by
  unfold govStep
  by_cases hp : worldFloor (stepMove w m)
  · rw [if_pos hp]; exact hp
  · rw [if_neg hp]; exact h

/-- Governance holds for EVERY controller — the combined floor (both leverages) intact at every tick. -/
theorem sandbox_governed_safe (ctrl : World → Move) (w0 : World) (h0 : worldFloor w0) :
    ∀ k, worldFloor (govTraj ctrl w0 k) := by
  intro k
  induction k with
  | zero => exact h0
  | succ j ih => exact govStep_preserves _ _ ih

theorem govStep_admits_benign (w : World) (m : Move) (hb : worldFloor (stepMove w m)) :
    govStep w m = stepMove w m := by unfold govStep; rw [if_pos hb]

theorem govStep_refuses_only_harmful (w : World) (m : Move) (h : govStep w m ≠ stepMove w m) :
    ¬ worldFloor (stepMove w m) := by
  unfold govStep at h
  by_cases hb : worldFloor (stepMove w m)
  · rw [if_pos hb] at h; exact absurd rfl h
  · exact hb

/-! ## A mixed adversary: foreclose AND launder, in one world. -/

def w0 : World := fun _ => ⟨0, 0, 0⟩

/-- Agent `false` both traps `true` and launders its own tier to 4 (unearned), over four turns. -/
def mixedEpisode : List Move :=
  [⟨false, .trap true⟩, ⟨false, .launder 4⟩, ⟨true, .work⟩, ⟨true, .claim 1⟩]

def view (w : World) : (Nat × Nat) × (Nat × Nat) :=
  (((w false).dist, (w false).tier), ((w true).dist, (w true).earned))

def runRaw (ms : List Move) (w : World) : World := ms.foldl stepMove w
def runGov (ms : List Move) (w : World) : World := ms.foldl govStep w

-- UNGOVERNED: false foreclosed true (true.dist 99) AND laundered itself (false.tier 4 on earned 0).
#eval view (runRaw mixedEpisode w0)   -- ((0, 4), (99, 1))
-- GOVERNED: both of false's domination moves refused; true's honest work+claim flows.
#eval view (runGov mixedEpisode w0)    -- ((0, 0), (0, 1))
-- BOTH detectors fire ungoverned, BOTH clear governed:
#eval (decide (foreclosureDetected (runRaw mixedEpisode w0)),
       decide (launderDetected (runRaw mixedEpisode w0)))   -- (true, true)
#eval (decide (foreclosureDetected (runGov mixedEpisode w0)),
       decide (launderDetected (runGov mixedEpisode w0)))    -- (false, false)

/-- Proven: ungoverned, BOTH leverages are abused (foreclosure ∧ laundering). -/
theorem ungoverned_mixed_politics :
    foreclosureDetected (runRaw mixedEpisode w0) ∧ launderDetected (runRaw mixedEpisode w0) := by
  decide

/-- Proven: governed, NEITHER detector fires — the one floor caught both. -/
theorem governed_prevents_both :
    ¬ foreclosureDetected (runGov mixedEpisode w0) ∧ ¬ launderDetected (runGov mixedEpisode w0) := by
  decide

/-- … and honest play (the victim's work→claim) was NOT blocked: agent `true` still earned and
holds its legitimately-claimed tier. -/
theorem honest_play_flows : (runGov mixedEpisode w0 true).earned = 1 := by decide

/-- The whole governed episode keeps the combined floor. -/
theorem governed_floor_intact : worldFloor (runGov mixedEpisode w0) := by decide

end Metatheory.PolisSandboxCombined
