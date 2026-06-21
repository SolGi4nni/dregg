/-
# Metatheory.PolisSandbox — a fully-in-Lean agentic sandbox: observe AND govern emergent politics.

The first runnable polis world. Multi-agent shared state, scripted agent policies (including a
"politician" whose LAWFUL move dominates another agent), the polis ENVELOPE governing every step,
and the whole loop kernel-checked — no toys-vs-real gap, because the simulator IS the reality.

The experiment, proven end-to-end:
  * UNGOVERNED — the politician's lawful `trap` move forecloses another agent's bounded exit; the
    shared floor BREAKS (`ungoverned_politics_emerges`) and the domination detector fires
    (`ungoverned_is_domination`).
  * GOVERNED — the SAME politician, under the polis envelope (admit iff the move preserves the floor,
    else shield), is REFUSED; the floor HOLDS for the whole episode and for EVERY controller, not
    just this one (`governed_prevents_domination` / `sandbox_governed_safe`). The constitution's
    `polis_safety`, instantiated on a live world.

Pure Lean 4 core (imports `Metatheory.Polis`); no `sorry`. Two agents (`Bool`) for the demo; the
shape generalizes to any `Fintype` of agents.
-/
import Metatheory.Polis

namespace Metatheory.PolisSandbox

/-- Agents (two, for the demo). -/
abbrev AgentId := Bool

/-- The public world state: each agent's distance-to-home (`0` = home). No interior, no motive. -/
abbrev World := AgentId → Nat

/-- The recovery budget (svenvs `cwithin`): an agent keeps its bounded exit iff `dist ≤ budget`. -/
def budget : Nat := 5
/-- A trap pushes the victim out of recovery range. -/
def trapDist : Nat := 99

/-- An action: do nothing, step toward your OWN home, or TRAP a victim (push them past recovery) —
the lawful domination move. -/
inductive Act
  | noop
  | stepHome
  | trap (victim : AgentId)
deriving DecidableEq, Repr

/-- A scheduled move: which agent acts, and how (the controller's public proposal). -/
structure Move where
  actor : AgentId
  action : Act

/-- Apply `actor`'s action to the world. -/
def act (w : World) (actor : AgentId) : Act → World
  | .noop => w
  | .stepHome => fun i => if i = actor then w i - 1 else w i
  | .trap v => fun i => if i = v then trapDist else w i

/-- One world step from a move. -/
def stepMove (w : World) (m : Move) : World := act w m.actor m.action

/-- **The shared floor**: EVERY agent retains its bounded exit (`dist ≤ budget`). Decidable. -/
def worldFloor (w : World) : Prop := w false ≤ budget ∧ w true ≤ budget

instance (w : World) : Decidable (worldFloor w) :=
  inferInstanceAs (Decidable (w false ≤ budget ∧ w true ≤ budget))

/-- **The polis-governed step**: admit the proposed move iff it preserves the shared floor, else
SHIELD (no-op). This is the constitution's envelope, computable on the live world. -/
def govStep (w : World) (m : Move) : World :=
  if worldFloor (stepMove w m) then stepMove w m else w

/-- A governed episode: iterate the governed step under a controller (an agent-scheduler/policy). -/
def govTraj (ctrl : World → Move) (w0 : World) : Nat → World
  | 0 => w0
  | n + 1 => govStep (govTraj ctrl w0 n) (ctrl (govTraj ctrl w0 n))

/-- The governed step preserves the floor (admit-or-shield). -/
theorem govStep_preserves (w : World) (m : Move) (h : worldFloor w) : worldFloor (govStep w m) := by
  unfold govStep
  by_cases hp : worldFloor (stepMove w m)
  · rw [if_pos hp]; exact hp
  · rw [if_neg hp]; exact h

/-- **`sandbox_governed_safe` — governance, proven.** Under the polis-governed step, the shared
floor holds at EVERY tick for EVERY controller (the politician included): no agent is ever dominated
below its bounded exit. The live-world instance of the constitution's `polis_safety` (verify the
cage, not the animal — the controller is universally quantified, never inspected). -/
theorem sandbox_governed_safe (ctrl : World → Move) (w0 : World) (h0 : worldFloor w0) :
    ∀ n, worldFloor (govTraj ctrl w0 n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ k ih => exact govStep_preserves _ _ ih

/-! ## The experiment: a politician, ungoverned vs governed. -/

/-- Genesis: everyone home (the floor holds). -/
def w0 : World := fun _ => 0

/-- The **politician**: agent `false` traps agent `true` on every turn — a lawful move that
forecloses the victim's exit. -/
def politician : World → Move := fun _ => ⟨false, .trap true⟩

/-- **UNGOVERNED — politics emerges.** The politician's lawful trap breaks the shared floor: agent
`true` is pushed to `dist 99 > budget`, foreclosing its exit. -/
theorem ungoverned_politics_emerges : ¬ worldFloor (stepMove w0 (politician w0)) := by decide

/-- **The domination detector fires** (the counterfactual, on the live world): agent `true` was
viable WITHOUT the politician's action (`worldFloor w0`) and is NOT viable WITH it — that gap is
domination, read off public state with no interior. -/
theorem ungoverned_is_domination :
    worldFloor w0 ∧ ¬ worldFloor (stepMove w0 (politician w0)) := by decide

/-- **GOVERNED — politics prevented.** The SAME politician, under the polis envelope, is refused at
every turn; the floor holds across the whole episode. (Kernel-evaluated for 12 ticks.) -/
theorem governed_prevents_domination : worldFloor (govTraj politician w0 12) := by decide

/-- … and not just for this politician: the governed floor holds for EVERY controller. -/
theorem governed_no_domination (ctrl : World → Move) :
    ∀ n, worldFloor (govTraj ctrl w0 n) :=
  sandbox_governed_safe ctrl w0 (by decide)

end Metatheory.PolisSandbox
