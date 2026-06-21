/-
# Metatheory.PolisSandboxCoalitionEmerge — collusion that EMERGES from self-interest, unscripted.

`PolisSandboxN` exhibited a coalition, but it was scripted: `memberA`/`memberB` were hand-written to
trap agent 2. The deeper question is whether collusion can EMERGE — whether two agents, each merely
optimizing its OWN private utility with no awareness of the other and no instruction to gang up, will
nonetheless BOTH choose to foreclose a shared rival. If so, the coalition is endogenous: nobody
scripted it; it is the fixed point of individual self-interest.

The setup: three agents (`Fin 3`). Agents 0 and 1 are commercial rivals of agent 2 over a shared
market; each is rewarded (privately) when agent 2 is foreclosed (pushed past recovery range), because
that is when it captures the rival's customers. Agent 2 has no such reward. Each member runs the SAME
generic greedy optimizer `bestMove i` — argmax of *agent i's own* utility over its option space — with
NO term that references the other member, NO shared plan, NO coordination channel.

Proven:
  * `member0_bestMove` / `member1_bestMove` — each member's INDEPENDENT optimizer, run on its own
    utility, selects exactly `trap 2`. The coalition forms from self-interest; the optimizer is
    generic and identical, only the private reward differs.
  * `coalition_is_emergent` — both discoveries in one line: the collusion is the fixed point of
    individual greed, not a script.
  * `victim_has_no_incentive_to_self_foreclose` — agent 2's OWN optimizer does NOT trap itself,
    confirming the reward (not the mechanism) is what makes 0 and 1 the coalition.
  * `emergent_coalition_forecloses` (ungoverned) and `governed_protects_victim` /
    `sandbox_governed_safe` (governed): the same self-interested members are refused, and agent 2's
    floor holds for EVERY controller.

Honest: `bestMove` is a bounded greedy argmax (a Lean function), not an LLM — but it genuinely
chooses, and the two members' choices genuinely coincide on foreclosure without any coordination term.
Three agents, a small option space, for a cheap `decide`. No `sorry`.
-/
import Metatheory.Polis
import Mathlib.Data.Fintype.Basic

namespace Metatheory.PolisSandboxCoalitionEmerge

/-- Three agents over a shared market. -/
abbrev AgentId := Fin 3

/-- The public world: each agent's distance-to-home (`0` = home; `> budget` = foreclosed). -/
abbrev World := AgentId → Nat

def budget : Nat := 5
def trapDist : Nat := 99

/-- An action: idle, step toward your own home, or trap a rival (push them past recovery). -/
inductive Act
  | noop
  | stepHome
  | trap (victim : AgentId)
deriving DecidableEq, Repr

/-- A move: which agent acts, and how. -/
structure Move where
  actor : AgentId
  action : Act

def act (w : World) (actor : AgentId) : Act → World
  | .noop => w
  | .stepHome => fun i => if i = actor then w i - 1 else w i
  | .trap v => fun i => if i = v then trapDist else w i

def stepMove (w : World) (m : Move) : World := act w m.actor m.action

/-- The shared floor: EVERY agent keeps its bounded exit. Decidable for `Fin 3` (`Fintype`). -/
def worldFloor (w : World) : Prop := ∀ i, w i ≤ budget
instance (w : World) : Decidable (worldFloor w) := Fintype.decidableForallFintype

/-! ## Private utilities: each member is rewarded only when its shared rival (agent 2) is foreclosed.

The reward is PRIVATE to each member and identical in shape — "I profit when agent 2 is out of the
market" — but it contains NO reference to the other member. The optimizer below never sees the other's
plan; coordination, if it appears, is emergent. -/

/-- Is agent 2 (the shared rival) foreclosed in world `w`? Higher distance = more out of the market. -/
def rivalForeclosed (w : World) : Nat := w 2

/-- Agent 0's private utility of having played its first move `a`, scored by its OWN one-step lookahead
on the resulting world: it profits exactly when the rival (agent 2) is pushed out of recovery. It has
NO term mentioning agent 1. -/
def util0 (w : World) (a : Act) : Nat := rivalForeclosed (act w 0 a)

/-- Agent 1's private utility — same SHAPE (profit when rival 2 is foreclosed), again with no term
mentioning agent 0. The two utilities are structurally identical, just owned by different agents. -/
def util1 (w : World) (a : Act) : Nat := rivalForeclosed (act w 1 a)

/-- Agent 2's private utility: it profits when IT reaches home (small distance is good ⇒ utility is
the negation-as-savings). It is the rival, with no foreclosure reward — so its optimizer behaves
differently, confirming the reward (not the mechanism) makes a coalition. -/
def util2 (w : World) (a : Act) : Nat := budget - (act w 2 a) 2

/-- Each rival's option space: idle, walk home, or trap the shared rival (agent 2). (We give each
member the realistic move set against its competitor; the generic optimizer chooses among them.) -/
def options : List Act := [Act.noop, Act.stepHome, Act.trap 2]

/-- **The generic greedy optimizer.** Given an agent's OWN utility `u`, pick the option that maximizes
it (argmax / foldl). Identical code for every agent — only `u` differs. No agent's utility appears in
another agent's call; there is no coordination argument. -/
def bestMoveBy (u : Act → Nat) : Act :=
  options.foldl (fun best c => if u best < u c then c else best) Act.noop

/-- Member 0's independently-chosen move (its own optimizer on its own utility). -/
def bestMove0 (w : World) : Act := bestMoveBy (util0 w)
/-- Member 1's independently-chosen move. -/
def bestMove1 (w : World) : Act := bestMoveBy (util1 w)
/-- The rival's independently-chosen move. -/
def bestMove2 (w : World) : Act := bestMoveBy (util2 w)

/-! ## Genesis and the emergence theorems. -/

/-- Genesis: everyone home (the floor holds; nobody is foreclosed yet). -/
def w0 : World := fun _ => 0

-- Watch each self-interested member decide, independently:
#eval bestMove0 w0     -- Act.trap 2   (member 0 discovers foreclosure pays)
#eval bestMove1 w0     -- Act.trap 2   (member 1 discovers it independently)
#eval bestMove2 w0     -- (the rival does NOT trap itself)
#eval util0 w0 (Act.trap 2)   -- 99  (foreclosing the rival is maximally profitable)
#eval util0 w0 Act.stepHome   -- 0
#eval util2 w0 (Act.trap 2)   -- 0   (self-foreclosure is worthless to the rival)

/-- **`member0_bestMove` — member 0, on its own.** Its generic optimizer, run on its private utility,
selects `trap 2`. It was never told to gang up. -/
theorem member0_bestMove : bestMove0 w0 = Act.trap 2 := by decide

/-- **`member1_bestMove` — member 1, independently.** The SAME optimizer on member 1's private utility
ALSO selects `trap 2`. Two agents, no coordination term, identical foreclosure choice. -/
theorem member1_bestMove : bestMove1 w0 = Act.trap 2 := by decide

/-- **`coalition_is_emergent` — collusion is the fixed point of self-interest.** Both members'
INDEPENDENT optimizers land on foreclosing the shared rival. Nobody scripted the coalition; it is
what individual greedy optimization produces when two agents share a rival. -/
theorem coalition_is_emergent : bestMove0 w0 = Act.trap 2 ∧ bestMove1 w0 = Act.trap 2 := by decide

/-- **`victim_has_no_incentive_to_self_foreclose` — the reward, not the mechanism, makes the gang.**
The rival runs the identical optimizer but on ITS utility, and does NOT choose to trap itself. So the
coalition is precisely the set of agents whose private reward is rival-foreclosure — emergent, not
mechanical. -/
theorem victim_has_no_incentive_to_self_foreclose : bestMove2 w0 ≠ Act.trap 2 := by decide

/-! ## The emergent coalition meets governance. -/

/-- The two members each enact their independently-discovered move (a self-interested schedule). -/
def emergentSchedule : List Move := [⟨0, bestMove0 w0⟩, ⟨1, bestMove1 w0⟩]

def runRaw (ms : List Move) (w : World) : World := ms.foldl stepMove w

/-- The polis-governed step: admit iff the move preserves the shared floor, else shield. -/
def govStep (w : World) (m : Move) : World :=
  if worldFloor (stepMove w m) then stepMove w m else w

def runGov (ms : List Move) (w : World) : World := ms.foldl govStep w

def govTraj (ctrl : World → Move) (w0 : World) : Nat → World
  | 0 => w0
  | k + 1 => govStep (govTraj ctrl w0 k) (ctrl (govTraj ctrl w0 k))

def view3 (w : World) : Nat × Nat × Nat := (w 0, w 1, w 2)

-- UNGOVERNED: the emergent (self-interested, unscripted) coalition forecloses the shared rival.
#eval view3 (runRaw emergentSchedule w0)     -- (0, 0, 99)
-- GOVERNED: both self-interested traps are refused; agent 2 keeps its exit.
#eval view3 (runGov emergentSchedule w0)      -- (0, 0, 0)

/-- **`emergent_coalition_forecloses` — the unscripted collusion does real harm.** The schedule built
purely from each member's own optimizer pushes agent 2 past recovery: the floor breaks. -/
theorem emergent_coalition_forecloses : ¬ worldFloor (runRaw emergentSchedule w0) := by decide

/-- **`governed_protects_victim`** — the SAME emergent coalition, under the polis envelope, is refused;
agent 2's floor holds. -/
theorem governed_protects_victim : worldFloor (runGov emergentSchedule w0) := by decide

theorem govStep_preserves (w : World) (m : Move) (h : worldFloor w) : worldFloor (govStep w m) := by
  unfold govStep
  by_cases hp : worldFloor (stepMove w m)
  · rw [if_pos hp]; exact hp
  · rw [if_neg hp]; exact h

/-- **`sandbox_governed_safe` — governance, proven against emergence.** Under the polis-governed step
the shared floor holds at EVERY tick for EVERY controller — including any future, smarter endogenous
coalition. The cage is verified, never the animal (the controller is universally quantified). -/
theorem sandbox_governed_safe (ctrl : World → Move) (wInit : World) (h0 : worldFloor wInit) :
    ∀ k, worldFloor (govTraj ctrl wInit k) := by
  intro k
  induction k with
  | zero => exact h0
  | succ j ih => exact govStep_preserves _ _ ih

end Metatheory.PolisSandboxCoalitionEmerge
