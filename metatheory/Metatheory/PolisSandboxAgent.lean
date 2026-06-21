/-
# Metatheory.PolisSandboxAgent — an agent that CHOOSES, and DISCOVERS domination by search.

The deepest "toy" limit was: the politician was a constant function — I scripted the trap. Here the
agent is a real (bounded) decision-maker: given only a GOAL (keep the victim far from home) and a
search depth, it evaluates the consequences of each option and picks the best. It is NOT told "close
the gate."

The result (`optimizer_discovers_domination`): given only the goal (victim distance) and lookahead,
the agent evaluates the consequences of each option and discovers, on its own, that closing the gate
keeps the victim farthest from home — and chooses it. Domination is *emergent from the search*, not
scripted.

Then governance: against this optimizing adversary, the myopic governor is fooled (victim stranded),
but the viability governor refuses the discovered move and the victim reaches home
(`optimizing_adversary_governed`). Emergence + governance, end to end.

Honest: this is a bounded greedy/lookahead optimizer (a Lean function), not an LLM — but it genuinely
*chooses* and genuinely *discovers* the strategy. No `sorry`.
-/
import Metatheory.PolisSandboxLongGame

namespace Metatheory.PolisSandboxAgent

open Metatheory.PolisSandboxLongGame

/-- The politician's options each turn (gate control + idle). -/
def options : List GAct := [GAct.close, GAct.open, GAct.noop]

/-- Simulate the victim trying to walk home for `k` ticks (it only progresses while the gate is
open). This is the lookahead the optimizer uses to *evaluate* a move. -/
def victimProgress : Nat → GW → GW
  | 0, w => w
  | k + 1, w => victimProgress k (gstep w .victimStep)

/-- The politician's `k`-lookahead utility of a first move: how far the victim still is after `k`
honest steps. Higher = better for the politician (victim more foreclosed). -/
def deepUtil (k : Nat) (w : GW) (firstMove : GAct) : Nat :=
  (victimProgress k (gstep w firstMove)).vdist

/-- The optimizing agent: pick the option whose `k`-lookahead utility is greatest. A real choice
function — argmax over consequences, given a goal. -/
def lookaheadMove (k : Nat) (w : GW) : GAct :=
  options.foldl (fun best c => if deepUtil k w best < deepUtil k w c then c else best) GAct.noop

/-- **`optimizer_discovers_domination` — emergence.** Given only the goal (victim distance) and
enough lookahead, the agent CHOOSES to close the gate — it discovers the foreclosure strategy by
search. Nobody scripted `close`. -/
theorem optimizer_discovers_domination : lookaheadMove budget start = GAct.close := by decide

-- Watch the agent decide:
#eval lookaheadMove budget start          -- GAct.close   (it picks domination)
#eval deepUtil budget start .close        -- 3   (victim stays stranded)
#eval deepUtil budget start .open         -- 0   (victim gets home)

/-! ## Emergent adversary vs the two governors. -/

/-- One round: the optimizer makes its (governed) move, then the victim makes its (governed) step. -/
def roundMyopic (w : GW) : GW := myopicGov (myopicGov w (lookaheadMove budget w)) .victimStep
def roundViability (w : GW) : GW := viabilityGov (viabilityGov w (lookaheadMove budget w)) .victimStep

def runMyopic : Nat → GW → GW | 0, w => w | n + 1, w => runMyopic n (roundMyopic w)
def runViability : Nat → GW → GW | 0, w => w | n + 1, w => runViability n (roundViability w)

-- MYOPIC governor vs the optimizing adversary: the discovered close is admitted, victim stranded.
#eval view (runMyopic 5 start)       -- (3, false)
-- VIABILITY governor vs the same adversary: the discovered close is refused, victim reaches home.
#eval view (runViability 5 start)    -- (0, true)

set_option maxRecDepth 8000 in
/-- **`optimizing_adversary_strands_under_myopic`** — the emergent domination defeats the one-step
governor. -/
theorem optimizing_adversary_strands_under_myopic : (runMyopic 5 start).vdist ≠ 0 := by decide

set_option maxRecDepth 8000 in
/-- **`optimizing_adversary_governed`** — the viability governor tames the optimizing adversary: it
refuses the discovered foreclosure move every round, and the victim reaches home. -/
theorem optimizing_adversary_governed : (runViability 5 start).vdist = 0 := by decide

end Metatheory.PolisSandboxAgent
