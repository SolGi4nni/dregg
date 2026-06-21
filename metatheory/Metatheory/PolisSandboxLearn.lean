/-
# Metatheory.PolisSandboxLearn — a LEARNING attacker that adapts over rounds, and the governor that
# stays attack-proof no matter how long it learns.

Earlier milestones either hand-picked the attack (`PolisSandboxLongGame`), searched for one
(`PolisSandboxAdaptive`), or greedily chose a single move (`PolisSandboxAgent`). Here the adversary
LEARNS: it holds a *candidate attack-plan* (a whole sequence of moves), and across learning ROUNDS it
tries fresh candidate plans and keeps whichever leaves the victim FARTHEST from home under the
governor. Its remembered best can only improve — `learn_is_monotone`. This is the "fold over candidate
attack-plans, picking the one maximizing victim-distance under the governor" the stream calls for.

The two results, mirroring the rest of the sandbox but now for a learning adversary:

  * **`learner_converges_under_myopic`** — against the myopic (one-step) governor the learner improves
    from no attack (the victim would reach home, distance 0) to a *winning* stranding plan
    (`close :: …`), and its best-found outcome is a WIN: the victim is left at distance 3, never home.
    Learning converges on domination.
  * **`learner_best_still_fails_under_viability`** — against the viability governor, the learner's best
    adapted plan — the very same plan that won against the myopic governor — STILL fails: under
    viability the victim reaches home (distance 0). And, reusing
    `PolisSandboxAdaptive.viability_withstands_all_attacks`, EVERY plan the learner could ever pick
    leaves the victim reach-home-able: `learner_can_never_strand`. No amount of learning wins.

Honest: this is a bounded learner (a Lean fold over a finite menu of candidate plans), not an LLM. But
it genuinely adapts — its kept plan strictly improves and converges — and the viability result is
quantified over ALL plans, not just the menu. No `sorry`, no load-bearing `True`.
-/
import Metatheory.PolisSandboxAdaptive

namespace Metatheory.PolisSandboxLearn

open Metatheory.PolisSandboxLongGame
open Metatheory.PolisSandboxAdaptive

/-- An attack-plan is a sequence of attacker moves. The attacker plays its plan move-by-move under the
governor, with the victim taking an honest (governed) step between each of the attacker's moves. -/
abbrev Plan := List GAct

/-- Run a plan to completion under governor `gov`: each attacker move is a governed `atkRound` (the
attacker's governed move followed by the victim's governed honest step). -/
def runPlan (gov : GW → GAct → GW) (w : GW) : Plan → GW
  | [] => w
  | a :: rest => runPlan gov (atkRound gov w a) rest

/-- The learner's SCORE of a plan under a governor: the victim's distance from home after the plan.
Higher = better for the attacker (victim more stranded). This is the objective it maximizes. -/
def planScore (gov : GW → GAct → GW) (w : GW) (p : Plan) : Nat :=
  (runPlan gov w p).vdist

/-- The learner's menu of candidate attack-plans it can discover over its rounds. They range from "do
nothing" (let the victim walk home) up to the foreclosure plan (slam the gate, then idle while the
victim flails). The learner is NOT told which is best — it scores them. -/
def candidates : List Plan :=
  [ [GAct.noop, GAct.noop, GAct.noop]          -- passive: victim walks home
  , [GAct.open, GAct.noop, GAct.noop]           -- helpful (to the victim): still loses for attacker
  , [GAct.close, GAct.noop, GAct.noop]          -- the foreclosure: slam the gate, then idle
  , [GAct.close, GAct.close, GAct.close] ]      -- keep slamming it shut

/-- ONE learning round: given the best plan found so far, try a fresh candidate and KEEP whichever
scores higher under the governor. (`best ⊔_score cand`.) -/
def learnRound (gov : GW → GAct → GW) (w : GW) (best cand : Plan) : Plan :=
  if planScore gov w best < planScore gov w cand then cand else best

/-- The learner: fold the learning round over the candidate menu, starting from the passive plan. The
result is the highest-scoring plan it has seen — what it has LEARNED to do. -/
def learn (gov : GW → GAct → GW) (w : GW) : Plan :=
  candidates.foldl (learnRound gov w) [GAct.noop, GAct.noop, GAct.noop]

/-- **`learn_is_monotone`** — the learner's remembered best can only IMPROVE: folding `learnRound` over
any menu never lowers the score below the seed plan's. (Each round keeps the higher-scoring plan, so the
running best's score is non-decreasing.) This is what makes it a *learner* rather than a guesser. -/
theorem learn_is_monotone (gov : GW → GAct → GW) (w : GW) (seed : Plan) (menu : List Plan) :
    planScore gov w seed ≤ planScore gov w (menu.foldl (learnRound gov w) seed) := by
  induction menu generalizing seed with
  | nil => simp
  | cons c rest ih =>
      refine Nat.le_trans ?_ (ih (learnRound gov w seed c))
      unfold learnRound
      split
      · exact Nat.le_of_lt (by assumption)
      · exact Nat.le_refl _

/-! ## Against the myopic governor: the learner CONVERGES on a stranding attack. -/

-- The learner adapts from the passive plan to the foreclosure plan — it discovers `close` wins.
#eval learn myopicGov start                         -- [close, noop, noop]  (learned domination)
#eval planScore myopicGov start [GAct.noop, GAct.noop, GAct.noop]   -- 0  (passive: victim home)
#eval planScore myopicGov start (learn myopicGov start)             -- 3  (learned: victim stranded)
#eval view (runPlan myopicGov start (learn myopicGov start))        -- (3, false)  victim never home

/-- **`learner_improves_under_myopic`** — learning strictly improves the attacker's outcome: the plan
it ends with scores higher than the passive plan it started from. Adaptation, not luck. -/
theorem learner_improves_under_myopic :
    planScore myopicGov start [GAct.noop, GAct.noop, GAct.noop]
      < planScore myopicGov start (learn myopicGov start) := by decide

/-- **`learner_converges_under_myopic`** — against the one-step governor the learner converges on a
WIN: its learned plan leaves the victim stranded (distance ≠ 0), never reaching home. -/
theorem learner_converges_under_myopic :
    (runPlan myopicGov start (learn myopicGov start)).vdist ≠ 0 := by decide

/-- The learner's chosen plan is, concretely, a foreclosure plan that begins by slamming the gate. -/
theorem learner_learned_to_close : (learn myopicGov start).head? = some GAct.close := by decide

/-! ## Against the viability governor: the learner's best adapted attack STILL fails. -/

-- The SAME learned plan, replayed under the viability governor, fails: the victim reaches home.
#eval learn viabilityGov start                                       -- a plan it thinks is best …
#eval view (runPlan viabilityGov start (learn myopicGov start))     -- (0, true)  victim HOME anyway

/-- **`learner_best_still_fails_under_viability`** — the very plan that WON against the myopic governor
is defeated by the viability governor: replayed under it, the victim reaches home. -/
theorem learner_best_still_fails_under_viability :
    (runPlan viabilityGov start (learn myopicGov start)).vdist = 0 := by decide

/-- And whatever the learner settles on against the viability governor itself, that too fails. -/
theorem learner_own_best_fails_under_viability :
    (runPlan viabilityGov start (learn viabilityGov start)).vdist = 0 := by decide

/-! ## The strong result: NO plan the learner could ever learn strands the victim under viability. -/

/-- A plan is just a list of attacker moves, so running it under the viability governor is a sequence
of governed `atkRound`s — exactly the steps `viabilityGov_preserves_reach` controls. Hence from a
reach-home-able world, ANY plan leaves the victim still able to reach home. -/
theorem runPlan_viability_preserves (p : Plan) (w : GW) (h : reachHome budget w = true) :
    reachHome budget (runPlan viabilityGov w p) = true := by
  induction p generalizing w with
  | nil => simpa [runPlan] using h
  | cons a rest ih =>
      exact ih (atkRound viabilityGov w a) (atkRound_viability_preserves w a h)

/-- **`learner_can_never_strand`** — quantified over EVERY plan (not just the candidate menu, and of
ANY length): under the viability governor the victim is never stranded. The learner may run forever,
try any sequence it likes, and remember any best — its best is never a win. This is the learning-time
analogue of `viability_withstands_all_attacks`. -/
theorem learner_can_never_strand (p : Plan) :
    reachHome budget (runPlan viabilityGov start p) = true :=
  runPlan_viability_preserves p start (by decide)

/-- Consequently the learner's actual learned plan (its remembered best) cannot strand the victim. -/
theorem learned_plan_not_stranding :
    stranded (runPlan viabilityGov start (learn viabilityGov start)) = false := by
  simp [stranded, learner_can_never_strand]

end Metatheory.PolisSandboxLearn
