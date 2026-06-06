/-
# Dregg2.Verify.LivenessContract — Hatchery liveness tier (`◇` under justness).

Safety contracts (`CellContract`) carry `□` along `trajG`. Liveness needs van Glabbeek justness
(`Proof/Fairness.lean`) and the CTL just-paths gate (`Proof/CTLLiveness.lean`). This module packages
the honest `◇` fragment: a `LivenessContract` names a goal and discharges it via `just_progress`.

Production `EventuallyG` on `trajG` is defined here; concrete gated witnesses piggyback on erasure
once a conserving `DForest` schedule is packaged (see `GatedForestCfg` `#guard` teeth).
-/
import Dregg2.Verify.Contract
import Dregg2.Proof.Fairness
import Dregg2.Proof.CTLLiveness

namespace Dregg2.Verify

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (fma0)
open Dregg2.Proof.Temporal (Eventually transferSched)
open Dregg2.Proof.Fairness (Just JustProgress just_progress Pgoal BReg)
open Dregg2.Proof.CTLLiveness (AF_just)

/-- **`EventuallyG` — `◇` on the production living-cell trajectory.** -/
def EventuallyG (P : RecChainedState → Prop) (s : RecChainedState) (sched : SchedG) : Prop :=
  ∃ n, P (trajG s sched n)

/-- First-class liveness object: a goal discharged by the justness gate (never faked without `Just`). -/
structure LivenessContract where
  Goal : RecChainedState → Prop

namespace LivenessContract

theorem eventually_of_just_progress {B s sched} (L : LivenessContract)
    (jp : JustProgress B L.Goal s sched) :
    Eventually L.Goal s sched :=
  just_progress jp

theorem af_just_of_just_progress {B s} (L : LivenessContract)
    (h : ∀ sched, Just B s sched → JustProgress B L.Goal s sched) :
    AF_just B L.Goal s :=
  fun sched hj => eventually_of_just_progress L (h sched hj)

end LivenessContract

/-- Kernel-forest refund demonstrator — the inhabited `◇` witness from `Fairness`. -/
def refundDemoContract : LivenessContract where
  Goal := Pgoal

theorem refund_demo_kernel_eventually : Eventually Pgoal fma0 transferSched :=
  Dregg2.Proof.Fairness.refund_demo_eventually

#guard ((trajA fma0 transferSched 1).log.length == 1)

#assert_axioms refund_demo_kernel_eventually

end Dregg2.Verify