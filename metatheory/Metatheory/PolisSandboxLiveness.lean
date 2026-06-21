/-
# Metatheory.PolisSandboxLiveness — bounded LIVENESS: the victim actually REACHES home.

`PolisSandboxLongGame` proved SAFETY (the floor stays true) and showed the viability governor *refuses*
the stranding close. `PolisSandboxAdaptive` proved the viability governor withstands every attack
(reach-home is never destroyed). But "reach-home is preserved" is a *possibility* — the option to get
home survives. This file closes the gap to an *actuality*: under the viability governor, if the victim
plays `victimStep` every tick, it REACHES home within its initial distance.

The argument is the dual of the safety one. `reachHome budget w = true` with `w.vdist ≠ 0` FORCES the
gate open (`w.gate = true`) — otherwise the victim could not progress, contradiction. So:
  * the victim's own `victimStep` is always *admitted* by the viability governor (it lands in a still-
    reach-home-able world), and
  * the gate being forced open means the step strictly DECREASES `vdist`.
Iterate `vdist` times and the victim is home. That is `victim_reaches_home_under_viability`.

Contrast (proven, by `decide`): under the MYOPIC governor the very same walk from a *closed-gate*
start strands the victim forever — distance never moves, though "safe" holds throughout. Liveness is a
property the one-step floor simply cannot deliver.

No `sorry`, no load-bearing `True`. `#eval`/`#guard` assert TRUE props (`decide` tells the truth).
-/
import Metatheory.PolisSandboxAdaptive

namespace Metatheory.PolisSandboxLiveness

open Metatheory.PolisSandboxLongGame
open Metatheory.PolisSandboxAdaptive

/-! ## The forced-gate lemma — the heart of liveness.

`reachHome` can only succeed through an OPEN gate. So a reach-home-able world that is not yet home has
its gate forced open. (This is exactly why the viability governor's refusal of `close` is not arbitrary
caution: a closed gate at `vdist > 0` is *literally* a non-reach-home state.) -/

/-- If the victim can reach home (in any horizon) but is not yet home, the gate is open. -/
theorem reach_forces_gate {k : Nat} {w : GW}
    (h : reachHome k w = true) (hd : w.vdist ≠ 0) : w.gate = true := by
  cases k with
  | zero =>
      -- `reachHome 0 w = (w.vdist == 0)`, but `w.vdist ≠ 0` — contradiction.
      simp only [reachHome] at h
      exact absurd (by simpa using h) hd
  | succ k =>
      simp only [reachHome] at h
      rcases Bool.or_eq_true _ _ |>.mp h with h0 | hg
      · exact absurd (by simpa using h0) hd
      · exact (Bool.and_eq_true _ _ |>.mp hg).1

/-- And the *tail* survives: reaching home from `w` (not yet home) means reaching home from the world
one step closer, in one less horizon. -/
theorem reach_tail {k : Nat} {w : GW}
    (h : reachHome (k + 1) w = true) (hd : w.vdist ≠ 0) :
    reachHome k { w with vdist := w.vdist - 1 } = true := by
  simp only [reachHome] at h
  rcases Bool.or_eq_true _ _ |>.mp h with h0 | hg
  · exact absurd (by simpa using h0) hd
  · exact (Bool.and_eq_true _ _ |>.mp hg).2

/-- `reachHome` is MONOTONE in the horizon: a spare tick never hurts. If the victim can get home in
`k` steps, it can get home in `k + 1`. -/
theorem reach_mono {k : Nat} : ∀ {w : GW}, reachHome k w = true → reachHome (k + 1) w = true := by
  induction k with
  | zero =>
      intro w h
      -- `reachHome 0 w = (vdist == 0)`; if home now, home in 1 too.
      simp only [reachHome] at h ⊢
      simp [h]
  | succ k ih =>
      intro w h
      -- Peel one tick. If home now, done; else gate is open and the tail reaches home in `k+1` by IH.
      by_cases hz : w.vdist = 0
      · have : (w.vdist == 0) = true := by simp [hz]
        simp only [reachHome, this, Bool.true_or]
      · have hgate : w.gate = true := reach_forces_gate h hz
        have htl : reachHome k { w with vdist := w.vdist - 1 } = true := reach_tail h hz
        have htl' : reachHome (k + 1) { w with vdist := w.vdist - 1 } = true := ih htl
        show (w.vdist == 0 || (w.gate && reachHome (k + 1) { w with vdist := w.vdist - 1 })) = true
        rw [htl', hgate]; simp

/-! ## The walk — iterate the victim's governed step. -/

/-- The victim takes `n` governed `victimStep`s under the viability governor. -/
def walk : Nat → GW → GW
  | 0, w => w
  | n + 1, w => walk n (viabilityGov w .victimStep)

/-- **Single governed step makes progress.** From a reach-home-able world that is not yet home, the
viability governor ADMITS the victim's step (gate forced open ⇒ landing is still reach-home-able) and
the step strictly decreases `vdist`. -/
theorem step_progresses {w : GW}
    (hr : reachHome budget w = true) (hd : w.vdist ≠ 0) :
    viabilityGov w .victimStep = { w with vdist := w.vdist - 1 } := by
  have hg : w.gate = true := reach_forces_gate hr hd
  -- The raw step, with the gate open, lands at `vdist - 1`.
  have hraw : gstep w .victimStep = { w with vdist := w.vdist - 1 } := by
    simp only [gstep, hg, if_true]
  -- That landing is still reach-home-able (it is the reach-home tail of `w`).
  have hbud : budget = (budget - 1) + 1 := by decide
  have htail : reachHome (budget - 1) { w with vdist := w.vdist - 1 } = true :=
    reach_tail (by rw [← hbud]; exact hr) hd
  -- `reachHome budget` of the landing follows because horizon only helps (one more tick to spare):
  have hland : reachHome budget (gstep w .victimStep) = true := by
    rw [hraw]
    have := reach_mono (k := budget - 1) htail
    rwa [← hbud] at this
  -- Hence the governor admits the step, and it equals the raw landing.
  unfold viabilityGov
  rw [if_pos hland, hraw]

/-- **The walk reaches home.** From a reach-home-able world, after `w.vdist` governed victim-steps the
victim is home (`vdist = 0`). The number of steps is exactly the initial distance. -/
theorem walk_reaches_home {w : GW} (hr : reachHome budget w = true) :
    (walk w.vdist w).vdist = 0 := by
  -- Induct on the distance, strengthening over the world via the reach-home witness.
  -- We generalize the goal to: for all m and w, if vdist = m and reachHome holds, walk m w is home.
  suffices H : ∀ m (w : GW), w.vdist = m → reachHome budget w = true → (walk m w).vdist = 0 by
    exact H w.vdist w rfl hr
  intro m
  induction m with
  | zero =>
      intro w hm _
      simp only [walk]; exact hm
  | succ k ih =>
      intro w hm hrw
      have hd : w.vdist ≠ 0 := by rw [hm]; exact Nat.succ_ne_zero k
      have hstep := step_progresses hrw hd
      -- After one governed step, distance is `k` and reach-home survives.
      have hr' : reachHome budget (viabilityGov w .victimStep) = true :=
        viabilityGov_preserves_reach w .victimStep hrw
      have hvd : (viabilityGov w .victimStep).vdist = k := by
        rw [hstep]; show w.vdist - 1 = k; rw [hm]; rfl
      -- `walk (k+1) w = walk k (viabilityGov w victimStep)`; apply the IH to the stepped world.
      simp only [walk]
      exact ih _ hvd hr'

/-- **`victim_reaches_home_under_viability` — the bounded-liveness theorem.** Under the viability
governor, a victim that plays `victimStep` every tick from any reach-home-able world REACHES home
within its initial distance: after exactly `w.vdist` governed steps, `vdist = 0`. Safety guaranteed the
floor; this guarantees ARRIVAL. -/
theorem victim_reaches_home_under_viability {w : GW} (hr : reachHome budget w = true) :
    (walk w.vdist w).vdist = 0 := walk_reaches_home hr

/-! ## Concrete instance + the myopic contrast (no liveness). -/

/-- The victim walking home under the MYOPIC governor — for the contrast. -/
def walkMyopic : Nat → GW → GW
  | 0, w => w
  | n + 1, w => walkMyopic n (myopicGov w .victimStep)

-- The viability-governed victim, started reach-home-able and 3 from home, ARRIVES (vdist 0) in 3 steps.
#eval view (walk start.vdist start)   -- (0, true)  — home, in `start.vdist` steps

/-- Concrete bounded liveness: from `start` (3 from home, gate open, reach-home-able), the viability-
governed victim is home after `start.vdist` steps. A direct corollary of the general theorem, but also
checkable by `decide`. -/
theorem start_reaches_home : (walk start.vdist start).vdist = 0 := by decide

/-- And the general theorem applies to `start` (it is reach-home-able), giving the same arrival. -/
theorem start_reaches_home_via_theorem : (walk start.vdist start).vdist = 0 :=
  victim_reaches_home_under_viability (by decide)

/-- A CLOSED-gate start (victim still "safe", 3 ≤ budget) but already non-reach-home: the myopic
governor cannot help. -/
def stuckStart : GW := ⟨3, false⟩

-- MYOPIC, closed gate: the victim walks forever and NEVER moves — stranded at distance 3.
#eval view (walkMyopic stuckStart.vdist stuckStart)   -- (3, false)  — never home
-- Even running the myopic walk far past its distance: still stranded (no liveness, ever).
#eval view (walkMyopic 50 stuckStart)                 -- (3, false)

-- 50-step `decide` exceeds the default recursion budget; raise it for this one closed-form check.
set_option maxRecDepth 2048 in
/-- **`myopic_strands_no_liveness` — the contrast, proven.** Under the myopic governor, from a safe but
gate-closed start, the victim is STILL not home after even `50` steps (≫ its distance): the one-step
floor delivers no liveness. The viability governor (above) does. -/
theorem myopic_strands_no_liveness :
    (walkMyopic 50 stuckStart).vdist ≠ 0 ∧ safe stuckStart := by decide

-- The two governors, side by side, from the same kind of episode: viability ARRIVES, myopic STRANDS.
#guard (walk start.vdist start).vdist == 0
#guard (walkMyopic 50 stuckStart).vdist != 0
#guard safe stuckStart

end Metatheory.PolisSandboxLiveness
