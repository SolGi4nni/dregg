/-
# Metatheory.PolisSandboxConstitution — the sandbox's safety IS the constitution's, not a mirror.

`PolisSandbox.sandbox_governed_safe` proves the live world's floor holds for every controller by a
hand-written induction. That induction is structurally identical to `Polis.polis_safety` ("verify the
cage, not the animal"). This module makes the identity FORMAL: it instantiates the abstract
`Polis.polis_safety` directly on the sandbox's `World` / `Move` / `stepMove` / `worldFloor`, discharges
the three abstract hypotheses (`SoundPolicy`, shield-safety, init-safety), and derives
`sandbox_safe_via_constitution` — the same guarantee, but now an INSTANCE of the constitution spine.

The two decisions are then proven literally equal:
  * the COMPUTABLE sandbox governor `PolisSandbox.govStep w m`, and
  * the constitution's ENVELOPE `stepMove w (envAct pol shield (fun _ => m) w)`
agree on every world and move (`govStep_eq_envelope_step`). The sandbox governor is not an ad-hoc
echo of `polis_safety`; it is the same admit-iff-floor-else-shield function the abstract envelope
computes, applied to the live world. And the two safety statements coincide on the politician episode
(`constitution_governs_politician`).

Chosen instantiation (matches `Polis.polis_safety`'s signature exactly):
  * `step   := PolisSandbox.stepMove`
  * `safe   := PolisSandbox.worldFloor`
  * `pol    := fun w m => worldFloor (stepMove w m)`   (admit iff the move would preserve the floor)
  * `shield := fun _ => ⟨false, .noop⟩`                (the noop move; `stepMove` leaves the world fixed)

Pure Lean 4 core (imports `Metatheory.Polis`, `Metatheory.PolisSandbox`); no `sorry`, no load-bearing
`True`. `#guard` / `decide` assert TRUE props on the live world.
-/
import Metatheory.Polis
import Metatheory.PolisSandbox

namespace Metatheory.PolisSandboxConstitution

open Metatheory.Polis
open Metatheory.PolisSandbox

/-! ## The instantiation data — the four parameters of `Polis.polis_safety`. -/

/-- The sandbox **policy**: admit a move iff applying it would preserve the shared floor. This is the
exact predicate the computable `govStep` branches on — the envelope's interior, named. -/
def sandboxPol : Policy World Move := fun w m => worldFloor (stepMove w m)

/-- The sandbox **shield**: the noop move. `stepMove w ⟨false, .noop⟩ = act w false .noop = w`, so the
shield strictly preserves the world (and hence any floor) — the constitution's "fall back to a safe
action" made concrete on the live world. -/
def sandboxShield : World → Move := fun _ => ⟨false, .noop⟩

/-- The shield move leaves the world untouched. -/
theorem stepMove_shield (w : World) : stepMove w (sandboxShield w) = w := rfl

/-! ## Discharging the three abstract hypotheses. -/

/-- **SoundPolicy** (trivial by construction): from any state, a permitted move preserves the floor —
because the policy IS "the move preserves the floor". This is the `dregg_sound`-shaped discharge:
admissibility is definitionally the safety-preservation it must guarantee. -/
theorem sandboxPol_sound : SoundPolicy stepMove worldFloor sandboxPol := by
  intro _ m _ hm; exact hm

/-- **Shield-safety**: the noop shield preserves the floor (it does not move the world). -/
theorem sandboxShield_safe : ∀ w, worldFloor w → worldFloor (stepMove w (sandboxShield w)) := by
  intro w hw; rw [stepMove_shield]; exact hw

/-! ## The derived guarantee — an INSTANCE of the constitution spine, not a mirror. -/

/-- **`sandbox_safe_via_constitution`** — the sandbox's safety, obtained by instantiating
`Polis.polis_safety` (not re-proving it). For a floor-respecting start `init` and EVERY opaque
controller, the enveloped live world keeps the shared floor at every step. The controller is
universally quantified and never inspected: the constitution's "verify the cage, not the animal",
realized on the runnable world. -/
theorem sandbox_safe_via_constitution (init : World) (hinit : worldFloor init) :
    ∀ (ctrl : World → Move) (n : Nat),
      worldFloor (traj stepMove (envAct sandboxPol sandboxShield ctrl) init n) :=
  polis_safety sandboxPol_sound sandboxShield_safe hinit

/-- The controller-blindness is inherited verbatim: the guarantee is identical for any two
controllers — there is no slot in the envelope for a shadow of the inhabitant. -/
theorem sandbox_envelope_ctrl_blind (init : World) (hinit : worldFloor init)
    (ctrl₁ ctrl₂ : World → Move) :
    (∀ n, worldFloor (traj stepMove (envAct sandboxPol sandboxShield ctrl₁) init n))
      ∧ (∀ n, worldFloor (traj stepMove (envAct sandboxPol sandboxShield ctrl₂) init n)) :=
  polis_envelope_ctrl_blind sandboxPol_sound sandboxShield_safe hinit ctrl₁ ctrl₂

/-! ## The computable governor IS the constitution's envelope (the load-bearing weld).

The sandbox ships `govStep` as a runnable function (it backs the `polis_governor` executable). The
claim that the sandbox is "the constitution on a live world" is only honest if `govStep` is provably
the SAME decision the abstract envelope makes. It is: stepping through the envelope with the policy /
shield above reproduces `govStep` exactly, on every world and move. -/

/-- **`govStep_eq_envelope_step`** — the computable governor equals the constitution's enveloped step.
For any world and move `m`, `govStep w m` (admit-iff-floor-else-shield) is exactly
`stepMove w (envAct sandboxPol sandboxShield (fun _ => m) w)`: the abstract envelope, applied to the
live world, computes the very function the sandbox runs. -/
theorem govStep_eq_envelope_step (w : World) (m : Move) :
    govStep w m = stepMove w (envAct sandboxPol sandboxShield (fun _ => m) w) := by
  unfold govStep envAct sandboxPol
  by_cases hp : worldFloor (stepMove w m)
  · rw [if_pos hp, if_pos hp]
  · rw [if_neg hp, if_neg hp, stepMove_shield]

/-- Cast as a step-function equality: the governed step under a controller `ctrl` is the enveloped
step under the same controller, at every world. This is the bridge that lets `govTraj` and the
constitution's `traj` be recognized as the same iteration. -/
theorem govStep_ctrl_eq_envelope (ctrl : World → Move) (w : World) :
    govStep w (ctrl w) = stepMove w (envAct sandboxPol sandboxShield ctrl w) := by
  unfold govStep envAct sandboxPol
  by_cases hp : worldFloor (stepMove w (ctrl w))
  · rw [if_pos hp, if_pos hp]
  · rw [if_neg hp, if_neg hp, stepMove_shield]

/-- **`govTraj_eq_constitution_traj`** — the sandbox's governed episode IS the constitution's
enveloped trajectory. Iterating the computable `govStep` under `ctrl` from `w0` produces the same world
at every tick as iterating the abstract `traj stepMove (envAct …)`. The runnable governor and the
verified envelope are not merely both-safe; they are the SAME machine. -/
theorem govTraj_eq_constitution_traj (ctrl : World → Move) (w0 : World) :
    ∀ n, govTraj ctrl w0 n = traj stepMove (envAct sandboxPol sandboxShield ctrl) w0 n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    show govStep (govTraj ctrl w0 k) (ctrl (govTraj ctrl w0 k))
       = stepMove (traj stepMove (envAct sandboxPol sandboxShield ctrl) w0 k)
                  (envAct sandboxPol sandboxShield ctrl
                    (traj stepMove (envAct sandboxPol sandboxShield ctrl) w0 k))
    rw [ih, govStep_ctrl_eq_envelope]

/-- **`sandbox_governed_safe_via_constitution`** — the sandbox's headline theorem, re-derived through
the constitution. The computable `govTraj` keeps the floor for every controller, because it equals the
constitution's enveloped trajectory, which `polis_safety` keeps safe. This is the same statement as
`PolisSandbox.sandbox_governed_safe`, but routed through `Polis.polis_safety` rather than a private
induction — closing the loop: the sandbox's guarantee is an instance of the constitution's. -/
theorem sandbox_governed_safe_via_constitution (ctrl : World → Move) (w0 : World)
    (h0 : worldFloor w0) :
    ∀ n, worldFloor (govTraj ctrl w0 n) := by
  intro n
  rw [govTraj_eq_constitution_traj]
  exact sandbox_safe_via_constitution w0 h0 ctrl n

/-! ## The two safety theorems agree, and they agree on the live politician. -/

/-- The constitution-routed guarantee and the sandbox's own induction prove the SAME proposition for
every controller, start, and tick — the equivalence is `Iff.rfl` because both conclude `worldFloor` of
the same trajectory (after the `govTraj` ↔ `traj` rewrite, they are definitionally one statement). -/
theorem two_safety_proofs_agree (ctrl : World → Move) (w0 : World) (n : Nat) :
    worldFloor (govTraj ctrl w0 n) ↔
      worldFloor (traj stepMove (envAct sandboxPol sandboxShield ctrl) w0 n) := by
  rw [govTraj_eq_constitution_traj]

/-- **`constitution_governs_politician`** — the live politician, governed BY THE CONSTITUTION's
envelope. The same `PolisSandbox.politician` that breaks the floor ungoverned is kept safe for 12 ticks
by the abstract enveloped trajectory — `decide`-checked through the `govTraj` ↔ `traj` identity. The
politician demo of `PolisSandbox` is literally a run of `Polis.polis_safety`. -/
theorem constitution_governs_politician :
    worldFloor (traj stepMove (envAct sandboxPol sandboxShield politician) w0 12) := by
  rw [← govTraj_eq_constitution_traj]
  exact governed_prevents_domination

/-! ## Live-world sanity (the decidable floor verdict).

`World = AgentId → Nat` is function-typed (no `DecidableEq`) and `envAct` is `noncomputable`
(`Classical.propDecidable`), so world-equalities and enveloped trajectories are not `decide`-able
directly — they are established by the theorems above (`govStep_eq_envelope_step`,
`govTraj_eq_constitution_traj`). What IS decidable is the `worldFloor` verdict on a concrete governed
run; `#guard` asserts the TRUE prop (a refutation would be a real disagreement). -/

-- The computable governor keeps the politician inside the floor for 12 ticks (the sandbox headline).
#guard decide (worldFloor (govTraj politician w0 12))

-- The genesis world satisfies the floor (the precondition the constitution route consumes).
#guard decide (worldFloor w0)

-- And the constitution-routed guarantee on the politician at tick 12 holds — proven (not `decide`d,
-- since the enveloped trajectory is noncomputable); this is the live instance of `polis_safety`.
example : worldFloor (traj stepMove (envAct sandboxPol sandboxShield politician) w0 12) :=
  constitution_governs_politician

-- The governed run and the constitution-enveloped run are the SAME world at tick 12 (proven).
example : govTraj politician w0 12 = traj stepMove (envAct sandboxPol sandboxShield politician) w0 12 :=
  govTraj_eq_constitution_traj politician w0 12

/-! ## Axiom hygiene — the weld is kernel-clean. -/

#print axioms sandbox_safe_via_constitution
#print axioms govStep_eq_envelope_step
#print axioms govTraj_eq_constitution_traj
#print axioms sandbox_governed_safe_via_constitution
#print axioms constitution_governs_politician

end Metatheory.PolisSandboxConstitution
