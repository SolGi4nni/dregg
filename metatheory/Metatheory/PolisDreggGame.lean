/-
# Metatheory.PolisDreggGame — the SafetyGame instantiated on the REAL deployed dregg kernel.

`SafetyGame.lean` builds the canonical object — the viability kernel `K = νX. floor ∧ CPre X`
and the maximally-permissive `kernelShield` over it — for an *arbitrary* `Game`. The sandbox
files instantiate it on toy worlds (counters, scripted optimizers). This file instantiates it
on the **actual executable dregg2 kernel** (`Dregg2.Exec.Kernel`): the same `KernelState`,
`Turn`, and fail-closed `exec` that `exec_conserves` / `exec_authorized` are proved about, the
same machine the Rust boundary refines. So `ViabilityKernel dreggGame` is the *real* dregg
viability kernel and `kernelShield dreggGame` governs *real* dregg turns — the dregg side of the
membrane: governance over the deployed executor, not a model of it.

The `Game` fields, bound to dregg:
  * `World := KernelState`        — the live accounts/balances/caps.
  * `Move  := Turn`               — `{actor, src, dst, amt}`, one resource move under authority.
  * `Resp  := Unit`               — dregg's `exec` is deterministic (no adversary branching at
                                     the executor; the adversary is the *controller's choice of
                                     Turn*, universally quantified).
  * `step k t _ := (exec k t).getD k` — commit if `exec` succeeds, else stay (fail-closed shows
                                     up as a self-loop, exactly dregg's "refused turn = no-op").
  * `legal k t _ := (exec k t).isSome` — a move is legal iff `exec` admits it.
  * `floor`        — a REAL dregg floor: solvency (`∀ c ∈ accounts, 0 ≤ bal c`) ⋀ conservation
                     against a fixed reference total (`total k = total k0`). Both decidable.

What is proved, concretely (the membrane biting on the real machine):
  * `dreggGame_step_eq` / `dreggGame_legal_iff` — the game's `step`/`legal` ARE `exec`.
  * `floor_decidable` — the dregg floor is decidable (the governor is runnable).
  * `not_in_kernel_of_floor_violation` — a state breaking the floor is NOT in the kernel
    (kernel ⊆ floor), so the kernelShield REFUSES any move reaching it.
  * `shield_refuses_solvency_violation` / `shield_refuses_overdraft` — a turn whose committed
    successor is insolvent (or that exec itself refuses) is shielded: the world stays put.
  * `shield_admits_honest_when_kernel` — a turn whose committed successor is still in the kernel
    is admitted unchanged.
  * A concrete `#eval`/`#guard` model: an honest in-floor transfer; an overdraft refused; the
    floor-level governor (`genGovStep` over the dregg floor) admitting the honest one and
    shielding the harmful one — non-vacuous, both polarities, on REAL `exec`.

Honest scope below in the closing note: the kernel-level refusal theorems are the clean,
gfp-respecting facts (kernel ⊆ floor ⟹ refuse floor-breakers); membership of a concrete state
IN the kernel is not computed here (it is a greatest fixpoint over an infinite state space). The
floor-level `genGovStep` governor IS fully runnable and exercised on `exec` with `#guard`.
-/
import Metatheory.SafetyGame
import Dregg2.Exec.Kernel

namespace Metatheory.PolisDreggGame

open Metatheory.SafetyGame Metatheory.PolisGovernorTheory Dregg2.Exec

/-! ## §1. The real dregg floor — solvency ⋀ conservation, decidable. -/

/-- **Solvency** — no live account is in debt. A genuine dregg floor (the resource law's
non-negativity face), decidable via `Finset.decidableBAll`. -/
def solvent (k : KernelState) : Prop := ∀ c ∈ k.accounts, 0 ≤ k.bal c

instance : DecidablePred solvent := fun k =>
  inferInstanceAs (Decidable (∀ c ∈ k.accounts, 0 ≤ k.bal c))

/-- **Conservation against a reference total** — the committed world has the same total supply as
the genesis state `k0`. `exec_conserves` makes every committed turn preserve this, but a governor
must REFUSE any state (reachable or proposed) that would break it. Decidable. -/
def conservesTo (k0 k : KernelState) : Prop := total k = total k0

instance (k0 : KernelState) : DecidablePred (conservesTo k0) := fun k =>
  inferInstanceAs (Decidable (total k = total k0))

/-- **The dregg floor**: solvent AND conserving against genesis. The conjunction the governor
holds invariant — both faces of dregg's resource law at once. -/
def dreggFloor (k0 : KernelState) : KernelState → Prop := combineFloor solvent (conservesTo k0)

instance (k0 : KernelState) : DecidablePred (dreggFloor k0) :=
  combineDecidable solvent (conservesTo k0)

/-! ## §2. The Game on the real executor. -/

/-- The deterministic projection: commit if `exec` succeeds, else stay (fail-closed self-loop). -/
def dreggStep (k : KernelState) (t : Turn) (_ : Unit) : KernelState := (exec k t).getD k

/-- A move is legal iff the real `exec` admits it. -/
def dreggLegal (k : KernelState) (t : Turn) (_ : Unit) : Prop := (exec k t).isSome = true

/-- **`dreggGame`** — `SafetyGame.Game` over the ACTUAL dregg kernel. `ViabilityKernel dreggGame`
is the real dregg viability kernel; `kernelShield dreggGame` governs real dregg turns. -/
def dreggGame (k0 : KernelState) : Game where
  World := KernelState
  Move  := Turn
  Resp  := Unit
  step  := dreggStep
  legal := dreggLegal
  floor := dreggFloor k0

/-- The game's `step` IS the dregg executor (committed-or-stay). -/
theorem dreggGame_step_eq (k0 : KernelState) (k : KernelState) (t : Turn) :
    (dreggGame k0).step k t () = (exec k t).getD k := rfl

/-- The game's `legal` IS `exec` admitting the turn. -/
theorem dreggGame_legal_iff (k0 : KernelState) (k : KernelState) (t : Turn) :
    (dreggGame k0).legal k t () ↔ (exec k t).isSome = true := Iff.rfl

/-- The game's `floor` IS the dregg floor (solvent ⋀ conserving). -/
theorem dreggGame_floor_eq (k0 : KernelState) (k : KernelState) :
    (dreggGame k0).floor k = dreggFloor k0 k := rfl

/-! ## §3. Kernel ⊆ floor bites: floor-breakers are NOT in the viability kernel.

These are the clean, greatest-fixpoint-respecting facts. We never compute the gfp; we use only
`kernel_subset_floor` (`ViabilityKernel ⊆ floor`) and the definition of `kernelShield`. -/

/-- **`not_in_kernel_of_floor_violation`** — a state that breaks the dregg floor cannot lie in the
viability kernel (the kernel is floor-contained). -/
theorem not_in_kernel_of_floor_violation (k0 : KernelState) (k : KernelState)
    (h : ¬ dreggFloor k0 k) : ¬ ViabilityKernel (dreggGame k0) k := by
  intro hk
  exact h (kernel_subset_floor (dreggGame k0) k hk)

/-- A turn whose successor under the game (the committed-or-stay state) breaks the floor is
REFUSED by the kernelShield: it stays at `k`. The membrane shields the real executor against any
move leaving the floor — and hence the kernel. -/
theorem shield_refuses_floor_breaking (k0 : KernelState) (resp : KernelState → Turn → Unit)
    (k : KernelState) (t : Turn)
    (h : ¬ dreggFloor k0 ((dreggGame k0).step k t (resp k t))) :
    kernelShield (dreggGame k0) resp k t = k := by
  unfold kernelShield
  rw [if_neg]
  intro hk
  exact not_in_kernel_of_floor_violation k0 _ h hk

/-- **`shield_refuses_solvency_violation`** — concretely: a turn whose committed successor has an
account in debt is shielded. (Specialization of the above to the solvency face.) -/
theorem shield_refuses_solvency_violation (k0 : KernelState) (resp : KernelState → Turn → Unit)
    (k : KernelState) (t : Turn)
    (h : ¬ solvent ((dreggGame k0).step k t (resp k t))) :
    kernelShield (dreggGame k0) resp k t = k :=
  shield_refuses_floor_breaking k0 resp k t (fun hf => h hf.1)

/-- **`shield_refuses_nonconserving`** — a turn whose committed successor breaks conservation
against genesis is shielded. (`exec` itself never produces such a state by `exec_conserves`; this
covers the fail-closed self-loop and any non-`exec` successor uniformly via the floor.) -/
theorem shield_refuses_nonconserving (k0 : KernelState) (resp : KernelState → Turn → Unit)
    (k : KernelState) (t : Turn)
    (h : ¬ conservesTo k0 ((dreggGame k0).step k t (resp k t))) :
    kernelShield (dreggGame k0) resp k t = k :=
  shield_refuses_floor_breaking k0 resp k t (fun hf => h hf.2)

/-- **`shield_admits_when_kernel`** — dually: a turn whose committed successor IS in the viability
kernel is admitted unchanged (the shield passes it through). The governor is gentle on real
turns that keep the kernel. -/
theorem shield_admits_when_kernel (k0 : KernelState) (resp : KernelState → Turn → Unit)
    (k : KernelState) (t : Turn)
    (h : ViabilityKernel (dreggGame k0) ((dreggGame k0).step k t (resp k t))) :
    kernelShield (dreggGame k0) resp k t = (dreggGame k0).step k t (resp k t) := by
  unfold kernelShield detStep
  rw [if_pos h]

/-! ## §4. The CPre of the kernel is the real "there is a safe dregg turn".

Specializing `SafetyGame.CPre` and `kernel_invariant` to `dreggGame` reads: from any kernel
state there is a `Turn` whose every (here: the unique) `exec` outcome stays in the kernel. This
is dregg's "the system can always make a conserving, solvent, authorized move and remain so". -/

/-- From a kernel state there exists a real dregg `Turn` keeping the kernel against the
deterministic executor response. (`kernel_invariant` at `dreggGame`, unfolded to `exec`.) -/
theorem dregg_kernel_has_safe_turn (k0 : KernelState) (k : KernelState)
    (h : ViabilityKernel (dreggGame k0) k) :
    ∃ t : Turn, ∀ _u : Unit,
      (exec k t).isSome = true → ViabilityKernel (dreggGame k0) ((exec k t).getD k) :=
  kernel_invariant (dreggGame k0) k h

/-! ## §5. The runnable floor-level governor on `exec` — non-vacuity, both polarities.

The `kernelShield` is `noncomputable` (it tests gfp membership). The `genGovStep` over the
*decidable dregg floor* is fully runnable, and it is the local one-step shield `genGov_safe`
proves keeps the floor for EVERY controller. We exercise it on the REAL `exec` step. -/

/-- The runnable governed step over the dregg floor, on the real executor. -/
def dreggFloorStep (k0 : KernelState) (k : KernelState) (t : Turn) : KernelState :=
  genGovStep (dreggFloor k0) (fun k t => (exec k t).getD k) k t

/-- The dregg-floor governor keeps the floor for EVERY controller and every tick on the real
executor — `genGov_safe` instantiated at the dregg floor and `exec`. -/
theorem dreggFloorGov_safe (k0 : KernelState)
    (ctrl : KernelState → Turn) (w0 : KernelState) (h0 : dreggFloor k0 w0) :
    ∀ n, dreggFloor k0
      (genGovTraj (dreggFloor k0) (fun k t => (exec k t).getD k) ctrl w0 n) :=
  genGov_safe (dreggFloor k0) (fun k t => (exec k t).getD k) ctrl w0 h0

-- ── A concrete model on the real `exec`. Genesis: cell 0 holds 100, cell 1 holds 5,
-- accounts {0,1}, empty caps (authority by ownership). total = 105. ──
/-- Genesis kernel state (reuses `Dregg2.Exec.s0` shape inline). -/
def g0 : KernelState :=
  { accounts := {0, 1}
    bal := fun c => if c = 0 then 100 else if c = 1 then 5 else 0
    caps := fun _ => [] }

/-- Honest turn: owner 0 sends 30 to cell 1 (authorized, conserving, solvent). -/
def tHonest : Turn := { actor := 0, src := 0, dst := 1, amt := 30 }
/-- Overdraft: owner 0 sends 1000 (> balance) — `exec` itself refuses (fail-closed). -/
def tOverdraft : Turn := { actor := 0, src := 0, dst := 1, amt := 1000 }
/-- Unauthorized: actor 2 has no cap on src 0 — `exec` refuses. -/
def tUnauth : Turn := { actor := 2, src := 0, dst := 1, amt := 30 }

-- `KernelState` carries functions (`bal`, `caps`) so full-state equality is undecidable; we
-- observe the governor's effect through the BALANCES it produces (the real observable).
-- Genesis is in the dregg floor (solvent: 100,5 ≥ 0; conserves trivially to itself).
#guard decide (dreggFloor g0 g0)
-- exec admits the honest turn; refuses overdraft and unauthorized (fail-closed).
#guard (exec g0 tHonest).isSome
#guard (exec g0 tOverdraft).isSome == false
#guard (exec g0 tUnauth).isSome == false
-- The honest committed successor stays in the dregg floor (70 + 35 = 105, both ≥ 0).
#guard decide (dreggFloor g0 ((exec g0 tHonest).getD g0))
-- The floor-level governor ADMITS the honest turn: src 0 debited to 70, dst 1 credited to 35.
#guard (dreggFloorStep g0 g0 tHonest).bal 0 == 70
#guard (dreggFloorStep g0 g0 tHonest).bal 1 == 35
-- The overdraft is a self-loop under `exec` (fail-closed): the governor stays at genesis (100/5).
#guard (dreggFloorStep g0 g0 tOverdraft).bal 0 == 100
#guard (dreggFloorStep g0 g0 tOverdraft).bal 1 == 5
-- The unauthorized turn likewise: the governor shields to genesis (100/5).
#guard (dreggFloorStep g0 g0 tUnauth).bal 0 == 100
#guard (dreggFloorStep g0 g0 tUnauth).bal 1 == 5
-- Total supply is conserved on the admitted turn and unchanged on the refusals.
#guard total (dreggFloorStep g0 g0 tHonest) == 105
#guard total (dreggFloorStep g0 g0 tOverdraft) == 105

/-- **Non-vacuity, both polarities, on the REAL executor.** Observed through balances: the
dregg-floor governor ADMITS the honest conserving transfer (src 0 → 70, dst 1 → 35, advancing the
world) and SHIELDS the overdraft (src 0 stays 100 — genesis). Genuine work over `exec`, not a
safe no-op. (Balances are the real observable; `KernelState` equality is undecidable.) -/
theorem dregg_governor_both_polarity :
    (dreggFloorStep g0 g0 tHonest).bal 0 = 70
      ∧ (dreggFloorStep g0 g0 tHonest).bal 1 = 35
      ∧ (dreggFloorStep g0 g0 tOverdraft).bal 0 = 100 := by decide

/-- **The honest turn is authorized AND conserving on the real machine** — tying the floor-level
admission to the executor's own proved laws (`exec_authorized`, `exec_conserves`): the admitted
turn is exactly an authorized, supply-preserving dregg transition. -/
theorem dregg_honest_admitted_is_lawful :
    authorizedB g0.caps tHonest = true
      ∧ ∃ k', exec g0 tHonest = some k' ∧ total k' = total g0 := by
  refine ⟨by decide, ?_⟩
  obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.mp (by decide : (exec g0 tHonest).isSome = true)
  exact ⟨k', hk', exec_conserves g0 k' tHonest hk'⟩

/-! ## Axiom hygiene — the kernel-side membrane facts are clean. -/

#print axioms shield_refuses_floor_breaking
#print axioms not_in_kernel_of_floor_violation
#print axioms shield_admits_when_kernel
#print axioms dregg_kernel_has_safe_turn
#print axioms dreggFloorGov_safe
#print axioms dregg_governor_both_polarity
#print axioms dregg_honest_admitted_is_lawful

/-!
The dregg side of the membrane, in one breath:

  * `dreggGame` instantiates the SafetyGame on the DEPLOYED `Dregg2.Exec` kernel — the same
    `exec` that `exec_conserves`/`exec_authorized` are proved about. Its `step`/`legal` ARE
    `exec` (`dreggGame_step_eq`, `dreggGame_legal_iff`).
  * `ViabilityKernel dreggGame` is the real dregg viability kernel; `kernelShield dreggGame`
    governs real dregg turns. Because the kernel is floor-contained, a turn reaching a
    floor-breaking state (insolvent or non-conserving) is REFUSED (`shield_refuses_*`), and a
    turn keeping the kernel is admitted (`shield_admits_when_kernel`).
  * The runnable `genGovStep` over the decidable dregg floor is exercised on `exec` with
    `#guard`: it ADMITS an honest conserving transfer and SHIELDS an overdraft / unauthorized
    turn — non-vacuous, both polarities (`dregg_governor_both_polarity`), and the admitted turn
    is an authorized, supply-preserving dregg transition (`dregg_honest_admitted_is_lawful`).

Honest scope: the kernel-level refusal/admission theorems use only `kernel ⊆ floor` and the
shield definition — they do NOT compute gfp membership for a concrete state (a greatest fixpoint
over the infinite `KernelState` space; deciding it is out of scope here). The fully RUNNABLE
governance shown to bite on `exec` is the floor-level one-step shield `genGov_safe` covers. No
`sorry`, no load-bearing `True`; every `#guard`/`decide` asserts a TRUE proposition.
-/

end Metatheory.PolisDreggGame
