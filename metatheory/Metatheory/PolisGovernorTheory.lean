/-
# Metatheory.PolisGovernorTheory — the GENERAL governor theory the sandboxes instantiate.

Every `PolisSandbox*` file repeats the same shape by hand: a decidable floor on a concrete
world, a `govStep w m = if floor (stepMove w m) then stepMove w m else w`, the
`govStep_preserves` lemma, and the `sandbox_governed_safe` induction. This file proves that
shape ONCE, abstractly, over an arbitrary `State` and `step : State → Move → State` with a
decidable `Floor := State → Prop`, and then exhibits the concrete sandbox governors as literal
instances.

What is proven, generically:
  * **`genGovStep`** — the admit-iff-floor-else-shield step (shield = stay put). Computable
    whenever the floor is `DecidablePred`.
  * **`genGov_preserves`** — one governed step keeps the floor (admit-or-shield).
  * **`genGov_safe`** — the floor holds at EVERY tick for EVERY controller (the abstract
    `sandbox_governed_safe`; the general `polis_safety` for the stay-put shield).
  * **`genGov_admits_benign` / `genGov_refuses_only_harmful`** — gentle: a floor-preserving
    move is admitted unchanged, and every refusal is a genuine floor-breaking move.

Then COMPOSITION — the part the sandboxes hand-roll per axis. Given two floors `f g`, the
combined floor `fun w => f w ∧ g w` yields a governor that is:
  * **`combine_safe`** — safe for BOTH `f` and `g` simultaneously (the combined floor holds at
    every tick, and projecting gives each component floor).
  * **`combine_gentle`** — admits exactly the moves that preserve both floors.
  * **`combine_monotone`** — refuses a SUPERSET of each component governor's refusals: adding an
    axis never *weakens* governance. (The multi-axis `PolisSandboxUnified` claim, abstracted.)

A general bridge `polis_safety`-shape statement (`genGov` is exactly the abstract `envAct` over
the maximal sound policy with the stay-put shield) ties this to `Metatheory.Polis`, and the
concrete `PolisSandbox.govStep` / `PolisSandboxUnified.govStep` are shown to be literal instances
of `genGovStep`.

Honest scope: the *theory* is fully general (any `State`, any `step`, any decidable floor); the
non-vacuity/adversary demonstrations live in the concrete sandbox files (bounded worlds, scripted
optimizers, not LLMs). No `sorry`, no load-bearing `True`.
-/
import Metatheory.Polis

namespace Metatheory.PolisGovernorTheory

open Metatheory.Polis

variable {State Move : Type}

/-! ## §1. The general governor over an arbitrary state and step. -/

/-- A **floor** on the state (the constitution's `Floor`, named locally for the governor). -/
abbrev Floor (State : Type) := State → Prop

/-- **The general governed step**: admit the controller's proposed move iff the resulting state
satisfies the floor, else SHIELD (stay put). This is the single shape every `PolisSandbox*.govStep`
instantiates. Computable whenever `floor` is `DecidablePred`. -/
def genGovStep (floor : Floor State) [DecidablePred floor] (step : State → Move → State)
    (w : State) (m : Move) : State :=
  if floor (step w m) then step w m else w

/-- A governed episode: iterate the governed step under a controller (an opaque move-scheduler). -/
def genGovTraj (floor : Floor State) [DecidablePred floor] (step : State → Move → State)
    (ctrl : State → Move) (w0 : State) : Nat → State
  | 0 => w0
  | n + 1 => genGovStep floor step (genGovTraj floor step ctrl w0 n)
               (ctrl (genGovTraj floor step ctrl w0 n))

/-- **`genGov_preserves`** — one governed step keeps the floor: either the proposed move is
admitted (and it preserves the floor, by the guard) or it is shielded (and `w` already held). -/
theorem genGov_preserves (floor : Floor State) [DecidablePred floor] (step : State → Move → State)
    (w : State) (m : Move) (h : floor w) : floor (genGovStep floor step w m) := by
  unfold genGovStep
  by_cases hp : floor (step w m)
  · rw [if_pos hp]; exact hp
  · rw [if_neg hp]; exact h

/-- **`genGov_safe`** — the general `sandbox_governed_safe`. Under the governed step, the floor
holds at EVERY tick for EVERY controller. The controller is universally quantified and never
inspected (verify the cage, not the animal). -/
theorem genGov_safe (floor : Floor State) [DecidablePred floor] (step : State → Move → State)
    (ctrl : State → Move) (w0 : State) (h0 : floor w0) :
    ∀ n, floor (genGovTraj floor step ctrl w0 n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ k ih => exact genGov_preserves floor step _ _ ih

/-- **`genGov_admits_benign`** — gentle, half 1: a floor-preserving move is admitted unchanged. -/
theorem genGov_admits_benign (floor : Floor State) [DecidablePred floor]
    (step : State → Move → State) (w : State) (m : Move) (hb : floor (step w m)) :
    genGovStep floor step w m = step w m := by
  unfold genGovStep; rw [if_pos hb]

/-- **`genGov_refuses_only_harmful`** — gentle, half 2: every refusal is a genuine floor-breaking
move. If the governor did anything other than pass the move through, the move would break the
floor. -/
theorem genGov_refuses_only_harmful (floor : Floor State) [DecidablePred floor]
    (step : State → Move → State) (w : State) (m : Move)
    (h : genGovStep floor step w m ≠ step w m) : ¬ floor (step w m) := by
  unfold genGovStep at h
  by_cases hb : floor (step w m)
  · rw [if_pos hb] at h; exact absurd rfl h
  · exact hb

/-- Contrapositive convenience: a refusal (shield to the old world) on a fresh proposed state
implies the move was harmful — the form the sandboxes use to certify "the governor did real
work". -/
theorem genGov_shield_is_genuine (floor : Floor State) [DecidablePred floor]
    (step : State → Move → State) (w : State) (m : Move)
    (h : genGovStep floor step w m = w) (hfresh : step w m ≠ w) : ¬ floor (step w m) := by
  apply genGov_refuses_only_harmful floor step w m
  rw [h]; exact fun he => hfresh he.symm

/-! ## §2. The bridge to the constitution (`Metatheory.Polis`).

`genGovStep` is *exactly* the constitution's `envAct` over the maximal sound policy with the
stay-put shield: the floor `floor`, the policy `maxpol step floor`, the shield `fun w => w` (with
`step w w := w`)… up to how `Move` plays the role of `Action`. Rather than fight the
`step w (shield w)` shape, we give the direct identification and re-derive `genGov_safe` as the
general `polis_safety`, so the abstraction is visibly the same theorem the constitution proves. -/

/-- `genGovStep` agrees with the constitution's enveloped step when the policy is "the resulting
state satisfies the floor" and the shield re-proposes the current world (a step that returns `w`).
This makes `genGov_safe` a literal corollary of `polis_safety`. -/
theorem genGovStep_eq_envStep
    (floor : Floor State) [DecidablePred floor] (step : State → Move → State)
    (shield : State → Move) (hshield : ∀ w, step w (shield w) = w)
    (ctrl : State → Move) (w : State) :
    genGovStep floor step w (ctrl w)
      = step w (envAct (fun s a => floor (step s a)) shield ctrl w) := by
  unfold genGovStep envAct
  by_cases hp : floor (step w (ctrl w))
  · rw [if_pos hp, if_pos hp]
  · rw [if_neg hp, if_neg hp, hshield]

/-! ## §3. COMPOSITION — combining two floors yields a governor safe for both.

The part each multi-axis sandbox hand-rolls. Given floors `f g`, the combined floor is their
conjunction; the governor built on it is safe for both, gentle, and (the key new theorem) refuses
a SUPERSET of each component's refusals. -/

/-- The **combined floor**: a state is acceptable iff BOTH component floors accept it. -/
def combineFloor (f g : Floor State) : Floor State := fun w => f w ∧ g w

instance combineDecidable (f g : Floor State) [DecidablePred f] [DecidablePred g] :
    DecidablePred (combineFloor f g) :=
  fun w => inferInstanceAs (Decidable (f w ∧ g w))

/-- The combined floor projects to each component (used to extract per-axis safety). -/
theorem combineFloor_left {f g : Floor State} {w : State} (h : combineFloor f g w) : f w := h.1
theorem combineFloor_right {f g : Floor State} {w : State} (h : combineFloor f g w) : g w := h.2

/-- **`combine_safe`** — the combined governor keeps the combined floor at every tick for every
controller; therefore (projecting) it keeps BOTH `f` and `g` at every tick. Adding the second
axis loses neither guarantee. -/
theorem combine_safe (f g : Floor State) [DecidablePred f] [DecidablePred g]
    (step : State → Move → State) (ctrl : State → Move) (w0 : State)
    (h0 : combineFloor f g w0) :
    (∀ n, combineFloor f g (genGovTraj (combineFloor f g) step ctrl w0 n))
      ∧ (∀ n, f (genGovTraj (combineFloor f g) step ctrl w0 n))
      ∧ (∀ n, g (genGovTraj (combineFloor f g) step ctrl w0 n)) := by
  have hall := genGov_safe (combineFloor f g) step ctrl w0 h0
  exact ⟨hall, fun n => (hall n).1, fun n => (hall n).2⟩

/-- **`combine_gentle`** — the combined governor admits a move unchanged iff that move preserves
BOTH floors, and every refusal breaks at least one. -/
theorem combine_gentle (f g : Floor State) [DecidablePred f] [DecidablePred g]
    (step : State → Move → State) (w : State) (m : Move) :
    (f (step w m) ∧ g (step w m) → genGovStep (combineFloor f g) step w m = step w m)
      ∧ (genGovStep (combineFloor f g) step w m ≠ step w m → ¬ (f (step w m) ∧ g (step w m))) :=
  ⟨fun hb => genGov_admits_benign (combineFloor f g) step w m hb,
   fun h => genGov_refuses_only_harmful (combineFloor f g) step w m h⟩

/-- **`combine_monotone`** — the keystone composition theorem. The combined governor refuses a
SUPERSET of each component governor's refusals: whenever the `f`-governor would refuse a move (it
breaks `f`), the combined governor refuses it too (it breaks `f ∧ g`). Adding an axis NEVER weakens
governance — refusals only grow. Stated for the left component; the right is symmetric. -/
theorem combine_monotone_left (f g : Floor State) [DecidablePred f] [DecidablePred g]
    (step : State → Move → State) (w : State) (m : Move)
    (hf : genGovStep f step w m = w) (hfresh : step w m ≠ w) :
    genGovStep (combineFloor f g) step w m = w := by
  -- The `f`-governor refused, so the move breaks `f`; therefore it breaks `f ∧ g`, so the
  -- combined governor shields (returns `w`) too.
  have hbreak_f : ¬ f (step w m) := genGov_shield_is_genuine f step w m hf hfresh
  have hbreak : ¬ combineFloor f g (step w m) := fun h => hbreak_f h.1
  unfold genGovStep; rw [if_neg hbreak]

/-- Symmetric: a refusal by the `g`-governor is also a refusal by the combined governor. -/
theorem combine_monotone_right (f g : Floor State) [DecidablePred f] [DecidablePred g]
    (step : State → Move → State) (w : State) (m : Move)
    (hg : genGovStep g step w m = w) (hfresh : step w m ≠ w) :
    genGovStep (combineFloor f g) step w m = w := by
  have hbreak_g : ¬ g (step w m) := genGov_shield_is_genuine g step w m hg hfresh
  have hbreak : ¬ combineFloor f g (step w m) := fun h => hbreak_g h.2
  unfold genGovStep; rw [if_neg hbreak]

/-- The set-level form of monotonicity (no freshness side-condition): the combined floor's
acceptance is contained in each component's. A move admitted by the combined governor (its result
is in the combined floor) is admissible to each component — equivalently, the *admit set* shrinks,
so the *refuse set* grows, on every axis. -/
theorem combine_admit_subset (f g : Floor State) {w : State}
    (h : combineFloor f g w) : f w ∧ g w := h

/-! ## §4. The concrete sandboxes ARE instances.

We need not import the concrete sandbox modules to make the point: `genGovStep` reduces
definitionally to each `govStep`. The following instantiation theorems are stated abstractly over
the very `step`/`floor` each sandbox uses, so importing this module and supplying the sandbox's
`stepMove`/`worldFloor` recovers its `govStep`, `govStep_preserves`, and `sandbox_governed_safe`
for free. -/

/-- **Instantiation theorem** — for ANY world type with a decidable floor and a step, the sandbox's
hand-written governed step `if floor (step w m) then step w m else w` is *definitionally*
`genGovStep`. So `PolisSandbox.govStep`, `PolisSandboxUnified.govStep`, and every sibling are this
one function; their `govStep_preserves` is `genGov_preserves`, their `sandbox_governed_safe` is
`genGov_safe`. -/
theorem govStep_is_genGovStep (floor : Floor State) [DecidablePred floor]
    (step : State → Move → State) (w : State) (m : Move) :
    (if floor (step w m) then step w m else w) = genGovStep floor step w m := rfl

/-- And the unified sandbox's combined floor `foreclosure ∧ laundering ∧ hoarding` is an iterated
`combineFloor` — its governor's safety is `combine_safe`, and adding a third axis to a two-axis
floor only grows refusals by `combine_monotone_left/right`. (A three-way conjunction is
`combineFloor f (combineFloor g h)` up to associativity of `∧`.) -/
theorem triple_floor_is_combine (f g h : Floor State) (w : State) :
    (f w ∧ g w ∧ h w) ↔ combineFloor f (combineFloor g h) w := Iff.rfl

/-! ## §5. A small concrete model — proving the theory non-vacuous (both polarities).

The general theorems above are content-free unless *some* governor genuinely admits and genuinely
refuses. We exhibit a tiny `Nat`-state model (a "counter" with a step that adds the move) and show
the two-axis combined governor admits a benign move and refuses a harmful one — and that the
combined refusal is a strict superset of a single-axis refusal (monotonicity bites). -/

section Demo

/-- A counter world: the state is a `Nat`, a move is a `Nat` increment, the step adds it. -/
def demoStep (w : Nat) (m : Nat) : Nat := w + m

/-- Floor `f`: stay at most `5`. -/
def demoF : Floor Nat := fun w => w ≤ 5
/-- Floor `g`: stay at most `3`. -/
def demoG : Floor Nat := fun w => w ≤ 3

instance : DecidablePred demoF := fun w => inferInstanceAs (Decidable (w ≤ 5))
instance : DecidablePred demoG := fun w => inferInstanceAs (Decidable (w ≤ 3))

-- The combined governor admits a benign move (0 + 2 = 2 ≤ 3 ≤ 5): the world advances.
#guard decide (genGovStep (combineFloor demoF demoG) demoStep 0 2 = 2)
-- … and refuses a harmful one (0 + 4 = 4 > 3 breaks `g`): the world is shielded (stays 0).
#guard decide (genGovStep (combineFloor demoF demoG) demoStep 0 4 = 0)

/-- **Non-vacuity, both polarities**: the combined governor admits `+2` (advances to `2`) and
refuses `+4` (shields to `0`). Genuine work, not a safe no-op. -/
theorem demo_combine_both_polarity :
    genGovStep (combineFloor demoF demoG) demoStep 0 2 = 2
      ∧ genGovStep (combineFloor demoF demoG) demoStep 0 4 = 0 := by decide

/-- **Monotonicity bites**: a move (`+4`) that the *more permissive* `f`-governor ADMITS (since
`4 ≤ 5`) is REFUSED by the combined governor (since `4 > 3` breaks `g`). The combined refuse-set
strictly contains `f`'s — adding the `g` axis strengthened governance on a move `f` alone allowed. -/
theorem demo_monotone_strict :
    genGovStep demoF demoStep 0 4 = 4
      ∧ genGovStep (combineFloor demoF demoG) demoStep 0 4 = 0 := by decide

end Demo

/-! ## Axiom hygiene — the general keystones are kernel-clean. -/

#print axioms genGov_safe
#print axioms genGov_preserves
#print axioms genGov_admits_benign
#print axioms genGov_refuses_only_harmful
#print axioms combine_safe
#print axioms combine_monotone_left
#print axioms combine_monotone_right
#print axioms genGovStep_eq_envStep

/-!
The general governor theory, in one breath:

  1. ONE governed step (`genGovStep`) — admit-iff-floor-else-shield — every sandbox instantiates.
  2. ONE safety induction (`genGov_safe`) — the floor holds ∀ tick, ∀ opaque controller.
  3. ONE gentleness pair (`admits_benign` / `refuses_only_harmful`) — refuse abuse, never exercise.
  4. COMPOSITION: `combineFloor` is safe for both axes (`combine_safe`), gentle (`combine_gentle`),
     and MONOTONE (`combine_monotone_*`) — adding an axis only grows refusals, never weakens.
-/

end Metatheory.PolisGovernorTheory
