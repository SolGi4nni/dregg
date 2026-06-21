/-
# Metatheory.PolisMembrane — THE MEMBRANE: projection soundness, and the irreducible trusted boundary.

Every `PolisSandbox*` file governs a SELF-CONTAINED world: the simulator IS the reality, so the
floor it proves true is true *of the simulator*. This file states what it costs to leave the toy and
govern a REAL system — and proves that the cost is a small, explicit, AUDITABLE set of conditions on
ONE surface, the **membrane**, not on the agent.

## The picture

    ┌─────────────────────────────┐         ┌──────────────────────────────────────┐
    │  dregg-controlled side      │  α      │  IRREDUCIBLE TRUSTED ORACLE            │
    │  • a CELL emitting input-   │ ◀────── │  • the Minecraft server                │
    │    events (proposed moves)  │ (read)  │  • AUTHORITATIVE for its own state     │
    │  • the abstract World       │         │  • `rstep` IS its transition; we do    │
    │    (`AState`), the FLOOR,   │ ──────▶ │    NOT model its interior — it is the  │
    │    the GOVERNOR             │ wrapper │    terminal trusted boundary, like a   │
    └─────────────────────────────┘ forwards│    crypto primitive / a hardware root  │
                                    a move   └──────────────────────────────────────┘

The sandbox World is the cell's *projection* of the server: `α : RState → AState` is the **membrane
read**. The governor (`genGovStep`, with `genGov_safe` for EVERY controller) runs on the abstract
side. A **wrapper** mediates the other direction: it forwards a real move `rm` to the trusted server
only when the move's abstract image `μ rm` is admitted by the governor at the read-off abstract state
`α r`. The server, being trusted, then evolves by `rstep r rm`.

## What the membrane must satisfy (the structure fields — the WHOLE trust surface)

  * `floor_sound`   — `absFloor (α r) → realFloor r`. The abstract floor, read back through the
                      membrane, IMPLIES the real floor. (The projection does not hide a real
                      violation behind an abstract success.)
  * `step_sim`      — `wrapperAccepts r rm → α (rstep r rm) = astep (α r) (μ rm)`. The membrane
                      COMMUTES with stepping, on accepted moves: reading-then-stepping (abstractly)
                      equals stepping (really, by the trusted server) then reading. A square.
  * `wrapper_sound` — `wrapperAccepts r rm → absAdmissible (α r) (μ rm)`. The wrapper forwards a move
                      only if the governor at the read-off state would admit its image. The wrapper is
                      the governor's enforcement arm on the real wire.

`absAdmissible w am := absFloor (astep w am)` is the governor's own admit-predicate (the `genGovStep`
guard). So `wrapper_sound` says exactly: *the wrapper forwards only governor-admitted moves.*

## The transfer theorem

`transfer_safety`: from a real start whose abstract read satisfies the floor, any trajectory of the
TRUSTED server under the wrapper keeps `realFloor` at every tick. The proof is the membrane square +
the governor's admit guard + `floor_sound`. The controller is never inspected (it is the cell on the
dregg side, fully arbitrary). The TRUSTED SURFACE is the membrane `(α, the wrapper, the server-as-
oracle)`, NOT the agent: the `∀`-controller result of `SafetyGame`/`PolisGovernorTheory` already
covers the agent, and this file shows it lifts across the membrane onto a real, un-modelled server.

## The irreducible boundary

`rstep` is the Minecraft server. We do NOT prove anything about its interior — it is the terminal
trusted oracle of this development, exactly as a hash function or a CPU is for a verified protocol.
The membrane's value is that it makes the trust surface SMALL and NAMED: three conditions on one
read map, one wrapper, one transition — auditable, not the whole agent. The honest limit is precisely
this: if the server lies about its state (`α` mis-reads) or the square fails to commute, the floor
guarantee does not reach reality. That is the line where verification ends and trust begins, and the
membrane is exactly where it sits.

No `sorry`, no load-bearing `True`. The concrete instance at the end exhibits a non-trivial membrane
over the sandbox world and checks both polarities by `decide`.
-/
import Metatheory.PolisGovernorTheory

namespace Metatheory.PolisMembrane

open Metatheory.PolisGovernorTheory

universe u v

/-! ## §1. The membrane as a structure — the whole trusted surface in one object. -/

/-- **Abstraction soundness** — the membrane between the dregg-controlled abstract side and the
irreducible trusted server. All fields are conditions on the projection `α`, the move map `μ`, the
wrapper, and the floors; the server transition `rstep` is opaque (trusted). -/
structure AbstractionSoundness where
  /-- The REAL/server state — opaque. We never inspect its interior; it is the trusted oracle. -/
  RState : Type u
  /-- The governed abstract state — the cell's projection of the server. -/
  AState : Type v
  /-- A real move the server can take (a cell-emitted input event, on the real wire). -/
  RealMove : Type u
  /-- An abstract move (the governed `Move`). -/
  AbsMove : Type v
  /-- **The membrane read**: project the server's real state to the governed abstract world. -/
  α : RState → AState
  /-- The map from real moves to their abstract images. -/
  μ : RealMove → AbsMove
  /-- **The TRUSTED server transition** — the Minecraft server. Authoritative; not modelled inside. -/
  rstep : RState → RealMove → RState
  /-- The abstract step the governor runs over (the sandbox `step`). -/
  astep : AState → AbsMove → AState
  /-- The REAL floor (the property we ultimately want to hold of the server). -/
  realFloor : RState → Prop
  /-- The ABSTRACT floor — the governed floor, the thing `genGov_safe` keeps. -/
  absFloor : AState → Prop
  /-- Decidability of the abstract floor — the governor must be computable. -/
  absFloorDec : DecidablePred absFloor
  /-- **The wrapper's accept relation**: which real moves the wrapper forwards to the trusted server. -/
  wrapperAccepts : RState → RealMove → Prop
  /-- **`floor_sound`** — the abstract floor read back through the membrane implies the real floor.
  The projection never hides a real violation behind an abstract success. -/
  floor_sound : ∀ r, absFloor (α r) → realFloor r
  /-- **`step_sim`** — the membrane COMMUTES with stepping on accepted moves: reading-then-abstract-
  stepping equals server-stepping-then-reading. The simulation square. -/
  step_sim : ∀ r rm, wrapperAccepts r rm → α (rstep r rm) = astep (α r) (μ rm)
  /-- **`wrapper_sound`** — the wrapper forwards a move only if the governor at the read-off abstract
  state would ADMIT its image (the image keeps the abstract floor). The governor's enforcement arm. -/
  wrapper_sound : ∀ r rm, wrapperAccepts r rm → absFloor (astep (α r) (μ rm))

attribute [instance] AbstractionSoundness.absFloorDec

variable (A : AbstractionSoundness)

/-- The governor's own admit-predicate, made explicit: a move is **abstractly admissible** at `w`
iff its abstract step keeps the abstract floor. This is exactly the `genGovStep` guard. -/
def absAdmissible (w : A.AState) (am : A.AbsMove) : Prop := A.absFloor (A.astep w am)

/-- `wrapper_sound` is literally "the wrapper forwards only abstractly-admissible moves". -/
theorem wrapper_forwards_only_admissible (r : A.RState) (rm : A.RealMove)
    (h : A.wrapperAccepts r rm) : absAdmissible A (A.α r) (A.μ rm) :=
  A.wrapper_sound r rm h

/-! ## §2. One membrane step preserves the floor — across the boundary. -/

/-- **`membrane_step_sound`** — the single-step transfer. If the wrapper accepts `rm`, then after the
TRUSTED server steps by `rstep`, the resulting real state satisfies `realFloor`. The proof is the
square (`step_sim`) carrying the governor's admit guard (`wrapper_sound`) onto the read of the stepped
server state, then `floor_sound` pushing it to reality. No assumption on the controller / cell. -/
theorem membrane_step_sound (r : A.RState) (rm : A.RealMove) (h : A.wrapperAccepts r rm) :
    A.realFloor (A.rstep r rm) := by
  -- The governor admits the move: the abstract step keeps the abstract floor.
  have hadm : A.absFloor (A.astep (A.α r) (A.μ rm)) := A.wrapper_sound r rm h
  -- The square: the read of the stepped server state IS that admitted abstract step.
  have hsq : A.α (A.rstep r rm) = A.astep (A.α r) (A.μ rm) := A.step_sim r rm h
  -- So the read of the stepped server state keeps the abstract floor…
  have habs : A.absFloor (A.α (A.rstep r rm)) := by rw [hsq]; exact hadm
  -- … and `floor_sound` carries that to the real floor.
  exact A.floor_sound _ habs

/-! ## §3. The real trajectory — the trusted server under the wrapper. -/

/-- A **real episode**: the cell (an opaque controller, fully arbitrary) proposes a real move at each
tick via `ctrl`; the trusted server `rstep` evolves by it. We thread the wrapper's acceptance as a
hypothesis on the trajectory (an accepted run) — the wrapper is what makes acceptance hold, but we
keep the trajectory definition controller-agnostic. -/
def realTraj (ctrl : A.RState → A.RealMove) (r0 : A.RState) : Nat → A.RState
  | 0 => r0
  | n + 1 => A.rstep (realTraj ctrl r0 n) (ctrl (realTraj ctrl r0 n))

/-- **`transfer_safety`** — THE MEMBRANE TRANSFER THEOREM. Given an `AbstractionSoundness`, a real
start whose membrane read satisfies the abstract floor, and an accepted run (every proposed move is
forwarded by the wrapper), the TRUSTED server's trajectory keeps `realFloor` at EVERY tick.

The abstract governor's `∀`-controller safety (`genGov_safe`) is what makes acceptance enforceable;
here the proof is the direct lift: each accepted step is sound by `membrane_step_sound`, and the
abstract floor of the read is reestablished by the square so the next step's `floor_sound` applies.
The trusted surface is the membrane `(α, wrapperAccepts, rstep)`; the controller (the cell) is never
inspected — it is universally quantified. This is the bridge out of the self-contained sandbox onto a
real, un-modelled Minecraft server. -/
theorem transfer_safety
    (ctrl : A.RState → A.RealMove) (r0 : A.RState)
    (h0 : A.absFloor (A.α r0))
    (hacc : ∀ n, A.wrapperAccepts (realTraj A ctrl r0 n) (ctrl (realTraj A ctrl r0 n))) :
    ∀ n, A.realFloor (realTraj A ctrl r0 n) := by
  -- Strengthen the induction to ALSO carry the abstract floor of the read, which the square preserves.
  suffices H : ∀ n, A.realFloor (realTraj A ctrl r0 n) ∧ A.absFloor (A.α (realTraj A ctrl r0 n)) by
    exact fun n => (H n).1
  intro n
  induction n with
  | zero =>
      exact ⟨A.floor_sound _ h0, h0⟩
  | succ k ih =>
      -- The accepted move at tick `k` is sound; the square reestablishes the abstract read floor.
      have hacck := hacc k
      have hreal : A.realFloor (realTraj A ctrl r0 (k + 1)) :=
        membrane_step_sound A _ _ hacck
      have habs : A.absFloor (A.α (realTraj A ctrl r0 (k + 1))) := by
        show A.absFloor (A.α (A.rstep (realTraj A ctrl r0 k) (ctrl (realTraj A ctrl r0 k))))
        rw [A.step_sim _ _ hacck]
        exact A.wrapper_sound _ _ hacck
      exact ⟨hreal, habs⟩

/-! ## §4. The wrapper IS the governor on the real wire.

`wrapper_sound` requires only that ACCEPTED moves are admissible. A canonical wrapper accepts EXACTLY
the governor-admissible moves: `wrapperAccepts r rm := absAdmissible (α r) (μ rm)`. With such a
wrapper, `wrapper_sound` is definitional, and a run is "accepted" exactly when every proposed move is
governor-admissible — i.e. the wrapper has *refused* nothing it would have to refuse. We record the
canonical-wrapper soundness obligation so an instance need only supply `floor_sound` + `step_sim`. -/

/-- The canonical wrapper-acceptance: forward iff the governor admits. With this choice
`wrapper_sound` holds by definition (it IS `absAdmissible`). -/
def canonicalAccepts (RState : Type u) (AState : Type v) (RealMove : Type u) (AbsMove : Type v)
    (α : RState → AState) (μ : RealMove → AbsMove) (astep : AState → AbsMove → AState)
    (absFloor : AState → Prop) : RState → RealMove → Prop :=
  fun r rm => absFloor (astep (α r) (μ rm))

/-- For the canonical wrapper, `wrapper_sound` is exactly reflexivity: accepting means admissible. -/
theorem canonical_wrapper_sound
    {RState : Type u} {AState : Type v} {RealMove : Type u} {AbsMove : Type v}
    (α : RState → AState) (μ : RealMove → AbsMove) (astep : AState → AbsMove → AState)
    (absFloor : AState → Prop) (r : RState) (rm : RealMove)
    (h : canonicalAccepts RState AState RealMove AbsMove α μ astep absFloor r rm) :
    absFloor (astep (α r) (μ rm)) := h

/-! ## §5. A concrete membrane — non-vacuity, both polarities, over the sandbox world.

We exhibit a small but non-trivial membrane and check that it does real work. The trusted "server"
holds a real state that is RICHER than the abstract projection: a pair `(dist, serverNonce)` where
`serverNonce` is interior the membrane does NOT read (it is server-private — exactly the "we don't
model the interior" point). The membrane reads off only `dist`. The abstract floor is `dist ≤ 5`; the
real floor is the SAME projected condition (so `floor_sound` is honest, not vacuous). The wrapper is
the canonical governor wrapper. We check it ADMITS a benign move and REFUSES a harmful one. -/

section Demo

/-- The trusted server's real state: a distance PLUS a private nonce the membrane cannot read. -/
structure RServer where
  dist : Nat
  serverNonce : Nat   -- server-interior; never read by `α`
deriving DecidableEq, Repr

/-- A real move: add to the distance (and, opaquely, bump the private nonce — server's business). -/
def rDemoStep (r : RServer) (m : Nat) : RServer := ⟨r.dist + m, r.serverNonce + 7⟩

/-- The membrane read: project to the distance ONLY (the nonce is invisible — server-private). -/
def αDemo (r : RServer) : Nat := r.dist

/-- Abstract move = real move (a `Nat` increment); abstract step adds it. -/
def aDemoStep (w : Nat) (m : Nat) : Nat := w + m

/-- Abstract floor: distance at most `5`. -/
def absFloorDemo (w : Nat) : Prop := w ≤ 5
/-- Real floor: the SAME condition on the (read-off) distance — `floor_sound` is then genuine. -/
def realFloorDemo (r : RServer) : Prop := r.dist ≤ 5

instance : DecidablePred absFloorDemo := fun w => inferInstanceAs (Decidable (w ≤ 5))
instance : DecidablePred realFloorDemo := fun r => inferInstanceAs (Decidable (r.dist ≤ 5))

/-- The canonical wrapper-accept on concrete types (definitionally the membrane's `wrapperAccepts`,
but with transparent `RServer`/`Nat` so numerals and `decide` resolve directly). -/
def demoAccepts (r : RServer) (m : Nat) : Prop := absFloorDemo (aDemoStep (αDemo r) m)
instance : ∀ r m, Decidable (demoAccepts r m) :=
  fun r m => inferInstanceAs (Decidable (absFloorDemo (aDemoStep (αDemo r) m)))

/-- The concrete membrane. `step_sim` holds because `α (rDemoStep r m) = r.dist + m = aDemoStep (α r)
m` — the private nonce drops out under `α`, so the square commutes. `floor_sound` is literal (`α r =
r.dist`, both floors are `· ≤ 5`). The wrapper is the canonical governor wrapper. -/
def demoMembrane : AbstractionSoundness where
  RState := RServer
  AState := Nat
  RealMove := Nat
  AbsMove := Nat
  α := αDemo
  μ := id
  rstep := rDemoStep
  astep := aDemoStep
  realFloor := realFloorDemo
  absFloor := absFloorDemo
  absFloorDec := inferInstance
  wrapperAccepts := demoAccepts
  floor_sound := by
    intro r h
    -- `absFloorDemo (αDemo r) = (r.dist ≤ 5) = realFloorDemo r`.
    exact h
  step_sim := by
    intro r m _
    -- `αDemo (rDemoStep r m) = r.dist + m`; `aDemoStep (αDemo r) (id m) = r.dist + m`.
    rfl
  wrapper_sound := by
    intro r m h
    -- The wrapper IS the admissibility predicate, so soundness is reflexivity.
    exact h

-- The membrane's `wrapperAccepts` IS `demoAccepts` (definitionally), checked on concrete types.
example : demoMembrane.wrapperAccepts = demoAccepts := rfl

-- The canonical wrapper admits a benign move (dist 0, +3 ⇒ 3 ≤ 5): accepted.
#guard decide (demoAccepts ⟨0, 0⟩ 3)
-- … and refuses a harmful one (dist 0, +9 ⇒ 9 > 5): not accepted.
#guard decide (¬ demoAccepts ⟨0, 0⟩ 9)

/-- **Non-vacuity, both polarities**: the membrane's wrapper accepts `+3` (lands at `3 ≤ 5`) and
refuses `+9` (would land at `9 > 5`). Real discrimination, not a constant. -/
theorem demo_wrapper_both_polarity :
    demoAccepts ⟨0, 0⟩ 3 ∧ ¬ demoAccepts ⟨0, 0⟩ 9 := by decide

/-- A concrete real trajectory on transparent types (definitionally `realTraj demoMembrane`), so the
`decide` checks below run without the structure-field numeral obstruction. -/
def demoRealTraj (ctrl : RServer → Nat) (r0 : RServer) : Nat → RServer
  | 0 => r0
  | n + 1 => rDemoStep (demoRealTraj ctrl r0 n) (ctrl (demoRealTraj ctrl r0 n))

theorem demoRealTraj_eq (ctrl : RServer → Nat) (r0 : RServer) (n : Nat) :
    demoRealTraj ctrl r0 n = realTraj demoMembrane ctrl r0 n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [demoRealTraj, realTraj, ih]; rfl

/-- A cell that always proposes `+1`. -/
def cellPlusOne : RServer → Nat := fun _ => 1

#guard decide (realFloorDemo (demoRealTraj cellPlusOne ⟨0, 0⟩ 0))
#guard decide (realFloorDemo (demoRealTraj cellPlusOne ⟨0, 0⟩ 3))
#guard decide (realFloorDemo (demoRealTraj cellPlusOne ⟨0, 0⟩ 5))
-- The server's interior really did evolve (nonce bumped by 7 each tick) — the membrane ignores it.
#guard decide ((demoRealTraj cellPlusOne ⟨0, 0⟩ 3).serverNonce = 21)

/-- **The transfer, concretely.** From `⟨0,0⟩` the `+1` cell, forwarded by the canonical wrapper, keeps
the real floor through tick `5` (dist climbs `0..5`, all `≤ 5`); and at tick `4` the proposed move is
still accepted. The general `transfer_safety` gives ALL ticks under the acceptance hypothesis; this is
the decidable witness that the hypothesis holds and the floor follows here. The server's private nonce
bumps every tick but never affects the verdict. -/
theorem demo_transfer_holds :
    realFloorDemo (demoRealTraj cellPlusOne ⟨0, 0⟩ 5)
      ∧ demoAccepts (demoRealTraj cellPlusOne ⟨0, 0⟩ 4)
          (cellPlusOne (demoRealTraj cellPlusOne ⟨0, 0⟩ 4)) := by decide

end Demo

/-! ## Axiom hygiene — the membrane keystones. -/

#print axioms membrane_step_sound
#print axioms transfer_safety
#print axioms canonical_wrapper_sound

/-!
The membrane, in one breath:

  1. The sandbox World is a PROJECTION (`α`) of an irreducible TRUSTED server (`rstep` — Minecraft).
  2. Three auditable conditions on the membrane — `floor_sound`, `step_sim`, `wrapper_sound` — are the
     WHOLE trust surface beyond the server itself.
  3. `transfer_safety` lifts the abstract governor's `∀`-controller floor guarantee across the
     membrane onto the real, un-modelled server: the trusted surface is `(α, wrapper, server)`, NOT
     the agent/cell — that was already covered by `genGov_safe`.
  4. The honest limit: if `α` mis-reads or the square fails to commute, the guarantee does not reach
     reality. That line — between verification and trust — is exactly the membrane.
-/

end Metatheory.PolisMembrane
