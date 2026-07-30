/-
# Dregg2.Circuit.Emit.MinaFixtureEmit — the Mina-bridge fixture AIR, AUTHORED IN LEAN (law #1).

## What this file IS

`bridge/mina-zkapp/src/DreggProofVerify.ts` is an o1js/Kimchi circuit that verifies a REAL dregg
FRI-STARK proof. The proof it consumes is minted by `circuit/src/bin/mina_stark_fixture.rs` over a
small AIR chosen to exercise every arm the STARK protocol arithmetic has: all three Lagrange
selectors, a next-row reference, public values in the transcript AND in a constraint, and a
degree-3 constraint so the quotient really splits into more than one chunk.

That AIR was HAND-WRITTEN IN RUST (`impl<AB: AirBuilder> Air<AB> for MinaFixtureAir`, landed
`6ce0c7a14`, caught red by `law1_enforcement_gate::law1_no_new_rust_authored_constraints` and
recorded as HORIZONLOG E4). **This module is its Lean author.** The Rust binary now reads the
emitted descriptor and interprets it (`Ir2UniAir`); it constructs no algebra.

## The trace and the four constraints

Columns `[a, b, c]` = `[0, 1, 2]`, public values `[c_first, c_last]`:

    C0                  b - a^3          (degree 3 — this is what forces n_chunks > 1)
    C1  is_first_row *  c - pi[0]
    C2  is_transition * c' - c - b       (the only next-row reference)
    C3  is_last_row  *  c - pi[1]

⚑ **THE LIST ORDER IS THE FOLDING ORDER.** `VerifierConstraintFolder::assert_zero` accumulates
`acc = acc * alpha + C` (`uni-stark/src/folder.rs`), so a permuted list is a different accumulator
and a different proof. `Ir2UniAir` walks `constraints` in LIST ORDER precisely so that this Lean
list — not an accident of a Rust traversal's grouping — is the authority the o1js twin
(`minaFixtureConstraints` in `DreggProofVerify.ts`) must agree with. The twin keeps a
`minaFixtureConstraintsPermuted` negative that must REFUSE; that negative is a statement about
THIS list.

## What is proved here

* `mina_forces_cube` / `mina_forces_first_pi` / `mina_forces_running_sum` / `mina_forces_last_pi` —
  the FORCING direction, one per constraint: a window that satisfies the emitted descriptor HAS
  the intended shape. These name the emitted `minaFixtureDesc.constraints`, not a paraphrase.
* `mina_window_holds_of_shape` — the converse: the intended shape satisfies every emitted
  constraint. Together with the forcings this is an IFF, so the descriptor is neither vacuous
  (something satisfies it) nor trivial (something does not).
* `mina_refuses_bent_degree` — the `a^3 → a^2` bend the o1js side keeps as a live counter-example
  (`minaFixtureConstraintsBentDegree`) is REFUSED in the denotation, with a concrete witness.

## Axiom hygiene

`#assert_axioms` on the two teeth. NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.EffectVmEmitTransfer

namespace Dregg2.Circuit.Emit.MinaFixtureEmit

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff not_modEq_zero_of_canon)

set_option autoImplicit false

/-! ## §1 — The AIR. -/

/-- Trace column `a` (the cubed input). -/
def colA : Nat := 0
/-- Trace column `b`, pinned to `a^3`. -/
def colB : Nat := 1
/-- Trace column `c`, the running sum of `b`. -/
def colC : Nat := 2

/-- `C0`'s body: `b - a^3`. Degree 3 — the constraint that forces more than one quotient chunk. -/
def c0Body : WindowExpr :=
  .add (.loc colB) (.mul (.const (-1)) (.mul (.loc colA) (.mul (.loc colA) (.loc colA))))

/-- `C2`'s body: `c' - c - b`. The AIR's only next-row reference, so `zeta` and `g*zeta` are both
opened and the DEEP quotient runs at two points. -/
def c2Body : WindowExpr :=
  .add (.nxt colC) (.add (.mul (.const (-1)) (.loc colC)) (.mul (.const (-1)) (.loc colB)))

/-- The four constraints, IN FOLDING ORDER (see the header). -/
def minaFixtureConstraints : List VmConstraint2 :=
  [ .windowGate { body := c0Body, onTransition := false }
  , .base (.piBinding .first colC 0)
  , .windowGate { body := c2Body, onTransition := true }
  , .base (.piBinding .last colC 1) ]

/-- The fixture descriptor. No tables, no hash sites, no ranges — it rides plain `p3_uni_stark`,
which has no bus, and `Ir2UniAir::new` REFUSES a descriptor that declares any of them. -/
def minaFixtureDesc : EffectVmDescriptor2 :=
  { name        := "dregg-mina-stark-fixture-v1"
  , traceWidth  := 3
  , piCount     := 2
  , tables      := []
  , constraints := minaFixtureConstraints
  , hashSites   := []
  , ranges      := [] }

/-! ## §2 — The FULL byte-pin: `circuit/descriptors/by-name/mina-fixture.json` is THIS string.

`circuit/src/bin/mina_stark_fixture.rs` `include_str!`s that file and decodes it with
`parse_vm_descriptor2`, so `Lean-emit ≡ golden ≡ Rust-decode` is closed on all three sides: a drift
on any one of them breaks this `#guard`, the binary's shape assertions, or
`scripts/check-descriptor-drift.sh` (this descriptor is routed in `metatheory/EmitByName.lean`, so
the drift gate RE-DERIVES the artifact from this module on every run). -/

#guard emitVmJson2 minaFixtureDesc ==
  "{\"name\":\"dregg-mina-stark-fixture-v1\",\"ir\":2,\"trace_width\":3,\"public_input_count\":2,\"tables\":[],\"constraints\":[{\"t\":\"window_gate\",\"on_transition\":false,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":0},\"r\":{\"t\":\"loc\",\"c\":0}}}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":0},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":2},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":2}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":1}}}}},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":2,\"pi_index\":1}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §2a — Shape tripwires (the Rust decoder asserts the SAME shape on its decoded twin). -/

#guard minaFixtureDesc.name == "dregg-mina-stark-fixture-v1"
#guard minaFixtureDesc.traceWidth == 3
#guard minaFixtureDesc.piCount == 2
#guard minaFixtureDesc.constraints.length == 4
#guard minaFixtureDesc.tables.isEmpty
#guard minaFixtureDesc.hashSites.isEmpty
#guard minaFixtureDesc.ranges.isEmpty

/-! ## §2b — The two window bodies, in closed form.

Both teeth below and the satisfiability direction go through `gate_modEq_iff`, which needs the
body written as `a - b`. Pinning that shape ONCE here is what keeps the `a`/`b` split explicit
rather than whatever the elaborator guesses: `c2Body` is `c' - (c + b)`, NOT `(c' - c) - b`. -/

/-- `C0`'s body in closed form: `b - a^3`. -/
theorem c0_eval (env : VmRowEnv) :
    c0Body.eval env = env.loc colB - env.loc colA * env.loc colA * env.loc colA := by
  simp only [c0Body, WindowExpr.eval]; ring

/-- `C2`'s body in closed form: `c' - (c + b)`. -/
theorem c2_eval (env : VmRowEnv) :
    c2Body.eval env = env.nxt colC - (env.loc colC + env.loc colB) := by
  simp only [c2Body, WindowExpr.eval]; ring

/-! ## §3 — The denotation, and the four FORCINGS.

`fixtureWindowHolds` is `Satisfied2.rowConstraints` specialised to this descriptor: the hash
carrier and trace family are irrelevant (no hash sites, no lookups), so they are supplied as the
trivial ones rather than quantified — a lookup-free descriptor's row denotation does not read
them. -/

/-- Every emitted constraint holds on one row window. -/
def fixtureWindowHolds (env : VmRowEnv) (isFirst isLast : Bool) : Prop :=
  ∀ c ∈ minaFixtureDesc.constraints,
    c.holdsAt (fun _ => 0) (fun _ => []) env isFirst isLast

/-- **C0 forces the cube, on EVERY row.** `onTransition := false`, so this one is not excused on
the wrap row — which is what makes `b` a function of `a` throughout the trace. -/
theorem mina_forces_cube (env : VmRowEnv) (isFirst isLast : Bool)
    (h : fixtureWindowHolds env isFirst isLast) :
    env.loc colB ≡ env.loc colA * env.loc colA * env.loc colA [ZMOD 2013265921] := by
  have hc : c0Body.eval env ≡ 0 [ZMOD 2013265921] :=
    h (.windowGate { body := c0Body, onTransition := false }) (by
      simp [minaFixtureDesc, minaFixtureConstraints])
  exact (gate_modEq_iff (c0_eval env)).mp hc

/-- **C1 forces the first-row public value.** -/
theorem mina_forces_first_pi (env : VmRowEnv) (isLast : Bool)
    (h : fixtureWindowHolds env true isLast) :
    env.loc colC ≡ env.pub 0 [ZMOD 2013265921] := by
  have hc := h (.base (.piBinding .first colC 0)) (by
    simp [minaFixtureDesc, minaFixtureConstraints])
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using hc

/-- **C2 forces the running sum on every transition row.** -/
theorem mina_forces_running_sum (env : VmRowEnv) (isFirst : Bool)
    (h : fixtureWindowHolds env isFirst false) :
    env.nxt colC ≡ env.loc colC + env.loc colB [ZMOD 2013265921] := by
  have hc : false = false → c2Body.eval env ≡ 0 [ZMOD 2013265921] :=
    h (.windowGate { body := c2Body, onTransition := true }) (by
      simp [minaFixtureDesc, minaFixtureConstraints])
  exact (gate_modEq_iff (c2_eval env)).mp (hc rfl)

/-- **C3 forces the last-row public value.** -/
theorem mina_forces_last_pi (env : VmRowEnv) (isFirst : Bool)
    (h : fixtureWindowHolds env isFirst true) :
    env.loc colC ≡ env.pub 1 [ZMOD 2013265921] := by
  have hc := h (.base (.piBinding .last colC 1)) (by
    simp [minaFixtureDesc, minaFixtureConstraints])
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm] using hc

/-! ## §4 — The converse: the intended shape SATISFIES the descriptor.

Without this the forcings above could all be true of a descriptor nothing satisfies. -/

/-- The intended row-window shape. -/
structure FixtureShape (env : VmRowEnv) (isFirst isLast : Bool) : Prop where
  cube      : env.loc colB = env.loc colA * env.loc colA * env.loc colA
  firstPi   : isFirst = true → env.loc colC = env.pub 0
  runSum    : isLast = false → env.nxt colC = env.loc colC + env.loc colB
  lastPi    : isLast = true → env.loc colC = env.pub 1

/-- **Satisfiability.** A window of the intended shape satisfies every emitted constraint — so the
descriptor is not vacuous, and the honest trace the Rust emitter builds is admitted. -/
theorem mina_window_holds_of_shape (env : VmRowEnv) (isFirst isLast : Bool)
    (hs : FixtureShape env isFirst isLast) :
    fixtureWindowHolds env isFirst isLast := by
  intro c hc
  simp only [minaFixtureDesc, minaFixtureConstraints, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · show c0Body.eval env ≡ 0 [ZMOD 2013265921]
    exact (gate_modEq_iff (c0_eval env)).mpr (by rw [hs.cube])
  · show isFirst = true → _
    intro hf; rw [hs.firstPi hf]
  · show isLast = false → c2Body.eval env ≡ 0 [ZMOD 2013265921]
    intro hl
    exact (gate_modEq_iff (c2_eval env)).mpr (by rw [hs.runSum hl])
  · show isLast = true → _
    intro hl; rw [hs.lastPi hl]

/-! ## §5 — The REFUTATION tooth: the `a^2` bend the o1js side keeps live.

`bridge/mina-zkapp/src/DreggProofVerify.ts::minaFixtureConstraintsBentDegree` is the same AIR with
`a^3` replaced by `a^2`, kept so the closing equality can be WATCHED refusing rather than assumed
to bite. This is that counter-example in the denotation. -/

/-- **A window whose `b` is not the cube of `a` is REFUSED.** Field-faithful: it needs the
canonicality both sides carry (`0 ≤ · < p`), so a mismatch cannot slip through by wrapping. -/
theorem mina_refuses_bent_degree (env : VmRowEnv) (isFirst isLast : Bool)
    (hcanonB : 0 ≤ env.loc colB ∧ env.loc colB < 2013265921)
    (hcanonCube : 0 ≤ env.loc colA * env.loc colA * env.loc colA
      ∧ env.loc colA * env.loc colA * env.loc colA < 2013265921)
    (hne : env.loc colB ≠ env.loc colA * env.loc colA * env.loc colA) :
    ¬ fixtureWindowHolds env isFirst isLast := by
  intro h
  have hc : c0Body.eval env ≡ 0 [ZMOD 2013265921] :=
    h (.windowGate { body := c0Body, onTransition := false }) (by
      simp [minaFixtureDesc, minaFixtureConstraints])
  exact not_modEq_zero_of_canon (c0_eval env) hcanonB hcanonCube hne hc

-- Non-vacuity, concretely: at `a = 2` the honest `b = 8` vanishes and the bent `b = 4` does not.
#guard decide (c0Body.eval { loc := fun i => if i = 0 then 2 else if i = 1 then 8 else 0,
                             nxt := fun _ => 0, pub := fun _ => 0 } = 0)
#guard decide (¬ (c0Body.eval { loc := fun i => if i = 0 then 2 else if i = 1 then 4 else 0,
                                nxt := fun _ => 0, pub := fun _ => 0 } = 0))

#assert_axioms mina_forces_cube
#assert_axioms mina_refuses_bent_degree

end Dregg2.Circuit.Emit.MinaFixtureEmit
