/-
# Dregg2.Circuit.Emit.EffectLower — `lowerEffect : EffectSpec2 → EffectVmDescriptor2`.

**Phase 1 of the logic-compiler refactor** (`metatheory/docs/LOGIC-COMPILER-ASSESSMENT.md` §7).
The assessment's finding: the spec-first framework (`EffectCommit2`) serializes through
`emittedEffect2` onto the flat `EmittedDescriptor` rail, which
`circuit/src/lean_descriptor_air.rs:3` self-labels **RETIRED / IR-v1, no deployed path**; the
LIVE rail is `EffectVmDescriptor2` → `circuit/src/descriptor_ir2.rs` (`Ir2Air`). There was no
general pass from an effect's spec to the live IR. This module is that pass.

## What it does

    lowerEffect : String → EffectSpec2 St Args → EffectVmDescriptor2

built out of `AirBuilder` (house law #1: Lean-authored AIR, and the gate vocabulary is the hoisted
one, not a fourth private copy). Three stages:

1. **`exprToHead`** — a real polynomial NORMALIZER from the framework's gate AST (`Circuit.Expr`
   = var|const|add|mul, an arbitrary tree) into `AirBuilder.Head` (`Σ coeff·∏cols + const`, the
   flat builder normal form). The multiplication case is a genuine distribute
   (`mulHead` + `evalH_mulHead`); this is the part a hand-rolled emitter skips by writing the
   normal form directly.
2. **`lowerConstraint`** — a flat `lhs = rhs` becomes the residual head `lhs − rhs` emitted as
   `AirBuilder.cgH`, so `headToExpr_eval` (`AirBuilder.lean:158`) discharges the gate-bite
   obligation instead of a per-effect hand proof.
3. **`lowerEffect`** — assembles the descriptor: the lowered `effectCircuit2 E` gate block plus a
   PI surface that REALIZES `WitnessExtract.PIBindsDigests` (`WitnessExtract.lean:54`) as actual
   `piBinding` pins — the guard region `0..guardWidth−1` and the six digest wires `66..71` the
   framework's own verifier obligation names.

## The two-sided faithfulness (§3), and where the residual is

* `lowered_of_satisfied` — UNCONDITIONAL. A row satisfying `effectCircuit2 E` over ℤ satisfies
  every lowered gate in the deployed mod-`p` denotation.
* `satisfied_of_lowered` — carries the DEPLOYED CANONICALITY envelope (`0 ≤ v < p` at the values
  the gates read). That is not slack introduced here: `VmConstraint.holdsVm` asserts
  `body ≡ 0 [ZMOD 2013265921]`, and the framework's `Constraint.holds` is ℤ equality, so the lift
  needs exactly the range discipline every deployed rung carries
  (`EffectVmEmitTransfer.not_modEq_zero_of_canon`).
* `.gate` is VACUOUS on the last row (`EffectVmEmit.holdsVm_gate_true`), so every statement is at
  `isLast = false` — the transition domain, as in every deployed rung.

## ⚑ THE DIFFERENTIAL (§5) — READ THIS BEFORE CITING THIS MODULE

`transferLoweredDesc` IS `lowerEffect` applied to transfer's `EffectSpec2` (`transferLoweredDesc_is_lowering`,
by `rfl`). It is **NOT** byte-equal to the deployed transfer AIR, and it cannot be, because
transfer's `EffectSpec2` carries no arithmetic to lower: `Inst/transfer.lean:99` commits the whole
6-conjunct `admitGuardA` as ONE `propBit` column asserted `= 1`, and `Inst/transfer.lean:118`
carries the ledger through an ABSTRACT injective digest `D`. §5 measures the gap with executed
`#guard`s (11 constraints vs 36; width 72 vs 188; 0 hash sites vs 4; 0 ranges vs 2) against the
bare v1 `def`, records the committed bytes of the LIVE registry member (**1874 wide, 663
constraints**), and `lowered_json_ne_deployed_json` REFUTES byte-equality as a theorem.

What IS proved is the refinement (`transferLowered_refines_balanceMovement`): the descriptor this
pass EMITS forces the same `BalanceMovementSpec` the deployed one does. Same spec, different
mechanism, and the deployed descriptor carries strictly more (§5's `deployedExtra` doc).
⚑ It does NOT route through `Inst.Transfer.transfer_full_sound`, because that carries
`logHashInjective`, which `StateCommit.lean:251` PROVES FALSE at deployed BabyBear — a theorem
under it says nothing about the shipping system. §6 calls `effect2_circuit_full_sound` directly at
the ported `¬ LogColl` side condition instead: refutable, at the one pair of logs the witness
supplies, and strictly stronger by `LogCommitRegrounded.noLogColl_of_inj`.

ADDITIVE: imports read-only; edits no descriptor, no registry, no `Dregg2.lean`.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Circuit.WitnessExtract
import Dregg2.Circuit.Emit.AirBuilder
import Dregg2.Circuit.Inst.transfer
import Dregg2.Circuit.Emit.EffectVmEmitTransfer

namespace Dregg2.Circuit.Emit.EffectLower

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The BabyBear modulus the deployed row denotation reduces against. -/
abbrev P : ℤ := 2013265921

/-! ## §1 — the polynomial normalizer `Expr → AirBuilder.Head`.

`Circuit.Expr` is an arbitrary var/const/+/× tree; `AirBuilder.Head` is the flat builder normal
form `Σ (coeff, cols) + const`. The `mul` case is the only real content: a distribute over both
term lists plus the two constant cross-terms. `evalH_mulHead` is its semantic bridge, and
`evalH_exprToHead` composes the four cases into "the head means what the expression meant". -/

/-- Multiply two heads: distribute term×term, then each side's terms against the other's constant,
then the constant product. -/
def mulHead (h o : Head) : Head :=
  { terms := (h.terms.flatMap fun t => o.terms.map fun u => ((t.1 * u.1, t.2 ++ u.2) : ℤ × List Nat))
             ++ (h.terms.map fun t => ((t.1 * o.const, t.2) : ℤ × List Nat))
             ++ (o.terms.map fun u => ((h.const * u.1, u.2) : ℤ × List Nat))
  , const := h.const * o.const }

private theorem sum_scaleR (a : Assignment) (k : ℤ) (ts : List (ℤ × List Nat)) :
    ((ts.map fun t => ((t.1 * k, t.2) : ℤ × List Nat)).map (evalTerm a)).sum
      = (ts.map (evalTerm a)).sum * k := by
  induction ts with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih, evalTerm]
    ring

private theorem sum_scaleL (a : Assignment) (k : ℤ) (ts : List (ℤ × List Nat)) :
    ((ts.map fun t => ((k * t.1, t.2) : ℤ × List Nat)).map (evalTerm a)).sum
      = k * (ts.map (evalTerm a)).sum := by
  induction ts with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih, evalTerm]
    ring

private theorem sum_crossOne (a : Assignment) (x : ℤ × List Nat) (us : List (ℤ × List Nat)) :
    ((us.map fun u => ((x.1 * u.1, x.2 ++ u.2) : ℤ × List Nat)).map (evalTerm a)).sum
      = evalTerm a x * (us.map (evalTerm a)).sum := by
  induction us with
  | nil => simp
  | cons y ys ih =>
    simp only [List.map_cons, List.sum_cons, ih, evalTerm, List.map_append, List.prod_append]
    ring

private theorem sum_cross (a : Assignment) (ts us : List (ℤ × List Nat)) :
    ((ts.flatMap fun t =>
        us.map fun u => ((t.1 * u.1, t.2 ++ u.2) : ℤ × List Nat)).map (evalTerm a)).sum
      = (ts.map (evalTerm a)).sum * (us.map (evalTerm a)).sum := by
  induction ts with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, ih, sum_crossOne,
      List.map_cons, List.sum_cons]
    ring

/-- **The multiplication bridge**: the distributed head means the product of the two heads. -/
theorem evalH_mulHead (a : Assignment) (h o : Head) :
    evalH (mulHead h o) a = evalH h a * evalH o a := by
  simp only [evalH, mulHead, List.map_append, List.sum_append, sum_cross, sum_scaleR, sum_scaleL]
  ring

/-- **`exprToHead`** — normalize a framework gate expression into the `AirBuilder` head vocabulary. -/
def exprToHead : Expr → Head
  | .var v     => Head.lin 1 v
  | .const k   => Head.c k
  | .add e₁ e₂ => (exprToHead e₁).append (exprToHead e₂)
  | .mul e₁ e₂ => mulHead (exprToHead e₁) (exprToHead e₂)

/-- **THE NORMALIZER IS MEANING-PRESERVING.** The head evaluates to exactly what the source
expression evaluated to — so nothing is lost between `EffectSpec2`'s gate algebra and the
builder's normal form. -/
theorem evalH_exprToHead (a : Assignment) (e : Expr) : evalH (exprToHead e) a = e.eval a := by
  induction e with
  | var v => simp [exprToHead, Expr.eval]
  | const k => simp [exprToHead, Expr.eval]
  | add e₁ e₂ ih₁ ih₂ => simp [exprToHead, Expr.eval, ih₁, ih₂]
  | mul e₁ e₂ ih₁ ih₂ => simp [exprToHead, Expr.eval, evalH_mulHead, ih₁, ih₂]

/-! ## §2 — lowering a constraint, and the descriptor assembly. -/

/-- The RESIDUAL head of a flat `lhs = rhs` constraint: `lhs − rhs`, the polynomial an AIR gate
asserts vanishes. -/
def constraintHead (c : Constraint) : Head :=
  (exprToHead c.lhs).append ((exprToHead c.rhs).scale (-1))

theorem evalH_constraintHead (a : Assignment) (c : Constraint) :
    evalH (constraintHead c) a = c.lhs.eval a - c.rhs.eval a := by
  simp only [constraintHead, evalH_append, evalH_scale, evalH_exprToHead]
  ring

/-- **`lowerConstraint`** — one framework constraint as a live-IR row gate, emitted THROUGH
`AirBuilder.cgH` (not a raw `.base (.gate …)` literal), so `headToExpr_eval` carries the
semantics. -/
def lowerConstraint (c : Constraint) : VmConstraint2 := cgH (constraintHead c)

/-- The six digest wires `WitnessExtract.PIBindsDigests` names as the verifier's binding surface
(`WitnessExtract.lean:54-60`): rest pre/post, component post/expected, log post/expected. The two
ROOT wires `64`/`65` are deliberately absent — the framework states explicitly that they are never
gated. -/
def digestPinCols : List Nat :=
  [vE2RestPre, vE2RestPost, vE2CompPost, vE2CompExp, vE2LogPost, vE2LogExp]

/-- The PI surface: the guard region `0 .. guardWidth−1` at PIs `0 ..`, then the six digest wires.
This REALIZES `PIBindsDigests` as circuit pins rather than leaving it a carried Prop. -/
def lowerPiPins (guardWidth : Nat) : List VmConstraint2 :=
  (List.range guardWidth).map (fun w => pinPi w w)
    ++ digestPinCols.zipIdx.map (fun p => pinPi p.1 (guardWidth + p.2))

/-- **The lowering, on raw spec data.** Split out from `lowerEffect` so the emitted object is a
CLOSED term (an `EffectSpec2` carries `Prop`-valued and abstract-digest fields that no `#guard`
can evaluate, but the lowering READS only these three) — this is what makes the byte-golden in §5
executable and the `rfl` in `transferLoweredDesc_is_lowering` available. -/
def lowerCS (name : String) (traceWidth guardWidth : Nat) (cs : ConstraintSystem) :
    EffectVmDescriptor2 :=
  { name        := name
  , traceWidth  := traceWidth
  , piCount     := guardWidth + digestPinCols.length
  , tables      := []
  , constraints := cs.map lowerConstraint ++ lowerPiPins guardWidth
  , hashSites   := []
  , ranges      := [] }

/-- **`lowerEffect` — THE PASS.** An `EffectSpec2` compiled to a live-rail `EffectVmDescriptor2`:
the derived circuit `effectCircuit2 E` (guard gates ++ the three frame/bind/log EQ gates) lowered
gate-by-gate through `AirBuilder`, over the framework's own 72-column layout, with the
`PIBindsDigests` surface pinned. -/
def lowerEffect {St Args : Type} (name : String) (E : EffectSpec2 St Args) : EffectVmDescriptor2 :=
  lowerCS name E.traceWidth E.guardWidth (effectCircuit2 E)

/-! ## §3 — two-sided faithfulness of the pass.

The deployed row denotation is mod-`p` (`VmConstraint.holdsVm` on a `.gate` asserts
`body ≡ 0 [ZMOD 2013265921]`); the framework's is ℤ equality. So the two directions are NOT
symmetric and we do not pretend they are: the emission direction is free, the soundness direction
carries the deployed canonicality envelope. -/

theorem sub_modEq_zero_iff {x y : ℤ} : (x - y ≡ 0 [ZMOD P]) ↔ (x ≡ y [ZMOD P]) := by
  constructor
  · intro h; simpa using Int.ModEq.add_right y h
  · intro h; simpa using Int.ModEq.sub_right y h

/-- The deployed range discipline lifts a mod-`p` congruence to ℤ equality. Same shape (and same
`omega` step) as `EffectVmEmitTransfer.not_modEq_zero_of_canon`. -/
theorem eq_of_modEq_canon {x y : ℤ} (hx0 : 0 ≤ x) (hx1 : x < P) (hy0 : 0 ≤ y) (hy1 : y < P)
    (h : x ≡ y [ZMOD P]) : x = y := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp h
  -- `P` is an `abbrev`; restate at the literal so `omega` sees the coefficient.
  have hx1' : x < 2013265921 := hx1
  have hy1' : y < 2013265921 := hy1
  have hk' : y - x = 2013265921 * k := hk
  omega

/-- A lowered gate on a TRANSITION row IS the source constraint, read mod `p`. This is the whole
content of the lowering, and it is proved once here rather than per effect. -/
theorem lowerConstraint_holdsAt_iff (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst : Bool) (c : Constraint) :
    (lowerConstraint c).holdsAt hash tf env isFirst false
      ↔ (c.lhs.eval env.loc ≡ c.rhs.eval env.loc [ZMOD P]) := by
  show ((headToExpr (constraintHead c)).eval env.loc ≡ 0 [ZMOD P]) ↔ _
  rw [headToExpr_eval, evalH_constraintHead, sub_modEq_zero_iff]

/-- **EMISSION direction — UNCONDITIONAL.** A row satisfying the framework's derived circuit over
ℤ satisfies every gate the pass emitted, in the deployed mod-`p` denotation. -/
theorem lowered_of_satisfied {St Args : Type} (name : String) (E : EffectSpec2 St Args)
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (isFirst : Bool)
    (h : satisfied (effectCircuit2 E) env.loc) :
    ∀ c ∈ effectCircuit2 E, (lowerConstraint c).holdsAt hash tf env isFirst false := by
  intro c hc
  rw [lowerConstraint_holdsAt_iff]
  exact Int.ModEq.refl _ |>.trans (by rw [h c hc])

/-- **SOUNDNESS direction.** Every lowered gate holding on a transition row, plus the deployed
canonicality envelope at the values those gates read, forces the ORIGINAL `EffectSpec2` circuit
satisfied over ℤ by that row — so every theorem the framework proves about `satisfiedE2` transfers
to a witness of the EMITTED descriptor.

The `hcanon` hypothesis is the deployed range invariant `0 ≤ v < p`, stated at the constraint sides
themselves. It is NOT decoration: without it a mod-`p`-satisfying row can carry an ℤ residual equal
to `p`, exactly the wrap class `docs/reference/WRAP-CLASS-AUDIT.md` catalogues. -/
theorem satisfied_of_lowered {St Args : Type} (name : String) (E : EffectSpec2 St Args)
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (isFirst : Bool)
    (hcanon : ∀ c ∈ effectCircuit2 E,
      (0 ≤ c.lhs.eval env.loc ∧ c.lhs.eval env.loc < P)
        ∧ (0 ≤ c.rhs.eval env.loc ∧ c.rhs.eval env.loc < P))
    (h : ∀ vc ∈ (lowerEffect name E).constraints, vc.holdsAt hash tf env isFirst false) :
    satisfied (effectCircuit2 E) env.loc := by
  intro c hc
  have hmem : lowerConstraint c ∈ (lowerEffect name E).constraints := by
    refine List.mem_append_left _ ?_
    exact List.mem_map_of_mem hc
  have hg := (lowerConstraint_holdsAt_iff hash tf env isFirst c).mp (h _ hmem)
  obtain ⟨⟨hl0, hl1⟩, ⟨hr0, hr1⟩⟩ := hcanon c hc
  exact eq_of_modEq_canon hl0 hl1 hr0 hr1 hg

/-! ## §4 — transfer: what the pass EMITS for the balance-movement effect.

Transfer's `EffectSpec2` is `Inst.Transfer.balanceE` (`Dregg2/Circuit/Inst/transfer.lean:122`);
its derived circuit is `balanceGuardGates ++ [cE2RestF, cE2Bind, cE2Log]` — the single `propBit`
guard gate at wire `0` plus the three digest EQ gates. `transferLoweredDesc` is the pass's output
on exactly that, and `transferLoweredDesc_is_lowering` pins the identity by `rfl` for EVERY carried
digest `D` (the lowering reads no digest, so the emitted object is `D`-independent). -/

open Dregg2.Circuit.Inst.Transfer (balanceE balanceGuardGates cBitGuard BalanceArgs)
open Dregg2.Exec (RecChainedState CellId AssetId)

/-- The lowered transfer AIR's identity. Distinct from the deployed
`"dregg-effectvm-transfer-v1"` on purpose: this is a DIFFERENT circuit (§5), and giving it the
deployed name would be exactly the display-name collision
`reference-a-display-name-is-not-a-key` catalogues. -/
def transferLoweredName : String := "dregg-transfer-v2-lowered"

/-- **The pass's output for transfer** — a closed `EffectVmDescriptor2` on the live rail. -/
def transferLoweredDesc : EffectVmDescriptor2 :=
  lowerCS transferLoweredName 72 1 (balanceGuardGates ++ [cE2RestF, cE2Bind, cE2Log])

/-- **`transferLoweredDesc` IS `lowerEffect` applied to transfer's spec** — by `rfl`, for every
carried ledger digest. This is what makes §5's measurements and the §6 refinement statements about
the GENERAL PASS rather than about a hand-written lookalike. -/
theorem transferLoweredDesc_is_lowering
    (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D) :
    transferLoweredDesc = lowerEffect transferLoweredName (balanceE D hD) := rfl

/-! ### §4a — the emitted shape, executed. -/

#guard transferLoweredDesc.name == "dregg-transfer-v2-lowered"
#guard transferLoweredDesc.traceWidth == 72
#guard transferLoweredDesc.piCount == 7
#guard transferLoweredDesc.constraints.length == 11
#guard transferLoweredDesc.tables.length == 0
#guard transferLoweredDesc.hashSites.length == 0
#guard transferLoweredDesc.ranges.length == 0

/-! **THE BYTE GOLDEN** — the same `#guard emitVmJson2 … == <literal>` pin every hand-authored
emitter carries, here on a descriptor NOBODY hand-wrote: these bytes are the compiler's output. -/
#guard emitVmJson2 transferLoweredDesc ==
  "{\"name\":\"dregg-transfer-v2-lowered\",\"ir\":2,\"trace_width\":72,\"public_input_count\":7,\"tables\":[],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":0}},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":66}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":67}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":68}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":69}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":70}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":71}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":66,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":67,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":68,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":69,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":70,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":71,\"pi_index\":6}],\"hash_sites\":[],\"ranges\":[]}"

/-! ### §4b — NON-VACUITY and the anti-ghost tooth.

`transferLowered_refines_balanceMovement`'s premise is a satisfying witness of the emitted
descriptor. A premise nothing can satisfy would make the keystone worthless, so we exhibit a row
that DOES satisfy every emitted constraint, and a row the emitted gates REJECT. -/

/-- A concrete canonical row: guard bit `1`, the three digest pairs agreeing. -/
def demoRow : Assignment := fun w =>
  if w = 0 then 1
  else if w = 66 then 7 else if w = 67 then 7
  else if w = 68 then 11 else if w = 69 then 11
  else if w = 70 then 5 else if w = 71 then 5
  else 0

/-- The PI vector the seven pins demand (guard bit, then the six digest wires in order). -/
def demoPub : Assignment := fun k =>
  if k = 0 then 1
  else if k = 1 then 7 else if k = 2 then 7
  else if k = 3 then 11 else if k = 4 then 11
  else if k = 5 then 5 else if k = 6 then 5
  else 0

def demoEnv : VmRowEnv := { loc := demoRow, nxt := demoRow, pub := demoPub }

/-- **NON-VACUITY** — every constraint the pass emitted for transfer HOLDS on `demoEnv`, PI pins
included. The keystone's premise is inhabited. -/
theorem demoEnv_satisfies_lowered (hash : List ℤ → ℤ) (tf : TraceFamily) :
    ∀ vc ∈ transferLoweredDesc.constraints, vc.holdsAt hash tf demoEnv true false := by
  intro vc hvc
  -- the four lowered gates go through the §3 bridge (which strips `hash`/`tf`); the seven PI pins
  -- are `isFirst = true → loc col ≡ pub idx`, and `demoPub` was built to satisfy exactly those.
  fin_cases hvc <;>
    first
      | exact (lowerConstraint_holdsAt_iff hash tf demoEnv true _).mpr (by decide)
      | exact fun _ => by decide

/-- A row that forges the component digest: `compDigPost = 11` but `compDigExpected = 12`. -/
def ghostRow : Assignment := fun w => if w = 69 then 12 else demoRow w

def ghostEnv : VmRowEnv := { loc := ghostRow, nxt := ghostRow, pub := demoPub }

/-- **THE ANTI-GHOST TOOTH — the emitted gate BITES.** The lowered `cE2Bind` gate (the framework's
component binding) REFUSES a row whose post component digest differs from the spec-expected one.
The pass does not merely produce a well-typed descriptor; the descriptor it produces rejects. -/
theorem lowered_rejects_component_forge (hash : List ℤ → ℤ) (tf : TraceFamily) :
    ¬ (∀ vc ∈ transferLoweredDesc.constraints, vc.holdsAt hash tf ghostEnv true false) := by
  intro h
  have hmem : lowerConstraint cE2Bind ∈ transferLoweredDesc.constraints :=
    List.mem_append_left _ (List.mem_map_of_mem
      (by simp [Dregg2.Circuit.Inst.Transfer.balanceGuardGates]))
  have hbite := (lowerConstraint_holdsAt_iff hash tf ghostEnv true cE2Bind).mp (h _ hmem)
  revert hbite
  decide

/-! ## §5 — ⚑ THE DIFFERENTIAL: lowered vs DEPLOYED.

The deployed transfer AIR is `EffectVmEmitTransfer.transferVmDescriptor`
(`Dregg2/Circuit/Emit/EffectVmEmitTransfer.lean:217`), a v1 `EffectVmDescriptor` whose live face is
reached by `graduateV1`/`v3OfFrozenWide` from the hardened `transferVmDescriptorAvail`
(`EmitRotationV3.lean:135` routes key `transferVmDescriptor2R24` to
`Emit.AvailWireMembers.transferV3AvailWire`). `embedV1` puts the v1 object on the v2 rail with no
reinterpretation, which is the fairest possible comparison basis for byte-equality.

**Result: NOT byte-exact, and refutably so.** The measurements below are executed. -/

open Dregg2.Circuit.Emit.EffectVmEmitTransfer (transferVmDescriptor)

/-- The deployed transfer AIR, placed on the v2 rail for comparison. -/
def transferDeployedV2 : EffectVmDescriptor2 := embedV1 transferVmDescriptor

#guard transferDeployedV2.name == "dregg-effectvm-transfer-v1"
#guard transferDeployedV2.traceWidth == 188
#guard transferDeployedV2.piCount == 42
#guard transferDeployedV2.constraints.length == 36
#guard transferDeployedV2.hashSites.length == 4
#guard transferDeployedV2.ranges.length == 2

/-! ⚑ **THE CRUX, MEASURED: the two rails do NOT fuse byte-wise at transfer.** -/
#guard transferLoweredDesc.traceWidth != transferDeployedV2.traceWidth
#guard transferLoweredDesc.constraints.length != transferDeployedV2.constraints.length
#guard emitVmJson2 transferLoweredDesc != emitVmJson2 transferDeployedV2

/-! ⚠ **AND THE COMPARISON ABOVE IS THE GENEROUS ONE.** `transferVmDescriptor` is the BARE v1 `def`;
`EffectVmEmitTransfer.lean:234` says in as many words that `EmitRotationV3` "now routes the LIVE
registry to the hardened avail member … NOT this bare def". The object a dregg node actually proves
is the `transferVmDescriptor2R24` row of `circuit/descriptors/rotation-v3-staged-registry.tsv`
(`dregg-effectvm-transfer-v1-avail-rot24-v3-staged-gentian-deployed-bare-refuse`), and those
committed bytes are:

    trace_width 1874 · public_input_count 50 · 663 constraints
    (340 lookup · 294 window_gate · 14 transition · 15 pi_binding) · 6 tables

against this pass's **72 / 7 / 11**. The rail distance at transfer is 11 constraints to 663, and
NONE of the 340 lookups or 294 window gates has any counterpart in `EffectSpec2`'s vocabulary. Any
reading of Phase 1 as "nearly fused" is refuted by that pair of numbers. -/

/-- ⚑ **The byte-differential as a THEOREM, not a note.** The emitted wire strings differ; the
witness is the `trace_width` field (72 vs 188), which `emitVmJson2` renders verbatim
(`DescriptorIR2.lean:1755-1762`). Stated so that a later lane cannot quietly read this module as
"the rails fused". -/
theorem lowered_ne_deployed : transferLoweredDesc.traceWidth ≠ transferDeployedV2.traceWidth := by
  decide

theorem lowered_json_ne_deployed_json :
    emitVmJson2 transferLoweredDesc ≠ emitVmJson2 transferDeployedV2 := by
  decide

/-- **WHAT THE HAND-AUTHORED DESCRIPTOR CARRIES THAT THE LOWERING CANNOT PRODUCE — named exactly.**

None of these is a gap in the pass. Each is structure that is ABSENT FROM `EffectSpec2` and could
not be recovered from it by any lowering, because the spec never held it:

1. **The guard's arithmetic.** `Inst/transfer.lean:99` supplies `guardGates := [cBitGuard]` — the
   6-conjunct `admitGuardA` (authority ∧ non-negativity ∧ availability ∧ distinctness ∧ src- and
   dst-liveness) committed as ONE `propBit` column ASSERTED `= 1`. The deployed AIR instead
   COMPUTES its guard: `gDirBool` (`:118`), the 15-bit borrow chain and range teeth of the §11.7
   availability weld. A `propBit` is a claim; the borrow chain is a proof.
2. **The 14-column EffectVM state layout** (`state_before`/`state_after`/`param`/`aux`,
   `EffectVmEmit.lean:47,64`) and the 8 field-passthrough + balance-hi + cap-root + reserved frame
   gates (`EffectVmEmitTransfer.lean:137,210`). `EffectSpec2` frames the untouched fields
   DECLARATIVELY (`restFrame`, a `Prop`) and binds them by a carried rest-hash portal, so there is
   no per-field gate to emit.
3. **`transitionAll`** — 14 `.transition` continuity constraints (`:146`). `EffectSpec2` is
   single-row; multi-row continuity is not in its vocabulary.
4. **The 4 ordered GROUP-4 `H4` hash sites** (`:202`) that BUILD `state_commit` in-circuit.
   `EffectSpec2` carries the commitment as an ABSTRACT `digest`/`RH`/`LH` (`EffectCommit2.lean:183`,
   `:120`) — the hash is a carried portal, never an emitted site. This is the single largest
   structural gap and it is deliberate in the framework's design.
5. **The 2 range teeth** `⟨saCol BALANCE_LO, 30⟩`, `⟨saCol BALANCE_HI, 30⟩` (`:236`) — the
   field-soundness / availability layer. `EffectSpec2` has no range vocabulary at all.
6. **The 7 boundary PI pins at the deployed indices** (`:150,157`) and `piCount = 42`. The pass
   emits 7 PIs realizing `PIBindsDigests`; the deployed surface is a different, larger, ordered
   contract the spec does not name.
7. **The selector gate** `selectorGates sel.TRANSFER` (`EffectVmEmit.lean:594`) — the multi-effect
   dispatch discipline. `EffectSpec2` describes ONE effect and has no selector.

Conversely the lowering emits ONE thing the deployed descriptor does not: the three digest EQ gates
`cE2RestF`/`cE2Bind`/`cE2Log` (`EffectCommit2.lean:314-318`), which is where the framework's
whole-post-state binding lives. -/
def deployedExtra : Unit := ()

/-! ## §6 — the REFINEMENT that DOES hold: the emitted descriptor forces `BalanceMovementSpec`.

This is the real Phase-1 result. It is a statement about the object the PASS produced — not about
`satisfiedE2`, not about a model beside it. A witness of `transferLoweredDesc` (the compiler's
output, byte-pinned in §4a) forces the same declarative spec the deployed rung forces. -/

open Dregg2.Circuit.Spec.BalanceMovement (BalanceMovementSpec)
open Dregg2.Circuit.LogCommitRegrounded (LogColl)

/-- The columns transfer's lowered gates read: the guard bit and the six digest wires. -/
def transferGateCols : List Nat := [0, 66, 67, 68, 69, 70, 71]

/-- **`transferLowered_refines_balanceMovement` — THE PHASE-1 KEYSTONE.**

A row of a trace satisfying the EMITTED descriptor `transferLoweredDesc`, which is the honest
`encodeE2` witness for `(s, args, s')` and is canonical at the columns the gates read, forces the
complete declarative `BalanceMovementSpec` — the SAME apex
`RotatedKernelRefinement*.transfer_descriptorRefines` reaches from the hand-authored side.

⚑ **IT DOES NOT CARRY `logHashInjective`, DELIBERATELY.** `Inst.Transfer.transfer_full_sound` takes
that carrier, and `StateCommit.lean:251` records it PROVED FALSE at deployed BabyBear parameters —
a theorem under it is VACUOUS at deployment. So this rung does NOT route through
`transfer_full_sound`; it calls `effect2_circuit_full_sound` directly at its own weaker side
condition `hno`, the ported `_or_collides` form (`LogCommitRegrounded.lean:70,152`): a NAMED,
REFUTABLE non-collision at the ONE pair of logs THIS witness supplies. By
`LogCommitRegrounded.noLogColl_of_inj` the old carrier implies `hno` at every pair, so this
statement is strictly STRONGER than the `transfer_full_sound` route, not a weakening of it.

Remaining carried portals, none refuted: `RestIffNoBal S.RH`, `Function.Injective D`, and the
deployed canonicality envelope the mod-`p` row denotation genuinely requires. -/
theorem transferLowered_refines_balanceMovement
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (isFirst : Bool)
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (hRest : RestIffNoBal S.RH)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState)
    (hno : ¬ LogColl S.LH s'.log (args.t :: s.log))
    (hrow : env.loc = encodeE2 S (balanceE D hD) s args s')
    (hcanon : ∀ c ∈ effectCircuit2 (balanceE D hD),
      (0 ≤ c.lhs.eval env.loc ∧ c.lhs.eval env.loc < P)
        ∧ (0 ≤ c.rhs.eval env.loc ∧ c.rhs.eval env.loc < P))
    (hsat : ∀ vc ∈ transferLoweredDesc.constraints,
      vc.holdsAt hash tf env isFirst false) :
    BalanceMovementSpec s args.t args.a s' := by
  -- the emitted descriptor IS the pass's output on transfer's spec
  rw [transferLoweredDesc_is_lowering D hD] at hsat
  -- soundness of the pass: the framework's derived circuit is satisfied over ℤ by this row
  have hsatZ : satisfied (effectCircuit2 (balanceE D hD)) env.loc :=
    satisfied_of_lowered transferLoweredName (balanceE D hD) hash tf env isFirst hcanon hsat
  rw [hrow] at hsatZ
  -- the framework's crown jewel, at the PORTED log side condition (no refuted carrier)
  have hapex : (balanceE D hD).apex s args s' :=
    effect2_circuit_full_sound S (balanceE D hD)
      (Dregg2.Circuit.Inst.Transfer.balanceRestFrameDecodes S D hD hRest)
      (Dregg2.Circuit.Inst.Transfer.balanceGuardDecodes D hD)
      s args s' (hno := hno) hsatZ
  exact (Dregg2.Circuit.Inst.Transfer.apex_iff_balanceMovementSpec D hD s args s').mp hapex

/-- **The converse (emission).** A genuine balance-movement step's honest witness satisfies every
gate the pass emitted — the compiler does not over-constrain. -/
theorem transferLowered_emits
    (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv) (isFirst : Bool)
    (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState)
    (hrow : env.loc = encodeE2 S (balanceE D hD) s args s')
    (h : satisfiedE2 S (balanceE D hD) (encodeE2 S (balanceE D hD) s args s')) :
    ∀ c ∈ effectCircuit2 (balanceE D hD),
      (lowerConstraint c).holdsAt hash tf env isFirst false := by
  refine lowered_of_satisfied transferLoweredName (balanceE D hD) hash tf env isFirst ?_
  rw [hrow]; exact h

/-! ## §7 — axiom-hygiene tripwires. -/

#assert_axioms evalH_mulHead
#assert_axioms evalH_exprToHead
#assert_axioms evalH_constraintHead
#assert_axioms lowerConstraint_holdsAt_iff
#assert_axioms lowered_of_satisfied
#assert_axioms satisfied_of_lowered
#assert_axioms transferLoweredDesc_is_lowering
#assert_axioms demoEnv_satisfies_lowered
#assert_axioms lowered_rejects_component_forge
#assert_axioms lowered_ne_deployed
#assert_axioms lowered_json_ne_deployed_json
#assert_axioms transferLowered_refines_balanceMovement
#assert_axioms transferLowered_emits

end Dregg2.Circuit.Emit.EffectLower
