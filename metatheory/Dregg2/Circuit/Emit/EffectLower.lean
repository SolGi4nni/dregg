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

## ⚑ PHASE 2 (2026-08-01) — the SOURCE was widened, and one deployed descriptor is now BYTE-EXACT

Phase 1's own finding was that the gap is the source language, measured: `EffectSpec2` reaches
12/76 of the deployed by-name descriptors, 25/76 with window gates, and **51 of the 76 carry a
lookup/table leg `EffectSpec2` had no word for.** Phase 2 gives it the words
(`Circuit/EffectAirIR.lean`, reusing `TableAirIR`'s `RowSel`/`WindowExpr`/multiplicity/`BusOp`
vocabulary rather than a fourth private copy) and `EffectSpec2` gains ONE defaulted field, `air`.

* **§2b** lowers the new legs: `lowerLookupLeg` (+51), `lowerWindowLeg` (the 4-way `RowSel` onto
  the target's two shapes, with TableAirIR's `nxt` refusal), `lowerPiPinLeg` (first AND last row),
  `lowerRangeLeg`. A leg the main rail cannot take lowers to `refuseConstraints` — an
  UNSATISFIABLE boundary pair, never silence, because a dropped leg accepts strictly more.
* **§8** is the falsifiable rung: `dregg-dfa-routing-table::exact-public-v1` — lookup + declared
  `exactPublicRows` table + `.transition` window + first/last PI pins — is emitted by the pass
  **BYTE-EXACT** (`DfaRung.dfaLowered_eq_deployed`, by `rfl`; width Δ 0, PI Δ 0, constraints Δ 0),
  and inherits the deployed refinement, witness and canary verbatim.
* **§9** separates syntax from semantics and gives the re-measured readout: kind coverage
  **25/76 → 76/76**, byte reach **8/76**, and names why the second number is bounded by the
  deployed set's own rendering inconsistency rather than by the source.

## ⚑ PHASE 3 (2026-08-01) — THE FIRST RAIL FUSION. Phase 2's `rfl` was CASHED, and it is gone

A proof that the compiler's output equals a hand-written descriptor is a reason to DELETE the
hand-written one, not to keep both. `DfaRoutingTableEmit.lean` §2 now reads

    def tableRoutingDesc (name) (tbl) := lowerAir name TRT_WIDTH TRT_PI_COUNT [] (dfaAir tbl)

and its four `VmConstraint2` `def`s (`transitionLookup`, `continuityWindow`, `b1InitialPin`,
`b2FinalPin`) plus the hand-written `constraints := [...]` list are DELETED. The deployed
`dregg-dfa-routing-table::exact-public-v1` — served by `descriptor_by_name()` and re-emitted into
`circuit/descriptors/by-name/` — is now a COMPILED artifact. It is the first one in the tree.

Two structural consequences, both deliberate:

* The back end moved DOWN into `Dregg2/Circuit/Emit/EffectLowerCore.lean` (same namespace), because
  a descriptor defined by the compiler must import it, and this module imports transfer's spec. The
  import edge — `EffectLowerCore` → `DfaRoutingTableEmit` → here — is what makes the fusion
  structural instead of a claim.
* `DfaRung.dfaLowered_eq_deployed` and the four theorems restating the witness/canary/refinement on
  a second copy are DELETED, not moved. With one object they would be `P = P`. §8 says so plainly
  and names what carries the weight now (the emission pins + the byte-golden, one module down).

Transfer is untouched by all of it — its `air` block is empty and §5's refutation stands, because
transfer's gap was never syntax.

Phase 2 was ADDITIVE (one defaulted `EffectSpec2` field). Phase 3 is NOT: it deletes a deployed
descriptor's hand-written body. Nothing re-emits — the bytes are identical, which is the point —
but `DfaRoutingTableEmit.transitionLookup` / `.continuityWindow` / `.b1InitialPin` / `.b2FinalPin`
no longer exist, and `simp only [tableRoutingDesc]` no longer unfolds anything useful; consumers
use `tableRoutingDesc_constraints` / `_tables` / `_ranges` instead.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Circuit.WitnessExtract
import Dregg2.Circuit.Emit.AirBuilder
import Dregg2.Circuit.Emit.EffectLowerCore
import Dregg2.Circuit.Inst.transfer
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.DfaRoutingTableEmit

namespace Dregg2.Circuit.Emit.EffectLower

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv VmRange)
open Dregg2.Exec.CircuitEmit (EmittedExpr emitExpr)
open Dregg2.Circuit.EffectAirIR
  (EffectAir AirLeg LookupLeg WindowLeg RangeLeg PiPinLeg exprIsOne)
open Dregg2.Circuit.TableAirIR (BusOp RowSel readsNext)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1–§2b — ⚑ MOVED to `Dregg2/Circuit/Emit/EffectLowerCore.lean` (2026-08-01, the FUSION).

The normalizer (`exprToHead`, `evalH_exprToHead`), `lowerConstraint`, the Phase-2 leg lowerings
(`lowerLookupLeg` / `lowerWindowLeg` / `lowerPiPinLeg` / `lowerRangeLeg` / `refuseConstraints`),
`assemble` and `lowerAir` now live one module DOWN, in the SAME namespace — so every name below
still resolves unqualified and no consumer moved.

⚑ Why: `DfaRoutingTableEmit.tableRoutingDesc` is no longer a hand-written `VmConstraint2` list, it
IS `lowerAir` of an `EffectAir` source. A descriptor DEFINED BY the compiler needs the compiler
BELOW it, and this module sits above `Inst/transfer.lean`. §8 below is what remains of the
fusion's evidence here; the deployed object and its byte-golden are in `DfaRoutingTableEmit`. -/

/-! ## §2c — the full-state PI surface. `lowerAir`'s counterpart adds nothing; this one realizes
`WitnessExtract.PIBindsDigests` as circuit pins. -/

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
can evaluate, but the lowering READS only these four) — this is what makes the byte-golden in §5
executable and the `rfl` in `transferLoweredDesc_is_lowering` available. -/
def lowerCS (name : String) (traceWidth guardWidth : Nat) (cs : ConstraintSystem)
    (air : EffectAir) : EffectVmDescriptor2 :=
  assemble name traceWidth (guardWidth + digestPinCols.length + air.extraPi) cs air
    (lowerPiPins guardWidth)

/-- **`lowerEffect` — THE PASS.** An `EffectSpec2` compiled to a live-rail `EffectVmDescriptor2`:
the derived circuit `effectCircuit2 E` (guard gates ++ the three frame/bind/log EQ gates) lowered
gate-by-gate through `AirBuilder`, over the framework's own 72-column layout, with the
`PIBindsDigests` surface pinned — PLUS (Phase 2) whatever lookup / table / range / window / boundary
legs the spec's `air` block declares. A spec that declares no air legs lowers byte-identically to
Phase 1 (`transferLowered_bytes_unchanged`). -/
def lowerEffect {St Args : Type} (name : String) (E : EffectSpec2 St Args) : EffectVmDescriptor2 :=
  lowerCS name E.traceWidth E.guardWidth (effectCircuit2 E) E.air

/-- ⚑ **THE WIDENING IS ADDITIVE, as a theorem over ALL specs.** A spec whose air block is empty —
which is every one of the ~29 existing `EffectSpec2` instances, since the field is defaulted —
lowers to EXACTLY what Phase 1 lowered: same constraint list, same PI count, no tables, no ranges.
So no existing statement about `lowerEffect` changes meaning, and §4a's byte-golden (unchanged
literal) is this theorem executed at transfer. -/
theorem lowerEffect_air_empty {St Args : Type} (name : String) (E : EffectSpec2 St Args)
    (h : E.air = {}) :
    lowerEffect name E =
      { name        := name
      , traceWidth  := E.traceWidth
      , piCount     := E.guardWidth + digestPinCols.length
      , tables      := []
      , constraints := (effectCircuit2 E).map lowerConstraint ++ lowerPiPins E.guardWidth
      , hashSites   := []
      , ranges      := [] } := by
  unfold lowerEffect lowerCS
  rw [h]
  simp [assemble, lowerAirLegs]

/-! ## §3 — two-sided faithfulness of the pass.

The deployed row denotation is mod-`p` (`VmConstraint.holdsVm` on a `.gate` asserts
`body ≡ 0 [ZMOD 2013265921]`); the framework's is ℤ equality. So the two directions are NOT
symmetric and we do not pretend they are: the emission direction is free, the soundness direction
carries the deployed canonicality envelope. -/

-- (`sub_modEq_zero_iff`, `eq_of_modEq_canon` and `lowerConstraint_holdsAt_iff` — the three that
-- mention no `EffectSpec2` — moved to `EffectLowerCore.lean` with the rest of the back end.)

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
  -- the emitted list is `((gates ++ air legs) ++ frame pins)`; the gate block is leftmost, so the
  -- lowered gate is a member however many air legs the spec declares.
  have hmem : lowerConstraint c ∈ (lowerEffect name E).constraints := by
    refine List.mem_append_left _ (List.mem_append_left _ ?_)
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

/-- **The pass's output for transfer** — a closed `EffectVmDescriptor2` on the live rail.
⚑ Transfer's spec declares NO air legs (`{}`), which is exactly the Phase-2 finding restated: the
widened vocabulary does not touch transfer, because transfer's gap is SEMANTIC (§9). -/
def transferLoweredDesc : EffectVmDescriptor2 :=
  lowerCS transferLoweredName 72 1 (balanceGuardGates ++ [cE2RestF, cE2Bind, cE2Log]) {}

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
    List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem
      (by simp [Dregg2.Circuit.Inst.Transfer.balanceGuardGates])))
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

/-! ## §8 — ⚑ THE FUSION: the deployed descriptor IS this pass's output (2026-08-01).

§5 refuted byte-equality at transfer and named why: transfer's gap is SEMANTIC, not vocabulary
(six guard conjuncts collapsed into one `propBit`; the commitment carried as an abstract portal).
Phase 2 took the OTHER kind of gap — a descriptor the source language simply could not SAY — and
proved the widened source says `dregg-dfa-routing-table::exact-public-v1` byte-exactly
(`dfaLowered = demoRoutingDesc`, by `rfl`).

**That theorem is now GONE, and its absence is the result.** An `rfl` between the compiler's output
and a hand-written twin is evidence only while the twin exists. `DfaRoutingTableEmit.lean` §2 now
DEFINES `tableRoutingDesc name tbl := lowerAir name TRT_WIDTH TRT_PI_COUNT [] (dfaAir tbl)` and its
four `VmConstraint2` `def`s are deleted, so restating the equality here would be `P = P` — a
tautology dressed as a differential, and this file is not going to ship one.

What replaced it, one module down and where the descriptor is actually deployed from:

* `DfaRoutingTableEmit.tableRoutingDesc_constraints` / `_tables` / `_ranges` / `_shape` — `rfl`
  pins of the compiler's emission against the deployed IR-v2 shape, transcribed from
  `circuit/src/descriptor_ir2.rs`. A change to a leg lowering, the leg ORDER or `assemble` goes RED
  there.
* the `emitVmJson2` byte-golden `#guard`, unchanged and now evaluating THE COMPILER'S OUTPUT
  against the bytes of `circuit/descriptors/by-name/dfa-routing-table-exact-public-v1.json`.
* `routeWit_satisfies` / `badTrace_not_satisfied` / `tableRouting_refines_classify` — the witness,
  the off-table canary and the general `classifyFrom` refinement, which were re-stated here as
  `dfaLowered_*` while there were two objects and are now simply theorems about the emitted one.

The prices this rung paid, kept for the record: the lookup + declared table are P1.5's **+51**
bucket, the window gate its **+13**, and the last-row pin was not sayable either — Phase 1's
`lowerPiPins` emits FIRST-row pins only. Three of the four constraint kinds were unsayable by
`EffectSpec2` and the fourth could not stand alone.

⚠ It is reached through `lowerAir`, not `lowerEffect`: the descriptor is not a full-state effect
and has no digest wires, so bolting the framework's `PIBindsDigests` surface onto it would emit a
descriptor nobody deployed. `lowerAir` and `lowerEffect` share the normalizer, the leg lowerings
and the emission order, and differ ONLY in that surface (`assemble`).

⚑ THE MODULE ORDER IS WHAT MAKES THE FUSION POSSIBLE — precisely, and not more than that.
`EffectLowerCore` (the back end) now sits BELOW `DfaRoutingTableEmit`, which sits below this file.
The edge is what lets the descriptor BE the compiler's output at all; it does not by itself forbid
hand-writing one beside it. What forbids that is the DELETION — there is no second `VmConstraint2`
literal left to drift from, and `tableRoutingDesc_constraints` goes red if the emission moves. -/

namespace DfaRung

open Dregg2.Circuit.Emit.DfaRoutingTableEmit
  (TRT_TID TRT_WIDTH TRT_PI_COUNT CURRENT SYMBOL NEXT PI_INITIAL PI_FINAL DEMO_NAME demoTbl
   demoRoutingDesc dfaAir)


/-! ### §8b — ⚑ THE REFUSAL, on this very rung.

The widened source can SAY a leg the deployed main rail cannot take. Re-authoring the SAME lookup
on the SERVING side of the bus is a one-token edit that changes nothing about the tuple or the
table — and the emitted descriptor stops being satisfiable at all, rather than quietly shipping
without its transition tooth. That direction is the one a byte-golden cannot see: a dropped leg
accepts strictly more. -/

/-- The same tuple, same table, `.provide` instead of `.query` — a one-token edit at the head of
THE DEPLOYED SOURCE'S OWN leg list (`DfaRoutingTableEmit.dfaAir`, the block the shipped descriptor
is compiled from), everything else identical. -/
def dfaAirServed : EffectAir :=
  { dfaAir demoTbl with
    legs := .lookup { table := TRT_TID, tuple := [.var CURRENT, .var SYMBOL, .var NEXT]
                    , op := BusOp.provide } :: (dfaAir demoTbl).legs.tail }

#guard dfaAirServed.mainRailOk == false

def dfaLoweredServed : EffectVmDescriptor2 :=
  lowerAir DEMO_NAME TRT_WIDTH TRT_PI_COUNT [] dfaAirServed

-- The one lookup became the two-constraint refusal: 4 → 5.
#guard dfaLoweredServed.constraints.length == 5

theorem mem_refuse_served :
    (VmConstraint2.base (.boundary VmRow.first (.const 1))) ∈ dfaLoweredServed.constraints :=
  List.mem_cons_self

/-- **THE REFUSED DESCRIPTOR HAS NO WITNESS AT ALL.** Not "accepts fewer traces" — none, for any
hash, any boundary, any non-empty trace. The unsatisfiable first-row boundary fires on row `0`. -/
theorem dfaLoweredServed_unsatisfiable
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace) (hne : t.rows ≠ []) :
    ¬ Satisfied2Public hash dfaLoweredServed minit mfin maddrs t := by
  intro h
  have hpos : 0 < t.rows.length := List.length_pos_of_ne_nil hne
  have hrc := h.rowConstraints 0 hpos _ mem_refuse_served
  have hone : (1 : ℤ) ≡ 0 [ZMOD 2013265921] := hrc rfl
  revert hone; decide

/-- …and it is therefore NOT the deployed descriptor: the source said something the rail refuses,
and the emitted bytes SAY SO. -/
theorem dfaLoweredServed_ne_deployed : dfaLoweredServed ≠ demoRoutingDesc := by
  intro h
  have := congrArg (fun d => d.constraints.length) h
  revert this
  decide

end DfaRung

/-! ## §9 — ⚑ WHAT STILL RESISTS, and the line between SYNTAX and SEMANTICS.

Phase 2 widened the SOURCE LANGUAGE. That closes the class of gaps where the deployed descriptor
does something `EffectSpec2` had no word for. It does NOT close the class where `EffectSpec2` has
a word but the word means something weaker. The two classes need different work and separating them
is the point of this section.

**VOCABULARY gaps — closed by this phase.** A lookup against a declared table, a range tooth, a
`.transition` continuity gate, a first/last boundary fix, a last-row PI pin. All five were
unsayable; all five are now legs, and §8 exhibits one deployed descriptor reached byte-exact
through them.

**SEMANTIC gaps — NOT closed, and no amount of syntax closes them.** These are transfer's, and
they are why §5's refutation stands untouched by Phase 2 (`transferLoweredDesc` still lowers a
spec whose `air` block is EMPTY):

1. **The collapsed guard.** `Inst/transfer.lean:99` supplies `guardGates := [cBitGuard]` — the
   6-conjunct `admitGuardA` committed as ONE `propBit` column asserted `= 1`. Giving the spec a
   `RangeLeg` does not turn that claim into the deployed 15-bit borrow chain; what is missing is
   that the spec never DECOMPOSES the guard into arithmetic at all. **A `propBit` is a claim; the
   borrow chain is a proof**, and the repair is to author `admitGuardA`'s conjuncts as gates over
   named columns — a change to what the spec SAYS, not to what it CAN say.
2. **The commitment as a carried portal.** `EffectCommit2.lean:120,183` carries `digest`/`RH`/`LH`
   as ABSTRACT functions; the deployed AIR BUILDS `state_commit` from four ordered `H4` sites
   in-circuit. `EffectAir` deliberately has no hash-site leg — adding one would let a spec DECLARE
   a site while `effectStateCommit2` still reads the abstract portal, i.e. two commitments that
   agree today and disagree later. The real repair is that `Surface2` must denote an emitted hash
   site, which is a change to the framework's commitment model.
   ⚠ Measured, and it is why the omission costs nothing on the deployed set: **no by-name
   descriptor uses a hash site at all** (P1.5's ladder, `+ hash sites: +0`).
3. **Single-row-ness of the ENCODER.** `WindowLeg` lets a spec ASSERT across two rows, but
   `encodeE2` still produces ONE `Assignment`. A spec can now state a continuity gate and cannot
   yet state the multi-row witness that satisfies it. `TableAirIR.Coherent` is the shape of the
   missing hypothesis (window `i`'s `nxt` IS window `i+1`'s `loc`, stated separately so a proof
   that forgets it fails to apply); the encoder-side counterpart is not built.
4. **The multiplicity / serving side.** Said by the source (`LookupLeg.mult`, `BusOp.provide`),
   REFUSED by the main rail, and legal on the `TableAir` rail. This one is neither a vocabulary gap
   nor a semantic gap in the spec — it is a rail seam, and §8b makes it a loud refusal instead of a
   silence.

**⚑ AND THE NUMBER THE KIND LADDER FLATTERS.** Kind coverage says 76/76; that is P1.5's question
("can the source SAY this descriptor's constraint kinds") and the honest answer to it. It is not
"could the pass emit these bytes". Measured over the same 76:

    kinds expressible by `lowerAir`                        76 / 76
    + every `gate` body already in builder normal form      8 / 76   ← byte-reachable today
    gate bodies NOT in the normal form the pass emits   12745 / 13983

The residual is a RENDERING difference, not a semantic one (`headToExpr_eval` proves the normalized
body means what the source meant). And it is not a defect of the normalizer, because **there is no
form to normalize TO**: measured across the 76, 37 descriptors render a unit coefficient as
`mul(const 1, x)` and 58 render it as a bare `x` — and **25 carry BOTH shapes inside a single
descriptor**. The hand-authored set is not internally consistent, so byte-agreement with it is not
a well-posed target for any canonical renderer.

Which makes the greenfield answer the right one and NOT a deferral: the deployed descriptors are
the thing to RE-EMIT from the compiler, not to imitate. That is a re-emission of by-name JSON +
the VK epoch it implies, and it is ordinary work — the reason it is not in this commit is that it
belongs to whoever owns the descriptor artifacts and the rotation, not that it is expensive.
⚠ The move this section deliberately does NOT make is bending `AirBuilder.headToExpr` toward one
of the two shapes: it would buy 8/76 → 21/76 while making the shared builder mimic an inconsistent
target, and it would break the `emitVmJson2` goldens of the 10 emitters whose committed bytes
already carry the `mul(const 1, ·)` form. That is the wrong direction of fit.

**The honest summary of the phase**: widening the source moved the reachable KIND coverage of the
deployed set from 25/76 to 76/76 and produced the first deployed descriptor a general pass emits
BYTE-EXACT. Byte reach is 8/76 and is bounded by the deployed set's own rendering inconsistency,
not by the source language. It moved transfer by zero, and that is the correct outcome — transfer
was never blocked on syntax. -/

/-! ## §10 — axiom-hygiene tripwires. -/

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
-- Phase 2.
#assert_axioms refuse_bites
#assert_axioms windowToLocal_eval
#assert_axioms lowerLeg_ne_nil
#assert_axioms lowerAirLegs_empty
#assert_axioms lowerEffect_air_empty
-- The fusion (§8): `dfaLowered_eq_deployed` and the four theorems it carried are DELETED, not
-- moved — the deployed descriptor IS this pass's output, so their restatements here would be
-- tautologies. Their content lives on `DfaRoutingTableEmit`'s own `#assert_axioms` block, over the
-- emitted object. What survives here is the REFUSAL rung, which has no counterpart there.
#assert_axioms DfaRung.dfaLoweredServed_unsatisfiable
#assert_axioms DfaRung.dfaLoweredServed_ne_deployed

end Dregg2.Circuit.Emit.EffectLower
