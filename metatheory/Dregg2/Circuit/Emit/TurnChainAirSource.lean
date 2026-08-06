/-
# `TurnChainAirSource` — the deployed TURN-CHAIN AIR, **derived** rather than hand-written.

## Why this file exists: the recurrence census, measured 2026-08-06

A census of the 179 emitted descriptors under `circuit/descriptors/` (69,964 constraints) split
every constraint body by shape. The result is the case for a source language, and it is not close:

    generator boilerplate (a column list + a width)   43,551   62.2%
    recurring parameterised gadget                     7,405   10.6%
    genuinely bespoke algebra                         19,008   27.2%

and inside the boilerplate the single largest entry is a one-column range lookup (22,938, 32.8% of
ALL constraints), followed by booleanity `x(x−1)` (9,924, 14.2%) — **one three-line fact emitted in
SIX distinct byte spellings** across 85 descriptors, because it is re-authored per emitter rather
than named once:

    m(v0,a(v0,m(c-1,c1)))            5,093   in 29 descriptors
    m(v0,a(v0,c-1))                  3,755   in 31 descriptors
    m(a(v0,c0),a(v0,c-1))              542   in  6 descriptors
    a(m(c1,m(v0,v0)),m(c-1,v0))        514   in 18 descriptors
    a(m(v0,v0),m(c-1,v0))               12   in  3 descriptors
    m(l0,a(l0,c-1))                      8   in  4 descriptors

Authorship at HEAD over the 111 routed by-name descriptors: **42 compiled** (the definition's RHS is
`EffectLower.lowerAir …` / `lowerEffect …`), **57 hand-written `VmConstraint2` literals**, 12 defined
through an intermediate. `dregg-turn-chain-binding-v2` was one of the 57.

## What this file establishes

`EffectVmEmitTurnChainBinding` hand-writes fourteen `VmConstraint2` values and assembles them into
`turnChainBindingDescriptor`. Every one of the fourteen is expressible in the EXISTING source
vocabulary (`EffectAirIR.AirLeg`) — six `window` legs, four `pin` legs, three more `window` legs at
`.first`, and one `lookup` leg — and

    turnChainDerived = turnChainBindingDescriptor   is `rfl`.

⚑ **`rfl`, at the whole `EffectVmDescriptor2`.** Not a shape count, not a per-constraint spot check,
not a JSON string comparison: definitional equality of the emitted record, so name, trace width, PI
count, tables, the ORDERED constraint list, hash sites and ranges all coincide by construction. Byte
identity of the artifact follows as a corollary (`turnChainDerived_emits_the_same_bytes`), because
`emitVmJson2` is a function of the descriptor. This is the acceptance test
`PastaMsmBucketed.rowGatesWith_pallas` established for a parameterised row, applied to a whole
descriptor: **the derivation captured what the hand-writer knew, and no gate moved.**

## What it does NOT claim

It does not claim the AIR is *right* — `EffectVmEmitTurnChainBinding`'s own rungs 1 and 2
(`turnChain_descriptor_refines_rust_air`, `turnChain_descriptor_iff_rust_air`) are what say that, and
they are unaffected because the object they quantify over is definitionally unchanged. It does not
claim `lowerAir` is proof-producing; that is a separate, live piece of work. What it establishes is
narrower and is the thing the census asked for: **for this descriptor the hand-work was not bespoke.
It was fourteen instances of five leg kinds, and the leg kinds already existed.**

⚑ **The lookup leg is the one place the source is WIDER than the hand-written form.** The
hand-written `perRowHash` writes `chipLookupTupleNarrow` directly in `EmittedExpr`; a `LookupLeg`
carries `List Expr` and the pass maps `CircuitEmit.emitExpr` over it. `chipTupleSrc` is that tuple at
the source level, and `chipTupleSrc_emits_narrow` proves the two agree — again `rfl`.

## Axiom hygiene
No `sorry`, no `native_decide`, no new axiom, no `#guard`. Every claim is a named theorem with an
`#assert_axioms` tripwire. ADDITIVE: nothing outside this file changes, so no descriptor re-emits
and no artifact byte moves.
-/
import Dregg2.Circuit.Emit.EffectLowerCore
import Dregg2.Circuit.Emit.EffectVmEmitTurnChainBinding

namespace Dregg2.Circuit.Emit.TurnChainAirSource

open Dregg2.Circuit (Expr)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg LookupLeg WindowLeg PiPinLeg)
open Dregg2.Circuit.TableAirIR (RowSel)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow)
open Dregg2.Exec.CircuitEmit (EmittedExpr emitExpr)
open Dregg2.Circuit.Emit.EffectVmEmitTurnChainBinding

set_option autoImplicit false

/-! ## §1 — the narrow-chip lookup tuple, at the SOURCE level.

`LookupLeg.tuple` is `List Expr` (the framework's own gate AST, so a spec author writes one
language); `lowerLookupLeg` maps `emitExpr` over it. The deployed narrow tuple is
`arity :: padTo 16 inputs ++ [digest column]` — this is that, one type down. -/

/-- The 18-wide NARROW chip lookup tuple in the source language: `arity`, the `CHIP_RATE`-padded
inputs, then the digest column. The `EmittedExpr` twin is `NarrowChip.chipLookupTupleNarrow`. -/
def chipTupleSrc (ins : List Expr) (digestCol : Nat) : List Expr :=
  Expr.const (ins.length : ℤ) ::
    (ins ++ List.replicate (CHIP_RATE - ins.length) (Expr.const 0)) ++ [Expr.var digestCol]

/-- The turn-chain preimage, in order: `[acc_in, old_root, new_root, idx]`. There is no IVC domain
tag and no `old_hash` — the same ordering the hand-written `hashInputs` reads. -/
def turnHashInputs : List Expr :=
  [ .var Chain.ACC_IN, .var Chain.OLD_ROOT, .var Chain.NEW_ROOT, .var Chain.IDX ]

/-- ⚑ **The source tuple emits the deployed narrow tuple.** The one place the source language and
the hand-written form use different types; they agree definitionally. -/
theorem chipTupleSrc_emits_narrow :
    (chipTupleSrc turnHashInputs Chain.ACC_OUT).map emitExpr
      = chipLookupTupleNarrow
          [.var Chain.ACC_IN, .var Chain.OLD_ROOT, .var Chain.NEW_ROOT, .var Chain.IDX]
          Chain.ACC_OUT := rfl

/-! ## §2 — the fourteen constraints, as legs.

Each leg is named for the site it denotes, in the emission order the target's ordered constraint
array requires. Read against `EffectVmEmitTurnChainBinding` §2: the correspondence is one-to-one. -/

open WindowExpr (loc nxt)

/-- 1. Temporal continuity `new_root[i] = old_root[i+1]` — a `.transition` window leg. -/
def legRootContinuity : AirLeg :=
  .window { sel := .transition
          , body := .add (loc Chain.NEW_ROOT) (.mul (.const (-1)) (nxt Chain.OLD_ROOT)) }

/-- 2. `old_root[0] = pi[genesis_root]`. -/
def legFirstOldRoot : AirLeg :=
  .pin { row := VmRow.first, col := Chain.OLD_ROOT, idx := Chain.PI_GENESIS_ROOT }

/-- 3. `new_root[last] = pi[final_root]`. -/
def legLastNewRoot : AirLeg :=
  .pin { row := VmRow.last, col := Chain.NEW_ROOT, idx := Chain.PI_FINAL_ROOT }

/-- 4. `acc_in[0] = 0` — a `.first` window leg, which the pass lowers through `windowToLocal?` to
the row-local `.boundary` the target's first-row constructor takes. -/
def legFirstAccZero : AirLeg :=
  .window { sel := .first, body := loc Chain.ACC_IN }

/-- 5. Digest continuity `acc_out[i] = acc_in[i+1]`. -/
def legAccContinuity : AirLeg :=
  .window { sel := .transition
          , body := .add (loc Chain.ACC_OUT) (.mul (.const (-1)) (nxt Chain.ACC_IN)) }

/-- 6. `acc_out[last] = pi[chain_digest]`. -/
def legLastAcc : AirLeg :=
  .pin { row := VmRow.last, col := Chain.ACC_OUT, idx := Chain.PI_CHAIN_DIGEST }

/-- 7. The per-row turn-chain hash, through the shared narrow Poseidon2 chip bus. Multiplicity and
side take their defaults (`.const 1`, `.query`) — the main rail's only expressible pair. -/
def legPerRowHash : AirLeg :=
  .lookup { table := poseidon2narrow
          , tuple := chipTupleSrc turnHashInputs Chain.ACC_OUT }

/-- 8. `idx[0] = 0`. -/
def legFirstIdxZero : AirLeg :=
  .window { sel := .first, body := loc Chain.IDX }

/-- 9. `idx[i+1] = idx[i] + 1`. -/
def legIdxIncrement : AirLeg :=
  .window { sel := .transition
          , body := .add (nxt Chain.IDX)
                      (.add (.mul (.const (-1)) (loc Chain.IDX)) (.const (-1))) }

/-- 10. `is_real` is boolean on EVERY row.

⚑ `sel := .all`, and the selector is the load-bearing part. A `.gate` leg would lower to
`.base (.gate …)`, which `Ir2Air` evaluates under `when_transition()` and is therefore VACUOUS on the
last row — unlike Rust's bare `assert_bool`. `.all` lowers to `windowGate ⟨body, false⟩`, which is
exact parity. The source has to be able to SAY the scope, which is why `RowSel` is carried rather
than inferred from the body. -/
def legIsRealBoolean : AirLeg :=
  .window { sel := .all
          , body := .mul (loc Chain.IS_REAL) (.add (loc Chain.IS_REAL) (.const (-1))) }

/-- 11. Real rows are a prefix: forbid a `0 → 1` step. -/
def legRealMonotone : AirLeg :=
  .window { sel := .transition
          , body := .mul (nxt Chain.IS_REAL)
                      (.add (.const 1) (.mul (.const (-1)) (loc Chain.IS_REAL))) }

/-- 12. `real_count[0] = is_real[0]`. -/
def legFirstRealCount : AirLeg :=
  .window { sel := .first
          , body := .add (loc Chain.REAL_COUNT) (.mul (.const (-1)) (loc Chain.IS_REAL)) }

/-- 13. `real_count[i+1] = real_count[i] + is_real[i+1]`. -/
def legRealCountAccum : AirLeg :=
  .window { sel := .transition
          , body := .add (nxt Chain.REAL_COUNT)
                      (.add (.mul (.const (-1)) (loc Chain.REAL_COUNT))
                            (.mul (.const (-1)) (nxt Chain.IS_REAL))) }

/-- 14. `real_count[last] = pi[num_turns]`. -/
def legLastRealCount : AirLeg :=
  .pin { row := VmRow.last, col := Chain.REAL_COUNT, idx := Chain.PI_NUM_TURNS }

/-- **The whole AIR as a source term.** Ordered, because the target's `constraints` is one ordered
array and this descriptor interleaves window · pin · pin · window · window · pin · lookup · … . A
source that emitted gates-then-lookups-then-pins could not say it. -/
def turnAir : EffectAir where
  tables  := []
  legs    := [ legRootContinuity, legFirstOldRoot, legLastNewRoot, legFirstAccZero
             , legAccContinuity, legLastAcc, legPerRowHash, legFirstIdxZero
             , legIdxIncrement, legIsRealBoolean, legRealMonotone, legFirstRealCount
             , legRealCountAccum, legLastRealCount ]
  ranges  := []
  extraPi := 0

/-- **The DERIVED descriptor.** No `VmConstraint2` appears on this right-hand side. -/
def turnChainDerived : EffectVmDescriptor2 :=
  Dregg2.Circuit.Emit.EffectLower.lowerAir
    "dregg-turn-chain-binding-v2" Chain.WIDTH Chain.PI_COUNT [] turnAir

/-! ## §3 — the acceptance test. -/

/-- ⚑⚑ **THE DERIVATION IS EXACT — `rfl` at the whole descriptor.**

Definitional equality of two `EffectVmDescriptor2` records, so every field agrees: the name, the
trace width, the PI count, the (empty) table roster, the FOURTEEN constraints IN ORDER, the (empty)
hash sites and the (empty) ranges. Nothing was normalised away, nothing was re-scoped, no gate
moved. This is the acceptance test for a derivation: it proves the source term captured exactly what
the hand-writer wrote, and it is the strongest form available — `PastaMsmBucketed.rowGatesWith_pallas`
is the same discipline one level down. -/
theorem turnChainDerived_eq_handwritten :
    turnChainDerived
      = Dregg2.Circuit.Emit.EffectVmEmitTurnChainBinding.turnChainBindingDescriptor := rfl

/-- **Byte identity, as a corollary.** `emitVmJson2` is a function of the descriptor, so the derived
object serialises to the artifact the hand-written one serialises to. The golden string in
`EffectVmEmitTurnChainBinding` therefore pins this object too, and re-emitting moves zero bytes. -/
theorem turnChainDerived_emits_the_same_bytes :
    emitVmJson2 turnChainDerived
      = emitVmJson2 Dregg2.Circuit.Emit.EffectVmEmitTurnChainBinding.turnChainBindingDescriptor :=
  congrArg emitVmJson2 turnChainDerived_eq_handwritten

/-- Every leg the source declares has a deployed main-rail image — no leg lowered to the
UNSATISFIABLE refusal pair. Without this the `rfl` above could hold by BOTH sides being wrong. -/
theorem turnAir_mainRailOk : turnAir.mainRailOk = true := rfl

/-- Every PI pin indexes a slot the descriptor declares. -/
theorem turnAir_pinsFit : turnAir.pinsFit Chain.PI_COUNT = true := rfl

/-! ## §4 — shape pins, as named theorems.

Named rather than `#guard`ed: a `#guard` checks one closed instance, leaves no term, and is
invisible to axiom accounting (`metatheory/docs/GUARD-DISCIPLINE.md`). A count that a re-emission
could move is worth a name. -/

/-- Fourteen legs in, fourteen constraints out — so no leg silently expanded or collapsed. -/
theorem turnAir_leg_count : turnAir.legs.length = 14 := rfl

theorem turnChainDerived_constraint_count : turnChainDerived.constraints.length = 14 := rfl

/-- The per-kind census of the source, matching the deployed descriptor's own inventory: nine window
legs (six `.transition`, one `.all`, three `.first` — the last three land as `boundary`), four PI
pins, one chip lookup. -/
theorem turnAir_kind_counts :
    turnAir.windowCount = 9 ∧ turnAir.pinCount = 4 ∧ turnAir.lookupCount = 1
      ∧ turnAir.gateCount = 0 ∧ turnAir.limbsCount = 0 ∧ turnAir.bindCount = 0 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ⚑ The source declares NO flat `.gate` leg at all. Every row-local assertion carries an explicit
`RowSel`, which is the difference between an every-row booleanity and one that is vacuous on the
last row. -/
theorem turnAir_has_no_bare_gate_leg : turnAir.gateCount = 0 := rfl

theorem turnChainDerived_width : turnChainDerived.traceWidth = 7 := rfl
theorem turnChainDerived_piCount : turnChainDerived.piCount = 4 := rfl
theorem turnChainDerived_no_tables : turnChainDerived.tables = [] := rfl
theorem turnChainDerived_no_ranges : turnChainDerived.ranges = [] := rfl
theorem turnChainDerived_no_hashSites : turnChainDerived.hashSites = [] := rfl

/-! ## §5 — the proof ladder is inherited, not restated.

`EffectVmEmitTurnChainBinding` proves rung 1 (`turnChain_descriptor_refines_rust_air`) and rung 2
(`turnChain_descriptor_iff_rust_air`) about `turnChainBindingDescriptor`. Because the derived object
IS that object definitionally, those conclusions transfer with no new hypothesis — stated here so the
transfer is a theorem rather than a reader's inference. -/

/-- **Rung 2, at the DERIVED descriptor.** Against the canonical genuine chip row, the derived
descriptor's full constraint set is equivalent to the exact fourteen-site Rust AIR semantics. -/
theorem turnChainDerived_iff_rust_air
    (hash : List ℤ → ℤ) (env : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv) (isFirst isLast : Bool) :
    (∀ c ∈ turnChainDerived.constraints,
        c.holdsAt hash
          (Dregg2.Circuit.Emit.EffectVmEmitTurnChainBinding.canonicalRowTf hash env)
          env isFirst isLast)
      ↔ Dregg2.Circuit.Emit.EffectVmEmitTurnChainBinding.RustTurnChainRow hash env isFirst isLast :=
  Dregg2.Circuit.Emit.EffectVmEmitTurnChainBinding.turnChain_descriptor_iff_rust_air
    hash env isFirst isLast

/-! ## §6 — axiom hygiene. -/

#assert_axioms chipTupleSrc_emits_narrow
#assert_axioms turnChainDerived_eq_handwritten
#assert_axioms turnChainDerived_emits_the_same_bytes
#assert_axioms turnAir_mainRailOk
#assert_axioms turnAir_pinsFit
#assert_axioms turnAir_leg_count
#assert_axioms turnChainDerived_constraint_count
#assert_axioms turnAir_kind_counts
#assert_axioms turnAir_has_no_bare_gate_leg
#assert_axioms turnChainDerived_width
#assert_axioms turnChainDerived_piCount
#assert_axioms turnChainDerived_no_tables
#assert_axioms turnChainDerived_no_ranges
#assert_axioms turnChainDerived_no_hashSites
#assert_axioms turnChainDerived_iff_rust_air

end Dregg2.Circuit.Emit.TurnChainAirSource
