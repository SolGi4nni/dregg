/-
# Dregg2.Circuit.Emit.TemporalPredicateEmit — the emit-from-Lean descriptor for the TEMPORAL
predicate family (the GTE continuous-predicate AIR).

## What this file IS

A REAL `EffectVmDescriptor2` that DECLARES, in the IR-v2 grammar, the statement the hand AIR
`circuit/src/temporal_predicate_dsl.rs` (`TemporalPredicateDsl`, the deployed GTE variant)
enforces: "the predicate `value ≥ threshold` held at every step of a padded run, with a
non-negativity range proof on `diff = value − threshold`, a monotone step/accumulator counter,
and the audit-#3 anti-forge bindings (threshold constancy + first/last state-root pins)."

It replaces the hand AIR's `eval_constraints` / `boundary_constraints` SEMANTICS with an emitted
descriptor whose:

* **C1** (`diff = value − threshold`) is a `Base .gate`;
* **C2** (30× bit-boolean), **C3** (bit recompose `Σ 2^i·bit_i = diff`), **C4** (high bit zero)
  together are the `diff < 2^29` non-negativity RANGE GADGET, emitted as `Base .gate`s exactly as
  the hand AIR writes them (the deployed AIR does the range in-line, NOT via a Range-table lookup,
  so the faithful emit is bit-gates — a below-threshold value produces a `diff` whose bits cannot
  recompose under a zero high bit, so C3/C4 are UNSAT: the range tooth BITES);
* **C5/C6** (the `acc+1` / `step+1` auxiliaries) are `Base .gate`s;
* **T1/T2/T3** (cross-row `next.acc = local.acc_plus_one`, `next.step = local.step_plus_one`,
  and the THRESHOLD-constancy anti-forge weld) are `WindowGate`s (`on_transition = true`);
* the boundary row-0 `acc = 1` / `step = 0` are `Base .boundary .first`, and the four PI bindings
  (last `acc = padded_len`, first `threshold`, first/last `state_root`) are `Base .piBinding` —
  the audit-`ce1e2def #3` anti-forge surface.

The emitted JSON (`emitVmJson2`) is BYTE-PINNED below (`#guard`). The Rust equality gate
(`circuit-prove/tests/temporal_predicate_emit_gate.rs`) DECODES this exact string via
`parse_vm_descriptor2`, asserts it equals an independently Rust-built descriptor, proves an honest
GTE run through the REAL `prove_vm_descriptor2` (ACCEPT), and mutates the witness (a below-threshold
value → range gadget UNSAT; a forged threshold/state-root/padded-len PI → binding UNSAT; a broken
counter → gate/window UNSAT) to force real rejection.

## Documented gaps preserved (NOT laundered)
The hand AIR (a) does NOT bind per-step VALUE into PIs (safe by contract — the promise is
"predicate held", not "values were X"), and (b) pins only the FIRST and LAST state roots (interior
roots are unbound). Both are carried faithfully: the descriptor emits exactly the four PI bindings
the hand AIR emits, no more.

## Axiom hygiene
Definitional descriptor + a byte-pinned `#guard` on its wire string + genuinely-proven,
non-vacuous semantic lemmas (the C1 diff gate and the C2 bit-boolean range tooth — TRUE and FALSE
witnessed). NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.TemporalPredicateEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 WindowExpr WindowConstraint emitVmJson2)

set_option autoImplicit false

/-! ## §1 — The trace column layout (38 columns; the deployed GTE layout).
Mirrors `temporal_predicate_dsl.rs` `col::*` exactly. -/

/-- The attribute value at this step. -/
def VALUE : Nat := 0
/-- The (constant) threshold. -/
def THRESHOLD : Nat := 1
/-- `diff = value − threshold` (the non-negativity witness). -/
def DIFF : Nat := 2
/-- First of the 30 bit columns decomposing `diff`. -/
def DIFF_BITS_START : Nat := 3
/-- The bit-decomposition width. -/
def NUM_DIFF_BITS : Nat := 30
/-- The 1-indexed step accumulator (row 0 → 1). -/
def ACCUMULATOR : Nat := 33
/-- The 0-indexed step counter. -/
def STEP_INDEX : Nat := 34
/-- `accumulator + 1` (the cross-row continuity auxiliary). -/
def ACC_PLUS_ONE : Nat := 35
/-- `step_index + 1`. -/
def STEP_PLUS_ONE : Nat := 36
/-- The per-step state root (bound to the IVC chain at the boundary). -/
def STATE_ROOT : Nat := 37
/-- Total main-trace width. -/
def TRACE_WIDTH : Nat := 38

/-! ## §2 — Public inputs `[padded_len, threshold, initial_state_root, final_state_root]`. -/

def PI_PADDED_LEN : Nat := 0
def PI_THRESHOLD : Nat := 1
def PI_INITIAL_STATE_ROOT : Nat := 2
def PI_FINAL_STATE_ROOT : Nat := 3
def PI_COUNT : Nat := 4

/-! ## §3 — The per-row gate bodies (`Base .gate`). -/

/-- **C1**: `diff − (value − threshold) = 0`. -/
def diffBody : EmittedExpr :=
  .add (.var DIFF) (.add (.mul (.const (-1)) (.var VALUE)) (.var THRESHOLD))

/-- **C2[i]**: the `i`-th diff bit is boolean, `bit·(bit − 1) = 0`. -/
def bitBinaryBody (i : Nat) : EmittedExpr :=
  let b := DIFF_BITS_START + i
  .mul (.var b) (.add (.var b) (.const (-1)))

/-- The `Σ_{i<30} 2^i · bit_i` reconstruction sum (a right fold, outermost term `i = 0`). -/
def recomposeSum : EmittedExpr :=
  (List.range NUM_DIFF_BITS).foldr
    (fun i acc => .add (.mul (.const ((2 : Int) ^ i)) (.var (DIFF_BITS_START + i))) acc)
    (.const 0)

/-- **C3**: `Σ 2^i·bit_i − diff = 0` (bit reconstruction). -/
def recomposeBody : EmittedExpr :=
  .add recomposeSum (.mul (.const (-1)) (.var DIFF))

/-- **C4**: the high bit is zero (⇒ `diff < 2^29` ⇒ non-negative). -/
def highBitBody : EmittedExpr := .var (DIFF_BITS_START + NUM_DIFF_BITS - 1)

/-- **C5**: `acc_plus_one − accumulator − 1 = 0`. -/
def accStepBody : EmittedExpr :=
  .add (.var ACC_PLUS_ONE) (.add (.mul (.const (-1)) (.var ACCUMULATOR)) (.const (-1)))

/-- **C6**: `step_plus_one − step_index − 1 = 0`. -/
def stepIncBody : EmittedExpr :=
  .add (.var STEP_PLUS_ONE) (.add (.mul (.const (-1)) (.var STEP_INDEX)) (.const (-1)))

/-! ## §4 — The cross-row window bodies (`WindowGate`, `on_transition = true`). -/

/-- **T1**: `next[accumulator] − local[acc_plus_one] = 0`. -/
def t1Body : WindowExpr := .add (.nxt ACCUMULATOR) (.mul (.const (-1)) (.loc ACC_PLUS_ONE))
/-- **T2**: `next[step_index] − local[step_plus_one] = 0`. -/
def t2Body : WindowExpr := .add (.nxt STEP_INDEX) (.mul (.const (-1)) (.loc STEP_PLUS_ONE))
/-- **T3**: `next[threshold] − local[threshold] = 0` (the audit-#3 constancy anti-forge weld). -/
def t3Body : WindowExpr := .add (.nxt THRESHOLD) (.mul (.const (-1)) (.loc THRESHOLD))

/-! ## §5 — The full constraint list. -/

/-- The per-row `Base .gate`s: C1, the 30 bit-boolean C2 gates, then C3, C4, C5, C6. -/
def perRowGates : List VmConstraint2 :=
  (.base (.gate diffBody))
    :: (List.range NUM_DIFF_BITS).map (fun i => VmConstraint2.base (.gate (bitBinaryBody i)))
    ++ [ .base (.gate recomposeBody)
       , .base (.gate highBitBody)
       , .base (.gate accStepBody)
       , .base (.gate stepIncBody) ]

/-- The three cross-row `WindowGate`s (T1/T2/T3, `on_transition = true`). -/
def windowGates : List VmConstraint2 :=
  [ .windowGate ⟨t1Body, true⟩
  , .windowGate ⟨t2Body, true⟩
  , .windowGate ⟨t3Body, true⟩ ]

/-- The boundary + PI-binding surface (the audit-#3 anti-forge weld). -/
def boundaries : List VmConstraint2 :=
  [ .base (.boundary VmRow.first (.add (.var ACCUMULATOR) (.const (-1))))   -- row 0: acc = 1
  , .base (.boundary VmRow.first (.var STEP_INDEX))                          -- row 0: step = 0
  , .base (.piBinding VmRow.last ACCUMULATOR PI_PADDED_LEN)                  -- last: acc = padded_len
  , .base (.piBinding VmRow.first THRESHOLD PI_THRESHOLD)                    -- row 0: threshold = pi[1]
  , .base (.piBinding VmRow.first STATE_ROOT PI_INITIAL_STATE_ROOT)          -- row 0: state_root = pi[2]
  , .base (.piBinding VmRow.last STATE_ROOT PI_FINAL_STATE_ROOT) ]          -- last: state_root = pi[3]

/-- **`temporalPredicateDesc`** — the emitted temporal-predicate (GTE) descriptor. Main-only:
no chip / range / memory tables (Presence-detected empty), exactly like the hand AIR's single
main trace. -/
def temporalPredicateDesc : EffectVmDescriptor2 :=
  { name        := "dregg-temporal-predicate-gte::dsl-v1"
  , traceWidth  := TRACE_WIDTH
  , piCount     := PI_COUNT
  , tables      := []
  , constraints := perRowGates ++ windowGates ++ boundaries
  , hashSites   := []
  , ranges      := [] }

/-! ## §6 — The byte-pinned wire golden. -/

/-! THE EQUALITY-GATE ANCHOR: this exact string is embedded verbatim in
`circuit-prove/tests/temporal_predicate_emit_gate.rs` (`GOLDEN_JSON`), decoded there via
`parse_vm_descriptor2`, and proven. A drift on either side breaks THIS `#guard` (Lean) or the Rust
`assert_eq!(decoded, hand_built)`. -/

#guard emitVmJson2 temporalPredicateDesc ==
  "{\"name\":\"dregg-temporal-predicate-gte::dsl-v1\",\"ir\":2,\"trace_width\":38,\"public_input_count\":4,\"tables\":[],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":0}},\"r\":{\"t\":\"var\",\"v\":1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":9},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":10},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":11},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":12},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":13},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":14},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":15},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":16},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":17},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":18},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":19},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":21},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":22},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":23},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":24},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":25},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":26},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":27},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":27},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":28},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":29},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":29},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":30},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":30},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":31},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":31},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":32},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":3}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":4}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":4},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":8},\"r\":{\"t\":\"var\",\"v\":6}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":16},\"r\":{\"t\":\"var\",\"v\":7}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":32},\"r\":{\"t\":\"var\",\"v\":8}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":64},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":128},\"r\":{\"t\":\"var\",\"v\":10}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":256},\"r\":{\"t\":\"var\",\"v\":11}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":512},\"r\":{\"t\":\"var\",\"v\":12}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1024},\"r\":{\"t\":\"var\",\"v\":13}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2048},\"r\":{\"t\":\"var\",\"v\":14}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":4096},\"r\":{\"t\":\"var\",\"v\":15}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":8192},\"r\":{\"t\":\"var\",\"v\":16}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":16384},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":32768},\"r\":{\"t\":\"var\",\"v\":18}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":65536},\"r\":{\"t\":\"var\",\"v\":19}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":131072},\"r\":{\"t\":\"var\",\"v\":20}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":262144},\"r\":{\"t\":\"var\",\"v\":21}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":524288},\"r\":{\"t\":\"var\",\"v\":22}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1048576},\"r\":{\"t\":\"var\",\"v\":23}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2097152},\"r\":{\"t\":\"var\",\"v\":24}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":4194304},\"r\":{\"t\":\"var\",\"v\":25}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":8388608},\"r\":{\"t\":\"var\",\"v\":26}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":16777216},\"r\":{\"t\":\"var\",\"v\":27}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":33554432},\"r\":{\"t\":\"var\",\"v\":28}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":67108864},\"r\":{\"t\":\"var\",\"v\":29}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":134217728},\"r\":{\"t\":\"var\",\"v\":30}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":268435456},\"r\":{\"t\":\"var\",\"v\":31}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":536870912},\"r\":{\"t\":\"var\",\"v\":32}},\"r\":{\"t\":\"const\",\"v\":0}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":2}}}},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":32}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":35},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":33}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":36},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":34}},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":33},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":35}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":34},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":36}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":1}}}},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"var\",\"v\":34}},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":33,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":1,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":37,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":37,\"pi_index\":3}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §7 — Non-vacuous semantic lemmas (the emitted gates' teeth). -/

/-- The C1 diff gate is zero EXACTLY when `diff = value − threshold` — the emitted `.gate` face of
the hand AIR's C1. -/
theorem diff_gate_zero_iff (a : Assignment) :
    diffBody.eval a = 0 ↔ a DIFF = a VALUE - a THRESHOLD := by
  simp only [diffBody, EmittedExpr.eval]
  constructor <;> intro h <;> omega

/-- The C2 bit-boolean gate is zero EXACTLY when the bit is `0` or `1` — the load-bearing tooth of
the range gadget (a non-boolean "bit" cannot pad a spurious recompose). -/
theorem bit_binary_zero_iff (a : Assignment) (i : Nat) :
    (bitBinaryBody i).eval a = 0
      ↔ (a (DIFF_BITS_START + i) = 0 ∨ a (DIFF_BITS_START + i) = 1) := by
  simp only [bitBinaryBody, EmittedExpr.eval]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (by omega)
  · rintro (h | h) <;> rw [h] <;> ring

/-- The T3 threshold-constancy window gate is zero EXACTLY when the threshold is held across the
row window — the emitted face of the anti-forge weld. -/
theorem t3_constancy_zero_iff (env : VmRowEnv) :
    t3Body.eval env = 0 ↔ env.nxt THRESHOLD = env.loc THRESHOLD := by
  simp only [t3Body, WindowExpr.eval]
  constructor <;> intro h <;> omega

-- Non-vacuity witnesses (TRUE and FALSE), Merkle-template style.
#guard decide (diffBody.eval (fun i => if i = DIFF then 5 else if i = VALUE then 8 else 3) = 0)
#guard decide (¬ (diffBody.eval (fun i => if i = DIFF then 99 else if i = VALUE then 8 else 3) = 0))
#guard decide ((bitBinaryBody 0).eval (fun i => if i = DIFF_BITS_START then 1 else 0) = 0)
#guard decide (¬ ((bitBinaryBody 0).eval (fun i => if i = DIFF_BITS_START then 2 else 0) = 0))

-- Shape pins.
#guard temporalPredicateDesc.traceWidth == TRACE_WIDTH
#guard temporalPredicateDesc.piCount == PI_COUNT
#guard temporalPredicateDesc.tables == []
#guard temporalPredicateDesc.constraints.length == 1 + NUM_DIFF_BITS + 4 + 3 + 6
#guard temporalPredicateDesc.constraints.length == 44

#assert_axioms diff_gate_zero_iff
#assert_axioms bit_binary_zero_iff
#assert_axioms t3_constancy_zero_iff

end Dregg2.Circuit.Emit.TemporalPredicateEmit
