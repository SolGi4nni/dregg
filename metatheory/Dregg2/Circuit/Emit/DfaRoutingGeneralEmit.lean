/-
# Dregg2.Circuit.Emit.DfaRoutingGeneralEmit — the emit-from-Lean descriptor for a SECOND concrete
DFA table over the SAME `dregg-dfa-routing-v1` running-hash carrier: the 3-state INJECTION DFA
(`zkoracle-prove/src/zk_leg.rs`, `injection_dfa_table`).

## What this file IS (and why it exists beside `DfaRoutingEmit`)

`DfaRoutingEmit.lean` pins ONE routing descriptor whose transition gate is hardcoded to the TOGGLE
automaton (`step(s,y) = s XOR y`, interpolant `cur + sym − 2·cur·sym`, grid `{0,1}²`). The zkOracle
injection leg is a DIFFERENT automaton: three states `clean=0 / brace=1 / dead=2`, symbols
`other=0 / brace=1`, recognizing `{{` in its absorbing DEAD state. So it needs its OWN routing
descriptor over the SAME carrier — the entry-hash chip, the running-hash chip, the copy-forward
accumulator, the continuity/seed/boundary skeleton are IDENTICAL to `DfaRoutingEmit`; only two gates
change: the STATE grid (now `{0,1,2}`, degree-3 vanishing) and the TRANSITION interpolant (the
injection step table's unique bivariate interpolant over `{0,1,2}×{0,1}`).

This is the pathfinder that moves `zk_leg.rs` off the legacy hand STARK (`circuit/src/stark.rs`,
`prove_dfa_routing`) and onto the plonky3 descriptor prover (`descriptor_ir2::prove_vm_descriptor2`):
the leg builds THIS descriptor's trace from the field's `{`-projection and proves it via the general
IR-v2 prover. The public statement is unchanged — `[initial, final, table_commitment,
route_commitment]`, verifier accepts iff `final` is a non-injecting state (`≠ 2`).

## The injection transition interpolant (the ONE new tooth)

`step` over the grid `{0,1,2} × {0,1}`:

| cur \ sym | 0 (other) | 1 (brace) |
|-----------|-----------|-----------|
| 0 clean   | 0         | 1         |
| 1 brace   | 0         | 2         |
| 2 dead    | 2         | 2         |

Its unique bivariate interpolant `P(a,b)` (degree ≤2 in `a`, ≤1 in `b`) has a `1/2` coefficient, so
the gate is written in DOUBLED form `2·next − 2·P(a,b)` to keep every constant a small integer:

  `G(a,b) = 2·next − 2a² + 2a + 3a²b − 5ab − 2b`.

Over BabyBear (odd prime, `2` invertible) `G == 0 ⟺ next == P(a,b)`, and on the grid `P == step`.
The grid-vanishing gates `a·(a−1)·(a−2)` and `b·(b−1)` pin `a ∈ {0,1,2}`, `b ∈ {0,1}` so the
interpolant is only ever evaluated at real grid points (off-grid escapes impossible) — the exact
grid-range tooth, mirroring `DfaRoutingEmit` and `circuit/src/dsl/dfa_routing.rs`'s
`vanishing_on_grid` + `TableFunction`.

## The byte-pinned wire golden + axiom hygiene

`emitVmJson2 injectionRoutingDesc` is BYTE-PINNED below (`#guard`). Definitional descriptor + the
byte-pin + three genuinely-proven, non-vacuous semantic lemmas (the injection transition tooth, the
C2 continuity window, the C3 copy-forward window — each TRUE iff its relation holds, FALSE
otherwise). `#assert_axioms` on each is pure `omega`. NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.GateExpr

namespace Dregg2.Circuit.Emit.DfaRoutingGeneralEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId WindowExpr WindowConstraint
   chipLookupTuple CHIP_RATE CHIP_OUT_LANES emitVmJson2)

set_option autoImplicit false

/-! ## §1 — The trace column layout (identical to `DfaRoutingEmit`: 8 base + 2×7 chip lanes). -/

/-- `current_state` — the DFA state entering this step. -/
def CURRENT : Nat := 0
/-- `symbol` — the input category read at this step (`other=0 / brace=1`). -/
def SYMBOL : Nat := 1
/-- `next_state` — the DFA state after this step. -/
def NEXT : Nat := 2
/-- `table_entry_hash` = `hash_4_to_1(current, symbol, next, 0)` (chip lookup out0). -/
def ENTRY_HASH : Nat := 3
/-- `running_hash` = `hash_2_to_1(acc, entry)` — the rolling route commitment (chip lookup out0). -/
def RUNNING_HASH : Nat := 4
/-- First-row selector: 1 at row 0 (gates the seed), 0 elsewhere. -/
def IS_FIRST : Nat := 5
/-- Fixed-zero lane: the 4th input to the 4-arity entry hash. -/
def ZERO_LANE : Nat := 6
/-- The COPY-FORWARD accumulator: `acc[0] = pi[table_commitment]`, `acc[i+1] = running[i]`. -/
def ACC : Nat := 7

/-- The seven exposed permutation lane columns 1..7 of the entry-hash chip lookup. -/
def ENTRY_LANES : List Nat := [8, 9, 10, 11, 12, 13, 14]
/-- The seven exposed permutation lane columns 1..7 of the running-hash chip lookup. -/
def RUNNING_LANES : List Nat := [15, 16, 17, 18, 19, 20, 21]

/-- Total main-trace width: 8 base columns + 7 + 7 chip lanes. -/
def DFA_WIDTH : Nat := 22

/-- pi[0] `initial_state` (B1). -/
def PI_INITIAL : Nat := 0
/-- pi[1] `final_state` (B2 — the classification). -/
def PI_FINAL : Nat := 1
/-- pi[2] `table_commitment` (the running-hash seed). -/
def PI_TABLE : Nat := 2
/-- pi[3] `route_commitment` (B3 — the binding). -/
def PI_ROUTE : Nat := 3
/-- Number of public inputs. -/
def DFA_PI_COUNT : Nat := 4

/-! ## §2 — The constraint list. -/

/-- C1 entry hash: an arity-4 `Poseidon2Chip` lookup absorbing `[current, symbol, next, zero_lane]`,
binding out0 to `ENTRY_HASH` (the `hash_4_to_1(current, symbol, next, 0)` shape). -/
def entryHashLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2,
    chipLookupTuple [.var CURRENT, .var SYMBOL, .var NEXT, .var ZERO_LANE] ENTRY_HASH ENTRY_LANES⟩

/-- C3 per-row running hash: an arity-2 `Poseidon2Chip` lookup absorbing `[acc, entry_hash]`,
binding out0 to `RUNNING_HASH` (the `hash_2_to_1(acc, entry)` shape). -/
def runningHashLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2,
    chipLookupTuple [.var ACC, .var ENTRY_HASH] RUNNING_HASH RUNNING_LANES⟩

/-- `zero_lane == 0` on every (transition-domain) row: the fixed padding lane of the entry hash. -/
def zeroLaneGate : VmConstraint2 := .base (.gate (.var ZERO_LANE))

/-- `is_first` is boolean: `is_first · (is_first − 1) == 0`. -/
def isFirstBoolGate : VmConstraint2 :=
  .base (.gate (Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toEmitted
    (Dregg2.Circuit.GateExpr.gBool (.leaf IS_FIRST))))

theorem isFirstBoolGate_eq :
    isFirstBoolGate = .base (.gate (.mul (.var IS_FIRST) (.add (.var IS_FIRST) (.const (-1))))) := rfl

/-- state on grid `{0,1,2}`: `current · (current − 1) · (current − 2) == 0` -- the alphabet gate
`∏(cur − sᵢ)` at `GateExpr.gAlphabet CURRENT [0,1,2]`, degree 3, the three injection states. ⚑ THE
GENUINE GENERALIZATION: `DfaRoutingEmit.stateGridGate` is the SAME parameterized gadget at `[0,1]`
-- one def (`gAlphabet`), two instantiations, not two copies that happen to agree. -/
def stateGridGate : VmConstraint2 :=
  .base (.gate (Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toEmitted
    (Dregg2.Circuit.GateExpr.gAlphabet (.leaf CURRENT) [0, 1, 2])))

/-- ⚑ **THE BYTE PIN, AT DEGREE 3.** `rfl` -- `gAlphabet`'s zero-elision (`gSub`) is what makes this
match the hand-written degree-3 product exactly rather than carrying a spurious `(cur − 0)` factor. -/
theorem stateGridGate_eq :
    stateGridGate = .base (.gate
      (.mul (.mul (.var CURRENT) (.add (.var CURRENT) (.const (-1))))
            (.add (.var CURRENT) (.const (-2))))) := rfl

/-- symbol on grid `{0,1}`: `symbol · (symbol − 1) == 0` (the `∏(sym − bⱼ)` vanishing poly). -/
def symbolGridGate : VmConstraint2 :=
  .base (.gate (Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toEmitted
    (Dregg2.Circuit.GateExpr.gBool (.leaf SYMBOL))))

theorem symbolGridGate_eq :
    symbolGridGate = .base (.gate (.mul (.var SYMBOL) (.add (.var SYMBOL) (.const (-1))))) := rfl

/-- GAP-A transition body (DOUBLED interpolant form): `2·next − 2a² + 2a + 3a²b − 5ab − 2b`, where
`a = current`, `b = symbol`. Over BabyBear (`2` invertible) this vanishes exactly when
`next == P(a,b)`, the unique interpolant of the injection `step` table over `{0,1,2}×{0,1}` — the
route-follows-the-table tooth for the injection DFA. -/
def transitionBody : EmittedExpr :=
  .add (.mul (.const 2) (.var NEXT))
    (.add (.mul (.const (-2)) (.mul (.var CURRENT) (.var CURRENT)))
      (.add (.mul (.const 2) (.var CURRENT))
        (.add (.mul (.const 3) (.mul (.mul (.var CURRENT) (.var CURRENT)) (.var SYMBOL)))
          (.add (.mul (.const (-5)) (.mul (.var CURRENT) (.var SYMBOL)))
            (.mul (.const (-2)) (.var SYMBOL))))))

/-- The GAP-A transition Base gate (the injection route-follows-the-table tooth). -/
def transitionGate : VmConstraint2 := .base (.gate transitionBody)

/-- C2 continuity body: `Nxt(current) − Loc(next)` (next row's `current` == this row's `next`).
⚑ `GateExpr.gThread` at the window view. -/
def contWindowBody : WindowExpr :=
  Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toWindow
    (Dregg2.Circuit.GateExpr.gThread CURRENT NEXT)

theorem contWindowBody_eq :
    contWindowBody = WindowExpr.add (.nxt CURRENT) (.mul (.const (-1)) (.loc NEXT)) := rfl

/-- The C2 continuity `WindowGate`, asserted on the transition (every row but the last). -/
def continuityWindow : VmConstraint2 := .windowGate ⟨contWindowBody, true⟩

/-- C3 copy-forward body: `Nxt(acc) − Loc(running)` (so `acc[i+1] = running[i]`).
⚑ `GateExpr.gThread`. -/
def copyForwardBody : WindowExpr :=
  Dregg2.Circuit.GateExpr.render Dregg2.Circuit.GateExpr.toWindow
    (Dregg2.Circuit.GateExpr.gThread ACC RUNNING_HASH)

theorem copyForwardBody_eq :
    copyForwardBody = WindowExpr.add (.nxt ACC) (.mul (.const (-1)) (.loc RUNNING_HASH)) := rfl

/-- The C3 copy-forward `WindowGate`, asserted on the transition. -/
def copyForwardWindow : VmConstraint2 := .windowGate ⟨copyForwardBody, true⟩

/-- B1: first row `current_state == pi[initial_state]`. -/
def b1InitialPin : VmConstraint2 := .base (.piBinding VmRow.first CURRENT PI_INITIAL)

/-- `is_first` pinned to 1 on the first row (`is_first − 1 == 0`, forcing the seed to fire there). -/
def isFirstPinned : VmConstraint2 := .base (.boundary VmRow.first (.add (.var IS_FIRST) (.const (-1))))

/-- The C3/seed pin: first row `acc == pi[table_commitment]`, so `running₀ =
hash_2_to_1(table_commitment, entry₀)`. -/
def seedAccPin : VmConstraint2 := .base (.piBinding VmRow.first ACC PI_TABLE)

/-- B2: last row `next_state == pi[final_state]` (the classification). -/
def b2FinalPin : VmConstraint2 := .base (.piBinding VmRow.last NEXT PI_FINAL)

/-- B3: last row `running_hash == pi[route_commitment]` (the binding). -/
def b3RoutePin : VmConstraint2 := .base (.piBinding VmRow.last RUNNING_HASH PI_ROUTE)

/-- **`injectionRoutingDesc`** — the 3-state INJECTION DFA routing descriptor over the
`dregg-dfa-routing-v1` carrier: two child hashes (entry + running), five per-row Base gates (with
the degree-3 state grid + the injection transition interpolant), two transition `WindowGate`s
(continuity + copy-forward), and the five boundary pins (B1, is_first=1, seed acc, B2, B3). -/
def injectionRoutingDesc : EffectVmDescriptor2 :=
  { name        := "dfa-routing-injection-3state::poseidon2-v1"
  , traceWidth  := DFA_WIDTH
  , piCount     := DFA_PI_COUNT
  , tables      := []
  , constraints :=
      [ entryHashLookup, runningHashLookup
      , zeroLaneGate, isFirstBoolGate, stateGridGate, symbolGridGate, transitionGate
      , continuityWindow, copyForwardWindow
      , b1InitialPin, isFirstPinned, seedAccPin, b2FinalPin, b3RoutePin ]
  , hashSites   := []
  , ranges      := [] }

/-! ## §3 — The byte-pinned wire golden (the Rust decoder ingests THIS string). -/

#guard emitVmJson2 injectionRoutingDesc == "{\"name\":\"dfa-routing-injection-3state::poseidon2-v1\",\"ir\":2,\"trace_width\":22,\"public_input_count\":4,\"challenges\":0,\"tables\":[],\"constraints\":[{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":4},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":1},{\"t\":\"var\",\"v\":2},{\"t\":\"var\",\"v\":6},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":3},{\"t\":\"var\",\"v\":8},{\"t\":\"var\",\"v\":9},{\"t\":\"var\",\"v\":10},{\"t\":\"var\",\"v\":11},{\"t\":\"var\",\"v\":12},{\"t\":\"var\",\"v\":13},{\"t\":\"var\",\"v\":14}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":2},{\"t\":\"var\",\"v\":7},{\"t\":\"var\",\"v\":3},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":4},{\"t\":\"var\",\"v\":15},{\"t\":\"var\",\"v\":16},{\"t\":\"var\",\"v\":17},{\"t\":\"var\",\"v\":18},{\"t\":\"var\",\"v\":19},{\"t\":\"var\",\"v\":20},{\"t\":\"var\",\"v\":21}]},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":6}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-2}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":2}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":0}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"var\",\"v\":0}},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":1}}}}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":2}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":4}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":7,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":2,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":4,\"pi_index\":3}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §4 — Genuinely-proven, non-vacuous semantic lemmas (the load-bearing teeth). -/

/-- THE INJECTION ROUTE/TRANSITION TOOTH: the transition gate body is zero EXACTLY when
`2·next` equals the doubled injection interpolant of `(current, symbol)` — TRUE when the route
follows the injection table, FALSE otherwise. On the grid `{0,1,2}×{0,1}` (pinned by the vanishing
gates) and over an odd-characteristic field this is `next == step(current, symbol)`. -/
theorem transition_body_zero_iff (a : Assignment) :
    transitionBody.eval a = 0 ↔
      2 * a NEXT =
        2 * (a CURRENT * a CURRENT) - 2 * a CURRENT
          - 3 * (a CURRENT * a CURRENT * a SYMBOL) + 5 * (a CURRENT * a SYMBOL)
          + 2 * a SYMBOL := by
  simp only [transitionBody, EmittedExpr.eval]
  constructor <;> intro h <;> ring_nf <;> ring_nf at h <;> omega

/-- THE C2 CONTINUITY TOOTH: the continuity window body is zero EXACTLY when the next row's
`current` equals this row's `next` (the DFA state threads across the row window). -/
theorem continuity_window_zero_iff (env : VmRowEnv) :
    contWindowBody.eval env = 0 ↔ env.nxt CURRENT = env.loc NEXT := by
  simp only [contWindowBody_eq, WindowExpr.eval]
  constructor <;> intro h <;> omega

/-- THE C3 COPY-FORWARD TOOTH: the copy-forward window body is zero EXACTLY when the next row's
accumulator equals this row's running hash (`acc[i+1] = running[i]`). -/
theorem copyforward_window_zero_iff (env : VmRowEnv) :
    copyForwardBody.eval env = 0 ↔ env.nxt ACC = env.loc RUNNING_HASH := by
  simp only [copyForwardBody_eq, WindowExpr.eval]
  constructor <;> intro h <;> omega

-- Non-vacuity witnesses: the transition gate ACCEPTS genuine injection edges and REJECTS bad ones.
-- `step(0,1) = 1` (clean sees `{` → brace) accepted; claiming `step(0,1) = 0` rejected.
#guard decide (transitionBody.eval (fun i => if i = SYMBOL then 1 else if i = NEXT then 1 else 0) = 0)
#guard decide (¬ (transitionBody.eval (fun i => if i = SYMBOL then 1 else 0) = 0))
-- `step(1,1) = 2` (brace sees `{` → DEAD) accepted; claiming `step(1,1) = 0` rejected.
#guard decide (transitionBody.eval
  (fun i => if i = CURRENT then 1 else if i = SYMBOL then 1 else if i = NEXT then 2 else 0) = 0)
#guard decide (¬ (transitionBody.eval
  (fun i => if i = CURRENT then 1 else if i = SYMBOL then 1 else 0) = 0))
-- `step(2,1) = 2` (DEAD absorbs) accepted; `step(2,0) = 2` accepted.
#guard decide (transitionBody.eval
  (fun i => if i = CURRENT then 2 else if i = SYMBOL then 1 else if i = NEXT then 2 else 0) = 0)
#guard decide (transitionBody.eval
  (fun i => if i = CURRENT then 2 else if i = NEXT then 2 else 0) = 0)

-- Shape pins.
#guard injectionRoutingDesc.traceWidth == DFA_WIDTH
#guard injectionRoutingDesc.piCount == 4
#guard injectionRoutingDesc.constraints.length == 14
#guard (chipLookupTuple [.var CURRENT, .var SYMBOL, .var NEXT, .var ZERO_LANE] ENTRY_HASH ENTRY_LANES).length
         == CHIP_RATE + 1 + CHIP_OUT_LANES
#guard (chipLookupTuple [.var ACC, .var ENTRY_HASH] RUNNING_HASH RUNNING_LANES).length
         == CHIP_RATE + 1 + CHIP_OUT_LANES

#assert_axioms transition_body_zero_iff
#assert_axioms continuity_window_zero_iff
#assert_axioms copyforward_window_zero_iff

end Dregg2.Circuit.Emit.DfaRoutingGeneralEmit
