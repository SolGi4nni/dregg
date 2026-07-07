/-
# Dregg2.Circuit.Emit.DfaRoutingEmit — the emit-from-Lean descriptor for the DFA message-routing
family (`dregg-dfa-routing-v1`, `circuit/src/dsl/dfa_routing.rs`), minimal-but-real instance.

## What this file IS

A MINIMAL but REAL `EffectVmDescriptor2` that DECLARES, in the IR-v2 grammar, the statement
"a trace is the deterministic run of a routing DFA whose per-step `(state, symbol, next)` chain is
committed by a rolling Poseidon2 route commitment". It replaces the RUST-authored
`dfa_routing_descriptor` SEMANTICS with a descriptor emitted FROM Lean. Every constraint the hand
AIR enforces is mapped onto a `VmConstraint2` per the family dossier:

| hand-AIR constraint (`dfa_routing.rs`)                | IR-v2 carrier                                  |
|-------------------------------------------------------|------------------------------------------------|
| C1 entry hash `entry = hash_4_to_1(cur,sym,next,0)`   | arity-4 `Poseidon2Chip` lookup (`TID_P2`)      |
| `zero_lane == 0`                                       | `Base(Gate(var ZERO_LANE))`                    |
| `is_first` boolean                                    | `Base(Gate(x·(x−1)))`                          |
| state on grid `∏(cur − sᵢ) == 0`                      | `Base(Gate)` (vanishing poly)                  |
| symbol on grid `∏(sym − bⱼ) == 0`                     | `Base(Gate)` (vanishing poly)                  |
| GAP-A transition `next == step(cur, sym)`             | `Base(Gate)` (the bivariate interpolant)       |
| C2 continuity `next.cur == this.next`                 | `WindowGate(Nxt(cur) − Loc(next))` transition  |
| C3 running hash `next.run == hash_2_to_1(run, entry)` | arity-2 chip + `WindowGate` copy-forward + pin |
| seed `run₀ == hash_2_to_1(table_commit, entry₀)`      | first-row `PiBinding acc == pi[table_commit]`  |
| B1 first `cur == pi[initial_state]`                   | `Base(PiBinding first)`                        |
| `is_first` pinned to 1 on first row                   | `Base(Boundary first (is_first − 1))`          |
| B2 last `next == pi[final_state]`                     | `Base(PiBinding last)`                         |
| B3 last `run == pi[route_commitment]`                 | `Base(PiBinding last)`                         |

The C3 cross-row running hash is lowered EXACTLY as the Rust adapter does
(`circuit-prove/src/custom_leaf_adapter.rs`, "Running-hash chains"): a fresh COPY-FORWARD
accumulator column `acc` (`acc[i+1] = run[i]` via a transition `WindowGate`, `acc[0] = pi[seed]`
via a first-row `PiBinding`) makes the per-row hash single-row again — `run[i] =
hash_2_to_1(acc[i], entry[i])` is one arity-2 `TID_P2` chip lookup. Together these reproduce BOTH
the `ChainedHash2to1` rolling step AND its `SeedHash2to1` table-commitment seed.

## The minimal DFA (the concrete instance)

Two states `{0,1}`, two symbols `{0,1}`, the TOGGLE transition `step(s,y) = s XOR y`
(`step(0,0)=0, step(0,1)=1, step(1,0)=1, step(1,1)=0`). Its unique bivariate interpolant over the
grid `{0,1}²` is `P(cur,sym) = cur + sym − 2·cur·sym` — this IS the polynomial the production
`TableFunction` Lagrange expansion computes (the interpolant is unique), written compactly. The
grid-vanishing gates `cur·(cur−1)`, `sym·(sym−1)` pin `cur, sym ∈ {0,1}` so the interpolant is
evaluated only at real grid points (off-grid escapes are impossible) — the exact grid-range tooth.

## The byte-pinned wire golden

`emitVmJson2 dfaRoutingDesc` is BYTE-PINNED below (`#guard`). The Rust equality gate
(`circuit-prove/tests/dfa_routing_emit_gate.rs`) DECODES this exact string via
`parse_vm_descriptor2`, asserts it EQUALS an independently hand-built descriptor, proves an honest
routing witness through `prove_vm_descriptor2` (ACCEPT), and mutates the claimed final state / route
commitment / table-commitment seed / a routed edge / a running hash to force real UNSAT.

## Axiom hygiene

Definitional descriptor + a byte-pinned `#guard` on its wire string + three genuinely-proven,
non-vacuous semantic lemmas (the transition/route tooth, the C2 continuity window, the C3
copy-forward window — each TRUE iff its relation holds, FALSE otherwise). `#assert_axioms` on each
is pure `omega`/`ring`. NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.DfaRoutingEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId WindowExpr WindowConstraint
   chipLookupTuple CHIP_RATE CHIP_OUT_LANES emitVmJson2)

set_option autoImplicit false

/-! ## §1 — The trace column layout (7 base columns + copy-forward acc + 2×7 chip lanes). -/

/-- `current_state` — the DFA state entering this step. -/
def CURRENT : Nat := 0
/-- `symbol` — the input category read at this step. -/
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
/-- The COPY-FORWARD accumulator: `acc[0] = pi[table_commitment]`, `acc[i+1] = running[i]`. The C3
running-hash chain's prior-accumulator carrier (`custom_leaf_adapter.rs` `ChainFill`). -/
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
binding out0 to `RUNNING_HASH` (the `hash_2_to_1(acc, entry)` shape). The cross-row seeding is
carried by the `acc` copy-forward (`runCopyForward`) + seed pin (`seedAccPin`). -/
def runningHashLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2,
    chipLookupTuple [.var ACC, .var ENTRY_HASH] RUNNING_HASH RUNNING_LANES⟩

/-- `zero_lane == 0` on every (transition-domain) row: the fixed padding lane of the entry hash. -/
def zeroLaneGate : VmConstraint2 := .base (.gate (.var ZERO_LANE))

/-- `is_first` is boolean: `is_first · (is_first − 1) == 0`. -/
def isFirstBoolGate : VmConstraint2 :=
  .base (.gate (.mul (.var IS_FIRST) (.add (.var IS_FIRST) (.const (-1)))))

/-- state on grid `{0,1}`: `current · (current − 1) == 0` (the `∏(cur − sᵢ)` vanishing poly). -/
def stateGridGate : VmConstraint2 :=
  .base (.gate (.mul (.var CURRENT) (.add (.var CURRENT) (.const (-1)))))

/-- symbol on grid `{0,1}`: `symbol · (symbol − 1) == 0` (the `∏(sym − bⱼ)` vanishing poly). -/
def symbolGridGate : VmConstraint2 :=
  .base (.gate (.mul (.var SYMBOL) (.add (.var SYMBOL) (.const (-1)))))

/-- The toggle transition interpolant `P(cur, sym) = cur + sym − 2·cur·sym` — the unique bivariate
interpolant of `step(s,y) = s XOR y` over the grid `{0,1}²`. -/
def toggleInterp : EmittedExpr :=
  .add (.add (.var CURRENT) (.var SYMBOL))
       (.mul (.const (-2)) (.mul (.var CURRENT) (.var SYMBOL)))

/-- GAP-A transition body: `next − P(cur, sym)` (must vanish → `next == step(cur, sym)` on grid). -/
def transitionBody : EmittedExpr := .add (.var NEXT) (.mul (.const (-1)) toggleInterp)

/-- The GAP-A transition Base gate (the route-follows-the-table tooth). -/
def transitionGate : VmConstraint2 := .base (.gate transitionBody)

/-- C2 continuity body: `Nxt(current) − Loc(next)` (next row's `current` == this row's `next`). -/
def contWindowBody : WindowExpr := .add (.nxt CURRENT) (.mul (.const (-1)) (.loc NEXT))

/-- The C2 continuity `WindowGate`, asserted on the transition (every row but the last). -/
def continuityWindow : VmConstraint2 := .windowGate ⟨contWindowBody, true⟩

/-- C3 copy-forward body: `Nxt(acc) − Loc(running)` (so `acc[i+1] = running[i]`, the prior
accumulator carried forward — the cross-row seed of the running hash). -/
def copyForwardBody : WindowExpr := .add (.nxt ACC) (.mul (.const (-1)) (.loc RUNNING_HASH))

/-- The C3 copy-forward `WindowGate`, asserted on the transition. -/
def copyForwardWindow : VmConstraint2 := .windowGate ⟨copyForwardBody, true⟩

/-- B1: first row `current_state == pi[initial_state]`. -/
def b1InitialPin : VmConstraint2 := .base (.piBinding VmRow.first CURRENT PI_INITIAL)

/-- `is_first` pinned to 1 on the first row (`is_first − 1 == 0`, forcing the seed to fire there). -/
def isFirstPinned : VmConstraint2 := .base (.boundary VmRow.first (.add (.var IS_FIRST) (.const (-1))))

/-- The C3/seed pin: first row `acc == pi[table_commitment]`, so `running₀ =
hash_2_to_1(table_commitment, entry₀)` (the `SeedHash2to1` seed, realized as the chain's first-row
accumulator pin). -/
def seedAccPin : VmConstraint2 := .base (.piBinding VmRow.first ACC PI_TABLE)

/-- B2: last row `next_state == pi[final_state]` (the classification). -/
def b2FinalPin : VmConstraint2 := .base (.piBinding VmRow.last NEXT PI_FINAL)

/-- B3: last row `running_hash == pi[route_commitment]` (the binding). -/
def b3RoutePin : VmConstraint2 := .base (.piBinding VmRow.last RUNNING_HASH PI_ROUTE)

/-- **`dfaRoutingDesc`** — the minimal-but-real DFA-routing descriptor: two child hashes (entry +
running), five per-row Base gates, two transition `WindowGate`s (continuity + copy-forward), and
the five boundary pins (B1, is_first=1, seed acc, B2, B3). The chip table (`TID_P2`) is IMPLICITLY
present (Presence-detected from the lookups), so `tables` is empty as the working descriptors leave
it. -/
def dfaRoutingDesc : EffectVmDescriptor2 :=
  { name        := "dfa-routing-toggle-2state::poseidon2-v1"
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

/-! ## §3 — The byte-pinned wire golden (the Rust decoder ingests THIS string).

THE EQUALITY-GATE ANCHOR: this exact string is embedded verbatim in
`circuit-prove/tests/dfa_routing_emit_gate.rs` (`GOLDEN_JSON`), decoded there via
`parse_vm_descriptor2`, and proven. A drift on either side breaks THIS `#guard` (Lean) or the Rust
`assert_eq!(decoded, hand_built)` — neither can silently diverge. -/

#guard emitVmJson2 dfaRoutingDesc ==
  "{\"name\":\"dfa-routing-toggle-2state::poseidon2-v1\",\"ir\":2,\"trace_width\":22,\"public_input_count\":4,\"tables\":[],\"constraints\":[{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":4},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":1},{\"t\":\"var\",\"v\":2},{\"t\":\"var\",\"v\":6},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":3},{\"t\":\"var\",\"v\":8},{\"t\":\"var\",\"v\":9},{\"t\":\"var\",\"v\":10},{\"t\":\"var\",\"v\":11},{\"t\":\"var\",\"v\":12},{\"t\":\"var\",\"v\":13},{\"t\":\"var\",\"v\":14}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":2},{\"t\":\"var\",\"v\":7},{\"t\":\"var\",\"v\":3},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":4},{\"t\":\"var\",\"v\":15},{\"t\":\"var\",\"v\":16},{\"t\":\"var\",\"v\":17},{\"t\":\"var\",\"v\":18},{\"t\":\"var\",\"v\":19},{\"t\":\"var\",\"v\":20},{\"t\":\"var\",\"v\":21}]},{\"t\":\"gate\",\"body\":{\"t\":\"var\",\"v\":6}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"var\",\"v\":1}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"var\",\"v\":1}}}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":2}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":4}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":7,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":2,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":4,\"pi_index\":3}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §4 — Genuinely-proven, non-vacuous semantic lemmas (the load-bearing teeth). -/

/-- THE ROUTE/TRANSITION TOOTH: the transition gate body is zero EXACTLY when `next` is the toggle
interpolant of `(current, symbol)` — TRUE when the route follows the table, FALSE otherwise. On the
grid `{0,1}²` (pinned by the vanishing gates) this is `next == step(current, symbol)`. -/
theorem transition_body_zero_iff (a : Assignment) :
    transitionBody.eval a = 0 ↔
      a NEXT = a CURRENT + a SYMBOL - 2 * (a CURRENT * a SYMBOL) := by
  simp only [transitionBody, toggleInterp, EmittedExpr.eval]
  constructor <;> intro h <;> ring_nf <;> ring_nf at h <;> omega

/-- THE C2 CONTINUITY TOOTH: the continuity window body is zero EXACTLY when the next row's
`current` equals this row's `next` (the DFA state threads across the row window). -/
theorem continuity_window_zero_iff (env : VmRowEnv) :
    contWindowBody.eval env = 0 ↔ env.nxt CURRENT = env.loc NEXT := by
  simp only [contWindowBody, WindowExpr.eval]
  constructor <;> intro h <;> omega

/-- THE C3 COPY-FORWARD TOOTH: the copy-forward window body is zero EXACTLY when the next row's
accumulator equals this row's running hash (`acc[i+1] = running[i]` — the prior accumulator carried
into the cross-row running-hash seeding). -/
theorem copyforward_window_zero_iff (env : VmRowEnv) :
    copyForwardBody.eval env = 0 ↔ env.nxt ACC = env.loc RUNNING_HASH := by
  simp only [copyForwardBody, WindowExpr.eval]
  constructor <;> intro h <;> omega

-- Non-vacuity witnesses: the transition gate ACCEPTS a genuine toggle edge and REJECTS a bad one.
-- `step(0,1) = 1` accepted; `step(0,1) = 0` (claiming a forbidden edge) rejected.
#guard decide (transitionBody.eval (fun i => if i = SYMBOL then 1 else if i = NEXT then 1 else 0) = 0)
#guard decide (¬ (transitionBody.eval (fun i => if i = SYMBOL then 1 else 0) = 0))

-- Shape pins.
#guard dfaRoutingDesc.traceWidth == DFA_WIDTH
#guard dfaRoutingDesc.piCount == 4
#guard dfaRoutingDesc.constraints.length == 14
#guard (chipLookupTuple [.var CURRENT, .var SYMBOL, .var NEXT, .var ZERO_LANE] ENTRY_HASH ENTRY_LANES).length
         == CHIP_RATE + 1 + CHIP_OUT_LANES
#guard (chipLookupTuple [.var ACC, .var ENTRY_HASH] RUNNING_HASH RUNNING_LANES).length
         == CHIP_RATE + 1 + CHIP_OUT_LANES

#assert_axioms transition_body_zero_iff
#assert_axioms continuity_window_zero_iff
#assert_axioms copyforward_window_zero_iff

end Dregg2.Circuit.Emit.DfaRoutingEmit
