/-

⚠ TWO NAMED RESIDUALS IN THE 2026-07-26 COST-MODEL FIX (found by the fix's own adversarial verify,
recorded here rather than patched at the end of a sprint — both are bounded and safe to pick up):

(R1) `area` CAN STILL PRODUCE THE "FREE" READING THE `Option` WAS ADDED TO PREVENT. §1a justifies
`DescCost.area : Option Nat` on the grounds that "a sentinel 0 area reads as free" — but a table with
`sem := .exactPublicRows []` (ZERO declared rows) together with one LIVE lookup still yields
`declaredRows = 0`, `lookupCount = 1`, hence `pinned (0 / 1) = pinned 0` and `area = some 0`. That is
the same misleading "free" reading, now wearing a `some`. The likely correct semantics: a live lookup
against a table declaring no rows forces a ZERO-row trace, and traces are nonempty, so this shape is
`contradictory`, not `pinned 0`. NOT changed here because it is a semantics decision that wants the
§5 length law re-read alongside it, not a one-line guess. `costOf_forced_sound` is unaffected — it
quantifies over descriptors that HAVE a `Satisfied2Public` witness, and this shape has none.

(R2) `DfaRoutingSubsetTableCost.lean` WAS NOT COVERED BY THE CENSUS. It sits in this directory, is
registered as "the subset-table cost companion", and publishes cost claims about the DEPLOYED
`dregg-dfa-routing-table::exact-public-v1` carrier ("+1.76 KiB of wire and +0.15 ms of single-thread
prover CPU per declared row"). The census enumerated `costOf`/`forcedTraceRows`/`area` consumers and
did not reach it. Its numbers may be fine — the deployed carrier is single-lookup-per-table, which is
exactly the regime where the OLD model was already correct — but that has not been CHECKED, so treat
its published figures as un-re-verified until someone does.

⚠⚠⚠ READ FIRST — AN ADVERSARIAL VERIFY DISMANTLED THIS FILE'S HEADLINE. The cost numbers below are
REAL (independently re-derived from the emitted JSON by a separate parser), but for most of the grid
they measure DESCRIPTORS NO PROVER CAN EVER SATISFY. Do not cite §4's crossover.

* **THE LANES ROUTE IS VACUOUS AT k ≥ 2.** `lanesK k` has ZERO satisfying traces for k = 2, 4, 8 —
  derived from THIS FILE'S OWN §5: each lane's `forced_trace_length` pins `t.rows.length = 4`, and
  `exact_lookup_perm` forces lane i's triples to be a PERMUTATION of its own 4-row table, so every
  lane's run must be an EULERIAN path over its 4 edges while all lanes read the ONE SHARED symbol
  column. `parityDfa`'s Eulerian words are {0101,1010,…}; `lastDfa`'s are {0110,1100,0011,1001}; the
  sets are DISJOINT. Exhaustive search over all 2^4 words × all 2^k start assignments: 0 solutions.
  So "lanes win at every k ≥ 2, AREA crossover k = 2" is measuring an unsatisfiable object.
* **THE PRODUCT ROUTE IS EMPTY FOR k ≥ 3** under the whole-graph discipline: at k=3 the declared
  16-row transition multigraph is DISCONNECTED; at k = 4…8 every vertex is degree-imbalanced. On the
  headline grid {1,2,4,8} ONLY (product, k=1) and (product, k=2) admit any satisfying trace at all.
  §4b's "satisfiable only by EULERIAN words" caution is correct but was never applied to the measured
  families.
* **THE "EXPONENTIAL" IS AN ARTIFACT OF A DEGENERATE FAMILY.** `fam k` alternates only TWO machines,
  so the k-fold product's REACHABLE space is 4 states / 8 edges for every k ≥ 2 while `tableOf`
  tabulates all 2^k. At k=8, 504 of 512 declared rows are UNREACHABLE dead states. A
  reachability-minimised product table is FLAT at 8 rows / area 24 for all k — which REVERSES the
  headline. The exponential is real for genuinely independent machines; it is NOT what this family
  measured.
* **THE §7 EXHIBIT RUNS NO CIRCUIT.** `pairDesc` declares 8 rows so §5 pins its trace to 8, while the
  exhibited words have length 7 — no satisfying trace reads them. The accept/reject poles are genuine
  Props about the ABSTRACT `pairDfa`, and the `#guard`s are `classifyFrom` evaluations: an AUTOMATON
  run, not a CIRCUIT run. NO `VmTrace`/`Satisfied2Public` witness is constructed for ANY composed
  descriptor in this file. (Repairable — the verify found 16 genuine 8-symbol Eulerian words for
  `pairDesc`.)

WHAT SURVIVES, and it is the useful part:
* `nonlinearMults = 0` at every k for BOTH table routes vs 4 per machine gate-baked — the per-automaton
  transition interpolant genuinely ceases to exist. That is a real, satisfiable-independent fact about
  the SHAPE.
* `lookupLog_length` / `forced_trace_length` / `tableRouting_forced_length` — the LAW that a declared
  `exactPublicRows` table is a unit-capacity LogUp receive and therefore PINS THE TRACE LENGTH. This is
  what makes "a table is free data" false, and it is exactly what makes the vacuity above derivable.
* `classify_prodList` and `productDesc_refines_components` / `productDesc_binary_components` — genuine
  non-tautological theorems over the emitted object (verified by reading the proof terms): the
  composed descriptor's classification IS the mixed-radix packing of the components', and composed
  acceptance ⟹ every component accepts. These are SOUNDNESS results and are unaffected by the vacuity;
  but note NON-VACUITY IS NOT EXHIBITED for any composed descriptor — the only firing witness in the
  file is `DfaRoutingTableEmit`'s single non-composed demo.

THE HONEST NEXT EXPERIMENT: measure over (a) genuinely INDEPENDENT tiny automata (not a 2-machine
alternation), (b) reachability-MINIMISED product tables, and (c) the RUN-table discipline (§4b) where
the Eulerian constraint is discharged by construction — and exhibit a real `Satisfied2Public` witness
for at least one composed descriptor before quoting any crossover.
# Dregg2.Circuit.Emit.TinyAutomataCompose — THE COMPOSITION COST LAW for table-driven tiny automata.

**This is Lean-authored AIR.** Both composed descriptor families below are authored here as
`EffectVmDescriptor2` values; the cost numbers are read off the EMITTED objects (not estimated);
the soundness theorem is a `Satisfied2Public <emitted descriptor> ⟹ per-component classification`
statement over the emitted object, reusing `DfaRoutingTableEmit.tableRouting_refines_classify`.
Rust parses the emitted IR2 bytes and supplies witnesses; it authors nothing.

## The question

`dfa-routing.json` (transition baked into GATES, `DfaRoutingEmit.lean`) is traceWidth 8 /
14 constraints for ONE 2-state automaton. `dfa-routing-table-exact-public-v1.json`
(transition table as INPUT, `DfaRoutingTableEmit.lean`) is traceWidth 3 / 4 constraints. The
thesis that gap suggests: a table-driven automaton is nearly free per machine, so `k` tiny
automata should cost ~`k` lookups over ONE shared row skeleton rather than `k` circuits.

This file COMPOSES tiny automata by the two available routes and measures both:

  * **PRODUCT-FIRST** (`productDesc`) — fold the `k` automata into ONE product DFA (state = the
    mixed-radix tuple), tabulate its whole transition graph, emit ONE `tableRoutingDesc`. The
    CIRCUIT is `k`-independent: 3 columns, 4 constraints, 2 PIs, forever. The TABLE grows as
    `∏|Qᵢ| · |Σ|`.

  * **PARALLEL-LANES** (`lanesDesc`) — `k` table-routing lanes over ONE shared symbol column:
    `1 + 2k` columns, `4k` constraints, `2k` PIs, `k` tables of `|Qᵢ| · |Σ|` rows each.

## What the measurement actually shows (the thesis is HALF right, and the correction is the point)

**The skeleton.** Both table routes emit ZERO nonlinear multiplications at every `k` — the
per-machine transition interpolant that costs the gate-baked baseline 4 of them simply does not
exist. Counting COLUMNS and CONSTRAINTS, product-first is flat (3 / 4 / 2 PIs, every `k`) and
lanes are linear (`1+2k` / `4k` / `2k`). On that axis alone product-first wins everywhere.

**Why that axis alone is WRONG.** `exactPublicRows` is a UNIT-CAPACITY LogUp receive:
`PublicLookupBalanced` forces the main-lookup multiset to be a PERMUTATION of the declared rows, so

    (number of main trace rows) × (lookups on that table) = (declared row count)

— proved here as `forced_trace_length` (general), `tableRouting_forced_length` (the family), and
fired on the deployed witness (`forced_length_fires`). A declared table is NOT free data: it PINS
THE TRACE LENGTH. Circuit AREA (`traceWidth × trace rows`) is the honest cost, and it is where the
`∏` vs `Σ` of the two routes actually lands.

**The law, measured (§4, §4b).** It depends on the TABLE DISCIPLINE, and that — not "product vs
lanes" — is the real fork:

  * WHOLE-GRAPH tables (the descriptor commits the automaton): product area `3·2^(k+1)`, lanes
    area `(1+2k)·4`. TIE at `k = 1` (12 = 12); lanes win at every `k ≥ 2`; **AREA crossover k = 2**,
    with the product exponentially worse after. In wire bytes the product stays smaller until
    **k = 8** (6264 vs 3892) — the two crossovers are six `k` apart.
  * RUN tables (the descriptor commits the run's edges, `|w|` rows — §4b): product area is FLAT in
    `k` (3 × 8 = 24 for an 8-symbol word, at `k` = 1, 2, 4, 8), lanes `(1+2k)·|w|`. **The law
    flips: product-first wins from `k = 2` on**, and its wire bytes barely move (648 → 674 from
    `k=1` to `k=8`).

**So the cheapest primitive is: ONE product-DFA table-routing descriptor over a RUN table** — 3
columns, 4 constraints, 2 PIs, 0 nonlinear mults, `|w|` rows, all `k`-independent. What it costs is
ATTESTATION: a run table does not commit the whole automaton, only the edges used, so "which
automaton ran" must be bound elsewhere. Whole-graph tables buy that binding at an exponential
price — and, worse, unit capacity + the continuity window make them satisfiable only by EULERIAN
words (§4b's warning).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. NEW file; imports
read-only. Every `#guard` is COMPILED EVALUATION of a closed `Bool` — it proves NO `Prop`; it pins
the measured numbers and the emitted bytes, nothing more. The load-bearing facts are the theorems.
-/
import Dregg2.Circuit.Emit.DfaRoutingTableEmit
import Dregg2.Circuit.Emit.DfaRoutingEmit

namespace Dregg2.Circuit.Emit.TinyAutomataCompose

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Crypto.DfaAcceptanceAir (TableDfa classifyFrom)
open Dregg2.Circuit.Emit.DfaRoutingTableEmit
  (CURRENT SYMBOL NEXT TRT_TID TRT_WIDTH TRT_PI_COUNT PI_INITIAL PI_FINAL
   tableRoutingDesc transitionTableDef transitionLookup tableRouting_refines_classify)

set_option autoImplicit false

/-! ## §1 — The cost metric, read off the EMITTED descriptor.

Four numbers per descriptor, all syntactic functions of the emitted object:
`traceWidth`, `piCount`, constraint count, declared-row count, and the NONLINEAR MULTIPLICATION
count — `mul` nodes whose two operands are both non-constant (a `const · x` node is a linear
scaling and costs no degree). Nonlinear-mult count is the degree proxy that separates a
gate-baked automaton (a bivariate interpolant per machine) from a table-driven one (zero). The
mem/map/umem/proofBind constraint legs are counted as 0 multiplications: no descriptor in this
file emits one, so that arm is never exercised (it is not a claim about those legs). -/

/-- Is this emitted expression a bare field constant? -/
def eIsConst : EmittedExpr → Bool
  | .const _ => true
  | _        => false

/-- NONLINEAR multiplications in a row-local expression: `mul` nodes with both operands
non-constant. -/
def eMults : EmittedExpr → Nat
  | .var _   => 0
  | .const _ => 0
  | .add a b => eMults a + eMults b
  | .mul a b => (if eIsConst a || eIsConst b then 0 else 1) + eMults a + eMults b

/-- Is this window expression a bare field constant? -/
def wIsConst : WindowExpr → Bool
  | .const _ => true
  | _        => false

/-- NONLINEAR multiplications in a two-row window expression. -/
def wMults : WindowExpr → Nat
  | .loc _   => 0
  | .nxt _   => 0
  | .const _ => 0
  | .add a b => wMults a + wMults b
  | .mul a b => (if wIsConst a || wIsConst b then 0 else 1) + wMults a + wMults b

/-- Nonlinear multiplications in a v1 base constraint. -/
def baseMults : VmConstraint → Nat
  | .gate b        => eMults b
  | .transition _ _ => 0
  | .boundary _ b  => eMults b
  | .piBinding _ _ _ => 0

/-- Nonlinear multiplications in a v2 constraint. -/
def c2Mults : VmConstraint2 → Nat
  | .base c       => baseMults c
  | .lookup l     => (l.tuple.map eMults).sum
  | .memOp _      => 0
  | .mapOp _      => 0
  | .umemOp _     => 0
  | .proofBind _  => 0
  | .windowGate w => wMults w.body

/-- Rows a table DECLARES (exact-public manifests only; other semantics declare no rows here). -/
def tdRows (td : TableDef) : Nat :=
  match td.sem with
  | .exactPublicRows rows => rows.length
  | _ => 0

/-! ### §1a — the LOOKUP MULTIPLICITY, which is what the length law divides by.

`forced_trace_length` (§5) reads `(trace rows) × (lookups targeting the table) = (declared rows)`.
The divisor is therefore part of the cost model, not an afterthought: these two selectors are
defined HERE, ahead of `costOf`, precisely so the record cannot be computed without it. -/

/-- The lookup selector: does this constraint target `table`, and with which lookup? -/
def lkOf (table : TableId) : VmConstraint2 → Option Lookup
  | .lookup l => if l.table = table then some l else none
  | _         => none

/-- How many lookup constraints of `d` target `table`. -/
def lookupCount (d : EffectVmDescriptor2) (table : TableId) : Nat :=
  (d.constraints.filterMap (lkOf table)).length

/-- **What the declared tables pin the main trace length to.** THREE-VALUED ON PURPOSE.

A bare `Nat` field cannot tell "nothing is pinned" from "pinned to zero" from "the declarations
CONTRADICT one another", and the shape this replaces did worse than conflate them: it reported the
declared ROW COUNT, which is the forced trace length only when `lookupCount = 1`. A descriptor with
`s` lookups on one table (e.g. `TinyAutomataPacked.packedDesc`) was mis-measured by a factor of `s`
while still type-checking, because every inhabitant of `Nat` is a plausible-looking answer. The
three constructors are the three things §5's law can actually say. -/
inductive ForcedRows where
  /-- No `exactPublicRows` table constrains the length: `forced_trace_length` says nothing. -/
  | unpinned
  /-- Every declaring table forces EXACTLY this many main trace rows. -/
  | pinned (n : Nat)
  /-- The declarations cannot be met at once (a non-dividing count, or two tables disagreeing):
  NO trace satisfies this descriptor, so it has no cost — it has no runs. -/
  | contradictory
  deriving Repr, DecidableEq

/-- Combine two tables' verdicts. `unpinned` is the unit; two `pinned` values must AGREE, since a
trace has one length; `contradictory` absorbs. -/
def ForcedRows.meet : ForcedRows → ForcedRows → ForcedRows
  | .contradictory, _ => .contradictory
  | _, .contradictory => .contradictory
  | .unpinned, y      => y
  | x, .unpinned      => x
  | .pinned a, .pinned b => if a = b then .pinned a else .contradictory

/-- **The length ONE declared table pins**, straight from `forced_trace_length`'s equation
`rows × lookupCount = declaredRows`, solved for `rows`:

  * no lookup targets it — the equation reads `0 = declaredRows`, so an EMPTY manifest is no
    constraint and a non-empty one is unsatisfiable;
  * `lookupCount = c > 0` — the length is `declaredRows / c`, and if `c ∤ declaredRows` there is
    no natural solution at all.

`tdForced_sound` (§5) proves this function never lies about a descriptor that has a witness. -/
def tdForced (d : EffectVmDescriptor2) (td : TableDef) : ForcedRows :=
  match td.sem with
  | .exactPublicRows rows =>
      let c := lookupCount d td.id
      if c = 0 then (if rows.isEmpty then .unpinned else .contradictory)
      else if rows.length % c = 0 then .pinned (rows.length / c)
      else .contradictory
  | _ => .unpinned

/-- The measured cost record of an emitted descriptor. `forcedTraceRows` is the trace length the
unit-capacity exact-public receives PIN — the `meet` of every declared table's own verdict, each
computed as `declaredRows / lookupCount` (§5's `forced_trace_length`, `tdForced_sound`). -/
structure DescCost where
  traceWidth      : Nat
  piCount         : Nat
  constraints     : Nat
  tables          : Nat
  declaredRows    : Nat
  forcedTraceRows : ForcedRows
  nonlinearMults  : Nat
  deriving Repr, DecidableEq

/-- Read the cost record off an emitted descriptor. -/
def costOf (d : EffectVmDescriptor2) : DescCost :=
  { traceWidth      := d.traceWidth
  , piCount         := d.piCount
  , constraints     := d.constraints.length
  , tables          := d.tables.length
  , declaredRows    := (d.tables.map tdRows).sum
  , forcedTraceRows := (d.tables.map (tdForced d)).foldl ForcedRows.meet .unpinned
  , nonlinearMults  := (d.constraints.map c2Mults).sum }

/-- CIRCUIT AREA — the honest cost: columns × the trace length the declaration pins. `none` when
there is no such number: either nothing pins a length (multiply by what?) or the declarations
contradict each other (the object has no runs to price). An `Option` here rather than a `0`, for
the same reason `ForcedRows` is not a `Nat` — a sentinel `0` area reads as "free". -/
def DescCost.area (c : DescCost) : Option Nat :=
  match c.forcedTraceRows with
  | .pinned n => some (c.traceWidth * n)
  | _         => none

/-- Emitted wire size in bytes (the descriptor the verifier must hold). -/
def jsonBytes (d : EffectVmDescriptor2) : Nat := (emitVmJson2 d).length

/-! ## §2 — Tiny automata, their transition tables, and the two composition routes. -/

/-- Alphabet size of the tiny automata used throughout: `Σ = {0, 1}`. -/
def NSYM : Nat := 2
/-- State-space size of each tiny automaton: `Q = {0, 1}`. The composition radix. -/
def RADIX : Nat := 2

/-- "EVEN number of 1s" — the parity automaton. `step s y = (s + y) % 2`, accept in state 0. -/
def parityDfa : TableDfa Nat Nat :=
  { step := fun s y => (s + y) % 2, start := 0, accepts := fun s => s = 0 }

/-- "ENDS IN 1" — the last-symbol automaton. `step s y = y % 2`, accept in state 1. (`% 2` keeps
the transition function TOTAL and bounded on all of `ℕ`, which the composition bounds need; on the
tabulated grid `y ∈ {0,1}` it is the identity.) -/
def lastDfa : TableDfa Nat Nat :=
  { step := fun _ y => y % 2, start := 0, accepts := fun s => s = 1 }

/-- The `k`-automaton family: alternating parity / last-symbol machines. -/
def fam (k : Nat) : List (TableDfa Nat Nat) :=
  (List.range k).map (fun i => if i % 2 = 0 then parityDfa else lastDfa)

/-- The COMPLETE transition table of a DFA over `nStates × nSyms`: one row `[s, y, step s y]` per
grid point. This is the table the descriptor DECLARES. -/
def tableOf (d : TableDfa Nat Nat) (nStates nSyms : Nat) : List (List Nat) :=
  (List.range nStates).flatMap (fun s => (List.range nSyms).map (fun y => [s, y, d.step s y]))

/-! ### Route (a) — PRODUCT-FIRST. -/

/-- The BINARY product DFA over `ℕ`-encoded states: the left machine's state rides the high digit
(radix `m` = the right machine's state-space size), the right machine's the low digit. This is the
`prodVpa` intersection construction at the DFA level: both components step on the SAME symbol,
and `accepts` is the conjunction. -/
def prod2 (d e : TableDfa Nat Nat) (m : Nat) : TableDfa Nat Nat :=
  { step    := fun s y => d.step (s / m) y * m + e.step (s % m) y
  , start   := d.start * m + e.start
  , accepts := fun s => d.accepts (s / m) ∧ e.accepts (s % m) }

/-- The one-state trivial DFA (the fold's unit): a single state `0`, always accepting. -/
def unitDfa : TableDfa Nat Nat :=
  { step := fun _ _ => 0, start := 0, accepts := fun _ => True }

/-- The `k`-FOLD product DFA over a state radix `r`: right-fold of `prod2`, the tail's state space
being `r ^ tail.length`. Its state space is `r ^ ds.length`, encoded mixed-radix. -/
def prodListDfa (r : Nat) : List (TableDfa Nat Nat) → TableDfa Nat Nat
  | []      => unitDfa
  | d :: ds => prod2 d (prodListDfa r ds) (r ^ ds.length)

/-- Mixed-radix encoding of a component-state tuple (most significant first). -/
def encodeDigits (r : Nat) : List Nat → Nat
  | []      => 0
  | q :: qs => q * r ^ qs.length + encodeDigits r qs

/-- **Route (a) — the PRODUCT-FIRST descriptor**: ONE `tableRoutingDesc` over the whole product
transition table. 3 columns / 4 constraints / 2 PIs for every `k`; the table carries `r^k · |Σ|`
rows. -/
def productDesc (k : Nat) : EffectVmDescriptor2 :=
  tableRoutingDesc s!"tiny-automata-product-k{k}::exact-public-v1"
    (tableOf (prodListDfa RADIX (fam k)) (RADIX ^ k) NSYM)

/-! ### Route (b) — PARALLEL LANES. -/

/-- Lane `i`'s declared transition table id (`.custom (40 + i)`, wire `45 + i` — the `40 +` block
is unclaimed in the tree; `TRT_TID` is `.custom 30`). -/
def LANE_TID (i : Nat) : TableId := .custom (40 + i)

/-- The shared symbol column: ONE input word read by every lane. -/
def LANE_SYMBOL : Nat := 0
/-- Lane `i`'s `current_state` column. -/
def laneCurrent (i : Nat) : Nat := 1 + 2 * i
/-- Lane `i`'s `next_state` column. -/
def laneNext (i : Nat) : Nat := 2 + 2 * i

/-- Lane `i`'s declared transition table. -/
def laneTableDef (i : Nat) (tbl : List (List Nat)) : TableDef :=
  ⟨LANE_TID i, "dfa_transition_table_lane", 3, .exactPublicRows tbl⟩

/-- Lane `i`'s four constraints: its own table-generic transition lookup (over the SHARED symbol
column), its continuity window, and its two boundary pins. -/
def laneConstraints (i : Nat) : List VmConstraint2 :=
  [ .lookup ⟨LANE_TID i, [.var (laneCurrent i), .var LANE_SYMBOL, .var (laneNext i)]⟩
  , .windowGate ⟨.add (.nxt (laneCurrent i)) (.mul (.const (-1)) (.loc (laneNext i))), true⟩
  , .base (.piBinding VmRow.first (laneCurrent i) (2 * i))
  , .base (.piBinding VmRow.last (laneNext i) (2 * i + 1)) ]

/-- **Route (b) — the PARALLEL-LANES descriptor**: `k` table-routing lanes over ONE row skeleton
(one shared symbol column). `1 + 2k` columns / `4k` constraints / `2k` PIs / `k` tiny tables.

RESIDUAL (a direct corollary of §5's `forced_trace_length`, applied per lane): every lane's
declared table pins the SAME trace length, so a lanes descriptor is satisfiable only if all `k`
declared tables have EQUAL row counts. Uniform tiny automata (as here) satisfy that; a bank of
automata with different state-space sizes does not, and must be padded. -/
def lanesDesc (name : String) (tbls : List (List (List Nat))) : EffectVmDescriptor2 :=
  { name        := name
  , traceWidth  := 1 + 2 * tbls.length
  , piCount     := 2 * tbls.length
  , tables      := (List.range tbls.length).map (fun i => laneTableDef i (tbls.getD i []))
  , constraints := (List.range tbls.length).flatMap laneConstraints
  , hashSites   := []
  , ranges      := [] }

/-- The `k`-lane instance over the tiny-automaton family. -/
def lanesK (k : Nat) : EffectVmDescriptor2 :=
  lanesDesc s!"tiny-automata-lanes-k{k}::exact-public-v1"
    ((fam k).map (fun d => tableOf d RADIX NSYM))

/-! ## §3 — Sanity: the two families reproduce the KNOWN datum at `k = 1`.

Both routes at `k = 1` must be the plain table-routing descriptor shape (3 / 4 / 2), and the
gate-baked baseline must still measure 8 / 14. COMPILED EVALUATION (`#guard` proves no `Prop`). -/

-- The gate-baked baseline, MEASURED (the key datum: traceWidth 8, 14 constraints) — and its
-- nonlinear-mult count, which the table route drives to zero.
#guard costOf DfaRoutingEmit.dfaRoutingDesc ==
  { traceWidth := 8, piCount := 4, constraints := 14, tables := 0
  , declaredRows := 0, forcedTraceRows := .unpinned, nonlinearMults := 4 }

#guard costOf (productDesc 1) ==
  { traceWidth := 3, piCount := 2, constraints := 4, tables := 1
  , declaredRows := 4, forcedTraceRows := .pinned 4, nonlinearMults := 0 }

#guard costOf (lanesK 1) ==
  { traceWidth := 3, piCount := 2, constraints := 4, tables := 1
  , declaredRows := 4, forcedTraceRows := .pinned 4, nonlinearMults := 0 }

/-! ## §4 — ⚑ THE MEASUREMENT: `k = 1, 2, 4, 8` by both routes.

Every number below is READ OFF the emitted descriptor by `costOf` / `jsonBytes`, pinned by
compiled evaluation (`#guard` — NO `Prop` is proved by these lines; §5 carries the theorems). -/

-- PRODUCT-FIRST costs at `k = 1, 2, 4, 8`: the CIRCUIT is flat (3 columns / 4 constraints / 2 PIs
-- for every k); the declared table — and so the PINNED trace length — doubles with every added
-- automaton: 2^(k+1) rows.
#guard (List.map (fun k => costOf (productDesc k)) [1, 2, 4, 8]) ==
  [ { traceWidth := 3, piCount := 2, constraints := 4, tables := 1
    , declaredRows := 4,   forcedTraceRows := .pinned 4,   nonlinearMults := 0 }
  , { traceWidth := 3, piCount := 2, constraints := 4, tables := 1
    , declaredRows := 8,   forcedTraceRows := .pinned 8,   nonlinearMults := 0 }
  , { traceWidth := 3, piCount := 2, constraints := 4, tables := 1
    , declaredRows := 32,  forcedTraceRows := .pinned 32,  nonlinearMults := 0 }
  , { traceWidth := 3, piCount := 2, constraints := 4, tables := 1
    , declaredRows := 512, forcedTraceRows := .pinned 512, nonlinearMults := 0 } ]

-- PARALLEL-LANES costs at `k = 1, 2, 4, 8`: columns `1 + 2k`, constraints `4k`, PIs `2k`, but each
-- lane's table stays 4 rows — so the PINNED trace length is 4 at EVERY k.
#guard (List.map (fun k => costOf (lanesK k)) [1, 2, 4, 8]) ==
  [ { traceWidth := 3,  piCount := 2,  constraints := 4,  tables := 1
    , declaredRows := 4,  forcedTraceRows := .pinned 4, nonlinearMults := 0 }
  , { traceWidth := 5,  piCount := 4,  constraints := 8,  tables := 2
    , declaredRows := 8,  forcedTraceRows := .pinned 4, nonlinearMults := 0 }
  , { traceWidth := 9,  piCount := 8,  constraints := 16, tables := 4
    , declaredRows := 16, forcedTraceRows := .pinned 4, nonlinearMults := 0 }
  , { traceWidth := 17, piCount := 16, constraints := 32, tables := 8
    , declaredRows := 32, forcedTraceRows := .pinned 4, nonlinearMults := 0 } ]

-- ⚑ THE CROSSOVER, in AREA (columns × the trace length the exact-public receive PINS):
-- product `3·2^(k+1)` vs lanes `(1+2k)·4`. They TIE at `k = 1` (12 = 12) and lanes win at every
-- `k ≥ 2` — the crossover is k = 2, and the product route is exponentially worse from there.
#guard (List.map (fun k => ((costOf (productDesc k)).area, (costOf (lanesK k)).area))
    [1, 2, 3, 4, 8])
  == [(some 12, some 12), (some 24, some 20), (some 48, some 28), (some 96, some 36),
      (some 1536, some 68)]

-- The SECOND crossover, in EMITTED DESCRIPTOR BYTES (the verifier-held object): the product
-- route's table IS its descriptor, so bytes grow with `∏|Qᵢ|`; the lanes' bytes grow linearly.
-- Here the product route is SMALLER up to k = 7 and loses at k = 8 (6264 vs 3892) — the byte
-- crossover is k = 8, six k later than the AREA crossover at k = 2.
#guard (List.map (fun k => (jsonBytes (productDesc k), jsonBytes (lanesK k)))
    [1, 2, 3, 4, 5, 6, 7, 8])
  == [(612, 615), (644, 1079), (708, 1543), (860, 2007), (1184, 2476), (1816, 2948),
      (3208, 3420), (6264, 3892)]

-- And the gate-baked route for reference: ONE 2-state automaton already costs 8 columns / 14
-- constraints / 4 nonlinear mults / 2188 wire bytes, with NO table at all. A `k`-fold gate-baked
-- lane bank is `k` copies of that gate block: the per-machine gate cost NEVER amortizes, which is
-- exactly what the table route removes (both table routes measure 0 nonlinear mults at every k).
#guard jsonBytes DfaRoutingEmit.dfaRoutingDesc == 2188

/-! ## §4b — THE SECOND DISCIPLINE, and the law FLIPS.

§5 proves the declared table pins the trace length. Turn that around: a descriptor may declare the
transitions THE RUN USES (with multiplicity) instead of the automaton's WHOLE graph. Then the
declared row count is `|w|` for BOTH routes, independent of `k`, and the product route's flat
3-column skeleton wins outright — its table stops growing as `∏|Qᵢ|` because it never tabulates
unvisited product states.

What is paid for it is ATTESTATION, not soundness: `tableRouting_refines_classify` still gives
`fN = classifyFrom d q₀ ws` for ANY `d` whose step graph extends the declared rows, so the
classification remains genuine — but the descriptor no longer COMMITS the whole automaton, only
the run's edges. Which automaton was run must then be bound elsewhere (a table commitment / a
whole-graph attestation). That is the real trade this measurement exposes; the choice is not
"product vs lanes" but "commit the automaton or commit the run".

⚠ There is a second, sharper consequence of unit capacity, and it is what makes the whole-graph
discipline nearly unusable rather than merely expensive: a satisfying trace must consume the
declared multiset EXACTLY *and* chain (the continuity window), so a WHOLE-GRAPH table is
satisfiable only by a word whose run is an EULERIAN PATH through the declared transition
multigraph. `DfaRoutingTableEmit`'s deployed demo (one declared row, one trace row) is trivially
Eulerian and hides this. The run-table discipline has no such obstruction — its declared multiset
IS the run. -/

/-- The transitions a run USES, in order, with multiplicity: `|w|` rows, whatever `|Q|` is. -/
def runTable (d : TableDfa Nat Nat) (q : Nat) : List Nat → List (List Nat)
  | []      => []
  | y :: ys => [q, y, d.step q y] :: runTable d (d.step q y) ys

/-- **Every run-table row is a genuine step-graph entry** — the `htbl` hypothesis of §6, discharged
for the run discipline (so the refinement applies unchanged). -/
theorem runTable_graph (d : TableDfa Nat Nat) :
    ∀ (w : List Nat) (q : Nat), ∀ row ∈ runTable d q w, ∃ s y, row = [s, y, d.step s y]
  | [], _, _, h => absurd h (List.not_mem_nil)
  | y :: ys, q, row, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨q, y, rfl⟩
    · exact runTable_graph d ys (d.step q y) row h

/-- The run table has exactly one row per input symbol. -/
theorem runTable_length (d : TableDfa Nat Nat) :
    ∀ (w : List Nat) (q : Nat), (runTable d q w).length = w.length
  | [], _ => rfl
  | y :: ys, q => by
    show (runTable d (d.step q y) ys).length + 1 = ys.length + 1
    rw [runTable_length d ys (d.step q y)]

/-- An 8-symbol probe word (the run length the §4b measurement holds fixed). -/
def probeWord : List Nat := [1, 0, 1, 1, 0, 0, 1, 1]

/-- PRODUCT-FIRST with a RUN table. -/
def productRunDesc (k : Nat) : EffectVmDescriptor2 :=
  tableRoutingDesc s!"tiny-automata-product-run-k{k}::exact-public-v1"
    (runTable (prodListDfa RADIX (fam k)) 0 probeWord)

/-- PARALLEL-LANES with RUN tables. -/
def lanesRunK (k : Nat) : EffectVmDescriptor2 :=
  lanesDesc s!"tiny-automata-lanes-run-k{k}::exact-public-v1"
    ((fam k).map (fun d => runTable d 0 probeWord))

-- ⚑ THE LAW FLIPS. Run tables at `k = 1, 2, 4, 8` over an 8-symbol word: the product route is
-- FLAT in `k` on every axis — 3 columns, 4 constraints, 8 declared rows, 8 forced trace rows,
-- AREA 24 — while the lanes pay `(1+2k) × 8`. Product wins from `k = 2` on (the tie is `k = 1`).
#guard (List.map (fun k => ((costOf (productRunDesc k)).declaredRows,
    (costOf (productRunDesc k)).area, (costOf (lanesRunK k)).area)) [1, 2, 4, 8])
  == [(8, some 24, some 24), (8, some 24, some 40), (8, some 24, some 72),
      (8, some 24, some 136)]

-- Same flip in wire bytes: the product's run descriptor barely moves with `k`; the lanes' grows.
#guard (List.map (fun k => (jsonBytes (productRunDesc k), jsonBytes (lanesRunK k))) [1, 2, 4, 8])
  == [(648, 651), (648, 1147), (659, 2139), (674, 4152)]

/-! ## §5 — THE AREA LAW IS A THEOREM: the declared table PINS the trace length.

`exactPublicRows` is a UNIT-CAPACITY LogUp receive: `PublicLookupBalanced` demands the main-lookup
log be a PERMUTATION of the declared rows. Lengths therefore agree, and the log's length is
`(trace rows) × (lookups on that table)`. So a declared table is NOT free data — it pins the trace
length, which is why `∏|Qᵢ|` lands in the AREA. (This restricts witness EXISTENCE, exactly as
`DfaRoutingTableEmit`'s residual note says — it is not a soundness claim.) -/

-- (`lkOf` and `lookupCount` are defined in §1a — the cost model needs the divisor.)

/-- The same selector, carrying the EVALUATED tuple (this is exactly `lookupLog`'s inner
`filterMap`, named so it can be rewritten). -/
def tupOf (table : TableId) (row : Assignment) : VmConstraint2 → Option (List ℤ)
  | .lookup l => if l.table = table then some (l.tuple.map (·.eval row)) else none
  | _         => none

/-- Two `filterMap`s that KEEP the same elements produce the same length. -/
theorem length_filterMap_congr {α β γ : Type} (f : α → Option β) (g : α → Option γ)
    (hfg : ∀ a, (f a).isSome = (g a).isSome) :
    ∀ l : List α, (l.filterMap f).length = (l.filterMap g).length
  | [] => rfl
  | a :: l => by
    have ih := length_filterMap_congr f g hfg l
    have h := hfg a
    cases hf : f a with
    | none =>
      cases hg : g a with
      | none => simp [hf, hg, ih]
      | some _ => rw [hf, hg] at h; simp at h
    | some _ =>
      cases hg : g a with
      | none => rw [hf, hg] at h; simp at h
      | some _ => simp [hf, hg, ih]

/-- The two selectors keep exactly the same constraints. -/
theorem tupOf_isSome (table : TableId) (row : Assignment) :
    ∀ c : VmConstraint2, (tupOf table row c).isSome = (lkOf table c).isSome := by
  intro c
  cases c with
  | lookup l => by_cases h : l.table = table <;> simp [tupOf, lkOf, h]
  | base _ => rfl
  | memOp _ => rfl
  | mapOp _ => rfl
  | umemOp _ => rfl
  | proofBind _ => rfl
  | windowGate _ => rfl

/-- The two selectors keep the same list length — the evaluated tuple carries no extra filtering. -/
theorem filterMap_tupOf_length (table : TableId) (row : Assignment) (cs : List VmConstraint2) :
    (cs.filterMap (tupOf table row)).length = (cs.filterMap (lkOf table)).length :=
  length_filterMap_congr _ _ (tupOf_isSome table row) cs

/-- The lookup log's length factors: one entry per (trace row × targeting lookup). -/
theorem lookupLog_length (d : EffectVmDescriptor2) (t : VmTrace) (table : TableId) :
    (lookupLog d t table).length = t.rows.length * lookupCount d table := by
  show (t.rows.flatMap (fun row => d.constraints.filterMap (tupOf table row))).length = _
  induction t.rows with
  | nil => simp
  | cons a rest ih =>
    rw [List.flatMap_cons, List.length_append, ih,
      filterMap_tupOf_length table a d.constraints, List.length_cons]
    show _ = (rest.length + 1) * lookupCount d table
    unfold lookupCount
    ring

/-- **`forced_trace_length` — THE AREA LAW.** For any descriptor declaring an exact-public table,
a satisfying trace has EXACTLY `declaredRows / lookupCount` main rows: the declared table pins the
trace length. -/
theorem forced_trace_length {hash : List ℤ → ℤ} {d : EffectVmDescriptor2}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2Public hash d minit mfin maddrs t)
    {td : TableDef} (htd : td ∈ d.tables) {rows : List (List Nat)}
    (hsem : td.sem = .exactPublicRows rows) :
    t.rows.length * lookupCount d td.id = rows.length := by
  have hperm := hsat.exact_lookup_perm htd hsem
  have hlen := hperm.length_eq
  rw [lookupLog_length] at hlen
  simpa [exactPublicTable] using hlen

/-- **`tdForced_sound` — THE COST MODEL CANNOT LIE ABOUT A WITNESSED DESCRIPTOR.** For any
descriptor with a satisfying trace, every declared table's `tdForced` verdict is either `unpinned`
(it says nothing) or `pinned` at the trace's ACTUAL row count. In particular it is never
`contradictory` and never `pinned` at a wrong number — which is exactly the failure the old `Nat`
field committed at `lookupCount ≠ 1`. -/
theorem tdForced_sound {hash : List ℤ → ℤ} {d : EffectVmDescriptor2}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2Public hash d minit mfin maddrs t)
    {td : TableDef} (htd : td ∈ d.tables) :
    tdForced d td = .pinned t.rows.length ∨ tdForced d td = .unpinned := by
  unfold tdForced
  cases hsem : td.sem with
  | exactPublicRows rows =>
    have hlaw : t.rows.length * lookupCount d td.id = rows.length :=
      forced_trace_length hsat htd hsem
    by_cases hc : lookupCount d td.id = 0
    · rw [hc, Nat.mul_zero] at hlaw
      have : rows = [] := List.eq_nil_of_length_eq_zero hlaw.symm
      subst this
      simp [hc]
    · have hcpos : 0 < lookupCount d td.id := Nat.pos_of_ne_zero hc
      have hmod : rows.length % lookupCount d td.id = 0 := by
        rw [← hlaw]; exact Nat.mul_mod_left _ _
      have hdiv : rows.length / lookupCount d td.id = t.rows.length := by
        rw [← hlaw, Nat.mul_div_cancel _ hcpos]
      simp [hc, hmod, hdiv]
  | _ => simp

/-- `meet` keeps the `{pinned n, unpinned}` invariant — so the fold over all tables does too. -/
theorem foldl_meet_sound (n : Nat) :
    ∀ (l : List ForcedRows), (∀ x ∈ l, x = .pinned n ∨ x = .unpinned) →
      ∀ acc, (acc = .pinned n ∨ acc = .unpinned) →
        l.foldl ForcedRows.meet acc = .pinned n ∨ l.foldl ForcedRows.meet acc = .unpinned
  | [], _, acc, hacc => hacc
  | x :: xs, hx, acc, hacc => by
    refine foldl_meet_sound n xs (fun y hy => hx y (List.mem_cons_of_mem _ hy))
      (ForcedRows.meet acc x) ?_
    rcases hacc with rfl | rfl <;> rcases hx x List.mem_cons_self with rfl | rfl <;>
      simp [ForcedRows.meet]

/-- **`costOf_forced_sound` — the PUBLISHED number is the trace's real length.** Whenever the
measured descriptor has a satisfying trace, `(costOf d).forcedTraceRows` is `pinned` at exactly
that trace's row count (or `unpinned`, saying nothing). Every `area` this file publishes for a
witnessed object is therefore `traceWidth ×` a length some prover actually pays. -/
theorem costOf_forced_sound {hash : List ℤ → ℤ} {d : EffectVmDescriptor2}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2Public hash d minit mfin maddrs t) :
    (costOf d).forcedTraceRows = .pinned t.rows.length
      ∨ (costOf d).forcedTraceRows = .unpinned := by
  refine foldl_meet_sound t.rows.length _ ?_ _ (Or.inr rfl)
  intro x hx
  obtain ⟨td, htd, rfl⟩ := List.mem_map.mp hx
  exact tdForced_sound hsat htd

/-- The table-routing family targets its table with EXACTLY one lookup. -/
theorem tableRouting_lookupCount (name : String) (tbl : List (List Nat)) :
    lookupCount (tableRoutingDesc name tbl) TRT_TID = 1 := rfl

/-- **The product route's trace length IS its table size** — `∏|Qᵢ|·|Σ|` rows, so its area is
`3 · ∏|Qᵢ| · |Σ|`. The `k`-independent column count does NOT make the composition free. -/
theorem tableRouting_forced_length {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {name : String} {tbl : List (List Nat)} {t : VmTrace}
    (hsat : Satisfied2Public hash (tableRoutingDesc name tbl) minit mfin maddrs t) :
    t.rows.length = tbl.length := by
  have h := forced_trace_length hsat (td := transitionTableDef tbl)
    (by simp [tableRoutingDesc]) (rows := tbl) rfl
  rwa [show (transitionTableDef tbl).id = TRT_TID from rfl,
    tableRouting_lookupCount name tbl, Nat.mul_one] at h

/-- The family's lookup log IS its trace's `(current, symbol, next)` column triple, row by row. -/
theorem tableRouting_lookupLog (name : String) (tbl : List (List Nat)) (t : VmTrace) :
    lookupLog (tableRoutingDesc name tbl) t TRT_TID
      = t.rows.map (fun a => [a CURRENT, a SYMBOL, a NEXT]) := by
  show t.rows.flatMap (fun row => [[row CURRENT, row SYMBOL, row NEXT]]) = _
  induction t.rows with
  | nil => rfl
  | cons a rest ih => rw [List.flatMap_cons, ih]; rfl

/-- **THE EULERIAN OBSTRUCTION, as a theorem (not prose).** A satisfying trace's sequence of
`(current, symbol, next)` triples is a PERMUTATION of the declared table — every declared
transition is traversed EXACTLY once — and the continuity window chains those triples end to end.
So a WHOLE-GRAPH declaration is satisfiable only by a word whose run is an Eulerian path through
the declared transition multigraph. This is why the whole-graph discipline is not merely expensive
(§4) but restrictive; the run-table discipline (§4b) has no such obstruction, its declared multiset
BEING the run. (Witness EXISTENCE, not soundness — the refinement never consumes this leg.) -/
theorem tableRouting_traverses_each_declared_row_once
    {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {name : String} {tbl : List (List Nat)} {t : VmTrace}
    (hsat : Satisfied2Public hash (tableRoutingDesc name tbl) minit mfin maddrs t) :
    (t.rows.map (fun a => [a CURRENT, a SYMBOL, a NEXT])).Perm (exactPublicTable tbl) := by
  have h := hsat.exact_lookup_perm (td := transitionTableDef tbl)
    (by simp [tableRoutingDesc]) (rows := tbl) rfl
  rwa [show (transitionTableDef tbl).id = TRT_TID from rfl, tableRouting_lookupLog] at h

/-- NON-VACUITY of the area law: it FIRES on the deployed family's own satisfying witness
(`DfaRoutingTableEmit.routeWit_satisfies`) — 1 declared row, 1 trace row. The hypothesis is
inhabited, so the law is a real constraint on real witnesses, not an empty implication. -/
theorem forced_length_fires :
    DfaRoutingTableEmit.routeWitTrace.rows.length = DfaRoutingTableEmit.demoTbl.length :=
  tableRouting_forced_length DfaRoutingTableEmit.routeWit_satisfies

/-! ## §6 — THE COMPOSITION IS SOUND: the product descriptor's acceptance exposes EVERY
component automaton's classification.

The DFA-level mirror of `VpaDecidable.prodVpa_lang`'s forward (projection) direction: components
step on the SAME symbol, so the product run projects componentwise. Here the projection is
arithmetic — the mixed-radix digits of the product state — and it composes with
`tableRouting_refines_classify` to give a statement about the EMITTED descriptor. -/

/-- Packing/unpacking a mixed-radix digit pair. -/
theorem pack_div_mod {a b m : Nat} (hb : b < m) :
    (a * m + b) / m = a ∧ (a * m + b) % m = b := by
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le b) hb
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hb, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

/-- A bounded-step automaton keeps its classification inside the state space. -/
theorem classifyFrom_lt (d : TableDfa Nat Nat) (r : Nat) (hd : ∀ s y, d.step s y < r) :
    ∀ (w : List Nat) (q : Nat), q < r → classifyFrom d q w < r
  | [], _, hq => hq
  | y :: ys, q, _ => classifyFrom_lt d r hd ys (d.step q y) (hd q y)

/-- The fold's unit classifies everything to `0`. -/
theorem classifyFrom_unit_zero : ∀ w : List Nat, classifyFrom unitDfa 0 w = 0
  | [] => rfl
  | _ :: ys => classifyFrom_unit_zero ys

/-- The `k`-fold product's step stays inside `r ^ k`. -/
theorem prodListDfa_step_lt (r : Nat) :
    ∀ (ds : List (TableDfa Nat Nat)), (∀ d ∈ ds, ∀ s y, d.step s y < r) →
      ∀ s y, (prodListDfa r ds).step s y < r ^ ds.length
  | [], _, _, _ => by simp [prodListDfa, unitDfa]
  | d :: ds, h, s, y => by
    have htail : ∀ e ∈ ds, ∀ a b, e.step a b < r := fun e he => h e (List.mem_cons_of_mem _ he)
    have hlo := prodListDfa_step_lt r ds htail (s % r ^ ds.length) y
    have hhi := h d List.mem_cons_self (s / r ^ ds.length) y
    show d.step _ y * r ^ ds.length + (prodListDfa r ds).step _ y < r ^ (ds.length + 1)
    calc d.step (s / r ^ ds.length) y * r ^ ds.length + (prodListDfa r ds).step _ y
        < d.step (s / r ^ ds.length) y * r ^ ds.length + r ^ ds.length := by omega
      _ = (d.step (s / r ^ ds.length) y + 1) * r ^ ds.length := by ring
      _ ≤ r * r ^ ds.length := Nat.mul_le_mul_right _ hhi
      _ = r ^ (ds.length + 1) := by rw [Nat.pow_succ]; ring

/-- The mixed-radix encoding of a bounded digit tuple stays inside `r ^ k`. -/
theorem encodeDigits_lt (r : Nat) :
    ∀ (qs : List Nat), 0 < r → (∀ q ∈ qs, q < r) → encodeDigits r qs < r ^ qs.length
  | [], _, _ => by simp [encodeDigits]
  | q :: qs, hr, h => by
    have htail := encodeDigits_lt r qs hr (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hq := h q List.mem_cons_self
    show q * r ^ qs.length + encodeDigits r qs < r ^ (qs.length + 1)
    calc q * r ^ qs.length + encodeDigits r qs
        < q * r ^ qs.length + r ^ qs.length := by omega
      _ = (q + 1) * r ^ qs.length := by ring
      _ ≤ r * r ^ qs.length := Nat.mul_le_mul_right _ hq
      _ = r ^ (qs.length + 1) := by rw [Nat.pow_succ]; ring

/-- **`classify_prod2` — the BINARY projection**: the product DFA's classification is the packed
pair of the components' classifications. Both components read the SAME word (this is
`prodVpa_lang`'s synchronization, at the DFA level where the stacks are absent). -/
theorem classify_prod2 (d e : TableDfa Nat Nat) (m : Nat) (he : ∀ s y, e.step s y < m) :
    ∀ (w : List Nat) (a b : Nat), b < m →
      classifyFrom (prod2 d e m) (a * m + b) w
        = classifyFrom d a w * m + classifyFrom e b w
  | [], _, _, _ => rfl
  | y :: ys, a, b, hb => by
    have hdm : (a * m + b) / m = a := (pack_div_mod (a := a) hb).1
    have hmm : (a * m + b) % m = b := (pack_div_mod (a := a) hb).2
    show classifyFrom (prod2 d e m) ((prod2 d e m).step (a * m + b) y) ys = _
    have hstep : (prod2 d e m).step (a * m + b) y = d.step a y * m + e.step b y := by
      show d.step ((a * m + b) / m) y * m + e.step ((a * m + b) % m) y = _
      rw [hdm, hmm]
    rw [hstep, classify_prod2 d e m he ys (d.step a y) (e.step b y) (he b y)]
    rfl

/-- **`classify_prodList` — the `k`-FOLD projection**: the `k`-fold product's classification is the
mixed-radix packing of the `k` component classifications, all reading the SAME word. This is the
whole content of "the product automaton accepts iff every component accepts", made arithmetic. -/
theorem classify_prodList (r : Nat) (hr : 0 < r) :
    ∀ (ds : List (TableDfa Nat Nat)) (qs : List Nat), ds.length = qs.length →
      (∀ d ∈ ds, ∀ s y, d.step s y < r) → (∀ q ∈ qs, q < r) →
      ∀ w : List Nat,
        classifyFrom (prodListDfa r ds) (encodeDigits r qs) w
          = encodeDigits r (List.zipWith (fun d q => classifyFrom d q w) ds qs)
  | [], [], _, _, _, w => by
      show classifyFrom unitDfa 0 w = 0
      exact classifyFrom_unit_zero w
  | [], _ :: _, hlen, _, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _, _ => by simp at hlen
  | d :: ds, q :: qs, hlen, hstep, hq, w => by
    have hlen' : ds.length = qs.length := by simpa using hlen
    have htailStep : ∀ e ∈ ds, ∀ s y, e.step s y < r :=
      fun e he => hstep e (List.mem_cons_of_mem _ he)
    have htailQ : ∀ x ∈ qs, x < r := fun x hx => hq x (List.mem_cons_of_mem _ hx)
    have hb : encodeDigits r qs < r ^ ds.length := by
      rw [hlen']; exact encodeDigits_lt r qs hr htailQ
    have hprod := classify_prod2 d (prodListDfa r ds) (r ^ ds.length)
      (prodListDfa_step_lt r ds htailStep) w q (encodeDigits r qs) hb
    have hzip : (List.zipWith (fun (a : TableDfa Nat Nat) (b : Nat) => classifyFrom a b w)
        ds qs).length = ds.length := by simp [hlen']
    have hIH := classify_prodList r hr ds qs hlen' htailStep htailQ w
    show classifyFrom (prod2 d (prodListDfa r ds) (r ^ ds.length))
        (q * r ^ qs.length + encodeDigits r qs) w
      = encodeDigits r (List.zipWith (fun a b => classifyFrom a b w) (d :: ds) (q :: qs))
    rw [← hlen', hprod, hIH, List.zipWith_cons_cons]
    show _ = classifyFrom d q w
        * r ^ (List.zipWith (fun a b => classifyFrom a b w) ds qs).length + _
    rw [hzip]

/-- **`productDesc_refines_components` — THE COMPOSITION SOUNDNESS THEOREM over the EMITTED
object.** For ANY declared table whose rows are graph entries of the `k`-fold product DFA, a trace
satisfying the emitted product descriptor (deployed exact-public acceptance `Satisfied2Public`)
reads a genuine ℕ-word off its shared symbol column, and its exposed public `final_state` IS the
mixed-radix packing of the `k` COMPONENT automata's classifications of that word. Every component's
verdict is therefore exposed by the one composed descriptor. `tableRouting_refines_classify` is the
whole descriptor leg; `classify_prodList` is the projection leg. -/
theorem productDesc_refines_components
    {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {name : String} {tbl : List (List Nat)} {t : VmTrace}
    (r : Nat) (hr : 0 < r) (ds : List (TableDfa Nat Nat)) (qs : List Nat)
    (hlen : ds.length = qs.length)
    (hstep : ∀ d ∈ ds, ∀ s y, d.step s y < r) (hq : ∀ q ∈ qs, q < r)
    (htbl : ∀ row ∈ tbl, ∃ s y, row = [s, y, (prodListDfa r ds).step s y])
    (hsmall : ∀ row ∈ tbl, ∀ v ∈ row, v < 2013265921)
    (hsat : Satisfied2Public hash (tableRoutingDesc name tbl) minit mfin maddrs t)
    (hne : t.rows ≠ [])
    (hstart : t.pub PI_INITIAL = Int.ofNat (encodeDigits r qs))
    (hq0 : encodeDigits r qs < 2013265921)
    (fN : ℕ) (hfin : t.pub PI_FINAL = Int.ofNat fN) (hfN : fN < 2013265921) :
    t.rows.map (fun a => a SYMBOL)
        = (t.rows.map (fun a => (a SYMBOL).toNat)).map Int.ofNat
      ∧ fN = encodeDigits r (List.zipWith
          (fun d q => classifyFrom d q (t.rows.map (fun a => (a SYMBOL).toNat))) ds qs) := by
  obtain ⟨hcol, hclass⟩ := tableRouting_refines_classify (prodListDfa r ds) htbl hsmall hsat hne
    (encodeDigits r qs) hstart hq0 fN hfin hfN
  refine ⟨hcol, ?_⟩
  rw [hclass, classify_prodList r hr ds qs hlen hstep hq]

/-- **The binary corollary — each component's verdict is read off by DIVISION and REMAINDER**, and
the product's `accepts` (the intersection) therefore implies BOTH components accept the shared
word. This is `prodVpa_lang`'s forward direction, landed on the emitted descriptor. -/
theorem productDesc_binary_components
    {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {name : String} {tbl : List (List Nat)} {t : VmTrace}
    (d e : TableDfa Nat Nat) (m : Nat)
    (he : ∀ s y, e.step s y < m) (a b : Nat) (hb : b < m)
    (htbl : ∀ row ∈ tbl, ∃ s y, row = [s, y, (prod2 d e m).step s y])
    (hsmall : ∀ row ∈ tbl, ∀ v ∈ row, v < 2013265921)
    (hsat : Satisfied2Public hash (tableRoutingDesc name tbl) minit mfin maddrs t)
    (hne : t.rows ≠ [])
    (hstart : t.pub PI_INITIAL = Int.ofNat (a * m + b)) (hq0 : a * m + b < 2013265921)
    (fN : ℕ) (hfin : t.pub PI_FINAL = Int.ofNat fN) (hfN : fN < 2013265921) :
    fN / m = classifyFrom d a (t.rows.map (fun x => (x SYMBOL).toNat))
      ∧ fN % m = classifyFrom e b (t.rows.map (fun x => (x SYMBOL).toNat))
      ∧ ((prod2 d e m).accepts fN →
          d.accepts (classifyFrom d a (t.rows.map (fun x => (x SYMBOL).toNat)))
            ∧ e.accepts (classifyFrom e b (t.rows.map (fun x => (x SYMBOL).toNat)))) := by
  have hclass := (tableRouting_refines_classify (prod2 d e m) htbl hsmall hsat hne
    (a * m + b) hstart hq0 fN hfin hfN).2
  rw [classify_prod2 d e m he _ a b hb] at hclass
  have hlt := classifyFrom_lt e m he (t.rows.map (fun x => (x SYMBOL).toNat)) b hb
  have hpack := pack_div_mod (a := classifyFrom d a (t.rows.map (fun x => (x SYMBOL).toNat)))
    (b := classifyFrom e b (t.rows.map (fun x => (x SYMBOL).toNat))) hlt
  refine ⟨by rw [hclass]; exact hpack.1, by rw [hclass]; exact hpack.2, ?_⟩
  intro hacc
  obtain ⟨h1, h2⟩ := hacc
  rw [hclass] at h1 h2
  rw [hpack.1] at h1
  rw [hpack.2] at h2
  exact ⟨h1, h2⟩

/-! ## §7 — THE EXHIBIT: 'even number of 1s' × 'ends in 1', composed and RUN.

A concrete pair of tiny automata composed by the product route, with an ACCEPTED and a REJECTED
word. `parityDfa` accepts words with an EVEN number of `1`s; `lastDfa` accepts words ENDING IN `1`.
The product's state packs both verdicts: `state / 2` is the parity machine's state, `state % 2` is
the last-symbol machine's.

⚠ Every `#guard` below is COMPILED EVALUATION of a closed `Bool` — it proves NO `Prop`; it pins the
decoded numbers. The `Prop`-level content is the two `accepts` theorems and §6's theorems. -/

/-- The composed pair: `parityDfa × lastDfa` at radix 2. -/
def pairDfa : TableDfa Nat Nat := prod2 parityDfa lastDfa 2

/-- The ACCEPTED word: `[1,1,0,1,1,1,1]` — six `1`s (even) and ends in `1`. -/
def acceptedWord : List Nat := [1, 1, 0, 1, 1, 1, 1]
/-- The REJECTED word: `[1,1,0,1,1,1,0]` — five `1`s (odd) and ends in `0`; BOTH components refuse. -/
def rejectedWord : List Nat := [1, 1, 0, 1, 1, 1, 0]

-- ⚑ THE COMPOSITION RUNNING (compiled evaluation — no `Prop`). The product classification PACKS
-- the two component classifications, exactly as §6's `classify_prod2` states. Start = 0*2 + 0 = 0.
#guard classifyFrom pairDfa 0 acceptedWord ==
  classifyFrom parityDfa 0 acceptedWord * 2 + classifyFrom lastDfa 0 acceptedWord
#guard classifyFrom pairDfa 0 rejectedWord ==
  classifyFrom parityDfa 0 rejectedWord * 2 + classifyFrom lastDfa 0 rejectedWord

-- ACCEPTED: composed state 1 decodes to (parity 0 = even ✓, last 1 = ends in 1 ✓).
#guard classifyFrom pairDfa 0 acceptedWord == 1
#guard (classifyFrom pairDfa 0 acceptedWord / 2, classifyFrom pairDfa 0 acceptedWord % 2) == (0, 1)

-- REJECTED: composed state 2 decodes to (parity 1 = odd ✗, last 0 ✗) — the product REFUSES.
#guard classifyFrom pairDfa 0 rejectedWord == 2
#guard (classifyFrom pairDfa 0 rejectedWord / 2, classifyFrom pairDfa 0 rejectedWord % 2) == (1, 0)

/-- The accepted word is genuinely accepted by the COMPOSED automaton — a `Prop`, not a `#guard`:
both components accept (`pairDfa.accepts` is the intersection). -/
theorem accepted_by_pair : pairDfa.accepts (classifyFrom pairDfa 0 acceptedWord) :=
  ⟨rfl, rfl⟩

/-- And the rejected word is genuinely REFUSED by the composed automaton. -/
theorem rejected_by_pair : ¬ pairDfa.accepts (classifyFrom pairDfa 0 rejectedWord) := by
  rintro ⟨h1, -⟩
  exact Nat.one_ne_zero h1

/-- The pair's emitted product descriptor (the `k = 2` instance of route (a)). -/
def pairDesc : EffectVmDescriptor2 :=
  tableRoutingDesc "tiny-automata-pair-parity-x-last::exact-public-v1"
    (tableOf pairDfa 4 2)

-- THE WIRE GOLDEN of the exhibit: 3 columns, 4 constraints, ONE declared 8-row table carrying the
-- WHOLE product transition graph. (Compiled evaluation; the Rust `exact_public_rows` arm parses
-- exactly this shape — see `DfaRoutingTableEmit`'s byte-pinned sibling.)
#guard emitVmJson2 pairDesc ==
  "{\"name\":\"tiny-automata-pair-parity-x-last::exact-public-v1\",\"ir\":2,\"trace_width\":3,\"public_input_count\":2,\"tables\":[{\"id\":35,\"name\":\"dfa_transition_table\",\"arity\":3,\"sem\":\"exact_public_rows\",\"rows\":[[0,0,0],[0,1,3],[1,0,0],[1,1,3],[2,0,2],[2,1,1],[3,0,2],[3,1,1]]}],\"constraints\":[{\"t\":\"lookup\",\"table\":35,\"tuple\":[{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":1},{\"t\":\"var\",\"v\":2}]},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":2}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"last\",\"col\":2,\"pi_index\":1}],\"hash_sites\":[],\"ranges\":[]}"

/-- **Every emitted table IS the automaton's transition graph** — the `htbl` hypothesis of §6,
discharged GENERALLY for `tableOf` (so it holds for every `k` of both routes, not just the
exhibit). -/
theorem tableOf_graph (d : TableDfa Nat Nat) (n m : Nat) :
    ∀ row ∈ tableOf d n m, ∃ s y, row = [s, y, d.step s y] := by
  intro row hrow
  simp only [tableOf, List.mem_flatMap, List.mem_map] at hrow
  obtain ⟨s, -, y, -, rfl⟩ := hrow
  exact ⟨s, y, rfl⟩

/-- The exhibit's table is the product graph. -/
theorem pairTbl_graph : ∀ row ∈ tableOf pairDfa 4 2, ∃ s y, row = [s, y, pairDfa.step s y] :=
  tableOf_graph pairDfa 4 2

/-- And its entries are wire-faithful (all `< p`) — the `hsmall` hypothesis, discharged. -/
theorem pairTbl_small : ∀ row ∈ tableOf pairDfa 4 2, ∀ v ∈ row, v < 2013265921 := by
  decide

/-- `lastDfa`'s step is bounded by 2 — the `he` hypothesis of the binary corollary. -/
theorem lastDfa_step_lt : ∀ s y, lastDfa.step s y < 2 := by
  intro s y
  exact Nat.mod_lt _ (by norm_num)

/-! ## §8 — axiom tripwires. -/

#assert_axioms lookupLog_length
#assert_axioms forced_trace_length
#assert_axioms tdForced_sound
#assert_axioms foldl_meet_sound
#assert_axioms costOf_forced_sound
#assert_axioms tableRouting_forced_length
#assert_axioms tableRouting_lookupLog
#assert_axioms tableRouting_traverses_each_declared_row_once
#assert_axioms forced_length_fires
#assert_axioms runTable_graph
#assert_axioms runTable_length
#assert_axioms classify_prod2
#assert_axioms classify_prodList
#assert_axioms productDesc_refines_components
#assert_axioms productDesc_binary_components
#assert_axioms tableOf_graph
#assert_axioms pairTbl_graph
#assert_axioms pairTbl_small
#assert_axioms accepted_by_pair
#assert_axioms rejected_by_pair

end Dregg2.Circuit.Emit.TinyAutomataCompose
