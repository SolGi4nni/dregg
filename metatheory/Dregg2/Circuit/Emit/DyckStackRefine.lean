/-
# Dregg2.Circuit.Emit.DyckStackRefine — SLICE 3 of *parse as derivation*: the SAT⇒SEM refinement
for the bounded-`D` Dyck pushdown descriptor (`circuit/src/dsl/dyck_stack.rs`,
`dregg-dyck-parse-v1`), plus the multi-row assembly into `CfgCompact.Replay`.

## What this file IS (and what it deliberately is NOT)

`docs/DESIGN-parse-as-derivation.md` §3 names the slice-3 goal: *a trace satisfying the dyck
descriptor implies a genuine `CfgCompact.Replay` of the Dyck reference grammar* — the direction that
says the circuit accepts ONLY real parses. The proven template is
`DerivationRefine.derivation_sat_imp_valid` (a whole-descriptor bridge that extracts on BOUNDARY ROW
0 under a named carrier + a range-check envelope, with concrete satisfying/rejecting witnesses).
This file mirrors that template and then attacks the burden the design names as genuinely new:
`derivation_sat_imp_valid` fires on ONE row; a parse is a MULTI-ROW run, so the bridge needs a
transition-relation induction with the STACK as the invariant.

It lands in two proven halves joined by ONE honestly-named residual (§7):

* **§1–§5 (per-row, against the descriptor).** `dyckDesc` transcribes the parse-semantic constraint
  set of the Rust `dyck_parse_descriptor` into IR-v2, and `dyck_sat_imp_row_valid` proves: a trace
  `Satisfied2 dyckDesc` witnesses the genuine per-row relation `DyckRowValid` on EVERY transition
  row — one legal rule application / terminal consumption / halt, with the full stack-threading
  equations (push + remainder shift + overflow guard) recovered over ℤ.
* **§6 (multi-row, abstract).** The pushdown machine as a FORWARD row list (`MRow`/`MStep`/`MRun`)
  and `mrun_imp_replay`: a forward-indexed run assembles into the BACKWARD-built inductive
  `CfgCompact.Replay`, with the rule sequence RECONSTRUCTED from the rows (`rulesOf`). This is the
  stack-invariant induction; it is proven, not assumed. Non-vacuity: `abs_brackets_accepts` derives
  `ReplayAccepts dyck [rBracket, rEmpty] [op, cl]` — the exact statement of the hand proof
  `CfgCompact.Reference.brackets_replays` — THROUGH the assembly, from the row list that mirrors
  `build_brackets_witness`'s action sequence one-for-one.

## §7 is the RESIDUAL — named, not `sorry`ed

The remaining seam is the DECODE GLUE: reading a satisfying trace's `D`-wide symbol-id cells +
`STACK_DEPTH` back into the `List (Symbol Brk NTs)` the abstract machine carries, and truncating the
`done` self-loop padding at the first `done`. That glue needs the depth↔occupancy invariant the Rust
module itself names as out of slice ("nothing yet ties `STACK_DEPTH` to which cells are nonzero").
Until it exists, `dyck_sat_imp_row_valid` and `mrun_imp_replay` are two proven halves of
`parse_sat_imp_replay`, NOT that theorem. This file does not claim otherwise, and states no `sorry`.

## The second named gap: `dyckDesc` is a TRANSCRIPTION, not an emit-gated twin

Every other `*Refine.lean` here refines a descriptor whose Rust twin is byte-pinned by an emit gate
(`DfaRoutingEmit`'s `#guard` on `emitVmJson2` + `circuit-prove/tests/dfa_routing_emit_gate.rs`).
`dyck_parse_descriptor` is RUST-authored with no Lean emit, so `dyckDesc` (§2) is a HAND
transcription. It is faithful by reading, not by a machine-checked equality: until the emit gate
lands, "SAT of `dyckDesc`" is not mechanically tied to "SAT of the deployed `dyck_parse_descriptor`".

Transcribed OUT: the `ENTRY_HASH`/`RUNNING_HASH` Poseidon2 commitment chain and the
`route_commitment` pin. They bind the parse to a public input; they constrain nothing about the
machine (the design calls the accumulator "orthogonal to the stack columns"), and modelling them
would drag in the chip carrier for zero parse-semantic content. Their absence cannot inflate the
SAT⇒SEM direction: fewer modelled constraints ⇒ a WEAKER hypothesis ⇒ a stronger theorem.

## The field denotation (mod-`p`, `p = 2013265921`)

As in `DerivationRefine`: gates vanish `≡ 0 [ZMOD p]`, and the ℤ conclusions of `DyckRowValid` are
recovered from the deployed range-check canonicality carried as the EXPLICIT hypothesis `DyckCanon`
(§3), inhabited concretely by `witTrace_canon` (§5). `DyckCanon` also carries the DEPTH range check
`0 ≤ STACK_DEPTH ≤ D` that `docs/DESIGN-parse-as-derivation.md` §2 specifies as a column property —
and that `dyck_stack.rs` does NOT emit as a constraint (a real gap in the circuit; see the lane
findings). Without it the `±1`/`+2` depth deltas are only field congruences and a wrapped depth is
not excluded.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. No crypto carrier is consumed (the hash
chain is out of the model). NEW file; imports read-only. Not reachable from `Dregg2.lean` (a shared
root this lane must not edit) — verified with `lake env lean` on this file.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.DecideSatisfied2
import Dregg2.Crypto.CfgCompact

namespace Dregg2.Circuit.Emit.DyckStackRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff pPrimeInt)
open Dregg2.Circuit.DecideSatisfied2
  (decideConstraint2 decideRowConstraints2 decideLookup_iff decideWindow_iff)
open Dregg2.Circuit.Argus.InterpCore (decideConstraint decideConstraint_iff)

set_option autoImplicit false
set_option maxRecDepth 40000

/-! ## §0 — Field-denotation glue (identical in shape to `DerivationRefine` §0). -/

/-- The deployed range-check invariant on a stored field cell: it is the canonical residue. -/
def Canon (x : ℤ) : Prop := 0 ≤ x ∧ x < 2013265921

instance (x : ℤ) : Decidable (Canon x) := inferInstanceAs (Decidable (_ ∧ _))

/-- Two canonical field cells congruent mod `p` are EQUAL over ℤ. -/
theorem eq_of_modEq_canon {a b : ℤ} (ha : Canon a) (hb : Canon b)
    (h : a ≡ b [ZMOD 2013265921]) : a = b := by
  obtain ⟨k, hk⟩ := h.dvd
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  omega

/-- Two SMALL integers (`|·| ≤ 16`, the depth arithmetic's range) congruent mod `p` are equal —
`p` dwarfs the gap, so no wrap can hide a difference. -/
theorem eq_of_modEq_small {a b : ℤ} (ha : -16 ≤ a ∧ a ≤ 16) (hb : -16 ≤ b ∧ b ≤ 16)
    (h : a ≡ b [ZMOD 2013265921]) : a = b := by
  obtain ⟨k, hk⟩ := h.dvd
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  omega

theorem canon_zero : Canon 0 := ⟨le_refl 0, by norm_num⟩
theorem canon_one : Canon 1 := ⟨by norm_num, by norm_num⟩
theorem canon_two : Canon 2 := ⟨by norm_num, by norm_num⟩
theorem canon_three : Canon 3 := ⟨by norm_num, by norm_num⟩

/-! ## §1 — The column layout, transcribed from `dyck_stack.rs::col` at `STACK_D = 5`. -/

/-- The bounded stack depth carried in columns (`dyck_stack.rs::STACK_D`). -/
def STACK_D : Nat := 5

/-- `STACK[i]` — cell `i` of the bounded stack; `STACK[0]` is the top. -/
def stk (i : Nat) : Nat := i

/-- Current stack depth (pointer). -/
def STACK_DEPTH : Nat := 5
/-- The stack depth AFTER this row's action (witness helper, threaded into `next.STACK_DEPTH`). -/
def DEPTH_NEXT : Nat := 6
/-- `STEP_KIND = rule` selector. -/
def IS_RULE : Nat := 7
/-- `STEP_KIND = term` selector. -/
def IS_TERM : Nat := 8
/-- `STEP_KIND = done` selector. -/
def IS_DONE : Nat := 9
/-- The production id this row fires. -/
def RULE_ID : Nat := 10
/-- The input token read on a `term` step. -/
def INPUT_TOKEN : Nat := 11
/-- Input-tape pointer. -/
def INPUT_POS : Nat := 12
/-- `INPUT_POS + 1` (witness helper). -/
def INPUT_POS_P1 : Nat := 13
/-- Rule selector: `1` iff this row fires `rBracket`. -/
def SEL_BRACKET : Nat := 14
/-- Rule selector: `1` iff this row fires `rEmpty`. -/
def SEL_EMPTY : Nat := 15
/-- Per-step commitment column (present in the layout; UNCONSTRAINED in this model — see header). -/
def ENTRY_HASH : Nat := 16
/-- Rolling parse commitment (present in the layout; UNCONSTRAINED in this model). -/
def RUNNING_HASH : Nat := 17
/-- First-row selector. -/
def IS_FIRST : Nat := 18
/-- Fixed lane `= op`. -/
def LANE_OP : Nat := 19
/-- Fixed lane `= cl`. -/
def LANE_CL : Nat := 20
/-- Fixed lane `= S`. -/
def LANE_S : Nat := 21
/-- Fixed lane `= 0`. -/
def LANE_ZERO : Nat := 22

/-- Trace width (`dyck_stack.rs::DYCK_WIDTH = STACK_D + 18`). -/
def DYCK_WIDTH : Nat := 23

/-- Reserved EMPTY stack-cell marker. -/
def SYM_EMPTY : ℤ := 0
/-- The sole nonterminal `S` (`CfgCompact.Reference.NTs.S`). -/
def SYM_S : ℤ := 1
/-- Terminal `op = '['` (`CfgCompact.Reference.Brk.op`). -/
def SYM_OP : ℤ := 2
/-- Terminal `cl = ']'` (`CfgCompact.Reference.Brk.cl`). -/
def SYM_CL : ℤ := 3

/-- `rBracket : S → [ S ]`. -/
def RULE_BRACKET : ℤ := 1
/-- `rEmpty : S → ε`. -/
def RULE_EMPTY : ℤ := 2

/-- pi[0] the grammar's initial nonterminal. -/
def PI_INITIAL : Nat := 0
/-- pi[1] the input word length. -/
def PI_INPUT_LEN : Nat := 1

/-! ## §2 — The descriptor: the parse-semantic constraint set of `dyck_parse_descriptor`. -/

/-- `x·(x−1)` — the booleanity gate (`ConstraintExpr::Binary`). -/
def gBin (c : Nat) : EmittedExpr := .mul (.var c) (.add (.var c) (.const (-1)))
/-- `sel · e` — the `Gated` wrapper. -/
def gGate (sel : Nat) (e : EmittedExpr) : EmittedExpr := .mul (.var sel) e
/-- `a − b`. -/
def gSub (a b : Nat) : EmittedExpr := .add (.var a) (.mul (.const (-1)) (.var b))
/-- `a − k`. -/
def gSubK (a : Nat) (k : ℤ) : EmittedExpr := .add (.var a) (.const (-k))
/-- `a − b − k`. -/
def gDiffIs (a b : Nat) (k : ℤ) : EmittedExpr := .add (gSub a b) (.const (-k))

/-- `next[nc] − local[lc]` as a two-row window body. -/
def wThread (nc lc : Nat) : WindowExpr := .add (.nxt nc) (.mul (.const (-1)) (.loc lc))
/-- `local[sel] · e` — the `Gated` wrapper on a window body. -/
def wGate (sel : Nat) (e : WindowExpr) : WindowExpr := .mul (.loc sel) e

/-- A per-row gate constraint. -/
def cg (e : EmittedExpr) : VmConstraint2 := .base (.gate e)
/-- A TRANSITION window constraint (asserted on every row but the last — the `when_transition`
lowering the Rust `references_next` driver mirrors by checking rows `0..n−1`). -/
def cw (b : WindowExpr) : VmConstraint2 := .windowGate ⟨b, true⟩

/-- The constraint list, flat, in the Rust module's order. -/
def dyckConstraints : List VmConstraint2 :=
  [ -- selector booleans
    cg (gBin IS_RULE), cg (gBin IS_TERM), cg (gBin IS_DONE), cg (gBin IS_FIRST),
    cg (gBin SEL_BRACKET), cg (gBin SEL_EMPTY),
    -- exactly one action kind: IS_RULE + IS_TERM + IS_DONE − 1 == 0
    cg (.add (.add (.add (.var IS_RULE) (.var IS_TERM)) (.var IS_DONE)) (.const (-1))),
    -- the rule sub-selectors partition IS_RULE
    cg (.add (.add (.var SEL_BRACKET) (.var SEL_EMPTY)) (.mul (.const (-1)) (.var IS_RULE))),
    -- rule sub-selectors pinned to their ids: sel · (RULE_ID − r) == 0
    cg (gGate SEL_BRACKET (gSubK RULE_ID RULE_BRACKET)),
    cg (gGate SEL_EMPTY (gSubK RULE_ID RULE_EMPTY)),
    -- rule membership: IS_RULE · (RULE_ID − 1)(RULE_ID − 2) == 0
    cg (gGate IS_RULE (.mul (gSubK RULE_ID 1) (gSubK RULE_ID 2))),
    -- top match, rule step: the popped stack top is the nonterminal S
    cg (gGate IS_RULE (gSubK (stk 0) SYM_S)),
    -- top match, term step: the stack top equals the input token
    cg (gGate IS_TERM (gSub (stk 0) INPUT_TOKEN)),
    -- done: stack top empty and depth zero
    cg (gGate IS_DONE (gSubK (stk 0) SYM_EMPTY)),
    cg (gGate IS_DONE (gSubK STACK_DEPTH 0)),
    -- input-pointer helper: INPUT_POS_P1 == INPUT_POS + 1
    cg (gDiffIs INPUT_POS_P1 INPUT_POS 1),
    -- depth deltas per action
    cg (gGate SEL_BRACKET (gDiffIs DEPTH_NEXT STACK_DEPTH 2)),
    cg (gGate SEL_EMPTY (gDiffIs DEPTH_NEXT STACK_DEPTH (-1))),
    cg (gGate IS_TERM (gDiffIs DEPTH_NEXT STACK_DEPTH (-1))),
    cg (gGate IS_DONE (gDiffIs DEPTH_NEXT STACK_DEPTH 0)),
    -- fixed constant lanes (the Transition sources for pushing constants)
    cg (gSubK LANE_OP SYM_OP), cg (gSubK LANE_CL SYM_CL), cg (gSubK LANE_S SYM_S),
    cg (gSubK LANE_ZERO SYM_EMPTY),
    -- rBracket overflow guard: local.STACK[3] and [4] must be EMPTY under the shift-by-2
    cg (gGate SEL_BRACKET (gSubK (stk 3) SYM_EMPTY)),
    cg (gGate SEL_BRACKET (gSubK (stk 4) SYM_EMPTY)),
    -- ============ cross-row (transition) constraints ============
    -- depth threading: next.STACK_DEPTH == this.DEPTH_NEXT
    cw (wThread STACK_DEPTH DEPTH_NEXT),
    -- rBracket push (γ = op S cl) — the RHS over the popped top
    cw (wGate SEL_BRACKET (wThread (stk 0) LANE_OP)),
    cw (wGate SEL_BRACKET (wThread (stk 1) LANE_S)),
    cw (wGate SEL_BRACKET (wThread (stk 2) LANE_CL)),
    -- rBracket remainder shift by |γ| − 1 = 2
    cw (wGate SEL_BRACKET (wThread (stk 3) (stk 1))),
    cw (wGate SEL_BRACKET (wThread (stk 4) (stk 2))),
    -- rEmpty (S → ε): pop the top, shift the rest down, vacate the deepest cell
    cw (wGate SEL_EMPTY (wThread (stk 0) (stk 1))),
    cw (wGate SEL_EMPTY (wThread (stk 1) (stk 2))),
    cw (wGate SEL_EMPTY (wThread (stk 2) (stk 3))),
    cw (wGate SEL_EMPTY (wThread (stk 3) (stk 4))),
    cw (wGate SEL_EMPTY (wThread (stk 4) LANE_ZERO)),
    -- term: pop the matched terminal, same shift-down
    cw (wGate IS_TERM (wThread (stk 0) (stk 1))),
    cw (wGate IS_TERM (wThread (stk 1) (stk 2))),
    cw (wGate IS_TERM (wThread (stk 2) (stk 3))),
    cw (wGate IS_TERM (wThread (stk 3) (stk 4))),
    cw (wGate IS_TERM (wThread (stk 4) LANE_ZERO)),
    -- done: the machine has halted; the stack holds
    cw (wGate IS_DONE (wThread (stk 0) (stk 0))),
    cw (wGate IS_DONE (wThread (stk 1) (stk 1))),
    cw (wGate IS_DONE (wThread (stk 2) (stk 2))),
    cw (wGate IS_DONE (wThread (stk 3) (stk 3))),
    cw (wGate IS_DONE (wThread (stk 4) (stk 4))),
    -- input pointer: a term advances it by one, every other step holds it
    cw (wGate IS_TERM (wThread INPUT_POS INPUT_POS_P1)),
    cw (.mul (.add (.const 1) (.mul (.const (-1)) (.loc IS_TERM))) (wThread INPUT_POS INPUT_POS)),
    -- ============ boundaries ============
    .base (.piBinding .first (stk 0) PI_INITIAL),
    .base (.boundary .first (gSubK STACK_DEPTH 1)),
    .base (.boundary .first (gSubK INPUT_POS 0)),
    .base (.boundary .first (gSubK IS_FIRST 1)),
    .base (.boundary .last (gSubK IS_DONE 1)),
    .base (.boundary .last (gSubK STACK_DEPTH 0)),
    .base (.piBinding .last INPUT_POS PI_INPUT_LEN) ]

/-- **`dyckDesc`** — the IR-v2 transcription of `dyck_parse_descriptor`'s parse-semantic constraint
set (see the header for what is transcribed OUT and why). -/
def dyckDesc : EffectVmDescriptor2 :=
  { name        := "dregg-dyck-parse-v1"
  , traceWidth  := DYCK_WIDTH
  , piCount     := 4
  , tables      := []
  , constraints := dyckConstraints
  , hashSites   := []
  , ranges      := [] }

/-! ## §3 — The canonicality + depth-range envelope. -/

/-- **The Dyck envelope**: every cell of every row is the canonical residue (the deployed
range-check invariant), and the two depth columns lie in `[0, D]` (the design's column property
`0 ≤ STACK_DEPTH ≤ D`; `dyck_stack.rs` does not yet emit it — see the header). Carried EXPLICITLY:
the field denotation only pins gates mod `p`. Inhabited concretely by `witTrace_canon` (§5), so it
is never a vacuous antecedent. -/
structure DyckCanon (t : VmTrace) : Prop where
  cells : ∀ i c, Canon (t.rows.getD i zeroAsg c)
  depth : ∀ i, 0 ≤ t.rows.getD i zeroAsg STACK_DEPTH ∧ t.rows.getD i zeroAsg STACK_DEPTH ≤ 5
  depthNext : ∀ i, 0 ≤ t.rows.getD i zeroAsg DEPTH_NEXT ∧ t.rows.getD i zeroAsg DEPTH_NEXT ≤ 5

theorem canon_loc {t : VmTrace} (h : DyckCanon t) (i c : Nat) : Canon ((envAt t i).loc c) :=
  h.cells i c

/-- Row `i`'s NEXT cells are canonical — they ARE row `i+1`'s local cells. -/
theorem canon_nxt {t : VmTrace} (h : DyckCanon t) (i c : Nat) : Canon ((envAt t i).nxt c) :=
  h.cells (i + 1) c

/-! ## §4 — The per-row semantic relation and its extraction. -/

/-- **`DyckRowValid env`** — the genuine per-row pushdown-step relation the Dyck circuit computes,
over the ℤ field model. A satisfying transition row witnesses exactly ONE legal machine action:

* `kindsBoolean`/`kindPartition` — the row commits to exactly one of `rule`/`term`/`done`;
* `subBoolean`/`subPartition`/`*Pinned` — a `rule` row commits to exactly one production, pinned to
  its id;
* `ruleMembership` — a `rule` row's `RULE_ID` IS a rule of the Dyck grammar (`1 = rBracket`,
  `2 = rEmpty`): the rule-table check;
* `ruleTopIsS` — a `rule` row pops the nonterminal `S` (the LHS match);
* `termTopIsToken` — a `term` row's stack top IS the consumed input token;
* `bracketPush` — the FULL `S → [ S ]` step: the pushed RHS `(op, S, cl)`, the REMAINDER SHIFT by
  `|γ| − 1 = 2`, the OVERFLOW GUARD (the two cells the shift would push out of the buffer are
  EMPTY, so nothing is silently dropped), and the depth delta `+2`;
* `emptyPop`/`termPop` — the `S → ε` / terminal-consumption steps: shift-down, vacated deepest cell,
  depth delta `−1` (which, with the depth range, also forces `STACK_DEPTH ≥ 1` — a pop cannot fire
  on an empty stack);
* `doneEmpty`/`doneHolds` — a `done` row has an empty top at depth `0` and moves nothing;
* `termAdvances`/`nonTermHolds` — the input tape moves exactly on a `term`;
* `depthThreads` — `next.STACK_DEPTH` IS this row's `DEPTH_NEXT`.

This is the design's `ParseStepValid` at the Dyck instance. -/
structure DyckRowValid (env : VmRowEnv) : Prop where
  kindsBoolean : (env.loc IS_RULE = 0 ∨ env.loc IS_RULE = 1)
    ∧ (env.loc IS_TERM = 0 ∨ env.loc IS_TERM = 1) ∧ (env.loc IS_DONE = 0 ∨ env.loc IS_DONE = 1)
  kindPartition : env.loc IS_RULE + env.loc IS_TERM + env.loc IS_DONE = 1
  subBoolean : (env.loc SEL_BRACKET = 0 ∨ env.loc SEL_BRACKET = 1)
    ∧ (env.loc SEL_EMPTY = 0 ∨ env.loc SEL_EMPTY = 1)
  subPartition : env.loc SEL_BRACKET + env.loc SEL_EMPTY = env.loc IS_RULE
  bracketPinned : env.loc SEL_BRACKET = 1 → env.loc RULE_ID = RULE_BRACKET
  emptyPinned : env.loc SEL_EMPTY = 1 → env.loc RULE_ID = RULE_EMPTY
  ruleMembership : env.loc IS_RULE = 1 →
    env.loc RULE_ID = RULE_BRACKET ∨ env.loc RULE_ID = RULE_EMPTY
  ruleTopIsS : env.loc IS_RULE = 1 → env.loc (stk 0) = SYM_S
  termTopIsToken : env.loc IS_TERM = 1 → env.loc (stk 0) = env.loc INPUT_TOKEN
  doneEmpty : env.loc IS_DONE = 1 → env.loc (stk 0) = SYM_EMPTY ∧ env.loc STACK_DEPTH = 0
  depthThreads : env.nxt STACK_DEPTH = env.loc DEPTH_NEXT
  bracketPush : env.loc SEL_BRACKET = 1 →
    env.nxt (stk 0) = SYM_OP ∧ env.nxt (stk 1) = SYM_S ∧ env.nxt (stk 2) = SYM_CL
      ∧ env.nxt (stk 3) = env.loc (stk 1) ∧ env.nxt (stk 4) = env.loc (stk 2)
      ∧ env.loc (stk 3) = SYM_EMPTY ∧ env.loc (stk 4) = SYM_EMPTY
      ∧ env.loc DEPTH_NEXT = env.loc STACK_DEPTH + 2
  emptyPop : env.loc SEL_EMPTY = 1 →
    env.nxt (stk 0) = env.loc (stk 1) ∧ env.nxt (stk 1) = env.loc (stk 2)
      ∧ env.nxt (stk 2) = env.loc (stk 3) ∧ env.nxt (stk 3) = env.loc (stk 4)
      ∧ env.nxt (stk 4) = SYM_EMPTY
      ∧ env.loc DEPTH_NEXT = env.loc STACK_DEPTH - 1 ∧ 1 ≤ env.loc STACK_DEPTH
  termPop : env.loc IS_TERM = 1 →
    env.nxt (stk 0) = env.loc (stk 1) ∧ env.nxt (stk 1) = env.loc (stk 2)
      ∧ env.nxt (stk 2) = env.loc (stk 3) ∧ env.nxt (stk 3) = env.loc (stk 4)
      ∧ env.nxt (stk 4) = SYM_EMPTY
      ∧ env.loc DEPTH_NEXT = env.loc STACK_DEPTH - 1 ∧ 1 ≤ env.loc STACK_DEPTH
  doneHolds : env.loc IS_DONE = 1 →
    env.nxt (stk 0) = env.loc (stk 0) ∧ env.nxt (stk 1) = env.loc (stk 1)
      ∧ env.nxt (stk 2) = env.loc (stk 2) ∧ env.nxt (stk 3) = env.loc (stk 3)
      ∧ env.nxt (stk 4) = env.loc (stk 4)
      ∧ env.loc DEPTH_NEXT = env.loc STACK_DEPTH
  termAdvances : env.loc IS_TERM = 1 →
    env.nxt INPUT_POS ≡ env.loc INPUT_POS + 1 [ZMOD 2013265921]
  nonTermHolds : env.loc IS_TERM = 0 → env.nxt INPUT_POS = env.loc INPUT_POS

section Extract
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- Any base gate forces its body to vanish mod `p` on a TRANSITION row (`i + 1 < length`). -/
theorem dyck_gate (hsat : Satisfied2 hash dyckDesc minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {g : EmittedExpr} (hg : cg g ∈ dyckDesc.constraints) :
    g.eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints i (by omega) _ hg
  have hlf : (i + 1 == t.rows.length) = false := by
    have h : i + 1 ≠ t.rows.length := by omega
    simpa using h
  simpa only [cg, VmConstraint2.holdsAt, VmConstraint.holdsVm, hlf] using hrc

/-- Any transition window constraint fires on a TRANSITION row. -/
theorem dyck_win (hsat : Satisfied2 hash dyckDesc minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {b : WindowExpr} (hw : cw b ∈ dyckDesc.constraints) :
    b.eval (envAt t i) ≡ 0 [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints i (by omega) _ hw
  have hlf : (i + 1 == t.rows.length) = false := by
    have h : i + 1 ≠ t.rows.length := by omega
    simpa using h
  have h2 : WindowConstraint.holdsAt (envAt t i) (i + 1 == t.rows.length) ⟨b, true⟩ := hrc
  simp only [WindowConstraint.holdsAt, if_true] at h2
  exact h2 hlf

end Extract

/-- Booleanity from a `gBin` gate under the field denotation: a CANONICAL cell whose booleanity
gate vanishes mod `p` IS `0` or `1` over ℤ (primality splits `p ∣ x(x−1)`). -/
theorem bin_of_gate {a : Assignment} {c : Nat}
    (h : (gBin c).eval a ≡ 0 [ZMOD 2013265921]) (hc : Canon (a c)) : a c = 0 ∨ a c = 1 := by
  simp only [gBin, EmittedExpr.eval] at h
  have hd : (2013265921 : ℤ) ∣ a c * (a c + (-1)) := Int.modEq_zero_iff_dvd.mp h
  obtain ⟨hc0, hc1⟩ := hc
  rcases pPrimeInt.dvd_mul.mp hd with hx | hx
  · obtain ⟨k, hk⟩ := hx; left; omega
  · obtain ⟨k, hk⟩ := hx; right; omega

/-- Membership plumbing: peel `List.mem_cons` to the named constraint's position. -/
macro "dyck_mem" : tactic =>
  `(tactic| (show _ ∈ dyckConstraints
             simp only [dyckConstraints]
             repeat' first | exact List.Mem.head _ | apply List.Mem.tail))

/-! ### §4.1 — THE PER-ROW BRIDGE (the SAT⇒SEM tooth). -/

/-- **`dyck_sat_imp_row_valid` — a satisfying trace's every TRANSITION row is a genuine pushdown
step.** A trace `t` that SATISFIES the transcribed `dyckDesc` (via the deployed acceptance predicate
`Satisfied2`), whose cells satisfy the deployed range-check envelope (`DyckCanon`), witnesses the
genuine relation `DyckRowValid` on every row `i` with `i + 1 < t.rows.length` (the rows on which the
deployed `when_transition` lowering binds). This is the design's `ParseStepValid` extraction: one
legal rule application / terminal consumption / halt per row, with the full stack-threading
equations recovered over ℤ. -/
theorem dyck_sat_imp_row_valid {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace} (hsat : Satisfied2 hash dyckDesc minit mfin maddrs t)
    (hcanon : DyckCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    DyckRowValid (envAt t i) := by
  set e := envAt t i with he
  have G : ∀ {g : EmittedExpr}, cg g ∈ dyckDesc.constraints →
      g.eval e.loc ≡ 0 [ZMOD 2013265921] := fun hg => dyck_gate hsat i hi hg
  have W : ∀ {b : WindowExpr}, cw b ∈ dyckDesc.constraints →
      b.eval e ≡ 0 [ZMOD 2013265921] := fun hw => dyck_win hsat i hi hw
  have CL : ∀ c, Canon (e.loc c) := fun c => canon_loc hcanon i c
  have CN : ∀ c, Canon (e.nxt c) := fun c => canon_nxt hcanon i c
  have DB : 0 ≤ e.loc STACK_DEPTH ∧ e.loc STACK_DEPTH ≤ 5 := hcanon.depth i
  have DNB : 0 ≤ e.loc DEPTH_NEXT ∧ e.loc DEPTH_NEXT ≤ 5 := hcanon.depthNext i
  have lift_loc : ∀ {a b : Nat}, e.loc a ≡ e.loc b [ZMOD 2013265921] → e.loc a = e.loc b :=
    fun h => eq_of_modEq_canon (CL _) (CL _) h
  have lift_nl : ∀ {a b : Nat}, e.nxt a ≡ e.loc b [ZMOD 2013265921] → e.nxt a = e.loc b :=
    fun h => eq_of_modEq_canon (CN _) (CL _) h
  -- the constant lanes are pinned (they are the push sources).
  have hop : e.loc LANE_OP = SYM_OP := by
    have hg := G (g := gSubK LANE_OP SYM_OP) (by dyck_mem)
    simp only [gSubK, EmittedExpr.eval] at hg
    exact eq_of_modEq_canon (CL _) canon_two ((gate_modEq_iff (by simp only [SYM_OP]; ring)).mp hg)
  have hlS : e.loc LANE_S = SYM_S := by
    have hg := G (g := gSubK LANE_S SYM_S) (by dyck_mem)
    simp only [gSubK, EmittedExpr.eval] at hg
    exact eq_of_modEq_canon (CL _) canon_one ((gate_modEq_iff (by simp only [SYM_S]; ring)).mp hg)
  have hcl : e.loc LANE_CL = SYM_CL := by
    have hg := G (g := gSubK LANE_CL SYM_CL) (by dyck_mem)
    simp only [gSubK, EmittedExpr.eval] at hg
    exact eq_of_modEq_canon (CL _) canon_three ((gate_modEq_iff (by simp only [SYM_CL]; ring)).mp hg)
  have hz : e.loc LANE_ZERO = SYM_EMPTY := by
    have hg := G (g := gSubK LANE_ZERO SYM_EMPTY) (by dyck_mem)
    simp only [gSubK, EmittedExpr.eval] at hg
    exact eq_of_modEq_canon (CL _) canon_zero ((gate_modEq_iff (by simp only [SYM_EMPTY]; ring)).mp hg)
  -- gated per-row equality against a constant.
  have gc : ∀ {sel a : Nat} {k : ℤ}, cg (gGate sel (gSubK a k)) ∈ dyckDesc.constraints →
      e.loc sel = 1 → Canon k → e.loc a = k := by
    intro sel a k hm hs hk
    have hg := G hm
    simp only [gGate, gSubK, EmittedExpr.eval] at hg
    rw [hs, one_mul] at hg
    exact eq_of_modEq_canon (CL _) hk ((gate_modEq_iff (by ring)).mp hg)
  -- gated cross-row threading.
  have wt : ∀ {sel nc lc : Nat}, cw (wGate sel (wThread nc lc)) ∈ dyckDesc.constraints →
      e.loc sel = 1 → e.nxt nc = e.loc lc := by
    intro sel nc lc hm hs
    have hw := W hm
    simp only [wGate, wThread, WindowExpr.eval] at hw
    rw [hs, one_mul] at hw
    exact lift_nl ((gate_modEq_iff (by ring)).mp hw)
  -- gated depth delta.
  have dd : ∀ {sel : Nat} {k : ℤ}, cg (gGate sel (gDiffIs DEPTH_NEXT STACK_DEPTH k))
      ∈ dyckDesc.constraints → e.loc sel = 1 → -6 ≤ k → k ≤ 6 →
      e.loc DEPTH_NEXT = e.loc STACK_DEPTH + k := by
    intro sel k hm hs hk0 hk1
    have hg := G hm
    simp only [gGate, gDiffIs, gSub, EmittedExpr.eval] at hg
    rw [hs, one_mul] at hg
    exact eq_of_modEq_small ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ((gate_modEq_iff (by ring)).mp hg)
  refine
    { kindsBoolean := ?_, kindPartition := ?_, subBoolean := ?_, subPartition := ?_,
      bracketPinned := ?_, emptyPinned := ?_, ruleMembership := ?_, ruleTopIsS := ?_,
      termTopIsToken := ?_, doneEmpty := ?_, depthThreads := ?_, bracketPush := ?_,
      emptyPop := ?_, termPop := ?_, doneHolds := ?_, termAdvances := ?_, nonTermHolds := ?_ }
  · exact ⟨bin_of_gate (G (by dyck_mem)) (CL _), bin_of_gate (G (by dyck_mem)) (CL _),
           bin_of_gate (G (by dyck_mem)) (CL _)⟩
  · have hg := G (g := .add (.add (.add (.var IS_RULE) (.var IS_TERM)) (.var IS_DONE)) (.const (-1)))
      (by dyck_mem)
    simp only [EmittedExpr.eval] at hg
    have h1 : e.loc IS_RULE + e.loc IS_TERM + e.loc IS_DONE ≡ 1 [ZMOD 2013265921] :=
      (gate_modEq_iff (by ring)).mp hg
    have hb1 := bin_of_gate (G (g := gBin IS_RULE) (by dyck_mem)) (CL IS_RULE)
    have hb2 := bin_of_gate (G (g := gBin IS_TERM) (by dyck_mem)) (CL IS_TERM)
    have hb3 := bin_of_gate (G (g := gBin IS_DONE) (by dyck_mem)) (CL IS_DONE)
    refine eq_of_modEq_small ?_ (by norm_num) h1
    rcases hb1 with h | h <;> rcases hb2 with h' | h' <;> rcases hb3 with h'' | h'' <;>
      rw [h, h', h''] <;> norm_num
  · exact ⟨bin_of_gate (G (by dyck_mem)) (CL _), bin_of_gate (G (by dyck_mem)) (CL _)⟩
  · have hg := G (g := .add (.add (.var SEL_BRACKET) (.var SEL_EMPTY))
      (.mul (.const (-1)) (.var IS_RULE))) (by dyck_mem)
    simp only [EmittedExpr.eval] at hg
    have h1 : e.loc SEL_BRACKET + e.loc SEL_EMPTY ≡ e.loc IS_RULE [ZMOD 2013265921] :=
      (gate_modEq_iff (by ring)).mp hg
    have hb1 := bin_of_gate (G (g := gBin SEL_BRACKET) (by dyck_mem)) (CL SEL_BRACKET)
    have hb2 := bin_of_gate (G (g := gBin SEL_EMPTY) (by dyck_mem)) (CL SEL_EMPTY)
    have hb3 := bin_of_gate (G (g := gBin IS_RULE) (by dyck_mem)) (CL IS_RULE)
    refine eq_of_modEq_small ?_ ?_ h1
    · rcases hb1 with h | h <;> rcases hb2 with h' | h' <;> rw [h, h'] <;> norm_num
    · rcases hb3 with h'' | h'' <;> rw [h''] <;> norm_num
  · intro hs; exact gc (by dyck_mem) hs canon_one
  · intro hs; exact gc (by dyck_mem) hs canon_two
  · intro hr
    have hg := G (g := gGate IS_RULE (.mul (gSubK RULE_ID 1) (gSubK RULE_ID 2))) (by dyck_mem)
    simp only [gGate, gSubK, EmittedExpr.eval] at hg
    rw [hr, one_mul] at hg
    have hd : (2013265921 : ℤ) ∣ (e.loc RULE_ID + (-1)) * (e.loc RULE_ID + (-2)) :=
      Int.modEq_zero_iff_dvd.mp hg
    obtain ⟨hc0, hc1⟩ := CL RULE_ID
    rcases pPrimeInt.dvd_mul.mp hd with hx | hx
    · obtain ⟨k, hk⟩ := hx; left; simp only [RULE_BRACKET]; omega
    · obtain ⟨k, hk⟩ := hx; right; simp only [RULE_EMPTY]; omega
  · intro hr; exact gc (by dyck_mem) hr canon_one
  · intro hr
    have hg := G (g := gGate IS_TERM (gSub (stk 0) INPUT_TOKEN)) (by dyck_mem)
    simp only [gGate, gSub, EmittedExpr.eval] at hg
    rw [hr, one_mul] at hg
    exact lift_loc ((gate_modEq_iff (by ring)).mp hg)
  · intro hr
    exact ⟨gc (by dyck_mem) hr canon_zero, gc (by dyck_mem) hr canon_zero⟩
  · have hw := W (b := wThread STACK_DEPTH DEPTH_NEXT) (by dyck_mem)
    simp only [wThread, WindowExpr.eval] at hw
    exact lift_nl ((gate_modEq_iff (by ring)).mp hw)
  · intro hs
    refine ⟨?_, ?_, ?_, wt (by dyck_mem) hs, wt (by dyck_mem) hs,
            gc (by dyck_mem) hs canon_zero, gc (by dyck_mem) hs canon_zero,
            dd (by dyck_mem) hs (by norm_num) (by norm_num)⟩
    · rw [wt (sel := SEL_BRACKET) (nc := stk 0) (lc := LANE_OP) (by dyck_mem) hs, hop]
    · rw [wt (sel := SEL_BRACKET) (nc := stk 1) (lc := LANE_S) (by dyck_mem) hs, hlS]
    · rw [wt (sel := SEL_BRACKET) (nc := stk 2) (lc := LANE_CL) (by dyck_mem) hs, hcl]
  · intro hs
    have hdd : e.loc DEPTH_NEXT = e.loc STACK_DEPTH + (-1) :=
      dd (by dyck_mem) hs (by norm_num) (by norm_num)
    refine ⟨wt (by dyck_mem) hs, wt (by dyck_mem) hs, wt (by dyck_mem) hs, wt (by dyck_mem) hs,
            ?_, by omega, by omega⟩
    · rw [wt (sel := SEL_EMPTY) (nc := stk 4) (lc := LANE_ZERO) (by dyck_mem) hs, hz]
  · intro hs
    have hdd : e.loc DEPTH_NEXT = e.loc STACK_DEPTH + (-1) :=
      dd (by dyck_mem) hs (by norm_num) (by norm_num)
    refine ⟨wt (by dyck_mem) hs, wt (by dyck_mem) hs, wt (by dyck_mem) hs, wt (by dyck_mem) hs,
            ?_, by omega, by omega⟩
    · rw [wt (sel := IS_TERM) (nc := stk 4) (lc := LANE_ZERO) (by dyck_mem) hs, hz]
  · intro hs
    have hdd : e.loc DEPTH_NEXT = e.loc STACK_DEPTH + 0 :=
      dd (by dyck_mem) hs (by norm_num) (by norm_num)
    exact ⟨wt (by dyck_mem) hs, wt (by dyck_mem) hs, wt (by dyck_mem) hs, wt (by dyck_mem) hs,
           wt (by dyck_mem) hs, by omega⟩
  · -- `INPUT_POS_P1 ≡ INPUT_POS + 1` is a FIELD relation (the helper column is not range-bounded
    -- by any deployed gate, so an ℤ equality is unprovable and would be FALSE at `INPUT_POS = p−1`);
    -- the cross-row thread then carries it to `next.INPUT_POS`. Same field-faithful reading
    -- `DerivationRefine`'s comparator teeth take.
    intro hs
    have hg := G (g := gDiffIs INPUT_POS_P1 INPUT_POS 1) (by dyck_mem)
    simp only [gDiffIs, gSub, EmittedExpr.eval] at hg
    have hp1 : e.loc INPUT_POS_P1 ≡ e.loc INPUT_POS + 1 [ZMOD 2013265921] :=
      (gate_modEq_iff (by ring)).mp hg
    have hthr := wt (sel := IS_TERM) (nc := INPUT_POS) (lc := INPUT_POS_P1) (by dyck_mem) hs
    rw [hthr]
    exact hp1
  · intro hs
    have hw := W (b := .mul (.add (.const 1) (.mul (.const (-1)) (.loc IS_TERM)))
      (wThread INPUT_POS INPUT_POS)) (by dyck_mem)
    simp only [wThread, WindowExpr.eval] at hw
    rw [hs] at hw
    norm_num at hw
    exact lift_nl ((gate_modEq_iff (by ring)).mp hw)

/-! ## §5 — Non-vacuity of the per-row bridge: a CONCRETE satisfying trace, and a rejecting one.

`dyck_sat_imp_row_valid` is worthless if its `Satisfied2` hypothesis is UNSATISFIABLE. §5 refutes
that with the honest `"[]"` parse — the exact row sequence `build_brackets_witness` lays
(`rule rBracket · term '[' · rule rEmpty · term ']' · done`, padded to 8 with `done` self-loops) —
and refutes constancy with a trace the descriptor REJECTS. -/

/-- Deciding one constraint against the trivially-false map oracle SOUNDLY implies it holds: the
`.mapOp` arm is unreachable and `dyckDesc` has no map ops anyway. -/
theorem holdsAt_of_dc2 {hash : List ℤ → ℤ} {tf : TraceFamily} {env : VmRowEnv} {f l : Bool}
    {c : VmConstraint2} (h : decideConstraint2 (fun _ _ => false) hash tf env f l c = true) :
    c.holdsAt hash tf env f l := by
  cases c with
  | base c'      => exact (decideConstraint_iff env f l c').mp h
  | lookup ll    => exact (decideLookup_iff tf env ll).mp h
  | memOp _      => exact True.intro
  | mapOp _      => exact absurd h Bool.false_ne_true
  | umemOp _     => exact True.intro
  | proofBind _  => exact True.intro
  | windowGate w => exact (decideWindow_iff env l w).mp h

/-- The whole `rowConstraints` leg from a single Boolean decision. -/
theorem witRowConstraints {hash : List ℤ → ℤ} {t : VmTrace}
    (hd : decideRowConstraints2 (fun _ _ => false) hash dyckDesc t = true) :
    ∀ i < t.rows.length, ∀ c ∈ dyckDesc.constraints,
      c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length) := by
  rw [decideRowConstraints2, List.all_eq_true] at hd
  intro i hi c hc
  have h2 := hd i (List.mem_range.mpr hi)
  rw [List.all_eq_true] at h2
  exact holdsAt_of_dc2 (h2 c hc)

/-- A row as a column-indexed list (off-the-end reads are `0`). -/
def ofList (l : List ℤ) : Assignment := fun c => l.getD c 0

/-- Row 0 — `rule rBracket` on stack `[S]`: depth `1 → 3`, tape at `0`. -/
def r0 : Assignment := ofList
  [1,0,0,0,0, 1,3, 1,0,0, 1, 0, 0,1, 1,0, 0,0, 1, 2,3,1,0]
/-- Row 1 — `term '['` on stack `[op,S,cl]`: depth `3 → 2`, tape `0 → 1`. -/
def r1 : Assignment := ofList
  [2,1,3,0,0, 3,2, 0,1,0, 0, 2, 0,1, 0,0, 0,0, 0, 2,3,1,0]
/-- Row 2 — `rule rEmpty` on stack `[S,cl]`: depth `2 → 1`, tape at `1`. -/
def r2 : Assignment := ofList
  [1,3,0,0,0, 2,1, 1,0,0, 2, 0, 1,2, 0,1, 0,0, 0, 2,3,1,0]
/-- Row 3 — `term ']'` on stack `[cl]`: depth `1 → 0`, tape `1 → 2`. -/
def r3 : Assignment := ofList
  [3,0,0,0,0, 1,0, 0,1,0, 0, 3, 1,2, 0,0, 0,0, 0, 2,3,1,0]
/-- Rows 4..7 — the accepting `done` and its self-loop padding: stack empty, tape at `2`. -/
def rD : Assignment := ofList
  [0,0,0,0,0, 0,0, 0,0,1, 0, 0, 2,3, 0,0, 0,0, 0, 2,3,1,0]

/-- **The witness**: the honest `"[]"` parse, 8 rows (5 actions + 3 `done` self-loops), with
`pi = [S, 2, 0, 0]` (initial nonterminal, input length; the two commitment PIs are out of the
model). This is `build_brackets_witness`'s row sequence, cell for cell. -/
def witTrace : VmTrace :=
  { rows := [r0, r1, r2, r3, rD, rD, rD, rD]
  , pub  := fun i => if i = 0 then 1 else if i = 1 then 2 else 0
  , tf   := fun _ => [] }

theorem witMemLog : memLog dyckDesc witTrace = [] := by rfl
theorem witMapLog : mapLog dyckDesc witTrace = [] := by rfl

/-- **`witTrace_satisfies` — the hypothesis is INHABITED.** The concrete honest `"[]"` parse is in
the deployed accept-set `Satisfied2 dyckDesc`: every selector/partition/rule-membership/top-match
gate holds on every row, every stack-threading window holds across every transition, and the
first/last boundaries pin the initial symbol, the starting depth, the accepting `done`, and the fully
consumed tape. So `dyck_sat_imp_row_valid`'s hypothesis is genuinely satisfiable — with the gate
teeth actually binding on rows 0..6. -/
theorem witTrace_satisfies :
    Satisfied2 (fun _ => (0 : ℤ)) dyckDesc (fun _ => 0) (fun _ => (0, 0)) [] witTrace := by
  refine
    { rowConstraints := ?_, rowHashes := ?_, rowRanges := ?_, memAddrsNodup := ?_,
      memClosed := ?_, memDisciplined := ?_, memBalanced := ?_, memTableFaithful := ?_,
      mapTableFaithful := ?_ }
  · exact witRowConstraints (by decide)
  · intro i _; exact True.intro
  · intro i _ r hr; exact absurd hr List.not_mem_nil
  · exact List.nodup_nil
  · intro op hop; rw [witMemLog] at hop; exact absurd hop List.not_mem_nil
  · rw [witMemLog]; decide
  · rw [witMemLog]; decide
  · rw [witMemLog]; rfl
  · rw [witMapLog]; rfl

/-- Off the end of a row's cell list, `ofList` reads `0`. -/
theorem ofList_ge {l : List ℤ} {c : Nat} (h : l.length ≤ c) : ofList l c = 0 := by
  simp only [ofList, List.getD]
  rw [List.getElem?_eq_none h]
  rfl

theorem r0_ge {c : Nat} (h : 23 ≤ c) : r0 c = 0 := ofList_ge (by simpa using h)
theorem r1_ge {c : Nat} (h : 23 ≤ c) : r1 c = 0 := ofList_ge (by simpa using h)
theorem r2_ge {c : Nat} (h : 23 ≤ c) : r2 c = 0 := ofList_ge (by simpa using h)
theorem r3_ge {c : Nat} (h : 23 ≤ c) : r3 c = 0 := ofList_ge (by simpa using h)
theorem rD_ge {c : Nat} (h : 23 ≤ c) : rD c = 0 := ofList_ge (by simpa using h)

/-- Past the 8 laid rows, the trace reads the all-zero assignment. -/
theorem wit_rows_ge {i : Nat} (h : 8 ≤ i) : witTrace.rows.getD i zeroAsg = zeroAsg := by
  simp only [witTrace, List.getD]
  rw [List.getElem?_eq_none (by simpa using h)]
  rfl

/-- Every laid cell of the witness is a small symbol id (`0..3`) — one decision over the 8×23 grid. -/
theorem wit_small : ∀ i < 8, ∀ c < 23,
    0 ≤ witTrace.rows.getD i zeroAsg c ∧ witTrace.rows.getD i zeroAsg c ≤ 3 := by decide

/-- Every cell the witness can be read at is in `[0, 3]`. -/
theorem wit_bound (i c : Nat) :
    0 ≤ witTrace.rows.getD i zeroAsg c ∧ witTrace.rows.getD i zeroAsg c ≤ 3 := by
  rcases Nat.lt_or_ge i 8 with hi | hi
  · rcases Nat.lt_or_ge c 23 with hc | hc
    · exact wit_small i hi c hc
    · have h0 : witTrace.rows.getD i zeroAsg c = 0 := by
        interval_cases i
        · exact r0_ge hc
        · exact r1_ge hc
        · exact r2_ge hc
        · exact r3_ge hc
        · exact rD_ge hc
        · exact rD_ge hc
        · exact rD_ge hc
        · exact rD_ge hc
      rw [h0]; exact ⟨le_refl 0, by norm_num⟩
  · rw [wit_rows_ge hi]; exact ⟨le_refl 0, by simp [zeroAsg]⟩

/-- **`witTrace_canon` — the envelope is genuinely INHABITED.** Every cell of the witness is a small
symbol id and both depth columns are `≤ 3`, so the range-check + depth-range envelope holds
concretely; the bridge does not rest on a vacuous hypothesis. -/
theorem witTrace_canon : DyckCanon witTrace where
  cells i c := ⟨(wit_bound i c).1, by have := (wit_bound i c).2; omega⟩
  depth i := ⟨(wit_bound i STACK_DEPTH).1, by have := (wit_bound i STACK_DEPTH).2; omega⟩
  depthNext i := ⟨(wit_bound i DEPTH_NEXT).1, by have := (wit_bound i DEPTH_NEXT).2; omega⟩

/-- **`witTrace_row_valid` — the bridge FIRES on the concrete witness (end-to-end non-vacuity).**
Row 0 of the honest `"[]"` parse is recovered as a genuine `rBracket` pushdown step. -/
theorem witTrace_row_valid : DyckRowValid (envAt witTrace 0) :=
  dyck_sat_imp_row_valid witTrace_satisfies witTrace_canon 0 (by decide)

/-- The rejecting trace: the SAME honest run with row 1's `term` reading the WRONG token — the tape
says `']'` (`3`) where the stack top is `'['` (`2`). -/
def r1Bad : Assignment := ofList
  [2,1,3,0,0, 3,2, 0,1,0, 0, 3, 0,1, 0,0, 0,0, 0, 2,3,1,0]

def witTraceBad : VmTrace := { witTrace with rows := [r0, r1Bad, r2, r3, rD, rD, rD, rD] }

/-- **`witTraceBad_not_satisfies` — the hypothesis is CONSTRAINING.** A `term` row whose consumed
token is not the stack top FAILS `Satisfied2`: the descriptor is not a constantly-true predicate, so
the accept-set genuinely discriminates real parses from fake ones. -/
theorem witTraceBad_not_satisfies :
    ¬ Satisfied2 (fun _ => (0 : ℤ)) dyckDesc (fun _ => 0) (fun _ => (0, 0)) [] witTraceBad := by
  intro h
  have hg := h.rowConstraints 1 (by decide) (cg (gGate IS_TERM (gSub (stk 0) INPUT_TOKEN)))
    (by dyck_mem)
  have hlf : (1 + 1 == witTraceBad.rows.length) = false := by decide
  simp only [cg, VmConstraint2.holdsAt, VmConstraint.holdsVm, hlf] at hg
  revert hg
  decide

/-! ### The per-row relation genuinely DISCRIMINATES (the conclusion is not a constant). -/

/-- An env whose `term` row claims a token different from the stack top. -/
def badEnv : VmRowEnv :=
  { loc := fun v => if v = IS_TERM then 1 else if v = stk 0 then 2 else if v = INPUT_TOKEN then 3
                    else 0
    nxt := fun _ => 0
    pub := fun _ => 0 }

/-- **`sem_fails`** — `DyckRowValid` is FALSIFIABLE: `badEnv`'s `term` row reads `']'` off a `'['`
top, so the relation is not constantly true and the bridge's conclusion has teeth. -/
theorem sem_fails : ¬ DyckRowValid badEnv := by
  intro h
  have := h.termTopIsToken (by decide)
  revert this
  decide

/-! ## §6 — THE MULTI-ROW ASSEMBLY: a forward run becomes a `CfgCompact.Replay`.

This is the burden `docs/DESIGN-parse-as-derivation.md` §3 names: "`derivation_sat_imp_valid` only
fires on row 0; the parse bridge is a genuine transition-relation induction across all active rows,
with the stack as the inductive invariant."

The shapes genuinely differ, which is where the content is. A trace is a FORWARD list of rows, each
carrying its own stack and remaining input, chained by a local step relation. `Replay` is a BACKWARD
inductive: its `rule` constructor builds `Replay g (r :: rs) input (nonterminal r.input :: stk)` FROM
a replay of the already-pushed stack `r.output ++ stk`. And the certificate `rs` does not exist in
the trace at all — it is RECONSTRUCTED by `rulesOf`, keeping only the rows that fire a production.
`mrun_imp_replay` is the induction that turns the former into the latter. -/

open Dregg2.Crypto.Cfg.Reference (Brk NTs dyck rBracket rEmpty)
open Dregg2.Crypto.CfgCompact (Replay ReplayAccepts)

/-- One machine action, mirroring `dyck_stack.rs::Action`. -/
inductive Act where
  | rule (r : ContextFreeRule Brk NTs)
  | term (x : Brk)
  | done
  deriving Repr

/-- One abstract row: the action it fires, the stack it reads, and the input still to consume. This
is the decoded form of a trace row (`STACK[0..D−1]` + `STACK_DEPTH` → `stk`, `INPUT_POS` → the
suffix `inp`, the selectors → `act`). -/
structure MRow where
  act : Act
  stk : List (Symbol Brk NTs)
  inp : List Brk

/-- **`MStep a b`** — the local, FORWARD transition relation between consecutive rows; the abstract
form of `DyckRowValid`'s per-action teeth:

* `rule r` — `r` is a rule of the grammar (the rule-table check / `ruleMembership`), the stack top IS
  the LHS nonterminal (`ruleTopIsS`), the next stack is the RHS pushed over the surviving REMAINDER
  (`bracketPush`'s shift, `emptyPop`'s shift-down), and the tape does not move (`nonTermHolds`).
* `term x` — the consumed token IS the stack top (`termTopIsToken`), the top pops (`termPop`), and
  the tape advances by exactly one (`termAdvances`).
* `done` — FALSE: a halted machine has no successor step. The `done` self-loop padding the circuit
  lays past the accepting row is not part of the run (see §7). -/
def MStep (a b : MRow) : Prop :=
  match a.act with
  | .rule r => r ∈ dyck.rules ∧ b.inp = a.inp ∧
      ∃ rest, a.stk = Symbol.nonterminal r.input :: rest ∧ b.stk = r.output ++ rest
  | .term x => a.inp = x :: b.inp ∧ ∃ rest, a.stk = Symbol.terminal x :: rest ∧ b.stk = rest
  | .done => False

/-- **`MFinal a`** — the accepting halt: a `done` row with an EMPTY stack and a FULLY consumed tape
(`doneEmpty` at `STACK_DEPTH = 0`, plus the last-row `INPUT_POS = pi[INPUT_LEN]` boundary). -/
def MFinal (a : MRow) : Prop := a.act = Act.done ∧ a.stk = [] ∧ a.inp = []

/-- **`MRun a rest`** — a forward run STARTING at row `a` and continuing through `rest`:
consecutive rows are `MStep`-linked and the last row accepts (`MFinal`). -/
inductive MRun : MRow → List MRow → Prop
  | last {a : MRow} (h : MFinal a) : MRun a []
  | step {a b : MRow} {rest : List MRow} (h : MStep a b) : MRun b rest → MRun a (b :: rest)

/-- **`rulesOf`** — the compact certificate RECONSTRUCTED from the rows: the productions the `rule`
rows fire, in order. `term`/`done` rows contribute nothing. This is the object `CfgCompact` calls the
O(tokens) wire form; the trace never stores it. -/
def rulesOf : List MRow → List (ContextFreeRule Brk NTs)
  | [] => []
  | a :: rest => match a.act with
    | .rule r => r :: rulesOf rest
    | _ => rulesOf rest

/-- **`mrun_imp_replay` — THE ASSEMBLY (the design's named hard part).** A forward-indexed run of
per-row-valid pushdown steps ending in an accepting `done` IS a `CfgCompact.Replay` of the Dyck
grammar: from the head row's stack, the RECONSTRUCTED rule sequence drives a complete consumption of
the head row's input.

The induction runs along the row list with the STACK as the invariant. Each `rule` row discharges the
`Replay.rule` constructor by handing it the SUCCESSOR row's stack — which the step relation forces to
be exactly `r.output ++ rest`, the shape `Replay.rule` demands — and each `term` row discharges
`Replay.term` against the tape suffix the step relation peels. The `done` row is the base case, where
`MFinal` supplies the empty stack and the empty tape `Replay.done` needs. The forward list and the
backward inductive are genuinely different objects, and the certificate is reconstructed, not
supplied: that is the content. -/
theorem mrun_imp_replay {a : MRow} {rest : List MRow} (h : MRun a rest) :
    Replay dyck (rulesOf (a :: rest)) a.inp a.stk := by
  induction h with
  | @last a hfin =>
    obtain ⟨hact, hstk, hinp⟩ := hfin
    rw [hstk, hinp]
    have hr : rulesOf [a] = [] := by simp only [rulesOf, hact]
    rw [hr]
    exact Replay.done
  | @step a b rest hstep hrun ih =>
    revert hstep
    cases hact : a.act with
    | rule r =>
      intro hstep
      simp only [MStep, hact] at hstep
      obtain ⟨hr, hinp, rest', hstk, hstk'⟩ := hstep
      have hrules : rulesOf (a :: b :: rest) = r :: rulesOf (b :: rest) := by
        simp only [rulesOf, hact]
      rw [hrules, hstk]
      refine Replay.rule hr ?_
      rw [hstk', hinp] at ih
      exact ih
    | term x =>
      intro hstep
      simp only [MStep, hact] at hstep
      obtain ⟨hinp, rest', hstk, hstk'⟩ := hstep
      have hrules : rulesOf (a :: b :: rest) = rulesOf (b :: rest) := by
        simp only [rulesOf, hact]
      rw [hrules, hstk, hinp]
      refine Replay.term x ?_
      rw [hstk'] at ih
      exact ih
    | done =>
      -- a halted machine has no successor step: `MStep .done` is FALSE by construction, so the
      -- `done` self-loop padding the circuit lays past the accepting row is not part of a run.
      intro hstep
      simp only [MStep, hact] at hstep

/-! ### §6.1 — Non-vacuity of the assembly, ON THE CIRCUIT'S OWN WITNESS.

The rows below are `build_brackets_witness`'s action sequence, one for one, with the stack/tape each
row carries — the SAME machine `witTrace` (§5) encodes in columns. Running them through
`mrun_imp_replay` reproduces `CfgCompact.Reference.brackets_replays`'s exact statement, so the
assembly is a genuine route to the semantic target and not an unsatisfiable envelope. -/

open Dregg2.Crypto.Cfg.Reference.Brk (op cl)

/-- The first row of the abstract `"[]"` run: `rule rBracket` on the initial stack `[S]`. -/
def bRow0 : MRow := ⟨.rule rBracket, [Symbol.nonterminal NTs.S], [op, cl]⟩

/-- The rest: `term '[' · rule rEmpty · term ']' · done`. -/
def bracketsRest : List MRow :=
  [ ⟨.term op, [Symbol.terminal op, Symbol.nonterminal NTs.S, Symbol.terminal cl], [op, cl]⟩
  , ⟨.rule rEmpty, [Symbol.nonterminal NTs.S, Symbol.terminal cl], [cl]⟩
  , ⟨.term cl, [Symbol.terminal cl], [cl]⟩
  , ⟨.done, [], []⟩ ]

/-- The row list IS an `MRun`: each consecutive pair is a legal step and the last row accepts. -/
theorem bracketsRows_run : MRun bRow0 bracketsRest := by
  refine MRun.step ?_ (MRun.step ?_ (MRun.step ?_ (MRun.step ?_ (MRun.last ?_))))
  · exact ⟨by simp only [dyck]; exact Finset.mem_insert_self _ _, rfl, [], rfl, by simp [rBracket]⟩
  · exact ⟨rfl, [Symbol.nonterminal NTs.S, Symbol.terminal cl], rfl, rfl⟩
  · exact ⟨by simp only [dyck]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _), rfl,
      [Symbol.terminal cl], rfl, by simp [rEmpty]⟩
  · exact ⟨rfl, [], rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

/-- The reconstructed certificate IS the two-rule compact certificate. -/
theorem rulesOf_brackets : rulesOf (bRow0 :: bracketsRest) = [rBracket, rEmpty] := by
  simp only [bracketsRest, bRow0, rulesOf]

/-- **`abs_brackets_accepts` — the assembly reaches the semantic target.** Feeding the circuit's own
`"[]"` action sequence through `mrun_imp_replay` yields EXACTLY the statement the hand proof
`CfgCompact.Reference.brackets_replays` establishes — reached here from a forward row list, through
the induction, with the rule sequence reconstructed rather than supplied. -/
theorem abs_brackets_accepts : ReplayAccepts dyck [rBracket, rEmpty] [op, cl] := by
  have h := mrun_imp_replay bracketsRows_run
  rw [rulesOf_brackets] at h
  exact h

/-- And therefore the parse certifies LANGUAGE MEMBERSHIP through the proven `CfgCompact` stack —
the composition `docs/DESIGN-parse-as-derivation.md` §3 names as the payoff. -/
theorem abs_brackets_in_language : [op, cl] ∈ dyck.language :=
  Dregg2.Crypto.CfgCompact.compact_sound dyck [rBracket, rEmpty] [op, cl] abs_brackets_accepts

/-! ## §7 — THE RESIDUAL (named, not `sorry`ed).

`parse_sat_imp_replay` — `Satisfied2 dyckDesc … t → Replay dyck (rulesOf t) (inputOf t)
[Symbol.nonterminal dyck.initial]` — is NOT proven here. Two proven halves stand:

  (§4.1)  Satisfied2 dyckDesc t  →  ∀ transition row i, DyckRowValid (envAt t i)
  (§6)    MRun rows              →  Replay dyck (rulesOf rows) rows.head.inp rows.head.stk

and the seam between them is ONE function plus ONE invariant:

* **`decode : VmTrace → List MRow`** — read each row's `STACK[0..D−1]` cells + `STACK_DEPTH` into a
  `List (Symbol Brk NTs)` (`1 ↦ nonterminal S`, `2 ↦ terminal op`, `3 ↦ terminal cl`, `0 ↦` absent),
  the selectors + `RULE_ID` into an `Act`, and `INPUT_POS` into the remaining-input suffix; then
  TRUNCATE at the first `done` row (the circuit pads with `done` self-loops, which `MStep .done`
  refuses by construction).
* **`DyckRowValid (envAt t i) → MStep (decode t)[i] (decode t)[i+1]`** — the per-row teeth already
  give every cell equation this needs. What it additionally needs is the **depth↔occupancy
  invariant**: that `STACK_DEPTH` counts exactly the non-`EMPTY` prefix of the cells. `dyck_stack.rs`
  states plainly that this does not exist yet ("nothing yet ties `STACK_DEPTH` to which cells are
  nonzero; the boundaries and the per-action depth deltas pin the endpoints, not every intermediate
  cell"). Without it, `decode`'s stack length and the depth column can disagree, and the shift
  equations do not compose into `b.stk = r.output ++ rest`.

So the honest ordering is: land the depth↔occupancy constraint in the CIRCUIT first (it is a real
missing tooth, not a proof inconvenience — see the lane findings), then `decode` + the glue lemma
close `parse_sat_imp_replay` by composing the two halves above. -/

#assert_axioms dyck_sat_imp_row_valid
#assert_axioms witTrace_satisfies
#assert_axioms witTrace_canon
#assert_axioms witTrace_row_valid
#assert_axioms witTraceBad_not_satisfies
#assert_axioms sem_fails
#assert_axioms mrun_imp_replay
#assert_axioms bracketsRows_run
#assert_axioms abs_brackets_accepts
#assert_axioms abs_brackets_in_language

end Dregg2.Circuit.Emit.DyckStackRefine
