/-
# Dregg2.Crypto.AbstractMachine — the forward pushdown-run layer (`MRow`/`MStep`/`MRun`), BELOW
both the circuit refinement and the certificate rung.

## Why this module exists (the layering fix)

`Circuit/Emit/DyckStackRefine.lean` §6 defined the abstract pushdown machine — a FORWARD row list
chained by a local step relation, with the compact certificate RECONSTRUCTED from the rows — and
proved the multi-row assembly `mrun_imp_replay`. `Crypto/ReplayAsCert.lean` then imported the
CIRCUIT file to state its subsumption theorems against the REAL `MRun`/`MStep`/`rulesOf`: a
Crypto←Circuit import (no cycle, but a layering inversion — the machine carries NO circuit-specific
content, so nothing about it belongs above the Crypto layer).

This module is the extraction: everything here is pure Crypto-layer material (the Dyck reference
grammar `Cfg.Reference.dyck` + `CfgCompact.Replay`), moved VERBATIM from `DyckStackRefine` §6/§6.1.
Both `DyckStackRefine` (which re-exports every name into its namespace, so all downstream
statements are unchanged) and `ReplayAsCert` now import DOWNWARD onto this file, and the inversion
is gone.

## Contents (the former §6/§6.1, statement-for-statement)

* `Act`/`MRow` — one decoded trace row: the action it fires, the stack it reads, the input still to
  consume.
* `MStep`/`MFinal`/`MRun` — the local forward transition relation, the accepting halt, and a run.
* `rulesOf` — the compact certificate RECONSTRUCTED from the rows.
* `mrun_imp_replay` — THE ASSEMBLY (the design's named hard multi-row induction, stack as the
  invariant): a forward run IS a `CfgCompact.Replay`.
* `bRow0`/`bracketsRest`/`bracketsRows_run`/`rulesOf_brackets`/`abs_brackets_accepts`/
  `abs_brackets_in_language` — non-vacuity ON THE CIRCUIT'S OWN `"[]"` action sequence
  (`build_brackets_witness`'s rows, one for one).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}, as in the source file.
-/
import Dregg2.Crypto.CfgCompact
import Dregg2.Tactics

namespace Dregg2.Crypto.AbstractMachine

open Dregg2.Crypto.Cfg.Reference (Brk NTs dyck rBracket rEmpty)
open Dregg2.Crypto.CfgCompact (Replay ReplayAccepts)

set_option autoImplicit false

/-! ## The machine: a forward run becomes a `CfgCompact.Replay`.

This is the burden `docs/DESIGN-parse-as-derivation.md` §3 names: "`derivation_sat_imp_valid` only
fires on row 0; the parse bridge is a genuine transition-relation induction across all active rows,
with the stack as the inductive invariant."

The shapes genuinely differ, which is where the content is. A trace is a FORWARD list of rows, each
carrying its own stack and remaining input, chained by a local step relation. `Replay` is a BACKWARD
inductive: its `rule` constructor builds `Replay g (r :: rs) input (nonterminal r.input :: stk)` FROM
a replay of the already-pushed stack `r.output ++ stk`. And the certificate `rs` does not exist in
the trace at all — it is RECONSTRUCTED by `rulesOf`, keeping only the rows that fire a production.
`mrun_imp_replay` is the induction that turns the former into the latter. -/

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
  lays past the accepting row is not part of the run. -/
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

/-! ### Non-vacuity of the assembly, ON THE CIRCUIT'S OWN WITNESS.

The rows below are `build_brackets_witness`'s action sequence, one for one, with the stack/tape each
row carries — the SAME machine `DyckStackRefine.witTrace` encodes in columns. Running them through
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

#assert_axioms mrun_imp_replay
#assert_axioms bracketsRows_run
#assert_axioms rulesOf_brackets
#assert_axioms abs_brackets_accepts
#assert_axioms abs_brackets_in_language

end Dregg2.Crypto.AbstractMachine
