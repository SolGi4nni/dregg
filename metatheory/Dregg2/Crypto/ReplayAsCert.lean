/-
# Dregg2.Crypto.ReplayAsCert — the CF-MACHINE rung: the pushdown replay as a `Hypergraph.Cert`.

The substrate ladder so far: regular acceptance is `Hypergraph.Cert delta` (`DfaAsCert`), visibly-
pushdown acceptance is `Cert R_vpa` (`VpaAsCert`), and context-free GRAMMAR derivation is
`Cert g.Produces` (`Hypergraph.cfg_parse_via_reduction`). What was missing is the context-free
MACHINE: `CfgCompact.Replay` — the pushdown verifier that replays a compact certificate — was its
own bespoke inductive, not yet expressed on the substrate. This file closes that rung:

    ReplayStep g        : Config g → Config g → Prop  (one pushdown move over (rules, input, stack))
    replay_iff_reflTransGen : Replay g rs input stk ↔ ReflTransGen (ReplayStep g) (rs,input,stk) ([],[],[])
    replay_as_cert      : Replay g rs input stk ↔ ∃ c, Hypergraph.Cert (ReplayStep g) (rs,input,stk) ([],[],[]) c

so the pushdown MACHINE run is the SAME chain-certificate object as the DFA run, the VPA run, and
the grammar derivation — four rungs, one `Hypergraph.bridge`, differing only in the relation `R`.

## The subsumption payoff

`AbstractMachine.mrun_imp_replay` — the design's named hard multi-row induction ("forward trace of
per-row-valid pushdown steps ⇒ backward `Replay` inductive, certificate RECONSTRUCTED by
`rulesOf`"; stated by the circuit refinement as `DyckStackRefine.mrun_imp_replay`, which re-exports
the SAME declaration) — is an INSTANCE of the generic `Hypergraph.Cert.foldSound` at
`out := rowRules` (a `rule` row contributes `[r]`, others `[]`) and
`Sem rs row := Replay dyck rs row.inp row.stk`. `mrun_imp_replay_via_fold` below re-derives the
IDENTICAL statement through the generic fold: the bespoke induction's content splits into

  * `mrun_cert`   — an `MRun` IS a chain certificate over `MStep` ending in an `MFinal` row
                    (run-shape, no pushdown content), and
  * `mstep_step`  — ONE local step is sound for prepending (the per-row content the machine layer
                    already isolated in `MStep`),

and `Cert.foldSound` supplies the whole multi-row induction. `subsumption_stmt_eq` checks (by
elaboration) that the statement types coincide — the generic fold genuinely subsumes the bespoke
proof, which stays untouched in `AbstractMachine`.

(The machine layer `MRow`/`MStep`/`MRun`/`rulesOf` used to live in
`Circuit/Emit/DyckStackRefine.lean` §6, and this file imported the CIRCUIT module to state the
subsumption against the real defs — a Crypto←Circuit layering inversion. The layer carries no
circuit-specific content, so it was extracted DOWN into `Dregg2.Crypto.AbstractMachine`; both this
file and `DyckStackRefine` now import it downward, and the inversion is gone.)
-/
import Dregg2.Crypto.CfgCompact
import Dregg2.Crypto.Hypergraph
import Dregg2.Crypto.AbstractMachine
import Dregg2.Tactics

namespace Dregg2.Crypto.ReplayAsCert

open ContextFreeGrammar
open Dregg2.Crypto
open Dregg2.Crypto.CfgCompact (Replay ReplayAccepts)

variable {T : Type}

/-! ## The machine-step relation — one pushdown move over full configurations. -/

/-- A pushdown-replay configuration: the remaining certificate rules, the remaining input, and the
working stack — the full state `CfgCompact.Replay` threads through its constructors. -/
abbrev Config (g : ContextFreeGrammar T) :=
  List (ContextFreeRule T g.NT) × List T × List (Symbol T g.NT)

/-- **`ReplayStep g`** — ONE move of the compact-certificate pushdown verifier, as a reduction
relation over configurations. Constructor for constructor with `CfgCompact.Replay`'s recursive
cases, read FORWARD:

* `term` — a terminal on top of the stack consumes the matching next input token;
* `rule` — a nonterminal on top consumes the next certificate rule `r ∈ g.rules` (whose lhs is
  that nonterminal) and pushes `r.output`.

`Replay`'s `done` is not a step: it is the accepting HALT `([], [], [])`, the fixed goal
configuration of the certificate. -/
inductive ReplayStep (g : ContextFreeGrammar T) : Config g → Config g → Prop
  | term {rs : List (ContextFreeRule T g.NT)} {input : List T} {stk : List (Symbol T g.NT)}
      (t : T) :
      ReplayStep g (rs, t :: input, Symbol.terminal t :: stk) (rs, input, stk)
  | rule {r : ContextFreeRule T g.NT} {rs : List (ContextFreeRule T g.NT)} {input : List T}
      {stk : List (Symbol T g.NT)} (hr : r ∈ g.rules) :
      ReplayStep g (r :: rs, input, Symbol.nonterminal r.input :: stk)
        (rs, input, r.output ++ stk)

/-- A replay unrolls to a reflexive-transitive `ReplayStep` reduction down to the halt
configuration: each `Replay` constructor is one `ReflTransGen.head`. -/
theorem replay_imp_reflTransGen {g : ContextFreeGrammar T}
    {rs : List (ContextFreeRule T g.NT)} {input : List T} {stk : List (Symbol T g.NT)}
    (h : Replay g rs input stk) :
    Relation.ReflTransGen (ReplayStep g) (rs, input, stk) ([], [], []) := by
  induction h with
  | done => exact Relation.ReflTransGen.refl
  | term t _ ih => exact Relation.ReflTransGen.head (ReplayStep.term t) ih
  | rule hr _ ih => exact Relation.ReflTransGen.head (ReplayStep.rule hr) ih

/-- A reflexive-transitive `ReplayStep` reduction to the halt configuration rebuilds the `Replay`:
head-induction, folding each machine move back into the matching `Replay` constructor. -/
theorem reflTransGen_imp_replay {g : ContextFreeGrammar T} {cfg : Config g}
    (h : Relation.ReflTransGen (ReplayStep g) cfg ([], [], [])) :
    Replay g cfg.1 cfg.2.1 cfg.2.2 := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Replay.done
  | @head a c hstep _htail ih =>
    cases hstep with
    | term t => exact Replay.term t ih
    | rule hr => exact Replay.rule hr ih

/-- **`replay_iff_reflTransGen`** — the pushdown replay IS the reflexive-transitive closure of the
machine-step relation, from the start configuration down to the accepting halt. -/
theorem replay_iff_reflTransGen (g : ContextFreeGrammar T)
    (rs : List (ContextFreeRule T g.NT)) (input : List T) (stk : List (Symbol T g.NT)) :
    Replay g rs input stk ↔
      Relation.ReflTransGen (ReplayStep g) (rs, input, stk) ([], [], []) :=
  ⟨replay_imp_reflTransGen, fun h => reflTransGen_imp_replay (cfg := (rs, input, stk)) h⟩

/-- **`replay_as_cert`** — THE CF-MACHINE RUNG. A pushdown replay holds IFF a locally-checkable
`Hypergraph.Cert` chain over `ReplayStep` exists from the start configuration to the halt: the
context-free MACHINE joins the substrate that already carries the DFA (`DfaAsCert.delta`), the VPA
(`VpaAsCert`), and the CF grammar (`cfg_parse_via_reduction`) — one `Hypergraph.bridge`, four
relations. -/
theorem replay_as_cert (g : ContextFreeGrammar T)
    (rs : List (ContextFreeRule T g.NT)) (input : List T) (stk : List (Symbol T g.NT)) :
    Replay g rs input stk ↔
      ∃ c, Hypergraph.Cert (ReplayStep g) (rs, input, stk) ([], [], []) c :=
  (replay_iff_reflTransGen g rs input stk).trans (Hypergraph.bridge _ _ _).symm

/-- The accepting form: `ReplayAccepts` is the certificate from the INITIAL configuration
(`[.nonterminal g.initial]` stack, full rules + input) to the halt. -/
theorem replayAccepts_as_cert (g : ContextFreeGrammar T)
    (rs : List (ContextFreeRule T g.NT)) (input : List T) :
    ReplayAccepts g rs input ↔
      ∃ c, Hypergraph.Cert (ReplayStep g)
        (rs, input, [Symbol.nonterminal g.initial]) ([], [], []) c :=
  replay_as_cert g rs input [Symbol.nonterminal g.initial]

#assert_axioms replay_imp_reflTransGen
#assert_axioms reflTransGen_imp_replay
#assert_axioms replay_iff_reflTransGen
#assert_axioms replay_as_cert
#assert_axioms replayAccepts_as_cert

/-! ## The subsumption — `DyckStackRefine.mrun_imp_replay` is a `Cert.foldSound` instance.

`MRun`'s forward row list is a chain certificate over `MStep` (`mrun_cert`); one row's soundness
for prepending is `mstep_step`; `Cert.foldSound` at `out := rowRules`,
`Sem rs row := Replay dyck rs row.inp row.stk` is the whole multi-row induction. -/

section Subsumption

open Dregg2.Crypto.AbstractMachine
open Dregg2.Crypto.Cfg.Reference (Brk NTs dyck rBracket rEmpty)

/-- The `out` of the fold: a `rule` row contributes its production to the reconstructed wire
certificate; `term`/`done` rows contribute nothing. `rulesOf` is its `flatMap`
(`rulesOf_eq_flatMap`). -/
def rowRules (row : MRow) : List (ContextFreeRule Brk NTs) :=
  match row.act with
  | .rule r => [r]
  | _ => []

/-- `DyckStackRefine.rulesOf` IS the `flatMap` of the per-row output — the reconstructed compact
certificate is the fold's accumulated output. -/
theorem rulesOf_eq_flatMap : ∀ rows : List MRow, rulesOf rows = rows.flatMap rowRules := by
  intro rows
  induction rows with
  | nil => rfl
  | cons a rest ih =>
    cases hact : a.act with
    | rule r => simp [rulesOf, rowRules, hact, ih]
    | term x => simp [rulesOf, rowRules, hact, ih]
    | done => simp [rulesOf, rowRules, hact, ih]

/-- ONE row is sound for prepending — the per-step content of the assembly, exactly `MStep`'s three
cases folded into `Replay`'s two recursive constructors (`done` steps are impossible). This is the
`hstep` hypothesis `Cert.foldSound` consumes. -/
theorem mstep_step (a b : MRow) (hstep : MStep a b) (rs : List (ContextFreeRule Brk NTs))
    (hsem : Replay dyck rs b.inp b.stk) : Replay dyck (rowRules a ++ rs) a.inp a.stk := by
  revert hstep
  cases hact : a.act with
  | rule r =>
    intro hstep
    simp only [MStep, hact] at hstep
    obtain ⟨hr, hinp, rest, hstka, hstkb⟩ := hstep
    have hout : rowRules a = [r] := by simp [rowRules, hact]
    rw [hout, hstka]
    refine Replay.rule hr ?_
    rw [hstkb, hinp] at hsem
    exact hsem
  | term t =>
    intro hstep
    simp only [MStep, hact] at hstep
    obtain ⟨hinp, rest, hstka, hstkb⟩ := hstep
    have hout : rowRules a = [] := by simp [rowRules, hact]
    rw [hout, hstka, hinp]
    refine Replay.term t ?_
    rw [hstkb] at hsem
    exact hsem
  | done =>
    intro hstep
    simp only [MStep, hact] at hstep

/-- An `MRun` IS a chain certificate over `MStep` from its head row to some `MFinal` row — the
run-shape half of the assembly, with no pushdown content at all. -/
theorem mrun_cert : ∀ {a : MRow} {rest : List MRow}, MRun a rest →
    ∃ last, Hypergraph.Cert MStep a last (a :: rest) ∧ MFinal last := by
  intro a rest h
  induction h with
  | @last a hfin => exact ⟨a, ⟨rfl, rfl, trivial⟩, hfin⟩
  | @step a b rest hstep _hrun ih =>
    obtain ⟨last, ⟨_hhead, hlast, hchain⟩, hfin⟩ := ih
    refine ⟨last, ⟨rfl, ?_, hstep, hchain⟩, hfin⟩
    rw [List.getLast?_cons_cons]
    exact hlast

/-- **`mrun_imp_replay_via_fold`** — the IDENTICAL statement of
`DyckStackRefine.mrun_imp_replay`, re-derived through the generic `Hypergraph.Cert.foldSound`:
the run is a chain certificate (`mrun_cert`), one step prepends soundly (`mstep_step`), the
`MFinal` row replays to `done`, and the generic fold does the entire multi-row induction. The
bespoke proof in `DyckStackRefine` §6 is an instance of the substrate's one fold lemma. -/
theorem mrun_imp_replay_via_fold {a : MRow} {rest : List MRow} (h : MRun a rest) :
    Replay dyck (rulesOf (a :: rest)) a.inp a.stk := by
  obtain ⟨last, hcert, hact, hstk, hinp⟩ := mrun_cert h
  have hbase : Replay dyck (rowRules last) last.inp last.stk := by
    have hout : rowRules last = [] := by simp [rowRules, hact]
    rw [hout, hstk, hinp]
    exact Replay.done
  have hfold := Hypergraph.Cert.foldSound rowRules
    (fun rs row => Replay dyck rs row.inp row.stk)
    (fun x y hxy rs hs => mstep_step x y hxy rs hs) hcert hbase
  rw [rulesOf_eq_flatMap]
  exact hfold

/-- The statements coincide — this elaborates ONLY because `mrun_imp_replay_via_fold`'s type is
(definitionally) the type of `AbstractMachine.mrun_imp_replay` (the SAME declaration
`DyckStackRefine.mrun_imp_replay` re-exports): the generic fold derivation proves the same theorem
the bespoke induction proves. -/
theorem subsumption_stmt_eq :
    (∀ {a : MRow} {rest : List MRow}, MRun a rest →
      Replay dyck (rulesOf (a :: rest)) a.inp a.stk) :=
  @Dregg2.Crypto.AbstractMachine.mrun_imp_replay

#assert_axioms rulesOf_eq_flatMap
#assert_axioms mstep_step
#assert_axioms mrun_cert
#assert_axioms mrun_imp_replay_via_fold

end Subsumption

/-! ## Non-vacuity — both poles on the Dyck reference, and the fold route reaches §6.1's target. -/

namespace Reference

open Dregg2.Crypto.Cfg.Reference Brk
open Dregg2.Crypto.AbstractMachine (bRow0 bracketsRest bracketsRows_run rulesOf_brackets)

/-- The accepting pole: the genuine 2-rule replay of `"[]"`
(`CfgCompact.Reference.brackets_replays`) yields, through the rung, a genuine machine-step chain
certificate from the initial configuration to the halt. -/
theorem brackets_cert :
    ∃ c, Hypergraph.Cert (ReplayStep dyck)
      ([rBracket, rEmpty], [op, cl], [Symbol.nonterminal dyck.initial]) ([], [], []) c :=
  (replayAccepts_as_cert dyck [rBracket, rEmpty] [op, cl]).mp
    Dregg2.Crypto.CfgCompact.Reference.brackets_replays

/-- The rejecting pole: NO machine-step chain certificate exists for the empty rule sequence
against a non-empty input — the rung's refusal is `CfgCompact`'s refusal, not vacuous. -/
theorem empty_rules_no_cert :
    ¬ ∃ c, Hypergraph.Cert (ReplayStep dyck)
      (([] : List (ContextFreeRule Brk NTs)), [op, cl], [Symbol.nonterminal dyck.initial])
      ([], [], []) c :=
  fun h => Dregg2.Crypto.CfgCompact.Reference.empty_rules_refused
    ((replayAccepts_as_cert dyck [] [op, cl]).mpr h)

/-- The fold route reaches §6.1's semantic target: feeding the circuit's own `"[]"` row list
through `mrun_imp_replay_via_fold` reproduces EXACTLY the statement of
`DyckStackRefine.abs_brackets_accepts` — the generic fold is a genuine route to the same
acceptance, not an unsatisfiable envelope. -/
theorem via_fold_brackets_accepts : ReplayAccepts dyck [rBracket, rEmpty] [op, cl] := by
  have h := mrun_imp_replay_via_fold bracketsRows_run
  rw [rulesOf_brackets] at h
  exact h

#assert_axioms brackets_cert
#assert_axioms empty_rules_no_cert
#assert_axioms via_fold_brackets_accepts

end Reference

end Dregg2.Crypto.ReplayAsCert
