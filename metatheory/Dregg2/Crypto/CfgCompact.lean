/-
# Dregg2.Crypto.CfgCompact — the COMPACT parse certificate: a leftmost rule sequence.

`Cfg.lean`'s certificate is the derivation FORM-CHAIN — every sentential form the derivation
passes through. That object is O(tokens²) symbols: the forms are recomputable from the rule
sequence, so storing them is pure redundancy (and a measured resource-blowup on structure-dense
inputs; see `docs/deos/ZKORACLE-PROVER-STATUS.md` "Measured paces").

This module is the O(tokens) wire form: the certificate is just the LEFTMOST derivation's rule
sequence, and the verifier REPLAYS it as a pushdown run — a stack starts at `[initial]`; a
terminal on top must match the next input token; a nonterminal on top consumes the next rule
(whose lhs must equal it) and pushes its rhs. `Replay` is that machine as an inductive.

    replay_derives   : Replay g rs input stk → g.Derives stk (input.map .terminal)
    compact_sound    : ReplayAccepts g rs input → input ∈ g.language
    compact_to_chain : ReplayAccepts g rs input → ∃ chain, CfgAccepts g input chain

`compact_to_chain` is the tie-back: an accepted replay yields exactly the `CfgAccepts` object
the capstone (`ZkOracle.lean`) consumes — the compact form changes the WIRE, not the theorem.
The Rust twin is `zkoracle-prove/src/cfg.rs::{CompactCert, verify_cfg_compact, expand_compact}`.

Direction honesty: SOUNDNESS (verifier accepts ⇒ language membership) is the load-bearing
security direction and is proven here. Prover-side completeness (every well-formed input has a
replaying rule sequence) is witnessed constructively by the Rust prover and its equivalence
tests (`compact_expands_to_the_exact_chain`), not restated as a Lean theorem.
-/
import Mathlib.Computability.ContextFreeGrammar
import Dregg2.Crypto.Cfg
import Dregg2.Tactics

namespace Dregg2.Crypto.CfgCompact

open ContextFreeGrammar
open Dregg2.Crypto.Cfg

variable {T : Type}

/-- **The pushdown replay** of a compact certificate (a leftmost rule sequence `rs`) against
`input`, with working stack `stk`:

* `done` — rules and input both exhausted as the stack empties: ACCEPT.
* `term` — a terminal on top of the stack consumes the matching next input token.
* `rule` — a nonterminal on top consumes the next certificate rule `r ∈ g.rules` whose lhs
  is that nonterminal, and pushes `r.output`.

`Replay g rs input stk` reads: from stack `stk`, the rule sequence `rs` drives a complete,
accepting consumption of `input`. -/
inductive Replay (g : ContextFreeGrammar T) :
    List (ContextFreeRule T g.NT) → List T → List (Symbol T g.NT) → Prop
  | done : Replay g [] [] []
  | term {rs : List (ContextFreeRule T g.NT)} {input : List T} {stk : List (Symbol T g.NT)}
      (t : T) : Replay g rs input stk → Replay g rs (t :: input) (Symbol.terminal t :: stk)
  | rule {r : ContextFreeRule T g.NT} {rs : List (ContextFreeRule T g.NT)} {input : List T}
      {stk : List (Symbol T g.NT)} (hr : r ∈ g.rules) :
      Replay g rs input (r.output ++ stk) →
      Replay g (r :: rs) input (Symbol.nonterminal r.input :: stk)

/-- **`ReplayAccepts g rs input`** — the compact certificate's accepting bit: the replay from
the initial stack `[.nonterminal g.initial]` consumes all of `input` and all of `rs`. -/
def ReplayAccepts (g : ContextFreeGrammar T) (rs : List (ContextFreeRule T g.NT))
    (input : List T) : Prop :=
  Replay g rs input [Symbol.nonterminal g.initial]

/-- **The replay invariant** — from any state, an accepting replay means the current stack
DERIVES the remaining input word: each `rule` step is one `Produces` at the head (leftmost)
and each `term` step is `Derives.append_left` under the matched terminal. -/
theorem replay_derives {g : ContextFreeGrammar T}
    {rs : List (ContextFreeRule T g.NT)} {input : List T} {stk : List (Symbol T g.NT)}
    (h : Replay g rs input stk) : g.Derives stk (input.map Symbol.terminal) := by
  induction h with
  | done => exact Relation.ReflTransGen.refl
  | term t _ ih =>
    simpa using ih.append_left [Symbol.terminal t]
  | rule hr _ ih =>
    refine Produces.trans_derives ⟨_, hr, ?_⟩ ih
    simpa using ContextFreeRule.rewrites_of_exists_parts _ [] _

/-- **`compact_sound`** — the compact certificate's soundness: an accepted replay proves the
input is in the grammar's language. The O(tokens) verifier certifies the SAME fact the
form-chain verifier does. -/
theorem compact_sound (g : ContextFreeGrammar T) (rs : List (ContextFreeRule T g.NT))
    (input : List T) (h : ReplayAccepts g rs input) : input ∈ g.language := by
  rw [mem_language_iff]
  exact replay_derives h

/-- **`compact_to_chain`** — the tie-back to `Cfg.lean`'s object: an accepted replay yields a
full `CfgAccepts` derivation chain (via the bridge), so everything downstream that consumes
`CfgAccepts` (the capstone composition) is untouched by the wire-format change. The Rust twin
is `expand_compact`. -/
theorem compact_to_chain (g : ContextFreeGrammar T) (rs : List (ContextFreeRule T g.NT))
    (input : List T) (h : ReplayAccepts g rs input) :
    ∃ chain, CfgAccepts g input chain :=
  (cfg_bridge g input).mpr (compact_sound g rs input h)

#assert_axioms replay_derives
#assert_axioms compact_sound
#assert_axioms compact_to_chain

/-! ## Non-vacuity — both poles, on the Dyck reference grammar.

The accepting pole: the two-rule sequence `[rBracket, rEmpty]` replays `"[]"` — the compact
certificate is 2 rules where `Cfg.lean`'s `bracketsChain` stores 3 full forms. The rejecting
pole: an empty rule sequence cannot replay a non-empty input. -/

namespace Reference

open Dregg2.Crypto.Cfg.Reference Brk

/-- The accepting pole: `[rBracket, rEmpty]` replays `"[]"` from the initial stack —
`S ⟹ [S] ⟹ []` as a pushdown run: rule, match `[`, rule, match `]`, done. -/
theorem brackets_replays : ReplayAccepts dyck [rBracket, rEmpty] [op, cl] := by
  refine Replay.rule ?_ ?_
  · simp only [dyck]; exact Finset.mem_insert_self _ _
  · show Replay dyck [rEmpty] [op, cl]
      [Symbol.terminal op, Symbol.nonterminal NTs.S, Symbol.terminal cl]
    refine Replay.term op ?_
    refine Replay.rule ?_ ?_
    · simp only [dyck]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · show Replay dyck [] [cl] [Symbol.terminal cl]
      exact Replay.term cl Replay.done

/-- Non-vacuity of `compact_sound`: the 2-rule compact certificate proves
`[op, cl] ∈ dyck.language` — the same membership `Cfg.lean` reaches through the 3-form chain. -/
theorem brackets_in_language_compact : [op, cl] ∈ dyck.language :=
  compact_sound dyck [rBracket, rEmpty] [op, cl] brackets_replays

/-- The rejecting pole: an EMPTY rule sequence cannot replay a non-empty input — the initial
nonterminal needs a rule, and none is supplied. The verifier's refusal is not vacuous. -/
theorem empty_rules_refused : ¬ ReplayAccepts dyck [] [op, cl] := by
  intro h
  cases h

#assert_axioms brackets_replays
#assert_axioms brackets_in_language_compact
#assert_axioms empty_rules_refused

end Reference

end Dregg2.Crypto.CfgCompact
