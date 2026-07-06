/-
# Dregg2.Crypto.Cfg — §8 discharge: context-free parse-certificate acceptance.

The DFA cascade (`Crypto/Dfa.lean`, `Crypto/Deriv/*`) certifies REGULAR structure — a finite-state run.
It cannot certify NESTED / balanced structure (arbitrary bracket depth), which is exactly what a JSON
payload or a handlebars template needs. This module lifts the same "prover supplies a locally-checkable
certificate; the verifier checks each step; the bridge says the certificate ⟺ the language" pattern to
CONTEXT-FREE grammars.

The spec side is mathlib's verified `ContextFreeGrammar` (`Produces`/`Derives`/`language`,
`mem_language_iff`) — read as the trusted denotational language, exactly as `Crypto/Dfa` leans on
mathlib's automata and `Crypto/Deriv/Thompson` leans on mathlib's `εNFA`. The ZK certificate is
home-grown: a DERIVATION FORM-CHAIN — the sentential forms `[initial] ⟶ … ⟶ input` the prover threads,
each consecutive pair a valid one-rule `Produces`. This is the context-free analogue of `Dfa.lean`'s
`DfaAccepts` run (a chain of `Step`s), and the bridge is the analogue of `dfa_bridge`.

    cfg_bridge        : (∃ chain, CfgAccepts g input chain) ↔ input ∈ g.language
    cfg_verify_sound  : verify accepts → input ∈ g.language   (derived off the bridge + `extractable`)

No `compress`/hash seam here — a parse certificate is pure structural checking. Crypto residue: the
STARK `extractable` carrier only (as with `Dfa.lean`).
-/
import Mathlib.Computability.ContextFreeGrammar
import Dregg2.Crypto.Primitives
import Dregg2.Authority.Predicate
import Metatheory.EpistemicDial
import Dregg2.Tactics

namespace Dregg2.Crypto.Cfg

open ContextFreeGrammar

universe u

variable {T : Type}

/-! ## The derivation form-chain (the ZK certificate) — a valid leftmost-agnostic derivation.

A `chain` is the list of sentential forms a derivation passes through. `producesChain g chain` says every
consecutive pair is a single-rule rewrite (`g.Produces`), i.e. each step is a valid production application
— the context-free analogue of `Dfa.lean`'s `chained` + per-step `Lookup`. `CfgAccepts g input chain`
then pins the two boundaries: the chain STARTS at the grammar's initial nonterminal and ENDS at the input
word (wrapped as terminals). This is exactly what an in-circuit CFG verifier's accepting bit certifies:
the prover exhibits the derivation, each rewrite is checked locally, and the endpoints are the public
boundary bindings. -/

/-- **`producesChain g chain`** — every consecutive pair of sentential forms is one valid production
step (`g.Produces`). The context-free `Transition`+`Lookup`: each rewrite applies a real grammar rule. -/
def producesChain (g : ContextFreeGrammar T) : List (List (Symbol T g.NT)) → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => g.Produces a b ∧ producesChain g (b :: rest)

/-- **`CfgAccepts g input chain`** — the CFG acceptance STATEMENT: the derivation chain is NON-EMPTY,
starts at the initial nonterminal `[.nonterminal g.initial]`, ends at the input word wrapped as terminals
`input.map .terminal`, and every step is a valid production (`producesChain`). This is the predicate the
verifier's accepting bit must certify — a valid derivation of `input` from the start symbol. -/
def CfgAccepts (g : ContextFreeGrammar T) (input : List T)
    (chain : List (List (Symbol T g.NT))) : Prop :=
  chain.head? = some [Symbol.nonterminal g.initial] ∧
  chain.getLast? = some (input.map Symbol.terminal) ∧
  producesChain g chain

/-! ## The bridge — `(∃ chain, CfgAccepts) ↔ input ∈ language`, FULLY proven (NO primitive seam).

`g.Derives = Relation.ReflTransGen g.Produces`, so a form-chain is exactly a reflexive-transitive
derivation unrolled into a checkable list. The two lemmas below are the standard `ReflTransGen ↔ chain`
correspondence, specialized to `Produces`; `cfg_bridge` then composes with mathlib's `mem_language_iff`
(which is `rfl`). No `compress`/hash anywhere — pure structural matching. -/

/-- A `Derives` unrolls to a form-chain: prepend the start symbol at each `head`-step. -/
theorem derives_to_chain (g : ContextFreeGrammar T) {u v : List (Symbol T g.NT)}
    (h : g.Derives u v) :
    ∃ chain, chain.head? = some u ∧ chain.getLast? = some v ∧ producesChain g chain := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[v], rfl, rfl, trivial⟩
  | @head a c h' _hcv ih =>
    obtain ⟨chain, hhead, hlast, hpc⟩ := ih
    cases chain with
    | nil => simp at hhead
    | cons c' rest =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      refine ⟨a :: c' :: rest, rfl, ?_, ?_⟩
      · rw [List.getLast?_cons_cons]; exact hlast
      · exact ⟨h', hpc⟩

/-- A form-chain from `u` to `v` witnesses `g.Derives u v`: fold each step through `Produces.trans_derives`. -/
theorem chain_to_derives (g : ContextFreeGrammar T) :
    ∀ (chain : List (List (Symbol T g.NT))) {u v},
      chain.head? = some u → chain.getLast? = some v → producesChain g chain → g.Derives u v := by
  intro chain
  induction chain with
  | nil => intro u v hhead _ _; simp at hhead
  | cons x xs ih =>
    intro u v hhead hlast hpc
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    cases xs with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst hlast
      exact Relation.ReflTransGen.refl
    | cons y ys =>
      obtain ⟨hxy, hrest⟩ := hpc
      rw [List.getLast?_cons_cons] at hlast
      exact hxy.trans_derives (ih rfl hlast hrest)

/-- **`cfg_bridge`** — the CFG parse-certificate's satisfiability is exactly membership in the grammar's
language. Soundness: a valid derivation chain from the start symbol to the input word proves
`input ∈ g.language`. Completeness: a word in the language has such a chain. No `compress` — no primitive
seam. Crypto residue: `extractable`, consumed by `cfg_verify_sound`. -/
theorem cfg_bridge (g : ContextFreeGrammar T) (input : List T) :
    (∃ chain, CfgAccepts g input chain) ↔ input ∈ g.language := by
  rw [mem_language_iff]
  constructor
  · rintro ⟨chain, hhead, hlast, hpc⟩
    exact chain_to_derives g chain hhead hlast hpc
  · intro hderiv
    obtain ⟨chain, hhead, hlast, hpc⟩ := derives_to_chain g hderiv
    exact ⟨chain, hhead, hlast, hpc⟩

#assert_axioms derives_to_chain
#assert_axioms chain_to_derives
#assert_axioms cfg_bridge

/-! ## Layer B — the CFG `VerifierKernel`: `verify` + carrier + DERIVED `verify_sound`.

Mirrors `Dfa.lean`'s kernel. `verify` is the §8 oracle over the disclosed grammar + input; `extractable`
(STARK soundness) gives "accept ⇒ a satisfying parse chain exists"; `cfg_verify_sound` is DERIVED off the
bridge. NO `binding`/`compress` carriers — the only assumption is STARK extractability. -/

/-- **The disclosed CFG statement** — the public inputs: the grammar `g` (the productions) and the input
word. At the `fullDisclosure` floor both are public (the deployed grammar + the cleartext payload). -/
structure Statement (T : Type) where
  /-- The public context-free grammar (the production set). -/
  g : ContextFreeGrammar T
  /-- The input word whose structure is certified. -/
  input : List T

/-- **Layer B — the CFG `VerifierKernel`.** The §8 `verify` oracle over the disclosed grammar + a parse
certificate, and the STARK `extractable` carrier. `extract` unpacks it: an accepted proof witnesses a
satisfying parse chain for the disclosed statement — the existence FRI/Fiat-Shamir soundness delivers. -/
class CfgVerifierKernel (T : Type) (Proof : Type) where
  /-- **The §8 verify oracle** (`stark::verify` for the CFG parse-check AIR). -/
  verify : Statement T → Proof → Bool
  /-- **CARRIER — STARK extractability/soundness**: accept ⇒ a satisfying parse chain exists. Never proved. -/
  extractable : Prop
  /-- `extractable` UNPACKED: an accepted proof witnesses a satisfying parse chain for the disclosed
  grammar+input. The named form the bridge composes with — STARK soundness. -/
  extract : extractable →
    ∀ (stmt : Statement T) (proof : Proof), verify stmt proof = true →
      ∃ chain, CfgAccepts stmt.g stmt.input chain

variable {Proof : Type}

/-- **`cfg_verify_sound`** — given `extractable`, an accepted CFG proof proves the input is in the
grammar's language: `verify stmt proof = true → stmt.input ∈ stmt.g.language`. Derived by composing
`extract` with `cfg_bridge`; never assumed. -/
theorem cfg_verify_sound {T : Type} [K : CfgVerifierKernel T Proof]
    (hext : K.extractable) (stmt : Statement T) (proof : Proof)
    (haccept : K.verify stmt proof = true) :
    stmt.input ∈ stmt.g.language := by
  obtain ⟨chain, hacc⟩ := K.extract hext stmt proof haccept
  exact (cfg_bridge stmt.g stmt.input).mp ⟨chain, hacc⟩

#assert_axioms cfg_verify_sound

/-! ## `Reference` — a concrete Dyck grammar + non-vacuity witnesses.

The one-bracket Dyck grammar `S → [ S ] | ε` (`op`/`cl` terminals), the canonical example of a language
that is context-free but NOT regular (the DFA cascade provably cannot recognize it). We exhibit a genuine
parse chain for `"[]"` and confirm it lands in the language via the bridge — the deliverable exercised on
a truly non-regular language, NO crypto. -/

namespace Reference

/-- Terminal alphabet: one bracket pair. -/
inductive Brk where
  | op
  | cl
  deriving DecidableEq, Repr

/-- The single nonterminal `S`. -/
inductive NTs where
  | S
  deriving DecidableEq, Repr

open Brk NTs

/-- Rule `S → [ S ]`. -/
def rBracket : ContextFreeRule Brk NTs :=
  ⟨NTs.S, [Symbol.terminal op, Symbol.nonterminal NTs.S, Symbol.terminal cl]⟩

/-- Rule `S → ε`. -/
def rEmpty : ContextFreeRule Brk NTs :=
  ⟨NTs.S, []⟩

/-- The Dyck grammar `S → [ S ] | ε`. -/
def dyck : ContextFreeGrammar Brk :=
  ⟨NTs, NTs.S, {rBracket, rEmpty}⟩

/-- The parse chain for `"[]"` = `[op, cl]`: `S ⟹ [ S ] ⟹ [ ]`. -/
def bracketsChain : List (List (Symbol Brk NTs)) :=
  [ [Symbol.nonterminal NTs.S],
    [Symbol.terminal op, Symbol.nonterminal NTs.S, Symbol.terminal cl],
    [Symbol.terminal op, Symbol.terminal cl] ]

/-- Non-vacuity: the `"[]"` chain is a genuine accepting parse (`CfgAccepts`). -/
theorem brackets_accepts : CfgAccepts dyck [op, cl] bracketsChain := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · -- Produces [S] [ [ S ] ] via rBracket (whole-nonterminal rewrite)
    refine ⟨rBracket, ?_, ?_⟩
    · simp only [dyck]; exact Finset.mem_insert_self _ _
    · exact ContextFreeRule.Rewrites.input_output
  · refine ⟨?_, trivial⟩
    -- Produces [ [ S ] ] [ [ ] ] via rEmpty rewriting the middle nonterminal
    refine ⟨rEmpty, ?_, ?_⟩
    · simp only [dyck]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · exact ContextFreeRule.rewrites_of_exists_parts rEmpty [Symbol.terminal op] [Symbol.terminal cl]

/-- Non-vacuity of the BRIDGE: the `"[]"` accepting parse proves `[op, cl] ∈ dyck.language`. -/
theorem brackets_in_language : [op, cl] ∈ dyck.language :=
  (cfg_bridge dyck [op, cl]).mp ⟨bracketsChain, brackets_accepts⟩

end Reference

end Dregg2.Crypto.Cfg
