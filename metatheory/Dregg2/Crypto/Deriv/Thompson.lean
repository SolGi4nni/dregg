/-
# Dregg2.Crypto.Deriv.Thompson — Stage 4, the LEGACY Thompson-subset path: the SUBSET-CONSTRUCTION
# half of the bridge, CLOSED; the Thompson-construction half NAMED precisely as the sole residual.

`Powerset.lean` closed faithfulness for the DEPLOYED *derivative* determinizer (`derivative.rs::Re::
compile`), whose `step` IS the Brzozowski derivative, so its table agrees with `derives` BY
CONSTRUCTION. Its closing note named the one piece still open: the LEGACY complement-free path
`compiler.rs::pattern_to_nfa().determinize()` — a Thompson ε-NFA construction followed by the
ε-closure subset (powerset) construction — instantiates the same faithfulness contract only via the
"residual-language = Brzozowski-derivative" bridge, i.e.

  Thompson-construction correctness   ∘   subset-construction correctness.

This module CLOSES the right factor — subset-construction correctness — end-to-end, and ISOLATES the
left factor as a single, precisely-stated obligation `ThompsonRecognizes`.

## What is closed (the subset/determinization half)

`compiler.rs::Nfa::determinize` (`dfa/src/compiler.rs:296`) is the textbook ε-closure powerset
construction: DFA states are ε-closed sets of NFA states, `step S b = εclosure (⋃_{s∈S} δ(s,b))`,
`start = εclosure {nfaStart}`, `accept S = (nfaAccept ∈ S)`, with the flat table laid out as
`transitions[state*256+byte]`. That construction is **already verified in mathlib**, in two proven
edges we IMPORT (not re-prove):

  * `εNFA.toNFA_correct` — ε-elimination: `M.toNFA.accepts = M.accepts` (the ε-closure is sound);
  * `NFA.toDFA_correct`  — the subset construction: `N.toDFA.accepts = N.accepts`.

`compiler.rs`'s `determinize` IS `M.toNFA.toDFA` (ε-closure folded into the powerset step). We model
the deployed flat-table fold `Dfa::matches` as our `TableDfa` (exactly as `TableDfa.lean` does for the
derivative path) via `ofDFA`, prove the fold agrees with mathlib's `DFA.eval`, and chain:

  `determinizedTable M . accepts w  ↔  w ∈ M.accepts`     (`determinizedTable_accepts`)

So given ONLY that the Thompson ε-NFA recognizes the right language, the deployed determinized table
is faithful to the denotational spec `Matches` — `legacy_determinized_faithful`, via the keystone
`derives ↔ Matches` (`Deriv.correctness`).

## What remains (the Thompson half — NAMED, not closed, not `sorry`-ed)

`ThompsonRecognizes M R := ∀ w, w ∈ M.accepts ↔ derives w R = true` is exactly Thompson-construction
correctness: that `pattern_to_nfa p`'s ε-NFA accepts exactly the language of `p`'s `PredRE`. Mathlib
does NOT provide a regex→ε-NFA Thompson construction (it connects regexes to languages via Brzozowski
derivatives, `RegularExpression.rmatch_iff_matches'`, NOT via Thompson). So this factor is genuinely
open — it is the design §3.2-step-3 "months-scale automata theory," the inductive
`accepts (thompson R) = Matches R` over the disjoint-state-space composition of the concat/star/union
sub-automata (the ε-closure-across-the-join reasoning). It is NOT discharged here.

It IS, however, shown INHABITED — non-vacuous — by exhibiting the canonical single-symbol Thompson
automaton `symENfa φ` (the 2-state `s --φ--> a` machine `Nfa::single_byte`/`byte_range` builds) and
proving `ThompsonRecognizes (symENfa φ) (.sym φ)` in full, kernel-clean. So the closed
subset-construction half provably carries a REAL Thompson automaton all the way to `Matches`-faithful.

The in-circuit `Dfa.lean` cascade is untouched; the determinized-state space here is `Set σ` (the
canonical subset-construction state), related to the deployed integer state IDs by a bijection exactly
as `Powerset.lean`'s `decode` relates residuals to integer IDs — and `tableDfa_faithful'` is opaque to
the state representation, so the relabeling is immaterial.

`#assert_axioms`-clean, `sorry`-free.
-/
import Mathlib.Computability.EpsilonNFA
import Dregg2.Crypto.Deriv.TableDfa

namespace Dregg2.Crypto.Deriv

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra (Pred)
open Set

namespace PredRE

/-! ## Bridging a (mathlib) `DFA` to our flat-table `TableDfa` — the deployed `Dfa::matches` fold. -/

/-- **`ofDFA D`** — view a mathlib `DFA Value S` as our `TableDfa S Value` (the deployed
`compiler.rs::Dfa`'s flat `step`/`start`/`accept`). The transition FUNCTION, start, and accept set
carry over directly; `TableDfa.runState` is `DFA.evalFrom` (both `List.foldl step`). -/
def ofDFA {S : Type} (D : DFA Value S) : TableDfa S Value where
  step := D.step
  start := D.start
  accept := fun s => s ∈ D.accept

/-- The flat-table fold IS mathlib's `DFA.evalFrom` (both fold `step` along the word). -/
theorem ofDFA_runState {S : Type} (D : DFA Value S) (q : S) (w : List Value) :
    (ofDFA D).runState q w = D.evalFrom q w := by
  induction w generalizing q with
  | nil => rfl
  | cons a as ih => exact ih (D.step q a)

/-- `ofDFA`'s acceptance is mathlib's `DFA.accepts`. So our deployed-table model recognizes exactly
the language the mathlib `DFA` does. -/
theorem ofDFA_accepts {S : Type} (D : DFA Value S) (w : List Value) :
    (ofDFA D).accepts w ↔ w ∈ D.accepts := by
  unfold TableDfa.accepts
  rw [ofDFA_runState]
  exact Iff.rfl

/-! ## The deployed determinized table — `compiler.rs::Nfa::determinize` as `M.toNFA.toDFA`. -/

/-- **`determinizedTable M`** — the flat table the LEGACY path emits for the Thompson ε-NFA `M`:
the ε-closure powerset construction `compiler.rs::Nfa::determinize`, modelled as the verified mathlib
pipeline `M.toNFA.toDFA` (ε-elimination then subset construction) viewed as a `TableDfa`. States are
ε-closed sets of NFA states (`Set σ`) — the canonical subset-construction state; the deployed integer
state IDs are a bijective relabeling, immaterial to `tableDfa_faithful'`. -/
def determinizedTable {σ : Type} (M : εNFA Value σ) : TableDfa (Set σ) Value :=
  ofDFA M.toNFA.toDFA

/-- **`determinizedTable_accepts`** — the SUBSET-CONSTRUCTION half, CLOSED: the determinized table
recognizes EXACTLY the Thompson ε-NFA's language. This is `compiler.rs::Nfa::determinize`'s
correctness, discharged by mathlib's verified `εNFA.toNFA_correct` (ε-elimination) and
`NFA.toDFA_correct` (subset construction) — no re-proof, the textbook theorems. -/
theorem determinizedTable_accepts {σ : Type} (M : εNFA Value σ) (w : List Value) :
    (determinizedTable M).accepts w ↔ w ∈ M.accepts := by
  rw [determinizedTable, ofDFA_accepts]
  rw [show M.toNFA.toDFA.accepts = M.accepts by rw [NFA.toDFA_correct, εNFA.toNFA_correct]]

/-! ## The keystone, generic over the state representation, and the legacy close. -/

/-- **`tableDfa_faithful'`** — the `TableDfa.tableDfa_faithful` keystone, stated generically over the
state space `State` (the deployed legacy table's states are `Set σ`, not `PredRE`): any table whose
`accepts` agrees with `derives` everywhere decides EXACTLY `Matches R`. Construction- AND
representation-opaque; chains `Deriv.correctness`. -/
theorem tableDfa_faithful' {State : Type} (td : TableDfa State Value) (R : PredRE)
    (hagree : ∀ w, td.accepts w ↔ derives w R = true) (w : List Value) :
    td.accepts w ↔ Matches w R := by
  rw [hagree w, correctness]

/-- **`ThompsonRecognizes M R`** — the SOLE remaining obligation: the Thompson ε-NFA `M`
(`compiler.rs::pattern_to_nfa p`) recognizes exactly the language of `R = p`'s `PredRE`. This IS
Thompson-construction correctness (design §3.2 step 3) — the inductive `accepts (thompson R) =
Matches R` over the concat/star/union sub-automata, which mathlib does NOT provide and which is NOT
discharged here. It is the precisely-named wall. -/
def ThompsonRecognizes {σ : Type} (M : εNFA Value σ) (R : PredRE) : Prop :=
  ∀ w, w ∈ M.accepts ↔ derives w R = true

/-- **`legacy_determinized_faithful`** — the LEGACY-path close, MODULO the Thompson factor: IF the
Thompson ε-NFA `M` recognizes `R`'s language (`ThompsonRecognizes`), THEN the deployed determinized
table is faithful to the denotational spec `Matches R`. The subset-construction factor is fully
discharged (`determinizedTable_accepts`, via mathlib); only `ThompsonRecognizes` is assumed.

So the legacy complement-free path is covered by the faithfulness keystone EXACTLY up to the
named-and-isolated Thompson-construction obligation. -/
theorem legacy_determinized_faithful {σ : Type} (M : εNFA Value σ) (R : PredRE)
    (hM : ThompsonRecognizes M R) (w : List Value) :
    (determinizedTable M).accepts w ↔ Matches w R :=
  tableDfa_faithful' (determinizedTable M) R
    (fun w => (determinizedTable_accepts M w).trans (hM w)) w

/-! ## Non-vacuity — the canonical single-symbol Thompson automaton satisfies the obligation.

`compiler.rs::Nfa::single_byte`/`byte_range` build a 2-state machine `start --byte--> accept`. Its
`PredRE`-leaf analog is `symENfa φ`: states `Bool` (`false` = start, `true` = accept), one transition
`false --(a : leaf φ a)--> true`, no ε-edges. We prove `ThompsonRecognizes (symENfa φ) (.sym φ)` in
full — so the closed subset half provably carries a GENUINE Thompson automaton to `Matches`-faithful,
and the `ThompsonRecognizes` contract is inhabited, not vacuous. -/

/-- The canonical single-symbol Thompson ε-NFA: `false --(leaf φ)--> true`, no ε. -/
def symENfa (φ : Pred) : εNFA Value Bool where
  step s o := match s, o with
    | false, some a => if leaf φ a then {true} else (∅ : Set Bool)
    | _, _ => (∅ : Set Bool)
  start := {false}
  accept := {true}

@[simp] theorem symENfa_step_true (φ : Pred) (o : Option Value) :
    (symENfa φ).step true o = (∅ : Set Bool) := rfl
@[simp] theorem symENfa_step_false_none (φ : Pred) :
    (symENfa φ).step false none = (∅ : Set Bool) := rfl
@[simp] theorem symENfa_step_false_some (φ : Pred) (a : Value) :
    (symENfa φ).step false (some a) = (if leaf φ a then {true} else (∅ : Set Bool)) := rfl

/-- No transition leaves `true` — any path FROM `true` is the empty path. -/
theorem symENfa_path_true {φ : Pred} {u : Bool} {x : List (Option Value)}
    (h : (symENfa φ).IsPath true u x) : u = true ∧ x = [] := by
  cases h with
  | nil => exact ⟨rfl, rfl⟩
  | cons t s u a x' hstep _ => exact absurd hstep (by simp)

/-- A path `false ⇝ true` is exactly a single symbol `a` satisfying the leaf. -/
theorem symENfa_path_false_true {φ : Pred} {x : List (Option Value)}
    (h : (symENfa φ).IsPath false true x) : ∃ a, x = [some a] ∧ leaf φ a = true := by
  cases h with
  | cons t s u a x' hstep hpath =>
    cases a with
    | none => exact absurd hstep (by simp)
    | some av =>
      by_cases hl : leaf φ av
      · rw [symENfa_step_false_some, if_pos hl, mem_singleton_iff] at hstep
        subst hstep
        obtain ⟨_, hx'⟩ := symENfa_path_true hpath
        subst hx'
        exact ⟨av, rfl, hl⟩
      · rw [symENfa_step_false_some, if_neg hl] at hstep
        exact absurd hstep (by simp)

/-- `symENfa φ` recognizes exactly singletons `[a]` with `leaf φ a`. -/
theorem symENfa_accepts (φ : Pred) (w : List Value) :
    w ∈ (symENfa φ).accepts ↔ ∃ a, w = [a] ∧ leaf φ a = true := by
  rw [εNFA.mem_accepts_iff_exists_path]
  constructor
  · rintro ⟨s₁, s₂, x', hs₁, hs₂, hred, hpath⟩
    rw [show (symENfa φ).start = ({false} : Set Bool) from rfl, mem_singleton_iff] at hs₁
    rw [show (symENfa φ).accept = ({true} : Set Bool) from rfl, mem_singleton_iff] at hs₂
    subst hs₁; subst hs₂
    obtain ⟨av, hx', hl⟩ := symENfa_path_false_true hpath
    subst hx'
    refine ⟨av, ?_, hl⟩
    simpa using hred.symm
  · rintro ⟨a, rfl, hl⟩
    refine ⟨false, true, [some a], rfl, rfl, by simp, ?_⟩
    rw [εNFA.isPath_singleton, symENfa_step_false_some, if_pos hl]
    exact mem_singleton _

/-- **`symENfa_recognizes`** — the obligation, DISCHARGED for the canonical single-symbol Thompson
automaton: `symENfa φ` recognizes exactly `(.sym φ)`'s language. So `ThompsonRecognizes` is inhabited
by a real Thompson construction. -/
theorem symENfa_recognizes (φ : Pred) : ThompsonRecognizes (symENfa φ) (.sym φ) := by
  intro w
  rw [symENfa_accepts, correctness, Matches]

/-! ### The closed subset half carries the canonical Thompson automaton to `Matches`-faithful. -/

section Witnesses

private def frameK7 : Value := .record [("k", .sym 7)]
private def isK7 : Pred := .symEq "k" 7

-- The determinized table of the single-symbol Thompson automaton is faithful to `Matches`…
example (w : List Value) :
    (determinizedTable (symENfa isK7)).accepts w ↔ Matches w (.sym isK7) :=
  legacy_determinized_faithful (symENfa isK7) (.sym isK7) (symENfa_recognizes isK7) w

-- …it ACCEPTS a real matching word (the determinized subset table, Set-states and all)…
example : (determinizedTable (symENfa isK7)).accepts [frameK7] := by
  rw [legacy_determinized_faithful (symENfa isK7) (.sym isK7) (symENfa_recognizes isK7), Matches]
  exact ⟨frameK7, rfl, by decide⟩

-- …and REJECTS the empty word (≠ a singleton) — both polarities, non-vacuous.
example : ¬ (determinizedTable (symENfa isK7)).accepts [] := by
  rw [legacy_determinized_faithful (symENfa isK7) (.sym isK7) (symENfa_recognizes isK7), Matches]
  rintro ⟨a, h, _⟩
  exact absurd h (by simp)

end Witnesses

end PredRE

end Dregg2.Crypto.Deriv

/-! ## Axiom hygiene. -/

#assert_all_clean [
  Dregg2.Crypto.Deriv.PredRE.ofDFA_accepts,
  Dregg2.Crypto.Deriv.PredRE.determinizedTable_accepts,
  Dregg2.Crypto.Deriv.PredRE.tableDfa_faithful',
  Dregg2.Crypto.Deriv.PredRE.legacy_determinized_faithful,
  Dregg2.Crypto.Deriv.PredRE.symENfa_accepts,
  Dregg2.Crypto.Deriv.PredRE.symENfa_recognizes
]
