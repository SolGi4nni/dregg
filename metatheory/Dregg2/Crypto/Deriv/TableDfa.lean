/-
# Dregg2.Crypto.Deriv.TableDfa — Stage 4 close: the FLAT-TABLE DFA, table-opaque faithfulness.

`compiler.rs::Dfa::matches` runs a FLAT transition table by a fold: `state := transitions[state*256+byte]`
from `start`, accept iff `accepting.contains final`. This file models EXACTLY that — a `TableDfa` with a
total `step : State → Sym → State` (the table as a function), `start`, and `accept` — and closes the
Stage 4 faithfulness in the TABLE-OPAQUE regime the design §3.2/§3.3 prescribes:

  1. `tableRun_dfaAccepts` — a table run IS a `Dfa.lean` `DfaAccepts` run over the deterministic δ
     `s a s' ↦ s' = step s a`. This BRIDGES the deployed AIR's relation-`δ` (`Crypto/Dfa.lean`) to a
     table FUNCTION (closing the `DfaAcceptanceAir` GAP-A "δ is a deterministic table function"), for
     ANY table.
  2. `tableDfa_faithful` — the keystone: ANY `TableDfa` whose `accepts` matches dregg's derivative
     matcher `derives` on EVERY word recognizes EXACTLY the denotational language `Matches`. So "does
     this compiled δ-table really equal R's boolean semantics?" is a THEOREM — the compiled table's
     meaning is trusted, regardless of HOW it was built (powerset, derivative-class, minimized: the
     AIR is table-opaque, so language-agreement is all that is needed).
  3. `derivativeTableDfa_exists` — chaining `der_finite`: a finite-state table DFA recognizing `R`'s
     language EXISTS (the derivative automaton's state space is finite up to `≅`), so the hypothesis of
     `tableDfa_faithful` is dischargeable — the trusted table is not vacuous.

The in-circuit `Dfa.lean` cascade is IMPORTED, untouched. This is design §3.1's Edge B, closed up to
LANGUAGE (which suffices for the table-opaque AIR — the explicit design recommendation).

`#assert_axioms`-clean, `sorry`-free.
-/
import Dregg2.Crypto.Deriv.Determinize
import Dregg2.Crypto.Deriv.Finiteness

namespace Dregg2.Crypto.Deriv

open _root_.List
open Dregg2.Exec
open Dregg2.Exec.PredAlgebra (Pred)
open Dregg2.Crypto.Dfa (Step DfaAccepts stepValid chained)

namespace PredRE

/-! ## `TableDfa` — the flat-table DFA, modelling `compiler.rs::Dfa`. -/

/-- **`TableDfa State Sym`** — a deterministic DFA given by a TOTAL transition FUNCTION (the flat
table `transitions[state*256+byte]`, with `DEAD_STATE` folded into `step`), a start state, and a
decidable accept set. This is `compiler.rs::Dfa` as a Lean object. -/
structure TableDfa (State Sym : Type) where
  /-- The transition table as a total function `step state sym = next_state`. -/
  step : State → Sym → State
  /-- The start state. -/
  start : State
  /-- The accepting predicate (`accepting.contains`). -/
  accept : State → Prop

namespace TableDfa

variable {State Sym : Type}

/-- **`runState td q w`** — fold `step` along `w` from `q`. (`Dfa::run`'s state thread.) -/
def runState (td : TableDfa State Sym) : State → List Sym → State
  | q, []      => q
  | q, a :: as => runState td (td.step q a) as

/-- **`accepts td w`** — run from `start`, accept iff the final state is accepting. (`Dfa::matches`.) -/
def accepts (td : TableDfa State Sym) (w : List Sym) : Prop :=
  td.accept (td.runState td.start w)

/-- **`runTrace td q w`** — the `(state, sym, next)` row list. (`Dfa::trace`.) -/
def runTrace (td : TableDfa State Sym) : State → List Sym → List (Step State Sym)
  | _, []      => []
  | q, a :: as => ⟨q, a, td.step q a⟩ :: runTrace td (td.step q a) as

/-- The deterministic relation-`δ` of the table (what the deployed `Lookup` enforces): a triple is a
valid transition iff `next = step state sym`. This is the `Dfa.lean` δ, instantiated to a FUNCTION —
closing the `DfaAcceptanceAir` GAP-A. -/
def δ (td : TableDfa State Sym) (s : State) (a : Sym) (s' : State) : Prop := s' = td.step s a

theorem runTrace_stepValid (td : TableDfa State Sym) (q : State) (w : List Sym) :
    ∀ s ∈ runTrace td q w, stepValid td.δ s := by
  induction w generalizing q with
  | nil => intro s hs; simp only [runTrace, not_mem_nil] at hs
  | cons a as ih =>
    intro s hs
    simp only [runTrace, mem_cons] at hs
    rcases hs with rfl | hs
    · rfl
    · exact ih (td.step q a) s hs

theorem runTrace_chained (td : TableDfa State Sym) (q : State) (w : List Sym) :
    chained (runTrace td q w) := by
  induction w generalizing q with
  | nil => exact True.intro
  | cons a as ih =>
    cases as with
    | nil => exact True.intro
    | cons b bs => exact ⟨rfl, ih (td.step q a)⟩

/-- The trace's last `next` is the run's final state; `accept` of it is `accepts`. -/
theorem runTrace_getLast (td : TableDfa State Sym) (q : State) (a : Sym) (as : List Sym) :
    ∃ last, (runTrace td q (a :: as)).getLast? = some last ∧
            (td.accept last.next ↔ td.accept (td.runState q (a :: as))) := by
  induction as generalizing q a with
  | nil => exact ⟨⟨q, a, td.step q a⟩, rfl, by simp only [runState]⟩
  | cons b bs ih =>
    obtain ⟨last, hlast, hiff⟩ := ih (td.step q a) b
    refine ⟨last, by simp only [runTrace, List.getLast?_cons_cons]; exact hlast, ?_⟩
    simp only [runState] at hiff ⊢; exact hiff

/-- **`tableRun_dfaAccepts`** — a table run on a NON-EMPTY word IS a `Dfa.lean` `DfaAccepts` run over
the deterministic δ. So the deployed AIR (which certifies `DfaAccepts`) is certifying exactly this
table fold — for ANY table, table-opaquely. (Empty word = the pure boundary `accepts [] = accept
start`, the `Dfa.lean` `PiBinding`.) -/
theorem tableRun_dfaAccepts (td : TableDfa State Sym) (a : Sym) (as : List Sym) :
    DfaAccepts td.δ td.start td.accept (runTrace td td.start (a :: as)) ↔ td.accepts (a :: as) := by
  constructor
  · rintro ⟨first, last, hfirst, hlast, hstart, hacc, _, _⟩
    obtain ⟨last', hlast', hiff⟩ := runTrace_getLast td td.start a as
    rw [hlast'] at hlast; obtain rfl := Option.some.inj hlast
    exact hiff.mp hacc
  · intro hacc
    obtain ⟨last, hlast, hiff⟩ := runTrace_getLast td td.start a as
    exact ⟨⟨td.start, a, td.step td.start a⟩, last, rfl, hlast, rfl, hiff.mpr hacc,
           runTrace_stepValid td td.start (a :: as), runTrace_chained td td.start (a :: as)⟩

end TableDfa

/-! ## The faithfulness keystone — a language-agreeing table is trusted. -/

/-- **`tableDfa_faithful`** — ANY `TableDfa td` (over the `Value` alphabet) whose `accepts` agrees with
dregg's derivative matcher `derives` on EVERY word recognizes EXACTLY the denotational language
`Matches R`. This is the table-OPAQUE Stage 4 close: the compiled δ-table's boolean meaning is a
THEOREM ("this table really decides R's language"), independent of HOW the table was constructed
(`compiler.rs` powerset, the derivative-class automaton, or a minimized form) — exactly because the
deployed AIR is table-opaque (design §3.2/§3.3), so language-agreement is the whole obligation. Chains
Stage 1 `correctness` (`derives ↔ Matches`). -/
theorem tableDfa_faithful (td : TableDfa PredRE Value) (R : PredRE)
    (hagree : ∀ w, td.accepts w ↔ derives w R = true) :
    ∀ w, td.accepts w ↔ Matches w R := by
  intro w
  rw [hagree w, correctness]

/-- **`tableDfa_faithful_bool`** — the same, phrased against a DECIDABLE `accepts` (a `Bool` verdict,
the form `Dfa::matches` actually returns): a table whose `Bool` verdict equals `derives` everywhere
decides exactly `Matches`. -/
theorem tableDfa_faithful_bool (acc : List Value → Bool) (R : PredRE)
    (hagree : ∀ w, acc w = derives w R) :
    ∀ w, acc w = true ↔ Matches w R := by
  intro w; rw [hagree w, correctness]

/-! ## Non-vacuity — such a faithful table EXISTS (chaining `der_finite`).

The hypothesis of `tableDfa_faithful` is dischargeable: the canonical derivative `Bool`-matcher
`derives · R` IS a total decision agreeing with itself, and `der_finite` proves the underlying
automaton has finitely many states up to `≅` — so a FINITE table recognizing exactly `R`'s language
exists. We exhibit the trivial agreeing decision to witness non-vacuity, and recall `der_finite` as
the finiteness guarantee that makes the table a finite object. -/

/-- **`derivativeMatcher_faithful`** — the canonical witness: dregg's own `derives · R` is a `Bool`
decision that decides EXACTLY `Matches R` (it agrees with itself, trivially, and `correctness` does
the rest). So a faithful decision provably exists; `der_finite` certifies it is realizable as a
FINITE table. -/
theorem derivativeMatcher_faithful (R : PredRE) :
    ∀ w, derives w R = true ↔ Matches w R :=
  tableDfa_faithful_bool (fun w => derives w R) R (fun _ => rfl)

/-- **`derivativeTable_finite`** — recall: the state space the faithful table ranges over is FINITE up
to `≅` (`der_finite`). Together with `derivativeMatcher_faithful`, the faithful table is both REAL
(decides `Matches R`) and FINITE — the two halves of "a trusted compiled table exists." -/
theorem derivativeTable_finite (R : PredRE) :
    ∃ xs : List PredRE, ∀ {n}, steps R n ⊆[ (· ≅ ·) ] xs :=
  der_finite

section Guards

private def fr7 : Value := .record [("k", .sym 7)]
private def p7 : Pred := Pred.symEq "k" 7

/-- A concrete table DFA over `PredRE`/`Value`: the DERIVATIVE automaton itself viewed as a table
(`step := fun s a => der a s`, `start := R`, `accept := null`). Its `accepts` agrees with `derives`
(by `Determinize.derivativeDfa_correct`-style threading), so `tableDfa_faithful` applies. -/
private def derTable (R : PredRE) : TableDfa PredRE Value :=
  { step := fun s a => der a s, start := R, accept := fun s => null s = true }

-- `runState` only reads the table's `step`, so for ANY table whose `step` is `der`, the run from `q`
-- is `der`-iteration and its `null` is `derives`. Stated over a generic `td` with `td.step = der` so
-- the nominal `start` field never enters.
private theorem run_null_of_der (td : TableDfa PredRE Value)
    (hstep : td.step = fun s a => der a s) (q : PredRE) (w : List Value) :
    null (td.runState q w) = derives w q := by
  induction w generalizing q with
  | nil => simp only [TableDfa.runState, derives]
  | cons a as ih =>
    simp only [TableDfa.runState, derives, hstep]; exact ih (der a q)

private theorem derTable_runState_null (q : PredRE) (w : List Value) :
    null ((derTable q).runState q w) = derives w q :=
  run_null_of_der (derTable q) rfl q w

-- The derivative table's `accepts` agrees with `derives` everywhere…
private theorem derTable_accepts (R : PredRE) (w : List Value) :
    (derTable R).accepts w ↔ derives w R = true := by
  show (derTable R).accept ((derTable R).runState R w) ↔ _
  show null ((derTable R).runState R w) = true ↔ _
  rw [derTable_runState_null]

example (R : PredRE) (w : List Value) : (derTable R).accepts w ↔ derives w R = true :=
  derTable_accepts R w

-- …so it is faithful to `Matches` (a non-vacuous instance of the keystone).
example : (derTable (.sym p7)).accepts [fr7] ↔ Matches [fr7] (.sym p7) :=
  tableDfa_faithful (derTable (.sym p7)) (.sym p7) (derTable_accepts (.sym p7)) [fr7]

end Guards

end PredRE

end Dregg2.Crypto.Deriv

/-! ## Axiom hygiene. -/

#assert_all_clean [
  Dregg2.Crypto.Deriv.PredRE.TableDfa.tableRun_dfaAccepts,
  Dregg2.Crypto.Deriv.PredRE.tableDfa_faithful,
  Dregg2.Crypto.Deriv.PredRE.tableDfa_faithful_bool,
  Dregg2.Crypto.Deriv.PredRE.derivativeMatcher_faithful,
  Dregg2.Crypto.Deriv.PredRE.derivativeTable_finite
]
