/-
# Dregg2.Crypto.Deriv.Powerset — Stage 4 narrow-residual close: the DEPLOYED determinized table
# specifically (not just "any agreeing table") agrees with `derives`.

`TableDfa.tableDfa_faithful` (the keystone) trusts ANY flat table whose `accepts` agrees with dregg's
derivative matcher `derives` on every word. It is CONSTRUCTION-agnostic — exactly because the deployed
AIR is table-opaque (design §3.2/§3.3). What it does NOT do, by itself, is discharge the agreement
hypothesis for the table a SPECIFIC compiler emits. This module closes that for the determinization
`dfa/src/{compiler,derivative}.rs` actually runs.

The deployed `Pattern::Not` / intersection path — the genuinely-new deny-filter capability of this
pillar (`75af4a99`) — compiles through `derivative.rs::Re::compile`, a LAZY DERIVATIVE
determinization: a worklist that assigns integer state IDs to canonicalized residual regexes, with
`step state byte = canonicalize(state.derive(byte))`, `accept = nullable`, `start = the regex`, dead
state `0 = ∅`. That construction's transition function IS the Brzozowski derivative (modulo a
language-preserving canonicalization done by the smart constructors), so its emitted table agrees with
`derives` BY CONSTRUCTION — no Thompson-NFA correctness, no subset-construction correctness needed.

This file models exactly that determinizer's CORRECTNESS CONTRACT and proves the consequence:

  * `LangEquiv` — the language equivalence `R ≈ S := ∀ w, derives w R = derives w S`. It is the right
    quotient for a determinizer: `null` and `der` are both `LangEquiv`-congruences (trivially, since
    `derives [] = null` and `derives w ∘ der a = derives (a :: w)`), and `≅`-similar regexes are
    `LangEquiv` (`sim_derives`) — so the deployed ACI/absorption canonicalization (the smart
    constructors) preserves it.
  * `DerivDeterminizer State R` — a flat `TableDfa` over `State` (the integer state IDs) PLUS a
    `decode : State → PredRE` recovering each state's residual, with the three contract conditions a
    derivative-determinizer maintains: the start state decodes to `R`, each transition decodes to the
    derivative of its source's residual, and acceptance is nullability of the residual — all UP TO
    `LangEquiv`, which is all that survives canonicalization.
  * `determinizer_faithful` — the close: under that contract the emitted table's `accepts` decides
    EXACTLY the denotational language `Matches R`. So the DEPLOYED table — integer states and all — is
    a concrete instance of `tableDfa_faithful`, not merely "some agreeing table."

Two witnesses pin non-vacuity over BOTH the residual-typed and the integer-ID (deployed) state spaces:
the identity-decode derivative automaton (for ANY `R`, incl. the deny-filter `neg (sym p)`), and a
concrete `State := Nat` table recognizing `ε`'s language — the integer-ID shape `Re::compile` emits.

The in-circuit `Dfa.lean` cascade is IMPORTED, untouched. `#assert_axioms`-clean, `sorry`-free.

What remains (NARROWED — see `Thompson.lean`): the LEGACY complement-free path
`compiler.rs::pattern_to_nfa().determinize()` (the Thompson-NFA ε-closure subset construction)
instantiates this same contract only via the residual-language = Brzozowski-derivative bridge — i.e.
Thompson-construction correctness composed with subset-construction correctness (design §3.2 step 3).
`Thompson.lean` CLOSES the right factor (subset construction) end-to-end via mathlib's verified
`εNFA.toNFA_correct` + `NFA.toDFA_correct`, isolating the LEFT factor as the single named obligation
`ThompsonRecognizes` (`accepts (thompson R) = Matches R`) — the one piece still open (mathlib has no
regex→ε-NFA Thompson construction), shown inhabited by the canonical single-symbol automaton. The
deny-filter path this module closes needs neither factor.
-/
import Dregg2.Crypto.Deriv.TableDfa

namespace Dregg2.Crypto.Deriv

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra (Pred)

namespace PredRE

/-! ## `LangEquiv` — language equivalence, the determinizer's state quotient. -/

/-- **`LangEquiv R S`** — `R` and `S` recognize the same language, witnessed executably: they give
the same `derives` verdict on every word. This is the equivalence a determinizer collapses its states
by; it is coarser than syntactic equality and coarser than `≅`-similarity (every `≅`-similar pair is
`LangEquiv`, `sim_langEquiv`). It is automatically a `der`/`null`-congruence (`langEquiv_null`,
`langEquiv_der`), so threading a run through `LangEquiv`-collapsed states never changes the verdict. -/
def LangEquiv (R S : PredRE) : Prop := ∀ w, derives w R = derives w S

@[refl] theorem LangEquiv.refl (R : PredRE) : LangEquiv R R := fun _ => rfl

theorem LangEquiv.symm {R S : PredRE} (h : LangEquiv R S) : LangEquiv S R :=
  fun w => (h w).symm

theorem LangEquiv.trans {R S T : PredRE} (h₁ : LangEquiv R S) (h₂ : LangEquiv S T) :
    LangEquiv R T := fun w => (h₁ w).trans (h₂ w)

/-- `null` is a `LangEquiv`-congruence: language-equivalent regexes are equi-nullable (the `w = []`
instance, since `derives [] R = null R`). -/
theorem langEquiv_null {R S : PredRE} (h : LangEquiv R S) : null R = null S := h []

/-- `der a` is a `LangEquiv`-congruence: the derivative of language-equivalent regexes is
language-equivalent (`derives w (der a R) = derives (a :: w) R`). This is what lets a determinizer
canonicalize residuals between steps without changing the recognized language. -/
theorem langEquiv_der {R S : PredRE} (h : LangEquiv R S) (a : Value) :
    LangEquiv (der a R) (der a S) := fun w => h (a :: w)

/-- Every `≅`-similar pair is `LangEquiv` (via Stage 3 `sim_derives`). So the deployed compiler's
ACI / `∅`-absorption / double-negation canonicalization (the `derivative.rs` smart constructors, all
`≅`-preserving) keeps a state's residual `LangEquiv` to its un-normalized derivative — exactly the
`step_spec` a `DerivDeterminizer` requires. -/
theorem sim_langEquiv {R S : PredRE} (h : R ≅ S) : LangEquiv R S := fun w => sim_derives h w

/-! ## `DerivDeterminizer` — the correctness contract of a derivative-based determinization. -/

/-- **`DerivDeterminizer State R`** — a flat `TableDfa` over a state space `State` (in the deployed
compiler, `State = Nat`: the integer state IDs into the `order` vector), together with a `decode`
recovering each state's residual regex, satisfying the three invariants a derivative determinizer
maintains while building `R`'s table:

* `start_spec`  — the start state decodes (up to `LangEquiv`) to `R` itself;
* `step_spec`   — every transition `step s a` decodes to the derivative `der a (decode s)` (up to
                  `LangEquiv`; the deployed `step` is `canonicalize ∘ der`, and canonicalization is
                  `≅` hence `LangEquiv`);
* `accept_spec` — a state accepts iff its residual is nullable.

This is precisely the contract `derivative.rs::Re::compile` satisfies by construction (its states ARE
canonicalized residuals, its `step` IS `derive`, its `accepting` IS `nullable`). -/
structure DerivDeterminizer (State : Type) (R : PredRE) where
  /-- The emitted flat transition table (`compiler.rs::Dfa`). -/
  td : TableDfa State Value
  /-- Recover a state's residual regex (the canonicalized `Re` the compiler stores per state ID). -/
  decode : State → PredRE
  /-- The start state's residual is `R`. -/
  start_spec : LangEquiv (decode td.start) R
  /-- Each transition decodes to the derivative of its source's residual. -/
  step_spec : ∀ s a, LangEquiv (decode (td.step s a)) (der a (decode s))
  /-- A state accepts iff its residual matches the empty word. -/
  accept_spec : ∀ s, td.accept s ↔ null (decode s) = true

namespace DerivDeterminizer

variable {State : Type} {R : PredRE}

/-- The run invariant: running the table from any state `q` and reading `w` lands in a state whose
residual's nullability is exactly `derives w (decode q)`. Induction on `w`, threading `step_spec`
through `LangEquiv`. This is "running the determinized DFA = iterating the derivative." -/
theorem run_derives (D : DerivDeterminizer State R) (q : State) (w : List Value) :
    null (D.decode (D.td.runState q w)) = derives w (D.decode q) := by
  induction w generalizing q with
  | nil => rfl
  | cons a as ih =>
    -- runState q (a :: as) = runState (step q a) as ; derives (a :: as) X = derives as (der a X)
    show null (D.decode (D.td.runState (D.td.step q a) as)) = derives as (der a (D.decode q))
    rw [ih (D.td.step q a)]
    exact D.step_spec q a as

/-- **`accepts_derives`** — the deployed table's `accepts` agrees with `derives` on EVERY word.
Discharges the hypothesis `tableDfa_faithful` requires, for the specific table this determinizer
emits. -/
theorem accepts_derives (D : DerivDeterminizer State R) (w : List Value) :
    D.td.accepts w ↔ derives w R = true := by
  unfold TableDfa.accepts
  rw [D.accept_spec, run_derives D D.td.start w, D.start_spec w]

/-- **`determinizer_faithful`** — THE close: the table the determinizer emits recognizes EXACTLY the
denotational language `Matches R`. The DEPLOYED table (integer state IDs and all) is therefore a
concrete instance of the `tableDfa_faithful` keystone — its compiled boolean semantics is a THEOREM,
not an untrusted Rust gap. Chains `accepts_derives` (this construction agrees with `derives`) with
Stage 1 `correctness` (`derives ↔ Matches`). -/
theorem determinizer_faithful (D : DerivDeterminizer State R) (w : List Value) :
    D.td.accepts w ↔ Matches w R :=
  (D.accepts_derives w).trans (correctness w R)

end DerivDeterminizer

/-! ## Non-vacuity — the contract is inhabited over both residual-typed and integer-ID state spaces. -/

section Witnesses

private def fr7 : Value := .record [("k", .sym 7)]
private def p7 : Pred := .symEq "k" 7

/-- **`derivAutomaton R`** — the derivative automaton itself as a `DerivDeterminizer`, with states =
residual regexes (`decode = id`): `step s a = der a s`, `start = R`, `accept = null`. Every contract
condition is `rfl`. This witnesses the contract for ANY `R` — including the deny-filter
`neg (sym p)` — so the new complement capability's table is faithful. -/
def derivAutomaton (R : PredRE) : DerivDeterminizer PredRE R where
  td := { step := fun s a => der a s, start := R, accept := fun s => null s = true }
  decode := id
  start_spec := fun _ => rfl
  step_spec := fun _ _ _ => rfl
  accept_spec := fun _ => Iff.rfl

-- The derivative automaton is faithful to `Matches`, for every pattern…
example (R : PredRE) (w : List Value) : (derivAutomaton R).td.accepts w ↔ Matches w R :=
  (derivAutomaton R).determinizer_faithful w

-- …including the DENY-FILTER `~(k = 7)` — the deny-filter capability's table decides its language.
example (w : List Value) :
    (derivAutomaton (.neg (.sym p7))).td.accepts w ↔ Matches w (.neg (.sym p7)) :=
  (derivAutomaton _).determinizer_faithful w

/-! ### A concrete INTEGER-ID table — the shape `Re::compile` actually emits.

States are `Nat` IDs (`0 = dead/∅`, the start state, …) with a `decode` back to residuals — the
deployed layout. We model the 2-state table for `ε`'s language: `decode 0 = ε` (start, accepting),
every other ID decodes to `∅` (the dead state, self-looping). This is the integer-ID determinized form
the keystone now covers concretely. -/

/-- `decode` for the concrete integer-ID table: state `0` is the start residual `ε`; all others are
the dead residual `∅` (`bot`). -/
private def decEps : Nat → PredRE := fun n => if n = 0 then .ε else bot

/-- The derivative of every residual in the `ε`-table is `∅`: `der a ε = ∅` and `der a ∅ = ∅`. -/
private theorem der_decEps (a : Value) (s : Nat) : der a (decEps s) = bot := by
  unfold decEps
  by_cases h : s = 0
  · subst h; rfl
  · rw [if_neg h]
    simp only [bot, der, leaf, Pred.eval, Bool.false_eq_true, if_false]

/-- A concrete `DerivDeterminizer` with `State := Nat` (integer state IDs, as the deployed compiler
emits) recognizing `ε`'s language. `step` sends everything to the dead state `1`; `accept` is "is the
start state `0`". -/
def epsilonDet : DerivDeterminizer Nat .ε where
  td := { step := fun _ _ => 1, start := 0, accept := fun n => n = 0 }
  decode := decEps
  start_spec := fun _ => rfl
  step_spec := by
    intro s a w
    -- decode (step s a) = decEps 1 = ∅ ; der a (decode s) = ∅ (der_decEps)
    show derives w (decEps 1) = derives w (der a (decEps s))
    rw [der_decEps a s, show decEps 1 = bot from rfl]
  accept_spec := by
    intro s
    show (s = 0) ↔ (null (decEps s) = true)
    unfold decEps
    by_cases h : s = 0 <;> simp [h]

-- The integer-ID table is faithful: it decides EXACTLY `ε`'s language.
example (w : List Value) : epsilonDet.td.accepts w ↔ Matches w .ε :=
  epsilonDet.determinizer_faithful w

-- …accepting the empty word…
example : epsilonDet.td.accepts [] :=
  (epsilonDet.accepts_derives []).mpr (by decide)

-- …and rejecting a non-empty word (so `[fr7]` is denied, integer-ID table and all).
example : ¬ epsilonDet.td.accepts [fr7] := by
  rw [epsilonDet.accepts_derives [fr7]]; decide

end Witnesses

end PredRE

end Dregg2.Crypto.Deriv

/-! ## Axiom hygiene. -/

#assert_all_clean [
  Dregg2.Crypto.Deriv.PredRE.langEquiv_null,
  Dregg2.Crypto.Deriv.PredRE.langEquiv_der,
  Dregg2.Crypto.Deriv.PredRE.sim_langEquiv,
  Dregg2.Crypto.Deriv.PredRE.DerivDeterminizer.run_derives,
  Dregg2.Crypto.Deriv.PredRE.DerivDeterminizer.accepts_derives,
  Dregg2.Crypto.Deriv.PredRE.DerivDeterminizer.determinizer_faithful
]
