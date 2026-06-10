/-
# Dregg2.Conserve — shared conservation lemmas + the `conserve` / `commit_cases` tactics.

Factors out two patterns that appear verbatim in the executable kernels:

1. `sum_pointUpdate` / `sum_conserve_of_deltas_zero` — general `Finset.sum`
   debit/credit-cancellation lemmas over `CellId → ℤ`.
2. `conserve` — a macro tactic closing `(∑ … f) = ∑ … g` when per-point deltas cancel
   pointwise; fails loudly when they do not (never silently masks a missing `src ≠ dst`).
3. `commit_cases h with pat` — structural split for a fail-closed `if guard then some … else none`
   executor: discharges the `none` branch and performs read-back + guard extraction on the `some`
   branch, leaving the content goal open.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Dregg2.Tactics

namespace Dregg2.Conserve

open scoped BigOperators

/-- A cell identity (kept generic; reuses `Nat` like the executable kernels). -/
abbrev CellId := Nat

/-! ## 1. The general conservation lemma library.

The single-point-indicator sum, and the two lemmas the executable kernels need: the value
of a sum after a pointwise update, and the conservation criterion "if per-point deltas sum
to zero, the total is unchanged". -/

/-- **Single-point indicator sum.** Summing an indicator that is `v` at exactly `a ∈ acc`
and `0` elsewhere gives `v`. -/
theorem sum_indicator (acc : Finset CellId) (a : CellId) (v : ℤ) (ha : a ∈ acc) :
    (∑ c ∈ acc, (if c = a then v else 0)) = v := by
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (fun h => absurd ha h)]
  simp

/-- **Sum after a pointwise update.** Updating `bal` to `bal'` changes the `Finset.sum` by
the sum of per-point deltas:

    (∑ c ∈ acc, bal' c) = (∑ c ∈ acc, bal c) + ∑ c ∈ acc, (bal' c - bal c). -/
theorem sum_pointUpdate (acc : Finset CellId) (bal bal' : CellId → ℤ) :
    (∑ c ∈ acc, bal' c)
      = (∑ c ∈ acc, bal c) + ∑ c ∈ acc, (bal' c - bal c) := by
  rw [Finset.sum_sub_distrib]; ring

/-- **Conservation from cancelling deltas.** If the per-point deltas sum to zero, the total
is conserved: `(∑ c ∈ acc, bal' c) = ∑ c ∈ acc, bal c`. -/
theorem sum_conserve_of_deltas_zero (acc : Finset CellId) (bal bal' : CellId → ℤ)
    (hzero : (∑ c ∈ acc, (bal' c - bal c)) = 0) :
    (∑ c ∈ acc, bal' c) = ∑ c ∈ acc, bal c := by
  rw [sum_pointUpdate acc bal bal', hzero, add_zero]

/-- **Two-cell transfer conservation.** A debit/credit between two distinct cells `src ≠ dst`,
both in `acc`, conserves the sum: the deltas (`-amt` at `src`, `+amt` at `dst`, `0` elsewhere)
cancel via `sum_conserve_of_deltas_zero`. -/
theorem sum_transfer_conserve (acc : Finset CellId) (bal : CellId → ℤ)
    (src dst : CellId) (amt : ℤ) (hsrc : src ∈ acc) (hdst : dst ∈ acc) (hne : src ≠ dst) :
    (∑ c ∈ acc,
        (if c = src then bal c - amt else if c = dst then bal c + amt else bal c))
      = ∑ c ∈ acc, bal c := by
  apply sum_conserve_of_deltas_zero
  have hg : ∀ c ∈ acc,
      ((if c = src then bal c - amt else if c = dst then bal c + amt else bal c) - bal c)
        = (if c = src then (-amt) else 0) + (if c = dst then amt else 0) := by
    intro c _
    rcases eq_or_ne c src with h1 | h1
    · subst h1; rw [if_pos rfl, if_pos rfl, if_neg hne]; ring
    · rcases eq_or_ne c dst with h2 | h2
      · subst h2; rw [if_neg h1, if_pos rfl, if_neg h1, if_pos rfl]; ring
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]; ring
  rw [Finset.sum_congr rfl hg, Finset.sum_add_distrib,
      sum_indicator acc src (-amt) hsrc, sum_indicator acc dst amt hdst]
  ring

-- Axiom-hygiene: the library rests only on the three standard kernel axioms.
#assert_axioms sum_indicator
#assert_axioms sum_pointUpdate
#assert_axioms sum_conserve_of_deltas_zero
#assert_axioms sum_transfer_conserve

/-! ## 2. The `conserve` tactic.

Closes a goal `(∑ c ∈ acc, f c) = ∑ c ∈ acc, g c` when per-point deltas `f c - g c` cancel
pointwise (each summand zero, after `split_ifs` and discharging guards from context). It
reduces to "delta-sum is zero" then proves each summand is `0` via `Finset.sum_eq_zero` →
`split_ifs` → `simp_all`/`ring`.

This handles the pointwise case (re-labellings, `+v-v` round-trips, per-cell net zero). The
two-point debit/credit move (deltas individually nonzero, globally cancelling) is NOT
pointwise — use `sum_transfer_conserve` instead; a macro cannot robustly drive that global
collapse without the specific membership facts.

Honesty rail: the real cancellation is wrapped in `first | <real> | fail "…"`. If deltas do
not cancel pointwise, `ring` fails and the tactic errors loudly — it never falls through to a
weaker closer that could mask a missing hypothesis. -/

/-- `conserve` — close `(∑ … f) = ∑ … g` when per-point deltas cancel pointwise. Fails
loudly ("conserve: deltas do not cancel …") if they do not; never silently closes a
non-conserving goal. Bring guard facts (`src ≠ dst`, memberships) into context first.
For the two-cell debit/credit move use `sum_transfer_conserve` instead. -/
macro "conserve" : tactic =>
  `(tactic|
    first
    | (rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
       refine Finset.sum_eq_zero ?_
       intro _ _
       split_ifs <;> (try simp_all) <;> ring
       -- `done` is load-bearing: forces an error (→ fall through to `fail`) if any summand
       -- was left unclosed, so `conserve` cannot silently leave a residual goal.
       done)
    | fail "conserve: deltas do not cancel pointwise — bring the guard facts (e.g. \
        `src ≠ dst`, memberships) into context, or use `sum_transfer_conserve` for a \
        two-point debit/credit move")

/-! ## 3. The `commit_cases h with pat` tactic.

For the fail-closed executor shape `def f … := if <guard> then some {…} else none`,
given `h : f … = some s'`, `commit_cases h with pat`:
- splits the `if` (`split at h`);
- on the `none` branch, closes by contradiction from `h : none = some s'`;
- on the `some` branch, reads back `h` (`Option.some.injEq`, `Prod.mk.injEq`) and `subst`s,
  then `obtain pat` the conjunctive guard `‹_ ∧ _›`,
leaving the live `some`-branch goal open for the caller to prove.

Structural rail: performs read-back + guard extraction only; does NOT run a closer on the
`some`-branch goal (which carries the real content obligation). -/

/-- `commit_cases h with pat` — split a fail-closed `if guard then some … else none` hypothesis
`h : f … = some s'`. Discharges the `none` branch by contradiction; on the `some` branch
performs `some`/`Prod` read-back, `subst`s the state equation, and `obtain pat` the guard —
leaving the content goal open. -/
syntax "commit_cases" ident "with" rcasesPat : tactic
macro_rules
  | `(tactic| commit_cases $h:ident with $pat:rcasesPat) =>
    `(tactic|
      (split at $h:ident
       -- impossible `none` branch: `h : none = some _` — closed by contradiction.
       -- `case isFalse` targets it explicitly so the closer cannot touch the live `some` branch.
       case isFalse => exact absurd $h:ident (by simp)
       -- only the committed `isTrue` goal remains. Read it back (`Option`/`Prod` injection,
       -- `subst` the recovered state equation, `obtain` the guard) — then STOP. No closer runs.
       simp only [Option.some.injEq, Prod.mk.injEq] at $h:ident
       subst $h:ident
       obtain $pat := ‹_ ∧ _›))

/-! ## Demonstrations / regression tests.

A toy ledger sum and a toy fail-closed executor in the style of the real kernel proofs. These
`example`s serve as usage documentation and regression guard. -/

/-! ### `conserve`: pointwise cancellation. -/

/-- A single-point re-labelling with cancelling `+v / −v` deltas conserves the sum.
`conserve` closes it: the per-cell net change is `0`. -/
example (acc : Finset CellId) (bal : CellId → ℤ) (a : CellId) (v : ℤ) :
    (∑ c ∈ acc, (if c = a then bal c + v - v else bal c)) = ∑ c ∈ acc, bal c := by
  conserve

/-- A two-touch update netting to zero at each cell (debit `amt`, then credit `amt`, same cell)
conserves — pointwise, so `conserve` closes it. (Contrast the two-cell move below.) -/
example (acc : Finset CellId) (bal : CellId → ℤ) (a : CellId) (amt : ℤ) :
    (∑ c ∈ acc, (if c = a then bal c - amt + amt else bal c)) = ∑ c ∈ acc, bal c := by
  conserve

/-- Honesty-rail demonstration (negative test). The deltas here do NOT cancel — at cell `a`
the net change is `+amt ≠ 0` — so `conserve` must fail rather than close the false claim.
We assert the failure with `fail_if_success`: if `conserve` ever proved this, the `example`
would fail to compile, making the rail a build-checked regression test. -/
example (_acc : Finset CellId) (_bal : CellId → ℤ) (_a : CellId) (_amt : ℤ) (_hpos : _amt ≠ 0) :
    True := by
  fail_if_success
    (have : (∑ c ∈ _acc, (if c = _a then _bal c + _amt else _bal c)) = ∑ c ∈ _acc, _bal c := by
       conserve)
  trivial

/-! ### The two-cell move: deltas nonzero pointwise but globally cancelling.

`-amt` at `src`, `+amt` at `dst` — not pointwise zero, so handled by `sum_transfer_conserve`
rather than `conserve`. -/

/-- A transfer between two distinct live cells conserves the total — one-line via
`sum_transfer_conserve`. -/
example (acc : Finset CellId) (bal : CellId → ℤ) (src dst : CellId) (amt : ℤ)
    (hsrc : src ∈ acc) (hdst : dst ∈ acc) (hne : src ≠ dst) :
    (∑ c ∈ acc, (if c = src then bal c - amt else if c = dst then bal c + amt else bal c))
      = ∑ c ∈ acc, bal c := by
  exact sum_transfer_conserve acc bal src dst amt hsrc hdst hne

/-- Honesty-rail: `sum_transfer_conserve` requires `hne : src ≠ dst`. Without it the
debit and credit collapse onto one cell and do not cancel; the `src = dst` version of this
claim is false. -/
example (acc : Finset CellId) (bal : CellId → ℤ) (src dst : CellId) (amt : ℤ)
    (hsrc : src ∈ acc) (hdst : dst ∈ acc) (hne : src ≠ dst) :
    (∑ c ∈ acc, (if c = src then bal c - amt else if c = dst then bal c + amt else bal c))
      = ∑ c ∈ acc, bal c :=
  -- `hne` is load-bearing: `sum_transfer_conserve` requires it.
  sum_transfer_conserve acc bal src dst amt hsrc hdst hne

/-! ### `commit_cases`: the fail-closed read-back. -/

/-- A toy fail-closed executor: credits cell `a` by `amt` only when `0 ≤ amt ∧ a ∈ accounts`. -/
def toyExec (accounts : Finset CellId) (bal : CellId → ℤ) (a : CellId) (amt : ℤ) :
    Option (CellId → ℤ) :=
  if 0 ≤ amt ∧ a ∈ accounts then
    some (fun c => if c = a then bal c + amt else bal c)
  else
    none

/-- `commit_cases` splits the executor, kills the `none` branch, reads back the result on the
`some` branch, and extracts the guard `⟨hpos, hmem⟩` — leaving the content goal open. -/
example (accounts : Finset CellId) (bal bal' : CellId → ℤ) (a : CellId) (amt : ℤ)
    (h : toyExec accounts bal a amt = some bal') :
    (∑ c ∈ accounts, bal' c) = (∑ c ∈ accounts, bal c) + amt := by
  unfold toyExec at h
  commit_cases h with ⟨hpos, hmem⟩
  -- Goal is now the live content (sum after the credit); prove it via the general library.
  rw [sum_pointUpdate accounts bal]
  have : (∑ c ∈ accounts, ((if c = a then bal c + amt else bal c) - bal c))
      = ∑ c ∈ accounts, (if c = a then amt else 0) := by
    apply Finset.sum_congr rfl; intro c _; split <;> ring
  rw [this, sum_indicator accounts a amt hmem]

/-- `commit_cases` for the authority read-back: from a committed run it hands you the guard,
from which the authority conjunct is immediate. -/
example (accounts : Finset CellId) (bal bal' : CellId → ℤ) (a : CellId) (amt : ℤ)
    (h : toyExec accounts bal a amt = some bal') :
    0 ≤ amt := by
  unfold toyExec at h
  commit_cases h with ⟨hpos, hmem⟩
  exact hpos

end Dregg2.Conserve
