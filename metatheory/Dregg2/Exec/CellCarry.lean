/-
# Dregg2.Exec.CellCarry — the PARAMETRIC crown: the living cell carries ANY app invariant forever.

`Exec/CellReal.lean` crowned the REAL executor with the coinductive living cell `livingCellA` (a
`Boundary.TurnCoalg` over `execFullForestA`, the 46-effect per-asset auth-gated tree) and proved
`livingCellA_obs_invariant`: the per-asset CONSERVATION badge never drifts along the unbounded
adversarial trajectory `trajA`. That is ONE safety property. This module distills the GENERAL crown
hiding behind it — and that generality is the whole point of building a coinductive cell:

> **Conservation is just one instance.** `livingCellA_carries` proves that ANY *state* predicate
> `Good` preserved by a SINGLE living-cell step holds along the ENTIRE unbounded trajectory, under
> EVERY adversarial schedule. An app author writes a state predicate + a one-step preservation lemma
> (discharging it from the executor's per-step correctness — `fullActionInvA` and the
> `Exec/FullForest.lean` theorems, available exactly because the cell is the REAL machine) and gets
> *"holds forever"* for FREE. THIS is what makes the cell enough for **userspace verification** — not
> just the conservation warmup.

Three theorems, ascending in what they demonstrate:

* **`livingCellA_carries`** — the parametric trajectory-invariant carry (the general theorem): a
  one-step preservation `hpres` lifts to `∀ n, Good (trajA s sched n)` by plain induction on `n`,
  because `trajA`'s successor IS `cellNextA` definitionally and the schedule is an arbitrary
  `SchedA := Nat → ConservingForest` (no fairness, no bound — every interleaving).

* **`livingCellA_obs_invariant'`** — conservation re-derived THROUGH the parametric carry, showing the
  crown SUBSUMES the warmup (`Good := the per-asset badge is constant`; preservation = `cellObsA_next`).

* **`livingCellA_logMono`** — the **app-verification demo**: a NON-conservation safety carried forever.
  The audit/receipt log is **append-only** (`s.log.length ≤ (trajA …).log.length` at every index) —
  the canonical OS *"the log is the truth, never rewritten"* / non-repudiation invariant. Its one-step
  preservation is discharged from the executor's **ChainLink/ObsAdvance** structure (`execFullA` always
  does `s'.log = fullReceiptA fa :: s.log`, so the length only grows), NOT from the per-asset measure.
  This is the proof that `livingCellA_carries` is a verification SUBSTRATE, not a conservation gadget.
-/
import Dregg2.Exec.CellReal

namespace Dregg2.Exec

open Dregg2.Boundary
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest

/-! ## Step 1 — `livingCellA_carries`: the PARAMETRIC trajectory-invariant carry (THE general crown). -/

/-- **`livingCellA_carries` — the parametric crown.** Let `Good` be ANY predicate on the real
kernel state `RecChainedState`. If `Good` is preserved by a SINGLE living-cell step (`hpres : ∀ s cf,
Good s → Good (cellNextA s cf)` — the app's one-step obligation, dischargeable from the executor's
per-step correctness `fullActionInvA` / the `Exec/FullForest` theorems), then `Good` holds at EVERY
index of the unbounded trajectory `trajA s sched`, under EVERY adversarial schedule `sched : SchedA`.

This is the whole payoff of a coinductive cell: an app author supplies a state invariant + a one-step
lemma and receives *"holds forever, against any interleaving"* — the temporal νF face made reusable.
Conservation (`livingCellA_obs_invariant`) is the special case `Good := badge-constant`; the
append-only audit log (`livingCellA_logMono` below) is a NON-conservation special case. The proof is
plain `Nat` induction: `trajA`'s `succ` step is `livingCellA.next (trajA … k) (sched k)` =
`cellNextA (trajA … k) (sched k)` *definitionally*, so `hpres` discharges it directly. -/
theorem livingCellA_carries (Good : RecChainedState → Prop)
    (hpres : ∀ s cf, Good s → Good (cellNextA s cf))
    (s : RecChainedState) (hinit : Good s) (sched : SchedA) :
    ∀ n, Good (trajA s sched n) := by
  intro n
  induction n with
  | zero => exact hinit
  | succ k ih =>
      show Good (cellNextA (trajA s sched k) (sched k))
      exact hpres _ _ ih

/-! ## Step 2 — conservation as the TRIVIAL instance (the crown subsumes the CellReal warmup). -/

/-- **`livingCellA_obs_invariant'` — conservation, re-derived THROUGH the parametric carry.**
The per-asset badge `cellObsA` never drifts along the unbounded trajectory — identical to
`CellReal.livingCellA_obs_invariant`, but obtained as the `Good := (cellObsA · = cellObsA s)` instance
of `livingCellA_carries`, with the one-step obligation discharged by the proved `cellObsA_next`. This
exhibits the conservation crown as a SPECIAL CASE of the parametric crown: the warmup is subsumed. -/
theorem livingCellA_obs_invariant' (s : RecChainedState) (sched : SchedA) :
    ∀ n, cellObsA (trajA s sched n) = cellObsA s :=
  livingCellA_carries (fun s' => cellObsA s' = cellObsA s)
    (fun a cf h => by show cellObsA (cellNextA a cf) = cellObsA s; rw [cellObsA_next]; exact h)
    s rfl sched

/-! ## Step 3 — THE APP-VERIFICATION DEMO: a NON-conservation invariant carried forever.

The receipt/audit log is **APPEND-ONLY** — it never shrinks. This is the canonical OS / blockchain
"the log is the truth, never rewritten" safety, the auditability / non-repudiation invariant — and it
is a NON-conservation property: its proof reads the executor's **ChainLink/ObsAdvance** structure (the
log grows by exactly one `fullReceiptA` row each committed step), NEVER the per-asset conservation
measure `recTotalAsset`. It is THE TEMPLATE for userspace verification on this cell. -/

/-- **The turn-level log-monotone lemma.** A committed per-asset full-turn never SHRINKS the
receipt log: `s.log.length ≤ s'.log.length`. Proved by induction on the action list — each committed
`execFullA` step only EXTENDS the log (`execFullA_log_suffix`: `s.log <:+ s1.log`, append-only — one
row for non-recursive kinds, `1 + |inner|` for a committed exercise), so the length is monotone; the
empty turn is `le_refl`, and the inductive step chains by `le_trans`. This reads only the **ChainLink**
(append-only log shape) conjunct, NOT the conservation measure. -/
theorem execFullTurnA_logMono :
    ∀ (s s' : RecChainedState) (tt : List FullActionA),
      execFullTurnA s tt = some s' → s.log.length ≤ s'.log.length
  | s, s', [], h => by
      simp only [execFullTurnA, Option.some.injEq] at h; subst h; exact le_refl _
  | s, s', a :: rest, h => by
      simp only [execFullTurnA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          -- The head step only EXTENDS the log (append-only): `s.log <:+ s1.log` ⇒ length-monotone.
          -- Non-recursive kinds extend by exactly one row; a committed exercise by `1 + |inner|`.
          have hhead : s.log.length ≤ s1.log.length := (execFullA_log_suffix s s1 a ha).length_le
          exact le_trans hhead (execFullTurnA_logMono s1 s' rest h)

/-- **`execFullForestA_logMono` — the forest-level log-monotone lemma.** A committed
full-FOREST never shrinks the receipt log. Read straight through the pre-order bridge
`execFullForestA_eq_execFullTurnA` into the turn-level `execFullTurnA_logMono`. NON-conservation: it
asserts the audit chain only grows, using the executor's ChainLink/ObsAdvance shape — not the measure. -/
theorem execFullForestA_logMono (s s' : RecChainedState) (f : FullForestA)
    (h : execFullForestA s f = some s') : s.log.length ≤ s'.log.length := by
  rw [execFullForestA_eq_execFullTurnA] at h
  exact execFullTurnA_logMono s s' (lowerForestA f) h

/-- **`livingCellA_logMono` — THE userspace-verification payoff: the audit log is append-only
FOREVER.** Along the ENTIRE unbounded adversarial trajectory, the receipt log NEVER shrinks below its
initial length: `s.log.length ≤ (trajA s sched n).log.length` at EVERY index `n`. This is the OS
non-repudiation / auditability invariant — *"the log is the truth, never rewritten"* — and it is a
**NON-conservation** safety: it is carried by `livingCellA_carries` with `Good := (s.log.length ≤
·.log.length)`, whose one-step obligation is discharged from the executor's **ChainLink** structure
(`execFullForestA_logMono` on a commit) and the **stay-put self-loop** on a reject (`cellNextA` leaves
the state — and thus the log — UNCHANGED).

**THIS IS THE TEMPLATE.** An app provides a state predicate `Good` + a one-step preservation lemma
(discharged from `fullActionInvA` / the `Exec/FullForest` theorems wherever it needs the executor's
correctness) and `livingCellA_carries` hands back `∀ n, Good (trajA …)` — *"holds forever under any
schedule"*. Conservation is the instance `Good := badge-constant` (the per-asset measure); THIS is the
instance `Good := log-append-only` — a NON-conservation safety, the auditability /
non-repudiation invariant the per-asset measure cannot express. The coinductive cell is therefore
ENOUGH for userspace verification, not merely for conservation. -/
theorem livingCellA_logMono (s : RecChainedState) (sched : SchedA) :
    ∀ n, s.log.length ≤ (trajA s sched n).log.length :=
  livingCellA_carries (fun s' => s.log.length ≤ s'.log.length)
    (fun a cf h => by
      -- One-step preservation. `cellNextA a cf = (execFullForestA a cf.1).getD a`: on a COMMIT the
      -- forest log-monotone lemma grows the log (chain by `le_trans`); on a REJECT the state is the
      -- UNCHANGED `a`, so `≤` is preserved trivially.
      show s.log.length ≤ (cellNextA a cf).log.length
      unfold cellNextA
      cases hc : execFullForestA a cf.1 with
      | some a' => simp only [Option.getD_some]
                   exact le_trans h (execFullForestA_logMono a a' cf.1 hc)
      | none    => simp only [Option.getD_none]; exact h)
    s (le_refl _) sched

/-! ## It runs (`#eval`) — the log length STRICTLY grows on a real committed transfer (non-vacuity).

The append-only invariant would be vacuous if no turn ever appended. `CellReal.transferCF` (actor 0
transfers 30 of asset 0 from cell 0 to cell 1, a real commit on `fma0`) appends exactly one
`fullReceiptA` row: the log goes `0 → 1`. So `livingCellA_logMono` is non-trivially true (it bounds a
strictly-growing quantity), and `livingCellA_carries` is exercised by a property that moves. -/

#guard ((execFullForestA fma0 transferCF.1).map (fun s' => s'.log.length)) == some 1  --  some 1 (grew from 0)
#guard (fma0.log.length) == 0  --  0   (BEFORE — strictly less)
#guard ((execFullForestA fma0 transferCF.1).map (fun s' => decide (fma0.log.length < s'.log.length))) == some true  --  some true
#guard ((execFullForestA fma0 transferCF.1).map (fun s' => decide (fma0.log.length ≤ s'.log.length))) == some true  --  some true (the carried ≤)

/-! ## Axiom hygiene — the parametric crown + the NON-conservation demo pinned to the kernel triple. -/

#assert_axioms livingCellA_carries
#assert_axioms execFullTurnA_logMono
#assert_axioms execFullForestA_logMono
#assert_axioms livingCellA_logMono
#assert_axioms livingCellA_obs_invariant'

end Dregg2.Exec
