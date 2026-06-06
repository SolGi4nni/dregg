/-
# Dregg2.Verify.Tactics — the Hatchery's boilerplate-killers (HATCHERY.md Tier 1).

Two domain tactics that compress the `livingCellA_carries` skeleton every shipped crown re-types by
hand (`HATCHERY.md` §1–§2):

* **`carry_forever Good`** — the front-end. Reduces a temporal goal `∀ n, Good' (trajA s sched n)` to
  the app author's TWO real obligations via `Exec/CellCarry.livingCellA_carries`:
    - `hpres : ∀ a cf, Good' a → Good' (cellNextA a cf)`  (the one-step preservation), and
    - `hinit : Good' s`                                    (the base case).
  The unbounded-time, every-schedule `νF` carry is then FREE. `s` and `sched` are unified silently
  from the goal — the author never spells them out.

* **`exec_frame (grow)?`** — THE keystone (`HATCHERY.md §2`). Discharges the `hpres` goal mechanically:
    1. `intro s cf hgood`; expose the executor via `cellNextA s cf = (execFullForestA s cf.1).getD s`;
    2. split on the commit/reject of `execFullForestA s cf.1`;
    3. the **reject (stay-put) arm is UNIVERSAL** — `getD_none` makes `cellNextA s cf = s`, so the
       invariant is preserved unchanged (`exact hgood`). This arm is closed for EVERY `Good`, always;
    4. the **commit arm** carries the content. `exec_frame` tries, in order:
         a. a SUPPLIED forest-grow lemma `grow : ∀ s s' f, execFullForestA s f = some s' → R (π s) (π s')`,
            chained with the baseline by `Trans.trans` (the `cellNextA_carries_rel` body), then
         b. `aesop (rule_sets := [Dregg2])` — the tagged frame family + `List.Subset.trans` close the
            registry-grow crowns with NO supplied lemma, then
         c. **HAND-BACK**: if neither closes it, the commit goal is LEFT OPEN as the current goal for
            the caller to discharge by hand. `exec_frame` NEVER fakes a close — it is honest by
            construction (no `sorry`, no `skip`-that-hides; the leftover is a real open goal that fails
            the build until addressed).

The §3 GATE reproduces, via these tactics, the one-step obligation of the hand-written crowns
`Exec.livingCellA_logMono` (`Exec/CellCarry.lean:135`) and `Apps.Identity.livingCellA_revoked_grow`
(`Apps/Identity.lean:572` / `…_identity_revoked_forever:593`) — proving the SAME forever statements with
`carry_forever`/`exec_frame` instead of the bespoke proofs. The reproduced theorems are `#assert_axioms`-
pinned to the kernel triple `{propext, Classical.choice, Quot.sound}`, certifying the tactics emit
ordinary kernel-checked terms with NO new axiom and NO `sorry`/`native_decide`/SMT oracle.

Substrate: Lean 4.30 `elab`/`macro` + `aesop` (an existing v4.30 dependency). No new lake deps.
-/
import Dregg2.Verify.Frames
import Dregg2.Exec.CellExecutor
import Dregg2.Tactics

namespace Dregg2.Verify

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (fma0)
open Dregg2.Exec.FullForest
open Lean Elab Tactic

/-! ## §1 — `carry_forever`: discharge the `livingCellA_carries` plumbing, leave `hpres` + `hinit`.

`refine livingCellA_carries $Good ?hpres _ ?hinit _` against a goal `∀ n, Good' (trajA s sched n)`:
`livingCellA_carries`'s conclusion is `∀ n, Good (trajA s sched n)`, so unification fixes `Good := Good'`
and the two `_` holes for `s`/`sched` from the goal — leaving exactly the named goals `hpres` and
`hinit`. (Using `_`, not `?_`, for `s`/`sched` keeps them implicit unification metavariables rather than
surfacing them as synthetic side-goals.) -/

/-- **`carry_forever Good`** — reduce `∀ n, Good (trajA s sched n)` to the one-step `hpres` and base
`hinit` via `livingCellA_carries`. The unbounded-time / every-schedule carry is supplied for free; the
author proves only the two named subgoals (`hpres` almost always by `exec_frame`). -/
macro "carry_forever" Good:term : tactic =>
  `(tactic| refine livingCellA_carries $Good ?hpres _ ?hinit _)

/-! ## §2 — `exec_frame`: the executor case-split + universal reject arm + frame/grow commit arm.

The split uses `rcases hc : execFullForestA s cf.1 with _ | s'` (the *flat* two-goal form, NOT the
`cases … with` alt form — the latter forces every branch to close inside the block, trapping the
handed-back goal; the flat form lets the unclosed commit goal ESCAPE to the caller). The raw binder
names (`s`/`cf`/`hgood`/`s'`/`hc`) are introduced unhygienically (via `mkIdent`) so the supplied
forest-grow term and the caller's hand-back closer can both refer to them. -/

/-- **`exec_frame (grow)?`** — prove `∀ s cf, Good s → Good (cellNextA s cf)`. Closes the universal
stay-put arm (`getD_none`), and on the commit arm tries `Trans.trans hgood (grow …)` (if a forest-grow
lemma is supplied), then `aesop (rule_sets := [Dregg2])` (the tagged frame family), else HANDS BACK the
commit goal (honest — never a hidden `sorry`).

The optional `grow` is parsed with `colGt` so it consumes a term ONLY when indented past the tactic —
a following `case`/tactic on the same or lesser column is NOT swallowed. -/
elab "exec_frame" grow?:(ppSpace colGt term)? : tactic => do
  -- raw (unhygienic) binders shared between the prefix split, the grow term, and the caller's closer.
  let s     := mkIdent `s
  let cf    := mkIdent `cf
  let hgood := mkIdent `hgood
  let hc    := mkIdent `hc
  let s'    := mkIdent `s'
  -- 1. intro the universally-quantified one-step obligation.
  evalTactic (← `(tactic| intro $s:ident $cf:ident $hgood:ident))
  -- 2. expose the executor: `cellNextA s cf = (execFullForestA s cf.1).getD s`.
  evalTactic (← `(tactic| simp only [cellNextA]))
  -- 3. split commit/reject (FLAT form so the commit goal can escape on hand-back).
  evalTactic (← `(tactic| rcases $hc:ident : execFullForestA $s:ident ($cf:ident).1 with _ | $s':ident))
  -- 4. THE UNIVERSAL REJECT ARM — stay-put self-loop: `cellNextA = s`, invariant preserved unchanged.
  evalTactic (← `(tactic| · simp only [Option.getD_none]; exact $hgood:ident))
  -- 5. expose the commit value `(some s').getD s = s'`.
  evalTactic (← `(tactic| simp only [Option.getD_some]))
  -- 6. THE COMMIT ARM — try the supplied grower, then the rule-set, else HAND BACK (`skip`: the goal
  --    survives as the current goal; nothing is faked).
  let closer ← match grow? with
    | some g => `(tactic| first
        | exact Trans.trans $hgood:ident ($g $s:ident $s':ident ($cf:ident).1 $hc:ident)
        | aesop (rule_sets := [Dregg2])
        | skip)
    | none   => `(tactic| first
        | aesop (rule_sets := [Dregg2])
        | skip)
  evalTactic closer

/-! ## §3 — THE GATE: reproduce the hand-written crowns' one-step obligations via the tactics.

Each gate theorem proves the SAME `∀ n, Good (trajA …)` statement as a shipped hand crown, but the
`hpres` is discharged by `exec_frame` (and the whole plumbing by `carry_forever`). The reproduced
theorems are `#assert_axioms`-pinned at the foot — certifying the tactic-emitted terms are kernel-clean.
-/

/-- **GATE (a) — `logMono_via_tactics` reproduces `Exec.livingCellA_logMono`** (`Exec/CellCarry.lean:135`).
The append-only audit-log lower bound `s.log.length ≤ (trajA s sched n).log.length`, FOREVER, proved via
`carry_forever` + `exec_frame execFullForestA_logMono`. The `exec_frame` commit arm chains the baseline
`≤` with the forest log-monotone lemma by `Trans.trans` (`Nat`'s `≤` is `Trans`); the reject arm is the
universal stay-put close. Same statement as the hand crown, mechanized one-step. -/
theorem logMono_via_tactics (s : RecChainedState) (sched : SchedA) :
    ∀ n, s.log.length ≤ (trajA s sched n).log.length := by
  carry_forever (fun s' => s.log.length ≤ s'.log.length)
  case hpres => exec_frame execFullForestA_logMono
  case hinit => exact le_refl _

/-- **GATE (b) — `revoked_grow_via_tactics` reproduces `Apps.Identity.livingCellA_revoked_grow`**
(`Apps/Identity.lean:572`). Permanent revocation `rev0 ⊆ (trajA s sched n).kernel.revoked`, FOREVER,
via `carry_forever` + `exec_frame …execFullForestA_revoked_grow`. The commit arm chains by
`List.Subset.trans`; the reject arm is the universal close. -/
theorem revoked_grow_via_tactics (rev0 : List Nat) (s : RecChainedState)
    (hinit : rev0 ⊆ s.kernel.revoked) (sched : SchedA) :
    ∀ n, rev0 ⊆ (trajA s sched n).kernel.revoked := by
  carry_forever (fun s' => rev0 ⊆ s'.kernel.revoked)
  case hpres => exec_frame Dregg2.Apps.Identity.execFullForestA_revoked_grow
  case hinit => exact hinit

/-- **GATE (b′) — `identity_revoked_forever_via_tactics` reproduces
`Apps.Identity.livingCellA_identity_revoked_forever`** (`Apps/Identity.lean:593`): a revoked credential
stays revoked forever. The single-element instance of the gate-(b) crown — exactly the hand theorem's
shape, built on the tactic-reproduced `revoked_grow_via_tactics`. -/
theorem identity_revoked_forever_via_tactics (credNul : Nat) (s : RecChainedState)
    (hinit : credNul ∈ s.kernel.revoked) (sched : SchedA) :
    ∀ n, credNul ∈ (trajA s sched n).kernel.revoked := by
  intro n
  have h := revoked_grow_via_tactics [credNul] s
    (by intro x hx; rw [List.mem_singleton] at hx; subst hx; exact hinit) sched n
  exact h (List.mem_singleton.mpr rfl)

/-- **GATE (auto) — `commitments_persist_via_auto` reproduces `Exec.livingCellA_commitments_persist`**
with `exec_frame` carrying NO supplied lemma: the `[Dregg2]` rule-set alone (the tagged forest-grow
frame + `List.Subset.trans`) closes the commit arm. Demonstrates Tier-2 search (HATCHERY.md §2):
`dregg_auto`-style discharge of a grow-only registry crown with zero hand input. -/
theorem commitments_persist_via_auto (com0 : List Nat) (s : RecChainedState) (sched : SchedA)
    (hinit : com0 ⊆ s.kernel.commitments) :
    ∀ n, com0 ⊆ (trajA s sched n).kernel.commitments := by
  carry_forever (fun s' => com0 ⊆ s'.kernel.commitments)
  case hpres => exec_frame
  case hinit => exact hinit

/-! ## §4 — The HONEST HAND-BACK, demonstrated (HATCHERY.md §5 "honest by construction").

`exec_frame` with NO supplied lemma cannot close the `log.length` commit arm — `aesop (rule_sets :=
[Dregg2])` knows the registry-subset frames but not `Nat`'s `le_trans` chained with
`execFullForestA_logMono`. So it HANDS BACK the commit goal: the `simp only [Option.getD_some]`-exposed
`s.log.length ≤ s'.log.length`, with `hgood`/`s`/`s'`/`cf`/`hc` in context. We then close it by hand,
*proving the goal was genuinely LEFT* (never `sorry`-faked: had `exec_frame` faked a close, the trailing
`exact` would error with "no goals"; had it errored, the build would fail here). This is the Hatchery
promise — kill the 45 boring arms + the stay-put arm, hand back the ONE real obligation. -/
theorem logMono_handback_demo (s : RecChainedState) (sched : SchedA) :
    ∀ n, s.log.length ≤ (trajA s sched n).log.length := by
  carry_forever (fun s' => s.log.length ≤ s'.log.length)
  case hpres =>
    exec_frame                 -- closes the reject arm; HANDS BACK the commit goal:
    -- the handed-back commit obligation, closed by the one content lemma (referencing the raw binders):
    exact le_trans hgood (execFullForestA_logMono s s' cf.1 hc)
  case hinit => exact le_refl _

/-! ## §5 — Regression equality: the tactic-built crowns are the hand crowns (defeq witnesses).

Each tactic-reproduced forever theorem is propositionally the SAME statement as the shipped hand crown
— witnessed by an `example` that closes the hand-crown's type with the tactic theorem (and vice-versa).
This is HATCHERY.md's H1 gate ("reproduce one crown's `hpres` with `by exec_frame`"), made into a
build-checked regression: if the tactics ever drifted from the hand proofs' statements, these break. -/

/-- The tactic log-mono crown discharges the hand crown's statement verbatim. -/
example (s : RecChainedState) (sched : SchedA) :
    ∀ n, s.log.length ≤ (trajA s sched n).log.length :=
  logMono_via_tactics s sched

/-- …and the hand crown discharges the tactic statement — same proposition, both directions. -/
example (s : RecChainedState) (sched : SchedA) :
    ∀ n, s.log.length ≤ (trajA s sched n).log.length :=
  Dregg2.Exec.livingCellA_logMono s sched

/-- The tactic revocation crown is the hand crown `livingCellA_identity_revoked_forever` statement. -/
example (credNul : Nat) (s : RecChainedState) (hinit : credNul ∈ s.kernel.revoked) (sched : SchedA) :
    ∀ n, credNul ∈ (trajA s sched n).kernel.revoked :=
  identity_revoked_forever_via_tactics credNul s hinit sched

/-- …and the hand crown discharges the tactic statement. -/
example (credNul : Nat) (s : RecChainedState) (hinit : credNul ∈ s.kernel.revoked) (sched : SchedA) :
    ∀ n, credNul ∈ (trajA s sched n).kernel.revoked :=
  Dregg2.Apps.Identity.livingCellA_identity_revoked_forever credNul s hinit sched

/-! ## §6 — Non-vacuity guards — the tactic-built crowns bind quantities that genuinely move. -/

#guard ((execFullForestA fma0 transferCF.1).map
          (fun s' => decide (fma0.log.length < s'.log.length)) == some true)
#guard (Dregg2.Apps.Identity.fmaRevoked.kernel.revoked.contains 42)
#guard (Dregg2.Apps.Identity.fmaRevoked.kernel.revoked.contains 99 == false)

/-! ## §7 — Axiom hygiene — the tactic-reproduced crowns pinned to the kernel triple (NO `sorryAx`). -/

#assert_axioms logMono_via_tactics
#assert_axioms revoked_grow_via_tactics
#assert_axioms identity_revoked_forever_via_tactics
#assert_axioms commitments_persist_via_auto
#assert_axioms logMono_handback_demo

/-! ## §8 — Production Hatchery (`CellExecutor.production` / `execForestG`).

`carry_forever_production` + `exec_frame_production` are the production counterparts of §1–§2.
`carry_foreverG` / `exec_frameG` remain as aliases in `TacticsG.lean` (deprecated import path). -/

namespace Production

open Dregg2.Exec.StarbridgeGated
open Dregg2.Exec.StarbridgeGated (execForestG)

macro "carry_forever_production" Good:term : tactic =>
  `(tactic| refine livingCellG_carries $Good ?hpres _ ?hinit _)

/-- Production executor case-split (mirrors `exec_frame` on `cellNextG` / `execForestG`). -/
elab "exec_frame_production" grow?:(ppSpace colGt term)? : tactic => do
  let s     := mkIdent `s
  let cg    := mkIdent `cg
  let hgood := mkIdent `hgood
  let hc    := mkIdent `hc
  let s'    := mkIdent `s'
  evalTactic (← `(tactic| intro $s:ident $cg:ident $hgood:ident))
  evalTactic (← `(tactic| dsimp [cellNextG]))
  evalTactic (← `(tactic| rcases $hc:ident : execForestG $s:ident ($cg:ident).val with _ | $s':ident))
  evalTactic (← `(tactic| · simp only [Option.getD_none]; exact $hgood:ident))
  evalTactic (← `(tactic| simp only [Option.getD_some]))
  let closer ← match grow? with
    | some g => `(tactic| first
        | exact Trans.trans $hgood:ident ($g $s:ident $s':ident ($cg:ident).val $hc:ident)
        | aesop (rule_sets := [Dregg2])
        | dregg_auto
        | skip)
    | none   => `(tactic| first
        | aesop (rule_sets := [Dregg2])
        | dregg_auto
        | skip)
  evalTactic closer

theorem logMono_via_tactics (s : RecChainedState) (sched : SchedG) :
    ∀ n, s.log.length ≤ (trajG s sched n).log.length := by
  carry_forever_production (fun s' => s.log.length ≤ s'.log.length)
  case hpres => exec_frame_production Production.execForestG_logMono
  case hinit => exact le_refl _

theorem revoked_grow_via_tactics (rev0 : List Nat) (s : RecChainedState)
    (hinit : rev0 ⊆ s.kernel.revoked) (sched : SchedG) :
    ∀ n, rev0 ⊆ (trajG s sched n).kernel.revoked := by
  carry_forever_production (fun s' => rev0 ⊆ s'.kernel.revoked)
  case hpres => exec_frame_production Production.execForestG_revoked_subset_grow
  case hinit => exact hinit

theorem identity_revoked_forever_via_tactics (credNul : Nat) (s : RecChainedState)
    (hinit : credNul ∈ s.kernel.revoked) (sched : SchedG) :
    ∀ n, credNul ∈ (trajG s sched n).kernel.revoked := by
  intro n
  have h := revoked_grow_via_tactics [credNul] s
    (by intro x hx; rw [List.mem_singleton] at hx; subst hx; exact hinit) sched n
  exact h (List.mem_singleton.mpr rfl)

#assert_axioms logMono_via_tactics
#assert_axioms revoked_grow_via_tactics
#assert_axioms identity_revoked_forever_via_tactics

end Production

end Dregg2.Verify
