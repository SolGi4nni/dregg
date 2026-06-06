/-
# Dregg2.Verify.Frames — the Hatchery's frame library (HATCHERY.md Tier 2).

The Hatchery thesis (`HATCHERY.md` §1): every shipped "crown" is the SAME proof retyped — a 46-way
`FullActionA` case split where ~45 arms leave a registry field UNTOUCHED ("frame") and one arm GROWS it.
This module is the reusable half of that skeleton:

1. **The frame family, tagged into the `[Dregg2]` aesop rule-set.** The per-mutator / per-effect
   "effect X leaves field Y alone" lemmas already proved across `Exec/CellCommit.lean`,
   `Exec/CellNullifier.lean`, `Exec/CellConfine.lean`, `Exec/Apps/Identity.lean` are re-exported and
   registered with `@[aesop safe apply (rule_sets := [Dregg2])]` (the rule-set is declared in
   `Dregg2/Catalog.lean`). Tagged once here, discovered forever by `aesop (rule_sets := [Dregg2])`
   and by the `exec_frame` tactic (`Dregg2/Verify/Tactics.lean`). These are the `@[dregg_frame]`
   candidates of `HATCHERY.md §2`.

2. **The reusable forest-monotone combinator** — the generalization of the EXISTING
   `execFullForestA_logMono` (`Exec/CellCarry.lean:114`) one-step proof. Every crown's `hpres`
   (`CellCommit.livingCellA_commitments_persist`, `CellNullifier.livingCellA_no_double_spend`,
   `Identity.livingCellA_revoked_grow`, `CellCarry.livingCellA_logMono`) re-proves, BY HAND, the SAME
   one-step body:

   ```
   show R base (proj (cellNextA a cf));  unfold cellNextA
   cases execFullForestA a cf.1 with
   | some a' => Option.getD_some; exact trans h (forestGrow … hc)   -- COMMIT: the field grows
   | none    => Option.getD_none;  exact h                          -- REJECT: stay-put self-loop
   ```

   `cellNextA_carries_rel` packages this body ONCE, parametric in a `Trans` relation `R` (covering
   BOTH the `⊆`-shaped registry crowns AND the `≤`-shaped log-length crown — both `Trans` instances)
   and a `proj`ection with a forest-grow witness. `livingCellA_carries_rel` then feeds it to
   `Exec/CellCarry.livingCellA_carries` to obtain the full *"holds forever, every schedule"* theorem.
   The hand proofs become a one-liner; new monotone fields inherit the combinator for free.

We keep as CONCRETE instances the four monotone registries whose forest-grow lemmas already exist
(`commitments`, `nullifiers`, `revoked` as `⊆`; `log.length` as `≤`), since their `forestGrow`
witnesses are theorems we merely supply — the combinator does not re-prove them.

Discipline: NO `sorry`/`admit`/`native_decide`/SMT. Every theorem is `#assert_axioms`-pinned to the
kernel triple `{propext, Classical.choice, Quot.sound}` at the foot of the file.
-/
import Dregg2.Exec.CellCommit
import Dregg2.Exec.CellNullifier
import Dregg2.Exec.CellConfine
import Dregg2.Apps.Identity
import Dregg2.Exec.CellExecutor
import Dregg2.Catalog          -- declares the `[Dregg2]` aesop rule-set + `@[dregg_frame]`
import Aesop

namespace Dregg2.Verify

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Authority
open Dregg2.Exec.StarbridgeGated (DForest execForestG execForestG_erases eraseForestG)

/-! ## §1 — The reusable forest-monotone combinator (generalizing `execFullForestA_logMono`).

`execFullForestA_logMono` (`Exec/CellCarry.lean:114`) and its three siblings each prove a per-step
preservation and then re-do the IDENTICAL `cellNextA` commit/stay-put case split inside the crown's
`hpres`. We lift that case split out ONCE. The key observation: the body uses only

* `cellNextA s cf = (execFullForestA s cf.1).getD s`  (definitional, `Exec/CellReal.lean:41`), and
* a `Trans` step to chain the baseline `R base (proj s)` with the commit's `R (proj s) (proj s')`.

Both `List.Subset` (`⊆`) and `Nat`'s `≤` carry `Trans` instances, so a SINGLE combinator covers every
shipped crown's one-step obligation. -/

/-- **`cellNextA_carries_rel` (PROVED) — the one-step packager.** Let `R` be any transitive relation
on `α`, `proj : RecChainedState → α` a state projection, and `forestGrow` a witness that a committed
full forest moves `proj` forward along `R` (`R (proj s) (proj s')`). Then a single living-cell step
preserves the baseline relation `R base (proj ·)`:

* on a **COMMIT** (`execFullForestA s cf.1 = some s'`) the field steps forward (`forestGrow`), chained
  with the baseline by `Trans.trans`;
* on a **REJECT** (`= none`) `cellNextA` is the stay-put self-loop (`getD_none`), so the baseline is
  preserved unchanged.

This is the verbatim body that `CellCommit`/`CellNullifier`/`Identity`/`CellCarry` each hand-wrote;
here it is proved ONCE. -/
theorem cellNextA_carries_rel {α : Type _} (R : α → α → Prop) [Trans R R R]
    (proj : RecChainedState → α)
    (forestGrow : ∀ (s s' : RecChainedState) (f : FullForestA),
      execFullForestA s f = some s' → R (proj s) (proj s'))
    {base : α} {s : RecChainedState} (h : R base (proj s)) (cf : ConservingForest) :
    R base (proj (cellNextA s cf)) := by
  unfold cellNextA
  cases hc : execFullForestA s cf.1 with
  | some s' => simp only [Option.getD_some]
               exact Trans.trans h (forestGrow s s' cf.1 hc)
  | none    => simp only [Option.getD_none]; exact h

/-- **`livingCellA_carries_rel` (PROVED) — the forever combinator.** The full Hatchery payoff for a
monotone field: given a `Trans` relation `R`, a projection `proj`, and a forest-grow witness, ANY
baseline `R base (proj s)` is preserved at EVERY index of the unbounded adversarial trajectory `trajA s
sched`, under EVERY schedule. Obtained by feeding `cellNextA_carries_rel` (the one-step obligation) to
`Exec/CellCarry.livingCellA_carries` (the parametric coinductive crown). This is the generalization the
Hatchery promised: one combinator subsumes `livingCellA_commitments_persist`,
`livingCellA_no_double_spend`, `livingCellA_revoked_grow`, and `livingCellA_logMono`. -/
theorem livingCellA_carries_rel {α : Type _} (R : α → α → Prop) [Trans R R R]
    (proj : RecChainedState → α)
    (forestGrow : ∀ (s s' : RecChainedState) (f : FullForestA),
      execFullForestA s f = some s' → R (proj s) (proj s'))
    (base : α) (s : RecChainedState) (hinit : R base (proj s)) (sched : SchedA) :
    ∀ n, R base (proj (trajA s sched n)) :=
  livingCellA_carries (fun s' => R base (proj s'))
    (fun _a cf h => cellNextA_carries_rel R proj forestGrow h cf)
    s hinit sched

/-! ## §2 — Concrete monotone-registry instances (the four shipped grow-only fields).

The combinator's `forestGrow` argument is supplied by the EXISTING forest-grow theorems (we do not
re-prove them — `Frames` collects them). Each instance is the combinator at a concrete `(R, proj)`:

| field                  | relation `R`   | forest-grow witness                       |
|------------------------|----------------|-------------------------------------------|
| `kernel.commitments`   | `⊆`            | `execFullForestA_commitments_grow`        |
| `kernel.nullifiers`    | `⊆`            | `execFullForestA_nullifiers_grow`         |
| `kernel.revoked`       | `⊆`            | `execFullForestA_revoked_grow`            |
| `log.length`           | `≤` (`Nat`)    | `execFullForestA_logMono`                 |
-/

/-- **`execFullForestA_commitments_grow_proj`** — `commitments` forest-grow in the combinator's
projection shape (`proj := (·.kernel.commitments)`). A thin re-statement of
`Exec.execFullForestA_commitments_grow` for direct use as `cellNextA_carries_rel`'s `forestGrow`. -/
theorem execFullForestA_commitments_grow_proj (s s' : RecChainedState) (f : FullForestA)
    (h : execFullForestA s f = some s') :
    (· ⊆ ·) s.kernel.commitments s'.kernel.commitments :=
  execFullForestA_commitments_grow s s' f h

/-- **`execFullForestA_nullifiers_grow_proj`** — `nullifiers` forest-grow in projection shape. -/
theorem execFullForestA_nullifiers_grow_proj (s s' : RecChainedState) (f : FullForestA)
    (h : execFullForestA s f = some s') :
    (· ⊆ ·) s.kernel.nullifiers s'.kernel.nullifiers :=
  execFullForestA_nullifiers_grow s s' f h

/-- **`execFullForestA_revoked_grow_proj`** — `revoked` forest-grow in projection shape. -/
theorem execFullForestA_revoked_grow_proj (s s' : RecChainedState) (f : FullForestA)
    (h : execFullForestA s f = some s') :
    (· ⊆ ·) s.kernel.revoked s'.kernel.revoked :=
  Dregg2.Apps.Identity.execFullForestA_revoked_grow s s' f h

/-- **`commitments_grow_forever` — the commitment-persistence crown, via the combinator.** Reproduces
`Exec.livingCellA_commitments_persist` as the `(⊆, ·.kernel.commitments)` instance of
`livingCellA_carries_rel`. A grow-only set carried forever; the hand-written crown becomes one line. -/
theorem commitments_grow_forever (com0 : List Nat) (s : RecChainedState) (sched : SchedA)
    (hinit : com0 ⊆ s.kernel.commitments) :
    ∀ n, com0 ⊆ (trajA s sched n).kernel.commitments :=
  livingCellA_carries_rel (· ⊆ ·) (·.kernel.commitments)
    execFullForestA_commitments_grow_proj com0 s hinit sched

/-- **`nullifiers_grow_forever` — no-double-spend, via the combinator.** The `(⊆, ·.kernel.nullifiers)`
instance — reproduces `Exec.livingCellA_no_double_spend`. -/
theorem nullifiers_grow_forever (nul0 : List Nat) (s : RecChainedState) (sched : SchedA)
    (hinit : nul0 ⊆ s.kernel.nullifiers) :
    ∀ n, nul0 ⊆ (trajA s sched n).kernel.nullifiers :=
  livingCellA_carries_rel (· ⊆ ·) (·.kernel.nullifiers)
    execFullForestA_nullifiers_grow_proj nul0 s hinit sched

/-- **`revoked_grow_forever` — permanent revocation, via the combinator.** The `(⊆, ·.kernel.revoked)`
instance — reproduces `Identity.livingCellA_revoked_grow`. -/
theorem revoked_grow_forever (rev0 : List Nat) (s : RecChainedState) (sched : SchedA)
    (hinit : rev0 ⊆ s.kernel.revoked) :
    ∀ n, rev0 ⊆ (trajA s sched n).kernel.revoked :=
  livingCellA_carries_rel (· ⊆ ·) (·.kernel.revoked)
    execFullForestA_revoked_grow_proj rev0 s hinit sched

/-- **`logLen_grow_forever` — the append-only audit log, via the combinator.** The `(≤, ·.log.length)`
instance over `Nat` — reproduces `Exec.livingCellA_logMono`. Demonstrates the combinator is NOT
subset-specific: `Nat`'s `≤` is `Trans` too, so the SAME machinery carries the log-length lower bound. -/
theorem logLen_grow_forever (s : RecChainedState) (sched : SchedA) :
    ∀ n, s.log.length ≤ (trajA s sched n).log.length :=
  livingCellA_carries_rel (· ≤ ·) (·.log.length)
    execFullForestA_logMono s.log.length s (le_refl _) sched

/-! ## §3 — The frame family, tagged into the `[Dregg2]` aesop rule-set.

The `_commitments = `-shaped per-mutator frames (`Exec/CellCommit.lean:64-289`) and the structural
closers are registered for `aesop (rule_sets := [Dregg2])` and for the `exec_frame` tactic
(`Dregg2/Verify/Tactics.lean`). The `_eq`-shaped frames are `safe apply` (they discharge "this mutator
leaves `commitments` fixed" subgoals); the canonical grower `List.subset_cons_self` and the reflexivity
bridge are `safe apply` too, so an `aesop` call on a grow-only commitment goal can both frame the
untouched arms and close the one growing arm.

We register the COMMITMENTS frame family (the most complete `_eq`-shaped set in the tree) plus the
cross-field forest-grow lifts as the rule-set's grow lemmas. The other fields' per-mutator frames
(`_caps`, `_revoked`, `_nullifiers`) are stated `private`/inline in their home modules; the forest-level
grow lemmas below are the reusable, public, aesop-visible entry points the tactic actually dispatches. -/

-- The transitivity bridge: lets `aesop (rule_sets := [Dregg2])` CHAIN a baseline `base ⊆ proj s`
-- (in context) with a forest-grow `proj s ⊆ proj s'` to close a commit-arm goal `base ⊆ proj s'`.
-- `unsafe` (not `safe`) because `Subset.trans` introduces a metavariable middle term `?m` that aesop
-- must instantiate by the grow lemma + the context hypothesis — exactly the `exec_frame` some-arm.
attribute [aesop unsafe 50% apply (rule_sets := [Dregg2])] List.Subset.trans

attribute [aesop safe apply (rule_sets := [Dregg2])]
  -- the commit/reflexivity bridge and the canonical grower
  subset_of_commitments_eq
  List.subset_cons_self
  List.Subset.refl
  -- per-mutator COMMITMENTS frames (the `k'.commitments = k.commitments` family)
  recKExecAsset_commitments
  recKMintAsset_commitments
  recKBurnAsset_commitments
  recKDelegate_commitments
  recKDelegateAtten_commitments
  noteSpendNullifier_commitments
  createEscrowKAsset_commitments
  releaseEscrowKAsset_commitments
  refundEscrowKAsset_commitments
  bridgeLockKAsset_commitments
  bridgeFinalizeKAsset_commitments
  bridgeCancelKAsset_commitments
  queueAllocateK_commitments
  queueEnqueueK_commitments
  queueDequeueK_commitments
  queueEnqueueDepositK_commitments
  queueDequeueRefundK_commitments
  queueResizeK_commitments
  swissExportK_commitments
  swissEnlivenK_commitments
  swissHandoffK_commitments
  swissDropK_commitments

attribute [aesop safe apply (rule_sets := [Dregg2])]
  -- the reflexivity-shaped frames (proved by `rfl`; `safe apply` lets aesop close the "= k" subgoal)
  recKRevokeTarget_commitments
  writeField_commitments
  makeSovereignKernel_commitments
  createCellIntoAsset_commitments
  createEscrowRawAsset_commitments
  settleEscrowRawAsset_commitments

attribute [aesop safe apply (rule_sets := [Dregg2])]
  -- the FOREST-level grow lifts — the reusable public entry points the crowns stand on.
  -- Tagged so `aesop (rule_sets := [Dregg2])` can discharge a commit-arm `proj s ⊆ proj s'` goal.
  execFullForestA_commitments_grow
  execFullForestA_nullifiers_grow
  Dregg2.Apps.Identity.execFullForestA_revoked_grow

/-! ## §4 — Non-vacuity guards — the combinator-derived crowns bind quantities that GENUINELY MOVE.

A real `noteCreateA` grows `commitments`; a real `noteSpendA` grows `nullifiers`; a real transfer
strictly grows `log.length`. Each `#guard` fails the build if the carried bound stops being substantive. -/

#guard ((execFullForestA fma0 noteCreateFA).map (fun s' => s'.kernel.commitments) == some [42])
#guard ((execFullForestA fma0 noteCreateFA).map
          (fun s' => decide (([42] : List Nat) ⊆ s'.kernel.commitments)) == some true)
#guard ((execFullForestA fma0 spendCF).map (fun s' => s'.kernel.nullifiers) == some [77])
#guard ((execFullForestA fma0 transferCF.1).map
          (fun s' => decide (fma0.log.length < s'.log.length)) == some true)

/-! ## §5 — Axiom hygiene — the combinator + every derived crown pinned to the kernel triple. -/

#assert_axioms cellNextA_carries_rel
#assert_axioms livingCellA_carries_rel
#assert_axioms commitments_grow_forever
#assert_axioms nullifiers_grow_forever
#assert_axioms revoked_grow_forever
#assert_axioms logLen_grow_forever

/-! ## §6 — Production forest-grow frames (`execForestG`, erasure-lifted).

The public Hatchery frame family for `CellExecutor.production`. Kernel-forest grow lemmas are reused
via `execForestG_erases`; admission-only `none` arms are the universal stay-put close. -/

namespace Production

open Dregg2.Exec.StarbridgeGated
open Dregg2.Exec.StarbridgeGated (DForest execForestG execForestG_erases eraseForestG)

theorem execForestG_revoked_subset_grow (s s' : RecChainedState) (f : DForest)
    (h : execForestG s f = some s') :
    s.kernel.revoked ⊆ s'.kernel.revoked := by
  have er := execForestG_erases s s' f h
  exact Dregg2.Apps.Identity.execFullForestA_revoked_grow s s' (eraseForestG f) er

theorem execForestG_commitments_grow (s s' : RecChainedState) (f : DForest)
    (h : execForestG s f = some s') :
    s.kernel.commitments ⊆ s'.kernel.commitments := by
  have er := execForestG_erases s s' f h
  exact execFullForestA_commitments_grow s s' (eraseForestG f) er

theorem execForestG_nullifiers_grow (s s' : RecChainedState) (f : DForest)
    (h : execForestG s f = some s') :
    s.kernel.nullifiers ⊆ s'.kernel.nullifiers := by
  have er := execForestG_erases s s' f h
  exact execFullForestA_nullifiers_grow s s' (eraseForestG f) er

theorem execForestG_logMono (s s' : RecChainedState) (f : DForest)
    (h : execForestG s f = some s') :
    s.log.length ≤ s'.log.length := by
  have er := execForestG_erases s s' f h
  exact execFullForestA_logMono s s' (eraseForestG f) er

theorem cellNextG_carries_rel {α : Type _} (R : α → α → Prop) [Trans R R R]
    (proj : RecChainedState → α)
    (forestGrowG : ∀ (s s' : RecChainedState) (f : DForest),
      execForestG s f = some s' → R (proj s) (proj s'))
    {base : α} {s : RecChainedState} (h : R base (proj s)) (cg : ConservingGatedForest) :
    R base (proj (cellNextG s cg)) := by
  dsimp [cellNextG]
  cases hc : execForestG s cg.val with
  | some s' => simp only [Option.getD_some]
               exact Trans.trans h (forestGrowG s s' cg.val hc)
  | none    => simp only [Option.getD_none]; exact h

attribute [aesop safe apply (rule_sets := [Dregg2])]
  execForestG_revoked_subset_grow
  execForestG_commitments_grow
  execForestG_nullifiers_grow

attribute [dregg_frame]
  execForestG_revoked_subset_grow
  execForestG_commitments_grow
  execForestG_nullifiers_grow
  execForestG_logMono

#assert_axioms execForestG_revoked_subset_grow
#assert_axioms execForestG_commitments_grow
#assert_axioms execForestG_nullifiers_grow
#assert_axioms execForestG_logMono
#assert_axioms cellNextG_carries_rel

end Production

end Dregg2.Verify
