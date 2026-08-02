/-
# `Dregg2.Circuit.Emit.BalanceComponentBindsOrCollides` — transfer's `bal` component, FLOOR-FREE.

⚑ THE WOUND THIS CLOSES, at the resolution it was found at (2026-08-01).

`Circuit.Inst.Transfer.balanceE` commits the whole per-asset ledger with `funcComponent`, whose
`binds` field is *plain injectivity of the digest*: `(hD : Function.Injective D)` at
`D : (CellId → AssetId → ℤ) → ℤ`. `Verify.InjSpelledFloors.balDigest_not_injective` proves that
hypothesis FALSE — not at deployed BabyBear parameters, not for any hash, but by CARDINALITY: the
domain is a function space (`2^ℵ₀` ledgers, one per real) and `ℤ` is countable, so no injection
exists at any parameters in any field. Every declaration binding it is VACUOUS.

The `lowerEffect` general-pass lane took that binder for its three transfer keystones
(`transferLoweredDesc_is_lowering`, `transferLowered_emits`,
`transferLowered_refines_balanceMovement`) while its own doc-comment recorded it as "not refuted",
directly under the paragraph explaining why it had routed AROUND `logHashInjective` to dodge exactly
this class. `#floor_ratchet` went red on all three, class `inj-spelled`.

## What this module builds instead

The idiom is the one the same lane applied on the LOG side (`LogCommitRegrounded.LogColl` +
`noLogColl_of_inj`) and that `WireCommitBindsOrCollides` / `CaveatCommitBindsOrCollides` apply on the
commitment side: **do not assume the collision away — hand it back.**

  * `BalColl D x y` (§1) — a NAMED, per-pair equivocation of the ledger digest: two DISTINCT ledgers,
    one digest. Distinctness is INSIDE the predicate, so `¬ BalColl D x x` is not a way to satisfy a
    side condition vacuously.
  * `balComponentFree` (§2) — the same `ActiveComponent` shape with the SAME digest and the SAME
    expected value, whose `postClause` is `read post = expected ∨ BalColl D …`. Its `binds` and
    `encodes` are proved with **no hypothesis on `D` whatsoever**: `binds` case-splits on the ledger
    equality and, in the failing branch, RETURNS the collision it was handed; `encodes` reads the
    digest equality straight out of either disjunct.
  * `balanceEFree` (§3) — transfer's spec at that component, through `Inst.Transfer.balanceEOf`, so
    the view / log / 18-clause rest frame / guard sub-system are literally the SAME OBJECT as
    `balanceE`'s and cannot drift from it.
  * `apexFree_or_collides` and `apexFree_iff_balanceMovementSpec` (§4) — the collapse. The first is
    HYPOTHESIS-FREE and disjunctive; the second takes `¬ BalColl D` at the ONE pair this witness
    supplies and delivers the COMPLETE `BalanceMovementSpec`, unweakened, in both directions.

## Strength, stated exactly

`¬ BalColl D bal_post bal_expected` is a claim about ONE named pair. The refuted `Function.Injective D`
would give it at EVERY pair (`balColl_refutes_inj` §1a is that implication, contrapositive, written
in the direction that does NOT bind the refuted floor: a collision handed back REFUTES injectivity).
So the statements here are strictly STRONGER than the `balanceE` route, and — unlike it — they are
not vacuous: §1b exhibits both poles, a `D` and a pair where `BalColl` HOLDS, and the agreement case
where it provably fails.

⚠ WHAT THIS DOES NOT FIX. `balComponent`/`balanceE`/`transfer_full_sound` and the ~600 other
`funcComponent` sites still bind the refuted digest injectivity; they are grandfathered in
`FloorRatchetBaselineInline` and remain vacuous. This module de-vacuums the compiler-pass keystones
and gives the rest of the tree the shape to port onto. The STRUCTURAL end state
`InjSpelledFloors` names — commit the FINITE support, never the whole function — is a different and
larger change to what the component SAYS, and is not made here.

Discipline: no `Function.Injective` in HYPOTHESIS position anywhere in this file; the only occurrence
is a CONCLUSION (`balColl_refutes_inj`), which is a refutation, not an assumption. Sorry-free.
-/
import Dregg2.Circuit.Inst.transfer

namespace Dregg2.Circuit.Emit.BalanceComponentBindsOrCollides

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Spec.BalanceMovement (BalanceMovementSpec)
open Dregg2.Exec (CellId AssetId RecChainedState RecordKernelState recTransferBal)
open Dregg2.Circuit.Inst.Transfer
  (BalanceArgs balanceEOf balanceGuardGates balanceGuardProp balanceOfGuardDecodes
   balanceOfGuardEncodes balanceOfRestFrameDecodes)

set_option autoImplicit false

/-! ## §1 — the NAMED collision event. Distinctness lives INSIDE the predicate. -/

/-- **`BalColl D x y`** — the ledger digest EQUIVOCATES at this pair: two DISTINCT per-asset ledgers
carrying one field element. This is the event `Function.Injective D` declares impossible at every
pair and which `Verify.InjSpelledFloors.balDigest_not_injective` proves is FORCED at some pair (the
domain is uncountable and `ℤ` is not). The component's residual is this event at the ONE pair the
witness actually supplies. -/
def BalColl (D : (CellId → AssetId → ℤ) → ℤ) (x y : CellId → AssetId → ℤ) : Prop :=
  x ≠ y ∧ D x = D y

/-! ### §1a — it CASHES OUT, in the direction that assumes nothing.

The bridge is deliberately NOT `Function.Injective D → ¬ BalColl D x y`: that spelling would take
the refuted floor as a HYPOTHESIS and be a fresh `inj-spelled` carrier — the same sin one theorem
over. The contrapositive says the same thing and binds nothing. -/

/-- **A returned collision REFUTES the digest floor.** So `¬ BalColl D x y` is exactly the residual
the deleted `hD` was covering up at this pair, and nothing weaker. -/
theorem balColl_refutes_inj {D : (CellId → AssetId → ℤ) → ℤ} {x y : CellId → AssetId → ℤ}
    (h : BalColl D x y) : ¬ Function.Injective D :=
  fun hinj => h.1 (hinj h.2)

/-! ### §1b — BOTH POLES (`feedback-prove-the-floor-false`): the event is satisfiable AND refutable,
so `¬ BalColl` is neither the constant `True` nor the constant `False`. -/

/-- The zero ledger. -/
def zeroLedger : CellId → AssetId → ℤ := fun _ _ => 0
/-- The all-ones ledger — distinct from `zeroLedger` at `(0, 0)`. -/
def oneLedger : CellId → AssetId → ℤ := fun _ _ => 1

theorem zeroLedger_ne_oneLedger : zeroLedger ≠ oneLedger := by
  intro h
  have := congrFun (congrFun h (0 : CellId)) (0 : AssetId)
  simp [zeroLedger, oneLedger] at this

/-- **SATISFIABLE POLE.** A digest that collapses everything genuinely collides on that pair, so
`BalColl` is not the constant `False` and `¬ BalColl` is not a free pass. -/
theorem balColl_satisfiable : BalColl (fun _ => 0) zeroLedger oneLedger :=
  ⟨zeroLedger_ne_oneLedger, rfl⟩

/-- **REFUTABLE POLE.** On AGREEING ledgers the event is FALSE at every digest, so `BalColl` is not
the constant `True` and the disjunctive `postClause` below is not free. -/
theorem balColl_refutable_on_agreement (D : (CellId → AssetId → ℤ) → ℤ)
    (x : CellId → AssetId → ℤ) : ¬ BalColl D x x :=
  fun h => h.1 rfl

/-! ## §2 — the FLOOR-FREE component. Same digest, same expected value, disjunctive `postClause`. -/

/-- The SPEC's predicted post-ledger — verbatim `balComponent`'s, so the two components commit the
same value and only their `postClause` differs. -/
def balExpected (pre : RecChainedState) (args : BalanceArgs) : CellId → AssetId → ℤ :=
  recTransferBal pre.kernel.bal args.t.src args.t.dst args.a args.t.amt

/-- **⚑ THE FLOOR-FREE `bal` COMPONENT.** `digest`/`expected` are `balComponent`'s exactly. The
`postClause` is the FULL whole-ledger equality OR the named equivocation at that very pair, which is
what lets `binds` be proved with NO hypothesis on `D`: equal digests either force the ledgers equal,
or the two ledgers ARE a collision and the clause hands it back. `encodes` reads the digest equality
out of either disjunct — the right one contains it literally. -/
def balComponentFree (D : (CellId → AssetId → ℤ) → ℤ) :
    ActiveComponent RecChainedState BalanceArgs where
  digest     := fun k => D k.bal
  expected   := fun pre args => D (balExpected pre args)
  postClause := fun pre args post =>
    post.bal = balExpected pre args ∨ BalColl D post.bal (balExpected pre args)
  binds      := by
    intro pre args post h
    by_cases hEq : post.bal = balExpected pre args
    · exact Or.inl hEq
    · exact Or.inr ⟨hEq, h⟩
  encodes    := by
    intro pre args post h
    rcases h with hEq | ⟨_, hD⟩
    · exact congrArg D hEq
    · exact hD

/-! ## §3 — transfer's spec at that component. -/

/-- **`balanceEFree`** — transfer's `EffectSpec2` with the floor-free `bal` component. Reached
through `Inst.Transfer.balanceEOf`, so the view, the growing log, the 18-clause rest frame and the
whole `propBit` guard sub-system are THE SAME OBJECT `balanceE` uses; there is no second frame to
drift. It takes no injectivity hypothesis, at all. -/
def balanceEFree (D : (CellId → AssetId → ℤ) → ℤ) : EffectSpec2 RecChainedState BalanceArgs :=
  balanceEOf (balComponentFree D)

/-- The floor-free spec's derived circuit is `balanceE`'s: the lowering reads `guardGates` and the
three digest EQ gates, none of which is the component. By `rfl`. -/
theorem effectCircuit2_free (D : (CellId → AssetId → ℤ) → ℤ) :
    effectCircuit2 (balanceEFree D) = balanceGuardGates ++ [cE2RestF, cE2Bind, cE2Log] := rfl

/-! ### §3a — the per-effect obligations, at the floor-free spec.

⚑ These are not transcriptions. `Inst.Transfer` proves both at `balanceEOf A` for an ARBITRARY
component (neither obligation reads `active`), so these are the SAME proof objects `balanceE`'s own
obligations are — instantiated at `balComponentFree D` instead of at `balComponent D hD`, with the
injectivity binder simply gone. There is no second proof to drift. -/

/-- `RestFrameDecodes2` at the floor-free spec: `RestIffNoBal RH`'s soundness side. -/
theorem balanceFreeRestFrameDecodes (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hRest : RestIffNoBal S.RH) : RestFrameDecodes2 S (balanceEFree D) :=
  balanceOfRestFrameDecodes S (balComponentFree D) hRest

/-- `GuardDecodes2` at the floor-free spec: the single bit gate decodes to `admitGuardA`. -/
theorem balanceFreeGuardDecodes (D : (CellId → AssetId → ℤ) → ℤ) :
    GuardDecodes2 (balanceEFree D) := balanceOfGuardDecodes (balComponentFree D)

/-- `GuardEncodes2` at the floor-free spec (the completeness side). -/
theorem balanceFreeGuardEncodes (D : (CellId → AssetId → ℤ) → ℤ) :
    GuardEncodes2 (balanceEFree D) := balanceOfGuardEncodes (balComponentFree D)

/-! ## §4 — THE COLLAPSE: apex ⟹ `BalanceMovementSpec`, disjunctively and then at a named pair.

The apex's four conjuncts line up with `BalanceMovementSpec`'s 21 with NO And-reassociation — the
`restFrame` clause order is verbatim the spec's frame order, which is what
`Inst.Transfer.apex_iff_balanceMovementSpec` already relies on. The ONLY difference here is the
component clause, which is now a disjunction. -/

/-- The apex, spelled out. A `def`-free restatement so the two theorems below read against the shape
rather than against four `whnf` steps; it is the identity by construction. -/
private theorem apexFree_unfold (D : (CellId → AssetId → ℤ) → ℤ)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState)
    (h : (balanceEFree D).apex s args s') :
    balanceGuardProp s args
      ∧ (s'.kernel.bal = balExpected s args ∨ BalColl D s'.kernel.bal (balExpected s args))
      ∧ s'.log = args.t :: s.log
      ∧ (balanceEFree D).restFrame s.kernel s'.kernel := h

/-- **⚑ HYPOTHESIS-FREE.** The floor-free apex either IS the complete declarative
`BalanceMovementSpec`, or it HANDS BACK a genuine equivocation of the deployed ledger digest at the
pair `(post ledger, spec-predicted ledger)`. Nothing is assumed about `D`. -/
theorem apexFree_or_collides (D : (CellId → AssetId → ℤ) → ℤ)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState)
    (h : (balanceEFree D).apex s args s') :
    BalanceMovementSpec s args.t args.a s' ∨ BalColl D s'.kernel.bal (balExpected s args) := by
  obtain ⟨hg, hcomp, hlog, hrest⟩ := apexFree_unfold D s args s' h
  rcases hcomp with hbal | hcoll
  · exact Or.inl ⟨hg, hbal, hlog, hrest⟩
  · exact Or.inr hcoll

/-- **The apex IS `BalanceMovementSpec`**, given the per-pair non-collision. The `→` needs `hno` to
kill the residual disjunct; the `←` needs nothing (a genuine movement takes the LEFT disjunct). The
conclusion is the COMPLETE 21-conjunct spec — guard, full whole-ledger equality, the grown log and
all 18 frame clauses — not a subset. -/
theorem apexFree_iff_balanceMovementSpec (D : (CellId → AssetId → ℤ) → ℤ)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState)
    (hno : ¬ BalColl D s'.kernel.bal (balExpected s args)) :
    (balanceEFree D).apex s args s' ↔ BalanceMovementSpec s args.t args.a s' := by
  constructor
  · intro h
    rcases apexFree_or_collides D s args s' h with hspec | hcoll
    · exact hspec
    · exact absurd hcoll hno
  · rintro ⟨hg, hbal, hlog, hrest⟩
    exact ⟨hg, Or.inl hbal, hlog, hrest⟩

/-! ## §5 — axiom-hygiene tripwires. -/

#assert_axioms balColl_refutes_inj
#assert_axioms balColl_satisfiable
#assert_axioms balColl_refutable_on_agreement
#assert_axioms effectCircuit2_free
#assert_axioms balanceFreeRestFrameDecodes
#assert_axioms balanceFreeGuardDecodes
#assert_axioms balanceFreeGuardEncodes
#assert_axioms apexFree_or_collides
#assert_axioms apexFree_iff_balanceMovementSpec

end Dregg2.Circuit.Emit.BalanceComponentBindsOrCollides
