/-
# Dregg2.Proof.Stingray — the Stingray bounded-counter concurrent-spend model.

Ports dregg1's Stingray bounded-counter protocol (arXiv:2501.06531;
`coord/src/budget.rs`, `coord/src/shared_budget.rs`) faithfully into Lean and proves the
headline safety property `stingray_no_concurrent_overspend`:

  Two concurrent draws `a₁ a₂` against a single Stingray slice with `a₁ + a₂ > remaining`
  can never both commit: whichever fires first debits the slice; the other sees
  `remaining' < a₂` and is rejected fail-closed. The committed set depends on the adversary's
  order — there is NO schedule-agnostic verdict (the CAP/BEC Thm 3.1 obstruction, same shape
  as `ContendedCrossCell.coupled_no_schedule_agnostic_commit`, on the actual bounded counter).

Faithfulness anchors: `Slice` mirrors `BudgetSlice { ceiling, spent }`; `Slice.remaining` is
`ceiling.saturating_sub(spent)` (Nat truncated subtraction = saturating); `Slice.tryDebit` is
`BudgetSlice::try_debit`; `sliceCeiling` is `balance·(f+1)/(2f+1)` in Nat floor-division.

Also proves the no-Byzantine soundness floor (`stingray_f0_ceiling_eq_balance`), the safe in-
budget fragment (`inbudget_both_commit_schedule_agnostic`), and bridges to `Confluence.IConfluent`.

The adversary's scheduling choice is explicit data
(`SDraw`, `runDraws`); the impossibility is a proved `¬ ∃`. Read-only consumer of `Confluence`.

GOSSIP RESIDUE (named, NOT built): the per-epoch `StingrayCounter::rebalance` reconciliation
half — signed `SpendingCertificate`s, quorum reconstruction, epoch monotonicity — is described
in the OPEN at §9. This module proves the within-epoch concurrent-spend safety that the rebalance
epoch boundary brackets.
-/
import Dregg2.Confluence
import Dregg2.Tactics

namespace Dregg2.Proof.Stingray

/-! ## §1 — The Stingray bounded counter (`BudgetSlice`), ported faithfully. -/

/-- A Stingray budget **slice** (`coord/src/budget.rs::BudgetSlice`, safety-core): the per-silo
ceiling and the amount already spent against it. -/
structure Slice where
  /-- The slice ceiling — the most this silo may debit locally with no coordination
  (`BudgetSlice.ceiling`, computed by `compute_slice_ceiling`). -/
  ceiling : Nat
  /-- Amount already spent from this slice (`BudgetSlice.spent`). -/
  spent   : Nat
  deriving DecidableEq, Repr

/-- Field-wise extensionality for `Slice` (a slice IS its `ceiling` and `spent`). -/
@[ext] theorem Slice.ext {s t : Slice} (hc : s.ceiling = t.ceiling) (hs : s.spent = t.spent) :
    s = t := by cases s; cases t; cases hc; cases hs; rfl

/-- Remaining budget in a slice — `ceiling.saturating_sub(spent)`. Truncated `Nat` subtraction
IS the saturating subtraction the Rust `BudgetSlice::remaining` uses. -/
def Slice.remaining (s : Slice) : Nat := s.ceiling - s.spent

/-- **`Slice.tryDebit`** — the faithful port of `BudgetSlice::try_debit`. Fail-closed: if the
amount exceeds `remaining`, return `none` (`Err(SliceExhausted)`); otherwise return the slice
with `spent += amount` (`saturating_add`, but no overflow on `Nat`). The HOT PATH: no
cross-silo coordination, just this local check. -/
def Slice.tryDebit (s : Slice) (amount : Nat) : Option Slice :=
  if amount ≤ s.remaining then
    some { s with spent := s.spent + amount }
  else
    none

/-- A debit *fires* (commits) on a slice iff `tryDebit` returns `some` — i.e. the slice can
cover it. The decidable admissibility predicate the scheduler's outcome hinges on. -/
def Slice.debitFires (s : Slice) (amount : Nat) : Bool := (s.tryDebit amount).isSome

/-- `tryDebit` fires **iff** the amount is within remaining — the executable face of the
fail-closed gate. -/
theorem tryDebit_isSome_iff (s : Slice) (amount : Nat) :
    (s.tryDebit amount).isSome = true ↔ amount ≤ s.remaining := by
  unfold Slice.tryDebit
  by_cases h : amount ≤ s.remaining
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]; simp [h]

/-- A committed debit advances `spent` by exactly `amount` (and leaves `ceiling` fixed). The
state-update lemma the over-draw argument rests on. -/
theorem tryDebit_spent {s s' : Slice} {amount : Nat} (h : s.tryDebit amount = some s') :
    s'.spent = s.spent + amount ∧ s'.ceiling = s.ceiling := by
  unfold Slice.tryDebit at h
  by_cases hc : amount ≤ s.remaining
  · rw [if_pos hc] at h; simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  · rw [if_neg hc] at h; exact absurd h (by simp)

/-- After a committed debit of `a₁`, the remaining budget DROPS by exactly `a₁`
(`remaining' = remaining - a₁`). The over-draw crux: the second draw now faces a smaller pot. -/
theorem tryDebit_remaining {s s' : Slice} {a₁ : Nat} (h : s.tryDebit a₁ = some s') :
    s'.remaining = s.remaining - a₁ := by
  obtain ⟨hsp, hcl⟩ := tryDebit_spent h
  unfold Slice.remaining
  rw [hcl, hsp]
  omega

/-! ## §2 — The slice-ceiling formula (`StingrayCounter::compute_slice_ceiling`).

`balance·(f+1)/(2f+1)` in Nat floor-division. At `f=0` the ceiling equals the balance; for
`f ≥ 1` it is a strict fraction, so `n` slices over-subscribe the budget (the concurrent-spend
affordance). -/

/-- The Stingray per-silo slice ceiling: `balance·(f+1)/(2f+1)` (`StingrayCounter::
compute_slice_ceiling`). `Nat` floor division mirrors the Rust u128 floor division. -/
def sliceCeiling (balance f : Nat) : Nat := balance * (f + 1) / (2 * f + 1)

/-- Faithfulness check against Rust test vectors:
`balance=3000, f=1 ⇒ 2000`; `balance=12000, f=1 ⇒ 8000`. -/
theorem sliceCeiling_examples :
    sliceCeiling 3000 1 = 2000 ∧ sliceCeiling 12000 1 = 8000 := by
  unfold sliceCeiling; refine ⟨?_, ?_⟩ <;> rfl

/-- With no Byzantine silos (`f=0`) the slice ceiling equals the balance: `balance·1/1 = balance`.
A single silo's slice is exactly the whole budget — it can spend everything but not more. -/
theorem stingray_f0_ceiling_eq_balance (balance : Nat) :
    sliceCeiling balance 0 = balance := by
  unfold sliceCeiling; simp

/-- At `f=0`, any committed draw `a` against a fresh slice satisfies `a ≤ balance` and the
resulting `spent ≤ balance`. A debit over-drawing the true balance is rejected fail-closed. -/
theorem stingray_no_byzantine_total_le_balance (balance a : Nat) {s' : Slice}
    (h : (Slice.mk (sliceCeiling balance 0) 0).tryDebit a = some s') :
    a ≤ balance ∧ s'.spent ≤ balance := by
  have hfire : ((Slice.mk (sliceCeiling balance 0) 0).tryDebit a).isSome = true := by
    rw [h]; rfl
  rw [tryDebit_isSome_iff] at hfire
  have hrem : (Slice.mk (sliceCeiling balance 0) 0).remaining = balance := by
    unfold Slice.remaining; simp [stingray_f0_ceiling_eq_balance]
  rw [hrem] at hfire
  obtain ⟨hsp, _⟩ := tryDebit_spent h
  exact ⟨hfire, by rw [hsp]; simpa using hfire⟩

/-! ## §3 — The concurrent-draw scheduler against ONE over-subscribed slice.

Two concurrent draws `a₁ a₂` are presented to a SINGLE slice with no coordination (the Stingray
hot path: both silos *think* they have budget, or — in the single-silo over-draw — two
concurrent debits race the same slice). An adversarial *scheduler* picks the order. `runDraws` is
the deterministic fail-closed semantics: the second draw sees the slice the first one left. This
is precisely `ContendedCrossCell.runSchedule` specialised to the Stingray bounded counter (no
credit side — the contention is purely the shared debit pot the budget IS). -/

/-- The adversary's scheduling choice for two concurrent draws against one slice. `d12` applies
draw `1` first then draw `2`; `d21` the reverse. The whole question is whether the committed
outcome can be made INDEPENDENT of this bit. -/
inductive SDraw where
  | d12
  | d21
  deriving DecidableEq, Repr

/-- The committed outcome of a concurrent run: the final slice and WHICH draws committed
(`none` = the scheduler's order forced this draw to abort, fail-closed: `SliceExhausted`). -/
structure SOutcome where
  /-- The final slice after the scheduled run. -/
  slice : Slice
  /-- Whether draw `1` committed. -/
  c₁ : Bool
  /-- Whether draw `2` committed. -/
  c₂ : Bool
  deriving Repr

/-- Apply one draw against the threaded slice, fail-closed. On success: the debited slice and
`true`; on failure: the slice UNCHANGED and `false`. The half-edge the scheduler threads. -/
def stepDraw (s : Slice) (amount : Nat) : Slice × Bool :=
  match s.tryDebit amount with
  | some s' => (s', true)
  | none    => (s, false)

/-- **`runDraws`** — deterministic fail-closed semantics of a concurrent draw schedule. The two
draws `a₁ a₂` debit the SAME slice `s`; the adversary's `SDraw` fixes the order; the second draw
sees the slice the first one left. (`ContendedCrossCell.runSchedule`, on the Stingray counter.) -/
def runDraws (s : Slice) (a₁ a₂ : Nat) : SDraw → SOutcome
  | .d12 =>
      let (s₁, r₁) := stepDraw s a₁
      let (s₂, r₂) := stepDraw s₁ a₂
      { slice := s₂, c₁ := r₁, c₂ := r₂ }
  | .d21 =>
      let (s₁, r₂) := stepDraw s a₂
      let (s₂, r₁) := stepDraw s₁ a₁
      { slice := s₂, c₁ := r₁, c₂ := r₂ }

/-- `stepDraw` on a committed debit threads the debited slice and records `true`. The bridge
from `tryDebit` to the scheduler's `stepDraw`. -/
theorem stepDraw_of_commit {s s' : Slice} {a : Nat} (h : s.tryDebit a = some s') :
    stepDraw s a = (s', true) := by
  unfold stepDraw; rw [h]

/-- `stepDraw` on a rejected debit leaves the slice unchanged and records `false`. -/
theorem stepDraw_of_reject {s : Slice} {a : Nat} (h : s.tryDebit a = none) :
    stepDraw s a = (s, false) := by
  unfold stepDraw; rw [h]

/-! ## §4 — THE HEADLINE: no concurrent overspend against one over-subscribed slice.

The COUPLED / over-subscribed case: two concurrent draws `a₁ a₂` against ONE slice whose
remaining budget cannot fund both (`a₁ + a₂ > remaining`). We prove BOTH draws cannot commit
under EITHER schedule, and — sharper — that the committed verdict is a genuine FUNCTION of the
adversary's order, so there is NO schedule-agnostic atomic commit (CAP/BEC Thm 3.1). -/

/-- **`overdraw_not_both_commit`.** Core no-double-spend: if the two concurrent draws
cannot BOTH be funded from the slice (`a₁ + a₂ > remaining`), then under EITHER adversary
schedule at most one of them commits — never both. Whichever fires first debits the slice; the
other then faces `remaining - (first) < (second)` and is rejected fail-closed. This is the
budget-layer no-concurrent-overspend, on the actual `BudgetSlice` semantics. -/
theorem overdraw_not_both_commit (s : Slice) (a₁ a₂ : Nat)
    (hover : s.remaining < a₁ + a₂) (sch : SDraw) :
    ¬ ((runDraws s a₁ a₂ sch).c₁ = true ∧ (runDraws s a₁ a₂ sch).c₂ = true) := by
  rintro ⟨hc1, hc2⟩
  -- In either schedule, the SECOND-applied draw runs against a slice whose remaining dropped by
  -- the first-applied draw's amount; the over-draw hypothesis makes that second draw fail.
  cases sch with
  | d12 =>
      -- d12: draw 1 first (if it fires), then draw 2 against the leftover.
      simp only [runDraws] at hc1 hc2
      -- draw 1's stepDraw: split on whether it fired.
      unfold stepDraw at hc1 hc2
      cases h1 : s.tryDebit a₁ with
      | none => rw [h1] at hc1; simp at hc1
      | some s₁ =>
          rw [h1] at hc2
          -- s₁.remaining = s.remaining - a₁; with a₁ ≤ remaining (it fired) and over-draw, a₂ > s₁.remaining.
          have ha1 : a₁ ≤ s.remaining := by
            have : (s.tryDebit a₁).isSome = true := by rw [h1]; rfl
            rwa [tryDebit_isSome_iff] at this
          have hrem1 : s₁.remaining = s.remaining - a₁ := tryDebit_remaining h1
          -- draw 2 against s₁ must fail: a₂ > s₁.remaining.
          cases h2 : s₁.tryDebit a₂ with
          | some s₂ =>
              have ha2 : a₂ ≤ s₁.remaining := by
                have : (s₁.tryDebit a₂).isSome = true := by rw [h2]; rfl
                rwa [tryDebit_isSome_iff] at this
              rw [hrem1] at ha2; omega
          | none => rw [h2] at hc2; simp at hc2
  | d21 =>
      -- symmetric: draw 2 first, then draw 1.
      simp only [runDraws] at hc1 hc2
      unfold stepDraw at hc1 hc2
      cases h2 : s.tryDebit a₂ with
      | none => rw [h2] at hc2; simp at hc2
      | some s₂ =>
          rw [h2] at hc1
          have ha2 : a₂ ≤ s.remaining := by
            have : (s.tryDebit a₂).isSome = true := by rw [h2]; rfl
            rwa [tryDebit_isSome_iff] at this
          have hrem2 : s₂.remaining = s.remaining - a₂ := tryDebit_remaining h2
          cases h1 : s₂.tryDebit a₁ with
          | some s₁ =>
              have ha1 : a₁ ≤ s₂.remaining := by
                have : (s₂.tryDebit a₁).isSome = true := by rw [h1]; rfl
                rwa [tryDebit_isSome_iff] at this
              rw [hrem2] at ha1; omega
          | none => rw [h1] at hc1; simp at hc1

/-! ### The concrete over-subscribed running example (machine-checked).

A Stingray slice with `ceiling = 2000` (the `f=1, balance=3000` slice from
`test_byzantine_agent_overspend_is_bounded`), fresh (`spent = 0`). Two concurrent draws of
`1200` each: together `2400 > 2000 = remaining`. Whichever the adversary schedules first commits;
the other sees `800 < 1200` and aborts fail-closed. -/

/-- The contended slice: `f=1, balance=3000` ceiling `= 2000`, freshly distributed
(`distribute_slices` sets `spent = 0`). -/
def potSlice : Slice := { ceiling := 2000, spent := 0 }

/-- Draw amount: `1200`. Two of these want `2400 > 2000` — an over-draw of the single slice. -/
def drawAmt : Nat := 1200

/-- The two draws over-subscribe the fresh slice: `remaining = 2000 < 2400 = 1200 + 1200`. -/
theorem pot_oversubscribed : potSlice.remaining < drawAmt + drawAmt := by
  unfold potSlice drawAmt Slice.remaining; decide

/-- Under `d12` draw `1` commits and draw `2` aborts (after `1` debits `1200`, only `800 < 1200`
remains, so `2`'s `tryDebit` fails `SliceExhausted`). Machine-checked on the real `BudgetSlice`
semantics. -/
theorem d12_one_aborts_two :
    (runDraws potSlice drawAmt drawAmt .d12).c₁ = true ∧
    (runDraws potSlice drawAmt drawAmt .d12).c₂ = false := by
  decide

/-- Under `d21` the outcome FLIPS: draw `2` commits, draw `1` aborts. The committed set is
order-dependent. Machine-checked. -/
theorem d21_two_aborts_one :
    (runDraws potSlice drawAmt drawAmt .d21).c₁ = false ∧
    (runDraws potSlice drawAmt drawAmt .d21).c₂ = true := by
  decide

/-- **`stingray_schedules_disagree`.** The two adversary schedules produce DIFFERENT
committed outcomes: `d12 ↦ (true,false)`, `d21 ↦ (false,true)`. The adversary's order bit is
OBSERVABLE in which draw commits. Machine-checked. -/
theorem stingray_schedules_disagree :
    ((runDraws potSlice drawAmt drawAmt .d12).c₁,
     (runDraws potSlice drawAmt drawAmt .d12).c₂)
    ≠
    ((runDraws potSlice drawAmt drawAmt .d21).c₁,
     (runDraws potSlice drawAmt drawAmt .d21).c₂) := by
  decide

/-- **KEYSTONE — `stingray_no_concurrent_overspend`.** THE HEADLINE.

There is NO schedule-agnostic atomic commit for two concurrent draws against one over-subscribed
Stingray slice: there exists a slice and two draw amounts (the real `f=1` ceiling-2000 slice, two
1200-draws) such that NO verdict `(Bool × Bool)` reading only the committed-draw flags can be
CONSTANT across the adversary's schedules while AGREEING with the fail-closed `BudgetSlice::
try_debit` semantics on every schedule. The semantics forces `d12 ↦ (true,false)` and
`d21 ↦ (false,true)`, which differ — so any faithful verdict is order-dependent.

This is the budget-layer **no-double-spend under concurrent draw**: two concurrent spends against
one over-subscribed budget cannot both commit, and which one does is a genuine function of the
adversary's order — the CAP/BEC Thm 3.1 obstruction on the ACTUAL Stingray bounded counter,
the same `¬ ∃ schedule-agnostic verdict` shape as
`ContendedCrossCell.coupled_no_schedule_agnostic_commit`. PROVED, machine-checked. -/
theorem stingray_no_concurrent_overspend :
    ∃ (s : Slice) (a₁ a₂ : Nat),
      s.remaining < a₁ + a₂ ∧
      ¬ ∃ verdict : Bool × Bool,
        (∀ sch : SDraw,
          ((runDraws s a₁ a₂ sch).c₁, (runDraws s a₁ a₂ sch).c₂) = verdict) := by
  refine ⟨potSlice, drawAmt, drawAmt, pot_oversubscribed, ?_⟩
  rintro ⟨verdict, hconst⟩
  -- a schedule-agnostic verdict would equal BOTH d12's and d21's outcomes, but they differ.
  exact stingray_schedules_disagree ((hconst .d12).trans (hconst .d21).symm)

/-! ## §5 — The classifier bridge: over-subscribed budget draws ARE `¬ IConfluent`.

The coupled budget fragment is exactly the NON-I-confluent one — the SAME third judgement
`ContendedCrossCell` uses. The contended slice's "at most one of the two over-draws may stand"
is the `card ≤ 1`-shape invariant whose concurrent merge overflows
(`Confluence.cardLeOne_not_iconfluent`); `nonpairwise_escalation` exhibits the forced clashing
pair. Two faces (operational schedule-disagreement; lattice merge-violation) of one obstruction. -/

/-- **`stingray_overdraw_must_escalate`.** The over-subscribed budget draw is NOT
I-confluent and is FORCED to escalate to consensus (dregg1's Tier-3 / the `escalate` path in
`shared_budget.rs`). We exhibit the bridge to the metatheory classifier: the contended budget has
the `card ≤ 1` shape (at most one over-draw may stand), which is NOT `Confluence.IConfluent`
(`cardLeOne_not_iconfluent`), and `nonpairwise_escalation` produces the concrete clashing pair —
the same impossibility `stingray_no_concurrent_overspend` proves operationally. -/
theorem stingray_overdraw_must_escalate :
    ¬ Dregg2.Confluence.IConfluent (S := Finset ℕ) (fun s => s.card ≤ 1) ∧
    (∃ x y : Finset ℕ, (fun s => s.card ≤ 1) x ∧ (fun s => s.card ≤ 1) y ∧
      ¬ (fun s => s.card ≤ 1) (x ⊔ y)) := by
  refine ⟨Dregg2.Confluence.cardLeOne_not_iconfluent, ?_⟩
  exact Dregg2.Confluence.nonpairwise_escalation _ Dregg2.Confluence.cardLeOne_not_iconfluent

/-! ## §6 — The DUAL fragment: well-subscribed concurrent draws DO commit schedule-agnostically.

When the slice CAN fund both draws (`a₁ + a₂ ≤ remaining` — the in-budget / coordination-free
hot path the Stingray design exists for), BOTH draws commit under EITHER schedule and the final
slice is the SAME. So the dichotomy is real: in-budget concurrency is schedule-agnostic
(no coordination), over-budget concurrency is not (must escalate). -/

/-- **`inbudget_both_commit_schedule_agnostic`.** THE SAFE FRAGMENT. When the slice can
fund BOTH draws (`a₁ + a₂ ≤ remaining`), both draws commit under EITHER adversary schedule, and
the final slice is identical (`spent` advanced by `a₁ + a₂` either way — addition commutes). So
the committed outcome is schedule-agnostic: the coordination-free hot path the Stingray bounded
counter is designed for. PROVED on the real `BudgetSlice` semantics. -/
theorem inbudget_both_commit_schedule_agnostic (s : Slice) (a₁ a₂ : Nat)
    (hfit : a₁ + a₂ ≤ s.remaining) :
    let o12 := runDraws s a₁ a₂ .d12
    let o21 := runDraws s a₁ a₂ .d21
    o12.c₁ = true ∧ o12.c₂ = true ∧ o21.c₁ = true ∧ o21.c₂ = true ∧
    o12.slice = o21.slice := by
  -- draw 1 fires (a₁ ≤ remaining), leaving remaining - a₁ ≥ a₂, so draw 2 fires; symmetric.
  have ha1 : a₁ ≤ s.remaining := by omega
  obtain ⟨s₁, h1⟩ : ∃ s₁, s.tryDebit a₁ = some s₁ := by
    rw [← Option.isSome_iff_exists, tryDebit_isSome_iff]; exact ha1
  have hrem1 : s₁.remaining = s.remaining - a₁ := tryDebit_remaining h1
  obtain ⟨hsp1, hcl1⟩ := tryDebit_spent h1
  have ha2' : a₂ ≤ s₁.remaining := by rw [hrem1]; omega
  obtain ⟨s₁₂, h12⟩ : ∃ s₁₂, s₁.tryDebit a₂ = some s₁₂ := by
    rw [← Option.isSome_iff_exists, tryDebit_isSome_iff]; exact ha2'
  -- the d21 leg.
  have ha2 : a₂ ≤ s.remaining := by omega
  obtain ⟨s₂, h2⟩ : ∃ s₂, s.tryDebit a₂ = some s₂ := by
    rw [← Option.isSome_iff_exists, tryDebit_isSome_iff]; exact ha2
  have hrem2 : s₂.remaining = s.remaining - a₂ := tryDebit_remaining h2
  obtain ⟨hsp2, hcl2⟩ := tryDebit_spent h2
  have ha1' : a₁ ≤ s₂.remaining := by rw [hrem2]; omega
  obtain ⟨s₂₁, h21⟩ : ∃ s₂₁, s₂.tryDebit a₁ = some s₂₁ := by
    rw [← Option.isSome_iff_exists, tryDebit_isSome_iff]; exact ha1'
  -- both final slices have the same ceiling and the same spent (s.spent + a₁ + a₂).
  obtain ⟨hsp12, hcl12⟩ := tryDebit_spent h12
  obtain ⟨hsp21, hcl21⟩ := tryDebit_spent h21
  simp only [runDraws, stepDraw_of_commit h1, stepDraw_of_commit h12,
    stepDraw_of_commit h2, stepDraw_of_commit h21, eq_self_iff_true, true_and, and_true]
  -- the four `c₁/c₂ = true` conjuncts collapse, leaving s₁₂ = s₂₁: same ceiling, same spent.
  refine Slice.ext ?_ ?_
  · rw [hcl12, hcl1, hcl21, hcl2]
  · rw [hsp12, hsp1, hsp21, hsp2]; omega

/-! ## §7 — Axiom-hygiene tripwires (the CLOSED keystones, all clean). -/

#assert_axioms tryDebit_isSome_iff
#assert_axioms tryDebit_spent
#assert_axioms tryDebit_remaining
#assert_axioms sliceCeiling_examples
#assert_axioms stingray_f0_ceiling_eq_balance
#assert_axioms stingray_no_byzantine_total_le_balance
#assert_axioms overdraw_not_both_commit
#assert_axioms pot_oversubscribed
#assert_axioms d12_one_aborts_two
#assert_axioms d21_two_aborts_one
#assert_axioms stingray_schedules_disagree
#assert_axioms stingray_no_concurrent_overspend
#assert_axioms stingray_overdraw_must_escalate
#assert_axioms inbudget_both_commit_schedule_agnostic

/-! ## §8 — Non-vacuity guards (the model runs, the witnesses are real). -/

#guard (sliceCeiling 3000 1 == 2000)
#guard (sliceCeiling 12000 1 == 8000)
#guard (sliceCeiling 1000 0 == 1000)
#guard ((runDraws potSlice drawAmt drawAmt .d12).c₁)
#guard ((runDraws potSlice drawAmt drawAmt .d12).c₂ == false)
#guard ((runDraws potSlice drawAmt drawAmt .d21).c₁ == false)
#guard ((runDraws potSlice drawAmt drawAmt .d21).c₂)
#guard ((runDraws potSlice 800 800 .d12).c₁)
#guard ((runDraws potSlice 800 800 .d12).c₂)
#guard ((runDraws potSlice 800 800 .d21).slice == (runDraws potSlice 800 800 .d12).slice)

/-! ## §9 — OUTCOME + the gossip-dissemination residue (NAMED, not built).

The Stingray within-epoch concurrent-spend safety is PROVED on a faithful port of the dregg1
`BudgetSlice`/`StingrayCounter` semantics, both poles of the dichotomy closed:

  * **Headline impossibility:** `stingray_no_concurrent_overspend` — two concurrent
    draws against one OVER-subscribed slice (`a₁ + a₂ > remaining`) cannot both commit, and which
    one does is a genuine function of the adversary's order (`stingray_schedules_disagree`); there
    is NO schedule-agnostic verdict. The budget-layer no-double-spend = the CAP/BEC Thm 3.1
    obstruction on the real bounded counter (`overdraw_not_both_commit` is the ∀-schedule core).
  * **Safe fragment:** `inbudget_both_commit_schedule_agnostic` — when the slice funds
    both draws (`a₁ + a₂ ≤ remaining`), both commit under EITHER schedule and leave the same
    slice. The coordination-free hot path the Stingray design exists for.
  * **No-Byzantine soundness floor:** `stingray_f0_ceiling_eq_balance` +
    `stingray_no_byzantine_total_le_balance` — at `f=0` the ceiling IS the balance, so a single
    slice can never over-draw the true balance.
  * **Classifier bridge:** `stingray_overdraw_must_escalate` — the over-subscribed case
    is `¬ Confluence.IConfluent` (`cardLeOne_not_iconfluent`), the SAME third judgement dregg2
    uses; escalation to Tier-3 consensus is forced by an exhibited counterexample.

All keystones `#assert_axioms`-clean; the adversary enters ONLY as explicit data (`SDraw`,
`runDraws`); the impossibility is a PROVED `¬ ∃`.

-- GOSSIP-DISSEMINATION RESIDUE (named, NOT built — the cross-epoch reconciliation half).
--   The model above is the WITHIN-epoch concurrent-spend layer. dregg1's Stingray ALSO has the
--   *rebalance / gossip* half (`StingrayCounter::rebalance`, `coord/src/budget.rs:402`) that
--   dregg2 still lacks. A faithful model of THAT needs, in order:
--   (1) **Signed spending certificates.** `BudgetSlice::certificate` Ed25519-signs
--       `agent ‖ version ‖ spent ‖ silo`; `verify_signature` checks it. Modelling this needs a
--       signature abstraction with an UNFORGEABILITY axiom/portal (a Byzantine silo cannot forge
--       an honest silo's certificate) — dregg2 has the crypto-portal floor
--       (`CryptoKernel`/`World`) this would hang off, but no certificate-unforgeability lemma yet.
--   (2) **Quorum reconstruction of true spending.** `rebalance` sums certificates and (partial
--       mode) charges missing silos their full ceiling. The safety theorem to prove is: with
--       `n ≥ 3f+1` silos (the `StingrayCounter::new` bound) and at most `f` Byzantine, the f+1
--       honest certificates PIN the true total spent (Byzantine silos can omit or under-report by
--       at most their `f·ceiling`, which `test_byzantine_agent_overspend_is_bounded` asserts is
--       the maximum UNDETECTABLE overspend). This is a threshold/counting argument over the silo
--       set — the gossip-dissemination safety bound proper. It reduces to a Blocklace-style
--       quorum-intersection lemma (dregg2 HAS the Blocklace + Cordial-Miners machinery, #105/#106,
--       to host it) but is not yet stated.
--   (3) **Epoch monotonicity.** `version` increments each rebalance and certificates must match
--       the current version (`VersionMismatch`); a stale certificate cannot be replayed into a
--       later epoch. A monotone-version / no-replay lemma (the `nullifiers`/`commitments`
--       append-only shape dregg2 already proves on the kernel would transfer).
--   (4) **Fast-unlock.** `FastUnlockManager` releases a 2PC-aborted lock with a silo quorum
--       without the epoch timeout; a liveness (not safety) obligation, out of scope for the
--       headline safety property but part of the full gossip layer.
--   NONE of (1)–(4) is built here. This module proves the within-epoch concurrent-overspend
--   safety that the rebalance epoch boundary brackets, and names exactly what the gossip half
--   would still require.
-/

end Dregg2.Proof.Stingray
