/-
# Dregg2.Distributed.Economics — the economics / DoS pillar (Titanium Phase 2.5)

**The grounding (see `docs/rebuild/TITANIUM-PHASE.md` §2.5 and `CONSENSUS-GROUNDING.md` §2,
Wong et al. 4.1).** "Sound ≠ live-under-economic-attack." A turn is *expensive to admit*
(the network pays `proveCost` to verify-admit it) but *cheap to emit* (an attacker pays only
`submitCost` to throw it at the mempool) — Wong's 4.1 distributed-DoS asymmetry. The protocol's
only lever against this is the **fee**: every admitted turn is charged `fee`, split (the model
already proved in `Exec.Admission`) **50% proposer / 30% treasury / ~20% burn**. This module is
the resource-accounting + mechanism layer that turns "we charge a fee" into three theorems:

1. **Spam-deterrence.** If `fee ≥ marginalJunkCost` (the network's marginal cost of admitting one
   junk turn, `= proveCost`), then the TOTAL work the system performs on an attacker's `k` turns
   is BOUNDED by the total fees that attacker pays: `networkWork k ≤ feesCollected k`. An attacker
   cannot force unbounded work without paying for it. The bound is exact and `k`-uniform.

2. **Griefing-unprofitability.** Griefing = burning your own value to inflict loss on a victim.
   Under the fee schedule the attacker's cost to inflict one unit of victim loss is `≥ 1` *iff*
   `fee ≥ victimLossPerTurn`; we prove the cost-domination `attackerCost ≥ victimLoss`
   conditionally on that exact fee condition (NOT unconditionally — the honest condition is named
   and the boundary is exhibited both directions).

3. **Incentive-compatibility of 50/30/burn.** The proposer's reward is `proposerShare fee = fee/2`
   (the real split from `Exec.Admission`). Under the named cost bound `proveCost ≤ fee/2`, the
   proposer's reward covers its proving cost — `proposerShare fee ≥ proveCost` — so honest block
   production is individually rational.

## Discipline (the bar — `feedback-dont-launder-vacuity-as-honest`)
Every theorem carries BOTH a non-vacuity witness AND a **negative tooth**: a concrete
fee-too-low instance where the deterred attack IS profitable / IS unbounded, proving the bound
is a real constraint and not vacuously true. Genuinely-open economic quantities (the exact
`proveCost` of a turn, the exact attacker-side `submitCost`) are carried as EXPLICITLY-NAMED
parameters of the model, never `sorry`, never `:= True`. Keystones are `#assert_axioms`-clean
(axioms ⊆ {propext, Classical.choice, Quot.sound}).

The fee-split semantics (`proposerShare`/`treasuryShare`/`feeBurned`) are REUSED verbatim from
`Dregg2.Exec.Admission`, so theorem 3 is about the real protocol split, not a re-modelled one.
-/
import Dregg2.Exec.Admission

namespace Dregg2.Distributed.Economics

open Dregg2.Exec.Admission (proposerShare treasuryShare feeBurned)

/-! ## §1 — The resource-accounting model

The economic state of the system over a workload is captured by a small mechanism record. The
quantities marked OPEN are empirical (they depend on the prover, the network, the
victim's exposure) and are carried as named parameters; the theorems are stated *for all* such
parameters under the explicit fee conditions. -/

/-- **`FeeSchedule`** — the protocol's per-turn economic parameters.

* `fee`             — the charge levied on every admitted turn (≥ 0; the protocol's only lever).
* `proveCost`       — OPEN(network): the work the network performs to verify-admit one turn (the
                      "proving is expensive" half of Wong 4.1's asymmetry). The *marginal junk
                      cost*: admitting one more junk turn costs the network exactly this.
* `submitCost`      — OPEN(attacker): the work an attacker performs to *emit* one turn (the "junk
                      is cheap" half). Typically `submitCost ≪ proveCost`; we do not assume it.

All in a common non-negative work/value unit (`Nat`). -/
structure FeeSchedule where
  fee       : Nat
  proveCost : Nat
  submitCost : Nat
deriving Repr, DecidableEq

namespace FeeSchedule

variable (φ : FeeSchedule)

/-- The marginal cost to the network of admitting one junk turn = the proving cost. This is the
quantity Wong 4.1 / TITANIUM §2.5 names "marginal junk cost". -/
def marginalJunkCost : Nat := φ.proveCost

/-- The total work the *network* performs to admit `k` turns: `k · proveCost`. This is what a
spammer is trying to inflate without paying. -/
def networkWork (k : Nat) : Nat := k * φ.proveCost

/-- The total fees the system *collects* from `k` admitted turns: `k · fee`. (Each turn is charged
`fee` in the admission prologue, `Exec.Admission.commitPrologue`.) -/
def feesCollected (k : Nat) : Nat := k * φ.fee

/-- The total cost an *attacker* pays to emit `k` turns: `k · submitCost`. Cheap per Wong 4.1; the
attacker is NOT charged `submitCost` by the protocol — it is charged `fee`. -/
def attackerEmitCost (k : Nat) : Nat := k * φ.submitCost

end FeeSchedule

/-! ## §2 — Theorem 1: spam-deterrence (`fee ≥ marginalJunkCost ⇒ work bounded by fees`)

The asymmetry Wong 4.1 warns about is that an attacker emits `k` junk turns cheaply
(`k · submitCost`) but forces the network to do `k · proveCost` work. The fee closes it: because
EVERY admitted turn pays `fee`, if `fee ≥ marginalJunkCost (= proveCost)` then the network's work
on those `k` turns is bounded above by the fees those same `k` turns paid. The attacker cannot
make the network do work it has not paid for. -/

/-- **`spam_work_bounded_by_fees` — THEOREM 1.** If the per-turn fee covers the marginal
junk cost (`fee ≥ marginalJunkCost`), then for EVERY workload size `k`, the total network work to
admit those `k` turns is `≤` the total fees collected from them. The bound is exact and uniform in
`k`: an attacker forcing `networkWork k` of work has paid at least that much in fees. -/
theorem spam_work_bounded_by_fees (φ : FeeSchedule)
    (hcover : φ.marginalJunkCost ≤ φ.fee) (k : Nat) :
    φ.networkWork k ≤ φ.feesCollected k := by
  simp only [FeeSchedule.networkWork, FeeSchedule.feesCollected, FeeSchedule.marginalJunkCost] at *
  exact Nat.mul_le_mul_left k hcover

/-- A sharper restatement: the *unpaid* network work (work in excess of fees) is ZERO under the
fee-covers-cost condition. The system never does work it was not paid for. -/
theorem spam_no_unpaid_work (φ : FeeSchedule)
    (hcover : φ.marginalJunkCost ≤ φ.fee) (k : Nat) :
    φ.networkWork k - φ.feesCollected k = 0 :=
  Nat.sub_eq_zero_of_le (spam_work_bounded_by_fees φ hcover k)

/-- **NEGATIVE TOOTH for Theorem 1.** When the fee does NOT cover the marginal junk cost
(`fee < proveCost`), the deterrence FAILS: there is a workload (`k = 1` here, hence any positive
`k`) on which the network's work strictly EXCEEDS the fees collected. The attacker forces
uncompensated work. This proves the `fee ≥ marginalJunkCost` hypothesis is load-bearing, not
vacuous. -/
theorem spam_work_unbounded_when_fee_too_low :
    let φ : FeeSchedule := { fee := 1, proveCost := 10, submitCost := 1 }
    φ.fee < φ.marginalJunkCost ∧ φ.feesCollected 1 < φ.networkWork 1 := by
  refine ⟨by decide, by decide⟩

/-- NON-VACUITY witness for Theorem 1: a concrete schedule where the fee DOES cover the cost, so
the deterrence bound holds with strict slack (fees strictly exceed work — the honest regime). -/
theorem spam_deterrence_nonvacuous :
    let φ : FeeSchedule := { fee := 10, proveCost := 4, submitCost := 1 }
    φ.marginalJunkCost ≤ φ.fee ∧ φ.networkWork 7 ≤ φ.feesCollected 7 := by
  refine ⟨by decide, spam_work_bounded_by_fees _ (by decide) 7⟩

/-! ## §3 — Theorem 2: griefing-unprofitability (the exact fee condition)

Griefing = an attacker spends value to inflict loss on a *victim*, with no direct gain to itself
(the loss is destroyed, not transferred). The relevant ratio is the attacker's **cost to inflict
one unit of victim loss**. Griefing is "not profitable" when that ratio is `≥ 1`, i.e. the
attacker pays at least as much as the harm it causes.

This is NOT unconditionally true under any fee — it depends on how much loss one griefing turn can
impose (`victimLossPerTurn`, OPEN: depends on the victim's exposure). We prove it *conditionally on
the exact fee condition* `fee ≥ victimLossPerTurn`, and exhibit the boundary both directions. -/

/-- A griefing campaign: `k` turns, each costing the attacker `fee` and inflicting
`victimLossPerTurn` of (destroyed) loss on the victim. `victimLossPerTurn` is OPEN — it is the
victim's per-turn exposure to a griefing turn. -/
structure GriefCampaign where
  fee              : Nat
  victimLossPerTurn : Nat
  turns            : Nat
deriving Repr, DecidableEq

namespace GriefCampaign

variable (g : GriefCampaign)

/-- The attacker's total cost: `turns · fee` (paid into the fee schedule, 50/30/burn-split). -/
def attackerCost : Nat := g.turns * g.fee

/-- The total loss inflicted on the victim: `turns · victimLossPerTurn`. -/
def victimLoss : Nat := g.turns * g.victimLossPerTurn

end GriefCampaign

/-- **`griefing_unprofitable` — THEOREM 2 (CONDITIONAL on the exact fee condition).** If
the per-turn fee is at least the per-turn victim loss (`fee ≥ victimLossPerTurn`), then over ANY
campaign length the attacker's total cost dominates the total victim loss it inflicts:
`attackerCost ≥ victimLoss`. The attacker pays at least one unit of its own value per unit of harm
— griefing is never net-profitable. The fee condition `fee ≥ victimLossPerTurn` is the EXACT
threshold (see the negative tooth). -/
theorem griefing_unprofitable (g : GriefCampaign)
    (hfee : g.victimLossPerTurn ≤ g.fee) :
    g.victimLoss ≤ g.attackerCost := by
  simp only [GriefCampaign.victimLoss, GriefCampaign.attackerCost]
  exact Nat.mul_le_mul_left g.turns hfee

/-- **NEGATIVE TOOTH for Theorem 2.** When the fee is BELOW the per-turn victim loss
(`fee < victimLossPerTurn`), griefing IS profitable: there is a campaign on which the victim's loss
strictly EXCEEDS the attacker's cost (here `turns = 1`, hence any positive length) — the attacker
destroys more victim value than it spends. This proves `fee ≥ victimLossPerTurn` is the exact,
load-bearing condition; the unprofitability is not vacuous. -/
theorem griefing_profitable_when_fee_too_low :
    let g : GriefCampaign := { fee := 3, victimLossPerTurn := 10, turns := 1 }
    g.fee < g.victimLossPerTurn ∧ g.attackerCost < g.victimLoss := by
  refine ⟨by decide, by decide⟩

/-- NON-VACUITY witness for Theorem 2: a concrete campaign meeting the fee condition where the
attacker strictly over-pays for the harm (cost > loss), the honest regime. -/
theorem griefing_unprofitable_nonvacuous :
    let g : GriefCampaign := { fee := 12, victimLossPerTurn := 5, turns := 9 }
    g.victimLossPerTurn ≤ g.fee ∧ g.victimLoss ≤ g.attackerCost := by
  refine ⟨by decide, griefing_unprofitable _ (by decide)⟩

/-! ## §4 — Theorem 3: incentive-compatibility of the 50/30/burn split

The proposer who admits a turn earns `proposerShare fee = fee / 2` (the REAL split from
`Exec.Admission`, reused verbatim). Honest block production is individually rational exactly when
that reward covers the proposer's proving cost. We carry `proveCost` as the named cost bound and
prove the reward dominates it under `proveCost ≤ fee / 2`. -/

/-- The proposer's reward for admitting a turn, in the model's `Int` arithmetic: the real
`Exec.Admission.proposerShare` (50% of the fee, truncated). -/
def proposerReward (fee : Int) : Int := proposerShare fee

/-- `proposerReward` is literally the protocol's `proposerShare` — `fee / 2`. (Defeq sanity check
tying theorem 3 to the audited split, not a re-modelled number.) -/
theorem proposerReward_eq (fee : Int) : proposerReward fee = fee / 2 := rfl

/-- **`proposer_reward_covers_cost` — THEOREM 3 (under a NAMED cost bound).** If the
proposer's proving cost is at most half the fee (`proveCost ≤ fee / 2`, equivalently
`2·proveCost ≤ fee` for the truncation), then the proposer's 50% reward `proposerShare fee` is at
least its cost `proveCost`. Honest block production is individually rational: the proposer is never
out of pocket. The cost bound is the EXACT named hypothesis (negative tooth below). -/
theorem proposer_reward_covers_cost (fee proveCost : Int)
    (hbound : proveCost ≤ fee / 2) :
    proveCost ≤ proposerReward fee := by
  rw [proposerReward_eq]; exact hbound

/-- A self-sufficiency restatement directly in terms of the fee: if the fee is at least twice the
proving cost (`2·proveCost ≤ fee`), the 50% proposer share covers the cost. This is the actionable
form — "set the fee to at least `2·proveCost`". -/
theorem proposer_self_sufficient (fee proveCost : Int)
    (hfee : 2 * proveCost ≤ fee) :
    proveCost ≤ proposerReward fee := by
  apply proposer_reward_covers_cost
  -- `2·proveCost ≤ fee` ⇒ `proveCost ≤ fee / 2` (truncating division of an Int).
  rw [Int.le_ediv_iff_mul_le (by decide : (0:Int) < 2)]
  omega

/-- **NEGATIVE TOOTH for Theorem 3.** When the fee is too low (`fee / 2 < proveCost`, here
`fee = 5`, `proveCost = 3`: `fee/2 = 2 < 3`), the proposer's 50% reward does NOT cover its proving
cost — honest production runs at a LOSS, so it is NOT individually rational. This proves the cost
bound `proveCost ≤ fee/2` is load-bearing: incentive-compatibility is a real constraint on the fee,
not vacuous. -/
theorem proposer_underwater_when_fee_too_low :
    proposerReward 5 < (3 : Int) := by
  rw [proposerReward_eq]; decide

/-- NON-VACUITY witness for Theorem 3: a concrete fee/cost meeting the bound where the proposer
earns strictly more than its cost (a positive margin — production is profitable, not just
break-even). -/
theorem proposer_incentive_nonvacuous :
    (4 : Int) ≤ proposerReward 20 ∧ proposerReward 20 = 10 := by
  refine ⟨proposer_reward_covers_cost 20 4 (by decide), by rw [proposerReward_eq]; decide⟩

/-! ## §5 — The pillar: all three properties hold simultaneously at a concrete healthy schedule.

A single witness in which spam-deterrence, griefing-unprofitability, and proposer
incentive-compatibility ALL hold — the regime the protocol targets (fee tuned above the marginal
junk cost, above the per-turn victim exposure, and above twice the proving cost). -/

/-- A concrete healthy point: `fee = 20`, `proveCost = 4`, victim per-turn exposure `5`. All three
pillar properties hold here (and the negative teeth above show each fails when its fee condition is
violated — the bounds are real). -/
theorem economics_pillar_coherent_witness :
    -- (1) spam deterred: marginal junk cost ≤ fee
    (let φ : FeeSchedule := { fee := 20, proveCost := 4, submitCost := 1 };
      φ.marginalJunkCost ≤ φ.fee ∧ ∀ k, φ.networkWork k ≤ φ.feesCollected k) ∧
    -- (2) griefing unprofitable: victim per-turn exposure ≤ fee
    (let g : GriefCampaign := { fee := 20, victimLossPerTurn := 5, turns := 100 };
      g.victimLossPerTurn ≤ g.fee ∧ g.victimLoss ≤ g.attackerCost) ∧
    -- (3) proposer covers its proving cost: proveCost ≤ fee/2
    ((4 : Int) ≤ proposerReward 20) := by
  refine ⟨⟨by decide, fun k => spam_work_bounded_by_fees _ (by decide) k⟩,
          ⟨by decide, griefing_unprofitable _ (by decide)⟩,
          proposer_reward_covers_cost 20 4 (by decide)⟩

/-! ## §6 — Axiom audit. Each keystone (and each negative tooth) is `#assert_axioms`-clean:
axioms ⊆ {propext, Classical.choice, Quot.sound}. -/

#assert_axioms spam_work_bounded_by_fees
#assert_axioms spam_no_unpaid_work
#assert_axioms spam_work_unbounded_when_fee_too_low
#assert_axioms spam_deterrence_nonvacuous
#assert_axioms griefing_unprofitable
#assert_axioms griefing_profitable_when_fee_too_low
#assert_axioms griefing_unprofitable_nonvacuous
#assert_axioms proposerReward_eq
#assert_axioms proposer_reward_covers_cost
#assert_axioms proposer_self_sufficient
#assert_axioms proposer_underwater_when_fee_too_low
#assert_axioms proposer_incentive_nonvacuous
#assert_axioms economics_pillar_coherent_witness

end Dregg2.Distributed.Economics
