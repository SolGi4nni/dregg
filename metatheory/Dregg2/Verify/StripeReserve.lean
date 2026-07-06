/-
# Dregg2.Verify.StripeReserve — the money-in RESERVE (Route α) + the APEX loss-bound.

The Stripe money-in reserve IS the Trustline fullReserve channel (`Apps.Trustline.ChannelC`, design
doc §4.2, "Route α"). The symbol binding:

  * spent-provisional exposure          = `drawn`
  * R (the disclosed reserve line)       = `ceiling`
  * realized reversal loss absorbed      = `settled`
  * reserve fund remaining               = `escrow = R − settled`

Every solvency property is a symbol-binding INSTANCE of the PROVED Trustline theorems — no new proof
of the core. The guarantee is unconditional over the dynamics: for ANY attest/reverse/spend/finalize
schedule (`SSched`), dregg's realized loss never exceeds the reserve R (`net ≥ −R`) and the reserve
fund is never negative — a proved theorem about the reserve `R` (real collateral). The payment
attestation is the `StripeAttest.stripe_attest_sound` gate (see `StripeBridgeV2`), an explicit
hypothesis (the §8 verify predicate).
-/
import Dregg2.Apps.Trustline

namespace Dregg2.Verify.StripeReserve

open Dregg2.Apps.Trustline

/-- The Stripe money-in reserve = a Trustline fullReserve channel. -/
abbrev MoneyInReserve := ChannelC

/-- Open a money-in reserve funded to line `R` (the disclosed reserve parameter). -/
def openReserve (R : Nat) : MoneyInReserve := ChannelC.openReserve R 0 0

/-- A freshly-opened reserve is well-formed (ReserveWF). -/
theorem openReserve_wf (R : Nat) : (openReserve R).ReserveWF := openReserve_ReserveWF R 0 0

/-! ## The reserve `≤`-forever core (Route α — reuse of Trustline by instantiation). -/

/-- **`stripe_exposure_within_reserve_forever`** (design Theorem 14): spent-provisional exposure
(`drawn`) never exceeds the reserve line R (`ceiling`), at EVERY reachable state along EVERY
adversarial schedule — a provisional spend commits only to the extent the reserve backs it. -/
theorem stripe_exposure_within_reserve_forever
    (c₀ : MoneyInReserve) (hinit : c₀.ReserveWF) (sched : SSched) :
    ∀ n, (trajC .fullReserve c₀ sched n).s.tl.drawn
          ≤ (trajC .fullReserve c₀ sched n).s.tl.ceiling :=
  fun n => (reserveWF_forever c₀ hinit sched n).1.1.1

/-- **`stripe_reserve_solvent_forever` (APEX):** the reserve fund (`escrow = R − settled`) is NEVER
NEGATIVE at any reachable state, along every adversarial attest/reverse/spend/finalize schedule.
≔ `escrow_solvent_forever` — the deployed solvency core. -/
theorem stripe_reserve_solvent_forever
    (c₀ : MoneyInReserve) (hinit : c₀.ReserveWF) (sched : SSched) :
    ∀ n, 0 ≤ (trajC .fullReserve c₀ sched n).escrow :=
  escrow_solvent_forever c₀ hinit sched

/-- **`stripe_money_in_loss_bounded` (APEX, net form):** dregg's realized loss (`settled`, reserve
consumed by reversals) never exceeds the disclosed reserve R (`ceiling`), for ANY schedule — i.e.
`net = −settled ≥ −R`. The two-line consequence of the escrow being non-negative
(`escrow = R − settled ≥ 0 ⟹ settled ≤ R`). THE money-in guarantee: loss-bounded under an
adversarial oracle by a named, disclosed reserve. -/
theorem stripe_money_in_loss_bounded
    (c₀ : MoneyInReserve) (hinit : c₀.ReserveWF) (sched : SSched) :
    ∀ n, ((trajC .fullReserve c₀ sched n).s.settled : Int)
          ≤ ((trajC .fullReserve c₀ sched n).s.tl.ceiling : Int) := by
  intro n
  have hs := stripe_reserve_solvent_forever c₀ hinit sched n
  obtain ⟨_, he⟩ := reserveWF_forever c₀ hinit sched n
  omega

/-! ## Non-vacuity: an opened reserve is well-formed and the guarantees are inhabited. -/

#guard decide (openReserve 100).ReserveWF

/-! ## Axiom hygiene: the reserve apexes self-guard against a future axiom leak in their own
derivation (the tripwire fails the build if the whitelist `{propext, Classical.choice, Quot.sound}`
is ever escaped). -/

#assert_axioms stripe_exposure_within_reserve_forever
#assert_axioms stripe_reserve_solvent_forever
#assert_axioms stripe_money_in_loss_bounded

end Dregg2.Verify.StripeReserve
