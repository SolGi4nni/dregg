/-
# `Dregg2.Storage.DealPayment` — the market conserves value (no minting, no destruction).

`DealLifecycle` proved the state machine; this proves the MONEY. A deal holds two locked amounts —
the provider's `bond` and the client's prepaid `escrow` (the price). The two terminal payouts move
value between buckets but never create or destroy it:
* **settle** pays the provider the escrow AND returns the bond;
* **slash** burns the bond and refunds the escrow to the client.
The invariant `total` (bond + escrow + everything paid/refunded/burned) is preserved by both — so the
market is not a money pump in either direction, and a slashed bond really is *burned*, not vanished.
-/
import Dregg2.Tactics

namespace Dregg2.Storage.DealPayment

/-- The value ledger of a deal: the two locked amounts plus the three sinks value can flow to. -/
structure Ledger where
  bond : Nat             -- provider's locked collateral
  escrow : Nat           -- client's prepaid payment (the price)
  paidToProvider : Nat   -- released to the provider
  refundedToClient : Nat -- returned to the client
  burned : Nat           -- slashed / destroyed
deriving Repr, DecidableEq

/-- Total value in the system — the conserved quantity. -/
def total (l : Ledger) : Nat :=
  l.bond + l.escrow + l.paidToProvider + l.refundedToClient + l.burned

/-- **Settle payout.** The provider is paid the escrow (the price) and the bond is returned to it;
both locked slots empty into `paidToProvider`. -/
def settlePay (l : Ledger) : Ledger :=
  { l with bond := 0, escrow := 0, paidToProvider := l.paidToProvider + l.escrow + l.bond }

/-- **Slash payout.** The bond is BURNED (up to `penalty`) and the escrow is REFUNDED to the client —
value the provider forfeits does not evaporate; it is accounted as `burned`. -/
def slashPay (l : Ledger) (penalty : Nat) : Ledger :=
  { l with
    bond := l.bond - penalty,
    escrow := 0,
    refundedToClient := l.refundedToClient + l.escrow,
    burned := l.burned + min penalty l.bond }

/-- **Settle conserves value.** -/
theorem settle_conserves_value (l : Ledger) : total (settlePay l) = total l := by
  simp only [total, settlePay]; omega

/-- **Slash conserves value** — the forfeited bond is burned, not vanished; the escrow is refunded,
not lost. -/
theorem slash_conserves_value (l : Ledger) (penalty : Nat) :
    total (slashPay l penalty) = total l := by
  simp only [total, slashPay]; omega

/-- **A slash strictly destroys the provider's stake** (up to its bond): `burned` grows by exactly
the amount the `bond` shrinks. The economic tooth is real, and it is a *burn*, not a transfer to the
house. -/
theorem slash_burn_is_the_bond_reduction (l : Ledger) (penalty : Nat) :
    (slashPay l penalty).burned - l.burned = l.bond - (slashPay l penalty).bond := by
  simp only [slashPay]; omega

#assert_axioms settle_conserves_value
#assert_axioms slash_conserves_value
#assert_axioms slash_burn_is_the_bond_reduction

end Dregg2.Storage.DealPayment
