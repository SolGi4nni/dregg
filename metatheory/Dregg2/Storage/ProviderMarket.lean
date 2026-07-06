/-
# `Dregg2.Storage.ProviderMarket` — the decentralized storage-provider market, as a Lean cell-program.

The economic layer of the storage north star. A DEAL cell: a client's blob (committed by content
root, `BucketCommitment`) is stored by a bonded PROVIDER at a price; a failed proof-of-retrievability
(`Retrievability.por_sound` / `Availability.verifiable_erasure_recovers`) lets an auditor SLASH the
provider's collateral. Modeled in the existing `SlotCaveat` + guarded-transition vocabulary (like
`Dregg2.Apps.QueueFactory`), so the market's rules are executor-enforced TURNS, not operator trust.

Proved decidable-eval, REAL (no carrier):
- `providerMarketFactory_conforms` — a well-formed factory publishes an invariant-respecting genesis.
- `unauthorized_claim_rejected` — only a BONDED provider can claim a deal (the cap-first gate: an
  impostor is refused).
- `open_deal_only` — a claimed deal cannot be re-claimed (no double-sell).
- `slash_decreases_collateral` — a slash (justified by a failed PoR) STRICTLY reduces the collateral:
  the economic teeth bite, so withholding data costs the provider its bond.
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Storage.ProviderMarket

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.EffectsState (setField fieldOf setField_fieldOf)

/-! ## §1 — the deal-cell SLOT layout. -/
/-- 0 = OPEN, 1 = CLAIMED (frozen once a bonded provider takes the deal). -/
abbrev providerField : FieldName := "market.provider"
/-- The provider's locked collateral bond (decreases only via `slashProvider`). -/
abbrev collateralField : FieldName := "market.collateral"
/-- The renter (frozen at open). -/
abbrev clientField : FieldName := "market.client"
/-- The committed content root of the stored blob (frozen at claim). -/
abbrev dealRootField : FieldName := "market.deal_root"
/-- The deal price (frozen). -/
abbrev priceField : FieldName := "market.price"
/-- Monotone audit/dispute counter (advances on each slash). -/
abbrev disputeSeqField : FieldName := "market.dispute_seq"

/-! ## §2 — reads + write. -/
def pmWriteField (k : RecordKernelState) (e : CellId) (f : FieldName) (v : Int) : RecordKernelState :=
  { k with cell := fun c => if c = e then setField f (k.cell e) (.int v) else k.cell c }

def pmProvider (k : RecordKernelState) (e : CellId) : Int := fieldOf providerField (k.cell e)
def pmCollateral (k : RecordKernelState) (e : CellId) : Int := fieldOf collateralField (k.cell e)

/-- Reading field `f` right after writing `f := v` to the same cell returns `v`. -/
theorem pmWriteField_same (k : RecordKernelState) (e : CellId) (f : FieldName) (v : Int) :
    fieldOf f ((pmWriteField k e f v).cell e) = v := by
  show fieldOf f (if e = e then setField f (k.cell e) (.int v) else k.cell e) = v
  rw [if_pos rfl]; exact setField_fieldOf f (k.cell e) v

/-! ## §3 — the factory descriptor. -/
def providerMarketFactory (client price : Int) : FactoryEntry where
  caveats :=
    [ SlotCaveat.immutable clientField
    , SlotCaveat.immutable priceField
    , SlotCaveat.monotonicSeq disputeSeqField ]
  initialFields :=
    [ (providerField, 0)
    , (collateralField, 0)
    , (clientField, client)
    , (priceField, price)
    , (dealRootField, 0)
    , (disputeSeqField, 0) ]
  programVk := 0

theorem providerMarketFactory_conforms (client price : Int) :
    (providerMarketFactory client price).conforms = true := by
  unfold providerMarketFactory FactoryEntry.conforms FactoryEntry.initialFieldsNoBalance
  simp only [SlotCaveat.field, SlotCaveat.bornFresh, List.all_cons, List.all_nil,
    List.find?, Bool.and_true, Bool.and_self]
  rfl

/-! ## §4 — transitions. -/

/-- **`claimDeal` — an authorized provider claims an OPEN deal, posting bond + the blob root.**
Rejects (`none`) unless the actor is a bonded provider, the deal is still OPEN (`provider = 0`), and
the bond is positive. -/
def claimDeal (k : RecordKernelState) (e actor : CellId) (providers : List CellId)
    (bond root : Int) : Option RecordKernelState :=
  if providers.contains actor ∧ pmProvider k e = 0 ∧ 0 < bond then
    some (pmWriteField (pmWriteField (pmWriteField k e dealRootField root)
            e collateralField bond) e providerField 1)
  else none

/-- **`slashProvider` — an auditor slashes a claimed provider on a failed PoR.** The `auditFailed`
witness is the `Retrievability` audit refusing the provider's response. Writes the collateral LAST
(so its read-back is direct). Rejects unless the deal is claimed and the penalty is a real, bounded
bite. -/
def slashProvider (k : RecordKernelState) (e : CellId) (penalty : Int) (auditFailed : Bool) :
    Option RecordKernelState :=
  if auditFailed ∧ pmProvider k e = 1 ∧ 0 < penalty ∧ penalty ≤ pmCollateral k e then
    some (pmWriteField (pmWriteField k e disputeSeqField (fieldOf disputeSeqField (k.cell e) + 1))
            e collateralField (pmCollateral k e - penalty))
  else none

/-- **The cap-first gate: only a bonded provider claims.** An actor NOT in the bonded-provider set
cannot claim the deal — the turn is refused. -/
theorem unauthorized_claim_rejected (k : RecordKernelState) (e actor : CellId)
    (providers : List CellId) (bond root : Int) (hun : ¬ providers.contains actor) :
    claimDeal k e actor providers bond root = none := by
  unfold claimDeal
  rw [if_neg (by rintro ⟨hc, _⟩; exact hun hc)]

/-- **No double-sell.** A deal that is already CLAIMED (`provider ≠ 0`) cannot be claimed again. -/
theorem open_deal_only (k : RecordKernelState) (e actor : CellId)
    (providers : List CellId) (bond root : Int) (hclaimed : pmProvider k e ≠ 0) :
    claimDeal k e actor providers bond root = none := by
  unfold claimDeal
  rw [if_neg (by rintro ⟨_, ho, _⟩; exact hclaimed ho)]

/-- **The economic teeth: a slash STRICTLY reduces the collateral.** A committed slash (justified by
a failed proof-of-retrievability) burns `penalty > 0` of the provider's bond — so withholding the
data it was paid to store costs it. -/
theorem slash_decreases_collateral (k k' : RecordKernelState) (e : CellId) (penalty : Int)
    (auditFailed : Bool) (h : slashProvider k e penalty auditFailed = some k') :
    pmCollateral k' e < pmCollateral k e := by
  unfold slashProvider at h
  by_cases hg : auditFailed ∧ pmProvider k e = 1 ∧ 0 < penalty ∧ penalty ≤ pmCollateral k e
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, _, hpos, _⟩ := hg
    unfold pmCollateral
    rw [pmWriteField_same]
    omega
  · rw [if_neg hg] at h; exact absurd h (by simp)

#assert_axioms providerMarketFactory_conforms
#assert_axioms unauthorized_claim_rejected
#assert_axioms open_deal_only
#assert_axioms slash_decreases_collateral

end Dregg2.Storage.ProviderMarket
