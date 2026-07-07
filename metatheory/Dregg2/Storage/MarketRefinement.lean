/-
# `Dregg2.Storage.MarketRefinement` — the executor-wired cell-program REFINES the abstract protocol.

`ProviderMarket` is the field-based cell-program the executor actually runs; `DealLifecycle` is the
abstract protocol whose soundness we proved. This closes the seam: an abstraction `abstractDeal` maps
a `ProviderMarket` cell to a `DealLifecycle.Deal`, and the executor's `claimDeal` — when it admits a
claim on an open deal — makes EXACTLY the abstract `claim` transition (open → claimed, bond locked).
So the deployed market's claim IS the proven protocol's claim, not merely a lookalike.

(`ProviderMarket` is coarser than the full lifecycle — it collapses the audit states into a
`slashProvider auditFailed` bit — so only the claim leg refines directly; aligning the slash leg is
the remaining mechanical step, tracked in GOAL.)
-/
import Dregg2.Apps.QueueFactory
import Dregg2.Storage.ProviderMarket
import Dregg2.Storage.DealLifecycle

namespace Dregg2.Storage.MarketRefinement

open Dregg2.Exec
open Dregg2.Exec.EffectsState (fieldOf)
open Dregg2.Storage.ProviderMarket
open Dregg2.Storage.DealLifecycle (Deal)

/-- Reading a DIFFERENT field after a `pmWriteField` is unchanged. -/
theorem pmWriteField_other (k : RecordKernelState) (e : CellId) (f g : FieldName) (v : Int)
    (hgf : g ≠ f) : fieldOf g ((pmWriteField k e f v).cell e) = fieldOf g (k.cell e) := by
  show fieldOf g (if e = e then EffectsState.setField f (k.cell e) (.int v) else k.cell e) = _
  rw [if_pos rfl]
  exact Dregg2.Apps.QueueFactory.fieldOf_setField_ne f g (k.cell e) v hgf

/-- Abstract a `ProviderMarket` cell into a `DealLifecycle` deal: `provider = 0` ⟹ open, else claimed;
the collateral is the bond. -/
def abstractDeal (k : RecordKernelState) (e : CellId) : Deal :=
  { state := if pmProvider k e = 0 then .open else .claimed,
    bond := (pmCollateral k e).toNat }

/-- **`ProviderMarket.claimDeal` REFINES `DealLifecycle.claim`.** When the executor admits a claim on
an OPEN deal, the abstract deal makes exactly the abstract `claim` transition — open → claimed with
the bond locked. The deployed cell-program's claim IS the proven protocol's claim. -/
theorem claimDeal_refines_claim (k k' : RecordKernelState) (e actor : CellId)
    (providers : List CellId) (bond root : Int)
    (h : claimDeal k e actor providers bond root = some k') :
    (abstractDeal k e).state = .open ∧
      abstractDeal k' e = { state := .claimed, bond := bond.toNat } := by
  unfold claimDeal at h
  by_cases hg : providers.contains actor ∧ pmProvider k e = 0 ∧ 0 < bond
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    obtain ⟨_, hopen, _⟩ := hg
    subst h
    have hprov : pmProvider (pmWriteField (pmWriteField (pmWriteField k e dealRootField root)
        e collateralField bond) e providerField 1) e = 1 :=
      pmWriteField_same _ e providerField 1
    have hcoll : pmCollateral (pmWriteField (pmWriteField (pmWriteField k e dealRootField root)
        e collateralField bond) e providerField 1) e = bond := by
      unfold pmCollateral
      rw [pmWriteField_other _ e providerField collateralField 1 (by decide)]
      exact pmWriteField_same _ e collateralField bond
    refine ⟨by simp [abstractDeal, hopen], ?_⟩
    simp only [abstractDeal, hprov, hcoll]
    norm_num
  · rw [if_neg hg] at h
    exact absurd h (by simp)

#assert_axioms pmWriteField_other
#assert_axioms claimDeal_refines_claim

end Dregg2.Storage.MarketRefinement
