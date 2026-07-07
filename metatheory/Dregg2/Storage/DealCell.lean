/-
# `Dregg2.Storage.DealCell` — the FAITHFUL executor cell-program: every leg refines the protocol.

`MarketRefinement` refined the *claim* leg of the coarse `ProviderMarket`. This is the faithful cell:
a deal cell carries an explicit `status` slot (the encoded `DealState`) and a `bond` slot, and each of
the SIX guarded transitions — claim, activate, auditPass, auditFail, settle, slash — provably makes
exactly its `DealLifecycle` counterpart under the abstraction `absDeal`. So the deployed cell-program
is the abstract protocol, ALL legs, ALL alignments — no coarsening, no collapsed audit states.
-/
import Dregg2.Apps.QueueFactory
import Dregg2.Storage.ProviderMarket
import Dregg2.Storage.MarketRefinement
import Dregg2.Storage.DealLifecycle

namespace Dregg2.Storage.DealCell

open Dregg2.Exec
open Dregg2.Exec.EffectsState (fieldOf)
open Dregg2.Storage.ProviderMarket (pmWriteField pmWriteField_same)
open Dregg2.Storage.MarketRefinement (pmWriteField_other)
open Dregg2.Storage.DealLifecycle

abbrev statusField : FieldName := "deal.status"
abbrev bondField : FieldName := "deal.bond"

/-- Encode a lifecycle state as the cell's status felt. -/
def enc : DealState → Int
  | .open => 0 | .claimed => 1 | .active => 2 | .auditedPass => 3
  | .auditedFail => 4 | .settled => 5 | .slashed => 6

/-- Decode the status felt back to a state (inverse of `enc`, `open` off-range). -/
def dec (i : Int) : DealState :=
  if i = 1 then .claimed else if i = 2 then .active else if i = 3 then .auditedPass
  else if i = 4 then .auditedFail else if i = 5 then .settled else if i = 6 then .slashed
  else .open

theorem dec_enc (s : DealState) : dec (enc s) = s := by cases s <;> decide

def st (k : RecordKernelState) (e : CellId) : Int := fieldOf statusField (k.cell e)
def bd (k : RecordKernelState) (e : CellId) : Int := fieldOf bondField (k.cell e)

/-- Abstract a deal cell into a `DealLifecycle.Deal`. -/
def absDeal (k : RecordKernelState) (e : CellId) : Deal :=
  { state := dec (st k e), bond := (bd k e).toNat }

/-- Write a new status, preserving the bond. -/
def setStatus (k : RecordKernelState) (e : CellId) (s : DealState) : RecordKernelState :=
  pmWriteField k e statusField (enc s)
/-- Write a new status AND bond. -/
def setStatusBond (k : RecordKernelState) (e : CellId) (s : DealState) (b : Int) : RecordKernelState :=
  pmWriteField (pmWriteField k e bondField b) e statusField (enc s)

/-! ## §1 — the six guarded transitions (mirror `DealLifecycle`). -/

def claimCell (k : RecordKernelState) (e : CellId) (b : Int) : Option RecordKernelState :=
  if st k e = 0 then some (setStatusBond k e .claimed b) else none
def activateCell (k : RecordKernelState) (e : CellId) : Option RecordKernelState :=
  if st k e = 1 then some (setStatus k e .active) else none
def auditPassCell (k : RecordKernelState) (e : CellId) : Option RecordKernelState :=
  if st k e = 2 then some (setStatus k e .auditedPass) else none
def auditFailCell (k : RecordKernelState) (e : CellId) : Option RecordKernelState :=
  if st k e = 2 then some (setStatus k e .auditedFail) else none
def settleCell (k : RecordKernelState) (e : CellId) : Option RecordKernelState :=
  if st k e = 3 then some (setStatus k e .settled) else none
def slashCell (k : RecordKernelState) (e : CellId) (penalty : Int) : Option RecordKernelState :=
  if st k e = 4 then
    some (setStatusBond k e .slashed (Int.ofNat ((bd k e).toNat - penalty.toNat))) else none

/-! ## §2 — read-back helpers over the writes. -/

theorem setStatus_st (k e s) : st (setStatus k e s) e = enc s := pmWriteField_same k e statusField (enc s)
theorem setStatus_bd (k e s) : bd (setStatus k e s) e = bd k e := by
  unfold bd setStatus; exact pmWriteField_other k e statusField bondField (enc s) (by decide)
theorem setStatusBond_st (k e s b) : st (setStatusBond k e s b) e = enc s :=
  pmWriteField_same _ e statusField (enc s)
theorem setStatusBond_bd (k e s b) : bd (setStatusBond k e s b) e = b := by
  unfold bd setStatusBond
  rw [pmWriteField_other _ e statusField bondField (enc s) (by decide)]
  exact pmWriteField_same k e bondField b

/-! ## §3 — the SIX refinement theorems: every leg IS its `DealLifecycle` counterpart. -/

/-- A status-only transition (guard `st = enc src`, write `dst`, bond preserved) refines the abstract
transition `tr` whenever `tr` fires from `src` to `dst` preserving the bond. -/
private theorem statusOnly_refines {src dst : DealState} {tr : Deal → Option Deal}
    (k k' : RecordKernelState) (e : CellId)
    (hcell : (if st k e = enc src then some (setStatus k e dst) else none) = some k')
    (htr : ∀ d, d.state = src → tr d = some { d with state := dst }) :
    tr (absDeal k e) = some (absDeal k' e) := by
  by_cases hg : st k e = enc src
  · rw [if_pos hg] at hcell; simp only [Option.some.injEq] at hcell; subst hcell
    have hsrc : (absDeal k e).state = src := by
      simp only [absDeal]; rw [hg]; exact dec_enc src
    rw [htr _ hsrc]
    simp only [absDeal, setStatus_st, setStatus_bd, dec_enc]
  · rw [if_neg hg] at hcell; exact absurd hcell (by simp)

theorem activateCell_refines (k k' : RecordKernelState) (e : CellId) (h : activateCell k e = some k') :
    activate (absDeal k e) = some (absDeal k' e) :=
  statusOnly_refines (src := .claimed) (dst := .active) k k' e h
    (fun d hd => by simp [activate, hd])

theorem auditPassCell_refines (k k' : RecordKernelState) (e : CellId) (h : auditPassCell k e = some k') :
    auditPass (absDeal k e) = some (absDeal k' e) :=
  statusOnly_refines (src := .active) (dst := .auditedPass) k k' e h
    (fun d hd => by simp [auditPass, hd])

theorem auditFailCell_refines (k k' : RecordKernelState) (e : CellId) (h : auditFailCell k e = some k') :
    auditFail (absDeal k e) = some (absDeal k' e) :=
  statusOnly_refines (src := .active) (dst := .auditedFail) k k' e h
    (fun d hd => by simp [auditFail, hd])

theorem settleCell_refines (k k' : RecordKernelState) (e : CellId) (h : settleCell k e = some k') :
    settle (absDeal k e) = some (absDeal k' e) :=
  statusOnly_refines (src := .auditedPass) (dst := .settled) k k' e h
    (fun d hd => by simp [settle, hd])

theorem claimCell_refines (k k' : RecordKernelState) (e : CellId) (b : Int)
    (h : claimCell k e b = some k') :
    claim (absDeal k e) b.toNat = some (absDeal k' e) := by
  by_cases hg : st k e = 0
  · unfold claimCell at h; rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
    have hsrc : (absDeal k e).state = .open := by
      simp only [absDeal]; rw [show st k e = enc .open from hg]; exact dec_enc .open
    rw [claim, hsrc]
    simp only [absDeal, setStatusBond_st, setStatusBond_bd, dec_enc]
  · unfold claimCell at h; rw [if_neg hg] at h; exact absurd h (by simp)

theorem slashCell_refines (k k' : RecordKernelState) (e : CellId) (penalty : Int)
    (h : slashCell k e penalty = some k') :
    slash (absDeal k e) penalty.toNat = some (absDeal k' e) := by
  unfold slashCell at h
  by_cases hg : st k e = 4
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
    have hsrc : (absDeal k e).state = .auditedFail := by
      simp only [absDeal]; rw [show st k e = enc .auditedFail from hg]; exact dec_enc .auditedFail
    rw [slash, hsrc]
    have hofNat : (Int.ofNat ((bd k e).toNat - penalty.toNat)).toNat = (bd k e).toNat - penalty.toNat := rfl
    simp only [absDeal, setStatusBond_st, setStatusBond_bd, dec_enc, hofNat]
  · rw [if_neg hg] at h; exact absurd h (by simp)


#assert_axioms dec_enc
#assert_axioms claimCell_refines
#assert_axioms activateCell_refines
#assert_axioms auditPassCell_refines
#assert_axioms auditFailCell_refines
#assert_axioms settleCell_refines
#assert_axioms slashCell_refines

end Dregg2.Storage.DealCell
