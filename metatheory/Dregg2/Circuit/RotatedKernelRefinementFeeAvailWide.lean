/-
# Dregg2.Circuit.RotatedKernelRefinementFeeAvailWide — the FEE'D-transfer availability discharged
on the WIDE + WELDED registry members (the wide-fee availability wrap-forgery, closed in-proof).

## What this module is

`RotatedKernelRefinementFeeAvail` discharged the §11.8 fee availability on the NARROW hardened
wire member (`transferFeeV3AvailWire`). The DEPLOYED light client, however, resolves the WIDE
registry (`WIDE_REGISTRY_STAGED_TSV`) and its umem-welded twin — whose fee'd-transfer member
(`transferFeeVmDescriptor2R24`, tail position 44, the LIVE SOVEREIGN transfer's effect-vm leg)
was still built over the BARE fee face, so the underflow-wrap mint-from-nothing stayed open on
the wide leg THROUGH EITHER DEBIT LEG (amount OR fee). With the emission retarget
(`AvailWideFeeMember` + the `EffectVmEmitUMemWeldWide` crown arm), this module carries the fee
availability discharge to the EXACT post-retarget wire objects:

  * **`transferFeeAvailWide`** — the bare-wide fee crown row (rc pins + wide carriers; the fee
    key carries NO capacity-floor refuse — the deployed fee member's wrapper shape);
  * **`weldedTransferFeeAvailWide`** — its umem-welded twin (the welded-registry row).

The chain: welded accept → (`satisfied2_of_weldUMemIntoWide`, the weld appends ONE row-locally
trivial `umemOp` and nothing else) the wide fee member → (`feeAvailWide_row_v1`, the FEE-PINNED
membership-parametric wide collapse `wideEmbeddedFee_sound_v1`) the hardened fee face's per-row
`satisfiedVm` → (`transferFeeAvail_derives_availability_row`, at the row's own flags) on the
designated ACTIVE debit row:

    `amount ≤ before  ∧  amount + fee ≤ before  ∧  after = before − amount − fee`  (over ℤ)

— availability INCLUDING the fee, and the EXACT move (no wrap witness through either leg). The
credit twin (`transferFeeAvail_credit_exact`) rides the same collapse. THE TEETH: both GAP #4
wrap-forgery witnesses (the fee-leg `before=1, amount=0, fee=1006632961` and the amount-leg
`before=1, amount=1006632961` — which the BARE wide fee member ADMITS) are UNSAT on the wide and
welded members.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. NEW file; imports
are read-only.
-/
import Dregg2.Circuit.RotatedKernelRefinementFeeAvail
import Dregg2.Circuit.Emit.AvailWideFeeMember
import Dregg2.Circuit.Emit.EffectVmEmitUMemWeldWide

namespace Dregg2.Circuit.RotatedKernelRefinementFeeAvailWide

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
open Dregg2.Circuit.Emit.AvailWideFeeMember (transferFeeAvailWide feeAvailWide_row_v1)
open Dregg2.Circuit.Emit.EffectVmEmitUMemWeldWide
  (weldUMemIntoWide satisfied2_of_weldUMemIntoWide wideUMemWeldSuffix wideKeyUMemDomain
   weldedWideRegistry crownWideHosts)
open Dregg2.Circuit.RotatedKernelRefinementAvail (RotTableSideW)
open Dregg2.Crypto.UniversalMemory (Domain)

set_option autoImplicit false

/-! ## §0 — the WELDED wide fee member (the exact welded-registry wire object for the fee key
post-retarget). -/

/-- The WELDED wide fee'd transfer as EMITTED (the heap-domain umem weld over the retargeted
wide fee member — transfer moves `Balance`, so `wideKeyUMemDomain "transferFeeVmDescriptor2R24"
= heap`; NO refuse on the fee key). -/
def weldedTransferFeeAvailWide : EffectVmDescriptor2 :=
  weldUMemIntoWide transferFeeAvailWide Domain.heap

-- The welded fee twin carries the weld marker, the +7 no-narrowing geometry, and the fee avail
-- name key (the Rust `avail_pad_for_descriptor_name` pad-16 prefix survives every wrapper).
#guard weldedTransferFeeAvailWide.name.endsWith wideUMemWeldSuffix
#guard weldedTransferFeeAvailWide.name.startsWith "dregg-effectvm-transfer-v1-fee-avail"
#guard weldedTransferFeeAvailWide.traceWidth == transferFeeAvailWide.traceWidth + 7
#guard weldedTransferFeeAvailWide.piCount == transferFeeAvailWide.piCount
#guard wideKeyUMemDomain "transferFeeVmDescriptor2R24" = Domain.heap
-- The registry rows ARE these members (the retarget landed name-stable under the LIVE key).
#guard (crownWideHosts.filter (·.1 == "transferFeeVmDescriptor2R24")).all
  (fun e => e.2.name == "dregg-effectvm-transfer-v1-fee-avail-rot24-v3-staged")
#guard (weldedWideRegistry.filter (·.1 == "transferFeeVmDescriptor2R24")).all
  (fun e => e.2.name.startsWith "dregg-effectvm-transfer-v1-fee-avail")

/-! ## §1 — the peel + the per-row v1 collapses on the WIRE objects. -/

/-- `Satisfied2` of the WELDED fee row peels to the wide fee member (the umem weld appends ONE
row-locally-`True` `umemOp` + two tables — the §11.8 borrow/carry chains survive untouched). -/
theorem satisfied2_of_weldedTransferFeeAvailWide (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash weldedTransferFeeAvailWide minit mfin maddrs t) :
    Satisfied2 hash transferFeeAvailWide minit mfin maddrs t :=
  satisfied2_of_weldUMemIntoWide hash transferFeeAvailWide _ h

/-- A wide-fee witness forces the hardened fee face's FULL v1 denotation on every row. -/
theorem wideFeeAvail_row_v1 (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferFeeAvailWide minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    satisfiedVm hash transferFeeVmDescriptorAvail
      (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
  feeAvailWide_row_v1 permOut hash minit mfin maddrs t (hside.toFaithfulW hsat) i hi

/-- A WELDED wide-fee witness forces the same v1 denotation (umem weld off first). -/
theorem weldedFeeAvail_row_v1 (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash weldedTransferFeeAvailWide minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    satisfiedVm hash transferFeeVmDescriptorAvail
      (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
  wideFeeAvail_row_v1 hash hside (satisfied2_of_weldedTransferFeeAvailWide hash hsat) i hi

/-! ## §2 — THE WIDE DISCHARGE: fee'd availability + the exact ℤ move, forced by a wide /
welded-registry witness. -/

/-- **`wideFee_availability_and_exact_move_forced`** — the wide fee wrap-forgery closed. A
`Satisfied2` witness of the retargeted WIDE fee member forces, on any designated ACTIVE debit
row (`direction = 1`, not the wrap/pad last row) under the deployed canonicality envelope:
`amount ≤ before.bal_lo`, `amount + fee ≤ before.bal_lo` (availability INCLUDING the fee — both
debit legs), AND the exact ℤ move `after = before − amount − fee` (no wrap witness exists
through EITHER leg). -/
theorem wideFee_availability_and_exact_move_forced (hash : List ℤ → ℤ)
    {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferFeeAvailWide minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921)
    (hdir : (envAt t i).loc (prmCol param.DIRECTION) = 1) :
    (envAt t i).loc (prmCol param.AMOUNT) ≤ (envAt t i).loc (sbCol state.BALANCE_LO)
    ∧ (envAt t i).loc (prmCol param.AMOUNT) + (envAt t i).loc feeCol
        ≤ (envAt t i).loc (sbCol state.BALANCE_LO)
    ∧ (envAt t i).loc (saCol state.BALANCE_LO)
        = (envAt t i).loc (sbCol state.BALANCE_LO) - (envAt t i).loc (prmCol param.AMOUNT)
          - (envAt t i).loc feeCol := by
  have hv1 := wideFeeAvail_row_v1 hash hside hsat i hi
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  rw [hlastf] at hv1
  exact transferFeeAvail_derives_availability_row hash (envAt t i) (i == 0)
    hcanon hv1 hdir

/-- The same discharge on the WELDED wide fee row (the exact welded-registry wire object). -/
theorem wideFee_availability_and_exact_move_forced_welded (hash : List ℤ → ℤ)
    {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash weldedTransferFeeAvailWide minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921)
    (hdir : (envAt t i).loc (prmCol param.DIRECTION) = 1) :
    (envAt t i).loc (prmCol param.AMOUNT) ≤ (envAt t i).loc (sbCol state.BALANCE_LO)
    ∧ (envAt t i).loc (prmCol param.AMOUNT) + (envAt t i).loc feeCol
        ≤ (envAt t i).loc (sbCol state.BALANCE_LO)
    ∧ (envAt t i).loc (saCol state.BALANCE_LO)
        = (envAt t i).loc (sbCol state.BALANCE_LO) - (envAt t i).loc (prmCol param.AMOUNT)
          - (envAt t i).loc feeCol :=
  wideFee_availability_and_exact_move_forced hash hside
    (satisfied2_of_weldedTransferFeeAvailWide hash hsat) i hi hnotlast hcanon hdir

/-- The CREDIT-side exactness on the welded wide row (the credit twin): `after = before +
amount − fee` over ℤ, no overflow wrap through the credit leg, no underflow wrap through the
fee leg. -/
theorem wideFee_credit_exact_forced_welded (hash : List ℤ → ℤ)
    {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash weldedTransferFeeAvailWide minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921)
    (hdir : (envAt t i).loc (prmCol param.DIRECTION) = 0) :
    (envAt t i).loc feeCol
        ≤ (envAt t i).loc (sbCol state.BALANCE_LO) + (envAt t i).loc (prmCol param.AMOUNT)
    ∧ (envAt t i).loc (saCol state.BALANCE_LO)
        = (envAt t i).loc (sbCol state.BALANCE_LO) + (envAt t i).loc (prmCol param.AMOUNT)
          - (envAt t i).loc feeCol := by
  have hv1 := weldedFeeAvail_row_v1 hash hside hsat i hi
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  rw [hlastf] at hv1
  exact transferFeeAvail_credit_exact hash (envAt t i) (i == 0)
    hcanon hv1 hdir

/-! ## §3 — THE TEETH: both wrap-forgery witnesses are UNSAT on the wide + welded members. -/

/-- **THE FEE-LEG FORGERY IS UNSAT ON THE WIDE MEMBER.** The fee wrap witness (`before=1,
amount=0, fee=1006632961, direction=1` — the fee member of the GAP #4 forgery family, which the
BARE wide fee member ADMITS) cannot ride any satisfying witness of the retargeted wide fee
member. -/
theorem wideFee_fee_forgery_unsat (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferFeeAvailWide minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921)
    (hdir : (envAt t i).loc (prmCol param.DIRECTION) = 1)
    (hbefore : (envAt t i).loc (sbCol state.BALANCE_LO) = 1)
    (hamount : (envAt t i).loc (prmCol param.AMOUNT) = 0)
    (hfee : (envAt t i).loc feeCol = 1006632961) : False := by
  have h :=
    (wideFee_availability_and_exact_move_forced hash hside hsat i hi hnotlast hcanon hdir).2.1
  rw [hbefore, hamount, hfee] at h; omega

/-- **THE AMOUNT-LEG FORGERY IS UNSAT ON THE WIDE MEMBER** (the §11.7 audit witness, against the
wide fee'd member). -/
theorem wideFee_amount_forgery_unsat (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferFeeAvailWide minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921)
    (hdir : (envAt t i).loc (prmCol param.DIRECTION) = 1)
    (hbefore : (envAt t i).loc (sbCol state.BALANCE_LO) = 1)
    (hamount : (envAt t i).loc (prmCol param.AMOUNT) = 1006632961) : False := by
  have h :=
    (wideFee_availability_and_exact_move_forced hash hside hsat i hi hnotlast hcanon hdir).1
  rw [hbefore, hamount] at h; omega

/-- The fee-leg forgery is UNSAT on the WELDED wide fee member too. -/
theorem weldedFee_fee_forgery_unsat (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash weldedTransferFeeAvailWide minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921)
    (hdir : (envAt t i).loc (prmCol param.DIRECTION) = 1)
    (hbefore : (envAt t i).loc (sbCol state.BALANCE_LO) = 1)
    (hamount : (envAt t i).loc (prmCol param.AMOUNT) = 0)
    (hfee : (envAt t i).loc feeCol = 1006632961) : False :=
  wideFee_fee_forgery_unsat hash hside (satisfied2_of_weldedTransferFeeAvailWide hash hsat)
    i hi hnotlast hcanon hdir hbefore hamount hfee

/-- The amount-leg forgery is UNSAT on the WELDED wide fee member too. -/
theorem weldedFee_amount_forgery_unsat (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash weldedTransferFeeAvailWide minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921)
    (hdir : (envAt t i).loc (prmCol param.DIRECTION) = 1)
    (hbefore : (envAt t i).loc (sbCol state.BALANCE_LO) = 1)
    (hamount : (envAt t i).loc (prmCol param.AMOUNT) = 1006632961) : False :=
  wideFee_amount_forgery_unsat hash hside (satisfied2_of_weldedTransferFeeAvailWide hash hsat)
    i hi hnotlast hcanon hdir hbefore hamount

/-! ## §4 — Axiom-hygiene tripwires. -/

#assert_axioms satisfied2_of_weldedTransferFeeAvailWide
#assert_axioms wideFeeAvail_row_v1
#assert_axioms weldedFeeAvail_row_v1
#assert_axioms wideFee_availability_and_exact_move_forced
#assert_axioms wideFee_availability_and_exact_move_forced_welded
#assert_axioms wideFee_credit_exact_forced_welded
#assert_axioms wideFee_fee_forgery_unsat
#assert_axioms wideFee_amount_forgery_unsat
#assert_axioms weldedFee_fee_forgery_unsat
#assert_axioms weldedFee_amount_forgery_unsat

end Dregg2.Circuit.RotatedKernelRefinementFeeAvailWide
