/-
# Dregg2.Circuit.RotatedKernelRefinementFeeAvail — the FEE'D-transfer availability wrap-forgery,
closed on the hardened graduable-wide FEE path (the fee member of the GAP #4 full-closure).

## What this module is

The deployed fee'd transfer (`transferFeeVmDescriptor2R24 = withDfaRcPins transferFeeV3`) debits
BOTH the transfer amount AND the published fee from `BALANCE_LO` (`gBalLoFee`) with NO availability
check — the same underflow-wrap class `RotatedKernelRefinementAvail` closes for the bare transfer,
open here through EITHER debit leg (amount OR fee: `before=1, amount=0, fee=1006632961` wraps and
passes the bare 30-bit ranges). Unlike the bare transfer, the fee route carries NO
`guardAvail`-style decode residual anywhere in the refinement tower — the wrap was simply
unwitnessed. So the closure IS the hardened descriptor + the emission retarget, and THIS module is
its rotated-path discharge:

  * **`transferFeeV3Avail`** — the hardened fee-pinned rotated graduated descriptor
    (`v3OfFrozenFeeWide transferFeeVmDescriptorAvail`), the wide mirror of `transferFeeV3`.
  * **`rotatedFeeAvail_row_v1`** — a `Satisfied2` witness of the hardened member (or of the wire
    member `AvailWireMembers.transferFeeV3AvailWire`, via the rc peel) yields the per-row v1
    denotation of the §11.8 fee availability face.
  * **`feeAvailability_and_exact_move_forced`** — THE DISCHARGE: on the designated debit row,
    `amount ≤ before`, `amount + fee ≤ before` (availability INCLUDING the fee) AND the exact ℤ
    move `after = before − amount − fee` are FORCED. No `hcanonMove`; the only envelope is the
    deployed canonicality invariant (width-only — NOT availability laundered in).
  * **`feeWire_fee_forgery_unsat` / `feeWire_amount_forgery_unsat`** — THE TEETH: both wrap-forgery
    witnesses are UNSAT against the hardened WIRE member.

## What this module is NOT (the remaining deployment step, EMBER-GATED)

The live registry still routes the bare `withDfaRcPins transferFeeV3`; the flip
(`EmitRotationV3.lean` override → `rotation-v3-staged-registry.tsv` regen → VK) is the ONE
big-bang regen, deliberately not done here.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem.
-/
import Dregg2.Circuit.RotatedKernelRefinementAvail
import Dregg2.Circuit.Emit.AvailWireMembers

namespace Dregg2.Circuit.RotatedKernelRefinementFeeAvail

open Dregg2.Circuit.Emit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitV2
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
open Dregg2.Circuit.Emit.AvailWireMembers
open Dregg2.Circuit.RotatedKernelRefinementAvail

set_option autoImplicit false

/-! ## §0 — the hardened fee-pinned rotated descriptor. -/

/-- The HARDENED fee'd rotated graduated transfer descriptor: the §11.8 fee availability weld
lifted through the V3 rotation + authority freeze + FEE PIN, graduated MULTI-WIDTH. The wide
mirror of `transferFeeV3` (and the body of the wire member `transferFeeV3AvailWire`). -/
def transferFeeV3Avail : EffectVmDescriptor2 :=
  v3OfFrozenFeeWide EffectVmEmitTransfer.transferFeeVmDescriptorAvail

/-- The hardened fee face is wide-graduable (its 15-bit MID/FEE-limb teeth are exactly why the
single-width `graduable` refuses it). -/
theorem transferFeeAvail_graduableWide :
    graduableWide EffectVmEmitTransfer.transferFeeVmDescriptorAvail = true := by decide

-- The wire member IS the rc-pinned hardened face (definitional identity of the two compositions).
#guard transferFeeV3AvailWire.constraints.length == transferFeeV3Avail.constraints.length + 4

/-! ## §1 — the per-row v1 denotation from a satisfying witness. -/

/-- **The hardened fee per-row v1 denotation** — a `Satisfied2` witness of `transferFeeV3Avail`
yields, on every row, the FULL v1 denotation of the §11.8 fee availability face (weld gates +
15-bit teeth included). -/
theorem rotatedFeeAvail_row_v1 (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferFeeV3Avail minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    satisfiedVm hash EffectVmEmitTransfer.transferFeeVmDescriptorAvail
      (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
  rotV3FrozenFeeWide_sound_v1 permOut hash EffectVmEmitTransfer.transferFeeVmDescriptorAvail
    minit mfin maddrs t transferFeeAvail_graduableWide (hside.toFaithfulW hsat) i hi

/-- The same, from a satisfying WIRE-member witness (through the rc peel) — the deployment-real
entry: `Satisfied2 (transferFeeV3AvailWire) ⟹` the per-row §11.8 denotation. -/
theorem rotatedFeeAvailWire_row_v1 (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferFeeV3AvailWire minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    satisfiedVm hash EffectVmEmitTransfer.transferFeeVmDescriptorAvail
      (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
  rotatedFeeAvail_row_v1 hash hside (satisfied2_of_transferFeeV3AvailWire hash hsat) i hi

/-! ## §2 — THE DISCHARGE: fee'd availability + the exact ℤ move are FORCED. -/

/-- **`feeAvailability_and_exact_move_forced` — the fee wrap-forgery closed.** A `Satisfied2`
witness of the hardened WIRE member forces, on any designated ACTIVE debit row (`direction = 1`,
not the wrap/pad last row) under the deployed canonicality envelope:
`amount ≤ before.bal_lo`, `amount + fee ≤ before.bal_lo` (availability INCLUDING the fee — both
debit legs), AND the exact ℤ move `after = before − amount − fee` (no wrap witness exists through
EITHER leg). -/
theorem feeAvailability_and_exact_move_forced (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferFeeV3AvailWire minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921)
    (hdir : (envAt t i).loc (prmCol param.DIRECTION) = 1) :
    (envAt t i).loc (prmCol param.AMOUNT) ≤ (envAt t i).loc (sbCol state.BALANCE_LO)
    ∧ (envAt t i).loc (prmCol param.AMOUNT) + (envAt t i).loc EffectVmEmitTransfer.feeCol
        ≤ (envAt t i).loc (sbCol state.BALANCE_LO)
    ∧ (envAt t i).loc (saCol state.BALANCE_LO)
        = (envAt t i).loc (sbCol state.BALANCE_LO) - (envAt t i).loc (prmCol param.AMOUNT)
          - (envAt t i).loc EffectVmEmitTransfer.feeCol := by
  have hv1 := rotatedFeeAvailWire_row_v1 hash hside hsat i hi
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  rw [hlastf] at hv1
  exact EffectVmEmitTransfer.transferFeeAvail_derives_availability_row hash (envAt t i) (i == 0)
    hcanon hv1 hdir

/-- The CREDIT-side exactness on the wire (the credit twin): `after = before + amount − fee` over
ℤ, no overflow wrap through the credit leg, no underflow wrap through the fee leg. -/
theorem feeCredit_exact_forced (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferFeeV3AvailWire minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921)
    (hdir : (envAt t i).loc (prmCol param.DIRECTION) = 0) :
    (envAt t i).loc EffectVmEmitTransfer.feeCol
        ≤ (envAt t i).loc (sbCol state.BALANCE_LO) + (envAt t i).loc (prmCol param.AMOUNT)
    ∧ (envAt t i).loc (saCol state.BALANCE_LO)
        = (envAt t i).loc (sbCol state.BALANCE_LO) + (envAt t i).loc (prmCol param.AMOUNT)
          - (envAt t i).loc EffectVmEmitTransfer.feeCol := by
  have hv1 := rotatedFeeAvailWire_row_v1 hash hside hsat i hi
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  rw [hlastf] at hv1
  exact EffectVmEmitTransfer.transferFeeAvail_credit_exact hash (envAt t i) (i == 0)
    hcanon hv1 hdir

/-! ## §3 — THE TEETH: both wrap-forgery witnesses are UNSAT on the hardened wire. -/

/-- **THE FEE-LEG FORGERY IS UNSAT ON THE WIRE.** The fee wrap witness (`before=1, amount=0,
fee=1006632961, direction=1` — the fee member of the GAP #4 forgery family, which the DEPLOYED
bare fee member ADMITS) cannot ride any satisfying witness of the hardened wire member. -/
theorem feeWire_fee_forgery_unsat (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferFeeV3AvailWire minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921)
    (hdir : (envAt t i).loc (prmCol param.DIRECTION) = 1)
    (hbefore : (envAt t i).loc (sbCol state.BALANCE_LO) = 1)
    (hamount : (envAt t i).loc (prmCol param.AMOUNT) = 0)
    (hfee : (envAt t i).loc EffectVmEmitTransfer.feeCol = 1006632961) : False := by
  have h := (feeAvailability_and_exact_move_forced hash hside hsat i hi hnotlast hcanon hdir).2.1
  rw [hbefore, hamount, hfee] at h; omega

/-- **THE AMOUNT-LEG FORGERY IS UNSAT ON THE WIRE** (the §11.7 audit witness, against the fee'd
member). -/
theorem feeWire_amount_forgery_unsat (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferFeeV3AvailWire minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921)
    (hdir : (envAt t i).loc (prmCol param.DIRECTION) = 1)
    (hbefore : (envAt t i).loc (sbCol state.BALANCE_LO) = 1)
    (hamount : (envAt t i).loc (prmCol param.AMOUNT) = 1006632961) : False := by
  have h := (feeAvailability_and_exact_move_forced hash hside hsat i hi hnotlast hcanon hdir).1
  rw [hbefore, hamount] at h; omega

/-! ## §4 — Axiom-hygiene tripwires. -/

#assert_axioms transferFeeAvail_graduableWide
#assert_axioms rotatedFeeAvail_row_v1
#assert_axioms rotatedFeeAvailWire_row_v1
#assert_axioms feeAvailability_and_exact_move_forced
#assert_axioms feeCredit_exact_forced
#assert_axioms feeWire_fee_forgery_unsat
#assert_axioms feeWire_amount_forgery_unsat

end Dregg2.Circuit.RotatedKernelRefinementFeeAvail
