/-
# Dregg2.Circuit.RotatedKernelRefinementAvailWideNarrow — the availability refinement discharged on
the NARROW-BASE (tuple-narrowing) crown members, riding the `RotTableSideNarrow` witness bus.

## What this module is

The deployed WIDE availability tower (`RotatedKernelRefinement{AvailWide,CapOpenAvailWide,
FeeAvailWide,MintBurnAvailWide}`) collapses each retargeted crown wire object to the hardened face's
per-row `satisfiedVm` through a `Satisfied2FaithfulWide` witness (the 25-wide Poseidon2 chip bus, 7
witnessed lane columns per single-output hash site) built from `RotTableSideW.toFaithfulW`. This
module carries the SAME availability discharge + teeth over the NARROW-base crown members
(`AvailWideMembersNarrow` — single-output sites on the 18-wide narrow bus, NO lane columns), riding
the new `RotTableSideNarrow.toFaithfulWNarrow` witness provider and the already-proven narrow
per-row collapses (`membershipAvailWideNarrow_row_v1` / `tbAvailWideNarrow_row_v1` /
`burnAvailWideNarrow_row_v1` / `effAvailWideNarrow_row_v1` / `feeAvailWideNarrow_row_v1`).

The decode objects (`rotatedEncodesAvail` / `rotatedEncodesBurnAvail`) and the row-level derivation
lemmas (`transferAvail_derives_availability_row` / `burnAvail_derives_availability_row` /
`transferFeeAvail_derives_availability_row` / `transferFeeAvail_credit_exact`) are consumed VERBATIM
— they are descriptor-independent (rows/ledger ties only), so every conclusion here is byte-identical
to its deployed wide twin, only the input descriptor is the narrow-base crown member and the witness
side is `RotTableSideNarrow`. The availability / over-debit / over-burn / fee-leg / audit-forgery teeth
are preserved (below). ⚠ NOT-YET-TWINNED residual: the EFF facet-selector tooth
`wideCapOpenEffAvail_rejects_wrong_facet` (clear `EFF_TRANSFER` mask ⟹ ¬Satisfied2) has NO narrow twin
here — it depends on the narrow face's column layout, so it is an honest TODO (`effNarrow_rejects_wrong_facet`),
NOT preserved by the derives-availability keystone. The teeth that ARE reproduced byte-identical:

    transfer/TB/EFF:  `tr.amt ≤ pre.bal src a ∧ post.bal src a = pre.bal src a − tr.amt`;
                      any over-debit / the audit forgery (`pre.bal=0, amt=10⁹`) is UNSAT.
    burn:             `amt ≤ pre.bal cell a ∧ post.bal cell a = pre.bal cell a − amt`;
                      any over-burn / the audit forgery (`pre.bal=1, amt=10⁹`) is UNSAT.
    fee:              `amt ≤ before ∧ amt+fee ≤ before ∧ after = before − amt − fee`;
                      the fee-leg and amount-leg wrap forgeries are UNSAT.

## Scope (honest)

These twins are stated over the narrow CROWN members (the plain membership / TB / EFF / fee / burn
faces). The deployed WIRE objects that carry the umem weld / capacity-floor refuse
(`weldedTransferAvailWide` / `transferAvailWideRefused` / `weldedTransferCapOpenTBAvailWide` /
`weldedTransferCapOpenEffAvailWide` / `weldedBurnAvailWide` / `burnAvailWideRefused` /
`weldedTransferFeeAvailWide`) still ride the 25-wide bus: their narrow twins are new
descriptors (umem-weld / refuse wrappers over the narrow crown members), which is the remaining
Rust-producer + VK-regen step, deliberately NOT built here. This module is the proof that the
crown-member availability tower rides the narrow bus once that regen lands.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. NEW file; imports are
read-only.
-/
import Dregg2.Circuit.RotatedKernelRefinementAvailWide
import Dregg2.Circuit.RotatedKernelRefinementCapOpenAvailWide
import Dregg2.Circuit.RotatedKernelRefinementFeeAvailWide
import Dregg2.Circuit.RotatedKernelRefinementMintBurnAvailWide
import Dregg2.Circuit.Emit.AvailWideMembersNarrow

namespace Dregg2.Circuit.RotatedKernelRefinementAvailWideNarrow

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitV2 (Satisfied2FaithfulWideNarrow)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
open Dregg2.Circuit.Emit.AvailWideMembersNarrow
  (transferV3MembershipAvailWideNarrow transferCapOpenTBAvailWideNarrow burnV3AvailWideNarrow
   transferCapOpenEffAvailWideNarrow transferFeeAvailWideNarrow
   membershipAvailWideNarrow_row_v1 tbAvailWideNarrow_row_v1 burnAvailWideNarrow_row_v1
   effAvailWideNarrow_row_v1 feeAvailWideNarrow_row_v1)
open Dregg2.Circuit.Spec.BalanceMovement
open Dregg2.Circuit.RotatedKernelRefinementAvail (RotTableSideNarrow rotatedEncodesAvail)
open Dregg2.Circuit.RotatedKernelRefinementMintBurnAvail (rotatedEncodesBurnAvail)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false

/-! ## §1 — TRANSFER (membership crown): availability + the EXACT ℤ debit + teeth on the narrow bus.
The narrow twin of `RotatedKernelRefinementAvailWide`'s membership-crown discharge. -/

/-- A narrow-base membership-crown witness forces the hardened face's FULL v1 denotation on every row
(the narrow twin of `weldedAvailWide_row_v1` / `refusedAvailWide_row_v1`, via
`RotTableSideNarrow.toFaithfulWNarrow` + the narrow collapse). -/
theorem membershipNarrow_row_v1 (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideNarrow hash t)
    (hsat : Satisfied2 hash transferV3MembershipAvailWideNarrow minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    satisfiedVm hash transferVmDescriptorAvail
      (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
  membershipAvailWideNarrow_row_v1 hash minit mfin maddrs t (hside.toFaithfulWNarrow hsat) i hi

/-- **`membershipNarrow_availability_and_exact_move_forced`** — a `Satisfied2` witness of the
narrow-base membership crown transfer + the hardened decode FORCE `tr.amt ≤ pre.bal src a` AND the
EXACT ℤ debit. Conclusion byte-identical to `availability_and_exact_move_forced_weldedWide`. -/
theorem membershipNarrow_availability_and_exact_move_forced (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideNarrow hash t)
    (hsat : Satisfied2 hash transferV3MembershipAvailWideNarrow minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a) :
    tr.amt ≤ pre.kernel.bal tr.src a
    ∧ post.kernel.bal tr.src a = pre.kernel.bal tr.src a - tr.amt := by
  have hv1 := membershipNarrow_row_v1 hash hside hsat henc.di henc.hdi
  have hlastf : (henc.di + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact henc.hdiNotLast
  rw [hlastf] at hv1
  obtain ⟨hbLo, _, _, _, _, _, _, hAmt, hDir, hsaLo, _⟩ := henc.hdiEnc
  have hdir1 : (envAt t henc.di).loc (prmCol param.DIRECTION) = 1 := by
    rw [hDir, henc.hdiDir]
  have h := transferAvail_derives_availability_row hash (envAt t henc.di) (henc.di == 0)
    henc.hdiCanon hv1 hdir1
  rw [hAmt, henc.hdiAmt, hbLo, henc.hsrcPre, hsaLo, henc.hsrcPost] at h
  exact h

/-- Availability alone, on the narrow membership crown. -/
theorem membershipNarrow_availability_forced (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideNarrow hash t)
    (hsat : Satisfied2 hash transferV3MembershipAvailWideNarrow minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a) :
    tr.amt ≤ pre.kernel.bal tr.src a :=
  (membershipNarrow_availability_and_exact_move_forced hash hside hsat pre post tr a henc).1

/-- **`transfer_descriptorRefinesNarrow`** — satisfying the narrow membership crown transfer together
with the hardened decode forces the KERNEL's `BalanceMovementSpec`, availability sourced FROM THE
WITNESS. The narrow twin of `transfer_descriptorRefinesAvail_weldedWide`. -/
theorem transfer_descriptorRefinesNarrow (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideNarrow hash t)
    (hsat : Satisfied2 hash transferV3MembershipAvailWideNarrow minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a) :
    BalanceMovementSpec pre tr a post := by
  have havail := membershipNarrow_availability_forced hash hside hsat pre post tr a henc
  exact ⟨⟨henc.guardAuth, henc.guardNonNeg, havail,
      henc.guardDistinct, henc.guardLiveSrc, henc.guardLiveDst,
      henc.guardSrcLifecycleLive, henc.guardAccepts⟩,
    henc.hledgerFrame, henc.logAdv,
    henc.frAccounts, henc.frCell, henc.frCaps, henc.frNullifiers, henc.frRevoked,
    henc.frCommitments, henc.frSlotCaveats, henc.frFactories, henc.frLifecycle,
    henc.frDeathCert, henc.frDelegate, henc.frDelegations, henc.frDelegationEpoch,
    henc.frDelegationEpochAt, henc.frHeaps, henc.frNullifierRoot, henc.frRevokedRoot,
    henc.frCommitmentsRoot⟩

/-- ANY over-debit decode riding a satisfying narrow membership crown witness is UNSAT. -/
theorem membershipNarrow_rejects_overdebit (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideNarrow hash t)
    (hsat : Satisfied2 hash transferV3MembershipAvailWideNarrow minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a)
    (hforge : pre.kernel.bal tr.src a < tr.amt) : False := by
  have h := membershipNarrow_availability_forced hash hside hsat pre post tr a henc
  omega

/-- The audit's CONCRETE forgery witness (`pre.bal src a = 0`, `tr.amt = 10⁹`) is UNSAT on the narrow
membership crown. -/
theorem membershipNarrow_audit_forgery_unsat (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideNarrow hash t)
    (hsat : Satisfied2 hash transferV3MembershipAvailWideNarrow minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a)
    (hbal : pre.kernel.bal tr.src a = 0) (hamt : tr.amt = 1000000000) : False := by
  refine membershipNarrow_rejects_overdebit hash hside hsat pre post tr a henc ?_
  omega

/-! ## §2 — TRANSFER (TB cap-open crown): the narrow twin of `weldedTBAvailWide_row_v1`'s discharge. -/

/-- A narrow-base TB cap-open crown witness forces the hardened face's v1 denotation on every row. -/
theorem tbNarrow_row_v1 (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideNarrow hash t)
    (hsat : Satisfied2 hash transferCapOpenTBAvailWideNarrow minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    satisfiedVm hash transferVmDescriptorAvail
      (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
  tbAvailWideNarrow_row_v1 hash minit mfin maddrs t (hside.toFaithfulWNarrow hsat) i hi

/-- Availability + the EXACT ℤ debit on the narrow TB cap-open crown. -/
theorem tbNarrow_availability_and_exact_move_forced (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideNarrow hash t)
    (hsat : Satisfied2 hash transferCapOpenTBAvailWideNarrow minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a) :
    tr.amt ≤ pre.kernel.bal tr.src a
    ∧ post.kernel.bal tr.src a = pre.kernel.bal tr.src a - tr.amt := by
  have hv1 := tbNarrow_row_v1 hash hside hsat henc.di henc.hdi
  have hlastf : (henc.di + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact henc.hdiNotLast
  rw [hlastf] at hv1
  obtain ⟨hbLo, _, _, _, _, _, _, hAmt, hDir, hsaLo, _⟩ := henc.hdiEnc
  have hdir1 : (envAt t henc.di).loc (prmCol param.DIRECTION) = 1 := by
    rw [hDir, henc.hdiDir]
  have h := transferAvail_derives_availability_row hash (envAt t henc.di) (henc.di == 0)
    henc.hdiCanon hv1 hdir1
  rw [hAmt, henc.hdiAmt, hbLo, henc.hsrcPre, hsaLo, henc.hsrcPost] at h
  exact h

/-- ANY over-debit decode riding a satisfying narrow TB crown witness is UNSAT. -/
theorem tbNarrow_rejects_overdebit (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideNarrow hash t)
    (hsat : Satisfied2 hash transferCapOpenTBAvailWideNarrow minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a)
    (hforge : pre.kernel.bal tr.src a < tr.amt) : False := by
  have h := (tbNarrow_availability_and_exact_move_forced hash hside hsat pre post tr a henc).1
  omega

/-! ## §3 — TRANSFER (EFF cap-open crown): the narrow twin of the WIDE cap-open-EFF discharge
(`RotatedKernelRefinementCapOpenAvailWide`). -/

/-- A narrow-base EFF cap-open crown witness forces the hardened face's v1 denotation on every row. -/
theorem effNarrow_row_v1 (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideNarrow hash t)
    (hsat : Satisfied2 hash transferCapOpenEffAvailWideNarrow minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    satisfiedVm hash transferVmDescriptorAvail
      (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
  effAvailWideNarrow_row_v1 hash minit mfin maddrs t (hside.toFaithfulWNarrow hsat) i hi

/-- Availability + the EXACT ℤ debit on the narrow EFF cap-open crown (the narrow twin of
`wideCapOpenEff_availability_and_exact_move_forced`). -/
theorem effNarrow_availability_and_exact_move_forced (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideNarrow hash t)
    (hsat : Satisfied2 hash transferCapOpenEffAvailWideNarrow minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a) :
    tr.amt ≤ pre.kernel.bal tr.src a
    ∧ post.kernel.bal tr.src a = pre.kernel.bal tr.src a - tr.amt := by
  have hv1 := effNarrow_row_v1 hash hside hsat henc.di henc.hdi
  have hlastf : (henc.di + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact henc.hdiNotLast
  rw [hlastf] at hv1
  obtain ⟨hbLo, _, _, _, _, _, _, hAmt, hDir, hsaLo, _⟩ := henc.hdiEnc
  have hdir1 : (envAt t henc.di).loc (prmCol param.DIRECTION) = 1 := by
    rw [hDir, henc.hdiDir]
  have h := transferAvail_derives_availability_row hash (envAt t henc.di) (henc.di == 0)
    henc.hdiCanon hv1 hdir1
  rw [hAmt, henc.hdiAmt, hbLo, henc.hsrcPre, hsaLo, henc.hsrcPost] at h
  exact h

/-- ANY over-debit decode riding a satisfying narrow EFF cap-open crown witness is UNSAT: a
cap-AUTHORIZED narrow-bus transfer still cannot move more than the source holds. -/
theorem effNarrow_rejects_overdebit (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideNarrow hash t)
    (hsat : Satisfied2 hash transferCapOpenEffAvailWideNarrow minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a)
    (hforge : pre.kernel.bal tr.src a < tr.amt) : False := by
  have h := (effNarrow_availability_and_exact_move_forced hash hside hsat pre post tr a henc).1
  omega

/-- The audit's CONCRETE forgery witness (`pre.bal src a = 0`, `tr.amt = 10⁹`) is UNSAT on the narrow
EFF cap-open crown. -/
theorem effNarrow_audit_forgery_unsat (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideNarrow hash t)
    (hsat : Satisfied2 hash transferCapOpenEffAvailWideNarrow minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a)
    (hbal : pre.kernel.bal tr.src a = 0) (hamt : tr.amt = 1000000000) : False := by
  refine effNarrow_rejects_overdebit hash hside hsat pre post tr a henc ?_
  omega

/-! ## §4 — BURN (crown): the narrow twin of `RotatedKernelRefinementMintBurnAvailWide`'s discharge.
Burn is debit-only (NO direction premise); its ledger frame CREDITS the well, so the tooth closes the
STRICTLY-WORSE well-supply-inflation forgery (audit forgery 2). -/

/-- A narrow-base burn crown witness forces the hardened burn face's v1 denotation on every row. -/
theorem burnNarrow_row_v1 (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideNarrow hash t)
    (hsat : Satisfied2 hash burnV3AvailWideNarrow minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    satisfiedVm hash Dregg2.Circuit.Emit.EffectVmEmitBurn.burnVmDescriptorAvail
      (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
  burnAvailWideNarrow_row_v1 hash minit mfin maddrs t (hside.toFaithfulWNarrow hsat) i hi

/-- **`burnNarrow_availability_and_exact_move_forced`** — a `Satisfied2` witness of the narrow-base
burn crown + the hardened decode FORCE `amt ≤ pre.bal cell a` AND the EXACT ℤ debit. Conclusion
byte-identical to `wideBurn_availability_and_exact_move_forced`. -/
theorem burnNarrow_availability_and_exact_move_forced (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideNarrow hash t)
    (hsat : Satisfied2 hash burnV3AvailWideNarrow minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesBurnAvail hash minit mfin maddrs t pre post actor cell a amt) :
    amt ≤ pre.kernel.bal cell a
    ∧ post.kernel.bal cell a = pre.kernel.bal cell a - amt := by
  have hv1 := burnNarrow_row_v1 hash hside hsat henc.di henc.hdi
  have hlastf : (henc.di + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact henc.hdiNotLast
  rw [hlastf] at hv1
  obtain ⟨hbLo, _, _, _, _, _, _, hAmt, hsaLo, _⟩ := henc.hdiEnc
  have h := Dregg2.Circuit.Emit.EffectVmEmitBurn.burnAvail_derives_availability_row hash
    (envAt t henc.di) (henc.di == 0) henc.hdiCanon hv1
  rw [hAmt, hbLo, henc.hholderPre, hsaLo, henc.hholderPost] at h
  exact h

/-- Availability alone, on the narrow burn crown. -/
theorem burnNarrow_availability_forced (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideNarrow hash t)
    (hsat : Satisfied2 hash burnV3AvailWideNarrow minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesBurnAvail hash minit mfin maddrs t pre post actor cell a amt) :
    amt ≤ pre.kernel.bal cell a :=
  (burnNarrow_availability_and_exact_move_forced hash hside hsat pre post actor cell a amt henc).1

/-- **`burn_descriptorRefinesNarrow`** — satisfying the narrow burn crown together with the hardened
decode forces the KERNEL's `BurnSpec`, availability sourced FROM THE WITNESS. The narrow twin of
`burn_descriptorRefinesAvail_weldedWide`. -/
theorem burn_descriptorRefinesNarrow (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideNarrow hash t)
    (hsat : Satisfied2 hash burnV3AvailWideNarrow minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesBurnAvail hash minit mfin maddrs t pre post actor cell a amt) :
    Spec.SupplyDestruction.BurnSpec pre actor cell a amt post := by
  have havail := burnNarrow_availability_forced hash hside hsat pre post actor cell a amt henc
  exact ⟨⟨henc.guardAuth, henc.guardNonNeg, havail,
      henc.guardLiveCell, henc.guardLiveWell, henc.guardDistinct, henc.guardLifecycleLive⟩,
    henc.hledgerFrame, henc.logAdv,
    henc.frAccounts, henc.frCell, henc.frCaps, henc.frNullifiers, henc.frRevoked,
    henc.frCommitments, henc.frSlotCaveats, henc.frFactories, henc.frLifecycle,
    henc.frDeathCert, henc.frDelegate, henc.frDelegations, henc.frDelegationEpoch,
    henc.frDelegationEpochAt, henc.frHeaps, henc.frNullifierRoot, henc.frRevokedRoot,
    henc.frCommitmentsRoot⟩

/-- ANY over-burn decode riding a satisfying narrow burn crown witness is UNSAT. -/
theorem burnNarrow_rejects_overburn (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideNarrow hash t)
    (hsat : Satisfied2 hash burnV3AvailWideNarrow minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesBurnAvail hash minit mfin maddrs t pre post actor cell a amt)
    (hforge : pre.kernel.bal cell a < amt) : False := by
  have h := burnNarrow_availability_forced hash hside hsat pre post actor cell a amt henc
  omega

/-- The audit's CONCRETE forgery witness (`pre.bal cell a = 1`, `amt = 10⁹` — the well-supply-inflation
trace of forgery 2) is UNSAT on the narrow burn crown. -/
theorem burnNarrow_audit_forgery_unsat (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideNarrow hash t)
    (hsat : Satisfied2 hash burnV3AvailWideNarrow minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesBurnAvail hash minit mfin maddrs t pre post actor cell a amt)
    (hbal : pre.kernel.bal cell a = 1) (hamt : amt = 1000000000) : False := by
  refine burnNarrow_rejects_overburn hash hside hsat pre post actor cell a amt henc ?_
  omega

/-! ## §5 — FEE'D TRANSFER (crown): the narrow twin of `RotatedKernelRefinementFeeAvailWide`'s
discharge — availability INCLUDING the fee, both debit legs, plus the credit twin, on the narrow bus. -/

/-- A narrow-base fee crown witness forces the hardened fee face's v1 denotation on every row. -/
theorem feeNarrow_row_v1 (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideNarrow hash t)
    (hsat : Satisfied2 hash transferFeeAvailWideNarrow minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    satisfiedVm hash transferFeeVmDescriptorAvail
      (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
  feeAvailWideNarrow_row_v1 hash minit mfin maddrs t (hside.toFaithfulWNarrow hsat) i hi

/-- **`feeNarrow_availability_and_exact_move_forced`** — the narrow fee wrap-forgery closed: on any
designated ACTIVE debit row under the deployed canonicality envelope, `amount ≤ before`,
`amount + fee ≤ before` (availability INCLUDING the fee — both debit legs) AND the exact ℤ move
`after = before − amount − fee`. Byte-identical to `wideFee_availability_and_exact_move_forced`. -/
theorem feeNarrow_availability_and_exact_move_forced (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideNarrow hash t)
    (hsat : Satisfied2 hash transferFeeAvailWideNarrow minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921)
    (hdir : (envAt t i).loc (prmCol param.DIRECTION) = 1) :
    (envAt t i).loc (prmCol param.AMOUNT) ≤ (envAt t i).loc (sbCol state.BALANCE_LO)
    ∧ (envAt t i).loc (prmCol param.AMOUNT) + (envAt t i).loc feeCol
        ≤ (envAt t i).loc (sbCol state.BALANCE_LO)
    ∧ (envAt t i).loc (saCol state.BALANCE_LO)
        = (envAt t i).loc (sbCol state.BALANCE_LO) - (envAt t i).loc (prmCol param.AMOUNT)
          - (envAt t i).loc feeCol := by
  have hv1 := feeNarrow_row_v1 hash hside hsat i hi
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  rw [hlastf] at hv1
  exact transferFeeAvail_derives_availability_row hash (envAt t i) (i == 0) hcanon hv1 hdir

/-- The CREDIT-side exactness on the narrow fee crown: `after = before + amount − fee` over ℤ, no
overflow wrap through the credit leg, no underflow wrap through the fee leg. -/
theorem feeNarrow_credit_exact_forced (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideNarrow hash t)
    (hsat : Satisfied2 hash transferFeeAvailWideNarrow minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921)
    (hdir : (envAt t i).loc (prmCol param.DIRECTION) = 0) :
    (envAt t i).loc feeCol
        ≤ (envAt t i).loc (sbCol state.BALANCE_LO) + (envAt t i).loc (prmCol param.AMOUNT)
    ∧ (envAt t i).loc (saCol state.BALANCE_LO)
        = (envAt t i).loc (sbCol state.BALANCE_LO) + (envAt t i).loc (prmCol param.AMOUNT)
          - (envAt t i).loc feeCol := by
  have hv1 := feeNarrow_row_v1 hash hside hsat i hi
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  rw [hlastf] at hv1
  exact transferFeeAvail_credit_exact hash (envAt t i) (i == 0) hcanon hv1 hdir

/-- **THE FEE-LEG FORGERY IS UNSAT ON THE NARROW FEE CROWN** (`before=1, amount=0, fee=1006632961,
direction=1`). -/
theorem feeNarrow_fee_forgery_unsat (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideNarrow hash t)
    (hsat : Satisfied2 hash transferFeeAvailWideNarrow minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921)
    (hdir : (envAt t i).loc (prmCol param.DIRECTION) = 1)
    (hbefore : (envAt t i).loc (sbCol state.BALANCE_LO) = 1)
    (hamount : (envAt t i).loc (prmCol param.AMOUNT) = 0)
    (hfee : (envAt t i).loc feeCol = 1006632961) : False := by
  have h := (feeNarrow_availability_and_exact_move_forced hash hside hsat i hi hnotlast hcanon hdir).2.1
  rw [hbefore, hamount, hfee] at h; omega

/-- **THE AMOUNT-LEG FORGERY IS UNSAT ON THE NARROW FEE CROWN** (`before=1, amount=1006632961`). -/
theorem feeNarrow_amount_forgery_unsat (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideNarrow hash t)
    (hsat : Satisfied2 hash transferFeeAvailWideNarrow minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcanon : ∀ c, 0 ≤ (envAt t i).loc c ∧ (envAt t i).loc c < 2013265921)
    (hdir : (envAt t i).loc (prmCol param.DIRECTION) = 1)
    (hbefore : (envAt t i).loc (sbCol state.BALANCE_LO) = 1)
    (hamount : (envAt t i).loc (prmCol param.AMOUNT) = 1006632961) : False := by
  have h := (feeNarrow_availability_and_exact_move_forced hash hside hsat i hi hnotlast hcanon hdir).1
  rw [hbefore, hamount] at h; omega

/-! ## §6 — Axiom-hygiene tripwires. -/

#assert_axioms membershipNarrow_row_v1
#assert_axioms membershipNarrow_availability_and_exact_move_forced
#assert_axioms membershipNarrow_availability_forced
#assert_axioms transfer_descriptorRefinesNarrow
#assert_axioms membershipNarrow_rejects_overdebit
#assert_axioms membershipNarrow_audit_forgery_unsat
#assert_axioms tbNarrow_row_v1
#assert_axioms tbNarrow_availability_and_exact_move_forced
#assert_axioms tbNarrow_rejects_overdebit
#assert_axioms effNarrow_row_v1
#assert_axioms effNarrow_availability_and_exact_move_forced
#assert_axioms effNarrow_rejects_overdebit
#assert_axioms effNarrow_audit_forgery_unsat
#assert_axioms burnNarrow_row_v1
#assert_axioms burnNarrow_availability_and_exact_move_forced
#assert_axioms burnNarrow_availability_forced
#assert_axioms burn_descriptorRefinesNarrow
#assert_axioms burnNarrow_rejects_overburn
#assert_axioms burnNarrow_audit_forgery_unsat
#assert_axioms feeNarrow_row_v1
#assert_axioms feeNarrow_availability_and_exact_move_forced
#assert_axioms feeNarrow_credit_exact_forced
#assert_axioms feeNarrow_fee_forgery_unsat
#assert_axioms feeNarrow_amount_forgery_unsat

end Dregg2.Circuit.RotatedKernelRefinementAvailWideNarrow
