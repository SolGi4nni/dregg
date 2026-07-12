/-
# Dregg2.Circuit.RotatedKernelRefinementAvailWide — transfer availability DISCHARGED on the WIDE
+ WELDED registry members (the wide-transfer availability wrap-forgery, closed in-proof).

## What this module is

`RotatedKernelRefinementAvail` discharged `guardAvail` on the NARROW hardened rotated transfer
(`transferV3Avail`). The DEPLOYED light client, however, resolves the WIDE registry
(`WIDE_REGISTRY_STAGED_TSV`) and its umem-welded twin — whose transfer members were built over
the BARE face, so the underflow-wrap mint-from-nothing stayed open on the wide leg. With the
emission retarget (`AvailWideMembers` + `EffectVmEmitUMemWeldWide`), this module carries the
availability discharge to the EXACT post-retarget wire objects:

  * **`weldedTransferAvailWide`** — the umem-welded, capacity-floor-refused crown transfer
    (the welded-registry row for `transferVmDescriptor2R24`);
  * **`transferAvailWideRefused`** — the bare-wide crown row (refuse, no umem weld);
  * **`weldedTransferCapOpenTBAvailWide`** / **`transferCapOpenTBAvailWide`** — the TB
    cap-open transfer twins (`transferCapOpenTBVmDescriptor2R24`).

The chain: welded accept → (`satisfied2_of_weldUMemIntoWide`, the weld appends ONE row-locally
trivial `umemOp` and nothing else) refused accept → (`satisfied2_of_gentianDeployedBareRefuseAt`)
the crown avail wide member → (`AvailWideMembers.membershipAvailWide_row_v1`, the
membership-parametric wide collapse over the legacy-pin-filtered embed) the hardened face's
per-row `satisfiedVm` → (`transferAvail_derives_availability_row`, at the row's own flags) the
borrow-forced order + EXACT ℤ move → (the decode's ledger ties) the kernel statement:

    `tr.amt ≤ pre.kernel.bal tr.src a  ∧  post.kernel.bal tr.src a = pre.bal src a − tr.amt`.

The decode is `RotatedKernelRefinementAvail.rotatedEncodesAvail` UNCHANGED — it is
descriptor-independent (rows/ledger ties only), so the wide discharge consumes the same object
with NO `guardAvail` anywhere. `transfer_descriptorRefinesAvail_weldedWide` assembles the full
`BalanceMovementSpec` refinement on the welded wide path; the teeth close the audit forgery class
(`pre.bal = 0, amt = 10⁹` UNSAT) on every member.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. NEW file; imports
are read-only.
-/
import Dregg2.Circuit.RotatedKernelRefinementAvail
import Dregg2.Circuit.Emit.EffectVmEmitUMemWeldWide

namespace Dregg2.Circuit.RotatedKernelRefinementAvailWide

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitV2 (Satisfied2FaithfulWide)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
open Dregg2.Circuit.Emit.AvailWideMembers
  (transferV3MembershipAvailWide transferAvailWideRefused transferCapOpenTBAvailWide
   membershipAvailWide_row_v1 tbAvailWide_row_v1)
open Dregg2.Circuit.Emit.AvailWireMembers
  (satisfied2_of_gentianDeployedBareRefuseAt cavBaseOf)
open Dregg2.Circuit.Emit.EffectVmEmitUMemWeldWide
  (weldedTransferAvailWide weldedTransferCapOpenTBAvailWide satisfied2_of_weldUMemIntoWide)
open Dregg2.Circuit.Spec.BalanceMovement
open Dregg2.Circuit.RotatedKernelRefinementAvail (RotTableSideW rotatedEncodesAvail)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false

/-! ## §1 — the peels: a welded-registry witness reaches the crown avail wide member. -/

/-- `Satisfied2` of the WELDED crown row peels to the crown avail wide member (umem weld off,
then the capacity-floor refuse off — both append-only). -/
theorem satisfied2_of_weldedTransferAvailWide (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash weldedTransferAvailWide minit mfin maddrs t) :
    Satisfied2 hash transferV3MembershipAvailWide minit mfin maddrs t :=
  satisfied2_of_gentianDeployedBareRefuseAt hash (cavBaseOf AVAIL_WIDTH)
    transferV3MembershipAvailWide
    (satisfied2_of_weldUMemIntoWide hash transferAvailWideRefused _ h)

/-! ## §2 — the per-row v1 collapses on the WIRE objects. -/

/-- A welded-crown witness forces the hardened face's FULL v1 denotation on every row. -/
theorem weldedAvailWide_row_v1 (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash weldedTransferAvailWide minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    satisfiedVm hash transferVmDescriptorAvail
      (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
  membershipAvailWide_row_v1 permOut hash minit mfin maddrs t
    (hside.toFaithfulW (satisfied2_of_weldedTransferAvailWide hash hsat)) i hi

/-- A bare-wide crown (refused, unwelded) witness forces the same v1 denotation. -/
theorem refusedAvailWide_row_v1 (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferAvailWideRefused minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    satisfiedVm hash transferVmDescriptorAvail
      (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
  membershipAvailWide_row_v1 permOut hash minit mfin maddrs t
    (hside.toFaithfulW (satisfied2_of_gentianDeployedBareRefuseAt hash (cavBaseOf AVAIL_WIDTH)
      transferV3MembershipAvailWide hsat)) i hi

/-- A welded-TB witness forces the same v1 denotation (umem weld off; no refuse on the TB key). -/
theorem weldedTBAvailWide_row_v1 (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash weldedTransferCapOpenTBAvailWide minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    satisfiedVm hash transferVmDescriptorAvail
      (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
  tbAvailWide_row_v1 permOut hash minit mfin maddrs t
    (hside.toFaithfulW (satisfied2_of_weldUMemIntoWide hash transferCapOpenTBAvailWide _ hsat))
    i hi

/-! ## §3 — THE WIDE DISCHARGE: availability + the EXACT ℤ debit, forced by a WELDED-registry
witness. The decode is the narrow `rotatedEncodesAvail` verbatim (descriptor-independent). -/

/-- **`availability_and_exact_move_forced_weldedWide`** — the umem-WELDED, refuse-carrying crown
transfer row (the exact welded-registry wire object) FORCES `tr.amt ≤ pre.bal src a` AND the
EXACT ℤ debit. The wide-transfer wrap forgery (audit forgery 1) is closed on the welded leg. -/
theorem availability_and_exact_move_forced_weldedWide (hash : List ℤ → ℤ)
    {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash weldedTransferAvailWide minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a) :
    tr.amt ≤ pre.kernel.bal tr.src a
    ∧ post.kernel.bal tr.src a = pre.kernel.bal tr.src a - tr.amt := by
  have hv1 := weldedAvailWide_row_v1 hash hside hsat henc.di henc.hdi
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

/-- Availability alone, on the welded crown row. -/
theorem availability_forced_weldedWide (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash weldedTransferAvailWide minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a) :
    tr.amt ≤ pre.kernel.bal tr.src a :=
  (availability_and_exact_move_forced_weldedWide hash hside hsat pre post tr a henc).1

/-- The same discharge on the WELDED TB cap-open transfer row. -/
theorem availability_and_exact_move_forced_weldedTB (hash : List ℤ → ℤ)
    {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash weldedTransferCapOpenTBAvailWide minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a) :
    tr.amt ≤ pre.kernel.bal tr.src a
    ∧ post.kernel.bal tr.src a = pre.kernel.bal tr.src a - tr.amt := by
  have hv1 := weldedTBAvailWide_row_v1 hash hside hsat henc.di henc.hdi
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

/-- The same discharge on the BARE-WIDE crown row (refused, unwelded — the
`WIDE_REGISTRY_STAGED_TSV` object). -/
theorem availability_and_exact_move_forced_refusedWide (hash : List ℤ → ℤ)
    {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferAvailWideRefused minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a) :
    tr.amt ≤ pre.kernel.bal tr.src a
    ∧ post.kernel.bal tr.src a = pre.kernel.bal tr.src a - tr.amt := by
  have hv1 := refusedAvailWide_row_v1 hash hside hsat henc.di henc.hdi
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

/-! ## §4 — the full refinement on the welded wide path (no `guardAvail` residual anywhere). -/

/-- **`transfer_descriptorRefinesAvail_weldedWide`** — satisfying the WELDED wide crown transfer
together with the hardened decode forces the KERNEL's balance-movement step, with availability
sourced FROM THE WITNESS. The wide mirror of
`RotatedKernelRefinementAvail.transfer_descriptorRefinesAvail`. -/
theorem transfer_descriptorRefinesAvail_weldedWide (hash : List ℤ → ℤ)
    {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash weldedTransferAvailWide minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a) :
    BalanceMovementSpec pre tr a post := by
  have havail := availability_forced_weldedWide hash hside hsat pre post tr a henc
  exact ⟨⟨henc.guardAuth, henc.guardNonNeg, havail,
      henc.guardDistinct, henc.guardLiveSrc, henc.guardLiveDst,
      henc.guardSrcLifecycleLive, henc.guardAccepts⟩,
    henc.hledgerFrame, henc.logAdv,
    henc.frAccounts, henc.frCell, henc.frCaps, henc.frNullifiers, henc.frRevoked,
    henc.frCommitments, henc.frSlotCaveats, henc.frFactories, henc.frLifecycle,
    henc.frDeathCert, henc.frDelegate, henc.frDelegations, henc.frDelegationEpoch,
    henc.frDelegationEpochAt, henc.frHeaps, henc.frNullifierRoot, henc.frRevokedRoot,
    henc.frCommitmentsRoot⟩

/-! ## §5 — THE TEETH: the audit forgery class is UNSAT on every retargeted wide member. -/

/-- ANY over-debit decode riding a satisfying WELDED crown witness is UNSAT. -/
theorem weldedWide_rejects_overdebit (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash weldedTransferAvailWide minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a)
    (hforge : pre.kernel.bal tr.src a < tr.amt) : False := by
  have h := availability_forced_weldedWide hash hside hsat pre post tr a henc
  omega

/-- The audit's CONCRETE forgery witness (`pre.bal src a = 0`, `tr.amt = 10⁹` — forgery 1 of
`docs/FINDING-modp-wrap-forgery-audit.md`) is UNSAT on the welded wide crown. -/
theorem weldedWide_audit_forgery_unsat (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash weldedTransferAvailWide minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a)
    (hbal : pre.kernel.bal tr.src a = 0) (hamt : tr.amt = 1000000000) : False := by
  refine weldedWide_rejects_overdebit hash hside hsat pre post tr a henc ?_
  omega

/-- The over-debit is UNSAT on the welded TB cap-open member too. -/
theorem weldedTB_rejects_overdebit (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash weldedTransferCapOpenTBAvailWide minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a)
    (hforge : pre.kernel.bal tr.src a < tr.amt) : False := by
  have h := (availability_and_exact_move_forced_weldedTB hash hside hsat pre post tr a henc).1
  omega

/-- The over-debit is UNSAT on the bare-wide (refused, unwelded) crown row. -/
theorem refusedWide_rejects_overdebit (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferAvailWideRefused minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a)
    (hforge : pre.kernel.bal tr.src a < tr.amt) : False := by
  have h := (availability_and_exact_move_forced_refusedWide hash hside hsat pre post tr a
    henc).1
  omega

/-! ## §6 — Axiom-hygiene tripwires. -/

#assert_axioms satisfied2_of_weldedTransferAvailWide
#assert_axioms weldedAvailWide_row_v1
#assert_axioms refusedAvailWide_row_v1
#assert_axioms weldedTBAvailWide_row_v1
#assert_axioms availability_and_exact_move_forced_weldedWide
#assert_axioms availability_forced_weldedWide
#assert_axioms availability_and_exact_move_forced_weldedTB
#assert_axioms availability_and_exact_move_forced_refusedWide
#assert_axioms transfer_descriptorRefinesAvail_weldedWide
#assert_axioms weldedWide_rejects_overdebit
#assert_axioms weldedWide_audit_forgery_unsat
#assert_axioms weldedTB_rejects_overdebit
#assert_axioms refusedWide_rejects_overdebit

end Dregg2.Circuit.RotatedKernelRefinementAvailWide
