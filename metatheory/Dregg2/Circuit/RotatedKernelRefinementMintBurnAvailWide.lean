/-
# Dregg2.Circuit.RotatedKernelRefinementMintBurnAvailWide — burn availability DISCHARGED on the
WIDE + WELDED registry members (the wide-burn availability wrap-forgery, closed in-proof — the
LAST member of the wrap-class full-closure).

## What this module is

`RotatedKernelRefinementMintBurnAvail` discharged burn `guardAvail` on the NARROW hardened
rotated burn (`burnV3Avail`). The DEPLOYED light client, however, resolves the WIDE registry
(`WIDE_REGISTRY_STAGED_TSV`) and its umem-welded twin — whose burn member was built over the
BARE burn face, so the underflow-wrap WELL-SUPPLY-INFLATION mint-from-nothing
(`docs/FINDING-modp-wrap-forgery-audit.md`, forgery 2 — STRICTLY WORSE than the transfer twin:
burn's ledger frame CREDITS the well `(a,a)` by the forged amount) stayed open on the wide leg.
With the emission retarget (`AvailWideMembers` §7 + `EffectVmEmitUMemWeldWide`), this module
carries the availability discharge to the EXACT post-retarget wire objects:

  * **`weldedBurnAvailWide`** — the umem-welded, capacity-floor-refused crown burn
    (the welded-registry row for `burnVmDescriptor2R24`);
  * **`burnAvailWideRefused`** — the bare-wide crown row (refuse, no umem weld).

The chain: welded accept → (`satisfied2_of_weldUMemIntoWide`, the weld appends ONE row-locally
trivial `umemOp` and nothing else) refused accept → (`satisfied2_of_gentianDeployedBareRefuseAt`)
the crown burn avail wide member → (`AvailWideMembers.burnAvailWide_row_v1`, the
membership-parametric wide collapse over the legacy-pin-filtered embed) the hardened burn face's
per-row `satisfiedVm` → (`burnAvail_derives_availability_row`, at the row's own flags; burn is
debit-only, so NO direction premise) the borrow-forced order + EXACT ℤ debit → (the decode's
ledger ties) the kernel statement:

    `amt ≤ pre.kernel.bal cell a  ∧  post.kernel.bal cell a = pre.kernel.bal cell a − amt`.

The decode is `RotatedKernelRefinementMintBurnAvail.rotatedEncodesBurnAvail` UNCHANGED — it is
descriptor-independent (rows/ledger ties only), so the wide discharge consumes the same object
with NO `guardAvail` anywhere. `burn_descriptorRefinesAvail_weldedWide` assembles the full
`Spec.SupplyDestruction.BurnSpec` refinement on the welded wide path; the teeth close the audit
forgery class (`pre.bal cell a = 1, amt = 1006632961` UNSAT) on every member. With this, the
wrap class (bare transfer + burn `aa282f8c0`, cap-open, fee `3c79e6798`, wide transfer
`98c148699`, THIS = the wide burn) is closed member-for-member.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. NEW file; imports
are read-only.
-/
import Dregg2.Circuit.RotatedKernelRefinementMintBurnAvail
import Dregg2.Circuit.Emit.EffectVmEmitUMemWeldWide

namespace Dregg2.Circuit.RotatedKernelRefinementMintBurnAvailWide

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitV2 (Satisfied2FaithfulWide)
open Dregg2.Circuit.Emit.AvailWideMembers
  (burnV3AvailWide burnAvailWideRefused burnAvailWide_row_v1 BU_AVAIL_BB)
open Dregg2.Circuit.Emit.AvailWireMembers
  (satisfied2_of_gentianDeployedBareRefuseAt cavBaseOf)
open Dregg2.Circuit.Emit.EffectVmEmitUMemWeldWide
  (weldedBurnAvailWide satisfied2_of_weldUMemIntoWide)
open Dregg2.Circuit.RotatedKernelRefinementAvail (RotTableSideW)
open Dregg2.Circuit.RotatedKernelRefinementMintBurnAvail (rotatedEncodesBurnAvail)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false

/-! ## §1 — the peels: a welded-registry witness reaches the crown burn avail wide member. -/

/-- `Satisfied2` of the WELDED crown burn row peels to the crown burn avail wide member (umem
weld off, then the capacity-floor refuse off — both append-only). -/
theorem satisfied2_of_weldedBurnAvailWide (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash weldedBurnAvailWide minit mfin maddrs t) :
    Satisfied2 hash burnV3AvailWide minit mfin maddrs t :=
  satisfied2_of_gentianDeployedBareRefuseAt hash (cavBaseOf BU_AVAIL_BB) burnV3AvailWide
    (satisfied2_of_weldUMemIntoWide hash burnAvailWideRefused _ h)

/-! ## §2 — the per-row v1 collapses on the WIRE objects. -/

/-- A welded-crown burn witness forces the hardened burn face's FULL v1 denotation on every
row. -/
theorem weldedBurnAvailWide_row_v1 (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash weldedBurnAvailWide minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    satisfiedVm hash Dregg2.Circuit.Emit.EffectVmEmitBurn.burnVmDescriptorAvail
      (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
  burnAvailWide_row_v1 permOut hash minit mfin maddrs t
    (hside.toFaithfulW (satisfied2_of_weldedBurnAvailWide hash hsat)) i hi

/-- A bare-wide crown burn (refused, unwelded) witness forces the same v1 denotation. -/
theorem refusedBurnAvailWide_row_v1 (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash burnAvailWideRefused minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    satisfiedVm hash Dregg2.Circuit.Emit.EffectVmEmitBurn.burnVmDescriptorAvail
      (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
  burnAvailWide_row_v1 permOut hash minit mfin maddrs t
    (hside.toFaithfulW (satisfied2_of_gentianDeployedBareRefuseAt hash (cavBaseOf BU_AVAIL_BB)
      burnV3AvailWide hsat)) i hi

/-! ## §3 — THE WIDE DISCHARGE: burn availability + the EXACT ℤ debit, forced by a
WELDED-registry witness. The decode is the narrow `rotatedEncodesBurnAvail` verbatim
(descriptor-independent). -/

/-- **`wideBurn_availability_and_exact_move_forced`** — the umem-WELDED, refuse-carrying crown
burn row (the exact welded-registry wire object) FORCES `amt ≤ pre.kernel.bal cell a` AND the
EXACT ℤ debit. The wide-burn well-supply-inflation forgery (audit forgery 2) is closed on the
welded leg. -/
theorem wideBurn_availability_and_exact_move_forced (hash : List ℤ → ℤ)
    {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash weldedBurnAvailWide minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesBurnAvail hash minit mfin maddrs t pre post actor cell a amt) :
    amt ≤ pre.kernel.bal cell a
    ∧ post.kernel.bal cell a = pre.kernel.bal cell a - amt := by
  have hv1 := weldedBurnAvailWide_row_v1 hash hside hsat henc.di henc.hdi
  have hlastf : (henc.di + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact henc.hdiNotLast
  rw [hlastf] at hv1
  obtain ⟨hbLo, _, _, _, _, _, _, hAmt, hsaLo, _⟩ := henc.hdiEnc
  have h := Dregg2.Circuit.Emit.EffectVmEmitBurn.burnAvail_derives_availability_row hash
    (envAt t henc.di) (henc.di == 0) henc.hdiCanon hv1
  rw [hAmt, hbLo, henc.hholderPre, hsaLo, henc.hholderPost] at h
  exact h

/-- Availability alone, on the welded crown burn row (`guardAvail`, wide-forced). -/
theorem wideBurn_availability_forced (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash weldedBurnAvailWide minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesBurnAvail hash minit mfin maddrs t pre post actor cell a amt) :
    amt ≤ pre.kernel.bal cell a :=
  (wideBurn_availability_and_exact_move_forced hash hside hsat pre post actor cell a amt
    henc).1

/-- The same discharge on the BARE-WIDE crown burn row (refused, unwelded — the
`WIDE_REGISTRY_STAGED_TSV` object). -/
theorem wideBurn_availability_and_exact_move_forced_refused (hash : List ℤ → ℤ)
    {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash burnAvailWideRefused minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesBurnAvail hash minit mfin maddrs t pre post actor cell a amt) :
    amt ≤ pre.kernel.bal cell a
    ∧ post.kernel.bal cell a = pre.kernel.bal cell a - amt := by
  have hv1 := refusedBurnAvailWide_row_v1 hash hside hsat henc.di henc.hdi
  have hlastf : (henc.di + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact henc.hdiNotLast
  rw [hlastf] at hv1
  obtain ⟨hbLo, _, _, _, _, _, _, hAmt, hsaLo, _⟩ := henc.hdiEnc
  have h := Dregg2.Circuit.Emit.EffectVmEmitBurn.burnAvail_derives_availability_row hash
    (envAt t henc.di) (henc.di == 0) henc.hdiCanon hv1
  rw [hAmt, hbLo, henc.hholderPre, hsaLo, henc.hholderPost] at h
  exact h

/-! ## §4 — the full refinement on the welded wide path (no `guardAvail` residual anywhere). -/

/-- **`burn_descriptorRefinesAvail_weldedWide`** — satisfying the WELDED wide crown burn
together with the hardened decode forces the KERNEL's `BurnSpec`, with availability sourced
FROM THE WITNESS. The wide mirror of
`RotatedKernelRefinementMintBurnAvail.burn_descriptorRefinesAvail`. -/
theorem burn_descriptorRefinesAvail_weldedWide (hash : List ℤ → ℤ)
    {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash weldedBurnAvailWide minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesBurnAvail hash minit mfin maddrs t pre post actor cell a amt) :
    Spec.SupplyDestruction.BurnSpec pre actor cell a amt post := by
  have havail := wideBurn_availability_forced hash hside hsat pre post actor cell a amt henc
  exact ⟨⟨henc.guardAuth, henc.guardNonNeg, havail,
      henc.guardLiveCell, henc.guardLiveWell, henc.guardDistinct, henc.guardLifecycleLive⟩,
    henc.hledgerFrame, henc.logAdv,
    henc.frAccounts, henc.frCell, henc.frCaps, henc.frNullifiers, henc.frRevoked,
    henc.frCommitments, henc.frSlotCaveats, henc.frFactories, henc.frLifecycle,
    henc.frDeathCert, henc.frDelegate, henc.frDelegations, henc.frDelegationEpoch,
    henc.frDelegationEpochAt, henc.frHeaps, henc.frNullifierRoot, henc.frRevokedRoot,
    henc.frCommitmentsRoot⟩

/-! ## §5 — THE TEETH: the well-supply-inflation forgery class is UNSAT on every retargeted
wide-burn member. -/

/-- ANY over-burn decode riding a satisfying WELDED crown witness is UNSAT. -/
theorem weldedBurnWide_rejects_overburn (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash weldedBurnAvailWide minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesBurnAvail hash minit mfin maddrs t pre post actor cell a amt)
    (hforge : pre.kernel.bal cell a < amt) : False := by
  have h := wideBurn_availability_forced hash hside hsat pre post actor cell a amt henc
  omega

/-- The audit's CONCRETE forgery witness (`pre.bal cell a = 1`, `amt = 1006632961` — the
`before=1, amount=1006632961, after=1006632961` well-supply-inflation trace of
`docs/FINDING-modp-wrap-forgery-audit.md` forgery 2, whose ledger frame would CREDIT the well
by the forged ~10⁹) is UNSAT on the welded wide crown burn. -/
theorem weldedBurnWide_audit_forgery_unsat (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash weldedBurnAvailWide minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesBurnAvail hash minit mfin maddrs t pre post actor cell a amt)
    (hbal : pre.kernel.bal cell a = 1) (hamt : amt = 1006632961) : False := by
  refine weldedBurnWide_rejects_overburn hash hside hsat pre post actor cell a amt henc ?_
  omega

/-- The over-burn is UNSAT on the bare-wide (refused, unwelded) crown burn row. -/
theorem refusedBurnWide_rejects_overburn (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash burnAvailWideRefused minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesBurnAvail hash minit mfin maddrs t pre post actor cell a amt)
    (hforge : pre.kernel.bal cell a < amt) : False := by
  have h := (wideBurn_availability_and_exact_move_forced_refused hash hside hsat pre post
    actor cell a amt henc).1
  omega

/-- The audit's concrete witness is UNSAT on the bare-wide crown burn row too. -/
theorem refusedBurnWide_audit_forgery_unsat (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash burnAvailWideRefused minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesBurnAvail hash minit mfin maddrs t pre post actor cell a amt)
    (hbal : pre.kernel.bal cell a = 1) (hamt : amt = 1006632961) : False := by
  refine refusedBurnWide_rejects_overburn hash hside hsat pre post actor cell a amt henc ?_
  omega

/-! ## §6 — Axiom-hygiene tripwires. -/

#assert_axioms satisfied2_of_weldedBurnAvailWide
#assert_axioms weldedBurnAvailWide_row_v1
#assert_axioms refusedBurnAvailWide_row_v1
#assert_axioms wideBurn_availability_and_exact_move_forced
#assert_axioms wideBurn_availability_forced
#assert_axioms wideBurn_availability_and_exact_move_forced_refused
#assert_axioms burn_descriptorRefinesAvail_weldedWide
#assert_axioms weldedBurnWide_rejects_overburn
#assert_axioms weldedBurnWide_audit_forgery_unsat
#assert_axioms refusedBurnWide_rejects_overburn
#assert_axioms refusedBurnWide_audit_forgery_unsat

end Dregg2.Circuit.RotatedKernelRefinementMintBurnAvailWide
