/-
# Dregg2.Circuit.RotatedKernelRefinementCapOpenAvailWide — the WIDE cap-open-EFF transfer
availability discharge, AUTHORITY INTACT (the wide-cap-open-EFF availability wrap-forgery twin,
closed).

## What this module is

`RotatedKernelRefinementCapOpenAvail` closed the GAP #4 underflow-wrap mint-from-nothing on the
NARROW cap-open transfer routes (`transferCapOpenEffV3Avail` + the TB twin), and
`RotatedKernelRefinementAvailWide` carried the discharge to the WIDE crown + TB wire objects. The
WIDE cap-open EFF member (`transferCapOpenEffVmDescriptor2R24`, `v3RegistryCapOpenWide` position
42) was the remaining transfer-shaped wide route still built over the BARE face — a cap-AUTHORIZED
wide transfer proof carried NO borrow gates, so the wrap forgery
(`docs/FINDING-modp-wrap-forgery-audit.md`, forgery 1) stayed open on that leg. This module
discharges availability on the EXACT post-retarget wire objects:

  * **`transferCapOpenEffAvailWide`** (`AvailWideMembers` §8) — the crown host post-retarget:
    the already-flipped narrow member wide-appended at the AVAIL face base (§0 pins the tie
    `= wideAppend transferCapOpenEffV3Avail TR_AVAIL_BB (TR_AVAIL_BB + B_SPAN)` definitionally —
    `B_SPAN` is the ONE named block span, 247 at the 184-limb geometry, was 239);
  * **`weldedTransferCapOpenEffAvailWide`** (`EffectVmEmitUMemWeldWide`) — its umem-welded twin
    (crown key, not a bare cohort route: umem-only, no capacity-floor refuse).

The chain: welded accept → (`satisfied2_of_weldUMemIntoWide`) wide accept →
(`effAvailWide_row_v1` = `wideEmbedded_sound_v1` over the legacy-pin-filtered embed) the hardened
face's per-row `satisfiedVm` → (`transferAvail_derives_availability_row`) the borrow-forced order
+ EXACT ℤ move → (the UNCHANGED descriptor-independent `rotatedEncodesAvail` decode) the kernel
statement. NO `guardAvail` anywhere.

## AUTHORITY INTACT (the second half of the twin's bar)

The wide weld must not break the cap-open AUTHORITY facet. `wideAppend` retires ONLY the two
legacy 1-felt commit pins; the whole cap-open appendix (the depth-16 membership open, the genuine
submask facet gates, the per-limb mask-recon gates, the selected-bit tooth) is `.lookup`/`.gate`-
shaped and rides the wide member VERBATIM (`capOpenAppendix_mem_effAvailWide`). §3 re-establishes
the live authority keystones ON THE WIDE MEMBER via the membership-parametric bridge
(`capOpenMem_satisfiedEff` / `capOpenMem_gate_forces`, the cap-open mirror of
`wideEmbedded_sound_v1`'s design):

  * **`wideCapOpenEffAvail_authorizes`** (+ the welded twin) — a satisfying wide witness whose
    opened leaf IS the effect-faithful `(actor ⇒ src)` edge discharges the kernel's
    `authorizedFacetB` and `leaf.target = src`, forced by the depth-16 open — the exact
    `transferCapOpenEffV3Avail_authorizes` statement, wide;
  * **`wideCapOpenEffAvail_rejects_wrong_facet`** (+ the welded twin) — a leaf whose
    `EFF_TRANSFER` mask bit is CLEAR is UNSAT on the wide member: the facet gate BITES through
    the wide weld. Nothing about `attenuate_nonAmp` / the facet gates changes: the appendix
    constraints are verbatim, only their host widened.

## Teeth

`wideCapOpenEff_rejects_overdebit` / `_welded` + the audit's concrete forgery witness
(`pre.bal = 0, amt = 10⁹` UNSAT) close the wrap class on the cap-authorized wide route;
the wrong-facet UNSAT teeth close the authority half.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. NEW file; imports
are read-only.
-/
import Dregg2.Circuit.RotatedKernelRefinementCapOpenAvail
import Dregg2.Circuit.Emit.EffectVmEmitUMemWeldWide

namespace Dregg2.Circuit.RotatedKernelRefinementCapOpenAvailWide

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitV2 (Satisfied2FaithfulWide)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
open Dregg2.Circuit.Emit.AvailWideMembers
  (transferAvailV3W TR_AVAIL_BB transferCapOpenEffAvailWide effAvailWide_row_v1
   capOpenAppendix_mem_effAvailWide)
open Dregg2.Circuit.Emit.EffectVmEmitUMemWeldWide
  (weldedTransferCapOpenEffAvailWide satisfied2_of_weldUMemIntoWide)
open Dregg2.Circuit.Emit.CapOpenEmit
  (capOpenCols CapOpenRowCanon capOpenConstraintsEff capOpenMem_satisfiedEff
   capOpenMem_gate_forces EFF_TRANSFER)
open Dregg2.Circuit.DeployedCapOpen (leafOf groupVal capPermOut MASK_BITS selectedBitGate)
open Dregg2.Circuit.DeployedCapTree (CapLeaf Cap8Scheme)
open Dregg2.Circuit.DeployedCapTree.Cap8Scheme (DeployedFaithfulEff8)
open Dregg2.Circuit.DeployedCapTree.CapHashScheme (tierOfTag)
open Dregg2.Authority (Label)
open Dregg2.Exec.FacetAuthority
  (AuthProvided FacetCaps authorizedFacetB authorizedFacetB_eq_eff)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.RotatedKernelRefinementAvail (RotTableSideW rotatedEncodesAvail)
open Dregg2.Circuit.RotatedKernelRefinementCapOpenAvail (transferCapOpenEffV3Avail)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false

/-! ## §0 — the tie: the wide member IS the wide lift of the already-flipped NARROW member. -/

/-- The emission-layer wide member (`AvailWideMembers.transferCapOpenEffAvailWide`) is
definitionally `wideAppend` of the flipped narrow member
(`RotatedKernelRefinementCapOpenAvail.transferCapOpenEffV3Avail`) at the AVAIL face base — the
two towers name ONE term. -/
theorem transferCapOpenEffAvailWide_eq :
    transferCapOpenEffAvailWide
      = Dregg2.Circuit.Emit.EffectVmEmitRotationWide.wideAppend transferCapOpenEffV3Avail
          TR_AVAIL_BB (TR_AVAIL_BB + Dregg2.Circuit.Emit.EffectVmEmitRotationV3.B_SPAN) := rfl

/-! ## §1 — the row-v1 collapses on the wire objects (wide + welded). -/

/-- A WELDED cap-open-EFF wide witness forces the hardened face's FULL v1 denotation on every
row (the weld peel, then the wide embed collapse). -/
theorem weldedEffAvailWide_row_v1 (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash weldedTransferCapOpenEffAvailWide minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    satisfiedVm hash transferVmDescriptorAvail
      (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
  effAvailWide_row_v1 permOut hash minit mfin maddrs t
    (hside.toFaithfulW (satisfied2_of_weldUMemIntoWide hash transferCapOpenEffAvailWide _ hsat))
    i hi

/-! ## §2 — THE WIDE DISCHARGE: availability + the EXACT ℤ debit on the cap-authorized wide
route. The decode is the narrow `rotatedEncodesAvail` verbatim (descriptor-independent). -/

/-- **`wideCapOpenEff_availability_and_exact_move_forced`** — the WIDE cap-open EFF transfer
member (the exact `transferCapOpenEffVmDescriptor2R24` crown wire object post-retarget) FORCES
`tr.amt ≤ pre.bal src a` AND the EXACT ℤ debit. The wide-cap-open-EFF wrap forgery is closed. -/
theorem wideCapOpenEff_availability_and_exact_move_forced (hash : List ℤ → ℤ)
    {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferCapOpenEffAvailWide minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a) :
    tr.amt ≤ pre.kernel.bal tr.src a
    ∧ post.kernel.bal tr.src a = pre.kernel.bal tr.src a - tr.amt := by
  have hv1 := effAvailWide_row_v1 permOut hash minit mfin maddrs t (hside.toFaithfulW hsat)
    henc.di henc.hdi
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

/-- The same discharge on the WELDED cap-open EFF wide member (the welded-registry wire
object). -/
theorem wideCapOpenEff_availability_and_exact_move_forced_welded (hash : List ℤ → ℤ)
    {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash weldedTransferCapOpenEffAvailWide minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a) :
    tr.amt ≤ pre.kernel.bal tr.src a
    ∧ post.kernel.bal tr.src a = pre.kernel.bal tr.src a - tr.amt :=
  wideCapOpenEff_availability_and_exact_move_forced hash hside
    (satisfied2_of_weldUMemIntoWide hash transferCapOpenEffAvailWide _ hsat) pre post tr a henc

/-! ## §2.T — THE TEETH: the audit forgery class is UNSAT on the cap-authorized wide route. -/

/-- ANY over-debit decode riding a satisfying wide cap-open-EFF witness is UNSAT: a
cap-AUTHORIZED wide transfer still cannot move more than the source holds. -/
theorem wideCapOpenEff_rejects_overdebit (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferCapOpenEffAvailWide minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a)
    (hforge : pre.kernel.bal tr.src a < tr.amt) : False := by
  have h := (wideCapOpenEff_availability_and_exact_move_forced hash hside hsat pre post
    tr a henc).1
  omega

/-- The over-debit is UNSAT on the WELDED member too. -/
theorem wideCapOpenEff_rejects_overdebit_welded (hash : List ℤ → ℤ)
    {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash weldedTransferCapOpenEffAvailWide minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a)
    (hforge : pre.kernel.bal tr.src a < tr.amt) : False := by
  have h := (wideCapOpenEff_availability_and_exact_move_forced_welded hash hside hsat pre post
    tr a henc).1
  omega

/-- The audit's CONCRETE forgery witness (`pre.bal src a = 0`, `tr.amt = 10⁹` — forgery 1 of
`docs/FINDING-modp-wrap-forgery-audit.md`) is UNSAT on the wide cap-open EFF crown member. -/
theorem wideCapOpenEff_audit_forgery_unsat (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferCapOpenEffAvailWide minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a)
    (hbal : pre.kernel.bal tr.src a = 0) (hamt : tr.amt = 1000000000) : False := by
  refine wideCapOpenEff_rejects_overdebit hash hside hsat pre post tr a henc ?_
  omega

/-! ## §3 — AUTHORITY INTACT: the live cap-open keystones re-established ON THE WIDE MEMBER.

The cap-open appendix rides the wide member verbatim (`capOpenAppendix_mem_effAvailWide` — the
appendix is never pin-shaped, so `wideAppend`'s legacy-pin retirement misses it entirely), and
the membership-parametric bridge (`capOpenMem_satisfiedEff` / `capOpenMem_gate_forces`) rebuilds
`SatisfiedEff` from ANY embedding descriptor — so each live keystone is one instantiation at the
wide member, at the SAME appendix columns (`capOpenCols transferAvailV3W.traceWidth`) as the
narrow member. Nothing about the facet gates / mask-recon / non-amplification changes. -/

open Dregg2.Circuit.DeployedCapOpen in
/-- **`wideCapOpenEffAvail_authorizes`** — the LIVE transfer authority keystone on the WIDE
member (the mirror of `transferCapOpenEffV3Avail_authorizes`, host widened): a `Satisfied2`
witness whose opened leaf IS the effect-faithful `(actor ⇒ src)` edge discharges the kernel's
`authorizedFacetB caps provided turn` and `leaf.target = src`, forced by the depth-16 open. -/
theorem wideCapOpenEffAvail_authorizes (S8 : Cap8Scheme) (hash : List ℤ → ℤ)
    (vkOfTag : ℤ → Nat) (provided : AuthProvided)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash transferCapOpenEffAvailWide minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcanon : CapOpenRowCanon (capOpenCols transferAvailV3W.traceWidth) (envAt t i)
      EFF_TRANSFER)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithfulEff8 S8 vkOfTag provided (1 <<< EFF_TRANSFER) caps
      (groupVal (envAt t i) (capOpenCols transferAvailV3W.traceWidth).capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : (envAt t i).loc (capOpenCols transferAvailV3W.traceWidth).src = (src : ℤ))
    (hedge : leafOf (capOpenCols transferAvailV3W.traceWidth) (envAt t i) = leafAt actor src)
    (htier : (tierOfTag vkOfTag (leafAt actor src).auth_tag).isSatisfiedBy provided = true) :
    authorizedFacetB caps provided
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) := by
  have hse := capOpenMem_satisfiedEff transferAvailV3W.traceWidth EFF_TRANSFER
    transferCapOpenEffAvailWide capOpenAppendix_mem_effAvailWide hash minit mfin maddrs t hsat
    i hi hnotlast hcanon
  have h := capOpenEff_authorizes S8 hash t.tf (capOpenCols transferAvailV3W.traceWidth)
    (envAt t i) EFF_TRANSFER (by decide) vkOfTag provided hChip hse caps leafAt hfaith
    actor src dst amt hsrc hedge htier
  refine ⟨?_, h.2⟩
  rw [authorizedFacetB_eq_eff]
  exact h.1

open Dregg2.Circuit.DeployedCapOpen in
/-- The authority keystone survives the umem weld too (the welded-registry wire object). -/
theorem wideCapOpenEffAvail_authorizes_welded (S8 : Cap8Scheme) (hash : List ℤ → ℤ)
    (vkOfTag : ℤ → Nat) (provided : AuthProvided)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hChip : ChipTableSoundN (capPermOut S8) (t.tf .poseidon2))
    (hsat : Satisfied2 hash weldedTransferCapOpenEffAvailWide minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (hcanon : CapOpenRowCanon (capOpenCols transferAvailV3W.traceWidth) (envAt t i)
      EFF_TRANSFER)
    (caps : FacetCaps) (leafAt : Label → Label → CapLeaf)
    (hfaith : DeployedFaithfulEff8 S8 vkOfTag provided (1 <<< EFF_TRANSFER) caps
      (groupVal (envAt t i) (capOpenCols transferAvailV3W.traceWidth).capRoot) leafAt)
    (actor src dst : Label) (amt : ℤ)
    (hsrc : (envAt t i).loc (capOpenCols transferAvailV3W.traceWidth).src = (src : ℤ))
    (hedge : leafOf (capOpenCols transferAvailV3W.traceWidth) (envAt t i) = leafAt actor src)
    (htier : (tierOfTag vkOfTag (leafAt actor src).auth_tag).isSatisfiedBy provided = true) :
    authorizedFacetB caps provided
      { actor := actor, src := src, dst := dst, amt := amt } = true
    ∧ (leafAt actor src).target = (src : ℤ) :=
  wideCapOpenEffAvail_authorizes S8 hash vkOfTag provided minit mfin maddrs t hChip
    (satisfied2_of_weldUMemIntoWide hash transferCapOpenEffAvailWide _ hsat)
    i hi hnotlast hcanon caps leafAt hfaith actor src dst amt hsrc hedge htier

/-- **`wideCapOpenEffAvail_rejects_wrong_facet`** — the wrong-facet tooth ON THE WIDE MEMBER:
a leaf whose `EFF_TRANSFER` mask bit is CLEAR ⟹ UNSAT. The selected-bit submask gate bites
through the wide weld, verbatim at the avail-shifted appendix columns (field-faithful, no
canonicality envelope — the clear bit pins the residual to `−1` and `p ∤ −1`). -/
theorem wideCapOpenEffAvail_rejects_wrong_facet (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace) (i : Nat) (hi : i < t.rows.length)
    (hnotlast : i + 1 ≠ t.rows.length)
    (hclear : (envAt t i).loc
      ((capOpenCols transferAvailV3W.traceWidth).bit EFF_TRANSFER) = 0) :
    ¬ Satisfied2 hash transferCapOpenEffAvailWide minit mfin maddrs t := by
  intro hsat
  have h := capOpenMem_gate_forces transferAvailV3W.traceWidth EFF_TRANSFER
    transferCapOpenEffAvailWide capOpenAppendix_mem_effAvailWide hash minit mfin maddrs t hsat
    i hi hnotlast (selectedBitGate (capOpenCols transferAvailV3W.traceWidth) EFF_TRANSFER)
    (by simp [capOpenConstraintsEff])
  unfold Dregg2.Circuit.DeployedCapOpen.selectedBitGate at h
  simp only [EmittedExpr.eval, hclear] at h
  rw [Int.modEq_zero_iff_dvd] at h
  obtain ⟨k, hk⟩ := h
  omega

/-- The wrong-facet tooth survives the umem weld (the welded-registry wire object). -/
theorem wideCapOpenEffAvail_rejects_wrong_facet_welded (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace) (i : Nat) (hi : i < t.rows.length)
    (hnotlast : i + 1 ≠ t.rows.length)
    (hclear : (envAt t i).loc
      ((capOpenCols transferAvailV3W.traceWidth).bit EFF_TRANSFER) = 0) :
    ¬ Satisfied2 hash weldedTransferCapOpenEffAvailWide minit mfin maddrs t := fun hsat =>
  wideCapOpenEffAvail_rejects_wrong_facet hash minit mfin maddrs t i hi hnotlast hclear
    (satisfied2_of_weldUMemIntoWide hash transferCapOpenEffAvailWide _ hsat)

/-! ## §4 — Axiom-hygiene tripwires. -/

#assert_axioms transferCapOpenEffAvailWide_eq
#assert_axioms weldedEffAvailWide_row_v1
#assert_axioms wideCapOpenEff_availability_and_exact_move_forced
#assert_axioms wideCapOpenEff_availability_and_exact_move_forced_welded
#assert_axioms wideCapOpenEff_rejects_overdebit
#assert_axioms wideCapOpenEff_rejects_overdebit_welded
#assert_axioms wideCapOpenEff_audit_forgery_unsat
#assert_axioms wideCapOpenEffAvail_authorizes
#assert_axioms wideCapOpenEffAvail_authorizes_welded
#assert_axioms wideCapOpenEffAvail_rejects_wrong_facet
#assert_axioms wideCapOpenEffAvail_rejects_wrong_facet_welded

end Dregg2.Circuit.RotatedKernelRefinementCapOpenAvailWide
