/-
# Dregg2.Circuit.Emit.AvailWideFeeMember — the HARDENED wide FEE'D-transfer member (the WIDE-fee
availability wrap-forgery closed: the `transferFeeVmDescriptor2R24` wide crown host rebuilt over
the §11.8 fee availability face `transferFeeVmDescriptorAvail`).

## What this module is

`AvailWideMembers` closed the WIDE transfer/TB routes over the §11.7 borrow-weld face (and the
burn twin over §8¾). The wide registry's FEE'D-transfer crown host (`v3RegistryCapOpenWide` tail
position 44: `wideAppend (withDfaRcPins transferFeeV3) 188 427`) was still built over the BARE
fee face — so a wide/welded fee proof carried NO borrow gates and the GAP #4 underflow-wrap
mint-from-nothing stayed open on the wide leg THROUGH EITHER DEBIT LEG (amount OR fee: the
fee-leg witness `before=1, amount=0, fee=1006632961` wraps and passes the bare 30-bit ranges) —
after the narrow fee flip (`transferFeeV3AvailWire`, `RotatedKernelRefinementFeeAvail`) already
closed the 1-felt wire. This module builds the wide fee AVAIL member the emission retargets to:

  * **`transferFeeAvailWide`** — the §11.8 fee availability face (MID-linked borrow/carry
    chains: dir-gated `before − amount = mid`, (1−dir)-gated `before + amount = mid`, UNGATED
    `mid − fee = after`, all 15-bit limbs) lifted `v3OfFrozenFeeWide` (freeze → FEE PIN → wide
    graduation, `transferFeeV3`'s exact composition) + the rc pins at the fee-avail-shifted
    geometry (= the narrow wire member `transferFeeV3AvailWire`), wide-appended at the FEE avail
    face base `FEE_AVAIL_BB = FEE_AVAIL_WIDTH = 204`. NO capacity-floor refuse and NO membership
    teeth (the fee key is registry tail position 44, not a bare cohort route — the deployed
    fee member's wrapper shape, mirrored wrapper-for-wrapper). PI layout UNCHANGED at 67
    (46 base + fee pin 46 + rc 47..50 + 16 wide anchors); width 2607 → 2623 (+16 fee avail pad).

## THE FEE-PINNED COLLAPSE KEYSTONE (`wideEmbeddedFee_sound_v1`)

The fee face composes `v3OfFrozenFeeWide = graduateV1Wide ∘ rotateV3WithFeePin ∘
rotateV3FrozenAuthority` — one appended `.piBinding` (the fee pin) between the freeze and the
graduation, which `AvailWideMembers.wideEmbedded_sound_v1` (stated over `v3OfFrozenWide`) cannot
see. `wideEmbeddedFee_sound_v1` is its fee-pinned twin: from a wide-faithful witness of ANY
descriptor `D` whose constraints EMBED the (legacy-pin-filtered) `v3OfFrozenFeeWide d`
constraints, the FULL per-row v1 denotation of the PRE-ROTATION fee face returns — exactly what
`transferFeeAvail_derives_availability_row` consumes. The fee pin's column (`FEE_COL`, a v1
column < 204) is never a retired commit-pin column (`bb/ab + B_STATE_COMMIT` = 383/622), so the
pin-filtered embed carries it and the three bullets mirror the transfer keystone verbatim.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem; NO sorryAx.
-/
import Dregg2.Circuit.Emit.CarrierComposed
import Dregg2.Circuit.Emit.AvailWireMembers

namespace Dregg2.Circuit.Emit.AvailWideFeeMember

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
  (EffectVmDescriptor VmConstraint satisfiedVm siteHoldsAll)
open Dregg2.Circuit.Emit.EffectVmEmitV2
  (graduableWide graduableWide_spec graduateV1Wide Satisfied2FaithfulWide WIDE_RANGE_WIDTHS
   rangeLookupW lookup_replaces_rangeW siteLookups_sound)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
  (rotateV3FrozenAuthority rotateV3FrozenAuthority_constraints v3OfFrozenFeeWide
   rotateV3WithFeePin rotateV3WithFeePin_constraints graduableWide_rotateV3WithFeePin
   graduableWide_rotateV3FrozenAuthority rotV3Appendix go_append_left B_STATE_COMMIT
   withDfaRcPins transferFeeV3)
open Dregg2.Circuit.Emit.EffectVmEmitRotationWide
  (wideAppend isLegacyCommitPin1 wideAppendixSpan)
open Dregg2.Circuit.Emit.CarrierComposed (wideAppend_mem_of_host)
open Dregg2.Circuit.Emit.AvailWireMembers
  (withDfaRcPinsAt withDfaRcPinsAt_constraints transferFeeV3AvailWire)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (transferFeeVmDescriptorAvail FEE_AVAIL_WIDTH)

set_option autoImplicit false
set_option maxRecDepth 16000

/-! ## §1 — THE FEE-PINNED COLLAPSE KEYSTONE. -/

/-- **`wideEmbeddedFee_sound_v1`** — the fee-pinned twin of
`AvailWideMembers.wideEmbedded_sound_v1`: a wide-faithful witness of ANY descriptor `D` whose
constraints EMBED the (legacy-pin-filtered) `v3OfFrozenFeeWide d` constraint set yields the FULL
per-row v1 denotation of the PRE-ROTATION fee face `d` (MID-linked borrow/carry weld gates +
15-bit teeth INCLUDED). `hclean` certifies (decidably, per member) that no face constraint is
itself pin-shaped; the fee pin (`rotateV3WithFeePin` appends ONE `.piBinding`, touching no
site/range) rides the embed like every other rotated constraint, and the two retired 1-felt
commit pins are appendix pins the face's v1 denotation never reads. -/
theorem wideEmbeddedFee_sound_v1 (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor) (D : EffectVmDescriptor2) (bb ab : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hgrad : graduableWide d = true)
    (hclean : ∀ c ∈ d.constraints,
      isLegacyCommitPin1 bb ab (VmConstraint2.base c) = false)
    (hemb : ∀ c ∈ (v3OfFrozenFeeWide d).constraints,
      isLegacyCommitPin1 bb ab c = false → c ∈ D.constraints)
    (hf : Satisfied2FaithfulWide permOut hash D minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash d (envAt t i) (i == 0) (i + 1 == t.rows.length) := by
  have hgradr : graduableWide (rotateV3WithFeePin (rotateV3FrozenAuthority d)) = true :=
    graduableWide_rotateV3WithFeePin (graduableWide_rotateV3FrozenAuthority hgrad)
  obtain ⟨hwf, hfit, hbits⟩ := graduableWide_spec hgradr
  intro i hi
  have hrow := hf.rowConstraints i hi
  refine ⟨?_, ?_, ?_⟩
  · -- the ORIGINAL fee face's v1 constraints (never the retired pins — `hclean`)
    intro c hc
    have hcr : c ∈ (rotateV3WithFeePin (rotateV3FrozenAuthority d)).constraints := by
      rw [rotateV3WithFeePin_constraints, rotateV3FrozenAuthority_constraints]
      exact List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ hc))
    have hmem : VmConstraint2.base c ∈ (v3OfFrozenFeeWide d).constraints := by
      show VmConstraint2.base c
        ∈ (graduateV1Wide (rotateV3WithFeePin (rotateV3FrozenAuthority d))).constraints
      unfold graduateV1Wide
      simp only [List.mem_append, List.mem_map, List.mem_mapIdx]
      exact Or.inl (Or.inl ⟨c, hcr, rfl⟩)
    exact hrow _ (hemb _ hmem (hclean c hc))
  · -- the ORIGINAL face's hash sites: the FULL fee-pinned rotated chained walk, then the prefix
    have hall : siteHoldsAll hash (envAt t i)
        (rotateV3WithFeePin (rotateV3FrozenAuthority d)).hashSites := by
      apply siteLookups_sound hash (t.tf .poseidon2) hf.chipSound (envAt t i)
        (rotateV3WithFeePin (rotateV3FrozenAuthority d)).hashSites
        (rotateV3WithFeePin (rotateV3FrozenAuthority d)).traceWidth hwf
      · intro s hs
        exact of_decide_eq_true (List.all_eq_true.mp hfit s hs)
      · intro j hj
        have hmem : VmConstraint2.lookup
            (siteLookup (rotateV3WithFeePin (rotateV3FrozenAuthority d)).hashSites
              (rotateV3WithFeePin (rotateV3FrozenAuthority d)).hashSites[j]
              ((rotateV3WithFeePin (rotateV3FrozenAuthority d)).traceWidth
                + (CHIP_OUT_LANES - 1) * j))
            ∈ (v3OfFrozenFeeWide d).constraints := by
          show _
            ∈ (graduateV1Wide (rotateV3WithFeePin (rotateV3FrozenAuthority d))).constraints
          unfold graduateV1Wide
          simp only [List.mem_append, List.mem_map, List.mem_mapIdx]
          exact Or.inl (Or.inr ⟨j, hj, rfl⟩)
        exact hrow _ (hemb _ hmem rfl)
    exact go_append_left hash (envAt t i) [] d.hashSites (rotV3Appendix d.traceWidth) hall
  · -- the ORIGINAL face's range teeth, each via ITS OWN width's table (15-bit EXACT)
    intro r hr
    have hb : r.bits ∈ WIDE_RANGE_WIDTHS := hbits r hr
    have hmem : VmConstraint2.lookup (rangeLookupW r) ∈ (v3OfFrozenFeeWide d).constraints := by
      show _ ∈ (graduateV1Wide (rotateV3WithFeePin (rotateV3FrozenAuthority d))).constraints
      unfold graduateV1Wide
      simp only [List.mem_append, List.mem_map, List.mem_mapIdx]
      exact Or.inr ⟨r, hr, rfl⟩
    exact lookup_replaces_rangeW r.bits t.tf (hf.rangeTablesWideFaithful r.bits hb)
      (envAt t i) r.wire (hrow _ (hemb _ hmem rfl))

#assert_axioms wideEmbeddedFee_sound_v1

/-! ## §2 — the wide FEE'D-transfer AVAIL member. -/

/-- The hardened fee-pinned rotated graduated fee face — the SAME term as
`RotatedKernelRefinementFeeAvail.transferFeeV3Avail` (`v3OfFrozenFeeWide
transferFeeVmDescriptorAvail`), restated here so the emission layer does not import the
refinement tower. -/
def transferFeeAvailV3W : EffectVmDescriptor2 :=
  v3OfFrozenFeeWide transferFeeVmDescriptorAvail

/-- The FEE avail wide BEFORE base: `rotateV3` lays the rotated limbs at the hardened FEE FACE
width (`FEE_AVAIL_WIDTH = 204` — the bare 188 shifted by the 16-column fee avail pad: the
transfer weld's 10 + MID limbs + fee limbs + fee borrow bits). -/
def FEE_AVAIL_BB : Nat := FEE_AVAIL_WIDTH

#guard FEE_AVAIL_BB == transferFeeVmDescriptorAvail.traceWidth
#guard FEE_AVAIL_BB == 204
#guard transferFeeAvailV3W.piCount == 47
#guard transferFeeAvailV3W.traceWidth == 1663
#guard graduableWide transferFeeVmDescriptorAvail
-- the Rust avail-pad key (TRANSFER_FEE_AVAIL_PAD = 16) survives every wrapper
#guard transferFeeAvailV3W.name.startsWith "dregg-effectvm-transfer-v1-fee-avail"

/-- **`transferFeeAvailWide`** — the FEE'D-transfer crown wide member post-retarget (the
`transferFeeVmDescriptor2R24` wide-registry host, `v3RegistryCapOpenWide` tail position 44):
the narrow hardened wire member (`transferFeeV3AvailWire = withDfaRcPinsAt FEE_AVAIL_WIDTH
transferFeeAvailV3W` — rc pins ONLY, the deployed fee member's wrapper shape, NO refuse)
wide-appended at the FEE avail face base. Geometry mirror of the bare wide fee member at the
fee avail pad (+16 everywhere; the 67-PI layout — 46 base + fee pin 46 + rc 47..50 + 16 wide
anchors — UNCHANGED). -/
def transferFeeAvailWide : EffectVmDescriptor2 :=
  wideAppend transferFeeV3AvailWire FEE_AVAIL_BB (FEE_AVAIL_BB + 239)

-- Geometry pins: the avail fee member mirrors the bare wide fee member (+16 pad): 67 PIs,
-- width 2623 (= 1663 + wideAppendixSpan 960).
#guard transferFeeAvailWide.piCount == 67
#guard transferFeeAvailWide.traceWidth == 2623
#guard transferFeeAvailWide.traceWidth == transferFeeAvailV3W.traceWidth + wideAppendixSpan
#guard transferFeeAvailWide.name == "dregg-effectvm-transfer-v1-fee-avail-rot24-v3-staged"
-- The bare wide fee twin for reference: the SAME 67-PI layout, fee-avail-shifted columns.
#guard (wideAppend (withDfaRcPins transferFeeV3) 188 (188 + 239)).piCount == 67
#guard transferFeeAvailWide.traceWidth
  == (wideAppend (withDfaRcPins transferFeeV3) 188 (188 + 239)).traceWidth + 16

/-! ## §3 — the pin-cleanliness + membership embed (the keystone's premises). -/

/-- No hardened-fee-face v1 constraint is a retired legacy commit pin: every face piBinding
column rides the v1 face (`< 204`), far below the rotated commit carriers
(`FEE_AVAIL_BB + B_STATE_COMMIT = 383` / `FEE_AVAIL_BB + 239 + B_STATE_COMMIT = 622`).
Decidable — the face is concrete. -/
theorem transferFeeAvail_no_legacy_pins :
    transferFeeVmDescriptorAvail.constraints.all
      (fun c => !isLegacyCommitPin1 FEE_AVAIL_BB (FEE_AVAIL_BB + 239) (VmConstraint2.base c))
      = true := by decide

theorem transferFeeAvail_clean :
    ∀ c ∈ transferFeeVmDescriptorAvail.constraints,
      isLegacyCommitPin1 FEE_AVAIL_BB (FEE_AVAIL_BB + 239) (VmConstraint2.base c) = false := by
  intro c hc
  have h := List.all_eq_true.mp transferFeeAvail_no_legacy_pins c hc
  simpa using h

/-- Face-host constraint membership in the fee avail wide member: the rc pins only APPEND, and
`wideAppend` keeps every non-pin host constraint (`wideAppend_mem_of_host`). -/
theorem feeAvailHost_mem_feeAvailWide :
    ∀ c ∈ transferFeeAvailV3W.constraints,
      isLegacyCommitPin1 FEE_AVAIL_BB (FEE_AVAIL_BB + 239) c = false →
      c ∈ transferFeeAvailWide.constraints := by
  intro c hc hnp
  refine wideAppend_mem_of_host _ FEE_AVAIL_BB (FEE_AVAIL_BB + 239) c ?_ hnp
  show c ∈ (withDfaRcPinsAt FEE_AVAIL_WIDTH transferFeeAvailV3W).constraints
  rw [withDfaRcPinsAt_constraints]
  exact List.mem_append_left _ hc

/-! ## §4 — the per-member v1 collapse: the hardened fee face's FULL row denotation returns from
a wide-faithful witness of the retargeted member (the MID-linked borrow/carry gates + 15-bit
teeth the fee availability keystone `transferFeeAvail_derives_availability_row` consumes). -/

/-- The fee avail wide member forces the hardened fee face's v1 denotation on every row. -/
theorem feeAvailWide_row_v1 (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hf : Satisfied2FaithfulWide permOut hash transferFeeAvailWide minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash transferFeeVmDescriptorAvail (envAt t i)
        (i == 0) (i + 1 == t.rows.length) :=
  wideEmbeddedFee_sound_v1 permOut hash transferFeeVmDescriptorAvail transferFeeAvailWide
    FEE_AVAIL_BB (FEE_AVAIL_BB + 239) minit mfin maddrs t (by decide) transferFeeAvail_clean
    feeAvailHost_mem_feeAvailWide hf

#assert_axioms transferFeeAvail_clean
#assert_axioms feeAvailHost_mem_feeAvailWide
#assert_axioms feeAvailWide_row_v1

end Dregg2.Circuit.Emit.AvailWideFeeMember
