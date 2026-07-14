/-
# Dregg2.Circuit.Emit.AvailWideMembersNarrow — the NARROW-BASE twins of the deployed wide
availability members + their per-row v1 collapses.

## What this module is

`AvailWideMembers` / `AvailWideFeeMember` / `RotatedKernelRefinementCapOpenAvailWide` build the
deployed WIDE availability members over `v3OfFrozenWide` (the 25-wide Poseidon2 chip bus, 7
witnessed lane columns per hash site) and collapse each to the hardened face's per-row `satisfiedVm`
through `wideEmbedded_sound_v1` (a `Satisfied2FaithfulWide` witness). This module adds the NARROW
twin BESIDE each: the SAME member re-anchored on `v3OfFrozenWideNarrow`
(`GraduateWideNarrow.lean` — single-output sites on the 18-wide narrow bus, NO lane columns, so the
trace is `7·(#sites)` columns narrower) and the SAME collapse through `wideEmbeddedNarrow_sound_v1`
(a `Satisfied2FaithfulWideNarrow` witness). The recovered `satisfiedVm hash <face>` is byte-identical
to the wide twin's, so the downstream availability keystones
(`transferAvail_derives_availability_row` / the burn / fee analog) are UNCHANGED.

This is ADDITIVE and read-only against the deployed tower: `v3OfFrozenWide`, the wide members,
`wideEmbedded_sound_v1`, every descriptor/registry are UNTOUCHED. A later (ember-gated) registry
switch + VK regen routes the single-output sites of the live wide descriptor to the narrow bus; these
twins are the soundness layer that switch lands on.

## The members twinned (each: `MNarrow` def + `MNarrow_row_v1` collapse + a width-shrink `#guard`)

  * `transferAvailV3WNarrow`         (the bare hardened rotated face — collapse = `rotV3FrozenWideNarrow_sound_v1`);
  * `transferV3MembershipAvailWideNarrow`  (the crown membership-teeth transfer host);
  * `transferCapOpenTBAvailWideNarrow`     (the live-only TB transfer host);
  * `burnV3AvailWideNarrow`                (the crown burn host);
  * `transferCapOpenEffAvailWideNarrow`    (the crown cap-open-EFF transfer host — the member
    underlying `RotatedKernelRefinementCapOpenAvailWide`);
  * `transferFeeAvailWideNarrow`           (the crown fee'd-transfer host — over the NEW narrow
    fee-pinned keystone `wideEmbeddedFeeNarrow_sound_v1`).

The membership premises (`availHost_mem_…Narrow`) mirror the wide `availHost_mem_…` verbatim (the
wrappers `withDfaRcPinsAt` / `withMembershipTeethPinsAt` / `effCapOpenV3…` / `withSelectorGate` /
`wideAppend` are base-agnostic — they only APPEND), reusing the face-level pin-cleanliness lemmas
`transferAvail_clean` / `burnAvail_clean` / `transferFeeAvail_clean` UNCHANGED.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem; NO sorryAx. Table
soundness enters ONLY as the `Satisfied2FaithfulWideNarrow.chipTableFaithfulNarrow` field (itself
riding the clean `chip_lookup_sound_narrow`), never an axiom.
-/
import Dregg2.Circuit.Emit.GraduateWideNarrow
import Dregg2.Circuit.Emit.AvailWideMembers
import Dregg2.Circuit.Emit.AvailWideFeeMember

namespace Dregg2.Circuit.Emit.AvailWideMembersNarrow

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
  (EffectVmDescriptor VmConstraint satisfiedVm siteHoldsAll)
open Dregg2.Circuit.Emit.EffectVmEmitV2
  (graduableWide graduableWide_spec graduateV1WideNarrow Satisfied2FaithfulWideNarrow
   WIDE_RANGE_WIDTHS rangeLookupW lookup_replaces_rangeW siteLookupsNarrow_sound
   v3OfFrozenWideNarrow wideEmbeddedNarrow_sound_v1 rotV3FrozenWideNarrow_sound_v1)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
  (rotateV3FrozenAuthority rotateV3FrozenAuthority_constraints
   graduableWide_rotateV3FrozenAuthority graduableWide_rotateV3WithFeePin
   rotateV3WithFeePin rotateV3WithFeePin_constraints rotV3Appendix go_append_left B_STATE_COMMIT
   v3OfFrozenWide v3OfFrozenFeeWide)
open Dregg2.Circuit.Emit.EffectVmEmitRotationWide
  (wideAppend isLegacyCommitPin1 wideAppendixSpan)
open Dregg2.Circuit.Emit.CarrierComposed
  (withMembershipTeethPinsAt withMembershipTeethPinsAt_constraints wideAppend_mem_of_host)
open Dregg2.Circuit.Emit.AvailWireMembers
  (withDfaRcPinsAt withDfaRcPinsAt_constraints)
open Dregg2.Circuit.Emit.AvailWideMembers
  (TR_AVAIL_BB transferAvail_clean BU_AVAIL_BB burnAvail_clean)
open Dregg2.Circuit.Emit.AvailWideFeeMember
  (FEE_AVAIL_BB transferFeeAvail_clean)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (transferVmDescriptorAvail AVAIL_WIDTH transferFeeVmDescriptorAvail FEE_AVAIL_WIDTH)

set_option autoImplicit false
set_option maxRecDepth 16000

/-! ## §0 — the NEW narrow fee-pinned collapse keystone (`v3OfFrozenFeeWideNarrow` +
`wideEmbeddedFeeNarrow_sound_v1`).

The narrow mirror of `AvailWideFeeMember.wideEmbeddedFee_sound_v1`: the fee face composes
`v3OfFrozenFeeWide = graduateV1Wide ∘ rotateV3WithFeePin ∘ rotateV3FrozenAuthority` (one appended
`.piBinding` fee pin between freeze and graduation, which `wideEmbeddedNarrow_sound_v1` — stated over
`v3OfFrozenWideNarrow` — cannot see). This is its narrow-base twin: same walk, hash sites on the
18-wide narrow bus, NO lane columns. CONCLUSION byte-identical to `wideEmbeddedFee_sound_v1`. -/

/-- **`v3OfFrozenFeeWideNarrow d`** — the narrow-base fee-pinned WIDE graduated rotated fee face (the
narrow twin of `v3OfFrozenFeeWide`): `transferFeeV3`'s composition (freeze → fee pin → graduation)
with the hash sites on the 18-wide narrow bus, NO lane columns appended. -/
def v3OfFrozenFeeWideNarrow (d : EffectVmDescriptor) : EffectVmDescriptor2 :=
  graduateV1WideNarrow (rotateV3WithFeePin (rotateV3FrozenAuthority d))

/-- **`wideEmbeddedFeeNarrow_sound_v1`** — the narrow-base fee-pinned twin of
`AvailWideFeeMember.wideEmbeddedFee_sound_v1`: from a narrow-wide-faithful witness of ANY descriptor
`D` whose constraints EMBED the (legacy-pin-filtered) `v3OfFrozenFeeWideNarrow d` constraint set, the
FULL per-row v1 denotation of the PRE-ROTATION fee face `d` returns. Mirror of the fee wide keystone:
the ONLY changed leg is the hash-sites walk, discharging through `siteLookupsNarrow_sound` over
`poseidon2narrow` (via the structure's own narrow chip field) instead of the 25-wide
`siteLookups_sound`. CONCLUSION byte-identical. -/
theorem wideEmbeddedFeeNarrow_sound_v1 (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor) (D : EffectVmDescriptor2) (bb ab : Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hgrad : graduableWide d = true)
    (hclean : ∀ c ∈ d.constraints,
      isLegacyCommitPin1 bb ab (VmConstraint2.base c) = false)
    (hemb : ∀ c ∈ (v3OfFrozenFeeWideNarrow d).constraints,
      isLegacyCommitPin1 bb ab c = false → c ∈ D.constraints)
    (hf : Satisfied2FaithfulWideNarrow hash D minit mfin maddrs t) :
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
    have hmem : VmConstraint2.base c ∈ (v3OfFrozenFeeWideNarrow d).constraints := by
      show VmConstraint2.base c
        ∈ (graduateV1WideNarrow (rotateV3WithFeePin (rotateV3FrozenAuthority d))).constraints
      unfold graduateV1WideNarrow
      simp only [List.mem_append, List.mem_map]
      exact Or.inl (Or.inl ⟨c, hcr, rfl⟩)
    exact hrow _ (hemb _ hmem (hclean c hc))
  · -- the ORIGINAL face's hash sites: the FULL fee-pinned rotated chained NARROW walk, then prefix
    have hall : siteHoldsAll hash (envAt t i)
        (rotateV3WithFeePin (rotateV3FrozenAuthority d)).hashSites := by
      apply siteLookupsNarrow_sound hash (t.tf poseidon2narrow) hf.chipTableFaithfulNarrow
        (envAt t i) (rotateV3WithFeePin (rotateV3FrozenAuthority d)).hashSites hwf
      · intro s hs
        exact of_decide_eq_true (List.all_eq_true.mp hfit s hs)
      · intro j hj
        have hmem : VmConstraint2.lookup
            (siteLookupNarrow (rotateV3WithFeePin (rotateV3FrozenAuthority d)).hashSites
              (rotateV3WithFeePin (rotateV3FrozenAuthority d)).hashSites[j])
            ∈ (v3OfFrozenFeeWideNarrow d).constraints := by
          show _
            ∈ (graduateV1WideNarrow (rotateV3WithFeePin (rotateV3FrozenAuthority d))).constraints
          unfold graduateV1WideNarrow
          simp only [List.mem_append, List.mem_map]
          exact Or.inl (Or.inr ⟨(rotateV3WithFeePin (rotateV3FrozenAuthority d)).hashSites[j],
            List.getElem_mem hj, rfl⟩)
        exact hrow _ (hemb _ hmem rfl)
    exact go_append_left hash (envAt t i) [] d.hashSites (rotV3Appendix d.traceWidth) hall
  · -- the ORIGINAL face's range teeth, each via ITS OWN width's table (15-bit EXACT)
    intro r hr
    have hb : r.bits ∈ WIDE_RANGE_WIDTHS := hbits r hr
    have hmem : VmConstraint2.lookup (rangeLookupW r) ∈ (v3OfFrozenFeeWideNarrow d).constraints := by
      show _ ∈ (graduateV1WideNarrow (rotateV3WithFeePin (rotateV3FrozenAuthority d))).constraints
      unfold graduateV1WideNarrow
      simp only [List.mem_append, List.mem_map]
      exact Or.inr ⟨r, hr, rfl⟩
    exact lookup_replaces_rangeW r.bits t.tf (hf.rangeTablesWideFaithful r.bits hb)
      (envAt t i) r.wire (hrow _ (hemb _ hmem rfl))

#assert_axioms v3OfFrozenFeeWideNarrow
#assert_axioms wideEmbeddedFeeNarrow_sound_v1

/-! ## §1 — the narrow hardened rotated faces (the bare members). -/

/-- The narrow-base hardened rotated graduated transfer face (the narrow twin of
`transferAvailV3W = v3OfFrozenWide transferVmDescriptorAvail`). -/
def transferAvailV3WNarrow : EffectVmDescriptor2 := v3OfFrozenWideNarrow transferVmDescriptorAvail

/-- The narrow-base hardened rotated graduated burn face (the narrow twin of `burnAvailV3W`). -/
def burnAvailV3WNarrow : EffectVmDescriptor2 :=
  v3OfFrozenWideNarrow Dregg2.Circuit.Emit.EffectVmEmitBurn.burnVmDescriptorAvail

/-- The narrow-base hardened fee-pinned rotated graduated fee face (the narrow twin of
`transferFeeAvailV3W`). -/
def transferFeeAvailV3WNarrow : EffectVmDescriptor2 :=
  v3OfFrozenFeeWideNarrow transferFeeVmDescriptorAvail

/-- **`transferAvailV3WNarrow_row_v1`** — the bare narrow hardened rotated face forces the hardened
face's v1 denotation on every row (the narrow twin of `RotatedKernelRefinementAvail.transferV3Avail`
collapse, via the already-proven `rotV3FrozenWideNarrow_sound_v1`). -/
theorem transferAvailV3WNarrow_row_v1 (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hf : Satisfied2FaithfulWideNarrow hash transferAvailV3WNarrow minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash transferVmDescriptorAvail (envAt t i)
        (i == 0) (i + 1 == t.rows.length) :=
  rotV3FrozenWideNarrow_sound_v1 hash transferVmDescriptorAvail minit mfin maddrs t (by decide) hf

#assert_axioms transferAvailV3WNarrow_row_v1

/-! ## §2 — the crown membership-teeth transfer narrow twin. -/

/-- The AVAIL narrow membership teeth column: past the narrow avail wide carriers
(`transferAvailV3WNarrow.traceWidth + wideAppendixSpan` — the narrow mirror of
`MEMBERSHIP_TEETH_COL_AVAIL_WIDE`; the teeth PI slots are UNCHANGED at 50..51). -/
def MEMBERSHIP_TEETH_COL_AVAIL_WIDE_NARROW : Nat :=
  transferAvailV3WNarrow.traceWidth + wideAppendixSpan

/-- The crown AVAIL narrow wide host BEFORE the teeth-column width bump (mirror of
`transferMembershipAvailWideBase`, narrow base). -/
def transferMembershipAvailWideNarrowBase : EffectVmDescriptor2 :=
  wideAppend
    (withMembershipTeethPinsAt MEMBERSHIP_TEETH_COL_AVAIL_WIDE_NARROW
      (withDfaRcPinsAt AVAIL_WIDTH transferAvailV3WNarrow))
    TR_AVAIL_BB (TR_AVAIL_BB + 239)

/-- **`transferV3MembershipAvailWideNarrow`** — the narrow twin of the AVAIL crown wide transfer
member (`transferV3MembershipAvailWide`): the membership-teeth transfer rebuilt over the narrow-base
hardened availability face. -/
def transferV3MembershipAvailWideNarrow : EffectVmDescriptor2 :=
  { transferMembershipAvailWideNarrowBase with
    traceWidth := transferMembershipAvailWideNarrowBase.traceWidth + 2 }

theorem transferV3MembershipAvailWideNarrow_constraints :
    transferV3MembershipAvailWideNarrow.constraints
      = transferMembershipAvailWideNarrowBase.constraints := rfl

/-- Face-host constraint membership in the CROWN narrow avail wide member (mirror of
`availHost_mem_membershipAvailWide`, narrow host). -/
theorem availHost_mem_membershipAvailWideNarrow :
    ∀ c ∈ transferAvailV3WNarrow.constraints,
      isLegacyCommitPin1 TR_AVAIL_BB (TR_AVAIL_BB + 239) c = false →
      c ∈ transferV3MembershipAvailWideNarrow.constraints := by
  intro c hc hnp
  show c ∈ transferMembershipAvailWideNarrowBase.constraints
  exact wideAppend_mem_of_host _ TR_AVAIL_BB (TR_AVAIL_BB + 239) c
    (List.mem_append_left _ (List.mem_append_left _ hc)) hnp

/-- **`membershipAvailWideNarrow_row_v1`** — the CROWN narrow avail wide member forces the hardened
face's v1 denotation on every row (byte-identical conclusion to `membershipAvailWide_row_v1`). -/
theorem membershipAvailWideNarrow_row_v1 (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hf : Satisfied2FaithfulWideNarrow hash transferV3MembershipAvailWideNarrow
      minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash transferVmDescriptorAvail (envAt t i)
        (i == 0) (i + 1 == t.rows.length) :=
  wideEmbeddedNarrow_sound_v1 hash transferVmDescriptorAvail transferV3MembershipAvailWideNarrow
    TR_AVAIL_BB (TR_AVAIL_BB + 239) minit mfin maddrs t (by decide) transferAvail_clean
    availHost_mem_membershipAvailWideNarrow hf

#assert_axioms membershipAvailWideNarrow_row_v1

/-! ## §3 — the live-only TB transfer narrow twin. -/

/-- **`transferCapOpenTBAvailWideNarrow`** — the narrow twin of the AVAIL TB wide transfer member
(`transferCapOpenTBAvailWide`): the turn-identity-pinned cap-open transfer over the narrow-base
hardened face. -/
def transferCapOpenTBAvailWideNarrow : EffectVmDescriptor2 :=
  wideAppend
    (Dregg2.Circuit.Emit.CapOpenTurnPins.effCapOpenV3TB transferAvailV3WNarrow
      "dregg-effectvm-transfer-v1-avail-rot24-v3-capopen-eff-tb"
      Dregg2.Circuit.Emit.CapOpenEmit.EFF_TRANSFER)
    TR_AVAIL_BB (TR_AVAIL_BB + 239)

/-- Face-host constraint membership in the TB narrow avail wide member (mirror of
`availHost_mem_tbAvailWide`, narrow host). -/
theorem availHost_mem_tbAvailWideNarrow :
    ∀ c ∈ transferAvailV3WNarrow.constraints,
      isLegacyCommitPin1 TR_AVAIL_BB (TR_AVAIL_BB + 239) c = false →
      c ∈ transferCapOpenTBAvailWideNarrow.constraints := by
  intro c hc hnp
  exact wideAppend_mem_of_host _ TR_AVAIL_BB (TR_AVAIL_BB + 239) c
    (List.mem_append_left _ (List.mem_append_left _ hc)) hnp

/-- **`tbAvailWideNarrow_row_v1`** — the TB narrow avail wide member forces the hardened face's v1
denotation on every row (byte-identical conclusion to `tbAvailWide_row_v1`). -/
theorem tbAvailWideNarrow_row_v1 (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hf : Satisfied2FaithfulWideNarrow hash transferCapOpenTBAvailWideNarrow minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash transferVmDescriptorAvail (envAt t i)
        (i == 0) (i + 1 == t.rows.length) :=
  wideEmbeddedNarrow_sound_v1 hash transferVmDescriptorAvail transferCapOpenTBAvailWideNarrow
    TR_AVAIL_BB (TR_AVAIL_BB + 239) minit mfin maddrs t (by decide) transferAvail_clean
    availHost_mem_tbAvailWideNarrow hf

#assert_axioms tbAvailWideNarrow_row_v1

/-! ## §4 — the crown burn narrow twin. -/

/-- **`burnV3AvailWideNarrow`** — the narrow twin of the burn crown wide host (`burnV3AvailWide`):
the plain cohort wide member rebuilt over the narrow-base hardened burn face. -/
def burnV3AvailWideNarrow : EffectVmDescriptor2 :=
  wideAppend (withDfaRcPinsAt BU_AVAIL_BB burnAvailV3WNarrow) BU_AVAIL_BB (BU_AVAIL_BB + 239)

/-- Face-host constraint membership in the burn narrow avail wide member (mirror of
`availHost_mem_burnAvailWide`, narrow host). -/
theorem availHost_mem_burnAvailWideNarrow :
    ∀ c ∈ burnAvailV3WNarrow.constraints,
      isLegacyCommitPin1 BU_AVAIL_BB (BU_AVAIL_BB + 239) c = false →
      c ∈ burnV3AvailWideNarrow.constraints := by
  intro c hc hnp
  refine wideAppend_mem_of_host _ BU_AVAIL_BB (BU_AVAIL_BB + 239) c ?_ hnp
  rw [withDfaRcPinsAt_constraints]
  exact List.mem_append_left _ hc

/-- **`burnAvailWideNarrow_row_v1`** — the burn crown narrow avail wide member forces the hardened
burn face's v1 denotation on every row (byte-identical conclusion to `burnAvailWide_row_v1`). -/
theorem burnAvailWideNarrow_row_v1 (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hf : Satisfied2FaithfulWideNarrow hash burnV3AvailWideNarrow minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash Dregg2.Circuit.Emit.EffectVmEmitBurn.burnVmDescriptorAvail
        (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
  wideEmbeddedNarrow_sound_v1 hash
    Dregg2.Circuit.Emit.EffectVmEmitBurn.burnVmDescriptorAvail burnV3AvailWideNarrow
    BU_AVAIL_BB (BU_AVAIL_BB + 239) minit mfin maddrs t (by decide) burnAvail_clean
    availHost_mem_burnAvailWideNarrow hf

#assert_axioms burnAvailWideNarrow_row_v1

/-! ## §5 — the crown cap-open-EFF transfer narrow twin (the member underlying
`RotatedKernelRefinementCapOpenAvailWide`). -/

/-- **`transferCapOpenEffAvailWideNarrow`** — the narrow twin of the AVAIL cap-open-EFF wide transfer
member (`transferCapOpenEffAvailWide`): the selector-gated effect-general cap-open transfer over the
narrow-base hardened rotated face. -/
def transferCapOpenEffAvailWideNarrow : EffectVmDescriptor2 :=
  wideAppend
    (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.withSelectorGate
      Dregg2.Circuit.Emit.EffectVmEmit.sel.TRANSFER
      (Dregg2.Circuit.Emit.CapOpenEmit.effCapOpenV3 transferAvailV3WNarrow
        "dregg-effectvm-transfer-v1-avail-rot24-v3-capopen-eff"
        Dregg2.Circuit.Emit.CapOpenEmit.EFF_TRANSFER))
    TR_AVAIL_BB (TR_AVAIL_BB + 239)

/-- Face-host constraint membership in the EFF narrow avail wide member (mirror of
`availHost_mem_effAvailWide`, narrow host). -/
theorem availHost_mem_effAvailWideNarrow :
    ∀ c ∈ transferAvailV3WNarrow.constraints,
      isLegacyCommitPin1 TR_AVAIL_BB (TR_AVAIL_BB + 239) c = false →
      c ∈ transferCapOpenEffAvailWideNarrow.constraints := by
  intro c hc hnp
  exact wideAppend_mem_of_host _ TR_AVAIL_BB (TR_AVAIL_BB + 239) c
    (List.mem_append_left _ (List.mem_append_left _ hc)) hnp

/-- **`effAvailWideNarrow_row_v1`** — the EFF narrow avail wide member forces the hardened face's v1
denotation on every row (byte-identical conclusion to `effAvailWide_row_v1`). -/
theorem effAvailWideNarrow_row_v1 (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hf : Satisfied2FaithfulWideNarrow hash transferCapOpenEffAvailWideNarrow minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash transferVmDescriptorAvail (envAt t i)
        (i == 0) (i + 1 == t.rows.length) :=
  wideEmbeddedNarrow_sound_v1 hash transferVmDescriptorAvail transferCapOpenEffAvailWideNarrow
    TR_AVAIL_BB (TR_AVAIL_BB + 239) minit mfin maddrs t (by decide) transferAvail_clean
    availHost_mem_effAvailWideNarrow hf

#assert_axioms effAvailWideNarrow_row_v1

/-! ## §6 — the crown fee'd-transfer narrow twin (over the §0 narrow fee-pinned keystone). -/

/-- **`transferFeeAvailWideNarrow`** — the narrow twin of the FEE'D-transfer crown wide member
(`transferFeeAvailWide`): the narrow-base hardened fee wire member (rc pins ONLY, NO refuse)
wide-appended at the FEE avail face base. -/
def transferFeeAvailWideNarrow : EffectVmDescriptor2 :=
  wideAppend (withDfaRcPinsAt FEE_AVAIL_WIDTH transferFeeAvailV3WNarrow)
    FEE_AVAIL_BB (FEE_AVAIL_BB + 239)

/-- Face-host constraint membership in the fee narrow avail wide member (mirror of
`feeAvailHost_mem_feeAvailWide`, narrow host). -/
theorem feeAvailHost_mem_feeAvailWideNarrow :
    ∀ c ∈ transferFeeAvailV3WNarrow.constraints,
      isLegacyCommitPin1 FEE_AVAIL_BB (FEE_AVAIL_BB + 239) c = false →
      c ∈ transferFeeAvailWideNarrow.constraints := by
  intro c hc hnp
  refine wideAppend_mem_of_host _ FEE_AVAIL_BB (FEE_AVAIL_BB + 239) c ?_ hnp
  show c ∈ (withDfaRcPinsAt FEE_AVAIL_WIDTH transferFeeAvailV3WNarrow).constraints
  rw [withDfaRcPinsAt_constraints]
  exact List.mem_append_left _ hc

/-- **`feeAvailWideNarrow_row_v1`** — the fee narrow avail wide member forces the hardened fee face's
v1 denotation on every row (byte-identical conclusion to `feeAvailWide_row_v1`). -/
theorem feeAvailWideNarrow_row_v1 (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hf : Satisfied2FaithfulWideNarrow hash transferFeeAvailWideNarrow minit mfin maddrs t) :
    ∀ i, i < t.rows.length →
      satisfiedVm hash transferFeeVmDescriptorAvail (envAt t i)
        (i == 0) (i + 1 == t.rows.length) :=
  wideEmbeddedFeeNarrow_sound_v1 hash transferFeeVmDescriptorAvail transferFeeAvailWideNarrow
    FEE_AVAIL_BB (FEE_AVAIL_BB + 239) minit mfin maddrs t (by decide) transferFeeAvail_clean
    feeAvailHost_mem_feeAvailWideNarrow hf

#assert_axioms feeAvailHost_mem_feeAvailWideNarrow
#assert_axioms feeAvailWideNarrow_row_v1

/-! ## §7 — the per-member width-shrink WIN (machine-checked): each narrow twin's underlying face is
`7·(#hash sites)` columns narrower than the deployed wide face (`CHIP_OUT_LANES - 1 = 7` lane columns
per single-output hash site, dropped by the narrow bus). -/

-- transfer crown / TB / EFF share the transfer avail face:
#guard (v3OfFrozenWide transferVmDescriptorAvail).traceWidth
        - (v3OfFrozenWideNarrow transferVmDescriptorAvail).traceWidth
     == (CHIP_OUT_LANES - 1)
        * (rotateV3FrozenAuthority transferVmDescriptorAvail).hashSites.length
-- burn:
#guard (v3OfFrozenWide Dregg2.Circuit.Emit.EffectVmEmitBurn.burnVmDescriptorAvail).traceWidth
        - (v3OfFrozenWideNarrow Dregg2.Circuit.Emit.EffectVmEmitBurn.burnVmDescriptorAvail).traceWidth
     == (CHIP_OUT_LANES - 1)
        * (rotateV3FrozenAuthority
            Dregg2.Circuit.Emit.EffectVmEmitBurn.burnVmDescriptorAvail).hashSites.length
-- fee (fee-pinned graduation — the fee pin appends no site, so the gap is the same `7·(#sites)`):
#guard (v3OfFrozenFeeWide transferFeeVmDescriptorAvail).traceWidth
        - (v3OfFrozenFeeWideNarrow transferFeeVmDescriptorAvail).traceWidth
     == (CHIP_OUT_LANES - 1)
        * (rotateV3WithFeePin
            (rotateV3FrozenAuthority transferFeeVmDescriptorAvail)).hashSites.length
-- and each narrow twin's face is STRICTLY narrower than its deployed wide twin:
#guard (v3OfFrozenWideNarrow transferVmDescriptorAvail).traceWidth
     < (v3OfFrozenWide transferVmDescriptorAvail).traceWidth
#guard (v3OfFrozenWideNarrow Dregg2.Circuit.Emit.EffectVmEmitBurn.burnVmDescriptorAvail).traceWidth
     < (v3OfFrozenWide Dregg2.Circuit.Emit.EffectVmEmitBurn.burnVmDescriptorAvail).traceWidth
#guard (v3OfFrozenFeeWideNarrow transferFeeVmDescriptorAvail).traceWidth
     < (v3OfFrozenFeeWide transferFeeVmDescriptorAvail).traceWidth

end Dregg2.Circuit.Emit.AvailWideMembersNarrow
