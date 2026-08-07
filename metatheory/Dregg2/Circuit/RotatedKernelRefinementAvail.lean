/-
# Dregg2.Circuit.RotatedKernelRefinementAvail — transfer `guardAvail` DISCHARGED on the hardened
graduable-wide path (the DEBT-A availability forgery, closed in-proof end-to-end).

## What this module is

`RotatedKernelRefinement` refines the DEPLOYED rotated transfer (`transferV3 = v3OfFrozen
transferVmDescriptor`) and — after the DEBT-A mod-`p` migration — carries ⚠ AVAILABILITY
(`amt ≤ bal src a`) as the NAMED `rotatedEncodes.guardAvail` decode residual: an ORDER over an
un-range-checked amount limb is NOT preserved mod `p < 2³¹`, so the bare circuit admits the
underflow-wrap mint-from-nothing (`docs/FINDING-modp-wrap-forgery-audit.md`, forgery 1).

The HARDENED descriptor `transferVmDescriptorAvail` (§11.7 of `EffectVmEmitTransfer`) closes the
forgery IN-CIRCUIT: 15-bit borrow-limb decomposition + range checks + a no-final-borrow gate force
`amt ≤ before.bal_lo` and the EXACT ℤ move (`transferAvail_derives_availability`). What blocked it
from the refinement tower was GRADUATION: `graduable` demands every range tooth at 30 bits, and the
single-width lowering would bound a 15-bit limb only `< 2³⁰`, defeating the borrow proof. The §10
multi-width graduation (`graduableWide` / `graduateV1Wide`, `EffectVmEmitV2`) and its rotation lift
(`rotV3FrozenWide_sound_v1`, `EffectVmEmitRotationV3`) remove the block. THIS module rides them to
the kernel refinement:

  * **`transferV3Avail`** — the hardened rotated graduated descriptor
    (`v3OfFrozenWide transferVmDescriptorAvail`), the wide mirror of `transferV3`.
  * **`rotatedEncodesAvail`** — the hardened decode: `rotatedEncodes` WITHOUT `guardAvail`
    (availability is NO LONGER a residual) plus the debit row's field-canonicality envelope
    (`hdiCanon` — width-only, the deployed canonical-element invariant; NOT availability
    laundered in).
  * **`availability_and_exact_move_forced`** — THE DISCHARGE: a `Satisfied2` witness of
    `transferV3Avail` + the hardened decode FORCE `tr.amt ≤ pre.kernel.bal tr.src a` AND the
    EXACT ℤ debit `post.bal src a = pre.bal src a − tr.amt` (strictly stronger than the bare
    path's mod-`p` congruence `debit_forced`).
  * **`rotatedEncodesAvail.toEncodes`** — the bare decode RECOVERED with `guardAvail` PROVEN
    (circuit-forced), so every bare-path theorem consumes the hardened decode.
  * **`transfer_descriptorRefinesAvail`** — the full `BalanceMovementSpec` refinement on the
    hardened path, availability sourced FROM THE WITNESS, not from a decode leg.
  * **`descriptorRefinesAvail_rejects_overdebit`** — the tooth: ANY over-debit decode
    (`pre.bal src a < tr.amt`, the audit's forgery class) riding a satisfying hardened witness
    is UNSAT.

## The deployment step — DONE (GAP 1-6 VK epoch flip)

The live registry routes the HARDENED transfer member, not the bare `transferVmDescriptor`:
`EmitRotationV3.lean`'s `availOverride` (cited by NAME — it sat at `:119` when this was written and a
concurrent commit moved it to `:134`; `Dregg2.lean:1020` and `:1022` cite the post-move numbers, so a
reader comparing the two would otherwise see the tree contradict itself) maps the cohort key
`transferVmDescriptor2R24` → `Emit.AvailWireMembers.transferV3AvailWire` (the wire wrapper over
THIS module's `transferV3Avail`). The flip was materialized into the re-keyed VK epoch —
descriptor-JSON/FP + VK regen with the Rust assembly realizing the 15-bit range table (the
`transfer_avail_weld.rs` teeth); `Emit/EffectVmEmitTransfer.lean:224` records the gap "CLOSED AND
DEPLOYED" and `:235` "the flip is DONE". Production transfer availability is therefore
circuit-FORCED, and `availOf` is discharged all the way to the apex
(`ClosureFinalAvail.lean:162-164`). This module is the refinement proof that the deployed flip
CLOSES the forgery; the bare-path `rotatedEncodes.guardAvail` residual survives only in
`RotatedKernelRefinement`, which nothing deployed reads. The in-library `v3RegistryBare` entry is
still the bare def — the wire coincides with it through `EmitRotationV3`'s override, and re-keying
that list member-for-member is the one named follow-up (`Emit/AvailWireMembers.lean` §"What
consumes it").

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. NEW file; imports
are read-only.
-/
import Dregg2.Circuit.RotatedKernelRefinement
import Dregg2.Circuit.Emit.GraduateWideNarrow

namespace Dregg2.Circuit.RotatedKernelRefinementAvail

open Dregg2.Circuit.Emit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitV2
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
open Dregg2.Circuit.Spec.BalanceMovement
open Dregg2.Circuit.RotatedKernelRefinement
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false

/-! ## §0 — the hardened rotated transfer descriptor. -/

/-- The HARDENED rotated graduated transfer descriptor: the §11.7 availability-weld descriptor
lifted through the V3 rotation + authority freeze, graduated MULTI-WIDTH (its 15-bit borrow-limb
teeth lower into the 15-bit table). The wide mirror of `transferV3`. -/
def transferV3Avail : EffectVmDescriptor2 :=
  v3OfFrozenWide EffectVmEmitTransfer.transferVmDescriptorAvail

/-- The hardened descriptor is wide-graduable — the decidable side condition
`rotV3FrozenWide_sound_v1` needs (its 15-bit teeth are exactly why `graduable` refuses it and
`graduableWide` exists). -/
theorem transferAvail_graduableWide :
    graduableWide EffectVmEmitTransfer.transferVmDescriptorAvail = true := by decide

-- The rotated hardened descriptor publishes the same 4 appended commit pins as every cohort
-- member (42 + 4), and stays wide-graduable through the rotation + freeze.
#guard (rotateV3FrozenAuthority EffectVmEmitTransfer.transferVmDescriptorAvail).piCount == 39
#guard graduableWide (rotateV3FrozenAuthority EffectVmEmitTransfer.transferVmDescriptorAvail)

/-! ## §1 — the wide table side + the per-row decode chain. -/

/-- The chip / PER-WIDTH range table faithfulness the wide rotated denotation carries — the
`RotTableSide` shape with the multi-width range pins (each allowed width's table is its genuine
limb table; the `b = BAL_LIMB_BITS` instance IS the deployed `.range` pin, `rangeTidW_bal`). The
15-bit pin is the table the availability-weld assembly realizes at the flip (the Rust weld's
`RangeSpec { bits: 15 }` teeth). -/
structure RotTableSideW (permOut : List ℤ → List ℤ) (hash : List ℤ → ℤ) (t : VmTrace) : Prop where
  /-- the genuine permutation exposes exactly `CHIP_OUT_LANES` output lanes. -/
  permWidth : ∀ ins, (permOut ins).length = CHIP_OUT_LANES
  /-- the v1 digest IS lane 0 of the genuine permutation (the deployed squeeze). -/
  chipHashIsLane0 : ∀ ins, hash ins = (permOut ins).headD 0
  /-- THE CHIP-TABLE-FAITHFUL CONJUNCT (`Ir2Air::Chip`), bound to `t.tf .poseidon2`. -/
  chipTableFaithful : ChipTableSoundN permOut (t.tf .poseidon2)
  /-- THE PER-WIDTH RANGE-FAITHFUL CONJUNCT: every allowed width's table is genuine. -/
  rangesWide : ∀ b ∈ WIDE_RANGE_WIDTHS, t.tf (rangeTidW b) = rangeRows b

/-- The wide table side projects to the single-width `RotTableSide` (the 30-bit pin is the
`b = BAL_LIMB_BITS` instance) — every bare-path rung stays reachable. -/
theorem RotTableSideW.toRotTableSide {permOut : List ℤ → List ℤ} {hash : List ℤ → ℤ}
    {t : VmTrace} (h : RotTableSideW permOut hash t) : RotTableSide permOut hash t :=
  { permWidth := h.permWidth
    chipHashIsLane0 := h.chipHashIsLane0
    chipTableFaithful := h.chipTableFaithful
    range := rangeTablesWide_range h.rangesWide }

/-- Assemble the WIDE faithful object from the wide table side + a `Satisfied2` witness (the
wide mirror of `RotTableSide.toFaithful`) — how this module threads `Satisfied2FaithfulWide`
into `rotV3FrozenWide_sound_v1` with no free lever. -/
theorem RotTableSideW.toFaithfulW {permOut : List ℤ → List ℤ} {hash : List ℤ → ℤ}
    {d : EffectVmDescriptor2} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash d minit mfin maddrs t) :
    Satisfied2FaithfulWide permOut hash d minit mfin maddrs t :=
  { hsat with
    permWidth := hside.permWidth
    chipHashIsLane0 := hside.chipHashIsLane0
    chipTableFaithful := hside.chipTableFaithful
    rangeTablesWideFaithful := hside.rangesWide }

/-! ## §1N — the NARROW-base table side (the tuple-narrowing bus) + its faithful assembler.

The narrow mirror of `RotTableSideW`: on the 18-wide narrow chip bus, the genuine rows encode
`hash ins` DIRECTLY as out0 (`ChipTableSoundNarrow hash`), so there is NO `permOut` indirection to
carry — the structure holds the narrow chip soundness as a field plus the per-width range pins. It
is the single missing witness-provider that lets the whole availability refinement tower consume a
`Satisfied2FaithfulWideNarrow` (the narrow-graduated members of `GraduateWideNarrow` /
`AvailWideMembersNarrow`) instead of the 25-wide `Satisfied2FaithfulWide`. -/

/-- The NARROW-base table side — the narrow mirror of `RotTableSideW`. Its chip field is
`ChipTableSoundNarrow hash (t.tf poseidon2narrow)` (the reserved `.custom 3` narrow bus, no
`permOut` / lane indirection); the per-width range pins are carried verbatim. -/
structure RotTableSideNarrow (hash : List ℤ → ℤ) (t : VmTrace) : Prop where
  /-- THE NARROW CHIP-TABLE-FAITHFUL CONJUNCT, bound to `t.tf poseidon2narrow`. -/
  chipTableFaithfulNarrow : ChipTableSoundNarrow hash (t.tf poseidon2narrow)
  /-- THE PER-WIDTH RANGE-FAITHFUL CONJUNCT: every allowed width's table is its genuine limb table. -/
  rangesWide : ∀ b ∈ WIDE_RANGE_WIDTHS, t.tf (rangeTidW b) = rangeRows b

/-- Assemble the NARROW faithful object from the narrow table side + a `Satisfied2` witness (the
narrow mirror of `RotTableSideW.toFaithfulW`) — how the narrowed tower threads
`Satisfied2FaithfulWideNarrow` into `rotV3FrozenWideNarrow_sound_v1` / `wideEmbeddedNarrow_sound_v1`
with no free lever. Fills EXACTLY the narrow struct's two extra fields. -/
theorem RotTableSideNarrow.toFaithfulWNarrow {hash : List ℤ → ℤ}
    {d : EffectVmDescriptor2} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideNarrow hash t)
    (hsat : Satisfied2 hash d minit mfin maddrs t) :
    Satisfied2FaithfulWideNarrow hash d minit mfin maddrs t :=
  { hsat with
    chipTableFaithfulNarrow := hside.chipTableFaithfulNarrow
    rangeTablesWideFaithful := hside.rangesWide }

#assert_axioms RotTableSideNarrow.toFaithfulWNarrow

/-- The hardened descriptor's per-row v1 denotation IMPLIES the bare descriptor's: the weld is
purely ADDITIVE (constraints appended, ranges appended, hash sites verbatim), so every bare
constraint/site/range fact survives. This is how the hardened path re-derives the whole bare
per-cell chain (`CellTransferSpec`) beside the new availability forcing. -/
theorem satisfiedVmAvail_bare (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst isLast : Bool)
    (h : satisfiedVm hash EffectVmEmitTransfer.transferVmDescriptorAvail env isFirst isLast) :
    satisfiedVm hash EffectVmEmitTransfer.transferVmDescriptor env isFirst isLast := by
  obtain ⟨hc, hs, hr⟩ := h
  exact ⟨fun c hc' => hc c (List.mem_append_left _ hc'), hs,
    fun r hr' => hr r (List.mem_append_left _ hr')⟩

/-- **The hardened per-row v1 denotation** — a `Satisfied2` witness of `transferV3Avail` yields,
on every row, the FULL v1 denotation of the hardened descriptor (weld gates + 15-bit teeth
INCLUDED — this is what the single-width bridge could not deliver). -/
theorem rotatedAvail_row_v1 (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferV3Avail minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    satisfiedVm hash EffectVmEmitTransfer.transferVmDescriptorAvail
      (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
  rotV3FrozenWide_sound_v1 permOut hash EffectVmEmitTransfer.transferVmDescriptorAvail
    minit mfin maddrs t transferAvail_graduableWide (hside.toFaithfulW hsat) i hi

/-- The per-row transfer GATES hold at an ACTIVE row (the hardened mirror of
`rotated_row_gates`). -/
theorem rotatedAvail_row_gates (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferV3Avail minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length) :
    ∀ c ∈ EffectVmEmitTransfer.transferRowGates,
      c.holdsVm (envAt t i) false false := by
  have hv1 : satisfiedVm hash EffectVmEmitTransfer.transferVmDescriptor
      (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
    satisfiedVmAvail_bare hash (envAt t i) _ _ (rotatedAvail_row_v1 hash hside hsat i hi)
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  intro c hc
  have hmem : c ∈ EffectVmEmitTransfer.transferVmDescriptor.constraints := by
    unfold EffectVmEmitTransfer.transferVmDescriptor
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
  have hh := hv1.1 c hmem
  rw [hlastf] at hh
  -- transferRowGates are all `.gate _`; at `isLast = false` `holdsVm` IS the body equation.
  unfold EffectVmEmitTransfer.transferRowGates EffectVmEmitTransfer.gFieldPassAll at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨j, hj, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using hh

/-- Hardened witness ⟹ per-cell value-block spec on row `i` (the mirror of
`rotated_row_cellSpec`): the bare per-cell chain survives the weld verbatim. -/
theorem rotatedAvail_row_cellSpec (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferV3Avail minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (pre post : CellState) (p : TransferParams)
    (henc : RowEncodes (envAt t i) pre p post)
    (hrow : IsTransferRow (envAt t i)) :
    CellTransferSpec pre p post := by
  have hint : TransferRowIntent (envAt t i) :=
    (EffectVmEmitTransfer.transferVm_faithful (envAt t i) hrow).mp
      (rotatedAvail_row_gates hash hside hsat i hi hnotlast)
  exact intent_to_cellSpec (envAt t i) pre post p henc hint

/-! ## §2 — `rotatedEncodesAvail`: the hardened decode (NO `guardAvail` residual).

The field-for-field mirror of `rotatedEncodes` with TWO deltas:

  * **`guardAvail` is GONE** — availability is derived from the witness
    (`availability_and_exact_move_forced`), no longer carried as an admissibility leg;
  * **`hdiCanon`** — the debit row's field-canonicality envelope (`0 ≤ loc c < p` for every
    column), the DEPLOYED canonical-element invariant the verifier's field decoding supplies
    (the same premise `rotV3_binds_published` consumes and the audit's repair pattern names).
    WIDTH-ONLY — it says nothing about order, so it is NOT availability laundered in
    (`transferAvail_derives_availability` derives the order from the borrow gates). -/

/-- The hardened decode: a satisfying `transferV3Avail` witness's two designated boundary rows
tied onto the kernel ledger, availability NOT assumed. -/
structure rotatedEncodesAvail (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId) : Type where
  -- the two designated rows + their decodes
  di : Nat
  ci : Nat
  hdi : di < t.rows.length
  hci : ci < t.rows.length
  -- the designated effect rows are ACTIVE (transition) rows, not the wrap/pad last row.
  hdiNotLast : di + 1 ≠ t.rows.length
  hciNotLast : ci + 1 ≠ t.rows.length
  srcPre : CellState
  srcPost : CellState
  dstPre : CellState
  dstPost : CellState
  srcParams : TransferParams
  dstParams : TransferParams
  hdiRow : IsTransferRow (envAt t di)
  hciRow : IsTransferRow (envAt t ci)
  hdiEnc : RowEncodes (envAt t di) srcPre srcParams srcPost
  hciEnc : RowEncodes (envAt t ci) dstPre dstParams dstPost
  -- THE CANONICALITY ENVELOPE (deployed invariant, width-only — see the section header).
  hdiCanon : ∀ c, 0 ≤ (envAt t di).loc c ∧ (envAt t di).loc c < 2013265921
  -- the debit row debits, the credit row credits; both carry the turn's amount.
  hdiDir : srcParams.direction = 1
  hciDir : dstParams.direction = 0
  hdiAmt : srcParams.amount = tr.amt
  hciAmt : dstParams.amount = tr.amt
  -- the decoded limbs ARE the kernel ledger at the moved coordinates.
  hsrcPre  : srcPre.balLo  = pre.kernel.bal tr.src a
  hdstPre  : dstPre.balLo  = pre.kernel.bal tr.dst a
  hsrcPost : srcPost.balLo = post.kernel.bal tr.src a
  hdstPost : dstPost.balLo = post.kernel.bal tr.dst a
  -- the ledger FRAME (cross-cell residual, as on the bare path).
  hledgerFrame : post.kernel.bal
    = recTransferBal pre.kernel.bal tr.src tr.dst a tr.amt
  -- the residual admissibility legs (kernel side-tables, not in the value block). NOTE: NO
  -- guardAvail — availability is CIRCUIT-FORCED on this path.
  guardAuth : authorizedB pre.kernel.caps tr = true
  guardNonNeg : 0 ≤ tr.amt
  guardDistinct : tr.src ≠ tr.dst
  guardLiveSrc : tr.src ∈ pre.kernel.accounts
  guardLiveDst : tr.dst ∈ pre.kernel.accounts
  guardSrcLifecycleLive : cellLifecycleLive pre.kernel tr.src = true
  guardAccepts : acceptsEffects pre.kernel tr.dst = true
  -- the 16 non-`bal` kernel frame fields + the receipt-log advance.
  frAccounts : post.kernel.accounts = pre.kernel.accounts
  frCell : post.kernel.cell = pre.kernel.cell
  frCaps : post.kernel.caps = pre.kernel.caps
  frNullifiers : post.kernel.nullifiers = pre.kernel.nullifiers
  frRevoked : post.kernel.revoked = pre.kernel.revoked
  frCommitments : post.kernel.commitments = pre.kernel.commitments
  frSlotCaveats : post.kernel.slotCaveats = pre.kernel.slotCaveats
  frFactories : post.kernel.factories = pre.kernel.factories
  frLifecycle : post.kernel.lifecycle = pre.kernel.lifecycle
  frDeathCert : post.kernel.deathCert = pre.kernel.deathCert
  frDelegate : post.kernel.delegate = pre.kernel.delegate
  frDelegations : post.kernel.delegations = pre.kernel.delegations
  frDelegationEpoch : post.kernel.delegationEpoch = pre.kernel.delegationEpoch
  frDelegationEpochAt : post.kernel.delegationEpochAt = pre.kernel.delegationEpochAt
  frHeaps : post.kernel.heaps = pre.kernel.heaps
  frNullifierRoot : post.kernel.nullifierRoot = pre.kernel.nullifierRoot
  frRevokedRoot : post.kernel.revokedRoot = pre.kernel.revokedRoot
  frCommitmentsRoot : post.kernel.commitmentsRoot = pre.kernel.commitmentsRoot
  logAdv : post.log = tr :: pre.log

/-! ## §3 — THE DISCHARGE: availability + the EXACT ℤ debit are FORCED by the hardened witness. -/

/-- **`availability_and_exact_move_forced` — `guardAvail` DISCHARGED (and upgraded).** A
`Satisfied2` witness of the hardened rotated transfer + the hardened decode FORCE, on the kernel
ledger: `tr.amt ≤ pre.bal src a` (AVAILABILITY — the DEBT-A forgery class closed) AND the EXACT ℤ
debit `post.bal src a = pre.bal src a − tr.amt` (STRICTLY STRONGER than the bare path's mod-`p`
`debit_forced`: the borrow chain makes the subtraction exact over ℤ, no wrap witness exists). The
chain: rotated accept → (`rotV3FrozenWide_sound_v1`) per-row hardened `satisfiedVm` →
(`transferAvail_derives_availability_row`, at the row's own flags) the borrow-forced order + move
→ (`RowEncodes` + the decode's ledger ties) the kernel statement. -/
theorem availability_and_exact_move_forced (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferV3Avail minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a) :
    tr.amt ≤ pre.kernel.bal tr.src a
    ∧ post.kernel.bal tr.src a = pre.kernel.bal tr.src a - tr.amt := by
  have hv1 := rotatedAvail_row_v1 hash hside hsat henc.di henc.hdi
  have hlastf : (henc.di + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact henc.hdiNotLast
  rw [hlastf] at hv1
  -- decode the debit row's param/state columns
  obtain ⟨hbLo, _, _, _, _, _, _, hAmt, hDir, hsaLo, _⟩ := henc.hdiEnc
  have hdir1 : (envAt t henc.di).loc (prmCol param.DIRECTION) = 1 := by
    rw [hDir, henc.hdiDir]
  have h := transferAvail_derives_availability_row hash (envAt t henc.di) (henc.di == 0)
    henc.hdiCanon hv1 hdir1
  rw [hAmt, henc.hdiAmt, hbLo, henc.hsrcPre, hsaLo, henc.hsrcPost] at h
  exact h

/-- Availability alone (`guardAvail`, proven). -/
theorem availability_forced (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferV3Avail minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a) :
    tr.amt ≤ pre.kernel.bal tr.src a :=
  (availability_and_exact_move_forced hash hside hsat pre post tr a henc).1

/-- The EXACT ℤ debit alone (the mod-`p` `debit_forced` upgraded to an ℤ equality). -/
theorem debit_exact_forced (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferV3Avail minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a) :
    post.kernel.bal tr.src a = pre.kernel.bal tr.src a - tr.amt :=
  (availability_and_exact_move_forced hash hside hsat pre post tr a henc).2

/-- The credit row's mod-`p` movement, retained on the hardened path (the mirror of
`credit_forced` — the credit leg's own exactness upgrade is `transferAvail_credit_no_overflow`,
consumable the same way once a credit-row canonicality envelope is threaded; the mod-`p` form
suffices for the refinement's ledger frame check). -/
theorem credit_forcedAvail (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferV3Avail minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a) :
    post.kernel.bal tr.dst a ≡ pre.kernel.bal tr.dst a + tr.amt [ZMOD 2013265921] := by
  have hspec : CellTransferSpec henc.dstPre henc.dstParams henc.dstPost :=
    rotatedAvail_row_cellSpec hash hside hsat henc.ci henc.hci henc.hciNotLast henc.dstPre
      henc.dstPost henc.dstParams henc.hciEnc henc.hciRow
  obtain ⟨_, hmove, _, _, _, _, _⟩ := hspec
  have hsm : signedMove henc.dstParams = henc.dstParams.amount := by
    unfold signedMove; rw [henc.hciDir]; ring
  rwa [hsm, henc.hciAmt, henc.hdstPost, henc.hdstPre] at hmove

/-! ## §4 — the bare decode RECOVERED (guardAvail proven), and the full refinement. -/

/-- **`rotatedEncodesAvail.toEncodes` — the hardened decode yields the bare decode with
`guardAvail` PROVEN.** Every `rotatedEncodes`-consuming theorem (the §4 conservation teeth, the
downstream completeness/closure consumers) applies to a hardened decode through this, with
availability circuit-forced instead of assumed. -/
def rotatedEncodesAvail.toEncodes (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {pre post : RecChainedState} {tr : Turn} {a : AssetId}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferV3Avail minit mfin maddrs t)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a) :
    rotatedEncodes hash minit mfin maddrs t pre post tr a :=
  { di := henc.di, ci := henc.ci, hdi := henc.hdi, hci := henc.hci
    hdiNotLast := henc.hdiNotLast, hciNotLast := henc.hciNotLast
    srcPre := henc.srcPre, srcPost := henc.srcPost
    dstPre := henc.dstPre, dstPost := henc.dstPost
    srcParams := henc.srcParams, dstParams := henc.dstParams
    hdiRow := henc.hdiRow, hciRow := henc.hciRow
    hdiEnc := henc.hdiEnc, hciEnc := henc.hciEnc
    hdiDir := henc.hdiDir, hciDir := henc.hciDir
    hdiAmt := henc.hdiAmt, hciAmt := henc.hciAmt
    hsrcPre := henc.hsrcPre, hdstPre := henc.hdstPre
    hsrcPost := henc.hsrcPost, hdstPost := henc.hdstPost
    hledgerFrame := henc.hledgerFrame
    guardAuth := henc.guardAuth
    guardNonNeg := henc.guardNonNeg
    -- THE DISCHARGE: availability from the WITNESS, not a residual.
    guardAvail := availability_forced hash hside hsat pre post tr a henc
    guardDistinct := henc.guardDistinct
    guardLiveSrc := henc.guardLiveSrc, guardLiveDst := henc.guardLiveDst
    guardSrcLifecycleLive := henc.guardSrcLifecycleLive
    guardAccepts := henc.guardAccepts
    frAccounts := henc.frAccounts, frCell := henc.frCell, frCaps := henc.frCaps
    frNullifiers := henc.frNullifiers, frRevoked := henc.frRevoked
    frCommitments := henc.frCommitments, frSlotCaveats := henc.frSlotCaveats
    frFactories := henc.frFactories, frLifecycle := henc.frLifecycle
    frDeathCert := henc.frDeathCert, frDelegate := henc.frDelegate
    frDelegations := henc.frDelegations, frDelegationEpoch := henc.frDelegationEpoch
    frDelegationEpochAt := henc.frDelegationEpochAt, frHeaps := henc.frHeaps
    frNullifierRoot := henc.frNullifierRoot, frRevokedRoot := henc.frRevokedRoot
    frCommitmentsRoot := henc.frCommitmentsRoot
    logAdv := henc.logAdv }

/-- **`transfer_descriptorRefinesAvail` — THE HARDENED REFINEMENT.** Satisfying the hardened
rotated transfer descriptor (`Satisfied2 hash transferV3Avail …`, wide table side) together with
the hardened decode forces the KERNEL's balance-movement step — with the AVAILABILITY guard
sourced FROM THE WITNESS (`availability_forced`), no `guardAvail` residual anywhere. The bare
path's honest gap note (`⚠⚠ AVAILABILITY IS NOT CIRCUIT-FORCED`, `RotatedKernelRefinement` §3)
is exactly what this theorem closes on the hardened path. -/
theorem transfer_descriptorRefinesAvail (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferV3Avail minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a) :
    BalanceMovementSpec pre tr a post := by
  -- the bare decode with `guardAvail` PROVEN, then the decode-only assembly (the same 21 legs
  -- `transfer_descriptorRefines` reads — its proof consumes ONLY the decode).
  have henc' := rotatedEncodesAvail.toEncodes hash hside hsat henc
  exact ⟨⟨henc'.guardAuth, henc'.guardNonNeg, henc'.guardAvail,
      henc'.guardDistinct, henc'.guardLiveSrc, henc'.guardLiveDst,
      henc'.guardSrcLifecycleLive, henc'.guardAccepts⟩,
    henc'.hledgerFrame, henc'.logAdv,
    henc'.frAccounts, henc'.frCell, henc'.frCaps, henc'.frNullifiers, henc'.frRevoked,
    henc'.frCommitments, henc'.frSlotCaveats, henc'.frFactories, henc'.frLifecycle,
    henc'.frDeathCert, henc'.frDelegate, henc'.frDelegations, henc'.frDelegationEpoch,
    henc'.frDelegationEpochAt, henc'.frHeaps, henc'.frNullifierRoot, henc'.frRevokedRoot,
    henc'.frCommitmentsRoot⟩

/-- The hardened refinement, stated against `fullActionStep` directly (the `.balanceA` arm). -/
theorem transfer_descriptorRefinesAvail_fullActionStep (hash : List ℤ → ℤ)
    {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferV3Avail minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a) :
    Dregg2.Circuit.ActionDispatch.fullActionStep pre (.balanceA tr a) post := by
  show BalanceMovementSpec pre tr a post
  exact transfer_descriptorRefinesAvail hash hside hsat pre post tr a henc

/-! ## §5 — THE TOOTH: the forgery class is UNSAT on the hardened path. -/

/-- **`descriptorRefinesAvail_rejects_overdebit`** — ANY over-debit decode (`pre.bal src a <
tr.amt` — the audit's mint-from-nothing class, e.g. `pre.bal = 0, amt = 10⁹`) riding a satisfying
hardened witness is UNSAT: the borrow chain forces `tr.amt ≤ pre.bal src a`, so the assumption is
`False`. The bare path ADMITS this witness (`⚠⚠ AVAILABILITY IS NOT CIRCUIT-FORCED`); the
hardened path REFUSES it — the forgery is closable by the registry flip. -/
theorem descriptorRefinesAvail_rejects_overdebit (hash : List ℤ → ℤ)
    {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferV3Avail minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a)
    (hforge : pre.kernel.bal tr.src a < tr.amt) : False := by
  have h := availability_forced hash hside hsat pre post tr a henc
  omega

/-- The audit's CONCRETE forgery witness (`pre.bal src a = 0`, `tr.amt = 10⁹`) is UNSAT on the
hardened path — the exact numbers of `docs/FINDING-modp-wrap-forgery-audit.md` forgery 1. -/
theorem descriptorRefinesAvail_audit_forgery_unsat (hash : List ℤ → ℤ)
    {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash transferV3Avail minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (henc : rotatedEncodesAvail hash minit mfin maddrs t pre post tr a)
    (hbal : pre.kernel.bal tr.src a = 0) (hamt : tr.amt = 1000000000) : False := by
  refine descriptorRefinesAvail_rejects_overdebit hash hside hsat pre post tr a henc ?_
  omega

/-! ## §6 — Axiom-hygiene tripwires. -/

#assert_axioms transferAvail_graduableWide
#assert_axioms RotTableSideW.toRotTableSide
#assert_axioms RotTableSideW.toFaithfulW
#assert_axioms satisfiedVmAvail_bare
#assert_axioms rotatedAvail_row_v1
#assert_axioms rotatedAvail_row_gates
#assert_axioms rotatedAvail_row_cellSpec
#assert_axioms availability_and_exact_move_forced
#assert_axioms availability_forced
#assert_axioms debit_exact_forced
#assert_axioms credit_forcedAvail
#assert_axioms transfer_descriptorRefinesAvail
#assert_axioms transfer_descriptorRefinesAvail_fullActionStep
#assert_axioms descriptorRefinesAvail_rejects_overdebit
#assert_axioms descriptorRefinesAvail_audit_forgery_unsat

end Dregg2.Circuit.RotatedKernelRefinementAvail
