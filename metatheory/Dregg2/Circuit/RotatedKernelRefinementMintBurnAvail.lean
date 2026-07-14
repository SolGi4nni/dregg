/-
# Dregg2.Circuit.RotatedKernelRefinementMintBurnAvail — burn `guardAvail` DISCHARGED on the hardened
graduable-wide path (the DEBT-A well-supply-inflation forgery, closed in-proof end-to-end).

## What this module is

`RotatedKernelRefinementMintBurn` refines the DEPLOYED rotated burn (`burnV3 = v3OfFrozen
burnVmDescriptor`) and — after the DEBT-A mod-`p` migration — carries ⚠ BURN AVAILABILITY
(`amt ≤ bal cell a`) as the NAMED `rotatedEncodesBurn.guardAvail` decode residual: an ORDER over the
un-range-checked `BURN_AMOUNT_LO` is NOT preserved mod `p < 2³¹`, so the bare circuit admits the
underflow-wrap over-burn (`docs/FINDING-modp-wrap-forgery-audit.md`, forgery 2) — and burn's ledger
frame CREDITS the well `(a,a)` by the forged amount, so the over-burn INFLATES WELL SUPPLY: a
mint-from-nothing, STRICTLY WORSE than the transfer twin.

The HARDENED descriptor `burnVmDescriptorAvail` (§8¾ of `EffectVmEmitBurn`) closes the forgery
IN-CIRCUIT: 15-bit borrow-limb decomposition + range checks (including, crucially, the previously
UNRANGED burn amount) + a no-final-borrow gate force `amt ≤ before.bal_lo` and the EXACT ℤ debit
(`burnAvail_derives_availability`). The §10 multi-width graduation (`graduableWide` /
`graduateV1Wide`, `EffectVmEmitV2`) and its rotation lift (`rotV3FrozenWide_sound_v1`,
`EffectVmEmitRotationV3`) carry the 15-bit teeth through the rotation tower — the same enablers the
transfer discharge (`RotatedKernelRefinementAvail`, THE TEMPLATE this module mirrors) rides. Here:

  * **`burnV3Avail`** — the hardened rotated graduated burn descriptor
    (`v3OfFrozenWide burnVmDescriptorAvail`), the wide mirror of `burnV3`.
  * **`rotatedEncodesBurnAvail`** — the hardened decode: `rotatedEncodesBurn` WITHOUT `guardAvail`
    (availability is NO LONGER a residual) plus the debit row's field-canonicality envelope
    (`hdiCanon` — width-only, the deployed canonical-element invariant; NOT availability
    laundered in).
  * **`burn_availability_and_exact_move_forced`** — THE DISCHARGE: a `Satisfied2` witness of
    `burnV3Avail` + the hardened decode FORCE `amt ≤ pre.kernel.bal cell a` AND the EXACT ℤ debit
    `post.bal cell a = pre.bal cell a − amt` (strictly stronger than the bare path's mod-`p`
    congruence `burn_debit_forced`).
  * **`rotatedEncodesBurnAvail.toEncodes`** — the bare decode RECOVERED with `guardAvail` PROVEN
    (circuit-forced), so every bare-path burn theorem consumes the hardened decode.
  * **`burn_descriptorRefinesAvail`** — the full `Spec.SupplyDestruction.BurnSpec` refinement on
    the hardened path, availability sourced FROM THE WITNESS, not from a decode leg.
  * **`burn_descriptorRefinesAvail_rejects_overburn`** — the tooth: ANY over-burn decode
    (`pre.bal cell a < amt`, the audit's well-supply-inflation class) riding a satisfying hardened
    witness is UNSAT.

## The deployment step — DONE (GAP 1-6 VK epoch flip)

The live registry now routes the HARDENED burn avail member (`Emit.AvailWireMembers`, the
`v3OfFrozenWide burnVmDescriptorAvail` face), NOT the bare `burnVmDescriptor` (`burnVmDescriptor2R24`).
The flip was materialized into the re-keyed VK epoch — descriptor-JSON/FP + VK regen with the Rust
assembly realizing the 15-bit range table (commits aa282f8c0 Rust half → 1e12d8886 authorized regen →
764225f0c producer reconcile → 72469afd0 "deployed VK IS vkOfRegistry RfixAvail"). Production burn
availability is now circuit-FORCED (the well-supply-inflation forgery is UNSAT on the deployed wire);
this module is the refinement proof that the deployed flip CLOSES the forgery. (The distinct WIDE /
welded-registry member — `RotatedKernelRefinementMintBurnAvailWide` — is the light-client-attestation
extension and remains a separate staged track.)

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. NEW file; the sole
enabler edit is the `burnAvail_derives_availability_row` flag generalization (statement-preserving;
the fixed-flag original is kept as a corollary).
-/
import Dregg2.Circuit.RotatedKernelRefinementAvail
import Dregg2.Circuit.RotatedKernelRefinementMintBurn

namespace Dregg2.Circuit.RotatedKernelRefinementMintBurnAvail

open Dregg2.Circuit.Emit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitV2
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.RotatedKernelRefinementAvail (RotTableSideW)
open Dregg2.Circuit.RotatedKernelRefinementMintBurn
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §0 — the hardened rotated burn descriptor. -/

/-- The HARDENED rotated graduated burn descriptor: the §8¾ availability-weld descriptor lifted
through the V3 rotation + authority freeze, graduated MULTI-WIDTH (its 15-bit borrow-limb teeth
lower into the 15-bit table). The wide mirror of `burnV3`. -/
def burnV3Avail : EffectVmDescriptor2 :=
  v3OfFrozenWide EffectVmEmitBurn.burnVmDescriptorAvail

/-- The hardened burn descriptor is wide-graduable — the decidable side condition
`rotV3FrozenWide_sound_v1` needs (its 15-bit teeth are exactly why `graduable` refuses it and
`graduableWide` exists). -/
theorem burnAvail_graduableWide :
    graduableWide EffectVmEmitBurn.burnVmDescriptorAvail = true := by decide

-- The rotated hardened descriptor publishes the same 4 appended commit pins as every cohort
-- member (42 + 4), and stays wide-graduable through the rotation + freeze.
#guard (rotateV3FrozenAuthority EffectVmEmitBurn.burnVmDescriptorAvail).piCount == 46
#guard graduableWide (rotateV3FrozenAuthority EffectVmEmitBurn.burnVmDescriptorAvail)

/-! ## §1 — the wide table side + the per-row decode chain.

The wide table side is the TRANSFER template's `RotTableSideW` (imported, not re-defined): the
multi-width range pins are shared cohort-wide — the 15-bit pin the burn weld's limbs lower into is
the SAME table the transfer/vault welds realize at the flip. -/

/-- The hardened burn descriptor's per-row v1 denotation IMPLIES the bare descriptor's: the weld is
purely ADDITIVE (constraints appended, ranges appended, hash sites verbatim), so every bare
constraint/site/range fact survives. This is how the hardened path re-derives the whole bare
per-cell chain (`CellBurnSpec`) beside the new availability forcing. -/
theorem satisfiedVmBurnAvail_bare (hash : List ℤ → ℤ) (env : VmRowEnv) (isFirst isLast : Bool)
    (h : satisfiedVm hash EffectVmEmitBurn.burnVmDescriptorAvail env isFirst isLast) :
    satisfiedVm hash EffectVmEmitBurn.burnVmDescriptor env isFirst isLast := by
  obtain ⟨hc, hs, hr⟩ := h
  exact ⟨fun c hc' => hc c (List.mem_append_left _ hc'), hs,
    fun r hr' => hr r (List.mem_append_left _ hr')⟩

/-- **The hardened per-row v1 denotation** — a `Satisfied2` witness of `burnV3Avail` yields, on
every row, the FULL v1 denotation of the hardened descriptor (weld gates + 15-bit teeth INCLUDED —
this is what the single-width bridge could not deliver). -/
theorem rotatedBurnAvail_row_v1 (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash burnV3Avail minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) :
    satisfiedVm hash EffectVmEmitBurn.burnVmDescriptorAvail
      (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
  rotV3FrozenWide_sound_v1 permOut hash EffectVmEmitBurn.burnVmDescriptorAvail
    minit mfin maddrs t burnAvail_graduableWide (hside.toFaithfulW hsat) i hi

/-- The per-row burn GATES hold at an ACTIVE row (the hardened mirror of
`rotated_row_gates_burn`). -/
theorem rotatedBurnAvail_row_gates (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash burnV3Avail minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length) :
    ∀ c ∈ EffectVmEmitBurn.burnRowGates, c.holdsVm (envAt t i) false false := by
  have hv1 : satisfiedVm hash EffectVmEmitBurn.burnVmDescriptor
      (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
    satisfiedVmBurnAvail_bare hash (envAt t i) _ _ (rotatedBurnAvail_row_v1 hash hside hsat i hi)
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  intro c hc
  have hmem : c ∈ EffectVmEmitBurn.burnVmDescriptor.constraints := by
    unfold EffectVmEmitBurn.burnVmDescriptor
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
  have hh := hv1.1 c hmem
  rw [hlastf] at hh
  unfold EffectVmEmitBurn.burnRowGates EffectVmEmitBurn.gFieldFixAll at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨j, hj, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using hh

/-- Hardened witness ⟹ per-cell burn value-block spec on row `i` (the mirror of
`rotated_row_cellSpec_burn`): the bare per-cell chain survives the weld verbatim. -/
theorem rotatedBurnAvail_row_cellSpec (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash burnV3Avail minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (pre post : CellState) (amt : ℤ)
    (henc : EffectVmEmitBurn.RowEncodes (envAt t i) pre amt post)
    (hrow : EffectVmEmitBurn.IsBurnRow (envAt t i)) :
    EffectVmEmitBurn.CellBurnSpec pre amt post := by
  have hint : EffectVmEmitBurn.BurnRowIntent (envAt t i) :=
    (EffectVmEmitBurn.burnVm_faithful (envAt t i) hrow).mp
      (rotatedBurnAvail_row_gates hash hside hsat i hi hnotlast)
  exact EffectVmEmitBurn.intent_to_cellSpec (envAt t i) pre post amt henc hint

/-! ## §2 — `rotatedEncodesBurnAvail`: the hardened decode (NO `guardAvail` residual).

The field-for-field mirror of `rotatedEncodesBurn` with TWO deltas:

  * **`guardAvail` is GONE** — availability is derived from the witness
    (`burn_availability_and_exact_move_forced`), no longer carried as an admissibility leg;
  * **`hdiCanon`** — the debit row's field-canonicality envelope (`0 ≤ loc c < p` for every
    column), the DEPLOYED canonical-element invariant the verifier's field decoding supplies
    (the same premise `rotV3_binds_published` consumes and the audit's repair pattern names).
    WIDTH-ONLY — it says nothing about order, so it is NOT availability laundered in
    (`burnAvail_derives_availability_row` derives the order from the borrow gates). -/

/-- The hardened decode: a satisfying `burnV3Avail` witness's designated holder-debit row tied onto
the kernel ledger, availability NOT assumed. -/
structure rotatedEncodesBurnAvail (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ) : Type where
  -- the designated holder-debit row + its decode
  di : Nat
  hdi : di < t.rows.length
  -- the designated debit row is an ACTIVE (transition) row, NOT the wrap/pad last row.
  hdiNotLast : di + 1 ≠ t.rows.length
  holderPre : CellState
  holderPost : CellState
  hdiRow : EffectVmEmitBurn.IsBurnRow (envAt t di)
  hdiEnc : EffectVmEmitBurn.RowEncodes (envAt t di) holderPre amt holderPost
  -- THE CANONICALITY ENVELOPE (deployed invariant, width-only — see the section header).
  hdiCanon : ∀ c, 0 ≤ (envAt t di).loc c ∧ (envAt t di).loc c < 2013265921
  -- the decoded holder limbs ARE the kernel ledger at the burned coordinate `(cell,a)`.
  hholderPre  : holderPre.balLo  = pre.kernel.bal cell a
  hholderPost : holderPost.balLo = post.kernel.bal cell a
  -- the ledger FRAME: the post ledger is the return-to-well image of the pre ledger.
  hledgerFrame : post.kernel.bal = recTransferBal pre.kernel.bal cell a a amt
  -- the residual admissibility legs (kernel side-tables, not in the value block). NOTE: NO
  -- guardAvail — availability is CIRCUIT-FORCED on this path.
  guardAuth : actor = cell ∨ mintAuthorizedB pre.kernel.caps actor a = true
  guardNonNeg : 0 ≤ amt
  guardLiveCell : cell ∈ pre.kernel.accounts
  guardLiveWell : a ∈ pre.kernel.accounts
  guardDistinct : cell ≠ a
  guardLifecycleLive : cellLifecycleLive pre.kernel a = true
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
  logAdv : post.log = Spec.SupplyDestruction.burnReceipt actor cell a amt :: pre.log

/-! ## §3 — THE DISCHARGE: availability + the EXACT ℤ debit are FORCED by the hardened witness. -/

/-- **`burn_availability_and_exact_move_forced` — burn `guardAvail` DISCHARGED (and upgraded).** A
`Satisfied2` witness of the hardened rotated burn + the hardened decode FORCE, on the kernel
ledger: `amt ≤ pre.bal cell a` (AVAILABILITY — the well-supply-inflation forgery class closed) AND
the EXACT ℤ debit `post.bal cell a = pre.bal cell a − amt` (STRICTLY STRONGER than the bare path's
mod-`p` `burn_debit_forced`: the borrow chain makes the subtraction exact over ℤ, no wrap witness
exists). The chain: rotated accept → (`rotV3FrozenWide_sound_v1`) per-row hardened `satisfiedVm` →
(`burnAvail_derives_availability_row`, at the row's own flags; burn is debit-only, so NO direction
premise) the borrow-forced order + move → (`RowEncodes` + the decode's ledger ties) the kernel
statement. The transfer template's `availability_and_exact_move_forced`, mirrored. -/
theorem burn_availability_and_exact_move_forced (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash burnV3Avail minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesBurnAvail hash minit mfin maddrs t pre post actor cell a amt) :
    amt ≤ pre.kernel.bal cell a
    ∧ post.kernel.bal cell a = pre.kernel.bal cell a - amt := by
  have hv1 := rotatedBurnAvail_row_v1 hash hside hsat henc.di henc.hdi
  have hlastf : (henc.di + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact henc.hdiNotLast
  rw [hlastf] at hv1
  -- decode the debit row's amount/state columns
  obtain ⟨hbLo, _, _, _, _, _, _, hAmt, hsaLo, _⟩ := henc.hdiEnc
  have h := EffectVmEmitBurn.burnAvail_derives_availability_row hash (envAt t henc.di)
    (henc.di == 0) henc.hdiCanon hv1
  rw [hAmt, hbLo, henc.hholderPre, hsaLo, henc.hholderPost] at h
  exact h

/-- Availability alone (`guardAvail`, proven). -/
theorem burn_availability_forced (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash burnV3Avail minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesBurnAvail hash minit mfin maddrs t pre post actor cell a amt) :
    amt ≤ pre.kernel.bal cell a :=
  (burn_availability_and_exact_move_forced hash hside hsat pre post actor cell a amt henc).1

/-- The EXACT ℤ debit alone (the mod-`p` `burn_debit_forced` upgraded to an ℤ equality). -/
theorem burn_debit_exact_forced (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash burnV3Avail minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesBurnAvail hash minit mfin maddrs t pre post actor cell a amt) :
    post.kernel.bal cell a = pre.kernel.bal cell a - amt :=
  (burn_availability_and_exact_move_forced hash hside hsat pre post actor cell a amt henc).2

/-! ## §4 — the bare decode RECOVERED (guardAvail proven), and the full refinement. -/

/-- **`rotatedEncodesBurnAvail.toEncodes` — the hardened decode yields the bare decode with
`guardAvail` PROVEN.** Every `rotatedEncodesBurn`-consuming theorem (`burn_descriptorRefines`, the
conservation tooth, the downstream consumers) applies to a hardened decode through this, with
availability circuit-forced instead of assumed — `RotatedKernelRefinementMintBurn`'s
`guardAvail` residual is discharged on the hardened path. -/
def rotatedEncodesBurnAvail.toEncodes (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {pre post : RecChainedState} {actor cell : CellId} {a : AssetId} {amt : ℤ}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash burnV3Avail minit mfin maddrs t)
    (henc : rotatedEncodesBurnAvail hash minit mfin maddrs t pre post actor cell a amt) :
    rotatedEncodesBurn hash minit mfin maddrs t pre post actor cell a amt :=
  { di := henc.di, hdi := henc.hdi, hdiNotLast := henc.hdiNotLast
    holderPre := henc.holderPre, holderPost := henc.holderPost
    hdiRow := henc.hdiRow, hdiEnc := henc.hdiEnc
    hholderPre := henc.hholderPre, hholderPost := henc.hholderPost
    hledgerFrame := henc.hledgerFrame
    guardAuth := henc.guardAuth
    guardNonNeg := henc.guardNonNeg
    -- THE DISCHARGE: availability from the WITNESS, not a residual.
    guardAvail := burn_availability_forced hash hside hsat pre post actor cell a amt henc
    guardLiveCell := henc.guardLiveCell, guardLiveWell := henc.guardLiveWell
    guardDistinct := henc.guardDistinct
    guardLifecycleLive := henc.guardLifecycleLive
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

/-- **`burn_descriptorRefinesAvail` — THE HARDENED BURN REFINEMENT.** Satisfying the hardened
rotated burn descriptor (`Satisfied2 hash burnV3Avail …`, wide table side) together with the
hardened decode forces the KERNEL's `BurnSpec` — with the AVAILABILITY guard sourced FROM THE
WITNESS (`burn_availability_forced`), no `guardAvail` residual anywhere. The bare path's honest gap
note (`⚠⚠ BURN AVAILABILITY IS NOT CIRCUIT-FORCED`, `RotatedKernelRefinementMintBurn` §3) is
exactly what this theorem closes on the hardened path. -/
theorem burn_descriptorRefinesAvail (hash : List ℤ → ℤ) {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash burnV3Avail minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesBurnAvail hash minit mfin maddrs t pre post actor cell a amt) :
    Spec.SupplyDestruction.BurnSpec pre actor cell a amt post := by
  -- the bare decode with `guardAvail` PROVEN, then the decode-only assembly (the same 21 legs
  -- `burn_descriptorRefines` reads — its proof consumes ONLY the decode).
  have henc' := rotatedEncodesBurnAvail.toEncodes hash hside hsat henc
  exact ⟨⟨henc'.guardAuth, henc'.guardNonNeg, henc'.guardAvail,
      henc'.guardLiveCell, henc'.guardLiveWell, henc'.guardDistinct, henc'.guardLifecycleLive⟩,
    henc'.hledgerFrame, henc'.logAdv,
    henc'.frAccounts, henc'.frCell, henc'.frCaps, henc'.frNullifiers, henc'.frRevoked,
    henc'.frCommitments, henc'.frSlotCaveats, henc'.frFactories, henc'.frLifecycle,
    henc'.frDeathCert, henc'.frDelegate, henc'.frDelegations, henc'.frDelegationEpoch,
    henc'.frDelegationEpochAt, henc'.frHeaps, henc'.frNullifierRoot, henc'.frRevokedRoot,
    henc'.frCommitmentsRoot⟩

/-! ## §5 — THE TOOTH: the forgery class is UNSAT on the hardened path. -/

/-- **`burn_descriptorRefinesAvail_rejects_overburn`** — ANY over-burn decode (`pre.bal cell a <
amt` — the audit's well-supply-inflation class) riding a satisfying hardened witness is UNSAT: the
borrow chain forces `amt ≤ pre.bal cell a`, so the assumption is `False`. The bare path ADMITS this
witness (`⚠⚠ BURN AVAILABILITY IS NOT CIRCUIT-FORCED`) and its ledger frame would CREDIT the well
`(a,a)` by the forged amount — mint-from-nothing; the hardened path REFUSES it — the forgery is
closable by the registry flip. -/
theorem burn_descriptorRefinesAvail_rejects_overburn (hash : List ℤ → ℤ)
    {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash burnV3Avail minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesBurnAvail hash minit mfin maddrs t pre post actor cell a amt)
    (hforge : pre.kernel.bal cell a < amt) : False := by
  have h := burn_availability_forced hash hside hsat pre post actor cell a amt henc
  omega

/-- The audit's CONCRETE forgery witness (`pre.bal cell a = 1`, `amt = 1006632961` — the
`before=1, amount=1006632961, after=1006632961` well-supply-inflation trace, `after − before +
amount = p ≡ 0` with `after < 2³⁰`) is UNSAT on the hardened path — the exact numbers of
`docs/FINDING-modp-wrap-forgery-audit.md` forgery 2 and of `burnAvail_forgery_unsat`, now refused
at the KERNEL refinement boundary. -/
theorem burn_descriptorRefinesAvail_audit_forgery_unsat (hash : List ℤ → ℤ)
    {permOut : List ℤ → List ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash burnV3Avail minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesBurnAvail hash minit mfin maddrs t pre post actor cell a amt)
    (hbal : pre.kernel.bal cell a = 1) (hamt : amt = 1006632961) : False := by
  refine burn_descriptorRefinesAvail_rejects_overburn hash hside hsat pre post actor cell a amt
    henc ?_
  omega

/-! ## §6 — Axiom-hygiene tripwires. -/

#assert_axioms burnAvail_graduableWide
#assert_axioms satisfiedVmBurnAvail_bare
#assert_axioms rotatedBurnAvail_row_v1
#assert_axioms rotatedBurnAvail_row_gates
#assert_axioms rotatedBurnAvail_row_cellSpec
#assert_axioms burn_availability_and_exact_move_forced
#assert_axioms burn_availability_forced
#assert_axioms burn_debit_exact_forced
#assert_axioms burn_descriptorRefinesAvail
#assert_axioms burn_descriptorRefinesAvail_rejects_overburn
#assert_axioms burn_descriptorRefinesAvail_audit_forgery_unsat

end Dregg2.Circuit.RotatedKernelRefinementMintBurnAvail
