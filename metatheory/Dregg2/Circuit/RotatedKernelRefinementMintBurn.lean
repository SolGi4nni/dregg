/-
# Dregg2.Circuit.RotatedKernelRefinementMintBurn — the VALUE-leg circuit→kernel refinement for the
**burn**, **mint**, and **bridgeMint** effects, on the LIVE ROTATED descriptors.

This module is the burn/mint clone of `RotatedKernelRefinement` (the `transfer` template). For each
effect it builds the apex obligation: satisfying the LIVE rotated descriptor (a `Satisfied2 hash
<effect>V3 …` witness, with the chip/range side conditions the rotated denotation already requires)
together with the boundary decode FORCES the kernel leaf-spec's state movement
(`Spec.SupplyDestruction.BurnSpec` / `Spec.SupplyCreation.MintASpec`).

## The two worlds, and what the circuit FORCES vs. what the decode carries

The live prover runs the ROTATED descriptors:
  * `burnV3  := v3OfFrozen EffectVmEmitBurn.burnVmDescriptor`  (registry `burnVmDescriptor2R24`);
  * `mintV3  := v3OfFrozen mintTickFace = v3OfFrozen EffectVmEmitMint.mintVmDescriptor` (`mintVmDescriptor2R24`).
The kernel leaves are `BurnSpec` (holder `(cell,a)` debit, well `(a,a)` credit; the W1 return-to-well)
and `MintASpec` (well `(a,a)` debit, recipient `(cell,a)` credit; the W1 issuer-move). bridgeMint
dispatches to the SAME `recCMintAsset` and meets `MintASpec` VERBATIM, so its refinement is the mint
refinement re-exported (`bridgeMint_descriptorRefines`, an alias).

Just as `transfer_descriptorRefines`, the honest split is:
  * the per-row circuit (`burnVm_faithful` / `mintVm_faithful`, lifted through `RowEncodes` to
    `CellBurnSpec` / `CellMintSpec`) FORCES the moved limb of the DESIGNATED debit/credit row, and the
    live range tooth on `bal_lo` pins non-negativity ⟹ availability;
  * the kernel-only residual (the authority/liveness/distinctness guard, the 16-field frame, the
    receipt log, and the CROSS-cell ledger frame `recTransferBal`) is NAMED as explicit decode legs in
    `rotatedEncodesBurn` / `rotatedEncodesMint` — not assumed away.

The both-polarity teeth (`burn_descriptorRefines_rejects_wrong_debit`, … `_wrong_credit` for mint)
witness that the circuit genuinely bites: a decode claiming a moved-limb post NOT equal to the
circuit-forced debit/credit is UNSAT, because the gate pins the limb to `pre ∓ amount`.

## Axiom hygiene

`#assert_axioms` on every theorem ⊆ {propext, Classical.choice, Quot.sound} + the named carriers
inherited through the imports (here NONE of the hash carriers are even needed — the value-block intent
is forced by the gates, not the commitment). NEW file; imports are read-only.
-/
import Dregg2.Circuit.RotatedKernelRefinement
import Dregg2.Circuit.Emit.EffectVmEmitBurn
import Dregg2.Circuit.Emit.EffectVmEmitMint
import Dregg2.Circuit.Spec.supplydestruction
import Dregg2.Circuit.Spec.supplycreation

namespace Dregg2.Circuit.RotatedKernelRefinementMintBurn

open Dregg2.Circuit.Emit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitV2
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (eSA eSB eSub)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.RotatedKernelRefinement (RotTableSide)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §0 — the live rotated burn / mint descriptors.

`burnV3` is exactly the descriptor the rotated prover runs for a burn (`v3Registry`'s
`burnVmDescriptor2R24`). `mintV3` is the rotated tick-faced BridgeMint (`mintVmDescriptor2R24`); since
`mintTickFace = EffectVmEmitMint.mintVmDescriptor` definitionally, `mintV3 = v3OfFrozen mintVmDescriptor`. -/

/-- The live rotated burn descriptor (`v3Registry`'s `burnVmDescriptor2R24`). -/
def burnV3 : EffectVmDescriptor2 := v3OfFrozen EffectVmEmitBurn.burnVmDescriptor

theorem burnV3_eq : burnV3 = v3OfFrozen EffectVmEmitBurn.burnVmDescriptor := rfl

/-- The live rotated BridgeMint descriptor (`v3Registry`'s `mintVmDescriptor2R24`), through the
tick-faced source which COINCIDES with `mintVmDescriptor` (`mintTickFace_eq_source`). -/
theorem mintV3_eq_source : mintV3 = v3OfFrozen EffectVmEmitMint.mintVmDescriptor := rfl

/-- `burnVmDescriptor` is graduable — the decidable side condition `rotV3Frozen_sound_v1` needs. -/
theorem burn_graduable : graduable EffectVmEmitBurn.burnVmDescriptor = true := by decide

/-- `mintVmDescriptor` is graduable. -/
theorem mint_graduable : graduable EffectVmEmitMint.mintVmDescriptor = true := by decide

/-! ## §1 — BURN: the rotated→per-row→per-cell decode chain (the witness side).

`rotV3Frozen_sound_v1` yields, on every row, the v1 denotation of `burnVmDescriptor`; the burn per-row gates
(`burnRowGates`, all flag-independent `.gate`s) hold; `burnVm_faithful` + `intent_to_cellSpec` lift the
row's value block to `CellBurnSpec` (the `bal_lo` debit by `param1`, the frame freeze). -/

/-- The per-row burn GATES hold at an ACTIVE row (`i` NOT the last row), mirroring transfer's
`rotated_row_gates`. The burn gates are all `.gate` constraints which under the deployed
`when_transition()` bind on every row but the last — so on a TRANSITION row (`i + 1 ≠ t.rows.length`,
`isLast` flag `false`) their body equation holds at `false false`. (The `hnotlast` hypothesis is the
faithful obligation that the designated effect row is a genuine transition row, not the wrap/pad row;
any real ≥2-row trace carries it.) -/
theorem rotated_row_gates_burn (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash burnV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length) :
    ∀ c ∈ EffectVmEmitBurn.burnRowGates, c.holdsVm (envAt t i) false false := by
  have hv1 : satisfiedVm hash EffectVmEmitBurn.burnVmDescriptor
      (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
    rotV3Frozen_sound_v1 permOut hash EffectVmEmitBurn.burnVmDescriptor minit mfin maddrs t
      burn_graduable (hside.toFaithful hsat) i hi
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

/-- **`rotated_row_cellSpec_burn` — rotated witness ⟹ per-cell burn spec on row `i`.** -/
theorem rotated_row_cellSpec_burn (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash burnV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (pre post : CellState) (amt : ℤ)
    (henc : EffectVmEmitBurn.RowEncodes (envAt t i) pre amt post)
    (hrow : EffectVmEmitBurn.IsBurnRow (envAt t i)) :
    EffectVmEmitBurn.CellBurnSpec pre amt post := by
  have hint : EffectVmEmitBurn.BurnRowIntent (envAt t i) :=
    (EffectVmEmitBurn.burnVm_faithful (envAt t i) hrow).mp
      (rotated_row_gates_burn hash hside hsat i hi hnotlast)
  exact EffectVmEmitBurn.intent_to_cellSpec (envAt t i) pre post amt henc hint

/-! ## §2 — `rotatedEncodesBurn`: the witness boundary ⟷ kernel state decode (burn).

The designated DEBIT row is the HOLDER's burn row (`(cell,a)`): the burn gate debits its `bal_lo` by
`param1`. The well credit (`(a,a)` rises by `amt`) and the cross-cell ledger frame live in the named
`hledgerFrame := recTransferBal pre.bal cell a a amt` leg (the per-cell row debits ONE entry; the
single-sign burn gate cannot also CREDIT the well — that leg is the kernel `recTransferBal` definition,
carried, with the circuit forcing the holder limb to agree). The guard / frame / log are the kernel
residual the value block cannot carry — NAMED, mirroring transfer's `rotatedEncodes`. -/

/-- The decode relating a satisfying rotated burn witness's HOLDER debit row to a kernel `pre → post`
burn of asset `a` from holder `cell` (well `a`) by `amt`, on actor `actor`. DATA-bearing (`Type`):
exhibits the designated debit row + its `CellState`s, the boundary-tying limb equalities, and the
kernel-side residual. -/
structure rotatedEncodesBurn (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ) : Type where
  -- the designated holder-debit row + its decode
  di : Nat
  hdi : di < t.rows.length
  -- the designated debit row is an ACTIVE (transition) row, NOT the wrap/pad last row: the deployed
  -- gates run under `when_transition()`, so the move is forced only off the last row. Any real ≥2-row
  -- burn trace carries this (the prover pads a wrap row after the effect row).
  hdiNotLast : di + 1 ≠ t.rows.length
  holderPre : CellState
  holderPost : CellState
  hdiRow : EffectVmEmitBurn.IsBurnRow (envAt t di)
  hdiEnc : EffectVmEmitBurn.RowEncodes (envAt t di) holderPre amt holderPost
  -- the decoded holder limbs ARE the kernel ledger at the burned coordinate `(cell,a)`.
  hholderPre  : holderPre.balLo  = pre.kernel.bal cell a
  hholderPost : holderPost.balLo = post.kernel.bal cell a
  -- the ledger FRAME: the post ledger is the return-to-well image of the pre ledger (the residual the
  -- per-cell holder row does not pin cross-cell — `recTransferBal cell a a amt`).
  hledgerFrame : post.kernel.bal = recTransferBal pre.kernel.bal cell a a amt
  -- the residual admissibility legs (kernel side-tables, not in the value block) — the `BurnGuard`.
  -- STAGE-3 authority split: holder self-redeem (`actor = cell`) OR issuer authority.
  guardAuth : actor = cell ∨ mintAuthorizedB pre.kernel.caps actor a = true
  guardNonNeg : 0 ≤ amt
  guardLiveCell : cell ∈ pre.kernel.accounts
  guardLiveWell : a ∈ pre.kernel.accounts
  guardDistinct : cell ≠ a
  -- the issuer well is lifecycle-LIVE ("Destroyed is terminal"): membership (`guardLiveWell`) is NOT
  -- liveness — a member-but-Destroyed well is refused. COMMITMENT-BINDABLE: it reads `lifecycle`,
  -- which the deployed record_digest binds (and the `frLifecycle` frame already carries it).
  guardLifecycleLive : cellLifecycleLive pre.kernel a = true
  -- the 16 non-`bal` kernel frame fields + the receipt-log advance (the full `BurnSpec` frame residual).
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
  logAdv : post.log = Spec.SupplyDestruction.burnReceipt actor cell a amt :: pre.log

/-! ## §3 — BURN: the circuit FORCES the holder debit + availability. -/

/-- The holder row's per-cell spec, read onto the kernel ledger: `post.bal cell a = pre.bal cell a −
amt`. The circuit FORCES it (the burn gate `bal_lo' = bal_lo − param1`). -/
theorem burn_debit_forced (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash burnV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesBurn hash minit mfin maddrs t pre post actor cell a amt) :
    post.kernel.bal cell a = pre.kernel.bal cell a - amt := by
  have hspec : EffectVmEmitBurn.CellBurnSpec henc.holderPre amt henc.holderPost :=
    rotated_row_cellSpec_burn hash hside hsat henc.di henc.hdi henc.hdiNotLast henc.holderPre
      henc.holderPost amt henc.hdiEnc henc.hdiRow
  obtain ⟨hmove, _, _, _, _, _⟩ := hspec
  rw [← henc.hholderPost, ← henc.hholderPre, hmove]

/-- **Availability is CIRCUIT-FORCED (burn).** On the holder row the live range tooth pins `0 ≤
holderPost.balLo`; with the debit gate `holderPost.balLo = holderPre.balLo − amount`, this is exactly
`amt ≤ pre.bal cell a` — the `BurnGuard` availability leg, enforced by the running circuit. -/
theorem burn_availability_forced (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash burnV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesBurn hash minit mfin maddrs t pre post actor cell a amt) :
    amt ≤ pre.kernel.bal cell a := by
  -- the v1 denotation on the holder row (i-dependent flags).
  have hv1 : satisfiedVm hash EffectVmEmitBurn.burnVmDescriptor
      (envAt t henc.di) (henc.di == 0) (henc.di + 1 == t.rows.length) :=
    rotV3Frozen_sound_v1 permOut hash EffectVmEmitBurn.burnVmDescriptor minit mfin maddrs t
      burn_graduable (hside.toFaithful hsat) henc.di henc.hdi
  -- the balance-debit gate (flag-independent) and the live range tooth (`hv1.2.2`).
  have hbal := rotated_row_gates_burn hash hside hsat henc.di henc.hdi henc.hdiNotLast
    (.gate EffectVmEmitBurn.gBalLoDebit)
    (by simp [EffectVmEmitBurn.burnRowGates])
  have hrng := hv1.2.2 (⟨saCol state.BALANCE_LO, 30⟩) (by simp [EffectVmEmitBurn.burnVmDescriptor])
  simp only [VmConstraint.holdsVm, EffectVmEmitBurn.gBalLoDebit, EffectVmEmitBurn.ePrmBurnAmt,
    eSA, eSB, eSub, Dregg2.Exec.CircuitEmit.EmittedExpr.eval] at hbal
  have hnn : 0 ≤ (envAt t henc.di).loc (saCol state.BALANCE_LO) := hrng.1
  -- decode the holder row's pre-limb / amount columns through RowEncodes.
  obtain ⟨hsbLo, _, _, _, _, _, _, hpAmt, _⟩ := henc.hdiEnc
  have hdebit : (envAt t henc.di).loc (saCol state.BALANCE_LO)
      = (envAt t henc.di).loc (sbCol state.BALANCE_LO)
        - (envAt t henc.di).loc (prmCol EffectVmEmitBurn.param.BURN_AMOUNT_LO) := by
    linarith [hbal]
  have hle : (envAt t henc.di).loc (prmCol EffectVmEmitBurn.param.BURN_AMOUNT_LO)
      ≤ (envAt t henc.di).loc (sbCol state.BALANCE_LO) := by linarith [hdebit, hnn]
  rw [hpAmt] at hle
  rw [hsbLo, henc.hholderPre] at hle
  exact hle

set_option maxHeartbeats 800000 in
/-- **`burn_descriptorRefines` — THE BURN CIRCUIT→KERNEL REFINEMENT.** Satisfying the LIVE rotated burn
descriptor (`Satisfied2 hash burnV3 …`, with the chip/range side conditions) together with
`rotatedEncodesBurn` forces the kernel's `BurnSpec pre actor cell a amt post`. The holder ledger debit
and the AVAILABILITY guard come FROM THE WITNESS (`burn_debit_forced` / `burn_availability_forced`); the
kernel-side residual (authority / liveness / distinctness / the 16-field frame / the well-credit ledger
frame / the log) comes from the decode. -/
theorem burn_descriptorRefines (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash burnV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesBurn hash minit mfin maddrs t pre post actor cell a amt) :
    Spec.SupplyDestruction.BurnSpec pre actor cell a amt post := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- BurnGuard: authority / non-neg / AVAILABILITY / live-cell / live-well / distinct / lifecycle-live.
    exact ⟨henc.guardAuth, henc.guardNonNeg,
      burn_availability_forced hash hside hsat pre post actor cell a amt henc,
      henc.guardLiveCell, henc.guardLiveWell, henc.guardDistinct, henc.guardLifecycleLive⟩
  · exact henc.hledgerFrame
  · exact henc.logAdv
  · exact henc.frAccounts
  · exact henc.frCell
  · exact henc.frCaps
  · exact henc.frNullifiers
  · exact henc.frRevoked
  · exact henc.frCommitments
  · exact henc.frSlotCaveats
  · exact henc.frFactories
  · exact henc.frLifecycle
  · exact henc.frDeathCert
  · exact henc.frDelegate
  · exact henc.frDelegations
  · exact henc.frDelegationEpoch
  · exact henc.frDelegationEpochAt
  · exact henc.frHeaps
  · exact henc.frNullifierRoot
  · exact henc.frRevokedRoot

/-- **`burn_descriptorRefines_rejects_wrong_debit` — the conservation tooth (burn).** A decode claiming
a holder post-balance NOT the genuine debit `pre.bal cell a − amt` rides NO satisfying witness: the
circuit pins the burn limb, so a wrong-amount burn is UNSAT. -/
theorem burn_descriptorRefines_rejects_wrong_debit (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash burnV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesBurn hash minit mfin maddrs t pre post actor cell a amt)
    (hwrong : post.kernel.bal cell a ≠ pre.kernel.bal cell a - amt) :
    False :=
  hwrong (burn_debit_forced hash hside hsat pre post actor cell a amt henc)

/-! ## §4 — MINT: the rotated→per-row→per-cell decode chain (the witness side).

Identical shape to burn, over `mintV3` / `mintVmDescriptor` / `mintRowGates` / `mintVm_faithful`. The
designated row is the RECIPIENT's credit row (`(cell,a)`): the mint gate credits its `bal_lo` by
`param1`. The well debit (`(a,a)` falls) + the cross-cell ledger frame are the named `recTransferBal a
cell a amt` leg. -/

/-- The per-row mint GATES hold at an ACTIVE row (`i` NOT the last row). The mint gates are all
`.gate` constraints which under the deployed `when_transition()` bind on every row but the last — so
on a TRANSITION row (`i + 1 ≠ t.rows.length`, `isLast` flag `false`) their body equation holds at
`false false`. (The `hnotlast` hypothesis is the faithful obligation that the designated effect row
is a genuine transition row, not the wrap/pad row.) -/
theorem rotated_row_gates_mint (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash mintV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length) :
    ∀ c ∈ EffectVmEmitMint.mintRowGates, c.holdsVm (envAt t i) false false := by
  have hv1 : satisfiedVm hash EffectVmEmitMint.mintVmDescriptor
      (envAt t i) (i == 0) (i + 1 == t.rows.length) :=
    rotV3Frozen_sound_v1 permOut hash EffectVmEmitMint.mintVmDescriptor minit mfin maddrs t
      mint_graduable (hside.toFaithful hsat) i hi
  have hlastf : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; exact hnotlast
  intro c hc
  have hmem : c ∈ EffectVmEmitMint.mintVmDescriptor.constraints := by
    unfold EffectVmEmitMint.mintVmDescriptor
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl hc))
  have hh := hv1.1 c hmem
  rw [hlastf] at hh
  unfold EffectVmEmitMint.mintRowGates EffectVmEmitMint.gFieldFixAll at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨j, hj, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using hh

/-- **`rotated_row_cellSpec_mint` — rotated witness ⟹ per-cell mint spec on row `i`.** -/
theorem rotated_row_cellSpec_mint (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash mintV3 minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (hnotlast : i + 1 ≠ t.rows.length)
    (pre post : CellState) (amt : ℤ)
    (henc : EffectVmEmitMint.RowEncodes (envAt t i) pre amt post)
    (hrow : EffectVmEmitMint.IsMintRow (envAt t i)) :
    EffectVmEmitMint.CellMintSpec pre amt post := by
  have hint : EffectVmEmitMint.MintRowIntent (envAt t i) :=
    (EffectVmEmitMint.mintVm_faithful (envAt t i) hrow).mp
      (rotated_row_gates_mint hash hside hsat i hi hnotlast)
  exact EffectVmEmitMint.intent_to_cellSpec (envAt t i) pre post amt henc hint

/-! ## §5 — `rotatedEncodesMint`: the witness boundary ⟷ kernel state decode (mint).

The designated CREDIT row is the RECIPIENT's mint row (`(cell,a)`). The named residual carries the
`MintASpec` guard (`mintAdmit`), the well-debit ledger frame `recTransferBal a cell a amt`, the 16
frame fields, and the receipt log. -/

/-- The decode relating a satisfying rotated mint witness's RECIPIENT credit row to a kernel
`pre → post` mint of asset `a` into recipient `cell` (well `a`) by `amt`, on actor `actor`. -/
structure rotatedEncodesMint (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ) : Type where
  -- the designated recipient-credit row + its decode
  ci : Nat
  hci : ci < t.rows.length
  -- the designated credit row is an ACTIVE (transition) row, NOT the wrap/pad last row: the deployed
  -- gates run under `when_transition()`, so the move is forced only off the last row. Any real ≥2-row
  -- mint trace carries this (the prover pads a wrap row after the effect row).
  hciNotLast : ci + 1 ≠ t.rows.length
  recipPre : CellState
  recipPost : CellState
  hciRow : EffectVmEmitMint.IsMintRow (envAt t ci)
  hciEnc : EffectVmEmitMint.RowEncodes (envAt t ci) recipPre amt recipPost
  -- the decoded recipient limbs ARE the kernel ledger at the minted coordinate `(cell,a)`.
  hrecipPre  : recipPre.balLo  = pre.kernel.bal cell a
  hrecipPost : recipPost.balLo = post.kernel.bal cell a
  -- the ledger FRAME: the post ledger is the issuer-move image of the pre ledger
  -- (`recTransferBal a cell a amt` — well `(a,a)` debited, recipient `(cell,a)` credited).
  hledgerFrame : post.kernel.bal = recTransferBal pre.kernel.bal a cell a amt
  -- the residual admissibility legs (the `mintAdmit` guard).
  guardAuth : mintAuthorizedB pre.kernel.caps actor a = true
  guardNonNeg : 0 ≤ amt
  guardLiveWell : a ∈ pre.kernel.accounts
  guardLiveCell : cell ∈ pre.kernel.accounts
  guardDistinct : a ≠ cell
  -- the issuer (well / bridge) cell is lifecycle-LIVE ("Destroyed is terminal"): a member-but-Destroyed
  -- issuer is refused. COMMITMENT-BINDABLE: reads `lifecycle` (deployed record_digest binds it; the
  -- `frLifecycle` frame already carries it).
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
  logAdv : post.log = Spec.SupplyCreation.mintReceipt actor cell a amt :: pre.log

/-! ## §6 — MINT: the circuit FORCES the recipient credit. -/

/-- The recipient row's per-cell spec, read onto the kernel ledger: `post.bal cell a = pre.bal cell a +
amt`. The circuit FORCES it (the mint credit gate `bal_lo' = bal_lo + param1`). -/
theorem mint_credit_forced (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash mintV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesMint hash minit mfin maddrs t pre post actor cell a amt) :
    post.kernel.bal cell a = pre.kernel.bal cell a + amt := by
  have hspec : EffectVmEmitMint.CellMintSpec henc.recipPre amt henc.recipPost :=
    rotated_row_cellSpec_mint hash hside hsat henc.ci henc.hci henc.hciNotLast henc.recipPre
      henc.recipPost amt henc.hciEnc henc.hciRow
  obtain ⟨hmove, _, _, _, _, _⟩ := hspec
  rw [← henc.hrecipPost, ← henc.hrecipPre, hmove]

set_option maxHeartbeats 800000 in
/-- **`mint_descriptorRefines` — THE MINT CIRCUIT→KERNEL REFINEMENT.** Satisfying the LIVE rotated mint
descriptor (`Satisfied2 hash mintV3 …`) together with `rotatedEncodesMint` forces the kernel's
`MintASpec pre actor cell a amt post`. The recipient ledger credit comes FROM THE WITNESS
(`mint_credit_forced`); the kernel-side residual (the `mintAdmit` guard, the well-debit ledger frame,
the 16-field frame, the log) comes from the decode. (Note: a mint has NO availability gate — the well
is negative-capable — so the guard has no circuit-availability leg, unlike burn/transfer.) -/
theorem mint_descriptorRefines (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash mintV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesMint hash minit mfin maddrs t pre post actor cell a amt) :
    Spec.SupplyCreation.MintASpec pre actor cell a amt post := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- mintAdmit: authority / non-neg / well-membership / recipient-membership / distinctness / lifecycle-live.
    exact ⟨henc.guardAuth, henc.guardNonNeg, henc.guardLiveWell, henc.guardLiveCell,
      henc.guardDistinct, henc.guardLifecycleLive⟩
  · exact henc.hledgerFrame
  · exact henc.logAdv
  · exact henc.frAccounts
  · exact henc.frCell
  · exact henc.frCaps
  · exact henc.frNullifiers
  · exact henc.frRevoked
  · exact henc.frCommitments
  · exact henc.frSlotCaveats
  · exact henc.frFactories
  · exact henc.frLifecycle
  · exact henc.frDeathCert
  · exact henc.frDelegate
  · exact henc.frDelegations
  · exact henc.frDelegationEpoch
  · exact henc.frDelegationEpochAt
  · exact henc.frHeaps
  · exact henc.frNullifierRoot
  · exact henc.frRevokedRoot

/-- **`mint_descriptorRefines_rejects_wrong_credit` — the conservation tooth (mint).** A decode claiming
a recipient post-balance NOT the genuine credit `pre.bal cell a + amt` rides NO satisfying witness: the
circuit pins the mint limb, so a wrong-amount mint is UNSAT. -/
theorem mint_descriptorRefines_rejects_wrong_credit (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash mintV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesMint hash minit mfin maddrs t pre post actor cell a amt)
    (hwrong : post.kernel.bal cell a ≠ pre.kernel.bal cell a + amt) :
    False :=
  hwrong (mint_credit_forced hash hside hsat pre post actor cell a amt henc)

/-! ## §7 — bridgeMint: the SAME refinement, re-exported.

`execFullA_bridgeMintA` dispatches to the SAME `recCMintAsset` and the bridge cell IS the issuer, so a
committed `bridgeMintA` meets `MintASpec` VERBATIM (`Spec.SupplyCreation.execBridgeMintA_iff_spec`). Its
live descriptor is the SAME `mintV3`. So bridgeMint's value-leg refinement is the mint refinement, with
no re-proof — the witness, decode, and conclusion are identical (the alias makes the intent explicit). -/

/-- **`bridgeMint_descriptorRefines` — bridgeMint refines to `MintASpec` (alias of mint).** Satisfying
the LIVE rotated `mintV3` descriptor (BridgeMint's registry leg) with `rotatedEncodesMint` forces
`MintASpec pre actor cell a amt post` — the SAME spec a committed `bridgeMintA` meets
(`execBridgeMintA_iff_spec`). Re-exported, not re-proved. -/
theorem bridgeMint_descriptorRefines (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash mintV3 minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesMint hash minit mfin maddrs t pre post actor cell a amt) :
    Spec.SupplyCreation.MintASpec pre actor cell a amt post :=
  mint_descriptorRefines hash hside hsat pre post actor cell a amt henc

/-! ## §8 — Axiom-hygiene tripwires. -/

#assert_axioms burn_graduable
#assert_axioms mint_graduable
#assert_axioms rotated_row_gates_burn
#assert_axioms rotated_row_cellSpec_burn
#assert_axioms burn_debit_forced
#assert_axioms burn_availability_forced
#assert_axioms burn_descriptorRefines
#assert_axioms burn_descriptorRefines_rejects_wrong_debit
#assert_axioms rotated_row_gates_mint
#assert_axioms rotated_row_cellSpec_mint
#assert_axioms mint_credit_forced
#assert_axioms mint_descriptorRefines
#assert_axioms mint_descriptorRefines_rejects_wrong_credit
#assert_axioms bridgeMint_descriptorRefines

end Dregg2.Circuit.RotatedKernelRefinementMintBurn
