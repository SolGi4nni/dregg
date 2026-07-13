/-
# Dregg2.Circuit.ClosureFloorReduceFanout — the per-effect column-read discharge, THREADED into the
fanout readouts: the `rotatedEncodes<E>` decode structures (`ClosureFanoutGenuine`'s readouts produce
them) are REBUILT from a column-free residual, their carried `RowEncodes` decode supplied by the
`derive_designation_discharge`-emitted `<e>_rowEncodes_of_designation` lemma — NOT carried as floor.

## What this lands (the P1 readout reduction, on the fanout effects)

`ClosureFloorReduce` realized the reduction on the TRANSFER template: `TransferTraceReadout`'s carried
`RowEncodes` decodes (`hdiEnc`/`hciEnc`) + decoded `srcPre`/…/`dstPost` records are reconstructed from
`{row designation + publish ties}` via `ClosureColumnDischarge.rowEncodes_of_designation`. This module
does the SAME for the non-transfer per-effect encode structures, now that the macro has emitted a
discharge lemma for EVERY clean family:

  * **incrementNonce (pre-post exemplar).** `rotatedEncodesIncNonce` carries `cellPre`/`cellPost`
    (decoded `CellState`s) + `hwiEnc : RowEncodesIncNonce (envAt t wi) cellPre cellPost` — the mechanical
    column decode. `IncNonceReadoutResidual` DROPS those three fields, keeping the row designation `wi`
    (+ its ACTIVE/not-last flag), the row shape `IsIncNonceRow`, the canonicality envelope
    `IncNonceRowCanon`, the two publish ties, and the GENUINE kernel residual (the forced tick `hnVal`,
    the whole-map move `hcellMove`, the guard, the log advance, the 18 frame fields).
    `rotatedEncodesIncNonce_of_residual` REBUILDS the full structure: `cellPre`/`cellPost` are the
    canonical `decodeCellPre/Post (envAt t wi)`, and `hwiEnc` is `incNonce_rowEncodes_of_designation`
    (the emitted discharge — 14 column reads `rfl`, 2 publish ties from the designation).

  * **mint (value-carrying exemplar).** `rotatedEncodesMint` carries `recipPre`/`recipPost` +
    `hciEnc : EffectVmEmitMint.RowEncodes (envAt t ci) recipPre amt recipPost`. `MintReadoutResidual`
    drops those, keeping the designation `ci`, the row shape, the two publish ties + the value-column
    tie `hAmt : (envAt t ci).loc (prmCol VALUE_LO) = amt`, and the GENUINE ledger residual (the limb
    ties `hrecipPre`/`hrecipPost` — the surface seam — the ledger frame, the `mintAdmit` guards, the 18
    frame fields, the log advance). `rotatedEncodesMint_of_residual` rebuilds it: the decode is
    `mint_rowEncodes_of_designation`, its value slot rewritten to `amt` by `hAmt`.

So the fanout readouts' `rotatedEncodes<E>` floor SHRINKS to `{row designation + publish ties (+ the
value-column tie)}` — all StarkSound / hash-CR class — with the `RowEncodes`/`*Encodes` limb decode
DISCHARGED, mirroring the transfer template exactly. The ledger-seam / guard / authority / availability
/ frame residuals SURVIVE BY DESIGN (only the column-decode content shrinks — the P1 assessment).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The rebuild is a structure literal; the
decode fields come from the discharge lemmas (`rfl` columns + the named publish ties). Imports read-only.
-/
import Dregg2.Circuit.ClosureDesignationDischarge
import Dregg2.Circuit.RotatedKernelRefinementIncNonce
import Dregg2.Circuit.RotatedKernelRefinementMintBurn

namespace Dregg2.Circuit.ClosureFloorReduceFanout

open Dregg2.Circuit.DescriptorIR2 (VmTrace envAt)
open Dregg2.Circuit.ClosureColumnDischarge (decodeCellPre decodeCellPost)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.RotatedKernelRefinementIncNonce (rotatedEncodesIncNonce)
open Dregg2.Circuit.RotatedKernelRefinementMintBurn (rotatedEncodesMint)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false

/-! ## §1 — incrementNonce (pre-post): the column-free residual + the rebuild. -/

/-- **`IncNonceReadoutResidual` — the column-free carry of `rotatedEncodesIncNonce`.** The row
designation `wi` (+ its ACTIVE/not-last flag), the row shape, the canonicality envelope, the two publish
ties, and the GENUINE kernel residual (the forced tick, the whole-map move, the guard, the log advance,
the 18 frame fields). NO `cellPre`/`cellPost` records, NO `RowEncodesIncNonce` decode — §1's rebuild
reconstructs those by reading `env.loc` + the discharge lemma. -/
structure IncNonceReadoutResidual (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pre post : RecChainedState) (actor cell : CellId) (n : Int) : Type where
  wi : Nat
  hwi : wi < t.rows.length
  hwiNotLast : wi + 1 ≠ t.rows.length
  hwiRow : Dregg2.Circuit.Emit.EffectVmEmitIncrementNonce.IsIncNonceRow (envAt t wi)
  hCanon : Dregg2.Circuit.Emit.EffectVmEmitIncrementNonce.IncNonceRowCanon (envAt t wi)
  -- the two publish ties (the `piBinding` hash-CR facts) that reconstruct the `RowEncodesIncNonce` decode.
  hwiOld : (envAt t wi).pub pi.OLD_COMMIT = (envAt t wi).loc (sbCol state.STATE_COMMIT)
  hwiNew : (envAt t wi).pub pi.NEW_COMMIT = (envAt t wi).loc (saCol state.STATE_COMMIT)
  -- the kernel write value IS the circuit-forced tick of the DECODED pre-cell nonce.
  hnVal : n = (decodeCellPre (envAt t wi)).nonce + 1
  hcellMove : post.kernel.cell
    = Dregg2.Circuit.Spec.CellStateMonotone.incNonceCellMap pre.kernel cell n
  logAdv : post.log = { actor := actor, src := cell, dst := cell, amt := 0 } :: pre.log
  guard : Dregg2.Circuit.Spec.CellStateMonotone.incNonceGuard pre actor cell n
  frAccounts : post.kernel.accounts = pre.kernel.accounts
  frCaps : post.kernel.caps = pre.kernel.caps
  frNullifiers : post.kernel.nullifiers = pre.kernel.nullifiers
  frRevoked : post.kernel.revoked = pre.kernel.revoked
  frCommitments : post.kernel.commitments = pre.kernel.commitments
  frBal : post.kernel.bal = pre.kernel.bal
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

/-- **`rotatedEncodesIncNonce_of_residual` — the decode column reads DISCHARGED.** From the column-free
residual, produce the full `rotatedEncodesIncNonce`: `cellPre`/`cellPost` are the canonical decoders, and
`hwiEnc` is `incNonce_rowEncodes_of_designation` (the emitted discharge — the 14 column reads `rfl`, the
2 publish ties supplied by the designation). The mechanical column decode was never floor. -/
def rotatedEncodesIncNonce_of_residual (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {pre post : RecChainedState} {actor cell : CellId} {n : Int}
    (r : IncNonceReadoutResidual hash minit mfin maddrs t pre post actor cell n) :
    rotatedEncodesIncNonce hash minit mfin maddrs t pre post actor cell n where
  wi := r.wi
  hwi := r.hwi
  hwiNotLast := r.hwiNotLast
  cellPre := decodeCellPre (envAt t r.wi)
  cellPost := decodeCellPost (envAt t r.wi)
  hwiRow := r.hwiRow
  hwiEnc := Dregg2.Circuit.ClosureDesignationDischarge.incNonce_rowEncodes_of_designation
    (envAt t r.wi) r.hwiOld r.hwiNew
  hCanon := r.hCanon
  hnVal := r.hnVal
  hcellMove := r.hcellMove
  logAdv := r.logAdv
  guard := r.guard
  frAccounts := r.frAccounts
  frCaps := r.frCaps
  frNullifiers := r.frNullifiers
  frRevoked := r.frRevoked
  frCommitments := r.frCommitments
  frBal := r.frBal
  frSlotCaveats := r.frSlotCaveats
  frFactories := r.frFactories
  frLifecycle := r.frLifecycle
  frDeathCert := r.frDeathCert
  frDelegate := r.frDelegate
  frDelegations := r.frDelegations
  frDelegationEpoch := r.frDelegationEpoch
  frDelegationEpochAt := r.frDelegationEpochAt
  frHeaps := r.frHeaps
  frNullifierRoot := r.frNullifierRoot
  frRevokedRoot := r.frRevokedRoot
  frCommitmentsRoot := r.frCommitmentsRoot

/-! ## §2 — mint (value-carrying): the column-free residual + the rebuild. -/

/-- **`MintReadoutResidual` — the column-free carry of `rotatedEncodesMint`.** The designation `ci` (+
its ACTIVE/not-last flag), the row shape, the two publish ties + the value-column tie, and the GENUINE
ledger residual (the limb ties — the surface seam — the ledger frame, the `mintAdmit` guards, the 18
frame fields, the log advance). NO `recipPre`/`recipPost` records, NO `RowEncodes` decode. -/
structure MintReadoutResidual (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ) : Type where
  ci : Nat
  hci : ci < t.rows.length
  hciNotLast : ci + 1 ≠ t.rows.length
  hciRow : Dregg2.Circuit.Emit.EffectVmEmitMint.IsMintRow (envAt t ci)
  -- the two publish ties + the value-column tie that reconstruct the `RowEncodes` decode.
  hciOld : (envAt t ci).pub pi.OLD_COMMIT = (envAt t ci).loc (sbCol state.STATE_COMMIT)
  hciNew : (envAt t ci).pub pi.NEW_COMMIT = (envAt t ci).loc (saCol state.STATE_COMMIT)
  hAmt : (envAt t ci).loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitMint.VALUE_LO) = amt
  -- the decoded recipient limbs ARE the kernel ledger at the minted coordinate (the surface seam).
  hrecipPre  : (decodeCellPre (envAt t ci)).balLo  = pre.kernel.bal cell a
  hrecipPost : (decodeCellPost (envAt t ci)).balLo = post.kernel.bal cell a
  hledgerFrame : post.kernel.bal = recTransferBal pre.kernel.bal a cell a amt
  guardAuth : Dregg2.Exec.mintAuthorizedB pre.kernel.caps actor a = true
  guardNonNeg : 0 ≤ amt
  guardLiveWell : a ∈ pre.kernel.accounts
  guardLiveCell : cell ∈ pre.kernel.accounts
  guardDistinct : a ≠ cell
  guardLifecycleLive : cellLifecycleLive pre.kernel a = true
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
  logAdv : post.log = Dregg2.Circuit.Spec.SupplyCreation.mintReceipt actor cell a amt :: pre.log

/-- **`rotatedEncodesMint_of_residual` — the decode column reads DISCHARGED.** The decode is
`mint_rowEncodes_of_designation` (the 17 column reads `rfl`, the 2 publish ties), its value slot
rewritten from `(envAt t ci).loc (prmCol VALUE_LO)` to `amt` by the residual's value-column tie `hAmt`. -/
def rotatedEncodesMint_of_residual (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {pre post : RecChainedState} {actor cell : CellId} {a : AssetId} {amt : ℤ}
    (r : MintReadoutResidual hash minit mfin maddrs t pre post actor cell a amt) :
    rotatedEncodesMint hash minit mfin maddrs t pre post actor cell a amt where
  ci := r.ci
  hci := r.hci
  hciNotLast := r.hciNotLast
  recipPre := decodeCellPre (envAt t r.ci)
  recipPost := decodeCellPost (envAt t r.ci)
  hciRow := r.hciRow
  hciEnc := by
    have h := Dregg2.Circuit.ClosureDesignationDischarge.mint_rowEncodes_of_designation
      (envAt t r.ci) r.hciOld r.hciNew
    rw [r.hAmt] at h
    exact h
  hrecipPre := r.hrecipPre
  hrecipPost := r.hrecipPost
  hledgerFrame := r.hledgerFrame
  guardAuth := r.guardAuth
  guardNonNeg := r.guardNonNeg
  guardLiveWell := r.guardLiveWell
  guardLiveCell := r.guardLiveCell
  guardDistinct := r.guardDistinct
  guardLifecycleLive := r.guardLifecycleLive
  frAccounts := r.frAccounts
  frCell := r.frCell
  frCaps := r.frCaps
  frNullifiers := r.frNullifiers
  frRevoked := r.frRevoked
  frCommitments := r.frCommitments
  frSlotCaveats := r.frSlotCaveats
  frFactories := r.frFactories
  frLifecycle := r.frLifecycle
  frDeathCert := r.frDeathCert
  frDelegate := r.frDelegate
  frDelegations := r.frDelegations
  frDelegationEpoch := r.frDelegationEpoch
  frDelegationEpochAt := r.frDelegationEpochAt
  frHeaps := r.frHeaps
  frNullifierRoot := r.frNullifierRoot
  frRevokedRoot := r.frRevokedRoot
  frCommitmentsRoot := r.frCommitmentsRoot
  logAdv := r.logAdv

/-! ## §3 — axiom hygiene. -/

#assert_axioms rotatedEncodesIncNonce_of_residual
#assert_axioms rotatedEncodesMint_of_residual

end Dregg2.Circuit.ClosureFloorReduceFanout
