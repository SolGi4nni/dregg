/-
# Dregg2.Circuit.ClosureFloorReduce — apply the column-read discharge to the carried readout floors:
the `TransferTraceReadout` decode columns are RECONSTRUCTED from the slim row designation, so the
carried floor is {StarkSound row designation + hash/Merkle CR publish ties + the genuine
ledger/frame/guard residuals}, never the mechanical `RowEncodes` decode records.

## What this lands (the loop-#4 reduction, made load-bearing)

`ClosureColumnDischarge` proved the GENERIC lemma: the 17 `RowEncodes` column reads are
`env.loc`-determined (the canonical `decodeCellPre/Params/Post` satisfy `RowEncodes` by `rfl`, modulo
the two publish ties). This module APPLIES it to the actual carried readout floor of `ClosureTransfer`:

  * `TransferReadoutResidual` — the genuine, column-free residual of `TransferTraceReadout`: the slim
    row designation (`ClosureColumnDischarge.TransferRowDesignation`), the table side-condition
    (`RotTableSide`), the LEDGER ties of the decoded limbs (`hsrcPre`/… — the surface seam, the
    `LedgerSurfaceReadout` class), and the kernel frame + side guards + log advance. NO carried
    `srcPre`/`srcPost`/`srcParams`/… records, NO carried `RowEncodes` decodes, NO `hdiDir`/`hciAmt`
    column tags — those are READ from the trace via the designation.

  * `transferTraceReadout_of_residual` — REBUILDS the full `TransferTraceReadout` from the residual:
    the decoded records are the canonical `decodeCellPre/Params/Post (envAt t ·)`, the `RowEncodes`
    decodes come from `rowEncodes_of_designation`, the dir tags from the designation's column reads.
    So `ClosureTransfer`'s carried readout floor is DISCHARGED to the residual — the column reads are
    not floor, only the designation + the named ledger/frame/guard residuals are.

The amount tags (`hdiAmt`/`hciAmt`: `srcParams.amount = tr.amt`) and the ledger ties (`hsrcPre`:
`srcPre.balLo = pre.kernel.bal tr.src a`) DO mention the kernel `tr`/`pre`/`post` — they are NOT pure
column reads; they are the LEDGER-SURFACE seam (`LedgerSurfaceReadout`, already a named realizable
floor in `ClosureTransfer`) and the receipt binding. So the residual keeps them, named — the discharge
removes ONLY the mechanical `env.loc`-determined `RowEncodes`/dir-tag fields, never the ledger seam.

## The minimal floor set, stated

After this reduction the transfer readout floor is exactly:

  `{ TransferRowDesignation (StarkSound-class row designation + publish ties)
   + RotTableSide (the chip/range table side, StarkSound-class)
   + the LEDGER ties (LedgerSurfaceReadout — the named wireCommit↔recStateCommit surface seam)
   + the kernel frame + guards + log advance (StarkSound-class trace facts) }`

— uniformly `{StarkSound + the hash/Merkle CR}`, with the `RowEncodes` limb decodes DISCHARGED. The
other 35 effects' `*Encodes` column blocks have the identical shape (column = field, `rfl`); the
uniform pattern is named in `ClosureColumnDischarge`. This module realizes it on the transfer template.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. All residual fields enter as Prop/Type
hypotheses; the column reads are `rfl` via the discharge. No `sorry`, no `native_decide`, no `:= True`,
no fresh axiom. NEW file; imports read-only.
-/
import Dregg2.Circuit.ClosureColumnDischarge
import Dregg2.Circuit.ClosureTransfer

namespace Dregg2.Circuit.ClosureFloorReduce

open Dregg2.Circuit.DescriptorIR2 (VmTrace envAt)
open Dregg2.Circuit.ClosureColumnDischarge
open Dregg2.Circuit.ClosureTransfer (TransferTraceReadout)
open Dregg2.Circuit.RotatedKernelRefinement (RotTableSide)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (IsTransferRow)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false

/-! ## §1 — `TransferReadoutResidual`: the column-free residual of `TransferTraceReadout`.

Everything in `TransferTraceReadout` EXCEPT the mechanical column reads (the decoded records, the
`RowEncodes` decodes, the direction tags — all `env.loc`-determined via the designation). The amount
tags / ledger ties keep their kernel content (the `LedgerSurfaceReadout` seam + receipt binding). -/

/-- **`TransferReadoutResidual` — the genuine, column-free carry.** The slim row designation (the rows
+ publish ties + dir tags, all read from the trace), the table side-condition, the LEDGER ties of the
canonical decoded limbs (the surface seam), the amount ties to the receipt, the kernel frame, the side
guards, and the log advance. NO `srcPre`/…/`srcParams` records, NO `RowEncodes` decodes — those are
reconstructed by reading `env.loc`. -/
structure TransferReadoutResidual (hash : List ℤ → ℤ) (t : VmTrace)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId) : Type where
  hside : RotTableSide hash t
  desig : TransferRowDesignation t
  -- the row shapes (a satisfying transfer trace exhibits them; StarkSound-class).
  hdiRow : IsTransferRow (envAt t desig.di)
  hciRow : IsTransferRow (envAt t desig.ci)
  -- the amount ties to the receipt (the decoded amount IS the turn's amount — receipt binding).
  hdiAmt : (decodeParams (envAt t desig.di)).amount = tr.amt
  hciAmt : (decodeParams (envAt t desig.ci)).amount = tr.amt
  -- the LEDGER ties of the canonical decoded limbs (the `LedgerSurfaceReadout` surface seam).
  hsrcPre  : (decodeCellPre (envAt t desig.di)).balLo  = pre.kernel.bal tr.src a
  hdstPre  : (decodeCellPre (envAt t desig.ci)).balLo  = pre.kernel.bal tr.dst a
  hsrcPost : (decodeCellPost (envAt t desig.di)).balLo = post.kernel.bal tr.src a
  hdstPost : (decodeCellPost (envAt t desig.ci)).balLo = post.kernel.bal tr.dst a
  -- the side guards (availability/liveness/distinct/accepts; NOT the cap authority — that is §3).
  guardNonNeg : 0 ≤ tr.amt
  guardDistinct : tr.src ≠ tr.dst
  guardLiveSrc : tr.src ∈ pre.kernel.accounts
  guardLiveDst : tr.dst ∈ pre.kernel.accounts
  guardAccepts : acceptsEffects pre.kernel tr.dst = true
  -- the 16 non-`bal` frame fields + the receipt-log advance.
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
  logAdv : post.log = tr :: pre.log

/-! ## §2 — `transferTraceReadout_of_residual`: REBUILD the full readout, columns discharged.

The decoded records are the canonical `decodeCellPre/Params/Post (envAt t ·)`; the `RowEncodes` decodes
are `rowEncodes_of_designation` (from the designation's publish ties); the direction tags are the
designation's column reads. So the full `TransferTraceReadout` floor `ClosureTransfer` carries is
PRODUCED from the column-free residual — the mechanical reads were never witness. -/

/-- **`transferTraceReadout_of_residual` — the readout floor, with the column reads DISCHARGED.** From
the column-free `TransferReadoutResidual` (the slim designation + the named ledger/frame/guard
residuals), produce the full `TransferTraceReadout` `ClosureTransfer` consumes. The decoded
`CellState`/`TransferParams` and their `RowEncodes` decodes come from the column-read discharge
(`ClosureColumnDischarge`), NOT from the carried floor. This is the reduction realized on the transfer
template: the carried readout = {row designation + publish ties + the ledger/frame/guard residuals}. -/
def transferTraceReadout_of_residual (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (r : TransferReadoutResidual hash t pre post tr a) :
    TransferTraceReadout hash minit mfin maddrs t pre post tr a where
  hside := r.hside
  di := r.desig.di
  ci := r.desig.ci
  hdi := r.desig.hdi
  hci := r.desig.hci
  srcPre := decodeCellPre (envAt t r.desig.di)
  srcPost := decodeCellPost (envAt t r.desig.di)
  dstPre := decodeCellPre (envAt t r.desig.ci)
  dstPost := decodeCellPost (envAt t r.desig.ci)
  srcParams := decodeParams (envAt t r.desig.di)
  dstParams := decodeParams (envAt t r.desig.ci)
  hdiRow := r.hdiRow
  hciRow := r.hciRow
  -- the `RowEncodes` decodes: the GENERIC column-read discharge (rfl columns + the publish ties).
  hdiEnc := rowEncodes_of_designation (envAt t r.desig.di) r.desig.hdiOld r.desig.hdiNew
  hciEnc := rowEncodes_of_designation (envAt t r.desig.ci) r.desig.hciOld r.desig.hciNew
  -- the direction tags: the designation's column reads (decodeParams.direction).
  hdiDir := r.desig.hdiDir
  hciDir := r.desig.hciDir
  hdiAmt := r.hdiAmt
  hciAmt := r.hciAmt
  guardNonNeg := r.guardNonNeg
  guardDistinct := r.guardDistinct
  guardLiveSrc := r.guardLiveSrc
  guardLiveDst := r.guardLiveDst
  guardAccepts := r.guardAccepts
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
  logAdv := r.logAdv

/-! ## §3 — axiom hygiene. -/

#assert_axioms transferTraceReadout_of_residual

end Dregg2.Circuit.ClosureFloorReduce
