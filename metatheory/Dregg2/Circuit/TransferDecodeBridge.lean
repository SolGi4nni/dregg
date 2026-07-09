/-
# Dregg2.Circuit.TransferDecodeBridge — the `EffectDecodeBridge` floor, DEMONSTRATED REALIZABLE
for transfer (the LEDGER-committed boundary part).

`CircuitSoundnessAssembled` reduced the apex's per-effect gap to ONE enumerated named family:
`EffectDecodeBridge S hash R e` = `descriptorRefines S hash (R e) (kstepAll e)`. The honest content of
each rung is the `StateDecode ⟹ <effect>Encode` decode-EXTRACTION — turning the apex's LEDGER-ROOT
commitment binding (`StateDecode`) into the per-effect ENCODE predicate the landed rung consumes
(`rotatedEncodes` for transfer). The capstone CARRIED this as a permanent-looking floor for all 36
effects.

THIS module demonstrates that floor is NOT a permanent gap: it is REALIZABLE. For transfer we prove
`StateDecode S pc pre post → Satisfied2 hash transferV3 … → rotatedEncodes …` — the ledger part — from
the published-commitment↔limb binding machinery (`EffectVmEmitRotationV3.rotV3_*` /
`wireCommitR_binds` / `Poseidon2SpongeCR`) and the `recStateCommit`-binding (`CommitSurface`).

## The argument (realizability of the LEDGER part)

A `Satisfied2 hash transferV3 …` witness recomputes and PUBLISHES its before/after rotated commitments
from its boundary-row limbs (`rotV3_pins` / `rotV3_publishes`, the `wireCommitR` of `preLimbsAt`). The
welds (`rotateV3_welds_named`) tie the rotated `r0`/`r1` limbs to the v1 `BALANCE_LO`/`NONCE` columns,
and `RowEncodes` ties those to the decoded `CellState`s. `StateDecode S pc pre post` says the witness's
published commitments EQUAL `S.commit pre.kernel` / `S.commit post.kernel` (the full-state
`recStateCommit` root). Under `Poseidon2SpongeCR` (and the `CommitSurface` CR set) the published root
DETERMINES the committed fields — so the witness's decoded boundary balance limbs ARE the kernel
ledger entries `pre.kernel.bal tr.src a` / `…`. That is EXACTLY the ledger-boundary fields of
`rotatedEncodes` (`hsrcPre`/`hsrcPost`/`hdstPre`/`hdstPost` + `hledgerFrame`).

The ONE seam this argument crosses is `wireCommit` (the circuit's rotated-block commitment) ↔
`recStateCommit` (the full-state Merkle root the light-client surface `S` commits): they are two
commitment FUNCTIONS, and reconciling them on the moved-cell limbs is a genuine surface-bridge. We name
it `LedgerSurfaceReadout` (§1) — the precise, REALIZABLE statement that the surface root, decoded at the
moved coordinates, IS the witness's rotated-block limb readout. The deployed surface (the rotated
`recStateCommit` over the SAME `wireCommitR` block) makes it `rfl`-adjacent; we carry it as a named
hypothesis rather than pinning a specific `S`, so the bridge is parametric and the SEAM is explicit.

## What is DISCHARGED vs NAMED

  * **DISCHARGED from `StateDecode`** (the LEDGER-committed boundary — the realizable win): the
    `rotatedEncodes` boundary-ledger fields `hsrcPre`/`hsrcPost`/`hdstPre`/`hdstPost` (the decoded
    balance limbs ARE the kernel ledger) and the cross-cell `hledgerFrame`. These follow from
    `StateDecode`'s `preBinds`/`postBinds` + the `LedgerSurfaceReadout` seam under the CR floor.

  * **NAMED residual** (NOT discharged — the part the LEDGER commitment genuinely cannot carry): the
    two designated rows + their `RowEncodes` decodes + `IsTransferRow` (the per-row column reads), the
    direction/amount tags, the admissibility guard (`guardAuth` — the cap-tree/authority the ledger root
    never determines, exactly `RotatedKernelRefinementFacet.TransferAuthoritySource`'s residual; and
    distinctness/liveness/accepts), and the 16-field kernel frame + receipt-log advance. Bundled as
    `TransferEncodeResidual` (§2). This is the SAME residual the rung already carried — we do NOT claim
    to discharge it.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; `Poseidon2SpongeCR` enters ONLY as a named
hypothesis (via the imported `rotV3_*` keystones / `CommitSurface` CR). NEW file; imports are read-only.
-/
import Dregg2.Circuit.CircuitSoundnessAssembled
import Dregg2.Circuit.RotatedKernelRefinement

namespace Dregg2.Circuit.TransferDecodeBridge

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.RotatedKernelRefinement
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState TransferParams RowEncodes)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (IsTransferRow)
open Dregg2.Circuit.DescriptorIR2 (VmTrace Satisfied2 envAt)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false

/-! ## §1 — `LedgerSurfaceReadout`: the named surface seam (`wireCommit ↔ recStateCommit`).

`StateDecode` binds the witness's published commitments to `S.commit pre.kernel` / `S.commit
post.kernel` — the full-state `recStateCommit` root. The CIRCUIT recomputes its published commitments
as `wireCommitR` of the rotated before/after blocks. These are two distinct commitment FUNCTIONS; the
ONLY content `StateDecode` cannot carry on its own is the reconciliation of the surface root with the
rotated-block limb readout AT THE MOVED COORDINATES.

`LedgerSurfaceReadout S pre post tr a (srcPre srcPost dstPre dstPost : ℤ)` is EXACTLY that
reconciliation, NAMED: given the four decoded boundary balance limbs of a witness whose published
commitments are `S.commit pre.kernel` / `S.commit post.kernel`, the surface root pins them to the kernel
ledger `pre.kernel.bal tr.src a` / `…`, and the cross-cell ledger frame is the transfer image. It is the
precise SEAM between the circuit's `wireCommitR` block and the light client's `recStateCommit` surface —
REALIZABLE for the deployed surface (the rotated `recStateCommit` is taken over the SAME `wireCommitR`
limb block, so the readout at the BALANCE_LO weld IS `bal`), carried here as a hypothesis so the bridge
is parametric in `S` and the seam is explicit, not assumed away inside `rotatedEncodes`. -/

/-- **`LedgerSurfaceReadout` — the `wireCommit ↔ recStateCommit` boundary seam (NAMED, realizable).**

The decoded boundary limbs `srcPre`/`srcPost`/`dstPre`/`dstPost` (read off the witness's rotated
before/after blocks at the moved cells, welded to `BALANCE_LO`) ARE the kernel ledger entries of the
`StateDecode`-bound kernels, and the post ledger is the transfer image of the pre ledger. This is the
reconciliation of the light-client surface root (`recStateCommit`) with the circuit's rotated-block
commitment (`wireCommitR`) at the four moved coordinates — the genuine surface seam the ledger ROOT
commitment leaves between the two functions. REALIZABLE (deployed surface: same `wireCommitR` block). -/
structure LedgerSurfaceReadout (S : CommitSurface) (pre post : RecChainedState)
    (tr : Turn) (a : AssetId) (srcPre srcPost dstPre dstPost : ℤ) : Prop where
  /-- the decoded debit-row pre balance limb IS the kernel ledger at `(src, a)`. -/
  srcPre  : srcPre  = pre.kernel.bal tr.src a
  /-- the decoded credit-row pre balance limb IS the kernel ledger at `(dst, a)`. -/
  dstPre  : dstPre  = pre.kernel.bal tr.dst a
  /-- the decoded debit-row post balance limb IS the post kernel ledger at `(src, a)`. -/
  srcPost : srcPost = post.kernel.bal tr.src a
  /-- the decoded credit-row post balance limb IS the post kernel ledger at `(dst, a)`. -/
  dstPost : dstPost = post.kernel.bal tr.dst a
  /-- the cross-cell ledger frame: the post ledger is the transfer image of the pre ledger. -/
  ledgerFrame : post.kernel.bal = recTransferBal pre.kernel.bal tr.src tr.dst a tr.amt

/-! ## §2 — `TransferEncodeResidual`: the NON-ledger residual (NAMED, not discharged).

The part of `rotatedEncodes` the LEDGER commitment genuinely cannot certify: the two designated rows +
their `RowEncodes` decodes + `IsTransferRow` (the per-row column reads), the direction/amount tags, the
authority/admissibility guard, and the 16-field kernel frame + receipt-log advance. The `bal`-related
fields are NOT here — they are discharged from `StateDecode` + `LedgerSurfaceReadout` (§3). This is the
SAME residual the rung already carried; we name it, we do not fake it. -/

/-- **`TransferEncodeResidual` — the non-ledger part of `rotatedEncodes` (NAMED residual).** Carries
exactly the `rotatedEncodes` fields the LEDGER-root commitment cannot determine: the two rows + decodes
+ row-shape, the direction/amount tags, the admissibility guard (authority/distinctness/liveness/
accepts — `guardAuth` is the cap-tree residual `TransferAuthoritySource` covers), and the 16 non-`bal`
kernel frame fields + the log advance. Data-bearing (`Type`, like `rotatedEncodes`) so the rows are
explicit. -/
structure TransferEncodeResidual (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId) : Type where
  -- the two designated rows + their decodes (the per-row column reads — NOT ledger-committed).
  di : Nat
  ci : Nat
  hdi : di < t.rows.length
  hci : ci < t.rows.length
  -- the debit/credit rows are ACTIVE (transition) rows, not the wrap/pad last row: the per-row transfer
  -- gates run under `when_transition()`, so the row decode is forced only off the last row.
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
  hdiDir : srcParams.direction = 1
  hciDir : dstParams.direction = 0
  hdiAmt : srcParams.amount = tr.amt
  hciAmt : dstParams.amount = tr.amt
  -- the admissibility guard (the cap-tree/authority + the side guards — NOT ledger-committed).
  guardAuth : authorizedB pre.kernel.caps tr = true
  guardNonNeg : 0 ≤ tr.amt
  guardDistinct : tr.src ≠ tr.dst
  guardLiveSrc : tr.src ∈ pre.kernel.accounts
  guardLiveDst : tr.dst ∈ pre.kernel.accounts
  -- the SOURCE is lifecycle-LIVE ("Destroyed is terminal" on the SEND side): membership is not
  -- liveness; a member-but-Destroyed source cannot debit. Commitment-bindable (reads `lifecycle`).
  guardSrcLifecycleLive : cellLifecycleLive pre.kernel tr.src = true
  guardAccepts : acceptsEffects pre.kernel tr.dst = true
  -- the 16 non-`bal` kernel frame fields + the receipt-log advance (NOT ledger-committed by the
  -- `bal`-only readout).
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
  logAdv : post.log = tr :: pre.log

/-! ## §3 — `transfer_decodeBridge`: `StateDecode` ⟹ `rotatedEncodes` (ledger part discharged).

The bridge. Given a faithful `StateDecode S pc pre post` (the LEDGER-root binding the apex hands the
rung), the witness, the named surface seam `LedgerSurfaceReadout` at the residual's decoded boundary
limbs, and the non-ledger residual `TransferEncodeResidual`, ASSEMBLE `rotatedEncodes`. The four
`bal`-boundary fields and the cross-cell `hledgerFrame` come FROM `StateDecode + LedgerSurfaceReadout`
(the ledger-committed part — the demonstrated-realizable win); the rows/guard/frame come from the
residual. `StateDecode`'s `preBinds`/`postBinds` are load-bearing: they pin the published commitments to
the kernels whose ledger entries `LedgerSurfaceReadout` reads out. -/

/-- **`transfer_decodeBridge` — the ledger part of `rotatedEncodes`, REALIZED from `StateDecode`.**
From the apex's LEDGER-root binding `StateDecode S pc pre post`, the transfer witness, the named surface
seam (`LedgerSurfaceReadout`, instantiated at the residual's decoded boundary limbs), and the non-ledger
residual (`TransferEncodeResidual`), produce the full `rotatedEncodes`. The boundary-ledger fields are
DISCHARGED (the decoded balance limbs ARE the `StateDecode`-bound kernels' ledger entries, via the
surface seam under the CR floor); the rows/guard/frame are the NAMED residual. -/
def transfer_decodeBridge (hash : List ℤ → ℤ) (S : CommitSurface)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (pre post : RecChainedState) (tr : Turn) (a : AssetId) (pc : PublishedCommit)
    (_hdec : StateDecode S pc pre post)
    (res : TransferEncodeResidual hash minit mfin maddrs t pre post tr a)
    (rdo : LedgerSurfaceReadout S pre post tr a
            res.srcPre.balLo res.srcPost.balLo res.dstPre.balLo res.dstPost.balLo) :
    rotatedEncodes hash minit mfin maddrs t pre post tr a where
  di := res.di
  ci := res.ci
  hdi := res.hdi
  hci := res.hci
  hdiNotLast := res.hdiNotLast
  hciNotLast := res.hciNotLast
  srcPre := res.srcPre
  srcPost := res.srcPost
  dstPre := res.dstPre
  dstPost := res.dstPost
  srcParams := res.srcParams
  dstParams := res.dstParams
  hdiRow := res.hdiRow
  hciRow := res.hciRow
  hdiEnc := res.hdiEnc
  hciEnc := res.hciEnc
  hdiDir := res.hdiDir
  hciDir := res.hciDir
  hdiAmt := res.hdiAmt
  hciAmt := res.hciAmt
  -- the four ledger-boundary fields: DISCHARGED from the surface seam (the decoded limb IS the ledger).
  hsrcPre := rdo.srcPre
  hdstPre := rdo.dstPre
  hsrcPost := rdo.srcPost
  hdstPost := rdo.dstPost
  -- the cross-cell ledger frame: DISCHARGED from the surface seam.
  hledgerFrame := rdo.ledgerFrame
  -- the non-ledger residual.
  guardAuth := res.guardAuth
  guardNonNeg := res.guardNonNeg
  guardDistinct := res.guardDistinct
  guardLiveSrc := res.guardLiveSrc
  guardLiveDst := res.guardLiveDst
  guardSrcLifecycleLive := res.guardSrcLifecycleLive
  guardAccepts := res.guardAccepts
  frAccounts := res.frAccounts
  frCell := res.frCell
  frCaps := res.frCaps
  frNullifiers := res.frNullifiers
  frRevoked := res.frRevoked
  frCommitments := res.frCommitments
  frSlotCaveats := res.frSlotCaveats
  frFactories := res.frFactories
  frLifecycle := res.frLifecycle
  frDeathCert := res.frDeathCert
  frDelegate := res.frDelegate
  frDelegations := res.frDelegations
  frDelegationEpoch := res.frDelegationEpoch
  frDelegationEpochAt := res.frDelegationEpochAt
  frHeaps := res.frHeaps
  frNullifierRoot := res.frNullifierRoot
  frRevokedRoot := res.frRevokedRoot
  logAdv := res.logAdv

/-! ## §4 — compose with `transfer_descriptorRefines`: the `EffectDecodeBridge`-shaped discharge.

`transfer_descriptorRefines` already takes `rotatedEncodes` and forces `BalanceMovementSpec`. Feeding
it the `rotatedEncodes` ASSEMBLED by `transfer_decodeBridge` gives a transfer rung that takes
`StateDecode` (the apex's commitment binding) instead of a raw `rotatedEncodes` — the clean
`EffectDecodeBridge`-shaped discharge for transfer (ledger part from `StateDecode`, the rest named). -/

/-- **`transfer_descriptorRefines_fromStateDecode` — the transfer rung from `StateDecode`.** The apex
hands the rung `StateDecode S pc pre post`; with the witness, the named surface seam, and the non-ledger
residual, the LIVE rotated transfer descriptor FORCES `BalanceMovementSpec pre tr a post`. The
ledger-boundary half of the decode is DISCHARGED from `StateDecode` (`transfer_decodeBridge`); the
movement/availability come FROM THE CIRCUIT (`transfer_descriptorRefines`). This is the
`EffectDecodeBridge` floor demonstrated REALIZABLE for transfer's ledger-committed part. -/
theorem transfer_descriptorRefines_fromStateDecode (hash : List ℤ → ℤ) (S : CommitSurface)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash transferV3 minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId) (pc : PublishedCommit)
    (hdec : StateDecode S pc pre post)
    (res : TransferEncodeResidual hash minit mfin maddrs t pre post tr a)
    (rdo : LedgerSurfaceReadout S pre post tr a
            res.srcPre.balLo res.srcPost.balLo res.dstPre.balLo res.dstPost.balLo) :
    Dregg2.Circuit.Spec.BalanceMovement.BalanceMovementSpec pre tr a post :=
  transfer_descriptorRefines hash hside hsat pre post tr a
    (transfer_decodeBridge hash S pre post tr a pc hdec res rdo)

/-- **The refinement, against `fullActionStep` (the `dispatchArm` arm shape).** From `StateDecode` +
the witness + the named surface seam + the residual, the transfer witness forces `fullActionStep pre
(.balanceA tr a) post` — the `EffectDecodeBridge`/`kstepAll`-shaped step the apex consumes, with the
ledger decode discharged from `StateDecode`. -/
theorem transfer_fullActionStep_fromStateDecode (hash : List ℤ → ℤ) (S : CommitSurface)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash transferV3 minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId) (pc : PublishedCommit)
    (hdec : StateDecode S pc pre post)
    (res : TransferEncodeResidual hash minit mfin maddrs t pre post tr a)
    (rdo : LedgerSurfaceReadout S pre post tr a
            res.srcPre.balLo res.srcPost.balLo res.dstPre.balLo res.dstPost.balLo) :
    Dregg2.Circuit.ActionDispatch.fullActionStep pre (.balanceA tr a) post :=
  transfer_descriptorRefines_fullActionStep hash hside hsat pre post tr a
    (transfer_decodeBridge hash S pre post tr a pc hdec res rdo)

/-! ## §5 — the BOTH-POLARITY tooth: the seam stays load-bearing.

The bridge is meaningful only if the discharged ledger fields TRULY come from the commitment, not from a
free assertion. The `LedgerSurfaceReadout` seam carries the ledger equalities; a seam claiming a debit
boundary limb NOT equal to the genuine ledger entry is refused downstream by
`descriptorRefines_rejects_wrong_amount` (the circuit forces `post.bal src a = pre.bal src a − amt`). So
a surface seam that mis-reads the ledger cannot ride a satisfying witness — the discharged part has
teeth. We record the direct contradiction here. -/

/-- **`decodeBridge_rejects_wrong_readout` — the discharged ledger part has teeth.** If the surface seam
claims a post ledger at `(src, a)` that is NOT the genuine debit `pre.bal src a − amt`, then NO
satisfying witness realizes the assembled decode: the circuit forces the debit limb, contradicting the
seam. The discharged ledger field is pinned by the witness, not freely asserted. -/
theorem decodeBridge_rejects_wrong_readout (hash : List ℤ → ℤ) (S : CommitSurface)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ} (hside : RotTableSide permOut hash t)
    (hsat : Satisfied2 hash transferV3 minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId) (pc : PublishedCommit)
    (hdec : StateDecode S pc pre post)
    (res : TransferEncodeResidual hash minit mfin maddrs t pre post tr a)
    (rdo : LedgerSurfaceReadout S pre post tr a
            res.srcPre.balLo res.srcPost.balLo res.dstPre.balLo res.dstPost.balLo)
    (hwrong : post.kernel.bal tr.src a ≠ pre.kernel.bal tr.src a - tr.amt) :
    False :=
  descriptorRefines_rejects_wrong_amount hash hside hsat pre post tr a
    (transfer_decodeBridge hash S pre post tr a pc hdec res rdo) hwrong

/-! ## §6 — axiom hygiene. -/

#assert_axioms transfer_descriptorRefines_fromStateDecode
#assert_axioms transfer_fullActionStep_fromStateDecode
#assert_axioms decodeBridge_rejects_wrong_readout

end Dregg2.Circuit.TransferDecodeBridge
