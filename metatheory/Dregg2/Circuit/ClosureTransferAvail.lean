/-
# Dregg2.Circuit.ClosureTransferAvail — the transfer closure slot ON THE HARDENED (DEPLOYED) PATH:
`availOf` DISCHARGED, not carried.

## What this module is

`ClosureTransfer.closedLogExtract_transfer_closed` discharges the transfer slot of `ClosedLogExtract`
at `Rfix 0` — and there it must CARRY availability (`availOf : tr.amt ≤ pre.kernel.bal tr.src a`) as a
named per-witness residual, because `Rfix 0 = CarrierComposed.transferV3Membership` peels to the BARE
rotated face `transferV3 = v3OfFrozen transferVmDescriptor`, whose mod-`p` balance gate + 30-bit range
check do NOT force `amt ≤ bal` (the underflow-wrap mint-from-nothing,
`docs/FINDING-modp-wrap-forgery-audit.md` forgery 1).

That gap is CLOSED IN THE DEPLOYED CIRCUIT. The wire registries
(`WIDE_REGISTRY_STAGED_TSV` / `WIDE_UMEM_WELD_REGISTRY_TSV`) route the transfer keys to the HARDENED
availability faces (borrow-limb decomposition + 15-bit range teeth + a no-final-borrow gate), and
`RotatedKernelRefinementAvailWide` proves the discharge on the EXACT wire objects
(`availability_and_exact_move_forced_weldedWide` — a satisfying welded-crown witness FORCES
`tr.amt ≤ pre.kernel.bal tr.src a` AND the EXACT ℤ debit).

This module carries that discharge UP TO THE CLOSURE: the transfer slot of `ClosedLogExtract`, stated
over a registry whose transfer entry IS the deployed hardened member
(`EffectVmEmitUMemWeldWide.weldedTransferAvailWide`), with availability a THEOREM, not a hypothesis.

  * **`TransferTraceReadoutAvail`** — the hardened column+frame readout floor. Field-for-field the
    `ClosureTransfer.TransferTraceReadout` floor (`.toReadout` projects onto it) with TWO deltas: the
    table side is the multi-width `RotTableSideW` (the hardened face's 15-bit teeth live in the 15-bit
    table), and it carries the debit row's field-CANONICALITY envelope `hdiCanon` (`0 ≤ loc c < p`, the
    deployed canonical-element invariant the verifier's field decoding supplies — WIDTH-only; it says
    nothing about order, so availability is NOT laundered in through it: the ORDER comes from the borrow
    gates via `transferAvail_derives_availability_row`).
  * **`rotatedEncodesAvail_of_floors`** — assemble the hardened decode from {readout, ledger seam,
    cap-open-projected authority}. NOTE the missing argument: NO `havail`.
  * **`transfer_descriptorRefinesAvail_closedLog`** — the closed-with-log rung on the welded wide crown.
  * **`closedLogExtract_transfer_closed_avail`** — THE SLOT: `ClosedLogExtract S_live LH hash R 0` for any
    registry `R` with `R 0 = weldedTransferAvailWide`. Carried floors: EXACTLY
    {`TransferTraceReadoutAvail`, `LedgerSurfaceReadout`, `TransferAuthorityWitness` + its toy-tier
    projection} — the `availOf` residual is GONE, replaced by `availability_forced_weldedWide`.
  * **`closure_rejects_overdebit_avail`** — the tooth: an over-debit readout riding a satisfying
    closure witness is UNSAT (the discharge is real, not a deletion).

§6 closes the SIBLING slot of the same class: **burn** (tag 4). `ClosureFanoutGenuine`'s burn slot
carries availability too — not as a separate `availOf` but INSIDE its decode
(`rotatedEncodesBurn.guardAvail`, the well-supply-inflation forgery 2). Over the deployed hardened burn
member (`weldedBurnAvailWide`) the readout floor supplies `rotatedEncodesBurnAvail`, which has NO
`guardAvail` field: `closedLogExtract_burn_closed_avail` asserts no availability anywhere, and
`closure_rejects_overburn_avail` is the tooth. Mint/setField/the cap-family slots carry NO availability
leg (they debit no balance), so the class is exactly these two.

## What is NOT closed here (and is NOT this module's residual)

  1. **The `Rfix` retarget — LANDED at the CONFIG apex** (`Dregg2.Circuit.ClosureFinalAvail`). `RfixAvail`
     (§5) is `Rfix` with EXACTLY the two debiting tags flipped to the deployed hardened members
     (`RfixAvail 0 = weldedTransferAvailWide`, `RfixAvail 4 = weldedBurnAvailWide`, every other tag `Rfix`
     verbatim by `RfixAvail_off`). `ClosureFinalAvail.lightclient_unfoolable_closed_final_avail` is the
     closed circuit-soundness apex over `RfixAvail`: its transfer/burn slots consume THIS module's `_avail`
     slots (`closedLogExtract_transfer_closed_availFix` / `closedLogExtract_burn_closed_availFix`), so
     `availOf` is DISCHARGED at the apex — the deployed borrow chain FORCES `amt ≤ bal` at the descriptor
     the light client verifies. (`CircuitSoundnessAssembled.Rfix` itself is deliberately UNCHANGED: it
     remains the bare-face registry the STARK-side `algoStarkSound_kernel` enumerates, and `Rfix 0 =
     transferV3Membership` is a load-bearing `rfl` — the flip is the parallel `RfixAvail`, not a mutation.)
     The remaining item is the STARK-SIDE re-key: building `[StarkSound hash RfixAvail]` from the
     enumerated floor is NOT a mem-free `side_transfer`/`side_burn` mirror, because the welded members
     append a `.umemOp` (`MapShape` provably fails — the `setFieldDynV3_not_mapShape` class), so they route
     through `algoStarkSound_of_memoryLegs` with a umem memory-checking leg (a separate, floor-expanding
     lane). At the apex altitude the STARK extraction is the allowed realizable floor, exactly as the
     `Rfix` apex carries `[StarkSound hash Rfix]`.
  2. **The cap-open authority witness** (`TransferAuthorityWitness`/`toyAuthOf`) — a SEPARATE open seam
     (the authority rides a different descriptor), untouched here.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`. NEW file; imports read-only.
-/
import Dregg2.Circuit.ClosureTransfer
import Dregg2.Circuit.RotatedKernelRefinementAvailWide
import Dregg2.Circuit.RotatedKernelRefinementMintBurnAvailWide

namespace Dregg2.Circuit.ClosureTransferAvail

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.CircuitSoundnessAssembled
open Dregg2.Circuit.ClosureAll
open Dregg2.Circuit.ClosureTransfer (TransferTraceReadout TransferAuthorityWitness
  authWitness_forces_faithful)
open Dregg2.Circuit.RotatedKernelRefinement (RotTableSide)
open Dregg2.Circuit.RotatedKernelRefinementAvail (RotTableSideW rotatedEncodesAvail)
open Dregg2.Circuit.RotatedKernelRefinementAvailWide (availability_forced_weldedWide
  transfer_descriptorRefinesAvail_weldedWide weldedWide_rejects_overdebit)
open Dregg2.Circuit.RotatedKernelRefinementMintBurnAvail (rotatedEncodesBurnAvail)
open Dregg2.Circuit.RotatedKernelRefinementMintBurnAvailWide (wideBurn_availability_forced
  burn_descriptorRefinesAvail_weldedWide weldedBurnWide_rejects_overburn)
open Dregg2.Circuit.Emit.EffectVmEmitUMemWeldWide (weldedTransferAvailWide weldedBurnAvailWide)
open Dregg2.Circuit.TransferDecodeBridge (LedgerSurfaceReadout)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.StateCommit (compressInjective compressNInjective cellLeafInjective
  RestHashIffFrame logHashInjective)
open Dregg2.Circuit.ClosureSurface (S_live)
open Dregg2.Circuit.ClosureLog (StateDecodeLog)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState TransferParams RowEncodes)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (IsTransferRow)
open Dregg2.Circuit.DescriptorIR2 (VmTrace Satisfied2 envAt)
open Dregg2.Circuit.Spec.BalanceMovement (BalanceMovementSpec)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false

/-! ## §1 — `TransferTraceReadoutAvail`: the HARDENED column+frame readout floor.

The same `WitnessDecodes`-class circuit-witness extraction `ClosureTransfer.TransferTraceReadout` names
(the two designated boundary rows + their `RowEncodes` decodes + row-shape/dir/amount tags + the table
side + the 16 non-`bal` frame fields + the side guards + the receipt-log prepend), on the HARDENED face:

  * the table side is `RotTableSideW` (per-width range tables — the hardened face's 15-bit borrow teeth
    lower into the 15-bit table; `RotTableSideW.toRotTableSide` projects back to the bare 30-bit pin, so
    this is a STRENGTHENING of the same floor, not a new class);
  * plus `hdiCanon`, the debit row's field-canonicality envelope — the deployed canonical-element
    invariant (every column holds a canonical BabyBear residue), WIDTH-only.

It carries NO availability leg. -/

/-- **`TransferTraceReadoutAvail` — the hardened circuit-witness column+frame extraction (NAMED,
realizable).** The `TransferTraceReadout` floor over the multi-width table side, plus the debit row's
canonical-element envelope. Availability is NOT a field: it is FORCED from the witness
(`availability_forced_weldedWide`). Data-bearing (`Type`) so the rows are explicit. -/
structure TransferTraceReadoutAvail (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId) : Type where
  -- the genuine deployed chip permutation the faithful table side rides.
  permOut : List ℤ → List ℤ
  -- the MULTI-WIDTH table faithfulness the hardened rotated denotation requires (chip + per-width
  -- range tables — the 15-bit borrow-limb table the availability weld realizes).
  hsideW : RotTableSideW permOut hash t
  -- the two designated rows + their decodes (the per-row column reads).
  di : Nat
  ci : Nat
  hdi : di < t.rows.length
  hci : ci < t.rows.length
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
  -- THE CANONICALITY ENVELOPE (the deployed field-decoding invariant; WIDTH-only — it constrains no
  -- ORDER, so availability is not smuggled in here: the borrow gates force the order).
  hdiCanon : ∀ c, 0 ≤ (envAt t di).loc c ∧ (envAt t di).loc c < 2013265921
  hdiDir : srcParams.direction = 1
  hciDir : dstParams.direction = 0
  hdiAmt : srcParams.amount = tr.amt
  hciAmt : dstParams.amount = tr.amt
  -- the side guards (liveness/distinct/accepts; NO availability — that is circuit-forced; NOT the cap
  -- authority — that rides the cap-open witness).
  guardNonNeg : 0 ≤ tr.amt
  guardDistinct : tr.src ≠ tr.dst
  guardLiveSrc : tr.src ∈ pre.kernel.accounts
  guardLiveDst : tr.dst ∈ pre.kernel.accounts
  guardSrcLifecycleLive : cellLifecycleLive pre.kernel tr.src = true
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
  frNullifierRoot : post.kernel.nullifierRoot = pre.kernel.nullifierRoot
  frRevokedRoot : post.kernel.revokedRoot = pre.kernel.revokedRoot
  frCommitmentsRoot : post.kernel.commitmentsRoot = pre.kernel.commitmentsRoot
  logAdv : post.log = tr :: pre.log

/-- The hardened readout PROJECTS onto the bare `TransferTraceReadout` floor (`RotTableSideW` projects
to `RotTableSide` at the 30-bit pin). So the hardened slot asks for the SAME named floor class as
`ClosureTransfer`, strengthened by the deployed per-width tables + the canonicality envelope — it does
not open a new residual. -/
def TransferTraceReadoutAvail.toReadout {hash : List ℤ → ℤ}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {pre post : RecChainedState} {tr : Turn} {a : AssetId}
    (rd : TransferTraceReadoutAvail hash minit mfin maddrs t pre post tr a) :
    TransferTraceReadout hash minit mfin maddrs t pre post tr a :=
  { permOut := rd.permOut
    hside := rd.hsideW.toRotTableSide
    di := rd.di, ci := rd.ci, hdi := rd.hdi, hci := rd.hci
    hdiNotLast := rd.hdiNotLast, hciNotLast := rd.hciNotLast
    srcPre := rd.srcPre, srcPost := rd.srcPost, dstPre := rd.dstPre, dstPost := rd.dstPost
    srcParams := rd.srcParams, dstParams := rd.dstParams
    hdiRow := rd.hdiRow, hciRow := rd.hciRow
    hdiEnc := rd.hdiEnc, hciEnc := rd.hciEnc
    hdiDir := rd.hdiDir, hciDir := rd.hciDir
    hdiAmt := rd.hdiAmt, hciAmt := rd.hciAmt
    guardNonNeg := rd.guardNonNeg, guardDistinct := rd.guardDistinct
    guardLiveSrc := rd.guardLiveSrc, guardLiveDst := rd.guardLiveDst
    guardSrcLifecycleLive := rd.guardSrcLifecycleLive, guardAccepts := rd.guardAccepts
    frAccounts := rd.frAccounts, frCell := rd.frCell, frCaps := rd.frCaps
    frNullifiers := rd.frNullifiers, frRevoked := rd.frRevoked
    frCommitments := rd.frCommitments, frSlotCaveats := rd.frSlotCaveats
    frFactories := rd.frFactories, frLifecycle := rd.frLifecycle
    frDeathCert := rd.frDeathCert, frDelegate := rd.frDelegate
    frDelegations := rd.frDelegations, frDelegationEpoch := rd.frDelegationEpoch
    frDelegationEpochAt := rd.frDelegationEpochAt, frHeaps := rd.frHeaps
    frNullifierRoot := rd.frNullifierRoot, frRevokedRoot := rd.frRevokedRoot
    frCommitmentsRoot := rd.frCommitmentsRoot
    logAdv := rd.logAdv }

/-! ## §2 — assemble the HARDENED decode from the floors (NO availability argument). -/

/-- **`rotatedEncodesAvail_of_floors` — the hardened decode from the three named floors.** Column reads
+ frame + side guards from `TransferTraceReadoutAvail`; the four ledger limbs + `hledgerFrame` from the
surface seam `LedgerSurfaceReadout`; the toy authority from the cap-open-forced fact. Compare
`ClosureTransfer.rotatedEncodes_of_floors`: THE `havail` ARGUMENT IS GONE — the hardened decode has no
`guardAvail` field, and availability is recovered from the witness downstream. -/
def rotatedEncodesAvail_of_floors (hash : List ℤ → ℤ) (S : CommitSurface)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (rd : TransferTraceReadoutAvail hash minit mfin maddrs t pre post tr a)
    (rdo : LedgerSurfaceReadout S pre post tr a
            rd.srcPre.balLo rd.srcPost.balLo rd.dstPre.balLo rd.dstPost.balLo)
    (htoyAuth : authorizedB pre.kernel.caps tr = true) :
    rotatedEncodesAvail hash minit mfin maddrs t pre post tr a where
  di := rd.di
  ci := rd.ci
  hdi := rd.hdi
  hci := rd.hci
  hdiNotLast := rd.hdiNotLast
  hciNotLast := rd.hciNotLast
  srcPre := rd.srcPre
  srcPost := rd.srcPost
  dstPre := rd.dstPre
  dstPost := rd.dstPost
  srcParams := rd.srcParams
  dstParams := rd.dstParams
  hdiRow := rd.hdiRow
  hciRow := rd.hciRow
  hdiEnc := rd.hdiEnc
  hciEnc := rd.hciEnc
  hdiCanon := rd.hdiCanon
  hdiDir := rd.hdiDir
  hciDir := rd.hciDir
  hdiAmt := rd.hdiAmt
  hciAmt := rd.hciAmt
  -- the four ledger-boundary fields + frame: from the surface seam (the decoded limb IS the ledger).
  hsrcPre := rdo.srcPre
  hdstPre := rdo.dstPre
  hsrcPost := rdo.srcPost
  hdstPost := rdo.dstPost
  hledgerFrame := rdo.ledgerFrame
  -- the authority: cap-open-forced (projected to the toy gate the rung field expects).
  guardAuth := htoyAuth
  guardNonNeg := rd.guardNonNeg
  guardDistinct := rd.guardDistinct
  guardLiveSrc := rd.guardLiveSrc
  guardLiveDst := rd.guardLiveDst
  guardSrcLifecycleLive := rd.guardSrcLifecycleLive
  guardAccepts := rd.guardAccepts
  frAccounts := rd.frAccounts
  frCell := rd.frCell
  frCaps := rd.frCaps
  frNullifiers := rd.frNullifiers
  frRevoked := rd.frRevoked
  frCommitments := rd.frCommitments
  frSlotCaveats := rd.frSlotCaveats
  frFactories := rd.frFactories
  frLifecycle := rd.frLifecycle
  frDeathCert := rd.frDeathCert
  frDelegate := rd.frDelegate
  frDelegations := rd.frDelegations
  frDelegationEpoch := rd.frDelegationEpoch
  frDelegationEpochAt := rd.frDelegationEpochAt
  frHeaps := rd.frHeaps
  frNullifierRoot := rd.frNullifierRoot
  frRevokedRoot := rd.frRevokedRoot
  frCommitmentsRoot := rd.frCommitmentsRoot
  logAdv := rd.logAdv

/-! ## §3 — the closed-with-log rung on the DEPLOYED welded wide crown. -/

section PerEffect
variable {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
variable {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
variable {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
variable {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
variable {hRest : RestHashIffFrame RH}
variable {LH : List Turn → ℤ}

local notation "Slive" => S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest

/-- **`transfer_descriptorRefinesAvail_closedLog` — transfer CLOSED WITH LOG on the HARDENED path.**
The mirror of `ClosureLog.transfer_descriptorRefines_closedLog` over the DEPLOYED welded wide crown
(`weldedTransferAvailWide`) and the hardened decode: from the kernel+log decode, the published
receipt-prepend, and the hardened `rotatedEncodesAvail` MINUS its `logAdv`, conclude `kstepAll 0 pre
post` with the FULL `BalanceMovementSpec` — whose availability leg is CIRCUIT-FORCED
(`availability_forced_weldedWide`), not carried. -/
theorem transfer_descriptorRefinesAvail_closedLog
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash weldedTransferAvailWide minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost = LH (tr :: pre.log))
    (logNeeds : post.log = tr :: pre.log →
      rotatedEncodesAvail hash minit mfin maddrs t pre post tr a) :
    kstepAll 0 pre post :=
  closedLog_of_encode (.balanceA tr a) tr hdec hpub (by rfl) (fun hadv =>
    show BalanceMovementSpec pre tr a post from
      transfer_descriptorRefinesAvail_weldedWide hash hside hsat pre post tr a (logNeeds hadv))

/-! ## §4 — THE SLOT: `ClosedLogExtract` at the transfer tag, availability DISCHARGED.

The floors are EXACTLY `ClosureTransfer`'s minus `availOf`: the hardened column+frame readout, the
receipt-prepend, the ledger surface seam, and the cap-open authority witness with its toy-tier
projection. `availOf` is replaced by `availability_forced_weldedWide` — a THEOREM about the deployed
descriptor, not a hypothesis. -/

/-- **`closedLogExtract_transfer_closed_avail` — the transfer slot with `availOf` DISCHARGED.** For any
registry `R` whose transfer entry is the DEPLOYED hardened member (`R 0 = weldedTransferAvailWide` — the
umem-welded, capacity-floor-refused crown row the wire registry carries since VK epoch `887b95e76`), the
transfer slot of `ClosedLogExtract` follows from {`TransferTraceReadoutAvail`, `hpub`,
`LedgerSurfaceReadout`, `TransferAuthorityWitness` + `toyAuthOf`}. NO `availOf`: availability is FORCED
by the borrow chain in the hardened descriptor the light client actually verifies. -/
theorem closedLogExtract_transfer_closed_avail
    (hash : List ℤ → ℤ) (R : Registry) (hR0 : R 0 = weldedTransferAvailWide)
    -- the hardened column+frame readout floor (the `WitnessDecodes`-class circuit-witness extraction).
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pre post : RecChainedState),
      Satisfied2 hash weldedTransferAvailWide minit mfin maddrs t →
      Σ' (tr : Turn) (a : AssetId), TransferTraceReadoutAvail hash minit mfin maddrs t pre post tr a)
    -- the receipt-prepend value (the realizable `logHashInjective` floor's published value).
    (hpub : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState)
      (hsat : Satisfied2 hash weldedTransferAvailWide minit mfin maddrs t),
      pubLogPost = LH ((readout minit mfin maddrs t pre post hsat).1 :: pre.log))
    -- the ledger surface seam (from the `S_live` `StateDecode`, under the CR floor).
    (ledger : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pre post : RecChainedState)
      (hsat : Satisfied2 hash weldedTransferAvailWide minit mfin maddrs t),
      LedgerSurfaceReadout (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
        pre post (readout minit mfin maddrs t pre post hsat).1
        (readout minit mfin maddrs t pre post hsat).2.1
        (readout minit mfin maddrs t pre post hsat).2.2.srcPre.balLo
        (readout minit mfin maddrs t pre post hsat).2.2.srcPost.balLo
        (readout minit mfin maddrs t pre post hsat).2.2.dstPre.balLo
        (readout minit mfin maddrs t pre post hsat).2.2.dstPost.balLo)
    -- the cap-open authority witness (the SOLE irreducible residual) + its deployed toy-tier projection.
    (fcaps : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pre post : RecChainedState), Satisfied2 hash weldedTransferAvailWide minit mfin maddrs t →
      Dregg2.Exec.FacetAuthority.FacetCaps)
    (authWitness : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pre post : RecChainedState)
      (hsat : Satisfied2 hash weldedTransferAvailWide minit mfin maddrs t),
      TransferAuthorityWitness hash (fcaps minit mfin maddrs t pre post hsat) pre
        (readout minit mfin maddrs t pre post hsat).1)
    (toyAuthOf : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pre post : RecChainedState)
      (hsat : Satisfied2 hash weldedTransferAvailWide minit mfin maddrs t),
      Dregg2.Exec.authorizedB pre.kernel.caps (readout minit mfin maddrs t pre post hsat).1 = true) :
    ClosedLogExtract
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) LH hash R 0 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  -- the registry's transfer entry IS the deployed hardened member.
  rw [hR0] at hsat
  -- bind the readout ONCE so the floors (stated at `(readout …)` projections) align with the row
  -- designation `tr`/`a`/`rd` here.
  set r := readout minit mfin maddrs t pre post hsat with hr
  -- the cap-open authority witness is GENUINELY exercised (it forces the deployed faithful gate).
  have _hfaithAuth : Dregg2.Exec.FacetAuthority.authorizedFacetB
      (fcaps minit mfin maddrs t pre post hsat) .signature r.1 = true :=
    authWitness_forces_faithful hash (fcaps minit mfin maddrs t pre post hsat) pre r.1
      (authWitness minit mfin maddrs t pre post hsat)
  -- assemble the HARDENED decode from the floors — NO availability argument.
  have henc : rotatedEncodesAvail hash minit mfin maddrs t pre post r.1 r.2.1 :=
    rotatedEncodesAvail_of_floors hash _ pre post r.1 r.2.1 r.2.2
      (ledger minit mfin maddrs t pre post hsat)
      (toyAuthOf minit mfin maddrs t pre post hsat)
  exact transfer_descriptorRefinesAvail_closedLog (LH := LH) hash r.2.2.hsideW hsat pre post r.1 r.2.1
    pc pubLogPre pubLogPost hdecLog (hpub minit mfin maddrs t pubLogPost pre post hsat) (fun _ => henc)

/-! ## §5 — `RfixAvail`: the apex registry with the transfer tag FLIPPED to the deployed hardened member.

`CircuitSoundnessAssembled.Rfix` still routes tag 0 to the BARE `transferV3Membership` (the Lean-side
registry lags the wire, which routes the hardened member since VK epoch `887b95e76`). `RfixAvail` is
`Rfix` with that ONE entry flipped — the registry the closure slot above discharges availability over.
Every other tag is `Rfix` verbatim, so the other 35 slots (`ClosureFanoutGenuine`) transport unchanged. -/

/-- The apex registry with the two BALANCE-DEBITING tags (transfer 0, burn 4) pointed at the DEPLOYED
hardened members. -/
def RfixAvail : Registry := fun e =>
  if e = 0 then weldedTransferAvailWide
  else if e = 4 then weldedBurnAvailWide
  else Rfix e

@[simp] theorem RfixAvail_transfer : RfixAvail 0 = weldedTransferAvailWide := by
  simp [RfixAvail]

@[simp] theorem RfixAvail_burn : RfixAvail 4 = weldedBurnAvailWide := by
  simp [RfixAvail]

/-- Off the two debiting tags, `RfixAvail` IS `Rfix` — the flip touches exactly those entries, so the
other 34 slots (`ClosureFanoutGenuine`) transport verbatim. -/
theorem RfixAvail_off {e : EffectIdx} (h0 : e ≠ 0) (h4 : e ≠ 4) : RfixAvail e = Rfix e := by
  simp [RfixAvail, h0, h4]

/-- **The transfer slot over `RfixAvail`** — the concrete instance: no availability hypothesis. -/
theorem closedLogExtract_transfer_closed_availFix
    (hash : List ℤ → ℤ)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pre post : RecChainedState),
      Satisfied2 hash weldedTransferAvailWide minit mfin maddrs t →
      Σ' (tr : Turn) (a : AssetId), TransferTraceReadoutAvail hash minit mfin maddrs t pre post tr a)
    (hpub : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState)
      (hsat : Satisfied2 hash weldedTransferAvailWide minit mfin maddrs t),
      pubLogPost = LH ((readout minit mfin maddrs t pre post hsat).1 :: pre.log))
    (ledger : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pre post : RecChainedState)
      (hsat : Satisfied2 hash weldedTransferAvailWide minit mfin maddrs t),
      LedgerSurfaceReadout (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
        pre post (readout minit mfin maddrs t pre post hsat).1
        (readout minit mfin maddrs t pre post hsat).2.1
        (readout minit mfin maddrs t pre post hsat).2.2.srcPre.balLo
        (readout minit mfin maddrs t pre post hsat).2.2.srcPost.balLo
        (readout minit mfin maddrs t pre post hsat).2.2.dstPre.balLo
        (readout minit mfin maddrs t pre post hsat).2.2.dstPost.balLo)
    (fcaps : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pre post : RecChainedState), Satisfied2 hash weldedTransferAvailWide minit mfin maddrs t →
      Dregg2.Exec.FacetAuthority.FacetCaps)
    (authWitness : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pre post : RecChainedState)
      (hsat : Satisfied2 hash weldedTransferAvailWide minit mfin maddrs t),
      TransferAuthorityWitness hash (fcaps minit mfin maddrs t pre post hsat) pre
        (readout minit mfin maddrs t pre post hsat).1)
    (toyAuthOf : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pre post : RecChainedState)
      (hsat : Satisfied2 hash weldedTransferAvailWide minit mfin maddrs t),
      Dregg2.Exec.authorizedB pre.kernel.caps (readout minit mfin maddrs t pre post hsat).1 = true) :
    ClosedLogExtract
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) LH hash RfixAvail 0 :=
  closedLogExtract_transfer_closed_avail (LH := LH) hash RfixAvail RfixAvail_transfer
    readout hpub ledger fcaps authWitness toyAuthOf

/-! ## §6 — the SIBLING slot: BURN (tag 4), the same availability class.

`ClosureFanoutGenuine.closedLogExtract_burn_closed` carries availability too — not as a separate
`availOf`, but INSIDE the decode its readout floor supplies: `rotatedEncodesBurn.guardAvail`
(`amt ≤ pre.kernel.bal cell a`, the DEBT-A relocation — audit forgery 2, the well-supply inflation).
Same staleness, same closure: the wire routes the hardened burn member (`weldedBurnAvailWide`), whose
witness FORCES the order (`wideBurn_availability_forced`). The hardened readout floor supplies
`rotatedEncodesBurnAvail`, which HAS NO `guardAvail` field — so the burn slot, like the transfer slot,
asserts no availability anywhere. -/

/-- **`BurnTraceReadoutAvail`** — the hardened burn readout floor: from a satisfying witness of the
DEPLOYED welded burn crown, the receipt data + the multi-width table side + the published prepend + the
hardened decode (NO `guardAvail`). The mirror of `ClosureFanoutGenuine.BurnTraceReadout` on the hardened
member. -/
abbrev BurnTraceReadoutAvail (hash : List ℤ → ℤ) (LH : List Turn → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pubLogPost : ℤ) (pre post : RecChainedState) : Type :=
  Satisfied2 hash weldedBurnAvailWide minit mfin maddrs t →
  Σ' (actor cell : CellId) (a : AssetId) (amt : ℤ) (permOut : List ℤ → List ℤ),
    RotTableSideW permOut hash t ×'
    PLift (pubLogPost
      = LH (Dregg2.Circuit.Spec.SupplyDestruction.burnReceipt actor cell a amt :: pre.log)) ×'
    (post.log = Dregg2.Circuit.Spec.SupplyDestruction.burnReceipt actor cell a amt :: pre.log →
      rotatedEncodesBurnAvail hash minit mfin maddrs t pre post actor cell a amt)

/-- **`burn_descriptorRefinesAvail_closedLog`** — burn CLOSED WITH LOG on the hardened path: the
`BurnSpec` with its availability leg CIRCUIT-FORCED (`wideBurn_availability_forced`), not carried. -/
theorem burn_descriptorRefinesAvail_closedLog
    (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash weldedBurnAvailWide minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ)
    (hdec : StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (hpub : pubLogPost
      = LH (Dregg2.Circuit.Spec.SupplyDestruction.burnReceipt actor cell a amt :: pre.log))
    (logNeeds : post.log
        = Dregg2.Circuit.Spec.SupplyDestruction.burnReceipt actor cell a amt :: pre.log →
      rotatedEncodesBurnAvail hash minit mfin maddrs t pre post actor cell a amt) :
    kstepAll 4 pre post :=
  closedLog_of_encode (.burnA actor cell a amt)
    (Dregg2.Circuit.Spec.SupplyDestruction.burnReceipt actor cell a amt) hdec hpub rfl
    (fun hadv => by
      show Dregg2.Circuit.ActionDispatch.fullActionStep pre (.burnA actor cell a amt) post
      simp only [Dregg2.Circuit.ActionDispatch.fullActionStep]
      exact burn_descriptorRefinesAvail_weldedWide hash hside hsat pre post actor cell a amt
        (logNeeds hadv))

/-- **`closedLogExtract_burn_closed_avail` — the burn slot with availability DISCHARGED.** For any
registry `R` whose burn entry is the DEPLOYED hardened member (`R 4 = weldedBurnAvailWide`), the burn
slot of `ClosedLogExtract` follows from the hardened readout floor ALONE — and that floor's decode
(`rotatedEncodesBurnAvail`) has no `guardAvail` field, so no availability is asserted anywhere. -/
theorem closedLogExtract_burn_closed_avail
    (hash : List ℤ → ℤ) (R : Registry) (hR4 : R 4 = weldedBurnAvailWide)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      BurnTraceReadoutAvail hash LH minit mfin maddrs t pubLogPost pre post) :
    ClosedLogExtract
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) LH hash R 4 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  rw [hR4] at hsat
  obtain ⟨actor, cell, a, amt, permOut, hside, hpub, logNeeds⟩ :=
    readout minit mfin maddrs t pubLogPost pre post hsat
  exact burn_descriptorRefinesAvail_closedLog (LH := LH) hash hside hsat pre post actor cell a amt
    pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **The burn slot over `RfixAvail`** — the concrete instance. -/
theorem closedLogExtract_burn_closed_availFix
    (hash : List ℤ → ℤ)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      BurnTraceReadoutAvail hash LH minit mfin maddrs t pubLogPost pre post) :
    ClosedLogExtract
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) LH hash RfixAvail 4 :=
  closedLogExtract_burn_closed_avail (LH := LH) hash RfixAvail RfixAvail_burn readout

end PerEffect

/-! ## §7 — THE TEETH: the discharge is a PROOF, not a deletion.

An over-debit readout (`pre.bal src a < tr.amt` — the audit's mint-from-nothing class) riding a
satisfying witness of the closure's descriptor is UNSAT. If `availOf` had merely been dropped, this
would be unprovable. -/

/-- **`closure_rejects_overdebit_avail`** — the forgery class the closure slot now REFUSES: any
`TransferTraceReadoutAvail` + ledger seam whose decoded ledger is over-debited, riding a satisfying
witness of the closure's transfer descriptor, is UNSAT. -/
theorem closure_rejects_overdebit_avail (hash : List ℤ → ℤ) (S : CommitSurface)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash weldedTransferAvailWide minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (rd : TransferTraceReadoutAvail hash minit mfin maddrs t pre post tr a)
    (rdo : LedgerSurfaceReadout S pre post tr a
            rd.srcPre.balLo rd.srcPost.balLo rd.dstPre.balLo rd.dstPost.balLo)
    (htoyAuth : authorizedB pre.kernel.caps tr = true)
    (hforge : pre.kernel.bal tr.src a < tr.amt) : False :=
  weldedWide_rejects_overdebit hash rd.hsideW hsat pre post tr a
    (rotatedEncodesAvail_of_floors hash S pre post tr a rd rdo htoyAuth) hforge

/-- The audit's CONCRETE forgery (`pre.bal src a = 0`, `tr.amt = 10⁹`) is UNSAT at the closure slot. -/
theorem closure_audit_forgery_unsat (hash : List ℤ → ℤ) (S : CommitSurface)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash weldedTransferAvailWide minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (rd : TransferTraceReadoutAvail hash minit mfin maddrs t pre post tr a)
    (rdo : LedgerSurfaceReadout S pre post tr a
            rd.srcPre.balLo rd.srcPost.balLo rd.dstPre.balLo rd.dstPost.balLo)
    (htoyAuth : authorizedB pre.kernel.caps tr = true)
    (hbal : pre.kernel.bal tr.src a = 0) (hamt : tr.amt = 1000000000) : False := by
  refine closure_rejects_overdebit_avail hash S hsat pre post tr a rd rdo htoyAuth ?_
  omega

/-- The availability the closure slot USES, stated on its own: the readout + a satisfying witness of the
deployed hardened member FORCE `tr.amt ≤ pre.kernel.bal tr.src a`. This is what replaced `availOf`. -/
theorem closure_availability_forced (hash : List ℤ → ℤ) (S : CommitSurface)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash weldedTransferAvailWide minit mfin maddrs t)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (rd : TransferTraceReadoutAvail hash minit mfin maddrs t pre post tr a)
    (rdo : LedgerSurfaceReadout S pre post tr a
            rd.srcPre.balLo rd.srcPost.balLo rd.dstPre.balLo rd.dstPost.balLo)
    (htoyAuth : authorizedB pre.kernel.caps tr = true) :
    tr.amt ≤ pre.kernel.bal tr.src a :=
  availability_forced_weldedWide hash rd.hsideW hsat pre post tr a
    (rotatedEncodesAvail_of_floors hash S pre post tr a rd rdo htoyAuth)

/-- **The BURN tooth** — an over-burn decode (`pre.bal cell a < amt`, the well-supply-inflation class)
riding a satisfying witness of the closure's burn descriptor is UNSAT. -/
theorem closure_rejects_overburn_avail (hash : List ℤ → ℤ)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    {permOut : List ℤ → List ℤ}
    (hside : RotTableSideW permOut hash t)
    (hsat : Satisfied2 hash weldedBurnAvailWide minit mfin maddrs t)
    (pre post : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (henc : rotatedEncodesBurnAvail hash minit mfin maddrs t pre post actor cell a amt)
    (hforge : pre.kernel.bal cell a < amt) : False :=
  weldedBurnWide_rejects_overburn hash hside hsat pre post actor cell a amt henc hforge

/-! ## §8 — axiom hygiene. -/

#assert_axioms TransferTraceReadoutAvail.toReadout
#assert_axioms rotatedEncodesAvail_of_floors
#assert_axioms transfer_descriptorRefinesAvail_closedLog
#assert_axioms closedLogExtract_transfer_closed_avail
#assert_axioms RfixAvail_transfer
#assert_axioms RfixAvail_burn
#assert_axioms RfixAvail_off
#assert_axioms closedLogExtract_transfer_closed_availFix
#assert_axioms burn_descriptorRefinesAvail_closedLog
#assert_axioms closedLogExtract_burn_closed_avail
#assert_axioms closedLogExtract_burn_closed_availFix
#assert_axioms closure_rejects_overdebit_avail
#assert_axioms closure_audit_forgery_unsat
#assert_axioms closure_availability_forced
#assert_axioms closure_rejects_overburn_avail

end Dregg2.Circuit.ClosureTransferAvail
