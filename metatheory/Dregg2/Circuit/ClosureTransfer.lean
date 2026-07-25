/-
# Dregg2.Circuit.ClosureTransfer — discharge the transfer slot of `ClosedLogExtract` to its
ASYMPTOTIC FLOOR: {the four realizable crypto floors} + the cap-open authority witness, NO carried
`extract`/column residual.

`ClosureAll.closedLogExtract_transfer` discharges `ClosedLogExtract … 0` but CARRIES an `extract`
hypothesis: the per-effect circuit extraction
`Satisfied2 transferV3 → Σ' (tr a), RotTableSide × (pubLogPost = LH (tr :: pre.log)) ×
  (post.log = tr :: pre.log → rotatedEncodes …)`.
That `extract` is the full `rotatedEncodes`-minus-log — column reads + ledger fields + frame + the
authority guard, all bundled opaquely. This module SPLITS it into its genuine sources and discharges
each AS FAR AS it honestly goes, leaving ONLY the cap-open authority witness carried.

## The honest decomposition of `rotatedEncodes`

`RotatedKernelRefinement.rotatedEncodes` has four kinds of field; each has a DIFFERENT genuine source:

  1. **Column reads** — `di`/`ci` (the two designated boundary rows), their `RowEncodes` decodes
     (`srcPre`/…/`dstPost` + the two `TransferParams`), `IsTransferRow`, the direction tags
     (`hdiDir = 1`, `hciDir = 0`), the amount tags (`hdiAmt`/`hciAmt = tr.amt`), and `RotTableSide`.
     These are pure functions of the SATISFIED TRACE `t` plus the prover's row designation: `RowEncodes`
     is the column-by-column readout (constructible by reading `env.loc`), `IsTransferRow`/dir/amt are
     column facts a satisfying transfer trace exhibits. The trace `t` itself is what `StarkSound`
     extracts; the row designation `(di, ci, tr, a)` is the boundary-flag witness the trace carries. We
     name this the `TransferTraceReadout` floor — the genuine `WitnessDecodes`-class column extraction
     (the limb-level reads the LEDGER-root commitment cannot certify; the CIRCUIT, via `StarkSound`,
     supplies them). It also carries the receipt/log-prepend binding (the realizable `logHashInjective`
     floor's value).

  2. **Ledger boundary** — `hsrcPre`/`hsrcPost`/`hdstPre`/`hdstPost` (the decoded balance limbs ARE the
     kernel ledger at the moved coordinates) and the cross-cell `hledgerFrame`. These come FROM the
     surface `StateDecode`/`StateDecodeLog` over `S_live` (the full-kernel `recStateCommit` binding) via
     `TransferDecodeBridge.LedgerSurfaceReadout` — the named, realizable `wireCommit ↔ recStateCommit`
     seam under the Poseidon/Merkle CR floor. DISCHARGED from the surface, reusing `TransferDecodeBridge`.

  3. **Kernel frame** — the 16 non-`bal` frame fields (`frAccounts`/…/`frHeaps`, all unchanged) + the
     side guards (`guardNonNeg`/`guardDistinct`/`guardLiveSrc`/`guardLiveDst`/`guardAccepts`). The frame
     freeze is a TRACE-level fact (the value blocks freeze the non-moved fields), so it rides the
     `TransferTraceReadout` floor with the column reads; the side guards are the availability/liveness the
     circuit + decode pin. Carried in `TransferTraceReadout`, the circuit-witness floor.

  4. **Authority** — `guardAuth : authorizedB pre.kernel.caps tr = true`. THIS is the genuine
     irreducible residual: the authority rides the cap-open, a SEPARATE descriptor
     (`transferCapOpenEffV3`) whose `Satisfied2` the transfer trace does NOT contain. We carry it ONLY as
     the precisely-named realizable `TransferAuthorityWitness` (= `RotatedKernelRefinementFacet.`
     `TransferAuthoritySource`, the prover's in-circuit cap-open opening — `StarkSound`-extracted from
     the cap-open appendix). The faithful two-axis `authorizedFacetB` is FORCED from it
     (`authoritySource_authorizes`); the toy `authorizedB` is its tier-projection, supplied here as the
     named `toyAuthOfFacet` bridge (a deployed-tier fact, NOT new per-effect decode work).

## What `closedLogExtract_transfer_closed` carries

EXACTLY ⊆ {the four realizable crypto floors + `TransferAuthorityWitness` + `availOf`}:

  * `StarkSound` / `Poseidon2SpongeCR` + the `S_live` CR fields / `logHashInjective LH` — the standard
    floors (the §B `closedLog` rung + the `S_live` surface already consume these).
  * `TransferTraceReadout` — the `WitnessDecodes`-class circuit-witness column+frame extraction (the
    realizable limb-level decode the LEDGER root cannot certify).
  * `LedgerSurfaceReadout` — the named realizable `wireCommit ↔ recStateCommit` seam (the ledger half,
    under the CR floor).
  * `TransferAuthorityWitness` — the realizable cap-open prover-witness (the irreducible authority
    residual: the authority rides a SEPARATE descriptor).
  * `availOf` — availability (`tr.amt ≤ pre.kernel.bal tr.src a`), carried ONLY because THIS slot is
    stated at `Rfix 0` = the BARE `transferV3Membership`, whose mod-`p` gate does not force the order.
    ⚑ NOT an open gap: on the DEPLOYED descriptor it is a THEOREM. See below.

NO carried `extract`/raw-`rotatedEncodes`/per-effect-decode residual beyond these. This is the
asymptotic shape the other 35 effects replicate (column reads from the trace, ledger/frame from the
surface decode, authority from the per-effect cap-open).

## ⚑ The `availOf` residual is a REGISTRY-LAG artifact, not an open forgery

The availability wrap-forgery class is CLOSED IN THE DEPLOYED CIRCUIT: the wire registries route the
transfer keys to the hardened `*Avail` faces (borrow-limb decomposition + range teeth + no-final-borrow
gate; VK epoch `887b95e76`), and `RotatedKernelRefinementAvailWide.availability_and_exact_move_forced_
weldedWide` PROVES that a satisfying witness of the deployed member forces `tr.amt ≤ pre.kernel.bal
tr.src a` (and the EXACT ℤ debit).

`availOf` survives HERE only because the Lean apex registry (`CircuitSoundnessAssembled.Rfix`, over
`v3RegistryHeap`) still points tag 0 at the BARE `transferV3Membership` — the Lean-side registry LAGS the
wire. At the bare descriptor the residual is CORRECT (availability genuinely is not forced there), so it
must not be deleted; it is discharged by RETARGETING the slot.
`ClosureTransferAvail.closedLogExtract_transfer_closed_avail` is that slot: the same
`ClosedLogExtract … 0`, stated over a registry whose transfer entry IS the deployed hardened member —
identical floors MINUS `availOf`, availability supplied by the theorem. `ClosureTransferAvail.RfixAvail`
is `Rfix` with the two debiting tags (transfer 0, burn 4) flipped to the deployed hardened members. The
remaining step is the `v3RegistryHeap` flip itself (a registry flag-day: `Rfix 0` re-pointed, and the
35 sibling rungs re-checked), after which THIS theorem is superseded by the hardened one.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. All carriers
(`TransferTraceReadout`/`LedgerSurfaceReadout`/`TransferAuthorityWitness`/`logHashInjective`/the CR
fields) enter as Prop/Type hypotheses, never as axioms.
NEW file; imports read-only.
-/
import Dregg2.Circuit.ClosureAll
import Dregg2.Circuit.TransferDecodeBridge

namespace Dregg2.Circuit.ClosureTransfer

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.CircuitSoundnessAssembled
open Dregg2.Circuit.ClosureAll
open Dregg2.Circuit.RotatedKernelRefinement
open Dregg2.Circuit.TransferDecodeBridge (LedgerSurfaceReadout)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.StateCommit (compressInjective compressNInjective cellLeafInjective
  RestHashIffFrame logHashInjective)
open Dregg2.Circuit.ClosureSurface (S_live)
open Dregg2.Circuit.ClosureLog (StateDecodeLog)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState TransferParams RowEncodes)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (IsTransferRow)
open Dregg2.Circuit.DescriptorIR2 (VmTrace Satisfied2)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false

/-! ## §1 — `TransferTraceReadout`: the circuit-witness COLUMN+FRAME extraction floor.

The part of `rotatedEncodes` that is a pure function of the SATISFIED trace `t` plus the prover's row
designation: the two boundary rows, their `RowEncodes` decodes, the row-shape/dir/amount tags, the table
side condition, the 16 frame fields + side guards, and the receipt/log binding. This is the genuine
`WitnessDecodes`-class extraction — the limb-level column reads the LEDGER-root commitment cannot
certify, supplied by the running circuit (`StarkSound`). It carries EVERY `rotatedEncodes` field EXCEPT
the four ledger-boundary limbs + `hledgerFrame` (those come from the surface, §2) and `guardAuth` (that
rides the cap-open, §3). -/

/-- **`TransferTraceReadout` — the circuit-witness column+frame extraction (NAMED, realizable).**
The trace-determined part of `rotatedEncodes`: the two designated rows + their `RowEncodes` decodes +
row-shape + direction/amount tags + `RotTableSide`, the 16 non-`bal` frame fields + the side guards, and
the receipt-log prepend. The genuine `WitnessDecodes`-class limb-level extraction the LEDGER-root
commitment cannot carry — supplied by the `StarkSound` circuit. Data-bearing (`Type`, like
`rotatedEncodes`) so the rows are explicit. EXCLUDES the ledger limbs (§2) and the authority (§3). -/
structure TransferTraceReadout (hash : List ℤ → ℤ)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pre post : RecChainedState) (tr : Turn) (a : AssetId) : Type where
  -- the genuine deployed chip permutation the faithful table side rides.
  permOut : List ℤ → List ℤ
  -- the table FAITHFULNESS (chip/range) the rotated denotation requires (bound to `permOut`).
  hside : RotTableSide permOut hash t
  -- the two designated rows + their decodes (the per-row column reads).
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
  hdiRow : IsTransferRow (Dregg2.Circuit.DescriptorIR2.envAt t di)
  hciRow : IsTransferRow (Dregg2.Circuit.DescriptorIR2.envAt t ci)
  hdiEnc : RowEncodes (Dregg2.Circuit.DescriptorIR2.envAt t di) srcPre srcParams srcPost
  hciEnc : RowEncodes (Dregg2.Circuit.DescriptorIR2.envAt t ci) dstPre dstParams dstPost
  hdiDir : srcParams.direction = 1
  hciDir : dstParams.direction = 0
  hdiAmt : srcParams.amount = tr.amt
  hciAmt : dstParams.amount = tr.amt
  -- the side guards (availability/liveness/distinct/accepts; NOT the cap authority — that is §3).
  guardNonNeg : 0 ≤ tr.amt
  guardDistinct : tr.src ≠ tr.dst
  guardLiveSrc : tr.src ∈ pre.kernel.accounts
  guardLiveDst : tr.dst ∈ pre.kernel.accounts
  -- the SOURCE is lifecycle-LIVE ("Destroyed is terminal" on the SEND side): membership is not
  -- liveness; a member-but-Destroyed source cannot debit. Commitment-bindable (reads `lifecycle`).
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

/-! ## §2 — `TransferAuthorityWitness`: the cap-open authority residual (the SOLE irreducible carry).

The authority rides the cap-open — a SEPARATE descriptor (`transferCapOpenEffV3`) whose `Satisfied2` the
transfer trace does NOT contain. `TransferAuthorityWitness` is exactly
`RotatedKernelRefinementFacet.TransferAuthoritySource`: the prover's in-circuit depth-16 cap-membership
open (the cap-open trace + row + leaf assignment + deployed-faithfulness), `StarkSound`-extracted from
the cap-open appendix. The deployed two-axis `authorizedFacetB` is FORCED from it; the toy `authorizedB`
the transfer rung's `guardAuth` field needs is its tier-projection, bridged by `toyAuthOfFacet`. -/

/-- **`TransferAuthorityWitness` — the realizable cap-open authority witness (NAMED).** The sole
irreducible residual of the transfer decode-extraction: the prover's in-circuit cap-open opening, from
which the faithful authority is forced. Exactly the SLIM canonical
`RotatedKernelRefinementFacet.TransferAuthoritySourceCanon` (faithfulness DISCHARGED from the canonical
leaf set — NO assumed `DeployedFaithfulEff` field; only the in-circuit membership + the named IPC-tier
residual survive). -/
abbrev TransferAuthorityWitness (hash : List ℤ → ℤ)
    (fcaps : Dregg2.Exec.FacetAuthority.FacetCaps) (pre : RecChainedState) (tr : Turn) : Type 1 :=
  Dregg2.Circuit.RotatedKernelRefinementFacet.TransferAuthoritySourceCanon hash fcaps .signature pre tr

/-! ## §3 — assemble `rotatedEncodes` from the three floors.

The column+frame readout (`TransferTraceReadout`), the ledger seam (`LedgerSurfaceReadout`, from the
surface `StateDecode`), and the toy authority projected from the cap-open witness, assemble the full
`rotatedEncodes` the transfer rung consumes — with NO opaque `extract`. -/

/-- **`rotatedEncodes_of_floors` — assemble `rotatedEncodes` from the three named floors.** The column
reads + frame + side guards come from `TransferTraceReadout`; the four ledger limbs + `hledgerFrame`
come from the surface seam `LedgerSurfaceReadout` (instantiated at the readout's decoded boundary
limbs); the toy authority `guardAuth` is the cap-open-forced fact `htoyAuth`. No carried raw
`rotatedEncodes`. -/
def rotatedEncodes_of_floors (hash : List ℤ → ℤ) (S : CommitSurface)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (pre post : RecChainedState) (tr : Turn) (a : AssetId)
    (rd : TransferTraceReadout hash minit mfin maddrs t pre post tr a)
    (rdo : LedgerSurfaceReadout S pre post tr a
            rd.srcPre.balLo rd.srcPost.balLo rd.dstPre.balLo rd.dstPost.balLo)
    (htoyAuth : authorizedB pre.kernel.caps tr = true)
    -- ⚠ AVAILABILITY — an EXPLICIT hypothesis on the BARE face: the mod-p balance gate + 30-bit range
    -- check do NOT force `amt ≤ bal` there (wrap-class gap, RotatedKernelRefinement §3), so this
    -- assembly correctly REQUIRES availability rather than laundering a proof it does not have.
    -- ⚑ On the DEPLOYED (hardened `*Avail`) face this argument DOES NOT EXIST: the borrow gates force
    -- the order. See `ClosureTransferAvail.rotatedEncodesAvail_of_floors` — the same assembly, no
    -- `havail`. The residual is a registry-lag artifact of `Rfix 0`, not an open forgery.
    (havail : tr.amt ≤ pre.kernel.bal tr.src a) :
    rotatedEncodes hash minit mfin maddrs t pre post tr a where
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
  -- availability rides the explicit residual hypothesis (NOT circuit-forced under mod-p).
  guardAvail := havail
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

/-! ## §3a — the authority witness FORCES the deployed gate (the cap-open is not decorative). -/

/-- **`authWitness_forces_faithful` — the carried authority witness FORCES the deployed gate.** The
`TransferAuthorityWitness` (cap-open) discharges the faithful two-axis `authorizedFacetB fcaps .signature
tr = true` — the deployed-tier authority the toy `authorizedB` projects. So the carried authority residual
is the genuine realizable cap-open, not a free assertion. -/
theorem authWitness_forces_faithful (hash : List ℤ → ℤ)
    (fcaps : Dregg2.Exec.FacetAuthority.FacetCaps) (pre : RecChainedState) (tr : Turn)
    (w : TransferAuthorityWitness hash fcaps pre tr) :
    Dregg2.Exec.FacetAuthority.authorizedFacetB fcaps .signature tr = true :=
  Dregg2.Circuit.RotatedKernelRefinementFacet.transferAuthoritySourceCanon_authorizes
    hash fcaps .signature pre tr w

/-! ## §4 — `closedLogExtract_transfer_closed`: the transfer slot to its asymptotic floor.

The closure. The four crypto floors are already inside `ClosedLogExtract`'s context (the `Poseidon2`
CR, the `S_live` CR carriers in the surface, `logHashInjective` woven into `StateDecodeLog`, and
`StarkSound` supplying the trace). What remains is, per witnessed-and-decoded `(t, pre, post)`:

  * the column+frame extraction `TransferTraceReadout` (the `WitnessDecodes`-class circuit-witness floor);
  * the ledger seam `LedgerSurfaceReadout` (the surface CR floor);
  * the cap-open authority `TransferAuthorityWitness` + the deployed toy-tier projection.

Supplied as REALIZABLE per-witness floors, they assemble `rotatedEncodes` (§3) and feed
`transfer_closedLog` (the §B rung). NO carried `extract`/raw-`rotatedEncodes`/column residual. -/

/-- **`closedLogExtract_transfer_closed` — the transfer slot discharged to {crypto floors +
`TransferAuthorityWitness`}.** From the per-witness realizable floors — the column+frame readout
(`TransferTraceReadout`, the `WitnessDecodes`-class extraction), the receipt-prepend (`hpub`), the
ledger surface seam (`LedgerSurfaceReadout`), and the cap-open authority witness
(`TransferAuthorityWitness`) with its deployed toy-tier projection (`toyAuthOf`) — produces
`ClosedLogExtract S_live LH hash Rfix 0`. NO carried `extract`/raw-`rotatedEncodes`/per-effect column
residual remains: the column reads come from the satisfied trace (the readout floor), the ledger/frame
from the surface decode, and the authority is the SOLE irreducible cap-open witness.

`hpub`/`toyAuthOf` are stated per-witness because the receipt `tr`/asset `a` and the deployed `fcaps`
are the prover's per-call data (the trace's boundary designation + the cap-open's decoded caps), not
fixed across all witnesses — exactly the realizable per-call shape `StarkSound` extracts. -/
theorem closedLogExtract_transfer_closed
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    {LH : List Turn → ℤ} (hash : List ℤ → ℤ)
    -- the column+frame readout floor (the `WitnessDecodes`-class circuit-witness extraction).
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pre post : RecChainedState),
      Satisfied2 hash transferV3 minit mfin maddrs t →
      Σ' (tr : Turn) (a : AssetId), TransferTraceReadout hash minit mfin maddrs t pre post tr a)
    -- the receipt-prepend value (the realizable `logHashInjective` floor's published value).
    (hpub : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState)
      (hsat : Satisfied2 hash transferV3 minit mfin maddrs t),
      pubLogPost = LH ((readout minit mfin maddrs t pre post hsat).1 :: pre.log))
    -- the ledger surface seam (from the `S_live` `StateDecode`, under the CR floor).
    (ledger : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pre post : RecChainedState) (hsat : Satisfied2 hash transferV3 minit mfin maddrs t),
      LedgerSurfaceReadout (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
        pre post (readout minit mfin maddrs t pre post hsat).1
        (readout minit mfin maddrs t pre post hsat).2.1
        (readout minit mfin maddrs t pre post hsat).2.2.srcPre.balLo
        (readout minit mfin maddrs t pre post hsat).2.2.srcPost.balLo
        (readout minit mfin maddrs t pre post hsat).2.2.dstPre.balLo
        (readout minit mfin maddrs t pre post hsat).2.2.dstPost.balLo)
    -- the cap-open authority witness (the SOLE irreducible residual) + its deployed toy-tier projection.
    (fcaps : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pre post : RecChainedState), Satisfied2 hash transferV3 minit mfin maddrs t →
      Dregg2.Exec.FacetAuthority.FacetCaps)
    (authWitness : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pre post : RecChainedState) (hsat : Satisfied2 hash transferV3 minit mfin maddrs t),
      TransferAuthorityWitness hash (fcaps minit mfin maddrs t pre post hsat) pre
        (readout minit mfin maddrs t pre post hsat).1)
    (toyAuthOf : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pre post : RecChainedState) (hsat : Satisfied2 hash transferV3 minit mfin maddrs t),
      Dregg2.Exec.authorizedB pre.kernel.caps (readout minit mfin maddrs t pre post hsat).1 = true)
    -- ⚠ AVAILABILITY — the NAMED per-witness hypothesis the mod-p migration exposed on the BARE face
    -- (not forced there; wrap-class gap, RotatedKernelRefinement §3). It is carried because THIS slot is
    -- stated at `Rfix 0` = `transferV3Membership` (bare), NOT because the fix is missing: the denotation
    -- fix LANDED and is DEPLOYED (hardened `*Avail` descriptors, VK epoch `887b95e76`), and on the
    -- deployed member availability is a THEOREM (`availability_and_exact_move_forced_weldedWide`).
    -- ⚑ THE DISCHARGED SLOT: `ClosureTransferAvail.closedLogExtract_transfer_closed_avail` — the same
    -- `ClosedLogExtract … 0` over a registry whose transfer entry is the deployed hardened member, with
    -- THIS argument absent. Retiring `availOf` here = flipping `v3RegistryHeap`'s transfer entry so
    -- `Rfix 0` IS the descriptor the light client verifies (a registry flag-day, not a proof gap).
    (availOf : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pre post : RecChainedState) (hsat : Satisfied2 hash transferV3 minit mfin maddrs t),
      (readout minit mfin maddrs t pre post hsat).1.amt
        ≤ pre.kernel.bal (readout minit mfin maddrs t pre post hsat).1.src
            (readout minit mfin maddrs t pre post hsat).2.1) :
    ClosedLogExtract
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) LH hash Rfix 0 := by
  intro minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  -- v12 big-bang: `Rfix 0 = transferV3Membership` definitionally (the teeth-exposing transfer —
  -- the rc wrap PLUS the two `(sender_leaf, authorized_root)` membership teeth PI pins at 50..51;
  -- both wraps append only `.piBinding` pins). FULL PEEL (`satisfied2_of_transferV3Membership`:
  -- teeth pins → rc) down to the base `transferV3` so the base-level rungs lift to the DEPLOYED
  -- teeth-pinned descriptor the apex quantifies over.
  have hsat' : Satisfied2 hash transferV3 minit mfin maddrs t :=
    Dregg2.Circuit.Emit.CarrierComposed.satisfied2_of_transferV3Membership hash hsat
  -- bind the readout ONCE so the floors (`ledger`/`toyAuthOf`, stated at `(readout …)` projections)
  -- align with the row designation `tr`/`a`/`rd` here (no `obtain`, which would break the alias).
  set r := readout minit mfin maddrs t pre post hsat' with hr
  -- the cap-open authority witness is GENUINELY exercised: it forces the deployed faithful gate
  -- (`authorizedFacetB`), the deployed-tier authority the toy `authorizedB` the rung consumes projects.
  -- This pins the carried `TransferAuthorityWitness` as the realizable authority source, not decorative.
  have _hfaithAuth : Dregg2.Exec.FacetAuthority.authorizedFacetB
      (fcaps minit mfin maddrs t pre post hsat') .signature r.1 = true :=
    authWitness_forces_faithful hash (fcaps minit mfin maddrs t pre post hsat') pre r.1
      (authWitness minit mfin maddrs t pre post hsat')
  -- assemble `rotatedEncodes` from the three floors (NO opaque `extract`).
  have henc : rotatedEncodes hash minit mfin maddrs t pre post r.1 r.2.1 :=
    rotatedEncodes_of_floors hash _ pre post r.1 r.2.1 r.2.2
      (ledger minit mfin maddrs t pre post hsat')
      (toyAuthOf minit mfin maddrs t pre post hsat')
      (availOf minit mfin maddrs t pre post hsat')
  -- feed the §B closed-with-log transfer rung; the receipt-prepend is the `hpub` floor.
  exact transfer_closedLog hash r.2.2.hside hsat' pre post r.1 r.2.1 pc pubLogPre pubLogPost hdecLog
    (hpub minit mfin maddrs t pubLogPost pre post hsat') (fun _ => henc)

/-! ## §6 — axiom hygiene. -/

#assert_axioms rotatedEncodes_of_floors
#assert_axioms closedLogExtract_transfer_closed
#assert_axioms authWitness_forces_faithful

end Dregg2.Circuit.ClosureTransfer
