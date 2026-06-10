/-
# Dregg2.Apps.BridgeCell — W2 LANE G: the cross-domain BRIDGE as a factory-born CELL.

This module re-lands the BRIDGE verb family (`bridgeLock`/`bridgeFinalize`/`bridgeCancel` over the
shared off-ledger `escrows` side-table with the `bridge := true` tag — `RecordKernel.lean:1797…1841`)
as a factory-born CELL that custodies the locked cross-domain value in its OWN per-asset `bal` column,
with the FOREIGN-FINALITY witness as the release condition. It is the bridge twin of W2's
`Dregg2.Apps.EscrowFactory` (the escrow factory), and it settles the finalized value to the W1
BRIDGE-POT (`Dregg2.Substrate.IssuerLedger.canonical_bridge_law` / the probe's
`bridgeFinalizeToPotK`), so the whole bridge lifecycle is conservation-EXACT with NO disclosed
off-ledger outflow.

## The move that makes the bridge a cell program (and the side-table redundant)

dregg1/dregg2 bridge today parks a `bridge := true`-tagged `EscrowRecord` in the SHARED off-ledger
store `k.escrows`: a LOCK single-cell DEBITs the originator and parks the record; a FINALIZE marks it
resolved WITHOUT a credit — the value LEFT for the foreign chain, a disclosed OUTFLOW that BREAKS the
plain per-asset conservation (`bridgeFinalize_breaks_exact`), bought back only by the bespoke
`recTotalAssetWithEscrow` combined measure; a CANCEL credits the originator back (conserved).

The cell-program rebuild does the OPPOSITE move — the SAME move escrow made: **the bridge cell HOLDS
the locked value in its own per-asset `bal` column.** A LOCK is an ordinary `move` IN
(originator ⇒ bridgeCell); a FINALIZE is an ordinary `move` OUT to the BRIDGE-POT cell (the foreign
chain's custody modelled as a cell, per W1) gated on the foreign-finality witness; a CANCEL is an
ordinary `move` OUT back to the originator. The lifecycle `state ∈ {locked, finalized, cancelled}`
lives in a SLOT governed by the SAME monotonic `admitTable` state machine. The off-ledger store
DISAPPEARS, and with it BOTH the bespoke combined measure AND the bridge-outflow conservation
EXEMPTION: the finalized value does not vanish off-ledger — it settles to the bridge-pot cell, so
conservation is the ORDINARY per-asset move law `recKExecAsset_conserves_per_asset` end to end.

## The shape (the published deliverable)

`bridgeFactoryEntry amount originator pot finalityWitness asset : FactoryEntry`
  — IS the escrow factory shape (`Dregg2.Verify.EscrowFactoryProbe.escrowFactory`) re-read with bridge
  meaning on its six slots:
    * `state`       — 0 = locked, 1 = finalized, 2 = cancelled   (the same automaton)
    * `amount`      — the locked cross-domain amount (immutable)
    * `depositor`   — the ORIGINATOR (the cancel/refund target — immutable)
    * `beneficiary` — the BRIDGE-POT cell (the finalize settle target — immutable)
    * `condition`   — the FOREIGN-FINALITY witness gate value (the `witnessed(vk)` Pred — immutable)
    * `asset`       — the asset class of the locked value (immutable)
  + the locked VALUE held in the bridge cell's per-asset `bal` column.

`bridgeRegistry vk` installs it at content-addressed key `vk`; `mintBridgeCell` runs the REAL factory
executor (`createCellFromFactoryChainA`); `lockBridge` moves the locked value IN; `finalizeBridge` is
the probe's `escrowRelease` (OPEN→FINALIZED + move to the bridge-pot) gated on the finality witness;
`cancelBridge` is the probe's `escrowRefund` (OPEN→CANCELLED + move to the originator).

## The bridge-safety keystones (re-established on the factory-born cell)

  (a) CONSERVATION across lock/finalize/cancel — INHERITED from the ordinary per-asset move law (a lock
      is a move IN, a finalize/cancel is a move OUT). The W1 bridge-pot law is SUBSUMED: settling the
      finalize to the bridge-pot cell makes finalize an ordinary move, so the per-asset total is FIXED
      (no outflow exemption). PROVED off `recKExecAsset_conserves_per_asset` / the probe keystones.
  (b) NO-DOUBLE-FINALIZE — the monotonic state machine: once FINALIZED (or CANCELLED), neither a second
      finalize nor a cancel commits. The locked value crosses AT MOST ONCE. PROVED.
  (c) FINALIZE GATED BY THE FINALITY WITNESS — a finalize whose supplied witness ≠ the cell's frozen
      finality-condition slot is rejected (the `witnessed(vk)` Pred polarity at the executable layer;
      §HARD-iii of the escrow probe shows the equality is a swappable abstract Pred-discharge). PROVED.
  (d) VALUE NOT STRANDED (locked ⇒ one-step resolvable) — from any LOCKED bridge cell with a live,
      distinct, settle-ready pot/originator, BOTH a finalize (witness discharged) AND a cancel COMMIT.
      PROVED as one-step resolvability (the consensus/GST eventual-finality liveness is the same
      out-of-band boundary the verbs had).

These RE-USE the escrow factory probe's already-proved keystones VERBATIM — the bridge cell minted by
`bridgeFactoryEntry` is exactly the `RecordKernelState` shape those theorems quantify over (state slot
+ value in `bal`), so feeding the factory-install facts in lifts them with no re-proof. That is the
witness that the factory is a FAITHFUL replacement for the bridge verbs (§DELETION).

NEW file only. Imports the escrow factory + the W1 issuer-supply probe (for the bridge-POT exact-ledger
law `bridgeFinalizeToPot_preserves_exact` + the `bridgeFinalize_breaks_exact` non-vacuity tooth — the
bridge-pot framing). Does NOT touch any shared mod/import file. `#assert_axioms`-pinned to
`{propext, Classical.choice, Quot.sound}` — no sorry, no `:= True`. Land-before-kill: nothing deleted.
-/
import Dregg2.Apps.EscrowFactory
import Dregg2.Substrate.IssuerSupplyProbe

namespace Dregg2.Apps.BridgeCell

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Cap)
open Dregg2.Verify.EscrowFactoryProbe
open Dregg2.Apps.EscrowFactory
open Dregg2.Exec.EffectsState (fieldOf setField)

/-! ## §0 — the bridge lifecycle vocabulary (the SAME automaton, bridge-named).

The bridge cell carries the escrow probe's six-slot layout; we only RENAME the lifecycle literals to
the bridge's three states. `sLocked`/`sFinalized`/`sCancelled` are DEFINITIONALLY the escrow probe's
`sOpen`/`sReleased`/`sRefunded` (`0`/`1`/`2`), so every state-machine theorem the probe proved applies
to the bridge cell on the nose. -/

/-- Bridge state: 0 = locked (awaiting foreign finality). DEFINITIONALLY `sOpen`. -/
abbrev sLocked : Int := sOpen
/-- Bridge state: 1 = finalized (the foreign-finality witness discharged; value settled to the pot).
DEFINITIONALLY `sReleased`. -/
abbrev sFinalized : Int := sReleased
/-- Bridge state: 2 = cancelled (timeout/failure; value refunded to the originator).
DEFINITIONALLY `sRefunded`. -/
abbrev sCancelled : Int := sRefunded

/-! ## §1 — the BRIDGE FACTORY ENTRY (the published `FactoryEntry`).

This IS the escrow factory descriptor (`escrowFactory`) re-exported under a bridge-facing name, with
its six slots re-read as the bridge deal terms: `amount` = locked cross-domain amount, `depositor` =
ORIGINATOR (cancel target), `beneficiary` = the BRIDGE-POT (finalize target), `condition` = the
FOREIGN-FINALITY witness gate, `asset` = the locked asset. The same `admitTable [(0,1),(0,2)]` state
machine is the no-double-finalize teeth. -/

/-- **The bridge factory entry.** Mints a bridge cell carrying the deal-term immutables + the
no-double-finalize state machine; the locked cross-domain value is held in the minted cell's `bal`
column. The `condition` slot holds the foreign-finality witness gate value. -/
def bridgeFactoryEntry (amount originator pot finalityWitness asset : Int) : FactoryEntry :=
  escrowFactoryEntry amount originator pot finalityWitness asset

/-- The bridge factory conforms to its own published invariants (re-exported probe keystone). -/
theorem bridgeFactoryEntry_conforms (amount originator pot finalityWitness asset : Int) :
    (bridgeFactoryEntry amount originator pot finalityWitness asset).conforms = true :=
  escrowFactoryEntry_conforms amount originator pot finalityWitness asset

/-- A kernel factory registry that publishes the bridge factory at content-addressed key `vk`. -/
def bridgeRegistry (vk : Nat) (amount originator pot finalityWitness asset : Int) :
    List (Nat × FactoryEntry) :=
  [(vk, bridgeFactoryEntry amount originator pot finalityWitness asset)]

/-- The registry resolves the bridge factory at exactly its published key. -/
theorem bridgeRegistry_finds (vk : Nat) (amount originator pot finalityWitness asset : Int) :
    findFactory (bridgeRegistry vk amount originator pot finalityWitness asset) vk
      = some (bridgeFactoryEntry amount originator pot finalityWitness asset) :=
  escrowRegistry_finds vk amount originator pot finalityWitness asset

/-! ## §2 — MINTING the bridge cell through the REAL factory executor. -/

/-- Mint a bridge cell from the bridge factory at key `vk` (the real factory executor — the SAME
`createCellFromFactoryChainA` the escrow factory uses). -/
def mintBridgeCell (s : RecChainedState) (actor bridgeCell : CellId) (vk : Int) :
    Option RecChainedState :=
  mintEscrowCell s actor bridgeCell vk

/-- **`mintBridgeCell_caveats` — PROVED.** When the registry IS `bridgeRegistry vk …`, the minted cell
carries the bridge state machine + deal-term immutables (installed by the executor, for life). -/
theorem mintBridgeCell_caveats {s s' : RecChainedState} {actor bridgeCell : CellId} {vk : Int}
    {amount originator pot finalityWitness asset : Int}
    (hreg : s.kernel.factories
              = bridgeRegistry vk.toNat amount originator pot finalityWitness asset)
    (h : mintBridgeCell s actor bridgeCell vk = some s') :
    s'.kernel.slotCaveats bridgeCell
      = (bridgeFactoryEntry amount originator pot finalityWitness asset).caveats :=
  mintEscrowCell_caveats hreg h

/-- **`mintBridgeCell_neutral` — PROVED.** Minting a bridge cell is conservation-NEUTRAL for every
asset (born EMPTY; the value is locked SEPARATELY by an ordinary move). -/
theorem mintBridgeCell_neutral {s s' : RecChainedState} {actor bridgeCell : CellId} {vk : Int}
    (b : AssetId) (h : mintBridgeCell s actor bridgeCell vk = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  mintEscrowCell_neutral b h

/-- **`mintBridgeCell_grows_accounts` — PROVED.** A minted bridge cell IS a live account (the mint
has teeth; neutrality is not a no-op). -/
theorem mintBridgeCell_grows_accounts {s s' : RecChainedState} {actor bridgeCell : CellId} {vk : Int}
    (h : mintBridgeCell s actor bridgeCell vk = some s') :
    bridgeCell ∈ s'.kernel.accounts :=
  mintEscrowCell_grows_accounts h

/-- **`mintBridgeCell_unknown_factory_fails` — PROVED (fail-closed).** Minting against an unknown
factory key never mints — the bridge program cannot be conjured without a published factory. -/
theorem mintBridgeCell_unknown_factory_fails (s : RecChainedState) (actor bridgeCell : CellId)
    (vk : Int) (h : findFactory s.kernel.factories vk.toNat = none) :
    mintBridgeCell s actor bridgeCell vk = none :=
  mintEscrowCell_unknown_factory_fails s actor bridgeCell vk h

/-! ## §3 — LOCK: an ordinary `move` of the cross-domain value INTO the bridge cell's `bal` column.

The originator funds the bridge by an ordinary per-asset move (`recKExecAsset`) from its own column
into the bridge cell's column — exactly the escrow factory's `depositEscrow`. After the lock the
bridge cell holds `amt` of `asset` in its `bal` column (the single source of truth for the locked
cross-domain value). -/

/-- **`lockBridge` — fund the bridge cell: move `amt` of `asset` from `originator` into `bridgeCell`'s
`bal` column.** An ordinary authorized per-asset move (`recKExecAsset`); fail-closed (authorized,
non-negative, sufficient balance, distinct live cells). This IS the W2 escrow `depositEscrow`. -/
def lockBridge (k : RecordKernelState) (originator bridgeCell : CellId) (asset : AssetId) (amt : ℤ) :
    Option RecordKernelState :=
  depositEscrow k originator bridgeCell asset amt

/-- **`lockBridge_conserves` — PROVED (KEYSTONE a, the LOCK leg).** A committed lock preserves every
asset's total supply (the value moves between two live accounts — funding the lock, not minting it).
The ordinary move law. -/
theorem lockBridge_conserves {k k' : RecordKernelState} {originator bridgeCell : CellId}
    {asset : AssetId} {amt : ℤ} (h : lockBridge k originator bridgeCell asset amt = some k')
    (b : AssetId) : recTotalAsset k' b = recTotalAsset k b :=
  depositEscrow_conserves h b

/-! ## §4 — FINALIZE / CANCEL on the FACTORY-BORN cell.

FINALIZE is the probe's `escrowRelease` (state LOCKED→FINALIZED + move the held value to the
BRIDGE-POT cell), gated on the foreign-finality witness equalling the cell's frozen `condition` slot —
the `witnessed(vk)` Pred at the executable layer. CANCEL is the probe's `escrowRefund` (state
LOCKED→CANCELLED + move the held value back to the originator). Because the finalize target is the
bridge-POT, the value does not leave the ledger — it SETTLES (the W1 repair), so conservation is the
ordinary move law for BOTH legs (no bridge-outflow exemption). -/

/-- **`finalizeBridge` — the bridge FINALIZE: move the held value to the bridge-POT, gated on the
foreign-finality witness.** The probe's `escrowRelease` with the finalize-target being the pot. -/
def finalizeBridge (k : RecordKernelState) (bridgeCell pot : CellId) (asset : AssetId)
    (finalityWitness : Int) : Option RecordKernelState :=
  escrowRelease k bridgeCell pot asset finalityWitness

/-- **`cancelBridge` — the bridge CANCEL (timeout/failure): refund the held value to the originator.**
The probe's `escrowRefund` with the refund-target being the originator. -/
def cancelBridge (k : RecordKernelState) (bridgeCell originator : CellId) (asset : AssetId) :
    Option RecordKernelState :=
  escrowRefund k bridgeCell originator asset

/-- **KEYSTONE (a) — `finalize_conserves`.** A committed finalize preserves every asset's supply: the
held value settles from the bridge cell's column to the bridge-pot cell — an ordinary move, NOT a
disclosed outflow. The W1 bridge-pot conservation, now inherited from the plain move law. -/
theorem finalize_conserves {k k' : RecordKernelState} {bridgeCell pot : CellId} {asset : AssetId}
    {finalityWitness : Int} (h : finalizeBridge k bridgeCell pot asset finalityWitness = some k')
    (b : AssetId) : recTotalAsset k' b = recTotalAsset k b :=
  escrowRelease_conserves h b

/-- **KEYSTONE (a) — `cancel_conserves`.** A committed cancel preserves every asset's supply (the
locked value returns to the originator). -/
theorem cancel_conserves {k k' : RecordKernelState} {bridgeCell originator : CellId} {asset : AssetId}
    (h : cancelBridge k bridgeCell originator asset = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b :=
  escrowRefund_conserves h b

/-- **KEYSTONE (b) — `no_double_finalize`.** Once a finalize drove the bridge cell to FINALIZED,
neither a second finalize nor a cancel commits — the installed state machine fail-closes. The locked
value crosses the bridge AT MOST ONCE. -/
theorem no_double_finalize {k : RecordKernelState} {bridgeCell tgt : CellId} {asset : AssetId}
    {finalityWitness : Int} (hfin : escrowState k bridgeCell = sFinalized) :
    finalizeBridge k bridgeCell tgt asset finalityWitness = none
      ∧ cancelBridge k bridgeCell tgt asset = none :=
  no_double_resolve hfin

/-- **KEYSTONE (b) — `no_refinalize_after_cancel`.** Once CANCELLED, neither a finalize nor a second
cancel commits (the value already returned). -/
theorem no_refinalize_after_cancel {k : RecordKernelState} {bridgeCell tgt : CellId} {asset : AssetId}
    {finalityWitness : Int} (hcan : escrowState k bridgeCell = sCancelled) :
    finalizeBridge k bridgeCell tgt asset finalityWitness = none
      ∧ cancelBridge k bridgeCell tgt asset = none :=
  no_double_resolve_refunded k bridgeCell tgt asset finalityWitness hcan

/-- **`finalize_advances_state` — PROVED.** After a committed finalize the bridge state slot reads
FINALIZED — so a SECOND finalize/cancel sees a non-LOCKED state and `no_double_finalize` bites. -/
theorem finalize_advances_state {k k' : RecordKernelState} {bridgeCell pot : CellId} {asset : AssetId}
    {finalityWitness : Int} (h : finalizeBridge k bridgeCell pot asset finalityWitness = some k') :
    escrowState k' bridgeCell = sFinalized :=
  release_advances_state h

/-- **KEYSTONE (c) — `finalize_requires_finality_witness`.** A finalize whose supplied witness ≠ the
cell's frozen foreign-finality `condition` slot is rejected — even on a LOCKED bridge cell. Nobody can
finalize the crossing without discharging the foreign-finality witness. This is the `witnessed(vk)`
Pred polarity at the executable layer (the §8 crypto portal; §HARD-iii of the escrow probe shows the
equality is a swappable abstract Pred-discharge). -/
theorem finalize_requires_finality_witness {k : RecordKernelState} {bridgeCell pot : CellId}
    {asset : AssetId} {finalityWitness : Int}
    (hbad : finalityWitness ≠ escrowCondition k bridgeCell) :
    finalizeBridge k bridgeCell pot asset finalityWitness = none :=
  release_requires_condition hbad

/-- **KEYSTONE (d) — `locked_finalizable`.** A LOCKED bridge cell with the correct finality witness and
a `SettleReady` bridge-pot finalizes (the crossing completes; the value is deliverable, not trapped). -/
theorem locked_finalizable {k : RecordKernelState} {bridgeCell pot : CellId} {asset : AssetId}
    {finalityWitness : Int} (hlocked : escrowState k bridgeCell = sLocked)
    (hcond : finalityWitness = escrowCondition k bridgeCell)
    (hr : SettleReady k bridgeCell pot asset) :
    (finalizeBridge k bridgeCell pot asset finalityWitness).isSome :=
  open_releasable hlocked hcond hr

/-- **KEYSTONE (d) — `locked_cancellable`.** A LOCKED bridge cell with a `SettleReady` originator
cancels (the abort/timeout path always returns the value). -/
theorem locked_cancellable {k : RecordKernelState} {bridgeCell originator : CellId} {asset : AssetId}
    (hlocked : escrowState k bridgeCell = sLocked) (hr : SettleReady k bridgeCell originator asset) :
    (cancelBridge k bridgeCell originator asset).isSome :=
  open_refundable hlocked hr

/-! ## §4b — the SETTLE-LIVENESS teeth (no value moved into a frozen/absent cell). -/

/-- **`finalize_requires_live_pot` — PROVED.** A finalize whose bridge-POT target is not a live account
is rejected — the move cannot deliver the crossed value into a non-account, so no locked value can be
settled into a frozen/absent pot. The factory-shape D3 teeth (the move's own fail-closed guard). -/
theorem finalize_requires_live_pot {k : RecordKernelState} {bridgeCell pot : CellId} {asset : AssetId}
    {finalityWitness : Int} (hdead : pot ∉ k.accounts) :
    finalizeBridge k bridgeCell pot asset finalityWitness = none :=
  release_requires_live_beneficiary hdead

/-- **`cancel_requires_live_originator` — PROVED.** A cancel whose originator refund target is not a
live account is rejected. -/
theorem cancel_requires_live_originator {k : RecordKernelState} {bridgeCell originator : CellId}
    {asset : AssetId} (hdead : originator ∉ k.accounts) :
    cancelBridge k bridgeCell originator asset = none :=
  refund_requires_live_depositor hdead

/-! ## §5 — NON-VACUITY: a factory-born bridge, end to end (mint → lock → finalize-to-pot / cancel /
double).

`bridgeWorld vk` PUBLISHES the bridge factory at key `vk` (amount 40, originator 2, bridge-pot 1,
finality witness 99, asset 0). Cell `0` is the privileged minter (holds a node-cap to the fresh bridge
cell `3`) and the funder; cell `1` is the bridge-pot (the foreign-chain custody cell); cell `2` is the
originator. We mint cell `3`, lock 40 into it, then witness: a finalize with the correct finality
witness settles 40 to the pot and advances to FINALIZED; a wrong witness is rejected; a cancel returns
40 to the originator; a double-finalize fails. ALL on the cell the factory actually minted, and ALL
conservation-EXACT (the finalize settles to the pot — no off-ledger drop). -/

/-- The funder/minter holds a node-cap to the fresh bridge cell `3` (so `mintAuthorizedB` admits) and
funds the lock (cell `0` holds 100 of asset 0). The bridge-pot is cell `1` (holds 5 of asset 0). The
registry publishes the bridge factory at key 7. -/
def bridgeWorld : RecChainedState :=
  { kernel :=
      { accounts := {0, 1, 2}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun c => if c = 0 then [Cap.node 3] else []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0
        factories := bridgeRegistry 7 40 2 1 99 0 }
    log := [] }

/-- Mint the bridge cell `3` from factory key 7, then lock 40 of asset 0 into it (funder = cell 0). -/
def bridgeLocked : Option RecordKernelState :=
  (mintBridgeCell bridgeWorld 0 3 7).bind (fun s => lockBridge s.kernel 0 3 0 40)

-- the factory resolves + conforms:
#guard (findFactory bridgeWorld.kernel.factories 7).isSome
#guard ((bridgeFactoryEntry 40 2 1 99 0).conforms)

-- the mint COMMITS and grows accounts, born conservation-neutral:
#guard ((mintBridgeCell bridgeWorld 0 3 7).isSome)
#guard ((mintBridgeCell bridgeWorld 0 3 7).map (fun s => decide (3 ∈ s.kernel.accounts))) == some true
#guard ((mintBridgeCell bridgeWorld 0 3 7).map (fun s => recTotalAsset s.kernel 0)) == some 105

-- the minted cell carries the bridge state machine and starts LOCKED with the finality condition 99:
#guard ((mintBridgeCell bridgeWorld 0 3 7).map (fun s => s.kernel.slotCaveats 3))
        == some (bridgeFactoryEntry 40 2 1 99 0).caveats
#guard ((mintBridgeCell bridgeWorld 0 3 7).map (fun s => escrowState s.kernel 3)) == some sLocked
#guard ((mintBridgeCell bridgeWorld 0 3 7).map (fun s => escrowCondition s.kernel 3)) == some 99

-- after lock, the bridge cell HOLDS the locked 40 in its bal column (funder 100→60); supply fixed:
#guard (bridgeLocked.map (fun k => k.bal 3 0)) == some 40
#guard (bridgeLocked.map (fun k => k.bal 0 0)) == some 60
#guard (bridgeLocked.map (fun k => recTotalAsset k 0)) == some 105

-- a CORRECT finalize (finality witness 99) settles 40 to the bridge-POT 1 (5→45), advances to FINALIZED:
#guard (bridgeLocked.bind (fun k => finalizeBridge k 3 1 0 99) |>.map (fun s => s.bal 1 0)) == some 45
#guard (bridgeLocked.bind (fun k => finalizeBridge k 3 1 0 99) |>.map (fun s => s.bal 3 0)) == some 0
#guard (bridgeLocked.bind (fun k => finalizeBridge k 3 1 0 99) |>.map (fun s => escrowState s 3)) == some sFinalized
-- ...and asset-0 total supply is FIXED — the finalize SETTLES to the pot, no off-ledger drop:
#guard (bridgeLocked.bind (fun k => finalizeBridge k 3 1 0 99) |>.map (fun s => recTotalAsset s 0)) == some 105

-- a WRONG finality witness (7 ≠ 99) is rejected (KEYSTONE c):
#guard (bridgeLocked.bind (fun k => finalizeBridge k 3 1 0 7) |>.isSome) == false

-- a CANCEL returns 40 to the originator 2 (0→40) and advances to CANCELLED:
#guard (bridgeLocked.bind (fun k => cancelBridge k 3 2 0) |>.map (fun s => s.bal 2 0)) == some 40
#guard (bridgeLocked.bind (fun k => cancelBridge k 3 2 0) |>.map (fun s => escrowState s 3)) == some sCancelled
#guard (bridgeLocked.bind (fun k => cancelBridge k 3 2 0) |>.map (fun s => recTotalAsset s 0)) == some 105

-- NO-DOUBLE-FINALIZE: finalize then a second finalize AND a cancel both fail (KEYSTONE b):
#guard (bridgeLocked.bind (fun k => finalizeBridge k 3 1 0 99) |>.bind (fun s => finalizeBridge s 3 1 0 99) |>.isSome) == false
#guard (bridgeLocked.bind (fun k => finalizeBridge k 3 1 0 99) |>.bind (fun s => cancelBridge s 3 2 0) |>.isSome) == false

-- an UNKNOWN factory key never mints (fail-closed):
#guard ((mintBridgeCell bridgeWorld 0 3 99).isSome) == false

/-! ## §6 — the W1 BRIDGE-POT framing (the conservation contrast, made explicit).

The factory-born finalize settles to the bridge-pot cell, so it is conservation-EXACT — exactly the W1
repair the issuer-supply probe made for the verb-era bridge (modelling the foreign chain's custody as a
pot CELL instead of an off-ledger drop). We re-export the probe's pot law here so the cell-program and
the verb-era pot law sit side by side: BOTH say "settle the finalized value to the pot cell and the
per-asset ledger stays EXACT", and the cell-program path gets it from the ORDINARY move law
(`finalize_conserves`) with NO bespoke combined measure. (`ExactLedger` = the per-asset exact
conservation invariant `∀ a, recTotalAssetWithEscrow k a = 0`, the W1 forward-model value law.) -/

open Dregg2.Substrate.IssuerSupplyProbe (ExactLedger)

/-- **`potted_finalize_is_exact` — the verb-era W1 bridge-pot law, re-exported.** The W1 result that the
verb-era `bridgeFinalizeToPotK` settles to a pot cell preserving the EXACT per-asset ledger. The
cell-program `finalize_conserves` above is the SAME guarantee on the factory-born cell, inherited from
the plain move law instead of the combined-measure pot theorem. -/
theorem potted_finalize_is_exact {pot : CellId} {k k' : RecordKernelState} {id : Nat}
    (h : Dregg2.Substrate.IssuerSupplyProbe.bridgeFinalizeToPotK pot k id = some k')
    (hex : ExactLedger k) : ExactLedger k' :=
  Dregg2.Substrate.IssuerSupplyProbe.bridgeFinalizeToPot_preserves_exact h hex

/-- **`verb_finalize_breaks_exact` — the NON-VACUITY contrast (re-exported W1 tooth).** The verb-era
`bridgeFinalizeKAsset` (the disclosed outflow, NOT settled to a pot) provably BREAKS the exact ledger —
so the bridge-pot / bridge-cell settle is a genuine REPAIR, not a relabeling. -/
theorem verb_finalize_breaks_exact {k k' : RecordKernelState} {id : Nat} {asset : AssetId}
    {amount : ℤ} (h : Dregg2.Exec.bridgeFinalizeKAsset k id asset amount = some k') (hnz : amount ≠ 0)
    (hex : ExactLedger k) : ¬ ExactLedger k' :=
  Dregg2.Substrate.IssuerSupplyProbe.bridgeFinalize_breaks_exact h hnz hex

/-! ## §7 — Axiom hygiene. -/

#assert_axioms bridgeFactoryEntry_conforms
#assert_axioms bridgeRegistry_finds
#assert_axioms mintBridgeCell_caveats
#assert_axioms mintBridgeCell_neutral
#assert_axioms mintBridgeCell_grows_accounts
#assert_axioms mintBridgeCell_unknown_factory_fails
#assert_axioms lockBridge_conserves
#assert_axioms finalize_conserves
#assert_axioms cancel_conserves
#assert_axioms no_double_finalize
#assert_axioms no_refinalize_after_cancel
#assert_axioms finalize_advances_state
#assert_axioms finalize_requires_finality_witness
#assert_axioms locked_finalizable
#assert_axioms locked_cancellable
#assert_axioms finalize_requires_live_pot
#assert_axioms cancel_requires_live_originator
#assert_axioms potted_finalize_is_exact
#assert_axioms verb_finalize_breaks_exact

/-! ## §DELETION — the bridge-verb deletion-readiness list (land-before-kill).

THIS module is the LAND-BEFORE-KILL prerequisite for the bridge family. Once the bridge factory is the
live cross-domain path (this module shipped + every bridge consumer re-pointed), W2 DELETES the bridge
verb family, which shares the SAME off-ledger `escrows` store as escrow (the `bridge := true` tag):

  WHAT W2 DELETES (the bridge surface — `Dregg2.Exec.RecordKernel`):
    (1) the THREE bridge kernel arms + their raw bodies:
          • `bridgeLockKAsset` / `createBridgeRawAsset`        (replaced by: `mintBridgeCell` +
            `lockBridge` = `createCellFromFactoryA` + the ordinary move IN);
          • `bridgeFinalizeKAsset` / `bridgeFinalizeRawAsset`  (replaced by: `finalizeBridge` = the
            move OUT to the bridge-pot, gated on the finality witness — `escrowRelease`);
          • `bridgeCancelKAsset`                                (replaced by: `cancelBridge` = the move
            OUT to the originator — `escrowRefund`).
    (2) the `bridge : Bool` TAG on `EscrowRecord` (`RecordKernel.lean:~269`) — DISSOLVED, because the
        bridge no longer parks a record in the shared store; its value lives in the minted cell's `bal`
        column and its lifecycle in the cell's `state` slot. (The tag's only job was to separate the
        two RESOLUTION semantics in the shared store; with no shared store the distinction is the
        finalize-target, the pot, not a record flag.)
    (3) the bridge-specific combined-measure theory:
          • `bridge_lock_conserves_combined_per_asset`
          • `bridge_cancel_conserves_combined_per_asset`
          • `bridgeFinalizeKAsset_moves_combined_per_asset` (the disclosed-outflow accounting)
        all DIE, because bridge conservation is now the ORDINARY per-asset move law
        (`recKExecAsset_conserves_per_asset`, lifted as `lockBridge/finalize/cancel_conserves`).
    (4) the W1 bridge-OUTFLOW EXEMPTION machinery:
          • `bridgeFinalize_breaks_exact` (the non-vacuity tooth — kept ONLY as the `§6` contrast,
            then retired with the verb);
          • `bridgeFinalizeToPotK` / `bridgeFinalizeToPot_preserves_exact` — the verb-era pot REPAIR is
            SUBSUMED by the cell-program finalize-to-pot (`finalize_conserves`): the pot is now just the
            finalize MOVE TARGET, not a bespoke settle verb. (`canonical_bridge_law` retires with it.)
    (5) the Argus IR welds for the deleted arms (`Circuit/Argus/Effects/BridgeLock.lean`,
        `BridgeFinalize.lean`, `BridgeCancel.lean`) re-point to the factory + move + setField welds
        (the SAME re-point the escrow Argus welds get) — NOT deleted blindly; re-welded onto the
        cell-program path.

  WHAT MUST BE RE-POINTED FIRST (the land-before-kill blockers — every bridge-verb consumer):
    • `Dregg2.Apps.CrossChainBridgeGated` — the headline bridge app; re-point to `bridgeFactoryEntry`
      + `mintBridgeCell`/`lockBridge`/`finalizeBridge`/`cancelBridge`. (This is the §VERDICT consumer.)
    • any `StakedSlaGated` / obligation twin that SHARES the `EscrowRecord.bridge` store — DECIDE
      per-family (per the escrow §DELETION ordering constraint): the shared `EscrowRecord` field and
      the `bridge` tag cannot be removed while a non-bridge consumer still reads the shared store. The
      bridge tag itself is deleted FIRST (only bridge reads it); the shared `escrows` field follows the
      escrow-family burn-down.
    • the executor `FullActionA` bridge arms (`.bridgeLockA` / `.bridgeFinalizeA` / `.bridgeCancelA`)
      + chain ops — re-point to `createCellFromFactoryA` + `balanceA`/`setFieldA` over
      `bridgeFactoryEntry`, mirroring the escrow `§DELETION` (1).

  ORDERING NOTE (the one genuine constraint): the bridge `§DELETION` is GATED on the escrow `§DELETION`
  for the SHARED `escrows` field, but the bridge `bridge` TAG and the three bridge arms can be removed
  INDEPENDENTLY (they are bridge-only) once `CrossChainBridgeGated` is re-pointed. The bridge-pot
  framing (§6) is the bridge family's analog of the escrow factory's no-side-table payoff.

  NOT DELETED HERE (land-before-kill): nothing above is removed in this commit — we only prove the
  factory is a faithful replacement + enumerate the burn-down. The verb deletion is the SUBSEQUENT W2
  commit, gated on the re-points above all landing green.
-/

end Dregg2.Apps.BridgeCell
