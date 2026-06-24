/-
# Dregg2.Apps.Obligation — the STANDING (recurring) OBLIGATION as a REAL, app-instantiable factory cell.

THE THIRD HOUSE ROOM, welded (after the vault + allowance). A standing obligation is a first-class,
schedule-enforced recurring commitment: a cell OWES a FIXED amount to a beneficiary every PERIOD blocks
— a subscription / salary / rent the protocol itself enforces on schedule. An agent ENTERS an obligation
it cannot escape silently: the schedule + amount are bound into the cell, so it can neither FORGE the
terms, nor UNDERPAY a period, nor DISCHARGE EARLY, nor REPLAY a discharged period. This module PROMOTES
the falsification probe (`Dregg2.Verify.ObligationFactoryProbe` — PASS) from a shape study into a LIVE
path: the obligation factory is a published `FactoryEntry` an app registers and instantiates via the
EXISTING factory executor `createCellFromFactoryChainA` (`Dregg2.Exec.TurnExecutorFull`).

A standing obligation is a COMPOSITION, NOT a new kernel verb: it earns NO `FullActionA` arm. Entering an
obligation (freeze the amount/period terms) + funding it + discharging period after period are the
already-wired `CreateCellFromFactory` + `Transfer` + `SetField` turns — light-client-verifiable. So:

  * the obligation factory is a published `FactoryEntry` (`obligationFactoryEntry`) an app registers in
    the kernel's `factories` registry and instantiates via `createCellFromFactoryA actor cell vk`;
  * the executor INSTALLS the factory's `slotCaveats` (the four deal-term immutables — the FROZEN amount
    + schedule — + the monotone `nextDue` cursor + the monotone `dischargedCount`) onto the minted cell
    for its WHOLE LIFE (`mintObligationCell_installs_caveats`), so the schedule is enforced by
    `stateStepGuarded` on every later `SetField`, not by an off-ledger guard;
  * the payable VALUE lives in the minted cell's own per-asset `bal` column (a `fund` is an ordinary
    `move` IN; a `discharge` is an ordinary `move` OUT — the probe's `obligationSettle`), so the
    obligation inherits the kernel's per-asset move conservation law VERBATIM, with NO side-table.

The four obligation-safety keystones (conservation / fixed-amount / no-forged-or-early-discharge /
due-period-dischargeable) are RE-ESTABLISHED on the FACTORY-BORN cell here — on the cell whose caveats
the executor actually installed — by feeding the factory-install facts into the probe's keystones.

## The shape (the published deliverable)

`obligationFactoryEntry beneficiary amount period start : FactoryEntry`
  caveats       = Immutable {beneficiary, amount, period, start}
                  ++ Monotonic nextDue ++ Monotonic dischargedCount   -- the schedule cursors
  initialFields = state=open, beneficiary, amount, period, start, nextDue=start, dischargedCount=0
  programVk     = 0

`obligationRegistry vk` installs it at content-addressed key `vk`; `mintObligationCell` runs the real
factory executor; `fundObligation` moves the payable value into the minted cell's `bal`; a discharge is
the probe's `obligationDischarge` on that cell.

NEW file. Imports the probe + the factory executor; does NOT touch `cell/src/capability.rs`/`seal.rs`,
`Argus/Compile.lean`, or the Substrate/Dynamics files. `#assert_axioms`-pinned to
`{propext, Classical.choice, Quot.sound}`.
-/
import Dregg2.Verify.ObligationFactoryProbe
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Apps.Obligation

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Cap)
open Dregg2.Verify.ObligationFactoryProbe
open Dregg2.Exec.EffectsState (fieldOf setField)

/-! ## §1 — The obligation FACTORY ENTRY (the published `FactoryEntry`).

This IS the probe's `obligationFactory` descriptor (re-exported under an app-facing name): the four
deal-term immutables (the FROZEN amount + schedule — no-forge) + the two monotone cursors (`nextDue`
advances only forward, `dischargedCount` never regresses). The factory's own initial state CONFORMS to
its own caveats (`obligationFactory_conforms`, proved in the probe). -/

/-- **The obligation factory entry.** Mints an obligation cell carrying the frozen amount/period terms +
the monotone schedule cursors; the payable value is held in the minted cell's `bal` column. -/
def obligationFactoryEntry (beneficiary amount period start : Int) : FactoryEntry :=
  obligationFactory beneficiary amount period start

/-- The obligation factory conforms to its own published invariants (re-exported probe keystone; every
caveat is a TRANSITION caveat permitting the genesis first write). -/
theorem obligationFactoryEntry_conforms (beneficiary amount period start : Int) :
    (obligationFactoryEntry beneficiary amount period start).conforms = true :=
  obligationFactory_conforms beneficiary amount period start

/-- A kernel factory registry that publishes the obligation factory at content-addressed key `vk`. An
app installs this into `s.kernel.factories` so `createCellFromFactoryA actor cell vk` resolves it. -/
def obligationRegistry (vk : Nat) (beneficiary amount period start : Int) :
    List (Nat × FactoryEntry) :=
  [(vk, obligationFactoryEntry beneficiary amount period start)]

/-- The registry resolves the obligation factory at exactly its published key. -/
theorem obligationRegistry_finds (vk : Nat) (beneficiary amount period start : Int) :
    findFactory (obligationRegistry vk beneficiary amount period start) vk
      = some (obligationFactoryEntry beneficiary amount period start) := by
  simp [obligationRegistry, findFactory]

/-! ## §2 — MINTING the obligation cell through the REAL factory executor.

`mintObligationCell` is `createCellFromFactoryChainA` over a kernel whose `factories` registry publishes
the obligation factory. The minted cell carries the factory's caveats (the frozen amount + schedule + the
monotone cursors) AND its initial fields (state=open + the frozen terms + the cursor at `start`) —
installed by the executor, for life. -/

/-- Mint an obligation cell from the obligation factory at key `vk` (the real factory executor). -/
def mintObligationCell (s : RecChainedState) (actor cell : CellId) (vk : Int) :
    Option RecChainedState :=
  createCellFromFactoryChainA s actor cell vk

/-- **`mintObligationCell_installs_caveats` (the factory keystone, obligation-specialized).** A minted
obligation cell carries EXACTLY the obligation factory's caveats — the four deal-term immutables (the
FROZEN amount + schedule) PLUS the monotone `nextDue` cursor PLUS the monotone `dischargedCount` —
installed by the executor, so `stateStepGuarded` enforces them on every later `SetField`. Reuses
`createCellFromFactoryChainA_installs_program`. -/
theorem mintObligationCell_installs_caveats {s s' : RecChainedState} {actor cell : CellId}
    {vk : Int} (e : FactoryEntry)
    (hreg : findFactory s.kernel.factories vk.toNat = some e)
    (h : mintObligationCell s actor cell vk = some s') :
    s'.kernel.slotCaveats cell = e.caveats := by
  obtain ⟨e', hfind, hcav⟩ := createCellFromFactoryChainA_installs_program h
  rw [hreg] at hfind
  rw [← (Option.some.injEq _ _).mp hfind] at hcav
  exact hcav

/-- **`mintObligationCell_caveats`.** When the registry IS `obligationRegistry vk …`, the minted cell
carries the schedule cursors + deal-term immutables (concretely). -/
theorem mintObligationCell_caveats {s s' : RecChainedState} {actor cell : CellId} {vk : Int}
    {beneficiary amount period start : Int}
    (hreg : s.kernel.factories = obligationRegistry vk.toNat beneficiary amount period start)
    (h : mintObligationCell s actor cell vk = some s') :
    s'.kernel.slotCaveats cell
      = (obligationFactoryEntry beneficiary amount period start).caveats := by
  have hfind : findFactory s.kernel.factories vk.toNat
      = some (obligationFactoryEntry beneficiary amount period start) := by
    rw [hreg]; exact obligationRegistry_finds vk.toNat beneficiary amount period start
  exact mintObligationCell_installs_caveats _ hfind h

/-- **`mintObligationCell_neutral`.** Minting an obligation cell is conservation-NEUTRAL for every asset
(the cell is born EMPTY; the value is funded SEPARATELY by an ordinary move). Reuses
`createCellFromFactoryChainA_neutral`. -/
theorem mintObligationCell_neutral {s s' : RecChainedState} {actor cell : CellId} {vk : Int}
    (b : AssetId) (h : mintObligationCell s actor cell vk = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  createCellFromFactoryChainA_neutral b h

/-- **`mintObligationCell_grows_accounts`.** A minted obligation cell IS a live account (the mint has
teeth). -/
theorem mintObligationCell_grows_accounts {s s' : RecChainedState} {actor cell : CellId} {vk : Int}
    (h : mintObligationCell s actor cell vk = some s') :
    cell ∈ s'.kernel.accounts :=
  createCellFromFactoryChainA_grows_accounts h

/-- **`mintObligationCell_unknown_factory_fails` (fail-closed).** Minting against an unknown factory key
never mints. The obligation program cannot be conjured without a published factory. -/
theorem mintObligationCell_unknown_factory_fails (s : RecChainedState) (actor cell : CellId)
    (vk : Int) (h : findFactory s.kernel.factories vk.toNat = none) :
    mintObligationCell s actor cell vk = none :=
  createCellFromFactoryChainA_unknown_factory_fails s actor cell vk h

/-! ## §3 — FUND: an ordinary `move` of the payable value INTO the minted cell's `bal` column.

The granter funds the obligation by an ordinary per-asset move (`recKExecAsset`) from its own column into
the obligation cell's column. After the fund the obligation cell HOLDS the payable value in its `bal`
column (the single source of truth — there is NO second "amount-held" slot to keep relationally in
sync; the per-period `amount` is the FIXED owed quantity, not a held balance). -/

/-- **`fundObligation` — fund the obligation cell: move `amt` of `asset` from `granter` into `cell`'s
`bal` column.** An ordinary authorized per-asset move (`recKExecAsset`); fail-closed. -/
def fundObligation (k : RecordKernelState) (granter cell : CellId) (asset : AssetId) (amt : ℤ) :
    Option RecordKernelState :=
  recKExecAsset k { actor := granter, src := granter, dst := cell, amt := amt } asset

/-- **`fundObligation_conserves`.** A committed fund preserves every asset's total supply (the value
moves between two live accounts — funding the obligation, not minting it). The ordinary move law. -/
theorem fundObligation_conserves {k k' : RecordKernelState} {granter cell : CellId}
    {asset : AssetId} {amt : ℤ} (h : fundObligation k granter cell asset amt = some k')
    (b : AssetId) : recTotalAsset k' b = recTotalAsset k b :=
  recKExecAsset_conserves_per_asset k k'
    { actor := granter, src := granter, dst := cell, amt := amt } asset h b

/-! ## §4 — DISCHARGE on the FACTORY-BORN cell (the probe keystones, re-established here).

The obligation discharge is the probe's `obligationDischarge` — it reads the committed amount/cursor the
factory installed, advances the cursor by one period + the discharged count, and moves exactly the fixed
amount out, gated on the schedule (the block must have reached the current period's due block). We
re-export it under an app-facing name and LIFT the probe's keystones onto the factory-born cell by
observing that a factory-minted-then-funded cell is exactly the `RecordKernelState` the probe's theorems
quantify over (state slot = open, frozen terms, value in `bal`). -/

/-- App-facing discharge (the probe's `obligationDischarge`): advance the schedule cursor by one period +
the discharged count + move exactly `amount` to the beneficiary, gated on `nextDue ≤ atBlock` (the period
is due — no early discharge) and `amount = committed amount` (the fixed amount — no under/over-pay). -/
abbrev discharge := @obligationDischarge

/-- **KEYSTONE (a) — `discharge_conserves`.** A committed discharge on the factory-born cell preserves
every asset's supply (the value is delivered from the held column, not conjured). -/
theorem discharge_conserves {k k' : RecordKernelState} {e beneficiary : CellId} {asset : AssetId}
    {atBlock amount : Int}
    (h : obligationDischarge k e beneficiary asset atBlock amount = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b :=
  obligationDischarge_conserves h b

/-- **KEYSTONE (b) — `wrong_amount_rejected`.** A discharge whose moved amount differs from the committed
per-period amount is rejected on the factory-born cell — the amount is FIXED, neither over- nor
under-payable. -/
theorem wrong_amount_rejected (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId)
    (atBlock amount : Int) (hwrong : amount ≠ obligationAmount k e) :
    obligationDischarge k e beneficiary asset atBlock amount = none :=
  Dregg2.Verify.ObligationFactoryProbe.wrong_amount_rejected k e beneficiary asset atBlock amount hwrong

/-- **KEYSTONE (c, early) — `early_discharge_rejected`.** A discharge whose block has NOT reached the
current period's due block (`atBlock < nextDue`) is rejected — no early payment; each period waits for
its due block, even on an OPEN factory-born obligation. -/
theorem early_discharge_rejected (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId)
    (atBlock amount : Int) (hearly : atBlock < obligationNextDue k e) :
    obligationDischarge k e beneficiary asset atBlock amount = none :=
  Dregg2.Verify.ObligationFactoryProbe.early_discharge_rejected k e beneficiary asset atBlock amount hearly

/-- **KEYSTONE (c, replay) — `replay_rejected`.** Once the committed cursor has advanced past a period's
due block (the `Monotonic nextDue` caveat only advances it forward), a second discharge presented at that
old due block is rejected — a discharged period is SPENT (the one-shot-per-period nullifier shape). -/
theorem replay_rejected (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId)
    (oldDue amount : Int) (hspent : oldDue < obligationNextDue k e) :
    obligationDischarge k e beneficiary asset oldDue amount = none :=
  Dregg2.Verify.ObligationFactoryProbe.replay_rejected k e beneficiary asset oldDue amount hspent

/-- **KEYSTONE (d) — `due_period_dischargeable`.** An OPEN factory-born obligation whose current period
is DUE (`nextDue ≤ atBlock`), discharging exactly the committed amount, with a `DischargeReady`
beneficiary, DISCHARGES (the due payment is deliverable, not trapped). -/
theorem due_period_dischargeable (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId)
    (atBlock : Int)
    (hdue : obligationNextDue k e ≤ atBlock)
    (hr : DischargeReady k e beneficiary asset (obligationAmount k e)) :
    (obligationDischarge k e beneficiary asset atBlock (obligationAmount k e)).isSome :=
  Dregg2.Verify.ObligationFactoryProbe.due_period_dischargeable k e beneficiary asset atBlock hdue hr

/-! ## §4b — The DISCHARGE-LIVENESS TOOTH (the factory-shape analog of the move's fail-closed guard).

In the factory shape the value moves by an ordinary `recKExecAsset`, whose OWN fail-closed guard requires
`dst ∈ accounts`: a discharge whose beneficiary is NOT a live account is rejected, for FREE, by the move
law — the payment can never be moved into a non-account. -/

/-- **`discharge_requires_live_beneficiary`.** A discharge whose beneficiary is not a live account is
rejected (the move cannot deliver value into a non-account). -/
theorem discharge_requires_live_beneficiary (k : RecordKernelState)
    {e beneficiary : CellId} {asset : AssetId} {atBlock amount : Int}
    (hdead : beneficiary ∉ k.accounts) :
    obligationDischarge k e beneficiary asset atBlock amount = none := by
  unfold obligationDischarge
  by_cases hg : obligationNextDue k e ≤ atBlock ∧ amount = obligationAmount k e
  · rw [if_pos hg]
    unfold obligationSettle recKExecAsset
    rw [if_neg]
    rintro ⟨_, _, _, _, _, htgt, _⟩
    exact hdead htgt
  · rw [if_neg hg]

/-! ## §5 — NON-VACUITY: a factory-born obligation, end to end (mint → fund → discharge / early / wrong).

`facWorld vk` is a kernel that PUBLISHES the obligation factory at key `vk` (beneficiary 1, amount 50,
period 100, start 1000). Cell `0` is the privileged minter (holds a node-cap to the fresh obligation cell
`3` so the mint is authorized) and the funder; cell `1` is the beneficiary. We mint cell `3` from the
factory, fund 1000 into it, then witness: an on-schedule discharge delivers the fixed amount and advances
the cursor; an early discharge is rejected; a wrong amount is rejected. ALL on the cell the factory
actually minted. -/

/-- The funder/minter holds a node-cap to the fresh obligation cell `3` (so `mintAuthorizedB` admits) and
funds the obligation (cell `0` holds 2000 of asset 0). The registry publishes the obligation factory at
key 7 (beneficiary 1, amount 50, period 100, start 1000). -/
def facWorld : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun c => if c = 0 then [Cap.node 3] else []
        bal := fun c a => if c = 0 then (if a = 0 then 2000 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0
        factories := obligationRegistry 7 1 50 100 1000 }
    log := [] }

/-- Mint the obligation cell `3` from factory key 7, then fund 1000 of asset 0 into it (funder = cell 0). -/
def facFunded : Option RecordKernelState :=
  (mintObligationCell facWorld 0 3 7).bind (fun s => fundObligation s.kernel 0 3 0 1000)

-- the factory resolves + conforms:
#guard (findFactory facWorld.kernel.factories 7).isSome                                  -- some (obligation factory)
#guard ((obligationFactoryEntry 1 50 100 1000).conforms)                                 -- true

-- the mint COMMITS and grows accounts, born conservation-neutral:
#guard ((mintObligationCell facWorld 0 3 7).isSome)                                      -- true (minted!)
#guard ((mintObligationCell facWorld 0 3 7).map (fun s => decide (3 ∈ s.kernel.accounts))) == some true
#guard ((mintObligationCell facWorld 0 3 7).map (fun s => recTotalAsset s.kernel 0)) == some 2005

-- the minted cell carries the obligation caveats + reads its frozen terms (amount 50, cursor at start):
#guard ((mintObligationCell facWorld 0 3 7).map (fun s => s.kernel.slotCaveats 3))
        == some (obligationFactoryEntry 1 50 100 1000).caveats
#guard ((mintObligationCell facWorld 0 3 7).map (fun s => obligationAmount s.kernel 3)) == some 50
#guard ((mintObligationCell facWorld 0 3 7).map (fun s => obligationNextDue s.kernel 3)) == some 1000
#guard ((mintObligationCell facWorld 0 3 7).map (fun s => obligationDischarged s.kernel 3)) == some 0

-- after fund, the obligation cell HOLDS the payable 1000 in its bal column (funder 2000→1000); supply fixed:
#guard (facFunded.map (fun k => k.bal 3 0)) == some 1000                                  -- payable value in bal
#guard (facFunded.map (fun k => k.bal 0 0)) == some 1000                                  -- funder debited
#guard (facFunded.map (fun k => recTotalAsset k 0)) == some 2005                          -- conserved

-- an ON-SCHEDULE discharge (period 0 at block 1000 = the due block, amount 50) delivers 50 to beneficiary
-- 1 (5→55), advances the cursor (1000→1100) + count (0→1), and conserves supply:
#guard (facFunded.bind (fun k => obligationDischarge k 3 1 0 1000 50) |>.map (fun s => s.bal 1 0)) == some 55
#guard (facFunded.bind (fun k => obligationDischarge k 3 1 0 1000 50) |>.map (fun s => s.bal 3 0)) == some 950
#guard (facFunded.bind (fun k => obligationDischarge k 3 1 0 1000 50) |>.map (fun s => obligationNextDue s 3)) == some 1100
#guard (facFunded.bind (fun k => obligationDischarge k 3 1 0 1000 50) |>.map (fun s => obligationDischarged s 3)) == some 1
#guard (facFunded.bind (fun k => obligationDischarge k 3 1 0 1000 50) |>.map (fun s => recTotalAsset s 0)) == some 2005

-- an EARLY discharge (block 999 < due block 1000) is REJECTED (KEYSTONE c — no early payment):
#guard (facFunded.bind (fun k => obligationDischarge k 3 1 0 999 50) |>.isSome) == false
-- a WRONG amount (51 ≠ 50 overpay, or 49 underpay) is REJECTED (KEYSTONE b — the amount is FIXED):
#guard (facFunded.bind (fun k => obligationDischarge k 3 1 0 1000 51) |>.isSome) == false
#guard (facFunded.bind (fun k => obligationDischarge k 3 1 0 1000 49) |>.isSome) == false

-- THE SCHEDULE MARCHES + NO REPLAY: discharge period 0 (1000), then period 1 (1100) — both commit and the
-- cursor advances; but a SECOND discharge at the old due block 1000 (now < cursor 1100) is rejected:
#guard (facFunded.bind (fun k => obligationDischarge k 3 1 0 1000 50)
          |>.bind (fun k => obligationDischarge k 3 1 0 1100 50) |>.map (fun s => obligationNextDue s 3)) == some 1200
#guard (facFunded.bind (fun k => obligationDischarge k 3 1 0 1000 50)
          |>.bind (fun k => obligationDischarge k 3 1 0 1100 50) |>.map (fun s => obligationDischarged s 3)) == some 2
#guard (facFunded.bind (fun k => obligationDischarge k 3 1 0 1000 50)
          |>.bind (fun k => obligationDischarge k 3 1 0 1100 50) |>.map (fun s => s.bal 1 0)) == some 105
-- ...the replay of period 0 (at block 1000, after the cursor advanced to 1100) is rejected — no double-pay:
#guard (facFunded.bind (fun k => obligationDischarge k 3 1 0 1000 50)
          |>.bind (fun k => obligationDischarge k 3 1 0 1000 50) |>.isSome) == false

-- an UNKNOWN factory key never mints (fail-closed):
#guard ((mintObligationCell facWorld 0 3 99).isSome) == false

/-! ## §VERDICT — the standing obligation is a LIVE factory-settled cell.

An agent ENTERS a standing obligation (mints the factory cell with the frozen per-period amount + period
terms, funds it), and discharges it period after period — the schedule + amount enforced so it can be
neither FORGED (the terms are frozen immutables) nor UNDERPAID (the amount is fixed) nor DISCHARGED EARLY
(the block must reach the period's due block) nor REPLAYED (the cursor is monotone) — all via the EXISTING
wired `CreateCellFromFactory` + `Transfer` + `SetField` turns, NO new `Effect`. The four
obligation-safety keystones (conservation / fixed-amount / no-forged-or-early-discharge /
due-period-dischargeable) hold on the FACTORY-BORN cell. This is the recurring sibling of the one-shot
bonded obligation (`Dregg2.Apps.ObligationFactory`); the bespoke heap-cell `cell/src/obligation_standing.rs`
library is superseded by this factory route, the same dissolution the vault + allowance + escrow families
made.

RESIDUALS (honest, the SAME the whole settlement family carries): the SDK-builder constructing the only
sensible discharge turn (binding `beneficiary` as the move target + advancing the cursor by exactly
`period`) is the off-program binding the settlement family's payout target is; an optional bounded count
(stop after N periods) is the SDK builder's discharge-turn precondition, not a new constraint kind;
eventual-settlement liveness is consensus-layer. None is obligation-specific.
-/

#assert_axioms obligationFactoryEntry_conforms
#assert_axioms obligationRegistry_finds
#assert_axioms mintObligationCell_installs_caveats
#assert_axioms mintObligationCell_caveats
#assert_axioms mintObligationCell_neutral
#assert_axioms mintObligationCell_grows_accounts
#assert_axioms mintObligationCell_unknown_factory_fails
#assert_axioms fundObligation_conserves
#assert_axioms discharge_conserves
#assert_axioms wrong_amount_rejected
#assert_axioms early_discharge_rejected
#assert_axioms replay_rejected
#assert_axioms due_period_dischargeable
#assert_axioms discharge_requires_live_beneficiary

end Dregg2.Apps.Obligation
