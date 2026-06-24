/-
# Dregg2.Apps.Allowance — the rate-limited ALLOWANCE as a REAL, app-instantiable factory cell.

THE SECOND HOUSE ROOM, welded (after the vault). An allowance is a sub-capability that may spend up to a
fixed CEILING of value per epoch, the ceiling enforced so it can be neither EXCEEDED nor FORGED,
refilling each epoch — pocket money an agent hands a sub-agent that the sub-agent literally CANNOT
overspend within an epoch. This module PROMOTES the falsification probe
(`Dregg2.Verify.AllowanceFactoryProbe` — PASS) from a shape study into a LIVE path: the allowance
factory is a published `FactoryEntry` an app registers and instantiates via the EXISTING factory
executor `createCellFromFactoryChainA` (`Dregg2.Exec.TurnExecutorFull`).

An allowance is a COMPOSITION, NOT a new kernel verb: it earns NO `FullActionA` arm. Creating an
allowance (freeze the ceiling/epoch terms) + funding it + the beneficiary spending up to the ceiling are
the already-wired `CreateCellFromFactory` + `Transfer` + `SetField` turns — light-client-verifiable. So:

  * the allowance factory is a published `FactoryEntry` (`allowanceFactoryEntry`) an app registers in
    the kernel's `factories` registry and instantiates via `createCellFromFactoryA actor cell vk`;
  * the executor INSTALLS the factory's `slotCaveats` (the four deal-term immutables — the FROZEN
    ceiling — + the monotone epoch cursor + the `boundedBy spentThisEpoch 0 limit` per-epoch ceiling)
    onto the minted cell for its WHOLE LIFE (`mintAllowanceCell_installs_caveats`), so the ceiling is
    enforced by `stateStepGuarded` on every later `SetField`, not by an off-ledger guard;
  * the spendable VALUE lives in the minted cell's own per-asset `bal` column (a `fund` is an ordinary
    `move` IN; a `spend` is an ordinary `move` OUT — the probe's `allowanceSettle`), so the allowance
    inherits the kernel's per-asset move conservation law VERBATIM, with NO side-table.

The four allowance-safety keystones (conservation / ceiling-no-over-limit / no-forged-or-early-refill /
within-budget-spendable) are RE-ESTABLISHED on the FACTORY-BORN cell here — on the cell whose caveats
the executor actually installed — by feeding the factory-install facts into the probe's keystones.

## The shape (the published deliverable)

`allowanceFactoryEntry beneficiary limit epochLength start : FactoryEntry`
  caveats       = Immutable {beneficiary, limit, epochLength, start}
                  ++ Monotonic currentEpoch ++ boundedBy spentThisEpoch [0, limit]   -- the ceiling teeth
  initialFields = state=open, beneficiary, limit, epochLength, start, currentEpoch=0, spentThisEpoch=0
  programVk     = 0

`allowanceRegistry vk` installs it at content-addressed key `vk`; `mintAllowanceCell` runs the real
factory executor; `fundAllowance` moves the spendable value into the minted cell's `bal`; a spend is the
probe's `allowanceSpend` on that cell.

NEW file. Imports the probe + the factory executor; does NOT touch `cell/src/capability.rs`/`seal.rs`,
`Argus/Compile.lean`, or the Substrate/Dynamics files. `#assert_axioms`-pinned to
`{propext, Classical.choice, Quot.sound}`.
-/
import Dregg2.Verify.AllowanceFactoryProbe
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Apps.Allowance

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Cap)
open Dregg2.Verify.AllowanceFactoryProbe
open Dregg2.Exec.EffectsState (fieldOf setField)

/-! ## §1 — The allowance FACTORY ENTRY (the published `FactoryEntry`).

This IS the probe's `allowanceFactory` descriptor (re-exported under an app-facing name): the four
deal-term immutables (the FROZEN ceiling — no-forge) + the monotone epoch cursor + the
`boundedBy spentThisEpoch [0, limit]` per-epoch ceiling. The factory's own initial state CONFORMS to
its own caveats (`allowanceFactory_conforms`, proved in the probe). -/

/-- **The allowance factory entry.** Mints an allowance cell carrying the frozen ceiling/epoch terms +
the per-epoch ceiling teeth; the spendable value is held in the minted cell's `bal` column. -/
def allowanceFactoryEntry (beneficiary limit epochLength start : Int) : FactoryEntry :=
  allowanceFactory beneficiary limit epochLength start

/-- The allowance factory conforms to its own published invariants (re-exported probe keystone; the
`boundedBy [0, limit]` born-at-0 spent counter needs a well-formed `0 ≤ limit` ceiling). -/
theorem allowanceFactoryEntry_conforms (beneficiary limit epochLength start : Int) (hlim : 0 ≤ limit) :
    (allowanceFactoryEntry beneficiary limit epochLength start).conforms = true :=
  allowanceFactory_conforms beneficiary limit epochLength start hlim

/-- A kernel factory registry that publishes the allowance factory at content-addressed key `vk`. An
app installs this into `s.kernel.factories` so `createCellFromFactoryA actor cell vk` resolves it. -/
def allowanceRegistry (vk : Nat) (beneficiary limit epochLength start : Int) :
    List (Nat × FactoryEntry) :=
  [(vk, allowanceFactoryEntry beneficiary limit epochLength start)]

/-- The registry resolves the allowance factory at exactly its published key. -/
theorem allowanceRegistry_finds (vk : Nat) (beneficiary limit epochLength start : Int) :
    findFactory (allowanceRegistry vk beneficiary limit epochLength start) vk
      = some (allowanceFactoryEntry beneficiary limit epochLength start) := by
  simp [allowanceRegistry, findFactory]

/-! ## §2 — MINTING the allowance cell through the REAL factory executor.

`mintAllowanceCell` is `createCellFromFactoryChainA` over a kernel whose `factories` registry publishes
the allowance factory. The minted cell carries the factory's caveats (the frozen ceiling + the per-epoch
bound) AND its initial fields (state=open + the frozen terms + a zeroed cursor/counter) — installed by
the executor, for life. -/

/-- Mint an allowance cell from the allowance factory at key `vk` (the real factory executor). -/
def mintAllowanceCell (s : RecChainedState) (actor cell : CellId) (vk : Int) :
    Option RecChainedState :=
  createCellFromFactoryChainA s actor cell vk

/-- **`mintAllowanceCell_installs_caveats` (the factory keystone, allowance-specialized).** A minted
allowance cell carries EXACTLY the allowance factory's caveats — the four deal-term immutables (the
FROZEN ceiling) PLUS the monotone epoch cursor PLUS the `boundedBy spentThisEpoch [0, limit]` per-epoch
ceiling — installed by the executor, so `stateStepGuarded` enforces them on every later `SetField`.
Reuses `createCellFromFactoryChainA_installs_program`. -/
theorem mintAllowanceCell_installs_caveats {s s' : RecChainedState} {actor cell : CellId}
    {vk : Int} (e : FactoryEntry)
    (hreg : findFactory s.kernel.factories vk.toNat = some e)
    (h : mintAllowanceCell s actor cell vk = some s') :
    s'.kernel.slotCaveats cell = e.caveats := by
  obtain ⟨e', hfind, hcav⟩ := createCellFromFactoryChainA_installs_program h
  rw [hreg] at hfind
  rw [← (Option.some.injEq _ _).mp hfind] at hcav
  exact hcav

/-- **`mintAllowanceCell_caveats`.** When the registry IS `allowanceRegistry vk …`, the minted cell
carries the ceiling teeth + deal-term immutables (concretely). -/
theorem mintAllowanceCell_caveats {s s' : RecChainedState} {actor cell : CellId} {vk : Int}
    {beneficiary limit epochLength start : Int}
    (hreg : s.kernel.factories = allowanceRegistry vk.toNat beneficiary limit epochLength start)
    (h : mintAllowanceCell s actor cell vk = some s') :
    s'.kernel.slotCaveats cell
      = (allowanceFactoryEntry beneficiary limit epochLength start).caveats := by
  have hfind : findFactory s.kernel.factories vk.toNat
      = some (allowanceFactoryEntry beneficiary limit epochLength start) := by
    rw [hreg]; exact allowanceRegistry_finds vk.toNat beneficiary limit epochLength start
  exact mintAllowanceCell_installs_caveats _ hfind h

/-- **`mintAllowanceCell_neutral`.** Minting an allowance cell is conservation-NEUTRAL for every asset
(the cell is born EMPTY; the value is funded SEPARATELY by an ordinary move). Reuses
`createCellFromFactoryChainA_neutral`. -/
theorem mintAllowanceCell_neutral {s s' : RecChainedState} {actor cell : CellId} {vk : Int}
    (b : AssetId) (h : mintAllowanceCell s actor cell vk = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  createCellFromFactoryChainA_neutral b h

/-- **`mintAllowanceCell_grows_accounts`.** A minted allowance cell IS a live account (the mint has
teeth). -/
theorem mintAllowanceCell_grows_accounts {s s' : RecChainedState} {actor cell : CellId} {vk : Int}
    (h : mintAllowanceCell s actor cell vk = some s') :
    cell ∈ s'.kernel.accounts :=
  createCellFromFactoryChainA_grows_accounts h

/-- **`mintAllowanceCell_unknown_factory_fails` (fail-closed).** Minting against an unknown factory key
never mints. The allowance program cannot be conjured without a published factory. -/
theorem mintAllowanceCell_unknown_factory_fails (s : RecChainedState) (actor cell : CellId)
    (vk : Int) (h : findFactory s.kernel.factories vk.toNat = none) :
    mintAllowanceCell s actor cell vk = none :=
  createCellFromFactoryChainA_unknown_factory_fails s actor cell vk h

/-! ## §3 — FUND: an ordinary `move` of the spendable value INTO the minted cell's `bal` column.

The granter funds the allowance by an ordinary per-asset move (`recKExecAsset`) from its own column into
the allowance cell's column. After the fund the allowance cell HOLDS the spendable value in its `bal`
column (the single source of truth — there is NO second "amount" slot to keep relationally in sync). -/

/-- **`fundAllowance` — fund the allowance cell: move `amt` of `asset` from `granter` into `cell`'s
`bal` column.** An ordinary authorized per-asset move (`recKExecAsset`); fail-closed. -/
def fundAllowance (k : RecordKernelState) (granter cell : CellId) (asset : AssetId) (amt : ℤ) :
    Option RecordKernelState :=
  recKExecAsset k { actor := granter, src := granter, dst := cell, amt := amt } asset

/-- **`fundAllowance_conserves`.** A committed fund preserves every asset's total supply (the value
moves between two live accounts — funding the budget, not minting it). The ordinary move law. -/
theorem fundAllowance_conserves {k k' : RecordKernelState} {granter cell : CellId}
    {asset : AssetId} {amt : ℤ} (h : fundAllowance k granter cell asset amt = some k')
    (b : AssetId) : recTotalAsset k' b = recTotalAsset k b :=
  recKExecAsset_conserves_per_asset k k'
    { actor := granter, src := granter, dst := cell, amt := amt } asset h b

/-! ## §4 — SPEND on the FACTORY-BORN cell (the probe keystones, re-established here).

The allowance spend is the probe's `allowanceSpend` — it reads the committed ceiling/cursor/counter the
factory installed, advances the cursor + spent counter, and moves the spent value out, gated on the
per-epoch ceiling. We re-export it under an app-facing name and LIFT the probe's four keystones onto the
factory-born cell by observing that a factory-minted-then-funded cell is exactly the `RecordKernelState`
the probe's theorems quantify over (state slot = open, frozen terms, value in `bal`). -/

/-- App-facing spend (the probe's `allowanceSpend`): advance the epoch cursor + spent counter + move
`amount` to the beneficiary, gated on `spent_baseline + amount ≤ limit` (the ceiling) and the
derived-epoch schedule (no early/stale refill). -/
abbrev spend := @allowanceSpend

/-- **KEYSTONE (a) — `spend_conserves`.** A committed spend on the factory-born cell preserves every
asset's supply (the value is delivered from the held column, not conjured). -/
theorem spend_conserves {k k' : RecordKernelState} {e beneficiary : CellId} {asset : AssetId}
    {atBlock amount : Int}
    (h : allowanceSpend k e beneficiary asset atBlock amount = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b :=
  allowanceSpend_conserves h b

/-- **KEYSTONE (b) — `over_ceiling_rejected`.** A spend whose post-spend running total exceeds the
committed per-epoch ceiling is rejected on the factory-born cell — the budget CANNOT be over-drawn. -/
theorem over_ceiling_rejected (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId)
    (atBlock amount : Int)
    (hover : allowanceLimit k e
        < spentBaseline (allowanceEpoch k e) (allowanceSpent k e)
            (epochOf (allowanceStart k e) (allowanceEpochLength k e) atBlock) + amount) :
    allowanceSpend k e beneficiary asset atBlock amount = none :=
  Dregg2.Verify.AllowanceFactoryProbe.over_ceiling_rejected k e beneficiary asset atBlock amount hover

/-- **KEYSTONE (c, stale) — `stale_epoch_rejected`.** A backdated spend whose block lands in an epoch
EARLIER than the committed cursor (reusing a closed epoch's headroom) is rejected — no past-budget
reuse, even on an OPEN factory-born allowance. -/
theorem stale_epoch_rejected (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId)
    (atBlock amount : Int)
    (hstale : epochOf (allowanceStart k e) (allowanceEpochLength k e) atBlock < allowanceEpoch k e) :
    allowanceSpend k e beneficiary asset atBlock amount = none :=
  Dregg2.Verify.AllowanceFactoryProbe.stale_epoch_rejected k e beneficiary asset atBlock amount hstale

/-- **KEYSTONE (c, early) — `no_early_refill`.** A spend still inside the committed epoch (no genuine
boundary crossing) does NOT refill the budget: a spend over the remaining headroom is rejected — the
budget can never be reset early. -/
theorem no_early_refill (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId)
    (atBlock amount : Int)
    (hsame : epochOf (allowanceStart k e) (allowanceEpochLength k e) atBlock = allowanceEpoch k e)
    (hover : allowanceLimit k e < allowanceSpent k e + amount) :
    allowanceSpend k e beneficiary asset atBlock amount = none :=
  Dregg2.Verify.AllowanceFactoryProbe.no_early_refill k e beneficiary asset atBlock amount hsame hover

/-- **KEYSTONE (d) — `within_budget_spendable`.** An OPEN factory-born allowance whose spend fits the
remaining budget (not stale, `baseline + amount ≤ limit`), with a `SpendReady` beneficiary, SPENDS (the
within-budget value is deliverable, not trapped). -/
theorem within_budget_spendable (k : RecordKernelState) (e beneficiary : CellId) (asset : AssetId)
    (atBlock amount : Int)
    (hfresh : allowanceEpoch k e ≤ epochOf (allowanceStart k e) (allowanceEpochLength k e) atBlock)
    (hfit : spentBaseline (allowanceEpoch k e) (allowanceSpent k e)
        (epochOf (allowanceStart k e) (allowanceEpochLength k e) atBlock) + amount
      ≤ allowanceLimit k e)
    (hr : SpendReady k e beneficiary asset amount) :
    (allowanceSpend k e beneficiary asset atBlock amount).isSome :=
  Dregg2.Verify.AllowanceFactoryProbe.within_budget_spendable k e beneficiary asset atBlock amount
    hfresh hfit hr

/-! ## §4b — The SPEND-LIVENESS TOOTH (the factory-shape analog of the move's fail-closed guard).

In the factory shape the value moves by an ordinary `recKExecAsset`, whose OWN fail-closed guard requires
`dst ∈ accounts`: a spend whose beneficiary is NOT a live account is rejected, for FREE, by the move law
— the budget can never be moved into a non-account. -/

/-- **`spend_requires_live_beneficiary`.** A spend whose beneficiary is not a live account is rejected
(the move cannot deliver value into a non-account). -/
theorem spend_requires_live_beneficiary (k : RecordKernelState)
    {e beneficiary : CellId} {asset : AssetId} {atBlock amount : Int}
    (hdead : beneficiary ∉ k.accounts) :
    allowanceSpend k e beneficiary asset atBlock amount = none := by
  unfold allowanceSpend
  by_cases hg : allowanceEpoch k e ≤ epochOf (allowanceStart k e) (allowanceEpochLength k e) atBlock
      ∧ spentBaseline (allowanceEpoch k e) (allowanceSpent k e)
          (epochOf (allowanceStart k e) (allowanceEpochLength k e) atBlock) + amount
        ≤ allowanceLimit k e
  · rw [if_pos hg]
    unfold allowanceSettle recKExecAsset
    rw [if_neg]
    rintro ⟨_, _, _, _, _, htgt, _⟩
    exact hdead htgt
  · rw [if_neg hg]

/-! ## §5 — NON-VACUITY: a factory-born allowance, end to end (mint → fund → spend / over / refill).

`facWorld vk` is a kernel that PUBLISHES the allowance factory at key `vk` (beneficiary 1, limit 100,
epochLength 1000, start 10000). Cell `0` is the privileged minter (holds a node-cap to the fresh
allowance cell `3` so the mint is authorized) and the funder; cell `1` is the beneficiary (the
sub-agent). We mint cell `3` from the factory, fund 1000 into it, then witness: a within-budget spend
delivers value and advances the counter; an over-ceiling spend is rejected; a genuine epoch rollover
refills the budget. ALL on the cell the factory actually minted. -/

/-- The funder/minter holds a node-cap to the fresh allowance cell `3` (so `mintAuthorizedB` admits) and
funds the budget (cell `0` holds 2000 of asset 0). The registry publishes the allowance factory at key
7 (beneficiary 1, limit 100, epochLength 1000, start 10000). -/
def facWorld : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun c => if c = 0 then [Cap.node 3] else []
        bal := fun c a => if c = 0 then (if a = 0 then 2000 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0
        factories := allowanceRegistry 7 1 100 1000 10000 }
    log := [] }

/-- Mint the allowance cell `3` from factory key 7, then fund 1000 of asset 0 into it (funder = cell 0). -/
def facFunded : Option RecordKernelState :=
  (mintAllowanceCell facWorld 0 3 7).bind (fun s => fundAllowance s.kernel 0 3 0 1000)

-- the factory resolves + conforms:
#guard (findFactory facWorld.kernel.factories 7).isSome                                  -- some (allowance factory)
#guard ((allowanceFactoryEntry 1 100 1000 10000).conforms)                               -- true

-- the mint COMMITS and grows accounts, born conservation-neutral:
#guard ((mintAllowanceCell facWorld 0 3 7).isSome)                                       -- true (minted!)
#guard ((mintAllowanceCell facWorld 0 3 7).map (fun s => decide (3 ∈ s.kernel.accounts))) == some true
#guard ((mintAllowanceCell facWorld 0 3 7).map (fun s => recTotalAsset s.kernel 0)) == some 2005

-- the minted cell carries the allowance caveats (the last caveat is the boundedBy ceiling):
#guard ((mintAllowanceCell facWorld 0 3 7).map (fun s => s.kernel.slotCaveats 3))
        == some (allowanceFactoryEntry 1 100 1000 10000).caveats
#guard ((mintAllowanceCell facWorld 0 3 7).map (fun s => allowanceLimit s.kernel 3)) == some 100
#guard ((mintAllowanceCell facWorld 0 3 7).map (fun s => allowanceSpent s.kernel 3)) == some 0

-- after fund, the allowance cell HOLDS the spendable 1000 in its bal column (funder 2000→1000); supply fixed:
#guard (facFunded.map (fun k => k.bal 3 0)) == some 1000                                  -- spendable value in bal
#guard (facFunded.map (fun k => k.bal 0 0)) == some 1000                                  -- funder debited
#guard (facFunded.map (fun k => recTotalAsset k 0)) == some 2005                          -- conserved

-- a WITHIN-BUDGET spend (40 of the 100 ceiling, at block 10500 = epoch 0) delivers 40 to beneficiary 1
-- (5→45), advances the spent counter, and conserves supply:
#guard (facFunded.bind (fun k => allowanceSpend k 3 1 0 10500 40) |>.map (fun s => s.bal 1 0)) == some 45
#guard (facFunded.bind (fun k => allowanceSpend k 3 1 0 10500 40) |>.map (fun s => s.bal 3 0)) == some 960
#guard (facFunded.bind (fun k => allowanceSpend k 3 1 0 10500 40) |>.map (fun s => allowanceSpent s 3)) == some 40
#guard (facFunded.bind (fun k => allowanceSpend k 3 1 0 10500 40) |>.map (fun s => recTotalAsset s 0)) == some 2005

-- a spend AT EXACTLY the ceiling (100, nothing yet spent) is LIVE (the ≤ boundary; non-vacuity):
#guard (facFunded.bind (fun k => allowanceSpend k 3 1 0 10500 100) |>.isSome)             -- true
-- ...ONE over the ceiling (101) is REJECTED (KEYSTONE b — no over-limit):
#guard (facFunded.bind (fun k => allowanceSpend k 3 1 0 10500 101) |>.isSome) == false

-- EPOCH ROLLOVER: spend 100 in epoch 0, then a fresh 100 in epoch 1 (block 11000) — both commit, the
-- counter resets at the genuine boundary (the budget refilled), and supply is conserved throughout:
#guard (facFunded.bind (fun k => allowanceSpend k 3 1 0 10500 100)
          |>.bind (fun k => allowanceSpend k 3 1 0 11000 100) |>.map (fun s => allowanceEpoch s 3)) == some 1
#guard (facFunded.bind (fun k => allowanceSpend k 3 1 0 10500 100)
          |>.bind (fun k => allowanceSpend k 3 1 0 11000 100) |>.map (fun s => allowanceSpent s 3)) == some 100
#guard (facFunded.bind (fun k => allowanceSpend k 3 1 0 10500 100)
          |>.bind (fun k => allowanceSpend k 3 1 0 11000 100) |>.map (fun s => s.bal 1 0)) == some 205
-- ...but a SECOND 100 STILL in epoch 0 (after the first 100) is rejected — no early refill (KEYSTONE c):
#guard (facFunded.bind (fun k => allowanceSpend k 3 1 0 10500 100)
          |>.bind (fun k => allowanceSpend k 3 1 0 10600 100) |>.isSome) == false

-- an UNKNOWN factory key never mints (fail-closed):
#guard ((mintAllowanceCell facWorld 0 3 99).isSome) == false

/-! ## §VERDICT — the allowance is a LIVE factory-settled cell.

An agent CREATES an allowance (mints the factory cell with the frozen per-epoch ceiling + epoch terms,
funds it), and a sub-agent SPENDS up to the ceiling per epoch — the ceiling enforced so it can be neither
EXCEEDED (over-limit rejected) nor FORGED (the terms are frozen immutables) nor REFILLED EARLY (the epoch
is derived from the block) — all via the EXISTING wired `CreateCellFromFactory` + `Transfer` + `SetField`
turns, NO new `Effect`. The four allowance-safety keystones (conservation / ceiling-no-over-limit /
no-forged-or-early-refill / within-budget-spendable) hold on the FACTORY-BORN cell. The bespoke heap-cell
`cell/src/allowance.rs` library is superseded by this factory route, the same dissolution the vault and
escrow families made.

RESIDUALS (honest, the SAME the whole settlement family carries): the SDK-builder constructing the only
sensible spend turn (binding `beneficiary` as the move target) is the off-program binding the settlement
family's payout target is; eventual-settlement liveness is consensus-layer. None is allowance-specific.
-/

#assert_axioms allowanceFactoryEntry_conforms
#assert_axioms allowanceRegistry_finds
#assert_axioms mintAllowanceCell_installs_caveats
#assert_axioms mintAllowanceCell_caveats
#assert_axioms mintAllowanceCell_neutral
#assert_axioms mintAllowanceCell_grows_accounts
#assert_axioms mintAllowanceCell_unknown_factory_fails
#assert_axioms fundAllowance_conserves
#assert_axioms spend_conserves
#assert_axioms over_ceiling_rejected
#assert_axioms stale_epoch_rejected
#assert_axioms no_early_refill
#assert_axioms within_budget_spendable
#assert_axioms spend_requires_live_beneficiary

end Dregg2.Apps.Allowance
