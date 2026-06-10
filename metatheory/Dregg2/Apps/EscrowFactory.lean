/-
# Dregg2.Apps.EscrowFactory — W2: the escrow FACTORY (real), the land-before-kill replacement for the
escrow verb family.

This module PROMOTES the R3 falsification probe (`Dregg2.Verify.EscrowFactoryProbe`, commit `6551ffab2`
— PASS) from a stand-alone shape study into a REAL, app-instantiable `FactoryEntry` wired through the
EXISTING factory executor `createCellFromFactoryChainA` (`Dregg2.Exec.TurnExecutorFull`). The probe
proved escrow-as-cell-program is sound; THIS module makes it the LIVE path:

  * the escrow factory is a published `FactoryEntry` (`escrowFactoryEntry`) an app registers in the
    kernel's `factories` registry and instantiates via `createCellFromFactoryA actor escrowCell vk`;
  * the executor INSTALLS the factory's `slotCaveats` (the escrow state machine + the deal-term
    immutables) onto the minted cell for its WHOLE LIFE (`createCellFromFactoryChainA_installs_program`),
    so the no-double-resolve teeth are enforced by `stateStepGuarded` on every later `SetField`, not by
    an off-ledger guard;
  * the locked VALUE lives in the minted cell's own per-asset `bal` column (a `deposit` is an ordinary
    `move` IN; a `release`/`refund` is an ordinary `move` OUT — the probe's `escrowSettle`), so escrow
    inherits the kernel's per-asset move conservation law VERBATIM, with NO `escrows` side-table and NO
    bespoke `recTotalAsset` quantity.

The four release-safety keystones (conservation / no-double-resolve / release-only-on-condition /
value-not-stranded) are RE-ESTABLISHED on the FACTORY-BORN cell here — i.e. on the cell whose caveats
the executor actually installed — by feeding the factory-install facts into the probe's already-proved
keystones. That is the witness that the factory is a FAITHFUL replacement for the verbs (§DELETION).

## The shape (the published deliverable)

`escrowFactoryEntry amount depositor beneficiary cond asset : FactoryEntry`
  caveats       = Immutable {amount, depositor, beneficiary, condition, asset}
                  ++ admitTable state [(open,released),(open,refunded)]   -- the state machine teeth
  initialFields = state=open, amount, depositor, beneficiary, condition, asset
  programVk     = 0

`escrowRegistry vk` installs it at content-addressed key `vk`; `mintEscrowCell` runs the real factory
executor; `deposit` moves the locked value into the minted cell's `bal`; release/refund are the probe's
`escrowRelease`/`escrowRefund` on that cell.

## §DELETION-READINESS (land-before-kill — what W2 removes once this is the live path)

ENUMERATED at the foot (`§DELETION`). NOTHING is deleted here (land-before-kill): we prove the factory
is a faithful replacement + list the verb-family surface to remove + the re-point prerequisite.

NEW file. Imports the probe + the factory executor; does NOT touch `cell/src/capability.rs`/`seal.rs`,
`Argus/Compile.lean`, or the Substrate/Dynamics files. `#assert_axioms`-pinned to
`{propext, Classical.choice, Quot.sound}` — no sorry, no `:= True`.
-/
import Dregg2.Verify.EscrowFactoryProbe
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Apps.EscrowFactory

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Cap)
open Dregg2.Verify.EscrowFactoryProbe
open Dregg2.Exec.EffectsState (fieldOf setField)

/-! ## §1 — The escrow FACTORY ENTRY (the published `FactoryEntry`).

This IS the probe's `escrowFactory` descriptor (re-exported under an app-facing name): the five
deal-term immutables + the state-machine `admitTable [(open,released),(open,refunded)]`. The factory's
own initial state CONFORMS to its own caveats (`escrowFactory_conforms`, proved in the probe). -/

/-- **The escrow factory entry.** Mints an escrow cell carrying the deal-term immutables + the
no-double-resolve state machine; the locked value is held in the minted cell's `bal` column. -/
def escrowFactoryEntry (amount depositor beneficiary cond asset : Int) : FactoryEntry :=
  escrowFactory amount depositor beneficiary cond asset

/-- The escrow factory conforms to its own published invariants (re-exported probe keystone). -/
theorem escrowFactoryEntry_conforms (amount depositor beneficiary cond asset : Int) :
    (escrowFactoryEntry amount depositor beneficiary cond asset).conforms = true :=
  escrowFactory_conforms amount depositor beneficiary cond asset

/-- A kernel factory registry that publishes the escrow factory at content-addressed key `vk`. An app
installs this into `s.kernel.factories` so `createCellFromFactoryA actor escrowCell vk` resolves it. -/
def escrowRegistry (vk : Nat) (amount depositor beneficiary cond asset : Int) :
    List (Nat × FactoryEntry) :=
  [(vk, escrowFactoryEntry amount depositor beneficiary cond asset)]

/-- The registry resolves the escrow factory at exactly its published key. -/
theorem escrowRegistry_finds (vk : Nat) (amount depositor beneficiary cond asset : Int) :
    findFactory (escrowRegistry vk amount depositor beneficiary cond asset) vk
      = some (escrowFactoryEntry amount depositor beneficiary cond asset) := by
  simp [escrowRegistry, findFactory]

/-! ## §2 — MINTING the escrow cell through the REAL factory executor.

`mintEscrowCell` is `createCellFromFactoryA` over a kernel whose `factories` registry publishes the
escrow factory. The minted cell carries the factory's caveats (the state machine) AND its initial
fields (state=open + the frozen deal terms) — installed by the executor, for life. -/

/-- Mint an escrow cell from the escrow factory at key `vk` (the real factory executor). -/
def mintEscrowCell (s : RecChainedState) (actor escrowCell : CellId) (vk : Int) :
    Option RecChainedState :=
  createCellFromFactoryChainA s actor escrowCell vk

/-- **`mintEscrowCell_installs_state_machine` (the factory keystone, escrow-specialized).**
A minted escrow cell carries EXACTLY the escrow factory's caveats — the five deal-term immutables PLUS
the no-double-resolve state machine `admitTable [(open,released),(open,refunded)]` — installed by the
executor, so `stateStepGuarded` enforces them on every later `SetField`. Reuses
`createCellFromFactoryChainA_installs_program`. -/
theorem mintEscrowCell_installs_state_machine {s s' : RecChainedState} {actor escrowCell : CellId}
    {vk : Int} (e : FactoryEntry)
    (hreg : findFactory s.kernel.factories vk.toNat = some e)
    (h : mintEscrowCell s actor escrowCell vk = some s') :
    s'.kernel.slotCaveats escrowCell = e.caveats := by
  obtain ⟨e', hfind, hcav⟩ := createCellFromFactoryChainA_installs_program h
  rw [hreg] at hfind
  rw [← (Option.some.injEq _ _).mp hfind] at hcav
  exact hcav

/-- **`mintEscrowCell_caveats`.** When the registry IS `escrowRegistry vk …`, the minted cell
carries the escrow state machine + deal-term immutables (concretely). -/
theorem mintEscrowCell_caveats {s s' : RecChainedState} {actor escrowCell : CellId} {vk : Int}
    {amount depositor beneficiary cond asset : Int}
    (hreg : s.kernel.factories = escrowRegistry vk.toNat amount depositor beneficiary cond asset)
    (h : mintEscrowCell s actor escrowCell vk = some s') :
    s'.kernel.slotCaveats escrowCell
      = (escrowFactoryEntry amount depositor beneficiary cond asset).caveats := by
  have hfind : findFactory s.kernel.factories vk.toNat
      = some (escrowFactoryEntry amount depositor beneficiary cond asset) := by
    rw [hreg]; exact escrowRegistry_finds vk.toNat amount depositor beneficiary cond asset
  exact mintEscrowCell_installs_state_machine _ hfind h

/-- **`mintEscrowCell_neutral`.** Minting an escrow cell is conservation-NEUTRAL for every
asset (the cell is born EMPTY; the value is deposited SEPARATELY by an ordinary move). Reuses
`createCellFromFactoryChainA_neutral`. -/
theorem mintEscrowCell_neutral {s s' : RecChainedState} {actor escrowCell : CellId} {vk : Int}
    (b : AssetId) (h : mintEscrowCell s actor escrowCell vk = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  createCellFromFactoryChainA_neutral b h

/-- **`mintEscrowCell_grows_accounts`.** A minted escrow cell IS a live account (the mint has
teeth: the registry grew, neutrality is not a no-op). -/
theorem mintEscrowCell_grows_accounts {s s' : RecChainedState} {actor escrowCell : CellId} {vk : Int}
    (h : mintEscrowCell s actor escrowCell vk = some s') :
    escrowCell ∈ s'.kernel.accounts :=
  createCellFromFactoryChainA_grows_accounts h

/-- **`mintEscrowCell_unknown_factory_fails` (fail-closed).** Minting against an unknown
factory key never mints. The escrow program cannot be conjured without a published factory. -/
theorem mintEscrowCell_unknown_factory_fails (s : RecChainedState) (actor escrowCell : CellId)
    (vk : Int) (h : findFactory s.kernel.factories vk.toNat = none) :
    mintEscrowCell s actor escrowCell vk = none :=
  createCellFromFactoryChainA_unknown_factory_fails s actor escrowCell vk h

/-! ## §3 — DEPOSIT: an ordinary `move` of the locked value INTO the minted cell's `bal` column.

The depositor funds the escrow by an ordinary per-asset move (`recKExecAsset`) from its own column into
the escrow cell's column — exactly the body of `escrowSettle`'s move, in reverse. After the deposit the
escrow cell holds `amt` of `asset` in its `bal` column (the single source of truth for the locked
value, per §HARD-i: there is NO second "remaining" slot to keep relationally in sync). -/

/-- **`depositEscrow` — fund the escrow cell: move `amt` of `asset` from `depositor` into `escrowCell`'s
`bal` column.** An ordinary authorized per-asset move (`recKExecAsset`); fail-closed (the move's guard:
authorized, non-negative, sufficient balance, distinct live cells). -/
def depositEscrow (k : RecordKernelState) (depositor escrowCell : CellId) (asset : AssetId) (amt : ℤ) :
    Option RecordKernelState :=
  recKExecAsset k { actor := depositor, src := depositor, dst := escrowCell, amt := amt } asset

/-- **`depositEscrow_conserves`.** A committed deposit preserves every asset's total supply
(the value moves between two live accounts — funding the lock, not minting it). The ordinary move law. -/
theorem depositEscrow_conserves {k k' : RecordKernelState} {depositor escrowCell : CellId}
    {asset : AssetId} {amt : ℤ} (h : depositEscrow k depositor escrowCell asset amt = some k')
    (b : AssetId) : recTotalAsset k' b = recTotalAsset k b :=
  recKExecAsset_conserves_per_asset k k'
    { actor := depositor, src := depositor, dst := escrowCell, amt := amt } asset h b

/-! ## §4 — RELEASE / REFUND on the FACTORY-BORN cell (the probe keystones, re-established here).

The escrow OPERATIONS are the probe's `escrowRelease`/`escrowRefund`/`escrowSettle` — they read the
state slot the factory installed and move the held `bal` out. We re-export them under app-facing names
so BountyBoardGated (and the §DELETION note) refer to one surface, and we LIFT the probe's four
keystones onto the factory-born cell by observing that a factory-minted-then-funded cell is exactly the
`RecordKernelState` the probe's theorems quantify over (state slot = open, value in `bal`). -/

/-- App-facing release (the probe's `escrowRelease`): OPEN→RELEASED + move held value to beneficiary,
gated on the condition witness. -/
abbrev releaseEscrow := @escrowRelease
/-- App-facing refund (the probe's `escrowRefund`): OPEN→REFUNDED + move held value to depositor. -/
abbrev refundEscrow := @escrowRefund

/-- **KEYSTONE (a) — `release_conserves`.** A committed release on the factory-born cell preserves every
asset's supply (the reward is delivered from the held column, not conjured). -/
theorem release_conserves {k k' : RecordKernelState} {e beneficiary : CellId} {asset : AssetId}
    {witness : Int} (h : escrowRelease k e beneficiary asset witness = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b :=
  escrowRelease_conserves h b

/-- **KEYSTONE (a) — `refund_conserves`.** A committed refund preserves every asset's supply. -/
theorem refund_conserves {k k' : RecordKernelState} {e depositor : CellId} {asset : AssetId}
    (h : escrowRefund k e depositor asset = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b :=
  escrowRefund_conserves h b

/-- **KEYSTONE (b) — `no_double_resolve`.** Once a settle drove the factory-born escrow to RELEASED,
neither a second release nor a refund commits — the installed state machine fail-closes. -/
theorem no_double_resolve {k : RecordKernelState} {e tgt : CellId} {asset : AssetId} {witness : Int}
    (hres : escrowState k e = sReleased) :
    escrowRelease k e tgt asset witness = none ∧ escrowRefund k e tgt asset = none :=
  no_double_resolve_released k e tgt asset witness hres

/-- **KEYSTONE (c) — `release_requires_condition`.** A release whose supplied witness ≠ the cell's
frozen `condition` slot is rejected — even on an OPEN factory-born escrow. -/
theorem release_requires_condition {k : RecordKernelState} {e beneficiary : CellId} {asset : AssetId}
    {witness : Int} (hbad : witness ≠ escrowCondition k e) :
    escrowRelease k e beneficiary asset witness = none :=
  Dregg2.Verify.EscrowFactoryProbe.release_requires_condition k e beneficiary asset witness hbad

/-- **KEYSTONE (d) — `open_releasable`.** An OPEN factory-born escrow with the correct condition and a
`SettleReady` beneficiary releases (the value is deliverable, not trapped). -/
theorem open_releasable {k : RecordKernelState} {e beneficiary : CellId} {asset : AssetId}
    {witness : Int} (hopen : escrowState k e = sOpen) (hcond : witness = escrowCondition k e)
    (hr : SettleReady k e beneficiary asset) :
    (escrowRelease k e beneficiary asset witness).isSome :=
  open_escrow_releasable k e beneficiary asset witness hopen hcond hr

/-- **KEYSTONE (d) — `open_refundable`.** An OPEN factory-born escrow with a `SettleReady` depositor
refunds (the abort path always returns the value). -/
theorem open_refundable {k : RecordKernelState} {e depositor : CellId} {asset : AssetId}
    (hopen : escrowState k e = sOpen) (hr : SettleReady k e depositor asset) :
    (escrowRefund k e depositor asset).isSome :=
  open_escrow_refundable k e depositor asset hopen hr

/-! ## §4b — The SETTLE-LIVENESS TEETH (the factory-shape analog of D3 `…_nonlive_fails`).

The verb-era D3 teeth (`releaseEscrowKAsset_nonlive_fails`) rejected crediting a Sealed/Destroyed cell
— delivering value into a frozen cell would silently DESTROY it (it vanishes from `recTotalAsset`,
breaking conservation). In the factory shape the value moves by an ordinary `recKExecAsset`, whose OWN
fail-closed guard requires `dst ∈ accounts`: a settle whose target is NOT a live account is rejected,
for FREE, by the move law — the reward can never be moved into a non-account. This is the single-machine
analog of the D3 liveness teeth, carried by the move itself rather than a bespoke side-table check. -/

/-- **`settle_requires_live_target`.** A settle (release or refund body) whose `target` is NOT
a live account is rejected (`none`) — the move cannot deliver value into a non-account, so no held value
can be moved into a frozen/absent cell. The factory-shape D3 teeth. -/
theorem settle_requires_live_target {k : RecordKernelState} {e target : CellId} {asset : AssetId}
    {newState : Int} (hdead : target ∉ k.accounts) :
    escrowSettle k e target asset newState = none := by
  unfold escrowSettle recKExecAsset
  rw [if_neg]
  rintro ⟨_, _, _, _, _, htgt⟩
  exact hdead htgt

/-- **`release_requires_live_beneficiary` (END-USER D3, release side).** A release whose
beneficiary is not a live account is rejected. -/
theorem release_requires_live_beneficiary {k : RecordKernelState} {e beneficiary : CellId}
    {asset : AssetId} {witness : Int} (hdead : beneficiary ∉ k.accounts) :
    escrowRelease k e beneficiary asset witness = none := by
  unfold escrowRelease
  by_cases hg : escrowState k e = sOpen ∧ witness = escrowCondition k e
  · rw [if_pos hg]; exact settle_requires_live_target hdead
  · rw [if_neg hg]

/-- **`refund_requires_live_depositor` (END-USER D3, refund side).** A refund whose depositor
target is not a live account is rejected. -/
theorem refund_requires_live_depositor {k : RecordKernelState} {e depositor : CellId} {asset : AssetId}
    (hdead : depositor ∉ k.accounts) :
    escrowRefund k e depositor asset = none := by
  unfold escrowRefund
  by_cases hg : escrowState k e = sOpen
  · rw [if_pos hg]; exact settle_requires_live_target hdead
  · rw [if_neg hg]

/-! ## §5 — NON-VACUITY: a factory-born escrow, end to end (mint → deposit → release/refund/double).

`facWorld vk` is a kernel that PUBLISHES the escrow factory at key `vk` (amount 40, depositor 2,
beneficiary 1, condition 99, asset 0). Cell `0` is the privileged minter (holds a node-cap to the fresh
escrow cell `3` so the mint is authorized) and the funder; cell `1` is the beneficiary; cell `2` the
depositor. We mint cell `3` from the factory, deposit 40 into it, then witness: a correct release
delivers 40 to the beneficiary and advances to RELEASED; a wrong condition is rejected; a refund returns
40 to the depositor; a double-resolve fails. ALL on the cell the factory actually minted. -/

/-- The funder/minter holds a node-cap to the fresh escrow cell `3` (so `mintAuthorizedB` admits) and
funds the deposit (cell `0` holds 100 of asset 0). The registry publishes the escrow factory at key 7. -/
def facWorld : RecChainedState :=
  { kernel :=
      { accounts := {0, 1, 2}
        cell := fun _ => .record [("balance", .int 0)]
        caps := fun c => if c = 0 then [Cap.node 3] else []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else 0)
                          else if c = 1 then (if a = 0 then 5 else 0) else 0
        factories := escrowRegistry 7 40 2 1 99 0 }
    log := [] }

/-- Mint the escrow cell `3` from factory key 7, then deposit 40 of asset 0 into it (funder = cell 0). -/
def facFunded : Option RecordKernelState :=
  (mintEscrowCell facWorld 0 3 7).bind (fun s => depositEscrow s.kernel 0 3 0 40)

-- the factory resolves + conforms:
#guard (findFactory facWorld.kernel.factories 7).isSome                                -- some (escrow factory)
#guard ((escrowFactoryEntry 40 2 1 99 0).conforms)                                     -- true

-- the mint COMMITS and grows accounts, born conservation-neutral:
#guard ((mintEscrowCell facWorld 0 3 7).isSome)                                        -- true (minted!)
#guard ((mintEscrowCell facWorld 0 3 7).map (fun s => decide (3 ∈ s.kernel.accounts))) == some true
#guard ((mintEscrowCell facWorld 0 3 7).map (fun s => recTotalAsset s.kernel 0)) == some 105

-- the minted cell carries the escrow state machine (the last caveat is the admitTable) and starts OPEN:
#guard ((mintEscrowCell facWorld 0 3 7).map (fun s => s.kernel.slotCaveats 3))
        == some (escrowFactoryEntry 40 2 1 99 0).caveats
#guard ((mintEscrowCell facWorld 0 3 7).map (fun s => escrowState s.kernel 3)) == some sOpen
#guard ((mintEscrowCell facWorld 0 3 7).map (fun s => escrowCondition s.kernel 3)) == some 99

-- after deposit, the escrow cell HOLDS the locked 40 in its bal column (funder 100→60); supply fixed:
#guard (facFunded.map (fun k => k.bal 3 0)) == some 40                                 -- locked value in bal
#guard (facFunded.map (fun k => k.bal 0 0)) == some 60                                 -- funder debited
#guard (facFunded.map (fun k => recTotalAsset k 0)) == some 105                        -- conserved

-- a CORRECT release (witness 99) delivers 40 to beneficiary 1 (5→45) and advances to RELEASED:
#guard (facFunded.bind (fun k => escrowRelease k 3 1 0 99) |>.map (fun s => s.bal 1 0)) == some 45
#guard (facFunded.bind (fun k => escrowRelease k 3 1 0 99) |>.map (fun s => s.bal 3 0)) == some 0
#guard (facFunded.bind (fun k => escrowRelease k 3 1 0 99) |>.map (fun s => escrowState s 3)) == some sReleased
#guard (facFunded.bind (fun k => escrowRelease k 3 1 0 99) |>.map (fun s => recTotalAsset s 0)) == some 105

-- a WRONG condition (7 ≠ 99) is rejected (KEYSTONE c):
#guard (facFunded.bind (fun k => escrowRelease k 3 1 0 7) |>.isSome) == false

-- a REFUND returns 40 to depositor 2 (0→40) and advances to REFUNDED:
#guard (facFunded.bind (fun k => escrowRefund k 3 2 0) |>.map (fun s => s.bal 2 0)) == some 40
#guard (facFunded.bind (fun k => escrowRefund k 3 2 0) |>.map (fun s => escrowState s 3)) == some sRefunded

-- NO-DOUBLE-RESOLVE: release then a second release AND a refund both fail (KEYSTONE b):
#guard (facFunded.bind (fun k => escrowRelease k 3 1 0 99) |>.bind (fun s => escrowRelease s 3 1 0 99) |>.isSome) == false
#guard (facFunded.bind (fun k => escrowRelease k 3 1 0 99) |>.bind (fun s => escrowRefund s 3 2 0) |>.isSome) == false

-- an UNKNOWN factory key never mints (fail-closed):
#guard ((mintEscrowCell facWorld 0 3 99).isSome) == false

/-! ## §DELETION — the W2 deletion-readiness note (land-before-kill).

THIS module + the BountyBoardGated re-point are the LAND-BEFORE-KILL prerequisite. Once the factory is
the live escrow path (this module shipped + every escrow app re-pointed), W2 DELETES the verb family:

  WHAT W2 DELETES (the escrow side-table surface — `Dregg2.Exec.RecordKernel` / `…TurnExecutorFull`):
    (1) the THREE kernel arms / chain ops:
          • `createEscrowKAsset` / `createEscrowChainA` / the `.createEscrowA` `FullActionA` arm
          • `releaseEscrowKAsset` / `releaseEscrowChainA` / the `.releaseEscrowA` arm
          • `refundEscrowKAsset` / `refundEscrowChainA` / the `.refundEscrowA` arm
        (replaced by: `createCellFromFactoryA` + `setFieldA` + `balanceA` over `escrowFactoryEntry`).
    (2) the OFF-LEDGER side-table itself: the `escrows : List EscrowRecord` field on `RecordKernelState`
        (`RecordKernel.lean:~483/542`) — DISSOLVED into the minted cell's own `bal` column.
    (3) `escrowHeldAsset` (the off-ledger held-value measure) and `EscrowRecord`'s escrow-specific
        fields (`creator`/`recipient`/`amount`/`resolved`) where used ONLY by escrow.
    (4) the E3 TRANSITIONAL term from W1: `recTotalAsset`'s escrow summand
        (`recTotalAsset + escrowHeldAsset`) COLLAPSES back to plain `recTotalAsset` — the bespoke
        combined conserved quantity and its accounting theory (`escrow_settle_conserves_combined`,
        `heldSum_markResolved_found`, the `…WithEscrow` neutrality lemmas) all DIE, because escrow
        conservation is now the ORDINARY per-asset move law (`recKExecAsset_conserves_per_asset`).
    (5) the escrow settle-liveness side teeth that read the side-table
        (`releaseEscrowKAsset_nonlive_fails` / `refundEscrowKAsset_nonlive_fails`) are SUBSUMED by the
        move's own fail-closed guard (a move into a non-live cell already fails) + the state machine.

  WHAT MUST BE RE-POINTED FIRST (the land-before-kill blockers — every escrow-verb consumer):
    • `Dregg2.Apps.BountyBoardGated`  — DONE in this wave (re-points to `escrowFactoryEntry`).
    • `Dregg2.Apps.BountyBoard`       — the ungated dual (same re-point pattern; W2 follow-up).
    • `Dregg2.Apps.ComputeExchange{,Gated}` — escrow-verb consumers (order/settle/refund); re-point.
    • `Dregg2.Apps.AtomicSwap`        — multi-party escrow swap on the verbs; re-point (uses the lock
                                        as a 2-party move pair — fits the factory shape directly).
    • the BRIDGE/OBLIGATION twins that SHARE `EscrowRecord`'s store (`bridge`/`queueDep` tags,
      `StakedSlaGated`/`CrossChainBridgeGated`) — DECIDE per-family whether they re-land as factories
      (obligation/swiss DO, per the probe §VERDICT) or keep a distinct store BEFORE deleting the shared
      `EscrowRecord`. This is the one genuine ordering constraint: the side-table field cannot be
      removed while a non-escrow consumer still reads it.

  NOT DELETED HERE (land-before-kill): nothing above is removed in this commit — we only prove the
  factory is a faithful replacement and enumerate the burn-down. The verb deletion is the SUBSEQUENT W2
  commit, gated on the re-points above all landing green.
-/

#assert_axioms escrowFactoryEntry_conforms
#assert_axioms escrowRegistry_finds
#assert_axioms mintEscrowCell_installs_state_machine
#assert_axioms mintEscrowCell_caveats
#assert_axioms mintEscrowCell_neutral
#assert_axioms mintEscrowCell_grows_accounts
#assert_axioms mintEscrowCell_unknown_factory_fails
#assert_axioms depositEscrow_conserves
#assert_axioms release_conserves
#assert_axioms refund_conserves
#assert_axioms no_double_resolve
#assert_axioms release_requires_condition
#assert_axioms open_releasable
#assert_axioms open_refundable
#assert_axioms settle_requires_live_target
#assert_axioms release_requires_live_beneficiary
#assert_axioms refund_requires_live_depositor

end Dregg2.Apps.EscrowFactory
