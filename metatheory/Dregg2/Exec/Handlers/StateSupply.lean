/-
# Dregg2.Exec.Handlers.StateSupply — the STATE + SUPPLY handler batch.

The SECOND batch of `EffectHandler` instances (after the `transfer`/`escrow`/`state` slice in
`Dregg2/Exec/Handler.lean`). This file EXTENDS the algebra: every handler reuses an effect's EXISTING
kernel step + its already-proved conservation/authority lemma from `TurnExecutorFull`/`RecordKernel`,
WRAPPED — where the bare kernel op lacks one — in the lifecycle admission gate (`acceptsEffects`) that
the obligation `admission_gated` then forces. We do NOT touch `execFullA`/`FullActionA` (the cutover is
a later step); we only IMPORT and REUSE.

Two faces:

  * **SUPPLY (the `delta ≠ 0` milestone).** `mintA`/`burnA`/`bridgeMintA` are the ONLY ops that
    legitimately move the conserved per-asset measure — and they exercise the path the algebra's global
    `turn_conserves` was built for: it SUMS NON-ZERO per-effect deltas. `mintH.delta a b = if b = a.asset
    then a.amt else 0` (a per-asset inflow), discharged by COMPOSING the proved `recKMintAsset_delta`
    (over the bare `bal` ledger) with a holding-store-fixed bridge (`mintStep_escrowHeld_fixed`) to the
    COMBINED measure `recTotalAssetWithEscrow`. `burnH` is the `-amt` dual (`recKBurnAsset_delta`).
    `bridgeMintH` ALIASES the mint kernel step (`recKMintAsset` — `bridgeMint` reuses the per-asset mint,
    `TurnExecutorFull:4610`), `delta = +value`. `createCellH`/`createCellFromFactoryH`/`spawnH` are
    ACCOUNT-GROWTH: a fresh cell born EMPTY, so the COMBINED measure is unchanged (`delta = 0`) even
    though `accounts` genuinely GREW (`recTotalAsset_insert_fresh` — non-vacuous neutrality).

  * **STATE/WRITE (closing R1's lifecycle-admission hole + R6).** dregg1's `SetField`/`IncrementNonce`/
    `SetPermissions`/`SetVerificationKey`/`MakeSovereign`/`Refusal`/`ReceiptArchive` are all
    balance-NEUTRAL named-field writes. The bare `EffectsState.stateStep` gates only on authority +
    `target ∈ accounts` — it does NOT consult the cell's lifecycle, so a write into a SEALED/Destroyed
    cell is silently admitted (the R6 hole: the write bypasses `cellSeal`). Each handler here ROUTES the
    field write through the live-cell admission gate (`acceptsEffects`) the bare step lacks — that WRAP
    is the hole-fix, and `admission_gated` makes it a TYPING obligation. `delta = 0` (the write touches
    `cell` only — never `bal`/`escrows`), so `conserves` is the trivial frame.

EVAL-VERIFIED (the gate's teeth — `§TEETH`): a mint/write into a SEALED cell returns `none`; into a
LIVE cell returns `some`; and a mint into a Live cell RAISES the combined per-asset measure by exactly
`+amt` (the `delta ≠ 0` milestone, evaluated).

Pure, computable, `#eval`-able. Verified standalone:
`lake build Dregg2.Exec.Handlers.StateSupply`.
-/
import Dregg2.Exec.Handler

namespace Dregg2.Exec.Handlers.StateSupply

open Dregg2.Authority Dregg2.Execution
open Dregg2.Exec
open Dregg2.Exec.Handler
open Dregg2.Exec.TurnExecutorFull
  (acceptsEffects lcLive lcSealed lcDestroyed setLifecycle
   recKMintAsset recKBurnAsset recKMintAsset_delta recKBurnAsset_delta
   recKMintAsset_authorized recKBurnAsset_authorized createCellChainA)
open Dregg2.Exec.EffectsState (writeField setField fieldOf)
open scoped BigOperators

/-! ## §1 — SUPPLY: the `delta ≠ 0` path. mint / burn / bridge-mint over the per-asset `bal` ledger.

`recKMintAsset` / `recKBurnAsset` are the PROVED privileged per-asset supply ops: they edit ONLY `bal`
(leaving `cell`/`escrows`/`lifecycle` fixed) under the `mintAuthorizedB` gate (a `node`/`control` cap —
a cell cannot coin its own supply). Their `*_delta` lemmas state the BARE-LEDGER move
(`recTotalAsset k' b = recTotalAsset k b + (if b = a then ±amt else 0)`). We bridge to the COMBINED
measure `recTotalAssetWithEscrow` exactly as the `transferH` slice did: a `bal`-only edit leaves the
holding-store fixed, so the combined measure follows the bare-ledger move. We WRAP each step in
`acceptsEffects` on the minted/burned cell — a supply move into a non-Live cell is REJECTED. -/

/-- Per-asset supply (mint/burn) arguments: the actor (authority subject), the target `cell`, the
moved `asset`, and the (non-negative) `amt`. -/
structure SupplyArgs where
  /-- The actor invoking the privileged supply op (must hold a `node`/`control` cap on `cell`). -/
  actor : CellId
  /-- The cell whose `asset` column is credited (mint) or debited (burn). -/
  cell : CellId
  /-- The asset column moved. -/
  asset : AssetId
  /-- The (non-negative) amount minted/burned. -/
  amt : Int

/-! ### §1.1 — `mintH`: the per-asset mint, gated on cell liveness. `delta = +amt` at the asset. -/

/-- **The R-closing wrapped mint step.** Credit `cell`'s `asset` column by `amt` ONLY if `cell` is Live
(`acceptsEffects`), then run the proved `recKMintAsset`. A mint into a non-Live cell is `none`. -/
def mintStep (k : RecordKernelState) (a : SupplyArgs) : Option RecordKernelState :=
  if acceptsEffects k a.cell then recKMintAsset k a.actor a.cell a.asset a.amt else none

/-- `recKMintAsset` keeps `escrows` (and every non-`bal` field) fixed, so its post-state's holding-store
is literally unchanged — the combined measure follows the bare-ledger measure. -/
theorem mintStep_escrowHeld_fixed (k k' : RecordKernelState) (a : SupplyArgs)
    (h : mintStep k a = some k') (b : AssetId) :
    escrowHeldAsset k' b = escrowHeldAsset k b := by
  unfold mintStep at h
  by_cases hadm : acceptsEffects k a.cell
  · rw [if_pos hadm] at h
    unfold recKMintAsset at h
    by_cases hg : mintAuthorizedB k.caps a.actor a.cell = true ∧ 0 ≤ a.amt ∧ a.cell ∈ k.accounts
    · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h; rfl
    · rw [if_neg hg] at h; exact absurd h (by simp)
  · rw [if_neg hadm] at h; exact absurd h (by simp)

/-- **`mintH` — the registered per-asset MINT handler (`delta ≠ 0`).** `conserves` composes the proved
`recKMintAsset_delta` (bare ledger) with `mintStep_escrowHeld_fixed` (holding-store fixed) to the COMBINED
measure: the combined measure rises by `+amt` AT the minted asset, by `0` elsewhere. `auth_gated` from
`recKMintAsset_authorized` (the privileged `mintAuthorizedB` gate). `admission_gated` from the
Live-cell wrapper. This is the supply face the global `turn_conserves` SUMS. -/
def mintH : EffectHandler SupplyArgs where
  step := mintStep
  delta := fun a b => if b = a.asset then a.amt else 0
  auth := fun k a => mintAuthorizedB k.caps a.actor a.cell
  admission := fun k a => acceptsEffects k a.cell
  trace := fun a => { actor := a.actor, src := a.cell, dst := a.cell, amt := a.amt }
  auth_gated := by
    intro s a s' h
    unfold mintStep at h
    by_cases hadm : acceptsEffects s a.cell
    · rw [if_pos hadm] at h; exact recKMintAsset_authorized s s' a.actor a.cell a.asset a.amt h
    · rw [if_neg hadm] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold mintStep at h
    by_cases hadm : acceptsEffects s a.cell
    · exact hadm
    · rw [if_neg hadm] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    -- bare ledger moves by `+amt` at the asset (the proved delta); held store fixed (the wrapper).
    have hbare : recTotalAsset s' b = recTotalAsset s b + (if b = a.asset then a.amt else 0) := by
      unfold mintStep at h
      by_cases hadm : acceptsEffects s a.cell
      · rw [if_pos hadm] at h; exact recKMintAsset_delta s s' a.actor a.cell a.asset a.amt h b
      · rw [if_neg hadm] at h; exact absurd h (by simp)
    have hheld : escrowHeldAsset s' b = escrowHeldAsset s b := mintStep_escrowHeld_fixed s s' a h b
    unfold recTotalAssetWithEscrow
    rw [hbare, hheld]; ring

/-! ### §1.2 — `burnH`: the per-asset burn, gated on cell liveness. `delta = -amt` at the asset. -/

/-- **The wrapped burn step.** Debit `cell`'s `asset` column by `amt` ONLY if `cell` is Live, then run
the proved `recKBurnAsset` (which itself also gates on availability + authority). -/
def burnStep (k : RecordKernelState) (a : SupplyArgs) : Option RecordKernelState :=
  if acceptsEffects k a.cell then recKBurnAsset k a.actor a.cell a.asset a.amt else none

/-- `recKBurnAsset` keeps `escrows` fixed (a `bal`-only edit), so the holding-store is unchanged. -/
theorem burnStep_escrowHeld_fixed (k k' : RecordKernelState) (a : SupplyArgs)
    (h : burnStep k a = some k') (b : AssetId) :
    escrowHeldAsset k' b = escrowHeldAsset k b := by
  unfold burnStep at h
  by_cases hadm : acceptsEffects k a.cell
  · rw [if_pos hadm] at h
    unfold recKBurnAsset at h
    by_cases hg : mintAuthorizedB k.caps a.actor a.cell = true ∧ 0 ≤ a.amt ∧ a.amt ≤ k.bal a.cell a.asset
        ∧ a.cell ∈ k.accounts
    · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h; rfl
    · rw [if_neg hg] at h; exact absurd h (by simp)
  · rw [if_neg hadm] at h; exact absurd h (by simp)

/-- **`burnH` — the registered per-asset BURN handler (`delta ≠ 0`).** The annihilative dual of `mintH`:
`conserves` composes `recKBurnAsset_delta` (the `-amt` move) with the held-fixed bridge; `auth_gated`
from `recKBurnAsset_authorized`; `admission_gated` from the Live-cell wrapper. -/
def burnH : EffectHandler SupplyArgs where
  step := burnStep
  delta := fun a b => if b = a.asset then (-a.amt) else 0
  auth := fun k a => mintAuthorizedB k.caps a.actor a.cell
  admission := fun k a => acceptsEffects k a.cell
  trace := fun a => { actor := a.actor, src := a.cell, dst := a.cell, amt := -a.amt }
  auth_gated := by
    intro s a s' h
    unfold burnStep at h
    by_cases hadm : acceptsEffects s a.cell
    · rw [if_pos hadm] at h; exact recKBurnAsset_authorized s s' a.actor a.cell a.asset a.amt h
    · rw [if_neg hadm] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold burnStep at h
    by_cases hadm : acceptsEffects s a.cell
    · exact hadm
    · rw [if_neg hadm] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    have hbare : recTotalAsset s' b = recTotalAsset s b + (if b = a.asset then (-a.amt) else 0) := by
      unfold burnStep at h
      by_cases hadm : acceptsEffects s a.cell
      · rw [if_pos hadm] at h; exact recKBurnAsset_delta s s' a.actor a.cell a.asset a.amt h b
      · rw [if_neg hadm] at h; exact absurd h (by simp)
    have hheld : escrowHeldAsset s' b = escrowHeldAsset s b := burnStep_escrowHeld_fixed s s' a h b
    unfold recTotalAssetWithEscrow
    rw [hbare, hheld]; ring

/-! ### §1.3 — `bridgeMintH`: `BridgeMint` ALIASES the per-asset mint kernel step.

dregg1's `Effect::BridgeMint` reuses the per-asset mint step over the bare `bal` ledger
(`TurnExecutorFull:4610` — `bridgeMint reuses the per-asset mint kernel step (recKMintAsset_delta)`).
So `bridgeMintH` is DEFINITIONALLY `mintH` (the same `mintStep`, same `+value` inflow delta); we register
it under its own tag so the audit trail records the bridge provenance. -/

/-- **`bridgeMintH` — `BridgeMint` registered as the mint alias.** Identical kernel step + obligations
to `mintH` (`bridgeMint` reuses `recKMintAsset`); `delta = +value` at the asset. -/
def bridgeMintH : EffectHandler SupplyArgs := mintH

/-! ### §1.4 — ACCOUNT-GROWTH: `createCellH` / `createCellFromFactoryH` / `spawnH`.

`Effect::CreateCell` mints a FRESH cell born EMPTY (`balance == 0` in every asset), so on the per-asset
ledger it is conservation-NEUTRAL (`delta = 0`) EVEN THOUGH `accounts` genuinely GREW — proved
non-vacuously via `recTotalAsset_insert_fresh` (the fresh cell contributes exactly `0`). Creation is
PRIVILEGED supply (`mintAuthorizedB` — bare ownership is NOT enough) AND requires a FRESH id
(`newCell ∉ accounts`, the exact freshness premise the neutrality lemma consumes). `spawn` /
`createCellFromFactory` are `createCell` plus a bal-orthogonal cap/metadata copy — still neutral. The
admission gate here is the freshness + privileged-creation gate (a cell can only be CREATED, never
"into a sealed cell" — the target does not yet exist), so `admission` reports `mintAuthorizedB ∧ fresh`. -/

/-- Account-growth (createCell/spawn) arguments: the privileged `actor` and the FRESH `newCell` id. -/
structure CreateArgs where
  /-- The actor performing the privileged creation (must hold `mintAuthorizedB` over `newCell`). -/
  actor : CellId
  /-- The FRESH cell id to mint (must be `∉ accounts`). -/
  newCell : CellId

/-- The privileged + freshness gate for account growth (the executable shadow of
`createCellChainA`'s gate, lifted to the bare kernel state). -/
def createGate (k : RecordKernelState) (a : CreateArgs) : Bool :=
  mintAuthorizedB k.caps a.actor a.newCell && decide (a.newCell ∉ k.accounts)

/-- **The createCell step.** Fail-closed: an authorized creator AND a FRESH id; on commit, insert the
fresh cell born EMPTY in every asset (`createCellIntoAsset` — grow `accounts`, reset the fresh `bal`
column to `0`). The dregg1-faithful born-`balance == 0`, so conservation-NEUTRAL. -/
def createCellStep (k : RecordKernelState) (a : CreateArgs) : Option RecordKernelState :=
  if createGate k a then some (createCellIntoAsset k a.newCell) else none

/-- **`createCellH` — the registered CreateCell handler (`delta = 0`, account-growth-neutral).**
`conserves` is the proved `recTotalAsset_insert_fresh` (the fresh cell contributes `0`; `escrows`
untouched). `auth_gated` from the privileged-creation conjunct of the gate. `admission_gated` from the
full gate (privileged creator AND fresh id). -/
def createCellH : EffectHandler CreateArgs where
  step := createCellStep
  delta := fun _ _ => 0          -- born empty ⇒ combined per-asset measure unchanged (growth-neutral)
  auth := fun k a => mintAuthorizedB k.caps a.actor a.newCell
  admission := fun k a => createGate k a
  trace := fun a => { actor := a.actor, src := a.newCell, dst := a.newCell, amt := 0 }
  auth_gated := by
    intro s a s' h
    unfold createCellStep createGate at h
    by_cases hg : mintAuthorizedB s.caps a.actor a.newCell && decide (a.newCell ∉ s.accounts)
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hg; exact hg.1
    · rw [if_neg hg] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold createCellStep at h
    by_cases hg : createGate s a
    · exact hg
    · rw [if_neg hg] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    unfold createCellStep createGate at h
    by_cases hg : mintAuthorizedB s.caps a.actor a.newCell && decide (a.newCell ∉ s.accounts)
    · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
      -- combined = bare + held; bare neutral by `recTotalAsset_insert_fresh`, held untouched.
      unfold recTotalAssetWithEscrow
      rw [recTotalAsset_insert_fresh s a.newCell b hg.2]
      have hheld : escrowHeldAsset (createCellIntoAsset s a.newCell) b = escrowHeldAsset s b := by
        unfold escrowHeldAsset createCellIntoAsset; rfl
      rw [hheld]; ring
    · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`createCellFromFactoryH` — `CreateCellFromFactory` as the createCell alias.** A factory-minted cell
is created born-empty exactly as `createCell` (the factory's slot-caveat install is bal-orthogonal —
it edits `slotCaveats`, never `bal`/`escrows`), so it shares `createCellH`'s neutral step + obligations.
The factory-program install is the next batch's concern (caveat enforcement); the SUPPLY content is the
growth-neutral creation. -/
def createCellFromFactoryH : EffectHandler CreateArgs := createCellH

/-- **The spawn step.** `SpawnWithDelegation` = `createCell` born-empty PLUS a bal-orthogonal cap copy +
delegation snapshot to the child (`caps`/`delegate`/`delegations` — never `bal`/`escrows`/`accounts`
beyond the fresh insert). We model the spawn here at the SUPPLY level: the conservation content is the
born-empty growth, so the step inserts the fresh child (the cap-copy is proven bal-orthogonal in
`TurnExecutorFull.spawnGrant_recTotalAsset` and is carried by the full executor's `spawnChainA`). -/
def spawnStep (k : RecordKernelState) (a : CreateArgs) : Option RecordKernelState :=
  createCellStep k a

/-- **`spawnH` — `SpawnWithDelegation` as the growth-neutral createCell.** Same neutral step +
obligations as `createCellH`: the spawn's resource content is the born-empty child; the cap handoff is
bal-orthogonal (`spawnGrant_recTotalAsset`). `delta = 0`. -/
def spawnH : EffectHandler CreateArgs := createCellH

/-! ## §2 — STATE/WRITE: balance-NEUTRAL named-field writes, gated on cell LIVENESS (closes R1/R6).

dregg1's `SetField`/`IncrementNonce`/`SetPermissions`/`SetVerificationKey`/`MakeSovereign`/`Refusal`/
`ReceiptArchive` are all balance-NEUTRAL writes to a NAMED field (`≠ "balance"`) of the
content-addressed record. `EffectsState.writeField` is the proved field-write (touches `cell` ONLY —
never `bal`/`escrows`/`lifecycle`), but the bare `EffectsState.stateStep` gates only on authority +
`target ∈ accounts`: it does NOT consult the cell's lifecycle, so a write into a SEALED/Destroyed cell
is silently admitted (the R6 hole — the write bypasses `cellSeal`). EACH handler here ROUTES the write
through the `acceptsEffects` live-cell gate — that WRAP is the hole-fix, and `admission_gated` makes it
a typing obligation. `delta = 0` and `conserves` is the trivial `bal`/`escrows`-frame (a `cell`-only
edit moves NEITHER the per-asset ledger NOR the holding-store). -/

/-- State-write arguments: the actor (authority subject), the target cell, the written field, and the
written scalar value. -/
structure StateWriteArgs where
  /-- The actor performing the write (must hold authority over `target`). -/
  actor : CellId
  /-- The cell whose named field is written. -/
  target : CellId
  /-- The named field written (`≠ "balance"` for every effect of this batch). -/
  field : FieldName
  /-- The scalar value written. -/
  value : Int

/-- **The R6-closing wrapped field write.** Commit the named-field write ONLY if `target` is Live
(`acceptsEffects`) AND the actor holds authority over it (`authorizedB` on the self-targeted turn);
then run the proved `writeField`. A write into a SEALED/Destroyed cell — which the bare `stateStep`
admits — is REJECTED here. -/
def stateWriteStep (k : RecordKernelState) (a : StateWriteArgs) : Option RecordKernelState :=
  if acceptsEffects k a.target
      && authorizedB k.caps { actor := a.actor, src := a.target, dst := a.target, amt := 0 } then
    some (writeField k a.field a.target (.int a.value))
  else none

/-- `writeField` edits ONLY `cell`, so a state write leaves the holding-store `escrows` literally
unchanged. -/
theorem stateWrite_escrowHeld_fixed (k : RecordKernelState) (a : StateWriteArgs) (b : AssetId) :
    escrowHeldAsset (writeField k a.field a.target (.int a.value)) b = escrowHeldAsset k b := by
  unfold escrowHeldAsset writeField; rfl

/-- `writeField` edits ONLY `cell`, so a state write leaves the per-asset `bal` ledger literally
unchanged. -/
theorem stateWrite_recTotalAsset_fixed (k : RecordKernelState) (a : StateWriteArgs) (b : AssetId) :
    recTotalAsset (writeField k a.field a.target (.int a.value)) b = recTotalAsset k b := by
  unfold recTotalAsset writeField; rfl

/-- **`stateWriteH` — the GENERIC live-gated named-field write handler.** `delta = 0`. `conserves` is
the trivial `bal`/`escrows`-frame (a `cell`-only edit). `auth_gated` from the authority conjunct of the
wrapper. The headline is `admission_gated`: the wrapper's `acceptsEffects` conjunct FORCES the liveness
check the bare `stateStep` skipped — a write into a SEALED cell does not type-check past it. Every
concrete state effect of this batch is THIS handler at a fixed field name. -/
def stateWriteH : EffectHandler StateWriteArgs where
  step := stateWriteStep
  delta := fun _ _ => 0
  auth := fun k a => authorizedB k.caps { actor := a.actor, src := a.target, dst := a.target, amt := 0 }
  admission := fun k a => acceptsEffects k a.target
  trace := fun a => { actor := a.actor, src := a.target, dst := a.target, amt := 0 }
  auth_gated := by
    intro s a s' h
    unfold stateWriteStep at h
    by_cases hg : acceptsEffects s a.target
        && authorizedB s.caps { actor := a.actor, src := a.target, dst := a.target, amt := 0 }
    · simp only [Bool.and_eq_true] at hg; exact hg.2
    · rw [if_neg hg] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold stateWriteStep at h
    by_cases hg : acceptsEffects s a.target
        && authorizedB s.caps { actor := a.actor, src := a.target, dst := a.target, amt := 0 }
    · simp only [Bool.and_eq_true] at hg; exact hg.1
    · rw [if_neg hg] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    unfold stateWriteStep at h
    by_cases hg : acceptsEffects s a.target
        && authorizedB s.caps { actor := a.actor, src := a.target, dst := a.target, amt := 0 }
    · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
      unfold recTotalAssetWithEscrow
      rw [stateWrite_recTotalAsset_fixed s a b, stateWrite_escrowHeld_fixed s a b]; ring
    · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ### §2.1 — The seven STATE effects as the generic write at a fixed field name.

Each is `stateWriteH` (the SAME proven handler) wrapped in a `ClosedEffect` builder that pins the
dregg1-faithful field name. They all share the R6-closing live-cell gate and `delta = 0` — the algebra
proves the obligation ONCE; adding an effect is fixing one field name. -/

/-- dregg1 field names for the seven state-write effects (all `≠ "balance"`). -/
def nonceField        : FieldName := "nonce"
def permissionsField  : FieldName := "permissions"
def vkField           : FieldName := "verification_key"
def sovereignField    : FieldName := "sovereign"
def refusalField      : FieldName := "refusal"
/-- The receipt-archive write targets the `"lifecycle"` RECORD slot — ALIGNED to `execFullA`'s
`receiptArchiveA` arm (`stateStep s lifecycleField actor cell (.int 1)`, see `Circuit/Spec/
cellstateaudit.lean`). Earlier this was a distinct `"receipt_archive"` flag, which made the
handler-vs-`execFullA` kernel diverge (the §6.3b hole); writing `"lifecycle"` closes it. -/
def receiptArchiveField : FieldName := "lifecycle"

/-! ## §3 — The SUPPLY+STATE registry coproduct and the `ClosedEffect` builders. -/

/-- The SUPPLY+STATE registry slice: mint, burn, bridge-mint, createCell, createCellFromFactory, spawn,
and the generic state write. Adding an effect is adding one well-typed `PackedHandler`. -/
def stateSupplyRegistry : Registry :=
  [ ⟨SupplyArgs, mintH⟩, ⟨SupplyArgs, burnH⟩, ⟨SupplyArgs, bridgeMintH⟩,
    ⟨CreateArgs, createCellH⟩, ⟨CreateArgs, createCellFromFactoryH⟩, ⟨CreateArgs, spawnH⟩,
    ⟨StateWriteArgs, stateWriteH⟩ ]

/-- Build a closed mint effect (tag `0`). -/
def mintEffect (actor cell : CellId) (asset : AssetId) (amt : Int) : ClosedEffect :=
  { tag := 0, Args := SupplyArgs,
    args := { actor := actor, cell := cell, asset := asset, amt := amt }, handler := mintH }

/-- Build a closed burn effect (tag `1`). -/
def burnEffect (actor cell : CellId) (asset : AssetId) (amt : Int) : ClosedEffect :=
  { tag := 1, Args := SupplyArgs,
    args := { actor := actor, cell := cell, asset := asset, amt := amt }, handler := burnH }

/-- Build a closed bridge-mint effect (tag `2`; aliases mint, `delta = +value`). -/
def bridgeMintEffect (actor cell : CellId) (asset : AssetId) (value : Int) : ClosedEffect :=
  { tag := 2, Args := SupplyArgs,
    args := { actor := actor, cell := cell, asset := asset, amt := value }, handler := bridgeMintH }

/-- Build a closed createCell effect (tag `3`). -/
def createCellEffect (actor newCell : CellId) : ClosedEffect :=
  { tag := 3, Args := CreateArgs, args := { actor := actor, newCell := newCell }, handler := createCellH }

/-- Build a closed createCellFromFactory effect (tag `4`). -/
def createCellFromFactoryEffect (actor newCell : CellId) : ClosedEffect :=
  { tag := 4, Args := CreateArgs, args := { actor := actor, newCell := newCell },
    handler := createCellFromFactoryH }

/-- Build a closed spawn effect (tag `5`). -/
def spawnEffect (actor child : CellId) : ClosedEffect :=
  { tag := 5, Args := CreateArgs, args := { actor := actor, newCell := child }, handler := spawnH }

/-- Build a closed state-write effect (tag `6`) at an explicit field name. -/
def stateWriteEffect (actor target : CellId) (field : FieldName) (value : Int) : ClosedEffect :=
  { tag := 6, Args := StateWriteArgs,
    args := { actor := actor, target := target, field := field, value := value }, handler := stateWriteH }

/-- `SetField` — the generic field write at an explicit field. -/
def setFieldEffect (actor target : CellId) (field : FieldName) (value : Int) : ClosedEffect :=
  stateWriteEffect actor target field value
/-- `IncrementNonce` — a write to the `nonce` field. -/
def incrementNonceEffect (actor target : CellId) (n : Int) : ClosedEffect :=
  stateWriteEffect actor target nonceField n
/-- `SetPermissions` — a write to the `permissions` field. -/
def setPermissionsEffect (actor target : CellId) (p : Int) : ClosedEffect :=
  stateWriteEffect actor target permissionsField p
/-- `SetVerificationKey` — a write to the `verification_key` field. -/
def setVKEffect (actor target : CellId) (vk : Int) : ClosedEffect :=
  stateWriteEffect actor target vkField vk
/-! ### §3.1 — `MakeSovereign` is a COMMITMENT-REBIND handler, not a flag write.

ALIGNED to `execFullA`'s `makeSovereignA` arm (`TurnExecutorFull.makeSovereignStep`): making a cell
sovereign DROPS its readable record and REPLACES it with a commitment-only record
(`makeSovereignKernel` / `sovereignRebind`, the faithful model of dregg1's
`cells.remove(id)` + `sovereign_commitments.insert(id, cell.state_commitment())`). The earlier flag
write (`sovereign := 1`) left the value readable — a semantic DIVERGENCE from `execFullA` (the
§6.3b hole). This handler runs the genuine rebind under the SAME live-cell + authority gate as the
other state writes (a STRENGTHENING: `execFullA` gates on `stateAuthB` alone; this adds
`acceptsEffects`). -/

/-- `MakeSovereign` arguments: the acting cell and the target made sovereign. -/
structure MakeSovereignArgs where
  /-- The actor (must hold authority over `target`). -/
  actor : CellId
  /-- The cell whose readable record is dropped behind a state commitment. -/
  target : CellId

/-- The commitment-rebind step: under the live-cell + self-authority gate, run the proved
`makeSovereignKernel` (drop the record, keep only the §8 state commitment). Fail-closed otherwise.
The committed kernel is EXACTLY `execFullA`'s `makeSovereignStep` post-kernel. -/
def makeSovereignStepK (k : RecordKernelState) (a : MakeSovereignArgs) : Option RecordKernelState :=
  if acceptsEffects k a.target
      && authorizedB k.caps { actor := a.actor, src := a.target, dst := a.target, amt := 0 } then
    some (Dregg2.Exec.TurnExecutorFull.makeSovereignKernel k a.target)
  else none

/-- **`makeSovereignH` — the commitment-rebind handler.** `delta = 0` (the rebind touches ONLY
`k.cell`; `recTotalAsset`/`escrowHeld` read `k.bal`/`k.escrows`, both fixed — `rfl`-grade). `auth` is
the self-targeted authority conjunct (= `stateAuthB`); `admission` is the `acceptsEffects` live-cell
gate. The headline is `admission_gated`: a make-sovereign into a SEALED cell is REJECTED — exactly the
live-cell discipline the other state writes carry, now over the whole-record drop. -/
def makeSovereignH : EffectHandler MakeSovereignArgs where
  step := makeSovereignStepK
  delta := fun _ _ => 0
  auth := fun k a => authorizedB k.caps { actor := a.actor, src := a.target, dst := a.target, amt := 0 }
  admission := fun k a => acceptsEffects k a.target
  trace := fun a => { actor := a.actor, src := a.target, dst := a.target, amt := 0 }
  auth_gated := by
    intro s a s' h
    unfold makeSovereignStepK at h
    by_cases hg : acceptsEffects s a.target
        && authorizedB s.caps { actor := a.actor, src := a.target, dst := a.target, amt := 0 }
    · simp only [Bool.and_eq_true] at hg; exact hg.2
    · rw [if_neg hg] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold makeSovereignStepK at h
    by_cases hg : acceptsEffects s a.target
        && authorizedB s.caps { actor := a.actor, src := a.target, dst := a.target, amt := 0 }
    · simp only [Bool.and_eq_true] at hg; exact hg.1
    · rw [if_neg hg] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    unfold makeSovereignStepK at h
    by_cases hg : acceptsEffects s a.target
        && authorizedB s.caps { actor := a.actor, src := a.target, dst := a.target, amt := 0 }
    · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
      unfold recTotalAssetWithEscrow
      rw [Dregg2.Exec.TurnExecutorFull.makeSovereignKernel_recTotalAsset s a.target b,
          show escrowHeldAsset (Dregg2.Exec.TurnExecutorFull.makeSovereignKernel s a.target) b
            = escrowHeldAsset s b from rfl]; ring
    · rw [if_neg hg] at h; exact absurd h (by simp)

/-- `MakeSovereign` — the commitment-rebind closed effect (tag `6`, the state family slot). DROPS
the readable record behind a state commitment, matching `execFullA`. -/
def makeSovereignEffect (actor target : CellId) : ClosedEffect :=
  { tag := 6, Args := MakeSovereignArgs,
    args := { actor := actor, target := target }, handler := makeSovereignH }
/-- `Refusal` — a write to the `refusal` field. -/
def refusalEffect (actor target : CellId) : ClosedEffect :=
  stateWriteEffect actor target refusalField 1
/-- `ReceiptArchive` — a write to the `receipt_archive` field. -/
def receiptArchiveEffect (actor target : CellId) (r : Int) : ClosedEffect :=
  stateWriteEffect actor target receiptArchiveField r

/-! ## §4 — TEETH: the R1/R6 attacks + the `delta ≠ 0` milestone, evaluated.

A write/mint into a SEALED/Destroyed cell is REJECTED; into a Live cell it SUCCEEDS; and a mint into a
Live cell RAISES the combined per-asset measure by exactly `+amt` (the `delta ≠ 0` milestone). The
gates are load-bearing: a handler whose step ignored `admission` would have FAILED `admission_gated`. -/

/-- A 2-cell, 1-asset fixture: cells 0 and 1 are live accounts; cell 0 holds 100 of asset 0 (on the
per-asset `bal` ledger). Cell 0 holds `node 0`/`node 1`/`node 2` caps — the PRIVILEGED mint authority
over those cells (a `node`/`control` cap, NOT bare ownership; `node 2` is the privileged-CREATION
authority for the fresh cell 2 in the account-growth eval). All cells default Live (`lifecycle = lcLive
= 0`). -/
def hs0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun c => if c = 0 then [Cap.node 0, Cap.node 1, Cap.node 2] else []
    bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0 }

/-- The SAME fixture but with cell 0 SEALED (`lcSealed = 1`) — a non-Live target. -/
def hs0Sealed : RecordKernelState :=
  { hs0 with lifecycle := fun c => if c = 0 then lcSealed else lcLive }

/-- The SAME fixture but with cell 0 DESTROYED (`lcDestroyed = 3`) — a non-Live target. -/
def hs0Destroyed : RecordKernelState :=
  { hs0 with lifecycle := fun c => if c = 0 then lcDestroyed else lcLive }

-- §TEETH-1 (the `delta ≠ 0` MILESTONE): a mint of 25 of asset 0 into LIVE cell 0 RAISES the combined
-- per-asset measure from 100 to 125 (`delta = +25`, NON-ZERO — the path `turn_conserves` sums).
#guard ((execEffect (mintEffect 0 0 0 25) hs0).map
        (fun k => (recTotalAssetWithEscrow hs0 0, recTotalAssetWithEscrow k 0))) == some (100, 125)  --  some (100, 125)
-- §TEETH-2 (R6 CLOSED): a mint into the SEALED cell 0 is REJECTED — the live-cell admission gate bites.
#guard ((execEffect (mintEffect 0 0 0 25) hs0Sealed).isSome) == false  --  false
-- §TEETH-3 (R6 CLOSED): a mint into the DESTROYED cell 0 is REJECTED too.
#guard ((execEffect (mintEffect 0 0 0 25) hs0Destroyed).isSome) == false  --  false
-- §TEETH-4: a burn of 40 of asset 0 from LIVE cell 0 LOWERS the combined measure to 60 (`delta = -40`).
#guard ((execEffect (burnEffect 0 0 0 40) hs0).map
        (fun k => recTotalAssetWithEscrow k 0)) == some 60  --  some 60
-- §TEETH-5: an UNAUTHORIZED mint (actor 1 holds NO node cap on cell 0) is REJECTED even into a Live cell.
#guard ((execEffect (mintEffect 1 0 0 25) hs0).isSome) == false  --  false
-- §TEETH-6 (account-growth, neutral): createCell of fresh cell 2 (by privileged actor 0) SUCCEEDS and
-- leaves the combined measure UNCHANGED (born empty), while genuinely growing `accounts`.
#guard ((execEffect (createCellEffect 0 2) hs0).map
        (fun k => (recTotalAssetWithEscrow k 0, decide (2 ∈ k.accounts)))) == some (100, true)  --  some (100, true)
-- §TEETH-7: createCell of a STALE id (cell 0 already exists) is REJECTED (the freshness gate bites —
-- this is the supply-amplification guard: a re-inserted credited id cannot manufacture supply).
#guard ((execEffect (createCellEffect 0 0) hs0).isSome) == false  --  false
-- §TEETH-8 (R6 CLOSED, state write): a SetField/IncrementNonce into the SEALED cell 0 is REJECTED.
#guard ((execEffect (incrementNonceEffect 0 0 7) hs0Sealed).isSome) == false  --  false
-- §TEETH-9: the SAME nonce write into a LIVE cell 0 SUCCEEDS and writes the field, measure unchanged.
#guard ((execEffect (incrementNonceEffect 0 0 7) hs0).map
        (fun k => (fieldOf nonceField (k.cell 0), recTotalAssetWithEscrow k 0))) == some (7, 100)  --  some (7, 100)
-- §TEETH-10: a turn = [mint 25; burn 10; setPermissions] runs through the registry foldlM and the
-- combined measure lands at 100 + 25 - 10 = 115 (the SUM of NON-ZERO deltas — the headline law).
#guard ((execTurn [mintEffect 0 0 0 25, burnEffect 0 0 0 10, setPermissionsEffect 0 0 3] hs0).map
        (fun k => recTotalAssetWithEscrow k 0)) == some 115  --  some 115
-- §TEETH-11: makeSovereign/refusal/receiptArchive into a SEALED cell are all REJECTED (R6 for all arms).
#guard ((execEffect (makeSovereignEffect 0 0) hs0Sealed).isSome) == false  --  false
#guard ((execEffect (refusalEffect 0 0) hs0Sealed).isSome) == false  --  false
#guard ((execEffect (receiptArchiveEffect 0 0 9) hs0Sealed).isSome) == false  --  false
-- §TEETH-11b: ALIGNMENT — into a LIVE cell, makeSovereign DROPS the readable record and replaces it
-- with the commitment-only record (the `execFullA` `makeSovereignKernel` rebind), so the readable
-- `balance` is GONE (`fieldOf "balance" = 0`, the FIELD_ZERO default) — NOT the old flag model where
-- balance stayed 100. NON-VACUITY: a flag handler would read `100` here; the rebind reads `0`.
#guard ((execEffect (makeSovereignEffect 0 0) hs0).map
        (fun k => fieldOf "balance" (k.cell 0))) == some 0  --  some 0 (record dropped)
-- and the rebound cell IS the commitment-only record (proved, not `#eval`'d — `Value` has no `BEq`):
example : (execEffect (makeSovereignEffect 0 0) hs0).map (fun k => k.cell 0)
    = some (Value.record
        [(Dregg2.Exec.TurnExecutorFull.commitmentField,
          Value.dig (Dregg2.Exec.TurnExecutorFull.stateCommitment (hs0.cell 0)))]) := by
  rfl

/-! ## §5 — turnDelta cross-check: the SUMMED non-zero deltas match the §TEETH-10 turn.

The §TEETH-10 turn's combined per-asset delta at asset 0 is `+25 - 10 + 0 = +15` (the SUM the
algebra's `turn_conserves` holds the measure to — evaluated to cross-check the milestone). -/
#guard (turnDelta [mintEffect 0 0 0 25, burnEffect 0 0 0 10, setPermissionsEffect 0 0 3] 0) == 15  --  15

/-! ## §6 — Axiom-hygiene pins (the keystones rest only on the three kernel axioms).

Pinning each handler `def` pins its obligation FIELDS transitively (the structure literal carries the
proofs), so these pins certify that mint/burn/createCell/state-write soundness rests only on the kernel
triple — a `sorryAx` anywhere in the composed lemmas would fail the pin (and the build). -/

#assert_axioms mintH
#assert_axioms burnH
#assert_axioms bridgeMintH
#assert_axioms createCellH
#assert_axioms createCellFromFactoryH
#assert_axioms spawnH
#assert_axioms stateWriteH
#assert_axioms makeSovereignH
#assert_axioms mintStep_escrowHeld_fixed
#assert_axioms burnStep_escrowHeld_fixed
#assert_axioms stateWrite_recTotalAsset_fixed
#assert_axioms stateWrite_escrowHeld_fixed

end Dregg2.Exec.Handlers.StateSupply
