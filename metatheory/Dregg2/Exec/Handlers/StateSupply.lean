/-
# Dregg2.Exec.Handlers.StateSupply — the STATE + SUPPLY handler batch.

The SECOND batch of `EffectHandler` instances (after the `transfer`/`escrow`/`state` slice in
`Dregg2/Exec/Handler.lean`). This file EXTENDS the algebra: every handler reuses an effect's EXISTING
kernel step + its already-proved conservation/authority lemma from `TurnExecutorFull`/`RecordKernel`,
WRAPPED — where the bare kernel op lacks one — in the lifecycle admission gate (`acceptsEffects`) that
the obligation `admission_gated` then forces. We do NOT touch `execFullA`/`FullActionA` (the cutover is
a later step); we only IMPORT and REUSE.

Two faces:

  * **SUPPLY (W1: `delta = 0` — the issuer-move).** `mintA`/`burnA`/`bridgeMintA` are ISSUER-MOVES
    (DREGG3 §2.2: `AssetId := CellId`; the issuer's negative-capable well carries −supply), so they
    CONSERVE the per-asset measure exactly like every other handler: `mintH.delta = 0`, discharged
    by the proved `recKMintAsset_delta` (exact conservation over the bare `bal` ledger). `burnH` is
    the return-to-well dual (`recKBurnAsset_delta`). `bridgeMintH` ALIASES the mint kernel step
    (the bridge cell IS the issuer of the bridged asset). The global `turn_conserves` now sums a
    family of zeros — exactness, not bookkeeping. `createCellH`/`createCellFromFactoryH`/`spawnH`
    are ACCOUNT-GROWTH: a fresh cell born EMPTY, so the COMBINED measure is unchanged (`delta = 0`)
    even though `accounts` GREW (`recTotalAsset_insert_fresh` — non-vacuous neutrality).

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

/-! ## §1 — SUPPLY (W1: `delta = 0` — the issuer-move). mint / burn / bridge-mint over the
per-asset `bal` ledger.

`recKMintAsset` / `recKBurnAsset` are the PROVED privileged per-asset supply ops, reshaped by W1
(DREGG3 §2.2) into ISSUER-MOVES: minting `amt` of asset `a` is an ordinary transfer from the
issuer's negative-capable well (`AssetId := CellId` — the asset IS its issuer cell) to the
recipient, burning is the return move. The gate is `mintAuthorizedB actor a` — authority over the
ISSUER (E2), never the recipient. Their `*_delta` lemmas now state EXACT conservation
(`recTotalAsset k' b = recTotalAsset k b`), so the supply handlers join every other handler at
`delta = 0` — the global `turn_conserves` sums a family of zeros. We WRAP each step in
`acceptsEffects` on the recipient/holder cell — a supply move into a non-Live cell is REJECTED. -/

/-- Per-asset supply (mint/burn) arguments: the actor (authority subject over the ISSUER = `asset`),
the recipient/holder `cell`, the moved `asset` (its issuer cell id), and the (non-negative) `amt`. -/
structure SupplyArgs where
  /-- The actor invoking the privileged supply op (must hold a `node`/`control` cap on the ISSUER
  cell — `asset` itself, W1/E2). -/
  actor : CellId
  /-- The recipient (mint) / holder (burn) cell. -/
  cell : CellId
  /-- The asset moved — the CellId of its issuer (W1: `AssetId := CellId`). -/
  asset : AssetId
  /-- The (non-negative) amount minted/burned. -/
  amt : Int

/-! ### §1.1 — `mintH`: the per-asset mint, gated on cell liveness. W1: `delta = 0` (issuer-move). -/

/-- **The R-closing wrapped mint step.** Move `amt` of `asset` from the issuer's well to `cell` ONLY
if `cell` is Live (`acceptsEffects`), then run the proved `recKMintAsset` (the issuer-move). A mint
into a non-Live cell is `none`. -/
def mintStep (k : RecordKernelState) (a : SupplyArgs) : Option RecordKernelState :=
  if acceptsEffects k a.cell then recKMintAsset k a.actor a.cell a.asset a.amt else none

/-- **`mintH` — the registered per-asset MINT handler (W1: `delta = 0`).** `conserves` is the proved
`recKMintAsset_delta` (exact conservation — the issuer-debit and recipient-credit cancel).
`auth_gated` from `recKMintAsset_authorized` (the privileged `mintAuthorizedB` gate over the
ISSUER). `admission_gated` from the Live-cell wrapper. -/
def mintH : EffectHandler SupplyArgs where
  step := mintStep
  delta := fun _ _ => 0
  auth := fun k a => mintAuthorizedB k.caps a.actor a.asset
  admission := fun k a => acceptsEffects k a.cell
  trace := fun a => { actor := a.actor, src := a.asset, dst := a.cell, amt := a.amt }
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
    -- W1: the issuer-move conserves exactly (the proved delta); the `+ 0` is definitional.
    have hbare : recTotalAsset s' b = recTotalAsset s b := by
      unfold mintStep at h
      by_cases hadm : acceptsEffects s a.cell
      · rw [if_pos hadm] at h; exact recKMintAsset_delta s s' a.actor a.cell a.asset a.amt h b
      · rw [if_neg hadm] at h; exact absurd h (by simp)
    rw [hbare]; ring

/-! ### §1.2 — `burnH`: the per-asset burn, gated on cell liveness. W1: `delta = 0` (return-to-well). -/

/-- **The wrapped burn step.** Return `amt` of `asset` from holder `cell` to the issuer's well ONLY
if `cell` is Live, then run the proved `recKBurnAsset` (which itself also gates on holder
availability + issuer authority). -/
def burnStep (k : RecordKernelState) (a : SupplyArgs) : Option RecordKernelState :=
  if acceptsEffects k a.cell then recKBurnAsset k a.actor a.cell a.asset a.amt else none

/-- **`burnH` — the registered per-asset BURN handler (W1: `delta = 0`).** The return-to-well dual of
`mintH`: `conserves` is `recKBurnAsset_delta` (exact); `auth_gated` from `recKBurnAsset_authorized`
(issuer authority); `admission_gated` from the Live-cell wrapper. -/
def burnH : EffectHandler SupplyArgs where
  step := burnStep
  delta := fun _ _ => 0
  -- STAGE-3 authority split: holder SELF-REDEEM (`actor == cell`, permissionless) OR issuer authority.
  auth := fun k a => (a.actor == a.cell) || mintAuthorizedB k.caps a.actor a.asset
  admission := fun k a => acceptsEffects k a.cell
  trace := fun a => { actor := a.actor, src := a.cell, dst := a.asset, amt := a.amt }
  auth_gated := by
    intro s a s' h
    unfold burnStep at h
    by_cases hadm : acceptsEffects s a.cell
    · rw [if_pos hadm] at h
      rcases recKBurnAsset_authorized s s' a.actor a.cell a.asset a.amt h with hself | hcap
      · simp [beq_iff_eq, hself]
      · simp [hcap]
    · rw [if_neg hadm] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold burnStep at h
    by_cases hadm : acceptsEffects s a.cell
    · exact hadm
    · rw [if_neg hadm] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    have hbare : recTotalAsset s' b = recTotalAsset s b := by
      unfold burnStep at h
      by_cases hadm : acceptsEffects s a.cell
      · rw [if_pos hadm] at h; exact recKBurnAsset_delta s s' a.actor a.cell a.asset a.amt h b
      · rw [if_neg hadm] at h; exact absurd h (by simp)
    rw [hbare]; ring

/-! ### §1.3 — `bridgeMintH`: `BridgeMint` ALIASES the per-asset mint kernel step.

dregg1's `Effect::BridgeMint` reuses the per-asset mint step over the bare `bal` ledger. W1: the
bridge cell IS the issuer of the bridged asset, so `bridgeMintH` is DEFINITIONALLY `mintH` (the
same issuer-move, the same exact conservation); we register it under its own tag so the audit
trail records the bridge provenance.

⚠ FAITHFULNESS SCOPE (Rust↔Lean kernel cross-check): this alias models ONLY the cell-backed
bridged-asset case — where a bridge cell IS the issuer and the bridge mints a `bal` credit, so
the issuer-liveness + per-asset conservation obligations of `mintH` apply verbatim. It is NOT
faithful to the deployed Rust `apply_bridge_mint` (`turn/src/executor/apply.rs`), which is a
NOTE-BRIDGE: it verifies a portable note STARK + inserts a nullifier and materializes value at
the NOTE layer, touching no issuer/recipient cell at all. That path has no cell to carry a
liveness gate; its soundness is CRYPTOGRAPHIC (federation-root binding + nullifier replay-
protection), a category distinct from cell-mint. Modeling the note-bridge proof inside the
verified surface is a separate note-layer spec, not this alias. -/

/-- **`bridgeMintH` — `BridgeMint` registered as the mint alias.** Identical kernel step + obligations
to `mintH` (`bridgeMint` reuses `recKMintAsset`); W1: exact conservation, the bridge well carries
−(outstanding bridged supply). -/
def bridgeMintH : EffectHandler SupplyArgs := mintH

/-! ### §1.4 — ACCOUNT-GROWTH: `createCellH` / `createCellFromFactoryH` / `spawnH`.

`Effect::CreateCell` mints a FRESH cell born EMPTY (`balance == 0` in every asset), so on the per-asset
ledger it is conservation-NEUTRAL (`delta = 0`) EVEN THOUGH `accounts` GREW — proved
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
      -- bare neutral by `recTotalAsset_insert_fresh` (born empty).
      rw [recTotalAsset_insert_fresh s a.newCell b hg.2]; ring
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
      rw [stateWrite_recTotalAsset_fixed s a b]; ring
    · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ### §2.0b — FLOOR-CARRYING STATE WRITES (the P1 migration: the gate-hole class closed structurally).

`stateWriteH` (above) is the GENERIC live-gated write the PROTOCOL-SLOT effects
(`IncrementNonce`/`SetPermissions`/`SetVK`/`SetProgram`/…) ride — each OWNS its (reserved) slot, so a
reserved-field gate would WRONGLY reject them. But the DEVELOPER-facing `SetField` (`.setFieldA`) must
fail-closed on the four protocol slots (the nonce-reset replay vector) AND honor the slot caveats; and
the dedicated `IncrementNonce` (`.incrementNonceA`) must fail-closed on a NON-advancing nonce (the
monotone floor). Carried TODAY as the `hnr`/`hcav`/`hmono` SIDE-HYPOTHESES of the refinement theorems —
the silent-gate holes.

The migration gives `.setFieldA` and `.incrementNonceA` their OWN floor-carrying handlers whose `step`
ROUTES THROUGH the just-banked gated kernel ops. The handler's `step` itself rejects a reserved /
caveat-violating / non-advancing write, so the refinement theorem reads the floor off the COMMIT
(`*_discharges` below) instead of taking it as a hypothesis — the side-hyp is SHED. -/

/-! #### `setFieldDevH` — the DEVELOPER `SetField`, reserved-field + caveat gated (sheds `hnr`/`hcav`). -/

/-- **The developer-write kernel step.** Fail-closed on a RESERVED protocol slot (`reservedField`), on
a caveat-violating write (`caveatsAdmit`), and on the live+authority gate `stateWriteStep` already
carries — then the same `writeField` post. The kernel twin of `EffectsState.stateStepDev` (which works
over `RecChainedState`); the reserved + caveat gates are read off the bare `RecordKernelState` so the
handler's own step now rejects what `hnr`/`hcav` USED to assert about the caller. -/
def setFieldDevStep (k : RecordKernelState) (a : StateWriteArgs) : Option RecordKernelState :=
  if (!EffectsState.reservedField a.field)
      && EffectsState.caveatsAdmit k a.field a.actor a.target a.value then
    stateWriteStep k a
  else none

/-- A committed developer write took a NON-reserved slot (`reservedField a.field = false`) — the
witness the reserved gate was passed. This is the `hnr` that `handler_refines_execFullA_setField`
USED to take as a hypothesis, now PRODUCED by the commit. -/
theorem setFieldDevStep_notReserved {k k' : RecordKernelState} {a : StateWriteArgs}
    (h : setFieldDevStep k a = some k') : EffectsState.reservedField a.field = false := by
  unfold setFieldDevStep at h
  by_cases hg : (!EffectsState.reservedField a.field)
      && EffectsState.caveatsAdmit k a.field a.actor a.target a.value
  · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hg; exact hg.1
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- A committed developer write satisfied every slot caveat (`caveatsAdmit = true`) — the `hcav` the
refinement USED to take, now read off the commit. -/
theorem setFieldDevStep_caveatsAdmit {k k' : RecordKernelState} {a : StateWriteArgs}
    (h : setFieldDevStep k a = some k') :
    EffectsState.caveatsAdmit k a.field a.actor a.target a.value = true := by
  unfold setFieldDevStep at h
  by_cases hg : (!EffectsState.reservedField a.field)
      && EffectsState.caveatsAdmit k a.field a.actor a.target a.value
  · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hg; exact hg.2
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- A committed developer write is EXACTLY the underlying `stateWriteStep` write (the reserved + caveat
gates only restrict the domain). Lifts `stateWriteStep`'s obligation discharges verbatim. -/
theorem setFieldDevStep_eq {k k' : RecordKernelState} {a : StateWriteArgs}
    (h : setFieldDevStep k a = some k') : stateWriteStep k a = some k' := by
  unfold setFieldDevStep at h
  by_cases hg : (!EffectsState.reservedField a.field)
      && EffectsState.caveatsAdmit k a.field a.actor a.target a.value
  · rw [if_pos hg] at h; exact h
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- FAIL-CLOSED: a developer `SetField` of a RESERVED slot does NOT commit (the reserved floor bites). -/
theorem setFieldDevStep_reserved_fails (k : RecordKernelState) (a : StateWriteArgs)
    (h : EffectsState.reservedField a.field = true) : setFieldDevStep k a = none := by
  unfold setFieldDevStep; rw [if_neg (by simp [h])]

/-- FAIL-CLOSED: a caveat-violating developer write does NOT commit (the caveat floor bites). -/
theorem setFieldDevStep_caveat_fails (k : RecordKernelState) (a : StateWriteArgs)
    (h : EffectsState.caveatsAdmit k a.field a.actor a.target a.value = false) :
    setFieldDevStep k a = none := by
  unfold setFieldDevStep; rw [if_neg (by simp [h])]

/-- **`setFieldDevH` — the reserved-field + caveat gated developer `SetField` handler.** Same `delta`
/`auth`/`admission`/`trace`/`conserves`/`auth_gated`/`admission_gated` as `stateWriteH` — all
discharged by routing the committed step through `setFieldDevStep_eq` to the underlying
`stateWriteStep`. The headline: the handler's OWN step rejects a reserved-slot or caveat-violating
write, so the `.setFieldA` refinement reads `hnr`/`hcav` OFF the commit rather than taking them as
hypotheses. -/
def setFieldDevH : EffectHandler StateWriteArgs where
  step := setFieldDevStep
  delta := fun _ _ => 0
  auth := fun k a => authorizedB k.caps { actor := a.actor, src := a.target, dst := a.target, amt := 0 }
  admission := fun k a => acceptsEffects k a.target
  trace := fun a => { actor := a.actor, src := a.target, dst := a.target, amt := 0 }
  auth_gated := by
    intro s a s' h; exact stateWriteH.auth_gated s a s' (setFieldDevStep_eq h)
  admission_gated := by
    intro s a s' h; exact stateWriteH.admission_gated s a s' (setFieldDevStep_eq h)
  conserves := by
    intro s a s' h b; exact stateWriteH.conserves s a s' (setFieldDevStep_eq h) b

/-! #### `incrementNonceDevH` — the MONOTONE `IncrementNonce` (sheds `hmono`). -/

/-- **The monotone-nonce kernel step.** Fail-closed on a NON-advancing nonce
(`fieldOf "nonce" (k.cell target) < value`), then the same live+authority `stateWriteStep` at the
`nonce` field. The kernel twin of `EffectsState.incrementNonceStep`; the monotone gate reads the bare
`RecordKernelState`, so the handler's own step rejects a reset — what `hmono` USED to assert. -/
def incrementNonceDevStep (k : RecordKernelState) (a : StateWriteArgs) : Option RecordKernelState :=
  if EffectsState.fieldOf "nonce" (k.cell a.target) < a.value then
    stateWriteStep k a
  else none

/-- A committed monotone-nonce write STRICTLY advanced the stored nonce — the `hmono` the refinement
USED to take, now read off the commit. -/
theorem incrementNonceDevStep_advances {k k' : RecordKernelState} {a : StateWriteArgs}
    (h : incrementNonceDevStep k a = some k') :
    EffectsState.fieldOf "nonce" (k.cell a.target) < a.value := by
  unfold incrementNonceDevStep at h
  by_cases hg : EffectsState.fieldOf "nonce" (k.cell a.target) < a.value
  · exact hg
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- A committed monotone-nonce write is EXACTLY the underlying `stateWriteStep` write. -/
theorem incrementNonceDevStep_eq {k k' : RecordKernelState} {a : StateWriteArgs}
    (h : incrementNonceDevStep k a = some k') : stateWriteStep k a = some k' := by
  unfold incrementNonceDevStep at h
  by_cases hg : EffectsState.fieldOf "nonce" (k.cell a.target) < a.value
  · rw [if_pos hg] at h; exact h
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- FAIL-CLOSED: a non-advancing `IncrementNonce` (a reset / no-op) does NOT commit (the monotone
floor bites). -/
theorem incrementNonceDevStep_nonincreasing_fails (k : RecordKernelState) (a : StateWriteArgs)
    (h : ¬ EffectsState.fieldOf "nonce" (k.cell a.target) < a.value) :
    incrementNonceDevStep k a = none := by
  unfold incrementNonceDevStep; rw [if_neg h]

/-- **`incrementNonceDevH` — the monotone `IncrementNonce` handler.** Same obligations as
`stateWriteH`, discharged via `incrementNonceDevStep_eq`. The handler's own step rejects a
non-advancing nonce, so the `.incrementNonceA` refinement reads `hmono` OFF the commit. -/
def incrementNonceDevH : EffectHandler StateWriteArgs where
  step := incrementNonceDevStep
  delta := fun _ _ => 0
  auth := fun k a => authorizedB k.caps { actor := a.actor, src := a.target, dst := a.target, amt := 0 }
  admission := fun k a => acceptsEffects k a.target
  trace := fun a => { actor := a.actor, src := a.target, dst := a.target, amt := 0 }
  auth_gated := by
    intro s a s' h; exact stateWriteH.auth_gated s a s' (incrementNonceDevStep_eq h)
  admission_gated := by
    intro s a s' h; exact stateWriteH.admission_gated s a s' (incrementNonceDevStep_eq h)
  conserves := by
    intro s a s' h b; exact stateWriteH.conserves s a s' (incrementNonceDevStep_eq h) b

/-! ### §2.1 — The seven STATE effects as the generic write at a fixed field name.

Each is `stateWriteH` (the SAME proven handler) wrapped in a `ClosedEffect` builder that pins the
dregg1-faithful field name. They all share the R6-closing live-cell gate and `delta = 0` — the algebra
proves the obligation ONCE; adding an effect is fixing one field name. -/

/-- dregg1 field names for the seven state-write effects (all `≠ "balance"`). -/
def nonceField        : FieldName := "nonce"
def permissionsField  : FieldName := "permissions"
def vkField           : FieldName := "verification_key"
def programField      : FieldName := "program"
def sovereignField    : FieldName := "sovereign"
def refusalField      : FieldName := "refusal"
/-- The receipt-archive write targets the `"lifecycle"` RECORD slot — ALIGNED to `execFullA`'s
`receiptArchiveA` arm (`stateStep s lifecycleField actor cell (.int 1)`, see `Circuit/Spec/
cellstateaudit.lean`). Earlier this was a distinct `"receipt_archive"` flag, which made the
handler-vs-`execFullA` kernel diverge (the §6.3b hole); writing `"lifecycle"` closes it. -/
def receiptArchiveField : FieldName := "lifecycle"

/-! ### §2.2 — THE HEAP write handler (REFINEMENT-DESIGN Decision 1, THE ROTATION's wire arm).

The handler face of `Substrate.HeapKernel.heapStepGuardedW`: the live-gated, authority-gated write
of the carried `newRoot` into the `heap_root` register PLUS the sorted insert-or-update splice of
the carried `addr ↦ value` into the target's `heaps` leaf list. Same gate pair as `stateWriteH`
(the `write`-verb family); the splice is balance-invisible (`recTotalAsset` reads neither `cell`
nor `heaps`). -/

/-- Heap-write arguments: the actor, the target cell, the carried sorted ADDRESS
(`addr = H[coll,key]`, the cap `slot_hash` discipline), the written value, and the carried
post-root (pinned into `heap_root`; verified by the descriptor gadget + the cell recompute). -/
structure HeapWriteArgs where
  /-- The actor performing the write (must hold authority over `target`). -/
  actor : CellId
  /-- The cell whose heap is written. -/
  target : CellId
  /-- The carried heap address (the sorted key, a Poseidon2 image of `(coll, key)`). -/
  addr : Int
  /-- The written value. -/
  value : Int
  /-- The carried post-root (pinned-as-digest into the `heap_root` register). -/
  newRoot : Int

/-- The live-gated heap write: gate exactly like `stateWriteStep`, then write `heap_root` AND
splice the target's heap leaf list. -/
def heapWriteStep (k : RecordKernelState) (a : HeapWriteArgs) : Option RecordKernelState :=
  if acceptsEffects k a.target
      && authorizedB k.caps { actor := a.actor, src := a.target, dst := a.target, amt := 0 } then
    some { writeField k Dregg2.Substrate.HeapKernel.heapRootField a.target (.int a.newRoot) with
             heaps := fun c => if c = a.target
                               then Dregg2.Substrate.Heap.set (k.heaps a.target) a.addr a.value
                               else k.heaps c }
  else none

/-- The spliced heap write leaves the per-asset ledger literally unchanged (`recTotalAsset` reads
`accounts`/`bal`; the step edits only `cell` + `heaps`). -/
theorem heapWrite_recTotalAsset_fixed (k : RecordKernelState) (a : HeapWriteArgs) (b : AssetId) :
    recTotalAsset { writeField k Dregg2.Substrate.HeapKernel.heapRootField a.target (.int a.newRoot) with
                      heaps := fun c => if c = a.target
                                        then Dregg2.Substrate.Heap.set (k.heaps a.target) a.addr a.value
                                        else k.heaps c } b
      = recTotalAsset k b := by
  unfold recTotalAsset writeField; rfl

/-- **`heapWriteH` — the heap-write handler.** `delta = 0`; the same live-cell + authority gate pair
as `stateWriteH`; the trace row is the standard clock row on the target. -/
def heapWriteH : EffectHandler HeapWriteArgs where
  step := heapWriteStep
  delta := fun _ _ => 0
  auth := fun k a => authorizedB k.caps { actor := a.actor, src := a.target, dst := a.target, amt := 0 }
  admission := fun k a => acceptsEffects k a.target
  trace := fun a => { actor := a.actor, src := a.target, dst := a.target, amt := 0 }
  auth_gated := by
    intro s a s' h
    unfold heapWriteStep at h
    by_cases hg : acceptsEffects s a.target
        && authorizedB s.caps { actor := a.actor, src := a.target, dst := a.target, amt := 0 }
    · simp only [Bool.and_eq_true] at hg; exact hg.2
    · rw [if_neg hg] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold heapWriteStep at h
    by_cases hg : acceptsEffects s a.target
        && authorizedB s.caps { actor := a.actor, src := a.target, dst := a.target, amt := 0 }
    · simp only [Bool.and_eq_true] at hg; exact hg.1
    · rw [if_neg hg] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    unfold heapWriteStep at h
    by_cases hg : acceptsEffects s a.target
        && authorizedB s.caps { actor := a.actor, src := a.target, dst := a.target, amt := 0 }
    · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
      rw [heapWrite_recTotalAsset_fixed s a b]; ring
    · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §3 — The SUPPLY+STATE registry coproduct and the `ClosedEffect` builders. -/

/-- The SUPPLY+STATE registry slice: mint, burn, bridge-mint, createCell, createCellFromFactory, spawn,
the generic state write, and the heap write. Adding an effect is adding one well-typed `PackedHandler`. -/
def stateSupplyRegistry : Registry :=
  [ ⟨SupplyArgs, mintH⟩, ⟨SupplyArgs, burnH⟩, ⟨SupplyArgs, bridgeMintH⟩,
    ⟨CreateArgs, createCellH⟩, ⟨CreateArgs, createCellFromFactoryH⟩, ⟨CreateArgs, spawnH⟩,
    ⟨StateWriteArgs, stateWriteH⟩, ⟨StateWriteArgs, setFieldDevH⟩,
    ⟨StateWriteArgs, incrementNonceDevH⟩, ⟨HeapWriteArgs, heapWriteH⟩ ]

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

/-- Build a closed heap-write effect (tag `7`): the carried `(addr, value, newRoot)` heap splice. -/
def heapWriteEffect (actor target : CellId) (addr value newRoot : Int) : ClosedEffect :=
  { tag := 7, Args := HeapWriteArgs,
    args := { actor := actor, target := target, addr := addr, value := value, newRoot := newRoot },
    handler := heapWriteH }

/-- `SetField` — the DEVELOPER field write, routed through the reserved-field + caveat gated
`setFieldDevH` (so a write of a protocol slot or a caveat-violating write FAILS in the handler's own
step — the floor is carried, not a caller obligation). -/
def setFieldEffect (actor target : CellId) (field : FieldName) (value : Int) : ClosedEffect :=
  { tag := 6, Args := StateWriteArgs,
    args := { actor := actor, target := target, field := field, value := value },
    handler := setFieldDevH }
/-- `IncrementNonce` — a write to the `nonce` field, routed through the MONOTONE-gated
`incrementNonceDevH` (a non-advancing nonce FAILS in the handler's own step — the monotone floor is
carried, not a caller obligation). -/
def incrementNonceEffect (actor target : CellId) (n : Int) : ClosedEffect :=
  { tag := 6, Args := StateWriteArgs,
    args := { actor := actor, target := target, field := nonceField, value := n },
    handler := incrementNonceDevH }
/-- `SetPermissions` — a write to the `permissions` field. -/
def setPermissionsEffect (actor target : CellId) (p : Int) : ClosedEffect :=
  stateWriteEffect actor target permissionsField p
/-- `SetVerificationKey` — a write to the `verification_key` field. -/
def setVKEffect (actor target : CellId) (vk : Int) : ClosedEffect :=
  stateWriteEffect actor target vkField vk
/-- `SetProgram` — a write to the `program` field (the cell's caveat-table slot). -/
def setProgramEffect (actor target : CellId) (prog : Int) : ClosedEffect :=
  stateWriteEffect actor target programField prog
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
      rw [Dregg2.Exec.TurnExecutorFull.makeSovereignKernel_recTotalAsset s a.target b]; ring
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

/-! ## §4 — TEETH: the R1/R6 attacks + the W1 exactness milestone, evaluated.

A write/mint into a SEALED/Destroyed cell is REJECTED; into a Live cell it SUCCEEDS; and a mint into
a Live cell CONSERVES the combined per-asset measure EXACTLY — the issuer's well debits what the
recipient credits (W1: the issuer-move; the well IS −supply). The gates are load-bearing: a handler
whose step ignored `admission` would have FAILED `admission_gated`. -/

/-- A 2-cell, 1-asset fixture: cells 0 and 1 are live accounts; cell 0 (the ISSUER of asset 0 —
W1: `AssetId := CellId`) holds 100 of asset 0, cell 1 holds 50. Cell 0 holds `node 0`/`node 1`/
`node 2` caps — `node 0` is the ISSUER authority for asset 0 (W1/E2: mint authority = control of
the issuer cell), `node 2` the privileged-CREATION authority for the fresh cell 2. All cells
default Live (`lifecycle = lcLive = 0`). -/
def hs0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun c => if c = 0 then [Cap.node 0, Cap.node 1, Cap.node 2] else []
    bal := fun c a => if c = 0 ∧ a = 0 then 100 else if c = 1 ∧ a = 0 then 50 else 0 }

/-- The SAME fixture but with cell 0 SEALED (`lcSealed = 1`) — a non-Live target. -/
def hs0Sealed : RecordKernelState :=
  { hs0 with lifecycle := fun c => if c = 0 then lcSealed else lcLive }

/-- The SAME fixture but with cell 0 DESTROYED (`lcDestroyed = 3`) — a non-Live target. -/
def hs0Destroyed : RecordKernelState :=
  { hs0 with lifecycle := fun c => if c = 0 then lcDestroyed else lcLive }

/-- The fixture with the RECIPIENT cell 1 SEALED (the mint-admission teeth). -/
def hs1Sealed : RecordKernelState :=
  { hs0 with lifecycle := fun c => if c = 1 then lcSealed else lcLive }

/-- The fixture with the recipient cell 1 DESTROYED. -/
def hs1Destroyed : RecordKernelState :=
  { hs0 with lifecycle := fun c => if c = 1 then lcDestroyed else lcLive }

-- §TEETH-1 (the W1 MILESTONE): a mint of 25 of asset 0 into LIVE cell 1 CONSERVES the combined
-- per-asset measure EXACTLY (150 → 150) — the issuer well 0 debits (100 → 75) while the recipient
-- credits (50 → 75). The supply increment lands ON the ledger, in the well.
#guard ((execEffect (mintEffect 0 1 0 25) hs0).map
        (fun k => (recTotalAsset hs0 0, recTotalAsset k 0))) == some (150, 150)  --  some (150, 150)
#guard ((execEffect (mintEffect 0 1 0 25) hs0).map
        (fun k => (k.bal 0 0, k.bal 1 0))) == some (75, 75)  --  the rows moved, the sum did not
-- §TEETH-2 (R6 CLOSED): a mint into the SEALED recipient cell 1 is REJECTED — the live-cell
-- admission gate bites.
#guard ((execEffect (mintEffect 0 1 0 25) hs1Sealed).isSome) == false  --  false
-- §TEETH-3 (R6 CLOSED): a mint into the DESTROYED recipient cell 1 is REJECTED too.
#guard ((execEffect (mintEffect 0 1 0 25) hs1Destroyed).isSome) == false  --  false
-- §TEETH-4: a burn of 40 of asset 0 from LIVE holder cell 1 RETURNS it to the well — measure
-- UNCHANGED (150), holder 50 → 10, well 100 → 140. Over-burning (60 > 50) is REJECTED.
#guard ((execEffect (burnEffect 0 1 0 40) hs0).map
        (fun k => (recTotalAsset k 0, k.bal 1 0, k.bal 0 0))) == some (150, 10, 140)  --  some (150, 10, 140)
#guard ((execEffect (burnEffect 0 1 0 60) hs0).isSome) == false  --  false (holder availability)
-- §TEETH-5: an UNAUTHORIZED mint (actor 1 holds NO node cap on the ISSUER cell 0) is REJECTED even
-- into a Live cell — production authority is control of the issuer (W1/E2).
#guard ((execEffect (mintEffect 1 1 0 25) hs0).isSome) == false  --  false
-- §TEETH-5b: self-mint into the issuer's own well is REJECTED (`a ≠ cell`).
#guard ((execEffect (mintEffect 0 0 0 25) hs0).isSome) == false  --  false
-- §TEETH-5c (STAGE-3, the non-self gate STILL bites): a burn of cell 1's holding by an actor (5) who
-- is NEITHER the holder NOR an issuer-cap holder is REJECTED — burning ANOTHER cell's holding stays
-- issuer-authority-gated. (Actor 5 holds no caps in hs0; cell 1 ≠ 5.)
#guard ((execEffect (burnEffect 5 1 0 40) hs0).isSome) == false  --  false (non-self, no issuer cap)
-- §TEETH-5d (STAGE-3, holder SELF-REDEEM is PERMISSIONLESS): cell 1 burning its OWN 40 of asset 0
-- (actor = holder = 1, NO issuer cap) now SUCCEEDS — the value returns to well 0, measure UNCHANGED
-- (holder 50 → 10, well 100 → 140). This is the relaxation: a genuine `cell ≠ asset` holder reduces
-- its own balance without an issuer cap. (Over-redeem 60 > 50 still REJECTED by holder availability.)
#guard ((execEffect (burnEffect 1 1 0 40) hs0).map
        (fun k => (recTotalAsset k 0, k.bal 1 0, k.bal 0 0))) == some (150, 10, 140)  --  some (150, 10, 140)
#guard ((execEffect (burnEffect 1 1 0 60) hs0).isSome) == false  --  false (self, but over-redeem)
-- §TEETH-6 (account-growth, neutral): createCell of fresh cell 2 (by privileged actor 0) SUCCEEDS and
-- leaves the combined measure UNCHANGED (born empty), while growing `accounts`.
#guard ((execEffect (createCellEffect 0 2) hs0).map
        (fun k => (recTotalAsset k 0, decide (2 ∈ k.accounts)))) == some (150, true)  --  some (150, true)
-- §TEETH-7: createCell of a STALE id (cell 0 already exists) is REJECTED (the freshness gate bites —
-- this is the supply-amplification guard: a re-inserted credited id cannot manufacture supply).
#guard ((execEffect (createCellEffect 0 0) hs0).isSome) == false  --  false
-- §TEETH-8 (R6 CLOSED, state write): a SetField/IncrementNonce into the SEALED cell 0 is REJECTED.
#guard ((execEffect (incrementNonceEffect 0 0 7) hs0Sealed).isSome) == false  --  false
-- §TEETH-9: the SAME nonce write into a LIVE cell 0 SUCCEEDS and writes the field, measure unchanged.
#guard ((execEffect (incrementNonceEffect 0 0 7) hs0).map
        (fun k => (fieldOf nonceField (k.cell 0), recTotalAsset k 0))) == some (7, 150)  --  some (7, 150)
-- §TEETH-9a (RESERVED FLOOR BITES, P1): a DEVELOPER `SetField` of a RESERVED protocol slot ("nonce")
-- into the LIVE, AUTHORIZED cell 0 is REJECTED by `setFieldDevH`'s OWN step — the reserved-field floor
-- the handler now CARRIES (a mutation that drops the gate would commit; this confirms it bites).
#guard ((execEffect (setFieldEffect 0 0 "nonce" 7) hs0).isSome) == false  --  false (reserved floor)
#guard ((execEffect (setFieldEffect 0 0 "permissions" 7) hs0).isSome) == false  --  false (reserved floor)
#guard ((execEffect (setFieldEffect 0 0 "verification_key" 7) hs0).isSome) == false  --  false
#guard ((execEffect (setFieldEffect 0 0 "program" 7) hs0).isSome) == false  --  false
-- §TEETH-9b: a DEVELOPER `SetField` of a NON-reserved slot ("display_name") SUCCEEDS (the floor only
-- forbids the four protocol slots — NON-VACUITY: the gate passes the honest write).
#guard ((execEffect (setFieldEffect 0 0 "display_name" 42) hs0).map
        (fun k => fieldOf "display_name" (k.cell 0))) == some 42  --  some 42
-- §TEETH-9c (MONOTONE FLOOR BITES, P1): a NON-advancing `IncrementNonce` is REJECTED by
-- `incrementNonceDevH`'s OWN step. First advance the stored nonce to 7, then a write of 7 (no-op) and
-- of 3 (a RESET) are both rejected — the monotone floor the handler now carries.
def hs0Nonce7 : RecordKernelState :=
  { hs0 with cell := fun c => if c = 0 then .record [("balance", .int 0), ("nonce", .int 7)] else hs0.cell c }
#guard ((execEffect (incrementNonceEffect 0 0 7) hs0Nonce7).isSome) == false  --  false (no-op, not advancing)
#guard ((execEffect (incrementNonceEffect 0 0 3) hs0Nonce7).isSome) == false  --  false (reset, replay vector)
#guard ((execEffect (incrementNonceEffect 0 0 9) hs0Nonce7).map
        (fun k => fieldOf nonceField (k.cell 0))) == some 9  --  some 9 (a strict advance commits)
-- §TEETH-10 (W1): a turn = [mint 25 → cell 1; burn 10 ← cell 1; setPermissions] runs through the
-- registry foldlM and the combined measure is EXACTLY CONSERVED at 150 — the sum of a family of
-- zeros (the issuer well absorbed the net +15: 100 → 85; cell 1 ended at 65).
#guard ((execTurn [mintEffect 0 1 0 25, burnEffect 0 1 0 10, setPermissionsEffect 0 0 3] hs0).map
        (fun k => (recTotalAsset k 0, k.bal 0 0, k.bal 1 0))) == some (150, 85, 65)  --  some (150, 85, 65)
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
-- and the rebound cell IS the commitment-form record (proved, not `#eval`'d — `Value` has no `BEq`):
-- commitment of the whole pre-state value, PLUS the RESERVED replay nonce (preserved, not reset to 0 —
-- the third nonce-reset vector closed; the host keeps the replay counter readable + monotone):
example : (execEffect (makeSovereignEffect 0 0) hs0).map (fun k => k.cell 0)
    = some (Value.record
        [(Dregg2.Exec.TurnExecutorFull.commitmentField,
          Value.dig (Dregg2.Exec.TurnExecutorFull.stateCommitment (hs0.cell 0))),
         (Dregg2.Exec.TurnExecutorFull.nonceField,
          Value.int (Dregg2.Exec.TurnExecutorFull.sovereignNonce (hs0.cell 0)))]) := by
  rfl

/-! ## §5 — turnDelta cross-check: the SUMMED deltas match the §TEETH-10 turn.

W1: the §TEETH-10 turn's combined per-asset delta at asset 0 is `0 + 0 + 0 = 0` — mint/burn are
issuer-moves, so `turn_conserves` holds the measure EXACTLY fixed (the cross-check of exactness). -/
#guard (turnDelta [mintEffect 0 1 0 25, burnEffect 0 1 0 10, setPermissionsEffect 0 0 3] 0) == 0  --  0 (W1: a family of zeros)

/-! ## §6 — Axiom-hygiene pins (the keystones rest only on the three kernel axioms).

Pinning each handler `def` pins its obligation FIELDS transitively (the structure literal carries the
proofs), so these pins certify that mint/burn/createCell/state-write soundness rests only on the kernel
triple. -/

#assert_axioms mintH
#assert_axioms burnH
#assert_axioms bridgeMintH
#assert_axioms createCellH
#assert_axioms createCellFromFactoryH
#assert_axioms spawnH
#assert_axioms stateWriteH
#assert_axioms setFieldDevH
#assert_axioms incrementNonceDevH
#assert_axioms makeSovereignH
#assert_axioms stateWrite_recTotalAsset_fixed

end Dregg2.Exec.Handlers.StateSupply
