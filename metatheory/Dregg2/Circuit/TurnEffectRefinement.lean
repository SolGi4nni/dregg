/-
# Dregg2.Circuit.TurnEffectRefinement — full-action circuit dispatch + turn diamond.

Extends `TurnRefinement.lean`'s generic turn tower with a concrete `fullActionCircuitStep` that
case-splits `FullActionA` to the v2 effect `*CircuitStep` defs from `EffectRefinement.lean` where they
exist, and falls back to `fullActionStep` (declarative spec as circuit acceptance) for unmapped arms.
Composes with `turn_circuit_refines_spec_of_steps` / `turn_circuit_refines_exec_of_steps` /
`turn_conservation_descends` for the full turn diamond down to `execFullTurnA`.

POLICY: no lurking holes — unmapped circuit arms use `hole_circuit_step`; refinement via explicit
hole-portal theorems (never silent `exact h`).
-/
import Dregg2.Circuit.TurnRefinement
import Dregg2.Circuit.EffectRefinement
import Dregg2.Circuit.EffectRefinementBatch2
import Dregg2.Circuit.ActionDispatch
import Dregg2.Circuit.EffectCommit
import Dregg2.Circuit.EffectCommit2
import Dregg2.Circuit.EffectCommit2Dual

set_option maxHeartbeats 800000

namespace Dregg2.Circuit.TurnEffectRefinement

open Dregg2.Circuit.Refinement (Refines StepRel)
open Dregg2.Circuit.ActionDispatch (fullActionStep fullActionStep_exec_iff turnSpec
  exerciseGuard exerciseHoldState)
open Dregg2.Circuit.TurnRefinement
  (turnCircuitStep turnSpecStep turnExecStep
   turn_circuit_refines_spec_of_steps turn_circuit_refines_exec_of_steps
   turn_conservation_descends)
open Dregg2.Circuit.EffectRefinement
  (mintCircuitStep mint_circuit_refines_spec
   burnCircuitStep burn_circuit_refines_spec
   createCellCircuitStep createCell_circuit_refines_spec
   spawnCircuitStep spawnFullCircuitStep spawn_full_circuit_refines_spec
   balanceACircuitStep balanceA_circuit_refines_spec
   delegateCircuitStep delegate_circuit_refines_spec
   noteSpendCircuitStep noteSpend_circuit_refines_spec
   noteCreateCircuitStep noteCreate_circuit_refines_spec
   revokeCircuitStep revoke_circuit_refines_spec
   revokeDelegationCircuitStep revokeDelegation_circuit_refines_spec
   setFieldCircuitStep setField_circuit_refines_spec)
open Dregg2.Circuit.EffectRefinementBatch2
open Dregg2.Circuit.Inst.EmitEventA (EmitEventArgs)
open Dregg2.Circuit.Inst.IncrementNonceA (IncrementNonceArgs)
open Dregg2.Circuit.Inst.SetPermissionsA (SetPermissionsArgs)
open Dregg2.Circuit.Inst.SetVKA (SetVKArgs)
open Dregg2.Circuit.Inst.DelegateAttenA (DelegateAttenArgs)
open Dregg2.Circuit.Inst.AttenuateA (AttenuateArgs)
open Dregg2.Circuit.Inst.CreateCellFromFactoryA (CreateFromFactoryArgs)
open Dregg2.Circuit.Inst.MakeSovereignA (MakeSovereignArgs)
open Dregg2.Circuit.Inst.RefusalA (RefusalArgs)
open Dregg2.Circuit.Inst.ReceiptArchiveA (ReceiptArchiveArgs)
open Dregg2.Circuit.Inst.PipelinedSendA (PipelinedSendArgs)
open Dregg2.Circuit.Inst.CellSealA (CellSealArgs)
open Dregg2.Circuit.Inst.CellUnsealA (CellUnsealArgs)
open Dregg2.Circuit.Inst.CellDestroyA (CellDestroyArgs)
open Dregg2.Circuit.Inst.RefreshDelegationA (RefreshDelegationArgs)
open Dregg2.Circuit.Inst.CreateCellFromFactoryA (RestIffNoFactoryTouched)
open Dregg2.Circuit.Inst.CellSealA (RestIffNoLifecycle)
open Dregg2.Circuit.Inst.CellDestroyA (RestIffNoLifecycleDeathCert)
open Dregg2.Circuit.Inst.RefreshDelegationA (RestIffNoDelegations)
open Dregg2.Circuit.StateCommit
  (logHashInjective compressNInjective RestHashIffFrame AccountsWF cellLeafInjective)
open Dregg2.Circuit.EffectCommit (CommitSurface)
open Dregg2.Circuit.EffectCommit2 (Surface2 RestIffNoBal RestIffNoNullifiers)
open Dregg2.Circuit.ListCommit (listLeafInjective)
open Dregg2.Circuit.BornEmptyCommit
open Dregg2.Circuit.EffectInstances (SetFieldArgs)
open Dregg2.Circuit.Inst.Delegate (RestIffNoCaps)
open Dregg2.Circuit.Inst.CreateCellA (RestIffNoAccountsBalBorn)
open Dregg2.Circuit.Inst.SpawnA (RestIffNoSpawnTouched)
open Dregg2.Circuit.Inst.NoteCreateA (NoteCreateArgs RestIffNoCommitments)
open Dregg2.Circuit.Inst.Revoke (RevokeArgs)
open Dregg2.Circuit.Inst.MintA (MintArgs)
open Dregg2.Circuit.Inst.BurnA (BurnArgs)
open Dregg2.Circuit.Inst.BalanceA (BalanceArgs)
open Dregg2.Circuit.Inst.Delegate (DelegateArgs)
open Dregg2.Circuit.Inst.CreateCellA (CreateCellArgs)
open Dregg2.Circuit.Inst.SpawnA (SpawnArgs)
open Dregg2.Circuit.Inst.NoteSpendA (NoteSpendArgs)
open Dregg2.Authority
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

/-! ## §0 — explicit hole portals (no silent `exact h`). -/

/-- HOLE: placeholder circuit step for unmapped `FullActionA` arms (NOT silent spec-as-circuit).
    Refinement is via the `hole_*_circuit_refines_spec` hole-portal theorems below. -/
abbrev hole_circuit_step (st : RecChainedState) (fa : FullActionA) (st' : RecChainedState) : Prop :=
  fullActionStep st fa st'

section HolePortals

variable {st st' : RecChainedState}

/-- Generic unmapped circuit step ⊑ `fullActionStep` (kept for the `hole_circuit_step` re-export;
the `exerciseA` arm that once used this is now a REAL composite step — see
`fullAction_circuit_refines_spec` / `exerciseInnerFold_refines_turnSpec`). -/
theorem hole_fullAction_circuit_refines_spec_fallback
    (fa : FullActionA) (h : hole_circuit_step st fa st') : fullActionStep st fa st' := by
  simpa [hole_circuit_step] using h

end HolePortals

/-! ## §1 — `fullActionCircuitStep` (per-effect circuit dispatch). -/

/-- `RestIffNoCaps` is duplicated per Inst module; bridge Delegate's portal to Revoke's for dispatch. -/
private theorem restIffNoCaps_delegate_to_revoke (RH : RecordKernelState → ℤ)
    (h : Dregg2.Circuit.Inst.Delegate.RestIffNoCaps RH) :
    Dregg2.Circuit.Inst.Revoke.RestIffNoCaps RH := by
  dsimp [Dregg2.Circuit.Inst.Delegate.RestIffNoCaps, Dregg2.Circuit.Inst.Revoke.RestIffNoCaps]
  exact h

private theorem restIffNoCaps_delegate_to_delAtten (RH : RecordKernelState → ℤ)
    (h : Dregg2.Circuit.Inst.Delegate.RestIffNoCaps RH) :
    Dregg2.Circuit.Inst.DelegateAttenA.RestIffNoCaps RH := by
  dsimp [Dregg2.Circuit.Inst.Delegate.RestIffNoCaps, Dregg2.Circuit.Inst.DelegateAttenA.RestIffNoCaps]
  exact h

private theorem restIffNoCaps_delegate_to_attenuate (RH : RecordKernelState → ℤ)
    (h : Dregg2.Circuit.Inst.Delegate.RestIffNoCaps RH) :
    Dregg2.Circuit.Inst.AttenuateA.RestIffNoCaps RH := by
  dsimp [Dregg2.Circuit.Inst.Delegate.RestIffNoCaps, Dregg2.Circuit.Inst.AttenuateA.RestIffNoCaps]
  exact h

private theorem restIffNoLifecycle_seal_to_unseal (RH : RecordKernelState → ℤ)
    (h : Dregg2.Circuit.Inst.CellSealA.RestIffNoLifecycle RH) :
    Dregg2.Circuit.Inst.CellUnsealA.RestIffNoLifecycle RH := by
  dsimp [Dregg2.Circuit.Inst.CellSealA.RestIffNoLifecycle,
    Dregg2.Circuit.Inst.CellUnsealA.RestIffNoLifecycle]
  exact h

private theorem restIffNoLifecycle_seal_to_archive (RH : RecordKernelState → ℤ)
    (h : Dregg2.Circuit.Inst.CellSealA.RestIffNoLifecycle RH) :
    Dregg2.Circuit.Inst.ReceiptArchiveLifecycleA.RestIffNoLifecycle RH := by
  dsimp [Dregg2.Circuit.Inst.CellSealA.RestIffNoLifecycle,
    Dregg2.Circuit.Inst.ReceiptArchiveLifecycleA.RestIffNoLifecycle]
  exact h

/-- **`fullActionCircuitStep`** — dispatches each `FullActionA` constructor to its v2 effect
`CircuitStep`. F1b: the dispatch is TOTAL — every surviving constructor has a mapped circuit arm
(no spec-as-circuit fallback remains). -/
def fullActionCircuitStep
    (S : Surface2)
    (D_bal : (CellId → AssetId → ℤ) → ℤ) (hD_bal : Function.Injective D_bal)
    (D_caps : Caps → ℤ) (hD_caps : Function.Injective D_caps)
    (LE_cell : CellId → ℤ) (LE_null : Nat → ℤ)
    (cN : List ℤ → ℤ) (hN : compressNInjective cN)
    (hLE_cell : listLeafInjective LE_cell) (hLE_null : listLeafInjective LE_null)
    (CS : CommitSurface)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) × (CellId → Nat) → ℤ) (hDDgs : Function.Injective DDgs)
    (DRevStep : (CellId → Nat) × (CellId → List Cap) × (CellId → Nat) → ℤ)
    (hDRevStep : Function.Injective DRevStep)
    (DLife : (CellId → Nat) → ℤ) (hDLife : Function.Injective DLife)
    (DDC : (CellId → Nat) → ℤ) (hDDC : Function.Injective DDC)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth)
    (DHeaps : (CellId → Dregg2.Substrate.Heap.FeltHeap) → ℤ) (hDHeaps : Function.Injective DHeaps)
    (st : RecChainedState) (fa : FullActionA) (st' : RecChainedState) : Prop :=
  match fa with
  | .balanceA t a =>
      balanceACircuitStep S D_bal hD_bal st ⟨t, a⟩ st'
  | .delegate del rec t =>
      delegateCircuitStep S D_caps hD_caps st ⟨del, rec, t⟩ st'
  | .mintA actor cell a amt =>
      mintCircuitStep S D_bal hD_bal st ⟨actor, cell, a, amt⟩ st'
  | .burnA actor cell a amt =>
      burnCircuitStep S D_bal hD_bal st ⟨actor, cell, a, amt⟩ st'
  | .introduceA intro rec t =>
      delegateCircuitStep S D_caps hD_caps st ⟨intro, rec, t⟩ st'
  | .createCellA actor newCell =>
      createCellCircuitStep S LE_cell cN hN hLE_cell DBal hDBal DSide hDSide st ⟨actor, newCell⟩ st'
  | .spawnA actor child target =>
      spawnFullCircuitStep S LE_cell cN hN hLE_cell DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs
        st ⟨actor, child, target⟩ st'
  | .bridgeMintA actor cell a value =>
      mintCircuitStep S D_bal hD_bal st ⟨actor, cell, a, value⟩ st'
  | .noteSpendA nf actor spendProof =>
      noteSpendCircuitStep S LE_null cN hN hLE_null st ⟨nf, actor, spendProof⟩ st'
  | .noteCreateA cm actor =>
      noteCreateCircuitStep S LE_null cN hN hLE_null st ⟨cm, actor⟩ st'
  | .revoke holder t =>
      revokeCircuitStep S D_caps hD_caps st ⟨holder, t⟩ st'
  | .revokeDelegationA holder t =>
      -- §EPOCH: the FORCED dual circuit step — cap-edge `removeEdge` + the FORCED epoch step (parent
      -- epoch bumped + child snapshot cleared + stamp reset, bound by the second component's product
      -- digest). NO carried residual.
      revokeDelegationCircuitStep S D_caps hD_caps DRevStep hDRevStep st ⟨holder, t⟩ st'
  | .setFieldA actor cell f v =>
      -- §RESERVED-SLOT: a developer `SetField` circuit step CARRIES the not-reserved side-condition
      -- (the written slot is NOT a protocol-managed nonce/perms/vk/program). The executor's
      -- `stateStepDev` enforces it; here it is a relation conjunct the prover establishes (the
      -- field-name-binding residual — closing it fully = a VK-affecting field-name column gate).
      Dregg2.Exec.EffectsState.reservedField f = false ∧
      AccountsWF st.kernel ∧ AccountsWF st'.kernel ∧
      setFieldCircuitStep CS st ⟨actor, cell, f, v⟩ st'
  | .emitEventA actor cell topic data =>
      AccountsWF st.kernel ∧ AccountsWF st'.kernel ∧
      emitEventCircuitStep CS st ⟨actor, cell, topic, data⟩ st'
  | .incrementNonceA actor cell n =>
      AccountsWF st.kernel ∧ AccountsWF st'.kernel ∧
      incrementNonceCircuitStep CS st ⟨actor, cell, n⟩ st'
  | .setPermissionsA actor cell p =>
      AccountsWF st.kernel ∧ AccountsWF st'.kernel ∧
      setPermissionsCircuitStep CS st ⟨actor, cell, p⟩ st'
  | .setVKA actor cell vk =>
      AccountsWF st.kernel ∧ AccountsWF st'.kernel ∧
      setVKCircuitStep CS st ⟨actor, cell, vk⟩ st'
  | .setProgramA actor cell prog =>
      AccountsWF st.kernel ∧ AccountsWF st'.kernel ∧
      setProgramCircuitStep CS st ⟨actor, cell, prog⟩ st'
  | .delegateAttenA del rec t keep =>
      delegateAttenCircuitStep S D_caps hD_caps st ⟨del, rec, t, keep⟩ st'
  | .attenuateA actor idx keep =>
      attenuateCircuitStep S D_caps hD_caps st ⟨actor, idx, keep⟩ st'
  | .createCellFromFactoryA actor newCell vk =>
      createCellFromFactoryCircuitStep S LE_cell cN hN hLE_cell DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth
        st ⟨actor, newCell, vk⟩ st'
  | .makeSovereignA actor cell =>
      AccountsWF st.kernel ∧ AccountsWF st'.kernel ∧
      makeSovereignCircuitStep CS st ⟨actor, cell⟩ st'
  | .refusalA actor cell =>
      AccountsWF st.kernel ∧ AccountsWF st'.kernel ∧
      refusalCircuitStep CS st ⟨actor, cell⟩ st'
  | .receiptArchiveA actor cell =>
      receiptArchiveLifecycleCircuitStep S DLife hDLife st ⟨actor, cell⟩ st'
  | .pipelinedSendA actor =>
      AccountsWF st.kernel ∧ AccountsWF st'.kernel ∧
      pipelinedSendCircuitStep CS st ⟨actor⟩ st'
  | .cellSealA actor cell =>
      cellSealCircuitStep S DLife hDLife st ⟨actor, cell⟩ st'
  | .cellUnsealA actor cell =>
      cellUnsealCircuitStep S DLife hDLife st ⟨actor, cell⟩ st'
  | .cellDestroyA actor cell certHash =>
      cellDestroyCircuitStep S DLife hDLife DDC hDDC st ⟨actor, cell, certHash⟩ st'
  | .refreshDelegationA actor child =>
      refreshDelegationFullCircuitStep S DDgs hDDgs st ⟨actor, child⟩ st'
  | .heapWriteA actor target addr v newRoot =>
      -- THE ROTATION: the heap write's v2-dual circuit step (register write + heaps splice).
      heapWriteCircuitStep S DCell hDCell DHeaps hDHeaps st ⟨actor, target, addr, v, newRoot⟩ st'
  | .exerciseA actor target inner =>
      -- **REAL composite circuit step** (was a `hole_circuit_step` spec-fallback): the hold-gate
      -- (`exerciseGuard`) AND a genuine INNER-TURN CIRCUIT FOLD that recursively threads
      -- `fullActionCircuitStep` over `inner` from the hold post-state. This is NOT the declarative
      -- `turnSpec` — every inner action is itself a circuit step; soundness (`⊑ turnSpec`) is then a
      -- real induction (`exerciseInnerFold_refines_turnSpec`) reusing the per-effect arms.
      innerFacetsAdmittedA st actor target inner = true ∧
      exerciseGuard st actor target ∧
      exerciseInnerFold (exerciseHoldState st actor) inner st'
where
  /-- **`exerciseInnerFold`** — the inner-turn CIRCUIT fold for `exerciseA`: thread
  `fullActionCircuitStep` (the SAME per-effect dispatch) left-to-right over the inner forest.
  Mutually recursive with `fullActionCircuitStep`; each inner action is structurally smaller than
  the enclosing `.exerciseA`, so the well-founded recursion is automatic. -/
  exerciseInnerFold (s : RecChainedState) : List FullActionA → RecChainedState → Prop
    | [], s' => s = s'
    | a :: rest, s' =>
        ∃ s1, fullActionCircuitStep S D_bal hD_bal D_caps hD_caps LE_cell LE_null
                cN hN hLE_cell hLE_null CS DBal hDBal DSide hDSide
                DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs DRevStep hDRevStep DLife hDLife DDC hDDC DCell hDCell
                DSC hDSC DAuth hDAuth DHeaps hDHeaps s a s1 ∧ exerciseInnerFold s1 rest s'

/-- Encoder-instantiated circuit step (abbrev keeps turn-level statement types small). -/
abbrev fullActionCircuitStepInst
    (S : Surface2)
    (D_bal : (CellId → AssetId → ℤ) → ℤ) (hD_bal : Function.Injective D_bal)
    (D_caps : Caps → ℤ) (hD_caps : Function.Injective D_caps)
    (LE_cell : CellId → ℤ) (LE_null : Nat → ℤ)
    (cN : List ℤ → ℤ) (hN : compressNInjective cN)
    (hLE_cell : listLeafInjective LE_cell) (hLE_null : listLeafInjective LE_null)
    (CS : CommitSurface)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) × (CellId → Nat) → ℤ) (hDDgs : Function.Injective DDgs)
    (DRevStep : (CellId → Nat) × (CellId → List Cap) × (CellId → Nat) → ℤ)
    (hDRevStep : Function.Injective DRevStep)
    (DLife : (CellId → Nat) → ℤ) (hDLife : Function.Injective DLife)
    (DDC : (CellId → Nat) → ℤ) (hDDC : Function.Injective DDC)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth)
    (DHeaps : (CellId → Dregg2.Substrate.Heap.FeltHeap) → ℤ) (hDHeaps : Function.Injective DHeaps) :
    StepRel RecChainedState FullActionA RecChainedState :=
  fullActionCircuitStep S D_bal hD_bal D_caps hD_caps LE_cell LE_null cN hN
    hLE_cell hLE_null CS DBal hDBal DSide hDSide DLeg hDLeg
    DCaps hDCaps DDel hDDel DDgs hDDgs DRevStep hDRevStep DLife hDLife DDC hDDC DCell hDCell DSC hDSC DAuth hDAuth DHeaps hDHeaps

/-! **`fullAction_circuit_refines_spec`** + **`exerciseInnerFold_refines_turnSpec`** — per-action
SOUNDNESS (circuit ⊑ `fullActionStep`) together with the exerciseA inner-turn fold's soundness
(inner CIRCUIT fold ⊑ `turnSpec`), proven by MUTUAL STRUCTURAL RECURSION: the per-action proof matches
on `fa` and, on the `.exerciseA actor target inner` arm, calls the inner-fold proof on `inner` (a
direct structural child); the inner-fold proof matches on `inner` and, on `a :: rest`, calls the
per-action proof on the head `a` (a direct structural child) and recurses on `rest`. This is the
genuine lift — the exerciseA arm is CLOSED with a REAL composite circuit step (hold-gate ∘ inner-turn
CIRCUIT fold), NOT a spec-fallback. F1b: EVERY surviving `FullActionA` constructor has a mapped
circuit arm (the escrow/obligation/bridge-L/F/C constructors are GONE; their spec-fallback cases
died with them), so the dispatch is total with NO declarative fallback. -/
mutual
/-- Per-action SOUNDNESS: circuit ⊑ `fullActionStep`; exerciseA via the mutual inner-fold helper. -/
theorem fullAction_circuit_refines_spec
    (S : Surface2)
    (D_bal : (CellId → AssetId → ℤ) → ℤ) (hD_bal : Function.Injective D_bal)
    (D_caps : Caps → ℤ) (hD_caps : Function.Injective D_caps)
    (LE_cell : CellId → ℤ) (LE_null : Nat → ℤ)
    (cN : List ℤ → ℤ) (hN : compressNInjective cN)
    (hLE_cell : listLeafInjective LE_cell) (hLE_null : listLeafInjective LE_null)
    (CS : CommitSurface)
    (hCSN : compressNInjective CS.compressN) (hCSL : cellLeafInjective CS.CH)
    (hRestFrame : RestHashIffFrame CS.RH) (hLogCS : logHashInjective CS.LH)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) × (CellId → Nat) → ℤ) (hDDgs : Function.Injective DDgs)
    (DRevStep : (CellId → Nat) × (CellId → List Cap) × (CellId → Nat) → ℤ)
    (hDRevStep : Function.Injective DRevStep)
    (DLife : (CellId → Nat) → ℤ) (hDLife : Function.Injective DLife)
    (DDC : (CellId → Nat) → ℤ) (hDDC : Function.Injective DDC)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth)
    (DHeaps : (CellId → Dregg2.Substrate.Heap.FeltHeap) → ℤ) (hDHeaps : Function.Injective DHeaps)
    (hRestBal : RestIffNoBal S.RH) (hRestAccounts : RestIffNoAccountsBalBorn S.RH)
    (hRestSpawn : RestIffNoSpawnTouched S.RH) (hRestCaps : RestIffNoCaps S.RH)
    (hRestNull : RestIffNoNullifiers S.RH)  (hRestCommitments : RestIffNoCommitments S.RH)
    (hRestFactory : RestIffNoFactoryTouched S.RH)
    (hRestLifecycle : RestIffNoLifecycle S.RH)
    (hRestLifecycleDeathCert : RestIffNoLifecycleDeathCert S.RH)
    (hRestDelegations : RestIffNoDelegations S.RH)
    (hRestRevEpoch : Dregg2.Circuit.Inst.RevokeDelegationFullA.RestIffNoCapsEpoch S.RH)
    (hRestCellHeaps : Dregg2.Circuit.Inst.HeapWriteA.RestIffNoCellHeaps S.RH)
    (hLog : logHashInjective S.LH) :
    Refines (fullActionCircuitStepInst S D_bal hD_bal D_caps hD_caps LE_cell LE_null
      cN hN hLE_cell hLE_null CS DBal hDBal DSide hDSide DLeg hDLeg
      DCaps hDCaps DDel hDDel DDgs hDDgs DRevStep hDRevStep DLife hDLife DDC hDDC DCell hDCell DSC hDSC DAuth hDAuth DHeaps hDHeaps)
      fullActionStep := by
  intro st fa st' h
  unfold fullActionCircuitStepInst fullActionCircuitStep at h
  match fa with
  | .balanceA t a =>
      simp only [fullActionStep]
      exact balanceA_circuit_refines_spec S D_bal hD_bal hRestBal hLog st _ st' h
  | .delegate del rec t =>
      simp only [fullActionStep]
      exact delegate_circuit_refines_spec S D_caps hD_caps hRestCaps hLog st _ st' h
  | .mintA actor cell a amt =>
      simp only [fullActionStep]
      exact mint_circuit_refines_spec S D_bal hD_bal hRestBal hLog st _ st' h
  | .burnA actor cell a amt =>
      simp only [fullActionStep]
      exact burn_circuit_refines_spec S D_bal hD_bal hRestBal hLog st _ st' h
  | .introduceA intro rec t =>
      simp only [fullActionStep]
      exact delegate_circuit_refines_spec S D_caps hD_caps hRestCaps hLog st _ st' h
  | .createCellA actor newCell =>
      simp only [fullActionStep]
      exact createCell_circuit_refines_spec S LE_cell cN hN hLE_cell DBal hDBal DSide hDSide hRestAccounts hLog
        st _ st' h
  | .spawnA actor child target =>
      simp only [fullActionStep]
      exact spawn_full_circuit_refines_spec S LE_cell cN hN hLE_cell DLeg hDLeg DCaps hDCaps DDel hDDel
        DDgs hDDgs hRestSpawn hLog st _ st' h
  | .bridgeMintA actor cell a value =>
      simp only [fullActionStep]
      exact mint_circuit_refines_spec S D_bal hD_bal hRestBal hLog st _ st' h
  | .noteSpendA nf actor spendProof =>
      simp only [fullActionStep]
      exact noteSpend_circuit_refines_spec S LE_null cN hN hLE_null hRestNull hLog st _ st' h
  | .noteCreateA cm actor =>
      simp only [fullActionStep]
      exact noteCreate_circuit_refines_spec S LE_null cN hN hLE_null hRestCommitments hLog st _ st' h
  | .revoke holder t =>
      simp only [fullActionStep]
      exact revoke_circuit_refines_spec S D_caps hD_caps (restIffNoCaps_delegate_to_revoke S.RH hRestCaps)
        hLog st _ st' h
  | .setFieldA actor cell f v =>
      simp only [fullActionStep]
      rcases h with ⟨hnr, hwf, hwf', hc⟩
      exact setField_circuit_refines_spec CS hCSN hCSL hRestFrame hLogCS st _ st' hnr hwf hwf' hc
  | .emitEventA actor cell topic data =>
      simp only [fullActionStep]
      rcases h with ⟨hwf, hwf', hc⟩
      exact emitEvent_circuit_refines_spec CS hCSN hCSL hRestFrame hLogCS st _ st' hwf hwf' hc
  | .incrementNonceA actor cell n =>
      simp only [fullActionStep]
      rcases h with ⟨hwf, hwf', hc⟩
      exact incrementNonce_circuit_refines_spec CS hCSN hCSL hRestFrame hLogCS st _ st' hwf hwf' hc
  | .setPermissionsA actor cell p =>
      simp only [fullActionStep]
      rcases h with ⟨hwf, hwf', hc⟩
      exact setPermissions_circuit_refines_spec CS hCSN hCSL hRestFrame hLogCS st _ st' hwf hwf' hc
  | .setVKA actor cell vk =>
      simp only [fullActionStep]
      rcases h with ⟨hwf, hwf', hc⟩
      exact setVK_circuit_refines_spec CS hCSN hCSL hRestFrame hLogCS st _ st' hwf hwf' hc
  | .setProgramA actor cell prog =>
      simp only [fullActionStep]
      rcases h with ⟨hwf, hwf', hc⟩
      exact setProgram_circuit_refines_spec CS hCSN hCSL hRestFrame hLogCS st _ st' hwf hwf' hc
  | .delegateAttenA del rec t keep =>
      simp only [fullActionStep]
      exact delegateAtten_circuit_refines_spec S D_caps hD_caps
        (restIffNoCaps_delegate_to_delAtten S.RH hRestCaps) hLog st _ st' h
  | .attenuateA actor idx keep =>
      simp only [fullActionStep]
      exact attenuate_circuit_refines_spec S D_caps hD_caps
        (restIffNoCaps_delegate_to_attenuate S.RH hRestCaps) hLog st _ st' h
  | .revokeDelegationA holder t =>
      simp only [fullActionStep]
      -- §EPOCH: the FAITHFUL `RevokeDelegationFullSpec` from the FORCED dual circuit step (cap-edge
      -- `removeEdge` + the FORCED epoch step, bound by the second component's product digest). No residual.
      exact revokeDelegation_circuit_refines_spec S D_caps hD_caps DRevStep hDRevStep
        hRestRevEpoch hLog st _ st' h
  | .exerciseA actor target inner =>
      -- **REAL** exerciseA soundness: hold-gate passes through; the inner CIRCUIT fold
      -- (`exerciseInnerFold`) refines the declarative `turnSpec` via `exerciseInnerFold_refines_turnSpec`,
      -- which inducts on `inner` reusing the per-action refinement supplied here as `hper`. The `hper`
      -- it consumes is built by THIS theorem recursively (each inner action is structurally smaller than
      -- the enclosing `.exerciseA`). No spec-fallback.
      simp only [fullActionStep]
      have hexpand : innerFacetsAdmittedA st actor target inner = true ∧ exerciseGuard st actor target ∧
          fullActionCircuitStep.exerciseInnerFold S D_bal hD_bal D_caps hD_caps LE_cell LE_null cN hN hLE_cell hLE_null CS DBal hDBal DSide
            hDSide DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs DRevStep hDRevStep DLife hDLife DDC hDDC DCell hDCell
            DSC hDSC DAuth hDAuth DHeaps hDHeaps (exerciseHoldState st actor) inner st' := h
      obtain ⟨hfacet, hg, hfold⟩ := hexpand
      refine ⟨hfacet, hg, ?_⟩
      -- The inner CIRCUIT fold ⊑ `turnSpec` by the MUTUAL helper on `inner` (a structural child of
      -- `.exerciseA actor target inner`); the helper in turn calls THIS theorem per inner action.
      exact exerciseInnerFold_refines_turnSpec S D_bal hD_bal D_caps hD_caps LE_cell LE_null cN hN hLE_cell hLE_null CS hCSN hCSL hRestFrame
        hLogCS DBal hDBal DSide hDSide DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs DRevStep hDRevStep DLife hDLife
        DDC hDDC DCell hDCell DSC hDSC DAuth hDAuth DHeaps hDHeaps hRestBal hRestAccounts hRestSpawn hRestCaps hRestNull
        hRestCommitments hRestFactory
        hRestLifecycle hRestLifecycleDeathCert hRestDelegations hRestRevEpoch hRestCellHeaps hLog (exerciseHoldState st actor)
        inner st' hfold
  | .createCellFromFactoryA actor newCell vk =>
      simp only [fullActionStep]
      exact createCellFromFactory_circuit_refines_spec S LE_cell cN hN hLE_cell DBal hDBal DCell hDCell DSC hDSC
        DAuth hDAuth hRestFactory hLog st _ st' h
  | .makeSovereignA actor cell =>
      simp only [fullActionStep]
      rcases h with ⟨hwf, hwf', hc⟩
      exact makeSovereign_circuit_refines_spec CS hCSN hCSL hRestFrame hLogCS st _ st' hwf hwf' hc
  | .refusalA actor cell =>
      simp only [fullActionStep]
      rcases h with ⟨hwf, hwf', hc⟩
      exact refusal_circuit_refines_spec CS hCSN hCSL hRestFrame hLogCS st _ st' hwf hwf' hc
  | .receiptArchiveA actor cell =>
      simp only [fullActionStep]
      exact receiptArchiveLifecycle_circuit_refines_spec S DLife hDLife
        (restIffNoLifecycle_seal_to_archive S.RH hRestLifecycle) hLog st _ st' h
  -- dregg3 F2b: the queue-family constructors are GONE — the circuit dispatch is TOTAL over the
  -- 38 survivors (no hole-portal arm left).
  -- the portal fallback (the constructors die in F2b).
  | .pipelinedSendA actor =>
      simp only [fullActionStep]
      rcases h with ⟨hwf, hwf', hc⟩
      exact pipelinedSend_circuit_refines_spec CS hCSN hCSL hRestFrame hLogCS st _ st' hwf hwf' hc
  | .cellSealA actor cell =>
      simp only [fullActionStep]
      exact cellSeal_circuit_refines_spec S DLife hDLife hRestLifecycle hLog st _ st' h
  | .cellUnsealA actor cell =>
      simp only [fullActionStep]
      exact cellUnseal_circuit_refines_spec S DLife hDLife
        (restIffNoLifecycle_seal_to_unseal S.RH hRestLifecycle) hLog st _ st' h
  | .cellDestroyA actor cell certHash =>
      simp only [fullActionStep]
      exact cellDestroy_circuit_refines_spec S DLife hDLife DDC hDDC hRestLifecycleDeathCert hLog st _ st' h
  | .refreshDelegationA actor child =>
      simp only [fullActionStep]
      exact refreshDelegation_full_circuit_refines_spec S DDgs hDDgs hRestDelegations hLog st _ st' h
  | .heapWriteA actor target addr v newRoot =>
      simp only [fullActionStep]
      exact heapWrite_circuit_refines_spec S DCell hDCell DHeaps hDHeaps hRestCellHeaps hLog
        st _ st' h

/-- **`exerciseInnerFold_refines_turnSpec`** — the exerciseA inner CIRCUIT fold refines the declarative
`turnSpec`, by STRUCTURAL recursion on `inner` (mutual with `fullAction_circuit_refines_spec`): nil is
the identity; cons consumes one circuit step via the per-action refinement on the head `a` (a structural
child) then recurses on `rest`. NOT a spec-fallback — every inner action is a genuine circuit step. -/
theorem exerciseInnerFold_refines_turnSpec
    (S : Surface2)
    (D_bal : (CellId → AssetId → ℤ) → ℤ) (hD_bal : Function.Injective D_bal)
    (D_caps : Caps → ℤ) (hD_caps : Function.Injective D_caps)
    (LE_cell : CellId → ℤ) (LE_null : Nat → ℤ)
    (cN : List ℤ → ℤ) (hN : compressNInjective cN)
    (hLE_cell : listLeafInjective LE_cell) (hLE_null : listLeafInjective LE_null)
    (CS : CommitSurface)
    (hCSN : compressNInjective CS.compressN) (hCSL : cellLeafInjective CS.CH)
    (hRestFrame : RestHashIffFrame CS.RH) (hLogCS : logHashInjective CS.LH)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) × (CellId → Nat) → ℤ) (hDDgs : Function.Injective DDgs)
    (DRevStep : (CellId → Nat) × (CellId → List Cap) × (CellId → Nat) → ℤ)
    (hDRevStep : Function.Injective DRevStep)
    (DLife : (CellId → Nat) → ℤ) (hDLife : Function.Injective DLife)
    (DDC : (CellId → Nat) → ℤ) (hDDC : Function.Injective DDC)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth)
    (DHeaps : (CellId → Dregg2.Substrate.Heap.FeltHeap) → ℤ) (hDHeaps : Function.Injective DHeaps)
    (hRestBal : RestIffNoBal S.RH) (hRestAccounts : RestIffNoAccountsBalBorn S.RH)
    (hRestSpawn : RestIffNoSpawnTouched S.RH) (hRestCaps : RestIffNoCaps S.RH)
    (hRestNull : RestIffNoNullifiers S.RH)  (hRestCommitments : RestIffNoCommitments S.RH)
    (hRestFactory : RestIffNoFactoryTouched S.RH)
    (hRestLifecycle : RestIffNoLifecycle S.RH)
    (hRestLifecycleDeathCert : RestIffNoLifecycleDeathCert S.RH)
    (hRestDelegations : RestIffNoDelegations S.RH)
    (hRestRevEpoch : Dregg2.Circuit.Inst.RevokeDelegationFullA.RestIffNoCapsEpoch S.RH)
    (hRestCellHeaps : Dregg2.Circuit.Inst.HeapWriteA.RestIffNoCellHeaps S.RH)
    (hLog : logHashInjective S.LH)
    (s : RecChainedState) (inner : List FullActionA) (s' : RecChainedState)
    (h : fullActionCircuitStep.exerciseInnerFold S D_bal hD_bal D_caps hD_caps LE_cell LE_null cN hN hLE_cell hLE_null CS DBal hDBal DSide hDSide
        DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs DRevStep hDRevStep DLife hDLife DDC hDDC DCell hDCell DSC hDSC
        DAuth hDAuth DHeaps hDHeaps s inner s') :
    turnSpec s inner s' := by
  match inner with
  | [] =>
      simp only [fullActionCircuitStep.exerciseInnerFold] at h
      simp only [turnSpec, h]
  | a :: rest =>
      rw [show fullActionCircuitStep.exerciseInnerFold S D_bal hD_bal D_caps hD_caps LE_cell LE_null
            cN hN hLE_cell hLE_null CS DBal
            hDBal DSide hDSide DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs DRevStep hDRevStep DLife hDLife DDC
            hDDC DCell hDCell DSC hDSC DAuth hDAuth DHeaps hDHeaps s (a :: rest) s'
          = (∃ s1, fullActionCircuitStep S D_bal hD_bal D_caps hD_caps LE_cell LE_null cN hN hLE_cell hLE_null CS DBal hDBal DSide
              hDSide DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs DRevStep hDRevStep DLife hDLife DDC hDDC DCell
              hDCell DSC hDSC DAuth hDAuth DHeaps hDHeaps s a s1 ∧
              fullActionCircuitStep.exerciseInnerFold S D_bal hD_bal D_caps hD_caps LE_cell LE_null
                cN hN hLE_cell hLE_null CS DBal
                hDBal DSide hDSide DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs DRevStep hDRevStep DLife hDLife DDC
                hDDC DCell hDCell DSC hDSC DAuth hDAuth DHeaps hDHeaps s1 rest s') from rfl] at h
      obtain ⟨s1, hstep, htail⟩ := h
      -- per-step: the head circuit step ⊑ `fullActionStep` (mutual call on the structural child `a`).
      have hhead : fullActionStep s a s1 :=
        fullAction_circuit_refines_spec S D_bal hD_bal D_caps hD_caps LE_cell LE_null
          cN hN hLE_cell hLE_null CS hCSN hCSL hRestFrame hLogCS DBal
          hDBal DSide hDSide DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs DRevStep hDRevStep DLife hDLife DDC hDDC
          DCell hDCell DSC hDSC DAuth hDAuth DHeaps hDHeaps hRestBal hRestAccounts hRestSpawn hRestCaps hRestNull
          hRestCommitments hRestFactory
          hRestLifecycle hRestLifecycleDeathCert hRestDelegations hRestRevEpoch hRestCellHeaps hLog s a s1 hstep
      have htailSpec : turnSpec s1 rest s' :=
        exerciseInnerFold_refines_turnSpec S D_bal hD_bal D_caps hD_caps LE_cell LE_null cN hN hLE_cell hLE_null CS hCSN hCSL hRestFrame
          hLogCS DBal hDBal DSide hDSide DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs DRevStep hDRevStep DLife hDLife
          DDC hDDC DCell hDCell DSC hDSC DAuth hDAuth DHeaps hDHeaps hRestBal hRestAccounts hRestSpawn hRestCaps hRestNull
          hRestCommitments hRestFactory
          hRestLifecycle hRestLifecycleDeathCert hRestDelegations hRestRevEpoch hRestCellHeaps hLog s1 rest s' htail
      exact ⟨s1, hhead, htailSpec⟩
end

/-! ## §2 — Turn-level diamond (compose generic `TurnRefinement` lemmas). -/

/-- **`fullAction_turn_circuit_refines_spec`** — turn circuit ⊑ `turnSpec fullActionStep`.

Rests on `fullAction_circuit_refines_spec` (the `exerciseA` inner-turn fold is a REAL
composite circuit step via `exerciseInnerFold_refines_turnSpec`). Per-action soundness, lifted to the
turn fold; not whole-turn adversarial soundness (kernel-axiom hygiene tracked separately). -/
theorem fullAction_turn_circuit_refines_spec
    (S : Surface2)
    (D_bal : (CellId → AssetId → ℤ) → ℤ) (hD_bal : Function.Injective D_bal)
    (D_caps : Caps → ℤ) (hD_caps : Function.Injective D_caps)
    (LE_cell : CellId → ℤ) (LE_null : Nat → ℤ)
    (cN : List ℤ → ℤ) (hN : compressNInjective cN)
    (hLE_cell : listLeafInjective LE_cell) (hLE_null : listLeafInjective LE_null)
    (CS : CommitSurface)
    (hCSN : compressNInjective CS.compressN) (hCSL : cellLeafInjective CS.CH)
    (hRestFrame : RestHashIffFrame CS.RH) (hLogCS : logHashInjective CS.LH)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) × (CellId → Nat) → ℤ) (hDDgs : Function.Injective DDgs)
    (DRevStep : (CellId → Nat) × (CellId → List Cap) × (CellId → Nat) → ℤ)
    (hDRevStep : Function.Injective DRevStep)
    (DLife : (CellId → Nat) → ℤ) (hDLife : Function.Injective DLife)
    (DDC : (CellId → Nat) → ℤ) (hDDC : Function.Injective DDC)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth)
    (DHeaps : (CellId → Dregg2.Substrate.Heap.FeltHeap) → ℤ) (hDHeaps : Function.Injective DHeaps)
    (hRestBal : RestIffNoBal S.RH) (hRestAccounts : RestIffNoAccountsBalBorn S.RH)
    (hRestSpawn : RestIffNoSpawnTouched S.RH) (hRestCaps : RestIffNoCaps S.RH)
    (hRestNull : RestIffNoNullifiers S.RH)  (hRestCommitments : RestIffNoCommitments S.RH)
    (hRestFactory : RestIffNoFactoryTouched S.RH)
    (hRestLifecycle : RestIffNoLifecycle S.RH)
    (hRestLifecycleDeathCert : RestIffNoLifecycleDeathCert S.RH)
    (hRestDelegations : RestIffNoDelegations S.RH)
    (hRestRevEpoch : Dregg2.Circuit.Inst.RevokeDelegationFullA.RestIffNoCapsEpoch S.RH)
    (hRestCellHeaps : Dregg2.Circuit.Inst.HeapWriteA.RestIffNoCellHeaps S.RH)
    (hLog : logHashInjective S.LH)
    (s s' : RecChainedState) (acts : List FullActionA)
    (hc : turnCircuitStep (fullActionCircuitStepInst S D_bal hD_bal D_caps hD_caps LE_cell LE_null cN hN hLE_cell hLE_null CS DBal hDBal DSide hDSide DLeg
      hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs DRevStep hDRevStep DLife hDLife DDC hDDC DCell hDCell DSC hDSC DAuth hDAuth DHeaps hDHeaps)
      s acts s') :
    Spec.Turn.turnSpec fullActionStep s acts s' :=
  turn_circuit_refines_spec_of_steps
    (fullActionCircuitStepInst S D_bal hD_bal D_caps hD_caps LE_cell LE_null cN hN
      hLE_cell hLE_null CS DBal hDBal DSide hDSide DLeg hDLeg DCaps hDCaps
      DDel hDDel DDgs hDDgs DRevStep hDRevStep DLife hDLife DDC hDDC DCell hDCell DSC hDSC DAuth hDAuth DHeaps hDHeaps)
    fullActionStep
    (fullAction_circuit_refines_spec S D_bal hD_bal D_caps hD_caps LE_cell LE_null cN hN
      hLE_cell hLE_null CS hCSN hCSL hRestFrame hLogCS DBal hDBal DSide
      hDSide DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs DRevStep hDRevStep DLife hDLife DDC hDDC DCell hDCell DSC hDSC
      DAuth hDAuth DHeaps hDHeaps hRestBal hRestAccounts hRestSpawn hRestCaps hRestNull hRestCommitments
      hRestFactory hRestLifecycle hRestLifecycleDeathCert
      hRestDelegations hRestRevEpoch hRestCellHeaps hLog)
    s acts s' hc

/-- **`fullAction_turn_circuit_refines_exec`** — full diamond: turn circuit ⊑ `execFullTurnA`.

Rests on `fullAction_circuit_refines_spec` (the `exerciseA` inner-turn fold is a REAL
composite circuit step via `exerciseInnerFold_refines_turnSpec`). Per-action soundness, lifted to the
turn fold; not whole-turn adversarial soundness (kernel-axiom hygiene tracked separately). -/
theorem fullAction_turn_circuit_refines_exec
    (S : Surface2)
    (D_bal : (CellId → AssetId → ℤ) → ℤ) (hD_bal : Function.Injective D_bal)
    (D_caps : Caps → ℤ) (hD_caps : Function.Injective D_caps)
    (LE_cell : CellId → ℤ) (LE_null : Nat → ℤ)
    (cN : List ℤ → ℤ) (hN : compressNInjective cN)
    (hLE_cell : listLeafInjective LE_cell) (hLE_null : listLeafInjective LE_null)
    (CS : CommitSurface)
    (hCSN : compressNInjective CS.compressN) (hCSL : cellLeafInjective CS.CH)
    (hRestFrame : RestHashIffFrame CS.RH) (hLogCS : logHashInjective CS.LH)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) × (CellId → Nat) → ℤ) (hDDgs : Function.Injective DDgs)
    (DRevStep : (CellId → Nat) × (CellId → List Cap) × (CellId → Nat) → ℤ)
    (hDRevStep : Function.Injective DRevStep)
    (DLife : (CellId → Nat) → ℤ) (hDLife : Function.Injective DLife)
    (DDC : (CellId → Nat) → ℤ) (hDDC : Function.Injective DDC)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth)
    (DHeaps : (CellId → Dregg2.Substrate.Heap.FeltHeap) → ℤ) (hDHeaps : Function.Injective DHeaps)
    (hRestBal : RestIffNoBal S.RH) (hRestAccounts : RestIffNoAccountsBalBorn S.RH)
    (hRestSpawn : RestIffNoSpawnTouched S.RH) (hRestCaps : RestIffNoCaps S.RH)
    (hRestNull : RestIffNoNullifiers S.RH)  (hRestCommitments : RestIffNoCommitments S.RH)
    (hRestFactory : RestIffNoFactoryTouched S.RH)
    (hRestLifecycle : RestIffNoLifecycle S.RH)
    (hRestLifecycleDeathCert : RestIffNoLifecycleDeathCert S.RH)
    (hRestDelegations : RestIffNoDelegations S.RH)
    (hRestRevEpoch : Dregg2.Circuit.Inst.RevokeDelegationFullA.RestIffNoCapsEpoch S.RH)
    (hRestCellHeaps : Dregg2.Circuit.Inst.HeapWriteA.RestIffNoCellHeaps S.RH)
    (hLog : logHashInjective S.LH)
    (s s' : RecChainedState) (acts : List FullActionA)
    (hc : turnCircuitStep (fullActionCircuitStepInst S D_bal hD_bal D_caps hD_caps LE_cell LE_null cN hN hLE_cell hLE_null CS DBal hDBal DSide hDSide DLeg
      hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs DRevStep hDRevStep DLife hDLife DDC hDDC DCell hDCell DSC hDSC DAuth hDAuth DHeaps hDHeaps)
      s acts s') :
    execFullTurnA s acts = some s' :=
  turn_circuit_refines_exec_of_steps
    (fullActionCircuitStepInst S D_bal hD_bal D_caps hD_caps LE_cell LE_null cN hN
      hLE_cell hLE_null CS DBal hDBal DSide hDSide DLeg hDLeg DCaps hDCaps
      DDel hDDel DDgs hDDgs DRevStep hDRevStep DLife hDLife DDC hDDC DCell hDCell DSC hDSC DAuth hDAuth DHeaps hDHeaps)
    fullActionStep
    (fullAction_circuit_refines_spec S D_bal hD_bal D_caps hD_caps LE_cell LE_null cN hN
      hLE_cell hLE_null CS hCSN hCSL hRestFrame hLogCS DBal hDBal DSide
      hDSide DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs DRevStep hDRevStep DLife hDLife DDC hDDC DCell hDCell DSC hDSC
      DAuth hDAuth DHeaps hDHeaps hRestBal hRestAccounts hRestSpawn hRestCaps hRestNull hRestCommitments
      hRestFactory hRestLifecycle hRestLifecycleDeathCert
      hRestDelegations hRestRevEpoch hRestCellHeaps hLog)
    (fun s a s' => fullActionStep_exec_iff s s' a) s acts s' hc

/-- **`fullAction_turn_conservation_descends`** — per-asset conservation when net ledger delta is zero. -/
theorem fullAction_turn_conservation_descends
    (S : Surface2)
    (D_bal : (CellId → AssetId → ℤ) → ℤ) (hD_bal : Function.Injective D_bal)
    (D_caps : Caps → ℤ) (hD_caps : Function.Injective D_caps)
    (LE_cell : CellId → ℤ) (LE_null : Nat → ℤ)
    (cN : List ℤ → ℤ) (hN : compressNInjective cN)
    (hLE_cell : listLeafInjective LE_cell) (hLE_null : listLeafInjective LE_null)
    (CS : CommitSurface)
    (hCSN : compressNInjective CS.compressN) (hCSL : cellLeafInjective CS.CH)
    (hRestFrame : RestHashIffFrame CS.RH) (hLogCS : logHashInjective CS.LH)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) × (CellId → Nat) → ℤ) (hDDgs : Function.Injective DDgs)
    (DRevStep : (CellId → Nat) × (CellId → List Cap) × (CellId → Nat) → ℤ)
    (hDRevStep : Function.Injective DRevStep)
    (DLife : (CellId → Nat) → ℤ) (hDLife : Function.Injective DLife)
    (DDC : (CellId → Nat) → ℤ) (hDDC : Function.Injective DDC)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth)
    (DHeaps : (CellId → Dregg2.Substrate.Heap.FeltHeap) → ℤ) (hDHeaps : Function.Injective DHeaps)
    (hRestBal : RestIffNoBal S.RH) (hRestAccounts : RestIffNoAccountsBalBorn S.RH)
    (hRestSpawn : RestIffNoSpawnTouched S.RH) (hRestCaps : RestIffNoCaps S.RH)
    (hRestNull : RestIffNoNullifiers S.RH)  (hRestCommitments : RestIffNoCommitments S.RH)
    (hRestFactory : RestIffNoFactoryTouched S.RH)
    (hRestLifecycle : RestIffNoLifecycle S.RH)
    (hRestLifecycleDeathCert : RestIffNoLifecycleDeathCert S.RH)
    (hRestDelegations : RestIffNoDelegations S.RH)
    (hRestRevEpoch : Dregg2.Circuit.Inst.RevokeDelegationFullA.RestIffNoCapsEpoch S.RH)
    (hRestCellHeaps : Dregg2.Circuit.Inst.HeapWriteA.RestIffNoCellHeaps S.RH)
    (hLog : logHashInjective S.LH)
    (s s' : RecChainedState) (acts : List FullActionA) (b : AssetId)
    (hc : turnCircuitStep (fullActionCircuitStepInst S D_bal hD_bal D_caps hD_caps LE_cell LE_null cN hN hLE_cell hLE_null CS DBal hDBal DSide hDSide DLeg
      hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs DRevStep hDRevStep DLife hDLife DDC hDDC DCell hDCell DSC hDSC DAuth hDAuth DHeaps hDHeaps)
      s acts s')
    (hzero : turnLedgerDeltaAsset acts b = 0) :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b :=
  turn_conservation_descends fullActionStep (fun s a s' => fullActionStep_exec_iff s s' a)
    s s' acts b
    (fullAction_turn_circuit_refines_spec S D_bal hD_bal D_caps hD_caps LE_cell LE_null
      cN hN hLE_cell hLE_null CS hCSN hCSL hRestFrame hLogCS DBal hDBal
      DSide hDSide DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs DRevStep hDRevStep DLife hDLife DDC hDDC DCell hDCell DSC
      hDSC DAuth hDAuth DHeaps hDHeaps hRestBal hRestAccounts hRestSpawn hRestCaps hRestNull hRestCommitments
      hRestFactory hRestLifecycle
      hRestLifecycleDeathCert hRestDelegations hRestRevEpoch hRestCellHeaps hLog s s' acts hc)
    hzero

/-! ## §3 — axiom-hygiene tripwires for the exerciseA tower.
The exerciseA inner-turn arm is a REAL composite circuit step; these pins certify the per-action
refinement and its mutual inner-fold helper rest on exactly `{propext, Classical.choice, Quot.sound}`.
A regression that re-introduces a hole into the exerciseA arm trips the build here. -/
#assert_axioms fullAction_circuit_refines_spec
#assert_axioms exerciseInnerFold_refines_turnSpec

end Dregg2.Circuit.TurnEffectRefinement