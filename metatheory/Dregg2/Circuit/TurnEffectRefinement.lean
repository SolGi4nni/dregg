/-
# Dregg2.Circuit.TurnEffectRefinement — full-action circuit dispatch + turn diamond.

Extends `TurnRefinement.lean`'s generic turn tower with a concrete `fullActionCircuitStep` that
case-splits `FullActionA` to the v2 effect `*CircuitStep` defs from `EffectRefinement.lean` where they
exist, and falls back to `fullActionStep` (declarative spec as circuit acceptance) for unmapped arms.
Composes with `turn_circuit_refines_spec_of_steps` / `turn_circuit_refines_exec_of_steps` /
`turn_conservation_descends` for the full turn diamond down to `execFullTurnA`.

No `sorry`/`admit`/`native_decide`/`axiom`.
-/
import Dregg2.Circuit.TurnRefinement
import Dregg2.Circuit.EffectRefinement
import Dregg2.Circuit.ActionDispatch
import Dregg2.Circuit.EffectCommit2
import Dregg2.Circuit.EffectCommit2Dual

set_option maxHeartbeats 800000

namespace Dregg2.Circuit.TurnEffectRefinement

open Dregg2.Circuit.Refinement (Refines StepRel)
open Dregg2.Circuit.ActionDispatch (fullActionStep fullActionStep_exec_iff turnSpec)
open Dregg2.Circuit.TurnRefinement
  (turnCircuitStep turnSpecStep turnExecStep
   turn_circuit_refines_spec_of_steps turn_circuit_refines_exec_of_steps
   turn_conservation_descends)
open Dregg2.Circuit.EffectRefinement
  (mintCircuitStep mint_circuit_refines_spec
   burnCircuitStep burn_circuit_refines_spec
   createCellCircuitStep createCell_circuit_refines_spec
   spawnCircuitStep spawn_circuit_refines_spec
   balanceACircuitStep balanceA_circuit_refines_spec
   delegateCircuitStep delegate_circuit_refines_spec
   noteSpendCircuitStep noteSpend_circuit_refines_spec
   createEscrowCircuitStep createEscrow_circuit_refines_spec)
open Dregg2.Circuit.StateCommit (logHashInjective compressNInjective)
open Dregg2.Circuit.EffectCommit2 (Surface2 RestIffNoBal RestIffNoNullifiers)
open Dregg2.Circuit.EffectCommit2Dual (RestIffNoBalEscrows)
open Dregg2.Circuit.ListCommit (listLeafInjective)
open Dregg2.Circuit.BornEmptyCommit
open Dregg2.Circuit.Inst.Delegate (RestIffNoCaps)
open Dregg2.Circuit.Inst.CreateCellA (RestIffNoAccountsBalBorn)
open Dregg2.Circuit.Inst.SpawnA (RestIffNoSpawnTouched)
open Dregg2.Circuit.Inst.MintA (MintArgs)
open Dregg2.Circuit.Inst.BurnA (BurnArgs)
open Dregg2.Circuit.Inst.BalanceA (BalanceArgs)
open Dregg2.Circuit.Inst.Delegate (DelegateArgs)
open Dregg2.Circuit.Inst.CreateCellA (CreateCellArgs)
open Dregg2.Circuit.Inst.SpawnA (SpawnArgs)
open Dregg2.Circuit.Inst.NoteSpendA (NoteSpendArgs)
open Dregg2.Circuit.Inst.CreateEscrowA (CreateEscrowArgs)
open Dregg2.Authority
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

/-! ## §1 — `fullActionCircuitStep` (per-effect circuit dispatch). -/

/-- **`fullActionCircuitStep`** — dispatches each `FullActionA` constructor to its v2 effect
`CircuitStep` when available; unmapped arms fall back to `fullActionStep` (spec-as-circuit). -/
def fullActionCircuitStep
    (S : Surface2)
    (D_bal : (CellId → AssetId → ℤ) → ℤ) (hD_bal : Function.Injective D_bal)
    (D_caps : Caps → ℤ) (hD_caps : Function.Injective D_caps)
    (LE_cell : CellId → ℤ) (LE_null : Nat → ℤ) (LE_escrow : EscrowRecord → ℤ)
    (cN : List ℤ → ℤ) (hN : compressNInjective cN)
    (hLE_cell : listLeafInjective LE_cell) (hLE_null : listLeafInjective LE_null)
    (hLE_escrow : listLeafInjective LE_escrow)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)
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
  | .validateHandoffA intro rec t =>
      delegateCircuitStep S D_caps hD_caps st ⟨intro, rec, t⟩ st'
  | .createCellA actor newCell =>
      createCellCircuitStep S LE_cell cN hN hLE_cell DBal hDBal DSide hDSide st ⟨actor, newCell⟩ st'
  | .spawnA actor child target =>
      spawnCircuitStep S LE_cell cN hN hLE_cell DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs
        st ⟨actor, child, target⟩ st'
  | .bridgeMintA actor cell a value =>
      mintCircuitStep S D_bal hD_bal st ⟨actor, cell, a, value⟩ st'
  | .createEscrowA id actor creator recipient asset amount =>
      createEscrowCircuitStep S D_bal hD_bal LE_escrow cN hN hLE_escrow
        st ⟨id, actor, creator, recipient, asset, amount⟩ st'
  | .noteSpendA nf actor =>
      noteSpendCircuitStep S LE_null cN hN hLE_null st ⟨nf, actor⟩ st'
  | fa' =>
      fullActionStep st fa' st'

/-- Encoder-instantiated circuit step (abbrev keeps turn-level statement types small). -/
abbrev fullActionCircuitStepInst
    (S : Surface2)
    (D_bal : (CellId → AssetId → ℤ) → ℤ) (hD_bal : Function.Injective D_bal)
    (D_caps : Caps → ℤ) (hD_caps : Function.Injective D_caps)
    (LE_cell : CellId → ℤ) (LE_null : Nat → ℤ) (LE_escrow : EscrowRecord → ℤ)
    (cN : List ℤ → ℤ) (hN : compressNInjective cN)
    (hLE_cell : listLeafInjective LE_cell) (hLE_null : listLeafInjective LE_null)
    (hLE_escrow : listLeafInjective LE_escrow)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs) :
    StepRel RecChainedState FullActionA RecChainedState :=
  fullActionCircuitStep S D_bal hD_bal D_caps hD_caps LE_cell LE_null LE_escrow cN hN hLE_cell hLE_null
    hLE_escrow DBal hDBal DSide hDSide DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs

/-- **`fullAction_circuit_refines_spec`** — per-action SOUNDNESS: circuit ⊑ `fullActionStep`. -/
theorem fullAction_circuit_refines_spec
    (S : Surface2)
    (D_bal : (CellId → AssetId → ℤ) → ℤ) (hD_bal : Function.Injective D_bal)
    (D_caps : Caps → ℤ) (hD_caps : Function.Injective D_caps)
    (LE_cell : CellId → ℤ) (LE_null : Nat → ℤ) (LE_escrow : EscrowRecord → ℤ)
    (cN : List ℤ → ℤ) (hN : compressNInjective cN)
    (hLE_cell : listLeafInjective LE_cell) (hLE_null : listLeafInjective LE_null)
    (hLE_escrow : listLeafInjective LE_escrow)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)
    (hRestBal : RestIffNoBal S.RH) (hRestAccounts : RestIffNoAccountsBalBorn S.RH)
    (hRestSpawn : RestIffNoSpawnTouched S.RH) (hRestCaps : RestIffNoCaps S.RH)
    (hRestNull : RestIffNoNullifiers S.RH) (hRestEscrow : RestIffNoBalEscrows S.RH)
    (hLog : logHashInjective S.LH) :
    Refines (fullActionCircuitStepInst S D_bal hD_bal D_caps hD_caps LE_cell LE_null LE_escrow cN hN
      hLE_cell hLE_null hLE_escrow DBal hDBal DSide hDSide DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs)
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
  | .validateHandoffA intro rec t =>
      simp only [fullActionStep]
      exact delegate_circuit_refines_spec S D_caps hD_caps hRestCaps hLog st _ st' h
  | .createCellA actor newCell =>
      simp only [fullActionStep]
      exact createCell_circuit_refines_spec S LE_cell cN hN hLE_cell DBal hDBal DSide hDSide hRestAccounts hLog
        st _ st' h
  | .spawnA actor child target =>
      simp only [fullActionStep]
      exact spawn_circuit_refines_spec S LE_cell cN hN hLE_cell DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs
        hRestSpawn hLog st _ st' h
  | .bridgeMintA actor cell a value =>
      simp only [fullActionStep]
      exact mint_circuit_refines_spec S D_bal hD_bal hRestBal hLog st _ st' h
  | .createEscrowA id actor creator recipient asset amount =>
      simp only [fullActionStep]
      exact createEscrow_circuit_refines_spec S D_bal hD_bal LE_escrow cN hN hLE_escrow hRestEscrow hLog
        st _ st' h
  | .noteSpendA nf actor =>
      simp only [fullActionStep]
      exact noteSpend_circuit_refines_spec S LE_null cN hN hLE_null hRestNull hLog st _ st' h
  | .revoke holder t => simp only [fullActionStep]; exact h
  | .setFieldA actor cell f v => simp only [fullActionStep]; exact h
  | .emitEventA actor cell topic data => simp only [fullActionStep]; exact h
  | .incrementNonceA actor cell n => simp only [fullActionStep]; exact h
  | .setPermissionsA actor cell p => simp only [fullActionStep]; exact h
  | .setVKA actor cell vk => simp only [fullActionStep]; exact h
  | .delegateAttenA del rec t keep => simp only [fullActionStep]; exact h
  | .attenuateA actor idx keep => simp only [fullActionStep]; exact h
  | .dropRefA holder t => simp only [fullActionStep]; exact h
  | .revokeDelegationA holder t => simp only [fullActionStep]; exact h
  | .exerciseA actor target inner => simp only [fullActionStep]; exact h
  | .createCellFromFactoryA actor newCell vk => simp only [fullActionStep]; exact h
  | .releaseEscrowA id actor => simp only [fullActionStep]; exact h
  | .refundEscrowA id actor => simp only [fullActionStep]; exact h
  | .createObligationA id actor obligor beneficiary asset stake => simp only [fullActionStep]; exact h
  | .fulfillObligationA id actor => simp only [fullActionStep]; exact h
  | .slashObligationA id actor => simp only [fullActionStep]; exact h
  | .noteCreateA cm actor => simp only [fullActionStep]; exact h
  | .createCommittedEscrowA id actor creator recipient asset amount hidingProof =>
      simp only [fullActionStep]; exact h
  | .releaseCommittedEscrowA id actor => simp only [fullActionStep]; exact h
  | .refundCommittedEscrowA id actor => simp only [fullActionStep]; exact h
  | .bridgeLockA id actor originator destination asset amount => simp only [fullActionStep]; exact h
  | .bridgeFinalizeA id actor asset amount => simp only [fullActionStep]; exact h
  | .bridgeCancelA id actor => simp only [fullActionStep]; exact h
  | .sealA pid actor payload => simp only [fullActionStep]; exact h
  | .unsealA pid actor recipient => simp only [fullActionStep]; exact h
  | .createSealPairA pid actor sealerHolder unsealerHolder => simp only [fullActionStep]; exact h
  | .makeSovereignA actor cell => simp only [fullActionStep]; exact h
  | .refusalA actor cell => simp only [fullActionStep]; exact h
  | .receiptArchiveA actor cell => simp only [fullActionStep]; exact h
  | .queueAllocateA id actor cell cap => simp only [fullActionStep]; exact h
  | .queueEnqueueA id m actor cell depId dAsset deposit => simp only [fullActionStep]; exact h
  | .queueDequeueA id actor cell depId deposit => simp only [fullActionStep]; exact h
  | .queueResizeA id newCap actor cell => simp only [fullActionStep]; exact h
  | .queueAtomicTxA actor ops => simp only [fullActionStep]; exact h
  | .queuePipelineStepA srcId owner sinkCells sinkIds => simp only [fullActionStep]; exact h
  | .pipelinedSendA actor => simp only [fullActionStep]; exact h
  | .exportSturdyRefA sw actor exporter target rights => simp only [fullActionStep]; exact h
  | .enlivenRefA sw actor exporter claimed => simp only [fullActionStep]; exact h
  | .swissHandoffA sw certHash introducer exporter => simp only [fullActionStep]; exact h
  | .swissDropA sw actor exporter => simp only [fullActionStep]; exact h
  | .cellSealA actor cell => simp only [fullActionStep]; exact h
  | .cellUnsealA actor cell => simp only [fullActionStep]; exact h
  | .cellDestroyA actor cell certHash => simp only [fullActionStep]; exact h
  | .refreshDelegationA actor child => simp only [fullActionStep]; exact h

/-! ## §2 — Turn-level diamond (compose generic `TurnRefinement` lemmas). -/

/-- **`fullAction_turn_circuit_refines_spec`** — turn circuit ⊑ `turnSpec fullActionStep`. -/
theorem fullAction_turn_circuit_refines_spec
    (S : Surface2)
    (D_bal : (CellId → AssetId → ℤ) → ℤ) (hD_bal : Function.Injective D_bal)
    (D_caps : Caps → ℤ) (hD_caps : Function.Injective D_caps)
    (LE_cell : CellId → ℤ) (LE_null : Nat → ℤ) (LE_escrow : EscrowRecord → ℤ)
    (cN : List ℤ → ℤ) (hN : compressNInjective cN)
    (hLE_cell : listLeafInjective LE_cell) (hLE_null : listLeafInjective LE_null)
    (hLE_escrow : listLeafInjective LE_escrow)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)
    (hRestBal : RestIffNoBal S.RH) (hRestAccounts : RestIffNoAccountsBalBorn S.RH)
    (hRestSpawn : RestIffNoSpawnTouched S.RH) (hRestCaps : RestIffNoCaps S.RH)
    (hRestNull : RestIffNoNullifiers S.RH) (hRestEscrow : RestIffNoBalEscrows S.RH)
    (hLog : logHashInjective S.LH)
    (s s' : RecChainedState) (acts : List FullActionA)
    (hc : turnCircuitStep (fullActionCircuitStepInst S D_bal hD_bal D_caps hD_caps LE_cell LE_null LE_escrow
      cN hN hLE_cell hLE_null hLE_escrow DBal hDBal DSide hDSide DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs)
      s acts s') :
    Spec.Turn.turnSpec fullActionStep s acts s' :=
  turn_circuit_refines_spec_of_steps
    (fullActionCircuitStepInst S D_bal hD_bal D_caps hD_caps LE_cell LE_null LE_escrow cN hN hLE_cell hLE_null
      hLE_escrow DBal hDBal DSide hDSide DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs)
    fullActionStep
    (fullAction_circuit_refines_spec S D_bal hD_bal D_caps hD_caps LE_cell LE_null LE_escrow cN hN hLE_cell
      hLE_null hLE_escrow DBal hDBal DSide hDSide DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs hRestBal
      hRestAccounts hRestSpawn hRestCaps hRestNull hRestEscrow hLog)
    s acts s' hc

/-- **`fullAction_turn_circuit_refines_exec`** — full diamond: turn circuit ⊑ `execFullTurnA`. -/
theorem fullAction_turn_circuit_refines_exec
    (S : Surface2)
    (D_bal : (CellId → AssetId → ℤ) → ℤ) (hD_bal : Function.Injective D_bal)
    (D_caps : Caps → ℤ) (hD_caps : Function.Injective D_caps)
    (LE_cell : CellId → ℤ) (LE_null : Nat → ℤ) (LE_escrow : EscrowRecord → ℤ)
    (cN : List ℤ → ℤ) (hN : compressNInjective cN)
    (hLE_cell : listLeafInjective LE_cell) (hLE_null : listLeafInjective LE_null)
    (hLE_escrow : listLeafInjective LE_escrow)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)
    (hRestBal : RestIffNoBal S.RH) (hRestAccounts : RestIffNoAccountsBalBorn S.RH)
    (hRestSpawn : RestIffNoSpawnTouched S.RH) (hRestCaps : RestIffNoCaps S.RH)
    (hRestNull : RestIffNoNullifiers S.RH) (hRestEscrow : RestIffNoBalEscrows S.RH)
    (hLog : logHashInjective S.LH)
    (s s' : RecChainedState) (acts : List FullActionA)
    (hc : turnCircuitStep (fullActionCircuitStepInst S D_bal hD_bal D_caps hD_caps LE_cell LE_null LE_escrow
      cN hN hLE_cell hLE_null hLE_escrow DBal hDBal DSide hDSide DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs)
      s acts s') :
    execFullTurnA s acts = some s' :=
  turn_circuit_refines_exec_of_steps
    (fullActionCircuitStepInst S D_bal hD_bal D_caps hD_caps LE_cell LE_null LE_escrow cN hN hLE_cell hLE_null
      hLE_escrow DBal hDBal DSide hDSide DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs)
    fullActionStep
    (fullAction_circuit_refines_spec S D_bal hD_bal D_caps hD_caps LE_cell LE_null LE_escrow cN hN hLE_cell
      hLE_null hLE_escrow DBal hDBal DSide hDSide DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs hRestBal
      hRestAccounts hRestSpawn hRestCaps hRestNull hRestEscrow hLog)
    (fun s a s' => fullActionStep_exec_iff s s' a) s acts s' hc

/-- **`fullAction_turn_conservation_descends`** — per-asset conservation when net ledger delta is zero. -/
theorem fullAction_turn_conservation_descends
    (S : Surface2)
    (D_bal : (CellId → AssetId → ℤ) → ℤ) (hD_bal : Function.Injective D_bal)
    (D_caps : Caps → ℤ) (hD_caps : Function.Injective D_caps)
    (LE_cell : CellId → ℤ) (LE_null : Nat → ℤ) (LE_escrow : EscrowRecord → ℤ)
    (cN : List ℤ → ℤ) (hN : compressNInjective cN)
    (hLE_cell : listLeafInjective LE_cell) (hLE_null : listLeafInjective LE_null)
    (hLE_escrow : listLeafInjective LE_escrow)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)
    (hRestBal : RestIffNoBal S.RH) (hRestAccounts : RestIffNoAccountsBalBorn S.RH)
    (hRestSpawn : RestIffNoSpawnTouched S.RH) (hRestCaps : RestIffNoCaps S.RH)
    (hRestNull : RestIffNoNullifiers S.RH) (hRestEscrow : RestIffNoBalEscrows S.RH)
    (hLog : logHashInjective S.LH)
    (s s' : RecChainedState) (acts : List FullActionA) (b : AssetId)
    (hc : turnCircuitStep (fullActionCircuitStepInst S D_bal hD_bal D_caps hD_caps LE_cell LE_null LE_escrow
      cN hN hLE_cell hLE_null hLE_escrow DBal hDBal DSide hDSide DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs)
      s acts s')
    (hzero : turnLedgerDeltaAsset acts b = 0) :
    recTotalAssetWithEscrow s'.kernel b = recTotalAssetWithEscrow s.kernel b :=
  turn_conservation_descends fullActionStep (fun s a s' => fullActionStep_exec_iff s s' a)
    s s' acts b
    (fullAction_turn_circuit_refines_spec S D_bal hD_bal D_caps hD_caps LE_cell LE_null LE_escrow cN hN
      hLE_cell hLE_null hLE_escrow DBal hDBal DSide hDSide DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs
      hRestBal hRestAccounts hRestSpawn hRestCaps hRestNull hRestEscrow hLog s s' acts hc)
    hzero

#assert_axioms fullAction_circuit_refines_spec
#assert_axioms fullAction_turn_circuit_refines_spec
#assert_axioms fullAction_turn_circuit_refines_exec
#assert_axioms fullAction_turn_conservation_descends

end Dregg2.Circuit.TurnEffectRefinement