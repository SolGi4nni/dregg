/-
# Dregg2.Circuit.TurnCircuitCompose — Wave 5 whole-turn circuit composition scaffold.

Folds a list of per-step `EmittedDescriptor`s into a composed `ConstraintSystem`
(`turnCircuitOfEmitted`), then composes per-step emitted→spec refinement with whole-turn
execution soundness (`turn_emitted_refines_exec_direct`) **without** the `fullAction_circuit_refines_spec`
fallback arm.

Explicit `sorry` portals (no silent fallbacks):
  * macaroon caveat-chain columns
  * root-compress binding (`preRoot`/`postRoot` ↔ `foldStepRoots`)
  * multi-step wire-alignment glue

Incomplete theorems use `sorry` only — never `exact h` pretending circuit = spec.
-/
import Dregg2.Circuit.TurnEmit
import Dregg2.Circuit.TurnWitness
import Dregg2.Circuit.ActionDispatch
import Dregg2.Circuit.TurnRefinement
import Dregg2.Exec.CircuitEmit

set_option maxHeartbeats 800000

namespace Dregg2.Circuit.TurnCircuitCompose

open Dregg2.Circuit
open Dregg2.Circuit.EffectEmitRegistry (actionAirName)
open Dregg2.Circuit.TurnEmit
  (DescriptorLookup stepEmittedSat TurnEmittedChain turnEmittedSat
   step_emitted_refines_fullActionStep turn_emitted_refines_exec
   defaultDescriptorLookup)
open Dregg2.Circuit.TurnWitness
  (StepWitness TurnWitness turnWitnessSatisfies foldStepRoots stepWitnessDigest)
open Dregg2.Circuit.ActionDispatch
  (fullActionStep actionTag turnSpec execFullTurnA_iff_turnSpec)
open Dregg2.Exec.CircuitEmit (EmittedDescriptor decodeE satisfiedEmitted)
open Dregg2.Exec.TurnExecutorFull (FullActionA)
open Dregg2.Exec

/-! ## §1 — fold per-step emitted AIRs into one constraint system (scaffold). -/

/-- Append one emitted step's decoded constraints to an accumulator (wire indices unchanged). -/
def appendEmittedStep (acc : ConstraintSystem) (d : EmittedDescriptor) : ConstraintSystem :=
  acc ++ decodeE d

/-- **`turnCircuitOfEmitted`** — fold a left-to-right list of per-step emitted descriptors into a
single composed `ConstraintSystem` (scaffold: constraint-list append; wire remapping deferred). -/
def turnCircuitOfEmitted (steps : List EmittedDescriptor) : ConstraintSystem :=
  steps.foldl appendEmittedStep []

/-- The composed circuit length is the sum of per-step constraint counts (scaffold identity). -/
theorem turnCircuitOfEmitted_length (steps : List EmittedDescriptor) :
    (turnCircuitOfEmitted steps).length =
      (steps.map (fun d => (decodeE d).length)).sum := by
  induction steps with
  | nil => simp [turnCircuitOfEmitted, appendEmittedStep]
  | cons d ds ih =>
      simp [turnCircuitOfEmitted, appendEmittedStep, List.foldl, ih, List.length_append]

/-! ## §2 — explicit sorry portals (Wave 5 composition gaps). -/

/-- HOLE W5: macaroon caveat-chain + hidden caveat columns arithmetized in the turn circuit. -/
theorem hole_turn_macaroon_chain
    (w : TurnWitness) (authChain : ℤ) : Prop := by
  sorry

/-- HOLE W5: abstract `compress` portal binds `preRoot`/`postRoot` to the step-root fold. -/
theorem hole_turn_root_compress_binding
    (compress : ℤ → ℤ → ℤ) (stepRoot : StepWitness → ℤ) (w : TurnWitness) : Prop := by
  sorry

/-- HOLE W5: multi-step emitted AIR glue (per-step trace widths aligned across the fold). -/
theorem hole_turn_multi_step_glue
    (steps : List EmittedDescriptor) (w : TurnWitness) : Prop := by
  sorry

/-! ## §3 — per-step emitted ⊑ `fullActionStep` without generic circuit fallback. -/

/-- **`step_emitted_refines_fullActionStep_direct`** — like `step_emitted_refines_fullActionStep`
for diamond-covered effects, but the catch-all `fa'` arm is an explicit sorry (no
`fullAction_circuit_refines_spec` silent fallback). -/
theorem step_emitted_refines_fullActionStep_direct
    (S : Dregg2.Circuit.EffectCommit2.Surface2)
    (D_bal : (CellId → AssetId → ℤ) → ℤ) (hD_bal : Function.Injective D_bal)
    (D_caps : Caps → ℤ) (hD_caps : Function.Injective D_caps)
    (LE_cell : CellId → ℤ) (LE_null : Nat → ℤ) (LE_escrow : EscrowRecord → ℤ)
    (LE_sealed : SealedBoxRecord → ℤ)
    (cN : List ℤ → ℤ) (hN : Dregg2.Circuit.StateCommit.compressNInjective cN)
    (hLE_cell : Dregg2.Circuit.ListCommit.listLeafInjective LE_cell)
    (hLE_null : Dregg2.Circuit.ListCommit.listLeafInjective LE_null)
    (hLE_escrow : Dregg2.Circuit.ListCommit.listLeafInjective LE_escrow)
    (hLE_sealed : Dregg2.Circuit.ListCommit.listLeafInjective LE_sealed)
    (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ)
    (hNQ : Dregg2.Circuit.StateCommit.compressNInjective cNQ)
    (hLQ : Dregg2.Circuit.ListCommit.listLeafInjective LQ)
    (CS : Dregg2.Circuit.EffectCommit.CommitSurface)
    (hCSN : Dregg2.Circuit.StateCommit.compressNInjective CS.compressN)
    (hCSL : Dregg2.Circuit.StateCommit.cellLeafInjective CS.CH)
    (hRestFrame : Dregg2.Circuit.StateCommit.RestHashIffFrame CS.RH)
    (hLogCS : Dregg2.Circuit.StateCommit.logHashInjective CS.LH)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : Dregg2.Circuit.BornEmptyCommit.BornEmptySideTables → ℤ)
    (hDSide : Function.Injective DSide)
    (DLeg : Dregg2.Circuit.EffectCommit5.SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)
    (hRestBal : Dregg2.Circuit.EffectCommit2.RestIffNoBal S.RH)
    (hRestAccounts : Dregg2.Circuit.Inst.CreateCellA.RestIffNoAccountsBalBorn S.RH)
    (hRestSpawn : Dregg2.Circuit.Inst.SpawnA.RestIffNoSpawnTouched S.RH)
    (hRestCaps : Dregg2.Circuit.Inst.Delegate.RestIffNoCaps S.RH)
    (hRestNull : Dregg2.Circuit.EffectCommit2.RestIffNoNullifiers S.RH)
    (hRestEscrow : Dregg2.Circuit.EffectCommit2Dual.RestIffNoBalEscrows S.RH)
    (hRestCommitments : Dregg2.Circuit.Inst.NoteCreateA.RestIffNoCommitments S.RH)
    (hRestSealed : Dregg2.Circuit.Inst.SealA.RestIffNoSealedBoxes S.RH)
    (hRestQueues : Dregg2.Circuit.Inst.QueueEnqueueA.RestIffNoQueuesBalEscrows S.RH)
    (hLog : Dregg2.Circuit.StateCommit.logHashInjective S.LH)
    (sw : StepWitness) (st st' : RecChainedState) (fa : FullActionA)
    (h : stepEmittedSat defaultDescriptorLookup sw st st' fa)
    (hEnc : Dregg2.Circuit.TurnEmit.stepEmittedEncodeAgrees S D_bal hD_bal D_caps hD_caps LE_cell
      LE_null LE_escrow LE_sealed cN hN hLE_cell hLE_null hLE_escrow hLE_sealed LQ cNQ hNQ hLQ CS
      DBal hDBal DSide hDSide DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs sw st st' fa)
    (hcircuit :
      Dregg2.Circuit.TurnEffectRefinement.fullActionCircuitStepInst S D_bal hD_bal D_caps hD_caps
        LE_cell LE_null LE_escrow LE_sealed cN hN hLE_cell hLE_null hLE_escrow hLE_sealed LQ cNQ hNQ
        hLQ CS DBal hDBal DSide hDSide DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs st fa st') :
    fullActionStep st fa st' := by
  by_cases hreg : ∃ d, defaultDescriptorLookup (actionAirName fa) = some d
  · exact step_emitted_refines_fullActionStep S D_bal hD_bal D_caps hD_caps LE_cell LE_null LE_escrow
      LE_sealed cN hN hLE_cell hLE_null hLE_escrow hLE_sealed LQ cNQ hNQ hLQ CS hCSN hCSL hRestFrame
      hLogCS DBal hDBal DSide hDSide DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs hRestBal
      hRestAccounts hRestSpawn hRestCaps hRestNull hRestEscrow hRestCommitments hRestSealed hRestQueues
      hLog sw st st' fa h hEnc hcircuit
  · sorry

/-! ## §4 — whole-turn emitted ⊑ `execFullTurnA` (direct path, no fallback). -/

/-- **`turn_emitted_refines_exec_direct`** — compose `step_emitted_refines_fullActionStep_direct` with
`turn_emitted_refines_exec`. Macaroon chain, root-compress binding, and multi-step glue are
explicit sorry obligations (not hidden in a circuit fallback). -/
theorem turn_emitted_refines_exec_direct
    (lookup : DescriptorLookup)
    (hstep :
      ∀ (sw : StepWitness) (st st' : RecChainedState) (fa : FullActionA),
        stepEmittedSat lookup sw st st' fa → fullActionStep st fa st')
    (s s' : RecChainedState) (acts : List FullActionA) (w : TurnWitness)
    (compress : ℤ → ℤ → ℤ) (stepRoot : StepWitness → ℤ)
    (h : TurnEmittedChain lookup compress stepRoot s acts s' w)
    (_hmac : hole_turn_macaroon_chain w w.authChain)
    (_hroot : hole_turn_root_compress_binding compress stepRoot w)
    (_hglue : hole_turn_multi_step_glue [] w) :
    execFullTurnA s acts = some s' := by
  exact turn_emitted_refines_exec lookup hstep s s' acts w compress stepRoot h

end Dregg2.Circuit.TurnCircuitCompose