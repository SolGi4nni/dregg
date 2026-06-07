/-
# Dregg2.Circuit.EffectRefinement — the v2 effect diamond: circuit ⟺ spec ⟺ executor.

Extends `Refinement.lean`'s tower to v2 single-component effects. The generic layer proves
`effect2CircuitStep ⟺ apex` and `emitted ⟺ circuit` for ANY `EffectSpec2`; concrete instances
(mint, burn, …) compose with their executor⟺spec bridges for the full diamond down to `execFullA`
and the Plonky3 wire bytes.

No `sorry`/`admit`/`native_decide`/`axiom`.
-/
import Dregg2.Circuit.Refinement
import Dregg2.Circuit.EffectCommit2
import Dregg2.Circuit.EffectCommit3
import Dregg2.Circuit.EffectCommit5
import Dregg2.Circuit.BornEmptyCommit
import Dregg2.Circuit.ListCommit
import Dregg2.Circuit.EffectCommit2Dual
import Dregg2.Circuit.Inst.mintA
import Dregg2.Circuit.Inst.burnA
import Dregg2.Circuit.Inst.transfer
import Dregg2.Circuit.Inst.balanceA
import Dregg2.Circuit.Inst.delegate
import Dregg2.Circuit.Inst.noteSpendA
import Dregg2.Circuit.Inst.createEscrowA
import Dregg2.Circuit.Inst.createCellA
import Dregg2.Circuit.Inst.spawnA
import Dregg2.Circuit.Inst.noteCreateA
import Dregg2.Circuit.Inst.releaseEscrowA
import Dregg2.Circuit.Inst.refundEscrowA
import Dregg2.Circuit.Inst.revoke
import Dregg2.Circuit.Inst.sealA
import Dregg2.Circuit.Inst.bridgeLockA
import Dregg2.Circuit.Inst.queueEnqueueA
import Dregg2.Circuit.EffectCommit
import Dregg2.Circuit.EffectInstances
import Dregg2.Circuit.Inst.exerciseA
import Dregg2.Circuit.Spec.exercise

namespace Dregg2.Circuit.EffectRefinement

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.EffectCommit3
open Dregg2.Circuit.EffectCommit5
open Dregg2.Authority
open Dregg2.Circuit.BornEmptyCommit
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Refinement (Refines Equiv StepRel)
open Dregg2.Circuit.EffectCommit2Dual
open Dregg2.Circuit.Inst.MintA
open Dregg2.Circuit.Inst.BurnA
open Dregg2.Circuit.Inst.Delegate
open Dregg2.Circuit.Inst.NoteSpendA
open Dregg2.Circuit.Inst.CreateEscrowA
open Dregg2.Circuit.Inst.CreateCellA
open Dregg2.Circuit.Inst.SpawnA
open Dregg2.Circuit.Inst.NoteCreateA
open Dregg2.Circuit.Inst.ReleaseEscrowA
open Dregg2.Circuit.Inst.RefundEscrowA
open Dregg2.Circuit.Inst.Revoke
open Dregg2.Circuit.Inst.SealA
open Dregg2.Circuit.Inst.BridgeLockA
open Dregg2.Circuit.Inst.QueueEnqueueA
open Dregg2.Circuit.EffectCommit
open Dregg2.Circuit.EffectInstances
open Dregg2.Circuit.Inst.ExerciseA
open Dregg2.Circuit.Spec.Exercise
open Dregg2.Circuit.ActionDispatch
open Dregg2.Circuit.Spec.SupplyCreation
open Dregg2.Circuit.Spec.SupplyDestruction
open Dregg2.Circuit.Spec.AccountGrowth
open Dregg2.Circuit.Spec.BalanceMovement
open Dregg2.Circuit.Spec.AuthorityUnattenuated
open Dregg2.Circuit.Spec.NoteNullifier
open Dregg2.Circuit.Spec.EscrowHoldingCreate
open Dregg2.Circuit.Spec.NoteCommitment
open Dregg2.Circuit.Spec.EscrowHoldingRelease
open Dregg2.Circuit.Spec.EscrowHoldingRefund
open Dregg2.Circuit.Spec.AuthorityRevocation
open Dregg2.Circuit.Spec.SealBoxOperations
open Dregg2.Circuit.Spec.BridgeOutboundLock
open Dregg2.Circuit.Spec.QueueFifoCore
open Dregg2.Circuit.Spec.CellStateField
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit
open Dregg2.Exec.TurnExecutorFull

/-! ## §1 — Generic v2 refinement (any `EffectSpec2`). -/

section GenericEffect2
variable {St Args : Type}
variable (S : Surface2) (E : EffectSpec2 St Args)

/-- The CIRCUIT step: full-state v2 arithmetization satisfied on the encoded triple. -/
abbrev effect2CircuitStep : StepRel St Args St :=
  fun pre args post => satisfiedE2 S E (encodeE2 S E pre args post)

/-- The APEX step: the framework's derived full-state declarative spec. -/
abbrev effect2ApexStep : StepRel St Args St :=
  fun pre args post => E.apex pre args post

/-- The EMITTED step: the polynomial gates the Rust prover checks. -/
abbrev effect2EmittedStep (name : String) : StepRel St Args St :=
  fun pre args post =>
    satisfiedEmitted (emittedEffect2 name E) (encodeE2 S E pre args post)

/-- **`effect2_circuit_refines_apex`** — SOUNDNESS: circuit ⊑ apex. -/
theorem effect2_circuit_refines_apex
    (hRestF : RestFrameDecodes2 S E) (hLog : logHashInjective S.LH) (hGuard : GuardDecodes2 E)
    (pre : St) (args : Args) (post : St) (h : effect2CircuitStep S E pre args post) :
    effect2ApexStep E pre args post :=
  effect2_circuit_full_sound S E hRestF hLog hGuard pre args post h

/-- **`effect2_apex_refines_circuit`** — COMPLETENESS: apex ⊑ circuit. -/
theorem effect2_apex_refines_circuit
    (hRestE : RestFrameEncodes2 S E) (hGuardE : GuardEncodes2 E)
    (pre : St) (args : Args) (post : St) (h : effect2ApexStep E pre args post) :
    effect2CircuitStep S E pre args post :=
  effect2_circuit_full_complete S E hRestE hGuardE pre args post h

/-- **`effect2_circuit_equiv_apex`** — mutual refinement on the algebraic layer. -/
theorem effect2_circuit_equiv_apex
    (hRestF : RestFrameDecodes2 S E) (hLog : logHashInjective S.LH) (hGuard : GuardDecodes2 E)
    (hRestE : RestFrameEncodes2 S E) (hGuardE : GuardEncodes2 E) :
    Equiv (effect2CircuitStep S E) (effect2ApexStep E) :=
  fun pre args post =>
    ⟨effect2_circuit_refines_apex S E hRestF hLog hGuard pre args post,
     effect2_apex_refines_circuit S E hRestE hGuardE pre args post⟩

/-- **`effect2_emitted_equiv_circuit`** — emitted wire form ⟺ algebraic circuit. -/
theorem effect2_emitted_equiv_circuit (name : String) (pre : St) (args : Args) (post : St) :
    effect2EmittedStep S E name pre args post ↔ effect2CircuitStep S E pre args post :=
  (emitEffect2Faithful name E (encodeE2 S E pre args post)).symm

/-- **`effect2_emitted_refines_apex`** — the Plonky3 layer refines to the apex spec. -/
theorem effect2_emitted_refines_apex
    (name : String) (hRestF : RestFrameDecodes2 S E) (hLog : logHashInjective S.LH)
    (hGuard : GuardDecodes2 E) (pre : St) (args : Args) (post : St)
    (h : effect2EmittedStep S E name pre args post) :
    effect2ApexStep E pre args post :=
  effect2_circuit_refines_apex S E hRestF hLog hGuard pre args post
    ((effect2_emitted_equiv_circuit S E name pre args post).mp h)

#assert_axioms effect2_circuit_refines_apex
#assert_axioms effect2_apex_refines_circuit
#assert_axioms effect2_circuit_equiv_apex
#assert_axioms effect2_emitted_equiv_circuit
#assert_axioms effect2_emitted_refines_apex

end GenericEffect2

/-! ## §2 — MintA diamond (circuit ⟺ MintASpec ⟺ execFullA ⟺ emitted). -/

def mintExecStep (s : RecChainedState) (args : MintArgs) (s' : RecChainedState) : Prop :=
  execFullA s (.mintA args.actor args.cell args.a args.amt) = some s'

def mintSpecStep (s : RecChainedState) (args : MintArgs) (s' : RecChainedState) : Prop :=
  MintASpec s args.actor args.cell args.a args.amt s'

def mintCircuitStep (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : MintArgs) (s' : RecChainedState) : Prop :=
  effect2CircuitStep S (mintE D hD) s args s'

def mintEmittedStep (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : MintArgs) (s' : RecChainedState) : Prop :=
  effect2EmittedStep S (mintE D hD) mintAirName s args s'

theorem mintRestFrameEncodes (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) :
    RestFrameEncodes2 S (mintE D hD) :=
  fun k k' hframe => (hRest k k').mpr hframe

theorem mint_exec_equiv_spec (s : RecChainedState) (args : MintArgs) (s' : RecChainedState) :
    mintExecStep s args s' ↔ mintSpecStep s args s' :=
  execMintA_iff_spec s args.actor args.cell args.a args.amt s'

theorem mint_circuit_refines_spec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : MintArgs) (s' : RecChainedState)
    (h : mintCircuitStep S D hD s args s') :
    mintSpecStep s args s' :=
  mintA_full_sound S D hD hRest hLog s args s' h

theorem mint_spec_refines_circuit (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH)
    (s : RecChainedState) (args : MintArgs) (s' : RecChainedState)
    (h : mintSpecStep s args s') :
    mintCircuitStep S D hD s args s' :=
  effect2_apex_refines_circuit S (mintE D hD)
    (mintRestFrameEncodes S D hD hRest) (mintGuardEncodes D hD) s args s'
    ((apex_iff_mintASpec D hD s args s').mpr h)

theorem mint_circuit_refines_exec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : MintArgs) (s' : RecChainedState)
    (h : mintCircuitStep S D hD s args s') :
    mintExecStep s args s' :=
  (mint_exec_equiv_spec s args s').mpr
    (mint_circuit_refines_spec S D hD hRest hLog s args s' h)

theorem mint_supply_delta_descends (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : MintArgs) (s' : RecChainedState)
    (h : mintCircuitStep S D hD s args s') (b : AssetId) :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b + (if b = args.a then args.amt else 0) :=
  mintA_supply_delta s args.actor args.cell args.a args.amt s'
    ((mint_exec_equiv_spec s args s').mpr
      (mint_circuit_refines_spec S D hD hRest hLog s args s' h)) b

theorem mint_emitted_equiv_circuit (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (s : RecChainedState) (args : MintArgs) (s' : RecChainedState) :
    mintEmittedStep S D hD s args s' ↔ mintCircuitStep S D hD s args s' :=
  effect2_emitted_equiv_circuit S (mintE D hD) mintAirName s args s'

theorem mint_emitted_refines_spec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : MintArgs) (s' : RecChainedState)
    (h : mintEmittedStep S D hD s args s') :
    mintSpecStep s args s' :=
  mint_circuit_refines_spec S D hD hRest hLog s args s'
    ((mint_emitted_equiv_circuit S D hD s args s').mp h)

#assert_axioms mint_exec_equiv_spec
#assert_axioms mint_circuit_refines_spec
#assert_axioms mint_spec_refines_circuit
#assert_axioms mint_circuit_refines_exec
#assert_axioms mint_supply_delta_descends
#assert_axioms mint_emitted_equiv_circuit
#assert_axioms mint_emitted_refines_spec

/-! ## §3 — BurnA diamond (the mint dual: debit instead of credit). -/

def burnExecStep (s : RecChainedState) (args : BurnArgs) (s' : RecChainedState) : Prop :=
  execFullA s (.burnA args.actor args.cell args.a args.amt) = some s'

def burnSpecStep (s : RecChainedState) (args : BurnArgs) (s' : RecChainedState) : Prop :=
  BurnSpec s args.actor args.cell args.a args.amt s'

def burnCircuitStep (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : BurnArgs) (s' : RecChainedState) : Prop :=
  effect2CircuitStep S (burnE D hD) s args s'

theorem burnRestFrameEncodes (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) :
    RestFrameEncodes2 S (burnE D hD) :=
  fun k k' hframe => (hRest k k').mpr hframe

theorem burn_exec_equiv_spec (s : RecChainedState) (args : BurnArgs) (s' : RecChainedState) :
    burnExecStep s args s' ↔ burnSpecStep s args s' :=
  execFullA_burnA_iff_spec s args.actor args.cell args.a args.amt s'

theorem burn_circuit_refines_spec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BurnArgs) (s' : RecChainedState)
    (h : burnCircuitStep S D hD s args s') :
    burnSpecStep s args s' :=
  burnA_full_sound S D hD hRest hLog s args s' h

theorem burn_spec_refines_circuit (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH)
    (s : RecChainedState) (args : BurnArgs) (s' : RecChainedState)
    (h : burnSpecStep s args s') :
    burnCircuitStep S D hD s args s' :=
  effect2_apex_refines_circuit S (burnE D hD)
    (burnRestFrameEncodes S D hD hRest) (burnGuardEncodes D hD) s args s'
    ((apex_iff_burnSpec D hD s args s').mpr h)

theorem burn_circuit_refines_exec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BurnArgs) (s' : RecChainedState)
    (h : burnCircuitStep S D hD s args s') :
    burnExecStep s args s' :=
  (burn_exec_equiv_spec s args s').mpr
    (burn_circuit_refines_spec S D hD hRest hLog s args s' h)

#assert_axioms burn_exec_equiv_spec
#assert_axioms burn_circuit_refines_spec
#assert_axioms burn_spec_refines_circuit
#assert_axioms burn_circuit_refines_exec

/-! ## §4 — CreateCellA diamond (circuit ⟺ CreateCellSpec ⟺ execFullA). -/

def createCellExecStep (s : RecChainedState) (args : CreateCellArgs) (s' : RecChainedState) : Prop :=
  execFullA s (.createCellA args.actor args.newCell) = some s'

def createCellSpecStep (s : RecChainedState) (args : CreateCellArgs) (s' : RecChainedState) : Prop :=
  CreateCellSpec s args.actor args.newCell s'

def createCellCircuitStep (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (s : RecChainedState) (args : CreateCellArgs) (s' : RecChainedState) : Prop :=
  satisfiedE2Triple S (createCellE LE cN hN hLE DBal hDBal DSide hDSide)
    (encodeE2Triple S (createCellE LE cN hN hLE DBal hDBal DSide hDSide) s args s')

theorem createCell_exec_equiv_spec (s : RecChainedState) (args : CreateCellArgs)
    (s' : RecChainedState) :
    createCellExecStep s args s' ↔ createCellSpecStep s args s' :=
  execCreateCellA_iff_spec s args.actor args.newCell s'

theorem createCell_circuit_refines_spec (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (hRest : RestIffNoAccountsBalBorn S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CreateCellArgs) (s' : RecChainedState)
    (h : createCellCircuitStep S LE cN hN hLE DBal hDBal DSide hDSide s args s') :
    createCellSpecStep s args s' :=
  createCellA_full_sound S LE cN hN hLE DBal hDBal DSide hDSide hRest hLog s args s' h

theorem createCell_spec_refines_circuit (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (hRest : RestIffNoAccountsBalBorn S.RH)
    (s : RecChainedState) (args : CreateCellArgs) (s' : RecChainedState)
    (h : createCellSpecStep s args s') :
    createCellCircuitStep S LE cN hN hLE DBal hDBal DSide hDSide s args s' :=
  effect2triple_circuit_full_complete S (createCellE LE cN hN hLE DBal hDBal DSide hDSide)
    (createCellRestFrameEncodes S LE cN hN hLE DBal hDBal DSide hDSide hRest)
    (createCellGuardEncodes LE cN hN hLE DBal hDBal DSide hDSide) s args s'
    ((apex_iff_createCellSpec LE cN hN hLE DBal hDBal DSide hDSide s args s').mpr h)

theorem createCell_circuit_refines_exec (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (hRest : RestIffNoAccountsBalBorn S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CreateCellArgs) (s' : RecChainedState)
    (h : createCellCircuitStep S LE cN hN hLE DBal hDBal DSide hDSide s args s') :
    createCellExecStep s args s' :=
  (createCell_exec_equiv_spec s args s').mpr
    (createCell_circuit_refines_spec S LE cN hN hLE DBal hDBal DSide hDSide hRest hLog s args s' h)

#assert_axioms createCell_exec_equiv_spec
#assert_axioms createCell_circuit_refines_spec
#assert_axioms createCell_spec_refines_circuit
#assert_axioms createCell_circuit_refines_exec

/-! ## §5 — SpawnA diamond (circuit ⟺ SpawnSpec ⟺ execFullA). -/

def spawnExecStep (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState) : Prop :=
  execFullA s (.spawnA args.actor args.child args.target) = some s'

def spawnSpecStep (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState) : Prop :=
  SpawnSpec s args.actor args.child args.target s'

def spawnCircuitStep (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)
    (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState) : Prop :=
  satisfiedE2Quint S (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs)
    (encodeE2Quint S (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs) s args s')

theorem spawn_exec_equiv_spec (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState) :
    spawnExecStep s args s' ↔ spawnSpecStep s args s' :=
  spawnChainA_iff_spec s args.actor args.child args.target s'

theorem spawnRestFrameEncodes (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)
    (hRest : RestIffNoSpawnTouched S.RH) :
    RestFrameEncodes2Quint S (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs) :=
  fun k k' h => (hRest k k').mpr h

theorem spawn_circuit_refines_spec (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)
    (hRest : RestIffNoSpawnTouched S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState)
    (h : spawnCircuitStep S LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs s args s') :
    spawnSpecStep s args s' :=
  spawnA_full_sound S LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs hRest hLog s args s' h

theorem spawn_spec_refines_circuit (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)
    (hRest : RestIffNoSpawnTouched S.RH)
    (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState)
    (h : spawnSpecStep s args s') :
    spawnCircuitStep S LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs s args s' :=
  effect2quint_circuit_full_complete S (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs)
    (spawnRestFrameEncodes S LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs hRest)
    (spawnGuardEncodes LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs) s args s'
    ((apex_iff_spawnSpec LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs s args s').mpr h)

theorem spawn_circuit_refines_exec (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)
    (hRest : RestIffNoSpawnTouched S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState)
    (h : spawnCircuitStep S LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs s args s') :
    spawnExecStep s args s' :=
  (spawn_exec_equiv_spec s args s').mpr
    (spawn_circuit_refines_spec S LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs hRest hLog
      s args s' h)

#assert_axioms spawn_exec_equiv_spec
#assert_axioms spawn_circuit_refines_spec
#assert_axioms spawn_spec_refines_circuit
#assert_axioms spawn_circuit_refines_exec

/-! ## §6 — Transfer diamond (circuit ⟺ BalanceMovementSpec ⟺ execFullA). -/

section TransferDiamond
open Dregg2.Circuit.Inst.Transfer

def transferExecStep (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState) : Prop :=
  execFullA s (.balanceA args.t args.a) = some s'

def transferSpecStep (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState) : Prop :=
  BalanceMovementSpec s args.t args.a s'

def transferCircuitStep (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState) : Prop :=
  effect2CircuitStep S (balanceE D hD) s args s'

theorem transferRestFrameEncodes (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) :
    RestFrameEncodes2 S (balanceE D hD) :=
  fun k k' hframe => (hRest k k').mpr hframe

theorem transfer_exec_equiv_spec (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState) :
    transferExecStep s args s' ↔ transferSpecStep s args s' :=
  execFullA_balanceA_iff_spec s args.t args.a s'

theorem transfer_circuit_refines_spec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState)
    (h : transferCircuitStep S D hD s args s') :
    transferSpecStep s args s' :=
  transfer_full_sound S D hD hRest hLog s args s' h

theorem transfer_spec_refines_circuit (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState)
    (h : transferSpecStep s args s') :
    transferCircuitStep S D hD s args s' :=
  effect2_apex_refines_circuit S (balanceE D hD)
    (transferRestFrameEncodes S D hD hRest) (balanceGuardEncodes D hD) s args s'
    ((apex_iff_balanceMovementSpec D hD s args s').mpr h)

theorem transfer_circuit_refines_exec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState)
    (h : transferCircuitStep S D hD s args s') :
    transferExecStep s args s' :=
  (transfer_exec_equiv_spec s args s').mpr
    (transfer_circuit_refines_spec S D hD hRest hLog s args s' h)

#assert_axioms transfer_exec_equiv_spec
#assert_axioms transfer_circuit_refines_spec
#assert_axioms transfer_spec_refines_circuit
#assert_axioms transfer_circuit_refines_exec

end TransferDiamond

/-! ## §7 — BalanceA diamond (`balanceAE` instance; same spec, distinct circuit package). -/

section BalanceADiamond
open Dregg2.Circuit.Inst.BalanceA

def balanceAExecStep (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState) : Prop :=
  execFullA s (.balanceA args.t args.a) = some s'

def balanceASpecStep (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState) : Prop :=
  BalanceMovementSpec s args.t args.a s'

def balanceACircuitStep (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState) : Prop :=
  effect2CircuitStep S (balanceAE D hD) s args s'

theorem balanceARestFrameEncodes (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) :
    RestFrameEncodes2 S (balanceAE D hD) :=
  fun k k' hframe => (hRest k k').mpr hframe

theorem balanceA_exec_equiv_spec (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState) :
    balanceAExecStep s args s' ↔ balanceASpecStep s args s' :=
  execFullA_balanceA_iff_spec s args.t args.a s'

theorem balanceA_circuit_refines_spec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState)
    (h : balanceACircuitStep S D hD s args s') :
    balanceASpecStep s args s' :=
  balanceA_full_sound S D hD hRest hLog s args s' h

theorem balanceA_spec_refines_circuit (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState)
    (h : balanceASpecStep s args s') :
    balanceACircuitStep S D hD s args s' :=
  effect2_apex_refines_circuit S (balanceAE D hD)
    (balanceARestFrameEncodes S D hD hRest) (balanceGuardEncodes D hD) s args s'
    ((apex_iff_balanceASpec D hD s args s').mpr h)

theorem balanceA_circuit_refines_exec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState)
    (h : balanceACircuitStep S D hD s args s') :
    balanceAExecStep s args s' :=
  (balanceA_exec_equiv_spec s args s').mpr
    (balanceA_circuit_refines_spec S D hD hRest hLog s args s' h)

#assert_axioms balanceA_exec_equiv_spec
#assert_axioms balanceA_circuit_refines_spec
#assert_axioms balanceA_spec_refines_circuit
#assert_axioms balanceA_circuit_refines_exec

end BalanceADiamond

/-! ## §8 — Delegate diamond (circuit ⟺ DelegateSpec ⟺ execFullA). -/

def delegateExecStep (s : RecChainedState) (args : DelegateArgs) (s' : RecChainedState) : Prop :=
  execFullA s (.delegate args.del args.recipient args.target) = some s'

def delegateSpecStep (s : RecChainedState) (args : DelegateArgs) (s' : RecChainedState) : Prop :=
  DelegateSpec s args.del args.recipient args.target s'

def delegateCircuitStep (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : DelegateArgs) (s' : RecChainedState) : Prop :=
  effect2CircuitStep S (delegateE D hD) s args s'

theorem delegateRestFrameEncodes (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.Delegate.RestIffNoCaps S.RH) :
    RestFrameEncodes2 S (delegateE D hD) :=
  fun k k' hframe => (hRest k k').mpr hframe

theorem delegate_exec_equiv_spec (s : RecChainedState) (args : DelegateArgs) (s' : RecChainedState) :
    delegateExecStep s args s' ↔ delegateSpecStep s args s' :=
  execFullA_delegate_iff_spec s args.del args.recipient args.target s'

theorem delegate_circuit_refines_spec (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.Delegate.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : DelegateArgs) (s' : RecChainedState)
    (h : delegateCircuitStep S D hD s args s') :
    delegateSpecStep s args s' :=
  delegate_full_sound S D hD hRest hLog s args s' h

theorem delegate_spec_refines_circuit (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.Delegate.RestIffNoCaps S.RH)
    (s : RecChainedState) (args : DelegateArgs) (s' : RecChainedState)
    (h : delegateSpecStep s args s') :
    delegateCircuitStep S D hD s args s' :=
  effect2_apex_refines_circuit S (delegateE D hD)
    (delegateRestFrameEncodes S D hD hRest) (delegateGuardEncodes D hD) s args s'
    ((apex_iff_delegateSpec D hD s args s').mpr h)

theorem delegate_circuit_refines_exec (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.Delegate.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : DelegateArgs) (s' : RecChainedState)
    (h : delegateCircuitStep S D hD s args s') :
    delegateExecStep s args s' :=
  (delegate_exec_equiv_spec s args s').mpr
    (delegate_circuit_refines_spec S D hD hRest hLog s args s' h)

#assert_axioms delegate_exec_equiv_spec
#assert_axioms delegate_circuit_refines_spec
#assert_axioms delegate_spec_refines_circuit
#assert_axioms delegate_circuit_refines_exec

/-! ## §9 — NoteSpendA diamond (circuit ⟺ NoteSpendSpec ⟺ execFullA). -/

def noteSpendExecStep (s : RecChainedState) (args : NoteSpendArgs) (s' : RecChainedState) : Prop :=
  execFullA s (.noteSpendA args.nf args.actor args.spendProof) = some s'

def noteSpendSpecStep (s : RecChainedState) (args : NoteSpendArgs) (s' : RecChainedState) : Prop :=
  NoteSpendSpec s args.nf args.actor args.spendProof s'

def noteSpendCircuitStep (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : NoteSpendArgs) (s' : RecChainedState) : Prop :=
  effect2CircuitStep S (noteSpendE LE cN hN hLE) s args s'

theorem noteSpendRestFrameEncodes (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (hRest : RestIffNoNullifiers S.RH) :
    RestFrameEncodes2 S (noteSpendE LE cN hN hLE) :=
  fun k k' hframe => (hRest k k').mpr hframe

theorem noteSpend_exec_equiv_spec (s : RecChainedState) (args : NoteSpendArgs) (s' : RecChainedState) :
    noteSpendExecStep s args s' ↔ noteSpendSpecStep s args s' :=
  execFullA_noteSpend_iff_spec s args.nf args.actor args.spendProof s'

theorem noteSpend_circuit_refines_spec (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoNullifiers S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : NoteSpendArgs) (s' : RecChainedState)
    (h : noteSpendCircuitStep S LE cN hN hLE s args s') :
    noteSpendSpecStep s args s' :=
  noteSpendA_full_sound S LE cN hN hLE hRest hLog s args s' h

theorem noteSpend_spec_refines_circuit (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoNullifiers S.RH)
    (s : RecChainedState) (args : NoteSpendArgs) (s' : RecChainedState)
    (h : noteSpendSpecStep s args s') :
    noteSpendCircuitStep S LE cN hN hLE s args s' :=
  effect2_apex_refines_circuit S (noteSpendE LE cN hN hLE)
    (noteSpendRestFrameEncodes S LE cN hN hLE hRest) (noteSpendGuardEncodes LE cN hN hLE) s args s'
    ((apex_iff_noteSpendSpec LE cN hN hLE s args s').mpr h)

theorem noteSpend_circuit_refines_exec (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoNullifiers S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : NoteSpendArgs) (s' : RecChainedState)
    (h : noteSpendCircuitStep S LE cN hN hLE s args s') :
    noteSpendExecStep s args s' :=
  (noteSpend_exec_equiv_spec s args s').mpr
    (noteSpend_circuit_refines_spec S LE cN hN hLE hRest hLog s args s' h)

#assert_axioms noteSpend_exec_equiv_spec
#assert_axioms noteSpend_circuit_refines_spec
#assert_axioms noteSpend_spec_refines_circuit
#assert_axioms noteSpend_circuit_refines_exec

/-! ## §10 — CreateEscrowA diamond (dual circuit ⟺ EscrowHoldingCreateSpec ⟺ execFullA). -/

def createEscrowExecStep (s : RecChainedState) (args : CreateEscrowArgs) (s' : RecChainedState) : Prop :=
  execFullA s (.createEscrowA args.id args.actor args.creator args.recipient args.asset args.amount) =
    some s'

def createEscrowSpecStep (s : RecChainedState) (args : CreateEscrowArgs) (s' : RecChainedState) : Prop :=
  EscrowHoldingCreateSpec s args.id args.actor args.creator args.recipient args.asset args.amount s'

def createEscrowCircuitStep (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : CreateEscrowArgs) (s' : RecChainedState) : Prop :=
  satisfiedE2Dual S (createEscrowE D hD LE cN hN hLE)
    (encodeE2Dual S (createEscrowE D hD LE cN hN hLE) s args s')

theorem createEscrowRestFrameEncodes (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (hRest : RestIffNoBalEscrows S.RH) :
    RestFrameEncodes2Dual S (createEscrowE D hD LE cN hN hLE) :=
  fun k k' hframe => (hRest k k').mpr hframe

theorem createEscrow_exec_equiv_spec (s : RecChainedState) (args : CreateEscrowArgs)
    (s' : RecChainedState) :
    createEscrowExecStep s args s' ↔ createEscrowSpecStep s args s' :=
  execFullA_createEscrowA_iff_spec s args.id args.actor args.creator args.recipient args.asset
    args.amount s'

theorem createEscrow_circuit_refines_spec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CreateEscrowArgs) (s' : RecChainedState)
    (h : createEscrowCircuitStep S D hD LE cN hN hLE s args s') :
    createEscrowSpecStep s args s' :=
  createEscrowA_full_sound S D hD LE cN hN hLE hRest hLog s args s' h

theorem createEscrow_spec_refines_circuit (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH)
    (s : RecChainedState) (args : CreateEscrowArgs) (s' : RecChainedState)
    (h : createEscrowSpecStep s args s') :
    createEscrowCircuitStep S D hD LE cN hN hLE s args s' :=
  effect2dual_circuit_full_complete S (createEscrowE D hD LE cN hN hLE)
    (createEscrowRestFrameEncodes S D hD LE cN hN hLE hRest)
    (createEscrowGuardEncodes D hD LE cN hN hLE) s args s'
    ((apex_iff_escrowHoldingCreateSpec D hD LE cN hN hLE s args s').mpr h)

theorem createEscrow_circuit_refines_exec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CreateEscrowArgs) (s' : RecChainedState)
    (h : createEscrowCircuitStep S D hD LE cN hN hLE s args s') :
    createEscrowExecStep s args s' :=
  (createEscrow_exec_equiv_spec s args s').mpr
    (createEscrow_circuit_refines_spec S D hD LE cN hN hLE hRest hLog s args s' h)

#assert_axioms createEscrow_exec_equiv_spec
#assert_axioms createEscrow_circuit_refines_spec
#assert_axioms createEscrow_spec_refines_circuit
#assert_axioms createEscrow_circuit_refines_exec

/-! ## §11 — NoteCreateA diamond (circuit ⟺ NoteCreateASpec ⟺ execFullA). -/

def noteCreateExecStep (s : RecChainedState) (args : NoteCreateArgs) (s' : RecChainedState) : Prop :=
  execFullA s (.noteCreateA args.cm args.actor) = some s'

def noteCreateSpecStep (s : RecChainedState) (args : NoteCreateArgs) (s' : RecChainedState) : Prop :=
  NoteCreateASpec s args.cm args.actor s'

def noteCreateCircuitStep (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : NoteCreateArgs) (s' : RecChainedState) : Prop :=
  effect2CircuitStep S (noteCreateE LE cN hN hLE) s args s'

theorem noteCreateRestFrameEncodes (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (hRest : RestIffNoCommitments S.RH) :
    RestFrameEncodes2 S (noteCreateE LE cN hN hLE) :=
  fun k k' hframe => (hRest k k').mpr hframe

theorem noteCreate_exec_equiv_spec (s : RecChainedState) (args : NoteCreateArgs)
    (s' : RecChainedState) :
    noteCreateExecStep s args s' ↔ noteCreateSpecStep s args s' :=
  execNoteCreateA_iff_spec s args.cm args.actor s'

theorem noteCreate_circuit_refines_spec (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoCommitments S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : NoteCreateArgs) (s' : RecChainedState)
    (h : noteCreateCircuitStep S LE cN hN hLE s args s') :
    noteCreateSpecStep s args s' :=
  noteCreateA_full_sound S LE cN hN hLE hRest hLog s args s' h

theorem noteCreate_spec_refines_circuit (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoCommitments S.RH)
    (s : RecChainedState) (args : NoteCreateArgs) (s' : RecChainedState)
    (h : noteCreateSpecStep s args s') :
    noteCreateCircuitStep S LE cN hN hLE s args s' :=
  effect2_apex_refines_circuit S (noteCreateE LE cN hN hLE)
    (noteCreateRestFrameEncodes S LE cN hN hLE hRest) (noteCreateGuardEncodes LE cN hN hLE) s args s'
    ((apex_iff_noteCreateASpec LE cN hN hLE s args s').mpr h)

theorem noteCreate_circuit_refines_exec (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoCommitments S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : NoteCreateArgs) (s' : RecChainedState)
    (h : noteCreateCircuitStep S LE cN hN hLE s args s') :
    noteCreateExecStep s args s' :=
  (noteCreate_exec_equiv_spec s args s').mpr
    (noteCreate_circuit_refines_spec S LE cN hN hLE hRest hLog s args s' h)

#assert_axioms noteCreate_exec_equiv_spec
#assert_axioms noteCreate_circuit_refines_spec
#assert_axioms noteCreate_spec_refines_circuit
#assert_axioms noteCreate_circuit_refines_exec

/-! ## §12 — ReleaseEscrowA diamond (dual circuit ⟺ ReleaseEscrowSpec ⟺ execFullA). -/

def releaseEscrowExecStep (s : RecChainedState) (args : ReleaseArgs) (s' : RecChainedState) : Prop :=
  execFullA s (.releaseEscrowA args.id args.actor) = some s'

def releaseEscrowSpecStep (s : RecChainedState) (args : ReleaseArgs) (s' : RecChainedState) : Prop :=
  ReleaseEscrowSpec s args.id args.actor s'

def releaseEscrowCircuitStep (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : ReleaseArgs) (s' : RecChainedState) : Prop :=
  satisfiedE2Dual S (releaseEscrowE D hD LE cN hN hLE)
    (encodeE2Dual S (releaseEscrowE D hD LE cN hN hLE) s args s')

theorem releaseEscrowRestFrameEncodes (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (hRest : RestIffNoBalEscrows S.RH) :
    RestFrameEncodes2Dual S (releaseEscrowE D hD LE cN hN hLE) :=
  fun k k' hframe => (hRest k k').mpr hframe

theorem releaseEscrow_exec_equiv_spec (s : RecChainedState) (args : ReleaseArgs)
    (s' : RecChainedState) :
    releaseEscrowExecStep s args s' ↔ releaseEscrowSpecStep s args s' :=
  execFullA_releaseEscrow_iff_spec s args.id args.actor s'

theorem releaseEscrow_circuit_refines_spec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : ReleaseArgs) (s' : RecChainedState)
    (h : releaseEscrowCircuitStep S D hD LE cN hN hLE s args s') :
    releaseEscrowSpecStep s args s' :=
  releaseEscrowA_full_sound S D hD LE cN hN hLE hRest hLog s args s' h

theorem releaseEscrow_spec_refines_circuit (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH)
    (s : RecChainedState) (args : ReleaseArgs) (s' : RecChainedState)
    (h : releaseEscrowSpecStep s args s') :
    releaseEscrowCircuitStep S D hD LE cN hN hLE s args s' :=
  effect2dual_circuit_full_complete S (releaseEscrowE D hD LE cN hN hLE)
    (releaseEscrowRestFrameEncodes S D hD LE cN hN hLE hRest)
    (releaseEscrowGuardEncodes D hD LE cN hN hLE) s args s'
    ((apex_iff_releaseEscrowSpec D hD LE cN hN hLE s args s').mpr h)

theorem releaseEscrow_circuit_refines_exec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : ReleaseArgs) (s' : RecChainedState)
    (h : releaseEscrowCircuitStep S D hD LE cN hN hLE s args s') :
    releaseEscrowExecStep s args s' :=
  (releaseEscrow_exec_equiv_spec s args s').mpr
    (releaseEscrow_circuit_refines_spec S D hD LE cN hN hLE hRest hLog s args s' h)

#assert_axioms releaseEscrow_exec_equiv_spec
#assert_axioms releaseEscrow_circuit_refines_spec
#assert_axioms releaseEscrow_spec_refines_circuit
#assert_axioms releaseEscrow_circuit_refines_exec

/-! ## §13 — RefundEscrowA diamond (dual circuit ⟺ RefundEscrowSpec ⟺ execFullA). -/

def refundEscrowExecStep (s : RecChainedState) (args : RefundEscrowArgs) (s' : RecChainedState) : Prop :=
  execFullA s (.refundEscrowA args.id args.actor) = some s'

def refundEscrowSpecStep (s : RecChainedState) (args : RefundEscrowArgs) (s' : RecChainedState) : Prop :=
  RefundEscrowSpec s args.id args.actor s'

def refundEscrowCircuitStep (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : RefundEscrowArgs) (s' : RecChainedState) : Prop :=
  satisfiedE2Dual S (refundEscrowE D hD LE cN hN hLE)
    (encodeE2Dual S (refundEscrowE D hD LE cN hN hLE) s args s')

theorem refundEscrowRestFrameEncodes (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (hRest : RestIffNoBalEscrows S.RH) :
    RestFrameEncodes2Dual S (refundEscrowE D hD LE cN hN hLE) :=
  fun k k' hframe => (hRest k k').mpr hframe

theorem refundEscrow_exec_equiv_spec (s : RecChainedState) (args : RefundEscrowArgs)
    (s' : RecChainedState) :
    refundEscrowExecStep s args s' ↔ refundEscrowSpecStep s args s' :=
  execFullA_refundEscrowA_iff_spec s args.id args.actor s'

theorem refundEscrow_circuit_refines_spec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RefundEscrowArgs) (s' : RecChainedState)
    (h : refundEscrowCircuitStep S D hD LE cN hN hLE s args s') :
    refundEscrowSpecStep s args s' :=
  refundEscrowA_full_sound S D hD LE cN hN hLE hRest hLog s args s' h

theorem refundEscrow_spec_refines_circuit (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH)
    (s : RecChainedState) (args : RefundEscrowArgs) (s' : RecChainedState)
    (h : refundEscrowSpecStep s args s') :
    refundEscrowCircuitStep S D hD LE cN hN hLE s args s' :=
  effect2dual_circuit_full_complete S (refundEscrowE D hD LE cN hN hLE)
    (refundEscrowRestFrameEncodes S D hD LE cN hN hLE hRest)
    (refundEscrowGuardEncodes D hD LE cN hN hLE) s args s'
    ((apex_iff_refundEscrowSpec D hD LE cN hN hLE s args s').mpr h)

theorem refundEscrow_circuit_refines_exec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RefundEscrowArgs) (s' : RecChainedState)
    (h : refundEscrowCircuitStep S D hD LE cN hN hLE s args s') :
    refundEscrowExecStep s args s' :=
  (refundEscrow_exec_equiv_spec s args s').mpr
    (refundEscrow_circuit_refines_spec S D hD LE cN hN hLE hRest hLog s args s' h)

#assert_axioms refundEscrow_exec_equiv_spec
#assert_axioms refundEscrow_circuit_refines_spec
#assert_axioms refundEscrow_spec_refines_circuit
#assert_axioms refundEscrow_circuit_refines_exec

/-! ## §14 — Revoke diamond (circuit ⟺ RevokeSpec ⟺ execFullA). -/

def revokeExecStep (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState) : Prop :=
  execFullA s (.revoke args.holder args.t) = some s'

def revokeSpecStep (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState) : Prop :=
  RevokeSpec s args.holder args.t s'

def revokeCircuitStep (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState) : Prop :=
  effect2CircuitStep S (revokeE D hD) s args s'

theorem revokeRestFrameEncodes (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.Revoke.RestIffNoCaps S.RH) :
    RestFrameEncodes2 S (revokeE D hD) :=
  fun k k' hframe => (hRest k k').mpr hframe

theorem revoke_exec_equiv_spec (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState) :
    revokeExecStep s args s' ↔ revokeSpecStep s args s' :=
  execFullA_revoke_iff_spec s args.holder args.t s'

theorem revoke_circuit_refines_spec (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.Revoke.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState)
    (h : revokeCircuitStep S D hD s args s') :
    revokeSpecStep s args s' :=
  revoke_full_sound S D hD hRest hLog s args s' h

theorem revoke_spec_refines_circuit (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.Revoke.RestIffNoCaps S.RH)
    (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState)
    (h : revokeSpecStep s args s') :
    revokeCircuitStep S D hD s args s' :=
  effect2_apex_refines_circuit S (revokeE D hD)
    (revokeRestFrameEncodes S D hD hRest) (revokeGuardEncodes D hD) s args s'
    ((apex_iff_revokeSpec D hD s args s').mpr h)

theorem revoke_circuit_refines_exec (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.Revoke.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState)
    (h : revokeCircuitStep S D hD s args s') :
    revokeExecStep s args s' :=
  (revoke_exec_equiv_spec s args s').mpr
    (revoke_circuit_refines_spec S D hD hRest hLog s args s' h)

#assert_axioms revoke_exec_equiv_spec
#assert_axioms revoke_circuit_refines_spec
#assert_axioms revoke_spec_refines_circuit
#assert_axioms revoke_circuit_refines_exec

/-! ## §15 — SealA diamond (circuit ⟺ SealSpec ⟺ execFullA). -/

def sealExecStep (s : RecChainedState) (args : SealArgs) (s' : RecChainedState) : Prop :=
  execFullA s (.sealA args.pid args.actor args.payload) = some s'

def sealSpecStep (s : RecChainedState) (args : SealArgs) (s' : RecChainedState) : Prop :=
  SealSpec s args.pid args.actor args.payload s'

def sealCircuitStep (S : Surface2) (LE : SealedBoxRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : SealArgs) (s' : RecChainedState) : Prop :=
  effect2CircuitStep S (sealE LE cN hN hLE) s args s'

theorem sealRestFrameEncodes (S : Surface2) (LE : SealedBoxRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (hRest : RestIffNoSealedBoxes S.RH) :
    RestFrameEncodes2 S (sealE LE cN hN hLE) :=
  fun k k' hframe => (hRest k k').mpr hframe

theorem seal_exec_equiv_spec (s : RecChainedState) (args : SealArgs) (s' : RecChainedState) :
    sealExecStep s args s' ↔ sealSpecStep s args s' :=
  execFullA_seal_iff_spec s args.pid args.actor args.payload s'

theorem seal_circuit_refines_spec (S : Surface2) (LE : SealedBoxRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoSealedBoxes S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SealArgs) (s' : RecChainedState)
    (h : sealCircuitStep S LE cN hN hLE s args s') :
    sealSpecStep s args s' :=
  sealA_full_sound S LE cN hN hLE hRest hLog s args s' h

theorem seal_spec_refines_circuit (S : Surface2) (LE : SealedBoxRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoSealedBoxes S.RH)
    (s : RecChainedState) (args : SealArgs) (s' : RecChainedState)
    (h : sealSpecStep s args s') :
    sealCircuitStep S LE cN hN hLE s args s' :=
  effect2_apex_refines_circuit S (sealE LE cN hN hLE)
    (sealRestFrameEncodes S LE cN hN hLE hRest) (sealGuardEncodes LE cN hN hLE) s args s'
    ((apex_iff_sealSpec LE cN hN hLE s args s').mpr h)

theorem seal_circuit_refines_exec (S : Surface2) (LE : SealedBoxRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoSealedBoxes S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SealArgs) (s' : RecChainedState)
    (h : sealCircuitStep S LE cN hN hLE s args s') :
    sealExecStep s args s' :=
  (seal_exec_equiv_spec s args s').mpr
    (seal_circuit_refines_spec S LE cN hN hLE hRest hLog s args s' h)

#assert_axioms seal_exec_equiv_spec
#assert_axioms seal_circuit_refines_spec
#assert_axioms seal_spec_refines_circuit
#assert_axioms seal_circuit_refines_exec

/-! ## §16 — BridgeLockA diamond (dual circuit ⟺ BridgeOutboundLockSpec ⟺ execFullA). -/

def bridgeLockExecStep (s : RecChainedState) (args : BridgeLockArgs) (s' : RecChainedState) : Prop :=
  execFullA s (.bridgeLockA args.id args.actor args.originator args.destination args.asset args.amount) =
    some s'

def bridgeLockSpecStep (s : RecChainedState) (args : BridgeLockArgs) (s' : RecChainedState) : Prop :=
  BridgeOutboundLockSpec s args.id args.actor args.originator args.destination args.asset args.amount s'

def bridgeLockCircuitStep (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : BridgeLockArgs) (s' : RecChainedState) : Prop :=
  satisfiedE2Dual S (bridgeLockE D hD LE cN hN hLE)
    (encodeE2Dual S (bridgeLockE D hD LE cN hN hLE) s args s')

theorem bridgeLockRestFrameEncodes (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (hRest : RestIffNoBalEscrows S.RH) :
    RestFrameEncodes2Dual S (bridgeLockE D hD LE cN hN hLE) :=
  fun k k' hframe => (hRest k k').mpr hframe

theorem bridgeLock_exec_equiv_spec (s : RecChainedState) (args : BridgeLockArgs)
    (s' : RecChainedState) :
    bridgeLockExecStep s args s' ↔ bridgeLockSpecStep s args s' :=
  execFullA_bridgeLockA_iff_spec s args.id args.actor args.originator args.destination args.asset
    args.amount s'

theorem bridgeLock_circuit_refines_spec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BridgeLockArgs) (s' : RecChainedState)
    (h : bridgeLockCircuitStep S D hD LE cN hN hLE s args s') :
    bridgeLockSpecStep s args s' :=
  bridgeLockA_full_sound S D hD LE cN hN hLE hRest hLog s args s' h

theorem bridgeLock_spec_refines_circuit (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH)
    (s : RecChainedState) (args : BridgeLockArgs) (s' : RecChainedState)
    (h : bridgeLockSpecStep s args s') :
    bridgeLockCircuitStep S D hD LE cN hN hLE s args s' :=
  effect2dual_circuit_full_complete S (bridgeLockE D hD LE cN hN hLE)
    (bridgeLockRestFrameEncodes S D hD LE cN hN hLE hRest)
    (bridgeLockGuardEncodes D hD LE cN hN hLE) s args s'
    ((apex_iff_bridgeOutboundLockSpec D hD LE cN hN hLE s args s').mpr h)

theorem bridgeLock_circuit_refines_exec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BridgeLockArgs) (s' : RecChainedState)
    (h : bridgeLockCircuitStep S D hD LE cN hN hLE s args s') :
    bridgeLockExecStep s args s' :=
  (bridgeLock_exec_equiv_spec s args s').mpr
    (bridgeLock_circuit_refines_spec S D hD LE cN hN hLE hRest hLog s args s' h)

#assert_axioms bridgeLock_exec_equiv_spec
#assert_axioms bridgeLock_circuit_refines_spec
#assert_axioms bridgeLock_spec_refines_circuit
#assert_axioms bridgeLock_circuit_refines_exec

/-! ## §17 — QueueEnqueueA diamond (triple circuit ⟺ QueueEnqueueSpec ⟺ execFullA). -/

def queueEnqueueExecStep (s : RecChainedState) (args : EnqueueArgs) (s' : RecChainedState) : Prop :=
  execFullA s (.queueEnqueueA args.id args.m args.actor args.cell args.depId args.dAsset args.deposit) =
    some s'

def queueEnqueueSpecStep (s : RecChainedState) (args : EnqueueArgs) (s' : RecChainedState) : Prop :=
  QueueEnqueueSpec s args.id args.m args.actor args.cell args.depId args.dAsset args.deposit s'

def queueEnqueueCircuitStep (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ) (hNQ : compressNInjective cNQ) (hLQ : listLeafInjective LQ)
    (LE : EscrowRecord → ℤ) (cNE : List ℤ → ℤ) (hNE : compressNInjective cNE) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : EnqueueArgs) (s' : RecChainedState) : Prop :=
  satisfiedE2Triple S (queueEnqueueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE)
    (encodeE2Triple S (queueEnqueueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE) s args s')

theorem queueEnqueueRestFrameEncodes (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ)
    (hNQ : compressNInjective cNQ) (hLQ : listLeafInjective LQ) (LE : EscrowRecord → ℤ)
    (cNE : List ℤ → ℤ) (hNE : compressNInjective cNE) (hLE : listLeafInjective LE)
    (hRest : RestIffNoQueuesBalEscrows S.RH) :
    RestFrameEncodes2Triple S (queueEnqueueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE) :=
  fun k k' hframe => (hRest k k').mpr hframe

theorem queueEnqueue_exec_equiv_spec (s : RecChainedState) (args : EnqueueArgs) (s' : RecChainedState) :
    queueEnqueueExecStep s args s' ↔ queueEnqueueSpecStep s args s' :=
  execFullA_queueEnqueueA_iff_spec s args.id args.m args.actor args.cell args.depId args.dAsset
    args.deposit s'

theorem queueEnqueue_circuit_refines_spec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ)
    (hNQ : compressNInjective cNQ) (hLQ : listLeafInjective LQ) (LE : EscrowRecord → ℤ)
    (cNE : List ℤ → ℤ) (hNE : compressNInjective cNE) (hLE : listLeafInjective LE)
    (hRest : RestIffNoQueuesBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : EnqueueArgs) (s' : RecChainedState)
    (h : queueEnqueueCircuitStep S D hD LQ cNQ hNQ hLQ LE cNE hNE hLE s args s') :
    queueEnqueueSpecStep s args s' :=
  queueEnqueueA_full_sound S D hD LQ cNQ hNQ hLQ LE cNE hNE hLE hRest hLog s args s' h

theorem queueEnqueue_spec_refines_circuit (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ)
    (hNQ : compressNInjective cNQ) (hLQ : listLeafInjective LQ) (LE : EscrowRecord → ℤ)
    (cNE : List ℤ → ℤ) (hNE : compressNInjective cNE) (hLE : listLeafInjective LE)
    (hRest : RestIffNoQueuesBalEscrows S.RH)
    (s : RecChainedState) (args : EnqueueArgs) (s' : RecChainedState)
    (h : queueEnqueueSpecStep s args s') :
    queueEnqueueCircuitStep S D hD LQ cNQ hNQ hLQ LE cNE hNE hLE s args s' :=
  effect2triple_circuit_full_complete S (queueEnqueueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE)
    (queueEnqueueRestFrameEncodes S D hD LQ cNQ hNQ hLQ LE cNE hNE hLE hRest)
    (enqueueGuardEncodes D hD LQ cNQ hNQ hLQ LE cNE hNE hLE) s args s'
    ((apex_iff_queueEnqueueSpec D hD LQ cNQ hNQ hLQ LE cNE hNE hLE s args s').mpr h)

theorem queueEnqueue_circuit_refines_exec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ)
    (hNQ : compressNInjective cNQ) (hLQ : listLeafInjective LQ) (LE : EscrowRecord → ℤ)
    (cNE : List ℤ → ℤ) (hNE : compressNInjective cNE) (hLE : listLeafInjective LE)
    (hRest : RestIffNoQueuesBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : EnqueueArgs) (s' : RecChainedState)
    (h : queueEnqueueCircuitStep S D hD LQ cNQ hNQ hLQ LE cNE hNE hLE s args s') :
    queueEnqueueExecStep s args s' :=
  (queueEnqueue_exec_equiv_spec s args s').mpr
    (queueEnqueue_circuit_refines_spec S D hD LQ cNQ hNQ hLQ LE cNE hNE hLE hRest hLog s args s' h)

#assert_axioms queueEnqueue_exec_equiv_spec
#assert_axioms queueEnqueue_circuit_refines_spec
#assert_axioms queueEnqueue_spec_refines_circuit
#assert_axioms queueEnqueue_circuit_refines_exec

/-! ## §18 — SetFieldA diamond (v1 circuit ⟺ SetFieldSpec ⟺ execFullA). -/

def setFieldExecStep (s : RecChainedState) (args : SetFieldArgs) (s' : RecChainedState) : Prop :=
  execFullA s (.setFieldA args.actor args.cell args.f args.v) = some s'

def setFieldSpecStep (s : RecChainedState) (args : SetFieldArgs) (s' : RecChainedState) : Prop :=
  SetFieldSpec s args.actor args.cell args.f args.v s'

def setFieldCircuitStep (S : CommitSurface) (s : RecChainedState) (args : SetFieldArgs)
    (s' : RecChainedState) : Prop :=
  satisfiedE S setFieldE (encodeE S setFieldE s args s')

theorem setField_exec_equiv_spec (s : RecChainedState) (args : SetFieldArgs) (s' : RecChainedState) :
    setFieldExecStep s args s' ↔ setFieldSpecStep s args s' :=
  execFullA_setFieldA_iff_spec s args.actor args.cell args.f args.v s'

theorem setField_circuit_refines_spec (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SetFieldArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : setFieldCircuitStep S s args s') :
    setFieldSpecStep s args s' :=
  setFieldE_full_sound S hN hL hRest hLog s args s' hwf hwf' h

theorem setField_spec_refines_circuit (S : CommitSurface) (hRest : RestHashIffFrame S.RH)
    (s : RecChainedState) (args : SetFieldArgs) (s' : RecChainedState)
    (h : setFieldSpecStep s args s') :
    setFieldCircuitStep S s args s' :=
  effect_circuit_full_complete S setFieldE hRest setFieldGuardEncodes s args s'
    ((apex_iff_setFieldSpec s args s').mpr h)

theorem setField_circuit_refines_exec (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SetFieldArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : setFieldCircuitStep S s args s') :
    setFieldExecStep s args s' :=
  (setField_exec_equiv_spec s args s').mpr
    (setField_circuit_refines_spec S hN hL hRest hLog s args s' hwf hwf' h)

#assert_axioms setField_exec_equiv_spec
#assert_axioms setField_circuit_refines_spec
#assert_axioms setField_spec_refines_circuit
#assert_axioms setField_circuit_refines_exec

/-! ## §19 — ExerciseA composite (v1 hold-layer ⟺ `ExerciseHoldSpec`; inner turn composed). -/

def exerciseHoldSpecStep (pre : RecChainedState) (args : ExerciseHoldArgs) (post : RecChainedState) :
    Prop :=
  ExerciseHoldSpec pre args.actor args.target post

theorem exerciseHold_exec_equiv_spec_step (pre post : RecChainedState) (args : ExerciseHoldArgs) :
    exerciseHoldExecStep pre post args ↔ exerciseHoldSpecStep pre args post :=
  exerciseHold_exec_equiv_spec pre post args

theorem exerciseHold_circuit_refines_spec (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (pre post : RecChainedState) (args : ExerciseHoldArgs)
    (hwf : AccountsWF pre.kernel) (hwf' : AccountsWF post.kernel)
    (h : exerciseHoldCircuitStep S pre args post) :
    exerciseHoldSpecStep pre args post :=
  exercise_circuit_refines_hold_spec S hN hL hRest hLog pre post args hwf hwf' h

theorem exercise_composite_circuit_refines_spec (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (pre post : RecChainedState) (args : ExerciseFullArgs)
    (innerTurnH : Prop) (hinner : innerTurnH)
    (hinnerBridge : innerTurnH ↔ turnSpec (exerciseHoldState pre args.actor) args.inner post)
    (hfacet : innerFacetsAdmittedA pre args.actor args.target args.inner = true)
    (hwf : AccountsWF pre.kernel)
    (hhold : exerciseHoldCircuitStep S pre ⟨args.actor, args.target⟩
        (exerciseHoldState pre args.actor)) :
    exerciseSpecStep pre post args :=
  exercise_circuit_refines_spec S hN hL hRest hLog pre post args innerTurnH hinner hinnerBridge hfacet hwf hhold

theorem exercise_composite_circuit_refines_exec (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (pre post : RecChainedState) (args : ExerciseFullArgs)
    (innerTurnH : Prop) (hinner : innerTurnH)
    (hinnerBridge : innerTurnH ↔ turnSpec (exerciseHoldState pre args.actor) args.inner post)
    (hfacet : innerFacetsAdmittedA pre args.actor args.target args.inner = true)
    (hwf : AccountsWF pre.kernel)
    (hhold : exerciseHoldCircuitStep S pre ⟨args.actor, args.target⟩
        (exerciseHoldState pre args.actor)) :
    exerciseExecStep pre post args :=
  exercise_circuit_refines_exec S hN hL hRest hLog pre post args innerTurnH hinner hinnerBridge hfacet hwf hhold

#assert_axioms exerciseHold_exec_equiv_spec_step
#assert_axioms exerciseHold_circuit_refines_spec
#assert_axioms exercise_composite_circuit_refines_spec
#assert_axioms exercise_composite_circuit_refines_exec

end Dregg2.Circuit.EffectRefinement