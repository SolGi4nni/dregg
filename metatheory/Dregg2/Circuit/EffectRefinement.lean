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
import Dregg2.Circuit.Inst.mintA
import Dregg2.Circuit.Inst.burnA
import Dregg2.Circuit.Inst.createCellA
import Dregg2.Circuit.Inst.spawnA

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
open Dregg2.Circuit.Inst.MintA
open Dregg2.Circuit.Inst.BurnA
open Dregg2.Circuit.Inst.CreateCellA
open Dregg2.Circuit.Inst.SpawnA
open Dregg2.Circuit.Spec.SupplyCreation
open Dregg2.Circuit.Spec.SupplyDestruction
open Dregg2.Circuit.Spec.AccountGrowth
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

end Dregg2.Circuit.EffectRefinement