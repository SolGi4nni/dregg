/-
# Dregg2.Circuit.EffectEmittedRefinement — Wave 2 batch emitted→spec refinement.

Extends `EffectRefinement.lean`'s circuit diamonds to the Plonky3 emitted wire layer: for every
effect with `*_circuit_refines_spec`, proves `*_emitted_refines_spec` (emitted ⊑ bespoke spec) via
the generic `emitted ⟺ circuit` faithfulness lemmas + circuit soundness.

POLICY: no lurking holes — incomplete `*_emitted_refines_spec` use explicit `sorry`.
-/
import Dregg2.Circuit.EffectRefinement
import Dregg2.Circuit.EffectEmitRegistry
import Dregg2.Circuit.EffectCommit
import Dregg2.Circuit.EffectCommit2
import Dregg2.Circuit.EffectCommit2Dual
import Dregg2.Circuit.EffectCommit3
import Dregg2.Circuit.EffectCommit4
import Dregg2.Circuit.EffectCommit5
import Dregg2.Circuit.SetFieldCommit
import Dregg2.Circuit.Inst.mintA
import Dregg2.Circuit.Inst.burnA
import Dregg2.Circuit.Inst.transfer
import Dregg2.Circuit.Inst.balanceA
import Dregg2.Circuit.Inst.delegate
import Dregg2.Circuit.Inst.noteSpendA
import Dregg2.Circuit.Inst.createCellA
import Dregg2.Circuit.Inst.spawnA
import Dregg2.Circuit.Inst.noteCreateA
import Dregg2.Circuit.Inst.revoke
import Dregg2.Circuit.Inst.sealA
import Dregg2.Circuit.Inst.exerciseA
import Dregg2.Circuit.Inst.attenuateA
import Dregg2.Circuit.Inst.emitEventA
import Dregg2.Circuit.Inst.incrementNonceA
import Dregg2.Circuit.Inst.setPermissionsA
import Dregg2.Circuit.Inst.setVKA
import Dregg2.Circuit.Inst.delegateAttenA
import Dregg2.Circuit.Inst.introduceA
import Dregg2.Circuit.Inst.validateHandoffA
import Dregg2.Circuit.Inst.revokeDelegationA
import Dregg2.Circuit.Inst.createCellFromFactoryA
import Dregg2.Circuit.Inst.unsealA
import Dregg2.Circuit.Inst.createSealPairA
import Dregg2.Circuit.Inst.makeSovereignA
import Dregg2.Circuit.Inst.refusalA
import Dregg2.Circuit.Inst.receiptArchiveA
import Dregg2.Circuit.Inst.pipelinedSendA
import Dregg2.Circuit.Inst.swissExportA
import Dregg2.Circuit.Inst.enlivenRefA
import Dregg2.Circuit.Inst.swissHandoffA
import Dregg2.Circuit.Inst.swissDropA
import Dregg2.Circuit.Inst.cellSealA
import Dregg2.Circuit.Inst.cellUnsealA
import Dregg2.Circuit.Inst.cellDestroyA
import Dregg2.Circuit.Inst.refreshDelegationA

namespace Dregg2.Circuit.EffectEmittedRefinement

open Dregg2.Circuit
open Dregg2.Circuit.Refinement (StepRel)
open Dregg2.Circuit.EffectRefinement
open Dregg2.Circuit.EffectCommit
  (emitEffectFaithful emittedEffect encodeE satisfiedE EffectSpec CommitSurface)
open Dregg2.Circuit.EffectCommit2
  (emitEffect2Faithful emittedEffect2 encodeE2 EffectSpec2 satisfiedE2)
open Dregg2.Circuit.EffectCommit2Dual
  (emitEffect2DualFaithful emittedEffect2Dual encodeE2Dual EffectSpec2Dual satisfiedE2Dual)
open Dregg2.Circuit.EffectCommit3
  (emitEffect2TripleFaithful emittedEffect2Triple encodeE2Triple EffectSpec2Triple satisfiedE2Triple)
open Dregg2.Circuit.EffectCommit5
  (emitEffect2QuintFaithful emittedEffect2Quint encodeE2Quint EffectSpec2Quint satisfiedE2Quint)
open Dregg2.Circuit.StateCommit (logHashInjective compressNInjective RestHashIffFrame AccountsWF cellLeafInjective)
open Dregg2.Circuit.EffectCommit2 (Surface2 RestIffNoBal RestIffNoNullifiers)
open Dregg2.Circuit.EffectCommit2Dual (RestIffNoBalEscrows)
open Dregg2.Circuit.ListCommit (listLeafInjective)
open Dregg2.Circuit.BornEmptyCommit
open Dregg2.Circuit.EffectInstances (setFieldE SetFieldArgs)
open Dregg2.Circuit.SetFieldCommit (setFieldAirName emittedSetField)
open Dregg2.Circuit.Inst.MintA
open Dregg2.Circuit.Inst.BurnA
open Dregg2.Circuit.Inst.Delegate
open Dregg2.Circuit.Inst.NoteSpendA
open Dregg2.Circuit.Inst.CreateCellA
open Dregg2.Circuit.Inst.SpawnA
open Dregg2.Circuit.Inst.NoteCreateA
open Dregg2.Circuit.Inst.Revoke
open Dregg2.Circuit.Inst.SealA
open Dregg2.Circuit.Inst.ExerciseA
open Dregg2.Exec.CircuitEmit (satisfiedEmitted)
open Dregg2.Authority
open Dregg2.Exec

/-! ## §1 — Generic emitted→bespoke-spec helpers. -/

section GenericEmitted
variable {St Args : Type}

/-- **`bespoke_emitted_refines_spec`** — generic one-liner: emitted ⊑ circuit ⊑ bespoke spec. -/
theorem bespoke_emitted_refines_spec
    (circuitStep emittedStep specStep : StepRel St Args St)
    (circuit_refines_spec :
      ∀ pre args post, circuitStep pre args post → specStep pre args post)
    (emitted_equiv_circuit :
      ∀ pre args post, emittedStep pre args post ↔ circuitStep pre args post)
    (pre : St) (args : Args) (post : St) (h : emittedStep pre args post) :
    specStep pre args post :=
  circuit_refines_spec pre args post ((emitted_equiv_circuit pre args post).mp h)

section Effect2Generic
variable (S : Surface2) (E : EffectSpec2 St Args) (name : String)

abbrev effect2EmittedStepLocal : StepRel St Args St :=
  fun pre args post =>
    satisfiedEmitted (emittedEffect2 name E) (encodeE2 S E pre args post)

theorem effect2_emitted_equiv_circuit_local (pre : St) (args : Args) (post : St) :
    effect2EmittedStepLocal S E name pre args post ↔ effect2CircuitStep S E pre args post :=
  (emitEffect2Faithful name E (encodeE2 S E pre args post)).symm

/-- **`effect2_emitted_refines_bespoke_spec`** — any v2 `EffectSpec2` emitted step refines a bespoke
spec when `*_circuit_refines_spec` is already available. -/
theorem effect2_emitted_refines_bespoke_spec
    (circuitStep specStep : StepRel St Args St)
    (circuit_refines_spec :
      ∀ pre args post, circuitStep pre args post → specStep pre args post)
    (hEmittedCircuit :
      ∀ pre args post, effect2EmittedStepLocal S E name pre args post ↔ circuitStep pre args post)
    (pre : St) (args : Args) (post : St)
    (h : effect2EmittedStepLocal S E name pre args post) :
    specStep pre args post :=
  bespoke_emitted_refines_spec circuitStep (effect2EmittedStepLocal S E name)
    specStep circuit_refines_spec hEmittedCircuit pre args post h

end Effect2Generic

section Effect1Generic
variable (S : CommitSurface) (E : EffectSpec St Args) (name : String)

abbrev effect1CircuitStepLocal : StepRel St Args St :=
  fun pre args post => satisfiedE S E (encodeE S E pre args post)

abbrev effect1EmittedStepLocal : StepRel St Args St :=
  fun pre args post =>
    satisfiedEmitted (emittedEffect name E) (encodeE S E pre args post)

theorem effect1_emitted_equiv_circuit_local (pre : St) (args : Args) (post : St) :
    effect1EmittedStepLocal S E name pre args post ↔ effect1CircuitStepLocal S E pre args post :=
  (emitEffectFaithful name E (encodeE S E pre args post)).symm

/-- **`effect1_emitted_refines_bespoke_spec`** — v1 `EffectCommit` emitted step refines bespoke spec. -/
theorem effect1_emitted_refines_bespoke_spec
    (specStep : StepRel St Args St)
    (circuit_refines_spec :
      ∀ pre args post, effect1CircuitStepLocal S E pre args post → specStep pre args post)
    (pre : St) (args : Args) (post : St)
    (h : effect1EmittedStepLocal S E name pre args post) :
    specStep pre args post :=
  circuit_refines_spec pre args post
    ((effect1_emitted_equiv_circuit_local S E name pre args post).mp h)

end Effect1Generic

section Effect2DualGeneric
variable (S : Surface2) (E : EffectSpec2Dual St Args) (name : String)

abbrev effect2dualEmittedStepLocal : StepRel St Args St :=
  fun pre args post =>
    satisfiedEmitted (emittedEffect2Dual name E) (encodeE2Dual S E pre args post)

theorem effect2dual_emitted_equiv_circuit_local (pre : St) (args : Args) (post : St) :
    effect2dualEmittedStepLocal S E name pre args post ↔
      satisfiedE2Dual S E (encodeE2Dual S E pre args post) :=
  (emitEffect2DualFaithful name E (encodeE2Dual S E pre args post)).symm

theorem effect2dual_emitted_refines_bespoke_spec
    (circuitStep specStep : StepRel St Args St)
    (circuit_refines_spec :
      ∀ pre args post, circuitStep pre args post → specStep pre args post)
    (hEmittedCircuit :
      ∀ pre args post, effect2dualEmittedStepLocal S E name pre args post ↔ circuitStep pre args post)
    (pre : St) (args : Args) (post : St)
    (h : effect2dualEmittedStepLocal S E name pre args post) :
    specStep pre args post :=
  bespoke_emitted_refines_spec circuitStep (effect2dualEmittedStepLocal S E name)
    specStep circuit_refines_spec hEmittedCircuit pre args post h

end Effect2DualGeneric

section Effect2TripleGeneric
variable (S : Surface2) (E : EffectSpec2Triple St Args) (name : String)

abbrev effect2tripleEmittedStepLocal : StepRel St Args St :=
  fun pre args post =>
    satisfiedEmitted (emittedEffect2Triple name E) (encodeE2Triple S E pre args post)

theorem effect2triple_emitted_equiv_circuit_local (pre : St) (args : Args) (post : St) :
    effect2tripleEmittedStepLocal S E name pre args post ↔
      satisfiedE2Triple S E (encodeE2Triple S E pre args post) :=
  (emitEffect2TripleFaithful name E (encodeE2Triple S E pre args post)).symm

theorem effect2triple_emitted_refines_bespoke_spec
    (circuitStep specStep : StepRel St Args St)
    (circuit_refines_spec :
      ∀ pre args post, circuitStep pre args post → specStep pre args post)
    (hEmittedCircuit :
      ∀ pre args post, effect2tripleEmittedStepLocal S E name pre args post ↔ circuitStep pre args post)
    (pre : St) (args : Args) (post : St)
    (h : effect2tripleEmittedStepLocal S E name pre args post) :
    specStep pre args post :=
  bespoke_emitted_refines_spec circuitStep (effect2tripleEmittedStepLocal S E name)
    specStep circuit_refines_spec hEmittedCircuit pre args post h

end Effect2TripleGeneric

section Effect2QuintGeneric
variable (S : Surface2) (E : EffectSpec2Quint St Args) (name : String)

abbrev effect2quintEmittedStepLocal : StepRel St Args St :=
  fun pre args post =>
    satisfiedEmitted (emittedEffect2Quint name E) (encodeE2Quint S E pre args post)

theorem effect2quint_emitted_equiv_circuit_local (pre : St) (args : Args) (post : St) :
    effect2quintEmittedStepLocal S E name pre args post ↔
      satisfiedE2Quint S E (encodeE2Quint S E pre args post) :=
  (emitEffect2QuintFaithful name E (encodeE2Quint S E pre args post)).symm

theorem effect2quint_emitted_refines_bespoke_spec
    (circuitStep specStep : StepRel St Args St)
    (circuit_refines_spec :
      ∀ pre args post, circuitStep pre args post → specStep pre args post)
    (hEmittedCircuit :
      ∀ pre args post, effect2quintEmittedStepLocal S E name pre args post ↔ circuitStep pre args post)
    (pre : St) (args : Args) (post : St)
    (h : effect2quintEmittedStepLocal S E name pre args post) :
    specStep pre args post :=
  bespoke_emitted_refines_spec circuitStep (effect2quintEmittedStepLocal S E name)
    specStep circuit_refines_spec hEmittedCircuit pre args post h

end Effect2QuintGeneric

end GenericEmitted

/-! ## §2 — MintA (v2; already in EffectRefinement, re-exported here for the batch portal). -/

def mintEmittedStep (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : MintArgs) (s' : RecChainedState) : Prop :=
  effect2EmittedStepLocal S (mintE D hD) mintAirName s args s'

theorem mint_emitted_equiv_circuit (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (s : RecChainedState) (args : MintArgs) (s' : RecChainedState) :
    mintEmittedStep S D hD s args s' ↔ mintCircuitStep S D hD s args s' :=
  effect2_emitted_equiv_circuit_local S (mintE D hD) mintAirName s args s'

theorem mint_emitted_refines_spec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : MintArgs) (s' : RecChainedState)
    (h : mintEmittedStep S D hD s args s') :
    mintSpecStep s args s' :=
  effect2_emitted_refines_bespoke_spec S (mintE D hD) mintAirName
    (mintCircuitStep S D hD) mintSpecStep (mint_circuit_refines_spec S D hD hRest hLog)
    (fun pre args post => mint_emitted_equiv_circuit S D hD pre args post) s args s' h

/-! ## §3 — BurnA. -/

def burnEmittedStep (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : BurnArgs) (s' : RecChainedState) : Prop :=
  effect2EmittedStepLocal S (burnE D hD) burnAirName s args s'

theorem burn_emitted_equiv_circuit (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (s : RecChainedState) (args : BurnArgs) (s' : RecChainedState) :
    burnEmittedStep S D hD s args s' ↔ burnCircuitStep S D hD s args s' :=
  effect2_emitted_equiv_circuit_local S (burnE D hD) burnAirName s args s'

theorem burn_emitted_refines_spec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BurnArgs) (s' : RecChainedState)
    (h : burnEmittedStep S D hD s args s') :
    burnSpecStep s args s' :=
  effect2_emitted_refines_bespoke_spec S (burnE D hD) burnAirName
    (burnCircuitStep S D hD) burnSpecStep (burn_circuit_refines_spec S D hD hRest hLog)
    (fun pre args post => burn_emitted_equiv_circuit S D hD pre args post) s args s' h

/-! ## §4 — CreateCellA (v2-triple). -/

def createCellEmittedStep (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (s : RecChainedState) (args : CreateCellArgs) (s' : RecChainedState) : Prop :=
  effect2tripleEmittedStepLocal S
    (createCellE LE cN hN hLE DBal hDBal DSide hDSide) createCellAAirName s args s'

theorem createCell_emitted_equiv_circuit (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (s : RecChainedState) (args : CreateCellArgs) (s' : RecChainedState) :
    createCellEmittedStep S LE cN hN hLE DBal hDBal DSide hDSide s args s' ↔
      createCellCircuitStep S LE cN hN hLE DBal hDBal DSide hDSide s args s' :=
  effect2triple_emitted_equiv_circuit_local S
    (createCellE LE cN hN hLE DBal hDBal DSide hDSide) createCellAAirName s args s'

theorem createCell_emitted_refines_spec (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DSide : BornEmptySideTables → ℤ) (hDSide : Function.Injective DSide)
    (hRest : RestIffNoAccountsBalBorn S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CreateCellArgs) (s' : RecChainedState)
    (h : createCellEmittedStep S LE cN hN hLE DBal hDBal DSide hDSide s args s') :
    createCellSpecStep s args s' :=
  effect2triple_emitted_refines_bespoke_spec S
    (createCellE LE cN hN hLE DBal hDBal DSide hDSide) createCellAAirName
    (createCellCircuitStep S LE cN hN hLE DBal hDBal DSide hDSide) createCellSpecStep
    (createCell_circuit_refines_spec S LE cN hN hLE DBal hDBal DSide hDSide hRest hLog)
    (fun pre args post =>
      createCell_emitted_equiv_circuit S LE cN hN hLE DBal hDBal DSide hDSide pre args post)
    s args s' h

/-! ## §5 — SpawnA (v2-quint). -/

def spawnEmittedStep (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)
    (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState) : Prop :=
  effect2quintEmittedStepLocal S
    (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs) spawnAAirName s args s'

theorem spawn_emitted_equiv_circuit (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)
    (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState) :
    spawnEmittedStep S LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs s args s' ↔
      spawnCircuitStep S LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs s args s' :=
  effect2quint_emitted_equiv_circuit_local S
    (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs) spawnAAirName s args s'

theorem spawn_emitted_refines_spec (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
    (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
    (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
    (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)
    (hRest : RestIffNoSpawnTouched S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState)
    (h : spawnEmittedStep S LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs s args s') :
    spawnSpecStep s args s' :=
  effect2quint_emitted_refines_bespoke_spec S
    (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs) spawnAAirName
    (spawnCircuitStep S LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs) spawnSpecStep
    (spawn_circuit_refines_spec S LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs hRest hLog)
    (fun pre args post =>
      spawn_emitted_equiv_circuit S LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs
        pre args post)
    s args s' h

/-! ## §6 — Transfer + BalanceA (both `BalanceMovementSpec`). -/

section TransferEmitted
open Dregg2.Circuit.Inst.Transfer

def transferEmittedStep (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState) : Prop :=
  effect2EmittedStepLocal S (balanceE D hD) transferAirName s args s'

theorem transfer_emitted_equiv_circuit (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState) :
    transferEmittedStep S D hD s args s' ↔ transferCircuitStep S D hD s args s' :=
  effect2_emitted_equiv_circuit_local S (balanceE D hD) transferAirName s args s'

theorem transfer_emitted_refines_spec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState)
    (h : transferEmittedStep S D hD s args s') :
    transferSpecStep s args s' :=
  transfer_circuit_refines_spec S D hD hRest hLog s args s'
    ((transfer_emitted_equiv_circuit S D hD s args s').mp h)

end TransferEmitted

section BalanceAEmitted
open Dregg2.Circuit.Inst.BalanceA

def balanceAEmittedStep (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState) : Prop :=
  effect2EmittedStepLocal S (balanceAE D hD) balanceAAirName s args s'

theorem balanceA_emitted_equiv_circuit (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState) :
    balanceAEmittedStep S D hD s args s' ↔ balanceACircuitStep S D hD s args s' :=
  effect2_emitted_equiv_circuit_local S (balanceAE D hD) balanceAAirName s args s'

theorem balanceA_emitted_refines_spec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (hRest : RestIffNoBal S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BalanceArgs) (s' : RecChainedState)
    (h : balanceAEmittedStep S D hD s args s') :
    balanceASpecStep s args s' :=
  balanceA_circuit_refines_spec S D hD hRest hLog s args s'
    ((balanceA_emitted_equiv_circuit S D hD s args s').mp h)

end BalanceAEmitted

/-! ## §7 — Delegate. -/

def delegateEmittedStep (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : DelegateArgs) (s' : RecChainedState) : Prop :=
  effect2EmittedStepLocal S (delegateE D hD) delegateAirName s args s'

theorem delegate_emitted_equiv_circuit (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : DelegateArgs) (s' : RecChainedState) :
    delegateEmittedStep S D hD s args s' ↔ delegateCircuitStep S D hD s args s' :=
  effect2_emitted_equiv_circuit_local S (delegateE D hD) delegateAirName s args s'

theorem delegate_emitted_refines_spec (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.Delegate.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : DelegateArgs) (s' : RecChainedState)
    (h : delegateEmittedStep S D hD s args s') :
    delegateSpecStep s args s' :=
  effect2_emitted_refines_bespoke_spec S (delegateE D hD) delegateAirName
    (delegateCircuitStep S D hD) delegateSpecStep (delegate_circuit_refines_spec S D hD hRest hLog)
    (fun pre args post => delegate_emitted_equiv_circuit S D hD pre args post) s args s' h

/-! ## §8 — NoteSpendA. -/

def noteSpendEmittedStep (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : NoteSpendArgs) (s' : RecChainedState) : Prop :=
  effect2EmittedStepLocal S (noteSpendE LE cN hN hLE) noteSpendAAirName s args s'

theorem noteSpend_emitted_equiv_circuit (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : NoteSpendArgs) (s' : RecChainedState) :
    noteSpendEmittedStep S LE cN hN hLE s args s' ↔
      noteSpendCircuitStep S LE cN hN hLE s args s' :=
  effect2_emitted_equiv_circuit_local S (noteSpendE LE cN hN hLE) noteSpendAAirName s args s'

theorem noteSpend_emitted_refines_spec (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoNullifiers S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : NoteSpendArgs) (s' : RecChainedState)
    (h : noteSpendEmittedStep S LE cN hN hLE s args s') :
    noteSpendSpecStep s args s' :=
  effect2_emitted_refines_bespoke_spec S (noteSpendE LE cN hN hLE) noteSpendAAirName
    (noteSpendCircuitStep S LE cN hN hLE) noteSpendSpecStep
    (noteSpend_circuit_refines_spec S LE cN hN hLE hRest hLog)
    (fun pre args post => noteSpend_emitted_equiv_circuit S LE cN hN hLE pre args post) s args s' h

/-! ## §10 — NoteCreateA. -/

def noteCreateEmittedStep (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : NoteCreateArgs) (s' : RecChainedState) : Prop :=
  effect2EmittedStepLocal S (noteCreateE LE cN hN hLE) noteCreateAAirName s args s'

theorem noteCreate_emitted_equiv_circuit (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : NoteCreateArgs) (s' : RecChainedState) :
    noteCreateEmittedStep S LE cN hN hLE s args s' ↔
      noteCreateCircuitStep S LE cN hN hLE s args s' :=
  effect2_emitted_equiv_circuit_local S (noteCreateE LE cN hN hLE) noteCreateAAirName s args s'

theorem noteCreate_emitted_refines_spec (S : Surface2) (LE : Nat → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoCommitments S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : NoteCreateArgs) (s' : RecChainedState)
    (h : noteCreateEmittedStep S LE cN hN hLE s args s') :
    noteCreateSpecStep s args s' :=
  effect2_emitted_refines_bespoke_spec S (noteCreateE LE cN hN hLE) noteCreateAAirName
    (noteCreateCircuitStep S LE cN hN hLE) noteCreateSpecStep
    (noteCreate_circuit_refines_spec S LE cN hN hLE hRest hLog)
    (fun pre args post => noteCreate_emitted_equiv_circuit S LE cN hN hLE pre args post) s args s' h

/-! ## §12 — Revoke. -/

def revokeEmittedStep (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState) : Prop :=
  effect2EmittedStepLocal S (revokeE D hD) revokeAirName s args s'

theorem revoke_emitted_equiv_circuit (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState) :
    revokeEmittedStep S D hD s args s' ↔ revokeCircuitStep S D hD s args s' :=
  effect2_emitted_equiv_circuit_local S (revokeE D hD) revokeAirName s args s'

theorem revoke_emitted_refines_spec (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.Revoke.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState)
    (h : revokeEmittedStep S D hD s args s') :
    revokeSpecStep s args s' :=
  effect2_emitted_refines_bespoke_spec S (revokeE D hD) revokeAirName
    (revokeCircuitStep S D hD) revokeSpecStep (revoke_circuit_refines_spec S D hD hRest hLog)
    (fun pre args post => revoke_emitted_equiv_circuit S D hD pre args post) s args s' h

/-! ## §13 — SealA. -/

def sealEmittedStep (S : Surface2) (LE : SealedBoxRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : SealArgs) (s' : RecChainedState) : Prop :=
  effect2EmittedStepLocal S (sealE LE cN hN hLE) sealAAirName s args s'

theorem seal_emitted_equiv_circuit (S : Surface2) (LE : SealedBoxRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : SealArgs) (s' : RecChainedState) :
    sealEmittedStep S LE cN hN hLE s args s' ↔ sealCircuitStep S LE cN hN hLE s args s' :=
  effect2_emitted_equiv_circuit_local S (sealE LE cN hN hLE) sealAAirName s args s'

theorem seal_emitted_refines_spec (S : Surface2) (LE : SealedBoxRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoSealedBoxes S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SealArgs) (s' : RecChainedState)
    (h : sealEmittedStep S LE cN hN hLE s args s') :
    sealSpecStep s args s' :=
  effect2_emitted_refines_bespoke_spec S (sealE LE cN hN hLE) sealAAirName
    (sealCircuitStep S LE cN hN hLE) sealSpecStep (seal_circuit_refines_spec S LE cN hN hLE hRest hLog)
    (fun pre args post => seal_emitted_equiv_circuit S LE cN hN hLE pre args post) s args s' h

-- (F2a) §15 QueueEnqueueA emitted diamond DELETED with the queue effect family.

/-! ## §16 — SetFieldA (v1 EffectCommit). -/

def setFieldEmittedStep (S : CommitSurface) (s : RecChainedState) (args : SetFieldArgs)
    (s' : RecChainedState) : Prop :=
  effect1EmittedStepLocal S setFieldE setFieldAirName s args s'

theorem setField_emitted_equiv_circuit (S : CommitSurface) (s : RecChainedState) (args : SetFieldArgs)
    (s' : RecChainedState) :
    setFieldEmittedStep S s args s' ↔ setFieldCircuitStep S s args s' :=
  effect1_emitted_equiv_circuit_local S setFieldE setFieldAirName s args s'

theorem setField_emitted_refines_spec (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SetFieldArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : setFieldEmittedStep S s args s') :
    setFieldSpecStep s args s' :=
  setField_circuit_refines_spec S hN hL hRest hLog s args s' hwf hwf'
    ((setField_emitted_equiv_circuit S s args s').mp h)

/-! ## §17 — ExerciseA hold-gate (v1 EffectCommit). -/

def exerciseHoldEmittedStep (S : CommitSurface) (pre : RecChainedState) (args : ExerciseHoldArgs)
    (post : RecChainedState) : Prop :=
  effect1EmittedStepLocal S exerciseE exerciseAAirName pre args post

theorem exerciseHold_emitted_equiv_circuit (S : CommitSurface) (pre : RecChainedState)
    (args : ExerciseHoldArgs) (post : RecChainedState) :
    exerciseHoldEmittedStep S pre args post ↔ exerciseHoldCircuitStep S pre args post :=
  effect1_emitted_equiv_circuit_local S exerciseE exerciseAAirName pre args post

theorem exerciseHold_emitted_refines_spec (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (pre post : RecChainedState) (args : ExerciseHoldArgs)
    (hwf : AccountsWF pre.kernel) (hwf' : AccountsWF post.kernel)
    (h : exerciseHoldEmittedStep S pre args post) :
    exerciseHoldSpecStep pre args post :=
  exerciseHold_circuit_refines_spec S hN hL hRest hLog pre post args hwf hwf'
    ((exerciseHold_emitted_equiv_circuit S pre args post).mp h)

/-! ## §19 — Batch-2 emitted portals (remaining Inst effects; `sorry` where circuit diamond open). -/

open Dregg2.Circuit.EffectCommit4
  (emitEffect2QuadFaithful emittedEffect2Quad encodeE2Quad EffectSpec2Quad satisfiedE2Quad)
open Dregg2.Circuit.Inst.AttenuateA
  (attenuateE attenuateAAirName AttenuateArgs attenuateA_full_sound)
open Dregg2.Circuit.Inst.EmitEventA
  (emitEventE emitEventAAirName EmitEventArgs emitEventA_full_sound)
open Dregg2.Circuit.Inst.IncrementNonceA
  (incrementNonceE incrementNonceAAirName IncrementNonceArgs incrementNonceA_full_sound)
open Dregg2.Circuit.Inst.SetPermissionsA
  (setPermissionsE setPermissionsAAirName SetPermissionsArgs setPermissionsA_full_sound)
open Dregg2.Circuit.Inst.SetVKA (setVKE setVKAAirName SetVKArgs setVKA_full_sound)
open Dregg2.Circuit.Inst.DelegateAttenA
  (delegateAttenE delegateAttenAAirName DelegateAttenArgs delegateAttenA_full_sound)
open Dregg2.Circuit.Inst.IntroduceA
  (introduceE introduceAAirName IntroduceArgs introduceA_full_sound)
open Dregg2.Circuit.Inst.ValidateHandoffA
  (validateHandoffE validateHandoffAAirName HandoffArgs validateHandoffA_full_sound)
open Dregg2.Circuit.Inst.RevokeDelegationA
  (revokeDelegationE revokeDelegationAAirName revokeDelegationA_full_sound)
open Dregg2.Circuit.Inst.CreateCellFromFactoryA
  (createFromFactoryE createCellFromFactoryAAirName CreateFromFactoryArgs
    createCellFromFactoryA_full_sound CreateFromFactoryCircuitSpec)
open Dregg2.Circuit.Inst.UnsealA (unsealE unsealAAirName UnsealArgs unsealA_full_sound)
open Dregg2.Circuit.Inst.CreateSealPairA
  (createSealPairE createSealPairAAirName CreateSealPairArgs createSealPairA_full_sound)
open Dregg2.Circuit.Inst.MakeSovereignA
  (makeSovereignE makeSovereignAAirName MakeSovereignArgs makeSovereignA_full_sound)
open Dregg2.Circuit.Inst.RefusalA (refusalE refusalAAirName RefusalArgs refusalA_full_sound)
open Dregg2.Circuit.Inst.ReceiptArchiveA
  (receiptArchiveE receiptArchiveAAirName ReceiptArchiveArgs receiptArchiveA_full_sound)
open Dregg2.Circuit.Inst.PipelinedSendA
  (pipelinedSendE pipelinedSendAAirName PipelinedSendArgs pipelinedSendA_full_sound)
open Dregg2.Circuit.Inst.SwissExportA
  (swissExportE swissExportAAirName ExportArgs RestIffNoSwiss swissExportA_full_sound)
open Dregg2.Circuit.Inst.EnlivenRefA
  (enlivenE enlivenRefAAirName EnlivenArgs enlivenRefA_full_sound)
open Dregg2.Circuit.Inst.SwissHandoffA (swissHandoffE swissHandoffAAirName swissHandoffA_full_sound)
open Dregg2.Circuit.Inst.SwissDropA (swissDropE swissDropAAirName DropArgs swissDropA_full_sound)
open Dregg2.Circuit.Inst.CellSealA (cellSealE cellSealAAirName CellSealArgs cellSealA_full_sound)
open Dregg2.Circuit.Inst.CellUnsealA
  (cellUnsealE cellUnsealAAirName CellUnsealArgs cellUnsealA_full_sound)
open Dregg2.Circuit.Inst.CellDestroyA
  (cellDestroyE cellDestroyAAirName CellDestroyArgs RestIffNoLifecycleDeathCert
    cellDestroyA_full_sound)
open Dregg2.Circuit.Inst.RefreshDelegationA
  (refreshDelegationE refreshDelegationAAirName RefreshDelegationArgs RestIffNoDelegations
    refreshDelegationA_full_sound)
open Dregg2.Circuit.Spec.AuthorityAttenuation (AttenuateSpec DelegateAttenSpec)
open Dregg2.Circuit.Spec.CellStateLog (EmitEventSpec)
open Dregg2.Circuit.Spec.CellStateMonotone (IncrementNonceSpec)
open Dregg2.Circuit.Spec.CellStatePermissions (SetPermissionsSpec)
open Dregg2.Circuit.Spec.CellStateVK (SetVKSpec)
open Dregg2.Circuit.Spec.AuthorityUnattenuated (DelegateSpec)
open Dregg2.Circuit.Spec.AuthorityRevocation (RevokeSpec)
open Dregg2.Circuit.Spec.FactoryCreation (CreateFromFactorySpec)
open Dregg2.Circuit.Spec.SealBoxOperations (UnsealSpec)
open Dregg2.Circuit.Spec.SealPairCreation (CreateSealPairSpec)
open Dregg2.Circuit.Spec.SovereignCommitment (MakeSovereignSpec)
open Dregg2.Circuit.Spec.CellStateAudit (RefusalSpec ReceiptArchiveSpec)
open Dregg2.Circuit.Spec.QueuePipelinedSend (PipelinedSendSpec)
open Dregg2.Circuit.Spec.SwissExport (ExportSpec)
open Dregg2.Circuit.Spec.SwissEnliven (EnlivenSpec)
open Dregg2.Circuit.Spec.SwissHandoff (HandoffSpec)
open Dregg2.Circuit.Spec.SwissDrop (DropSpec)
open Dregg2.Circuit.Spec.CellLifecycle (CellSealSpec CellUnsealSpec CellDestroySpec)
open Dregg2.Circuit.Spec.RefreshDelegation (RefreshDelegationSpec)

-- Batch-2 effects: emitted portals composed through Inst `*_full_sound` diamonds.
def attenuateAEmittedStep (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : AttenuateArgs) (s' : RecChainedState) : Prop :=
  effect2EmittedStepLocal S (attenuateE D hD) attenuateAAirName s args s'

theorem attenuateA_emitted_equiv_circuit (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : AttenuateArgs) (s' : RecChainedState) :
    attenuateAEmittedStep S D hD s args s' ↔ effect2CircuitStep S (attenuateE D hD) s args s' :=
  effect2_emitted_equiv_circuit_local S (attenuateE D hD) attenuateAAirName s args s'

theorem attenuateA_emitted_refines_spec (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.AttenuateA.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : AttenuateArgs) (s' : RecChainedState)
    (h : attenuateAEmittedStep S D hD s args s') :
    AttenuateSpec s args.actor args.idx args.keep s' :=
  effect2_emitted_refines_bespoke_spec S (attenuateE D hD) attenuateAAirName
    (fun pre args post => satisfiedE2 S (attenuateE D hD) (encodeE2 S (attenuateE D hD) pre args post))
    (fun pre args post => AttenuateSpec pre args.actor args.idx args.keep post)
    (fun pre args post hc => attenuateA_full_sound S D hD hRest hLog pre args post hc)
    (fun pre args post => attenuateA_emitted_equiv_circuit S D hD pre args post)
    s args s' h

def emitEventAEmittedStep (S : CommitSurface) (s : RecChainedState) (args : EmitEventArgs)
    (s' : RecChainedState) : Prop :=
  effect1EmittedStepLocal S emitEventE emitEventAAirName s args s'

theorem emitEventA_emitted_equiv_circuit (S : CommitSurface) (s : RecChainedState) (args : EmitEventArgs)
    (s' : RecChainedState) :
    emitEventAEmittedStep S s args s' ↔ effect1CircuitStepLocal S emitEventE s args s' :=
  effect1_emitted_equiv_circuit_local S emitEventE emitEventAAirName s args s'

theorem emitEventA_emitted_refines_spec (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : EmitEventArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : emitEventAEmittedStep S s args s') :
    EmitEventSpec s args.actor args.cell args.topic args.data s' :=
  emitEventA_full_sound S hN hL hRest hLog s args s' hwf hwf'
    ((effect1_emitted_equiv_circuit_local S emitEventE emitEventAAirName s args s').mp h)

def incrementNonceAEmittedStep (S : CommitSurface) (s : RecChainedState) (args : IncrementNonceArgs)
    (s' : RecChainedState) : Prop :=
  effect1EmittedStepLocal S incrementNonceE incrementNonceAAirName s args s'

theorem incrementNonceA_emitted_refines_spec (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : IncrementNonceArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : incrementNonceAEmittedStep S s args s') :
    IncrementNonceSpec s args.actor args.cell args.n s' :=
  incrementNonceA_full_sound S hN hL hRest hLog s args s' hwf hwf'
    ((effect1_emitted_equiv_circuit_local S incrementNonceE incrementNonceAAirName s args s').mp h)

def setPermissionsAEmittedStep (S : CommitSurface) (s : RecChainedState) (args : SetPermissionsArgs)
    (s' : RecChainedState) : Prop :=
  effect1EmittedStepLocal S setPermissionsE setPermissionsAAirName s args s'

theorem setPermissionsA_emitted_refines_spec (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SetPermissionsArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : setPermissionsAEmittedStep S s args s') :
    SetPermissionsSpec s args.actor args.cell args.p s' :=
  setPermissionsA_full_sound S hN hL hRest hLog s args s' hwf hwf'
    ((effect1_emitted_equiv_circuit_local S setPermissionsE setPermissionsAAirName s args s').mp h)

def setVKAEmittedStep (S : CommitSurface) (s : RecChainedState) (args : SetVKArgs)
    (s' : RecChainedState) : Prop :=
  effect1EmittedStepLocal S setVKE setVKAAirName s args s'

theorem setVKA_emitted_refines_spec (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SetVKArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : setVKAEmittedStep S s args s') :
    SetVKSpec s args.actor args.cell args.vk s' :=
  setVKA_full_sound S hN hL hRest hLog s args s' hwf hwf'
    ((effect1_emitted_equiv_circuit_local S setVKE setVKAAirName s args s').mp h)

def delegateAttenAEmittedStep (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : DelegateAttenArgs) (s' : RecChainedState) : Prop :=
  effect2EmittedStepLocal S (delegateAttenE D hD) delegateAttenAAirName s args s'

theorem delegateAttenA_emitted_equiv_circuit (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : DelegateAttenArgs) (s' : RecChainedState) :
    delegateAttenAEmittedStep S D hD s args s' ↔
      effect2CircuitStep S (delegateAttenE D hD) s args s' :=
  effect2_emitted_equiv_circuit_local S (delegateAttenE D hD) delegateAttenAAirName s args s'

theorem delegateAttenA_emitted_refines_spec (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.DelegateAttenA.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : DelegateAttenArgs) (s' : RecChainedState)
    (h : delegateAttenAEmittedStep S D hD s args s') :
    DelegateAttenSpec s args.del args.recv args.t args.keep s' :=
  effect2_emitted_refines_bespoke_spec S (delegateAttenE D hD) delegateAttenAAirName
    (fun pre args post =>
      satisfiedE2 S (delegateAttenE D hD) (encodeE2 S (delegateAttenE D hD) pre args post))
    (fun pre args post => DelegateAttenSpec pre args.del args.recv args.t args.keep post)
    (fun pre args post hc => delegateAttenA_full_sound S D hD hRest hLog pre args post hc)
    (fun pre args post => delegateAttenA_emitted_equiv_circuit S D hD pre args post)
    s args s' h

def introduceAEmittedStep (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : IntroduceArgs) (s' : RecChainedState) : Prop :=
  effect2EmittedStepLocal S (introduceE D hD) introduceAAirName s args s'

theorem introduceA_emitted_equiv_circuit (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : IntroduceArgs) (s' : RecChainedState) :
    introduceAEmittedStep S D hD s args s' ↔ effect2CircuitStep S (introduceE D hD) s args s' :=
  effect2_emitted_equiv_circuit_local S (introduceE D hD) introduceAAirName s args s'

theorem introduceA_emitted_refines_spec (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.IntroduceA.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : IntroduceArgs) (s' : RecChainedState)
    (h : introduceAEmittedStep S D hD s args s') :
    DelegateSpec s args.intro args.recip args.t s' :=
  effect2_emitted_refines_bespoke_spec S (introduceE D hD) introduceAAirName
    (fun pre args post =>
      satisfiedE2 S (introduceE D hD) (encodeE2 S (introduceE D hD) pre args post))
    (fun pre args post => DelegateSpec pre args.intro args.recip args.t post)
    (fun pre args post hc => introduceA_full_sound S D hD hRest hLog pre args post hc)
    (fun pre args post => introduceA_emitted_equiv_circuit S D hD pre args post)
    s args s' h

def validateHandoffAEmittedStep (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : HandoffArgs) (s' : RecChainedState) : Prop :=
  effect2EmittedStepLocal S (validateHandoffE D hD) validateHandoffAAirName s args s'

theorem validateHandoffA_emitted_equiv_circuit (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : HandoffArgs) (s' : RecChainedState) :
    validateHandoffAEmittedStep S D hD s args s' ↔
      effect2CircuitStep S (validateHandoffE D hD) s args s' :=
  effect2_emitted_equiv_circuit_local S (validateHandoffE D hD) validateHandoffAAirName s args s'

theorem validateHandoffA_emitted_refines_spec (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.ValidateHandoffA.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : HandoffArgs) (s' : RecChainedState)
    (h : validateHandoffAEmittedStep S D hD s args s') :
    DelegateSpec s args.intro args.recip args.tgt s' :=
  effect2_emitted_refines_bespoke_spec S (validateHandoffE D hD) validateHandoffAAirName
    (fun pre args post =>
      satisfiedE2 S (validateHandoffE D hD) (encodeE2 S (validateHandoffE D hD) pre args post))
    (fun pre args post => DelegateSpec pre args.intro args.recip args.tgt post)
    (fun pre args post hc => validateHandoffA_full_sound S D hD hRest hLog pre args post hc)
    (fun pre args post => validateHandoffA_emitted_equiv_circuit S D hD pre args post)
    s args s' h

def revokeDelegationAEmittedStep (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : Dregg2.Circuit.Inst.RevokeDelegationA.RevokeArgs) (s' : RecChainedState) : Prop :=
  effect2EmittedStepLocal S (revokeDelegationE D hD) revokeDelegationAAirName s args s'

theorem revokeDelegationA_emitted_equiv_circuit (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : Dregg2.Circuit.Inst.RevokeDelegationA.RevokeArgs)
    (s' : RecChainedState) :
    revokeDelegationAEmittedStep S D hD s args s' ↔
      effect2CircuitStep S (revokeDelegationE D hD) s args s' :=
  effect2_emitted_equiv_circuit_local S (revokeDelegationE D hD) revokeDelegationAAirName s args s'

theorem revokeDelegationA_emitted_refines_spec (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.RevokeDelegationA.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Dregg2.Circuit.Inst.RevokeDelegationA.RevokeArgs) (s' : RecChainedState)
    (h : revokeDelegationAEmittedStep S D hD s args s') :
    RevokeSpec s args.holder args.t s' :=
  effect2_emitted_refines_bespoke_spec S (revokeDelegationE D hD) revokeDelegationAAirName
    (fun pre args post =>
      satisfiedE2 S (revokeDelegationE D hD) (encodeE2 S (revokeDelegationE D hD) pre args post))
    (fun pre args post => RevokeSpec pre args.holder args.t post)
    (fun pre args post hc => revokeDelegationA_full_sound S D hD hRest hLog pre args post hc)
    (fun pre args post => revokeDelegationA_emitted_equiv_circuit S D hD pre args post)
    s args s' h

def createCellFromFactoryAEmittedStep (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth)
    (s : RecChainedState) (args : CreateFromFactoryArgs) (s' : RecChainedState) : Prop :=
  effect2quintEmittedStepLocal S
    (createFromFactoryE LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth)
    createCellFromFactoryAAirName s args s'

theorem createCellFromFactoryA_emitted_refines_spec (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (DBal : (CellId → AssetId → ℤ) → ℤ) (hDBal : Function.Injective DBal)
    (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DSC : (CellId → List SlotCaveat) → ℤ) (hDSC : Function.Injective DSC)
    (DAuth : BornEmptyAuthorityTables → ℤ) (hDAuth : Function.Injective DAuth)
    (hRest : Dregg2.Circuit.Inst.CreateCellFromFactoryA.RestIffNoFactoryTouched S.RH)
    (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CreateFromFactoryArgs) (s' : RecChainedState)
    (h : createCellFromFactoryAEmittedStep S LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth
      s args s') :
    CreateFromFactorySpec s args.actor args.newCell args.vk s' := by
  -- emitted ↔ satisfiedE2Quint (faithful decode), then the validated `full_sound` apex spec, then the
  -- born-empty-authority bridge back to the declarative `CreateFromFactorySpec`.
  have hsat :
      satisfiedE2Quint S
        (createFromFactoryE LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth)
        (encodeE2Quint S
          (createFromFactoryE LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth) s args s') :=
    (effect2quint_emitted_equiv_circuit_local S
      (createFromFactoryE LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth)
      createCellFromFactoryAAirName s args s').mp h
  have hapex : CreateFromFactoryCircuitSpec s args.actor args.newCell args.vk s' :=
    createCellFromFactoryA_full_sound S LE cN hN hLE DBal hDBal DCell hDCell DSC hDSC DAuth hDAuth
      hRest hLog s args s' hsat
  -- reverse born-empty-authority bridge (apex circuit spec ⟹ declarative spec).
  obtain ⟨e, hadmit, hacc, hbal, hcell, hsc, hauth, hlog, hNull, hRev, hCom, hQ, hSw, hFac, hSB⟩ :=
    hapex
  obtain ⟨hcaps, hlif, hdc, hdel, hdgs⟩ :=
    (bornEmptyAuthority_post_iff s.kernel args.newCell s'.kernel).mp hauth
  exact ⟨e, hadmit, hacc, hbal, hcell, hsc, hlog, hcaps, hlif, hdc, hdel, hdgs, hNull, hRev, hCom,
    hQ, hSw, hFac, hSB⟩

def unsealAEmittedStep (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : UnsealArgs) (s' : RecChainedState) : Prop :=
  effect2EmittedStepLocal S (unsealE D hD) unsealAAirName s args s'

theorem unsealA_emitted_equiv_circuit (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : UnsealArgs) (s' : RecChainedState) :
    unsealAEmittedStep S D hD s args s' ↔ effect2CircuitStep S (unsealE D hD) s args s' :=
  effect2_emitted_equiv_circuit_local S (unsealE D hD) unsealAAirName s args s'

theorem unsealA_emitted_refines_spec (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.UnsealA.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : UnsealArgs) (s' : RecChainedState)
    (h : unsealAEmittedStep S D hD s args s') :
    UnsealSpec s args.pid args.actor args.recipient args.box s' :=
  effect2_emitted_refines_bespoke_spec S (unsealE D hD) unsealAAirName
    (fun pre args post => satisfiedE2 S (unsealE D hD) (encodeE2 S (unsealE D hD) pre args post))
    (fun pre args post => UnsealSpec pre args.pid args.actor args.recipient args.box post)
    (fun pre args post hc => unsealA_full_sound S D hD hRest hLog pre args post hc)
    (fun pre args post => unsealA_emitted_equiv_circuit S D hD pre args post)
    s args s' h

def createSealPairAEmittedStep (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : CreateSealPairArgs) (s' : RecChainedState) : Prop :=
  effect2EmittedStepLocal S (createSealPairE D hD) createSealPairAAirName s args s'

theorem createSealPairA_emitted_equiv_circuit (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (s : RecChainedState) (args : CreateSealPairArgs) (s' : RecChainedState) :
    createSealPairAEmittedStep S D hD s args s' ↔
      effect2CircuitStep S (createSealPairE D hD) s args s' :=
  effect2_emitted_equiv_circuit_local S (createSealPairE D hD) createSealPairAAirName s args s'

theorem createSealPairA_emitted_refines_spec (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.CreateSealPairA.RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CreateSealPairArgs) (s' : RecChainedState)
    (h : createSealPairAEmittedStep S D hD s args s') :
    CreateSealPairSpec s args.pid args.actor args.sealerHolder args.unsealerHolder s' :=
  effect2_emitted_refines_bespoke_spec S (createSealPairE D hD) createSealPairAAirName
    (fun pre args post =>
      satisfiedE2 S (createSealPairE D hD) (encodeE2 S (createSealPairE D hD) pre args post))
    (fun pre args post =>
      CreateSealPairSpec pre args.pid args.actor args.sealerHolder args.unsealerHolder post)
    (fun pre args post hc => createSealPairA_full_sound S D hD hRest hLog pre args post hc)
    (fun pre args post => createSealPairA_emitted_equiv_circuit S D hD pre args post)
    s args s' h

def makeSovereignAEmittedStep (S : CommitSurface) (s : RecChainedState) (args : MakeSovereignArgs)
    (s' : RecChainedState) : Prop :=
  effect1EmittedStepLocal S makeSovereignE makeSovereignAAirName s args s'

theorem makeSovereignA_emitted_refines_spec (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : MakeSovereignArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : makeSovereignAEmittedStep S s args s') :
    MakeSovereignSpec s args.actor args.cell s' :=
  makeSovereignA_full_sound S hN hL hRest hLog s args s' hwf hwf'
    ((effect1_emitted_equiv_circuit_local S makeSovereignE makeSovereignAAirName s args s').mp h)

def refusalAEmittedStep (S : CommitSurface) (s : RecChainedState) (args : RefusalArgs)
    (s' : RecChainedState) : Prop :=
  effect1EmittedStepLocal S refusalE refusalAAirName s args s'

theorem refusalA_emitted_refines_spec (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RefusalArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : refusalAEmittedStep S s args s') :
    RefusalSpec s args.actor args.cell s' :=
  refusalA_full_sound S hN hL hRest hLog s args s' hwf hwf'
    ((effect1_emitted_equiv_circuit_local S refusalE refusalAAirName s args s').mp h)

def receiptArchiveAEmittedStep (S : CommitSurface) (s : RecChainedState) (args : ReceiptArchiveArgs)
    (s' : RecChainedState) : Prop :=
  effect1EmittedStepLocal S receiptArchiveE receiptArchiveAAirName s args s'

theorem receiptArchiveA_emitted_refines_spec (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : ReceiptArchiveArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : receiptArchiveAEmittedStep S s args s') :
    ReceiptArchiveSpec s args.actor args.cell s' :=
  receiptArchiveA_full_sound S hN hL hRest hLog s args s' hwf hwf'
    ((effect1_emitted_equiv_circuit_local S receiptArchiveE receiptArchiveAAirName s args s').mp h)

-- (F2a) the queueAllocate/Dequeue/Resize/AtomicTx/PipelineStep emitted steps DELETED with the queue family.

def pipelinedSendAEmittedStep (S : CommitSurface) (s : RecChainedState) (args : PipelinedSendArgs)
    (s' : RecChainedState) : Prop :=
  effect1EmittedStepLocal S pipelinedSendE pipelinedSendAAirName s args s'

theorem pipelinedSendA_emitted_refines_spec (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : PipelinedSendArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : pipelinedSendAEmittedStep S s args s') :
    PipelinedSendSpec s args.actor s' :=
  pipelinedSendA_full_sound S hN hL hRest hLog s args s' hwf hwf'
    ((effect1_emitted_equiv_circuit_local S pipelinedSendE pipelinedSendAAirName s args s').mp h)

def exportSturdyRefAEmittedStep (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : ExportArgs) (s' : RecChainedState) : Prop :=
  effect2EmittedStepLocal S (swissExportE LE cN hN hLE) swissExportAAirName s args s'

theorem exportSturdyRefA_emitted_equiv_circuit (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : ExportArgs) (s' : RecChainedState) :
    exportSturdyRefAEmittedStep S LE cN hN hLE s args s' ↔
      effect2CircuitStep S (swissExportE LE cN hN hLE) s args s' :=
  effect2_emitted_equiv_circuit_local S (swissExportE LE cN hN hLE) swissExportAAirName s args s'

theorem exportSturdyRefA_emitted_refines_spec (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoSwiss S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : ExportArgs) (s' : RecChainedState)
    (h : exportSturdyRefAEmittedStep S LE cN hN hLE s args s') :
    ExportSpec s args.sw args.actor args.exporter args.target args.rights s' :=
  effect2_emitted_refines_bespoke_spec S (swissExportE LE cN hN hLE) swissExportAAirName
    (fun pre args post =>
      satisfiedE2 S (swissExportE LE cN hN hLE)
        (encodeE2 S (swissExportE LE cN hN hLE) pre args post))
    (fun pre args post =>
      ExportSpec pre args.sw args.actor args.exporter args.target args.rights post)
    (fun pre args post hc => swissExportA_full_sound S LE cN hN hLE hRest hLog pre args post hc)
    (fun pre args post => exportSturdyRefA_emitted_equiv_circuit S LE cN hN hLE pre args post)
    s args s' h

def enlivenRefAEmittedStep (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : EnlivenArgs) (s' : RecChainedState) : Prop :=
  effect2EmittedStepLocal S (enlivenE LE cN hN hLE) enlivenRefAAirName s args s'

theorem enlivenRefA_emitted_equiv_circuit (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : EnlivenArgs) (s' : RecChainedState) :
    enlivenRefAEmittedStep S LE cN hN hLE s args s' ↔
      effect2CircuitStep S (enlivenE LE cN hN hLE) s args s' :=
  effect2_emitted_equiv_circuit_local S (enlivenE LE cN hN hLE) enlivenRefAAirName s args s'

theorem enlivenRefA_emitted_refines_spec (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : Dregg2.Circuit.Inst.EnlivenRefA.RestIffNoSwiss S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : EnlivenArgs) (s' : RecChainedState)
    (h : enlivenRefAEmittedStep S LE cN hN hLE s args s') :
    EnlivenSpec s args.sw args.actor args.exporter args.claimed s' :=
  effect2_emitted_refines_bespoke_spec S (enlivenE LE cN hN hLE) enlivenRefAAirName
    (fun pre args post =>
      satisfiedE2 S (enlivenE LE cN hN hLE) (encodeE2 S (enlivenE LE cN hN hLE) pre args post))
    (fun pre args post => EnlivenSpec pre args.sw args.actor args.exporter args.claimed post)
    (fun pre args post hc => enlivenRefA_full_sound S LE cN hN hLE hRest hLog pre args post hc)
    (fun pre args post => enlivenRefA_emitted_equiv_circuit S LE cN hN hLE pre args post)
    s args s' h

def swissHandoffAEmittedStep (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : Dregg2.Circuit.Inst.SwissHandoffA.HandoffArgs) (s' : RecChainedState) : Prop :=
  effect2EmittedStepLocal S (swissHandoffE LE cN hN hLE) swissHandoffAAirName s args s'

theorem swissHandoffA_emitted_equiv_circuit (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : Dregg2.Circuit.Inst.SwissHandoffA.HandoffArgs) (s' : RecChainedState) :
    swissHandoffAEmittedStep S LE cN hN hLE s args s' ↔
      effect2CircuitStep S (swissHandoffE LE cN hN hLE) s args s' :=
  effect2_emitted_equiv_circuit_local S (swissHandoffE LE cN hN hLE) swissHandoffAAirName s args s'

theorem swissHandoffA_emitted_refines_spec (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : Dregg2.Circuit.Inst.SwissHandoffA.RestIffNoSwiss S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Dregg2.Circuit.Inst.SwissHandoffA.HandoffArgs) (s' : RecChainedState)
    (h : swissHandoffAEmittedStep S LE cN hN hLE s args s') :
    HandoffSpec s args.sw args.certHash args.introducer args.exporter s' :=
  effect2_emitted_refines_bespoke_spec S (swissHandoffE LE cN hN hLE) swissHandoffAAirName
    (fun pre args post =>
      satisfiedE2 S (swissHandoffE LE cN hN hLE)
        (encodeE2 S (swissHandoffE LE cN hN hLE) pre args post))
    (fun pre args post =>
      HandoffSpec pre args.sw args.certHash args.introducer args.exporter post)
    (fun pre args post hc => swissHandoffA_full_sound S LE cN hN hLE hRest hLog pre args post hc)
    (fun pre args post => swissHandoffA_emitted_equiv_circuit S LE cN hN hLE pre args post)
    s args s' h

def swissDropAEmittedStep (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : DropArgs) (s' : RecChainedState) : Prop :=
  effect2EmittedStepLocal S (swissDropE LE cN hN hLE) swissDropAAirName s args s'

theorem swissDropA_emitted_equiv_circuit (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : DropArgs) (s' : RecChainedState) :
    swissDropAEmittedStep S LE cN hN hLE s args s' ↔
      effect2CircuitStep S (swissDropE LE cN hN hLE) s args s' :=
  effect2_emitted_equiv_circuit_local S (swissDropE LE cN hN hLE) swissDropAAirName s args s'

theorem swissDropA_emitted_refines_spec (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : Dregg2.Circuit.Inst.SwissDropA.RestIffNoSwiss S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : DropArgs) (s' : RecChainedState)
    (h : swissDropAEmittedStep S LE cN hN hLE s args s') :
    DropSpec s args.sw args.actor args.exporter s' :=
  effect2_emitted_refines_bespoke_spec S (swissDropE LE cN hN hLE) swissDropAAirName
    (fun pre args post =>
      satisfiedE2 S (swissDropE LE cN hN hLE) (encodeE2 S (swissDropE LE cN hN hLE) pre args post))
    (fun pre args post => DropSpec pre args.sw args.actor args.exporter post)
    (fun pre args post hc => swissDropA_full_sound S LE cN hN hLE hRest hLog pre args post hc)
    (fun pre args post => swissDropA_emitted_equiv_circuit S LE cN hN hLE pre args post)
    s args s' h

def cellSealAEmittedStep (S : Surface2) (DLife : (CellId → Nat) → ℤ)
    (hDLife : Function.Injective DLife) (s : RecChainedState) (args : CellSealArgs)
    (s' : RecChainedState) : Prop :=
  effect2EmittedStepLocal S (cellSealE DLife hDLife) cellSealAAirName s args s'

theorem cellSealA_emitted_equiv_circuit (S : Surface2) (DLife : (CellId → Nat) → ℤ)
    (hDLife : Function.Injective DLife) (s : RecChainedState) (args : CellSealArgs)
    (s' : RecChainedState) :
    cellSealAEmittedStep S DLife hDLife s args s' ↔
      effect2CircuitStep S (cellSealE DLife hDLife) s args s' :=
  effect2_emitted_equiv_circuit_local S (cellSealE DLife hDLife) cellSealAAirName s args s'

theorem cellSealA_emitted_refines_spec (S : Surface2) (DLife : (CellId → Nat) → ℤ)
    (hDLife : Function.Injective DLife)
    (hRest : Dregg2.Circuit.Inst.CellSealA.RestIffNoLifecycle S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CellSealArgs) (s' : RecChainedState)
    (h : cellSealAEmittedStep S DLife hDLife s args s') :
    CellSealSpec s args.actor args.cell s' :=
  effect2_emitted_refines_bespoke_spec S (cellSealE DLife hDLife) cellSealAAirName
    (fun pre args post =>
      satisfiedE2 S (cellSealE DLife hDLife) (encodeE2 S (cellSealE DLife hDLife) pre args post))
    (fun pre args post => CellSealSpec pre args.actor args.cell post)
    (fun pre args post hc => cellSealA_full_sound S DLife hDLife hRest hLog pre args post hc)
    (fun pre args post => cellSealA_emitted_equiv_circuit S DLife hDLife pre args post)
    s args s' h

def cellUnsealAEmittedStep (S : Surface2) (DLife : (CellId → Nat) → ℤ)
    (hDLife : Function.Injective DLife) (s : RecChainedState) (args : CellUnsealArgs)
    (s' : RecChainedState) : Prop :=
  effect2EmittedStepLocal S (cellUnsealE DLife hDLife) cellUnsealAAirName s args s'

theorem cellUnsealA_emitted_equiv_circuit (S : Surface2) (DLife : (CellId → Nat) → ℤ)
    (hDLife : Function.Injective DLife) (s : RecChainedState) (args : CellUnsealArgs)
    (s' : RecChainedState) :
    cellUnsealAEmittedStep S DLife hDLife s args s' ↔
      effect2CircuitStep S (cellUnsealE DLife hDLife) s args s' :=
  effect2_emitted_equiv_circuit_local S (cellUnsealE DLife hDLife) cellUnsealAAirName s args s'

theorem cellUnsealA_emitted_refines_spec (S : Surface2) (DLife : (CellId → Nat) → ℤ)
    (hDLife : Function.Injective DLife)
    (hRest : Dregg2.Circuit.Inst.CellUnsealA.RestIffNoLifecycle S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CellUnsealArgs) (s' : RecChainedState)
    (h : cellUnsealAEmittedStep S DLife hDLife s args s') :
    CellUnsealSpec s args.actor args.cell s' :=
  effect2_emitted_refines_bespoke_spec S (cellUnsealE DLife hDLife) cellUnsealAAirName
    (fun pre args post =>
      satisfiedE2 S (cellUnsealE DLife hDLife) (encodeE2 S (cellUnsealE DLife hDLife) pre args post))
    (fun pre args post => CellUnsealSpec pre args.actor args.cell post)
    (fun pre args post hc => cellUnsealA_full_sound S DLife hDLife hRest hLog pre args post hc)
    (fun pre args post => cellUnsealA_emitted_equiv_circuit S DLife hDLife pre args post)
    s args s' h

def cellDestroyAEmittedStep (S : Surface2) (DLife : (CellId → Nat) → ℤ)
    (hDLife : Function.Injective DLife) (DDeath : (CellId → Nat) → ℤ)
    (hDDeath : Function.Injective DDeath)
    (s : RecChainedState) (args : CellDestroyArgs) (s' : RecChainedState) : Prop :=
  effect2dualEmittedStepLocal S (cellDestroyE DLife hDLife DDeath hDDeath) cellDestroyAAirName s args s'

theorem cellDestroyA_emitted_equiv_circuit (S : Surface2) (DLife : (CellId → Nat) → ℤ)
    (hDLife : Function.Injective DLife) (DDeath : (CellId → Nat) → ℤ)
    (hDDeath : Function.Injective DDeath) (s : RecChainedState) (args : CellDestroyArgs)
    (s' : RecChainedState) :
    cellDestroyAEmittedStep S DLife hDLife DDeath hDDeath s args s' ↔
      satisfiedE2Dual S (cellDestroyE DLife hDLife DDeath hDDeath)
        (encodeE2Dual S (cellDestroyE DLife hDLife DDeath hDDeath) s args s') :=
  effect2dual_emitted_equiv_circuit_local S (cellDestroyE DLife hDLife DDeath hDDeath) cellDestroyAAirName
    s args s'

theorem cellDestroyA_emitted_refines_spec (S : Surface2) (DLife : (CellId → Nat) → ℤ)
    (hDLife : Function.Injective DLife) (DDeath : (CellId → Nat) → ℤ)
    (hDDeath : Function.Injective DDeath)
    (hRest : RestIffNoLifecycleDeathCert S.RH)
    (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CellDestroyArgs) (s' : RecChainedState)
    (h : cellDestroyAEmittedStep S DLife hDLife DDeath hDDeath s args s') :
    CellDestroySpec s args.actor args.cell args.certHash s' :=
  effect2dual_emitted_refines_bespoke_spec S (cellDestroyE DLife hDLife DDeath hDDeath) cellDestroyAAirName
    (fun pre args post =>
      satisfiedE2Dual S (cellDestroyE DLife hDLife DDeath hDDeath)
        (encodeE2Dual S (cellDestroyE DLife hDLife DDeath hDDeath) pre args post))
    (fun pre args post => CellDestroySpec pre args.actor args.cell args.certHash post)
    (fun pre args post hc =>
      cellDestroyA_full_sound S DLife hDLife DDeath hDDeath hRest hLog pre args post hc)
    (fun pre args post =>
      cellDestroyA_emitted_equiv_circuit S DLife hDLife DDeath hDDeath pre args post)
    s args s' h

def refreshDelegationAEmittedStep (S : Surface2) (DDel : (CellId → List Cap) → ℤ)
    (hDDel : Function.Injective DDel) (s : RecChainedState) (args : RefreshDelegationArgs)
    (s' : RecChainedState) : Prop :=
  effect2EmittedStepLocal S (refreshDelegationE DDel hDDel) refreshDelegationAAirName s args s'

theorem refreshDelegationA_emitted_equiv_circuit (S : Surface2) (DDel : (CellId → List Cap) → ℤ)
    (hDDel : Function.Injective DDel) (s : RecChainedState) (args : RefreshDelegationArgs)
    (s' : RecChainedState) :
    refreshDelegationAEmittedStep S DDel hDDel s args s' ↔
      effect2CircuitStep S (refreshDelegationE DDel hDDel) s args s' :=
  effect2_emitted_equiv_circuit_local S (refreshDelegationE DDel hDDel) refreshDelegationAAirName s args s'

theorem refreshDelegationA_emitted_refines_spec (S : Surface2) (DDel : (CellId → List Cap) → ℤ)
    (hDDel : Function.Injective DDel)
    (hRest : RestIffNoDelegations S.RH)
    (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RefreshDelegationArgs) (s' : RecChainedState)
    (h : refreshDelegationAEmittedStep S DDel hDDel s args s') :
    RefreshDelegationSpec s args.actor args.child s' :=
  effect2_emitted_refines_bespoke_spec S (refreshDelegationE DDel hDDel) refreshDelegationAAirName
    (fun pre args post =>
      satisfiedE2 S (refreshDelegationE DDel hDDel)
        (encodeE2 S (refreshDelegationE DDel hDDel) pre args post))
    (fun pre args post => RefreshDelegationSpec pre args.actor args.child post)
    (fun pre args post hc => refreshDelegationA_full_sound S DDel hDDel hRest hLog pre args post hc)
    (fun pre args post => refreshDelegationA_emitted_equiv_circuit S DDel hDDel pre args post)
    s args s' h

/-! ## §18 — Axiom hygiene. -/

#assert_axioms bespoke_emitted_refines_spec
#assert_axioms effect2_emitted_refines_bespoke_spec
#assert_axioms effect1_emitted_refines_bespoke_spec
#assert_axioms effect2dual_emitted_refines_bespoke_spec
#assert_axioms effect2triple_emitted_refines_bespoke_spec
#assert_axioms effect2quint_emitted_refines_bespoke_spec
#assert_axioms mint_emitted_refines_spec
#assert_axioms burn_emitted_refines_spec
#assert_axioms createCell_emitted_refines_spec
#assert_axioms spawn_emitted_refines_spec
#assert_axioms transfer_emitted_refines_spec
#assert_axioms balanceA_emitted_refines_spec
#assert_axioms delegate_emitted_refines_spec
#assert_axioms noteSpend_emitted_refines_spec
#assert_axioms noteCreate_emitted_refines_spec
#assert_axioms revoke_emitted_refines_spec
#assert_axioms seal_emitted_refines_spec
#assert_axioms setField_emitted_refines_spec
#assert_axioms exerciseHold_emitted_refines_spec
#assert_axioms createCellFromFactoryA_emitted_refines_spec

end Dregg2.Circuit.EffectEmittedRefinement