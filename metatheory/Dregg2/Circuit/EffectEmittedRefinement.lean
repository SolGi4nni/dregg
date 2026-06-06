/-
# Dregg2.Circuit.EffectEmittedRefinement — Wave 2 batch emitted→spec refinement.

Extends `EffectRefinement.lean`'s circuit diamonds to the Plonky3 emitted wire layer: for every
effect with `*_circuit_refines_spec`, proves `*_emitted_refines_spec` (emitted ⊑ bespoke spec) via
the generic `emitted ⟺ circuit` faithfulness lemmas + circuit soundness.

No `sorry`/`admit`/`native_decide`/`axiom`.
-/
import Dregg2.Circuit.EffectRefinement
import Dregg2.Circuit.EffectEmitRegistry
import Dregg2.Circuit.EffectCommit
import Dregg2.Circuit.EffectCommit2
import Dregg2.Circuit.EffectCommit2Dual
import Dregg2.Circuit.EffectCommit3
import Dregg2.Circuit.EffectCommit5
import Dregg2.Circuit.SetFieldCommit
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
import Dregg2.Circuit.Inst.exerciseA

namespace Dregg2.Circuit.EffectEmittedRefinement

open Dregg2.Circuit
open Dregg2.Circuit.Refinement (StepRel)
open Dregg2.Circuit.EffectRefinement
open Dregg2.Circuit.EffectCommit
  (emitEffectFaithful emittedEffect encodeE satisfiedE EffectSpec CommitSurface)
open Dregg2.Circuit.EffectCommit2
  (emitEffect2Faithful emittedEffect2 encodeE2 EffectSpec2)
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

/-! ## §9 — CreateEscrowA (v2-dual). -/

def createEscrowEmittedStep (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ) (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : CreateEscrowArgs) (s' : RecChainedState) : Prop :=
  effect2dualEmittedStepLocal S (createEscrowE D hD LE cN hN hLE) createEscrowAAirName s args s'

theorem createEscrow_emitted_equiv_circuit (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : CreateEscrowArgs) (s' : RecChainedState) :
    createEscrowEmittedStep S D hD LE cN hN hLE s args s' ↔
      createEscrowCircuitStep S D hD LE cN hN hLE s args s' :=
  effect2dual_emitted_equiv_circuit_local S (createEscrowE D hD LE cN hN hLE) createEscrowAAirName
    s args s'

theorem createEscrow_emitted_refines_spec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : CreateEscrowArgs) (s' : RecChainedState)
    (h : createEscrowEmittedStep S D hD LE cN hN hLE s args s') :
    createEscrowSpecStep s args s' :=
  effect2dual_emitted_refines_bespoke_spec S (createEscrowE D hD LE cN hN hLE) createEscrowAAirName
    (createEscrowCircuitStep S D hD LE cN hN hLE) createEscrowSpecStep
    (createEscrow_circuit_refines_spec S D hD LE cN hN hLE hRest hLog)
    (fun pre args post => createEscrow_emitted_equiv_circuit S D hD LE cN hN hLE pre args post)
    s args s' h

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

/-! ## §11 — ReleaseEscrowA + RefundEscrowA (v2-dual). -/

def releaseEscrowEmittedStep (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ) (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : ReleaseArgs) (s' : RecChainedState) : Prop :=
  effect2dualEmittedStepLocal S (releaseEscrowE D hD LE cN hN hLE) releaseEscrowAAirName s args s'

theorem releaseEscrow_emitted_equiv_circuit (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : ReleaseArgs) (s' : RecChainedState) :
    releaseEscrowEmittedStep S D hD LE cN hN hLE s args s' ↔
      releaseEscrowCircuitStep S D hD LE cN hN hLE s args s' :=
  effect2dual_emitted_equiv_circuit_local S (releaseEscrowE D hD LE cN hN hLE) releaseEscrowAAirName
    s args s'

theorem releaseEscrow_emitted_refines_spec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : ReleaseArgs) (s' : RecChainedState)
    (h : releaseEscrowEmittedStep S D hD LE cN hN hLE s args s') :
    releaseEscrowSpecStep s args s' :=
  effect2dual_emitted_refines_bespoke_spec S (releaseEscrowE D hD LE cN hN hLE) releaseEscrowAAirName
    (releaseEscrowCircuitStep S D hD LE cN hN hLE) releaseEscrowSpecStep
    (releaseEscrow_circuit_refines_spec S D hD LE cN hN hLE hRest hLog)
    (fun pre args post => releaseEscrow_emitted_equiv_circuit S D hD LE cN hN hLE pre args post)
    s args s' h

def refundEscrowEmittedStep (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ) (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : RefundEscrowArgs) (s' : RecChainedState) : Prop :=
  effect2dualEmittedStepLocal S (refundEscrowE D hD LE cN hN hLE) refundEscrowAAirName s args s'

theorem refundEscrow_emitted_equiv_circuit (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : RefundEscrowArgs) (s' : RecChainedState) :
    refundEscrowEmittedStep S D hD LE cN hN hLE s args s' ↔
      refundEscrowCircuitStep S D hD LE cN hN hLE s args s' :=
  effect2dual_emitted_equiv_circuit_local S (refundEscrowE D hD LE cN hN hLE) refundEscrowAAirName
    s args s'

theorem refundEscrow_emitted_refines_spec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RefundEscrowArgs) (s' : RecChainedState)
    (h : refundEscrowEmittedStep S D hD LE cN hN hLE s args s') :
    refundEscrowSpecStep s args s' :=
  effect2dual_emitted_refines_bespoke_spec S (refundEscrowE D hD LE cN hN hLE) refundEscrowAAirName
    (refundEscrowCircuitStep S D hD LE cN hN hLE) refundEscrowSpecStep
    (refundEscrow_circuit_refines_spec S D hD LE cN hN hLE hRest hLog)
    (fun pre args post => refundEscrow_emitted_equiv_circuit S D hD LE cN hN hLE pre args post)
    s args s' h

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

/-! ## §14 — BridgeLockA (v2-dual). -/

def bridgeLockEmittedStep (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ) (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : BridgeLockArgs) (s' : RecChainedState) : Prop :=
  effect2dualEmittedStepLocal S (bridgeLockE D hD LE cN hN hLE) bridgeLockAAirName s args s'

theorem bridgeLock_emitted_equiv_circuit (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : BridgeLockArgs) (s' : RecChainedState) :
    bridgeLockEmittedStep S D hD LE cN hN hLE s args s' ↔
      bridgeLockCircuitStep S D hD LE cN hN hLE s args s' :=
  effect2dual_emitted_equiv_circuit_local S (bridgeLockE D hD LE cN hN hLE) bridgeLockAAirName
    s args s'

theorem bridgeLock_emitted_refines_spec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : BridgeLockArgs) (s' : RecChainedState)
    (h : bridgeLockEmittedStep S D hD LE cN hN hLE s args s') :
    bridgeLockSpecStep s args s' :=
  effect2dual_emitted_refines_bespoke_spec S (bridgeLockE D hD LE cN hN hLE) bridgeLockAAirName
    (bridgeLockCircuitStep S D hD LE cN hN hLE) bridgeLockSpecStep
    (bridgeLock_circuit_refines_spec S D hD LE cN hN hLE hRest hLog)
    (fun pre args post => bridgeLock_emitted_equiv_circuit S D hD LE cN hN hLE pre args post)
    s args s' h

/-! ## §15 — QueueEnqueueA (v2-triple). -/

def queueEnqueueEmittedStep (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ) (hNQ : compressNInjective cNQ) (hLQ : listLeafInjective LQ)
    (LE : EscrowRecord → ℤ) (cNE : List ℤ → ℤ) (hNE : compressNInjective cNE) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : EnqueueArgs) (s' : RecChainedState) : Prop :=
  effect2tripleEmittedStepLocal S
    (queueEnqueueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE) queueEnqueueAAirName s args s'

theorem queueEnqueue_emitted_equiv_circuit (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ)
    (hNQ : compressNInjective cNQ) (hLQ : listLeafInjective LQ) (LE : EscrowRecord → ℤ)
    (cNE : List ℤ → ℤ) (hNE : compressNInjective cNE) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : EnqueueArgs) (s' : RecChainedState) :
    queueEnqueueEmittedStep S D hD LQ cNQ hNQ hLQ LE cNE hNE hLE s args s' ↔
      queueEnqueueCircuitStep S D hD LQ cNQ hNQ hLQ LE cNE hNE hLE s args s' :=
  effect2triple_emitted_equiv_circuit_local S
    (queueEnqueueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE) queueEnqueueAAirName s args s'

theorem queueEnqueue_emitted_refines_spec (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ)
    (hD : Function.Injective D) (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ)
    (hNQ : compressNInjective cNQ) (hLQ : listLeafInjective LQ) (LE : EscrowRecord → ℤ)
    (cNE : List ℤ → ℤ) (hNE : compressNInjective cNE) (hLE : listLeafInjective LE)
    (hRest : RestIffNoQueuesBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : EnqueueArgs) (s' : RecChainedState)
    (h : queueEnqueueEmittedStep S D hD LQ cNQ hNQ hLQ LE cNE hNE hLE s args s') :
    queueEnqueueSpecStep s args s' :=
  effect2triple_emitted_refines_bespoke_spec S
    (queueEnqueueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE) queueEnqueueAAirName
    (queueEnqueueCircuitStep S D hD LQ cNQ hNQ hLQ LE cNE hNE hLE) queueEnqueueSpecStep
    (queueEnqueue_circuit_refines_spec S D hD LQ cNQ hNQ hLQ LE cNE hNE hLE hRest hLog)
    (fun pre args post =>
      queueEnqueue_emitted_equiv_circuit S D hD LQ cNQ hNQ hLQ LE cNE hNE hLE pre args post)
    s args s' h

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
#assert_axioms createEscrow_emitted_refines_spec
#assert_axioms noteCreate_emitted_refines_spec
#assert_axioms releaseEscrow_emitted_refines_spec
#assert_axioms refundEscrow_emitted_refines_spec
#assert_axioms revoke_emitted_refines_spec
#assert_axioms seal_emitted_refines_spec
#assert_axioms bridgeLock_emitted_refines_spec
#assert_axioms queueEnqueue_emitted_refines_spec
#assert_axioms setField_emitted_refines_spec
#assert_axioms exerciseHold_emitted_refines_spec

end Dregg2.Circuit.EffectEmittedRefinement