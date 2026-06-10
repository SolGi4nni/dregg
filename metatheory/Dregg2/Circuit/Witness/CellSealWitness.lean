/-
# Dregg2.Circuit.Witness.CellSealWitness — the v2 WITNESS GENERATOR for `cellSealA` / `cellUnsealA`.

The `execute → prove → verify → anti-ghost` beachhead for the two cell-LIFECYCLE effects, over the v2
framework (`EffectCommit2`) — both touch a single non-`cell` component (`kernel.lifecycle : CellId → Nat`,
a `funcComponent`), grow the receipt log by one `cellLifecycleReceipt`, and freeze the 16 other kernel
fields. Mirrors `DelegateWitness` (the v2 template).

Reused (not re-proved): `execFullA … (.cellSealA/.cellUnsealA …)` (the chained executor),
`Inst.CellSealA.cellSealA_full_sound` / `Inst.CellUnsealA.cellUnsealA_full_sound`, the executor⟺spec
corners `cellSeal_iff_spec` / `cellUnseal_iff_spec`, and `effect2_circuit_full_complete`.

Poseidon-CR portals carried on the abstract keystones.
-/
import Dregg2.Circuit.Inst.cellSealA
import Dregg2.Circuit.Inst.cellUnsealA
import Dregg2.Circuit.Poseidon2Surface

namespace Dregg2.Circuit.Witness.CellSealWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Spec.CellLifecycle
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Poseidon2Surface (refP2 turnLogDigest)

set_option linter.dupNamespace false

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))
instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §3 — ABSTRACT execute→prove / prove→state (CR portals carried). -/

section Abstract
variable (S : Surface2) (D : (CellId → Nat) → ℤ) (hD : Function.Injective D)

open Dregg2.Circuit.Inst.CellSealA in
/-- **`seal_execute_produces_satisfying_witness`** — a `CellSealSpec`-satisfying step makes the v2
witness SATISFY the v2 circuit (via `effect2_circuit_full_complete` + `apex_iff_cellSealSpec`). -/
theorem seal_execute_produces_satisfying_witness
    (hRest : Inst.CellSealA.RestIffNoLifecycle S.RH)
    (s : RecChainedState) (args : Inst.CellSealA.CellSealArgs) (s' : RecChainedState)
    (hspec : CellSealSpec s args.actor args.cell s') :
    satisfiedE2 S (Inst.CellSealA.cellSealE D hD)
      (encodeE2 S (Inst.CellSealA.cellSealE D hD) s args s') :=
  effect2_circuit_full_complete S (Inst.CellSealA.cellSealE D hD)
    (fun k k' h => (hRest k k').mpr h) (Inst.CellSealA.cellSealGuardEncodes D hD) s args s'
    ((Inst.CellSealA.apex_iff_cellSealSpec D hD s args s').mpr hspec)

/-- **`seal_satisfying_witness_proves_full_state`** — a satisfying v2 witness proves `CellSealSpec`
(all 17 kernel fields + log). Reuses `cellSealA_full_sound`. -/
theorem seal_satisfying_witness_proves_full_state
    (hRest : Inst.CellSealA.RestIffNoLifecycle S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.CellSealA.CellSealArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (Inst.CellSealA.cellSealE D hD)
        (encodeE2 S (Inst.CellSealA.cellSealE D hD) s args s')) :
    CellSealSpec s args.actor args.cell s' :=
  Inst.CellSealA.cellSealA_full_sound S D hD hRest hLog s args s' h

/-- **`unseal_satisfying_witness_proves_full_state`** — the `cellUnsealA` twin. -/
theorem unseal_satisfying_witness_proves_full_state
    (hRest : Inst.CellUnsealA.RestIffNoLifecycle S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : Inst.CellUnsealA.CellUnsealArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (Inst.CellUnsealA.cellUnsealE D hD)
        (encodeE2 S (Inst.CellUnsealA.cellUnsealE D hD) s args s')) :
    CellUnsealSpec s args.actor args.cell s' :=
  Inst.CellUnsealA.cellUnsealA_full_sound S D hD hRest hLog s args s' h

end Abstract

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS. -/

/-- Concrete computable lifecycle digest over the fixed carrier `[0,1,2]`: the REAL `refP2` sponge of each
cell's lifecycle Nat (binds each — the OLD `% 1000` Horner truncated lifecycle values ≥ 1000). -/
def lifeDigConcrete : (CellId → Nat) → ℤ :=
  fun lc => refP2 [(lc 0 : ℤ), (lc 1 : ℤ), (lc 2 : ℤ)]

/-- Concrete rest hash (field-count of non-`lifecycle` components — unchanged by a pure lifecycle
forgery, so the COMPONENT-bind gate is the one that bites). -/
def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ)

/-- Concrete log hash: the REAL `turnLogDigest` (binds `dst`/`amt` the OLD `actor*1000 + src` fold dropped). -/
def lhConcrete : List Turn → ℤ := turnLogDigest

def SC : Surface2 := { RH := rhConcrete, LH := lhConcrete }

/-! ### cellSealA concrete instance. -/

/-- The concrete `lifecycle` component for `cellSealA` (computable digest; `postClause` = the digest
equality, so the `ActiveComponent` is inhabited — `binds`/`encodes` are the identity). -/
def sealLifeCompC : ActiveComponent RecChainedState Inst.CellSealA.CellSealArgs :=
  { digest    := fun k => lifeDigConcrete k.lifecycle
  , expected  := fun s args => lifeDigConcrete (sealLifecycleMap s.kernel args.cell)
  , postClause := fun s args post =>
      lifeDigConcrete post.lifecycle = lifeDigConcrete (sealLifecycleMap s.kernel args.cell)
  , binds     := fun _ _ _ h => h
  , encodes   := fun _ _ _ h => h }

def cellSealEC : EffectSpec2 RecChainedState Inst.CellSealA.CellSealArgs :=
  { view         := Inst.CellSealA.chainView
  , active       := sealLifeCompC
  , logUpdate    := some (fun s args => cellLifecycleReceipt args.actor args.cell :: s.log)
  , restFrame    := fun _ _ => True
  , guardGates   := Inst.CellSealA.cellSealGuardGates
  , guardProp    := Inst.CellSealA.cellSealGuardProp
  , guardWidth   := 1
  , guardEncode  := Inst.CellSealA.cellSealGuardEncode
  , guardLocal   := Inst.CellSealA.cellSealGuardLocal
  , guardWidth_le := by decide }

/-! ### cellUnsealA concrete instance. -/

def unsealLifeCompC : ActiveComponent RecChainedState Inst.CellUnsealA.CellUnsealArgs :=
  { digest    := fun k => lifeDigConcrete k.lifecycle
  , expected  := fun s args => lifeDigConcrete (unsealLifecycleMap s.kernel args.cell)
  , postClause := fun s args post =>
      lifeDigConcrete post.lifecycle = lifeDigConcrete (unsealLifecycleMap s.kernel args.cell)
  , binds     := fun _ _ _ h => h
  , encodes   := fun _ _ _ h => h }

def cellUnsealEC : EffectSpec2 RecChainedState Inst.CellUnsealA.CellUnsealArgs :=
  { view         := Inst.CellUnsealA.chainView
  , active       := unsealLifeCompC
  , logUpdate    := some (fun s args => cellLifecycleReceipt args.actor args.cell :: s.log)
  , restFrame    := fun _ _ => True
  , guardGates   := Inst.CellUnsealA.cellUnsealGuardGates
  , guardProp    := Inst.CellUnsealA.cellUnsealGuardProp
  , guardWidth   := 1
  , guardEncode  := Inst.CellUnsealA.cellUnsealGuardEncode
  , guardLocal   := Inst.CellUnsealA.cellUnsealGuardLocal
  , guardWidth_le := by decide }

/-! ### Concrete reference triples (actor 0 self-seals or unseals cell 0; carrier {0,1,2}). -/

/-- Pre-state for SEAL: cell 0 Live (lifecycle 0 everywhere), self-authority (actor 0 == cell 0). -/
def kPreSeal : RecordKernelState :=
  { accounts := {0, 1, 2}, cell := fun _ => default, caps := fun _ => []
  , lifecycle := fun _ => lcLive }
def sPreSeal : RecChainedState := { kernel := kPreSeal, log := [] }
def sealArgs : Inst.CellSealA.CellSealArgs := { actor := 0, cell := 0 }
def sPostSeal : RecChainedState := (execFullA sPreSeal (.cellSealA 0 0)).getD sPreSeal

/-- THE SEAL FORGERY: cell 0 sealed, but a THIRD cell (2) is ALSO flipped to Sealed — a
bystander lifecycle tamper. The component-bind gate must reject it. -/
def sForgedSeal : RecChainedState :=
  { kernel := { kPreSeal with
      lifecycle := fun c => if c = 0 then lcSealed else if c = 2 then lcSealed else lcLive }
  , log := cellLifecycleReceipt 0 0 :: sPreSeal.log }

/-- Pre-state for UNSEAL: cell 0 Sealed (lifecycle 1), others Live; self-authority. -/
def kPreUnseal : RecordKernelState :=
  { accounts := {0, 1, 2}, cell := fun _ => default, caps := fun _ => []
  , lifecycle := fun c => if c = 0 then lcSealed else lcLive }
def sPreUnseal : RecChainedState := { kernel := kPreUnseal, log := [] }
def unsealArgs : Inst.CellUnsealA.CellUnsealArgs := { actor := 0, cell := 0 }
def sPostUnseal : RecChainedState := (execFullA sPreUnseal (.cellUnsealA 0 0)).getD sPreUnseal

/-- THE UNSEAL FORGERY: cell 0 unsealed (→ Live), but a THIRD cell (2) is flipped to Sealed. -/
def sForgedUnseal : RecChainedState :=
  { kernel := { kPreUnseal with
      lifecycle := fun c => if c = 2 then lcSealed else lcLive }
  , log := cellLifecycleReceipt 0 0 :: sPreUnseal.log }

/-! ### The witness vectors. -/

def sealWitnessOf (s : RecChainedState) (args : Inst.CellSealA.CellSealArgs) (s' : RecChainedState) :
    List Int :=
  (List.range cellSealEC.traceWidth).map (fun w => encodeE2 SC cellSealEC s args s' w)
def unsealWitnessOf (s : RecChainedState) (args : Inst.CellUnsealA.CellUnsealArgs)
    (s' : RecChainedState) : List Int :=
  (List.range cellUnsealEC.traceWidth).map (fun w => encodeE2 SC cellUnsealEC s args s' w)

/-- **`sealWitnessVec` — the executor-driven seal witness generator.** -/
def sealWitnessVec (s : RecChainedState) (args : Inst.CellSealA.CellSealArgs) : List Int :=
  match execFullA s (.cellSealA args.actor args.cell) with
  | some s' => sealWitnessOf s args s'
  | none    => sealWitnessOf s args s

def unsealWitnessVec (s : RecChainedState) (args : Inst.CellUnsealA.CellUnsealArgs) : List Int :=
  match execFullA s (.cellUnsealA args.actor args.cell) with
  | some s' => unsealWitnessOf s args s'
  | none    => unsealWitnessOf s args s

def sealHonestWitness : List Int := sealWitnessVec sPreSeal sealArgs
def sealForgedWitness : List Int := sealWitnessOf sPreSeal sealArgs sForgedSeal
def unsealHonestWitness : List Int := unsealWitnessVec sPreUnseal unsealArgs
def unsealForgedWitness : List Int := unsealWitnessOf sPreUnseal unsealArgs sForgedUnseal

-- widths
#guard sealHonestWitness.length == 72
#guard unsealHonestWitness.length == 72

-- EXECUTE→PROVE: the executor-derived witnesses SATISFY the v2 circuit.
#guard decide (satisfied (effectCircuit2 cellSealEC) (encodeE2 SC cellSealEC sPreSeal sealArgs sPostSeal))
#guard decide (satisfied (effectCircuit2 cellUnsealEC)
  (encodeE2 SC cellUnsealEC sPreUnseal unsealArgs sPostUnseal))

-- ANTI-GHOST (real UNSAT): the forged post-states FAIL the circuit, broken at the component-bind gate 68≠69.
#guard decide (satisfied (effectCircuit2 cellSealEC)
  (encodeE2 SC cellSealEC sPreSeal sealArgs sForgedSeal)) == false
#guard decide (satisfied (effectCircuit2 cellUnsealEC)
  (encodeE2 SC cellUnsealEC sPreUnseal unsealArgs sForgedUnseal)) == false
#guard !(sealForgedWitness.getD 68 0 == sealForgedWitness.getD 69 0)
#guard !(unsealForgedWitness.getD 68 0 == unsealForgedWitness.getD 69 0)
-- honest binds + guard + rest frame hold:
#guard sealHonestWitness.getD 68 0 == sealHonestWitness.getD 69 0
#guard sealHonestWitness.getD 66 0 == sealHonestWitness.getD 67 0
#guard sealHonestWitness.getD 0 0 == 1
#guard unsealHonestWitness.getD 0 0 == 1

/-! ## §5 — JSON export. -/

def sealEmitted : EmittedDescriptor := emittedEffect2 "dregg-cellSealA-v2" cellSealEC
def unsealEmitted : EmittedDescriptor := emittedEffect2 "dregg-cellUnsealA-v2" cellUnsealEC
def sealDescriptorJson : String := emitDescriptorJson sealEmitted
def unsealDescriptorJson : String := emitDescriptorJson unsealEmitted
def witnessJson (xs : List Int) : String := "[" ++ String.intercalate "," (xs.map toString) ++ "]"
def sealHonestWitnessJson : String := witnessJson sealHonestWitness
def sealForgedWitnessJson : String := witnessJson sealForgedWitness
def unsealHonestWitnessJson : String := witnessJson unsealHonestWitness
def unsealForgedWitnessJson : String := witnessJson unsealForgedWitness

#guard sealEmitted.constraints.length == 4
#guard sealEmitted.traceWidth == 72

-- Structural component-bind goldens (the field-binding `refP2` lifecycle digest is arbitrary-precision
-- — non-vacuity is at the bind gates; the Rust paste is regenerated from the JSON accessors).
#guard sealHonestWitness.getD 68 0 == sealHonestWitness.getD 69 0      -- seal component binds (honest)
#guard !(sealForgedWitness.getD 68 0 == sealForgedWitness.getD 69 0)   -- seal forged differs (REJECTED)
#guard unsealHonestWitness.getD 68 0 == unsealHonestWitness.getD 69 0  -- unseal component binds (honest)
#guard !(unsealForgedWitness.getD 68 0 == unsealForgedWitness.getD 69 0) -- unseal forged differs (REJECTED)
#guard !(sealHonestWitnessJson == sealForgedWitnessJson)

#assert_axioms seal_satisfying_witness_proves_full_state
#assert_axioms unseal_satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.CellSealWitness
