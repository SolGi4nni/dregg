/-
# Dregg2.Circuit.Witness.cellDestroyAWitness — `execute → satisfying assignment` for `cellDestroyA` (the
non-terminal → Destroyed lifecycle effect; v2-DUAL family, touched components = `lifecycle` AND
`deathCert`, both `funcComponent`s).

The DUAL-component analog of `attenuateAWitness`: `cellDestroyWitnessVec` RUNS the REAL executor
`cellDestroyChainA` (the arm `execFullA` dispatches `.cellDestroyA` to) and lays the satisfying 74-wire
`encodeE2Dual` assignment out as a flat `List Int` over the concrete commitment surface. The dual circuit
has FIVE gates: guard (`var 0 = 1`), rest (`66=67`), component-1 `lifecycle` (`68=69`), component-2
`deathCert` (`70=71`), log (`72=73`). The honest witness satisfies `effectCircuit2Dual`; a forged
post-state that ALSO destroys a BYSTANDER cell (lifecycle-component tamper) is REJECTED by the
component-1 bind gate `68 ≠ 69`. `Inst.cellDestroyA.cellDestroyA_full_sound` proved the crown jewel
(`⇒ CellDestroySpec`).
-/
import Dregg2.Circuit.Inst.cellDestroyA
import Dregg2.Circuit.Poseidon2Surface

namespace Dregg2.Circuit.Witness.CellDestroyAWitness

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.EffectCommit2Dual
open Dregg2.Circuit.Inst.CellDestroyA
open Dregg2.Circuit.Spec.CellLifecycle
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Poseidon2Surface (refP2 turnLogDigest)

set_option linter.dupNamespace false
set_option linter.unusedVariables false

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))
instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §1 — the CONCRETE commitment surface (two `CellId → Nat` function components). -/

def rhConcrete2 : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ)
/-- The log hash: the REAL `turnLogDigest` (binds the WHOLE receipt chain; the OLD `.length` collapse
dropped its content). -/
def lhConcrete : List Turn → ℤ := turnLogDigest

/-- The probe cells the concrete `CellId → Nat` digests sample: the destroyed `cell`, plus a bystander
cell `1` (so a bystander destroy / cert bind shows up). -/
def natProbes (cell : CellId) : List CellId := [cell, 1]

/-- Concrete `CellId → Nat` digest: the REAL `refP2` sponge over the probe values (binds each — NO lossy
`% 10⁶` collapse, so a probe value ≥ 10⁶ does not alias). -/
def natFnDigestC (cell : CellId) (f : CellId → Nat) : ℤ :=
  refP2 ((natProbes cell).map (fun c => (f c : ℤ)))

def cellDestroySurfaceC : Surface2 := { RH := rhConcrete2, LH := lhConcrete }

/-! ## §2 — the concrete dual `ActiveComponent`s + the concrete `cellDestroyEC`. -/

def lifecycleComponentC (cell : CellId) : ActiveComponent RecChainedState CellDestroyArgs where
  digest    := fun k => natFnDigestC cell k.lifecycle
  expected  := fun s args => natFnDigestC cell (destroyKernelMap s.kernel args.cell args.certHash).lifecycle
  postClause := fun s args post =>
    natFnDigestC cell post.lifecycle = natFnDigestC cell (destroyKernelMap s.kernel args.cell args.certHash).lifecycle
  binds     := fun _ _ _ h => h
  encodes   := fun _ _ _ h => h

def deathCertComponentC (cell : CellId) : ActiveComponent RecChainedState CellDestroyArgs where
  digest    := fun k => natFnDigestC cell k.deathCert
  expected  := fun s args => natFnDigestC cell (destroyKernelMap s.kernel args.cell args.certHash).deathCert
  postClause := fun s args post =>
    natFnDigestC cell post.deathCert = natFnDigestC cell (destroyKernelMap s.kernel args.cell args.certHash).deathCert
  binds     := fun _ _ _ h => h
  encodes   := fun _ _ _ h => h

def cellDestroyEC (cell : CellId) : EffectSpec2Dual RecChainedState CellDestroyArgs where
  view         := chainView
  active1      := lifecycleComponentC cell
  active2      := deathCertComponentC cell
  logUpdate    := some (fun s args => cellLifecycleReceipt args.actor args.cell :: s.log)
  restFrame    := fun k k' => True
  guardGates   := cellDestroyGuardGates
  guardProp    := cellDestroyGuardProp
  guardWidth   := 1
  guardEncode  := cellDestroyGuardEncode
  guardLocal   := cellDestroyGuardLocal
  guardWidth_le := by decide

/-! ## §3 — THE WITNESS GENERATOR. -/

def witnessOf (cell : CellId) (s : RecChainedState) (args : CellDestroyArgs) (s' : RecChainedState) :
    List Int :=
  (List.range (cellDestroyEC cell).traceWidth).map
    (fun v => encodeE2Dual cellDestroySurfaceC (cellDestroyEC cell) s args s' v)

def cellDestroyWitnessVec (s : RecChainedState) (args : CellDestroyArgs) : List Int :=
  match cellDestroyChainA s args.actor args.cell args.certHash with
  | some s' => witnessOf args.cell s args s'
  | none    => witnessOf args.cell s args s

theorem cellDestroyWitnessVec_commit {s s' : RecChainedState} {args : CellDestroyArgs}
    (h : cellDestroyChainA s args.actor args.cell args.certHash = some s') :
    cellDestroyWitnessVec s args = witnessOf args.cell s args s' := by
  unfold cellDestroyWitnessVec; rw [h]

theorem witnessOf_get (cell : CellId) (s : RecChainedState) (args : CellDestroyArgs)
    (s' : RecChainedState) (v : Nat) (hv : v < (cellDestroyEC cell).traceWidth) :
    (witnessOf cell s args s')[v]'(by simpa [witnessOf] using hv)
      = encodeE2Dual cellDestroySurfaceC (cellDestroyEC cell) s args s' v := by
  unfold witnessOf; rw [List.getElem_map, List.getElem_range]

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS.

A pre-state with cells {0,1} both LIVE (`lifecycle = 0`); actor 0 self-authorized over cell 0
(`stateAuthB` true since `actor = target`). `cellDestroyA` flips cell 0 to Destroyed (3) and binds
`certHash = 77` at cell 0; the bystander cell 1 must stay LIVE. -/

def sC0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => default
        caps := fun _ => [] }
    log := [] }

/-- Destroy cell 0 (actor 0), binding death-cert hash 77. -/
def goodArgsC : CellDestroyArgs := { actor := 0, cell := 0, certHash := 77 }

def goodPostC : RecChainedState := (cellDestroyChainA sC0 0 0 77).getD sC0

/-- THE FORGERY: cell 0 destroyed, BUT bystander cell 1 is ALSO destroyed (lifecycle → 3) — a
collateral kill the destroy never authorized. The deathCert/frame/log stay honest, so a projection
circuit would have passed it; the LIFECYCLE component digest differs (component-1 gate `68 = 69`). -/
def forgedLifecycleC : CellId → Nat :=
  fun c => if c = 0 then 3 else if c = 1 then 3 else goodPostC.kernel.lifecycle c

def forgedPostC : RecChainedState :=
  { kernel := { goodPostC.kernel with lifecycle := forgedLifecycleC }, log := goodPostC.log }

def honestWitness : List Int := cellDestroyWitnessVec sC0 goodArgsC
def forgedWitness : List Int := witnessOf 0 sC0 goodArgsC forgedPostC

#guard honestWitness.length == 74
#guard forgedWitness.length == 74

#guard decide (satisfied (effectCircuit2Dual (cellDestroyEC 0))
  (encodeE2Dual cellDestroySurfaceC (cellDestroyEC 0) sC0 goodArgsC goodPostC))
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0   -- rest
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0   -- comp1 lifecycle
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0   -- comp2 deathCert
#guard honestWitness.getD 72 0 == honestWitness.getD 73 0   -- log

#guard decide (satisfied (effectCircuit2Dual (cellDestroyEC 0))
  (encodeE2Dual cellDestroySurfaceC (cellDestroyEC 0) sC0 goodArgsC forgedPostC)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)   -- lifecycle component REJECTED

-- HIGH-field MODULAR-COLLISION anti-ghost tooth: bystander cell 1's `deathCert` forged ABOVE the OLD
-- `% 10⁶` Horner window (a substituted certificate hash). The OLD positional fold carried/aliased across
-- 10⁶; `refP2` does NOT, so the deathCert comp2 bind gate `70 ≠ 71` REJECTS.
def forgedCertC : CellId → Nat :=
  fun c => if c = 1 then goodPostC.kernel.deathCert 1 + 1000000 else goodPostC.kernel.deathCert c
def forgedCertPostC : RecChainedState :=
  { kernel := { goodPostC.kernel with deathCert := forgedCertC }, log := goodPostC.log }
#guard decide (satisfied (effectCircuit2Dual (cellDestroyEC 0))
  (encodeE2Dual cellDestroySurfaceC (cellDestroyEC 0) sC0 goodArgsC forgedCertPostC)) == false

/-! ## §5 — JSON export. -/

def witnessJson (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"
def cellDestroyHonestWitnessJson : String := witnessJson honestWitness
def cellDestroyForgedWitnessJson : String := witnessJson forgedWitness

-- Structural component-bind goldens (the field-binding `refP2` digests are arbitrary-precision; non-vacuity
-- is at the bind gates; the Rust paste is regenerated from the JSON accessors).
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0   -- lifecycle binds (honest)
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0   -- deathCert binds (honest)
#guard honestWitness.getD 72 0 == honestWitness.getD 73 0   -- log binds (honest)
#guard !(cellDestroyHonestWitnessJson == cellDestroyForgedWitnessJson)

#assert_axioms cellDestroyWitnessVec_commit
#assert_axioms witnessOf_get

end Dregg2.Circuit.Witness.CellDestroyAWitness
