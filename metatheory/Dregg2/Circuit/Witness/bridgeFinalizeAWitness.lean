/-
# Dregg2.Circuit.Witness.bridgeFinalizeAWitness — `execute → satisfying assignment` for `bridgeFinalizeA`
(the bridge-OUTBOUND no-credit RESOLVE; v2 family, touched component = `escrows`, a `listComponent`).

The escrow-list analog of `burnAWitness`: `bridgeFinalizeWitnessVec` RUNS the REAL chained executor
`bridgeFinalizeChainA` and lays the satisfying 72-wire `encodeE2` assignment out as a flat `List Int`
over the concrete commitment surface (the touched-component digest is now an injective `listDigest` over
the `escrows` side-table, not a function digest). The honest witness satisfies `effectCircuit2`; a forged
post-state whose `escrows` list is TAMPERED (the finalized record left UNresolved, or a bystander record
mutated) is REJECTED by the component-bind gate `68 ≠ 69`. `Inst.bridgeFinalizeA.bridgeFinalizeA_full_sound`
proved the crown jewel (`⇒ BridgeFinalizeSpec`).
-/
import Dregg2.Circuit.Inst.bridgeFinalizeA
import Dregg2.Circuit.Poseidon2Surface

namespace Dregg2.Circuit.Witness.BridgeFinalizeAWitness

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Inst.BridgeFinalizeA
open Dregg2.Circuit.Spec.BridgeOutboundFinalize
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Poseidon2Surface (refP2 recListDigest encEscrowRec turnLogDigest)

set_option linter.dupNamespace false
set_option linter.unusedVariables false

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))
instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §1 — the REAL (Poseidon2 CR-grounded) commitment surface (escrows-list variant).

The escrows digest is `recListDigest encEscrowRec` (the CR-grounded `refP2` sponge over the field-binding
`encEscrowRec`, binding ALL nine `EscrowRecord` fields — the OLD `leConcrete` DROPPED
`creator`/`recipient`/`bridge`/`queueDep`/`queueMsg` and folded `amount` into `* 1000`). The log hash is
`turnLogDigest` (the FULL `encTurnRec`; the OLD `lhConcrete` collapsed the whole chain to its `.length`). -/

def rhConcrete2 : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ)
def lhConcrete : List Turn → ℤ := turnLogDigest

/-- The concrete `escrows` list digest: the REAL `refP2` sponge over the field-binding `encEscrowRec`. -/
def escrowsDigestC (escrows : List EscrowRecord) : ℤ := recListDigest encEscrowRec escrows

def finalizeSurfaceC : Surface2 := { RH := rhConcrete2, LH := lhConcrete }

/-! ## §2 — the concrete `ActiveComponent` + the concrete `bridgeFinalizeEC`. -/

def escrowsComponentC : ActiveComponent RecChainedState BridgeFinalizeArgs where
  digest    := fun k => escrowsDigestC k.escrows
  expected  := fun s args => escrowsDigestC (markResolved s.kernel.escrows args.id)
  postClause := fun s args post =>
    escrowsDigestC post.escrows = escrowsDigestC (markResolved s.kernel.escrows args.id)
  binds     := fun _ _ _ h => h
  encodes   := fun _ _ _ h => h

def bridgeFinalizeEC : EffectSpec2 RecChainedState BridgeFinalizeArgs where
  view         := chainView
  active       := escrowsComponentC
  logUpdate    := some (fun s args => escrowReceiptA args.actor :: s.log)
  restFrame    := fun k k' => True
  guardGates   := bridgeFinalizeGuardGates
  guardProp    := bridgeFinalizeGuardProp
  guardWidth   := 1
  guardEncode  := bridgeFinalizeGuardEncode
  guardLocal   := bridgeFinalizeGuardLocal
  guardWidth_le := by decide

/-! ## §3 — THE WITNESS GENERATOR. -/

def witnessOf (s : RecChainedState) (args : BridgeFinalizeArgs) (s' : RecChainedState) : List Int :=
  (List.range bridgeFinalizeEC.traceWidth).map
    (fun v => encodeE2 finalizeSurfaceC bridgeFinalizeEC s args s' v)

def bridgeFinalizeWitnessVec (s : RecChainedState) (args : BridgeFinalizeArgs) : List Int :=
  match bridgeFinalizeChainA s args.id args.actor args.asset args.amount with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

theorem bridgeFinalizeWitnessVec_commit {s s' : RecChainedState} {args : BridgeFinalizeArgs}
    (h : bridgeFinalizeChainA s args.id args.actor args.asset args.amount = some s') :
    bridgeFinalizeWitnessVec s args = witnessOf s args s' := by
  unfold bridgeFinalizeWitnessVec; rw [h]

theorem witnessOf_get (s : RecChainedState) (args : BridgeFinalizeArgs) (s' : RecChainedState)
    (v : Nat) (hv : v < bridgeFinalizeEC.traceWidth) :
    (witnessOf s args s')[v]'(by simpa [witnessOf] using hv)
      = encodeE2 finalizeSurfaceC bridgeFinalizeEC s args s' v := by
  unfold witnessOf; rw [List.getElem_map, List.getElem_range]

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS.

A pre-state with ONE unresolved BRIDGE escrow record (id 7, creator 0, asset 1, amount 5) plus a
bystander resolved record (id 8) the finalize must NOT touch. `bridgeAuthOK` holds (`r.bridge = true ∧
r.creator = actor 0`); the finalize marks id 7 resolved. -/

def recA : EscrowRecord :=
  { id := 7, creator := 0, recipient := 0, amount := 5, resolved := false, asset := 1, bridge := true }
def recB : EscrowRecord :=
  { id := 8, creator := 1, recipient := 1, amount := 9, resolved := true, asset := 1, bridge := true }

def sC0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun _ => default
        caps := fun _ => []
        escrows := [recA, recB] }
    log := [] }

/-- Finalize bridge escrow id 7 (actor 0, asset 1, amount 5). -/
def goodArgsC : BridgeFinalizeArgs := { id := 7, actor := 0, asset := 1, amount := 5 }

def goodPostC : RecChainedState := (bridgeFinalizeChainA sC0 7 0 1 5).getD sC0

/-- THE FORGERY: record id 7 left UNresolved (the finalize's resolve silently dropped) — a replay /
double-finalize laundering. The escrows list digest differs from the honest `markResolved`. -/
def forgedEscrowsC : List EscrowRecord := [recA, recB]   -- recA STILL unresolved (resolve dropped)

def forgedPostC : RecChainedState :=
  { kernel := { goodPostC.kernel with escrows := forgedEscrowsC }, log := goodPostC.log }

def honestWitness : List Int := bridgeFinalizeWitnessVec sC0 goodArgsC
def forgedWitness : List Int := witnessOf sC0 goodArgsC forgedPostC

#guard honestWitness.length == 72
#guard forgedWitness.length == 72

#guard decide (satisfied (effectCircuit2 bridgeFinalizeEC)
  (encodeE2 finalizeSurfaceC bridgeFinalizeEC sC0 goodArgsC goodPostC))
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0

#guard decide (satisfied (effectCircuit2 bridgeFinalizeEC)
  (encodeE2 finalizeSurfaceC bridgeFinalizeEC sC0 goodArgsC forgedPostC)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)

/-- HIGH-field anti-ghost tooth: the honest `markResolved`, but record id 7's `amount` is forged ABOVE
the OLD `* 1000` window (`5 → 5 + 1000`). Under `leConcrete` that collided into the `id` digit; under the
field-binding `encEscrowRec` the `escrows` digest DIFFERS, so the bind gate `68 ≠ 69` rejects. -/
def forgedHighPostC : RecChainedState :=
  { goodPostC with kernel := { goodPostC.kernel with
      escrows := goodPostC.kernel.escrows.map (fun r => if r.id = 7 then { r with amount := r.amount + 1000 } else r) } }
#guard decide (satisfied (effectCircuit2 bridgeFinalizeEC)
  (encodeE2 finalizeSurfaceC bridgeFinalizeEC sC0 goodArgsC forgedHighPostC)) == false

/-! ## §5 — JSON export. -/

def witnessJson (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"
def bridgeFinalizeHonestWitnessJson : String := witnessJson honestWitness
def bridgeFinalizeForgedWitnessJson : String := witnessJson forgedWitness

-- Structural bind-gate goldens (the field-binding `refP2`/`encEscrowRec` digests are arbitrary-precision
-- — non-vacuity is at the bind GATES; the Rust paste is regenerated from these JSON accessors).
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0   -- escrows binds (honest)
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0   -- log binds (honest)
#guard !(bridgeFinalizeHonestWitnessJson == bridgeFinalizeForgedWitnessJson)

#assert_axioms bridgeFinalizeWitnessVec_commit
#assert_axioms witnessOf_get

end Dregg2.Circuit.Witness.BridgeFinalizeAWitness
