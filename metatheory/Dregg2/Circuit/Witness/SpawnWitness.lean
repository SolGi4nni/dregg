/-
# Dregg2.Circuit.Witness.SpawnWitness — the v2-QUINT WITNESS GENERATOR for `spawnA`.

Closes the verifiable-execution beachhead for `spawnA` (coin a fresh child cell: grow `accounts`,
born-empty its `bal`/cell-metadata, copy the held parent cap into the child's `caps`, set the child's
`delegate`/`delegations`), over the v2-QUINT framework (`EffectCommit5`), which touches FIVE non-`cell`
components at once (accounts, the create-leg, caps, delegate, delegations). Reused: `Exec.execFullA`
(`.spawnA` arm), `Inst.SpawnA.spawnA_full_sound` (⇒ `SpawnSpec`), `effect2quint_circuit_full_complete`,
`emittedEffect2Quint`/`emitDescriptorJson`.

The quint circuit is EIGHT gates over an 80-wide trace: guard (`v0 = 1`), rest (66/67), and FIVE
component-bind gates (68/69, 70/71, 72/73, 74/75, 76/77) + log (78/79). §3 abstract execute→prove +
verify→accept; §4 the concrete `spawnWitnessVec` running the real executor; §5 the descriptor + witness
JSON. The anti-ghost forgery: the child's `caps` (component 3) is tampered to copy the WRONG parent
cap — the comp3-bind gate (72/73) breaks, a real UNSAT.

No `sorry`/`admit`/`axiom`/`native_decide`. CR portals carried HYPOTHESES on the abstract keystones.
-/
import Dregg2.Circuit.Inst.spawnA

namespace Dregg2.Circuit.Witness.SpawnWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.EffectCommit5
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Inst.SpawnA
open Dregg2.Circuit.Spec.AccountGrowth
open Dregg2.Circuit.BornEmptyCommit
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap Auth)

set_option linter.dupNamespace false

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))
instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §3 — THE ABSTRACT EXECUTE→PROVE / PROVE→STATE theorems (CR portals carried). -/

variable (S : Surface2) (LE : CellId → ℤ) (cN : List ℤ → ℤ)
  (hN : compressNInjective cN) (hLE : listLeafInjective LE)
  (DLeg : SpawnCreateLeg → ℤ) (hDLeg : Function.Injective DLeg)
  (DCaps : Caps → ℤ) (hDCaps : Function.Injective DCaps)
  (DDel : (CellId → Option CellId) → ℤ) (hDDel : Function.Injective DDel)
  (DDgs : (CellId → List Cap) → ℤ) (hDDgs : Function.Injective DDgs)

theorem execute_produces_satisfying_witness
    (hRest : RestIffNoSpawnTouched S.RH)
    (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState)
    (hspec : SpawnSpec s args.actor args.child args.target s') :
    satisfiedE2Quint S (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs)
      (encodeE2Quint S (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs) s args s') :=
  effect2quint_circuit_full_complete S (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs)
    (fun k k' h => (hRest k k').mpr h)
    (spawnGuardEncodes LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs) s args s'
    ((apex_iff_spawnSpec LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs s args s').mpr hspec)

theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoSpawnTouched S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState)
    (h : satisfiedE2Quint S (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs)
        (encodeE2Quint S (spawnE LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs) s args s')) :
    SpawnSpec s args.actor args.child args.target s' :=
  spawnA_full_sound S LE cN hN hLE DLeg hDLeg DCaps hDCaps DDel hDDel DDgs hDDgs hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS (five concrete computable components). -/

def capCode : Cap → ℤ
  | .null         => 1
  | .node t       => 101 + (t : ℤ) * 3
  | .endpoint t r => 11 + (t : ℤ) * 3 + (r.length : ℤ)

def capListCode (cs : List Cap) : ℤ :=
  cs.foldl (fun acc c => (acc * 131 + capCode c) % 2000003) ((cs.length : ℤ) + 1)

/-- The toy carrier window the digests fold over. -/
def win : List Nat := [0, 1, 2]

/-- Component 1 — accounts: a digest of membership over the window. -/
def accountsDigC : RecordKernelState → ℤ :=
  fun k => win.foldl (fun acc l => (acc * 7919 + (if l ∈ k.accounts then 1 else 0)) % 2000003) 1

/-- Component 2 — the create-leg: a digest of `bal · 0` + the lifecycle slot over the window. -/
def createLegDigC : RecordKernelState → ℤ :=
  fun k => win.foldl (fun acc l =>
    (acc * 7919 + (k.bal l 0) * 13 + (k.lifecycle l : ℤ) * 17 + (k.deathCert l : ℤ) * 19) % 2000003) 1

/-- Component 3 — caps: a digest of each cell's cap-list over the window. -/
def capsDigC : RecordKernelState → ℤ :=
  fun k => win.foldl (fun acc l => (acc * 7919 + capListCode (k.caps l)) % 2000003) 1

/-- Component 4 — delegate: a digest of the `delegate` pointer over the window. -/
def delegateDigC : RecordKernelState → ℤ :=
  fun k => win.foldl (fun acc l =>
    (acc * 7919 + (match k.delegate l with | none => 0 | some c => (c : ℤ) + 1)) % 2000003) 1

/-- Component 5 — delegations: a digest of the `delegations` snapshot over the window. -/
def delegationsDigC : RecordKernelState → ℤ :=
  fun k => win.foldl (fun acc l => (acc * 7919 + capListCode (k.delegations l)) % 2000003) 1

def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.nullifiers.length : ℤ) + (k.commitments.length : ℤ) * 7
           + (k.swiss.length : ℤ) * 13 + (k.escrows.length : ℤ) * 17

def lhConcrete : List Turn → ℤ :=
  fun xs => xs.foldl (fun acc t => (acc * 131 + (t.actor : ℤ) + 1) % 2000003) ((xs.length : ℤ) + 1)

def SC : Surface2 := { RH := rhConcrete, LH := lhConcrete }

/-- Build a concrete component from a `digest`/`expected` pair (proof-irrelevant `binds`/`encodes`). -/
def mkComp (dig : RecordKernelState → ℤ) (exp : RecChainedState → SpawnArgs → ℤ) :
    ActiveComponent RecChainedState SpawnArgs :=
  { digest := dig, expected := exp
  , postClause := fun s args post => dig post = exp s args
  , binds := fun _ _ _ h => h, encodes := fun _ _ _ h => h }

/-- A kernel whose accounts carry the expected post set (to score `accountsDigC` of the spec). -/
def withAccounts (k : RecordKernelState) (acc : Finset CellId) : RecordKernelState := { k with accounts := acc }
/-- A kernel whose bal/lifecycle/deathCert carry the create-leg's expected born-empty post. -/
def withLeg (k : RecordKernelState) (leg : SpawnCreateLeg) : RecordKernelState :=
  { k with bal := leg.bal, lifecycle := leg.cellMeta.lifecycle, deathCert := leg.cellMeta.deathCert }

def spawnEC : EffectSpec2Quint RecChainedState SpawnArgs :=
  { view         := chainView
  , active1      := mkComp accountsDigC (fun s args => accountsDigC (withAccounts s.kernel (expectedAccounts s args)))
  , active2      := mkComp createLegDigC (fun s args =>
      createLegDigC (withLeg s.kernel (expectedSpawnCreateLeg s.kernel args.child)))
  , active3      := mkComp capsDigC (fun s args =>
      capsDigC { s.kernel with caps := spawnCapsMap s.kernel args.actor args.child args.target })
  , active4      := mkComp delegateDigC (fun s args =>
      delegateDigC { s.kernel with delegate := spawnDelegateMap s.kernel args.actor args.child })
  , active5      := mkComp delegationsDigC (fun s args =>
      delegationsDigC { s.kernel with delegations := spawnDelegationsMap s.kernel args.actor args.child })
  , logUpdate    := some (fun s args => createReceipt args.actor args.child :: s.log)
  , restFrame    := fun k k' => rhConcrete k = rhConcrete k'
  , guardGates   := spawnGuardGates
  , guardProp    := spawnGuardProp
  , guardWidth   := 1
  , guardEncode  := spawnGuardEncode
  , guardLocal   := spawnGuardLocal
  , guardWidth_le := by decide }

/-! ### The concrete reference: actor 9 (holding edges to 0/1/2) spawns child 2 off parent 0. -/

def kPre : RecordKernelState :=
  { accounts := {0, 1}
  , cell := fun _ => .record [("balance", .int 0)]
  , caps := fun a => if a = 9 then [Cap.node 0, Cap.node 1, Cap.node 2] else [] }

def sPre : RecChainedState := { kernel := kPre, log := [] }

/-- The spawn args: actor 9 spawns fresh child 2 off parent 0. -/
def argsRef : SpawnArgs := { actor := 9, child := 2, target := 0 }

def sPost : RecChainedState := (execFullA sPre (.spawnA 9 2 0)).getD sPre

/-- **THE FORGERY:** the SAME guard/log/frame + the four other components, but the child's `caps`
(component 3) copies the WRONG parent cap (`node 1` not the held edge to parent 0 = `node 0`). The
comp3-bind gate (72/73) must reject it. -/
def sForged : RecChainedState :=
  { sPost with kernel := { sPost.kernel with
      caps := fun l => if l = 2 then [Cap.node 1] else sPost.kernel.caps l } }

def witnessOf (s : RecChainedState) (args : SpawnArgs) (s' : RecChainedState) : List Int :=
  (List.range (spawnEC.traceWidth)).map (fun w => encodeE2Quint SC spawnEC s args s' w)

def spawnWitnessVec (s : RecChainedState) (args : SpawnArgs) : List Int :=
  match execFullA s (.spawnA args.actor args.child args.target) with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

theorem spawnWitnessVec_commit {s s' : RecChainedState} {args : SpawnArgs}
    (h : execFullA s (.spawnA args.actor args.child args.target) = some s') :
    spawnWitnessVec s args = witnessOf s args s' := by
  unfold spawnWitnessVec; rw [h]

def honestWitness : List Int := spawnWitnessVec sPre argsRef
def forgedWitness : List Int := witnessOf sPre argsRef sForged

#guard honestWitness.length == 80
#guard forgedWitness.length == 80
#guard decide (satisfied (effectCircuit2Quint spawnEC) (encodeE2Quint SC spawnEC sPre argsRef sPost))
#guard decide (satisfied (effectCircuit2Quint spawnEC) (encodeE2Quint SC spawnEC sPre argsRef sForged)) == false
-- the FIVE component-bind gates hold honest; the caps gate (72/73) breaks under the forgery.
#guard honestWitness.getD 0 0 == 1
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0    -- rest
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0    -- accounts
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0    -- create-leg
#guard honestWitness.getD 72 0 == honestWitness.getD 73 0    -- caps
#guard honestWitness.getD 74 0 == honestWitness.getD 75 0    -- delegate
#guard honestWitness.getD 76 0 == honestWitness.getD 77 0    -- delegations
#guard honestWitness.getD 78 0 == honestWitness.getD 79 0    -- log
#guard !(forgedWitness.getD 72 0 == forgedWitness.getD 73 0) -- caps bind REJECTED (wrong child cap)
#guard forgedWitness.getD 68 0 == forgedWitness.getD 69 0    -- the other four components stay honest
#guard forgedWitness.getD 70 0 == forgedWitness.getD 71 0
#guard forgedWitness.getD 74 0 == forgedWitness.getD 75 0
#guard forgedWitness.getD 76 0 == forgedWitness.getD 77 0

/-! ## §5 — JSON export. -/

def spawnAirName : String := "dregg-spawnA-v2"
def emittedSpawn : EmittedDescriptor := emittedEffect2Quint spawnAirName spawnEC
def descriptorJson : String := emitDescriptorJson emittedSpawn
def witnessJson (xs : List Int) : String := "[" ++ String.intercalate "," (xs.map toString) ++ "]"
def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

#guard emittedSpawn.constraints.length == 8
#guard emittedSpawn.traceWidth == 80
#guard descriptorJson ==
  "{\"name\":\"dregg-spawnA-v2\",\"trace_width\":80,\"constraints\":[{\"lhs\":{\"t\":\"var\",\"v\":0},\"rhs\":{\"t\":\"const\",\"v\":1}},{\"lhs\":{\"t\":\"var\",\"v\":66},\"rhs\":{\"t\":\"var\",\"v\":67}},{\"lhs\":{\"t\":\"var\",\"v\":68},\"rhs\":{\"t\":\"var\",\"v\":69}},{\"lhs\":{\"t\":\"var\",\"v\":70},\"rhs\":{\"t\":\"var\",\"v\":71}},{\"lhs\":{\"t\":\"var\",\"v\":72},\"rhs\":{\"t\":\"var\",\"v\":73}},{\"lhs\":{\"t\":\"var\",\"v\":74},\"rhs\":{\"t\":\"var\",\"v\":75}},{\"lhs\":{\"t\":\"var\",\"v\":76},\"rhs\":{\"t\":\"var\",\"v\":77}},{\"lhs\":{\"t\":\"var\",\"v\":78},\"rhs\":{\"t\":\"var\",\"v\":79}}]}"
#guard honestWitness.getD 72 0 == 906403   -- caps component binds (honest child cap = node 0)
#guard forgedWitness.getD 72 0 == 906406    -- forged caps digest differs (wrong child cap node 1)
#guard forgedWitness.getD 73 0 == 906403    -- expected stays the spec caps map
#guard honestWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3093429,3833413,0,0,906041,906041,187653,187653,906403,906403,187663,187663,1645381,1645381,272,272]"
#guard forgedWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3093429,3833416,0,0,906041,906041,187653,187653,906406,906403,187663,187663,1645381,1645381,272,272]"

#assert_axioms spawnWitnessVec_commit
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.SpawnWitness
