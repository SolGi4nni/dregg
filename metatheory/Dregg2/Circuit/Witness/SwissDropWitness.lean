/-
# Dregg2.Circuit.Witness.SwissDropWitness — the v2 WITNESS GENERATOR for `swissDropA`.

Closes the verifiable-execution beachhead for `swissDropA` (the CapTP sturdy-ref DROP/GC: decrement
the swiss entry's refcount, GC-ing it at 0), over the v2 framework (`EffectCommit2`), touched
component `kernel.swiss` (a `listComponent`). Reused: `Exec.swissDropChainA`,
`Inst.SwissDropA.swissDropA_full_sound` (⇒ `DropSpec`), `effect2_circuit_full_complete`,
`emittedEffect2`/`emitDescriptorJson`.

§3 abstract execute→prove + verify→accept; §4 the concrete `swissDropWitnessVec`; §5 the descriptor +
witness JSON. The anti-ghost forgery: the post entry does NOT decrement the refcount (stays at its old
value — a phantom live ref). The component-bind gate 68≠69 = a real UNSAT.

No `sorry`/`admit`/`axiom`/`native_decide`. CR portals carried HYPOTHESES on the abstract keystones.
-/
import Dregg2.Circuit.Inst.swissDropA

namespace Dregg2.Circuit.Witness.SwissDropWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Inst.SwissDropA
open Dregg2.Circuit.Spec.SwissDrop
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Auth)

set_option linter.dupNamespace false

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))
instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §3 — THE ABSTRACT EXECUTE→PROVE / PROVE→STATE theorems (CR portals carried). -/

variable (S : Surface2) (LE : SwissRecord → ℤ) (cN : List ℤ → ℤ)
  (hN : compressNInjective cN) (hLE : listLeafInjective LE)

theorem execute_produces_satisfying_witness
    (hRest : RestIffNoSwiss S.RH)
    (s : RecChainedState) (args : DropArgs) (s' : RecChainedState)
    (hspec : DropSpec s args.sw args.actor args.exporter s') :
    satisfiedE2 S (swissDropE LE cN hN hLE) (encodeE2 S (swissDropE LE cN hN hLE) s args s') :=
  effect2_circuit_full_complete S (swissDropE LE cN hN hLE)
    (fun k k' h => (hRest k k').mpr h) (dropGuardEncodes LE cN hN hLE) s args s'
    ((apex_iff_dropSpec LE cN hN hLE s args s').mpr hspec)

theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoSwiss S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : DropArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (swissDropE LE cN hN hLE) (encodeE2 S (swissDropE LE cN hN hLE) s args s')) :
    DropSpec s args.sw args.actor args.exporter s' :=
  swissDropA_full_sound S LE cN hN hLE hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS. -/

def authCode : Auth → ℤ
  | .read => 1 | .write => 2 | .grant => 3 | .call => 4 | .reply => 5 | .reset => 6 | .control => 7

def swissCode (r : SwissRecord) : ℤ :=
  ((r.swiss : ℤ) * 101 + (r.exporter : ℤ) * 103 + (r.target : ℤ) * 107
    + r.rights.foldl (fun acc a => (acc * 11 + authCode a) % 2000003) 1 * 109
    + (r.refcount : ℤ) * 113 + (match r.cert with | none => 0 | some h => (h : ℤ) + 1) * 127) % 2000003

def swissDigConcrete : List SwissRecord → ℤ :=
  fun rs => rs.foldl (fun acc r => (acc * 7919 + swissCode r) % 2000003) ((rs.length : ℤ) + 1)

def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ) * 7
           + (k.commitments.length : ℤ) * 13 + (k.caps 0).length * 17

def lhConcrete : List Turn → ℤ :=
  fun xs => xs.foldl (fun acc t => (acc * 131 + (t.actor : ℤ) + 1) % 2000003) ((xs.length : ℤ) + 1)

def SC : Surface2 := { RH := rhConcrete, LH := lhConcrete }

def swissCompC : ActiveComponent RecChainedState DropArgs :=
  { digest    := fun k => swissDigConcrete k.swiss
  , expected  := fun s args => swissDigConcrete (dropSwissPostClause s args)
  , postClause := fun s args post =>
      swissDigConcrete post.swiss = swissDigConcrete (dropSwissPostClause s args)
  , binds     := fun _ _ _ h => h
  , encodes   := fun _ _ _ h => h }

def swissDropEC : EffectSpec2 RecChainedState DropArgs :=
  { view         := chainView
  , active       := swissCompC
  , logUpdate    := some (fun s args => dropReceipt args.actor args.exporter :: s.log)
  , restFrame    := fun k k' => rhConcrete k = rhConcrete k'
  , guardGates   := dropGuardGates
  , guardProp    := dropGuardProp
  , guardWidth   := 1
  , guardEncode  := dropGuardEncode
  , guardLocal   := dropGuardLocal
  , guardWidth_le := by decide }

/-! ### The concrete reference: an entry with refcount 2; drop decrements it to 1. -/

/-- An existing sturdy-ref record for sw 7 with refcount 2 (so a drop decrements to 1, not GC). -/
def refEntry : SwissRecord :=
  { swiss := 7, exporter := 0, target := 1, rights := [], refcount := 2, cert := none }

def kPre : RecordKernelState :=
  { accounts := {0, 1}, cell := fun _ => default, caps := fun _ => []
  , swiss := [refEntry] }

def sPre : RecChainedState := { kernel := kPre, log := [] }

/-- The drop args: actor 0 = exporter 0 (self-auth) drops one live ref to sw 7. -/
def argsRef : DropArgs := { sw := 7, actor := 0, exporter := 0 }

def sPost : RecChainedState := (swissDropChainA sPre argsRef.sw argsRef.actor argsRef.exporter).getD sPre

/-- **THE FORGERY:** the SAME guard/log/frame, but the post entry does NOT decrement the refcount
(stays at 2) — a phantom live ref kept alive after a drop. The component-bind gate must reject it. -/
def sForged : RecChainedState :=
  { sPost with kernel := { sPost.kernel with swiss := [refEntry] } }

def witnessOf (s : RecChainedState) (args : DropArgs) (s' : RecChainedState) : List Int :=
  (List.range (swissDropEC.traceWidth)).map (fun w => encodeE2 SC swissDropEC s args s' w)

def swissDropWitnessVec (s : RecChainedState) (args : DropArgs) : List Int :=
  match swissDropChainA s args.sw args.actor args.exporter with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

theorem swissDropWitnessVec_commit {s s' : RecChainedState} {args : DropArgs}
    (h : swissDropChainA s args.sw args.actor args.exporter = some s') :
    swissDropWitnessVec s args = witnessOf s args s' := by
  unfold swissDropWitnessVec; rw [h]

def honestWitness : List Int := swissDropWitnessVec sPre argsRef
def forgedWitness : List Int := witnessOf sPre argsRef sForged

#guard honestWitness.length == 72
#guard forgedWitness.length == 72
#guard decide (satisfied (effectCircuit2 swissDropEC) (encodeE2 SC swissDropEC sPre argsRef sPost))
#guard decide (satisfied (effectCircuit2 swissDropEC) (encodeE2 SC swissDropEC sPre argsRef sForged)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)
#guard honestWitness.getD 0 0 == 1
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0
#guard forgedWitness.getD 66 0 == forgedWitness.getD 67 0
#guard forgedWitness.getD 70 0 == forgedWitness.getD 71 0

/-! ## §5 — JSON export. -/

def swissDropAirName : String := "dregg-swissDropA-v2"
def emittedSwissDrop : EmittedDescriptor := emittedEffect2 swissDropAirName swissDropEC
def descriptorJson : String := emitDescriptorJson emittedSwissDrop
def witnessJson (xs : List Int) : String := "[" ++ String.intercalate "," (xs.map toString) ++ "]"
def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

#guard emittedSwissDrop.constraints.length == 4
#guard emittedSwissDrop.traceWidth == 72
#guard descriptorJson ==
  "{\"name\":\"dregg-swissDropA-v2\",\"trace_width\":72,\"constraints\":[{\"lhs\":{\"t\":\"var\",\"v\":0},\"rhs\":{\"t\":\"const\",\"v\":1}},{\"lhs\":{\"t\":\"var\",\"v\":66},\"rhs\":{\"t\":\"var\",\"v\":67}},{\"lhs\":{\"t\":\"var\",\"v\":68},\"rhs\":{\"t\":\"var\",\"v\":69}},{\"lhs\":{\"t\":\"var\",\"v\":70},\"rhs\":{\"t\":\"var\",\"v\":71}}]}"
#guard honestWitness.getD 68 0 == 16874   -- component digest binds (refcount decremented to 1)
#guard forgedWitness.getD 68 0 == 16987    -- forged component digest differs (phantom refcount 2)
#guard forgedWitness.getD 69 0 == 16874    -- expected stays the spec decrement
#guard honestWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16990,17139,2,2,16874,16874,263,263]"
#guard forgedWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16990,17252,2,2,16987,16874,263,263]"

#assert_axioms swissDropWitnessVec_commit
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.SwissDropWitness
