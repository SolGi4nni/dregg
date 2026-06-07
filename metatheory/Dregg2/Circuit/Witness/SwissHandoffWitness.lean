/-
# Dregg2.Circuit.Witness.SwissHandoffWitness — the v2 WITNESS GENERATOR for `swissHandoffA`.

Closes the verifiable-execution beachhead for `swissHandoffA` (the 3-vat handoff cert-bind: bind a
handoff cert hash to an existing swiss entry and bump its refcount), over the v2 framework
(`EffectCommit2`), touched component `kernel.swiss` (a `listComponent`). Reused:
`Exec.swissHandoffChainA`, `Inst.SwissHandoffA.swissHandoffA_full_sound` (⇒ `HandoffSpec`),
`effect2_circuit_full_complete`, `emittedEffect2`/`emitDescriptorJson`.

§3 abstract execute→prove + verify→accept; §4 the concrete `swissHandoffWitnessVec`; §5 the descriptor
+ witness JSON. The anti-ghost forgery: the post entry does NOT bind the handoff cert (cert stays
`none`) — the component-bind gate 68≠69 = a real UNSAT.

No `sorry`/`admit`/`axiom`/`native_decide`. CR portals carried HYPOTHESES on the abstract keystones.
-/
import Dregg2.Circuit.Inst.swissHandoffA

namespace Dregg2.Circuit.Witness.SwissHandoffWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Inst.SwissHandoffA
open Dregg2.Circuit.Spec.SwissHandoff
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
    (s : RecChainedState) (args : HandoffArgs) (s' : RecChainedState)
    (hspec : HandoffSpec s args.sw args.certHash args.introducer args.exporter s') :
    satisfiedE2 S (swissHandoffE LE cN hN hLE) (encodeE2 S (swissHandoffE LE cN hN hLE) s args s') :=
  effect2_circuit_full_complete S (swissHandoffE LE cN hN hLE)
    (fun k k' h => (hRest k k').mpr h) (handoffGuardEncodes LE cN hN hLE) s args s'
    ((apex_iff_handoffSpec LE cN hN hLE s args s').mpr hspec)

theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoSwiss S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : HandoffArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (swissHandoffE LE cN hN hLE) (encodeE2 S (swissHandoffE LE cN hN hLE) s args s')) :
    HandoffSpec s args.sw args.certHash args.introducer args.exporter s' :=
  swissHandoffA_full_sound S LE cN hN hLE hRest hLog s args s' h

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

def swissCompC : ActiveComponent RecChainedState HandoffArgs :=
  { digest    := fun k => swissDigConcrete k.swiss
  , expected  := fun s args => swissDigConcrete (handoffSwissPostClause s args)
  , postClause := fun s args post =>
      swissDigConcrete post.swiss = swissDigConcrete (handoffSwissPostClause s args)
  , binds     := fun _ _ _ h => h
  , encodes   := fun _ _ _ h => h }

def swissHandoffEC : EffectSpec2 RecChainedState HandoffArgs :=
  { view         := chainView
  , active       := swissCompC
  , logUpdate    := some (fun s args => handoffReceipt args.introducer args.exporter :: s.log)
  , restFrame    := fun k k' => rhConcrete k = rhConcrete k'
  , guardGates   := handoffGuardGates
  , guardProp    := handoffGuardProp
  , guardWidth   := 1
  , guardEncode  := handoffGuardEncode
  , guardLocal   := handoffGuardLocal
  , guardWidth_le := by decide }

/-! ### The concrete reference: an existing sturdy ref for sw 7; introducer 0 binds cert 99. -/

/-- An existing sturdy-ref record for sw 7 (exporter 0, target 1, no rights, refcount 1, no cert). -/
def refEntry : SwissRecord :=
  { swiss := 7, exporter := 0, target := 1, rights := [], refcount := 1, cert := none }

/-- Pre-state: swiss holds `refEntry` (an existing export for sw 7). Accounts {0,1}. -/
def kPre : RecordKernelState :=
  { accounts := {0, 1}, cell := fun _ => default, caps := fun _ => []
  , swiss := [refEntry] }

def sPre : RecChainedState := { kernel := kPre, log := [] }

/-- The handoff args: introducer 0 = exporter 0 (self-auth) binds cert 99 to sw 7. -/
def argsRef : HandoffArgs := { sw := 7, certHash := 99, introducer := 0, exporter := 0 }

def sPost : RecChainedState :=
  (swissHandoffChainA sPre argsRef.sw argsRef.certHash argsRef.introducer argsRef.exporter).getD sPre

/-- **THE FORGERY:** the SAME guard/log/frame, but the post entry does NOT bind the cert (cert stays
`none`, refcount still bumped) — a handoff that pretends to bind a 3-vat cert but doesn't. The
component-bind gate must reject it. -/
def sForged : RecChainedState :=
  { sPost with kernel := { sPost.kernel with
      swiss := [{ refEntry with refcount := 2, cert := none }] } }

def witnessOf (s : RecChainedState) (args : HandoffArgs) (s' : RecChainedState) : List Int :=
  (List.range (swissHandoffEC.traceWidth)).map (fun w => encodeE2 SC swissHandoffEC s args s' w)

def swissHandoffWitnessVec (s : RecChainedState) (args : HandoffArgs) : List Int :=
  match swissHandoffChainA s args.sw args.certHash args.introducer args.exporter with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

theorem swissHandoffWitnessVec_commit {s s' : RecChainedState} {args : HandoffArgs}
    (h : swissHandoffChainA s args.sw args.certHash args.introducer args.exporter = some s') :
    swissHandoffWitnessVec s args = witnessOf s args s' := by
  unfold swissHandoffWitnessVec; rw [h]

def honestWitness : List Int := swissHandoffWitnessVec sPre argsRef
def forgedWitness : List Int := witnessOf sPre argsRef sForged

#guard honestWitness.length == 72
#guard forgedWitness.length == 72
#guard decide (satisfied (effectCircuit2 swissHandoffEC) (encodeE2 SC swissHandoffEC sPre argsRef sPost))
#guard decide (satisfied (effectCircuit2 swissHandoffEC) (encodeE2 SC swissHandoffEC sPre argsRef sForged)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)
#guard honestWitness.getD 0 0 == 1
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0
#guard forgedWitness.getD 66 0 == forgedWitness.getD 67 0
#guard forgedWitness.getD 70 0 == forgedWitness.getD 71 0

/-! ## §5 — JSON export. -/

def swissHandoffAirName : String := "dregg-swissHandoffA-v2"
def emittedSwissHandoff : EmittedDescriptor := emittedEffect2 swissHandoffAirName swissHandoffEC
def descriptorJson : String := emitDescriptorJson emittedSwissHandoff
def witnessJson (xs : List Int) : String := "[" ++ String.intercalate "," (xs.map toString) ++ "]"
def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

#guard emittedSwissHandoff.constraints.length == 4
#guard emittedSwissHandoff.traceWidth == 72
#guard descriptorJson ==
  "{\"name\":\"dregg-swissHandoffA-v2\",\"trace_width\":72,\"constraints\":[{\"lhs\":{\"t\":\"var\",\"v\":0},\"rhs\":{\"t\":\"const\",\"v\":1}},{\"lhs\":{\"t\":\"var\",\"v\":66},\"rhs\":{\"t\":\"var\",\"v\":67}},{\"lhs\":{\"t\":\"var\",\"v\":68},\"rhs\":{\"t\":\"var\",\"v\":69}},{\"lhs\":{\"t\":\"var\",\"v\":70},\"rhs\":{\"t\":\"var\",\"v\":71}}]}"
#guard honestWitness.getD 68 0 == 29687   -- component digest binds (cert 99 bound, refcount 2)
#guard forgedWitness.getD 68 0 == 16987    -- forged component digest differs (cert not bound)
#guard forgedWitness.getD 69 0 == 29687    -- expected stays the spec cert-bind
#guard honestWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16877,29952,2,2,29687,29687,263,263]"
#guard forgedWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16877,17252,2,2,16987,29687,263,263]"

#assert_axioms swissHandoffWitnessVec_commit
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.SwissHandoffWitness
