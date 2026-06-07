/-
# Dregg2.Circuit.Witness.SealWitness — the v2 WITNESS GENERATOR for `sealA`.

Closes the verifiable-execution beachhead for `sealA` (the seal-box constructor: PREPEND a
`SealedBoxRecord` binding a sealed cap to the holding-store), over the v2 framework (`EffectCommit2`),
touched component `kernel.sealedBoxes` (a `listComponent`). Reused: `Exec.sealChainA`,
`Inst.SealA.sealA_full_sound` (⇒ `SealSpec`), `effect2_circuit_full_complete`,
`emittedEffect2`/`emitDescriptorJson`.

§3 abstract execute→prove + verify→accept; §4 the concrete `sealWitnessVec`; §5 the descriptor +
witness JSON. The anti-ghost forgery: the prepended box binds a DIFFERENT payload than the one sealed
(a cap-substitution) — the component-bind gate 68≠69 = a real UNSAT.

No `sorry`/`admit`/`axiom`/`native_decide`. CR portals carried HYPOTHESES on the abstract keystones.
-/
import Dregg2.Circuit.Inst.sealA

namespace Dregg2.Circuit.Witness.SealWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Inst.SealA
open Dregg2.Circuit.Spec.SealBoxOperations
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Cap Auth)

set_option linter.dupNamespace false

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))
instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §3 — THE ABSTRACT EXECUTE→PROVE / PROVE→STATE theorems (CR portals carried). -/

variable (S : Surface2) (LE : SealedBoxRecord → ℤ) (cN : List ℤ → ℤ)
  (hN : compressNInjective cN) (hLE : listLeafInjective LE)

theorem execute_produces_satisfying_witness
    (hRest : RestIffNoSealedBoxes S.RH)
    (s : RecChainedState) (args : SealArgs) (s' : RecChainedState)
    (hspec : SealSpec s args.pid args.actor args.payload s') :
    satisfiedE2 S (sealE LE cN hN hLE) (encodeE2 S (sealE LE cN hN hLE) s args s') :=
  effect2_circuit_full_complete S (sealE LE cN hN hLE)
    (fun k k' h => (hRest k k').mpr h) (sealGuardEncodes LE cN hN hLE) s args s'
    ((apex_iff_sealSpec LE cN hN hLE s args s').mpr hspec)

theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoSealedBoxes S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SealArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (sealE LE cN hN hLE) (encodeE2 S (sealE LE cN hN hLE) s args s')) :
    SealSpec s args.pid args.actor args.payload s' :=
  sealA_full_sound S LE cN hN hLE hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS. -/

def capCode : Cap → ℤ
  | .null         => 1
  | .node t       => 101 + (t : ℤ) * 3
  | .endpoint t r => 11 + (t : ℤ) * 3 + (r.length : ℤ)

/-- Concrete computable per-`SealedBoxRecord` leaf code (all three fields folded, mod a small prime). -/
def boxCode (b : SealedBoxRecord) : ℤ :=
  ((b.pairId : ℤ) * 101 + (b.sealer : ℤ) * 103 + capCode b.payload * 107) % 2000003

def boxDigConcrete : List SealedBoxRecord → ℤ :=
  fun bs => bs.foldl (fun acc b => (acc * 7919 + boxCode b) % 2000003) ((bs.length : ℤ) + 1)

def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ) * 7
           + (k.commitments.length : ℤ) * 13 + (k.caps 0).length * 17

def lhConcrete : List Turn → ℤ :=
  fun xs => xs.foldl (fun acc t => (acc * 131 + (t.actor : ℤ) + 1) % 2000003) ((xs.length : ℤ) + 1)

def SC : Surface2 := { RH := rhConcrete, LH := lhConcrete }

def boxesCompC : ActiveComponent RecChainedState SealArgs :=
  { digest    := fun k => boxDigConcrete k.sealedBoxes
  , expected  := fun s args =>
      boxDigConcrete (sealedBoxPrepend s.kernel.sealedBoxes args.pid args.actor args.payload)
  , postClause := fun s args post =>
      boxDigConcrete post.sealedBoxes
        = boxDigConcrete (sealedBoxPrepend s.kernel.sealedBoxes args.pid args.actor args.payload)
  , binds     := fun _ _ _ h => h
  , encodes   := fun _ _ _ h => h }

def sealEC : EffectSpec2 RecChainedState SealArgs :=
  { view         := chainView
  , active       := boxesCompC
  , logUpdate    := some (fun s args => sealReceipt args.actor :: s.log)
  , restFrame    := fun k k' => rhConcrete k = rhConcrete k'
  , guardGates   := sealGuardGates
  , guardProp    := sealGuardProp
  , guardWidth   := 1
  , guardEncode  := sealGuardEncode
  , guardLocal   := sealGuardLocal
  , guardWidth_le := by decide }

/-! ### The concrete reference: actor 0 holds the sealer cap for pid 5 + the payload it seals. -/

/-- Concrete pre-state: actor 0 holds `[sealerCap 5, node 9]` (the sealer cap for pid 5 makes
`holdsSealCapFor 5` fire; `node 9` is the payload it seals, so `payload ∈ caps 0` holds). Empty
sealedBoxes. Accounts {0,1}. -/
def kPre : RecordKernelState :=
  { accounts := {0, 1}, cell := fun _ => default
  , caps := fun l => if l = 0 then [sealerCap 5, Cap.node 9] else []
  , sealedBoxes := [] }

def sPre : RecChainedState := { kernel := kPre, log := [] }

/-- The seal args: actor 0 seals the `node 9` cap under pair 5. -/
def argsRef : SealArgs := { pid := 5, actor := 0, payload := Cap.node 9 }

def sPost : RecChainedState := (sealChainA sPre argsRef.pid argsRef.actor argsRef.payload).getD sPre

/-- **THE FORGERY:** the SAME guard/log/frame, but the prepended box binds a DIFFERENT payload
(`node 42` not the sealed `node 9`) — a cap-substitution. The component-bind gate must reject it. -/
def sForged : RecChainedState :=
  { sPost with kernel := { sPost.kernel with
      sealedBoxes := { pairId := 5, sealer := 0, payload := Cap.node 42 } :: kPre.sealedBoxes } }

def witnessOf (s : RecChainedState) (args : SealArgs) (s' : RecChainedState) : List Int :=
  (List.range (sealEC.traceWidth)).map (fun w => encodeE2 SC sealEC s args s' w)

def sealWitnessVec (s : RecChainedState) (args : SealArgs) : List Int :=
  match sealChainA s args.pid args.actor args.payload with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

theorem sealWitnessVec_commit {s s' : RecChainedState} {args : SealArgs}
    (h : sealChainA s args.pid args.actor args.payload = some s') :
    sealWitnessVec s args = witnessOf s args s' := by
  unfold sealWitnessVec; rw [h]

def honestWitness : List Int := sealWitnessVec sPre argsRef
def forgedWitness : List Int := witnessOf sPre argsRef sForged

#guard honestWitness.length == 72
#guard forgedWitness.length == 72
#guard decide (satisfied (effectCircuit2 sealEC) (encodeE2 SC sealEC sPre argsRef sPost))
#guard decide (satisfied (effectCircuit2 sealEC) (encodeE2 SC sealEC sPre argsRef sForged)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)
#guard honestWitness.getD 0 0 == 1
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0
#guard forgedWitness.getD 66 0 == forgedWitness.getD 67 0
#guard forgedWitness.getD 70 0 == forgedWitness.getD 71 0

/-! ## §5 — JSON export. -/

def sealAirName : String := "dregg-sealA-v2"
def emittedSeal : EmittedDescriptor := emittedEffect2 sealAirName sealEC
def descriptorJson : String := emitDescriptorJson emittedSeal
def witnessJson (xs : List Int) : String := "[" ++ String.intercalate "," (xs.map toString) ++ "]"
def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

#guard emittedSeal.constraints.length == 4
#guard emittedSeal.traceWidth == 72
#guard descriptorJson ==
  "{\"name\":\"dregg-sealA-v2\",\"trace_width\":72,\"constraints\":[{\"lhs\":{\"t\":\"var\",\"v\":0},\"rhs\":{\"t\":\"const\",\"v\":1}},{\"lhs\":{\"t\":\"var\",\"v\":66},\"rhs\":{\"t\":\"var\",\"v\":67}},{\"lhs\":{\"t\":\"var\",\"v\":68},\"rhs\":{\"t\":\"var\",\"v\":69}},{\"lhs\":{\"t\":\"var\",\"v\":70},\"rhs\":{\"t\":\"var\",\"v\":71}}]}"
#guard honestWitness.getD 68 0 == 30039   -- component digest binds (sealed node 9)
#guard forgedWitness.getD 68 0 == 40632    -- forged component digest differs (substituted node 42)
#guard forgedWitness.getD 69 0 == 30039    -- expected stays the spec box prepend
#guard honestWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,38,30338,36,36,30039,30039,263,263]"
#guard forgedWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,38,40931,36,36,40632,30039,263,263]"

#assert_axioms sealWitnessVec_commit
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.SealWitness
