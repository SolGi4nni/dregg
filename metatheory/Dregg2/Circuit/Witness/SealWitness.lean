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

CR portals carried HYPOTHESES on the abstract keystones.
-/
import Dregg2.Circuit.Inst.sealA
import Dregg2.Circuit.Poseidon2Surface

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
open Dregg2.Circuit.Poseidon2Surface (refP2 recListDigest turnLogDigest)

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

/-- Field-binding `Auth` index. -/
def authCode : Auth → ℤ
  | .read => 0 | .write => 1 | .grant => 2 | .call => 3 | .reply => 4 | .reset => 5 | .control => 6
/-- **Field-binding** `Cap` encoder (binds the SEALED payload's full rights — the OLD `capCode` reduced
`endpoint`'s rights to their `.length`, so the sealed payload's authority was under-bound). -/
def encCap : Cap → List ℤ
  | .null         => [0]
  | .node t       => [1, (t : ℤ)]
  | .endpoint t r => 2 :: (t : ℤ) :: (r.length : ℤ) :: r.map authCode

/-- **Field-binding** `SealedBoxRecord` encoder: `pairId, sealer` then the WHOLE payload cap. The OLD
`boxCode … % 2000003` was a NON-injective field hash that folded the payload through the rights-dropping
`capCode`. -/
def encBox (b : SealedBoxRecord) : List ℤ := (b.pairId : ℤ) :: (b.sealer : ℤ) :: encCap b.payload

/-- The sealed-boxes list digest: the REAL `refP2` sponge over the field-binding `encBox`. -/
def boxDigConcrete : List SealedBoxRecord → ℤ := recListDigest encBox

def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ) * 7
           + (k.commitments.length : ℤ) * 13 + (k.caps 0).length * 17

/-- The log hash: the REAL `turnLogDigest` (binds `src`/`dst`/`amt` the OLD `actor % 2000003` fold
DROPPED and field-reduced). -/
def lhConcrete : List Turn → ℤ := turnLogDigest

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

-- PAYLOAD-RIGHTS anti-ghost tooth: the prepended box binds a SEALED payload forged to
-- `endpoint 9 [grant]` (an amplified-authority cap) instead of the honest `node 9`. The OLD `boxCode`
-- folded the payload through the rights-dropping `capCode % 2000003`, so the sealed authority was
-- under-bound; `encBox`/`encCap` bind the full payload rights, so the component-bind gate `68 ≠ 69`
-- REJECTS — sealing a wrong-authority cap is caught.
def sForgedRights : RecChainedState :=
  { sPost with kernel := { sPost.kernel with
      sealedBoxes := { pairId := 5, sealer := 0, payload := Cap.endpoint 9 [Auth.grant] }
        :: kPre.sealedBoxes } }
#guard decide (satisfied (effectCircuit2 sealEC) (encodeE2 SC sealEC sPre argsRef sForgedRights)) == false

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
-- Structural component-bind goldens (the field-binding `refP2`/`encBox` digests replace the non-injective
-- `% 2000003` field hash; non-vacuity is at the bind gates; the Rust paste is regenerated from JSON).
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0      -- component binds (honest)
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)   -- forged component differs (REJECTED)
#guard !(honestWitnessJson == forgedWitnessJson)               -- honest ≠ forged byte streams

#assert_axioms sealWitnessVec_commit
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.SealWitness
