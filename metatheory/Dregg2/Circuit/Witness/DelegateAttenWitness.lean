/-
# Dregg2.Circuit.Witness.DelegateAttenWitness — execute→prove→verify→anti-ghost for `delegateAttenA`.

Amplifies the `Transfer` beachhead to the GATED, ATTENUATED authority grant `delegateAttenA` through
the v2 framework (`EffectCommit2`), the SAME `execute → prove → verify → anti-ghost` path the validated
`TransferWitness`/`DelegateWitness` references walk (a `caps`-component effect). REUSED (not re-proved):

  * `Exec.execFullA` — the real chained executor (`.delegateAttenA del recv t keep` arm =
    `recCDelegateAtten`, the gated attenuated grant + authority receipt).
  * `Spec.AuthorityAttenuation.delegateAtten_iff_spec` — executor ⟺ `DelegateAttenSpec`.
  * `Inst.DelegateAttenA.{delegateAttenE, apex_iff_delegateAttenSpec, delegateAttenA_full_sound}`.
  * `EffectCommit2.{encodeE2, satisfiedE2, effect2_circuit_full_complete}`.
  * `Witness.DelegateWitness.{capsDigConcrete, rhConcrete, lhConcrete, witnessJson}` — the concrete
    caps-table commitment surface (a positional Horner fold over `[0,1,2]`'s cap-lists).

SUPPLIED: §3 the abstract execute→prove / prove→state halves; §4 the executor-driven witness generator
`delegateAttenWitnessVec` (runs `execFullA`, lays the v2 width-72 witness over the concrete surface)
with the concrete `#guard`s; §5 the JSON the Rust `lean_executor_derived_delegate_atten` prover
proves+verifies / rejects. ANTI-GHOST: a forged post-state where recipient 1 STEALS an extra `node 9`
cap on top of the attenuated grant — the component-bind gate (68/69) rejects (a real UNSAT), while the
rest frame + guard + log stay honest (a projection circuit would have passed it).

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Circuit.Inst.delegateAttenA
import Dregg2.Circuit.Witness.DelegateWitness

namespace Dregg2.Circuit.Witness.DelegateAttenWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Inst.DelegateAttenA
open Dregg2.Circuit.Spec.AuthorityAttenuation
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap Auth)

set_option linter.dupNamespace false

/-! ## §0 — decidability re-exports. -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §3 — THE ABSTRACT EXECUTE→PROVE / PROVE→STATE theorems (CR portals carried). -/

variable (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)

/-- **`execute_produces_satisfying_witness` — execute→prove.** A `DelegateAttenSpec`-satisfying step
makes the v2 full-state witness SATISFY the v2 circuit. Reuses `effect2_circuit_full_complete` via
`apex_iff_delegateAttenSpec`; the rest-frame ENCODE leg is `RestIffNoCaps.←`. -/
theorem execute_produces_satisfying_witness
    (hRest : RestIffNoCaps S.RH)
    (s : RecChainedState) (args : DelegateAttenArgs) (s' : RecChainedState)
    (hspec : DelegateAttenSpec s args.del args.recv args.t args.keep s') :
    satisfiedE2 S (delegateAttenE D hD) (encodeE2 S (delegateAttenE D hD) s args s') :=
  effect2_circuit_full_complete S (delegateAttenE D hD)
    (fun k k' h => (hRest k k').mpr h) (delAttenGuardEncodes D hD) s args s'
    ((apex_iff_delegateAttenSpec D hD s args s').mpr hspec)

/-- **`satisfying_witness_proves_full_state` — prove→accept.** ANY witness satisfying the v2 circuit
proves the complete declarative `DelegateAttenSpec` (all 17 kernel fields + log). Reuses
`delegateAttenA_full_sound`. -/
theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : DelegateAttenArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (delegateAttenE D hD) (encodeE2 S (delegateAttenE D hD) s args s')) :
    DelegateAttenSpec s args.del args.recv args.t args.keep s' :=
  delegateAttenA_full_sound S D hD hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS (the bytes the Rust prover proves).

The concrete caps-table commitment surface is REUSED from `DelegateWitness` (the same `capsDigConcrete`
positional Horner fold over `[0,1,2]`). The component's `expected` is the ATTENUATED grant. -/

open Dregg2.Circuit.Witness.DelegateWitness (capsDigConcrete witnessJson)

/-- The concrete `caps` component for the attenuated grant: a computable digest, the spec-expected being
`grant caps recv (attenuate keep (heldCapTo caps del t))`. `binds`/`encodes` are proof-irrelevant (the
concrete `#guard` rides the gate's arithmetic equality, as in `DelegateWitness.capsCompC`). -/
def capsCompC : ActiveComponent RecChainedState DelegateAttenArgs :=
  { digest     := fun k => capsDigConcrete k.caps
  , expected   := fun s args =>
      capsDigConcrete (grant s.kernel.caps args.recv
        (attenuate args.keep (heldCapTo s.kernel.caps args.del args.t)))
  , postClause := fun s args post =>
      capsDigConcrete post.caps
        = capsDigConcrete (grant s.kernel.caps args.recv
            (attenuate args.keep (heldCapTo s.kernel.caps args.del args.t)))
  , binds      := fun _ _ _ h => h
  , encodes    := fun _ _ _ h => h }

/-- The concrete `delegateAttenA` effect spec (computable surface), for the witness `#guard`s. -/
def delAttenEC : EffectSpec2 RecChainedState DelegateAttenArgs :=
  { view         := chainView
  , active       := capsCompC
  , logUpdate    := some (fun s args => authReceipt args.del :: s.log)
  , restFrame    := fun _ _ => True
  , guardGates   := delAttenGuardGates
  , guardProp    := delAttenGuardProp
  , guardWidth   := 1
  , guardEncode  := delAttenGuardEncode
  , guardLocal   := delAttenGuardLocal
  , guardWidth_le := by decide }

/-- The concrete v2 surface (reused from `DelegateWitness`). -/
def SC : Surface2 :=
  { RH := Dregg2.Circuit.Witness.DelegateWitness.rhConcrete
  , LH := Dregg2.Circuit.Witness.DelegateWitness.lhConcrete }

/-! ### The concrete reference triple: delegator 0 holds `node 5`, attenuated-grants to recipient 1. -/

def kPre : RecordKernelState :=
  { accounts := {0, 1, 2}
  , cell := fun _ => default
  , caps := fun c => if c = 0 then [Cap.node 5] else [] }

def sPre : RecChainedState := { kernel := kPre, log := [] }
def argsRef : DelegateAttenArgs := { del := 0, recv := 1, t := 5, keep := [Auth.write] }
def sPost : RecChainedState := (execFullA sPre (.delegateAttenA 0 1 5 [Auth.write])).getD sPre

/-- **THE FORGERY:** the SAME guard/log, but recipient 1's `caps` slot gains an EXTRA stolen `node 9`
cap on top of the attenuated grant. The component-bind gate (68/69) must reject it. -/
def sForged : RecChainedState :=
  { kernel := { kPre with
      caps := fun c => if c = 1 then Cap.node 9 :: sPost.kernel.caps c else sPost.kernel.caps c }
  , log := sPost.log }

def witnessOf (s : RecChainedState) (args : DelegateAttenArgs) (s' : RecChainedState) : List Int :=
  (List.range delAttenEC.traceWidth).map (fun w => encodeE2 SC delAttenEC s args s' w)

/-- **`delegateAttenWitnessVec`** — runs `execFullA`; on commit lays out the satisfying v2 witness. -/
def delegateAttenWitnessVec (s : RecChainedState) (args : DelegateAttenArgs) : List Int :=
  match execFullA s (.delegateAttenA args.del args.recv args.t args.keep) with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

theorem delegateAttenWitnessVec_commit {s s' : RecChainedState} {args : DelegateAttenArgs}
    (h : execFullA s (.delegateAttenA args.del args.recv args.t args.keep) = some s') :
    delegateAttenWitnessVec s args = witnessOf s args s' := by
  unfold delegateAttenWitnessVec; rw [h]

def honestWitness : List Int := delegateAttenWitnessVec sPre argsRef
def forgedWitness : List Int := witnessOf sPre argsRef sForged

#guard honestWitness.length == 72
#guard forgedWitness.length == 72

-- THE EXECUTE→PROVE GUARANTEE: the executor-derived witness SATISFIES the v2 circuit.
#guard decide (satisfied (effectCircuit2 delAttenEC) (encodeE2 SC delAttenEC sPre argsRef sPost))
-- THE ANTI-GHOST TOOTH (real UNSAT): the forged post-state's witness FAILS — component gate 68 ≠ 69.
#guard decide (satisfied (effectCircuit2 delAttenEC) (encodeE2 SC delAttenEC sPre argsRef sForged)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)   -- compDigPost ≠ compDigExpected: REJECTED
-- ...while the forgery keeps the rest frame + guard honest (a projection circuit would pass it):
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0
#guard forgedWitness.getD 66 0 == forgedWitness.getD 67 0
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard honestWitness.getD 0 0 == 1

/-! ## §5 — JSON export. -/

def delegateAttenAirName : String := "dregg-delegateAttenA-v2"
def emittedDelegateAtten : EmittedDescriptor := emittedEffect2 delegateAttenAirName delAttenEC
def descriptorJson : String := emitDescriptorJson emittedDelegateAtten
def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

#guard emittedDelegateAtten.constraints.length == 4
#guard emittedDelegateAtten.traceWidth == 72
#guard descriptorJson == "{\"name\":\"dregg-delegateAttenA-v2\",\"trace_width\":72,\"constraints\":[{\"lhs\":{\"t\":\"var\",\"v\":0},\"rhs\":{\"t\":\"const\",\"v\":1}},{\"lhs\":{\"t\":\"var\",\"v\":66},\"rhs\":{\"t\":\"var\",\"v\":67}},{\"lhs\":{\"t\":\"var\",\"v\":68},\"rhs\":{\"t\":\"var\",\"v\":69}},{\"lhs\":{\"t\":\"var\",\"v\":70},\"rhs\":{\"t\":\"var\",\"v\":71}}]}"
#guard honestWitness.getD 68 0 == 1015001015000000
#guard forgedWitness.getD 68 0 == 1017019015000000
#guard forgedWitness.getD 69 0 == 1015001015000000

#assert_axioms delegateAttenWitnessVec_commit
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.DelegateAttenWitness
