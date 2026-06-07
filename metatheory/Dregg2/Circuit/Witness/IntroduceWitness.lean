/-
# Dregg2.Circuit.Witness.IntroduceWitness — execute→prove→verify→anti-ghost for `introduceA`.

Amplifies the `Transfer` beachhead to the authority-INTRODUCE effect `introduceA` (the unattenuated
held-cap copy, definitionally the same `recCDelegate` primitive) through the v2 framework
(`EffectCommit2`). REUSED (not re-proved):

  * `Exec.execFullA` — the real chained executor (`.introduceA intro recip t` arm, `recCDelegate` via
    `execFullA_introduceA_eq`, an `rfl`).
  * `Spec.AuthorityUnattenuated.execFullA_introduceA_iff_spec` — executor ⟺ `DelegateSpec`.
  * `Inst.IntroduceA.{introduceE, apex_iff_delegateSpec, introduceA_full_sound}`.
  * `EffectCommit2.{encodeE2, satisfiedE2, effect2_circuit_full_complete}`.
  * `Witness.DelegateWitness.{capsDigConcrete, witnessJson}` — the concrete caps-table surface.

SUPPLIED: §3 the abstract execute→prove / prove→state halves; §4 the executor-driven witness generator
`introduceWitnessVec` (runs `execFullA`, lays the v2 width-72 witness over the concrete surface) with
the concrete `#guard`s; §5 the JSON the Rust `lean_executor_derived_introduce` prover proves+verifies /
rejects. ANTI-GHOST: a forged post-state where recipient 1 STEALS an extra `node 9` cap on top of the
introduced grant — the component-bind gate (68/69) rejects (a real UNSAT).

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Circuit.Inst.introduceA
import Dregg2.Circuit.Witness.DelegateWitness

namespace Dregg2.Circuit.Witness.IntroduceWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Inst.IntroduceA
open Dregg2.Circuit.Spec.AuthorityUnattenuated
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

/-- **`execute_produces_satisfying_witness` — execute→prove.** A `DelegateSpec`-satisfying step makes
the v2 full-state witness SATISFY the v2 circuit. Reuses `effect2_circuit_full_complete` via
`apex_iff_delegateSpec`. -/
theorem execute_produces_satisfying_witness
    (hRest : RestIffNoCaps S.RH)
    (s : RecChainedState) (args : IntroduceArgs) (s' : RecChainedState)
    (hspec : DelegateSpec s args.intro args.recip args.t s') :
    satisfiedE2 S (introduceE D hD) (encodeE2 S (introduceE D hD) s args s') :=
  effect2_circuit_full_complete S (introduceE D hD)
    (fun k k' h => (hRest k k').mpr h) (introduceGuardEncodes D hD) s args s'
    ((apex_iff_delegateSpec D hD s args s').mpr hspec)

/-- **`satisfying_witness_proves_full_state` — prove→accept.** ANY witness satisfying the v2 circuit
proves the complete declarative `DelegateSpec` (all 17 kernel fields + log). Reuses
`introduceA_full_sound`. -/
theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : IntroduceArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (introduceE D hD) (encodeE2 S (introduceE D hD) s args s')) :
    DelegateSpec s args.intro args.recip args.t s' :=
  introduceA_full_sound S D hD hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS. The concrete caps surface is REUSED from
`DelegateWitness`; the component's `expected` is `recDelegateCaps`. -/

open Dregg2.Circuit.Witness.DelegateWitness (capsDigConcrete witnessJson)

def capsCompC : ActiveComponent RecChainedState IntroduceArgs :=
  { digest     := fun k => capsDigConcrete k.caps
  , expected   := fun s args => capsDigConcrete (recDelegateCaps s.kernel.caps args.intro args.recip args.t)
  , postClause := fun s args post =>
      capsDigConcrete post.caps
        = capsDigConcrete (recDelegateCaps s.kernel.caps args.intro args.recip args.t)
  , binds      := fun _ _ _ h => h
  , encodes    := fun _ _ _ h => h }

def introduceEC : EffectSpec2 RecChainedState IntroduceArgs :=
  { view         := chainView
  , active       := capsCompC
  , logUpdate    := some (fun s args => authReceipt args.intro :: s.log)
  , restFrame    := fun _ _ => True
  , guardGates   := introduceGuardGates
  , guardProp    := introduceGuardProp
  , guardWidth   := 1
  , guardEncode  := introduceGuardEncode
  , guardLocal   := introduceGuardLocal
  , guardWidth_le := by decide }

def SC : Surface2 :=
  { RH := Dregg2.Circuit.Witness.DelegateWitness.rhConcrete
  , LH := Dregg2.Circuit.Witness.DelegateWitness.lhConcrete }

/-! ### The concrete reference triple: introducer 0 holds `node 5`, introduces recipient 1 to 5. -/

def kPre : RecordKernelState :=
  { accounts := {0, 1, 2}
  , cell := fun _ => default
  , caps := fun c => if c = 0 then [Cap.node 5] else [] }

def sPre : RecChainedState := { kernel := kPre, log := [] }
def argsRef : IntroduceArgs := { intro := 0, recip := 1, t := 5 }
def sPost : RecChainedState := (execFullA sPre (.introduceA 0 1 5)).getD sPre

/-- **THE FORGERY:** the SAME guard/log, but recipient 1's `caps` slot gains an EXTRA stolen `node 9`
cap on top of the introduced grant. The component-bind gate (68/69) must reject it. -/
def sForged : RecChainedState :=
  { kernel := { kPre with
      caps := fun c => if c = 1 then Cap.node 9 :: sPost.kernel.caps c else sPost.kernel.caps c }
  , log := sPost.log }

def witnessOf (s : RecChainedState) (args : IntroduceArgs) (s' : RecChainedState) : List Int :=
  (List.range introduceEC.traceWidth).map (fun w => encodeE2 SC introduceEC s args s' w)

/-- **`introduceWitnessVec`** — runs `execFullA`; on commit lays out the satisfying v2 witness. -/
def introduceWitnessVec (s : RecChainedState) (args : IntroduceArgs) : List Int :=
  match execFullA s (.introduceA args.intro args.recip args.t) with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

theorem introduceWitnessVec_commit {s s' : RecChainedState} {args : IntroduceArgs}
    (h : execFullA s (.introduceA args.intro args.recip args.t) = some s') :
    introduceWitnessVec s args = witnessOf s args s' := by
  unfold introduceWitnessVec; rw [h]

def honestWitness : List Int := introduceWitnessVec sPre argsRef
def forgedWitness : List Int := witnessOf sPre argsRef sForged

#guard honestWitness.length == 72
#guard forgedWitness.length == 72

#guard decide (satisfied (effectCircuit2 introduceEC) (encodeE2 SC introduceEC sPre argsRef sPost))
#guard decide (satisfied (effectCircuit2 introduceEC) (encodeE2 SC introduceEC sPre argsRef sForged)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)   -- component-bind: REJECTED
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0
#guard forgedWitness.getD 66 0 == forgedWitness.getD 67 0
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard honestWitness.getD 0 0 == 1

/-! ## §5 — JSON export. -/

def introduceAirName : String := "dregg-introduceA-v2"
def emittedIntroduce : EmittedDescriptor := emittedEffect2 introduceAirName introduceEC
def descriptorJson : String := emitDescriptorJson emittedIntroduce
def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

#guard emittedIntroduce.constraints.length == 4
#guard emittedIntroduce.traceWidth == 72
#guard descriptorJson == "{\"name\":\"dregg-introduceA-v2\",\"trace_width\":72,\"constraints\":[{\"lhs\":{\"t\":\"var\",\"v\":0},\"rhs\":{\"t\":\"const\",\"v\":1}},{\"lhs\":{\"t\":\"var\",\"v\":66},\"rhs\":{\"t\":\"var\",\"v\":67}},{\"lhs\":{\"t\":\"var\",\"v\":68},\"rhs\":{\"t\":\"var\",\"v\":69}},{\"lhs\":{\"t\":\"var\",\"v\":70},\"rhs\":{\"t\":\"var\",\"v\":71}}]}"
#guard !(honestWitness.getD 68 0 == forgedWitness.getD 68 0)
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0

#assert_axioms introduceWitnessVec_commit
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.IntroduceWitness
