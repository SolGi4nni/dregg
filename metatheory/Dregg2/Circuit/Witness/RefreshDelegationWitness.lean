/-
# Dregg2.Circuit.Witness.RefreshDelegationWitness — the v2 WITNESS GENERATOR for `refreshDelegationA`.

Closes the verifiable-execution beachhead for `refreshDelegationA` (the parent-c-list snapshot into the
`delegations` field), the SAME `execute → prove → verify → anti-ghost` path the validated
`DelegateWitness`/`RevokeDelegationWitness` references walk — over the GENERIC v2 framework
(`EffectCommit2`), since `refreshDelegationA` touches a single non-`cell` component
(`kernel.delegations`, a `funcComponent` over `CellId → List Cap`). Reused (not re-proved):

  * `Exec.execFullA` — `execFullA s (.refreshDelegationA actor child) = some s'` IS the post-state.
  * `Spec.RefreshDelegation.refreshDelegation_iff_spec` — executor ⟺ `RefreshDelegationSpec`.
  * `Inst.RefreshDelegationA.{refreshDelegationE, apex_iff_refreshDelegationSpec,
    refreshDelegationA_full_sound}`.
  * `EffectCommit2.{encodeE2, effect2_circuit_full_complete, emittedEffect2}`.

No `sorry`/`admit`/`axiom`/`native_decide`. The Poseidon-CR portals are carried HYPOTHESES on the
abstract keystones (the template).
-/
import Dregg2.Circuit.Inst.refreshDelegationA

namespace Dregg2.Circuit.Witness.RefreshDelegationWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Inst.RefreshDelegationA
open Dregg2.Circuit.Spec.RefreshDelegation
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap)

set_option linter.dupNamespace false

/-! ## §0 — decidability re-exports (so the executor-derived `#guard`s can `decide`). -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §3 — THE ABSTRACT EXECUTE→PROVE / PROVE→STATE theorems (CR portals carried). -/

variable (S : Surface2) (D : (CellId → List Cap) → ℤ) (hD : Function.Injective D)

/-- **`execute_produces_satisfying_witness`.** A `RefreshDelegationSpec`-satisfying step (the executor's
corner `refreshDelegation_iff_spec`) makes the v2 full-state witness SATISFY the v2 circuit. -/
theorem execute_produces_satisfying_witness
    (hRest : RestIffNoDelegations S.RH)
    (s : RecChainedState) (args : RefreshDelegationArgs) (s' : RecChainedState)
    (hspec : RefreshDelegationSpec s args.actor args.child s') :
    satisfiedE2 S (refreshDelegationE D hD) (encodeE2 S (refreshDelegationE D hD) s args s') :=
  effect2_circuit_full_complete S (refreshDelegationE D hD)
    (fun k k' h => (hRest k k').mpr h) (refreshDelegationGuardEncodes D hD) s args s'
    ((apex_iff_refreshDelegationSpec D hD s args s').mpr hspec)

/-- **`satisfying_witness_proves_full_state`.** ANY witness satisfying the v2 circuit proves the complete
declarative `RefreshDelegationSpec`. Reuses `refreshDelegationA_full_sound`. -/
theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoDelegations S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RefreshDelegationArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (refreshDelegationE D hD) (encodeE2 S (refreshDelegationE D hD) s args s')) :
    RefreshDelegationSpec s args.actor args.child s' :=
  refreshDelegationA_full_sound S D hD hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS (the bytes the Rust prover proves). -/

/-- Concrete computable per-`Cap` code (tag + target), kept small. -/
def capCode : Cap → ℤ
  | .null         => 1
  | .node t       => 101 + (t : ℤ) * 3
  | .endpoint t r => 11 + (t : ℤ) * 3 + (r.length : ℤ)

/-- Concrete computable cap-list code: a small modular Horner fold (length-tagged). -/
def capListCode (cs : List Cap) : ℤ :=
  cs.foldl (fun acc c => (acc * 131 + capCode c) % 2000003) ((cs.length : ℤ) + 1)

/-- Concrete delegations digest over the fixed label window `[0,4)`, mod a small prime. A tamper of ANY
window cell's delegation c-list changes this number. -/
def delegationsDigConcrete : (CellId → List Cap) → ℤ :=
  fun dg => (List.range 4).foldl (fun acc l => (acc * 7919 + capListCode (dg l)) % 2000003) 1

/-- Concrete rest hash: reads only NON-`delegations` frame fields (so a pure delegation forgery leaves
it fixed — the COMPONENT-bind gate bites, not the rest gate). -/
def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ) * 7
           + (k.commitments.length : ℤ) * 13 + (k.swiss.length : ℤ) * 17

/-- Concrete log hash: a small modular Horner fold over the receipt actors. -/
def lhConcrete : List Turn → ℤ :=
  fun xs => xs.foldl (fun acc t => (acc * 131 + (t.actor : ℤ) + 1) % 2000003) ((xs.length : ℤ) + 1)

/-- The concrete v2 surface. -/
def SC : Surface2 := { RH := rhConcrete, LH := lhConcrete }

/-- The concrete `delegations` component (computable digest), spec-expected being `refreshDelegationsMap`.
`binds`/`encodes` are proof-irrelevant for the concrete `#guard` (the gate's arithmetic equality is the
binding); the abstract soundness is `refreshDelegationA_full_sound`. -/
def delegationsCompC : ActiveComponent RecChainedState RefreshDelegationArgs :=
  { digest    := fun k => delegationsDigConcrete k.delegations
  , expected  := fun s args => delegationsDigConcrete (refreshDelegationsMap s.kernel args.child)
  , postClause := fun s args post =>
      delegationsDigConcrete post.delegations
        = delegationsDigConcrete (refreshDelegationsMap s.kernel args.child)
  , binds     := fun _ _ _ h => h
  , encodes   := fun _ _ _ h => h }

/-- The concrete `refreshDelegationA` effect spec (computable surface), for the witness `#guard`s. -/
def refreshEC : EffectSpec2 RecChainedState RefreshDelegationArgs :=
  { view         := chainView
  , active       := delegationsCompC
  , logUpdate    := some (fun s args => refreshDelegationReceipt args.actor args.child :: s.log)
  , restFrame    := fun k k' => rhConcrete k = rhConcrete k'
  , guardGates   := refreshDelegationGuardGates
  , guardProp    := refreshDelegationGuardProp
  , guardWidth   := 1
  , guardEncode  := refreshDelegationGuardEncode
  , guardLocal   := refreshDelegationGuardLocal
  , guardWidth_le := by decide }

/-! ### The concrete reference: child 1 has parent 0; cell 0 holds `[node 5]`; refresh snapshots it. -/

/-- Concrete pre-state: cell 0 holds caps `[node 5]`; child 1's parent pointer is `some 0`; delegations
all empty. Accounts {0,1}. -/
def kPre : RecordKernelState :=
  { accounts := {0, 1}
  , cell := fun _ => default
  , caps := fun l => if l = 0 then [Cap.node 5] else []
  , delegate := fun c => if c = 1 then some 0 else none
  , delegations := fun _ => [] }

/-- The chained pre-state (empty log). -/
def sPre : RecChainedState := { kernel := kPre, log := [] }

/-- The refresh args: actor 1 = child 1 (self-auth), child has parent 0. -/
def argsRef : RefreshDelegationArgs := { actor := 1, child := 1 }

/-- The honest post-state (run the REAL executor: delegations 1 ← parentClist = caps 0 = [node 5]). -/
def sPost : RecChainedState := (execFullA sPre (.refreshDelegationA 1 1)).getD sPre

/-- **THE FORGERY:** the SAME guard/log/frame, but the post `delegations` snapshot is TAMPERED — child 1
gains an EXTRA stolen `node 9` cap on top of the honest parent snapshot. A delegate-authority forgery
the component-bind gate must catch. -/
def sForged : RecChainedState :=
  { sPost with kernel := { sPost.kernel with
      delegations := fun c => if c = 1 then [Cap.node 9, Cap.node 5] else sPost.kernel.delegations c } }

/-! ### The witness vectors. -/

/-- Lay an `encodeE2 SC refreshEC s args s'` assignment out as a flat `List Int` of length 72. -/
def witnessOf (s : RecChainedState) (args : RefreshDelegationArgs) (s' : RecChainedState) : List Int :=
  (List.range (refreshEC.traceWidth)).map (fun w => encodeE2 SC refreshEC s args s' w)

/-- **`refreshWitnessVec` — the executor-driven witness generator.** Runs `execFullA`; on commit
produces the satisfying full-state witness for the executor's post-state. -/
def refreshWitnessVec (s : RecChainedState) (args : RefreshDelegationArgs) : List Int :=
  match execFullA s (.refreshDelegationA args.actor args.child) with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

theorem refreshWitnessVec_commit {s s' : RecChainedState} {args : RefreshDelegationArgs}
    (h : execFullA s (.refreshDelegationA args.actor args.child) = some s') :
    refreshWitnessVec s args = witnessOf s args s' := by
  unfold refreshWitnessVec; rw [h]

def honestWitness : List Int := refreshWitnessVec sPre argsRef
def forgedWitness : List Int := witnessOf sPre argsRef sForged

-- (1) the witnesses have the v2 trace width.
#guard honestWitness.length == 72
#guard forgedWitness.length == 72

-- (2) THE EXECUTE→PROVE GUARANTEE: the executor-derived witness SATISFIES the full-state v2 circuit.
#guard decide (satisfied (effectCircuit2 refreshEC) (encodeE2 SC refreshEC sPre argsRef sPost))

-- (3) THE ANTI-GHOST TOOTH (real UNSAT): the forged post-state's witness FAILS on the component-bind
--     gate (68 ≠ 69) — the stolen delegation cap is caught.
#guard decide (satisfied (effectCircuit2 refreshEC) (encodeE2 SC refreshEC sPre argsRef sForged)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0
#guard forgedWitness.getD 66 0 == forgedWitness.getD 67 0
#guard forgedWitness.getD 70 0 == forgedWitness.getD 71 0
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard honestWitness.getD 0 0 == 1

/-! ## §5 — JSON export of the descriptor + witness vectors (the bytes the Rust prover consumes). -/

def refreshAirName : String := "dregg-refreshDelegationA-v2"

def emittedRefresh : EmittedDescriptor := emittedEffect2 refreshAirName refreshEC

def descriptorJson : String := emitDescriptorJson emittedRefresh

def witnessJson (xs : List Int) : String := "[" ++ String.intercalate "," (xs.map toString) ++ "]"

def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

#guard emittedRefresh.constraints.length == 4
#guard emittedRefresh.traceWidth == 72

-- The exact bytes the Rust `lean_executor_derived_refresh_delegation` test pastes.
#guard descriptorJson ==
  "{\"name\":\"dregg-refreshDelegationA-v2\",\"trace_width\":72,\"constraints\":[{\"lhs\":{\"t\":\"var\",\"v\":0},\"rhs\":{\"t\":\"const\",\"v\":1}},{\"lhs\":{\"t\":\"var\",\"v\":66},\"rhs\":{\"t\":\"var\",\"v\":67}},{\"lhs\":{\"t\":\"var\",\"v\":68},\"rhs\":{\"t\":\"var\",\"v\":69}},{\"lhs\":{\"t\":\"var\",\"v\":70},\"rhs\":{\"t\":\"var\",\"v\":71}}]}"
#guard honestWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,927922,774219,2,2,773953,773953,264,264]"
#guard forgedWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,927922,710615,2,2,710349,773953,264,264]"

#assert_axioms refreshWitnessVec_commit
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.RefreshDelegationWitness
