/-
# Dregg2.Circuit.Witness.RevokeDelegationWitness — the v2 WITNESS GENERATOR for `revokeDelegationA`.

This closes the verifiable-execution beachhead for `revokeDelegationA` (the cap-graph `removeEdge`),
the SAME `execute → prove → verify → anti-ghost` path the validated `TransferWitness` /
`DelegateWitness` references walk — over the GENERIC v2 framework (`EffectCommit2`), since
`revokeDelegationA` touches a single non-`cell` component (`kernel.caps`, a `funcComponent`). Reused
(not re-proved):

  * `Exec.recCRevoke` — the REAL chained authority executor (runs `recKRevokeTarget`, prepends an
    authority receipt). It is UNCONDITIONAL (`recCRevoke st holder t = st'`, total).
  * `Inst.RevokeDelegationA.revokeDelegationA_full_sound` — a satisfying v2 full-state witness PROVES
    the complete declarative `RevokeSpec` (all 16 frame fields + caps + log), carrying the realizable
    Poseidon-CR portals.
  * `EffectCommit2.effect2_circuit_full_complete` — every apex-satisfying step yields a satisfying witness.
  * `EffectCommit2.emittedEffect2` / `CircuitEmit.emitDescriptorJson` — the wire form the Rust prover ingests.

THE MISSING PIECE supplied here:
  * §3 ABSTRACT execute→prove (`execute_produces_satisfying_witness`) + verify→accept
    (`satisfying_witness_proves_full_state`), at the abstract surface (CR portals carried).
  * §4 a CONCRETE witness GENERATOR `revokeWitnessVec` that RUNS `recCRevoke` and lays the full-state v2
    witness (width 72) out as a flat `List Int`, every digest column filled by a CONCRETE computable
    commitment surface over the executor's post-state. The `#guard`s certify (decidably): the
    executor-derived witness SATISFIES the v2 circuit, and a REAL forged post-state (a cap-graph that
    FAILS to revoke — keeps the `node t` cap) yields a witness the circuit REJECTS (the component-bind
    gate 68≠69 = a real UNSAT).
  * §5 the descriptor JSON + witness JSON the Rust `lean_executor_derived_revoke_delegation` prover
    proves+verifies (honest) and rejects (forged).

The Poseidon-CR portals are carried HYPOTHESES on the
abstract keystones (the template).
-/
import Dregg2.Circuit.Inst.revokeDelegationA
import Dregg2.Circuit.Poseidon2Surface

namespace Dregg2.Circuit.Witness.RevokeDelegationWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Inst.RevokeDelegationA
open Dregg2.Circuit.Spec.AuthorityRevocation
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap Auth)
open Dregg2.Circuit.Poseidon2Surface (refP2 recListDigest turnLogDigest)

set_option linter.dupNamespace false

/-! ## §0 — decidability re-exports (so the executor-derived `#guard`s can `decide`). -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §3 — THE ABSTRACT EXECUTE→PROVE / PROVE→STATE theorems (CR portals carried). -/

variable (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)

/-- **`execute_produces_satisfying_witness` — the execute→prove direction.** A `RevokeSpec`-satisfying
step (the executor's `RevokeSpec` corner, `recCRevoke_iff_spec`) makes the v2 full-state witness
`encodeE2 … s args s'` SATISFY the v2 circuit. Reuses `effect2_circuit_full_complete` via the
`apex_iff_revokeSpec` bridge. THIS is "running the kernel IS generating a valid witness", for the REAL
full-state v2 circuit. -/
theorem execute_produces_satisfying_witness
    (hRest : RestIffNoCaps S.RH)
    (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState)
    (hspec : RevokeSpec s args.holder args.t s') :
    satisfiedE2 S (revokeDelegationE D hD) (encodeE2 S (revokeDelegationE D hD) s args s') :=
  effect2_circuit_full_complete S (revokeDelegationE D hD)
    (fun k k' h => (hRest k k').mpr h) (revokeGuardEncodes D hD) s args s'
    ((apex_iff_revokeSpec D hD s args s').mpr hspec)

/-- **`satisfying_witness_proves_full_state` — the verify→accept direction (soundness).** ANY witness
satisfying the v2 circuit proves the complete declarative `RevokeSpec` (all 16 frame fields + caps +
log) — so a verifier that accepts the proof has certified the WHOLE post-state, not a projection.
Reuses `Inst.RevokeDelegationA.revokeDelegationA_full_sound`; carries the realizable Poseidon-CR
portals (`RestIffNoCaps`, `logHashInjective`, `Function.Injective D`). -/
theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (revokeDelegationE D hD) (encodeE2 S (revokeDelegationE D hD) s args s')) :
    RevokeSpec s args.holder args.t s' :=
  revokeDelegationA_full_sound S D hD hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS (the bytes the Rust prover proves).

A CONCRETE, COMPUTABLE commitment surface over a toy domain (the role `capCode`/`capsDigConcrete` play
in `DelegateWitness`). Every primitive stays SMALL (mod a prime) so the folded digests fit i64 — the
v2 gate only checks EQUALITY, so a bounded computable hash suffices. -/

/-- Field-binding `Auth` index (so endpoint `rights` are bound, not collapsed to `.length`). -/
def authCode : Auth → ℤ
  | .read => 0 | .write => 1 | .grant => 2 | .call => 3 | .reply => 4 | .reset => 5 | .control => 6
  | .notify => 7   -- async-signal authority; RESERVED code (no cap emits it yet ⇒ VK byte-identical)
/-- **Field-binding** `Cap` encoder: tag + target + the WHOLE rights list (the OLD `capCode` reduced
`endpoint t r => 11 + t*3 + r.length`, dropping WHICH rights for the LENGTH). -/
def encCap : Cap → List ℤ
  | .null         => [0]
  | .node t       => [1, (t : ℤ)]
  | .endpoint t r => 2 :: (t : ℤ) :: (r.length : ℤ) :: r.map authCode

/-- One cell's cap-list digest: the REAL `refP2` sponge over the field-binding `encCap` (the OLD
`% 2000003` Horner was a NON-injective field hash). -/
def capListCode (cs : List Cap) : ℤ := recListDigest encCap cs

/-- Concrete caps digest over the fixed label window `[0,4)`: the REAL `refP2` sponge of each cell's
cap-list digest. -/
def capsDigConcrete : Caps → ℤ :=
  fun caps => refP2 ((List.range 4).map (fun l => capListCode (caps l)))

/-- Concrete rest hash: reads only the NON-`caps` frame fields (so a pure cap forgery leaves it fixed —
the COMPONENT-bind gate bites, not the rest gate). -/
def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ) * 7
           + (k.commitments.length : ℤ) * 13 + (k.revoked.length : ℤ) * 17

/-- Concrete log hash: the REAL `turnLogDigest` (binds `src`/`dst`/`amt` the OLD `actor % 2000003` fold
DROPPED and field-reduced). -/
def lhConcrete : List Turn → ℤ := turnLogDigest

/-- The concrete v2 surface. -/
def SC : Surface2 := { RH := rhConcrete, LH := lhConcrete }

/-- The concrete `caps` component (computable digest), spec-expected being `removeEdgeCaps`.
`binds`/`encodes` are proof-irrelevant for the concrete `#guard` (the gate's arithmetic equality is
the binding); the abstract soundness is `revokeDelegationA_full_sound`. -/
def capsCompC : ActiveComponent RecChainedState RevokeArgs :=
  { digest    := fun k => capsDigConcrete k.caps
  , expected  := fun s args => capsDigConcrete (removeEdgeCaps s.kernel.caps args.holder args.t)
  , postClause := fun s args post =>
      capsDigConcrete post.caps
        = capsDigConcrete (removeEdgeCaps s.kernel.caps args.holder args.t)
  , binds     := fun _ _ _ h => h
  , encodes   := fun _ _ _ h => h }

/-- The concrete `revokeDelegationA` effect spec (computable surface), for the witness `#guard`s. -/
def revokeEC : EffectSpec2 RecChainedState RevokeArgs :=
  { view         := chainView
  , active       := capsCompC
  , logUpdate    := some (fun s args => authReceipt args.holder :: s.log)
  , restFrame    := fun k k' => rhConcrete k = rhConcrete k'
  , guardGates   := revokeGuardGates
  , guardProp    := revokeGuardProp
  , guardWidth   := 1
  , guardEncode  := revokeGuardEncode
  , guardLocal   := revokeGuardLocal
  , guardWidth_le := by decide }

/-! ### The concrete reference triple: holder 0 holds `[node 5, node 7]`, revokes the edge to 5. -/

/-- Concrete pre-state: holder 0 = `[node 5, node 7]` (only `node 5` confers an edge to target 5);
label 1 = `[node 9]`; others empty. Accounts {0,1}. -/
def kPre : RecordKernelState :=
  { accounts := {0, 1}
  , cell := fun _ => default
  , caps := fun l => if l = 0 then [Cap.node 5, Cap.node 7]
                     else if l = 1 then [Cap.node 9]
                     else [] }

/-- The chained pre-state (empty log). -/
def sPre : RecChainedState := { kernel := kPre, log := [] }

/-- The revoke args: holder 0 revokes every cap conferring an edge to target 5. -/
def argsRef : RevokeArgs := { holder := 0, t := 5 }

/-- The honest post-state (run the REAL executor `recCRevoke`: caps 0 → `[node 7]`, log grows). -/
def sPost : RecChainedState := recCRevoke sPre argsRef.holder argsRef.t

/-- **THE FORGERY:** the SAME guard/log/frame, but the post `caps` FAIL to revoke — holder 0 keeps
`[node 5, node 7]` (the `node 5` edge to target 5 is NOT removed). A bearer of the supposedly-revoked
cap stays authorized: an authority-forgery the component-bind gate must catch. -/
def sForged : RecChainedState :=
  { sPost with kernel := { sPost.kernel with caps := kPre.caps } }

/-! ### The witness vectors. -/

/-- Lay an `encodeE2 SC revokeEC s args s'` assignment out as a flat `List Int` of length 72. -/
def witnessOf (s : RecChainedState) (args : RevokeArgs) (s' : RecChainedState) : List Int :=
  (List.range (revokeEC.traceWidth)).map (fun w => encodeE2 SC revokeEC s args s' w)

/-- **`revokeWitnessVec` — the executor-driven witness generator.** Runs the REAL executor
`recCRevoke` (unconditional) and produces the satisfying full-state witness for the executor's
post-state, every digest column filled by the concrete commitment surface. THIS is
`execute → the satisfying assignment for the real v2 circuit`. -/
def revokeWitnessVec (s : RecChainedState) (args : RevokeArgs) : List Int :=
  witnessOf s args (recCRevoke s args.holder args.t)

theorem revokeWitnessVec_commit (s : RecChainedState) (args : RevokeArgs) :
    revokeWitnessVec s args = witnessOf s args (recCRevoke s args.holder args.t) := rfl

/-- The honest executor-derived witness for the reference triple. -/
def honestWitness : List Int := revokeWitnessVec sPre argsRef

/-- The forged witness: the SAME pre/args but the REAL `sForged` post-state (un-revoked `node 5`). -/
def forgedWitness : List Int := witnessOf sPre argsRef sForged

-- (1) the witnesses have the v2 trace width.
#guard honestWitness.length == 72
#guard forgedWitness.length == 72

-- (2) THE EXECUTE→PROVE GUARANTEE: the executor-derived witness SATISFIES the full-state v2 circuit.
#guard decide (satisfied (effectCircuit2 revokeEC) (encodeE2 SC revokeEC sPre argsRef sPost))

-- (3) THE ANTI-GHOST TOOTH (real UNSAT): the forged post-state's witness FAILS the circuit, and
--     specifically it is the COMPONENT-bind gate (68 ≠ 69) that breaks — the un-revoked cap is caught.
#guard decide (satisfied (effectCircuit2 revokeEC) (encodeE2 SC revokeEC sPre argsRef sForged)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)   -- compDigPost ≠ compDigExpected: REJECTED
-- ...while the forgery still keeps the rest frame + guard + log honest (a projection circuit would pass):
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0      -- restDigPre = restDigPost
#guard forgedWitness.getD 66 0 == forgedWitness.getD 67 0      -- forgery preserves the rest frame
#guard forgedWitness.getD 70 0 == forgedWitness.getD 71 0      -- forgery preserves the log
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0      -- honest component binds
#guard honestWitness.getD 0 0 == 1                              -- guard propBit = 1

-- RIGHTS-ATTENUATION anti-ghost tooth: instead of un-revoking, holder 0's slot is forged to a
-- `node 7 ++ endpoint 5 [grant]` (the revoked target 5 re-appears as an AMPLIFIED endpoint). The OLD
-- rights-LENGTH `capCode` over `% 2000003` could alias such tampers; `encCap` binds the full rights so
-- the component-bind gate `68 ≠ 69` REJECTS.
def sForgedRights : RecChainedState :=
  { sPost with kernel := { sPost.kernel with
      caps := fun l => if l = 0 then [Cap.node 7, Cap.endpoint 5 [Auth.grant]] else sPost.kernel.caps l } }
#guard decide (satisfied (effectCircuit2 revokeEC) (encodeE2 SC revokeEC sPre argsRef sForgedRights)) == false

/-! ## §5 — JSON export of the descriptor + witness vectors (the bytes the Rust prover consumes). -/

def revokeAirName : String := "dregg-revokeDelegationA-v2"

/-- The emitted v2 circuit (4 gates: guard bit + rest/component/log EQ), width 72. -/
def emittedRevoke : EmittedDescriptor := emittedEffect2 revokeAirName revokeEC

/-- The descriptor JSON the Rust `parse_descriptor` ingests. -/
def descriptorJson : String := emitDescriptorJson emittedRevoke

/-- Render a `List Int` as a JSON number array. -/
def witnessJson (xs : List Int) : String := "[" ++ String.intercalate "," (xs.map toString) ++ "]"

def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

#guard emittedRevoke.constraints.length == 4
#guard emittedRevoke.traceWidth == 72

-- The exact bytes the Rust `lean_executor_derived_revoke_delegation` test pastes (golden pins).
#guard descriptorJson ==
  "{\"name\":\"dregg-revokeDelegationA-v2\",\"trace_width\":72,\"constraints\":[{\"lhs\":{\"t\":\"var\",\"v\":0},\"rhs\":{\"t\":\"const\",\"v\":1}},{\"lhs\":{\"t\":\"var\",\"v\":66},\"rhs\":{\"t\":\"var\",\"v\":67}},{\"lhs\":{\"t\":\"var\",\"v\":68},\"rhs\":{\"t\":\"var\",\"v\":69}},{\"lhs\":{\"t\":\"var\",\"v\":70},\"rhs\":{\"t\":\"var\",\"v\":71}}]}"
-- Structural component-bind goldens (the field-binding `refP2`/`encCap` digests replace the non-injective
-- `% 2000003` field hashes; non-vacuity is at the bind gates; the Rust paste is regenerated from JSON).
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0      -- component binds (honest)
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)   -- forged component differs (REJECTED)
#guard !(honestWitnessJson == forgedWitnessJson)               -- honest ≠ forged byte streams

#assert_axioms revokeWitnessVec_commit
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.RevokeDelegationWitness
