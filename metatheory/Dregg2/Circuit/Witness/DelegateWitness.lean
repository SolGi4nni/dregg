/-
# Dregg2.Circuit.Witness.DelegateWitness — the v2 WITNESS GENERATOR for `delegate`.

This closes the verifiable-execution beachhead for `delegate` (the Granovetter unattenuated held-cap
copy), the SAME `execute → prove → verify → anti-ghost` path the validated `TransferWitness` reference
walks — but over the GENERIC v2 framework (`EffectCommit2`), since `delegate` touches a single non-`cell`
component (`kernel.caps`, a `funcComponent`). The pieces reused (not re-proved):

  * `Exec.recCDelegate` — the REAL chained executor (runs `recKDelegate`, prepends an authority receipt).
  * `Inst.Delegate.delegate_full_sound` — a satisfying v2 full-state witness PROVES the complete
    declarative `DelegateSpec` (all 17 kernel fields + log), carrying the realizable Poseidon-CR portals.
  * `EffectCommit2.effect2_circuit_full_complete` — every apex-satisfying step yields a satisfying witness.
  * `EffectCommit2.emittedEffect2` / `CircuitEmit.emitDescriptorJson` — the wire form the Rust prover ingests.

THE MISSING PIECE supplied here:

  * §3 ABSTRACT execute→prove (`execute_produces_satisfying_witness`) and verify→accept
    (`satisfying_witness_proves_full_state`), at the abstract surface (CR portals carried, the template's
    soundness form).
  * §4 a CONCRETE witness GENERATOR `delegateWitnessVec` that RUNS `recCDelegate` and lays the full-state
    v2 witness (width 72) out as a flat `List Int`, every digest column filled by a CONCRETE computable
    commitment surface (`rhConcrete`/`lhConcrete`/`capsDigConcrete`) over the executor's post-state. The
    `#guard`s certify (decidably, no `native_decide`): the executor-derived witness SATISFIES the v2
    circuit, and a REAL forged post-state (the recipient's `caps` slot tampered — a stolen extra cap)
    yields a witness the circuit REJECTS (the component-bind gate 68≠69 = a real UNSAT).
  * §5 the descriptor JSON + witness JSON the Rust `lean_executor_derived_delegate` prover proves+verifies
    (honest) and rejects (forged).

The Poseidon-CR portals are carried HYPOTHESES on the abstract
keystones (exactly the template).
-/
import Dregg2.Circuit.Inst.delegate
import Dregg2.Circuit.Poseidon2Surface

namespace Dregg2.Circuit.Witness.DelegateWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.Inst.Delegate
open Dregg2.Circuit.Spec.AuthorityUnattenuated
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

/-! ## §3 — THE ABSTRACT EXECUTE→PROVE / PROVE→STATE theorems (CR portals carried).

Both halves at the ABSTRACT `Surface2` level — the soundness form. The concrete surface in §4 is
the toy that makes the specific `#guard`s decide, not a CR hash. -/

variable (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)

/-- **`execute_produces_satisfying_witness` — the execute→prove direction.** A `DelegateSpec`-satisfying
step (the executor's `DelegateSpec` corner, `recCDelegate_iff_spec`) makes the v2 full-state witness
`encodeE2 … s args s'` SATISFY the v2 circuit. Reuses `effect2_circuit_full_complete` via the
`apex_iff_delegateSpec` bridge. THIS is "running the kernel IS generating a valid witness", for the REAL
full-state v2 circuit. -/
theorem execute_produces_satisfying_witness
    (hRest : RestIffNoCaps S.RH)
    (s : RecChainedState) (args : DelegateArgs) (s' : RecChainedState)
    (hspec : DelegateSpec s args.del args.recipient args.target s') :
    satisfiedE2 S (delegateE D hD) (encodeE2 S (delegateE D hD) s args s') :=
  effect2_circuit_full_complete S (delegateE D hD)
    (fun k k' h => (hRest k k').mpr h) (delegateGuardEncodes D hD) s args s'
    ((apex_iff_delegateSpec D hD s args s').mpr hspec)

/-- **`satisfying_witness_proves_full_state` — the verify→accept direction (soundness).** ANY witness
satisfying the v2 circuit proves the complete declarative `DelegateSpec` (all 17 kernel fields + log) —
so a verifier that accepts the proof has certified the WHOLE post-state, not a projection. Reuses
`Inst.Delegate.delegate_full_sound`; carries the realizable Poseidon-CR portals (`RestIffNoCaps`,
`logHashInjective`, `Function.Injective D`). -/
theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoCaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : DelegateArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (delegateE D hD) (encodeE2 S (delegateE D hD) s args s')) :
    DelegateSpec s args.del args.recipient args.target s' :=
  delegate_full_sound S D hD hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS (the bytes the Rust prover proves).

A CONCRETE, COMPUTABLE commitment surface over a toy domain, exactly the role `chConcrete`/`cmbConcrete`/
`compressNConcrete` play in `TransferWitness`. The witness generator fills the digest columns from this
surface, so the produced numbers are REAL field values the Rust prover consumes. -/

/-- Field-binding `Auth` index (the 7-constructor enum, so the endpoint `rights` list is bound, not
dropped). -/
def authCode : Auth → ℤ
  | .read => 0 | .write => 1 | .grant => 2 | .call => 3 | .reply => 4 | .reset => 5 | .control => 6

/-- **Field-binding** `Cap` encoder: a tag + target + the WHOLE `rights` list (length-prefixed). The OLD
`capCode` collapsed `endpoint t r => 500 + t`, DROPPING `r` entirely (so an attenuation forgery on the
granted rights was invisible). This binds every field. -/
def encCap : Cap → List ℤ
  | .null         => [0]
  | .node t       => [1, (t : ℤ)]
  | .endpoint t r => 2 :: (t : ℤ) :: (r.length : ℤ) :: r.map authCode

/-- One cell's cap-list digest: the REAL `refP2` sponge over the field-binding `encCap` (binds the whole
ordered list INCLUDING the endpoint rights — the OLD `capListCode` `% 1000` Horner dropped them). -/
def capListCode (cs : List Cap) : ℤ := recListDigest encCap cs

/-- Concrete computable caps digest over the fixed carrier `[0,1,2]`: the REAL `refP2` sponge of each
cell's cap-list digest. A tamper of ANY carrier cell's caps (including a forged-rights endpoint, EVEN
above the OLD `% 1000` window) changes this number. -/
def capsDigConcrete : Caps → ℤ :=
  fun caps => refP2 ([0, 1, 2].map (fun c => capListCode (caps c)))

/-- Concrete rest hash: a field-count of the non-`caps` components (account cardinality + nullifier
length) — unchanged by a pure `caps` forgery, so the rest-frame gate is not the one that bites; the
COMPONENT-bind gate is. -/
def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ)

/-- Concrete log hash: the REAL `turnLogDigest` (`refP2` over the FULL `encTurnRec`, binding
`src`/`dst` which the OLD `actor*1000 + amt` fold DROPPED). -/
def lhConcrete : List Turn → ℤ := turnLogDigest

/-- The concrete v2 surface. -/
def SC : Surface2 := { RH := rhConcrete, LH := lhConcrete }

/-- The concrete `caps` component: a computable digest (`capsDigConcrete`), the spec-expected being the
`recDelegateCaps` grant. `postClause := True` (the binding for the concrete `#guard` is the gate's
arithmetic equality, not a portal — `binds`/`encodes` are proof-irrelevant, as in the `*EWire` pattern). -/
def capsCompC : ActiveComponent RecChainedState DelegateArgs :=
  { digest    := fun k => capsDigConcrete k.caps
  , expected  := fun s args => capsDigConcrete (recDelegateCaps s.kernel.caps args.del args.recipient args.target)
  , postClause := fun s args post =>
      capsDigConcrete post.caps
        = capsDigConcrete (recDelegateCaps s.kernel.caps args.del args.recipient args.target)
  , binds     := fun _ _ _ h => h
  , encodes   := fun _ _ _ h => h }

/-- The concrete `delegate` effect spec (computable surface), for the witness `#guard`s. -/
def delegateEC : EffectSpec2 RecChainedState DelegateArgs :=
  { view         := chainView
  , active       := capsCompC
  , logUpdate    := some (fun s args => authReceipt args.del :: s.log)
  , restFrame    := fun _ _ => True
  , guardGates   := delegateGuardGates
  , guardProp    := delegateGuardProp
  , guardWidth   := 1
  , guardEncode  := delegateGuardEncode
  , guardLocal   := delegateGuardLocal
  , guardWidth_le := by decide }

/-! ### The concrete reference triple: actor 0 holds `node 5`, delegates to recipient 1. -/

/-- Concrete pre-state: cell 0 holds a `node 5` cap (confers an edge to target 5); cells 1,2 hold no
caps. Accounts {0,1,2}. -/
def kPre : RecordKernelState :=
  { accounts := {0, 1, 2}
  , cell := fun _ => default
  , caps := fun c => if c = 0 then [Cap.node 5] else [] }

/-- The chained pre-state (empty log). -/
def sPre : RecChainedState := { kernel := kPre, log := [] }

/-- The delegate args: delegator 0 grants recipient 1 a cap to target 5. -/
def argsRef : DelegateArgs := { del := 0, recipient := 1, target := 5 }

/-- The honest post-state (run the REAL executor `recCDelegate`). -/
def sPost : RecChainedState := (recCDelegate sPre 0 1 5).getD sPre

/-- **THE FORGERY:** the SAME guard/log, but recipient 1's `caps` slot is tampered — it gains an EXTRA
stolen `node 9` cap on top of the honest grant. The component-bind gate must reject it. -/
def sForged : RecChainedState :=
  { kernel := { kPre with caps := fun c => if c = 1 then [Cap.node 9, Cap.node 5] else kPre.caps c }
  , log := authReceipt 0 :: sPre.log }

/-! ### The witness vectors. -/

/-- Lay an `encodeE2 SC delegateEC s args s'` assignment out as a flat `List Int` of length 72. -/
def witnessOf (s : RecChainedState) (args : DelegateArgs) (s' : RecChainedState) : List Int :=
  (List.range (delegateEC.traceWidth)).map (fun w => encodeE2 SC delegateEC s args s' w)

/-- **`delegateWitnessVec` — the executor-driven witness generator.** Runs `recCDelegate`; on commit
produces the satisfying full-state witness for the executor's post-state, every digest column filled by
the concrete commitment surface. THIS is `execute → the satisfying assignment for the real v2 circuit`. -/
def delegateWitnessVec (s : RecChainedState) (args : DelegateArgs) : List Int :=
  match recCDelegate s args.del args.recipient args.target with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

theorem delegateWitnessVec_commit {s s' : RecChainedState} {args : DelegateArgs}
    (h : recCDelegate s args.del args.recipient args.target = some s') :
    delegateWitnessVec s args = witnessOf s args s' := by
  unfold delegateWitnessVec; rw [h]

/-- The honest executor-derived witness for the reference triple. -/
def honestWitness : List Int := delegateWitnessVec sPre argsRef

/-- The forged witness: the SAME pre/args but the REAL `sForged` post-state (recipient 1 stole `node 9`). -/
def forgedWitness : List Int := witnessOf sPre argsRef sForged

-- (1) the witnesses have the v2 trace width.
#guard honestWitness.length == 72
#guard forgedWitness.length == 72

-- (2) THE EXECUTE→PROVE GUARANTEE: the executor-derived witness SATISFIES the full-state v2 circuit.
#guard decide (satisfied (effectCircuit2 delegateEC) (encodeE2 SC delegateEC sPre argsRef sPost))

-- (3) THE ANTI-GHOST TOOTH (real UNSAT): the forged post-state's witness FAILS the circuit, and
--     specifically it is the COMPONENT-bind gate (68 ≠ 69) that breaks — the stolen cap is caught.
#guard decide (satisfied (effectCircuit2 delegateEC) (encodeE2 SC delegateEC sPre argsRef sForged)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)   -- compDigPost ≠ compDigExpected: REJECTED
-- ...while the forgery still keeps the rest frame + guard honest (so a projection circuit would pass):
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0      -- restDigPre = restDigPost
#guard forgedWitness.getD 66 0 == forgedWitness.getD 67 0      -- forgery preserves the rest frame
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0      -- honest component binds
#guard honestWitness.getD 0 0 == 1                              -- guard propBit = 1

-- RIGHTS-ATTENUATION anti-ghost tooth (the forgery class the OLD `capCode` MISSED — it dropped the
-- endpoint `rights` entirely). Recipient 1's slot is forged to hold an `endpoint 5 [grant]` (an
-- amplified-authority cap) instead of the honest grant. The OLD `endpoint t _ => 500+t` collapse made
-- this INVISIBLE; `encCap` binds the whole rights list, so the component-bind gate `68 ≠ 69` REJECTS.
def sForgedRights : RecChainedState :=
  { kernel := { kPre with caps := fun c => if c = 1 then [Cap.endpoint 5 [Auth.grant]] else kPre.caps c }
  , log := authReceipt 0 :: sPre.log }
#guard decide (satisfied (effectCircuit2 delegateEC) (encodeE2 SC delegateEC sPre argsRef sForgedRights)) == false

/-! ## §5 — JSON export of the descriptor + witness vectors (the bytes the Rust prover consumes). -/

def delegateAirName : String := "dregg-delegate-v2"

/-- The emitted v2 circuit (4 gates: guard bit + rest/component/log EQ), width 72. -/
def emittedDelegate : EmittedDescriptor := emittedEffect2 delegateAirName delegateEC

/-- The descriptor JSON the Rust `parse_descriptor` ingests. -/
def descriptorJson : String := emitDescriptorJson emittedDelegate

/-- Render a `List Int` as a JSON number array. -/
def witnessJson (xs : List Int) : String := "[" ++ String.intercalate "," (xs.map toString) ++ "]"

/-- The honest / forged executor-derived witnesses, as JSON arrays for the Rust prover. -/
def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

-- Sanity pins (decoded gate count + width).
#guard emittedDelegate.constraints.length == 4
#guard emittedDelegate.traceWidth == 72

-- The exact bytes the Rust `lean_executor_derived_delegate` test pastes (golden pins: a drift in the
-- executor/surface is caught HERE first). The constrained EQ wires (66/67 rest, 68/69 component,
-- 70/71 log) are small; the root wires 64/65 are unconstrained positional-Horner sums (fit i64).
#guard descriptorJson == "{\"name\":\"dregg-delegate-v2\",\"trace_width\":72,\"constraints\":[{\"lhs\":{\"t\":\"var\",\"v\":0},\"rhs\":{\"t\":\"const\",\"v\":1}},{\"lhs\":{\"t\":\"var\",\"v\":66},\"rhs\":{\"t\":\"var\",\"v\":67}},{\"lhs\":{\"t\":\"var\",\"v\":68},\"rhs\":{\"t\":\"var\",\"v\":69}},{\"lhs\":{\"t\":\"var\",\"v\":70},\"rhs\":{\"t\":\"var\",\"v\":71}}]}"
-- Structural component-bind goldens (the field-binding `refP2`/`encCap` digests are arbitrary-precision;
-- non-vacuity is at the bind gates; the Rust paste is regenerated from the JSON accessors).
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0      -- component binds (honest)
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)   -- forged component differs (REJECTED)
#guard !(honestWitnessJson == forgedWitnessJson)               -- honest ≠ forged byte streams

#assert_axioms delegateWitnessVec_commit
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.DelegateWitness
