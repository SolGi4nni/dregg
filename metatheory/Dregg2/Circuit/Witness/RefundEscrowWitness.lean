/-
# Dregg2.Circuit.Witness.RefundEscrowWitness — the v2-DUAL WITNESS GENERATOR for `refundEscrowA`.

Closes the verifiable-execution beachhead for `refundEscrowA` (the dual-component escrow refund: CREDIT
the per-asset ledger `bal` at the CREATOR AND mark the `EscrowRecord` resolved in `escrows`), the SAME
`execute → prove → verify → anti-ghost` path as `ReleaseEscrowWitness` — over the GENERIC v2-DUAL
framework (`EffectCommit2Dual`). Reused (not re-proved):

  * `Exec.execFullA` — `execFullA s (.refundEscrowA id actor) = some s'` IS the post-state.
  * `Spec.EscrowHoldingRefund.execFullA_refundEscrowA_iff_spec` — executor ⟺ `RefundEscrowSpec`.
  * `Inst.RefundEscrowA.{refundEscrowE, apex_iff_refundEscrowSpec, refundEscrowA_full_sound}`.
  * `EffectCommit2Dual.{encodeE2Dual, effect2dual_circuit_full_complete, emittedEffect2Dual}`.

The Poseidon-CR portals are carried HYPOTHESES.
-/
import Dregg2.Circuit.Inst.refundEscrowA
import Dregg2.Circuit.Spec.escrowholdingrelease
import Dregg2.Circuit.Poseidon2Surface

namespace Dregg2.Circuit.Witness.RefundEscrowWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.EffectCommit2Dual
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Inst.RefundEscrowA
open Dregg2.Circuit.Spec.EscrowHoldingRefund
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Poseidon2Surface (refP2 recListDigest encEscrowRec turnLogDigest)

set_option linter.dupNamespace false

/-! ## §0 — decidability re-exports (so the executor-derived `#guard`s can `decide`). -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §3 — THE ABSTRACT EXECUTE→PROVE / PROVE→STATE theorems (CR portals carried). -/

variable (S : Surface2) (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
  (LE : EscrowRecord → ℤ) (cN : List ℤ → ℤ)
  (hN : compressNInjective cN) (hLE : listLeafInjective LE)

theorem execute_produces_satisfying_witness
    (hRest : RestIffNoBalEscrows S.RH)
    (s : RecChainedState) (args : RefundEscrowArgs) (s' : RecChainedState)
    (hspec : RefundEscrowSpec s args.id args.actor s') :
    satisfiedE2Dual S (refundEscrowE D hD LE cN hN hLE)
      (encodeE2Dual S (refundEscrowE D hD LE cN hN hLE) s args s') :=
  effect2dual_circuit_full_complete S (refundEscrowE D hD LE cN hN hLE)
    (fun k k' h => (hRest k k').mpr h)
    (refundEscrowGuardEncodes D hD LE cN hN hLE) s args s'
    ((apex_iff_refundEscrowSpec D hD LE cN hN hLE s args s').mpr hspec)

theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RefundEscrowArgs) (s' : RecChainedState)
    (h : satisfiedE2Dual S (refundEscrowE D hD LE cN hN hLE)
        (encodeE2Dual S (refundEscrowE D hD LE cN hN hLE) s args s')) :
    RefundEscrowSpec s args.id args.actor s' :=
  refundEscrowA_full_sound S D hD LE cN hN hLE hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS (the bytes the Rust prover proves). -/

/-- The `bal` digest: the REAL `refP2` sponge over the (cell 0-3 × asset 0-1) ledger entries (binds each —
the OLD `(… ) % 2000003` modular fold was a TRUE field hash, NOT injective: it could COLLIDE two distinct
ledgers). `refP2` is the genuinely-injective CR-grounded sponge. -/
def balDigConcrete : (CellId → AssetId → ℤ) → ℤ :=
  fun bal => refP2 ((List.range 4).flatMap (fun c => (List.range 2).map (fun a => bal c a)))

/-- The escrows-list digest: the REAL `refP2` sponge over the field-binding `encEscrowRec` (binds ALL nine
fields — the OLD `escrowCode … % 2000003` was a non-injective field hash dropping `creator`/`asset`/…). -/
def escrowsDigConcrete : List EscrowRecord → ℤ := recListDigest encEscrowRec

def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ) * 7
           + (k.commitments.length : ℤ) * 13 + (k.swiss.length : ℤ) * 17

/-- The log hash: the REAL `turnLogDigest` (`refP2` over the FULL `encTurnRec`, binding `src`/`dst`/`amt`
which the OLD `actor … % 2000003` fold DROPPED and field-reduced). -/
def lhConcrete : List Turn → ℤ := turnLogDigest

def SC : Surface2 := { RH := rhConcrete, LH := lhConcrete }

/-- The concrete `bal` component (computable digest), spec-expected being the CREATOR credit. -/
def balCompC : ActiveComponent RecChainedState RefundEscrowArgs :=
  { digest    := fun k => balDigConcrete k.bal
  , expected  := fun s args => balDigConcrete (balExpected s args)
  , postClause := fun s args post => balDigConcrete post.bal = balDigConcrete (balExpected s args)
  , binds     := fun _ _ _ h => h
  , encodes   := fun _ _ _ h => h }

def escrowsCompC : ActiveComponent RecChainedState RefundEscrowArgs :=
  { digest    := fun k => escrowsDigConcrete k.escrows
  , expected  := fun s args => escrowsDigConcrete (markResolved s.kernel.escrows args.id)
  , postClause := fun s args post =>
      escrowsDigConcrete post.escrows = escrowsDigConcrete (markResolved s.kernel.escrows args.id)
  , binds     := fun _ _ _ h => h
  , encodes   := fun _ _ _ h => h }

def refundEC : EffectSpec2Dual RecChainedState RefundEscrowArgs :=
  { view         := chainView
  , active1      := balCompC
  , active2      := escrowsCompC
  , logUpdate    := some (fun s args => escrowReceiptA args.actor :: s.log)
  , restFrame    := fun k k' => rhConcrete k = rhConcrete k'
  , guardGates   := refundEscrowGuardGates
  , guardProp    := refundEscrowGuardProp
  , guardWidth   := 1
  , guardEncode  := refundEscrowGuardEncode
  , guardLocal   := refundEscrowGuardLocal
  , guardWidth_le := by decide }

/-! ### The concrete reference: escrow 7 (creator 0 ← refund of 30); actor 0 self-authorized. -/

/-- Concrete pre-state: accounts {0,1}; actor 0 == creator 0 (self-auth refund); escrows = [escrow 7
parking 30 of asset 0, creator 0 / recipient 1]. -/
def sPre : RecChainedState :=
  { kernel := { accounts := {0, 1}
                cell := fun _ => .record [("balance", .int 0)]
                caps := fun _ => []
                escrows := [{ id := 7, creator := 0, recipient := 1, amount := 30,
                              resolved := false, asset := 0 }] }
    log := [] }

/-- The refund args: refund escrow 7, actor 0 (= creator, self-authorized). -/
def argsRef : RefundEscrowArgs := { id := 7, actor := 0 }

/-- The honest post-state (run the REAL executor: bal 0 0 ← +30, escrow 7 → resolved, log grows). -/
def sPost : RecChainedState := (execFullA sPre (.refundEscrowA 7 0)).getD sPre

/-- **THE FORGERY:** the SAME guard/log/frame/escrows, but the `bal` refund is MINTED beyond the parked
amount — creator 0 gains 999 (not the parked 30) at asset 0. A value-forgery the comp1-bind gate
(68/69) must catch. -/
def sForged : RecChainedState :=
  { sPost with kernel := { sPost.kernel with
      bal := fun c a => if c = 0 ∧ a = 0 then 999 else sPost.kernel.bal c a } }

/-! ### The witness vectors. -/

def witnessOf (s : RecChainedState) (args : RefundEscrowArgs) (s' : RecChainedState) : List Int :=
  (List.range (refundEC.traceWidth)).map (fun w => encodeE2Dual SC refundEC s args s' w)

/-- **`refundWitnessVec` — the executor-driven witness generator.** Runs `execFullA`; on commit
produces the satisfying dual full-state witness for the executor's post-state. -/
def refundWitnessVec (s : RecChainedState) (args : RefundEscrowArgs) : List Int :=
  match execFullA s (.refundEscrowA args.id args.actor) with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

theorem refundWitnessVec_commit {s s' : RecChainedState} {args : RefundEscrowArgs}
    (h : execFullA s (.refundEscrowA args.id args.actor) = some s') :
    refundWitnessVec s args = witnessOf s args s' := by
  unfold refundWitnessVec; rw [h]

def honestWitness : List Int := refundWitnessVec sPre argsRef
def forgedWitness : List Int := witnessOf sPre argsRef sForged

#guard honestWitness.length == 74
#guard forgedWitness.length == 74

-- THE EXECUTE→PROVE GUARANTEE: the executor-derived witness SATISFIES the full-state dual circuit.
#guard decide (satisfied (effectCircuit2Dual refundEC) (encodeE2Dual SC refundEC sPre argsRef sPost))

-- THE ANTI-GHOST TOOTH (real UNSAT): the forged post-state FAILS on the comp1-bind gate (68 ≠ 69).
#guard decide (satisfied (effectCircuit2Dual refundEC) (encodeE2Dual SC refundEC sPre argsRef sForged)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0
#guard forgedWitness.getD 66 0 == forgedWitness.getD 67 0
#guard forgedWitness.getD 70 0 == forgedWitness.getD 71 0
#guard forgedWitness.getD 72 0 == forgedWitness.getD 73 0
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0
#guard honestWitness.getD 0 0 == 1

/-- HIGH-field MODULAR-COLLISION anti-ghost tooth: the creator's refunded balance forged by EXACTLY the
old modulus `2000003` (so `bal ≡ honest (mod 2000003)`). The OLD `% 2000003` field hash COLLIDED here
(forged ≡ honest), accepting the tamper; `refP2` is genuinely injective and the `bal` bind gate `68 ≠ 69`
REJECTS. -/
def sForgedMod : RecChainedState :=
  { sPost with kernel := { sPost.kernel with
      bal := fun c a => if c = 0 ∧ a = 0 then sPost.kernel.bal 0 0 + 2000003 else sPost.kernel.bal c a } }
#guard decide (satisfied (effectCircuit2Dual refundEC) (encodeE2Dual SC refundEC sPre argsRef sForgedMod)) == false

/-! ## §5 — JSON export of the descriptor + witness vectors. -/

def refundAirName : String := "dregg-refundEscrowA-v2dual"

def emittedRefund : EmittedDescriptor := emittedEffect2Dual refundAirName refundEC

def descriptorJson : String := emitDescriptorJson emittedRefund

def witnessJson (xs : List Int) : String := "[" ++ String.intercalate "," (xs.map toString) ++ "]"

def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

#guard emittedRefund.constraints.length == 5
#guard emittedRefund.traceWidth == 74

-- The exact bytes the Rust `lean_executor_derived_refund_escrow` test pastes.
#guard descriptorJson ==
  "{\"name\":\"dregg-refundEscrowA-v2dual\",\"trace_width\":74,\"constraints\":[{\"lhs\":{\"t\":\"var\",\"v\":0},\"rhs\":{\"t\":\"const\",\"v\":1}},{\"lhs\":{\"t\":\"var\",\"v\":66},\"rhs\":{\"t\":\"var\",\"v\":67}},{\"lhs\":{\"t\":\"var\",\"v\":68},\"rhs\":{\"t\":\"var\",\"v\":69}},{\"lhs\":{\"t\":\"var\",\"v\":70},\"rhs\":{\"t\":\"var\",\"v\":71}},{\"lhs\":{\"t\":\"var\",\"v\":72},\"rhs\":{\"t\":\"var\",\"v\":73}}]}"
-- Structural bind-gate goldens (the field-binding `refP2`/`encEscrowRec` digests are arbitrary-precision,
-- replacing the non-injective `% 2000003` field hashes; non-vacuity is at the bind gates; the Rust paste
-- is regenerated from the JSON accessors when the prover field-reduces).
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0   -- bal binds (honest)
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0   -- escrows binds (honest)
#guard honestWitness.getD 72 0 == honestWitness.getD 73 0   -- log binds (honest)
#guard !(honestWitnessJson == forgedWitnessJson)            -- honest ≠ forged byte streams

#assert_axioms refundWitnessVec_commit
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.RefundEscrowWitness
