/-
# Dregg2.Circuit.Witness.ReleaseEscrowWitness — the v2-DUAL WITNESS GENERATOR for `releaseEscrowA`.

Closes the verifiable-execution beachhead for `releaseEscrowA` (the canonical dual-component escrow
settle: CREDIT the per-asset ledger `bal` AND mark the `EscrowRecord` resolved in `escrows`), the SAME
`execute → prove → verify → anti-ghost` path the validated references walk — over the GENERIC v2-DUAL
framework (`EffectCommit2Dual`), since `releaseEscrowA` touches TWO non-`cell` components (`bal`, a
`funcComponent`, and `escrows`, a `listComponent`). Reused (not re-proved):

  * `Exec.execFullA` — `execFullA s (.releaseEscrowA id actor) = some s'` IS the post-state.
  * `Spec.EscrowHoldingRelease.execFullA_releaseEscrow_iff_spec` — executor ⟺ `ReleaseEscrowSpec`.
  * `Inst.ReleaseEscrowA.{releaseEscrowE, apex_iff_releaseEscrowSpec, releaseEscrowA_full_sound}`.
  * `EffectCommit2Dual.{encodeE2Dual, effect2dual_circuit_full_complete, emittedEffect2Dual}`.

The dual circuit (width 74, 5 gates): guard(0), rest(66=67), bind1(68=69, `bal`), bind2(70=71,
`escrows`), log(72=73). The anti-ghost forgery tampers comp1 (`bal`): a minted recipient credit beyond
the parked amount breaks gate 68=69.

The Poseidon-CR portals are carried HYPOTHESES on the
abstract keystones.
-/
import Dregg2.Circuit.Inst.releaseEscrowA
import Dregg2.Circuit.Poseidon2Surface

namespace Dregg2.Circuit.Witness.ReleaseEscrowWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.EffectCommit2Dual
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Inst.ReleaseEscrowA
open Dregg2.Circuit.Spec.EscrowHoldingRelease
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

/-- **`execute_produces_satisfying_witness`.** A `ReleaseEscrowSpec`-satisfying step (the executor's
corner `execFullA_releaseEscrow_iff_spec`) makes the dual full-state witness SATISFY the dual circuit. -/
theorem execute_produces_satisfying_witness
    (hRest : RestIffNoBalEscrows S.RH)
    (s : RecChainedState) (args : ReleaseArgs) (s' : RecChainedState)
    (hspec : ReleaseEscrowSpec s args.id args.actor s') :
    satisfiedE2Dual S (releaseEscrowE D hD LE cN hN hLE)
      (encodeE2Dual S (releaseEscrowE D hD LE cN hN hLE) s args s') :=
  effect2dual_circuit_full_complete S (releaseEscrowE D hD LE cN hN hLE)
    (fun k k' h => (hRest k k').mpr h)
    (releaseEscrowGuardEncodes D hD LE cN hN hLE) s args s'
    ((apex_iff_releaseEscrowSpec D hD LE cN hN hLE s args s').mpr hspec)

/-- **`satisfying_witness_proves_full_state`.** ANY witness satisfying the dual circuit proves the
complete declarative `ReleaseEscrowSpec`. Reuses `releaseEscrowA_full_sound`. -/
theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : ReleaseArgs) (s' : RecChainedState)
    (h : satisfiedE2Dual S (releaseEscrowE D hD LE cN hN hLE)
        (encodeE2Dual S (releaseEscrowE D hD LE cN hN hLE) s args s')) :
    ReleaseEscrowSpec s args.id args.actor s' :=
  releaseEscrowA_full_sound S D hD LE cN hN hLE hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS (the bytes the Rust prover proves). -/

/-- The `bal` digest: the REAL `refP2` sponge over the (cell 0-3 × asset 0-1) ledger entries (binds each —
the OLD `(…) % 2000003` modular fold was a TRUE field hash, NOT injective: it could COLLIDE two distinct
ledgers). `refP2` is the genuinely-injective CR-grounded sponge. -/
def balDigConcrete : (CellId → AssetId → ℤ) → ℤ :=
  fun bal => refP2 ((List.range 4).flatMap (fun c => (List.range 2).map (fun a => bal c a)))

/-- The `escrows` list digest: the REAL `refP2` sponge over the field-binding `encEscrowRec` (binds ALL
nine fields — the OLD `escrowCode … % 2000003` was a non-injective field hash dropping `creator`/`asset`/…). -/
def escrowsDigConcrete : List EscrowRecord → ℤ := recListDigest encEscrowRec

/-- Concrete rest hash: reads only NON-`bal`/`escrows` frame fields (so a pure bal/escrows forgery
leaves it fixed — a component-bind gate bites, not the rest gate). -/
def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ) * 7
           + (k.commitments.length : ℤ) * 13 + (k.swiss.length : ℤ) * 17

/-- The log hash: the REAL `turnLogDigest` (`refP2` over the FULL `encTurnRec`, binding `src`/`dst`/`amt`
which the OLD `actor … % 2000003` fold DROPPED and field-reduced). -/
def lhConcrete : List Turn → ℤ := turnLogDigest

/-- The concrete v2 surface. -/
def SC : Surface2 := { RH := rhConcrete, LH := lhConcrete }

/-- The concrete `bal` component (computable digest), spec-expected being the recipient credit. -/
def balCompC : ActiveComponent RecChainedState ReleaseArgs :=
  { digest    := fun k => balDigConcrete k.bal
  , expected  := fun s args => balDigConcrete (balExpected s args)
  , postClause := fun s args post => balDigConcrete post.bal = balDigConcrete (balExpected s args)
  , binds     := fun _ _ _ h => h
  , encodes   := fun _ _ _ h => h }

/-- The concrete `escrows` component (computable digest), spec-expected being `markResolved`. -/
def escrowsCompC : ActiveComponent RecChainedState ReleaseArgs :=
  { digest    := fun k => escrowsDigConcrete k.escrows
  , expected  := fun s args => escrowsDigConcrete (markResolved s.kernel.escrows args.id)
  , postClause := fun s args post =>
      escrowsDigConcrete post.escrows = escrowsDigConcrete (markResolved s.kernel.escrows args.id)
  , binds     := fun _ _ _ h => h
  , encodes   := fun _ _ _ h => h }

/-- The concrete `releaseEscrowA` dual effect spec (computable surface), for the witness `#guard`s. -/
def releaseEC : EffectSpec2Dual RecChainedState ReleaseArgs :=
  { view         := chainView
  , active1      := balCompC
  , active2      := escrowsCompC
  , logUpdate    := some (fun s args => escrowReceiptA args.actor :: s.log)
  , restFrame    := fun k k' => rhConcrete k = rhConcrete k'
  , guardGates   := releaseGuardGates
  , guardProp    := releaseGuardProp
  , guardWidth   := 1
  , guardEncode  := releaseGuardEncode
  , guardLocal   := releaseGuardLocal
  , guardWidth_le := by decide }

/-! ### The concrete reference: `sR0` (escrow 7: creator 0 → recipient 1, amount 30, unresolved). -/

/-- Concrete pre-state: accounts {0,1}; actor 0 holds `node 1` over recipient 1 (R2 settle-auth);
escrows = [escrow 7 parking 30 of asset 0 for recipient 1]. -/
def sPre : RecChainedState := sR0

/-- The release args: settle escrow 7, actor 0. -/
def argsRef : ReleaseArgs := { id := 7, actor := 0 }

/-- The honest post-state (run the REAL executor: bal 1 0 ← +30, escrow 7 → resolved, log grows). -/
def sPost : RecChainedState := (execFullA sPre (.releaseEscrowA 7 0)).getD sPre

/-- **THE FORGERY:** the SAME guard/log/frame/escrows, but the `bal` credit is MINTED beyond the parked
amount — recipient 1 gains 999 (not the parked 30) at asset 0. A value-forgery the comp1-bind gate
(68/69) must catch. -/
def sForged : RecChainedState :=
  { sPost with kernel := { sPost.kernel with
      bal := fun c a => if c = 1 ∧ a = 0 then 999 else sPost.kernel.bal c a } }

/-! ### The witness vectors. -/

/-- Lay an `encodeE2Dual SC releaseEC s args s'` assignment out as a flat `List Int` of length 74. -/
def witnessOf (s : RecChainedState) (args : ReleaseArgs) (s' : RecChainedState) : List Int :=
  (List.range (releaseEC.traceWidth)).map (fun w => encodeE2Dual SC releaseEC s args s' w)

/-- **`releaseWitnessVec` — the executor-driven witness generator.** Runs `execFullA`; on commit
produces the satisfying dual full-state witness for the executor's post-state. -/
def releaseWitnessVec (s : RecChainedState) (args : ReleaseArgs) : List Int :=
  match execFullA s (.releaseEscrowA args.id args.actor) with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

theorem releaseWitnessVec_commit {s s' : RecChainedState} {args : ReleaseArgs}
    (h : execFullA s (.releaseEscrowA args.id args.actor) = some s') :
    releaseWitnessVec s args = witnessOf s args s' := by
  unfold releaseWitnessVec; rw [h]

def honestWitness : List Int := releaseWitnessVec sPre argsRef
def forgedWitness : List Int := witnessOf sPre argsRef sForged

-- (1) the witnesses have the dual trace width.
#guard honestWitness.length == 74
#guard forgedWitness.length == 74

-- (2) THE EXECUTE→PROVE GUARANTEE: the executor-derived witness SATISFIES the full-state dual circuit.
#guard decide (satisfied (effectCircuit2Dual releaseEC) (encodeE2Dual SC releaseEC sPre argsRef sPost))

-- (3) THE ANTI-GHOST TOOTH (real UNSAT): the forged post-state's witness FAILS on the comp1-bind gate
--     (68 ≠ 69) — the minted bal credit is caught.
#guard decide (satisfied (effectCircuit2Dual releaseEC) (encodeE2Dual SC releaseEC sPre argsRef sForged)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0
#guard forgedWitness.getD 66 0 == forgedWitness.getD 67 0
#guard forgedWitness.getD 70 0 == forgedWitness.getD 71 0   -- forgery preserves escrows comp2
#guard forgedWitness.getD 72 0 == forgedWitness.getD 73 0   -- forgery preserves log
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0
#guard honestWitness.getD 0 0 == 1

/-- HIGH-field MODULAR-COLLISION anti-ghost tooth: recipient 1's credited balance forged by EXACTLY the
old modulus `2000003` (so `bal ≡ honest (mod 2000003)`). The OLD `% 2000003` field hash COLLIDED here
(accepting the tamper); `refP2` is genuinely injective and the `bal` bind gate `68 ≠ 69` REJECTS. -/
def sForgedMod : RecChainedState :=
  { sPost with kernel := { sPost.kernel with
      bal := fun c a => if c = 1 ∧ a = 0 then sPost.kernel.bal 1 0 + 2000003 else sPost.kernel.bal c a } }
#guard decide (satisfied (effectCircuit2Dual releaseEC) (encodeE2Dual SC releaseEC sPre argsRef sForgedMod)) == false

/-! ## §5 — JSON export of the descriptor + witness vectors (the bytes the Rust prover consumes). -/

def releaseAirName : String := "dregg-releaseEscrowA-v2dual"

def emittedRelease : EmittedDescriptor := emittedEffect2Dual releaseAirName releaseEC

def descriptorJson : String := emitDescriptorJson emittedRelease

def witnessJson (xs : List Int) : String := "[" ++ String.intercalate "," (xs.map toString) ++ "]"

def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

#guard emittedRelease.constraints.length == 5
#guard emittedRelease.traceWidth == 74

-- The exact bytes the Rust `lean_executor_derived_release_escrow` test pastes.
#guard descriptorJson ==
  "{\"name\":\"dregg-releaseEscrowA-v2dual\",\"trace_width\":74,\"constraints\":[{\"lhs\":{\"t\":\"var\",\"v\":0},\"rhs\":{\"t\":\"const\",\"v\":1}},{\"lhs\":{\"t\":\"var\",\"v\":66},\"rhs\":{\"t\":\"var\",\"v\":67}},{\"lhs\":{\"t\":\"var\",\"v\":68},\"rhs\":{\"t\":\"var\",\"v\":69}},{\"lhs\":{\"t\":\"var\",\"v\":70},\"rhs\":{\"t\":\"var\",\"v\":71}},{\"lhs\":{\"t\":\"var\",\"v\":72},\"rhs\":{\"t\":\"var\",\"v\":73}}]}"
-- Structural bind-gate goldens (the field-binding `refP2`/`encEscrowRec` digests are arbitrary-precision,
-- replacing the non-injective `% 2000003` field hashes; non-vacuity is at the bind gates; the Rust paste
-- is regenerated from the JSON accessors when the prover field-reduces).
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0   -- bal binds (honest)
#guard honestWitness.getD 70 0 == honestWitness.getD 71 0   -- escrows binds (honest)
#guard honestWitness.getD 72 0 == honestWitness.getD 73 0   -- log binds (honest)
#guard !(honestWitnessJson == forgedWitnessJson)            -- honest ≠ forged byte streams

#assert_axioms releaseWitnessVec_commit
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.ReleaseEscrowWitness
