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

No `sorry`/`admit`/`axiom`/`native_decide`. The Poseidon-CR portals are carried HYPOTHESES on the
abstract keystones.
-/
import Dregg2.Circuit.Inst.releaseEscrowA

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

/-- Concrete computable `bal` digest: sample over the toy cell×asset window `[0,4)×[0,2)`, small
modular Horner fold. A tamper of ANY window entry's balance changes this number. -/
def balDigConcrete : (CellId → AssetId → ℤ) → ℤ :=
  fun bal => (List.range 4).foldl (fun acc c =>
    (List.range 2).foldl (fun acc2 a => (acc2 * 131 + bal c a + 1000) % 2000003) acc) 1

/-- Concrete computable per-`EscrowRecord` leaf code (id/recipient/amount/resolved), kept small. -/
def escrowCode (r : EscrowRecord) : ℤ :=
  ((r.id : ℤ) * 17 + (r.recipient : ℤ) * 7 + r.amount + (if r.resolved then 1 else 0)) % 2000003

/-- Concrete computable `escrows` list digest: a small modular Horner fold (length-tagged). -/
def escrowsDigConcrete : List EscrowRecord → ℤ :=
  fun xs => xs.foldl (fun acc r => (acc * 7919 + escrowCode r) % 2000003) ((xs.length : ℤ) + 1)

/-- Concrete rest hash: reads only NON-`bal`/`escrows` frame fields (so a pure bal/escrows forgery
leaves it fixed — a component-bind gate bites, not the rest gate). -/
def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ) * 7
           + (k.commitments.length : ℤ) * 13 + (k.swiss.length : ℤ) * 17

/-- Concrete log hash: a small modular Horner fold over the receipt actors. -/
def lhConcrete : List Turn → ℤ :=
  fun xs => xs.foldl (fun acc t => (acc * 131 + (t.actor : ℤ) + 1) % 2000003) ((xs.length : ℤ) + 1)

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
#guard honestWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,344325,1298045,2,2,1281785,1281785,15995,15995,263,263]"
#guard forgedWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,344325,694659,2,2,678399,1281785,15995,15995,263,263]"

#assert_axioms releaseWitnessVec_commit
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.ReleaseEscrowWitness
