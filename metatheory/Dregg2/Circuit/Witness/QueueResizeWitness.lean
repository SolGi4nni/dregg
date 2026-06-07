/-
# Dregg2.Circuit.Witness.QueueResizeWitness — the v2 WITNESS GENERATOR for `queueResizeA`.

Closes the verifiable-execution beachhead for `queueResizeA` (the balance-neutral FIFO queue re-cap:
replace the witnessed queue record in place via `replaceQueue`, buffer unchanged), the SAME
`execute → prove → verify → anti-ghost` path the validated references walk — over the GENERIC v2
framework (`EffectCommit2`), since `queueResizeA` touches a single non-`cell` component (`kernel.queues`,
a `listComponent` over `List QueueRecord`). Reused (not re-proved):

  * `Exec.execFullA` — `execFullA s (.queueResizeA id newCap actor cell) = some s'` IS the post-state.
  * `Spec.QueueFifoCore.execFullA_queueResizeA_iff_spec` — executor ⟺ `QueueResizeSpec`.
  * `Inst.QueueResizeA.{queueResizeE, resizePostQueues, apex_implies_queueResizeSpec,
    queueResizeA_full_sound}`.
  * `EffectCommit2.{encodeE2, effect2_circuit_full_complete, emittedEffect2}`.

The spec's `queues` clause is a CONDITIONAL (`∀ q, findQueue … = some q → …`); on a committed step the
guard guarantees the queue EXISTS, so the apex's FULL-list `resizePostQueues` clause follows. The
execute→prove theorem derives the apex from the executor commit through that branch.

No `sorry`/`admit`/`axiom`/`native_decide`. The Poseidon-CR portals are carried HYPOTHESES.
-/
import Dregg2.Circuit.Inst.queueResizeA

namespace Dregg2.Circuit.Witness.QueueResizeWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Inst.QueueResizeA
open Dregg2.Circuit.Spec.QueueFifoCore
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

variable (S : Surface2) (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
  (hN : compressNInjective cN) (hLE : listLeafInjective LE)

/-- **The executor post-`queues` IS `resizePostQueues`** on a committed step (the guard's queue-exists
branch fires). The bridge that lets the apex's FULL-list component clause hold from a committed step. -/
theorem post_queues_eq_resizePostQueues
    {s s' : RecChainedState} {id newCap : Nat} {actor cell : CellId}
    (h : execFullA s (.queueResizeA id newCap actor cell) = some s') :
    s'.kernel.queues = resizePostQueues s { id := id, newCap := newCap, actor := actor, cell := cell } := by
  have hspec := (execFullA_queueResizeA_iff_spec s id newCap actor cell s').mp h
  obtain ⟨⟨_, _, q, hfind, _⟩, hqclause, _⟩ := hspec
  rw [hqclause q hfind, resizePostQueues, hfind]

/-- **`execute_produces_satisfying_witness`.** A committed `execFullA` resize step makes the v2
full-state witness SATISFY the v2 circuit. Builds the apex from the executor commit (guard from the
spec's first conjunct; the FULL-list `queues` clause from `post_queues_eq_resizePostQueues`; log + frame
from the spec). -/
theorem execute_produces_satisfying_witness
    (hRest : RestIffNoQueues S.RH)
    {s s' : RecChainedState} {args : ResizeArgs}
    (h : execFullA s (.queueResizeA args.id args.newCap args.actor args.cell) = some s') :
    satisfiedE2 S (queueResizeE LE cN hN hLE) (encodeE2 S (queueResizeE LE cN hN hLE) s args s') := by
  have hspec := (execFullA_queueResizeA_iff_spec s args.id args.newCap args.actor args.cell s').mp h
  obtain ⟨hguard, _, hlog, hAcc, hCell, hCaps, hEsc, hNul, hRev, hCom, hBal, hSw, hSC, hFac, hLif,
    hDC, hDel, hDgs, hSB⟩ := hspec
  have hq : s'.kernel.queues = resizePostQueues s args := by
    have := post_queues_eq_resizePostQueues (s := s) (s' := s')
      (id := args.id) (newCap := args.newCap) (actor := args.actor) (cell := args.cell) h
    simpa using this
  refine effect2_circuit_full_complete S (queueResizeE LE cN hN hLE)
    (fun k k' hk => (hRest k k').mpr hk) (resizeGuardEncodes LE cN hN hLE) s args s' ?_
  exact ⟨hguard, hq, hlog, hAcc, hCell, hCaps, hEsc, hNul, hRev, hCom, hBal, hSw, hSC, hFac, hLif,
    hDC, hDel, hDgs, hSB⟩

/-- **`satisfying_witness_proves_full_state`.** ANY witness satisfying the v2 circuit proves the complete
declarative `QueueResizeSpec`. Reuses `queueResizeA_full_sound`. -/
theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoQueues S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : ResizeArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (queueResizeE LE cN hN hLE) (encodeE2 S (queueResizeE LE cN hN hLE) s args s')) :
    QueueResizeSpec s args.id args.newCap args.actor args.cell s' :=
  queueResizeA_full_sound S LE cN hN hLE hRest hLog s args s' h

/-! ## §4 — THE EXECUTOR-DERIVED CONCRETE WITNESS (the bytes the Rust prover proves). -/

/-- Concrete computable per-`QueueRecord` leaf code (id/owner/capacity/buffer), kept small. -/
def queueCode (q : QueueRecord) : ℤ :=
  ((q.id : ℤ) * 17 + (q.owner : ℤ) * 7 + (q.capacity : ℤ) * 3
    + q.buffer.foldl (fun acc m => (acc * 31 + (m : ℤ)) % 2000003) ((q.buffer.length : ℤ) + 1)) % 2000003

/-- Concrete computable `queues` list digest: a small modular Horner fold (length-tagged). -/
def queuesDigConcrete : List QueueRecord → ℤ :=
  fun xs => xs.foldl (fun acc q => (acc * 7919 + queueCode q) % 2000003) ((xs.length : ℤ) + 1)

/-- Concrete rest hash: reads only NON-`queues` frame fields. -/
def rhConcrete : RecordKernelState → ℤ :=
  fun k => (k.accounts.card : ℤ) + (k.nullifiers.length : ℤ) * 7
           + (k.commitments.length : ℤ) * 13 + (k.swiss.length : ℤ) * 17

/-- Concrete log hash: a small modular Horner fold over the receipt actors. -/
def lhConcrete : List Turn → ℤ :=
  fun xs => xs.foldl (fun acc t => (acc * 131 + (t.actor : ℤ) + 1) % 2000003) ((xs.length : ℤ) + 1)

def SC : Surface2 := { RH := rhConcrete, LH := lhConcrete }

/-- The concrete `queues` component (computable digest), spec-expected being `resizePostQueues`. -/
def queuesCompC : ActiveComponent RecChainedState ResizeArgs :=
  { digest    := fun k => queuesDigConcrete k.queues
  , expected  := fun s args => queuesDigConcrete (resizePostQueues s args)
  , postClause := fun s args post =>
      queuesDigConcrete post.queues = queuesDigConcrete (resizePostQueues s args)
  , binds     := fun _ _ _ h => h
  , encodes   := fun _ _ _ h => h }

def resizeEC : EffectSpec2 RecChainedState ResizeArgs :=
  { view         := chainView
  , active       := queuesCompC
  , logUpdate    := some (fun s args => resizeReceipt args.actor args.cell :: s.log)
  , restFrame    := fun k k' => rhConcrete k = rhConcrete k'
  , guardGates   := resizeGuardGates
  , guardProp    := resizeGuardProp
  , guardWidth   := 1
  , guardEncode  := resizeGuardEncode
  , guardLocal   := resizeGuardLocal
  , guardWidth_le := by decide }

/-! ### The concrete reference: queue 7 (owner 0, cap 2, buffer [10]) re-capped 2 → 5; actor 0 = cell 0. -/

/-- Concrete pre-state: accounts {0}; actor 0 == cell 0 (self-auth, Live); queues = [queue 7 owner 0
capacity 2 buffer [10]]. -/
def sPre : RecChainedState :=
  { kernel := { accounts := {0}
                cell := fun _ => default
                caps := fun _ => []
                queues := [{ id := 7, owner := 0, capacity := 2, buffer := [10] }] }
    log := [] }

/-- The resize args: re-cap queue 7 to capacity 5; actor 0, representing cell 0. -/
def argsRef : ResizeArgs := { id := 7, newCap := 5, actor := 0, cell := 0 }

/-- The honest post-state (run the REAL executor: queue 7 → capacity 5, buffer unchanged, log grows). -/
def sPost : RecChainedState := (execFullA sPre (.queueResizeA 7 5 0 0)).getD sPre

/-- **THE FORGERY:** the SAME guard/log/frame, but the post `queues` is TAMPERED — queue 7's BUFFER is
mutated (a message dropped) on top of the honest re-cap. A re-cap must NOT touch the buffer; the
component-bind gate (68/69) must catch it. -/
def sForged : RecChainedState :=
  { sPost with kernel := { sPost.kernel with
      queues := [{ id := 7, owner := 0, capacity := 5, buffer := [] }] } }

/-! ### The witness vectors. -/

def witnessOf (s : RecChainedState) (args : ResizeArgs) (s' : RecChainedState) : List Int :=
  (List.range (resizeEC.traceWidth)).map (fun w => encodeE2 SC resizeEC s args s' w)

/-- **`resizeWitnessVec` — the executor-driven witness generator.** Runs `execFullA`; on commit produces
the satisfying full-state witness for the executor's post-state. -/
def resizeWitnessVec (s : RecChainedState) (args : ResizeArgs) : List Int :=
  match execFullA s (.queueResizeA args.id args.newCap args.actor args.cell) with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

theorem resizeWitnessVec_commit {s s' : RecChainedState} {args : ResizeArgs}
    (h : execFullA s (.queueResizeA args.id args.newCap args.actor args.cell) = some s') :
    resizeWitnessVec s args = witnessOf s args s' := by
  unfold resizeWitnessVec; rw [h]

def honestWitness : List Int := resizeWitnessVec sPre argsRef
def forgedWitness : List Int := witnessOf sPre argsRef sForged

#guard honestWitness.length == 72
#guard forgedWitness.length == 72

-- THE EXECUTE→PROVE GUARANTEE: the executor-derived witness SATISFIES the full-state v2 circuit.
#guard decide (satisfied (effectCircuit2 resizeEC) (encodeE2 SC resizeEC sPre argsRef sPost))

-- THE ANTI-GHOST TOOTH (real UNSAT): the forged post-state FAILS on the component-bind gate (68 ≠ 69).
#guard decide (satisfied (effectCircuit2 resizeEC) (encodeE2 SC resizeEC sPre argsRef sForged)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0
#guard forgedWitness.getD 66 0 == forgedWitness.getD 67 0
#guard forgedWitness.getD 70 0 == forgedWitness.getD 71 0
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard honestWitness.getD 0 0 == 1

/-! ## §5 — JSON export of the descriptor + witness vectors. -/

def resizeAirName : String := "dregg-queueResizeA-v2"

def emittedResize : EmittedDescriptor := emittedEffect2 resizeAirName resizeEC

def descriptorJson : String := emitDescriptorJson emittedResize

def witnessJson (xs : List Int) : String := "[" ++ String.intercalate "," (xs.map toString) ++ "]"

def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

#guard emittedResize.constraints.length == 4
#guard emittedResize.traceWidth == 72

-- The exact bytes the Rust `lean_executor_derived_queue_resize` test pastes.
#guard descriptorJson ==
  "{\"name\":\"dregg-queueResizeA-v2\",\"trace_width\":72,\"constraints\":[{\"lhs\":{\"t\":\"var\",\"v\":0},\"rhs\":{\"t\":\"const\",\"v\":1}},{\"lhs\":{\"t\":\"var\",\"v\":66},\"rhs\":{\"t\":\"var\",\"v\":67}},{\"lhs\":{\"t\":\"var\",\"v\":68},\"rhs\":{\"t\":\"var\",\"v\":69}},{\"lhs\":{\"t\":\"var\",\"v\":70},\"rhs\":{\"t\":\"var\",\"v\":71}}]}"
#guard honestWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16037,16308,1,1,16044,16044,263,263]"
#guard forgedWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16037,16237,1,1,15973,16044,263,263]"

#assert_axioms post_queues_eq_resizePostQueues
#assert_axioms resizeWitnessVec_commit
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.QueueResizeWitness
