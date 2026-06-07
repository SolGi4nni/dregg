/-
# Dregg2.Circuit.Witness.QueuePipelineStepWitness — the v2 WITNESS GENERATOR for `queuePipelineStepA`.

Closes the verifiable-execution beachhead for `queuePipelineStepA` (the message-routing fan-out: dequeue
the source queue's head, then fan it out into the sink queues), the SAME
`execute → prove → verify → anti-ghost` path the validated references walk — over the GENERIC v2
framework (`EffectCommit2`), since `queuePipelineStepA` touches a single non-`cell` component
(`kernel.queues`, a `listComponent` over `List QueueRecord`). Reused (not re-proved):

  * `Exec.execFullA` — `execFullA s (.queuePipelineStepA …) = some s'` IS the post-state.
  * `Spec.QueuePipelineFanout.execFullA_iff_spec` — executor ⟺ `QueuePipelineFanoutSpec`.
  * `Inst.QueuePipelineStepA.{queuePipelineStepE, apex_iff_queuePipelineFanoutSpec,
    queuePipelineStepA_full_sound}`.
  * `EffectCommit2.{encodeE2, effect2_circuit_full_complete, emittedEffect2}`.

No `sorry`/`admit`/`axiom`/`native_decide`. The Poseidon-CR portals are carried HYPOTHESES.
-/
import Dregg2.Circuit.Inst.queuePipelineStepA

namespace Dregg2.Circuit.Witness.QueuePipelineStepWitness

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Inst.QueuePipelineStepA
open Dregg2.Circuit.Spec.QueuePipelineFanout
open Dregg2.Exec
open Dregg2.Exec.CircuitEmit
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Cap)

set_option linter.dupNamespace false

/-! ## §0 — decidability re-exports (so the executor-derived `#guard`s can `decide`). -/

instance (c : Constraint) (a : Assignment) : Decidable (c.holds a) := by
  unfold Constraint.holds; exact inferInstanceAs (Decidable (_ = _))

instance (cs : ConstraintSystem) (a : Assignment) : Decidable (satisfied cs a) := by
  unfold satisfied; exact List.decidableBAll _ _

/-! ## §3 — THE ABSTRACT EXECUTE→PROVE / PROVE→STATE theorems (CR portals carried). -/

variable (S : Surface2) (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
  (hN : compressNInjective cN) (hLE : listLeafInjective LE)

/-- **`execute_produces_satisfying_witness`.** A committed `execFullA` pipeline step makes the v2
full-state witness SATISFY the v2 circuit. Reuses `effect2_circuit_full_complete` via
`apex_iff_queuePipelineFanoutSpec` ∘ `execFullA_iff_spec`. -/
theorem execute_produces_satisfying_witness
    (hRest : RestIffNoQueues S.RH)
    {s s' : RecChainedState} {args : PipelineArgs}
    (h : execFullA s (.queuePipelineStepA args.srcId args.owner args.sinkCells args.sinkIds) = some s') :
    satisfiedE2 S (queuePipelineStepE LE cN hN hLE)
      (encodeE2 S (queuePipelineStepE LE cN hN hLE) s args s') := by
  have hspec := (execFullA_iff_spec s args.srcId args.owner args.sinkCells args.sinkIds s').mp h
  have hapex : (queuePipelineStepE LE cN hN hLE).apex s args s' :=
    (apex_iff_queuePipelineFanoutSpec LE cN hN hLE s args s').mpr hspec
  exact effect2_circuit_full_complete S (queuePipelineStepE LE cN hN hLE)
    (fun k k' hk => (hRest k k').mpr hk) (pipelineGuardEncodes LE cN hN hLE) s args s' hapex

/-- **`satisfying_witness_proves_full_state`.** ANY witness satisfying the v2 circuit proves the complete
declarative `QueuePipelineFanoutSpec`. Reuses `queuePipelineStepA_full_sound`. -/
theorem satisfying_witness_proves_full_state
    (hRest : RestIffNoQueues S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : PipelineArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (queuePipelineStepE LE cN hN hLE)
        (encodeE2 S (queuePipelineStepE LE cN hN hLE) s args s')) :
    QueuePipelineFanoutSpec s args.srcId args.owner args.sinkCells args.sinkIds s' :=
  queuePipelineStepA_full_sound S LE cN hN hLE hRest hLog s args s' h

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

/-- The concrete `queues` component (computable digest), spec-expected being `pipelinePostQueues`. -/
def queuesCompC : ActiveComponent RecChainedState PipelineArgs :=
  { digest    := fun k => queuesDigConcrete k.queues
  , expected  := fun s args => queuesDigConcrete (pipelinePostQueues s args)
  , postClause := fun s args post =>
      queuesDigConcrete post.queues = queuesDigConcrete (pipelinePostQueues s args)
  , binds     := fun _ _ _ h => h
  , encodes   := fun _ _ _ h => h }

def pipelineEC : EffectSpec2 RecChainedState PipelineArgs :=
  { view         := chainView
  , active       := queuesCompC
  , logUpdate    := some (fun s args => routingRow args.owner :: s.log)
  , restFrame    := fun k k' => rhConcrete k = rhConcrete k'
  , guardGates   := pipelineGuardGates
  , guardProp    := pipelineGuardProp
  , guardWidth   := 1
  , guardEncode  := pipelineGuardEncode
  , guardLocal   := pipelineGuardLocal
  , guardWidth_le := by decide }

/-! ### The concrete reference: route message 111 from source queue 10 into sink queues 11/12. -/

/-- Concrete pre-state: owner 0 holds `node 0/1/2` caps over sinks 1/2; source queue 10 has head 111;
sink queues 11/12 empty. Accounts {0,1,2}. -/
def sPre : RecChainedState :=
  { kernel := { accounts := {0, 1, 2}
                cell := fun _ => .record [("balance", .int 0)]
                caps := fun l => if l = 0 then [Cap.node 0, Cap.node 1, Cap.node 2] else []
                queues :=
                  [ { id := 10, owner := 0, capacity := 3, buffer := [111] }
                  , { id := 11, owner := 0, capacity := 3, buffer := [] }
                  , { id := 12, owner := 0, capacity := 3, buffer := [] } ] }
    log := [] }

/-- The pipeline args: dequeue source 10, owner 0, fan out into sink cells 1/2 (queue ids 11/12). -/
def argsRef : PipelineArgs := { srcId := 10, owner := 0, sinkCells := [1, 2], sinkIds := [11, 12] }

/-- The honest post-state (run the REAL executor: 111 dequeued from q10, fanned into q11/q12). -/
def sPost : RecChainedState :=
  (execFullA sPre (.queuePipelineStepA 10 0 [1, 2] [11, 12])).getD sPre

/-- **THE FORGERY:** the SAME guard/log/frame, but the post `queues` is TAMPERED — the routed message
is DROPPED (sink queue 11 stays empty rather than receiving 111). A routing-loss the component-bind
gate (68/69) must catch. -/
def sForged : RecChainedState :=
  { sPost with kernel := { sPost.kernel with
      queues :=
        [ { id := 10, owner := 0, capacity := 3, buffer := [] }
        , { id := 11, owner := 0, capacity := 3, buffer := [] }   -- DROPPED: should hold 111
        , { id := 12, owner := 0, capacity := 3, buffer := [111] } ] } }

/-! ### The witness vectors. -/

def witnessOf (s : RecChainedState) (args : PipelineArgs) (s' : RecChainedState) : List Int :=
  (List.range (pipelineEC.traceWidth)).map (fun w => encodeE2 SC pipelineEC s args s' w)

/-- **`pipelineWitnessVec` — the executor-driven witness generator.** Runs `execFullA`; on commit
produces the satisfying full-state witness for the executor's post-state. -/
def pipelineWitnessVec (s : RecChainedState) (args : PipelineArgs) : List Int :=
  match execFullA s (.queuePipelineStepA args.srcId args.owner args.sinkCells args.sinkIds) with
  | some s' => witnessOf s args s'
  | none    => witnessOf s args s

theorem pipelineWitnessVec_commit {s s' : RecChainedState} {args : PipelineArgs}
    (h : execFullA s (.queuePipelineStepA args.srcId args.owner args.sinkCells args.sinkIds) = some s') :
    pipelineWitnessVec s args = witnessOf s args s' := by
  unfold pipelineWitnessVec; rw [h]

def honestWitness : List Int := pipelineWitnessVec sPre argsRef
def forgedWitness : List Int := witnessOf sPre argsRef sForged

#guard honestWitness.length == 72
#guard forgedWitness.length == 72

-- THE EXECUTE→PROVE GUARANTEE: the executor-derived witness SATISFIES the full-state v2 circuit.
#guard decide (satisfied (effectCircuit2 pipelineEC) (encodeE2 SC pipelineEC sPre argsRef sPost))

-- THE ANTI-GHOST TOOTH (real UNSAT): the forged post-state FAILS on the component-bind gate (68 ≠ 69).
#guard decide (satisfied (effectCircuit2 pipelineEC) (encodeE2 SC pipelineEC sPre argsRef sForged)) == false
#guard !(forgedWitness.getD 68 0 == forgedWitness.getD 69 0)
#guard honestWitness.getD 66 0 == honestWitness.getD 67 0
#guard forgedWitness.getD 66 0 == forgedWitness.getD 67 0
#guard forgedWitness.getD 70 0 == forgedWitness.getD 71 0
#guard honestWitness.getD 68 0 == honestWitness.getD 69 0
#guard honestWitness.getD 0 0 == 1

/-! ## §5 — JSON export of the descriptor + witness vectors. -/

def pipelineAirName : String := "dregg-queuePipelineStepA-v2"

def emittedPipeline : EmittedDescriptor := emittedEffect2 pipelineAirName pipelineEC

def descriptorJson : String := emitDescriptorJson emittedPipeline

def witnessJson (xs : List Int) : String := "[" ++ String.intercalate "," (xs.map toString) ++ "]"

def honestWitnessJson : String := witnessJson honestWitness
def forgedWitnessJson : String := witnessJson forgedWitness

#guard emittedPipeline.constraints.length == 4
#guard emittedPipeline.traceWidth == 72

-- The exact bytes the Rust `lean_executor_derived_queue_pipeline_step` test pastes.
#guard descriptorJson ==
  "{\"name\":\"dregg-queuePipelineStepA-v2\",\"trace_width\":72,\"constraints\":[{\"lhs\":{\"t\":\"var\",\"v\":0},\"rhs\":{\"t\":\"const\",\"v\":1}},{\"lhs\":{\"t\":\"var\",\"v\":66},\"rhs\":{\"t\":\"var\",\"v\":67}},{\"lhs\":{\"t\":\"var\",\"v\":68},\"rhs\":{\"t\":\"var\",\"v\":69}},{\"lhs\":{\"t\":\"var\",\"v\":70},\"rhs\":{\"t\":\"var\",\"v\":71}}]}"
#guard honestWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,395231,1557420,3,3,1557154,1557154,263,263]"
#guard forgedWitnessJson ==
  "[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,395231,195352,3,3,195086,1557154,263,263]"

#assert_axioms pipelineWitnessVec_commit
#assert_axioms execute_produces_satisfying_witness
#assert_axioms satisfying_witness_proves_full_state

end Dregg2.Circuit.Witness.QueuePipelineStepWitness
