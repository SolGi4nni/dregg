/-
# Dregg2.Circuit.Inst.queuePipelineStepA — the v2 (`EffectCommit2`) instance for the FIFO pipeline
FAN-OUT step `queuePipelineStepA`.

`queuePipelineStepA` DEQUEUEs the FIFO head of a source queue and RE-ENQUEUEs it into each sink. It
touches ONLY the `queues` side-table (FULL-list digest), prepends the routing receipt to the log, and
FREEZES the other 16 kernel fields. Guard: the spec's `admitGuard` (source dequeue ∧ sink fan-out both
succeed). The INDEPENDENT bespoke apex is `QueuePipelineFanoutSpec` in
`Dregg2/Circuit/Spec/queuepipelinefanout.lean`.

THE VALIDATION: `queuePipelineStepA_full_sound ⇒ QueuePipelineFanoutSpec` THROUGH the framework.

ADDITIVE: imports `EffectCommit2` + the queue-pipeline-fanout spec; edits neither. Follows the
`queueAllocateA` template + the `queueResizeA` canonical-post-list pattern.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Circuit.EffectCommit2
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.queuepipelinedsend
import Dregg2.Circuit.Spec.queuepipelinefanout

namespace Dregg2.Circuit.Inst.QueuePipelineStepA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.ListCommit
open Dregg2.Circuit.Spec.QueuePipelinedSend (recKernel_ext)
open Dregg2.Circuit.Spec.QueuePipelineFanout
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (`propBit` at wire `0`). -/

abbrev vBitGuard : Var := 0
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `RestIffNoQueues` portal (the v1 `RestHashIffFrame` minus `queues`). -/

/-- **`RestIffNoQueues RH`** — the rest hash binds the 16 non-`queues` components (BIDIRECTIONAL),
omitting `queues` (the touched field of `queuePipelineStepA`). -/
def RestIffNoQueues (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.escrows = k.escrows ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes)

/-! ## §2 — the `queuePipelineStepE` instance (touched component = `queues`). -/

/-- The pipeline-step effect arguments: source queue id, owner, paired sink cells/ids. -/
structure PipelineArgs where
  srcId     : Nat
  owner     : CellId
  sinkCells : List CellId
  sinkIds   : List Nat

def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

def pipelineGuardProp (s : RecChainedState) (args : PipelineArgs) : Prop :=
  admitGuard s args.srcId args.owner args.sinkCells args.sinkIds

/-- Executable shadow of `admitGuard` (for `Decidable` instance). -/
def pipelineAdmits (s : RecChainedState) (args : PipelineArgs) : Bool :=
  match queueDequeueK s.kernel args.srcId args.owner with
  | none => false
  | some (k1, m) =>
      (pipelineFanoutK k1 args.owner m args.sinkCells args.sinkIds).isSome

theorem pipelineAdmits_iff (s : RecChainedState) (args : PipelineArgs) :
    pipelineAdmits s args = true ↔ pipelineGuardProp s args := by
  unfold pipelineAdmits pipelineGuardProp admitGuard
  cases h : queueDequeueK s.kernel args.srcId args.owner with
  | none => simp [h]
  | some pr =>
      obtain ⟨k1, m⟩ := pr
      simp only [h]
      cases hf : pipelineFanoutK k1 args.owner m args.sinkCells args.sinkIds with
      | none => simp [hf]
      | some _ => simp [hf]

instance (s : RecChainedState) (args : PipelineArgs) : Decidable (pipelineGuardProp s args) := by
  rw [← pipelineAdmits_iff]
  exact inferInstanceAs (Decidable (pipelineAdmits s args = true))

def pipelineGuardEncode (s : RecChainedState) (args : PipelineArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (pipelineGuardProp s args) else 0

def pipelineGuardGates : ConstraintSystem := [cBitGuard]

theorem pipelineGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied pipelineGuardGates a ↔ satisfied pipelineGuardGates b := by
  unfold satisfied pipelineGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- The canonical post-`queues` list a committed pipeline step produces (pure in pre+args). On the
(guard-guaranteed) live branch, this is the fan-out fold's post-`queues`; otherwise the pre-list. -/
def pipelinePostQueues (s : RecChainedState) (args : PipelineArgs) : List QueueRecord :=
  match queueDequeueK s.kernel args.srcId args.owner with
  | some (k1, m) =>
      match pipelineFanoutK k1 args.owner m args.sinkCells args.sinkIds with
      | some k2 => k2.queues
      | none    => s.kernel.queues
  | none => s.kernel.queues

/-- On the live branch, `pipelinePostQueues` reads the fan-out kernel's `queues`. -/
theorem pipelinePostQueues_eq {s : RecChainedState} {args : PipelineArgs}
    {k1 : RecordKernelState} {m : Nat} {k2 : RecordKernelState}
    (hd : queueDequeueK s.kernel args.srcId args.owner = some (k1, m))
    (hf : pipelineFanoutK k1 args.owner m args.sinkCells args.sinkIds = some k2) :
    pipelinePostQueues s args = k2.queues := by
  simp only [pipelinePostQueues, hd, hf]

/-- If the fan-out fold and post-state agree on `queues` and the 16 non-`queues` frame fields match the
pre-kernel, the post-kernel IS the fan-out result. -/
theorem kernel_eq_of_queues_frame {kPre kFan kPost : RecordKernelState}
    (hq : kPost.queues = kFan.queues)
    (hAcc : kPost.accounts = kPre.accounts) (hCell : kPost.cell = kPre.cell)
    (hCaps : kPost.caps = kPre.caps) (hEsc : kPost.escrows = kPre.escrows)
    (hNul : kPost.nullifiers = kPre.nullifiers) (hRev : kPost.revoked = kPre.revoked)
    (hCom : kPost.commitments = kPre.commitments) (hBal : kPost.bal = kPre.bal)
    (hSw : kPost.swiss = kPre.swiss) (hSC : kPost.slotCaveats = kPre.slotCaveats)
    (hFac : kPost.factories = kPre.factories) (hLif : kPost.lifecycle = kPre.lifecycle)
    (hDC : kPost.deathCert = kPre.deathCert) (hDel : kPost.delegate = kPre.delegate)
    (hDgs : kPost.delegations = kPre.delegations) (hSB : kPost.sealedBoxes = kPre.sealedBoxes)
    (hf1 : kFan.accounts = kPre.accounts) (hf2 : kFan.cell = kPre.cell)
    (hf3 : kFan.caps = kPre.caps) (hf4 : kFan.escrows = kPre.escrows)
    (hf5 : kFan.nullifiers = kPre.nullifiers) (hf6 : kFan.revoked = kPre.revoked)
    (hf7 : kFan.commitments = kPre.commitments) (hf8 : kFan.bal = kPre.bal)
    (hf9 : kFan.swiss = kPre.swiss) (hf10 : kFan.slotCaveats = kPre.slotCaveats)
    (hf11 : kFan.factories = kPre.factories) (hf12 : kFan.lifecycle = kPre.lifecycle)
    (hf13 : kFan.deathCert = kPre.deathCert) (hf14 : kFan.delegate = kPre.delegate)
    (hf15 : kFan.delegations = kPre.delegations) (hf16 : kFan.sealedBoxes = kPre.sealedBoxes) :
    kPost = kFan :=
  recKernel_ext
    (hAcc.trans hf1.symm) (hCell.trans hf2.symm) (hCaps.trans hf3.symm) (hEsc.trans hf4.symm)
    (hNul.trans hf5.symm) (hRev.trans hf6.symm) (hCom.trans hf7.symm) (hBal.trans hf8.symm) hq
    (hSw.trans hf9.symm) (hSC.trans hf10.symm) (hFac.trans hf11.symm) (hLif.trans hf12.symm)
    (hDC.trans hf13.symm) (hDel.trans hf14.symm) (hDgs.trans hf15.symm) (hSB.trans hf16.symm)

def queuesComponent (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    ActiveComponent RecChainedState PipelineArgs :=
  listComponent (·.queues) LE cN hN hLE pipelinePostQueues

def queuePipelineStepE (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    EffectSpec2 RecChainedState PipelineArgs where
  view         := chainView
  active       := queuesComponent LE cN hN hLE
  logUpdate    := some (fun s args => routingRow args.owner :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.escrows = k.escrows ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal ∧ k'.swiss = k.swiss
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes)
  guardGates   := pipelineGuardGates
  guardProp    := pipelineGuardProp
  guardWidth   := 1
  guardEncode  := pipelineGuardEncode
  guardLocal   := pipelineGuardLocal
  guardWidth_le := by decide

/-! ### §2a — the per-effect obligations for `queuePipelineStepE`. -/

theorem pipelineGuardDecodes (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardDecodes2 (queuePipelineStepE LE cN hN hLE) := by
  intro s args s' hsat
  change satisfied pipelineGuardGates (pipelineGuardEncode s args s') at hsat
  show pipelineGuardProp s args
  have hg := hsat cBitGuard (by simp [pipelineGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, pipelineGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

theorem pipelineGuardEncodes (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) :
    GuardEncodes2 (queuePipelineStepE LE cN hN hLE) := by
  intro s args s' hg
  show satisfied pipelineGuardGates (pipelineGuardEncode s args s')
  intro c hc
  simp only [pipelineGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, pipelineGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

theorem pipelineRestFrameDecodes (S : Surface2) (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE) (hRest : RestIffNoQueues S.RH) :
    RestFrameDecodes2 S (queuePipelineStepE LE cN hN hLE) := fun k k' h => (hRest k k').mp h

/-! ### §2b — the apex ↔ `QueuePipelineFanoutSpec` bridge. -/

theorem apex_iff_queuePipelineFanoutSpec (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (s : RecChainedState) (args : PipelineArgs) (s' : RecChainedState) :
    (queuePipelineStepE LE cN hN hLE).apex s args s'
      ↔ QueuePipelineFanoutSpec s args.srcId args.owner args.sinkCells args.sinkIds s' := by
  show (pipelineGuardProp s args
        ∧ s'.kernel.queues = pipelinePostQueues s args
        ∧ s'.log = routingRow args.owner :: s.log
        ∧ ((queuePipelineStepE LE cN hN hLE).restFrame s.kernel s'.kernel))
       ↔ QueuePipelineFanoutSpec s args.srcId args.owner args.sinkCells args.sinkIds s'
  unfold QueuePipelineFanoutSpec pipelineGuardProp admitGuard queuePipelineStepE
  constructor
  · rintro ⟨hg, hq, hlog, hAcc, hCell, hCaps, hEsc, hNul, hRev, hCom, hBal, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    obtain ⟨k1, m, hd, hsome⟩ := hg
    match hf : pipelineFanoutK k1 args.owner m args.sinkCells args.sinkIds with
    | none =>
        rw [hf] at hsome
        exact absurd hsome (by simp)
    | some k2 =>
      have hfan : pipelineFanoutK k1 args.owner m args.sinkCells args.sinkIds = some s'.kernel := by
        have hq' : s'.kernel.queues = k2.queues := by rw [hq, pipelinePostQueues_eq hd hf]
        obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16⟩ :=
          queueDequeueK_frame hd
        obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
          pipelineFanoutK_frame hf
        have hk : s'.kernel = k2 :=
          kernel_eq_of_queues_frame hq'
            hAcc hCell hCaps hEsc hNul hRev hCom hBal hSw hSC hFac hLif hDC hDel hDgs hSB
            (f1.trans d1) (f2.trans d2) (f3.trans d3) (f4.trans d4) (f5.trans d5) (f6.trans d6)
            (f7.trans d7) (f8.trans d8) (f9.trans d9) (f10.trans d10) (f11.trans d11) (f12.trans d12)
            (f13.trans d13) (f14.trans d14) (f15.trans d15) (f16.trans d16)
        rw [hk, hf]
      exact ⟨⟨k1, m, hd, hfan⟩, hlog, hAcc, hCell, hCaps, hEsc, hNul, hRev, hCom, hBal, hSw, hSC,
        hFac, hLif, hDC, hDel, hDgs, hSB⟩
  · rintro ⟨⟨k1, m, hd, hf⟩, hlog, hAcc, hCell, hCaps, hEsc, hNul, hRev, hCom, hBal, hSw, hSC, hFac,
      hLif, hDC, hDel, hDgs, hSB⟩
    refine ⟨⟨k1, m, hd, ?_⟩, ?_, hlog, hAcc, hCell, hCaps, hEsc, hNul, hRev, hCom, hBal, hSw, hSC,
      hFac, hLif, hDC, hDel, hDgs, hSB⟩
    · simp [hf]
    · exact (pipelinePostQueues_eq hd hf).symm

/-! ### §2c — THE VALIDATION: `queuePipelineStepA_full_sound ⇒ QueuePipelineFanoutSpec`. -/

/-- **`queuePipelineStepA_full_sound` — the VALIDATION (pipeline fan-out through the v2 framework).** A
satisfying v2 full-state witness for `queuePipelineStepE` proves the complete declarative bespoke
`QueuePipelineFanoutSpec`. Portals: `RestIffNoQueues RH`, `logHashInjective LH`,
`compressNInjective cN` + `listLeafInjective LE` (the `queues` list-component carriers). -/
theorem queuePipelineStepA_full_sound
    (S : Surface2) (LE : QueueRecord → ℤ) (cN : List ℤ → ℤ)
    (hN : compressNInjective cN) (hLE : listLeafInjective LE)
    (hRest : RestIffNoQueues S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : PipelineArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (queuePipelineStepE LE cN hN hLE)
          (encodeE2 S (queuePipelineStepE LE cN hN hLE) s args s')) :
    QueuePipelineFanoutSpec s args.srcId args.owner args.sinkCells args.sinkIds s' := by
  have hapex : (queuePipelineStepE LE cN hN hLE).apex s args s' :=
    effect2_circuit_full_sound S (queuePipelineStepE LE cN hN hLE)
      (pipelineRestFrameDecodes S LE cN hN hLE hRest) hLog (pipelineGuardDecodes LE cN hN hLE)
      s args s' h
  exact (apex_iff_queuePipelineFanoutSpec LE cN hN hLE s args s').mp hapex


/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def queuePipelineStepEWire : EffectSpec2 RecChainedState PipelineArgs where
  view         := chainView
  active      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := pipelineGuardGates
  guardProp    := pipelineGuardProp
  guardWidth   := 1
  guardEncode  := pipelineGuardEncode
  guardLocal   := pipelineGuardLocal
  guardWidth_le := by decide

def queuePipelineStepAAirName : String := "dregg-queuePipelineStepA-v2"

def queuePipelineStepAEmitted : EmittedDescriptor := emittedEffect2 queuePipelineStepAAirName queuePipelineStepEWire

#guard queuePipelineStepAEmitted.name == queuePipelineStepAAirName

/-! ## §3 — axiom-hygiene tripwires. -/

#assert_axioms pipelineGuardLocal
#assert_axioms pipelinePostQueues_eq
#assert_axioms kernel_eq_of_queues_frame
#assert_axioms pipelineGuardDecodes
#assert_axioms pipelineGuardEncodes
#assert_axioms apex_iff_queuePipelineFanoutSpec
#assert_axioms queuePipelineStepA_full_sound

end Dregg2.Circuit.Inst.QueuePipelineStepA