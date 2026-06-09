/-
# Dregg2.Circuit.Emit.EffectVmEmitQueuePipelineStep — the `queuePipelineStepA` (pipeline DEQUEUE-and-route)
effect's EffectVM emission, through the SAME `EffectVmEmit` IR as transfer.

Universe A (`Inst/queuePipelineStepA.lean`, `Spec/queuepipelinefanout.lean`) carries the FULL-state
soundness `queuePipelineStepA_full_sound ⇒ QueuePipelineFanoutSpec`: a committed step DEQUEUES the FIFO
front of the source queue and routes the message to the sink queues, advancing the `queues` side-table
and the log, FREEZING the ledger (`s'.kernel.bal = s.kernel.bal` — balance-NEUTRAL) and the other fields.

## STAGE-3 AMPLIFICATION: the queue side-table root is NOW BOUND.

STAGE 3 (`Exec.SystemRoots`, `state.systemRoot.QUEUE`) gives the queue side-table a committed root carried
at `state.FIELD_BASE + 4` (`fields[4]`). The runtime advances the SOURCE queue root on a pipeline step:
`fields[4]_before = source_old_root` (`param1`), `fields[4]_after = source_new_root` (`param2`), where
`source_new = hash_2_to_1(source_old, message_hash)` (the dequeue advance, `effect_vm/air.rs`
`PipelineStep` arm). This descriptor now BINDS that source-root transition (before-pin + after-write);
GROUP-4 site1 folds `fields[4]` into `state_commit`. So the routed-message dequeue is bound — no longer
out-of-IR.

## RECONCILIATION onto the runtime trace-generator layout (the cutover-harness pattern, 3aaf0772d).

  * FREEZES `bal_lo`/`bal_hi` (pipeline routing moves no value — AGREES with universe A directly).
  * PINS `fields[4]_before = source_old_root` and WRITES `fields[4]_after = source_new_root`; FREEZES
    `fields[0..3]`, `fields[5..7]`, cap_root, reserved.
  * TICKS the nonce; the earlier descriptor FROZE it (UNSAT) — now fixed via the shared `gNonce`.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` hypothesis. No `sorry`, no `:= True`, no `native_decide`. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.queuepipelinefanout

namespace Dregg2.Circuit.Emit.EffectVmEmitQueuePipelineStep

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA ePrm eSub eSelNoop gNonce gBalHi gCapPass gResPass gFieldPass
   transitionAll boundaryFirstPins boundaryLastPins
   transferHashSites transferHash_binds boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState absorbedCols absorbed_determined_by_commit)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option linter.unusedVariables false

/-! ## §0 — The queuePipelineStep selector + the runtime pipeline params + the queue-root carrier. -/

/-- The queuePipelineStep selector column index (`columns.rs::sel::PIPELINE_STEP`). -/
def SEL_QUEUE_PIPELINE : Nat := 23

/-! Runtime pipeline parameter columns. -/
namespace param
/-- The source OLD queue root (`param::PIPELINE_SOURCE_OLD_ROOT`). -/
def PIPELINE_SOURCE_OLD_ROOT : Nat := 1
/-- The source NEW queue root (`param::PIPELINE_SOURCE_NEW_ROOT`). -/
def PIPELINE_SOURCE_NEW_ROOT : Nat := 2
end param

/-- The source old root as an expression (`param1`). -/
def ePrmOldRoot : EmittedExpr := .var (prmCol param.PIPELINE_SOURCE_OLD_ROOT)
/-- The source new root as an expression (`param2`). -/
def ePrmNewRoot : EmittedExpr := .var (prmCol param.PIPELINE_SOURCE_NEW_ROOT)

/-- The queue-root state column (`fields[4]`, the runtime's queue-side-table-root carrier). -/
def QUEUE_ROOT_FIELD : Nat := state.FIELD_BASE + 4

/-- The pipeline-step row: `s_queue_pipeline = 1`, `s_noop = 0`. -/
def IsQueuePipelineRow (env : VmRowEnv) : Prop :=
  env.loc SEL_QUEUE_PIPELINE = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — The per-row gate bodies (balance FREEZE + queue-root before-pin + after-write + nonce TICK). -/

/-- Balance-lo FREEZE body: `new_bal_lo − old_bal_lo` (pipeline routing moves no value). -/
def gBalLoFreeze : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)

/-- Queue-root BEFORE-pin body: `fields[4]_before − source_old_root`. -/
def gQueueRootBefore : EmittedExpr := eSub (eSB QUEUE_ROOT_FIELD) ePrmOldRoot

/-- Queue-root AFTER-write body: `fields[4]_after − source_new_root` (the routed-message dequeue). -/
def gQueueRootAfter : EmittedExpr := eSub (eSA QUEUE_ROOT_FIELD) ePrmNewRoot

/-- Nonce TICK body, reused verbatim from transfer. -/
def gNonceTick : EmittedExpr := gNonce

/-- The seven NON-queue-root field passthrough gates (`fields[0..3]`, `fields[5..7]`). -/
def gFieldPassNonRoot : List VmConstraint :=
  ([0, 1, 2, 3, 5, 6, 7] : List Nat).map (fun i => VmConstraint.gate (gFieldPass i))

/-! ## §2 — The emitted queuePipelineStep descriptor. -/

/-- The queuePipelineStep AIR identity. -/
def queuePipelineVmAirName : String := "dregg-effectvm-queuepipelinestep-v1"

/-- The pipeline-step per-row gates: balance freeze, bal_hi freeze, nonce TICK, cap/reserved freeze,
queue-root before-pin + after-write, 7 non-root field freezes. -/
def queuePipelineRowGates : List VmConstraint :=
  [ .gate gBalLoFreeze, .gate gBalHi, .gate gNonceTick
  , .gate gCapPass, .gate gResPass, .gate gQueueRootBefore, .gate gQueueRootAfter ] ++ gFieldPassNonRoot

/-- **`queuePipelineVmDescriptor`** — the FULL pipeline-step descriptor reconciled onto the runtime
layout: balance-freeze + queue-root before-pin/after-write + nonce-tick + freeze gates ++ transition ++
boundary pins, with the 4 GROUP-4 hash sites (site1 absorbs `fields[4]`) and the 2 range checks. -/
def queuePipelineVmDescriptor : EffectVmDescriptor :=
  { name := queuePipelineVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := queuePipelineRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The queuePipelineStep ROW INTENT (runtime-reconciled). -/

/-- **`QueuePipelineRowIntent env`** — the runtime pipeline-step move: the ledger is FROZEN, the queue-root
carrier (`fields[4]`) goes from `source_old_root` to `source_new_root`, the nonce TICKS, the rest FROZEN. -/
def QueuePipelineRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ env.loc (sbCol QUEUE_ROOT_FIELD) = env.loc (prmCol param.PIPELINE_SOURCE_OLD_ROOT)
  ∧ env.loc (saCol QUEUE_ROOT_FIELD) = env.loc (prmCol param.PIPELINE_SOURCE_NEW_ROOT)
  ∧ (∀ i ∈ ([0, 1, 2, 3, 5, 6, 7] : List Nat),
        env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS. -/

theorem queuePipelineVm_faithful (env : VmRowEnv) :
    (∀ c ∈ queuePipelineRowGates, c.holdsVm env false false) ↔ QueuePipelineRowIntent env := by
  unfold queuePipelineRowGates gFieldPassNonRoot QueuePipelineRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoFreeze) (by simp)
    have hHi := h (.gate gBalHi) (by simp)
    have hNon := h (.gate gNonceTick) (by simp)
    have hCap := h (.gate gCapPass) (by simp)
    have hRes := h (.gate gResPass) (by simp)
    have hBef := h (.gate gQueueRootBefore) (by simp)
    have hAft := h (.gate gQueueRootAfter) (by simp)
    have hFld : ∀ i ∈ ([0, 1, 2, 3, 5, 6, 7] : List Nat),
        VmConstraint.holdsVm env false false (.gate (gFieldPass i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoFreeze, gBalHi, gNonceTick, gNonce, gCapPass, gResPass,
      gQueueRootBefore, gQueueRootAfter, eSA, eSB, ePrmOldRoot, ePrmNewRoot, eSelNoop,
      eSub, EmittedExpr.eval] at hLo hHi hNon hCap hRes hBef hAft
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · linarith [hLo]
    · linarith [hHi]
    · linarith [hNon]
    · linarith [hCap]
    · linarith [hRes]
    · linarith [hBef]
    · linarith [hAft]
    · intro i hi
      have := hFld i hi
      simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval] at this
      linarith
  · rintro ⟨hLo, hHi, hNon, hCap, hRes, hBef, hAft, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hLo]; ring
    · simp only [VmConstraint.holdsVm, gBalHi, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hHi]; ring
    · simp only [VmConstraint.holdsVm, gNonceTick, gNonce, eSA, eSB, eSelNoop, eSub, EmittedExpr.eval]
      rw [hNon]; ring
    · simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hCap]; ring
    · simp only [VmConstraint.holdsVm, gResPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gQueueRootBefore, eSB, ePrmOldRoot, eSub, EmittedExpr.eval]
      rw [hBef]; ring
    · simp only [VmConstraint.holdsVm, gQueueRootAfter, eSA, ePrmNewRoot, eSub, EmittedExpr.eval]
      rw [hAft]; ring
    · simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval]
      have hmem : i ∈ ([0, 1, 2, 3, 5, 6, 7] : List Nat) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto
      rw [hFld i hmem]; ring

/-! ## §5 — ANTI-GHOST. -/

theorem queuePipelineVm_rejects_wrong_output (env : VmRowEnv)
    (hwrong : ¬ QueuePipelineRowIntent env) :
    ¬ (∀ c ∈ queuePipelineRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((queuePipelineVm_faithful env).mp h)

/-- **Anti-ghost (queue-root after-tamper).** A row whose post-`fields[4]` is NOT the declared
`source_new_root` (a forged routing outcome) is rejected by `gQueueRootAfter` alone. -/
theorem queuePipelineVm_rejects_wrong_queue_root (env : VmRowEnv)
    (hwrong : env.loc (saCol QUEUE_ROOT_FIELD) ≠ env.loc (prmCol param.PIPELINE_SOURCE_NEW_ROOT)) :
    ¬ (VmConstraint.gate gQueueRootAfter).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gQueueRootAfter, eSA, ePrmNewRoot, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

theorem queuePipelineVm_rejects_moved_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (VmConstraint.gate gBalLoFreeze).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-! ## §6 — The structured per-cell spec + descriptor soundness (REUSING `CellState`). -/

/-- The pipeline parameters carried in the param block. -/
structure PipelineParams where
  oldRoot : ℤ
  newRoot : ℤ

/-- `RowEncodesPipeline env pre p post` ties the row's state-block + param columns to a transition. -/
def RowEncodesPipeline (env : VmRowEnv) (pre : CellState) (p : PipelineParams) (post : CellState) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (sbCol state.STATE_COMMIT) = pre.commit
  ∧ env.loc (prmCol param.PIPELINE_SOURCE_OLD_ROOT) = p.oldRoot
  ∧ env.loc (prmCol param.PIPELINE_SOURCE_NEW_ROOT) = p.newRoot
  ∧ env.loc sel.NOOP = 0
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved
  ∧ env.loc (saCol state.STATE_COMMIT) = post.commit
  ∧ env.pub pi.OLD_COMMIT = pre.commit
  ∧ env.pub pi.NEW_COMMIT = post.commit

/-- **`CellPipelineSpec pre p post`** — the per-cell FULL-state pipeline-step spec: the ledger is FROZEN,
the queue-root cell (`fields 4`) goes `oldRoot → newRoot`, the nonce TICKS, the rest frozen. -/
def CellPipelineSpec (pre : CellState) (p : PipelineParams) (post : CellState) : Prop :=
  post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce + 1
  ∧ pre.fields 4 = p.oldRoot
  ∧ post.fields 4 = p.newRoot
  ∧ (∀ i : Fin 8, i.val ≠ 4 → post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

theorem intent_to_cellPipelineSpec (env : VmRowEnv) (pre post : CellState) (p : PipelineParams)
    (henc : RowEncodesPipeline env pre p post) (hint : QueuePipelineRowIntent env) :
    CellPipelineSpec pre p post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC, hpOld, hpNew, hNoop,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hbef, haft, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsaLo, ← hsbLo]; exact hbal
  · rw [← hsaHi, ← hsbHi]; exact hbhi
  · have : post.nonce = pre.nonce + (1 - env.loc sel.NOOP) := by rw [← hsaN, ← hsbN]; exact hnon
    rw [this, hNoop]; ring
  · have h4b : env.loc (sbCol (state.FIELD_BASE + 4)) = pre.fields ⟨4, by decide⟩ := hsbF ⟨4, by decide⟩
    have hbef' : env.loc (sbCol (state.FIELD_BASE + 4)) = env.loc (prmCol param.PIPELINE_SOURCE_OLD_ROOT) := hbef
    have hfe : pre.fields (4 : Fin 8) = pre.fields ⟨4, by decide⟩ := by congr 1
    rw [hfe, ← h4b, hbef', hpOld]
  · have h4a : env.loc (saCol (state.FIELD_BASE + 4)) = post.fields ⟨4, by decide⟩ := hsaF ⟨4, by decide⟩
    have haft' : env.loc (saCol (state.FIELD_BASE + 4)) = env.loc (prmCol param.PIPELINE_SOURCE_NEW_ROOT) := haft
    have hfe : post.fields (4 : Fin 8) = post.fields ⟨4, by decide⟩ := by congr 1
    rw [hfe, ← h4a, haft', hpNew]
  · intro i hi4
    have hmem : i.val ∈ ([0, 1, 2, 3, 5, 6, 7] : List Nat) := by
      have := i.isLt; fin_cases i <;> first | (exact absurd rfl hi4) | decide
    have := hfld i.val hmem
    rw [← hsaF i, ← hsbF i]; exact this
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres

theorem queuePipelineDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (p : PipelineParams)
    (henc : RowEncodesPipeline env pre p post)
    (hsat : satisfiedVm hash queuePipelineVmDescriptor env true true) :
    CellPipelineSpec pre p post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates' : ∀ c ∈ queuePipelineRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ queuePipelineVmDescriptor.constraints := by
      unfold queuePipelineVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hc))
    have := hcs c hmem
    unfold queuePipelineRowGates gFieldPassNonRoot at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (queuePipelineVm_faithful env).mp hgates'
  refine ⟨intent_to_cellPipelineSpec env pre post p henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ queuePipelineVmDescriptor.constraints := by
      unfold queuePipelineVmDescriptor
      simp only [List.mem_append]
      exact Or.inr hc
    have hh := hcs c hmem
    unfold boundaryLastPins at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      · simp only [VmConstraint.holdsVm] at hh ⊢
        exact hh
  have hpin := (boundaryLast_pins env hlast).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]; exact hpin

/-! ## §7 — The anti-ghost commitment tooth (REUSED; site1 absorbs `fields[4]`, the queue root). -/

theorem queuePipelineDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash queuePipelineVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash queuePipelineVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ transferHashSites := hsat₁.2.1
  have hs₂ : siteHoldsAll hash e₂ transferHashSites := hsat₂.2.1
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash queuePipelineVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ queuePipelineVmDescriptor.constraints := by
        unfold queuePipelineVmDescriptor
        simp only [List.mem_append]
        exact Or.inr hc
      have hh := hcs c hmem
      unfold boundaryLastPins at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        · simp only [VmConstraint.holdsVm] at hh ⊢
          exact hh
    exact (boundaryLast_pins e hlast).1
  have hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT) := by
    rw [hc e₁ hsat₁, hc e₂ hsat₂, hpub]
  exact absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §8 — CONNECTOR to universe-A: the ledger FREEZE agrees; the source-root advance is the routing image.

`QueuePipelineFanoutSpec` pins `s'.kernel.bal = s.kernel.bal` (balance-NEUTRAL) — the descriptor's
balance-freeze gate AGREES with universe A DIRECTLY (no divergence, unlike the fee'd effects). The
routed-message dequeue is realized at the runtime's `fields[4]` source-root advance (bound above). -/

open Dregg2.Circuit.Spec.QueuePipelineFanout
open Dregg2.Exec

/-- Project the `(c, asset)` per-asset ledger entry into the keystone `CellState`'s `balLo` limb. -/
def cellProjBal (bal : CellId → AssetId → ℤ) (c : CellId) (asset : AssetId) : CellState where
  balLo    := bal c asset
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`unify_pipeline_balFrozen`** — across a committed `QueuePipelineFanoutSpec` post-state, the projected
`(c, asset)` ledger entry is FROZEN. So the descriptor's balance-freeze gate IS `queuePipelineStepA`'s
genuine per-cell balance image — DIRECT agreement with universe A. The source-root advance is bound at
`fields[4]` (the runtime carrier). -/
theorem unify_pipeline_balFrozen (s : RecChainedState) (srcId : Nat) (owner : CellId)
    (sinkCells : List CellId) (sinkIds : List Nat) (s' : RecChainedState) (c : CellId) (asset : AssetId)
    (hspec : QueuePipelineFanoutSpec s srcId owner sinkCells sinkIds s') :
    (cellProjBal s'.kernel.bal c asset).balLo = (cellProjBal s.kernel.bal c asset).balLo := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hbal, _⟩ := hspec
  show s'.kernel.bal c asset = s.kernel.bal c asset
  rw [hbal]

/-! ## §9 — NON-VACUITY. -/

/-- A concrete pipeline-step row (old root 9, new root 30): `bal_lo 64 → 64` (FROZEN), nonce 2 → 3 (TICK),
`fields[4] 9 → 30` (source-root advance), rest frozen. -/
def goodPipelineRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_QUEUE_PIPELINE then 1
    else if v = sbCol state.BALANCE_LO then 64
    else if v = saCol state.BALANCE_LO then 64
    else if v = sbCol state.NONCE then 2
    else if v = saCol state.NONCE then 3
    else if v = prmCol param.PIPELINE_SOURCE_OLD_ROOT then 9
    else if v = prmCol param.PIPELINE_SOURCE_NEW_ROOT then 30
    else if v = sbCol QUEUE_ROOT_FIELD then 9
    else if v = saCol QUEUE_ROOT_FIELD then 30
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `goodPipelineRow` REALIZES the reconciled pipeline-step intent. -/
theorem goodPipelineRow_realizes_intent : QueuePipelineRowIntent goodPipelineRow := by
  unfold QueuePipelineRowIntent goodPipelineRow QUEUE_ROOT_FIELD
  simp only [sbCol, saCol, prmCol, SEL_QUEUE_PIPELINE, sel.NOOP, STATE_BEFORE_BASE, STATE_AFTER_BASE,
    PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE, param.PIPELINE_SOURCE_OLD_ROOT,
    param.PIPELINE_SOURCE_NEW_ROOT]
  refine ⟨rfl, rfl, by norm_num, rfl, rfl, by norm_num, by norm_num, ?_⟩
  intro i hi
  fin_cases hi <;> norm_num

/-- A FORGED pipeline-step row: the post queue root tampered to `999` (a forged routing outcome). -/
def badRootRow : VmRowEnv where
  loc := fun v => if v = saCol QUEUE_ROOT_FIELD then 999 else goodPipelineRow.loc v
  nxt := goodPipelineRow.nxt
  pub := goodPipelineRow.pub

/-- **NON-VACUITY (witness FALSE / concrete queue-root anti-ghost).** `badRootRow`'s post queue root is
not `source_new_root`, so `gQueueRootAfter` REJECTS it — the bound routing outcome. -/
theorem badRootRow_rejected :
    ¬ (VmConstraint.gate gQueueRootAfter).holdsVm badRootRow false false := by
  apply queuePipelineVm_rejects_wrong_queue_root
  simp only [badRootRow, goodPipelineRow, saCol, sbCol, prmCol, QUEUE_ROOT_FIELD, SEL_QUEUE_PIPELINE,
    STATE_AFTER_BASE, STATE_BEFORE_BASE, PARAM_BASE, STATE_SIZE, NUM_PARAMS, NUM_EFFECTS,
    state.FIELD_BASE, state.BALANCE_LO, state.NONCE, param.PIPELINE_SOURCE_OLD_ROOT,
    param.PIPELINE_SOURCE_NEW_ROOT]
  norm_num

/-! ## §10 — Axiom-hygiene pins. -/

#guard queuePipelineVmDescriptor.constraints.length == 14 + 14 + 4 + 3
#guard queuePipelineVmDescriptor.hashSites.length == 4
#guard queuePipelineVmDescriptor.traceWidth == 186

#assert_axioms queuePipelineVm_faithful
#assert_axioms queuePipelineVm_rejects_wrong_output
#assert_axioms queuePipelineVm_rejects_wrong_queue_root
#assert_axioms queuePipelineVm_rejects_moved_balance
#assert_axioms intent_to_cellPipelineSpec
#assert_axioms queuePipelineDescriptor_full_sound
#assert_axioms queuePipelineDescriptor_commit_binds_state
#assert_axioms unify_pipeline_balFrozen
#assert_axioms goodPipelineRow_realizes_intent
#assert_axioms badRootRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitQueuePipelineStep
