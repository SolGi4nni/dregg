/-
# Dregg2.Circuit.Emit.EffectVmEmitQueueDequeueFullState — the MAGNESIUM lift of `queueDequeueA`'s
RUNNABLE EffectVM descriptor to FULL state (all 17 `RecordKernelState` fields bound, INCLUDING the
`queues` side-table root).

## The gap this module closes (for the queue family)

`EffectVmEmitQueueDequeue.queueDequeueVmDescriptor` is a `186`-wide row whose published `state_commit`
absorbs the 13 state-block columns (via `transferHashSites`). The FIFO pop-front is bound at `fields[4]`
(the in-row queue-root carrier), but the `state_commit` does NOT absorb the dedicated, non-aliasing
`system_roots` digest carrier (`sysRootsDigestCol = 186`, PAST the `186`-wide layout) — so the queue
side-table is bound by the descriptor only as a per-cell `fields[4]` projection, NOT as the whole
8-root `system_roots` sub-block. A satisfying RUNNABLE proof pins a projection, not the WHOLE post-state.

This module SUPERSEDES that with the verified-by-construction WIDE descriptor + the GENERIC full-state
crown `EffectVmFullStateRunnable.runnable_full_sound` on the RUNNABLE `EffectVmDescriptor` /
`satisfiedVm`. The widening follows the §6 RECIPE verbatim (the twin of `EffectVmEmitQueueEnqueueFullState`,
with the refund CREDIT in place of the deposit debit):

  1. **the wide descriptor** `queueDequeueVmDescriptorWide`: the `186`-wide dequeue descriptor with
     `traceWidth := EFFECT_VM_WIDTH_SYSROOTS`, `hashSites := wideHashSites` (so `usesWideSites := rfl`),
     PLUS the root-UPDATE gate `gQueueSysRootUpdate` pinning `sysRootsDigestCol =
     sysRootsDigestColBefore + step` over the DEDICATED carrier (the §6 step-1 gate on the non-aliasing
     `sysRootsDigestCol`/`sysRootsDigestColBefore`).
  2. **`isRow`** := `IsQueueDequeueRow`.
  3. **`decodeAfter`** := `RowEncodesCredit` EXTENDED with the `queues`-root structural transition
     `postRoots = Function.update preRoots QUEUE newQueueRoot`.
  4. **`fullClause`** := the declarative 17-field post for dequeue: the per-cell `CellCreditSpec` (balance
     credited by the refund, the queue-root cell advanced, nonce ticked, frame frozen) AND the
     `system_roots` sub-block moved ONLY at the `QUEUE` index (the other 7 roots frozen).
  5. **`decodeFull`** := THIN: project the per-row gates to `QueueDequeueRowIntent`
     (`queueDequeueVm_faithful`), then `intent_to_cellCreditSpec`, then carry the decode root transition.

The crypto is DISCHARGED ONCE in the generic module; this instance carries NO new portal. The anti-ghost
on all 17 fields is `runnable_full_commit_binds`/`wide_rejects_*_tamper` at this spec (§3½).

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; the sole crypto carrier is the named
`Poseidon2SpongeCR` portal. No `sorry`, no `:= True`, no `native_decide`. `fullClause` is NON-vacuous
(witness TRUE + a refuted forged post-state + a refuted dropped-root post-state). Imports are read-only;
this file owns only itself.
-/
import Dregg2.Circuit.Emit.EffectVmEmitQueueDequeue
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable

namespace Dregg2.Circuit.Emit.EffectVmEmitQueueDequeueFullState

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSub boundaryLastPins boundaryLast_pins transferHashSites)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState absorbedCols)
open Dregg2.Circuit.Emit.EffectVmEmitQueueDequeue
  (SEL_QUEUE_DEQUEUE IsQueueDequeueRow QUEUE_ROOT_FIELD RefundParams CellCreditSpec
   RowEncodesCredit QueueDequeueRowIntent queueDequeueRowGates queueDequeueVmDescriptor
   queueDequeueVm_faithful intent_to_cellCreditSpec gFieldPassNonRoot)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (wideHashSites RunnableFullStateSpec runnable_full_sound runnable_full_commit_binds
   wide_rejects_state_tamper wide_rejects_root_tamper)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec.SystemRoots
  (SysRoots systemRootsDigest N_SYSTEM_ROOTS emptySystemRoots)

set_option linter.unusedVariables false

/-! ## §0 — the `queues` side-table root index + the accumulator-step carrier (over the DEDICATED columns). -/

/-- The kernel index of the `queues` side-table root in the `system_roots` sub-block
(`Exec.SystemRoots.systemRoot.QUEUE = 1`). Binding the dedicated carrier binds this root. -/
def QUEUE_ROOT_INDEX : Fin N_SYSTEM_ROOTS := ⟨Dregg2.Exec.SystemRoots.systemRoot.QUEUE, by decide⟩

/-- The `queues`-accumulator STEP param: the field-element delta the popped message contributes to the
`system_roots` digest. The trace generator lays it at `param2` (param1 = the refund; param2 = the digest
step the prover computed from the FIFO pop), as `EffectVmEmitCreateEscrow.ESCROW_ROOT_STEP_PARAM`. -/
def QUEUE_ROOT_STEP_PARAM : Nat := 2

/-- The accumulator-step expression (param column 2). -/
def ePrmQueueStep : EmittedExpr := .var (prmCol QUEUE_ROOT_STEP_PARAM)

/-- **Root-UPDATE gate body** over the DEDICATED carrier: `sysRootsDigestCol − sysRootsDigestColBefore −
step` (so `sysRootsDigestCol = sysRootsDigestColBefore + step`). Reads the before/after `system_roots`
digest carriers (`= 187`/`= 186`, both PAST the `186`-wide layout, non-aliasing) and the `param2`
accumulator step. The §6 step-1 gate on the dedicated carrier the wide commitment ABSORBS. -/
def gQueueSysRootUpdate : EmittedExpr :=
  eSub (eSub (.var sysRootsDigestCol) (.var sysRootsDigestColBefore)) ePrmQueueStep

/-! ## §1 — the WIDE dequeue descriptor (§6 step-1). -/

/-- **`queueDequeueVmDescriptorWide newRoot`** — the dequeue descriptor WIDENED to bind the WHOLE
`system_roots` sub-block: the SAME per-row gates + transitions + boundary pins as
`queueDequeueVmDescriptor newRoot`, PLUS the root-UPDATE gate `gQueueSysRootUpdate`, with
`traceWidth := EFFECT_VM_WIDTH_SYSROOTS` and `hashSites := wideHashSites`. Strictly additive. -/
def queueDequeueVmDescriptorWide (newRoot : ℤ) : EffectVmDescriptor :=
  { queueDequeueVmDescriptor newRoot with
    name := "dregg-effectvm-queuedequeue-v1-sysroots"
    traceWidth := EFFECT_VM_WIDTH_SYSROOTS
    constraints := (queueDequeueVmDescriptor newRoot).constraints ++ [.gate gQueueSysRootUpdate]
    hashSites := wideHashSites }

/-- The wide descriptor's hash-sites ARE the `system_roots`-absorbing wide sites. By `rfl`. -/
theorem queueDequeueWide_usesWideSites :
    (queueDequeueVmDescriptorWide 0).hashSites = wideHashSites := rfl

/-- The per-row dequeue gates remain a sublist of the wide descriptor's constraints. -/
theorem queueDequeueWide_rowGates_sub (newRoot : ℤ) (c : VmConstraint)
    (hc : c ∈ queueDequeueRowGates newRoot) :
    c ∈ (queueDequeueVmDescriptorWide newRoot).constraints := by
  show c ∈ ((queueDequeueVmDescriptor newRoot).constraints ++ [.gate gQueueSysRootUpdate])
  rw [List.mem_append]
  refine Or.inl ?_
  unfold queueDequeueVmDescriptor
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl hc))

/-! ## §2 — FAITHFULNESS + ANTI-GHOST of the dedicated-carrier root-update gate. -/

/-- **`QueueSysRootIntent env`** — the intended `queues`-root move on the row: the dedicated digest
carrier ADVANCES by the `param2` accumulator step (`sysRootsDigestCol = sysRootsDigestColBefore + step`).
The per-row projection of the FIFO pop onto the committed `system_roots` digest. -/
def QueueSysRootIntent (env : VmRowEnv) : Prop :=
  env.loc sysRootsDigestCol = env.loc sysRootsDigestColBefore + env.loc (prmCol QUEUE_ROOT_STEP_PARAM)

/-- **`queueSysRoot_gate_faithful`.** The root-update gate holds IFF the dedicated digest carrier advances
by the accumulator step. -/
theorem queueSysRoot_gate_faithful (env : VmRowEnv) :
    (VmConstraint.gate gQueueSysRootUpdate).holdsVm env false false ↔ QueueSysRootIntent env := by
  simp only [VmConstraint.holdsVm, gQueueSysRootUpdate, ePrmQueueStep, eSub, EmittedExpr.eval,
    QueueSysRootIntent]
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-- **Anti-ghost (dedicated-carrier root tamper).** A row whose after-digest carrier is NOT the advanced
accumulator (`before + step`) is rejected by `gQueueSysRootUpdate` — a dropped/forged `queues` update is
UNSAT at the dedicated carrier the wide commitment absorbs. -/
theorem queueSysRoot_rejects_wrong_root (env : VmRowEnv)
    (hwrong : env.loc sysRootsDigestCol
      ≠ env.loc sysRootsDigestColBefore + env.loc (prmCol QUEUE_ROOT_STEP_PARAM)) :
    ¬ (VmConstraint.gate gQueueSysRootUpdate).holdsVm env false false := by
  intro h; exact hwrong ((queueSysRoot_gate_faithful env).mp h)

/-! ## §3 — THE FULL-STATE RUNNABLE INSTANCE (the deliverable). -/

/-- **`QueueDequeueFullClause p newRoot preRoots queueRootAfter`** — the full declarative post-state for
a queue dequeue over `(pre, post, postRoots)`: the per-cell `CellCreditSpec pre p newRoot post` AND the
`system_roots` sub-block moved ONLY at the `QUEUE` index
(`postRoots = Function.update preRoots QUEUE_ROOT_INDEX queueRootAfter`). NON-vacuous (§4). -/
def QueueDequeueFullClause (p : RefundParams) (newRoot : ℤ) (preRoots : SysRoots) (queueRootAfter : ℤ)
    (pre post : CellState) (postRoots : SysRoots) : Prop :=
  CellCreditSpec pre p newRoot post
  ∧ postRoots = Function.update preRoots QUEUE_ROOT_INDEX queueRootAfter

/-- **`queueDequeueRunnableSpec` — THE FULL-STATE RUNNABLE INSTANCE.** `decodeAfter` is `RowEncodesCredit`
PLUS the `queues`-root structural transition; `decodeFull` projects the wide descriptor's per-row gates
(= dequeue's) to the GATE-ONLY per-cell soundness (`queueDequeueVm_faithful` ⟹ `intent_to_cellCreditSpec`),
then carries the root transition. THIN; NON-VACUOUS (`fullClause` is the genuine refund credit + the
precise queue root advance, not `True`). -/
def queueDequeueRunnableSpec (newRoot : ℤ) (p : RefundParams) (preRoots : SysRoots)
    (queueRootAfter : ℤ) : RunnableFullStateSpec CellState where
  descriptor    := queueDequeueVmDescriptorWide newRoot
  usesWideSites := rfl
  isRow         := IsQueueDequeueRow
  decodeAfter   := fun env pre post postRoots =>
    RowEncodesCredit env pre p newRoot post
      ∧ postRoots = Function.update preRoots QUEUE_ROOT_INDEX queueRootAfter
  fullClause    := QueueDequeueFullClause p newRoot preRoots queueRootAfter
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots⟩ := hdec
    have hrowgates : ∀ c ∈ queueDequeueRowGates newRoot, c.holdsVm env false false := by
      intro c hc
      have hh := hgates c (queueDequeueWide_rowGates_sub newRoot c hc)
      unfold queueDequeueRowGates gFieldPassNonRoot at hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hc
      rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
        simpa only [VmConstraint.holdsVm] using hh
    have hint := (queueDequeueVm_faithful env newRoot).mp hrowgates
    exact ⟨intent_to_cellCreditSpec env pre post p newRoot henc hint, hroots⟩

/-! ## §3¼ — THE CROWN: a satisfying WIDE row pins the FULL 17-field dequeue post-state. -/

/-- **`queueDequeue_runnable_full_sound` — THE DELIVERABLE.** A row satisfying the WIDE dequeue runnable
descriptor (`satisfiedVm`, first/last active), under the structured decode (per-cell `RowEncodesCredit` +
the `queues`-root transition), pins the FULL 17-field declarative post-state `QueueDequeueFullClause`: the
per-cell refund-credit / queue-root-cell-advance / nonce-tick / frame-freeze (gate-forced) AND the
`system_roots` sub-block moved ONLY at the `QUEUE` index. The analog of the transfer reference, for the
circuit the prover ACTUALLY RUNS — strengthening the per-cell `queueDequeueDescriptor_full_sound` to the
WHOLE `system_roots` state. -/
theorem queueDequeue_runnable_full_sound (hash : List ℤ → ℤ)
    (newRoot : ℤ) (p : RefundParams) (preRoots : SysRoots) (queueRootAfter : ℤ)
    (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsQueueDequeueRow env)
    (henc : RowEncodesCredit env pre p newRoot post)
    (hroots : postRoots = Function.update preRoots QUEUE_ROOT_INDEX queueRootAfter)
    (hsat : satisfiedVm hash (queueDequeueVmDescriptorWide newRoot) env true true) :
    QueueDequeueFullClause p newRoot preRoots queueRootAfter pre post postRoots :=
  runnable_full_sound (queueDequeueRunnableSpec newRoot p preRoots queueRootAfter) hash env pre post
    postRoots hrow ⟨henc, hroots⟩ hsat

#assert_axioms queueDequeue_runnable_full_sound

/-! ## §3½ — THE WHOLE-STATE ANTI-GHOST (all 17 fields, on the RUNNABLE descriptor). -/

/-- **`queueDequeue_full_commit_binds`** — two wide dequeue rows publishing the same `NEW_COMMIT`, whose
dedicated carriers ARE the `systemRootsDigest` of their post sub-blocks, agree on every absorbed
state-block column AND every side-table root (the queue root included). The runnable dequeue commitment
binds the whole post-state. -/
theorem queueDequeue_full_commit_binds
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (newRoot : ℤ)
    (p : RefundParams) (preRoots : SysRoots) (queueRootAfter : ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash (queueDequeueVmDescriptorWide newRoot) e₁ true true)
    (hsat₂ : satisfiedVm hash (queueDequeueVmDescriptorWide newRoot) e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂) :
    absorbedCols e₁ = absorbedCols e₂ ∧ (∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i) :=
  runnable_full_commit_binds (queueDequeueRunnableSpec newRoot p preRoots queueRootAfter)
    hash hCR e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂

/-- **Anti-ghost (queue side-table root tamper, on the RUNNABLE descriptor).** Two wide dequeue rows
publishing the same `NEW_COMMIT` (with `systemRootsDigest` carriers) whose `system_roots` sub-blocks
DIFFER at the `QUEUE` index (a dropped/forged FIFO pop) cannot both satisfy. -/
theorem queueDequeue_rejects_queue_root_tamper
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (newRoot : ℤ)
    (p : RefundParams) (preRoots : SysRoots) (queueRootAfter : ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash (queueDequeueVmDescriptorWide newRoot) e₁ true true)
    (hsat₂ : satisfiedVm hash (queueDequeueVmDescriptorWide newRoot) e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    (htamper : sr₁ QUEUE_ROOT_INDEX ≠ sr₂ QUEUE_ROOT_INDEX) : False :=
  wide_rejects_root_tamper (queueDequeueRunnableSpec newRoot p preRoots queueRootAfter)
    hash hCR e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-- **Anti-ghost (per-cell state-block tamper, on the RUNNABLE descriptor).** Two wide dequeue rows
publishing the same `NEW_COMMIT` whose absorbed state-block columns DIFFER cannot both satisfy. -/
theorem queueDequeue_rejects_state_tamper
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (newRoot : ℤ)
    (p : RefundParams) (preRoots : SysRoots) (queueRootAfter : ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash (queueDequeueVmDescriptorWide newRoot) e₁ true true)
    (hsat₂ : satisfiedVm hash (queueDequeueVmDescriptorWide newRoot) e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    (htamper : absorbedCols e₁ ≠ absorbedCols e₂) : False :=
  wide_rejects_state_tamper (queueDequeueRunnableSpec newRoot p preRoots queueRootAfter)
    hash hCR e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

#assert_axioms queueDequeue_full_commit_binds
#assert_axioms queueDequeue_rejects_queue_root_tamper
#assert_axioms queueDequeue_rejects_state_tamper

/-! ## §4 — NON-VACUITY of the full clause (witness TRUE + a refuted forged post-state). -/

/-- A concrete pre `CellState` (balance 70, nonce 4, all fields/cap/reserved 0). -/
def goodPre : CellState where
  balLo := 70; balHi := 0; nonce := 4; fields := fun _ => 0; capRoot := 0; reserved := 0; commit := 0

/-- The genuine dequeue image of `goodPre` (refund 25, advanced queue root 888): balance 95, nonce 5,
`fields 4 = 888`, the rest frozen. -/
def goodPost : CellState where
  balLo := 95; balHi := 0; nonce := 5
  fields := fun i => if i = (4 : Fin 8) then 888 else 0
  capRoot := 0; reserved := 0; commit := 0

/-- The dequeue params (refund 25). -/
def goodParams : RefundParams := ⟨25⟩

/-- A frozen reference `system_roots` sub-block (the empty sub-block). The post sub-block updates ONLY the
`QUEUE` index to a new digest value (here 888). -/
def goodPreRoots : SysRoots := emptySystemRoots

/-- **`dequeue_realizes` — NON-VACUITY (witness TRUE).** The dequeue `fullClause` is INHABITED by a real
dequeue: `goodPost` is the genuine `CellCreditSpec` image of `goodPre` (70 → 95, nonce 4 → 5,
`fields 4 → 888`, frame frozen) and the post sub-block advances ONLY the `QUEUE` root. So the framework's
`fullClause` is NOT `True`. -/
theorem dequeue_realizes :
    (queueDequeueRunnableSpec 888 goodParams goodPreRoots 888).fullClause goodPre goodPost
      (Function.update goodPreRoots QUEUE_ROOT_INDEX 888) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · decide          -- balLo: 95 = 70 + 25
  · rfl             -- balHi frozen
  · decide          -- nonce: 5 = 4 + 1
  · simp [goodPost]   -- fields 4 = 888
  · intro i hi              -- the 7 other field cells frozen (both 0)
    have hne : i ≠ (4 : Fin 8) := fun h => hi (by rw [h]; rfl)
    simp only [goodPost, goodPre, if_neg hne]
  · rfl             -- capRoot frozen
  · rfl             -- reserved frozen

/-- **`dequeue_clause_not_trivial` — the clause is REFUTABLE (witness FALSE).** A post-state whose `balLo`
is NOT the refund-credited value (`goodPre.balLo = 70`, demanding `95`, but a forged `999`) FAILS
`QueueDequeueFullClause`. -/
theorem dequeue_clause_not_trivial :
    ¬ QueueDequeueFullClause goodParams 888 goodPreRoots 888 goodPre
        { goodPost with balLo := 999 } (Function.update goodPreRoots QUEUE_ROOT_INDEX 888) := by
  rintro ⟨⟨hbal, _⟩, _⟩
  -- hbal : (999) = goodPre.balLo + goodParams.amount = 70 + 25 = 95
  simp only [goodPre, goodParams] at hbal
  norm_num at hbal

/-- **`dequeue_clause_rejects_root_drop` — the clause REJECTS a dropped queue-root advance (witness
FALSE).** A post sub-block that FREEZES the `QUEUE` root (leaves it at `preRoots`'s `0`) instead of
advancing it to `888` FAILS the structural transition conjunct — the queue side-table move is genuinely
PART of the full clause. -/
theorem dequeue_clause_rejects_root_drop :
    ¬ QueueDequeueFullClause goodParams 888 goodPreRoots 888 goodPre goodPost goodPreRoots := by
  rintro ⟨_, hroots⟩
  have := congrFun hroots QUEUE_ROOT_INDEX
  simp only [goodPreRoots, emptySystemRoots, Function.update_self] at this
  exact absurd this (by norm_num)

#assert_axioms dequeue_realizes
#assert_axioms dequeue_clause_not_trivial
#assert_axioms dequeue_clause_rejects_root_drop
#assert_axioms queueSysRoot_gate_faithful
#assert_axioms queueSysRoot_rejects_wrong_root

/-! ## §5 — width/shape pins. -/

#guard (queueDequeueVmDescriptorWide 0).traceWidth == 188
#guard (queueDequeueVmDescriptorWide 0).hashSites.length == 4
#guard (queueDequeueVmDescriptorWide 0).constraints.length
        == (queueDequeueVmDescriptor 0).constraints.length + 1
#guard QUEUE_ROOT_INDEX.val == 1

end Dregg2.Circuit.Emit.EffectVmEmitQueueDequeueFullState
