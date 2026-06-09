/-
# Dregg2.Circuit.Emit.EffectVmEmitQueueAllocate — the `queueAllocateA` (FIFO-queue ALLOCATE) effect's
EffectVM emission, through the SAME `EffectVmEmit` IR as transfer.

Universe A (`Inst/queueAllocateA.lean`, `Spec/queuefifocore.lean`) carries the FULL-state soundness
`queueAllocateA_full_sound ⇒ QueueAllocateSpec`: a committed allocate PREPENDS one fresh `QueueRecord`
(`owner := actor`, empty buffer, the given capacity) onto the `queues` side-table, advances the chained
`log` by the allocate receipt, and FREEZES the other 16 kernel fields (`st'.kernel.bal = st.kernel.bal`
— balance-NEUTRAL in universe A).

## STAGE-3 AMPLIFICATION: the queue side-table root is NOW BOUND.

The earlier version of this descriptor reported the FIFO-list leg as OUT-OF-IR (there was no column to
carry the `queues` accumulator root). STAGE 3 (`Exec.SystemRoots`, `state.systemRoot.QUEUE`) gives each
side-table a committed root; the RUNNING EffectVM prover already carries the queue side-table root in the
state block — at `state.FIELD_BASE + 4` (`fields[4]`), the runtime's queue-root carrier
(`effect_vm/trace.rs` + `effect_vm/air.rs` `AllocateQueue` arm). This descriptor now BINDS that carrier:
on an allocate row the runtime writes `fields[4] := hash_2_to_1(0,0)` (the empty-queue root) and the
GROUP-4 site1 (which absorbs `fields[1..5]`, INCLUDING `fields[4]`) folds it into `state_commit`. So the
prepended-fresh-queue root IS bound into the published commitment — the FIFO leg is no longer out-of-IR.

## RECONCILIATION onto the runtime trace-generator layout (the cutover-harness pattern, 3aaf0772d).

The descriptor must AGREE with the hand-AIR on the honest trace. The runtime `AllocateQueue` arm:
  * DEBITS the balance by `capacity * cost_per_slot` (`param0 * param2`) — NOT balance-neutral on the row
    (the runtime charges the allocation fee; universe A's `QueueAllocateSpec` is balance-NEUTRAL — the
    §connector reports this runtime-fee-vs-univA-neutral divergence exactly as the notes keystone does,
    reconciling at `cap*cost = 0`).
  * TICKS the nonce (the global non-NoOp invariant `new_nonce − old_nonce − (1 − s_noop) = 0`); the
    earlier descriptor FROZE it (UNSAT on the honest trace) — now fixed via the shared `gNonce`.
  * WRITES `fields[4] := empty_queue_hash` (the fresh-queue root) and FREEZES `fields[0..3]`, `fields[5..7]`,
    cap_root, reserved, bal_hi.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` hypothesis. No `sorry`, no `:= True`, no `native_decide`, no `rfl`-posing-as-bridge.
Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.queuefifocore

namespace Dregg2.Circuit.Emit.EffectVmEmitQueueAllocate

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

/-! ## §0 — The queueAllocate selector + the runtime allocate parameters.

The running EffectVM lays one selector per effect (`columns.rs::sel::ALLOCATE_QUEUE = 18`). The allocate
fee parameters are `param0 = QUEUE_CAPACITY`, `param2 = QUEUE_COST_PER_SLOT` (the runtime's
`Effect::AllocateQueue` arm); the fee debited is their product. On a genuine allocate row the allocate
selector is `1` and `s_noop = 0` (so the nonce TICKS). -/

/-- The queueAllocate selector column index (`columns.rs::sel::ALLOCATE_QUEUE`). -/
def SEL_QUEUE_ALLOCATE : Nat := 18

/-! Runtime allocate parameter columns (`columns.rs::param::QUEUE_*`). -/
namespace param
/-- Queue capacity (`param::QUEUE_CAPACITY`). -/
def QUEUE_CAPACITY : Nat := 0
/-- Per-slot cost (`param::QUEUE_COST_PER_SLOT`). -/
def QUEUE_COST_PER_SLOT : Nat := 2
end param

/-- Capacity as an expression (`param0`). -/
def ePrmCap : EmittedExpr := .var (prmCol param.QUEUE_CAPACITY)
/-- Per-slot cost as an expression (`param2`). -/
def ePrmCost : EmittedExpr := .var (prmCol param.QUEUE_COST_PER_SLOT)

/-- The queue-root state column (`fields[4]`, the runtime's queue-side-table-root carrier;
`state.systemRoot.QUEUE`'s in-state-block home under the STAGE-3 reconciliation). -/
def QUEUE_ROOT_FIELD : Nat := state.FIELD_BASE + 4

/-- The allocate row: `s_queue_allocate = 1`, `s_noop = 0`. -/
def IsQueueAllocateRow (env : VmRowEnv) : Prop :=
  env.loc SEL_QUEUE_ALLOCATE = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — The per-row gate bodies (allocation-fee DEBIT + queue-root BIND + nonce TICK).

* `gBalLoDebit` — `new_bal_lo − old_bal_lo + capacity·cost` (the allocation fee leaves the ledger).
* `gQueueRootBind` — `fields[4]_after − emptyQueueRoot` (the fresh-queue root is written; `emptyQueueRoot`
  is a SYMBOL the descriptor binds against the runtime's `hash_2_to_1(0,0)` witness column — passed in
  so the descriptor is hash-agnostic, matching the cutover harness which supplies the concrete felt).
* `gNonceTick` (= the shared `gNonce`) — `new_nonce − old_nonce − (1 − s_noop)` (TICKS on a non-NoOp row).
* `gBalHi`/`gCapPass`/`gResPass`/`gFieldPass i` (i ≠ 4) — REUSED from the transfer template (frozen). -/

/-- Balance-lo DEBIT body: `new_bal_lo − old_bal_lo + capacity·cost` (the fee leaves: `new = old − cap·cost`). -/
def gBalLoDebit : EmittedExpr :=
  .add (eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)) (.mul ePrmCap ePrmCost)

/-- Queue-root BIND body: `fields[4]_after − emptyRoot`. The fresh-queue empty root (the runtime's
`hash_2_to_1(0,0)`) is supplied as a parameter so the gate is hash-agnostic — the cutover harness fills
the concrete felt; the descriptor only asserts the carrier equals it. -/
def gQueueRootBind (emptyRoot : ℤ) : EmittedExpr :=
  .add (eSA QUEUE_ROOT_FIELD) (.const (-emptyRoot))

/-- Nonce TICK body (the running prover's global non-NoOp invariant), reused verbatim from transfer. -/
def gNonceTick : EmittedExpr := gNonce

/-- The seven NON-queue-root field passthrough gates (`fields[0..3]`, `fields[5..7]`; `fields[4]` is the
queue-root carrier, bound by `gQueueRootBind` instead of frozen). -/
def gFieldPassNonRoot : List VmConstraint :=
  ([0, 1, 2, 3, 5, 6, 7] : List Nat).map (fun i => VmConstraint.gate (gFieldPass i))

/-! ## §2 — The emitted queueAllocate descriptor. -/

/-- The queueAllocate AIR identity. -/
def queueAllocateVmAirName : String := "dregg-effectvm-queueallocate-v1"

/-- The allocate per-row gates (parameterized by the empty-queue root felt): fee debit, bal_hi freeze,
nonce TICK, cap/reserved freeze, queue-root bind, 7 non-root field freezes. -/
def queueAllocateRowGates (emptyRoot : ℤ) : List VmConstraint :=
  [ .gate gBalLoDebit, .gate gBalHi, .gate gNonceTick
  , .gate gCapPass, .gate gResPass, .gate (gQueueRootBind emptyRoot) ] ++ gFieldPassNonRoot

/-- **`queueAllocateVmDescriptor emptyRoot`** — the FULL allocate descriptor reconciled onto the runtime
layout: fee-debit + queue-root-bind + nonce-tick + freeze gates ++ transition continuity ++ the 7
boundary PI pins, with the 4 ordered GROUP-4 hash sites (site1 absorbs `fields[4]`, so the queue root is
folded into `state_commit`) and the 2 balance-limb range checks. -/
def queueAllocateVmDescriptor (emptyRoot : ℤ) : EffectVmDescriptor :=
  { name := queueAllocateVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := queueAllocateRowGates emptyRoot ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The queueAllocate ROW INTENT (the faithfulness target, runtime-reconciled).

`QueueAllocateRowIntent env emptyRoot`: on an allocate row, the balance drops by `capacity·cost` (the
allocation fee), the queue-root carrier (`fields[4]`) becomes `emptyRoot` (the fresh-queue root), the
nonce TICKS, and the rest of the frame (bal_hi, cap/reserved, `fields[0..3]`, `fields[5..7]`) is FROZEN. -/

/-- **`QueueAllocateRowIntent env emptyRoot`** — the runtime allocate move. -/
def QueueAllocateRowIntent (env : VmRowEnv) (emptyRoot : ℤ) : Prop :=
  env.loc (saCol state.BALANCE_LO)
      = env.loc (sbCol state.BALANCE_LO)
        - env.loc (prmCol param.QUEUE_CAPACITY) * env.loc (prmCol param.QUEUE_COST_PER_SLOT)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ env.loc (saCol QUEUE_ROOT_FIELD) = emptyRoot
  ∧ (∀ i ∈ ([0, 1, 2, 3, 5, 6, 7] : List Nat),
        env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the (runtime-reconciled) intent. -/

/-- **`queueAllocateVm_faithful`.** On an allocate row, the emitted descriptor's per-row gates all hold
IFF `QueueAllocateRowIntent` holds — the gates pin EXACTLY the fee-debit + queue-root-bind + nonce-tick
+ frame-freeze. -/
theorem queueAllocateVm_faithful (env : VmRowEnv) (emptyRoot : ℤ) :
    (∀ c ∈ queueAllocateRowGates emptyRoot, c.holdsVm env false false)
      ↔ QueueAllocateRowIntent env emptyRoot := by
  unfold queueAllocateRowGates gFieldPassNonRoot QueueAllocateRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoDebit) (by simp)
    have hHi := h (.gate gBalHi) (by simp)
    have hNon := h (.gate gNonceTick) (by simp)
    have hCap := h (.gate gCapPass) (by simp)
    have hRes := h (.gate gResPass) (by simp)
    have hRoot := h (.gate (gQueueRootBind emptyRoot)) (by simp)
    have hFld : ∀ i ∈ ([0, 1, 2, 3, 5, 6, 7] : List Nat),
        VmConstraint.holdsVm env false false (.gate (gFieldPass i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoDebit, gBalHi, gNonceTick, gNonce, gCapPass, gResPass,
      gQueueRootBind, eSA, eSB, ePrmCap, ePrmCost, eSelNoop, eSub,
      EmittedExpr.eval] at hLo hHi hNon hCap hRes hRoot
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · linarith [hLo]
    · linarith [hHi]
    · linarith [hNon]
    · linarith [hCap]
    · linarith [hRes]
    · linarith [hRoot]
    · intro i hi
      have := hFld i hi
      simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval] at this
      linarith
  · rintro ⟨hLo, hHi, hNon, hCap, hRes, hRoot, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gBalLoDebit, eSA, eSB, ePrmCap, ePrmCost, eSub,
        EmittedExpr.eval]
      rw [hLo]; ring
    · simp only [VmConstraint.holdsVm, gBalHi, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hHi]; ring
    · simp only [VmConstraint.holdsVm, gNonceTick, gNonce, eSA, eSB, eSelNoop, eSub, EmittedExpr.eval]
      rw [hNon]; ring
    · simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hCap]; ring
    · simp only [VmConstraint.holdsVm, gResPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gQueueRootBind, eSA, EmittedExpr.eval]
      rw [hRoot]; ring
    · simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval]
      have hmem : i ∈ ([0, 1, 2, 3, 5, 6, 7] : List Nat) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto
      rw [hFld i hmem]; ring

/-! ## §5 — ANTI-GHOST: a row that does not realize the (reconciled) move fails the descriptor. -/

/-- **Anti-ghost (general).** A row not realizing the allocate intent fails the per-row gates. -/
theorem queueAllocateVm_rejects_wrong_output (env : VmRowEnv) (emptyRoot : ℤ)
    (hwrong : ¬ QueueAllocateRowIntent env emptyRoot) :
    ¬ (∀ c ∈ queueAllocateRowGates emptyRoot, c.holdsVm env false false) :=
  fun h => hwrong ((queueAllocateVm_faithful env emptyRoot).mp h)

/-- **Anti-ghost (queue-root tamper).** A row whose post-`fields[4]` is NOT the fresh-queue root (an
attacker prepending a forged/omitted queue record) is rejected by `gQueueRootBind` alone. This is the
side-table-root binding the STAGE-3 amplification buys: tampering the queue root ⇒ UNSAT. -/
theorem queueAllocateVm_rejects_wrong_queue_root (env : VmRowEnv) (emptyRoot : ℤ)
    (hwrong : env.loc (saCol QUEUE_ROOT_FIELD) ≠ emptyRoot) :
    ¬ (VmConstraint.gate (gQueueRootBind emptyRoot)).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gQueueRootBind, eSA, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-- **Anti-ghost (fee tamper).** A row whose post-`bal_lo` is not the fee-debited value (the allocation
fee skipped/forged) is rejected by `gBalLoDebit` alone. -/
theorem queueAllocateVm_rejects_wrong_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO)
      ≠ env.loc (sbCol state.BALANCE_LO)
        - env.loc (prmCol param.QUEUE_CAPACITY) * env.loc (prmCol param.QUEUE_COST_PER_SLOT)) :
    ¬ (VmConstraint.gate gBalLoDebit).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoDebit, eSA, eSB, ePrmCap, ePrmCost, eSub,
    EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-! ## §6 — The structured per-cell spec + descriptor soundness (REUSING `CellState`). -/

/-- The allocate parameters carried in the param block (the fee = `capacity·cost`). -/
structure AllocateParams where
  capacity : ℤ
  cost     : ℤ

/-- `RowEncodesAlloc env pre p emptyRoot post` ties the row's state-block + param columns to a
`(pre, p, emptyRoot, post)` allocate transition. The queue-root carrier (`fields[4]`) is tracked
separately as the `pre.fields 4`/`post.fields 4` cells. -/
def RowEncodesAlloc (env : VmRowEnv) (pre : CellState) (p : AllocateParams) (emptyRoot : ℤ)
    (post : CellState) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (sbCol state.STATE_COMMIT) = pre.commit
  ∧ env.loc (prmCol param.QUEUE_CAPACITY) = p.capacity
  ∧ env.loc (prmCol param.QUEUE_COST_PER_SLOT) = p.cost
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

/-- **`CellAllocSpec pre p emptyRoot post`** — the per-cell FULL-state allocate spec: `balLo` drops by
`capacity·cost`, the queue-root cell (`fields 4`) becomes `emptyRoot`, the nonce TICKS, and the rest of
the frame (bal_hi, cap_root, reserved, `fields` 0–3, 5–7) is LITERALLY unchanged. -/
def CellAllocSpec (pre : CellState) (p : AllocateParams) (emptyRoot : ℤ) (post : CellState) : Prop :=
  post.balLo = pre.balLo - p.capacity * p.cost
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce + 1
  ∧ post.fields 4 = emptyRoot
  ∧ (∀ i : Fin 8, i.val ≠ 4 → post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

/-- Decode lemma: under `RowEncodesAlloc`, `QueueAllocateRowIntent` IS the structured `CellAllocSpec`. -/
theorem intent_to_cellAllocSpec (env : VmRowEnv) (pre post : CellState) (p : AllocateParams)
    (emptyRoot : ℤ) (henc : RowEncodesAlloc env pre p emptyRoot post)
    (hint : QueueAllocateRowIntent env emptyRoot) :
    CellAllocSpec pre p emptyRoot post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC, hpCap, hpCost, hNoop,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hroot, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : post.balLo = pre.balLo
        - env.loc (prmCol param.QUEUE_CAPACITY) * env.loc (prmCol param.QUEUE_COST_PER_SLOT) := by
      rw [← hsaLo, ← hsbLo]; exact hbal
    rw [this, hpCap, hpCost]
  · rw [← hsaHi, ← hsbHi]; exact hbhi
  · have : post.nonce = pre.nonce + (1 - env.loc sel.NOOP) := by
      rw [← hsaN, ← hsbN]; exact hnon
    rw [this, hNoop]; ring
  · have h4 : env.loc (saCol (state.FIELD_BASE + 4)) = post.fields ⟨4, by decide⟩ := hsaF ⟨4, by decide⟩
    have hroot' : env.loc (saCol (state.FIELD_BASE + 4)) = emptyRoot := hroot
    have hfe : post.fields (4 : Fin 8) = post.fields ⟨4, by decide⟩ := by
      congr 1
    rw [hfe, ← h4]; exact hroot'
  · intro i hi4
    have hmem : i.val ∈ ([0, 1, 2, 3, 5, 6, 7] : List Nat) := by
      have := i.isLt; fin_cases i <;> first | (exact absurd rfl hi4) | decide
    have := hfld i.val hmem
    rw [← hsaF i, ← hsbF i]; exact this
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres

/-- **`queueAllocateDescriptor_full_sound`** — satisfying the WHOLE runnable descriptor (gates +
transitions + boundaries + hash sites), under the `RowEncodesAlloc` decoding, forces the structured
per-cell `CellAllocSpec` (including the queue-root write) AND publishes the post-commit as
`PI[NEW_COMMIT]`. The queue root is folded into the commitment via site1 (it absorbs `fields[4]`). -/
theorem queueAllocateDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (p : AllocateParams) (emptyRoot : ℤ)
    (henc : RowEncodesAlloc env pre p emptyRoot post)
    (hsat : satisfiedVm hash (queueAllocateVmDescriptor emptyRoot) env true true) :
    CellAllocSpec pre p emptyRoot post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates' : ∀ c ∈ queueAllocateRowGates emptyRoot, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ (queueAllocateVmDescriptor emptyRoot).constraints := by
      unfold queueAllocateVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hc))
    have := hcs c hmem
    unfold queueAllocateRowGates gFieldPassNonRoot at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (queueAllocateVm_faithful env emptyRoot).mp hgates'
  refine ⟨intent_to_cellAllocSpec env pre post p emptyRoot henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ (queueAllocateVmDescriptor emptyRoot).constraints := by
      unfold queueAllocateVmDescriptor
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

/-! ## §7 — The anti-ghost commitment tooth (REUSED — hash sites identical to transfer; site1 absorbs
`fields[4]`, so the queue root is part of the bound state-block). -/

/-- **`queueAllocateDescriptor_commit_binds_state`** — two descriptor-satisfying allocate rows publishing
the SAME `NEW_COMMIT` (under `Poseidon2SpongeCR`) have identical absorbed state-block columns — INCLUDING
`saCol fields[4]` (the queue root, absorbed by site1). So a prover cannot keep `NEW_COMMIT` while
tampering the queue root: the side-table-root binding the STAGE-3 amplification delivers. -/
theorem queueAllocateDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (emptyRoot : ℤ) (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash (queueAllocateVmDescriptor emptyRoot) e₁ true true)
    (hsat₂ : satisfiedVm hash (queueAllocateVmDescriptor emptyRoot) e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ transferHashSites := hsat₁.2.1
  have hs₂ : siteHoldsAll hash e₂ transferHashSites := hsat₂.2.1
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash (queueAllocateVmDescriptor emptyRoot) e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ (queueAllocateVmDescriptor emptyRoot).constraints := by
        unfold queueAllocateVmDescriptor
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

/-! ## §8 — CONNECTOR to universe-A: the IR-supportable freeze legs agree; the divergences are reported.

`QueueAllocateSpec` PREPENDS a fresh `QueueRecord` onto `queues` and pins `st'.kernel.bal = st.kernel.bal`
(balance-NEUTRAL in universe A). The RUNTIME instead (a) DEBITS the allocation fee and (b) models the
`queues` prepend as the `fields[4]` queue-root advance. We connect the two genuine agreements:

  * the `queues` PREPEND ⇄ the queue-root write: universe A's `st'.kernel.queues = freshQueue :: …`
    realizes a queue-root TRANSITION; the descriptor binds that transition at `fields[4]` (the runtime
    carrier) and the commitment folds it in (site1). The exact accumulator digest equality is the
    runtime's `hash_2_to_1` convention (a hash-realization detail), reported as the queue-root carrier.
  * the BALANCE: universe A is neutral; the runtime debits `cap·cost`. We report this
    runtime-fee-vs-univA-neutral divergence exactly as the notes keystone does — they reconcile only at
    `cap·cost = 0`. -/

open Dregg2.Circuit.Spec.QueueFifoCore
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

/-- **`unify_allocate_balFrozen_univA`** — universe A's `QueueAllocateSpec` is balance-NEUTRAL: across a
committed allocate, the projected `(c, asset)` ledger entry is FROZEN. So the descriptor's runtime
fee-debit AGREES with universe A's frozen ledger EXACTLY at `cap·cost = 0` (the reconciliation point);
for a non-zero fee the runtime row and universe A genuinely DIVERGE — reported, not papered. -/
theorem unify_allocate_balFrozen_univA (st : RecChainedState) (id : Nat) (actor cell : CellId)
    (cap : Nat) (st' : RecChainedState) (c : CellId) (asset : AssetId)
    (hspec : QueueAllocateSpec st id actor cell cap st') :
    (cellProjBal st'.kernel.bal c asset).balLo = (cellProjBal st.kernel.bal c asset).balLo := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hbal, _⟩ := hspec
  show st'.kernel.bal c asset = st.kernel.bal c asset
  rw [hbal]

/-- **`allocate_runtime_vs_univA_reconcile`** — the runtime fee-debit `CellAllocSpec.balLo` and universe
A's frozen ledger entry reconcile EXACTLY when the fee is zero (`p.capacity * p.cost = 0`). The honest
gap statement (the cutover differential's `runtime_debit_vs_univA_neutral` analog). -/
theorem allocate_runtime_vs_univA_reconcile (pre p emptyRoot post)
    (hcell : CellAllocSpec pre p emptyRoot post) (hzero : p.capacity * p.cost = 0) :
    post.balLo = pre.balLo := by
  obtain ⟨hbal, _⟩ := hcell
  rw [hbal, hzero, sub_zero]

/-! ## §9 — NON-VACUITY: a concrete reconciled row realizes the intent; tampers are rejected. -/

/-- A concrete allocate row (empty-queue root = 555): `bal_lo 100 → 88` (fee cap=3·cost=4=12),
nonce 7 → 8 (TICK, `s_noop = 0`), `fields[4] 0 → 555` (queue root), rest frozen. -/
def goodAllocRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_QUEUE_ALLOCATE then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 88
    else if v = sbCol state.NONCE then 7
    else if v = saCol state.NONCE then 8
    else if v = prmCol param.QUEUE_CAPACITY then 3
    else if v = prmCol param.QUEUE_COST_PER_SLOT then 4
    else if v = saCol QUEUE_ROOT_FIELD then 555
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `goodAllocRow` REALIZES the reconciled allocate intent (root = 555). -/
theorem goodAllocRow_realizes_intent : QueueAllocateRowIntent goodAllocRow 555 := by
  unfold QueueAllocateRowIntent goodAllocRow QUEUE_ROOT_FIELD
  simp only [sbCol, saCol, prmCol, SEL_QUEUE_ALLOCATE, sel.NOOP, STATE_BEFORE_BASE, STATE_AFTER_BASE,
    PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE, param.QUEUE_CAPACITY, param.QUEUE_COST_PER_SLOT]
  refine ⟨by norm_num, rfl, by norm_num, rfl, rfl, by norm_num, ?_⟩
  intro i hi
  fin_cases hi <;> norm_num

/-- A FORGED allocate row: `goodAllocRow` with the queue root tampered to `999` (an attacker forging the
prepended queue record). -/
def badRootRow : VmRowEnv where
  loc := fun v => if v = saCol QUEUE_ROOT_FIELD then 999 else goodAllocRow.loc v
  nxt := goodAllocRow.nxt
  pub := goodAllocRow.pub

/-- **NON-VACUITY (witness FALSE / concrete queue-root anti-ghost).** `badRootRow`'s queue root is
tampered, so the `gQueueRootBind` gate REJECTS it — a concrete UNSAT over the now-BOUND side-table root. -/
theorem badRootRow_rejected :
    ¬ (VmConstraint.gate (gQueueRootBind 555)).holdsVm badRootRow false false := by
  apply queueAllocateVm_rejects_wrong_queue_root
  simp only [badRootRow, goodAllocRow, saCol, QUEUE_ROOT_FIELD, STATE_AFTER_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.FIELD_BASE]
  norm_num

/-! ## §10 — Axiom-hygiene pins. -/

#guard (queueAllocateVmDescriptor 0).constraints.length == 13 + 14 + 4 + 3
#guard (queueAllocateVmDescriptor 0).hashSites.length == 4
#guard (queueAllocateVmDescriptor 0).traceWidth == 186

#assert_axioms queueAllocateVm_faithful
#assert_axioms queueAllocateVm_rejects_wrong_output
#assert_axioms queueAllocateVm_rejects_wrong_queue_root
#assert_axioms queueAllocateVm_rejects_wrong_balance
#assert_axioms intent_to_cellAllocSpec
#assert_axioms queueAllocateDescriptor_full_sound
#assert_axioms queueAllocateDescriptor_commit_binds_state
#assert_axioms unify_allocate_balFrozen_univA
#assert_axioms allocate_runtime_vs_univA_reconcile
#assert_axioms goodAllocRow_realizes_intent
#assert_axioms badRootRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitQueueAllocate
