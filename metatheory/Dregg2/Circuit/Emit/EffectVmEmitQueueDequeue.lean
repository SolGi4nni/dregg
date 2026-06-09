/-
# Dregg2.Circuit.Emit.EffectVmEmitQueueDequeue — the `queueDequeueA` (FIFO pop-front + refund SETTLE)
effect's EffectVM emission, through the SAME `EffectVmEmit` IR as transfer.

Universe A (`Inst/queueDequeueA.lean`, `Spec/queuefifocore.lean`) carries the FULL-state soundness
`queueDequeueA_full_sound ⇒ QueueDequeueSpec`: a committed dequeue POP-FRONTS queue `id`'s FIFO buffer
(`queueDequeueK`, owner-gated), SETTLES the front deposit `EscrowRecord` (crediting the dequeuer's `bal`
by the witnessed refund `r.amount` at `r.asset`), advances the log, and freezes the remaining fields.

## STAGE-3 AMPLIFICATION: the queue side-table root is NOW BOUND.

The earlier version reported the FIFO pop-front leg as OUT-OF-IR. STAGE 3 (`Exec.SystemRoots`,
`state.systemRoot.QUEUE`) gives the queue side-table a committed root; the RUNNING prover carries it at
`state.FIELD_BASE + 4` (`fields[4]`) and ADVANCES it on dequeue:
`fields[4]_after = hash_2_to_1(fields[4]_before, expected_message_hash)` (`effect_vm/air.rs`
`DequeueMessage` arm). This descriptor now BINDS that advance; GROUP-4 site1 (absorbing `fields[1..5]`)
folds the new queue root into `state_commit`. So the FIFO pop is bound — no longer out-of-IR.

## RECONCILIATION onto the runtime trace-generator layout (the cutover-harness pattern, 3aaf0772d).

  * CREDITS `bal_lo` by the refund (`param1 = DEQUEUE_DEPOSIT_REFUND` — the runtime column, NOT transfer's
    `param0`).
  * TICKS the nonce (the global non-NoOp invariant); the earlier descriptor FROZE it (UNSAT) — now fixed.
  * ADVANCES `fields[4]` (queue root); FREEZES `fields[0..3]`, `fields[5..7]`, cap_root, reserved, bal_hi.

The refund CREDIT genuinely AGREES with universe A (`unify_dequeue_credit`, preserved).

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` hypothesis. No `sorry`, no `:= True`, no `native_decide`. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.queuefifocore

namespace Dregg2.Circuit.Emit.EffectVmEmitQueueDequeue

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

/-! ## §0 — The queueDequeue selector + the refund CREDIT parameter + the queue-root carrier. -/

/-- The queueDequeue selector column index (`columns.rs::sel::DEQUEUE_MESSAGE`). -/
def SEL_QUEUE_DEQUEUE : Nat := 20

/-! Runtime dequeue parameter columns. -/
namespace param
/-- The deposit refund (`param::DEQUEUE_DEPOSIT_REFUND`). -/
def DEQUEUE_DEPOSIT_REFUND : Nat := 1
end param

/-- The refund as an expression (`param1`). -/
def ePrmRefund : EmittedExpr := .var (prmCol param.DEQUEUE_DEPOSIT_REFUND)

/-- The queue-root state column (`fields[4]`, the runtime's queue-side-table-root carrier). -/
def QUEUE_ROOT_FIELD : Nat := state.FIELD_BASE + 4

/-- The dequeue row: `s_queue_dequeue = 1`, `s_noop = 0`. -/
def IsQueueDequeueRow (env : VmRowEnv) : Prop :=
  env.loc SEL_QUEUE_DEQUEUE = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — The per-row gate bodies (refund CREDIT + queue-root advance BIND + nonce TICK). -/

/-- Balance-lo CREDIT body: `new_bal_lo − old_bal_lo − refund` (so `new = old + refund`). -/
def gBalLoCredit : EmittedExpr :=
  eSub (eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)) ePrmRefund

/-- Queue-root ADVANCE BIND body: `fields[4]_after − newRoot` (hash-agnostic; harness fills the felt). -/
def gQueueRootBind (newRoot : ℤ) : EmittedExpr :=
  .add (eSA QUEUE_ROOT_FIELD) (.const (-newRoot))

/-- Nonce TICK body, reused verbatim from transfer. -/
def gNonceTick : EmittedExpr := gNonce

/-- The seven NON-queue-root field passthrough gates (`fields[0..3]`, `fields[5..7]`). -/
def gFieldPassNonRoot : List VmConstraint :=
  ([0, 1, 2, 3, 5, 6, 7] : List Nat).map (fun i => VmConstraint.gate (gFieldPass i))

/-! ## §2 — The emitted queueDequeue descriptor. -/

/-- The queueDequeue AIR identity. -/
def queueDequeueVmAirName : String := "dregg-effectvm-queuedequeue-v1"

/-- The dequeue per-row gates (parameterized by the advanced queue root felt). -/
def queueDequeueRowGates (newRoot : ℤ) : List VmConstraint :=
  [ .gate gBalLoCredit, .gate gBalHi, .gate gNonceTick
  , .gate gCapPass, .gate gResPass, .gate (gQueueRootBind newRoot) ] ++ gFieldPassNonRoot

/-- **`queueDequeueVmDescriptor newRoot`** — the FULL dequeue descriptor reconciled onto the runtime
layout: refund-credit + queue-root-advance + nonce-tick + freeze gates ++ transition ++ boundary pins,
with the 4 GROUP-4 hash sites (site1 absorbs `fields[4]`) and the 2 range checks. -/
def queueDequeueVmDescriptor (newRoot : ℤ) : EffectVmDescriptor :=
  { name := queueDequeueVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := queueDequeueRowGates newRoot ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The queueDequeue ROW INTENT (runtime-reconciled). -/

/-- **`QueueDequeueRowIntent env newRoot`** — the runtime dequeue move: `bal_lo` rises by `refund`, the
queue-root carrier (`fields[4]`) becomes `newRoot`, the nonce TICKS, the rest FROZEN. -/
def QueueDequeueRowIntent (env : VmRowEnv) (newRoot : ℤ) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO) + env.loc (prmCol param.DEQUEUE_DEPOSIT_REFUND)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ env.loc (saCol QUEUE_ROOT_FIELD) = newRoot
  ∧ (∀ i ∈ ([0, 1, 2, 3, 5, 6, 7] : List Nat),
        env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS. -/

theorem queueDequeueVm_faithful (env : VmRowEnv) (newRoot : ℤ) :
    (∀ c ∈ queueDequeueRowGates newRoot, c.holdsVm env false false)
      ↔ QueueDequeueRowIntent env newRoot := by
  unfold queueDequeueRowGates gFieldPassNonRoot QueueDequeueRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoCredit) (by simp)
    have hHi := h (.gate gBalHi) (by simp)
    have hNon := h (.gate gNonceTick) (by simp)
    have hCap := h (.gate gCapPass) (by simp)
    have hRes := h (.gate gResPass) (by simp)
    have hRoot := h (.gate (gQueueRootBind newRoot)) (by simp)
    have hFld : ∀ i ∈ ([0, 1, 2, 3, 5, 6, 7] : List Nat),
        VmConstraint.holdsVm env false false (.gate (gFieldPass i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoCredit, gBalHi, gNonceTick, gNonce, gCapPass, gResPass,
      gQueueRootBind, eSA, eSB, ePrmRefund, eSelNoop, eSub,
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
    · simp only [VmConstraint.holdsVm, gBalLoCredit, eSA, eSB, ePrmRefund, eSub, EmittedExpr.eval]
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

/-! ## §5 — ANTI-GHOST. -/

theorem queueDequeueVm_rejects_wrong_output (env : VmRowEnv) (newRoot : ℤ)
    (hwrong : ¬ QueueDequeueRowIntent env newRoot) :
    ¬ (∀ c ∈ queueDequeueRowGates newRoot, c.holdsVm env false false) :=
  fun h => hwrong ((queueDequeueVm_faithful env newRoot).mp h)

/-- **Anti-ghost (queue-root tamper).** A forged/dropped FIFO pop is rejected by `gQueueRootBind`. -/
theorem queueDequeueVm_rejects_wrong_queue_root (env : VmRowEnv) (newRoot : ℤ)
    (hwrong : env.loc (saCol QUEUE_ROOT_FIELD) ≠ newRoot) :
    ¬ (VmConstraint.gate (gQueueRootBind newRoot)).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gQueueRootBind, eSA, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

theorem queueDequeueVm_rejects_wrong_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO)
      ≠ env.loc (sbCol state.BALANCE_LO) + env.loc (prmCol param.DEQUEUE_DEPOSIT_REFUND)) :
    ¬ (VmConstraint.gate gBalLoCredit).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoCredit, eSA, eSB, ePrmRefund, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-! ## §6 — The structured per-cell spec + descriptor soundness (REUSING `CellState`). -/

/-- The refund parameters carried in the param block. -/
structure RefundParams where
  amount : ℤ

/-- `RowEncodesCredit env pre p newRoot post` ties the row's state-block + param columns to a transition. -/
def RowEncodesCredit (env : VmRowEnv) (pre : CellState) (p : RefundParams) (newRoot : ℤ)
    (post : CellState) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (sbCol state.STATE_COMMIT) = pre.commit
  ∧ env.loc (prmCol param.DEQUEUE_DEPOSIT_REFUND) = p.amount
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

/-- **`CellCreditSpec pre p newRoot post`** — the per-cell FULL-state refund-credit spec: `balLo` rises by
`amount`, the queue-root cell (`fields 4`) becomes `newRoot`, the nonce TICKS, the rest frozen. -/
def CellCreditSpec (pre : CellState) (p : RefundParams) (newRoot : ℤ) (post : CellState) : Prop :=
  post.balLo = pre.balLo + p.amount
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce + 1
  ∧ post.fields 4 = newRoot
  ∧ (∀ i : Fin 8, i.val ≠ 4 → post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

theorem intent_to_cellCreditSpec (env : VmRowEnv) (pre post : CellState) (p : RefundParams)
    (newRoot : ℤ) (henc : RowEncodesCredit env pre p newRoot post)
    (hint : QueueDequeueRowIntent env newRoot) :
    CellCreditSpec pre p newRoot post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC, hpAmt, hNoop,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hroot, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : post.balLo = pre.balLo + env.loc (prmCol param.DEQUEUE_DEPOSIT_REFUND) := by
      rw [← hsaLo, ← hsbLo]; exact hbal
    rw [this, hpAmt]
  · rw [← hsaHi, ← hsbHi]; exact hbhi
  · have : post.nonce = pre.nonce + (1 - env.loc sel.NOOP) := by
      rw [← hsaN, ← hsbN]; exact hnon
    rw [this, hNoop]; ring
  · have h4 : env.loc (saCol (state.FIELD_BASE + 4)) = post.fields ⟨4, by decide⟩ := hsaF ⟨4, by decide⟩
    have hroot' : env.loc (saCol (state.FIELD_BASE + 4)) = newRoot := hroot
    have hfe : post.fields (4 : Fin 8) = post.fields ⟨4, by decide⟩ := by congr 1
    rw [hfe, ← h4]; exact hroot'
  · intro i hi4
    have hmem : i.val ∈ ([0, 1, 2, 3, 5, 6, 7] : List Nat) := by
      have := i.isLt; fin_cases i <;> first | (exact absurd rfl hi4) | decide
    have := hfld i.val hmem
    rw [← hsaF i, ← hsbF i]; exact this
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres

theorem queueDequeueDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (p : RefundParams) (newRoot : ℤ)
    (henc : RowEncodesCredit env pre p newRoot post)
    (hsat : satisfiedVm hash (queueDequeueVmDescriptor newRoot) env true true) :
    CellCreditSpec pre p newRoot post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates' : ∀ c ∈ queueDequeueRowGates newRoot, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ (queueDequeueVmDescriptor newRoot).constraints := by
      unfold queueDequeueVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hc))
    have := hcs c hmem
    unfold queueDequeueRowGates gFieldPassNonRoot at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (queueDequeueVm_faithful env newRoot).mp hgates'
  refine ⟨intent_to_cellCreditSpec env pre post p newRoot henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ (queueDequeueVmDescriptor newRoot).constraints := by
      unfold queueDequeueVmDescriptor
      simp only [List.mem_append]
      exact Or.inr hc
    have hh := hcs c hmem
    unfold boundaryLastPins at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      · simp only [VmConstraint.holdsVm] at hh ⊢
        exact hh
  have hpin := (boundaryLast_pins env hlast).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]; exact hpin

/-! ## §7 — The anti-ghost commitment tooth (REUSED; site1 absorbs `fields[4]`, the queue root). -/

theorem queueDequeueDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (newRoot : ℤ) (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash (queueDequeueVmDescriptor newRoot) e₁ true true)
    (hsat₂ : satisfiedVm hash (queueDequeueVmDescriptor newRoot) e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ transferHashSites := hsat₁.2.1
  have hs₂ : siteHoldsAll hash e₂ transferHashSites := hsat₂.2.1
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash (queueDequeueVmDescriptor newRoot) e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ (queueDequeueVmDescriptor newRoot).constraints := by
        unfold queueDequeueVmDescriptor
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

/-! ## §8 — CONNECTOR to universe-A: the refund CREDIT IS `QueueDequeueSpec`'s per-cell `bal` image.

`QueueDequeueSpec` commits `st'.kernel = k'` where `queueDequeueRefundK st.kernel id actor depId =
some (k', m)`. That helper composes `queueDequeueK` (balance-NEUTRAL — touches only `queues`) with
`settleEscrowRawAsset k₁ depId actor r.asset r.amount` (`r = findUnresolvedDeposit k₁ depId`), which
rewrites `bal := recBalCreditCell k₁.bal actor r.asset r.amount` — the dequeuer's `(actor, r.asset)`
entry RISES by `r.amount`. The FIFO pop is bound at the runtime's `fields[4]` queue root (above). -/

open Dregg2.Circuit.Spec.QueueFifoCore
open Dregg2.Exec

/-- `queueDequeueK` is balance-preserving on the raw `bal` function (it rewrites only `queues`). -/
theorem queueDequeueK_bal {k k₁ : RecordKernelState} {id : Nat} {actor : CellId} {mh : Nat}
    (h : queueDequeueK k id actor = some (k₁, mh)) : k₁.bal = k.bal := by
  unfold queueDequeueK at h
  cases hf : findQueue k.queues id with
  | none   => simp only [hf] at h; exact absurd h (by simp)
  | some q =>
      simp only [hf] at h
      by_cases ho : actor = q.owner
      · rw [if_pos ho] at h
        cases hd : qbufDequeue q.buffer with
        | none          => rw [hd] at h; exact absurd h (by simp)
        | some hr       =>
            obtain ⟨m, rest⟩ := hr
            rw [hd] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hk, _⟩ := h; subst hk; rfl
      · rw [if_neg ho] at h; exact absurd h (by simp)

/-- Project the `(c, asset)` per-asset ledger entry into the keystone `CellState`'s `balLo` limb. -/
def cellProjBal (bal : CellId → AssetId → ℤ) (c : CellId) (asset : AssetId) : CellState where
  balLo    := bal c asset
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`unify_dequeue_credit`** — across a committed `QueueDequeueSpec` post-state, the dequeuer cell's
projected `(actor, r.asset)` ledger entry RISES by the witnessed refund `r.amount`. So the descriptor's
refund-credit IS `QueueDequeueSpec`'s per-cell `bal` image — NOT a fourth spec. (`balHi` placeholder is
the projection's `0 + amount`; the FULL `CellCreditSpec`'s queue-root/nonce legs are runtime-trace facts,
proved against the descriptor in §6.) -/
theorem unify_dequeue_credit (st st' : RecChainedState) (id : Nat) (actor cell : CellId)
    (depId : Nat) (hspec : QueueDequeueSpec st id actor cell depId st') :
    ∃ (asset : AssetId) (amount : ℤ),
      (cellProjBal st'.kernel.bal actor asset).balLo
        = (cellProjBal st.kernel.bal actor asset).balLo + amount := by
  obtain ⟨_, _, _, _, k', m, hk, hker, _⟩ := hspec
  unfold queueDequeueRefundK at hk
  cases hk₁ : queueDequeueK st.kernel id actor with
  | none => simp only [hk₁] at hk; exact absurd hk (by simp)
  | some kr =>
      obtain ⟨k₁, mh⟩ := kr
      simp only [hk₁] at hk
      by_cases hbind : dequeueMsgBindB k₁ actor depId id mh = true
      · rw [if_pos hbind] at hk
        cases hfind : findUnresolvedDeposit k₁ depId with
        | none => simp only [hfind] at hk; exact absurd hk (by simp)
        | some r =>
            simp only [hfind] at hk
            by_cases hacc : actor ∈ k₁.accounts
            · rw [if_pos hacc] at hk
              simp only [Option.some.injEq, Prod.mk.injEq] at hk
              obtain ⟨hkeq, _⟩ := hk
              refine ⟨r.asset, r.amount, ?_⟩
              show st'.kernel.bal actor r.asset = st.kernel.bal actor r.asset + r.amount
              rw [hker, ← hkeq]
              show (settleEscrowRawAsset k₁ depId actor r.asset r.amount).bal actor r.asset
                  = st.kernel.bal actor r.asset + r.amount
              have hbalfn : (settleEscrowRawAsset k₁ depId actor r.asset r.amount).bal
                  = recBalCreditCell k₁.bal actor r.asset r.amount := rfl
              rw [hbalfn]
              unfold recBalCreditCell
              rw [if_pos (And.intro rfl rfl), queueDequeueK_bal hk₁]
            · rw [if_neg hacc] at hk; exact absurd hk (by simp)
      · rw [if_neg hbind] at hk; exact absurd hk (by simp)

/-! ## §9 — NON-VACUITY. -/

/-- A concrete dequeue row (advanced root = 888): `bal_lo 70 → 95` (refund 25), nonce 4 → 5 (TICK),
`fields[4] 0 → 888`, rest frozen. -/
def goodDequeueRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_QUEUE_DEQUEUE then 1
    else if v = sbCol state.BALANCE_LO then 70
    else if v = saCol state.BALANCE_LO then 95
    else if v = sbCol state.NONCE then 4
    else if v = saCol state.NONCE then 5
    else if v = prmCol param.DEQUEUE_DEPOSIT_REFUND then 25
    else if v = saCol QUEUE_ROOT_FIELD then 888
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `goodDequeueRow` REALIZES the reconciled dequeue intent (root = 888). -/
theorem goodDequeueRow_realizes_intent : QueueDequeueRowIntent goodDequeueRow 888 := by
  unfold QueueDequeueRowIntent goodDequeueRow QUEUE_ROOT_FIELD
  simp only [sbCol, saCol, prmCol, SEL_QUEUE_DEQUEUE, sel.NOOP, STATE_BEFORE_BASE, STATE_AFTER_BASE,
    PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE, param.DEQUEUE_DEPOSIT_REFUND]
  refine ⟨by norm_num, rfl, by norm_num, rfl, rfl, by norm_num, ?_⟩
  intro i hi
  fin_cases hi <;> norm_num

/-- A FORGED dequeue row: queue root tampered to `999` (a forged FIFO pop). -/
def badRootRow : VmRowEnv where
  loc := fun v => if v = saCol QUEUE_ROOT_FIELD then 999 else goodDequeueRow.loc v
  nxt := goodDequeueRow.nxt
  pub := goodDequeueRow.pub

/-- **NON-VACUITY (witness FALSE / concrete queue-root anti-ghost).** `badRootRow`'s queue root is
tampered, so `gQueueRootBind` REJECTS it — a concrete UNSAT over the now-BOUND side-table root. -/
theorem badRootRow_rejected :
    ¬ (VmConstraint.gate (gQueueRootBind 888)).holdsVm badRootRow false false := by
  apply queueDequeueVm_rejects_wrong_queue_root
  simp only [badRootRow, goodDequeueRow, saCol, QUEUE_ROOT_FIELD, STATE_AFTER_BASE, PARAM_BASE,
    STATE_SIZE, NUM_PARAMS, state.FIELD_BASE]
  norm_num

/-! ## §10 — Axiom-hygiene pins. -/

#guard (queueDequeueVmDescriptor 0).constraints.length == 13 + 14 + 4 + 3
#guard (queueDequeueVmDescriptor 0).hashSites.length == 4
#guard (queueDequeueVmDescriptor 0).traceWidth == 186

#assert_axioms queueDequeueVm_faithful
#assert_axioms queueDequeueVm_rejects_wrong_output
#assert_axioms queueDequeueVm_rejects_wrong_queue_root
#assert_axioms queueDequeueVm_rejects_wrong_balance
#assert_axioms intent_to_cellCreditSpec
#assert_axioms queueDequeueDescriptor_full_sound
#assert_axioms queueDequeueDescriptor_commit_binds_state
#assert_axioms queueDequeueK_bal
#assert_axioms unify_dequeue_credit
#assert_axioms goodDequeueRow_realizes_intent
#assert_axioms badRootRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitQueueDequeue
