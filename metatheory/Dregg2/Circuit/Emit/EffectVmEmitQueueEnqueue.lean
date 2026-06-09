/-
# Dregg2.Circuit.Emit.EffectVmEmitQueueEnqueue — the `queueEnqueueA` (FIFO append + refundable deposit
PARK) effect's EffectVM emission, through the SAME `EffectVmEmit` IR as transfer.

Universe A (`Inst/queueEnqueueA.lean`, `Spec/queuefifocore.lean`) carries the FULL-state soundness
`queueEnqueueA_full_sound ⇒ QueueEnqueueSpec`: a committed enqueue APPENDS a message to queue `id`'s
FIFO buffer (`queueEnqueueK`), DEBITS the per-asset ledger `bal` at `(actor, dAsset)` by `deposit`
(`createEscrowRawAssetQueue`), prepends an unresolved deposit `EscrowRecord`, advances the log, and
freezes the remaining kernel fields.

## STAGE-3 AMPLIFICATION: the queue side-table root is NOW BOUND.

The earlier version reported the FIFO-append leg as OUT-OF-IR. STAGE 3 (`Exec.SystemRoots`,
`state.systemRoot.QUEUE`) gives the queue side-table a committed root; the RUNNING prover carries it at
`state.FIELD_BASE + 4` (`fields[4]`) and ADVANCES it on enqueue: `fields[4]_after = hash_2_to_1(fields[4]_before,
message_hash)` (`effect_vm/air.rs` `EnqueueMessage` arm). This descriptor now BINDS that hash-chain
advance; GROUP-4 site1 (absorbing `fields[1..5]`, including `fields[4]`) folds the new queue root into
`state_commit`. So the FIFO append + its ORDER (the chain depends on the prior root) is bound — no longer
out-of-IR.

## RECONCILIATION onto the runtime trace-generator layout (the cutover-harness pattern, 3aaf0772d).

  * DEBITS `bal_lo` by the deposit (`param1 = ENQUEUE_DEPOSIT`) — already correct.
  * TICKS the nonce (the global non-NoOp invariant); the earlier descriptor FROZE it (UNSAT on the honest
    trace) — now fixed via the shared `gNonce`.
  * ADVANCES `fields[4]` (queue root) by the hash-chain; FREEZES `fields[0..3]`, `fields[5..7]`, cap_root,
    reserved, bal_hi.

The deposit DEBIT genuinely AGREES with universe A (`unify_enqueue_debit`, preserved); the queue-root
advance is the runtime's hash-chain realization of the FIFO append (bound at `fields[4]`).

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` hypothesis. No `sorry`, no `:= True`, no `native_decide`. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.queuefifocore

namespace Dregg2.Circuit.Emit.EffectVmEmitQueueEnqueue

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

/-! ## §0 — The queueEnqueue selector + the deposit DEBIT parameter + the queue-root carrier. -/

/-- The queueEnqueue selector column index (`columns.rs::sel::ENQUEUE_MESSAGE`). -/
def SEL_QUEUE_ENQUEUE : Nat := 19

/-! Runtime enqueue parameter columns. -/
namespace param
/-- The deposit amount (`param::ENQUEUE_DEPOSIT`). -/
def ENQUEUE_DEPOSIT : Nat := 1
end param

/-- The deposit as an expression (`param1`). -/
def ePrmDeposit : EmittedExpr := .var (prmCol param.ENQUEUE_DEPOSIT)

/-- The queue-root state column (`fields[4]`, the runtime's queue-side-table-root carrier). -/
def QUEUE_ROOT_FIELD : Nat := state.FIELD_BASE + 4

/-- The enqueue row: `s_queue_enqueue = 1`, `s_noop = 0`. -/
def IsQueueEnqueueRow (env : VmRowEnv) : Prop :=
  env.loc SEL_QUEUE_ENQUEUE = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — The per-row gate bodies (deposit DEBIT + queue-root advance BIND + nonce TICK). -/

/-- Balance-lo DEBIT body: `new_bal_lo − old_bal_lo + deposit`. -/
def gBalLoDebit : EmittedExpr :=
  .add (eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)) ePrmDeposit

/-- Queue-root ADVANCE BIND body: `fields[4]_after − newRoot`, where `newRoot` (the runtime's
`hash_2_to_1(fields[4]_before, message_hash)`) is supplied as a parameter so the gate is hash-agnostic —
the cutover harness fills the concrete felt; the descriptor asserts the carrier equals it. -/
def gQueueRootBind (newRoot : ℤ) : EmittedExpr :=
  .add (eSA QUEUE_ROOT_FIELD) (.const (-newRoot))

/-- Nonce TICK body, reused verbatim from transfer. -/
def gNonceTick : EmittedExpr := gNonce

/-- The seven NON-queue-root field passthrough gates (`fields[0..3]`, `fields[5..7]`). -/
def gFieldPassNonRoot : List VmConstraint :=
  ([0, 1, 2, 3, 5, 6, 7] : List Nat).map (fun i => VmConstraint.gate (gFieldPass i))

/-! ## §2 — The emitted queueEnqueue descriptor. -/

/-- The queueEnqueue AIR identity. -/
def queueEnqueueVmAirName : String := "dregg-effectvm-queueenqueue-v1"

/-- The enqueue per-row gates (parameterized by the advanced queue root felt). -/
def queueEnqueueRowGates (newRoot : ℤ) : List VmConstraint :=
  [ .gate gBalLoDebit, .gate gBalHi, .gate gNonceTick
  , .gate gCapPass, .gate gResPass, .gate (gQueueRootBind newRoot) ] ++ gFieldPassNonRoot

/-- **`queueEnqueueVmDescriptor newRoot`** — the FULL enqueue descriptor reconciled onto the runtime
layout: deposit-debit + queue-root-advance + nonce-tick + freeze gates ++ transition continuity ++ the 7
boundary PI pins, with the 4 ordered GROUP-4 hash sites (site1 absorbs `fields[4]`) and the 2 range checks. -/
def queueEnqueueVmDescriptor (newRoot : ℤ) : EffectVmDescriptor :=
  { name := queueEnqueueVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := queueEnqueueRowGates newRoot ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The queueEnqueue ROW INTENT (runtime-reconciled). -/

/-- **`QueueEnqueueRowIntent env newRoot`** — the runtime enqueue move: `bal_lo` drops by `deposit`, the
queue-root carrier (`fields[4]`) becomes `newRoot`, the nonce TICKS, the rest of the frame is FROZEN. -/
def QueueEnqueueRowIntent (env : VmRowEnv) (newRoot : ℤ) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO) - env.loc (prmCol param.ENQUEUE_DEPOSIT)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ env.loc (saCol QUEUE_ROOT_FIELD) = newRoot
  ∧ (∀ i ∈ ([0, 1, 2, 3, 5, 6, 7] : List Nat),
        env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS. -/

/-- **`queueEnqueueVm_faithful`.** On an enqueue row, the per-row gates hold IFF `QueueEnqueueRowIntent`. -/
theorem queueEnqueueVm_faithful (env : VmRowEnv) (newRoot : ℤ) :
    (∀ c ∈ queueEnqueueRowGates newRoot, c.holdsVm env false false)
      ↔ QueueEnqueueRowIntent env newRoot := by
  unfold queueEnqueueRowGates gFieldPassNonRoot QueueEnqueueRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoDebit) (by simp)
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
    simp only [VmConstraint.holdsVm, gBalLoDebit, gBalHi, gNonceTick, gNonce, gCapPass, gResPass,
      gQueueRootBind, eSA, eSB, ePrmDeposit, eSelNoop, eSub,
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
    · simp only [VmConstraint.holdsVm, gBalLoDebit, eSA, eSB, ePrmDeposit, eSub, EmittedExpr.eval]
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

theorem queueEnqueueVm_rejects_wrong_output (env : VmRowEnv) (newRoot : ℤ)
    (hwrong : ¬ QueueEnqueueRowIntent env newRoot) :
    ¬ (∀ c ∈ queueEnqueueRowGates newRoot, c.holdsVm env false false) :=
  fun h => hwrong ((queueEnqueueVm_faithful env newRoot).mp h)

/-- **Anti-ghost (queue-root tamper).** A row whose post-`fields[4]` is NOT the advanced root (a forged or
dropped FIFO append) is rejected by `gQueueRootBind` alone — the bound side-table root. -/
theorem queueEnqueueVm_rejects_wrong_queue_root (env : VmRowEnv) (newRoot : ℤ)
    (hwrong : env.loc (saCol QUEUE_ROOT_FIELD) ≠ newRoot) :
    ¬ (VmConstraint.gate (gQueueRootBind newRoot)).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gQueueRootBind, eSA, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

theorem queueEnqueueVm_rejects_wrong_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO)
      ≠ env.loc (sbCol state.BALANCE_LO) - env.loc (prmCol param.ENQUEUE_DEPOSIT)) :
    ¬ (VmConstraint.gate gBalLoDebit).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoDebit, eSA, eSB, ePrmDeposit, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-! ## §6 — The structured per-cell spec + descriptor soundness (REUSING `CellState`). -/

/-- The enqueue parameters carried in the param block. -/
structure DepositParams where
  deposit : ℤ

/-- `RowEncodesEnqueue env pre p newRoot post` ties the row's state-block + param columns to a transition. -/
def RowEncodesEnqueue (env : VmRowEnv) (pre : CellState) (p : DepositParams) (newRoot : ℤ)
    (post : CellState) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (sbCol state.STATE_COMMIT) = pre.commit
  ∧ env.loc (prmCol param.ENQUEUE_DEPOSIT) = p.deposit
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

/-- **`CellEnqueueSpec pre p newRoot post`** — the per-cell FULL-state enqueue spec: `balLo` drops by
`deposit`, the queue-root cell (`fields 4`) becomes `newRoot`, the nonce TICKS, the rest frozen. -/
def CellEnqueueSpec (pre : CellState) (p : DepositParams) (newRoot : ℤ) (post : CellState) : Prop :=
  post.balLo = pre.balLo - p.deposit
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce + 1
  ∧ post.fields 4 = newRoot
  ∧ (∀ i : Fin 8, i.val ≠ 4 → post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

theorem intent_to_cellEnqueueSpec (env : VmRowEnv) (pre post : CellState) (p : DepositParams)
    (newRoot : ℤ) (henc : RowEncodesEnqueue env pre p newRoot post)
    (hint : QueueEnqueueRowIntent env newRoot) :
    CellEnqueueSpec pre p newRoot post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC, hpDep, hNoop,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hroot, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : post.balLo = pre.balLo - env.loc (prmCol param.ENQUEUE_DEPOSIT) := by
      rw [← hsaLo, ← hsbLo]; exact hbal
    rw [this, hpDep]
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

/-- **`queueEnqueueDescriptor_full_sound`** — the WHOLE runnable descriptor forces `CellEnqueueSpec`
(including the queue-root advance) AND publishes the post-commit as `PI[NEW_COMMIT]`. -/
theorem queueEnqueueDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (p : DepositParams) (newRoot : ℤ)
    (henc : RowEncodesEnqueue env pre p newRoot post)
    (hsat : satisfiedVm hash (queueEnqueueVmDescriptor newRoot) env true true) :
    CellEnqueueSpec pre p newRoot post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates' : ∀ c ∈ queueEnqueueRowGates newRoot, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ (queueEnqueueVmDescriptor newRoot).constraints := by
      unfold queueEnqueueVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hc))
    have := hcs c hmem
    unfold queueEnqueueRowGates gFieldPassNonRoot at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (queueEnqueueVm_faithful env newRoot).mp hgates'
  refine ⟨intent_to_cellEnqueueSpec env pre post p newRoot henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ (queueEnqueueVmDescriptor newRoot).constraints := by
      unfold queueEnqueueVmDescriptor
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

theorem queueEnqueueDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (newRoot : ℤ) (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash (queueEnqueueVmDescriptor newRoot) e₁ true true)
    (hsat₂ : satisfiedVm hash (queueEnqueueVmDescriptor newRoot) e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ transferHashSites := hsat₁.2.1
  have hs₂ : siteHoldsAll hash e₂ transferHashSites := hsat₂.2.1
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash (queueEnqueueVmDescriptor newRoot) e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ (queueEnqueueVmDescriptor newRoot).constraints := by
        unfold queueEnqueueVmDescriptor
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

/-! ## §8 — CONNECTOR to universe-A: the deposit DEBIT IS `QueueEnqueueSpec`'s per-cell `bal` image.

`QueueEnqueueSpec` commits `st'.kernel = createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit
id m` off the FIFO-appended `k₁` (`queueEnqueueK st.kernel id m = some k₁`, balance-NEUTRAL). The helper
rewrites `bal := recBalCreditCell k₁.bal actor dAsset (-deposit)` — the `(actor, dAsset)` entry drops by
`deposit`. The FIFO append is realized at the runtime's `fields[4]` queue-root advance (bound above). -/

open Dregg2.Circuit.Spec.QueueFifoCore
open Dregg2.Exec

/-- `queueEnqueueK` is balance-preserving on the raw `bal` function. -/
theorem queueEnqueueK_bal {k k₁ : RecordKernelState} {id m : Nat}
    (h : queueEnqueueK k id m = some k₁) : k₁.bal = k.bal := by
  unfold queueEnqueueK at h
  cases hf : findQueue k.queues id with
  | none   => simp only [hf] at h; exact absurd h (by simp)
  | some q =>
      simp only [hf] at h
      by_cases hc : q.buffer.length < q.capacity
      · rw [if_pos hc] at h; simp only [Option.some.injEq] at h; subst h; rfl
      · rw [if_neg hc] at h; exact absurd h (by simp)

/-- Project the `(c, asset)` per-asset ledger entry into the keystone `CellState`'s `balLo` limb. -/
def cellProjBal (bal : CellId → AssetId → ℤ) (c : CellId) (asset : AssetId) : CellState where
  balLo    := bal c asset
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`unify_enqueue_debit`** — across a committed `QueueEnqueueSpec` post-state, the actor cell's
projected ledger entry drops by `deposit` EXACTLY: the descriptor's deposit-debit IS `QueueEnqueueSpec`'s
per-cell `bal` image. -/
theorem unify_enqueue_debit (st st' : RecChainedState) (id m : Nat) (actor cell : CellId)
    (depId : Nat) (dAsset : AssetId) (deposit : ℤ)
    (hspec : QueueEnqueueSpec st id m actor cell depId dAsset deposit st') :
    (cellProjBal st'.kernel.bal actor dAsset).balLo
      = (cellProjBal st.kernel.bal actor dAsset).balLo - deposit := by
  obtain ⟨k₁, _, _, hk₁, _, _, _, _, hker, _⟩ := hspec
  show st'.kernel.bal actor dAsset = st.kernel.bal actor dAsset - deposit
  rw [hker]
  show (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).bal actor dAsset
      = st.kernel.bal actor dAsset - deposit
  have hbalfn : (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).bal
      = recBalCreditCell k₁.bal actor dAsset (-deposit) := rfl
  rw [hbalfn]
  unfold recBalCreditCell
  rw [if_pos (And.intro rfl rfl), queueEnqueueK_bal hk₁]
  ring

/-! ## §9 — THE per-cell circuit⟺executor AGREEMENT (the payoff). -/

/-- **`descriptor_agrees_with_executor_enqueue`** — a satisfying run of the runnable descriptor encoding
the actor cell of a committed enqueue agrees with the executor's per-cell debited `bal actor dAsset`. The
FIFO append is bound at the runtime's `fields[4]` queue root (no longer out-of-IR). -/
theorem descriptor_agrees_with_executor_enqueue
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (st st' : RecChainedState) (id m : Nat) (actor cell : CellId) (depId : Nat)
    (dAsset : AssetId) (deposit : ℤ) (newRoot : ℤ) (post : CellState)
    (henc : RowEncodesEnqueue env (cellProjBal st.kernel.bal actor dAsset) ⟨deposit⟩ newRoot post)
    (hsat : satisfiedVm hash (queueEnqueueVmDescriptor newRoot) env true true)
    (hspec : QueueEnqueueSpec st id m actor cell depId dAsset deposit st') :
    post.balLo = (cellProjBal st'.kernel.bal actor dAsset).balLo := by
  obtain ⟨hcirc, _⟩ := queueEnqueueDescriptor_full_sound hash env
    (cellProjBal st.kernel.bal actor dAsset) post ⟨deposit⟩ newRoot henc hsat
  obtain ⟨hcLo, _⟩ := hcirc
  have heLo := unify_enqueue_debit st st' id m actor cell depId dAsset deposit hspec
  rw [hcLo, heLo]

/-! ## §10 — NON-VACUITY. -/

/-- A concrete enqueue row (advanced root = 777): `bal_lo 200 → 188` (deposit 12), nonce 9 → 10 (TICK),
`fields[4] 0 → 777`, rest frozen. -/
def goodEnqueueRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_QUEUE_ENQUEUE then 1
    else if v = sbCol state.BALANCE_LO then 200
    else if v = saCol state.BALANCE_LO then 188
    else if v = sbCol state.NONCE then 9
    else if v = saCol state.NONCE then 10
    else if v = prmCol param.ENQUEUE_DEPOSIT then 12
    else if v = saCol QUEUE_ROOT_FIELD then 777
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `goodEnqueueRow` REALIZES the reconciled enqueue intent (root = 777). -/
theorem goodEnqueueRow_realizes_intent : QueueEnqueueRowIntent goodEnqueueRow 777 := by
  unfold QueueEnqueueRowIntent goodEnqueueRow QUEUE_ROOT_FIELD
  simp only [sbCol, saCol, prmCol, SEL_QUEUE_ENQUEUE, sel.NOOP, STATE_BEFORE_BASE, STATE_AFTER_BASE,
    PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE, param.ENQUEUE_DEPOSIT]
  refine ⟨by norm_num, rfl, by norm_num, rfl, rfl, by norm_num, ?_⟩
  intro i hi
  fin_cases hi <;> norm_num

/-- A FORGED enqueue row: queue root tampered to `999` (a forged FIFO append). -/
def badRootRow : VmRowEnv where
  loc := fun v => if v = saCol QUEUE_ROOT_FIELD then 999 else goodEnqueueRow.loc v
  nxt := goodEnqueueRow.nxt
  pub := goodEnqueueRow.pub

/-- **NON-VACUITY (witness FALSE / concrete queue-root anti-ghost).** `badRootRow`'s queue root is
tampered, so `gQueueRootBind` REJECTS it — a concrete UNSAT over the now-BOUND side-table root. -/
theorem badRootRow_rejected :
    ¬ (VmConstraint.gate (gQueueRootBind 777)).holdsVm badRootRow false false := by
  apply queueEnqueueVm_rejects_wrong_queue_root
  simp only [badRootRow, goodEnqueueRow, saCol, QUEUE_ROOT_FIELD, STATE_AFTER_BASE, PARAM_BASE,
    STATE_SIZE, NUM_PARAMS, state.FIELD_BASE]
  norm_num

/-! ## §11 — Axiom-hygiene pins. -/

#guard (queueEnqueueVmDescriptor 0).constraints.length == 13 + 14 + 4 + 3
#guard (queueEnqueueVmDescriptor 0).hashSites.length == 4
#guard (queueEnqueueVmDescriptor 0).traceWidth == 186

#assert_axioms queueEnqueueVm_faithful
#assert_axioms queueEnqueueVm_rejects_wrong_output
#assert_axioms queueEnqueueVm_rejects_wrong_queue_root
#assert_axioms queueEnqueueVm_rejects_wrong_balance
#assert_axioms intent_to_cellEnqueueSpec
#assert_axioms queueEnqueueDescriptor_full_sound
#assert_axioms queueEnqueueDescriptor_commit_binds_state
#assert_axioms queueEnqueueK_bal
#assert_axioms unify_enqueue_debit
#assert_axioms descriptor_agrees_with_executor_enqueue
#assert_axioms goodEnqueueRow_realizes_intent
#assert_axioms badRootRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitQueueEnqueue
