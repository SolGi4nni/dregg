/-
# Dregg2.Circuit.Emit.EffectVmEmitQueueAtomicTx — the `queueAtomicTxA` (ALL-OR-NOTHING atomic queue-op
batch) effect's EffectVM emission, through the SAME `EffectVmEmit` IR as transfer.

Universe A (`Spec/queueatomictx.lean`) carries the FULL-state soundness `execFullA_queueAtomicTxA_iff_spec
⇒ QueueAtomicTxSpec`: a committed batch folds a VARIABLE-LENGTH list of sub-ops (enqueue/dequeue) through
`queueAtomicTxChainA`, touching `queues` + `bal` + `escrows`, with one batch-commit log row. The
post-kernel is EXACTLY the fold's `s1.kernel`.

## STAGE-3 AMPLIFICATION: the queue side-table root is NOW BOUND.

STAGE 3 (`Exec.SystemRoots`, `state.systemRoot.QUEUE`) gives the queue side-table a committed root carried
at `state.FIELD_BASE + 4` (`fields[4]`). The runtime models the WHOLE atomic batch as one queue-root
TRANSITION: `fields[4]_before = combined_old_root`, `fields[4]_after = combined_new_root`
(`effect_vm/air.rs` `AtomicQueueTx` arm, bound to the tx via `aux[0] = hash(tx_hash, hash(old, new))`).
This descriptor now BINDS that transition (both the before-pin and the after-write); GROUP-4 site1 folds
`fields[4]` into `state_commit`. So the atomic batch's net queue-root change is bound — no longer
out-of-IR.

## RECONCILIATION onto the runtime trace-generator layout (the cutover-harness pattern, 3aaf0772d).

  * DEBITS `bal_lo` by the net deposit (`param4 = ATOMIC_TX_NET_DEPOSIT`) — the net of sub-op
    deposits/refunds.
  * PINS `fields[4]_before = combined_old_root` (`param2`) and WRITES `fields[4]_after = combined_new_root`
    (`param3`); FREEZES `fields[0..3]`, `fields[5..7]`, cap_root, reserved, bal_hi.
  * TICKS the nonce; the earlier descriptor FROZE it (UNSAT) — now fixed via the shared `gNonce`.

The EMPTY batch reconciles with universe A exactly (`unify_atomic_empty_balFrozen`: net = 0, root
unchanged). A non-empty batch's full fold is the batch's intrinsic semantics; the descriptor binds its
NET queue-root + balance image (the runtime's single-row atomic representation).

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` hypothesis. No `sorry`, no `:= True`, no `native_decide`. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.queueatomictx

namespace Dregg2.Circuit.Emit.EffectVmEmitQueueAtomicTx

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

/-! ## §0 — The queueAtomicTx selector + the runtime atomic params + the queue-root carrier. -/

/-- The queueAtomicTx selector column index (`columns.rs::sel::ATOMIC_QUEUE_TX`). -/
def SEL_QUEUE_ATOMIC : Nat := 22

/-! Runtime atomic-tx parameter columns. -/
namespace param
/-- The combined OLD queue root (`param::ATOMIC_TX_COMBINED_OLD_ROOT`). -/
def ATOMIC_TX_COMBINED_OLD_ROOT : Nat := 2
/-- The combined NEW queue root (`param::ATOMIC_TX_COMBINED_NEW_ROOT`). -/
def ATOMIC_TX_COMBINED_NEW_ROOT : Nat := 3
/-- The net deposit debited (`param::ATOMIC_TX_NET_DEPOSIT`). -/
def ATOMIC_TX_NET_DEPOSIT : Nat := 4
end param

/-- The net deposit as an expression (`param4`). -/
def ePrmNetDeposit : EmittedExpr := .var (prmCol param.ATOMIC_TX_NET_DEPOSIT)
/-- The combined old root as an expression (`param2`). -/
def ePrmOldRoot : EmittedExpr := .var (prmCol param.ATOMIC_TX_COMBINED_OLD_ROOT)
/-- The combined new root as an expression (`param3`). -/
def ePrmNewRoot : EmittedExpr := .var (prmCol param.ATOMIC_TX_COMBINED_NEW_ROOT)

/-- The queue-root state column (`fields[4]`, the runtime's queue-side-table-root carrier). -/
def QUEUE_ROOT_FIELD : Nat := state.FIELD_BASE + 4

/-- The atomic-tx row: `s_queue_atomic = 1`, `s_noop = 0`. -/
def IsQueueAtomicRow (env : VmRowEnv) : Prop :=
  env.loc SEL_QUEUE_ATOMIC = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — The per-row gate bodies (net-deposit DEBIT + queue-root before-pin + after-write + nonce TICK). -/

/-- Balance-lo DEBIT body: `new_bal_lo − old_bal_lo + net_deposit`. -/
def gBalLoDebit : EmittedExpr :=
  .add (eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)) ePrmNetDeposit

/-- Queue-root BEFORE-pin body: `fields[4]_before − combined_old_root` (the batch starts at the old root). -/
def gQueueRootBefore : EmittedExpr := eSub (eSB QUEUE_ROOT_FIELD) ePrmOldRoot

/-- Queue-root AFTER-write body: `fields[4]_after − combined_new_root` (the batch lands the new root). -/
def gQueueRootAfter : EmittedExpr := eSub (eSA QUEUE_ROOT_FIELD) ePrmNewRoot

/-- Nonce TICK body, reused verbatim from transfer. -/
def gNonceTick : EmittedExpr := gNonce

/-- The seven NON-queue-root field passthrough gates (`fields[0..3]`, `fields[5..7]`). -/
def gFieldPassNonRoot : List VmConstraint :=
  ([0, 1, 2, 3, 5, 6, 7] : List Nat).map (fun i => VmConstraint.gate (gFieldPass i))

/-! ## §2 — The emitted queueAtomicTx descriptor. -/

/-- The queueAtomicTx AIR identity. -/
def queueAtomicVmAirName : String := "dregg-effectvm-queueatomictx-v1"

/-- The atomic-tx per-row gates: net-deposit debit, bal_hi freeze, nonce TICK, cap/reserved freeze,
queue-root before-pin + after-write, 7 non-root field freezes. -/
def queueAtomicRowGates : List VmConstraint :=
  [ .gate gBalLoDebit, .gate gBalHi, .gate gNonceTick
  , .gate gCapPass, .gate gResPass, .gate gQueueRootBefore, .gate gQueueRootAfter ] ++ gFieldPassNonRoot

/-- **`queueAtomicVmDescriptor`** — the FULL atomic-tx descriptor reconciled onto the runtime layout:
net-deposit-debit + queue-root before-pin/after-write + nonce-tick + freeze gates ++ transition ++
boundary pins, with the 4 GROUP-4 hash sites (site1 absorbs `fields[4]`) and the 2 range checks. -/
def queueAtomicVmDescriptor : EffectVmDescriptor :=
  { name := queueAtomicVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := queueAtomicRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The queueAtomicTx ROW INTENT (runtime-reconciled). -/

/-- **`QueueAtomicRowIntent env`** — the runtime atomic-batch move: `bal_lo` drops by `net_deposit`, the
queue-root carrier (`fields[4]`) goes from `combined_old_root` to `combined_new_root`, the nonce TICKS,
the rest FROZEN. -/
def QueueAtomicRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO) - env.loc (prmCol param.ATOMIC_TX_NET_DEPOSIT)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ env.loc (sbCol QUEUE_ROOT_FIELD) = env.loc (prmCol param.ATOMIC_TX_COMBINED_OLD_ROOT)
  ∧ env.loc (saCol QUEUE_ROOT_FIELD) = env.loc (prmCol param.ATOMIC_TX_COMBINED_NEW_ROOT)
  ∧ (∀ i ∈ ([0, 1, 2, 3, 5, 6, 7] : List Nat),
        env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS. -/

theorem queueAtomicVm_faithful (env : VmRowEnv) :
    (∀ c ∈ queueAtomicRowGates, c.holdsVm env false false) ↔ QueueAtomicRowIntent env := by
  unfold queueAtomicRowGates gFieldPassNonRoot QueueAtomicRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoDebit) (by simp)
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
    simp only [VmConstraint.holdsVm, gBalLoDebit, gBalHi, gNonceTick, gNonce, gCapPass, gResPass,
      gQueueRootBefore, gQueueRootAfter, eSA, eSB, ePrmNetDeposit, ePrmOldRoot, ePrmNewRoot, eSelNoop,
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
    · simp only [VmConstraint.holdsVm, gBalLoDebit, eSA, eSB, ePrmNetDeposit, eSub, EmittedExpr.eval]
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

theorem queueAtomicVm_rejects_wrong_output (env : VmRowEnv)
    (hwrong : ¬ QueueAtomicRowIntent env) :
    ¬ (∀ c ∈ queueAtomicRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((queueAtomicVm_faithful env).mp h)

/-- **Anti-ghost (queue-root after-tamper).** A row whose post-`fields[4]` is NOT the declared
`combined_new_root` (a forged atomic outcome) is rejected by `gQueueRootAfter` alone. -/
theorem queueAtomicVm_rejects_wrong_queue_root (env : VmRowEnv)
    (hwrong : env.loc (saCol QUEUE_ROOT_FIELD) ≠ env.loc (prmCol param.ATOMIC_TX_COMBINED_NEW_ROOT)) :
    ¬ (VmConstraint.gate gQueueRootAfter).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gQueueRootAfter, eSA, ePrmNewRoot, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

theorem queueAtomicVm_rejects_wrong_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO)
      ≠ env.loc (sbCol state.BALANCE_LO) - env.loc (prmCol param.ATOMIC_TX_NET_DEPOSIT)) :
    ¬ (VmConstraint.gate gBalLoDebit).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoDebit, eSA, eSB, ePrmNetDeposit, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-! ## §6 — The structured per-cell spec + descriptor soundness (REUSING `CellState`). -/

/-- The atomic-tx parameters carried in the param block. -/
structure AtomicParams where
  netDeposit : ℤ
  oldRoot    : ℤ
  newRoot    : ℤ

/-- `RowEncodesAtomic env pre p post` ties the row's state-block + param columns to a transition. -/
def RowEncodesAtomic (env : VmRowEnv) (pre : CellState) (p : AtomicParams) (post : CellState) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (sbCol state.STATE_COMMIT) = pre.commit
  ∧ env.loc (prmCol param.ATOMIC_TX_NET_DEPOSIT) = p.netDeposit
  ∧ env.loc (prmCol param.ATOMIC_TX_COMBINED_OLD_ROOT) = p.oldRoot
  ∧ env.loc (prmCol param.ATOMIC_TX_COMBINED_NEW_ROOT) = p.newRoot
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

/-- **`CellAtomicSpec pre p post`** — the per-cell FULL-state atomic-batch spec: `balLo` drops by
`netDeposit`, the queue-root cell (`fields 4`) goes `oldRoot → newRoot`, the nonce TICKS, the rest
frozen. -/
def CellAtomicSpec (pre : CellState) (p : AtomicParams) (post : CellState) : Prop :=
  post.balLo = pre.balLo - p.netDeposit
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce + 1
  ∧ pre.fields 4 = p.oldRoot
  ∧ post.fields 4 = p.newRoot
  ∧ (∀ i : Fin 8, i.val ≠ 4 → post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

theorem intent_to_cellAtomicSpec (env : VmRowEnv) (pre post : CellState) (p : AtomicParams)
    (henc : RowEncodesAtomic env pre p post) (hint : QueueAtomicRowIntent env) :
    CellAtomicSpec pre p post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC, hpNet, hpOld, hpNew, hNoop,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hbef, haft, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : post.balLo = pre.balLo - env.loc (prmCol param.ATOMIC_TX_NET_DEPOSIT) := by
      rw [← hsaLo, ← hsbLo]; exact hbal
    rw [this, hpNet]
  · rw [← hsaHi, ← hsbHi]; exact hbhi
  · have : post.nonce = pre.nonce + (1 - env.loc sel.NOOP) := by rw [← hsaN, ← hsbN]; exact hnon
    rw [this, hNoop]; ring
  · have h4b : env.loc (sbCol (state.FIELD_BASE + 4)) = pre.fields ⟨4, by decide⟩ := hsbF ⟨4, by decide⟩
    have hbef' : env.loc (sbCol (state.FIELD_BASE + 4)) = env.loc (prmCol param.ATOMIC_TX_COMBINED_OLD_ROOT) := hbef
    have hfe : pre.fields (4 : Fin 8) = pre.fields ⟨4, by decide⟩ := by congr 1
    rw [hfe, ← h4b, hbef', hpOld]
  · have h4a : env.loc (saCol (state.FIELD_BASE + 4)) = post.fields ⟨4, by decide⟩ := hsaF ⟨4, by decide⟩
    have haft' : env.loc (saCol (state.FIELD_BASE + 4)) = env.loc (prmCol param.ATOMIC_TX_COMBINED_NEW_ROOT) := haft
    have hfe : post.fields (4 : Fin 8) = post.fields ⟨4, by decide⟩ := by congr 1
    rw [hfe, ← h4a, haft', hpNew]
  · intro i hi4
    have hmem : i.val ∈ ([0, 1, 2, 3, 5, 6, 7] : List Nat) := by
      have := i.isLt; fin_cases i <;> first | (exact absurd rfl hi4) | decide
    have := hfld i.val hmem
    rw [← hsaF i, ← hsbF i]; exact this
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres

theorem queueAtomicDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (p : AtomicParams)
    (henc : RowEncodesAtomic env pre p post)
    (hsat : satisfiedVm hash queueAtomicVmDescriptor env true true) :
    CellAtomicSpec pre p post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates' : ∀ c ∈ queueAtomicRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ queueAtomicVmDescriptor.constraints := by
      unfold queueAtomicVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hc))
    have := hcs c hmem
    unfold queueAtomicRowGates gFieldPassNonRoot at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (queueAtomicVm_faithful env).mp hgates'
  refine ⟨intent_to_cellAtomicSpec env pre post p henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ queueAtomicVmDescriptor.constraints := by
      unfold queueAtomicVmDescriptor
      simp only [List.mem_append]
      exact Or.inr hc
    have hh := hcs c hmem
    unfold boundaryLastPins at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      · simp only [VmConstraint.holdsVm] at hh ⊢
        exact hh
  have hpin := (boundaryLast_pins env hlast).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]; exact hpin

/-! ## §7 — The anti-ghost commitment tooth (REUSED; site1 absorbs `fields[4]`, the queue root). -/

theorem queueAtomicDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash queueAtomicVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash queueAtomicVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ transferHashSites := hsat₁.2.1
  have hs₂ : siteHoldsAll hash e₂ transferHashSites := hsat₂.2.1
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash queueAtomicVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ queueAtomicVmDescriptor.constraints := by
        unfold queueAtomicVmDescriptor
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

/-! ## §8 — CONNECTOR to universe-A: the EMPTY batch IS the no-op (frozen ledger + unchanged root).

`QueueAtomicTxSpec st actor [] st'` has `st'.kernel = st.kernel` — the WHOLE per-asset ledger AND the
queue side-table are FROZEN. The runtime models this as `net_deposit = 0` and `combined_new = combined_old`,
so the descriptor's net-deposit-debit + queue-root transition reduces to the freeze EXACTLY. A non-empty
batch's full fold is the batch's intrinsic variable-length semantics; the descriptor binds its NET
queue-root + balance image (the runtime's single-row atomic representation). -/

open Dregg2.Circuit.Spec.QueueAtomicTx
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

/-- Project the `(c, asset)` per-asset ledger entry into the keystone `CellState`'s `balLo` limb. -/
def cellProjBal (bal : CellId → AssetId → ℤ) (c : CellId) (asset : AssetId) : CellState where
  balLo    := bal c asset
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- The EMPTY-batch fold is the identity on the kernel: `queueAtomicTxChainA s [] = some s`. -/
theorem emptyBatch_kernel_id (s s1 : RecChainedState)
    (h : queueAtomicTxChainA s [] = some s1) : s1.kernel = s.kernel := by
  simp only [queueAtomicTxChainA, Option.some.injEq] at h
  rw [← h]

/-- **`unify_atomic_empty_balFrozen`** — across a committed EMPTY `QueueAtomicTxSpec` batch, the projected
`(c, asset)` ledger entry is FROZEN. So the descriptor's balance-debit reduces to the freeze EXACTLY on
the empty batch (net = 0) — its genuine per-cell balance image. -/
theorem unify_atomic_empty_balFrozen (st st' : RecChainedState) (actor : CellId)
    (c : CellId) (asset : AssetId)
    (hspec : QueueAtomicTxSpec st actor [] st') :
    (cellProjBal st'.kernel.bal c asset).balLo = (cellProjBal st.kernel.bal c asset).balLo := by
  obtain ⟨s1, hchain, hker, _⟩ := hspec
  show st'.kernel.bal c asset = st.kernel.bal c asset
  rw [hker, emptyBatch_kernel_id st s1 hchain]

/-- **`atomic_empty_reconcile`** — the runtime atomic-batch `CellAtomicSpec` reduces to a full freeze when
the batch is the empty/no-op case (`netDeposit = 0`, `oldRoot = newRoot`): balance frozen and the queue
root unchanged. The honest reconciliation of the runtime single-row image with universe A's empty batch. -/
theorem atomic_empty_reconcile (pre p post)
    (hcell : CellAtomicSpec pre p post) (hzero : p.netDeposit = 0) (hroot : p.oldRoot = p.newRoot) :
    post.balLo = pre.balLo ∧ post.fields 4 = pre.fields 4 := by
  obtain ⟨hbal, _, _, hpre4, hpost4, _⟩ := hcell
  refine ⟨?_, ?_⟩
  · rw [hbal, hzero, sub_zero]
  · rw [hpost4, ← hroot, ← hpre4]

/-! ## §9 — NON-VACUITY. -/

/-- A concrete atomic-batch row (net deposit 5, old root 13, new root 21): `bal_lo 40 → 35`, nonce 1 → 2
(TICK), `fields[4] 13 → 21` (queue root advance), rest frozen. -/
def goodAtomicRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_QUEUE_ATOMIC then 1
    else if v = sbCol state.BALANCE_LO then 40
    else if v = saCol state.BALANCE_LO then 35
    else if v = sbCol state.NONCE then 1
    else if v = saCol state.NONCE then 2
    else if v = prmCol param.ATOMIC_TX_NET_DEPOSIT then 5
    else if v = prmCol param.ATOMIC_TX_COMBINED_OLD_ROOT then 13
    else if v = prmCol param.ATOMIC_TX_COMBINED_NEW_ROOT then 21
    else if v = sbCol QUEUE_ROOT_FIELD then 13
    else if v = saCol QUEUE_ROOT_FIELD then 21
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `goodAtomicRow` REALIZES the reconciled atomic-batch intent. -/
theorem goodAtomicRow_realizes_intent : QueueAtomicRowIntent goodAtomicRow := by
  unfold QueueAtomicRowIntent goodAtomicRow QUEUE_ROOT_FIELD
  simp only [sbCol, saCol, prmCol, SEL_QUEUE_ATOMIC, sel.NOOP, STATE_BEFORE_BASE, STATE_AFTER_BASE,
    PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE, param.ATOMIC_TX_NET_DEPOSIT,
    param.ATOMIC_TX_COMBINED_OLD_ROOT, param.ATOMIC_TX_COMBINED_NEW_ROOT]
  refine ⟨by norm_num, rfl, by norm_num, rfl, rfl, by norm_num, by norm_num, ?_⟩
  intro i hi
  fin_cases hi <;> norm_num

/-- A FORGED atomic-batch row: the post queue root tampered to `999` (a forged atomic outcome). -/
def badRootRow : VmRowEnv where
  loc := fun v => if v = saCol QUEUE_ROOT_FIELD then 999 else goodAtomicRow.loc v
  nxt := goodAtomicRow.nxt
  pub := goodAtomicRow.pub

/-- **NON-VACUITY (witness FALSE / concrete queue-root anti-ghost).** `badRootRow`'s post queue root is
not `combined_new_root`, so `gQueueRootAfter` REJECTS it — the bound atomic outcome. -/
theorem badRootRow_rejected :
    ¬ (VmConstraint.gate gQueueRootAfter).holdsVm badRootRow false false := by
  apply queueAtomicVm_rejects_wrong_queue_root
  simp only [badRootRow, goodAtomicRow, saCol, sbCol, prmCol, QUEUE_ROOT_FIELD, SEL_QUEUE_ATOMIC,
    STATE_AFTER_BASE, STATE_BEFORE_BASE, PARAM_BASE, STATE_SIZE, NUM_PARAMS, NUM_EFFECTS,
    state.FIELD_BASE, state.BALANCE_LO, state.NONCE, param.ATOMIC_TX_NET_DEPOSIT,
    param.ATOMIC_TX_COMBINED_OLD_ROOT, param.ATOMIC_TX_COMBINED_NEW_ROOT]
  norm_num

/-! ## §10 — Axiom-hygiene pins. -/

#guard queueAtomicVmDescriptor.constraints.length == 14 + 14 + 4 + 3
#guard queueAtomicVmDescriptor.hashSites.length == 4
#guard queueAtomicVmDescriptor.traceWidth == 186

#assert_axioms queueAtomicVm_faithful
#assert_axioms queueAtomicVm_rejects_wrong_output
#assert_axioms queueAtomicVm_rejects_wrong_queue_root
#assert_axioms queueAtomicVm_rejects_wrong_balance
#assert_axioms intent_to_cellAtomicSpec
#assert_axioms queueAtomicDescriptor_full_sound
#assert_axioms queueAtomicDescriptor_commit_binds_state
#assert_axioms emptyBatch_kernel_id
#assert_axioms unify_atomic_empty_balFrozen
#assert_axioms atomic_empty_reconcile
#assert_axioms goodAtomicRow_realizes_intent
#assert_axioms badRootRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitQueueAtomicTx
