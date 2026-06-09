/-
# Dregg2.Circuit.Emit.EffectVmEmitQueueResize — the `queueResizeA` (FIFO-queue capacity RESIZE) effect's
EffectVM emission, through the SAME `EffectVmEmit` IR as transfer.

Universe A (`Inst/queueResizeA.lean`, `Spec/queuefifocore.lean`) carries the FULL-state soundness
`queueResizeA_full_sound ⇒ QueueResizeSpec`: a committed resize REPLACES the witnessed queue record's
capacity in place (`replaceQueue … {q with capacity := newCap}`), advances the log, and FREEZES the other
16 kernel fields (`st'.kernel.bal = st.kernel.bal` — balance-NEUTRAL in universe A).

## STAGE-3 AMPLIFICATION: the queue side-table root is NOW BOUND.

STAGE 3 (`Exec.SystemRoots`, `state.systemRoot.QUEUE`) gives the queue side-table a committed root carried
at `state.FIELD_BASE + 4` (`fields[4]`). A resize touches only the CAPACITY, not the FIFO buffer, so the
runtime FREEZES the queue root (`fields[4]` unchanged) and writes the new capacity into `fields[5]`
(`effect_vm/air.rs` `ResizeQueue` arm). This descriptor now BINDS both: the queue-root FREEZE (the FIFO
contents are provably untouched — anti-ghost against a smuggled FIFO mutation) and the capacity write at
`fields[5]`. GROUP-4 site1 absorbs `fields[1..5]` (including BOTH `fields[4]` and `fields[5]`), folding
them into `state_commit`. So the resize state image is fully bound.

## RECONCILIATION onto the runtime trace-generator layout (the cutover-harness pattern, 3aaf0772d).

  * WRITES `fields[5] := new_capacity` (the capacity carrier); FREEZES `fields[4]` (queue root) and the
    other fields, cap_root, reserved, bal_hi.
  * DEBITS `bal_lo` by the witnessed resize cost `delta_mag · cost_per_slot · (1 − sign)` (grow ⇒ debit;
    shrink ⇒ no debit). The descriptor reads this cost as a supplied felt `resizeCost` (the hand-AIR's
    sign-decomposed value, witnessed in `aux::RESIZE_DELTA_*`), so it AGREES with the hand-AIR on the
    honest trace. Universe A is balance-NEUTRAL — the §connector reports the runtime-fee-vs-univA-neutral
    divergence (reconcile at `resizeCost = 0`, i.e. a shrink or a free grow).
  * TICKS the nonce; the earlier descriptor FROZE it (UNSAT) — now fixed via the shared `gNonce`.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` hypothesis. No `sorry`, no `:= True`, no `native_decide`. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.queuefifocore

namespace Dregg2.Circuit.Emit.EffectVmEmitQueueResize

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

/-! ## §0 — The queueResize selector + the runtime resize parameters + the carriers. -/

/-- The queueResize selector column index (`columns.rs::sel::RESIZE_QUEUE`). -/
def SEL_QUEUE_RESIZE : Nat := 21

/-! Runtime resize parameter columns. -/
namespace param
/-- The new capacity (`param::RESIZE_NEW_CAPACITY`). -/
def RESIZE_NEW_CAPACITY : Nat := 0
end param

/-- The new capacity as an expression (`param0`). -/
def ePrmNewCap : EmittedExpr := .var (prmCol param.RESIZE_NEW_CAPACITY)

/-- The queue-root state column (`fields[4]`, FROZEN on resize — the FIFO contents are untouched). -/
def QUEUE_ROOT_FIELD : Nat := state.FIELD_BASE + 4
/-- The capacity carrier state column (`fields[5]`, written to `new_capacity` on resize). -/
def QUEUE_CAP_FIELD : Nat := state.FIELD_BASE + 5

/-- The resize row: `s_queue_resize = 1`, `s_noop = 0`. -/
def IsQueueResizeRow (env : VmRowEnv) : Prop :=
  env.loc SEL_QUEUE_RESIZE = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — The per-row gate bodies (cost DEBIT + capacity WRITE + queue-root FREEZE + nonce TICK). -/

/-- Balance-lo DEBIT body: `new_bal_lo − old_bal_lo + resizeCost` (the witnessed sign-decomposed fee).
`resizeCost` is supplied as a parameter so the gate matches the hand-AIR's aux-witnessed value. -/
def gBalLoDebit (resizeCost : ℤ) : EmittedExpr :=
  .add (eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)) (.const resizeCost)

/-- Capacity WRITE BIND body: `fields[5]_after − new_capacity` (the capacity carrier becomes `param0`). -/
def gCapWrite : EmittedExpr := eSub (eSA QUEUE_CAP_FIELD) ePrmNewCap

/-- Queue-root FREEZE body: `fields[4]_after − fields[4]_before` (the FIFO contents untouched). -/
def gQueueRootFreeze : EmittedExpr := eSub (eSA QUEUE_ROOT_FIELD) (eSB QUEUE_ROOT_FIELD)

/-- Nonce TICK body, reused verbatim from transfer. -/
def gNonceTick : EmittedExpr := gNonce

/-- The six NON-capacity NON-queue-root field passthrough gates (`fields[0..3]`, `fields[6..7]`). -/
def gFieldPassNonCapRoot : List VmConstraint :=
  ([0, 1, 2, 3, 6, 7] : List Nat).map (fun i => VmConstraint.gate (gFieldPass i))

/-! ## §2 — The emitted queueResize descriptor. -/

/-- The queueResize AIR identity. -/
def queueResizeVmAirName : String := "dregg-effectvm-queueresize-v1"

/-- The resize per-row gates (parameterized by the witnessed resize cost felt). -/
def queueResizeRowGates (resizeCost : ℤ) : List VmConstraint :=
  [ .gate (gBalLoDebit resizeCost), .gate gBalHi, .gate gNonceTick
  , .gate gCapPass, .gate gResPass, .gate gCapWrite, .gate gQueueRootFreeze ] ++ gFieldPassNonCapRoot

/-- **`queueResizeVmDescriptor resizeCost`** — the FULL resize descriptor reconciled onto the runtime
layout: cost-debit + capacity-write + queue-root-freeze + nonce-tick + freeze gates ++ transition ++
boundary pins, with the 4 GROUP-4 hash sites (site1 absorbs `fields[4]` AND `fields[5]`) and ranges. -/
def queueResizeVmDescriptor (resizeCost : ℤ) : EffectVmDescriptor :=
  { name := queueResizeVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := queueResizeRowGates resizeCost ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The queueResize ROW INTENT (runtime-reconciled). -/

/-- **`QueueResizeRowIntent env resizeCost`** — the runtime resize move: `bal_lo` drops by `resizeCost`,
`fields[5]` (capacity) becomes `new_capacity`, `fields[4]` (queue root) FROZEN, the nonce TICKS, the rest
FROZEN. -/
def QueueResizeRowIntent (env : VmRowEnv) (resizeCost : ℤ) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO) - resizeCost
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ env.loc (saCol QUEUE_CAP_FIELD) = env.loc (prmCol param.RESIZE_NEW_CAPACITY)
  ∧ env.loc (saCol QUEUE_ROOT_FIELD) = env.loc (sbCol QUEUE_ROOT_FIELD)
  ∧ (∀ i ∈ ([0, 1, 2, 3, 6, 7] : List Nat),
        env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS. -/

theorem queueResizeVm_faithful (env : VmRowEnv) (resizeCost : ℤ) :
    (∀ c ∈ queueResizeRowGates resizeCost, c.holdsVm env false false)
      ↔ QueueResizeRowIntent env resizeCost := by
  unfold queueResizeRowGates gFieldPassNonCapRoot QueueResizeRowIntent
  constructor
  · intro h
    have hLo := h (.gate (gBalLoDebit resizeCost)) (by simp)
    have hHi := h (.gate gBalHi) (by simp)
    have hNon := h (.gate gNonceTick) (by simp)
    have hCap := h (.gate gCapPass) (by simp)
    have hRes := h (.gate gResPass) (by simp)
    have hCapW := h (.gate gCapWrite) (by simp)
    have hRoot := h (.gate gQueueRootFreeze) (by simp)
    have hFld : ∀ i ∈ ([0, 1, 2, 3, 6, 7] : List Nat),
        VmConstraint.holdsVm env false false (.gate (gFieldPass i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoDebit, gBalHi, gNonceTick, gNonce, gCapPass, gResPass,
      gCapWrite, gQueueRootFreeze, eSA, eSB, ePrmNewCap, eSelNoop, eSub,
      EmittedExpr.eval] at hLo hHi hNon hCap hRes hCapW hRoot
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · linarith [hLo]
    · linarith [hHi]
    · linarith [hNon]
    · linarith [hCap]
    · linarith [hRes]
    · linarith [hCapW]
    · linarith [hRoot]
    · intro i hi
      have := hFld i hi
      simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval] at this
      linarith
  · rintro ⟨hLo, hHi, hNon, hCap, hRes, hCapW, hRoot, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gBalLoDebit, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hLo]; ring
    · simp only [VmConstraint.holdsVm, gBalHi, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hHi]; ring
    · simp only [VmConstraint.holdsVm, gNonceTick, gNonce, eSA, eSB, eSelNoop, eSub, EmittedExpr.eval]
      rw [hNon]; ring
    · simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hCap]; ring
    · simp only [VmConstraint.holdsVm, gResPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gCapWrite, eSA, ePrmNewCap, eSub, EmittedExpr.eval]
      rw [hCapW]; ring
    · simp only [VmConstraint.holdsVm, gQueueRootFreeze, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hRoot]; ring
    · simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval]
      have hmem : i ∈ ([0, 1, 2, 3, 6, 7] : List Nat) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto
      rw [hFld i hmem]; ring

/-! ## §5 — ANTI-GHOST. -/

theorem queueResizeVm_rejects_wrong_output (env : VmRowEnv) (resizeCost : ℤ)
    (hwrong : ¬ QueueResizeRowIntent env resizeCost) :
    ¬ (∀ c ∈ queueResizeRowGates resizeCost, c.holdsVm env false false) :=
  fun h => hwrong ((queueResizeVm_faithful env resizeCost).mp h)

/-- **Anti-ghost (queue-root tamper).** A resize row that SMUGGLES a FIFO mutation (`fields[4]` moved)
is rejected by `gQueueRootFreeze` — the bound side-table root keeps resize from touching the buffer. -/
theorem queueResizeVm_rejects_moved_queue_root (env : VmRowEnv)
    (hwrong : env.loc (saCol QUEUE_ROOT_FIELD) ≠ env.loc (sbCol QUEUE_ROOT_FIELD)) :
    ¬ (VmConstraint.gate gQueueRootFreeze).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gQueueRootFreeze, eSA, eSB, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-- **Anti-ghost (capacity tamper).** A resize row whose `fields[5]` is NOT the declared new capacity is
rejected by `gCapWrite` — the capacity carrier is pinned to `param0`. -/
theorem queueResizeVm_rejects_wrong_capacity (env : VmRowEnv)
    (hwrong : env.loc (saCol QUEUE_CAP_FIELD) ≠ env.loc (prmCol param.RESIZE_NEW_CAPACITY)) :
    ¬ (VmConstraint.gate gCapWrite).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gCapWrite, eSA, ePrmNewCap, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-! ## §6 — The structured per-cell spec + descriptor soundness (REUSING `CellState`). -/

/-- The resize parameters carried in the param block. -/
structure ResizeParams where
  newCap : ℤ
  cost   : ℤ

/-- `RowEncodesResize env pre p post` ties the row's state-block + param columns to a transition. -/
def RowEncodesResize (env : VmRowEnv) (pre : CellState) (p : ResizeParams) (post : CellState) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (sbCol state.STATE_COMMIT) = pre.commit
  ∧ env.loc (prmCol param.RESIZE_NEW_CAPACITY) = p.newCap
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

/-- **`CellResizeSpec pre p post`** — the per-cell FULL-state resize spec: `balLo` drops by `cost`,
`fields 5` (capacity) becomes `newCap`, `fields 4` (queue root) FROZEN, the nonce TICKS, the rest frozen. -/
def CellResizeSpec (pre : CellState) (p : ResizeParams) (post : CellState) : Prop :=
  post.balLo = pre.balLo - p.cost
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce + 1
  ∧ post.fields 5 = p.newCap
  ∧ post.fields 4 = pre.fields 4
  ∧ (∀ i : Fin 8, i.val ≠ 4 → i.val ≠ 5 → post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

theorem intent_to_cellResizeSpec (env : VmRowEnv) (pre post : CellState) (p : ResizeParams)
    (henc : RowEncodesResize env pre p post)
    (hint : QueueResizeRowIntent env p.cost) :
    CellResizeSpec pre p post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC, hpNewCap, hNoop,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hcapW, hroot, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : post.balLo = pre.balLo - p.cost := by rw [← hsaLo, ← hsbLo]; exact hbal
    exact this
  · rw [← hsaHi, ← hsbHi]; exact hbhi
  · have : post.nonce = pre.nonce + (1 - env.loc sel.NOOP) := by rw [← hsaN, ← hsbN]; exact hnon
    rw [this, hNoop]; ring
  · have h5 : env.loc (saCol (state.FIELD_BASE + 5)) = post.fields ⟨5, by decide⟩ := hsaF ⟨5, by decide⟩
    have hcapW' : env.loc (saCol (state.FIELD_BASE + 5)) = env.loc (prmCol param.RESIZE_NEW_CAPACITY) := hcapW
    have hfe : post.fields (5 : Fin 8) = post.fields ⟨5, by decide⟩ := by congr 1
    rw [hfe, ← h5, hcapW', hpNewCap]
  · have h4a : env.loc (saCol (state.FIELD_BASE + 4)) = post.fields ⟨4, by decide⟩ := hsaF ⟨4, by decide⟩
    have h4b : env.loc (sbCol (state.FIELD_BASE + 4)) = pre.fields ⟨4, by decide⟩ := hsbF ⟨4, by decide⟩
    have hroot' : env.loc (saCol (state.FIELD_BASE + 4)) = env.loc (sbCol (state.FIELD_BASE + 4)) := hroot
    have hfe4 : post.fields (4 : Fin 8) = post.fields ⟨4, by decide⟩ := by congr 1
    have hfe4' : pre.fields (4 : Fin 8) = pre.fields ⟨4, by decide⟩ := by congr 1
    rw [hfe4, hfe4', ← h4a, ← h4b]; exact hroot'
  · intro i hi4 hi5
    have hmem : i.val ∈ ([0, 1, 2, 3, 6, 7] : List Nat) := by
      have := i.isLt; fin_cases i <;> first | (exact absurd rfl hi4) | (exact absurd rfl hi5) | decide
    have := hfld i.val hmem
    rw [← hsaF i, ← hsbF i]; exact this
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres

theorem queueResizeDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (p : ResizeParams)
    (henc : RowEncodesResize env pre p post)
    (hsat : satisfiedVm hash (queueResizeVmDescriptor p.cost) env true true) :
    CellResizeSpec pre p post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates' : ∀ c ∈ queueResizeRowGates p.cost, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ (queueResizeVmDescriptor p.cost).constraints := by
      unfold queueResizeVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hc))
    have := hcs c hmem
    unfold queueResizeRowGates gFieldPassNonCapRoot at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (queueResizeVm_faithful env p.cost).mp hgates'
  refine ⟨intent_to_cellResizeSpec env pre post p henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ (queueResizeVmDescriptor p.cost).constraints := by
      unfold queueResizeVmDescriptor
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

/-! ## §7 — The anti-ghost commitment tooth (REUSED; site1 absorbs `fields[4]` AND `fields[5]`). -/

theorem queueResizeDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (resizeCost : ℤ) (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash (queueResizeVmDescriptor resizeCost) e₁ true true)
    (hsat₂ : satisfiedVm hash (queueResizeVmDescriptor resizeCost) e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ transferHashSites := hsat₁.2.1
  have hs₂ : siteHoldsAll hash e₂ transferHashSites := hsat₂.2.1
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash (queueResizeVmDescriptor resizeCost) e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ (queueResizeVmDescriptor resizeCost).constraints := by
        unfold queueResizeVmDescriptor
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

/-! ## §8 — CONNECTOR to universe-A: the capacity write IS the resize image; balance reconciles at cost 0.

`QueueResizeSpec` REPLACES the witnessed queue's capacity (`replaceQueue … {q with capacity := newCap}`)
and pins `st'.kernel.bal = st.kernel.bal` (balance-NEUTRAL in universe A). The descriptor binds the
capacity write at the runtime's `fields[5]` carrier (the IR-supportable resize image) and FREEZES the
queue root `fields[4]` (the FIFO is provably untouched). The runtime fee reconciles with universe A's
frozen ledger exactly at `cost = 0` (a shrink or free grow). -/

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

/-- **`unify_resize_balFrozen_univA`** — universe A's `QueueResizeSpec` is balance-NEUTRAL: across a
committed resize, the projected `(c, asset)` ledger entry is FROZEN. So the descriptor's runtime
cost-debit AGREES with universe A's frozen ledger EXACTLY at `cost = 0`; for a non-zero grow fee the
runtime row and universe A genuinely DIVERGE — reported, not papered. -/
theorem unify_resize_balFrozen_univA (st : RecChainedState) (id newCap : Nat) (actor cell : CellId)
    (st' : RecChainedState) (c : CellId) (asset : AssetId)
    (hspec : QueueResizeSpec st id newCap actor cell st') :
    (cellProjBal st'.kernel.bal c asset).balLo = (cellProjBal st.kernel.bal c asset).balLo := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hbal, _⟩ := hspec
  show st'.kernel.bal c asset = st.kernel.bal c asset
  rw [hbal]

/-- **`resize_runtime_vs_univA_reconcile`** — the runtime cost-debit `CellResizeSpec.balLo` and universe
A's frozen ledger reconcile EXACTLY when the resize cost is zero (`p.cost = 0`). The honest gap statement. -/
theorem resize_runtime_vs_univA_reconcile (pre p post)
    (hcell : CellResizeSpec pre p post) (hzero : p.cost = 0) :
    post.balLo = pre.balLo := by
  obtain ⟨hbal, _⟩ := hcell
  rw [hbal, hzero, sub_zero]

/-! ## §9 — NON-VACUITY. -/

/-- A concrete resize row (cost = 6, new cap = 32): `bal_lo 50 → 44`, nonce 3 → 4 (TICK),
`fields[5] 0 → 32` (capacity), `fields[4] 17 → 17` (queue root FROZEN), rest frozen. -/
def goodResizeRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_QUEUE_RESIZE then 1
    else if v = sbCol state.BALANCE_LO then 50
    else if v = saCol state.BALANCE_LO then 44
    else if v = sbCol state.NONCE then 3
    else if v = saCol state.NONCE then 4
    else if v = prmCol param.RESIZE_NEW_CAPACITY then 32
    else if v = saCol QUEUE_CAP_FIELD then 32
    else if v = sbCol QUEUE_ROOT_FIELD then 17
    else if v = saCol QUEUE_ROOT_FIELD then 17
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `goodResizeRow` REALIZES the reconciled resize intent (cost = 6). -/
theorem goodResizeRow_realizes_intent : QueueResizeRowIntent goodResizeRow 6 := by
  unfold QueueResizeRowIntent goodResizeRow QUEUE_CAP_FIELD QUEUE_ROOT_FIELD
  simp only [sbCol, saCol, prmCol, SEL_QUEUE_RESIZE, sel.NOOP, STATE_BEFORE_BASE, STATE_AFTER_BASE,
    PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE, param.RESIZE_NEW_CAPACITY]
  refine ⟨by norm_num, rfl, by norm_num, rfl, rfl, by norm_num, by norm_num, ?_⟩
  intro i hi
  fin_cases hi <;> norm_num

/-- A FORGED resize row: the queue root smuggled to `999` (a FIFO mutation hidden in a resize). -/
def badRootRow : VmRowEnv where
  loc := fun v => if v = saCol QUEUE_ROOT_FIELD then 999 else goodResizeRow.loc v
  nxt := goodResizeRow.nxt
  pub := goodResizeRow.pub

/-- **NON-VACUITY (witness FALSE / concrete queue-root anti-ghost).** `badRootRow` moves the queue root,
so `gQueueRootFreeze` REJECTS it — resize cannot touch the FIFO contents. -/
theorem badRootRow_rejected :
    ¬ (VmConstraint.gate gQueueRootFreeze).holdsVm badRootRow false false := by
  apply queueResizeVm_rejects_moved_queue_root
  simp only [badRootRow, goodResizeRow, sbCol, saCol, QUEUE_ROOT_FIELD, QUEUE_CAP_FIELD,
    SEL_QUEUE_RESIZE, prmCol, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, STATE_SIZE, NUM_PARAMS,
    NUM_EFFECTS, state.FIELD_BASE, state.BALANCE_LO, state.NONCE, param.RESIZE_NEW_CAPACITY]
  norm_num

/-! ## §10 — Axiom-hygiene pins. -/

#guard (queueResizeVmDescriptor 0).constraints.length == 13 + 14 + 4 + 3
#guard (queueResizeVmDescriptor 0).hashSites.length == 4
#guard (queueResizeVmDescriptor 0).traceWidth == 186

#assert_axioms queueResizeVm_faithful
#assert_axioms queueResizeVm_rejects_wrong_output
#assert_axioms queueResizeVm_rejects_moved_queue_root
#assert_axioms queueResizeVm_rejects_wrong_capacity
#assert_axioms intent_to_cellResizeSpec
#assert_axioms queueResizeDescriptor_full_sound
#assert_axioms queueResizeDescriptor_commit_binds_state
#assert_axioms unify_resize_balFrozen_univA
#assert_axioms resize_runtime_vs_univA_reconcile
#assert_axioms goodResizeRow_realizes_intent
#assert_axioms badRootRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitQueueResize
