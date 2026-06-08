/-
# Dregg2.Circuit.Emit.EffectVmEmitQueueResize — the `queueResizeA` (FIFO-queue RE-CAP) effect's
EffectVM emission, through the SAME `EffectVmEmit` IR as transfer.

Universe A (`Inst/queueResizeA.lean`, `Spec/queuefifocore.lean`) carries the FULL-state soundness
`queueResizeA_full_sound ⇒ QueueResizeSpec`: a committed resize REPLACES the witnessed queue record by
`{q with capacity := newCap}` in `queues` (buffer UNTOUCHED — a capacity-only re-cap), advances the
chained `log` by the resize receipt, and FREEZES the other 16 kernel fields (NO balance move).

## What the EffectVM IR (a 14-column per-cell state block + GROUP-4 commitment) DOES support

`queueResizeA` is balance-NEUTRAL: it moves NO value on the per-asset `bal` ledger. On the EffectVM row
the representing cell's balance limbs are UNCHANGED, the nonce is FROZEN (the executor does not tick it
— `queueResizeChainA` rewrites only `queues` + `log`), and the whole frame (cap_root, reserved, the 8
fields) is frozen. The IR carries this NO-OP-cell shape totally (the full-state freeze gates ++ the
GROUP-4 commitment chain binding the unchanged after-state block into `state_commit`).

## THE IR-EXTENSION FLAG (the FIFO-queue set-membership / no-shrink-below-occupancy leg)

`QueueResizeSpec`'s load-bearing clause is `st'.queues = replaceQueue st.queues id {q with capacity :=
newCap}` GATED by `q.buffer.length ≤ newCap` (the no-shrink-below-occupancy bound, so pending messages
cannot be silently dropped). This is a MERKLE/LIST-MEMBERSHIP UPDATE (find the record by `id`, replace
it in place, leave every other record + the buffer ORDER intact), plus an OCCUPANCY COMPARISON over the
buffer length — both of which universe A binds via `listComponent`/`listDigest`.

The EffectVM 14-column state block has NO queue-side-table-root column, and the four GROUP-4 hash-sites
absorb NONE of the `queues` list. So the IR CANNOT bind the in-place record replacement into
`state_commit`, CANNOT express the buffer-length occupancy bound, and CANNOT pin that every OTHER queue
record is preserved.

  ⇒ **needs IR extension: a queue-side-table-root column absorbed by a NEW merkle/list-accumulator
     hash-site (matching universe A's `listDigest LE`), PLUS a per-record-update gate that pins
     `replaceQueue id {q with capacity := newCap}` against the root (the merkle-update form), PLUS a
     RANGE/COMPARE gate `q.buffer.length ≤ newCap` over the buffer's modeled length. The current IR has
     NO list-accumulator gate-kind and NO membership-update form — only gate/transition/boundary/
     piBinding/hashSite(fixed-arity-per-row)/range.**

`queueResizeA` is therefore **IR-BLOCKED for its load-bearing re-cap+occupancy leg**. This module proves
what the IR DOES support (the balance-neutral no-op cell + 14-column commitment) and reports the
queue-record replacement + occupancy bound as out-of-IR — NOT papered, NOT faked.

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
  (eSB eSA ePrm eSub gBalHi gCapPass gResPass gFieldPass gFieldPassAll
   transitionAll boundaryFirstPins boundaryLastPins
   transferHashSites transferHash_binds boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState absorbedCols absorbed_determined_by_commit)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option linter.unusedVariables false

/-! ## §0 — The queueResize selector + the (no) balance move. -/

/-- The queueResize selector column index (a LAYOUT CHOICE local to this descriptor). -/
def SEL_QUEUE_RESIZE : Nat := 4

/-- The resize row: `s_queue_resize = 1`, `s_noop = 0`. -/
def IsQueueResizeRow (env : VmRowEnv) : Prop :=
  env.loc SEL_QUEUE_RESIZE = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — The per-row gate bodies (balance-NEUTRAL no-op cell: FULL state freeze). -/

/-- Balance-lo FREEZE body: `new_bal_lo − old_bal_lo`. -/
def gBalLoFreeze : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)

/-- Nonce-FREEZE body: `new_nonce − old_nonce`. -/
def gNonceFreeze : EmittedExpr := eSub (eSA state.NONCE) (eSB state.NONCE)

/-! ## §2 — The emitted queueResize descriptor. -/

/-- The queueResize AIR identity. -/
def queueResizeVmAirName : String := "dregg-effectvm-queueresize-v1"

/-- The resize per-row gates: balance-lo freeze, bal_hi freeze, nonce freeze, cap/reserved freeze,
8 fields freeze. -/
def queueResizeRowGates : List VmConstraint :=
  [ .gate gBalLoFreeze, .gate gBalHi, .gate gNonceFreeze
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-- **`queueResizeVmDescriptor`** — the IR-supportable part of queueResize: the per-row full-state
freeze gates ++ transition continuity ++ the 7 boundary PI pins, with the 4 ordered GROUP-4 hash sites
and the 2 balance-limb range checks. The FIFO-record re-cap + occupancy bound is OUT-OF-IR. -/
def queueResizeVmDescriptor : EffectVmDescriptor :=
  { name := queueResizeVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := queueResizeRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The queueResize ROW INTENT (the IR-supportable faithfulness target: cell frozen). -/

/-- **`QueueResizeRowIntent env`** — the IR-supportable resize move: the representing cell frozen. -/
def QueueResizeRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the (IR-supportable) intent. -/

/-- **`queueResizeVm_faithful`.** On a resize row, the emitted descriptor's per-row gates all hold IFF
`QueueResizeRowIntent` holds — the gates pin EXACTLY the balance-neutral full-cell freeze. -/
theorem queueResizeVm_faithful (env : VmRowEnv) :
    (∀ c ∈ queueResizeRowGates, c.holdsVm env false false) ↔ QueueResizeRowIntent env := by
  unfold queueResizeRowGates gFieldPassAll QueueResizeRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoFreeze) (by simp)
    have hHi := h (.gate gBalHi) (by simp)
    have hNon := h (.gate gNonceFreeze) (by simp)
    have hCap := h (.gate gCapPass) (by simp)
    have hRes := h (.gate gResPass) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldPass i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoFreeze, gBalHi, gNonceFreeze, gCapPass, gResPass,
      eSA, eSB, eSub, EmittedExpr.eval] at hLo hHi hNon hCap hRes
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · linarith [hLo]
    · linarith [hHi]
    · linarith [hNon]
    · linarith [hCap]
    · linarith [hRes]
    · intro i hi
      have := hFld i hi
      simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval] at this
      linarith
  · rintro ⟨hLo, hHi, hNon, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hLo]; ring
    · simp only [VmConstraint.holdsVm, gBalHi, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hHi]; ring
    · simp only [VmConstraint.holdsVm, gNonceFreeze, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hNon]; ring
    · simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hCap]; ring
    · simp only [VmConstraint.holdsVm, gResPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hFld i hi]; ring

/-! ## §5 — ANTI-GHOST. -/

theorem queueResizeVm_rejects_wrong_output (env : VmRowEnv)
    (hwrong : ¬ QueueResizeRowIntent env) :
    ¬ (∀ c ∈ queueResizeRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((queueResizeVm_faithful env).mp h)

theorem queueResizeVm_rejects_moved_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (VmConstraint.gate gBalLoFreeze).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-! ## §6 — The structured per-cell spec + descriptor soundness (REUSING `CellState`). -/

/-- `RowEncodesNoop env pre post` ties the row's state-block columns to a frozen `(pre, post)` cell. -/
def RowEncodesNoop (env : VmRowEnv) (pre post : CellState) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (sbCol state.STATE_COMMIT) = pre.commit
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved
  ∧ env.loc (saCol state.STATE_COMMIT) = post.commit
  ∧ env.pub pi.OLD_COMMIT = pre.commit
  ∧ env.pub pi.NEW_COMMIT = post.commit

/-- **`CellFreezeSpec pre post`** — the per-cell FULL-state freeze (cell unchanged on every data
column). The EffectVM-row projection of resize's balance-neutral, cell-untouched nature. -/
def CellFreezeSpec (pre post : CellState) : Prop :=
  post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

theorem intent_to_cellFreezeSpec (env : VmRowEnv) (pre post : CellState)
    (henc : RowEncodesNoop env pre post) (hint : QueueResizeRowIntent env) :
    CellFreezeSpec pre post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsaLo, ← hsbLo]; exact hbal
  · rw [← hsaHi, ← hsbHi]; exact hbhi
  · rw [← hsaN, ← hsbN]; exact hnon
  · intro i
    have := hfld i.val i.isLt
    rw [← hsaF i, ← hsbF i]; exact this
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres

/-- **`queueResizeDescriptor_full_sound`** — satisfying the WHOLE runnable descriptor forces the
per-cell `CellFreezeSpec` AND publishes the post-commit as `PI[NEW_COMMIT]`. (FIFO re-cap is out-of-IR.) -/
theorem queueResizeDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState)
    (henc : RowEncodesNoop env pre post)
    (hsat : satisfiedVm hash queueResizeVmDescriptor env true true) :
    CellFreezeSpec pre post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates' : ∀ c ∈ queueResizeRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ queueResizeVmDescriptor.constraints := by
      unfold queueResizeVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hc))
    have := hcs c hmem
    unfold queueResizeRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (queueResizeVm_faithful env).mp hgates'
  refine ⟨intent_to_cellFreezeSpec env pre post henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ queueResizeVmDescriptor.constraints := by
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
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]; exact hpin

/-! ## §7 — The anti-ghost commitment tooth (REUSED — hash sites identical to transfer). -/

theorem queueResizeDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash queueResizeVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash queueResizeVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ transferHashSites := hsat₁.2
  have hs₂ : siteHoldsAll hash e₂ transferHashSites := hsat₂.2
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash queueResizeVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ queueResizeVmDescriptor.constraints := by
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

/-! ## §8 — CONNECTOR to universe-A: the IR-supportable part agrees with `QueueResizeSpec`.

`QueueResizeSpec` asserts `st'.kernel.bal = st.kernel.bal` (the entire per-asset ledger frozen). We
project ONE `(cell, asset)` ledger entry and prove it is FROZEN across a committed resize — so the
descriptor's balance-freeze gate provably agrees with the executor. The FIFO record re-cap + occupancy
bound is the OUT-OF-IR leg (no column to carry it — §IR flag). -/

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

/-- **`unify_resize_balFrozen`** — across a committed `QueueResizeSpec` post-state, the projected
`(c, asset)` ledger entry is FROZEN (the IR-supportable `CellFreezeSpec`). So the descriptor's
balance-freeze gate IS `queueResizeA`'s genuine per-cell balance image. The FIFO re-cap is out-of-IR. -/
theorem unify_resize_balFrozen (st : RecChainedState) (id newCap : Nat) (actor cell : CellId)
    (st' : RecChainedState) (c : CellId) (asset : AssetId)
    (hspec : QueueResizeSpec st id newCap actor cell st') :
    CellFreezeSpec (cellProjBal st.kernel.bal c asset) (cellProjBal st'.kernel.bal c asset) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hbal, _⟩ := hspec
  refine ⟨?_, rfl, rfl, fun _ => rfl, rfl, rfl⟩
  show st'.kernel.bal c asset = st.kernel.bal c asset
  rw [hbal]

/-! ## §9 — NON-VACUITY. -/

/-- A concrete resize row: `bal_lo 50 → 50` (FROZEN), nonce 3 → 3, frame fixed at 0. -/
def goodResizeRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_QUEUE_RESIZE then 1
    else if v = sbCol state.BALANCE_LO then 50
    else if v = saCol state.BALANCE_LO then 50
    else if v = sbCol state.NONCE then 3
    else if v = saCol state.NONCE then 3
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `goodResizeRow` REALIZES the resize intent: the cell is frozen. -/
theorem goodResizeRow_realizes_intent : QueueResizeRowIntent goodResizeRow := by
  unfold QueueResizeRowIntent goodResizeRow
  simp only [sbCol, saCol, SEL_QUEUE_RESIZE, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE]
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro i hi
  have e1 : (76 + (3 + i) = 4) = False := by simp; omega
  have e2 : (76 + (3 + i) = 54) = False := by simp; omega
  have e3 : (76 + (3 + i) = 76) = False := by simp
  have e4 : (76 + (3 + i) = 56) = False := by simp; omega
  have e5 : (76 + (3 + i) = 78) = False := by simp; omega
  have f1 : (54 + (3 + i) = 4) = False := by simp; omega
  have f2 : (54 + (3 + i) = 54) = False := by simp
  have f3 : (54 + (3 + i) = 76) = False := by simp; omega
  have f4 : (54 + (3 + i) = 56) = False := by simp; omega
  have f5 : (54 + (3 + i) = 78) = False := by simp; omega
  simp only [e1, e2, e3, e4, e5, f1, f2, f3, f4, f5, if_false]

/-- A FORGED resize row: `goodResizeRow` with the post-`bal_lo` moved to `999` (resize is balance-neutral). -/
def badResizeRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodResizeRow.loc v
  nxt := goodResizeRow.nxt
  pub := goodResizeRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badResizeRow`'s post-`bal_lo` moved, so the
`gBalLoFreeze` gate REJECTS it — a concrete UNSAT. -/
theorem badResizeRow_rejected : ¬ (VmConstraint.gate gBalLoFreeze).holdsVm badResizeRow false false := by
  apply queueResizeVm_rejects_moved_balance
  simp only [badResizeRow, goodResizeRow, sbCol, saCol, SEL_QUEUE_RESIZE, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE]
  norm_num

/-! ## §10 — Axiom-hygiene pins. -/

#guard queueResizeVmDescriptor.constraints.length == 13 + 14 + 4 + 3
#guard queueResizeVmDescriptor.hashSites.length == 4
#guard queueResizeVmDescriptor.traceWidth == 186

#assert_axioms queueResizeVm_faithful
#assert_axioms queueResizeVm_rejects_wrong_output
#assert_axioms queueResizeVm_rejects_moved_balance
#assert_axioms intent_to_cellFreezeSpec
#assert_axioms queueResizeDescriptor_full_sound
#assert_axioms queueResizeDescriptor_commit_binds_state
#assert_axioms unify_resize_balFrozen
#assert_axioms goodResizeRow_realizes_intent
#assert_axioms badResizeRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitQueueResize
