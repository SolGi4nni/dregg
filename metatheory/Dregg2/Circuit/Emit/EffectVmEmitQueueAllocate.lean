/-
# Dregg2.Circuit.Emit.EffectVmEmitQueueAllocate — the `queueAllocateA` (FIFO-queue ALLOCATE) effect's
EffectVM emission, through the SAME `EffectVmEmit` IR as transfer.

Universe A (`Inst/queueAllocateA.lean`, `Spec/queuefifocore.lean`) carries the FULL-state soundness
`queueAllocateA_full_sound ⇒ QueueAllocateSpec`: a committed allocate PREPENDS one fresh `QueueRecord`
(`owner := actor`, empty buffer, the given capacity) onto the `queues` side-table, advances the chained
`log` by the allocate receipt, and FREEZES the other 16 kernel fields (NO balance move — balance-NEUTRAL).

## What the EffectVM IR (a 14-column per-cell state block + GROUP-4 commitment) DOES support

`queueAllocateA` is balance-NEUTRAL: it moves NO value on the per-asset `bal` ledger. On the EffectVM
row, the representing cell's `state.BALANCE_LO`/`BALANCE_HI` limbs are UNCHANGED, the nonce is FROZEN
(the executor does not tick it — `queueAllocateChainA` rewrites only `queues` + `log`), and the whole
frame (cap_root, reserved, the 8 fields) is frozen. The IR carries this NO-OP-cell shape totally — the
balance/nonce/frame freeze gates ++ the GROUP-4 commitment chain binding the (unchanged) after-state
block into `state_commit` exactly as for transfer.

## THE IR-EXTENSION FLAG (the FIFO-queue set-membership leg — the WHOLE point of allocate)

`QueueAllocateSpec`'s load-bearing clause is `st'.kernel.queues = freshQueue id actor cap :: st.queues`
— a PREPEND onto a `List QueueRecord` whose digest universe A binds via `listComponent`/`listDigest`
(`listLeafInjective LE` + `compressNInjective cN`, so a drop/REORDER of an existing queue record is
REJECTED, not just "the list grew"). This is a MERKLE/ACCUMULATOR MEMBERSHIP + LIST-ORDER property.

The EffectVM 14-column state block (`state.BALANCE_LO/HI`, `state.NONCE`, the 8 `state.FIELD_BASE+i`,
`state.CAP_ROOT`, `state.STATE_COMMIT`, `state.RESERVED`) has NO queue-list-root column, and the four
GROUP-4 hash-sites absorb NONE of the `queues` list. So the IR as it stands CANNOT bind the FIFO-list
prepend into `state_commit`, and CANNOT express the FIFO ORDER of the buffer.

  ⇒ **needs IR extension: a queue-side-table-root column in the EffectVM state block (a data column,
     e.g. repurposing one named field as `QUEUE_ROOT`) absorbed by a NEW hash-site that is a
     MERKLE/LIST-ACCUMULATOR over the `List QueueRecord` (matching universe A's `listDigest LE`), so
     the prepended fresh record (and the preserved order of the prior records) is bound into the
     published `state_commit`. The current IR has NO set-membership / list-accumulator gate-kind — only
     gate/transition/boundary/piBinding/hashSite(fixed-arity-per-row)/range.**

`queueAllocateA` is therefore **IR-BLOCKED for its load-bearing list leg**. This module proves what the
IR DOES support (the balance-neutral no-op cell + 14-column commitment) and reports the queue-list
prepend/order binding as out-of-IR — NOT papered, NOT faked with a vacuous gate.

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
  (eSB eSA ePrm eSub gBalHi gCapPass gResPass gFieldPass gFieldPassAll
   transitionAll boundaryFirstPins boundaryLastPins
   transferHashSites transferHash_binds boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState absorbedCols absorbed_determined_by_commit)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option linter.unusedVariables false

/-! ## §0 — The queueAllocate selector + the (no) balance move.

The EffectVM layout names `sel.NOOP = 0` / `sel.TRANSFER = 1`; queueAllocate takes its own selector
column (a LAYOUT CHOICE local to this descriptor — the running prover's `columns.rs` would assign it).
queueAllocate makes NO balance move, so the balance-lo gate is a FREEZE (not a debit/credit). -/

/-- The queueAllocate selector column index. -/
def SEL_QUEUE_ALLOCATE : Nat := 3

/-- The allocate row: `s_queue_allocate = 1`, `s_noop = 0`. -/
def IsQueueAllocateRow (env : VmRowEnv) : Prop :=
  env.loc SEL_QUEUE_ALLOCATE = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — The per-row gate bodies (balance-NEUTRAL no-op cell: FULL state freeze).

* `gBalLoFreeze` — `new_bal_lo − old_bal_lo = 0` (the limb is UNCHANGED; allocate moves no value).
* `gNonceFreeze` — `new_nonce − old_nonce = 0` (FROZEN; the executor does NOT tick the nonce).
* `gBalHi`/`gCapPass`/`gResPass`/`gFieldPass i` — REUSED from the transfer template (all frozen). -/

/-- Balance-lo FREEZE body: `new_bal_lo − old_bal_lo`. -/
def gBalLoFreeze : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)

/-- Nonce-FREEZE body: `new_nonce − old_nonce`. -/
def gNonceFreeze : EmittedExpr := eSub (eSA state.NONCE) (eSB state.NONCE)

/-! ## §2 — The emitted queueAllocate descriptor. -/

/-- The queueAllocate AIR identity. -/
def queueAllocateVmAirName : String := "dregg-effectvm-queueallocate-v1"

/-- The allocate per-row gates: balance-lo freeze, bal_hi freeze, nonce freeze, cap/reserved freeze,
8 fields freeze. The whole cell is frozen (allocate touches only the out-of-IR `queues` table). -/
def queueAllocateRowGates : List VmConstraint :=
  [ .gate gBalLoFreeze, .gate gBalHi, .gate gNonceFreeze
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-- **`queueAllocateVmDescriptor`** — the IR-supportable part of queueAllocate: the per-row full-state
freeze gates ++ transition continuity ++ the 7 boundary PI pins, with the 4 ordered GROUP-4 hash sites
(REUSED — the post-state commitment chain is the SAME 14-column binding) and the 2 balance-limb range
checks. NOTE: this descriptor binds ONLY the representing cell's (unchanged) content; the FIFO-queue
list prepend is OUT-OF-IR (see the §IR-extension flag in the header). -/
def queueAllocateVmDescriptor : EffectVmDescriptor :=
  { name := queueAllocateVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := queueAllocateRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The queueAllocate ROW INTENT (the IR-supportable faithfulness target).

`QueueAllocateRowIntent env`: on an allocate row, the cell is UNCHANGED — both balance limbs, the nonce,
and the whole frame (cap/reserved/8 fields) are FIXED. This is the EffectVM-row projection of the
balance-NEUTRAL nature of allocate (no `bal` move) + nonce-freeze + frame-freeze. It does NOT (cannot)
express the FIFO-list prepend — that is the out-of-IR leg. -/

/-- **`QueueAllocateRowIntent env`** — the IR-supportable allocate move: the representing cell frozen. -/
def QueueAllocateRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the (IR-supportable) intent. -/

/-- **`queueAllocateVm_faithful`.** On an allocate row, the emitted descriptor's per-row gates all hold
IFF `QueueAllocateRowIntent` holds — the gates pin EXACTLY the balance-neutral full-cell freeze. -/
theorem queueAllocateVm_faithful (env : VmRowEnv) :
    (∀ c ∈ queueAllocateRowGates, c.holdsVm env false false) ↔ QueueAllocateRowIntent env := by
  unfold queueAllocateRowGates gFieldPassAll QueueAllocateRowIntent
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

/-! ## §5 — ANTI-GHOST: a row whose cell is NOT frozen fails the emitted descriptor. -/

/-- **Anti-ghost (general).** A row whose cell is NOT held frozen (a value moved that allocate must
leave alone) does NOT satisfy the per-row gates. -/
theorem queueAllocateVm_rejects_wrong_output (env : VmRowEnv)
    (hwrong : ¬ QueueAllocateRowIntent env) :
    ¬ (∀ c ∈ queueAllocateRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((queueAllocateVm_faithful env).mp h)

/-- **Anti-ghost (balance tamper).** A row whose post-`bal_lo` differs from the pre (allocate must
leave the ledger entry alone) has no satisfying gate set — `gBalLoFreeze` alone rejects it. -/
theorem queueAllocateVm_rejects_moved_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (VmConstraint.gate gBalLoFreeze).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-! ## §6 — The structured per-cell spec + descriptor soundness (REUSING `CellState`). -/

/-- `RowEncodesNoop env pre post` ties the row's state-block columns to a frozen `(pre, post)` cell
transition (allocate carries NO param of interest — the queue args live OUTSIDE the EffectVM cell). -/
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

/-- **`CellFreezeSpec pre post`** — the per-cell FULL-state freeze: the representing cell is UNCHANGED
on every data column (both balance limbs, nonce, the 8 fields, cap_root, reserved). This is the
EffectVM-row projection of allocate's balance-neutral, cell-untouched nature. -/
def CellFreezeSpec (pre post : CellState) : Prop :=
  post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

/-- Decode lemma: under `RowEncodesNoop`, `QueueAllocateRowIntent` IS the structured `CellFreezeSpec`. -/
theorem intent_to_cellFreezeSpec (env : VmRowEnv) (pre post : CellState)
    (henc : RowEncodesNoop env pre post) (hint : QueueAllocateRowIntent env) :
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

/-- **`queueAllocateDescriptor_full_sound`** — satisfying the WHOLE runnable descriptor (gates +
transitions + boundaries + hash sites), under the `RowEncodesNoop` decoding, forces the structured
per-cell `CellFreezeSpec` AND publishes the post-commit as `PI[NEW_COMMIT]`. (The FIFO-list prepend is
out-of-IR — this binds ONLY the representing cell.) -/
theorem queueAllocateDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState)
    (henc : RowEncodesNoop env pre post)
    (hsat : satisfiedVm hash queueAllocateVmDescriptor env true true) :
    CellFreezeSpec pre post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates' : ∀ c ∈ queueAllocateRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ queueAllocateVmDescriptor.constraints := by
      unfold queueAllocateVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hc))
    have := hcs c hmem
    unfold queueAllocateRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (queueAllocateVm_faithful env).mp hgates'
  refine ⟨intent_to_cellFreezeSpec env pre post henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ queueAllocateVmDescriptor.constraints := by
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
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]; exact hpin

/-! ## §7 — The anti-ghost commitment tooth (REUSED — hash sites identical to transfer). -/

/-- **`queueAllocateDescriptor_commit_binds_state`** — two descriptor-satisfying allocate rows
publishing the SAME `NEW_COMMIT` (under `Poseidon2SpongeCR`) have identical absorbed state-block
columns. So a prover cannot keep `NEW_COMMIT` while tampering any absorbed cell. (This binds the
representing cell's content; the queue-list digest would need its own absorbed column — §IR flag.) -/
theorem queueAllocateDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash queueAllocateVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash queueAllocateVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ transferHashSites := hsat₁.2
  have hs₂ : siteHoldsAll hash e₂ transferHashSites := hsat₂.2
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash queueAllocateVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ queueAllocateVmDescriptor.constraints := by
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

/-! ## §8 — CONNECTOR to universe-A: the IR-supportable part agrees with `QueueAllocateSpec`.

`QueueAllocateSpec` asserts `st'.kernel.bal = st.kernel.bal` (the ENTIRE per-asset ledger frozen — a
balance-NEUTRAL effect). We project ONE `(cell, asset)` ledger entry into the keystone `CellState`'s
`balLo` limb and prove that ledger entry is FROZEN across a committed allocate (the IR-supportable
`CellFreezeSpec.balLo` clause) — so the descriptor's balance-freeze gate provably agrees with the
executor. The FIFO-list prepend (`st'.queues = freshQueue :: st.queues`) is the OUT-OF-IR leg; we do
NOT connect it (no column to carry it — §IR flag). -/

open Dregg2.Circuit.Spec.QueueFifoCore
open Dregg2.Exec

/-- Project the `(c, asset)` per-asset ledger entry into the keystone `CellState`'s `balLo` limb (the
conserved measure). The EffectVM limbs with no universe-A analogue on the ledger entry are `0`. -/
def cellProjBal (bal : CellId → AssetId → ℤ) (c : CellId) (asset : AssetId) : CellState where
  balLo    := bal c asset
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`unify_allocate_balFrozen`** — across a committed `QueueAllocateSpec` post-state, the projected
`(c, asset)` ledger entry is FROZEN (the IR-supportable `CellFreezeSpec`). So the descriptor's
balance-freeze gate IS `queueAllocateA`'s genuine per-cell balance image — NOT a fourth spec. The
queue-list prepend is out-of-IR. -/
theorem unify_allocate_balFrozen (st : RecChainedState) (id : Nat) (actor cell : CellId) (cap : Nat)
    (st' : RecChainedState) (c : CellId) (asset : AssetId)
    (hspec : QueueAllocateSpec st id actor cell cap st') :
    CellFreezeSpec (cellProjBal st.kernel.bal c asset) (cellProjBal st'.kernel.bal c asset) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hbal, _⟩ := hspec
  refine ⟨?_, rfl, rfl, fun _ => rfl, rfl, rfl⟩
  show st'.kernel.bal c asset = st.kernel.bal c asset
  rw [hbal]

/-! ## §9 — NON-VACUITY: a concrete frozen-cell row realizes the intent; a forged one is rejected. -/

/-- A concrete allocate row: `bal_lo 100 → 100` (FROZEN), nonce 7 → 7 (frozen), frame fixed at 0. -/
def goodAllocRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_QUEUE_ALLOCATE then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 100
    else if v = sbCol state.NONCE then 7
    else if v = saCol state.NONCE then 7
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `goodAllocRow` REALIZES the allocate intent: the cell is frozen
(`bal_lo 100 → 100`, nonce `7 → 7`, frame fixed). -/
theorem goodAllocRow_realizes_intent : QueueAllocateRowIntent goodAllocRow := by
  unfold QueueAllocateRowIntent goodAllocRow
  simp only [sbCol, saCol, SEL_QUEUE_ALLOCATE, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE]
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro i hi
  have e1 : (76 + (3 + i) = 3) = False := by simp; omega
  have e2 : (76 + (3 + i) = 54) = False := by simp; omega
  have e3 : (76 + (3 + i) = 76) = False := by simp
  have e4 : (76 + (3 + i) = 56) = False := by simp; omega
  have e5 : (76 + (3 + i) = 78) = False := by simp; omega
  have f1 : (54 + (3 + i) = 3) = False := by simp; omega
  have f2 : (54 + (3 + i) = 54) = False := by simp
  have f3 : (54 + (3 + i) = 76) = False := by simp; omega
  have f4 : (54 + (3 + i) = 56) = False := by simp; omega
  have f5 : (54 + (3 + i) = 78) = False := by simp; omega
  simp only [e1, e2, e3, e4, e5, f1, f2, f3, f4, f5, if_false]

/-- A FORGED allocate row: `goodAllocRow` with the post-`bal_lo` moved to `999` (allocate must NOT move
the ledger — balance-neutral). -/
def badAllocRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodAllocRow.loc v
  nxt := goodAllocRow.nxt
  pub := goodAllocRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badAllocRow`'s post-`bal_lo` moved, so the
`gBalLoFreeze` gate REJECTS it — a concrete UNSAT (allocate is balance-neutral). -/
theorem badAllocRow_rejected : ¬ (VmConstraint.gate gBalLoFreeze).holdsVm badAllocRow false false := by
  apply queueAllocateVm_rejects_moved_balance
  simp only [badAllocRow, goodAllocRow, sbCol, saCol, SEL_QUEUE_ALLOCATE, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE]
  norm_num

/-! ## §10 — Axiom-hygiene pins. -/

#guard queueAllocateVmDescriptor.constraints.length == 13 + 14 + 4 + 3
#guard queueAllocateVmDescriptor.hashSites.length == 4
#guard queueAllocateVmDescriptor.traceWidth == 186

#assert_axioms queueAllocateVm_faithful
#assert_axioms queueAllocateVm_rejects_wrong_output
#assert_axioms queueAllocateVm_rejects_moved_balance
#assert_axioms intent_to_cellFreezeSpec
#assert_axioms queueAllocateDescriptor_full_sound
#assert_axioms queueAllocateDescriptor_commit_binds_state
#assert_axioms unify_allocate_balFrozen
#assert_axioms goodAllocRow_realizes_intent
#assert_axioms badAllocRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitQueueAllocate
