/-
# Dregg2.Circuit.Emit.EffectVmEmitSetVK — the VERIFICATION-KEY effect `setVKA`, EMITTED onto the runnable
  EffectVM row, RECONCILED onto the RUNNING hand-AIR's columns (cutover convention) and GRADUATED into the
  descriptor cutover (v2).

## THE RUNTIME GROUND TRUTH (the cutover-faithful reconciliation, v2)

The running prover (`circuit/src/effect_vm/air.rs:961-980`) runs `setVerificationKey` (selector 27) as a
**state-passthrough** row: it asserts EVERY state-block column is UNCHANGED (`new_bal_lo == old_bal_lo`,
`bal_hi`, `new_cap_root == old_cap_root`, and ALL 8 `field[i]` frozen) and the GLOBAL nonce gate
(`new_nonce == old_nonce + (1 − s_noop)`, `air.rs`) TICKS the nonce by 1 on this non-NoOp row. The VK
value LIVES OFF-TRACE: the trace arm (`trace.rs:584`) anchors `vk_hash[0]` into `params[0]` and binds the
full 8-limb VK digest via `compute_effects_hash` — the AIR carries NO `field` column for the VK.

So the cutover-faithful row is the FROZEN-FRAME + NONCE-TICK shape (the cellDestroy / createSealPair
gauntlet): every economic state-block column frozen, the nonce ticks, the post-state bound into
`state_commit` (GROUP-4) with the full last-row balance PI pins. The PRE-v2 descriptor emitted a
`field[0]` MOVE gate (`new_field0 - vkNew`) that the runtime hand-AIR does NOT enforce (the hand-AIR
FREEZES `field[0]`), and FROZE the nonce — so the honest TICKED+field-frozen trace was UNSAT under it.
This v2 reconciles the descriptor to the runtime passthrough+tick.

## What the EffectVM row CAN pin (honest)

  * the cell's economic block (bal/fields/cap/reserved) is FROZEN; the nonce TICKS by 1;
  * the post-state is bound into `state_commit` (GROUP-4) and published as `NEW_COMMIT`.

## What the EffectVM row CANNOT enforce (the boundary)

  * the actual `verification_key` slot write — it rides `params[0]` + `effects_hash` OFF the per-row
    state block (the hand-AIR carries no VK `field` column). The VK-write soundness lives in universe-A's
    `SetVKSpec` (cited via the §connector); the runnable row pins the conserved frame + nonce tick.

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Poseidon2 CR = NAMED hypothesis. No sorry /
:= True / native_decide / rfl-bridge. Imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.cellstatevk

namespace Dregg2.Circuit.Emit.EffectVmEmitSetVK

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA eSub eSelNoop gBalHi gNonce gCapPass gResPass gFieldPass gFieldPassAll
   transitionAll boundaryFirstPins boundaryLastPins
   transferHashSites boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState RowEncodes absorbedCols absorbed_determined_by_commit)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec
open Dregg2.Exec.EffectsState
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Spec.CellStateVK

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — Selector for the setVK row (runtime `sel::SET_VERIFICATION_KEY = 27`). -/

/-- The `setVerificationKey` selector column index (runtime `sel::SET_VERIFICATION_KEY = 27`). -/
def SEL_SET_VK : Nat := 27

/-- The setVK row: `s_set_vk = 1`, `s_noop = 0` (load-bearing for the nonce TICK gate). -/
def IsSetVKRow (env : VmRowEnv) : Prop :=
  env.loc SEL_SET_VK = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — The per-row gate bodies (RUNTIME-RECONCILED: state-block passthrough + nonce TICK). -/

/-- Balance-lo FREEZE body: `new_bal_lo − old_bal_lo` (a VK write moves no value; runtime passthrough). -/
def gBalLoFreeze : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)

/-- The per-row gates: whole state block PASSTHROUGH + nonce TICK (`gNonce`, runtime convention). -/
def setVKRowGates : List VmConstraint :=
  [ .gate gBalLoFreeze, .gate gBalHi, .gate gNonce
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-! ## §2 — The emitted SET-VK descriptor (v2 = runtime-reconciled, last-row PI pins). -/

def setVKVmAirName : String := "dregg-effectvm-setVK-v2"

def setVKHashSites : List VmHashSite := transferHashSites

/-- **`setVKVmDescriptor`** — the `setVKA` EffectVM-row circuit, RECONCILED onto the runtime hand-AIR:
the per-row passthrough gates with the nonce TICK ++ transition continuity ++ the 7 boundary PI pins
(incl. the last-row `FINAL_BAL_LO`/`FINAL_BAL_HI`/`NEW_COMMIT`), the 4 ordered GROUP-4 hash sites and the
2 balance-limb range checks. -/
def setVKVmDescriptor : EffectVmDescriptor :=
  { name := setVKVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 42
  , constraints := setVKRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                     ++ selectorGates 27
  , hashSites := setVKHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The SET-VK ROW INTENT: state-block passthrough + nonce TICK (runtime-faithful). -/

/-- **`SetVKRowIntent env`** — every economic state-block column UNCHANGED EXCEPT the nonce, which TICKS
by 1 (on a non-NoOp row `s_noop = 0`). The VK-slot write is OFF-row (the §connector). -/
def SetVKRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the runtime-reconciled intent. -/

theorem setVKVm_faithful (env : VmRowEnv) :
    (∀ c ∈ setVKRowGates, c.holdsVm env false false) ↔ SetVKRowIntent env := by
  unfold setVKRowGates gFieldPassAll SetVKRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoFreeze) (by simp)
    have hHi := h (.gate gBalHi) (by simp)
    have hNon := h (.gate gNonce) (by simp)
    have hCap := h (.gate gCapPass) (by simp)
    have hRes := h (.gate gResPass) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldPass i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoFreeze, gBalHi, gNonce, gCapPass, gResPass,
      eSA, eSB, eSub, eSelNoop, EmittedExpr.eval] at hLo hHi hNon hCap hRes
    refine ⟨by linarith [hLo], by linarith [hHi], by linarith [hNon], by linarith [hCap],
      by linarith [hRes], ?_⟩
    intro i hi
    have := hFld i hi
    simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval] at this
    linarith
  · rintro ⟨hLo, hHi, hNon, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]; rw [hLo]; ring
    · simp only [VmConstraint.holdsVm, gBalHi, eSA, eSB, eSub, EmittedExpr.eval]; rw [hHi]; ring
    · simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
      rw [hNon]; ring
    · simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]; rw [hCap]; ring
    · simp only [VmConstraint.holdsVm, gResPass, eSA, eSB, eSub, EmittedExpr.eval]; rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hFld i hi]; ring

/-! ## §5 — ANTI-GHOST. -/

theorem setVKVm_rejects_wrong_output (env : VmRowEnv) (hwrong : ¬ SetVKRowIntent env) :
    ¬ (∀ c ∈ setVKRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((setVKVm_faithful env).mp h)

/-- **Anti-ghost (balance moved).** A row whose post-`bal_lo` ≠ pre-`bal_lo` fails the freeze gate — a VK
write cannot silently move value. -/
theorem setVKVm_rejects_moved_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (VmConstraint.gate gBalLoFreeze).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
  intro h; apply hwrong; linarith

/-- **Anti-ghost (nonce tamper).** A row whose nonce does NOT tick by 1 fails the reconciled `gNonce`
tick gate — a frozen-nonce trace (the pre-v2 convention) is now correctly UNSAT. -/
theorem setVKVm_rejects_nonce_freeze (env : VmRowEnv)
    (hwrong : env.loc (saCol state.NONCE) ≠ env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)) :
    ¬ (VmConstraint.gate gNonce).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
  intro h; apply hwrong; linarith

/-! ## §6 — the commitment binding (REUSED; hash sites identical to transfer's). -/

theorem setVK_sites_eq : setVKVmDescriptor.hashSites = transferHashSites := rfl

theorem setVKDescriptor_commit_binds_block (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ setVKHashSites)
    (hs₂ : siteHoldsAll hash e₂ setVKHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ :=
  absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §7 — the structured per-cell spec (REUSING `CellState`): passthrough + nonce tick. -/

/-- `RowEncodesVK env pre post` ties the row's state-block columns to a `(pre, post)` transition. -/
def RowEncodesVK (env : VmRowEnv) (pre post : CellState) : Prop :=
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

/-- **`CellSetVKSpec pre post`** — the per-cell FULL-state setVK row spec: economic block FROZEN; the
nonce TICKS by 1. (The VK-slot write is OFF-row — the §connector.) -/
def CellSetVKSpec (pre post : CellState) : Prop :=
  post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce + 1
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

theorem intent_to_cellSpec (env : VmRowEnv) (pre post : CellState)
    (hnoop : env.loc sel.NOOP = 0)
    (henc : RowEncodesVK env pre post) (hint : SetVKRowIntent env) :
    CellSetVKSpec pre post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsaLo, ← hsbLo]; exact hbal
  · rw [← hsaHi, ← hsbHi]; exact hbhi
  · rw [← hsaN, ← hsbN, hnon, hnoop]; ring
  · intro i
    have := hfld i.val i.isLt
    rw [← hsaF i, ← hsbF i]; exact this
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres

/-! ## §8 — the full descriptor soundness + the commitment binding. -/

theorem setVKDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (hnoop : env.loc sel.NOOP = 0)
    (henc : RowEncodesVK env pre post)
    (hgatesat : satisfiedVm hash setVKVmDescriptor env true false)
    (hsat : satisfiedVm hash setVKVmDescriptor env true true) :
    CellSetVKSpec pre post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  obtain ⟨hcsT, _⟩ := hgatesat
  -- the per-row gates run under `when_transition()`, so their content is at the ACTIVE row
  -- (`isLast = false`), drawn from `hgatesat`; the last-row commit pin is from `hsat`.
  have hgates' : ∀ c ∈ setVKRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ setVKVmDescriptor.constraints := by
      unfold setVKVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
    have := hcsT c hmem
    unfold setVKRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (setVKVm_faithful env).mp hgates'
  refine ⟨intent_to_cellSpec env pre post hnoop henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ setVKVmDescriptor.constraints := by
      unfold setVKVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inr hc)
    have hh := hcs c hmem
    unfold boundaryLastPins at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      · simp only [VmConstraint.holdsVm] at hh ⊢
        exact hh
  have hpin := (boundaryLast_pins env hlast).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]; exact hpin

theorem setVKDescriptor_commit_binds_state (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash setVKVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash setVKVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ setVKHashSites := hsat₁.2.1
  have hs₂ : siteHoldsAll hash e₂ setVKHashSites := hsat₂.2.1
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash setVKVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ setVKVmDescriptor.constraints := by
        unfold setVKVmDescriptor
        simp only [List.mem_append]
        exact Or.inl (Or.inr hc)
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

/-! ## §9 — THE CONNECTOR — `cellProjV` to universe-A's `SetVKSpec` (conserved-balance freeze). -/

/-- Read cell `c`'s conserved economic balance out of the real record-kernel state. -/
def cellProjV (k : RecordKernelState) (c : CellId) : CellState where
  balLo    := balOf (k.cell c)
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`setVK_balance_frozen` — the OVERLAP, from the executor.** A committed `setVKA` freezes the cell's
conserved economic balance (the VK write rewrites only the `verification_key` slot). -/
theorem setVK_balance_frozen (s s' : RecChainedState) (actor cell : CellId) (vk : Int)
    (hspec : SetVKSpec s actor cell vk s') :
    (cellProjV s'.kernel cell).balLo = (cellProjV s.kernel cell).balLo := by
  show balOf (s'.kernel.cell cell) = balOf (s.kernel.cell cell)
  rw [hspec.2.1]
  exact (setVK_cellWrite_correct s.kernel cell vk).2.1

/-- **`vk_write_is_out_of_row` — the honest finding (universe-A leg).** A committed `setVKA` writes the
cell's `verification_key` slot to exactly `vk` (`setVK_cellWrite_correct`). This slot write is a
universe-A property; the RUNNABLE descriptor binds only the on-trace conserved frame (the runtime's
hand-AIR carrier), since the hand-AIR has no VK `field` column (the VK rides `params[0]` + effects_hash).
The §connector connects to the slot write. -/
theorem vk_write_is_out_of_row (s s' : RecChainedState) (actor cell : CellId) (vk : Int)
    (hspec : SetVKSpec s actor cell vk s') :
    fieldOf vkField (s'.kernel.cell cell) = (vk : ℤ) := by
  rw [hspec.2.1]
  exact (setVK_cellWrite_correct s.kernel cell vk).1

/-- **`descriptor_agrees_with_executor_setVK`** — a satisfying run of the runnable descriptor encoding the
touched cell agrees with the executor's post-state on the FROZEN balance dimension (`balLo`); the
nonce-tick is the runtime cell-bookkeeping leg (off universe-A state). -/
theorem descriptor_agrees_with_executor_setVK
    (hash : List ℤ → ℤ) (env : VmRowEnv) (hnoop : env.loc sel.NOOP = 0)
    (s s' : RecChainedState) (actor cell : CellId) (vk : Int) (pre post : CellState)
    (hpre : pre = cellProjV s.kernel cell)
    (henc : RowEncodesVK env pre post)
    (hgatesat : satisfiedVm hash setVKVmDescriptor env true false)
    (hsat : satisfiedVm hash setVKVmDescriptor env true true)
    (hspec : SetVKSpec s actor cell vk s') :
    post.balLo = (cellProjV s'.kernel cell).balLo := by
  obtain ⟨hcirc, _⟩ := setVKDescriptor_full_sound hash env pre post hnoop henc hgatesat hsat
  obtain ⟨hcLo, _, _, _, _, _⟩ := hcirc
  have heLo := setVK_balance_frozen s s' actor cell vk hspec
  subst hpre
  rw [hcLo, heLo]

/-! ## §10 — NON-VACUITY. -/

/-- A concrete setVK row: state-block passthrough + nonce TICK (bal_lo 100 → 100, nonce 5 → 6). -/
def goodSetVKRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_SET_VK then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 100
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 6
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

theorem goodSetVKRow_noop : goodSetVKRow.loc sel.NOOP = 0 := by
  show goodSetVKRow.loc 0 = 0
  simp only [goodSetVKRow, SEL_SET_VK, sbCol, saCol, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE]
  norm_num

/-- **NON-VACUITY (witness TRUE).** `goodSetVKRow` REALIZES the runtime setVK intent. -/
theorem goodSetVKRow_realizes_intent : SetVKRowIntent goodSetVKRow := by
  unfold SetVKRowIntent
  have hnoop : goodSetVKRow.loc sel.NOOP = 0 := goodSetVKRow_noop
  refine ⟨rfl, rfl, ?_, rfl, rfl, ?_⟩
  · rw [hnoop]
    show goodSetVKRow.loc (saCol state.NONCE) = goodSetVKRow.loc (sbCol state.NONCE) + (1 - 0)
    simp only [goodSetVKRow, SEL_SET_VK, sbCol, saCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE]
    norm_num
  · intro i hi
    show goodSetVKRow.loc (saCol (state.FIELD_BASE + i)) = goodSetVKRow.loc (sbCol (state.FIELD_BASE + i))
    simp only [goodSetVKRow, SEL_SET_VK, sbCol, saCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE, state.FIELD_BASE]
    have e1 : (76 + (3 + i) = 27) = False := eq_false (by omega)
    have e2 : (76 + (3 + i) = 54 + 0) = False := eq_false (by omega)
    have e3 : (76 + (3 + i) = 76 + 0) = False := eq_false (by omega)
    have e4 : (76 + (3 + i) = 54 + 2) = False := eq_false (by omega)
    have e5 : (76 + (3 + i) = 76 + 2) = False := eq_false (by omega)
    have f1 : (54 + (3 + i) = 27) = False := eq_false (by omega)
    have f2 : (54 + (3 + i) = 54 + 0) = False := eq_false (by omega)
    have f3 : (54 + (3 + i) = 76 + 0) = False := eq_false (by omega)
    have f4 : (54 + (3 + i) = 54 + 2) = False := eq_false (by omega)
    have f5 : (54 + (3 + i) = 76 + 2) = False := eq_false (by omega)
    simp only [e1, e2, e3, e4, e5, f1, f2, f3, f4, f5, if_false]

/-- A FORGED setVK row: `goodSetVKRow` with the post-`bal_lo` minted to `999`. -/
def badSetVKRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodSetVKRow.loc v
  nxt := goodSetVKRow.nxt
  pub := goodSetVKRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badSetVKRow`'s post-`bal_lo` is forged, so
`gBalLoFreeze` REJECTS it. -/
theorem badSetVKRow_rejected : ¬ (VmConstraint.gate gBalLoFreeze).holdsVm badSetVKRow false false := by
  apply setVKVm_rejects_moved_balance
  simp only [badSetVKRow, goodSetVKRow, sbCol, saCol, SEL_SET_VK, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE]
  norm_num

/-- A FROZEN-NONCE setVK row: `goodSetVKRow` with the post-nonce held at `5`. -/
def staleNonceSetVKRow : VmRowEnv where
  loc := fun v => if v = saCol state.NONCE then 5 else goodSetVKRow.loc v
  nxt := goodSetVKRow.nxt
  pub := goodSetVKRow.pub

/-- **NON-VACUITY (cutover witness FALSE).** A frozen-nonce row is now correctly UNSAT under the
reconciled `gNonce` tick gate. -/
theorem staleNonceSetVKRow_rejected :
    ¬ (VmConstraint.gate gNonce).holdsVm staleNonceSetVKRow false false := by
  apply setVKVm_rejects_nonce_freeze
  simp only [staleNonceSetVKRow, goodSetVKRow, sel.NOOP, sbCol, saCol, SEL_SET_VK,
    STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
    state.BALANCE_LO, state.NONCE]
  norm_num

/-! ## §11 — Axiom-hygiene tripwires. -/

#guard setVKVmDescriptor.constraints.length == 13 + 14 + 4 + 3 + 1
#guard setVKVmDescriptor.hashSites.length == 4
#guard setVKVmDescriptor.traceWidth == 188

#assert_axioms setVKVm_faithful
#assert_axioms setVKVm_rejects_wrong_output
#assert_axioms setVKVm_rejects_moved_balance
#assert_axioms setVKVm_rejects_nonce_freeze
#assert_axioms intent_to_cellSpec
#assert_axioms setVKDescriptor_full_sound
#assert_axioms setVKDescriptor_commit_binds_state
#assert_axioms setVK_balance_frozen
#assert_axioms vk_write_is_out_of_row
#assert_axioms descriptor_agrees_with_executor_setVK
#assert_axioms goodSetVKRow_realizes_intent
#assert_axioms badSetVKRow_rejected
#assert_axioms staleNonceSetVKRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitSetVK
