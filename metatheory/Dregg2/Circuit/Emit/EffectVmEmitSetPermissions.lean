/-
# Dregg2.Circuit.Emit.EffectVmEmitSetPermissions — the CELL-STATE-PERMISSIONS effect `setPermissionsA`,
  EMITTED onto the runnable EffectVM row, RECONCILED onto the RUNNING hand-AIR's columns (cutover
  convention) and GRADUATED into the descriptor cutover (v2).

## THE RUNTIME GROUND TRUTH (the cutover-faithful reconciliation, v2)

The running prover (`circuit/src/effect_vm/air.rs:939-960`) runs `setPermissions` (selector 26) as a
**state-passthrough** row: it asserts EVERY state-block column is UNCHANGED (`new_bal_lo == old_bal_lo`,
`bal_hi`, `new_cap_root == old_cap_root`, and ALL 8 `field[i]` frozen) and the GLOBAL nonce gate ticks
the nonce by 1 on this non-NoOp row. The permissions value LIVES OFF-TRACE: the trace arm
(`trace.rs:577`) anchors `permissions_hash[0]` into `params[0]` and binds the full 8-limb digest via
`compute_effects_hash` — the AIR carries NO `field` column for the permissions.

So the cutover-faithful row is the FROZEN-FRAME + NONCE-TICK shape (the cellDestroy / createSealPair
gauntlet). The PRE-v2 descriptor emitted a `field[0]` MOVE gate (`new_field0 - permsNew`) that the
runtime hand-AIR does NOT enforce (the hand-AIR FREEZES `field[0]`), and FROZE the nonce — so the honest
TICKED+field-frozen trace was UNSAT under it. This v2 reconciles the descriptor to the runtime
passthrough+tick.

## What the EffectVM row CAN pin (honest)

  * the cell's economic block (bal/fields/cap/reserved) is FROZEN; the nonce TICKS by 1;
  * the post-state is bound into `state_commit` (GROUP-4) and published as `NEW_COMMIT`.

## What the EffectVM row CANNOT enforce (the boundary)

  * the actual `permissions` slot write + the self-targeted receipt — they ride `params[0]` +
    `effects_hash` OFF the per-row state block. The write soundness lives in universe-A's
    `SetPermissionsSpec` (cited via the §connector); the runnable row pins the conserved frame + tick.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. Poseidon2 CR enters ONLY as
the NAMED hypothesis `Poseidon2SpongeCR hash`. No `sorry`, no `:= True`, no `native_decide`, no
`rfl`-posing-as-bridge. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.cellstatepermissions

namespace Dregg2.Circuit.Emit.EffectVmEmitSetPermissions

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

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — the `setPermissions` selector column (runtime `sel::SET_PERMISSIONS = 26`). -/

/-- The `setPermissions` selector column index (runtime `sel::SET_PERMISSIONS = 26`). -/
def SEL_SET_PERMS : Nat := 26

/-- The setPermissions row: `s_set_perms = 1`, `s_noop = 0` (load-bearing for the nonce TICK gate). -/
def IsSetPermsRow (env : VmRowEnv) : Prop :=
  env.loc SEL_SET_PERMS = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — the per-row gate bodies (RUNTIME-RECONCILED: state-block passthrough + nonce TICK). -/

/-- Balance-lo FREEZE body (a permissions write moves no value; runtime passthrough batch). -/
def gBalLoFreeze : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)

/-- The per-row gates: whole state block PASSTHROUGH + nonce TICK (`gNonce`, runtime convention). -/
def setPermsRowGates : List VmConstraint :=
  [ .gate gBalLoFreeze, .gate gBalHi, .gate gNonce
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-! ## §2 — the emitted descriptor (v2 = runtime-reconciled, last-row PI pins). -/

def setPermsVmAirName : String := "dregg-effectvm-setPermissionsA-v2"

def setPermsHashSites : List VmHashSite := transferHashSites

/-- **`setPermsVmDescriptor`** — the `setPermissionsA` EffectVM-row circuit, RECONCILED onto the runtime
hand-AIR: the per-row passthrough gates with the nonce TICK ++ transition continuity ++ the 7 boundary PI
pins, the 4 ordered GROUP-4 hash sites and the 2 balance-limb range checks. -/
def setPermsVmDescriptor : EffectVmDescriptor :=
  { name := setPermsVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := setPermsRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                     ++ selectorGates 26
  , hashSites := setPermsHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — the ROW INTENT: state-block passthrough + nonce TICK (runtime-faithful). -/

/-- **`SetPermsRowIntent env`** — every economic state-block column UNCHANGED EXCEPT the nonce, which
TICKS by 1 (on a non-NoOp row `s_noop = 0`). The permissions-slot write is OFF-row (the §connector). -/
def SetPermsRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the runtime-reconciled intent. -/

theorem setPermsVm_faithful (env : VmRowEnv) :
    (∀ c ∈ setPermsRowGates, c.holdsVm env false false) ↔ SetPermsRowIntent env := by
  unfold setPermsRowGates gFieldPassAll SetPermsRowIntent
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

theorem setPermsVm_rejects_wrong_output (env : VmRowEnv) (hwrong : ¬ SetPermsRowIntent env) :
    ¬ (∀ c ∈ setPermsRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((setPermsVm_faithful env).mp h)

/-- **Anti-ghost (balance moved).** A row whose post-`bal_lo` ≠ pre-`bal_lo` fails the freeze gate. -/
theorem setPermsVm_rejects_moved_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (VmConstraint.gate gBalLoFreeze).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
  intro h; apply hwrong; linarith

/-- **Anti-ghost (nonce tamper).** A row whose nonce does NOT tick by 1 fails the reconciled `gNonce`
tick gate — a frozen-nonce trace (the pre-v2 convention) is now correctly UNSAT. -/
theorem setPermsVm_rejects_nonce_freeze (env : VmRowEnv)
    (hwrong : env.loc (saCol state.NONCE) ≠ env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)) :
    ¬ (VmConstraint.gate gNonce).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
  intro h; apply hwrong; linarith

/-! ## §6 — the commitment binding (REUSED; hash sites identical to transfer's). -/

theorem setPermsHashSites_eq : setPermsHashSites = transferHashSites := rfl

theorem setPermsVm_commit_binds_block (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ setPermsHashSites)
    (hs₂ : siteHoldsAll hash e₂ setPermsHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ :=
  absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §7 — the structured per-cell spec (REUSING `CellState`): passthrough + nonce tick. -/

/-- `RowEncodesPerms env pre post` ties the row's state-block columns to a `(pre, post)` transition. -/
def RowEncodesPerms (env : VmRowEnv) (pre post : CellState) : Prop :=
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

/-- **`PermCellSpec pre post`** — the per-cell FULL-state setPermissions row spec: economic block FROZEN;
the nonce TICKS by 1. (The permissions-slot write is OFF-row — the §connector.) -/
def PermCellSpec (pre post : CellState) : Prop :=
  post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce + 1
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

theorem intent_to_permCellSpec (env : VmRowEnv) (pre post : CellState)
    (hnoop : env.loc sel.NOOP = 0)
    (henc : RowEncodesPerms env pre post) (hint : SetPermsRowIntent env) :
    PermCellSpec pre post := by
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

theorem setPermsDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (hnoop : env.loc sel.NOOP = 0)
    (henc : RowEncodesPerms env pre post)
    (hsat : satisfiedVm hash setPermsVmDescriptor env true true) :
    PermCellSpec pre post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates' : ∀ c ∈ setPermsRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ setPermsVmDescriptor.constraints := by
      unfold setPermsVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
    have := hcs c hmem
    unfold setPermsRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (setPermsVm_faithful env).mp hgates'
  refine ⟨intent_to_permCellSpec env pre post hnoop henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ setPermsVmDescriptor.constraints := by
      unfold setPermsVmDescriptor
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

theorem setPermsDescriptor_commit_binds_state (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash setPermsVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash setPermsVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ setPermsHashSites := hsat₁.2.1
  have hs₂ : siteHoldsAll hash e₂ setPermsHashSites := hsat₂.2.1
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash setPermsVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ setPermsVmDescriptor.constraints := by
        unfold setPermsVmDescriptor
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

/-! ## §9 — THE CONNECTOR — `cellProjP` to universe-A's `SetPermissionsSpec` (conserved-balance freeze). -/

open Dregg2.Circuit.Spec.CellStatePermissions
  (SetPermissionsSpec setPermsCellMap setPermissions_cellWrite_correct execFullA_setPermissions_iff_spec)

/-- Read cell `c`'s conserved economic balance out of the real record-kernel state. -/
def cellProjP (k : RecordKernelState) (c : CellId) : CellState where
  balLo    := balOf (k.cell c)
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`setPerms_balance_frozen` — the OVERLAP, from the executor.** A committed `setPermissionsA` freezes
the cell's conserved economic balance (the write rewrites only the `permissions` slot). -/
theorem setPerms_balance_frozen (s s' : RecChainedState) (actor cell : CellId) (p : Int)
    (hspec : SetPermissionsSpec s actor cell p s') :
    (cellProjP s'.kernel cell).balLo = (cellProjP s.kernel cell).balLo := by
  obtain ⟨_, hcell, _⟩ := hspec
  show balOf (s'.kernel.cell cell) = balOf (s.kernel.cell cell)
  rw [hcell]
  exact (setPermissions_cellWrite_correct s.kernel cell p).2.1

/-- **`perms_write_is_out_of_row` — the honest finding (universe-A leg).** A committed `setPermissionsA`
writes the cell's `permissions` slot to exactly `p` (`setPermissions_cellWrite_correct`). This slot write
is a universe-A property; the RUNNABLE descriptor binds only the on-trace conserved frame, since the
hand-AIR has no permissions `field` column (the value rides `params[0]` + effects_hash). -/
theorem perms_write_is_out_of_row (s s' : RecChainedState) (actor cell : CellId) (p : Int)
    (hspec : SetPermissionsSpec s actor cell p s') :
    fieldOf permsField (s'.kernel.cell cell) = (p : ℤ) := by
  obtain ⟨_, hcell, _⟩ := hspec
  rw [hcell]
  exact (setPermissions_cellWrite_correct s.kernel cell p).1

/-- **`descriptor_agrees_with_executor_setPerms`** — a satisfying run of the runnable descriptor encoding
the touched cell agrees with the executor's post-state on the FROZEN balance dimension (`balLo`); the
nonce-tick is the runtime cell-bookkeeping leg (off universe-A state). -/
theorem descriptor_agrees_with_executor_setPerms
    (hash : List ℤ → ℤ) (env : VmRowEnv) (hnoop : env.loc sel.NOOP = 0)
    (s s' : RecChainedState) (actor cell : CellId) (p : Int) (pre post : CellState)
    (hpre : pre = cellProjP s.kernel cell)
    (henc : RowEncodesPerms env pre post)
    (hsat : satisfiedVm hash setPermsVmDescriptor env true true)
    (hspec : SetPermissionsSpec s actor cell p s') :
    post.balLo = (cellProjP s'.kernel cell).balLo := by
  obtain ⟨hcirc, _⟩ := setPermsDescriptor_full_sound hash env pre post hnoop henc hsat
  obtain ⟨hcLo, _, _, _, _, _⟩ := hcirc
  have heLo := setPerms_balance_frozen s s' actor cell p hspec
  subst hpre
  rw [hcLo, heLo]

/-! ## §10 — NON-VACUITY. -/

/-- A concrete setPermissions row: state-block passthrough + nonce TICK (bal_lo 100 → 100, nonce 5 → 6). -/
def goodPermRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_SET_PERMS then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 100
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 6
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

theorem goodPermRow_noop : goodPermRow.loc sel.NOOP = 0 := by
  show goodPermRow.loc 0 = 0
  simp only [goodPermRow, SEL_SET_PERMS, sbCol, saCol, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE]
  norm_num

/-- **NON-VACUITY (witness TRUE).** `goodPermRow` REALIZES the runtime setPermissions intent. -/
theorem goodPermRow_realizes_intent : SetPermsRowIntent goodPermRow := by
  unfold SetPermsRowIntent
  have hnoop : goodPermRow.loc sel.NOOP = 0 := goodPermRow_noop
  refine ⟨rfl, rfl, ?_, rfl, rfl, ?_⟩
  · rw [hnoop]
    show goodPermRow.loc (saCol state.NONCE) = goodPermRow.loc (sbCol state.NONCE) + (1 - 0)
    simp only [goodPermRow, SEL_SET_PERMS, sbCol, saCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE]
    norm_num
  · intro i hi
    show goodPermRow.loc (saCol (state.FIELD_BASE + i)) = goodPermRow.loc (sbCol (state.FIELD_BASE + i))
    simp only [goodPermRow, SEL_SET_PERMS, sbCol, saCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE, state.FIELD_BASE]
    have e1 : (76 + (3 + i) = 26) = False := eq_false (by omega)
    have e2 : (76 + (3 + i) = 54 + 0) = False := eq_false (by omega)
    have e3 : (76 + (3 + i) = 76 + 0) = False := eq_false (by omega)
    have e4 : (76 + (3 + i) = 54 + 2) = False := eq_false (by omega)
    have e5 : (76 + (3 + i) = 76 + 2) = False := eq_false (by omega)
    have f1 : (54 + (3 + i) = 26) = False := eq_false (by omega)
    have f2 : (54 + (3 + i) = 54 + 0) = False := eq_false (by omega)
    have f3 : (54 + (3 + i) = 76 + 0) = False := eq_false (by omega)
    have f4 : (54 + (3 + i) = 54 + 2) = False := eq_false (by omega)
    have f5 : (54 + (3 + i) = 76 + 2) = False := eq_false (by omega)
    simp only [e1, e2, e3, e4, e5, f1, f2, f3, f4, f5, if_false]

/-- A FORGED setPermissions row: `goodPermRow` with the post-`bal_lo` minted to `999`. -/
def badPermRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodPermRow.loc v
  nxt := goodPermRow.nxt
  pub := goodPermRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badPermRow`'s post-`bal_lo` is forged, so
`gBalLoFreeze` REJECTS it. -/
theorem badPermRow_rejected : ¬ (VmConstraint.gate gBalLoFreeze).holdsVm badPermRow false false := by
  apply setPermsVm_rejects_moved_balance
  simp only [badPermRow, goodPermRow, sbCol, saCol, SEL_SET_PERMS, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE]
  norm_num

/-- A FROZEN-NONCE setPermissions row: `goodPermRow` with the post-nonce held at `5`. -/
def staleNoncePermRow : VmRowEnv where
  loc := fun v => if v = saCol state.NONCE then 5 else goodPermRow.loc v
  nxt := goodPermRow.nxt
  pub := goodPermRow.pub

/-- **NON-VACUITY (cutover witness FALSE).** A frozen-nonce row is now correctly UNSAT under the
reconciled `gNonce` tick gate. -/
theorem staleNoncePermRow_rejected :
    ¬ (VmConstraint.gate gNonce).holdsVm staleNoncePermRow false false := by
  apply setPermsVm_rejects_nonce_freeze
  simp only [staleNoncePermRow, goodPermRow, sel.NOOP, sbCol, saCol, SEL_SET_PERMS,
    STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
    state.BALANCE_LO, state.NONCE]
  norm_num

/-! ## §11 — Axiom-hygiene tripwires. -/

#guard setPermsVmDescriptor.constraints.length == 13 + 14 + 4 + 3 + 1
#guard setPermsVmDescriptor.hashSites.length == 4
#guard setPermsVmDescriptor.traceWidth == 186

#assert_axioms setPermsVm_faithful
#assert_axioms setPermsVm_rejects_wrong_output
#assert_axioms setPermsVm_rejects_moved_balance
#assert_axioms setPermsVm_rejects_nonce_freeze
#assert_axioms intent_to_permCellSpec
#assert_axioms setPermsDescriptor_full_sound
#assert_axioms setPermsDescriptor_commit_binds_state
#assert_axioms setPerms_balance_frozen
#assert_axioms perms_write_is_out_of_row
#assert_axioms descriptor_agrees_with_executor_setPerms
#assert_axioms goodPermRow_realizes_intent
#assert_axioms badPermRow_rejected
#assert_axioms staleNoncePermRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitSetPermissions
