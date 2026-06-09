/-
# Dregg2.Circuit.Emit.EffectVmEmitExercise — the composite hold-gate effect `exerciseA`'s OUTER layer,
  EMITTED onto the runnable EffectVM row, RECONCILED onto the RUNNING hand-AIR's columns (cutover
  convention) and GRADUATED into the descriptor cutover (v2).

## THE RUNTIME GROUND TRUTH (the cutover-faithful reconciliation, v2)

The running prover runs `exerciseViaCapability` (selector 34) as a member of the **Stage-3 passthrough
batch** (`air.rs:983-1018`): every economic state-block column UNCHANGED (`new_bal_lo == old_bal_lo`,
`bal_hi`, `cap_root`, `fields[0..7]` frozen) and the GLOBAL nonce gate TICKS the nonce by 1 on this
non-NoOp row. The variant `exercise_hash[0]` is parked into `params[0]` and binds via `compute_effects_hash`.

So the cutover-faithful row is the FROZEN-FRAME + NONCE-TICK shape (the cellDestroy gauntlet). The PRE-v2
descriptor FROZE the nonce (`gNonceFix`) and carried only `boundaryFirstPins` — so (a) the honest TICKED
trace was UNSAT and (b) the forged-`FINAL_BAL_LO` anti-ghost tooth did not bite. This v2 swaps the
nonce-freeze gate to the runtime TICK gate `gNonce` and appends `boundaryLastPins` (incl. the last-row
balance PI pins), so the descriptor AGREES with the hand-AIR on the honest witness AND both anti-ghost
teeth bite.

## What the EffectVM row CAN pin (honest)

  * the cell's economic block (bal/fields/cap/reserved) is FROZEN; the nonce TICKS by 1;
  * the post-state is bound into `state_commit` (GROUP-4) and published as `NEW_COMMIT`.

## What the EffectVM row CANNOT enforce (the honest boundary — the OUTER hold layer + inner fold)

  * the `authReceipt` log growth (no log column); the `exerciseGuard` cap-edge hold (v1 `propBit`,
    off-row); the INNER `List FullActionA` fold (each inner action is its OWN per-row descriptor,
    composed through the turn layer `TurnEmit`, cited). The hold-layer SOUNDNESS lives in
    `exerciseA_full_sound`; this module pins the conserved frame + nonce tick and connects to the
    validated kernel-freeze.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. Poseidon2 CR enters ONLY as
the NAMED hypothesis `Poseidon2SpongeCR hash`. No `sorry`, no `:= True`, no `native_decide`. Imports are
read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.ActionDispatch

namespace Dregg2.Circuit.Emit.EffectVmEmitExercise

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA eSub eSelNoop gBalHi gNonce gCapPass gResPass gFieldPass gFieldPassAll
   transitionAll boundaryFirstPins boundaryLastPins
   transferHashSites boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState absorbedCols absorbed_determined_by_commit)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — the `exerciseViaCapability` selector column (runtime `sel::EXERCISE_VIA_CAPABILITY = 34`). -/

/-- The exercise selector column index (runtime `sel::EXERCISE_VIA_CAPABILITY = 34`). -/
def SEL_EXERCISE : Nat := 34

/-- The exercise row: `s_exercise = 1`, `s_noop = 0` (load-bearing for the nonce TICK gate). -/
def IsExerciseRow (env : VmRowEnv) : Prop :=
  env.loc SEL_EXERCISE = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — the per-row gate bodies (RUNTIME-RECONCILED: state-block passthrough + nonce TICK). -/

/-- Balance-lo FREEZE body (the hold layer moves no value; runtime passthrough batch). -/
def gBalLoFreeze : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)

/-- The per-row gates: whole state block PASSTHROUGH + nonce TICK (`gNonce`, runtime convention). -/
def exerciseRowGates : List VmConstraint :=
  [ .gate gBalLoFreeze, .gate gBalHi, .gate gNonce
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-! ## §2 — the emitted descriptor (v2 = runtime-reconciled, last-row PI pins). -/

def exerciseVmAirName : String := "dregg-effectvm-exerciseA-holdlayer-v2"

def exerciseHashSites : List VmHashSite := transferHashSites

/-- **`exerciseVmDescriptor`** — the `exerciseA` hold-layer EffectVM-row circuit, RECONCILED onto the
runtime hand-AIR: the per-row passthrough gates with the nonce TICK ++ transition continuity ++ the 7
boundary PI pins, the 4 ordered GROUP-4 hash sites and the 2 balance-limb range checks. -/
def exerciseVmDescriptor : EffectVmDescriptor :=
  { name := exerciseVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := exerciseRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                     ++ selectorGates 34
  , hashSites := exerciseHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — the ROW INTENT: state-block passthrough + nonce TICK (runtime-faithful). -/

/-- **`ExerciseRowIntent env`** — every economic state-block column UNCHANGED EXCEPT the nonce, which
TICKS by 1 (on a non-NoOp row `s_noop = 0`). The hold-gate / log / inner fold are out-of-row. -/
def ExerciseRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the runtime-reconciled intent. -/

theorem exerciseVm_faithful (env : VmRowEnv) :
    (∀ c ∈ exerciseRowGates, c.holdsVm env false false) ↔ ExerciseRowIntent env := by
  unfold exerciseRowGates gFieldPassAll ExerciseRowIntent
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

theorem exerciseVm_rejects_wrong_output (env : VmRowEnv) (hwrong : ¬ ExerciseRowIntent env) :
    ¬ (∀ c ∈ exerciseRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((exerciseVm_faithful env).mp h)

/-- **Anti-ghost (balance moved).** A row whose post-`bal_lo` ≠ pre-`bal_lo` fails the freeze gate — a
hold step cannot silently move value. -/
theorem exerciseVm_rejects_moved_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (VmConstraint.gate gBalLoFreeze).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
  intro h; apply hwrong; linarith

/-- **Anti-ghost (cap-root tamper).** A row whose post-`cap_root` ≠ pre-`cap_root` fails the freeze gate
— no forged authority change rides a hold step. -/
theorem exerciseVm_rejects_wrong_capRoot (env : VmRowEnv)
    (hwrong : env.loc (saCol state.CAP_ROOT) ≠ env.loc (sbCol state.CAP_ROOT)) :
    ¬ (VmConstraint.gate gCapPass).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]
  intro h; apply hwrong; linarith

/-- **Anti-ghost (nonce tamper).** A row whose nonce does NOT tick by 1 fails the reconciled `gNonce`
tick gate — a frozen-nonce trace (the pre-v2 convention) is now correctly UNSAT. -/
theorem exerciseVm_rejects_nonce_freeze (env : VmRowEnv)
    (hwrong : env.loc (saCol state.NONCE) ≠ env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)) :
    ¬ (VmConstraint.gate gNonce).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
  intro h; apply hwrong; linarith

/-! ## §6 — the commitment binding (REUSED; hash sites identical to transfer's). -/

theorem exerciseHashSites_eq : exerciseHashSites = transferHashSites := rfl

theorem exerciseVm_commit_binds_block (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ exerciseHashSites)
    (hs₂ : siteHoldsAll hash e₂ exerciseHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ := by
  rw [exerciseHashSites_eq] at hs₁ hs₂
  exact absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §7 — the structured per-cell spec (REUSING `CellState`): passthrough + nonce tick. -/

/-- `RowEncodesExercise env pre post` ties the row's state-block columns to a `(pre, post)` transition. -/
def RowEncodesExercise (env : VmRowEnv) (pre post : CellState) : Prop :=
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

/-- **`ExerciseCellSpec pre post`** — the per-cell FULL-state exercise-hold row spec: economic block
FROZEN; the nonce TICKS by 1. (The hold-gate + log + inner fold are off-row.) -/
def ExerciseCellSpec (pre post : CellState) : Prop :=
  post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce + 1
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

theorem intent_to_cellSpec (env : VmRowEnv) (pre post : CellState)
    (hnoop : env.loc sel.NOOP = 0)
    (henc : RowEncodesExercise env pre post) (hint : ExerciseRowIntent env) :
    ExerciseCellSpec pre post := by
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

theorem exerciseDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (hnoop : env.loc sel.NOOP = 0)
    (henc : RowEncodesExercise env pre post)
    (hsat : satisfiedVm hash exerciseVmDescriptor env true true) :
    ExerciseCellSpec pre post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates' : ∀ c ∈ exerciseRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ exerciseVmDescriptor.constraints := by
      unfold exerciseVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
    have := hcs c hmem
    unfold exerciseRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (exerciseVm_faithful env).mp hgates'
  refine ⟨intent_to_cellSpec env pre post hnoop henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ exerciseVmDescriptor.constraints := by
      unfold exerciseVmDescriptor
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

theorem exerciseDescriptor_commit_binds_state (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash exerciseVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash exerciseVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ exerciseHashSites := hsat₁.2.1
  have hs₂ : siteHoldsAll hash e₂ exerciseHashSites := hsat₂.2.1
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash exerciseVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ exerciseVmDescriptor.constraints := by
        unfold exerciseVmDescriptor
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

/-! ## §9 — THE CONNECTOR — `balProj`/`capRootProj` to universe-A's `ExerciseHoldSpec` (kernel freeze). -/

open Dregg2.Circuit.ActionDispatch (ExerciseHoldSpec exerciseHoldState exerciseStepA_iff_holdSpec)
open Dregg2.Authority (Caps)

/-- **`balProj k c`** — the conserved balance of cell `c`. -/
def balProj (k : RecordKernelState) (c : CellId) : ℤ := balOf (k.cell c)

/-- **`capRootProj D k`** — the cap-table digest. -/
def capRootProj (D : Caps → ℤ) (k : RecordKernelState) : ℤ := D k.caps

/-- **`unify_exercise` — THE CONNECTOR.** When universe-A's `ExerciseHoldSpec` holds, the WHOLE kernel is
frozen, so for EVERY cell `c` and digest `D` the projected post-balance equals the pre-balance AND the
projected post cap-digest equals the pre cap-digest — exactly the freeze the descriptor pins. The
nonce-tick is the runtime cell-bookkeeping leg (off universe-A state). -/
theorem unify_exercise (D : Caps → ℤ)
    (s : RecChainedState) (actor target : CellId) (s' : RecChainedState) (c : CellId)
    (hspec : ExerciseHoldSpec s actor target s') :
    balProj s'.kernel c = balProj s.kernel c
    ∧ capRootProj D s'.kernel = capRootProj D s.kernel := by
  obtain ⟨_, hhold⟩ := hspec
  have hker : s'.kernel = s.kernel := by rw [hhold]; rfl
  refine ⟨?_, ?_⟩
  · show balOf (s'.kernel.cell c) = balOf (s.kernel.cell c); rw [hker]
  · show D s'.kernel.caps = D s.kernel.caps; rw [hker]

/-- **`unify_exercise_via_exec` — the runnable freeze inherits the VALIDATED guarantee.** -/
theorem unify_exercise_via_exec (D : Caps → ℤ)
    (s : RecChainedState) (actor target : CellId) (s' : RecChainedState) (c : CellId)
    (h : exerciseStepA s actor target = some s') :
    balProj s'.kernel c = balProj s.kernel c
    ∧ capRootProj D s'.kernel = capRootProj D s.kernel :=
  unify_exercise D s actor target s' c
    ((exerciseStepA_iff_holdSpec s s' actor target).mp h)

/-- **`descriptor_agrees_with_executor_exercise`** — a satisfying run of the runnable descriptor encoding
any cell agrees with the executor's post-state on the FROZEN balance dimension (`balLo`); the nonce-tick
is the runtime cell-bookkeeping leg (off universe-A state). -/
theorem descriptor_agrees_with_executor_exercise
    (hash : List ℤ → ℤ) (env : VmRowEnv) (hnoop : env.loc sel.NOOP = 0)
    (s s' : RecChainedState) (actor target c : CellId) (pre post : CellState)
    (hpreBal : env.loc (sbCol state.BALANCE_LO) = balProj s.kernel c)
    (henc : RowEncodesExercise env pre post)
    (hsat : satisfiedVm hash exerciseVmDescriptor env true true)
    (hspec : ExerciseHoldSpec s actor target s') :
    post.balLo = balProj s'.kernel c := by
  obtain ⟨hcirc, _⟩ := exerciseDescriptor_full_sound hash env pre post hnoop henc hsat
  obtain ⟨hcLo, _, _, _, _, _⟩ := hcirc
  obtain ⟨heBal, _⟩ := unify_exercise (fun _ => 0) s actor target s' c hspec
  obtain ⟨hsbLo, _⟩ := henc
  -- post.balLo = pre.balLo (circuit freeze) = sb balance (encoding) = balProj s = balProj s' (exec)
  rw [hcLo, ← hsbLo, hpreBal, heBal]

/-! ## §10 — NON-VACUITY. -/

/-- A concrete exercise row: state-block passthrough + nonce TICK (bal_lo 100 → 100, nonce 5 → 6). -/
def goodExRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_EXERCISE then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 100
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 6
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

theorem goodExRow_noop : goodExRow.loc sel.NOOP = 0 := by
  show goodExRow.loc 0 = 0
  simp only [goodExRow, SEL_EXERCISE, sbCol, saCol, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE]
  norm_num

/-- **NON-VACUITY (witness TRUE).** `goodExRow` REALIZES the runtime exercise intent. -/
theorem goodExRow_realizes_intent : ExerciseRowIntent goodExRow := by
  unfold ExerciseRowIntent
  have hnoop : goodExRow.loc sel.NOOP = 0 := goodExRow_noop
  refine ⟨rfl, rfl, ?_, rfl, rfl, ?_⟩
  · rw [hnoop]
    show goodExRow.loc (saCol state.NONCE) = goodExRow.loc (sbCol state.NONCE) + (1 - 0)
    simp only [goodExRow, SEL_EXERCISE, sbCol, saCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE]
    norm_num
  · intro i hi
    show goodExRow.loc (saCol (state.FIELD_BASE + i)) = goodExRow.loc (sbCol (state.FIELD_BASE + i))
    simp only [goodExRow, SEL_EXERCISE, sbCol, saCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE, state.FIELD_BASE]
    have e1 : (76 + (3 + i) = 34) = False := eq_false (by omega)
    have e2 : (76 + (3 + i) = 54 + 0) = False := eq_false (by omega)
    have e3 : (76 + (3 + i) = 76 + 0) = False := eq_false (by omega)
    have e4 : (76 + (3 + i) = 54 + 2) = False := eq_false (by omega)
    have e5 : (76 + (3 + i) = 76 + 2) = False := eq_false (by omega)
    have f1 : (54 + (3 + i) = 34) = False := eq_false (by omega)
    have f2 : (54 + (3 + i) = 54 + 0) = False := eq_false (by omega)
    have f3 : (54 + (3 + i) = 76 + 0) = False := eq_false (by omega)
    have f4 : (54 + (3 + i) = 54 + 2) = False := eq_false (by omega)
    have f5 : (54 + (3 + i) = 76 + 2) = False := eq_false (by omega)
    simp only [e1, e2, e3, e4, e5, f1, f2, f3, f4, f5, if_false]

/-- A FORGED exercise row: `goodExRow` with the post-`bal_lo` minted to `999`. -/
def badExRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodExRow.loc v
  nxt := goodExRow.nxt
  pub := goodExRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badExRow`'s post-`bal_lo` is forged, so
`gBalLoFreeze` REJECTS it. -/
theorem badExRow_rejected : ¬ (VmConstraint.gate gBalLoFreeze).holdsVm badExRow false false := by
  apply exerciseVm_rejects_moved_balance
  simp only [badExRow, goodExRow, sbCol, saCol, SEL_EXERCISE, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE]
  norm_num

/-- A FROZEN-NONCE exercise row: `goodExRow` with the post-nonce held at `5`. -/
def staleNonceExRow : VmRowEnv where
  loc := fun v => if v = saCol state.NONCE then 5 else goodExRow.loc v
  nxt := goodExRow.nxt
  pub := goodExRow.pub

/-- **NON-VACUITY (cutover witness FALSE).** A frozen-nonce row is now correctly UNSAT under the
reconciled `gNonce` tick gate. -/
theorem staleNonceExRow_rejected :
    ¬ (VmConstraint.gate gNonce).holdsVm staleNonceExRow false false := by
  apply exerciseVm_rejects_nonce_freeze
  simp only [staleNonceExRow, goodExRow, sel.NOOP, sbCol, saCol, SEL_EXERCISE,
    STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
    state.BALANCE_LO, state.NONCE]
  norm_num

/-! ## §11 — Axiom-hygiene tripwires. -/

#guard exerciseVmDescriptor.constraints.length == 13 + 14 + 4 + 3 + 1
#guard exerciseVmDescriptor.hashSites.length == 4
#guard exerciseVmDescriptor.traceWidth == 186

#assert_axioms exerciseVm_faithful
#assert_axioms exerciseVm_rejects_wrong_output
#assert_axioms exerciseVm_rejects_moved_balance
#assert_axioms exerciseVm_rejects_wrong_capRoot
#assert_axioms exerciseVm_rejects_nonce_freeze
#assert_axioms intent_to_cellSpec
#assert_axioms exerciseDescriptor_full_sound
#assert_axioms exerciseDescriptor_commit_binds_state
#assert_axioms unify_exercise
#assert_axioms unify_exercise_via_exec
#assert_axioms descriptor_agrees_with_executor_exercise
#assert_axioms goodExRow_realizes_intent
#assert_axioms badExRow_rejected
#assert_axioms staleNonceExRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitExercise
