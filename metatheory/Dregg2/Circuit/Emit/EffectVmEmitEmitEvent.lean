/-
# Dregg2.Circuit.Emit.EffectVmEmitEmitEvent — the OBSERVATION-LOG effect `emitEventA`, EMITTED onto
  the runnable EffectVM row, RECONCILED onto the RUNNING hand-AIR's columns (cutover convention) and
  GRADUATED into the descriptor cutover (v1, nonce-tick reconcile).

## THE RUNTIME GROUND TRUTH (the cutover-faithful reconciliation)

A committed emit writes the observation `log` and NOTHING in the kernel (`Spec/cellstatelog.lean`): a
committed emit prepends one self-targeted receipt row and leaves the ENTIRE `RecordKernelState` literally
unchanged (`execFullA_emitEvent_kernel`). The running prover (`circuit/src/effect_vm/air.rs`) runs the
emit row as a **state-passthrough** row: EVERY economic state-block column is FROZEN
(`new_bal_lo == old_bal_lo`, `bal_hi`, `new_cap_root == old_cap_root`, `reserved`, and ALL 8 `field[i]`),
and the GLOBAL nonce gate (`circuit/src/effect_vm/air.rs:1331-1332`, `new_nonce == old_nonce + (1 -
s_noop)`) TICKS the actor's turn-SEQUENCE nonce by 1 on this non-NoOp row. The topic/payload digests live
OFF-trace: they ride the row's params + `compute_effects_hash` — the AIR carries NO `field` column for the
log payload.

So the cutover-faithful row is the FROZEN-FRAME + NONCE-TICK shape (the setPermissions / cellDestroy /
refusal gauntlet). The PRE-v1 descriptor FROZE the nonce (`new_nonce - old_nonce = 0`) AND emitted a
`state_commit` PASSTHROUGH gate — so the honest TICKED trace (whose `state_commit` is recomputed over the
ticked nonce) was UNSAT under it. This reconciles the runnable descriptor to the runtime passthrough+tick:
the 13 economic columns FREEZE, the nonce TICKS, and `state_commit` is bound ONLY via the last-row PI pin
(the GROUP-4 hash chain recomputes it over the ticked nonce).

## TWO NONCE NOTIONS (the honest distinction)

The EffectVM row's `state.NONCE` column is the ACTOR turn-SEQUENCE nonce (anti-replay, `PI[ACTOR_NONCE]`),
which the protocol ticks on every real effect. This is a DIFFERENT object than the cell's own `nonce`
FIELD inside `RecordKernelState` (which a committed emit leaves FROZEN, since emit changes no kernel
field). So this module carries BOTH:

  * the runnable TICK shape (`EmitTickRowIntent` / `EmitTickCellSpec`) — the actor-sequence nonce TICKS,
    matching the runtime column the prover RUNS. This drives the cutover descriptor `emitEventVmDescriptor`.
  * the FREEZE-ALL shape (`EmitRowIntent` / `CellFreezeSpec` / `unify_emitEvent`) — every block column
    INCLUDING the nonce slot FROZEN, the universe-A kernel-freeze projected per cell. This is the shared
    no-op-style freeze primitive (reused by `EffectVmEmitNoopWide`, which models the `s_noop = 1` PAD row
    whose global nonce gate does NOT tick), and the abstract per-cell kernel-freeze the Argus §1–§5 weld
    pins. The two differ ONLY on the actor-sequence nonce slot.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. Poseidon2 CR enters ONLY as
the NAMED hypothesis `Poseidon2SpongeCR hash`. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.cellstatelog

namespace Dregg2.Circuit.Emit.EffectVmEmitEmitEvent

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA eSub eSelNoop gBalHi gNonce gCapPass gResPass gFieldPass gFieldPassAll
   transitionAll boundaryFirstPins boundaryLastPins
   transferHashSites boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState absorbedCols absorbed_determined_by_commit)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec
open Dregg2.Exec.EffectsState
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Spec.CellStateLog

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — Selector for the emit-event effect row (runtime `sel::EMIT_EVENT = 25`). -/

/-- The `emitEventA` effect selector column index (runtime `sel::EMIT_EVENT = 25`). -/
def SEL_EMIT_EVENT : Nat := 25

/-- The emit-event row: `s_emit_event = 1`, `s_noop = 0` (load-bearing for the nonce TICK gate). -/
def IsEmitRow (env : VmRowEnv) : Prop :=
  env.loc SEL_EMIT_EVENT = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — the SHARED FREEZE-ALL primitives (every block column frozen, INCLUDING the nonce slot).

These are the no-op-style whole-block-freeze gates: the universe-A kernel-freeze projected per cell (a
committed emit moves NO kernel field, including the cell-nonce field). Reused by `EffectVmEmitNoopWide`
(the `s_noop = 1` PAD row, whose global nonce gate does NOT tick) and by the abstract per-cell kernel-
freeze the Argus §1–§5 weld pins. NOT the runnable descriptor — that ticks the actor-sequence nonce (§2). -/

/-- Passthrough body for state offset `off`: `state_after[off] - state_before[off]`. -/
def gFreeze (off : Nat) : EmittedExpr := eSub (eSA off) (eSB off)

/-- The 14 whole-block passthrough gates (offsets 0..13). -/
def emitRowGates : List VmConstraint :=
  (List.range STATE_SIZE).map (fun off => VmConstraint.gate (gFreeze off))

/-- **`EmitRowIntent env`** — every state-block offset 0..13 is frozen `after = before` (INCLUDING the
nonce slot). -/
def EmitRowIntent (env : VmRowEnv) : Prop :=
  ∀ off < STATE_SIZE, env.loc (saCol off) = env.loc (sbCol off)

theorem emitEventVm_faithful (env : VmRowEnv) :
    (∀ c ∈ emitRowGates, c.holdsVm env false false) ↔ EmitRowIntent env := by
  unfold emitRowGates EmitRowIntent
  constructor
  · intro h off hoff
    have := h (.gate (gFreeze off)) (by
      simp only [List.mem_map, List.mem_range]; exact ⟨off, hoff, rfl⟩)
    simp only [VmConstraint.holdsVm, gFreeze, eSA, eSB, eSub, EmittedExpr.eval] at this
    linarith
  · intro h c hc
    simp only [List.mem_map, List.mem_range] at hc
    obtain ⟨off, hoff, rfl⟩ := hc
    simp only [VmConstraint.holdsVm, gFreeze, eSA, eSB, eSub, EmittedExpr.eval]
    rw [h off hoff]; ring

theorem emitRowGates_flag_indep (env : VmRowEnv) (b1 : Bool)
    (h : ∀ c ∈ emitRowGates, c.holdsVm env b1 false) :
    ∀ c ∈ emitRowGates, c.holdsVm env false false := by
  intro c hc
  have := h c hc
  unfold emitRowGates at hc
  simp only [List.mem_map, List.mem_range] at hc
  obtain ⟨off, hoff, rfl⟩ := hc
  simpa only [VmConstraint.holdsVm] using this

/-- The per-cell freeze spec: post equals pre on EVERY block component (including the nonce slot). -/
def CellFreezeSpec (pre : CellState) (post : CellState) : Prop :=
  post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

/-- `RowEncodes env pre post` ties the row's state-block columns to a `(pre, post)` transition. -/
def RowEncodes (env : VmRowEnv) (pre : CellState) (post : CellState) : Prop :=
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

theorem intent_to_cellSpec (env : VmRowEnv) (pre post : CellState)
    (henc : RowEncodes env pre post) (hint : EmitRowIntent env) :
    CellFreezeSpec pre post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsaLo, ← hsbLo]; exact hint state.BALANCE_LO (by decide)
  · rw [← hsaHi, ← hsbHi]; exact hint state.BALANCE_HI (by decide)
  · rw [← hsaN, ← hsbN]; exact hint state.NONCE (by decide)
  · intro i
    rw [← hsaF i, ← hsbF i]
    exact hint (state.FIELD_BASE + i.val) (by have := i.isLt; unfold state.FIELD_BASE STATE_SIZE; omega)
  · rw [← hsaCap, ← hsbCap]; exact hint state.CAP_ROOT (by decide)
  · rw [← hsaRes, ← hsbRes]; exact hint state.RESERVED (by decide)

/-! ## §2 — the RUNNABLE per-row gate bodies (RUNTIME-RECONCILED: state-block passthrough + nonce TICK).

The economic state block passes through unchanged; the actor's turn-SEQUENCE nonce TICKS by 1 (the global
runtime nonce gate). The `state_commit` cell is NOT frozen by a gate — it is recomputed over the ticked
nonce by the GROUP-4 hash chain and bound via the last-row PI pin. This is the descriptor the prover RUNS. -/

/-- Balance-lo FREEZE body (an emit moves no value). -/
def gBalLoFreeze : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)

/-- The RUNNABLE per-row gates: whole economic state block PASSTHROUGH + nonce TICK (`gNonce`, runtime
convention). Order mirrors the running hand-AIR's passthrough batch + the global nonce gate. -/
def emitTickRowGates : List VmConstraint :=
  [ .gate gBalLoFreeze, .gate gBalHi, .gate gNonce
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-- **`EmitTickRowIntent env`** — every economic state-block column UNCHANGED EXCEPT the nonce, which TICKS
by 1 (on a non-NoOp row `s_noop = 0`). The log-receipt write is OFF-row (the §connector). -/
def EmitTickRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

theorem emitTickVm_faithful (env : VmRowEnv) :
    (∀ c ∈ emitTickRowGates, c.holdsVm env false false) ↔ EmitTickRowIntent env := by
  unfold emitTickRowGates gFieldPassAll EmitTickRowIntent
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

/-- **Flag-independence of the RUNNABLE tick gates.** Pure per-row polynomial gates, no transition/boundary
terms, so satisfaction is independent of the `isFirst`/`isLast` flags. (Used by the wide full-state lift,
which passes `true true`.) -/
theorem emitTickRowGates_flag_indep (env : VmRowEnv) (b1 : Bool)
    (h : ∀ c ∈ emitTickRowGates, c.holdsVm env b1 false) :
    ∀ c ∈ emitTickRowGates, c.holdsVm env false false := by
  intro c hc
  have := h c hc
  unfold emitTickRowGates gFieldPassAll at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using this

/-! ## §3 — The emitted EMIT-EVENT descriptor (v1 = runtime-reconciled passthrough+tick). -/

def emitVmAirName : String := "dregg-effectvm-emitEvent-v1"

/-- **`emitEventVmDescriptor`** — the `emitEventA` EffectVM-row circuit, RECONCILED onto the runtime
hand-AIR: the per-row passthrough gates with the nonce TICK ++ transition continuity ++ the 7 boundary PI
pins ++ the selector-binding gate, the 4 ordered GROUP-4 hash sites and the 2 balance-limb range checks. -/
def emitEventVmDescriptor : EffectVmDescriptor :=
  { name := emitVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 42
  , constraints := emitTickRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                     ++ selectorGates SEL_EMIT_EVENT
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §4 — ANTI-GHOST (runnable shape). -/

theorem emitEventVm_rejects_wrong_output (env : VmRowEnv) (hwrong : ¬ EmitTickRowIntent env) :
    ¬ (∀ c ∈ emitTickRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((emitTickVm_faithful env).mp h)

/-- **Anti-ghost (state move).** A row whose post-`bal_lo` ≠ pre-`bal_lo` fails the freeze gate (UNSAT). -/
theorem emitEventVm_rejects_moved_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (VmConstraint.gate gBalLoFreeze).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
  intro h; apply hwrong; linarith

/-- **Anti-ghost (nonce tamper).** A row whose nonce does NOT tick by 1 fails the reconciled `gNonce` tick
gate — a frozen-nonce trace (the pre-v1 convention) is now correctly UNSAT. -/
theorem emitEventVm_rejects_nonce_freeze (env : VmRowEnv)
    (hwrong : env.loc (saCol state.NONCE) ≠ env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)) :
    ¬ (VmConstraint.gate gNonce).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
  intro h; apply hwrong; linarith

/-! ## §5 — `EmitTickCellSpec` + `RowEncodes` → structured per-cell soundness (block frozen, nonce ticks). -/

/-- The per-cell emit spec (runnable): the economic block is FROZEN; the actor nonce TICKS by 1. (The log
write is OFF-row — the §connector.) -/
def EmitTickCellSpec (pre post : CellState) : Prop :=
  post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce + 1
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

theorem intent_to_tickCellSpec (env : VmRowEnv) (pre post : CellState)
    (hnoop : env.loc sel.NOOP = 0)
    (henc : RowEncodes env pre post) (hint : EmitTickRowIntent env) :
    EmitTickCellSpec pre post := by
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

/-! ## §6 — the full RUNNABLE descriptor soundness + the commitment binding. -/

theorem emitEventDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (hnoop : env.loc sel.NOOP = 0)
    (henc : RowEncodes env pre post)
    (hgatesat : satisfiedVm hash emitEventVmDescriptor env true false)
    (hsat : satisfiedVm hash emitEventVmDescriptor env true true) :
    EmitTickCellSpec pre post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  obtain ⟨hcsT, _⟩ := hgatesat
  have hgates' : ∀ c ∈ emitTickRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ emitEventVmDescriptor.constraints := by
      unfold emitEventVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
    have := hcsT c hmem
    unfold emitTickRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (emitTickVm_faithful env).mp hgates'
  refine ⟨intent_to_tickCellSpec env pre post hnoop henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ emitEventVmDescriptor.constraints := by
      unfold emitEventVmDescriptor
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

/-! ## §7 — ANTI-GHOST COMMITMENT TOOTH (reused from the transfer keystone). -/

theorem emit_sites_eq : emitEventVmDescriptor.hashSites = transferHashSites := rfl

theorem emitEventDescriptor_commit_binds_state (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash emitEventVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash emitEventVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ transferHashSites := hsat₁.2.1
  have hs₂ : siteHoldsAll hash e₂ transferHashSites := hsat₂.2.1
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash emitEventVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ emitEventVmDescriptor.constraints := by
        unfold emitEventVmDescriptor
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

/-! ## §8 — THE CONNECTOR — `cellProjE` to universe-A's `EmitEventSpec` (the whole-kernel FREEZE).

`cellProjE k c` reads cell `c`'s conserved `balLo` (`balOf`) and `nonce` (`fieldOf nonceField`); the
EffectVM columns with no record analogue are `0`. A committed emit leaves the WHOLE kernel unchanged
(`execFullA_emitEvent_kernel`), so `cellProjE` of the post-kernel equals `cellProjE` of the pre-kernel —
the whole projection is FROZEN (this is the `CellFreezeSpec` shape, the cell-nonce FIELD frozen). The
runnable descriptor's actor-sequence nonce TICK (§2) is a DISTINCT column, the runtime turn-bookkeeping
leg (off this universe-A per-cell projection). -/

def cellProjE (k : RecordKernelState) (c : CellId) : CellState where
  balLo    := balOf (k.cell c)
  balHi    := 0
  nonce    := fieldOf nonceField (k.cell c)
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`unify_emitEvent` — THE UNIFICATION (whole-kernel freeze).** A committed `EmitEventSpec` (the
executor leaves the WHOLE kernel unchanged), projected onto any cell `c` under `cellProjE`, satisfies
`CellFreezeSpec` EXACTLY: post = pre on every block component (because `k' = k` for the whole kernel),
including the cell-nonce field. -/
theorem unify_emitEvent (s s' : RecChainedState) (actor cell c : CellId) (topic data : Int)
    (hspec : EmitEventSpec s actor cell topic data s') :
    CellFreezeSpec (cellProjE s.kernel c) (cellProjE s'.kernel c) := by
  obtain ⟨_, _, h1, h2, h3, h4, h5, h6, h7, h10, h11, h12, h13, h14, h15, h17, h18, h19,
    h20, h21⟩ := hspec
  have hk : s'.kernel = s.kernel :=
    recKernel_ext h1 h2 h3 h4 h5 h6 h7 h10 h11 h12 h13 h14 h15 h17 h18 h19 h20 h21
  rw [hk]
  exact ⟨rfl, rfl, rfl, fun _ => rfl, rfl, rfl⟩

/-- **`unify_emitEvent_exec` — same, against the executor directly.** -/
theorem unify_emitEvent_exec (s s' : RecChainedState) (actor cell c : CellId) (topic data : Int)
    (h : execFullA s (.emitEventA actor cell topic data) = some s') :
    CellFreezeSpec (cellProjE s.kernel c) (cellProjE s'.kernel c) :=
  unify_emitEvent s s' actor cell c topic data
    ((execFullA_emitEvent_iff_spec s actor cell topic data s').mp h)

/-- **`descriptor_agrees_with_executor` — per-cell circuit⟺executor agreement on the conserved block.**
With `pre = cellProjE s.kernel c`, the RUNNABLE descriptor's pinned post-balance agrees with the executor's
post-cell projection (the kernel-freeze); the actor-nonce tick is the runtime turn-sequence leg (off
universe-A state). -/
theorem descriptor_agrees_with_executor
    (hash : List ℤ → ℤ) (env : VmRowEnv) (hnoop : env.loc sel.NOOP = 0)
    (s s' : RecChainedState) (actor cell c : CellId) (topic data : Int) (pre post : CellState)
    (hpre : pre = cellProjE s.kernel c)
    (henc : RowEncodes env pre post)
    (hgatesat : satisfiedVm hash emitEventVmDescriptor env true false)
    (hsat : satisfiedVm hash emitEventVmDescriptor env true true)
    (hexec : execFullA s (.emitEventA actor cell topic data) = some s') :
    post.balLo = (cellProjE s'.kernel c).balLo := by
  obtain ⟨hcirc, _⟩ := emitEventDescriptor_full_sound hash env pre post hnoop henc hgatesat hsat
  obtain ⟨hcLo, _, _, _, _, _⟩ := hcirc
  obtain ⟨heLo, _, _, _, _, _⟩ := unify_emitEvent_exec s s' actor cell c topic data hexec
  subst hpre
  rw [hcLo, heLo]

/-! ## §9 — NON-VACUITY. -/

/-- A concrete emit row: economic-block passthrough + nonce TICK (bal_lo 100 → 100, nonce 5 → 6). -/
def goodEmitRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_EMIT_EVENT then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 100
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 6
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

theorem goodEmitRow_noop : goodEmitRow.loc sel.NOOP = 0 := by
  show goodEmitRow.loc 0 = 0
  simp only [goodEmitRow, SEL_EMIT_EVENT, sbCol, saCol, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE]
  norm_num

/-- **NON-VACUITY (witness TRUE).** `goodEmitRow` REALIZES the runtime emit (tick) intent. -/
theorem goodEmitRow_realizes_intent : EmitTickRowIntent goodEmitRow := by
  unfold EmitTickRowIntent
  have hnoop : goodEmitRow.loc sel.NOOP = 0 := goodEmitRow_noop
  refine ⟨rfl, rfl, ?_, rfl, rfl, ?_⟩
  · rw [hnoop]
    show goodEmitRow.loc (saCol state.NONCE) = goodEmitRow.loc (sbCol state.NONCE) + (1 - 0)
    simp only [goodEmitRow, SEL_EMIT_EVENT, sbCol, saCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE]
    norm_num
  · intro i hi
    show goodEmitRow.loc (saCol (state.FIELD_BASE + i)) = goodEmitRow.loc (sbCol (state.FIELD_BASE + i))
    simp only [goodEmitRow, SEL_EMIT_EVENT, sbCol, saCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE, state.FIELD_BASE]
    have e1 : (76 + (3 + i) = 25) = False := eq_false (by omega)
    have e2 : (76 + (3 + i) = 54 + 0) = False := eq_false (by omega)
    have e3 : (76 + (3 + i) = 76 + 0) = False := eq_false (by omega)
    have e4 : (76 + (3 + i) = 54 + 2) = False := eq_false (by omega)
    have e5 : (76 + (3 + i) = 76 + 2) = False := eq_false (by omega)
    have f1 : (54 + (3 + i) = 25) = False := eq_false (by omega)
    have f2 : (54 + (3 + i) = 54 + 0) = False := eq_false (by omega)
    have f3 : (54 + (3 + i) = 76 + 0) = False := eq_false (by omega)
    have f4 : (54 + (3 + i) = 54 + 2) = False := eq_false (by omega)
    have f5 : (54 + (3 + i) = 76 + 2) = False := eq_false (by omega)
    simp only [e1, e2, e3, e4, e5, f1, f2, f3, f4, f5, if_false]

/-- A FORGED emit row: `goodEmitRow` with the post-`bal_lo` minted to `999`. -/
def badEmitRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodEmitRow.loc v
  nxt := goodEmitRow.nxt
  pub := goodEmitRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badEmitRow`'s post-`bal_lo` is forged, so
`gBalLoFreeze` REJECTS it. -/
theorem badEmitRow_rejected : ¬ (VmConstraint.gate gBalLoFreeze).holdsVm badEmitRow false false := by
  apply emitEventVm_rejects_moved_balance
  simp only [badEmitRow, goodEmitRow, sbCol, saCol, SEL_EMIT_EVENT, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE]
  norm_num

/-- A FROZEN-NONCE emit row: `goodEmitRow` with the post-nonce held at `5`. -/
def staleNonceEmitRow : VmRowEnv where
  loc := fun v => if v = saCol state.NONCE then 5 else goodEmitRow.loc v
  nxt := goodEmitRow.nxt
  pub := goodEmitRow.pub

/-- **NON-VACUITY (cutover witness FALSE).** A frozen-nonce row is now correctly UNSAT under the
reconciled `gNonce` tick gate. -/
theorem staleNonceEmitRow_rejected :
    ¬ (VmConstraint.gate gNonce).holdsVm staleNonceEmitRow false false := by
  apply emitEventVm_rejects_nonce_freeze
  simp only [staleNonceEmitRow, goodEmitRow, sel.NOOP, sbCol, saCol, SEL_EMIT_EVENT,
    STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
    state.BALANCE_LO, state.NONCE]
  norm_num

/-! ## §10 — Axiom-hygiene tripwires. -/

#guard emitEventVmDescriptor.constraints.length == 13 + 14 + 4 + 3 + 1
#guard emitEventVmDescriptor.hashSites.length == 4
#guard emitEventVmDescriptor.traceWidth == 188
#guard emitRowGates.length == 14

#assert_axioms emitEventVm_faithful
#assert_axioms emitRowGates_flag_indep
#assert_axioms intent_to_cellSpec
#assert_axioms unify_emitEvent
#assert_axioms unify_emitEvent_exec
#assert_axioms emitTickVm_faithful
#assert_axioms emitTickRowGates_flag_indep
#assert_axioms emitEventVm_rejects_wrong_output
#assert_axioms emitEventVm_rejects_moved_balance
#assert_axioms emitEventVm_rejects_nonce_freeze
#assert_axioms intent_to_tickCellSpec
#assert_axioms emitEventDescriptor_full_sound
#assert_axioms emitEventDescriptor_commit_binds_state
#assert_axioms descriptor_agrees_with_executor
#assert_axioms goodEmitRow_realizes_intent
#assert_axioms badEmitRow_rejected
#assert_axioms staleNonceEmitRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitEmitEvent
