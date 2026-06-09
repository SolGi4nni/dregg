/-
# Dregg2.Circuit.Emit.EffectVmEmitCellUnseal — the `cellUnseal` (lifecycle Sealed→Live) effect's
EffectVM-row circuit, EMITTED + RECONCILED onto the RUNNING hand-AIR's columns (selector 50), THEN
LIFTED to FULL-STATE on the RUNNABLE descriptor (the magnesium breadth: binds all 17 fields).

## Why this module exists (the gap it fills)

cellSeal/cellDestroy/refusal each have a RUNNABLE EffectVM descriptor (`EffectVmEmitCellSeal` etc.).
`cellUnseal` (the lifecycle Sealed→Live inverse of cellSeal) did NOT — `EffectVmEmitUnseal` is the
DIFFERENT userspace sealed-box `Unseal` effect. The running prover DOES run `cellUnseal` as selector 50
(`circuit/src/effect_vm/columns.rs:235`, AIR-impl lane #119), in the SAME Stage-3 passthrough batch as
cellSeal: the trace arm does ONLY `new_state.nonce += 1` and leaves every economic state-block column
FROZEN (`trace.rs:1239`), the single `CELL_UNSEAL_TARGET` param binding the cell. So the cutover-faithful
RUNNABLE row is the cellSeal-shaped FROZEN-FRAME + nonce-TICK passthrough, and this module emits it
(selector 50) so cellUnseal has a runnable circuit to amplify — exactly the cellSeal-v2 descriptor with
the cellUnseal selector.

## What the EffectVM row CAN pin (honest)

  * the cell's economic block (bal/fields/cap/reserved) is FROZEN; the nonce TICKS by 1;
  * the post-state is bound into `state_commit` (GROUP-4) and published as `NEW_COMMIT`.

## What the EffectVM row CANNOT enforce (the honest boundary — the WHOLE point of the effect)

  * the `lifecycle` flip Sealed → Live — a per-cell SIDE-TABLE, NO EffectVM column. Its SOUNDNESS lives
    ONLY in universe-A's `cellUnsealA_full_sound` (the `Inst/cellUnsealA.lean` v2 `Surface2` descriptor).

## The FULL-STATE lift (the magnesium breadth, the §RECIPE of `EffectVmFullStateRunnable`)

The 186-wide row's `state_commit` absorbs only the 13 state-block columns. This module WIDENS the
descriptor to the `system_roots`-absorbing shape (`EFFECT_VM_WIDTH_SYSROOTS`, `wideHashSites`) and lifts
through the generic `runnable_full_sound`: a satisfying WIDE-descriptor witness pins the FULL 17-field
post-state — the per-cell block (`CellUnsealCellSpec`) AND every one of the 8 side-table roots FROZEN
(cellUnseal touches no side-table on-row). The anti-ghost tooth bites on all 17 (incl. any root).

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY through the named
`Poseidon2SpongeCR` portal (in the generic theorems). No `sorry`/`:= True`/`native_decide`. `fullClause`
NON-VACUOUS. Read-only imports; owns only its own declarations.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable

namespace Dregg2.Circuit.Emit.EffectVmEmitCellUnseal

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA eSub eSelNoop gBalHi gNonce gCapPass gResPass gFieldPass gFieldPassAll
   transitionAll boundaryFirstPins boundaryLastPins transferHashSites boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState absorbedCols absorbed_determined_by_commit)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (RunnableFullStateSpec runnable_full_sound runnable_full_commit_binds wide_rejects_root_tamper
   wideHashSites)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest emptySystemRoots N_SYSTEM_ROOTS)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — the `cellUnseal` selector column (runtime `sel::CELL_UNSEAL = 50`). -/

/-- The `cellUnseal` selector column index (runtime `sel::CELL_UNSEAL = 50`). -/
def SEL_CELLUNSEAL : Nat := 50

/-- The row is a cellUnseal row: `s_cellUnseal = 1`, `s_noop = 0`. -/
def IsCellUnsealRow (env : VmRowEnv) : Prop :=
  env.loc SEL_CELLUNSEAL = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — the per-row gate bodies (RUNTIME-RECONCILED: state-block passthrough + nonce TICK). -/

/-- Balance-lo FREEZE body: `new_bal_lo − old_bal_lo` (balance-neutral; runtime passthrough batch). -/
def gBalLoFreeze : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)

/-- The per-row gates: whole state block PASSTHROUGH + nonce TICK (`gNonce`, runtime convention). -/
def cellUnsealRowGates : List VmConstraint :=
  [ .gate gBalLoFreeze, .gate gBalHi, .gate gNonce
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-! ## §2 — the GROUP-4 state-commitment hash sites (reused). -/

def cellUnsealHashSites : List VmHashSite := transferHashSites

/-! ## §3 — the emitted descriptor (v2 = runtime-reconciled, last-row PI pins). -/

def cellUnsealVmAirName : String := "dregg-effectvm-cellunseal-v2"

/-- **`cellUnsealVmDescriptor`** — the `cellUnseal` EffectVM-row circuit, RECONCILED onto the runtime
hand-AIR (selector 50): the per-row passthrough gates with the nonce TICK ++ transition continuity ++ the
7 boundary PI pins (incl. the last-row `FINAL_BAL_LO`/`FINAL_BAL_HI`/`NEW_COMMIT`), the 4 ordered GROUP-4
hash sites and the 2 balance-limb range checks. The cellSeal-v2 descriptor shape with the cellUnseal
selector. -/
def cellUnsealVmDescriptor : EffectVmDescriptor :=
  { name := cellUnsealVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := cellUnsealRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                     ++ selectorGates 50
  , hashSites := cellUnsealHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §4 — the ROW INTENT: state-block passthrough + nonce TICK (runtime-faithful). -/

/-- **`CellUnsealRowIntent env`** — every economic state-block column UNCHANGED EXCEPT the nonce, which
TICKS by 1 (on a non-NoOp row `s_noop = 0`). The lifecycle flip + authority guard are out-of-row. -/
def CellUnsealRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §5 — FAITHFULNESS: the emitted per-row gates ⟺ the runtime-reconciled intent. -/

theorem cellUnsealVm_faithful (env : VmRowEnv) :
    (∀ c ∈ cellUnsealRowGates, c.holdsVm env false false) ↔ CellUnsealRowIntent env := by
  unfold cellUnsealRowGates gFieldPassAll CellUnsealRowIntent
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
    · simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
      rw [hNon]; ring
    · simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hCap]; ring
    · simp only [VmConstraint.holdsVm, gResPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hFld i hi]; ring

/-! ## §6 — ANTI-GHOST (gate level). -/

theorem cellUnsealVm_rejects_moved_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (VmConstraint.gate gBalLoFreeze).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
  intro h; apply hwrong; linarith

theorem cellUnsealVm_rejects_nonce_freeze (env : VmRowEnv)
    (hwrong : env.loc (saCol state.NONCE) ≠ env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)) :
    ¬ (VmConstraint.gate gNonce).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
  intro h; apply hwrong; linarith

/-! ## §7 — the structured per-cell spec (REUSING `CellState`): passthrough + nonce tick. -/

/-- `RowEncodesUnseal env pre post` ties the row's state-block columns to a `(pre, post)` cell transition. -/
def RowEncodesUnseal (env : VmRowEnv) (pre post : CellState) : Prop :=
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

/-- **`CellUnsealCellSpec pre post`** — the per-cell FULL-state cellUnseal row spec: economic block
FROZEN; the nonce TICKS by 1. (The lifecycle Sealed→Live flip is off-block — the honest boundary.) -/
def CellUnsealCellSpec (pre post : CellState) : Prop :=
  post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce + 1
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

theorem intent_to_cellSpec (env : VmRowEnv) (pre post : CellState)
    (hnoop : env.loc sel.NOOP = 0)
    (henc : RowEncodesUnseal env pre post) (hint : CellUnsealRowIntent env) :
    CellUnsealCellSpec pre post := by
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

/-! ## §8 — the narrow descriptor soundness + commitment binding (the 13-column projection). -/

/-- **`cellUnsealDescriptor_full_sound`** — satisfying the WHOLE narrow runnable descriptor, under
`RowEncodesUnseal` on a non-NoOp row, forces the structured per-cell `CellUnsealCellSpec` AND publishes
the post-commit as `PI[NEW_COMMIT]`. -/
theorem cellUnsealDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (hnoop : env.loc sel.NOOP = 0)
    (henc : RowEncodesUnseal env pre post)
    (hsat : satisfiedVm hash cellUnsealVmDescriptor env true true) :
    CellUnsealCellSpec pre post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates' : ∀ c ∈ cellUnsealRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ cellUnsealVmDescriptor.constraints := by
      unfold cellUnsealVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
    have := hcs c hmem
    unfold cellUnsealRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (cellUnsealVm_faithful env).mp hgates'
  refine ⟨intent_to_cellSpec env pre post hnoop henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ cellUnsealVmDescriptor.constraints := by
      unfold cellUnsealVmDescriptor
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

/-! ## §9 — THE FULL-STATE LIFT: the WIDE descriptor + the magnesium crown. -/

/-- **`cellUnsealVmDescriptorWide`** — cellUnseal's descriptor WIDENED to the `system_roots`-absorbing
shape (`traceWidth := EFFECT_VM_WIDTH_SYSROOTS`, `hashSites := wideHashSites`). Constraint list
byte-identical (`usesWideSites := rfl`). -/
def cellUnsealVmDescriptorWide : EffectVmDescriptor :=
  { cellUnsealVmDescriptor with
    name := cellUnsealVmDescriptor.name ++ "-sysroots"
    traceWidth := EFFECT_VM_WIDTH_SYSROOTS
    hashSites := wideHashSites }

theorem cellUnsealWide_constraints_eq :
    cellUnsealVmDescriptorWide.constraints = cellUnsealVmDescriptor.constraints := rfl

/-- The GATE-ONLY per-cell soundness (no hash-site hypothesis — the THIN per-effect content). -/
theorem cellUnsealGates_give_cellSpec (env : VmRowEnv) (pre post : CellState)
    (hnoop : env.loc sel.NOOP = 0) (henc : RowEncodesUnseal env pre post)
    (hgates : ∀ c ∈ cellUnsealVmDescriptor.constraints, c.holdsVm env true true) :
    CellUnsealCellSpec pre post := by
  have hrowgates : ∀ c ∈ cellUnsealRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ cellUnsealVmDescriptor.constraints := by
      unfold cellUnsealVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
    have hh := hgates c hmem
    unfold cellUnsealRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using hh
  exact intent_to_cellSpec env pre post hnoop henc ((cellUnsealVm_faithful env).mp hrowgates)

/-- **`CellUnsealFullClause`** — the FULL 17-field declarative post for cellUnseal: the per-cell
`CellUnsealCellSpec` (economic block FROZEN, the seq-nonce TICKS) AND the `system_roots` sub-block FROZEN. -/
def CellUnsealFullClause (preRoots : SysRoots) (pre post : CellState) (postRoots : SysRoots) : Prop :=
  CellUnsealCellSpec pre post ∧ postRoots = preRoots

/-- **`cellUnsealRunnableSpec`** — the FULL-state RUNNABLE instance for cellUnseal. THIN; NON-VACUOUS. -/
def cellUnsealRunnableSpec (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor    := cellUnsealVmDescriptorWide
  usesWideSites := rfl
  isRow         := IsCellUnsealRow
  decodeAfter   := fun env pre post postRoots =>
    RowEncodesUnseal env pre post ∧ postRoots = preRoots
  fullClause    := CellUnsealFullClause preRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots⟩ := hdec
    exact ⟨cellUnsealGates_give_cellSpec env pre post hrow.2 henc
            (cellUnsealWide_constraints_eq ▸ hgates), hroots⟩

/-- **`cellUnseal_runnable_full_sound` — the magnesium crown for cellUnseal.** A row satisfying the WIDE
RUNNABLE cellUnseal descriptor, decoded by `RowEncodesUnseal` with the frozen-roots witness, pins the
FULL 17-field post-state: the per-cell block (`CellUnsealCellSpec`) AND all 8 side-table roots FROZEN. -/
theorem cellUnseal_runnable_full_sound (hash : List ℤ → ℤ) (preRoots : SysRoots)
    (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsCellUnsealRow env)
    (henc : RowEncodesUnseal env pre post) (hroots : postRoots = preRoots)
    (hsat : satisfiedVm hash cellUnsealVmDescriptorWide env true true) :
    CellUnsealCellSpec pre post ∧ postRoots = preRoots :=
  runnable_full_sound (cellUnsealRunnableSpec preRoots) hash env pre post postRoots hrow
    ⟨henc, hroots⟩ hsat

/-! ## §10 — THE ANTI-GHOST. -/

theorem cellUnseal_runnable_full_commit_binds (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (preRoots : SysRoots) (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash cellUnsealVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash cellUnsealVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂) :
    absorbedCols e₁ = absorbedCols e₂ ∧ (∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i) :=
  runnable_full_commit_binds (cellUnsealRunnableSpec preRoots) hash hCR e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂

theorem cellUnseal_rejects_root_tamper (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (preRoots : SysRoots) (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash cellUnsealVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash cellUnsealVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) : False :=
  wide_rejects_root_tamper (cellUnsealRunnableSpec preRoots) hash hCR e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-! ## §11 — NON-VACUITY. -/

def cellUnsealPreRoots : SysRoots := emptySystemRoots

def cellUnsealPre : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

def cellUnsealPost : CellState :=
  { balLo := 100, balHi := 0, nonce := 6, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

theorem goodCellUnseal_realizes :
    (cellUnsealRunnableSpec cellUnsealPreRoots).fullClause cellUnsealPre cellUnsealPost cellUnsealPreRoots :=
  ⟨⟨rfl, rfl, rfl, fun _ => rfl, rfl, rfl⟩, rfl⟩

theorem cellUnseal_clause_not_trivial :
    ¬ CellUnsealFullClause cellUnsealPreRoots cellUnsealPre
        { cellUnsealPost with balLo := 999 } cellUnsealPreRoots := by
  rintro ⟨⟨hbal, _, _, _, _, _⟩, _⟩
  simp only [cellUnsealPre] at hbal
  norm_num at hbal

theorem cellUnseal_clause_rejects_root_drop :
    ¬ CellUnsealFullClause cellUnsealPreRoots cellUnsealPre cellUnsealPost
        (fun i => if i = (⟨0, by decide⟩ : Fin N_SYSTEM_ROOTS) then 1 else 0) := by
  rintro ⟨_, hroots⟩
  have h0 := congrFun hroots (⟨0, by decide⟩ : Fin N_SYSTEM_ROOTS)
  simp only [cellUnsealPreRoots, emptySystemRoots] at h0
  norm_num at h0

/-! ## §12 — layout + axiom-hygiene tripwires. -/

#guard cellUnsealVmDescriptor.constraints.length == 13 + 14 + 4 + 3 + 1
#guard cellUnsealVmDescriptor.hashSites.length == 4
#guard cellUnsealVmDescriptor.traceWidth == 186
#guard cellUnsealVmDescriptorWide.traceWidth == 188
#guard cellUnsealVmDescriptorWide.constraints.length == cellUnsealVmDescriptor.constraints.length

#assert_axioms cellUnsealVm_faithful
#assert_axioms cellUnsealDescriptor_full_sound
#assert_axioms cellUnsealGates_give_cellSpec
#assert_axioms cellUnseal_runnable_full_sound
#assert_axioms cellUnseal_runnable_full_commit_binds
#assert_axioms cellUnseal_rejects_root_tamper
#assert_axioms goodCellUnseal_realizes
#assert_axioms cellUnseal_clause_not_trivial
#assert_axioms cellUnseal_clause_rejects_root_drop

end Dregg2.Circuit.Emit.EffectVmEmitCellUnseal
