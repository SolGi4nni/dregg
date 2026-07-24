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

## What the EffectVM row CANNOT enforce (the boundary — the WHOLE point of the effect)

  * the `lifecycle` flip Sealed → Live — a per-cell SIDE-TABLE, NO EffectVM column. Its SOUNDNESS lives
    ONLY in universe-A's `cellUnsealA_full_sound` (the `Inst/cellUnsealA.lean` v2 `Surface2` descriptor).

## The FULL-STATE lift (the magnesium breadth, the §RECIPE of `EffectVmFullStateRunnable`)

The 186-wide row's `state_commit` absorbs only the 13 state-block columns. This module WIDENS the
descriptor to the `system_roots`-absorbing shape (`EFFECT_VM_WIDTH_SYSROOTS`, `wideHashSites`) and lifts
through the generic `runnable_full_sound`: a satisfying WIDE-descriptor witness pins the FULL 17-field
post-state — the per-cell block (`CellUnsealCellSpec`) AND every one of the 8 side-table roots FROZEN
(cellUnseal touches no side-table on-row). The anti-ghost tooth bites on all 17 (incl. any root).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The anti-ghost theorems carry NO
collision-resistance hypothesis: they conclude a disjunction naming the sponge collision they would
otherwise assume away. `fullClause` NON-VACUOUS. Read-only imports; owns only its own declarations.

## The field-faithful denotation

Gates hold `≡ 0 [ZMOD 2013265921]` (BabyBear), not ℤ `= 0`. The ℤ-stated intent is read back through
the EXPLICIT canonicality envelope `CellUnsealRowCanon` (state cells canonical in `[0, p)`, boolean
NOOP, in-field nonce tick — the deployed range-check invariant), witnessed satisfiable by
`goodUnsealRow_canonical`; the anti-ghost teeth carry the same per-cell bounds (`¬ (p ∣ residual)`).
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable
import Dregg2.Circuit.Emit.EffectVmRowCommitReduction

namespace Dregg2.Circuit.Emit.EffectVmEmitCellUnseal

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA eSub eSelNoop gBalHi gNonce gCapPass gResPass gFieldPass gFieldPassAll
   transitionAll boundaryFirstPins boundaryLastPins transferHashSites boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState absorbed_determined_by_commit_of_injective)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (baseAbsorbedCols RunnableFullStateSpec runnable_full_sound runnable_full_commit_binds_or_collides
   wide_rejects_root_tamper_or_collides WideColl RootsColl wideHashSites)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
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
  , piCount := 42
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

/-- **`CellUnsealRowCanon env`** — the row's EXPLICIT canonicality envelope (the deployed range-check /
field-representative invariant, carried as named hypotheses): every state-block cell of both windows
is a canonical BabyBear representative in `[0, p)`; the NOOP selector is boolean (GROUP-1 selector
validity); and the pre-nonce tick stays in-field (`nonce_before + 1 < p` — the per-cell sequence
counter is far below `p`). Under the mod-p `holdsVm` denotation these are exactly the hypotheses that
let the ℤ-stated row intent be read back off the field-checked gates (a `≡ 0 [ZMOD p]` residual
strictly inside `(-p, p)` is `0`). -/
def CellUnsealRowCanon (env : VmRowEnv) : Prop :=
  (∀ off, off < STATE_SIZE →
      (0 ≤ env.loc (sbCol off) ∧ env.loc (sbCol off) < 2013265921)
      ∧ (0 ≤ env.loc (saCol off) ∧ env.loc (saCol off) < 2013265921))
  ∧ (env.loc sel.NOOP = 0 ∨ env.loc sel.NOOP = 1)
  ∧ env.loc (sbCol state.NONCE) + 1 < 2013265921

/-! ## §5 — FAITHFULNESS (mod-p, under the explicit canonicality envelope). -/

/-- **`cellUnsealVm_faithful`.** On a cellUnseal row, under the explicit canonicality envelope, the
emitted per-row gates all hold IFF `CellUnsealRowIntent` holds — the gates pin EXACTLY the passthrough
+ nonce-tick, read back off the field-checked (`≡ 0 [ZMOD p]`) bodies via canonicality. -/
theorem cellUnsealVm_faithful (env : VmRowEnv) (hcanon : CellUnsealRowCanon env) :
    (∀ c ∈ cellUnsealRowGates, c.holdsVm env false false) ↔ CellUnsealRowIntent env := by
  obtain ⟨hcells, hnoopB, hovf⟩ := hcanon
  have hbLo := hcells state.BALANCE_LO (by norm_num [state.BALANCE_LO, STATE_SIZE])
  have hbHi := hcells state.BALANCE_HI (by norm_num [state.BALANCE_HI, STATE_SIZE])
  have hbN := hcells state.NONCE (by norm_num [state.NONCE, STATE_SIZE])
  have hbCap := hcells state.CAP_ROOT (by norm_num [state.CAP_ROOT, STATE_SIZE])
  have hbRes := hcells state.RESERVED (by norm_num [state.RESERVED, STATE_SIZE])
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
    rw [Int.modEq_zero_iff_dvd] at hLo hHi hNon hCap hRes
    refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
    intro i hi
    have hFi := hFld i hi
    have hbF := hcells (state.FIELD_BASE + i) (by simp only [state.FIELD_BASE, STATE_SIZE]; omega)
    simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval] at hFi
    rw [Int.modEq_zero_iff_dvd] at hFi
    omega
  · rintro ⟨hLo, hHi, hNon, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
      rw [Int.modEq_zero_iff_dvd]; omega
    · simp only [VmConstraint.holdsVm, gBalHi, eSA, eSB, eSub, EmittedExpr.eval]
      rw [Int.modEq_zero_iff_dvd]; omega
    · simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
      rw [Int.modEq_zero_iff_dvd]; omega
    · simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [Int.modEq_zero_iff_dvd]; omega
    · simp only [VmConstraint.holdsVm, gResPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [Int.modEq_zero_iff_dvd]; omega
    · simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [Int.modEq_zero_iff_dvd]
      have := hFld i hi
      omega

/-! ## §6 — ANTI-GHOST (gate level; the teeth carry the explicit canonicality — none dropped). -/

/-- **Anti-ghost (balance moved).** A row whose post-`bal_lo` ≠ pre-`bal_lo` fails the freeze gate — a
lifecycle flag flip cannot silently move value. Both cells canonical in `[0, p)` (the deployed
range-check invariant), so the moved-balance residual is nonzero strictly inside `(-p, p)`:
`¬ (p ∣ residual)`. -/
theorem cellUnsealVm_rejects_moved_balance (env : VmRowEnv)
    (hsa : 0 ≤ env.loc (saCol state.BALANCE_LO) ∧ env.loc (saCol state.BALANCE_LO) < 2013265921)
    (hsb : 0 ≤ env.loc (sbCol state.BALANCE_LO) ∧ env.loc (sbCol state.BALANCE_LO) < 2013265921)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (VmConstraint.gate gBalLoFreeze).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
  rw [Int.modEq_zero_iff_dvd]
  intro h
  exact hwrong (by omega)

/-- **Anti-ghost (nonce tamper).** A row whose nonce does NOT tick by 1 (on `s_noop = 0`) fails the
reconciled `gNonce` tick gate. Canonicality: both nonce cells canonical, the tick in-field
(`nonce_before + 1 < p`), the NOOP selector boolean — the tampered residual lies strictly inside
`(-p, p)` and is nonzero. -/
theorem cellUnsealVm_rejects_nonce_freeze (env : VmRowEnv)
    (hsa : 0 ≤ env.loc (saCol state.NONCE) ∧ env.loc (saCol state.NONCE) < 2013265921)
    (hsb : 0 ≤ env.loc (sbCol state.NONCE) ∧ env.loc (sbCol state.NONCE) + 1 < 2013265921)
    (hnoopB : env.loc sel.NOOP = 0 ∨ env.loc sel.NOOP = 1)
    (hwrong : env.loc (saCol state.NONCE) ≠ env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)) :
    ¬ (VmConstraint.gate gNonce).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
  rw [Int.modEq_zero_iff_dvd]
  intro h
  have hnoop01 : 0 ≤ env.loc sel.NOOP ∧ env.loc sel.NOOP ≤ 1 := by
    rcases hnoopB with h' | h' <;> rw [h'] <;> norm_num
  exact hwrong (by omega)

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
FROZEN; the nonce TICKS by 1. (The lifecycle Sealed→Live flip is off-block — the boundary.) -/
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
    (hcanon : CellUnsealRowCanon env)
    (hpubc : 0 ≤ env.pub pi.NEW_COMMIT ∧ env.pub pi.NEW_COMMIT < 2013265921)
    (henc : RowEncodesUnseal env pre post)
    (hgatesat : satisfiedVm hash cellUnsealVmDescriptor env true false)
    (hsat : satisfiedVm hash cellUnsealVmDescriptor env true true) :
    CellUnsealCellSpec pre post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  obtain ⟨hcsT, _⟩ := hgatesat
  have hgates' : ∀ c ∈ cellUnsealRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ cellUnsealVmDescriptor.constraints := by
      unfold cellUnsealVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
    have := hcsT c hmem
    unfold cellUnsealRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (cellUnsealVm_faithful env hcanon).mp hgates'
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
  -- The NEW_COMMIT pin (mod-p) lifted to ℤ equality by canonicality of the commit cell + the PI.
  have hmod := (boundaryLast_pins env hlast).1
  have hdvd := Int.ModEq.dvd hmod
  have hcell := (hcanon.1 state.STATE_COMMIT (by norm_num [state.STATE_COMMIT, STATE_SIZE])).2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]
  omega

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

/-- The GATE-ONLY per-cell soundness (no hash-site hypothesis — the THIN per-effect content),
under the explicit canonicality envelope (the mod-p read-back needs it). -/
theorem cellUnsealGates_give_cellSpec (env : VmRowEnv) (pre post : CellState)
    (hnoop : env.loc sel.NOOP = 0) (hcanon : CellUnsealRowCanon env)
    (henc : RowEncodesUnseal env pre post)
    (hgates : ∀ c ∈ cellUnsealVmDescriptor.constraints, c.holdsVm env true false) :
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
  exact intent_to_cellSpec env pre post hnoop henc ((cellUnsealVm_faithful env hcanon).mp hrowgates)

/-- **`CellUnsealFullClause`** — the FULL 17-field declarative post for cellUnseal: the per-cell
`CellUnsealCellSpec` (economic block FROZEN, the seq-nonce TICKS) AND the `system_roots` sub-block FROZEN. -/
def CellUnsealFullClause (preRoots : SysRoots) (pre post : CellState) (postRoots : SysRoots) : Prop :=
  CellUnsealCellSpec pre post ∧ postRoots = preRoots

/-- **`cellUnsealRunnableSpec`** — the FULL-state RUNNABLE instance for cellUnseal. THIN; NON-VACUOUS.
The structured decode carries the explicit canonicality envelope (`CellUnsealRowCanon` — the deployed
range-check invariant), which the mod-p gate read-back consumes; `goodUnsealRow_canonical` witnesses
its satisfiability. -/
def cellUnsealRunnableSpec (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor    := cellUnsealVmDescriptorWide
  usesWideSites := rfl
  isRow         := IsCellUnsealRow
  decodeAfter   := fun env pre post postRoots =>
    RowEncodesUnseal env pre post ∧ postRoots = preRoots ∧ CellUnsealRowCanon env
  fullClause    := CellUnsealFullClause preRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots, hcanon⟩ := hdec
    exact ⟨cellUnsealGates_give_cellSpec env pre post hrow.2 hcanon henc
            (cellUnsealWide_constraints_eq ▸ hgates), hroots⟩

/-- **`cellUnseal_runnable_full_sound` — the magnesium crown for cellUnseal.** A row satisfying the WIDE
RUNNABLE cellUnseal descriptor, decoded by `RowEncodesUnseal` with the frozen-roots witness, pins the
FULL 17-field post-state: the per-cell block (`CellUnsealCellSpec`) AND all 8 side-table roots FROZEN. -/
theorem cellUnseal_runnable_full_sound (hash : List ℤ → ℤ) (preRoots : SysRoots)
    (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsCellUnsealRow env) (hcanon : CellUnsealRowCanon env)
    (henc : RowEncodesUnseal env pre post) (hroots : postRoots = preRoots)
    (hsat : satisfiedVm hash cellUnsealVmDescriptorWide env true false) :
    CellUnsealCellSpec pre post ∧ postRoots = preRoots :=
  runnable_full_sound (cellUnsealRunnableSpec preRoots) hash env pre post postRoots hrow
    ⟨henc, hroots, hcanon⟩ hsat

/-! ## §10 — THE ANTI-GHOST. -/

/-- **`cellUnseal_runnable_full_commit_binds_or_collides` — the cellUnseal anti-ghost.** Two wide
cellUnseal rows publishing the same `NEW_COMMIT` (with `systemRootsDigest` carriers) EITHER agree on
all 12 absorbed state-block columns AND pointwise on the 8 side-table roots, OR exhibit a collision of
the deployed sponge — at the wide absorb, or at the two root lists.

The old form concluded the bare conjunction from `Poseidon2SpongeCR hash`, which the deployed sponge
REFUTES; at deployed parameters it was vacuous. The disjunction is formally weaker and HOLDS of the
deployed sponge. -/
theorem cellUnseal_runnable_full_commit_binds_or_collides (hash : List ℤ → ℤ)
    (preRoots : SysRoots) (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash cellUnsealVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash cellUnsealVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂) :
    (baseAbsorbedCols e₁ = baseAbsorbedCols e₂ ∧ (∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i))
    ∨ WideColl hash e₁ e₂ ∨ RootsColl hash sr₁ sr₂ :=
  runnable_full_commit_binds_or_collides (cellUnsealRunnableSpec preRoots) hash e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂

/-- **`cellUnseal_rejects_root_tamper_or_collides` — side-table anti-ghost for cellUnseal.** Two wide
cellUnseal rows publishing the same `NEW_COMMIT` whose side-table sub-blocks DIFFER at some index `i`
exhibit a collision of the deployed sponge: forging a side-table root under a fixed commitment costs a
sponge collision.

The old form concluded `False` from `Poseidon2SpongeCR hash`, which the deployed sponge REFUTES; at
deployed parameters it was vacuous. This one names the collision instead of assuming it away. -/
theorem cellUnseal_rejects_root_tamper_or_collides (hash : List ℤ → ℤ)
    (preRoots : SysRoots) (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash cellUnsealVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash cellUnsealVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) :
    WideColl hash e₁ e₂ ∨ RootsColl hash sr₁ sr₂ :=
  wide_rejects_root_tamper_or_collides (cellUnsealRunnableSpec preRoots) hash e₁ e₂ sr₁ sr₂
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

/-! ## §11b — NON-VACUITY at the ROW level: a concrete runtime cellUnseal row realizes the intent AND
the canonicality envelope (so the mod-p hypotheses are jointly satisfiable, not a vacuous guard);
concrete tampers are rejected. -/

/-- A concrete cellUnseal row: state-block passthrough + nonce TICK (bal_lo 100 → 100, nonce 5 → 6,
frame 0, `s_noop = 0`). -/
def goodUnsealRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_CELLUNSEAL then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 100
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 6
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

theorem goodUnsealRow_noop : goodUnsealRow.loc sel.NOOP = 0 := by
  show goodUnsealRow.loc 0 = 0
  simp only [goodUnsealRow, SEL_CELLUNSEAL, sbCol, saCol, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE]
  norm_num

/-- **NON-VACUITY (witness TRUE).** `goodUnsealRow` REALIZES the runtime cellUnseal intent
(passthrough + nonce tick). -/
theorem goodUnsealRow_realizes_intent : CellUnsealRowIntent goodUnsealRow := by
  unfold CellUnsealRowIntent
  have hnoop : goodUnsealRow.loc sel.NOOP = 0 := goodUnsealRow_noop
  refine ⟨rfl, rfl, ?_, rfl, rfl, ?_⟩
  · rw [hnoop]
    show goodUnsealRow.loc (saCol state.NONCE) = goodUnsealRow.loc (sbCol state.NONCE) + (1 - 0)
    simp only [goodUnsealRow, SEL_CELLUNSEAL, sbCol, saCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE]
    norm_num
  · intro i hi
    show goodUnsealRow.loc (saCol (state.FIELD_BASE + i)) = goodUnsealRow.loc (sbCol (state.FIELD_BASE + i))
    simp only [goodUnsealRow, SEL_CELLUNSEAL, sbCol, saCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE, state.FIELD_BASE]
    have e1 : (76 + (3 + i) = 50) = False := eq_false (by omega)
    have e2 : (76 + (3 + i) = 54 + 0) = False := eq_false (by omega)
    have e3 : (76 + (3 + i) = 76 + 0) = False := eq_false (by omega)
    have e4 : (76 + (3 + i) = 54 + 2) = False := eq_false (by omega)
    have e5 : (76 + (3 + i) = 76 + 2) = False := eq_false (by omega)
    have f1 : (54 + (3 + i) = 50) = False := eq_false (by omega)
    have f2 : (54 + (3 + i) = 54 + 0) = False := eq_false (by omega)
    have f3 : (54 + (3 + i) = 76 + 0) = False := eq_false (by omega)
    have f4 : (54 + (3 + i) = 54 + 2) = False := eq_false (by omega)
    have f5 : (54 + (3 + i) = 76 + 2) = False := eq_false (by omega)
    simp only [e1, e2, e3, e4, e5, f1, f2, f3, f4, f5, if_false]

/-- **NON-VACUITY (canonicality witness).** The honest row satisfies the explicit canonicality
envelope — the mod-p hypotheses are jointly satisfiable, not a vacuous guard. -/
theorem goodUnsealRow_canonical : CellUnsealRowCanon goodUnsealRow := by
  refine ⟨?_, Or.inl goodUnsealRow_noop, ?_⟩
  · intro off hoff
    have hall : ∀ v, 0 ≤ goodUnsealRow.loc v ∧ goodUnsealRow.loc v < 2013265921 := by
      intro v
      simp only [goodUnsealRow]
      split_ifs <;> norm_num
    exact ⟨hall _, hall _⟩
  · show goodUnsealRow.loc (sbCol state.NONCE) + 1 < 2013265921
    simp only [goodUnsealRow, SEL_CELLUNSEAL, sbCol, saCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE]
    norm_num

/-- A FORGED cellUnseal row: `goodUnsealRow` with the post-`bal_lo` minted to `999`. -/
def badUnsealRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodUnsealRow.loc v
  nxt := goodUnsealRow.nxt
  pub := goodUnsealRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badUnsealRow`'s post-`bal_lo` is NOT
frozen (forged mint), so `gBalLoFreeze` REJECTS it — a concrete UNSAT (conservation has teeth). -/
theorem badUnsealRow_rejected : ¬ (VmConstraint.gate gBalLoFreeze).holdsVm badUnsealRow false false := by
  apply cellUnsealVm_rejects_moved_balance <;>
    · simp only [badUnsealRow, goodUnsealRow, sbCol, saCol, SEL_CELLUNSEAL, STATE_BEFORE_BASE,
        STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
        state.NONCE]
      norm_num

/-- A FROZEN-NONCE cellUnseal row: `goodUnsealRow` with the post-nonce held at `5`. -/
def staleNonceUnsealRow : VmRowEnv where
  loc := fun v => if v = saCol state.NONCE then 5 else goodUnsealRow.loc v
  nxt := goodUnsealRow.nxt
  pub := goodUnsealRow.pub

/-- **NON-VACUITY (cutover witness FALSE).** A frozen-nonce row is UNSAT under the reconciled `gNonce`
tick gate — the descriptor agrees with the hand-AIR (which ticks). -/
theorem staleNonceUnsealRow_rejected :
    ¬ (VmConstraint.gate gNonce).holdsVm staleNonceUnsealRow false false := by
  apply cellUnsealVm_rejects_nonce_freeze
  · simp only [staleNonceUnsealRow, goodUnsealRow, sbCol, saCol, SEL_CELLUNSEAL,
      STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
      state.BALANCE_LO, state.NONCE]
    norm_num
  · simp only [staleNonceUnsealRow, goodUnsealRow, sbCol, saCol, SEL_CELLUNSEAL,
      STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
      state.BALANCE_LO, state.NONCE]
    norm_num
  · left
    simp only [staleNonceUnsealRow, goodUnsealRow, sel.NOOP, sbCol, saCol, SEL_CELLUNSEAL,
      STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
      state.BALANCE_LO, state.NONCE]
    norm_num
  · simp only [staleNonceUnsealRow, goodUnsealRow, sel.NOOP, sbCol, saCol, SEL_CELLUNSEAL,
      STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
      state.BALANCE_LO, state.NONCE]
    norm_num

/-! ## §12 — layout + axiom-hygiene tripwires. -/

#guard cellUnsealVmDescriptor.constraints.length == 13 + 14 + 4 + 3 + 1
#guard cellUnsealVmDescriptor.hashSites.length == 4
#guard cellUnsealVmDescriptor.traceWidth == 188
#guard cellUnsealVmDescriptorWide.traceWidth == 190
#guard cellUnsealVmDescriptorWide.constraints.length == cellUnsealVmDescriptor.constraints.length

#assert_axioms cellUnsealVm_faithful
#assert_axioms cellUnsealVm_rejects_moved_balance
#assert_axioms cellUnsealVm_rejects_nonce_freeze
#assert_axioms cellUnsealDescriptor_full_sound
#assert_axioms cellUnsealGates_give_cellSpec
#assert_axioms cellUnseal_runnable_full_sound
#assert_axioms cellUnseal_runnable_full_commit_binds_or_collides
#assert_axioms cellUnseal_rejects_root_tamper_or_collides
#assert_axioms goodCellUnseal_realizes
#assert_axioms cellUnseal_clause_not_trivial
#assert_axioms cellUnseal_clause_rejects_root_drop
#assert_axioms goodUnsealRow_realizes_intent
#assert_axioms goodUnsealRow_canonical
#assert_axioms badUnsealRow_rejected
#assert_axioms staleNonceUnsealRow_rejected

/-! ## §ROM — ⚡ THE ROM SUCCESSORS: the commitment legs as REDUCTIONS on the PROVED
keyed floor.

⚡ STATUS (2026-07-24). The `…_or_collides` exportS above carry TWO kinds of content: the
DETERMINISTIC constraint-side extraction (`satisfiedVm` ⇒ the shared published commit and the
absorbed columns — circuit content, not a security claim) and the collision pricing, which as a
bare disjunction was a SHIRK — at deployed BabyBear parameters a sponge collision EXISTS by
pigeonhole, so the disjunction holds through its right branch with NO binding. The security
statementS are THIS section's reductionS: the deployed absorb schedule at this site is the
keystone chain (the wide runnable schedule (`cellUnsealVmDescriptorWide` rides `wideHashSites`; `cellUnsealHashSites := transferHashSites`)), so the site's commitment equivocation at the SAMPLED oracle
IS the row ROM forgery, priced by `EffectVmRowCommitReduction`'s union bound on
`KeyedRomFloor.keyedRom_hard` — the birthday bound, a THEOREM. NO refuted floor, NO cost model;
the modelling step is `RomCarrierSites`' labelled idealisation (ideal `Fin (2 ^ l)` digest vs the
deployed ~31-bit felt, said out loud). The disjunctionS stay as the deterministic
extractor/constraint machinery the downstream consumers `rcases` on. -/

section RomSuccessor

open Dregg2.Circuit.Emit.EffectVmRowCommitReduction
  (wideRomFamily wideRomBreakGame effectVmWideRomForgery wideRow_binds_rom
   effectVmWideRomStateTamper wide_state_tamper_rom
   effectVmWideRomRootTamper wide_root_tamper_rom)
open Dregg2.Crypto.SpongeCarrierReduction (SpongeKeyed)
open Dregg2.Crypto.RomCarrierSites (RomForgeryEff)
open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded)
open Dregg2.Crypto.FloorGames (Adversary gameAdv)

/-- **⚡⚡ THE CELL-UNSEAL FULL-STATE BINDING, DISCHARGED** — the ROM successor of
`cellUnseal_runnable_full_commit_binds_or_collides`: every query-bounded forger that equivocates
the whole 17-field nested wide commitment has NEGLIGIBLE advantage (`wideRow_binds_rom`). -/
theorem cellUnseal_runnable_full_commit_binds_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (wideRomBreakGame D tagDec))
    (hA : RomForgeryEff (wideRomFamily D tagDec) (effectVmWideRomForgery D tagDec) Q A) :
    Negl (gameAdv (wideRomBreakGame D tagDec) A) :=
  wideRow_binds_rom D tagDec Q hQ A hA

/-- **⚡ THE CELL-UNSEAL SIDE-TABLE TOOTH, DISCHARGED** — the ROM successor of
`cellUnseal_rejects_root_tamper_or_collides` (`wide_root_tamper_rom`). -/
theorem cellUnseal_rejects_root_tamper_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (effectVmWideRomRootTamper D tagDec).game)
    (hA : RomForgeryEff (wideRomFamily D tagDec) (effectVmWideRomRootTamper D tagDec) Q A) :
    Negl (gameAdv (effectVmWideRomRootTamper D tagDec).game A) :=
  wide_root_tamper_rom D tagDec Q hQ A hA

end RomSuccessor

#assert_axioms cellUnseal_runnable_full_commit_binds_rom
#assert_axioms cellUnseal_rejects_root_tamper_rom

end Dregg2.Circuit.Emit.EffectVmEmitCellUnseal
