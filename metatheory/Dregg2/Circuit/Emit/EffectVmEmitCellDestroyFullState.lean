/-
# Dregg2.Circuit.Emit.EffectVmEmitCellDestroyFullState — cellDestroy LIFTED to FULL-STATE on the
RUNNABLE descriptor (the magnesium breadth: the circuit the prover RUNS binds all 17 fields).

`EffectVmEmitCellDestroy` welds the per-cell block (`CellDestroyCellSpec`: economic block FROZEN, the
seq-nonce TICKS) on the 186-wide RUNNABLE descriptor; its `state_commit` absorbs only the 13 state-block
columns, NOT the 8 side-table roots. This module CLOSES that by amplifying cellDestroy's RUNNABLE
descriptor to the WIDE (`system_roots`-absorbing) shape and lifting through the generic
`EffectVmFullStateRunnable.runnable_full_sound` crown: a satisfying WIDE-descriptor witness pins the FULL
17-field declarative post-state — the per-cell block AND every one of the 8 side-table roots FROZEN.

cellDestroy's lifecycle flip-to-Destroyed + deathCert bind are OFF the per-row state block (SOUNDNESS in
universe-A's `cellDestroyA_full_sound`); the RUNNABLE row is the frozen-frame + nonce-tick passthrough. So
its `system_roots` sub-block is FROZEN; the magnesium win is the WIDE commitment now BINDS all 8 roots.
The §RECIPE applied to cellDestroy.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR only via the generic theorems.
`fullClause` NON-VACUOUS. Read-only imports; owns only itself.
-/
import Dregg2.Circuit.Emit.EffectVmEmitCellDestroy
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable

namespace Dregg2.Circuit.Emit.EffectVmEmitCellDestroyFullState

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gFieldPassAll)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitCellDestroy
  (SEL_CELLDESTROY cellDestroyRowGates cellDestroyVmDescriptor RowEncodesDestroy CellDestroyCellSpec
   CellDestroyRowCanon cellDestroyVm_faithful intent_to_cellSpec)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (baseAbsorbedCols RunnableFullStateSpec runnable_full_sound runnable_full_commit_binds wide_rejects_root_tamper
   wideHashSites)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest emptySystemRoots N_SYSTEM_ROOTS)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §1 — the WIDE cellDestroy descriptor (width + sites; constraints UNCHANGED). -/

def cellDestroyVmDescriptorWide : EffectVmDescriptor :=
  { cellDestroyVmDescriptor with
    name := cellDestroyVmDescriptor.name ++ "-sysroots"
    traceWidth := EFFECT_VM_WIDTH_SYSROOTS
    hashSites := wideHashSites }

theorem cellDestroyWide_constraints_eq :
    cellDestroyVmDescriptorWide.constraints = cellDestroyVmDescriptor.constraints := rfl

/-- The row hypothesis: a cellDestroy row (`s_cellDestroy = 1`, `s_noop = 0`). -/
def IsCellDestroyRow (env : VmRowEnv) : Prop :=
  env.loc SEL_CELLDESTROY = 1 ∧ env.loc sel.NOOP = 0

/-! ## §2 — the GATE-ONLY per-cell soundness (no hash-site hypothesis). -/

theorem cellDestroyGates_give_cellSpec (env : VmRowEnv) (pre post : CellState)
    (hnoop : env.loc sel.NOOP = 0) (hcanon : CellDestroyRowCanon env)
    (henc : RowEncodesDestroy env pre post)
    (hgates : ∀ c ∈ cellDestroyVmDescriptor.constraints, c.holdsVm env true false) :
    CellDestroyCellSpec pre post := by
  have hrowgates : ∀ c ∈ cellDestroyRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ cellDestroyVmDescriptor.constraints := by
      unfold cellDestroyVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
    have hh := hgates c hmem
    unfold cellDestroyRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using hh
  exact intent_to_cellSpec env pre post hnoop henc ((cellDestroyVm_faithful env hcanon).mp hrowgates)

/-! ## §3 — the FULL declarative clause + the `RunnableFullStateSpec` instance. -/

def CellDestroyFullClause (preRoots : SysRoots) (pre post : CellState) (postRoots : SysRoots) : Prop :=
  CellDestroyCellSpec pre post ∧ postRoots = preRoots

def cellDestroyRunnableSpec (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor    := cellDestroyVmDescriptorWide
  usesWideSites := rfl
  isRow         := fun env => IsCellDestroyRow env ∧ CellDestroyRowCanon env
  decodeAfter   := fun env pre post postRoots =>
    RowEncodesDestroy env pre post ∧ postRoots = preRoots
  fullClause    := CellDestroyFullClause preRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots⟩ := hdec
    exact ⟨cellDestroyGates_give_cellSpec env pre post hrow.1.2 hrow.2 henc
            (cellDestroyWide_constraints_eq ▸ hgates), hroots⟩

/-! ## §4 — THE DELIVERABLE: `cellDestroy_runnable_full_sound`. -/

/-- **`cellDestroy_runnable_full_sound` — the magnesium crown for cellDestroy.** A row satisfying the WIDE
RUNNABLE cellDestroy descriptor, decoded by `RowEncodesDestroy` with the frozen-roots witness, pins the
FULL 17-field post-state: the per-cell block (`CellDestroyCellSpec`) AND all 8 side-table roots FROZEN. -/
theorem cellDestroy_runnable_full_sound (hash : List ℤ → ℤ) (preRoots : SysRoots)
    (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsCellDestroyRow env) (hcanon : CellDestroyRowCanon env)
    (henc : RowEncodesDestroy env pre post) (hroots : postRoots = preRoots)
    (hsat : satisfiedVm hash cellDestroyVmDescriptorWide env true false) :
    CellDestroyCellSpec pre post ∧ postRoots = preRoots :=
  runnable_full_sound (cellDestroyRunnableSpec preRoots) hash env pre post postRoots
    ⟨hrow, hcanon⟩ ⟨henc, hroots⟩ hsat

/-! ## §5 — THE ANTI-GHOST. -/

theorem cellDestroy_runnable_full_commit_binds (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (preRoots : SysRoots) (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash cellDestroyVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash cellDestroyVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂) :
    baseAbsorbedCols e₁ = baseAbsorbedCols e₂ ∧ (∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i) :=
  runnable_full_commit_binds (cellDestroyRunnableSpec preRoots) hash hCR e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂

theorem cellDestroy_rejects_root_tamper (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (preRoots : SysRoots) (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash cellDestroyVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash cellDestroyVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) : False :=
  wide_rejects_root_tamper (cellDestroyRunnableSpec preRoots) hash hCR e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-! ## §6 — NON-VACUITY. -/

def cellDestroyPreRoots : SysRoots := emptySystemRoots

def cellDestroyPre : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

def cellDestroyPost : CellState :=
  { balLo := 100, balHi := 0, nonce := 6, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

theorem goodCellDestroy_realizes :
    (cellDestroyRunnableSpec cellDestroyPreRoots).fullClause cellDestroyPre cellDestroyPost cellDestroyPreRoots :=
  ⟨⟨rfl, rfl, rfl, fun _ => rfl, rfl, rfl⟩, rfl⟩

theorem cellDestroy_clause_not_trivial :
    ¬ CellDestroyFullClause cellDestroyPreRoots cellDestroyPre
        { cellDestroyPost with balLo := 999 } cellDestroyPreRoots := by
  rintro ⟨⟨hbal, _, _, _, _, _⟩, _⟩
  simp only [cellDestroyPre] at hbal
  norm_num at hbal

theorem cellDestroy_clause_rejects_root_drop :
    ¬ CellDestroyFullClause cellDestroyPreRoots cellDestroyPre cellDestroyPost
        (fun i => if i = (⟨0, by decide⟩ : Fin N_SYSTEM_ROOTS) then 1 else 0) := by
  rintro ⟨_, hroots⟩
  have h0 := congrFun hroots (⟨0, by decide⟩ : Fin N_SYSTEM_ROOTS)
  simp only [cellDestroyPreRoots, emptySystemRoots] at h0
  norm_num at h0

/-! ## §7 — layout + axiom-hygiene tripwires. -/

#guard cellDestroyVmDescriptorWide.traceWidth == 190
#guard cellDestroyVmDescriptorWide.hashSites.length == 4
#guard cellDestroyVmDescriptorWide.constraints.length == cellDestroyVmDescriptor.constraints.length

#assert_axioms cellDestroyGates_give_cellSpec
#assert_axioms cellDestroy_runnable_full_sound
#assert_axioms cellDestroy_runnable_full_commit_binds
#assert_axioms cellDestroy_rejects_root_tamper
#assert_axioms goodCellDestroy_realizes
#assert_axioms cellDestroy_clause_not_trivial
#assert_axioms cellDestroy_clause_rejects_root_drop

end Dregg2.Circuit.Emit.EffectVmEmitCellDestroyFullState
