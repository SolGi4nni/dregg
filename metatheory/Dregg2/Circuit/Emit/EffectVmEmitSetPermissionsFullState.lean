/-
# Dregg2.Circuit.Emit.EffectVmEmitSetPermissionsFullState — setPermissions LIFTED to FULL-STATE on the
RUNNABLE descriptor (the magnesium breadth: the circuit the prover RUNS binds all 17 fields).

`EffectVmEmitSetPermissions` welds the per-cell block (`PermCellSpec`: economic block FROZEN, the
seq-nonce TICKS) on the 186-wide RUNNABLE descriptor; its `state_commit` absorbs only the 13 state-block
columns, NOT the 8 side-table roots. This module CLOSES that by amplifying the RUNNABLE descriptor to the
WIDE (`system_roots`-absorbing) shape and lifting through the generic
`EffectVmFullStateRunnable.runnable_full_sound` crown: a satisfying WIDE-descriptor witness pins the FULL
17-field declarative post-state — the per-cell block AND every one of the 8 side-table roots FROZEN.

setPermissions writes the permissions slot OFF-row (its SOUNDNESS is the universe-A leg); the RUNNABLE row
is the frozen-frame + nonce-tick passthrough. So its `system_roots` sub-block is FROZEN; the magnesium win
is the WIDE commitment now BINDS all 8 roots. The `cap_root` column is absorbed (it rides the per-cell
block), so a `cap_root` tamper is anti-ghosted too; the cap-graph MEMBERSHIP stays the named opaque digest
(a refinement, not a soundness gap). The §RECIPE applied to setPermissions.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR only via the generic theorems.
No `sorry`/`:= True`/`native_decide`. `fullClause` NON-VACUOUS. Read-only imports; owns only itself.
-/
import Dregg2.Circuit.Emit.EffectVmEmitSetPermissions
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable

namespace Dregg2.Circuit.Emit.EffectVmEmitSetPermissionsFullState

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gFieldPassAll)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState absorbedCols)
open Dregg2.Circuit.Emit.EffectVmEmitSetPermissions
  (SEL_SET_PERMS IsSetPermsRow setPermsRowGates setPermsVmDescriptor RowEncodesPerms PermCellSpec
   setPermsVm_faithful intent_to_permCellSpec)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (RunnableFullStateSpec runnable_full_sound runnable_full_commit_binds wide_rejects_root_tamper
   wideHashSites)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest emptySystemRoots N_SYSTEM_ROOTS)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §1 — the WIDE setPermissions descriptor (width + sites; constraints UNCHANGED). -/

def setPermsVmDescriptorWide : EffectVmDescriptor :=
  { setPermsVmDescriptor with
    name := setPermsVmDescriptor.name ++ "-sysroots"
    traceWidth := EFFECT_VM_WIDTH_SYSROOTS
    hashSites := wideHashSites }

theorem setPermsWide_constraints_eq :
    setPermsVmDescriptorWide.constraints = setPermsVmDescriptor.constraints := rfl

/-! ## §2 — the GATE-ONLY per-cell soundness (no hash-site hypothesis). -/

theorem setPermsGates_give_cellSpec (env : VmRowEnv) (pre post : CellState)
    (hnoop : env.loc sel.NOOP = 0) (henc : RowEncodesPerms env pre post)
    (hgates : ∀ c ∈ setPermsVmDescriptor.constraints, c.holdsVm env true true) :
    PermCellSpec pre post := by
  have hrowgates : ∀ c ∈ setPermsRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ setPermsVmDescriptor.constraints := by
      unfold setPermsVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
    have hh := hgates c hmem
    unfold setPermsRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using hh
  exact intent_to_permCellSpec env pre post hnoop henc ((setPermsVm_faithful env).mp hrowgates)

/-! ## §3 — the FULL declarative clause + the `RunnableFullStateSpec` instance. -/

def SetPermsFullClause (preRoots : SysRoots) (pre post : CellState) (postRoots : SysRoots) : Prop :=
  PermCellSpec pre post ∧ postRoots = preRoots

def setPermsRunnableSpec (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor    := setPermsVmDescriptorWide
  usesWideSites := rfl
  isRow         := IsSetPermsRow
  decodeAfter   := fun env pre post postRoots =>
    RowEncodesPerms env pre post ∧ postRoots = preRoots
  fullClause    := SetPermsFullClause preRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots⟩ := hdec
    exact ⟨setPermsGates_give_cellSpec env pre post hrow.2 henc
            (setPermsWide_constraints_eq ▸ hgates), hroots⟩

/-! ## §4 — THE DELIVERABLE: `setPermissions_runnable_full_sound`. -/

/-- **`setPermissions_runnable_full_sound` — the magnesium crown for setPermissions.** A row satisfying
the WIDE RUNNABLE descriptor, decoded by `RowEncodesPerms` with the frozen-roots witness, pins the FULL
17-field post-state: the per-cell block (`PermCellSpec`) AND all 8 side-table roots FROZEN. -/
theorem setPermissions_runnable_full_sound (hash : List ℤ → ℤ) (preRoots : SysRoots)
    (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsSetPermsRow env)
    (henc : RowEncodesPerms env pre post) (hroots : postRoots = preRoots)
    (hsat : satisfiedVm hash setPermsVmDescriptorWide env true true) :
    PermCellSpec pre post ∧ postRoots = preRoots :=
  runnable_full_sound (setPermsRunnableSpec preRoots) hash env pre post postRoots hrow
    ⟨henc, hroots⟩ hsat

/-! ## §5 — THE ANTI-GHOST. -/

theorem setPermissions_runnable_full_commit_binds (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (preRoots : SysRoots) (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash setPermsVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash setPermsVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂) :
    absorbedCols e₁ = absorbedCols e₂ ∧ (∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i) :=
  runnable_full_commit_binds (setPermsRunnableSpec preRoots) hash hCR e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂

theorem setPermissions_rejects_root_tamper (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (preRoots : SysRoots) (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash setPermsVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash setPermsVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) : False :=
  wide_rejects_root_tamper (setPermsRunnableSpec preRoots) hash hCR e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-! ## §6 — NON-VACUITY. -/

def setPermsPreRoots : SysRoots := emptySystemRoots

def setPermsPre : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

def setPermsPost : CellState :=
  { balLo := 100, balHi := 0, nonce := 6, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

theorem goodSetPerms_realizes :
    (setPermsRunnableSpec setPermsPreRoots).fullClause setPermsPre setPermsPost setPermsPreRoots :=
  ⟨⟨rfl, rfl, rfl, fun _ => rfl, rfl, rfl⟩, rfl⟩

theorem setPerms_clause_not_trivial :
    ¬ SetPermsFullClause setPermsPreRoots setPermsPre { setPermsPost with balLo := 999 } setPermsPreRoots := by
  rintro ⟨⟨hbal, _, _, _, _, _⟩, _⟩
  simp only [setPermsPre] at hbal
  norm_num at hbal

theorem setPerms_clause_rejects_root_drop :
    ¬ SetPermsFullClause setPermsPreRoots setPermsPre setPermsPost
        (fun i => if i = (⟨0, by decide⟩ : Fin N_SYSTEM_ROOTS) then 1 else 0) := by
  rintro ⟨_, hroots⟩
  have h0 := congrFun hroots (⟨0, by decide⟩ : Fin N_SYSTEM_ROOTS)
  simp only [setPermsPreRoots, emptySystemRoots] at h0
  norm_num at h0

/-! ## §7 — layout + axiom-hygiene tripwires. -/

#guard setPermsVmDescriptorWide.traceWidth == 188
#guard setPermsVmDescriptorWide.hashSites.length == 4
#guard setPermsVmDescriptorWide.constraints.length == setPermsVmDescriptor.constraints.length

#assert_axioms setPermsGates_give_cellSpec
#assert_axioms setPermissions_runnable_full_sound
#assert_axioms setPermissions_runnable_full_commit_binds
#assert_axioms setPermissions_rejects_root_tamper
#assert_axioms goodSetPerms_realizes
#assert_axioms setPerms_clause_not_trivial
#assert_axioms setPerms_clause_rejects_root_drop

end Dregg2.Circuit.Emit.EffectVmEmitSetPermissionsFullState
