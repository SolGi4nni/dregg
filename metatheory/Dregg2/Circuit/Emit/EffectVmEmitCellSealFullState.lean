/-
# Dregg2.Circuit.Emit.EffectVmEmitCellSealFullState — cellSeal LIFTED to FULL-STATE on the RUNNABLE
descriptor (the magnesium breadth: the circuit the prover RUNS binds all 17 fields).

`EffectVmEmitCellSeal` welds the per-cell block (`CellSealCellSpec`: economic block FROZEN, the seq-nonce
TICKS) on the 186-wide RUNNABLE descriptor; its `state_commit` absorbs only the 13 state-block columns,
NOT the 8 side-table roots (the dominant Class-C gap). This module CLOSES that by amplifying cellSeal's
RUNNABLE descriptor to the WIDE (`system_roots`-absorbing) shape and lifting through the generic
`EffectVmFullStateRunnable.runnable_full_sound` crown: a satisfying WIDE-descriptor witness pins the FULL
17-field declarative post-state — the per-cell block AND every one of the 8 side-table roots FROZEN.

cellSeal's lifecycle Live→Sealed flip is OFF the per-row state block (its SOUNDNESS lives in universe-A's
`cellSealA_full_sound`); the RUNNABLE row is the frozen-frame + nonce-tick passthrough. So its
`system_roots` sub-block is FROZEN (`postRoots = preRoots`); the magnesium win is that the WIDE commitment
now BINDS all 8 roots, so a prover CANNOT tamper any side-table root while keeping the published
`NEW_COMMIT` (the anti-ghost tooth bites on all 17). The §RECIPE applied to cellSeal.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY through the generic
`runnable_full_sound`/`runnable_full_commit_binds` (the named `Poseidon2SpongeCR` portal).
`fullClause` is NON-VACUOUS. Imports are read-only; this file owns only
its own declarations.
-/
import Dregg2.Circuit.Emit.EffectVmEmitCellSeal
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable

namespace Dregg2.Circuit.Emit.EffectVmEmitCellSealFullState

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gFieldPassAll)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitCellSeal
  (SEL_CELLSEAL cellSealRowGates cellSealVmDescriptor RowEncodesSeal CellSealCellSpec
   CellSealRowCanon cellSealVm_faithful intent_to_cellSpec)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (baseAbsorbedCols RunnableFullStateSpec runnable_full_sound runnable_full_commit_binds wide_rejects_root_tamper
   wideHashSites)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest emptySystemRoots N_SYSTEM_ROOTS)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §1 — the WIDE cellSeal descriptor (width + sites; constraints UNCHANGED). -/

/-- **`cellSealVmDescriptorWide`** — cellSeal's descriptor WIDENED: the SAME passthrough+nonce-tick gates
+ transitions + boundary pins + selector gate, but `traceWidth := EFFECT_VM_WIDTH_SYSROOTS` and
`hashSites := wideHashSites`. Strictly additive; the constraint list is byte-identical. -/
def cellSealVmDescriptorWide : EffectVmDescriptor :=
  { cellSealVmDescriptor with
    name := cellSealVmDescriptor.name ++ "-sysroots"
    traceWidth := EFFECT_VM_WIDTH_SYSROOTS
    hashSites := wideHashSites }

theorem cellSealWide_constraints_eq :
    cellSealVmDescriptorWide.constraints = cellSealVmDescriptor.constraints := rfl

/-- The row hypothesis: a cellSeal row (`s_cellSeal = 1`, `s_noop = 0`). -/
def IsCellSealRow (env : VmRowEnv) : Prop :=
  env.loc SEL_CELLSEAL = 1 ∧ env.loc sel.NOOP = 0

/-! ## §2 — the GATE-ONLY per-cell soundness (no hash-site hypothesis — the THIN per-effect content). -/

/-- **`cellSealGates_give_cellSpec`** — the per-row gates of the cellSeal descriptor, on a row decoded by
`RowEncodesSeal` with `s_noop = 0`, force `CellSealCellSpec`. Flag-free (all gates are `.gate`). -/
theorem cellSealGates_give_cellSpec (env : VmRowEnv) (pre post : CellState)
    (hnoop : env.loc sel.NOOP = 0) (hcanon : CellSealRowCanon env)
    (henc : RowEncodesSeal env pre post)
    (hgates : ∀ c ∈ cellSealVmDescriptor.constraints, c.holdsVm env true false) :
    CellSealCellSpec pre post := by
  have hrowgates : ∀ c ∈ cellSealRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ cellSealVmDescriptor.constraints := by
      unfold cellSealVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
    have hh := hgates c hmem
    unfold cellSealRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using hh
  exact intent_to_cellSpec env pre post hnoop henc ((cellSealVm_faithful env hcanon).mp hrowgates)

/-! ## §3 — the FULL declarative clause + the `RunnableFullStateSpec` instance. -/

/-- **`CellSealFullClause`** — the FULL 17-field declarative post for cellSeal: the per-cell
`CellSealCellSpec` (economic block FROZEN, the seq-nonce TICKS) AND the `system_roots` sub-block FROZEN
(`postRoots = preRoots` — cellSeal touches no side-table on-row). NON-VACUOUS. -/
def CellSealFullClause (preRoots : SysRoots) (pre post : CellState) (postRoots : SysRoots) : Prop :=
  CellSealCellSpec pre post ∧ postRoots = preRoots

/-- **`cellSealRunnableSpec` — the FULL-state RUNNABLE instance for cellSeal.** THIN; NON-VACUOUS. -/
def cellSealRunnableSpec (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor    := cellSealVmDescriptorWide
  usesWideSites := rfl
  isRow         := fun env => IsCellSealRow env ∧ CellSealRowCanon env
  decodeAfter   := fun env pre post postRoots =>
    RowEncodesSeal env pre post ∧ postRoots = preRoots
  fullClause    := CellSealFullClause preRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots⟩ := hdec
    exact ⟨cellSealGates_give_cellSpec env pre post hrow.1.2 hrow.2 henc
            (cellSealWide_constraints_eq ▸ hgates), hroots⟩

/-! ## §4 — THE DELIVERABLE: `cellSeal_runnable_full_sound`. -/

/-- **`cellSeal_runnable_full_sound` — the magnesium crown for cellSeal.** A row satisfying the WIDE
RUNNABLE cellSeal descriptor, decoded by `RowEncodesSeal` with the frozen-roots witness, pins the FULL
17-field post-state: the per-cell block (`CellSealCellSpec`) AND all 8 side-table roots FROZEN. -/
theorem cellSeal_runnable_full_sound (hash : List ℤ → ℤ) (preRoots : SysRoots)
    (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsCellSealRow env) (hcanon : CellSealRowCanon env)
    (henc : RowEncodesSeal env pre post) (hroots : postRoots = preRoots)
    (hsat : satisfiedVm hash cellSealVmDescriptorWide env true false) :
    CellSealCellSpec pre post ∧ postRoots = preRoots :=
  runnable_full_sound (cellSealRunnableSpec preRoots) hash env pre post postRoots
    ⟨hrow, hcanon⟩ ⟨henc, hroots⟩ hsat

/-! ## §5 — THE ANTI-GHOST: tamper ANY of the 17 fields ⇒ UNSAT (incl. any side-table root). -/

theorem cellSeal_runnable_full_commit_binds (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (preRoots : SysRoots) (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash cellSealVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash cellSealVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂) :
    baseAbsorbedCols e₁ = baseAbsorbedCols e₂ ∧ (∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i) :=
  runnable_full_commit_binds (cellSealRunnableSpec preRoots) hash hCR e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂

/-- **`cellSeal_rejects_root_tamper` — the side-table anti-ghost tooth.** Two wide cellSeal rows
publishing the same `NEW_COMMIT` (with `systemRootsDigest` carriers) but whose side-table sub-blocks
DIFFER at some root index cannot both satisfy. -/
theorem cellSeal_rejects_root_tamper (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (preRoots : SysRoots) (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash cellSealVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash cellSealVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) : False :=
  wide_rejects_root_tamper (cellSealRunnableSpec preRoots) hash hCR e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-! ## §6 — NON-VACUITY. -/

def cellSealPreRoots : SysRoots := emptySystemRoots

def cellSealPre : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

def cellSealPost : CellState :=
  { balLo := 100, balHi := 0, nonce := 6, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

/-- **NON-VACUITY (witness TRUE).** The cellSeal `fullClause` is inhabited by a real frozen-frame seal
(balance `100` frozen, nonce `5 → 6`, frame frozen, roots frozen). -/
theorem goodCellSeal_realizes :
    (cellSealRunnableSpec cellSealPreRoots).fullClause cellSealPre cellSealPost cellSealPreRoots :=
  ⟨⟨rfl, rfl, rfl, fun _ => rfl, rfl, rfl⟩, rfl⟩

/-- **NON-VACUITY (witness FALSE).** A forged post that MOVES the balance (`100 → 999`) FAILS the clause. -/
theorem cellSeal_clause_not_trivial :
    ¬ CellSealFullClause cellSealPreRoots cellSealPre { cellSealPost with balLo := 999 } cellSealPreRoots := by
  rintro ⟨⟨hbal, _, _, _, _, _⟩, _⟩
  simp only [cellSealPre] at hbal
  norm_num at hbal

/-- **NON-VACUITY (side-table dimension).** A post whose `system_roots` sub-block is NOT the frozen
reference (a populated sub-block) FAILS the clause — the frozen-roots leg is genuine. -/
theorem cellSeal_clause_rejects_root_drop :
    ¬ CellSealFullClause cellSealPreRoots cellSealPre cellSealPost
        (fun i => if i = (⟨0, by decide⟩ : Fin N_SYSTEM_ROOTS) then 1 else 0) := by
  rintro ⟨_, hroots⟩
  have h0 := congrFun hroots (⟨0, by decide⟩ : Fin N_SYSTEM_ROOTS)
  simp only [cellSealPreRoots, emptySystemRoots] at h0
  norm_num at h0

/-! ## §7 — layout + axiom-hygiene tripwires. -/

#guard cellSealVmDescriptorWide.traceWidth == 190
#guard cellSealVmDescriptorWide.hashSites.length == 4
#guard cellSealVmDescriptorWide.constraints.length == cellSealVmDescriptor.constraints.length

#assert_axioms cellSealGates_give_cellSpec
#assert_axioms cellSeal_runnable_full_sound
#assert_axioms cellSeal_runnable_full_commit_binds
#assert_axioms cellSeal_rejects_root_tamper
#assert_axioms goodCellSeal_realizes
#assert_axioms cellSeal_clause_not_trivial
#assert_axioms cellSeal_clause_rejects_root_drop

end Dregg2.Circuit.Emit.EffectVmEmitCellSealFullState
