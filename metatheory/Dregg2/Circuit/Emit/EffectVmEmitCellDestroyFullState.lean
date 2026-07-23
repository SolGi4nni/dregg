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

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NO collision-resistance hypothesis enters:
the anti-ghost theorems are the UNCONDITIONAL `_or_collides` forms, whose alternative branch hands back
a specific colliding pair. The former `Poseidon2SpongeCR`-carrying forms were vacuous at deployed
BabyBear parameters — the deployed compressing sponge REFUTES that hypothesis.
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
  (baseAbsorbedCols RunnableFullStateSpec runnable_full_sound WideColl RootsColl
   runnable_full_commit_binds_or_collides wide_rejects_root_tamper_or_collides
   wideHashSites)
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

/-! ### ⚑ THE WHOLE-STATE ANTI-GHOST IS A SECURITY REDUCTION, AND IT LIVES DOWNSTREAM (07-22).

`cellDestroy_runnable_full_commit_binds_or_collides` and `cellDestroy_rejects_root_tamper_or_collides` USED TO BE EXPORTED HERE as BARE DISJUNCTIONS —
`(cols agree ∧ roots agree) ∨ WideColl … ∨ RootsColl …`. True at deployed BabyBear parameters, unlike
their `Poseidon2SpongeCR`-carrying predecessors (which the deployed compressing sponge REFUTES), but
still UNCLOSED: a collision of that sponge EXISTS at deployed parameters by pigeonhole, so the right
branches are unconditionally available and `binds ∨ collides` never has to bind. A disjunction
quantifies over SOLUTIONS; cryptographic hardness quantifies over EFFICIENT ADVERSARIES.

**BOTH ARE DELETED.** The deployed binding of cellDestroy's wide commitment is now the REDUCTION
`Dregg2.Circuit.Emit.EffectVmCommitReduction.cellDestroy_wide_binds_full_state_advantage_bound`
(with `hEff` discharged at `Eff := IsPolyTime` by `cellDestroy_wide_binds_full_state_from_polyTime`): the
forgery is a `Game` whose answers are DEPLOYED WIDE cellDestroy ROWS
(`cellDestroy_wide_forgery_is_break` / `cellDestroy_root_tamper_is_break`), the extractor is a MAP OF ADVERSARIES
into the deployed sponge's collision game, and the conclusion is a NEGLIGIBLE ADVANTAGE under
`DomainSeparatedCREff`, whose two poles are both proved.

⚑ It lives in a DOWNSTREAM module, not here, for a hard reason: the deployed sponge's keyed family
(`Poseidon2KeyedBridge`) transitively imports the effect-emission tree, so a reduction stated at that
family CANNOT be imported by an emission module without a build cycle. The GAME still names THIS
file's `cellDestroyVmDescriptorWide` — nothing is stated about an idealised stand-in. -/

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
#assert_axioms goodCellDestroy_realizes
#assert_axioms cellDestroy_clause_not_trivial
#assert_axioms cellDestroy_clause_rejects_root_drop

end Dregg2.Circuit.Emit.EffectVmEmitCellDestroyFullState
