/-
# Dregg2.Circuit.Emit.EffectVmEmitRefusalFullState — refusal LIFTED to FULL-STATE on the RUNNABLE
descriptor (the magnesium breadth: the circuit the prover RUNS binds all 17 fields).

`EffectVmEmitRefusal` welds the per-cell block (`RefusalCellSpec`: economic block FROZEN, the seq-nonce
TICKS) on the 186-wide RUNNABLE descriptor; its `state_commit` absorbs only the 13 state-block columns,
NOT the 8 side-table roots. This module CLOSES that by amplifying refusal's RUNNABLE descriptor to the
WIDE (`system_roots`-absorbing) shape and lifting through the generic
`EffectVmFullStateRunnable.runnable_full_sound` crown: a satisfying WIDE-descriptor witness pins the FULL
17-field declarative post-state — the per-cell block AND every one of the 8 side-table roots FROZEN.

refusal is evidence-of-absence (state passthrough + nonce-tick; the receipt + reason are off-row). So its
`system_roots` sub-block is FROZEN; the magnesium win is the WIDE commitment now BINDS all 8 roots. The
§RECIPE applied to refusal.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The anti-ghost theorems carry NO
collision-resistance hypothesis: they conclude a disjunction naming the sponge collision they
would otherwise assume away.
`fullClause` NON-VACUOUS. Read-only imports; owns only itself.
-/
import Dregg2.Circuit.Emit.EffectVmEmitRefusal
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable

namespace Dregg2.Circuit.Emit.EffectVmEmitRefusalFullState

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gFieldPassAll)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitRefusal
  (SEL_REFUSAL refusalRowGates refusalVmDescriptor RowEncodesRefusal RefusalCellSpec
   refusalVm_faithful intent_to_cellSpec)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (baseAbsorbedCols RunnableFullStateSpec runnable_full_sound runnable_full_commit_binds_or_collides
   wide_rejects_root_tamper_or_collides WideColl RootsColl wideHashSites)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest emptySystemRoots N_SYSTEM_ROOTS)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §1 — the WIDE refusal descriptor (width + sites; constraints UNCHANGED). -/

def refusalVmDescriptorWide : EffectVmDescriptor :=
  { refusalVmDescriptor with
    name := refusalVmDescriptor.name ++ "-sysroots"
    traceWidth := EFFECT_VM_WIDTH_SYSROOTS
    hashSites := wideHashSites }

theorem refusalWide_constraints_eq :
    refusalVmDescriptorWide.constraints = refusalVmDescriptor.constraints := rfl

/-- The row hypothesis: a refusal row (`s_refusal = 1`, `s_noop = 0`). -/
def IsRefusalRow (env : VmRowEnv) : Prop :=
  env.loc SEL_REFUSAL = 1 ∧ env.loc sel.NOOP = 0

/-! ## §2 — the GATE-ONLY per-cell soundness (no hash-site hypothesis). -/

theorem refusalGates_give_cellSpec (env : VmRowEnv) (pre post : CellState)
    (hnoop : env.loc sel.NOOP = 0) (henc : RowEncodesRefusal env pre post)
    (hgates : ∀ c ∈ refusalVmDescriptor.constraints, c.holdsVm env true false) :
    RefusalCellSpec pre post := by
  have hrowgates : ∀ c ∈ refusalRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ refusalVmDescriptor.constraints := by
      unfold refusalVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
    have hh := hgates c hmem
    unfold refusalRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using hh
  exact intent_to_cellSpec env pre post hnoop henc ((refusalVm_faithful env).mp hrowgates)

/-! ## §3 — the FULL declarative clause + the `RunnableFullStateSpec` instance. -/

def RefusalFullClause (preRoots : SysRoots) (pre post : CellState) (postRoots : SysRoots) : Prop :=
  RefusalCellSpec pre post ∧ postRoots = preRoots

def refusalRunnableSpec (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor    := refusalVmDescriptorWide
  usesWideSites := rfl
  isRow         := IsRefusalRow
  decodeAfter   := fun env pre post postRoots =>
    RowEncodesRefusal env pre post ∧ postRoots = preRoots
  fullClause    := RefusalFullClause preRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots⟩ := hdec
    exact ⟨refusalGates_give_cellSpec env pre post hrow.2 henc
            (refusalWide_constraints_eq ▸ hgates), hroots⟩

/-! ## §4 — THE DELIVERABLE: `refusal_runnable_full_sound`. -/

/-- **`refusal_runnable_full_sound` — the magnesium crown for refusal.** A row satisfying the WIDE
RUNNABLE refusal descriptor, decoded by `RowEncodesRefusal` with the frozen-roots witness, pins the FULL
17-field post-state: the per-cell block (`RefusalCellSpec`) AND all 8 side-table roots FROZEN. -/
theorem refusal_runnable_full_sound (hash : List ℤ → ℤ) (preRoots : SysRoots)
    (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsRefusalRow env)
    (henc : RowEncodesRefusal env pre post) (hroots : postRoots = preRoots)
    (hgatesat : satisfiedVm hash refusalVmDescriptorWide env true false) :
    RefusalCellSpec pre post ∧ postRoots = preRoots :=
  runnable_full_sound (refusalRunnableSpec preRoots) hash env pre post postRoots hrow
    ⟨henc, hroots⟩ hgatesat

/-! ## §5 — THE ANTI-GHOST. -/

/-! ### ⚑ THE WHOLE-STATE ANTI-GHOST IS A SECURITY REDUCTION, AND IT LIVES DOWNSTREAM (07-22).

`refusal_runnable_full_commit_binds_or_collides` and `refusal_rejects_root_tamper_or_collides` USED TO BE EXPORTED HERE as BARE DISJUNCTIONS —
`(cols agree ∧ roots agree) ∨ WideColl … ∨ RootsColl …`. True at deployed BabyBear parameters, unlike
their `Poseidon2SpongeCR`-carrying predecessors (which the deployed compressing sponge REFUTES), but
still UNCLOSED: a collision of that sponge EXISTS at deployed parameters by pigeonhole, so the right
branches are unconditionally available and `binds ∨ collides` never has to bind. A disjunction
quantifies over SOLUTIONS; cryptographic hardness quantifies over EFFICIENT ADVERSARIES.

**BOTH ARE DELETED.** The deployed binding of refusal's wide commitment is now the REDUCTION
`Dregg2.Circuit.Emit.EffectVmCommitReduction.refusal_wide_binds_full_state_advantage_bound`
(with `hEff` discharged at `Eff := IsPolyTime` by `refusal_wide_binds_full_state_from_polyTime`): the
forgery is a `Game` whose answers are DEPLOYED WIDE refusal ROWS
(`refusal_wide_forgery_is_break` / `refusal_root_tamper_is_break`), the extractor is a MAP OF ADVERSARIES
into the deployed sponge's collision game, and the conclusion is a NEGLIGIBLE ADVANTAGE under
`DomainSeparatedCREff`, whose two poles are both proved.

⚑ It lives in a DOWNSTREAM module, not here, for a hard reason: the deployed sponge's keyed family
(`Poseidon2KeyedBridge`) transitively imports the effect-emission tree, so a reduction stated at that
family CANNOT be imported by an emission module without a build cycle. The GAME still names THIS
file's `refusalVmDescriptorWide` — nothing is stated about an idealised stand-in. -/

/-! ## §6 — NON-VACUITY. -/

def refusalPreRoots : SysRoots := emptySystemRoots

def refusalPre : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

def refusalPost : CellState :=
  { balLo := 100, balHi := 0, nonce := 6, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

theorem goodRefusal_realizes :
    (refusalRunnableSpec refusalPreRoots).fullClause refusalPre refusalPost refusalPreRoots :=
  ⟨⟨rfl, rfl, rfl, fun _ => rfl, rfl, rfl⟩, rfl⟩

theorem refusal_clause_not_trivial :
    ¬ RefusalFullClause refusalPreRoots refusalPre { refusalPost with balLo := 999 } refusalPreRoots := by
  rintro ⟨⟨hbal, _, _, _, _, _⟩, _⟩
  simp only [refusalPre] at hbal
  norm_num at hbal

theorem refusal_clause_rejects_root_drop :
    ¬ RefusalFullClause refusalPreRoots refusalPre refusalPost
        (fun i => if i = (⟨0, by decide⟩ : Fin N_SYSTEM_ROOTS) then 1 else 0) := by
  rintro ⟨_, hroots⟩
  have h0 := congrFun hroots (⟨0, by decide⟩ : Fin N_SYSTEM_ROOTS)
  simp only [refusalPreRoots, emptySystemRoots] at h0
  norm_num at h0

/-! ## §7 — layout + axiom-hygiene tripwires. -/

#guard refusalVmDescriptorWide.traceWidth == 190
#guard refusalVmDescriptorWide.hashSites.length == 4
#guard refusalVmDescriptorWide.constraints.length == refusalVmDescriptor.constraints.length

#assert_axioms refusalGates_give_cellSpec
#assert_axioms refusal_runnable_full_sound
#assert_axioms goodRefusal_realizes
#assert_axioms refusal_clause_not_trivial
#assert_axioms refusal_clause_rejects_root_drop

end Dregg2.Circuit.Emit.EffectVmEmitRefusalFullState
