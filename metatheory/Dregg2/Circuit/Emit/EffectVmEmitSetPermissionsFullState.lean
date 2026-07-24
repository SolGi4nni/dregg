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

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The anti-ghost theorems carry NO
collision-resistance hypothesis carried as a floor: they are SECURITY REDUCTIONS (fixed-hash
`_advantage_bound` forms with `hEff` in the OPEN + keyed-ROM `_rom` discharges from the proved
birthday floor), never a bare `binds ∨ collides` disjunction.
`fullClause` NON-VACUOUS. Read-only imports; owns only itself.
-/
import Dregg2.Circuit.Emit.EffectVmEmitSetPermissions
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable
import Dregg2.Circuit.Emit.EffectVmRowCommitReduction

namespace Dregg2.Circuit.Emit.EffectVmEmitSetPermissionsFullState

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gFieldPassAll)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitSetPermissions
  (SEL_SET_PERMS IsSetPermsRow SetPermsRowCanon setPermsRowGates setPermsVmDescriptor
   RowEncodesPerms PermCellSpec setPermsVm_faithful intent_to_permCellSpec)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (baseAbsorbedCols RunnableFullStateSpec runnable_full_sound runnable_full_commit_binds_or_collides
   wide_rejects_root_tamper_or_collides WideColl RootsColl wideHashSites)
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

/-! ## §2 — the GATE-ONLY per-cell soundness (no hash-site hypothesis).

Field-faithful: the base `setPermsVm_faithful` reads the ℤ row intent back off the mod-`p`
(`≡ 0 [ZMOD 2013265921]`) gates under the deployed range-check envelope `SetPermsRowCanon`; the
envelope is threaded here and through the spec's `isRow` — conclusions unchanged. -/

theorem setPermsGates_give_cellSpec (env : VmRowEnv) (pre post : CellState)
    (hnoop : env.loc sel.NOOP = 0) (hcanon : SetPermsRowCanon env)
    (henc : RowEncodesPerms env pre post)
    (hgates : ∀ c ∈ setPermsVmDescriptor.constraints, c.holdsVm env true false) :
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
  exact intent_to_permCellSpec env pre post hnoop henc
    ((setPermsVm_faithful env hcanon).mp hrowgates)

/-! ## §3 — the FULL declarative clause + the `RunnableFullStateSpec` instance. -/

def SetPermsFullClause (preRoots : SysRoots) (pre post : CellState) (postRoots : SysRoots) : Prop :=
  PermCellSpec pre post ∧ postRoots = preRoots

def setPermsRunnableSpec (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor    := setPermsVmDescriptorWide
  usesWideSites := rfl
  isRow         := fun env => IsSetPermsRow env ∧ SetPermsRowCanon env
  decodeAfter   := fun env pre post postRoots =>
    RowEncodesPerms env pre post ∧ postRoots = preRoots
  fullClause    := SetPermsFullClause preRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots⟩ := hdec
    exact ⟨setPermsGates_give_cellSpec env pre post hrow.1.2 hrow.2 henc
            (setPermsWide_constraints_eq ▸ hgates), hroots⟩

/-! ## §4 — THE DELIVERABLE: `setPermissions_runnable_full_sound`. -/

/-- **`setPermissions_runnable_full_sound` — the magnesium crown for setPermissions.** A row satisfying
the WIDE RUNNABLE descriptor, decoded by `RowEncodesPerms` with the frozen-roots witness, pins the FULL
17-field post-state: the per-cell block (`PermCellSpec`) AND all 8 side-table roots FROZEN. -/
theorem setPermissions_runnable_full_sound (hash : List ℤ → ℤ) (preRoots : SysRoots)
    (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsSetPermsRow env) (hcanon : SetPermsRowCanon env)
    (henc : RowEncodesPerms env pre post) (hroots : postRoots = preRoots)
    (hsat : satisfiedVm hash setPermsVmDescriptorWide env true false) :
    PermCellSpec pre post ∧ postRoots = preRoots :=
  runnable_full_sound (setPermsRunnableSpec preRoots) hash env pre post postRoots ⟨hrow, hcanon⟩
    ⟨henc, hroots⟩ hsat

/-! ## §5 — THE ANTI-GHOST. -/

/-! ⚑ ANTI-GHOST ON ALL 17 FIELDS, REBUILT AS SECURITY REDUCTIONS (the mint recipe,
`EffectVmEmitMintRunnable` §4). The bare `..._or_collides` forms that stood here are DELETED: at
deployed BabyBear parameters a sponge collision EXISTS by pigeonhole
(`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`), so `binds ∨ collides` is satisfiable through
its RIGHT branch without the binding ever holding — they quantified over SOLUTIONS, where hardness
quantifies over EFFICIENT ADVERSARIES. Their extraction spine
(`EffectVmFullStateRunnable.runnable_full_commit_binds_or_collides` /
`wide_rejects_root_tamper_or_collides`, `WideColl`, `RootsColl`) REMAINS as the reduction-internal
witness. The successors: the break/tamper is a first-class `Game` at setPermissions's OWN wide descriptor
(two rows BOTH ACCEPTED by the deployed wide circuit, one published `NEW_COMMIT`, genuine
`systemRootsDigest` carriers, different bound 17-field state), the extractor is the wide carrier
lift, and the conclusion is negligibility — the fixed-hash `_advantage_bound` forms with `hEff`
honestly in the OPEN (`IsPolyTime` is refuted; both poles of the floor are priced in
`EffectVmRowCommitReduction` §6), and the `_rom` forms DISCHARGED from `keyedRom_hard` (the birthday
bound) with NO floor hypothesis, in the labelled keyed-ROM idealization of
`EffectVmRowCommitReduction` §5's header. -/

open Dregg2.Circuit.Emit.EffectVmRowCommitReduction Dregg2.Crypto.SpongeCarrierReduction
  Dregg2.Crypto.FloorGames Dregg2.Crypto.ConcreteSecurity Dregg2.Crypto.RomCarrierSites in
/-- setPermissions's WIDE runnable descriptor as the reduction's per-effect datum: its hash sites ARE the
`system_roots`-absorbing wide sites (`rfl`). -/
def setPermissionsWideRowSpec : WideRowSpec where
  descriptor := setPermsVmDescriptorWide
  usesWideSites := rfl

open Dregg2.Circuit.Emit.EffectVmRowCommitReduction Dregg2.Crypto.SpongeCarrierReduction
  Dregg2.Crypto.FloorGames Dregg2.Crypto.ConcreteSecurity Dregg2.Crypto.RomCarrierSites in
/-- **⚑ THE REDUCED WHOLE-17-FIELD BINDING for setPermissions** — successor of the deleted
`..._or_collides` whole-state anti-ghost: under the DEPLOYED sponge's collision floor at the class
`Eff`, an adversary producing two rows BOTH SATISFYING the wide descriptor, publishing one
`NEW_COMMIT` with genuine `systemRootsDigest` carriers, yet binding DIFFERENT state (an absorbed
column or a side-table root), has NEGLIGIBLE advantage. -/
theorem setPermissions_runnable_full_binds_advantage_bound (D : SpongeKeyed)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (wideRowBreakGame D setPermissionsWideRowSpec))
    (hEff : Eff (carrierBreakToFinder D wideStateCarrier (wideRowToCarrier D setPermissionsWideRowSpec A)))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (wideRowBreakGame D setPermissionsWideRowSpec) A) :=
  wideRow_binds_advantage_bound D setPermissionsWideRowSpec Eff A hEff hCR

open Dregg2.Circuit.Emit.EffectVmRowCommitReduction Dregg2.Crypto.SpongeCarrierReduction
  Dregg2.Crypto.FloorGames Dregg2.Crypto.ConcreteSecurity Dregg2.Crypto.RomCarrierSites in
/-- **⚑⚑ THE WHOLE-17-FIELD BINDING, DISCHARGED ON THE PROVED KEYED-ROM FLOOR** — a query-bounded
forger of the wide nested `state_commit` (the very commitment setPermissions's wide row publishes) has
NEGLIGIBLE advantage, from `keyedRom_hard` (the birthday bound — a THEOREM). NO floor hypothesis.
The COMMITMENT layer carries no descriptor (the nested absorb schedule is one object across
effects); setPermissions's per-effect circuit content stays in the `_advantage_bound` form above,
`hEff` in the open. -/
theorem setPermissions_runnable_full_binds_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (wideRomBreakGame D tagDec))
    (hA : RomForgeryEff (wideRomFamily D tagDec) (effectVmWideRomForgery D tagDec) Q A) :
    Negl (gameAdv (wideRomBreakGame D tagDec) A) :=
  wideRow_binds_rom D tagDec Q hQ A hA

open Dregg2.Circuit.Emit.EffectVmRowCommitReduction Dregg2.Crypto.SpongeCarrierReduction
  Dregg2.Crypto.FloorGames Dregg2.Crypto.ConcreteSecurity Dregg2.Crypto.RomCarrierSites in
/-- **⚑ THE REDUCED SIDE-TABLE ANTI-GHOST for setPermissions** — successor of the deleted
`..._rejects_root_tamper_or_collides`: under the DEPLOYED sponge's collision floor at the class
`Eff`, an adversary that keeps the published `NEW_COMMIT` while tampering a side-table root of a
satisfying wide setPermissions row (a dropped escrow, an omitted nullifier, a reordered queue) has
NEGLIGIBLE advantage. -/
theorem setPermissions_rejects_root_tamper_advantage_bound (D : SpongeKeyed)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (wideRootTamperGame D setPermissionsWideRowSpec))
    (hEff : Eff (carrierBreakToFinder D wideStateCarrier
      (wideRowToCarrier D setPermissionsWideRowSpec (rootTamperToWide D setPermissionsWideRowSpec A))))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (wideRootTamperGame D setPermissionsWideRowSpec) A) :=
  wide_root_tamper_advantage_bound D setPermissionsWideRowSpec Eff A hEff hCR

open Dregg2.Circuit.Emit.EffectVmRowCommitReduction Dregg2.Crypto.SpongeCarrierReduction
  Dregg2.Crypto.FloorGames Dregg2.Crypto.ConcreteSecurity Dregg2.Crypto.RomCarrierSites in
/-- **⚑ THE SIDE-TABLE ANTI-GHOST, DISCHARGED ON THE PROVED KEYED-ROM FLOOR** — a query-bounded
adversary cannot keep the published nested wide commitment while tampering a side-table root, except
with negligible probability (`wide_root_tamper_rom`, from `keyedRom_hard`). NO floor hypothesis. -/
theorem setPermissions_rejects_root_tamper_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (effectVmWideRomRootTamper D tagDec).game)
    (hA : RomForgeryEff (wideRomFamily D tagDec) (effectVmWideRomRootTamper D tagDec) Q A) :
    Negl (gameAdv (effectVmWideRomRootTamper D tagDec).game A) :=
  wide_root_tamper_rom D tagDec Q hQ A hA

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

#guard setPermsVmDescriptorWide.traceWidth == 190
#guard setPermsVmDescriptorWide.hashSites.length == 4
#guard setPermsVmDescriptorWide.constraints.length == setPermsVmDescriptor.constraints.length

#assert_axioms setPermsGates_give_cellSpec
#assert_axioms setPermissions_runnable_full_sound
#assert_axioms setPermissions_runnable_full_binds_advantage_bound
#assert_axioms setPermissions_runnable_full_binds_rom
#assert_axioms setPermissions_rejects_root_tamper_advantage_bound
#assert_axioms setPermissions_rejects_root_tamper_rom
#assert_axioms goodSetPerms_realizes
#assert_axioms setPerms_clause_not_trivial
#assert_axioms setPerms_clause_rejects_root_drop

end Dregg2.Circuit.Emit.EffectVmEmitSetPermissionsFullState
