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

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The anti-ghost theorems are SECURITY
REDUCTIONS (the mint recipe): fixed-hash `_advantage_bound` forms with `hEff` in the OPEN plus
keyed-ROM `_rom` discharges from the PROVED birthday floor — never a bare `binds ∨ collides`
disjunction (satisfiable through its collision branch by pigeonhole at deployed parameters).
`fullClause` NON-VACUOUS. Read-only imports; owns only itself.
-/
import Dregg2.Circuit.Emit.EffectVmEmitRefusal
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable
import Dregg2.Circuit.Emit.EffectVmRowCommitReduction

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

/-! ⚑ ANTI-GHOST ON ALL 17 FIELDS, REBUILT AS SECURITY REDUCTIONS (the mint recipe,
`EffectVmEmitMintRunnable` §4). The bare `..._or_collides` forms that stood here are DELETED: at
deployed BabyBear parameters a sponge collision EXISTS by pigeonhole
(`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`), so `binds ∨ collides` is satisfiable through
its RIGHT branch without the binding ever holding — they quantified over SOLUTIONS, where hardness
quantifies over EFFICIENT ADVERSARIES. Their extraction spine
(`EffectVmFullStateRunnable.runnable_full_commit_binds_or_collides` /
`wide_rejects_root_tamper_or_collides`, `WideColl`, `RootsColl`) REMAINS as the reduction-internal
witness. The successors: the break/tamper is a first-class `Game` at refusal's OWN wide descriptor
(two rows BOTH ACCEPTED by the deployed wide circuit, one published `NEW_COMMIT`, genuine
`systemRootsDigest` carriers, different bound 17-field state), the extractor is the wide carrier
lift, and the conclusion is negligibility — the fixed-hash `_advantage_bound` forms with `hEff`
honestly in the OPEN (`IsPolyTime` is refuted; both poles of the floor are priced in
`EffectVmRowCommitReduction` §6), and the `_rom` forms DISCHARGED from `keyedRom_hard` (the birthday
bound) with NO floor hypothesis, in the labelled keyed-ROM idealization of
`EffectVmRowCommitReduction` §5's header. -/

open Dregg2.Circuit.Emit.EffectVmRowCommitReduction Dregg2.Crypto.SpongeCarrierReduction
  Dregg2.Crypto.FloorGames Dregg2.Crypto.ConcreteSecurity Dregg2.Crypto.RomCarrierSites in
/-- refusal's WIDE runnable descriptor as the reduction's per-effect datum: its hash sites ARE the
`system_roots`-absorbing wide sites (`rfl`). -/
def refusalWideRowSpec : WideRowSpec where
  descriptor := refusalVmDescriptorWide
  usesWideSites := rfl

open Dregg2.Circuit.Emit.EffectVmRowCommitReduction Dregg2.Crypto.SpongeCarrierReduction
  Dregg2.Crypto.FloorGames Dregg2.Crypto.ConcreteSecurity Dregg2.Crypto.RomCarrierSites in
/-- **⚑ THE REDUCED WHOLE-17-FIELD BINDING for refusal** — successor of the deleted
`..._or_collides` whole-state anti-ghost: under the DEPLOYED sponge's collision floor at the class
`Eff`, an adversary producing two rows BOTH SATISFYING the wide descriptor, publishing one
`NEW_COMMIT` with genuine `systemRootsDigest` carriers, yet binding DIFFERENT state (an absorbed
column or a side-table root), has NEGLIGIBLE advantage. -/
theorem refusal_runnable_full_binds_advantage_bound (D : SpongeKeyed)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (wideRowBreakGame D refusalWideRowSpec))
    (hEff : Eff (carrierBreakToFinder D wideStateCarrier (wideRowToCarrier D refusalWideRowSpec A)))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (wideRowBreakGame D refusalWideRowSpec) A) :=
  wideRow_binds_advantage_bound D refusalWideRowSpec Eff A hEff hCR

open Dregg2.Circuit.Emit.EffectVmRowCommitReduction Dregg2.Crypto.SpongeCarrierReduction
  Dregg2.Crypto.FloorGames Dregg2.Crypto.ConcreteSecurity Dregg2.Crypto.RomCarrierSites in
/-- **⚑⚑ THE WHOLE-17-FIELD BINDING, DISCHARGED ON THE PROVED KEYED-ROM FLOOR** — a query-bounded
forger of the wide nested `state_commit` (the very commitment refusal's wide row publishes) has
NEGLIGIBLE advantage, from `keyedRom_hard` (the birthday bound — a THEOREM). NO floor hypothesis.
The COMMITMENT layer carries no descriptor (the nested absorb schedule is one object across
effects); refusal's per-effect circuit content stays in the `_advantage_bound` form above,
`hEff` in the open. -/
theorem refusal_runnable_full_binds_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (wideRomBreakGame D tagDec))
    (hA : RomForgeryEff (wideRomFamily D tagDec) (effectVmWideRomForgery D tagDec) Q A) :
    Negl (gameAdv (wideRomBreakGame D tagDec) A) :=
  wideRow_binds_rom D tagDec Q hQ A hA

open Dregg2.Circuit.Emit.EffectVmRowCommitReduction Dregg2.Crypto.SpongeCarrierReduction
  Dregg2.Crypto.FloorGames Dregg2.Crypto.ConcreteSecurity Dregg2.Crypto.RomCarrierSites in
/-- **⚑ THE REDUCED SIDE-TABLE ANTI-GHOST for refusal** — successor of the deleted
`..._rejects_root_tamper_or_collides`: under the DEPLOYED sponge's collision floor at the class
`Eff`, an adversary that keeps the published `NEW_COMMIT` while tampering a side-table root of a
satisfying wide refusal row (a dropped escrow, an omitted nullifier, a reordered queue) has
NEGLIGIBLE advantage. -/
theorem refusal_rejects_root_tamper_advantage_bound (D : SpongeKeyed)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (wideRootTamperGame D refusalWideRowSpec))
    (hEff : Eff (carrierBreakToFinder D wideStateCarrier
      (wideRowToCarrier D refusalWideRowSpec (rootTamperToWide D refusalWideRowSpec A))))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (wideRootTamperGame D refusalWideRowSpec) A) :=
  wide_root_tamper_advantage_bound D refusalWideRowSpec Eff A hEff hCR

open Dregg2.Circuit.Emit.EffectVmRowCommitReduction Dregg2.Crypto.SpongeCarrierReduction
  Dregg2.Crypto.FloorGames Dregg2.Crypto.ConcreteSecurity Dregg2.Crypto.RomCarrierSites in
/-- **⚑ THE SIDE-TABLE ANTI-GHOST, DISCHARGED ON THE PROVED KEYED-ROM FLOOR** — a query-bounded
adversary cannot keep the published nested wide commitment while tampering a side-table root, except
with negligible probability (`wide_root_tamper_rom`, from `keyedRom_hard`). NO floor hypothesis. -/
theorem refusal_rejects_root_tamper_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (effectVmWideRomRootTamper D tagDec).game)
    (hA : RomForgeryEff (wideRomFamily D tagDec) (effectVmWideRomRootTamper D tagDec) Q A) :
    Negl (gameAdv (effectVmWideRomRootTamper D tagDec).game A) :=
  wide_root_tamper_rom D tagDec Q hQ A hA

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
#assert_axioms refusal_runnable_full_binds_advantage_bound
#assert_axioms refusal_runnable_full_binds_rom
#assert_axioms refusal_rejects_root_tamper_advantage_bound
#assert_axioms refusal_rejects_root_tamper_rom
#assert_axioms goodRefusal_realizes
#assert_axioms refusal_clause_not_trivial
#assert_axioms refusal_clause_rejects_root_drop

end Dregg2.Circuit.Emit.EffectVmEmitRefusalFullState
