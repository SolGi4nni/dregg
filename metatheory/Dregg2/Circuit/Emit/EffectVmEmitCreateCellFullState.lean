/-
# Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState — createCell LIFTED to FULL-STATE on the RUNNABLE
descriptor (the magnesium breadth: the circuit the prover RUNS binds all 17 fields).

`EffectVmEmitCreateCell`'s RUNNABLE row is BORN-EMPTY: `createCellRowGates` force `state_after[off] = 0`
for every economic-data column (the new cell's block is the all-zero economic block), and the 4 GROUP-4
sites bind that zero block into `state_commit`. But that commitment absorbs only the 13 state-block
columns, NOT the 8 side-table roots. This module CLOSES that by amplifying the RUNNABLE descriptor to the
WIDE (`system_roots`-absorbing) shape and lifting through the generic
`EffectVmFullStateRunnable.runnable_full_sound` crown: a satisfying WIDE-descriptor witness pins the FULL
17-field declarative post-state — the per-cell BORN-EMPTY block (`ZeroBlockSpec`: every economic column
zero) AND every one of the 8 side-table roots FROZEN (createCell's RUNNABLE row touches no side-table).
The anti-ghost tooth bites on all 17 (incl. any root).

NOTE: the cross-cell `accounts` GROW (the new cell joins the live set) is the TURN-COMPOSITION layer fact
(the "PER-CELL, not cross-cell" boundary), NOT this single-row descriptor; the structural-alloc primitive
obstruction is proven in `Argus/Effects/CreateCell`. The §RECIPE applied to createCell.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NO collision-resistance hypothesis enters:
the anti-ghost theorems are the UNCONDITIONAL `_or_collides` forms, whose alternative branch hands back
a specific colliding pair. The former `Poseidon2SpongeCR`-carrying forms were vacuous at deployed
BabyBear parameters — the deployed compressing sponge REFUTES that hypothesis.
`fullClause` NON-VACUOUS. Read-only imports; owns only itself.
-/
import Dregg2.Circuit.Emit.EffectVmEmitCreateCell
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable
import Dregg2.Circuit.Emit.EffectVmRowCommitReduction

namespace Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitCreateCell
  (SEL_CREATECELL createCellRowGates createCellVmDescriptor BornEmptyRowIntent createCellVm_faithful)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (baseAbsorbedCols RunnableFullStateSpec runnable_full_sound WideColl RootsColl
   runnable_full_commit_binds_or_collides wide_rejects_root_tamper_or_collides
   wideHashSites)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest emptySystemRoots N_SYSTEM_ROOTS)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §1 — the WIDE createCell descriptor (width + sites; constraints UNCHANGED). -/

def createCellVmDescriptorWide : EffectVmDescriptor :=
  { createCellVmDescriptor with
    name := createCellVmDescriptor.name ++ "-sysroots"
    traceWidth := EFFECT_VM_WIDTH_SYSROOTS
    hashSites := wideHashSites }

theorem createCellWide_constraints_eq :
    createCellVmDescriptorWide.constraints = createCellVmDescriptor.constraints := rfl

/-- The row hypothesis: a createCell row (`s_createCell = 1`). -/
def IsCreateCellRow (env : VmRowEnv) : Prop :=
  env.loc SEL_CREATECELL = 1

/-! ## §2 — the structured post decode + the BORN-EMPTY spec. -/

/-- `RowEncodesCreate env post` ties the row's `state_after` block to a concrete post-`CellState`. -/
def RowEncodesCreate (env : VmRowEnv) (post : CellState) : Prop :=
  env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved

/-- **`ZeroBlockSpec post`** — the per-cell FULL-state born-empty spec: every economic-data column of
`post` is ZERO as a field value (mod-`p` congruent to `0`; canonical `[0, p)` cells make this exact). -/
def ZeroBlockSpec (post : CellState) : Prop :=
  post.balLo ≡ 0 [ZMOD 2013265921]
  ∧ post.balHi ≡ 0 [ZMOD 2013265921]
  ∧ post.nonce ≡ 0 [ZMOD 2013265921]
  ∧ (∀ i : Fin 8, post.fields i ≡ 0 [ZMOD 2013265921])
  ∧ post.capRoot ≡ 0 [ZMOD 2013265921]
  ∧ post.reserved ≡ 0 [ZMOD 2013265921]

theorem intent_to_zeroSpec (env : VmRowEnv) (post : CellState)
    (henc : RowEncodesCreate env post) (hint : BornEmptyRowIntent env) :
    ZeroBlockSpec post := by
  obtain ⟨hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsaLo]; exact hbal
  · rw [← hsaHi]; exact hbhi
  · rw [← hsaN]; exact hnon
  · intro i
    have := hfld i.val i.isLt
    rw [← hsaF i]; exact this
  · rw [← hsaCap]; exact hcap
  · rw [← hsaRes]; exact hres

/-! ## §3 — the GATE-ONLY soundness (no hash-site hypothesis). -/

theorem createCellGates_give_zeroSpec (env : VmRowEnv) (post : CellState)
    (henc : RowEncodesCreate env post)
    (hgates : ∀ c ∈ createCellVmDescriptor.constraints, c.holdsVm env true false) :
    ZeroBlockSpec post := by
  have hrowgates : ∀ c ∈ createCellRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ createCellVmDescriptor.constraints := by
      unfold createCellVmDescriptor; exact hc
    have hh := hgates c hmem
    unfold createCellRowGates Dregg2.Circuit.Emit.EffectVmEmitCreateCell.gZero at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using hh
  exact intent_to_zeroSpec env post henc ((createCellVm_faithful env).mp hrowgates)

/-! ## §4 — the FULL declarative clause + the `RunnableFullStateSpec` instance. -/

/-- **`CreateCellFullClause`** — the FULL 17-field declarative post for createCell: the per-cell
BORN-EMPTY block (`ZeroBlockSpec`) AND the `system_roots` sub-block FROZEN. NON-VACUOUS. -/
def CreateCellFullClause (preRoots : SysRoots) (pre post : CellState) (postRoots : SysRoots) : Prop :=
  ZeroBlockSpec post ∧ postRoots = preRoots

def createCellRunnableSpec (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor    := createCellVmDescriptorWide
  usesWideSites := rfl
  isRow         := IsCreateCellRow
  decodeAfter   := fun env _pre post postRoots =>
    RowEncodesCreate env post ∧ postRoots = preRoots
  fullClause    := CreateCellFullClause preRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots⟩ := hdec
    exact ⟨createCellGates_give_zeroSpec env post henc
            (createCellWide_constraints_eq ▸ hgates), hroots⟩

/-! ## §5 — THE DELIVERABLE: `createCell_runnable_full_sound`. -/

/-- **`createCell_runnable_full_sound` — the magnesium crown for createCell.** A row satisfying the WIDE
RUNNABLE descriptor, decoded by `RowEncodesCreate` with the frozen-roots witness, pins the FULL 17-field
post-state: the per-cell BORN-EMPTY block (`ZeroBlockSpec`) AND all 8 side-table roots FROZEN. -/
theorem createCell_runnable_full_sound (hash : List ℤ → ℤ) (preRoots : SysRoots)
    (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsCreateCellRow env)
    (henc : RowEncodesCreate env post) (hroots : postRoots = preRoots)
    (hsat : satisfiedVm hash createCellVmDescriptorWide env true false) :
    ZeroBlockSpec post ∧ postRoots = preRoots :=
  runnable_full_sound (createCellRunnableSpec preRoots) hash env pre post postRoots hrow
    ⟨henc, hroots⟩ hsat

/-! ## §6 — THE ANTI-GHOST. -/

/-- ⚑ **WHAT CHANGED AND WHY (the reduction that replaces the deleted disjunctions).** This section
used to export `createCell_runnable_full_commit_binds_or_collides` / `createCell_rejects_root_tamper_or_collides`, each concluding
`… ∨ WideColl hash e₁ e₂ ∨ RootsColl hash sr₁ sr₂`. Those forms are TRUE of the deployed sponge —
unlike the `Poseidon2SpongeCR` predecessors, which it REFUTES — but they are UNCLOSED: a collision
of the deployed sponge EXISTS at BabyBear parameters by pigeonhole
(`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`), so `binds ∨ collides` is satisfiable through
its RIGHT branch WITHOUT the binding ever holding. They quantify over SOLUTIONS; cryptographic
hardness quantifies over EFFICIENT ADVERSARIES. They are DELETED and rebuilt on
`Emit.EffectVmRowCommitReduction`, exactly as `EffectVmEmitMintRunnable` §4: the forgery is a
first-class `Game` at createCell's OWN wide descriptor, the extractor is a MAP OF ADVERSARIES (the
reduction-internal witness), and the conclusions are (a) negligibility under the DEPLOYED sponge's
collision floor `HashCRHardQuant (spongeFamily D) Eff`, `hEff` in the open, both poles priced
(`rowCommitFloor_top_false_babyBear` / `_bot_vacuous`), and (b) the DISCHARGED keyed-ROM forms on
the PROVED birthday floor (`keyedRom_hard`) — NO floor hypothesis — in the LABELLED random-oracle
model of `EffectVmRowCommitReduction` §5's header (the sampled `Fin (2 ^ l)` digest is the
modelling step; no `l` is the deployed ~31-bit felt). The ROM commitment layer carries no
descriptor (the nested absorb schedule is one object across effects); createCell's per-effect circuit
content (`satisfiedVm` at `createCellVmDescriptorWide`) lives in the `_advantage_bound` forms. -/
def createCellWideRowSpec : Dregg2.Circuit.Emit.EffectVmRowCommitReduction.WideRowSpec where
  descriptor := createCellVmDescriptorWide
  usesWideSites := rfl

open Dregg2.Crypto.SpongeCarrierReduction (SpongeKeyed spongeFamily carrierBreakToFinder) in
open Dregg2.Circuit.Emit.EffectVmRowCommitReduction in
open Dregg2.Crypto.FloorGames (Adversary gameAdv hashGame HashCRHardQuant) in
open Dregg2.Crypto.ConcreteSecurity (Negl) in
/-- **⚑ `createCell_binds_full_state_advantage_bound` — THE REDUCED WHOLE-17-FIELD BINDING for
createCell.** Under the DEPLOYED sponge's collision floor at the class `Eff`, an adversary producing
two rows BOTH SATISFYING `createCellVmDescriptorWide`, publishing one `NEW_COMMIT` with genuine `systemRootsDigest`
carriers, yet binding DIFFERENT state (an absorbed column or a side-table root), has NEGLIGIBLE
advantage. Replaces the deleted bare disjunction. -/
theorem createCell_binds_full_state_advantage_bound (D : SpongeKeyed)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (wideRowBreakGame D createCellWideRowSpec))
    (hEff : Eff (carrierBreakToFinder D wideStateCarrier
      (wideRowToCarrier D createCellWideRowSpec A)))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (wideRowBreakGame D createCellWideRowSpec) A) :=
  wideRow_binds_advantage_bound D createCellWideRowSpec Eff A hEff hCR

open Dregg2.Crypto.SpongeCarrierReduction (SpongeKeyed) in
open Dregg2.Circuit.Emit.EffectVmRowCommitReduction in
open Dregg2.Crypto.RomCarrierSites (RomForgeryEff) in
open Dregg2.Crypto.FloorGames (Adversary gameAdv) in
open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded) in
/-- **⚑⚑ `createCell_binds_full_state_rom` — the DISCHARGED whole-17-field binding, on the PROVED
floor.** A query-bounded forger of the wide nested `state_commit` — the very commitment createCell's
wide row publishes — has NEGLIGIBLE advantage, in the keyed ROM model of
`EffectVmRowCommitReduction` §5's header. NO floor hypothesis. The COMMITMENT layer carries no
descriptor, so this is `wideRow_binds_rom` at the deployed tag space; createCell's per-effect circuit
content stays in the `_advantage_bound` form above, `hEff` in the open. -/
theorem createCell_binds_full_state_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (wideRomBreakGame D tagDec))
    (hA : RomForgeryEff (wideRomFamily D tagDec) (effectVmWideRomForgery D tagDec) Q A) :
    Negl (gameAdv (wideRomBreakGame D tagDec) A) :=
  wideRow_binds_rom D tagDec Q hQ A hA

open Dregg2.Crypto.SpongeCarrierReduction (SpongeKeyed spongeFamily carrierBreakToFinder) in
open Dregg2.Circuit.Emit.EffectVmRowCommitReduction in
open Dregg2.Crypto.FloorGames (Adversary gameAdv hashGame HashCRHardQuant) in
open Dregg2.Crypto.ConcreteSecurity (Negl) in
/-- **⚑ `createCell_rejects_root_tamper_advantage_bound` — the side-table anti-ghost, REDUCED.** An
efficient adversary cannot keep the published `NEW_COMMIT` while tampering a side-table root of a
satisfying wide createCell row (a dropped escrow, an omitted nullifier, a reordered queue), except
with negligible probability. Replaces the deleted `createCell_rejects_root_tamper_or_collides`. -/
theorem createCell_rejects_root_tamper_advantage_bound (D : SpongeKeyed)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (wideRootTamperGame D createCellWideRowSpec))
    (hEff : Eff (carrierBreakToFinder D wideStateCarrier
      (wideRowToCarrier D createCellWideRowSpec (rootTamperToWide D createCellWideRowSpec A))))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (wideRootTamperGame D createCellWideRowSpec) A) :=
  wide_root_tamper_advantage_bound D createCellWideRowSpec Eff A hEff hCR

open Dregg2.Crypto.SpongeCarrierReduction (SpongeKeyed) in
open Dregg2.Circuit.Emit.EffectVmRowCommitReduction in
open Dregg2.Crypto.RomCarrierSites (RomForgeryEff) in
open Dregg2.Crypto.FloorGames (Adversary gameAdv) in
open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded) in
/-- **⚑ `createCell_rejects_root_tamper_rom`** — the same tooth DISCHARGED on the PROVED floor: a
query-bounded adversary cannot keep the published nested commitment while tampering a side-table
root. -/
theorem createCell_rejects_root_tamper_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (effectVmWideRomRootTamper D tagDec).game)
    (hA : RomForgeryEff (wideRomFamily D tagDec) (effectVmWideRomRootTamper D tagDec) Q A) :
    Negl (gameAdv (effectVmWideRomRootTamper D tagDec).game A) :=
  wide_root_tamper_rom D tagDec Q hQ A hA

/-! ## §7 — NON-VACUITY. -/

def createCellPreRoots : SysRoots := emptySystemRoots

def createCellPre : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

def createCellPost : CellState :=
  { balLo := 0, balHi := 0, nonce := 0, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

theorem goodCreateCell_realizes :
    (createCellRunnableSpec createCellPreRoots).fullClause createCellPre createCellPost createCellPreRoots :=
  ⟨⟨rfl, rfl, rfl, fun _ => rfl, rfl, rfl⟩, rfl⟩

theorem createCell_clause_not_trivial :
    ¬ CreateCellFullClause createCellPreRoots createCellPre
        { createCellPost with balLo := 999 } createCellPreRoots := by
  rintro ⟨⟨hbal, _, _, _, _, _⟩, _⟩
  simp only [createCellPost] at hbal
  unfold Int.ModEq at hbal
  omega

theorem createCell_clause_rejects_root_drop :
    ¬ CreateCellFullClause createCellPreRoots createCellPre createCellPost
        (fun i => if i = (⟨0, by decide⟩ : Fin N_SYSTEM_ROOTS) then 1 else 0) := by
  rintro ⟨_, hroots⟩
  have h0 := congrFun hroots (⟨0, by decide⟩ : Fin N_SYSTEM_ROOTS)
  simp only [createCellPreRoots, emptySystemRoots] at h0
  norm_num at h0

/-! ## §8 — layout + axiom-hygiene tripwires. -/

#guard createCellVmDescriptorWide.traceWidth == 190
#guard createCellVmDescriptorWide.hashSites.length == 4
#guard createCellVmDescriptorWide.constraints.length == createCellVmDescriptor.constraints.length

#assert_axioms intent_to_zeroSpec
#assert_axioms createCellGates_give_zeroSpec
#assert_axioms createCell_runnable_full_sound
#assert_axioms createCell_binds_full_state_advantage_bound
#assert_axioms createCell_binds_full_state_rom
#assert_axioms createCell_rejects_root_tamper_advantage_bound
#assert_axioms createCell_rejects_root_tamper_rom
#assert_axioms goodCreateCell_realizes
#assert_axioms createCell_clause_not_trivial
#assert_axioms createCell_clause_rejects_root_drop

end Dregg2.Circuit.Emit.EffectVmEmitCreateCellFullState
