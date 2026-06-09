/-
# Dregg2.Circuit.Emit.EffectVmEmitCreateCellFromFactoryFullState — createCellFromFactory LIFTED to
FULL-STATE on the RUNNABLE descriptor (the magnesium breadth: the circuit the prover RUNS binds all 17
fields).

`EffectVmEmitCreateCellFromFactory`'s RUNNABLE row is BORN-EMPTY (identical SHAPE to createCell): the
minted cell's economic block is the all-zero block (`factoryRowGates`), bound into `state_commit` by the
4 GROUP-4 sites. That commitment absorbs only the 13 state-block columns, NOT the 8 side-table roots.
This module CLOSES that by amplifying the RUNNABLE descriptor to the WIDE (`system_roots`-absorbing)
shape and lifting through the generic `EffectVmFullStateRunnable.runnable_full_sound` crown: a satisfying
WIDE-descriptor witness pins the FULL 17-field declarative post-state — the per-cell BORN-EMPTY block
(`ZeroBlockSpec`) AND every one of the 8 side-table roots FROZEN. The anti-ghost tooth bites on all 17.

The factory writes only NON-`balance` record fields (no economic-column counterpart); the cross-cell
`accounts` GROW is the TURN-COMPOSITION layer fact. The §RECIPE applied to createCellFromFactory.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR only via the generic theorems.
No `sorry`/`:= True`/`native_decide`. `fullClause` NON-VACUOUS. Read-only imports; owns only itself.
-/
import Dregg2.Circuit.Emit.EffectVmEmitCreateCellFromFactory
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable

namespace Dregg2.Circuit.Emit.EffectVmEmitCreateCellFromFactoryFullState

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState absorbedCols)
open Dregg2.Circuit.Emit.EffectVmEmitCreateCellFromFactory
  (SEL_CREATECELLFROMFACTORY factoryRowGates factoryVmDescriptor BornEmptyRowIntent factoryVm_faithful)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (RunnableFullStateSpec runnable_full_sound runnable_full_commit_binds wide_rejects_root_tamper
   wideHashSites)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest emptySystemRoots N_SYSTEM_ROOTS)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §1 — the WIDE factory descriptor (width + sites; constraints UNCHANGED). -/

def factoryVmDescriptorWide : EffectVmDescriptor :=
  { factoryVmDescriptor with
    name := factoryVmDescriptor.name ++ "-sysroots"
    traceWidth := EFFECT_VM_WIDTH_SYSROOTS
    hashSites := wideHashSites }

theorem factoryWide_constraints_eq :
    factoryVmDescriptorWide.constraints = factoryVmDescriptor.constraints := rfl

/-- The row hypothesis: a createCellFromFactory row (`s_factory = 1`). -/
def IsFactoryRow (env : VmRowEnv) : Prop :=
  env.loc SEL_CREATECELLFROMFACTORY = 1

/-! ## §2 — the structured post decode + the BORN-EMPTY spec. -/

/-- `RowEncodesFactory env post` ties the row's `state_after` block to a concrete post-`CellState`. -/
def RowEncodesFactory (env : VmRowEnv) (post : CellState) : Prop :=
  env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved

/-- **`ZeroBlockSpec post`** — the per-cell FULL-state born-empty spec: every economic-data column of
`post` is ZERO. -/
def ZeroBlockSpec (post : CellState) : Prop :=
  post.balLo = 0
  ∧ post.balHi = 0
  ∧ post.nonce = 0
  ∧ (∀ i : Fin 8, post.fields i = 0)
  ∧ post.capRoot = 0
  ∧ post.reserved = 0

theorem intent_to_zeroSpec (env : VmRowEnv) (post : CellState)
    (henc : RowEncodesFactory env post) (hint : BornEmptyRowIntent env) :
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

theorem factoryGates_give_zeroSpec (env : VmRowEnv) (post : CellState)
    (henc : RowEncodesFactory env post)
    (hgates : ∀ c ∈ factoryVmDescriptor.constraints, c.holdsVm env true true) :
    ZeroBlockSpec post := by
  have hrowgates : ∀ c ∈ factoryRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ factoryVmDescriptor.constraints := by
      unfold factoryVmDescriptor; exact hc
    have hh := hgates c hmem
    unfold factoryRowGates Dregg2.Circuit.Emit.EffectVmEmitCreateCellFromFactory.gZero at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using hh
  exact intent_to_zeroSpec env post henc ((factoryVm_faithful env).mp hrowgates)

/-! ## §4 — the FULL declarative clause + the `RunnableFullStateSpec` instance. -/

/-- **`FactoryFullClause`** — the FULL 17-field declarative post for createCellFromFactory: the per-cell
BORN-EMPTY block (`ZeroBlockSpec`) AND the `system_roots` sub-block FROZEN. NON-VACUOUS. -/
def FactoryFullClause (preRoots : SysRoots) (pre post : CellState) (postRoots : SysRoots) : Prop :=
  ZeroBlockSpec post ∧ postRoots = preRoots

def factoryRunnableSpec (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor    := factoryVmDescriptorWide
  usesWideSites := rfl
  isRow         := IsFactoryRow
  decodeAfter   := fun env _pre post postRoots =>
    RowEncodesFactory env post ∧ postRoots = preRoots
  fullClause    := FactoryFullClause preRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots⟩ := hdec
    exact ⟨factoryGates_give_zeroSpec env post henc
            (factoryWide_constraints_eq ▸ hgates), hroots⟩

/-! ## §5 — THE DELIVERABLE: `createCellFromFactory_runnable_full_sound`. -/

/-- **`createCellFromFactory_runnable_full_sound` — the magnesium crown for createCellFromFactory.** A row
satisfying the WIDE RUNNABLE descriptor, decoded by `RowEncodesFactory` with the frozen-roots witness,
pins the FULL 17-field post-state: the per-cell BORN-EMPTY block (`ZeroBlockSpec`) AND all 8 side-table
roots FROZEN. -/
theorem createCellFromFactory_runnable_full_sound (hash : List ℤ → ℤ) (preRoots : SysRoots)
    (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsFactoryRow env)
    (henc : RowEncodesFactory env post) (hroots : postRoots = preRoots)
    (hsat : satisfiedVm hash factoryVmDescriptorWide env true true) :
    ZeroBlockSpec post ∧ postRoots = preRoots :=
  runnable_full_sound (factoryRunnableSpec preRoots) hash env pre post postRoots hrow
    ⟨henc, hroots⟩ hsat

/-! ## §6 — THE ANTI-GHOST. -/

theorem createCellFromFactory_runnable_full_commit_binds (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (preRoots : SysRoots) (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash factoryVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash factoryVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂) :
    absorbedCols e₁ = absorbedCols e₂ ∧ (∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i) :=
  runnable_full_commit_binds (factoryRunnableSpec preRoots) hash hCR e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂

theorem createCellFromFactory_rejects_root_tamper (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (preRoots : SysRoots) (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash factoryVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash factoryVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) : False :=
  wide_rejects_root_tamper (factoryRunnableSpec preRoots) hash hCR e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-! ## §7 — NON-VACUITY. -/

def factoryPreRoots : SysRoots := emptySystemRoots

def factoryPre : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

def factoryPost : CellState :=
  { balLo := 0, balHi := 0, nonce := 0, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

theorem goodFactory_realizes :
    (factoryRunnableSpec factoryPreRoots).fullClause factoryPre factoryPost factoryPreRoots :=
  ⟨⟨rfl, rfl, rfl, fun _ => rfl, rfl, rfl⟩, rfl⟩

theorem factory_clause_not_trivial :
    ¬ FactoryFullClause factoryPreRoots factoryPre { factoryPost with balLo := 999 } factoryPreRoots := by
  rintro ⟨⟨hbal, _, _, _, _, _⟩, _⟩
  simp only [factoryPost] at hbal
  norm_num at hbal

theorem factory_clause_rejects_root_drop :
    ¬ FactoryFullClause factoryPreRoots factoryPre factoryPost
        (fun i => if i = (⟨0, by decide⟩ : Fin N_SYSTEM_ROOTS) then 1 else 0) := by
  rintro ⟨_, hroots⟩
  have h0 := congrFun hroots (⟨0, by decide⟩ : Fin N_SYSTEM_ROOTS)
  simp only [factoryPreRoots, emptySystemRoots] at h0
  norm_num at h0

/-! ## §8 — layout + axiom-hygiene tripwires. -/

#guard factoryVmDescriptorWide.traceWidth == 188
#guard factoryVmDescriptorWide.hashSites.length == 4
#guard factoryVmDescriptorWide.constraints.length == factoryVmDescriptor.constraints.length

#assert_axioms intent_to_zeroSpec
#assert_axioms factoryGates_give_zeroSpec
#assert_axioms createCellFromFactory_runnable_full_sound
#assert_axioms createCellFromFactory_runnable_full_commit_binds
#assert_axioms createCellFromFactory_rejects_root_tamper
#assert_axioms goodFactory_realizes
#assert_axioms factory_clause_not_trivial
#assert_axioms factory_clause_rejects_root_drop

end Dregg2.Circuit.Emit.EffectVmEmitCreateCellFromFactoryFullState
