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

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The §6 anti-ghost is a SECURITY
REDUCTION (game + extractor-as-map-of-adversaries), not a bare `binds ∨ collides` disjunction: the
deployed-sponge leg is `Eff`-parametric with `hEff` in the open, and the keyed-ROM leg is DISCHARGED
on the PROVED birthday floor. `fullClause` NON-VACUOUS. Read-only imports; owns only itself.
-/
import Dregg2.Circuit.Emit.EffectVmEmitCreateCellFromFactory
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable
import Dregg2.Circuit.Emit.EffectVmRowCommitReduction

namespace Dregg2.Circuit.Emit.EffectVmEmitCreateCellFromFactoryFullState

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitCreateCellFromFactory
  (SEL_CREATECELLFROMFACTORY factoryRowGates factoryVmDescriptor BornEmptyRowIntent factoryVm_faithful)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (baseAbsorbedCols RunnableFullStateSpec runnable_full_sound wideHashSites)
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
`post` is ZERO as a field value (mod-`p` congruent to `0`; canonical `[0, p)` cells make this exact). -/
def ZeroBlockSpec (post : CellState) : Prop :=
  post.balLo ≡ 0 [ZMOD 2013265921]
  ∧ post.balHi ≡ 0 [ZMOD 2013265921]
  ∧ post.nonce ≡ 0 [ZMOD 2013265921]
  ∧ (∀ i : Fin 8, post.fields i ≡ 0 [ZMOD 2013265921])
  ∧ post.capRoot ≡ 0 [ZMOD 2013265921]
  ∧ post.reserved ≡ 0 [ZMOD 2013265921]

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
    (hgates : ∀ c ∈ factoryVmDescriptor.constraints, c.holdsVm env true false) :
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
    (hsat : satisfiedVm hash factoryVmDescriptorWide env true false) :
    ZeroBlockSpec post ∧ postRoots = preRoots :=
  runnable_full_sound (factoryRunnableSpec preRoots) hash env pre post postRoots hrow
    ⟨henc, hroots⟩ hsat

/-! ## §6 — ANTI-GHOST on all 17 fields, REBUILT AS SECURITY REDUCTIONS.

⚑ **WHAT CHANGED AND WHY.** This section used to export
`createCellFromFactory_runnable_full_commit_binds_or_collides` /
`createCellFromFactory_rejects_root_tamper_or_collides`, each concluding
`… ∨ WideColl hash e₁ e₂ ∨ RootsColl hash sr₁ sr₂`. Those forms are TRUE of the deployed sponge —
unlike the `Poseidon2SpongeCR` predecessors they replaced, which it REFUTES — but they are UNCLOSED:
a collision of the deployed sponge EXISTS at BabyBear parameters by pigeonhole
(`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`), so `binds ∨ collides` is satisfiable through
its RIGHT branch WITHOUT the binding ever holding. They quantify over SOLUTIONS; cryptographic
hardness quantifies over EFFICIENT ADVERSARIES.

They are DELETED — not kept beside the new forms — and rebuilt on
`Emit.EffectVmRowCommitReduction`, exactly as `EffectVmEmitMintRunnable` §4: the forgery is a
first-class `Game` AT THE FACTORY'S OWN WIDE DESCRIPTOR (a win is two rows BOTH ACCEPTED by
`factoryVmDescriptorWide` publishing one `NEW_COMMIT` over different bound state), the extractor is
a MAP OF ADVERSARIES (the reduction-internal witness, its correct role), and the conclusions are

  * negligibility under the DEPLOYED sponge's collision floor `HashCRHardQuant (spongeFamily D) Eff`,
    `hEff` in the open, both poles priced (`rowCommitFloor_top_false_babyBear` / `_bot_vacuous`); and
  * the DISCHARGED keyed-ROM forms on the PROVED birthday floor (`keyedRom_hard`) — NO floor
    hypothesis — in the LABELLED random-oracle model of `EffectVmRowCommitReduction` §5's header
    (the sampled `Fin (2 ^ l)` digest is the modelling step; no `l` is the deployed ~31-bit felt).

The ROM commitment layer carries no descriptor (the nested absorb schedule is one object across
effects); the factory's per-effect circuit content (`satisfiedVm` at `factoryVmDescriptorWide`)
lives in the `_advantage_bound` forms. -/

open Dregg2.Crypto.SpongeCarrierReduction (SpongeKeyed spongeFamily carrierBreakToFinder)
open Dregg2.Circuit.Emit.EffectVmRowCommitReduction
  (WideRowSpec wideStateCarrier wideRowBreakGame wideRowToCarrier wideRow_binds_advantage_bound
   wideRootTamperGame rootTamperToWide wide_root_tamper_advantage_bound
   wideRomFamily wideRomBreakGame effectVmWideRomForgery wideRow_binds_rom
   effectVmWideRomRootTamper wide_root_tamper_rom)
open Dregg2.Crypto.RomCarrierSites (RomForgeryEff)
open Dregg2.Crypto.FloorGames (Adversary gameAdv hashGame HashCRHardQuant)
open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded)

/-- **`factoryWideRowSpec`** — the factory's WIDE runnable descriptor as the reduction's per-effect
datum. The only obligation is that its hash sites ARE the `system_roots`-absorbing wide sites
(`rfl`). -/
def factoryWideRowSpec : WideRowSpec where
  descriptor := factoryVmDescriptorWide
  usesWideSites := rfl

/-- **⚑ `createCellFromFactory_binds_full_state_advantage_bound` — THE REDUCED WHOLE-17-FIELD
BINDING.** Under the DEPLOYED sponge's collision floor at the class `Eff`, an adversary producing
two rows BOTH SATISFYING `factoryVmDescriptorWide`, publishing one `NEW_COMMIT` with genuine
`systemRootsDigest` carriers, yet binding DIFFERENT state, has NEGLIGIBLE advantage. Replaces the
deleted bare disjunction. -/
theorem createCellFromFactory_binds_full_state_advantage_bound (D : SpongeKeyed)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (wideRowBreakGame D factoryWideRowSpec))
    (hEff : Eff (carrierBreakToFinder D wideStateCarrier
      (wideRowToCarrier D factoryWideRowSpec A)))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (wideRowBreakGame D factoryWideRowSpec) A) :=
  wideRow_binds_advantage_bound D factoryWideRowSpec Eff A hEff hCR

/-- **⚑⚑ `createCellFromFactory_binds_full_state_rom` — the DISCHARGED whole-17-field binding, on
the PROVED floor.** A query-bounded forger of the wide nested `state_commit` — the very commitment
the factory's wide row publishes — has NEGLIGIBLE advantage, in the keyed ROM model of
`EffectVmRowCommitReduction` §5's header. NO floor hypothesis. The COMMITMENT layer carries no
descriptor (the nested absorb schedule is one object across effects), so this is
`wideRow_binds_rom` at the deployed tag space; the factory's per-effect circuit content stays in
the `_advantage_bound` form above, `hEff` in the open. -/
theorem createCellFromFactory_binds_full_state_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (wideRomBreakGame D tagDec))
    (hA : RomForgeryEff (wideRomFamily D tagDec) (effectVmWideRomForgery D tagDec) Q A) :
    Negl (gameAdv (wideRomBreakGame D tagDec) A) :=
  wideRow_binds_rom D tagDec Q hQ A hA

/-- **⚑ `createCellFromFactory_rejects_root_tamper_advantage_bound` — the side-table anti-ghost,
REDUCED.** An efficient adversary cannot keep the published `NEW_COMMIT` while tampering a
side-table root of a satisfying wide factory row, except with negligible probability. Replaces the
deleted `createCellFromFactory_rejects_root_tamper_or_collides`. -/
theorem createCellFromFactory_rejects_root_tamper_advantage_bound (D : SpongeKeyed)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (wideRootTamperGame D factoryWideRowSpec))
    (hEff : Eff (carrierBreakToFinder D wideStateCarrier
      (wideRowToCarrier D factoryWideRowSpec (rootTamperToWide D factoryWideRowSpec A))))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (wideRootTamperGame D factoryWideRowSpec) A) :=
  wide_root_tamper_advantage_bound D factoryWideRowSpec Eff A hEff hCR

/-- **⚑ `createCellFromFactory_rejects_root_tamper_rom`** — the same tooth DISCHARGED on the PROVED
floor: a query-bounded adversary cannot keep the published nested commitment while tampering a
side-table root. -/
theorem createCellFromFactory_rejects_root_tamper_rom (D : SpongeKeyed)
    (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (effectVmWideRomRootTamper D tagDec).game)
    (hA : RomForgeryEff (wideRomFamily D tagDec) (effectVmWideRomRootTamper D tagDec) Q A) :
    Negl (gameAdv (effectVmWideRomRootTamper D tagDec).game A) :=
  wide_root_tamper_rom D tagDec Q hQ A hA

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
  unfold Int.ModEq at hbal
  omega

theorem factory_clause_rejects_root_drop :
    ¬ FactoryFullClause factoryPreRoots factoryPre factoryPost
        (fun i => if i = (⟨0, by decide⟩ : Fin N_SYSTEM_ROOTS) then 1 else 0) := by
  rintro ⟨_, hroots⟩
  have h0 := congrFun hroots (⟨0, by decide⟩ : Fin N_SYSTEM_ROOTS)
  simp only [factoryPreRoots, emptySystemRoots] at h0
  norm_num at h0

/-! ## §8 — layout + axiom-hygiene tripwires. -/

#guard factoryVmDescriptorWide.traceWidth == 190
#guard factoryVmDescriptorWide.hashSites.length == 4
#guard factoryVmDescriptorWide.constraints.length == factoryVmDescriptor.constraints.length

#assert_axioms intent_to_zeroSpec
#assert_axioms factoryGates_give_zeroSpec
#assert_axioms createCellFromFactory_runnable_full_sound
#assert_axioms createCellFromFactory_binds_full_state_advantage_bound
#assert_axioms createCellFromFactory_binds_full_state_rom
#assert_axioms createCellFromFactory_rejects_root_tamper_advantage_bound
#assert_axioms createCellFromFactory_rejects_root_tamper_rom
#assert_axioms goodFactory_realizes
#assert_axioms factory_clause_not_trivial
#assert_axioms factory_clause_rejects_root_drop

end Dregg2.Circuit.Emit.EffectVmEmitCreateCellFromFactoryFullState
