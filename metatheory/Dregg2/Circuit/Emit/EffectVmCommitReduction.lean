/-
# `Dregg2.Circuit.Emit.EffectVmCommitReduction` — the per-effect EffectVM state-commit bindings
rebuilt as SECURITY REDUCTIONS on the deployed sponge's collision floor.

## The sin this retires

Every per-effect emission module exported its commitment binding as a BARE DISJUNCTION:

    absorbedCols e₁ = absorbedCols e₂ ∨ TransferColl hash e₁ e₂                      -- narrow
    (baseAbsorbedCols e₁ = baseAbsorbedCols e₂ ∧ roots agree) ∨ WideColl … ∨ RootsColl …  -- wide

Those forms were a genuine improvement on their predecessors (which carried
`Poseidon2Binding.Poseidon2SpongeCR`, a floor the deployed BabyBear sponge REFUTES, so they were
VACUOUS at deployed parameters). But they are still UNCLOSED. A collision of the deployed sponge
EXISTS at deployed parameters by pigeonhole (`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`),
so `binds ∨ collides` is satisfiable through the `collides` branch WITHOUT `binds` ever holding.
The disjunction quantifies over SOLUTIONS; cryptographic hardness quantifies over EFFICIENT
ADVERSARIES.

## What replaces them (the `Market.WideCommitBoundary` §R shape, at the EffectVM row layer)

  * the honest floor is `FloorGames.HashCRHardQuant (poseidon2KeyedFamily D) Eff` — the collision
    game of the DEPLOYED domain-separated Poseidon2 sponge at an explicit adversary class, the same
    object `Circuit.DomainSeparatedCREffRegrounded` names, with BOTH poles already proved there
    (`effFloor_top_false_babyBear`: `Eff := ⊤` is FALSE at deployed BabyBear params;
    `effFloor_bot_vacuous`: `Eff := ⊥` is vacuous);
  * the forgery is a first-class `Game` whose ANSWERS ARE DEPLOYED ROWS — `narrowSiteBreakGame` /
    `narrowDescriptorBreakGame E` / `wideSiteBreakGame` / `wideDescriptorBreakGame E`. The win
    relation contains `satisfiedVm` at the effect's OWN descriptor, so the game is not a
    free-floating construction: a win IS two satisfying rows of the deployed circuit publishing one
    `NEW_COMMIT` while disagreeing on an absorbed state column (or a side-table root);
  * the reduction is an EXTRACTOR AS A MAP OF ADVERSARIES — `narrowBreakToFinder` runs the deployed
    GROUP-4 trace (`transferCollFind`), `wideBreakToFinder` runs the wide GROUP-4 trace and falls
    through to the roots list — with a win-preservation theorem and an UNCONDITIONAL advantage
    inequality over ALL adversaries (the class does NOT appear in the inequality);
  * `hEff` is DISCHARGED at `Eff := IsPolyTime` by `CostTactics.poly_time`: both hops are pure
    output reshapings, so `isPolyTime_postMap` folds in the tight-δ composition and the derived
    poly overhead, leaving ONLY the output-size fact (`hout`), which is PROVED here
    (`group4Find_len_le`, `wideRowFind_len_le`) rather than hypothesized.

The `_or_collides` extractors REMAIN — as the reduction's INTERNAL witness, which is their correct
role. What is DELETED at each site is the bare disjunction as the EXPORTED headline binding.

## Bars

No `sorry`, no `axiom`, no `native_decide`, no `decide` on an opaque prop. Cost stays SYNTACTIC
(`CostAdversary`'s `FreeOracle` program syntax; no assertable cost field). `#assert_all_clean` at
the bottom.
-/
import Dregg2.Circuit.DomainSeparatedCREffRegrounded
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable
import Dregg2.Crypto.CostAdversary
import Dregg2.Crypto.CostTactics
import Dregg2.Circuit.Emit.EffectVmEmitCellDestroy
import Dregg2.Circuit.Emit.EffectVmEmitCellDestroyFullState
import Dregg2.Circuit.Emit.EffectVmEmitMakeSovereign
import Dregg2.Circuit.Emit.EffectVmEmitMakeSovereignFullState
import Dregg2.Circuit.Emit.EffectVmEmitIncrementNonce
import Dregg2.Circuit.Emit.EffectVmEmitIncrementNonceFullState
import Dregg2.Circuit.Emit.EffectVmEmitExercise
import Dregg2.Circuit.Emit.EffectVmEmitExerciseWide
import Dregg2.Circuit.Emit.EffectVmEmitEmitEvent
import Dregg2.Circuit.Emit.EffectVmEmitEmitEventWide
import Dregg2.Circuit.Emit.EffectVmEmitReceiptArchive
import Dregg2.Circuit.Emit.EffectVmEmitReceiptArchiveWide
import Dregg2.Circuit.Emit.EffectVmEmitPipelinedSend
import Dregg2.Circuit.Emit.EffectVmEmitPipelinedSendWide
import Dregg2.Circuit.Emit.EffectVmEmitRefusal
import Dregg2.Circuit.Emit.EffectVmEmitRefusalFullState
import Dregg2.Circuit.Emit.EffectVmEmitNoopWide

namespace Dregg2.Circuit.Emit.EffectVmCommitReduction

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (transferHashSites boundaryLastPins boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (absorbedCols transferBlockA transferBlockB transferBlockC transferCollFind TransferColl
   absorbed_determined_by_commit_or_collides)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (baseAbsorbedCols wideHashSites wideBlockA wideBlockB wideBlockC wideCollFind WideColl
   wide_binds_or_collides wide_binds_systemRoots_or_collides RootsColl rootsCollFind)
open Dregg2.Circuit.Poseidon2Binding (SpongeColl group4Find group4Find_spec)
open Dregg2.Circuit.Poseidon2KeyedBridge (DomainSeparatedSponge poseidon2KeyedFamily)
open Dregg2.Circuit.DomainSeparatedCREffRegrounded
  (DomainSeparatedCREff effFloor_top_false_babyBear effFloor_bot_vacuous)
open Dregg2.Crypto.FloorGames
  (Game Adversary gameAdv gameAdv_mem_unit hashGame HashCRHardQuant)
open Dregg2.Crypto.ConcreteSecurity (Negl)
open Dregg2.Crypto.ProbCrypto (winProb_le_of_imp negl_of_le)
open Dregg2.Crypto.CostAdversary (AnsSize IsPolyTime)
open Dregg2.Exec.SystemRoots (SysRoots systemRootsDigest rootList N_SYSTEM_ROOTS)

set_option autoImplicit false

/-! ## §0 — the deployed BabyBear modulus the row canonicality envelope uses. -/

/-- The deployed BabyBear prime `p = 2³¹ − 2²⁷ + 1`, the modulus `VmConstraint.holdsVm` works in. -/
def babyBearP : ℤ := 2013265921

/-! ## §1 — OUTPUT-SIZE FACTS for the two extractors (the `hout` slot, PROVED not assumed).

`CostAdversary`'s efficiency-preservation lemma charges the reduction for the symbols it WRITES.
Both extractors here are chain/tree traces that hand back a pair of short lists; these two lemmas
prove exactly how short, so `poly_time`'s only remaining obligation is discharged from a theorem
rather than from an assumption. -/

/-- **THE GROUP-4 TRACE DOES NOT BLOW UP ITS INPUT.** Every branch of `group4Find` returns either a
freshly built four-slot outer list or one of the (≤ 4-wide) inner blocks, so the pair it hands back
is at most `8` felts wide, whichever branch it takes. -/
theorem group4Find_len_le (hash : List ℤ → ℤ) (A₁ B₁ C₁ : List ℤ) (d₁ : ℤ)
    (A₂ B₂ C₂ : List ℤ) (d₂ : ℤ)
    (hA₁ : A₁.length ≤ 4) (hA₂ : A₂.length ≤ 4)
    (hB₁ : B₁.length ≤ 4) (hB₂ : B₂.length ≤ 4)
    (hC₁ : C₁.length ≤ 4) (hC₂ : C₂.length ≤ 4) :
    (group4Find hash A₁ B₁ C₁ d₁ A₂ B₂ C₂ d₂).1.length
      + (group4Find hash A₁ B₁ C₁ d₁ A₂ B₂ C₂ d₂).2.length ≤ 8 := by
  unfold group4Find
  split_ifs <;> simp only [List.length_cons, List.length_nil] <;> omega

/-- The deployed narrow GROUP-4 blocks are literal four-limb lists. -/
theorem transferBlock_len (e : VmRowEnv) :
    (transferBlockA e).length = 4 ∧ (transferBlockB e).length = 4
      ∧ (transferBlockC e).length = 4 := ⟨rfl, rfl, rfl⟩

/-- The deployed wide GROUP-4 blocks are literal four-limb lists. -/
theorem wideBlock_len (e : VmRowEnv) :
    (wideBlockA e).length = 4 ∧ (wideBlockB e).length = 4
      ∧ (wideBlockC e).length = 4 := ⟨rfl, rfl, rfl⟩

/-- **⚑ THE NARROW EXTRACTOR'S OUTPUT IS A CONSTANT `8` FELTS.** -/
theorem transferCollFind_len_le (hash : List ℤ → ℤ) (e₁ e₂ : VmRowEnv) :
    (transferCollFind hash e₁ e₂).1.length + (transferCollFind hash e₁ e₂).2.length ≤ 8 := by
  unfold transferCollFind
  exact group4Find_len_le hash _ _ _ _ _ _ _ _ (le_of_eq rfl) (le_of_eq rfl) (le_of_eq rfl)
    (le_of_eq rfl) (le_of_eq rfl) (le_of_eq rfl)

/-- The ordered side-table root list is exactly the eight-wide sub-block. -/
theorem rootList_len (sr : SysRoots) : (rootList sr).length = N_SYSTEM_ROOTS := by
  simp [rootList]

/-! ## §2 — the NARROW (13-column `state_commit`) forgery, as a GAME on DEPLOYED ROWS. -/

/-- **THE NARROW HASH-SITE FORGERY GAME.** The adversary is handed a uniformly sampled
domain-separation tag and WINS iff it outputs two rows whose deployed GROUP-4 hash sites hold at
that tag, whose published `state_commit` COLUMNS are EQUAL, and whose ABSORBED STATE COLUMNS DIFFER
— i.e. it equivocates the deployed `commitOf` digest. The break is IN the win relation. -/
noncomputable def narrowSiteBreakGame (D : DomainSeparatedSponge) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => VmRowEnv × VmRowEnv
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t c =>
    siteHoldsAll (D.hashAt t) c.1 transferHashSites
      ∧ siteHoldsAll (D.hashAt t) c.2 transferHashSites
      ∧ c.1.loc (saCol state.STATE_COMMIT) = c.2.loc (saCol state.STATE_COMMIT)
      ∧ absorbedCols c.1 ≠ absorbedCols c.2
  winsDec := fun _ _ _ => Classical.propDecidable _

/-- **THE PROBLEM IS IN THE STATEMENT** — the win relation is a genuine equivocation of the deployed
narrow state commitment. -/
theorem narrowSiteBreakGame_wins_iff (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (c : VmRowEnv × VmRowEnv) :
    (narrowSiteBreakGame D).wins l t c ↔
      (siteHoldsAll (D.hashAt t) c.1 transferHashSites
        ∧ siteHoldsAll (D.hashAt t) c.2 transferHashSites
        ∧ c.1.loc (saCol state.STATE_COMMIT) = c.2.loc (saCol state.STATE_COMMIT)
        ∧ absorbedCols c.1 ≠ absorbedCols c.2) :=
  Iff.rfl

/-- **THE EXTRACTOR, AS A MAP OF ADVERSARIES.** A narrow state-commit equivocator becomes a sponge
collision finder by running the deployed GROUP-4 trace (`transferCollFind`) on its two rows. This is
the very extractor the retired `_or_collides` disjunctions handed back as data; here it is the
reduction's internal witness, which is its correct role. -/
noncomputable def narrowBreakToFinder (D : DomainSeparatedSponge)
    (A : Adversary (narrowSiteBreakGame D)) : Adversary (hashGame (poseidon2KeyedFamily D)) where
  run := fun l t => transferCollFind (D.hashAt t) (A.run l t).1 (A.run l t).2

/-- **⚑ WIN-PRESERVATION — the reduction, at the game level.** At every tag the equivocator wins, the
extracted finder wins the DEPLOYED sponge's collision game: `absorbed_determined_by_commit_or_collides`
either forces the absorbed columns equal (contradicting the win) or hands back a genuine collision. -/
theorem narrow_wins_imp (D : DomainSeparatedSponge) (A : Adversary (narrowSiteBreakGame D))
    (l : ℕ) (t : D.Tag) (hwin : (narrowSiteBreakGame D).wins l t (A.run l t)) :
    (hashGame (poseidon2KeyedFamily D)).wins l t ((narrowBreakToFinder D A).run l t) := by
  obtain ⟨hs₁, hs₂, hcommit, hne⟩ := hwin
  rcases absorbed_determined_by_commit_or_collides (D.hashAt t) (A.run l t).1 (A.run l t).2
    hs₁ hs₂ hcommit with heq | hcoll
  · exact absurd heq hne
  · exact hcoll

/-- **THE ADVANTAGE INEQUALITY** — UNCONDITIONAL, over ALL adversaries: no class appears. The
equivocator's advantage is at most the extracted collision finder's, at every parameter, over the
SAME sampled tag space. -/
theorem narrow_adv_le (D : DomainSeparatedSponge) (A : Adversary (narrowSiteBreakGame D)) (l : ℕ) :
    gameAdv (narrowSiteBreakGame D) A l
      ≤ gameAdv (hashGame (poseidon2KeyedFamily D)) (narrowBreakToFinder D A) l := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  rw [Adversary.hit_eq_true] at ht ⊢
  exact narrow_wins_imp D A l t ht

/-- **⚑ THE REDUCED NARROW BINDING — from the DEPLOYED sponge's collision floor, VIA the reduction.**

Under the deployed domain-separated Poseidon2's collision floor at the class `Eff`, a narrow
state-commit equivocator whose extracted finder is in that class has NEGLIGIBLE advantage: the
published `state_commit` binds all thirteen absorbed state-block columns except with negligible
probability. This REPLACES the bare `_binds_block_or_collides` disjunction as the deployed binding.

`hEff` is the standard "the reduction is efficient" obligation, in the open; §5 DISCHARGES it at
`Eff := IsPolyTime`. -/
theorem narrowCommit_binds_advantage_bound (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : Adversary (narrowSiteBreakGame D))
    (hEff : Eff (narrowBreakToFinder D A))
    (hCR : DomainSeparatedCREff D Eff) :
    Negl (gameAdv (narrowSiteBreakGame D) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (narrowSiteBreakGame D) A l).1)
    (narrow_adv_le D A) (hCR _ hEff)

/-! ## §3 — the DESCRIPTOR-level narrow forgery: the row the PROVER RUNS.

§2's game hypothesises the two rows' `state_commit` COLUMNS agree. The deployed anti-ghost claim is
stronger and is about the descriptor: two rows SATISFYING the effect's circuit and publishing the
same `NEW_COMMIT` public input. Chaining the two needs the per-effect fact that satisfaction PINS
the commit column to the published PI — which is exactly the per-effect content the retired
`_binds_state_or_collides` theorems carried. `NarrowCommitSpec` is that obligation, named. -/

/-- The per-effect data a narrow (13-column) EffectVM descriptor must supply to ride this reduction:
its hash sites ARE the deployed GROUP-4 sites, and satisfaction PINS the after-state `state_commit`
column to the published `NEW_COMMIT` (mod the deployed BabyBear prime — `holdsVm`'s modulus). -/
structure NarrowCommitSpec where
  /-- The effect's emitted EffectVM descriptor. -/
  descriptor : EffectVmDescriptor
  /-- Its hash sites ARE the deployed narrow GROUP-4 sites (`transferHashSites`). -/
  usesTransferSites : descriptor.hashSites = transferHashSites
  /-- **THE PER-EFFECT OBLIGATION.** A satisfying row's after-state `state_commit` column is the
  published `NEW_COMMIT`, mod the deployed prime — the descriptor's own last-row PI pins. -/
  pinsNewCommit : ∀ (hash : List ℤ → ℤ) (e : VmRowEnv),
    satisfiedVm hash descriptor e true true →
    e.loc (saCol state.STATE_COMMIT) ≡ e.pub pi.NEW_COMMIT [ZMOD 2013265921]

/-- **THE DESCRIPTOR-LEVEL NARROW FORGERY GAME.** The adversary WINS iff it outputs two rows that
SATISFY the effect's emitted descriptor at the sampled tag, whose commit columns are canonical
(the deployed range-check envelope), which publish the SAME `NEW_COMMIT`, and whose absorbed state
columns DIFFER. A win is a ghost post-state accepted by the circuit the prover runs. -/
noncomputable def narrowDescriptorBreakGame (D : DomainSeparatedSponge) (E : NarrowCommitSpec) :
    Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => VmRowEnv × VmRowEnv
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t c =>
    satisfiedVm (D.hashAt t) E.descriptor c.1 true true
      ∧ satisfiedVm (D.hashAt t) E.descriptor c.2 true true
      ∧ (0 ≤ c.1.loc (saCol state.STATE_COMMIT)
          ∧ c.1.loc (saCol state.STATE_COMMIT) < babyBearP)
      ∧ (0 ≤ c.2.loc (saCol state.STATE_COMMIT)
          ∧ c.2.loc (saCol state.STATE_COMMIT) < babyBearP)
      ∧ c.1.pub pi.NEW_COMMIT = c.2.pub pi.NEW_COMMIT
      ∧ absorbedCols c.1 ≠ absorbedCols c.2
  winsDec := fun _ _ _ => Classical.propDecidable _

/-- **THE PROBLEM IS IN THE STATEMENT** — a win is two SATISFYING rows of the deployed circuit that
publish one commitment and disagree on the state they claim. -/
theorem narrowDescriptorBreakGame_wins_iff (D : DomainSeparatedSponge) (E : NarrowCommitSpec)
    (l : ℕ) (t : D.Tag) (c : VmRowEnv × VmRowEnv) :
    (narrowDescriptorBreakGame D E).wins l t c ↔
      (satisfiedVm (D.hashAt t) E.descriptor c.1 true true
        ∧ satisfiedVm (D.hashAt t) E.descriptor c.2 true true
        ∧ (0 ≤ c.1.loc (saCol state.STATE_COMMIT)
            ∧ c.1.loc (saCol state.STATE_COMMIT) < babyBearP)
        ∧ (0 ≤ c.2.loc (saCol state.STATE_COMMIT)
            ∧ c.2.loc (saCol state.STATE_COMMIT) < babyBearP)
        ∧ c.1.pub pi.NEW_COMMIT = c.2.pub pi.NEW_COMMIT
        ∧ absorbedCols c.1 ≠ absorbedCols c.2) :=
  Iff.rfl

/-- **THE LIFT, AS A MAP OF ADVERSARIES.** A descriptor-level forger IS a hash-site-level
equivocator — the rows pass through untouched; what the reduction supplies is the PROOF that the
descriptor's PI pins turn a shared `NEW_COMMIT` into a shared commit COLUMN. -/
noncomputable def descriptorToSiteBreak (D : DomainSeparatedSponge) (E : NarrowCommitSpec)
    (A : Adversary (narrowDescriptorBreakGame D E)) : Adversary (narrowSiteBreakGame D) where
  run := fun l t => A.run l t

/-- **⚑ WIN-PRESERVATION — the descriptor's PI pins chain the two commit columns.** Each satisfying
row pins its commit cell to `PI[NEW_COMMIT]` mod `p`; the shared PI value then chains the two
(both canonical) into an equality over `ℤ`. No canonicality of the PI itself is needed. -/
theorem descriptorToSite_wins_imp (D : DomainSeparatedSponge) (E : NarrowCommitSpec)
    (A : Adversary (narrowDescriptorBreakGame D E)) (l : ℕ) (t : D.Tag)
    (hwin : (narrowDescriptorBreakGame D E).wins l t (A.run l t)) :
    (narrowSiteBreakGame D).wins l t ((descriptorToSiteBreak D E A).run l t) := by
  obtain ⟨hsat₁, hsat₂, hc₁, hc₂, hpub, hne⟩ := hwin
  refine ⟨E.usesTransferSites ▸ hsat₁.2.1, E.usesTransferSites ▸ hsat₂.2.1, ?_, hne⟩
  show (A.run l t).1.loc (saCol state.STATE_COMMIT) = (A.run l t).2.loc (saCol state.STATE_COMMIT)
  have h₁ := E.pinsNewCommit (D.hashAt t) _ hsat₁
  have h₂ := E.pinsNewCommit (D.hashAt t) _ hsat₂
  rw [hpub] at h₁
  have hdvd := Int.ModEq.dvd (h₁.trans h₂.symm)
  simp only [babyBearP] at hc₁ hc₂
  omega

/-- **THE ADVANTAGE INEQUALITY** for the descriptor lift — UNCONDITIONAL, over ALL adversaries. -/
theorem descriptorToSite_adv_le (D : DomainSeparatedSponge) (E : NarrowCommitSpec)
    (A : Adversary (narrowDescriptorBreakGame D E)) (l : ℕ) :
    gameAdv (narrowDescriptorBreakGame D E) A l
      ≤ gameAdv (narrowSiteBreakGame D) (descriptorToSiteBreak D E A) l := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  rw [Adversary.hit_eq_true] at ht ⊢
  exact descriptorToSite_wins_imp D E A l t ht

/-- **⚑ THE REDUCED DESCRIPTOR BINDING — the headline that replaces `_binds_state_or_collides`.**

Under the deployed sponge's collision floor at the class `Eff`, a forger that produces two
SATISFYING rows of the effect's emitted descriptor publishing one `NEW_COMMIT` while disagreeing on
an absorbed state column has NEGLIGIBLE advantage. The composition is
descriptor forger → (`descriptorToSiteBreak`) hash-site equivocator → (`narrowBreakToFinder`) a
genuine collision of the DEPLOYED sponge. -/
theorem narrowDescriptor_binds_advantage_bound (D : DomainSeparatedSponge) (E : NarrowCommitSpec)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : Adversary (narrowDescriptorBreakGame D E))
    (hEff : Eff (narrowBreakToFinder D (descriptorToSiteBreak D E A)))
    (hCR : DomainSeparatedCREff D Eff) :
    Negl (gameAdv (narrowDescriptorBreakGame D E) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (narrowDescriptorBreakGame D E) A l).1)
    (descriptorToSite_adv_le D E A)
    (narrowCommit_binds_advantage_bound D Eff (descriptorToSiteBreak D E A) hEff hCR)

/-! ## §4 — the WIDE (`system_roots`-absorbing) forgery, as a GAME on DEPLOYED ROWS.

The wide commitment absorbs the twelve base state columns AND the side-table digest carrier, so a
wide forgery has TWO possible collision sources: the GROUP-4 tree (`WideColl`) and the roots list
(`RootsColl`). Both are collisions of the SAME deployed sponge, so ONE extractor suffices — it takes
the GROUP-4 pair when that pair genuinely collides and falls through to the roots pair otherwise.
This is why the wide reduction lands on one floor and needs no union bound. -/

/-- **THE WIDE EXTRACTOR.** Take the GROUP-4 trace's pair when it is a genuine sponge collision;
otherwise the two ordered side-table root lists. Decidable branch (`decidableSpongeColl`), so this
is a TOTAL function with no `Classical.choice` in the walk. -/
noncomputable def wideRowFind (hash : List ℤ → ℤ) (c c' : VmRowEnv × SysRoots) : List ℤ × List ℤ :=
  if SpongeColl hash (wideCollFind hash c.1 c'.1) then wideCollFind hash c.1 c'.1
  else rootsCollFind c.2 c'.2

/-- **⚑ THE WIDE EXTRACTOR'S OUTPUT IS BOUNDED BY A CONSTANT.** The GROUP-4 branch returns at most
`8` felts; the roots branch returns the two eight-wide sub-blocks, `16`. -/
theorem wideRowFind_len_le (hash : List ℤ → ℤ) (c c' : VmRowEnv × SysRoots) :
    (wideRowFind hash c c').1.length + (wideRowFind hash c c').2.length ≤ 16 := by
  unfold wideRowFind
  split_ifs with h
  · have := group4Find_len_le hash (wideBlockA c.1) (wideBlockB c.1) (wideBlockC c.1)
      (c.1.loc sysRootsDigestCol) (wideBlockA c'.1) (wideBlockB c'.1) (wideBlockC c'.1)
      (c'.1.loc sysRootsDigestCol) (le_of_eq rfl) (le_of_eq rfl) (le_of_eq rfl) (le_of_eq rfl)
      (le_of_eq rfl) (le_of_eq rfl)
    show (wideCollFind hash c.1 c'.1).1.length + (wideCollFind hash c.1 c'.1).2.length ≤ 16
    unfold wideCollFind
    omega
  · show (rootList c.2).length + (rootList c'.2).length ≤ 16
    rw [rootList_len, rootList_len]
    simp [N_SYSTEM_ROOTS]

/-- **THE WIDE HASH-SITE FORGERY GAME.** The adversary WINS iff it outputs two rows-with-side-tables
whose wide hash sites hold at the sampled tag, whose side-table carriers ARE the `systemRootsDigest`
of their claimed sub-blocks, whose `state_commit` columns are EQUAL, and which nevertheless DISAGREE
— on a base absorbed column, or on some side-table root. -/
noncomputable def wideSiteBreakGame (D : DomainSeparatedSponge) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => (VmRowEnv × SysRoots) × (VmRowEnv × SysRoots)
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t c =>
    siteHoldsAll (D.hashAt t) c.1.1 wideHashSites
      ∧ siteHoldsAll (D.hashAt t) c.2.1 wideHashSites
      ∧ c.1.1.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) c.1.2
      ∧ c.2.1.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) c.2.2
      ∧ c.1.1.loc (saCol state.STATE_COMMIT) = c.2.1.loc (saCol state.STATE_COMMIT)
      ∧ ¬ (baseAbsorbedCols c.1.1 = baseAbsorbedCols c.2.1
            ∧ ∀ i : Fin N_SYSTEM_ROOTS, c.1.2 i = c.2.2 i)
  winsDec := fun _ _ _ => Classical.propDecidable _

/-- **THE PROBLEM IS IN THE STATEMENT** — a win is a genuine equivocation of the deployed WIDE
commitment, over the whole 17-field post-state. -/
theorem wideSiteBreakGame_wins_iff (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (c : (VmRowEnv × SysRoots) × (VmRowEnv × SysRoots)) :
    (wideSiteBreakGame D).wins l t c ↔
      (siteHoldsAll (D.hashAt t) c.1.1 wideHashSites
        ∧ siteHoldsAll (D.hashAt t) c.2.1 wideHashSites
        ∧ c.1.1.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) c.1.2
        ∧ c.2.1.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) c.2.2
        ∧ c.1.1.loc (saCol state.STATE_COMMIT) = c.2.1.loc (saCol state.STATE_COMMIT)
        ∧ ¬ (baseAbsorbedCols c.1.1 = baseAbsorbedCols c.2.1
              ∧ ∀ i : Fin N_SYSTEM_ROOTS, c.1.2 i = c.2.2 i)) :=
  Iff.rfl

/-- **THE WIDE EXTRACTOR, AS A MAP OF ADVERSARIES.** -/
noncomputable def wideBreakToFinder (D : DomainSeparatedSponge)
    (A : Adversary (wideSiteBreakGame D)) : Adversary (hashGame (poseidon2KeyedFamily D)) where
  run := fun l t => wideRowFind (D.hashAt t) (A.run l t).1 (A.run l t).2

/-- **⚑ WIN-PRESERVATION — the wide reduction, at the game level.** The deployed peel
(`wide_binds_or_collides` for the base columns, `wide_binds_systemRoots_or_collides` for the roots)
either forces full agreement — contradicting the win — or lands on one of the two named collisions,
and `wideRowFind` selects whichever one is genuine. -/
theorem wide_wins_imp (D : DomainSeparatedSponge) (A : Adversary (wideSiteBreakGame D))
    (l : ℕ) (t : D.Tag) (hwin : (wideSiteBreakGame D).wins l t (A.run l t)) :
    (hashGame (poseidon2KeyedFamily D)).wins l t ((wideBreakToFinder D A).run l t) := by
  obtain ⟨hs₁, hs₂, hd₁, hd₂, hcommit, hne⟩ := hwin
  show SpongeColl (D.hashAt t) (wideRowFind (D.hashAt t) (A.run l t).1 (A.run l t).2)
  unfold wideRowFind
  split_ifs with hg
  · exact hg
  · rcases wide_binds_or_collides (D.hashAt t) (A.run l t).1.1 (A.run l t).2.1 hs₁ hs₂ hcommit with
      ⟨hcols, _⟩ | hcoll
    · rcases wide_binds_systemRoots_or_collides (D.hashAt t) (A.run l t).1.1 (A.run l t).2.1
        (A.run l t).1.2 (A.run l t).2.2 hs₁ hs₂ hcommit hd₁ hd₂ with hroots | hcoll' | hrcoll
      · exact absurd ⟨hcols, hroots⟩ hne
      · exact absurd hcoll' hg
      · exact hrcoll
    · exact absurd hcoll hg

/-- **THE ADVANTAGE INEQUALITY** — UNCONDITIONAL, over ALL adversaries. -/
theorem wide_adv_le (D : DomainSeparatedSponge) (A : Adversary (wideSiteBreakGame D)) (l : ℕ) :
    gameAdv (wideSiteBreakGame D) A l
      ≤ gameAdv (hashGame (poseidon2KeyedFamily D)) (wideBreakToFinder D A) l := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  rw [Adversary.hit_eq_true] at ht ⊢
  exact wide_wins_imp D A l t ht

/-- **⚑ THE REDUCED WIDE BINDING — the headline that replaces `_wide_binds_full_state_or_collides`.**
Under the deployed sponge's collision floor at `Eff`, a wide equivocator whose extracted finder is in
that class has NEGLIGIBLE advantage: the wide commitment binds the twelve base state columns AND all
eight side-table roots except with negligible probability. -/
theorem wideCommit_binds_advantage_bound (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : Adversary (wideSiteBreakGame D))
    (hEff : Eff (wideBreakToFinder D A))
    (hCR : DomainSeparatedCREff D Eff) :
    Negl (gameAdv (wideSiteBreakGame D) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (wideSiteBreakGame D) A l).1)
    (wide_adv_le D A) (hCR _ hEff)

/-! ### §4b — the DESCRIPTOR-level wide forgery. -/

/-- The per-effect data a WIDE (`system_roots`-absorbing) descriptor supplies: its hash sites ARE
the wide sites. (Unlike the narrow case no PI-pinning obligation is needed — the deployed wide
anti-ghost statements take the commit-column pins as explicit hypotheses, and so does the game.) -/
structure WideCommitSpec where
  /-- The effect's WIDE emitted descriptor. -/
  descriptor : EffectVmDescriptor
  /-- Its hash sites ARE the `system_roots`-absorbing wide sites. -/
  usesWideSites : descriptor.hashSites = wideHashSites

/-- **THE DESCRIPTOR-LEVEL WIDE FORGERY GAME.** The adversary WINS iff it outputs two
rows-with-side-tables that SATISFY the effect's WIDE descriptor at the sampled tag, whose commit
columns are pinned to their published `NEW_COMMIT`s, which publish the SAME `NEW_COMMIT`, whose
carriers are the claimed sub-blocks' digests, and which DISAGREE on a base column or a root. -/
noncomputable def wideDescriptorBreakGame (D : DomainSeparatedSponge) (E : WideCommitSpec) :
    Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => (VmRowEnv × SysRoots) × (VmRowEnv × SysRoots)
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t c =>
    satisfiedVm (D.hashAt t) E.descriptor c.1.1 true true
      ∧ satisfiedVm (D.hashAt t) E.descriptor c.2.1 true true
      ∧ c.1.1.loc (saCol state.STATE_COMMIT) = c.1.1.pub pi.NEW_COMMIT
      ∧ c.2.1.loc (saCol state.STATE_COMMIT) = c.2.1.pub pi.NEW_COMMIT
      ∧ c.1.1.pub pi.NEW_COMMIT = c.2.1.pub pi.NEW_COMMIT
      ∧ c.1.1.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) c.1.2
      ∧ c.2.1.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) c.2.2
      ∧ ¬ (baseAbsorbedCols c.1.1 = baseAbsorbedCols c.2.1
            ∧ ∀ i : Fin N_SYSTEM_ROOTS, c.1.2 i = c.2.2 i)
  winsDec := fun _ _ _ => Classical.propDecidable _

/-- **THE PROBLEM IS IN THE STATEMENT** — a win is two SATISFYING wide rows of the circuit the prover
runs, publishing one commitment over two different whole-system states. -/
theorem wideDescriptorBreakGame_wins_iff (D : DomainSeparatedSponge) (E : WideCommitSpec)
    (l : ℕ) (t : D.Tag) (c : (VmRowEnv × SysRoots) × (VmRowEnv × SysRoots)) :
    (wideDescriptorBreakGame D E).wins l t c ↔
      (satisfiedVm (D.hashAt t) E.descriptor c.1.1 true true
        ∧ satisfiedVm (D.hashAt t) E.descriptor c.2.1 true true
        ∧ c.1.1.loc (saCol state.STATE_COMMIT) = c.1.1.pub pi.NEW_COMMIT
        ∧ c.2.1.loc (saCol state.STATE_COMMIT) = c.2.1.pub pi.NEW_COMMIT
        ∧ c.1.1.pub pi.NEW_COMMIT = c.2.1.pub pi.NEW_COMMIT
        ∧ c.1.1.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) c.1.2
        ∧ c.2.1.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) c.2.2
        ∧ ¬ (baseAbsorbedCols c.1.1 = baseAbsorbedCols c.2.1
              ∧ ∀ i : Fin N_SYSTEM_ROOTS, c.1.2 i = c.2.2 i)) :=
  Iff.rfl

/-- **THE WIDE LIFT, AS A MAP OF ADVERSARIES.** -/
noncomputable def wideDescriptorToSiteBreak (D : DomainSeparatedSponge) (E : WideCommitSpec)
    (A : Adversary (wideDescriptorBreakGame D E)) : Adversary (wideSiteBreakGame D) where
  run := fun l t => A.run l t

/-- **⚑ WIN-PRESERVATION for the wide lift** — the two commit pins plus the shared `NEW_COMMIT`
chain the commit columns; the wide hash sites come from satisfaction. -/
theorem wideDescriptorToSite_wins_imp (D : DomainSeparatedSponge) (E : WideCommitSpec)
    (A : Adversary (wideDescriptorBreakGame D E)) (l : ℕ) (t : D.Tag)
    (hwin : (wideDescriptorBreakGame D E).wins l t (A.run l t)) :
    (wideSiteBreakGame D).wins l t ((wideDescriptorToSiteBreak D E A).run l t) := by
  obtain ⟨hsat₁, hsat₂, hpin₁, hpin₂, hpub, hd₁, hd₂, hne⟩ := hwin
  refine ⟨E.usesWideSites ▸ hsat₁.2.1, E.usesWideSites ▸ hsat₂.2.1, hd₁, hd₂, ?_, hne⟩
  show (A.run l t).1.1.loc (saCol state.STATE_COMMIT)
    = (A.run l t).2.1.loc (saCol state.STATE_COMMIT)
  rw [hpin₁, hpin₂, hpub]

/-- **THE ADVANTAGE INEQUALITY** for the wide descriptor lift. -/
theorem wideDescriptorToSite_adv_le (D : DomainSeparatedSponge) (E : WideCommitSpec)
    (A : Adversary (wideDescriptorBreakGame D E)) (l : ℕ) :
    gameAdv (wideDescriptorBreakGame D E) A l
      ≤ gameAdv (wideSiteBreakGame D) (wideDescriptorToSiteBreak D E A) l := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  rw [Adversary.hit_eq_true] at ht ⊢
  exact wideDescriptorToSite_wins_imp D E A l t ht

/-- **⚑ THE REDUCED WIDE DESCRIPTOR BINDING — the headline that replaces the wide
`_or_collides` disjunctions.** -/
theorem wideDescriptor_binds_advantage_bound (D : DomainSeparatedSponge) (E : WideCommitSpec)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : Adversary (wideDescriptorBreakGame D E))
    (hEff : Eff (wideBreakToFinder D (wideDescriptorToSiteBreak D E A)))
    (hCR : DomainSeparatedCREff D Eff) :
    Negl (gameAdv (wideDescriptorBreakGame D E) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (wideDescriptorBreakGame D E) A l).1)
    (wideDescriptorToSite_adv_le D E A)
    (wideCommit_binds_advantage_bound D Eff (wideDescriptorToSiteBreak D E A) hEff hCR)

/-! ## §5 — `hEff` DISCHARGED at `Eff := IsPolyTime` (no floating efficiency parameter).

Both hops of each reduction are `CostAdversary.Adversary.postMap` instances (pure output reshaping,
the sampled tag passed through), so `CostTactics.poly_time` applies `isPolyTime_postMap` — which
folds in the tight-δ composition AND derives the poly overhead from the forger's OWN bound — leaving
only the output-growth obligation, discharged from §1's proved constants. The one honest modelling
input per hop is its DECLARED instruction count (`cw`/`bw`): a Lean function has no runtime, so that
number can only be CHARGED IN THE PROGRAM'S SYNTAX, never derived. -/

/-- **THE ROW GAMES' ANSWER ENCODING.** A forged pair of rows costs, to write down, the two rows'
DECLARED trace columns and public inputs. Concrete on purpose: the size measure belongs to the GAME,
and leaving it open would let a degenerate `sz := 0` make output free again. -/
def narrowRowAnsSize (D : DomainSeparatedSponge) : AnsSize (narrowSiteBreakGame D) :=
  fun _ _ => 2 * (EFFECT_VM_WIDTH + 42)

/-- The descriptor-level narrow game's encoding — the SAME two rows. -/
def narrowDescriptorAnsSize (D : DomainSeparatedSponge) (E : NarrowCommitSpec) :
    AnsSize (narrowDescriptorBreakGame D E) :=
  fun _ _ => 2 * (E.descriptor.traceWidth + E.descriptor.piCount)

/-- The wide games' encoding — the two rows plus their two eight-wide side-table sub-blocks. -/
def wideRowAnsSize (D : DomainSeparatedSponge) : AnsSize (wideSiteBreakGame D) :=
  fun _ _ => 2 * (EFFECT_VM_WIDTH_SYSROOTS + 42 + N_SYSTEM_ROOTS)

/-- The descriptor-level wide game's encoding. -/
def wideDescriptorAnsSize (D : DomainSeparatedSponge) (E : WideCommitSpec) :
    AnsSize (wideDescriptorBreakGame D E) :=
  fun _ _ => 2 * (E.descriptor.traceWidth + E.descriptor.piCount + N_SYSTEM_ROOTS)

/-- The collision game's encoding — the two claimed sponge preimages. -/
def spongeAnsSize (D : DomainSeparatedSponge) : AnsSize (hashGame (poseidon2KeyedFamily D)) :=
  fun _ p => p.1.length + p.2.length

/-- **⚑ `hEff` DISCHARGED (narrow).** A hash-site-level equivocator that is EFFICIENT at the game's
own answer encoding, put through the GROUP-4 extractor, yields a sponge-collision finder that is
still efficient — so the deployed floor at `Eff := IsPolyTime` applies to it and the equivocator's
advantage is negligible. NO `PolyBoundedNat` hypothesis is taken: the overhead's poly-ness follows
from `hA`. -/
theorem narrowCommit_binds_from_polyTime (D : DomainSeparatedSponge)
    (A : Adversary (narrowSiteBreakGame D))
    (hA : IsPolyTime (narrowRowAnsSize D) A) (cw bw : ℕ)
    (hCR : DomainSeparatedCREff D (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (narrowSiteBreakGame D) A) := by
  have hEff : IsPolyTime (spongeAnsSize D) (narrowBreakToFinder D A) := by
    poly_time (narrowRowAnsSize D) (spongeAnsSize D)
      (fun _ t (c : VmRowEnv × VmRowEnv) => transferCollFind (D.hashAt t) c.1 c.2)
      cw bw 0 8 hA
    intro l t c
    have := transferCollFind_len_le (D.hashAt t) c.1 c.2
    show (transferCollFind (D.hashAt t) c.1 c.2).1.length
        + (transferCollFind (D.hashAt t) c.1 c.2).2.length
      ≤ 0 * (narrowRowAnsSize D l c) + 8
    omega
  exact narrowCommit_binds_advantage_bound D (IsPolyTime (spongeAnsSize D)) A hEff hCR

/-- **⚑ `hEff` DISCHARGED (narrow, descriptor level).** The extra hop is the identity reshaping of
the two rows — its output-growth obligation is the declared row encoding, and the composition stays
poly-time. -/
theorem narrowDescriptor_binds_from_polyTime (D : DomainSeparatedSponge) (E : NarrowCommitSpec)
    (A : Adversary (narrowDescriptorBreakGame D E))
    (hA : IsPolyTime (narrowDescriptorAnsSize D E) A) (cw₀ bw₀ cw bw : ℕ)
    (hsz : 2 * (EFFECT_VM_WIDTH + 42)
      ≤ 2 * (E.descriptor.traceWidth + E.descriptor.piCount))
    (hCR : DomainSeparatedCREff D (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (narrowDescriptorBreakGame D E) A) := by
  have h1 : IsPolyTime (narrowRowAnsSize D) (descriptorToSiteBreak D E A) := by
    poly_time (narrowDescriptorAnsSize D E) (narrowRowAnsSize D)
      (fun _ _ (c : VmRowEnv × VmRowEnv) => c) cw₀ bw₀ 1 0 hA
    intro l t c
    show 2 * (EFFECT_VM_WIDTH + 42)
      ≤ 1 * (narrowDescriptorAnsSize D E l c) + 0
    simpa [narrowDescriptorAnsSize] using hsz
  have hEff : IsPolyTime (spongeAnsSize D)
      (narrowBreakToFinder D (descriptorToSiteBreak D E A)) := by
    poly_time (narrowRowAnsSize D) (spongeAnsSize D)
      (fun _ t (c : VmRowEnv × VmRowEnv) => transferCollFind (D.hashAt t) c.1 c.2)
      cw bw 0 8 h1
    intro l t c
    have := transferCollFind_len_le (D.hashAt t) c.1 c.2
    show (transferCollFind (D.hashAt t) c.1 c.2).1.length
        + (transferCollFind (D.hashAt t) c.1 c.2).2.length
      ≤ 0 * (narrowRowAnsSize D l c) + 8
    omega
  exact narrowDescriptor_binds_advantage_bound D E (IsPolyTime (spongeAnsSize D)) A hEff hCR

/-- **⚑ `hEff` DISCHARGED (wide).** -/
theorem wideCommit_binds_from_polyTime (D : DomainSeparatedSponge)
    (A : Adversary (wideSiteBreakGame D))
    (hA : IsPolyTime (wideRowAnsSize D) A) (cw bw : ℕ)
    (hCR : DomainSeparatedCREff D (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (wideSiteBreakGame D) A) := by
  have hEff : IsPolyTime (spongeAnsSize D) (wideBreakToFinder D A) := by
    poly_time (wideRowAnsSize D) (spongeAnsSize D)
      (fun _ t (c : (VmRowEnv × SysRoots) × (VmRowEnv × SysRoots)) =>
        wideRowFind (D.hashAt t) c.1 c.2)
      cw bw 0 16 hA
    intro l t c
    have := wideRowFind_len_le (D.hashAt t) c.1 c.2
    show (wideRowFind (D.hashAt t) c.1 c.2).1.length
        + (wideRowFind (D.hashAt t) c.1 c.2).2.length
      ≤ 0 * (wideRowAnsSize D l c) + 16
    omega
  exact wideCommit_binds_advantage_bound D (IsPolyTime (spongeAnsSize D)) A hEff hCR

/-- **⚑ `hEff` DISCHARGED (wide, descriptor level).** -/
theorem wideDescriptor_binds_from_polyTime (D : DomainSeparatedSponge) (E : WideCommitSpec)
    (A : Adversary (wideDescriptorBreakGame D E))
    (hA : IsPolyTime (wideDescriptorAnsSize D E) A) (cw₀ bw₀ cw bw : ℕ)
    (hsz : 2 * (EFFECT_VM_WIDTH_SYSROOTS + 42 + N_SYSTEM_ROOTS)
      ≤ 2 * (E.descriptor.traceWidth + E.descriptor.piCount + N_SYSTEM_ROOTS))
    (hCR : DomainSeparatedCREff D (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (wideDescriptorBreakGame D E) A) := by
  have h1 : IsPolyTime (wideRowAnsSize D) (wideDescriptorToSiteBreak D E A) := by
    poly_time (wideDescriptorAnsSize D E) (wideRowAnsSize D)
      (fun _ _ (c : (VmRowEnv × SysRoots) × (VmRowEnv × SysRoots)) => c) cw₀ bw₀ 1 0 hA
    intro l t c
    show 2 * (EFFECT_VM_WIDTH_SYSROOTS + 42 + N_SYSTEM_ROOTS)
      ≤ 1 * (wideDescriptorAnsSize D E l c) + 0
    simpa [wideDescriptorAnsSize] using hsz
  have hEff : IsPolyTime (spongeAnsSize D)
      (wideBreakToFinder D (wideDescriptorToSiteBreak D E A)) := by
    poly_time (wideRowAnsSize D) (spongeAnsSize D)
      (fun _ t (c : (VmRowEnv × SysRoots) × (VmRowEnv × SysRoots)) =>
        wideRowFind (D.hashAt t) c.1 c.2)
      cw bw 0 16 h1
    intro l t c
    have := wideRowFind_len_le (D.hashAt t) c.1 c.2
    show (wideRowFind (D.hashAt t) c.1 c.2).1.length
        + (wideRowFind (D.hashAt t) c.1 c.2).2.length
      ≤ 0 * (wideRowAnsSize D l c) + 16
    omega
  exact wideDescriptor_binds_advantage_bound D E (IsPolyTime (spongeAnsSize D)) A hEff hCR

/-- **(TOOTH — the class the floor is instantiated at is NOT EMPTY.)** The constant finder is in
`IsPolyTime (spongeAnsSize D)`, because the answer it writes has size `0` under the game's own
encoding. Together with `CostAdversary.bruteForce_not_polyTime` (the ⊤-collapse witness is excluded)
this pins the instantiated floor strictly between the two poles. -/
theorem spongeFloor_isPolyTime_inhabited (D : DomainSeparatedSponge) :
    IsPolyTime (spongeAnsSize D)
      (Dregg2.Crypto.CostAdversary.idAdv (O := Unit) (Q := fun _ => Unit) (R := fun _ => Unit)
        (fun _ _ => (([] : List ℤ), ([] : List ℤ)))).toAdversary :=
  Dregg2.Crypto.CostAdversary.isPolyTime_inhabited _ _
    ⟨0, 0, fun _ _ => by simp [spongeAnsSize]⟩

/-! ## §6 — the floor's TWO POLES, and the CANARIES.

Both poles are `Circuit.DomainSeparatedCREffRegrounded`'s, re-exported here so a reader of any
per-effect site can price its instantiation exactly without leaving the reduction. -/

/-- **⚑ THE ⊤ POLE — the floor is FALSE at the REAL BabyBear parameters** (the honest price of
`hEff`). What the reduction buys is not a floor the deployed sponge satisfies at ⊤ — no such floor
exists — it is that the residual is ONE named parameter with both poles proved, in place of an
unclosed disjunction whose right branch is unconditionally available. -/
theorem commitFloor_top_false_babyBear (D : DomainSeparatedSponge)
    (hb : ∀ xs, 0 ≤ D.sponge xs ∧ D.sponge xs < babyBearP) :
    ¬ DomainSeparatedCREff D (fun _ => True) :=
  effFloor_top_false_babyBear D hb

/-- **THE ⊥ POLE — vacuous.** Recorded so the floor's satisfiability cannot be mistaken for
evidence. -/
theorem commitFloor_bot_vacuous (D : DomainSeparatedSponge) :
    DomainSeparatedCREff D (fun _ => False) :=
  effFloor_bot_vacuous D

/-- **(CANARY — the keystone does NOT follow from the floor applied at ANOTHER finder.)** Strip the
reduction: try to conclude the narrow equivocator's negligibility from the sponge floor applied at
some OTHER finder `B`, not the one EXTRACTED from it. It does not go through — only `narrow_adv_le`
connects the extracted finder to the row game. This tooth reds if a future edit reconnects them. -/
example (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : Adversary (narrowSiteBreakGame D))
    (B : Adversary (hashGame (poseidon2KeyedFamily D))) (hB : Eff B)
    (hCR : DomainSeparatedCREff D Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (narrowSiteBreakGame D) A) := hCR B hB)
  trivial

/-- **(CANARY — the wide keystone likewise.)** -/
example (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : Adversary (wideSiteBreakGame D))
    (B : Adversary (hashGame (poseidon2KeyedFamily D))) (hB : Eff B)
    (hCR : DomainSeparatedCREff D Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (wideSiteBreakGame D) A) := hCR B hB)
  trivial

/-- **THE POSITIVE POLE — the RIGHT floor DOES discharge it.** A gate that refuses everything is a
broken keystone, not a fixed one: with the collision floor at the EXTRACTED finder, the narrow row
binding fires. -/
theorem the_reduced_narrow_bound_fires (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : Adversary (narrowSiteBreakGame D))
    (hEff : Eff (narrowBreakToFinder D A))
    (hCR : DomainSeparatedCREff D Eff) :
    Negl (gameAdv (narrowSiteBreakGame D) A) :=
  narrowCommit_binds_advantage_bound D Eff A hEff hCR

/-- **THE POSITIVE POLE for the wide leg.** -/
theorem the_reduced_wide_bound_fires (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : Adversary (wideSiteBreakGame D))
    (hEff : Eff (wideBreakToFinder D A))
    (hCR : DomainSeparatedCREff D Eff) :
    Negl (gameAdv (wideSiteBreakGame D) A) :=
  wideCommit_binds_advantage_bound D Eff A hEff hCR

#assert_all_clean [
  group4Find_len_le,
  transferCollFind_len_le,
  wideRowFind_len_le,
  narrowSiteBreakGame_wins_iff,
  narrow_wins_imp,
  narrow_adv_le,
  narrowCommit_binds_advantage_bound,
  narrowDescriptorBreakGame_wins_iff,
  descriptorToSite_wins_imp,
  descriptorToSite_adv_le,
  narrowDescriptor_binds_advantage_bound,
  wideSiteBreakGame_wins_iff,
  wide_wins_imp,
  wide_adv_le,
  wideCommit_binds_advantage_bound,
  wideDescriptorBreakGame_wins_iff,
  wideDescriptorToSite_wins_imp,
  wideDescriptorToSite_adv_le,
  wideDescriptor_binds_advantage_bound,
  narrowCommit_binds_from_polyTime,
  narrowDescriptor_binds_from_polyTime,
  wideCommit_binds_from_polyTime,
  wideDescriptor_binds_from_polyTime,
  spongeFloor_isPolyTime_inhabited,
  commitFloor_top_false_babyBear,
  commitFloor_bot_vacuous,
  the_reduced_narrow_bound_fires,
  the_reduced_wide_bound_fires
]


/-! ## §7 — THE TWELVE DEPLOYED EFFECT SITES, INSTANTIATED.

Each effect below gets exactly three things and nothing else:

  * a FORGERY-IS-BREAK theorem, which is where the per-effect content lives — it says the effect's
    OWN emitted descriptor / hash sites make its rows answers of the forgery game (so the game is
    about the circuit the prover runs, not an idealised stand-in);
  * the SECURITY REDUCTION at that game, replacing the retired bare disjunction as the headline;
  * the `IsPolyTime` discharge of `hEff`.

For the descriptor-level narrow sites the per-effect content also includes the `pinsNewCommit` field
— the `boundaryLastPins` step that turns a shared published `NEW_COMMIT` into a shared `state_commit`
COLUMN — carried VERBATIM from the theorem it replaces. -/

/-! ### §7.1 — the NARROW hash-site bindings. -/

/-- **⚑ A cellDestroy ROW EQUIVOCATION IS A GAME WIN.** cellDestroy absorbs the DEPLOYED GROUP-4 hash sites
(`cellDestroyHashSites = transferHashSites`), so two cellDestroy rows whose sites hold at the sampled tag, publishing
the SAME `state_commit` column while DISAGREEING on an absorbed state-block column, ARE literally an
answer that wins `narrowSiteBreakGame`. This is what ties the game to the row the prover runs. -/
theorem cellDestroyVm_row_forgery_is_break (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll (D.hashAt t) e₁ EffectVmEmitCellDestroy.cellDestroyHashSites)
    (hs₂ : siteHoldsAll (D.hashAt t) e₂ EffectVmEmitCellDestroy.cellDestroyHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT))
    (hne : absorbedCols e₁ ≠ absorbedCols e₂) :
    (narrowSiteBreakGame D).wins l t (e₁, e₂) :=
  ⟨hs₁, hs₂, hcommit, hne⟩

/-- **⚑ THE cellDestroy STATE-BLOCK BINDING — a SECURITY REDUCTION** (replaces the DELETED
`cellDestroyVm_commit_binds_block_or_collides`). Under the deployed sponge's collision floor at `Eff`, an
adversary producing a cellDestroy row equivocation has NEGLIGIBLE advantage, provided the finder
EXTRACTED from it (the GROUP-4 trace `transferCollFind`) is in the class. -/
theorem cellDestroy_commit_binds_block_advantage_bound (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : Adversary (narrowSiteBreakGame D))
    (hEff : Eff (narrowBreakToFinder D A))
    (hCR : DomainSeparatedCREff D Eff) :
    Negl (gameAdv (narrowSiteBreakGame D) A) :=
  narrowCommit_binds_advantage_bound D Eff A hEff hCR

/-- **⚑ `hEff` DISCHARGED for the cellDestroy row binding** (`Eff := IsPolyTime`). -/
theorem cellDestroy_commit_binds_block_from_polyTime (D : DomainSeparatedSponge)
    (A : Adversary (narrowSiteBreakGame D))
    (hA : IsPolyTime (narrowRowAnsSize D) A) (cw bw : ℕ)
    (hCR : DomainSeparatedCREff D (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (narrowSiteBreakGame D) A) :=
  narrowCommit_binds_from_polyTime D A hA cw bw hCR

/-- **⚑ A makeSovereign ROW EQUIVOCATION IS A GAME WIN.** makeSovereign absorbs the DEPLOYED GROUP-4 hash sites
(`makeSovereignHashSites = transferHashSites`), so two makeSovereign rows whose sites hold at the sampled tag, publishing
the SAME `state_commit` column while DISAGREEING on an absorbed state-block column, ARE literally an
answer that wins `narrowSiteBreakGame`. This is what ties the game to the row the prover runs. -/
theorem makeSovereignVm_row_forgery_is_break (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll (D.hashAt t) e₁ EffectVmEmitMakeSovereign.makeSovereignHashSites)
    (hs₂ : siteHoldsAll (D.hashAt t) e₂ EffectVmEmitMakeSovereign.makeSovereignHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT))
    (hne : absorbedCols e₁ ≠ absorbedCols e₂) :
    (narrowSiteBreakGame D).wins l t (e₁, e₂) :=
  ⟨hs₁, hs₂, hcommit, hne⟩

/-- **⚑ THE makeSovereign STATE-BLOCK BINDING — a SECURITY REDUCTION** (replaces the DELETED
`makeSovereignVm_commit_binds_block_or_collides`). Under the deployed sponge's collision floor at `Eff`, an
adversary producing a makeSovereign row equivocation has NEGLIGIBLE advantage, provided the finder
EXTRACTED from it (the GROUP-4 trace `transferCollFind`) is in the class. -/
theorem makeSovereign_commit_binds_block_advantage_bound (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : Adversary (narrowSiteBreakGame D))
    (hEff : Eff (narrowBreakToFinder D A))
    (hCR : DomainSeparatedCREff D Eff) :
    Negl (gameAdv (narrowSiteBreakGame D) A) :=
  narrowCommit_binds_advantage_bound D Eff A hEff hCR

/-- **⚑ `hEff` DISCHARGED for the makeSovereign row binding** (`Eff := IsPolyTime`). -/
theorem makeSovereign_commit_binds_block_from_polyTime (D : DomainSeparatedSponge)
    (A : Adversary (narrowSiteBreakGame D))
    (hA : IsPolyTime (narrowRowAnsSize D) A) (cw bw : ℕ)
    (hCR : DomainSeparatedCREff D (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (narrowSiteBreakGame D) A) :=
  narrowCommit_binds_from_polyTime D A hA cw bw hCR

/-- **⚑ A exercise ROW EQUIVOCATION IS A GAME WIN.** exercise absorbs the DEPLOYED GROUP-4 hash sites
(`exerciseHashSites = transferHashSites`), so two exercise rows whose sites hold at the sampled tag, publishing
the SAME `state_commit` column while DISAGREEING on an absorbed state-block column, ARE literally an
answer that wins `narrowSiteBreakGame`. This is what ties the game to the row the prover runs. -/
theorem exerciseVm_row_forgery_is_break (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll (D.hashAt t) e₁ EffectVmEmitExercise.exerciseHashSites)
    (hs₂ : siteHoldsAll (D.hashAt t) e₂ EffectVmEmitExercise.exerciseHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT))
    (hne : absorbedCols e₁ ≠ absorbedCols e₂) :
    (narrowSiteBreakGame D).wins l t (e₁, e₂) :=
  ⟨hs₁, hs₂, hcommit, hne⟩

/-- **⚑ THE exercise STATE-BLOCK BINDING — a SECURITY REDUCTION** (replaces the DELETED
`exerciseVm_commit_binds_block_or_collides`). Under the deployed sponge's collision floor at `Eff`, an
adversary producing a exercise row equivocation has NEGLIGIBLE advantage, provided the finder
EXTRACTED from it (the GROUP-4 trace `transferCollFind`) is in the class. -/
theorem exercise_commit_binds_block_advantage_bound (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : Adversary (narrowSiteBreakGame D))
    (hEff : Eff (narrowBreakToFinder D A))
    (hCR : DomainSeparatedCREff D Eff) :
    Negl (gameAdv (narrowSiteBreakGame D) A) :=
  narrowCommit_binds_advantage_bound D Eff A hEff hCR

/-- **⚑ `hEff` DISCHARGED for the exercise row binding** (`Eff := IsPolyTime`). -/
theorem exercise_commit_binds_block_from_polyTime (D : DomainSeparatedSponge)
    (A : Adversary (narrowSiteBreakGame D))
    (hA : IsPolyTime (narrowRowAnsSize D) A) (cw bw : ℕ)
    (hCR : DomainSeparatedCREff D (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (narrowSiteBreakGame D) A) :=
  narrowCommit_binds_from_polyTime D A hA cw bw hCR

/-- **⚑ A receiptArchive ROW EQUIVOCATION IS A GAME WIN.** receiptArchive absorbs the DEPLOYED GROUP-4 hash sites
(`archiveHashSites = transferHashSites`), so two receiptArchive rows whose sites hold at the sampled tag, publishing
the SAME `state_commit` column while DISAGREEING on an absorbed state-block column, ARE literally an
answer that wins `narrowSiteBreakGame`. This is what ties the game to the row the prover runs. -/
theorem archiveVm_row_forgery_is_break (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll (D.hashAt t) e₁ EffectVmEmitReceiptArchive.archiveHashSites)
    (hs₂ : siteHoldsAll (D.hashAt t) e₂ EffectVmEmitReceiptArchive.archiveHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT))
    (hne : absorbedCols e₁ ≠ absorbedCols e₂) :
    (narrowSiteBreakGame D).wins l t (e₁, e₂) :=
  ⟨hs₁, hs₂, hcommit, hne⟩

/-- **⚑ THE receiptArchive STATE-BLOCK BINDING — a SECURITY REDUCTION** (replaces the DELETED
`archiveDescriptor_commit_binds_state_or_collides`). Under the deployed sponge's collision floor at `Eff`, an
adversary producing a receiptArchive row equivocation has NEGLIGIBLE advantage, provided the finder
EXTRACTED from it (the GROUP-4 trace `transferCollFind`) is in the class. -/
theorem archive_commit_binds_block_advantage_bound (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : Adversary (narrowSiteBreakGame D))
    (hEff : Eff (narrowBreakToFinder D A))
    (hCR : DomainSeparatedCREff D Eff) :
    Negl (gameAdv (narrowSiteBreakGame D) A) :=
  narrowCommit_binds_advantage_bound D Eff A hEff hCR

/-- **⚑ `hEff` DISCHARGED for the receiptArchive row binding** (`Eff := IsPolyTime`). -/
theorem archive_commit_binds_block_from_polyTime (D : DomainSeparatedSponge)
    (A : Adversary (narrowSiteBreakGame D))
    (hA : IsPolyTime (narrowRowAnsSize D) A) (cw bw : ℕ)
    (hCR : DomainSeparatedCREff D (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (narrowSiteBreakGame D) A) :=
  narrowCommit_binds_from_polyTime D A hA cw bw hCR

/-- **⚑ A pipelinedSend ROW EQUIVOCATION IS A GAME WIN.** pipelinedSend absorbs the DEPLOYED GROUP-4 hash sites
(`pipelinedSendHashSites = transferHashSites`), so two pipelinedSend rows whose sites hold at the sampled tag, publishing
the SAME `state_commit` column while DISAGREEING on an absorbed state-block column, ARE literally an
answer that wins `narrowSiteBreakGame`. This is what ties the game to the row the prover runs. -/
theorem pipelinedSendVm_row_forgery_is_break (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll (D.hashAt t) e₁ EffectVmEmitPipelinedSend.pipelinedSendHashSites)
    (hs₂ : siteHoldsAll (D.hashAt t) e₂ EffectVmEmitPipelinedSend.pipelinedSendHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT))
    (hne : absorbedCols e₁ ≠ absorbedCols e₂) :
    (narrowSiteBreakGame D).wins l t (e₁, e₂) :=
  ⟨hs₁, hs₂, hcommit, hne⟩

/-- **⚑ THE pipelinedSend STATE-BLOCK BINDING — a SECURITY REDUCTION** (replaces the DELETED
`pipelinedSendVm_commit_binds_block_or_collides`). Under the deployed sponge's collision floor at `Eff`, an
adversary producing a pipelinedSend row equivocation has NEGLIGIBLE advantage, provided the finder
EXTRACTED from it (the GROUP-4 trace `transferCollFind`) is in the class. -/
theorem pipelinedSend_commit_binds_block_advantage_bound (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : Adversary (narrowSiteBreakGame D))
    (hEff : Eff (narrowBreakToFinder D A))
    (hCR : DomainSeparatedCREff D Eff) :
    Negl (gameAdv (narrowSiteBreakGame D) A) :=
  narrowCommit_binds_advantage_bound D Eff A hEff hCR

/-- **⚑ `hEff` DISCHARGED for the pipelinedSend row binding** (`Eff := IsPolyTime`). -/
theorem pipelinedSend_commit_binds_block_from_polyTime (D : DomainSeparatedSponge)
    (A : Adversary (narrowSiteBreakGame D))
    (hA : IsPolyTime (narrowRowAnsSize D) A) (cw bw : ℕ)
    (hCR : DomainSeparatedCREff D (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (narrowSiteBreakGame D) A) :=
  narrowCommit_binds_from_polyTime D A hA cw bw hCR

/-- **⚑ A refusal ROW EQUIVOCATION IS A GAME WIN.** refusal absorbs the DEPLOYED GROUP-4 hash sites
(`refusalHashSites = transferHashSites`), so two refusal rows whose sites hold at the sampled tag, publishing
the SAME `state_commit` column while DISAGREEING on an absorbed state-block column, ARE literally an
answer that wins `narrowSiteBreakGame`. This is what ties the game to the row the prover runs. -/
theorem refusalVm_row_forgery_is_break (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll (D.hashAt t) e₁ EffectVmEmitRefusal.refusalHashSites)
    (hs₂ : siteHoldsAll (D.hashAt t) e₂ EffectVmEmitRefusal.refusalHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT))
    (hne : absorbedCols e₁ ≠ absorbedCols e₂) :
    (narrowSiteBreakGame D).wins l t (e₁, e₂) :=
  ⟨hs₁, hs₂, hcommit, hne⟩

/-- **⚑ THE refusal STATE-BLOCK BINDING — a SECURITY REDUCTION** (replaces the DELETED
`refusalVm_commit_binds_block_or_collides`). Under the deployed sponge's collision floor at `Eff`, an
adversary producing a refusal row equivocation has NEGLIGIBLE advantage, provided the finder
EXTRACTED from it (the GROUP-4 trace `transferCollFind`) is in the class. -/
theorem refusal_commit_binds_block_advantage_bound (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : Adversary (narrowSiteBreakGame D))
    (hEff : Eff (narrowBreakToFinder D A))
    (hCR : DomainSeparatedCREff D Eff) :
    Negl (gameAdv (narrowSiteBreakGame D) A) :=
  narrowCommit_binds_advantage_bound D Eff A hEff hCR

/-- **⚑ `hEff` DISCHARGED for the refusal row binding** (`Eff := IsPolyTime`). -/
theorem refusal_commit_binds_block_from_polyTime (D : DomainSeparatedSponge)
    (A : Adversary (narrowSiteBreakGame D))
    (hA : IsPolyTime (narrowRowAnsSize D) A) (cw bw : ℕ)
    (hCR : DomainSeparatedCREff D (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (narrowSiteBreakGame D) A) :=
  narrowCommit_binds_from_polyTime D A hA cw bw hCR

/-! ### §7.2 — the NARROW DESCRIPTOR bindings (the circuit the prover runs). -/

/-- **⚑ cellDestroy's PER-EFFECT OBLIGATION, NAMED.** cellDestroy's emitted descriptor rides the deployed
GROUP-4 sites, and a satisfying row's after-state `state_commit` column IS its published `NEW_COMMIT`
mod the deployed prime — the descriptor's own `boundaryLastPins`. This bundle carries VERBATIM the
content the DELETED `cellDestroyDescriptor_commit_binds_state_or_collides` carried (its `hc`/`hcm` step), now as
data a reduction consumes rather than as a disjunction. -/
def cellDestroyNarrowSpec : NarrowCommitSpec where
  descriptor := EffectVmEmitCellDestroy.cellDestroyVmDescriptor
  usesTransferSites := rfl
  pinsNewCommit := by
    intro hash e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ (EffectVmEmitCellDestroy.cellDestroyVmDescriptor).constraints := by
        unfold EffectVmEmitCellDestroy.cellDestroyVmDescriptor
        simp only [List.mem_append]
        exact Or.inl (Or.inr hc)
      have hh := hcs c hmem
      unfold boundaryLastPins at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        · simp only [VmConstraint.holdsVm] at hh ⊢
          exact hh
    exact (boundaryLast_pins e hlast).1

/-- **⚑ A SATISFYING cellDestroy DESCRIPTOR EQUIVOCATION IS A GAME WIN.** Two rows satisfying the EMITTED
cellDestroy descriptor, with canonical commit columns, publishing the SAME `NEW_COMMIT` while DISAGREEING
on an absorbed state column, ARE an answer that wins `narrowDescriptorBreakGame` at cellDestroy's own
spec. A win is a GHOST post-state accepted by the circuit the prover runs. -/
theorem cellDestroyDescriptor_forgery_is_break (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv)
    (hc₁ : 0 ≤ e₁.loc (saCol state.STATE_COMMIT) ∧ e₁.loc (saCol state.STATE_COMMIT) < babyBearP)
    (hc₂ : 0 ≤ e₂.loc (saCol state.STATE_COMMIT) ∧ e₂.loc (saCol state.STATE_COMMIT) < babyBearP)
    (hsat₁ : satisfiedVm (D.hashAt t) EffectVmEmitCellDestroy.cellDestroyVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm (D.hashAt t) EffectVmEmitCellDestroy.cellDestroyVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hne : absorbedCols e₁ ≠ absorbedCols e₂) :
    (narrowDescriptorBreakGame D cellDestroyNarrowSpec).wins l t (e₁, e₂) :=
  ⟨hsat₁, hsat₂, hc₁, hc₂, hpub, hne⟩

/-- **⚑ THE cellDestroy DESCRIPTOR STATE BINDING — a SECURITY REDUCTION** (replaces the DELETED
`cellDestroyDescriptor_commit_binds_state_or_collides`). The chain is: descriptor forger → (`descriptorToSiteBreak`,
using cellDestroy's `boundaryLastPins`) row equivocator → (`narrowBreakToFinder`, the GROUP-4 trace) a
genuine collision of the deployed sponge. -/
theorem cellDestroyDescriptor_commit_binds_state_advantage_bound (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : Adversary (narrowDescriptorBreakGame D cellDestroyNarrowSpec))
    (hEff : Eff (narrowBreakToFinder D (descriptorToSiteBreak D cellDestroyNarrowSpec A)))
    (hCR : DomainSeparatedCREff D Eff) :
    Negl (gameAdv (narrowDescriptorBreakGame D cellDestroyNarrowSpec) A) :=
  narrowDescriptor_binds_advantage_bound D cellDestroyNarrowSpec Eff A hEff hCR

/-- **⚑ `hEff` DISCHARGED for the cellDestroy descriptor binding** (`Eff := IsPolyTime`). -/
theorem cellDestroyDescriptor_commit_binds_state_from_polyTime (D : DomainSeparatedSponge)
    (A : Adversary (narrowDescriptorBreakGame D cellDestroyNarrowSpec))
    (hA : IsPolyTime (narrowDescriptorAnsSize D cellDestroyNarrowSpec) A) (cw₀ bw₀ cw bw : ℕ)
    (hCR : DomainSeparatedCREff D (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (narrowDescriptorBreakGame D cellDestroyNarrowSpec) A) :=
  narrowDescriptor_binds_from_polyTime D cellDestroyNarrowSpec A hA cw₀ bw₀ cw bw (Nat.le_refl _) hCR

/-- **⚑ incrementNonce's PER-EFFECT OBLIGATION, NAMED.** incrementNonce's emitted descriptor rides the deployed
GROUP-4 sites, and a satisfying row's after-state `state_commit` column IS its published `NEW_COMMIT`
mod the deployed prime — the descriptor's own `boundaryLastPins`. This bundle carries VERBATIM the
content the DELETED `incNonceDescriptor_commit_binds_state_or_collides` carried (its `hc`/`hcm` step), now as
data a reduction consumes rather than as a disjunction. -/
def incNonceNarrowSpec : NarrowCommitSpec where
  descriptor := EffectVmEmitIncrementNonce.incrementNonceVmDescriptor
  usesTransferSites := rfl
  pinsNewCommit := by
    intro hash e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hmem : (VmConstraint.piBinding .last (saCol state.STATE_COMMIT) pi.NEW_COMMIT)
        ∈ (EffectVmEmitIncrementNonce.incrementNonceVmDescriptor).constraints := by
      unfold EffectVmEmitIncrementNonce.incrementNonceVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inr (by simp [boundaryLastPins]))
    simpa [VmConstraint.holdsVm] using hcs _ hmem

/-- **⚑ A SATISFYING incrementNonce DESCRIPTOR EQUIVOCATION IS A GAME WIN.** Two rows satisfying the EMITTED
incrementNonce descriptor, with canonical commit columns, publishing the SAME `NEW_COMMIT` while DISAGREEING
on an absorbed state column, ARE an answer that wins `narrowDescriptorBreakGame` at incrementNonce's own
spec. A win is a GHOST post-state accepted by the circuit the prover runs. -/
theorem incNonceDescriptor_forgery_is_break (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv)
    (hc₁ : 0 ≤ e₁.loc (saCol state.STATE_COMMIT) ∧ e₁.loc (saCol state.STATE_COMMIT) < babyBearP)
    (hc₂ : 0 ≤ e₂.loc (saCol state.STATE_COMMIT) ∧ e₂.loc (saCol state.STATE_COMMIT) < babyBearP)
    (hsat₁ : satisfiedVm (D.hashAt t) EffectVmEmitIncrementNonce.incrementNonceVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm (D.hashAt t) EffectVmEmitIncrementNonce.incrementNonceVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hne : absorbedCols e₁ ≠ absorbedCols e₂) :
    (narrowDescriptorBreakGame D incNonceNarrowSpec).wins l t (e₁, e₂) :=
  ⟨hsat₁, hsat₂, hc₁, hc₂, hpub, hne⟩

/-- **⚑ THE incrementNonce DESCRIPTOR STATE BINDING — a SECURITY REDUCTION** (replaces the DELETED
`incNonceDescriptor_commit_binds_state_or_collides`). The chain is: descriptor forger → (`descriptorToSiteBreak`,
using incrementNonce's `boundaryLastPins`) row equivocator → (`narrowBreakToFinder`, the GROUP-4 trace) a
genuine collision of the deployed sponge. -/
theorem incNonceDescriptor_commit_binds_state_advantage_bound (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : Adversary (narrowDescriptorBreakGame D incNonceNarrowSpec))
    (hEff : Eff (narrowBreakToFinder D (descriptorToSiteBreak D incNonceNarrowSpec A)))
    (hCR : DomainSeparatedCREff D Eff) :
    Negl (gameAdv (narrowDescriptorBreakGame D incNonceNarrowSpec) A) :=
  narrowDescriptor_binds_advantage_bound D incNonceNarrowSpec Eff A hEff hCR

/-- **⚑ `hEff` DISCHARGED for the incrementNonce descriptor binding** (`Eff := IsPolyTime`). -/
theorem incNonceDescriptor_commit_binds_state_from_polyTime (D : DomainSeparatedSponge)
    (A : Adversary (narrowDescriptorBreakGame D incNonceNarrowSpec))
    (hA : IsPolyTime (narrowDescriptorAnsSize D incNonceNarrowSpec) A) (cw₀ bw₀ cw bw : ℕ)
    (hCR : DomainSeparatedCREff D (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (narrowDescriptorBreakGame D incNonceNarrowSpec) A) :=
  narrowDescriptor_binds_from_polyTime D incNonceNarrowSpec A hA cw₀ bw₀ cw bw (Nat.le_refl _) hCR

/-- **⚑ exercise's PER-EFFECT OBLIGATION, NAMED.** exercise's emitted descriptor rides the deployed
GROUP-4 sites, and a satisfying row's after-state `state_commit` column IS its published `NEW_COMMIT`
mod the deployed prime — the descriptor's own `boundaryLastPins`. This bundle carries VERBATIM the
content the DELETED `exerciseDescriptor_commit_binds_state_or_collides` carried (its `hc`/`hcm` step), now as
data a reduction consumes rather than as a disjunction. -/
def exerciseNarrowSpec : NarrowCommitSpec where
  descriptor := EffectVmEmitExercise.exerciseVmDescriptor
  usesTransferSites := rfl
  pinsNewCommit := by
    intro hash e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ (EffectVmEmitExercise.exerciseVmDescriptor).constraints := by
        unfold EffectVmEmitExercise.exerciseVmDescriptor
        simp only [List.mem_append]
        exact Or.inl (Or.inr hc)
      have hh := hcs c hmem
      unfold boundaryLastPins at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        · simp only [VmConstraint.holdsVm] at hh ⊢
          exact hh
    exact (boundaryLast_pins e hlast).1

/-- **⚑ A SATISFYING exercise DESCRIPTOR EQUIVOCATION IS A GAME WIN.** Two rows satisfying the EMITTED
exercise descriptor, with canonical commit columns, publishing the SAME `NEW_COMMIT` while DISAGREEING
on an absorbed state column, ARE an answer that wins `narrowDescriptorBreakGame` at exercise's own
spec. A win is a GHOST post-state accepted by the circuit the prover runs. -/
theorem exerciseDescriptor_forgery_is_break (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv)
    (hc₁ : 0 ≤ e₁.loc (saCol state.STATE_COMMIT) ∧ e₁.loc (saCol state.STATE_COMMIT) < babyBearP)
    (hc₂ : 0 ≤ e₂.loc (saCol state.STATE_COMMIT) ∧ e₂.loc (saCol state.STATE_COMMIT) < babyBearP)
    (hsat₁ : satisfiedVm (D.hashAt t) EffectVmEmitExercise.exerciseVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm (D.hashAt t) EffectVmEmitExercise.exerciseVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hne : absorbedCols e₁ ≠ absorbedCols e₂) :
    (narrowDescriptorBreakGame D exerciseNarrowSpec).wins l t (e₁, e₂) :=
  ⟨hsat₁, hsat₂, hc₁, hc₂, hpub, hne⟩

/-- **⚑ THE exercise DESCRIPTOR STATE BINDING — a SECURITY REDUCTION** (replaces the DELETED
`exerciseDescriptor_commit_binds_state_or_collides`). The chain is: descriptor forger → (`descriptorToSiteBreak`,
using exercise's `boundaryLastPins`) row equivocator → (`narrowBreakToFinder`, the GROUP-4 trace) a
genuine collision of the deployed sponge. -/
theorem exerciseDescriptor_commit_binds_state_advantage_bound (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : Adversary (narrowDescriptorBreakGame D exerciseNarrowSpec))
    (hEff : Eff (narrowBreakToFinder D (descriptorToSiteBreak D exerciseNarrowSpec A)))
    (hCR : DomainSeparatedCREff D Eff) :
    Negl (gameAdv (narrowDescriptorBreakGame D exerciseNarrowSpec) A) :=
  narrowDescriptor_binds_advantage_bound D exerciseNarrowSpec Eff A hEff hCR

/-- **⚑ `hEff` DISCHARGED for the exercise descriptor binding** (`Eff := IsPolyTime`). -/
theorem exerciseDescriptor_commit_binds_state_from_polyTime (D : DomainSeparatedSponge)
    (A : Adversary (narrowDescriptorBreakGame D exerciseNarrowSpec))
    (hA : IsPolyTime (narrowDescriptorAnsSize D exerciseNarrowSpec) A) (cw₀ bw₀ cw bw : ℕ)
    (hCR : DomainSeparatedCREff D (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (narrowDescriptorBreakGame D exerciseNarrowSpec) A) :=
  narrowDescriptor_binds_from_polyTime D exerciseNarrowSpec A hA cw₀ bw₀ cw bw (Nat.le_refl _) hCR

/-- **⚑ emitEvent's PER-EFFECT OBLIGATION, NAMED.** emitEvent's emitted descriptor rides the deployed
GROUP-4 sites, and a satisfying row's after-state `state_commit` column IS its published `NEW_COMMIT`
mod the deployed prime — the descriptor's own `boundaryLastPins`. This bundle carries VERBATIM the
content the DELETED `emitEventDescriptor_commit_binds_state_or_collides` carried (its `hc`/`hcm` step), now as
data a reduction consumes rather than as a disjunction. -/
def emitEventNarrowSpec : NarrowCommitSpec where
  descriptor := EffectVmEmitEmitEvent.emitEventVmDescriptor
  usesTransferSites := rfl
  pinsNewCommit := by
    intro hash e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ (EffectVmEmitEmitEvent.emitEventVmDescriptor).constraints := by
        unfold EffectVmEmitEmitEvent.emitEventVmDescriptor
        simp only [List.mem_append]
        exact Or.inl (Or.inr hc)
      have hh := hcs c hmem
      unfold boundaryLastPins at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        · simp only [VmConstraint.holdsVm] at hh ⊢
          exact hh
    exact (boundaryLast_pins e hlast).1

/-- **⚑ A SATISFYING emitEvent DESCRIPTOR EQUIVOCATION IS A GAME WIN.** Two rows satisfying the EMITTED
emitEvent descriptor, with canonical commit columns, publishing the SAME `NEW_COMMIT` while DISAGREEING
on an absorbed state column, ARE an answer that wins `narrowDescriptorBreakGame` at emitEvent's own
spec. A win is a GHOST post-state accepted by the circuit the prover runs. -/
theorem emitEventDescriptor_forgery_is_break (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv)
    (hc₁ : 0 ≤ e₁.loc (saCol state.STATE_COMMIT) ∧ e₁.loc (saCol state.STATE_COMMIT) < babyBearP)
    (hc₂ : 0 ≤ e₂.loc (saCol state.STATE_COMMIT) ∧ e₂.loc (saCol state.STATE_COMMIT) < babyBearP)
    (hsat₁ : satisfiedVm (D.hashAt t) EffectVmEmitEmitEvent.emitEventVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm (D.hashAt t) EffectVmEmitEmitEvent.emitEventVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hne : absorbedCols e₁ ≠ absorbedCols e₂) :
    (narrowDescriptorBreakGame D emitEventNarrowSpec).wins l t (e₁, e₂) :=
  ⟨hsat₁, hsat₂, hc₁, hc₂, hpub, hne⟩

/-- **⚑ THE emitEvent DESCRIPTOR STATE BINDING — a SECURITY REDUCTION** (replaces the DELETED
`emitEventDescriptor_commit_binds_state_or_collides`). The chain is: descriptor forger → (`descriptorToSiteBreak`,
using emitEvent's `boundaryLastPins`) row equivocator → (`narrowBreakToFinder`, the GROUP-4 trace) a
genuine collision of the deployed sponge. -/
theorem emitEventDescriptor_commit_binds_state_advantage_bound (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : Adversary (narrowDescriptorBreakGame D emitEventNarrowSpec))
    (hEff : Eff (narrowBreakToFinder D (descriptorToSiteBreak D emitEventNarrowSpec A)))
    (hCR : DomainSeparatedCREff D Eff) :
    Negl (gameAdv (narrowDescriptorBreakGame D emitEventNarrowSpec) A) :=
  narrowDescriptor_binds_advantage_bound D emitEventNarrowSpec Eff A hEff hCR

/-- **⚑ `hEff` DISCHARGED for the emitEvent descriptor binding** (`Eff := IsPolyTime`). -/
theorem emitEventDescriptor_commit_binds_state_from_polyTime (D : DomainSeparatedSponge)
    (A : Adversary (narrowDescriptorBreakGame D emitEventNarrowSpec))
    (hA : IsPolyTime (narrowDescriptorAnsSize D emitEventNarrowSpec) A) (cw₀ bw₀ cw bw : ℕ)
    (hCR : DomainSeparatedCREff D (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (narrowDescriptorBreakGame D emitEventNarrowSpec) A) :=
  narrowDescriptor_binds_from_polyTime D emitEventNarrowSpec A hA cw₀ bw₀ cw bw (Nat.le_refl _) hCR

/-- **⚑ pipelinedSend's PER-EFFECT OBLIGATION, NAMED.** pipelinedSend's emitted descriptor rides the deployed
GROUP-4 sites, and a satisfying row's after-state `state_commit` column IS its published `NEW_COMMIT`
mod the deployed prime — the descriptor's own `boundaryLastPins`. This bundle carries VERBATIM the
content the DELETED `pipelinedSendDescriptor_commit_binds_state_or_collides` carried (its `hc`/`hcm` step), now as
data a reduction consumes rather than as a disjunction. -/
def pipelinedSendNarrowSpec : NarrowCommitSpec where
  descriptor := EffectVmEmitPipelinedSend.pipelinedSendVmDescriptor
  usesTransferSites := rfl
  pinsNewCommit := by
    intro hash e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ (EffectVmEmitPipelinedSend.pipelinedSendVmDescriptor).constraints := by
        unfold EffectVmEmitPipelinedSend.pipelinedSendVmDescriptor
        simp only [List.mem_append]
        exact Or.inl (Or.inr hc)
      have hh := hcs c hmem
      unfold boundaryLastPins at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        · simp only [VmConstraint.holdsVm] at hh ⊢
          exact hh
    exact (boundaryLast_pins e hlast).1

/-- **⚑ A SATISFYING pipelinedSend DESCRIPTOR EQUIVOCATION IS A GAME WIN.** Two rows satisfying the EMITTED
pipelinedSend descriptor, with canonical commit columns, publishing the SAME `NEW_COMMIT` while DISAGREEING
on an absorbed state column, ARE an answer that wins `narrowDescriptorBreakGame` at pipelinedSend's own
spec. A win is a GHOST post-state accepted by the circuit the prover runs. -/
theorem pipelinedSendDescriptor_forgery_is_break (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv)
    (hc₁ : 0 ≤ e₁.loc (saCol state.STATE_COMMIT) ∧ e₁.loc (saCol state.STATE_COMMIT) < babyBearP)
    (hc₂ : 0 ≤ e₂.loc (saCol state.STATE_COMMIT) ∧ e₂.loc (saCol state.STATE_COMMIT) < babyBearP)
    (hsat₁ : satisfiedVm (D.hashAt t) EffectVmEmitPipelinedSend.pipelinedSendVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm (D.hashAt t) EffectVmEmitPipelinedSend.pipelinedSendVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hne : absorbedCols e₁ ≠ absorbedCols e₂) :
    (narrowDescriptorBreakGame D pipelinedSendNarrowSpec).wins l t (e₁, e₂) :=
  ⟨hsat₁, hsat₂, hc₁, hc₂, hpub, hne⟩

/-- **⚑ THE pipelinedSend DESCRIPTOR STATE BINDING — a SECURITY REDUCTION** (replaces the DELETED
`pipelinedSendDescriptor_commit_binds_state_or_collides`). The chain is: descriptor forger → (`descriptorToSiteBreak`,
using pipelinedSend's `boundaryLastPins`) row equivocator → (`narrowBreakToFinder`, the GROUP-4 trace) a
genuine collision of the deployed sponge. -/
theorem pipelinedSendDescriptor_commit_binds_state_advantage_bound (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : Adversary (narrowDescriptorBreakGame D pipelinedSendNarrowSpec))
    (hEff : Eff (narrowBreakToFinder D (descriptorToSiteBreak D pipelinedSendNarrowSpec A)))
    (hCR : DomainSeparatedCREff D Eff) :
    Negl (gameAdv (narrowDescriptorBreakGame D pipelinedSendNarrowSpec) A) :=
  narrowDescriptor_binds_advantage_bound D pipelinedSendNarrowSpec Eff A hEff hCR

/-- **⚑ `hEff` DISCHARGED for the pipelinedSend descriptor binding** (`Eff := IsPolyTime`). -/
theorem pipelinedSendDescriptor_commit_binds_state_from_polyTime (D : DomainSeparatedSponge)
    (A : Adversary (narrowDescriptorBreakGame D pipelinedSendNarrowSpec))
    (hA : IsPolyTime (narrowDescriptorAnsSize D pipelinedSendNarrowSpec) A) (cw₀ bw₀ cw bw : ℕ)
    (hCR : DomainSeparatedCREff D (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (narrowDescriptorBreakGame D pipelinedSendNarrowSpec) A) :=
  narrowDescriptor_binds_from_polyTime D pipelinedSendNarrowSpec A hA cw₀ bw₀ cw bw (Nat.le_refl _) hCR

/-- **⚑ refusal's PER-EFFECT OBLIGATION, NAMED.** refusal's emitted descriptor rides the deployed
GROUP-4 sites, and a satisfying row's after-state `state_commit` column IS its published `NEW_COMMIT`
mod the deployed prime — the descriptor's own `boundaryLastPins`. This bundle carries VERBATIM the
content the DELETED `refusalDescriptor_commit_binds_state_or_collides` carried (its `hc`/`hcm` step), now as
data a reduction consumes rather than as a disjunction. -/
def refusalNarrowSpec : NarrowCommitSpec where
  descriptor := EffectVmEmitRefusal.refusalVmDescriptor
  usesTransferSites := rfl
  pinsNewCommit := by
    intro hash e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ (EffectVmEmitRefusal.refusalVmDescriptor).constraints := by
        unfold EffectVmEmitRefusal.refusalVmDescriptor
        simp only [List.mem_append]
        exact Or.inl (Or.inr hc)
      have hh := hcs c hmem
      unfold boundaryLastPins at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        · simp only [VmConstraint.holdsVm] at hh ⊢
          exact hh
    exact (boundaryLast_pins e hlast).1

/-- **⚑ A SATISFYING refusal DESCRIPTOR EQUIVOCATION IS A GAME WIN.** Two rows satisfying the EMITTED
refusal descriptor, with canonical commit columns, publishing the SAME `NEW_COMMIT` while DISAGREEING
on an absorbed state column, ARE an answer that wins `narrowDescriptorBreakGame` at refusal's own
spec. A win is a GHOST post-state accepted by the circuit the prover runs. -/
theorem refusalDescriptor_forgery_is_break (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv)
    (hc₁ : 0 ≤ e₁.loc (saCol state.STATE_COMMIT) ∧ e₁.loc (saCol state.STATE_COMMIT) < babyBearP)
    (hc₂ : 0 ≤ e₂.loc (saCol state.STATE_COMMIT) ∧ e₂.loc (saCol state.STATE_COMMIT) < babyBearP)
    (hsat₁ : satisfiedVm (D.hashAt t) EffectVmEmitRefusal.refusalVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm (D.hashAt t) EffectVmEmitRefusal.refusalVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hne : absorbedCols e₁ ≠ absorbedCols e₂) :
    (narrowDescriptorBreakGame D refusalNarrowSpec).wins l t (e₁, e₂) :=
  ⟨hsat₁, hsat₂, hc₁, hc₂, hpub, hne⟩

/-- **⚑ THE refusal DESCRIPTOR STATE BINDING — a SECURITY REDUCTION** (replaces the DELETED
`refusalDescriptor_commit_binds_state_or_collides`). The chain is: descriptor forger → (`descriptorToSiteBreak`,
using refusal's `boundaryLastPins`) row equivocator → (`narrowBreakToFinder`, the GROUP-4 trace) a
genuine collision of the deployed sponge. -/
theorem refusalDescriptor_commit_binds_state_advantage_bound (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : Adversary (narrowDescriptorBreakGame D refusalNarrowSpec))
    (hEff : Eff (narrowBreakToFinder D (descriptorToSiteBreak D refusalNarrowSpec A)))
    (hCR : DomainSeparatedCREff D Eff) :
    Negl (gameAdv (narrowDescriptorBreakGame D refusalNarrowSpec) A) :=
  narrowDescriptor_binds_advantage_bound D refusalNarrowSpec Eff A hEff hCR

/-- **⚑ `hEff` DISCHARGED for the refusal descriptor binding** (`Eff := IsPolyTime`). -/
theorem refusalDescriptor_commit_binds_state_from_polyTime (D : DomainSeparatedSponge)
    (A : Adversary (narrowDescriptorBreakGame D refusalNarrowSpec))
    (hA : IsPolyTime (narrowDescriptorAnsSize D refusalNarrowSpec) A) (cw₀ bw₀ cw bw : ℕ)
    (hCR : DomainSeparatedCREff D (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (narrowDescriptorBreakGame D refusalNarrowSpec) A) :=
  narrowDescriptor_binds_from_polyTime D refusalNarrowSpec A hA cw₀ bw₀ cw bw (Nat.le_refl _) hCR

/-! ### §7.3 — the WIDE (`system_roots`-absorbing) whole-state bindings. -/

/-- **THE PER-EFFECT DATUM.** cellDestroy's WIDE descriptor absorbs the `system_roots`-extended GROUP-4
sites, so its satisfying rows ARE answers of the wide forgery game. -/
def cellDestroyWideSpec : WideCommitSpec where
  descriptor := EffectVmEmitCellDestroyFullState.cellDestroyVmDescriptorWide
  usesWideSites := rfl

/-- **⚑ A SATISFYING WIDE cellDestroy EQUIVOCATION IS A GAME WIN.** Two rows satisfying the WIDE cellDestroy
descriptor, commit columns pinned to their published `NEW_COMMIT`s, publishing the SAME `NEW_COMMIT`,
carrying the `systemRootsDigest` of their claimed sub-blocks, yet DISAGREEING on a base absorbed
column or on some side-table root, ARE an answer that wins `wideDescriptorBreakGame` at cellDestroy's own
spec. -/
theorem cellDestroy_wide_forgery_is_break (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm (D.hashAt t) EffectVmEmitCellDestroyFullState.cellDestroyVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm (D.hashAt t) EffectVmEmitCellDestroyFullState.cellDestroyVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₂)
    (hne : ¬ (baseAbsorbedCols e₁ = baseAbsorbedCols e₂
              ∧ ∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i)) :
    (wideDescriptorBreakGame D cellDestroyWideSpec).wins l t ((e₁, sr₁), (e₂, sr₂)) :=
  ⟨hsat₁, hsat₂, hpin₁, hpin₂, hpub, hd₁, hd₂, hne⟩

/-- **⚑ A SIDE-TABLE ROOT TAMPER IS A GAME WIN** — the tooth the DELETED
`cellDestroy_rejects_root_tamper_or_collides` used to state as a disjunction. Tampering ONE side-table root
(a dropped escrow, an omitted nullifier) while keeping the published `NEW_COMMIT` IS a forgery, so it
is PRICED by the reduction below instead of being left to an always-available `collides` branch. -/
theorem cellDestroy_root_tamper_is_break (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm (D.hashAt t) EffectVmEmitCellDestroyFullState.cellDestroyVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm (D.hashAt t) EffectVmEmitCellDestroyFullState.cellDestroyVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) :
    (wideDescriptorBreakGame D cellDestroyWideSpec).wins l t ((e₁, sr₁), (e₂, sr₂)) :=
  cellDestroy_wide_forgery_is_break D l t e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂
    (fun h => htamper (h.2 i))

/-- **⚑ THE cellDestroy WHOLE-STATE BINDING — a SECURITY REDUCTION** (replaces BOTH deleted
disjunctions `cellDestroy_runnable_full_commit_binds_or_collides` and `cellDestroy_rejects_root_tamper_or_collides`). Under the deployed sponge's
collision floor at `Eff`, an adversary producing a wide cellDestroy forgery — two satisfying rows, one
published `NEW_COMMIT`, two different whole-system states — has NEGLIGIBLE advantage. The binding of
all twelve base state columns AND all eight side-table roots IS that negligible advantage. -/
theorem cellDestroy_wide_binds_full_state_advantage_bound (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : Adversary (wideDescriptorBreakGame D cellDestroyWideSpec))
    (hEff : Eff (wideBreakToFinder D (wideDescriptorToSiteBreak D cellDestroyWideSpec A)))
    (hCR : DomainSeparatedCREff D Eff) :
    Negl (gameAdv (wideDescriptorBreakGame D cellDestroyWideSpec) A) :=
  wideDescriptor_binds_advantage_bound D cellDestroyWideSpec Eff A hEff hCR

/-- **⚑ `hEff` DISCHARGED for the cellDestroy whole-state binding** (`Eff := IsPolyTime`). -/
theorem cellDestroy_wide_binds_full_state_from_polyTime (D : DomainSeparatedSponge)
    (A : Adversary (wideDescriptorBreakGame D cellDestroyWideSpec))
    (hA : IsPolyTime (wideDescriptorAnsSize D cellDestroyWideSpec) A) (cw₀ bw₀ cw bw : ℕ)
    (hCR : DomainSeparatedCREff D (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (wideDescriptorBreakGame D cellDestroyWideSpec) A) :=
  wideDescriptor_binds_from_polyTime D cellDestroyWideSpec A hA cw₀ bw₀ cw bw (Nat.le_refl _) hCR

/-- **THE PER-EFFECT DATUM.** makeSovereign's WIDE descriptor absorbs the `system_roots`-extended GROUP-4
sites, so its satisfying rows ARE answers of the wide forgery game. -/
def makeSovereignWideSpec : WideCommitSpec where
  descriptor := EffectVmEmitMakeSovereignFullState.makeSovereignVmDescriptorWide
  usesWideSites := rfl

/-- **⚑ A SATISFYING WIDE makeSovereign EQUIVOCATION IS A GAME WIN.** Two rows satisfying the WIDE makeSovereign
descriptor, commit columns pinned to their published `NEW_COMMIT`s, publishing the SAME `NEW_COMMIT`,
carrying the `systemRootsDigest` of their claimed sub-blocks, yet DISAGREEING on a base absorbed
column or on some side-table root, ARE an answer that wins `wideDescriptorBreakGame` at makeSovereign's own
spec. -/
theorem makeSovereign_wide_forgery_is_break (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm (D.hashAt t) EffectVmEmitMakeSovereignFullState.makeSovereignVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm (D.hashAt t) EffectVmEmitMakeSovereignFullState.makeSovereignVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₂)
    (hne : ¬ (baseAbsorbedCols e₁ = baseAbsorbedCols e₂
              ∧ ∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i)) :
    (wideDescriptorBreakGame D makeSovereignWideSpec).wins l t ((e₁, sr₁), (e₂, sr₂)) :=
  ⟨hsat₁, hsat₂, hpin₁, hpin₂, hpub, hd₁, hd₂, hne⟩

/-- **⚑ A SIDE-TABLE ROOT TAMPER IS A GAME WIN** — the tooth the DELETED
`makeSovereign_rejects_root_tamper_or_collides` used to state as a disjunction. Tampering ONE side-table root
(a dropped escrow, an omitted nullifier) while keeping the published `NEW_COMMIT` IS a forgery, so it
is PRICED by the reduction below instead of being left to an always-available `collides` branch. -/
theorem makeSovereign_root_tamper_is_break (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm (D.hashAt t) EffectVmEmitMakeSovereignFullState.makeSovereignVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm (D.hashAt t) EffectVmEmitMakeSovereignFullState.makeSovereignVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) :
    (wideDescriptorBreakGame D makeSovereignWideSpec).wins l t ((e₁, sr₁), (e₂, sr₂)) :=
  makeSovereign_wide_forgery_is_break D l t e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂
    (fun h => htamper (h.2 i))

/-- **⚑ THE makeSovereign WHOLE-STATE BINDING — a SECURITY REDUCTION** (replaces BOTH deleted
disjunctions `makeSovereign_runnable_full_commit_binds_or_collides` and `makeSovereign_rejects_root_tamper_or_collides`). Under the deployed sponge's
collision floor at `Eff`, an adversary producing a wide makeSovereign forgery — two satisfying rows, one
published `NEW_COMMIT`, two different whole-system states — has NEGLIGIBLE advantage. The binding of
all twelve base state columns AND all eight side-table roots IS that negligible advantage. -/
theorem makeSovereign_wide_binds_full_state_advantage_bound (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : Adversary (wideDescriptorBreakGame D makeSovereignWideSpec))
    (hEff : Eff (wideBreakToFinder D (wideDescriptorToSiteBreak D makeSovereignWideSpec A)))
    (hCR : DomainSeparatedCREff D Eff) :
    Negl (gameAdv (wideDescriptorBreakGame D makeSovereignWideSpec) A) :=
  wideDescriptor_binds_advantage_bound D makeSovereignWideSpec Eff A hEff hCR

/-- **⚑ `hEff` DISCHARGED for the makeSovereign whole-state binding** (`Eff := IsPolyTime`). -/
theorem makeSovereign_wide_binds_full_state_from_polyTime (D : DomainSeparatedSponge)
    (A : Adversary (wideDescriptorBreakGame D makeSovereignWideSpec))
    (hA : IsPolyTime (wideDescriptorAnsSize D makeSovereignWideSpec) A) (cw₀ bw₀ cw bw : ℕ)
    (hCR : DomainSeparatedCREff D (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (wideDescriptorBreakGame D makeSovereignWideSpec) A) :=
  wideDescriptor_binds_from_polyTime D makeSovereignWideSpec A hA cw₀ bw₀ cw bw (Nat.le_refl _) hCR

/-- **THE PER-EFFECT DATUM.** incrementNonce's WIDE descriptor absorbs the `system_roots`-extended GROUP-4
sites, so its satisfying rows ARE answers of the wide forgery game. -/
def incrementNonceWideSpec : WideCommitSpec where
  descriptor := EffectVmEmitIncrementNonceFullState.incrementNonceVmDescriptorWide
  usesWideSites := rfl

/-- **⚑ A SATISFYING WIDE incrementNonce EQUIVOCATION IS A GAME WIN.** Two rows satisfying the WIDE incrementNonce
descriptor, commit columns pinned to their published `NEW_COMMIT`s, publishing the SAME `NEW_COMMIT`,
carrying the `systemRootsDigest` of their claimed sub-blocks, yet DISAGREEING on a base absorbed
column or on some side-table root, ARE an answer that wins `wideDescriptorBreakGame` at incrementNonce's own
spec. -/
theorem incrementNonce_wide_forgery_is_break (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm (D.hashAt t) EffectVmEmitIncrementNonceFullState.incrementNonceVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm (D.hashAt t) EffectVmEmitIncrementNonceFullState.incrementNonceVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₂)
    (hne : ¬ (baseAbsorbedCols e₁ = baseAbsorbedCols e₂
              ∧ ∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i)) :
    (wideDescriptorBreakGame D incrementNonceWideSpec).wins l t ((e₁, sr₁), (e₂, sr₂)) :=
  ⟨hsat₁, hsat₂, hpin₁, hpin₂, hpub, hd₁, hd₂, hne⟩

/-- **⚑ A SIDE-TABLE ROOT TAMPER IS A GAME WIN** — the tooth the DELETED
`incrementNonce_rejects_root_tamper_or_collides` used to state as a disjunction. Tampering ONE side-table root
(a dropped escrow, an omitted nullifier) while keeping the published `NEW_COMMIT` IS a forgery, so it
is PRICED by the reduction below instead of being left to an always-available `collides` branch. -/
theorem incrementNonce_root_tamper_is_break (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm (D.hashAt t) EffectVmEmitIncrementNonceFullState.incrementNonceVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm (D.hashAt t) EffectVmEmitIncrementNonceFullState.incrementNonceVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) :
    (wideDescriptorBreakGame D incrementNonceWideSpec).wins l t ((e₁, sr₁), (e₂, sr₂)) :=
  incrementNonce_wide_forgery_is_break D l t e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂
    (fun h => htamper (h.2 i))

/-- **⚑ THE incrementNonce WHOLE-STATE BINDING — a SECURITY REDUCTION** (replaces BOTH deleted
disjunctions `incrementNonce_runnable_full_commit_binds_or_collides` and `incrementNonce_rejects_root_tamper_or_collides`). Under the deployed sponge's
collision floor at `Eff`, an adversary producing a wide incrementNonce forgery — two satisfying rows, one
published `NEW_COMMIT`, two different whole-system states — has NEGLIGIBLE advantage. The binding of
all twelve base state columns AND all eight side-table roots IS that negligible advantage. -/
theorem incrementNonce_wide_binds_full_state_advantage_bound (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : Adversary (wideDescriptorBreakGame D incrementNonceWideSpec))
    (hEff : Eff (wideBreakToFinder D (wideDescriptorToSiteBreak D incrementNonceWideSpec A)))
    (hCR : DomainSeparatedCREff D Eff) :
    Negl (gameAdv (wideDescriptorBreakGame D incrementNonceWideSpec) A) :=
  wideDescriptor_binds_advantage_bound D incrementNonceWideSpec Eff A hEff hCR

/-- **⚑ `hEff` DISCHARGED for the incrementNonce whole-state binding** (`Eff := IsPolyTime`). -/
theorem incrementNonce_wide_binds_full_state_from_polyTime (D : DomainSeparatedSponge)
    (A : Adversary (wideDescriptorBreakGame D incrementNonceWideSpec))
    (hA : IsPolyTime (wideDescriptorAnsSize D incrementNonceWideSpec) A) (cw₀ bw₀ cw bw : ℕ)
    (hCR : DomainSeparatedCREff D (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (wideDescriptorBreakGame D incrementNonceWideSpec) A) :=
  wideDescriptor_binds_from_polyTime D incrementNonceWideSpec A hA cw₀ bw₀ cw bw (Nat.le_refl _) hCR

/-- **THE PER-EFFECT DATUM.** exercise's WIDE descriptor absorbs the `system_roots`-extended GROUP-4
sites, so its satisfying rows ARE answers of the wide forgery game. -/
def exerciseWideSpec : WideCommitSpec where
  descriptor := EffectVmEmitExerciseWide.exerciseVmDescriptorWide
  usesWideSites := rfl

/-- **⚑ A SATISFYING WIDE exercise EQUIVOCATION IS A GAME WIN.** Two rows satisfying the WIDE exercise
descriptor, commit columns pinned to their published `NEW_COMMIT`s, publishing the SAME `NEW_COMMIT`,
carrying the `systemRootsDigest` of their claimed sub-blocks, yet DISAGREEING on a base absorbed
column or on some side-table root, ARE an answer that wins `wideDescriptorBreakGame` at exercise's own
spec. -/
theorem exercise_wide_forgery_is_break (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm (D.hashAt t) EffectVmEmitExerciseWide.exerciseVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm (D.hashAt t) EffectVmEmitExerciseWide.exerciseVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₂)
    (hne : ¬ (baseAbsorbedCols e₁ = baseAbsorbedCols e₂
              ∧ ∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i)) :
    (wideDescriptorBreakGame D exerciseWideSpec).wins l t ((e₁, sr₁), (e₂, sr₂)) :=
  ⟨hsat₁, hsat₂, hpin₁, hpin₂, hpub, hd₁, hd₂, hne⟩

/-- **⚑ A SIDE-TABLE ROOT TAMPER IS A GAME WIN** — the tooth the DELETED
`exercise_wide_rejects_root_tamper_or_collides` used to state as a disjunction. Tampering ONE side-table root
(a dropped escrow, an omitted nullifier) while keeping the published `NEW_COMMIT` IS a forgery, so it
is PRICED by the reduction below instead of being left to an always-available `collides` branch. -/
theorem exercise_root_tamper_is_break (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm (D.hashAt t) EffectVmEmitExerciseWide.exerciseVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm (D.hashAt t) EffectVmEmitExerciseWide.exerciseVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) :
    (wideDescriptorBreakGame D exerciseWideSpec).wins l t ((e₁, sr₁), (e₂, sr₂)) :=
  exercise_wide_forgery_is_break D l t e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂
    (fun h => htamper (h.2 i))

/-- **⚑ THE exercise WHOLE-STATE BINDING — a SECURITY REDUCTION** (replaces BOTH deleted
disjunctions `exercise_wide_binds_full_state_or_collides` and `exercise_wide_rejects_root_tamper_or_collides`). Under the deployed sponge's
collision floor at `Eff`, an adversary producing a wide exercise forgery — two satisfying rows, one
published `NEW_COMMIT`, two different whole-system states — has NEGLIGIBLE advantage. The binding of
all twelve base state columns AND all eight side-table roots IS that negligible advantage. -/
theorem exercise_wide_binds_full_state_advantage_bound (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : Adversary (wideDescriptorBreakGame D exerciseWideSpec))
    (hEff : Eff (wideBreakToFinder D (wideDescriptorToSiteBreak D exerciseWideSpec A)))
    (hCR : DomainSeparatedCREff D Eff) :
    Negl (gameAdv (wideDescriptorBreakGame D exerciseWideSpec) A) :=
  wideDescriptor_binds_advantage_bound D exerciseWideSpec Eff A hEff hCR

/-- **⚑ `hEff` DISCHARGED for the exercise whole-state binding** (`Eff := IsPolyTime`). -/
theorem exercise_wide_binds_full_state_from_polyTime (D : DomainSeparatedSponge)
    (A : Adversary (wideDescriptorBreakGame D exerciseWideSpec))
    (hA : IsPolyTime (wideDescriptorAnsSize D exerciseWideSpec) A) (cw₀ bw₀ cw bw : ℕ)
    (hCR : DomainSeparatedCREff D (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (wideDescriptorBreakGame D exerciseWideSpec) A) :=
  wideDescriptor_binds_from_polyTime D exerciseWideSpec A hA cw₀ bw₀ cw bw (Nat.le_refl _) hCR

/-- **THE PER-EFFECT DATUM.** emitEvent's WIDE descriptor absorbs the `system_roots`-extended GROUP-4
sites, so its satisfying rows ARE answers of the wide forgery game. -/
def emitEventWideSpec : WideCommitSpec where
  descriptor := EffectVmEmitEmitEventWide.emitEventVmDescriptorWide
  usesWideSites := rfl

/-- **⚑ A SATISFYING WIDE emitEvent EQUIVOCATION IS A GAME WIN.** Two rows satisfying the WIDE emitEvent
descriptor, commit columns pinned to their published `NEW_COMMIT`s, publishing the SAME `NEW_COMMIT`,
carrying the `systemRootsDigest` of their claimed sub-blocks, yet DISAGREEING on a base absorbed
column or on some side-table root, ARE an answer that wins `wideDescriptorBreakGame` at emitEvent's own
spec. -/
theorem emitEvent_wide_forgery_is_break (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm (D.hashAt t) EffectVmEmitEmitEventWide.emitEventVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm (D.hashAt t) EffectVmEmitEmitEventWide.emitEventVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₂)
    (hne : ¬ (baseAbsorbedCols e₁ = baseAbsorbedCols e₂
              ∧ ∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i)) :
    (wideDescriptorBreakGame D emitEventWideSpec).wins l t ((e₁, sr₁), (e₂, sr₂)) :=
  ⟨hsat₁, hsat₂, hpin₁, hpin₂, hpub, hd₁, hd₂, hne⟩

/-- **⚑ A SIDE-TABLE ROOT TAMPER IS A GAME WIN** — the tooth the DELETED
`emitEvent_wide_rejects_root_tamper_or_collides` used to state as a disjunction. Tampering ONE side-table root
(a dropped escrow, an omitted nullifier) while keeping the published `NEW_COMMIT` IS a forgery, so it
is PRICED by the reduction below instead of being left to an always-available `collides` branch. -/
theorem emitEvent_root_tamper_is_break (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm (D.hashAt t) EffectVmEmitEmitEventWide.emitEventVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm (D.hashAt t) EffectVmEmitEmitEventWide.emitEventVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) :
    (wideDescriptorBreakGame D emitEventWideSpec).wins l t ((e₁, sr₁), (e₂, sr₂)) :=
  emitEvent_wide_forgery_is_break D l t e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂
    (fun h => htamper (h.2 i))

/-- **⚑ THE emitEvent WHOLE-STATE BINDING — a SECURITY REDUCTION** (replaces BOTH deleted
disjunctions `emitEvent_wide_binds_full_state_or_collides` and `emitEvent_wide_rejects_root_tamper_or_collides`). Under the deployed sponge's
collision floor at `Eff`, an adversary producing a wide emitEvent forgery — two satisfying rows, one
published `NEW_COMMIT`, two different whole-system states — has NEGLIGIBLE advantage. The binding of
all twelve base state columns AND all eight side-table roots IS that negligible advantage. -/
theorem emitEvent_wide_binds_full_state_advantage_bound (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : Adversary (wideDescriptorBreakGame D emitEventWideSpec))
    (hEff : Eff (wideBreakToFinder D (wideDescriptorToSiteBreak D emitEventWideSpec A)))
    (hCR : DomainSeparatedCREff D Eff) :
    Negl (gameAdv (wideDescriptorBreakGame D emitEventWideSpec) A) :=
  wideDescriptor_binds_advantage_bound D emitEventWideSpec Eff A hEff hCR

/-- **⚑ `hEff` DISCHARGED for the emitEvent whole-state binding** (`Eff := IsPolyTime`). -/
theorem emitEvent_wide_binds_full_state_from_polyTime (D : DomainSeparatedSponge)
    (A : Adversary (wideDescriptorBreakGame D emitEventWideSpec))
    (hA : IsPolyTime (wideDescriptorAnsSize D emitEventWideSpec) A) (cw₀ bw₀ cw bw : ℕ)
    (hCR : DomainSeparatedCREff D (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (wideDescriptorBreakGame D emitEventWideSpec) A) :=
  wideDescriptor_binds_from_polyTime D emitEventWideSpec A hA cw₀ bw₀ cw bw (Nat.le_refl _) hCR

/-- **THE PER-EFFECT DATUM.** receiptArchive's WIDE descriptor absorbs the `system_roots`-extended GROUP-4
sites, so its satisfying rows ARE answers of the wide forgery game. -/
def receiptArchiveWideSpec : WideCommitSpec where
  descriptor := EffectVmEmitReceiptArchiveWide.archiveVmDescriptorWide
  usesWideSites := rfl

/-- **⚑ A SATISFYING WIDE receiptArchive EQUIVOCATION IS A GAME WIN.** Two rows satisfying the WIDE receiptArchive
descriptor, commit columns pinned to their published `NEW_COMMIT`s, publishing the SAME `NEW_COMMIT`,
carrying the `systemRootsDigest` of their claimed sub-blocks, yet DISAGREEING on a base absorbed
column or on some side-table root, ARE an answer that wins `wideDescriptorBreakGame` at receiptArchive's own
spec. -/
theorem receiptArchive_wide_forgery_is_break (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm (D.hashAt t) EffectVmEmitReceiptArchiveWide.archiveVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm (D.hashAt t) EffectVmEmitReceiptArchiveWide.archiveVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₂)
    (hne : ¬ (baseAbsorbedCols e₁ = baseAbsorbedCols e₂
              ∧ ∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i)) :
    (wideDescriptorBreakGame D receiptArchiveWideSpec).wins l t ((e₁, sr₁), (e₂, sr₂)) :=
  ⟨hsat₁, hsat₂, hpin₁, hpin₂, hpub, hd₁, hd₂, hne⟩

/-- **⚑ A SIDE-TABLE ROOT TAMPER IS A GAME WIN** — the tooth the DELETED
`receiptArchive_wide_rejects_root_tamper_or_collides` used to state as a disjunction. Tampering ONE side-table root
(a dropped escrow, an omitted nullifier) while keeping the published `NEW_COMMIT` IS a forgery, so it
is PRICED by the reduction below instead of being left to an always-available `collides` branch. -/
theorem receiptArchive_root_tamper_is_break (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm (D.hashAt t) EffectVmEmitReceiptArchiveWide.archiveVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm (D.hashAt t) EffectVmEmitReceiptArchiveWide.archiveVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) :
    (wideDescriptorBreakGame D receiptArchiveWideSpec).wins l t ((e₁, sr₁), (e₂, sr₂)) :=
  receiptArchive_wide_forgery_is_break D l t e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂
    (fun h => htamper (h.2 i))

/-- **⚑ THE receiptArchive WHOLE-STATE BINDING — a SECURITY REDUCTION** (replaces BOTH deleted
disjunctions `receiptArchive_wide_binds_full_state_or_collides` and `receiptArchive_wide_rejects_root_tamper_or_collides`). Under the deployed sponge's
collision floor at `Eff`, an adversary producing a wide receiptArchive forgery — two satisfying rows, one
published `NEW_COMMIT`, two different whole-system states — has NEGLIGIBLE advantage. The binding of
all twelve base state columns AND all eight side-table roots IS that negligible advantage. -/
theorem receiptArchive_wide_binds_full_state_advantage_bound (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : Adversary (wideDescriptorBreakGame D receiptArchiveWideSpec))
    (hEff : Eff (wideBreakToFinder D (wideDescriptorToSiteBreak D receiptArchiveWideSpec A)))
    (hCR : DomainSeparatedCREff D Eff) :
    Negl (gameAdv (wideDescriptorBreakGame D receiptArchiveWideSpec) A) :=
  wideDescriptor_binds_advantage_bound D receiptArchiveWideSpec Eff A hEff hCR

/-- **⚑ `hEff` DISCHARGED for the receiptArchive whole-state binding** (`Eff := IsPolyTime`). -/
theorem receiptArchive_wide_binds_full_state_from_polyTime (D : DomainSeparatedSponge)
    (A : Adversary (wideDescriptorBreakGame D receiptArchiveWideSpec))
    (hA : IsPolyTime (wideDescriptorAnsSize D receiptArchiveWideSpec) A) (cw₀ bw₀ cw bw : ℕ)
    (hCR : DomainSeparatedCREff D (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (wideDescriptorBreakGame D receiptArchiveWideSpec) A) :=
  wideDescriptor_binds_from_polyTime D receiptArchiveWideSpec A hA cw₀ bw₀ cw bw (Nat.le_refl _) hCR

/-- **THE PER-EFFECT DATUM.** pipelinedSend's WIDE descriptor absorbs the `system_roots`-extended GROUP-4
sites, so its satisfying rows ARE answers of the wide forgery game. -/
def pipelinedSendWideSpec : WideCommitSpec where
  descriptor := EffectVmEmitPipelinedSendWide.pipelinedSendVmDescriptorWide
  usesWideSites := rfl

/-- **⚑ A SATISFYING WIDE pipelinedSend EQUIVOCATION IS A GAME WIN.** Two rows satisfying the WIDE pipelinedSend
descriptor, commit columns pinned to their published `NEW_COMMIT`s, publishing the SAME `NEW_COMMIT`,
carrying the `systemRootsDigest` of their claimed sub-blocks, yet DISAGREEING on a base absorbed
column or on some side-table root, ARE an answer that wins `wideDescriptorBreakGame` at pipelinedSend's own
spec. -/
theorem pipelinedSend_wide_forgery_is_break (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm (D.hashAt t) EffectVmEmitPipelinedSendWide.pipelinedSendVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm (D.hashAt t) EffectVmEmitPipelinedSendWide.pipelinedSendVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₂)
    (hne : ¬ (baseAbsorbedCols e₁ = baseAbsorbedCols e₂
              ∧ ∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i)) :
    (wideDescriptorBreakGame D pipelinedSendWideSpec).wins l t ((e₁, sr₁), (e₂, sr₂)) :=
  ⟨hsat₁, hsat₂, hpin₁, hpin₂, hpub, hd₁, hd₂, hne⟩

/-- **⚑ A SIDE-TABLE ROOT TAMPER IS A GAME WIN** — the tooth the DELETED
`pipelinedSend_wide_rejects_root_tamper_or_collides` used to state as a disjunction. Tampering ONE side-table root
(a dropped escrow, an omitted nullifier) while keeping the published `NEW_COMMIT` IS a forgery, so it
is PRICED by the reduction below instead of being left to an always-available `collides` branch. -/
theorem pipelinedSend_root_tamper_is_break (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm (D.hashAt t) EffectVmEmitPipelinedSendWide.pipelinedSendVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm (D.hashAt t) EffectVmEmitPipelinedSendWide.pipelinedSendVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) :
    (wideDescriptorBreakGame D pipelinedSendWideSpec).wins l t ((e₁, sr₁), (e₂, sr₂)) :=
  pipelinedSend_wide_forgery_is_break D l t e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂
    (fun h => htamper (h.2 i))

/-- **⚑ THE pipelinedSend WHOLE-STATE BINDING — a SECURITY REDUCTION** (replaces BOTH deleted
disjunctions `pipelinedSend_wide_binds_full_state_or_collides` and `pipelinedSend_wide_rejects_root_tamper_or_collides`). Under the deployed sponge's
collision floor at `Eff`, an adversary producing a wide pipelinedSend forgery — two satisfying rows, one
published `NEW_COMMIT`, two different whole-system states — has NEGLIGIBLE advantage. The binding of
all twelve base state columns AND all eight side-table roots IS that negligible advantage. -/
theorem pipelinedSend_wide_binds_full_state_advantage_bound (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : Adversary (wideDescriptorBreakGame D pipelinedSendWideSpec))
    (hEff : Eff (wideBreakToFinder D (wideDescriptorToSiteBreak D pipelinedSendWideSpec A)))
    (hCR : DomainSeparatedCREff D Eff) :
    Negl (gameAdv (wideDescriptorBreakGame D pipelinedSendWideSpec) A) :=
  wideDescriptor_binds_advantage_bound D pipelinedSendWideSpec Eff A hEff hCR

/-- **⚑ `hEff` DISCHARGED for the pipelinedSend whole-state binding** (`Eff := IsPolyTime`). -/
theorem pipelinedSend_wide_binds_full_state_from_polyTime (D : DomainSeparatedSponge)
    (A : Adversary (wideDescriptorBreakGame D pipelinedSendWideSpec))
    (hA : IsPolyTime (wideDescriptorAnsSize D pipelinedSendWideSpec) A) (cw₀ bw₀ cw bw : ℕ)
    (hCR : DomainSeparatedCREff D (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (wideDescriptorBreakGame D pipelinedSendWideSpec) A) :=
  wideDescriptor_binds_from_polyTime D pipelinedSendWideSpec A hA cw₀ bw₀ cw bw (Nat.le_refl _) hCR

/-- **THE PER-EFFECT DATUM.** refusal's WIDE descriptor absorbs the `system_roots`-extended GROUP-4
sites, so its satisfying rows ARE answers of the wide forgery game. -/
def refusalWideSpec : WideCommitSpec where
  descriptor := EffectVmEmitRefusalFullState.refusalVmDescriptorWide
  usesWideSites := rfl

/-- **⚑ A SATISFYING WIDE refusal EQUIVOCATION IS A GAME WIN.** Two rows satisfying the WIDE refusal
descriptor, commit columns pinned to their published `NEW_COMMIT`s, publishing the SAME `NEW_COMMIT`,
carrying the `systemRootsDigest` of their claimed sub-blocks, yet DISAGREEING on a base absorbed
column or on some side-table root, ARE an answer that wins `wideDescriptorBreakGame` at refusal's own
spec. -/
theorem refusal_wide_forgery_is_break (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm (D.hashAt t) EffectVmEmitRefusalFullState.refusalVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm (D.hashAt t) EffectVmEmitRefusalFullState.refusalVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₂)
    (hne : ¬ (baseAbsorbedCols e₁ = baseAbsorbedCols e₂
              ∧ ∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i)) :
    (wideDescriptorBreakGame D refusalWideSpec).wins l t ((e₁, sr₁), (e₂, sr₂)) :=
  ⟨hsat₁, hsat₂, hpin₁, hpin₂, hpub, hd₁, hd₂, hne⟩

/-- **⚑ A SIDE-TABLE ROOT TAMPER IS A GAME WIN** — the tooth the DELETED
`refusal_rejects_root_tamper_or_collides` used to state as a disjunction. Tampering ONE side-table root
(a dropped escrow, an omitted nullifier) while keeping the published `NEW_COMMIT` IS a forgery, so it
is PRICED by the reduction below instead of being left to an always-available `collides` branch. -/
theorem refusal_root_tamper_is_break (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm (D.hashAt t) EffectVmEmitRefusalFullState.refusalVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm (D.hashAt t) EffectVmEmitRefusalFullState.refusalVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) :
    (wideDescriptorBreakGame D refusalWideSpec).wins l t ((e₁, sr₁), (e₂, sr₂)) :=
  refusal_wide_forgery_is_break D l t e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂
    (fun h => htamper (h.2 i))

/-- **⚑ THE refusal WHOLE-STATE BINDING — a SECURITY REDUCTION** (replaces BOTH deleted
disjunctions `refusal_runnable_full_commit_binds_or_collides` and `refusal_rejects_root_tamper_or_collides`). Under the deployed sponge's
collision floor at `Eff`, an adversary producing a wide refusal forgery — two satisfying rows, one
published `NEW_COMMIT`, two different whole-system states — has NEGLIGIBLE advantage. The binding of
all twelve base state columns AND all eight side-table roots IS that negligible advantage. -/
theorem refusal_wide_binds_full_state_advantage_bound (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : Adversary (wideDescriptorBreakGame D refusalWideSpec))
    (hEff : Eff (wideBreakToFinder D (wideDescriptorToSiteBreak D refusalWideSpec A)))
    (hCR : DomainSeparatedCREff D Eff) :
    Negl (gameAdv (wideDescriptorBreakGame D refusalWideSpec) A) :=
  wideDescriptor_binds_advantage_bound D refusalWideSpec Eff A hEff hCR

/-- **⚑ `hEff` DISCHARGED for the refusal whole-state binding** (`Eff := IsPolyTime`). -/
theorem refusal_wide_binds_full_state_from_polyTime (D : DomainSeparatedSponge)
    (A : Adversary (wideDescriptorBreakGame D refusalWideSpec))
    (hA : IsPolyTime (wideDescriptorAnsSize D refusalWideSpec) A) (cw₀ bw₀ cw bw : ℕ)
    (hCR : DomainSeparatedCREff D (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (wideDescriptorBreakGame D refusalWideSpec) A) :=
  wideDescriptor_binds_from_polyTime D refusalWideSpec A hA cw₀ bw₀ cw bw (Nat.le_refl _) hCR

/-- **THE PER-EFFECT DATUM.** noop's WIDE descriptor absorbs the `system_roots`-extended GROUP-4
sites, so its satisfying rows ARE answers of the wide forgery game. -/
def noopWideSpec : WideCommitSpec where
  descriptor := EffectVmEmitNoopWide.noopVmDescriptorWide
  usesWideSites := rfl

/-- **⚑ A SATISFYING WIDE noop EQUIVOCATION IS A GAME WIN.** Two rows satisfying the WIDE noop
descriptor, commit columns pinned to their published `NEW_COMMIT`s, publishing the SAME `NEW_COMMIT`,
carrying the `systemRootsDigest` of their claimed sub-blocks, yet DISAGREEING on a base absorbed
column or on some side-table root, ARE an answer that wins `wideDescriptorBreakGame` at noop's own
spec. -/
theorem noop_wide_forgery_is_break (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm (D.hashAt t) EffectVmEmitNoopWide.noopVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm (D.hashAt t) EffectVmEmitNoopWide.noopVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₂)
    (hne : ¬ (baseAbsorbedCols e₁ = baseAbsorbedCols e₂
              ∧ ∀ i : Fin N_SYSTEM_ROOTS, sr₁ i = sr₂ i)) :
    (wideDescriptorBreakGame D noopWideSpec).wins l t ((e₁, sr₁), (e₂, sr₂)) :=
  ⟨hsat₁, hsat₂, hpin₁, hpin₂, hpub, hd₁, hd₂, hne⟩

/-- **⚑ A SIDE-TABLE ROOT TAMPER IS A GAME WIN** — the tooth the DELETED
`noop_wide_rejects_root_tamper_or_collides` used to state as a disjunction. Tampering ONE side-table root
(a dropped escrow, an omitted nullifier) while keeping the published `NEW_COMMIT` IS a forgery, so it
is PRICED by the reduction below instead of being left to an always-available `collides` branch. -/
theorem noop_root_tamper_is_break (D : DomainSeparatedSponge) (l : ℕ) (t : D.Tag)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm (D.hashAt t) EffectVmEmitNoopWide.noopVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm (D.hashAt t) EffectVmEmitNoopWide.noopVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) :
    (wideDescriptorBreakGame D noopWideSpec).wins l t ((e₁, sr₁), (e₂, sr₂)) :=
  noop_wide_forgery_is_break D l t e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂
    (fun h => htamper (h.2 i))

/-- **⚑ THE noop WHOLE-STATE BINDING — a SECURITY REDUCTION** (replaces BOTH deleted
disjunctions `noop_wide_binds_full_state_or_collides` and `noop_wide_rejects_root_tamper_or_collides`). Under the deployed sponge's
collision floor at `Eff`, an adversary producing a wide noop forgery — two satisfying rows, one
published `NEW_COMMIT`, two different whole-system states — has NEGLIGIBLE advantage. The binding of
all twelve base state columns AND all eight side-table roots IS that negligible advantage. -/
theorem noop_wide_binds_full_state_advantage_bound (D : DomainSeparatedSponge)
    (Eff : Adversary (hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : Adversary (wideDescriptorBreakGame D noopWideSpec))
    (hEff : Eff (wideBreakToFinder D (wideDescriptorToSiteBreak D noopWideSpec A)))
    (hCR : DomainSeparatedCREff D Eff) :
    Negl (gameAdv (wideDescriptorBreakGame D noopWideSpec) A) :=
  wideDescriptor_binds_advantage_bound D noopWideSpec Eff A hEff hCR

/-- **⚑ `hEff` DISCHARGED for the noop whole-state binding** (`Eff := IsPolyTime`). -/
theorem noop_wide_binds_full_state_from_polyTime (D : DomainSeparatedSponge)
    (A : Adversary (wideDescriptorBreakGame D noopWideSpec))
    (hA : IsPolyTime (wideDescriptorAnsSize D noopWideSpec) A) (cw₀ bw₀ cw bw : ℕ)
    (hCR : DomainSeparatedCREff D (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (wideDescriptorBreakGame D noopWideSpec) A) :=
  wideDescriptor_binds_from_polyTime D noopWideSpec A hA cw₀ bw₀ cw bw (Nat.le_refl _) hCR

#assert_all_clean [
  cellDestroyVm_row_forgery_is_break,
  cellDestroy_commit_binds_block_advantage_bound,
  cellDestroy_commit_binds_block_from_polyTime,
  makeSovereignVm_row_forgery_is_break,
  makeSovereign_commit_binds_block_advantage_bound,
  makeSovereign_commit_binds_block_from_polyTime,
  exerciseVm_row_forgery_is_break,
  exercise_commit_binds_block_advantage_bound,
  exercise_commit_binds_block_from_polyTime,
  archiveVm_row_forgery_is_break,
  archive_commit_binds_block_advantage_bound,
  archive_commit_binds_block_from_polyTime,
  pipelinedSendVm_row_forgery_is_break,
  pipelinedSend_commit_binds_block_advantage_bound,
  pipelinedSend_commit_binds_block_from_polyTime,
  refusalVm_row_forgery_is_break,
  refusal_commit_binds_block_advantage_bound,
  refusal_commit_binds_block_from_polyTime,
  cellDestroyDescriptor_forgery_is_break,
  cellDestroyDescriptor_commit_binds_state_advantage_bound,
  cellDestroyDescriptor_commit_binds_state_from_polyTime,
  incNonceDescriptor_forgery_is_break,
  incNonceDescriptor_commit_binds_state_advantage_bound,
  incNonceDescriptor_commit_binds_state_from_polyTime,
  exerciseDescriptor_forgery_is_break,
  exerciseDescriptor_commit_binds_state_advantage_bound,
  exerciseDescriptor_commit_binds_state_from_polyTime,
  emitEventDescriptor_forgery_is_break,
  emitEventDescriptor_commit_binds_state_advantage_bound,
  emitEventDescriptor_commit_binds_state_from_polyTime,
  pipelinedSendDescriptor_forgery_is_break,
  pipelinedSendDescriptor_commit_binds_state_advantage_bound,
  pipelinedSendDescriptor_commit_binds_state_from_polyTime,
  refusalDescriptor_forgery_is_break,
  refusalDescriptor_commit_binds_state_advantage_bound,
  refusalDescriptor_commit_binds_state_from_polyTime,
  cellDestroy_wide_forgery_is_break,
  cellDestroy_root_tamper_is_break,
  cellDestroy_wide_binds_full_state_advantage_bound,
  cellDestroy_wide_binds_full_state_from_polyTime,
  makeSovereign_wide_forgery_is_break,
  makeSovereign_root_tamper_is_break,
  makeSovereign_wide_binds_full_state_advantage_bound,
  makeSovereign_wide_binds_full_state_from_polyTime,
  incrementNonce_wide_forgery_is_break,
  incrementNonce_root_tamper_is_break,
  incrementNonce_wide_binds_full_state_advantage_bound,
  incrementNonce_wide_binds_full_state_from_polyTime,
  exercise_wide_forgery_is_break,
  exercise_root_tamper_is_break,
  exercise_wide_binds_full_state_advantage_bound,
  exercise_wide_binds_full_state_from_polyTime,
  emitEvent_wide_forgery_is_break,
  emitEvent_root_tamper_is_break,
  emitEvent_wide_binds_full_state_advantage_bound,
  emitEvent_wide_binds_full_state_from_polyTime,
  receiptArchive_wide_forgery_is_break,
  receiptArchive_root_tamper_is_break,
  receiptArchive_wide_binds_full_state_advantage_bound,
  receiptArchive_wide_binds_full_state_from_polyTime,
  pipelinedSend_wide_forgery_is_break,
  pipelinedSend_root_tamper_is_break,
  pipelinedSend_wide_binds_full_state_advantage_bound,
  pipelinedSend_wide_binds_full_state_from_polyTime,
  refusal_wide_forgery_is_break,
  refusal_root_tamper_is_break,
  refusal_wide_binds_full_state_advantage_bound,
  refusal_wide_binds_full_state_from_polyTime,
  noop_wide_forgery_is_break,
  noop_root_tamper_is_break,
  noop_wide_binds_full_state_advantage_bound,
  noop_wide_binds_full_state_from_polyTime
]

end Dregg2.Circuit.Emit.EffectVmCommitReduction
