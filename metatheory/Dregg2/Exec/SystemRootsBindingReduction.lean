/-
# `Dregg2.Exec.SystemRootsBindingReduction` — the `system_roots` consensus binding, REBUILT as a
SECURITY REDUCTION on the grounded floor.

## What was here before, and why it was still a shirk

`Dregg2.Exec.SystemRoots` §3/§4 exports five bindings for the eight kernel-owned side-table roots
(escrow · queue · refcount · sturdyref · delegation · nullifier · commitments · sealed-boxes):

    systemRootsDigest_binds_or_collides           rootList sr = rootList sr' ∨ RootsColl …
    systemRootsDigest_binds_fn_or_collides        sr = sr'                   ∨ RootsColl …
    systemRootsDigest_binds_pointwise_or_collides (∀ i, sr i = sr' i)        ∨ RootsColl …
    cellCommitS_binds_systemRoots_or_collides     equal digest               ∨ CellCommitSColl …
    cellCommitS_binds_roots_pointwise_or_collides (∀ i, sr i = sr' i) ∨ CellCommitSColl ∨ RootsColl

Each was a genuine repair of a VACUOUS predecessor (they used to carry `compressNInjective`, which the
deployed BabyBear sponge REFUTES).  But they are still BARE DISJUNCTIONS, and at deployed parameters a
sponge collision EXISTS by pigeonhole — so `binds ∨ collides` is satisfiable through the `collides`
branch with `binds` never holding.  They quantify over SOLUTIONS.  Cryptographic hardness quantifies
over EFFICIENT ADVERSARIES.

⚑ **THESE ARE NOT THE HEADLINE ANY MORE.**  This module supplies the headline, and `SystemRoots`'s
docstrings now say so.  The exported security claim about the eight consensus roots is now
`sysRoots_binds_from_polyTime` / `cellCommitS_binds_from_polyTime` / `cellRoots_binds_from_polyTime`
below.

⚑ **AND THE DEMOTION IS NOT A DEPENDENCE — SAID PLAINLY, BECAUSE THE OPPOSITE IS THE EASY CLAIM.**
This reduction does NOT consume the five disjunctions.  Its win relation is
`EncodedBindingReduction.encBreakGame` at the deployed encoder, and the two bridges
(`sysRoots_forgery_is_break`, `cellCommitS_forgery_is_break`) are proved from `rootsEnc_faithful` +
`rootsEnc_inj` and from `List.append_cancel_left` respectively — the disjunctions appear over there
only in prose.  They survive for two reasons that are OPEN WORK, not architecture:

  1. `SystemRoots` §3′'s `_of_injective` strength bridges are derived from them, and
  2. they are STILL the exported headline one layer up — `Circuit.Emit.EffectVmFullStateRunnable`'s
     `wide_binds_systemRoots_or_collides` and its per-tag re-exports across 29 `Circuit/Emit`
     modules, of which exactly ONE (`EffectVmEmitMintRunnable`, via
     `EffectVmRowCommitReduction.wideRow_binds_from_polyTime`) has been re-pointed at a reduction.

Until (2) is finished, the deployed per-tag statements still offer the escape branch that this module
prices at the record layer.  That residual is named here rather than left for a reader to discover.

## The shape, and what it costs

The primitive is the deployed domain-separated Poseidon2 sponge
(`Poseidon2KeyedBridge.spongeFamily D`) — the real `List ℤ → ℤ` the prover computes, keyed by
the tag it absorbs.  The whole reduction is inherited from
`Dregg2.Crypto.EncodedBindingReduction`; this file supplies only

  * the two ENCODERS — `rootList` (the eight ordered root cells) at the digest layer, and
    `rest ++ [systemRootsDigest]` at the commitment layer — plus the definitional facts that the
    deployed digest/commitment ARE the family applied to them,
  * the STRUCTURAL injectivity `List.ofFn_inj` (a fact about the LIMB LAYOUT, not about the hash),
  * the fixed widths (`8` limbs at the digest layer, `rest.length + 1` at the commitment layer) that
    discharge the `poly_time` output-growth slot.

The three-way disjunction of `cellCommitS_binds_roots_pointwise_or_collides` becomes the standard
UNION BOUND (`EncodedBindingReduction.chained_binding_advantage_bound`): two extracted finders, two
advantages, one floor, one negligible sum.

⚑ **THE RESIDUAL, NAMED — AND THE INSTANTIATION IS PART OF IT.** The floor is
`HashCRHardQuant (spongeFamily D) Eff`, and at `Eff := ⊤` it is FALSE at deployed BabyBear parameters
(§5 — the honest price), at `Eff := ⊥` vacuous.  `Eff := IsPolyTime` is a strictly intermediate CLASS
(the class is proved inhabited, and `CostAdversary.bruteForce_not_polyTime` excludes the brute-force
PROGRAM) — but §6 PROVES that the floor AT that class is FALSE too at the deployed sponge:
`IsPolyTime` prices only ANSWER SIZE and declared syntactic work, so the `Classical.choice` adversary
that answers each tag with a TWO-LIMB collision is in it and wins with probability `1`
(`sysRoots_floor_polyTime_false_babyBear`).

So, stated without softening: the `_advantage_bound` theorems (arbitrary `Eff`, `hEff` in the open)
are this module's live content; the three `_from_polyTime` theorems are VACUOUS at deployed
parameters, because their floor hypothesis is refutable there.  What the `poly_time` discharge buys is
that the REDUCTION's own efficiency is a theorem rather than an assumption — it does not buy a floor
the deployed sponge satisfies.  Closing that needs a computability- or query-bounded adversary class
in `Dregg2.Crypto.CostAdversary`, which is shared by every `_from_polyTime` in the tree.

No `sorry`, no `axiom`, no `native_decide`.
-/
import Dregg2.Exec.SystemRoots
import Dregg2.Crypto.SpongeCarrierReduction
import Dregg2.Crypto.EncodedBindingReduction

namespace Dregg2.Exec.SystemRootsBindingReduction

open Dregg2.Exec.SystemRoots
open Dregg2.Crypto.SpongeCarrierReduction (SpongeKeyed spongeFamily)
open Dregg2.Crypto.ConcreteSecurity (Negl)
open Dregg2.Crypto.FloorGames (Game Adversary gameAdv hashGame HashCRHardQuant)
open Dregg2.Crypto.CostAdversary (AnsSize IsPolyTime)
open Dregg2.Crypto.EncodedBindingReduction

set_option autoImplicit false

/-! ## §1 — the two deployed ENCODERS, and the faithfulness facts. -/

/-- **THE DIGEST-LAYER ENCODER** — the eight ordered side-table roots, exactly the list the deployed
`systemRootsDigest` sponge absorbs.  Key-independent: the domain separation lives in the family's own
`H` (`sponge (tagCode t ++ ·)`), which is where the deployment puts it. -/
def rootsEnc (D : SpongeKeyed) :
    ∀ l, (spongeFamily D).Key l → SysRoots → (spongeFamily D).Input :=
  fun _ _ sr => rootList sr

/-- **THE COMMITMENT-LAYER ENCODER** — the canonical cell's absorbed list with the `system_roots`
digest folded in as its last limb.  Key-DEPENDENT, because the inner digest is itself computed at the
sampled tag: this is the deployed nesting, not an idealization. -/
def commitEnc (D : SpongeKeyed) (rest : List FieldElem) :
    ∀ l, (spongeFamily D).Key l → SysRoots → (spongeFamily D).Input :=
  fun _ t sr => rest ++ [systemRootsDigest (D.hashAt t) sr]

/-- **FAITHFULNESS (digest layer).** The deployed `systemRootsDigest` at the sampled tag IS the keyed
family applied to the encoder — a definitional equality, so the game below is a game about the very
function the prover computes. -/
theorem rootsEnc_faithful (D : SpongeKeyed) (l : ℕ)
    (t : (spongeFamily D).Key l) (sr : SysRoots) :
    systemRootsDigest (D.hashAt t) sr = (spongeFamily D).H l t (rootsEnc D l t sr) := by
  simp [systemRootsDigest, Dregg2.Circuit.ListCommit.listDigest, rootsEnc, spongeFamily,
    SpongeKeyed.hashAt]

/-- **FAITHFULNESS (commitment layer).** The deployed `cellCommitS` at the sampled tag IS the keyed
family applied to the commitment encoder. -/
theorem commitEnc_faithful (D : SpongeKeyed) (rest : List FieldElem) (l : ℕ)
    (t : (spongeFamily D).Key l) (sr : SysRoots) :
    cellCommitS (D.hashAt t) rest sr = (spongeFamily D).H l t (commitEnc D rest l t sr) :=
  rfl

/-- **THE STRUCTURAL INJECTIVITY — about the LIMB LAYOUT, never about the hash.** `rootList` is
`List.ofFn`, so equal root lists force the whole sub-block function equal.  This is the fact that makes
a sub-block equivocation an ENCODING equivocation, i.e. a genuine sponge break. -/
theorem rootsEnc_inj (D : SpongeKeyed) (l : ℕ) (t : (spongeFamily D).Key l)
    (sr sr' : SysRoots) (h : rootsEnc D l t sr = rootsEnc D l t sr') : sr = sr' :=
  List.ofFn_inj.mp h

/-! ## §2 — the two forgery GAMES, and the deployed-object bridges.

⚑ These REPLACE `systemRootsDigest_binds_or_collides` / `_binds_fn_or_collides` /
`_binds_pointwise_or_collides` / `cellCommitS_binds_systemRoots_or_collides` as the exported claim.
All three digest-layer disjunctions are ONE game — they differed only in how the SAME binding was
projected (list / function / pointwise), which is precisely why three bare disjunctions were three
copies of one unpriced escape. -/

/-- **THE `system_roots` DIGEST FORGERY.** The adversary is handed a sampled domain-separation tag and
WINS iff it publishes ONE `systemRootsDigest` for TWO different side-table configurations — a dropped
escrow, an omitted nullifier, a reordered queue, all at once. -/
def sysRootsBreakGame (D : SpongeKeyed) : Game :=
  encBreakGame (spongeFamily D) SysRoots (rootsEnc D)

/-- **THE CELL-COMMITMENT FORGERY.** The adversary WINS iff two cells over the same `rest` publish one
`cellCommitS` while their absorbed `system_roots` digests differ. -/
def cellCommitSBreakGame (D : SpongeKeyed) (rest : List FieldElem) : Game :=
  encBreakGame (spongeFamily D) SysRoots (commitEnc D rest)

/-- **⚑ THE FORGERY IS THE DEPLOYED ANTI-GHOST VIOLATION (digest layer).** Two side-table sub-blocks
that DIFFER AT ANY KERNEL INDEX yet share the deployed `systemRootsDigest` ARE a win.  This is the
statement `systemRootsDigest_binds_pointwise_or_collides` was reaching for, with the escape priced
instead of offered. -/
theorem sysRoots_forgery_is_break (D : SpongeKeyed) (l : ℕ)
    (t : (spongeFamily D).Key l) {sr sr' : SysRoots}
    (hne : ¬ (∀ i : Fin N_SYSTEM_ROOTS, sr i = sr' i))
    (heq : systemRootsDigest (D.hashAt t) sr = systemRootsDigest (D.hashAt t) sr') :
    (sysRootsBreakGame D).wins l t (sr, sr') := by
  refine encForgery_is_break_of_inj (spongeFamily D) SysRoots (rootsEnc D)
    (rootsEnc_inj D) (fun h => hne (fun i => congrFun h i)) ?_
  rw [← rootsEnc_faithful, ← rootsEnc_faithful]
  exact heq

/-- **⚑ THE FORGERY IS THE DEPLOYED ANTI-GHOST VIOLATION (commitment layer).** Two cells with EQUAL
canonical commitments over the same `rest` but DIFFERENT `system_roots` digests ARE a win — the
statement `cellCommitS_binds_systemRoots_or_collides` was reaching for. -/
theorem cellCommitS_forgery_is_break (D : SpongeKeyed) (rest : List FieldElem) (l : ℕ)
    (t : (spongeFamily D).Key l) {sr sr' : SysRoots}
    (hne : systemRootsDigest (D.hashAt t) sr ≠ systemRootsDigest (D.hashAt t) sr')
    (heq : cellCommitS (D.hashAt t) rest sr = cellCommitS (D.hashAt t) rest sr') :
    (cellCommitSBreakGame D rest).wins l t (sr, sr') := by
  refine encForgery_is_break (spongeFamily D) SysRoots (commitEnc D rest) ?_ heq
  intro h
  have happ : rest ++ [systemRootsDigest (D.hashAt t) sr]
      = rest ++ [systemRootsDigest (D.hashAt t) sr'] := h
  exact hne (by simpa using List.append_cancel_left happ)

/-! ## §3 — THE HEADLINE BINDINGS, as reductions, with efficiency DISCHARGED. -/

/-- The digest game's answer encoding — two eight-cell sub-blocks. -/
def sysRootsAnsSize (D : SpongeKeyed) : AnsSize (sysRootsBreakGame D) :=
  domainAnsSize (spongeFamily D) SysRoots (rootsEnc D) (fun _ _ => N_SYSTEM_ROOTS)

/-- The commitment game's answer encoding — the same two sub-blocks. -/
def cellCommitSAnsSize (D : SpongeKeyed) (rest : List FieldElem) :
    AnsSize (cellCommitSBreakGame D rest) :=
  domainAnsSize (spongeFamily D) SysRoots (commitEnc D rest) (fun _ _ => N_SYSTEM_ROOTS)

/-- The sponge collision game's answer encoding — the two claimed absorbed lists. -/
def spongeAnsSize (D : SpongeKeyed) : AnsSize (hashGame (spongeFamily D)) :=
  pairAnsSize (spongeFamily D) (fun _ xs => xs.length)

/-- The deployed sub-block is EXACTLY eight limbs wide — the layout fact that discharges the
`poly_time` output-growth slot at the digest layer. -/
theorem rootsEnc_width (D : SpongeKeyed) (l : ℕ)
    (t : (spongeFamily D).Key l) (sr : SysRoots) :
    (rootsEnc D l t sr).length ≤ N_SYSTEM_ROOTS := by
  simp [rootsEnc, rootList, N_SYSTEM_ROOTS]

/-- The deployed cell absorbs `rest` plus ONE digest limb — the commitment-layer width fact. -/
theorem commitEnc_width (D : SpongeKeyed) (rest : List FieldElem) (l : ℕ)
    (t : (spongeFamily D).Key l) (sr : SysRoots) :
    (commitEnc D rest l t sr).length ≤ rest.length + 1 := by
  simp [commitEnc]

/-- **⚑ THE `system_roots` BINDING — the headline, at an arbitrary adversary class.** Under the
deployed sponge's collision floor, a side-table-root forger whose extracted finder is in the class has
NEGLIGIBLE advantage: the committed digest binds all EIGHT consensus roots except with negligible
probability.  `hEff` is the honest open obligation; the next theorem discharges it. -/
theorem sysRoots_binds_advantage_bound (D : SpongeKeyed)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (sysRootsBreakGame D))
    (hEff : Eff (encBreakToFinder (spongeFamily D) SysRoots (rootsEnc D) A))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (sysRootsBreakGame D) A) :=
  encBinding_advantage_bound (spongeFamily D) SysRoots (rootsEnc D) Eff A hEff hCR

/-- **⚑ THE `system_roots` BINDING, WITH `hEff` DISCHARGED.** An EFFICIENT forger of the eight
consensus roots has negligible advantage under the deployed sponge's collision floor at
`Eff := IsPolyTime`.  The only per-site input is the encoder's declared work `(cw, bw)`; the
output-growth obligation is the eight-limb layout fact, PROVED.

⚑ This is what replaces `systemRootsDigest_binds_or_collides`, `_binds_fn_or_collides` and
`_binds_pointwise_or_collides` as the exported binding of the side-table roots. -/
theorem sysRoots_binds_from_polyTime (D : SpongeKeyed)
    (A : Adversary (sysRootsBreakGame D))
    (hA : IsPolyTime (sysRootsAnsSize D) A) (cw bw : ℕ)
    (hCR : HashCRHardQuant (spongeFamily D)
      (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (sysRootsBreakGame D) A) :=
  encBinding_from_polyTime_fixedWidth (spongeFamily D) SysRoots (rootsEnc D)
    (fun _ xs => xs.length) (fun _ _ => N_SYSTEM_ROOTS) N_SYSTEM_ROOTS
    (rootsEnc_width D) A hA cw bw hCR

/-- **⚑ THE CELL-COMMITMENT BINDING, WITH `hEff` DISCHARGED** — what replaces
`cellCommitS_binds_systemRoots_or_collides`.  An EFFICIENT forger that equivocates the absorbed
`system_roots` digest under one canonical commitment has negligible advantage. -/
theorem cellCommitS_binds_from_polyTime (D : SpongeKeyed) (rest : List FieldElem)
    (A : Adversary (cellCommitSBreakGame D rest))
    (hA : IsPolyTime (cellCommitSAnsSize D rest) A) (cw bw : ℕ)
    (hCR : HashCRHardQuant (spongeFamily D) (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (cellCommitSBreakGame D rest) A) :=
  encBinding_from_polyTime_fixedWidth (spongeFamily D) SysRoots (commitEnc D rest)
    (fun _ xs => xs.length) (fun _ _ => N_SYSTEM_ROOTS) (rest.length + 1)
    (commitEnc_width D rest) A hA cw bw hCR

/-! ## §4 — the FULL CHAIN (commitment ⟸ digest ⟸ sub-block), as a UNION BOUND.

`cellCommitS_binds_roots_pointwise_or_collides` exported a THREE-way bare disjunction — TWO escape
branches.  Here it is one game with two extractors and one floor: the standard union bound. -/

/-- **THE FULL-CHAIN FORGERY.** The adversary WINS iff two cells with the SAME canonical commitment
(over the same `rest`) disagree on ANY of the eight side-table roots.  This is the deployed soundness
statement for the whole `system_roots` sub-block: "the canonical commitment binds the whole side-table
state". -/
def cellRootsForgery (D : SpongeKeyed) (rest : List FieldElem) :
    KeyedForgery (spongeFamily D) where
  Ans := fun _ => SysRoots × SysRoots
  wins := fun _ t c =>
    (¬ (∀ i : Fin N_SYSTEM_ROOTS, c.1 i = c.2 i))
      ∧ cellCommitS (D.hashAt t) rest c.1 = cellCommitS (D.hashAt t) rest c.2
  winsDec := fun _ t c => by
    letI : DecidableEq SysRoots := Classical.decEq _
    exact inferInstance

/-- **THE PROBLEM IS IN THE STATEMENT.** -/
theorem cellRootsForgery_wins_iff (D : SpongeKeyed) (rest : List FieldElem) (l : ℕ)
    (t : (spongeFamily D).Key l) (c : SysRoots × SysRoots) :
    (cellRootsForgery D rest).wins l t c ↔
      ((¬ (∀ i : Fin N_SYSTEM_ROOTS, c.1 i = c.2 i))
        ∧ cellCommitS (D.hashAt t) rest c.1 = cellCommitS (D.hashAt t) rest c.2) :=
  Iff.rfl

/-- The commitment-layer extractor: hand the chain forger's answer straight to the commitment game. -/
def chainToCommit (D : SpongeKeyed) (rest : List FieldElem)
    (A : Adversary (cellRootsForgery D rest).game) : Adversary (cellCommitSBreakGame D rest) where
  run := A.run

/-- The digest-layer extractor: the SAME answer, read at the inner layer. -/
def chainToRoots (D : SpongeKeyed) (rest : List FieldElem)
    (A : Adversary (cellRootsForgery D rest).game) : Adversary (sysRootsBreakGame D) where
  run := A.run

/-- **⚑ THE CHAIN PEEL, AS A WIN IMPLICATION.** Every tag the chain forger wins, at least ONE layer
forger wins: either the two absorbed cell lists DIFFER (a commitment-layer break) or they AGREE — in
which case the two `system_roots` digests are equal while the sub-blocks differ, a digest-layer break.
This is `cellCommitS_binds_roots_pointwise_or_collides`'s case analysis, turned from an exported
disjunction into the internal step of a union bound. -/
theorem chain_wins_imp (D : SpongeKeyed) (rest : List FieldElem)
    (A : Adversary (cellRootsForgery D rest).game) (l : ℕ)
    (t : (spongeFamily D).Key l)
    (hwin : (cellRootsForgery D rest).wins l t (A.run l t)) :
    (cellCommitSBreakGame D rest).wins l t ((chainToCommit D rest A).run l t)
      ∨ (sysRootsBreakGame D).wins l t ((chainToRoots D rest A).run l t) := by
  obtain ⟨hne, heq⟩ := hwin
  by_cases hdig : systemRootsDigest (D.hashAt t) (A.run l t).1
      = systemRootsDigest (D.hashAt t) (A.run l t).2
  · exact Or.inr (sysRoots_forgery_is_break D l t hne hdig)
  · exact Or.inl (cellCommitS_forgery_is_break D rest l t hdig heq)

/-- **⚑ THE FULL-CHAIN BINDING — the headline that replaces the three-way disjunction.** Under ONE
collision floor for the deployed sponge, a forger that equivocates ANY of the eight side-table roots
under a fixed canonical cell commitment has NEGLIGIBLE advantage.  Two extracted finders, two
advantages, one floor, one negligible sum — the union bound, not an escape hatch.

⚑ This is what replaces `cellCommitS_binds_roots_pointwise_or_collides` as the exported claim: the
soundness statement STAGE 3 buys for ALL 8 side-tables, at deployed parameters, against EFFICIENT
adversaries. -/
theorem cellRoots_binds_advantage_bound (D : SpongeKeyed) (rest : List FieldElem)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (cellRootsForgery D rest).game)
    (hEff₁ : Eff (encBreakToFinder (spongeFamily D) SysRoots (commitEnc D rest)
      (chainToCommit D rest A)))
    (hEff₂ : Eff (encBreakToFinder (spongeFamily D) SysRoots (rootsEnc D)
      (chainToRoots D rest A)))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (cellRootsForgery D rest).game A) :=
  chained_binding_advantage_bound (cellRootsForgery D rest) SysRoots SysRoots
    (commitEnc D rest) (rootsEnc D) Eff A (chainToCommit D rest A) (chainToRoots D rest A)
    (chain_wins_imp D rest A) hEff₁ hEff₂ hCR

/-- **⚑ THE FULL-CHAIN BINDING, WITH BOTH `hEff`s DISCHARGED.** Both extracted finders are pure
post-maps of an EFFICIENT chain forger, so `poly_time` proves both efficient; the floor at
`Eff := IsPolyTime` then kills both advantages and their sum is negligible.  Nothing floats. -/
theorem cellRoots_binds_from_polyTime (D : SpongeKeyed) (rest : List FieldElem)
    (A : Adversary (cellRootsForgery D rest).game)
    (hA₁ : IsPolyTime (cellCommitSAnsSize D rest) (chainToCommit D rest A))
    (hA₂ : IsPolyTime (sysRootsAnsSize D) (chainToRoots D rest A))
    (cw bw : ℕ)
    (hCR : HashCRHardQuant (spongeFamily D) (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (cellRootsForgery D rest).game A) := by
  refine cellRoots_binds_advantage_bound D rest (IsPolyTime (spongeAnsSize D)) A ?_ ?_ hCR
  · rw [encBreakToFinder_eq_postMap]
    poly_time (cellCommitSAnsSize D rest) (spongeAnsSize D)
      (fun l (t : (spongeFamily D).Key l) (c : SysRoots × SysRoots) =>
        (commitEnc D rest l t c.1, commitEnc D rest l t c.2))
      cw bw 0 (2 * (rest.length + 1)) hA₁
    intro l t c
    have h1 := commitEnc_width D rest l t c.1
    have h2 := commitEnc_width D rest l t c.2
    show (commitEnc D rest l t c.1).length + (commitEnc D rest l t c.2).length
      ≤ 0 * (cellCommitSAnsSize D rest l c) + 2 * (rest.length + 1)
    omega
  · rw [encBreakToFinder_eq_postMap]
    poly_time (sysRootsAnsSize D) (spongeAnsSize D)
      (fun l (t : (spongeFamily D).Key l) (c : SysRoots × SysRoots) =>
        (rootsEnc D l t c.1, rootsEnc D l t c.2))
      cw bw 0 16 hA₂
    intro l t c
    have h1 := rootsEnc_width D l t c.1
    have h2 := rootsEnc_width D l t c.2
    show (rootsEnc D l t c.1).length + (rootsEnc D l t c.2).length
      ≤ 0 * (sysRootsAnsSize D l c) + 16
    simp only [N_SYSTEM_ROOTS] at h1 h2
    omega

/-! ## §5 — BOTH POLES of the floor, PROVED, plus the non-vacuity teeth. -/

/-- **⚑ THE ⊤ POLE — the floor is FALSE at the REAL BabyBear parameters** (the honest price of `hEff`).
A sponge whose output is a genuine field element has finite range on the infinite `List ℤ`, so a
collision exists at every tag and the floor at `Eff := ⊤` is FALSE.  What the reduction buys is not a
floor the deployed sponge satisfies at ⊤ — no such floor exists — it is one named parameter with both
poles proved, in place of an unconditionally-available disjunct. -/
theorem sysRoots_floor_top_false_babyBear (D : SpongeKeyed)
    (hb : ∀ xs : List ℤ, 0 ≤ D.sponge xs ∧ D.sponge xs < (2013265921 : ℤ)) :
    ¬ HashCRHardQuant (spongeFamily D) (fun _ => True) := by
  refine floor_top_false_of_compressing _ ⟨([] : List ℤ)⟩ (fun l t => ?_)
  refine exists_collision_of_not_injective
    (h := fun xs => (spongeFamily D).H l t xs) (fun hinj => ?_)
  refine Dregg2.Circuit.HashFloorHonesty.poseidon2SpongeCR_false_babyBear
    (fun xs => D.sponge (D.tagCode t ++ xs)) (fun xs => hb _) ?_
  intro xs ys hxy
  exact hinj xs ys hxy

/-- **THE ⊥ POLE — vacuous.** Recorded so the floor's satisfiability cannot be mistaken for evidence. -/
theorem sysRoots_floor_bot_vacuous (D : SpongeKeyed) :
    HashCRHardQuant (spongeFamily D) (fun _ => False) :=
  floor_bot_vacuous _

/-- **(TOOTH — the instantiated class is NOT EMPTY.)** The constant finder is in `IsPolyTime` at the
sponge game's own answer encoding, so `Eff := IsPolyTime` is not `⊥` in disguise.  With
`CostAdversary.bruteForce_not_polyTime` (the ⊤-collapse witness EXCLUDED) this pins the instantiated
floor strictly between the two poles. -/
theorem sysRoots_polyTime_class_inhabited (D : SpongeKeyed) :
    IsPolyTime (spongeAnsSize D)
      (Dregg2.Crypto.CostAdversary.idAdv (G := hashGame (spongeFamily D)) (O := Unit)
        (Q := fun _ => Unit) (R := fun _ => Unit)
        (fun _ _ => (([] : List ℤ), ([] : List ℤ)))).toAdversary :=
  isPolyTime_class_inhabited (spongeFamily D) (fun _ xs => xs.length) _
    ⟨0, 0, fun _ _ => by simp [pairAnsSize]⟩

/-- **(CANARY — the keystone does NOT follow from the floor applied at ANOTHER finder.)** Strip the
reduction and the binding does not go through: only `enc_adv_le` connects the extracted finder to the
forgery game.  Reds if a future edit collapses the two games. -/
example (D : SpongeKeyed)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (sysRootsBreakGame D))
    (B : Adversary (hashGame (spongeFamily D))) (hB : Eff B)
    (hCR : HashCRHardQuant (spongeFamily D) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (sysRootsBreakGame D) A) := hCR B hB)
  trivial

/-- **THE POSITIVE POLE — the RIGHT floor DOES discharge it.** A gate that refuses everything is a
broken keystone, not a fixed one. -/
theorem the_reduced_sysRoots_bound_fires (D : SpongeKeyed)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (sysRootsBreakGame D))
    (hEff : Eff (encBreakToFinder (spongeFamily D) SysRoots (rootsEnc D) A))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (sysRootsBreakGame D) A) :=
  sysRoots_binds_advantage_bound D Eff A hEff hCR

/-- **(TOOTH — a REFLEXIVE answer is never a win.)** The game does not hand the adversary a free win,
so the negligibility is not the negligibility of an unwinnable game's advantage in disguise. -/
theorem sysRoots_no_reflexive_break (D : SpongeKeyed) (l : ℕ)
    (t : (spongeFamily D).Key l) (sr : SysRoots) :
    ¬ (sysRootsBreakGame D).wins l t (sr, sr) :=
  no_reflexive_break (spongeFamily D) SysRoots (rootsEnc D) l t sr

/-! ## §6 — ⚑ THE INSTANTIATED FLOOR IS FALSE TOO, AT THE DEPLOYED SPONGE.

§5 prices the ⊤ pole and records that `Eff := IsPolyTime` sits STRICTLY BETWEEN the two poles AS A
CLASS.  That is true and it is not enough, and this section says why in Lean rather than in prose.

`CostAdversary.IsPolyTime sz A` is `∃ B : CostAdversary …, B.toAdversary = A ∧ PolyTime sz B`, and
`CostAdversary.idAdv a₀` accepts an ARBITRARY Lean function `a₀` — including a `Classical.choice` one —
as `.pure (a₀ l i)`, whose whole cost is `sz l (a₀ l i)`.  So the class contains EVERY adversary whose
ANSWERS are poly-size, no matter how hard those answers are to find:
`isPolyTime_of_polySize_answers` below is that observation, proved.

Consequently the floor at `Eff := IsPolyTime` is not the class restriction it reads as.  A compressing
sponge has SHORT collisions — the one-limb messages `[n]`, `n : ℤ`, are an infinite family landing in
one bounded field — so the choice adversary that answers with a short collision at every tag is in the
class, wins with probability `1`, and REFUTES the floor.  `sysRoots_floor_polyTime_false_babyBear` is
that refutation at the deployed BabyBear bound.

⚑ **WHAT THIS MEANS FOR THE HEADLINES ABOVE, STATED WITHOUT SOFTENING.**
`sysRoots_binds_from_polyTime`, `cellCommitS_binds_from_polyTime` and `cellRoots_binds_from_polyTime`
carry `HashCRHardQuant (spongeFamily D) (IsPolyTime (spongeAnsSize D))` as a hypothesis, and at the
deployed sponge that hypothesis is FALSE.  They are therefore VACUOUS at deployed parameters — the
same defect, one level up, as the `compressNInjective` bindings this whole repair deleted.  The
`_advantage_bound` forms are NOT vacuous: they quantify over an arbitrary class with `hEff` in the
open, and they are the honest content of this module.  What the `poly_time` discharge buys is that the
reduction's own efficiency is a THEOREM rather than an assumption; what it does NOT buy is a floor the
deployed sponge satisfies.

⚑ **THE DEFECT IS THE COST MODEL, NOT THIS SITE.** `IsPolyTime` measures OUTPUT SIZE plus DECLARED
syntactic work, and lets any Lean function be embedded at that price, so it cannot separate "writes a
short string" from "finds a collision".  Closing it needs the class to be a COMPUTABILITY-bounded (or
oracle-query-bounded) one — an adversary that must COMPUTE its answer from the tag — which is a change
to `Dregg2.Crypto.CostAdversary`, shared by every `_from_polyTime` in the tree.  Recording it here,
where it is provable at a deployed instance, rather than leaving it for a reader to find. -/

/-- **⚑ `IsPolyTime` IS EXACTLY "POLY-SIZE ANSWERS" (the ⊇ half, which is the damaging one).** Any
adversary at all — `Classical.choice`-defined, non-computable, whatever — is in the class as soon as
the answers it writes are poly-size, because `idAdv` embeds its `run` verbatim and charges only the
answer.  Nothing about finding the answer is priced. -/
theorem isPolyTime_of_polySize_answers {G : Dregg2.Crypto.FloorGames.Game}
    (sz : AnsSize G) (A : Adversary G)
    (hsz : ∃ C k : ℕ, ∀ l (i : G.Inst l), sz l (A.run l i) ≤ C * l ^ k + C) :
    IsPolyTime sz A :=
  Dregg2.Crypto.CostAdversary.isPolyTime_inhabited sz A.run hsz

/-- **A SHORT COLLISION AT EVERY TAG.** The one-limb messages `[n]` for `n : ℤ` are an infinite family
whose sponge images all land in `[0, p)` — so two of them collide, and the witness is TWO LIMBS TOTAL.
Pure pigeonhole (`HashFloorHonesty.not_injective_of_finite_range`), no Poseidon2 structure used. -/
theorem exists_short_collision (D : SpongeKeyed)
    (hb : ∀ xs : List ℤ, 0 ≤ D.sponge xs ∧ D.sponge xs < (2013265921 : ℤ))
    (l : ℕ) (t : (spongeFamily D).Key l) :
    ∃ p : List ℤ × List ℤ, (hashGame (spongeFamily D)).wins l t p
      ∧ p.1.length + p.2.length ≤ 2 := by
  have hfin : (Set.range (fun n : ℤ => D.sponge (D.tagCode t ++ [n]))).Finite := by
    refine (Set.finite_Ico (0 : ℤ) 2013265921).subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨(hb _).1, (hb _).2⟩
  have hni := Dregg2.Circuit.HashFloorHonesty.not_injective_of_finite_range
    (fun n : ℤ => D.sponge (D.tagCode t ++ [n])) hfin
  rw [Function.not_injective_iff] at hni
  obtain ⟨n, m, himg, hne⟩ := hni
  refine ⟨([n], [m]), ⟨fun h => hne ?_, himg⟩, by simp⟩
  injection h with h1 _

/-- **THE SHORT-COLLISION ADVERSARY** — answers every sampled tag with a two-limb collision. It is a
perfectly good `Adversary`: nothing in that type demands computability, and nothing in `IsPolyTime`
demands it either. -/
noncomputable def shortCollAdv (D : SpongeKeyed)
    (hb : ∀ xs : List ℤ, 0 ≤ D.sponge xs ∧ D.sponge xs < (2013265921 : ℤ)) :
    Adversary (hashGame (spongeFamily D)) where
  run := fun l t => (exists_short_collision D hb l t).choose

/-- It wins at EVERY tag. -/
theorem shortCollAdv_wins (D : SpongeKeyed)
    (hb : ∀ xs : List ℤ, 0 ≤ D.sponge xs ∧ D.sponge xs < (2013265921 : ℤ))
    (l : ℕ) (t : (spongeFamily D).Key l) :
    (hashGame (spongeFamily D)).wins l t ((shortCollAdv D hb).run l t) :=
  (exists_short_collision D hb l t).choose_spec.1

/-- And it is IN the class the headline theorems instantiate the floor at — two limbs is poly-size. -/
theorem shortCollAdv_isPolyTime (D : SpongeKeyed)
    (hb : ∀ xs : List ℤ, 0 ≤ D.sponge xs ∧ D.sponge xs < (2013265921 : ℤ)) :
    IsPolyTime (spongeAnsSize D) (shortCollAdv D hb) :=
  isPolyTime_of_polySize_answers _ _
    ⟨2, 0, fun l t => by
      have h := (exists_short_collision D hb l t).choose_spec.2
      simpa [spongeAnsSize, pairAnsSize, shortCollAdv] using h.trans (by omega)⟩

/-- **⚑ THE INSTANTIATED FLOOR IS FALSE AT THE DEPLOYED SPONGE.** So
`sysRoots_binds_from_polyTime` / `cellCommitS_binds_from_polyTime` / `cellRoots_binds_from_polyTime`
are VACUOUS at deployed BabyBear parameters, and the module's live content is the `_advantage_bound`
forms with `hEff` in the open.  This is the honest price of the `poly_time` discharge as
`Dregg2.Crypto.CostAdversary` currently defines the class, and it is a defect of that shared cost
model rather than of this instantiation. -/
theorem sysRoots_floor_polyTime_false_babyBear (D : SpongeKeyed)
    (hb : ∀ xs : List ℤ, 0 ≤ D.sponge xs ∧ D.sponge xs < (2013265921 : ℤ)) :
    ¬ HashCRHardQuant (spongeFamily D) (IsPolyTime (spongeAnsSize D)) := by
  intro hHard
  have hneg := hHard (shortCollAdv D hb) (shortCollAdv_isPolyTime D hb)
  have hone : gameAdv (hashGame (spongeFamily D)) (shortCollAdv D hb) = fun _ => (1 : ℝ) := by
    funext l
    show @Dregg2.Crypto.ProbCrypto.winProb _ ((hashGame (spongeFamily D)).instFin l) _ = 1
    have hall : (shortCollAdv D hb).hit l = fun _ => true := by
      funext t
      exact ((shortCollAdv D hb).hit_eq_true l t).mpr (shortCollAdv_wins D hb l t)
    rw [hall]
    exact @Dregg2.Crypto.ProbCrypto.winProb_top _ ((hashGame (spongeFamily D)).instFin l)
      ((hashGame (spongeFamily D)).instNe l)
  rw [hone] at hneg
  exact Dregg2.Crypto.ConcreteSecurity.not_negl_one hneg

#assert_axioms rootsEnc_faithful
#assert_axioms commitEnc_faithful
#assert_axioms rootsEnc_inj
#assert_axioms sysRoots_forgery_is_break
#assert_axioms cellCommitS_forgery_is_break
#assert_axioms rootsEnc_width
#assert_axioms commitEnc_width
#assert_axioms sysRoots_binds_advantage_bound
#assert_axioms sysRoots_binds_from_polyTime
#assert_axioms cellCommitS_binds_from_polyTime
#assert_axioms cellRootsForgery_wins_iff
#assert_axioms chain_wins_imp
#assert_axioms cellRoots_binds_advantage_bound
#assert_axioms cellRoots_binds_from_polyTime
#assert_axioms sysRoots_floor_top_false_babyBear
#assert_axioms sysRoots_floor_bot_vacuous
#assert_axioms sysRoots_polyTime_class_inhabited
#assert_axioms the_reduced_sysRoots_bound_fires
#assert_axioms sysRoots_no_reflexive_break
#assert_axioms isPolyTime_of_polySize_answers
#assert_axioms exists_short_collision
#assert_axioms shortCollAdv_wins
#assert_axioms shortCollAdv_isPolyTime
#assert_axioms sysRoots_floor_polyTime_false_babyBear

end Dregg2.Exec.SystemRootsBindingReduction
