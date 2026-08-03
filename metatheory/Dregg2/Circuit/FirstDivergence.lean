/-
# Dregg2.Circuit.FirstDivergence — THE COMBINATOR the ~40 hand-rolled repairs were each re-deriving.

**What this is.** Between 2026-08-01 and 2026-08-02 roughly forty theorems in this tree were ported
off an injectivity floor (`Poseidon2SpongeCR` and friends — FALSE at deployed BabyBear by counting,
so every conclusion conditioned on one was VACUOUSLY TRUE). Each port re-derived the same four
moves BY HAND: find the appeal `h a = h b ⊢ a = b`; build a TOTAL extractor that walks the structure
and returns the pair whose inputs DIVERGE while their images AGREE; restate as `conclusion ∨ Coll h
(extractor …)` INDEXED AT THAT PAIR; emit three teeth (`_unconditional_false`, `_refutable`,
`_fires`).

⚑ **The defects the audits caught were almost all INCONSISTENCY BETWEEN HAND-ROLLED INSTANCES, not
proof errors** — teeth stated about a different object than the residual they were cited as covering;
an `_unconditional_false` refuting a statement with different hypotheses than the one it was named
for. Those are the absence of a combinator. This module is the combinator.

**What was measured.** 81 `def …Find` extractors (77 distinct names; `recomposeUp8Find` and
`wideFoldColl8Find` each appear in several files) plus `peelPath`, and 235 `…_or_collides` theorems.
Every extractor body was read. Read in full first: `AggregationAirSound.aggCollFind`,
`StateTransitionAirSound.stCollFind`, `BindingAirSound.histCollFind`, `Crypto.HashSigMerkle.pkLeafFind`,
`Substrate.Heap.mapLeafFind`/`rootFind`, `Circuit.MapOpsColumnLayout.pathCollFind`,
`Circuit.FriCompressRegrounded.peelPath`, plus `Circuit.CollisionReduce`.

**What the measurement says.** They are **NOT all "first divergence over a traversal"** — that
hypothesis is REFUTED. They are COMPOSITIONS OF FIVE PIECES, all five built here. Counted at each
site's OUTERMOST skeleton: leaf ≈27, pick ≈31, zip ≈8, fold 3, climb ≈9, genuinely site-specific ≈4.

  * `leafPair` — depth 0: `(enc a, enc b)`. `pkLeafFind`, `Heap.addrFind`,
    `DeployedCapTree.leafCollFind`/`nodeCollFind`, `FinFrameHash.frameCollFind`, … — the single
    largest family in the census.
  * `pick` — LAYER SELECTION: `if outer.1 = outer.2 then inner else outer`. `Heap.rootFind`,
    `MapOpWideKeyGate.mapRootWFind`, `MMR.collFind`/`bagFind`, `ReceiptChain8.rchainR8Find`, …
  * `zipFirst` — FIRST divergence over two lists whose images agree POINTWISE. `Heap.mapLeafFind`,
    `MapOpWideKeyGate.mapLeafWFind`, `DeployedMapDenotation.imtLeafFind`, …
  * `foldLast` — an ACCUMULATING fold, decided POST-ORDER. `aggCollFind`, `stCollFind`,
    `histCollFind` (exactly three sites, and they are byte-for-byte the same recursion).
  * `climb` — the SAME `foldOf` walked the other way, decided PRE-ORDER, in the DUAL polarity: the
    hypothesis is *inputs differ* and the conclusion is a bare collision with NO good branch.
    `peelPath`, `FloorRegroundedConsumers.merklePathCollFind`, `OodCommitmentBinding.merkleFind`,
    `CapMerkleGeneric.recomposeGFind`, `Emit/WireCommitBindsOrCollides.chainCollFind1`. See §3c;
    §7 says why `MapOpsColumnLayout.pathCollFind` is a separate shape AGAIN.

⚑ **`foldLast` IS NOT FIRST-DIVERGENCE, and the difference is load-bearing.** In `zipFirst` the
images agree at EVERY index by hypothesis, so the walk may stop at the first differing position. In
`foldLast` the images are known equal only at the END of the fold, and equality at level `i` is
DERIVED from non-divergence at level `i+1`; the walk must therefore recurse to the deepest level
first and prefer the DEEPER pair. Read in the direction information actually flows — backwards from
the digest — it IS a first divergence; read in the direction the list is written, it is a last one.
Anyone who "simplifies" `foldLast` into `zipFirst` breaks it.

**What the signature buys.** §2 proves the two refused shapes are refused FOR A REASON, generically:
`forall_noColl_iff_injective` (a `∀`-quantified residual IS the floor rewritten) and
`globalBreak_free` (a `∃`-quantified break is FREE at any non-injective hash — the generic form of
`SpongeCollisionShirk.orBreak_spongeCollision_iff_True`), against `indexedBreak_not_free` (the
indexed form is NOT). §5's `Site`/`Teeth` bundle makes the measured defect a TYPE ERROR: every
tooth is stated against the SAME `Hyp`/`Good`/`find` fields the keystone is, so an
`_unconditional_false` about a different statement cannot be written down.

Nothing here assumes anything about any hash. `Coll` contains no existential and no quantifier at
all: it is a predicate ON A PAIR.
-/
import Dregg2.Tactics

namespace Dregg2.Circuit.FirstDivergence

universe u v w x

/-! ## 1. THE RESIDUAL — a collision AT A NAMED PAIR, with no quantifier in it. -/

/-- **`Coll h p`** — the pair `p` is a genuine collision of `h`: DISTINCT inputs, EQUAL images.

⚑ The pair is an ARGUMENT, not an existential. Definitionally identical to the tree's
`Poseidon2Binding.SpongeColl` and `SpongeCarrierReduction.IsSpongeColl` at `π := List ℤ, α := ℤ`,
so a site can be re-derived through this module and keep its exported statement byte-for-byte. -/
def Coll {π : Type u} {α : Type v} (h : π → α) (p : π × π) : Prop :=
  p.1 ≠ p.2 ∧ h p.1 = h p.2

variable {π : Type u} {α : Type v} {ρ : Type w} {κ : Type x}

/-- Deciding "is this pair a collision" is a COMPUTATION, so every extractor below may branch on it
and stay total with no `Classical.choose` in the walk. -/
instance instDecidableColl [DecidableEq π] [DecidableEq α] (h : π → α) (p : π × π) :
    Decidable (Coll h p) := by unfold Coll; infer_instance

theorem Coll.ne {h : π → α} {p : π × π} (hc : Coll h p) : p.1 ≠ p.2 := hc.1

theorem Coll.img {h : π → α} {p : π × π} (hc : Coll h p) : h p.1 = h p.2 := hc.2

/-- **THE DISCHARGE RULE.** An extractor that bottomed out at an EQUAL pair has found nothing, so
the residual is refuted — for EVERY `h`, with no cryptographic hypothesis at all. Every `_fires`
tooth in the tree is this lemma plus a `self_eq` for the particular walk. -/
theorem noColl_of_eq {h : π → α} {p : π × π} (hp : p.1 = p.2) : ¬ Coll h p := fun hc => hc.1 hp

/-! ## 2. ⚑ THE REFUSALS — the two shapes this combinator must not let a caller write, PROVED
degenerate, generically.

The brief's four failure shapes, and where each dies:

 1. `P ∨ Break` with `Break` a GLOBAL EXISTENTIAL is FREE — `globalBreak_free` below proves it for
    ANY non-injective `h`, so the pigeonhole that refutes a floor ESTABLISHES the break. `Coll` has
    no existential in it; the only way back to this shape is to write `∃ p, Coll h p` explicitly,
    which is now a named, refuted object rather than an accident.
 2. A `∀`-quantified side condition IS injectivity — `forall_noColl_iff_injective`, an `Iff`, so
    there is nothing to argue about.
 3. A residual quantified OUTSIDE the claim rather than INDEXED BY the pair — `Site.sound` (§5) has
    the `∀ h i` OUTERMOST and both disjuncts under it, and `Site.binds` hands the caller a residual
    at `S.find h i` for the SAME `h` and `i` the conclusion is stated at. `indexedBreak_not_free`
    is the separation: the indexed form is NOT discharged by non-injectivity.
 4. A conclusion that IS the break event — `Teeth.broken_good_false` (§5) demands the conclusion
    FAIL at the broken hash, which a break-event conclusion cannot do. (The real gate for this one
    is `Verify/FreeConclusionRatchet`'s idle-hypothesis test; this is a tripwire, not a replacement.) -/

/-- **FAILURE SHAPE 2, PROVED.** A residual quantified over ALL pairs is EXACTLY injectivity of `h`
— the floor, rewritten. Not "similar to": an `Iff`. -/
theorem forall_noColl_iff_injective (h : π → α) :
    (∀ p : π × π, ¬ Coll h p) ↔ Function.Injective h := by
  constructor
  · intro hall a b hab
    by_contra hne
    exact hall (a, b) ⟨hne, hab⟩
  · intro hinj p hc
    exact hc.1 (hinj hc.2)

/-- The global existential break is EXACTLY the negation of the floor. -/
theorem exists_coll_iff_not_injective (h : π → α) :
    (∃ p : π × π, Coll h p) ↔ ¬ Function.Injective h := by
  constructor
  · rintro ⟨p, hne, himg⟩ hinj
    exact hne (hinj himg)
  · intro hni
    by_contra hex
    exact hni ((forall_noColl_iff_injective h).mp (fun p hc => hex ⟨p, hc⟩))

/-- **FAILURE SHAPE 1, PROVED.** At any NON-INJECTIVE `h` — which is every hash this tree deploys,
by `HashFloorHonesty.poseidon2SpongeCR_false_babyBear`'s counting argument — the global-existential
disjunct is FREE: it holds for an ARBITRARY `P`, including a false one. The generic form of
`SpongeCollisionShirk.orBreak_spongeCollision_iff_True`. -/
theorem globalBreak_free (h : π → α) (hni : ¬ Function.Injective h) (P : Prop) :
    P ∨ ∃ p : π × π, Coll h p :=
  Or.inr ((exists_coll_iff_not_injective h).mpr hni)

/-- **THE SEPARATION — and it is the whole point of indexing.** The INDEXED disjunct is NOT free:
non-injectivity of `h` does not discharge `P ∨ Coll h p` at a NAMED pair `p`. Witnessed at the
collapsing sponge `fun _ => 0` (maximally non-injective) and the pair `([], [])`, where the residual
is refuted by `noColl_of_eq` while `P := False`. Same symbols as `globalBreak_free`, opposite
content. -/
theorem indexedBreak_not_free :
    ¬ ∀ (h : List ℤ → ℤ), ¬ Function.Injective h →
        ∀ (p : List ℤ × List ℤ) (P : Prop), P ∨ Coll h p := by
  intro hall
  have hni : ¬ Function.Injective (fun _ : List ℤ => (0 : ℤ)) := by
    intro hinj
    have h01 : ([] : List ℤ) = [0] := hinj rfl
    simp at h01
  rcases hall _ hni ([], []) False with hF | hc
  · exact hF
  · exact hc.1 rfl

/-! ## 3. THE ALGEBRA — three total, decidable extractor pieces. Each returns a PAIR; each has an
unconditional soundness lemma and a `self_eq` (the `_fires` tooth's engine). -/

/-- **DEPTH 0 — the leaf.** The two encoded preimages, verbatim. The largest family in the census:
`HashSigMerkle.pkLeafFind`, `Heap.addrFind`, `DeployedCapTree.leafCollFind`/`nodeCollFind`,
`DeployedFieldsTree.fieldsLeafColl8Find`, `FinFrameHash.frameCollFind`/`restCollFind`,
`CommitmentBinding.Compress2.nodeCollFind`, … -/
def leafPair (enc : ρ → π) (a b : ρ) : π × π := (enc a, enc b)

/-- **THE LEAF DICHOTOMY — UNCONDITIONAL, NO FLOOR.** Two values sharing a hashed leaf either are
equal, or the named pair of their encodings is a genuine collision. Nothing is assumed about `h`. -/
theorem leafPair_binds_or_coll (h : π → α) (enc : ρ → π) (henc : Function.Injective enc)
    (a b : ρ) (heq : h (enc a) = h (enc b)) : a = b ∨ Coll h (leafPair enc a b) := by
  by_cases he : enc a = enc b
  · exact Or.inl (henc he)
  · exact Or.inr ⟨he, heq⟩

/-- **THE LEAF FIRES.** One value against itself discharges the residual for EVERY `h`. -/
theorem leafPair_self_eq (enc : ρ → π) (a : ρ) : (leafPair enc a a).1 = (leafPair enc a a).2 := rfl

/-- **LAYER SELECTION.** Prefer the OUTER candidate when it genuinely diverges; otherwise the outer
preimages agree and the break must be INSIDE, so hand back the inner walk's pair. This one
combinator is `Heap.rootFind`, `MapOpWideKeyGate.mapRootWFind`, `MapOpWideDigest8.mapRootW8Find`,
`MMR.collFind`/`bagFind`, `ReceiptChain8.rchainR8Find` — and, with the arguments swapped, the
`if deep.1 = deep.2 then thisLevel else deep` step of every `foldLast` site. -/
def pick [DecidableEq π] (outer inner : π × π) : π × π :=
  if outer.1 = outer.2 then inner else outer

/-- **`pick` IS SOUND — UNCONDITIONAL.** If the outer pair's images agree, and the inner walk
delivers a collision whenever the outer pair does not diverge, then `pick` delivers a collision. -/
theorem pick_coll [DecidableEq π] (h : π → α) {outer inner : π × π}
    (houter : h outer.1 = h outer.2) (hinner : outer.1 = outer.2 → Coll h inner) :
    Coll h (pick outer inner) := by
  unfold pick
  by_cases he : outer.1 = outer.2
  · rw [if_pos he]; exact hinner he
  · rw [if_neg he]; exact ⟨he, houter⟩

/-- **`pick` FIRES.** Both candidates bottoming out equal keeps the selection equal, so the residual
is discharged for EVERY `h`. -/
theorem pick_self_eq [DecidableEq π] {outer inner : π × π}
    (ho : outer.1 = outer.2) (hi : inner.1 = inner.2) : (pick outer inner).1 = (pick outer inner).2 := by
  unfold pick; rw [if_pos ho]; exact hi

/-- **FIRST DIVERGENCE over two lists whose images agree POINTWISE.** Walk in step; at the first
position whose encodings differ, hand back that position's two preimages. Total: the fallback pair
is equal, hence never a collision. `Heap.mapLeafFind`, `MapOpWideKeyGate.mapLeafWFind`,
`DeployedMapDenotation.imtLeafFind`, `MapMerkleRoot.mapLeaf8Find`.

Branching on `enc a = enc b` rather than `a = b` needs only `DecidableEq π` and makes `self_eq`
floor-free; under injective `enc` the two tests agree. -/
def zipFirst [DecidableEq π] [Inhabited π] (enc : ρ → π) : List ρ → List ρ → π × π
  | a :: as, b :: bs => if enc a = enc b then zipFirst enc as bs else leafPair enc a b
  | _, _ => (default, default)

/-- **THE ZIP FIRES.** One list against itself bottoms out at an EQUAL pair, for EVERY `h`. -/
theorem zipFirst_self_eq [DecidableEq π] [Inhabited π] (enc : ρ → π) (l : List ρ) :
    (zipFirst enc l l).1 = (zipFirst enc l l).2 := by
  induction l with
  | nil => rfl
  | cons a as ih => rw [zipFirst, if_pos rfl]; exact ih

/-- **THE ZIP IS CORRECT — UNCONDITIONAL, NO FLOOR.** Two lists with EQUAL pointwise images either
are equal, or `zipFirst` names a genuine collision of `h`. Nothing is assumed about `h`.

The good branch also reports that the walk found nothing (`.1 = .2`), which is what a caller
threading this into a larger `pick` needs. -/
theorem zipFirst_binds_or_coll [DecidableEq π] [Inhabited π] (h : π → α) (enc : ρ → π)
    (henc : Function.Injective enc) :
    ∀ l₁ l₂ : List ρ, l₁.map (fun x => h (enc x)) = l₂.map (fun x => h (enc x)) →
      (l₁ = l₂ ∧ (zipFirst enc l₁ l₂).1 = (zipFirst enc l₁ l₂).2)
      ∨ Coll h (zipFirst enc l₁ l₂) := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ hmap
    cases l₂ with
    | nil => exact Or.inl ⟨rfl, rfl⟩
    | cons b bs => simp at hmap
  | cons a as ih =>
    intro l₂ hmap
    cases l₂ with
    | nil => simp at hmap
    | cons b bs =>
      simp only [List.map_cons, List.cons.injEq] at hmap
      obtain ⟨hhead, htail⟩ := hmap
      by_cases he : enc a = enc b
      · have hstep : zipFirst enc (a :: as) (b :: bs) = zipFirst enc as bs := by
          rw [zipFirst, if_pos he]
        rw [hstep]
        rcases ih bs htail with ⟨heq, hfound⟩ | hc
        · exact Or.inl ⟨by rw [henc he, heq], hfound⟩
        · exact Or.inr hc
      · have hstep : zipFirst enc (a :: as) (b :: bs) = leafPair enc a b := by
          rw [zipFirst, if_neg he]
        rw [hstep]
        exact Or.inr ⟨he, hhead⟩

/-! ### 3b. THE ACCUMULATING FOLD — the `aggCollFind`/`stCollFind`/`histCollFind` recursion, once. -/

/-- The ordered hash fold every digest-chain AIR in this tree publishes: from `a`, absorb each row
and re-hash. `AggregationAirSound.aggFold`, `StateTransitionAirSound.stFold`,
`BindingAirSound.histDigest` are this at three different `absorb`s. -/
def foldOf (h : π → α) (absorb : α → ρ → π) : α → List ρ → α
  | a, []      => a
  | a, r :: rs => foldOf h absorb (h (absorb a r)) rs

/-- **⚑ THE FOLD EXTRACTOR — POST-ORDER, and that is not an implementation detail.** Recurse to the
DEEPEST level first: a deeper named pair is DISTINCT by construction and is returned unchanged
(`pick` prefers it); otherwise the deeper accumulators provably agree and THIS level's two absorbed
preimages are where the two folds can differ. Runs off the end at an equal pair.

The equality the caller has is at the END of the fold, so the information flows BACKWARD; a
front-first `zipFirst`-style walk has nothing to decide with at level 0. -/
def foldLast [DecidableEq π] [Inhabited π] (h : π → α) (absorb : α → ρ → π) :
    α → α → List ρ → List ρ → π × π
  | a, b, r :: rs, r' :: rs' =>
      pick (foldLast h absorb (h (absorb a r)) (h (absorb b r')) rs rs') (absorb a r, absorb b r')
  | _, _, _, _ => (default, default)

/-- **THE FOLD FIRES.** One history against itself bottoms out at an EQUAL pair at every level, so
the residual is discharged for EVERY `h` — no floor, no cryptographic hypothesis. -/
theorem foldLast_self_eq [DecidableEq π] [Inhabited π] (h : π → α) (absorb : α → ρ → π) :
    ∀ (rs : List ρ) (a : α), (foldLast h absorb a a rs rs).1 = (foldLast h absorb a a rs rs).2 := by
  intro rs
  induction rs with
  | nil => intro a; rfl
  | cons r rest ih =>
    intro a
    rw [foldLast]
    exact pick_self_eq (ih (h (absorb a r))) rfl

/-- **⚑ THE FOLD EXTRACTOR IS CORRECT — UNCONDITIONAL, NO FLOOR.** Two equal-length row lists folded
to the SAME digest EITHER agree on the starting accumulator and on the whole ordered `proj`
projection, OR `foldLast` names a GENUINE collision of `h`. Nothing is assumed about `h`, so this is
TRUE at deployed parameters — unlike every injectivity-conditioned binding it replaces.

`absorbSplits` is the ONLY property of `absorb` the three ported sites use: an absorbed preimage
determines the accumulator it was taken at and the row's committed projection. `proj` is a
projection rather than the row itself because the deployed row structs carry lanes the digest never
absorbs (`AggRow.accIn`/`accOut` are threaded by the continuity tooth, not by the hash).

The good branch also reports that the walk found nothing; that conjunct is what lets the induction
step know the deeper walk is exhausted and this level's pair is the one `pick` returns. -/
theorem foldLast_binds_or_coll [DecidableEq π] [Inhabited π]
    (h : π → α) (absorb : α → ρ → π) (proj : ρ → κ)
    (absorbSplits : ∀ (a b : α) (r r' : ρ), absorb a r = absorb b r' → a = b ∧ proj r = proj r') :
    ∀ (rs rs' : List ρ) (a b : α),
      rs.length = rs'.length →
      foldOf h absorb a rs = foldOf h absorb b rs' →
      (a = b ∧ rs.map proj = rs'.map proj
        ∧ (foldLast h absorb a b rs rs').1 = (foldLast h absorb a b rs rs').2)
      ∨ Coll h (foldLast h absorb a b rs rs') := by
  intro rs
  induction rs with
  | nil =>
    intro rs' a b hlen heq
    cases rs' with
    | nil => exact Or.inl ⟨heq, rfl, rfl⟩
    | cons r' rest' => simp at hlen
  | cons r rest ih =>
    intro rs' a b hlen heq
    cases rs' with
    | nil => simp at hlen
    | cons r' rest' =>
      have hlen' : rest.length = rest'.length := by simpa using hlen
      simp only [foldOf] at heq
      rw [foldLast]
      rcases ih rest' (h (absorb a r)) (h (absorb b r')) hlen' heq with
        ⟨hinner, htail, hdeep⟩ | hcoll
      · -- the deeper walk found nothing, so `pick` returns THIS level's absorbed pair.
        rw [pick, if_pos hdeep]
        by_cases hpre : absorb a r = absorb b r'
        · obtain ⟨hacc, hproj⟩ := absorbSplits a b r r' hpre
          exact Or.inl ⟨hacc, by simp only [List.map_cons, hproj, htail], hpre⟩
        · exact Or.inr ⟨hpre, hinner⟩
      · -- the deeper walk NAMED a pair; a named pair is DISTINCT, so `pick` returns it unchanged.
        rw [pick, if_neg hcoll.1]
        exact Or.inr hcoll

/-! ### 3c. ⚑ THE SAME FOLD, WALKED THE OTHER WAY — the Merkle/chain CLIMB.

`foldLast` and `climb` are the SAME `foldOf`, at the SAME `absorb`, under OPPOSITE invariants:

  * `foldLast` — TWO different step lists, images known equal at the END. Invariant: *the images
    agree*. Decided POST-ORDER. Conclusion: the lists agree, OR a collision. (`aggCollFind`,
    `stCollFind`, `histCollFind`.)
  * `climb` — ONE SHARED step list, accumulators known DISTINCT at the START. Invariant: *the
    accumulators differ*. Decided PRE-ORDER. Conclusion: a collision, FULL STOP — there is no good
    branch, because distinct leaves reaching one root is already the break.
    (`FriCompressRegrounded.peelPath`, `FloorRegroundedConsumers.merklePathCollFind`,
    `OodCommitmentBinding.merkleFind`, `CapMerkleGeneric.recomposeGFind`, and the accumulating chains
    `Emit/WireCommitBindsOrCollides.chainCollFind1` / `Emit/EffectVmEmitRotationR.chainCollFind`.)

⚑ **MEASURED FINDING: the accumulating-hash-chain family carries BOTH schedulings, hand-rolled.**
`chainCollFind1` and `aggCollFind` walk the same kind of object — an accumulator re-hashed against
per-level material — and were written with opposite orders and incompatible spec shapes by different
hands. Neither is wrong; they were simply never reconciled, which is the inconsistency this module
exists to remove. -/

/-- **THE CLIMB.** Walk a shared path from the leaves toward the root; return the FIRST level whose
two images already agree on distinct inputs, otherwise descend with the two new (still distinct)
accumulators. Runs off the end only on inputs `climb_wins` excludes. -/
def climb [DecidableEq α] [Inhabited π] (h : π → α) (absorb : α → ρ → π) :
    α → α → List ρ → π × π
  | _, _, []      => (default, default)
  | a, b, g :: gs =>
      if h (absorb a g) = h (absorb b g) then (absorb a g, absorb b g)
      else climb h absorb (h (absorb a g)) (h (absorb b g)) gs

/-- **THE CLIMB IS CORRECT — UNCONDITIONAL, NO FLOOR, AND NO GOOD BRANCH.** Two DISTINCT
accumulators whose folds over the SAME path agree yield a genuine collision of `h`. `absorbDistinct`
is the only property of `absorb` used: absorbing distinct accumulators against the same level
material keeps them distinct (for a Merkle node it is injectivity of the ordered pair).

⚠ Do NOT restate this as `a = b ∨ Coll h (climb …)`: `a ≠ b` is a HYPOTHESIS here, so the good
branch would be empty and the statement strictly weaker than what is proved. -/
theorem climb_wins [DecidableEq α] [Inhabited π] (h : π → α) (absorb : α → ρ → π)
    (absorbDistinct : ∀ (a b : α) (g : ρ), a ≠ b → absorb a g ≠ absorb b g) :
    ∀ (gs : List ρ) (a b : α), a ≠ b →
      foldOf h absorb a gs = foldOf h absorb b gs → Coll h (climb h absorb a b gs) := by
  intro gs
  induction gs with
  | nil => intro a b hne heq; exact absurd heq hne
  | cons g rest ih =>
    intro a b hne heq
    simp only [foldOf] at heq
    by_cases hc : h (absorb a g) = h (absorb b g)
    · rw [climb, if_pos hc]
      exact ⟨absorbDistinct a b g hne, hc⟩
    · rw [climb, if_neg hc]
      exact ih (h (absorb a g)) (h (absorb b g)) hc heq

/-! ## 4. THE KEYSTONE FORM — `.resolve_right` at the named pair, once. -/

/-- **THE CONSUMER ENTRY POINT.** A dichotomy plus the per-instance residual AT THE PAIR THE SAME
DICHOTOMY NAMES gives the conclusion. Trivial as a proof and load-bearing as a shape: the residual
argument's type mentions `p`, which is the extractor applied to the very data the conclusion is
about, so it cannot be a `∀`-quantified side condition and cannot float outside the claim. -/
theorem resolve {P : Prop} {h : π → α} {p : π × π}
    (d : P ∨ Coll h p) (hno : ¬ Coll h p) : P := d.resolve_right hno

/-- **THE UNIVERSAL BRIDGE, GENERIC.** A consumer still holding the (refuted) floor discharges the
residual at EVERY extractor output through one application — quantified over the PAIR, so porting a
site mints no new carrier. The tree's `Poseidon2Binding.spongeColl_refutable_of_injective` is this
at `π := List ℤ, α := ℤ`; DO NOT mint per-site `_of_CR` twins. -/
theorem noColl_of_injective (h : π → α) (hinj : Function.Injective h) (p : π × π) : ¬ Coll h p :=
  (forall_noColl_iff_injective h).mpr hinj p

/-! ## 5. ⚑ THE BUNDLE — the four teeth, forced to be about the SAME statement.

This is the part that kills the measured defect class. The audits found teeth stated about a
DIFFERENT object than the residual they were cited as covering, and an `_unconditional_false`
refuting a statement with DIFFERENT hypotheses than the one it was named for (twice, in two files,
one of them reproducing the error a sibling lane was repairing in the same workflow). Those are
possible only because each tooth was an independently-written top-level theorem.

Here `Hyp`, `Good` and `find` are FIELDS. `sound` and every tooth are typed against those same
fields, so a tooth about a different statement does not typecheck. -/

/-- **A REPAIRED SITE.** `ι` is whatever the site quantifies over (rows, heaps, openings, …).
`Hyp` is the equal-image hypothesis, `Good` the conclusion, `find` the total extractor, `sound` the
floor-free dichotomy — with the `∀ h i` OUTERMOST and BOTH disjuncts under it, so the residual is
indexed by the pair it ranges over rather than quantified outside the claim. -/
structure Site (π : Type u) (α : Type v) (ι : Type w) where
  /-- the site's equal-image hypothesis (e.g. "these two folds published the same digest") -/
  Hyp   : (π → α) → ι → Prop
  /-- the site's conclusion -/
  Good  : (π → α) → ι → Prop
  /-- the TOTAL extractor -/
  find  : (π → α) → ι → π × π
  /-- ⚑ UNCONDITIONAL: no hypothesis on `h` anywhere. -/
  sound : ∀ (h : π → α) (i : ι), Hyp h i → Good h i ∨ Coll h (find h i)

/-- **THE KEYSTONE, GENERATED.** The residual is at `S.find h i` for the SAME `h` and `i` the
conclusion is stated at — mechanically, once, for every site that goes through the bundle. -/
theorem Site.binds {ι : Type w} (S : Site π α ι) (h : π → α) (i : ι)
    (hy : S.Hyp h i) (hno : ¬ Coll h (S.find h i)) : S.Good h i :=
  (S.sound h i hy).resolve_right hno

/-- **A REPAIRED SITE WITH ITS TEETH.** A repair is not done when it compiles; it is done when the
residual is shown SATISFIABLE (`fires`, at an honest index, for EVERY hash, with no floor),
REFUTABLE (`broken_coll`, the extractor really returns a collision at a broken hash) and
LOAD-BEARING (`broken_hyp` + `broken_good_false`: dropping it makes the binding FALSE).

⚑ `broken_hyp` and `broken_good_false` are stated against the SAME `Hyp` and `Good` fields as
`sound`. The measured defect — a `_unconditional_false` refuting a statement with different
hypotheses than the keystone it was named for — is a TYPE ERROR here.

⚑ `broken_good_false` also tripwires failure shape 4: if `Good` were the break event itself, it
would HOLD at the broken hash and this field would be unprovable. The real gate for shape 4 remains
`Verify/FreeConclusionRatchet`'s idle-hypothesis test. -/
structure Teeth (π : Type u) (α : Type v) (ι : Type w) extends Site π α ι where
  /-- the indices an honest party actually produces (typically "the two sides coincide") -/
  Honest : ι → Prop
  /-- ⚑ SATISFIABLE, FOR EVERY HASH: an honest index discharges the residual with NO floor. -/
  fires : ∀ (h : π → α) (i : ι), Honest i → ¬ Coll h (find h i)
  /-- a hash at which the site genuinely breaks -/
  brokenHash : π → α
  /-- an index at which it genuinely breaks -/
  brokenIdx : ι
  /-- the site's hypothesis HOLDS there … -/
  broken_hyp : Hyp brokenHash brokenIdx
  /-- … and its conclusion FAILS there, so the residual is LOAD-BEARING … -/
  broken_good_false : ¬ Good brokenHash brokenIdx
  /-- … and the extractor really RETURNS the collision, so the residual is REFUTABLE. -/
  broken_coll : Coll brokenHash (find brokenHash brokenIdx)

variable {ι : Type w}

/-- **TOOTH 1 — LOAD-BEARING (`*_unconditional_false`), GENERATED.** Dropping the residual makes the
binding FALSE. Derived from `broken_hyp`/`broken_good_false`, which are typed against the very
`Hyp`/`Good` the keystone uses — so this cannot drift onto a different statement. -/
theorem Teeth.unconditional_false (T : Teeth π α ι) :
    ¬ ∀ (h : π → α) (i : ι), T.Hyp h i → T.Good h i :=
  fun hall => T.broken_good_false (hall _ _ T.broken_hyp)

/-- **TOOTH 2 — REFUTABLE (`*_refutable`), GENERATED.** The residual really can fail: at the broken
hash the extractor returns a genuine collision, so the keystone does not discharge itself by taking
the right branch. -/
theorem Teeth.refutable (T : Teeth π α ι) :
    Coll T.brokenHash (T.find T.brokenHash T.brokenIdx) := T.broken_coll

/-- The residual is not a `True` in disguise — stated as the refutation of the universal claim that
it always holds, which is the form a reader checking for laundering wants. -/
theorem Teeth.residual_not_trivial (T : Teeth π α ι) :
    ¬ ∀ (h : π → α) (i : ι), ¬ Coll h (T.find h i) :=
  fun hall => hall _ _ T.broken_coll

/-- **TOOTH 3 — FIRES (`*_fires`), GENERATED.** At an honest index the conclusion holds for EVERY
hash — no floor, no cryptographic hypothesis — so the repaired keystone genuinely fires at deployed
parameters. This is the separation a global-existential disjunct provably cannot make
(`globalBreak_free` vs `indexedBreak_not_free`). -/
theorem Teeth.fires_good (T : Teeth π α ι) (h : π → α) (i : ι)
    (hon : T.Honest i) (hy : T.Hyp h i) : T.Good h i :=
  T.toSite.binds h i hy (T.fires h i hon)

/-- **TOOTH 4 — THE REFUTATION, NOT A NEW FLOOR.** Exhibiting the residual REFUTES injectivity
outright, so a port through this bundle is a strict WEAKENING of the premise it replaces. Stated
contrapositively so it assumes no floor content. -/
theorem Teeth.coll_refutes_injective {h : π → α} {p : π × π} (hc : Coll h p) :
    ¬ Function.Injective h := fun hinj => hc.1 (hinj hc.2)

/-! ## 6. Axiom hygiene. -/

#assert_axioms noColl_of_eq
#assert_axioms forall_noColl_iff_injective
#assert_axioms exists_coll_iff_not_injective
#assert_axioms globalBreak_free
#assert_axioms indexedBreak_not_free
#assert_axioms leafPair_binds_or_coll
#assert_axioms leafPair_self_eq
#assert_axioms pick_coll
#assert_axioms pick_self_eq
#assert_axioms zipFirst_self_eq
#assert_axioms zipFirst_binds_or_coll
#assert_axioms foldLast_self_eq
#assert_axioms foldLast_binds_or_coll
#assert_axioms climb_wins
#assert_axioms resolve
#assert_axioms noColl_of_injective
#assert_axioms Site.binds
#assert_axioms Teeth.unconditional_false
#assert_axioms Teeth.refutable
#assert_axioms Teeth.residual_not_trivial
#assert_axioms Teeth.fires_good
#assert_axioms Teeth.coll_refutes_injective

/-! ## 7. ⚠ WHAT THIS COMBINATOR REFUSES, AND WHY — read before trying to force a site through it.

**(a) A CLIMB must not be restated in `foldLast`'s shape.** `climb_wins` (§3c) concludes a bare
collision from `a ≠ b`; writing it as `a = b ∨ Coll h …` puts the hypothesis in the good branch and
makes the theorem strictly weaker. `peelPath`'s `π` is `List F × List F` — the 2-ary compressor
uncurried — which `Coll` accommodates with no adaptation.

**(b) `MapOpsColumnLayout.pathCollFind` is a THIRD shape.** It walks a CLAIMED path against a TRUE
tree — heterogeneous, driven by the path while the vector is narrowed by `take`/`drop` — and its
good branch is not "the two structures agree" but a POSITIONAL binding plus an update law
(`xs[pathPos steps]? = some leaf ∧ ∀ leaf', …`). The traversal is site-specific; only the residual
vocabulary and the `Site`/`Teeth` bundle transfer.

**(c) `zipFirst` is NOT a legal simplification of `foldLast`.** See the module docstring: `zipFirst`
has pointwise image equality as its hypothesis, `foldLast` has it only at the end of the fold.

**(d) A general `Traversable`/`Foldable` version was NOT built.** The measured sites are `List`-
shaped or tree-shaped-with-an-explicit-`pick`; a traversal class buys nothing here and costs the
`rfl`-level agreement with the deployed extractors that §1 of the instantiation module relies on. -/

end Dregg2.Circuit.FirstDivergence
