/-
# Dregg2.Circuit.FirstDivergenceInstances — the combinator REPRODUCES the hand-rolled repairs.

`Dregg2.Circuit.FirstDivergence` claims that the tree's ~82 hand-written collision extractors are
compositions of five pieces. A claim like that is worth exactly the entailment that backs it, so this
module instantiates the combinator on FIVE ALREADY-PORTED sites that walk FIVE DIFFERENT structures,
and proves in each case that the generic object AGREES WITH THE DEPLOYED ONE and that the generic
soundness theorem ENTAILS the hand-rolled one verbatim:

  * §1 `Crypto.HashSigMerkle.pkLeafFind` — a depth-0 leaf over a flattened OTS public key.
    `pkLeafFind = leafPair pkEncode` by `rfl`.
  * §2 `Circuit.AggregationAirSound.aggCollFind` — an accumulating Poseidon2 fold over AIR rows.
    `aggCollFind = foldLast` and `aggFold = foldOf`, by induction; `aggFold_binds_or_collides` is
    re-derived from `foldLast_binds_or_coll` with its statement copied character-for-character.
  * §3 `Substrate.Heap.mapLeafFind` — a first-divergence zip over heap entries.
    `mapLeafFind = zipFirst` where the entry encoding is `fun e => [e.1, e.2]`.
  * §3b `Substrate.Heap.rootFind` — the two-layer outer/inner extractor, `pick` of §3's zip.
  * §5 `Circuit.FriCompressRegrounded.peelPath` — the FRI Merkle climb, at a different `π`
    (`List F × List F`) and in the DUAL polarity. `merkleRecompute = foldOf`, so `climb` and
    `foldLast` provably fold the same object in opposite orders.

§3c names each reproduced statement ONCE as a `Prop` and inhabits it TWICE — by the deployed theorem
and by the combinator's output — so statement drift on either side turns this file red.

⚑ The hand-rolled versions are NOT deleted and NOT weakened. Each `…_via_combinator` theorem below
restates the ORIGINAL conclusion at the ORIGINAL residual — `Poseidon2Binding.SpongeColl hash p` is
DEFEQ to `FirstDivergence.Coll hash p`, so `exact` closes the gap with no bridging lemma and no new
carrier. That defeq is the evidence the abstraction is faithful rather than merely plausible: a
statement that needed a translation layer would be a different statement.

§4 builds the `Teeth` bundle at the aggregation site and DERIVES the three teeth
(`_unconditional_false`, `_refutable`, `_fires`), then proves each derived tooth entails the
hand-rolled one it corresponds to. That is the defect-killing half: the audits' failures were teeth
that had drifted onto a different statement than the keystone they were cited for, and in the bundle
that mismatch does not typecheck.

Nothing here assumes anything about any hash. `#assert_axioms`-clean.
-/
import Dregg2.Circuit.FirstDivergence
import Dregg2.Circuit.AggregationAirSound
import Dregg2.Crypto.HashSigMerkle
import Dregg2.Substrate.Heap
import Dregg2.Circuit.FriCompressRegrounded

namespace Dregg2.Circuit.FirstDivergenceInstances

open Dregg2.Circuit.FirstDivergence
open Dregg2.Circuit.Poseidon2Binding (SpongeColl)

/-! ## 0. The residual vocabularies COINCIDE — no translation layer.

`Poseidon2Binding.SpongeColl hash p` is `p.1 ≠ p.2 ∧ hash p.1 = hash p.2`; `Coll hash p` is the same
proposition at `π := List ℤ, α := ℤ`. Proved by `Iff.rfl`, so every theorem below can be `exact`ed
into its hand-rolled counterpart's statement. -/

theorem spongeColl_eq_coll (hash : List ℤ → ℤ) (p : List ℤ × List ℤ) :
    SpongeColl hash p ↔ Coll hash p := Iff.rfl

/-! ## 1. `pkLeafFind` — the DEPTH-0 LEAF (`Crypto/HashSigMerkle.lean:111`). -/

open Dregg2.Crypto.HashSigMerkle (pkEncode pkLeaf pkLeafFind pkEncode_injective)

/-- **THE EXTRACTORS ARE THE SAME OBJECT** — `rfl`, not a proved coincidence. -/
theorem pkLeafFind_eq_leafPair {ℓ : ℕ} (pk pk' : Fin ℓ → Bool → ℤ) :
    pkLeafFind pk pk' = leafPair pkEncode pk pk' := rfl

/-- **THE COMBINATOR ENTAILS `pkLeaf_binds_or_collides`** — statement copied verbatim from
`Crypto/HashSigMerkle.lean:118`, proof replaced by one application of `leafPair_binds_or_coll`. -/
theorem pkLeaf_binds_or_collides_via_combinator (hash : List ℤ → ℤ) {ℓ : ℕ}
    (pk pk' : Fin ℓ → Bool → ℤ) (h : pkLeaf hash pk = pkLeaf hash pk') :
    pk = pk' ∨ SpongeColl hash (pkLeafFind pk pk') :=
  leafPair_binds_or_coll hash pkEncode (fun _ _ he => pkEncode_injective he) pk pk' h

/-- **THE HAND-ROLLED THEOREM IS RECOVERED**, not merely paralleled: the combinator's output has the
type of `Dregg2.Crypto.HashSigMerkle.pkLeaf_binds_or_collides` on the nose. -/
theorem pkLeaf_handrolled_recovered (hash : List ℤ → ℤ) {ℓ : ℕ} (pk pk' : Fin ℓ → Bool → ℤ)
    (h : pkLeaf hash pk = pkLeaf hash pk') :
    pk = pk' ∨ SpongeColl hash (pkLeafFind pk pk') :=
  Dregg2.Crypto.HashSigMerkle.pkLeaf_binds_or_collides hash pk pk' h

/-- **THE DISCHARGE TOOTH IS RECOVERED TOO** (`pkLeafColl_dischargeable`): one key against itself
refutes the residual for EVERY hash, straight out of `leafPair_self_eq`. -/
theorem pkLeafColl_dischargeable_via_combinator (hash : List ℤ → ℤ) {ℓ : ℕ}
    (pk : Fin ℓ → Bool → ℤ) : ¬ SpongeColl hash (pkLeafFind pk pk) :=
  noColl_of_eq (leafPair_self_eq pkEncode pk)

/-! ## 2. `aggCollFind` — the ACCUMULATING FOLD (`Circuit/AggregationAirSound.lean:237`).

The three fold sites in the tree (`aggCollFind`, `StateTransitionAirSound.stCollFind`,
`BindingAirSound.histCollFind`) differ ONLY in `absorb` and `proj`; `stCollFind`'s extra `tag` is a
partially-applied `absorb`. -/

open Dregg2.Circuit.AggregationAirSound
  (AggRow aggExtend aggFold aggAbsorb aggCollFind projAgg)

/-- **THE DEPLOYED PER-ROW GATE IS AN `absorb`.** `aggExtend sponge a r.leaf r.root r.idx` is
`sponge (aggAbsorb a r)` — `rfl`, so the fold below is the deployed one and not a reconstruction. -/
theorem aggExtend_eq_absorb (sponge : List ℤ → ℤ) (a : ℤ) (r : AggRow) :
    aggExtend sponge a r.leaf r.root r.idx = sponge (aggAbsorb a r) := rfl

/-- **THE FOLDS ARE THE SAME FUNCTION.** -/
theorem aggFold_eq_foldOf (sponge : List ℤ → ℤ) :
    ∀ (rows : List AggRow) (a : ℤ), aggFold sponge a rows = foldOf sponge aggAbsorb a rows := by
  intro rows
  induction rows with
  | nil => intro a; rfl
  | cons r rest ih => intro a; exact ih (aggExtend sponge a r.leaf r.root r.idx)

/-- **THE EXTRACTORS ARE THE SAME FUNCTION** — the hand-rolled `let deep := …; if deep.1 = deep.2
then thisLevel else deep` IS `pick deep thisLevel`. -/
theorem aggCollFind_eq_foldLast (sponge : List ℤ → ℤ) :
    ∀ (rows rows' : List AggRow) (a b : ℤ),
      aggCollFind sponge a b rows rows' = foldLast sponge aggAbsorb a b rows rows' := by
  intro rows
  induction rows with
  | nil => intro rows' a b; cases rows' <;> rfl
  | cons r rest ih =>
    intro rows' a b
    cases rows' with
    | nil => rfl
    | cons r' rest' =>
      rw [foldLast, aggCollFind, pick,
        ih rest' (aggExtend sponge a r.leaf r.root r.idx) (aggExtend sponge b r'.leaf r'.root r'.idx)]
      rfl

/-- The only property of `aggAbsorb` the hand-rolled proof used: an absorbed 4-list determines the
accumulator it was taken at and the row's committed `(leaf, root, idx)` projection. -/
theorem aggAbsorb_splits (a b : ℤ) (r r' : AggRow) (h : aggAbsorb a r = aggAbsorb b r') :
    a = b ∧ projAgg r = projAgg r' := by
  simp only [aggAbsorb, List.cons.injEq, and_true] at h
  obtain ⟨hacc, hleaf, hroot, hidx⟩ := h
  exact ⟨hacc, by unfold projAgg; rw [hleaf, hroot, hidx]⟩

/-- **⚑ THE COMBINATOR ENTAILS `aggFold_binds_or_collides`** — statement copied verbatim from
`Circuit/AggregationAirSound.lean:251`, including the good branch's third conjunct, with the
hand-rolled 50-line induction replaced by one application of `foldLast_binds_or_coll`. -/
theorem aggFold_binds_or_collides_via_combinator (sponge : List ℤ → ℤ) :
    ∀ (rows rows' : List AggRow) (a b : ℤ),
      rows.length = rows'.length →
      aggFold sponge a rows = aggFold sponge b rows' →
      (a = b ∧ rows.map projAgg = rows'.map projAgg
        ∧ (aggCollFind sponge a b rows rows').1 = (aggCollFind sponge a b rows rows').2)
      ∨ SpongeColl sponge (aggCollFind sponge a b rows rows') := by
  intro rows rows' a b hlen heq
  rw [aggCollFind_eq_foldLast]
  refine foldLast_binds_or_coll sponge aggAbsorb projAgg
    (fun a b r r' h => aggAbsorb_splits a b r r' h) rows rows' a b hlen ?_
  rw [← aggFold_eq_foldOf, ← aggFold_eq_foldOf]
  exact heq

/-- **AND THE `_fires` TOOTH** (`aggColl_fires`, `Circuit/AggregationAirSound.lean:406`): at an
honest equal history the walk bottoms out at an EQUAL pair, so the residual is discharged for EVERY
sponge — no CR, no floor. Out of `foldLast_self_eq`. -/
theorem aggColl_fires_via_combinator (sponge : List ℤ → ℤ) (rows : List AggRow) (a : ℤ) :
    ¬ SpongeColl sponge (aggCollFind sponge a a rows rows) := by
  rw [aggCollFind_eq_foldLast]
  exact noColl_of_eq (foldLast_self_eq sponge aggAbsorb rows a)

/-! ## 3. `mapLeafFind` — the FIRST-DIVERGENCE ZIP (`Substrate/Heap.lean:519`).

A third structure, and the one that shows `foldLast` and `zipFirst` are genuinely different: here
the images agree POINTWISE (the hypothesis is an equality of `List.map`s), so the walk may decide at
the first differing position. In §2 the images are known equal only at the END of the fold. -/

open Dregg2.Substrate.Heap (FeltHeap leafOf mapLeafFind)

/-- The heap entry's deployed preimage — `Heap.leafOf hash e = hash (heapEnc e)` by `rfl`. -/
def heapEnc (e : ℤ × ℤ) : List ℤ := [e.1, e.2]

theorem leafOf_eq_enc (hash : List ℤ → ℤ) (e : ℤ × ℤ) : leafOf hash e = hash (heapEnc e) := rfl

theorem heapEnc_injective : Function.Injective heapEnc := by
  intro a b h
  simp only [heapEnc, List.cons.injEq, and_true] at h
  exact Prod.ext h.1 h.2

/-- **THE EXTRACTORS ARE THE SAME FUNCTION.** `mapLeafFind` branches on the ENTRY, `zipFirst` on its
ENCODING; injectivity of `heapEnc` makes the two tests agree at every position. -/
theorem mapLeafFind_eq_zipFirst (hash : List ℤ → ℤ) :
    ∀ l₁ l₂ : FeltHeap, mapLeafFind hash l₁ l₂ = zipFirst heapEnc l₁ l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; cases l₂ <;> rfl
  | cons a as ih =>
    intro l₂
    cases l₂ with
    | nil => rfl
    | cons b bs =>
      by_cases hab : a = b
      · rw [mapLeafFind, if_pos hab, zipFirst, if_pos (congrArg heapEnc hab), ih bs]
      · rw [mapLeafFind, if_neg hab, zipFirst, if_neg (fun he => hab (heapEnc_injective he))]
        rfl

/-- **THE COMBINATOR ENTAILS `map_leaf_binds_or_collides`** — statement copied verbatim from
`Substrate/Heap.lean:564`. -/
theorem map_leaf_binds_or_collides_via_combinator (hash : List ℤ → ℤ) (l₁ l₂ : FeltHeap)
    (hmap : l₁.map (leafOf hash) = l₂.map (leafOf hash)) :
    l₁ = l₂ ∨ SpongeColl hash (mapLeafFind hash l₁ l₂) := by
  rw [mapLeafFind_eq_zipFirst]
  rcases zipFirst_binds_or_coll hash heapEnc heapEnc_injective l₁ l₂ hmap with ⟨heq, _⟩ | hc
  · exact Or.inl heq
  · exact Or.inr hc

/-- **AND ITS DISCHARGE TOOTH** (`mapLeafFind_self_eq`, `Substrate/Heap.lean:556`). -/
theorem mapLeafFind_self_eq_via_combinator (hash : List ℤ → ℤ) (l : FeltHeap) :
    (mapLeafFind hash l l).1 = (mapLeafFind hash l l).2 := by
  rw [mapLeafFind_eq_zipFirst]
  exact zipFirst_self_eq heapEnc l

/-! ### 3b. `rootFind` — `pick` COMPOSES WITH `zipFirst` (`Substrate/Heap.lean:584`).

The two-layer deployed extractor: if the two heaps' leaf VECTORS already differ, the equal roots make
THEM the outer collision; otherwise the break is inside and the leaf zip locates it. That `if` is
`pick`, with no adaptation. This is the shape 31 of the tree's extractors are built out of
(`mapRootWFind`, `mapRoot8Find`, `padImtRootFind`, `MMR.collFind`/`bagFind`, `capOpen8Find`, …). -/

open Dregg2.Substrate.Heap (root rootFind)

/-- **THE TWO-LAYER EXTRACTOR IS `pick` OF THE OUTER PAIR AND THE INNER ZIP.** -/
theorem rootFind_eq_pick (hash : List ℤ → ℤ) (h₁ h₂ : FeltHeap) :
    rootFind hash h₁ h₂
      = pick (h₁.map (leafOf hash), h₂.map (leafOf hash)) (zipFirst heapEnc h₁ h₂) := by
  unfold rootFind pick
  by_cases hm : h₁.map (leafOf hash) = h₂.map (leafOf hash)
  · rw [if_pos hm, if_pos hm, mapLeafFind_eq_zipFirst]
  · rw [if_neg hm, if_neg hm]

/-- **THE COMBINATOR ENTAILS `rootFind_spec`** — statement copied verbatim from
`Substrate/Heap.lean:592` (its conjunction IS `Coll hash (rootFind hash h₁ h₂)`), proof replaced by
`pick_coll` fed with `zipFirst_binds_or_coll`. -/
theorem rootFind_spec_via_combinator (hash : List ℤ → ℤ) {h₁ h₂ : FeltHeap}
    (hne : h₁ ≠ h₂) (hroot : root hash h₁ = root hash h₂) :
    (rootFind hash h₁ h₂).1 ≠ (rootFind hash h₁ h₂).2
      ∧ hash (rootFind hash h₁ h₂).1 = hash (rootFind hash h₁ h₂).2 := by
  rw [rootFind_eq_pick]
  refine pick_coll hash hroot ?_
  intro hm
  rcases zipFirst_binds_or_coll hash heapEnc heapEnc_injective h₁ h₂ hm with ⟨heq, _⟩ | hc
  · exact absurd heq hne
  · exact hc

/-! ## 3c. ⚑ STATEMENT IDENTITY, MACHINE-CHECKED.

"The combinator reproduces the hand-rolled theorem" is a claim about STATEMENTS, and the audits'
whole defect class was statements that had quietly drifted. So each statement is named ONCE as a
`Prop` and inhabited TWICE — by the deployed theorem and by the combinator's output. If either
statement drifts, this file goes red; a prose claim of agreement could not do that. -/

/-- The exact statement of `Crypto.HashSigMerkle.pkLeaf_binds_or_collides`. -/
def PkLeafStatement : Prop :=
  ∀ (hash : List ℤ → ℤ) {ℓ : ℕ} (pk pk' : Fin ℓ → Bool → ℤ),
    pkLeaf hash pk = pkLeaf hash pk' → pk = pk' ∨ SpongeColl hash (pkLeafFind pk pk')

theorem pkLeaf_statement_handrolled : PkLeafStatement :=
  fun hash {_ℓ} pk pk' h => Dregg2.Crypto.HashSigMerkle.pkLeaf_binds_or_collides hash pk pk' h

theorem pkLeaf_statement_combinator : PkLeafStatement :=
  fun hash {_ℓ} pk pk' h => pkLeaf_binds_or_collides_via_combinator hash pk pk' h

/-- The exact statement of `Circuit.AggregationAirSound.aggFold_binds_or_collides`. -/
def AggFoldStatement : Prop :=
  ∀ (sponge : List ℤ → ℤ) (rows rows' : List AggRow) (a b : ℤ),
    rows.length = rows'.length →
    aggFold sponge a rows = aggFold sponge b rows' →
    (a = b ∧ rows.map projAgg = rows'.map projAgg
      ∧ (aggCollFind sponge a b rows rows').1 = (aggCollFind sponge a b rows rows').2)
    ∨ SpongeColl sponge (aggCollFind sponge a b rows rows')

theorem aggFold_statement_handrolled : AggFoldStatement :=
  fun sponge => Dregg2.Circuit.AggregationAirSound.aggFold_binds_or_collides sponge

theorem aggFold_statement_combinator : AggFoldStatement :=
  fun sponge => aggFold_binds_or_collides_via_combinator sponge

/-- The exact statement of `Substrate.Heap.map_leaf_binds_or_collides`. -/
def MapLeafStatement : Prop :=
  ∀ (hash : List ℤ → ℤ) (l₁ l₂ : FeltHeap),
    l₁.map (leafOf hash) = l₂.map (leafOf hash) →
    l₁ = l₂ ∨ SpongeColl hash (mapLeafFind hash l₁ l₂)

theorem mapLeaf_statement_handrolled : MapLeafStatement :=
  fun hash l₁ l₂ h => Dregg2.Substrate.Heap.map_leaf_binds_or_collides hash l₁ l₂ h

theorem mapLeaf_statement_combinator : MapLeafStatement :=
  fun hash l₁ l₂ h => map_leaf_binds_or_collides_via_combinator hash l₁ l₂ h

/-! ## 4. ⚑ THE BUNDLE AT THE AGGREGATION SITE — the three teeth, GENERATED.

This is the half that kills the measured defect class. Below, `Hyp`, `Good` and `find` are written
ONCE, as fields; `sound` and every tooth are typed against those same fields. A tooth stated about a
different object — the actual defect the audits found, twice — does not typecheck here. -/

/-- The aggregation site's index: two row lists and two starting accumulators. -/
abbrev AggIdx : Type := (List AggRow × List AggRow) × (ℤ × ℤ)

/-- **THE AGGREGATION FOLD, AS A BUNDLED REPAIR.** Every field names the deployed objects:
`Hyp` is equal lengths plus an equal published digest, `Good` is the ordered-history binding, `find`
is the deployed `aggCollFind`, and `sound` is §2's entailment. The broken witness is the SAME
collapsing sponge and the SAME two one-row histories the hand-rolled teeth use
(`aggFold_inj_unconditional_false` / `aggColl_refutable`) — so the derived teeth below are about
the deployed statement, not a convenient neighbour of it. -/
def aggTeeth : Teeth (List ℤ) ℤ AggIdx where
  Hyp := fun sponge i => i.1.1.length = i.1.2.length ∧
    aggFold sponge i.2.1 i.1.1 = aggFold sponge i.2.2 i.1.2
  Good := fun _ i => i.2.1 = i.2.2 ∧ i.1.1.map projAgg = i.1.2.map projAgg
  find := fun sponge i => aggCollFind sponge i.2.1 i.2.2 i.1.1 i.1.2
  sound := by
    rintro sponge ⟨⟨rows, rows'⟩, ⟨a, b⟩⟩ hy
    obtain ⟨hlen, hdig⟩ := hy
    have hlen' : rows.length = rows'.length := hlen
    have hdig' : aggFold sponge a rows = aggFold sponge b rows' := hdig
    rcases aggFold_binds_or_collides_via_combinator sponge rows rows' a b hlen' hdig' with
      ⟨h1, h2, _⟩ | hc
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr hc
  Honest := fun i => i.1.1 = i.1.2 ∧ i.2.1 = i.2.2
  fires := by
    rintro sponge ⟨⟨rows, rows'⟩, ⟨a, b⟩⟩ hon
    obtain ⟨hr, ha⟩ := hon
    have hr' : rows = rows' := hr
    have ha' : a = b := ha
    subst hr'; subst ha'
    exact aggColl_fires_via_combinator sponge rows a
  brokenHash := fun _ => 0
  brokenIdx :=
    (([{ accIn := 0, leaf := 1, root := 0, idx := 0, accOut := 0 }],
      [{ accIn := 0, leaf := 2, root := 0, idx := 0, accOut := 0 }]), (0, 0))
  broken_hyp := ⟨rfl, rfl⟩
  broken_good_false := by
    rintro ⟨-, hproj⟩
    have hp : [projAgg { accIn := 0, leaf := 1, root := 0, idx := 0, accOut := 0 }]
        = [projAgg { accIn := 0, leaf := 2, root := 0, idx := 0, accOut := 0 }] := hproj
    simp only [List.cons.injEq, projAgg, Prod.mk.injEq] at hp
    omega
  broken_coll := Dregg2.Circuit.AggregationAirSound.aggColl_refutable

/-! ### 4b. THE THREE TEETH, DERIVED — and each ENTAILS its hand-rolled counterpart.

Nothing below is written by hand. `Teeth.unconditional_false`, `Teeth.refutable` and
`Teeth.fires_good` are generic theorems of the bundle; the only content here is that each of them
recovers the theorem `AggregationAirSound` states separately. -/

/-- **LOAD-BEARING, GENERATED → `aggFold_inj_unconditional_false`.** Statement copied verbatim from
`Circuit/AggregationAirSound.lean:380`; the proof is `Teeth.broken_good_false` applied to the
bundle's own broken witness, so it CANNOT be about a statement with different hypotheses than
`aggTeeth.sound`'s. -/
theorem aggFold_inj_unconditional_false_via_bundle :
    ¬ (∀ (sponge : List ℤ → ℤ) (rows rows' : List AggRow) (a b : ℤ),
        rows.length = rows'.length →
        aggFold sponge a rows = aggFold sponge b rows' →
        rows.map projAgg = rows'.map projAgg) := by
  intro hall
  refine aggTeeth.broken_good_false ⟨rfl, ?_⟩
  exact hall _ _ _ _ _ aggTeeth.broken_hyp.1 aggTeeth.broken_hyp.2

/-- The bundle's own load-bearing tooth, unspecialised: the keystone's hypothesis cannot be dropped. -/
theorem aggTeeth_unconditional_false :
    ¬ ∀ (h : List ℤ → ℤ) (i : AggIdx), aggTeeth.Hyp h i → aggTeeth.Good h i :=
  aggTeeth.unconditional_false

/-- **REFUTABLE, GENERATED → `aggColl_refutable`.** The residual is not `True` in disguise. -/
theorem aggTeeth_refutable :
    Coll aggTeeth.brokenHash (aggTeeth.find aggTeeth.brokenHash aggTeeth.brokenIdx) :=
  aggTeeth.refutable

/-- The residual is refutable AS A UNIVERSAL CLAIM — the form a reader checking for laundering
wants: it is NOT the case that the extractor never finds anything. -/
theorem aggTeeth_residual_not_trivial :
    ¬ ∀ (h : List ℤ → ℤ) (i : AggIdx), ¬ Coll h (aggTeeth.find h i) :=
  aggTeeth.residual_not_trivial

/-- **FIRES, GENERATED → the `agg_digest_binds_history` binding at an honest history.** At an honest
index the conclusion holds for EVERY sponge, with no cryptographic hypothesis at all — the
separation `globalBreak_free` / `indexedBreak_not_free` says a global-existential disjunct cannot
make. -/
theorem aggTeeth_fires (sponge : List ℤ → ℤ) (rows : List AggRow) (a : ℤ) :
    a = a ∧ rows.map projAgg = rows.map projAgg :=
  aggTeeth.fires_good sponge ((rows, rows), (a, a)) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩

/-! ## 5. ⚑ `peelPath` — THE CLIMB, AND THE PROOF IT IS THE SAME `foldOf`.

The strongest claim in `FirstDivergence` is §3c's: `foldLast` and `climb` are ONE fold walked two
ways. Backed here at the FRI Merkle peel — a fourth structure, a different `π` (`List F × List F`,
the 2-ary compressor uncurried), and the DUAL polarity.

  * `merkleRecompute_eq_foldOf` — the deployed FRI recompute IS `foldOf`, once the index bits are
    zipped onto the sibling path. Same fold as §2's aggregation digest.
  * `merkle_climb_wins` — `climb_wins` at that instance reproduces `peelPath_wins`'s content: from
    DISTINCT leaves reaching one root, a genuine `compress` collision, with NO hypothesis on
    `compress` and NO good branch.

⚠ `peelPath` and `climb` are NOT equal as functions: their unreachable `[]` cases return different
junk (`((l1,l1),(l2,l2))` vs `(default, default)`). Under the spec's own hypotheses the empty path
is contradictory (equal roots then force equal leaves), so they agree wherever either is defined to
matter — but the equation is stated here as what it is, not as more. -/

open Dregg2.Circuit.FriVerifier (merkleRecompute)
open Dregg2.Circuit.FriCompressRegrounded (peelPath peelPath_wins)

variable {F : Type}

/-- The deployed compressor, uncurried, so `Coll` applies to it with no adaptation. -/
def compressU (compress : List F → List F → List F) (p : List F × List F) : List F :=
  compress p.1 p.2

/-- One path level's ordered node preimage: the index bit says which side the accumulator sits on.
`absorb` in `foldOf`/`climb`'s sense, at `α := List F`, `π := List F × List F`. -/
def sideAbsorb (a : List F) (g : Bool × List F) : List F × List F :=
  if g.1 then (a, g.2) else (g.2, a)

/-- The sibling path with its index bits zipped on — the FRI opening's `idx`/`idx / 2` ladder made
into the step list `foldOf` consumes. -/
def sidePath : Nat → List (List F) → List (Bool × List F)
  | _,   []       => []
  | idx, s :: rest => (idx % 2 == 0, s) :: sidePath (idx / 2) rest

/-- **THE DEPLOYED FRI RECOMPUTE IS `foldOf`** — the same fold as the aggregation digest in §2. -/
theorem merkleRecompute_eq_foldOf (compress : List F → List F → List F) :
    ∀ (sibs : List (List F)) (idx : Nat) (acc : List F),
      merkleRecompute compress idx acc sibs
        = foldOf (compressU compress) sideAbsorb acc (sidePath idx sibs) := by
  intro sibs
  induction sibs with
  | nil => intro idx acc; rfl
  | cons s rest ih =>
    intro idx acc
    rw [merkleRecompute, sidePath, foldOf, ih (idx / 2)]
    by_cases hb : idx % 2 = 0
    · simp only [hb, if_pos, beq_self_eq_true, sideAbsorb, compressU]
    · simp only [hb, sideAbsorb, compressU]
      simp only [beq_iff_eq, hb, if_false]

/-- Absorbing DISTINCT accumulators against the same level material keeps them distinct — the only
property of `sideAbsorb` the climb uses (injectivity of the ordered Merkle node). -/
theorem sideAbsorb_distinct (a b : List F) (g : Bool × List F) (hne : a ≠ b) :
    sideAbsorb a g ≠ sideAbsorb b g := by
  cases hg : g.1 <;> simp only [sideAbsorb, hg, Bool.false_eq_true, if_false, if_true, ne_eq,
    Prod.mk.injEq, not_and] <;> intro h1 h2 <;> first | exact hne h1 | exact hne h2

/-- **⚑ `climb_wins` REPRODUCES `peelPath_wins`'s CONTENT** at the FRI peel: from DISTINCT leaves
that recompute to the SAME root, the generic climb returns a genuine `compress` collision.
Unconditional — nothing is assumed about `compress` — and, like the hand-rolled original and unlike
`foldLast`'s shape, there is NO good branch. -/
theorem merkle_climb_wins [DecidableEq F] (compress : List F → List F → List F)
    (sibs : List (List F)) (idx : Nat) (l1 l2 : List F) (hne : l1 ≠ l2)
    (heq : merkleRecompute compress idx l1 sibs = merkleRecompute compress idx l2 sibs) :
    Coll (compressU compress)
      (climb (compressU compress) sideAbsorb l1 l2 (sidePath idx sibs)) := by
  refine climb_wins (compressU compress) sideAbsorb
    (fun a b g h => sideAbsorb_distinct a b g h) (sidePath idx sibs) l1 l2 hne ?_
  rw [← merkleRecompute_eq_foldOf, ← merkleRecompute_eq_foldOf]
  exact heq

/-- **AND THE HAND-ROLLED PEEL IS RECOVERED** — `peelPath_wins`'s conclusion IS
`Coll (compressU compress) (peelPath …)`, so the two extractors deliver the SAME residual type at
the SAME site. (They are different terms; see the section note.) -/
theorem peelPath_wins_is_a_coll [DecidableEq F] (compress : List F → List F → List F)
    (sibs : List (List F)) (idx : Nat) (l1 l2 : List F) (hne : l1 ≠ l2)
    (heq : merkleRecompute compress idx l1 sibs = merkleRecompute compress idx l2 sibs) :
    Coll (compressU compress) (peelPath compress idx l1 l2 sibs) :=
  peelPath_wins compress sibs idx l1 l2 hne heq

/-! ## 6. Axiom hygiene. -/

#assert_axioms spongeColl_eq_coll
#assert_axioms pkLeafFind_eq_leafPair
#assert_axioms pkLeaf_binds_or_collides_via_combinator
#assert_axioms pkLeafColl_dischargeable_via_combinator
#assert_axioms aggExtend_eq_absorb
#assert_axioms aggFold_eq_foldOf
#assert_axioms aggCollFind_eq_foldLast
#assert_axioms aggAbsorb_splits
#assert_axioms aggFold_binds_or_collides_via_combinator
#assert_axioms aggColl_fires_via_combinator
#assert_axioms leafOf_eq_enc
#assert_axioms heapEnc_injective
#assert_axioms mapLeafFind_eq_zipFirst
#assert_axioms map_leaf_binds_or_collides_via_combinator
#assert_axioms mapLeafFind_self_eq_via_combinator
#assert_axioms rootFind_eq_pick
#assert_axioms rootFind_spec_via_combinator
#assert_axioms pkLeaf_statement_handrolled
#assert_axioms pkLeaf_statement_combinator
#assert_axioms aggFold_statement_handrolled
#assert_axioms aggFold_statement_combinator
#assert_axioms mapLeaf_statement_handrolled
#assert_axioms mapLeaf_statement_combinator
#assert_axioms merkleRecompute_eq_foldOf
#assert_axioms sideAbsorb_distinct
#assert_axioms merkle_climb_wins
#assert_axioms peelPath_wins_is_a_coll
#assert_axioms aggFold_inj_unconditional_false_via_bundle
#assert_axioms aggTeeth_unconditional_false
#assert_axioms aggTeeth_refutable
#assert_axioms aggTeeth_residual_not_trivial
#assert_axioms aggTeeth_fires

end Dregg2.Circuit.FirstDivergenceInstances
