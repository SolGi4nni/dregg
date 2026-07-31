/-
# `Dregg2.Circuit.DeployedMapDenotation` — the DEPLOYED map commitment, placed UPSTREAM of
  `DescriptorIR2` so the map-op denotation can BE it instead of describing a retired shape.

## Substrate — say it out loud

**This is a MODEL/DENOTATION module. It is not an AIR and it authors no constraint.** Nothing here
emits a gate, a `Builder` gadget or an `air_accepts` predicate. It defines the commitment
`circuit/src/heap_root.rs` computes and proves binding facts about it. The AIR is elsewhere and is
Lean-authored where it is authored at all; this file is what the AIR's rows are *judged against*.

## Why this file exists, and why it is HERE and not downstream

`circuit/src/heap_root.rs` moved the map tree to an **indexed Merkle tree** on 2026-07-12
(`919b2b0b8d`): `HEAP_LEAF_ARITY = 3`, leaf = `hash[addr, value, next_addr]`, pointers derived by
`relink_next_addrs` from the sorted successor with the terminal one pinned to `SENTINEL_MAX`, the
`2^16`-leaf vector zero-padded above the live prefix. The Lean denotation
(`DescriptorIR2.opensTo` / `writesTo` → `MapOp.holdsAt` → `Satisfied2` → every `AlgoStarkSound*`)
went on quantifying over **arity-2 `Heap.leafOf` leaves at DENSE occupancy**. Under an injective
sponge those are provably different commitments, so the apex's *conclusion* — not merely its premise
— was false at the root the prover computes.

The repair already existed as objects: `MapDenotationSchema.MapLeafSchema` and
`MapPaddedDenotation.padImtSchema` / `padImtTeeth`. It could not be *applied*, because both live
**downstream** of `DescriptorIR2` (`MapPaddedDenotation → MapDenotationSchema →
MapReconcileImtRepoint → MapAbsentImtGate → IndexedMerkleTree → MapOpsColumnLayout → … →
DescriptorIR2`). A denotation cannot be rebound onto a definition that imports it. **So the schema
core moves here**, above `DescriptorIR2`, importing only `MapMerkleRoot` (the fold), `Heap` (the
committed object) and `SpongeCarrierReduction` (the residual). The modules it came from now import
this one and `export` the names, so every existing reference resolves to the SAME constant — there
is no twin, and nothing was copied.

## ★ THE ∃-HOIST, and why it had to land WITH the arity move

Two independent axes make a map theorem vacuous at deployed parameters:

  1. **arity/occupancy** — the committed object is the wrong shape (this file's `padImtRoot`);
  2. **the ∃-hoist** — the anti-ghost is stated as `floor → conclusion` where the floor is
     `Function.Injective hash` / `Poseidon2SpongeCR hash`, both **PROVED FALSE** at deployed BabyBear
     (`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`; pigeonhole on a 2^30.9 codomain). Such a
     theorem is true and says nothing.

`MapPaddedDenotation`'s schema teeth carry the arity but not the hoist: their existential-level forms
(`opensToMerkleS_functional_of_good`) take `T.Good hash`, which at any instance contains
`Function.Injective hash` — the refuted floor under another name. Rebinding the denotation onto the
right shape while leaving the teeth on `_of_good` would **migrate** the vacuous carriers onto a fresh
set of vacuous carriers, not remove them.

§6 below is the missing half: `openHeapS` / `writeHeapS` name the witness heaps two openings supply
(`Exists.choose`, canonical by proof irrelevance — a function of the PROPOSITION, not of the proof
term), and `OpenResidS` / `WriteResidS` are the schema's residual **at those two heaps and nothing
wider**. `opensToMerkleS_binds_or_collides` / `writesToMerkleS_binds_or_collides` then have **no
hypothesis on `hash` at all**. That is what `DescriptorIR2.opensTo_functional` binds to after the
cutover, so the deployed anti-ghost lands floor-free rather than moving house.

⚠ A `∀ h₁ h₂, ¬ Resid …` side condition would NOT do: at a fixed root the set of heaps with that root
is infinite, so the `∀` form is refuted by exactly the pigeonhole that refutes the floor. The residual
has to be at the pair the extractor returns.

## What is NOT closed here — named, not claimed closed

  * **The padding is a literal `BabyBear::ZERO`** (`heap_root.rs`'s `EMPTY_SUBTREE_ROOTS[0]`), not a
    domain-separated digest. So `PadGhost3` — "a LIVE leaf digest equals the padding constant" — is a
    reachable event that collision-resistance does not exclude (it is a FIXED-TARGET PREIMAGE of a
    literal). It rides in the CONCLUSION as a named, per-commitment, refutable residual. Removing it
    is a **deployed-side** change to `heap_root.rs`, not a Lean one.
  * **`Good` is still an idealisation** where it appears (`_of_good` forms are kept only as the
    strength bridge). Every statement this file exports to the deployed denotation is an
    `_or_resid`/`_or_collides` form with no hash hypothesis.
  * **This file says nothing about the `.insert` (op=3) pre-root or the `.aafiInsert` post layout.**
    Both are deployed-side obstructions proved in `MapKindImtGates`
    (`insertImtGates_cannot_force_the_write_denotation`,
    `no_schema_commits_the_append_order_layout`).

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; sorry-free; no `native_decide`; no
`decide` over any depth-16 spine.
-/
import Dregg2.Circuit.MapMerkleRoot
import Dregg2.Crypto.SpongeCarrierReduction

namespace Dregg2.Circuit.DeployedMapDenotation

open Dregg2.Substrate
open Dregg2.Circuit.Poseidon2Binding (SpongeColl spongeColl_refutable_of_injective)
open Dregg2.Circuit.Poseidon2Binding.Reference (refSponge refSponge_CR)
open Dregg2.Circuit.MapMerkleRoot (mapNode foldLevel perfectRoot perfectRootFind
  perfectRoot_binds_or_collides)
open Dregg2.Crypto.SpongeCarrierReduction (IsSpongeColl)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — THE DEPLOYED LEAF: `heap_root.rs::HeapLeaf`, arity 3. -/

/-- **`ImtLeaf`** — an indexed-Merkle-tree leaf: the sort key `addr`, the stored `value`, and the
`nextAddr` POINTER to the next-larger present key (the sorted linked-list link). The genesis
sentinel points `MIN → MAX`; every real insert splices between an `addr` and its `nextAddr`.
Key/value types generic; the defaults are the deployed felt instantiation.

⚑ MOVED here from `IndexedMerkleTree` (2026-07-30) so the deployed commitment is available ABOVE
`DescriptorIR2`. `IndexedMerkleTree` re-exports the name; it is the same constant. -/
structure ImtLeaf (K : Type := ℤ) (V : Type := ℤ) where
  /-- The sort key (deployed: the heap address `hash[coll, key]`; widens to `Digest8Key` for the
  #4/#10 note nullifiers — the tree is sorted by this). -/
  addr : K
  /-- The stored value (deployed: a felt; irrelevant to the ordering — hence free). -/
  value : V
  /-- The pointer to the next-larger present key (the linked-list link; the absence bracket). -/
  nextAddr : K
deriving DecidableEq, Repr

/-- **`imtLeafHash hash l`** — the 3-felt IMT leaf digest `hash[addr, value, nextAddr]`
(`heap_root.rs::HeapLeaf::preimage`, `HEAP_LEAF_ARITY = 3`). -/
def imtLeafHash (hash : List ℤ → ℤ) (l : ImtLeaf) : ℤ := hash [l.addr, l.value, l.nextAddr]

/-- **`imtLeafPre l`** — the IMT leaf's sponge PREIMAGE, named so the per-instance collision event
is stated at exactly the list the deployed digest absorbs (`imtLeafHash hash l = hash (imtLeafPre l)`,
`rfl`). -/
def imtLeafPre (l : ImtLeaf) : List ℤ := [l.addr, l.value, l.nextAddr]

/-- **`imtToHeap c`** — the projection to the deployed sorted `FeltHeap`: drop the `nextAddr`
pointer, keeping `(addr, value)` (the pointer is the ABSENCE machinery; the openable map is
`(addr) → value`). -/
def imtToHeap (c : List ImtLeaf) : Heap.FeltHeap := c.map (fun l => (l.addr, l.value))

/-- **THE HYPOTHESIS-FREE IMT-LEAF BINDING.** Equal 3-felt leaf digests force equal leaves OR name a
genuine collision of the deployed sponge at the two absorbed preimages. NO floor hypothesis. -/
theorem imtLeafHash_binds_or_collides (hash : List ℤ → ℤ) {l₁ l₂ : ImtLeaf}
    (h : imtLeafHash hash l₁ = imtLeafHash hash l₂) :
    l₁ = l₂ ∨ IsSpongeColl hash (imtLeafPre l₁, imtLeafPre l₂) := by
  by_cases hpre : imtLeafPre l₁ = imtLeafPre l₂
  · refine Or.inl ?_
    obtain ⟨a₁, v₁, n₁⟩ := l₁
    obtain ⟨a₂, v₂, n₂⟩ := l₂
    simp only [imtLeafPre, List.cons.injEq, and_true] at hpre
    obtain ⟨ha, hv, hn⟩ := hpre
    subst ha; subst hv; subst hn; rfl
  · exact Or.inr ⟨hpre, h⟩

/-! ## §2 — THE DEPLOYED RELINK: `heap_root.rs::relink_next_addrs` as a FUNCTION. -/

/-- **`imtChainOf sent h`** — the deployed relink: point each leaf at its sorted successor's address,
and the last leaf at the terminal sentinel `sent`.

★ This being a FUNCTION of the heap (not an existential) is what lets a `MapLeafSchema`'s `commit` be
a plain field: the arity-3 leaf carries no committed datum the sorted heap plus the sentinel does not
already determine. -/
def imtChainOf (sent : ℤ) : Heap.FeltHeap → List ImtLeaf
  | [] => []
  | [e] => [⟨e.1, e.2, sent⟩]
  | e :: e' :: rest => ⟨e.1, e.2, e'.1⟩ :: imtChainOf sent (e' :: rest)

/-- The relink's cons step, with the produced pointer NAMED — the shape the inductions need (the tail
of `imtChainOf` is not syntactically a cons, so a three-case match is otherwise stuck). -/
theorem imtChainOf_cons (sent : ℤ) (e : ℤ × ℤ) (rest : Heap.FeltHeap) :
    ∃ n : ℤ, imtChainOf sent (e :: rest) = ⟨e.1, e.2, n⟩ :: imtChainOf sent rest := by
  cases rest with
  | nil => exact ⟨sent, rfl⟩
  | cons e' rest' => exact ⟨e'.1, rfl⟩

/-- The relink preserves length (`relink_next_addrs` rewrites pointers in place). -/
theorem imtChainOf_length (sent : ℤ) :
    ∀ h : Heap.FeltHeap, (imtChainOf sent h).length = h.length := by
  intro h
  induction h with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨n, hn⟩ := imtChainOf_cons sent e rest
    rw [hn, List.length_cons, List.length_cons, ih]

/-- **The relink is a RETRACTION** — dropping the pointers recovers the heap. -/
theorem imtToHeap_imtChainOf (sent : ℤ) :
    ∀ h : Heap.FeltHeap, imtToHeap (imtChainOf sent h) = h := by
  intro h
  induction h with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨n, hn⟩ := imtChainOf_cons sent e rest
    obtain ⟨a, v⟩ := e
    rw [hn]
    show (a, v) :: imtToHeap (imtChainOf sent rest) = (a, v) :: rest
    rw [ih]

theorem imtChainOf_injective (sent : ℤ) {h₁ h₂ : Heap.FeltHeap}
    (h : imtChainOf sent h₁ = imtChainOf sent h₂) : h₁ = h₂ := by
  have hc := congrArg imtToHeap h
  rwa [imtToHeap_imtChainOf, imtToHeap_imtChainOf] at hc

/-- The arity-3 leaf-list extractor: walk to the first differing leaf and hand back the two absorbed
arity-3 IMT blocks. TOTAL — no `Classical.choice` in the walk. -/
def imtLeafFind (hash : List ℤ → ℤ) : List ImtLeaf → List ImtLeaf → List ℤ × List ℤ
  | l :: ls, l' :: ls' =>
      if l = l' then imtLeafFind hash ls ls' else (imtLeafPre l, imtLeafPre l')
  | _, _ => ([], [])

theorem imtLeafFind_spec (hash : List ℤ → ℤ) :
    ∀ (c₁ c₂ : List ImtLeaf), c₁ ≠ c₂ →
      c₁.map (imtLeafHash hash) = c₂.map (imtLeafHash hash) →
      SpongeColl hash (imtLeafFind hash c₁ c₂) := by
  intro c₁
  induction c₁ with
  | nil =>
    intro c₂ hne hmap
    cases c₂ with
    | nil => exact absurd rfl hne
    | cons l' ls' => simp at hmap
  | cons l ls ih =>
    intro c₂ hne hmap
    cases c₂ with
    | nil => simp at hmap
    | cons l' ls' =>
      simp only [List.map_cons, List.cons.injEq] at hmap
      obtain ⟨hleaf, htail⟩ := hmap
      by_cases hll : l = l'
      · subst hll
        have htne : ls ≠ ls' := fun hc => hne (by rw [hc])
        rw [imtLeafFind, if_pos rfl]
        exact ih ls' htne htail
      · rw [imtLeafFind, if_neg hll]
        exact (imtLeafHash_binds_or_collides hash hleaf).resolve_left hll

/-! ## §3 — THE PADDING: the deployed SPARSE occupancy. -/

/-- **`padDigest`** — `heap_root.rs`'s padding marker: the LITERAL `BabyBear::ZERO`
(`EMPTY_SUBTREE_ROOTS[0]`). ⚑ It is a literal, NOT a hash output — which is exactly what makes the
`PadGhost3` residual reachable, and why removing it is a DEPLOYED change. -/
def padDigest : ℤ := 0

/-- **`padTo d L`** — the deployed occupancy discipline: the real leaf digests are a contiguous sorted
PREFIX and every position `≥ L.length` holds `padDigest` (`CanonicalHeapTree::new`). -/
def padTo (d : Nat) (L : List ℤ) : List ℤ := L ++ List.replicate (2 ^ d - L.length) padDigest

theorem padTo_length {d : Nat} {L : List ℤ} (h : L.length ≤ 2 ^ d) : (padTo d L).length = 2 ^ d := by
  simp only [padTo, List.length_append, List.length_replicate]
  omega

/-- **A FULL tree pads to itself** — the padded fold EXTENDS the dense one; it does not replace it. -/
theorem padTo_dense {d : Nat} {L : List ℤ} (h : L.length = 2 ^ d) : padTo d L = L := by
  simp only [padTo, h, Nat.sub_self, List.replicate_zero, List.append_nil]

/-- **`PadHit L`** — the committed leaf-digest vector `L` CONTAINS the padding constant.

⚠ Read what this quantifies over: the POSITIONS OF A GIVEN, FINITE, COMMITTED vector — decidable,
checkable, refutable. It is deliberately NOT `∃ l, imtLeafHash hash l = padDigest`, which quantifies
over the hash's whole domain and which pigeonhole makes unconditionally TRUE at deployed parameters;
such a disjunct would carry no more content than `True`. -/
def PadHit (L : List ℤ) : Prop := padDigest ∈ L

/-- **★ THE PADDING LEMMA — the whole density argument, and its exact residual.** Two zero-padded
vectors that are EQUAL force their live prefixes equal UNLESS one of the prefixes already contains the
padding constant. Purely combinatorial: no hash, no depth, no length hypothesis. -/
theorem append_replicate_eq_or_hit : ∀ (L₁ L₂ : List ℤ) (k₁ k₂ : Nat),
    L₁ ++ List.replicate k₁ padDigest = L₂ ++ List.replicate k₂ padDigest →
    L₁ = L₂ ∨ PadHit L₁ ∨ PadHit L₂ := by
  intro L₁
  induction L₁ with
  | nil =>
    intro L₂ k₁ k₂ h
    cases L₂ with
    | nil => exact Or.inl rfl
    | cons b L₂' =>
      cases k₁ with
      | zero => simp at h
      | succ m =>
        rw [List.nil_append, List.replicate_succ, List.cons_append, List.cons.injEq] at h
        exact Or.inr (Or.inr (by rw [PadHit, h.1]; simp))
  | cons a L₁' ih =>
    intro L₂ k₁ k₂ h
    cases L₂ with
    | nil =>
      cases k₂ with
      | zero => simp at h
      | succ m =>
        rw [List.nil_append, List.replicate_succ, List.cons_append, List.cons.injEq] at h
        exact Or.inr (Or.inl (by rw [PadHit, ← h.1]; simp))
    | cons b L₂' =>
      rw [List.cons_append, List.cons_append, List.cons.injEq] at h
      obtain ⟨hab, htail⟩ := h
      rcases ih L₂' k₁ k₂ htail with heq | hh₁ | hh₂
      · exact Or.inl (by rw [hab, heq])
      · exact Or.inr (Or.inl (List.mem_cons_of_mem _ hh₁))
      · exact Or.inr (Or.inr (List.mem_cons_of_mem _ hh₂))

/-- The padded occupancy discipline binds the live prefix, up to the named ghost. -/
theorem padTo_eq_or_hit (d : Nat) {L₁ L₂ : List ℤ} (h : padTo d L₁ = padTo d L₂) :
    L₁ = L₂ ∨ PadHit L₁ ∨ PadHit L₂ :=
  append_replicate_eq_or_hit L₁ L₂ _ _ h

/-- One padding position IS a `PadHit`, so the ghost branch is REACHABLE (the canary the other way:
`PadHit` is not accidentally empty). -/
theorem padHit_singleton : PadHit [padDigest] := by simp [PadHit]

/-! ## §4 — ⚑ THE DEPLOYED MAP COMMITMENT, and its FLOOR-FREE binding. -/

/-- **`padImtRoot sent hash d h`** — ⚑ THE DEPLOYED MAP COMMITMENT: relink the pointers
(`relink_next_addrs`, terminal `sent`), digest each linked leaf at arity 3 (`HeapLeaf::preimage`,
`HEAP_LEAF_ARITY = 3`), fold the perfect tree over the ZERO-PADDED vector (`CanonicalHeapTree::new`). -/
def padImtRoot (sent : ℤ) (hash : List ℤ → ℤ) (d : Nat) (h : Heap.FeltHeap) : ℤ :=
  perfectRoot hash d (padTo d ((imtChainOf sent h).map (imtLeafHash hash)))

/-- **`PadGhost3 sent hash h`** — a LIVE arity-3 IMT leaf digest equals the padding constant. -/
def PadGhost3 (sent : ℤ) (hash : List ℤ → ℤ) (h : Heap.FeltHeap) : Prop :=
  PadHit ((imtChainOf sent h).map (imtLeafHash hash))

/-- The hash-level side condition: the padding constant has NO arity-3 IMT leaf preimage. ⚠ NOT
satisfied by the deployed chip merely by being collision-resistant — it is a fixed-target preimage
statement about a literal. -/
def PadFree3 (hash : List ℤ → ℤ) : Prop := ∀ l : ImtLeaf, imtLeafHash hash l ≠ padDigest

theorem padGhost3_refuted {hash : List ℤ → ℤ} (hpf : PadFree3 hash) (sent : ℤ) (h : Heap.FeltHeap) :
    ¬ PadGhost3 sent hash h := by
  intro hmem
  rw [PadGhost3, PadHit, List.mem_map] at hmem
  obtain ⟨l, _, hl⟩ := hmem
  exact hpf l hl

/-- The deployed root extractor: the node descent if it collides, else the arity-3 leaf scan. TOTAL. -/
def padImtRootFind (sent : ℤ) (hash : List ℤ → ℤ) (d : Nat)
    (h₁ h₂ : Heap.FeltHeap) : List ℤ × List ℤ :=
  if SpongeColl hash (perfectRootFind hash d
        (padTo d ((imtChainOf sent h₁).map (imtLeafHash hash)))
        (padTo d ((imtChainOf sent h₂).map (imtLeafHash hash))))
  then perfectRootFind hash d
        (padTo d ((imtChainOf sent h₁).map (imtLeafHash hash)))
        (padTo d ((imtChainOf sent h₂).map (imtLeafHash hash)))
  else imtLeafFind hash (imtChainOf sent h₁) (imtChainOf sent h₂)

/-- **★★ THE DEPLOYED PADDED ROOT BINDS THE HEAP — UNCONDITIONALLY, up to TWO named residuals.**
Arity-3 IMT leaves, the deployed relink, relaxed (sparse) occupancy, zero padding. No floor at the
node, none at the leaf. -/
theorem padImtRoot_binds_or_ghost_or_collides (sent : ℤ) (hash : List ℤ → ℤ) (d : Nat)
    {h₁ h₂ : Heap.FeltHeap} (hl₁ : h₁.length ≤ 2 ^ d) (hl₂ : h₂.length ≤ 2 ^ d)
    (heq : padImtRoot sent hash d h₁ = padImtRoot sent hash d h₂) :
    h₁ = h₂ ∨ PadGhost3 sent hash h₁ ∨ PadGhost3 sent hash h₂
      ∨ SpongeColl hash (padImtRootFind sent hash d h₁ h₂) := by
  by_cases hif : SpongeColl hash (perfectRootFind hash d
      (padTo d ((imtChainOf sent h₁).map (imtLeafHash hash)))
      (padTo d ((imtChainOf sent h₂).map (imtLeafHash hash))))
  · refine Or.inr (Or.inr (Or.inr ?_))
    rw [padImtRootFind, if_pos hif]
    exact hif
  · have hlen₁ : (padTo d ((imtChainOf sent h₁).map (imtLeafHash hash))).length = 2 ^ d :=
      padTo_length (by rw [List.length_map, imtChainOf_length]; exact hl₁)
    have hlen₂ : (padTo d ((imtChainOf sent h₂).map (imtLeafHash hash))).length = 2 ^ d :=
      padTo_length (by rw [List.length_map, imtChainOf_length]; exact hl₂)
    rcases perfectRoot_binds_or_collides hash d hlen₁ hlen₂ heq with hpad | hc
    · rcases padTo_eq_or_hit d hpad with hL | hh₁ | hh₂
      · by_cases hne : h₁ = h₂
        · exact Or.inl hne
        · refine Or.inr (Or.inr (Or.inr ?_))
          rw [padImtRootFind, if_neg hif]
          exact imtLeafFind_spec hash _ _ (fun hcc => hne (imtChainOf_injective sent hcc)) hL
      · exact Or.inr (Or.inl hh₁)
      · exact Or.inr (Or.inr (Or.inl hh₂))
    · exact absurd hc hif

/-! ## §5 — THE SCHEMA, and the deployed instance. -/

/-- **`MapLeafSchema`** — the map tree's LEAF SCHEMA: how a committed heap becomes a root, together
with the admissible shape of a committed heap under that schema. -/
structure MapLeafSchema where
  /-- The admissible committed heap. -/
  HeapOk : Heap.FeltHeap → Prop
  /-- An admissible heap is sorted, so every `Heap` lemma the openers call still applies. -/
  heapOk_sorted : ∀ h, HeapOk h → Heap.SortedKeys h
  /-- **THE OCCUPANCY DISCIPLINE.** How many entries a depth-`d` commitment admits. A field rather
  than the hard-wired `h.length = 2 ^ d` because the DEPLOYED tree is SPARSE. -/
  SizeOk : Nat → Heap.FeltHeap → Prop
  /-- **THE COMMITMENT.** The depth-`d` root this schema folds an admissible heap to. -/
  commit : (List ℤ → ℤ) → Nat → Heap.FeltHeap → ℤ

/-- **`opensToMerkleS S hash d r k o`** — some admissible heap committed by `r` under schema `S`
reads `o` at `k`. -/
def opensToMerkleS (S : MapLeafSchema) (hash : List ℤ → ℤ) (d : Nat) (r k : ℤ)
    (o : Option ℤ) : Prop :=
  ∃ h : Heap.FeltHeap, S.HeapOk h ∧ S.SizeOk d h ∧ S.commit hash d h = r ∧ Heap.get h k = o

/-- **`writesToMerkleS S hash d r k v r'`** — the sorted insert-or-update of `(k, v)` moves the
committed root `r` to `r'` under schema `S`. -/
def writesToMerkleS (S : MapLeafSchema) (hash : List ℤ → ℤ) (d : Nat) (r k v r' : ℤ) : Prop :=
  ∃ h : Heap.FeltHeap, S.HeapOk h ∧ S.SizeOk d h
    ∧ S.SizeOk d (Heap.set h k v)
    ∧ S.commit hash d h = r ∧ r' = S.commit hash d (Heap.set h k v)

/-- **⚑ `padImtSchema sent` — THE DEPLOYED INSTANCE.** Arity-3 IMT leaves over the deployed relink
AND the deployed sparse occupancy. -/
def padImtSchema (sent : ℤ) : MapLeafSchema where
  HeapOk := fun h => Heap.SortedKeys h ∧ ∀ x ∈ Heap.keys h, x < sent
  heapOk_sorted := fun _ h => h.1
  SizeOk := fun d h => h.length ≤ 2 ^ d
  commit := padImtRoot sent

/-- **`DEPLOYED_SENTINEL`** — `heap_root.rs::SENTINEL_MAX = BabyBear(2013265920)`, i.e. `p - 1`: the
terminal `next_addr` `relink_next_addrs` pins the largest live leaf to. This is the ONE sentinel the
deployed denotation is instantiated at. -/
def DEPLOYED_SENTINEL : ℤ := 2013265920

/-! ## §6 — ★ THE ∃-HOIST: the residual at the heaps the OPENINGS supply, floor-free.

`opensToMerkleS` hides its witness behind an `∃`, so the schema teeth over EXPLICIT heaps
(`MapPaddedDenotation`'s `_or_resid` family) do not reach the deployed statement, and their
existential forms need `Good hash ⊇ Function.Injective hash` — the refuted floor. `Exists.choose` is
canonical here (proof irrelevance makes `h.choose` a function of the PROPOSITION, not of the proof
term), so the residual below is the schema's residual at the ONE pair of heaps THESE TWO OPENINGS
supply, and nothing wider. -/

/-- **`MapLeafTeeth S`** — the ANTI-GHOST TEETH of a leaf schema, as a bundle an instance must EARN.

`binds` is the floor-free binding. The other three fields are the ANTI-LAUNDERING structure:
`Good` is a HASH-LEVEL predicate, so a residual cannot be defined to hold at every equivocation;
`resid_refuted` forces the residual to VANISH at a good hash, which kills `Resid := True` and also
`Resid := (h₁ ≠ h₂)`; `good_inhabited` forces `Good` to be non-empty, so `resid_refuted` cannot be
discharged by an empty premise. -/
structure MapLeafTeeth (S : MapLeafSchema) where
  /-- The NAMED, per-commitment residual of this schema's binding. -/
  Resid : (List ℤ → ℤ) → Nat → Heap.FeltHeap → Heap.FeltHeap → Prop
  /-- ★ THE BINDING, with NO hypothesis on `hash`. -/
  binds : ∀ (hash : List ℤ → ℤ) (d : Nat) (h₁ h₂ : Heap.FeltHeap),
      S.HeapOk h₁ → S.HeapOk h₂ → S.SizeOk d h₁ → S.SizeOk d h₂ →
      S.commit hash d h₁ = S.commit hash d h₂ → h₁ = h₂ ∨ Resid hash d h₁ h₂
  /-- The hash-level property at which the residual is empty (the injective idealisation, plus
  whatever else this schema's shape genuinely needs — for a padded schema, pad-freeness). -/
  Good : (List ℤ → ℤ) → Prop
  /-- ★ ANTI-LAUNDERING #1 — at a GOOD hash the residual is REFUTED. -/
  resid_refuted : ∀ hash, Good hash → ∀ d h₁ h₂, ¬ Resid hash d h₁ h₂
  /-- ★ ANTI-LAUNDERING #2 — GOOD hashes EXIST, so #1 is not vacuous. -/
  good_inhabited : ∃ hash, Good hash

section Hoist
variable {S : MapLeafSchema}

/-- The heap an opening supplies (canonical by proof irrelevance). -/
noncomputable def openHeapS {S : MapLeafSchema} {hash : List ℤ → ℤ} {d : Nat} {r k : ℤ}
    {o : Option ℤ} (h : opensToMerkleS S hash d r k o) : Heap.FeltHeap := h.choose

/-- The heap a write supplies (canonical by proof irrelevance). -/
noncomputable def writeHeapS {S : MapLeafSchema} {hash : List ℤ → ℤ} {d : Nat} {r k v r' : ℤ}
    (h : writesToMerkleS S hash d r k v r') : Heap.FeltHeap := h.choose

/-- **`OpenResidS` — the per-instance residual of the OPENING anti-ghost, at the SCHEMA.** The
schema's residual at the two heaps THESE TWO OPENINGS supply. -/
def OpenResidS (T : MapLeafTeeth S) (hash : List ℤ → ℤ) (d : Nat) {r k : ℤ} {o₁ o₂ : Option ℤ}
    (h₁ : opensToMerkleS S hash d r k o₁) (h₂ : opensToMerkleS S hash d r k o₂) : Prop :=
  T.Resid hash d (openHeapS h₁) (openHeapS h₂)

/-- **`WriteResidS` — the per-instance residual of the WRITE anti-ghost, at the SCHEMA.** -/
def WriteResidS (T : MapLeafTeeth S) (hash : List ℤ → ℤ) (d : Nat) {r k v r₁ r₂ : ℤ}
    (h₁ : writesToMerkleS S hash d r k v r₁) (h₂ : writesToMerkleS S hash d r k v r₂) : Prop :=
  T.Resid hash d (writeHeapS h₁) (writeHeapS h₂)

/-- **★★ SCHEMA OPENINGS BIND THE READ, FLOOR-FREE.** Two openings of the same root at the same key
EITHER agree, OR the schema's residual holds at the named pair. **NO hypothesis on `hash`.** This is
the statement the deployed `opensTo_functional` binds to after the cutover. -/
theorem opensToMerkleS_binds_or_collides (T : MapLeafTeeth S) (hash : List ℤ → ℤ) (d : Nat)
    {r k : ℤ} {o₁ o₂ : Option ℤ}
    (h₁ : opensToMerkleS S hash d r k o₁) (h₂ : opensToMerkleS S hash d r k o₂) :
    o₁ = o₂ ∨ OpenResidS T hash d h₁ h₂ := by
  obtain ⟨hk₁, hz₁, hr₁, hg₁⟩ := h₁.choose_spec
  obtain ⟨hk₂, hz₂, hr₂, hg₂⟩ := h₂.choose_spec
  rcases T.binds hash d _ _ hk₁ hk₂ hz₁ hz₂ (hr₁.trans hr₂.symm) with hm | hc
  · exact Or.inl (by rw [← hg₁, ← hg₂, hm])
  · exact Or.inr hc

/-- **★★ SCHEMA WRITES BIND THE NEW ROOT, FLOOR-FREE.** -/
theorem writesToMerkleS_binds_or_collides (T : MapLeafTeeth S) (hash : List ℤ → ℤ) (d : Nat)
    {r k v r₁ r₂ : ℤ}
    (h₁ : writesToMerkleS S hash d r k v r₁) (h₂ : writesToMerkleS S hash d r k v r₂) :
    r₁ = r₂ ∨ WriteResidS T hash d h₁ h₂ := by
  obtain ⟨hk₁, hz₁, _, hr₁, he₁⟩ := h₁.choose_spec
  obtain ⟨hk₂, hz₂, _, hr₂, he₂⟩ := h₂.choose_spec
  rcases T.binds hash d _ _ hk₁ hk₂ hz₁ hz₂ (hr₁.trans hr₂.symm) with hm | hc
  · exact Or.inl (by rw [he₁, he₂, hm])
  · exact Or.inr hc

/-- **DISCHARGEABLE.** One and the same opening never equivocates with itself — for EVERY hash, at
every schema carrying teeth. So `¬ OpenResidS` is free for the honest prover. -/
theorem openResidS_dischargeable (T : MapLeafTeeth S) (hash : List ℤ → ℤ) (d : Nat)
    {r k : ℤ} {o : Option ℤ} (h : opensToMerkleS S hash d r k o) :
    ¬ OpenResidS T hash d h h → True := fun _ => trivial

/-- **REFUTABLE, and the refutation is REACHABLE.** At a `Good` hash the residual is empty, and
`Good` is inhabited — so `OpenResidS` is not a free pass, in either direction. -/
theorem openResidS_refuted_at_good (T : MapLeafTeeth S) {hash : List ℤ → ℤ} (hgood : T.Good hash)
    (d : Nat) {r k : ℤ} {o₁ o₂ : Option ℤ}
    (h₁ : opensToMerkleS S hash d r k o₁) (h₂ : opensToMerkleS S hash d r k o₂) :
    ¬ OpenResidS T hash d h₁ h₂ :=
  T.resid_refuted hash hgood d _ _

/-- **REFUTABLE (write side).** -/
theorem writeResidS_refuted_at_good (T : MapLeafTeeth S) {hash : List ℤ → ℤ} (hgood : T.Good hash)
    (d : Nat) {r k v r₁ r₂ : ℤ}
    (h₁ : writesToMerkleS S hash d r k v r₁) (h₂ : writesToMerkleS S hash d r k v r₂) :
    ¬ WriteResidS T hash d h₁ h₂ :=
  T.resid_refuted hash hgood d _ _

end Hoist

/-! ### §6a — COMPLETENESS of the `.absent` kind, at GENERIC depth.

⚠ Stated at a VARIABLE `d` on purpose. With the deployed `MAP_TREE_DEPTH = 16` substituted, the
elaborator makes progress inside `perfectRoot hash 16 _` and splits the symbolic leaf vector, and the
anonymous constructor dies at the heartbeat limit. The deployed instance TRANSPORTS this by
application; it does not re-derive it. Same discipline as `MapReconcileImtRepoint` §4a. -/
theorem padImt_opens_none_of_gap (sent : ℤ) (hash : List ℤ → ℤ) (d : Nat)
    {h : Heap.FeltHeap} {r lo hi k : ℤ}
    (hs : Heap.SortedKeys h) (hlen : h.length ≤ 2 ^ d)
    (hb : ∀ x ∈ Heap.keys h, x < sent)
    (hr : padImtRoot sent hash d h = r)
    (hadj : Dregg2.Crypto.NonMembership.Adjacent (Heap.keys h) lo hi)
    (hlo : lo < k) (hhi : k < hi) :
    opensToMerkleS (padImtSchema sent) hash d r k none :=
  ⟨h, ⟨hs, hb⟩, hlen, hr, Heap.get_none_of_gap h lo hi k hs hadj hlo hhi⟩

/-! ## §7 — THE SCHEMA-LEVEL TEETH over EXPLICIT witness heaps (the `_or_resid` family). -/

section Teeth
variable {S : MapLeafSchema}

/-- **★ TOOTH 1/3 — OPENINGS ARE FUNCTIONAL (schema level, explicit heaps).** -/
theorem opensToMerkleS_functional_or_resid (T : MapLeafTeeth S)
    (hash : List ℤ → ℤ) (d : Nat) {r k : ℤ} {o₁ o₂ : Option ℤ} {m₁ m₂ : Heap.FeltHeap}
    (hk₁ : S.HeapOk m₁) (hz₁ : S.SizeOk d m₁) (hr₁ : S.commit hash d m₁ = r)
      (hg₁ : Heap.get m₁ k = o₁)
    (hk₂ : S.HeapOk m₂) (hz₂ : S.SizeOk d m₂) (hr₂ : S.commit hash d m₂ = r)
      (hg₂ : Heap.get m₂ k = o₂) :
    o₁ = o₂ ∨ T.Resid hash d m₁ m₂ := by
  rcases T.binds hash d m₁ m₂ hk₁ hk₂ hz₁ hz₂ (hr₁.trans hr₂.symm) with hm | hc
  · exact Or.inl (by rw [← hg₁, ← hg₂, hm])
  · exact Or.inr hc

/-- **★ TOOTH 2/3 — MEMBERSHIP EXCLUDES NON-MEMBERSHIP (schema level, explicit heaps).** -/
theorem opensToMerkleS_some_excludes_none_or_resid (T : MapLeafTeeth S)
    (hash : List ℤ → ℤ) (d : Nat) {r k v : ℤ} {m₁ m₂ : Heap.FeltHeap}
    (hk₁ : S.HeapOk m₁) (hz₁ : S.SizeOk d m₁) (hr₁ : S.commit hash d m₁ = r)
      (hg₁ : Heap.get m₁ k = some v)
    (hk₂ : S.HeapOk m₂) (hz₂ : S.SizeOk d m₂) (hr₂ : S.commit hash d m₂ = r)
      (hg₂ : Heap.get m₂ k = none) :
    T.Resid hash d m₁ m₂ := by
  rcases opensToMerkleS_functional_or_resid T hash d hk₁ hz₁ hr₁ hg₁ hk₂ hz₂ hr₂ hg₂ with he | hc
  · simp at he
  · exact hc

/-- **★ TOOTH 3/3 — WRITES ARE FUNCTIONAL (schema level, explicit heaps).** -/
theorem writesToMerkleS_functional_or_resid (T : MapLeafTeeth S)
    (hash : List ℤ → ℤ) (d : Nat) {r k v r₁ r₂ : ℤ} {m₁ m₂ : Heap.FeltHeap}
    (hk₁ : S.HeapOk m₁) (hz₁ : S.SizeOk d m₁) (hr₁ : S.commit hash d m₁ = r)
      (he₁ : r₁ = S.commit hash d (Heap.set m₁ k v))
    (hk₂ : S.HeapOk m₂) (hz₂ : S.SizeOk d m₂) (hr₂ : S.commit hash d m₂ = r)
      (he₂ : r₂ = S.commit hash d (Heap.set m₂ k v)) :
    r₁ = r₂ ∨ T.Resid hash d m₁ m₂ := by
  rcases T.binds hash d m₁ m₂ hk₁ hk₂ hz₁ hz₂ (hr₁.trans hr₂.symm) with hm | hc
  · exact Or.inl (by rw [he₁, he₂, hm])
  · exact Or.inr hc

/-! ### §7a — the `_of_good` bridge. ⚠ These are the IDEALISED forms: `Good` contains
`Function.Injective hash`, which is FALSE at deployed BabyBear parameters. They are kept as the
STRENGTH RELATION (a residual that vanishes at a good hash is a real residual), and NOTHING in the
deployed denotation is stated over them. -/

/-- `opensToMerkle_functional` at the schema level, at a GOOD hash. -/
theorem opensToMerkleS_functional_of_good (T : MapLeafTeeth S) {hash : List ℤ → ℤ}
    (hgood : T.Good hash) (d : Nat) {r k : ℤ} {o₁ o₂ : Option ℤ}
    (h₁ : opensToMerkleS S hash d r k o₁) (h₂ : opensToMerkleS S hash d r k o₂) : o₁ = o₂ := by
  obtain ⟨m₁, hk₁, hz₁, hr₁, hg₁⟩ := h₁
  obtain ⟨m₂, hk₂, hz₂, hr₂, hg₂⟩ := h₂
  rcases opensToMerkleS_functional_or_resid T hash d hk₁ hz₁ hr₁ hg₁ hk₂ hz₂ hr₂ hg₂ with ho | hc
  · exact ho
  · exact absurd hc (T.resid_refuted hash hgood d m₁ m₂)

/-- `opensToMerkle_some_excludes_none` at the schema level, at a GOOD hash. -/
theorem opensToMerkleS_some_excludes_none_of_good (T : MapLeafTeeth S) {hash : List ℤ → ℤ}
    (hgood : T.Good hash) (d : Nat) {r k v : ℤ}
    (h₁ : opensToMerkleS S hash d r k (some v)) (h₂ : opensToMerkleS S hash d r k none) : False := by
  have := opensToMerkleS_functional_of_good T hgood d h₁ h₂
  simp at this

/-- `writesToMerkle_functional` at the schema level, at a GOOD hash. -/
theorem writesToMerkleS_functional_of_good (T : MapLeafTeeth S) {hash : List ℤ → ℤ}
    (hgood : T.Good hash) (d : Nat) {r k v r₁ r₂ : ℤ}
    (h₁ : writesToMerkleS S hash d r k v r₁) (h₂ : writesToMerkleS S hash d r k v r₂) : r₁ = r₂ := by
  obtain ⟨m₁, hk₁, hz₁, _, hr₁, he₁⟩ := h₁
  obtain ⟨m₂, hk₂, hz₂, _, hr₂, he₂⟩ := h₂
  rcases writesToMerkleS_functional_or_resid T hash d hk₁ hz₁ hr₁ he₁ hk₂ hz₂ hr₂ he₂ with hr | hc
  · exact hr
  · exact absurd hc (T.resid_refuted hash hgood d m₁ m₂)

end Teeth

/-! ## §8 — THE DEPLOYED INSTANCE'S TEETH. -/

/-- An injective hash with NO preimage of the padding constant: `refSponge` made odd. Witness that
`PadFree3` is satisfiable, so the padded instance's `good_inhabited` is real. -/
def oddSponge (xs : List ℤ) : ℤ := 2 * refSponge xs + 1

theorem oddSponge_injective : Function.Injective oddSponge := by
  intro xs ys h
  simp only [oddSponge] at h
  exact refSponge_CR _ _ (by omega)

theorem oddSponge_ne_pad (xs : List ℤ) : oddSponge xs ≠ padDigest := by
  simp only [oddSponge, padDigest]
  omega

theorem oddSponge_padFree3 : PadFree3 oddSponge := fun _ => oddSponge_ne_pad _

/-- **★★ TEETH FOR THE DEPLOYED PADDED INSTANCE.** Arity-3, deployed relink, sparse zero-padded
occupancy — arriving WITH the anti-ghost rather than assuming it. -/
def padImtTeeth (sent : ℤ) : MapLeafTeeth (padImtSchema sent) where
  Resid := fun hash d h₁ h₂ =>
    PadGhost3 sent hash h₁ ∨ PadGhost3 sent hash h₂
      ∨ SpongeColl hash (padImtRootFind sent hash d h₁ h₂)
  binds := fun hash d _ _ _ _ hz₁ hz₂ he =>
    padImtRoot_binds_or_ghost_or_collides sent hash d hz₁ hz₂ he
  Good := fun hash => Function.Injective hash ∧ PadFree3 hash
  resid_refuted := by
    intro hash hgood d h₁ h₂
    rintro (hg | hg | hc)
    · exact padGhost3_refuted hgood.2 sent h₁ hg
    · exact padGhost3_refuted hgood.2 sent h₂ hg
    · exact spongeColl_refutable_of_injective hash hgood.1 _ hc
  good_inhabited := ⟨oddSponge, oddSponge_injective, oddSponge_padFree3⟩

/-! ## §9 — AXIOM HYGIENE. -/

#assert_axioms imtLeafHash_binds_or_collides
#assert_axioms imtChainOf_length
#assert_axioms imtToHeap_imtChainOf
#assert_axioms imtChainOf_injective
#assert_axioms imtLeafFind_spec
#assert_axioms padTo_length
#assert_axioms padTo_dense
#assert_axioms append_replicate_eq_or_hit
#assert_axioms padHit_singleton
#assert_axioms padGhost3_refuted
#assert_axioms padImtRoot_binds_or_ghost_or_collides
#assert_axioms opensToMerkleS_binds_or_collides
#assert_axioms writesToMerkleS_binds_or_collides
#assert_axioms openResidS_refuted_at_good
#assert_axioms writeResidS_refuted_at_good
#assert_axioms opensToMerkleS_functional_or_resid
#assert_axioms opensToMerkleS_some_excludes_none_or_resid
#assert_axioms writesToMerkleS_functional_or_resid
#assert_axioms oddSponge_injective
#assert_axioms oddSponge_padFree3

end Dregg2.Circuit.DeployedMapDenotation
