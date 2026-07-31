/-
# `Dregg2.Circuit.MapPaddedDenotation` — STAGE 2b: the PADDED (sparse) map-tree instance, WITH the
  anti-ghost functional teeth, and the exact price of the padding constant.

## The measured gap this closes

`docs/DESIGN-mapop-denotation-move.md` §10.6 measured that relaxing `opensToMerkle`'s
`h.length = 2 ^ d` to `≤` — exactly the `SizeOk` generalisation the padded/sparse instance needs —
**does not survive its own defining module**: `MapMerkleRoot.lean:238`/`:255` feed the relaxed length
to `mapRoot_injective`, which wants `=`. So `opensToMerkle_functional`,
`opensToMerkle_some_excludes_none` and `writesToMerkle_functional` — the three ANTI-GHOST teeth — all
go red at a relaxed occupancy, and the landed `MapDenotationSchema` carries **no** schema-level
functional theorem for a padded instance to inherit. The padded instance was structurally free and
arrived toothless.

## ⚑ THE LOAD-BEARING FINDING: the padded root is NOT injective, and COLLISION-RESISTANCE DOES NOT
   FIX IT — the residual is a FIXED-TARGET PREIMAGE OF THE PADDING CONSTANT

`heap_root.rs` pads every position `≥ n` with the **literal** `BabyBear::ZERO`
(`EMPTY_SUBTREE_ROOTS[0]`, read this session at `heap_root.rs:72-87`; the real leaves are a
contiguous sorted prefix, `CanonicalHeapTree::new:213-262`). The padded leaf-digest vector is a
FUNCTION of the live prefix, so injectivity on prefixes *would* lift — except for one edge case, and
it is the ghost:

> **If a LIVE leaf digest equals the padding constant, the entry becomes INVISIBLE.** The heap
> `h ++ [e]` with `Heap.leafOf hash e = 0` pads to the SAME digest vector as `h`, hence to the same
> root, while `Heap.get` disagrees at `e.1`: one heap PRESENTS the key, the other reports it ABSENT.
> That is precisely what `opensToMerkle_some_excludes_none` forbids.

And this event is **orthogonal to the hash floor**: `Poseidon2SpongeCR hash` is
`∀ xs ys, hash xs = hash ys → xs = ys`, which says nothing about whether the padding constant lies in
the leaf-digest image. §5 EXHIBITS an INJECTIVE hash at which the ghost occurs, at every depth
including the deployed one — so the refutation is not an artefact of the refuted floor, and stating
the result "at `refSponge`" would not have removed it. Six of the last seven obvious approaches on
this epoch were impossible; **the naive form of "prove `mapRoot` injective on the padded domain" is
the seventh, and it is REFUTED.**

Priced at deployed parameters, the residual is a **single-target preimage** search, not a birthday
search: an adversary needs one `(addr, value, next)` with `hash[addr, value, next] = 0`. At the
1-felt scalar commitment this denotation layer uses (`commit : … → ℤ`, BabyBear `p ≈ 2^31`) that is
~2^31 hash evaluations with `next = SENTINEL_MAX` fixed and `value` free — **feasible on a laptop**.
At the deployed 8-felt tree (`HEAP_ZERO8`, `CanonicalHeapTree8`) the same event costs ~2^124. The
deployed-side fix is cheap and named in §9: pad with a DOMAIN-SEPARATED digest instead of a literal
zero, and the padding/leaf separation becomes the same named CR floor rather than a new preimage
event.

⚑ **AND THE CLASS IS A SPREAD.** `cap_root.rs:137-188` pads with the same literal constant
(`CAP_ZERO8`, `EMPTY_SUBTREE_ROOTS[0]`) under the same contiguous-prefix sparse fold, and
`heap_root.rs:48-51` says the sentinels are shared by "the sorted openable trees (heap / cap /
fields)". Grepped both files: **no leaf-digest-vs-padding guard exists anywhere** — the only
`assert_ne!(_, ZERO)` is a test about the empty ROOT (`heap_root.rs:1294`), and the dense reference
build is literally `leaf_digests.resize(capacity, BabyBear::ZERO)` (`heap_root.rs:1554`), which is
exactly the `padTo` modelled below. The argument here transfers verbatim to the CAP and FIELDS trees.

## What is landed here, and the shape chosen

Option (a) — padded injectivity as a plain theorem — is REFUTED (§5). Option (b) — the functional
theorems as schema HYPOTHESES — would push an obligation onto the one instance that cannot discharge
it. What is landed is **(c): the `_or_collides` idiom applied to the padding event.** The binding is
UNCONDITIONAL (no floor hypothesis at all, at either the node or the leaf), and the two residuals are
NAMED, per-commitment and REFUTABLE:

  * `PadGhost2` / `PadGhost3` — *the actual committed leaf-digest vector contains the padding
    constant*. A bounded, decidable property of the data the prover committed. NOT
    `∃ e, leafOf hash e = 0` over the hash's whole domain (which pigeonhole makes unconditionally
    true at deployed parameters and which would therefore carry no more content than `True`).
  * `SpongeColl hash (…Find …)` — the collision of the SPECIFIC pair a TOTAL extractor returns, the
    `3245e88148` idiom, reused verbatim from the 8-felt §5b tower.

`MapLeafTeeth S` (§6) is the schema-level bundle the landed `MapLeafSchema` had nothing of. It carries
`binds` plus **two anti-laundering fields**: `resid_refuted` (a hash-level `Good` predicate kills the
residual outright) and `good_inhabited` (`Good` is non-empty, so `resid_refuted` is not vacuous). A
`Resid := True` or `Resid := (h₁ ≠ h₂)` bundle cannot be built. The three anti-ghost teeth are proved
ONCE over the bundle (§6) and every instance inherits them.

Instances, all three inhabited (§7): `narrowTeeth` (the dense arity-2 deployed-today schema),
`padNarrowTeeth` (arity-2 padded), `padImtTeeth` (**arity-3 IMT leaves AND zero padding — the
deployed tree**). Conservativity (§8): the padded `commit` is *equal* to the dense one on dense heaps
(`padMapRoot_dense`, `padImtRoot_dense`), so the padded instance EXTENDS rather than replaces, and
the three existing dense theorems come back verbatim from the schema-level ones
(`narrow_opensToMerkle_functional` &c.) — the measured §10.6 breakage does not recur.

## Floors

**No new floor, and none assumed.** `mapRoot_binds_or_collides`, `padMapRoot_…` and `padImtRoot_…`
take NO hypothesis on `hash`. `Poseidon2SpongeCR` appears in no type in this file: the injective
idealisation is spelled `Function.Injective` (definitionally the same predicate) and rides only in the
`Good` FIELD of a bundle, where it is refuted-floor-free by construction and where §5 shows it does
NOT discharge the padding ghost. The `refSponge`-vs-`_or_collides` disposition is therefore: the
BINDING half is at the deployed sponge (unconditional); the *strength bridges* (`…_of_good`) are at an
injective idealisation and are labelled as such; and the padding ghost is refuted by NEITHER — it
needs the separate, checkable `PadFree` side condition, which the deployed builder does not check.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; sorry-free; no `native_decide`; no
`decide` on any object containing the depth-16 spine (the deployed-depth exhibits never evaluate a
root — they name it). NEW file; every import read-only.
-/
import Dregg2.Circuit.MapDenotationSchema

namespace Dregg2.Circuit.MapPaddedDenotation

open Dregg2.Substrate
open Dregg2.Circuit.Poseidon2Binding (SpongeColl spongeColl_refutable_of_injective)
open Dregg2.Circuit.Poseidon2Binding.Reference (refSponge refSponge_CR)
open Dregg2.Circuit.MapMerkleRoot (mapNode foldLevel perfectRoot mapRoot opensToMerkle writesToMerkle
  foldLevel_length_half foldLevelFind perfectRootFind foldLevel_binds_or_collides
  perfectRoot_binds_or_collides mapRootFind MapRootSpongeColl mapRoot_binds_or_collides)
open Dregg2.Circuit.MapDenotationSchema (narrowSchema imtSchema)
open Dregg2.Circuit.DeployedMapDenotation (MapLeafSchema opensToMerkleS writesToMerkleS imtChainOf
  MapLeafTeeth padDigest padTo padTo_length padTo_dense PadHit append_replicate_eq_or_hit
  padTo_eq_or_hit padHit_singleton imtChainOf_length imtToHeap_imtChainOf imtChainOf_injective
  imtLeafFind imtLeafFind_spec padImtRoot PadGhost3 PadFree3 padGhost3_refuted padImtRootFind
  padImtRoot_binds_or_ghost_or_collides padImtSchema padImtTeeth oddSponge oddSponge_injective
  oddSponge_ne_pad oddSponge_padFree3 opensToMerkleS_functional_or_resid
  opensToMerkleS_some_excludes_none_or_resid writesToMerkleS_functional_or_resid
  opensToMerkleS_functional_of_good opensToMerkleS_some_excludes_none_of_good
  writesToMerkleS_functional_of_good)
open Dregg2.Circuit.IndexedMerkleTree (ImtLeaf imtLeafHash imtLeafPre imtToHeap)
open Dregg2.Circuit.DescriptorIR2 (MAP_TREE_DEPTH)

set_option autoImplicit false

/-! ## §1 — THE 1-FELT PERFECT-TREE BINDING, FLOOR-FREE — ⚑ NOW A SINGLE COPY, IN `MapMerkleRoot`.

This section used to carry its OWN `mapNodeColl` / `foldLevelFind` / `perfectRootFind` and its own
`mapNode_binds_or_collides` / `foldLevel_binds_or_collides` / `perfectRoot_binds_or_collides` — a
verbatim second tower over the SAME arity-2 fold that `MapMerkleRoot` §3b already carried, differing
only in whether the level extractor branches on list inequality or on collision-ness, and in whether
the residual is spelled `SpongeColl` or the identically-defined `IsSpongeColl`.

That duplication is not cosmetic: it is WHY the cure sat downstream of the wound. `MapMerkleRoot`'s
own `perfectRoot_injective` / `mapRoot_injective` — the last peel of the DEPLOYED map-op anti-ghost —
went on consuming the refuted `Poseidon2SpongeCR` floor while a floor-free binding for the identical
fold existed twice, in files that import it. Both towers are now ONE, at the definition of the fold,
and `MapMerkleRoot`'s keystones ride it (2026-07-28).

The names are `open`ed above, so everything below reads exactly as it did. -/

/-! ## §2 — THE PADDING, and its weld to `heap_root.rs`'s precomputed empty-subtree roots. -/

/-- `heap_root.rs`'s `EMPTY_SUBTREE_ROOTS[k]`: `roots[0] = ZERO`, `roots[k] = heap_node(r,r)`. -/
def emptySubtreeRoot (hash : List ℤ → ℤ) : Nat → ℤ
  | 0     => padDigest
  | k + 1 => mapNode hash (emptySubtreeRoot hash k) (emptySubtreeRoot hash k)

/-- The perfect fold of a CONSTANT level, as an accumulator. -/
def constRoot (hash : List ℤ → ℤ) : Nat → ℤ → ℤ
  | 0,     x => x
  | k + 1, x => constRoot hash k (mapNode hash x x)

theorem foldLevel_replicate (hash : List ℤ → ℤ) :
    ∀ (n : Nat) (x : ℤ), foldLevel hash (List.replicate (2 * n) x)
      = List.replicate n (mapNode hash x x) := by
  intro n
  induction n with
  | zero => intro x; simp [foldLevel]
  | succ m ih =>
    intro x
    have h2 : 2 * (m + 1) = (2 * m) + 1 + 1 := by omega
    rw [h2, List.replicate_succ, List.replicate_succ, foldLevel, ih x, List.replicate_succ]

theorem perfectRoot_replicate (hash : List ℤ → ℤ) :
    ∀ (k : Nat) (x : ℤ), perfectRoot hash k (List.replicate (2 ^ k) x) = constRoot hash k x := by
  intro k
  induction k with
  | zero => intro x; simp [perfectRoot, constRoot]
  | succ k ih =>
    intro x
    have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [perfectRoot, hp, foldLevel_replicate hash (2 ^ k) x, ih (mapNode hash x x), constRoot]

theorem constRoot_succ (hash : List ℤ → ℤ) :
    ∀ (k : Nat) (x : ℤ), constRoot hash (k + 1) x
      = mapNode hash (constRoot hash k x) (constRoot hash k x) := by
  intro k
  induction k with
  | zero => intro x; simp [constRoot]
  | succ k ih => intro x; rw [constRoot, ih (mapNode hash x x), constRoot]

/-- **★ THE PADDING WELD.** An all-padding depth-`k` subtree folds to `heap_root.rs`'s precomputed
`EMPTY_SUBTREE_ROOTS[k]` — the fact the deployed SPARSE fold rests on when it substitutes the
constant in place of folding 65k zeros, so that "roots and witnesses stay byte-identical" to the
dense build (`heap_root.rs:76-80`). This is why modelling the deployed sparse tree as the DENSE fold
of a zero-padded vector is faithful. -/
theorem perfectRoot_all_padding (hash : List ℤ → ℤ) :
    ∀ (k : Nat), perfectRoot hash k (List.replicate (2 ^ k) padDigest) = emptySubtreeRoot hash k := by
  intro k
  rw [perfectRoot_replicate hash k padDigest]
  induction k with
  | zero => rfl
  | succ k ih => rw [constRoot_succ, ih, emptySubtreeRoot]

/-! ## §3 — THE PADDING GHOST: the residual the relaxed occupancy actually costs. -/

/-! ## §4 — THE PADDED COMMITMENTS, and their floor-free bindings.

Two instances, because the deployed tree needs BOTH shape moves: `padMapRoot` is §3-of-the-design's
arity-2 padded fold, and `padImtRoot` is the DEPLOYED one — arity-3 IMT leaves (`HeapLeaf::digest`)
over the relinked chain (`relink_next_addrs`), zero-padded to `2^d`. -/

/-! ### §4a — arity-2 padded. -/

/-- **`padMapRoot hash d h`** — the arity-2 binary fold of the zero-PADDED leaf-digest vector. -/
def padMapRoot (hash : List ℤ → ℤ) (d : Nat) (h : Heap.FeltHeap) : ℤ :=
  perfectRoot hash d (padTo d (h.map (Heap.leafOf hash)))

/-- **`PadGhost2 hash h`** — a LIVE arity-2 leaf digest of `h` equals the padding constant. -/
def PadGhost2 (hash : List ℤ → ℤ) (h : Heap.FeltHeap) : Prop := PadHit (h.map (Heap.leafOf hash))

/-- The hash-level side condition that kills the ghost: the padding constant has NO leaf preimage. -/
def PadFree2 (hash : List ℤ → ℤ) : Prop := ∀ e : ℤ × ℤ, Heap.leafOf hash e ≠ padDigest

theorem padGhost2_refuted {hash : List ℤ → ℤ} (hpf : PadFree2 hash) (h : Heap.FeltHeap) :
    ¬ PadGhost2 hash h := by
  intro hmem
  rw [PadGhost2, PadHit, List.mem_map] at hmem
  obtain ⟨e, _, he⟩ := hmem
  exact hpf e he

/-- The padded arity-2 root extractor: the node descent if it collides, else the leaf scan. TOTAL. -/
def padMapRootFind (hash : List ℤ → ℤ) (d : Nat) (h₁ h₂ : Heap.FeltHeap) : List ℤ × List ℤ :=
  if SpongeColl hash (perfectRootFind hash d (padTo d (h₁.map (Heap.leafOf hash)))
                                             (padTo d (h₂.map (Heap.leafOf hash))))
  then perfectRootFind hash d (padTo d (h₁.map (Heap.leafOf hash)))
                              (padTo d (h₂.map (Heap.leafOf hash)))
  else Heap.mapLeafFind hash h₁ h₂

/-- **★ THE PADDED ARITY-2 ROOT BINDS THE HEAP — UNCONDITIONALLY, up to TWO named residuals.** At
RELAXED occupancy (`≤ 2^d`, the deployed sparse discipline) two heaps publishing the same padded root
are EITHER equal, OR one of them presents a live leaf digest equal to the padding constant, OR the
sponge genuinely collides at the pair the extractor returns. No floor. -/
theorem padMapRoot_binds_or_ghost_or_collides (hash : List ℤ → ℤ) (d : Nat) {h₁ h₂ : Heap.FeltHeap}
    (hl₁ : h₁.length ≤ 2 ^ d) (hl₂ : h₂.length ≤ 2 ^ d)
    (heq : padMapRoot hash d h₁ = padMapRoot hash d h₂) :
    h₁ = h₂ ∨ PadGhost2 hash h₁ ∨ PadGhost2 hash h₂
      ∨ SpongeColl hash (padMapRootFind hash d h₁ h₂) := by
  by_cases hif : SpongeColl hash (perfectRootFind hash d (padTo d (h₁.map (Heap.leafOf hash)))
                                                         (padTo d (h₂.map (Heap.leafOf hash))))
  · refine Or.inr (Or.inr (Or.inr ?_))
    rw [padMapRootFind, if_pos hif]
    exact hif
  · have hlen₁ : (padTo d (h₁.map (Heap.leafOf hash))).length = 2 ^ d :=
      padTo_length (by rw [List.length_map]; exact hl₁)
    have hlen₂ : (padTo d (h₂.map (Heap.leafOf hash))).length = 2 ^ d :=
      padTo_length (by rw [List.length_map]; exact hl₂)
    rcases perfectRoot_binds_or_collides hash d hlen₁ hlen₂ heq with hpad | hc
    · rcases padTo_eq_or_hit d hpad with hL | hh₁ | hh₂
      · by_cases hne : h₁ = h₂
        · exact Or.inl hne
        · refine Or.inr (Or.inr (Or.inr ?_))
          rw [padMapRootFind, if_neg hif]
          exact Heap.mapLeafFind_spec hash h₁ h₂ hne hL
      · exact Or.inr (Or.inl hh₁)
      · exact Or.inr (Or.inr (Or.inl hh₂))
    · exact absurd hc hif

/-! ### §4b — arity-3 padded: THE DEPLOYED TREE. -/

/-! ### §4c — the DENSE arity-2 root: ⚑ MOVED to `MapMerkleRoot` §4a (2026-07-28).

`mapRootFind` and `mapRoot_binds_or_collides` were defined HERE — downstream of the theorem they
cure. `MapMerkleRoot.mapRoot_injective`, one import UP, therefore kept peeling the tree with the
refuted `Poseidon2SpongeCR` floor while its cure sat in a file that imports it, feeding only §7's
`narrowTeeth`. They now live beside `mapRoot`, `mapRoot_injective` is proved FROM
`mapRoot_binds_or_collides`, and both names are `open`ed above, so §7 reads unchanged. -/

/-! ## §5 — ⚑⚑ THE REFUTATION: PADDED INJECTIVITY IS NOT AVAILABLE, AND THE HASH FLOOR DOES NOT
   SUPPLY IT.

This is the first-class negative result of stage 2b. Option (a) of the work order — "prove `mapRoot`
injective on the PADDED domain" — is REFUTED, not merely unproven, and it is refuted at a hash that
satisfies the very injectivity the whole commitment tower assumes. So no amount of strengthening the
hash assumption reaches it: the padding ghost is a SEPARATE event, a fixed-target preimage of a
literal constant, and it must be carried as a named residual (which is what §4 does). -/

/-- **`ghostSpongeAt pre`** — `refSponge` re-based so that `pre` lands exactly on the PADDING
CONSTANT. Still INJECTIVE (subtracting a constant is a bijection of ℤ), so it satisfies the tower's
injectivity idealisation; but the padding constant is now in its leaf-digest image. This models the
one fact about the deployed hash that matters here: a hash whose range covers BabyBear certainly has
a preimage of `0`, and the deployed builder never checks that no live leaf hits it. -/
def ghostSpongeAt (pre : List ℤ) : List ℤ → ℤ := fun xs => refSponge xs - refSponge pre

theorem ghostSpongeAt_injective (pre : List ℤ) : Function.Injective (ghostSpongeAt pre) := by
  intro xs ys h
  simp only [ghostSpongeAt] at h
  exact refSponge_CR _ _ (by omega)

theorem ghostSpongeAt_hit (pre : List ℤ) : ghostSpongeAt pre pre = padDigest := by
  simp only [ghostSpongeAt, padDigest]
  omega

/-- `[padDigest]` and `[]` pad to the SAME `2^d`-vector — the entire ghost, in one line. -/
theorem padTo_singleton_pad (d : Nat) : padTo d [padDigest] = padTo d ([] : List ℤ) := by
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ d = m + 1 := ⟨2 ^ d - 1, by have := Nat.one_le_pow d 2 (by norm_num); omega⟩
  simp only [padTo, List.length_cons, List.length_nil, List.nil_append, Nat.sub_zero, hm]
  simp [List.replicate_succ]

/-- **⚑⚑ THE GHOST, EXHIBITED AT THE DEPLOYED PADDING CONSTANT — arity-2.** At the INJECTIVE hash
`ghostSpongeAt [a, v]`, the one-entry sorted heap `[(a, v)]` and the EMPTY heap — both of admissible
sparse occupancy at EVERY depth, including the deployed `MAP_TREE_DEPTH = 16` — publish the SAME
padded root while DISAGREEING at the key `a`: one PRESENTS it, the other reports it ABSENT. -/
theorem padded_ghost2 (a v : ℤ) (d : Nat) :
    Function.Injective (ghostSpongeAt [a, v])
    ∧ Heap.SortedKeys [(a, v)] ∧ Heap.SortedKeys ([] : Heap.FeltHeap)
    ∧ ([(a, v)] : Heap.FeltHeap).length ≤ 2 ^ d ∧ ([] : Heap.FeltHeap).length ≤ 2 ^ d
    ∧ padMapRoot (ghostSpongeAt [a, v]) d [(a, v)] = padMapRoot (ghostSpongeAt [a, v]) d []
    ∧ Heap.get [(a, v)] a = some v ∧ Heap.get ([] : Heap.FeltHeap) a = none := by
  refine ⟨ghostSpongeAt_injective _, by simp [Heap.SortedKeys, Heap.keys],
    by simp [Heap.SortedKeys, Heap.keys], ?_, ?_, ?_, by simp, by simp⟩
  · exact Nat.one_le_pow d 2 (by norm_num)
  · exact Nat.zero_le _
  · show perfectRoot _ d (padTo d ([(a, v)].map (Heap.leafOf (ghostSpongeAt [a, v]))))
      = perfectRoot _ d (padTo d (([] : Heap.FeltHeap).map (Heap.leafOf (ghostSpongeAt [a, v]))))
    have hleaf : Heap.leafOf (ghostSpongeAt [a, v]) (a, v) = padDigest := ghostSpongeAt_hit [a, v]
    rw [List.map_cons, List.map_nil, hleaf, padTo_singleton_pad]

/-- **⚑⚑ THE GHOST AT THE DEPLOYED TREE — arity-3 IMT leaves, deployed relink, zero padding.** Same
shape at the commitment `heap_root.rs` actually computes. Both heaps are `HeapOk` for the deployed
schema (sorted, every key below the terminal sentinel). -/
theorem padded_ghost3 (a v sent : ℤ) (ha : a < sent) (d : Nat) :
    Function.Injective (ghostSpongeAt [a, v, sent])
    ∧ (Heap.SortedKeys [(a, v)] ∧ ∀ x ∈ Heap.keys [(a, v)], x < sent)
    ∧ (Heap.SortedKeys ([] : Heap.FeltHeap) ∧ ∀ x ∈ Heap.keys ([] : Heap.FeltHeap), x < sent)
    ∧ ([(a, v)] : Heap.FeltHeap).length ≤ 2 ^ d ∧ ([] : Heap.FeltHeap).length ≤ 2 ^ d
    ∧ padImtRoot sent (ghostSpongeAt [a, v, sent]) d [(a, v)]
        = padImtRoot sent (ghostSpongeAt [a, v, sent]) d []
    ∧ Heap.get [(a, v)] a = some v ∧ Heap.get ([] : Heap.FeltHeap) a = none := by
  refine ⟨ghostSpongeAt_injective _,
    ⟨by simp [Heap.SortedKeys, Heap.keys], by simpa [Heap.keys] using ha⟩,
    ⟨by simp [Heap.SortedKeys, Heap.keys], by simp [Heap.keys]⟩,
    Nat.one_le_pow d 2 (by norm_num), Nat.zero_le _, ?_, by simp, by simp⟩
  show perfectRoot _ d (padTo d ((imtChainOf sent [(a, v)]).map
        (imtLeafHash (ghostSpongeAt [a, v, sent]))))
    = perfectRoot _ d (padTo d ((imtChainOf sent ([] : Heap.FeltHeap)).map
        (imtLeafHash (ghostSpongeAt [a, v, sent]))))
  have hchain : imtChainOf sent [(a, v)] = [(⟨a, v, sent⟩ : ImtLeaf)] := rfl
  have hleaf : imtLeafHash (ghostSpongeAt [a, v, sent]) (⟨a, v, sent⟩ : ImtLeaf) = padDigest :=
    ghostSpongeAt_hit [a, v, sent]
  rw [hchain, List.map_cons, List.map_nil, hleaf]
  show perfectRoot _ d (padTo d [padDigest]) = perfectRoot _ d (padTo d ([] : List ℤ))
  rw [padTo_singleton_pad]

/-- **⚑⚑ OPTION (a) IS REFUTED.** There is NO theorem "the padded root is injective on sorted heaps
of admissible sparse occupancy", not even under the tower's injectivity idealisation — which is
`Poseidon2SpongeCR` definitionally. The witness is `padded_ghost2`. (Anti-floor content: the
conclusion is `False`.) -/
theorem padded_injectivity_is_refuted :
    ¬ (∀ (hash : List ℤ → ℤ), Function.Injective hash → ∀ (d : Nat) (h₁ h₂ : Heap.FeltHeap),
        Heap.SortedKeys h₁ → Heap.SortedKeys h₂ → h₁.length ≤ 2 ^ d → h₂.length ≤ 2 ^ d →
        padMapRoot hash d h₁ = padMapRoot hash d h₂ → h₁ = h₂) := by
  intro hbad
  obtain ⟨hinj, hs₁, hs₂, hz₁, hz₂, hroot, _, _⟩ := padded_ghost2 0 0 1
  exact absurd (hbad _ hinj 1 _ _ hs₁ hs₂ hz₁ hz₂ hroot) (by simp)

/-- **⚑⚑ AND IT IS REFUTED AT THE DEPLOYED TREE, AT THE DEPLOYED DEPTH.** Arity-3 leaves, the
deployed relink, `MAP_TREE_DEPTH = 16`, terminal sentinel free. (Anti-floor content.) -/
theorem padded_imt_injectivity_is_refuted (sent : ℤ) (hs : 0 < sent) :
    ¬ (∀ (hash : List ℤ → ℤ), Function.Injective hash → ∀ (h₁ h₂ : Heap.FeltHeap),
        Heap.SortedKeys h₁ → Heap.SortedKeys h₂ →
        h₁.length ≤ 2 ^ MAP_TREE_DEPTH → h₂.length ≤ 2 ^ MAP_TREE_DEPTH →
        padImtRoot sent hash MAP_TREE_DEPTH h₁ = padImtRoot sent hash MAP_TREE_DEPTH h₂ →
        h₁ = h₂) := by
  intro hbad
  obtain ⟨hinj, ⟨hs₁, _⟩, ⟨hs₂, _⟩, hz₁, hz₂, hroot, _, _⟩ :=
    padded_ghost3 0 0 sent hs MAP_TREE_DEPTH
  exact absurd (hbad _ hinj _ _ hs₁ hs₂ hz₁ hz₂ hroot) (by simp)

/-! ## §6 — THE SCHEMA-LEVEL TEETH: what the landed `MapLeafSchema` had nothing of. -/

section Teeth
variable {S : MapLeafSchema}

/-! ### §6.S — the EXISTENTIAL-level teeth at a GOOD hash: the three theorems the design doc names,
recovered VERBATIM in shape over `opensToMerkleS` / `writesToMerkleS`, for ANY schema carrying teeth.
These are the statements the padded instance had nothing to inherit; they now exist once. -/

end Teeth

/-! ## §7 — THE INSTANCES. Three, all INHABITED — the schema-level teeth are not an ∃-image. -/

theorem oddSponge_padFree2 : PadFree2 oddSponge := fun _ => oddSponge_ne_pad _
/-- **TEETH FOR THE DENSE arity-2 schema (the RETIRED shape).** No padding, hence NO ghost: the residual
is a genuine sponge collision and nothing else. This is the CONSERVATIVITY anchor of §8 — and that is
all it is. ⚠ This doc-comment said "(deployed-today)", inheriting the false claim in
`MapDenotationSchema.narrowSchema`'s own header: the deployed instance is `padImtSchema` below
(arity-3 IMT leaves, deployed relink, sparse padded occupancy), with `padImtTeeth`. -/
def narrowTeeth : MapLeafTeeth narrowSchema where
  Resid := fun hash d h₁ h₂ => MapRootSpongeColl hash d h₁ h₂
  binds := fun hash d _ _ _ _ hz₁ hz₂ he => mapRoot_binds_or_collides hash d hz₁ hz₂ he
  Good := Function.Injective
  resid_refuted := fun _ hg _ _ _ => fun hc => hc.1 (hg hc.2)
  good_inhabited := ⟨refSponge, refSponge_CR⟩

/-- **`padNarrowSchema`** — the design doc §3's padded/sparse instance at arity 2: `SizeOk` relaxed
to `≤ 2 ^ d`, `commit` folding the prefix against the constant-zero padding. `HeapOk` is UNCHANGED
(`Heap.SortedKeys`) — the pad-freeness deliberately does NOT go here, because the deployed builder
cannot discharge it; it rides in the CONCLUSION as a named residual instead. -/
def padNarrowSchema : MapLeafSchema where
  HeapOk := Heap.SortedKeys
  heapOk_sorted := fun _ h => h
  SizeOk := fun d h => h.length ≤ 2 ^ d
  commit := padMapRoot

/-- **TEETH FOR THE arity-2 PADDED schema.** -/
def padNarrowTeeth : MapLeafTeeth padNarrowSchema where
  Resid := fun hash d h₁ h₂ =>
    PadGhost2 hash h₁ ∨ PadGhost2 hash h₂ ∨ SpongeColl hash (padMapRootFind hash d h₁ h₂)
  binds := fun hash d _ _ _ _ hz₁ hz₂ he =>
    padMapRoot_binds_or_ghost_or_collides hash d hz₁ hz₂ he
  Good := fun hash => Function.Injective hash ∧ PadFree2 hash
  resid_refuted := by
    intro hash hgood d h₁ h₂
    rintro (hg | hg | hc)
    · exact padGhost2_refuted hgood.2 h₁ hg
    · exact padGhost2_refuted hgood.2 h₂ hg
    · exact spongeColl_refutable_of_injective hash hgood.1 _ hc
  good_inhabited := ⟨oddSponge, oddSponge_injective, oddSponge_padFree2⟩

/-! ## §8 — CONSERVATIVITY: the padded instances EXTEND the dense ones, and the three dense theorems
come back verbatim.

The measured §10.6 breakage was that the three FUNCTIONAL theorems die at a relaxed occupancy. They do
not die here, in either direction:

  * the padded `commit` is EQUAL to the dense one on a dense heap (`padMapRoot_dense`,
    `padImtRoot_dense`), so the padded schema is a conservative EXTENSION of the landed pair rather
    than a rival commitment; and
  * the dense theorems are re-derived FROM the schema-level teeth at `narrowTeeth`, at the same
    statement shape they have in `MapMerkleRoot`. -/

theorem padMapRoot_dense (hash : List ℤ → ℤ) (d : Nat) {h : Heap.FeltHeap}
    (hlen : h.length = 2 ^ d) : padMapRoot hash d h = mapRoot hash d h := by
  show perfectRoot hash d (padTo d (h.map (Heap.leafOf hash)))
    = perfectRoot hash d (h.map (Heap.leafOf hash))
  rw [padTo_dense (by rw [List.length_map]; exact hlen)]

theorem padImtRoot_dense (sent : ℤ) (hash : List ℤ → ℤ) (d : Nat) {h : Heap.FeltHeap}
    (hlen : h.length = 2 ^ d) : padImtRoot sent hash d h = (imtSchema sent).commit hash d h := by
  have hd : padTo d ((imtChainOf sent h).map (imtLeafHash hash))
      = (imtChainOf sent h).map (imtLeafHash hash) :=
    padTo_dense (by rw [List.length_map, imtChainOf_length]; exact hlen)
  simp only [padImtRoot, hd, Dregg2.Circuit.MapDenotationSchema.imtSchema]

/-- A DENSE opening is a PADDED opening: the padded denotation CONTAINS the deployed-today one, so
nothing that held before is lost by relaxing the occupancy. -/
theorem opensToMerkle_to_padded (hash : List ℤ → ℤ) (d : Nat) {r k : ℤ} {o : Option ℤ}
    (h : opensToMerkle hash d r k o) : opensToMerkleS padNarrowSchema hash d r k o := by
  obtain ⟨m, hs, hlen, hr, hg⟩ := h
  exact ⟨m, hs, le_of_eq hlen, by rw [show padNarrowSchema.commit hash d m = padMapRoot hash d m from rfl,
    padMapRoot_dense hash d hlen]; exact hr, hg⟩

/-- **★ CONSERVATIVITY 1/3 — `opensToMerkle_functional`, recovered from the schema-level tooth.**
Statement shape identical to `MapMerkleRoot.opensToMerkle_functional`, with the refuted
`Poseidon2SpongeCR` floor replaced by the injectivity it definitionally is. -/
theorem narrow_opensToMerkle_functional (hash : List ℤ → ℤ) (hinj : Function.Injective hash)
    (d : Nat) {r k : ℤ} {o₁ o₂ : Option ℤ}
    (h₁ : opensToMerkle hash d r k o₁) (h₂ : opensToMerkle hash d r k o₂) : o₁ = o₂ :=
  opensToMerkleS_functional_of_good narrowTeeth hinj d h₁ h₂

/-- **★ CONSERVATIVITY 2/3 — `opensToMerkle_some_excludes_none`, recovered. -/
theorem narrow_opensToMerkle_some_excludes_none (hash : List ℤ → ℤ)
    (hinj : Function.Injective hash) (d : Nat) {r k v : ℤ}
    (h₁ : opensToMerkle hash d r k (some v)) (h₂ : opensToMerkle hash d r k none) : False :=
  opensToMerkleS_some_excludes_none_of_good narrowTeeth hinj d h₁ h₂

/-- **★ CONSERVATIVITY 3/3 — `writesToMerkle_functional`, recovered. -/
theorem narrow_writesToMerkle_functional (hash : List ℤ → ℤ) (hinj : Function.Injective hash)
    (d : Nat) {r k v r₁ r₂ : ℤ}
    (h₁ : writesToMerkle hash d r k v r₁) (h₂ : writesToMerkle hash d r k v r₂) : r₁ = r₂ :=
  writesToMerkleS_functional_of_good narrowTeeth hinj d h₁ h₂

/-! ## §9 — THE TEETH BITE AT THE DEPLOYED PADDING CONSTANT (the non-vacuity exhibit).

A schema-level functional theorem with no inhabited padded instance would be exactly the ∃-image
mistake this campaign spent two days refuting. So both halves are exhibited concretely, at the
DEPLOYED depth `MAP_TREE_DEPTH = 16`, at the DEPLOYED padding constant, on the DEPLOYED arity-3
padded instance. Nothing below evaluates a root: the root is NAMED as the schema's own `commit`. -/

section Bite

/-- A one-entry deployed padded heap: key `1`, value `7`, terminal sentinel `3`. Sparse — one live
leaf in a `2^16`-leaf tree, which is what `heap_root.rs` actually builds and what the DENSE
`opensToMerkle` has no witness for. -/
def biteHeap : Heap.FeltHeap := [(1, 7)]
/-- Its terminal sentinel. -/
def biteSent : ℤ := 3
/-- Its committed root, at the deployed depth. NAMED, never evaluated. -/
noncomputable def biteRoot : ℤ :=
  (padImtSchema biteSent).commit oddSponge MAP_TREE_DEPTH biteHeap

theorem bite_heapOk : (padImtSchema biteSent).HeapOk biteHeap := by
  refine ⟨by simp [Heap.SortedKeys, Heap.keys, biteHeap], ?_⟩
  intro x hx
  simp only [biteHeap, Heap.keys, List.map_cons, List.map_nil, List.mem_singleton] at hx
  subst hx
  show (1 : ℤ) < biteSent
  norm_num [biteSent]

theorem bite_sizeOk : (padImtSchema biteSent).SizeOk MAP_TREE_DEPTH biteHeap := by
  show biteHeap.length ≤ 2 ^ MAP_TREE_DEPTH
  show 1 ≤ 2 ^ MAP_TREE_DEPTH
  exact Nat.one_le_pow _ 2 (by norm_num)

/-- **★ THE TREE PRESENTS THE KEY.** The padded, deployed-shape denotation is INHABITED on a SPARSE
tree — which is precisely what the dense `opensToMerkle` is not. -/
theorem bite_presents :
    opensToMerkleS (padImtSchema biteSent) oddSponge MAP_TREE_DEPTH biteRoot 1 (some 7) :=
  ⟨biteHeap, bite_heapOk, bite_sizeOk, rfl, by simp [biteHeap]⟩

/-- **★★ THE ANTI-GHOST TOOTH BITES, AT THE DEPLOYED PADDING CONSTANT.** No prover can open the SAME
committed padded root at the SAME key as ABSENT. This is the statement the padded instance arrived
WITHOUT, and the reason the move is worth making — a denotation that cannot refuse a ghost refuses
nothing. It holds at `oddSponge`, a hash that is injective AND `PadFree3`; §5 shows the second
conjunct is INDISPENSABLE, since dropping it makes this very statement FALSE. -/
theorem bite_absence_is_refused :
    ¬ opensToMerkleS (padImtSchema biteSent) oddSponge MAP_TREE_DEPTH biteRoot 1 none := fun hno =>
  opensToMerkleS_some_excludes_none_of_good (padImtTeeth biteSent)
    ⟨oddSponge_injective, oddSponge_padFree3⟩ MAP_TREE_DEPTH bite_presents hno

/-- **★★ AND THE WRITE TOOTH BITES.** The `new_root` column of a deployed padded map-op row is
determined by `(root, key, value)`. -/
theorem bite_write_is_functional {r₁ r₂ : ℤ}
    (h₁ : writesToMerkleS (padImtSchema biteSent) oddSponge MAP_TREE_DEPTH biteRoot 1 9 r₁)
    (h₂ : writesToMerkleS (padImtSchema biteSent) oddSponge MAP_TREE_DEPTH biteRoot 1 9 r₂) :
    r₁ = r₂ :=
  writesToMerkleS_functional_of_good (padImtTeeth biteSent)
    ⟨oddSponge_injective, oddSponge_padFree3⟩ MAP_TREE_DEPTH h₁ h₂

/-- **★★ THE GHOST PAIR IS EXACTLY THE NAMED RESIDUAL, not an unnamed escape.** Fed to the tooth,
`padded_ghost3`'s two colliding heaps do not yield `False` — they yield `PadGhost3` at the entry whose
leaf digest IS the padding constant. So the residual is REACHED by the attack it prices, and the
disjunction is informative in both directions. -/
theorem ghost_pair_is_the_named_resid (a v sent : ℤ) (d : Nat) :
    (padImtTeeth sent).Resid (ghostSpongeAt [a, v, sent]) d [(a, v)] [] := by
  refine Or.inl ?_
  show PadHit ((imtChainOf sent [(a, v)]).map (imtLeafHash (ghostSpongeAt [a, v, sent])))
  have hchain : imtChainOf sent [(a, v)] = [(⟨a, v, sent⟩ : ImtLeaf)] := rfl
  have hleaf : imtLeafHash (ghostSpongeAt [a, v, sent]) (⟨a, v, sent⟩ : ImtLeaf) = padDigest :=
    ghostSpongeAt_hit [a, v, sent]
  rw [hchain, List.map_cons, List.map_nil, hleaf]
  exact padHit_singleton

end Bite

/-! ## §10 — AXIOM HYGIENE. -/

#assert_axioms padTo_length
#assert_axioms padTo_dense
#assert_axioms perfectRoot_all_padding
#assert_axioms append_replicate_eq_or_hit
#assert_axioms padTo_eq_or_hit
#assert_axioms padMapRoot_binds_or_ghost_or_collides
#assert_axioms imtChainOf_length
#assert_axioms imtToHeap_imtChainOf
#assert_axioms imtChainOf_injective
#assert_axioms imtLeafFind_spec
#assert_axioms padImtRoot_binds_or_ghost_or_collides
#assert_axioms ghostSpongeAt_injective
#assert_axioms padded_ghost2
#assert_axioms padded_ghost3
#assert_axioms padded_injectivity_is_refuted
#assert_axioms padded_imt_injectivity_is_refuted
#assert_axioms opensToMerkleS_functional_or_resid
#assert_axioms opensToMerkleS_some_excludes_none_or_resid
#assert_axioms writesToMerkleS_functional_or_resid
#assert_axioms opensToMerkleS_functional_of_good
#assert_axioms opensToMerkleS_some_excludes_none_of_good
#assert_axioms writesToMerkleS_functional_of_good
#assert_axioms padMapRoot_dense
#assert_axioms padImtRoot_dense
#assert_axioms opensToMerkle_to_padded
#assert_axioms narrow_opensToMerkle_functional
#assert_axioms narrow_opensToMerkle_some_excludes_none
#assert_axioms narrow_writesToMerkle_functional
#assert_axioms bite_presents
#assert_axioms bite_absence_is_refused
#assert_axioms bite_write_is_functional
#assert_axioms ghost_pair_is_the_named_resid

/-! ## §Re-export — emitted LAST, so the body's bare names stay unambiguous.

⚑⚑ **THESE 32 DECLARATIONS MOVED UPSTREAM (2026-07-30)** to
`Dregg2.Circuit.DeployedMapDenotation`, and are re-exported here so every consumer's existing
`open Dregg2.Circuit.MapPaddedDenotation (…)` resolves UNCHANGED — to the SAME constant.

They had to move because `DescriptorIR2.opensTo`/`writesTo` now DENOTE `padImtSchema
MAP_SENTINEL`, and `DescriptorIR2` is upstream of this module. A second `padImtSchema` here would
have been strictly worse than the wound this file closed: `MapKindImtGates`' four arm laws, stated
over it, would be theorems about a schema the deployed denotation does not use — green, and about
nothing. There is ONE `padImtSchema` in the tree, and one `MapLeafTeeth`.

⚠ `oddSponge` changed WITNESS in the move: it was `2 * refSponge xs + 1`, whose injectivity is
`refSponge_CR : Poseidon2SpongeCR refSponge` — which put the REFUTED floor constant into the
proof-term closure of `padImtTeeth`, hence of `opensTo_functional`, hence of every apex route. It is
an `Encodable` injection now: same content, no Poseidon2-flavoured constant, so
`#assert_not_depends_on … [Poseidon2SpongeCR]` on the deployed anti-ghost can be LANDED instead of
relaxed. -/
export Dregg2.Circuit.DeployedMapDenotation (MapLeafTeeth padDigest padTo padTo_length padTo_dense
  PadHit append_replicate_eq_or_hit padTo_eq_or_hit padHit_singleton imtChainOf_length
  imtToHeap_imtChainOf imtChainOf_injective imtLeafFind imtLeafFind_spec padImtRoot PadGhost3
  PadFree3 padGhost3_refuted padImtRootFind padImtRoot_binds_or_ghost_or_collides padImtSchema
  padImtTeeth oddSponge oddSponge_injective oddSponge_ne_pad oddSponge_padFree3
  opensToMerkleS_functional_or_resid opensToMerkleS_some_excludes_none_or_resid
  writesToMerkleS_functional_or_resid opensToMerkleS_functional_of_good
  opensToMerkleS_some_excludes_none_of_good writesToMerkleS_functional_of_good)

end Dregg2.Circuit.MapPaddedDenotation
