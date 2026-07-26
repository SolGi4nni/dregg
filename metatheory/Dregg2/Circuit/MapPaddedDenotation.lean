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
  foldLevel_length_half)
open Dregg2.Circuit.MapDenotationSchema (MapLeafSchema narrowSchema imtSchema imtChainOf
  opensToMerkleS writesToMerkleS)
open Dregg2.Circuit.IndexedMerkleTree (ImtLeaf imtLeafHash imtLeafPre imtToHeap)
open Dregg2.Circuit.DescriptorIR2 (MAP_TREE_DEPTH)

set_option autoImplicit false

/-! ## §1 — THE 1-FELT PERFECT-TREE BINDING, FLOOR-FREE.

`MapMerkleRoot` proves `perfectRoot_injective` under `Poseidon2SpongeCR`, which is FALSE at deployed
BabyBear parameters. The 8-felt §5b tower already carries the cured form; the 1-felt scalar layer —
the one the map DENOTATION rides — did not. These are its total extractors, mechanically mirroring
`foldLevel8Find` / `perfectRoot8Find`. Nothing below assumes anything about `hash`. -/

/-- The two absorbed arity-2 node blocks of a `mapNode` equivocation, NAMED. -/
def mapNodeColl (l₁ r₁ l₂ r₂ : ℤ) : List ℤ × List ℤ := ([l₁, r₁], [l₂, r₂])

/-- **The 2-to-1 node BINDS its children, UNCONDITIONAL.** The cured `mapNode_injective`. -/
theorem mapNode_binds_or_collides (hash : List ℤ → ℤ) {l₁ r₁ l₂ r₂ : ℤ}
    (h : mapNode hash l₁ r₁ = mapNode hash l₂ r₂) :
    (l₁ = l₂ ∧ r₁ = r₂) ∨ SpongeColl hash (mapNodeColl l₁ r₁ l₂ r₂) := by
  by_cases hp : ([l₁, r₁] : List ℤ) = [l₂, r₂]
  · refine Or.inl ?_
    simp only [List.cons.injEq, and_true] at hp
    exact ⟨hp.1, hp.2⟩
  · exact Or.inr ⟨hp, h⟩

/-- **The one-level EXTRACTOR** — scan two Merkle levels pairwise and return the first pair of arity-2
node blocks that is a GENUINE collision; `([], [])` if the scan runs out (the spec's terminal cases
deliver equality outright and never read it). TOTAL. -/
def foldLevelFind (hash : List ℤ → ℤ) : List ℤ → List ℤ → List ℤ × List ℤ
  | l :: r :: rest, l' :: r' :: rest' =>
      if SpongeColl hash (mapNodeColl l r l' r')
      then mapNodeColl l r l' r'
      else foldLevelFind hash rest rest'
  | _, _ => ([], [])

/-- **One fold level BINDS its input, UNCONDITIONAL** (the cured `foldLevel_injective`). -/
theorem foldLevel_binds_or_collides (hash : List ℤ → ℤ) :
    ∀ (n : Nat) {xs ys : List ℤ}, xs.length = 2 * n → ys.length = 2 * n →
      foldLevel hash xs = foldLevel hash ys →
      xs = ys ∨ SpongeColl hash (foldLevelFind hash xs ys) := by
  intro n
  induction n with
  | zero =>
    intro xs ys hx hy _
    have hxe : xs = [] := List.length_eq_zero_iff.mp (by omega)
    have hye : ys = [] := List.length_eq_zero_iff.mp (by omega)
    exact Or.inl (by rw [hxe, hye])
  | succ m ih =>
    intro xs ys hx hy hfold
    match xs, hx, ys, hy with
    | l :: r :: rest, hx, l' :: r' :: rest', hy =>
      simp only [foldLevel, List.cons.injEq] at hfold
      obtain ⟨hnode, hrest⟩ := hfold
      by_cases hif : SpongeColl hash (mapNodeColl l r l' r')
      · refine Or.inr ?_
        show SpongeColl hash (foldLevelFind hash (l :: r :: rest) (l' :: r' :: rest'))
        rw [foldLevelFind, if_pos hif]
        exact hif
      · rcases mapNode_binds_or_collides hash hnode with ⟨hl, hr⟩ | hc
        · simp only [List.length_cons] at hx hy
          have hxlen : rest.length = 2 * m := by omega
          have hylen : rest'.length = 2 * m := by omega
          rcases ih hxlen hylen hrest with htail | hct
          · exact Or.inl (by rw [hl, hr, htail])
          · refine Or.inr ?_
            show SpongeColl hash (foldLevelFind hash (l :: r :: rest) (l' :: r' :: rest'))
            rw [foldLevelFind, if_neg hif]
            exact hct
        · exact absurd hc hif

/-- **The perfect-tree EXTRACTOR** — descend the `d` fold levels; if the deeper walk found a genuine
collision that is the answer, otherwise the deeper levels are already forced equal and the collision
(if any) is at THIS level. TOTAL. -/
def perfectRootFind (hash : List ℤ → ℤ) : Nat → List ℤ → List ℤ → List ℤ × List ℤ
  | 0,     _,  _  => ([], [])
  | d + 1, xs, ys =>
      if SpongeColl hash (perfectRootFind hash d (foldLevel hash xs) (foldLevel hash ys))
      then perfectRootFind hash d (foldLevel hash xs) (foldLevel hash ys)
      else foldLevelFind hash xs ys

/-- **★ THE 1-FELT BINARY-MERKLE ROOT BINDS ITS LEAF-DIGEST VECTOR, UNCONDITIONAL.** The cured
`perfectRoot_injective`: two length-`2^d` digest vectors with equal roots are EITHER equal, OR the
descent lands on a level whose two node blocks genuinely collide. No floor. -/
theorem perfectRoot_binds_or_collides (hash : List ℤ → ℤ) :
    ∀ (d : Nat) {xs ys : List ℤ}, xs.length = 2 ^ d → ys.length = 2 ^ d →
      perfectRoot hash d xs = perfectRoot hash d ys →
      xs = ys ∨ SpongeColl hash (perfectRootFind hash d xs ys) := by
  intro d
  induction d with
  | zero =>
    intro xs ys hx hy hroot
    rw [pow_zero] at hx hy
    match xs, ys, hx, hy with
    | [x], [y], _, _ =>
      simp only [perfectRoot, List.headD_cons] at hroot
      exact Or.inl (by rw [hroot])
  | succ d ih =>
    intro xs ys hx hy hroot
    simp only [perfectRoot] at hroot
    have hfl_x : (foldLevel hash xs).length = 2 ^ d :=
      foldLevel_length_half hash (2 ^ d) xs (by omega)
    have hfl_y : (foldLevel hash ys).length = 2 ^ d :=
      foldLevel_length_half hash (2 ^ d) ys (by omega)
    by_cases hif : SpongeColl hash
        (perfectRootFind hash d (foldLevel hash xs) (foldLevel hash ys))
    · refine Or.inr ?_
      show SpongeColl hash (perfectRootFind hash (d + 1) xs ys)
      rw [perfectRootFind, if_pos hif]
      exact hif
    · rcases ih hfl_x hfl_y hroot with hfold | hc
      · rcases foldLevel_binds_or_collides hash (2 ^ d) (by omega) (by omega) hfold with hxy | hcl
        · exact Or.inl hxy
        · refine Or.inr ?_
          show SpongeColl hash (perfectRootFind hash (d + 1) xs ys)
          rw [perfectRootFind, if_neg hif]
          exact hcl
      · exact absurd hc hif

/-! ## §2 — THE PADDING, and its weld to `heap_root.rs`'s precomputed empty-subtree roots. -/

/-- **`padDigest`** — `heap_root.rs`'s padding marker: the LITERAL `BabyBear::ZERO`
(`EMPTY_SUBTREE_ROOTS[0]`, `heap_root.rs:72-87`). ⚑ It is a literal, NOT a hash output — which is
exactly what makes §5's ghost available. -/
def padDigest : ℤ := 0

/-- **`padTo d L`** — the deployed occupancy discipline: the real leaf digests are a contiguous sorted
PREFIX and every position `≥ L.length` holds `padDigest`
(`CanonicalHeapTree::new:234-238`, "every position `>= n` is the ZERO padding leaf the dense build
`resize`d in"). -/
def padTo (d : Nat) (L : List ℤ) : List ℤ := L ++ List.replicate (2 ^ d - L.length) padDigest

theorem padTo_length {d : Nat} {L : List ℤ} (h : L.length ≤ 2 ^ d) : (padTo d L).length = 2 ^ d := by
  simp only [padTo, List.length_append, List.length_replicate]
  omega

/-- **A FULL tree pads to itself** — the padded fold EXTENDS the dense one; it does not replace it. -/
theorem padTo_dense {d : Nat} {L : List ℤ} (h : L.length = 2 ^ d) : padTo d L = L := by
  simp only [padTo, h, Nat.sub_self, List.replicate_zero, List.append_nil]

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

/-- **`PadHit L`** — the committed leaf-digest vector `L` CONTAINS the padding constant.

⚠ Read what this quantifies over: the POSITIONS OF A GIVEN, FINITE, COMMITTED vector — decidable,
checkable, refutable. It is deliberately NOT `∃ e, leafOf hash e = padDigest`, which quantifies over
the hash's whole domain and which pigeonhole makes unconditionally TRUE at deployed parameters; such a
disjunct would carry no more content than `True`. Same discipline as `SpongeColl`'s "the SPECIFIC pair
the extractor returns". -/
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

/-- The relink preserves length (`relink_next_addrs` rewrites pointers in place). -/
theorem imtChainOf_length (sent : ℤ) :
    ∀ h : Heap.FeltHeap, (imtChainOf sent h).length = h.length := by
  intro h
  induction h with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨n, hn⟩ := Dregg2.Circuit.MapDenotationSchema.imtChainOf_cons sent e rest
    rw [hn, List.length_cons, List.length_cons, ih]

/-- **The relink is a RETRACTION** — dropping the pointers recovers the heap. The other half of the
landed `imtChainOf_imtToHeap` weld, and what makes the relink INJECTIVE. -/
theorem imtToHeap_imtChainOf (sent : ℤ) :
    ∀ h : Heap.FeltHeap, imtToHeap (imtChainOf sent h) = h := by
  intro h
  induction h with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨n, hn⟩ := Dregg2.Circuit.MapDenotationSchema.imtChainOf_cons sent e rest
    obtain ⟨a, v⟩ := e
    rw [hn]
    show (a, v) :: imtToHeap (imtChainOf sent rest) = (a, v) :: rest
    rw [ih]

theorem imtChainOf_injective (sent : ℤ) {h₁ h₂ : Heap.FeltHeap}
    (h : imtChainOf sent h₁ = imtChainOf sent h₂) : h₁ = h₂ := by
  have hc := congrArg imtToHeap h
  rwa [imtToHeap_imtChainOf, imtToHeap_imtChainOf] at hc

/-- The arity-3 leaf-list extractor: walk to the first differing leaf and hand back the two absorbed
arity-3 IMT blocks. TOTAL. -/
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
        exact (Dregg2.Circuit.IndexedMerkleTree.imtLeafHash_binds_or_collides hash
          hleaf).resolve_left hll

/-- **`padImtRoot sent hash d h`** — ⚑ THE DEPLOYED MAP COMMITMENT: relink the pointers
(`relink_next_addrs`, terminal `sent`), digest each linked leaf at arity 3 (`HeapLeaf::digest`), fold
the perfect tree over the ZERO-PADDED vector (`CanonicalHeapTree::new`). -/
def padImtRoot (sent : ℤ) (hash : List ℤ → ℤ) (d : Nat) (h : Heap.FeltHeap) : ℤ :=
  perfectRoot hash d (padTo d ((imtChainOf sent h).map (imtLeafHash hash)))

/-- **`PadGhost3 sent hash h`** — a LIVE arity-3 IMT leaf digest equals the padding constant. -/
def PadGhost3 (sent : ℤ) (hash : List ℤ → ℤ) (h : Heap.FeltHeap) : Prop :=
  PadHit ((imtChainOf sent h).map (imtLeafHash hash))

/-- The hash-level side condition: the padding constant has NO arity-3 IMT leaf preimage. -/
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
node, none at the leaf. This is the theorem the padded instance's teeth are built from. -/
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

/-! ### §4c — the DENSE arity-2 root, cured of its floor as well (used by §7's narrow instance). -/

def mapRootFind (hash : List ℤ → ℤ) (d : Nat) (h₁ h₂ : Heap.FeltHeap) : List ℤ × List ℤ :=
  if SpongeColl hash (perfectRootFind hash d (h₁.map (Heap.leafOf hash))
                                             (h₂.map (Heap.leafOf hash)))
  then perfectRootFind hash d (h₁.map (Heap.leafOf hash)) (h₂.map (Heap.leafOf hash))
  else Heap.mapLeafFind hash h₁ h₂

/-- **The DENSE arity-2 `mapRoot` BINDS the heap, UNCONDITIONALLY** — the cured `mapRoot_injective`.
At a dense heap there is NO padding, hence NO ghost: the only residual is a real collision. -/
theorem mapRoot_binds_or_collides (hash : List ℤ → ℤ) (d : Nat) {h₁ h₂ : Heap.FeltHeap}
    (hl₁ : h₁.length = 2 ^ d) (hl₂ : h₂.length = 2 ^ d)
    (heq : mapRoot hash d h₁ = mapRoot hash d h₂) :
    h₁ = h₂ ∨ SpongeColl hash (mapRootFind hash d h₁ h₂) := by
  by_cases hif : SpongeColl hash (perfectRootFind hash d (h₁.map (Heap.leafOf hash))
                                                         (h₂.map (Heap.leafOf hash)))
  · refine Or.inr ?_
    rw [mapRootFind, if_pos hif]
    exact hif
  · rcases perfectRoot_binds_or_collides hash d (by rw [List.length_map]; exact hl₁)
      (by rw [List.length_map]; exact hl₂) heq with hmap | hc
    · by_cases hne : h₁ = h₂
      · exact Or.inl hne
      · refine Or.inr ?_
        rw [mapRootFind, if_neg hif]
        exact Heap.mapLeafFind_spec hash h₁ h₂ hne hmap
    · exact absurd hc hif

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

/-- **`MapLeafTeeth S`** — the ANTI-GHOST TEETH of a leaf schema, as a bundle an instance must EARN.

`binds` is the floor-free binding. The other three fields are the ANTI-LAUNDERING structure, and they
are what stops this from being option (b) in disguise:

  * `Good` is a HASH-LEVEL predicate, so a residual cannot be defined to hold at every equivocation;
  * `resid_refuted` forces the residual to VANISH at a good hash, which kills `Resid := True` and
    also `Resid := (h₁ ≠ h₂)` (that would force every good hash to identify all heaps);
  * `good_inhabited` forces `Good` to be non-empty, so `resid_refuted` cannot be discharged by an
    empty premise.

Together: the residual is refutable AND the refutation is reachable. That is the §5b.S "strength
relation, both directions" discipline, generalised to a schema. -/
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

section Teeth
variable {S : MapLeafSchema}

/-- **★ TOOTH 1/3 — OPENINGS ARE FUNCTIONAL (schema level).** Root + key determine the read, up to
the schema's named residual. Stated over EXPLICIT witness heaps, per §5b.E's discipline: the residual
is a function of the WITNESSES, so hiding them behind the existential and writing `… ∨ ∃ residual`
would be the free pass this whole idiom exists to avoid. -/
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

/-- **★ TOOTH 2/3 — MEMBERSHIP EXCLUDES NON-MEMBERSHIP (schema level).** The tooth that stops a
prover claiming ABSENCE of a key the committed tree PRESENTS. -/
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

/-- **★ TOOTH 3/3 — WRITES ARE FUNCTIONAL (schema level).** Root + key + value determine the new
root: the map-op row's `new_root` column cannot be forged, up to the named residual. -/
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

/-! ### §6.S — the EXISTENTIAL-level teeth at a GOOD hash: the three theorems the design doc names,
recovered VERBATIM in shape over `opensToMerkleS` / `writesToMerkleS`, for ANY schema carrying teeth.
These are the statements the padded instance had nothing to inherit; they now exist once. -/

/-- **`opensToMerkle_functional` at the schema level.** -/
theorem opensToMerkleS_functional_of_good (T : MapLeafTeeth S) {hash : List ℤ → ℤ}
    (hgood : T.Good hash) (d : Nat) {r k : ℤ} {o₁ o₂ : Option ℤ}
    (h₁ : opensToMerkleS S hash d r k o₁) (h₂ : opensToMerkleS S hash d r k o₂) : o₁ = o₂ := by
  obtain ⟨m₁, hk₁, hz₁, hr₁, hg₁⟩ := h₁
  obtain ⟨m₂, hk₂, hz₂, hr₂, hg₂⟩ := h₂
  rcases opensToMerkleS_functional_or_resid T hash d hk₁ hz₁ hr₁ hg₁ hk₂ hz₂ hr₂ hg₂ with ho | hc
  · exact ho
  · exact absurd hc (T.resid_refuted hash hgood d m₁ m₂)

/-- **`opensToMerkle_some_excludes_none` at the schema level.** -/
theorem opensToMerkleS_some_excludes_none_of_good (T : MapLeafTeeth S) {hash : List ℤ → ℤ}
    (hgood : T.Good hash) (d : Nat) {r k v : ℤ}
    (h₁ : opensToMerkleS S hash d r k (some v)) (h₂ : opensToMerkleS S hash d r k none) : False := by
  have := opensToMerkleS_functional_of_good T hgood d h₁ h₂
  simp at this

/-- **`writesToMerkle_functional` at the schema level.** -/
theorem writesToMerkleS_functional_of_good (T : MapLeafTeeth S) {hash : List ℤ → ℤ}
    (hgood : T.Good hash) (d : Nat) {r k v r₁ r₂ : ℤ}
    (h₁ : writesToMerkleS S hash d r k v r₁) (h₂ : writesToMerkleS S hash d r k v r₂) : r₁ = r₂ := by
  obtain ⟨m₁, hk₁, hz₁, _, hr₁, he₁⟩ := h₁
  obtain ⟨m₂, hk₂, hz₂, _, hr₂, he₂⟩ := h₂
  rcases writesToMerkleS_functional_or_resid T hash d hk₁ hz₁ hr₁ he₁ hk₂ hz₂ hr₂ he₂ with hr | hc
  · exact hr
  · exact absurd hc (T.resid_refuted hash hgood d m₁ m₂)

end Teeth

/-! ## §7 — THE INSTANCES. Three, all INHABITED — the schema-level teeth are not an ∃-image. -/

/-- An injective hash with NO preimage of the padding constant: `refSponge` made odd. Witness that
`PadFree2` / `PadFree3` are satisfiable, so the padded instances' `good_inhabited` is real. -/
def oddSponge (xs : List ℤ) : ℤ := 2 * refSponge xs + 1

theorem oddSponge_injective : Function.Injective oddSponge := by
  intro xs ys h
  simp only [oddSponge] at h
  exact refSponge_CR _ _ (by omega)

theorem oddSponge_ne_pad (xs : List ℤ) : oddSponge xs ≠ padDigest := by
  simp only [oddSponge, padDigest]
  omega

theorem oddSponge_padFree2 : PadFree2 oddSponge := fun _ => oddSponge_ne_pad _
theorem oddSponge_padFree3 : PadFree3 oddSponge := fun _ => oddSponge_ne_pad _

/-- **TEETH FOR THE DENSE arity-2 schema (the RETIRED shape).** No padding, hence NO ghost: the residual
is a genuine sponge collision and nothing else. This is the CONSERVATIVITY anchor of §8 — and that is
all it is. ⚠ This doc-comment said "(deployed-today)", inheriting the false claim in
`MapDenotationSchema.narrowSchema`'s own header: the deployed instance is `padImtSchema` below
(arity-3 IMT leaves, deployed relink, sparse padded occupancy), with `padImtTeeth`. -/
def narrowTeeth : MapLeafTeeth narrowSchema where
  Resid := fun hash d h₁ h₂ => SpongeColl hash (mapRootFind hash d h₁ h₂)
  binds := fun hash d _ _ _ _ hz₁ hz₂ he => mapRoot_binds_or_collides hash d hz₁ hz₂ he
  Good := Function.Injective
  resid_refuted := fun hash hg _ _ _ => spongeColl_refutable_of_injective hash hg _
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

/-- **⚑ `padImtSchema sent` — THE DEPLOYED INSTANCE.** Arity-3 IMT leaves over the deployed relink
AND the deployed sparse occupancy. `HeapOk` is the landed `imtSchema`'s (sorted, every key below the
terminal sentinel); only `SizeOk` and `commit` move. -/
def padImtSchema (sent : ℤ) : MapLeafSchema where
  HeapOk := fun h => Heap.SortedKeys h ∧ ∀ x ∈ Heap.keys h, x < sent
  heapOk_sorted := fun _ h => h.1
  SizeOk := fun d h => h.length ≤ 2 ^ d
  commit := padImtRoot sent

/-- **★★ TEETH FOR THE DEPLOYED PADDED INSTANCE.** This is stage 2b's deliverable: the padded,
arity-3, deployed-shape instance now ARRIVES WITH the three anti-ghost theorems instead of assuming
them. -/
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
  show perfectRoot hash d (padTo d ((imtChainOf sent h).map (imtLeafHash hash)))
    = perfectRoot hash d ((imtChainOf sent h).map (imtLeafHash hash))
  rw [padTo_dense (by rw [List.length_map, imtChainOf_length]; exact hlen)]

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

#assert_axioms mapNode_binds_or_collides
#assert_axioms foldLevel_binds_or_collides
#assert_axioms perfectRoot_binds_or_collides
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
#assert_axioms mapRoot_binds_or_collides
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

end Dregg2.Circuit.MapPaddedDenotation
