/-
# `Dregg2.Circuit.MapKindImtGates` — STAGE 2 PROPER: the four arity-3 opener laws
  (`.read` / `.write` / `.insert` / `.aafiInsert`) at the DEPLOYED padded shape.

`docs/DESIGN-mapop-denotation-move.md` §11.6-3 named the gap in one line: *"stage 2 proper is
untouched — `.read`/`.write`/`.insert`/`.aafiInsert` still have no arity-3 opener law, so the
modeller still cannot DERIVE `holdsAtS` for them."* `MapAbsentImtGate` did the `.absent` arm and
found, on contact, that the deployed table is a DIFFERENT constraint system from the Lean model.
This file grounds the other four against `circuit/src/descriptor_ir2.rs` (`Ir2Air::MapOps`) rather
than porting the existing Lean shape — and the same species of divergence is present in three of
the four.

## THE DEPLOYED SHAPE, read this session, per kind (`Ir2Air::MapOps`, `descriptor_ir2.rs:3232-3541`)

Common: `map_leaf_input_cols(v) = [MAP_KEY, v, MAP_NEXT]` (`:2198`) — **arity 3 for EVERY kind**,
and `MAP_NEXT` is ONE column SHARED by the old- and new-leaf absorb.

| kind | op | deployed gates | divergence from `MapOpsColumnLayout.ReconcileGatesAt` |
|---|---|---|---|
| `.read` | 0 | old-leaf `hash[key, old_value, next]` folds PATH1 → `MAP_ROOT`; new-leaf `hash[key, value, next]` folds the **same** PATH1 → `MAP_NEW_ROOT`; `MAP_OLD_VALUE = MAP_VALUE` forced (`:3283`) | leaf arity, and **`new_root = root` is DERIVED, not a gate** — the model ASSERTS a column equality the AIR never writes |
| `.write` | 1 | identical minus the `old_value = value` constraint; the **shared `MAP_NEXT`** is what forbids a relink | leaf arity + the shared pointer |
| `.insert` | 3 | `rw_sel = 0` and `not_insert3 = 0`, so there is **NO old-leaf absorb and NO PATH1 fold to the pre-root at all** (`:3277-3278`, `:3384`); the ONLY gate is new-leaf → `MAP_NEW_ROOT` | ⚑⚑ the model demands an old-leaf path to the PRE-root **that the AIR does not carry**, at a key the deployed builder REQUIRES to be absent (`insert_witness`, `heap_root.rs:1007-1042`) |
| `.aafiInsert` | 4 | low-leaf `hash[low_addr, low_value, MAP_NEXT]` → PATH1 → root; bracket `low < k < next`; low-update `hash[low_addr, low_value, MAP_KEY]` → PATH1 → `R1`; free slot **PINNED to `ZERO8`** (`:3493-3495`) → PATH2 → `R1`; append `hash[key, value, MAP_NEXT]` → PATH2 → `new_root` | the Lean `AafiGatesAt` leaves `freeEmpty` a FREE variable; the AIR pins it to the **padding constant**, i.e. the deployed AAFI grows into the padding |

## THE FOUR LAWS, and what each one costs

* §5 `.read` — `readImtRow_opens_of_good` : an accepting row FORCES
  `opensToMerkleS (padImtSchema sent) hash dep root key (some value)` **and** `newRoot = root`.
* §5 `.write` — `writeImtRow_writes_of_good` : an accepting row FORCES
  `writesToMerkleS (padImtSchema sent) hash dep root key value newRoot`. The proof runs through
  `imtChainOf_set`, which is exactly where the deployed **shared `MAP_NEXT` column** does its work:
  a relinking write would leave the post-vector outside the image of `imtChainOf` and the law would
  fail. §5c states that as a theorem (`unshared_pointer_write_is_not_a_relink`).
* §6 `.insert` — TWO results, and the second is the honest one:
  `insertImtRow_post_opens_of_good` (the post-root DOES open the key to the written value) and
  ⚑ `insertImtGates_cannot_force_the_write_denotation` — **REFUTED**, because op=3 leaves the
  pre-root unconstrained. Plus `reconcileGates_insert_forces_key_present` /
  `reconcileGates_insert_unsat_at_fresh_key`: the EXISTING arity-2 `.insert` model is unsatisfiable
  at exactly the rows the deployed prover emits — the `.absent` finding, verbatim, on a second arm.
  (And the epoch's own `.insert` non-vacuity exhibit, `MapOpsColumnLayout.toy_insert_gates`, writes
  key `20` which `toyHeap` already HOLDS: it is a value update wearing an insert's name.)
* §7 `.aafiInsert` — `aafiImtRow_forces_absence_of_good` : an accepting row FORCES
  `opensToMerkleS (padImtSchema sent) hash dep root key none` (the double-spend tooth, at the
  deployed padded commitment), and §9d exhibits a row whose post-root IS the padded sorted commit,
  so growth there is a genuine map GROWTH at the deployed depth.

## ⚑⚑ THE EIGHTH IMPOSSIBILITY — no `MapLeafSchema` can be the deployed AAFI POST-commitment

Seven "obvious approaches" on this epoch were proved impossible. Here is the eighth, and it is
structural rather than cryptographic. `heap_root.rs::insert_witness_aafi` (`:1077-1156`) appends at
`next_free_index` and folds `append_order_after` — *"a distinct commitment lineage from the
sorted-compacted `root8` (same leaf SET, different positions)"* (`:1139-1141`). But
`MapLeafSchema.commit : (List ℤ → ℤ) → Nat → Heap.FeltHeap → ℤ` is a **FUNCTION of the logical
sorted map**, and the append-order fold depends on insertion HISTORY. §7b proves
`no_schema_commits_the_append_order_layout`: for EVERY schema `S`, at every depth ≥ 1, at a hash
that is injective AND pad-free, the claim *"the padded fold of the physical layout equals
`S.commit` of the logical chain"* is FALSE. So the `.aafiInsert` arm of `MapOp.holdsAtS S` —
which is `writesToMerkleS S`, a statement about the logical map — **cannot** be the deployed AAFI
post-condition at ANY instance of the landed schema. `aafi_post_is_not_the_sorted_commit` exhibits
the separation concretely at the deployed leaf. The positive half (`.aafiInsert`'s PRE-side
absence, §7) is unaffected, because the pre-root IS the sorted commitment — `heap_root.rs`'s
`root8`, which `CanonicalHeapTree::new` builds in SORTED position order.

⚠ THIS CORRECTS A FRAMING. Stage 2b called `padImtTeeth` "the deployed shape": it is faithful to
`CanonicalHeapTree::new`'s sorted-prefix build — which is what every PRE-root is — and NOT to the
AAFI POST-layout, which `insert_witness_aafi` folds in append order.

## THE INSERT/WRITE GROWTH QUESTION, ANSWERED (§8)


The sibling's finding is confirmed and then MOVED. At a DENSE schema `SizeOk d h` is
`h.length = 2 ^ d`, and `imtSchema_write_forces_key_present` proves that forces the written key
ALREADY committed — so `.write`/`.insert` denote an in-place UPDATE and nothing else. At the
PADDED schema `SizeOk` is `≤`, and `padImt_write_admits_growth` exhibits a `writesToMerkleS`
witness **at `MAP_TREE_DEPTH = 16` whose key is FRESH and whose heap GROWS by one**. So stage 2b
did change what these laws can say: fresh-key growth is representable at the padded instance, it
was not at the dense one, and the deployed AAFI op is the operation that realises it (§9d).

## FLOORS — none new, and the refuted one is not leaned on

`Poseidon2SpongeCR` appears in NO type in this file. Every extraction law comes in two forms:

* `…_or_resid` — **no hypothesis on `hash` at all**, with three NAMED, per-row, refutable residuals
  (`OpenResid`): a path collision at the pair `pathCollFind` returns, an arity-3 leaf collision at
  the pair the total `chainAt` extractor names, and `imtLeafHash hash l = padDigest` (the opened
  leaf digest IS the padding constant — stage 2b's ghost, at the row);
* `…_of_good` — the strength bridge at `MapGood hash := Function.Injective hash ∧ PadFree3 hash`,
  which is **`MapPaddedDenotation.padImtTeeth`'s own `Good` field, verbatim** (`mapGood_is_teeth_good`
  is `Iff.rfl`), so this file introduces no new hash property and inherits `good_inhabited`
  (`oddSponge`). ⚠ LABELLED: the bridge is at an injective idealisation; `Poseidon2SpongeCR` is
  PROVED FALSE at deployed BabyBear parameters, so only the `_or_resid` halves are unconditional.

`ImtSorted` / the committed heap behind a root stays a HYPOTHESIS, in the same knowledge-extraction
slot `ReconcileGatesAt`'s `∃ h` occupies. Not promoted, not renamed a floor.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; sorry-free; no `native_decide`; no
`decide` on any object containing the depth-16 spine (every depth-16 exhibit NAMES its root and
builds its path by the symbolic `leftPadPath`/`slot1Path` recursion — nothing is enumerated).
NEW file; every import read-only; no deployed byte touched.
-/
import Dregg2.Circuit.MapPaddedDenotation

namespace Dregg2.Circuit.MapKindImtGates

open Dregg2.Substrate
open Dregg2.Circuit.Poseidon2Binding (SpongeColl spongeColl_refutable_of_injective)
open Dregg2.Circuit.Poseidon2Binding.Reference (refSponge refSponge_CR)
open Dregg2.Crypto.SpongeCarrierReduction (IsSpongeColl)
open Dregg2.Circuit.MapMerkleRoot (mapNode foldLevel perfectRoot mapRoot opensToMerkle writesToMerkle)
open Dregg2.Circuit.MapDenotationSchema (MapLeafSchema narrowSchema imtSchema imtChainOf
  imtChainOf_cons opensToMerkleS writesToMerkleS)
open Dregg2.Circuit.MapPaddedDenotation (padDigest padTo padTo_length padTo_dense emptySubtreeRoot
  perfectRoot_all_padding perfectRoot_binds_or_collides PadHit append_replicate_eq_or_hit
  padImtRoot PadGhost3 PadFree3 padGhost3_refuted padImtRoot_binds_or_ghost_or_collides
  padImtSchema padImtTeeth MapLeafTeeth imtChainOf_length imtToHeap_imtChainOf
  oddSponge oddSponge_injective oddSponge_padFree3 oddSponge_ne_pad
  opensToMerkleS_functional_of_good opensToMerkleS_some_excludes_none_of_good
  writesToMerkleS_functional_of_good)
open Dregg2.Circuit.IndexedMerkleTree (ImtLeaf ImtSorted ImtAbsent imtAddrs imtLeafHash imtLeafPre
  imtLeafHash_binds_or_collides imtToHeap imtAbsent_excludes keys_imtToHeap)
open Dregg2.Circuit.MapOpsColumnLayout (pathPos pathRecompute pathCollFind
  pathRecompute_binds_updates set_append_left' map_set' perfectRoot_append
  get_eq_some_of_getElem? heapSet_eq_listSet ReconcileGatesAt leafPre leafOf_injective heapAt
  heapAt_of_getElem?)
open Dregg2.Circuit.DescriptorIR2 (MapOp MapOpKind MAP_TREE_DEPTH)
open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.MapPaddedDenotation (mapRootFind mapRoot_binds_or_collides)
open Dregg2.Circuit.MapDenotationSchema (imtSchema_chain_imtSorted)
open Dregg2.Circuit.MapOpsColumnLayout (noPathColl_of_CR noLeafColl_of_CR)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — THE PADDED ARITY-3 COMMITTED VECTOR, and the positional face of the deployed relink. -/

/-- **`padVec sent hash dep h`** — the digest vector the deployed prover actually folds: relink
(`relink_next_addrs`), digest at arity 3 (`HeapLeaf::digest`), zero-pad to `2 ^ dep`
(`CanonicalHeapTree::new`). `padImtRoot` is its `perfectRoot`, by definition. -/
def padVec (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat) (h : Heap.FeltHeap) : List ℤ :=
  padTo dep ((imtChainOf sent h).map (imtLeafHash hash))

theorem padImtRoot_eq_padVec (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat) (h : Heap.FeltHeap) :
    padImtRoot sent hash dep h = perfectRoot hash dep (padVec sent hash dep h) := rfl

/-- The deployed commitment, spelled out at GENERIC depth. ⚠ Stated depth-generically on purpose:
per `MapDenotationSchema`'s measured discipline, an equation of this shape with `MAP_TREE_DEPTH`
substituted and closed by a FRESH `rfl` dives into `perfectRoot _ 16 _` and dies at the heartbeat
limit. Every deployed-depth exhibit below TRANSPORTS this instead of re-deriving it. -/
theorem padImtRoot_unfold (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat) (h : Heap.FeltHeap) :
    padImtRoot sent hash dep h
      = perfectRoot hash dep (padTo dep ((imtChainOf sent h).map (imtLeafHash hash))) := rfl

theorem padVec_length {sent : ℤ} {hash : List ℤ → ℤ} {dep : Nat} {h : Heap.FeltHeap}
    (hl : h.length ≤ 2 ^ dep) : (padVec sent hash dep h).length = 2 ^ dep :=
  padTo_length (by rw [List.length_map, imtChainOf_length]; exact hl)

/-- **The relink, POSITIONALLY.** Leaf `i` of the deployed chain carries `h`'s entry at `i` and the
pointer to `h`'s SUCCESSOR address (the terminal one to `sent`). This is `relink_next_addrs` read as
a function of the index rather than a recursion, and it is what makes the write law's chain algebra
tractable. -/
theorem imtChainOf_getElem? (sent : ℤ) :
    ∀ (h : Heap.FeltHeap) (i : Nat),
      (imtChainOf sent h)[i]? =
        (h[i]?).map (fun e => (⟨e.1, e.2, (h[i + 1]?).elim sent Prod.fst⟩ : ImtLeaf)) := by
  intro h
  induction h with
  | nil => intro i; simp [imtChainOf]
  | cons e rest ih =>
    intro i
    cases i with
    | zero =>
      cases rest with
      | nil => rfl
      | cons e' rest' => rfl
    | succ j =>
      obtain ⟨n, hn⟩ := imtChainOf_cons sent e rest
      rw [hn]
      show (imtChainOf sent rest)[j]?
        = (rest[j]?).map (fun x => (⟨x.1, x.2, (rest[j + 1]?).elim sent Prod.fst⟩ : ImtLeaf))
      exact ih j

/-- The chain has the same length as the heap it relinks, positionally. -/
theorem imtChainOf_getElem?_isSome (sent : ℤ) (h : Heap.FeltHeap) (i : Nat) :
    ((imtChainOf sent h)[i]?).isSome = (h[i]?).isSome := by
  rw [imtChainOf_getElem? sent h i]
  cases h[i]? <;> rfl

/-- **A positional VALUE update leaves every pointer alone** — because `List.set` at `p` writes the
SAME address `k` the position already held, so no successor address moves. This is the exact fact
the deployed SHARED `MAP_NEXT` column encodes: old and new leaf differ only in the value felt. -/
theorem imtChainOf_set (sent : ℤ) :
    ∀ (h : Heap.FeltHeap) (p : Nat) (k vOld v : ℤ), h[p]? = some (k, vOld) →
      imtChainOf sent (h.set p (k, v))
        = (imtChainOf sent h).set p (⟨k, v, (h[p + 1]?).elim sent Prod.fst⟩ : ImtLeaf) := by
  intro h p k vOld v hp
  have hplt : p < h.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hp
    simp at hp
  have hclen : p < (imtChainOf sent h).length := by rw [imtChainOf_length]; exact hplt
  -- The successor address is unchanged at EVERY index, because `set` preserves the address at `p`.
  have hnext : ∀ i : Nat,
      ((h.set p (k, v))[i + 1]?).elim sent Prod.fst = (h[i + 1]?).elim sent Prod.fst := by
    intro i
    by_cases hip : i + 1 = p
    · subst hip
      rw [List.getElem?_set_self hplt, hp]
      rfl
    · rw [List.getElem?_set_ne (fun hc => hip hc.symm)]
  refine List.ext_getElem? ?_
  intro i
  rw [imtChainOf_getElem? sent (h.set p (k, v)) i]
  simp only [hnext]
  by_cases hip : i = p
  · subst hip
    rw [List.getElem?_set_self hplt, List.getElem?_set_self hclen]
    rfl
  · rw [List.getElem?_set_ne (fun hc => hip hc.symm), List.getElem?_set_ne (fun hc => hip hc.symm),
      imtChainOf_getElem? sent h i]

/-! ## §2 — PADDING ALGEBRA: what the sparse occupancy does to positions and to one more level. -/

theorem padTo_set (d : Nat) (L : List ℤ) (p : Nat) (x : ℤ) (hp : p < L.length) :
    padTo d (L.set p x) = (padTo d L).set p x := by
  simp only [padTo, List.length_set]
  rw [set_append_left' L _ p x hp]

/-- Reading a cell of the padded vector: either it is a LIVE cell of the prefix, or the value read
is the padding constant itself. The one-line decode every arity-3 opener needs. -/
theorem padTo_getElem? (d : Nat) (L : List ℤ) (p : Nat) (y : ℤ)
    (hp : (padTo d L)[p]? = some y) : (p < L.length ∧ L[p]? = some y) ∨ y = padDigest := by
  by_cases hlt : p < L.length
  · exact Or.inl ⟨hlt, by rwa [padTo, List.getElem?_append_left hlt] at hp⟩
  · refine Or.inr ?_
    rw [padTo, List.getElem?_append_right (by omega)] at hp
    exact List.eq_of_mem_replicate (List.mem_of_getElem? hp)

/-- One padded level splits into the padded level below plus an ALL-PADDING right half — the
structural fact the depth-16 symbolic paths descend through. -/
theorem padTo_succ_split (k : Nat) (L : List ℤ) (h : L.length ≤ 2 ^ k) :
    padTo (k + 1) L = padTo k L ++ List.replicate (2 ^ k) padDigest := by
  have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ]; ring
  simp only [padTo, List.append_assoc, ← List.replicate_add]
  congr 2
  omega

/-- Appending ONE padding cell to the live prefix changes nothing — the deployed AAFI free slot is
inside the padding, so "the slot was empty" and "the slot is past the prefix" are the same vector. -/
theorem padTo_snoc_pad (d : Nat) (L : List ℤ) (h : L.length + 1 ≤ 2 ^ d) :
    padTo d (L ++ [padDigest]) = padTo d L := by
  have hlen : (L ++ [padDigest]).length = L.length + 1 := by simp
  simp only [padTo, hlen, List.append_assoc]
  congr 1
  rw [show ([padDigest] : List ℤ) = List.replicate 1 padDigest from rfl, ← List.replicate_add]
  congr 1
  omega

/-! ## §3 — THE SYMBOLIC DEPTH-`d` PATHS over a SPARSE tree.

`MapReconcileImtRepoint`'s `spineC` kit builds a `2^16` DENSE spine at symbolic depth. The deployed
tree is SPARSE, so the exhibits below need the other kit: the membership paths of positions `0` and
`1` in a tree whose live prefix is one or two leaves and whose every other cell is `heap_root.rs`'s
`EMPTY_SUBTREE_ROOTS`. Both are cons-recursions on the depth; no `2^16` object is ever built. -/

/-- The root-first membership path of position `0` in a zero-padded depth-`k` tree: at every level
the sibling is the all-padding subtree root of the level below (`EMPTY_SUBTREE_ROOTS[lvl]`). -/
def leftPadPath (hash : List ℤ → ℤ) : Nat → List (Bool × ℤ)
  | 0 => []
  | k + 1 => (false, emptySubtreeRoot hash k) :: leftPadPath hash k

theorem leftPadPath_length (hash : List ℤ → ℤ) : ∀ k, (leftPadPath hash k).length = k := by
  intro k; induction k with
  | zero => rfl
  | succ k ih => simp [leftPadPath, ih]

theorem leftPadPath_pos (hash : List ℤ → ℤ) : ∀ k, pathPos (leftPadPath hash k) = 0 := by
  intro k; induction k with
  | zero => rfl
  | succ k ih => simpa [leftPadPath, pathPos] using ih

/-- **★ THE SPARSE LEFTMOST OPENING, at symbolic depth.** One live leaf at position `0`, every other
cell the padding constant: the path recomputes to the padded root. -/
theorem leftPadPath_recompute (hash : List ℤ → ℤ) :
    ∀ (k : Nat) (x : ℤ), pathRecompute hash x (leftPadPath hash k) = perfectRoot hash k (padTo k [x]) := by
  intro k
  induction k with
  | zero => intro x; rfl
  | succ k ih =>
    intro x
    have hle : ([x] : List ℤ).length ≤ 2 ^ k := by
      simpa using Nat.one_le_pow k 2 (by norm_num)
    show mapNode hash (pathRecompute hash x (leftPadPath hash k)) (emptySubtreeRoot hash k) = _
    rw [ih x, padTo_succ_split k [x] hle,
      perfectRoot_append hash k _ _ (padTo_length hle) (by simp),
      perfectRoot_all_padding hash k]

/-- The root-first membership path of position `1` in a zero-padded depth-`k` tree whose position
`0` holds the digest `x0`. -/
def slot1Path (hash : List ℤ → ℤ) (x0 : ℤ) : Nat → List (Bool × ℤ)
  | 0 => []
  | 1 => [(true, x0)]
  | k + 2 => (false, emptySubtreeRoot hash (k + 1)) :: slot1Path hash x0 (k + 1)

theorem slot1Path_length (hash : List ℤ → ℤ) (x0 : ℤ) :
    ∀ k, (slot1Path hash x0 k).length = k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    cases k with
    | zero => rfl
    | succ m => simpa [slot1Path] using ih

theorem slot1Path_pos (hash : List ℤ → ℤ) (x0 : ℤ) :
    ∀ k, 0 < k → pathPos (slot1Path hash x0 k) = 1 := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro _
    cases k with
    | zero => rfl
    | succ m => simpa [slot1Path, pathPos] using ih (by omega)

/-- **★ THE SPARSE SLOT-1 OPENING, at symbolic depth.** Two live cells at positions `0`/`1`, every
other cell the padding constant. This is the path the deployed AAFI append (`free_index =
next_free_index`, `heap_root.rs:1124`) uses when the tree holds one live leaf. -/
theorem slot1Path_recompute (hash : List ℤ → ℤ) (x0 : ℤ) :
    ∀ (k : Nat), 0 < k → ∀ x1 : ℤ,
      pathRecompute hash x1 (slot1Path hash x0 k) = perfectRoot hash k (padTo k [x0, x1]) := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro _ x1
    cases k with
    | zero =>
      show mapNode hash x0 (pathRecompute hash x1 []) = _
      have : padTo 1 [x0, x1] = [x0, x1] := padTo_dense (by simp)
      rw [this]
      rfl
    | succ m =>
      have hle : ([x0, x1] : List ℤ).length ≤ 2 ^ (m + 1) := by
        have : 2 ≤ 2 ^ (m + 1) := by
          calc (2 : Nat) = 2 ^ 1 := rfl
            _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        simpa using this
      show mapNode hash (pathRecompute hash x1 (slot1Path hash x0 (m + 1)))
          (emptySubtreeRoot hash (m + 1)) = _
      rw [ih (by omega) x1, padTo_succ_split (m + 1) [x0, x1] hle,
        perfectRoot_append hash (m + 1) _ _ (padTo_length hle) (by simp),
        perfectRoot_all_padding hash (m + 1)]

/-! ## §4 — THE ARITY-3 PADDED OPENING EXTRACTION, and its THREE NAMED RESIDUALS.

Every one of the four laws below runs through this one theorem. It takes **no hypothesis on `hash`**
— the binding half is unconditional at the deployed sponge — and everything the refuted floor used
to buy is instead NAMED, per-row, and refutable:

  * a genuine collision at the pair `pathCollFind` returns for THIS path and THIS committed vector
    (the `3245e88148` idiom, reused verbatim);
  * a genuine collision at the arity-3 leaf pair the TOTAL extractor `chainAt` names;
  * `imtLeafHash hash l = padDigest` — the opened digest IS `heap_root.rs`'s padding constant, i.e.
    the row opened a padding cell. This is stage 2b's ghost, localized to one row: a FIXED-TARGET
    PREIMAGE of a literal, which `Poseidon2SpongeCR` does not exclude and `PadFree3` does. -/

/-- The TOTAL extractor naming the chain leaf a path position points at (`⟨0,0,0⟩` off the end; the
spec's live branch never reads that value). Totality is what lets the leaf residual be stated at a
NAMED pair instead of a proof-local binder. -/
def chainAt (sent : ℤ) (h : Heap.FeltHeap) (p : Nat) : ImtLeaf :=
  ((imtChainOf sent h)[p]?).getD ⟨0, 0, 0⟩

/-- **`OpenResid`** — the NAMED residual of one arity-3 padded opening. All three disjuncts are
properties of data the row and the commitment actually hold; none quantifies over the hash's
domain. -/
def OpenResid (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat) (h : Heap.FeltHeap)
    (steps : List (Bool × ℤ)) (l : ImtLeaf) : Prop :=
  IsSpongeColl hash (pathCollFind hash steps (padVec sent hash dep h) (imtLeafHash hash l))
  ∨ IsSpongeColl hash (imtLeafPre (chainAt sent h (pathPos steps)), imtLeafPre l)
  ∨ imtLeafHash hash l = padDigest

/-- **`MapGood hash`** — the hash-level idealisation at which every residual below vanishes. ⚠ It is
`MapPaddedDenotation.padImtTeeth`'s own `Good` FIELD, so this file introduces NO new hash property
and inherits stage 2b's `good_inhabited`. -/
def MapGood (hash : List ℤ → ℤ) : Prop := Function.Injective hash ∧ PadFree3 hash

/-- The strength bridge is stage 2b's, definitionally — not a fresh assumption wearing a new name. -/
theorem mapGood_is_teeth_good (sent : ℤ) (hash : List ℤ → ℤ) :
    MapGood hash ↔ (padImtTeeth sent).Good hash := Iff.rfl

/-- ANTI-LAUNDERING: good hashes EXIST, so `openResid_refuted` is not discharged by an empty
premise. `oddSponge` is injective and never hits the padding constant. -/
theorem mapGood_inhabited : MapGood oddSponge := ⟨oddSponge_injective, oddSponge_padFree3⟩

/-- ANTI-LAUNDERING: at a good hash the residual is REFUTED, so `Resid := True` is unbuildable and
the disjunctions below are informative. -/
theorem openResid_refuted {hash : List ℤ → ℤ} (hgood : MapGood hash) (sent : ℤ) (dep : Nat)
    (h : Heap.FeltHeap) (steps : List (Bool × ℤ)) (l : ImtLeaf) :
    ¬ OpenResid sent hash dep h steps l := by
  rintro (⟨hne, he⟩ | ⟨hne, he⟩ | hpad)
  · exact hne (hgood.1 he)
  · exact hne (hgood.1 he)
  · exact hgood.2 l hpad

/-- **★★ THE ARITY-3 PADDED OPENING BINDS — UNCONDITIONALLY, up to the three named residuals.**
A path recomputing an arity-3 IMT leaf digest to the DEPLOYED padded root of a sparse committed heap
(i) BINDS the leaf into the relinked chain at the path's position, (ii) decodes it to the heap entry
there, (iii) pins its pointer to the successor address the relink assigns, and (iv) FORCES THE UPDATE
— the same siblings recompute any replacement leaf to the genuinely updated padded root. No floor. -/
theorem padOpen_binds_or_resid (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat)
    {h : Heap.FeltHeap} {steps : List (Bool × ℤ)} {l : ImtLeaf}
    (hlen : h.length ≤ 2 ^ dep) (hsl : steps.length = dep)
    (hpath : pathRecompute hash (imtLeafHash hash l) steps = padImtRoot sent hash dep h) :
    (pathPos steps < h.length
      ∧ (imtChainOf sent h)[pathPos steps]? = some l
      ∧ h[pathPos steps]? = some (l.addr, l.value)
      ∧ l.nextAddr = (h[pathPos steps + 1]?).elim sent Prod.fst
      ∧ ∀ l' : ImtLeaf, pathRecompute hash (imtLeafHash hash l') steps
          = perfectRoot hash dep ((padVec sent hash dep h).set (pathPos steps)
              (imtLeafHash hash l')))
    ∨ OpenResid sent hash dep h steps l := by
  by_cases hc1 : IsSpongeColl hash
      (pathCollFind hash steps (padVec sent hash dep h) (imtLeafHash hash l))
  · exact Or.inr (Or.inl hc1)
  · have hvl : (padVec sent hash dep h).length = 2 ^ steps.length := by
      rw [hsl]; exact padVec_length hlen
    have hroot : pathRecompute hash (imtLeafHash hash l) steps
        = perfectRoot hash steps.length (padVec sent hash dep h) := by rw [hsl]; exact hpath
    obtain ⟨hmem, hupd⟩ := pathRecompute_binds_updates hash steps (padVec sent hash dep h)
      (imtLeafHash hash l) hvl hroot hc1
    rcases padTo_getElem? dep ((imtChainOf sent h).map (imtLeafHash hash)) (pathPos steps)
      (imtLeafHash hash l) hmem with ⟨hlt, hcell⟩ | hpad
    · rw [List.length_map, imtChainOf_length] at hlt
      rw [List.getElem?_map] at hcell
      cases he : (imtChainOf sent h)[pathPos steps]? with
      | none => rw [he] at hcell; simp at hcell
      | some l₀ =>
        rw [he] at hcell
        simp only [Option.map_some, Option.some.injEq] at hcell
        have hca : chainAt sent h (pathPos steps) = l₀ := by rw [chainAt, he]; rfl
        rcases imtLeafHash_binds_or_collides hash hcell with heq | hcol
        · subst heq
          have hdec : ∃ e : ℤ × ℤ, h[pathPos steps]? = some e
              ∧ l₀ = (⟨e.1, e.2, (h[pathPos steps + 1]?).elim sent Prod.fst⟩ : ImtLeaf) := by
            have he' := he
            rw [imtChainOf_getElem? sent h (pathPos steps)] at he'
            cases hh : h[pathPos steps]? with
            | none => rw [hh] at he'; simp at he'
            | some e =>
              rw [hh] at he'
              simp only [Option.map_some, Option.some.injEq] at he'
              exact ⟨e, rfl, he'.symm⟩
          obtain ⟨e, hh, hl₀⟩ := hdec
          refine Or.inl ⟨hlt, rfl, ?_, ?_, ?_⟩
          · rw [hh, hl₀]
          · rw [hl₀]
          · intro l'
            have := hupd (imtLeafHash hash l')
            rwa [hsl] at this
        · exact Or.inr (Or.inr (Or.inl (by rw [hca]; exact hcol)))
    · exact Or.inr (Or.inr (Or.inr hpad))

/-! ## §5 — THE `.read` AND `.write` ARMS (op = 0 and op = 1).

`Ir2Air::MapOps` treats these two with the SAME columns and the SAME lookups: one sibling path
(`MAP_SIB0`/`MAP_DIR0`), an old-leaf absorb `hash[MAP_KEY, MAP_OLD_VALUE, MAP_NEXT]` folding to
`MAP_ROOT` and a new-leaf absorb `hash[MAP_KEY, MAP_VALUE, MAP_NEXT]` folding the SAME path to
`MAP_NEW_ROOT`. The ONLY difference is `descriptor_ir2.rs:3283`, which forces
`MAP_OLD_VALUE = MAP_VALUE` on read rows. So the model below is ONE predicate and `.read` is its
`oldValue := value` instance — which is exactly how the deployment is written. -/

/-- **`RwImtGatesOn`** — the deployed read/write gate acceptance for ONE row, modelled 1:1 and
depth-generic. ⚑ Note what is NOT here and is not in the AIR either: no `new_root = root` column
equality (the `.absent` table has one, `MapOps` does not) and no second sibling path. ⚑ Note what IS
shared: ONE `next` felt across both leaf absorbs — the deployed `MAP_NEXT` column
(`map_leaf_input_cols`, "a value update holds the pointer fixed"). -/
def RwImtGatesOn (hash : List ℤ → ℤ) (dep : Nat) (steps : List (Bool × ℤ))
    (oldRoot newRoot key value oldValue next : ℤ) : Prop :=
  steps.length = dep ∧
  pathRecompute hash (imtLeafHash hash ⟨key, oldValue, next⟩) steps = oldRoot ∧
  pathRecompute hash (imtLeafHash hash ⟨key, value, next⟩) steps = newRoot

/-- **`RwImtRowAt`** — the gates PLUS the knowledge-extraction premise: the committed sparse heap
behind the pre-root, carried in exactly the slot `ReconcileGatesAt`'s `∃ h, Heap.SortedKeys h`
occupies. Not a new floor; the same per-deployment premise at the deployed leaf shape. -/
def RwImtRowAt (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat)
    (oldRoot newRoot key value oldValue next : ℤ) : Prop :=
  ∃ (h : Heap.FeltHeap) (steps : List (Bool × ℤ)),
    (padImtSchema sent).HeapOk h ∧ (padImtSchema sent).SizeOk dep h ∧
    padImtRoot sent hash dep h = oldRoot ∧
    RwImtGatesOn hash dep steps oldRoot newRoot key value oldValue next

/-- **`ReadImtRowAt`** — the `.read` row: `RwImtRowAt` at `oldValue := value`, which IS the deployed
`is_real·(1−op)·(op−3)·(MAP_OLD_VALUE − MAP_VALUE) = 0` constraint. -/
def ReadImtRowAt (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat)
    (oldRoot newRoot key value next : ℤ) : Prop :=
  RwImtRowAt sent hash dep oldRoot newRoot key value value next

/-- **★ THE `.write` OPENER, floor-free.** An accepting deployed write row FORCES the row's key
present at the claimed old value AND the post-root column to be the GENUINE padded commitment of
`Heap.set h key value` — the `new_root` column cannot be forged, up to the named residual.

⚑ The proof runs through `imtChainOf_set`, and that is where the deployed SHARED `MAP_NEXT` column
does its work: because the new leaf reuses the old leaf's pointer felt, the post-vector stays inside
the image of `relink_next_addrs` and is therefore the commitment of an actual heap. §5c shows that a
row free to move the pointer is NOT a relink at all. -/
theorem writeImtGates_writes_or_resid (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat)
    {oldRoot newRoot key value oldValue next : ℤ} {h : Heap.FeltHeap} {steps : List (Bool × ℤ)}
    (hok : (padImtSchema sent).HeapOk h) (hsz : (padImtSchema sent).SizeOk dep h)
    (hcommit : padImtRoot sent hash dep h = oldRoot)
    (hg : RwImtGatesOn hash dep steps oldRoot newRoot key value oldValue next) :
    (Heap.get h key = some oldValue
      ∧ writesToMerkleS (padImtSchema sent) hash dep oldRoot key value newRoot)
    ∨ OpenResid sent hash dep h steps ⟨key, oldValue, next⟩ := by
  obtain ⟨hsl, hpOld, hpNew⟩ := hg
  have hsz' : h.length ≤ 2 ^ dep := hsz
  rcases padOpen_binds_or_resid sent hash dep hsz' hsl (by rw [hpOld, ← hcommit]) with
    ⟨hlt, hchain, hheap, hnx, hupd⟩ | hres
  · have hheap' : h[pathPos steps]? = some (key, oldValue) := hheap
    have hnx' : next = (h[pathPos steps + 1]?).elim sent Prod.fst := hnx
    refine Or.inl ⟨get_eq_some_of_getElem? hok.1 hheap', ?_⟩
    have hkmem : key ∈ Heap.keys h :=
      List.mem_map.mpr ⟨_, List.mem_of_getElem? hheap', rfl⟩
    -- the sorted update IS the positional one, at the position the path opened
    have hset : Heap.set h key value = h.set (pathPos steps) (key, value) :=
      heapSet_eq_listSet hok.1 hheap' value
    have hlen' : (Heap.set h key value).length ≤ 2 ^ dep := by
      rw [Heap.length_set_mem h key value hok.1 hkmem]; exact hsz'
    refine ⟨h, hok, hsz, hlen', hcommit, ?_⟩
    -- the post-root is the genuine relinked padded commitment
    have hchainSet : imtChainOf sent (Heap.set h key value)
        = (imtChainOf sent h).set (pathPos steps) (⟨key, value, next⟩ : ImtLeaf) := by
      rw [hset, imtChainOf_set sent h (pathPos steps) key oldValue value hheap', hnx']
    have hclen : pathPos steps < ((imtChainOf sent h).map (imtLeafHash hash)).length := by
      rw [List.length_map, imtChainOf_length]; exact hlt
    have hstep : padTo dep ((imtChainOf sent (Heap.set h key value)).map (imtLeafHash hash))
        = (padVec sent hash dep h).set (pathPos steps)
            (imtLeafHash hash ⟨key, value, next⟩) := by
      rw [hchainSet, map_set']
      exact padTo_set dep _ _ _ hclen
    show newRoot = perfectRoot hash dep (padTo dep
      ((imtChainOf sent (Heap.set h key value)).map (imtLeafHash hash)))
    rw [hstep, ← hupd ⟨key, value, next⟩]
    exact hpNew.symm
  · exact Or.inr hres

/-- **★ THE `.read` OPENER, floor-free.** An accepting deployed read row FORCES the membership
opening at the deployed padded commitment AND — ⚑ **DERIVED, not asserted** — `new_root = root`.
The Lean model `ReconcileGatesAt` states root preservation as a GATE; the deployed `Ir2Air::MapOps`
table writes no such column equality. It falls out because `MAP_OLD_VALUE = MAP_VALUE` makes the two
absorbs the SAME digest and the two chains share `MAP_SIB0`/`MAP_DIR0`. -/
theorem readImtGates_opens_or_resid (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat)
    {oldRoot newRoot key value next : ℤ} {h : Heap.FeltHeap} {steps : List (Bool × ℤ)}
    (hok : (padImtSchema sent).HeapOk h) (hsz : (padImtSchema sent).SizeOk dep h)
    (hcommit : padImtRoot sent hash dep h = oldRoot)
    (hg : RwImtGatesOn hash dep steps oldRoot newRoot key value value next) :
    (opensToMerkleS (padImtSchema sent) hash dep oldRoot key (some value)
      ∧ newRoot = oldRoot)
    ∨ OpenResid sent hash dep h steps ⟨key, value, next⟩ := by
  obtain ⟨hsl, hpOld, hpNew⟩ := hg
  have hsz' : h.length ≤ 2 ^ dep := hsz
  rcases padOpen_binds_or_resid sent hash dep hsz' hsl (by rw [hpOld, ← hcommit]) with
    ⟨_, _, hheap, _, _⟩ | hres
  · exact Or.inl ⟨⟨h, hok, hsz, hcommit, get_eq_some_of_getElem? hok.1 hheap⟩,
      by rw [← hpNew, hpOld]⟩
  · exact Or.inr hres

/-! ### §5b — the STRENGTH BRIDGES, at the injective + pad-free idealisation.

⚠ LABELLED, per the epoch's discipline: these are the `_of_good` forms. `Poseidon2SpongeCR` is
PROVED FALSE at deployed BabyBear parameters, so only the `_or_resid` halves above are statements
about the deployed sponge. What `MapGood` buys is exactly stage 2b's `padImtTeeth.Good`. -/

/-- **★ `.read` at a good hash: gates ⇒ the denotation.** -/
theorem readImtRow_opens_of_good {hash : List ℤ → ℤ} (hgood : MapGood hash) (sent : ℤ) (dep : Nat)
    {oldRoot newRoot key value next : ℤ}
    (hr : ReadImtRowAt sent hash dep oldRoot newRoot key value next) :
    opensToMerkleS (padImtSchema sent) hash dep oldRoot key (some value) ∧ newRoot = oldRoot := by
  obtain ⟨h, steps, hok, hsz, hcommit, hg⟩ := hr
  rcases readImtGates_opens_or_resid sent hash dep hok hsz hcommit hg with hres | hbad
  · exact hres
  · exact absurd hbad (openResid_refuted hgood sent dep h steps _)

/-- **★ `.write` at a good hash: gates ⇒ the denotation.** -/
theorem writeImtRow_writes_of_good {hash : List ℤ → ℤ} (hgood : MapGood hash) (sent : ℤ) (dep : Nat)
    {oldRoot newRoot key value oldValue next : ℤ}
    (hr : RwImtRowAt sent hash dep oldRoot newRoot key value oldValue next) :
    writesToMerkleS (padImtSchema sent) hash dep oldRoot key value newRoot := by
  obtain ⟨h, steps, hok, hsz, hcommit, hg⟩ := hr
  rcases writeImtGates_writes_or_resid sent hash dep hok hsz hcommit hg with hres | hbad
  · exact hres.2
  · exact absurd hbad (openResid_refuted hgood sent dep h steps _)

/-- The deployed padded root BINDS the committed sparse heap, at a good hash — stage 2b's
`padImtTeeth` applied, so nothing new is assumed. Used by every forgery tooth below. -/
theorem padImt_heap_binds {hash : List ℤ → ℤ} (hgood : MapGood hash) (sent : ℤ) (dep : Nat)
    {h₁ h₂ : Heap.FeltHeap}
    (ho₁ : (padImtSchema sent).HeapOk h₁) (ho₂ : (padImtSchema sent).HeapOk h₂)
    (hz₁ : (padImtSchema sent).SizeOk dep h₁) (hz₂ : (padImtSchema sent).SizeOk dep h₂)
    (he : padImtRoot sent hash dep h₁ = padImtRoot sent hash dep h₂) : h₁ = h₂ :=
  ((padImtTeeth sent).binds hash dep h₁ h₂ ho₁ ho₂ hz₁ hz₂ he).resolve_right
    ((padImtTeeth sent).resid_refuted hash hgood dep h₁ h₂)

/-! ### §5c — the SHARED POINTER COLUMN IS LOAD-BEARING.

The deployed old- and new-leaf absorbs read ONE `MAP_NEXT` column. If they did not, a write row
could move the pointer, and the resulting digest vector would be **outside the image of
`relink_next_addrs`** — i.e. not the commitment of ANY heap. This is that fact as a theorem, at the
positional face of the relink: a chain that differs from `imtChainOf` only in one leaf's pointer is
not `imtChainOf` of anything unless the pointer was already the right one. -/

/-- A relinked chain's pointer at a live position is DETERMINED by the heap — so a row that writes a
different pointer has left the image of `relink_next_addrs`. -/
theorem imtChainOf_pointer_determined (sent : ℤ) (h : Heap.FeltHeap) (p : Nat) (l : ImtLeaf)
    (hp : (imtChainOf sent h)[p]? = some l) :
    l.nextAddr = (h[p + 1]?).elim sent Prod.fst := by
  rw [imtChainOf_getElem? sent h p] at hp
  cases hh : h[p]? with
  | none => rw [hh] at hp; simp at hp
  | some e =>
    rw [hh] at hp
    simp only [Option.map_some, Option.some.injEq] at hp
    rw [← hp]

/-- **★ A WRITE THAT MOVES THE POINTER IS NOT A RELINK.** Two distinct pointers at the same live
position cannot both be the deployed relink's. So the write law's conclusion genuinely depends on
the deployed column sharing; it is not an artefact of how the model was written. -/
theorem unshared_pointer_write_is_not_a_relink (sent : ℤ) (h : Heap.FeltHeap) (p : Nat)
    (l l' : ImtLeaf) (hp : (imtChainOf sent h)[p]? = some l)
    (hp' : (imtChainOf sent h)[p]? = some l') : l.nextAddr = l'.nextAddr := by
  rw [imtChainOf_pointer_determined sent h p l hp, imtChainOf_pointer_determined sent h p l' hp']

/-! ## §6 — THE `.insert` ARM (op = 3): the deployed gate, what it FORCES, and what it CANNOT.

⚑ Read `descriptor_ir2.rs` at the selectors. `rw_sel = not_insert + s` is `0` at op = 3, so the
OLD-leaf absorb does not fire; `not_insert3 = not_insert + 2·s` is `0` at op = 3, so the PATH1
old-chain does not fire either. The comment says it plainly: *"insert opens the NEW leaf against the
NEW root (no old leaf at a fresh key)"* (`:3364-3366`). **There is no gate on `MAP_ROOT` at all.**
The enum agrees: *"Freshness must be established separately, e.g. by a paired `MapKind::Absent`
opening against the same pre-root"* (`:540-542`). -/

/-- **`InsertImtGatesOn`** — the deployed op = 3 acceptance, 1:1. Note the absent parameter: this
predicate does not mention the pre-root, because the AIR does not constrain it. -/
def InsertImtGatesOn (hash : List ℤ → ℤ) (dep : Nat) (steps : List (Bool × ℤ))
    (newRoot key value next : ℤ) : Prop :=
  steps.length = dep ∧
  pathRecompute hash (imtLeafHash hash ⟨key, value, next⟩) steps = newRoot

/-- The `.insert` row: the gates plus the knowledge-extraction premise on the **POST** side, which is
the only side the deployed table folds a chain to. -/
def InsertImtRowAt (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat)
    (newRoot key value next : ℤ) : Prop :=
  ∃ (h' : Heap.FeltHeap) (steps : List (Bool × ℤ)),
    (padImtSchema sent).HeapOk h' ∧ (padImtSchema sent).SizeOk dep h' ∧
    padImtRoot sent hash dep h' = newRoot ∧
    InsertImtGatesOn hash dep steps newRoot key value next

/-- **★ THE `.insert` OPENER — the honest positive half.** An accepting deployed insert row FORCES
the POST-root to open the row's key to the row's value: the write LANDED. This is a genuine
denotational fact and it is all the deployed op = 3 gate carries. -/
theorem insertImtGates_post_opens_or_resid (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat)
    {newRoot key value next : ℤ} {h' : Heap.FeltHeap} {steps : List (Bool × ℤ)}
    (hok : (padImtSchema sent).HeapOk h') (hsz : (padImtSchema sent).SizeOk dep h')
    (hcommit : padImtRoot sent hash dep h' = newRoot)
    (hg : InsertImtGatesOn hash dep steps newRoot key value next) :
    opensToMerkleS (padImtSchema sent) hash dep newRoot key (some value)
    ∨ OpenResid sent hash dep h' steps ⟨key, value, next⟩ := by
  obtain ⟨hsl, hp⟩ := hg
  have hsz' : h'.length ≤ 2 ^ dep := hsz
  rcases padOpen_binds_or_resid sent hash dep hsz' hsl (by rw [hp, ← hcommit]) with
    ⟨_, _, hheap, _, _⟩ | hres
  · exact Or.inl ⟨h', hok, hsz, hcommit,
      get_eq_some_of_getElem? hok.1 (show h'[pathPos steps]? = some (key, value) from hheap)⟩
  · exact Or.inr hres

theorem insertImtRow_post_opens_of_good {hash : List ℤ → ℤ} (hgood : MapGood hash)
    (sent : ℤ) (dep : Nat) {newRoot key value next : ℤ}
    (hr : InsertImtRowAt sent hash dep newRoot key value next) :
    opensToMerkleS (padImtSchema sent) hash dep newRoot key (some value) := by
  obtain ⟨h', steps, hok, hsz, hcommit, hg⟩ := hr
  rcases insertImtGates_post_opens_or_resid sent hash dep hok hsz hcommit hg with hres | hbad
  · exact hres
  · exact absurd hbad (openResid_refuted hgood sent dep h' steps _)

/-! ### §6b — ⚑ WHAT THE DEPLOYED `.insert` GATE CANNOT FORCE, PROVED.

`MapOp.holdsAtS`'s `.insert` arm is `writesToMerkleS S hash dep root key value newRoot` — a
statement RELATING the pre-root to the post-root. The deployed op = 3 row constrains only the
post-root, so no such law exists. This is not "not yet proved": it is refuted, below, at a hash that
is injective AND pad-free, with the accepting gate exhibited alongside. -/

/-- A one-entry padded heap is admissible whenever its key is below the sentinel. -/
theorem heapOk_singleton {sent a v : ℤ} (h : a < sent) :
    (padImtSchema sent).HeapOk [(a, v)] := by
  refine ⟨by simp [Heap.SortedKeys, Heap.keys], ?_⟩
  intro x hx
  simp only [Heap.keys, List.map_cons, List.map_nil, List.mem_singleton] at hx
  subst hx
  exact h

theorem sizeOk_of_le {sent : ℤ} {dep : Nat} {h : Heap.FeltHeap} (hl : h.length ≤ 2 ^ dep) :
    (padImtSchema sent).SizeOk dep h := hl

/-- **⚑⚑ THE DEPLOYED `.insert` GATE CANNOT FORCE THE WRITE DENOTATION.** The same accepting op = 3
gate data is compatible with a pre-root at which `writesToMerkleS` is FALSE — because the AIR folds
no chain to `MAP_ROOT` on an insert row. Any "`.insert` opener law" of the shape the other three arms
enjoy is therefore impossible, and the deployed fix is a paired `.absent`/AAFI row, not a proof.
(Anti-floor content: the conclusion is `False`.) -/
theorem insertImtGates_cannot_force_the_write_denotation :
    ¬ (∀ (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat) (oldRoot newRoot key value next : ℤ),
        MapGood hash →
        InsertImtRowAt sent hash dep newRoot key value next →
        writesToMerkleS (padImtSchema sent) hash dep oldRoot key value newRoot) := by
  intro hbad
  have hok57 : (padImtSchema 100).HeapOk [(5, 7)] := heapOk_singleton (by norm_num)
  have hok12 : (padImtSchema 100).HeapOk [(1, 2)] := heapOk_singleton (by norm_num)
  have hok125 : (padImtSchema 100).HeapOk [(1, 2), (5, 7)] := by
    refine ⟨by simp [Heap.SortedKeys, Heap.keys], ?_⟩
    intro x hx
    simp only [Heap.keys, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl <;> norm_num
  -- The accepting gate: ONE path opening the appended leaf to the POST-root, nothing else.
  have hrow : InsertImtRowAt 100 oddSponge 1 (padImtRoot 100 oddSponge 1 [(5, 7)]) 5 7 100 :=
    ⟨[(5, 7)], leftPadPath oddSponge 1, hok57, sizeOk_of_le (by norm_num), rfl,
      leftPadPath_length _ _, by rw [leftPadPath_recompute]; rfl⟩
  have hw := hbad 100 oddSponge 1 (padImtRoot 100 oddSponge 1 [(1, 2)])
    (padImtRoot 100 oddSponge 1 [(5, 7)]) 5 7 100 mapGood_inhabited hrow
  obtain ⟨m, hokm, hszm, hszm', hrm, hnew⟩ := hw
  have hm : m = [(1, 2)] :=
    padImt_heap_binds mapGood_inhabited 100 1 hokm hok12 hszm
      (sizeOk_of_le (by norm_num)) hrm
  subst hm
  have hset : Heap.set ([(1, 2)] : Heap.FeltHeap) 5 7 = [(1, 2), (5, 7)] := by
    norm_num [Heap.set]
  rw [hset] at hnew
  have : ([(5, 7)] : Heap.FeltHeap) = [(1, 2), (5, 7)] :=
    padImt_heap_binds mapGood_inhabited 100 1 hok57 hok125 (sizeOk_of_le (by norm_num))
      (sizeOk_of_le (by norm_num)) hnew
  simp at this

/-! ### §6c — THE EXISTING ARITY-2 `.insert` MODEL IS UNSATISFIABLE AT A FRESH KEY.

This is `MapAbsentImtGate`'s `.absent` finding, verbatim, on a second arm — and it was hiding in
plain sight: `MapOpsColumnLayout.ReconcileGatesAt`'s `.insert` arm demands an OLD-leaf path
`pathRecompute (leafOf (key, vOld)) steps = root`, which BINDS the row's key into the PRE-heap. The
deployed builder refuses an insert whose key is already present (`heap_root.rs::insert_witness`),
so on every honest deployed insert row the model's hypothesis is FALSE and every theorem over it is
vacuous exactly where the prover operates.

⚠ And the epoch's own non-vacuity exhibit does not catch it: `MapOpsColumnLayout.toy_insert_gates`
writes key `20`, which `toyHeap` already HOLDS (`toyGrown = Heap.set toyHeap 20 9` is an in-place
UPDATE, `toyHeap.length = toyGrown.length`). The `.insert` teeth have only ever been exercised on a
value update. -/

/-- The arity-2 model's `.insert` arm FORCES the row's key into the committed pre-heap. -/
theorem reconcileGates_insert_forces_key_present (hash : List ℤ → ℤ)
    (hinj : Function.Injective hash) (dep : Nat) (a : Assignment) (m : MapOp)
    (hop : m.op = MapOpKind.insert) (hg : ReconcileGatesAt hash dep a m) :
    ∃ h : Heap.FeltHeap, Heap.SortedKeys h ∧ h.length = 2 ^ dep ∧
      mapRoot hash dep h = (m.root 0).eval a ∧ m.key.eval a ∈ Heap.keys h := by
  obtain ⟨h, hs, hlen, hroot, hgates⟩ := hg
  rw [hop] at hgates
  obtain ⟨steps, vOld, hsl, hpOld, _⟩ := hgates
  have hbind := (pathRecompute_binds_updates hash steps (h.map (Heap.leafOf hash))
    (Heap.leafOf hash (m.key.eval a, vOld))
    (by rw [List.length_map, hlen, hsl]) (by rw [hsl]; exact hpOld.trans hroot.symm)
    (noPathColl_of_CR hinj)).1
  simp only [List.getElem?_map] at hbind
  cases he : h[pathPos steps]? with
  | none => rw [he] at hbind; simp at hbind
  | some e =>
    rw [he] at hbind
    simp only [Option.map_some, Option.some.injEq] at hbind
    obtain rfl := leafOf_injective hash (noLeafColl_of_CR hinj) hbind
    exact ⟨h, hs, hlen, hroot, List.mem_map.mpr ⟨_, List.mem_of_getElem? he, rfl⟩⟩

/-- **★ THE ARITY-2 `.insert` MODEL HAS NO WITNESS AT A FRESH KEY** — for any committed heap behind
the row's pre-root and any path. Exactly the shape of
`MapAbsentImtGate.adjacentBracket_unsat_above_max`, on the arm nobody looked at. -/
theorem reconcileGates_insert_unsat_at_fresh_key (hash : List ℤ → ℤ)
    (hinj : Function.Injective hash) (dep : Nat) (a : Assignment) (m : MapOp)
    (hop : m.op = MapOpKind.insert) (h : Heap.FeltHeap) (hlen : h.length = 2 ^ dep)
    (hroot : mapRoot hash dep h = (m.root 0).eval a) (hfresh : m.key.eval a ∉ Heap.keys h) :
    ¬ ReconcileGatesAt hash dep a m := by
  intro hg
  obtain ⟨h', _, hlen', hroot', hmem⟩ :=
    reconcileGates_insert_forces_key_present hash hinj dep a m hop hg
  have hhh : h' = h :=
    (mapRoot_binds_or_collides hash dep hlen' hlen (hroot'.trans hroot.symm)).resolve_right
      (spongeColl_refutable_of_injective hash hinj _)
  rw [hhh] at hmem
  exact hfresh hmem

/-! ## §7 — THE `.aafiInsert` ARM (op = 4): the deployed gate at the PINNED padding constant.

The Lean `MapOpsColumnLayout.AafiGatesAt` carries the free-slot digest as a FREE variable
`freeEmpty`. The deployed AIR does not: `descriptor_ir2.rs:3493-3495` asserts
`s · MAP_FREE_EMPTY[i] = 0` for all eight lanes, pinning it to `heap_empty_subtree_root_8(0)` =
`ZERO8` — **the padding constant**. So the deployed AAFI append lands in the PADDING, which is
precisely the occupancy stage 2b modelled, and the model below pins it. -/

/-- **`AafiImtGatesOn`** — the deployed op = 4 acceptance for ONE row, 1:1, at the PINNED free-slot
digest. Gates (a) low-open, (b) pointer bracket, (c) PATH1 low-update → `R1`, (d1) PATH2 free slot
holds `padDigest` under `R1`, (d2) PATH2 append → `new_root`. -/
def AafiImtGatesOn (hash : List ℤ → ℤ) (dep : Nat) (steps1 steps2 : List (Bool × ℤ))
    (oldRoot newRoot R1 key value lowAddr lowValue lowNext : ℤ) : Prop :=
  steps1.length = dep ∧ steps2.length = dep ∧ pathPos steps1 ≠ pathPos steps2 ∧
  pathRecompute hash (imtLeafHash hash ⟨lowAddr, lowValue, lowNext⟩) steps1 = oldRoot ∧
  lowAddr < key ∧ key < lowNext ∧
  pathRecompute hash (imtLeafHash hash ⟨lowAddr, lowValue, key⟩) steps1 = R1 ∧
  pathRecompute hash padDigest steps2 = R1 ∧
  pathRecompute hash (imtLeafHash hash ⟨key, value, lowNext⟩) steps2 = newRoot

/-- The `.aafiInsert` row: the gates plus the committed sparse heap behind the PRE-root (which is
`heap_root.rs`'s SORTED `root8`, `insert_witness_aafi:1153`). -/
def AafiImtRowAt (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat)
    (oldRoot newRoot R1 key value lowAddr lowValue lowNext : ℤ) : Prop :=
  ∃ (h : Heap.FeltHeap) (steps1 steps2 : List (Bool × ℤ)),
    (padImtSchema sent).HeapOk h ∧ (padImtSchema sent).SizeOk dep h ∧
    padImtRoot sent hash dep h = oldRoot ∧
    AafiImtGatesOn hash dep steps1 steps2 oldRoot newRoot R1 key value lowAddr lowValue lowNext

/-- **★ THE `.aafiInsert` OPENER — the double-spend tooth at the DEPLOYED PADDED commitment.** An
accepting deployed AAFI row FORCES the row's key ABSENT from the pre-tree: gate (a) binds the low
leaf into the relinked chain, gate (b)'s pointer bracket is the `ImtAbsent` witness, and
`imtAbsent_excludes` on the chain the schema's `HeapOk` guarantees is sorted does the rest.

⚠ The pre-chain's `ImtSorted` is DERIVED here (`imtSchema_chain_imtSorted`), not assumed — the
schema's `HeapOk` field already pays for it. That is the one place this arm is CHEAPER than
`MapAbsentImtGate`'s `.absent` law, which takes `ImtSorted c` as a hypothesis. -/
theorem aafiImtGates_force_absence_or_resid (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat)
    {oldRoot newRoot R1 key value lowAddr lowValue lowNext : ℤ}
    {h : Heap.FeltHeap} {steps1 steps2 : List (Bool × ℤ)}
    (hok : (padImtSchema sent).HeapOk h) (hsz : (padImtSchema sent).SizeOk dep h)
    (hcommit : padImtRoot sent hash dep h = oldRoot)
    (hg : AafiImtGatesOn hash dep steps1 steps2 oldRoot newRoot R1 key value lowAddr lowValue
      lowNext) :
    (Heap.get h key = none
      ∧ opensToMerkleS (padImtSchema sent) hash dep oldRoot key none)
    ∨ OpenResid sent hash dep h steps1 ⟨lowAddr, lowValue, lowNext⟩ := by
  obtain ⟨hsl1, _, _, hpa, hlk, hkn, _, _, _⟩ := hg
  have hsz' : h.length ≤ 2 ^ dep := hsz
  rcases padOpen_binds_or_resid sent hash dep hsz' hsl1 (by rw [hpa, ← hcommit]) with
    ⟨_, hchain, _, _, _⟩ | hres
  · have hmem : (⟨lowAddr, lowValue, lowNext⟩ : ImtLeaf) ∈ imtChainOf sent h :=
      List.mem_of_getElem? hchain
    have hs : ImtSorted (imtChainOf sent h) := imtSchema_chain_imtSorted sent h hok
    have hnotin : key ∉ imtAddrs (imtChainOf sent h) :=
      imtAbsent_excludes hs ⟨⟨lowAddr, lowValue, lowNext⟩, hmem, hlk, hkn⟩
    have hkeys : Heap.keys h = imtAddrs (imtChainOf sent h) := by
      rw [← keys_imtToHeap (imtChainOf sent h), imtToHeap_imtChainOf sent h]
    have hnone : Heap.get h key = none := by
      rw [Heap.get_eq_none_iff, hkeys]; exact hnotin
    exact Or.inl ⟨hnone, ⟨h, hok, hsz, hcommit, hnone⟩⟩
  · exact Or.inr hres

/-- **★ `.aafiInsert` at a good hash: gates ⇒ the absence denotation.** -/
theorem aafiImtRow_forces_absence_of_good {hash : List ℤ → ℤ} (hgood : MapGood hash)
    (sent : ℤ) (dep : Nat) {oldRoot newRoot R1 key value lowAddr lowValue lowNext : ℤ}
    (hr : AafiImtRowAt sent hash dep oldRoot newRoot R1 key value lowAddr lowValue lowNext) :
    opensToMerkleS (padImtSchema sent) hash dep oldRoot key none := by
  obtain ⟨h, steps1, steps2, hok, hsz, hcommit, hg⟩ := hr
  rcases aafiImtGates_force_absence_or_resid sent hash dep hok hsz hcommit hg with hres | hbad
  · exact hres.2
  · exact absurd hbad (openResid_refuted hgood sent dep h steps1 _)

/-! ## §7b — ⚑⚑ THE EIGHTH IMPOSSIBILITY: the deployed AAFI POST-root is not a function of the map.

`heap_root.rs::insert_witness_aafi` appends at `next_free_index` and folds `append_order_after`,
which the code itself calls *"a distinct commitment lineage from the sorted-compacted `root8` (same
leaf SET, different positions)"*. A `MapLeafSchema.commit` is a function of the SORTED heap. Two
physical layouts of one logical map therefore have one `S.commit` and two padded folds — so no
schema models the AAFI post-commitment, at any depth, at any hash good enough for the teeth. -/

/-- The PHYSICAL (append-order) padded fold — `fold_append_order_8`'s 1-felt face. -/
def appendOrderRoot (hash : List ℤ → ℤ) (dep : Nat) (phys : List ImtLeaf) : ℤ :=
  perfectRoot hash dep (padTo dep (phys.map (imtLeafHash hash)))

/-- The deployed SORTED commitment is the physical fold of the RELINKED SORTED layout — so the two
differ exactly by the placement, which is the whole content of §7b. -/
theorem padImtRoot_eq_appendOrderRoot (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat)
    (h : Heap.FeltHeap) :
    padImtRoot sent hash dep h = appendOrderRoot hash dep (imtChainOf sent h) := rfl

theorem padHit_map_refuted {hash : List ℤ → ℤ} (hpf : PadFree3 hash) (p : List ImtLeaf) :
    ¬ PadHit (p.map (imtLeafHash hash)) := by
  intro hmem
  rw [PadHit, List.mem_map] at hmem
  obtain ⟨l, _, hl⟩ := hmem
  exact hpf l hl

theorem map_imtLeafHash_injective {hash : List ℤ → ℤ} (hinj : Function.Injective hash) :
    ∀ {p q : List ImtLeaf}, p.map (imtLeafHash hash) = q.map (imtLeafHash hash) → p = q := by
  intro p
  induction p with
  | nil =>
    intro q h
    cases q with
    | nil => rfl
    | cons _ _ => simp at h
  | cons l ls ih =>
    intro q h
    cases q with
    | nil => simp at h
    | cons l' ls' =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨hd, ht⟩ := h
      have hll : l = l' :=
        (imtLeafHash_binds_or_collides hash hd).resolve_right (fun hc => hc.1 (hinj hc.2))
      rw [hll, ih ht]

/-- **The PHYSICAL padded fold BINDS the physical layout** — at a good hash, two layouts with the
same padded root are the same LIST, order included. -/
theorem appendOrderRoot_binds {hash : List ℤ → ℤ} (hgood : MapGood hash) (dep : Nat)
    {p q : List ImtLeaf} (hp : p.length ≤ 2 ^ dep) (hq : q.length ≤ 2 ^ dep)
    (he : appendOrderRoot hash dep p = appendOrderRoot hash dep q) : p = q := by
  have hlp : (padTo dep (p.map (imtLeafHash hash))).length = 2 ^ dep :=
    padTo_length (by rw [List.length_map]; exact hp)
  have hlq : (padTo dep (q.map (imtLeafHash hash))).length = 2 ^ dep :=
    padTo_length (by rw [List.length_map]; exact hq)
  rcases perfectRoot_binds_or_collides hash dep hlp hlq he with hveq | hcol
  · rcases append_replicate_eq_or_hit _ _ _ _ hveq with hmeq | hh | hh
    · exact map_imtLeafHash_injective hgood.1 hmeq
    · exact absurd hh (padHit_map_refuted hgood.2 p)
    · exact absurd hh (padHit_map_refuted hgood.2 q)
  · exact absurd hcol (spongeColl_refutable_of_injective hash hgood.1 _)

/-- **⚑⚑ NO `MapLeafSchema` COMMITS THE DEPLOYED AAFI POST-LAYOUT.** For EVERY schema, at every
depth ≥ 1, the claim *"the padded fold of the physical layout is `S.commit` of the logical chain"*
is FALSE — because a permutation of the chain is a different layout with the same logical map, and
`S.commit` cannot take two values at one argument. Hence the `.aafiInsert` arm of `MapOp.holdsAtS S`
(which is `writesToMerkleS S`, a statement about the logical map) cannot be the deployed AAFI
post-condition at ANY instance of the landed schema. (Anti-floor content: conclusion `False`.) -/
theorem no_schema_commits_the_append_order_layout (S : MapLeafSchema) (dep : Nat) (hdep : 1 ≤ dep) :
    ¬ (∀ (hash : List ℤ → ℤ), MapGood hash →
        ∀ (c phys : List ImtLeaf), List.Perm phys c → ImtSorted c → phys.length ≤ 2 ^ dep →
          appendOrderRoot hash dep phys = S.commit hash dep (imtToHeap c)) := by
  intro hbad
  have h2 : (2 : Nat) ≤ 2 ^ dep := by
    calc (2 : Nat) = 2 ^ 1 := rfl
      _ ≤ 2 ^ dep := Nat.pow_le_pow_right (by norm_num) hdep
  have hs : ImtSorted [(⟨1, 0, 2⟩ : ImtLeaf), (⟨2, 0, 3⟩ : ImtLeaf)] :=
    ⟨by norm_num, rfl, by norm_num⟩
  have hlen2 : ([(⟨1, 0, 2⟩ : ImtLeaf), (⟨2, 0, 3⟩ : ImtLeaf)]).length ≤ 2 ^ dep := by
    simpa using h2
  have hlen2' : ([(⟨2, 0, 3⟩ : ImtLeaf), (⟨1, 0, 2⟩ : ImtLeaf)]).length ≤ 2 ^ dep := by
    simpa using h2
  have e1 := hbad oddSponge mapGood_inhabited _ _ (List.Perm.refl _) hs hlen2
  have e2 := hbad oddSponge mapGood_inhabited [(⟨1, 0, 2⟩ : ImtLeaf), (⟨2, 0, 3⟩ : ImtLeaf)]
    [(⟨2, 0, 3⟩ : ImtLeaf), (⟨1, 0, 2⟩ : ImtLeaf)]
    (List.Perm.swap (⟨1, 0, 2⟩ : ImtLeaf) (⟨2, 0, 3⟩ : ImtLeaf) []) hs hlen2'
  have hswap := appendOrderRoot_binds mapGood_inhabited dep hlen2 hlen2' (e1.trans e2.symm)
  simp at hswap

/-- **⚑ THE SEPARATION, CONCRETELY, at the deployed leaf.** Insert key `5` into `[(1,7),(9,3)]`:
the deployed AAFI post-layout is `[⟨1,7,5⟩, ⟨9,3,100⟩, ⟨5,2,9⟩]` (append order, `free_index` last)
while the padded SORTED commitment of the same logical map folds `[⟨1,7,5⟩, ⟨5,2,9⟩, ⟨9,3,100⟩]`.
Different roots at a hash that is injective and pad-free. So the AAFI write denotation at
`padImtSchema` holds only when the appended key happens to be the MAXIMUM (§9's exhibit is such a
row); in general it does not. -/
theorem aafi_post_is_not_the_sorted_commit (dep : Nat) (hdep : 2 ≤ dep) :
    appendOrderRoot oddSponge dep
        [(⟨1, 7, 5⟩ : ImtLeaf), (⟨9, 3, 100⟩ : ImtLeaf), (⟨5, 2, 9⟩ : ImtLeaf)]
      ≠ padImtRoot 100 oddSponge dep [(1, 7), (5, 2), (9, 3)] := by
  intro he
  have h4 : (4 : Nat) ≤ 2 ^ dep := by
    calc (4 : Nat) = 2 ^ 2 := rfl
      _ ≤ 2 ^ dep := Nat.pow_le_pow_right (by norm_num) hdep
  have hchain : imtChainOf 100 [(1, 7), (5, 2), (9, 3)]
      = [(⟨1, 7, 5⟩ : ImtLeaf), (⟨5, 2, 9⟩ : ImtLeaf), (⟨9, 3, 100⟩ : ImtLeaf)] := rfl
  have h3 : (3 : Nat) ≤ 2 ^ dep := by omega
  rw [padImtRoot_eq_appendOrderRoot, hchain] at he
  have := appendOrderRoot_binds mapGood_inhabited dep (by simpa using h3) (by simpa using h3) he
  simp at this

/-! ## §8 — THE INSERT/WRITE GROWTH QUESTION, ANSWERED.

A sibling proved that at the map-tree layer `(Heap.set h k v).length = 2 ^ dep` forces the written
key ALREADY committed. That is confirmed below at schema level — and then MOVED: it is a consequence
of the DENSE `SizeOk`, and stage 2b's padded `SizeOk` (`≤`) removes it. Growth is representable at
the padded instance and is exhibited at `MAP_TREE_DEPTH = 16`. -/

/-- **★ AT A DENSE SCHEMA, A WRITE CANNOT GROW THE MAP** — the written key must already be
committed, so `.write`/`.insert` denote an in-place UPDATE and nothing else. -/
theorem denseSchema_write_forces_key_present (S : MapLeafSchema)
    (hdense : ∀ (d : Nat) (m : Heap.FeltHeap), S.SizeOk d m → m.length = 2 ^ d)
    (hash : List ℤ → ℤ) (dep : Nat) {r k v r' : ℤ}
    (hw : writesToMerkleS S hash dep r k v r') :
    ∃ m : Heap.FeltHeap, S.HeapOk m ∧ m.length = 2 ^ dep ∧ k ∈ Heap.keys m := by
  obtain ⟨m, hok, hz, hz', _, _⟩ := hw
  refine ⟨m, hok, hdense dep m hz, ?_⟩
  by_contra hk
  have hgrow : (Heap.set m k v).length = m.length + 1 := Heap.length_set_fresh m k v hk
  have h1 : (Heap.set m k v).length = 2 ^ dep := hdense dep _ hz'
  have h2 : m.length = 2 ^ dep := hdense dep m hz
  omega

/-- The deployed-today arity-2 shape: `writesToMerkle` (hence `DescriptorIR2.writesTo`) is an
in-place update predicate. -/
theorem narrow_write_forces_key_present (hash : List ℤ → ℤ) (dep : Nat) {r k v r' : ℤ}
    (hw : writesToMerkle hash dep r k v r') :
    ∃ m : Heap.FeltHeap, Heap.SortedKeys m ∧ m.length = 2 ^ dep ∧ k ∈ Heap.keys m :=
  denseSchema_write_forces_key_present narrowSchema (fun _ _ h => h) hash dep hw

/-- The landed arity-3 DENSE schema: same verdict. -/
theorem imtSchema_write_forces_key_present (sent : ℤ) (hash : List ℤ → ℤ) (dep : Nat)
    {r k v r' : ℤ} (hw : writesToMerkleS (imtSchema sent) hash dep r k v r') :
    ∃ m : Heap.FeltHeap, (imtSchema sent).HeapOk m ∧ m.length = 2 ^ dep ∧ k ∈ Heap.keys m :=
  denseSchema_write_forces_key_present (imtSchema sent) (fun _ _ h => h) hash dep hw

section Growth

/-- A one-live-leaf sparse tree at the DEPLOYED depth, and a FRESH key written into it. -/
def growSent : ℤ := 100
def growHeap : Heap.FeltHeap := [(1, 2)]
noncomputable def growRoot : ℤ := padImtRoot growSent oddSponge MAP_TREE_DEPTH growHeap
noncomputable def growNewRoot : ℤ :=
  padImtRoot growSent oddSponge MAP_TREE_DEPTH (Heap.set growHeap 5 7)

theorem growHeap_ok : (padImtSchema growSent).HeapOk growHeap :=
  heapOk_singleton (by norm_num [growSent])

theorem growHeap_set_ok : (padImtSchema growSent).HeapOk (Heap.set growHeap 5 7) := by
  have hset : Heap.set growHeap 5 7 = [(1, 2), (5, 7)] := by norm_num [growHeap, Heap.set]
  rw [hset]
  refine ⟨by simp [Heap.SortedKeys, Heap.keys], ?_⟩
  intro x hx
  simp only [Heap.keys, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl | rfl <;> norm_num [growSent]

/-- **★★ AT THE PADDED SCHEMA, GROWTH IS REPRESENTABLE — and here it is, at `MAP_TREE_DEPTH = 16`.**
The key `5` is FRESH, the heap gains one entry, and `writesToMerkleS` still holds. This is exactly
what `denseSchema_write_forces_key_present` forbids at the dense instances, so stage 2b's `SizeOk`
relaxation genuinely changed what the `.write`/`.insert` denotations can SAY. -/
theorem padImt_write_admits_growth :
    writesToMerkleS (padImtSchema growSent) oddSponge MAP_TREE_DEPTH growRoot 5 7 growNewRoot
    ∧ (5 : ℤ) ∉ Heap.keys growHeap
    ∧ (Heap.set growHeap 5 7).length = growHeap.length + 1 := by
  have hfresh : (5 : ℤ) ∉ Heap.keys growHeap := by decide
  refine ⟨⟨growHeap, growHeap_ok, ?_, ?_, rfl, rfl⟩, hfresh,
    Heap.length_set_fresh growHeap 5 7 hfresh⟩
  · show growHeap.length ≤ 2 ^ MAP_TREE_DEPTH
    show 1 ≤ 2 ^ MAP_TREE_DEPTH
    exact Nat.one_le_pow _ 2 (by norm_num)
  · show (Heap.set growHeap 5 7).length ≤ 2 ^ MAP_TREE_DEPTH
    rw [Heap.length_set_fresh growHeap 5 7 hfresh]
    show 1 + 1 ≤ 2 ^ MAP_TREE_DEPTH
    calc (2 : Nat) = 2 ^ 1 := rfl
      _ ≤ 2 ^ MAP_TREE_DEPTH := Nat.pow_le_pow_right (by norm_num) (by decide)

end Growth

/-! ## §9 — NON-VACUITY, AT `MAP_TREE_DEPTH = 16` OVER A SPARSE TREE.

Each of the four arms gets BOTH polarities on the shape `heap_root.rs` actually builds — a
`2^16`-leaf commitment holding ONE live leaf, everything else `EMPTY_SUBTREE_ROOTS` — because a law
with no inhabited instance at the deployed depth is the ∃-image mistake this campaign spent days
refuting. Nothing here evaluates a root or a `2^16` object: every root is NAMED as the schema's own
`commit`, and every path is the symbolic `leftPadPath` / `slot1Path` recursion of §3. -/

section Bite16

theorem two_le_two_pow_depth : (2 : Nat) ≤ 2 ^ MAP_TREE_DEPTH := by
  calc (2 : Nat) = 2 ^ 1 := rfl
    _ ≤ 2 ^ MAP_TREE_DEPTH := Nat.pow_le_pow_right (by norm_num) (by decide)

/-- The deployed terminal sentinel of these exhibits. -/
def biteSent : ℤ := 100
/-- ⚑ A SPARSE tree: ONE live leaf in a `2^16`-leaf commitment. The DENSE `opensToMerkle` has no
witness for such a tree at all; this is the occupancy `CanonicalHeapTree::new` produces. -/
def biteHeap : Heap.FeltHeap := [(1, 7)]
def biteLeaf : ImtLeaf := ⟨1, 7, biteSent⟩
/-- The committed root, NAMED as the schema's own `commit` — never evaluated. -/
noncomputable def biteRoot : ℤ := padImtRoot biteSent oddSponge MAP_TREE_DEPTH biteHeap
/-- The deployed membership path of position `0` at depth 16, built symbolically. -/
noncomputable def biteSteps : List (Bool × ℤ) := leftPadPath oddSponge MAP_TREE_DEPTH

theorem bite_steps_length : biteSteps.length = MAP_TREE_DEPTH := leftPadPath_length _ _
theorem bite_steps_pos : pathPos biteSteps = 0 := leftPadPath_pos _ _

/-- The one-entry relinked chain, at the LIST level (cheap `rfl`; nothing folds). -/
theorem bite_chain (a v n : ℤ) :
    (imtChainOf n [(a, v)]).map (imtLeafHash oddSponge) = [imtLeafHash oddSponge ⟨a, v, n⟩] := rfl

/-- The depth-16 leftmost opening, for ANY arity-3 leaf: the path recomputes to the padded root of
the one-entry heap whose terminal pointer is the leaf's. -/
theorem bite_path_leaf (a v n : ℤ) :
    pathRecompute oddSponge (imtLeafHash oddSponge ⟨a, v, n⟩) biteSteps
      = padImtRoot n oddSponge MAP_TREE_DEPTH [(a, v)] := by
  rw [padImtRoot_unfold, bite_chain]
  show pathRecompute oddSponge _ (leftPadPath oddSponge MAP_TREE_DEPTH) = _
  exact leftPadPath_recompute _ _ _

theorem biteHeap_ok : (padImtSchema biteSent).HeapOk biteHeap :=
  heapOk_singleton (by norm_num [biteSent])

theorem biteHeap_sz : (padImtSchema biteSent).SizeOk MAP_TREE_DEPTH biteHeap := by
  show biteHeap.length ≤ 2 ^ MAP_TREE_DEPTH
  show 1 ≤ 2 ^ MAP_TREE_DEPTH
  exact Nat.one_le_pow _ 2 (by norm_num)

/-! ### §9a — `.read`. -/

theorem bite_read_row : ReadImtRowAt biteSent oddSponge MAP_TREE_DEPTH biteRoot biteRoot 1 7
    biteSent :=
  ⟨biteHeap, biteSteps, biteHeap_ok, biteHeap_sz, rfl,
    bite_steps_length, bite_path_leaf 1 7 biteSent, bite_path_leaf 1 7 biteSent⟩

/-- **★ THE `.read` LAW FIRES at the deployed depth on a sparse tree** — and root preservation comes
out DERIVED. -/
theorem bite_read_fires :
    opensToMerkleS (padImtSchema biteSent) oddSponge MAP_TREE_DEPTH biteRoot 1 (some 7)
    ∧ biteRoot = biteRoot :=
  readImtRow_opens_of_good mapGood_inhabited biteSent MAP_TREE_DEPTH bite_read_row

/-- **★★ THE `.read` TOOTH BITES.** No accepting deployed read row — for ANY claimed post-root and
ANY claimed pointer — can open key `1` of this commitment to the forged value `9`. -/
theorem bite_read_forged_value_refused (newRoot next : ℤ) :
    ¬ ReadImtRowAt biteSent oddSponge MAP_TREE_DEPTH biteRoot newRoot 1 9 next := by
  intro hr
  have h9 := (readImtRow_opens_of_good mapGood_inhabited biteSent MAP_TREE_DEPTH hr).1
  have hEq := opensToMerkleS_functional_of_good (padImtTeeth biteSent)
    ⟨oddSponge_injective, oddSponge_padFree3⟩ MAP_TREE_DEPTH h9 bite_read_fires.1
  simp at hEq

/-! ### §9b — `.write`. -/

noncomputable def biteNewRoot : ℤ := padImtRoot biteSent oddSponge MAP_TREE_DEPTH [(1, 9)]

theorem bite_write_row :
    RwImtRowAt biteSent oddSponge MAP_TREE_DEPTH biteRoot biteNewRoot 1 9 7 biteSent :=
  ⟨biteHeap, biteSteps, biteHeap_ok, biteHeap_sz, rfl,
    bite_steps_length, bite_path_leaf 1 7 biteSent, bite_path_leaf 1 9 biteSent⟩

/-- **★ THE `.write` LAW FIRES**: the post-root column is the GENUINE padded commitment of the
updated sparse map, at `MAP_TREE_DEPTH = 16`. -/
theorem bite_write_fires :
    writesToMerkleS (padImtSchema biteSent) oddSponge MAP_TREE_DEPTH biteRoot 1 9 biteNewRoot :=
  writeImtRow_writes_of_good mapGood_inhabited biteSent MAP_TREE_DEPTH bite_write_row

/-- **★★ THE `.write` TOOTH BITES — the FROZEN post-root forgery is refused.** A write row that
claims to move the value while keeping `new_root = root` has no accepting deployed gate data. -/
theorem bite_write_frozen_root_refused :
    ¬ RwImtRowAt biteSent oddSponge MAP_TREE_DEPTH biteRoot biteRoot 1 9 7 biteSent := by
  intro hr
  have hfrozen := writeImtRow_writes_of_good mapGood_inhabited biteSent MAP_TREE_DEPTH hr
  have heq : biteRoot = biteNewRoot :=
    writesToMerkleS_functional_of_good (padImtTeeth biteSent)
      ⟨oddSponge_injective, oddSponge_padFree3⟩ MAP_TREE_DEPTH hfrozen bite_write_fires
  have hok19 : (padImtSchema biteSent).HeapOk [(1, 9)] := heapOk_singleton (by norm_num [biteSent])
  have hsz19 : (padImtSchema biteSent).SizeOk MAP_TREE_DEPTH [(1, 9)] := by
    show ([(1, 9)] : Heap.FeltHeap).length ≤ 2 ^ MAP_TREE_DEPTH
    show 1 ≤ 2 ^ MAP_TREE_DEPTH
    exact Nat.one_le_pow _ 2 (by norm_num)
  have hbad : biteHeap = [(1, 9)] :=
    padImt_heap_binds mapGood_inhabited biteSent MAP_TREE_DEPTH biteHeap_ok hok19 biteHeap_sz
      hsz19 heq
  simp [biteHeap] at hbad

/-! ### §9c — `.insert`: the gate ACCEPTS a FRESH key, and the pre-root is FREE. -/

theorem bite_insert_row : InsertImtRowAt biteSent oddSponge MAP_TREE_DEPTH biteRoot 1 7 biteSent :=
  ⟨biteHeap, biteSteps, biteHeap_ok, biteHeap_sz, rfl,
    bite_steps_length, bite_path_leaf 1 7 biteSent⟩

/-- **★ THE `.insert` LAW FIRES on its POST side**: the write landed in the committed post-tree. -/
theorem bite_insert_post_opens :
    opensToMerkleS (padImtSchema biteSent) oddSponge MAP_TREE_DEPTH biteRoot 1 (some 7) :=
  insertImtRow_post_opens_of_good mapGood_inhabited biteSent MAP_TREE_DEPTH bite_insert_row

noncomputable def biteOtherRoot : ℤ := padImtRoot biteSent oddSponge MAP_TREE_DEPTH [(3, 4)]

/-- **The write denotation is FALSE at a pre-root whose genuine update misses the claimed post-root**
— depth-GENERIC, so the deployed-depth instance below transports it instead of re-deriving it. -/
theorem write_denotation_false_of_wrong_preroot {hash : List ℤ → ℤ} (hgood : MapGood hash)
    (sent : ℤ) (dep : Nat) {h₀ h₁ : Heap.FeltHeap} {k v : ℤ}
    (ho₀ : (padImtSchema sent).HeapOk h₀) (hz₀ : (padImtSchema sent).SizeOk dep h₀)
    (ho₁ : (padImtSchema sent).HeapOk h₁) (hz₁ : (padImtSchema sent).SizeOk dep h₁)
    (hoS : (padImtSchema sent).HeapOk (Heap.set h₀ k v))
    (hzS : (padImtSchema sent).SizeOk dep (Heap.set h₀ k v))
    (hne : h₁ ≠ Heap.set h₀ k v) :
    ¬ writesToMerkleS (padImtSchema sent) hash dep
        (padImtRoot sent hash dep h₀) k v (padImtRoot sent hash dep h₁) := by
  rintro ⟨m, hokm, hszm, _, hrm, hnew⟩
  have hm : m = h₀ := padImt_heap_binds hgood sent dep hokm ho₀ hszm hz₀ hrm
  subst hm
  exact hne (padImt_heap_binds hgood sent dep ho₁ hoS hz₁ hzS hnew)

theorem bite_set34 : Heap.set ([(3, 4)] : Heap.FeltHeap) 1 7 = [(1, 7), (3, 4)] := by
  norm_num [Heap.set]

theorem bite_ok34 : (padImtSchema biteSent).HeapOk [(3, 4)] :=
  heapOk_singleton (by norm_num [biteSent])

theorem bite_sz34 : (padImtSchema biteSent).SizeOk MAP_TREE_DEPTH [(3, 4)] := by
  show ([(3, 4)] : Heap.FeltHeap).length ≤ 2 ^ MAP_TREE_DEPTH
  show 1 ≤ 2 ^ MAP_TREE_DEPTH
  exact Nat.one_le_pow _ 2 (by norm_num)

theorem bite_ok134 : (padImtSchema biteSent).HeapOk (Heap.set ([(3, 4)] : Heap.FeltHeap) 1 7) := by
  rw [bite_set34]
  refine ⟨by simp [Heap.SortedKeys, Heap.keys], ?_⟩
  intro x hx
  simp only [Heap.keys, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl | rfl <;> norm_num [biteSent]

theorem bite_sz134 :
    (padImtSchema biteSent).SizeOk MAP_TREE_DEPTH (Heap.set ([(3, 4)] : Heap.FeltHeap) 1 7) := by
  show (Heap.set ([(3, 4)] : Heap.FeltHeap) 1 7).length ≤ 2 ^ MAP_TREE_DEPTH
  rw [bite_set34]
  show 2 ≤ 2 ^ MAP_TREE_DEPTH
  exact two_le_two_pow_depth

theorem bite_ne134 : biteHeap ≠ Heap.set ([(3, 4)] : Heap.FeltHeap) 1 7 := by
  rw [bite_set34]
  simp [biteHeap]

/-- **⚑⚑ THE `.insert` IMPOSSIBILITY, CONCRETE AT THE DEPLOYED DEPTH.** The very same accepting
op = 3 gate data sits alongside a pre-root at which `writesToMerkleS` is FALSE — because the deployed
AIR folds NO chain to `MAP_ROOT` on an insert row. This is why `.insert` gets a post-side law and
not an opener: freshness and the pre-root have to come from a paired `.absent` / AAFI row. -/
theorem bite_insert_preroot_is_unforced :
    InsertImtRowAt biteSent oddSponge MAP_TREE_DEPTH biteRoot 1 7 biteSent
    ∧ ¬ writesToMerkleS (padImtSchema biteSent) oddSponge MAP_TREE_DEPTH biteOtherRoot 1 7
        biteRoot :=
  ⟨bite_insert_row,
    write_denotation_false_of_wrong_preroot mapGood_inhabited biteSent MAP_TREE_DEPTH
      bite_ok34 bite_sz34 biteHeap_ok biteHeap_sz bite_ok134 bite_sz134 bite_ne134⟩

/-! ### §9d — `.aafiInsert`: the two-path insert at the deployed depth, growing INTO the padding. -/

/-- The intermediate root after the low-pointer update — which is the padded commitment of the SAME
one-entry heap with terminal pointer `5` (`imtChainOf 5 [(1,7)] = [⟨1,7,5⟩]`). -/
noncomputable def aafiR1 : ℤ := padImtRoot 5 oddSponge MAP_TREE_DEPTH [(1, 7)]
noncomputable def aafiNewRoot : ℤ := padImtRoot biteSent oddSponge MAP_TREE_DEPTH [(1, 7), (5, 2)]
/-- PATH2 — the free-slot path, at the FIRST PADDING POSITION (`free_index = next_free_index = 1`). -/
noncomputable def aafiSteps2 : List (Bool × ℤ) :=
  slot1Path oddSponge (imtLeafHash oddSponge ⟨1, 7, 5⟩) MAP_TREE_DEPTH

theorem aafi_steps2_length : aafiSteps2.length = MAP_TREE_DEPTH := slot1Path_length _ _ _
theorem aafi_steps2_pos : pathPos aafiSteps2 = 1 := slot1Path_pos _ _ _ (by decide)

theorem aafi_steps2_recompute (x : ℤ) :
    pathRecompute oddSponge x aafiSteps2
      = perfectRoot oddSponge MAP_TREE_DEPTH
          (padTo MAP_TREE_DEPTH [imtLeafHash oddSponge ⟨1, 7, 5⟩, x]) :=
  slot1Path_recompute _ _ MAP_TREE_DEPTH (by decide) x

theorem aafiR1_eq : aafiR1
    = perfectRoot oddSponge MAP_TREE_DEPTH
        (padTo MAP_TREE_DEPTH [imtLeafHash oddSponge ⟨1, 7, 5⟩]) := by
  show padImtRoot 5 oddSponge MAP_TREE_DEPTH [(1, 7)] = _
  rw [padImtRoot_unfold, bite_chain]

theorem bite_chain2 : (imtChainOf biteSent [(1, 7), (5, 2)]).map (imtLeafHash oddSponge)
    = [imtLeafHash oddSponge ⟨1, 7, 5⟩, imtLeafHash oddSponge ⟨5, 2, biteSent⟩] := rfl

theorem aafiNewRoot_eq : aafiNewRoot
    = perfectRoot oddSponge MAP_TREE_DEPTH (padTo MAP_TREE_DEPTH
        [imtLeafHash oddSponge ⟨1, 7, 5⟩, imtLeafHash oddSponge ⟨5, 2, biteSent⟩]) := by
  show padImtRoot biteSent oddSponge MAP_TREE_DEPTH [(1, 7), (5, 2)] = _
  rw [padImtRoot_unfold, bite_chain2]

theorem cons_pad_append :
    ([imtLeafHash oddSponge ⟨1, 7, 5⟩, padDigest] : List ℤ)
      = [imtLeafHash oddSponge ⟨1, 7, 5⟩] ++ [padDigest] := rfl

/-- **⚑ THE DEPLOYED AAFI FREE SLOT IS A PADDING CELL.** Gate (d1) pins `MAP_FREE_EMPTY` to `ZERO8`
and opens it at position `1`, which in a one-live-leaf `2^16` commitment holds the padding constant —
so the deployed AAFI append GROWS INTO THE PADDING stage 2b modelled, and the pre- and post-vectors
differ in exactly the one cell. -/
theorem aafi_free_slot_is_padding :
    padTo MAP_TREE_DEPTH ([imtLeafHash oddSponge ⟨1, 7, 5⟩] ++ [padDigest])
      = padTo MAP_TREE_DEPTH [imtLeafHash oddSponge ⟨1, 7, 5⟩] :=
  padTo_snoc_pad MAP_TREE_DEPTH _
    (by show 1 + 1 ≤ 2 ^ MAP_TREE_DEPTH; exact two_le_two_pow_depth)

theorem bite_aafi_row :
    AafiImtRowAt biteSent oddSponge MAP_TREE_DEPTH biteRoot aafiNewRoot aafiR1 5 2 1 7 biteSent := by
  refine ⟨biteHeap, biteSteps, aafiSteps2, biteHeap_ok, biteHeap_sz, rfl,
    bite_steps_length, aafi_steps2_length, ?_, bite_path_leaf 1 7 biteSent,
    by norm_num, by norm_num [biteSent], bite_path_leaf 1 7 5, ?_, ?_⟩
  · rw [bite_steps_pos, aafi_steps2_pos]; decide
  · rw [aafi_steps2_recompute, cons_pad_append, aafi_free_slot_is_padding, aafiR1_eq]
  · rw [aafi_steps2_recompute, aafiNewRoot_eq]

/-- **★ THE `.aafiInsert` LAW FIRES — the DOUBLE-SPEND TOOTH at the deployed padded commitment.**
An accepting AAFI row forces key `5` ABSENT from the pre-tree. -/
theorem bite_aafi_absence_fires :
    opensToMerkleS (padImtSchema biteSent) oddSponge MAP_TREE_DEPTH biteRoot 5 none :=
  aafiImtRow_forces_absence_of_good mapGood_inhabited biteSent MAP_TREE_DEPTH bite_aafi_row

/-- **★★ THE `.aafiInsert` TOOTH BITES — a PRESENT key has NO accepting AAFI row**, for any claimed
low leaf, any claimed intermediate root and any claimed post-root. -/
theorem bite_aafi_present_key_refused (newRoot R1 value lowAddr lowValue lowNext : ℤ) :
    ¬ AafiImtRowAt biteSent oddSponge MAP_TREE_DEPTH biteRoot newRoot R1 1 value lowAddr lowValue
        lowNext := fun hr =>
  opensToMerkleS_some_excludes_none_of_good (padImtTeeth biteSent)
    ⟨oddSponge_injective, oddSponge_padFree3⟩ MAP_TREE_DEPTH bite_read_fires.1
    (aafiImtRow_forces_absence_of_good mapGood_inhabited biteSent MAP_TREE_DEPTH hr)

/-- **★★ THE DEPLOYED AAFI ROW GROWS THE MAP, at `MAP_TREE_DEPTH = 16`.** Here the appended key `5`
is the new MAXIMUM, so the append-order layout and the sorted layout coincide and the row's post-root
IS the padded sorted commitment — the write denotation holds with the map one entry LARGER, which no
dense schema can express (`denseSchema_write_forces_key_present`). ⚠ §7b proves the coincidence does
NOT generalise: when the appended key is interior, the deployed post-root is a DIFFERENT felt from
any schema's commitment of the same logical map. -/
theorem bite_aafi_grows :
    writesToMerkleS (padImtSchema biteSent) oddSponge MAP_TREE_DEPTH biteRoot 5 2 aafiNewRoot
    ∧ (5 : ℤ) ∉ Heap.keys biteHeap
    ∧ (Heap.set biteHeap 5 2).length = biteHeap.length + 1 := by
  have hfresh : (5 : ℤ) ∉ Heap.keys biteHeap := by decide
  have hset : Heap.set biteHeap 5 2 = [(1, 7), (5, 2)] := by norm_num [biteHeap, Heap.set]
  refine ⟨⟨biteHeap, biteHeap_ok, biteHeap_sz, ?_, rfl, ?_⟩, hfresh,
    Heap.length_set_fresh biteHeap 5 2 hfresh⟩
  · show (Heap.set biteHeap 5 2).length ≤ 2 ^ MAP_TREE_DEPTH
    rw [hset]
    show 2 ≤ 2 ^ MAP_TREE_DEPTH
    exact two_le_two_pow_depth
  · show aafiNewRoot = padImtRoot biteSent oddSponge MAP_TREE_DEPTH (Heap.set biteHeap 5 2)
    rw [hset]
    rfl

end Bite16

/-! ## §10 — AXIOM HYGIENE. -/

#assert_axioms imtChainOf_getElem?
#assert_axioms imtChainOf_set
#assert_axioms padTo_set
#assert_axioms padTo_getElem?
#assert_axioms padTo_succ_split
#assert_axioms padTo_snoc_pad
#assert_axioms leftPadPath_recompute
#assert_axioms slot1Path_recompute
#assert_axioms openResid_refuted
#assert_axioms mapGood_inhabited
#assert_axioms padOpen_binds_or_resid
#assert_axioms padImt_heap_binds
#assert_axioms unshared_pointer_write_is_not_a_relink
#assert_axioms readImtGates_opens_or_resid
#assert_axioms writeImtGates_writes_or_resid
#assert_axioms readImtRow_opens_of_good
#assert_axioms writeImtRow_writes_of_good
#assert_axioms insertImtGates_post_opens_or_resid
#assert_axioms insertImtRow_post_opens_of_good
#assert_axioms insertImtGates_cannot_force_the_write_denotation
#assert_axioms reconcileGates_insert_forces_key_present
#assert_axioms reconcileGates_insert_unsat_at_fresh_key
#assert_axioms aafiImtGates_force_absence_or_resid
#assert_axioms aafiImtRow_forces_absence_of_good
#assert_axioms appendOrderRoot_binds
#assert_axioms no_schema_commits_the_append_order_layout
#assert_axioms aafi_post_is_not_the_sorted_commit
#assert_axioms denseSchema_write_forces_key_present
#assert_axioms narrow_write_forces_key_present
#assert_axioms imtSchema_write_forces_key_present
#assert_axioms padImt_write_admits_growth
#assert_axioms bite_read_row
#assert_axioms bite_read_fires
#assert_axioms bite_read_forged_value_refused
#assert_axioms bite_write_fires
#assert_axioms bite_write_frozen_root_refused
#assert_axioms bite_insert_post_opens
#assert_axioms bite_insert_preroot_is_unforced
#assert_axioms aafi_free_slot_is_padding
#assert_axioms bite_aafi_row
#assert_axioms bite_aafi_absence_fires
#assert_axioms bite_aafi_present_key_refused
#assert_axioms bite_aafi_grows

end Dregg2.Circuit.MapKindImtGates
