/-
# `Dregg2.Circuit.WholeImageFoldRealization` — the whole-image fold chip's ACTUAL correspondent,
  and the no-extra-cells cone RE-PROVED over it.

## The finding this file repairs (measured 2026-07-28; `file:line` on both sides)

`circuit/src/whole_image_fold.rs` — the WHOLE-IMAGE FOLD CHIP — presented itself as the in-circuit
realization of the `hpin` hypothesis carried by `Dregg2.Exec.UniversalBridge`'s

  * `crossCellRead_whole_image`
  * `crossCellRead_whole_image_sem`
  * `cross_cell_read_no_extra_cell`
  * `cross_cell_read_whole_image_teeth`

namely `hpin : MapMerkleRoot.mapRoot hash d boundaryHeap = publishedRoot`, and its banner named the
folded object as "`heap_root.rs::CanonicalHeapTree::root`, modelled byte-identically by
`MapMerkleRoot.mapRoot`". THREE independent things are wrong with that, each fatal on its own.
(SYMBOLS, not `file:line` — `heap_root.rs` moves weekly and a line-keyed finding here decays in days.)

  1. **Leaf ARITY.** `MapMerkleRoot.mapRoot` folds arity-2 leaves
     `Heap.leafOf hash (a, v) = hash [a, v]`. The deployed tree has folded arity-3 INDEXED-Merkle
     leaves `hash [addr, value, next_addr]` since 2026-07-12 (`919b2b0b8d`;
     `circuit/src/heap_root.rs`'s `HEAP_LEAF_ARITY = 3` and `HeapLeaf::preimage`). `mapRoot`'s own
     doc-comment retracts the byte-identity claim, and `MapReconcileImtRepoint.imtRoot_ne_mapRoot`
     proves the two are DIFFERENT commitments over the same logical map.
  2. **DIGEST WIDTH — and the chip does not compute `CanonicalHeapTree::root` either.**
     `whole_boundary_fold` computes `CanonicalHeapTree8::new(..).root8()` — the 8-FELT tree, leaves
     `HeapLeaf::digest8` (arity-3, all eight lanes squeezed), nodes `heap_node8` (the arity-16 chip
     absorb). `mapRoot` is `ℤ`-valued; the chip's published root is an eight-lane PI GROUP
     (`WIF_PI_PUBLISHED_ROOT`). There is no `hpin` OF THE THEOREMS' SHAPE available at the chip's
     public input at all — the mismatch is not a drifted constant, it is a type wall.
  3. **OCCUPANCY.** `mapRoot` folds the DENSE `2 ^ d` leaf vector. The deployed tree prepends ONE MIN
     sentinel (`min_sentinel_leaf`), relinks the successor pointers (`relink_next_addrs`) and
     ZERO-pads a sparse prefix to `2 ^ d`.

So the `hpin` the chip realizes was never the `hpin` the theorems take, and the no-extra-cells
argument did not connect to the chip. This file supplies the object the chip ACTUALLY folds and
re-proves the cone over it, so the realization claim has a referent.

## What is authored here

  * **§1** `padImtRoot8` — the deployed-shape 8-felt padded IMT root: relink (`linkHeap`), arity-3
    `heapLeafDigest8` leaves, ZERO-digest padding to `2 ^ d`, `node8` perfect-tree fold. Plus
    `wholeBoundaryFold8`, which prepends the MIN sentinel exactly as `CanonicalHeapTree8::new` does,
    so it is the correspondent of `whole_boundary_fold` at the level of DECLARED cells.
  * **§2** the padding lemma at `Digest8` and `padImtRoot8_binds_or_ghost_or_collides` — the binding,
    with NO floor: two heaps publishing the same deployed-shape root are EQUAL, or one presents a
    live leaf digest equal to the padding constant, or the deployed chip genuinely collides at the
    ONE pair a total extractor hands back.
  * **§3** the whole-image cone re-proved at the deployed shape: `crossCellRead_wholeImage8`,
    `_sem8`, `cross_cell_read_no_extra_cell8`, `_teeth8`, and the sentinel-level (chip-level) forms
    over `wholeBoundaryFold8`.
  * **§4** THE ARITY WALL AT THE CHIP'S OWN WIDTH — `padImtRoot8_ne_arity2Root8`: the arity-2 fold,
    lifted to `Digest8` so it is type-comparable, is NOT the deployed-shape root on a concrete heap.
    The 8-felt shadow of `imtRoot_ne_mapRoot`, and the reason this is a REPAIR and not a rename.
  * **§5** the residual kit: both residuals REFUTABLE (at an injective / pad-free chip) and both
    SATISFIABLE (at `badHeapScheme8`), plus `honestScheme8` — a chip at which BOTH are discharged, so
    the cone fires with ZERO residual hypotheses left and the conclusion is not vacuous.

## Honest scope — three named residuals, none claimed closed

  1. **SPARSE ≡ DENSE-PADDED.** `CanonicalHeapTree8::new` folds only the non-empty prefix per level,
     reading `heap_empty_subtree_root_8(level)` for an all-padding sibling. This model folds the
     DENSE zero-padded vector. The two agree by the contiguous-prefix argument the Rust builder rests
     on, and this file takes the dense-padded view — the SAME modelling choice `padTo` already makes
     at `ℤ` (`MapPaddedDenotation.padTo`, citing `CanonicalHeapTree::new`). NOT PROVED here; it is
     MEASURED on concrete instances by
     `circuit/tests/whole_image_fold_lean_correspondent.rs::deployed_tree_is_the_lean_denotation_shape`,
     which folds the dense zero-padded vector and compares it to the deployed sparse builder. A
     measurement over five views at four depths is not a proof, and this residual stays open.
  2. **NO BYTE DIFFERENTIAL.** `Heap8Scheme.chipAbsorb8` has no KAT-faithful Poseidon2 inhabitant in
     Lean, and there is no `@[export]` for any heap root — nothing crosses the FFI. This is a
     SHAPE-faithful model, and shape is exactly what the arity/width finding was about. The Rust-side
     tooth against re-drift is `circuit/tests/whole_image_fold_lean_correspondent.rs`.
  3. **THE CHIP IS STILL HAND-WRITTEN RUST AIR** (`circuit-prove/tests/law1_enforcement_gate.rs:704`
     ledgers 38 sites) and has ZERO production callers (`baseline/production-callers.tsv` classes its
     three verifiers `THEATRE`). Nothing here promotes it; this file only gives its stated
     correspondence a true referent.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; sorry-free; no `native_decide`; no
`decide` over any `Encodable.encode` value. NEW file; every import read-only; no deployed descriptor,
emit, JSON or Rust byte is touched by this module.
-/
import Dregg2.Circuit.MapPaddedDenotation

namespace Dregg2.Circuit.WholeImageFoldRealization

open Dregg2.Substrate
open Dregg2.Circuit.DeployedCapTree (Digest8 Coll8 Compress8CR)
open Dregg2.Circuit.DeployedCapTree.Cap8Scheme (coll8_refutable_of_injective)
open Dregg2.Circuit.DeployedHeapTree (Heap8Scheme)
open Dregg2.Circuit.DeployedHeapTree.Heap8Scheme (heapLeafDigest8 heapLeafColl8Find)
open Dregg2.Circuit.DeployedHeapTree.Reference8 (badHeapScheme8)
open Dregg2.Circuit.MapMerkleRoot (zeroDigest8 perfectRoot8 perfectRoot8Find
  perfectRoot8_binds_or_collides mapLeaf8Find map_leaf8_binds_or_collides
  linkHeap linkHeap_length linkHeap_injective SENTINEL_MAX8)

variable (S8 : Heap8Scheme)

/-! ## §1 — THE OBJECT THE CHIP ACTUALLY FOLDS. -/

/-- The MIN sentinel address — `heap_root.rs:71` `SENTINEL_MIN: BabyBear = ZERO`. The deployed tree
stores it as a real leaf (`HEAP_SENTINEL_LEAVES = 1`); the MAX sentinel survives only as the terminal
`next_addr` pointer, which `linkHeap` installs as `SENTINEL_MAX8`. -/
def SENTINEL_MIN8 : ℤ := 0

/-- **`padDigest8`** — the 8-felt padding / empty-leaf marker: `heap_root.rs:784`'s `HEAP_ZERO8`, the
all-zero digest that `heap_empty_subtree_root_8(0)` is. -/
def padDigest8 : Digest8 := zeroDigest8

/-- **`padTo8 d L`** — the deployed occupancy discipline at 8-felt width: the real leaf digests are a
contiguous sorted PREFIX and every position `≥ L.length` holds `padDigest8`. The `Digest8` twin of
`MapPaddedDenotation.padTo`. -/
def padTo8 (d : Nat) (L : List Digest8) : List Digest8 :=
  L ++ List.replicate (2 ^ d - L.length) padDigest8

theorem padTo8_length {d : Nat} {L : List Digest8} (h : L.length ≤ 2 ^ d) :
    (padTo8 d L).length = 2 ^ d := by
  simp only [padTo8, List.length_append, List.length_replicate]
  omega

/-- **A FULL tree pads to itself** — the padded fold EXTENDS the dense one rather than replacing it. -/
theorem padTo8_dense {d : Nat} {L : List Digest8} (h : L.length = 2 ^ d) : padTo8 d L = L := by
  simp only [padTo8, h, Nat.sub_self, List.replicate_zero, List.append_nil]

/-- **`PadHit8 L`** — a position of the LIVE prefix already holds the padding constant. -/
def PadHit8 (L : List Digest8) : Prop := padDigest8 ∈ L

/-- **★ THE PADDING LEMMA at `Digest8`.** Two zero-padded digest vectors that are EQUAL force their
live prefixes equal UNLESS one prefix already contains the padding constant. Purely combinatorial:
no chip, no depth, no length hypothesis. The `Digest8` twin of
`MapPaddedDenotation.append_replicate_eq_or_hit`. -/
theorem append_replicate_eq_or_hit8 : ∀ (L₁ L₂ : List Digest8) (k₁ k₂ : Nat),
    L₁ ++ List.replicate k₁ padDigest8 = L₂ ++ List.replicate k₂ padDigest8 →
    L₁ = L₂ ∨ PadHit8 L₁ ∨ PadHit8 L₂ := by
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
        exact Or.inr (Or.inr (by rw [PadHit8, h.1]; simp))
  | cons a L₁' ih =>
    intro L₂ k₁ k₂ h
    cases L₂ with
    | nil =>
      cases k₂ with
      | zero => simp at h
      | succ m =>
        rw [List.nil_append, List.replicate_succ, List.cons_append, List.cons.injEq] at h
        exact Or.inr (Or.inl (by rw [PadHit8, ← h.1]; simp))
    | cons b L₂' =>
      rw [List.cons_append, List.cons_append, List.cons.injEq] at h
      obtain ⟨hab, htail⟩ := h
      rcases ih L₂' k₁ k₂ htail with heq | hh₁ | hh₂
      · exact Or.inl (by rw [hab, heq])
      · exact Or.inr (Or.inl (List.mem_cons_of_mem _ hh₁))
      · exact Or.inr (Or.inr (List.mem_cons_of_mem _ hh₂))

theorem padTo8_eq_or_hit (d : Nat) {L₁ L₂ : List Digest8} (h : padTo8 d L₁ = padTo8 d L₂) :
    L₁ = L₂ ∨ PadHit8 L₁ ∨ PadHit8 L₂ :=
  append_replicate_eq_or_hit8 L₁ L₂ _ _ h

/-- One padding position IS a `PadHit8`, so the ghost branch is REACHABLE. -/
theorem padHit8_singleton : PadHit8 [padDigest8] := by simp [PadHit8]

/-- **⚑ `padImtRoot8 S8 d h` — THE DEPLOYED-SHAPE MAP COMMITMENT AT THE DEPLOYED WIDTH, and the
object `circuit/src/whole_image_fold.rs::whole_boundary_fold` computes.** Relink the successor
pointers (`linkHeap` ≡ `relink_next_addrs`, terminal `SENTINEL_MAX8`), digest each linked leaf at
arity 3 through the eight-lane chip (`heapLeafDigest8` ≡ `HeapLeaf::digest8`), ZERO-pad the digest
vector to `2 ^ d`, and fold the perfect `node8` tree (`perfectRoot8` ≡ `heap_node8`).

This is `MapPaddedDenotation.padImtRoot` moved from `ℤ` to `Digest8` — the SAME shape move, at the
width the deployment actually commits (`cell/src/state.rs:311` `heap_root : Faithful8`,
absorbed into the rotated commitment at `HEAP_ROOT_GROUP`, `cell/src/commitment.rs:1229`). -/
def padImtRoot8 (d : Nat) (h : Heap.FeltHeap) : Digest8 :=
  perfectRoot8 S8 d (padTo8 d ((linkHeap h).map (heapLeafDigest8 S8)))

/-- **`sentinelHeap h`** — the MIN-sentinel prepend `CanonicalHeapTree8::new` performs before sorting
(`heap_root.rs:1011`). Callers hand the tree their DECLARED cells; the sentinel is the builder's.

⚠ **MODELLING PRECONDITION, stated rather than assumed.** The Rust builder SORTS and DEDUPS by
address; this model takes `h` already in sorted, duplicate-free order and with every declared address
strictly above `SENTINEL_MIN8`, so that `(SENTINEL_MIN8, 0) :: h` is the builder's post-sort list.
That precondition is NOT a hypothesis of the theorems below — they bind the LIST, and `Heap.get`
needs no order — but it IS what makes `wholeBoundaryFold8` the correspondent of
`whole_boundary_fold` rather than merely a similar fold. `build_whole_image_fold` enforces the
duplicate-freeness on the Rust side and refuses otherwise; the sort and the address bound are
enforced by `CanonicalHeapTree8::new`. -/
def sentinelHeap (h : Heap.FeltHeap) : Heap.FeltHeap := (SENTINEL_MIN8, 0) :: h

theorem sentinelHeap_injective {h₁ h₂ : Heap.FeltHeap} (h : sentinelHeap h₁ = sentinelHeap h₂) :
    h₁ = h₂ := by
  simpa [sentinelHeap] using h

theorem sentinelHeap_length (h : Heap.FeltHeap) : (sentinelHeap h).length = h.length + 1 := rfl

/-- **⚑ `wholeBoundaryFold8 S8 d h` — THE CORRESPONDENT OF `whole_boundary_fold`**, at the level of
DECLARED boundary cells: prepend the MIN sentinel, then take the deployed-shape padded IMT root. This
is the `hpin` object the whole-image fold chip pins its published-root PI group to. -/
def wholeBoundaryFold8 (d : Nat) (h : Heap.FeltHeap) : Digest8 :=
  padImtRoot8 S8 d (sentinelHeap h)

theorem wholeBoundaryFold8_eq (d : Nat) (h : Heap.FeltHeap) :
    wholeBoundaryFold8 S8 d h = padImtRoot8 S8 d (sentinelHeap h) := rfl

/-! ## §2 — THE BINDING, with NO floor and two NAMED residuals. -/

/-- **`PadGhost8 S8 h`** — a LIVE arity-3 leaf digest of `h` equals the padding constant. The
occupancy ghost: the deployed builder never checks that no real leaf hashes to `HEAP_ZERO8`. -/
def PadGhost8 (h : Heap.FeltHeap) : Prop :=
  PadHit8 ((linkHeap h).map (heapLeafDigest8 S8))

/-- The chip-level side condition that kills the ghost: the padding constant has no arity-3 IMT leaf
preimage under the eight-lane absorb. -/
def PadFree8 : Prop := ∀ e : ℤ × ℤ × ℤ, heapLeafDigest8 S8 e ≠ padDigest8

theorem padGhost8_refuted (hpf : PadFree8 S8) (h : Heap.FeltHeap) : ¬ PadGhost8 S8 h := by
  intro hmem
  rw [PadGhost8, PadHit8, List.mem_map] at hmem
  obtain ⟨e, _, he⟩ := hmem
  exact hpf e he

/-- **THE EXTRACTOR** — the SINGLE pair the whole deployed-shape peel hands back. Run the `node8`
perfect-tree descent over the two padded digest vectors; if that found a genuine chip collision, that
is the answer. Otherwise the descent has already forced the two DIGEST VECTORS equal, so any
collision is at the arity-3 leaf absorb and the linked-leaf scan supplies the pair. Total, decidable,
and independent of anything assumed about the chip. -/
def padImtRoot8Find (d : Nat) (h₁ h₂ : Heap.FeltHeap) : List ℤ × List ℤ :=
  if Coll8 S8.chipAbsorb8
      (perfectRoot8Find S8 d (padTo8 d ((linkHeap h₁).map (heapLeafDigest8 S8)))
                             (padTo8 d ((linkHeap h₂).map (heapLeafDigest8 S8))))
  then perfectRoot8Find S8 d (padTo8 d ((linkHeap h₁).map (heapLeafDigest8 S8)))
                             (padTo8 d ((linkHeap h₂).map (heapLeafDigest8 S8)))
  else mapLeaf8Find S8 (linkHeap h₁) (linkHeap h₂)

/-- **`PadImtRoot8Coll S8 d h₁ h₂`** — the pair `padImtRoot8Find` RETURNS on this heap equivocation is
a genuine collision of the deployed arity-16 chip.

Deliberately NOT `∃ a b, chip collides`: at deployed BabyBear parameters that existence claim is
UNCONDITIONALLY TRUE by pigeonhole (`VacuitySweepTeeth.compress8CR_false_babyBear`), so a disjunct of
that shape would carry no more content than `True`. This one is about the SPECIFIC pair a total
extractor hands back, and it is REFUTABLE (`padImtRoot8Coll_refutable_of_injective`). -/
def PadImtRoot8Coll (d : Nat) (h₁ h₂ : Heap.FeltHeap) : Prop :=
  Coll8 S8.chipAbsorb8 (padImtRoot8Find S8 d h₁ h₂)

/-- **★★ THE DEPLOYED-SHAPE 8-FELT ROOT BINDS THE HEAP — UNCONDITIONALLY, up to TWO named
residuals.** Arity-3 IMT leaves, the deployed relink, the deployed SPARSE occupancy (`≤ 2 ^ d`), zero
padding, eight-lane digests. No floor at the node, none at the leaf. This is the theorem the
whole-image cone below is built from. -/
theorem padImtRoot8_binds_or_ghost_or_collides (d : Nat) {h₁ h₂ : Heap.FeltHeap}
    (hl₁ : h₁.length ≤ 2 ^ d) (hl₂ : h₂.length ≤ 2 ^ d)
    (heq : padImtRoot8 S8 d h₁ = padImtRoot8 S8 d h₂) :
    h₁ = h₂ ∨ PadGhost8 S8 h₁ ∨ PadGhost8 S8 h₂ ∨ PadImtRoot8Coll S8 d h₁ h₂ := by
  by_cases hif : Coll8 S8.chipAbsorb8
      (perfectRoot8Find S8 d (padTo8 d ((linkHeap h₁).map (heapLeafDigest8 S8)))
                             (padTo8 d ((linkHeap h₂).map (heapLeafDigest8 S8))))
  · refine Or.inr (Or.inr (Or.inr ?_))
    show Coll8 S8.chipAbsorb8 (padImtRoot8Find S8 d h₁ h₂)
    rw [padImtRoot8Find, if_pos hif]
    exact hif
  · have hlen₁ : (padTo8 d ((linkHeap h₁).map (heapLeafDigest8 S8))).length = 2 ^ d :=
      padTo8_length (by rw [List.length_map, linkHeap_length]; exact hl₁)
    have hlen₂ : (padTo8 d ((linkHeap h₂).map (heapLeafDigest8 S8))).length = 2 ^ d :=
      padTo8_length (by rw [List.length_map, linkHeap_length]; exact hl₂)
    rcases perfectRoot8_binds_or_collides S8 d hlen₁ hlen₂ heq with hpad | hc
    · rcases padTo8_eq_or_hit d hpad with hL | hh₁ | hh₂
      · rcases map_leaf8_binds_or_collides S8 _ _ hL with hlink | hcl
        · exact Or.inl (linkHeap_injective hlink)
        · refine Or.inr (Or.inr (Or.inr ?_))
          show Coll8 S8.chipAbsorb8 (padImtRoot8Find S8 d h₁ h₂)
          rw [padImtRoot8Find, if_neg hif]
          exact hcl
      · exact Or.inr (Or.inl hh₁)
      · exact Or.inr (Or.inr (Or.inl hh₂))
    · exact absurd hc hif

/-! ## §3 — THE WHOLE-IMAGE (no-extra-cells) CONE, RE-PROVED AT THE DEPLOYED SHAPE.

Statement-for-statement the `UniversalBridge` §6.5b cone, with `mapRoot hash d` replaced by the
object the chip folds and the single `Poseidon2SpongeCR` floor replaced by the two named residuals
this width actually admits. -/

section WholeImage

variable (d : Nat)

/-- **`crossCellRead_wholeImage8` — the committed peer heap IS the declared whole-boundary view (no
extra cells), AT THE DEPLOYED SHAPE.** If the published peer root is the deployed-shape padded IMT
root of peer B's committed field heap (`hcommit`) AND equals that of the declared whole-boundary view
(`hpin` — the pin the fold chip forces), then the committed peer heap EQUALS that boundary view: a
single extra or altered leaf moves the root, so the peer can hold NOTHING the boundary never
declared.

The deployed-shape replacement for `UniversalBridge.crossCellRead_whole_image`, whose `hpin` is at
the arity-2 `mapRoot` and therefore has no referent at this chip's published-root PI group. -/
theorem crossCellRead_wholeImage8 {published : Digest8} {peerHeap boundaryHeap : Heap.FeltHeap}
    (hpl : peerHeap.length ≤ 2 ^ d) (hbl : boundaryHeap.length ≤ 2 ^ d)
    (hgp : ¬ PadGhost8 S8 peerHeap) (hgb : ¬ PadGhost8 S8 boundaryHeap)
    (hnc : ¬ PadImtRoot8Coll S8 d peerHeap boundaryHeap)
    (hcommit : padImtRoot8 S8 d peerHeap = published)
    (hpin : padImtRoot8 S8 d boundaryHeap = published) :
    peerHeap = boundaryHeap := by
  rcases padImtRoot8_binds_or_ghost_or_collides S8 d hpl hbl (hcommit.trans hpin.symm) with
    h | h | h | h
  · exact h
  · exact absurd h hgp
  · exact absurd h hgb
  · exact absurd h hnc

/-- **`crossCellRead_wholeImage8_sem` — the committed peer heap agrees with the declared image at
EVERY address.** Declared cells open to their declared value, and every address OFF the declared list
is ABSENT in the peer heap. -/
theorem crossCellRead_wholeImage8_sem {published : Digest8} {peerHeap boundaryHeap : Heap.FeltHeap}
    {init : ℤ → Option ℤ} {as : List ℤ}
    (hpl : peerHeap.length ≤ 2 ^ d) (hbl : boundaryHeap.length ≤ 2 ^ d)
    (hgp : ¬ PadGhost8 S8 peerHeap) (hgb : ¬ PadGhost8 S8 boundaryHeap)
    (hnc : ¬ PadImtRoot8Coll S8 d peerHeap boundaryHeap)
    (hcommit : padImtRoot8 S8 d peerHeap = published)
    (hpin : padImtRoot8 S8 d boundaryHeap = published)
    (hbsem : ∀ k, Heap.get boundaryHeap k = if k ∈ as then init k else none) :
    ∀ k, Heap.get peerHeap k = if k ∈ as then init k else none := by
  intro k
  rw [crossCellRead_wholeImage8 S8 d hpl hbl hgp hgb hnc hcommit hpin]
  exact hbsem k

/-- **`cross_cell_read_no_extra_cell8` — a peer cell OFF the declared boundary is ABSENT.** The
no-extra-cells punch the per-cell subset view cannot reach, at the shape the chip folds: under the
whole-boundary fold pin, any never-declared address is `none` in the committed peer heap, so a
cross-cell read returning `none` there is SOUND. -/
theorem cross_cell_read_no_extra_cell8 {published : Digest8} {peerHeap boundaryHeap : Heap.FeltHeap}
    {init : ℤ → Option ℤ} {as : List ℤ} {k : ℤ}
    (hpl : peerHeap.length ≤ 2 ^ d) (hbl : boundaryHeap.length ≤ 2 ^ d)
    (hgp : ¬ PadGhost8 S8 peerHeap) (hgb : ¬ PadGhost8 S8 boundaryHeap)
    (hnc : ¬ PadImtRoot8Coll S8 d peerHeap boundaryHeap)
    (hcommit : padImtRoot8 S8 d peerHeap = published)
    (hpin : padImtRoot8 S8 d boundaryHeap = published)
    (hbsem : ∀ k, Heap.get boundaryHeap k = if k ∈ as then init k else none)
    (hk : k ∉ as) :
    Heap.get peerHeap k = none := by
  have h := crossCellRead_wholeImage8_sem S8 d hpl hbl hgp hgb hnc hcommit hpin hbsem k
  rwa [if_neg hk] at h

/-- **`cross_cell_read_wholeImage8_teeth` — the no-extra-cells REFUSAL.** A committed peer heap that
DIFFERS from the declared whole-boundary view CANNOT share the deployed-shape fold root. The
two-valued tooth showing the pin is not vacuous — the contrapositive of `crossCellRead_wholeImage8`. -/
theorem cross_cell_read_wholeImage8_teeth {peerHeap boundaryHeap : Heap.FeltHeap}
    (hpl : peerHeap.length ≤ 2 ^ d) (hbl : boundaryHeap.length ≤ 2 ^ d)
    (hgp : ¬ PadGhost8 S8 peerHeap) (hgb : ¬ PadGhost8 S8 boundaryHeap)
    (hnc : ¬ PadImtRoot8Coll S8 d peerHeap boundaryHeap)
    (hne : peerHeap ≠ boundaryHeap) :
    padImtRoot8 S8 d peerHeap ≠ padImtRoot8 S8 d boundaryHeap := fun heq =>
  hne (crossCellRead_wholeImage8 S8 d hpl hbl hgp hgb hnc rfl heq.symm)

/-! ### §3b — THE CHIP-LEVEL FORMS, over `wholeBoundaryFold8` (declared cells in, sentinel supplied
by the builder). These are the statements a caller of `whole_boundary_fold` can read directly. -/

/-- The chip-level no-extra-cells punch: the argument of `whole_boundary_fold` is the DECLARED cell
list, and the sentinel is the builder's. -/
theorem cross_cell_read_no_extra_cell8_chip {published : Digest8}
    {peerCells boundaryCells : Heap.FeltHeap} {init : ℤ → Option ℤ} {as : List ℤ} {k : ℤ}
    (hpl : peerCells.length + 1 ≤ 2 ^ d) (hbl : boundaryCells.length + 1 ≤ 2 ^ d)
    (hgp : ¬ PadGhost8 S8 (sentinelHeap peerCells))
    (hgb : ¬ PadGhost8 S8 (sentinelHeap boundaryCells))
    (hnc : ¬ PadImtRoot8Coll S8 d (sentinelHeap peerCells) (sentinelHeap boundaryCells))
    (hcommit : wholeBoundaryFold8 S8 d peerCells = published)
    (hpin : wholeBoundaryFold8 S8 d boundaryCells = published)
    (hbsem : ∀ k, Heap.get boundaryCells k = if k ∈ as then init k else none)
    (hk : k ∉ as) :
    Heap.get peerCells k = none := by
  have hpeq : sentinelHeap peerCells = sentinelHeap boundaryCells :=
    crossCellRead_wholeImage8 S8 d
      (by rw [sentinelHeap_length]; exact hpl) (by rw [sentinelHeap_length]; exact hbl)
      hgp hgb hnc hcommit hpin
  have := sentinelHeap_injective hpeq
  rw [this]
  have h := hbsem k
  rwa [if_neg hk] at h

/-- The chip-level REFUSAL tooth: two DIFFERENT declared cell lists cannot fold to the same published
root. This is what `verify_whole_image_fold`'s `PiBinding{Last}` refusal is supposed to mean. -/
theorem whole_boundary_fold8_teeth {peerCells boundaryCells : Heap.FeltHeap}
    (hpl : peerCells.length + 1 ≤ 2 ^ d) (hbl : boundaryCells.length + 1 ≤ 2 ^ d)
    (hgp : ¬ PadGhost8 S8 (sentinelHeap peerCells))
    (hgb : ¬ PadGhost8 S8 (sentinelHeap boundaryCells))
    (hnc : ¬ PadImtRoot8Coll S8 d (sentinelHeap peerCells) (sentinelHeap boundaryCells))
    (hne : peerCells ≠ boundaryCells) :
    wholeBoundaryFold8 S8 d peerCells ≠ wholeBoundaryFold8 S8 d boundaryCells := fun heq =>
  hne (sentinelHeap_injective
    (crossCellRead_wholeImage8 S8 d
      (by rw [sentinelHeap_length]; exact hpl) (by rw [sentinelHeap_length]; exact hbl)
      hgp hgb hnc rfl heq.symm))

end WholeImage

/-! ## §4 — ⚑ THE ARITY WALL AT THE CHIP'S OWN WIDTH.

`MapReconcileImtRepoint.imtRoot_ne_mapRoot` proves the arity-3 IMT root is never the arity-2
`mapRoot` at `ℤ`. At `Digest8` the two are not even the same TYPE as stated (`mapRoot : ℤ`), which is
already a wall — but a type wall is easy to mistake for a mere encoding difference. So the arity-2
fold is LIFTED to `Digest8` here, where it IS type-comparable, and shown to differ from the deployed
shape on a concrete heap. This is why re-pointing the theorems is a repair and not a rename: the two
objects genuinely disagree, at the chip's own width, with no floor assumed. -/

/-- The arity-2 leaf fold at 8-felt width: `mapRoot`'s shape (`hash [addr, value]`, no successor
pointer) transported to `Digest8` so it is comparable with `padImtRoot8`. Authored HERE and used ONLY
by §4 — it is not a deployed object and nothing else may consume it. -/
def arity2Root8 (d : Nat) (h : Heap.FeltHeap) : Digest8 :=
  perfectRoot8 S8 d (padTo8 d (h.map (fun e => S8.chipAbsorb8 [e.1, e.2])))

/-- **`honestChipAbsorb8`** — an INJECTIVE, PAD-FREE reference chip: `Encodable.encode` shifted off
zero. Not a Poseidon2 and not claimed to be one; its job is to make both residual branches CONCRETELY
discharged so §4's separation and §5's non-vacuity witness carry content. -/
def honestChipAbsorb8 (xs : List ℤ) : Digest8 := fun _ => ((Encodable.encode xs : ℕ) : ℤ) + 1

theorem honestChip8_CR : Compress8CR honestChipAbsorb8 := by
  intro a b h
  have h0 := congrFun h 0
  unfold honestChipAbsorb8 at h0
  have : ((Encodable.encode a : ℕ) : ℤ) = ((Encodable.encode b : ℕ) : ℤ) := by omega
  exact Encodable.encode_injective (by exact_mod_cast this)

/-- The reference scheme both §4 and §5 land at. -/
def honestScheme8 : Heap8Scheme := ⟨honestChipAbsorb8⟩

theorem honestScheme8_chip : honestScheme8.chipAbsorb8 = honestChipAbsorb8 := rfl

theorem honestScheme8_padFree : PadFree8 honestScheme8 := by
  intro e hcon
  have h0 := congrFun hcon 0
  simp only [heapLeafDigest8, honestScheme8_chip, honestChipAbsorb8, padDigest8, zeroDigest8] at h0
  have hnn : (0 : ℤ) ≤ ((Encodable.encode [e.1, e.2.1, e.2.2] : ℕ) : ℤ) := Int.natCast_nonneg _
  omega

/-- **⚑ THE SEPARATION, at the chip's own width and with NO floor.** On a one-cell heap at depth 0
the deployed-shape root (arity-3, the successor pointer INSIDE the digest) is NOT the arity-2 fold.
The `Digest8` shadow of `MapReconcileImtRepoint.imtRoot_ne_mapRoot`, and the exact statement that
makes `hpin : mapRoot hash d boundaryHeap = publishedRoot` the WRONG hypothesis for this chip. -/
theorem padImtRoot8_ne_arity2Root8 :
    padImtRoot8 honestScheme8 0 [(1, 1)] ≠ arity2Root8 honestScheme8 0 [(1, 1)] := by
  intro hcon
  -- Both sides reduce definitionally to a single chip absorb: the deployed shape absorbs the
  -- arity-3 LINKED leaf `[addr, value, next_addr]`, the arity-2 fold absorbs `[addr, value]`.
  have hc : honestChipAbsorb8 [1, 1, SENTINEL_MAX8] = honestChipAbsorb8 [1, 1] := hcon
  have hlist : ([1, 1, SENTINEL_MAX8] : List ℤ) = ([1, 1] : List ℤ) := honestChip8_CR _ _ hc
  simp at hlist

/-! ## §5 — THE RESIDUAL KIT: both branches REFUTABLE, both SATISFIABLE, and one scheme where the
cone fires with NOTHING left over. -/

/-- **REFUTABLE (the canary).** At an injective chip no extracted pair is a collision, so the
collision disjunct is not a free pass — the binding half does the work. -/
theorem padImtRoot8Coll_refutable_of_injective (hCR : Compress8CR S8.chipAbsorb8)
    (d : Nat) (h₁ h₂ : Heap.FeltHeap) : ¬ PadImtRoot8Coll S8 d h₁ h₂ :=
  coll8_refutable_of_injective hCR _

theorem honest_padImtRoot8Coll_refuted (d : Nat) (h₁ h₂ : Heap.FeltHeap) :
    ¬ PadImtRoot8Coll honestScheme8 d h₁ h₂ :=
  padImtRoot8Coll_refutable_of_injective honestScheme8 honestChip8_CR d h₁ h₂

theorem honest_padGhost8_refuted (h : Heap.FeltHeap) : ¬ PadGhost8 honestScheme8 h :=
  padGhost8_refuted honestScheme8 honestScheme8_padFree h

/-- **SATISFIABLE (the other canary).** At the colliding chip the ghost branch is genuinely
INHABITED: every live leaf digest IS the padding constant, so `padGhost8_refuted`'s side condition is
not free. -/
theorem badHeapScheme8_padGhost8 : PadGhost8 badHeapScheme8 [(1, 1)] :=
  List.Mem.head _

/-- **SATISFIABLE (the collision canary).** At the colliding chip the extracted pair on two distinct
one-cell heaps IS a genuine collision, so the collision disjunct of
`padImtRoot8_binds_or_ghost_or_collides` is genuinely reachable. -/
theorem badHeapScheme8_padImtRoot8Coll : PadImtRoot8Coll badHeapScheme8 0 [(1, 1)] [(2, 2)] := by
  -- At depth 0 the tree descent hands back `([], [])`, which is never a collision, so the extractor
  -- falls through to the LEAF scan — and there the two arity-3 IMT blocks genuinely collide.
  have hleaf : Coll8 badHeapScheme8.chipAbsorb8
      (heapLeafColl8Find ((1 : ℤ), (1 : ℤ), SENTINEL_MAX8) ((2 : ℤ), (2 : ℤ), SENTINEL_MAX8)) :=
    ⟨by decide, rfl⟩
  have hcond : ¬ Coll8 badHeapScheme8.chipAbsorb8
      (perfectRoot8Find badHeapScheme8 0
        (padTo8 0 ((linkHeap [((1 : ℤ), (1 : ℤ))]).map (heapLeafDigest8 badHeapScheme8)))
        (padTo8 0 ((linkHeap [((2 : ℤ), (2 : ℤ))]).map (heapLeafDigest8 badHeapScheme8)))) := by
    rintro ⟨h, -⟩
    exact h rfl
  have hml : mapLeaf8Find badHeapScheme8 (linkHeap [((1 : ℤ), (1 : ℤ))])
        (linkHeap [((2 : ℤ), (2 : ℤ))])
      = heapLeafColl8Find ((1 : ℤ), (1 : ℤ), SENTINEL_MAX8) ((2 : ℤ), (2 : ℤ), SENTINEL_MAX8) := by
    show mapLeaf8Find badHeapScheme8 [((1 : ℤ), (1 : ℤ), SENTINEL_MAX8)]
        [((2 : ℤ), (2 : ℤ), SENTINEL_MAX8)] = _
    rw [mapLeaf8Find, if_pos hleaf]
  show Coll8 badHeapScheme8.chipAbsorb8 (padImtRoot8Find badHeapScheme8 0 [(1, 1)] [(2, 2)])
  rw [padImtRoot8Find, if_neg hcond, hml]
  exact hleaf

/-! ### §5b — THE NON-VACUITY WITNESS: the cone fires with ZERO residual hypotheses left.

At `honestScheme8` both residuals are discharged by theorem, so the whole-image conclusion is
delivered from the ROOT EQUALITY ALONE. If the cone were vacuous this could not be stated. -/

/-- A concrete declared whole-boundary view at depth 1: the tree holds `2 ^ 1 = 2` leaves — the MIN
sentinel and ONE declared cell `(1 ↦ 7)`. Depth 1 rather than 0 on purpose: at depth 0 the sentinel
takes the only slot, `peerCells` is forced empty, and the conclusion would be true for free. Here a
committed peer heap of length 1 is genuinely free to be `[(5, 99)]`, and the theorem is what excludes
it. -/
def demoBoundary : Heap.FeltHeap := [(1, 7)]

/-- The declared image the boundary realizes: `1 ↦ 7`, everything else absent. -/
def demoInit : ℤ → Option ℤ := fun k => if k = 1 then some 7 else none

theorem demoBoundary_sem :
    ∀ k, Heap.get demoBoundary k = if k ∈ [(1 : ℤ)] then demoInit k else none := by
  intro k
  by_cases h : k = 1 <;> simp [demoBoundary, demoInit, Heap.get, h]

/-- **⚑ THE CONE FIRES, WITH NOTHING LEFT OVER.** Any committed peer heap that fits the deployed
tree and publishes the SAME deployed-shape whole-boundary root as the declared view holds NOTHING at
the undeclared address 5. No `PadGhost8`, no `PadImtRoot8Coll` and no hash floor survives to the
caller — all three are discharged by theorem at `honestScheme8`. -/
theorem demo_no_extra_cell (peerCells : Heap.FeltHeap) (hpl : peerCells.length + 1 ≤ 2 ^ 1)
    (hcommit : wholeBoundaryFold8 honestScheme8 1 peerCells
             = wholeBoundaryFold8 honestScheme8 1 demoBoundary) :
    Heap.get peerCells 5 = none :=
  cross_cell_read_no_extra_cell8_chip honestScheme8 1 (init := demoInit) (as := [(1 : ℤ)])
    hpl (by simp [demoBoundary])
    (honest_padGhost8_refuted _) (honest_padGhost8_refuted _)
    (honest_padImtRoot8Coll_refuted _ _ _)
    hcommit rfl demoBoundary_sem (by simp)

/-- **THE CANARY THE OTHER WAY** — the conclusion of `demo_no_extra_cell` is NOT true for free: a
peer heap of the very size the hypothesis admits CAN hold a cell at the undeclared address 5. It is
the root pin, and only the root pin, that excludes it. -/
theorem demo_hidden_cell_is_visible : Heap.get [((5 : ℤ), (99 : ℤ))] 5 = some 99 := rfl

/-- And the DECLARED address still opens to its declared value under the same pin — the conclusion is
two-valued, not a blanket `none`. -/
theorem demo_declared_cell_survives (peerCells : Heap.FeltHeap) (hpl : peerCells.length + 1 ≤ 2 ^ 1)
    (hcommit : wholeBoundaryFold8 honestScheme8 1 peerCells
             = wholeBoundaryFold8 honestScheme8 1 demoBoundary) :
    Heap.get peerCells 1 = some 7 := by
  have hpeq : sentinelHeap peerCells = sentinelHeap demoBoundary :=
    crossCellRead_wholeImage8 honestScheme8 1
      (by rw [sentinelHeap_length]; exact hpl) (by rw [sentinelHeap_length]; simp [demoBoundary])
      (honest_padGhost8_refuted _) (honest_padGhost8_refuted _)
      (honest_padImtRoot8Coll_refuted _ _ _) hcommit rfl
  rw [sentinelHeap_injective hpeq]
  rfl

#assert_axioms append_replicate_eq_or_hit8
#assert_axioms padTo8_eq_or_hit
#assert_axioms padImtRoot8_binds_or_ghost_or_collides
#assert_axioms crossCellRead_wholeImage8
#assert_axioms crossCellRead_wholeImage8_sem
#assert_axioms cross_cell_read_no_extra_cell8
#assert_axioms cross_cell_read_wholeImage8_teeth
#assert_axioms cross_cell_read_no_extra_cell8_chip
#assert_axioms whole_boundary_fold8_teeth
#assert_axioms padImtRoot8_ne_arity2Root8
#assert_axioms padImtRoot8Coll_refutable_of_injective
#assert_axioms badHeapScheme8_padGhost8
#assert_axioms badHeapScheme8_padImtRoot8Coll
#assert_axioms demo_no_extra_cell
#assert_axioms demo_declared_cell_survives

end Dregg2.Circuit.WholeImageFoldRealization
