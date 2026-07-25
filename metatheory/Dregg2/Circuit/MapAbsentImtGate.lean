/-
# `Dregg2.Circuit.MapAbsentImtGate` — the `.absent` arm on the shape that SHIPS.

## Why this file exists (the finding, first sentence)

`MapOpsColumnLayout.ReconcileGatesAt`'s `.absent` arm models the deployed `Ir2Air::MapAbsent` table
as **TWO adjacent-position paths** bracketing the key. The DEPLOYED table
(`circuit/src/descriptor_ir2.rs`, `Ir2Air::MapAbsent`, the `MA_*` columns) checks **ONE low-leaf
opening whose arity-3 digest binds `low_next`, plus `lo_addr < key < low_next` as canonical
integers** — no second leaf, no physical-position adjacency. Those are two DIFFERENT constraint
systems over two DIFFERENT committed objects, and the divergence is one-sided in a way that matters:
the deployed table ACCEPTS honest rows for which the adjacency model has NO gate data at all
(`absent_model_is_incomplete_at_the_top_gap`), so the `.absent` soundness results stated over
`ReconcileGatesAt` do not cover those rows.

This is arm-specific. `MapOpsColumnLayout.AafiGatesAt` and `MapOpWideKeyGate.AafiGatesAtW` ALREADY
carry the pointer-bracket shape (gate (a) low-open at the arity-3/arity-17 leaf, gate (b) the
bracket) — the `.absent` arm is the one that was never repointed when `heap_root.rs` moved to the
indexed Merkle tree and DROPPED the MAX sentinel leaf.

## What this file authors (ADDITIVE — the adjacency model is untouched)

  * **§1 `AbsentImtGatesAt`** — the DEPLOYED `Ir2Air::MapAbsent` acceptance, modelled 1:1: the
    committed digest vector behind the pre-root (the knowledge-extraction premise, NAMED exactly as
    `ReconcileGatesAt`'s `∃ h` and `AafiGatesAt`'s `∃ xs`), ONE path to the pre-root at the arity-3
    IMT leaf `hash[lo_addr, lo_value, low_next]` (= `IndexedMerkleTree.imtLeafHash`, the deployed
    `HeapLeaf::digest8`), the pointer bracket `lo_addr < key < low_next`, and root preservation.
    Then the LAW `absentImtGates_force_absence`: under the single named `Poseidon2SpongeCR` floor and
    a committed `ImtSorted` chain behind the pre-root, an accepting deployed row FORCES
    `key ∉ imtAddrs c` and `Heap.get (imtToHeap c) key = none` — the `.absent` denotation,
    re-derived on the shape that ships.

  * **§2 `AdjacentBracketGates`** — the MODEL's `.absent` body, named and isolated (definitionally
    `ReconcileGatesAt`'s `.absent` first conjunct), plus what it FORCES:
    `adjacentBracket_forces_committed_pair` — it can only fire when TWO PHYSICALLY ADJACENT entries
    of the committed heap bracket the key. Hence `adjacentBracket_unsat_above_max`: **above the
    largest committed key the adjacency model has no witness, for any heap and any path.** That is
    the incompleteness, general, not a special case.

  * **§3 the INTERIOR EQUIVALENCE** (`interior_pointerBracket_iff_adjacent`) — on an `ImtSorted`
    chain a leaf's pointer `nextAddr` IS its physical successor's `addr`
    (`imtSorted_next_eq_succ_addr`), so at every INTERIOR low leaf the deployed pointer bracket and
    the model's adjacency bracket are the SAME predicate on the key. The mismatch is therefore
    exactly the TOP SLOT: the deployed chain's last leaf points at the terminal `SENTINEL_MAX`,
    which `heap_root.rs` deliberately does NOT store as a leaf ("The MAX sentinel is NO LONGER a
    separate sorted leaf — it survives only as the terminal `next_addr` pointer"), so the adjacency
    model's hi path has nothing to open. This converts most of the mismatch into a NAMED DEPENDENCY
    on `ImtSorted` and localizes the residue to one slot, as a theorem rather than a comment.

  * **§4 the ARITY SEPARATION** (`imtLeafHash_ne_heapLeafOf`) — under CR an arity-3 IMT leaf digest
    is NEVER an arity-2 heap leaf digest. So the two models do not merely disagree about the gate,
    they commit different leaf objects; neither constraint system refines the other, and the
    interior equivalence of §3 is an equivalence of BRACKET PREDICATES on a shared chain, never an
    equivalence of gate data.

  * **§5 TEETH on the CR-PROVED reference sponge** (`refSponge`, so nothing is hypothetical): the
    top-gap row the deployed table accepts and the model rejects, at the SAME logical map
    (`MapOpsColumnLayout.toyHeap`); the deployed law FIRING on it; and the anti-ghost — a PRESENT
    key admits NO deployed gate data.

## ⚠ NAMED PREMISE: `ImtSorted` at a deployed pre-root is a CROSS-TURN invariant

`absentImtGates_force_absence` takes `ImtSorted c` as a hypothesis, and that is honest, not lazy.
What the deployed AIR forces PER TURN is real:
  * `MapKind::Write`/`Read` (op ∈ {0,1}) hold the pointer FIXED **by column sharing** — the old- and
    new-leaf absorbs both read `MAP_NEXT` (`map_leaf_input_cols`), so a value update cannot relink;
  * `MapKind::AafiInsert` (op=4) forces the two-point `imtInsert` update at the digest-vector level
    (`MapOpsColumnLayout.aafiInsert_forces_imtInsert`), which is where the relink `next := k` lives,
    and the AAFI flip HAS landed on every set that an `.absent` op brackets (`nullifierInsertOp`,
    `revokedInsertOp`, `cellsInsertOp` are all `.aafiInsert`);
  * the two surviving op=3 `.insert`s (`insertWriteOp`, `insertWriteOpRot`) write only `cap_root`,
    which NO `.absent` op brackets — so the sorted-splice arm, which does NOT relink in-circuit,
    cannot corrupt a bracketed chain.
What is NOT forced is the INDUCTION: nothing in a per-turn AIR pins the genesis root, and nothing
composes the per-turn steps into `IndexedMerkleTree.Reachable`, so `ImtSorted` at the pre-root of an
arbitrary turn is established by `reachable_sorted` over an HONEST turn stream, not by the circuit.
The digest-vector → chain-symbol bridge is the already-named follow-up at
`MapOpsColumnLayout.lean` §8's "REMAINING WIRE". This premise is therefore carried NAMED, in the
same slot `ReconcileGatesAt`'s `∃ h, SortedKeys h` already occupies — it is not a new floor, it is
the same per-deployment knowledge-extraction premise, now stated at the pointer-chain resolution the
deployed gate actually needs.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; sorry-free; no `native_decide`. Crypto
enters ONLY as the named `Poseidon2SpongeCR` floor. Every concrete object is a literal ≤4-element
list; `MAP_TREE_DEPTH` is never unfolded and no `2^16` object is constructed. NEW file; every import
read-only; no deployed descriptor/emit/JSON/Rust byte touched.
-/
import Dregg2.Circuit.IndexedMerkleTree

namespace Dregg2.Circuit.MapAbsentImtGate

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (MapOp MapOpKind)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.MapMerkleRoot (mapNode perfectRoot perfectRoot_injective mapRoot
  mapRoot_injective)
open Dregg2.Circuit.MapOpsColumnLayout (pathPos pathRecompute pathRecompute_binds_updates
  leafOf_injective ReconcileGatesAt toyHeap toyHeap_sorted toyAbsentOp)
open Dregg2.Circuit.IndexedMerkleTree (ImtLeaf ImtSorted ImtAbsent imtAddrs imtToHeap imtLeafHash
  imtLeafHash_injective imtAbsent_excludes keys_imtToHeap imtSorted_cons_cons)
open Dregg2.Substrate

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — THE DEPLOYED `Ir2Air::MapAbsent` GATE, MODELLED 1:1.

The deployed constraint set on a real (`MA_IS_REAL = 1`) map-absent row, column by column:

  * `MA_IS_REAL` and every `MA_LO_DIR0 + lvl` are BOOLEAN;
  * `MA_NEW_ROOT[i] = MA_ROOT[i]` for all 8 lanes — a non-membership read preserves the root;
  * ONE arity-3 chip absorb `[3, MA_LO_ADDR, MA_LO_VALUE, MA_LO_NEXT, 0…, MA_LO_LEAF[0..8]]` on
    `BUS_P2` — the low leaf's IMT digest, which BINDS the pointer `MA_LO_NEXT` into the commitment;
  * `HEAP_TREE_DEPTH` `node8` compressions folding `MA_LO_LEAF` up `(MA_LO_SIB0, MA_LO_DIR0)`
    through `MA_LO_CHAIN0`, the final link BEING `MA_ROOT` — ONE membership path, not two;
  * `eval_canon_decomp` on each of `MA_LO_ADDR`, `MA_KEY`, `MA_LO_NEXT` (13 columns each:
    `[hi4, lo27 limbs, is15, inv15]`) pinning each felt to its UNIQUE canonical lift, and
    `eval_lex_lt` on `MA_CMP_LO0` / `MA_CMP_HI0` (13 columns each) giving `lo_addr < key` and
    `key < low_next` as INTEGER comparisons on those lifts;
  * the 19-felt `[root8, key, 0, 2, new_root8]` log receive on `BUS_MAP_LOG`.

Modelled below: the canonical-decomposition + comparator blocks are exactly `<` on ℤ (that is what
uniqueness of the lift buys, and it is the same modelling seam every `MapOp` denotation sits on); the
`node8` fold is `pathRecompute`; the arity-3 absorb is `imtLeafHash`. There is NO second path and NO
`pathPos` adjacency constraint, because the deployed table has neither. -/

/-- **`AbsentImtGatesAt`** — the deployed `Ir2Air::MapAbsent` acceptance for ONE row
(depth-generic; the deployment pins `MAP_TREE_DEPTH = 16`). Existentially carries the committed
digest vector `xs` behind the pre-root — the knowledge-extraction premise, NAMED exactly as
`ReconcileGatesAt`'s `∃ h` and `AafiGatesAt`'s `∃ xs`, never a claim about row columns — and asserts
the gates: the low-leaf open at the arity-3 IMT leaf, the POINTER bracket, and root preservation. -/
def AbsentImtGatesAt (hash : List ℤ → ℤ) (dep : Nat)
    (oldRoot newRoot key lowAddr lowValue lowNext : ℤ) : Prop :=
  ∃ (xs : List ℤ) (steps : List (Bool × ℤ)),
    xs.length = 2 ^ dep ∧
    steps.length = dep ∧
    oldRoot = perfectRoot hash dep xs ∧
    -- the low-leaf opening (ONE path, arity-3 leaf: the pointer is INSIDE the committed digest)
    pathRecompute hash (imtLeafHash hash ⟨lowAddr, lowValue, lowNext⟩) steps = oldRoot ∧
    -- the POINTER bracket (`MA_CMP_LO0` / `MA_CMP_HI0` over the canonical lifts)
    lowAddr < key ∧
    key < lowNext ∧
    -- `MA_NEW_ROOT = MA_ROOT`, lane by lane
    newRoot = oldRoot

/-- **The deployed gate BINDS the low leaf to the committed vector.** The single path recomputing to
the pre-root forces the arity-3 low-leaf digest — pointer included — to BE the committed digest at
the path's position; a forged pointer is a Poseidon2 collision. `pathRecompute_binds_updates` used
ONCE (the deployed table opens once). -/
theorem absentImtGates_bind_low (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (dep : Nat)
    {oldRoot newRoot key lowAddr lowValue lowNext : ℤ}
    (hg : AbsentImtGatesAt hash dep oldRoot newRoot key lowAddr lowValue lowNext) :
    ∃ (xs : List ℤ) (p : Nat),
      xs.length = 2 ^ dep ∧
      oldRoot = perfectRoot hash dep xs ∧
      xs[p]? = some (imtLeafHash hash ⟨lowAddr, lowValue, lowNext⟩) ∧
      lowAddr < key ∧ key < lowNext ∧ newRoot = oldRoot := by
  obtain ⟨xs, steps, hlen, hsl, hor, hp, hlk, hkn, hnr⟩ := hg
  have e1 : xs.length = 2 ^ steps.length := by rw [hsl]; exact hlen
  have hroot1 : pathRecompute hash (imtLeafHash hash ⟨lowAddr, lowValue, lowNext⟩) steps
      = perfectRoot hash steps.length xs := by rw [hp, hor, hsl]
  obtain ⟨hmem, _⟩ := pathRecompute_binds_updates hash hCR steps xs
    (imtLeafHash hash ⟨lowAddr, lowValue, lowNext⟩) e1 hroot1
  exact ⟨xs, pathPos steps, hlen, hor, hmem, hlk, hkn, hnr⟩

/-- **The deployed gate yields the `ImtAbsent` witness** — the pointer bracket IS the witness the
sorted-chain keystone consumes. No CR needed: this is the bracket half. The narrow twin of
`MapOpWideKeyGate.aafiGatesW_force_imtAbsentW`. -/
theorem absentImtGates_force_imtAbsent (hash : List ℤ → ℤ) (dep : Nat)
    {oldRoot newRoot key lowAddr lowValue lowNext : ℤ} {c : List ImtLeaf}
    (hg : AbsentImtGatesAt hash dep oldRoot newRoot key lowAddr lowValue lowNext)
    (hlow : (⟨lowAddr, lowValue, lowNext⟩ : ImtLeaf) ∈ c) : ImtAbsent c key := by
  obtain ⟨_, _, _, _, _, _, hlk, hkn, _⟩ := hg
  exact ⟨⟨lowAddr, lowValue, lowNext⟩, hlow, hlk, hkn⟩

/-- **★ THE DEPLOYED `.absent` LAW, on the shape that ships.** Given the committed `ImtSorted` chain
behind the pre-root (the NAMED per-deployment premise — see the header's ⚠), an accepting
`Ir2Air::MapAbsent` row FORCES the key ABSENT from the whole committed address spine, and hence
`Heap.get` on the projected map to be `none`, and the post-root to equal the pre-root. The low leaf's
membership in the chain is DERIVED here (through `imtLeafHash_injective` + root injectivity), not
assumed: the row cannot open a leaf the commitment does not hold.

This is the `.absent` result the epoch's theorems SHOULD have been stated over. -/
theorem absentImtGates_force_absence (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (dep : Nat)
    {oldRoot newRoot key lowAddr lowValue lowNext : ℤ} {c : List ImtLeaf}
    (hs : ImtSorted c) (hlen : c.length = 2 ^ dep)
    (hroot : oldRoot = perfectRoot hash dep (c.map (imtLeafHash hash)))
    (hg : AbsentImtGatesAt hash dep oldRoot newRoot key lowAddr lowValue lowNext) :
    key ∉ imtAddrs c ∧ Heap.get (imtToHeap c) key = none ∧ newRoot = oldRoot := by
  obtain ⟨xs, p, hxlen, hor, hmem, hlk, hkn, hnr⟩ := absentImtGates_bind_low hash hCR dep hg
  -- The opened vector IS the chain's leaf-digest image: same length, same perfect root.
  have hxs : xs = c.map (imtLeafHash hash) :=
    perfectRoot_injective hash hCR dep hxlen (by rw [List.length_map]; exact hlen)
      (by rw [← hor, hroot])
  subst hxs
  -- The bound digest decodes to a chain leaf (CR on the arity-3 leaf).
  simp only [List.getElem?_map] at hmem
  have hlow : (⟨lowAddr, lowValue, lowNext⟩ : ImtLeaf) ∈ c := by
    cases he : c[p]? with
    | none => rw [he] at hmem; simp at hmem
    | some l =>
      rw [he] at hmem
      simp only [Option.map_some, Option.some.injEq] at hmem
      obtain rfl := imtLeafHash_injective hash hCR hmem
      exact List.mem_of_getElem? he
  have hnotin : key ∉ imtAddrs c :=
    imtAbsent_excludes hs ⟨⟨lowAddr, lowValue, lowNext⟩, hlow, hlk, hkn⟩
  refine ⟨hnotin, ?_, hnr⟩
  rw [Heap.get_eq_none_iff, keys_imtToHeap]
  exact hnotin

/-! ## §2 — THE MODEL'S `.absent` BODY, AND WHAT IT FORCES.

`AdjacentBracketGates` is, definitionally, the first conjunct of `ReconcileGatesAt`'s `.absent`
arm at `r := (m.root 0).eval a`, `k := m.key.eval a`. Isolating it makes the incompleteness a
theorem about the model rather than a remark about a `def`. -/

/-- **`AdjacentBracketGates`** — the `.absent` gate body `ReconcileGatesAt` actually requires: TWO
paths at CONSECUTIVE positions (`pathPos stepsHi = pathPos stepsLo + 1`) opening arity-2 heap leaves
whose keys strictly bracket `k`. -/
def AdjacentBracketGates (hash : List ℤ → ℤ) (dep : Nat) (r k : ℤ) : Prop :=
  ∃ (stepsLo stepsHi : List (Bool × ℤ)) (klo vlo khi vhi : ℤ),
    stepsLo.length = dep ∧ stepsHi.length = dep ∧
    pathPos stepsHi = pathPos stepsLo + 1 ∧
    pathRecompute hash (Heap.leafOf hash (klo, vlo)) stepsLo = r ∧
    pathRecompute hash (Heap.leafOf hash (khi, vhi)) stepsHi = r ∧
    klo < k ∧ k < khi

/-- **The model's gate can only fire on a PHYSICALLY ADJACENT committed pair.** Under CR, accepted
adjacency gate data forces two entries of the committed heap at positions `p` and `p+1` whose keys
bracket the row's key. This is the structural content of the adjacency shape — and the reason it
cannot express the deployed pointer bracket, whose hi bound is a leaf FIELD, not a neighbour. -/
theorem adjacentBracket_forces_committed_pair (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep : Nat) {r k : ℤ} (h : Heap.FeltHeap) (hlen : h.length = 2 ^ dep)
    (hroot : mapRoot hash dep h = r) (hg : AdjacentBracketGates hash dep r k) :
    ∃ (p : Nat) (klo vlo khi vhi : ℤ),
      h[p]? = some (klo, vlo) ∧ h[p + 1]? = some (khi, vhi) ∧ klo < k ∧ k < khi := by
  obtain ⟨sLo, sHi, klo, vlo, khi, vhi, hlLo, hlHi, hadj, hpLo, hpHi, hklo, hkhi⟩ := hg
  subst hroot
  have hbindLo := (pathRecompute_binds_updates hash hCR sLo (h.map (Heap.leafOf hash))
    (Heap.leafOf hash (klo, vlo))
    (by rw [List.length_map, hlen, hlLo]) (by rw [hlLo]; exact hpLo)).1
  have hbindHi := (pathRecompute_binds_updates hash hCR sHi (h.map (Heap.leafOf hash))
    (Heap.leafOf hash (khi, vhi))
    (by rw [List.length_map, hlen, hlHi]) (by rw [hlHi]; exact hpHi)).1
  simp only [List.getElem?_map] at hbindLo hbindHi
  cases heLo : h[pathPos sLo]? with
  | none => rw [heLo] at hbindLo; simp at hbindLo
  | some eLo =>
    rw [heLo] at hbindLo
    simp only [Option.map_some, Option.some.injEq] at hbindLo
    obtain rfl := leafOf_injective hash hCR hbindLo
    cases heHi : h[pathPos sHi]? with
    | none => rw [heHi] at hbindHi; simp at hbindHi
    | some eHi =>
      rw [heHi] at hbindHi
      simp only [Option.map_some, Option.some.injEq] at hbindHi
      obtain rfl := leafOf_injective hash hCR hbindHi
      rw [hadj] at heHi
      exact ⟨pathPos sLo, klo, vlo, khi, vhi, heLo, heHi, hklo, hkhi⟩

/-- **★ THE INCOMPLETENESS, GENERAL.** ABOVE the largest committed key the adjacency model has NO
gate data — for ANY heap behind the root and ANY pair of paths. The hi bracket would have to be a
committed entry strictly GREATER than the key, and there is none. The deployed pointer bracket has no
such trouble: the last leaf's `next_addr` is the terminal `SENTINEL_MAX`, which brackets every key
above the maximum, and `heap_root.rs` deliberately does not store it as a leaf. -/
theorem adjacentBracket_unsat_above_max (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep : Nat) {r k : ℤ} (h : Heap.FeltHeap) (hlen : h.length = 2 ^ dep)
    (hroot : mapRoot hash dep h = r) (hmax : ∀ x ∈ Heap.keys h, x < k) :
    ¬ AdjacentBracketGates hash dep r k := by
  intro hg
  obtain ⟨p, klo, vlo, khi, vhi, _, hhi, _, hkhi⟩ :=
    adjacentBracket_forces_committed_pair hash hCR dep h hlen hroot hg
  have hmem : (khi, vhi) ∈ h := List.mem_of_getElem? hhi
  have hkey : khi ∈ Heap.keys h := by
    simp only [Heap.keys]
    exact List.mem_map.mpr ⟨(khi, vhi), hmem, rfl⟩
  exact absurd hkhi (not_lt.mpr (le_of_lt (hmax khi hkey)))

/-! ## §3 — THE INTERIOR EQUIVALENCE: where the two shapes DO agree, and exactly where they do not.

The deployed `ImtSorted` invariant says a leaf's pointer EQUALS its physical successor's address
(`l.nextAddr = l'.addr`, the well-linked conjunct). So on the interior the pointer bracket and the
adjacency bracket are the SAME predicate on the key — the mismatch reduces to a NAMED DEPENDENCY on
`ImtSorted` there, and the residue is exactly the LAST slot. -/

/-- On an `ImtSorted` chain the pointer of the leaf at `p` IS the address of the leaf at `p+1` —
the well-linked conjunct, read positionally. -/
theorem imtSorted_next_eq_succ_addr {K V : Type} [LinearOrder K] :
    ∀ {c : List (ImtLeaf K V)}, ImtSorted c → ∀ (p : Nat) (l l' : ImtLeaf K V),
      c[p]? = some l → c[p + 1]? = some l' → l.nextAddr = l'.addr := by
  intro c
  induction c with
  | nil => intro _ p l l' hl _; simp at hl
  | cons hd tl ih =>
    intro hs p l l' hl hl'
    cases p with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hl
      subst hl
      simp only [Nat.zero_add, List.getElem?_cons_succ] at hl'
      cases tl with
      | nil => simp at hl'
      | cons hd2 tl2 =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hl'
        subst hl'
        rw [imtSorted_cons_cons] at hs
        exact hs.2.1
    | succ q =>
      simp only [List.getElem?_cons_succ] at hl hl'
      have hts : ImtSorted tl := by
        cases tl with
        | nil => exact trivial
        | cons hd2 tl2 => rw [imtSorted_cons_cons] at hs; exact hs.2.2
      exact ih hts q l l' hl hl'

/-- **★ THE INTERIOR EQUIVALENCE.** On an `ImtSorted` chain, at any low leaf that HAS a physical
successor, the DEPLOYED pointer bracket `low.addr < k < low.nextAddr` and the MODEL's adjacency
bracket `low.addr < k < succ.addr` are the SAME condition. So for interior gaps the shape mismatch is
a NAMED DEPENDENCY on the maintained invariant, not a difference in what is proved — which is
precisely why it took this long to notice. -/
theorem interior_pointerBracket_iff_adjacent {c : List ImtLeaf} (hs : ImtSorted c)
    {p : Nat} {l l' : ImtLeaf} (hl : c[p]? = some l) (hl' : c[p + 1]? = some l') (k : ℤ) :
    (l.addr < k ∧ k < l.nextAddr) ↔ (l.addr < k ∧ k < l'.addr) := by
  rw [imtSorted_next_eq_succ_addr hs p l l' hl hl']

/-- The projected map sees the chain positionally (the bridge the adjacency model's committed pair
would have to land in). -/
theorem imtToHeap_getElem? {c : List ImtLeaf} {p : Nat} {l : ImtLeaf} (h : c[p]? = some l) :
    (imtToHeap c)[p]? = some (l.addr, l.value) := by
  simp only [imtToHeap, List.getElem?_map, h, Option.map_some]

/-- **The interior bracket DOES produce the model's committed pair.** On an `ImtSorted` chain, an
interior deployed bracket hands the adjacency model exactly the two consecutive projected entries it
demands — the one-directional bridge, valid wherever a physical successor exists. -/
theorem interior_bracket_gives_adjacent_pair {c : List ImtLeaf} (hs : ImtSorted c)
    {p : Nat} {l l' : ImtLeaf} (hl : c[p]? = some l) (hl' : c[p + 1]? = some l') {k : ℤ}
    (hlo : l.addr < k) (hhi : k < l.nextAddr) :
    (imtToHeap c)[p]? = some (l.addr, l.value) ∧
    (imtToHeap c)[p + 1]? = some (l'.addr, l'.value) ∧ l.addr < k ∧ k < l'.addr :=
  ⟨imtToHeap_getElem? hl, imtToHeap_getElem? hl', hlo,
    ((interior_pointerBracket_iff_adjacent hs hl hl' k).mp ⟨hlo, hhi⟩).2⟩

/-! ## §4 — THE ARITY SEPARATION: the two models commit DIFFERENT leaf objects. -/

/-- **★ An arity-3 IMT leaf digest is NEVER an arity-2 heap leaf digest** (under CR: equal digests
would be equal preimage LISTS, and `3 ≠ 2`). So the deployed `Ir2Air::MapAbsent` opening and
`ReconcileGatesAt`'s `.absent` opening cannot be satisfied by one committed vector at one position:
neither constraint system refines the other. §3's equivalence is an equivalence of BRACKET
PREDICATES on a shared chain — never a translation of gate data. -/
theorem imtLeafHash_ne_heapLeafOf (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (l : ImtLeaf) (e : ℤ × ℤ) : imtLeafHash hash l ≠ Heap.leafOf hash e := by
  intro h
  simp only [imtLeafHash, Heap.leafOf] at h
  have hl := congrArg List.length (hCR _ _ h)
  simp at hl

/-! ## §5 — TEETH, on the CR-PROVED reference sponge (`refSponge`): nothing hypothetical. -/

section Teeth

open Dregg2.Circuit.Poseidon2Binding.Reference (refSponge refSponge_CR)

/-- The deployed-shape IMT chain behind the toy root: FOUR leaves (so `2^2`, no padding seam),
well-linked, and TERMINATED by the pointer `100` — the `SENTINEL_MAX` face, which `heap_root.rs`
deliberately does NOT store as a leaf. -/
def topChain : List ImtLeaf :=
  [⟨10, 1, 20⟩, ⟨20, 2, 30⟩, ⟨30, 3, 40⟩, ⟨40, 4, 100⟩]

theorem topChain_sorted : ImtSorted topChain := by
  refine ⟨by decide, rfl, ⟨by decide, rfl, ⟨by decide, rfl, ?_⟩⟩⟩
  show (40 : ℤ) < 100
  decide

/-- The chain projects to EXACTLY `MapOpsColumnLayout.toyHeap` — the two models are being compared
on the SAME logical map, not on two conveniently different ones. -/
theorem topChain_projects_to_toyHeap : imtToHeap topChain = toyHeap := rfl

/-- The arity-3 committed digest vector behind the chain's root, and that root. -/
def topLeaves (hash : List ℤ → ℤ) : List ℤ := topChain.map (imtLeafHash hash)

def topRoot (hash : List ℤ → ℤ) : ℤ := perfectRoot hash 2 (topLeaves hash)

/-- The position-3 membership path (root-first: RIGHT at the top, RIGHT at the bottom —
`pathPos = 2 + 1 = 3`, the LAST leaf). -/
def topSteps (hash : List ℤ → ℤ) : List (Bool × ℤ) :=
  [(true, mapNode hash (imtLeafHash hash ⟨10, 1, 20⟩) (imtLeafHash hash ⟨20, 2, 30⟩)),
   (true, imtLeafHash hash ⟨30, 3, 40⟩)]

theorem topSteps_recompute (hash : List ℤ → ℤ) :
    pathRecompute hash (imtLeafHash hash ⟨40, 4, 100⟩) (topSteps hash) = topRoot hash := rfl

/-- **★ HALF ONE — the DEPLOYED table ACCEPTS the honest top-gap row.** Key `50` is above every
committed key; the last leaf's terminal pointer brackets it (`40 < 50 < 100`), one path authenticates
the low leaf, the root is preserved. This is an ORDINARY row: a fresh nullifier / cell-id above the
current maximum lands here. -/
theorem topGap_deployed_accepts (hash : List ℤ → ℤ) :
    AbsentImtGatesAt hash 2 (topRoot hash) (topRoot hash) 50 40 4 100 :=
  ⟨topLeaves hash, topSteps hash, rfl, rfl, rfl, topSteps_recompute hash,
    by decide, by decide, rfl⟩

/-- **★ HALF TWO — the MODEL REJECTS the same row, at every heap and every path.** `50` exceeds
every key of the committed map, so `AdjacentBracketGates` has no witness: the hi path would have to
open a committed entry above `50`. -/
theorem topGap_model_rejects :
    ¬ AdjacentBracketGates refSponge 2 (mapRoot refSponge 2 toyHeap) 50 :=
  adjacentBracket_unsat_above_max refSponge refSponge_CR 2 toyHeap rfl rfl (by decide)

/-- A top-gap `.absent` ROW on the toy wires: root/newRoot the committed toy root, key `50`. -/
def toyTopGapEnv (hash : List ℤ → ℤ) : Assignment := fun c =>
  if c = 0 then mapRoot hash 2 toyHeap
  else if c = 1 then 50 else if c = 2 then 0
  else if c = 3 then mapRoot hash 2 toyHeap else 0

/-- **★ THE BLAST RADIUS, CONCRETE — `ReconcileGatesAt` itself is UNSATISFIABLE on an honest
deployed row.** There is NO gate data, at any heap and any paths, for the top-gap `.absent` row the
deployed `Ir2Air::MapAbsent` table accepts. Every theorem whose hypothesis is
`ReconcileGatesAt … .absent` (or `ReconcileGatesAtW … .absent`, which is the SAME predicate at
`narrowEnc` by `MapOpWideKeyGate.narrow_gates_is_instance`) therefore says NOTHING about these
rows — the hypothesis is false, so the implication is vacuous exactly where the deployed prover
operates. -/
theorem topGap_reconcileGates_unsat :
    ¬ ReconcileGatesAt refSponge 2 (toyTopGapEnv refSponge) toyAbsentOp := by
  rintro ⟨h, _, hlen, hroot, hgb, _⟩
  -- The row's root column IS the committed toy root, so root injectivity pins the extracted heap.
  have hr : mapRoot refSponge 2 h = mapRoot refSponge 2 toyHeap := hroot
  have hmax : ∀ x ∈ Heap.keys h, x < (50 : ℤ) := by
    have hh : h = toyHeap := mapRoot_injective refSponge refSponge_CR 2 hlen rfl hr
    subst hh
    decide
  exact adjacentBracket_unsat_above_max refSponge refSponge_CR 2 h hlen hroot hmax hgb

/-- **★ RESPECTING TOOTH — the DEPLOYED law FIRES on the row the model cannot see.** The shipped
pointer-bracket gate, plus the named `ImtSorted` premise, forces `50` absent from the whole committed
spine and `Heap.get` to be `none` on the projected map. The arm is not merely re-modelled; the
soundness is re-derived on it. -/
theorem topGap_deployed_law_fires :
    (50 : ℤ) ∉ imtAddrs topChain ∧ Heap.get (imtToHeap topChain) 50 = none ∧
      topRoot refSponge = topRoot refSponge :=
  absentImtGates_force_absence refSponge refSponge_CR 2 topChain_sorted rfl rfl
    (topGap_deployed_accepts refSponge)

/-- **★ ANTI-GHOST — a PRESENT key admits NO deployed gate data.** For ANY claimed low leaf and ANY
claimed post-root, the shipped gate cannot open `30` (which the chain HOLDS) as absent: a bracket
around a present key would have to point THROUGH it, and `imtAbsent_excludes` refutes. The
pointer-bracket model is not vacuously accepting. -/
theorem present_key_has_no_deployed_gate (newRoot lowAddr lowValue lowNext : ℤ) :
    ¬ AbsentImtGatesAt refSponge 2 (topRoot refSponge) newRoot 30 lowAddr lowValue lowNext := by
  intro hg
  exact (absentImtGates_force_absence refSponge refSponge_CR 2 topChain_sorted rfl rfl hg).1
    (by decide)

/-- **★ THE MISMATCH, in one statement.** On ONE logical map, for ONE honest absent key: the
deployed table ACCEPTS, the model has NO witness, and the key really is absent (both faces). The
divergence is not a difference of abstraction level — it is an assurance GAP, one-sided, on the
ordinary path. -/
theorem absent_model_is_incomplete_at_the_top_gap :
    AbsentImtGatesAt refSponge 2 (topRoot refSponge) (topRoot refSponge) 50 40 4 100 ∧
    ¬ AdjacentBracketGates refSponge 2 (mapRoot refSponge 2 toyHeap) 50 ∧
    ¬ ReconcileGatesAt refSponge 2 (toyTopGapEnv refSponge) toyAbsentOp ∧
    (50 : ℤ) ∉ imtAddrs topChain ∧
    Heap.get toyHeap 50 = none :=
  ⟨topGap_deployed_accepts refSponge, topGap_model_rejects, topGap_reconcileGates_unsat,
    topGap_deployed_law_fires.1, topChain_projects_to_toyHeap ▸ topGap_deployed_law_fires.2.1⟩

/-- The INTERIOR agrees, on the same chain: key `25` sits in the `20 → 30` pointer gap, and that
pointer IS position 2's address — so here the deployed bracket and the model's adjacency bracket are
the same condition (`interior_pointerBracket_iff_adjacent` instantiated). -/
theorem interior_25_agrees :
    ((⟨20, 2, 30⟩ : ImtLeaf).addr < 25 ∧ (25 : ℤ) < (⟨20, 2, 30⟩ : ImtLeaf).nextAddr) ↔
      ((⟨20, 2, 30⟩ : ImtLeaf).addr < 25 ∧ (25 : ℤ) < (⟨30, 3, 40⟩ : ImtLeaf).addr) :=
  interior_pointerBracket_iff_adjacent topChain_sorted (p := 1) rfl rfl 25

end Teeth

/-! ## §6 — AXIOM HYGIENE. -/

#assert_axioms absentImtGates_force_absence
#assert_axioms adjacentBracket_forces_committed_pair
#assert_axioms adjacentBracket_unsat_above_max
#assert_axioms interior_pointerBracket_iff_adjacent
#assert_axioms imtLeafHash_ne_heapLeafOf
#assert_axioms absent_model_is_incomplete_at_the_top_gap
#assert_axioms present_key_has_no_deployed_gate

end Dregg2.Circuit.MapAbsentImtGate
