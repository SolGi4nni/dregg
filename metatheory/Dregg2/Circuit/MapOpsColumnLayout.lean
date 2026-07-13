/-
# `Dregg2.Circuit.MapOpsColumnLayout` — the MAPOPS-AIR MODELER: from ANY descriptor's `.mapOp`
constraints onto the deployed map-reconcile gate data (the in-circuit binary-Merkle path
recompute), ∀ `d : EffectVmDescriptor2` — the memory/map twin of `LogUpColumnLayout`.

## HONEST SCOPE (first sentence)

This file MODELS, for an ARBITRARY v2 descriptor, the `Ir2Air::MapOps` AIR
(`circuit/src/descriptor_ir2.rs:2213`, `heap_root.rs::CanonicalHeapTree`) that
`docs/reference/MEMORY-LEGS-SCOPE.md` §3 names as the ONE shared real item for the 7 mapOp
effects — and PROVES the ∀ d MAPOPS-AIR LAW: the deployed map-reconcile gates (a sibling-path
recompute of the opened leaf to the committed pre-root, plus — for writes — the SAME path
recomputing the new leaf to the post-root column) FORCE `MapOp.holdsAt`, the existential
`opensTo`/`writesTo` denotation (`DescriptorIR2.lean:511`), for every `.mapOp` row of every
descriptor (`mapOp_holds_of_mapReconcile` / `mapOpsArm_of_modeler`). The crux is the
extraction-shaped Merkle-opening argument (`pathRecompute_binds_updates`): under the single named
hash floor `Poseidon2SpongeCR`, a path recomputing to the committed perfect-tree root BINDS the
opened leaf to the committed leaf vector at the path's position — a forged opening is two distinct
lists under one 2-to-1 node image, i.e. a Poseidon2 collision (the same floor and the same
induction shape as `OodCommitmentBinding.merkleRecomputeZ_binds` / `FriVerifier.merkleRecompute_binds`,
here strengthened with the UPDATE direction so the post-root of a write is forced too).

This is NOT a bus: the mapOps table's `TableDef` kind is `.mapReconcile` (`DescriptorIR2.lean:169`),
one row per boundary reconciliation, checked by path recomputation — a different argument from the
LogUp cumulative sum, hence this separate modeler (MEMORY-LEGS-SCOPE §1).

## What is GENERAL (∀ d) vs what stays PER-DESCRIPTOR / per-deployment

GENERAL, proved here for every descriptor:
  * the extraction — `mapOpsOf d` (`DescriptorIR2`), the fired row ops `firedMapOpsAt`, and
    `mapLog_eq_fired`: the gathered map-ops log IS the per-row fired-op rows, read off ANY `d`;
  * the PATH-BINDING LAW (`pathRecompute_binds_updates`): a path recomputing to the root of a
    `2^dep`-leaf digest vector opens EXACTLY the committed leaf at the path position, and the same
    siblings recompute any replacement leaf to the root of the UPDATED vector — pure CR peeling,
    level by level (`mapNode_injective` at each node);
  * the per-kind openers riding it: `opensToMerkle_of_path` (`.read`),
    `opensToMerkle_none_of_bracket` (`.absent` — TWO adjacent-position paths bracketing the key,
    the deployed gap opening; adjacency of positions ⟹ `Adjacent` on the key spine ⟹
    `Heap.get_none_of_gap`), `writesToMerkle_of_path` (`.write`/`.insert` — old-leaf path to the
    pre-root + new-leaf path to the post-root ⟹ the post-root IS `mapRoot (Heap.set …)`);
  * THE LAW (∀ d): `mapOp_holds_of_mapReconcile` (per row) and `mapOpsArm_of_modeler` (the whole
    `.mapOp` arm of `Satisfied2.rowConstraints` for any `d`), plus the graduated+mapOps `hbus`
    splitter `hbus_of_busModels_and_mapModel` (every non-arith constraint a `.lookup` OR a
    `.mapOp` — the shape all 7 memory-touching mapOp effects have) and the full assembler
    `airAccept_forces_satisfied2_of_modelers`.

PER-DESCRIPTOR / per-deployment (each NAMED, none silently assumed):
  * the KNOWLEDGE-EXTRACTION premise inside `ReconcileGatesAt`: the prover's committed canonical
    heap behind the row's pre-root column (`∃ h, SortedKeys h ∧ |h| = 2^dep ∧ mapRoot h = root`).
    This is MEMORY-LEGS-SCOPE §3's honest crux, option (i): the deployed prover's
    `CanonicalHeapTree` update witness IS the whole-tree witness; what the GATES then FORCE — the
    real content of this file — is that the row's `(key, value, new_root)` columns cannot LIE
    about that heap (a lie ⟹ a Poseidon2 collision). The row columns are never assumed truthful;
    they are derived truthful.
  * SPECIES B (`mapTableFaithful : t.tf .mapOps = mapLog d t`) — the table-ASSEMBLY fact, the
    same classification `AirLegsDischarged` gives transferV3's emptiness pair; carried NAMED in
    the assembler (`hMapTF`), never derived from AIR arithmetic. Part B of the split.
  * WHICH map each effect writes and that its selector fires — the per-effect teeth that already
    exist downstream of `Satisfied2` (`noteSpendV3_grow_gate_forces_set_insert`,
    `noteCreateV3_grow_gate_forces_set_insert`, `createCellV3/factoryV3/spawnV3/spawnWriteV3_…`,
    `refusalFieldsWriteV3_forces_write`, `heapWrite_splice_forced`) — those consume the arm this
    file produces; nothing per-effect is re-proved here.
  * the Rust-assembly correspondence: that the deployed p3 mapOps columns are laid out as modeled
    (the `mix` closure = `pathRecompute` with the leaf-to-root fold listed root-first; the gap
    opening = two adjacent-position paths). The SAME pinned Lean-model-to-Rust boundary every
    `DescriptorIR2` denotation sits on.

Note on `.insert` vs `.write`: both denote `writesTo` (sorted insert-or-update) with the deployed
`2^dep`-leaf PADDED vector (MIN/MAX sentinels are real entries of the modeled heap), so the
modeled gate for both is the update-at-an-opened-leaf shape; `.insert` freshness is established
SEPARATELY by the paired `.absent` op (exactly the noteSpend pattern, `DescriptorIR2.lean:251-256`).

## Heap safety

Everything is symbolic — `MAP_TREE_DEPTH = 16` is never unfolded into a tree, no `2^16` object is
ever constructed. The non-vacuity teeth run at a 2-LEVEL heap (`dep = 2`, 4 leaves) through the
SAME depth-generic theorems the deployed depth instantiates; `decide` only ever touches short
literal ℤ lists.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; sorry-free. Crypto enters ONLY as the
named `Poseidon2SpongeCR` floor (the same one the whole commitment tower carries), never as an
axiom. NEW file; imports read-only.
-/
import Dregg2.Circuit.LogUpColumnLayout

namespace Dregg2.Circuit.MapOpsColumnLayout

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv siteHoldsAll)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.MapMerkleRoot (mapNode mapNode_injective foldLevel perfectRoot
  perfectRoot_injective foldLevel_length_half mapRoot mapRoot_injective opensToMerkle
  writesToMerkle opensToMerkle_functional writesToMerkle_functional)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.AirChecksSatisfied (isArith MainAirAcceptF airAccept_forces_satisfied2)
open Dregg2.Circuit.LogUpColumnLayout (BusModelOk busModel_forces_lookup_holds mem_lookupsInto)
open Dregg2.Substrate
open Dregg2.Crypto

set_option autoImplicit false

/-! ## §1 — THE EXTRACTION (∀ d): the map ops a trace performs, read off ANY descriptor.

`mapOpsOf d` (the declared `.mapOp` constraints) already lives in `DescriptorIR2`; here we pin its
membership characterization and the ROW face — which declared ops FIRE on a row (guard = 1), and
that the gathered `mapLog` is exactly the fired ops' evaluated `(root, key, value, op, new_root)`
rows. This is the A-side extraction: what the mapOps table must carry, per row, for any `d`. -/

/-- Membership in the extracted map-op family: exactly the declared `.mapOp`s. -/
theorem mem_mapOpsOf {d : EffectVmDescriptor2} {m : MapOp} :
    m ∈ mapOpsOf d ↔ VmConstraint2.mapOp m ∈ d.constraints := by
  unfold mapOpsOf
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨c, hc, hf⟩
    cases c <;> simp_all
  · intro hc
    exact ⟨.mapOp m, hc, rfl⟩

/-- **The fired map ops on a row** — the declared ops whose selector guard is `1` on the row
assignment (NoOp / pad rows contribute nothing: selector discipline). -/
def firedMapOpsAt (d : EffectVmDescriptor2) (a : Assignment) : List MapOp :=
  (mapOpsOf d).filter (fun m => m.guard.eval a == 1)

/-- Fired-op membership: declared AND guard-firing. -/
theorem mem_firedMapOpsAt {d : EffectVmDescriptor2} {a : Assignment} {m : MapOp} :
    m ∈ firedMapOpsAt d a ↔ m ∈ mapOpsOf d ∧ m.guard.eval a = 1 := by
  unfold firedMapOpsAt
  rw [List.mem_filter, beq_iff_eq]

/-- **The gathered map-ops log IS the fired extraction** — `mapLog d t` (the rows the committed
mapOps table must carry, `Satisfied2.mapTableFaithful`'s RHS) equals, row by row, the fired ops'
evaluated `(root, key, value, op, new_root)` tuples. The ∀ d bridge between the declared
constraint list and the table the AIR checks. -/
theorem mapLog_eq_fired (d : EffectVmDescriptor2) (t : VmTrace) :
    mapLog d t
      = t.rows.flatMap (fun a => (firedMapOpsAt d a).map (fun m => m.rowAt a)) := by
  unfold mapLog firedMapOpsAt
  congr 1
  funext a
  induction mapOpsOf d with
  | nil => rfl
  | cons m ms ih =>
    by_cases hg : m.guard.eval a = 1
    · simp [List.filterMap_cons, List.filter_cons, hg, ih]
    · simp [List.filterMap_cons, List.filter_cons, hg, ih]

/-! ## §2 — THE PATH MODEL: the deployed `mix` closure and the CR binding law.

The deployed `Ir2Air::MapOps` AIR recomputes the opened leaf up its sibling path to the committed
root (the `mix` closure over `heap_root.rs`'s update/membership witnesses). We model a path as the
ROOT-FIRST list of `(side, sibling)` steps — `(false, s)` = the opened subtree is the LEFT child
(sibling `s` on the right), `(true, s)` = RIGHT child (sibling on the left); the deployed fold
iterates leaf-to-root, which is this list reversed (a presentation choice, same fold). `pathPos`
is the leaf index the side bits select. -/

/-- The leaf position a root-first path selects (`true` = right child at that level). -/
def pathPos : List (Bool × ℤ) → Nat
  | [] => 0
  | (false, _) :: rest => pathPos rest
  | (true, _) :: rest => 2 ^ rest.length + pathPos rest

/-- **`pathRecompute`** — the in-circuit Merkle-path recompute: fold the opened `leaf` up through
the root-first `(side, sibling)` steps with the deployed 2-to-1 node `mapNode` (= `hash[l, r]`,
`heap_root.rs`'s `hash_fact(l, [r])`). -/
def pathRecompute (hash : List ℤ → ℤ) (leaf : ℤ) : List (Bool × ℤ) → ℤ
  | [] => leaf
  | (false, sib) :: rest => mapNode hash (pathRecompute hash leaf rest) sib
  | (true, sib) :: rest => mapNode hash sib (pathRecompute hash leaf rest)

/-- The selected position is inside the `2^depth`-leaf tree. -/
theorem pathPos_lt : ∀ steps : List (Bool × ℤ), pathPos steps < 2 ^ steps.length := by
  intro steps
  induction steps with
  | nil => simp [pathPos]
  | cons s rest ih =>
    obtain ⟨b, sib⟩ := s
    have h2 : 2 ^ (rest.length + 1) = 2 ^ rest.length + 2 ^ rest.length := by
      rw [pow_succ]; ring
    cases b <;> simp only [pathPos, List.length_cons] <;> omega

/-- `List.set` inside the left half of an append (helper; index below the left length). -/
theorem set_append_left' {α : Type*} :
    ∀ (l₁ l₂ : List α) (i : Nat) (x : α), i < l₁.length →
      (l₁ ++ l₂).set i x = l₁.set i x ++ l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ i x h; simp at h
  | cons a t ih =>
    intro l₂ i x h
    cases i with
    | zero => rfl
    | succ j =>
      simp only [List.length_cons] at h
      show a :: (t ++ l₂).set j x = a :: (t.set j x ++ l₂)
      rw [ih l₂ j x (by omega)]

/-- `List.set` inside the right half of an append (helper; index past the left length). -/
theorem set_append_right' {α : Type*} :
    ∀ (l₁ l₂ : List α) (i : Nat) (x : α),
      (l₁ ++ l₂).set (l₁.length + i) x = l₁ ++ l₂.set i x := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ i x; simp
  | cons a t ih =>
    intro l₂ i x
    have harith : (a :: t).length + i = (t.length + i) + 1 := by
      simp only [List.length_cons]; omega
    rw [harith]
    show a :: (t ++ l₂).set (t.length + i) x = a :: (t ++ l₂.set i x)
    rw [ih]

/-- `map` commutes with `set` (helper). -/
theorem map_set' {α β : Type*} (f : α → β) :
    ∀ (l : List α) (n : Nat) (x : α), (l.set n x).map f = (l.map f).set n (f x) := by
  intro l
  induction l with
  | nil => intro n x; simp
  | cons a t ih =>
    intro n x
    cases n with
    | zero => rfl
    | succ m =>
      show f a :: (t.set m x).map f = f a :: (t.map f).set m (f x)
      rw [ih]

/-- One fold level distributes over an append whose left part has even length. -/
theorem foldLevel_append (hash : List ℤ → ℤ) :
    ∀ (n : Nat) (L R : List ℤ), L.length = 2 * n →
      foldLevel hash (L ++ R) = foldLevel hash L ++ foldLevel hash R := by
  intro n
  induction n with
  | zero =>
    intro L R hL
    have : L = [] := List.length_eq_zero_iff.mp (by omega)
    subst this; rfl
  | succ m ih =>
    intro L R hL
    match L, hL with
    | l :: r :: rest, hL =>
      simp only [List.length_cons] at hL
      show mapNode hash l r :: foldLevel hash (rest ++ R)
          = mapNode hash l r :: foldLevel hash rest ++ foldLevel hash R
      rw [ih rest R (by omega)]
      rfl

/-- **The perfect-tree root SPLITS at the top node**: the root of `L ++ R` (each half `2^d`
leaves) is `mapNode (root L) (root R)` — the structural fact the path peel descends through. -/
theorem perfectRoot_append (hash : List ℤ → ℤ) :
    ∀ (d : Nat) (L R : List ℤ), L.length = 2 ^ d → R.length = 2 ^ d →
      perfectRoot hash (d + 1) (L ++ R)
        = mapNode hash (perfectRoot hash d L) (perfectRoot hash d R) := by
  intro d
  induction d with
  | zero =>
    intro L R hL hR
    rw [pow_zero] at hL hR
    obtain ⟨x, rfl⟩ : ∃ x, L = [x] := by
      cases L with
      | nil => simp at hL
      | cons a t =>
        cases t with
        | nil => exact ⟨a, rfl⟩
        | cons b t' => simp at hL
    obtain ⟨y, rfl⟩ : ∃ y, R = [y] := by
      cases R with
      | nil => simp at hR
      | cons a t =>
        cases t with
        | nil => exact ⟨a, rfl⟩
        | cons b t' => simp at hR
    rfl
  | succ d ih =>
    intro L R hL hR
    have h2L : L.length = 2 * 2 ^ d := by rw [hL, pow_succ]; ring
    show perfectRoot hash (d + 1) (foldLevel hash (L ++ R)) = _
    rw [foldLevel_append hash (2 ^ d) L R h2L]
    rw [ih (foldLevel hash L) (foldLevel hash R)
      (foldLevel_length_half hash (2 ^ d) L h2L)
      (foldLevel_length_half hash (2 ^ d) R (by rw [hR, pow_succ]; ring))]
    rfl

/-- **THE PATH-BINDING + UPDATE LAW (the crux; the extraction-shaped Merkle-opening argument).**
Under the single named CR floor: a path recomputing `leaf` to the perfect-tree root of a
`2^depth`-leaf vector `xs`
  (1) BINDS the opened leaf — `xs[pathPos steps]? = some leaf` (a different claimed leaf under
      the same root is two distinct child pairs under one `mapNode` image at some level, i.e. a
      Poseidon2 collision — the same peel as `OodCommitmentBinding.merkleRecomputeZ_binds`), and
  (2) FORCES THE UPDATE — the SAME siblings recompute any replacement `leaf'` to the root of
      `xs.set (pathPos steps) leaf'` (CR pins every sibling to the true subtree root, so the
      write's post-root column is the genuine updated commitment, not a forgery).
Proven by ONE induction on the path, peeling `mapNode_injective` per level. -/
theorem pathRecompute_binds_updates (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    ∀ (steps : List (Bool × ℤ)) (xs : List ℤ) (leaf : ℤ),
      xs.length = 2 ^ steps.length →
      pathRecompute hash leaf steps = perfectRoot hash steps.length xs →
      xs[pathPos steps]? = some leaf ∧
      ∀ leaf', pathRecompute hash leaf' steps
        = perfectRoot hash steps.length (xs.set (pathPos steps) leaf') := by
  intro steps
  induction steps with
  | nil =>
    intro xs leaf hlen hroot
    simp only [List.length_nil, pow_zero] at hlen
    obtain ⟨x, rfl⟩ : ∃ x, xs = [x] := by
      cases xs with
      | nil => simp at hlen
      | cons a t =>
        cases t with
        | nil => exact ⟨a, rfl⟩
        | cons b t' => simp at hlen
    have hx : leaf = x := hroot
    constructor
    · simp [pathPos, hx]
    · intro leaf'; rfl
  | cons step rest ih =>
    obtain ⟨b, sib⟩ := step
    intro xs leaf hlen hroot
    simp only [List.length_cons] at hlen
    have hp2 : 2 ^ (rest.length + 1) = 2 ^ rest.length + 2 ^ rest.length := by
      rw [pow_succ]; ring
    obtain ⟨L, R, rfl, hL, hR⟩ :
        ∃ L R : List ℤ, xs = L ++ R ∧ L.length = 2 ^ rest.length
          ∧ R.length = 2 ^ rest.length := by
      refine ⟨xs.take (2 ^ rest.length), xs.drop (2 ^ rest.length),
        (List.take_append_drop _ _).symm, ?_, ?_⟩
      · rw [List.length_take]; omega
      · rw [List.length_drop]; omega
    have hposlt := pathPos_lt rest
    cases b with
    | false =>
      simp only [pathRecompute, List.length_cons] at hroot
      rw [perfectRoot_append hash rest.length L R hL hR] at hroot
      obtain ⟨hrec, hsib⟩ := mapNode_injective hash hCR hroot
      obtain ⟨hmem, hupd⟩ := ih L leaf hL hrec
      constructor
      · simp only [pathPos]
        rw [List.getElem?_append_left (by omega)]
        exact hmem
      · intro leaf'
        simp only [pathRecompute, pathPos, List.length_cons]
        rw [set_append_left' L R _ _ (by omega)]
        rw [perfectRoot_append hash rest.length _ R (by rw [List.length_set]; exact hL) hR]
        rw [hupd leaf', hsib]
    | true =>
      simp only [pathRecompute, List.length_cons] at hroot
      rw [perfectRoot_append hash rest.length L R hL hR] at hroot
      obtain ⟨hsib, hrec⟩ := mapNode_injective hash hCR hroot
      obtain ⟨hmem, hupd⟩ := ih R leaf hR hrec
      constructor
      · simp only [pathPos]
        rw [List.getElem?_append_right (by omega)]
        rw [show 2 ^ rest.length + pathPos rest - L.length = pathPos rest by omega]
        exact hmem
      · intro leaf'
        simp only [pathRecompute, pathPos, List.length_cons]
        rw [show 2 ^ rest.length + pathPos rest = L.length + pathPos rest by omega]
        rw [set_append_right' L R _ _]
        rw [perfectRoot_append hash rest.length L _ hL (by rw [List.length_set]; exact hR)]
        rw [hupd leaf', hsib]

/-! ## §3 — from a bound leaf to the HEAP opening (the sorted-map decode). -/

/-- The heap leaf `hash[addr, value]` is injective under CR (the entry cannot be forged inside
its digest). -/
theorem leafOf_injective (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {e₁ e₂ : ℤ × ℤ} (h : Heap.leafOf hash e₁ = Heap.leafOf hash e₂) : e₁ = e₂ := by
  obtain ⟨a₁, b₁⟩ := e₁
  obtain ⟨a₂, b₂⟩ := e₂
  have hl := hCR _ _ h
  simp only [List.cons.injEq, and_true] at hl
  simp_all

/-- A positional entry of a SORTED heap IS its `get`: `h[p]? = some (k, v)` ⟹
`Heap.get h k = some v` (strict sortedness makes the match unique). -/
theorem get_eq_some_of_getElem? :
    ∀ {h : Heap.FeltHeap} {p : Nat} {k v : ℤ},
      Heap.SortedKeys h → h[p]? = some (k, v) → Heap.get h k = some v := by
  intro h
  induction h with
  | nil => intro p k v _ he; simp at he
  | cons hd t ih =>
    intro p k v hs he
    obtain ⟨k', v'⟩ := hd
    cases p with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he
      injection he with h1 h2
      subst h1; subst h2
      exact Heap.get_cons_self k' v' t
    | succ q =>
      simp only [List.getElem?_cons_succ] at he
      have hmem : (k, v) ∈ t := List.mem_of_getElem? he
      have hk : k' < k :=
        Heap.sortedKeys_head_lt hs k (List.mem_map.mpr ⟨_, hmem, rfl⟩)
      rw [Heap.get_cons_ne v' t hk.ne']
      exact ih (Heap.sortedKeys_tail hs) he

/-- Two consecutive positions split the list around them (helper for the gap decode). -/
theorem split_of_getElem?_pair {α : Type*} :
    ∀ (l : List α) (p : Nat) (x y : α),
      l[p]? = some x → l[p + 1]? = some y → ∃ pre post, l = pre ++ x :: y :: post := by
  intro l
  induction l with
  | nil => intro p x y hx _; simp at hx
  | cons a t ih =>
    intro p x y hx hy
    cases p with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      simp only [List.getElem?_cons_succ] at hy
      cases t with
      | nil => simp at hy
      | cons b t' =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
        subst hy
        exact ⟨[], t', rfl⟩
    | succ q =>
      simp only [List.getElem?_cons_succ] at hx hy
      obtain ⟨pre, post, rfl⟩ := ih q x y hx hy
      exact ⟨a :: pre, post, rfl⟩

/-- **Adjacent positions give an `Adjacent` key bracket** — two consecutive heap entries are
consecutive on the key spine, exactly the `NonMembership.Adjacent` witness `get_none_of_gap`
consumes. The deployed gap opening (two adjacent-position paths) decodes to the proven sorted
bracketing with ZERO new combinatorics. -/
theorem adjacent_of_getElem?_pair {h : Heap.FeltHeap} {p : Nat} {klo vlo khi vhi : ℤ}
    (hlo : h[p]? = some (klo, vlo)) (hhi : h[p + 1]? = some (khi, vhi)) :
    Dregg2.Crypto.NonMembership.Adjacent (Heap.keys h) klo khi := by
  obtain ⟨pre, post, rfl⟩ := split_of_getElem?_pair h p _ _ hlo hhi
  exact ⟨pre.map Prod.fst, post.map Prod.fst, by simp [Heap.keys]⟩

/-- **The in-place update decode**: on a SORTED heap whose position `p` holds key `k`,
`Heap.set h k v` IS the positional `List.set` — the path's update direction lands exactly on the
sorted insert-or-update semantics. -/
theorem heapSet_eq_listSet :
    ∀ {h : Heap.FeltHeap} {p : Nat} {k vOld : ℤ},
      Heap.SortedKeys h → h[p]? = some (k, vOld) → ∀ v : ℤ,
        Heap.set h k v = h.set p (k, v) := by
  intro h
  induction h with
  | nil => intro p k vOld _ he _; simp at he
  | cons hd t ih =>
    intro p k vOld hs he v
    obtain ⟨k', v'⟩ := hd
    cases p with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he
      injection he with h1 h2
      subst h1
      simp [Heap.set]
    | succ q =>
      simp only [List.getElem?_cons_succ] at he
      have hmem : (k, vOld) ∈ t := List.mem_of_getElem? he
      have hk : k' < k :=
        Heap.sortedKeys_head_lt hs k (List.mem_map.mpr ⟨_, hmem, rfl⟩)
      simp only [Heap.set]
      rw [if_neg (not_lt.mpr hk.le), if_neg hk.ne']
      rw [ih (Heap.sortedKeys_tail hs) he v]
      rfl

/-! ## §4 — the per-kind OPENERS: gates in, `opensToMerkle`/`writesToMerkle` out (∀ depth). -/

/-- **`.read` opener** — a path recomputing the row's `(key, value)` leaf to the committed root
of a canonical heap FORCES the membership opening: the row cannot claim a value the heap does not
hold at that key (a lie is a collision). -/
theorem opensToMerkle_of_path (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (dep : Nat)
    {r k v : ℤ} (h : Heap.FeltHeap) (hs : Heap.SortedKeys h) (hlen : h.length = 2 ^ dep)
    (hroot : mapRoot hash dep h = r)
    (steps : List (Bool × ℤ)) (hsl : steps.length = dep)
    (hpath : pathRecompute hash (Heap.leafOf hash (k, v)) steps = r) :
    opensToMerkle hash dep r k (some v) := by
  subst hroot
  have hbind := (pathRecompute_binds_updates hash hCR steps (h.map (Heap.leafOf hash))
    (Heap.leafOf hash (k, v))
    (by rw [List.length_map, hlen, hsl]) (by rw [hsl]; exact hpath)).1
  simp only [List.getElem?_map] at hbind
  cases he : h[pathPos steps]? with
  | none => rw [he] at hbind; simp at hbind
  | some e =>
    rw [he] at hbind
    simp only [Option.map_some, Option.some.injEq] at hbind
    obtain rfl := leafOf_injective hash hCR hbind
    exact ⟨h, hs, hlen, rfl, get_eq_some_of_getElem? hs he⟩

/-- **`.absent` opener (the gap arm)** — TWO paths at CONSECUTIVE positions, opening leaves whose
keys strictly bracket the row's key, FORCE the non-membership opening: the committed root pins
both bracket leaves, position adjacency pins spine adjacency, and the proven sorted bracketing
(`Heap.get_none_of_gap` = `sorted_gap_excludes`) excludes the key. The deployed double-spend
tooth's opening, derived. -/
theorem opensToMerkle_none_of_bracket (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep : Nat) {r k : ℤ} (h : Heap.FeltHeap) (hs : Heap.SortedKeys h)
    (hlen : h.length = 2 ^ dep) (hroot : mapRoot hash dep h = r)
    (stepsLo stepsHi : List (Bool × ℤ)) {klo vlo khi vhi : ℤ}
    (hlLo : stepsLo.length = dep) (hlHi : stepsHi.length = dep)
    (hadj : pathPos stepsHi = pathPos stepsLo + 1)
    (hpathLo : pathRecompute hash (Heap.leafOf hash (klo, vlo)) stepsLo = r)
    (hpathHi : pathRecompute hash (Heap.leafOf hash (khi, vhi)) stepsHi = r)
    (hklo : klo < k) (hkhi : k < khi) :
    opensToMerkle hash dep r k none := by
  subst hroot
  have hbindLo := (pathRecompute_binds_updates hash hCR stepsLo (h.map (Heap.leafOf hash))
    (Heap.leafOf hash (klo, vlo))
    (by rw [List.length_map, hlen, hlLo]) (by rw [hlLo]; exact hpathLo)).1
  have hbindHi := (pathRecompute_binds_updates hash hCR stepsHi (h.map (Heap.leafOf hash))
    (Heap.leafOf hash (khi, vhi))
    (by rw [List.length_map, hlen, hlHi]) (by rw [hlHi]; exact hpathHi)).1
  simp only [List.getElem?_map] at hbindLo hbindHi
  cases heLo : h[pathPos stepsLo]? with
  | none => rw [heLo] at hbindLo; simp at hbindLo
  | some eLo =>
    rw [heLo] at hbindLo
    simp only [Option.map_some, Option.some.injEq] at hbindLo
    obtain rfl := leafOf_injective hash hCR hbindLo
    cases heHi : h[pathPos stepsHi]? with
    | none => rw [heHi] at hbindHi; simp at hbindHi
    | some eHi =>
      rw [heHi] at hbindHi
      simp only [Option.map_some, Option.some.injEq] at hbindHi
      obtain rfl := leafOf_injective hash hCR hbindHi
      rw [hadj] at heHi
      exact ⟨h, hs, hlen, rfl,
        Heap.get_none_of_gap h klo khi k hs (adjacent_of_getElem?_pair heLo heHi) hklo hkhi⟩

/-- **`.write`/`.insert` opener** — an old-leaf path to the pre-root plus the SAME siblings
recomputing the new `(key, value)` leaf to the post-root column FORCE the write opening: the
post-root IS `mapRoot (Heap.set h key value)` (the update direction of the binding law pins every
sibling, so a frozen or forged post-root is a collision), and the opened old leaf pins the key
present so the sorted insert-or-update is the in-place positional update. -/
theorem writesToMerkle_of_path (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (dep : Nat)
    {r k v r' : ℤ} (h : Heap.FeltHeap) (hs : Heap.SortedKeys h) (hlen : h.length = 2 ^ dep)
    (hroot : mapRoot hash dep h = r)
    (steps : List (Bool × ℤ)) (vOld : ℤ) (hsl : steps.length = dep)
    (hpathOld : pathRecompute hash (Heap.leafOf hash (k, vOld)) steps = r)
    (hpathNew : pathRecompute hash (Heap.leafOf hash (k, v)) steps = r') :
    writesToMerkle hash dep r k v r' := by
  subst hroot
  obtain ⟨hmem, hupd⟩ := pathRecompute_binds_updates hash hCR steps (h.map (Heap.leafOf hash))
    (Heap.leafOf hash (k, vOld))
    (by rw [List.length_map, hlen, hsl]) (by rw [hsl]; exact hpathOld)
  simp only [List.getElem?_map] at hmem
  cases he : h[pathPos steps]? with
  | none => rw [he] at hmem; simp at hmem
  | some e =>
    rw [he] at hmem
    simp only [Option.map_some, Option.some.injEq] at hmem
    obtain rfl := leafOf_injective hash hCR hmem
    have hkmem : k ∈ Heap.keys h :=
      List.mem_map.mpr ⟨_, List.mem_of_getElem? he, rfl⟩
    have hnew : r' = mapRoot hash dep (Heap.set h k v) := by
      rw [← hpathNew, heapSet_eq_listSet hs he v]
      have h2 := hupd (Heap.leafOf hash (k, v))
      rw [hsl] at h2
      calc pathRecompute hash (Heap.leafOf hash (k, v)) steps
          = perfectRoot hash dep
              ((h.map (Heap.leafOf hash)).set (pathPos steps) (Heap.leafOf hash (k, v))) := h2
        _ = perfectRoot hash dep
              ((h.set (pathPos steps) (k, v)).map (Heap.leafOf hash)) := by
              rw [map_set']
        _ = mapRoot hash dep (h.set (pathPos steps) (k, v)) := rfl
    exact ⟨h, hs, hlen,
      by rw [Heap.length_set_mem h k v hs hkmem]; exact hlen, rfl, hnew⟩

/-! ## §5 — THE GATE MODEL (∀ d) and THE MAPOPS-AIR LAW.

`ReconcileGatesAt` is what the deployed `Ir2Air::MapOps` AIR accepts for ONE fired map-op row,
depth-generic (`dep`; the deployment pins `MAP_TREE_DEPTH = 16`): the committed canonical heap
behind the row's pre-root column (the knowledge-extraction premise — the prover's
`CanonicalHeapTree`, NAMED per the header) plus, per op kind, the path-recompute GATES. The LAW
then DERIVES `MapOp.holdsAt` — the row's columns are forced truthful, never assumed. -/

/-- The deployed map-reconcile gate acceptance for one map-op row (depth-generic). -/
def ReconcileGatesAt (hash : List ℤ → ℤ) (dep : Nat) (a : Assignment) (m : MapOp) : Prop :=
  ∃ h : Heap.FeltHeap,
    Heap.SortedKeys h ∧ h.length = 2 ^ dep ∧
    mapRoot hash dep h = (m.root 0).eval a ∧
    match m.op with
    | .read =>
        (∃ steps : List (Bool × ℤ), steps.length = dep ∧
            pathRecompute hash (Heap.leafOf hash (m.key.eval a, m.value.eval a)) steps
              = (m.root 0).eval a)
        ∧ (m.newRoot 0).eval a = (m.root 0).eval a
    | .absent =>
        (∃ (stepsLo stepsHi : List (Bool × ℤ)) (klo vlo khi vhi : ℤ),
            stepsLo.length = dep ∧ stepsHi.length = dep ∧
            pathPos stepsHi = pathPos stepsLo + 1 ∧
            pathRecompute hash (Heap.leafOf hash (klo, vlo)) stepsLo = (m.root 0).eval a ∧
            pathRecompute hash (Heap.leafOf hash (khi, vhi)) stepsHi = (m.root 0).eval a ∧
            klo < m.key.eval a ∧ m.key.eval a < khi)
        ∧ (m.newRoot 0).eval a = (m.root 0).eval a
    | .write =>
        ∃ (steps : List (Bool × ℤ)) (vOld : ℤ), steps.length = dep ∧
          pathRecompute hash (Heap.leafOf hash (m.key.eval a, vOld)) steps
            = (m.root 0).eval a ∧
          pathRecompute hash (Heap.leafOf hash (m.key.eval a, m.value.eval a)) steps
            = (m.newRoot 0).eval a
    | .insert =>
        ∃ (steps : List (Bool × ℤ)) (vOld : ℤ), steps.length = dep ∧
          pathRecompute hash (Heap.leafOf hash (m.key.eval a, vOld)) steps
            = (m.root 0).eval a ∧
          pathRecompute hash (Heap.leafOf hash (m.key.eval a, m.value.eval a)) steps
            = (m.newRoot 0).eval a

/-- **The gates force the opening (depth-generic core).** For every op kind, accepted
map-reconcile gate data yields the exact `opensToMerkle`/`writesToMerkle` denotation of the
row's evaluated columns — the per-kind openers dispatched. -/
theorem reconcileGates_force_opening (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep : Nat) (a : Assignment) (m : MapOp) (hg : ReconcileGatesAt hash dep a m) :
    (match m.op with
     | .read =>
        opensToMerkle hash dep ((m.root 0).eval a) (m.key.eval a) (some (m.value.eval a))
        ∧ (m.newRoot 0).eval a = (m.root 0).eval a
     | .absent =>
        opensToMerkle hash dep ((m.root 0).eval a) (m.key.eval a) none
        ∧ (m.newRoot 0).eval a = (m.root 0).eval a
     | .write =>
        writesToMerkle hash dep ((m.root 0).eval a) (m.key.eval a) (m.value.eval a)
          ((m.newRoot 0).eval a)
     | .insert =>
        writesToMerkle hash dep ((m.root 0).eval a) (m.key.eval a) (m.value.eval a)
          ((m.newRoot 0).eval a)) := by
  obtain ⟨h, hs, hlen, hroot, hgates⟩ := hg
  cases hop : m.op with
  | read =>
    rw [hop] at hgates
    obtain ⟨⟨steps, hsl, hpath⟩, hnr⟩ := hgates
    exact ⟨opensToMerkle_of_path hash hCR dep h hs hlen hroot steps hsl hpath, hnr⟩
  | absent =>
    rw [hop] at hgates
    obtain ⟨⟨sLo, sHi, klo, vlo, khi, vhi, hlLo, hlHi, hposadj, hpLo, hpHi, hklo, hkhi⟩,
      hnr⟩ := hgates
    exact ⟨opensToMerkle_none_of_bracket hash hCR dep h hs hlen hroot sLo sHi
      hlLo hlHi hposadj hpLo hpHi hklo hkhi, hnr⟩
  | write =>
    rw [hop] at hgates
    obtain ⟨steps, vOld, hsl, hpOld, hpNew⟩ := hgates
    exact writesToMerkle_of_path hash hCR dep h hs hlen hroot steps vOld hsl hpOld hpNew
  | insert =>
    rw [hop] at hgates
    obtain ⟨steps, vOld, hsl, hpOld, hpNew⟩ := hgates
    exact writesToMerkle_of_path hash hCR dep h hs hlen hroot steps vOld hsl hpOld hpNew

/-- **THE MAPOPS-AIR LAW (per row, deployed depth).** The deployed map-reconcile gates (at
`MAP_TREE_DEPTH`) plus the single named CR floor FORCE the row denotation `MapOp.holdsAt` — the
existential `opensTo`/`writesTo` — for ANY map op on ANY row. The `.mapOp` twin of
`busModel_forces_lookup_holds`. -/
theorem mapOp_holds_of_mapReconcile (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (env : VmRowEnv) (m : MapOp)
    (hg : m.guard.eval env.loc = 1 → ReconcileGatesAt hash MAP_TREE_DEPTH env.loc m) :
    MapOp.holdsAt hash env m := by
  intro hguard
  have h := reconcileGates_force_opening hash hCR MAP_TREE_DEPTH env.loc m (hg hguard)
  revert h
  cases m.op <;> exact fun h => h

/-- **The per-trace map-reconcile model (∀ d)**: every declared map op whose guard fires on a row
has accepted gate data there — what the deployed `Ir2Air::MapOps` AIR checks over the whole
trace, read off ANY descriptor's `mapOpsOf`. -/
def MapReconcileModelOk (hash : List ℤ → ℤ) (d : EffectVmDescriptor2) (t : VmTrace) : Prop :=
  ∀ i < t.rows.length, ∀ m ∈ mapOpsOf d,
    m.guard.eval (envAt t i).loc = 1 → ReconcileGatesAt hash MAP_TREE_DEPTH (envAt t i).loc m

/-- **THE `.mapOp` ARM, ∀ d (`mapOpsArm_of_modeler`).** For ANY descriptor, the map-reconcile
model + CR discharge the ENTIRE `.mapOp` arm of `Satisfied2.rowConstraints`: every declared
`.mapOp` holds on every row. The 7 mapOp effects' Species-A leg
(`docs/reference/MEMORY-LEGS-SCOPE.md` §0), now produced by the modeler for all of them at once —
their per-effect teeth (`*_grow_gate_forces_set_insert`, `*_forces_write`,
`heapWrite_splice_forced`) consume `Satisfied2` downstream unchanged. -/
theorem mapOpsArm_of_modeler (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (d : EffectVmDescriptor2) (t : VmTrace) (hok : MapReconcileModelOk hash d t) :
    ∀ i < t.rows.length, ∀ m : MapOp, VmConstraint2.mapOp m ∈ d.constraints →
      MapOp.holdsAt hash (envAt t i) m :=
  fun i hi m hm => mapOp_holds_of_mapReconcile hash hCR (envAt t i) m
    (fun hg => hok i hi m (mem_mapOpsOf.mpr hm) hg)

/-! ## §6 — the ASSEMBLY: the graduated+mapOps `hbus` and the full `Satisfied2` for the 7-effect
shape. -/

/-- **The graduated+mapOps `hbus` splitter (∀ d).** For any descriptor whose non-arithmetic
constraints are `.lookup`s OR `.mapOp`s (the shape of all 7 memory-touching mapOp effects —
graduated hashing/ranges plus the kernel-set grow gates), per-table LogUp bus models + the
map-reconcile model discharge the FULL non-arith arm of `rowConstraints` — the mild
generalization of `hbus_of_busModels` MEMORY-LEGS-SCOPE §1 calls for. -/
theorem hbus_of_busModels_and_mapModel {F : Type*} [Field F] [DecidableEq F]
    (hash : List ℤ → ℤ) (fp : List ℤ → F) (embed : ℤ → F)
    (d : EffectVmDescriptor2) (t : VmTrace)
    (hCR : Poseidon2SpongeCR hash)
    (hshape : ∀ c ∈ d.constraints, ¬ isArith c →
        (∃ l : Lookup, c = .lookup l) ∨ (∃ m : MapOp, c = .mapOp m))
    (hlok : ∀ l : Lookup, VmConstraint2.lookup l ∈ d.constraints →
        ∃ mult : List ℕ, BusModelOk fp embed d t l.table mult)
    (hmap : MapReconcileModelOk hash d t) :
    ∀ i < t.rows.length, ∀ c ∈ d.constraints, ¬ isArith c →
      c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length) := by
  intro i hi c hc hA
  rcases hshape c hc hA with ⟨l, rfl⟩ | ⟨m, rfl⟩
  · obtain ⟨mult, hm⟩ := hlok l hc
    exact busModel_forces_lookup_holds fp embed d t l.table mult hm i hi l
      (mem_lookupsInto.mpr ⟨hc, rfl⟩)
  · exact mapOpsArm_of_modeler hash hCR d t hmap i hi m hc

/-- A descriptor with no declared mem ops gathers an EMPTY memory log on every trace (the
`rfl`-adjacent lemma the 7 mapOp effects need — `.mapOp` appends contribute nothing to `memLog`). -/
theorem memLog_nil_of_no_memOps (d : EffectVmDescriptor2) (t : VmTrace)
    (h : memOpsOf d = []) : memLog d t = [] := by
  unfold memLog
  rw [h]
  simp

/-- **The full `Satisfied2` for the 7-effect shape (∀ d), modelers in.** AIR quotient acceptance
(`MainAirAcceptF`) + the LogUp bus models + the MAP-RECONCILE model + the ONE named CR floor give
`Satisfied2` for any graduated, mem-op-free, mapOp-carrying descriptor — with exactly TWO carried
assembly facts, each NAMED (the same species as transferV3's emptiness pair,
`AirLegsDischarged.lean:30-35`):
  * `hMemEmpty` — the committed memory table is empty (the descriptor declares no mem ops);
  * `hMapTF` — SPECIES B, `mapTableFaithful`: the committed mapOps table IS the gathered
    `mapLog d t` (`mapLog_eq_fired` gives its fired-extraction face). Part B of the split —
    a table-ASSEMBLY fact, not an AIR consequence; carried, not laundered.
Everything else — including the whole `.mapOp` row arm, previously a bare carried premise — is
DERIVED. -/
theorem airAccept_forces_satisfied2_of_modelers {F : Type*} [Field F] [DecidableEq F]
    (hash : List ℤ → ℤ) (fp : List ℤ → F) (embed : ℤ → F)
    (d : EffectVmDescriptor2) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (t : VmTrace)
    (hAir : MainAirAcceptF d t)
    (hCR : Poseidon2SpongeCR hash)
    (hshape : ∀ c ∈ d.constraints, ¬ isArith c →
        (∃ l : Lookup, c = .lookup l) ∨ (∃ m : MapOp, c = .mapOp m))
    (hlok : ∀ l : Lookup, VmConstraint2.lookup l ∈ d.constraints →
        ∃ mult : List ℕ, BusModelOk fp embed d t l.table mult)
    (hmap : MapReconcileModelOk hash d t)
    (hNoHash : d.hashSites = []) (hNoRange : d.ranges = [])
    (hNoMemOps : memOpsOf d = [])
    (hMemEmpty : t.tf .memory = [])
    (hMapTF : t.tf .mapOps = mapLog d t) :
    Satisfied2 hash d minit mfin [] t := by
  have hMemLog := memLog_nil_of_no_memOps d t hNoMemOps
  exact airAccept_forces_satisfied2 hash d minit mfin [] t
    hAir
    (hbus_of_busModels_and_mapModel hash fp embed d t hCR hshape hlok hmap)
    (by intro i _; rw [hNoHash]; trivial)
    (by intro i _ r hr; rw [hNoRange] at hr; simp at hr)
    List.nodup_nil
    (by intro op hop; rw [hMemLog] at hop; simp at hop)
    (by rw [hMemLog]; trivial)
    (by rw [hMemLog]; simp [MemoryChecking.MemCheck, MemoryChecking.initSet,
      MemoryChecking.finalSet, MemoryChecking.readSet, MemoryChecking.writeSetFrom,
      MemoryChecking.boundarySet])
    (by rw [hMemLog, List.map_nil]; exact hMemEmpty)
    hMapTF

#assert_axioms mem_mapOpsOf
#assert_axioms mem_firedMapOpsAt
#assert_axioms mapLog_eq_fired
#assert_axioms pathPos_lt
#assert_axioms perfectRoot_append
#assert_axioms pathRecompute_binds_updates
#assert_axioms leafOf_injective
#assert_axioms get_eq_some_of_getElem?
#assert_axioms adjacent_of_getElem?_pair
#assert_axioms heapSet_eq_listSet
#assert_axioms opensToMerkle_of_path
#assert_axioms opensToMerkle_none_of_bracket
#assert_axioms writesToMerkle_of_path
#assert_axioms reconcileGates_force_opening
#assert_axioms mapOp_holds_of_mapReconcile
#assert_axioms mapOpsArm_of_modeler
#assert_axioms hbus_of_busModels_and_mapModel
#assert_axioms airAccept_forces_satisfied2_of_modelers

/-! ## §7 — NON-VACUITY TEETH (both polarities), at a 2-LEVEL heap (4 leaves — heap-safe;
the deployed `dep = 16` case is the SAME depth-generic theorems applied symbolically), on the
CR-PROVED reference sponge (`Poseidon2Binding.Reference.refSponge_CR` — no unproven hypothesis
in any tooth).

RESPECTING teeth: honest gate data for a `.read`, the `.absent` GAP, and an `.insert` all FIRE
the law into the genuine openings. FORGED teeth: a read claiming a WRONG value, and an insert
whose post-root column is FROZEN at the old root (exactly the
`kernel_set_insert_is_not_forced_by_the_live_descriptor` forgery), admit NO gate data at all —
∀-quantified over every heap/path witness, refuted through the CR collision argument. -/

section Teeth

open Dregg2.Circuit.Poseidon2Binding.Reference (refSponge refSponge_CR)

/-- The 2-level toy heap: `4 = 2^2` sorted leaves. -/
def toyHeap : Heap.FeltHeap := [(10, 1), (20, 2), (30, 3), (40, 4)]

theorem toyHeap_sorted : Heap.SortedKeys toyHeap := by
  norm_num [toyHeap, Heap.SortedKeys, Heap.keys, List.pairwise_cons]

/-- The genuine sorted update `20 ↦ 9` of the toy heap (in place — key present). -/
def toyGrown : Heap.FeltHeap := [(10, 1), (20, 9), (30, 3), (40, 4)]

/-- `toyGrown` IS `Heap.set toyHeap 20 9` — the opened write is the real sorted-map update. -/
theorem toyGrown_eq : Heap.set toyHeap 20 9 = toyGrown := by decide

/-- The opened-leaf path for position 1 (the `(20, ·)` leaf): top step LEFT (sibling = the right
half's node), bottom step RIGHT (sibling = the `(10,1)` leaf). -/
def toySteps (hash : List ℤ → ℤ) : List (Bool × ℤ) :=
  [(false, mapNode hash (Heap.leafOf hash (30, 3)) (Heap.leafOf hash (40, 4))),
   (true, Heap.leafOf hash (10, 1))]

/-- The path for position 2 (the `(30, 3)` leaf): top RIGHT (sibling = the left half's node),
bottom LEFT (sibling = the `(40,4)` leaf) — the high bracket of the gap tooth. -/
def toyStepsHi (hash : List ℤ → ℤ) : List (Bool × ℤ) :=
  [(true, mapNode hash (Heap.leafOf hash (10, 1)) (Heap.leafOf hash (20, 2))),
   (false, Heap.leafOf hash (40, 4))]

/-- The position-1 path recomputes ANY `(20, v)` leaf to the root of the correspondingly-updated
heap (at `v = 2`, the committed `toyHeap` root; at `v = 9`, the `toyGrown` root) — structural,
for every hash. -/
theorem toySteps_recompute (hash : List ℤ → ℤ) (v : ℤ) :
    pathRecompute hash (Heap.leafOf hash (20, v)) (toySteps hash)
      = mapRoot hash 2 [(10, 1), (20, v), (30, 3), (40, 4)] := rfl

/-- The position-2 path recomputes the `(30, 3)` leaf to the committed `toyHeap` root. -/
theorem toyStepsHi_recompute (hash : List ℤ → ℤ) :
    pathRecompute hash (Heap.leafOf hash (30, 3)) (toyStepsHi hash)
      = mapRoot hash 2 toyHeap := rfl

/-- The toy read op: root/key/value/newRoot on wires 0/1/2/3, always-firing guard. -/
def toyReadOp : MapOp :=
  { guard := .const 1, root := fun _ => .var 0, key := .var 1, value := .var 2
  , newRoot := fun _ => .var 3, op := .read }

/-- The toy absent op (same wires, `.absent`). -/
def toyAbsentOp : MapOp :=
  { guard := .const 1, root := fun _ => .var 0, key := .var 1, value := .var 2
  , newRoot := fun _ => .var 3, op := .absent }

/-- The toy insert op (same wires, `.insert`). -/
def toyInsertOp : MapOp :=
  { guard := .const 1, root := fun _ => .var 0, key := .var 1, value := .var 2
  , newRoot := fun _ => .var 3, op := .insert }

/-- An honest READ row: root/newRoot carry the committed toy root, key 20, value 2. -/
def toyReadEnv (hash : List ℤ → ℤ) : Assignment := fun c =>
  if c = 0 then mapRoot hash 2 toyHeap
  else if c = 1 then 20 else if c = 2 then 2
  else if c = 3 then mapRoot hash 2 toyHeap else 0

/-- A FORGED read row: same root, same key 20, but the value column claims 99. -/
def toyForgedReadEnv (hash : List ℤ → ℤ) : Assignment := fun c =>
  if c = 0 then mapRoot hash 2 toyHeap
  else if c = 1 then 20 else if c = 2 then 99
  else if c = 3 then mapRoot hash 2 toyHeap else 0

/-- An honest ABSENT row: key 25 (strictly between the present 20 and 30). -/
def toyAbsentEnv (hash : List ℤ → ℤ) : Assignment := fun c =>
  if c = 0 then mapRoot hash 2 toyHeap
  else if c = 1 then 25 else if c = 2 then 0
  else if c = 3 then mapRoot hash 2 toyHeap else 0

/-- An honest INSERT row: key 20 ↦ 9; the post-root column carries the GROWN root. -/
def toyInsertEnv (hash : List ℤ → ℤ) : Assignment := fun c =>
  if c = 0 then mapRoot hash 2 toyHeap
  else if c = 1 then 20 else if c = 2 then 9
  else if c = 3 then mapRoot hash 2 toyGrown else 0

/-- A FROZEN insert row: same write claim, but the post-root column keeps the OLD root — the
exact `kernel_set_insert_is_not_forced_by_the_live_descriptor` forgery shape. -/
def toyFrozenInsertEnv (hash : List ℤ → ℤ) : Assignment := fun c =>
  if c = 0 then mapRoot hash 2 toyHeap
  else if c = 1 then 20 else if c = 2 then 9
  else if c = 3 then mapRoot hash 2 toyHeap else 0

/-- Honest READ gate data exists (for every hash): the committed heap + the position-1 path. -/
theorem toy_read_gates (hash : List ℤ → ℤ) :
    ReconcileGatesAt hash 2 (toyReadEnv hash) toyReadOp :=
  ⟨toyHeap, toyHeap_sorted, rfl, rfl,
    ⟨⟨toySteps hash, rfl, toySteps_recompute hash 2⟩, rfl⟩⟩

/-- Honest ABSENT gate data exists: the two bracket paths at adjacent positions 1 and 2, keys
`20 < 25 < 30`. -/
theorem toy_absent_gates (hash : List ℤ → ℤ) :
    ReconcileGatesAt hash 2 (toyAbsentEnv hash) toyAbsentOp :=
  ⟨toyHeap, toyHeap_sorted, rfl, rfl,
    ⟨⟨toySteps hash, toyStepsHi hash, 20, 2, 30, 3, rfl, rfl, rfl,
      toySteps_recompute hash 2, toyStepsHi_recompute hash,
      by norm_num [toyAbsentOp, toyAbsentEnv, EmittedExpr.eval],
      by norm_num [toyAbsentOp, toyAbsentEnv, EmittedExpr.eval]⟩, rfl⟩⟩

/-- Honest INSERT gate data exists: the old-leaf path to the pre-root, the new-leaf path to the
grown post-root. -/
theorem toy_insert_gates (hash : List ℤ → ℤ) :
    ReconcileGatesAt hash 2 (toyInsertEnv hash) toyInsertOp :=
  ⟨toyHeap, toyHeap_sorted, rfl, rfl,
    ⟨toySteps hash, 2, rfl, toySteps_recompute hash 2, toySteps_recompute hash 9⟩⟩

/-- **RESPECTING TOOTH (read FIRES).** On the CR-proved sponge, the law turns the honest read
gate data into the GENUINE membership opening: the committed root opens key 20 to `some 2` — the
heap's real value, produced through the whole path-binding extraction. Nothing assumed. -/
theorem toy_read_fires :
    opensToMerkle refSponge 2 (mapRoot refSponge 2 toyHeap) 20 (some 2) :=
  (reconcileGates_force_opening refSponge refSponge_CR 2 (toyReadEnv refSponge) toyReadOp
    (toy_read_gates refSponge)).1

/-- **RESPECTING TOOTH (the GAP arm FIRES).** The two bracket paths force the genuine
NON-membership opening of key 25 — the deployed double-spend/freshness (`.absent`) denotation,
derived from the gates. -/
theorem toy_absent_fires :
    opensToMerkle refSponge 2 (mapRoot refSponge 2 toyHeap) 25 none :=
  (reconcileGates_force_opening refSponge refSponge_CR 2 (toyAbsentEnv refSponge) toyAbsentOp
    (toy_absent_gates refSponge)).1

/-- **RESPECTING TOOTH (a real map insert forces the write opening).** The insert gate data
forces `writesToMerkle`: the post-root IS the root of the genuine sorted update
(`toyGrown = Heap.set toyHeap 20 9`, `toyGrown_eq`). -/
theorem toy_insert_fires :
    writesToMerkle refSponge 2 (mapRoot refSponge 2 toyHeap) 20 9
      (mapRoot refSponge 2 toyGrown) :=
  reconcileGates_force_opening refSponge refSponge_CR 2 (toyInsertEnv refSponge) toyInsertOp
    (toy_insert_gates refSponge)

/-- **FORGED TOOTH 1 (a lying read value BITES).** Under CR there is NO gate data — for ANY
heap and ANY path — opening the toy root at key 20 to the forged value 99: the law would force
`opensTo … (some 99)`, the honest tooth forces `some 2`, and opening FUNCTIONALITY (the CR
collision argument, `opensToMerkle_functional`) refutes. The forger has no witness. -/
theorem toy_forged_read_bites :
    ¬ ReconcileGatesAt refSponge 2 (toyForgedReadEnv refSponge) toyReadOp := by
  intro hg
  have h := (reconcileGates_force_opening refSponge refSponge_CR 2
    (toyForgedReadEnv refSponge) toyReadOp hg).1
  have := opensToMerkle_functional refSponge refSponge_CR 2 h toy_read_fires
  norm_num [toyReadOp, toyForgedReadEnv, EmittedExpr.eval] at this

/-- **FORGED TOOTH 2 (the frozen post-root BITES) — path to a different root is UNSAT.** Under
CR there is NO gate data letting the insert claim the write while keeping `newRoot = root` (the
frozen-root forgery `kernel_set_insert_is_not_forced_by_the_live_descriptor` documented): write
FUNCTIONALITY forces the frozen root to EQUAL the grown root, root injectivity forces
`toyHeap = toyGrown` — false. The gates repoint the after-root from a free witness limb into a
FORCED commitment. -/
theorem toy_frozen_insert_bites :
    ¬ ReconcileGatesAt refSponge 2 (toyFrozenInsertEnv refSponge) toyInsertOp := by
  intro hg
  have h := reconcileGates_force_opening refSponge refSponge_CR 2
    (toyFrozenInsertEnv refSponge) toyInsertOp hg
  have heq : mapRoot refSponge 2 toyHeap = mapRoot refSponge 2 toyGrown :=
    writesToMerkle_functional refSponge refSponge_CR 2 h toy_insert_fires
  have : toyHeap = toyGrown := mapRoot_injective refSponge refSponge_CR 2 rfl rfl heq
  exact absurd this (by decide)

-- The openings the teeth force are the heap's REAL lookup semantics (executable face):
#guard Heap.get toyHeap (20 : ℤ) == some 2
#guard Heap.get toyHeap (25 : ℤ) == none
#guard Heap.get toyGrown (20 : ℤ) == some 9
#guard (Heap.set toyHeap 20 9).length == toyHeap.length   -- present key updates in place
-- The two bracket paths sit at ADJACENT positions (the gap gate's index check, executable):
#guard pathPos (toySteps (fun _ => 0)) == 1
#guard pathPos (toyStepsHi (fun _ => 0)) == 2

#assert_axioms toy_read_gates
#assert_axioms toy_absent_gates
#assert_axioms toy_insert_gates
#assert_axioms toy_read_fires
#assert_axioms toy_absent_fires
#assert_axioms toy_insert_fires
#assert_axioms toy_forged_read_bites
#assert_axioms toy_frozen_insert_bites

end Teeth

#check @pathRecompute_binds_updates
#check @mapOp_holds_of_mapReconcile
#check @mapOpsArm_of_modeler
#check @airAccept_forces_satisfied2_of_modelers

/-! ## §8 — THE AAFI TWO-PATH INSERT COLUMN MODEL (`MapKind::AafiInsert`, code 4).

Mirrors `docs/reference/GAP5-AAFI-CUTOVER-PLAN.md` §2 (the AAFI cutover of the append-only
accumulators — nullifier / commitment / revoked sets — to the two-path insert that closes GAP #5's
double-spend). The current per-turn `.insert` opens ONE leaf over ONE shared path against
`new_root` — sound for value-updates (stable position) but NOT for insert (the compacted-array
suffix shifts, no shared pre-image binds the shifted region). AAFI replaces it with the Aztec
INDEXED-Merkle two-path insert at STABLE positions (append-at-free-index), whose leaf is the 3-felt
linked-list node `hash[addr, value, nextAddr]`.

The AAFI row carries TWO INDEPENDENT openings plus the pointer-bracket range gate (§2.2 columns):
  * PATH1 (`MAP_SIB0/DIR0`, repurposed) — the LOW leaf `hash[low.addr, low.value, low.next]` opens
    to the pre-root, and (updated `next := k`) recomputes to the intermediate root `R1` (`MAP_R1`);
  * the RANGE gate `low.addr < k < low.next` (`MAP_RANGE0`) — the pointer bracket that binds `k`
    into the low leaf's real gap (the double-spend tooth: a present / out-of-gap `k` has no
    bracket → UNSAT);
  * PATH2 (`MAP_SIB2_0/DIR2_0`, NEW) — the FREE slot opens EMPTY (`MAP_FREE_EMPTY`) to `R1`
    (no overwrite), and the appended leaf `hash[k, v, low.next]` recomputes to `new_root`.

THE LAW (`aafiInsert_forces_imtInsert`): accepting AAFI gates FORCE `new_root` to be the perfect-
tree root of the digest vector `xs` with EXACTLY two positions changed — the low position updated
to `next := k`, and the free position set to the appended leaf — i.e. the DIGEST-VECTOR FACE of
`IndexedMerkleTree.imtInsert` (step (i) update-low-`nextAddr` + step (ii) append-`(k,v,low_oldNext)`
at a free slot, no shift). Forced through the proven `pathRecompute_binds_updates` (used TWICE: the
low-update leg — `IndexedMerkleTree.imtLowUpdate_binds` is its 3-felt IMT face — and the append
leg), under the single named `Poseidon2SpongeCR` floor. The pointer bracket `low.addr < k < low.next`
survives to the conclusion — the `IndexedMerkleTree.ImtAbsent` witness the sorted-preservation step
consumes.

★ REMAINING WIRE (named, per `feedback-named-seam-is-not-a-hole.md`) — the `imtInsert`-SYMBOL
correspondence and `ImtSorted`-preservation live in `Dregg2.Circuit.IndexedMerkleTree`, NOT here:
that module IMPORTS this file (it opens `pathRecompute`/`pathPos`/`pathRecompute_binds_updates`
from here), so referencing `imtInsert` / `imtInsert_preserves` / `canonicalHeapExtract_of_imt` in
this file is a MODULE-IMPORT CYCLE. This law delivers the two-path forcing at the digest-vector
level (the maximal statement expressible below IMT in the DAG) PLUS the pointer bracket; the bridge
`new_root = perfectRoot (imtToHeap-digest-vector of imtInsert c k v)` ∧ `ImtSorted (imtInsert …)`
(from `imtInsert_preserves` + `reachable_sorted` ⟹ `canonicalHeapExtract_of_imt`) is the one-lemma
follow-up that belongs in `IndexedMerkleTree.lean` (which has both `imtInsert` and this law in
scope). No re-assumption: the forcing here is genuine (`pathRecompute_binds_updates`, twice). -/

/-- **`aafiLeafHash`** — the 3-felt indexed-Merkle leaf digest `hash[addr, value, nextAddr]` (the
deployed `heap_root.rs::HeapLeaf::digest8` at arity 3; the `Dregg2.Circuit.IndexedMerkleTree.imtLeafHash`
twin, restated below IMT in the module DAG). -/
def aafiLeafHash (hash : List ℤ → ℤ) (addr value nextAddr : ℤ) : ℤ := hash [addr, value, nextAddr]

/-- The 3-felt IMT leaf digest BINDS all three fields under CR — a prover cannot forge the pointer
(or address, or value) inside the digest. `Heap.leafOf_injective` / `imtLeafHash_injective` at 3-felt
width, the SAME `Poseidon2SpongeCR` floor. -/
theorem aafiLeafHash_injective (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {a₁ v₁ n₁ a₂ v₂ n₂ : ℤ}
    (h : aafiLeafHash hash a₁ v₁ n₁ = aafiLeafHash hash a₂ v₂ n₂) :
    a₁ = a₂ ∧ v₁ = v₂ ∧ n₁ = n₂ := by
  have hl := hCR _ _ h
  simp only [List.cons.injEq, and_true] at hl
  exact hl

/-- **`AafiGatesAt`** — the deployed `MapKind::AafiInsert` (code 4) gate acceptance for ONE AAFI row
(depth-generic; the deployment pins `MAP_TREE_DEPTH`). Existentially carries the committed digest
vector `xs` behind the pre-root (the knowledge-extraction premise — the prover's `CanonicalHeapTree8`
/ `AafiInsertWitness8`, NAMED like `ReconcileGatesAt`'s `∃ h`), the two paths, and `R1`, and asserts
the four AAFI gates: (a) low-open, (b) pointer-bracket, (c) PATH1 low-update → `R1`,
(d1) PATH2 free-slot-empty, (d2) PATH2 append → `new_root`. -/
def AafiGatesAt (hash : List ℤ → ℤ) (dep : Nat)
    (oldRoot newRoot k v lowAddr lowValue lowNext freeEmpty : ℤ) : Prop :=
  ∃ (R1 : ℤ) (xs : List ℤ) (steps1 steps2 : List (Bool × ℤ)),
    xs.length = 2 ^ dep ∧
    steps1.length = dep ∧
    steps2.length = dep ∧
    pathPos steps1 ≠ pathPos steps2 ∧
    oldRoot = perfectRoot hash dep xs ∧
    -- gate (a): low-leaf open at its STABLE position vs the pre-root (PATH1).
    pathRecompute hash (aafiLeafHash hash lowAddr lowValue lowNext) steps1 = oldRoot ∧
    -- gate (b): the pointer bracket `low.addr < k < low.next`.
    lowAddr < k ∧
    k < lowNext ∧
    -- gate (c): PATH1 low-update (`next := k`) recomputes to R1.
    pathRecompute hash (aafiLeafHash hash lowAddr lowValue k) steps1 = R1 ∧
    -- gate (d1): the free slot was EMPTY under R1 (PATH2, no overwrite).
    pathRecompute hash freeEmpty steps2 = R1 ∧
    -- gate (d2): PATH2 append of `(k, v, low.next)` recomputes to the post-root.
    pathRecompute hash (aafiLeafHash hash k v lowNext) steps2 = newRoot

/-- **`aafiInsert_forces_imtInsert` — THE AAFI LAW.** Under the single named CR floor, an accepting
AAFI row's gates FORCE its `(old_root, new_root, k, v)` to be an `imtInsert` step at the DIGEST-VECTOR
level: there is a committed digest vector `xs` behind `old_root` whose LOW position holds the opened
low leaf, whose free position is EMPTY after the low-update, and whose two-point update (low
`next := k`; append `(k, v, low.next)` at the distinct free slot) has root EXACTLY `new_root`. Forced
by `pathRecompute_binds_updates` used TWICE (PATH1 low → R1, PATH2 free → new_root through R1). The
pointer bracket `low.addr < k < low.next` survives — the `ImtAbsent` witness sorted-preservation
consumes. No re-assumption: the two-point forcing is the proven Merkle-opening extraction. -/
theorem aafiInsert_forces_imtInsert (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (dep : Nat)
    {oldRoot newRoot k v lowAddr lowValue lowNext freeEmpty : ℤ}
    (hg : AafiGatesAt hash dep oldRoot newRoot k v lowAddr lowValue lowNext freeEmpty) :
    ∃ (xs : List ℤ) (p1 p2 : Nat),
      xs.length = 2 ^ dep ∧
      p1 ≠ p2 ∧
      oldRoot = perfectRoot hash dep xs ∧
      xs[p1]? = some (aafiLeafHash hash lowAddr lowValue lowNext) ∧
      (xs.set p1 (aafiLeafHash hash lowAddr lowValue k))[p2]? = some freeEmpty ∧
      newRoot = perfectRoot hash dep
        ((xs.set p1 (aafiLeafHash hash lowAddr lowValue k)).set p2
          (aafiLeafHash hash k v lowNext)) ∧
      lowAddr < k ∧ k < lowNext := by
  obtain ⟨R1, xs, s1, s2, hlen, hl1, hl2, hne, hor, hp1old, hlk, hkn, hp1new, hp2e, hp2app⟩ := hg
  -- PATH1: the low leaf opens to the pre-root, so it is bound and its update lands to R1.
  have e1 : xs.length = 2 ^ s1.length := by rw [hl1]; exact hlen
  have hroot1 : pathRecompute hash (aafiLeafHash hash lowAddr lowValue lowNext) s1
      = perfectRoot hash s1.length xs := by rw [hp1old, hor, hl1]
  obtain ⟨hmem1, hupd1⟩ := pathRecompute_binds_updates hash hCR s1 xs
    (aafiLeafHash hash lowAddr lowValue lowNext) e1 hroot1
  have hR1 : R1 = perfectRoot hash dep
      (xs.set (pathPos s1) (aafiLeafHash hash lowAddr lowValue k)) := by
    rw [← hp1new, hupd1 (aafiLeafHash hash lowAddr lowValue k), hl1]
  -- PATH2: the free slot opens EMPTY to R1, so the append lands to new_root.
  have e2 : (xs.set (pathPos s1) (aafiLeafHash hash lowAddr lowValue k)).length = 2 ^ s2.length := by
    rw [List.length_set, hl2]; exact hlen
  have hroot2 : pathRecompute hash freeEmpty s2
      = perfectRoot hash s2.length
          (xs.set (pathPos s1) (aafiLeafHash hash lowAddr lowValue k)) := by
    rw [hp2e, hR1, hl2]
  obtain ⟨hmem2, hupd2⟩ := pathRecompute_binds_updates hash hCR s2
    (xs.set (pathPos s1) (aafiLeafHash hash lowAddr lowValue k)) freeEmpty e2 hroot2
  have hnew : newRoot = perfectRoot hash dep
      ((xs.set (pathPos s1) (aafiLeafHash hash lowAddr lowValue k)).set (pathPos s2)
        (aafiLeafHash hash k v lowNext)) := by
    rw [← hp2app, hupd2 (aafiLeafHash hash k v lowNext), hl2]
  exact ⟨xs, pathPos s1, pathPos s2, hlen, hne, hor, hmem1, hmem2, hnew, hlk, hkn⟩

/-! ## §8b — THE AAFI COLUMN-WIDTH MIRROR (the DEPLOYED `descriptor_ir2.rs` op=4 block).

The Lean twin of A1's `circuit/src/descriptor_ir2.rs` `MapKind::AafiInsert` (code 4) columns. The
offsets below are pinned to the DEPLOYED `const MAP_*` values — i.e. the values the compiler
EVALUATES the const expressions to (`descriptor_ir2.rs:1845-1869`), the columns the AIR actually
reads — NOT the hand-written `//` comments beside them.

⚠ GROUND-TRUTH NOTE (do not "fix" these to the Rust `//` comments): with `CHIP_OUT_LANES = 8`,
`HEAP_TREE_DEPTH = 16`, `MA_DECOMP_COLS = MA_CMP_COLS = 13`, the const chain evaluates to
`MAP_S=421, MAP_R1=422, MAP_LOW_ADDR=430, MAP_LOW_VALUE=431, MAP_LOW_NEW=432, MAP_LOW_NEW_CHAIN0=440,
MAP_SIB2_0=560, MAP_DIR2_0=688, MAP_FREE_EMPTY=704, MAP_FREE_EMPTY_CHAIN0=712, MAP_A_DEC0=832,
MAP_WIDTH=897`. The `//` comments in descriptor_ir2.rs beside the AAFI block (429, 559, 831, …) are
STALE — off by −1 below `MAP_S`, left over from the pre-`MAP_S` plan layout where `MAP_R1 = 421`.
The compiler ignores comments; the deployed circuit uses the arithmetic, so THIS mirror uses the
arithmetic. (A1 added the degree-1 `MAP_S` selector at `MAP_AAFI_BASE = 421`, forced by the frozen
map-ops degree-4 budget — a `op(op-1)(op-3)` polynomial selector is degree 3. It is pinned to op=4
by three low-degree constraints `s(s-1)=0`, `s·(op-4)=0`, `op(op-1)(op-3)·(1-s)=0`.)

The AAFI region is `[MAP_AAFI_BASE, MAP_WIDTH) = [421, 897) = 476` columns: the 1-felt `MAP_S`
selector at 421 plus the 475-column two-path payload. The `#guard`s pin every offset to the deployed
per-group widths (1,8,1,1,8,120,128,16,8,120,65) so this model AGREES with A1's ACTUAL layout
(WITH `MAP_S`) column-for-column. -/

def MAP_AAFI_BASE : Nat := 421       -- op≤3 layout ends at 421; op=4 columns are byte-disjoint below
def MAP_S : Nat := 421               -- (1)   the degree-1 `is_aafi` selector (op=4), pinned to op=4
def MAP_R1 : Nat := 422              -- (8)   intermediate root after the low update
def MAP_LOW_ADDR : Nat := 430        -- (1)   low_leaf_old.addr  (range lo bound)
def MAP_LOW_VALUE : Nat := 431       -- (1)   low_leaf_old.value
def MAP_LOW_NEW : Nat := 432         -- (8)   low leaf digest after next_addr := k
def MAP_LOW_NEW_CHAIN0 : Nat := 440  -- (120) low_new → R1 over PATH1
def MAP_SIB2_0 : Nat := 560          -- (128) PATH2 siblings (free slot)
def MAP_DIR2_0 : Nat := 688          -- (16)  PATH2 direction bits
def MAP_FREE_EMPTY : Nat := 704      -- (8)   the empty-slot digest, pre-append
def MAP_FREE_EMPTY_CHAIN0 : Nat := 712 -- (120) free_empty → R1 over PATH2
def MAP_RANGE0 : Nat := 832          -- (65)  pointer-bracket range block = MAP_A_DEC0 (3·13 + 2·13)
def MAP_WIDTH_AAFI : Nat := 897      -- = MAP_AAFI_BASE + 476 = 421 + (1 selector + 475 payload)

#guard MAP_AAFI_BASE == 421
#guard MAP_S == MAP_AAFI_BASE       -- the selector IS the first AAFI column (op=4)
#guard MAP_R1 == MAP_S + 1          -- R1 sits AFTER MAP_S (the +1 A2 previously omitted)
#guard MAP_R1 == 422
#guard MAP_LOW_ADDR == MAP_R1 + 8
#guard MAP_LOW_VALUE == MAP_LOW_ADDR + 1
#guard MAP_LOW_NEW == MAP_LOW_VALUE + 1
#guard MAP_LOW_NEW_CHAIN0 == MAP_LOW_NEW + 8
#guard MAP_SIB2_0 == MAP_LOW_NEW_CHAIN0 + 120
#guard MAP_DIR2_0 == MAP_SIB2_0 + 128
#guard MAP_FREE_EMPTY == MAP_DIR2_0 + 16
#guard MAP_FREE_EMPTY_CHAIN0 == MAP_FREE_EMPTY + 8
#guard MAP_RANGE0 == MAP_FREE_EMPTY_CHAIN0 + 120
#guard MAP_WIDTH_AAFI == MAP_RANGE0 + 65
#guard MAP_WIDTH_AAFI == 897
#guard MAP_WIDTH_AAFI - MAP_AAFI_BASE == 476   -- AAFI region incl. MAP_S (1 selector + 475 payload)

#assert_axioms aafiLeafHash_injective
#assert_axioms aafiInsert_forces_imtInsert

/-! ## §8c — AAFI NON-VACUITY TEETH (both polarities), at a 2-LEVEL heap (4 leaves — heap-safe:
depth-generic theorems applied symbolically, no `2^16` object, no BabyBear field `decide`), on the
CR-PROVED reference sponge. FIRES: honest two-path gate data forces the genuine two-point update.
REJECTS: (1) an out-of-gap key (no pointer bracket → the double-spend tooth) and (2) a FROZEN
post-root (the append kept `new_root = old_root`) admit NO gate data at all. -/

section AafiTeeth

open Dregg2.Circuit.Poseidon2Binding.Reference (refSponge refSponge_CR)

/-- A toy empty-slot digest (the free position before append). -/
def aafiEmpty (hash : List ℤ → ℤ) : ℤ := aafiLeafHash hash 0 0 0
/-- The 2-level committed digest vector: low leaf `(0,0,100)` at position 0, empties at 1/2/3. -/
def aafiXsToy (hash : List ℤ → ℤ) : List ℤ :=
  [aafiLeafHash hash 0 0 100, aafiEmpty hash, aafiEmpty hash, aafiEmpty hash]
/-- PATH1 for position 0 (the low leaf): both steps LEFT. -/
def aafiSteps1 (hash : List ℤ → ℤ) : List (Bool × ℤ) :=
  [(false, mapNode hash (aafiEmpty hash) (aafiEmpty hash)), (false, aafiEmpty hash)]
/-- PATH2 for position 1 (the free slot): top LEFT, bottom RIGHT; the low sibling is `low_new`. -/
def aafiSteps2 (hash : List ℤ → ℤ) : List (Bool × ℤ) :=
  [(false, mapNode hash (aafiEmpty hash) (aafiEmpty hash)), (true, aafiLeafHash hash 0 0 50)]
def aafiOldRootToy (hash : List ℤ → ℤ) : ℤ := perfectRoot hash 2 (aafiXsToy hash)
def aafiR1Toy (hash : List ℤ → ℤ) : ℤ :=
  perfectRoot hash 2 [aafiLeafHash hash 0 0 50, aafiEmpty hash, aafiEmpty hash, aafiEmpty hash]
def aafiNewRootToy (hash : List ℤ → ℤ) : ℤ :=
  perfectRoot hash 2 [aafiLeafHash hash 0 0 50, aafiLeafHash hash 50 7 100,
    aafiEmpty hash, aafiEmpty hash]

/-- **Honest AAFI gate data exists** (for every hash) — insert `50 ↦ 7` in the `(0 → 100)` gap: the
low-open PATH1, the pointer bracket `0 < 50 < 100`, the low-update to R1, the free-slot-empty PATH2,
and the append to the grown root. All the path recomputes hold STRUCTURALLY. -/
theorem aafi_toy_gates (hash : List ℤ → ℤ) :
    AafiGatesAt hash 2 (aafiOldRootToy hash) (aafiNewRootToy hash) 50 7 0 0 100 (aafiEmpty hash) :=
  ⟨aafiR1Toy hash, aafiXsToy hash, aafiSteps1 hash, aafiSteps2 hash,
    rfl, rfl, rfl,
    by rw [show pathPos (aafiSteps1 hash) = 0 from rfl, show pathPos (aafiSteps2 hash) = 1 from rfl]
       decide,
    rfl, rfl, by norm_num, by norm_num, rfl, rfl, rfl⟩

/-- **RESPECTING TOOTH — the AAFI row FIRES.** On the CR-proved sponge the law turns the honest gate
data into the genuine two-point update: the post-root IS the perfect-tree root of `xs` with the low
position updated (`next := 50`) and the appended leaf `(50, 7, 100)` at the free slot — the
digest-vector face of `imtInsert`, produced through the whole path-binding extraction. -/
theorem aafi_toy_fires :
    ∃ (xs : List ℤ) (p1 p2 : Nat),
      xs.length = 2 ^ 2 ∧
      p1 ≠ p2 ∧
      aafiOldRootToy refSponge = perfectRoot refSponge 2 xs ∧
      xs[p1]? = some (aafiLeafHash refSponge 0 0 100) ∧
      (xs.set p1 (aafiLeafHash refSponge 0 0 50))[p2]? = some (aafiEmpty refSponge) ∧
      aafiNewRootToy refSponge = perfectRoot refSponge 2
        ((xs.set p1 (aafiLeafHash refSponge 0 0 50)).set p2 (aafiLeafHash refSponge 50 7 100)) ∧
      (0 : ℤ) < 50 ∧ (50 : ℤ) < 100 :=
  aafiInsert_forces_imtInsert refSponge refSponge_CR 2 (aafi_toy_gates refSponge)

/-- **REJECT TOOTH 1 (out-of-gap key BITES — the double-spend tooth).** A key `150` outside the low
leaf's pointer gap `(0, 100)` admits NO accepting AAFI gate data: the pointer-bracket gate
`k < low.next` demands `150 < 100`, false. A present / out-of-gap `k` (the double-spend shape) is
UNSAT at the gate. -/
theorem aafi_toy_out_of_gap_bites (hash : List ℤ → ℤ) :
    ¬ AafiGatesAt hash 2 (aafiOldRootToy hash) (aafiNewRootToy hash) 150 7 0 0 100 (aafiEmpty hash) := by
  rintro ⟨_, _, _, _, _, _, _, _, _, _, _, hkn, _, _, _⟩
  exact absurd hkn (by norm_num)

/-- **REJECT TOOTH 2 (a FROZEN post-root BITES).** No gate data lets an AAFI row claim the insert
while keeping `new_root = old_root`: the law forces `old_root = perfectRoot xs` AND (frozen)
`old_root = perfectRoot (two-point-updated xs)`; `perfectRoot_injective` forces the two vectors
EQUAL, but they differ at the low position (`(0,0,100)` vs `(0,0,50)`, distinct by
`aafiLeafHash_injective` since `100 ≠ 50`). The append genuinely MOVES the committed root — the
after-root is a FORCED commitment, not a free witness limb. -/
theorem aafi_toy_frozen_bites :
    ¬ AafiGatesAt refSponge 2 (aafiOldRootToy refSponge) (aafiOldRootToy refSponge)
        50 7 0 0 100 (aafiEmpty refSponge) := by
  intro hg
  obtain ⟨xs, p1, p2, hxlen, hne, hor, hlowmem, _, hnew, _, _⟩ :=
    aafiInsert_forces_imtInsert refSponge refSponge_CR 2 hg
  have hx2len : ((xs.set p1 (aafiLeafHash refSponge 0 0 50)).set p2
      (aafiLeafHash refSponge 50 7 100)).length = 2 ^ 2 := by
    rw [List.length_set, List.length_set]; exact hxlen
  have hroots : perfectRoot refSponge 2 xs
      = perfectRoot refSponge 2 ((xs.set p1 (aafiLeafHash refSponge 0 0 50)).set p2
          (aafiLeafHash refSponge 50 7 100)) := by rw [← hor, ← hnew]
  have hxx := perfectRoot_injective refSponge refSponge_CR 2 hxlen hx2len hroots
  have hp1lt : p1 < xs.length := (List.getElem?_eq_some_iff.mp hlowmem).1
  -- xs = the two-point-updated vector; but at the low position that vector holds low_NEW, while
  -- `hlowmem` says xs holds low_OLD there — distinct digests (100 ≠ 50) under CR.
  rw [hxx, List.getElem?_set_ne (fun h => hne h.symm),
    List.getElem?_set_self hp1lt] at hlowmem
  -- hlowmem : some (aafiLeafHash refSponge 0 0 50) = some (aafiLeafHash refSponge 0 0 100)
  have hlow := Option.some.inj hlowmem
  exact absurd (aafiLeafHash_injective refSponge refSponge_CR hlow).2.2 (by norm_num)

-- The AAFI row's forced two-point update is the heap's REAL insert semantics (executable face):
#guard pathPos (aafiSteps1 (fun _ => 0)) == 0                         -- low position
#guard pathPos (aafiSteps2 (fun _ => 0)) == 1                         -- free position (distinct)
#guard (((aafiXsToy (fun _ => 0)).set 0 99).set 1 88).length == 4     -- two-point update keeps width

#assert_axioms aafi_toy_gates
#assert_axioms aafi_toy_fires
#assert_axioms aafi_toy_out_of_gap_bites
#assert_axioms aafi_toy_frozen_bites

end AafiTeeth

#check @aafiInsert_forces_imtInsert

end Dregg2.Circuit.MapOpsColumnLayout
