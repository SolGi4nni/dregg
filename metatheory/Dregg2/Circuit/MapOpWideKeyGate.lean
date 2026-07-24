/-
# Dregg2.Circuit.MapOpWideKeyGate — the WIDENED MAP-OP DENOTATION and GATE MODEL at the 8-felt key.

The second byte-safe chunk of the kind-D (`docs/DESIGN-wide-mapop-keys.md`) epoch. `MapOpWideKey`
authored the widened IR node (`MapOpW`), the order-isomorphic embedding, the arity-17 leaf digest
and THE WELD (`absentBracket_of_lexBlocks`). This file authors what sits between them and a
deployable widened AIR:

  * **S4 — the widened DENOTATION.** `DescriptorIR2.opensTo`/`writesTo`/`MapOp.holdsAt`
    (`DescriptorIR2.lean:534-590`) are ℤ-keyed because `Heap.leafOf`/`mapRoot` are. This file
    factors the KEY ABSORPTION out as a `LaneEnc K` (how many felts of the key the leaf digest
    eats) and re-states `leafOf`/`mapRoot`/`opensToMerkle`/`writesToMerkle` over it. The DEPLOYED
    objects are the `K := ℤ, LaneEnc := narrowEnc` instance, **definitionally** — `leafOfW_narrow`,
    `mapRootW_narrow`, `opensToMerkleW_narrow`, `writesToMerkleW_narrow` are all `rfl`.
  * **S8 — the three per-kind OPENERS** (`MapOpsColumnLayout.lean:466-566`) at `[LinearOrder K]`:
    `opensToMerkleW_of_path`, `opensToMerkleW_none_of_bracket`, `writesToMerkleW_of_path`. The
    deployed narrow openers are RE-DERIVED as the `narrowEnc` instance
    (`deployed_bracket_opener_is_instance` et al) — the generalization is conservative, checked by
    the kernel, not by eye.
  * **S7 — the arity-17 leaf SCHEMA** at `ImtLeaf Digest8Key ℤ` (key 8 felts ‖ value ‖ pointer 8
    felts) with its injectivity wired through the existing `imtLeafHash8_injective`, and the
    design's **blocker #2 as a theorem**: a wide address with a PROJECTED pointer
    (`halfWideLeafHash`) still conflates two committed leaves — and the conflation FORGES a
    non-membership of a key the honest chain PRESENTS (`halfWideLeaf_forges_absence_of_present`).
    Widening the key alone is not a repair.
  * **S5/S6 — the widened `.absent` / AAFI GATE**, `AafiGatesAtW` at the arity-17 leaf and the
    8-felt lex bracket, with `aafiInsertW_forces_imtInsertW` (the two-path append law, key width
    substituted) and `aafiBracketW_of_lexBlocks` (the emitted `lexLt8` blocks supply gate (b) AND
    the chain-level absence, through `MapOpWideKey.absentBracket_of_lexBlocks`).
  * **The design's blocker #1 as theorems, both directions.** `insertW_absentW_jointly_unsat`
    (a widened insert of `k` and a widened `.absent` open of `k` cannot both hold — composed from
    `HoldsKindW`, not restated), and the MIXED-WIDTH pair: narrow-insert + wide-open is a
    DOUBLE SPEND (`narrowInsert_wideOpen_double_spend`), wide-insert + narrow-open is a permanent
    LIVENESS break (`MapOpWideKey.narrowAbsent_unprovable`). Both halves must move in ONE epoch.

## What is INSTANTIATED vs AUTHORED (the design's §2 claim, checked)

INSTANTIATED (composed, zero new proof): `pathRecompute_binds_updates`, `perfectRoot_injective`,
every `Heap` lemma (`get_none_of_gap`, `set_sorted`, `length_set_mem`, `ext_get` — already
`[LinearOrder κ]`-generic), `sorted_gap_excludes`, `imtAbsent_excludes`, `nonMembership_soundW`,
`update_soundW`, `insert_then_no_nonmembershipW`, `lexLt8_refines`, `imtLeafHash8_injective`,
`absentBracket_of_lexBlocks`, `split_of_getElem?_pair`, `map_set'`.

AUTHORED (a proof script had to be re-run, because the DEPLOYED statement is ℤ-pinned even though
its ARGUMENT is not): `leafOfW`+injectivity, `mapRootW`+injectivity, `getW_eq_some_of_getElem?`,
`heapSetW_eq_listSet`, `adjacentW_of_getElem?_pair`, the three openers, the gate model and its law,
the arity-17 leaf schema, and every tooth. The design said "mechanical `ℤ → [LinearOrder K]`
generalization"; that is accurate about the ARGUMENTS and optimistic about the LABOUR — nothing new
had to be *discovered*, but the generic layer had to be *written*, and the payment for it is that
the deployed narrow objects come back as `rfl` instances.

## Honest scope (NOT closed here)

  * `Opens` in the `keysOfW`/`SpineCommitsW` wrapper stays ABSTRACT (the Wide8 discipline); this
    file's Merkle layer (`opensToMerkleW`) is the CONCRETE half and they are not yet welded to each
    other — that weld is a named follow-up, not a claim made here.
  * Nothing deployed is touched: no descriptor registered, no emit path, no JSON face, no changed
    byte. The widened chip ROW (`LEX_WIDTH` compare blocks, the 17-column leaf absorb) is the Rust
    re-emit, i.e. the VK epoch (W3/W4 in the design).
  * The map-op VALUE stays one felt (a separate named site).

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Crypto enters ONLY as the existing
named `Poseidon2SpongeCR` floor — no new floor. NEW file; every import read-only; no
`sorry`/`admit`/`native_decide`. Every concrete object is a literal ≤3-element list.
-/
import Dregg2.Circuit.MapOpWideKey

namespace Dregg2.Circuit.MapOpWideKeyGate

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2 (MapOp MapOpKind MAP_TREE_DEPTH)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.Emit.LexCompare8Emit (lexBlockHolds lexTf lexLt8_refines)
open Dregg2.Circuit.MapMerkleRoot (mapNode perfectRoot perfectRoot_injective mapRoot opensToMerkle
  writesToMerkle)
open Dregg2.Circuit.MapOpsColumnLayout (pathPos pathRecompute pathRecompute_binds_updates map_set'
  split_of_getElem?_pair ReconcileGatesAt)
open Dregg2.Circuit.IndexedMerkleTree (ImtLeaf ImtSorted ImtAbsent imtAddrs)
open Dregg2.Crypto.NonMembership (Sorted Adjacent)
open Dregg2.Crypto.Digest8KeySpike (Digest8Key keyLo keyE keyHi keyLo_lt_keyE keyE_lt_keyHi
  keyLo_lt_keyHi)
open Dregg2.Circuit.SortedTreeNonMembershipWide8 (proj0 keysOfW SpineCommitsW GapOpenW
  nonMembership_soundW demoOpens lowfelt_collision)
open Dregg2.Circuit.SortedTreeInsertWide8 (sortedInsertW update_soundW)
open Dregg2.Circuit.MapOpWideKey (keyLanes keyLanes_length keyLanes_inj digest8_ext MapOpW
  imtLeafHash8 imtLeafHash8_injective KeyCanon absentBracket_of_lexBlocks HoldsKindW projOpens
  narrowKeys_poisoned wideAbsent_provable)
open Dregg2.Substrate

set_option autoImplicit false
set_option linter.unusedVariables false
-- Several generic lemmas below need only `LaneEnc K`, not the order; the order is in scope for the
-- heap layer that surrounds them.
set_option linter.unusedSectionVars false

/-! ## §1 — `LaneEnc`: HOW MANY FELTS OF THE KEY THE LEAF DIGEST EATS.

This is the whole kind-D waist, isolated. The deployed map leaf is `Heap.leafOf hash e =
hash [e.1, e.2]` — the key contributes ONE felt because the encoding is `k ↦ [k]`. The widened leaf
contributes EIGHT because the encoding is `k ↦ keyLanes k`. Everything downstream (the root fold,
the openings, the openers, the gate model) is parametric in this one object, so the deployed narrow
denotation and the widened one are the SAME theorems at two encodings — not a twin pair. -/

/-- **`LaneEnc K`** — a map key's ABSORPTION SCHEDULE into a leaf digest: a fixed-width, injective
lane encoding. `width` is the number of felts the key contributes to the leaf's hash input; the
injectivity is what makes the leaf digest bind the WHOLE key. -/
structure LaneEnc (K : Type) where
  /-- The key's felt lanes, most-significant first. -/
  enc : K → List ℤ
  /-- The number of felts the key contributes to a leaf absorb. -/
  width : Nat
  /-- Every key absorbs exactly `width` felts (the AIR's column group is fixed-width). -/
  enc_length : ∀ k, (enc k).length = width
  /-- The lanes DETERMINE the key: no pre-folding, no projection. -/
  enc_inj : Function.Injective enc

/-- **The DEPLOYED encoding** — one felt, `k ↦ [k]`. `MapOp.key : EmittedExpr` is exactly this. -/
def narrowEnc : LaneEnc ℤ where
  enc := fun k => [k]
  width := 1
  enc_length := fun _ => rfl
  enc_inj := by intro a b h; simpa using h

/-- **The WIDENED encoding** — all eight felts of a `Digest8Key`, most-significant lane first. -/
def wideEnc : LaneEnc Digest8Key where
  enc := keyLanes
  width := 8
  enc_length := keyLanes_length
  enc_inj := by intro a b h; exact keyLanes_inj h

/-- The deployed map-tree leaf absorb arity `hash[key, value]`. -/
def MAP_TREE_LEAF_ARITY_NARROW : Nat := narrowEnc.width + 1
/-- The widened map-tree leaf absorb arity `hash[key8 ‖ value]`. -/
def MAP_TREE_LEAF_ARITY_WIDE : Nat := wideEnc.width + 1

#guard MAP_TREE_LEAF_ARITY_NARROW == 2
#guard MAP_TREE_LEAF_ARITY_WIDE == 9

section Generic

variable {K : Type} [LinearOrder K]

/-! ### §1a — the leaf, the root, and their injectivity, over an arbitrary `LaneEnc`. -/

/-- **`leafOfW hash E e`** — the map-tree leaf digest `hash[key-lanes ‖ value]`. At `narrowEnc`
this is DEFINITIONALLY the deployed `Heap.leafOf`. -/
def leafOfW (hash : List ℤ → ℤ) (E : LaneEnc K) (e : K × ℤ) : ℤ :=
  hash (E.enc e.1 ++ [e.2])

/-- **★ CONSERVATIVE EXTENSION (leaf).** The deployed 2-felt map leaf IS the narrow instance. -/
theorem leafOfW_narrow (hash : List ℤ → ℤ) (e : ℤ × ℤ) :
    leafOfW hash narrowEnc e = Heap.leafOf hash e := rfl

/-- The widened leaf BINDS the whole key and the value under the SAME named `Poseidon2SpongeCR`
floor the deployed leaf carries — no new cryptographic assumption at any width. -/
theorem leafOfW_injective (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (E : LaneEnc K)
    {e₁ e₂ : K × ℤ} (h : leafOfW hash E e₁ = leafOfW hash E e₂) : e₁ = e₂ := by
  obtain ⟨k₁, v₁⟩ := e₁
  obtain ⟨k₂, v₂⟩ := e₂
  have hl : E.enc k₁ ++ [v₁] = E.enc k₂ ++ [v₂] := hCR _ _ h
  have hlen : (E.enc k₁).length = (E.enc k₂).length := by rw [E.enc_length, E.enc_length]
  obtain ⟨hk, hv⟩ := List.append_inj hl hlen
  have h1 : k₁ = k₂ := E.enc_inj hk
  have h2 : v₁ = v₂ := by simpa using hv
  rw [h1, h2]

/-- The leaf-digest vector of a heap is injective (the per-leaf CR, lifted to the list). -/
theorem map_leafOfW_injective (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (E : LaneEnc K) :
    ∀ h₁ h₂ : List (K × ℤ),
      h₁.map (leafOfW hash E) = h₂.map (leafOfW hash E) → h₁ = h₂ := by
  intro h₁
  induction h₁ with
  | nil =>
    intro h₂ h
    cases h₂ with
    | nil => rfl
    | cons b s => simp at h
  | cons a t ih =>
    intro h₂ h
    cases h₂ with
    | nil => simp at h
    | cons b s =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [leafOfW_injective hash hCR E h.1, ih s h.2]

/-- **`mapRootW hash E d h`** — the depth-`d` binary-Merkle root of a heap whose leaves absorb the
key at `E`'s width. The node layer (`mapNode`, `perfectRoot`) is UNTOUCHED: the key width never
enters the digest-vector fold. -/
def mapRootW (hash : List ℤ → ℤ) (E : LaneEnc K) (d : Nat) (h : List (K × ℤ)) : ℤ :=
  perfectRoot hash d (h.map (leafOfW hash E))

/-- **★ CONSERVATIVE EXTENSION (root).** The deployed `mapRoot` IS the narrow instance. -/
theorem mapRootW_narrow (hash : List ℤ → ℤ) (d : Nat) (h : Heap.FeltHeap) :
    mapRootW hash narrowEnc d h = mapRoot hash d h := rfl

/-- The widened root BINDS the whole heap: `perfectRoot_injective` (untouched, it folds ℤ digests)
composed with the widened leaf CR. -/
theorem mapRootW_injective (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (E : LaneEnc K)
    (d : Nat) {h₁ h₂ : List (K × ℤ)} (hlen₁ : h₁.length = 2 ^ d) (hlen₂ : h₂.length = 2 ^ d)
    (h : mapRootW hash E d h₁ = mapRootW hash E d h₂) : h₁ = h₂ :=
  map_leafOfW_injective hash hCR E h₁ h₂
    (perfectRoot_injective hash hCR d (by rw [List.length_map, hlen₁])
      (by rw [List.length_map, hlen₂]) h)

/-! ### §1b — the widened OPENINGS (`opensToMerkleW`/`writesToMerkleW`) and their anti-ghosts. -/

/-- **`opensToMerkleW hash E d r k o`** — some sorted `2^d`-leaf heap, keyed at `K` and committed by
the depth-`d` binary root `r`, reads `o` at `k`. At `narrowEnc` this is DEFINITIONALLY the deployed
`opensToMerkle` (hence `DescriptorIR2.opensTo`). -/
def opensToMerkleW (hash : List ℤ → ℤ) (E : LaneEnc K) (d : Nat) (r : ℤ) (k : K)
    (o : Option ℤ) : Prop :=
  ∃ h : List (K × ℤ), Heap.SortedKeys h ∧ h.length = 2 ^ d ∧ mapRootW hash E d h = r
    ∧ Heap.get h k = o

/-- **`writesToMerkleW hash E d r k v r'`** — the sorted insert-or-update of `(k, v)` moves the
committed root `r` to `r'`, at key width `E`. -/
def writesToMerkleW (hash : List ℤ → ℤ) (E : LaneEnc K) (d : Nat) (r : ℤ) (k : K) (v : ℤ)
    (r' : ℤ) : Prop :=
  ∃ h : List (K × ℤ), Heap.SortedKeys h ∧ h.length = 2 ^ d
    ∧ (Heap.set h k v).length = 2 ^ d
    ∧ mapRootW hash E d h = r ∧ r' = mapRootW hash E d (Heap.set h k v)

/-- **★ CONSERVATIVE EXTENSION (opening).** The DEPLOYED `opensToMerkle` IS the narrow instance. -/
theorem opensToMerkleW_narrow (hash : List ℤ → ℤ) (d : Nat) (r k : ℤ) (o : Option ℤ) :
    opensToMerkleW hash narrowEnc d r k o = opensToMerkle hash d r k o := rfl

/-- **★ CONSERVATIVE EXTENSION (write).** The DEPLOYED `writesToMerkle` IS the narrow instance. -/
theorem writesToMerkleW_narrow (hash : List ℤ → ℤ) (d : Nat) (r k v r' : ℤ) :
    writesToMerkleW hash narrowEnc d r k v r' = writesToMerkle hash d r k v r' := rfl

/-- Widened openings are FUNCTIONAL (the anti-ghost at any key width). -/
theorem opensToMerkleW_functional (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (E : LaneEnc K) (d : Nat) {r : ℤ} {k : K} {o₁ o₂ : Option ℤ}
    (h₁ : opensToMerkleW hash E d r k o₁) (h₂ : opensToMerkleW hash E d r k o₂) : o₁ = o₂ := by
  obtain ⟨m₁, _, hl₁, hr₁, hg₁⟩ := h₁
  obtain ⟨m₂, _, hl₂, hr₂, hg₂⟩ := h₂
  have hm : m₁ = m₂ := mapRootW_injective hash hCR E d hl₁ hl₂ (hr₁.trans hr₂.symm)
  rw [← hg₁, ← hg₂, hm]

/-- Membership and non-membership at the same widened root/key EXCLUDE each other — the
double-spend tooth at the full key. -/
theorem opensToMerkleW_some_excludes_none (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (E : LaneEnc K) (d : Nat) {r : ℤ} {k : K} {v : ℤ}
    (h₁ : opensToMerkleW hash E d r k (some v)) (h₂ : opensToMerkleW hash E d r k none) :
    False := by
  have := opensToMerkleW_functional hash hCR E d h₁ h₂
  simp at this

/-- Widened writes are FUNCTIONAL: the `new_root` column cannot be forged at any key width. -/
theorem writesToMerkleW_functional (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (E : LaneEnc K) (d : Nat) {r : ℤ} {k : K} {v r₁ r₂ : ℤ}
    (h₁ : writesToMerkleW hash E d r k v r₁) (h₂ : writesToMerkleW hash E d r k v r₂) :
    r₁ = r₂ := by
  obtain ⟨m₁, _, hl₁, _, hr₁, he₁⟩ := h₁
  obtain ⟨m₂, _, hl₂, _, hr₂, he₂⟩ := h₂
  have hm : m₁ = m₂ := mapRootW_injective hash hCR E d hl₁ hl₂ (hr₁.trans hr₂.symm)
  rw [he₁, he₂, hm]

/-! ### §1c — the sorted-heap decode helpers, at `[LinearOrder K]`.

The deployed twins (`MapOpsColumnLayout.get_eq_some_of_getElem?`, `heapSet_eq_listSet`,
`adjacent_of_getElem?_pair`) are ℤ-pinned STATEMENTS whose proofs never touch ℤ arithmetic; every
`Heap` lemma they call is already `[LinearOrder κ]`-generic. These are the same scripts at `K`. -/

/-- A positional entry of a SORTED heap IS its `get` (strict sortedness makes the match unique). -/
theorem getW_eq_some_of_getElem? :
    ∀ {h : List (K × ℤ)} {p : Nat} {k : K} {v : ℤ},
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

/-- On a SORTED heap whose position `p` holds key `k`, `Heap.set h k v` IS the positional
`List.set` — the path's update direction lands exactly on the sorted insert-or-update. -/
theorem heapSetW_eq_listSet :
    ∀ {h : List (K × ℤ)} {p : Nat} {k : K} {vOld : ℤ},
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

/-- Two CONSECUTIVE positions of a heap are ADJACENT on its key spine — the
`NonMembership.Adjacent` witness `Heap.get_none_of_gap` consumes, at any key type. -/
theorem adjacentW_of_getElem?_pair {h : List (K × ℤ)} {p : Nat} {klo khi : K} {vlo vhi : ℤ}
    (hlo : h[p]? = some (klo, vlo)) (hhi : h[p + 1]? = some (khi, vhi)) :
    Adjacent (Heap.keys h) klo khi := by
  obtain ⟨pre, post, rfl⟩ := split_of_getElem?_pair h p _ _ hlo hhi
  exact ⟨pre.map Prod.fst, post.map Prod.fst, by simp [Heap.keys]⟩

/-! ### §1d — THE THREE PER-KIND OPENERS at `[LinearOrder K]` (design S8).

`MapOpsColumnLayout.lean:466-566`, key width abstracted. `pathRecompute_binds_updates` is reused
verbatim: it operates on the ℤ DIGEST VECTOR, which does not widen. -/

/-- **`.read` opener (widened).** A path recomputing the row's `(key, value)` leaf to the committed
root FORCES the membership opening at the FULL key: the row cannot claim a value the heap does not
hold there, and it cannot claim it at a colliding projection either — the leaf absorbs all
`E.width` lanes. -/
theorem opensToMerkleW_of_path (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (E : LaneEnc K)
    (dep : Nat) {r : ℤ} {k : K} {v : ℤ} (h : List (K × ℤ)) (hs : Heap.SortedKeys h)
    (hlen : h.length = 2 ^ dep) (hroot : mapRootW hash E dep h = r)
    (steps : List (Bool × ℤ)) (hsl : steps.length = dep)
    (hpath : pathRecompute hash (leafOfW hash E (k, v)) steps = r) :
    opensToMerkleW hash E dep r k (some v) := by
  subst hroot
  have hbind := (pathRecompute_binds_updates hash hCR steps (h.map (leafOfW hash E))
    (leafOfW hash E (k, v))
    (by rw [List.length_map, hlen, hsl]) (by rw [hsl]; exact hpath)).1
  simp only [List.getElem?_map] at hbind
  cases he : h[pathPos steps]? with
  | none => rw [he] at hbind; simp at hbind
  | some e =>
    rw [he] at hbind
    simp only [Option.map_some, Option.some.injEq] at hbind
    obtain rfl := leafOfW_injective hash hCR E hbind
    exact ⟨h, hs, hlen, rfl, getW_eq_some_of_getElem? hs he⟩

/-- **`.absent` opener (widened) — the gap arm.** TWO paths at CONSECUTIVE positions, opening
leaves whose keys strictly bracket the row's key AT THE FULL KEY ORDER, FORCE the non-membership
opening. The committed root pins both bracket leaves (arity `E.width + 1` absorb), position
adjacency pins spine adjacency, and `Heap.get_none_of_gap` (= `sorted_gap_excludes`, already
`[LinearOrder κ]`-generic) excludes the key. -/
theorem opensToMerkleW_none_of_bracket (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (E : LaneEnc K) (dep : Nat) {r : ℤ} {k : K} (h : List (K × ℤ)) (hs : Heap.SortedKeys h)
    (hlen : h.length = 2 ^ dep) (hroot : mapRootW hash E dep h = r)
    (stepsLo stepsHi : List (Bool × ℤ)) {klo khi : K} {vlo vhi : ℤ}
    (hlLo : stepsLo.length = dep) (hlHi : stepsHi.length = dep)
    (hadj : pathPos stepsHi = pathPos stepsLo + 1)
    (hpathLo : pathRecompute hash (leafOfW hash E (klo, vlo)) stepsLo = r)
    (hpathHi : pathRecompute hash (leafOfW hash E (khi, vhi)) stepsHi = r)
    (hklo : klo < k) (hkhi : k < khi) :
    opensToMerkleW hash E dep r k none := by
  subst hroot
  have hbindLo := (pathRecompute_binds_updates hash hCR stepsLo (h.map (leafOfW hash E))
    (leafOfW hash E (klo, vlo))
    (by rw [List.length_map, hlen, hlLo]) (by rw [hlLo]; exact hpathLo)).1
  have hbindHi := (pathRecompute_binds_updates hash hCR stepsHi (h.map (leafOfW hash E))
    (leafOfW hash E (khi, vhi))
    (by rw [List.length_map, hlen, hlHi]) (by rw [hlHi]; exact hpathHi)).1
  simp only [List.getElem?_map] at hbindLo hbindHi
  cases heLo : h[pathPos stepsLo]? with
  | none => rw [heLo] at hbindLo; simp at hbindLo
  | some eLo =>
    rw [heLo] at hbindLo
    simp only [Option.map_some, Option.some.injEq] at hbindLo
    obtain rfl := leafOfW_injective hash hCR E hbindLo
    cases heHi : h[pathPos stepsHi]? with
    | none => rw [heHi] at hbindHi; simp at hbindHi
    | some eHi =>
      rw [heHi] at hbindHi
      simp only [Option.map_some, Option.some.injEq] at hbindHi
      obtain rfl := leafOfW_injective hash hCR E hbindHi
      rw [hadj] at heHi
      exact ⟨h, hs, hlen, rfl,
        Heap.get_none_of_gap h klo khi k hs (adjacentW_of_getElem?_pair heLo heHi) hklo hkhi⟩

/-- **`.write`/`.insert` opener (widened).** An old-leaf path to the pre-root plus the SAME siblings
recomputing the new `(key, value)` leaf to the post-root FORCE the write opening at the full key. -/
theorem writesToMerkleW_of_path (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (E : LaneEnc K)
    (dep : Nat) {r : ℤ} {k : K} {v r' : ℤ} (h : List (K × ℤ)) (hs : Heap.SortedKeys h)
    (hlen : h.length = 2 ^ dep) (hroot : mapRootW hash E dep h = r)
    (steps : List (Bool × ℤ)) (vOld : ℤ) (hsl : steps.length = dep)
    (hpathOld : pathRecompute hash (leafOfW hash E (k, vOld)) steps = r)
    (hpathNew : pathRecompute hash (leafOfW hash E (k, v)) steps = r') :
    writesToMerkleW hash E dep r k v r' := by
  subst hroot
  obtain ⟨hmem, hupd⟩ := pathRecompute_binds_updates hash hCR steps (h.map (leafOfW hash E))
    (leafOfW hash E (k, vOld))
    (by rw [List.length_map, hlen, hsl]) (by rw [hsl]; exact hpathOld)
  simp only [List.getElem?_map] at hmem
  cases he : h[pathPos steps]? with
  | none => rw [he] at hmem; simp at hmem
  | some e =>
    rw [he] at hmem
    simp only [Option.map_some, Option.some.injEq] at hmem
    obtain rfl := leafOfW_injective hash hCR E hmem
    have hkmem : k ∈ Heap.keys h :=
      List.mem_map.mpr ⟨_, List.mem_of_getElem? he, rfl⟩
    have hnew : r' = mapRootW hash E dep (Heap.set h k v) := by
      rw [← hpathNew, heapSetW_eq_listSet hs he v]
      have h2 := hupd (leafOfW hash E (k, v))
      rw [hsl] at h2
      calc pathRecompute hash (leafOfW hash E (k, v)) steps
          = perfectRoot hash dep
              ((h.map (leafOfW hash E)).set (pathPos steps) (leafOfW hash E (k, v))) := h2
        _ = perfectRoot hash dep
              ((h.set (pathPos steps) (k, v)).map (leafOfW hash E)) := by rw [map_set']
        _ = mapRootW hash E dep (h.set (pathPos steps) (k, v)) := rfl
    exact ⟨h, hs, hlen,
      by rw [Heap.length_set_mem h k v hs hkmem]; exact hlen, rfl, hnew⟩

/-! ### §1e — the widened PER-KIND DENOTATION and GATE MODEL (design S4 + S5). -/

/-- **`HoldsKindMerkleW`** — what one map-op row MEANS at key width `E`, per kind. The deployed
`DescriptorIR2.MapOp.holdsAt` body is this at `narrowEnc` (`narrow_holdsAt_is_instance`). -/
def HoldsKindMerkleW (hash : List ℤ → ℤ) (E : LaneEnc K) (dep : Nat)
    (r : ℤ) (k : K) (v r' : ℤ) : MapOpKind → Prop
  | .read       => opensToMerkleW hash E dep r k (some v) ∧ r' = r
  | .absent     => opensToMerkleW hash E dep r k none ∧ r' = r
  | .write      => writesToMerkleW hash E dep r k v r'
  | .insert     => writesToMerkleW hash E dep r k v r'
  | .aafiInsert => writesToMerkleW hash E dep r k v r'

/-- **`ReconcileGatesW`** — the per-kind PATH GATES the widened `Ir2Air::MapOps` accepts, at key
width `E`. The `.absent` arm's two compares are the ones the emitted `lexLt8` blocks realize at
`E := wideEnc` (design S5; the deployed `MA_DECOMP`/`MA_CMP` blocks are the `narrowEnc` shape). -/
def ReconcileGatesW (hash : List ℤ → ℤ) (E : LaneEnc K) (dep : Nat)
    (r : ℤ) (k : K) (v r' : ℤ) : MapOpKind → Prop
  | .read =>
      (∃ steps : List (Bool × ℤ), steps.length = dep ∧
          pathRecompute hash (leafOfW hash E (k, v)) steps = r)
      ∧ r' = r
  | .absent =>
      (∃ (stepsLo stepsHi : List (Bool × ℤ)) (klo : K) (vlo : ℤ) (khi : K) (vhi : ℤ),
          stepsLo.length = dep ∧ stepsHi.length = dep ∧
          pathPos stepsHi = pathPos stepsLo + 1 ∧
          pathRecompute hash (leafOfW hash E (klo, vlo)) stepsLo = r ∧
          pathRecompute hash (leafOfW hash E (khi, vhi)) stepsHi = r ∧
          klo < k ∧ k < khi)
      ∧ r' = r
  | .write =>
      ∃ (steps : List (Bool × ℤ)) (vOld : ℤ), steps.length = dep ∧
        pathRecompute hash (leafOfW hash E (k, vOld)) steps = r ∧
        pathRecompute hash (leafOfW hash E (k, v)) steps = r'
  | .insert =>
      ∃ (steps : List (Bool × ℤ)) (vOld : ℤ), steps.length = dep ∧
        pathRecompute hash (leafOfW hash E (k, vOld)) steps = r ∧
        pathRecompute hash (leafOfW hash E (k, v)) steps = r'
  | .aafiInsert =>
      ∃ (steps : List (Bool × ℤ)) (vOld : ℤ), steps.length = dep ∧
        pathRecompute hash (leafOfW hash E (k, vOld)) steps = r ∧
        pathRecompute hash (leafOfW hash E (k, v)) steps = r'

/-- **`ReconcileGatesAtW`** — the widened gate acceptance for ONE map-op row: the
knowledge-extraction premise (the prover's committed canonical heap, NAMED exactly as the deployed
`ReconcileGatesAt`'s `∃ h`) plus the per-kind path gates. -/
def ReconcileGatesAtW (hash : List ℤ → ℤ) (E : LaneEnc K) (dep : Nat)
    (r : ℤ) (k : K) (v r' : ℤ) (op : MapOpKind) : Prop :=
  ∃ h : List (K × ℤ),
    Heap.SortedKeys h ∧ h.length = 2 ^ dep ∧ mapRootW hash E dep h = r
      ∧ ReconcileGatesW hash E dep r k v r' op

/-- **★ THE WIDENED MAPOPS LAW.** For every op kind, accepted widened gate data yields the exact
widened denotation of the row's columns — the three openers dispatched. The row's columns are
FORCED truthful at the full key width, never assumed. -/
theorem reconcileGatesW_force_openingW (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (E : LaneEnc K) (dep : Nat) (r : ℤ) (k : K) (v r' : ℤ) (op : MapOpKind)
    (hg : ReconcileGatesAtW hash E dep r k v r' op) :
    HoldsKindMerkleW hash E dep r k v r' op := by
  obtain ⟨h, hs, hlen, hroot, hgates⟩ := hg
  cases op with
  | read =>
    obtain ⟨⟨steps, hsl, hpath⟩, hnr⟩ := hgates
    exact ⟨opensToMerkleW_of_path hash hCR E dep h hs hlen hroot steps hsl hpath, hnr⟩
  | absent =>
    obtain ⟨⟨sLo, sHi, klo, vlo, khi, vhi, hlLo, hlHi, hposadj, hpLo, hpHi, hklo, hkhi⟩,
      hnr⟩ := hgates
    exact ⟨opensToMerkleW_none_of_bracket hash hCR E dep h hs hlen hroot sLo sHi
      hlLo hlHi hposadj hpLo hpHi hklo hkhi, hnr⟩
  | write =>
    obtain ⟨steps, vOld, hsl, hpOld, hpNew⟩ := hgates
    exact writesToMerkleW_of_path hash hCR E dep h hs hlen hroot steps vOld hsl hpOld hpNew
  | insert =>
    obtain ⟨steps, vOld, hsl, hpOld, hpNew⟩ := hgates
    exact writesToMerkleW_of_path hash hCR E dep h hs hlen hroot steps vOld hsl hpOld hpNew
  | aafiInsert =>
    obtain ⟨steps, vOld, hsl, hpOld, hpNew⟩ := hgates
    exact writesToMerkleW_of_path hash hCR E dep h hs hlen hroot steps vOld hsl hpOld hpNew

end Generic

/-! ## §2 — THE DEPLOYED NARROW OBJECTS, RE-DERIVED AS THE `narrowEnc` INSTANCE.

These are the conservativity checks. Each one type-checks ONLY because the widened definition is
definitionally the deployed one at `narrowEnc` — the kernel, not the eye, certifies that the
generalization changed no deployed meaning. -/

/-- **★ The DEPLOYED `.absent` opener IS the widened one at `narrowEnc`** — re-derived, not
restated (`MapOpsColumnLayout.opensToMerkle_none_of_bracket`'s exact conclusion). -/
theorem deployed_bracket_opener_is_instance (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep : Nat) {r k : ℤ} (h : Heap.FeltHeap) (hs : Heap.SortedKeys h)
    (hlen : h.length = 2 ^ dep) (hroot : mapRoot hash dep h = r)
    (stepsLo stepsHi : List (Bool × ℤ)) {klo vlo khi vhi : ℤ}
    (hlLo : stepsLo.length = dep) (hlHi : stepsHi.length = dep)
    (hadj : pathPos stepsHi = pathPos stepsLo + 1)
    (hpathLo : pathRecompute hash (Heap.leafOf hash (klo, vlo)) stepsLo = r)
    (hpathHi : pathRecompute hash (Heap.leafOf hash (khi, vhi)) stepsHi = r)
    (hklo : klo < k) (hkhi : k < khi) :
    opensToMerkle hash dep r k none :=
  opensToMerkleW_none_of_bracket hash hCR narrowEnc dep h hs hlen hroot stepsLo stepsHi
    hlLo hlHi hadj hpathLo hpathHi hklo hkhi

/-- **★ The DEPLOYED `.read` opener IS the widened one at `narrowEnc`.** -/
theorem deployed_read_opener_is_instance (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep : Nat) {r k v : ℤ} (h : Heap.FeltHeap) (hs : Heap.SortedKeys h)
    (hlen : h.length = 2 ^ dep) (hroot : mapRoot hash dep h = r)
    (steps : List (Bool × ℤ)) (hsl : steps.length = dep)
    (hpath : pathRecompute hash (Heap.leafOf hash (k, v)) steps = r) :
    opensToMerkle hash dep r k (some v) :=
  opensToMerkleW_of_path hash hCR narrowEnc dep h hs hlen hroot steps hsl hpath

/-- **★ The DEPLOYED `.write` opener IS the widened one at `narrowEnc`.** -/
theorem deployed_write_opener_is_instance (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep : Nat) {r k v r' : ℤ} (h : Heap.FeltHeap) (hs : Heap.SortedKeys h)
    (hlen : h.length = 2 ^ dep) (hroot : mapRoot hash dep h = r)
    (steps : List (Bool × ℤ)) (vOld : ℤ) (hsl : steps.length = dep)
    (hpathOld : pathRecompute hash (Heap.leafOf hash (k, vOld)) steps = r)
    (hpathNew : pathRecompute hash (Heap.leafOf hash (k, v)) steps = r') :
    writesToMerkle hash dep r k v r' :=
  writesToMerkleW_of_path hash hCR narrowEnc dep h hs hlen hroot steps vOld hsl hpathOld hpathNew

/-- **★ The DEPLOYED per-row denotation `MapOp.holdsAt` IS `HoldsKindMerkleW` at `narrowEnc`** —
the S4 surface, conservative by `rfl`. -/
theorem narrow_holdsAt_is_instance (hash : List ℤ → ℤ) (env : VmRowEnv) (m : MapOp) :
    Dregg2.Circuit.DescriptorIR2.MapOp.holdsAt hash env m ↔
      (m.guard.eval env.loc = 1 →
        HoldsKindMerkleW hash narrowEnc MAP_TREE_DEPTH ((m.root 0).eval env.loc)
          (m.key.eval env.loc) (m.value.eval env.loc) ((m.newRoot 0).eval env.loc) m.op) :=
  Iff.rfl

/-- **★ The DEPLOYED gate model `ReconcileGatesAt` IS `ReconcileGatesAtW` at `narrowEnc`** — the S5
surface, conservative by `rfl`. So repointing the `.absent` bracket onto `lexLt8Descriptor` is a
CHANGE OF `E`, not a change of the law. -/
theorem narrow_gates_is_instance (hash : List ℤ → ℤ) (dep : Nat) (a : Assignment) (m : MapOp) :
    ReconcileGatesAt hash dep a m ↔
      ReconcileGatesAtW hash narrowEnc dep ((m.root 0).eval a) (m.key.eval a) (m.value.eval a)
        ((m.newRoot 0).eval a) m.op :=
  Iff.rfl

/-! ## §3 — THE WIDENED ROW: `MapOpW`'s denotation and gate at `wideEnc`. -/

/-- **`MapOpW.holdsAtW`** — the widened per-row denotation: when the guard fires, the row's
evaluated `(root, key8, value, new_root)` columns are a genuine opening at the FULL 8-felt key.
The deployed `MapOp.holdsAt` is the lane-0 shadow (`MapOpWideKey.narrow_key_is_lane0`). -/
def holdsAtW (hash : List ℤ → ℤ) (env : VmRowEnv) (m : MapOpW) : Prop :=
  m.guard.eval env.loc = 1 →
    HoldsKindMerkleW hash wideEnc MAP_TREE_DEPTH ((m.root 0).eval env.loc)
      (m.keyAt env.loc) (m.value.eval env.loc) ((m.newRoot 0).eval env.loc) m.op

/-- **`gatesAtW`** — the widened gate acceptance for the row's evaluated columns. -/
def gatesAtW (hash : List ℤ → ℤ) (dep : Nat) (a : Assignment) (m : MapOpW) : Prop :=
  ReconcileGatesAtW hash wideEnc dep ((m.root 0).eval a) (m.keyAt a) (m.value.eval a)
    ((m.newRoot 0).eval a) m.op

/-- **★ THE WIDENED ROW LAW.** An accepting widened gate row FORCES the widened denotation: the
8-felt-keyed map-op row cannot lie about what it read, wrote, or found absent. -/
theorem mapOpW_gates_force_holds (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (env : VmRowEnv) (m : MapOpW) (hg : gatesAtW hash MAP_TREE_DEPTH env.loc m) :
    holdsAtW hash env m :=
  fun _ => reconcileGatesW_force_openingW hash hCR wideEnc MAP_TREE_DEPTH _ _ _ _ _ hg

/-- **★ THE EMITTED WIDE `.absent` BRACKET, at the gate.** Two satisfied `lexLt8` blocks over the
FULL 8 lanes (`low.addr < k`, `k < low.next`) plus two adjacent committed paths ARE a widened
`.absent` gate. This is the design's S5 substitution — the deployed `MA_DECOMP`/`MA_CMP` blocks
replaced by instantiations of the Lean-authored `lexLt8Descriptor`, with the compares' meaning
supplied by `lexLt8_refines` rather than assumed. -/
theorem absentGateW_of_lexBlocks (hash : List ℤ → ℤ) (dep : Nat) (r v : ℤ)
    (envLo envHi : VmRowEnv) (lowAddr kk lowNext : Fin 8 → ℤ)
    (hcLow : KeyCanon lowAddr) (hcK : KeyCanon kk) (hcNext : KeyCanon lowNext)
    (hLoA : ∀ i : Fin 8, envLo.loc i.val = lowAddr i)
    (hLoB : ∀ i : Fin 8, envLo.loc (8 + i.val) = kk i)
    (hLoBlk : lexBlockHolds lexTf envLo)
    (hHiA : ∀ i : Fin 8, envHi.loc i.val = kk i)
    (hHiB : ∀ i : Fin 8, envHi.loc (8 + i.val) = lowNext i)
    (hHiBlk : lexBlockHolds lexTf envHi)
    (stepsLo stepsHi : List (Bool × ℤ)) (vlo vhi : ℤ)
    (hlLo : stepsLo.length = dep) (hlHi : stepsHi.length = dep)
    (hadj : pathPos stepsHi = pathPos stepsLo + 1)
    (hpLo : pathRecompute hash (leafOfW hash wideEnc (toLex lowAddr, vlo)) stepsLo = r)
    (hpHi : pathRecompute hash (leafOfW hash wideEnc (toLex lowNext, vhi)) stepsHi = r) :
    ReconcileGatesW hash wideEnc dep r (toLex kk) v r MapOpKind.absent :=
  ⟨⟨stepsLo, stepsHi, toLex lowAddr, vlo, toLex lowNext, vhi, hlLo, hlHi, hadj, hpLo, hpHi,
    (lexLt8_refines lowAddr kk hcLow hcK).mp ⟨envLo, hLoA, hLoB, hLoBlk⟩,
    (lexLt8_refines kk lowNext hcK hcNext).mp ⟨envHi, hHiA, hHiB, hHiBlk⟩⟩, rfl⟩

/-! ## §4 — THE ARITY-17 LEAF SCHEMA, and the design's BLOCKER #2 as a theorem.

`IndexedMerkleTree.ImtLeaf` is already key-generic, so the widened IMT leaf is
`ImtLeaf Digest8Key ℤ` — key 8 felts, value 1 felt, POINTER 8 felts. The pointer widening is not
optional: the IMT absence bracket is `low.addr < k < low.next`, so a wide address with a projected
pointer leaves every gap's UPPER bound at ~31 bits, and the attacker simply aims at the pointer. -/

/-- **`imtLeafInput8 l`** — the arity-**17** absorb of a widened IMT leaf:
`addr8 ‖ value ‖ next8`. Written out so the arity is a `rfl` fact, not a comment. -/
def imtLeafInput8 (l : ImtLeaf Digest8Key ℤ) : List ℤ :=
  keyLanes l.addr ++ l.value :: keyLanes l.nextAddr

theorem imtLeafInput8_length (l : ImtLeaf Digest8Key ℤ) : (imtLeafInput8 l).length = 17 := rfl

/-- **`imtLeafHash8Of hash l`** — the widened IMT leaf digest of a `ImtLeaf Digest8Key ℤ`. The
`MapOpWideKey.imtLeafHash8` fields bundled into the deployed generic leaf structure. -/
def imtLeafHash8Of (hash : List ℤ → ℤ) (l : ImtLeaf Digest8Key ℤ) : ℤ :=
  hash (imtLeafInput8 l)

theorem imtLeafHash8Of_eq (hash : List ℤ → ℤ) (l : ImtLeaf Digest8Key ℤ) :
    imtLeafHash8Of hash l = imtLeafHash8 hash l.addr l.value l.nextAddr := rfl

/-- **★ THE WIDENED LEAF SCHEMA BINDS ALL 17 FELTS** under the SAME named `Poseidon2SpongeCR`
floor — address, value AND pointer. `imtLeafHash8_injective` wired through the leaf structure. -/
theorem imtLeafHash8Of_injective (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {l₁ l₂ : ImtLeaf Digest8Key ℤ} (h : imtLeafHash8Of hash l₁ = imtLeafHash8Of hash l₂) :
    l₁ = l₂ := by
  obtain ⟨a₁, v₁, n₁⟩ := l₁
  obtain ⟨a₂, v₂, n₂⟩ := l₂
  have hh : imtLeafHash8 hash a₁ v₁ n₁ = imtLeafHash8 hash a₂ v₂ n₂ := h
  obtain ⟨ha, hv, hn⟩ := imtLeafHash8_injective hash hCR hh
  rw [ha, hv, hn]

/-- **`halfWideLeafHash`** — THE LAUNDERING SHAPE the design forbids: widen the ADDRESS to 8 felts
but keep the POINTER projected to lane 0 (arity 10). Looks widened; is not. -/
def halfWideLeafHash (hash : List ℤ → ℤ) (l : ImtLeaf Digest8Key ℤ) : ℤ :=
  hash (keyLanes l.addr ++ [l.value, proj0 l.nextAddr])

/-! ### §4a — three pointers colliding on lane 0, and the gap they forge. -/

/-- A pointer `(0,…,0,2)`: collides with `keyE` and `ptrHi` on lane 0, differs at felt 7. -/
def ptrMid : Digest8Key := toLex (fun i : Fin 8 => if i = 7 then 2 else 0)
/-- A pointer `(0,…,0,3)`: collides with `keyE` and `ptrMid` on lane 0, differs at felt 7. -/
def ptrHi : Digest8Key := toLex (fun i : Fin 8 => if i = 7 then 3 else 0)

theorem proj0_ptrMid : proj0 ptrMid = 0 := by
  show (if (0 : Fin 8) = 7 then (2 : ℤ) else 0) = 0
  decide

theorem proj0_ptrHi : proj0 ptrHi = 0 := by
  show (if (0 : Fin 8) = 7 then (3 : ℤ) else 0) = 0
  decide

theorem keyE_lt_ptrMid : keyE < ptrMid := by
  refine ⟨7, fun j hj => ?_, ?_⟩
  · show (if j = 7 then (1 : ℤ) else 0) = if j = 7 then (2 : ℤ) else 0
    rw [if_neg (Fin.ne_of_lt hj), if_neg (Fin.ne_of_lt hj)]
  · show (if (7 : Fin 8) = 7 then (1 : ℤ) else 0) < if (7 : Fin 8) = 7 then (2 : ℤ) else 0
    decide

theorem ptrMid_lt_ptrHi : ptrMid < ptrHi := by
  refine ⟨7, fun j hj => ?_, ?_⟩
  · show (if j = 7 then (2 : ℤ) else 0) = if j = 7 then (3 : ℤ) else 0
    rw [if_neg (Fin.ne_of_lt hj), if_neg (Fin.ne_of_lt hj)]
  · show (if (7 : Fin 8) = 7 then (2 : ℤ) else 0) < if (7 : Fin 8) = 7 then (3 : ℤ) else 0
    decide

theorem keyE_lt_ptrHi : keyE < ptrHi := keyE_lt_ptrMid.trans ptrMid_lt_ptrHi

/-- The HONEST widened chain: `keyLo → keyE → ptrHi`. Both `keyLo` and `keyE` are PRESENT
addresses; the chain is well-linked and strictly increasing at the 8-felt lex order. -/
def forgeChain : List (ImtLeaf Digest8Key ℤ) :=
  [⟨keyLo, 1, keyE⟩, ⟨keyE, 2, ptrHi⟩]

theorem forgeChain_sorted : ImtSorted forgeChain :=
  ⟨keyLo_lt_keyE, rfl, keyE_lt_ptrHi⟩

theorem keyE_present_in_forgeChain : keyE ∈ imtAddrs forgeChain := by
  simp [imtAddrs, forgeChain]

/-- **★ BLOCKER #2, MACHINE-CHECKED: WIDENING THE KEY ALONE FORGES A NON-MEMBERSHIP.**
The honest low leaf `⟨keyLo, 1, keyE⟩` and the fabricated `⟨keyLo, 1, ptrHi⟩` have the SAME
half-wide digest — for EVERY hash, with NO collision-resistance hypothesis at all, because the
pointer is projected to lane 0 and both pointers project to `0`. The honest leaf's pointer bracket
`(keyLo, keyE)` does NOT contain `keyE`; the fabricated one's bracket `(keyLo, ptrHi)` DOES. So a
prover opening the committed digest can claim the wider gap and prove `keyE` ABSENT — while `keyE`
is a PRESENT address of the very chain that digest commits to. A wide address with a narrow pointer
is not a repair; it is a non-membership forgery. -/
theorem halfWideLeaf_forges_absence_of_present (hash : List ℤ → ℤ) :
    halfWideLeafHash hash ⟨keyLo, 1, keyE⟩ = halfWideLeafHash hash ⟨keyLo, 1, ptrHi⟩
      ∧ keyE ∈ imtAddrs forgeChain
      ∧ (keyLo < keyE ∧ keyE < ptrHi)
      ∧ ¬ (keyE < keyE) := by
  refine ⟨?_, keyE_present_in_forgeChain, ⟨keyLo_lt_keyE, keyE_lt_ptrHi⟩, lt_irrefl _⟩
  show hash (keyLanes keyLo ++ [(1 : ℤ), proj0 keyE])
      = hash (keyLanes keyLo ++ [(1 : ℤ), proj0 ptrHi])
  rw [Dregg2.Circuit.SortedTreeNonMembershipWide8.proj0_keyE, proj0_ptrHi]

/-- **★ THE ARITY-17 LEAF KILLS THE FORGERY.** Under the SAME named `Poseidon2SpongeCR` floor the
deployed leaf already carries, the two leaves have DISTINCT digests: the lanes the projection
discarded are exactly the lanes the widened absorb now carries, so the committed digest PINS the
gap's upper bound at the full 8 felts. -/
theorem wideLeaf_kills_the_pointer_forgery (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    imtLeafHash8Of hash ⟨keyLo, 1, keyE⟩ ≠ imtLeafHash8Of hash ⟨keyLo, 1, ptrHi⟩ := by
  intro h
  have hh : imtLeafHash8 hash keyLo 1 keyE = imtLeafHash8 hash keyLo 1 ptrHi := h
  exact keyE_lt_ptrHi.ne (imtLeafHash8_injective hash hCR hh).2.2

/-- **★ THE SLOT IS BOUND (the positive form).** One committed arity-17 digest admits exactly ONE
`(addr8, value, next8)` reading — contrast `halfWideLeaf_forges_absence_of_present`, where the same
premise leaves the pointer free. This is what "the pointer widens too" buys. -/
theorem wideLeaf_slot_binds (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) {d : ℤ}
    {l₁ l₂ : ImtLeaf Digest8Key ℤ}
    (h₁ : imtLeafHash8Of hash l₁ = d) (h₂ : imtLeafHash8Of hash l₂ = d) : l₁ = l₂ :=
  imtLeafHash8Of_injective hash hCR (h₁.trans h₂.symm)

/-! ## §5 — THE WIDENED AAFI GATE: arity-17 leaf, 8-felt lex bracket, two-path append law. -/

/-- **`aafiLeafHashW`** — the AAFI leaf digest at the widened schema (`MapOpsColumnLayout`'s
`aafiLeafHash` with both key groups widened: arity 3 → 17). -/
def aafiLeafHashW (hash : List ℤ → ℤ) (addr : Digest8Key) (value : ℤ) (nextAddr : Digest8Key) : ℤ :=
  imtLeafHash8 hash addr value nextAddr

/-- **`AafiGatesAtW`** — the widened `MapKind::AafiInsert` gate acceptance: the committed digest
vector behind the pre-root, the two paths, `R1`, and the four gates — (a) low-open at the arity-17
leaf, (b) the POINTER BRACKET at the FULL 8-felt lex order, (c) PATH1 low-update → `R1`, (d1) PATH2
free-slot empty, (d2) PATH2 append → `new_root`. Structurally `AafiGatesAt` with the leaf schema and
the compare width substituted; the digest-vector layer is untouched. -/
def AafiGatesAtW (hash : List ℤ → ℤ) (dep : Nat) (oldRoot newRoot : ℤ) (k : Digest8Key) (v : ℤ)
    (lowAddr : Digest8Key) (lowValue : ℤ) (lowNext : Digest8Key) (freeEmpty : ℤ) : Prop :=
  ∃ (R1 : ℤ) (xs : List ℤ) (steps1 steps2 : List (Bool × ℤ)),
    xs.length = 2 ^ dep ∧
    steps1.length = dep ∧
    steps2.length = dep ∧
    pathPos steps1 ≠ pathPos steps2 ∧
    oldRoot = perfectRoot hash dep xs ∧
    pathRecompute hash (aafiLeafHashW hash lowAddr lowValue lowNext) steps1 = oldRoot ∧
    lowAddr < k ∧
    k < lowNext ∧
    pathRecompute hash (aafiLeafHashW hash lowAddr lowValue k) steps1 = R1 ∧
    pathRecompute hash freeEmpty steps2 = R1 ∧
    pathRecompute hash (aafiLeafHashW hash k v lowNext) steps2 = newRoot

/-- **★ THE WIDENED AAFI LAW.** Under the single named CR floor, an accepting widened AAFI row's
gates FORCE its `(old_root, new_root, k8, v)` to be an `imtInsert` step at the digest-vector level:
a committed vector whose LOW slot holds the arity-17 low leaf, whose free slot is EMPTY after the
low update, and whose two-point update has root EXACTLY `new_root` — with the 8-felt pointer bracket
surviving to the conclusion. `pathRecompute_binds_updates` is used TWICE, verbatim: the key width
never enters the digest-vector fold, which is precisely why this law is a substitution and not a
re-derivation. -/
theorem aafiInsertW_forces_imtInsertW (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (dep : Nat)
    {oldRoot newRoot : ℤ} {k : Digest8Key} {v : ℤ} {lowAddr : Digest8Key} {lowValue : ℤ}
    {lowNext : Digest8Key} {freeEmpty : ℤ}
    (hg : AafiGatesAtW hash dep oldRoot newRoot k v lowAddr lowValue lowNext freeEmpty) :
    ∃ (xs : List ℤ) (p1 p2 : Nat),
      xs.length = 2 ^ dep ∧
      p1 ≠ p2 ∧
      oldRoot = perfectRoot hash dep xs ∧
      xs[p1]? = some (aafiLeafHashW hash lowAddr lowValue lowNext) ∧
      (xs.set p1 (aafiLeafHashW hash lowAddr lowValue k))[p2]? = some freeEmpty ∧
      newRoot = perfectRoot hash dep
        ((xs.set p1 (aafiLeafHashW hash lowAddr lowValue k)).set p2
          (aafiLeafHashW hash k v lowNext)) ∧
      lowAddr < k ∧ k < lowNext := by
  obtain ⟨R1, xs, s1, s2, hlen, hl1, hl2, hne, hor, hp1old, hlk, hkn, hp1new, hp2e, hp2app⟩ := hg
  have e1 : xs.length = 2 ^ s1.length := by rw [hl1]; exact hlen
  have hroot1 : pathRecompute hash (aafiLeafHashW hash lowAddr lowValue lowNext) s1
      = perfectRoot hash s1.length xs := by rw [hp1old, hor, hl1]
  obtain ⟨hmem1, hupd1⟩ := pathRecompute_binds_updates hash hCR s1 xs
    (aafiLeafHashW hash lowAddr lowValue lowNext) e1 hroot1
  have hR1 : R1 = perfectRoot hash dep
      (xs.set (pathPos s1) (aafiLeafHashW hash lowAddr lowValue k)) := by
    rw [← hp1new, hupd1 (aafiLeafHashW hash lowAddr lowValue k), hl1]
  have e2 : (xs.set (pathPos s1) (aafiLeafHashW hash lowAddr lowValue k)).length
      = 2 ^ s2.length := by rw [List.length_set, hl2]; exact hlen
  have hroot2 : pathRecompute hash freeEmpty s2
      = perfectRoot hash s2.length
          (xs.set (pathPos s1) (aafiLeafHashW hash lowAddr lowValue k)) := by
    rw [hp2e, hR1, hl2]
  obtain ⟨hmem2, hupd2⟩ := pathRecompute_binds_updates hash hCR s2
    (xs.set (pathPos s1) (aafiLeafHashW hash lowAddr lowValue k)) freeEmpty e2 hroot2
  have hnew : newRoot = perfectRoot hash dep
      ((xs.set (pathPos s1) (aafiLeafHashW hash lowAddr lowValue k)).set (pathPos s2)
        (aafiLeafHashW hash k v lowNext)) := by
    rw [← hp2app, hupd2 (aafiLeafHashW hash k v lowNext), hl2]
  exact ⟨xs, pathPos s1, pathPos s2, hlen, hne, hor, hmem1, hmem2, hnew, hlk, hkn⟩

/-- **★ THE WIDENED AAFI GATES FORCE THE `ImtAbsent` WITNESS at the FULL 8-felt key** — the
widened twin of `IndexedMerkleTree.aafiGates_force_imtAbsent`. The bracket the gate checks IS the
pointer bracket the sorted-chain keystone consumes. -/
theorem aafiGatesW_force_imtAbsentW (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (dep : Nat)
    {oldRoot newRoot : ℤ} {k : Digest8Key} {v : ℤ} {lowAddr : Digest8Key} {lowValue : ℤ}
    {lowNext : Digest8Key} {freeEmpty : ℤ} {c : List (ImtLeaf Digest8Key ℤ)}
    (hg : AafiGatesAtW hash dep oldRoot newRoot k v lowAddr lowValue lowNext freeEmpty)
    (hlow : (⟨lowAddr, lowValue, lowNext⟩ : ImtLeaf Digest8Key ℤ) ∈ c) :
    ImtAbsent c k := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hlk, hkn⟩ :=
    aafiInsertW_forces_imtInsertW hash hCR dep hg
  exact ⟨⟨lowAddr, lowValue, lowNext⟩, hlow, hlk, hkn⟩

/-- **★ THE FULL WIDENED `.absent`/AAFI ROW, END TO END.** Two satisfied `lexLt8` blocks over the
FULL 8 lanes give BOTH the widened AAFI gate's pointer bracket (gate (b)) AND — through
`MapOpWideKey.absentBracket_of_lexBlocks`, the weld — the chain-level exclusion of the queried key
from the whole committed spine. The emitted compare gadget and the widened bracketing keystone,
composed at the gate. -/
theorem aafiBracketW_of_lexBlocks
    (envLo envHi : VmRowEnv) (lowAddr kk lowNext : Fin 8 → ℤ)
    (hcLow : KeyCanon lowAddr) (hcK : KeyCanon kk) (hcNext : KeyCanon lowNext)
    (hLoA : ∀ i : Fin 8, envLo.loc i.val = lowAddr i)
    (hLoB : ∀ i : Fin 8, envLo.loc (8 + i.val) = kk i)
    (hLoBlk : lexBlockHolds lexTf envLo)
    (hHiA : ∀ i : Fin 8, envHi.loc i.val = kk i)
    (hHiB : ∀ i : Fin 8, envHi.loc (8 + i.val) = lowNext i)
    (hHiBlk : lexBlockHolds lexTf envHi)
    (c : List (ImtLeaf Digest8Key ℤ)) (hs : ImtSorted c) (val : ℤ)
    (hmem : (⟨toLex lowAddr, val, toLex lowNext⟩ : ImtLeaf Digest8Key ℤ) ∈ c) :
    ((toLex lowAddr : Digest8Key) < toLex kk ∧ (toLex kk : Digest8Key) < toLex lowNext)
      ∧ (toLex kk : Digest8Key) ∉ imtAddrs c :=
  ⟨⟨(lexLt8_refines lowAddr kk hcLow hcK).mp ⟨envLo, hLoA, hLoB, hLoBlk⟩,
    (lexLt8_refines kk lowNext hcK hcNext).mp ⟨envHi, hHiA, hHiB, hHiBlk⟩⟩,
   absentBracket_of_lexBlocks envLo envHi lowAddr kk lowNext hcLow hcK hcNext
     hLoA hLoB hLoBlk hHiA hHiB hHiBlk c hs val hmem⟩

/-! ## §6 — THE DESIGN'S BLOCKER #1: INSERT AND OPEN MOVE TOGETHER, both directions. -/

section MoveTogether

variable {Root : Type*}

/-- **★ DIRECTION (a) — SAME WIDTH, BOTH LEGS: jointly UNSAT.** The widened `.aafiInsert`
denotation for `k` into `post` and the widened `.absent` denotation for the SAME 8-felt `k` at
`post` cannot both hold. Composed straight out of `MapOpWideKey.HoldsKindW` (whose insert leg IS
`update_soundW` and whose absent leg IS `nonMembership_soundW`) — no tree combinatorics restated. -/
theorem insertW_absentW_jointly_unsat (Opens : Root → Digest8Key × ℤ → Prop) (pre post : Root)
    (k : Digest8Key) (v v' : ℤ)
    (hins : HoldsKindW Opens pre post k v MapOpKind.aafiInsert)
    (habs : HoldsKindW Opens post post k v' MapOpKind.absent) : False :=
  habs.1 ((hins k).mpr (Or.inl rfl))

/-- The same, for the plain `.insert` kind. -/
theorem insertW_absentW_jointly_unsat' (Opens : Root → Digest8Key × ℤ → Prop) (pre post : Root)
    (k : Digest8Key) (v v' : ℤ)
    (hins : HoldsKindW Opens pre post k v MapOpKind.insert)
    (habs : HoldsKindW Opens post post k v' MapOpKind.absent) : False :=
  habs.1 ((hins k).mpr (Or.inl rfl))

end MoveTogether

/-- **★ DIRECTION (b1) — NARROW INSERT + WIDE OPEN IS A DOUBLE SPEND.** Widening only the OPEN side
is not a hardening: a lane-0-keyed insert of `keyE` writes the felt `proj0 keyE = 0`, which the
committed set ALREADY holds (`keyLo` projects there), so the narrow insert grows NOTHING — while the
WIDE `.absent` open for `keyE` still goes through. The key is consumed and its absence is still
provable. (`narrowKeys_poisoned` supplies the first half; `wideAbsent_provable` the second.) -/
theorem narrowInsert_wideOpen_double_spend :
    proj0 keyE ∈ keysOfW (projOpens demoOpens) ()
      ∧ (∀ n : ℤ, n ∈ keysOfW (projOpens demoOpens) ()
          ↔ (n = proj0 keyE ∨ n ∈ keysOfW (projOpens demoOpens) ()))
      ∧ keyE ∉ keysOfW demoOpens () :=
  ⟨narrowKeys_poisoned,
   fun n => ⟨Or.inr, fun h => h.elim (fun he => he ▸ narrowKeys_poisoned) id⟩,
   wideAbsent_provable⟩

/-- **★ DIRECTION (b2) — WIDE INSERT + NARROW OPEN IS A LIVENESS BREAK.** The lane-0 compare is
SOUND but INCOMPLETE: a strict lane-0 bracket implies the full lex bracket, so a narrow gate never
forges — but two keys sharing lane 0 (`keyLo`, `keyE`) admit NO narrow bracket at all, so the honest
fresh key becomes permanently unopenable. This is why the design's `narrowAbsent_unprovable` is an
AVAILABILITY theorem and `narrow_only_over_revokes` a SOUNDNESS one, and why "widen the open first"
bricks rather than hardens. -/
theorem proj0_bracket_sound_but_incomplete :
    (∀ a b : Digest8Key, proj0 a < proj0 b → a < b)
      ∧ (keyLo < keyE ∧ ¬ (proj0 keyLo < proj0 keyE)) := by
  refine ⟨fun a b h => ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), h⟩, keyLo_lt_keyE, ?_⟩
  rw [lowfelt_collision.1]
  exact lt_irrefl _

/-! ## §7 — NON-VACUITY: a concrete ACCEPTING widened gate, and the forged rows it REFUSES.

Depth 1, a two-leaf committed heap `[(keyLo,1), (keyHi,2)]` at the 8-felt lex order, over an
ARBITRARY hash — the gate fires with no assumption on the sponge beyond the named CR floor where
soundness is claimed. `keyE` is the honest fresh key whose lane-0 projection COLLIDES with the
present `keyLo`; the widened gate opens it, the deployed narrow one cannot. -/

/-- The committed widened heap: two leaves, sorted at the FULL 8-felt lex order. -/
def demoHeapW : List (Digest8Key × ℤ) := [(keyLo, 1), (keyHi, 2)]

theorem demoHeapW_sorted : Heap.SortedKeys demoHeapW := by
  show List.Pairwise (· < ·) [keyLo, keyHi]
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil)
  · intro b hb
    rw [List.mem_singleton.mp hb]
    exact keyLo_lt_keyHi
  · intro b hb
    simp at hb

theorem demoHeapW_length : demoHeapW.length = 2 ^ 1 := rfl

/-- The committed root of the demo heap, at the widened leaf schema. -/
def demoRootW (hash : List ℤ → ℤ) : ℤ := mapRootW hash wideEnc 1 demoHeapW

/-- **★ A REAL ACCEPTING WIDENED `.absent` GATE.** Two adjacent committed paths bracket the honest
fresh key `keyE` at the FULL 8-felt lex order (`keyLo < keyE` decided at felt **7** — the limb the
deployed projection discards — and `keyE < keyHi` at felt 0). Every path obligation closes by
`rfl`: the gate is a real row, not a shape. -/
theorem demoAbsentGateW_accepts (hash : List ℤ → ℤ) :
    ReconcileGatesAtW hash wideEnc 1 (demoRootW hash) keyE 0 (demoRootW hash)
      MapOpKind.absent :=
  ⟨demoHeapW, demoHeapW_sorted, demoHeapW_length, rfl,
   ⟨[(false, leafOfW hash wideEnc (keyHi, 2))], [(true, leafOfW hash wideEnc (keyLo, 1))],
    keyLo, 1, keyHi, 2, rfl, rfl, rfl, rfl, rfl, keyLo_lt_keyE, keyE_lt_keyHi⟩, rfl⟩

/-- **★ …AND IT FORCES A GENUINE WIDE NON-MEMBERSHIP.** The widened law turns that row into
`opensToMerkleW … keyE none` at the full key. -/
theorem demoAbsentGateW_forces_absence (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    opensToMerkleW hash wideEnc 1 (demoRootW hash) keyE none :=
  (reconcileGatesW_force_openingW hash hCR wideEnc 1 (demoRootW hash) keyE 0 (demoRootW hash)
    MapOpKind.absent (demoAbsentGateW_accepts hash)).1

/-- The demo heap really OPENS at the present key (the discrimination side). -/
theorem demoOpensW_keyLo (hash : List ℤ → ℤ) :
    opensToMerkleW hash wideEnc 1 (demoRootW hash) keyLo (some 1) :=
  ⟨demoHeapW, demoHeapW_sorted, demoHeapW_length, rfl, Heap.get_cons_self keyLo 1 [(keyHi, 2)]⟩

/-- **★ TOOTH — A FORGED `.absent` ON A PRESENT KEY IS UNSAT.** No widened `.absent` opening exists
for `keyLo`, which the committed root holds. The gate discriminates. -/
theorem demoAbsentGateW_rejects_present (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    ¬ opensToMerkleW hash wideEnc 1 (demoRootW hash) keyLo none := fun habs =>
  opensToMerkleW_some_excludes_none hash hCR wideEnc 1 (demoOpensW_keyLo hash) habs

/-- **★ TOOTH — THE DEPLOYED NARROW KEY CANNOT DISTINGUISH THE TWO ROWS.** `keyE` (absent, wide)
and `keyLo` (present) have the SAME lane-0 projection, so the deployed one-felt `MapOp.key` column
carries the identical value on both rows: whatever the narrow gate decides, it decides for both.
That is the kind-D waist, on this concrete accepting row. -/
theorem demoRows_indistinguishable_narrowly : proj0 keyE = proj0 keyLo ∧ keyE ≠ keyLo :=
  lowfelt_collision

/-! ## §8 — the INSTALL SURFACE, as arithmetic on the deployed constants. -/

/-- The deployed AAFI/absent compare-block width per bracket compare
(`MA_DECOMP_COLS + MA_CMP_COLS = 13 + 13`). -/
def MA_COMPARE_COLS_NARROW : Nat := 26
/-- The widened compare-block width per bracket compare (`LexCompare8Emit.LEX_WIDTH`). -/
def MA_COMPARE_COLS_WIDE : Nat := Dregg2.Circuit.Emit.LexCompare8Emit.LEX_WIDTH

#guard MA_COMPARE_COLS_WIDE == 40
-- Two compares per `.absent` / AAFI row: the bracket costs +28 columns.
#guard 2 * MA_COMPARE_COLS_WIDE - 2 * MA_COMPARE_COLS_NARROW == 28
-- The IMT leaf absorb: arity 3 → 17 (both key groups widen; the pointer is not optional).
#guard 17 - 3 == 14
-- The map-tree leaf absorb: arity 2 → 9.
#guard MAP_TREE_LEAF_ARITY_WIDE - MAP_TREE_LEAF_ARITY_NARROW == 7

/-! ## §9 — axiom hygiene: every keystone rests on the kernel triple only. -/

#assert_axioms leafOfW_injective
#assert_axioms map_leafOfW_injective
#assert_axioms mapRootW_injective
#assert_axioms opensToMerkleW_functional
#assert_axioms opensToMerkleW_some_excludes_none
#assert_axioms writesToMerkleW_functional
#assert_axioms getW_eq_some_of_getElem?
#assert_axioms heapSetW_eq_listSet
#assert_axioms adjacentW_of_getElem?_pair
#assert_axioms opensToMerkleW_of_path
#assert_axioms opensToMerkleW_none_of_bracket
#assert_axioms writesToMerkleW_of_path
#assert_axioms reconcileGatesW_force_openingW
#assert_axioms deployed_bracket_opener_is_instance
#assert_axioms deployed_read_opener_is_instance
#assert_axioms deployed_write_opener_is_instance
#assert_axioms narrow_holdsAt_is_instance
#assert_axioms narrow_gates_is_instance
#assert_axioms mapOpW_gates_force_holds
#assert_axioms absentGateW_of_lexBlocks
#assert_axioms imtLeafHash8Of_injective
#assert_axioms halfWideLeaf_forges_absence_of_present
#assert_axioms wideLeaf_kills_the_pointer_forgery
#assert_axioms wideLeaf_slot_binds
#assert_axioms aafiInsertW_forces_imtInsertW
#assert_axioms aafiGatesW_force_imtAbsentW
#assert_axioms aafiBracketW_of_lexBlocks
#assert_axioms insertW_absentW_jointly_unsat
#assert_axioms insertW_absentW_jointly_unsat'
#assert_axioms narrowInsert_wideOpen_double_spend
#assert_axioms proj0_bracket_sound_but_incomplete
#assert_axioms demoAbsentGateW_accepts
#assert_axioms demoAbsentGateW_forces_absence
#assert_axioms demoAbsentGateW_rejects_present
#assert_axioms demoRows_indistinguishable_narrowly

end Dregg2.Circuit.MapOpWideKeyGate
