/-
# Dregg2.Substrate.Heap — THE HEAP's sorted-map semantics (REFINEMENT-DESIGN Decision 1, wave R2).

A cell's programmable state becomes **registers + `heap_root`**: a sorted-Poseidon2 Merkle map over
`(collection_id, key) → value` (`.docs-history-noclaude/REFINEMENT-DESIGN.md` Decision 1). This module is the Lean
SEMANTIC FLOOR of that heap — the openable sorted map the circuit's gates will open against — built
as the GENERALIZATION of the proven `cap_root` machinery with a GENERIC leaf:

  * the SORTED-by-key invariant is the same strict `Pairwise (· < ·)` the non-membership bracketing
    proof rides (`Dregg2.Crypto.NonMembership.Sorted`, the cap/nullifier sorted tree);
  * NON-MEMBERSHIP openings reuse `sorted_gap_excludes` LITERALLY (the proven combinatorial heart of
    the sorted-tree non-membership AIR) — `get_none_of_gap` below is that theorem applied to the
    heap's key list;
  * the ROOT is a recomputed digest of the sorted leaf list, with the SAME single named crypto floor
    the cap-root advance carries (`Poseidon2SpongeCR`, `Circuit/Poseidon2Binding.lean`) and the same
    anti-ghost shape (`EffectVmEmitCapRoot.capRoot_binds_edge`): equal roots BIND the whole heap.

## Layer plan (mirrors the cap-root value model, `circuit/src/cap_root.rs` CanonicalCapTree)

  §1 — the GENERIC sorted map over any `LinearOrder` key: `get` / `set` (= sorted insert-or-update),
       proven: read-after-write, frame (untouched keys preserve openings), sorted-insert correctness
       (sortedness preserved + fresh-key grows by one + present-key updates in place), the
       membership characterization, the bracketing NON-MEMBERSHIP opening, and CANONICITY
       (`ext_get`: two sorted maps with the same lookup semantics are EQUAL — the determinism that
       makes the root a function of the map's MEANING, not its build history).
  §2 — the FELT heap (the deployed shape): addresses are key-hashes `addrOf = hash[coll, key]`
       (the sorted-by-key-hash tree of the design), leaves are `hash[addr, value]`, the root is the
       sponge of the sorted leaf list. Proven: `root_deterministic` (same semantics ⇒ same root,
       pure combinatorics) and `root_injective` (same root ⇒ same heap, under the ONE named CR
       hypothesis) — the two directions of "deterministic openable root", exactly the
       `KeyedCommit.KeyedDigestBindsKeys` discipline with a generic leaf.
  §3 — non-vacuity: concrete witnesses TRUE (reads back, frames, sorted) and FALSE (tampered value
       MOVES the root; absent key reads none) on a computable reference sponge.

The KERNEL face (how this sits beside `RecordKernelState` under the `write` verb's frame
discipline) is `Dregg2.Substrate.HeapKernel` — this module is executor/state-free on purpose.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. Crypto enters ONLY as
the named `Poseidon2SpongeCR` hypothesis (the cap-root floor), never as an axiom. NEW file; imports are read-only.
-/
import Dregg2.Crypto.NonMembership
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Crypto.SpongeCarrierReduction
import Dregg2.Crypto.RomCarrierSites
import Dregg2.Tactics

namespace Dregg2.Substrate.Heap

open Dregg2.Crypto.NonMembership (Sorted Adjacent sorted_gap_excludes)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Crypto.SpongeCarrierReduction
  (SpongeCarrier SpongeKeyed spongeFamily carrierBreakGame carrierAnsSize spongeAnsSize
   carrierBreakToFinder carrier_binds_advantage_bound
   carrierFloor_top_false_babyBear carrierFloor_bot_vacuous)
open Dregg2.Crypto.FloorGames (Game Adversary gameAdv HashCRHardQuant)
open Dregg2.Crypto.CostAdversary (IsPolyTime)
open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded)
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily)
open Dregg2.Crypto.RomBindingReduction (RomCarrier romCarrierGame RomCarrierComp romCarrierAdv
  RomCarrierEff romCarrier_binds romCarrier_choiceForger_excluded)
open Dregg2.Crypto.RomCarrierSites

universe u v

variable {κ : Type u} {ν : Type v} [LinearOrder κ]

/-! ## §1 — the generic sorted map (the openable-map semantics over ANY ordered key).

An entry is a `(key, value)` pair; the map is a key-sorted association list — the in-order leaf
list of the sorted Merkle tree (the same canonical realization the non-membership AIR is over,
`Crypto/NonMembership.lean §"The sorted committed set"`). -/

/-- The key list of a map (the sorted leaf-key spine the bracketing combinatorics read). -/
def keys (h : List (κ × ν)) : List κ := h.map Prod.fst

omit [LinearOrder κ] in
/-- `keys` on a cons (the definitional unfolding, named so proofs can `rw` it). -/
theorem keys_cons (k : κ) (v : ν) (t : List (κ × ν)) : keys ((k, v) :: t) = k :: keys t := rfl

/-- **The heap invariant** — the key spine is STRICTLY increasing (`Pairwise (· < ·)`, the exact
`Crypto.NonMembership.Sorted` predicate of the proven sorted tree). Strictness ⇒ keys are unique ⇒
the map is canonical (`ext_get`). -/
def SortedKeys (h : List (κ × ν)) : Prop := (keys h).Pairwise (· < ·)

/-- The head key of a sorted map is strictly below every tail key. -/
theorem sortedKeys_head_lt {k : κ} {v : ν} {t : List (κ × ν)}
    (hs : SortedKeys ((k, v) :: t)) : ∀ x ∈ keys t, k < x := by
  rw [SortedKeys, keys_cons] at hs
  exact (List.pairwise_cons.mp hs).1

/-- The tail of a sorted map is sorted. -/
theorem sortedKeys_tail {k : κ} {v : ν} {t : List (κ × ν)}
    (hs : SortedKeys ((k, v) :: t)) : SortedKeys t := by
  rw [SortedKeys, keys_cons] at hs
  exact (List.pairwise_cons.mp hs).2

/-- A sorted map's head key does NOT recur in its tail (strictness kills the duplicate). -/
theorem head_key_not_mem {k : κ} {v : ν} {t : List (κ × ν)}
    (hs : SortedKeys ((k, v) :: t)) : k ∉ keys t :=
  fun hmem => lt_irrefl k (sortedKeys_head_lt hs k hmem)

/-- **`get`** — the map lookup (the MEMBERSHIP OPENING's semantic content): the value at `k`, or
`none` when absent. First-match association lookup; on a `SortedKeys` map the match is unique. -/
def get : List (κ × ν) → κ → Option ν
  | [], _ => none
  | (k', v') :: rest, k => if k = k' then some v' else get rest k

@[simp] theorem get_nil (k : κ) : get ([] : List (κ × ν)) k = none := rfl

@[simp] theorem get_cons_self (k : κ) (v : ν) (t : List (κ × ν)) :
    get ((k, v) :: t) k = some v := by simp [get]

theorem get_cons_ne {k'' k' : κ} (v' : ν) (t : List (κ × ν)) (hne : k'' ≠ k') :
    get ((k', v') :: t) k'' = get t k'' := by simp [get, hne]

/-- **`set`** — the SORTED INSERT-OR-UPDATE (the leaf-update + sorted-insert gates' semantic
content): walk to the key's sorted position; overwrite in place if present, splice a fresh leaf if
absent. The single mutation primitive the `write` verb's heap instances reduce to. -/
def set : List (κ × ν) → κ → ν → List (κ × ν)
  | [], k, v => [(k, v)]
  | (k', v') :: rest, k, v =>
    if k < k' then (k, v) :: (k', v') :: rest
    else if k = k' then (k, v) :: rest
    else (k', v') :: set rest k v

/-- **READ-AFTER-WRITE (`get_after_set`).** The written key reads back exactly the written value —
unconditionally (no sortedness needed; the walk places the binding before any stale duplicate). -/
theorem get_set_self (h : List (κ × ν)) (k : κ) (v : ν) : get (set h k v) k = some v := by
  induction h with
  | nil => simp [set]
  | cons hd rest ih =>
    obtain ⟨k', v'⟩ := hd
    simp only [set]
    by_cases hlt : k < k'
    · rw [if_pos hlt]; simp
    · rw [if_neg hlt]
      by_cases heq : k = k'
      · rw [if_pos heq]; simp
      · rw [if_neg heq]
        rw [get_cons_ne v' (set rest k v) heq]
        exact ih

/-- **FRAME (`get_set_frame`).** A write to key `k` leaves the opening of EVERY other key
untouched: `get (set h k v) k'' = get h k''` for `k'' ≠ k`. Untouched data costs (and changes)
nothing — the per-touched-key discipline of the design. -/
theorem get_set_frame (h : List (κ × ν)) (k k'' : κ) (v : ν) (hne : k'' ≠ k) :
    get (set h k v) k'' = get h k'' := by
  induction h with
  | nil => simp [set, get, hne]
  | cons hd rest ih =>
    obtain ⟨k', v'⟩ := hd
    simp only [set]
    by_cases hlt : k < k'
    · rw [if_pos hlt, get_cons_ne v ((k', v') :: rest) hne]
    · rw [if_neg hlt]
      by_cases heq : k = k'
      · subst heq
        rw [if_pos rfl, get_cons_ne v rest hne, get_cons_ne v' rest hne]
      · rw [if_neg heq]
        by_cases h2 : k'' = k'
        · subst h2; simp
        · rw [get_cons_ne v' (set rest k v) h2, get_cons_ne v' rest h2]
          exact ih

/-- The key spine after a `set` is the old spine plus (at most) the written key. -/
theorem mem_keys_set_iff (h : List (κ × ν)) (k x : κ) (v : ν) :
    x ∈ keys (set h k v) ↔ x = k ∨ x ∈ keys h := by
  induction h with
  | nil => simp [set, keys]
  | cons hd rest ih =>
    obtain ⟨k', v'⟩ := hd
    simp only [set]
    by_cases hlt : k < k'
    · rw [if_pos hlt]; simp [keys_cons, List.mem_cons]
    · rw [if_neg hlt]
      by_cases heq : k = k'
      · subst heq
        rw [if_pos rfl]
        simp only [keys_cons, List.mem_cons]
        tauto
      · rw [if_neg heq]
        simp only [keys_cons, List.mem_cons, ih]
        tauto

/-- **SORTED-INSERT CORRECTNESS (invariant preservation).** `set` preserves the strict-sorted key
invariant — the splice lands the fresh leaf at its unique sorted position (the sorted-insert gate's
semantic obligation), and an in-place update never moves a key. -/
theorem set_sorted (h : List (κ × ν)) (k : κ) (v : ν) (hs : SortedKeys h) :
    SortedKeys (set h k v) := by
  induction h with
  | nil => simp [set, SortedKeys, keys]
  | cons hd rest ih =>
    obtain ⟨k', v'⟩ := hd
    simp only [set]
    by_cases hlt : k < k'
    · rw [if_pos hlt]
      rw [SortedKeys, keys_cons, keys_cons]
      refine List.pairwise_cons.mpr ⟨?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact hlt
        · exact hlt.trans (sortedKeys_head_lt hs x hx')
      · rw [SortedKeys, keys_cons] at hs; exact hs
    · rw [if_neg hlt]
      by_cases heq : k = k'
      · subst heq
        rw [if_pos rfl]
        rw [SortedKeys, keys_cons]
        exact List.pairwise_cons.mpr ⟨sortedKeys_head_lt hs, sortedKeys_tail hs⟩
      · rw [if_neg heq]
        rw [SortedKeys, keys_cons]
        refine List.pairwise_cons.mpr ⟨?_, ih (sortedKeys_tail hs)⟩
        intro x hx
        rcases (mem_keys_set_iff rest k x v).mp hx with rfl | hx'
        · exact lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm heq)
        · exact sortedKeys_head_lt hs x hx'

/-- **SORTED-INSERT CORRECTNESS (fresh key GROWS by one).** Writing an ABSENT key splices exactly
one new leaf — the insert face of `set`. -/
theorem length_set_fresh (h : List (κ × ν)) (k : κ) (v : ν) (hk : k ∉ keys h) :
    (set h k v).length = h.length + 1 := by
  induction h with
  | nil => simp [set]
  | cons hd rest ih =>
    obtain ⟨k', v'⟩ := hd
    rw [keys_cons] at hk
    simp only [List.mem_cons, not_or] at hk
    obtain ⟨hne, hk'⟩ := hk
    simp only [set]
    by_cases hlt : k < k'
    · rw [if_pos hlt]; simp
    · rw [if_neg hlt, if_neg hne]
      simp [ih hk']

/-- **SORTED-INSERT CORRECTNESS (present key UPDATES in place).** Writing a PRESENT key replaces
its leaf without growing the map — the leaf-update face of `set`. -/
theorem length_set_mem (h : List (κ × ν)) (k : κ) (v : ν) (hs : SortedKeys h)
    (hk : k ∈ keys h) : (set h k v).length = h.length := by
  induction h with
  | nil => simp [keys] at hk
  | cons hd rest ih =>
    obtain ⟨k', v'⟩ := hd
    rw [keys_cons] at hk
    rcases List.mem_cons.mp hk with rfl | hmem
    · simp [set]
    · have hgt : k' < k := sortedKeys_head_lt hs k hmem
      simp only [set]
      rw [if_neg (not_lt.mpr hgt.le), if_neg (ne_of_gt hgt)]
      simp [ih (sortedKeys_tail hs) hmem]

/-- **The membership characterization.** `get` returns `none` exactly when the key is OFF the
spine — the semantic content both the membership opening (`isSome`) and the non-membership opening
(`= none`) certify. -/
theorem get_eq_none_iff (h : List (κ × ν)) (k : κ) : get h k = none ↔ k ∉ keys h := by
  induction h with
  | nil => simp [keys]
  | cons hd rest ih =>
    obtain ⟨k', v'⟩ := hd
    rw [keys_cons]
    by_cases heq : k = k'
    · subst heq; simp
    · rw [get_cons_ne v' rest heq]
      simp [heq, ih]

/-- **NON-MEMBERSHIP OPENING (`get_none_of_gap`) — the cap-root bracketing, REUSED.** If two
ADJACENT present keys `lo`, `hi` bracket `k` (`lo < k < hi`) on a sorted heap, then `k` is ABSENT:
`get h k = none`. The combinatorial heart is LITERALLY `Crypto.NonMembership.sorted_gap_excludes`
(the proven sorted-tree neighbor-bracketing of the nullifier/cap non-membership AIR), applied to
the heap's key spine — the design's "non-membership openings proven for nullifiers" generalized to
the generic-leaf heap with ZERO new combinatorics. -/
theorem get_none_of_gap (h : List (κ × ν)) (lo hi k : κ) (hs : SortedKeys h)
    (hadj : Adjacent (keys h) lo hi) (hlo : lo < k) (hhi : k < hi) :
    get h k = none :=
  (get_eq_none_iff h k).mpr (sorted_gap_excludes (keys h) lo hi k hs hadj hlo hhi)

/-- **CANONICITY (`ext_get`) — the determinism heart.** Two SORTED heaps with the SAME lookup
semantics are EQUAL (as leaf lists). This is what makes the committed root a function of the map's
MEANING: however a heap was built (any insert order, any update history), the sorted leaf list —
hence the root — is determined by `get` alone. The semantic twin of the canonical-tree property the
Rust `CanonicalCapTree` realizes by construction. -/
theorem ext_get : ∀ {h₁ h₂ : List (κ × ν)}, SortedKeys h₁ → SortedKeys h₂ →
    (∀ k, get h₁ k = get h₂ k) → h₁ = h₂ := by
  intro h₁
  induction h₁ with
  | nil =>
    intro h₂ _ _ hext
    cases h₂ with
    | nil => rfl
    | cons hd₂ t₂ =>
      obtain ⟨k₂, v₂⟩ := hd₂
      have h := hext k₂
      simp at h
  | cons hd₁ t₁ ih =>
    intro h₂ hs₁ hs₂ hext
    obtain ⟨k₁, v₁⟩ := hd₁
    cases h₂ with
    | nil =>
      have h := hext k₁
      simp at h
    | cons hd₂ t₂ =>
      obtain ⟨k₂, v₂⟩ := hd₂
      have hk : k₁ = k₂ := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have h := hext k₁
          rw [get_cons_self] at h
          have h2 : get ((k₂, v₂) :: t₂) k₁ = none := by
            rw [get_eq_none_iff, keys_cons]
            intro hmem
            rcases List.mem_cons.mp hmem with rfl | hmem'
            · exact lt_irrefl _ hlt
            · exact lt_irrefl _ (hlt.trans (sortedKeys_head_lt hs₂ _ hmem'))
          rw [h2] at h
          exact absurd h (by simp)
        · have h := (hext k₂).symm
          rw [get_cons_self] at h
          have h2 : get ((k₁, v₁) :: t₁) k₂ = none := by
            rw [get_eq_none_iff, keys_cons]
            intro hmem
            rcases List.mem_cons.mp hmem with rfl | hmem'
            · exact lt_irrefl _ hgt
            · exact lt_irrefl _ (hgt.trans (sortedKeys_head_lt hs₁ _ hmem'))
          rw [h2] at h
          exact absurd h (by simp)
      subst hk
      have hv : v₁ = v₂ := by
        have h := hext k₁
        rw [get_cons_self, get_cons_self] at h
        exact Option.some.inj h
      subst hv
      have htail : ∀ k, get t₁ k = get t₂ k := by
        intro k
        by_cases hkk : k = k₁
        · subst hkk
          rw [(get_eq_none_iff t₁ k).mpr (head_key_not_mem hs₁),
              (get_eq_none_iff t₂ k).mpr (head_key_not_mem hs₂)]
        · calc get t₁ k = get ((k₁, v₁) :: t₁) k := (get_cons_ne v₁ t₁ hkk).symm
            _ = get ((k₁, v₁) :: t₂) k := hext k
            _ = get t₂ k := get_cons_ne v₁ t₂ hkk
      exact congrArg (List.cons (k₁, v₁)) (ih (sortedKeys_tail hs₁) (sortedKeys_tail hs₂) htail)

-- §1 tripwires: every generic-map keystone is kernel-clean (pure combinatorics, NO crypto).
#assert_axioms get_set_self
#assert_axioms get_set_frame
#assert_axioms mem_keys_set_iff
#assert_axioms set_sorted
#assert_axioms length_set_fresh
#assert_axioms length_set_mem
#assert_axioms get_eq_none_iff
#assert_axioms get_none_of_gap
#assert_axioms ext_get

/-! ## §2 — the FELT heap: `(collection_id, key) → value` over the field, with the committed root.

The deployed shape (`REFINEMENT-DESIGN.md` Decision 1): the tree is sorted by KEY-HASH
`addrOf hash coll key = hash[coll, key]` (the `(collection_id, key)` address), the leaf binds the
address AND the value (`hash[addr, value]` — the generic-leaf generalization of the cap leaf
`hash[holder, target, rights, op]`, `EffectVmEmitCapRoot.siteCapEdgeLeaf`), and the root is the
sponge of the sorted leaf list (the `KeyedCommit.keyedDigest` shape). ONE crypto floor:
`Poseidon2SpongeCR` — the SAME named hypothesis the cap-root advance carries. -/

/-- The felt heap: a key-hash-addressed sorted map over the field (`ℤ` here, as everywhere in the
emit layer — the BabyBear felt is the deployment instance). -/
abbrev FeltHeap := List (ℤ × ℤ)

/-- **`addrOf`** — the heap ADDRESS of `(collection_id, key)`: the key-hash the tree is sorted by
(the design's "sorted-by-key-hash"). Distinct addresses ⇐ distinct pairs, under CR. -/
def addrOf (hash : List ℤ → ℤ) (coll key : ℤ) : ℤ := hash [coll, key]

/-- **`leafOf`** — the heap LEAF: `hash[addr, value]` — the generic-leaf generalization of the
cap-edge leaf (the address pins WHERE, the value pins WHAT; tampering either moves the leaf). -/
def leafOf (hash : List ℤ → ℤ) (e : ℤ × ℤ) : ℤ := hash [e.1, e.2]

/-- **`root`** — the committed heap root: the sponge of the (sorted) leaf list. The value the
`heap_root` register carries; the openable sorted-Poseidon2 root, computed from the SAME leaf list
the cell holds (cell≡circuit identity is BY DEFINITION at this layer — both read THIS function). -/
def root (hash : List ℤ → ℤ) (h : FeltHeap) : ℤ := hash (h.map (leafOf hash))

/-- `get` at a `(collection_id, key)` address. -/
def hget (hash : List ℤ → ℤ) (h : FeltHeap) (coll key : ℤ) : Option ℤ :=
  get h (addrOf hash coll key)

/-- `set` at a `(collection_id, key)` address (sorted insert-or-update). -/
def hset (hash : List ℤ → ℤ) (h : FeltHeap) (coll key v : ℤ) : FeltHeap :=
  set h (addrOf hash coll key) v

/-- Read-after-write at the addressed key (no crypto needed). -/
theorem hget_hset_self (hash : List ℤ → ℤ) (h : FeltHeap) (coll key v : ℤ) :
    hget hash (hset hash h coll key v) coll key = some v :=
  get_set_self h (addrOf hash coll key) v

/-! ### §2.1 — the EXTRACTORS: what the old CR-peeling inductions become when nothing is assumed.

⚑ **THE `Poseidon2SpongeCR` FLOOR IS DELETED FROM THIS SECTION.** It used to be the hypothesis of
`hget_hset_frame`, `map_leaf_injective` and `root_injective`. It is **FALSE at deployed BabyBear
parameters** (`Circuit.HashFloorHonesty.poseidon2SpongeCR_false_babyBear`: the sponge lands in one
bounded field while `List ℤ` is infinite, so collisions exist by pigeonhole), so all three theorems
were **VACUOUSLY TRUE at the deployed hash** — true implications whose hypothesis nothing deployed
satisfies. `#assert_axioms` was blind to it: the proofs were clean; the HYPOTHESIS was the flaw.

What replaces it assumes NOTHING. Each old induction, which used to consume a CR hypothesis to peel a
digest, becomes a total function that LOCATES the colliding pair instead — so an equivocation on the
deployed `heap_root` either forces the heaps equal or HANDS BACK the two distinct lists at which the
sponge actually collides. That is a true theorem at deployed parameters, where the old one was empty.

The probabilistic residual is priced in §2.3 as a real reduction to the deployed sponge's collision
game at an explicit adversary class, on `Crypto.SpongeCarrierReduction`. -/

/-- **THE ADDRESS EXTRACTOR.** Two `(collection, key)` pairs claimed at the same address are handed
back as the two preimages of `addrOf` — a genuine sponge collision whenever the pairs differ. -/
def addrFind (c k c' k' : ℤ) : List ℤ × List ℤ := ([c, k], [c', k'])

/-- **THE ADDRESS EXTRACTOR IS CORRECT — unconditionally.** Distinct `(collection, key)` pairs
carrying the SAME heap address collide the sponge. No floor: the old `hget_hset_frame` consumed CR
exactly here, and this is that step with the assumption removed and the witness produced. -/
theorem addrFind_spec (hash : List ℤ → ℤ) {c k c' k' : ℤ}
    (hne : ¬(c' = c ∧ k' = k)) (heq : addrOf hash c' k' = addrOf hash c k) :
    ([c', k'] : List ℤ) ≠ [c, k] ∧ hash [c', k'] = hash [c, k] := by
  refine ⟨fun hcon => ?_, heq⟩
  simp only [List.cons.injEq, and_true] at hcon
  exact hne ⟨hcon.1, hcon.2⟩

/-- **FRAME at distinct addresses — NO CRYPTO AT ALL.** Writing `(coll, key)` preserves the opening of
any OTHER address. This is the honest combinatorial core of the old `hget_hset_frame`: the crypto was
only ever used to get the address inequality, and here that is a hypothesis instead of a floor. -/
theorem hget_hset_frame_of_addr_ne (hash : List ℤ → ℤ)
    (h : FeltHeap) (coll key coll' key' v : ℤ)
    (haddr : addrOf hash coll' key' ≠ addrOf hash coll key) :
    hget hash (hset hash h coll key v) coll' key' = hget hash h coll' key' :=
  get_set_frame h _ _ v haddr

/-- **⚑ DEMOTED — `hget_hset_frame` at plain INJECTIVITY, which BabyBear REFUTES.** The named floor
`Poseidon2SpongeCR` is gone from the statement; what remains is the mathematical special case, kept as
the strength bridge (nothing was lost re-grounding) and NOT as a deployed guarantee.

**This is NOT the deployed frame law.** The deployed one is §2.3's reduction
`heapFrame_binds_advantage_bound` (`hEff` in the open), DISCHARGED on the keyed-ROM floor as §2.4's
`heapAddr_binds_rom`. A deployed BabyBear sponge does not satisfy `Function.Injective`, so
reading this theorem as a statement about the running system is exactly the vacuity being retired. -/
theorem hget_hset_frame (hash : List ℤ → ℤ) (hinj : Function.Injective hash)
    (h : FeltHeap) (coll key coll' key' v : ℤ) (hne : ¬(coll' = coll ∧ key' = key)) :
    hget hash (hset hash h coll key v) coll' key' = hget hash h coll' key' := by
  refine hget_hset_frame_of_addr_ne hash h coll key coll' key' v (fun haddr => ?_)
  exact (addrFind_spec hash hne haddr).1 (hinj haddr)

/-- **THE LEAF-LIST EXTRACTOR.** Walk two leaf-equal entry lists to the FIRST position at which the
entries themselves differ, and hand back that leaf's two preimages. A total function: the fallback
`([], [])` is returned only on inputs the spec excludes. -/
def mapLeafFind (hash : List ℤ → ℤ) : FeltHeap → FeltHeap → List ℤ × List ℤ
  | a :: as, b :: bs => if a = b then mapLeafFind hash as bs else ([a.1, a.2], [b.1, b.2])
  | _, _ => ([], [])

/-- **THE LEAF-LIST EXTRACTOR IS CORRECT — unconditionally.** Two DISTINCT entry lists with EQUAL leaf
maps collide the sponge at the first position where they differ. This is `map_leaf_injective`'s old
induction with the CR hypothesis removed: the same walk, producing the witness rather than assuming it
away. -/
theorem mapLeafFind_spec (hash : List ℤ → ℤ) :
    ∀ (l₁ l₂ : FeltHeap), l₁ ≠ l₂ → l₁.map (leafOf hash) = l₂.map (leafOf hash) →
      (mapLeafFind hash l₁ l₂).1 ≠ (mapLeafFind hash l₁ l₂).2
        ∧ hash (mapLeafFind hash l₁ l₂).1 = hash (mapLeafFind hash l₁ l₂).2 := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ hne hmap
      cases l₂ with
      | nil => exact absurd rfl hne
      | cons b bs => simp at hmap
  | cons a as ih =>
      intro l₂ hne hmap
      cases l₂ with
      | nil => simp at hmap
      | cons b bs =>
          simp only [List.map_cons, List.cons.injEq] at hmap
          obtain ⟨hleaf, htail⟩ := hmap
          by_cases hab : a = b
          · subst hab
            have htne : as ≠ bs := fun hc => hne (by rw [hc])
            simpa only [mapLeafFind, if_pos rfl] using ih bs htne htail
          · rw [mapLeafFind, if_neg hab]
            refine ⟨fun hcon => ?_, hleaf⟩
            simp only [List.cons.injEq, and_true] at hcon
            exact hab (Prod.ext hcon.1 hcon.2)

/-- **⚑ DEMOTED — `map_leaf_injective` at plain INJECTIVITY, which BabyBear REFUTES.** The named floor
is gone; this is the strength bridge, not a deployed guarantee. The deployed statement is §2.3. -/
theorem map_leaf_injective (hash : List ℤ → ℤ) (hinj : Function.Injective hash) :
    ∀ (l₁ l₂ : FeltHeap), l₁.map (leafOf hash) = l₂.map (leafOf hash) → l₁ = l₂ := by
  intro l₁ l₂ hmap
  by_contra hne
  exact (mapLeafFind_spec hash l₁ l₂ hne hmap).1 (hinj (mapLeafFind_spec hash l₁ l₂ hne hmap).2)

/-- **THE ROOT EXTRACTOR.** Either the two heaps' leaf lists already differ — then the equal roots ARE
an outer-sponge collision on those lists — or they agree and the collision is inside, located by
`mapLeafFind`. Total, and it is the reduction's witness in §2.3. -/
def rootFind (hash : List ℤ → ℤ) (h₁ h₂ : FeltHeap) : List ℤ × List ℤ :=
  if h₁.map (leafOf hash) = h₂.map (leafOf hash) then mapLeafFind hash h₁ h₂
  else (h₁.map (leafOf hash), h₂.map (leafOf hash))

/-- **⚑ THE ROOT EXTRACTOR IS CORRECT — UNCONDITIONALLY, and this is the theorem that replaces
`root_injective` as content.** Two DISTINCT heaps publishing the SAME `heap_root` yield a genuine
collision of the deployed sponge. No hypothesis on `hash` whatsoever, so — unlike the theorem it
replaces — it is a true and non-empty statement at deployed BabyBear parameters. -/
theorem rootFind_spec (hash : List ℤ → ℤ) {h₁ h₂ : FeltHeap}
    (hne : h₁ ≠ h₂) (hroot : root hash h₁ = root hash h₂) :
    (rootFind hash h₁ h₂).1 ≠ (rootFind hash h₁ h₂).2
      ∧ hash (rootFind hash h₁ h₂).1 = hash (rootFind hash h₁ h₂).2 := by
  unfold rootFind
  by_cases hmap : h₁.map (leafOf hash) = h₂.map (leafOf hash)
  · rw [if_pos hmap]
    exact mapLeafFind_spec hash h₁ h₂ hne hmap
  · rw [if_neg hmap]
    exact ⟨hmap, hroot⟩

/-- **THE EXTRACTOR DOES NOT BLOW UP ITS INPUT** — at most the two heaps' own lengths plus four felts,
whichever branch it takes. The cost model's output-growth obligation, PROVED; without it the reduction
in §2.3 would not preserve efficiency. -/
theorem rootFind_len_le (hash : List ℤ → ℤ) (h₁ h₂ : FeltHeap) :
    (rootFind hash h₁ h₂).1.length + (rootFind hash h₁ h₂).2.length
      ≤ 1 * (h₁.length + h₂.length) + 4 := by
  have hmapLen : ∀ (l₁ l₂ : FeltHeap),
      (mapLeafFind hash l₁ l₂).1.length + (mapLeafFind hash l₁ l₂).2.length ≤ 4 := by
    intro l₁
    induction l₁ with
    | nil => intro l₂; cases l₂ <;> simp [mapLeafFind]
    | cons a as ih =>
        intro l₂
        cases l₂ with
        | nil => simp [mapLeafFind]
        | cons b bs =>
            by_cases hab : a = b
            · rw [mapLeafFind, if_pos hab]; exact ih bs
            · rw [mapLeafFind, if_neg hab]; simp
  unfold rootFind
  by_cases hmap : h₁.map (leafOf hash) = h₂.map (leafOf hash)
  · rw [if_pos hmap]; have := hmapLen h₁ h₂; omega
  · rw [if_neg hmap]
    simp only [List.length_map]
    omega

/-- **⚑ DEMOTED — `root_injective` at plain INJECTIVITY, which BabyBear REFUTES.**

The named floor `Poseidon2SpongeCR` is DELETED from this statement. What remains is exactly the
injective special case — the strength bridge showing nothing was lost — and it is **NOT the deployed
anti-ghost**. A deployed BabyBear sponge is not injective, so this theorem says nothing about the
running system; that is precisely the vacuity this sweep retires.

**The deployed anti-ghost is §2.3's `heapRoot_binds_advantage_bound`** (an adversary that keeps the
published `heap_root` while tampering any address or any value has NEGLIGIBLE advantage, under the
deployed sponge's collision floor at a class its extracted finder inhabits — `hEff` honestly in the
open), with the address layer DISCHARGED on the keyed-ROM floor in §2.4. -/
theorem root_injective (hash : List ℤ → ℤ) (hinj : Function.Injective hash)
    {h₁ h₂ : FeltHeap} (h : root hash h₁ = root hash h₂) : h₁ = h₂ := by
  by_contra hne
  exact (rootFind_spec hash hne h).1 (hinj (rootFind_spec hash hne h).2)

/-- **(CANARY — the extractor's output is a REAL collision, so it is refutable.)** On an injective
sponge no equivocation can produce one, which is what makes the extraction load-bearing rather than a
disjunction whose right branch is always available. This reds if `rootFind` is ever weakened to
return a trivially-equal pair. -/
theorem rootColl_refutable_of_injective (hash : List ℤ → ℤ) (hinj : Function.Injective hash)
    {h₁ h₂ : FeltHeap} (hne : h₁ ≠ h₂) : root hash h₁ ≠ root hash h₂ :=
  fun hroot => hne (root_injective hash hinj hroot)

/-- **`root_deterministic` — the root is a function of the map's MEANING.** Two SORTED heaps with
the same lookup semantics have the SAME root (via canonicity `ext_get`; NO crypto). Build history
is invisible to the commitment — the openable root is well-defined on the abstract map. -/
theorem root_deterministic (hash : List ℤ → ℤ) {h₁ h₂ : FeltHeap}
    (hs₁ : SortedKeys h₁) (hs₂ : SortedKeys h₂)
    (hext : ∀ k, get h₁ k = get h₂ k) : root hash h₁ = root hash h₂ := by
  rw [ext_get hs₁ hs₂ hext]

/-- **⚑ DEMOTED — `root_binds_get` at plain INJECTIVITY.** Same demotion as `root_injective`: the named
floor is gone, and this is the strength bridge, not the deployed opening law (that is §2.3). -/
theorem root_binds_get (hash : List ℤ → ℤ) (hinj : Function.Injective hash)
    {h₁ h₂ : FeltHeap} (h : root hash h₁ = root hash h₂) :
    ∀ coll key, hget hash h₁ coll key = hget hash h₂ coll key := by
  intro coll key
  rw [root_injective hash hinj h]

#assert_axioms hget_hset_self
#assert_axioms addrFind_spec
#assert_axioms hget_hset_frame_of_addr_ne
#assert_axioms hget_hset_frame
#assert_axioms mapLeafFind_spec
#assert_axioms map_leaf_injective
#assert_axioms rootFind_spec
#assert_axioms rootFind_len_le
#assert_axioms root_injective
#assert_axioms rootColl_refutable_of_injective
#assert_axioms root_deterministic
#assert_axioms root_binds_get

/-! ## §2.3 — ⚑ THE DEPLOYED HEAP-ROOT ANTI-GHOST, AS A SECURITY REDUCTION.

This is the HEADLINE binding of the `heap_root` register, and it replaces `root_injective` in that
role. The difference from what it replaces is not presentational:

  * `root_injective` assumed the deployed sponge is injective. It is not, at BabyBear — so that
    theorem is VACUOUS at deployed parameters and transports nothing.
  * A `binds ∨ collides` disjunction would not fix it either: a collision EXISTS by pigeonhole, so the
    disjunction is satisfiable through its right branch without binding ever holding. It quantifies
    over SOLUTIONS.
  * The reduction below quantifies over EFFICIENT ADVERSARIES, which is what cryptographic hardness
    actually quantifies over. An adversary that keeps the published `heap_root` while tampering ANY
    address or ANY value is turned, by `rootFind`, into a genuine collision finder for the deployed
    sponge — so its advantage is negligible under the deployed sponge's collision floor.

⚑ **THE FLOOR DISCIPLINE (07-23).** The `Eff := IsPolyTime` discharge this section used to export
(`heapRoot_binds_from_polyTime` / `heapFrame_binds_from_polyTime`) is DELETED:
`Exec.SystemRootsBindingReduction.sysRoots_floor_polyTime_false_babyBear` REFUTES
`HashCRHardQuant (spongeFamily D) (IsPolyTime …)` at the deployed sponge, and
`Crypto.RomBindingReduction`'s header proves the fixed-function game cannot be repaired by ANY class.
What remains here is the honest fixed-hash form with `hEff` in the open (`_advantage_bound`); the
DISCHARGED binding lives on the keyed-ROM floor — §2.4 for the ADDRESS CODEC (a one-query
commitment, mechanically re-pointed), while the ROOT is a FOLD commitment (`hash` of `leafOf hash`
digests, one inner query per leaf) that the one-query `RomCarrier` shape does NOT cover: its ROM
re-grounding needs a fold/vector carrier with a first-differing-leaf extractor, NAMED OPEN WORK, not
silently claimed.

⚑ **THE ~31-BIT BOUNDARY IS NOT CLOSED BY THIS, AND MUST NOT BE READ AS CLOSED.** `heap_root` is ONE
felt. The floor bounds an adversary's advantage in a collision game; at a ~31-bit digest that game is
winnable in ~2^15.5 work by birthday search, so the honest reading of every binding here is "binds
exactly as well as its width allows". Widening the carrier is a separate, still-open repair. -/

/-- **THE HEAP-ROOT CARRIER.** No context; the payload is the whole heap; the commitment is the
deployed `root`; the extractor is `rootFind`, with its unconditional spec and its proved output
bound. Everything a deployed 1-felt commitment site owes the spine, and nothing more. -/
def heapRootCarrier : SpongeCarrier where
  Ctx := Unit
  Val := FeltHeap
  valDecEq := inferInstance
  enc := fun hash _ h => root hash h
  find := fun hash _ h₁ h₂ => rootFind hash h₁ h₂
  find_spec := fun hash _ h₁ h₂ hne heq => rootFind_spec hash hne heq
  size := fun _ h => h.length
  outCo := 1
  outBo := 4
  find_len_le := fun hash _ h₁ h₂ => rootFind_len_le hash h₁ h₂

/-- **THE HEAP-ROOT FORGERY GAME.** The adversary is handed a sampled domain-separation tag and WINS
iff it outputs two DISTINCT heaps publishing the SAME `heap_root` — the anti-ghost break, stated as
the event it actually is. -/
abbrev heapRootBreakGame (D : SpongeKeyed) :=
  carrierBreakGame D heapRootCarrier

/-- **⚑ THE DEPLOYED HEAP-ROOT BINDING — the honest fixed-hash form, `hEff` in the OPEN.** An
adversary that keeps the published `heap_root` while tampering the heap, whose EXTRACTED finder is in
the class `Eff`, has NEGLIGIBLE advantage under the deployed sponge's collision floor at `Eff`.

⚑ This replaces the DELETED `heapRoot_binds_from_polyTime`: the `IsPolyTime` discharge carried a
floor hypothesis that is REFUTED in-tree (§2.3 header), so no discharged fixed-hash form survives.
The ROM-discharged successor needs the fold carrier named in §2.3 — open work, not yet claimed. -/
theorem heapRoot_binds_advantage_bound (D : SpongeKeyed)
    (Eff : Adversary (Dregg2.Crypto.FloorGames.hashGame (spongeFamily D)) → Prop)
    (A : Adversary (heapRootBreakGame D))
    (hEff : Eff (carrierBreakToFinder D heapRootCarrier A))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (heapRootBreakGame D) A) :=
  carrier_binds_advantage_bound D heapRootCarrier Eff A hEff hCR

/-- **THE ADDRESS-CODEC CARRIER** — the frame law's crypto content, isolated. The payload is the
`(collection, key)` pair; the commitment is the deployed `addrOf`. -/
def addrCarrier : SpongeCarrier where
  Ctx := Unit
  Val := ℤ × ℤ
  valDecEq := inferInstance
  enc := fun hash _ p => addrOf hash p.1 p.2
  find := fun _ _ p q => ([p.1, p.2], [q.1, q.2])
  find_spec := fun _ _ p q hne heq => by
    refine ⟨fun hcon => ?_, heq⟩
    simp only [List.cons.injEq, and_true] at hcon
    exact hne (Prod.ext hcon.1 hcon.2)
  size := fun _ _ => 2
  outCo := 1
  outBo := 4
  find_len_le := fun _ _ _ _ => by simp

/-- **⚑ THE DEPLOYED FRAME LAW — the honest fixed-hash form, `hEff` in the OPEN.** An adversary that
finds two distinct `(collection, key)` pairs sharing a heap address — the ONLY way to break
"untouched data costs nothing", by `hget_hset_frame_of_addr_ne`, which needs no crypto at all —
whose extracted finder is in `Eff`, has NEGLIGIBLE advantage under the deployed sponge's collision
floor at `Eff`.  Replaces the DELETED `heapFrame_binds_from_polyTime` (refuted floor, §2.3 header);
the DISCHARGED successor is §2.4's `heapAddr_binds_rom`. -/
theorem heapFrame_binds_advantage_bound (D : SpongeKeyed)
    (Eff : Adversary (Dregg2.Crypto.FloorGames.hashGame (spongeFamily D)) → Prop)
    (A : Adversary (carrierBreakGame D addrCarrier))
    (hEff : Eff (carrierBreakToFinder D addrCarrier A))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (carrierBreakGame D addrCarrier) A) :=
  carrier_binds_advantage_bound D addrCarrier Eff A hEff hCR

/-! ## §2.4 — ⚑ THE ADDRESS CODEC, DISCHARGED ON THE KEYED-ROM FLOOR.

The one-query re-pointing of the frame law, on `Crypto.RomCarrierSites`' kit. ⚑ THE MODELLING STEP,
STATED: the sampled `H : Tag × AddrPair → Fin (2 ^ l)` idealises the deployed
`sponge (tagCode t ++ [coll, key])` at an asymptotic digest width — a deliberate, labelled ROM
idealisation (the `RomCarrierSites` header names exactly what it buys and does not buy); the message
domain is the BabyBear-RANGE pair, lossless on every pair the deployed prover can absorb
(`truncAddr_inj`, `truncAddr_limbs`). The floor under the binding is
`KeyedRomFloor.keyedRom_hard` — the birthday bound, PROVED — where the deleted discharge carried a
refuted hypothesis. At the deployed ~31-bit width the honest reading remains §2.3's: binds as well
as the width allows. -/

/-- The in-range `(collection_id, key)` pair — each coordinate a genuine BabyBear felt. -/
abbrev AddrPair : Type := Fin babyBearP × Fin babyBearP

/-- **THE ADDRESS-CODEC KEYED ROM FAMILY** — keyed by the deployed tag space, over in-range pairs,
with the ideal `λ`-bit digest. -/
def addrRomFamily (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) : KeyedRomFamily :=
  flatFamily D.Tag D.tagFintype tagDec D.tagNonempty (fun _ => AddrPair)
    (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => ⟨⟨0, babyBearP_pos⟩, ⟨0, babyBearP_pos⟩⟩)

/-- The family's width obligation, closed by construction. -/
theorem addrRomFamily_card_R (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) (l : ℕ) :
    letI := (addrRomFamily D tagDec).rFin l
    Fintype.card ((addrRomFamily D tagDec).R l) = 2 ^ l := by
  show Fintype.card (Fin (2 ^ l)) = 2 ^ l
  simp

/-- **THE ADDRESS CARRIER** — commitment `H (t, (coll, key))`: the heap address binds its pair.  The
embedding is the identity, injective on the nose (the ROM restatement of `addrCarrier`'s two-limb
`List.cons.injEq` extraction). -/
def addrRomCarrier (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) :
    RomCarrier (addrRomFamily D tagDec) :=
  taggedCarrier _ (fun _ => Unit) (fun _ => AddrPair) (fun _ => inferInstance)
    (fun _ _ p => p) (fun _ _ _ _ h => h)

/-- The address-forgery game at the sampled oracle: two distinct in-range pairs, one address. -/
abbrev heapAddrRomGame (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) : Game :=
  romCarrierGame (addrRomFamily D tagDec) (addrRomCarrier D tagDec)

/-- Truncate an IN-RANGE deployed pair — total on exactly the pairs the deployed prover absorbs. -/
def truncAddr (p : ℤ × ℤ) (h1 : 0 ≤ p.1 ∧ p.1 < (babyBearP : ℤ))
    (h2 : 0 ≤ p.2 ∧ p.2 < (babyBearP : ℤ)) : AddrPair :=
  (⟨p.1.toNat, (Int.toNat_lt h1.1).mpr h1.2⟩, ⟨p.2.toNat, (Int.toNat_lt h2.1).mpr h2.2⟩)

/-- **THE TRUNCATION LOSES NOTHING** — distinct in-range pairs stay distinct. -/
theorem truncAddr_inj {p q : ℤ × ℤ}
    (hp1 : 0 ≤ p.1 ∧ p.1 < (babyBearP : ℤ)) (hp2 : 0 ≤ p.2 ∧ p.2 < (babyBearP : ℤ))
    (hq1 : 0 ≤ q.1 ∧ q.1 < (babyBearP : ℤ)) (hq2 : 0 ≤ q.2 ∧ q.2 < (babyBearP : ℤ))
    (h : truncAddr p hp1 hp2 = truncAddr q hq1 hq2) : p = q := by
  have hv1 : p.1.toNat = q.1.toNat := congrArg Fin.val (congrArg Prod.fst h)
  have hv2 : p.2.toNat = q.2.toNat := congrArg Fin.val (congrArg Prod.snd h)
  have hc1 : ((p.1.toNat : ℕ) : ℤ) = ((q.1.toNat : ℕ) : ℤ) := by exact_mod_cast hv1
  have hc2 : ((p.2.toNat : ℕ) : ℤ) = ((q.2.toNat : ℕ) : ℤ) := by exact_mod_cast hv2
  rw [Int.toNat_of_nonneg hp1.1, Int.toNat_of_nonneg hq1.1] at hc1
  rw [Int.toNat_of_nonneg hp2.1, Int.toNat_of_nonneg hq2.1] at hc2
  exact Prod.ext hc1 hc2

/-- **LIMB-FOR-LIMB FAITHFULNESS** — reading the truncated pair back as integers IS the deployed
absorbed list `[coll, key]` that `addrOf` hands the sponge. -/
theorem truncAddr_limbs (p : ℤ × ℤ) (h1 : 0 ≤ p.1 ∧ p.1 < (babyBearP : ℤ))
    (h2 : 0 ≤ p.2 ∧ p.2 < (babyBearP : ℤ)) :
    [(((truncAddr p h1 h2).1 : ℕ) : ℤ), (((truncAddr p h1 h2).2 : ℕ) : ℤ)] = [p.1, p.2] := by
  simp only [truncAddr]
  rw [Int.toNat_of_nonneg h1.1, Int.toNat_of_nonneg h2.1]

/-- **⚑ THE FORGERY IS THE DEPLOYED FRAME VIOLATION** — two DISTINCT in-range pairs whose truncations
the sampled oracle maps to ONE address ARE a win of the address game. -/
theorem heapAddrRom_forgery_is_break (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (l : ℕ) (H : (heapAddrRomGame D tagDec).Inst l) (t : D.Tag) {p q : ℤ × ℤ}
    (hp1 : 0 ≤ p.1 ∧ p.1 < (babyBearP : ℤ)) (hp2 : 0 ≤ p.2 ∧ p.2 < (babyBearP : ℤ))
    (hq1 : 0 ≤ q.1 ∧ q.1 < (babyBearP : ℤ)) (hq2 : 0 ≤ q.2 ∧ q.2 < (babyBearP : ℤ))
    (hne : p ≠ q)
    (heq : H (t, truncAddr p hp1 hp2) = H (t, truncAddr q hq1 hq2)) :
    (heapAddrRomGame D tagDec).wins l H ((t, ()), truncAddr p hp1 hp2, truncAddr q hq1 hq2) :=
  ⟨fun hc => hne (truncAddr_inj hp1 hp2 hq1 hq2 hc), heq⟩

/-- **⚑⚑ THE ADDRESS-CODEC BINDING, DISCHARGED ON THE PROVED FLOOR** — the successor of the deleted
`heapFrame_binds_from_polyTime`: every query-bounded forger of the heap address has NEGLIGIBLE
advantage, in the keyed ROM model of §2.4's header.  Only the honest hypotheses remain: a polynomial
query budget and membership in the query class. -/
theorem heapAddr_binds_rom (D : SpongeKeyed) (tagDec : DecidableEq D.Tag) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (heapAddrRomGame D tagDec))
    (hA : RomCarrierEff (addrRomFamily D tagDec) (addrRomCarrier D tagDec) Q A) :
    Negl (gameAdv (heapAddrRomGame D tagDec) A) :=
  romCarrier_binds _ _ Q hQ (addrRomFamily_card_R D tagDec) A hA

/-- **(TOOTH — the class is INHABITED with POSITIVE advantage.)** The `0`-query constant answerer on
two distinct pairs is in the class and wins with positive probability at every parameter. -/
theorem heapAddrRom_class_inhabited_pos (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) :
    ∃ A, RomCarrierEff (addrRomFamily D tagDec) (addrRomCarrier D tagDec) Q A
      ∧ ∀ l, 0 < gameAdv (heapAddrRomGame D tagDec) A l := by
  obtain ⟨t₀⟩ := D.tagNonempty
  refine ⟨romCarrierAdv _ _ (constTripleComp _ _ (fun _ => (t₀, ()))
      (fun _ => (⟨0, babyBearP_pos⟩, ⟨0, babyBearP_pos⟩))
      (fun _ => (⟨1, one_lt_babyBearP⟩, ⟨0, babyBearP_pos⟩))),
    constTriple_in_eff _ _ _ _ _ Q, fun l => constTriple_gameAdv_pos _ _ _ _ _ l ?_⟩
  intro hcon
  have h0 : (0 : ℕ) = 1 := congrArg (fun x : AddrPair => (x.1 : ℕ)) hcon
  omega

/-- **(TOOTH — the `shortCollAdv` shape is ADMITTED and DEFANGED at this site.)** The `0`-query
constant answerer — the exact shape that refutes the `IsPolyTime` floor — is in the class, and its
advantage is NEGLIGIBLE against the sampled oracle. -/
theorem heapAddrRom_constAnswer_defanged (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (c : ∀ l, (addrRomCarrier D tagDec).Ctx l) (v w : ∀ l, (addrRomCarrier D tagDec).Val l) :
    Negl (gameAdv (heapAddrRomGame D tagDec)
      (romCarrierAdv _ _ (constTripleComp _ _ c v w))) :=
  constTriple_binds _ _ c v w Q hQ (addrRomFamily_card_R D tagDec)

/-- **(TOOTH — a non-negligible forger is OUTSIDE the class.)** -/
theorem heapAddrRom_nonNegl_forger_excluded (D : SpongeKeyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (heapAddrRomGame D tagDec))
    (hnn : ¬ Negl (gameAdv (heapAddrRomGame D tagDec) A)) :
    ¬ RomCarrierEff (addrRomFamily D tagDec) (addrRomCarrier D tagDec) Q A :=
  romCarrier_choiceForger_excluded _ _ Q hQ (addrRomFamily_card_R D tagDec) A hnn

/-- **(TOOTH — the floor is FALSE at the REAL BabyBear parameters.)** The honest price of the `hEff`
obligation, re-exported at this carrier so the heap lane cannot read its own reduction as stronger
than it is: at the UNRESTRICTED adversary class the floor the reduction rests on is refuted by any
sponge whose output is a genuine BabyBear felt. -/
theorem heapRoot_floor_top_false_babyBear (D : SpongeKeyed)
    (hb : ∀ xs, 0 ≤ D.sponge xs ∧ D.sponge xs < (2013265921 : ℤ)) :
    ¬ HashCRHardQuant (spongeFamily D) (fun _ => True) :=
  carrierFloor_top_false_babyBear D hb

/-- **(TOOTH — the other pole is vacuous.)** Recorded beside the refutation, so satisfiability of the
floor can never be mistaken for evidence. -/
theorem heapRoot_floor_bot_vacuous (D : SpongeKeyed) :
    HashCRHardQuant (spongeFamily D) (fun _ => False) :=
  carrierFloor_bot_vacuous D

#assert_axioms heapRoot_binds_advantage_bound
#assert_axioms heapFrame_binds_advantage_bound
#assert_axioms heapRoot_floor_top_false_babyBear
#assert_axioms heapRoot_floor_bot_vacuous
#assert_axioms addrRomFamily_card_R
#assert_axioms truncAddr_inj
#assert_axioms truncAddr_limbs
#assert_axioms heapAddrRom_forgery_is_break
#assert_axioms heapAddr_binds_rom
#assert_axioms heapAddrRom_class_inhabited_pos
#assert_axioms heapAddrRom_constAnswer_defanged
#assert_axioms heapAddrRom_nonNegl_forger_excluded

/-! ## §3 — NON-VACUITY: concrete witnesses TRUE and FALSE on a computable reference sponge.

The same Horner-with-length-tag toy sponge the cap-root recompute uses (`EffectVmEmitCapRoot.cN`)
so the heap is computable and a tampered write provably MOVES the root. (The soundness theorems
above use the abstract CR sponge; these guards exhibit realizable witnesses.) -/

/-- The reference sponge (Horner with a length tag) — computable, injective-enough for the
concrete guards. NOT real crypto (the deployment instance is the p3 Poseidon2 sponge behind
`Poseidon2SpongeCR`). -/
def refSponge : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 1000003 + x) (xs.length : ℤ)

/-- A hand-sorted raw heap (addresses 10, 20 holding 1, 2) for the bracketing witnesses. -/
def demoRaw : FeltHeap := [(10, 1), (20, 2)]

/-- `demoRaw` satisfies the sorted invariant (10 < 20). -/
theorem demoRaw_sorted : SortedKeys demoRaw := by
  norm_num [demoRaw, SortedKeys, keys, List.pairwise_cons]

/-- Addresses 10 and 20 are ADJACENT on `demoRaw`'s spine (nothing between). -/
theorem demoRaw_adjacent : Adjacent (keys demoRaw) 10 20 := ⟨[], [], rfl⟩

/-- **Non-vacuity of the NON-MEMBERSHIP opening**: 15 is bracketed by the adjacent present
addresses 10 < 15 < 20, so `get demoRaw 15 = none` — `sorted_gap_excludes` firing on the heap. -/
theorem demoRaw_gap_15 : get demoRaw (15 : ℤ) = none :=
  get_none_of_gap demoRaw 10 20 15 demoRaw_sorted demoRaw_adjacent
    (by norm_num) (by norm_num)

-- Membership/absence read off the same spine (the executable face of the same facts):
#guard get demoRaw (10 : ℤ) == some 1
#guard get demoRaw (15 : ℤ) == none
-- Sorted insert in the middle lands between the brackets and preserves reads:
#guard keys (set demoRaw (15 : ℤ) 99) == [10, 15, 20]
#guard get (set demoRaw (15 : ℤ) 99) (15 : ℤ) == some 99
#guard get (set demoRaw (15 : ℤ) 99) (10 : ℤ) == some 1   -- frame
#guard (set demoRaw (15 : ℤ) 99).length == 3              -- fresh key grows
#guard (set demoRaw (10 : ℤ) 99).length == 2              -- present key updates in place

/-- A concrete addressed heap: write (coll 1, key 2) := 42 then (coll 3, key 4) := 7. -/
def demoHeap : FeltHeap := hset refSponge (hset refSponge [] 1 2 42) 3 4 7

-- Read-after-write + frame at the addressed layer (witness TRUE):
#guard hget refSponge demoHeap 1 2 == some 42
#guard hget refSponge demoHeap 3 4 == some 7
#guard hget refSponge demoHeap 9 9 == none
#guard hget refSponge (hset refSponge demoHeap 1 2 50) 3 4 == some 7  -- untouched key preserved

-- **Witness FALSE (anti-ghost):** tampering ONE value MOVES the root — the published `heap_root`
-- cannot be kept while editing the heap (the executable shadow of `root_injective`):
#guard (root refSponge (hset refSponge demoHeap 1 2 50) != root refSponge demoHeap)
-- ...and writing a DIFFERENT address also moves it (addresses are bound, not just values):
#guard (root refSponge (hset refSponge demoHeap 5 6 42) != root refSponge demoHeap)

#assert_axioms demoRaw_sorted
#assert_axioms demoRaw_adjacent
#assert_axioms demoRaw_gap_15

end Dregg2.Substrate.Heap
