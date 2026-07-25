/-
# `Dregg2.Circuit.IndexedMerkleTree` — THE INDEXED-MERKLE-TREE (IMT) CLOSURE OF GAP #5:
heap-sortedness made an IN-CIRCUIT INDUCTIVE invariant, so `CanonicalHeapExtract` (the
`∃ h, SortedKeys h ∧ mapRoot h = pre-root` premise the 7 mapOp effects carry inside
`MapOpsColumnLayout.ReconcileGatesAt`) is DERIVED, not ASSUMED.

## The gap (grounded, `docs/reference/CANONICAL-HEAP-TREE-INVESTIGATION.md`)

The deployed per-turn `.insert` gate PATH-RECOMPUTES a fresh leaf to a free-witness post-root with
NO sorted-placement check (`descriptor_ir2.rs:2817-2845`); the `.absent` gap rides physical position
adjacency (`pathPos hi = pathPos lo + 1`, `descriptor_ir2.rs:2882`). Sortedness of the committed
`2^16`-leaf heap is therefore CARRIED as a knowledge-extraction ASSUMPTION (`SortedKeys h` inside
`ReconcileGatesAt`, never derived from the gates). Under the fully-adversarial SNARK-soundness model
a prover commits a NON-sorted root `[MIN,20,30,25,MAX]` (nullifier `25` out of order at position 3),
brackets it absent via positions 1,2 (`20 < 25 < 30`), and double-spends (§3 witness).

## The IMT fix (standard Aztec indexed Merkle tree)

The leaf becomes a LINKED-LIST node `hash[addr, value, nextAddr]` embedding a sorted chain in the
tree. Then:
  * ABSENCE of `k` = ONE low-leaf opening with a POINTER bracket `low.addr < k < low.nextAddr` (no
    physical-position adjacency needed — the `nextAddr` pointer IS the bracket, certified by the
    maintained well-linked invariant); the old `MapAbsent` `pathPos hi = pathPos lo + 1` retires.
  * INSERT of `k` = (i) update the low-leaf `nextAddr → k`, (ii) append `(k, value, low_oldNext)`;
    TWO O(depth) Merkle-path updates (`pathRecompute_binds_updates`, reused), NO shift.
  * SORTED-PRESERVATION `sorted(pre) ⟹ sorted(post)` is a LOCAL per-row pointer-bracket check
    (`imtInsert_preserves`), NOT an O(n) rebuild — chained from the sorted genesis it is an in-circuit
    INDUCTIVE invariant (`Reachable ⟹ ImtSorted`, `reachable_sorted`), so the `SortedKeys` premise
    DISCHARGES into `{Poseidon2SpongeCR, FRI-LDT}` (`canonicalHeapExtract_of_imt`).

## What is PROVEN here (all `#assert_axioms`-clean, sorry/admit/carrier-free)

  * the IMT model: `ImtLeaf` — KEY-GENERIC: `ImtLeaf K V` with `[LinearOrder K]`; the DEPLOYED
    shape is the DEFAULT instantiation (bare `ImtLeaf` IS `ImtLeaf ℤ ℤ`), and the #4/#10 8-felt
    note-nullifier key `Digest8Key := Lex (Fin 8 → ℤ)` instantiates the SAME object with zero
    reproof (`Crypto/Digest8KeySpike.lean`) — `imtLeafHash` (3-felt, CR-injective
    `imtLeafHash_injective`), `ImtSorted` (well-linked strictly-increasing chain), `ImtAbsent`
    (pointer bracket), `imtInsert`; the ordering core (`imtSorted_addrs_sorted`,
    `imtSorted_dichotomy`, `imtAbsent_excludes`, `imtInsert_preserves`, `mem_imtAddrs_imtInsert`,
    `imt_double_spend_unsat`) is proved over ANY `LinearOrder` key — only `<`/`≤`/`.trans`/
    `lt_irrefl`, no ℤ arithmetic;
  * the in-circuit INDUCTION: `genesis_sorted` (the `[MIN → MAX]` sentinel chain is `ImtSorted`,
    a pinnable constant) + `imtInsert_preserves` (local bracket check preserves it) + the CHAIN
    `reachable_sorted` (`Reachable ⟹ ImtSorted`);
  * `imtSorted_sortedKeys` : `ImtSorted c ⟹ Heap.SortedKeys (imtToHeap c)` — the projection to the
    deployed `FeltHeap` is sorted (the load-bearing conjunct);
  * `canonicalHeapExtract_of_imt` : a reachable chain's projected heap is `Heap.SortedKeys` — the
    conjunct `MapReconcileFamily` carried as an ASSUMPTION is now a THEOREM;
  * ★ SOUNDNESS `imt_double_spend_unsat` : under `ImtSorted`, a present key CANNOT be pointer-bracket
    absent (`imtAbsent_excludes`) — the §3 out-of-order-`25` double-spend is UNSAT;
  * LIVENESS: `genesis_sorted` + honest bracketed inserts stay `ImtSorted`, grow the spine by exactly
    the fresh key (`mem_imtAddrs_imtInsert`), and the inserted key is present-after / absent-before.

## The reused proven infrastructure

`Heap.SortedKeys`/`Heap.keys` (`Substrate/Heap.lean`), `Crypto.NonMembership.{Sorted, head_lt_of_sorted}`
(`sorted_gap_excludes`'s home), the Merkle path binding `MapOpsColumnLayout.pathRecompute_binds_updates`
(the O(depth) update leg, `imtLowUpdate_binds`), the single named `Poseidon2SpongeCR` floor. The
`SortedTreeNonMembership.sortedInsert` algebra is the abstract twin of the spine growth
(`mem_imtAddrs_imtInsert` ↔ `mem_sortedInsert`).

## Heap safety

`ImtSorted` is a per-leaf pointer property + O(depth) path checks; the `2^16` tree is NEVER
enumerated, no BabyBear field `decide`. `omega`/order/`Poseidon2` only; the concrete teeth run on
short literal `ℤ` chains (the BabyBear felt is the deployment instance of `ℤ` here, as everywhere in
this layer). NEW file; imports read-only; builds targeted
(`lake build Dregg2.Circuit.IndexedMerkleTree`).

## The deployed-Rust CHANGE SPEC (for the follow-up Rust lane — see the scratch note)

  1. `heap_root.rs` — `HeapLeaf { addr, value }` gains `next_addr: BabyBear`; `digest()`/`digest8()`
     hash `[addr, value, next_addr]` (arity 2→3); `sentinel_leaf(MIN)` becomes `{MIN, 0, MAX}` and
     the genesis is the single MIN-sentinel chain `[{MIN,0,MAX}]` (append MAX only as the terminal
     pointer, not a separate sorted entry). `insert_witness` performs update-low + append instead of
     splice-and-rebuild.
  2. `descriptor_ir2.rs` — MapOps insert leg (`:2817`): the new leaf absorb becomes a 3-felt
     `chip_absorb_tuple([addr, value, next_addr])`; ADD (a) the low-leaf UPDATE path
     (`nextAddr → k`, one `node8` chain to the post-root) and (b) the append path of
     `(k, value, low_oldNext)` at the free slot, plus the LOCAL pointer-bracket range gate
     `low.addr < k < low.nextAddr` (two `eval_lex_lt`) binding the inserted key to the low-leaf's
     pointer gap of the PRE-root. MapAbsent leg (`:2880`): DELETE the `diff == 1` adjacency
     constraint; replace the two-leaf gap with ONE low-leaf opening + the pointer-bracket range
     `low.addr < key < low.nextAddr` (the `nextAddr` column of the single opened leaf is the hi
     bracket).
  3. `effect_vm/trace_rotated.rs` — the mapOp fill (`:1415/1516`): populate `next_addr` on every
     emitted `HeapLeaf`; on `.absent` emit ONE low-leaf witness (addr/value/nextAddr) instead of the
     lo/hi pair; on `.insert` emit the low-leaf-before + the two updated leaves.
  4. the producer (`CanonicalHeapTree8`/`insert_witness`) maintains the linked chain: `new` sorts by
     addr AND links `nextAddr` to the successor's addr (sentinel-terminated); `apply_value_update`
     leaves `nextAddr` fixed; `insert_witness` = update-low-next + append.
-/
import Dregg2.Circuit.MapOpsColumnLayout
import Dregg2.Circuit.SortedTreeNonMembership

namespace Dregg2.Circuit.IndexedMerkleTree

open Dregg2.Crypto.NonMembership (Sorted Adjacent sorted_gap_excludes head_lt_of_sorted sorted_tail)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.MapMerkleRoot (perfectRoot)
open Dregg2.Circuit.MapOpsColumnLayout (pathRecompute pathPos pathRecompute_binds_updates
  pathCollFind noPathColl_of_CR)
open Dregg2.Crypto.SpongeCarrierReduction (IsSpongeColl)
open Dregg2.Substrate

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — THE IMT LEAF/SCHEME: the linked-list node embedded in the sorted Merkle tree.

The KEY type is GENERIC: `addr`/`nextAddr : K` need only `[LinearOrder K]` for every ordering
proof below (the value `V` is never ordered). The DEPLOYED instantiation is the DEFAULT
`K := ℤ, V := ℤ` — bare `ImtLeaf` IS the deployed shape, so every existing consumer compiles
unchanged — and the #4/#10 note-nullifier widening instantiates `K := Digest8Key = Lex (Fin 8 → ℤ)`
directly (`Crypto/Digest8KeySpike.lean`), the lex-order bracketing coming for free. -/

/-- **`ImtLeaf`** — an indexed-Merkle-tree leaf: the sort key `addr`, the stored `value`, and the
`nextAddr` POINTER to the next-larger present key (the sorted linked-list link). The genesis
sentinel points `MIN → MAX`; every real insert splices between an `addr` and its `nextAddr`.
Key/value types generic; the defaults are the deployed felt instantiation. -/
structure ImtLeaf (K : Type := ℤ) (V : Type := ℤ) where
  /-- The sort key (deployed: the heap address `hash[coll, key]`; widens to `Digest8Key` for the
  #4/#10 note nullifiers — the tree is sorted by this). -/
  addr : K
  /-- The stored value (deployed: a felt; irrelevant to the ordering — hence free). -/
  value : V
  /-- The pointer to the next-larger present key (the linked-list link; the absence bracket). -/
  nextAddr : K
deriving DecidableEq, Repr

/-- **`imtLeafHash hash l`** — the 3-felt IMT leaf digest `hash[addr, value, nextAddr]` (the deployed
`heap_root.rs::HeapLeaf::digest8` gains the `nextAddr` felt: arity 2 → 3). -/
def imtLeafHash (hash : List ℤ → ℤ) (l : ImtLeaf) : ℤ := hash [l.addr, l.value, l.nextAddr]

/-- **`imtLeafPre l`** — the IMT leaf's sponge PREIMAGE, named so the per-instance collision event
is stated at exactly the list the deployed digest absorbs (`imtLeafHash hash l = hash (imtLeafPre l)`,
`rfl`). -/
def imtLeafPre (l : ImtLeaf) : List ℤ := [l.addr, l.value, l.nextAddr]

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

/-- **`imtLeafHash_injective`** — the IMT leaf digest BINDS its three fields: a prover cannot forge
the pointer (or address, or value) inside the digest. The crypto residue that binds a pointer-bracket
opening / a low-leaf update to the committed chain — exactly `Heap.leafOf_injective` at 3-felt width.
⛑ CUT OVER 2026-07-25: the refuted `Poseidon2SpongeCR hash` premise is replaced by the per-instance,
refutable side condition at the two NAMED preimages (implied by the old one, `noImtLeafColl_of_CR`). -/
theorem imtLeafHash_injective (hash : List ℤ → ℤ)
    {l₁ l₂ : ImtLeaf} (hno : ¬ IsSpongeColl hash (imtLeafPre l₁, imtLeafPre l₂))
    (h : imtLeafHash hash l₁ = imtLeafHash hash l₂) : l₁ = l₂ :=
  (imtLeafHash_binds_or_collides hash h).resolve_right hno

/-- **THE CUTOVER BRIDGE (IMT leaf side).** -/
theorem noImtLeafColl_of_CR {hash : List ℤ → ℤ} (hCR : Poseidon2SpongeCR hash)
    {l₁ l₂ : ImtLeaf} : ¬ IsSpongeColl hash (imtLeafPre l₁, imtLeafPre l₂) :=
  fun hc => hc.1 (hCR _ _ hc.2)

/-- **`ImtLeafCollIn hash ls low`** — the BOUNDED collision event: some leaf of the NAMED finite list
`ls` collides with `low` under the deployed sponge. Bounded over data the deployment actually holds,
so it is checkable and refutable — never a universal quantification over the sponge's whole domain. -/
def ImtLeafCollIn (hash : List ℤ → ℤ) (ls : List ImtLeaf) (low : ImtLeaf) : Prop :=
  ∃ l ∈ ls, IsSpongeColl hash (imtLeafPre l, imtLeafPre low)

/-- The bounded event's bridge: the refuted universal kills it. -/
theorem noImtLeafCollIn_of_CR {hash : List ℤ → ℤ} (hCR : Poseidon2SpongeCR hash)
    {ls : List ImtLeaf} {low : ImtLeaf} : ¬ ImtLeafCollIn hash ls low := by
  rintro ⟨l, _, hne, hh⟩
  exact hne (hCR _ _ hh)

variable {K : Type} {V : Type}

/-- The address spine of an IMT chain (the sorted key list the bracketing combinatorics read). -/
def imtAddrs (c : List (ImtLeaf K V)) : List K := c.map (·.addr)

@[simp] theorem imtAddrs_cons (l : ImtLeaf K V) (c : List (ImtLeaf K V)) :
    imtAddrs (l :: c) = l.addr :: imtAddrs c := rfl

@[simp] theorem imtAddrs_nil : imtAddrs ([] : List (ImtLeaf K V)) = [] := rfl

theorem mem_imtAddrs {c : List (ImtLeaf K V)} {x : K} :
    x ∈ imtAddrs c ↔ ∃ l ∈ c, l.addr = x := by
  simp [imtAddrs, List.mem_map]

variable [LinearOrder K]

/-- **`ImtSorted c`** — the tree invariant: the leaves form a strictly-increasing WELL-LINKED chain
— each leaf's `addr < nextAddr`, and each leaf's `nextAddr` EQUALS the next leaf's `addr` (the
sorted linked-list link). This is the per-leaf pointer property (O(1) per leaf, O(depth) per path),
NEVER a whole-tree scan. -/
def ImtSorted : List (ImtLeaf K V) → Prop
  | [] => True
  | [l] => l.addr < l.nextAddr
  | l :: l' :: rest => l.addr < l.nextAddr ∧ l.nextAddr = l'.addr ∧ ImtSorted (l' :: rest)

@[simp] theorem imtSorted_nil : ImtSorted ([] : List (ImtLeaf K V)) = True := rfl
@[simp] theorem imtSorted_singleton (l : ImtLeaf K V) :
    ImtSorted [l] = (l.addr < l.nextAddr) := rfl
@[simp] theorem imtSorted_cons_cons (l l' : ImtLeaf K V) (rest : List (ImtLeaf K V)) :
    ImtSorted (l :: l' :: rest)
      = (l.addr < l.nextAddr ∧ l.nextAddr = l'.addr ∧ ImtSorted (l' :: rest)) := rfl

/-! ## §2 — GENESIS: the `[MIN → MAX]` sentinel chain is `ImtSorted` (a pinnable constant). -/

/-- **`genesis lo hi`** — the empty IMT: a single MIN-sentinel leaf pointing to the MAX sentinel
(`heap_root.rs`'s `empty_heap_root_8`, sorted by construction — a verifier-known constant root,
in-circuit-pinnable). -/
def genesis (lo hi : ℤ) : List ImtLeaf := [{ addr := lo, value := 0, nextAddr := hi }]

/-- **GENESIS is `ImtSorted`** — the sentinel chain `[MIN → MAX]` is a valid sorted IMT (the base
of the induction; a constant root). -/
theorem genesis_sorted {lo hi : ℤ} (h : lo < hi) : ImtSorted (genesis lo hi) := h

/-! ## §3 — `ImtSorted ⟹ Sorted (imtAddrs)` and the projection to the deployed `FeltHeap`. -/

/-- The well-linked strictly-increasing chain has a STRICTLY-SORTED address spine (the linked-list
pointers transitively order the addresses). Proved by induction — O(chain), pointer-local. -/
theorem imtSorted_addrs_sorted : ∀ {c : List (ImtLeaf K V)}, ImtSorted c → Sorted (imtAddrs c) := by
  intro c
  induction c with
  | nil => intro _; simp [imtAddrs, Sorted]
  | cons l rest ih =>
    intro hs
    cases rest with
    | nil => simp [imtAddrs, Sorted, List.pairwise_cons]
    | cons l' rest' =>
      rw [imtSorted_cons_cons] at hs
      obtain ⟨h1, h2, htail⟩ := hs
      have ihs : Sorted (imtAddrs (l' :: rest')) := ih htail
      have hll' : l.addr < l'.addr := by rw [h2] at h1; exact h1
      rw [imtAddrs_cons, Sorted, List.pairwise_cons]
      refine ⟨?_, ihs⟩
      intro x hx
      rw [imtAddrs_cons] at hx
      rcases List.mem_cons.mp hx with rfl | hxr
      · exact hll'
      · exact hll'.trans (head_lt_of_sorted ihs x hxr)

/-- **`imtToHeap c`** — the projection to the deployed sorted `FeltHeap`: drop the `nextAddr`
pointer, keeping `(addr, value)` (the pointer is the ABSENCE machinery; the openable map is
`(addr) → value`). -/
def imtToHeap (c : List ImtLeaf) : Heap.FeltHeap := c.map (fun l => (l.addr, l.value))

theorem keys_imtToHeap (c : List ImtLeaf) : Heap.keys (imtToHeap c) = imtAddrs c := by
  simp [Heap.keys, imtToHeap, imtAddrs, List.map_map, Function.comp]

/-- **`imtSorted_sortedKeys` — the DERIVATION.** An `ImtSorted` chain projects to a `Heap.SortedKeys`
felt heap: the load-bearing sortedness conjunct of `CanonicalHeapExtract`, now a THEOREM about the
chain invariant. -/
theorem imtSorted_sortedKeys {c : List ImtLeaf} (hs : ImtSorted c) :
    Heap.SortedKeys (imtToHeap c) := by
  rw [Heap.SortedKeys, keys_imtToHeap]
  exact imtSorted_addrs_sorted hs

/-! ## §4 — THE POINTER-BRACKET ABSENCE and its exclusion (the soundness heart). -/

/-- **`ImtAbsent c k`** — the deployed IMT non-membership open: ONE low-leaf in the chain whose
POINTER bracket straddles `k` (`low.addr < k < low.nextAddr`). No physical-position adjacency — the
`nextAddr` pointer IS the hi bracket. -/
def ImtAbsent (c : List (ImtLeaf K V)) (k : K) : Prop :=
  ∃ low ∈ c, low.addr < k ∧ k < low.nextAddr

/-- **The addr dichotomy** — on an `ImtSorted` chain every address is `≤ low.addr` (at or before the
low leaf) OR `≥ low.nextAddr` (at or after the low leaf's successor): the pointer gap
`(low.addr, low.nextAddr)` contains NO present address. The pointer-local face of sortedness. -/
theorem imtSorted_dichotomy : ∀ {c : List (ImtLeaf K V)}, ImtSorted c →
    ∀ low ∈ c, ∀ x ∈ imtAddrs c, x ≤ low.addr ∨ low.nextAddr ≤ x := by
  intro c
  induction c with
  | nil => intro _ low hlow; exact absurd hlow (by simp)
  | cons l rest ih =>
    intro hs low hlow x hx
    have hsort : Sorted (imtAddrs (l :: rest)) := imtSorted_addrs_sorted hs
    rcases List.mem_cons.mp hlow with rfl | hlowr
    · -- low = l (head): x ≤ l.addr (x is the head) or x ≥ l.nextAddr (x after the head).
      rw [imtAddrs_cons] at hx
      rcases List.mem_cons.mp hx with rfl | hxr
      · exact Or.inl (le_refl _)
      · refine Or.inr ?_
        cases rest with
        | nil => exact absurd hxr (by simp)
        | cons r rest' =>
          rw [imtSorted_cons_cons] at hs
          rw [hs.2.1]
          rw [imtAddrs_cons] at hxr
          rcases List.mem_cons.mp hxr with rfl | hxr'
          · exact le_refl _
          · exact le_of_lt (head_lt_of_sorted (imtSorted_addrs_sorted hs.2.2) x hxr')
    · -- low ∈ rest.
      cases rest with
      | nil => exact absurd hlowr (by simp)
      | cons r rest' =>
        rw [imtAddrs_cons] at hx
        rcases List.mem_cons.mp hx with rfl | hxr
        · -- x = l.addr: l.addr < low.addr (head below every tail addr).
          refine Or.inl (le_of_lt ?_)
          have hlowaddr : low.addr ∈ imtAddrs (r :: rest') := mem_imtAddrs.mpr ⟨low, hlowr, rfl⟩
          exact head_lt_of_sorted hsort low.addr hlowaddr
        · rw [imtSorted_cons_cons] at hs
          exact ih hs.2.2 low hlowr x hxr

/-- **`imtAbsent_excludes` — THE POINTER-BRACKET NON-MEMBERSHIP KEYSTONE.** On an `ImtSorted` chain,
a single low-leaf pointer bracket `low.addr < k < low.nextAddr` proves `k` ABSENT from the address
spine — the deployed `.absent` open, with NO physical-position adjacency gate. K-GENERIC: the
bracket needs NOTHING from ℤ — the 8-felt lex key instantiates it directly. -/
theorem imtAbsent_excludes {c : List (ImtLeaf K V)} (hs : ImtSorted c) {k : K}
    (ha : ImtAbsent c k) : k ∉ imtAddrs c := by
  obtain ⟨low, hlow, h1, h2⟩ := ha
  intro hk
  rcases imtSorted_dichotomy hs low hlow k hk with hle | hge
  · exact absurd (lt_of_le_of_lt hle h1) (lt_irrefl _)
  · exact absurd (lt_of_lt_of_le h2 hge) (lt_irrefl _)

/-! ## §5 — INSERT: update-low + append, and PRESERVATION (the local per-row check). -/

/-- **`imtInsert c k v`** — the IMT insert: find the low leaf bracketing `k`, (i) update its
`nextAddr → k`, (ii) splice the new leaf `(k, v, low_oldNext)` right after it. TWO O(depth)
Merkle-path updates (no shift). On an `ImtSorted` chain the first bracketing leaf is the unique
one. -/
def imtInsert : List (ImtLeaf K V) → K → V → List (ImtLeaf K V)
  | [], _, _ => []
  | l :: rest, k, v =>
    if l.addr < k ∧ k < l.nextAddr then
      { l with nextAddr := k } :: { addr := k, value := v, nextAddr := l.nextAddr } :: rest
    else l :: imtInsert rest k v

theorem imtInsert_cons (l : ImtLeaf K V) (rest : List (ImtLeaf K V)) (k : K) (v : V) :
    imtInsert (l :: rest) k v =
      if l.addr < k ∧ k < l.nextAddr then
        { l with nextAddr := k } :: { addr := k, value := v, nextAddr := l.nextAddr } :: rest
      else l :: imtInsert rest k v := rfl

/-- `imtInsert` never changes the head ADDRESS (it only edits the low leaf's `nextAddr` and splices
AFTER it) — the fact preservation threads to keep the incoming link intact. -/
theorem imtInsert_head_addr (l : ImtLeaf K V) (rest : List (ImtLeaf K V)) (k : K) (v : V) :
    ∃ hd tl, imtInsert (l :: rest) k v = hd :: tl ∧ hd.addr = l.addr := by
  rw [imtInsert_cons]
  by_cases hbr : l.addr < k ∧ k < l.nextAddr
  · rw [if_pos hbr]; exact ⟨_, _, rfl, rfl⟩
  · rw [if_neg hbr]; exact ⟨l, imtInsert rest k v, rfl, rfl⟩

/-- **`imtInsert_preserves` — THE IN-CIRCUIT INDUCTION STEP (local pointer-bracket check).** Inserting
a pointer-bracket-absent key into an `ImtSorted` chain yields an `ImtSorted` chain: the spliced pair
`{low; nextAddr:=k}, {k; nextAddr:=low_oldNext}` keeps every link (`low.addr<k`, `k<low_oldNext`,
`k` links to the old successor). A LOCAL per-row check — NOT an O(n) rebuild. -/
theorem imtInsert_preserves : ∀ {c : List (ImtLeaf K V)}, ImtSorted c → ∀ {k : K} {v : V},
    ImtAbsent c k → ImtSorted (imtInsert c k v) := by
  intro c
  induction c with
  | nil =>
    intro _ k v ha
    obtain ⟨low, hlow, _⟩ := ha
    exact absurd hlow (by simp)
  | cons l rest ih =>
    intro hs k v ha
    rw [imtInsert_cons]
    by_cases hbr : l.addr < k ∧ k < l.nextAddr
    · rw [if_pos hbr]
      obtain ⟨hlk, hkn⟩ := hbr
      cases rest with
      | nil =>
        rw [imtSorted_cons_cons, imtSorted_singleton]
        exact ⟨hlk, rfl, hkn⟩
      | cons r rest' =>
        rw [imtSorted_cons_cons] at hs
        obtain ⟨_, hlr, htail⟩ := hs
        rw [imtSorted_cons_cons, imtSorted_cons_cons]
        exact ⟨hlk, rfl, hkn, hlr, htail⟩
    · rw [if_neg hbr]
      obtain ⟨low, hlow, hlowbr⟩ := ha
      have hlowrest : low ∈ rest := by
        rcases List.mem_cons.mp hlow with rfl | h
        · exact absurd hlowbr hbr
        · exact h
      cases rest with
      | nil => exact absurd hlowrest (by simp)
      | cons r rest' =>
        rw [imtSorted_cons_cons] at hs
        obtain ⟨hln, hlr, htail⟩ := hs
        have hins : ImtSorted (imtInsert (r :: rest') k v) :=
          ih htail ⟨low, hlowrest, hlowbr⟩
        obtain ⟨hd, tl, heq, hhd⟩ := imtInsert_head_addr r rest' k v
        rw [heq] at hins ⊢
        rw [imtSorted_cons_cons]
        exact ⟨hln, by rw [hhd]; exact hlr, hins⟩

/-- **`mem_imtAddrs_imtInsert` — the spine grows by EXACTLY the fresh key** (the `mem_sortedInsert`
analog for the IMT chain): after a bracketed insert, an address is present iff it is `k` or was
present. The insert is faithful — no ghost keys, no lost keys. -/
theorem mem_imtAddrs_imtInsert : ∀ {c : List (ImtLeaf K V)} {k : K} {v : V}, ImtAbsent c k →
    ∀ x, x ∈ imtAddrs (imtInsert c k v) ↔ x = k ∨ x ∈ imtAddrs c := by
  intro c
  induction c with
  | nil => intro k v ha; obtain ⟨low, hlow, _⟩ := ha; exact absurd hlow (by simp)
  | cons l rest ih =>
    intro k v ha x
    rw [imtInsert_cons]
    by_cases hbr : l.addr < k ∧ k < l.nextAddr
    · rw [if_pos hbr]
      simp only [imtAddrs_cons, List.mem_cons]
      constructor
      · rintro (rfl | rfl | h)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr h)
      · rintro (rfl | rfl | h)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr h)
    · rw [if_neg hbr]
      obtain ⟨low, hlow, hlowbr⟩ := ha
      have hlowrest : low ∈ rest := by
        rcases List.mem_cons.mp hlow with rfl | h
        · exact absurd hlowbr hbr
        · exact h
      rw [imtAddrs_cons, List.mem_cons, ih ⟨low, hlowrest, hlowbr⟩ x, imtAddrs_cons, List.mem_cons]
      tauto

/-! ## §6 — THE CHAIN: `Reachable ⟹ ImtSorted` (genesis + preservation, inductive invariant). -/

/-- **`Reachable lo hi c`** — the chains an honest turn stream reaches: the genesis sentinel chain,
or one bracketed insert from a reachable chain. The in-circuit turn chain (`heap_root` frame
continuity pins each turn's pre-root to the previous post-root). -/
inductive Reachable (lo hi : ℤ) : List ImtLeaf → Prop where
  | genesis : Reachable lo hi (genesis lo hi)
  | step {c k v} : Reachable lo hi c → ImtAbsent c k → Reachable lo hi (imtInsert c k v)

/-- **`reachable_sorted` — THE CHAIN INVARIANT.** `ImtSorted (genesis) ∧ (∀ turn, imtInsert preserves
ImtSorted) ⟹ ∀ reachable chain, ImtSorted`. Every root the honest chain reaches is a sorted IMT —
now FORCED by the per-turn local pointer-bracket check, not a trusted producer. -/
theorem reachable_sorted {lo hi : ℤ} (hlohi : lo < hi) {c : List ImtLeaf}
    (h : Reachable lo hi c) : ImtSorted c := by
  induction h with
  | genesis => exact genesis_sorted hlohi
  | step _ ha ih => exact imtInsert_preserves ih ha

/-- **`canonicalHeapExtract_of_imt` — CanonicalHeapExtract DERIVED.** The `SortedKeys h` premise the
7 mapOp effects carry inside `MapReconcileFamily`/`ReconcileGatesAt` (`MapOpsColumnLayout.lean:578`,
never derived from the deployed gates — the ASSUMPTION named in
`CANONICAL-HEAP-TREE-INVESTIGATION.md`) is, under the IMT, a THEOREM: any chain the honest turn
stream reaches projects to a `Heap.SortedKeys` felt heap. So the sortedness conjunct of
`CanonicalHeapExtract` reduces into `{Poseidon2SpongeCR, FRI-LDT}` (the leaf/root binding is
`imtLeafHash_injective` + the reused `pathRecompute_binds_updates`; the residual is exactly the STARK
floor, no separate heap-sortedness assumption). -/
theorem canonicalHeapExtract_of_imt {lo hi : ℤ} (hlohi : lo < hi) {c : List ImtLeaf}
    (hreach : Reachable lo hi c) : Heap.SortedKeys (imtToHeap c) :=
  imtSorted_sortedKeys (reachable_sorted hlohi hreach)

/-! ## §7 — ★ SOUNDNESS: the gap-#5 double-spend witness is UNSAT under the IMT. -/

/-- **`imt_double_spend_unsat` — THE SOUNDNESS PAYOFF.** Under `ImtSorted` a key CANNOT be BOTH
present in the chain AND pointer-bracket absent — the pointer bracket around `k` would have to point
THROUGH the present `k` (contradicting the well-linked dichotomy). The §3 double-spend (the spent
nullifier `25` placed out of sorted order, then bracketed absent by `20 < 25 < 30`) is impossible:
the forge needed a NON-sorted committed root, but the induction (`reachable_sorted`) forces every
reachable root `ImtSorted`, and this theorem then refutes the absence open. -/
theorem imt_double_spend_unsat {c : List (ImtLeaf K V)} (hs : ImtSorted c) {k : K}
    (hpresent : k ∈ imtAddrs c) (habsent : ImtAbsent c k) : False :=
  imtAbsent_excludes hs habsent hpresent

/-- The reachable-chain form: no honest-reachable IMT root admits a double-spend (present ∧
absence-provable) of ANY key. The deployed guarantee. -/
theorem imt_double_spend_unsat_reachable {lo hi : ℤ} (hlohi : lo < hi) {c : List ImtLeaf}
    (hreach : Reachable lo hi c) {k : ℤ}
    (hpresent : k ∈ imtAddrs c) (habsent : ImtAbsent c k) : False :=
  imt_double_spend_unsat (reachable_sorted hlohi hreach) hpresent habsent

/-! ## §8 — the O(depth) low-leaf UPDATE leg binds (reused `pathRecompute_binds_updates`). -/

/-- **`imtLowUpdate_binds`** — insert leg (i): the low-leaf `nextAddr → k` update is one O(depth)
Merkle-path recompute whose post-root BINDS the spliced digest vector, via the PROVEN
`pathRecompute_binds_updates` at the 3-felt IMT leaf (`imtLeafHash`). A frozen/forged post-root is a
Poseidon2 collision — the SAME extraction the write leg rides, here on the pointer update. -/
theorem imtLowUpdate_binds (hash : List ℤ → ℤ)
    (steps : List (Bool × ℤ)) (xs : List ℤ) (low : ImtLeaf) (newNext : ℤ)
    (hlen : xs.length = 2 ^ steps.length)
    (hroot : pathRecompute hash (imtLeafHash hash low) steps
      = perfectRoot hash steps.length xs)
    (hno : ¬ IsSpongeColl hash (pathCollFind hash steps xs (imtLeafHash hash low))) :
    xs[pathPos steps]? = some (imtLeafHash hash low) ∧
    pathRecompute hash (imtLeafHash hash { low with nextAddr := newNext }) steps
      = perfectRoot hash steps.length
          (xs.set (pathPos steps) (imtLeafHash hash { low with nextAddr := newNext })) := by
  obtain ⟨hmem, hupd⟩ :=
    pathRecompute_binds_updates hash steps xs (imtLeafHash hash low) hlen hroot hno
  exact ⟨hmem, hupd _⟩

/-! ## §9 — LIVENESS + NON-VACUITY TEETH (both polarities), on short literal `ℤ` chains
(heap-safe: pointer-local, no `2^16` object, no BabyBear field `decide`). -/

section Teeth

/-- A concrete genesis chain `[0 → 100]` (sentinels MIN=0, MAX=100). -/
def demoGenesis : List ImtLeaf := genesis 0 100

theorem demoGenesis_sorted : ImtSorted demoGenesis := genesis_sorted (by norm_num)

/-- Insert `20`, then `30` (each in its real pointer gap): the honest turn stream. -/
def demoChain : List ImtLeaf := imtInsert (imtInsert demoGenesis 20 7) 30 9

/-- `20` is bracket-absent in the genesis chain (`0 < 20 < 100`). -/
theorem demo_20_absent_genesis : ImtAbsent demoGenesis 20 :=
  ⟨{ addr := 0, value := 0, nextAddr := 100 }, by simp [demoGenesis, genesis], by norm_num, by norm_num⟩

/-- **LIVENESS — the honest chain stays `ImtSorted`.** Genesis + the two bracketed inserts is a valid
sorted IMT (`Reachable`, hence `ImtSorted`). -/
theorem demoChain_reachable : Reachable (0 : ℤ) 100 demoChain := by
  refine Reachable.step (Reachable.step Reachable.genesis demo_20_absent_genesis) ?_
  -- 30 is bracketed by the (20 → 100) leaf in `imtInsert demoGenesis 20 7`.
  exact ⟨{ addr := 20, value := 7, nextAddr := 100 }, by decide, by norm_num, by norm_num⟩

theorem demoChain_sorted : ImtSorted demoChain :=
  reachable_sorted (by norm_num) demoChain_reachable

/-- The projected felt heap of the honest chain is `Heap.SortedKeys` — CanonicalHeapExtract fired. -/
theorem demoChain_sortedKeys : Heap.SortedKeys (imtToHeap demoChain) :=
  canonicalHeapExtract_of_imt (by norm_num) demoChain_reachable

-- The chain's linked structure + address spine are exactly the sorted list {0,20,30} → sentinel:
#guard demoChain
  == [{ addr := 0, value := 0, nextAddr := 20 },
      { addr := 20, value := 7, nextAddr := 30 },
      { addr := 30, value := 9, nextAddr := 100 }]
#guard imtAddrs demoChain == [0, 20, 30]

/-- **RESPECTING TOOTH — `25` is pointer-bracket absent** (bracketed by the `20 → 30` leaf, ONE
opening, no adjacency gate): `imtAbsent_excludes` fires, `25 ∉ {0,20,30}`. -/
theorem demo_25_excluded : (25 : ℤ) ∉ imtAddrs demoChain :=
  imtAbsent_excludes demoChain_sorted
    ⟨{ addr := 20, value := 7, nextAddr := 30 }, by decide, by norm_num, by norm_num⟩

/-- **★ DOUBLE-SPEND TOOTH — a PRESENT key cannot be bracket-absent.** `20` is present in the honest
chain, so NO pointer bracket can straddle it (a bracket would point through `20`): the §3
double-spend is UNSAT on the reachable root. This is the anti-ghost — the keystone is not vacuously
excluding everything. -/
theorem demo_present_not_absent : ¬ ImtAbsent demoChain 20 := by
  intro ha
  exact imt_double_spend_unsat demoChain_sorted (by decide) ha

-- The fresh insert GROWS the spine by exactly the key (executable face of `mem_imtAddrs_imtInsert`):
#guard imtAddrs (imtInsert demoChain 25 5) == [0, 20, 25, 30]   -- 25 lands in its pointer gap
#guard imtAddrs (imtInsert demoGenesis 50 1) == [0, 50]         -- first real insert
-- ...and the inserted key is present-after (liveness):
#guard decide ((25 : ℤ) ∈ imtAddrs (imtInsert demoChain 25 5))
-- ...but absent-before (the freshness precondition holds):
#guard decide ((25 : ℤ) ∈ imtAddrs demoChain) == false

end Teeth

/-! ## §9b — ★ THE LAYOUT: the chain↔vector correspondence, and MEMBERSHIP DISCHARGED FROM IT.

This is the seam §10's bridge previously took as a bare `low ∈ c` MEMBERSHIP hypothesis. A2's law
lives on the FLAT committed digest vector `xs` (`xs[p1]? = some (imtLeafHash low)`, CR-bound); the
chain invariants live on the SORTED `c : List ImtLeaf`. The connecting fact is the placement of the
chain's leaves into the flat `2^dep` vector — the layout `heap_root.rs` maintains
(`CanonicalHeapTree8::new` places leaves at slots + `insert_witness_aafi.append_order_after` appends
at the free slot, low edited in place).

★ THE ORDER OBSERVATION (why membership is modelable but the placement is not a function of `c`):
the DEPLOYED placement is APPEND order (insertion history), NOT sorted order — the post-insert root is
`fold_append_order_8(append_order_after)`, so a later insert's pre-vector is append-, not sorted-,
ordered. The exact position of a leaf in `xs` is therefore order-dependent and NOT reconstructible
from the sorted `c` alone. BUT the fact the bridge needs — that the opened low leaf is a MEMBER of `c`
— is order-INVARIANT: it survives any permutation. So we model the physical vector as the layout of a
PHYSICAL leaf list `phys` that is a `List.Perm` of the logical chain `c` (same multiset, reordered),
and DISCHARGE membership from that. The residual is the named, differential-checkable
`ImtVecCorr` faithfulness (`xs = imtLayout phys ∧ phys ~ c`) — NOT a free membership. -/

section Layout

/-- **`imtLayout hash pad n phys`** — the flat committed digest vector obtained by placing the
PHYSICAL leaf list `phys` (the append-order slots the producer maintains) at positions `0…`, then
PADDING to length `n = 2^dep` with the empty-slot digest `pad`. The digest-vector face of
`heap_root.rs::fold_append_order_8` (the leaf-digest prefix + the empty-subtree padding). -/
def imtLayout (hash : List ℤ → ℤ) (pad : ℤ) (n : Nat) (phys : List ImtLeaf) : List ℤ :=
  phys.map (imtLeafHash hash) ++ List.replicate (n - phys.length) pad

/-- **`mem_phys_of_layout_get` — MEMBERSHIP FROM THE LAYOUT (a pure Lean fact).** Any occupied cell of
`imtLayout hash pad n phys` holding a leaf digest (distinct from the empty-slot `pad`) is the digest of
a genuine member of `phys`: the append-splits into the leaf-digest prefix (⟹ `∈ phys` by CR
injectivity) or the `pad` replicate (excluded by `hpad`). NO re-assumption — proved from `imtLayout`'s
definition. -/
theorem mem_phys_of_layout_get (hash : List ℤ → ℤ)
    {pad : ℤ} {n : Nat} {phys : List ImtLeaf} {p : Nat} {low : ImtLeaf}
    (hno : ¬ ImtLeafCollIn hash phys low)
    (hpad : imtLeafHash hash low ≠ pad)
    (hp : (imtLayout hash pad n phys)[p]? = some (imtLeafHash hash low)) :
    low ∈ phys := by
  have hmem : imtLeafHash hash low ∈ imtLayout hash pad n phys := List.mem_of_getElem? hp
  rw [imtLayout, List.mem_append] at hmem
  rcases hmem with hL | hR
  · rw [List.mem_map] at hL
    obtain ⟨l, hlp, hlh⟩ := hL
    rwa [imtLeafHash_injective hash (fun hc => hno ⟨l, hlp, hc⟩) hlh] at hlp
  · exact absurd (List.eq_of_mem_replicate hR) hpad

/-- **`ImtVecCorr hash pad n c xs`** — the chain↔vector correspondence the producer maintains, lifted
to a NAMED Lean predicate: the committed digest vector `xs` is the `imtLayout` of some physical leaf
list `phys` that is a `List.Perm` of the logical sorted chain `c`. This is the maximal honest content
below the (order-dependent) placement map: the permutation is all that survives the append-order
scramble, and it is exactly what membership needs. The named, differential-checkable Lean↔Rust
faithfulness (same class as every descriptor boundary) that REPLACES the bare `low ∈ c` hypothesis. -/
def ImtVecCorr (hash : List ℤ → ℤ) (pad : ℤ) (n : Nat)
    (c : List ImtLeaf) (xs : List ℤ) : Prop :=
  ∃ phys : List ImtLeaf, xs = imtLayout hash pad n phys ∧ List.Perm phys c

/-- **`imtVecCorr_mem` — the membership the bridge needs, DERIVED from the correspondence.** Given the
`ImtVecCorr` faithfulness, a CR-bound low leaf opened at any cell of `xs` (distinct from `pad`) is a
member of the sorted chain `c`: it is a member of the physical list (`mem_phys_of_layout_get`), and the
permutation carries membership to `c` (`Perm.mem_iff`). This is the pure Lean fact that discharges the
seam — the old `low ∈ c` hypothesis is now a THEOREM about the layout. -/
theorem imtVecCorr_mem (hash : List ℤ → ℤ)
    {pad : ℤ} {n : Nat} {c : List ImtLeaf} {xs : List ℤ} {p : Nat} {low : ImtLeaf}
    (hno : ¬ ImtLeafCollIn hash c low)
    (hcorr : ImtVecCorr hash pad n c xs)
    (hpad : imtLeafHash hash low ≠ pad)
    (hp : xs[p]? = some (imtLeafHash hash low)) :
    low ∈ c := by
  obtain ⟨phys, hxs, hperm⟩ := hcorr
  subst hxs
  refine hperm.mem_iff.mp (mem_phys_of_layout_get hash ?_ hpad hp)
  rintro ⟨l, hl, hc⟩
  exact hno ⟨l, hperm.mem_iff.mp hl, hc⟩

/-- **`PreRootModelsChain hash pad dep c oldRoot`** — the producer faithfulness for the AAFI PRE-root:
whatever digest vector the gate commits behind `oldRoot` (`oldRoot = perfectRoot hash dep xs`) is an
`ImtVecCorr` of the sorted chain `c`. The root→vector binding is the in-floor CR/FRI commitment; the
genuine residual carried here is the layout faithfulness `xs = imtLayout phys ∧ phys ~ c`. This is the
NAMED differential (what a `heap_root.rs`↔Lean check verifies: `xs` bytes = `imtLayout` of the
append-order `append_order_after`, a permutation of the `sorted_leaves` chain), NOT a free membership.
-/
def PreRootModelsChain (hash : List ℤ → ℤ) (pad : ℤ) (dep : Nat)
    (c : List ImtLeaf) (oldRoot : ℤ) : Prop :=
  ∀ xs : List ℤ, xs.length = 2 ^ dep → oldRoot = perfectRoot hash dep xs →
    ImtVecCorr hash pad (2 ^ dep) c xs

end Layout

/-! ## §10 — ★ THE AAFI BRIDGE: the deployed AAFI gates' law (A2) DERIVES sorted-chain preservation
and `CanonicalHeapExtract`, closing the gap-#5 residual into `{Poseidon2SpongeCR, FRI-LDT}`.

`MapOpsColumnLayout.aafiInsert_forces_imtInsert` (A2, PROVEN) delivers — from an accepting AAFI row —
the DIGEST-VECTOR FACE of the two-point update PLUS the pointer bracket `low.addr < k < low.next`
(the `ImtAbsent` witness, forced by the deployed range gate, NOT a free witness). A2 could not name
`imtInsert`/`imtInsert_preserves` (`IndexedMerkleTree` IMPORTS `MapOpsColumnLayout`, not the reverse),
so the one-lemma follow-up lives HERE, where both A2's law and `imtInsert_preserves` are in scope.

⚠ NAMED SHAPE SEAM (per `feedback-named-seam-is-not-a-hole.md`) — NOW DISCHARGED into the layout (§9b):
A2's conclusion lives on the FLAT committed digest vector `xs : List ℤ` (length `2^dep`, positions
`p1/p2`); `imtInsert` lives on the SORTED chain `c : List ImtLeaf`. The connecting fact — that the low
leaf the AAFI row OPENS (bound into `xs` at `p1` by `pathRecompute_binds_updates` under CR) is a MEMBER
of the sorted chain `c` — was previously a bare `(⟨lowAddr,lowValue,lowNext⟩ : ImtLeaf) ∈ c` hypothesis.
§9b MODELS the chain↔vector correspondence (`imtLayout` + `ImtVecCorr`) and DISCHARGES membership FROM
it (`imtVecCorr_mem`): the `_layout` bridge (§10-L) consumes `PreRootModelsChain` — the named,
differential-checkable faithfulness `xs = imtLayout phys ∧ phys ~ c` — and DERIVES `low ∈ c` as a
theorem. The exact placement is order-dependent (append order, not a function of `c`) and stays as the
differential, but MEMBERSHIP is order-invariant, so nothing about `low ∈ c` remains assumed. The plain
`aafiGates_force_*` below still take the raw membership (the underlying lemmas the `_layout` twins call);
the deployed guarantee is the `_layout` chain: gap #5 reduces into `{Poseidon2SpongeCR, FRI-LDT}` + the
`PreRootModelsChain` layout differential — same class as every Lean↔Rust descriptor boundary. -/

section AafiBridge

open Dregg2.Circuit.Poseidon2Binding.Reference (refSponge refSponge_CR)

/-- **`aafiGates_force_imtAbsent` — the deployed range gate FORCES the `ImtAbsent` witness.** An
accepting AAFI row (`AafiGatesAt`) whose opened low leaf `⟨lowAddr, lowValue, lowNext⟩` is a member of
the sorted chain `c` FORCES `k` pointer-bracket-absent from `c`: A2's law surfaces the bracket
`lowAddr < k < lowNext` (forced by the deployed range gate through `pathRecompute_binds_updates`), and
the membership completes the `∃ low ∈ c, …` witness. NO re-assumption — the bracket is gate-forced. -/
theorem aafiGates_force_imtAbsent (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (dep : Nat)
    {c : List ImtLeaf} {oldRoot newRoot k v lowAddr lowValue lowNext freeEmpty : ℤ}
    (hg : MapOpsColumnLayout.AafiGatesAt hash dep
      oldRoot newRoot k v lowAddr lowValue lowNext freeEmpty)
    (hlow : (⟨lowAddr, lowValue, lowNext⟩ : ImtLeaf) ∈ c) :
    ImtAbsent c k := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hlk, hkn⟩ :=
    MapOpsColumnLayout.aafiInsert_forces_imtInsert hash hCR dep hg
  exact ⟨⟨lowAddr, lowValue, lowNext⟩, hlow, hlk, hkn⟩

/-- **`aafiGates_force_sortedKeys` — the deployed AAFI gates DERIVE sorted-chain preservation.** On an
`ImtSorted` pre-chain, an accepting AAFI row whose opened low leaf is in the chain yields (i) an
`ImtSorted` POST-chain (`imtInsert_preserves`, applicable because A2's bracket is the `ImtAbsent`
bracket) and (ii) its projected felt heap is `Heap.SortedKeys` (`imtSorted_sortedKeys`). So the
deployed gates FORCE the sortedness `CanonicalHeapExtract` carries — not a trusted producer. -/
theorem aafiGates_force_sortedKeys (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (dep : Nat)
    {c : List ImtLeaf} {oldRoot newRoot k v lowAddr lowValue lowNext freeEmpty : ℤ}
    (hs : ImtSorted c)
    (hg : MapOpsColumnLayout.AafiGatesAt hash dep
      oldRoot newRoot k v lowAddr lowValue lowNext freeEmpty)
    (hlow : (⟨lowAddr, lowValue, lowNext⟩ : ImtLeaf) ∈ c) :
    ImtSorted (imtInsert c k v) ∧ Heap.SortedKeys (imtToHeap (imtInsert c k v)) := by
  have hpost : ImtSorted (imtInsert c k v) :=
    imtInsert_preserves hs (aafiGates_force_imtAbsent hash hCR dep hg hlow)
  exact ⟨hpost, imtSorted_sortedKeys hpost⟩

/-! ### §10-L — ★ THE REWIRED BRIDGE: consume the `imtLayout`-correspondence, not a bare membership.
The `_layout` lemmas DISCHARGE the `low ∈ c` the plain bridge assumed — they DERIVE it from the named
`PreRootModelsChain` faithfulness (`imtVecCorr_mem` on A2's CR-bound opening `xs[p1]? = some (low)`),
so the seam is now `xs = imtLayout phys ∧ phys ~ c` (differential-checkable), not a free `low ∈ c`. -/

/-- **`aafiGates_force_lowMem_layout` — the LOW-LEAF MEMBERSHIP, discharged from the layout.** The seam
itself, closed: A2's CR-bound opening `xs[p1]? = some (imtLeafHash low)` against the committed pre-root,
fed through the `PreRootModelsChain` layout faithfulness (`imtVecCorr_mem`), YIELDS `low ∈ c`. This is
the fact the plain bridge took as a bare hypothesis — now a theorem about `imtLayout`. -/
theorem aafiGates_force_lowMem_layout (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep : Nat) (pad : ℤ)
    {c : List ImtLeaf} {oldRoot newRoot k v lowAddr lowValue lowNext freeEmpty : ℤ}
    (hg : MapOpsColumnLayout.AafiGatesAt hash dep
      oldRoot newRoot k v lowAddr lowValue lowNext freeEmpty)
    (hpad : imtLeafHash hash ⟨lowAddr, lowValue, lowNext⟩ ≠ pad)
    (hcorr : PreRootModelsChain hash pad dep c oldRoot) :
    (⟨lowAddr, lowValue, lowNext⟩ : ImtLeaf) ∈ c := by
  obtain ⟨xs, p1, p2, hlen, hne, hor, hmem1, hmem2, hnew, hlk, hkn⟩ :=
    MapOpsColumnLayout.aafiInsert_forces_imtInsert hash hCR dep hg
  -- `aafiLeafHash hash a v n` and `imtLeafHash hash ⟨a,v,n⟩` are both `hash [a,v,n]` (defeq).
  have hmem1' : xs[p1]? = some (imtLeafHash hash ⟨lowAddr, lowValue, lowNext⟩) := hmem1
  exact imtVecCorr_mem hash (noImtLeafCollIn_of_CR hCR) (hcorr xs hlen hor) hpad hmem1'

/-- **`aafiGates_force_imtAbsent_layout` — the bracket witness with membership DISCHARGED.** Same
conclusion as `aafiGates_force_imtAbsent`, but instead of the bare `low ∈ c` hypothesis it consumes the
`PreRootModelsChain` layout faithfulness (and the low leaf ≠ the empty-slot digest): the membership is
now derived (`aafiGates_force_lowMem_layout`) and A2's forced bracket completes the `ImtAbsent c k`
witness. The membership is a THEOREM about the layout, not an import from the producer. -/
theorem aafiGates_force_imtAbsent_layout (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep : Nat) (pad : ℤ)
    {c : List ImtLeaf} {oldRoot newRoot k v lowAddr lowValue lowNext freeEmpty : ℤ}
    (hg : MapOpsColumnLayout.AafiGatesAt hash dep
      oldRoot newRoot k v lowAddr lowValue lowNext freeEmpty)
    (hpad : imtLeafHash hash ⟨lowAddr, lowValue, lowNext⟩ ≠ pad)
    (hcorr : PreRootModelsChain hash pad dep c oldRoot) :
    ImtAbsent c k :=
  aafiGates_force_imtAbsent hash hCR dep hg
    (aafiGates_force_lowMem_layout hash hCR dep pad hg hpad hcorr)

/-- **`aafiGates_force_sortedKeys_layout` — sorted-chain preservation with membership DISCHARGED.** The
`_layout` twin of `aafiGates_force_sortedKeys`: on an `ImtSorted` pre-chain, an accepting AAFI row plus
the `PreRootModelsChain` layout faithfulness yields the `ImtSorted` post-chain and its `Heap.SortedKeys`
projection — the sortedness `CanonicalHeapExtract` carries, now forced by the gates and the NAMED
layout correspondence, with NO free membership. -/
theorem aafiGates_force_sortedKeys_layout (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (dep : Nat) (pad : ℤ)
    {c : List ImtLeaf} {oldRoot newRoot k v lowAddr lowValue lowNext freeEmpty : ℤ}
    (hs : ImtSorted c)
    (hg : MapOpsColumnLayout.AafiGatesAt hash dep
      oldRoot newRoot k v lowAddr lowValue lowNext freeEmpty)
    (hpad : imtLeafHash hash ⟨lowAddr, lowValue, lowNext⟩ ≠ pad)
    (hcorr : PreRootModelsChain hash pad dep c oldRoot) :
    ImtSorted (imtInsert c k v) ∧ Heap.SortedKeys (imtToHeap (imtInsert c k v)) := by
  have hpost : ImtSorted (imtInsert c k v) :=
    imtInsert_preserves hs (aafiGates_force_imtAbsent_layout hash hCR dep pad hg hpad hcorr)
  exact ⟨hpost, imtSorted_sortedKeys hpost⟩

/-- **`AafiReachableL`** — the DEPLOYED AAFI stream with the seam DISCHARGED: each step is an accepting
AAFI gate row PLUS the NAMED `PreRootModelsChain` layout faithfulness (and the low leaf ≠ empty),
replacing the bare `low ∈ c`. Membership is derived per step from the layout, so this reachability rests
on `{Poseidon2SpongeCR, FRI-LDT}` + the differential-checkable `xs = imtLayout phys ∧ phys ~ c`. -/
inductive AafiReachableL (hash : List ℤ → ℤ) (pad : ℤ) (dep : Nat) (lo hi : ℤ) :
    List ImtLeaf → Prop where
  | genesis : AafiReachableL hash pad dep lo hi (genesis lo hi)
  | step {c k v oldRoot newRoot lowAddr lowValue lowNext freeEmpty} :
      AafiReachableL hash pad dep lo hi c →
      MapOpsColumnLayout.AafiGatesAt hash dep
        oldRoot newRoot k v lowAddr lowValue lowNext freeEmpty →
      imtLeafHash hash ⟨lowAddr, lowValue, lowNext⟩ ≠ pad →
      PreRootModelsChain hash pad dep c oldRoot →
      AafiReachableL hash pad dep lo hi (imtInsert c k v)

/-- **`aafiReachableL_sorted` — THE AAFI CHAIN INVARIANT, seam discharged.** Every chain the deployed
AAFI stream reaches is `ImtSorted`, with each step's membership DERIVED from the layout faithfulness
(`aafiGates_force_imtAbsent_layout`) rather than assumed. -/
theorem aafiReachableL_sorted (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (pad : ℤ)
    (dep : Nat) {lo hi : ℤ} (hlohi : lo < hi) {c : List ImtLeaf}
    (h : AafiReachableL hash pad dep lo hi c) : ImtSorted c := by
  induction h with
  | genesis => exact genesis_sorted hlohi
  | step _ hg hpad hcorr ih =>
      exact imtInsert_preserves ih (aafiGates_force_imtAbsent_layout hash hCR dep pad hg hpad hcorr)

/-- **`aafiChainL_canonicalHeapExtract` — CanonicalHeapExtract DERIVED, seam discharged.** Every root
the deployed AAFI stream reaches projects to `Heap.SortedKeys` — the residual is now EXACTLY
`{Poseidon2SpongeCR, FRI-LDT}` + the NAMED `PreRootModelsChain` layout differential, with the low-leaf
membership no longer a free assumption but a theorem (`imtVecCorr_mem`). -/
theorem aafiChainL_canonicalHeapExtract (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (pad : ℤ)
    (dep : Nat) {lo hi : ℤ} (hlohi : lo < hi) {c : List ImtLeaf}
    (h : AafiReachableL hash pad dep lo hi c) : Heap.SortedKeys (imtToHeap c) :=
  imtSorted_sortedKeys (aafiReachableL_sorted hash hCR pad dep hlohi h)

/-- **`AafiReachable`** — the chains the DEPLOYED AAFI-routed turn stream reaches: the genesis
sentinel chain, or one accepting AAFI ROW (`AafiGatesAt` + the opened low leaf in the current chain)
from a reachable chain. The `Reachable` twin whose step is an actual GATE acceptance rather than an
abstract `ImtAbsent` — the bridge derives the `ImtAbsent` the step needs from the gate. -/
inductive AafiReachable (hash : List ℤ → ℤ) (dep : Nat) (lo hi : ℤ) : List ImtLeaf → Prop where
  | genesis : AafiReachable hash dep lo hi (genesis lo hi)
  | step {c k v oldRoot newRoot lowAddr lowValue lowNext freeEmpty} :
      AafiReachable hash dep lo hi c →
      MapOpsColumnLayout.AafiGatesAt hash dep
        oldRoot newRoot k v lowAddr lowValue lowNext freeEmpty →
      (⟨lowAddr, lowValue, lowNext⟩ : ImtLeaf) ∈ c →
      AafiReachable hash dep lo hi (imtInsert c k v)

/-- **`aafiReachable_sorted` — THE AAFI CHAIN INVARIANT.** Every chain the deployed AAFI-routed stream
reaches is `ImtSorted`: genesis is sorted, and each accepting AAFI row's gate-forced bracket (via the
bridge) drives `imtInsert_preserves`. The sorted-chain induction is DISCHARGED by the deployed gates,
not assumed. -/
theorem aafiReachable_sorted (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (dep : Nat)
    {lo hi : ℤ} (hlohi : lo < hi) {c : List ImtLeaf}
    (h : AafiReachable hash dep lo hi c) : ImtSorted c := by
  induction h with
  | genesis => exact genesis_sorted hlohi
  | step _ hg hlow ih => exact imtInsert_preserves ih (aafiGates_force_imtAbsent hash hCR dep hg hlow)

/-- **`aafiChain_canonicalHeapExtract` — CanonicalHeapExtract DERIVED for the AAFI accumulators.** Every
root the deployed AAFI-routed stream reaches from the sorted genesis projects to a `Heap.SortedKeys`
felt heap — the `SortedKeys h` premise the 7 mapOp effects carry inside `MapReconcileFamily` is, for
the AAFI path, a THEOREM forced by the gates (`aafiReachable_sorted` + `imtSorted_sortedKeys`). The
leaf/root binding is `imtLeafHash_injective` + the reused `pathRecompute_binds_updates` (twice, inside
A2); the residual is EXACTLY `{Poseidon2SpongeCR, FRI-LDT}` — no separate heap-sortedness assumption. -/
theorem aafiChain_canonicalHeapExtract (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (dep : Nat)
    {lo hi : ℤ} (hlohi : lo < hi) {c : List ImtLeaf}
    (h : AafiReachable hash dep lo hi c) : Heap.SortedKeys (imtToHeap c) :=
  imtSorted_sortedKeys (aafiReachable_sorted hash hCR dep hlohi h)

/-- **`aafiReachableL_toReachable`** — the DISCHARGED reachability REFINES the plain one: every step's
derived `low ∈ c` (via the layout, `aafiGates_force_lowMem_layout`) is exactly the membership the plain
`AafiReachable.step` took as data. So `AafiReachableL` is a genuine strengthening — it consumes strictly
less (a checkable layout fact, not a free membership) yet reaches the same chains. -/
theorem aafiReachableL_toReachable (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) (pad : ℤ)
    (dep : Nat) {lo hi : ℤ} {c : List ImtLeaf}
    (h : AafiReachableL hash pad dep lo hi c) : AafiReachable hash dep lo hi c := by
  induction h with
  | genesis => exact AafiReachable.genesis
  | step _ hg hpad hcorr ih =>
      exact AafiReachable.step ih hg (aafiGates_force_lowMem_layout hash hCR dep pad hg hpad hcorr)

/-! ### §10a — NON-VACUITY TEETH: a concrete accepting AAFI row FIRES the derivation; a forged
(out-of-gap) row admits NO gate, so it cannot reach it. On the CR-proved reference sponge, at the
2-level toy heap (heap-safe: depth-generic law applied symbolically, no `2^16` object, no field
`decide`); reuses A2's `aafi_toy_gates` / `aafi_toy_out_of_gap_bites`. -/

/-- **★ RESPECTING TOOTH — the AAFI row FIRES the derivation.** The honest gate data inserting
`50 ↦ 7` in the genesis `(0 → 100)` gap (A2's `aafi_toy_gates`, low leaf `⟨0,0,100⟩ ∈ genesis 0 100`)
steps `AafiReachable`: the deployed gate DERIVES a reachable post-chain. -/
theorem aafi_genesis_reachable :
    AafiReachable refSponge 2 (0 : ℤ) 100 (imtInsert (genesis 0 100) 50 7) :=
  AafiReachable.step AafiReachable.genesis
    (MapOpsColumnLayout.aafi_toy_gates refSponge) (by simp [genesis])

/-- **★ …and it PROJECTS to `Heap.SortedKeys`** — `CanonicalHeapExtract` fired end-to-end from the
deployed AAFI gate acceptance, through the bridge, to the sortedness conjunct. Non-vacuous: a real
accepting row produces a real `SortedKeys` heap. -/
theorem aafi_genesis_sortedKeys :
    Heap.SortedKeys (imtToHeap (imtInsert (genesis 0 100) 50 7)) :=
  aafiChain_canonicalHeapExtract refSponge refSponge_CR 2 (by norm_num) aafi_genesis_reachable

/-- **REJECT TOOTH — a FORGED (out-of-gap) row admits NO gate.** A key `150` outside the `(0, 100)`
pointer gap has no accepting AAFI gate data (A2's `aafi_toy_out_of_gap_bites`: the range gate demands
`150 < 100`, false), so NO `AafiReachable.step` can be built from it — the derivation fires only on
genuinely bracketed inserts, never on the out-of-gap (double-spend-shape) forge. -/
theorem aafi_forged_no_gate :
    ¬ MapOpsColumnLayout.AafiGatesAt refSponge 2
        (MapOpsColumnLayout.aafiOldRootToy refSponge)
        (MapOpsColumnLayout.aafiNewRootToy refSponge) 150 7 0 0 100
        (MapOpsColumnLayout.aafiEmpty refSponge) :=
  MapOpsColumnLayout.aafi_toy_out_of_gap_bites refSponge

/-! ### §10b — LAYOUT NON-VACUITY: the DISCHARGED bridge fires end-to-end — membership DERIVED from a
real `imtLayout`, not re-assumed; a concrete `ImtVecCorr`/`PreRootModelsChain` holds for the toy
pre-root (via `perfectRoot_injective`). Heap-safe: the layout is a 4-cell symbolic list, no `2^16`,
no field `decide`. -/

open Dregg2.Circuit.MapMerkleRoot (perfectRoot_injective)

/-- The genesis MIN-sentinel leaf `⟨0,0,100⟩` is DISTINCT from the empty-slot digest `hash[0,0,0]`:
under CR, `hash[0,0,100] = hash[0,0,0]` would force `100 = 0`. Discharges the `hpad` side-condition —
no real bracketing low leaf collides with the pad. -/
theorem toy_low_ne_pad :
    imtLeafHash refSponge ⟨0, 0, 100⟩ ≠ MapOpsColumnLayout.aafiEmpty refSponge := by
  intro h
  have h' : imtLeafHash refSponge ⟨0, 0, 100⟩ = imtLeafHash refSponge ⟨0, 0, 0⟩ := h
  have heq : (⟨0, 0, 100⟩ : ImtLeaf) = ⟨0, 0, 0⟩ :=
    imtLeafHash_injective refSponge (noImtLeafColl_of_CR refSponge_CR) h'
  exact absurd (congrArg ImtLeaf.nextAddr heq) (by norm_num)

/-- **★ `ImtVecCorr` HOLDS concretely** — the toy committed vector `aafiXsToy` IS the `imtLayout` of the
genesis chain (`phys = genesis 0 100`, a `List.Perm.refl`): the low leaf at cell 0, empties elsewhere.
The correspondence predicate is inhabited by a real layout, not vacuous. -/
theorem toy_imtVecCorr :
    ImtVecCorr refSponge (MapOpsColumnLayout.aafiEmpty refSponge) 4
      (genesis 0 100) (MapOpsColumnLayout.aafiXsToy refSponge) :=
  ⟨genesis 0 100, rfl, List.Perm.refl _⟩

/-- **★ `PreRootModelsChain` HOLDS for the toy pre-root** — any length-4 vector committing to
`aafiOldRootToy` IS the genesis layout: `perfectRoot_injective` peels the root to `aafiXsToy`, then
`toy_imtVecCorr`. The named faithfulness is discharged for a concrete pre-root — the residual is a
GENUINE, satisfiable predicate (the differential a `heap_root.rs`↔Lean check certifies), not a hole. -/
theorem toy_preRootModelsChain :
    PreRootModelsChain refSponge (MapOpsColumnLayout.aafiEmpty refSponge) 2
      (genesis 0 100) (MapOpsColumnLayout.aafiOldRootToy refSponge) := by
  intro xs hxlen hroot
  have hxsToyLen : (MapOpsColumnLayout.aafiXsToy refSponge).length = 2 ^ 2 := by decide
  have hroots : perfectRoot refSponge 2 (MapOpsColumnLayout.aafiXsToy refSponge)
      = perfectRoot refSponge 2 xs := by
    rw [show perfectRoot refSponge 2 (MapOpsColumnLayout.aafiXsToy refSponge)
          = MapOpsColumnLayout.aafiOldRootToy refSponge from rfl, hroot]
  have hxs : MapOpsColumnLayout.aafiXsToy refSponge = xs :=
    perfectRoot_injective refSponge refSponge_CR 2 hxsToyLen hxlen hroots
  rw [← hxs]; exact toy_imtVecCorr

/-- **★ MEMBERSHIP DISCHARGED — the seam CLOSED end-to-end.** `aafiGates_force_lowMem_layout` DERIVES
`⟨0,0,100⟩ ∈ genesis 0 100` from the accepting toy gate + the layout faithfulness — the fact the plain
bridge took as a bare hypothesis is now PRODUCED, on a real accepting row. NOT re-assumed. -/
theorem aafiL_lowMem_fires :
    (⟨0, 0, 100⟩ : ImtLeaf) ∈ genesis (0 : ℤ) 100 :=
  aafiGates_force_lowMem_layout refSponge refSponge_CR 2 (MapOpsColumnLayout.aafiEmpty refSponge)
    (MapOpsColumnLayout.aafi_toy_gates refSponge) toy_low_ne_pad toy_preRootModelsChain

/-- **★ RESPECTING TOOTH (layout path) — the DISCHARGED AAFI row FIRES.** The honest gate data plus the
NAMED layout faithfulness steps `AafiReachableL` — the deployed gate DERIVES a reachable post-chain with
the low membership no longer assumed but proved from `imtLayout`. -/
theorem aafiL_genesis_reachable :
    AafiReachableL refSponge (MapOpsColumnLayout.aafiEmpty refSponge) 2 (0 : ℤ) 100
      (imtInsert (genesis 0 100) 50 7) :=
  AafiReachableL.step AafiReachableL.genesis
    (MapOpsColumnLayout.aafi_toy_gates refSponge) toy_low_ne_pad toy_preRootModelsChain

/-- **★ …and it PROJECTS to `Heap.SortedKeys`** — `CanonicalHeapExtract` fired from the deployed gate
acceptance, through the DISCHARGED bridge (membership from the layout), to the sortedness conjunct. The
gap-#5 residual for this path is `{Poseidon2SpongeCR, FRI-LDT}` + the named `PreRootModelsChain`
differential — no free membership. -/
theorem aafiL_genesis_sortedKeys :
    Heap.SortedKeys (imtToHeap (imtInsert (genesis 0 100) 50 7)) :=
  aafiChainL_canonicalHeapExtract refSponge refSponge_CR
    (MapOpsColumnLayout.aafiEmpty refSponge) 2 (by norm_num) aafiL_genesis_reachable

end AafiBridge

/-! ## §11 — AXIOM HYGIENE. -/

#assert_axioms imtLeafHash_injective
#assert_axioms imtSorted_addrs_sorted
#assert_axioms imtSorted_sortedKeys
#assert_axioms imtSorted_dichotomy
#assert_axioms imtAbsent_excludes
#assert_axioms imtInsert_preserves
#assert_axioms mem_imtAddrs_imtInsert
#assert_axioms reachable_sorted
#assert_axioms canonicalHeapExtract_of_imt
#assert_axioms imt_double_spend_unsat
#assert_axioms imt_double_spend_unsat_reachable
#assert_axioms imtLowUpdate_binds
#assert_axioms demoChain_reachable
#assert_axioms demo_25_excluded
#assert_axioms demo_present_not_absent
#assert_axioms aafiGates_force_imtAbsent
#assert_axioms aafiGates_force_sortedKeys
#assert_axioms aafiReachable_sorted
#assert_axioms aafiChain_canonicalHeapExtract
#assert_axioms aafi_genesis_reachable
#assert_axioms aafi_genesis_sortedKeys
#assert_axioms aafi_forged_no_gate
-- §9b/§10-L: the layout correspondence + the DISCHARGED bridge (membership no longer assumed).
#assert_axioms mem_phys_of_layout_get
#assert_axioms imtVecCorr_mem
#assert_axioms aafiGates_force_lowMem_layout
#assert_axioms aafiGates_force_imtAbsent_layout
#assert_axioms aafiGates_force_sortedKeys_layout
#assert_axioms aafiReachableL_sorted
#assert_axioms aafiChainL_canonicalHeapExtract
#assert_axioms aafiReachableL_toReachable
#assert_axioms toy_low_ne_pad
#assert_axioms toy_imtVecCorr
#assert_axioms toy_preRootModelsChain
#assert_axioms aafiL_lowMem_fires
#assert_axioms aafiL_genesis_reachable
#assert_axioms aafiL_genesis_sortedKeys

end Dregg2.Circuit.IndexedMerkleTree
