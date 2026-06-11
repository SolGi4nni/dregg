/-
# Dregg2.Lightclient.HistoryIndex — the receipt index as an openable sorted map.

THE NON-OMISSION FOUNDATION, part 1 of 2. A light client asking "show me the receipts for cell `c`
between heights `h₁` and `h₂`" needs more than soundness (every shown receipt is real — a membership
opening); it needs COMPLETENESS (no receipt was hidden — a gap opening). This module builds the
INDEX that makes both available against one committed root:

  * the index is the GENERIC sorted map of `Dregg2.Substrate.Heap` §1 (the proven `cap_root`
    machinery with a generic leaf), keyed by `(subject, height, seq)` in LEXICOGRAPHIC order —
    so "subject `c`, heights `h₁..h₂`" is a CONTIGUOUS key range, answerable by openings + gaps;
  * RANGE RESTRICTION `rangeOf` (the exact answer to a range query) is proven determined by the
    map's lookup semantics alone (`rangeOf_ext` via the canonical `ext_get`), hence by the root;
  * the committed root `iroot` (sponge of `hash[subject, height, seq, commitment]` leaves) BINDS
    the whole index (`iroot_injective`) and therefore every range (`iroot_binds_range`) — under the
    SAME single named crypto floor the cap-root/heap advance carries (`Poseidon2SpongeCR`);
  * insertion (`addReceipt` = the heap's sorted insert-or-update `set`) preserves the sorted
    invariant (`addReceipt_sorted` — `Heap.set_sorted` instantiated).

`Dregg2.Lightclient.AttestedQuery` (part 2) puts the query/answer protocol ON this index and proves
THE THEOREM: a verifying answer cannot omit a receipt in the queried range.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. Crypto enters ONLY as
the named `Poseidon2SpongeCR` hypothesis (the one floor), never as an axiom. No `sorry`. NEW file;
all imports read-only.
-/
import Dregg2.Substrate.Heap
import Mathlib.Data.Prod.Lex

namespace Dregg2.Lightclient.HistoryIndex

open Dregg2.Substrate.Heap
open Dregg2.Crypto.NonMembership (Sorted Adjacent)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

universe u v

variable {κ : Type u} {ν : Type v} [LinearOrder κ]

/-! ## §1 — range restriction on the generic sorted map (the exact answer to a range query).

`Heap` §1 gives `get`/`set`/`SortedKeys`/`ext_get`/`get_none_of_gap` over any `LinearOrder` key.
Here we add the RANGE face: `inRange`/`rangeOf`, the membership/lookup characterizations a query
answer is checked against, and the determinism transfer (same lookups ⇒ same range restriction). -/

/-- **`inRange lo hi k`** — the queried closed key interval `[lo, hi]`. -/
def inRange (lo hi k : κ) : Prop := lo ≤ k ∧ k ≤ hi

instance (lo hi k : κ) : Decidable (inRange lo hi k) := by unfold inRange; infer_instance

/-- **`rangeOf h lo hi`** — the EXACT range restriction: the entries of `h` whose key lies in
`[lo, hi]`, in index (key-sorted) order. THE complete answer a range query must equal. -/
def rangeOf (h : List (κ × ν)) (lo hi : κ) : List (κ × ν) :=
  h.filter (fun e => decide (inRange lo hi e.1))

/-- Membership in the range restriction is membership-in-the-index AND in-range. -/
theorem mem_rangeOf {h : List (κ × ν)} {lo hi : κ} {e : κ × ν} :
    e ∈ rangeOf h lo hi ↔ e ∈ h ∧ inRange lo hi e.1 := by
  simp [rangeOf, List.mem_filter]

/-- The range restriction of a sorted map is sorted (a filter is a sublist; `Pairwise` descends). -/
theorem rangeOf_sorted (h : List (κ × ν)) (lo hi : κ) (hs : SortedKeys h) :
    SortedKeys (rangeOf h lo hi) :=
  List.Pairwise.sublist (List.Sublist.map Prod.fst List.filter_sublist) hs

omit [LinearOrder κ] in
/-- A key is on the spine iff some entry carries it. -/
theorem mem_keys_iff {h : List (κ × ν)} {k : κ} : k ∈ keys h ↔ ∃ v, (k, v) ∈ h := by
  constructor
  · intro hk
    obtain ⟨⟨a, b⟩, hm, rfl⟩ := List.mem_map.mp hk
    exact ⟨b, hm⟩
  · rintro ⟨v, hm⟩
    exact List.mem_map.mpr ⟨(k, v), hm, rfl⟩

/-- A successful lookup exhibits a genuine entry (no sortedness needed). -/
theorem mem_of_get_eq_some {h : List (κ × ν)} {k : κ} {v : ν} (hg : get h k = some v) :
    (k, v) ∈ h := by
  induction h with
  | nil => simp at hg
  | cons hd t ih =>
    obtain ⟨k', v'⟩ := hd
    by_cases heq : k = k'
    · subst heq
      rw [get_cons_self] at hg
      exact List.mem_cons.mpr (Or.inl (by rw [Option.some.inj hg]))
    · rw [get_cons_ne v' t heq] at hg
      exact List.mem_cons_of_mem _ (ih hg)

/-- On a SORTED map every genuine entry is found by lookup (keys are unique, so the first match is
the only match). -/
theorem get_eq_some_of_mem {h : List (κ × ν)} (hs : SortedKeys h) {k : κ} {v : ν}
    (hm : (k, v) ∈ h) : get h k = some v := by
  induction h with
  | nil => simp at hm
  | cons hd t ih =>
    obtain ⟨k', v'⟩ := hd
    rcases List.mem_cons.mp hm with heq | htail
    · rw [Prod.mk.injEq] at heq
      rw [heq.1, heq.2, get_cons_self]
    · have hne : k ≠ k' := by
        rintro rfl
        exact head_key_not_mem hs (mem_keys_iff.mpr ⟨v, htail⟩)
      rw [get_cons_ne v' t hne]
      exact ih (sortedKeys_tail hs) htail

/-- **The lookup⇔membership characterization** on a sorted map — the semantic content a membership
opening certifies, in both directions. -/
theorem get_eq_some_iff_mem {h : List (κ × ν)} (hs : SortedKeys h) {k : κ} {v : ν} :
    get h k = some v ↔ (k, v) ∈ h :=
  ⟨mem_of_get_eq_some, get_eq_some_of_mem hs⟩

/-- **Determinism transfer (`rangeOf_ext`)** — two sorted maps with the same lookup semantics have
the SAME range restriction, for every range. Rides `ext_get` (canonicity): same lookups ⇒ equal
leaf lists ⇒ equal filters. The combinatorial half of "the root determines every range". -/
theorem rangeOf_ext {h₁ h₂ : List (κ × ν)} (hs₁ : SortedKeys h₁) (hs₂ : SortedKeys h₂)
    (hext : ∀ k, get h₁ k = get h₂ k) (lo hi : κ) :
    rangeOf h₁ lo hi = rangeOf h₂ lo hi := by
  rw [ext_get hs₁ hs₂ hext]

#assert_axioms mem_rangeOf
#assert_axioms rangeOf_sorted
#assert_axioms mem_keys_iff
#assert_axioms mem_of_get_eq_some
#assert_axioms get_eq_some_of_mem
#assert_axioms get_eq_some_iff_mem
#assert_axioms rangeOf_ext

/-! ## §2 — the RECEIPT INDEX: `(subject, height, seq) ↦ receipt commitment`, lex-keyed.

The deployed shape: the key is the lexicographic triple (subject `CellId`-felt, block height,
intra-block sequence number) so a subject's receipts at consecutive heights occupy a CONTIGUOUS
key range; the value is the receipt commitment (a felt). The leaf binds all four felts
(`hash[subject, height, seq, commitment]` — the generic-leaf discipline of `Heap.leafOf`), and the
root is the sponge of the sorted leaf list. ONE crypto floor: `Poseidon2SpongeCR`. -/

/-- **`ReceiptKey`** — the lexicographic `(subject, height, seq)` key. `ℤ` felts, as everywhere in
the emit layer. Lex order makes per-subject and per-subject-height queries contiguous ranges. -/
abbrev ReceiptKey : Type := ℤ ×ₗ (ℤ ×ₗ ℤ)

/-- Build a `ReceiptKey` from its three coordinates. -/
def rkey (subject height seq : ℤ) : ReceiptKey := toLex (subject, toLex (height, seq))

namespace ReceiptKey

/-- The subject (the cell whose receipt this is). -/
def subject (k : ReceiptKey) : ℤ := (ofLex k).1
/-- The block height. -/
def height (k : ReceiptKey) : ℤ := (ofLex (ofLex k).2).1
/-- The intra-block sequence number. -/
def seq (k : ReceiptKey) : ℤ := (ofLex (ofLex k).2).2

@[simp] theorem rkey_subject (c h s : ℤ) : (rkey c h s).subject = c := rfl
@[simp] theorem rkey_height (c h s : ℤ) : (rkey c h s).height = h := rfl
@[simp] theorem rkey_seq (c h s : ℤ) : (rkey c h s).seq = s := rfl

/-- A `ReceiptKey` is exactly its three coordinates. -/
theorem ext {k k' : ReceiptKey} (h1 : k.subject = k'.subject)
    (h2 : k.height = k'.height) (h3 : k.seq = k'.seq) : k = k' := by
  have hin : (ofLex k).2 = (ofLex k').2 :=
    ofLex.injective (Prod.ext h2 h3)
  exact ofLex.injective (Prod.ext h1 hin)

/-- The lex order, unfolded onto coordinates: subject-major, then height, then seq. -/
theorem rkey_lt_iff {c h s c' h' s' : ℤ} :
    rkey c h s < rkey c' h' s' ↔
      c < c' ∨ (c = c' ∧ (h < h' ∨ (h = h' ∧ s < s'))) := by
  simp [rkey, Prod.Lex.toLex_lt_toLex]

end ReceiptKey

/-- **`ReceiptIndex`** — the receipt index: a `ReceiptKey`-sorted association list of receipt
commitments (the in-order leaf list of the sorted-Poseidon2 tree, generic-map instantiated). -/
abbrev ReceiptIndex := List (ReceiptKey × ℤ)

/-- **`rleaf`** — the index LEAF: `hash[subject, height, seq, commitment]`. All four felts bound
(tampering any coordinate or the commitment moves the leaf). -/
def rleaf (hash : List ℤ → ℤ) (e : ReceiptKey × ℤ) : ℤ :=
  hash [e.1.subject, e.1.height, e.1.seq, e.2]

/-- **`iroot`** — the committed index root: the sponge of the (sorted) leaf list. The ONE value the
block commitment must absorb for whole-history non-omission (`AttestedQuery` §chain face). -/
def iroot (hash : List ℤ → ℤ) (idx : ReceiptIndex) : ℤ := hash (idx.map (rleaf hash))

/-- **`addReceipt`** — record a receipt: sorted insert-or-update at `(subject, height, seq)`. -/
def addReceipt (idx : ReceiptIndex) (subject height seq commit : ℤ) : ReceiptIndex :=
  set idx (rkey subject height seq) commit

/-- **Insertion preserves the sorted invariant** (`Heap.set_sorted` instantiated — the sorted-insert
gate's obligation at the receipt index). -/
theorem addReceipt_sorted (idx : ReceiptIndex) (c h s v : ℤ) (hs : SortedKeys idx) :
    SortedKeys (addReceipt idx c h s v) :=
  set_sorted idx (rkey c h s) v hs

/-- Read-after-write at the receipt index. -/
theorem addReceipt_get (idx : ReceiptIndex) (c h s v : ℤ) :
    get (addReceipt idx c h s v) (rkey c h s) = some v :=
  get_set_self idx (rkey c h s) v

/-- The leaf is injective under CR: equal leaves force equal entries (peel the 4-felt list, then
rebuild the key from its coordinates). -/
theorem rleaf_injective (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {e e' : ReceiptKey × ℤ} (h : rleaf hash e = rleaf hash e') : e = e' := by
  have hlist := hCR _ _ h
  simp only [List.cons.injEq, and_true] at hlist
  obtain ⟨h1, h2, h3, h4⟩ := hlist
  exact Prod.ext (ReceiptKey.ext h1 h2 h3) h4

/-- The leaf-list map is injective under CR (heads by `rleaf_injective`, tails by induction). -/
theorem map_rleaf_injective (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    ∀ (i₁ i₂ : ReceiptIndex), i₁.map (rleaf hash) = i₂.map (rleaf hash) → i₁ = i₂ := by
  intro i₁
  induction i₁ with
  | nil =>
    intro i₂ h
    cases i₂ with
    | nil => rfl
    | cons hd t => simp at h
  | cons hd₁ t₁ ih =>
    intro i₂ h
    cases i₂ with
    | nil => simp at h
    | cons hd₂ t₂ =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [rleaf_injective hash hCR h.1, ih t₂ h.2]

/-- **`iroot_injective` — the root BINDS the whole index (the anti-ghost).** Two indices with equal
roots are EQUAL, under the single named CR floor. A server cannot keep the published index root
while suppressing, forging, or reordering ANY receipt entry. -/
theorem iroot_injective (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {i₁ i₂ : ReceiptIndex} (h : iroot hash i₁ = iroot hash i₂) : i₁ = i₂ :=
  map_rleaf_injective hash hCR i₁ i₂ (hCR _ _ h)

/-- **`iroot_deterministic`** — the root is a function of the index's MEANING: two sorted indices
with the same lookups share the root (canonicity; NO crypto). -/
theorem iroot_deterministic (hash : List ℤ → ℤ) {i₁ i₂ : ReceiptIndex}
    (hs₁ : SortedKeys i₁) (hs₂ : SortedKeys i₂)
    (hext : ∀ k, get i₁ k = get i₂ k) : iroot hash i₁ = iroot hash i₂ := by
  rw [ext_get hs₁ hs₂ hext]

/-- Equal roots open identically at every key (the per-key consumable form). -/
theorem iroot_binds_get (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {i₁ i₂ : ReceiptIndex} (h : iroot hash i₁ = iroot hash i₂) :
    ∀ k, get i₁ k = get i₂ k := by
  intro k
  rw [iroot_injective hash hCR h]

/-- **`iroot_binds_range` — A RANGE IS FULLY DETERMINED BY THE ROOT.** Under CR, two indices
publishing the same root have the SAME range restriction for EVERY range `[lo, hi]`. This is the
commitment half of query completeness: once the root is fixed, there is exactly one correct answer
to every range query. -/
theorem iroot_binds_range (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {i₁ i₂ : ReceiptIndex} (h : iroot hash i₁ = iroot hash i₂) (lo hi : ReceiptKey) :
    rangeOf i₁ lo hi = rangeOf i₂ lo hi := by
  rw [iroot_injective hash hCR h]

#assert_axioms ReceiptKey.ext
#assert_axioms ReceiptKey.rkey_lt_iff
#assert_axioms addReceipt_sorted
#assert_axioms addReceipt_get
#assert_axioms rleaf_injective
#assert_axioms map_rleaf_injective
#assert_axioms iroot_injective
#assert_axioms iroot_deterministic
#assert_axioms iroot_binds_get
#assert_axioms iroot_binds_range

/-! ## §3 — NON-VACUITY: a concrete receipt index on the computable reference sponge.

Witness TRUE: receipts read back, lex ranges select exactly the in-range receipts, insertion keeps
the spine sorted. Witness FALSE: a tampered receipt commitment MOVES the root; so does suppressing
an entry (the executable shadow of `iroot_injective`). `refSponge` is the same Horner toy sponge
`Heap` §3 uses — computable, NOT real crypto (deployment = p3 Poseidon2 behind the CR floor). -/

/-- A concrete index: subject 1 has receipts at heights 5 and 7; subject 2 at height 1.
Hand-sorted in lex order. -/
def demoIdx : ReceiptIndex :=
  [(rkey 1 5 0, 111), (rkey 1 7 2, 222), (rkey 2 1 0, 333)]

/-- `demoIdx` is key-sorted (the lex order unfolded onto coordinates). -/
theorem demoIdx_sorted : SortedKeys demoIdx := by
  simp only [demoIdx, SortedKeys, keys, List.map_cons, List.map_nil, List.pairwise_cons,
    List.mem_cons, List.not_mem_nil]
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    rcases hk with rfl | rfl | h
    · exact ReceiptKey.rkey_lt_iff.mpr (Or.inr ⟨rfl, Or.inl (by norm_num)⟩)
    · exact ReceiptKey.rkey_lt_iff.mpr (Or.inl (by norm_num))
    · exact absurd h (by simp)
  · intro k hk
    rcases hk with rfl | h
    · exact ReceiptKey.rkey_lt_iff.mpr (Or.inl (by norm_num))
    · exact absurd h (by simp)
  · simp [List.Pairwise.nil]

-- Receipts read back; absent keys read none (the executable lookup face):
#guard get demoIdx (rkey 1 5 0) == some 111
#guard get demoIdx (rkey 1 7 2) == some 222
#guard get demoIdx (rkey 1 6 0) == none
-- The lex range "subject 1, heights 5..7 (any seq < 10)" selects exactly subject 1's receipts:
#guard (rangeOf demoIdx (rkey 1 5 0) (rkey 1 7 10)).map Prod.snd == [111, 222]
-- ...and the full-subject-1 range excludes subject 2:
#guard (rangeOf demoIdx (rkey 1 0 0) (rkey 1 1000 1000)).map Prod.snd == [111, 222]
-- Insertion lands in lex position and preserves reads (sorted-insert face):
#guard get (addReceipt demoIdx 1 6 0 444) (rkey 1 6 0) == some 444
#guard get (addReceipt demoIdx 1 6 0 444) (rkey 1 5 0) == some 111  -- frame
#guard (addReceipt demoIdx 1 6 0 444).length == 4                   -- fresh key grows
#guard (addReceipt demoIdx 1 5 0 999).length == 3                   -- present key updates in place

-- **Witness FALSE (anti-ghost):** tampering ONE receipt commitment MOVES the root...
#guard (iroot refSponge (addReceipt demoIdx 1 5 0 999) != iroot refSponge demoIdx)
-- ...suppressing an entry moves it (omission is visible at the root)...
#guard (iroot refSponge [(rkey 1 5 0, 111), (rkey 2 1 0, 333)] != iroot refSponge demoIdx)
-- ...and so does forging an extra receipt:
#guard (iroot refSponge (addReceipt demoIdx 1 6 0 444) != iroot refSponge demoIdx)

#assert_axioms demoIdx_sorted

end Dregg2.Lightclient.HistoryIndex
