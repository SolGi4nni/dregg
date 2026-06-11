/-
# Dregg2.Lightclient.MMR — the receipt index as an append-only range structure (Merkle Mountain Range).

THE EPOCH's per-structure choice for the receipt index (docs/EPOCH-DESIGN.md): history keys are
DENSE POSITIONS, so the index does not need a sorted map — it needs an append-only structure where
completeness holds BY CONSTRUCTION. This module is the MMR theory that specializes the
`HistoryIndex`/`AttestedQuery` non-omission machinery onto exactly that structure:

  * **the forest** (§2): peaks are PERFECT Poseidon2 trees; `push` is the carry — merge while the
    youngest peak has equal height, else prepend. `peaksOf L = L.foldl appendLeaf []`, so the
    peak update IS the append algorithm (amortized O(1): each append touches one new height-0 peak
    plus carries, and `peaksOf (L ++ [v]) = push (peaksOf L) (.leaf v)` holds by `foldl` — the
    O(1) incremental form is DEFINITIONALLY the recomputation, `peaksOf_append`);
  * **the recovery keystone** `forestLeaves_peaksOf`: the forest's leaves, read oldest-first, are
    EXACTLY the appended log — no entry moves once appended (prefix stability by construction);
  * **the structure theorem** `peaksOf_mountains`: every peak is perfect and heights strictly
    increase from the youngest — the binary decomposition of the log length (so #peaks ≤ log₂ n,
    the succinct frontier the prover carries);
  * **bagging + the root** (§3): `mroot = bag (peaksOf L)`; `mroot_injective` — the root BINDS the
    whole log under the SAME single named CR floor (`Poseidon2SpongeCR`) the cap-root/heap/receipt
    advances carry; nothing else;
  * **positional + range openings** (§4): `Opens`/`mrange`; appends preserve prior openings and
    prior ranges VERBATIM (`append_preserves_opens`, `append_preserves_range`);
  * **POSITIONAL COMPLETENESS** (§5): the range protocol needs NO gap openings — positions are
    dense, so the client checks a COUNT (pinned by the committed length) and per-slot openings;
    `range_complete` proves a verifying answer contains EVERY position in the range (positions
    cannot be skipped), `rverifies_iff_exact` the two-sided characterization, `mroot` faces
    (`server_cannot_omit_position`) pin everything to the genuine log;
  * **the bridge** (§6): `light_client_position_non_omission` restates `AttestedQuery`'s
    per-block face over the MMR index — `CommitBindsMMR` is the `CommitBindsIndex` limb
    obligation VERBATIM with `iroot := mroot`, and composes with
    `RecursiveAggregation.light_client_verifies_whole_history` identically. The obligation list
    SHRINKS on this structure: no sorted invariant (`hsorted` is gone — the log is its own
    canonical order) and no gap-opening machinery (density replaces bracketing).

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. Crypto enters ONLY as
the named `Poseidon2SpongeCR` hypothesis (the one floor) + `EngineSound`'s named fields at the
bridge — hypotheses, never axioms. No `sorry`. Non-vacuity §7: witnesses TRUE (a complete range
answer verifies; the demo forest has the binary-decomposition shape) and FALSE (a skipped position
is rejected; a substituted/reordered value is rejected; tamper/truncate/extend/reorder each MOVE
the root). NEW file; all imports read-only.
-/
import Dregg2.Lightclient.AttestedQuery

namespace Dregg2.Lightclient.MMR

open Dregg2.Substrate.Heap (refSponge)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

/-! ## §1 — perfect peak trees.

An MMR peak is a PERFECT binary Poseidon2 tree over a contiguous chunk of the log. The model keeps
the TREES (the implementation keeps only their hashes; `hashOf` is the projection), so leaf
recovery is a function and root injectivity reduces to hash injectivity structurally. -/

/-- A peak tree: a leaf holds one log entry (a receipt-commitment felt); a node is the Poseidon2
compression of its two children. Perfectness is the separate invariant `Perfect`. -/
inductive PTree : Type where
  | leaf (v : ℤ)
  | node (l r : PTree)
deriving Repr, BEq, DecidableEq

namespace PTree

/-- Peak height: a leaf is 0, a node is one above its LEFT child (merges are equal-height, so the
bias is immaterial on perfect trees). -/
def height : PTree → ℕ
  | .leaf _ => 0
  | .node l _ => l.height + 1

/-- The leaves, left-to-right (oldest-first within the peak's chunk). -/
def leaves : PTree → List ℤ
  | .leaf v => [v]
  | .node l r => l.leaves ++ r.leaves

/-- The perfect-tree invariant: every node joins two perfect trees of EQUAL height. -/
def Perfect : PTree → Prop
  | .leaf _ => True
  | .node l r => l.Perfect ∧ r.Perfect ∧ l.height = r.height

/-- The peak hash — what the implementation stores: `hash [v]` at a leaf, `hash [hl, hr]` at a
node. The 1-vs-2 arity separates leaf from node domains under CR; no extra tag needed. -/
def hashOf (hash : List ℤ → ℤ) : PTree → ℤ
  | .leaf v => hash [v]
  | .node l r => hash [l.hashOf hash, r.hashOf hash]

@[simp] theorem height_leaf (v : ℤ) : (PTree.leaf v).height = 0 := rfl
@[simp] theorem height_node (l r : PTree) : (PTree.node l r).height = l.height + 1 := rfl
@[simp] theorem leaves_leaf (v : ℤ) : (PTree.leaf v).leaves = [v] := rfl
@[simp] theorem leaves_node (l r : PTree) : (PTree.node l r).leaves = l.leaves ++ r.leaves := rfl
@[simp] theorem perfect_leaf (v : ℤ) : (PTree.leaf v).Perfect := trivial
@[simp] theorem hashOf_leaf (hash : List ℤ → ℤ) (v : ℤ) :
    (PTree.leaf v).hashOf hash = hash [v] := rfl
@[simp] theorem hashOf_node (hash : List ℤ → ℤ) (l r : PTree) :
    (PTree.node l r).hashOf hash = hash [l.hashOf hash, r.hashOf hash] := rfl

/-- **The peak hash binds the peak.** Under the one CR floor, equal hashes force equal TREES
(hence equal leaf chunks). Leaf-vs-node collisions die on preimage arity (1 ≠ 2); node-vs-node
recurses. -/
theorem hashOf_injective (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    ∀ t t' : PTree, t.hashOf hash = t'.hashOf hash → t = t' := by
  intro t
  induction t with
  | leaf v =>
    intro t' h
    cases t' with
    | leaf v' =>
      have hl := hCR _ _ h
      simp only [List.cons.injEq, and_true] at hl
      rw [hl]
    | node l' r' => exact absurd (hCR _ _ h) (by simp)
  | node l r ihl ihr =>
    intro t' h
    cases t' with
    | leaf v' => exact absurd (hCR _ _ h) (by simp)
    | node l' r' =>
      have hl := hCR _ _ h
      simp only [List.cons.injEq, and_true] at hl
      rw [ihl l' hl.1, ihr r' hl.2]

/-- A perfect peak of height `h` carries exactly `2 ^ h` leaves (the chunk sizes are the binary
decomposition of the log length). -/
theorem length_leaves : ∀ t : PTree, t.Perfect → t.leaves.length = 2 ^ t.height := by
  intro t
  induction t with
  | leaf v => intro _; simp
  | node l r ihl ihr =>
    intro hp
    obtain ⟨hl, hr, hh⟩ := hp
    simp only [leaves_node, List.length_append, ihl hl, ihr hr, ← hh, height_node, pow_succ]
    omega

end PTree

#assert_axioms PTree.hashOf_injective
#assert_axioms PTree.length_leaves

/-! ## §2 — the forest: `push` (the carry), `peaksOf` (the fold), leaf recovery, the mountains
invariant.

Head = youngest (smallest) peak. `push` merges while heights match — the binary carry; an append
is `push f (.leaf v)`. The forest of a log is the left fold, so the incremental peak update agrees
with recomputation BY DEFINITION (`peaksOf_append` is `foldl` over a concat). -/

/-- The mountain range: peaks, youngest (lowest) first. -/
abbrev Forest := List PTree

/-- **`push`** — the carry: while the youngest peak has the SAME height as the incoming tree,
merge (older peak on the LEFT — its leaves precede); otherwise prepend. Amortized O(1) appends:
each merge retires a peak, each append mints one. -/
def push : Forest → PTree → Forest
  | [], t => [t]
  | s :: rest, t => if t.height = s.height then push rest (.node s t) else t :: s :: rest

@[simp] theorem push_nil (t : PTree) : push [] t = [t] := rfl

theorem push_cons (s : PTree) (rest : Forest) (t : PTree) :
    push (s :: rest) t =
      if t.height = s.height then push rest (.node s t) else t :: s :: rest := rfl

/-- Append one log entry: push a fresh height-0 peak. -/
def appendLeaf (f : Forest) (v : ℤ) : Forest := push f (.leaf v)

/-- **`peaksOf`** — the forest of a log: fold the appends. The implementation maintains this
incrementally; the model recomputes — `peaksOf_append` says the two agree. -/
def peaksOf (L : List ℤ) : Forest := L.foldl appendLeaf []

/-- The forest's leaves, OLDEST-FIRST (tail peaks are older; within a peak, left-to-right). -/
def forestLeaves (f : Forest) : List ℤ := f.foldr (fun t acc => acc ++ t.leaves) []

@[simp] theorem forestLeaves_nil : forestLeaves [] = [] := rfl
@[simp] theorem forestLeaves_cons (t : PTree) (f : Forest) :
    forestLeaves (t :: f) = forestLeaves f ++ t.leaves := rfl

/-- Pushing a tree appends its leaves at the YOUNG end — the leaf order is append order, through
every carry (associativity is the whole proof). -/
theorem forestLeaves_push : ∀ (f : Forest) (t : PTree),
    forestLeaves (push f t) = forestLeaves f ++ t.leaves := by
  intro f
  induction f with
  | nil => intro t; simp
  | cons s rest ih =>
    intro t
    rw [push_cons]
    by_cases h : t.height = s.height
    · rw [if_pos h, ih]
      simp [List.append_assoc]
    · rw [if_neg h]
      rfl

/-- **The O(1) peak update agrees with recomputation** (a `foldl` over a concat — definitional).
This IS "append = peak update": the implementation's incremental push computes `peaksOf`. -/
theorem peaksOf_append (L : List ℤ) (v : ℤ) :
    peaksOf (L ++ [v]) = push (peaksOf L) (.leaf v) := by
  simp [peaksOf, appendLeaf, List.foldl_append]

/-- **THE RECOVERY KEYSTONE (`forestLeaves_peaksOf`).** The forest's oldest-first leaves are
EXACTLY the appended log. Two consequences fall out by construction: the structure is its own
canonical order (no sorted invariant to maintain), and appending never moves a prior position
(prefix stability — §4 consumes it). -/
theorem forestLeaves_peaksOf (L : List ℤ) : forestLeaves (peaksOf L) = L := by
  induction L using List.reverseRecOn with
  | nil => rfl
  | append_singleton L v ih =>
    rw [peaksOf_append, forestLeaves_push, ih, PTree.leaves_leaf]

/-- **`Mountains`** — the range invariant: every peak perfect, heights STRICTLY increasing from
the youngest. (Strict increase = the binary decomposition of the log length: at most one peak per
height, so #peaks ≤ log₂(n)+1 — the succinct frontier.) -/
def Mountains (f : Forest) : Prop :=
  (∀ t ∈ f, t.Perfect) ∧ f.Pairwise (fun a b => a.height < b.height)

/-- The carry preserves the invariant: pushing a perfect tree no taller than every peak yields
mountains again, with every peak still at least the pushed height. -/
theorem push_invariant : ∀ (f : Forest) (t : PTree), Mountains f → t.Perfect →
    (∀ s ∈ f, t.height ≤ s.height) →
    Mountains (push f t) ∧ ∀ s ∈ push f t, t.height ≤ s.height := by
  intro f
  induction f with
  | nil =>
    intro t _ hp _
    simp [Mountains, hp]
  | cons s rest ih =>
    intro t hm hp hle
    obtain ⟨hperf, hpair⟩ := hm
    rw [push_cons]
    by_cases h : t.height = s.height
    · rw [if_pos h]
      have hsp : s.Perfect := hperf s List.mem_cons_self
      have hnp : (PTree.node s t).Perfect := ⟨hsp, hp, h.symm⟩
      have hrest : Mountains rest :=
        ⟨fun u hu => hperf u (List.mem_cons_of_mem _ hu), (List.pairwise_cons.mp hpair).2⟩
      have hle' : ∀ u ∈ rest, (PTree.node s t).height ≤ u.height := by
        intro u hu
        simpa using (List.pairwise_cons.mp hpair).1 u hu
      obtain ⟨hm', hge'⟩ := ih (PTree.node s t) hrest hnp hle'
      refine ⟨hm', fun u hu => le_trans ?_ (hge' u hu)⟩
      simp [h]
    · rw [if_neg h]
      have hts : t.height < s.height := lt_of_le_of_ne (hle s List.mem_cons_self) h
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hp
        · exact hperf u hu
      · rw [List.pairwise_cons]
        refine ⟨fun u hu => ?_, hpair⟩
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hts
        · exact hts.trans ((List.pairwise_cons.mp hpair).1 u hu)
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact le_refl _
        · exact hle u hu

/-- **The structure theorem.** Every log's forest is mountains: perfect peaks, strictly
increasing heights — the binary-decomposition shape, for free, forever (the invariant is
maintained by the only mutation the structure has). -/
theorem peaksOf_mountains (L : List ℤ) : Mountains (peaksOf L) := by
  induction L using List.reverseRecOn with
  | nil => simp [peaksOf, Mountains]
  | append_singleton L v ih =>
    rw [peaksOf_append]
    exact (push_invariant (peaksOf L) (.leaf v) ih trivial (fun s _ => Nat.zero_le _)).1

#assert_axioms forestLeaves_push
#assert_axioms peaksOf_append
#assert_axioms forestLeaves_peaksOf
#assert_axioms push_invariant
#assert_axioms peaksOf_mountains

/-! ## §3 — bagging and THE ROOT.

`bag` folds the peaks into ONE felt (right-assoc: `hash [peakHash, bagOfRest]`, empty = `hash []`
— arities 0/2/1 keep the three hash domains apart under CR with no tags). `mroot` is the committed
value; `mroot_injective` is the root_injective transfer onto the MMR. -/

/-- **`bag`** — the single root over the peaks: `hash []` for the empty range, else
`hash [peak, bag rest]` youngest-outward. -/
def bag (hash : List ℤ → ℤ) : Forest → ℤ
  | [] => hash []
  | t :: rest => hash [t.hashOf hash, bag hash rest]

@[simp] theorem bag_nil (hash : List ℤ → ℤ) : bag hash [] = hash [] := rfl
@[simp] theorem bag_cons (hash : List ℤ → ℤ) (t : PTree) (f : Forest) :
    bag hash (t :: f) = hash [t.hashOf hash, bag hash f] := rfl

/-- **`mroot`** — the committed MMR root of a receipt log: bag the forest. THE value the per-turn
commitment absorbs (§6) — `iroot` for the append-only index. -/
def mroot (hash : List ℤ → ℤ) (L : List ℤ) : ℤ := bag hash (peaksOf L)

/-- The bag binds the forest: equal bags force equal peak lists (arity separates empty from cons;
`hashOf_injective` pins each peak; induction pins the rest). -/
theorem bag_injective (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    ∀ f₁ f₂ : Forest, bag hash f₁ = bag hash f₂ → f₁ = f₂ := by
  intro f₁
  induction f₁ with
  | nil =>
    intro f₂ h
    cases f₂ with
    | nil => rfl
    | cons t rest => exact absurd (hCR _ _ h) (by simp)
  | cons t rest ih =>
    intro f₂ h
    cases f₂ with
    | nil => exact absurd (hCR _ _ h) (by simp)
    | cons t' rest' =>
      have hl := hCR _ _ h
      simp only [List.cons.injEq, and_true] at hl
      rw [PTree.hashOf_injective hash hCR t t' hl.1, ih rest' hl.2]

/-- **`mroot_injective` — THE ROOT BINDS THE WHOLE LOG (the anti-ghost, transferred).** Two logs
with equal roots are EQUAL, under the single named CR floor: a server cannot keep the published
root while suppressing, forging, REORDERING, or truncating ANY receipt position. The proof is the
recovery keystone riding bag injectivity — the sorted-map `iroot_injective`, specialized to the
structure where canonical order is free. -/
theorem mroot_injective (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {L₁ L₂ : List ℤ} (h : mroot hash L₁ = mroot hash L₂) : L₁ = L₂ := by
  have hf := bag_injective hash hCR _ _ h
  calc L₁ = forestLeaves (peaksOf L₁) := (forestLeaves_peaksOf L₁).symm
    _ = forestLeaves (peaksOf L₂) := by rw [hf]
    _ = L₂ := forestLeaves_peaksOf L₂

#assert_axioms bag_injective
#assert_axioms mroot_injective

/-! ## §4 — positional and range openings; appends preserve them.

A positional opening certifies "position `i` holds `v`"; a range opening is the contiguous slice
`mrange`. Because the structure only ever APPENDS, every prior opening and every prior range stays
true VERBATIM after any number of later appends — prefix stability by construction, the property
the sorted map had to re-prove per insert. -/

/-- **`Opens L i v`** — the positional opening's semantic content: position `i` of the log holds
`v`. (At the wire: the Merkle path through the covering peak + the peak's bag position; at the
model the log is pinned by `mroot_injective`.) -/
def Opens (L : List ℤ) (i : ℕ) (v : ℤ) : Prop := L[i]? = some v

instance (L : List ℤ) (i : ℕ) (v : ℤ) : Decidable (Opens L i v) := by
  unfold Opens; infer_instance

/-- **`mrange L lo hi`** — the EXACT range answer: positions `[lo, hi]` of the log, clipped to the
committed length. THE complete answer a range query must equal. -/
def mrange (L : List ℤ) (lo hi : ℕ) : List ℤ := (L.take (hi + 1)).drop lo

/-- The committed in-range position count: `|[lo, hi] ∩ [0, len)|`. Computable from the committed
length alone — the client-side count check of §5. -/
def rangeCount (len lo hi : ℕ) : ℕ := min (hi + 1) len - lo

@[simp] theorem mrange_length (L : List ℤ) (lo hi : ℕ) :
    (mrange L lo hi).length = rangeCount L.length lo hi := by
  simp [mrange, rangeCount]

/-- The range answer reads the log at dense offsets: slot `j` is position `lo + j`. -/
theorem mrange_getElem? (L : List ℤ) (lo hi j : ℕ) (hj : j < rangeCount L.length lo hi) :
    (mrange L lo hi)[j]? = L[lo + j]? := by
  have h1 : lo + j < hi + 1 := by unfold rangeCount at hj; omega
  simp [mrange, List.getElem?_drop, h1]

/-- Equal roots open identically at every position (the per-position consumable form). -/
theorem mroot_binds_position (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {L L' : List ℤ} (h : mroot hash L' = mroot hash L) (i : ℕ) : L'[i]? = L[i]? := by
  rw [mroot_injective hash hCR h]

/-- **A range is fully determined by the root**: once the root is fixed there is exactly one
correct answer to every positional range query (`iroot_binds_range`, transferred). -/
theorem mroot_binds_range (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {L L' : List ℤ} (h : mroot hash L' = mroot hash L) (lo hi : ℕ) :
    mrange L' lo hi = mrange L lo hi := by
  rw [mroot_injective hash hCR h]

/-- **Appends preserve prior positions** — any suffix of later appends leaves every committed
position untouched (prefix stability, by construction). -/
theorem append_preserves_get (L M : List ℤ) {i : ℕ} (hi : i < L.length) :
    (L ++ M)[i]? = L[i]? :=
  List.getElem?_append_left hi

/-- **Appends preserve prior OPENINGS**: an opening made against the old log is verbatim true of
the appended log. (The sorted map re-sorts on insert; the MMR never moves a leaf.) -/
theorem append_preserves_opens {L : List ℤ} {i : ℕ} {v : ℤ} (h : Opens L i v) (M : List ℤ) :
    Opens (L ++ M) i v := by
  have hi : i < L.length := by
    by_contra hn
    rw [Opens, List.getElem?_eq_none (Nat.le_of_not_lt hn)] at h
    simp at h
  rw [Opens, append_preserves_get L M hi]
  exact h

/-- **Appends preserve prior RANGES**: a range answer whose upper end is already committed is
verbatim the same after any number of later appends. -/
theorem append_preserves_range (L M : List ℤ) {lo hi : ℕ} (hhi : hi < L.length) :
    mrange (L ++ M) lo hi = mrange L lo hi := by
  unfold mrange
  rw [List.take_append_of_le_length (by omega)]

#assert_axioms mrange_getElem?
#assert_axioms mroot_binds_position
#assert_axioms mroot_binds_range
#assert_axioms append_preserves_get
#assert_axioms append_preserves_opens
#assert_axioms append_preserves_range

/-! ## §5 — the range protocol + POSITIONAL COMPLETENESS (non-omission WITHOUT gap openings).

The sorted map needed gap openings (bracketing absent KEYS); positions are DENSE, so absence needs
no witness at all. The client checks (1) the answer's COUNT equals the committed clip — `rangeCount`
from the committed length, which the root pins — and (2) each value opens at its dense slot
`lo + j`. A position cannot be skipped: skipping shifts every later slot and breaks the count. -/

/-- **`RVerifies L lo hi vals`** — the client-side acceptance for a positional range answer:
the count matches the committed clip, and slot `j` opens position `lo + j`. NO gap openings. -/
def RVerifies (L : List ℤ) (lo hi : ℕ) (vals : List ℤ) : Prop :=
  vals.length = rangeCount L.length lo hi
  ∧ ∀ j v, vals[j]? = some v → Opens L (lo + j) v

/-- **SOUNDNESS (`range_sound`).** Every answered value genuinely opens at its claimed position. -/
theorem range_sound {L : List ℤ} {lo hi : ℕ} {vals : List ℤ}
    (hv : RVerifies L lo hi vals) :
    ∀ j v, vals[j]? = some v → Opens L (lo + j) v := hv.2

/-- **THE KEYSTONE — POSITIONAL COMPLETENESS (`range_complete`): positions cannot be skipped.**
A verifying answer contains EVERY committed position in the queried range, each at its dense slot
`i - lo`, agreeing with the log. Non-omission with no gap openings: density + the count are the
whole argument. -/
theorem range_complete {L : List ℤ} {lo hi : ℕ} {vals : List ℤ}
    (hv : RVerifies L lo hi vals) :
    ∀ i, lo ≤ i → i ≤ hi → i < L.length →
      ∃ v, vals[i - lo]? = some v ∧ Opens L i v := by
  intro i hlo hhi hlen
  have hj : i - lo < vals.length := by
    rw [hv.1]; unfold rangeCount; omega
  have hval : vals[i - lo]? = some vals[i - lo] := List.getElem?_eq_getElem hj
  have hopen := hv.2 (i - lo) _ hval
  rw [Nat.add_sub_cancel' hlo] at hopen
  exact ⟨_, hval, hopen⟩

/-- **The two-sided characterization (`rverifies_iff_exact`).** An answer verifies IFF it is
EXACTLY `mrange L lo hi` — the unique correct answer: nothing skipped, nothing forged, dense
order. (The backward direction is honest-prover totality: the exact answer ALWAYS verifies, so
completeness is achievable, not vacuous.) -/
theorem rverifies_iff_exact {L : List ℤ} {lo hi : ℕ} {vals : List ℤ} :
    RVerifies L lo hi vals ↔ vals = mrange L lo hi := by
  constructor
  · intro hv
    apply List.ext_getElem?
    intro j
    by_cases hj : j < vals.length
    · have hval : vals[j]? = some vals[j] := List.getElem?_eq_getElem hj
      rw [hval, mrange_getElem? L lo hi j (hv.1 ▸ hj)]
      exact (hv.2 j _ hval).symm
    · rw [List.getElem?_eq_none (Nat.le_of_not_lt hj),
        List.getElem?_eq_none (by rw [mrange_length, ← hv.1]; omega)]
  · rintro rfl
    refine ⟨mrange_length L lo hi, fun j v hval => ?_⟩
    have hj : j < (mrange L lo hi).length := by
      by_contra hn
      rw [List.getElem?_eq_none (Nat.le_of_not_lt hn)] at hval
      simp at hval
    show L[lo + j]? = some v
    rw [← mrange_getElem? L lo hi j (by rwa [mrange_length] at hj)]
    exact hval

/-- **Honest-prover totality.** The exact answer always verifies — every positional range query on
every log is answerable, completely, with no auxiliary witnesses. -/
theorem exact_range_verifies (L : List ℤ) (lo hi : ℕ) :
    RVerifies L lo hi (mrange L lo hi) :=
  rverifies_iff_exact.mpr rfl

/-- A `RVerifies` run against ANY log recomposing the published root is a run against THE log
(CR pins the leaves). -/
theorem mroot_pins_rverifies (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {L L' : List ℤ} (hroot : mroot hash L' = mroot hash L)
    {lo hi : ℕ} {vals : List ℤ}
    (hv : RVerifies L' lo hi vals) : RVerifies L lo hi vals := by
  rwa [mroot_injective hash hCR hroot] at hv

/-- **`server_cannot_omit_position` — THE ROOT-FACE HEADLINE.** A client holding ONLY the committed
`mroot`: a verifying answer against ANY log recomposing that root IS the unique exact range of the
genuine log — every committed in-range position present at its dense slot (omission impossible),
every value genuine (forgery impossible). One named CR floor; no sorted invariant, no gaps. -/
theorem server_cannot_omit_position (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {L L' : List ℤ} (hroot : mroot hash L' = mroot hash L)
    {lo hi : ℕ} {vals : List ℤ}
    (hv : RVerifies L' lo hi vals) :
    vals = mrange L lo hi
    ∧ ∀ i, lo ≤ i → i ≤ hi → i < L.length →
        ∃ v, vals[i - lo]? = some v ∧ Opens L i v := by
  have hv' := mroot_pins_rverifies hash hCR hroot hv
  exact ⟨rverifies_iff_exact.mp hv', range_complete hv'⟩

#assert_axioms range_sound
#assert_axioms range_complete
#assert_axioms rverifies_iff_exact
#assert_axioms exact_range_verifies
#assert_axioms mroot_pins_rverifies
#assert_axioms server_cannot_omit_position

/-! ## §6 — the CHAIN face: `AttestedQuery`'s per-block obligation, restated over the MMR.

`CommitBindsMMR` is `CommitBindsIndex` VERBATIM with `iroot := mroot` — the per-turn state
commitment absorbs the receipt-index root as its LAST sponge limb (the EPOCH commitment layout
places the receipt-index root last, exactly so this discharges by construction). The composition
with `RecursiveAggregation` is identical; the obligation list SHRINKS: `hsorted` is GONE (the
append-only log is its own canonical order) and the answer carries no gap openings. -/

/-- **`CommitBindsMMR` — the rotation obligation, carried over verbatim.** The per-turn commitment
is a sponge absorbing the MMR root as a limb (`limbs` = the other absorbed fields — cells root,
registers, map roots). The EPOCH layout (receipt-index root LAST) discharges this by construction
at the flag-day. -/
def CommitBindsMMR (hash : List ℤ → ℤ) (limbs : List ℤ) (commit : ℤ)
    (L : List ℤ) : Prop :=
  commit = hash (limbs ++ [mroot hash L])

/-- A commitment binding an MMR root pins the log: two openings of the SAME commitment expose the
SAME receipt log (CR peels the sponge, the root limb is last regardless of the other limbs' shape,
`mroot_injective` pins the leaves — `commit_pins_index`, transferred). -/
theorem commit_pins_mmr (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {limbs limbs' : List ℤ} {c : ℤ} {L L' : List ℤ}
    (hb : CommitBindsMMR hash limbs c L)
    (hb' : CommitBindsMMR hash limbs' c L') : L' = L := by
  have hl : limbs ++ [mroot hash L] = limbs' ++ [mroot hash L'] :=
    hCR _ _ (hb.symm.trans hb')
  have h1 : (limbs ++ [mroot hash L]).getLast? = some (mroot hash L) :=
    List.getLast?_concat
  have h2 : (limbs' ++ [mroot hash L']).getLast? = some (mroot hash L') :=
    List.getLast?_concat
  rw [hl, h2] at h1
  exact mroot_injective hash hCR (Option.some.inj h1)

open Dregg2.Circuit.RecursiveAggregation
open Dregg2.Distributed.HistoryAggregation (ChainStep)
open Dregg2.Exec (RecChainedState)

/-- **`light_client_position_non_omission` — non-omission over the WHOLE history, on the MMR
index.** The per-block face of `AttestedQuery.light_client_query_non_omission`, restated: a light
client holding ONLY the aggregation root, given

  * a sound recursion engine (`EngineSound`) and `verify agg.root = true` (the ONE client check),
  * the weld — every step's folded state commitment absorbs its receipt log's MMR root
    (`CommitBindsMMR`, the `CommitBindsIndex` limb obligation verbatim, `iroot := mroot`),

concludes, for ANY step, ANY server-supplied opening of that step's attested commitment, and ANY
verifying positional range answer: the whole chain is attested (`AggregateAttests`), the answer is
EXACTLY the genuine range, and every committed in-range position is present at its dense slot.
Versus the sorted-map face, TWO obligations vanish: no per-index sorted invariant (`hsorted` is
gone — append-only is canonically ordered) and no gap openings (density replaces bracketing). The
server cannot skip a position anywhere in history. -/
theorem light_client_position_non_omission
    (Proof : Type) (verify : Proof → Bool)
    (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
    (RH : Dregg2.Exec.RecordKernelState → ℤ)
    (cmb : ℤ → ℤ → ℤ) (compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
    (hroot : verify agg.root = true)
    -- the per-turn receipt log and THE WELD (the rotation obligation, per step):
    (logOf : ChainStep → List ℤ) (limbsOf : ChainStep → List ℤ)
    (hweld : ∀ s ∈ steps, CommitBindsMMR hash (limbsOf s)
      (ChainStep.newRoot CH RH cmb compress compressN s) (logOf s))
    -- the queried step + the server's opening of its ATTESTED commitment + a verifying answer:
    {s : ChainStep} (hstep : s ∈ steps)
    {L' : List ℤ} {limbs' : List ℤ}
    (hopen : CommitBindsMMR hash limbs'
      (ChainStep.newRoot CH RH cmb compress compressN s) L')
    {lo hi : ℕ} {vals : List ℤ}
    (hv : RVerifies L' lo hi vals) :
    AggregateAttests Proof CH RH cmb compress compressN agg g steps
      ∧ vals = mrange (logOf s) lo hi
      ∧ (∀ i, lo ≤ i → i ≤ hi → i < (logOf s).length →
          ∃ v, vals[i - lo]? = some v ∧ Opens (logOf s) i v) := by
  have hpin : L' = logOf s := commit_pins_mmr hash hCR (hweld s hstep) hopen
  rw [hpin] at hv
  exact ⟨light_client_verifies_whole_history Proof verify CH RH cmb compress compressN
      agg g steps es hroot,
    rverifies_iff_exact.mp hv, range_complete hv⟩

#assert_axioms commit_pins_mmr
#assert_axioms light_client_position_non_omission

/-! ## §7 — NON-VACUITY: witnesses TRUE and FALSE on a concrete log.

Log `[111, 222, 333]` (receipt commitments at positions 0, 1, 2), query range `[1, 2]`, on the
computable Horner toy sponge `refSponge` (`Heap` §3 — NOT real crypto; deployment = p3 Poseidon2
behind the CR floor):

  * TRUE — the forest has the binary-decomposition shape (peaks heights `[0, 1]`; appending a 4th
    leaf carries to ONE height-2 peak); the leaves read back; the exact answer `[222, 333]`
    VERIFIES; appends preserve prior ranges (executable prefix stability);
  * FALSE — a SKIPPED position is rejected (`demo_skipped_rejected` — derived from THE keystone);
    a SUBSTITUTED value and a REORDERED answer are rejected (the dense slot pins each value);
    tamper / truncate / extend / reorder each MOVE the root (the executable shadow of
    `mroot_injective` — note REORDER is detected, which the sorted map could not even express). -/

/-- The demo receipt log: positions 0, 1, 2. -/
def demoLog : List ℤ := [111, 222, 333]

-- The forest is the binary decomposition of 3 = 2 + 1: peak heights [0, 1], youngest first...
#guard (peaksOf demoLog).map PTree.height == [0, 1]
-- ...the leaves read back oldest-first (the recovery keystone, executable)...
#guard forestLeaves (peaksOf demoLog) == demoLog
-- ...and the 4th append CARRIES: 4 = 2² gives ONE peak of height 2 (amortized O(1) shape).
#guard (peaksOf (demoLog ++ [444])).map PTree.height == [2]

-- Positional + range openings compute:
#guard demoLog[1]? == some 222
#guard mrange demoLog 1 2 == [222, 333]
#guard mrange demoLog 0 10 == demoLog               -- clipping at the committed length
#guard rangeCount demoLog.length 1 2 == 2
-- Prefix stability, executable: a later append leaves the prior range VERBATIM.
#guard mrange (demoLog ++ [444]) 1 2 == mrange demoLog 1 2
-- Determinism sanity: same log, same root.
#guard mroot refSponge [111, 222, 333] == mroot refSponge demoLog

-- **Witness FALSE at the root (anti-ghost):** tampering ONE position MOVES the root...
#guard mroot refSponge [111, 999, 333] != mroot refSponge demoLog
-- ...truncating the log moves it (omission is visible at the root)...
#guard mroot refSponge [111, 222] != mroot refSponge demoLog
-- ...forging an extra receipt moves it...
#guard mroot refSponge (demoLog ++ [444]) != mroot refSponge demoLog
-- ...and so does REORDERING (position is part of the commitment — the append-only tooth):
#guard mroot refSponge [222, 111, 333] != mroot refSponge demoLog

/-- The demo forest is mountains (perfect peaks, strictly increasing heights) — the structure
theorem, instantiated. -/
theorem demo_mountains : Mountains (peaksOf demoLog) := peaksOf_mountains demoLog

/-- **Witness TRUE** — the exact answer to range `[1, 2]` VERIFIES. -/
theorem demo_range_verifies : RVerifies demoLog 1 2 [222, 333] :=
  rverifies_iff_exact.mpr (by decide)

/-- **Witness FALSE #1 — a skipped position is REJECTED.** The server drops position 1 and slides
333 into its slot: position 2 then has NO slot (the count breaks). Derived from THE keystone:
a verifying answer would have to carry position 2 at slot 1. -/
theorem demo_skipped_rejected : ¬ RVerifies demoLog 1 2 [333] := by
  intro hv
  obtain ⟨v, hslot, _⟩ := range_complete hv 2 (by norm_num) (by norm_num)
    (by norm_num [demoLog])
  simp at hslot

/-- **Witness FALSE #2 — a substituted value is REJECTED.** Right count, wrong value at slot 0:
the dense opening pins slot 0 to position 1, which holds 222, not 333. -/
theorem demo_substituted_rejected : ¬ RVerifies demoLog 1 2 [333, 333] := by
  intro hv
  exact absurd (hv.2 0 333 (by decide)) (by decide)

/-- **Witness FALSE #3 — a reordered answer is REJECTED** (positions cannot be permuted: each slot
opens its own position). -/
theorem demo_reordered_rejected : ¬ RVerifies demoLog 1 2 [333, 222] := by
  intro hv
  exact absurd (hv.2 0 333 (by decide)) (by decide)

#assert_axioms demo_mountains
#assert_axioms demo_range_verifies
#assert_axioms demo_skipped_rejected
#assert_axioms demo_substituted_rejected
#assert_axioms demo_reordered_rejected

end Dregg2.Lightclient.MMR
