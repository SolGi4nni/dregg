/-
# Dregg2.Lightclient.AttestedQuery — provable COMPLETENESS of query answers (non-omission).

THE NON-OMISSION FOUNDATION, part 2 of 2 (the protocol on `HistoryIndex`). Membership openings make
a query answer SOUND ("every receipt shown is real"); GAP openings — the proven sorted-tree
bracketing of `Crypto.NonMembership.sorted_gap_excludes` — make it COMPLETE ("and there are NO
others in the range"). This module defines the query/answer surface and proves THE THEOREM:

    **a verifying answer cannot omit a key** (`answer_complete` / `server_cannot_omit`):
    any omitted in-range key would have to fall inside some claimed gap, and a VALID gap
    opening excludes everything strictly inside it — contradiction.

The full inventory:
  * `Gap` — the four gap-witness shapes (`inner` adjacent-pair bracketing = the cap/nullifier
    non-membership opening, plus the `below`-minimum / `above`-maximum boundary forms and the
    `empty`-index form) with `Gap.excludes`: a valid gap covering `k` proves `k` absent;
  * `Answer` + `Verifies` — an answer is (membership openings, gap openings); it verifies iff every
    item opens in-range against the index, every gap opening is valid, and the gaps cover every
    in-range key the items don't claim;
  * SOUNDNESS `answer_sound`, COMPLETENESS `answer_complete` (THE THEOREM), and the two-sided
    characterization `verifies_iff_exact`: an answer (with sorted item spine) verifies for SOME
    gaps iff its items are EXACTLY `rangeOf h lo hi` — the unique correct answer;
  * the honest prover is total: `exactAnswer` (range restriction + the canonical gap list
    `gapsOf`) always verifies (`exact_answer_verifies`) — completeness is ACHIEVABLE, not vacuous;
  * the ROOT face: against a committed `iroot`, the CR floor pins the whole protocol to the genuine
    index (`server_cannot_omit`);
  * the CHAIN face: `CommitBindsIndex` names EXACTLY the rotation obligation — the per-turn state
    commitment must absorb `iroot` as a sponge limb — and `light_client_query_non_omission`
    composes it with `RecursiveAggregation.light_client_verifies_whole_history`: a light client
    holding ONLY the aggregation root gets non-omission over the WHOLE history.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem; crypto enters only as
the named `Poseidon2SpongeCR` hypothesis + `RecursiveAggregation.EngineSound`'s named fields (both
hypotheses, never axioms). No `sorry`. Non-vacuity witnessed TRUE (a complete answer verifies) and
FALSE (a dropped receipt is rejected; a forged gap is invalid; a forged extra receipt is rejected).
NEW file; all imports read-only.
-/
import Dregg2.Lightclient.HistoryIndex
import Dregg2.Circuit.RecursiveAggregation

namespace Dregg2.Lightclient.AttestedQuery

open Dregg2.Substrate.Heap
open Dregg2.Crypto.NonMembership (Sorted Adjacent sorted_gap_excludes)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Lightclient.HistoryIndex

universe u v

variable {κ : Type u} {ν : Type v} [LinearOrder κ]

/-! ## §1 — gap witnesses: the four non-membership opening shapes over a sorted key spine.

`inner a b` is the proven cap/nullifier bracketing (`Adjacent` + strictly-between ⇒ absent,
`sorted_gap_excludes`). The boundary forms close the range protocol without sentinel keys:
`below b` (nothing precedes the minimum), `above a` (nothing follows the maximum), `empty`
(nothing at all). Each `Valid` form is exactly what a Merkle opening against the sorted tree
certifies: head/last/adjacency positions of PRESENT leaves. -/

/-- A gap opening: a claim that a whole key interval is absent from the index, witnessed by the
position of PRESENT neighbor leaves (or by emptiness). -/
inductive Gap (κ : Type u) where
  /-- The index is empty (everything is absent). -/
  | empty : Gap κ
  /-- `b` is the FIRST (minimum) key: everything below `b` is absent. -/
  | below (b : κ) : Gap κ
  /-- `a`, `b` are ADJACENT present keys: everything strictly between is absent — the
  `sorted_gap_excludes` bracketing. -/
  | inner (a b : κ) : Gap κ
  /-- `a` is the LAST (maximum) key: everything above `a` is absent. -/
  | above (a : κ) : Gap κ
  deriving Repr, BEq, DecidableEq

namespace Gap

/-- **`Valid l g`** — the gap opening verifies against the (committed) sorted key spine `l`: the
claimed neighbors really occupy the claimed positions. (At the wire this is the Merkle opening of
the neighbor leaves; at the model the spine is pinned by the root, `iroot_injective`.) -/
def Valid (l : List κ) : Gap κ → Prop
  | .empty => l = []
  | .below b => l.head? = some b
  | .inner a b => Adjacent l a b
  | .above a => l.getLast? = some a

/-- **`covers k g`** — the queried key `k` lies strictly inside the gap's claimed-absent interval. -/
def covers (k : κ) : Gap κ → Prop
  | .empty => True
  | .below b => k < b
  | .inner a b => a < k ∧ k < b
  | .above a => a < k

/-- **`Gap.excludes` — a valid gap covering `k` proves `k` ABSENT.** The `inner` case is LITERALLY
`sorted_gap_excludes` (the proven non-membership heart); the boundary cases ride the same strict
`Pairwise` order. This is the tooth that makes omission impossible: an omitted present key cannot
be covered by any valid gap. -/
theorem excludes {l : List κ} {g : Gap κ} {k : κ}
    (hs : Sorted l) (hv : g.Valid l) (hc : g.covers k) : k ∉ l := by
  cases g with
  | empty =>
    subst hv; simp
  | below b =>
    cases l with
    | nil => simp
    | cons x t =>
      have hx : x = b := by simpa [Valid] using hv
      subst hx
      intro hmem
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact absurd hc (lt_irrefl _)
      · exact absurd ((Dregg2.Crypto.NonMembership.head_lt_of_sorted hs k htail).trans hc)
          (lt_irrefl _)
  | inner a b =>
    exact sorted_gap_excludes l a b k hs hv hc.1 hc.2
  | above a =>
    obtain ⟨pre, rfl⟩ := List.getLast?_eq_some_iff.mp hv
    intro hmem
    rcases List.mem_append.mp hmem with hpre | hlast
    · have hlt : k < a := (List.pairwise_append.mp hs).2.2 k hpre a (by simp)
      exact absurd (hlt.trans hc) (lt_irrefl _)
    · rw [List.mem_singleton.mp hlast] at hc
      exact absurd hc (lt_irrefl _)

end Gap

/-! ## §2 — the query/answer protocol + THE THEOREM.

A query is a key range `[lo, hi]`. An answer is a list of membership openings (the claimed
receipts) and a list of gap openings (the claimed absences). `Verifies` is what the client checks
— every check is against the spine the committed root pins. -/

/-- A query answer: the claimed in-range entries (each backed by a membership opening) and the gap
openings covering the claimed-absent remainder of the range. -/
structure Answer (κ : Type u) (ν : Type v) where
  /-- The claimed entries, with their values (membership openings). -/
  items : List (κ × ν)
  /-- The gap openings (non-membership witnesses for the rest of the range). -/
  gaps : List (Gap κ)

/-- **`Verifies h lo hi ans`** — the client-side acceptance condition:
  (1) every claimed item is in-range and OPENS against the index (`get h k = some v`);
  (2) every claimed gap opening is VALID against the index's key spine;
  (3) the gaps COVER every in-range key the items don't claim (the complement of the answered
      keys within the range — checked structurally as interval tiling at the wire). -/
def Verifies (h : List (κ × ν)) (lo hi : κ) (ans : Answer κ ν) : Prop :=
  (∀ e ∈ ans.items, inRange lo hi e.1 ∧ get h e.1 = some e.2)
  ∧ (∀ g ∈ ans.gaps, g.Valid (keys h))
  ∧ (∀ k, inRange lo hi k → k ∉ keys ans.items → ∃ g ∈ ans.gaps, g.covers k)

/-- **`AnswerComplete`** — the completeness property an answer must have: it contains EVERY key in
the range that is present in the index. (What `answer_complete` proves of every verifying answer.) -/
def AnswerComplete (h : List (κ × ν)) (lo hi : κ) (ans : Answer κ ν) : Prop :=
  ∀ k ∈ keys h, inRange lo hi k → k ∈ keys ans.items

/-- **SOUNDNESS (`answer_sound`).** Every answered item is genuinely in the index, in range. (The
membership-opening direction — no sortedness needed.) -/
theorem answer_sound {h : List (κ × ν)} {lo hi : κ} {ans : Answer κ ν}
    (hv : Verifies h lo hi ans) :
    ∀ e ∈ ans.items, e ∈ h ∧ inRange lo hi e.1 :=
  fun e he => ⟨mem_of_get_eq_some (hv.1 e he).2, (hv.1 e he).1⟩

/-- **THE THEOREM — COMPLETENESS (`answer_complete`): omission is impossible.** A verifying answer
contains EVERY in-range key present in the index: an omitted key would (by coverage) fall inside
some claimed gap, and `Gap.excludes` — the same CR-pinned bracketing the heap carries — proves a
valid gap contains NO present key. The server cannot hide a receipt from you. -/
theorem answer_complete {h : List (κ × ν)} {lo hi : κ} {ans : Answer κ ν}
    (hs : SortedKeys h) (hv : Verifies h lo hi ans) :
    AnswerComplete h lo hi ans := by
  intro k hk hr
  by_contra hmiss
  obtain ⟨g, hg, hcov⟩ := hv.2.2 k hr hmiss
  exact Gap.excludes hs (hv.2.1 g hg) hcov hk

/-- **Exactness (`verifies_items_eq_range`).** A verifying answer with a sorted item spine answers
EXACTLY the range restriction — not one receipt fewer (completeness), not one more (soundness),
in canonical order (`ext_get`). -/
theorem verifies_items_eq_range {h : List (κ × ν)} {lo hi : κ} {ans : Answer κ ν}
    (hs : SortedKeys h) (hsi : SortedKeys ans.items)
    (hv : Verifies h lo hi ans) : ans.items = rangeOf h lo hi := by
  apply ext_get hsi (rangeOf_sorted h lo hi hs)
  intro k
  cases hgi : get ans.items k with
  | some v =>
    have hmem : (k, v) ∈ ans.items := mem_of_get_eq_some hgi
    obtain ⟨hr, hgv⟩ := hv.1 (k, v) hmem
    exact (get_eq_some_of_mem (rangeOf_sorted h lo hi hs)
      (mem_rangeOf.mpr ⟨mem_of_get_eq_some hgv, hr⟩)).symm
  | none =>
    symm
    rw [get_eq_none_iff]
    intro hkr
    obtain ⟨v, hvr⟩ := mem_keys_iff.mp hkr
    obtain ⟨hmem_h, hr⟩ := mem_rangeOf.mp hvr
    have hnk : k ∉ keys ans.items := (get_eq_none_iff _ _).mp hgi
    obtain ⟨g, hg, hcov⟩ := hv.2.2 k hr hnk
    exact Gap.excludes hs (hv.2.1 g hg) hcov (mem_keys_iff.mpr ⟨v, hmem_h⟩)

#assert_axioms Gap.excludes
#assert_axioms answer_sound
#assert_axioms answer_complete
#assert_axioms verifies_items_eq_range

/-! ## §3 — the honest prover is TOTAL: the canonical gap list + `exact_answer_verifies`.

Completeness would be hollow if no answer could ever verify. `gapsOf` is the canonical gap list of
a sorted spine (below-the-head, every adjacent pair, above-the-last); `gapsOf_covers` proves every
ABSENT key is covered by one of them — the bracket-EXISTENCE half the non-membership AIR's
completeness (`nonmembership_complete`) takes as a hypothesis, here PROVED. -/

/-- The adjacent-pair gaps of a spine: one `inner` gap per consecutive pair. -/
def innerGaps : List κ → List (Gap κ)
  | a :: b :: t => .inner a b :: innerGaps (b :: t)
  | _ => []

/-- The canonical gap list: `empty` for the empty spine; otherwise below-the-head, above-the-last,
and every adjacent pair. Covers the whole complement of the spine (`gapsOf_covers`). -/
def gapsOf : List κ → List (Gap κ)
  | [] => [.empty]
  | a :: t => .below a :: .above ((a :: t).getLast (List.cons_ne_nil a t)) :: innerGaps (a :: t)

omit [LinearOrder κ] in
/-- Every member of `innerGaps l` is an `inner` gap over an ADJACENT pair of `l`. -/
theorem mem_innerGaps : ∀ {l : List κ} {g : Gap κ}, g ∈ innerGaps l →
    ∃ a b, g = .inner a b ∧ Adjacent l a b := by
  intro l
  induction l with
  | nil => intro g hg; simp [innerGaps] at hg
  | cons a t ih =>
    cases t with
    | nil => intro g hg; simp [innerGaps] at hg
    | cons b t' =>
      intro g hg
      rw [innerGaps] at hg
      rcases List.mem_cons.mp hg with rfl | hg'
      · exact ⟨a, b, rfl, [], t', rfl⟩
      · obtain ⟨x, y, rfl, pre, post, heq⟩ := ih hg'
        exact ⟨x, y, rfl, a :: pre, post, by rw [List.cons_append, heq]⟩

omit [LinearOrder κ] in
/-- Every canonical gap is VALID against its spine. -/
theorem gapsOf_valid : ∀ (l : List κ), ∀ g ∈ gapsOf l, g.Valid l := by
  intro l g hg
  cases l with
  | nil =>
    simp only [gapsOf, List.mem_singleton] at hg
    subst hg; rfl
  | cons a t =>
    rw [gapsOf] at hg
    rcases List.mem_cons.mp hg with rfl | hg
    · rfl
    rcases List.mem_cons.mp hg with rfl | hg
    · exact List.getLast?_eq_some_getLast _
    · obtain ⟨x, y, rfl, hadj⟩ := mem_innerGaps hg
      exact hadj

/-- **Bracket existence (`gapsOf_covers`).** Every key ABSENT from a sorted spine is covered by a
canonical gap: below the minimum, above the maximum, or strictly between an adjacent pair. The
constructive heart of honest-prover totality. -/
theorem gapsOf_covers : ∀ {l : List κ}, Sorted l → ∀ {k : κ}, k ∉ l →
    ∃ g ∈ gapsOf l, g.covers k := by
  intro l
  induction l with
  | nil =>
    intro _ k _
    exact ⟨.empty, by simp [gapsOf], trivial⟩
  | cons a t ih =>
    intro hs k hk
    have hka : k ≠ a := fun h => hk (h ▸ List.mem_cons_self)
    have hkt : k ∉ t := fun h => hk (List.mem_cons_of_mem a h)
    rcases lt_or_gt_of_ne hka with hlt | hgt
    · exact ⟨.below a, by rw [gapsOf]; exact List.mem_cons_self, hlt⟩
    · cases t with
      | nil =>
        refine ⟨.above a, ?_, hgt⟩
        rw [gapsOf]
        exact List.mem_cons_of_mem _ List.mem_cons_self
      | cons b t' =>
        by_cases hkb : k < b
        · refine ⟨.inner a b, ?_, hgt, hkb⟩
          rw [gapsOf, innerGaps]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
        · obtain ⟨g, hg, hcov⟩ :=
            ih (Dregg2.Crypto.NonMembership.sorted_tail hs) hkt
          rw [gapsOf] at hg
          rcases List.mem_cons.mp hg with rfl | hg
          · exact absurd hcov hkb
          rcases List.mem_cons.mp hg with rfl | hg
          · refine ⟨.above ((b :: t').getLast (List.cons_ne_nil b t')), ?_, hcov⟩
            rw [gapsOf]
            have hlast : (a :: b :: t').getLast (List.cons_ne_nil a (b :: t'))
                = (b :: t').getLast (List.cons_ne_nil b t') :=
              List.getLast_cons (List.cons_ne_nil b t')
            rw [hlast]
            exact List.mem_cons_of_mem _ List.mem_cons_self
          · refine ⟨g, ?_, hcov⟩
            rw [gapsOf, innerGaps]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg))

/-- The EXACT answer the honest prover assembles: the range restriction + the canonical gaps. -/
def exactAnswer (h : List (κ × ν)) (lo hi : κ) : Answer κ ν :=
  ⟨rangeOf h lo hi, gapsOf (keys h)⟩

/-- **Honest-prover totality (`exact_answer_verifies`).** The exact answer ALWAYS verifies: every
range query on a sorted index is answerable, completely. (The protocol's completeness direction —
without it `Verifies` could be unsatisfiable and non-omission vacuous.) -/
theorem exact_answer_verifies (h : List (κ × ν)) (lo hi : κ) (hs : SortedKeys h) :
    Verifies h lo hi (exactAnswer h lo hi) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨hmem, hr⟩ := mem_rangeOf.mp he
    exact ⟨hr, get_eq_some_of_mem hs hmem⟩
  · exact gapsOf_valid (keys h)
  · intro k hr hnk
    have hkh : k ∉ keys h := by
      intro hkh
      obtain ⟨v, hv⟩ := mem_keys_iff.mp hkh
      exact hnk (mem_keys_iff.mpr ⟨v, mem_rangeOf.mpr ⟨hv, hr⟩⟩)
    exact gapsOf_covers hs hkh

/-- **The two-sided characterization (`verifies_iff_exact`).** An answer with a sorted item spine
verifies for SOME choice of gap openings IFF its items are EXACTLY the range restriction. Verifying
≡ answering the unique correct answer: nothing dropped, nothing forged, canonical order. -/
theorem verifies_iff_exact {h : List (κ × ν)} {lo hi : κ} {items : List (κ × ν)}
    (hs : SortedKeys h) (hsi : SortedKeys items) :
    (∃ gaps, Verifies h lo hi ⟨items, gaps⟩) ↔ items = rangeOf h lo hi := by
  constructor
  · rintro ⟨gaps, hv⟩
    exact verifies_items_eq_range hs hsi hv
  · rintro rfl
    exact ⟨gapsOf (keys h), exact_answer_verifies h lo hi hs⟩

#assert_axioms mem_innerGaps
#assert_axioms gapsOf_valid
#assert_axioms gapsOf_covers
#assert_axioms exact_answer_verifies
#assert_axioms verifies_iff_exact

/-! ## §4 — the ROOT face: completeness against the COMMITMENT.

The client never sees the index — only `iroot`. Under the one named CR floor, anything verifying
against an index that RECOMPOSES the published root is verifying against THE index
(`iroot_injective`), so soundness + completeness + exactness all pin to the genuine history. -/

open Dregg2.Lightclient.HistoryIndex (ReceiptIndex ReceiptKey iroot)

/-- A `Verifies` run against ANY index recomposing the published root is a run against the genuine
index (CR pins the spine). -/
theorem root_pins_verifies (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {idx idx' : ReceiptIndex} (hroot : iroot hash idx' = iroot hash idx)
    {lo hi : ReceiptKey} {ans : Answer ReceiptKey ℤ}
    (hv : Verifies idx' lo hi ans) : Verifies idx lo hi ans := by
  rwa [iroot_injective hash hCR hroot] at hv

/-- **`server_cannot_omit` — THE HEADLINE.** A client holding ONLY the committed root `iroot idx`:
if the server's answer verifies against ANY index recomposing that root, then (1) the answer
contains EVERY in-range receipt of the genuine index — omission impossible — and (2) every answered
receipt is genuine and in-range — forgery impossible. One named CR floor, nothing else. -/
theorem server_cannot_omit (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {idx idx' : ReceiptIndex} (hs : SortedKeys idx)
    (hroot : iroot hash idx' = iroot hash idx)
    {lo hi : ReceiptKey} {ans : Answer ReceiptKey ℤ}
    (hv : Verifies idx' lo hi ans) :
    AnswerComplete idx lo hi ans ∧ (∀ e ∈ ans.items, e ∈ idx ∧ inRange lo hi e.1) := by
  have hv' := root_pins_verifies hash hCR hroot hv
  exact ⟨answer_complete hs hv', answer_sound hv'⟩

#assert_axioms root_pins_verifies
#assert_axioms server_cannot_omit

/-! ## §5 — the CHAIN face: non-omission over the WHOLE history.

**THE BINDING OBLIGATION the rotation inherits** (stated, named, and consumed here — the weld
itself is the rotation's): the per-turn state commitment that the IVC chain folds
(`recStateCommit` = `HistoryAggregation.stateRoot`, the value `TurnChainBindingAir` pins as
`new_root[i]`) must ABSORB the receipt-index root `iroot` as a SPONGE LIMB — exactly the
`heap_root` discipline (`Substrate.HeapKernel`: register binds heap, commitment binds register).
`CommitBindsIndex` is that obligation; given it, `light_client_query_non_omission` composes with
`RecursiveAggregation.light_client_verifies_whole_history`: ONE `verify agg.root` check pins every
per-turn commitment, each commitment pins its index root, each index root pins every range —
non-omission over the whole history from a single succinct verification. -/

/-- **`CommitBindsIndex` — THE ROTATION OBLIGATION, named.** The per-turn commitment `commit` is a
sponge absorbing the receipt-index root as a limb (`limbs` = the other absorbed fields — cell
digests, registers, turn context). Once the rotation welds `iroot` into `recStateCommit`'s absorbed
list, this hypothesis is discharged by construction. -/
def CommitBindsIndex (hash : List ℤ → ℤ) (limbs : List ℤ) (commit : ℤ)
    (idx : ReceiptIndex) : Prop :=
  commit = hash (limbs ++ [iroot hash idx])

/-- A commitment binding an index root pins the index: two openings of the SAME commitment expose
the SAME index (CR peels the sponge; the index-root limb is the last absorbed element, so it
matches regardless of the other limbs' shape; then `iroot_injective` pins the leaves). -/
theorem commit_pins_index (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {limbs limbs' : List ℤ} {c : ℤ} {idx idx' : ReceiptIndex}
    (hb : CommitBindsIndex hash limbs c idx)
    (hb' : CommitBindsIndex hash limbs' c idx') : idx' = idx := by
  have hl : limbs ++ [iroot hash idx] = limbs' ++ [iroot hash idx'] :=
    hCR _ _ (hb.symm.trans hb')
  have h1 : (limbs ++ [iroot hash idx]).getLast? = some (iroot hash idx) :=
    List.getLast?_concat
  have h2 : (limbs' ++ [iroot hash idx']).getLast? = some (iroot hash idx') :=
    List.getLast?_concat
  rw [hl, h2] at h1
  exact iroot_injective hash hCR (Option.some.inj h1)

open Dregg2.Circuit.RecursiveAggregation
open Dregg2.Distributed.HistoryAggregation (ChainStep)
open Dregg2.Exec (RecChainedState)

/-- **`light_client_query_non_omission` — non-omission over the WHOLE history.** A light client
holding ONLY the aggregation root: if

  * the recursion engine is sound (`EngineSound` — the three named, realizable hypotheses of
    `RecursiveAggregation`) and `verify agg.root = true` (the ONE check the client runs), and
  * the rotation has welded the per-turn receipt-index root into the folded state commitment
    (`hweld : CommitBindsIndex … (ChainStep.newRoot …) (indexOf s)` for every step — THE named
    obligation), with the per-turn indices sorted,

then for ANY step of the history, ANY server-supplied opening of that step's attested commitment,
and ANY verifying range answer: the whole chain is attested (`AggregateAttests` — every turn
executed, correctly ordered, endpoints pinned) AND the answer contains EVERY in-range receipt of
that turn's genuine index, with every answered receipt genuine. The server cannot hide a receipt
anywhere in history from a client that verified one succinct root. -/
theorem light_client_query_non_omission
    (Proof : Type) (verify : Proof → Bool)
    (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
    (RH : Dregg2.Exec.RecordKernelState → ℤ)
    (cmb : ℤ → ℤ → ℤ) (compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
    (hroot : verify agg.root = true)
    -- the per-turn receipt index and THE WELD (the rotation obligation, per step):
    (indexOf : ChainStep → ReceiptIndex) (limbsOf : ChainStep → List ℤ)
    (hsorted : ∀ s ∈ steps, SortedKeys (indexOf s))
    (hweld : ∀ s ∈ steps, CommitBindsIndex hash (limbsOf s)
      (ChainStep.newRoot CH RH cmb compress compressN s) (indexOf s))
    -- the queried step + the server's opening of its ATTESTED commitment + a verifying answer:
    {s : ChainStep} (hstep : s ∈ steps)
    {idx' : ReceiptIndex} {limbs' : List ℤ}
    (hopen : CommitBindsIndex hash limbs'
      (ChainStep.newRoot CH RH cmb compress compressN s) idx')
    {lo hi : ReceiptKey} {ans : Answer ReceiptKey ℤ}
    (hv : Verifies idx' lo hi ans) :
    AggregateAttests Proof CH RH cmb compress compressN agg g steps
      ∧ AnswerComplete (indexOf s) lo hi ans
      ∧ (∀ e ∈ ans.items, e ∈ indexOf s ∧ inRange lo hi e.1) := by
  have hpin : idx' = indexOf s := commit_pins_index hash hCR (hweld s hstep) hopen
  rw [hpin] at hv
  exact ⟨light_client_verifies_whole_history Proof verify CH RH cmb compress compressN
      agg g steps es hroot,
    answer_complete (hsorted s hstep) hv, answer_sound hv⟩

#assert_axioms commit_pins_index
#assert_axioms light_client_query_non_omission

/-! ## §6 — NON-VACUITY: witnesses TRUE and FALSE on a concrete index.

Over `ℤ` keys (the generic layer is what the protocol theorems live on; `HistoryIndex` §3 already
witnesses the `ReceiptKey` instantiation + root movement). Index `[(10,1),(20,2),(30,3)]`, query
range `[15, 30]`:

  * TRUE — the exact answer `{items := [(20,2),(30,3)], gaps := [inner 10 20, inner 20 30]}`
    VERIFIES (`demo_good_verifies`), and `exactAnswer` computes it (`#guard`);
  * FALSE — dropping receipt `(20,2)` is REJECTED (`demo_dropped_rejected` — the false witness for
    completeness: key 20 is in range and in the index but not answerable by any valid gap);
  * FALSE — the forged wide gap `inner 10 30` that would "cover" the dropped key is INVALID
    (`demo_forged_gap_invalid` — adjacency cannot be faked while 20 is present);
  * FALSE — a forged extra receipt `(25, 9)` is REJECTED (`demo_forged_item_rejected` — no
    membership opening exists for an absent key). -/

/-- The demo index over `ℤ` keys. -/
def demoIdx : List (ℤ × ℤ) := [(10, 1), (20, 2), (30, 3)]

theorem demoIdx_sorted : SortedKeys demoIdx := by
  norm_num [demoIdx, SortedKeys, keys, List.pairwise_cons]

/-- The honest complete answer to the range `[15, 30]`. -/
def goodAns : Answer ℤ ℤ := ⟨[(20, 2), (30, 3)], [.inner 10 20, .inner 20 30]⟩

/-- **Witness TRUE** — the complete answer VERIFIES. -/
theorem demo_good_verifies : Verifies demoIdx 15 30 goodAns := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨⟨by norm_num, by norm_num⟩, by decide⟩
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨⟨by norm_num, by norm_num⟩, by decide⟩
    · simp at he
  · intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨[], [30], rfl⟩
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨[10], [], rfl⟩
    · simp at hg
  · intro k hr hnk
    simp only [goodAns, keys, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false, not_or] at hnk
    obtain ⟨h20, h30⟩ := hnk
    obtain ⟨h15, h30'⟩ := hr
    by_cases hk : k < 20
    · exact ⟨.inner 10 20, List.mem_cons_self, by omega, hk⟩
    · exact ⟨.inner 20 30, List.mem_cons_of_mem _ List.mem_cons_self, by omega, by omega⟩

-- The executable face: `exactAnswer` computes exactly the honest items + canonical gaps.
#guard (exactAnswer demoIdx 15 30).items == [(20, 2), (30, 3)]
#guard rangeOf demoIdx 15 30 == [(20, 2), (30, 3)]
#guard gapsOf (keys demoIdx)
    == [.below 10, .above 30, .inner 10 20, .inner 20 30]
-- An empty range is answerable too (pure gaps):
#guard rangeOf demoIdx 11 19 == []
#guard (exactAnswer demoIdx 11 19).items == ([] : List (ℤ × ℤ))

/-- The dishonest answer: receipt `(20, 2)` silently DROPPED (gaps kept honest). -/
def droppedAns : Answer ℤ ℤ := ⟨[(30, 3)], [.inner 10 20, .inner 20 30]⟩

/-- **Witness FALSE #1 — omission is REJECTED.** No valid gap can cover the present key 20, so the
coverage check fails: `Verifies` is false for the dropped answer. (Derived from THE THEOREM:
a verifying answer would have to contain key 20.) -/
theorem demo_dropped_rejected : ¬ Verifies demoIdx 15 30 droppedAns := by
  intro hv
  have h20 := answer_complete demoIdx_sorted hv 20
    (by norm_num [demoIdx, keys]) ⟨by norm_num, by norm_num⟩
  norm_num [droppedAns, keys] at h20

/-- **Witness FALSE #2 — the forged covering gap is INVALID.** The adversary trying to hide
`(20, 2)` behind a wide gap `inner 10 30` fails: 10 and 30 are NOT adjacent while 20 sits between
them, and `Gap.excludes` turns any claimed validity into `20 ∉ keys demoIdx` — absurd. -/
theorem demo_forged_gap_invalid : ¬ (Gap.inner (10 : ℤ) 30).Valid (keys demoIdx) := by
  intro hadj
  have h20 : (20 : ℤ) ∉ keys demoIdx :=
    Gap.excludes (l := keys demoIdx) demoIdx_sorted hadj ⟨by norm_num, by norm_num⟩
  exact h20 (by norm_num [demoIdx, keys])

/-- ...and therefore the drop-plus-forged-gap answer is rejected wholesale (still THE THEOREM). -/
theorem demo_dropped_forged_rejected :
    ¬ Verifies demoIdx 15 30 ⟨[(30, 3)], [.inner 10 30]⟩ := by
  intro hv
  have h20 := answer_complete demoIdx_sorted hv 20
    (by norm_num [demoIdx, keys]) ⟨by norm_num, by norm_num⟩
  norm_num [keys] at h20

/-- **Witness FALSE #3 — a forged extra receipt is REJECTED.** `(25, 9)` is not in the index, so
its membership opening cannot verify (`get demoIdx 25 = none ≠ some 9`). -/
theorem demo_forged_item_rejected :
    ¬ Verifies demoIdx 15 30 ⟨[(20, 2), (25, 9), (30, 3)], [.inner 20 30]⟩ := by
  intro hv
  have h25 := (hv.1 (25, 9) (List.mem_cons_of_mem _ List.mem_cons_self)).2
  exact absurd h25 (by decide)

/-- **Witness FALSE #4 — a tampered receipt VALUE is rejected** (`(20, 7)` against genuine
`(20, 2)`): the opening pins the value, not just the key. -/
theorem demo_tampered_value_rejected :
    ¬ Verifies demoIdx 15 30 ⟨[(20, 7), (30, 3)], [.inner 10 20, .inner 20 30]⟩ := by
  intro hv
  have h20 := (hv.1 (20, 7) List.mem_cons_self).2
  exact absurd h20 (by decide)

#assert_axioms demo_good_verifies
#assert_axioms demo_dropped_rejected
#assert_axioms demo_forged_gap_invalid
#assert_axioms demo_dropped_forged_rejected
#assert_axioms demo_forged_item_rejected
#assert_axioms demo_tampered_value_rejected

end Dregg2.Lightclient.AttestedQuery
