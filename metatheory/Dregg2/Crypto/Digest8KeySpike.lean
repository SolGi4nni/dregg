/-
# Dregg2.Crypto.Digest8KeySpike — SPIKE: the #4/#10 note-nullifier reclassification, machine-checked.

CLAIM UNDER TEST: the feared "new bracketing math over multi-felt keys" for the note-nullifier
non-membership is too pessimistic, because `NonMembership.sorted_gap_excludes` is already
`[LinearOrder Digest]`-GENERIC — so the 8-felt key only needs `Digest := Lex (Fin 8 → ℤ)` and the
bracketing combinatorics come for free (zero ℤ-specific reproof).

VERDICT: **CONFIRMED**, both halves:
  * `sorted_gap_excludes_digest8` — `sorted_gap_excludes` fully instantiated at the 8-felt lex key,
    a one-line `exact`; non-vacuity teeth run a REAL multi-felt bracket (the lo/e compare decided at
    felt 7, the e/hi compare at felt 0 — genuinely lexicographic, not a felt-0-only disguise).
  * the IMT pointer bracket (`Circuit/IndexedMerkleTree.imtAbsent_excludes`, stated concretely over
    `ℤ` at :261) generalizes in ONE step: `ImtLeafK K V` below is the verbatim ℤ→K rename of
    `ImtLeaf`/`ImtSorted`/`ImtAbsent`, and the proofs (`imtSortedK_addrs_sorted`,
    `imtSortedK_dichotomy`, `imtAbsentK_excludes`) close UNCHANGED — they use only `<`/`≤`/`.trans`,
    no ℤ arithmetic (no `omega`, no `norm_num`-on-ℤ inside the order proofs).

THE WRINKLE (why `Lex` and not bare `Fin 8 → ℤ`): the deployed `Digest8 := Fin 8 → ℤ` carries the
POINTWISE product order, which is only partial — `product_order_incomparable` exhibits two 8-felt
keys neither ≤ the other, and `lex_repairs_comparability` shows the SAME pair is strictly ordered
under `Lex`. So the sorted-key boundary must run under the `Lex` synonym (Mathlib
`Pi.Lex.linearOrder`, needing `[LinearOrder (Fin 8)]` + `WellFoundedLT (Fin 8)` + `[LinearOrder ℤ]`,
all synthesized; `DecidableEq` via `instDecidableEqLex`). `[DecidableEq K]` needs no separate
hypothesis — `LinearOrder K` carries it.

⚠ ONE ITEM NOT MACHINE-CHECKED HERE (build-perimeter, not math): the bridge lemma mapping the
deployed `Circuit.IndexedMerkleTree.ImtLeaf` into `ImtLeafK ℤ ℤ` (field-for-field identical) could
not be compiled in this spike because `Dregg2/Circuit/MapOpsColumnLayout.olean` is absent from the
current build tree and this spike is forbidden from building it. `imtAbsentK_excludes_int` (the
K := ℤ instantiation, the exact deployed statement shape) stands in; the follow-up lane that owns
the real generalization should land it INSIDE `IndexedMerkleTree.lean` (unadditive: change ℤ to K
there, don't keep a twin here).

REMAINING REAL WORK for #4/#10 (unchanged by this spike, now correctly scoped): the lex-compare AIR
gadget (an 8-limb lexicographic `<` circuit) + the leaf widening (addr/nextAddr 1 felt → 8 felts).
The SOUNDNESS side is "instantiate an existing lemma family," as this file demonstrates.

Heap safety: everything here is on literal 2-element lists and `Fin 8` iteration; no `2^16` object,
no `native_decide`; `decide` only on `Fin 8`/small-`ℤ` literals.
-/
import Dregg2.Crypto.NonMembership
import Mathlib.Order.PiLex

namespace Dregg2.Crypto.Digest8KeySpike

open Dregg2.Crypto.NonMembership

set_option autoImplicit false

/-! ## §1 — the 8-felt key type: `Lex (Fin 8 → ℤ)`, with its order wired from Mathlib. -/

/-- **`Digest8Key`** — the 8-felt digest as a NON-MEMBERSHIP SORT KEY: the deployed
`Digest8 := Fin 8 → ℤ` under the LEXICOGRAPHIC order (`Lex` synonym; felt 0 is the most-significant
limb). The bare product order on `Fin 8 → ℤ` is not linear (§1-wrinkle below), so the key lives
under `Lex`, where Mathlib's `Pi.Lex.linearOrder` applies. -/
abbrev Digest8Key : Type := Lex (Fin 8 → ℤ)

/-- The `LinearOrder` is synthesized (Mathlib `Pi.Lex.linearOrder`: `LinearOrder (Fin 8)` +
`WellFoundedLT (Fin 8)` + `LinearOrder ℤ`). Noncomputable (total-order comparison via
well-founded choice of the first differing index) — irrelevant here: the AIR gadget implements the
compare; Lean only needs the ORDER for the combinatorics. -/
noncomputable example : LinearOrder Digest8Key := inferInstance

/-- `DecidableEq` is synthesized (`instDecidableEqLex` over `Fintype (Fin 8)` + `DecidableEq ℤ`). -/
example : DecidableEq Digest8Key := inferInstance

/-- **THE WRINKLE, witnessed** — the bare product order on `Fin 8 → ℤ` is NOT linear: the keys
`(1,0,0,…)` and `(0,1,0,…)` are incomparable pointwise. Any "sorted leaves" statement over bare
`Digest8` is therefore ill-posed; the `Lex` synonym is load-bearing, not decorative. -/
theorem product_order_incomparable :
    ∃ x y : Fin 8 → ℤ, ¬ x ≤ y ∧ ¬ y ≤ x := by
  refine ⟨(fun i => if i = 0 then 1 else 0), (fun i => if i = 1 then 1 else 0), ?_, ?_⟩
  · intro h
    have := h 0
    simp at this
  · intro h
    have := h 1
    simp at this

/-- …and the SAME pair is strictly ordered under `Lex` (decided at felt 0): the synonym repairs
exactly the comparability the bracketing needs. -/
theorem lex_repairs_comparability :
    toLex (fun i : Fin 8 => if i = 1 then (1 : ℤ) else 0)
      < toLex (fun i : Fin 8 => if i = 0 then (1 : ℤ) else 0) := by
  refine ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), ?_⟩
  show (if (0 : Fin 8) = 1 then (1 : ℤ) else 0) < if (0 : Fin 8) = 0 then 1 else 0
  decide

/-! ## §2 — THE LOAD-BEARING CONFIRMATION: `sorted_gap_excludes` at `Digest := Digest8Key`. -/

#check @sorted_gap_excludes Digest8Key _

/-- **`sorted_gap_excludes_digest8` — the reclassification, machine-confirmed.** The sorted-gap
non-membership soundness heart at the 8-felt lex key, FULLY APPLIED and closing by direct
instantiation — zero new bracketing math, zero ℤ-specific reproof. The #4/#10 soundness core for
multi-felt note-nullifier keys IS the existing lemma family. -/
theorem sorted_gap_excludes_digest8 (leaves : List Digest8Key) (lo hi e : Digest8Key)
    (hsorted : Sorted leaves) (hadj : Adjacent leaves lo hi)
    (hlo : lo < e) (hhi : e < hi) : e ∉ leaves :=
  sorted_gap_excludes leaves lo hi e hsorted hadj hlo hhi

/-! ### §2-teeth — a REAL multi-felt bracket (compares decided at DIFFERENT limbs).

`keyLo = (0,…,0)`, `keyE = (0,…,0,1)` (differs at felt 7 only), `keyHi = (1,0,…,0)` (differs at
felt 0). So `keyLo < keyE` is decided at the LAST limb and `keyE < keyHi` at the FIRST — the bracket
genuinely exercises the lexicographic order across limbs, not a felt-0 disguise of the old ℤ case. -/

/-- The all-zeros 8-felt key (as a raw function). -/
def z8 : Fin 8 → ℤ := fun _ => 0

/-- `(0,0,0,0,0,0,0,0)` — the left bracketing neighbor. -/
def keyLo : Digest8Key := toLex z8
/-- `(0,0,0,0,0,0,0,1)` — the bracketed element; differs from `keyLo` ONLY at felt 7. -/
def keyE : Digest8Key := toLex (fun i => if i = 7 then 1 else 0)
/-- `(1,0,0,0,0,0,0,0)` — the right bracketing neighbor; differs at felt 0. -/
def keyHi : Digest8Key := toLex (fun i => if i = 0 then 1 else 0)

/-- `keyLo < keyE`, decided at felt 7 (all earlier limbs EQUAL — the lex witness walks past them). -/
theorem keyLo_lt_keyE : keyLo < keyE := by
  refine ⟨7, fun j hj => ?_, ?_⟩
  · show z8 j = if j = 7 then 1 else 0
    rw [if_neg (Fin.ne_of_lt hj)]
    rfl
  · show z8 7 < if (7 : Fin 8) = 7 then 1 else 0
    simp [z8]

/-- `keyE < keyHi`, decided at felt 0 (the most-significant limb dominates felt 7's `1`). -/
theorem keyE_lt_keyHi : keyE < keyHi := by
  refine ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), ?_⟩
  show (if (0 : Fin 8) = 7 then (1 : ℤ) else 0) < if (0 : Fin 8) = 0 then 1 else 0
  decide

/-- `keyLo < keyHi`, decided at felt 0 — the sortedness of the two-leaf committed list. -/
theorem keyLo_lt_keyHi : keyLo < keyHi := by
  refine ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), ?_⟩
  show z8 0 < if (0 : Fin 8) = 0 then (1 : ℤ) else 0
  simp [z8]

/-- The committed sorted 8-felt-key leaf list `[keyLo, keyHi]`. -/
def spikeLeaves : List Digest8Key := [keyLo, keyHi]

theorem spikeLeaves_sorted : Sorted spikeLeaves := by
  simp only [spikeLeaves, Sorted, List.pairwise_cons, List.mem_singleton, List.not_mem_nil,
    false_implies, implies_true]
  exact ⟨fun a' ha' => by rw [ha']; exact keyLo_lt_keyHi, trivial, List.Pairwise.nil⟩

theorem spike_adjacent : Adjacent spikeLeaves keyLo keyHi := ⟨[], [], rfl⟩

/-- **★ NON-VACUITY — the instantiated keystone FIRES on a real multi-felt bracket:** `keyE` (the
felt-7 bump) is excluded from the committed list by the `keyLo`/`keyHi` neighbors, with the two
strict compares decided at felts 7 and 0 respectively. -/
theorem spike_excluded : keyE ∉ spikeLeaves :=
  sorted_gap_excludes_digest8 spikeLeaves keyLo keyHi keyE
    spikeLeaves_sorted spike_adjacent keyLo_lt_keyE keyE_lt_keyHi

/-- **DISCRIMINATION TOOTH** — the exclusion is not vacuous about everything: the genuine member
`keyLo` IS in the list. -/
theorem spike_member : keyLo ∈ spikeLeaves := by simp [spikeLeaves]

/-! ## §3 — the IMT pointer bracket generalizes in ONE step (ℤ → K).

`Circuit/IndexedMerkleTree.lean` states `ImtLeaf.addr/nextAddr : ℤ` concretely (:105) and proves
`imtAbsent_excludes` (:261) over it. Below is the SAME def/proof text with `ℤ` renamed to
`{K} [LinearOrder K]` (value type also freed to `V` — the ordering never touches it). Every proof
closes verbatim: the chain uses only `<`/`≤`/`le_of_lt`/`.trans`/`lt_irrefl` and the generic
`NonMembership.Sorted`/`head_lt_of_sorted` — NO ℤ arithmetic anywhere. The real closure should be
UNADDITIVE (rename inside `IndexedMerkleTree.lean` once its build tree is green), not a twin. -/

universe u v

variable {K : Type u} {V : Type v}

/-- `ImtLeaf` with the key type freed: `addr`/`nextAddr : K` (the 8-felt lex key slot), `value : V`.
Verbatim ℤ→K rename of `Circuit.IndexedMerkleTree.ImtLeaf`. -/
structure ImtLeafK (K : Type u) (V : Type v) where
  /-- The sort key (widens to `Digest8Key` for note nullifiers). -/
  addr : K
  /-- The stored value (irrelevant to the ordering — hence a free `V`). -/
  value : V
  /-- The pointer to the next-larger present key (the absence bracket). -/
  nextAddr : K

/-- The address spine (ℤ→K rename of `imtAddrs`). -/
def imtAddrsK (c : List (ImtLeafK K V)) : List K := c.map (·.addr)

@[simp] theorem imtAddrsK_cons (l : ImtLeafK K V) (c : List (ImtLeafK K V)) :
    imtAddrsK (l :: c) = l.addr :: imtAddrsK c := rfl

@[simp] theorem imtAddrsK_nil : imtAddrsK ([] : List (ImtLeafK K V)) = [] := rfl

theorem mem_imtAddrsK {c : List (ImtLeafK K V)} {x : K} :
    x ∈ imtAddrsK c ↔ ∃ l ∈ c, l.addr = x := by
  simp [imtAddrsK, List.mem_map]

variable [LinearOrder K]

/-- The well-linked strictly-increasing chain invariant (ℤ→K rename of `ImtSorted`). -/
def ImtSortedK : List (ImtLeafK K V) → Prop
  | [] => True
  | [l] => l.addr < l.nextAddr
  | l :: l' :: rest => l.addr < l.nextAddr ∧ l.nextAddr = l'.addr ∧ ImtSortedK (l' :: rest)

@[simp] theorem imtSortedK_nil : ImtSortedK ([] : List (ImtLeafK K V)) = True := rfl
@[simp] theorem imtSortedK_singleton (l : ImtLeafK K V) :
    ImtSortedK [l] = (l.addr < l.nextAddr) := rfl
@[simp] theorem imtSortedK_cons_cons (l l' : ImtLeafK K V) (rest : List (ImtLeafK K V)) :
    ImtSortedK (l :: l' :: rest)
      = (l.addr < l.nextAddr ∧ l.nextAddr = l'.addr ∧ ImtSortedK (l' :: rest)) := rfl

/-- The pointer-bracket absence open (ℤ→K rename of `ImtAbsent`). -/
def ImtAbsentK (c : List (ImtLeafK K V)) (k : K) : Prop :=
  ∃ low ∈ c, low.addr < k ∧ k < low.nextAddr

/-- ℤ→K rename of `imtSorted_addrs_sorted` — proof UNCHANGED (only `<`-monotone steps). -/
theorem imtSortedK_addrs_sorted :
    ∀ {c : List (ImtLeafK K V)}, ImtSortedK c → Sorted (imtAddrsK c) := by
  intro c
  induction c with
  | nil => intro _; simp [imtAddrsK, Sorted]
  | cons l rest ih =>
    intro hs
    cases rest with
    | nil => simp [imtAddrsK, Sorted, List.pairwise_cons]
    | cons l' rest' =>
      rw [imtSortedK_cons_cons] at hs
      obtain ⟨h1, h2, htail⟩ := hs
      have ihs : Sorted (imtAddrsK (l' :: rest')) := ih htail
      have hll' : l.addr < l'.addr := by rw [h2] at h1; exact h1
      rw [imtAddrsK_cons, Sorted, List.pairwise_cons]
      refine ⟨?_, ihs⟩
      intro x hx
      rw [imtAddrsK_cons] at hx
      rcases List.mem_cons.mp hx with rfl | hxr
      · exact hll'
      · exact hll'.trans (head_lt_of_sorted ihs x hxr)

/-- ℤ→K rename of `imtSorted_dichotomy` — proof UNCHANGED (`le_refl`/`le_of_lt`/head facts only). -/
theorem imtSortedK_dichotomy : ∀ {c : List (ImtLeafK K V)}, ImtSortedK c →
    ∀ low ∈ c, ∀ x ∈ imtAddrsK c, x ≤ low.addr ∨ low.nextAddr ≤ x := by
  intro c
  induction c with
  | nil => intro _ low hlow; exact absurd hlow (by simp)
  | cons l rest ih =>
    intro hs low hlow x hx
    have hsort : Sorted (imtAddrsK (l :: rest)) := imtSortedK_addrs_sorted hs
    rcases List.mem_cons.mp hlow with rfl | hlowr
    · rw [imtAddrsK_cons] at hx
      rcases List.mem_cons.mp hx with rfl | hxr
      · exact Or.inl (le_refl _)
      · refine Or.inr ?_
        cases rest with
        | nil => exact absurd hxr (by simp)
        | cons r rest' =>
          rw [imtSortedK_cons_cons] at hs
          rw [hs.2.1]
          rw [imtAddrsK_cons] at hxr
          rcases List.mem_cons.mp hxr with rfl | hxr'
          · exact le_refl _
          · exact le_of_lt (head_lt_of_sorted (imtSortedK_addrs_sorted hs.2.2) x hxr')
    · cases rest with
      | nil => exact absurd hlowr (by simp)
      | cons r rest' =>
        rw [imtAddrsK_cons] at hx
        rcases List.mem_cons.mp hx with rfl | hxr
        · refine Or.inl (le_of_lt ?_)
          have hlowaddr : low.addr ∈ imtAddrsK (r :: rest') := mem_imtAddrsK.mpr ⟨low, hlowr, rfl⟩
          exact head_lt_of_sorted hsort low.addr hlowaddr
        · rw [imtSortedK_cons_cons] at hs
          exact ih hs.2.2 low hlowr x hxr

/-- **`imtAbsentK_excludes` — the IMT pointer-bracket keystone, K-GENERIC.** ℤ→K rename of
`imtAbsent_excludes` (:261) — proof UNCHANGED (`lt_of_le_of_lt`/`lt_of_lt_of_le`/`lt_irrefl`). The
IMT bracket needs NOTHING from ℤ. -/
theorem imtAbsentK_excludes {c : List (ImtLeafK K V)} (hs : ImtSortedK c) {k : K}
    (ha : ImtAbsentK c k) : k ∉ imtAddrsK c := by
  obtain ⟨low, hlow, h1, h2⟩ := ha
  intro hk
  rcases imtSortedK_dichotomy hs low hlow k hk with hle | hge
  · exact absurd (lt_of_le_of_lt hle h1) (lt_irrefl _)
  · exact absurd (lt_of_lt_of_le h2 hge) (lt_irrefl _)

/-- The K := ℤ instantiation — the deployed statement SHAPE (`ImtLeafK ℤ ℤ` is field-for-field
`Circuit.IndexedMerkleTree.ImtLeaf`) recovered from the generic keystone, showing nothing is lost at
the deployed instance. (The literal bridge to `ImtLeaf` itself is the build-perimeter item in the
header.) -/
theorem imtAbsentK_excludes_int {c : List (ImtLeafK ℤ ℤ)} (hs : ImtSortedK c) {k : ℤ}
    (ha : ImtAbsentK c k) : k ∉ imtAddrsK c :=
  imtAbsentK_excludes hs ha

/-- **The 8-felt-key IMT bracket** — the #4/#10 leaf-widening target: `addr`/`nextAddr` are 8-felt
lex keys, `value` stays a felt. Direct instantiation of the generic keystone. -/
theorem imtAbsentK_excludes_digest8 {c : List (ImtLeafK Digest8Key ℤ)} (hs : ImtSortedK c)
    {k : Digest8Key} (ha : ImtAbsentK c k) : k ∉ imtAddrsK c :=
  imtAbsentK_excludes hs ha

/-! ### §3-teeth — the widened-leaf bracket fires on a concrete 8-felt chain. -/

/-- A one-leaf IMT chain over 8-felt keys: the `keyLo → keyHi` sentinel-style leaf. -/
def spikeLeaf : ImtLeafK Digest8Key ℤ := ⟨keyLo, 7, keyHi⟩

theorem spikeChain_sorted : ImtSortedK [spikeLeaf] := keyLo_lt_keyHi

/-- **★ NON-VACUITY** — the pointer bracket `keyLo < keyE < keyHi` (multi-felt compares, felts 7
and 0) excludes `keyE` from the widened chain's spine. -/
theorem spike_imt_excluded : keyE ∉ imtAddrsK [spikeLeaf] :=
  imtAbsentK_excludes_digest8 spikeChain_sorted ⟨spikeLeaf, by simp, keyLo_lt_keyE, keyE_lt_keyHi⟩

/-! ## §4 — axiom hygiene: every keystone rests on the kernel triple only. -/

#assert_axioms sorted_gap_excludes_digest8
#assert_axioms spike_excluded
#assert_axioms spike_member
#assert_axioms product_order_incomparable
#assert_axioms lex_repairs_comparability
#assert_axioms imtSortedK_addrs_sorted
#assert_axioms imtSortedK_dichotomy
#assert_axioms imtAbsentK_excludes
#assert_axioms imtAbsentK_excludes_int
#assert_axioms imtAbsentK_excludes_digest8
#assert_axioms spike_imt_excluded

end Dregg2.Crypto.Digest8KeySpike
