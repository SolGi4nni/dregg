/-
# Dregg2.Crypto.Digest8KeySpike — the #4/#10 note-nullifier reclassification, machine-checked.

CLAIM (CONFIRMED by the original spike, now landed): the feared "new bracketing math over
multi-felt keys" for the note-nullifier non-membership is too pessimistic —
`NonMembership.sorted_gap_excludes` is `[LinearOrder Digest]`-GENERIC, and the deployed IMT chain
(`Circuit/IndexedMerkleTree.lean`) is now KEY-GENERIC (`ImtLeaf K V` with `[LinearOrder K]`,
deployed shape = the default `K := ℤ, V := ℤ`). So the 8-felt key only needs
`Digest8Key := Lex (Fin 8 → ℤ)` and BOTH bracketing keystones instantiate directly:
  * `sorted_gap_excludes_digest8` — the sorted-gap non-membership at the 8-felt lex key, a
    one-line `exact`; non-vacuity teeth run a REAL multi-felt bracket (the lo/e compare decided at
    felt 7, the e/hi compare at felt 0 — genuinely lexicographic, not a felt-0-only disguise).
  * `imtAbsent_excludes_digest8` / `imtInsert_preserves_digest8` — the DEPLOYED IMT pointer-bracket
    keystone and its insert-preservation, instantiated at the widened key from the SAME generic
    object the felt chain deploys (no twin, no re-statement — the ℤ→K generalization landed
    unadditively inside `IndexedMerkleTree.lean`, closing this file's original ⚠ bridge item).

THE WRINKLE (why `Lex` and not bare `Fin 8 → ℤ`): the deployed `Digest8 := Fin 8 → ℤ` carries the
POINTWISE product order, which is only partial — `product_order_incomparable` exhibits two 8-felt
keys neither ≤ the other, and `lex_repairs_comparability` shows the SAME pair is strictly ordered
under `Lex`. So the sorted-key boundary must run under the `Lex` synonym (Mathlib
`Pi.Lex.linearOrder`, needing `[LinearOrder (Fin 8)]` + `WellFoundedLT (Fin 8)` + `[LinearOrder ℤ]`,
all synthesized; `DecidableEq` via `instDecidableEqLex`). `[DecidableEq K]` needs no separate
hypothesis — `LinearOrder K` carries it.

REMAINING REAL WORK for #4/#10 (correctly scoped): the lex-compare AIR gadget (an 8-limb
lexicographic `<` circuit) + the leaf widening (addr/nextAddr 1 felt → 8 felts). The SOUNDNESS side
is "instantiate the existing lemma family," as this file demonstrates against the deployed objects.

Heap safety: everything here is on literal 1-2-element lists and `Fin 8` iteration; no `2^16`
object, no `native_decide`; `decide` only on `Fin 8`/small-`ℤ` literals.
-/
import Dregg2.Crypto.NonMembership
import Dregg2.Circuit.IndexedMerkleTree
import Mathlib.Order.PiLex

namespace Dregg2.Crypto.Digest8KeySpike

open Dregg2.Crypto.NonMembership
open Dregg2.Circuit.IndexedMerkleTree (ImtLeaf ImtSorted ImtAbsent imtAddrs imtInsert
  imtAbsent_excludes imtInsert_preserves)

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

/-! ## §3 — THE DEPLOYED IMT AT THE 8-FELT KEY: direct instantiation, no twin.

`Circuit/IndexedMerkleTree.lean` is key-generic (`ImtLeaf K V`, `[LinearOrder K]`; the deployed
felt chain is the default instantiation `ImtLeaf ℤ ℤ`). The original spike's `ImtLeafK` twin (a
diff-checked re-statement) is RETIRED — these are the SAME `ImtLeaf`/`ImtSorted`/`ImtAbsent`/
`imtInsert`/`imtAbsent_excludes`/`imtInsert_preserves` the felt chain deploys, at
`K := Digest8Key, V := ℤ`. -/

/-- **The 8-felt-key IMT pointer bracket** — the #4/#10 leaf-widening target: `addr`/`nextAddr`
are 8-felt lex keys, `value` stays a felt. Direct instantiation of the DEPLOYED generic keystone
`IndexedMerkleTree.imtAbsent_excludes`. -/
theorem imtAbsent_excludes_digest8 {c : List (ImtLeaf Digest8Key ℤ)} (hs : ImtSorted c)
    {k : Digest8Key} (ha : ImtAbsent c k) : k ∉ imtAddrs c :=
  imtAbsent_excludes hs ha

/-- **The 8-felt-key insert preservation** — the DEPLOYED `imtInsert_preserves` at the widened key
(the spike could not state this: its twin never generalized the insert). A bracketed insert of an
8-felt lex key keeps the chain `ImtSorted` — the in-circuit induction step for the widened leaf. -/
theorem imtInsert_preserves_digest8 {c : List (ImtLeaf Digest8Key ℤ)} (hs : ImtSorted c)
    {k : Digest8Key} {v : ℤ} (ha : ImtAbsent c k) : ImtSorted (imtInsert c k v) :=
  imtInsert_preserves hs ha

/-! ### §3-teeth — the widened-leaf bracket fires on a concrete 8-felt chain. -/

/-- A one-leaf IMT chain over 8-felt keys: the `keyLo → keyHi` sentinel-style leaf — a leaf of the
DEPLOYED generic `ImtLeaf`, key type widened. -/
def spikeLeaf : ImtLeaf Digest8Key ℤ := ⟨keyLo, 7, keyHi⟩

theorem spikeChain_sorted : ImtSorted [spikeLeaf] := keyLo_lt_keyHi

/-- **★ NON-VACUITY** — the pointer bracket `keyLo < keyE < keyHi` (multi-felt compares, felts 7
and 0) excludes `keyE` from the widened chain's spine. -/
theorem spike_imt_excluded : keyE ∉ imtAddrs [spikeLeaf] :=
  imtAbsent_excludes_digest8 spikeChain_sorted ⟨spikeLeaf, by simp, keyLo_lt_keyE, keyE_lt_keyHi⟩

/-- **★ LIVENESS** — inserting the bracketed `keyE` into the widened chain PRESERVES `ImtSorted`:
the deployed induction step fires at the 8-felt key on a concrete chain. -/
theorem spike_imt_insert_sorted : ImtSorted (imtInsert [spikeLeaf] keyE (5 : ℤ)) :=
  imtInsert_preserves_digest8 spikeChain_sorted ⟨spikeLeaf, by simp, keyLo_lt_keyE, keyE_lt_keyHi⟩

/-! ## §4 — axiom hygiene: every keystone rests on the kernel triple only. -/

#assert_axioms sorted_gap_excludes_digest8
#assert_axioms spike_excluded
#assert_axioms spike_member
#assert_axioms product_order_incomparable
#assert_axioms lex_repairs_comparability
#assert_axioms imtAbsent_excludes_digest8
#assert_axioms imtInsert_preserves_digest8
#assert_axioms spike_imt_excluded
#assert_axioms spike_imt_insert_sorted

end Dregg2.Crypto.Digest8KeySpike
