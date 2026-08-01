/-
# Dregg2.Crypto.Digest9Key — THE MAP KEY THAT IS ACTUALLY INJECTIVE, and the arity-19 leaf.

## Why this file exists

`Crypto/Digest8KeySpike.lean` built `Digest8Key := Lex (Fin 8 → ℤ)` and the whole wide `.absent`
tower stands on it. `Circuit/MapOpWideKeyPigeonhole.lean` then REFUTED that tower's deployed
instance:

  * `no_injection_bytes32_to_canonKey8` — NO function from 32-byte addresses into eight canonical
    BabyBear lanes is injective. Not "none is known": `P ^ 8 < 2 ^ 256`, pigeonhole.
  * `arity17_conflates_two_addresses` — so the arity-17 leaf `addr8 ‖ value ‖ next8` absorbs the
    IDENTICAL preimage for two distinct 32-byte addresses, **for every hash, at every codomain,
    with no collision-resistance hypothesis.**

That refutation names two exits (`nine_lanes_would_clear_it`, `u16_limbs_admit_a_bijection`). This
file takes the NINE-LANE one and builds the successor key: `Digest9Key`, the arity-19 leaf
`addr9 ‖ value ‖ next9`, and the constructed injection that is the exact negation of the refutation
above.

## ⚑ KEY vs HASH NODE — the distinction that picks the width, said out loud

A **hash node** needs COLLISION RESISTANCE: eight BabyBear lanes give `8 · log₂ p = 247.26` bits, a
`2^123.63` birthday bound, and that clears this tree's bar. A **KEY** needs INJECTIVITY, which is
not a bound at all — it is a property of the encoding, and eight lanes cannot have it against 32
bytes at any hash. **Neither number transfers to the other question.** `node8` roots and folds stay
at eight lanes throughout; only the three columns that carry a KEY move to nine.

## ⚑ WHICH NONET, and why — the fork, decided on the evidence

Two nine-lane primitives exist in this tree and they are DIFFERENT MAPS. This file uses
`Circuit.KeyLanes9.keyToLanes9`, not `Circuit.FieldLanes9.fieldToLanes9`:

| | `KeyLanes9` (chosen) | `FieldLanes9` (rejected here) |
|---|---|---|
| shape | base-`2^29` digits of the 256-bit word | lanes 0/1 are `lo % p` / `hi % p`, then 28-bit limbs of the rest + a carry digit |
| any lane a reduction? | **no** — `2^29 < p`, nothing ever reduces | **yes** — lanes 0/1 ARE a `mod p` map, pinned to the deployed kernel-`u64` `SetField` ABI |
| canonicity envelope | 8 lookups at width 29 + **1 at width 24**; zero gates, zero aux columns | needs the `NoWrap` leg, a cube gate and aux columns (that is what the FIELDS octet paid for) |
| single-lane aliasing | none | lane 0 aliases on its own (`x` and `x + p`); only the lane-8 carry keeps the alias off the vector |

The deciding fact is the third row. A map key must be RANGE-BOUND IN CIRCUIT before its comparator
means anything, and `KeyLanes9`'s envelope is nine lookups and nothing else
(`KeyLanes9.canonicalKey9_iff_in_image` proves those two legs are EXACTLY the image). `FieldLanes9`
carries a `mod p` reduction it cannot move because it is welded to an ABI that has nothing to do
with a sort key. Both are injective; only one is cheap to force, and the names say which is which.

ⓘ `KeyLanes9`'s own §6 docblock says "There is no Rust twin of `keyToLanes9` yet". **That line is
STALE** — `commit/src/typed.rs::canonical_32_to_lanes_9` says in its own doc comment that it is
"The Rust mirror of `Dregg2.Circuit.KeyLanes9.keyToLanes9`", and there are three siblings. What
`KeyLanes9` lacked was an APPLIED emit face, and `Emit/KeyCanonicity9Emit.keyCanonical9At` was
written and wired to nothing. The stale line is corrected in that file by this change.

## Lane order: index 0 is the MOST significant

`keyToLanes9` is LITTLE-endian (lane 0 = the low base-`2^29` digit). Mathlib's `Pi.Lex` compares at
the SMALLEST differing index. So `canonKey9` REVERSES: `Digest9Key` index 0 carries lane 8. That
makes the lexicographic order on `Digest9Key` the numeric order of the key as a 256-bit integer,
which is what lets an honest producer sort a nullifier set by its bytes and get the committed IMT
chain. ⚠ Stated at its true resolution: the reversal is `rev9` and it is proved to be an
involution; the ORDER AGREEMENT with `keyWord` is exercised on concrete vectors in §5, not proved
in general — soundness of the tree never needs it, since an IMT needs only SOME linear order plus
injectivity, and both of those ARE proved here.

## What is FLOOR-FREE here and what is not

  * `canonKey9_injective`, `nine_lanes_admit_an_injection`, `leaf19Pre_injective`,
    `halfWide9_conflates_two_pointers` — **floor-free.** No hash, no CR, no ROM. Counting and a
    machine-checked left inverse.
  * A statement that the arity-19 *digest* separates addresses needs `hash` injective on the two
    named 19-felt preimages, i.e. the SAME per-instance non-collision side condition
    `MapOpWideKeyGate.imtLeafHash8Of_injective` carries. Nothing here upgrades that, and nothing
    here needs to: the refutation this file repairs was itself at the PREIMAGE level.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. No `sorry`, no `native_decide`.
-/
import Dregg2.Crypto.NonMembership
import Dregg2.Circuit.IndexedMerkleTree
import Dregg2.Circuit.KeyLanes9
import Mathlib.Order.PiLex

namespace Dregg2.Crypto.Digest9Key

open Dregg2.Crypto.NonMembership
open Dregg2.Circuit.IndexedMerkleTree (ImtLeaf ImtSorted ImtAbsent imtAddrs imtInsert
  imtAbsent_excludes imtInsert_preserves)
open Dregg2.Circuit.FieldLanes9 (P Byte Bytes32)
open Dregg2.Circuit.KeyLanes9 (keyToLanes9 keyToLanes9_lt_P keyToLanes9_injective
  keyLanes9ToBytes keyLanes9ToBytes_keyToLanes9 CanonicalKey9 canonicalKey9_of_encode
  canonicalKey9_iff_in_image)

set_option autoImplicit false
set_option linter.dupNamespace false

/-! ## §1 — the nine-felt key type, with its order wired from Mathlib. -/

/-- **`Digest9Key`** — the nine-felt key as a NON-MEMBERSHIP SORT KEY, under the LEXICOGRAPHIC
order. Index 0 is the most-significant lane (see the module doc's reversal note).

The bare product order on `Fin 9 → ℤ` is not linear — `product_order_incomparable` witnesses it —
so the key lives under `Lex`, exactly as `Digest8Key` does. -/
abbrev Digest9Key : Type := Lex (Fin 9 → ℤ)

/-- The `LinearOrder` is synthesized (`Pi.Lex.linearOrder`: `LinearOrder (Fin 9)` +
`WellFoundedLT (Fin 9)` + `LinearOrder ℤ`). Noncomputable, and irrelevantly so: the emitted AIR
implements the compare, Lean needs the ORDER only for the combinatorics. -/
noncomputable example : LinearOrder Digest9Key := inferInstance

example : DecidableEq Digest9Key := inferInstance

/-- **THE WRINKLE, witnessed at nine lanes** — the bare product order on `Fin 9 → ℤ` is NOT linear.
Restated rather than imported from the eight-lane file because the type is different and a reader
must not have to take it on faith that the obstruction survived the widening. -/
theorem product_order_incomparable :
    ∃ x y : Fin 9 → ℤ, ¬ x ≤ y ∧ ¬ y ≤ x := by
  refine ⟨(fun i => if i = 0 then 1 else 0), (fun i => if i = 1 then 1 else 0), ?_, ?_⟩
  · intro h; have := h 0; simp at this
  · intro h; have := h 1; simp at this

/-- …and `Lex` repairs exactly that pair, decided at index 0. -/
theorem lex_repairs_comparability :
    toLex (fun i : Fin 9 => if i = 1 then (1 : ℤ) else 0)
      < toLex (fun i : Fin 9 => if i = 0 then (1 : ℤ) else 0) := by
  refine ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), ?_⟩
  show (if (0 : Fin 9) = 1 then (1 : ℤ) else 0) < if (0 : Fin 9) = 0 then 1 else 0
  decide

/-! ## §2 — ★ THE CONSTRUCTED INJECTION: the exact negation of the arity-17 refutation.

`MapOpWideKeyPigeonhole.no_injection_bytes32_to_canonKey8` says every `Bytes32 → Fin 9 → Fin P`…
no. It says every `Bytes32 → (Fin 8 → Fin P)` fails. This section exhibits a `Bytes32 → (Fin 9 →
Fin P)` that SUCCEEDS, and it is a real encoder with a real decoder rather than a cardinality
shuffle — `Fintype.equivOfCardEq` would prove existence while producing a map no circuit can
compute. -/

/-- One canonical BabyBear felt, the same envelope `MapOpWideKeyPigeonhole.CanonFelt` names. -/
abbrev CanonFelt : Type := Fin P

/-- **The nine-lane canonical address slot** — what an arity-19 leaf can carry, at the deployed
envelope. Contrast `MapOpWideKeyPigeonhole.CanonKey8`, which is the same type one lane narrower and
is refuted. -/
abbrev CanonKey9 : Type := Fin 9 → CanonFelt

/-- Index reversal on `Fin 9`: little-endian lane `i` becomes lex index `8 - i`. -/
def rev9 (i : Fin 9) : Fin 9 := ⟨8 - i.1, by have := i.isLt; omega⟩

/-- `rev9` is an involution, so it is a bijection and reversing loses nothing. -/
theorem rev9_rev9 (i : Fin 9) : rev9 (rev9 i) = i := by
  apply Fin.ext; have := i.isLt; simp only [rev9]; omega

theorem rev9_injective : Function.Injective rev9 := by
  intro a b h
  have := congrArg rev9 h
  rwa [rev9_rev9, rev9_rev9] at this

/-- **THE ENCODER**, at the canonical envelope: 32 bytes → nine canonical felts, most-significant
lane first. The `Fin P` bound is `KeyLanes9.keyToLanes9_lt_P`, i.e. it is a THEOREM that this lands
in the envelope, not a truncation. -/
def canonKey9 (b : Bytes32) : CanonKey9 :=
  fun i => ⟨keyToLanes9 b (rev9 i), keyToLanes9_lt_P b (rev9 i)⟩

/-- **★ INJECTIVE.** The nine-lane address encoder separates every pair of distinct 32-byte
addresses. Not a hash bound, not a birthday bound — `KeyLanes9.keyToLanes9_injective`, which is
proved from a total decoder and a machine-checked left inverse, carried through the reversal. -/
theorem canonKey9_injective : Function.Injective canonKey9 := by
  intro a b h
  refine keyToLanes9_injective (funext fun i => ?_)
  have := congrFun h (rev9 i)
  have hv : keyToLanes9 a (rev9 (rev9 i)) = keyToLanes9 b (rev9 (rev9 i)) :=
    congrArg Fin.val this
  rwa [rev9_rev9] at hv

/-- **★ THE NEGATION OF THE REFUTATION, CONSTRUCTED.** Read this directly against
`MapOpWideKeyPigeonhole.no_injection_bytes32_to_canonKey8` (`∀ f : Bytes32 → CanonKey8, ¬
Injective f`): one lane up, the quantifier flips from a refuted `∀ ¬` to an inhabited `∃`, and the
witness is the encoder four Rust twins already compute. -/
theorem nine_lanes_admit_an_injection : ∃ f : Bytes32 → CanonKey9, Function.Injective f :=
  ⟨canonKey9, canonKey9_injective⟩

/-- **THE ROUND-TRIP** — the anti-vacuity that a difference-only test cannot fake. A scrambling
change to the encoder would still separate distinct keys; only a DECODER pins that the nine lanes
carry the address itself. `keyLanes9ToBytes` is total, and it is a left inverse here. -/
theorem canonKey9_round_trips (b : Bytes32) :
    keyLanes9ToBytes (fun i => (canonKey9 b (rev9 i)).1) = b := by
  have : (fun i => (canonKey9 b (rev9 i)).1) = keyToLanes9 b := by
    funext i; simp only [canonKey9, rev9_rev9]
  rw [this, keyLanes9ToBytes_keyToLanes9]

/-- The encoded lanes satisfy the emitted canonicity envelope — the COMPLETENESS pole, so the
range block the AIR will carry refuses no honest address. -/
theorem canonKey9_canonical (b : Bytes32) :
    CanonicalKey9 (fun i => (canonKey9 b (rev9 i)).1) := by
  have : (fun i => (canonKey9 b (rev9 i)).1) = keyToLanes9 b := by
    funext i; simp only [canonKey9, rev9_rev9]
  rw [this]; exact canonicalKey9_of_encode b

/-- The address as a `Digest9Key` — the sort key the IMT chain orders by. -/
def keyOf (b : Bytes32) : Digest9Key := toLex (fun i => ((canonKey9 b i : Fin P) : ℤ))

/-- **★ THE SORT KEY IS INJECTIVE.** Two distinct 32-byte addresses are two distinct points of the
committed order — which is precisely what the one-felt fold, and the eight-lane widening after it,
could not say. -/
theorem keyOf_injective : Function.Injective keyOf := by
  intro a b h
  refine canonKey9_injective (funext fun i => ?_)
  have hi := congrFun (congrArg ofLex h) i
  simp only [keyOf, ofLex_toLex] at hi
  exact Fin.ext (by exact_mod_cast hi)

#assert_axioms canonKey9_injective
#assert_axioms nine_lanes_admit_an_injection
#assert_axioms canonKey9_round_trips
#assert_axioms canonKey9_canonical
#assert_axioms keyOf_injective

/-! ## §3 — ★ THE ARITY-19 LEAF, and what it repairs.

`MapOpWideKeyPigeonhole.leaf17` absorbs `addr8 ‖ value ‖ next8` — nineteen felts short of nothing,
but eight lanes short of an address. This is the same schema one lane wider on each key half. -/

/-- The arity-19 leaf PREIMAGE: `addr9 ‖ value ‖ next9`. Nineteen felts. -/
def leaf19Pre (enc : Bytes32 → CanonKey9) (addr : Bytes32) (value : ℕ) (next : Bytes32) :
    List ℕ :=
  (List.ofFn fun i : Fin 9 => ((enc addr i : Fin P) : ℕ))
    ++ value :: (List.ofFn fun i : Fin 9 => ((enc next i : Fin P) : ℕ))

/-- The arity is 19, by `rfl` on the emitted list rather than by a comment. -/
theorem leaf19Pre_length (enc : Bytes32 → CanonKey9) (a : Bytes32) (v : ℕ) (n : Bytes32) :
    (leaf19Pre enc a v n).length = 19 := by
  simp [leaf19Pre]

/-- The arity-19 leaf digest, at an ARBITRARY hash and an arbitrary codomain. -/
def leaf19 {D : Type} (hash : List ℕ → D) (enc : Bytes32 → CanonKey9)
    (addr : Bytes32) (value : ℕ) (next : Bytes32) : D :=
  hash (leaf19Pre enc addr value next)

/-- **★ THE REPAIR, FLOOR-FREE — the arity-19 preimage SEPARATES what arity-17 conflates.**

Read against `MapOpWideKeyPigeonhole.arity17_conflates_two_addresses`, which produces two DISTINCT
addresses with an EQUAL preimage for every hash. Here, at the real nine-lane encoder, equal
preimages force equal addresses AND equal pointers. No collision-resistance hypothesis is used,
because the refutation it answers used none either — the conflation was in the ENCODING, and so is
the repair. -/
theorem leaf19Pre_injective {a b : Bytes32} {v w : ℕ} {m n : Bytes32}
    (h : leaf19Pre canonKey9 a v m = leaf19Pre canonKey9 b w n) :
    a = b ∧ v = w ∧ m = n := by
  have hlen : (List.ofFn fun i : Fin 9 => ((canonKey9 a i : Fin P) : ℕ)).length
      = (List.ofFn fun i : Fin 9 => ((canonKey9 b i : Fin P) : ℕ)).length := by simp
  obtain ⟨hA, hrest⟩ := List.append_inj h hlen
  have haddr : canonKey9 a = canonKey9 b := by
    have hf := List.ofFn_inj.mp hA
    funext i; exact Fin.ext (congrFun hf i)
  obtain ⟨hv, hN⟩ := List.cons.inj hrest
  refine ⟨canonKey9_injective haddr, hv, canonKey9_injective ?_⟩
  have hf := List.ofFn_inj.mp hN
  funext i; exact Fin.ext (congrFun hf i)

/-- …and therefore the arity-19 DIGEST separates them under exactly the per-instance
non-collision the eight-lane file already carried, and under nothing more. Stated with `hash`
injectivity as an explicit HYPOTHESIS rather than a floor, so a reader can see it is assumed. -/
theorem leaf19_separates {D : Type} (hash : List ℕ → D) (hinj : Function.Injective hash)
    {a b : Bytes32} {v w : ℕ} {m n : Bytes32}
    (h : leaf19 hash canonKey9 a v m = leaf19 hash canonKey9 b w n) :
    a = b ∧ v = w ∧ m = n :=
  leaf19Pre_injective (hinj h)

#assert_axioms leaf19Pre_length
#assert_axioms leaf19Pre_injective
#assert_axioms leaf19_separates

/-! ## §4 — ⚑ THE HALF-WIDENED STATE, REFUTED AT NINE LANES.

`MapOpWideKeyGate.halfWideLeaf_forges_absence_of_present` proves this at eight. It has to be
re-proved at NINE, because the theorem is about the SCHEMA, and a reader porting the tower one lane
up would otherwise be carrying a refutation of a schema nobody is about to build while the schema
they ARE about to build goes unrefuted.

The forgery: widen the ADDRESS to nine lanes, leave the POINTER projected to index 0. The honest
low leaf `⟨lowAddr, v, keyE⟩` and a FABRICATED `⟨lowAddr, v, ptrHi⟩` then absorb the SAME preimage
whenever `keyE` and `ptrHi` agree at index 0 — one edit arranges it — and the fabricated pointer
BRACKETS `keyE`, an address the honest chain PRESENTS. A present key certified absent. -/

/-- The half-widened preimage: address at all nine lanes, pointer projected to index 0. Arity 11. -/
def halfWide9Pre (enc : Bytes32 → CanonKey9) (addr : Bytes32) (value : ℕ) (next : Bytes32) :
    List ℕ :=
  (List.ofFn fun i : Fin 9 => ((enc addr i : Fin P) : ℕ))
    ++ [value, ((enc next 0 : Fin P) : ℕ)]

theorem halfWide9Pre_length (enc : Bytes32 → CanonKey9) (a : Bytes32) (v : ℕ) (n : Bytes32) :
    (halfWide9Pre enc a v n).length = 11 := by simp [halfWide9Pre]

/-- **★ THE HALF-WIDENED LEAF CONFLATES TWO POINTERS — for EVERY hash, no CR hypothesis.**

Any two pointers agreeing at index 0 give one preimage, hence one digest at every hash. The
hypothesis is exactly "the projection cannot tell them apart", which is one edit to a low byte. -/
theorem halfWide9_conflates_two_pointers {D : Type} (hash : List ℕ → D)
    (enc : Bytes32 → CanonKey9) (addr : Bytes32) (value : ℕ) {m n : Bytes32}
    (h0 : enc m 0 = enc n 0) :
    hash (halfWide9Pre enc addr value m) = hash (halfWide9Pre enc addr value n) := by
  simp only [halfWide9Pre, h0]

/-- …and the ARITY-19 schema separates the very same pair, provided they differ at all. This is the
pair of statements that makes "widen the key and the pointer TOGETHER" a theorem rather than a
style preference: the left one is available at the half-widened schema and the right one is not. -/
theorem full_wide_separates_what_half_wide_conflates {m n : Bytes32} (hmn : m ≠ n)
    (addr : Bytes32) (value : ℕ) :
    leaf19Pre canonKey9 addr value m ≠ leaf19Pre canonKey9 addr value n := by
  intro h
  exact hmn (leaf19Pre_injective h).2.2

#assert_axioms halfWide9Pre_length
#assert_axioms halfWide9_conflates_two_pointers
#assert_axioms full_wide_separates_what_half_wide_conflates

/-! ### §4-teeth — the forgery as a CONSTRUCTION at concrete nine-lane vectors.

Stated at the LANE level, which is the level the leaf absorbs and the comparator compares. The
three vectors below are the nine-lane analogue of the eight-lane exhibit in
`circuit/tests/mapabsent_key_width_tooth.rs::half_widening_conflates_the_pointer_and_forges_absence`,
and every compare below is `decide`d on `Fin 9 → ℤ` literals — there is no search and no branch. -/

/-- The honest low leaf's address: index 8 = 3, everything else zero. -/
def lowAddr9 : Digest9Key := toLex (fun i => if i = 8 then 3 else 0)
/-- The PRESENT address the forgery certifies absent: index 8 = 7. -/
def keyE9 : Digest9Key := toLex (fun i => if i = 8 then 7 else 0)
/-- The FABRICATED pointer: index 0 IDENTICAL to `keyE9` (both zero), strictly greater at index 7.
One edit, no search — the `O(1)` the theorem claims. -/
def ptrHi9 : Digest9Key := toLex (fun i => if i = 8 then 7 else if i = 7 then 8 else 0)

theorem lowAddr9_lt_keyE9 : lowAddr9 < keyE9 := by
  refine ⟨8, fun j hj => ?_, ?_⟩
  · have h8 : j ≠ 8 := Fin.ne_of_lt hj
    show (if j = 8 then (3 : ℤ) else 0) = if j = 8 then (7 : ℤ) else 0
    rw [if_neg h8, if_neg h8]
  · show (if (8 : Fin 9) = 8 then (3 : ℤ) else 0) < if (8 : Fin 9) = 8 then (7 : ℤ) else 0
    decide

/-- ⚑ The fabricated bracket is REAL and STRICT: it genuinely CONTAINS `keyE9`, which is what makes
the conflation a non-membership forgery rather than a curiosity. -/
theorem keyE9_lt_ptrHi9 : keyE9 < ptrHi9 := by
  refine ⟨7, fun j hj => ?_, ?_⟩
  · have h7 : j ≠ 7 := Fin.ne_of_lt hj
    have h8 : j ≠ 8 := Fin.ne_of_lt (lt_trans hj (by decide))
    show (if j = 8 then (7 : ℤ) else 0)
        = if j = 8 then (7 : ℤ) else if j = 7 then (8 : ℤ) else 0
    rw [if_neg h8, if_neg h8, if_neg h7]
  · show (if (7 : Fin 9) = 8 then (7 : ℤ) else 0)
        < if (7 : Fin 9) = 8 then (7 : ℤ) else if (7 : Fin 9) = 7 then (8 : ℤ) else 0
    decide

theorem lowAddr9_lt_ptrHi9 : lowAddr9 < ptrHi9 := lt_trans lowAddr9_lt_keyE9 keyE9_lt_ptrHi9

/-- **★ THE CONFLATION, at the concrete pair**: the fabricated pointer and the present address are
DISTINCT keys that the index-0 projection reads identically. -/
theorem ptrHi9_ne_keyE9_but_proj0_agrees :
    ptrHi9 ≠ keyE9 ∧ (ofLex ptrHi9) 0 = (ofLex keyE9) 0 := by
  refine ⟨fun h => ?_, ?_⟩
  · have hj := congrFun (congrArg ofLex h) 7
    simp only [ptrHi9, keyE9, ofLex_toLex] at hj
    exact absurd hj (by decide)
  · simp only [ptrHi9, keyE9, ofLex_toLex]
    decide

#assert_axioms lowAddr9_lt_keyE9
#assert_axioms keyE9_lt_ptrHi9
#assert_axioms ptrHi9_ne_keyE9_but_proj0_agrees

/-! ## §5 — THE KEYSTONES AT `Digest9Key`: direct instantiation, no twin.

`Crypto/NonMembership.sorted_gap_excludes` and `Circuit/IndexedMerkleTree`'s
`imtAbsent_excludes` / `imtInsert_preserves` are `[LinearOrder K]`-GENERIC. So the whole bracketing
core arrives at nine lanes by instantiation, exactly as it arrived at eight in
`Digest8KeySpike`. **Zero new bracketing math.** -/

#check @sorted_gap_excludes Digest9Key _

/-- The sorted-gap non-membership heart at the nine-felt lex key. -/
theorem sorted_gap_excludes_digest9 (leaves : List Digest9Key) (lo hi e : Digest9Key)
    (hsorted : Sorted leaves) (hadj : Adjacent leaves lo hi)
    (hlo : lo < e) (hhi : e < hi) : e ∉ leaves :=
  sorted_gap_excludes leaves lo hi e hsorted hadj hlo hhi

/-- **The nine-felt-key IMT pointer bracket** — the deployed generic keystone at the widened key. -/
theorem imtAbsent_excludes_digest9 {c : List (ImtLeaf Digest9Key ℤ)} (hs : ImtSorted c)
    {k : Digest9Key} (ha : ImtAbsent c k) : k ∉ imtAddrs c :=
  imtAbsent_excludes hs ha

/-- **The nine-felt-key insert preservation** — a bracketed insert keeps the chain `ImtSorted`. -/
theorem imtInsert_preserves_digest9 {c : List (ImtLeaf Digest9Key ℤ)} (hs : ImtSorted c)
    {k : Digest9Key} {v : ℤ} (ha : ImtAbsent c k) : ImtSorted (imtInsert c k v) :=
  imtInsert_preserves hs ha

/-! ### §5-teeth — a REAL nine-felt bracket, with the compares decided at DIFFERENT indices.

`lowAddr9 < keyE9` is decided at index 8 (the LAST lane) and `keyE9 < ptrHi9` at index 7. A
bracket that only ever separated at index 0 would be the one-felt gate wearing nine columns; these
do not. -/

/-- A one-leaf IMT chain over nine-felt keys. -/
def teethLeaf : ImtLeaf Digest9Key ℤ := ⟨lowAddr9, 7, ptrHi9⟩

theorem teethChain_sorted : ImtSorted [teethLeaf] := lowAddr9_lt_ptrHi9

/-- **★ NON-VACUITY — the instantiated keystone FIRES on a real nine-felt bracket.** -/
theorem teeth_imt_excluded : keyE9 ∉ imtAddrs [teethLeaf] :=
  imtAbsent_excludes_digest9 teethChain_sorted
    ⟨teethLeaf, by simp, lowAddr9_lt_keyE9, keyE9_lt_ptrHi9⟩

/-- **★ LIVENESS** — inserting the bracketed key PRESERVES sortedness at nine lanes. -/
theorem teeth_imt_insert_sorted : ImtSorted (imtInsert [teethLeaf] keyE9 (5 : ℤ)) :=
  imtInsert_preserves_digest9 teethChain_sorted
    ⟨teethLeaf, by simp, lowAddr9_lt_keyE9, keyE9_lt_ptrHi9⟩

/-- **DISCRIMINATION TOOTH** — the exclusion is not vacuous about everything: the genuine member
`lowAddr9` IS on the spine. Without this the theorem above is compatible with "nothing is ever
present". -/
theorem teeth_member : lowAddr9 ∈ imtAddrs [teethLeaf] := by simp [imtAddrs, teethLeaf]

#assert_axioms sorted_gap_excludes_digest9
#assert_axioms imtAbsent_excludes_digest9
#assert_axioms imtInsert_preserves_digest9
#assert_axioms teeth_imt_excluded
#assert_axioms teeth_imt_insert_sorted
#assert_axioms teeth_member

/-! ## §6 — THE VERDICT, in one proposition.

Stated together so a reader cannot take the pleasant half, and shaped to be read directly against
`MapOpWideKeyPigeonhole.schema_verdict`. -/

/-- **THE VERDICT.** (1) nine canonical lanes admit an injective encoding of 32 bytes — the exact
`∃` the eight-lane `∀ ¬` refuted; (2) it round-trips through a total decoder; (3) the arity-19
preimage separates addresses, values and pointers with no CR hypothesis; (4) the half-widened
schema does not, for every hash. -/
theorem digest9_verdict :
    (∃ f : Bytes32 → CanonKey9, Function.Injective f)
    ∧ (∀ b : Bytes32, keyLanes9ToBytes (fun i => (canonKey9 b (rev9 i)).1) = b)
    ∧ (∀ {a b : Bytes32} {v w : ℕ} {m n : Bytes32},
        leaf19Pre canonKey9 a v m = leaf19Pre canonKey9 b w n → a = b ∧ v = w ∧ m = n)
    ∧ (∀ {D : Type} (hash : List ℕ → D) (enc : Bytes32 → CanonKey9) (addr : Bytes32) (value : ℕ)
        (m n : Bytes32), enc m 0 = enc n 0 →
        hash (halfWide9Pre enc addr value m) = hash (halfWide9Pre enc addr value n)) :=
  ⟨nine_lanes_admit_an_injection, canonKey9_round_trips,
   fun h => leaf19Pre_injective h, fun hash enc addr value _m _n h0 =>
     halfWide9_conflates_two_pointers hash enc addr value h0⟩

#assert_axioms digest9_verdict

end Dregg2.Crypto.Digest9Key
