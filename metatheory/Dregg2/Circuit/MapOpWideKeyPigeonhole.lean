/-
# Dregg2.Circuit.MapOpWideKeyPigeonhole — the ARITY-17 SCHEMA IS BELOW THE BAR AT ITS OWN
  CANONICALITY ENVELOPE, and the counting says so before a hash is named.

## Why this file exists

`MapOpWideKey` / `MapOpWideKeyGate` author the widened map-op node and the arity-17 IMT leaf
`addr8 ‖ value ‖ next8`, and they prove real things: `halfWideLeaf_forges_absence_of_present`
(widening the address while the pointer stays lane-0 is a NON-MEMBERSHIP FORGERY, floor-free) and
`wideLeaf_kills_the_pointer_forgery` (the arity-17 leaf kills it). Those are correct.

But the address slot they widen into is `Digest8Key = Lex (Fin 8 → ℤ)` — EIGHT lanes — and the
deployed canonicality envelope those same files consume is `MapOpWideKey.KeyCanon`:

    KeyCanon k := ∀ i : Fin 8, 0 ≤ k i ∧ k i < 2013265921

i.e. every lane is one BabyBear felt. **So the deployed arity-17 address slot holds `P^8` values
against a 32-byte address space of `2^256`, and `FieldLanes9.nine_lanes_is_the_minimum` already
proves `P^8 < 2^256`.** In the MODEL the lanes are unbounded `ℤ` and `imtLeafHash8_injective` is
true; at the ENVELOPE the model is evaluated at, it cannot be. That gap is the whole content of
this file, and it is stated as a REFUTATION rather than a caveat because the repo's own law is that
a documented wound is not a detected one.

## The precedent this is the second instance of

`circuit/src/exact_nullifier_aafi.rs` carries the first, as a deletion note dated 2026-07-31: an
8-lane Poseidon2-image containment for the fields octet "landed at a **2^92.7 COLLISION** … below
this tree's ~124-bit bar, because eight BabyBear lanes cannot carry 256 bits at all:
`8 · log₂ p = 247.26`. Pigeonhole." The repair was a NINTH lane
(`FieldLanes9.fieldToLanes9_injective`), and it cost the geometry flag day
`rotatedNumPreLimbs` 178 → 184. **The arity-17 map-leaf address is the same 8-lane move at a
different site**, and this file is the tooth that stops it being built green a second time.

## What is refuted, and what is not

  * REFUTED — `no_injection_bytes32_to_canonKey8`: NO function from 32-byte addresses into the
    arity-17 leaf's canonical 8-lane address slot is injective. Not "no known one": none exists.
  * REFUTED — `arity17_conflates_two_addresses`: hence the arity-17 leaf digest CONFLATES two
    distinct 32-byte addresses, **for every hash, at every codomain, with NO collision-resistance
    hypothesis** — the `MapOpWideKey.narrowLeaf_conflates` shape, one width up, and against the
    schema that file offers as the repair.
  * REFUTED — `no_injection_u64_to_canonFelt`: the arity-17 leaf's VALUE slot is ONE felt
    (`imtLeafHash8 hash addr value next` with `value : ℤ`), so it cannot injectively carry a `u64`
    either. **The arity-17 schema does not address the value aliasing at all** — the deployed
    `split_u64(v).0` keeps 30 bits, and the schema keeps ~30.9.
  * NOT refuted — anything in `MapOpWideKey`/`MapOpWideKeyGate`. Their statements quantify over
    `Digest8Key = Lex (Fin 8 → ℤ)` with UNBOUNDED lanes and are true there. This file does not
    contradict them; it prices the instance the deployment would use.
  * NOT a claim about a hash. Nothing here is a birthday bound or a floor. It is counting.

## The width that does work, and it is already on disk

`circuit/src/exact_nullifier_aafi.rs` commits an address as `tag ‖ raw_to_u16_le(raw)[16]` and a
value as `u64_to_u16_le(v)[4]` — sixteen and four `u16` limbs, each `< 2^16 ≪ p`, so the felt lift
is the identity and NOTHING reduces. `card_key16` and `card_value4` below are `2^256` and `2^64`
ON THE NOSE: the counting obstruction vanishes exactly at that shape, and `schema_verdict` states
the two schemas against each other in one proposition.

## Substrate
This is a MODEL/counting module. It authors no constraint, no gadget, no `air_accepts`. It names
the deployed envelope (`P`, `Bytes32`) and counts.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. No `sorry`, no `native_decide`.
No `Fintype.card` of a `Fin P`-indexed function type is ever EVALUATED — every cardinality goes
through `Fintype.card_fun` / `Fintype.card_fin` as a rewrite.
-/
import Dregg2.Circuit.FieldLanes9
import Dregg2.Tactics
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

namespace Dregg2.Circuit.MapOpWideKeyPigeonhole

open Dregg2.Circuit.FieldLanes9 (P Byte Bytes32 nine_lanes_is_the_minimum)

set_option autoImplicit false

/-! ## §1 — the two alphabets, and the deployed envelope named as a type. -/

/-- One BabyBear felt, as the deployed canonicality envelope pins it: `MapOpWideKey.KeyCanon`
requires `0 ≤ cell < 2013265921 = P` on every key cell, and `P` is `FieldLanes9.P`. -/
abbrev CanonFelt : Type := Fin P

/-- **The arity-17 leaf's ADDRESS slot, at the envelope.** `MapOpWideKey.imtLeafHash8` absorbs
`keyLanes addr` — eight lanes of a `Digest8Key` — and every consumer of the emitted compare
(`lexLt8_refines`) requires `KeyCanon` on all eight. So the address a deployed arity-17 leaf can
carry is exactly this type. -/
abbrev CanonKey8 : Type := Fin 8 → CanonFelt

/-- The `u16` limb of the DEPLOYED exact codec (`exact_nullifier_aafi::raw_to_u16_le`). -/
abbrev U16 : Type := Fin 65536

/-- **The exact codec's address slot**: sixteen `u16` limbs. -/
abbrev Key16 : Type := Fin 16 → U16

/-- **The exact codec's value slot**: four `u16` limbs (`u64_to_u16_le`). -/
abbrev Value4 : Type := Fin 4 → U16

/-- A `u64` note value, the thing both accumulators record. -/
abbrev U64 : Type := Fin (2 ^ 64)

/-! ## §2 — the cardinalities, as rewrites (nothing is enumerated). -/

/-- `256 ^ 32 = 2 ^ 256` — the byte count against the bit count, so the two sides of every
comparison below are stated in the SAME base and nothing is being read off a docstring. -/
theorem pow256_32 : (256 : ℕ) ^ 32 = 2 ^ 256 := by
  rw [show (256 : ℕ) ^ 32 = ((2 : ℕ) ^ 8) ^ 32 from rfl, ← pow_mul]

/-- `65536 ^ 16 = 2 ^ 256` — sixteen `u16` limbs land on the byte count EXACTLY. -/
theorem pow65536_16 : (65536 : ℕ) ^ 16 = 2 ^ 256 := by
  rw [show (65536 : ℕ) ^ 16 = ((2 : ℕ) ^ 16) ^ 16 from rfl, ← pow_mul]

/-- `65536 ^ 4 = 2 ^ 64` — four `u16` limbs land on a `u64` EXACTLY. -/
theorem pow65536_4 : (65536 : ℕ) ^ 4 = 2 ^ 64 := by
  rw [show (65536 : ℕ) ^ 4 = ((2 : ℕ) ^ 16) ^ 4 from rfl, ← pow_mul]

theorem card_bytes32 : Fintype.card Bytes32 = 2 ^ 256 := by
  have h : Fintype.card Bytes32 = 256 ^ 32 := by simp [Byte]
  rw [h, pow256_32]

theorem card_canonKey8 : Fintype.card CanonKey8 = P ^ 8 := by simp [CanonFelt]

theorem card_canonFelt : Fintype.card CanonFelt = P := Fintype.card_fin _

theorem card_u64 : Fintype.card U64 = 2 ^ 64 := Fintype.card_fin _

theorem card_key16 : Fintype.card Key16 = 2 ^ 256 := by
  have h : Fintype.card Key16 = 65536 ^ 16 := by simp [U16]
  rw [h, pow65536_16]

theorem card_value4 : Fintype.card Value4 = 2 ^ 64 := by
  have h : Fintype.card Value4 = 65536 ^ 4 := by simp [U16]
  rw [h, pow65536_4]

/-! ## §3 — ★ THE REFUTATIONS. -/

/-- **★ NO 8-LANE ADDRESS ENCODING IS INJECTIVE.** Not "none is known" — none exists. The
obstruction is `FieldLanes9.nine_lanes_is_the_minimum`'s `P ^ 8 < 2 ^ 256`, which this repo already
paid a geometry flag day for at the fields octet. Every arity-17 map-leaf address is an instance of
this `f`. -/
theorem no_injection_bytes32_to_canonKey8 (f : Bytes32 → CanonKey8) :
    ¬ Function.Injective f := by
  intro hf
  have hle : Fintype.card Bytes32 ≤ Fintype.card CanonKey8 := Fintype.card_le_of_injective f hf
  rw [card_bytes32, card_canonKey8] at hle
  exact absurd hle (not_le.mpr nine_lanes_is_the_minimum.1)

/-- **★ NOR IS THE ONE-FELT VALUE SLOT.** `imtLeafHash8 hash addr value next` gives the value ONE
felt. A `u64` note value does not fit: `P < 2 ^ 64`. So the arity-17 schema leaves A3 — the
`split_u64(v).0` 30-bit value aliasing — exactly where it found it, moving 30 bits to ~30.9. -/
theorem no_injection_u64_to_canonFelt (g : U64 → CanonFelt) : ¬ Function.Injective g := by
  intro hg
  have hle : Fintype.card U64 ≤ Fintype.card CanonFelt := Fintype.card_le_of_injective g hg
  rw [card_u64, card_canonFelt] at hle
  have : P < 2 ^ 64 := by norm_num [P]
  exact absurd hle (not_le.mpr this)

/-- The arity-17 leaf digest, written at the DEPLOYED envelope: the address and the pointer are
canonical 8-lane keys, the value is one felt, and the absorb is
`addr8 ‖ value ‖ next8` — `MapOpWideKey.imtLeafHash8`'s own preimage shape
(`imtLeafPre8`), with `Digest8Key` replaced by what a canonical row can actually hold. `hash` is
ARBITRARY, at an arbitrary codomain: no floor, no `Poseidon2SpongeCR`, no ROM. -/
def leaf17 {D : Type} (hash : List ℕ → D) (enc : Bytes32 → CanonKey8)
    (addr : Bytes32) (value : ℕ) (next : Bytes32) : D :=
  hash ((List.ofFn fun i : Fin 8 => ((enc addr i : Fin P) : ℕ))
        ++ value :: (List.ofFn fun i : Fin 8 => ((enc next i : Fin P) : ℕ)))

/-- **★ THE ARITY-17 LEAF CONFLATES TWO DISTINCT 32-BYTE ADDRESSES — FOR EVERY HASH.**
No collision-resistance hypothesis, no codomain hypothesis, no ROM: two distinct addresses share a
canonical 8-lane image by §3's counting, and the leaf then absorbs the identical preimage. This is
`MapOpWideKey.narrowLeaf_conflates`' shape one width up — and it is aimed at the schema that file
offers as the REPAIR, which is why it belongs beside it rather than in a doc comment. -/
theorem arity17_conflates_two_addresses {D : Type} (hash : List ℕ → D)
    (enc : Bytes32 → CanonKey8) (value : ℕ) (next : Bytes32) :
    ∃ a b : Bytes32, a ≠ b ∧
      leaf17 hash enc a value next = leaf17 hash enc b value next := by
  have hni := no_injection_bytes32_to_canonKey8 enc
  rw [Function.not_injective_iff] at hni
  obtain ⟨a, b, hab, hne⟩ := hni
  exact ⟨a, b, hne, by simp only [leaf17, hab]⟩

/-- **★ AND THE POINTER SLOT CONFLATES TOO** — which is the half that carries the absence bracket.
`MapOpWideKeyGate.halfWideLeaf_forges_absence_of_present` proves a lane-0 pointer forges a
non-membership; this says the 8-lane pointer is not a repair of that either, it is a wider version
of the same obstruction. Two distinct 32-byte POINTERS share a leaf digest, for every hash. -/
theorem arity17_conflates_two_pointers {D : Type} (hash : List ℕ → D)
    (enc : Bytes32 → CanonKey8) (addr : Bytes32) (value : ℕ) :
    ∃ m n : Bytes32, m ≠ n ∧
      leaf17 hash enc addr value m = leaf17 hash enc addr value n := by
  have hni := no_injection_bytes32_to_canonKey8 enc
  rw [Function.not_injective_iff] at hni
  obtain ⟨m, n, hmn, hne⟩ := hni
  exact ⟨m, n, hne, by simp only [leaf17, hmn]⟩

/-! ## §4 — the width that DOES work, and it is the one already on disk. -/

/-- **★ SIXTEEN `u16` LIMBS ARE EXACTLY 32 BYTES.** `2 ^ 256` on the nose — the counting
obstruction is not merely relieved, it vanishes. This is the alphabet the DEPLOYED
`exact_nullifier_aafi::raw_to_u16_le` already writes, and its felt lift is the identity because
every limb is `< 2 ^ 16 ≪ p`, so nothing reduces. -/
theorem u16_limbs_admit_a_bijection : ∃ f : Bytes32 → Key16, Function.Bijective f :=
  ⟨Fintype.equivOfCardEq (card_bytes32.trans card_key16.symm), Equiv.bijective _⟩

/-- **★ FOUR `u16` LIMBS ARE EXACTLY A `u64`** — `exact_nullifier_aafi::u64_to_u16_le`. The value
half of A3, closed by the same codec that closes the address half. -/
theorem value4_limbs_admit_a_bijection : ∃ g : U64 → Value4, Function.Bijective g :=
  ⟨Fintype.equivOfCardEq (card_u64.trans card_value4.symm), Equiv.bijective _⟩

/-- **★ `schema_verdict` — THE TWO SCHEMAS, PRICED AGAINST EACH OTHER IN ONE PROPOSITION.**

  (1) the arity-17 leaf's canonical 8-lane ADDRESS admits NO injective encoding of 32 bytes;
  (2) its one-felt VALUE admits NO injective encoding of a `u64`;
  (3) the deployed exact codec's sixteen `u16` limbs admit a BIJECTION with 32 bytes;
  (4) its four `u16` limbs admit a BIJECTION with a `u64`.

Read as a decision: `addr8 ‖ value ‖ next8` is not the schema — `addr16 ‖ value4 ‖ next16` at the
`u16` codec is, and `circuit/src/exact_nullifier_aafi.rs` already commits exactly that
(`FNI2 ‖ addr17 ‖ value4 ‖ next17`, tag-prefixed, digest in eight lanes). -/
theorem schema_verdict :
    (∀ f : Bytes32 → CanonKey8, ¬ Function.Injective f)
    ∧ (∀ g : U64 → CanonFelt, ¬ Function.Injective g)
    ∧ (∃ f : Bytes32 → Key16, Function.Bijective f)
    ∧ (∃ g : U64 → Value4, Function.Bijective g) :=
  ⟨no_injection_bytes32_to_canonKey8, no_injection_u64_to_canonFelt,
   u16_limbs_admit_a_bijection, value4_limbs_admit_a_bijection⟩

/-! ## §5 — NON-VACUITY: the refutations are not satisfied by an empty premise.

`arity17_conflates_two_addresses` would be uninteresting if `Bytes32` or `CanonKey8` were empty, or
if the two schemas happened to have the same size. They do not. -/

/-- The 8-lane slot is genuinely SMALLER, and by a stated factor's worth of room: it is strictly
below the 32-byte space and strictly below the 16-limb one, which are equal. -/
theorem the_gap_is_real :
    Fintype.card CanonKey8 < Fintype.card Bytes32
    ∧ Fintype.card Bytes32 = Fintype.card Key16
    ∧ Fintype.card CanonFelt < Fintype.card U64
    ∧ Fintype.card U64 = Fintype.card Value4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [card_canonKey8, card_bytes32]; exact nine_lanes_is_the_minimum.1
  · rw [card_bytes32, card_key16]
  · rw [card_canonFelt, card_u64]; norm_num [P]
  · rw [card_u64, card_value4]

/-- …and NINE lanes would clear the address obstruction, which is what the fields octet paid for
(`FieldLanes9.fieldToLanes9_injective`). Stated so the arity-17 reader can see the two live exits —
a ninth lane, or the `u16` codec — rather than concluding the site is unrepairable. -/
theorem nine_lanes_would_clear_it : (2 : ℕ) ^ 256 ≤ P ^ 9 := nine_lanes_is_the_minimum.2

/-! ## §6 — axiom hygiene. -/

#assert_axioms card_bytes32
#assert_axioms card_canonKey8
#assert_axioms card_key16
#assert_axioms card_value4
#assert_axioms no_injection_bytes32_to_canonKey8
#assert_axioms no_injection_u64_to_canonFelt
#assert_axioms arity17_conflates_two_addresses
#assert_axioms arity17_conflates_two_pointers
#assert_axioms u16_limbs_admit_a_bijection
#assert_axioms value4_limbs_admit_a_bijection
#assert_axioms schema_verdict
#assert_axioms the_gap_is_real
#assert_axioms nine_lanes_would_clear_it

end Dregg2.Circuit.MapOpWideKeyPigeonhole
