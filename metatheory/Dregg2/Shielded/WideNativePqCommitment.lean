/-
# Dregg2.Shielded.WideNativePqCommitment

A faithful, wide, curve-free value-commitment *law surface* for the native-PQ
shielded path.  This file deliberately separates three things that the old
single-felt `value_link_binding` conflated:

1. the opening is serialized canonically, without reducing a `u64` modulo the
   BabyBear prime;
2. domain, version, purpose, and payload length are part of the transcript;
3. the commitment output has an exact sixteen-BabyBear-lane type wall.

The serialization facts below are theorems.  Collision resistance is not.
`NativePqWideHashSurface` only pins a hash implementation to the deployed
`babyBearD4W16` Poseidon2 parameter descriptor; equal commitments for distinct
openings are reduced to an explicit `HashCollision`.  A production theorem must
bound the probability of finding that collision through
`Crypto.FloorGames.HashCRHardQuant F Eff` with `Eff` named, or
`Crypto.RomQueryFloor.birthday_bound` (PROVED, query-counted), or a stronger
construction-specific QROM analysis.  ⚑ NOT through
`HashFloorHonesty.CollisionResistant`, which this line used to name: that was
the same floor at `⊤`, refuted for exactly the compressing realizations this
module is about, and DELETED 2026-07-28.  In particular, this module does NOT assume the false statement
that a compressing Poseidon sponge is injective.

The four 16-bit words are the canonical little-endian bignum representation of
a `u64`.  They reuse `Dregg2.Bignum`'s integer denotation and range predicate;
each word is strictly below BabyBear's modulus before it is cast into the field.
-/
import Dregg2.Bignum
import Dregg2.Circuit.BabyBearFriField
import Dregg2.Circuit.HashFloorHonesty

namespace Dregg2.Shielded.WideNativePqCommitment

open Dregg2.Circuit.CaveatBignum (Ranged bignumVal)
open Dregg2.Circuit.BabyBearFriField (BabyBear babyBearP)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2RealParams babyBearD4W16)

set_option autoImplicit false

/-! ## 1. Canonical `u64` words and the faithful opening preimage. -/

/-- A small limb is chosen well below BabyBear: `2^16 < p`. -/
def limbBase : Nat := 2 ^ 16

/-- One canonical 16-bit word. -/
abbrev Limb16 := Fin limbBase

/-- A `u64` represented by exactly four little-endian 16-bit words. -/
structure CanonicalU64 where
  limb0 : Limb16
  limb1 : Limb16
  limb2 : Limb16
  limb3 : Limb16
  deriving DecidableEq, Repr

namespace CanonicalU64

/-- The exact four-word bignum consumed by integer-faithful circuit gadgets. -/
def asBignum (x : CanonicalU64) : List Int :=
  [x.limb0.val, x.limb1.val, x.limb2.val, x.limb3.val]

@[simp] theorem asBignum_length (x : CanonicalU64) : x.asBignum.length = 4 := by
  simp [asBignum]

/-- Every word is canonical for base `2^16`; no limb is a field residue masquerading as an integer. -/
theorem asBignum_ranged (x : CanonicalU64) : Ranged (limbBase : Int) x.asBignum := by
  intro z hz
  simp [asBignum] at hz
  rcases hz with h | h | h | h
  · subst z
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast x.limb0.isLt⟩
  · subst z
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast x.limb1.isLt⟩
  · subst z
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast x.limb2.isLt⟩
  · subst z
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast x.limb3.isLt⟩

/-- Integer denotation of the little-endian words, using the shared bignum semantics. -/
def toInt (x : CanonicalU64) : Int := bignumVal (limbBase : Int) x.asBignum

/-- The four-word denotation is nonnegative. -/
theorem toInt_nonneg (x : CanonicalU64) : 0 <= x.toInt := by
  exact Dregg2.Bignum.bignumVal_nonneg (by norm_num [limbBase]) x.asBignum x.asBignum_ranged

/-- The four-word denotation fits exactly below `2^64`. -/
theorem toInt_lt_two_pow_64 (x : CanonicalU64) : x.toInt < (2 : Int) ^ 64 := by
  have h := Dregg2.Bignum.bignumVal_lt_base_pow
    (B := (limbBase : Int)) (by norm_num [limbBase]) x.asBignum x.asBignum_ranged
  simpa [toInt, asBignum_length, limbBase] using h

/-- The raw canonical words, without any field reduction. -/
def words (x : CanonicalU64) : List Nat :=
  [x.limb0.val, x.limb1.val, x.limb2.val, x.limb3.val]

theorem word_mem_lt (x : CanonicalU64) : ∀ z ∈ x.words, z < limbBase := by
  intro z hz
  simp [words] at hz
  rcases hz with h | h | h | h
  · exact h ▸ x.limb0.isLt
  · exact h ▸ x.limb1.isLt
  · exact h ▸ x.limb2.isLt
  · exact h ▸ x.limb3.isLt

theorem words_injective : Function.Injective words := by
  intro x y h
  cases x with
  | mk x0 x1 x2 x3 =>
    cases y with
    | mk y0 y1 y2 y3 =>
      simp [words] at h
      rcases h with ⟨h0, h1, h2, h3⟩
      have e0 : x0 = y0 := Fin.ext h0
      have e1 : x1 = y1 := Fin.ext h1
      have e2 : x2 = y2 := Fin.ext h2
      have e3 : x3 = y3 := Fin.ext h3
      cases e0; cases e1; cases e2; cases e3
      rfl

end CanonicalU64

/-- The hidden opening binds all three full-width `u64` values. -/
structure Opening where
  value : CanonicalU64
  asset : CanonicalU64
  randomness : CanonicalU64
  deriving DecidableEq, Repr

/-- The twelve canonical payload words: value, asset, then randomness. -/
def payload (o : Opening) : List Nat :=
  o.value.words ++ o.asset.words ++ o.randomness.words

@[simp] theorem payload_length (o : Opening) : (payload o).length = 12 := by
  simp [payload, CanonicalU64.words]

theorem payload_word_lt (o : Opening) : ∀ z ∈ payload o, z < limbBase := by
  intro z hz
  simp only [payload, List.mem_append] at hz
  rcases hz with (hv | ha) | hr
  · exact o.value.word_mem_lt z hv
  · exact o.asset.word_mem_lt z ha
  · exact o.randomness.word_mem_lt z hr

/-- The payload serializer is injective before hashing. -/
theorem payload_injective : Function.Injective payload := by
  intro x y h
  cases x with
  | mk xv xa xr =>
    cases y with
    | mk yv ya yr =>
      cases xv with
      | mk xv0 xv1 xv2 xv3 =>
        cases xa with
        | mk xa0 xa1 xa2 xa3 =>
          cases xr with
          | mk xr0 xr1 xr2 xr3 =>
            cases yv with
            | mk yv0 yv1 yv2 yv3 =>
              cases ya with
              | mk ya0 ya1 ya2 ya3 =>
                cases yr with
                | mk yr0 yr1 yr2 yr3 =>
                  simp [payload, CanonicalU64.words] at h
                  rcases h with
                    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
                  have e0 : xv0 = yv0 := Fin.ext h0
                  have e1 : xv1 = yv1 := Fin.ext h1
                  have e2 : xv2 = yv2 := Fin.ext h2
                  have e3 : xv3 = yv3 := Fin.ext h3
                  have e4 : xa0 = ya0 := Fin.ext h4
                  have e5 : xa1 = ya1 := Fin.ext h5
                  have e6 : xa2 = ya2 := Fin.ext h6
                  have e7 : xa3 = ya3 := Fin.ext h7
                  have e8 : xr0 = yr0 := Fin.ext h8
                  have e9 : xr1 = yr1 := Fin.ext h9
                  have e10 : xr2 = yr2 := Fin.ext h10
                  have e11 : xr3 = yr3 := Fin.ext h11
                  cases e0; cases e1; cases e2; cases e3
                  cases e4; cases e5; cases e6; cases e7
                  cases e8; cases e9; cases e10; cases e11
                  rfl

/-! ## 2. Domain-separated transcript. -/

/-- A commitment purpose is part of the transcript, so distinct protocols cannot replay a digest. -/
inductive Purpose where
  | valueBinding
  | noteLeaf
  | settlementJoin
  deriving DecidableEq, Repr

/-- Stable, distinct 16-bit purpose tags. -/
def Purpose.tag : Purpose -> Nat
  | .valueBinding => 1
  | .noteLeaf => 2
  | .settlementJoin => 3

theorem Purpose.tag_injective : Function.Injective Purpose.tag := by
  intro x y h
  cases x <;> cases y <;> simp_all [Purpose.tag]

/-- `DREGG-WIDE-PQ-V1` represented as fixed 16-bit protocol words. -/
def domainPrefix : List Nat := [0x4452, 0x4547, 0x4757, 0x5051]

/-- Domain || version || purpose || payload length || canonical payload. -/
def transcript (purpose : Purpose) (o : Opening) : List Nat :=
  domainPrefix ++ [1, purpose.tag, 12] ++ payload o

@[simp] theorem transcript_length (purpose : Purpose) (o : Opening) :
    (transcript purpose o).length = 19 := by
  simp [transcript, domainPrefix]

/-- The protocol domain is an actual prefix of every transcript, not out-of-band metadata. -/
theorem transcript_has_domain_prefix (purpose : Purpose) (o : Opening) :
    ∃ rest, transcript purpose o = domainPrefix ++ rest := by
  exact ⟨[1, purpose.tag, 12] ++ payload o, rfl⟩

/-- Every transcript word embeds into BabyBear without reduction. -/
theorem transcript_word_lt_limbBase (purpose : Purpose) (o : Opening) :
    ∀ x ∈ transcript purpose o, x < limbBase := by
  intro x hx
  simp only [transcript, List.mem_append] at hx
  rcases hx with (hd | hh) | hp
  · have hd' : x = 0x4452 ∨ x = 0x4547 ∨ x = 0x4757 ∨ x = 0x5051 := by
      simpa [domainPrefix] using hd
    rcases hd' with rfl | rfl | rfl | rfl <;> norm_num [limbBase]
  · have hh' : x = 1 ∨ x = purpose.tag ∨ x = 12 := by
      simpa using hh
    rcases hh' with rfl | hpurpose | rfl
    · norm_num [limbBase]
    · subst x
      cases purpose <;> norm_num [Purpose.tag, limbBase]
    · norm_num [limbBase]
  · exact payload_word_lt o x hp

/-- Purpose and complete opening are both recoverable from an equal canonical transcript. -/
theorem transcript_injective {p q : Purpose} {x y : Opening}
    (h : transcript p x = transcript q y) : p = q ∧ x = y := by
  have htail : [1, p.tag, 12] ++ payload x = [1, q.tag, 12] ++ payload y := by
    simpa [transcript, domainPrefix] using h
  simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at htail
  rcases htail with ⟨hp, hpayload⟩
  have hpq : p = q := Purpose.tag_injective hp
  subst q
  exact ⟨rfl, payload_injective hpayload⟩

/-! ## 3. Field embedding: the serializer itself has no `x` versus `x+p` alias. -/

/-- Cast a transcript word into the deployed BabyBear field. -/
noncomputable def wordToBabyBear (x : Nat) : BabyBear := x

/-- Nat cast into BabyBear is injective throughout the canonical 16-bit word range. -/
theorem wordToBabyBear_injective_below_limbBase {x y : Nat}
    (hx : x < limbBase) (hy : y < limbBase)
    (h : wordToBabyBear x = wordToBabyBear y) : x = y := by
  have hxp : x < babyBearP := hx.trans (by norm_num [limbBase, babyBearP])
  have hyp : y < babyBearP := hy.trans (by norm_num [limbBase, babyBearP])
  change (x : BabyBear) = (y : BabyBear) at h
  rw [← ZMod.val_natCast_of_lt hxp, ← ZMod.val_natCast_of_lt hyp, h]

/-- Field-level transcript absorbed by the real Poseidon surface. -/
noncomputable def fieldTranscript (purpose : Purpose) (o : Opening) : List BabyBear :=
  (transcript purpose o).map wordToBabyBear

/-- Equality after BabyBear casts still pins purpose and opening: no input word crossed `p`. -/
theorem fieldTranscript_injective {p q : Purpose} {x y : Opening}
    (h : fieldTranscript p x = fieldTranscript q y) : p = q ∧ x = y := by
  have map_inj : ∀ (as bs : List Nat),
      (∀ z ∈ as, z < limbBase) ->
      (∀ z ∈ bs, z < limbBase) ->
      as.map wordToBabyBear = bs.map wordToBabyBear -> as = bs := by
    intro as
    induction as with
    | nil =>
      intro bs _ _ hm
      cases bs <;> simp_all
    | cons a as ih =>
      intro bs ha hb hm
      cases bs with
      | nil => simp at hm
      | cons b bs =>
        simp only [List.map_cons, List.cons.injEq] at hm
        have hab : a = b := wordToBabyBear_injective_below_limbBase
          (ha a (by simp)) (hb b (by simp)) hm.1
        have hrest : as = bs := ih bs
          (fun z hz => ha z (by simp [hz]))
          (fun z hz => hb z (by simp [hz])) hm.2
        simp [hab, hrest]
  apply transcript_injective
  exact map_inj _ _ (transcript_word_lt_limbBase p x)
    (transcript_word_lt_limbBase q y) h

/-- Cross-protocol replay is structurally impossible before the hash collision question arises. -/
theorem cross_purpose_field_transcripts_ne {p q : Purpose} (hpq : p ≠ q) (x y : Opening) :
    fieldTranscript p x ≠ fieldTranscript q y := by
  intro h
  exact hpq (fieldTranscript_injective h).1

/-! ### Concrete hostile tooth: the exact old `x` / `x+p` collision. -/

/-- The old compatibility bridge's lossy scalar fold. -/
def oldSingleFeltTag (x : Nat) : Nat := x % babyBearP

def seven : CanonicalU64 :=
  ⟨⟨7, by norm_num [limbBase]⟩, ⟨0, by norm_num [limbBase]⟩,
    ⟨0, by norm_num [limbBase]⟩, ⟨0, by norm_num [limbBase]⟩⟩

/-- `7 + p = 0x78000008`, still a perfectly valid `u64`. -/
def sevenPlusBabyBearP : CanonicalU64 :=
  ⟨⟨8, by norm_num [limbBase]⟩, ⟨0x7800, by norm_num [limbBase]⟩,
    ⟨0, by norm_num [limbBase]⟩, ⟨0, by norm_num [limbBase]⟩⟩

theorem hostile_old_single_felt_alias :
    oldSingleFeltTag 7 = oldSingleFeltTag (7 + babyBearP) := by
  norm_num [oldSingleFeltTag, babyBearP]

theorem hostile_canonical_words_separate :
    seven.words ≠ sevenPlusBabyBearP.words := by
  decide

def hostileOpening : Opening := ⟨seven, seven, seven⟩
def hostileOpeningPlusP : Opening := ⟨sevenPlusBabyBearP, seven, seven⟩

theorem hostile_field_transcript_separates :
    fieldTranscript .valueBinding hostileOpening ≠
      fieldTranscript .valueBinding hostileOpeningPlusP := by
  intro h
  have := (fieldTranscript_injective h).2
  exact (by decide : hostileOpening ≠ hostileOpeningPlusP) this

#guard oldSingleFeltTag 7 == oldSingleFeltTag (7 + babyBearP)
#guard seven.words != sevenPlusBabyBearP.words

/-! ## 4. Sixteen-lane native-PQ output wall and honest collision reduction. -/

/-- Exact output-width wall.  Callers cannot accidentally substitute the old one-felt digest. -/
abbrev WideDigest := Fin 16 -> BabyBear

theorem wideDigest_lane_count : Fintype.card (Fin 16) = 16 := by decide

/-- Even the conservative accounting of 30 bits per canonical BabyBear lane exceeds 384 bits.
This is a TYPE/CAPACITY fact, not a claim that all bits are independent or that Poseidon CR is proved. -/
theorem wideDigest_nominal_capacity_ge_384 : 384 <= 16 * 30 := by norm_num

/-- A hash surface pinned to the deployed Poseidon2 parameter descriptor.  There is intentionally
no injectivity or collision-resistance field here. -/
structure NativePqWideHashSurface where
  hash : List BabyBear -> WideDigest
  params : Poseidon2RealParams
  params_are_real : params = babyBearD4W16

/-! ⚑ **`ComputationalBindingFloor` DELETED 2026-07-28 — the routing pin pointed at a REFUTED floor.**

It was `abbrev ComputationalBindingFloor (F : KeyedHashFamily) : Prop :=
HashFloorHonesty.CollisionResistant F`, introduced as "the only appropriate cryptographic floor for a
compressing realization … a routing pin, not an inhabitant or proof". Its own words name the defect:
that floor is `HashCRHardQuant F ⊤`, and `FloorGames.hashCRHardQuant_top_false_of_compressing` proves
it FALSE for exactly the COMPRESSING realizations the pin was pointing at. It had no Lean consumer in
the tree — pin and alias both, so deleting it costs no proof.

The appropriate floor for this file's wide Poseidon2 digest is `Crypto.RomQueryFloor.birthday_bound`
(PROVED, query-counted, no assumption) or `Crypto.FloorGames.HashCRHardQuant F Eff` with `Eff`
written down. `equivocation_reduces_to_hash_collision` below is unchanged and is the half this file
actually proves: it reduces equivocation to a genuine transcript collision and stops there, which was
always the honest boundary. -/

/-- Domain-separated wide commitment. -/
noncomputable def commit (S : NativePqWideHashSurface) (purpose : Purpose) (o : Opening) : WideDigest :=
  S.hash (fieldTranscript purpose o)

/-- The exact collision event a computational hash floor must bound. -/
def HashCollision (S : NativePqWideHashSurface)
    (a b : List BabyBear) : Prop := a ≠ b ∧ S.hash a = S.hash b

/-- **Faithful binding law.** Two distinct typed openings/purposes with the same digest produce a
genuine collision in the field transcript hash.  The structural half is proved; excluding the
collision is deliberately left to a proper computational CR theorem, never false injectivity. -/
theorem equivocation_reduces_to_hash_collision (S : NativePqWideHashSurface)
    {p q : Purpose} {x y : Opening} (hdiff : p ≠ q ∨ x ≠ y)
    (heq : commit S p x = commit S q y) :
    HashCollision S (fieldTranscript p x) (fieldTranscript q y) := by
  refine ⟨?_, heq⟩
  intro htranscript
  obtain ⟨hp, ho⟩ := fieldTranscript_injective htranscript
  exact hdiff.elim (fun h => h hp) (fun h => h ho)

/-! ## Axiom audit. -/

#assert_axioms CanonicalU64.asBignum_ranged
#assert_axioms CanonicalU64.toInt_lt_two_pow_64
#assert_axioms payload_injective
#assert_axioms transcript_has_domain_prefix
#assert_axioms transcript_injective
#assert_axioms fieldTranscript_injective
#assert_axioms cross_purpose_field_transcripts_ne
#assert_axioms hostile_old_single_felt_alias
#assert_axioms hostile_field_transcript_separates
#assert_axioms equivocation_reduces_to_hash_collision

end Dregg2.Shielded.WideNativePqCommitment
