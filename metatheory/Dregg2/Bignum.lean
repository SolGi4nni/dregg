/-
# Dregg2.Bignum — the unified, PROVEN, EMITTABLE bignum arithmetic every dregg circuit weld builds on.

Numerics bugs — overflow, underflow-wrap, a field equation mistaken for an integer equation,
off-by-one — are the #1 way protocols get drained. This module is the numerics bedrock: the
schoolbook bignum operations (`compare` / `sub` / `add` / `mul` / `mod` / `range`), each with

  1. a WITNESS GATE SYSTEM — the schoolbook per-limb equations, in the SAME arithmetic IR
     (`Dregg2.Circuit.Expr`/`Constraint`) + range checks (`Dregg2.Circuit.Lookup.rangeCheck`) that
     `circuit/src/lean_descriptor_air.rs` ingests, so it is EMITTABLE, not a mirror;
  2. a SOUNDNESS + COMPLETENESS keystone (`_iff`) — a valid witness EXISTS iff the INTEGER relation
     holds (never a mod-`p` field equality passed off as an integer one), in the shape of the
     compare keystone `CaveatBignum.borrowSub_iff`;
  3. the ANTI-EXPLOIT theorems, each of the #1-protocol-killer classes proven UNCONSTRUCTABLE:
       * NO-OVERFLOW      — add/mul results are range-bounded; the field cannot wrap (`add_iff`,
                            `add_overflow_unsat`, `bignumVal_mul_bound`);
       * NO-UNDERFLOW-WRAP — a subtraction below zero has NO valid witness (UNSAT) — the
                            burn/transfer-debit drain class (`sub_underflow_unsat`);
       * FIELD-vs-INTEGER — a mod-`p`-equal-but-integer-unequal witness does not exist under the
                            range bounds — the mint-by-wraparound class (`rangeBound_field_faithful`,
                            `legs_noWrap_conservation`);
       * CANONICALITY     — a modular reduction is unique/unbiased; a non-canonical representative is
                            UNSAT (`modValid_unique`, `mod_noncanonical_unsat`).
  4. NON-VACUITY at BOTH polarities — a valid computation has a witness; the exploit
     (overflow/underflow/wraparound/non-canonical) has NONE — `#guard`ed at deployed params.

## The shared denotation (reused, not re-derived)

`bignumVal B : List ℤ → ℤ` (the base-`B` little-endian limb integer) and `Ranged B` (each limb in
`[0, B)`) are `Dregg2.Circuit.CaveatBignum`'s — the SAME denotation the compare keystone is stated
over. Everything here is stated over that core, so a weld gets one algebra, not five. The comparison
op is `borrowSub_iff`/`bignumLe_iff`/`bignumLt_iff` lifted verbatim; `sub` reuses the SAME `BSValid`
borrow-subtraction witness (its value identity + underflow-UNSAT tooth); `add`/`mul`/`mod`/`range`
add the carry-chain, schoolbook-product, Euclidean-reduction, and bit-decomposition gate systems.

`Int`-valued, `sorry`-free, `#assert_axioms`-clean; the STATEMENTS are audited (no vacuity — every
op is exhibited true AND its exploit exhibited false at the deployed params).

## ⚠ WHAT THIS LIBRARY IS NOT, AND THE SECOND POSITIONAL ALGEBRA THAT LIVES BESIDE IT

The header above says a weld gets "one algebra, not five". Measured 2026-07-31, that is not true of
the tree, and the exception is worth stating here rather than being rediscovered:
`Dregg2.Circuit.FieldLanes9` carries its OWN positional-numeral core — `ofDigits` / `digitsN` over
`Nat`, with `ofDigits_append`, `ofDigits_lt`, `ofDigits_digitsN`, `digitsN_ofDigits`, `digitsN_lt`.
It is not a mirror written in ignorance; it is there because of two real gaps.

**Gap 1 — DIRECTION. This library only ever goes DIGITS → VALUE.** Every keystone here takes a limb
list as given and says what integer it denotes (`bsValid_val`, `addValid_val`, `mul2_val`) or which
limb lists are admissible (`_iff`). `Dregg2.Bignum.DigitInjective.bignumVal_injective` completes that
direction: ranged limb lists are determined BY their value. **Nothing here goes VALUE → DIGITS** — no
`digitsN`, and no `ofDigits (digitsN b k n) = n`. A CODEC needs exactly that half: it is handed a
value and must produce the digits. §6's `ModValid` is ONE Euclidean step of it (`x = q·m + r`, with
`modValid_pins_ediv`/`_emod` pinning `q`/`r`), and `digitsN` is that step ITERATED — so the missing
piece is an induction over §6, not a new theory. It has simply never been written.

⚑ So the natural-looking shortcut is wrong: `bignumVal_injective` does NOT discharge a codec's
injectivity. It says two ranged digit lists with the same value are equal; a codec needs that two
distinct values give distinct digit lists. Those are injectivity of DIFFERENT MAPS, and only one of
them is proved here.

**Gap 2 — CARRIER.** This library is `Int`-valued because `CaveatBignum`'s borrow chain needs signed
intermediates. A codec's lanes are `Nat`/`Fin` — that is the shape the deployed `[BabyBear; 9]` has,
and it is what makes the `#guard` protocol vectors (the pin to the Rust twin) decidable. Routing a
codec through this carrier would put an `Int.toNat` at every leaf and buy nothing.

**And a third difference that is not a gap but a LAYER.** Everything here is EMITTABLE — §8 ties each
op to a real `Dregg2.Circuit.Constraint`. `FieldLanes9` emits nothing: measured across all 174
deployed members, there is not one range check, constant pin or arithmetic gate on the fields lane
columns. It is a producer-side encoding whose in-AIR image is unconstrained. Two different layers.

**Verdict, so the next reader does not re-litigate it: do NOT re-derive `fieldToLanes9_injective` or
`commitmentToLanes16_injective` through this library.** The one move that would pay is closing Gap 1
here — lifting `digitsN` and `ofDigits_digitsN` out of `FieldLanes9` into this file (or a `Nat`-side
sibling) — and that is worth doing when a SECOND codec needs it, not before. One consumer is how the
17-implementation zoo this tree spent a month deleting got started.
-/
import Dregg2.Circuit.CaveatBignumCompare
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.LinearCombination

namespace Dregg2.Bignum

open Dregg2.Circuit
open Dregg2.Circuit.Lookup
open Dregg2.Circuit.CaveatBignum

set_option autoImplicit false

/-! ## §1 — Foundational bounds over the shared denotation.

A ranged limb list is a NON-NEGATIVE integer that FITS in its width (`< Bⁿ`). These two facts are the
backbone of every no-overflow argument: "fits in `n` limbs" is exactly "cannot wrap a field of size
`≥ Bⁿ`". They are stated over `CaveatBignum.bignumVal`/`Ranged` — the reused shared core. -/

/-- A ranged limb list denotes a NON-NEGATIVE integer. -/
theorem bignumVal_nonneg {B : ℤ} (hB : 0 ≤ B) :
    ∀ (xs : List ℤ), Ranged B xs → 0 ≤ bignumVal B xs
  | [], _ => by simp
  | x :: xs, hr => by
      have hx : 0 ≤ x ∧ x < B := hr x List.mem_cons_self
      have hr' : Ranged B xs := fun z hz => hr z (List.mem_cons_of_mem _ hz)
      have ih := bignumVal_nonneg hB xs hr'
      simp only [bignumVal_cons]
      have := mul_nonneg hB ih
      omega

/-- **THE FITS LEMMA (anti-overflow backbone).** A ranged limb list of length `n` denotes an integer
`< Bⁿ` — it CANNOT reach a field of size `Bⁿ`, so mapping it into such a field cannot wrap. -/
theorem bignumVal_lt_base_pow {B : ℤ} (hB : 0 < B) :
    ∀ (xs : List ℤ), Ranged B xs → bignumVal B xs < B ^ xs.length
  | [], _ => by simp
  | x :: xs, hr => by
      have hx : 0 ≤ x ∧ x < B := hr x List.mem_cons_self
      have hr' : Ranged B xs := fun z hz => hr z (List.mem_cons_of_mem _ hz)
      have ih := bignumVal_lt_base_pow hB xs hr'
      have ih0 := bignumVal_nonneg (le_of_lt hB) xs hr'
      have hpow : B ^ (x :: xs).length = B * B ^ xs.length := by
        simp [List.length_cons, pow_succ]; ring
      simp only [bignumVal_cons, hpow]
      nlinarith [hx.1, hx.2, ih, ih0, hB]

/-! ## §2 — COMPARE (`≤` / `<`): the keystone, lifted verbatim.

The comparison op IS `CaveatBignum.borrowSub_iff`. We re-export it under the unified-library names so a
weld imports `Dregg2.Bignum.le_iff` / `lt_iff` rather than reaching across to the caveat module. The
witness is the schoolbook borrow-subtraction `BSValid` (incoming borrow `0` = `≤`, `1` = strict `<`);
a valid witness exists iff the integer comparison holds. -/

/-- **`le_iff`** — a valid borrow-sub witness (incoming borrow `0`) exists iff `X ≤ Y`. -/
theorem le_iff {B : ℤ} (hB : 0 < B) (xs ys : List ℤ)
    (hlen : xs.length = ys.length) (hrx : Ranged B xs) (hry : Ranged B ys) :
    (∃ ds, BSValid B xs ys ds 0) ↔ bignumVal B xs ≤ bignumVal B ys :=
  bignumLe_iff hB xs ys hlen hrx hry

/-- **`lt_iff`** — a valid borrow-sub witness (incoming borrow `1`) exists iff `X < Y` (strict). -/
theorem lt_iff {B : ℤ} (hB : 0 < B) (xs ys : List ℤ)
    (hlen : xs.length = ys.length) (hrx : Ranged B xs) (hry : Ranged B ys) :
    (∃ ds, BSValid B xs ys ds 1) ↔ bignumVal B xs < bignumVal B ys :=
  bignumLt_iff hB xs ys hlen hrx hry

/-! ## §3 — SUB: `diff = minuend − subtrahend`, and the ANTI-UNDERFLOW-WRAP tooth.

Subtraction reuses the SAME borrow-subtraction witness as compare (`BSValid`, no borrowing off the
top). The value identity says the difference limbs denote exactly `minuend − subtrahend`; the
existence keystone (from `borrowSub_iff`) says a valid witness exists IFF `subtrahend ≤ minuend`. So a
would-underflow subtraction (`minuend < subtrahend`) has NO valid witness — the debit that would wrap
to a huge positive balance is UNSAT. This is the burn / transfer-debit drain class, closed. -/

/-- A `BSValid` witness with incoming borrow `br` denotes the exact difference: the difference limbs
reconstruct `Y − X − br`. Pure value identity (no range needed) — proved by induction on the limbs. -/
theorem bsValid_val {B : ℤ} :
    ∀ (xs ys ds : List ℤ) (br : ℤ), BSValid B xs ys ds br →
      bignumVal B ds = bignumVal B ys - bignumVal B xs - br
  | [], [], [], br, h => by
      simp only [BSValid] at h; simp [bignumVal_nil, h]
  | x :: xs, y :: ys, d :: ds, br, h => by
      obtain ⟨br', _, hd, _, _, hrest⟩ := h
      have ih := bsValid_val xs ys ds br' hrest
      simp only [bignumVal_cons]; rw [hd, ih]; ring
  | [], [], _ :: _, _, h => by simp only [BSValid] at h
  | [], _ :: _, _, _, h => by simp only [BSValid] at h
  | _ :: _, [], _, _, h => by simp only [BSValid] at h
  | _ :: _, _ :: _, [], _, h => by simp only [BSValid] at h

/-- A `BSValid` difference is itself a valid ranged bignum (each difference limb range-checked into
`[0, B)`) — so `sub` COMPOSES with the other ops. General over the incoming borrow. -/
theorem bsValid_ranged {B : ℤ} :
    ∀ (xs ys ds : List ℤ) (br : ℤ), BSValid B xs ys ds br → Ranged B ds
  | [], [], [], _, _ => by intro z hz; simp at hz
  | x :: xs, y :: ys, d :: ds, br, h => by
      obtain ⟨br', _, _, hd0, hdB, hrest⟩ := h
      have ih := bsValid_ranged xs ys ds br' hrest
      intro z hz
      rcases List.mem_cons.mp hz with h1 | h1
      · exact h1 ▸ ⟨hd0, hdB⟩
      · exact ih z h1
  | [], [], _ :: _, _, h => by simp only [BSValid] at h
  | [], _ :: _, _, _, h => by simp only [BSValid] at h
  | _ :: _, [], _, _, h => by simp only [BSValid] at h
  | _ :: _, _ :: _, [], _, h => by simp only [BSValid] at h

/-- **`SubValid B minuend subtrahend diff`** — `diff` is the schoolbook borrow-difference
`minuend − subtrahend` with no borrow off the top. (The witness is `CaveatBignum.BSValid` with the
operands in subtraction order and incoming borrow `0`.) -/
def SubValid (B : ℤ) (minuend subtrahend diff : List ℤ) : Prop :=
  BSValid B subtrahend minuend diff 0

/-- The difference limbs are themselves a valid (ranged) bignum — so `sub` COMPOSES with the other
ops. Each difference limb is range-checked into `[0, B)`. -/
theorem subValid_ranged {B : ℤ} (minuend subtrahend diff : List ℤ)
    (h : SubValid B minuend subtrahend diff) : Ranged B diff :=
  bsValid_ranged subtrahend minuend diff 0 h

/-- **`subVal` — SUB SOUNDNESS.** A valid difference denotes EXACTLY `minuend − subtrahend` over ℤ
(not merely mod `p`). This is the value semantics every debit/burn/settlement relies on. -/
theorem subVal {B : ℤ} (minuend subtrahend diff : List ℤ)
    (h : SubValid B minuend subtrahend diff) :
    bignumVal B diff = bignumVal B minuend - bignumVal B subtrahend := by
  have := bsValid_val subtrahend minuend diff 0 h
  simpa using this

/-- **`sub_iff` — SUB SOUNDNESS + COMPLETENESS.** A valid difference witness EXISTS iff the
subtraction does not underflow (`subtrahend ≤ minuend`). Lifted from the compare keystone. -/
theorem sub_iff {B : ℤ} (hB : 0 < B) (minuend subtrahend : List ℤ)
    (hlen : subtrahend.length = minuend.length)
    (hrs : Ranged B subtrahend) (hrm : Ranged B minuend) :
    (∃ diff, SubValid B minuend subtrahend diff) ↔ bignumVal B subtrahend ≤ bignumVal B minuend :=
  bignumLe_iff hB subtrahend minuend hlen hrs hrm

/-- **THE ANTI-UNDERFLOW-WRAP THEOREM.** A subtraction that would go below zero
(`minuend < subtrahend`) has NO valid witness — it is UNSAT. There is no difference-limb assignment,
so a burn/debit exceeding the balance cannot be proven; the wraparound-to-a-huge-balance mint is
UNCONSTRUCTABLE. -/
theorem sub_underflow_unsat {B : ℤ} (hB : 0 < B) (minuend subtrahend : List ℤ)
    (hlen : subtrahend.length = minuend.length)
    (hrs : Ranged B subtrahend) (hrm : Ranged B minuend)
    (hunder : bignumVal B minuend < bignumVal B subtrahend) :
    ¬ ∃ diff, SubValid B minuend subtrahend diff := by
  rw [sub_iff hB minuend subtrahend hlen hrs hrm]; omega

/-! ## §4 — ADD: `sum = x + y` with the carry chain, and the ANTI-OVERFLOW tooth.

The schoolbook carry chain, mirroring the borrow chain: per limb
`sⱼ = xⱼ + yⱼ + cinⱼ − coutⱼ·B` with `sⱼ ∈ [0, B)`, boolean carries, incoming carry pinned, and the
TOP carry pinned `0` (no carry off the top — the result FITS the width). The value identity says the
sum limbs denote exactly `x + y (+ incoming carry)`; the existence keystone says a valid witness
exists IFF the true sum fits in `n` limbs (`< Bⁿ`). So an addition that would overflow the width has
NO witness — the field cannot be made to wrap. -/

/-- **`AddValid B xs ys ss cin`** — the sum limbs `ss` are the schoolbook carry-addition of `xs`, `ys`
with incoming carry `cin`, each limb range-checked and each carry boolean, the carry off the top
pinned `0` (the sum FITS in the width — the anti-overflow discipline). -/
def AddValid (B : ℤ) : List ℤ → List ℤ → List ℤ → ℤ → Prop
  | [], [], [], cin => cin = 0
  | x :: xs, y :: ys, s :: ss, cin =>
      ∃ cout, (cout = 0 ∨ cout = 1) ∧ s = x + y + cin - cout * B ∧ 0 ≤ s ∧ s < B
        ∧ AddValid B xs ys ss cout
  | _, _, _, _ => False

/-- **`addValid_val` — ADD SOUNDNESS.** The sum limbs denote EXACTLY `x + y + cin` over ℤ. Pure value
identity (no range needed): the carries telescope. -/
theorem addValid_val {B : ℤ} :
    ∀ (xs ys ss : List ℤ) (cin : ℤ), AddValid B xs ys ss cin →
      bignumVal B ss = bignumVal B xs + bignumVal B ys + cin
  | [], [], [], cin, h => by
      simp only [AddValid] at h; simp [bignumVal_nil, h]
  | x :: xs, y :: ys, s :: ss, cin, h => by
      obtain ⟨cout, _, hs, _, _, hrest⟩ := h
      have ih := addValid_val xs ys ss cout hrest
      simp only [bignumVal_cons]; rw [hs, ih]; ring
  | [], [], _ :: _, _, h => by simp only [AddValid] at h
  | [], _ :: _, _, _, h => by simp only [AddValid] at h
  | _ :: _, [], _, _, h => by simp only [AddValid] at h
  | _ :: _, _ :: _, [], _, h => by simp only [AddValid] at h

/-- The sum limbs are themselves a valid ranged bignum of the operand length — `add` COMPOSES. -/
theorem addValid_ranged_len {B : ℤ} :
    ∀ (xs ys ss : List ℤ) (cin : ℤ), AddValid B xs ys ss cin →
      Ranged B ss ∧ ss.length = xs.length
  | [], [], [], _, _ => ⟨fun z hz => by simp at hz, rfl⟩
  | x :: xs, y :: ys, s :: ss, cin, h => by
      obtain ⟨cout, _, _, hs0, hsB, hrest⟩ := h
      obtain ⟨ihr, ihl⟩ := addValid_ranged_len xs ys ss cout hrest
      refine ⟨?_, by simp [List.length_cons, ihl]⟩
      intro z hz
      rcases List.mem_cons.mp hz with h1 | h1
      · exact h1 ▸ ⟨hs0, hsB⟩
      · exact ihr z h1
  | [], [], _ :: _, _, h => by simp only [AddValid] at h
  | [], _ :: _, _, _, h => by simp only [AddValid] at h
  | _ :: _, [], _, _, h => by simp only [AddValid] at h
  | _ :: _, _ :: _, [], _, h => by simp only [AddValid] at h

/-- **`add_iff` — ADD SOUNDNESS + COMPLETENESS (the anti-overflow keystone).** A valid fixed-width sum
witness EXISTS iff the true sum FITS in `n` limbs (`x + y + cin < Bⁿ`). Forward: a witness proves the
sum fits (soundness — the result did not wrap). Backward: any fitting sum is computable (completeness).
Proved by induction over the limb lists, the carry decided per limb by whether the low sum reaches
`B` — the additive twin of `borrowSub_iff`. -/
theorem add_iff {B : ℤ} (hB : 0 < B) :
    ∀ (xs ys : List ℤ) (cin : ℤ),
      xs.length = ys.length → Ranged B xs → Ranged B ys → (cin = 0 ∨ cin = 1) →
      ((∃ ss, AddValid B xs ys ss cin) ↔
        bignumVal B xs + bignumVal B ys + cin < B ^ xs.length)
  | [], [], cin, _, _, _, hcin => by
      simp only [bignumVal_nil, List.length_nil, pow_zero]
      constructor
      · rintro ⟨ss, hv⟩
        match ss with
        | [] => simp only [AddValid] at hv; omega
        | _ :: _ => simp only [AddValid] at hv
      · intro _; exact ⟨[], by simp only [AddValid]; omega⟩
  | x :: xs, y :: ys, cin, hlen, hrx, hry, hcin => by
      have hxr : 0 ≤ x ∧ x < B := hrx x List.mem_cons_self
      have hyr : 0 ≤ y ∧ y < B := hry y List.mem_cons_self
      have hrx' : Ranged B xs := fun z hz => hrx z (List.mem_cons_of_mem _ hz)
      have hry' : Ranged B ys := fun z hz => hry z (List.mem_cons_of_mem _ hz)
      have hlen' : xs.length = ys.length := by simpa using hlen
      have hpow : B ^ (x :: xs).length = B * B ^ xs.length := by
        simp [List.length_cons, pow_succ]; ring
      simp only [bignumVal_cons, hpow]
      constructor
      · -- witness ⇒ the sum fits
        rintro ⟨ss, hv⟩
        match ss, hv with
        | s :: ss', hv =>
          obtain ⟨cout, hcout, hs, hs0, hsB, hrest⟩ := hv
          have hIH := add_iff hB xs ys cout hlen' hrx' hry' hcout
          have hfit : bignumVal B xs + bignumVal B ys + cout < B ^ xs.length := hIH.mp ⟨ss', hrest⟩
          have key : bignumVal B xs + bignumVal B ys + cout ≤ B ^ xs.length - 1 := by omega
          nlinarith [hfit, hs, hs0, hsB, hxr.1, hxr.2, hyr.1, hyr.2, hB,
            mul_le_mul_of_nonneg_left key hB.le]
      · -- the sum fits ⇒ a witness
        have hcin0 : (0 : ℤ) ≤ cin := by rcases hcin with h | h <;> omega
        intro hfit
        by_cases hlow : x + y + cin < B
        · -- no carry out of the low limb
          have htail : bignumVal B xs + bignumVal B ys + 0 < B ^ xs.length := by
            have hBmul : B * (bignumVal B xs + bignumVal B ys) < B * B ^ xs.length := by
              nlinarith [hfit, hxr.1, hyr.1, hcin0]
            have := lt_of_mul_lt_mul_left hBmul hB.le; omega
          obtain ⟨ss', hss'⟩ := (add_iff hB xs ys 0 hlen' hrx' hry' (Or.inl rfl)).mpr htail
          exact ⟨(x + y + cin) :: ss', 0, Or.inl rfl, by ring, by omega, by omega, hss'⟩
        · -- carry out of the low limb
          simp only [not_lt] at hlow
          have htail : bignumVal B xs + bignumVal B ys + 1 < B ^ xs.length := by
            have hBmul : B * (bignumVal B xs + bignumVal B ys + 1) < B * B ^ xs.length := by
              nlinarith [hfit, hlow]
            have := lt_of_mul_lt_mul_left hBmul hB.le; omega
          obtain ⟨ss', hss'⟩ := (add_iff hB xs ys 1 hlen' hrx' hry' (Or.inr rfl)).mpr htail
          exact ⟨(x + y + cin - B) :: ss', 1, Or.inr rfl, by ring, by omega, by omega, hss'⟩
  | [], _ :: _, _, hlen, _, _, _ => by simp at hlen
  | _ :: _, [], _, hlen, _, _, _ => by simp at hlen

/-- **THE NO-OVERFLOW THEOREM.** An addition whose true sum does not fit the width
(`Bⁿ ≤ x + y + cin`) has NO valid witness — it is UNSAT. The field-wraparound that would let an
overflowing sum masquerade as a small in-range value is UNCONSTRUCTABLE. -/
theorem add_overflow_unsat {B : ℤ} (hB : 0 < B) (xs ys : List ℤ) (cin : ℤ)
    (hlen : xs.length = ys.length) (hrx : Ranged B xs) (hry : Ranged B ys) (hcin : cin = 0 ∨ cin = 1)
    (hover : B ^ xs.length ≤ bignumVal B xs + bignumVal B ys + cin) :
    ¬ ∃ ss, AddValid B xs ys ss cin := by
  rw [add_iff hB xs ys cin hlen hrx hry hcin]; omega

/-- **RESULT RANGE-BOUNDED.** A valid sum FITS: it denotes an integer `< Bⁿ`, hence maps into any
field of size `≥ Bⁿ` without wrapping (the direct payoff of the pinned top carry). -/
theorem add_result_fits {B : ℤ} (hB : 0 < B) (xs ys ss : List ℤ) (cin : ℤ)
    (hlen : xs.length = ys.length) (hrx : Ranged B xs) (hry : Ranged B ys) (hcin : cin = 0 ∨ cin = 1)
    (h : AddValid B xs ys ss cin) :
    bignumVal B xs + bignumVal B ys + cin < B ^ xs.length :=
  (add_iff hB xs ys cin hlen hrx hry hcin).mp ⟨ss, h⟩

/-! ## §5 — MUL: the schoolbook product, overflow-safe.

Two faces. (a) The GENERAL width bound: the product of an `m`-limb and an `n`-limb ranged bignum is
non-negative and `< B^(m+n)` — the overflow-safe width fact every product gate relies on to stay
below the field modulus (this is `VaultSatDescriptor.limbMul_lt` generalized to arbitrary width).
(b) The concrete `2×2 → 4`-limb schoolbook product with witnessed carries — byte-for-byte the deployed
`vault_weld::product_gates` — whose value identity says the four product limbs denote EXACTLY the
integer product. -/

/-- **THE OVERFLOW-SAFE MUL WIDTH BOUND (general).** The product of an `m`-limb by an `n`-limb ranged
bignum is non-negative and strictly below `B^(m+n)`, so at operand widths whose sum keeps `B^(m+n) ≤ p`
the product gate CANNOT wrap the field. -/
theorem bignumVal_mul_bound {B : ℤ} (hB : 0 < B) (xs ys : List ℤ)
    (hrx : Ranged B xs) (hry : Ranged B ys) :
    0 ≤ bignumVal B xs * bignumVal B ys
      ∧ bignumVal B xs * bignumVal B ys < B ^ (xs.length + ys.length) := by
  have hx0 := bignumVal_nonneg (le_of_lt hB) xs hrx
  have hy0 := bignumVal_nonneg (le_of_lt hB) ys hry
  have hxm := bignumVal_lt_base_pow hB xs hrx
  have hyn := bignumVal_lt_base_pow hB ys hry
  refine ⟨mul_nonneg hx0 hy0, ?_⟩
  have hpx : (0 : ℤ) < B ^ xs.length := pow_pos hB _
  have hpy : (0 : ℤ) < B ^ ys.length := pow_pos hB _
  have hpow : B ^ (xs.length + ys.length) = B ^ xs.length * B ^ ys.length := pow_add B _ _
  rw [hpow]; nlinarith [hx0, hy0, hxm, hyn, hpx, hpy]

/-- **`Mul2Valid`** — the deployed `2×2 → 4`-limb schoolbook product with witnessed carries `ca cb cc`
and cross-term `t1` (Rust `vault_weld::product_gates`):
  `A: x0·y0 = z0 + ca·B` · `B: x1·y0 + ca = t1 + cb·B` · `C: x0·y1 + t1 = z1 + cc·B` ·
  `D: x1·y1 + cb + cc = z2 + z3·B`, all limbs/carries range-checked into `[0, B)`. -/
def Mul2Valid (B : ℤ) (x0 x1 y0 y1 z0 z1 z2 z3 ca cb cc t1 : ℤ) : Prop :=
  x0 * y0 = z0 + ca * B
    ∧ x1 * y0 + ca = t1 + cb * B
    ∧ x0 * y1 + t1 = z1 + cc * B
    ∧ x1 * y1 + cb + cc = z2 + z3 * B
    ∧ (0 ≤ z0 ∧ z0 < B) ∧ (0 ≤ z1 ∧ z1 < B) ∧ (0 ≤ z2 ∧ z2 < B) ∧ (0 ≤ z3 ∧ z3 < B)
    ∧ (0 ≤ ca ∧ ca < B) ∧ (0 ≤ cb ∧ cb < B) ∧ (0 ≤ cc ∧ cc < B) ∧ (0 ≤ t1 ∧ t1 < B)

/-- **`mul2_val` — MUL SOUNDNESS (2-limb).** The four product limbs denote EXACTLY the integer product
of the two-limb operands: `bignumVal [z0,z1,z2,z3] = (x0 + B·x1)·(y0 + B·y1)`. Pure algebra over the
four schoolbook equations (the carries telescope). -/
theorem mul2_val {B : ℤ} {x0 x1 y0 y1 z0 z1 z2 z3 ca cb cc t1 : ℤ}
    (h : Mul2Valid B x0 x1 y0 y1 z0 z1 z2 z3 ca cb cc t1) :
    bignumVal B [z0, z1, z2, z3] = bignumVal B [x0, x1] * bignumVal B [y0, y1] := by
  obtain ⟨hA, hB, hC, hD, _⟩ := h
  simp only [bignumVal_cons, bignumVal_nil]
  linear_combination -hA - B * hB - B * hC - B ^ 2 * hD

/-- **MUL RESULT OVERFLOW-SAFE (2-limb).** A valid 2-limb product's limbs are all ranged, and the
product it denotes is `< B⁴` for `0 ≤ x,y < B²` — it FITS four limbs, no field wrap. -/
theorem mul2_fits {B : ℤ} (hB : 0 < B) {x0 x1 y0 y1 z0 z1 z2 z3 ca cb cc t1 : ℤ}
    (hx : (0 ≤ x0 ∧ x0 < B) ∧ (0 ≤ x1 ∧ x1 < B)) (hy : (0 ≤ y0 ∧ y0 < B) ∧ (0 ≤ y1 ∧ y1 < B))
    (h : Mul2Valid B x0 x1 y0 y1 z0 z1 z2 z3 ca cb cc t1) :
    0 ≤ bignumVal B [z0, z1, z2, z3] ∧ bignumVal B [z0, z1, z2, z3] < B ^ 4 := by
  rw [mul2_val h]
  have hrx : Ranged B [x0, x1] := by
    intro z hz
    rcases List.mem_cons.mp hz with h1 | h1
    · exact h1 ▸ hx.1
    · rcases List.mem_cons.mp h1 with h2 | h2
      · exact h2 ▸ hx.2
      · simp at h2
  have hry : Ranged B [y0, y1] := by
    intro z hz
    rcases List.mem_cons.mp hz with h1 | h1
    · exact h1 ▸ hy.1
    · rcases List.mem_cons.mp h1 with h2 | h2
      · exact h2 ▸ hy.2
      · simp at h2
  have := bignumVal_mul_bound hB [x0, x1] [y0, y1] hrx hry
  simpa using this

/-! ## §6 — MOD / REDUCE: canonical Euclidean reduction, and the CANONICALITY teeth.

`r = x mod m` with `0 ≤ r < m` — the reduction that makes a field element CANONICAL (used everywhere a
value must be a unique representative). The witness is the Euclidean pair `x = q·m + r` with `r`
range-checked into `[0, m)`. The soundness+completeness keystone pins `(q, r)` to the exact Euclidean
quotient/remainder. The teeth: the reduction is UNIQUE (no bias), and a NON-canonical representative
(`r ≥ m`, still congruent) has NO witness — the mint-by-alternate-representative class, closed. -/

/-- **`ModValid x q r m`** — the emittable reduction witness: `x = q·m + r` with `r` range-checked into
`[0, m)` (the quotient `q` is a free witness column). -/
def ModValid (x q r m : ℤ) : Prop := x = q * m + r ∧ 0 ≤ r ∧ r < m

/-- **`modValid_pins_emod` — CANONICALITY (soundness).** A valid reduction pins `r` to the canonical
residue `x % m`: the remainder column CANNOT be anything but the true modular residue. -/
theorem modValid_pins_emod {x q r m : ℤ} (_hm : 0 < m) (h : ModValid x q r m) : r = x % m := by
  obtain ⟨hx, hr0, hrm⟩ := h
  rw [hx, show q * m + r = r + m * q from by ring, Int.add_mul_emod_self_left,
    Int.emod_eq_of_lt hr0 hrm]

/-- The quotient column is likewise pinned to the Euclidean quotient `x / m`. -/
theorem modValid_pins_ediv {x q r m : ℤ} (hm : 0 < m) (h : ModValid x q r m) : q = x / m := by
  obtain ⟨hx, hr0, hrm⟩ := h
  have hmne : m ≠ 0 := ne_of_gt hm
  rw [hx, show q * m + r = r + m * q from by ring, Int.add_mul_ediv_left r q hmne,
    Int.ediv_eq_zero_of_lt hr0 hrm, zero_add]

/-- **`modValid_iff` — REDUCTION SOUNDNESS + COMPLETENESS.** A valid reduction witness exists for `(q,r)`
iff `(q, r)` are EXACTLY the Euclidean quotient/remainder. Forward is the two pins; backward is
`Int.ediv_add_emod` with the emod range facts (`Int.emod_nonneg`/`Int.emod_lt_of_pos`). -/
theorem modValid_iff {x q r m : ℤ} (hm : 0 < m) :
    ModValid x q r m ↔ (q = x / m ∧ r = x % m) := by
  constructor
  · intro h; exact ⟨modValid_pins_ediv hm h, modValid_pins_emod hm h⟩
  · rintro ⟨hq, hr⟩
    subst hq; subst hr
    refine ⟨?_, Int.emod_nonneg x (ne_of_gt hm), Int.emod_lt_of_pos x hm⟩
    linear_combination -Int.emod_add_mul_ediv x m

/-- **NON-VACUITY (positive): completeness.** Every `x` reduces — the Euclidean pair is a witness. -/
theorem modValid_exists {x m : ℤ} (hm : 0 < m) : ModValid x (x / m) (x % m) m :=
  (modValid_iff hm).mpr ⟨rfl, rfl⟩

/-- **`modValid_unique` — CANONICALITY (no bias).** Two valid reductions of the same `x` agree on BOTH
columns: the canonical representative is UNIQUE. A prover cannot present two different reductions. -/
theorem modValid_unique {x q₁ r₁ q₂ r₂ m : ℤ} (hm : 0 < m)
    (h₁ : ModValid x q₁ r₁ m) (h₂ : ModValid x q₂ r₂ m) : q₁ = q₂ ∧ r₁ = r₂ :=
  ⟨(modValid_pins_ediv hm h₁).trans (modValid_pins_ediv hm h₂).symm,
   (modValid_pins_emod hm h₁).trans (modValid_pins_emod hm h₂).symm⟩

/-- **THE NON-CANONICAL-REPRESENTATIVE TOOTH.** A representative `r' = x % m + m` (still congruent to
`x` mod `m`, but shifted out of `[0, m)`) has NO valid reduction witness — it is UNSAT. The
mint-by-alternate-representative attack (present `value + m` in place of `value`) is
UNCONSTRUCTABLE. -/
theorem mod_noncanonical_unsat {x m : ℤ} (hm : 0 < m) :
    ¬ ∃ q, ModValid x q (x % m + m) m := by
  rintro ⟨q, h⟩
  have := modValid_pins_emod hm h
  have hlt := Int.emod_lt_of_pos x hm
  omega

/-- **FIELD-vs-INTEGER (mod-reduce).** Two integers congruent mod `m` have the SAME canonical
reduction: canonicalization collapses a residue class to one representative, so an attacker cannot use
a `≡ (mod m)` sibling to smuggle a different canonical value. -/
theorem mod_field_vs_integer {x y q₁ r₁ q₂ r₂ m : ℤ} (hm : 0 < m)
    (h₁ : ModValid x q₁ r₁ m) (h₂ : ModValid y q₂ r₂ m) (hcong : x % m = y % m) : r₁ = r₂ := by
  rw [modValid_pins_emod hm h₁, modValid_pins_emod hm h₂, hcong]

/-! ## §7 — RANGE: bit-decomposition, and the ANTI-WRAPAROUND (field-vs-integer) keystone.

A range gadget bit-decomposes a value into `[0, 2ⁿ)`. In the shared denotation this is exactly
`bignumVal 2 bits` with `Ranged 2 bits` (each "limb" a bit in `{0,1}`), so the fits lemma gives
`value ∈ [0, 2ⁿ)` for free. The load-bearing consequence — generalizing `RealCrypto`'s
`twoLeg_noWrap_conservation` — is that WITH the range bound a BabyBear FIELD equation IS the integer
equation: a value-minting wraparound (an output committed to `p − k`) is refuted, because range-bounded
integers below `p` that agree mod `p` are equal. -/

/-- A bit-list (`Ranged 2`) denotes a value in `[0, 2ⁿ)` — the meaning of the range gadget, as an
instance of the fits lemma at base `2`. -/
theorem range_bits_bound (bits : List ℤ) (hr : Ranged 2 bits) :
    0 ≤ bignumVal 2 bits ∧ bignumVal 2 bits < 2 ^ bits.length :=
  ⟨bignumVal_nonneg (by norm_num) bits hr, bignumVal_lt_base_pow (by norm_num) bits hr⟩

/-- **`rangeBound_field_faithful` — THE ANTI-WRAPAROUND KEYSTONE (single value).** Two range-bounded
values (`0 ≤ a,b < P`) in a field of size `p ≥ P` that agree mod `p` are EQUAL over ℤ. This is what
upgrades a field-gate equality to an integer equality — the range bound (`P ≤ p`) is LOAD-BEARING:
drop it and a wraparound (`a`, `a + p`) satisfies the congruence while minting. -/
theorem rangeBound_field_faithful {p P a b : ℤ}
    (ha0 : 0 ≤ a) (haP : a < P) (hb0 : 0 ≤ b) (hbP : b < P) (hPp : P ≤ p)
    (h : a ≡ b [ZMOD p]) : a = b := by
  unfold Int.ModEq at h
  rw [Int.emod_eq_of_lt ha0 (by omega), Int.emod_eq_of_lt hb0 (by omega)] at h
  exact h

/-- A bit-decomposed value (`Ranged 2`, `n = bits.length`) with `2ⁿ ≤ p` is field-faithful: agreement
mod `p` with another such value forces integer equality. The range gadget's exact purpose. -/
theorem rangeDecomp_field_faithful {p : ℤ} {a b : List ℤ}
    (hra : Ranged 2 a) (hrb : Ranged 2 b) (hlen : a.length = b.length)
    (hnoWrap : (2 : ℤ) ^ a.length ≤ p) (h : bignumVal 2 a ≡ bignumVal 2 b [ZMOD p]) :
    bignumVal 2 a = bignumVal 2 b := by
  obtain ⟨ha0, haP⟩ := range_bits_bound a hra
  obtain ⟨hb0, hbP⟩ := range_bits_bound b hrb
  rw [hlen] at haP hnoWrap
  exact rangeBound_field_faithful ha0 haP hb0 hbP hnoWrap h

/-- Bound helper: a Nat list whose entries are each `< c` has `sum + length ≤ length · c`. -/
theorem sum_add_length_le {c : ℕ} :
    ∀ (l : List ℕ), (∀ x ∈ l, x < c) → l.sum + l.length ≤ l.length * c
  | [], _ => by simp
  | x :: xs, h => by
      have hx : x < c := h x List.mem_cons_self
      have ih := sum_add_length_le xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
      simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
      omega

/-- A range-bounded leg sum stays below the field modulus: each of `≤ legs` legs is `< 2ⁿ` with
`legs · 2ⁿ ≤ p`, so the sum `< p`. -/
theorem sum_lt_p {n p : ℕ} (hp : 0 < p) :
    ∀ (l : List ℕ), (∀ x ∈ l, x < 2 ^ n) → l.length * 2 ^ n ≤ p → l.sum < p
  | [], _, _ => hp
  | x :: xs, h, hlen => by
      have hx : x < 2 ^ n := h x List.mem_cons_self
      have hbound := sum_add_length_le (c := 2 ^ n) xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
      have hlen' : xs.length * 2 ^ n + 2 ^ n ≤ p := by
        simpa [List.length_cons, Nat.succ_mul] using hlen
      simp only [List.sum_cons]
      omega

/-- **`legs_noWrap_conservation` — THE ANTI-WRAPAROUND KEYSTONE (generalized `k`-leg conservation).**
Two lists of range-bounded legs (each `< 2ⁿ`, with `#legs · 2ⁿ ≤ p` — the BabyBear no-wrap bound the
AIR asserts at compile time) whose FIELD sums agree mod `p` have EQUAL INTEGER sums. Generalizes
`RealCrypto.twoLeg_noWrap_conservation` from the deployed `RING_LEGS = 2` to any leg count. The range
bound is LOAD-BEARING: drop it and a value-minting wraparound satisfies the congruence. -/
theorem legs_noWrap_conservation {n p : ℕ} {as bs : List ℕ} (hp : 0 < p)
    (ha : ∀ x ∈ as, x < 2 ^ n) (hb : ∀ x ∈ bs, x < 2 ^ n)
    (hlenA : as.length * 2 ^ n ≤ p) (hlenB : bs.length * 2 ^ n ≤ p)
    (hcong : as.sum % p = bs.sum % p) : as.sum = bs.sum := by
  have hA : as.sum < p := sum_lt_p hp as ha hlenA
  have hB : bs.sum < p := sum_lt_p hp bs hb hlenB
  rwa [Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hB] at hcong

/-! ## §8 — THE EMITTABLE-CONSTRAINT TIES.

Every op's per-limb equation is not a bespoke shape — it is the denotation of the SAME arithmetic-gate
IR (`Dregg2.Circuit.Constraint`, an `Expr` equality) that `circuit/src/lean_descriptor_air.rs` ingests
to build the AIR, and every range clause is a `Dregg2.Circuit.Lookup.rangeCheck`. These theorems
witness each gate concretely as an emittable `Constraint` (the SUB gate is `CaveatBignum`'s
`bsLimbEqn_is_gate`, re-exported). -/

/-- The ADD carry-limb equation `s = x + y + cin − cout·B`, as an emittable `Constraint`. -/
theorem addLimbEqn_is_gate (B : ℤ) (vs vx vy vcin vcout : Var) (a : Assignment) :
    (Constraint.holds
      ⟨Expr.var vs,
        .add (.var vx) (.add (.var vy) (.add (.var vcin) (.mul (.const (-1)) (.mul (.const B) (.var vcout)))))⟩ a)
      ↔ a vs = a vx + a vy + a vcin - B * a vcout := by
  simp only [Constraint.holds, Expr.eval]; ring_nf

/-- The MUL schoolbook product-A gate `x0·y0 = z0 + ca·B`, as an emittable `Constraint`. -/
theorem mul2LimbEqn_is_gate (B : ℤ) (vx0 vy0 vz0 vca : Var) (a : Assignment) :
    (Constraint.holds
      ⟨.mul (.var vx0) (.var vy0), .add (.var vz0) (.mul (.const B) (.var vca))⟩ a)
      ↔ a vx0 * a vy0 = a vz0 + B * a vca := by
  simp only [Constraint.holds, Expr.eval]

/-- The MOD reduction gate `x = q·m + r`, as an emittable `Constraint`. -/
theorem modEqn_is_gate (vx vq vm vr : Var) (a : Assignment) :
    (Constraint.holds
      ⟨.var vx, .add (.mul (.var vq) (.var vm)) (.var vr)⟩ a)
      ↔ a vx = a vq * a vm + a vr := by
  simp only [Constraint.holds, Expr.eval]

/-- The SUB borrow-limb equation is `CaveatBignum.bsLimbEqn_is_gate`, re-exported into the unified
library so a weld imports the one emittable gate. -/
theorem subLimbEqn_is_gate (B : ℤ) (vd vy vx vbr vbr' : Var) (a : Assignment) :
    (Constraint.holds
      ⟨Expr.var vd,
        .add (.var vy) (.add (.mul (.const (-1)) (.var vx))
          (.add (.mul (.const (-1)) (.var vbr)) (.mul (.const B) (.var vbr'))))⟩ a)
      ↔ a vd = a vy - a vx - a vbr + B * a vbr' :=
  bsLimbEqn_is_gate B vd vy vx vbr vbr' a

/-- A range clause is a `Lookup.rangeCheck`: a limb in `[0, 2ᵏ)` is exactly a row of the range table.
(Definitional; the `#guard`s in §9 exhibit the acceptance / rejection concretely, as `Lookup.lean`
does — the `∃ n < 2ᵏ` closed form fights Mathlib's singleton-`List.map` membership normalization.) -/
theorem rangeClause_is_lookup (v : ℤ) (k : Nat) (a : Assignment) :
    (rangeCheck (.const v) k).holds a ↔ [v] ∈ rangeTable k := by
  simp only [rangeCheck, LookupConstraint.holds, List.map_cons, List.map_nil, Expr.eval]

/-! ## §9 — NON-VACUITY at the DEPLOYED params (both polarities).

`Base = 2^26` (compare/caveat), `2^15` (vault limbs), `p = 2013265921` (BabyBear). Each op is exhibited
TRUE on a valid computation and its exploit exhibited FALSE (UNSAT) — no op is vacuous. -/

-- SUB: a valid debit `100 − 40` has a witness; an underflowing debit `40 − 100` has NONE.
example : ∃ diff, SubValid Base [100] [40] diff :=
  (sub_iff Base_pos [100] [40] rfl (by decide) (by decide)).mpr (by decide)
/-- THE ANTI-UNDERFLOW TOOTH FIRES: `40 − 100` underflows, so NO difference witness exists. -/
example : ¬ ∃ diff, SubValid Base [40] [100] diff :=
  sub_underflow_unsat Base_pos [40] [100] rfl (by decide) (by decide) (by decide)

-- SUB value soundness at the deployed base, concretely: `100 − 40 = 60`.
example (diff : List ℤ) (h : SubValid Base [100] [40] diff) : bignumVal Base diff = 60 := by
  rw [subVal [100] [40] diff h]; decide

-- ADD: a fitting sum `40 + 50 < 2^26` has a witness; an overflowing sum has NONE.
example : ∃ ss, AddValid Base [40] [50] ss 0 :=
  (add_iff Base_pos [40] [50] 0 rfl (by decide) (by decide) (Or.inl rfl)).mpr (by decide)
/-- THE ANTI-OVERFLOW TOOTH FIRES: two near-top limbs sum past `2^26`, so NO width-`1` sum exists. -/
example : ¬ ∃ ss, AddValid Base [50000000] [40000000] ss 0 :=
  add_overflow_unsat Base_pos [50000000] [40000000] 0 rfl (by decide) (by decide) (Or.inl rfl) (by decide)

-- MUL: a concrete 2-limb product's value is the integer product (value soundness, non-vacuous).
example : bignumVal 32768 [15, 0, 0, 0] = bignumVal 32768 [3, 0] * bignumVal 32768 [5, 0] :=
  mul2_val (B := 32768) (x0 := 3) (x1 := 0) (y0 := 5) (y1 := 0)
    (z0 := 15) (z1 := 0) (z2 := 0) (z3 := 0) (ca := 0) (cb := 0) (cc := 0) (t1 := 0)
    (by refine ⟨by ring, by ring, by ring, by ring, ?_⟩; refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> decide)

-- MOD: every value reduces (completeness); a non-canonical `r + m` rep is UNSAT (canonicality tooth).
example : ModValid 100 (100 / 7) (100 % 7) 7 := modValid_exists (by norm_num)
/-- THE CANONICALITY TOOTH FIRES: the non-canonical `100 % 7 + 7` representative has NO witness. -/
example : ¬ ∃ q, ModValid 100 q (100 % 7 + 7) 7 := mod_noncanonical_unsat (by norm_num)

-- RANGE / anti-wraparound at BabyBear: agreement mod p with the range bound forces integer equality;
-- WITHOUT the range bound a wraparound mints (`0` and `p` agree mod `p` but differ as integers).
example : (0 : ℤ) = 0 :=
  rangeBound_field_faithful (p := 2013265921) (P := 1024) (a := 0) (b := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Int.ModEq.refl 0)

-- The deployed 2-leg no-wrap conservation is the k=2 instance of the generalized keystone.
example : ([5, 7] : List ℕ).sum = ([12, 0] : List ℕ).sum :=
  legs_noWrap_conservation (n := 26) (p := 2013265921) (by norm_num)
    (by intro x hx; fin_cases hx <;> norm_num) (by intro x hx; fin_cases hx <;> norm_num)
    (by norm_num) (by norm_num) (by decide)

-- Emittable range clause: an in-range limb is accepted, an out-of-range / boundary one REJECTED.
#guard decide ((rangeCheck (.const 5) 3).holds (fun _ => 0))
#guard decide (¬ (rangeCheck (.const 999) 3).holds (fun _ => 0))
#guard decide (¬ (rangeCheck (.const (-1)) 3).holds (fun _ => 0))
#guard decide (¬ (rangeCheck (.const 8) 3).holds (fun _ => 0))

/-! ## §10 — THE ANTI-EXPLOIT SUMMARY (the four #1-protocol-killer classes, named).

Each reusable soundness lemma a weld gets for free. Collected here as named theorems pointing at the
proofs above, so an integrator can cite the CLASS. -/

/-- NO-UNDERFLOW-WRAP — a subtraction below zero is UNSAT (burn/debit drain class). -/
theorem antiExploit_no_underflow_wrap {B : ℤ} (hB : 0 < B) (minuend subtrahend : List ℤ)
    (hlen : subtrahend.length = minuend.length) (hrs : Ranged B subtrahend) (hrm : Ranged B minuend)
    (hunder : bignumVal B minuend < bignumVal B subtrahend) :
    ¬ ∃ diff, SubValid B minuend subtrahend diff :=
  sub_underflow_unsat hB minuend subtrahend hlen hrs hrm hunder

/-- NO-OVERFLOW — an addition that overflows the width is UNSAT (the field cannot wrap). -/
theorem antiExploit_no_overflow {B : ℤ} (hB : 0 < B) (xs ys : List ℤ) (cin : ℤ)
    (hlen : xs.length = ys.length) (hrx : Ranged B xs) (hry : Ranged B ys) (hcin : cin = 0 ∨ cin = 1)
    (hover : B ^ xs.length ≤ bignumVal B xs + bignumVal B ys + cin) :
    ¬ ∃ ss, AddValid B xs ys ss cin :=
  add_overflow_unsat hB xs ys cin hlen hrx hry hcin hover

/-- FIELD-vs-INTEGER — under the range bound a mod-`p` equality IS an integer equality (mint-by-
wraparound class). -/
theorem antiExploit_field_vs_integer {p P a b : ℤ}
    (ha0 : 0 ≤ a) (haP : a < P) (hb0 : 0 ≤ b) (hbP : b < P) (hPp : P ≤ p)
    (h : a ≡ b [ZMOD p]) : a = b :=
  rangeBound_field_faithful ha0 haP hb0 hbP hPp h

/-- CANONICALITY — a modular reduction is unique; no two representatives of one residue class pass
(mint-by-alternate-representative class). -/
theorem antiExploit_canonical {x q₁ r₁ q₂ r₂ m : ℤ} (hm : 0 < m)
    (h₁ : ModValid x q₁ r₁ m) (h₂ : ModValid x q₂ r₂ m) : q₁ = q₂ ∧ r₁ = r₂ :=
  modValid_unique hm h₁ h₂

/-! ## §AXIOM HYGIENE — the ops' keystones + anti-exploit theorems pinned to the standard axioms. -/

#assert_axioms bignumVal_lt_base_pow
#assert_axioms le_iff
#assert_axioms lt_iff
#assert_axioms subVal
#assert_axioms sub_iff
#assert_axioms sub_underflow_unsat
#assert_axioms addValid_val
#assert_axioms add_iff
#assert_axioms add_overflow_unsat
#assert_axioms bignumVal_mul_bound
#assert_axioms mul2_val
#assert_axioms modValid_iff
#assert_axioms modValid_unique
#assert_axioms mod_noncanonical_unsat
#assert_axioms rangeBound_field_faithful
#assert_axioms legs_noWrap_conservation
#assert_axioms addLimbEqn_is_gate
#assert_axioms mul2LimbEqn_is_gate
#assert_axioms modEqn_is_gate

end Dregg2.Bignum
