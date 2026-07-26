/-
# Market.PackedBookFamily — the Dark Bazaar order pack, PARAMETERIC in the family size.

`Market.DarkBazaarPrivateDescriptor` commits to four private orders by packing them into ONE
BabyBear felt as four base-128 digits, and proved that pack injective by writing the sum out
literally and handing eight bound hypotheses to `omega`.  That proof is why the family is stuck
at four: it is quadratic in the order count and says nothing at any other size.

This module is the size-generic replacement.  An order is `kind ∈ Fin K` (a one-hot
side × limit selector) plus `qty ∈ Fin (2^Q)`, so `orderCode = kind + K · qty` is exactly ONE
digit in base `radix K Q = K · 2^Q`.  A book is then a base-`radix` bignum and every claim about
it is a claim about `Dregg2.Circuit.CaveatBignum.bignumVal` — discharged once, by induction, in
`Dregg2.Bignum.DigitInjective`, at every width simultaneously.

Three things this buys that the enumerated proof could not:

  * **`packedValue_injective`** at ANY order count, ANY kind count, ANY quantity width.
  * **`feltValues_injective`** — the MULTI-FELT pack.  Once a book exceeds one felt (which is
    the entire reason the deployed family is `N=4`), the commitment carries a LIST of felts, and
    injectivity is the per-block keystone applied blockwise.  Nothing is enumerated.
  * **`feltValue_eq_zero_iff`** — the padding question, answered by proof rather than assumed:
    a felt is worth the all-padding constant `0` iff every order it carries IS the padding
    order.  A live order cannot alias the pad, at the PACKING layer.  (The HASH layer is a
    separate, computational, Poseidon-binding assumption and is not touched here.)

§7 records the MEASURED shape of the two families, including the two facts that decide whether a
game-sized Dark Bazaar can reuse the deployed commitment: how many felts the pack needs, and
whether the resulting hash preimage still fits one full-arity Poseidon2 permutation.  It does
not.  That is stated as a theorem, not a caveat.

`Int`-valued, no field wraparound in the model, `sorry`-free.
-/
import Dregg2.Bignum.DigitInjective
import Dregg2.Bignum
import Mathlib.Data.List.OfFn

namespace Market.PackedBookFamily

open Dregg2.Circuit.CaveatBignum (bignumVal Ranged bignumVal_nil bignumVal_cons)
open Dregg2.Bignum.DigitInjective

set_option autoImplicit false

/-! ## §1 — A size-generic private order and its single-digit code. -/

/-- One private order in a family with `K` one-hot kinds (side × limit) and `Q`-bit quantities. -/
structure Order (K Q : Nat) where
  kind : Fin K
  qty : Fin (2 ^ Q)
  deriving DecidableEq, Repr

/-- The digit radix: one order occupies exactly one base-`radix` digit. -/
def radix (K Q : Nat) : Nat := K * 2 ^ Q

/-- The order's digit, as a `Nat`. -/
def codeNat {K Q : Nat} (o : Order K Q) : Nat := o.kind.val + K * o.qty.val

/-- The order's digit, in the integer model the circuit IR evaluates over. -/
def code {K Q : Nat} (o : Order K Q) : Int := (codeNat o : Int)

/-- An inhabited kind forces a positive kind count. -/
theorem kindCount_pos {K Q : Nat} (o : Order K Q) : 0 < K :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) o.kind.isLt

theorem radix_pos {K Q : Nat} (hK : 0 < K) : 0 < radix K Q :=
  Nat.mul_pos hK (by positivity)

/-- Every order code is a legal base-`radix` digit.  Proved from the two `Fin` bounds; no case
analysis on `K` or `Q`. -/
theorem codeNat_lt {K Q : Nat} (o : Order K Q) : codeNat o < radix K Q := by
  have h1 : o.kind.val < K := o.kind.isLt
  have h2 : o.qty.val < 2 ^ Q := o.qty.isLt
  calc o.kind.val + K * o.qty.val
      < K + K * o.qty.val := by omega
    _ = K * (o.qty.val + 1) := by ring
    _ ≤ K * 2 ^ Q := Nat.mul_le_mul_left K (by omega)

theorem code_bounds {K Q : Nat} (o : Order K Q) :
    0 ≤ code o ∧ code o < (radix K Q : Int) := by
  refine ⟨Int.natCast_nonneg _, ?_⟩
  simp only [code]
  exact_mod_cast codeNat_lt o

/-- **The digit is faithful.**  `kind + K · qty` recovers both fields — it is base-`K` division
with remainder, not a lossy mix. -/
theorem code_injective {K Q : Nat} : Function.Injective (code (K := K) (Q := Q)) := by
  intro left right h
  have hnat : codeNat left = codeNat right := by
    have : (codeNat left : Int) = (codeNat right : Int) := h
    exact_mod_cast this
  have hK : 0 < K := kindCount_pos left
  have hkind : left.kind.val = right.kind.val := by
    have e1 : (left.kind.val + K * left.qty.val) % K = left.kind.val := by
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt left.kind.isLt
    have e2 : (right.kind.val + K * right.qty.val) % K = right.kind.val := by
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt right.kind.isLt
    rw [← e1, ← e2]
    simp only [codeNat] at hnat
    rw [hnat]
  have hqty : left.qty.val = right.qty.val := by
    simp only [codeNat, hkind] at hnat
    exact Nat.eq_of_mul_eq_mul_left hK (Nat.add_left_cancel hnat)
  cases left with
  | mk lk lq =>
    cases right with
    | mk rk rq =>
      simp only at hkind hqty
      cases Fin.ext hkind
      cases Fin.ext hqty
      rfl

/-! ## §2 — The positional-sum form agrees with the bignum denotation.

The deployed descriptor writes its pack as `Σ Bⁱ · codeᵢ`.  That is the SAME object as
`bignumVal B` of the code list — proved once, generically, so a descriptor written either way
inherits every bignum theorem without a per-size bridge. -/

private theorem list_smul_sum (B : Int) : ∀ l : List Int, B * l.sum = (l.map (fun x => B * x)).sum
  | [] => by simp
  | x :: xs => by
      simp only [List.sum_cons, List.map_cons, mul_add, list_smul_sum B xs]

/-- `bignumVal` IS the positional sum `Σ Bⁱ · fᵢ`, at every length. -/
theorem bignumVal_ofFn (B : Int) :
    ∀ (n : Nat) (f : Fin n → Int),
      bignumVal B (List.ofFn f) = (List.ofFn fun i : Fin n => B ^ i.val * f i).sum
  | 0, _ => by simp
  | (n + 1), f => by
      have ih := bignumVal_ofFn B n (fun i : Fin n => f i.succ)
      have hmul : B * (List.ofFn fun i : Fin n => B ^ i.val * f i.succ).sum
          = (List.ofFn fun i : Fin n => B ^ (i.val + 1) * f i.succ).sum := by
        rw [list_smul_sum, List.map_ofFn]
        exact congrArg List.sum (List.ofFn_inj.mpr (funext fun i => by
          simp only [Function.comp_apply]
          ring))
      rw [List.ofFn_succ, bignumVal_cons, ih, hmul, List.ofFn_succ, List.sum_cons]
      simp [Fin.val_succ]

/-! ## §3 — A book of `n` orders is one base-`radix` bignum. -/

/-- The book's digit list, little-endian in the slot index. -/
def codes {K Q n : Nat} (w : Fin n → Order K Q) : List Int := List.ofFn fun i => code (w i)

/-- The packed book: the base-`radix` integer the digit list denotes. -/
def packedValue {K Q n : Nat} (w : Fin n → Order K Q) : Int :=
  bignumVal (radix K Q : Int) (codes w)

@[simp] theorem codes_length {K Q n : Nat} (w : Fin n → Order K Q) : (codes w).length = n := by
  simp [codes]

theorem codes_ranged {K Q n : Nat} (w : Fin n → Order K Q) :
    Ranged (radix K Q : Int) (codes w) := by
  intro z hz
  simp only [codes, List.mem_ofFn] at hz
  obtain ⟨i, hi⟩ := hz
  exact hi ▸ code_bounds (w i)

/-- The packed book in positional form — the shape a descriptor's `Σ Bⁱ · ORDER_PACKᵢ` gate
emits.  Generic in `n`: nothing is written out. -/
theorem packedValue_positional {K Q n : Nat} (w : Fin n → Order K Q) :
    packedValue w =
      (List.ofFn fun i : Fin n => (radix K Q : Int) ^ i.val * code (w i)).sum := by
  simpa [packedValue, codes] using bignumVal_ofFn (radix K Q : Int) n (fun i => code (w i))

/-- **The pack loses no fixed-slot order information — at any size.**  One induction over the
limbs (`bignumVal_injective`) plus one `Fin`-indexed digit inversion (`code_injective`).  There
is no `omega` over enumerated bound hypotheses here, so this statement costs the same at `n = 4`
and at `n = 4096`. -/
theorem packedValue_injective {K Q n : Nat} (hK : 0 < K) {left right : Fin n → Order K Q}
    (hpack : packedValue left = packedValue right) : left = right := by
  have hlists : codes left = codes right :=
    bignumVal_injective (by exact_mod_cast radix_pos (Q := Q) hK) (codes left) (codes right)
      (by simp) (codes_ranged left) (codes_ranged right) hpack
  have hfun : (fun i => code (left i)) = fun i => code (right i) :=
    List.ofFn_inj.mp hlists
  funext i
  exact code_injective (congrFun hfun i)

/-! ## §4 — Padding: the pad order is the unique zero digit. -/

/-- The canonical padding order: kind `0`, quantity `0`.  A padded slot is a MEMBER of the order
domain, not a separate symbol — which is what makes "injective on the padded domain" the same
statement as "injective". -/
def padOrder {K Q : Nat} (hK : 0 < K) : Order K Q :=
  ⟨⟨0, hK⟩, ⟨0, by positivity⟩⟩

@[simp] theorem code_padOrder {K Q : Nat} (hK : 0 < K) : code (padOrder (K := K) (Q := Q) hK) = 0 := by
  simp [code, codeNat, padOrder]

/-- **Can a live order's digit collide with the padding constant?  NO.**  The pad is the ONLY
order whose digit is `0`; every live order (any nonzero kind, or any nonzero quantity) has a
strictly positive digit.  Answered by proof, not assumed. -/
theorem code_eq_zero_iff {K Q : Nat} (hK : 0 < K) (o : Order K Q) :
    code o = 0 ↔ o = padOrder hK := by
  constructor
  · intro h
    have : code o = code (padOrder (K := K) (Q := Q) hK) := by simp [h]
    exact code_injective this
  · intro h; simp [h]

/-! ## §5 — The MULTI-FELT pack: one felt per block of orders.

Past one felt the commitment is not a scalar.  A book is a rectangle `felts × perFelt`, each row
packed into its own base-`radix` felt, and the commitment absorbs the LIST of felts. -/

/-- A book laid out as `felts` blocks of `perFelt` orders. -/
structure ChunkedBook (K Q felts perFelt : Nat) where
  slots : Fin felts → Fin perFelt → Order K Q

/-- The digit list of one block. -/
def ChunkedBook.blockCodes {K Q felts perFelt : Nat}
    (b : ChunkedBook K Q felts perFelt) (j : Fin felts) : List Int :=
  codes (b.slots j)

/-- The felt each block packs to. -/
def ChunkedBook.feltValue {K Q felts perFelt : Nat}
    (b : ChunkedBook K Q felts perFelt) (j : Fin felts) : Int :=
  packedValue (b.slots j)

/-- The commitment payload: one felt per block. -/
def ChunkedBook.feltValues {K Q felts perFelt : Nat}
    (b : ChunkedBook K Q felts perFelt) : List Int :=
  List.ofFn b.feltValue

@[simp] theorem ChunkedBook.feltValues_length {K Q felts perFelt : Nat}
    (b : ChunkedBook K Q felts perFelt) : b.feltValues.length = felts := by
  simp [ChunkedBook.feltValues]

/-- **The multi-felt pack is injective on the padded domain.**  Every slot of the rectangle is
a member of the order domain (pads included), so this is injectivity outright: two books with
the same felt list are the same book.  Blockwise `bignumVal_injective`; the felt COUNT is never
enumerated. -/
theorem ChunkedBook.feltValues_injective {K Q felts perFelt : Nat} (hK : 0 < K)
    {left right : ChunkedBook K Q felts perFelt}
    (h : left.feltValues = right.feltValues) : left = right := by
  have hfelt : left.feltValue = right.feltValue :=
    List.ofFn_inj.mp (by simpa [ChunkedBook.feltValues] using h)
  have hslots : left.slots = right.slots := by
    funext j
    exact packedValue_injective hK (congrFun hfelt j)
  cases left; cases right
  simp_all

/-- Each felt is a `perFelt`-digit base-`radix` number, hence strictly below `radix ^ perFelt`.
This is the FELT-FIT side condition: the family is legal exactly when `radix ^ perFelt` does not
exceed the field. -/
theorem ChunkedBook.feltValue_bounds {K Q felts perFelt : Nat} (hK : 0 < K)
    (b : ChunkedBook K Q felts perFelt) (j : Fin felts) :
    0 ≤ b.feltValue j ∧ b.feltValue j < (radix K Q : Int) ^ perFelt := by
  have hpos : (0 : Int) < (radix K Q : Int) := by exact_mod_cast radix_pos (Q := Q) hK
  refine ⟨Dregg2.Bignum.bignumVal_nonneg (le_of_lt hpos) _ (codes_ranged _), ?_⟩
  have hlt := Dregg2.Bignum.bignumVal_lt_base_pow hpos (codes (b.slots j)) (codes_ranged _)
  simpa [ChunkedBook.feltValue, packedValue, codes_length] using hlt

/-- **The padding question at the felt layer.**  A felt equals the all-padding constant `0` iff
every order in its block IS the pad.  So a block carrying any live order cannot be mistaken for
an empty block, and a verifier that treats a zero felt as "no orders here" is not being fooled —
at the PACKING layer.  (Whether the HASH can be fooled is Poseidon binding, elsewhere.) -/
theorem ChunkedBook.feltValue_eq_zero_iff {K Q felts perFelt : Nat} (hK : 0 < K)
    (b : ChunkedBook K Q felts perFelt) (j : Fin felts) :
    b.feltValue j = 0 ↔ ∀ t, b.slots j t = padOrder hK := by
  have hpos : (0 : Int) < (radix K Q : Int) := by exact_mod_cast radix_pos (Q := Q) hK
  rw [ChunkedBook.feltValue, packedValue,
    bignumVal_eq_zero_iff hpos (codes (b.slots j)) (codes_ranged _)]
  constructor
  · intro h t
    have hmem : code (b.slots j t) ∈ codes (b.slots j) := by
      simp only [codes, List.mem_ofFn]
      exact ⟨t, rfl⟩
    exact (code_eq_zero_iff hK _).mp (h _ hmem)
  · intro h z hz
    simp only [codes, List.mem_ofFn] at hz
    obtain ⟨t, ht⟩ := hz
    rw [← ht, h t, code_padOrder]

/-! ## §6 — The DEPLOYED n4k4 family, recovered as an instance.

`K = 8` (bid/ask × four limits), `Q = 4` (quantities `< 16`), so `radix = 128` and four orders
pack into `128^4 = 2^28`, comfortably inside BabyBear.  This is the family
`Market.DarkBazaarPrivateDescriptor` emits; the numbers below are its constants, re-derived here
from the parameters rather than asserted. -/

/-- BabyBear, the deployed field. -/
def BABYBEAR : Nat := 2013265921

abbrev N4K4Order := Order 8 4

theorem n4k4_radix : radix 8 4 = 128 := by decide

/-- Four orders fit ONE felt: `128^4 = 2^28 < 2^31`. -/
theorem n4k4_one_felt : radix 8 4 ^ 4 < BABYBEAR := by decide

/-- And FIVE would not have: `128^5 = 2^35` overflows BabyBear.  `ORDER_COUNT = 4` is a felt-width
artifact, and this is the exact inequality that pins it. -/
theorem n4k4_five_overflow : BABYBEAR < radix 8 4 ^ 5 := by decide

/-! ## §7 — The GAME-SIZED family, and the two facts that decide its shape.

`ORDER_COUNT = 16`, `PRICE_COUNT = 8` (so `K = 16`: bid/ask × eight limits), `Q = 8`
(quantities `< 256`).  One order is `radix = 16 · 256 = 4096 = 2^12` — twelve bits, not the
thirteen a side-plus-eight-buckets estimate suggests, because the side bit is already inside the
sixteen-way one-hot kind.  Sixteen orders are therefore 192 bits. -/

abbrev G16K8Order := Order 16 8

theorem g16k8_radix : radix 16 8 = 4096 := by decide

/-- **MEASURED, not estimated: TWO orders per felt, not three.**  `4096^2 = 2^24` fits BabyBear;
`4096^3 = 2^36` does not.  So a sixteen-order book is EIGHT felts on whole-order alignment — not
the seven a `192 / 31` information-theoretic estimate gives.  Recovering that eighth felt would
require an order to STRADDLE a felt boundary, which is a base-change argument this module does
not make and which is therefore NOT proven. -/
theorem g16k8_two_per_felt : radix 16 8 ^ 2 < BABYBEAR := by decide

theorem g16k8_three_per_felt_overflows : BABYBEAR < radix 16 8 ^ 3 := by decide

/-- The game-sized book: eight felts of two orders. -/
abbrev G16K8Book := ChunkedBook 16 8 8 2

/-- The game-sized pack IS injective on the padded domain. -/
theorem g16k8_injective {left right : G16K8Book}
    (h : left.feltValues = right.feltValues) : left = right :=
  ChunkedBook.feltValues_injective (by decide) h

/-- Every game-sized felt is a legal BabyBear element. -/
theorem g16k8_felt_in_field (b : G16K8Book) (j : Fin 8) :
    0 ≤ b.feltValue j ∧ b.feltValue j < (BABYBEAR : Int) := by
  obtain ⟨h0, hlt⟩ := ChunkedBook.feltValue_bounds (by decide) b j
  refine ⟨h0, lt_of_lt_of_le hlt ?_⟩
  norm_num [radix, BABYBEAR]

/-- A game-sized felt is the padding constant iff both its orders are pads. -/
theorem g16k8_pad_exact (b : G16K8Book) (j : Fin 8) :
    b.feltValue j = 0 ↔ ∀ t, b.slots j t = padOrder (by decide : 0 < 16) :=
  ChunkedBook.feltValue_eq_zero_iff (by decide) b j

/-! ### §7.1 — The commitment does NOT fit the deployed permutation.

`Market.DarkBazaarPrivateDescriptor` absorbs its whole source in ONE full-arity Poseidon2
permutation: `[tag, session, rule, packedBook] ++ blinding(8) ++ [0,0,0,0]` — twelve meaningful
inputs, four zero framing lanes, arity sixteen exactly.  Swap the single `packedBook` felt for a
list of eight and the preimage is nineteen felts.  Sixteen is the whole permutation.

This is a STRUCTURAL blocker on reusing the deployed commitment at game size, not a tuning knob:
the blind budget is already at eight and the header is three.  A game-sized family needs a
sponge (two or more permutations) or a different absorb schedule, and that changes the binding
argument — so the game-sized family is NOT a drop-in and must not be advertised as one. -/

/-- The deployed preimage arity. -/
def POSEIDON2_ARITY : Nat := 16

/-- Header (`tag`, `session`, `rule`) + one felt per pack block + eight blind limbs. -/
def preimageLen (packFelts blindLimbs : Nat) : Nat := 3 + packFelts + blindLimbs

/-- The DEPLOYED n4k4 preimage fits exactly, with four zero framing lanes to spare. -/
theorem n4k4_preimage_fits : preimageLen 1 8 + 4 = POSEIDON2_ARITY := by decide

/-- **The game-sized preimage does NOT fit.**  Nineteen felts into a sixteen-lane permutation. -/
theorem g16k8_preimage_overflows : POSEIDON2_ARITY < preimageLen 8 8 := by decide

/-- Even at zero framing lanes and with the pack alone, eight pack felts plus eight blinds plus
the three-felt header cannot be absorbed by one permutation.  There is no packing choice inside
this module that rescues it — the felt count is forced by `g16k8_three_per_felt_overflows`. -/
theorem g16k8_needs_a_sponge : ¬ (preimageLen 8 8 ≤ POSEIDON2_ARITY) := by decide

/-! ## §8 — Non-vacuity, both poles. -/

/-- POSITIVE: the pack of a concrete four-order book is the expected `2^28`-range integer. -/
example :
    packedValue (fun i : Fin 4 =>
      (⟨⟨i.val % 8, Nat.mod_lt _ (by decide)⟩, ⟨1, by decide⟩⟩ : N4K4Order)) =
    8 + 128 * 9 + 16384 * 10 + 2097152 * 11 := by decide

/-- NEGATIVE (the tooth): two books that differ in ONE slot pack to DIFFERENT integers.  If the
pack were not injective this `decide` would fail. -/
example :
    packedValue (fun _ : Fin 4 => (⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩ : N4K4Order)) ≠
    packedValue (fun i : Fin 4 =>
      if i = 2 then (⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩ : N4K4Order)
      else ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩) := by decide

/-- The all-pad four-order book packs to `0`. -/
example : packedValue (fun _ : Fin 4 => padOrder (K := 8) (Q := 4) (by decide)) = 0 := by decide

/-- A book with ONE live order does NOT pack to `0` — the pad constant is not reachable from a
live book. -/
example :
    packedValue (fun i : Fin 4 =>
      if i = 3 then (⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩ : N4K4Order)
      else padOrder (by decide)) ≠ 0 := by decide

/-! ## §9 — The MEASURED cost of resizing.

The descriptor's column layout and gate count are arithmetic in the family parameters.  Written
out as functions of them, they reproduce the DEPLOYED numbers exactly — `TRACE_WIDTH = 181`,
`semanticBodies.length = 181`, `constraints.length = 375`, all three pinned by `#guard` against
the live descriptor in `Market.DarkBazaarPrivateDescriptor`.  THAT is what makes the game-sized
row below a computation over a validated model rather than an estimate.

What is NOT measured here, and must not be read as if it were: **prove time**.  The game-sized
AIR has not been emitted (see the note at the end of §7 — the generic descriptor is not built),
so no proof of it has ever been produced and no wall clock exists for it.  The columns and gates
below are exact; a prover second is not claimed. -/

/-- Public header: `session`, `rule`, the eight root lanes, `pStar`, `vStar`. -/
def HEADER_COLS : Nat := 12
/-- Blind limbs absorbed by the commitment. -/
def BLIND_COLS : Nat := 8

/-- Columns one order occupies: a `K`-way one-hot kind, the quantity, its `Q` bits, and the
order's packed digit. -/
def orderCols (K Q : Nat) : Nat := K + Q + 2

/-- Columns one price bucket occupies: demand, supply, the min selector, volume, the min
difference, the max difference, the tie slack, the bucket selector, and three `diffBits`-wide
range decompositions. -/
def priceCols (diffBits : Nat) : Nat := 8 + 3 * diffBits

def traceWidthOf (N P K Q diffBits packFelts : Nat) : Nat :=
  HEADER_COLS + BLIND_COLS + packFelts + N * orderCols K Q + P * priceCols diffBits

/-- Gate bodies one order contributes: `K` one-hot binaries, the one-hot sum, the quantity
recomposition, its `Q` bit binaries, and the order-digit equation. -/
def orderBodyCount (K Q : Nat) : Nat := K + Q + 3

/-- Gate bodies one price bucket contributes: demand, supply, the min selector binary, volume,
the min-difference relation and its recomposition, the bucket selector binary, the max-difference
relation and its recomposition, the tie-slack relation and its recomposition — ELEVEN — plus the
three `diffBits`-wide bit binaries. -/
def priceBodyCount (diffBits : Nat) : Nat := 11 + 3 * diffBits

/-- The rule pin, one packed-felt equation per pack felt, the per-order and per-price bodies,
and the three closing bodies (selector sum, `pStar`, `vStar`). -/
def semanticBodyCount (N P K Q diffBits packFelts : Nat) : Nat :=
  1 + packFelts + N * orderBodyCount K Q + P * priceBodyCount diffBits + 3

/-- The descriptor pins each body on the transition domain AND on the last row, plus the
commitment lookups and the twelve public-input bindings. -/
def constraintCount (N P K Q diffBits packFelts hashLookups : Nat) : Nat :=
  hashLookups + 2 * semanticBodyCount N P K Q diffBits packFelts + 12

/-- The range width the difference/slack decompositions need: they must cover the largest
possible bucket volume, `N · (2^Q − 1)`. -/
def maxBucketVolume (N Q : Nat) : Nat := N * (2 ^ Q - 1)

/-- **The model is VALIDATED against the deployed artifact.**  `181` is
`Market.DarkBazaarPrivateDescriptor.TRACE_WIDTH`, byte-for-byte the `trace_width` in
`circuit/descriptors/by-name/dark-bazaar-private-n4k4.json`. -/
theorem n4k4_trace_width : traceWidthOf 4 4 8 4 6 1 = 181 := by decide
theorem n4k4_body_count : semanticBodyCount 4 4 8 4 6 1 = 181 := by decide
theorem n4k4_constraint_count : constraintCount 4 4 8 4 6 1 1 = 375 := by decide

/-- `DIFF_BITS = 6` is TIGHT for the deployed family: six bits cover the largest bucket volume
`4 · 15 = 60`, five do not. -/
theorem n4k4_diff_bits_tight :
    maxBucketVolume 4 4 < 2 ^ 6 ∧ ¬ (maxBucketVolume 4 4 < 2 ^ 5) := by decide

/-- And `TWELVE` bits, not thirteen, are tight for the game family: `16 · 255 = 4080 < 4096`. -/
theorem g16k8_diff_bits_tight :
    maxBucketVolume 16 8 < 2 ^ 12 ∧ ¬ (maxBucketVolume 16 8 < 2 ^ 11) := by decide

/-- **The game-sized shape, computed over the validated model.**  `N=16`, `P=8`, `K=16`, `Q=8`,
`diffBits=12`, and the EIGHT pack felts `g16k8_three_per_felt_overflows` forces. -/
theorem g16k8_trace_width : traceWidthOf 16 8 16 8 12 8 = 796 := by decide
theorem g16k8_body_count : semanticBodyCount 16 8 16 8 12 8 = 820 := by decide

/-- With the two-permutation sponge §7.1 forces, the constraint count is `1654` — versus the
deployed `375`.  Roughly `4.4×` the columns and `4.4×` the gates, at `4×` the orders and `2×`
the price buckets. -/
theorem g16k8_constraint_count : constraintCount 16 8 16 8 12 8 2 = 1654 := by decide

#guard decide (radix 8 4 = 128)
#guard decide (radix 16 8 = 4096)
#guard decide (preimageLen 8 8 = 19)
#guard decide (traceWidthOf 4 4 8 4 6 1 = 181)
#guard decide (traceWidthOf 16 8 16 8 12 8 = 796)
#guard decide (constraintCount 16 8 16 8 12 8 2 = 1654)

#assert_axioms code_injective
#assert_axioms packedValue_injective
#assert_axioms ChunkedBook.feltValues_injective
#assert_axioms ChunkedBook.feltValue_eq_zero_iff
#assert_axioms bignumVal_ofFn
#assert_axioms g16k8_injective
#assert_axioms g16k8_preimage_overflows

end Market.PackedBookFamily
