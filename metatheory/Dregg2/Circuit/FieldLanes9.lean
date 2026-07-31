/-
# Dregg2.Circuit.FieldLanes9 — THE INJECTIVE FIELDS-OCTET ENCODER

`p = 2013265921`, `log₂ p = 30.907`. **Eight lanes carry 247.26 bits against a 32-byte field's
256.** No 8-lane encoding of 32 bytes is injective under ANY chunking — pigeonhole, before a line
of code is read. That counting argument is why the previous repairs of this octet (an eight-way
`fold_bytes32_to_bb` Horner fold, then a `u32 % p` chunking, then a Poseidon2 image over an
injective preimage) each moved the attacker's COST and never reached injectivity: the last of them
priced out at a **2^92.7 collision**, below the ~124-bit bar quoted elsewhere in this tree, making
the fields octet the weakest collision term in the rotated commitment.

**Nine lanes is the minimum, and this is the ninth-lane encoding.** It is not a hash and it does not
borrow a hash's strength: it is an EXPLICIT BIJECTION onto its image, with a total decoder and a
machine-checked left inverse. `fieldToLanes9_injective` is a theorem about the encoding the
producers write, not about a model of it.

## The two pinned lanes

Lanes 0 and 1 are **byte-identical to the previous `field_limbs8`** and had to be. Together they are
the kernel's u64 lane (`field_from_u64`'s payload window, bytes `24..32`): lane 0 is welded to the v1
face column `stateBase + FIELD_BASE + i`, forced by `gFieldWriteP1` against `param1`, and read by
`field_to_u64`; lane 1 is the staged capacity descriptors' named hi-pin slot. The escrow / discharge
/ vault welds, `setfield_encoder_window_gate` and every app encoder (`deos-js-core::pack_u64`,
`starbridge-web-surface::pack_coord`) depend on that. So injectivity has to come from the remaining
seven lanes PLUS those two — never by moving them.

```text
  lane 0   = u32::from_be_bytes(b[28..32]) % p          -- UNCHANGED
  lane 1   = u32::from_be_bytes(b[24..28]) % p          -- UNCHANGED
  lane 2+i = the i-th base-2^28 digit of W,  i = 0..6   -- the ninth-lane repair
```

## Why the pinned pair is not enough, and exactly what the seven repair

Lane 0 is `x % p` for `x = BE(b[28..32]) < 2^32`. Since `2p = 4026531842 < 2^32`, `x` is recoverable
from `x % p` only up to its QUOTIENT `x / p ∈ {0, 1, 2}` — the identical aliasing that made the old
octet `O(1)`-forgeable. Same for lane 1. So the pinned pair leaves `b[24..32]` ambiguous across up to
nine candidates, and carries **nothing at all** about `b[0..24]`.

The seven free lanes therefore carry a single number `W` holding BOTH halves of that residual:

```text
  W = ofDigits 256 ( [b 0, …, b 23]  ++  [ BE(b[28..32])/p  +  4 · BE(b[24..28])/p ] )
```

— a **25-digit base-256 number**: the 24 unbound bytes, then ONE digit carrying both quotients (each
`≤ 2`, so the digit is `≤ 10 < 256`). `W < 11 · 2^192 < 2^196 = (2^28)^7`, so it is exactly seven
base-`2^28` digits and **nothing reduces**: every free lane is `< 2^28 = 268435456 < p`. That is the
point of 28 bits — `7 × 28 = 196` is the tight fit, and a `u32 % p` lane (the shape that aliased)
never appears.

Decoding is total and explicit: recompose `W`, read the 24 bytes back off as base-256 digits, split
the last digit into the two quotients, and undo the reduction on the pinned lanes
(`BE(b[28..32]) = lane 0 + q₀·p`). `lanes9ToField_fieldToLanes9` proves it round-trips;
`fieldToLanes9_injective` is the corollary.

⚑ **The `#guard` vectors at the bottom are Lean-COMPUTED**, not constants transcribed from a Rust
run. `circuit/tests/field_lanes9_injective.rs` asserts the deployed `field_limbs9` reproduces them
and that `field_from_lanes9` returns the VALUE — round-trip, not "the hashes differ".
-/
import Mathlib.Tactic
import Mathlib.Data.List.GetD
import Dregg2.Tactics

namespace Dregg2.Circuit.FieldLanes9

set_option autoImplicit false

/-! ## Carriers -/

/-- BabyBear's modulus — the reduction lanes 0 and 1 perform. -/
def P : Nat := 2013265921

/-- The free lanes' radix, `2^28`. Strictly below `P`, so a free lane NEVER reduces. -/
def CH : Nat := 268435456

theorem CH_lt_P : CH < P := by decide

abbrev Byte := Fin 256
abbrev Bytes32 := Fin 32 → Byte

/-- The nine committed lanes, as naturals. `fieldToLanes9_lt_P` pins every one below `P`, so this
is exactly the deployed `[BabyBear; 9]` with no representability gap. -/
abbrev Lanes9 := Fin 9 → Nat

/-! ## Generic positional-numeral machinery (base `b`, low digit first)

⚠ **THIS IS A SECOND POSITIONAL ALGEBRA AND `Dregg2.Bignum` IS THE FIRST.** Do not delete this block
in favour of that one without reading why it is here; the answer is not "nobody looked".

`Dregg2.Bignum` (over `Dregg2.Circuit.CaveatBignum.bignumVal`) is the emittable, `Int`-valued
schoolbook library — compare/add/sub/mul/mod/range, each tied to a real `Dregg2.Circuit.Constraint`.
`Dregg2.Bignum.DigitInjective.bignumVal_injective` even proves that ranged limb lists are determined
by their value. **None of it discharges anything below**, for two reasons:

1. **DIRECTION.** Every theorem there runs DIGITS → VALUE. `bignumVal_injective` says two ranged
   digit lists with equal value are equal. A codec needs the converse map: a VALUE, and the digits
   it determines — `digitsN` plus `ofDigits_digitsN`. `Bignum` §6's `ModValid` is one Euclidean step
   of that (and pins `q`/`r` exactly); nobody iterated it. That iteration is `digitsN`, below.
2. **CARRIER.** `Bignum` is `Int`-valued because the borrow chain needs signed intermediates. These
   lanes are `Nat`, which is the deployed `[BabyBear; 9]`'s shape and what makes the `#guard` vectors
   at the bottom of this file decidable — and those vectors are the whole pin to the Rust twin.

⚑ And the encoder below is NOT a `bignumVal` instance in the first place, in the way the shape
suggests. Lanes 0/1 are a `mod p` REDUCTION — deliberately non-injective, and no positional-digit
theorem covers them. The injectivity comes from the DECODER being a left inverse
(`lanes9ToField_fieldToLanes9`), which routes the quotient those lanes discard through
`carryDigit` into the free lanes. That composition is this file's, not an algebra's.

(By contrast `Dregg2.Circuit.CommitmentTreeWide.commitmentToLanes16` — 16 lanes of two base-256
digits each — genuinely IS `DigitInjective.chunkedVal_injective` at `B = 256`, `width = 2`. Its
bespoke proof is ten lines and the generic route through `Int` would be longer, so it stays bespoke
too. Recorded so the census is honest, not as a TODO.)
-/

/-- `ofDigits b [d₀, d₁, …] = d₀ + b·d₁ + b²·d₂ + …` -/
def ofDigits (b : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => d + b * ofDigits b ds

/-- The first `k` base-`b` digits of `n`, low first. -/
def digitsN (b : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, n => (n % b) :: digitsN b k (n / b)

theorem digitsN_length (b k n : Nat) : (digitsN b k n).length = k := by
  induction k generalizing n with
  | zero => simp [digitsN]
  | succ k ih => simp [digitsN, ih]

theorem ofDigits_append (b : Nat) (L₁ L₂ : List Nat) :
    ofDigits b (L₁ ++ L₂) = ofDigits b L₁ + b ^ L₁.length * ofDigits b L₂ := by
  induction L₁ with
  | nil => simp [ofDigits]
  | cons d ds ih =>
      simp only [List.cons_append, ofDigits, ih, List.length_cons, pow_succ]
      ring

theorem ofDigits_lt (b : Nat) (_hb : 0 < b) :
    ∀ L : List Nat, (∀ x ∈ L, x < b) → ofDigits b L < b ^ L.length := by
  intro L
  induction L with
  | nil => intro _; simp [ofDigits]
  | cons d ds ih =>
      intro hall
      have hd : d < b := hall d (by simp)
      have hds : ofDigits b ds < b ^ ds.length := ih (fun x hx => hall x (by simp [hx]))
      have key : d + b * ofDigits b ds < b ^ ds.length * b := by
        have hsucc : ofDigits b ds + 1 ≤ b ^ ds.length := hds
        calc d + b * ofDigits b ds < b + b * ofDigits b ds := by omega
          _ = b * (ofDigits b ds + 1) := by ring
          _ ≤ b * b ^ ds.length := Nat.mul_le_mul_left b hsucc
          _ = b ^ ds.length * b := by ring
      simpa [List.length_cons, ofDigits, pow_succ] using key

/-- Recomposition: `k` digits recover any `n < b^k`. -/
theorem ofDigits_digitsN (b : Nat) (hb : 0 < b) :
    ∀ (k n : Nat), n < b ^ k → ofDigits b (digitsN b k n) = n := by
  intro k
  induction k with
  | zero =>
      intro n hn
      simp only [pow_zero] at hn
      simp only [digitsN, ofDigits]
      omega
  | succ k ih =>
      intro n hn
      have hdiv : n / b < b ^ k := by
        rw [Nat.div_lt_iff_lt_mul hb]
        calc n < b ^ (k + 1) := hn
          _ = b ^ k * b := by rw [pow_succ]
      simp only [digitsN, ofDigits, ih (n / b) hdiv]
      exact Nat.mod_add_div n b

/-- Digit extraction: a canonical digit list is recovered from its value. -/
theorem digitsN_ofDigits (b : Nat) (hb : 0 < b) :
    ∀ (L : List Nat), (∀ x ∈ L, x < b) → digitsN b L.length (ofDigits b L) = L := by
  intro L
  induction L with
  | nil => intro _; simp [digitsN]
  | cons d ds ih =>
      intro hall
      have hd : d < b := hall d (by simp)
      have hds : ∀ x ∈ ds, x < b := fun x hx => hall x (by simp [hx])
      have h1 : (d + b * ofDigits b ds) % b = d := by
        rw [Nat.add_mul_mod_self_left]
        exact Nat.mod_eq_of_lt hd
      have h2 : (d + b * ofDigits b ds) / b = ofDigits b ds := by
        rw [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt hd, Nat.zero_add]
      show digitsN b (ds.length + 1) (d + b * ofDigits b ds) = d :: ds
      rw [digitsN, h1, h2, ih hds]

/-- Every digit `digitsN` emits is a genuine base-`b` digit. -/
theorem digitsN_lt (b : Nat) (hb : 0 < b) :
    ∀ (k n : Nat), ∀ x ∈ digitsN b k n, x < b := by
  intro k
  induction k with
  | zero => intro n x hx; simp [digitsN] at hx
  | succ k ih =>
      intro n x hx
      simp only [digitsN, List.mem_cons] at hx
      rcases hx with h | h
      · subst h; exact Nat.mod_lt _ hb
      · exact ih (n / b) x h

/-! ## THE ENCODER -/

/-- `u32::from_be_bytes(b[28..32])` — the kernel u64 lane's `lo32`. -/
def loWord (b : Bytes32) : Nat :=
  (b 28).1 * 16777216 + (b 29).1 * 65536 + (b 30).1 * 256 + (b 31).1

/-- `u32::from_be_bytes(b[24..28])` — the kernel u64 lane's `hi32`. -/
def hiWord (b : Bytes32) : Nat :=
  (b 24).1 * 16777216 + (b 25).1 * 65536 + (b 26).1 * 256 + (b 27).1

theorem loWord_lt (b : Bytes32) : loWord b < 4294967296 := by
  have h0 := (b 28).2; have h1 := (b 29).2; have h2 := (b 30).2; have h3 := (b 31).2
  simp only [loWord]; omega

theorem hiWord_lt (b : Bytes32) : hiWord b < 4294967296 := by
  have h0 := (b 24).2; have h1 := (b 25).2; have h2 := (b 26).2; have h3 := (b 27).2
  simp only [hiWord]; omega

/-- The 24 bytes the pinned lanes carry NOTHING about, low index first. Written out so the
round-trip discharge reduces instead of unfolding an `ofFn`. -/
def lowBytes (b : Bytes32) : List Nat :=
  [(b 0).1, (b 1).1, (b 2).1, (b 3).1, (b 4).1, (b 5).1,
   (b 6).1, (b 7).1, (b 8).1, (b 9).1, (b 10).1, (b 11).1,
   (b 12).1, (b 13).1, (b 14).1, (b 15).1, (b 16).1, (b 17).1,
   (b 18).1, (b 19).1, (b 20).1, (b 21).1, (b 22).1, (b 23).1]

theorem lowBytes_length (b : Bytes32) : (lowBytes b).length = 24 := by
  simp [lowBytes]

theorem lowBytes_lt (b : Bytes32) : ∀ x ∈ lowBytes b, x < 256 := by
  intro x hx
  simp only [lowBytes, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> exact (b _).2

/-- **The disambiguation digit.** Lane 0 pins `loWord % p` and lane 1 pins `hiWord % p`; since
`2p < 2^32` each quotient is `0`, `1` or `2`, so this ONE base-256 digit (`≤ 2 + 4·2 = 10`) closes
the residual ambiguity the pinned lanes leave. -/
def carryDigit (b : Bytes32) : Nat := loWord b / P + 4 * (hiWord b / P)

theorem loWord_div_le (b : Bytes32) : loWord b / P ≤ 2 := by
  have hl := loWord_lt b
  show loWord b / 2013265921 ≤ 2
  omega

theorem hiWord_div_le (b : Bytes32) : hiWord b / P ≤ 2 := by
  have hh := hiWord_lt b
  show hiWord b / 2013265921 ≤ 2
  omega

theorem carryDigit_le (b : Bytes32) : carryDigit b ≤ 10 := by
  have h1 := loWord_div_le b
  have h2 := hiWord_div_le b
  simp only [carryDigit]; omega

/-- `W` — the single number the seven free lanes carry. -/
def preWord (b : Bytes32) : Nat := ofDigits 256 (lowBytes b ++ [carryDigit b])

theorem preWord_lt (b : Bytes32) : preWord b < CH ^ 7 := by
  have hsplit : preWord b = ofDigits 256 (lowBytes b) + 256 ^ 24 * carryDigit b := by
    simp only [preWord, ofDigits_append, lowBytes_length, ofDigits]
    ring
  have hlow : ofDigits 256 (lowBytes b) < 256 ^ 24 := by
    have := ofDigits_lt 256 (by norm_num) (lowBytes b) (lowBytes_lt b)
    rwa [lowBytes_length] at this
  have hc := carryDigit_le b
  have hmul : 256 ^ 24 * carryDigit b ≤ 256 ^ 24 * 10 := Nat.mul_le_mul_left _ hc
  have hpow : (256 : Nat) ^ 24 * 11 < CH ^ 7 := by norm_num [CH]
  omega

/-- The seven free lanes, low digit first. -/
def chunks7 (b : Bytes32) : List Nat := digitsN CH 7 (preWord b)

theorem chunks7_length (b : Bytes32) : (chunks7 b).length = 7 := digitsN_length _ _ _

/-- **THE ENCODER.** Lanes 0 and 1 are the deployed kernel u64 lane, byte-identical. Lanes `2..8`
are the seven base-`2^28` digits of `W`. -/
def fieldToLanes9 (b : Bytes32) : Lanes9 := fun i =>
  if i.1 = 0 then loWord b % P
  else if i.1 = 1 then hiWord b % P
  else (chunks7 b).getD (i.1 - 2) 0

/-- Every lane is a genuine BabyBear element — the free lanes because `2^28 < p` (they NEVER
reduce), the pinned pair because they are reductions. -/
theorem chunks7_lt_CH (b : Bytes32) : ∀ x ∈ chunks7 b, x < CH :=
  digitsN_lt CH (by decide) 7 (preWord b)

theorem fieldToLanes9_lt_P (b : Bytes32) (i : Fin 9) : fieldToLanes9 b i < P := by
  simp only [fieldToLanes9]
  split
  · exact Nat.mod_lt _ (by decide)
  · split
    · exact Nat.mod_lt _ (by decide)
    · rcases Nat.lt_or_ge (i.1 - 2) (chunks7 b).length with h | h
      · rw [List.getD_eq_getElem _ _ h]
        exact lt_trans (chunks7_lt_CH b _ (List.getElem_mem h)) CH_lt_P
      · rw [List.getD_eq_default _ _ h]
        decide

/-! ## THE DECODER — total, explicit, and the inverse -/

def laneList (L : Lanes9) : List Nat := [L 2, L 3, L 4, L 5, L 6, L 7, L 8]

/-- `W`, recomposed from the seven free lanes. -/
def decWord (L : Lanes9) : Nat := ofDigits CH (laneList L)

/-- The 25 base-256 digits of the recomposed `W`. -/
def decDigits (L : Lanes9) : List Nat := digitsN 256 25 (decWord L)

/-- The disambiguation digit, read back. -/
def decCarry (L : Lanes9) : Nat := (decDigits L).getD 24 0

/-- The kernel u64 lane's `hi32`, with lane 1's reduction undone. -/
def decHi (L : Lanes9) : Nat := L 1 + (decCarry L / 4) * P

/-- The kernel u64 lane's `lo32`, with lane 0's reduction undone. -/
def decLo (L : Lanes9) : Nat := L 0 + (decCarry L % 4) * P

/-- **THE DECODER.** Total on every lane vector; the exact inverse on the encoder's image. -/
def lanes9ToField (L : Lanes9) : Bytes32 := fun j =>
  if j.1 < 24 then ⟨(decDigits L).getD j.1 0 % 256, Nat.mod_lt _ (by decide)⟩
  else if j.1 = 24 then ⟨decHi L / 16777216 % 256, Nat.mod_lt _ (by decide)⟩
  else if j.1 = 25 then ⟨decHi L / 65536 % 256, Nat.mod_lt _ (by decide)⟩
  else if j.1 = 26 then ⟨decHi L / 256 % 256, Nat.mod_lt _ (by decide)⟩
  else if j.1 = 27 then ⟨decHi L % 256, Nat.mod_lt _ (by decide)⟩
  else if j.1 = 28 then ⟨decLo L / 16777216 % 256, Nat.mod_lt _ (by decide)⟩
  else if j.1 = 29 then ⟨decLo L / 65536 % 256, Nat.mod_lt _ (by decide)⟩
  else if j.1 = 30 then ⟨decLo L / 256 % 256, Nat.mod_lt _ (by decide)⟩
  else ⟨decLo L % 256, Nat.mod_lt _ (by decide)⟩

private theorem list7_eta (l : List Nat) (h : l.length = 7) :
    [l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0, l.getD 4 0, l.getD 5 0, l.getD 6 0] = l := by
  rcases l with _ | ⟨a, l⟩; · simp at h
  rcases l with _ | ⟨b, l⟩; · simp at h
  rcases l with _ | ⟨c, l⟩; · simp at h
  rcases l with _ | ⟨d, l⟩; · simp at h
  rcases l with _ | ⟨e, l⟩; · simp at h
  rcases l with _ | ⟨f, l⟩; · simp at h
  rcases l with _ | ⟨g, l⟩; · simp at h
  rcases l with _ | ⟨x, l⟩
  · rfl
  · simp at h

/-- The seven free lanes recompose to exactly `W`. -/
theorem decWord_encode (b : Bytes32) : decWord (fieldToLanes9 b) = preWord b := by
  have hshape : laneList (fieldToLanes9 b) = chunks7 b := by
    simp only [laneList, fieldToLanes9]
    norm_num
    exact list7_eta (chunks7 b) (chunks7_length b)
  simp only [decWord, hshape, chunks7]
  exact ofDigits_digitsN CH (by decide) 7 (preWord b) (preWord_lt b)

/-- The 25 base-256 digits of `W` are exactly the 24 unbound bytes and the disambiguation digit. -/
theorem decDigits_encode (b : Bytes32) :
    decDigits (fieldToLanes9 b) = lowBytes b ++ [carryDigit b] := by
  have hlen : (lowBytes b ++ [carryDigit b]).length = 25 := by
    simp [lowBytes_length]
  have hall : ∀ x ∈ lowBytes b ++ [carryDigit b], x < 256 := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact lowBytes_lt b x h
    · simp only [List.mem_singleton] at h
      subst h
      have := carryDigit_le b
      omega
  have hcanon := digitsN_ofDigits 256 (by norm_num) (lowBytes b ++ [carryDigit b]) hall
  rw [hlen] at hcanon
  simp only [decDigits, decWord_encode]
  simpa [preWord] using hcanon

theorem decCarry_encode (b : Bytes32) : decCarry (fieldToLanes9 b) = carryDigit b := by
  simp only [decCarry, decDigits_encode, lowBytes, List.cons_append, List.nil_append,
    List.getD_cons_succ, List.getD_cons_zero]

/-- The disambiguation digit really does carry BOTH quotients, separably. -/
theorem carryDigit_mod (b : Bytes32) : carryDigit b % 4 = loWord b / P := by
  have h1 := loWord_div_le b
  simp only [carryDigit]
  generalize loWord b / P = x at h1 ⊢
  generalize hiWord b / P = y
  omega

theorem carryDigit_div (b : Bytes32) : carryDigit b / 4 = hiWord b / P := by
  have h1 := loWord_div_le b
  simp only [carryDigit]
  generalize loWord b / P = x at h1 ⊢
  generalize hiWord b / P = y
  omega

/-- The pinned lanes' `mod p` reduction is undone exactly. -/
theorem decLo_encode (b : Bytes32) : decLo (fieldToLanes9 b) = loWord b := by
  have h0 : fieldToLanes9 b 0 = loWord b % P := by simp [fieldToLanes9]
  rw [decLo, decCarry_encode, carryDigit_mod, h0]
  exact Nat.mod_add_div' (loWord b) P

theorem decHi_encode (b : Bytes32) : decHi (fieldToLanes9 b) = hiWord b := by
  have h1 : fieldToLanes9 b 1 = hiWord b % P := by simp [fieldToLanes9]
  rw [decHi, decCarry_encode, carryDigit_div, h1]
  exact Nat.mod_add_div' (hiWord b) P

/-- **THE LEFT INVERSE.** Every 32-byte field value round-trips through the nine lanes. -/
theorem lanes9ToField_fieldToLanes9 (b : Bytes32) :
    lanes9ToField (fieldToLanes9 b) = b := by
  funext j
  apply Fin.ext
  simp only [lanes9ToField, decDigits_encode, decLo_encode, decHi_encode]
  fin_cases j <;>
    simp only [lowBytes, loWord, hiWord, List.cons_append, List.nil_append,
      List.getD_cons_zero, List.getD_cons_succ, Nat.reduceLT, Nat.reduceEqDiff,
      reduceIte, Fin.isValue] <;>
    first
      | exact Nat.mod_eq_of_lt (b _).2
      | (have e24 : b ⟨24, by omega⟩ = b 24 := rfl
         have e25 : b ⟨25, by omega⟩ = b 25 := rfl
         have e26 : b ⟨26, by omega⟩ = b 26 := rfl
         have e27 : b ⟨27, by omega⟩ = b 27 := rfl
         have e28 : b ⟨28, by omega⟩ = b 28 := rfl
         have e29 : b ⟨29, by omega⟩ = b 29 := rfl
         have e30 : b ⟨30, by omega⟩ = b 30 := rfl
         have e31 : b ⟨31, by omega⟩ = b 31 := rfl
         simp only [e24, e25, e26, e27, e28, e29, e30, e31]
         have h24 := (b 24).2; have h25 := (b 25).2
         have h26 := (b 26).2; have h27 := (b 27).2
         have h28 := (b 28).2; have h29 := (b 29).2
         have h30 := (b 30).2; have h31 := (b 31).2
         omega)

/-- **THE THEOREM.** The nine-lane fields encoder is INJECTIVE: no two distinct 32-byte field
values share a lane vector. Not a hash bound, not a birthday bound — an injection. -/
theorem fieldToLanes9_injective : Function.Injective fieldToLanes9 := by
  intro a b h
  have := congrArg lanes9ToField h
  simpa [lanes9ToField_fieldToLanes9] using this

/-- The counting argument this closes, as arithmetic: nine lanes clear 256 bits where eight
cannot. `P^8 < 2^256 ≤ P^9`. -/
theorem nine_lanes_is_the_minimum : P ^ 8 < 2 ^ 256 ∧ 2 ^ 256 ≤ P ^ 9 := by
  constructor <;> norm_num [P]

#assert_axioms ofDigits_digitsN
#assert_axioms digitsN_ofDigits
#assert_axioms lanes9ToField_fieldToLanes9
#assert_axioms fieldToLanes9_injective
#assert_axioms nine_lanes_is_the_minimum

/-! ## Lean-COMPUTED protocol vectors (mirrored by `circuit/tests/field_lanes9_injective.rs`) -/

def ascendingBytes : Bytes32 := fun i => ⟨i.1, by omega⟩
def zeroBytes : Bytes32 := fun _ => 0
def maxBytes : Bytes32 := fun _ => ⟨255, by decide⟩

/-- `field_from_u64 v` — the kernel's numeric field encoding: `v` big-endian in bytes `24..32`. -/
def fromU64 (v : Nat) : Bytes32 := fun i =>
  if 24 ≤ i.1 then ⟨v / 256 ^ (31 - i.1) % 256, Nat.mod_lt _ (by decide)⟩ else 0

def lanesOf (b : Bytes32) : List Nat := List.ofFn (fieldToLanes9 b)

/-- Byte view, for the round-trip guards. -/
def bytesOf (b : Bytes32) : List Nat := List.ofFn (fun i => (b i).1)

/-! ⚑ **THE VALVE OUTCOME, PRESERVED.** Lane 0 still carries the raw numeric value, so the escrow /
discharge / vault weld constants, `setfield_encoder_window_gate` and every app encoder survive
verbatim. The seven free lanes are all ZERO for a numeric value — they carry `b[0..24]`, which
`field_from_u64` leaves empty.

⚠ **THE HONEST WINDOW IS `v < p`, NOT `v < 2^31`.** The `field_limbs8` docstring said "`v < 2^31`"
and that is FALSE across `[p, 2^31) = [2013265921, 2147483648)` — 134,217,727 values wide, every one
of which lane 0 reports as `v - p`. The guards below pin BOTH sides of that boundary, because a weld
constant that reads lane 0 as the raw value is wrong for exactly that window and no test named it. -/
#guard lanesOf (fromU64 1) = [1, 0, 0, 0, 0, 0, 0, 0, 0]
#guard lanesOf (fromU64 1000000) = [1000000, 0, 0, 0, 0, 0, 0, 0, 0]
#guard lanesOf zeroBytes = [0, 0, 0, 0, 0, 0, 0, 0, 0]

/-! The two sides of the honest window. At `p - 1` lane 0 is still the raw value and the ninth lane
is empty; at `p` lane 0 reads ZERO — the residue — and the ninth lane carries the quotient that
distinguishes them. Without lane 8 these two values would be indistinguishable in lane 0 AND in
every other lane, since `field_from_u64` leaves `b[0..24]` empty. -/
#guard fieldToLanes9 (fromU64 2013265920) 0 = 2013265920
#guard fieldToLanes9 (fromU64 2013265920) 8 = 0
#guard fieldToLanes9 (fromU64 2013265921) 0 = 0
#guard fieldToLanes9 (fromU64 2013265921) 8 = 16777216
#guard lanesOf (fromU64 2013265921) ≠ lanesOf zeroBytes

/-! `2^32 - 1` — the pinned lane reduces (`% p`) and the NINTH lane carries the quotient that used
to be lost. `268435453 = (2^32-1) mod p`, and lane 8 `= 2·2^24` is `q₀ = 2` in the top digit. -/
#guard lanesOf (fromU64 4294967295) = [268435453, 0, 0, 0, 0, 0, 0, 0, 33554432]

/-! Both quotients at once: every byte `0xff`, so `q₀ = q₁ = 2` and the carry digit is `10`. -/
#guard lanesOf maxBytes =
  [268435453, 268435453, 268435455, 268435455, 268435455,
   268435455, 268435455, 268435455, 184549375]

/-! A value with structure in every byte. -/
#guard lanesOf ascendingBytes =
  [471670303, 404298267, 50462976, 6312000, 168364039,
   13680816, 17829646, 21049633, 1512981]

/-! ⚑ ANTI-VACUITY, IN LEAN: the vectors above are not merely distinct — the VALUES come back. -/
#guard bytesOf (lanes9ToField (fieldToLanes9 ascendingBytes)) = bytesOf ascendingBytes
#guard bytesOf (lanes9ToField (fieldToLanes9 maxBytes)) = bytesOf maxBytes
#guard bytesOf (lanes9ToField (fieldToLanes9 (fromU64 4294967295))) = bytesOf (fromU64 4294967295)

/-! ⚑ AND THE POLE THAT WAS OPEN: the `+p` sibling that used to share an octet. Under the old
eight-lane encoding `x` and `x + p` agreed in lane 0 with nothing else to separate them; here
lane 8 splits them — and `fieldToLanes9_injective` says so for every pair, not just this one. -/
#guard fieldToLanes9 (fromU64 1) 0 = fieldToLanes9 (fromU64 (1 + 2013265921)) 0
#guard lanesOf (fromU64 1) ≠ lanesOf (fromU64 (1 + 2013265921))
#guard fieldToLanes9 (fromU64 (1 + 2013265921)) 8 = 16777216

end Dregg2.Circuit.FieldLanes9
