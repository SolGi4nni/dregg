/-!
# Decimal ASCII, and its inverse

The HTTP/1.1 response serializer renders numeric fields (the status code, the
derived `Content-Length`) as decimal ASCII via `Nat.repr … |>.toUTF8.toList`.
The response *client* has to read those bytes back. This module proves that a
plain left-to-right decimal fold inverts that rendering exactly:

    dval 0 (natToDec n) = n        (`dval_natToDec`)

and that every byte of `natToDec n` is an ASCII digit `0x30…0x39`
(`natToDec_isDigit`) — the two facts the response parser needs so the status
token and the `Content-Length` value are recovered faithfully and neither
carries a `SP`, `CR`, `LF`, or `:` delimiter.

The kernel obstacle is that `String.toUTF8`/`ByteArray.toList` do not reduce by
`decide` (they are `@[extern]`, and `ByteArray.toList` is a `get!` loop with no
library lemmas). `baMkList` proves the one loop-invariant that unblocks the
bridge from `natToDec` to the character list `Nat.toDigits 10 n`.

Everything here is Lean-core only; total; no `sorry`.
-/

namespace Proto
namespace Dec

open Nat (toDigitsCore toDigits digitChar)

/-- Wire bytes as a list. -/
abbrev Bytes := List UInt8

/-- Exactly the serializer's rendering (`Reactor.natToDec`), defined locally so
this module depends on nothing. `Reactor.natToDec = Proto.Dec.natToDec` by `rfl`. -/
def natToDec (n : Nat) : Bytes := (Nat.repr n).toUTF8.toList

/-- Decimal value of one ASCII digit byte. -/
def digitByteVal (b : UInt8) : Nat := b.toNat - 48

/-- Left-to-right decimal fold over bytes. -/
def dval : Nat → Bytes → Nat
  | acc, [] => acc
  | acc, b :: bs => dval (acc * 10 + digitByteVal b) bs

/-- Left-to-right decimal fold over the digit characters `Nat.repr` produces. -/
def cval : Nat → List Char → Nat
  | acc, [] => acc
  | acc, c :: cs => cval (acc * 10 + (c.val.toNat - 48)) cs

theorem dval_append (xs ys : Bytes) (acc : Nat) :
    dval acc (xs ++ ys) = dval (dval acc xs) ys := by
  induction xs generalizing acc with
  | nil => rfl
  | cons a t ih => exact ih (acc * 10 + digitByteVal a)

theorem cval_append (xs ys : List Char) (acc : Nat) :
    cval acc (xs ++ ys) = cval (cval acc xs) ys := by
  induction xs generalizing acc with
  | nil => rfl
  | cons a t ih => exact ih (acc * 10 + (a.val.toNat - 48))

/-- `toDigitsCore` prepends the digits of `n` in front of its accumulator. -/
theorem tdc_append (fuel n : Nat) (ds : List Char) :
    toDigitsCore 10 fuel n ds = toDigitsCore 10 fuel n [] ++ ds := by
  induction fuel generalizing n ds with
  | zero => rfl
  | succ f ih =>
    unfold toDigitsCore
    by_cases h : n / 10 = 0
    · simp [h]
    · simp only [h, if_false]
      rw [ih (n / 10) (digitChar (n % 10) :: ds), ih (n / 10) [digitChar (n % 10)]]
      simp

/-- `digitChar r` (`r < 10`) is the ASCII digit whose value is `r`. -/
theorem digitChar_val : ∀ r, r < 10 → (digitChar r).val.toNat - 48 = r
  | 0, _ => by decide
  | 1, _ => by decide
  | 2, _ => by decide
  | 3, _ => by decide
  | 4, _ => by decide
  | 5, _ => by decide
  | 6, _ => by decide
  | 7, _ => by decide
  | 8, _ => by decide
  | 9, _ => by decide
  | (_ + 10), h => by omega

/-- Character-level inversion: folding the digit characters of `n` yields `n`. -/
theorem cval_tdc (fuel n : Nat) (h : n < fuel) :
    cval 0 (toDigitsCore 10 fuel n []) = n := by
  induction fuel generalizing n with
  | zero => omega
  | succ f ih =>
    unfold toDigitsCore
    by_cases hn : n / 10 = 0
    · simp only [hn, if_true]
      show (0 : Nat) * 10 + ((digitChar (n % 10)).val.toNat - 48) = n
      rw [digitChar_val (n % 10) (by omega)]; omega
    · simp only [hn, if_false]
      rw [tdc_append f (n / 10) [digitChar (n % 10)], cval_append]
      have hpos : 0 < n := by omega
      have hdf : n / 10 < f := by
        have := Nat.div_lt_self hpos (by omega : 1 < 10); omega
      rw [ih (n / 10) hdf]
      show (n / 10) * 10 + ((digitChar (n % 10)).val.toNat - 48) = n
      rw [digitChar_val (n % 10) (by omega)]; omega

/-! ### The `ByteArray.toList` / `toUTF8` bridge -/

/-- The `ByteArray.toList` `get!`-loop, characterized on a concrete list. -/
theorem toList_loop_inv (L : Bytes) : ∀ fuel i r, L.length - i ≤ fuel →
    ByteArray.toList.loop ⟨⟨L⟩⟩ i r = r.reverse ++ L.drop i := by
  intro fuel
  induction fuel with
  | zero =>
    intro i r hle
    have hge : L.length ≤ i := by omega
    unfold ByteArray.toList.loop
    have hsz : (⟨⟨L⟩⟩ : ByteArray).size = L.length := rfl
    rw [hsz]
    simp only [Nat.not_lt.mpr hge, if_false, List.drop_eq_nil_of_le hge, List.append_nil]
  | succ f ih =>
    intro i r hle
    unfold ByteArray.toList.loop
    have hsz : (⟨⟨L⟩⟩ : ByteArray).size = L.length := rfl
    rw [hsz]
    by_cases h : i < L.length
    · simp only [h, if_true]
      have hget : (⟨⟨L⟩⟩ : ByteArray).get! i = L[i]'h := by
        show (⟨L⟩ : Array UInt8)[i]! = L[i]'h
        rw [getElem!_pos (⟨L⟩ : Array UInt8) i h]; rfl
      rw [hget, ih (i + 1) (L[i]'h :: r) (by omega), List.drop_eq_getElem_cons h]
      simp
    · simp only [h, if_false]
      have hge : L.length ≤ i := by omega
      simp only [List.drop_eq_nil_of_le hge, List.append_nil]

/-- Reading a freshly built byte array back as a list is the identity. -/
theorem baMkList (L : Bytes) : (ByteArray.mk (Array.mk L)).toList = L := by
  show ByteArray.toList.loop _ 0 [] = L
  rw [toList_loop_inv L L.length 0 [] (by omega)]; simp

/-- `ByteArray.toList` reads out exactly the underlying array data. (Structure-eta
turns any `bs` into `⟨⟨bs.data.toList⟩⟩`, so `baMkList` applies.) -/
theorem toList_eq_data_toList (bs : ByteArray) : bs.toList = bs.data.toList :=
  baMkList bs.data.toList

/-- `natToDec n` is exactly the UTF-8 encoding of the digit characters of `n`. -/
theorem natToDec_eq (n : Nat) :
    natToDec n = (toDigits 10 n).flatMap String.utf8EncodeChar := by
  show ((Nat.repr n).toUTF8).toList = _
  unfold Nat.repr
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
  unfold List.utf8Encode
  rw [toList_eq_data_toList, List.toList_data_toByteArray]

/-! ### Every digit character encodes to one ASCII-digit byte -/

/-- Per-digit encoding: `dval` of the UTF-8 of one digit character adds that digit. -/
theorem dval_encode_digit : ∀ r, r < 10 → ∀ acc,
    dval acc (String.utf8EncodeChar (digitChar r)) = acc * 10 + r
  | 0, _, acc => by rw [show String.utf8EncodeChar (digitChar 0) = [48] from by decide]; rfl
  | 1, _, acc => by rw [show String.utf8EncodeChar (digitChar 1) = [49] from by decide]; rfl
  | 2, _, acc => by rw [show String.utf8EncodeChar (digitChar 2) = [50] from by decide]; rfl
  | 3, _, acc => by rw [show String.utf8EncodeChar (digitChar 3) = [51] from by decide]; rfl
  | 4, _, acc => by rw [show String.utf8EncodeChar (digitChar 4) = [52] from by decide]; rfl
  | 5, _, acc => by rw [show String.utf8EncodeChar (digitChar 5) = [53] from by decide]; rfl
  | 6, _, acc => by rw [show String.utf8EncodeChar (digitChar 6) = [54] from by decide]; rfl
  | 7, _, acc => by rw [show String.utf8EncodeChar (digitChar 7) = [55] from by decide]; rfl
  | 8, _, acc => by rw [show String.utf8EncodeChar (digitChar 8) = [56] from by decide]; rfl
  | 9, _, acc => by rw [show String.utf8EncodeChar (digitChar 9) = [57] from by decide]; rfl
  | (_ + 10), h, _ => by omega

/-- Every character of `toDigits 10 n` is a decimal digit character. -/
theorem mem_toDigits_isDigit (n : Nat) :
    ∀ c ∈ toDigits 10 n, ∃ r, r < 10 ∧ c = digitChar r := by
  have go : ∀ fuel m c, c ∈ toDigitsCore 10 fuel m [] → ∃ r, r < 10 ∧ c = digitChar r := by
    intro fuel
    induction fuel with
    | zero => intro m c hc; simp [toDigitsCore] at hc
    | succ f ih =>
      intro m c hc
      unfold toDigitsCore at hc
      by_cases h : m / 10 = 0
      · simp only [h, if_true, List.mem_singleton] at hc
        exact ⟨m % 10, Nat.mod_lt _ (by omega), hc⟩
      · simp only [h, if_false] at hc
        rw [tdc_append f (m / 10) [digitChar (m % 10)]] at hc
        simp only [List.mem_append, List.mem_singleton] at hc
        rcases hc with hc | hc
        · exact ih (m / 10) c hc
        · exact ⟨m % 10, Nat.mod_lt _ (by omega), hc⟩
  intro c hc; exact go (n + 1) n c hc

/-- The bridge: `dval` of the UTF-8 of a digit-character list equals `cval` of it. -/
theorem dval_flatMap (cs : List Char)
    (hcs : ∀ c ∈ cs, ∃ r, r < 10 ∧ c = digitChar r) :
    ∀ acc, dval acc (cs.flatMap String.utf8EncodeChar) = cval acc cs := by
  induction cs with
  | nil => intro acc; rfl
  | cons a t ih =>
    intro acc
    obtain ⟨r, hr, rfl⟩ := hcs a (by simp)
    rw [List.flatMap_cons, dval_append, dval_encode_digit r hr acc]
    rw [ih (fun c hc => hcs c (by simp [hc]))]
    show cval (acc * 10 + r) t = cval (acc * 10 + ((digitChar r).val.toNat - 48)) t
    rw [digitChar_val r hr]

/-- **Decimal round-trip.** The decimal fold inverts the serializer's numeric
rendering exactly: `dval 0 (natToDec n) = n`. -/
theorem dval_natToDec (n : Nat) : dval 0 (natToDec n) = n := by
  rw [natToDec_eq, dval_flatMap _ (mem_toDigits_isDigit n) 0]
  show cval 0 (toDigitsCore 10 (n + 1) n []) = n
  exact cval_tdc (n + 1) n (by omega)

/-! ### `natToDec` carries only ASCII-digit bytes -/

/-- Every byte of `natToDec n` is an ASCII decimal digit `0x30…0x39`. -/
theorem natToDec_isDigit (n : Nat) :
    ∀ b ∈ natToDec n, 48 ≤ b.toNat ∧ b.toNat ≤ 57 := by
  rw [natToDec_eq]
  intro b hb
  rw [List.mem_flatMap] at hb
  obtain ⟨c, hc, hb⟩ := hb
  obtain ⟨r, hr, rfl⟩ := mem_toDigits_isDigit n c hc
  revert hb
  match r, hr with
  | 0, _ => intro hb; rw [show String.utf8EncodeChar (digitChar 0) = [48] from by decide] at hb; simp_all
  | 1, _ => intro hb; rw [show String.utf8EncodeChar (digitChar 1) = [49] from by decide] at hb; simp_all
  | 2, _ => intro hb; rw [show String.utf8EncodeChar (digitChar 2) = [50] from by decide] at hb; simp_all
  | 3, _ => intro hb; rw [show String.utf8EncodeChar (digitChar 3) = [51] from by decide] at hb; simp_all
  | 4, _ => intro hb; rw [show String.utf8EncodeChar (digitChar 4) = [52] from by decide] at hb; simp_all
  | 5, _ => intro hb; rw [show String.utf8EncodeChar (digitChar 5) = [53] from by decide] at hb; simp_all
  | 6, _ => intro hb; rw [show String.utf8EncodeChar (digitChar 6) = [54] from by decide] at hb; simp_all
  | 7, _ => intro hb; rw [show String.utf8EncodeChar (digitChar 7) = [55] from by decide] at hb; simp_all
  | 8, _ => intro hb; rw [show String.utf8EncodeChar (digitChar 8) = [56] from by decide] at hb; simp_all
  | 9, _ => intro hb; rw [show String.utf8EncodeChar (digitChar 9) = [57] from by decide] at hb; simp_all
  | (_ + 10), h => intro _; omega

end Dec
end Proto
