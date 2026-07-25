/-
# `Dregg2.Crypto.AcvpHex` -- THE hex codec for every byte wire that crosses the `@[export]` boundary.

## What this module is for (read this before adding a sixth copy)

It began as a build-time helper: the ACVP `internalProjection.json` files carry every field as a
lowercase hex string, and pinning the hex VERBATIM (rather than a decoded byte array) keeps the Lean
constants diff-able by eye against the published JSON. That is still true and still valuable.

It is ALSO, now, the PRODUCTION marshal. The deployed PQ FFI entries
(`dregg_fips204_sign_real`, `dregg_fips204_verify_real`, `dregg_mlkem_{encaps,decaps,keygen}_real`,
`dregg_mldsa_keygen_real`) all speak a space-separated lowercase-hex wire, so every signature this
system produces or checks runs through `decodeHexChars` on the way in and `hexEncode` on the way out.
An ML-DSA-65 sign alone decodes 8,064 hex chars for `sk` and re-encodes 3,309 bytes of signature.

Until 2026-07-25 that fact was hidden by DUPLICATION: five byte-identical (up to spelling) copies of
this codec lived in `AcvpHex`, `MlDsaSignReal`, `Fips204Verify`, `MlKemDecaps` and `MlDsaSigVerAcvp`.
Five copies is how one gets fixed and four do not. There is now ONE, here, and the other four modules
`export` these names rather than redefining them.

## Why the decoder is written twice

`decodeHexChars` is the SPEC: the obvious `Option`-monadic cons-walk, in the shape every proof and
`#guard` in this repo was written against. It is NOT tail-recursive, so as a RUNTIME object it
consumes one stack frame per BYTE — and at ~64 KiB of decoded payload the compiled walk overflows the
stack and ABORTS THE PROCESS. That is strictly worse than the fail-closed `none` this codec promises:
a wire long enough to be interesting kills the node instead of being rejected.

So `decodeHexCharsAux` is the IMPLEMENTATION: the same function with an accumulator, constant stack.
`decodeHexChars_eq_decodeHexCharsTR` PROVES the two are the same function, and `@[csimp]` tells the
compiler to run the tail-recursive one wherever the spec is called. Nothing at any call site changes,
every theorem about `decodeHexChars` stays a theorem about `decodeHexChars`, and the `native_decide`
ACVP pins re-check the deployed object end to end. The fail-closed contract is unchanged: `none` on an
odd length or any non-hex character.

(`hexEncode` needs no such treatment: it is a `List.foldr`, which Lean core already `@[csimp]`s to the
tail-recursive `List.foldrTR`.)
-/

namespace Dregg2.Crypto.AcvpHex

/-- One lowercase/uppercase hex nibble to its `[0,16)` value; `none` on a non-hex char. -/
def hexNibble? (c : Char) : Option UInt8 :=
  if '0' <= c && c <= '9' then some (UInt8.ofNat (c.toNat - '0'.toNat))
  else if 'a' <= c && c <= 'f' then some (UInt8.ofNat (c.toNat - 'a'.toNat + 10))
  else if 'A' <= c && c <= 'F' then some (UInt8.ofNat (c.toNat - 'A'.toNat + 10))
  else none

/-- Decode a hex char list to bytes; `none` on an odd length or any non-hex char (fail-closed).

THE SPEC. Every proof and `#guard` in the repo is stated against this shape. It is not what RUNS —
see `decodeHexCharsAux` and the `@[csimp]` below, which replace it with a constant-stack equal. -/
def decodeHexChars : List Char -> Option (List UInt8)
  | [] => some []
  | [_] => none
  | a :: b :: rest => do
      let hi <- hexNibble? a
      let lo <- hexNibble? b
      let tl <- decodeHexChars rest
      return (hi * 16 + lo) :: tl

/-- The IMPLEMENTATION of `decodeHexChars`: same function, accumulator-passing, so it runs in CONSTANT
stack instead of one frame per decoded byte. Proved equal to the spec below and installed by
`@[csimp]`, so no call site names it. -/
def decodeHexCharsAux : List Char -> List UInt8 -> Option (List UInt8)
  | [], acc => some acc.reverse
  | [_], _ => none
  | a :: b :: rest, acc =>
      match hexNibble? a, hexNibble? b with
      | some hi, some lo => decodeHexCharsAux rest ((hi * 16 + lo) :: acc)
      | _, _ => none

/-- The accumulator invariant: decoding with `acc` already in hand prepends `acc` (reversed) to
whatever the spec would have produced, and fails on exactly the same inputs. -/
theorem decodeHexCharsAux_eq :
    ∀ (cs : List Char) (acc : List UInt8),
      decodeHexCharsAux cs acc = (decodeHexChars cs).map (fun bs => acc.reverse ++ bs)
  | [], acc => by simp [decodeHexCharsAux, decodeHexChars]
  | [_], acc => by simp [decodeHexCharsAux, decodeHexChars]
  | a :: b :: rest, acc => by
      cases ha : hexNibble? a with
      | none => simp [decodeHexCharsAux, decodeHexChars, ha]
      | some hi =>
        cases hb : hexNibble? b with
        | none => simp [decodeHexCharsAux, decodeHexChars, ha, hb]
        | some lo =>
          simp only [decodeHexCharsAux, decodeHexChars, ha, hb]
          rw [decodeHexCharsAux_eq rest ((hi * 16 + lo) :: acc)]
          cases decodeHexChars rest <;>
            simp [List.reverse_cons, List.append_assoc]

/-- The tail-recursive entry point installed for `decodeHexChars` by `@[csimp]`. -/
def decodeHexCharsTR (cs : List Char) : Option (List UInt8) := decodeHexCharsAux cs []

/-- **The runtime swap.** `decodeHexChars` and its constant-stack twin are the SAME FUNCTION — a
machine-checked equality, not a claim — so the compiler may (and does) run the twin everywhere. This
is what keeps a 64 KiB wire from aborting the process without weakening the fail-closed contract by
one input. -/
@[csimp] theorem decodeHexChars_eq_decodeHexCharsTR : @decodeHexChars = @decodeHexCharsTR := by
  funext cs
  rw [decodeHexCharsTR, decodeHexCharsAux_eq cs []]
  cases decodeHexChars cs <;> simp

/-- One byte to two lowercase-hex chars. -/
def toHexDigit (n : UInt8) : Char :=
  let n := n.toNat
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)

/-- Encode bytes as a lowercase-hex string (`decodeHexChars` is its left inverse). Stack-safe already:
Lean core `@[csimp]`s `List.foldr` to the tail-recursive `List.foldrTR`. -/
def hexEncode (bs : List UInt8) : String :=
  String.ofList (bs.foldr (fun b acc => toHexDigit (b / 16) :: toHexDigit (b % 16) :: acc) [])

/-- Decode a hex string to bytes, `[]` on malformed input. Never reached for a pinned vector: the
`wellFormed` `#guard` in each pinning module rejects any string this would fail on. -/
def hexBytes (s : String) : List UInt8 := (decodeHexChars s.toList).getD []

/-- The pinned string is even-length, all-hex, and decodes to exactly `n` bytes. -/
def hexOfLen (s : String) (n : Nat) : Bool :=
  (decodeHexChars s.toList).isSome && (hexBytes s).length == n

/-! ### Teeth — the codec round-trips and fails closed, checked at build time. -/

-- Round-trip on a non-trivial byte range, both nibble halves exercised.
#guard decodeHexChars (hexEncode [0, 1, 15, 16, 127, 128, 255]).toList
  = some [0, 1, 15, 16, 127, 128, 255]
-- Fail-CLOSED: odd length, and a non-hex character in either nibble position.
#guard decodeHexChars "abc".toList = none
#guard decodeHexChars "zz".toList = none
#guard decodeHexChars "az".toList = none
-- Upper case decodes, and agrees with lower case.
#guard decodeHexChars "DEADBEEF".toList = decodeHexChars "deadbeef".toList

end Dregg2.Crypto.AcvpHex
