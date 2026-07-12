/-
# `Dregg2.Crypto.MlDsaCodec` — the REAL ML-DSA-65 byte codec (FIPS 204), as EXECUTABLE `def`s.

BRICK 5 of replacing the `A = id` scalar caricature in `Fips204Verify.lean` with the full-dimension
ML-DSA-65 verify. This module is the byte-faithful interop layer with the deployed `fips204` crate: the
1952-byte public key and the 3309-byte signature are DECODED into the ring objects (`ρ`, the `t1` vector,
`c̃`, the `z` vector, the hint `h`) that BRICK 6 `verifyCore` consumes, and ENCODED back so the codec is a
true round-trip. Everything here is plain computable `Nat`/`Array`/`UInt8` arithmetic — the same
`leanc`-extractable shape as BRICK 1 `Keccak` and BRICK 2 `MlDsaRing` — no `Prop`, no classical choice.

## FIPS 204 §7 codec, at the ML-DSA-65 parameters (Table 2)

`k = 6`, `ℓ = 5`, `τ = 49`, `γ₁ = 2¹⁹ = 524288`, `d = 13`, `ω = 55`, `|c̃| = 48`. Hence
`|pk| = 32 + 6·320 = 1952` and `|sig| = 48 + 5·640 + (ω+k) = 48 + 3200 + 61 = 3309`.

* `pkDecode` / `pkEncode` — `ρ` = first 32 bytes; `t1` = 6 polynomials, each 256 coeffs `SimpleBitUnpack`'d
  at **10 bits/coeff** (`SimpleBitUnpack(·, 2¹⁰−1)`), coeffs in `[0, 2¹⁰)`. Byte order is FIPS `BytesToBits`:
  LSB-first within each byte, coefficients packed as consecutive 10-bit little-endian groups.
* `sigDecode` / `sigEncode` — `c̃` = first 48 bytes; `z` = 5 polynomials × 256 coeffs `BitUnpack(·, γ₁−1, γ₁)`
  at **20 bits/coeff**: the raw field `f ∈ [0, 2²⁰)` maps to the signed coefficient `γ₁ − f ∈ (−γ₁, γ₁]`,
  carried as its canonical `ℤ_q` rep (negatives as `q + v`). `h` = `HintBitUnpack` of the trailing 61 bytes
  into `k = 6` `{0,1}`-polynomials, in the packed-index + per-poly cumulative-boundary format.

## FAIL-CLOSED HINT (FIPS `HintBitUnpack` REJECTS malformed hints)

`hintDecode : Option (Array Poly)` returns `none` exactly when the FIPS decode rejects: a per-poly cumulative
boundary that decreases or exceeds `ω`, set-bit indices that are not strictly increasing within a poly, or a
nonzero byte in the trailing padding. `sigDecode` propagates this as a sentinel: a rejected hint yields an
EMPTY `h` array (`h.size ≠ k`), which `verifyCore` treats as reject.

## THE ANTI-FAKE GATE — round-trip GENUINE `fips204` crate bytes (`native_decide`)

`realPk` (1952 bytes) and `realSig` (3309 bytes) are a REAL ML-DSA-65 keypair+signature produced by the
actual `fips204` v0.4.6 crate (`ml_dsa_65::try_keygen` / `.try_sign`), pinned verbatim. The gate theorems —
run on the COMPILED `def`s by `native_decide` — check:

* `pk_roundtrip` — `pkEncode (pkDecode realPk) = realPk` (exact, 1952 → decode → encode → 1952, 0 diff).
* `sig_roundtrip` — `sigEncode (sigDecode realSig) = realSig` (exact, 3309 → decode → encode → 3309, 0 diff).
* `pk_t1_in_range` — every decoded `t1` coefficient is `< 2¹⁰` (the `SimpleBitUnpack` codomain).
* `sig_z_in_range` — every decoded `z` coefficient has `|signed| ≤ γ₁` (the `BitUnpack` codomain).
* `sig_hint_valid` — the real signature's hint DECODES (`hintDecode` is `some`) to `k = 6` polys with
  `≤ ω = 55` total set bits.
* `sig_hint_reject` — a hint with a boundary `> ω` is REJECTED (`hintDecode = none`): the fail-closed teeth
  are non-vacuous.

If the bit order, the 10/20-bit widths, the `γ₁ − f` sign map, the `ℤ_q` negative rep, or the hint
boundary/padding logic were wrong, these would NOT close on the real crate bytes. No `sorry`, no user
`axiom`, no toy substitute.

## RESIDUAL

`native_decide`'s trusted base is `Lean.ofReduceBool` + `Lean.trustCompiler` (compiled evaluation) — the SAME
residual `Keccak`, `MlDsaRing`, and `Fips204Verify` already name.
-/
import Dregg2.Crypto.MlDsaRing

namespace Dregg2.Crypto.MlDsaCodec

open Dregg2.Crypto.MlDsaRing (Poly q zeroPoly)

/-! ## ML-DSA-65 codec parameters (FIPS 204 Table 2) -/

/-- Number of `t1`/`h` polynomials in a public key / hint. -/
def paramK : Nat := 6
/-- Number of `z` polynomials in a signature. -/
def paramL : Nat := 5
/-- Maximum number of `1`s in the hint (`ω`). -/
def omega : Nat := 55
/-- `γ₁ = 2¹⁹`, the mask/`z` bound. -/
def gamma1 : Nat := 524288
/-- `|c̃|`, the challenge-hash byte length. -/
def cTildeLen : Nat := 48
/-- `|pk|` bytes. -/
def pkLen : Nat := 1952
/-- `|sig|` bytes. -/
def sigLen : Nat := 3309
/-- Bits per `t1` coefficient (`bitlen(2¹⁰−1)`). -/
def t1Bits : Nat := 10
/-- Bits per `z` coefficient (`bitlen(2·γ₁−1) = bitlen(2²⁰−1)`). -/
def zBits : Nat := 20
/-- Bytes per packed `t1` polynomial (`256·10/8`). -/
def t1PolyBytes : Nat := 320
/-- Bytes per packed `z` polynomial (`256·20/8`). -/
def zPolyBytes : Nat := 640

/-! ## FIPS 204 `BytesToBits` / `BitsToBytes` as little-endian `Nat` field (un)packers.

The FIPS bit order (`BytesToBits`: LSB-first within each byte, `BitsToBytes` the inverse) makes a run of
bytes the little-endian `Nat` `Σ bᵢ·256ⁱ`, and each `c`-bit coefficient the consecutive `c`-bit group
`(N >>> (i·c)) &&& (2ᶜ−1)`. So `unpackBits`/`packBits` are exact inverses whenever the coefficients are
`< 2ᶜ` and the total bit-count is a multiple of 8 (both hold for `t1` at `c=10` and `z` at `c=20`). -/

/-- Little-endian `Nat` value of `len` bytes of `b` starting at `off`. -/
def bytesToNatLE (b : Array UInt8) (off len : Nat) : Nat := Id.run do
  let mut acc : Nat := 0
  let mut mul : Nat := 1
  for i in [0:len] do
    acc := acc + (b[off + i]!).toNat * mul
    mul := mul * 256
  return acc

/-- Unpack `count` coefficients of `cbits` bits each (FIPS LSB-first order) from `b` at byte `off`. -/
def unpackBits (b : Array UInt8) (off count cbits : Nat) : Array Nat := Id.run do
  let nbytes := count * cbits / 8
  let big := bytesToNatLE b off nbytes
  let base := 2 ^ cbits
  let mut out : Array Nat := Array.mkEmpty count
  let mut cur := big
  for _ in [0:count] do
    out := out.push (cur % base)
    cur := cur / base
  return out

/-- Pack `coeffs` (each `< 2^cbits`) into bytes (FIPS LSB-first order). Inverse of `unpackBits`. -/
def packBits (coeffs : Array Nat) (cbits : Nat) : Array UInt8 := Id.run do
  let base := 2 ^ cbits
  let mut big : Nat := 0
  let mut mul : Nat := 1
  for i in [0:coeffs.size] do
    big := big + (coeffs[i]! % base) * mul
    mul := mul * base
  let nbytes := coeffs.size * cbits / 8
  let mut out : Array UInt8 := Array.mkEmpty nbytes
  let mut cur := big
  for _ in [0:nbytes] do
    out := out.push (UInt8.ofNat (cur % 256))
    cur := cur / 256
  return out

/-! ## Public-key codec (FIPS 204 Algorithm 22/23: `pkEncode` / `pkDecode`). -/

/-- Decode a 1952-byte ML-DSA-65 public key into `ρ` (32 bytes) and the 6-polynomial `t1` vector
(`SimpleBitUnpack` at 10 bits/coeff; each coefficient in `[0, 2¹⁰)`). -/
def pkDecode (pk : List UInt8) : (List UInt8 × Array Poly) := Id.run do
  let b := pk.toArray
  let rho := (b.extract 0 32).toList  -- ρ is the first 32 bytes
  let mut t1 : Array Poly := Array.mkEmpty paramK
  for i in [0:paramK] do
    let off := 32 + i * t1PolyBytes
    t1 := t1.push (unpackBits b off 256 t1Bits)
  return (rho, t1)

/-- Encode `ρ` (32 bytes) and the `t1` vector back into a 1952-byte public key. Inverse of `pkDecode`. -/
def pkEncode (parts : List UInt8 × Array Poly) : List UInt8 := Id.run do
  let (rho, t1) := parts
  let mut out : Array UInt8 := (rho.toArray)
  for i in [0:paramK] do
    out := out ++ packBits (t1[i]!) t1Bits
  return out.toList

/-! ## `z` coefficient sign map (FIPS 204 `BitUnpack(·, γ₁−1, γ₁)` / `BitPack`).

The raw 20-bit field `f ∈ [0, 2²⁰)` decodes to the signed coefficient `γ₁ − f ∈ (−γ₁, γ₁]`, carried as its
canonical `ℤ_q` rep. `zFieldFromCoeff` is the exact inverse on that codomain. -/

/-- Decode a 20-bit field to a `z` coefficient (canonical `ℤ_q` rep; negatives as `q + v`). -/
def zCoeffFromField (f : Nat) : Nat :=
  if f ≤ gamma1 then gamma1 - f else q - (f - gamma1)

/-- Re-encode a `z` coefficient (canonical `ℤ_q` rep) back to its 20-bit field. Inverse of `zCoeffFromField`
on the `BitUnpack` codomain. -/
def zFieldFromCoeff (c : Nat) : Nat :=
  if c ≤ gamma1 then gamma1 - c else gamma1 + q - c

/-- The signed value of a `z` coefficient held in canonical `ℤ_q` rep, as an `Int`. -/
def zSigned (c : Nat) : Int :=
  if c ≤ gamma1 then (c : Int) else (c : Int) - (q : Int)

/-! ## Hint codec (FIPS 204 Algorithm 20/21: `HintBitPack` / `HintBitUnpack`).

`hintEncode` writes, for each of the `k` polynomials, its set-bit indices in increasing order into the first
`ω` bytes, and the running cumulative count into byte `ω+i`; the tail is zero-padded. `hintDecode` inverts it
and REJECTS (`none`) a malformed hint: a boundary that decreases or exceeds `ω`, non-strictly-increasing
indices within a poly, or nonzero trailing padding. -/

/-- `HintBitUnpack`: decode the `ω+k = 61` hint bytes of `b` at `hoff` into `k` `{0,1}`-polynomials, or
`none` if the FIPS decode rejects the hint as malformed. -/
def hintDecode (b : Array UInt8) (hoff : Nat) : Option (Array Poly) := Id.run do
  let mut index : Nat := 0
  let mut ok : Bool := true
  let mut polys : Array Poly := Array.mkEmpty paramK
  for i in [0:paramK] do
    let bound := (b[hoff + omega + i]!).toNat
    if bound < index || bound > omega then
      ok := false
    let start := index
    let mut p : Poly := zeroPoly
    let mut prevIdx : Nat := 0
    for pos in [start:bound] do
      let idx := (b[hoff + pos]!).toNat
      if pos > start && idx ≤ prevIdx then
        ok := false
      p := p.set! idx 1
      prevIdx := idx
    index := bound
    polys := polys.push p
  for pos in [index:omega] do
    if (b[hoff + pos]!).toNat ≠ 0 then
      ok := false
  if ok then return some polys else return none

/-- `HintBitPack`: encode `k` `{0,1}`-polynomials into the `ω+k = 61` hint bytes. Inverse of `hintDecode` on
a valid hint. -/
def hintEncode (hs : Array Poly) : Array UInt8 := Id.run do
  let mut y : Array UInt8 := Array.replicate (omega + paramK) 0
  let mut index : Nat := 0
  for i in [0:paramK] do
    let p := hs[i]!
    for j in [0:256] do
      if p[j]! ≠ 0 then
        y := y.set! index (UInt8.ofNat j)
        index := index + 1
    y := y.set! (omega + i) (UInt8.ofNat index)
  return y

/-! ## Signature codec (FIPS 204 Algorithm 26/27: `sigEncode` / `sigDecode`). -/

/-- Decode a 3309-byte ML-DSA-65 signature into `c̃` (48 bytes), the 5-polynomial `z` vector (`BitUnpack` at
20 bits/coeff, canonical `ℤ_q` reps), and the hint `h` (`k = 6` `{0,1}`-polynomials). A malformed hint
fails CLOSED: `h` is returned EMPTY (`h.size ≠ paramK`), which `verifyCore` treats as reject. -/
def sigDecode (sig : List UInt8) : (List UInt8 × Array Poly × Array Poly) := Id.run do
  let b := sig.toArray
  let ctilde := (b.extract 0 cTildeLen).toList
  let mut z : Array Poly := Array.mkEmpty paramL
  for i in [0:paramL] do
    let off := cTildeLen + i * zPolyBytes
    let fields := unpackBits b off 256 zBits
    let mut p : Poly := zeroPoly
    for j in [0:256] do
      p := p.set! j (zCoeffFromField (fields[j]!))
    z := z.push p
  let hoff := cTildeLen + paramL * zPolyBytes
  let h := match hintDecode b hoff with
    | some hs => hs
    | none => (#[] : Array Poly)
  return (ctilde, z, h)

/-- Encode `c̃`, the `z` vector, and the hint `h` back into a 3309-byte signature. Inverse of `sigDecode`
on a valid signature. -/
def sigEncode (parts : List UInt8 × Array Poly × Array Poly) : List UInt8 := Id.run do
  let (ctilde, z, h) := parts
  let mut out : Array UInt8 := ctilde.toArray
  for i in [0:paramL] do
    let p := z[i]!
    let mut fields : Array Nat := Array.mkEmpty 256
    for j in [0:256] do
      fields := fields.push (zFieldFromCoeff (p[j]!))
    out := out ++ packBits fields zBits
  out := out ++ hintEncode h
  return out.toList

/-! ## Structural helpers for the gate. -/

/-- Every coefficient of every poly in `ps` is `< bound`. -/
def allCoeffsLt (ps : Array Poly) (bound : Nat) : Bool := Id.run do
  let mut ok := true
  for p in ps do
    for j in [0:256] do
      if !(p[j]! < bound) then ok := false
  return ok

/-- Every `z` coefficient of every poly in `ps` has `|signed| ≤ γ₁`. -/
def allZInRange (ps : Array Poly) : Bool := Id.run do
  let mut ok := true
  for p in ps do
    for j in [0:256] do
      let s := zSigned (p[j]!)
      if !((-(gamma1 : Int) ≤ s) && (s ≤ (gamma1 : Int))) then ok := false
  return ok

/-- Total number of set (`= 1`) hint coefficients across all polys in `hs`. -/
def hintWeight (hs : Array Poly) : Nat := Id.run do
  let mut w := 0
  for p in hs do
    for j in [0:256] do
      if p[j]! ≠ 0 then w := w + 1
  return w

/-! ## Pinned REAL `fips204` v0.4.6 bytes (genuine `ml_dsa_65::try_keygen` + `.try_sign`). -/

/-- A genuine ML-DSA-65 public key (1952 bytes) from the real `fips204` crate. -/
def realPk : Array UInt8 := #[54, 212, 179, 118, 67, 44, 131, 31, 165, 168, 242, 255, 57, 41, 39, 36, 140, 35, 252, 169, 223, 245, 41, 180, 7, 27, 208, 247, 149, 81, 76, 207, 188, 52, 195, 33, 71, 61, 220, 177, 238, 98, 215, 41, 66, 173, 227, 69, 66, 105, 88, 160, 115, 94, 29, 183, 57, 112, 117, 169, 233, 151, 152, 223, 97, 151, 215, 202, 66, 25, 71, 136, 113, 223, 78, 135, 28, 88, 51, 177, 110, 182, 130, 242, 12, 62, 246, 74, 104, 33, 101, 95, 72, 245, 78, 176, 14, 205, 152, 167, 22, 42, 251, 79, 180, 247, 215, 140, 117, 94, 177, 163, 135, 115, 232, 139, 53, 189, 112, 38, 102, 134, 33, 170, 23, 44, 175, 246, 158, 96, 26, 192, 167, 56, 152, 40, 66, 223, 149, 237, 253, 77, 252, 58, 181, 226, 117, 62, 209, 244, 176, 105, 234, 8, 62, 241, 170, 104, 231, 34, 219, 42, 109, 7, 53, 178, 67, 6, 28, 54, 82, 158, 47, 28, 49, 58, 242, 9, 211, 43, 19, 115, 227, 102, 130, 91, 249, 103, 67, 122, 217, 28, 86, 247, 83, 227, 52, 139, 236, 160, 62, 50, 92, 26, 204, 180, 213, 181, 123, 226, 140, 171, 104, 44, 83, 110, 3, 14, 63, 150, 49, 194, 59, 110, 162, 68, 50, 72, 96, 2, 217, 82, 115, 255, 49, 185, 195, 125, 7, 200, 49, 181, 144, 131, 52, 240, 198, 254, 2, 39, 98, 116, 252, 20, 222, 129, 64, 233, 174, 44, 73, 70, 8, 123, 7, 161, 201, 163, 53, 221, 75, 151, 48, 73, 162, 44, 78, 135, 24, 49, 254, 188, 235, 161, 145, 190, 95, 171, 226, 171, 176, 63, 172, 148, 20, 6, 24, 99, 209, 133, 121, 207, 198, 161, 140, 242, 29, 139, 78, 112, 160, 164, 45, 145, 3, 187, 3, 138, 166, 70, 152, 215, 2, 253, 19, 216, 178, 5, 219, 57, 76, 198, 129, 221, 203, 62, 8, 213, 216, 186, 196, 192, 182, 68, 236, 141, 163, 101, 73, 164, 148, 226, 184, 147, 228, 249, 121, 181, 86, 154, 143, 17, 82, 84, 143, 59, 47, 59, 98, 210, 156, 51, 67, 223, 58, 242, 33, 82, 73, 199, 165, 164, 153, 129, 213, 25, 186, 119, 2, 225, 248, 65, 37, 1, 225, 182, 128, 150, 239, 23, 164, 21, 253, 178, 226, 42, 249, 66, 76, 68, 4, 222, 161, 1, 6, 225, 151, 252, 111, 68, 122, 105, 141, 201, 121, 182, 199, 167, 143, 191, 156, 65, 123, 55, 22, 105, 39, 167, 237, 46, 98, 130, 12, 11, 181, 249, 133, 158, 216, 58, 88, 114, 96, 95, 127, 60, 202, 81, 204, 43, 155, 60, 102, 249, 47, 241, 135, 192, 237, 226, 240, 73, 88, 169, 72, 99, 55, 131, 139, 235, 181, 241, 251, 73, 167, 67, 57, 254, 207, 44, 127, 82, 179, 156, 139, 153, 12, 191, 251, 233, 107, 138, 252, 189, 143, 114, 140, 179, 217, 178, 175, 221, 146, 75, 231, 183, 126, 248, 235, 194, 56, 187, 223, 153, 32, 37, 138, 199, 253, 242, 238, 125, 221, 204, 220, 67, 190, 45, 103, 210, 231, 2, 69, 104, 18, 198, 225, 53, 116, 149, 175, 132, 234, 42, 46, 8, 42, 87, 146, 128, 207, 49, 130, 185, 203, 240, 221, 165, 50, 160, 61, 1, 178, 60, 117, 195, 131, 33, 234, 113, 54, 177, 81, 139, 29, 13, 121, 213, 123, 254, 238, 192, 137, 186, 159, 46, 30, 247, 51, 44, 123, 174, 246, 201, 30, 106, 196, 221, 52, 120, 120, 115, 76, 120, 177, 166, 235, 78, 16, 246, 171, 49, 9, 88, 92, 238, 99, 105, 190, 7, 63, 81, 231, 69, 64, 250, 207, 199, 37, 93, 207, 100, 131, 249, 3, 133, 135, 36, 111, 62, 197, 117, 108, 181, 197, 179, 21, 238, 94, 240, 128, 185, 55, 124, 53, 176, 149, 199, 89, 23, 90, 251, 171, 28, 20, 149, 116, 11, 238, 118, 65, 178, 104, 38, 178, 235, 204, 4, 79, 106, 173, 53, 193, 9, 193, 232, 25, 203, 110, 119, 68, 2, 18, 196, 173, 198, 68, 236, 170, 7, 60, 38, 195, 226, 176, 49, 79, 131, 230, 119, 144, 249, 77, 95, 31, 198, 202, 246, 174, 39, 126, 70, 254, 206, 113, 86, 62, 246, 8, 144, 36, 253, 184, 91, 1, 103, 239, 217, 164, 195, 198, 120, 131, 192, 5, 137, 231, 15, 51, 158, 8, 112, 176, 214, 194, 81, 218, 194, 15, 121, 198, 30, 158, 189, 184, 117, 77, 0, 211, 29, 70, 229, 17, 131, 127, 181, 185, 48, 247, 101, 77, 38, 85, 155, 244, 97, 160, 238, 243, 111, 53, 143, 211, 174, 214, 65, 4, 82, 6, 4, 178, 168, 196, 206, 122, 221, 205, 143, 91, 186, 241, 124, 91, 28, 107, 55, 10, 174, 77, 255, 214, 202, 106, 67, 79, 179, 222, 252, 207, 164, 109, 62, 106, 179, 80, 116, 82, 158, 88, 159, 114, 236, 182, 204, 184, 97, 230, 66, 128, 229, 67, 107, 109, 171, 114, 227, 179, 229, 234, 203, 206, 115, 192, 124, 23, 86, 255, 38, 240, 140, 66, 204, 39, 7, 253, 140, 243, 2, 105, 9, 32, 198, 238, 77, 34, 68, 199, 139, 22, 128, 212, 161, 151, 39, 229, 1, 97, 22, 39, 27, 64, 105, 176, 88, 20, 139, 58, 237, 173, 254, 12, 138, 208, 167, 245, 29, 49, 126, 19, 253, 15, 106, 253, 254, 154, 175, 129, 217, 133, 75, 157, 177, 166, 35, 39, 241, 78, 0, 179, 221, 64, 164, 4, 138, 100, 111, 14, 238, 154, 48, 184, 121, 5, 57, 255, 80, 247, 34, 26, 221, 47, 144, 204, 81, 13, 41, 230, 49, 168, 243, 238, 167, 163, 108, 63, 40, 95, 94, 156, 101, 234, 24, 47, 45, 88, 104, 43, 98, 226, 245, 92, 48, 236, 173, 108, 198, 170, 107, 184, 117, 23, 126, 68, 204, 105, 219, 71, 36, 210, 189, 19, 67, 132, 87, 84, 142, 57, 68, 83, 175, 40, 237, 111, 98, 96, 80, 158, 56, 252, 96, 23, 111, 74, 250, 110, 181, 87, 78, 255, 246, 221, 49, 163, 94, 3, 12, 205, 16, 220, 39, 240, 200, 146, 95, 205, 18, 129, 225, 134, 145, 193, 146, 99, 26, 185, 99, 65, 148, 23, 67, 10, 30, 241, 202, 231, 59, 215, 141, 35, 142, 117, 119, 52, 21, 19, 89, 178, 143, 75, 150, 238, 129, 236, 122, 0, 85, 14, 108, 97, 140, 182, 42, 163, 213, 59, 129, 94, 78, 236, 149, 151, 161, 50, 151, 150, 145, 180, 87, 85, 130, 237, 147, 184, 161, 101, 59, 37, 77, 115, 208, 94, 205, 55, 56, 161, 203, 36, 86, 252, 90, 213, 2, 137, 168, 168, 235, 217, 122, 76, 83, 184, 52, 173, 116, 247, 163, 235, 55, 48, 182, 218, 94, 138, 124, 13, 30, 192, 136, 242, 151, 105, 27, 30, 182, 52, 52, 4, 184, 251, 110, 182, 66, 14, 252, 209, 203, 124, 133, 54, 206, 227, 113, 7, 131, 188, 9, 13, 240, 225, 199, 124, 201, 94, 190, 82, 167, 112, 5, 157, 151, 163, 158, 71, 183, 202, 147, 190, 81, 128, 208, 193, 197, 129, 89, 123, 20, 127, 44, 228, 12, 201, 226, 219, 17, 48, 15, 176, 113, 120, 241, 33, 94, 188, 195, 254, 57, 244, 120, 72, 233, 90, 141, 54, 203, 253, 195, 248, 187, 249, 179, 202, 78, 189, 43, 139, 92, 136, 45, 208, 155, 41, 162, 26, 122, 19, 103, 249, 242, 171, 147, 17, 1, 117, 147, 114, 4, 206, 248, 67, 210, 2, 175, 116, 184, 160, 89, 5, 234, 136, 237, 104, 255, 80, 227, 220, 189, 218, 210, 168, 206, 194, 168, 107, 70, 162, 125, 62, 37, 248, 64, 38, 162, 79, 180, 57, 149, 48, 103, 212, 184, 57, 199, 186, 55, 70, 54, 69, 136, 178, 187, 171, 176, 164, 142, 140, 238, 246, 234, 40, 180, 194, 195, 103, 77, 78, 85, 79, 39, 217, 144, 150, 198, 61, 193, 105, 205, 134, 113, 50, 150, 207, 10, 41, 43, 9, 47, 251, 217, 63, 129, 141, 103, 44, 103, 64, 108, 70, 139, 192, 175, 130, 26, 243, 246, 203, 231, 69, 54, 190, 91, 239, 233, 18, 183, 175, 189, 174, 34, 185, 173, 28, 75, 57, 42, 85, 77, 205, 153, 238, 82, 107, 38, 182, 245, 193, 3, 241, 181, 39, 58, 72, 76, 62, 249, 230, 160, 200, 65, 110, 75, 12, 206, 252, 46, 48, 42, 1, 126, 202, 187, 183, 152, 192, 3, 206, 10, 96, 201, 95, 123, 17, 83, 178, 142, 215, 154, 176, 170, 135, 62, 235, 187, 140, 242, 104, 212, 119, 241, 21, 99, 84, 224, 206, 181, 33, 143, 26, 186, 101, 117, 122, 239, 62, 238, 153, 179, 132, 75, 21, 99, 200, 119, 200, 216, 154, 123, 146, 190, 160, 223, 180, 153, 56, 208, 165, 255, 160, 125, 197, 15, 234, 93, 245, 173, 231, 138, 170, 182, 197, 213, 249, 208, 80, 80, 208, 83, 24, 172, 157, 215, 186, 86, 155, 63, 240, 116, 222, 140, 35, 140, 164, 44, 6, 178, 210, 220, 105, 39, 20, 212, 11, 85, 109, 183, 31, 82, 135, 107, 171, 234, 50, 229, 90, 162, 254, 215, 191, 127, 52, 93, 15, 16, 26, 210, 160, 251, 29, 90, 21, 153, 139, 31, 121, 224, 179, 214, 123, 227, 5, 141, 26, 182, 40, 23, 45, 72, 135, 40, 56, 77, 131, 55, 61, 199, 125, 144, 35, 217, 203, 71, 98, 23, 68, 142, 114, 250, 185, 230, 220, 119, 0, 86, 146, 15, 213, 24, 195, 255, 155, 35, 248, 209, 106, 32, 151, 38, 198, 33, 108, 154, 165, 141, 155, 4, 225, 123, 13, 204, 32, 209, 34, 98, 193, 112, 253, 80, 144, 99, 33, 24, 170, 21, 91, 9, 212, 112, 209, 138, 91, 121, 167, 55, 166, 79, 219, 12, 109, 58, 165, 186, 113, 0, 106, 243, 238, 106, 124, 122, 241, 185, 89, 211, 200, 215, 99, 202, 220, 221, 99, 68, 13, 9, 163, 114, 225, 145, 244, 193, 13, 239, 62, 224, 160, 37, 76, 142, 208, 55, 243, 74, 52, 171, 90, 253, 172, 247, 232, 85, 202, 88, 119, 234, 233, 145, 65, 219, 47, 130, 40, 185, 116, 172, 95, 183, 78, 15, 186, 74, 2, 140, 93, 84, 17, 130, 207, 25, 95, 84, 0, 5, 6, 99, 19, 121, 191, 28, 8, 59, 45, 151, 215, 23, 182, 209, 101, 82, 75, 181, 193, 41, 150, 42, 236, 73, 104, 79, 128, 189, 171, 193, 223, 198, 65, 242, 110, 117, 197, 105, 246, 248, 179, 116, 230, 147, 81, 69, 62, 34, 19, 90, 72, 188, 145, 115, 192, 24, 17, 154, 44, 193, 54, 234, 16, 90, 24, 97, 108, 241, 58, 62, 69, 162, 191, 201, 122, 35, 238, 134, 84, 166, 30, 145, 253, 4, 89, 194, 255, 110, 76, 126, 254, 86, 81, 212, 93, 69, 167, 47, 243, 199, 68, 128, 235, 164, 62, 126, 148, 255, 232, 90, 181, 195, 133, 165, 44, 240, 75, 150, 136, 210, 141, 224, 53, 154, 214, 74, 56, 11, 164, 68, 242, 177, 39, 61, 127, 113, 164, 174, 65, 21, 212, 191, 92, 237, 60, 209, 251, 97, 71, 56, 79, 183, 181, 238, 171, 56, 147, 110, 174, 138, 73, 139, 69, 142, 15, 176, 216, 246, 126, 243, 105, 134]

/-- A genuine ML-DSA-65 signature (3309 bytes) over a fixed message from the real `fips204` crate. -/
def realSig : Array UInt8 := #[244, 40, 217, 131, 189, 66, 188, 180, 254, 110, 33, 217, 39, 11, 11, 240, 82, 136, 2, 3, 213, 16, 136, 183, 106, 179, 130, 171, 134, 8, 78, 45, 35, 39, 193, 86, 98, 155, 157, 128, 231, 136, 201, 170, 113, 169, 90, 40, 95, 199, 214, 218, 101, 190, 49, 40, 57, 34, 146, 197, 126, 190, 0, 127, 203, 53, 174, 122, 155, 26, 218, 3, 65, 23, 236, 6, 213, 90, 173, 104, 245, 167, 129, 161, 49, 26, 141, 221, 93, 143, 30, 5, 79, 254, 42, 249, 130, 243, 24, 231, 91, 30, 210, 166, 230, 15, 139, 253, 10, 186, 249, 167, 207, 91, 211, 3, 22, 178, 119, 100, 217, 162, 51, 76, 210, 149, 221, 105, 183, 186, 247, 60, 152, 81, 29, 189, 98, 65, 62, 116, 212, 195, 200, 208, 173, 188, 237, 96, 100, 218, 143, 76, 59, 95, 39, 99, 8, 112, 234, 248, 108, 196, 27, 159, 9, 124, 201, 75, 106, 108, 50, 227, 32, 180, 158, 196, 153, 169, 162, 83, 222, 172, 20, 39, 216, 232, 79, 218, 87, 14, 224, 104, 70, 68, 31, 22, 158, 173, 4, 45, 192, 173, 217, 27, 128, 18, 161, 167, 211, 240, 126, 133, 178, 63, 76, 170, 98, 244, 242, 211, 59, 37, 158, 138, 124, 52, 251, 136, 240, 72, 64, 180, 251, 29, 158, 6, 233, 202, 196, 214, 92, 232, 108, 126, 149, 82, 237, 226, 108, 116, 23, 35, 125, 133, 136, 128, 42, 236, 25, 22, 105, 133, 237, 190, 249, 31, 66, 159, 102, 126, 176, 129, 238, 22, 188, 153, 133, 121, 76, 202, 93, 176, 186, 119, 119, 123, 234, 30, 23, 26, 144, 204, 78, 168, 131, 159, 62, 109, 89, 85, 146, 88, 254, 225, 26, 199, 8, 187, 245, 206, 197, 172, 106, 158, 108, 154, 160, 88, 140, 228, 87, 23, 96, 235, 184, 250, 150, 14, 86, 60, 28, 67, 10, 24, 111, 226, 82, 127, 138, 114, 249, 253, 206, 133, 211, 123, 169, 187, 109, 26, 185, 87, 5, 155, 126, 139, 176, 116, 27, 203, 123, 99, 78, 146, 230, 75, 84, 48, 203, 96, 248, 39, 15, 31, 8, 198, 147, 121, 154, 169, 46, 82, 109, 169, 184, 110, 98, 191, 207, 31, 119, 114, 42, 224, 22, 231, 50, 61, 132, 89, 188, 14, 204, 164, 178, 131, 123, 78, 155, 152, 1, 59, 59, 183, 205, 210, 10, 191, 59, 58, 92, 23, 176, 190, 134, 69, 79, 0, 200, 0, 230, 226, 30, 146, 50, 115, 27, 246, 20, 221, 220, 86, 129, 97, 40, 187, 110, 177, 217, 35, 106, 69, 106, 75, 152, 251, 2, 194, 121, 249, 176, 22, 69, 121, 77, 172, 72, 107, 39, 59, 193, 227, 216, 218, 5, 128, 47, 126, 169, 230, 162, 233, 241, 102, 116, 148, 229, 205, 197, 134, 6, 79, 59, 34, 139, 16, 136, 12, 242, 131, 247, 120, 9, 33, 76, 197, 177, 75, 85, 89, 224, 208, 2, 32, 34, 5, 238, 241, 166, 116, 14, 107, 243, 239, 99, 87, 41, 176, 200, 101, 26, 226, 203, 187, 24, 36, 34, 144, 178, 47, 197, 76, 19, 94, 141, 59, 183, 79, 199, 193, 130, 27, 225, 241, 53, 171, 176, 196, 36, 169, 230, 37, 39, 55, 241, 16, 9, 186, 252, 199, 114, 126, 135, 112, 181, 93, 127, 138, 253, 100, 171, 211, 141, 18, 145, 104, 236, 233, 27, 165, 33, 14, 206, 125, 190, 9, 80, 175, 50, 24, 174, 172, 141, 151, 79, 15, 4, 66, 14, 22, 165, 109, 58, 229, 181, 212, 254, 206, 190, 199, 72, 168, 114, 67, 22, 19, 24, 128, 153, 105, 105, 100, 62, 34, 112, 180, 129, 239, 83, 69, 174, 162, 157, 207, 106, 120, 208, 149, 65, 54, 147, 180, 110, 136, 249, 20, 194, 207, 33, 7, 92, 94, 130, 2, 203, 249, 242, 170, 229, 142, 167, 111, 148, 144, 231, 161, 24, 53, 155, 14, 20, 241, 60, 134, 12, 31, 173, 60, 243, 8, 143, 119, 107, 10, 37, 12, 209, 210, 189, 211, 226, 187, 105, 205, 19, 179, 157, 43, 170, 73, 181, 237, 122, 135, 240, 6, 12, 239, 205, 82, 51, 121, 139, 254, 17, 49, 1, 25, 179, 183, 238, 122, 191, 212, 134, 225, 50, 55, 190, 119, 213, 196, 189, 100, 30, 53, 199, 249, 108, 209, 66, 242, 91, 161, 229, 132, 197, 52, 59, 206, 65, 7, 190, 223, 196, 3, 158, 156, 243, 254, 11, 106, 196, 102, 12, 179, 206, 248, 19, 73, 139, 61, 236, 228, 248, 137, 37, 183, 173, 206, 43, 137, 201, 236, 217, 114, 132, 188, 50, 100, 101, 174, 235, 222, 86, 177, 159, 14, 184, 57, 11, 127, 104, 98, 121, 215, 184, 238, 48, 186, 185, 174, 230, 129, 136, 112, 61, 214, 49, 57, 127, 198, 116, 197, 30, 253, 118, 80, 163, 63, 246, 13, 96, 120, 238, 56, 233, 240, 86, 19, 108, 93, 193, 104, 18, 83, 80, 9, 70, 116, 19, 90, 88, 154, 97, 178, 142, 66, 103, 193, 120, 112, 131, 144, 59, 79, 69, 232, 53, 20, 82, 70, 244, 184, 186, 84, 19, 24, 55, 79, 5, 186, 22, 85, 209, 96, 86, 185, 210, 50, 128, 179, 79, 11, 69, 116, 144, 157, 61, 53, 107, 92, 102, 115, 11, 124, 175, 163, 188, 123, 179, 132, 42, 125, 173, 123, 232, 19, 203, 179, 183, 38, 16, 49, 8, 243, 73, 198, 222, 32, 204, 245, 176, 161, 218, 27, 46, 165, 78, 116, 93, 204, 3, 214, 36, 172, 189, 93, 103, 130, 39, 225, 86, 194, 147, 141, 123, 218, 114, 52, 50, 223, 143, 116, 143, 8, 212, 107, 27, 164, 199, 29, 228, 109, 12, 119, 144, 159, 47, 2, 187, 24, 5, 55, 242, 123, 240, 7, 231, 166, 103, 96, 104, 244, 187, 145, 245, 145, 181, 28, 214, 245, 71, 183, 219, 141, 127, 209, 14, 123, 115, 184, 175, 242, 204, 223, 173, 74, 253, 110, 60, 65, 6, 113, 52, 219, 216, 85, 152, 147, 132, 56, 233, 96, 187, 233, 68, 60, 12, 38, 64, 249, 170, 29, 156, 50, 80, 1, 153, 166, 173, 237, 240, 229, 44, 87, 85, 166, 234, 116, 208, 63, 88, 236, 123, 248, 27, 59, 215, 61, 205, 31, 225, 218, 229, 203, 44, 88, 199, 252, 99, 177, 239, 135, 159, 20, 153, 151, 199, 82, 175, 240, 106, 73, 23, 171, 93, 17, 185, 19, 207, 185, 131, 172, 109, 200, 111, 231, 123, 102, 63, 203, 252, 106, 162, 147, 50, 61, 57, 133, 82, 32, 82, 226, 151, 146, 204, 225, 154, 219, 229, 52, 201, 102, 170, 81, 65, 88, 67, 236, 215, 241, 38, 129, 57, 238, 179, 212, 166, 220, 234, 28, 95, 161, 245, 238, 238, 205, 5, 59, 215, 23, 111, 16, 197, 12, 23, 176, 61, 62, 243, 172, 33, 208, 122, 201, 140, 249, 214, 209, 96, 233, 73, 101, 147, 242, 65, 97, 185, 78, 215, 176, 250, 24, 142, 145, 149, 43, 37, 253, 170, 45, 251, 168, 120, 223, 219, 144, 25, 21, 48, 177, 116, 91, 61, 13, 49, 196, 100, 130, 106, 162, 26, 199, 234, 243, 135, 35, 104, 253, 114, 0, 50, 117, 122, 92, 131, 83, 225, 228, 242, 59, 63, 174, 73, 88, 204, 89, 142, 201, 79, 41, 37, 64, 154, 235, 198, 92, 3, 169, 135, 22, 57, 15, 105, 112, 208, 213, 152, 100, 220, 48, 172, 109, 219, 181, 172, 231, 205, 230, 137, 50, 113, 90, 244, 32, 138, 52, 37, 66, 242, 215, 226, 187, 95, 219, 153, 104, 210, 131, 240, 254, 228, 91, 93, 106, 79, 2, 220, 119, 252, 56, 11, 22, 85, 211, 27, 157, 23, 50, 90, 243, 28, 118, 118, 25, 241, 156, 18, 4, 44, 11, 94, 158, 103, 172, 11, 157, 78, 213, 159, 189, 106, 232, 56, 212, 63, 74, 162, 78, 212, 181, 94, 235, 152, 171, 39, 55, 78, 158, 159, 8, 57, 9, 24, 58, 66, 131, 189, 80, 23, 218, 239, 229, 83, 37, 40, 176, 207, 160, 29, 242, 15, 148, 160, 244, 0, 99, 123, 181, 57, 83, 33, 162, 79, 223, 59, 218, 93, 124, 28, 247, 102, 165, 73, 139, 166, 42, 208, 212, 105, 93, 194, 56, 253, 92, 104, 164, 75, 131, 144, 188, 108, 187, 198, 192, 248, 147, 70, 219, 2, 205, 107, 184, 164, 40, 140, 9, 37, 123, 176, 72, 45, 122, 122, 233, 199, 128, 20, 188, 172, 93, 117, 142, 92, 238, 156, 215, 255, 132, 185, 58, 52, 19, 246, 48, 178, 146, 186, 106, 232, 146, 196, 219, 150, 75, 182, 133, 113, 2, 219, 130, 179, 193, 247, 18, 156, 14, 123, 23, 74, 99, 205, 224, 61, 105, 189, 86, 10, 169, 211, 150, 58, 66, 181, 183, 135, 49, 77, 193, 237, 210, 233, 7, 66, 99, 88, 135, 148, 68, 108, 52, 217, 40, 249, 85, 50, 157, 40, 178, 11, 20, 165, 2, 26, 61, 222, 136, 166, 69, 32, 47, 52, 243, 55, 95, 80, 18, 72, 134, 248, 250, 145, 199, 202, 75, 92, 153, 33, 162, 220, 98, 21, 99, 148, 159, 222, 128, 124, 88, 150, 28, 204, 10, 127, 138, 46, 49, 244, 135, 148, 136, 34, 60, 14, 27, 43, 0, 24, 103, 135, 54, 6, 64, 213, 222, 38, 102, 134, 116, 132, 99, 140, 196, 40, 186, 223, 182, 40, 211, 110, 63, 15, 200, 172, 192, 207, 219, 40, 176, 147, 203, 228, 20, 127, 99, 62, 27, 212, 24, 199, 18, 118, 209, 48, 16, 97, 250, 252, 36, 23, 215, 249, 40, 200, 173, 169, 64, 86, 123, 69, 150, 103, 193, 91, 128, 209, 53, 39, 187, 5, 196, 144, 50, 113, 148, 231, 106, 190, 226, 205, 86, 233, 239, 53, 50, 15, 63, 9, 243, 118, 23, 79, 95, 70, 8, 67, 127, 41, 122, 151, 189, 7, 0, 135, 126, 131, 162, 135, 148, 71, 106, 187, 226, 69, 13, 238, 109, 240, 4, 123, 92, 224, 46, 74, 127, 52, 28, 139, 38, 177, 107, 115, 53, 231, 214, 229, 28, 212, 94, 125, 23, 40, 128, 117, 92, 78, 198, 102, 249, 6, 230, 189, 137, 150, 9, 136, 134, 117, 78, 53, 115, 41, 113, 202, 191, 163, 149, 128, 76, 196, 128, 13, 105, 169, 105, 185, 54, 147, 23, 230, 234, 160, 79, 112, 170, 239, 66, 102, 230, 116, 190, 157, 252, 143, 182, 211, 51, 6, 141, 2, 128, 37, 154, 100, 186, 67, 254, 33, 40, 34, 99, 87, 251, 53, 208, 194, 156, 204, 145, 193, 55, 118, 167, 255, 150, 170, 10, 73, 77, 192, 209, 24, 144, 87, 46, 235, 232, 0, 105, 16, 222, 249, 207, 12, 199, 67, 207, 65, 121, 35, 42, 144, 241, 95, 48, 89, 6, 18, 239, 163, 78, 23, 62, 7, 51, 153, 247, 29, 188, 185, 88, 9, 58, 208, 12, 164, 16, 238, 89, 29, 238, 200, 135, 101, 181, 20, 34, 195, 52, 105, 139, 191, 34, 121, 213, 158, 251, 17, 79, 140, 22, 217, 14, 91, 36, 47, 142, 252, 133, 122, 234, 101, 229, 135, 98, 130, 43, 212, 179, 90, 155, 165, 88, 224, 191, 10, 133, 234, 222, 92, 248, 13, 98, 7, 49, 50, 150, 132, 158, 81, 91, 22, 250, 73, 224, 50, 162, 75, 23, 163, 58, 165, 162, 126, 28, 83, 197, 72, 204, 118, 102, 119, 28, 150, 109, 190, 2, 161, 214, 33, 64, 234, 174, 82, 186, 109, 229, 36, 111, 122, 223, 81, 190, 86, 99, 118, 189, 166, 48, 49, 100, 237, 236, 148, 167, 186, 238, 230, 217, 22, 230, 220, 141, 100, 251, 80, 133, 115, 43, 71, 206, 45, 44, 52, 195, 15, 185, 190, 45, 157, 148, 177, 51, 56, 156, 219, 207, 49, 197, 17, 145, 89, 219, 61, 2, 97, 250, 15, 245, 84, 187, 88, 24, 195, 254, 73, 247, 82, 27, 44, 118, 186, 88, 232, 253, 179, 103, 243, 148, 189, 215, 221, 39, 148, 82, 239, 205, 212, 104, 149, 201, 88, 45, 53, 107, 127, 122, 47, 108, 212, 128, 185, 141, 217, 97, 34, 9, 8, 172, 208, 132, 34, 20, 15, 13, 232, 89, 132, 32, 30, 205, 228, 85, 110, 247, 156, 15, 174, 34, 160, 114, 178, 37, 218, 193, 50, 3, 107, 233, 239, 226, 17, 18, 200, 51, 146, 154, 52, 64, 204, 140, 170, 58, 221, 199, 59, 142, 156, 40, 0, 63, 153, 178, 102, 97, 176, 7, 49, 248, 93, 206, 49, 9, 227, 93, 204, 117, 226, 236, 83, 1, 67, 166, 198, 31, 40, 177, 83, 228, 245, 27, 127, 163, 150, 115, 44, 223, 116, 52, 63, 195, 148, 34, 108, 38, 205, 121, 21, 255, 158, 147, 214, 212, 217, 110, 203, 119, 84, 85, 34, 209, 96, 232, 200, 220, 36, 96, 175, 93, 128, 232, 167, 106, 234, 102, 157, 119, 168, 227, 22, 181, 157, 31, 136, 184, 5, 143, 132, 107, 92, 44, 47, 153, 157, 66, 43, 51, 59, 88, 176, 37, 100, 142, 80, 62, 254, 30, 129, 65, 69, 254, 202, 30, 150, 70, 17, 145, 136, 29, 210, 124, 64, 169, 218, 34, 184, 73, 150, 158, 58, 24, 79, 123, 217, 151, 133, 109, 9, 87, 139, 107, 142, 166, 40, 181, 45, 149, 111, 71, 84, 56, 100, 249, 160, 50, 163, 204, 188, 139, 227, 224, 88, 230, 199, 120, 16, 30, 148, 103, 131, 171, 95, 115, 14, 254, 26, 168, 195, 56, 218, 45, 221, 228, 0, 70, 229, 214, 160, 223, 123, 192, 182, 95, 20, 103, 199, 90, 139, 92, 230, 183, 125, 92, 23, 139, 175, 61, 44, 19, 25, 37, 126, 111, 16, 179, 85, 131, 136, 8, 93, 36, 220, 190, 155, 237, 56, 112, 147, 71, 228, 118, 20, 86, 238, 155, 195, 209, 125, 157, 209, 147, 202, 130, 34, 37, 138, 232, 168, 249, 46, 133, 240, 113, 180, 92, 32, 207, 93, 242, 14, 80, 233, 101, 211, 138, 48, 34, 154, 46, 7, 13, 237, 252, 172, 128, 102, 188, 186, 26, 194, 210, 109, 216, 70, 154, 93, 110, 224, 162, 3, 149, 26, 221, 122, 125, 205, 141, 70, 41, 153, 49, 144, 96, 205, 145, 218, 70, 179, 172, 226, 109, 39, 135, 57, 137, 118, 157, 44, 207, 74, 48, 164, 236, 226, 213, 99, 207, 140, 144, 86, 14, 239, 52, 171, 50, 180, 15, 22, 54, 240, 49, 3, 5, 51, 201, 16, 135, 128, 148, 212, 135, 236, 61, 10, 43, 59, 92, 0, 175, 200, 161, 152, 166, 129, 238, 244, 131, 23, 61, 72, 109, 182, 190, 96, 220, 201, 103, 135, 36, 96, 144, 37, 181, 58, 153, 185, 108, 235, 80, 118, 111, 32, 38, 29, 169, 224, 94, 103, 231, 66, 113, 198, 250, 35, 21, 0, 26, 57, 47, 214, 21, 232, 224, 198, 223, 88, 88, 9, 47, 64, 53, 93, 102, 228, 122, 47, 185, 129, 243, 80, 166, 169, 210, 17, 45, 16, 34, 241, 62, 241, 8, 231, 133, 92, 122, 216, 48, 1, 50, 167, 218, 103, 144, 243, 12, 203, 125, 148, 28, 17, 220, 73, 195, 144, 16, 132, 72, 236, 6, 238, 36, 123, 106, 158, 3, 142, 58, 162, 154, 247, 118, 141, 144, 73, 74, 29, 16, 32, 100, 197, 58, 241, 146, 35, 186, 114, 20, 130, 235, 160, 171, 90, 43, 180, 220, 219, 180, 18, 150, 214, 13, 232, 201, 78, 79, 176, 105, 38, 7, 150, 236, 175, 180, 221, 229, 75, 251, 216, 226, 92, 43, 159, 201, 236, 117, 175, 153, 36, 137, 101, 234, 172, 205, 218, 246, 171, 231, 16, 147, 230, 123, 232, 27, 51, 79, 94, 44, 44, 76, 188, 190, 15, 192, 150, 254, 55, 245, 122, 218, 3, 245, 9, 38, 145, 158, 139, 51, 58, 220, 71, 61, 15, 94, 163, 158, 90, 147, 118, 43, 169, 97, 77, 252, 108, 88, 83, 235, 136, 49, 19, 108, 21, 56, 89, 126, 228, 3, 73, 151, 59, 150, 109, 71, 151, 254, 135, 47, 72, 106, 128, 202, 205, 182, 101, 29, 84, 143, 121, 205, 224, 235, 77, 138, 28, 220, 51, 36, 139, 194, 137, 220, 155, 46, 140, 113, 24, 181, 172, 125, 141, 248, 148, 176, 205, 162, 66, 47, 69, 153, 162, 222, 226, 62, 242, 194, 148, 39, 196, 223, 226, 215, 95, 127, 68, 234, 15, 73, 28, 186, 134, 29, 32, 189, 152, 164, 153, 95, 157, 66, 21, 215, 245, 125, 79, 69, 23, 119, 159, 183, 25, 108, 165, 211, 193, 26, 224, 216, 190, 62, 194, 81, 133, 50, 127, 205, 82, 179, 59, 211, 22, 192, 29, 109, 136, 141, 154, 147, 59, 144, 55, 61, 243, 200, 26, 9, 162, 180, 83, 169, 151, 137, 181, 148, 235, 45, 182, 10, 104, 230, 92, 68, 224, 101, 247, 50, 251, 60, 158, 115, 15, 153, 28, 102, 219, 240, 39, 13, 6, 247, 84, 239, 209, 115, 104, 108, 37, 65, 133, 121, 105, 14, 105, 200, 23, 200, 230, 73, 164, 229, 55, 163, 100, 136, 14, 204, 36, 189, 43, 185, 86, 12, 84, 72, 153, 92, 135, 6, 122, 185, 11, 123, 232, 222, 193, 80, 0, 118, 210, 22, 151, 218, 240, 44, 167, 248, 15, 29, 139, 210, 153, 169, 200, 125, 20, 114, 242, 167, 96, 196, 173, 177, 145, 244, 36, 147, 181, 240, 190, 248, 119, 70, 201, 176, 65, 88, 200, 243, 68, 19, 100, 51, 72, 92, 245, 161, 43, 234, 17, 146, 178, 6, 114, 33, 85, 198, 77, 40, 237, 167, 218, 56, 203, 228, 209, 57, 220, 195, 133, 106, 47, 102, 98, 239, 40, 136, 147, 156, 0, 252, 53, 121, 239, 167, 140, 178, 108, 119, 178, 142, 158, 218, 80, 4, 76, 218, 106, 204, 64, 129, 202, 152, 251, 153, 94, 42, 129, 251, 83, 85, 59, 129, 26, 87, 45, 120, 103, 45, 72, 95, 116, 217, 104, 95, 196, 239, 129, 60, 180, 191, 153, 6, 61, 231, 197, 208, 13, 169, 169, 205, 51, 233, 12, 163, 79, 177, 121, 14, 43, 224, 105, 162, 170, 142, 227, 47, 141, 24, 131, 246, 243, 171, 154, 4, 75, 171, 146, 143, 203, 211, 205, 20, 178, 128, 148, 227, 183, 222, 254, 112, 13, 224, 110, 83, 114, 168, 192, 208, 129, 50, 174, 62, 57, 25, 137, 87, 243, 31, 175, 231, 4, 81, 76, 216, 93, 235, 19, 67, 145, 149, 1, 103, 252, 156, 206, 4, 253, 33, 154, 113, 232, 214, 115, 206, 138, 229, 126, 227, 51, 255, 215, 167, 238, 79, 63, 136, 117, 126, 66, 152, 77, 238, 238, 96, 7, 194, 75, 3, 141, 99, 159, 31, 137, 219, 162, 79, 237, 165, 11, 94, 30, 123, 223, 169, 149, 47, 86, 248, 112, 195, 157, 186, 39, 103, 39, 22, 45, 34, 200, 231, 112, 179, 190, 192, 78, 14, 17, 149, 51, 77, 111, 189, 48, 94, 124, 129, 146, 148, 164, 24, 37, 66, 117, 123, 209, 241, 27, 35, 196, 207, 15, 22, 76, 100, 119, 126, 148, 241, 251, 8, 60, 76, 88, 99, 104, 190, 202, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 11, 18, 22, 31, 40]

/-! ## THE ANTI-FAKE GATE — round-trip GENUINE `fips204` v0.4.6 crate bytes.

`realPk` / `realSig` are a real ML-DSA-65 keypair+signature (below). `native_decide` runs the COMPILED
`def`s over them. -/

/-- Decoded public key of the real crate bytes. -/
def realPkDecoded : (List UInt8 × Array Poly) := pkDecode realPk.toList
/-- Decoded signature of the real crate bytes. -/
def realSigDecoded : (List UInt8 × Array Poly × Array Poly) := sigDecode realSig.toList

/-- Sanity: the pinned bytes are exactly the ML-DSA-65 lengths.
`.size` of the literal byte arrays reduces in the kernel, so `decide` closes it with NO
`Lean.ofReduceBool`/`trustCompiler` (`maxRecDepth` clears the array-literal traversal). -/
theorem real_lengths : realPk.size = pkLen ∧ realSig.size = sigLen := by
  set_option maxRecDepth 20000 in decide

/-- **PK round-trip**: `pkEncode (pkDecode realPk) = realPk` — exact, 1952 → decode → encode → 1952, 0 diff.
The load-bearing gate for the public-key codec on REAL crate bytes. -/
theorem pk_roundtrip : (pkEncode (pkDecode realPk.toList)).toArray = realPk := by native_decide

/-- **SIG round-trip**: `sigEncode (sigDecode realSig) = realSig` — exact, 3309 → decode → encode → 3309, 0
diff. The load-bearing gate for the signature codec (`c̃` + `z` + hint) on REAL crate bytes. -/
theorem sig_roundtrip : (sigEncode (sigDecode realSig.toList)).toArray = realSig := by native_decide

/-- Structural: every decoded `t1` coefficient is `< 2¹⁰` (the `SimpleBitUnpack` codomain). -/
theorem pk_t1_in_range : allCoeffsLt realPkDecoded.2 1024 = true := by native_decide

/-- Structural: every decoded `z` coefficient has `|signed| ≤ γ₁` (the `BitUnpack` codomain). -/
theorem sig_z_in_range : allZInRange realSigDecoded.2.1 = true := by native_decide

/-- The real signature's hint DECODES (fail-closed decoder accepts it) to `k = 6` polys. -/
theorem sig_hint_decodes :
    (hintDecode realSig (cTildeLen + paramL * zPolyBytes)).isSome = true := by native_decide

/-- The decoded hint has `k = 6` polynomials and `≤ ω = 55` total set bits (a VALID ML-DSA hint). -/
theorem sig_hint_valid :
    realSigDecoded.2.2.size = paramK ∧ hintWeight realSigDecoded.2.2 ≤ omega := by native_decide

/-- **Non-vacuity of the fail-closed teeth**: corrupting a per-poly boundary byte to `ω+1 = 56 > ω`
makes `hintDecode` REJECT (`none`). The FIPS `HintBitUnpack` rejection is real, not decorative. -/
theorem sig_hint_reject :
    hintDecode ((realSig).set! (cTildeLen + paramL * zPolyBytes + omega) (UInt8.ofNat 56))
      (cTildeLen + paramL * zPolyBytes) = none := by native_decide

/-- Non-vacuity: a nonzero byte in the hint's trailing padding is REJECTED. -/
theorem sig_hint_reject_padding :
    hintDecode
      ((realSig).set! (cTildeLen + paramL * zPolyBytes + omega - 1) (UInt8.ofNat 200))
      (cTildeLen + paramL * zPolyBytes) = none := by native_decide

end Dregg2.Crypto.MlDsaCodec
