/-
# `Dregg2.Crypto.MlKemCodec` — the REAL ML-KEM-768 byte codec (FIPS 203 §4.2.1), as EXECUTABLE `def`s.

BRICK K3 of replacing the `A = 1`, `n = 1` scalar caricature in `Fips203Kem.lean` with the real
ML-KEM-768 encaps/decaps. Where K1 (`MlKemRing`) built the negacyclic ring `R_q = ℤ_q[X]/(X²⁵⁶+1)` and the
incomplete Kyber NTT, this module is the byte-faithful interop layer with the deployed `ml-kem` v0.2.3 crate
(the SAME crate `dregg-pq/src/hybrid_kem.rs` runs): the 1184-byte encapsulation key, the 1088-byte
ciphertext, and the 2400-byte decapsulation key are DECODED into the ring objects (`t̂`, `ρ`, `u`, `v`, `ŝ`)
that BRICK K4 encaps/decaps consumes, and ENCODED back so the codec is a true round-trip. Everything here is
plain computable `Nat`/`Array`/`UInt8` arithmetic — the same `leanc`-extractable shape as K1 `MlKemRing`,
`Keccak`, and `MlDsaCodec` — no `Prop`, no classical choice.

## ML-KEM-768 codec parameters (FIPS 203 §8, Table)

`k = 3`, `d = 12` (NTT-domain `t̂`/`ŝ` coeffs, `< q`), `du = 10` (ciphertext `u` compression), `dv = 4`
(ciphertext `v` compression), `n = 256`, `q = 3329`. Hence
* `|ek| = 3·(256·12/8) + 32 = 3·384 + 32 = 1152 + 32 = 1184`,
* `|ct| = 3·(256·10/8) + (256·4/8) = 3·320 + 128 = 960 + 128 = 1088`,
* `|dk| = 3·384 + |ek| + 32 + 32 = 1152 + 1184 + 32 + 32 = 2400` (`dk_pke ‖ ek ‖ H(ek) ‖ z`).

## FIPS 203 `ByteEncode_d` / `ByteDecode_d` (Algorithms 5, 6)

The FIPS bit order (`BytesToBits` LSB-first within each byte, `BitsToBytes` the inverse) makes a run of bytes
the little-endian `Nat` `Σ bᵢ·256ⁱ`, and each `d`-bit coefficient the consecutive `d`-bit group
`(N >>> (i·d)) &&& (2ᵈ−1)`. `byteEncode`/`byteDecode` pack/unpack the 256 coefficients LSB-first. For `d = 12`
the field modulus is `q` (`ByteDecode₁₂` reduces mod `q`); for `d < 12` (the compressed `u`, `v`) it is `2ᵈ`.
They are exact inverses whenever the coefficients are `< 2ᵈ` (and `< q` for `d = 12`) — which holds for a
valid `t̂`/`ŝ` (`< q`) and for compressed `u`/`v` (`< 2^{du}`, `< 2^{dv}`).

## FIPS 203 `Compress_d` / `Decompress_d` (§4.2.1)

`Compress_d(x) = ⌈(2ᵈ/q)·x⌋ mod 2ᵈ` and `Decompress_d(y) = ⌈(q/2ᵈ)·y⌋`, with `⌈·⌋` **round-half-up**.
Carried out in exact integer arithmetic:
* `compress d x = ((2·2ᵈ·x + q) / (2·q)) mod 2ᵈ` — `⌊(2ᵈx)/q + ½⌋ = ⌊(2·2ᵈx + q)/(2q)⌋`, then `mod 2ᵈ`
  (the round can hit `2ᵈ` when `x` is near `q`, which wraps to `0`).
* `decompress d y = (2·q·y + 2ᵈ) / (2·2ᵈ)` — `⌊(qy)/2ᵈ + ½⌋ = ⌊(2qy + 2ᵈ)/2^{d+1}⌋`.
Applied componentwise, `decompressPoly` maps a compressed field to a genuine `R_q` ring element (the shape
K4 decaps needs), and `compressPoly` maps it back. Because `2ᵈ < q` at both `du = 10` and `dv = 4`,
`Compress_d ∘ Decompress_d = id` on `[0, 2ᵈ)` — the inverse-consistency the ciphertext round-trip needs.

## THE ANTI-FAKE GATE — round-trip GENUINE `ml-kem` v0.2.3 crate bytes (`native_decide`)

`realEk` (1184 B), `realDk` (2400 B), `realCt` (1088 B) are a REAL ML-KEM-768 keypair + ciphertext produced
by the actual `ml-kem` v0.2.3 crate (`MlKem768::generate` → `ek.as_bytes()`/`dk.as_bytes()`;
`ek.encapsulate` → `ct.as_slice()`), pinned verbatim; `realSs` (32 B) is the shared secret, and the
generator confirmed `dk.decapsulate(ct) == ss` before pinning. The gate theorems — run on the COMPILED
`def`s by `native_decide` — check:

* `ek_roundtrip` — `ekEncode (ekDecode realEk) = realEk` (exact, 1184 → decode → encode → 1184, 0 diff).
* `ct_roundtrip` — `ctEncode (ctDecode realCt) = realCt` (exact, 1088 → decode → encode → 1088, 0 diff): this
  exercises `Compress ∘ Decompress` being inverse-consistent on REAL compressed ciphertext data.
* `dk_embeds_ek` — the `ek` sub-slice `dkDecode` recovers from `realDk` equals `realEk` (the `dk_pke ‖ ek ‖
  H(ek) ‖ z` layout is located correctly).
* `ek_that_lt_q` — every decoded `t̂` coefficient is `< q` (the `ByteDecode₁₂` codomain).
* `compress_lt` — `Compress_d(x) < 2ᵈ` for every `x` (`d = 10` and `d = 4`).
* `compress_decompress_id` — `Compress_d(Decompress_d(y)) = y` for every `y < 2ᵈ` (`d = 10`, `d = 4`): the
  inverse-consistency is a THEOREM over the whole field, not just the sampled bytes — non-vacuous.

If the bit order, the 10/12/4-bit widths, the round-half-up in `Compress`/`Decompress`, or the `dk` layout
were wrong, these would NOT close on the real crate bytes. No `sorry`, no user `axiom`, no toy substitute.

## RESIDUAL

`native_decide`'s trusted base is `Lean.ofReduceBool` + `Lean.trustCompiler` (compiled evaluation) — the SAME
residual `MlKemRing`, `Keccak`, `MlDsaCodec`, and `Fips204Verify` already name.
-/
import Dregg2.Crypto.MlKemRing

namespace Dregg2.Crypto.MlKemCodec

open Dregg2.Crypto.MlKemRing (Poly q zeroPoly)

/-! ## ML-KEM-768 codec parameters (FIPS 203 §8). -/

/-- Number of `t̂`/`ŝ`/`u` polynomials (module rank `k`). -/
def paramK : Nat := 3
/-- Bits per NTT-domain (`t̂`, `ŝ`) coefficient: `d = 12` (coeffs `< q`). -/
def dCoeff : Nat := 12
/-- Ciphertext `u` compression width `du = 10`. -/
def du : Nat := 10
/-- Ciphertext `v` compression width `dv = 4`. -/
def dv : Nat := 4
/-- Bytes per `ByteEncode_d`'d polynomial: `256·d/8 = 32·d`. -/
def polyBytes (d : Nat) : Nat := 32 * d
/-- `|ek|` bytes. -/
def ekLen : Nat := 1184
/-- `|ct|` bytes. -/
def ctLen : Nat := 1088
/-- `|dk|` bytes. -/
def dkLen : Nat := 2400

/-! ## FIPS 203 `ByteEncode_d` / `ByteDecode_d` (Algorithms 5, 6) as little-endian `Nat` (un)packers. -/

/-- Little-endian `Nat` value of `len` bytes of `b` starting at `off`. -/
def bytesToNatLE (b : Array UInt8) (off len : Nat) : Nat := Id.run do
  let mut acc : Nat := 0
  let mut mul : Nat := 1
  for i in [0:len] do
    acc := acc + (b[off + i]!).toNat * mul
    mul := mul * 256
  return acc

/-- **`ByteEncode_d`** (FIPS 203 Alg 5): pack the 256 coefficients of `f` (each taken `mod 2ᵈ`) into `32·d`
bytes, LSB-first. -/
def byteEncode (d : Nat) (f : Poly) : List UInt8 := Id.run do
  let base := 2 ^ d
  let mut big : Nat := 0
  let mut mul : Nat := 1
  for i in [0:256] do
    big := big + (f[i]! % base) * mul
    mul := mul * base
  let nbytes := polyBytes d
  let mut out : Array UInt8 := Array.mkEmpty nbytes
  let mut cur := big
  for _ in [0:nbytes] do
    out := out.push (UInt8.ofNat (cur % 256))
    cur := cur / 256
  return out.toList

/-- **`ByteDecode_d`** core (FIPS 203 Alg 6): unpack 256 coefficients of `d` bits each from `b` at byte
`off`, LSB-first. For `d = 12` the field modulus is `q` (reduce mod `q`); for `d < 12` it is `2ᵈ` (the raw
`d`-bit value is already `< 2ᵈ`). -/
def byteDecodeAt (d : Nat) (b : Array UInt8) (off : Nat) : Poly := Id.run do
  let base := 2 ^ d
  let nbytes := polyBytes d
  let big := bytesToNatLE b off nbytes
  let mut out : Poly := zeroPoly
  let mut cur := big
  for i in [0:256] do
    let v := cur % base
    cur := cur / base
    out := out.set! i (if d == 12 then v % q else v)
  return out

/-- `ByteDecode_d` on a byte list (decodes the first `32·d` bytes). Inverse of `byteEncode`. -/
def byteDecode (d : Nat) (bytes : List UInt8) : Poly := byteDecodeAt d bytes.toArray 0

/-! ## FIPS 203 `Compress_d` / `Decompress_d` (§4.2.1), round-half-up in exact integer arithmetic. -/

/-- **`Compress_d(x) = ⌈(2ᵈ/q)·x⌋ mod 2ᵈ`** (round-half-up): `⌊(2·2ᵈ·x + q)/(2q)⌋ mod 2ᵈ`. -/
def compress (d : Nat) (x : Nat) : Nat :=
  let base := 2 ^ d
  ((2 * base * (x % q) + q) / (2 * q)) % base

/-- **`Decompress_d(y) = ⌈(q/2ᵈ)·y⌋`** (round-half-up): `⌊(2·q·y + 2ᵈ)/2^{d+1}⌋`. Result in `[0, q)`. -/
def decompress (d : Nat) (y : Nat) : Nat :=
  let base := 2 ^ d
  (2 * q * (y % base) + base) / (2 * base)

/-- `Compress_d` applied to every coefficient. -/
def compressPoly (d : Nat) (p : Poly) : Poly := Id.run do
  let mut out : Poly := zeroPoly
  for i in [0:256] do
    out := out.set! i (compress d p[i]!)
  return out

/-- `Decompress_d` applied to every coefficient (compressed field → genuine `R_q` ring element). -/
def decompressPoly (d : Nat) (p : Poly) : Poly := Id.run do
  let mut out : Poly := zeroPoly
  for i in [0:256] do
    out := out.set! i (decompress d p[i]!)
  return out

/-! ## Encapsulation-key codec (FIPS 203 Alg 7/8 `K-PKE.KeyGen` byte forms): `ek = ByteEncode₁₂(t̂) ‖ ρ`. -/

/-- Decode a 1184-byte encapsulation key into `t̂` (3 polynomials, `ByteDecode₁₂`, coeffs `< q`) and `ρ`
(the trailing 32 bytes). -/
def ekDecode (ek : List UInt8) : (Array Poly × List UInt8) := Id.run do
  let b := ek.toArray
  let mut tHat : Array Poly := Array.mkEmpty paramK
  for i in [0:paramK] do
    tHat := tHat.push (byteDecodeAt dCoeff b (i * polyBytes dCoeff))
  let rho := (b.extract (paramK * polyBytes dCoeff) (paramK * polyBytes dCoeff + 32)).toList
  return (tHat, rho)

/-- Encode `t̂` (3 polynomials, `ByteEncode₁₂`) and `ρ` back into a 1184-byte encapsulation key. Inverse of
`ekDecode`. -/
def ekEncode (parts : Array Poly × List UInt8) : List UInt8 := Id.run do
  let (tHat, rho) := parts
  let mut out : Array UInt8 := Array.mkEmpty ekLen
  for i in [0:paramK] do
    out := out ++ (byteEncode dCoeff tHat[i]!).toArray
  out := out ++ rho.toArray
  return out.toList

/-! ## Ciphertext codec (FIPS 203 Alg 13/14 `K-PKE.Encrypt`/`Decrypt` byte forms):
`ct = ByteEncode_{du}(Compress_{du}(u)) ‖ ByteEncode_{dv}(Compress_{dv}(v))`. -/

/-- Decode a 1088-byte ciphertext into `u` (3 polynomials: `ByteDecode_{du}` → `Decompress_{du}`, genuine
`R_q` ring elements) and `v` (1 polynomial: `ByteDecode_{dv}` → `Decompress_{dv}`). -/
def ctDecode (ct : List UInt8) : (Array Poly × Poly) := Id.run do
  let b := ct.toArray
  let mut u : Array Poly := Array.mkEmpty paramK
  for i in [0:paramK] do
    let field := byteDecodeAt du b (i * polyBytes du)
    u := u.push (decompressPoly du field)
  let vField := byteDecodeAt dv b (paramK * polyBytes du)
  let v := decompressPoly dv vField
  return (u, v)

/-- Encode `u` (3 polynomials, `Compress_{du}` → `ByteEncode_{du}`) and `v` (`Compress_{dv}` →
`ByteEncode_{dv}`) back into a 1088-byte ciphertext. Inverse of `ctDecode`. -/
def ctEncode (parts : Array Poly × Poly) : List UInt8 := Id.run do
  let (u, v) := parts
  let mut out : Array UInt8 := Array.mkEmpty ctLen
  for i in [0:paramK] do
    out := out ++ (byteEncode du (compressPoly du u[i]!)).toArray
  out := out ++ (byteEncode dv (compressPoly dv v)).toArray
  return out.toList

/-! ## Decapsulation-key codec (FIPS 203 §8): `dk = dk_pke ‖ ek ‖ H(ek) ‖ z`, with
`dk_pke = ByteEncode₁₂(ŝ)`. `dkDecode` reaches all four fields. -/

/-- Decode a 2400-byte decapsulation key into `ŝ` (3 polynomials, `ByteDecode₁₂`), the embedded 1184-byte
`ek`, `H(ek)` (32 bytes), and `z` (32 bytes). -/
def dkDecode (dk : List UInt8) : (Array Poly × List UInt8 × List UInt8 × List UInt8) := Id.run do
  let b := dk.toArray
  let mut sHat : Array Poly := Array.mkEmpty paramK
  for i in [0:paramK] do
    sHat := sHat.push (byteDecodeAt dCoeff b (i * polyBytes dCoeff))
  let ekOff := paramK * polyBytes dCoeff          -- 1152
  let ek := (b.extract ekOff (ekOff + ekLen)).toList
  let hOff := ekOff + ekLen                        -- 2336
  let hek := (b.extract hOff (hOff + 32)).toList
  let zOff := hOff + 32                             -- 2368
  let z := (b.extract zOff (zOff + 32)).toList
  return (sHat, ek, hek, z)

/-! ## Structural helpers for the gate. -/

/-- Every coefficient of every poly in `ps` is `< bound`. -/
def allCoeffsLt (ps : Array Poly) (bound : Nat) : Bool := Id.run do
  let mut ok := true
  for p in ps do
    for j in [0:256] do
      if !(p[j]! < bound) then ok := false
  return ok

/-- `Compress_d(x) < 2ᵈ` for every `x < hi`. -/
def compressAllLt (d hi : Nat) : Bool := Id.run do
  let base := 2 ^ d
  let mut ok := true
  for x in [0:hi] do
    if !(compress d x < base) then ok := false
  return ok

/-- `Compress_d(Decompress_d(y)) = y` for every `y < 2ᵈ` (inverse-consistency over the whole field). -/
def compressDecompressId (d : Nat) : Bool := Id.run do
  let base := 2 ^ d
  let mut ok := true
  for y in [0:base] do
    if compress d (decompress d y) ≠ y then ok := false
  return ok

/-! ## Pinned REAL `ml-kem` v0.2.3 bytes (genuine `MlKem768::generate` + `ek.encapsulate`;
`dk.decapsulate(ct) == ss` was confirmed by the generator before pinning). -/

def realEk : Array UInt8 := #[88, 89, 154, 56, 119, 39, 91, 134, 143, 64, 6, 123, 41, 160, 95, 51, 140, 25, 80, 18, 88, 162, 185, 202, 214, 184, 177, 224, 11, 24, 167, 87, 126, 168, 35, 201, 248, 122, 106, 19, 81, 205, 151, 64, 138, 188, 224, 143, 254, 177, 166, 21, 144, 181, 69, 56, 60, 178, 144, 168, 162, 17, 33, 118, 167, 146, 39, 185, 185, 74, 68, 39, 136, 215, 170, 184, 251, 127, 63, 100, 27, 172, 180, 129, 84, 103, 164, 63, 155, 84, 29, 55, 164, 181, 54, 81, 120, 212, 121, 237, 89, 100, 239, 251, 141, 242, 211, 188, 227, 251, 5, 73, 248, 83, 133, 226, 77, 127, 4, 62, 229, 185, 160, 57, 149, 148, 3, 76, 66, 12, 71, 157, 128, 180, 195, 139, 16, 125, 61, 86, 27, 201, 194, 16, 45, 121, 152, 168, 182, 141, 193, 230, 50, 58, 248, 47, 22, 56, 139, 139, 57, 125, 134, 133, 144, 85, 121, 191, 8, 136, 69, 112, 226, 50, 99, 139, 131, 215, 170, 175, 173, 136, 100, 151, 146, 73, 97, 248, 190, 82, 240, 111, 3, 123, 148, 241, 165, 106, 223, 177, 92, 111, 138, 48, 27, 6, 8, 73, 229, 25, 243, 192, 75, 111, 56, 186, 111, 39, 89, 159, 3, 206, 110, 113, 173, 247, 217, 182, 42, 70, 128, 98, 59, 122, 131, 252, 132, 160, 186, 80, 109, 4, 13, 184, 1, 25, 10, 28, 149, 192, 216, 81, 224, 211, 25, 212, 67, 184, 101, 96, 46, 152, 9, 200, 129, 8, 11, 61, 12, 96, 181, 186, 152, 242, 180, 145, 8, 232, 24, 36, 117, 77, 108, 192, 25, 85, 112, 14, 54, 140, 148, 92, 188, 3, 133, 210, 37, 251, 5, 142, 143, 7, 171, 179, 176, 98, 144, 101, 51, 165, 167, 179, 169, 4, 152, 27, 234, 178, 182, 181, 137, 47, 192, 82, 74, 163, 89, 168, 9, 110, 188, 176, 159, 27, 90, 167, 69, 16, 181, 168, 80, 50, 110, 144, 115, 224, 51, 37, 223, 65, 137, 0, 120, 119, 244, 212, 125, 40, 0, 95, 219, 41, 2, 45, 178, 138, 138, 27, 206, 40, 139, 14, 8, 114, 73, 192, 51, 137, 211, 201, 57, 198, 201, 38, 165, 121, 137, 43, 243, 107, 130, 115, 30, 93, 225, 162, 126, 177, 204, 105, 247, 89, 181, 149, 105, 110, 6, 27, 22, 235, 57, 83, 160, 6, 147, 18, 69, 156, 123, 70, 171, 182, 30, 66, 172, 48, 209, 232, 93, 168, 161, 105, 158, 16, 31, 206, 211, 153, 220, 41, 35, 20, 208, 189, 165, 16, 195, 145, 161, 73, 110, 138, 54, 12, 213, 159, 55, 42, 52, 228, 132, 45, 185, 131, 6, 123, 75, 165, 178, 8, 104, 134, 162, 167, 243, 201, 193, 137, 131, 20, 183, 88, 187, 16, 105, 126, 193, 188, 138, 166, 84, 0, 5, 128, 126, 25, 226, 188, 41, 66, 140, 193, 113, 151, 118, 12, 199, 19, 194, 29, 176, 113, 16, 52, 103, 69, 197, 133, 102, 8, 246, 23, 245, 153, 75, 114, 240, 163, 83, 165, 114, 2, 26, 143, 36, 234, 180, 220, 162, 74, 47, 176, 187, 32, 8, 182, 144, 87, 193, 158, 162, 153, 151, 227, 133, 33, 147, 157, 164, 35, 8, 165, 73, 69, 196, 50, 6, 200, 133, 38, 253, 187, 59, 129, 49, 9, 211, 198, 100, 35, 184, 111, 84, 2, 45, 134, 37, 50, 224, 24, 93, 70, 104, 133, 40, 185, 47, 188, 135, 101, 211, 179, 201, 158, 213, 44, 197, 101, 152, 93, 0, 164, 119, 49, 83, 242, 27, 53, 186, 245, 4, 99, 201, 132, 33, 98, 192, 226, 21, 73, 159, 219, 123, 154, 20, 129, 59, 42, 110, 6, 181, 170, 232, 164, 121, 131, 22, 157, 83, 241, 156, 42, 130, 182, 154, 169, 74, 101, 5, 33, 38, 229, 101, 27, 181, 94, 25, 213, 51, 100, 210, 103, 170, 177, 177, 194, 40, 16, 175, 154, 102, 224, 74, 182, 35, 87, 84, 49, 236, 52, 11, 64, 50, 229, 105, 7, 137, 170, 150, 125, 199, 1, 196, 88, 0, 95, 183, 51, 119, 150, 26, 49, 228, 184, 210, 76, 95, 21, 251, 154, 212, 203, 178, 193, 244, 113, 91, 160, 147, 118, 161, 154, 85, 108, 69, 191, 230, 15, 250, 86, 3, 67, 248, 77, 166, 229, 143, 23, 208, 109, 41, 27, 42, 126, 74, 189, 202, 156, 194, 80, 48, 87, 187, 24, 136, 92, 85, 88, 14, 243, 23, 202, 231, 165, 184, 105, 99, 11, 179, 80, 230, 116, 14, 173, 26, 130, 28, 66, 145, 248, 182, 3, 241, 60, 108, 112, 12, 118, 251, 98, 20, 61, 28, 44, 244, 2, 61, 143, 178, 124, 141, 165, 190, 80, 201, 180, 249, 140, 47, 194, 243, 194, 199, 12, 119, 199, 198, 182, 118, 178, 71, 127, 162, 0, 240, 214, 146, 124, 201, 207, 129, 25, 99, 73, 161, 153, 108, 105, 39, 8, 250, 10, 240, 7, 101, 116, 227, 187, 107, 24, 76, 188, 128, 4, 49, 151, 70, 101, 217, 15, 220, 177, 64, 65, 140, 202, 105, 243, 107, 95, 53, 170, 152, 105, 118, 236, 43, 123, 3, 151, 174, 244, 232, 188, 119, 170, 164, 70, 215, 161, 51, 113, 97, 146, 24, 191, 220, 209, 79, 136, 211, 101, 64, 119, 15, 61, 124, 40, 198, 37, 73, 31, 146, 175, 7, 186, 31, 14, 129, 75, 210, 132, 108, 208, 136, 107, 127, 91, 63, 213, 80, 199, 231, 102, 167, 165, 35, 61, 174, 181, 90, 89, 202, 177, 126, 133, 114, 19, 246, 6, 128, 233, 80, 152, 18, 15, 14, 245, 113, 103, 101, 12, 228, 164, 196, 59, 146, 119, 55, 184, 43, 85, 119, 87, 173, 103, 74, 148, 81, 191, 109, 6, 41, 173, 87, 42, 115, 198, 197, 238, 218, 136, 100, 28, 139, 54, 233, 164, 80, 76, 11, 247, 134, 21, 5, 40, 155, 214, 68, 10, 153, 204, 39, 102, 74, 84, 72, 66, 37, 172, 69, 55, 94, 10, 104, 154, 23, 80, 221, 146, 3, 169, 38, 182, 7, 182, 177, 95, 36, 67, 51, 182, 3, 252, 160, 63, 101, 106, 93, 213, 131, 181, 214, 130, 82, 4, 247, 105, 149, 218, 43, 52, 88, 175, 148, 89, 77, 125, 50, 169, 64, 185, 63, 222, 41, 99, 139, 171, 106, 151, 220, 141, 21, 132, 43, 6, 27, 18, 211, 90, 165, 223, 88, 44, 133, 102, 120, 111, 244, 66, 81, 198, 61, 213, 216, 96, 45, 3, 100, 74, 6, 28, 14, 211, 104, 79, 113, 55, 115, 165, 91, 69, 10, 138, 214, 108, 142, 28, 50, 180, 241, 36, 187, 136, 105, 4, 158, 220, 106, 5, 168, 125, 170, 246, 30, 126, 236, 7, 99, 215, 138, 191, 7, 144, 232, 128, 14, 133, 101, 230, 122, 182, 12, 85, 129, 30, 123, 53, 166, 129, 203, 124, 10, 194]
def realDk : Array UInt8 := #[88, 186, 194, 83, 170, 37, 8, 180, 182, 193, 167, 25, 147, 162, 172, 162, 202, 165, 1, 145, 132, 15, 230, 35, 184, 92, 133, 254, 70, 161, 214, 112, 94, 122, 219, 181, 245, 234, 186, 64, 37, 170, 64, 5, 12, 160, 44, 25, 89, 210, 175, 113, 186, 70, 158, 87, 160, 161, 102, 161, 135, 165, 139, 1, 22, 7, 1, 150, 40, 46, 208, 26, 28, 145, 185, 193, 150, 156, 73, 226, 13, 199, 26, 10, 27, 145, 66, 218, 248, 85, 47, 128, 186, 194, 242, 100, 226, 235, 5, 151, 154, 202, 92, 231, 174, 182, 234, 62, 220, 196, 81, 151, 233, 167, 5, 68, 122, 84, 107, 100, 25, 235, 39, 129, 50, 163, 146, 27, 108, 172, 117, 66, 218, 136, 24, 153, 252, 132, 95, 216, 128, 104, 0, 135, 210, 24, 200, 76, 122, 18, 3, 20, 27, 39, 220, 145, 10, 184, 112, 74, 123, 103, 76, 149, 170, 53, 38, 161, 151, 161, 103, 169, 48, 202, 164, 119, 45, 35, 234, 72, 81, 9, 64, 49, 113, 165, 240, 188, 152, 157, 208, 114, 82, 196, 96, 89, 219, 81, 114, 7, 66, 18, 195, 185, 112, 51, 90, 67, 99, 17, 7, 124, 158, 18, 89, 115, 185, 35, 3, 9, 80, 120, 223, 85, 136, 16, 161, 68, 198, 65, 173, 162, 122, 200, 194, 179, 125, 17, 128, 96, 76, 248, 12, 108, 56, 10, 230, 235, 19, 148, 187, 144, 57, 54, 22, 250, 147, 190, 165, 1, 186, 25, 225, 103, 63, 27, 25, 13, 25, 156, 76, 59, 146, 223, 107, 133, 130, 123, 44, 119, 193, 101, 195, 68, 29, 226, 18, 99, 34, 123, 1, 88, 188, 131, 97, 152, 66, 231, 224, 201, 43, 217, 184, 89, 118, 154, 46, 55, 102, 184, 227, 199, 170, 101, 88, 189, 97, 190, 155, 249, 49, 254, 115, 89, 170, 113, 112, 214, 122, 0, 21, 70, 149, 91, 198, 59, 186, 53, 75, 227, 213, 30, 90, 10, 163, 112, 241, 73, 120, 202, 204, 129, 244, 114, 154, 17, 20, 166, 51, 24, 72, 66, 108, 99, 41, 104, 91, 42, 59, 226, 7, 199, 68, 120, 77, 249, 242, 191, 207, 146, 115, 110, 114, 155, 54, 224, 198, 197, 248, 48, 37, 178, 204, 198, 225, 78, 16, 204, 77, 243, 179, 197, 158, 137, 37, 134, 76, 4, 179, 231, 159, 138, 26, 130, 140, 4, 208, 150, 188, 136, 44, 213, 146, 90, 33, 82, 99, 51, 48, 172, 251, 142, 143, 220, 90, 227, 167, 132, 248, 236, 8, 77, 213, 145, 158, 23, 113, 2, 69, 132, 167, 140, 130, 104, 231, 90, 228, 231, 46, 38, 89, 199, 48, 251, 195, 160, 228, 103, 55, 19, 122, 2, 60, 56, 254, 104, 115, 92, 2, 119, 237, 25, 53, 218, 81, 155, 243, 225, 87, 65, 227, 100, 148, 249, 62, 44, 86, 162, 169, 91, 83, 230, 55, 157, 101, 9, 45, 169, 69, 82, 207, 137, 113, 80, 130, 169, 15, 146, 60, 244, 133, 49, 48, 55, 135, 103, 249, 26, 70, 68, 8, 232, 41, 78, 212, 128, 46, 205, 235, 32, 183, 213, 206, 2, 133, 12, 73, 74, 115, 54, 145, 192, 192, 215, 205, 56, 187, 124, 168, 169, 39, 135, 4, 140, 242, 137, 145, 39, 128, 178, 231, 121, 143, 146, 179, 151, 67, 200, 76, 53, 214, 127, 23, 162, 141, 73, 216, 200, 216, 199, 155, 193, 106, 198, 167, 73, 140, 57, 122, 55, 5, 102, 64, 61, 226, 66, 36, 247, 19, 50, 68, 141, 186, 152, 50, 217, 113, 63, 168, 203, 71, 211, 42, 86, 118, 100, 87, 156, 188, 48, 176, 85, 87, 130, 137, 157, 211, 120, 17, 190, 211, 87, 226, 233, 116, 241, 38, 103, 28, 226, 198, 3, 226, 176, 222, 228, 57, 67, 33, 194, 199, 139, 159, 2, 161, 75, 25, 117, 20, 181, 226, 116, 55, 132, 66, 175, 245, 96, 187, 100, 19, 121, 148, 65, 122, 232, 189, 138, 117, 21, 97, 76, 39, 61, 193, 77, 113, 92, 59, 122, 203, 161, 229, 21, 193, 208, 84, 179, 104, 35, 76, 93, 140, 201, 69, 164, 78, 197, 74, 99, 4, 44, 42, 87, 183, 147, 207, 72, 55, 81, 138, 121, 172, 200, 185, 234, 27, 45, 152, 113, 179, 200, 185, 119, 27, 51, 66, 194, 145, 62, 154, 49, 104, 134, 1, 107, 117, 81, 54, 171, 18, 67, 228, 219, 143, 11, 87, 163, 209, 170, 192, 41, 225, 117, 126, 2, 125, 130, 200, 114, 12, 105, 180, 12, 42, 191, 59, 179, 104, 163, 212, 199, 216, 214, 92, 149, 49, 173, 222, 201, 71, 95, 25, 85, 92, 39, 160, 3, 117, 7, 36, 217, 118, 232, 235, 199, 168, 44, 147, 139, 52, 103, 95, 50, 32, 187, 40, 34, 247, 195, 205, 236, 66, 101, 41, 195, 201, 167, 212, 109, 147, 196, 196, 140, 139, 21, 42, 218, 57, 157, 244, 75, 245, 232, 19, 164, 248, 136, 219, 65, 57, 104, 6, 196, 20, 52, 44, 63, 160, 93, 40, 161, 75, 212, 246, 63, 182, 104, 65, 173, 131, 185, 123, 134, 45, 134, 21, 33, 206, 0, 170, 75, 115, 56, 11, 58, 120, 244, 155, 134, 161, 171, 30, 41, 0, 153, 80, 197, 43, 202, 20, 81, 160, 183, 46, 73, 2, 48, 99, 195, 101, 168, 3, 21, 240, 195, 177, 163, 52, 58, 49, 217, 205, 97, 232, 15, 31, 139, 127, 214, 212, 35, 160, 160, 20, 110, 98, 96, 113, 1, 118, 243, 20, 21, 197, 92, 72, 160, 38, 104, 148, 146, 53, 29, 3, 27, 101, 247, 42, 120, 167, 33, 151, 170, 0, 216, 196, 66, 188, 214, 150, 206, 185, 207, 95, 1, 98, 242, 19, 100, 81, 214, 192, 219, 129, 65, 227, 103, 47, 156, 180, 15, 148, 67, 157, 89, 162, 69, 84, 114, 173, 188, 170, 140, 30, 1, 114, 102, 176, 177, 12, 71, 68, 27, 72, 171, 213, 9, 150, 180, 153, 72, 140, 217, 27, 247, 155, 36, 136, 226, 52, 188, 180, 79, 75, 87, 111, 67, 67, 129, 250, 115, 163, 30, 252, 121, 125, 105, 1, 233, 213, 167, 182, 82, 9, 135, 172, 121, 248, 148, 172, 137, 168, 64, 232, 19, 176, 172, 120, 168, 49, 151, 180, 11, 230, 207, 75, 233, 101, 228, 232, 20, 218, 50, 178, 226, 139, 99, 152, 23, 173, 32, 232, 197, 114, 138, 72, 161, 208, 74, 180, 204, 198, 180, 224, 164, 43, 244, 25, 153, 232, 70, 28, 160, 63, 33, 178, 105, 64, 208, 26, 29, 187, 125, 47, 25, 20, 10, 232, 152, 160, 208, 199, 79, 170, 2, 140, 32, 182, 156, 121, 167, 88, 89, 154, 56, 119, 39, 91, 134, 143, 64, 6, 123, 41, 160, 95, 51, 140, 25, 80, 18, 88, 162, 185, 202, 214, 184, 177, 224, 11, 24, 167, 87, 126, 168, 35, 201, 248, 122, 106, 19, 81, 205, 151, 64, 138, 188, 224, 143, 254, 177, 166, 21, 144, 181, 69, 56, 60, 178, 144, 168, 162, 17, 33, 118, 167, 146, 39, 185, 185, 74, 68, 39, 136, 215, 170, 184, 251, 127, 63, 100, 27, 172, 180, 129, 84, 103, 164, 63, 155, 84, 29, 55, 164, 181, 54, 81, 120, 212, 121, 237, 89, 100, 239, 251, 141, 242, 211, 188, 227, 251, 5, 73, 248, 83, 133, 226, 77, 127, 4, 62, 229, 185, 160, 57, 149, 148, 3, 76, 66, 12, 71, 157, 128, 180, 195, 139, 16, 125, 61, 86, 27, 201, 194, 16, 45, 121, 152, 168, 182, 141, 193, 230, 50, 58, 248, 47, 22, 56, 139, 139, 57, 125, 134, 133, 144, 85, 121, 191, 8, 136, 69, 112, 226, 50, 99, 139, 131, 215, 170, 175, 173, 136, 100, 151, 146, 73, 97, 248, 190, 82, 240, 111, 3, 123, 148, 241, 165, 106, 223, 177, 92, 111, 138, 48, 27, 6, 8, 73, 229, 25, 243, 192, 75, 111, 56, 186, 111, 39, 89, 159, 3, 206, 110, 113, 173, 247, 217, 182, 42, 70, 128, 98, 59, 122, 131, 252, 132, 160, 186, 80, 109, 4, 13, 184, 1, 25, 10, 28, 149, 192, 216, 81, 224, 211, 25, 212, 67, 184, 101, 96, 46, 152, 9, 200, 129, 8, 11, 61, 12, 96, 181, 186, 152, 242, 180, 145, 8, 232, 24, 36, 117, 77, 108, 192, 25, 85, 112, 14, 54, 140, 148, 92, 188, 3, 133, 210, 37, 251, 5, 142, 143, 7, 171, 179, 176, 98, 144, 101, 51, 165, 167, 179, 169, 4, 152, 27, 234, 178, 182, 181, 137, 47, 192, 82, 74, 163, 89, 168, 9, 110, 188, 176, 159, 27, 90, 167, 69, 16, 181, 168, 80, 50, 110, 144, 115, 224, 51, 37, 223, 65, 137, 0, 120, 119, 244, 212, 125, 40, 0, 95, 219, 41, 2, 45, 178, 138, 138, 27, 206, 40, 139, 14, 8, 114, 73, 192, 51, 137, 211, 201, 57, 198, 201, 38, 165, 121, 137, 43, 243, 107, 130, 115, 30, 93, 225, 162, 126, 177, 204, 105, 247, 89, 181, 149, 105, 110, 6, 27, 22, 235, 57, 83, 160, 6, 147, 18, 69, 156, 123, 70, 171, 182, 30, 66, 172, 48, 209, 232, 93, 168, 161, 105, 158, 16, 31, 206, 211, 153, 220, 41, 35, 20, 208, 189, 165, 16, 195, 145, 161, 73, 110, 138, 54, 12, 213, 159, 55, 42, 52, 228, 132, 45, 185, 131, 6, 123, 75, 165, 178, 8, 104, 134, 162, 167, 243, 201, 193, 137, 131, 20, 183, 88, 187, 16, 105, 126, 193, 188, 138, 166, 84, 0, 5, 128, 126, 25, 226, 188, 41, 66, 140, 193, 113, 151, 118, 12, 199, 19, 194, 29, 176, 113, 16, 52, 103, 69, 197, 133, 102, 8, 246, 23, 245, 153, 75, 114, 240, 163, 83, 165, 114, 2, 26, 143, 36, 234, 180, 220, 162, 74, 47, 176, 187, 32, 8, 182, 144, 87, 193, 158, 162, 153, 151, 227, 133, 33, 147, 157, 164, 35, 8, 165, 73, 69, 196, 50, 6, 200, 133, 38, 253, 187, 59, 129, 49, 9, 211, 198, 100, 35, 184, 111, 84, 2, 45, 134, 37, 50, 224, 24, 93, 70, 104, 133, 40, 185, 47, 188, 135, 101, 211, 179, 201, 158, 213, 44, 197, 101, 152, 93, 0, 164, 119, 49, 83, 242, 27, 53, 186, 245, 4, 99, 201, 132, 33, 98, 192, 226, 21, 73, 159, 219, 123, 154, 20, 129, 59, 42, 110, 6, 181, 170, 232, 164, 121, 131, 22, 157, 83, 241, 156, 42, 130, 182, 154, 169, 74, 101, 5, 33, 38, 229, 101, 27, 181, 94, 25, 213, 51, 100, 210, 103, 170, 177, 177, 194, 40, 16, 175, 154, 102, 224, 74, 182, 35, 87, 84, 49, 236, 52, 11, 64, 50, 229, 105, 7, 137, 170, 150, 125, 199, 1, 196, 88, 0, 95, 183, 51, 119, 150, 26, 49, 228, 184, 210, 76, 95, 21, 251, 154, 212, 203, 178, 193, 244, 113, 91, 160, 147, 118, 161, 154, 85, 108, 69, 191, 230, 15, 250, 86, 3, 67, 248, 77, 166, 229, 143, 23, 208, 109, 41, 27, 42, 126, 74, 189, 202, 156, 194, 80, 48, 87, 187, 24, 136, 92, 85, 88, 14, 243, 23, 202, 231, 165, 184, 105, 99, 11, 179, 80, 230, 116, 14, 173, 26, 130, 28, 66, 145, 248, 182, 3, 241, 60, 108, 112, 12, 118, 251, 98, 20, 61, 28, 44, 244, 2, 61, 143, 178, 124, 141, 165, 190, 80, 201, 180, 249, 140, 47, 194, 243, 194, 199, 12, 119, 199, 198, 182, 118, 178, 71, 127, 162, 0, 240, 214, 146, 124, 201, 207, 129, 25, 99, 73, 161, 153, 108, 105, 39, 8, 250, 10, 240, 7, 101, 116, 227, 187, 107, 24, 76, 188, 128, 4, 49, 151, 70, 101, 217, 15, 220, 177, 64, 65, 140, 202, 105, 243, 107, 95, 53, 170, 152, 105, 118, 236, 43, 123, 3, 151, 174, 244, 232, 188, 119, 170, 164, 70, 215, 161, 51, 113, 97, 146, 24, 191, 220, 209, 79, 136, 211, 101, 64, 119, 15, 61, 124, 40, 198, 37, 73, 31, 146, 175, 7, 186, 31, 14, 129, 75, 210, 132, 108, 208, 136, 107, 127, 91, 63, 213, 80, 199, 231, 102, 167, 165, 35, 61, 174, 181, 90, 89, 202, 177, 126, 133, 114, 19, 246, 6, 128, 233, 80, 152, 18, 15, 14, 245, 113, 103, 101, 12, 228, 164, 196, 59, 146, 119, 55, 184, 43, 85, 119, 87, 173, 103, 74, 148, 81, 191, 109, 6, 41, 173, 87, 42, 115, 198, 197, 238, 218, 136, 100, 28, 139, 54, 233, 164, 80, 76, 11, 247, 134, 21, 5, 40, 155, 214, 68, 10, 153, 204, 39, 102, 74, 84, 72, 66, 37, 172, 69, 55, 94, 10, 104, 154, 23, 80, 221, 146, 3, 169, 38, 182, 7, 182, 177, 95, 36, 67, 51, 182, 3, 252, 160, 63, 101, 106, 93, 213, 131, 181, 214, 130, 82, 4, 247, 105, 149, 218, 43, 52, 88, 175, 148, 89, 77, 125, 50, 169, 64, 185, 63, 222, 41, 99, 139, 171, 106, 151, 220, 141, 21, 132, 43, 6, 27, 18, 211, 90, 165, 223, 88, 44, 133, 102, 120, 111, 244, 66, 81, 198, 61, 213, 216, 96, 45, 3, 100, 74, 6, 28, 14, 211, 104, 79, 113, 55, 115, 165, 91, 69, 10, 138, 214, 108, 142, 28, 50, 180, 241, 36, 187, 136, 105, 4, 158, 220, 106, 5, 168, 125, 170, 246, 30, 126, 236, 7, 99, 215, 138, 191, 7, 144, 232, 128, 14, 133, 101, 230, 122, 182, 12, 85, 129, 30, 123, 53, 166, 129, 203, 124, 10, 194, 86, 66, 244, 123, 72, 222, 45, 227, 27, 145, 245, 101, 7, 14, 40, 58, 42, 171, 153, 33, 97, 32, 6, 253, 186, 160, 118, 110, 137, 34, 17, 236, 182, 61, 246, 64, 133, 123, 184, 199, 29, 2, 107, 50, 116, 193, 38, 106, 161, 175, 232, 177, 211, 168, 173, 210, 70, 253, 136, 112, 221, 122, 0, 84]
def realCt : Array UInt8 := #[50, 90, 9, 9, 74, 55, 251, 149, 25, 3, 171, 119, 116, 116, 67, 169, 24, 151, 227, 193, 218, 136, 206, 70, 96, 93, 112, 127, 133, 245, 1, 185, 2, 101, 57, 182, 249, 122, 152, 156, 201, 17, 41, 143, 239, 137, 207, 133, 247, 213, 185, 141, 32, 215, 187, 138, 223, 158, 50, 181, 202, 60, 38, 64, 195, 133, 58, 196, 182, 241, 189, 125, 153, 94, 123, 203, 241, 167, 153, 149, 186, 57, 232, 212, 84, 240, 183, 46, 90, 2, 170, 155, 142, 244, 171, 83, 76, 200, 21, 147, 144, 170, 250, 11, 208, 140, 163, 88, 150, 149, 186, 199, 237, 26, 1, 45, 100, 132, 231, 234, 98, 222, 88, 218, 102, 14, 153, 129, 61, 156, 142, 215, 38, 10, 117, 2, 15, 92, 119, 183, 154, 0, 119, 154, 28, 113, 44, 127, 154, 254, 69, 208, 231, 22, 215, 114, 20, 108, 134, 126, 197, 75, 238, 199, 173, 12, 173, 124, 120, 183, 176, 224, 49, 0, 47, 13, 109, 153, 29, 209, 172, 129, 189, 108, 253, 106, 160, 9, 100, 199, 123, 96, 201, 28, 249, 201, 184, 86, 181, 185, 43, 210, 86, 56, 82, 132, 59, 102, 219, 19, 31, 207, 197, 176, 96, 125, 96, 246, 45, 28, 68, 28, 133, 5, 10, 148, 118, 57, 68, 39, 249, 254, 26, 236, 217, 150, 101, 175, 174, 252, 137, 150, 24, 200, 184, 11, 219, 41, 199, 37, 133, 179, 203, 5, 127, 246, 4, 198, 136, 150, 198, 36, 101, 217, 209, 23, 11, 126, 55, 60, 227, 174, 95, 255, 110, 115, 19, 78, 179, 154, 45, 197, 175, 74, 71, 47, 67, 79, 47, 93, 113, 136, 200, 127, 12, 104, 8, 118, 80, 34, 152, 75, 12, 210, 168, 220, 172, 115, 11, 33, 87, 77, 160, 90, 7, 236, 158, 67, 217, 178, 197, 128, 120, 169, 163, 43, 125, 240, 26, 247, 198, 109, 156, 63, 203, 212, 226, 235, 198, 176, 235, 173, 109, 29, 226, 188, 128, 27, 76, 4, 47, 25, 8, 108, 218, 113, 146, 42, 125, 62, 19, 54, 236, 83, 29, 156, 75, 12, 49, 209, 105, 239, 220, 105, 178, 118, 205, 132, 202, 239, 57, 16, 216, 97, 253, 80, 60, 237, 9, 148, 77, 42, 174, 240, 57, 229, 64, 21, 93, 191, 214, 191, 202, 155, 108, 248, 161, 119, 105, 56, 255, 32, 116, 169, 163, 60, 140, 65, 231, 41, 143, 207, 244, 155, 72, 108, 52, 102, 99, 216, 20, 250, 55, 107, 179, 123, 194, 151, 247, 98, 148, 92, 49, 234, 159, 242, 147, 84, 212, 216, 84, 154, 15, 157, 216, 79, 108, 247, 101, 179, 229, 52, 56, 212, 94, 90, 155, 127, 46, 197, 151, 242, 199, 32, 235, 187, 127, 102, 196, 210, 129, 186, 117, 53, 16, 237, 246, 37, 108, 67, 57, 143, 211, 240, 241, 23, 44, 118, 180, 167, 123, 98, 138, 79, 252, 127, 159, 171, 143, 76, 212, 172, 153, 134, 237, 78, 66, 147, 110, 166, 136, 238, 202, 24, 228, 56, 9, 171, 187, 48, 71, 108, 56, 165, 162, 138, 249, 170, 137, 74, 31, 130, 25, 140, 146, 252, 161, 167, 178, 56, 186, 79, 179, 124, 57, 56, 28, 201, 71, 202, 34, 232, 127, 177, 36, 254, 115, 115, 31, 214, 89, 11, 228, 56, 212, 74, 88, 120, 32, 133, 108, 161, 227, 13, 140, 241, 48, 202, 96, 80, 206, 233, 193, 255, 33, 165, 172, 236, 196, 236, 162, 30, 123, 241, 27, 85, 204, 217, 109, 64, 55, 168, 96, 176, 141, 236, 26, 140, 164, 89, 166, 12, 231, 221, 156, 64, 210, 167, 201, 65, 199, 150, 164, 230, 114, 33, 31, 89, 99, 95, 132, 87, 94, 96, 177, 29, 47, 197, 210, 209, 104, 40, 221, 212, 237, 52, 74, 177, 188, 182, 45, 17, 94, 243, 31, 89, 88, 170, 181, 0, 103, 245, 64, 204, 121, 213, 251, 234, 27, 246, 189, 165, 111, 29, 107, 237, 140, 254, 52, 202, 91, 0, 112, 187, 196, 27, 197, 154, 233, 28, 60, 137, 110, 211, 211, 80, 255, 76, 124, 95, 16, 176, 222, 203, 206, 66, 212, 179, 186, 48, 254, 179, 84, 190, 62, 6, 173, 81, 149, 202, 131, 210, 75, 150, 205, 91, 116, 239, 132, 168, 66, 44, 51, 209, 242, 182, 3, 184, 248, 178, 213, 217, 164, 43, 82, 144, 55, 150, 221, 120, 47, 98, 37, 216, 129, 184, 193, 67, 252, 40, 189, 128, 230, 161, 54, 104, 158, 147, 106, 190, 82, 148, 113, 9, 162, 25, 14, 77, 23, 88, 143, 16, 154, 142, 39, 210, 214, 55, 140, 25, 230, 134, 175, 54, 137, 141, 74, 234, 234, 110, 150, 99, 34, 78, 141, 31, 22, 147, 48, 20, 231, 2, 190, 120, 85, 183, 220, 58, 149, 245, 132, 121, 116, 119, 26, 254, 45, 202, 187, 242, 79, 247, 145, 161, 115, 94, 92, 45, 28, 59, 202, 97, 95, 247, 98, 213, 236, 171, 224, 244, 43, 134, 245, 187, 218, 87, 253, 0, 52, 9, 164, 96, 224, 87, 118, 36, 53, 83, 75, 128, 104, 0, 183, 146, 194, 58, 39, 111, 227, 190, 80, 159, 29, 154, 129, 254, 143, 150, 235, 58, 253, 130, 97, 112, 115, 18, 186, 76, 225, 117, 195, 236, 21, 90, 220, 192, 252, 170, 169, 201, 147, 8, 26, 255, 144, 19, 238, 247, 133, 136, 97, 230, 232, 78, 159, 75, 27, 232, 84, 55, 132, 197, 253, 152, 182, 248, 27, 219, 74, 190, 197, 70, 238, 223, 34, 124, 127, 84, 198, 84, 126, 48, 217, 188, 30, 216, 65, 200, 117, 33, 64, 136, 141, 106, 106, 181, 201, 83, 98, 89, 175, 48, 74, 227, 163, 149, 192, 84, 201, 54, 214, 37, 72, 144, 4, 212, 196, 15, 103, 129, 149, 226, 206, 47, 64, 190, 131, 69, 164, 182, 121, 169, 202, 177, 225, 48, 59, 36, 127, 107, 112, 14, 223, 180, 37, 228, 63, 10, 30, 51, 238, 209, 188, 161, 133, 223, 6, 25, 36, 77, 223, 174, 132, 246, 245, 59, 205, 162, 67, 22, 118, 66, 176, 137, 122, 221, 219, 177, 109, 33, 244, 17, 15, 212, 125, 244, 26, 75, 132, 206, 82, 57, 48, 52, 72, 111, 200, 23, 123, 144, 2, 189, 130, 7, 249, 217, 83, 129]
def realSs : Array UInt8 := #[131, 63, 67, 76, 178, 18, 166, 222, 121, 238, 87, 19, 32, 98, 212, 133, 34, 31, 27, 144, 13, 58, 36, 51, 110, 105, 190, 100, 96, 230, 76, 11]

/-! ## THE ANTI-FAKE GATE — round-trip GENUINE `ml-kem` v0.2.3 crate bytes. `native_decide` runs the
COMPILED `def`s over them. -/

/-- Decoded encapsulation key of the real crate bytes. -/
def realEkDecoded : (Array Poly × List UInt8) := ekDecode realEk.toList
/-- Decoded ciphertext of the real crate bytes. -/
def realCtDecoded : (Array Poly × Poly) := ctDecode realCt.toList
/-- Decoded decapsulation key of the real crate bytes. -/
def realDkDecoded : (Array Poly × List UInt8 × List UInt8 × List UInt8) := dkDecode realDk.toList

/-- Sanity: the pinned bytes are exactly the ML-KEM-768 lengths. -/
theorem real_lengths : realEk.size = ekLen ∧ realCt.size = ctLen ∧ realDk.size = dkLen := by
  native_decide

/-- **EK round-trip**: `ekEncode (ekDecode realEk) = realEk` — exact, 1184 → decode → encode → 1184, 0 diff.
The load-bearing gate for the encapsulation-key codec (`t̂` at `d = 12` + `ρ`) on REAL crate bytes. -/
theorem ek_roundtrip : (ekEncode (ekDecode realEk.toList)).toArray = realEk := by native_decide

/-- **CT round-trip**: `ctEncode (ctDecode realCt) = realCt` — exact, 1088 → decode → encode → 1088, 0 diff.
Exercises `Compress ∘ Decompress` being inverse-consistent on REAL compressed ciphertext data (`u` at
`du = 10`, `v` at `dv = 4`). -/
theorem ct_roundtrip : (ctEncode (ctDecode realCt.toList)).toArray = realCt := by native_decide

/-- **`dk` layout**: the `ek` sub-slice `dkDecode` recovers from `realDk` equals `realEk`. The
`dk_pke ‖ ek ‖ H(ek) ‖ z` layout is located correctly. -/
theorem dk_embeds_ek : realDkDecoded.2.1.toArray = realEk := by native_decide

/-- Structural: every decoded `t̂` coefficient is `< q` (the `ByteDecode₁₂` codomain). -/
theorem ek_that_lt_q : allCoeffsLt realEkDecoded.1 q = true := by native_decide

/-- Structural: every decoded `ŝ` coefficient is `< q`. -/
theorem dk_shat_lt_q : allCoeffsLt realDkDecoded.1 q = true := by native_decide

/-- Structural: `Compress_{du}(x) < 2^{du}` and `Compress_{dv}(x) < 2^{dv}` for every `x < q`. -/
theorem compress_lt : compressAllLt du q = true ∧ compressAllLt dv q = true := by native_decide

/-- **Non-vacuity**: `Compress_d(Decompress_d(y)) = y` for every `y < 2ᵈ` at both `d = du = 10` and
`d = dv = 4` — the inverse-consistency the ciphertext round-trip relies on, as a THEOREM over the whole
compressed field, not just the sampled bytes. -/
theorem compress_decompress_id :
    compressDecompressId du = true ∧ compressDecompressId dv = true := by native_decide

end Dregg2.Crypto.MlKemCodec
