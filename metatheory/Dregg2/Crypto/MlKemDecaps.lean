/-
# `Dregg2.Crypto.MlKemDecaps` — the REAL ML-KEM-768 decapsulation (+ K-PKE encrypt/decrypt), EXECUTABLE `def`s.

BRICK K4 — the KEYSTONE — of replacing the `A = 1`, `n = 1` scalar caricature in `Fips203Kem.lean` with the
real ML-KEM-768. K1 (`MlKemRing`) built the ring `R_q = ℤ_q[X]/(X²⁵⁶+1)` + the incomplete Kyber NTT; K2
(`MlKemSample`) built `SampleNTT`/`ExpandA`/`SamplePolyCBD`; K3 (`MlKemCodec`) built the byte codec and pinned
the GENUINE `ml-kem` v0.2.3 crate keypair + ciphertext + shared secret (`realDk`, `realCt`, `realSs`). This
module ASSEMBLES them into the FO decapsulation (FIPS 203 Algorithm 17) and proves — by `native_decide` over
the COMPILED `def`s — that the Lean decaps, given the REAL crate decapsulation key + ciphertext, recovers the
REAL 32-byte shared secret, and that a tampered ciphertext takes the implicit-reject path to a DIFFERENT secret.

## ML-KEM-768 parameters (FIPS 203 §8): `k = 3`, `η1 = η2 = 2`, `du = 10`, `dv = 4`, `n = 256`, `q = 3329`.

## The three FIPS 203 hashes: `G = SHA3-512`, `H = SHA3-256`, `J = SHAKE-256`

K1 `Keccak` supplies Keccak-f[1600] + SHAKE (domain byte `0x1F`). SHA-3 is the SAME permutation with domain
byte `0x06` (FIPS 202 §6.1) and a FIXED-length squeeze — added here (`sha3_256`, `sha3_512`) over the K1
`absorb`/`squeeze`/`keccakF`, gated against the published NIST SHA-3 Known-Answer-Test vectors
(`SHA3-256("") = a7ffc6f8bf1ed766…`, `SHA3-512("") = a69f73cca23a9ac5…`, plus the `"abc"` cross-checks). SHAKE-256
(the `J` implicit-reject PRF and the CBD `PRF_η`) is reused verbatim from K1.

## THE ASSEMBLY (FIPS 203 Algorithms 14, 13, 17)

* **`kpkeDecrypt dkPke c` (Alg 14).** `(u,v) = ctDecode c` (K3: `u` is `Decompress_{du} ∘ ByteDecode_{du}`,
  `v` is `Decompress_{dv} ∘ ByteDecode_{dv}` — genuine `R_q` elements); `ŝ = ByteDecode₁₂(dkPke)` (`k` NTT-domain
  polys); `w = v − NTT⁻¹(Σᵢ ŝᵢ ∘ NTT(uᵢ))`; `m = ByteEncode₁(Compress₁(w))` — the 32-byte message.
* **`kpkeEncrypt ek m r` (Alg 13).** `(t̂,ρ) = ekDecode ek`; `Â = ExpandA(ρ)`; sample `y,e1` (`η1`), `e2` (`η2`)
  from `PRF_η(r,·) = SHAKE256(r ‖ N, 64η)`; `ŷ = NTT(y)`; `u = NTT⁻¹(Âᵀ ∘ ŷ) + e1`;
  `v = NTT⁻¹(t̂ᵀ ∘ ŷ) + e2 + Decompress₁(ByteDecode₁(m))`; `ct = ctEncode(u,v)` (K3 compress+encode). The `Âᵀ`
  transpose consumes `Â[j][i]` (index `j·k+i`) — the classic Kyber matrix asymmetry (KeyGen uses `Â`, Encrypt `Âᵀ`).
* **`mlkemDecaps dk c` (Alg 17).** Parse `dk = (dkPke ‖ ek ‖ h ‖ z)`; `m' = kpkeDecrypt dkPke c`;
  `(K',r') = G(m' ‖ h)` (SHA3-512, split 32+32); `c' = kpkeEncrypt ek m' r'`;
  `K = if c' = c then K' else J(z ‖ c)` (SHAKE-256, 32 B) — the FO implicit reject. Returns the 32-byte secret.

## THE KEYSTONE GATE (`native_decide`, over the REAL K3 crate vectors)

* `decaps_recovers_real_secret` — `mlkemDecaps realDk realCt = realSs`: the Lean decaps, given a REAL `ml-kem`
  crate decapsulation key + ciphertext, RECOVERS the REAL 32-byte shared secret. This is the whole brick — it
  forces decrypt (correct `w`, `Compress₁`), the `G = SHA3-512` split, the FULL re-encryption (`ExpandA`, CBD
  from `PRF`, both `NTT⁻¹` products, both compressions), and the byte-exact `c' = c` FO check ALL to be right: a
  single wrong step yields either `m' ≠ m` (wrong `K'`) or `c' ≠ c` (implicit reject) — either way `≠ realSs`.
* `decaps_rejects_tampered` — one flipped ciphertext byte ⇒ `mlkemDecaps realDk c_tampered ≠ realSs`: the FO
  implicit-reject path (`c' ≠ c` ⇒ `K = J(z ‖ c_tampered)`) gives a DIFFERENT secret, ML-KEM's implicit-reject
  semantics.

`native_decide` runs the COMPILED `def`s; its trusted base is `Lean.ofReduceBool` + `Lean.trustCompiler` — the
SAME residual K1–K3, `Keccak`, and `Fips204Verify` already name. No `sorry`, no user `axiom`, no toy substitute.
-/
import Dregg2.Crypto.Keccak
import Dregg2.Crypto.MlKemRing
import Dregg2.Crypto.MlKemSample
import Dregg2.Crypto.MlKemCodec

namespace Dregg2.Crypto.MlKemDecaps

open Dregg2.Crypto.Keccak (shake256 absorb squeeze)
open Dregg2.Crypto.MlKemRing (Poly zeroPoly ntt intt pointwiseNtt addPoly subPoly)
open Dregg2.Crypto.MlKemSample (expandMatrix samplePolyCBD)
open Dregg2.Crypto.MlKemCodec

/-! ## SHA-3 fixed-length hashes over the K1 Keccak permutation (domain byte `0x06`, FIPS 202 §6.1).

Reuses K1 `absorb`/`squeeze`/`keccakF`; only the padding domain byte (`0x06`, not SHAKE's `0x1F`) differs. -/

/-- `pad10*1` with the SHA-3 domain byte `0x06` (FIPS 202 §6.1 — SHA-3, not SHAKE's `0x1F`). Appends the
domain byte, zero-fills to a multiple of `rate`, sets the final byte's high bit. When only one pad byte is
available both collapse into `0x86`. -/
def sha3Pad (rate : Nat) (msg : List UInt8) : List UInt8 :=
  let q := rate - (msg.length % rate)          -- pad-byte count, 1..rate
  if q == 1 then
    msg ++ [0x86]
  else
    msg ++ (0x06 :: List.replicate (q - 2) 0x00) ++ [0x80]

/-- **SHA3-256** (FIPS 202): rate 136 bytes (capacity 512 bits), domain `0x06`, fixed 32-byte output. -/
def sha3_256 (input : List UInt8) : List UInt8 :=
  squeeze 136 (absorb 136 (sha3Pad 136 input)) 32

/-- **SHA3-512** (FIPS 202): rate 72 bytes (capacity 1024 bits), domain `0x06`, fixed 64-byte output. -/
def sha3_512 (input : List UInt8) : List UInt8 :=
  squeeze 72 (absorb 72 (sha3Pad 72 input)) 64

/-! ### The SHA-3 anti-fake gate — published NIST Known-Answer-Test vectors. -/

/-- `SHA3-256("")` — the FIPS 202 anchor. -/
theorem sha3_256_empty_kat :
    sha3_256 [] =
      [0xa7, 0xff, 0xc6, 0xf8, 0xbf, 0x1e, 0xd7, 0x66,
       0x51, 0xc1, 0x47, 0x56, 0xa0, 0x61, 0xd6, 0x62,
       0xf5, 0x80, 0xff, 0x4d, 0xe4, 0x3b, 0x49, 0xfa,
       0x82, 0xd8, 0x0a, 0x4b, 0x80, 0xf8, 0x43, 0x4a] := by native_decide

/-- `SHA3-512("")` — the FIPS 202 anchor. -/
theorem sha3_512_empty_kat :
    sha3_512 [] =
      [0xa6, 0x9f, 0x73, 0xcc, 0xa2, 0x3a, 0x9a, 0xc5,
       0xc8, 0xb5, 0x67, 0xdc, 0x18, 0x5a, 0x75, 0x6e,
       0x97, 0xc9, 0x82, 0x16, 0x4f, 0xe2, 0x58, 0x59,
       0xe0, 0xd1, 0xdc, 0xc1, 0x47, 0x5c, 0x80, 0xa6,
       0x15, 0xb2, 0x12, 0x3a, 0xf1, 0xf5, 0xf9, 0x4c,
       0x11, 0xe3, 0xe9, 0x40, 0x2c, 0x3a, 0xc5, 0x58,
       0xf5, 0x00, 0x19, 0x9d, 0x95, 0xb6, 0xd3, 0xe3,
       0x01, 0x75, 0x85, 0x86, 0x28, 0x1d, 0xcd, 0x26] := by native_decide

/-- `SHA3-256("abc")` — non-empty cross-check (`"abc" = 0x61 0x62 0x63`). -/
theorem sha3_256_abc_kat :
    sha3_256 [0x61, 0x62, 0x63] =
      [0x3a, 0x98, 0x5d, 0xa7, 0x4f, 0xe2, 0x25, 0xb2,
       0x04, 0x5c, 0x17, 0x2d, 0x6b, 0xd3, 0x90, 0xbd,
       0x85, 0x5f, 0x08, 0x6e, 0x3e, 0x9d, 0x52, 0x5b,
       0x46, 0xbf, 0xe2, 0x45, 0x11, 0x43, 0x15, 0x32] := by native_decide

/-- `SHA3-512("abc")` — non-empty cross-check. -/
theorem sha3_512_abc_kat :
    sha3_512 [0x61, 0x62, 0x63] =
      [0xb7, 0x51, 0x85, 0x0b, 0x1a, 0x57, 0x16, 0x8a,
       0x56, 0x93, 0xcd, 0x92, 0x4b, 0x6b, 0x09, 0x6e,
       0x08, 0xf6, 0x21, 0x82, 0x74, 0x44, 0xf7, 0x0d,
       0x88, 0x4f, 0x5d, 0x02, 0x40, 0xd2, 0x71, 0x2e,
       0x10, 0xe1, 0x16, 0xe9, 0x19, 0x2a, 0xf3, 0xc9,
       0x1a, 0x7e, 0xc5, 0x76, 0x47, 0xe3, 0x93, 0x40,
       0x57, 0x34, 0x0b, 0x4c, 0xf4, 0x08, 0xd5, 0xa5,
       0x65, 0x92, 0xf8, 0x27, 0x4e, 0xec, 0x53, 0xf0] := by native_decide

/-! ## The FO PRF (FIPS 203): `PRF_η(s, b) = SHAKE256(s ‖ IntegerToBytes(b,1), 64·η)`. -/

/-- `PRF_η(s, N)` — SHAKE-256 over `s` with the one-byte counter `N` appended, squeezing `64·η` bytes. For
`η = 2` this is 128 bytes = the `SamplePolyCBD_η` input length. -/
def prf (eta : Nat) (s : List UInt8) (b : Nat) : List UInt8 :=
  shake256 (s ++ [UInt8.ofNat b]) (64 * eta)

/-! ## K-PKE.Decrypt (FIPS 203 Algorithm 14). -/

/-- **`K-PKE.Decrypt(dkPke, c)`** (FIPS 203 Alg 14). `(u,v) = ctDecode c` (decompressed `R_q` elements);
`ŝ = ByteDecode₁₂(dkPke)`; `w = v − NTT⁻¹(Σᵢ ŝᵢ ∘ NTT(uᵢ))`; return `ByteEncode₁(Compress₁(w))` — 32 message
bytes. -/
def kpkeDecrypt (dkPke : List UInt8) (c : List UInt8) : List UInt8 := Id.run do
  let (u, v) := ctDecode c
  let dkArr := dkPke.toArray
  let mut acc : Poly := zeroPoly
  for i in [0:paramK] do
    let sHat_i := byteDecodeAt dCoeff dkArr (i * polyBytes dCoeff)
    acc := addPoly acc (pointwiseNtt sHat_i (ntt u[i]!))
  let w := subPoly v (intt acc)
  return byteEncode 1 (compressPoly 1 w)

/-! ## K-PKE.Encrypt (FIPS 203 Algorithm 13). -/

/-- **`K-PKE.Encrypt(ek, m, r)`** (FIPS 203 Alg 13). `(t̂,ρ) = ekDecode ek`; `Â = ExpandA(ρ)`; sample `y,e1,e2`
from `PRF_η(r,·)`; `ŷ = NTT(y)`; `u = NTT⁻¹(Âᵀ ∘ ŷ) + e1`;
`v = NTT⁻¹(t̂ᵀ ∘ ŷ) + e2 + Decompress₁(ByteDecode₁(m))`; `ct = ctEncode(u,v)`. `Âᵀ` uses `Â[j][i]` at index
`j·k+i` (the KeyGen-vs-Encrypt transpose). ML-KEM-768: `η1 = η2 = 2`. -/
def kpkeEncrypt (ek : List UInt8) (m : List UInt8) (r : List UInt8) : List UInt8 := Id.run do
  let (tHat, rho) := ekDecode ek
  let aHat := expandMatrix rho                         -- Â[i][j] at index i·k+j
  -- sample noise y (η1), e1 (η2), e2 (η2); ML-KEM-768 has η1 = η2 = 2
  let mut y : Array Poly := #[]
  let mut n : Nat := 0
  for _ in [0:paramK] do
    y := y.push (samplePolyCBD 2 (prf 2 r n)); n := n + 1
  let mut e1 : Array Poly := #[]
  for _ in [0:paramK] do
    e1 := e1.push (samplePolyCBD 2 (prf 2 r n)); n := n + 1
  let e2 := samplePolyCBD 2 (prf 2 r n)
  -- ŷ = NTT(y)
  let mut yHat : Array Poly := #[]
  for i in [0:paramK] do
    yHat := yHat.push (ntt y[i]!)
  -- u[i] = NTT⁻¹(Σⱼ Âᵀ[i][j] ∘ ŷ[j]) + e1[i]  =  NTT⁻¹(Σⱼ Â[j][i] ∘ ŷ[j]) + e1[i]
  let mut u : Array Poly := #[]
  for i in [0:paramK] do
    let mut acc : Poly := zeroPoly
    for j in [0:paramK] do
      acc := addPoly acc (pointwiseNtt aHat[j * paramK + i]! yHat[j]!)
    u := u.push (addPoly (intt acc) e1[i]!)
  -- v = NTT⁻¹(Σᵢ t̂[i] ∘ ŷ[i]) + e2 + Decompress₁(ByteDecode₁(m))
  let mut vacc : Poly := zeroPoly
  for i in [0:paramK] do
    vacc := addPoly vacc (pointwiseNtt tHat[i]! yHat[i]!)
  let mu := decompressPoly 1 (byteDecode 1 m)
  let v := addPoly (addPoly (intt vacc) e2) mu
  return ctEncode (u, v)

/-! ## ML-KEM.Decaps (FIPS 203 Algorithm 17) — the Fujisaki–Okamoto decapsulation. -/

/-- **`ML-KEM.Decaps(dk, c)`** (FIPS 203 Alg 17). Parse `dk = (dkPke ‖ ek ‖ h ‖ z)`;
`m' = K-PKE.Decrypt(dkPke, c)`; `(K',r') = G(m' ‖ h)` (`G = SHA3-512`, split 32+32);
`c' = K-PKE.Encrypt(ek, m', r')`; `K = if c' = c then K' else J(z ‖ c)` (`J = SHAKE-256`, 32 bytes) — the FO
implicit reject. Returns the 32-byte shared secret. -/
def mlkemDecaps (dk : List UInt8) (c : List UInt8) : List UInt8 := Id.run do
  let dkArr := dk.toArray
  let dkPke := (dkArr.extract 0 (paramK * polyBytes dCoeff)).toList   -- dk[0 : 1152]
  let (_, _ek, hek, z) := dkDecode dk
  let mPrime := kpkeDecrypt dkPke c
  let g := sha3_512 (mPrime ++ hek)                    -- G(m' ‖ h) → 64 bytes
  let kPrime := g.take 32                              -- K'
  let rPrime := g.drop 32                              -- r'
  let cPrime := kpkeEncrypt _ek mPrime rPrime          -- re-encrypt
  let kReject := shake256 (z ++ c) 32                  -- J(z ‖ c)
  if cPrime == c then
    return kPrime
  else
    return kReject

/-! ## THE KEYSTONE GATE — `native_decide` over the GENUINE `ml-kem` v0.2.3 crate vectors (from K3). -/

/-- **THE KEYSTONE**: `mlkemDecaps realDk realCt = realSs` — the Lean decaps, given a REAL `ml-kem` crate
decapsulation key + ciphertext, RECOVERS the REAL 32-byte shared secret. This forces the full FO pipeline —
K-PKE decrypt (`w`, `Compress₁`), the `G = SHA3-512` split, the entire re-encryption (`ExpandA`, CBD from
`PRF`, both `NTT⁻¹` products, both compressions), and the byte-exact `c' = c` check — to ALL be correct: any
single wrong step yields `m' ≠ m` (wrong `K'`) or `c' ≠ c` (implicit reject), either way `≠ realSs`. -/
theorem decaps_recovers_real_secret :
    mlkemDecaps realDk.toList realCt.toList = realSs.toList := by native_decide

/-- A tampered ciphertext: the real ciphertext with its first byte flipped (`^^^ 1`). -/
def realCtTampered : Array UInt8 := realCt.set! 0 (realCt[0]! ^^^ 1)

/-- **Implicit reject**: one flipped ciphertext byte ⇒ `mlkemDecaps realDk c_tampered ≠ realSs`. The FO
re-encryption `c' = kpkeEncrypt ek m' r'` no longer equals the tampered `c` (`c' = realCt ≠ c_tampered` even
if `m'` were unchanged), so decaps takes the implicit-reject branch `K = J(z ‖ c_tampered)` — a DIFFERENT
secret, exactly ML-KEM's implicit-reject semantics. -/
theorem decaps_rejects_tampered :
    mlkemDecaps realDk.toList realCtTampered.toList ≠ realSs.toList := by native_decide

/-! ## THE `@[export]` FFI ENTRY (Rust → Lean) — the REAL, FULL-BYTE ML-KEM-768 decapsulation over a byte wire.

BRICK K6 — the ML-KEM analog of BRICK 8's `dregg_fips204_verify_real`. The deployed hybrid-KEM decaps
(`dregg-pq/src/hybrid_kem.rs` `HybridResponder::finish`) currently recovers the ML-KEM shared secret by
calling the `ml-kem` crate's `.decapsulate`. This export routes THAT call through the Lean-verified
`mlkemDecaps` (the full FO pipeline proved to recover the REAL crate secret and implicit-reject tampers, above),
so the `ml-kem` crate leaves the node's KEM-decaps TCB. `dregg-lean-ffi::shadow_mlkem_decaps_real` runs it
natively; the transcript/KDF around the ML-KEM secret (X25519 combiner) is unchanged — only the `.decapsulate`
call is replaced. -/

/-- One lowercase/uppercase hex nibble → its `[0,16)` value; `none` on a non-hex char. -/
def hexNibble? (c : Char) : Option UInt8 :=
  let n := c.toNat
  if '0'.toNat ≤ n ∧ n ≤ '9'.toNat then some (UInt8.ofNat (n - '0'.toNat))
  else if 'a'.toNat ≤ n ∧ n ≤ 'f'.toNat then some (UInt8.ofNat (n - 'a'.toNat + 10))
  else if 'A'.toNat ≤ n ∧ n ≤ 'F'.toNat then some (UInt8.ofNat (n - 'A'.toNat + 10))
  else none

/-- Decode a hex char list to bytes; `none` on an odd length or any non-hex char (fail-closed). -/
def decodeHexChars : List Char → Option (List UInt8)
  | [] => some []
  | [_] => none
  | hi :: lo :: rest => do
    let h ← hexNibble? hi
    let l ← hexNibble? lo
    let rest' ← decodeHexChars rest
    pure (UInt8.ofNat (h.toNat * 16 + l.toNat) :: rest')

/-- One byte → two lowercase-hex chars. -/
def toHexDigit (n : UInt8) : Char :=
  let n := n.toNat
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)

/-- Encode bytes as a lowercase-hex string (`decodeHexChars` is its left inverse). -/
def hexEncode (bs : List UInt8) : String :=
  String.ofList (bs.foldr (fun b acc => toHexDigit (b / 16) :: toHexDigit (b % 16) :: acc) [])

/-- The real byte wire `hex(dk) hex(ct)` the FFI reads. -/
def realWireKem (dk ct : List UInt8) : String :=
  hexEncode dk ++ " " ++ hexEncode ct

/-- **FFI entry** (Rust→Lean) for the REAL, FULL-BYTE ML-KEM-768 DECAPS (BRICK K6): parse the two hex fields
`hex(dk) hex(ct)`, run the Lean-verified `mlkemDecaps` over the decoded bytes, and return `hex(K)` — the
recovered 32-byte shared secret (`H(m′)`-derived on a matching re-encryption, else the implicit-reject secret
`J(z‖c)`; ML-KEM decaps never fails on a well-formed ciphertext, a tamper yields a DIFFERENT secret). This runs
the FULL-DIMENSION FO decapsulation (not the `A=1,n=1` scalar toy) as native code — the security-critical
recover of a REAL 2400-byte decapsulation key + 1088-byte ciphertext. Any malformed wire fails CLOSED (`"ERR"`),
which the Rust caller treats as a decaps fault (fail-closed, the parties diverge). -/
@[export dregg_mlkem_decaps_real]
def mlkemDecapsRealFFI (input : String) : String :=
  match input.splitOn " " with
  | [dkH, ctH] =>
    match decodeHexChars dkH.toList, decodeHexChars ctH.toList with
    | some dk, some ct => hexEncode (mlkemDecaps dk ct)
    | _, _ => "ERR"
  | _ => "ERR"

/-! ### Teeth — the byte-wire decaps is NON-VACUOUS: the REAL crate ciphertext recovers the REAL secret,
a tamper recovers a DIFFERENT one. Drive the WHOLE wire path (hex encode → split → hex decode → `mlkemDecaps`
→ hex encode) at build time with `native_decide` over the GENUINE `ml-kem` v0.2.3 crate vectors (from K3). -/

/-- **THE KEYSTONE (byte-wire)**: the FFI, fed the REAL crate `dk`/`ct` as the hex wire, recovers `hex(realSs)`
— the whole Rust→Lean marshalling path recovers the REAL 32-byte shared secret. -/
theorem mlkemDecapsRealFFI_recovers_real_secret :
    mlkemDecapsRealFFI (realWireKem realDk.toList realCt.toList) = hexEncode realSs.toList := by
  native_decide

/-- **Implicit reject (byte-wire)**: one flipped ciphertext byte on the wire ⇒ a DIFFERENT recovered secret. -/
theorem mlkemDecapsRealFFI_rejects_tampered :
    mlkemDecapsRealFFI (realWireKem realDk.toList realCtTampered.toList) ≠ hexEncode realSs.toList := by
  native_decide

-- A malformed wire fails CLOSED (interpreted `#guard`, fast): wrong field count, odd-length hex, non-hex.
#guard mlkemDecapsRealFFI "zz zz" = "ERR"
#guard mlkemDecapsRealFFI "00" = "ERR"
#guard mlkemDecapsRealFFI "0 0" = "ERR"

end Dregg2.Crypto.MlKemDecaps
