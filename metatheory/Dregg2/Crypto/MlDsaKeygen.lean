/-
# `Dregg2.Crypto.MlDsaKeygen` — the REAL ML-DSA-65 KEY GENERATION (FIPS 204), EXECUTABLE `def`s.

The KEYGEN mirror of the ML-KEM `MlKemKeygen` (K7) brick, on the ML-DSA side. It builds the DETERMINISTIC
ML-DSA-65 key generation from a 32-byte `ξ` seed per **FIPS 204 Algorithm 6** (`ML-DSA.KeyGen_internal`). It
REUSES the existing ML-DSA pieces (no reinvention): `expandA` (K/L rejection matrix, `MlDsaExpandA`), the
`ntt` / `intt` / `pointwiseMul` / `addPoly` ring ops (`MlDsaRing`), and `pkEncode` / `packBits` (`MlDsaCodec`).
Only the pieces the tree did NOT yet have are authored here: `ExpandS` (`RejBoundedPoly` / `CoeffFromHalfByte`,
FIPS 204 Alg 31/33), `Power2Round` (Alg 35), the `BitPack` sign map `bEncode` (the ENCODE inverse of the sign
core's `bDecode`), and the `skEncode` assembly (Alg 24).

## ML-DSA-65 parameters (FIPS 204 Table 1): `k = 6`, `ℓ = 5`, `η = 4`, `d = 13`, `q = 8380417`.

## ML-DSA.KeyGen_internal(ξ)  (FIPS 204 Algorithm 6)
```
1: (ρ, ρ′, K) ← H(ξ ‖ IntegerToBytes(k,1) ‖ IntegerToBytes(ℓ,1), 128)   -- H = SHAKE256; split 32‖64‖32
2: Â ← ExpandA(ρ)
3: (s1, s2) ← ExpandS(ρ′)
4: t ← NTT⁻¹(Â ∘ NTT(s1)) + s2
5: (t1, t0) ← Power2Round(t, d)
6: pk ← pkEncode(ρ, t1)
7: tr ← H(pk, 64)                                                        -- H = SHAKE256
8: sk ← skEncode(ρ, K, tr, s1, s2, t0)
9: return (pk, sk)
```
The KAT anchor (in `MlDsaKeygenAcvp`) is the NIST ACVP `ML-DSA-keyGen-FIPS204` vector set (ML-DSA-65 group),
NOT a crate.

READ THE STATEMENTS, NOT THIS PROSE. The gates in `MlDsaKeygenAcvp` are SINGLE-VECTOR `native_decide` KATs (no
`forall`): byte-exact agreement with the NIST reference on specific seeds — evidence, not a for-all correctness
proof. The for-all obligation (the byte↔ring KeyGen refinement) is stated EXPLICITLY at the bottom of this file
and is OPEN. `native_decide` runs the COMPILED `def`s; its trusted base is `Lean.ofReduceBool` +
`Lean.trustCompiler`. No `sorry`, no user `axiom`, no toy substitute.
-/
import Dregg2.Crypto.MlDsaRing
import Dregg2.Crypto.MlDsaExpandA
import Dregg2.Crypto.MlDsaCodec
import Dregg2.Crypto.MlKemDecaps

namespace Dregg2.Crypto.MlDsaKeygen

open Dregg2.Crypto.MlDsaRing (Poly q zeroPoly ntt intt pointwiseMul addPoly)
open Dregg2.Crypto.MlDsaExpandA (expandA)
open Dregg2.Crypto.MlDsaCodec (paramK paramL t1Bits pkEncode packBits)
open Dregg2.Crypto.Keccak (shake256)
open Dregg2.Crypto.MlKemDecaps (hexEncode decodeHexChars)

/-! ## ML-DSA-65 keygen parameters. -/

/-- `η = 4`, the `s1`/`s2` secret coefficient bound. -/
def etaP : Nat := 4
/-- Bits per packed `s1`/`s2` coefficient: `bitlen(2η) = bitlen(8) = 4`. -/
def etaBits : Nat := 4
/-- `2^{d−1} = 2¹² = 4096`, the `t0` `BitPack` centre `b` (`d = 13`). -/
def t0Half : Nat := 4096
/-- Bits per packed `t0` coefficient: `d = 13`. -/
def t0Bits : Nat := 13
/-- `2^d = 8192`, the `Power2Round` low-order modulus. -/
def twoD : Nat := 8192
/-- SHAKE-256 bytes drawn per `RejBoundedPoly` — generous margin: 512 bytes = 1024 nibbles, accept prob
`9/16` per nibble (η = 4) ⇒ ~576 accepts expected for the 256 needed. Fixed length keeps the squeeze a
deterministic prefix of the infinite XOF (matches Alg 31 reading bytes one at a time). -/
def sReads : Nat := 512

/-! ## `ExpandS` (FIPS 204 Alg 31/33) — sample `(s1, s2)` from `ρ′`. -/

/-- **`CoeffFromHalfByte` — FIPS 204 Algorithm 15 for η = 4.** A half-byte `b ∈ [0,16)` maps to the signed
coefficient `4 − b ∈ [−4, 4]` when `b < 9`, else it is rejected (`none`). Result carried as its canonical
`ℤ_q` rep (negatives as `q + v`). -/
def coeffFromHalfByte (b : Nat) : Option Nat :=
  if b < 9 then some (if b ≤ 4 then 4 - b else q - (b - 4)) else none

/-- **`RejBoundedPoly` — FIPS 204 Algorithm 31 for ML-DSA-65 (η = 4).** Drive SHAKE-256 over `seed`; read the
stream one byte `z` at a time, split into the low nibble `z mod 16` then the high nibble `z / 16`, map each
through `coeffFromHalfByte`, and ACCEPT non-`⊥` coefficients in that order until 256 are collected. -/
def rejBoundedPoly (seed : List UInt8) : Poly := Id.run do
  let stream : Array UInt8 := (shake256 seed sReads).toArray
  let mut coeffs : Array Nat := #[]
  for r in [0:sReads] do
    if coeffs.size < 256 then
      let z := stream[r]!.toNat
      match coeffFromHalfByte (z % 16) with
      | some c0 => coeffs := coeffs.push c0
      | none => pure ()
      if coeffs.size < 256 then
        match coeffFromHalfByte (z / 16) with
        | some c1 => coeffs := coeffs.push c1
        | none => pure ()
  return coeffs

/-- **`ExpandS` — FIPS 204 Algorithm 33 for ML-DSA-65 (`ℓ = 5`, `k = 6`).** `s1[i] = RejBoundedPoly(ρ′ ‖
IntegerToBytes(i, 2))` for `i ∈ [0,ℓ)`, `s2[i] = RejBoundedPoly(ρ′ ‖ IntegerToBytes(i+ℓ, 2))` for `i ∈ [0,k)`
(2-byte little-endian nonce). Returns `(s1, s2)` — normal (non-NTT) domain. -/
def expandS (rhoP : List UInt8) : (Array Poly × Array Poly) := Id.run do
  let mut s1 : Array Poly := Array.mkEmpty paramL
  for i in [0:paramL] do
    let seed := rhoP ++ [UInt8.ofNat (i % 256), UInt8.ofNat (i / 256)]
    s1 := s1.push (rejBoundedPoly seed)
  let mut s2 : Array Poly := Array.mkEmpty paramK
  for i in [0:paramK] do
    let n := i + paramL
    let seed := rhoP ++ [UInt8.ofNat (n % 256), UInt8.ofNat (n / 256)]
    s2 := s2.push (rejBoundedPoly seed)
  return (s1, s2)

/-! ## `Power2Round` (FIPS 204 Algorithm 35) and the `BitPack` sign map. -/

/-- **`Power2Round` — FIPS 204 Algorithm 35** (`d = 13`). For a canonical `ℤ_q` coefficient `r`, split
`r = r1·2^d + r0` with `r0 ∈ (−2^{d−1}, 2^{d−1}]` (centered). Returns `(r1, t0canon)` where `r1 ∈ [0, 1024)`
is the high part (`t1` coefficient) and `t0canon` is `r0` carried as its canonical `ℤ_q` rep. -/
def power2round (r : Nat) : (Nat × Nat) :=
  let rp := r % q
  let m := rp % twoD
  if m ≤ t0Half then ((rp - m) / twoD, m)           -- r0 = m ∈ [0, 4096]
  else ((rp - m) / twoD + 1, q + m - twoD)          -- r0 = m − 8192 ∈ (−4096, 0); canonical = q + r0 (Nat-safe)

/-- **`BitPack` sign map (ENCODE)** — the inverse of the sign core's `bDecode`. A canonical `ℤ_q` coefficient
`c` (representing the signed value `s` with `s = c` if small-nonneg else `s = c − q`) packs to the field
`b − s = (b + q − c) mod q`. Covers `s1`/`s2` (`b = η`) and `t0` (`b = 2^{d−1}`). -/
def bEncode (b c : Nat) : Nat := (b + q - c) % q

/-- Pack one `s1`/`s2` polynomial: `BitPack(·, η, η)` at 4 bits/coeff → 128 bytes. -/
def packEta (p : Poly) : Array UInt8 := packBits (p.map (fun c => bEncode etaP c)) etaBits

/-- Pack one `t0` polynomial: `BitPack(·, 2^{d−1}−1, 2^{d−1})` at 13 bits/coeff → 416 bytes. -/
def packT0 (p : Poly) : Array UInt8 := packBits (p.map (fun c => bEncode t0Half c)) t0Bits

/-! ## The RING-LEVEL keygen (FIPS 204 Algorithm 6 steps 1–5) — the abstract objects, NO byte codec.

`ML-DSA.KeyGen_internal` splits cleanly at step 5: everything up to `Power2Round` lives in `R_q`
(`ExpandA` / `ExpandS` / `NTT` / matvec / `Power2Round`), and steps 6–8 are pure byte packing
(`pkEncode` / `H` / `skEncode`). That split is made STRUCTURAL here: `mldsaKeygenRing` is the ring
generator, and `mldsaKeygenInternal` (below) IS `mldsaKeygenRing` composed with the byte codecs — the
shape the byte↔ring refinement `MlDsaKeygenRefine.mldsaKeygen_refines_ring` is stated over. -/

/-- The RING-level ML-DSA-65 key material: `(ρ, K, s1, s2, t1, t0)`, FIPS 204 Alg 6 through step 5.
`ρ`/`K` are the raw `H(ξ‖k‖ℓ)` seed slices; `s1`/`s2`/`t1`/`t0` are `R_q` vectors (arrays of `Poly`),
NOT bytes. -/
structure RingKey where
  /-- `ρ` — the 32-byte `ExpandA` seed (the first slice of `H(ξ ‖ k ‖ ℓ, 128)`). -/
  rho : List UInt8
  /-- `K` — the 32-byte signing seed (the last slice of `H(ξ ‖ k ‖ ℓ, 128)`). -/
  kk  : List UInt8
  /-- `s1 ∈ R_q^ℓ` — `ExpandS(ρ′)` low half, coefficients in `[−η, η]`. -/
  s1  : Array Poly
  /-- `s2 ∈ R_q^k` — `ExpandS(ρ′)` high half, coefficients in `[−η, η]`. -/
  s2  : Array Poly
  /-- `t1 ∈ R_q^k` — the `Power2Round` high parts, coefficients in `[0, 2¹⁰)`. -/
  t1  : Array Poly
  /-- `t0 ∈ R_q^k` — the `Power2Round` low parts, coefficients in `(−2^{d−1}, 2^{d−1}]`. -/
  t0  : Array Poly

/-- Row `i` of the NTT-domain matrix product: `Σⱼ Â[i][j] ∘ ŝ1[j]` (FIPS 204 Alg 6 step 4, NTT domain). -/
def matAcc (aHat s1Hat : Array Poly) (i : Nat) : Poly := Id.run do
  let mut acc : Poly := zeroPoly
  for j in [0:paramL] do
    acc := addPoly acc (pointwiseMul aHat[i * paramL + j]! s1Hat[j]!)
  return acc

/-- Coefficient-wise `Power2Round` of one polynomial: `(t1ᵢ, t0ᵢ)` (FIPS 204 Alg 6 step 5). -/
def p2rLoop (ti : Poly) : (Poly × Poly) := Id.run do
  let mut t1p := zeroPoly
  let mut t0p := zeroPoly
  for c in [0:256] do
    let (r1, r0) := power2round (ti[c]!)
    t1p := t1p.set! c r1
    t0p := t0p.set! c r0
  return (t1p, t0p)

/-- `ŝ1 = NTT(s1)`, component-wise (FIPS 204 Alg 6 step 4). -/
def s1HatOf (s1 : Array Poly) : Array Poly := Id.run do
  let mut s1Hat : Array Poly := Array.mkEmpty paramL
  for j in [0:paramL] do
    s1Hat := s1Hat.push (ntt s1[j]!)
  return s1Hat

/-- The per-row `Power2Round` split: row `i` yields the pair `(t1ᵢ, t0ᵢ)` for
`t[i] = NTT⁻¹(Σⱼ Â[i][j] ∘ ŝ1[j]) + s2[i]` (FIPS 204 Alg 6 steps 4–5).

ONE mutable accumulator, holding the `(t1ᵢ, t0ᵢ)` PAIR — deliberately, not two parallel `mut` vectors.
A two-`mut` `do`-loop elaborates to a `forIn` over an `MProd` state whose `List.foldl` normalisation the
KERNEL cannot check here: each iteration carries the term `p2rLoop (addPoly (intt (matAcc …)) …)`, and
verifying that rewrite delta-unfolds `intt`/`matAcc`/`p2rLoop` symbolically (256-point loops over symbolic
arrays) until it deep-recurses. The single-`mut` `out.push (f i)` shape normalises to a plain indexed
push-fold whose spec applies by UNIFICATION, leaving `f` abstract — the same shape the ML-KEM ring keygen
uses. Same values, same order; `tLoop` below just projects the two columns. -/
def tPairs (aHat s1Hat s2 : Array Poly) : Array (Poly × Poly) := Id.run do
  let mut tp : Array (Poly × Poly) := Array.mkEmpty paramK
  for i in [0:paramK] do
    tp := tp.push (p2rLoop (addPoly (intt (matAcc aHat s1Hat i)) s2[i]!))
  return tp

/-- The `t` vector split: `t[i] = NTT⁻¹(Σⱼ Â[i][j] ∘ ŝ1[j]) + s2[i]`, then `Power2Round` per coefficient
(FIPS 204 Alg 6 steps 4–5). Returns `(t1, t0)` — the two columns of `tPairs`. -/
def tLoop (aHat s1Hat s2 : Array Poly) : (Array Poly × Array Poly) :=
  ((tPairs aHat s1Hat s2).map Prod.fst, (tPairs aHat s1Hat s2).map Prod.snd)

/-- **THE RING-LEVEL `ML-DSA.KeyGen_internal(ξ)`** (FIPS 204 Algorithm 6, steps 1–5). `(ρ,ρ′,K) =
H(ξ ‖ k ‖ ℓ, 128)` (`H = SHAKE256`, split 32‖64‖32); `Â = ExpandA(ρ)`; `(s1,s2) = ExpandS(ρ′)`;
`t[i] = NTT⁻¹(Σⱼ Â[i][j] ∘ NTT(s1)[j]) + s2[i]`; `(t1,t0) = Power2Round(t, d)`. NO byte codec: the result
is the `R_q` key material. This is the SPECIFICATION side of the keygen refinement. -/
def mldsaKeygenRing (xi : List UInt8) : RingKey := Id.run do
  let g := shake256 (xi ++ [UInt8.ofNat paramK, UInt8.ofNat paramL]) 128
  let rho  := g.take 32
  let rhoP := (g.drop 32).take 64
  let kk   := g.drop 96
  let aHat := expandA rho                                   -- Â[i][j] at index i·ℓ+j (NTT domain)
  let (s1, s2) := expandS rhoP
  let s1Hat := s1HatOf s1
  let (t1v, t0v) := tLoop aHat s1Hat s2
  return { rho := rho, kk := kk, s1 := s1, s2 := s2, t1 := t1v, t0 := t0v }

/-- **`skEncode` — FIPS 204 Algorithm 24** at the ML-DSA-65 parameters:
`sk = ρ ‖ K ‖ tr ‖ BitPack(s1, η, η) ‖ BitPack(s2, η, η) ‖ BitPack(t0, 2^{d−1}−1, 2^{d−1})`
(32 + 32 + 64 + ℓ·128 + k·128 + k·416 = 4032 bytes). -/
def skEncode (rho kk tr : List UInt8) (s1 s2 t0 : Array Poly) : List UInt8 := Id.run do
  let mut sk : List UInt8 := rho ++ kk ++ tr
  for i in [0:paramL] do
    sk := sk ++ (packEta s1[i]!).toList
  for i in [0:paramK] do
    sk := sk ++ (packEta s2[i]!).toList
  for i in [0:paramK] do
    sk := sk ++ (packT0 t0[i]!).toList
  return sk

/-! ## ML-DSA.KeyGen_internal (FIPS 204 Algorithm 6) — the deterministic keygen from a 32-byte `ξ`. -/

/-- **`ML-DSA.KeyGen_internal(ξ)`** (FIPS 204 Algorithm 6) for ML-DSA-65 — the RING generator composed
with the BYTE codecs. Steps 1–5 are `mldsaKeygenRing` (`(ρ,ρ′,K) = H(ξ ‖ k ‖ ℓ, 128)`; `Â = ExpandA(ρ)`;
`(s1,s2) = ExpandS(ρ′)`; `t̂[i] = Σⱼ Â[i][j] ∘ NTT(s1[j])`, `t[i] = NTT⁻¹(t̂[i]) + s2[i]`;
`(t1,t0) = Power2Round(t)`); steps 6–8 are the byte layer `pk = pkEncode(ρ, t1)`; `tr = H(pk, 64)`;
`sk = skEncode(ρ, K, tr, s1, s2, t0)`. Input `xi` is the 32-byte seed. Returns `(pk, sk)` — the 1952-byte
public key and the 4032-byte secret key. -/
def mldsaKeygenInternal (xi : List UInt8) : (List UInt8 × List UInt8) :=
  let rk := mldsaKeygenRing xi
  let pk := pkEncode (rk.rho, rk.t1)
  let tr := shake256 pk 64
  (pk, skEncode rk.rho rk.kk tr rk.s1 rk.s2 rk.t0)

/-! ## THE `@[export]` FFI ENTRY (Rust → Lean) — the REAL, FULL-BYTE ML-DSA-65 KEY GENERATION over a byte wire.

The KEYGEN analog of `dregg_mlkem_keygen_real`. `dregg-pq`'s `MlDsaKey::from_ed25519_seed` currently mints the
NODE IDENTITY ML-DSA key by calling the `fips204` crate's `keygen_from_seed`. This export routes THAT call
through the Lean-verified `mldsaKeygenInternal` (KAT-anchored byte-exact vs the NIST ACVP vectors in
`MlDsaKeygenAcvp`), so the `fips204` crate leaves the node's IDENTITY-KEY KEYGEN TCB. The caller supplies its
own 32-byte `ξ` seed; the returned `(pk, sk)` are used verbatim. -/

/-- The real byte wire `hex(ξ)` (64 hex chars = 32 bytes) the keygen FFI reads. -/
def realWireKeygen (xi : List UInt8) : String := hexEncode xi

/-- **FFI entry** (Rust→Lean) for the REAL, FULL-BYTE ML-DSA-65 KEYGEN: parse the single hex field `hex(ξ)`,
require exactly 32 decoded bytes, run the Lean-verified `mldsaKeygenInternal`, and return `hex(pk) hex(sk)` —
the 1952-byte public key and the 4032-byte secret key, two space-separated lowercase-hex fields. Any malformed
wire (non-hex, odd length, ≠ 32 bytes) fails CLOSED (`"ERR"`). -/
@[export dregg_mldsa_keygen_real]
def mldsaKeygenRealFFI (input : String) : String :=
  match decodeHexChars input.toList with
  | some xi =>
    if xi.length == 32 then
      let (pk, sk) := mldsaKeygenInternal xi
      hexEncode pk ++ " " ++ hexEncode sk
    else "ERR"
  | none => "ERR"

-- A malformed wire fails CLOSED (interpreted `#guard`, fast): non-hex, odd-length hex, wrong seed length.
#guard mldsaKeygenRealFFI "zz" = "ERR"
#guard mldsaKeygenRealFFI "0" = "ERR"
#guard mldsaKeygenRealFFI "00" = "ERR"

/-! ## THE OPEN REFINEMENT OBLIGATION (stated, NOT proved — no `sorry`, just the named goal).

The KATs in `MlDsaKeygenAcvp` are single-vector `native_decide` agreements with NIST; they are NOT a for-all
correctness proof. The genuine for-all refinement — that the BYTE-level `mldsaKeygenInternal` is the byte
encoding of an abstract RING-level ML-DSA KeyGen (identical H/ExpandA/ExpandS/matmul/Power2Round, stopping
BEFORE the byte codecs `pkEncode`/`skEncode`) — is OPEN. Written out, with

  `mldsaKeygenRing (ξ) : Array Poly × Array Poly × Array Poly × List UInt8 × List UInt8`   -- `(t1, s1, s2, ρ, K)` etc.

the target is that decoding the emitted `pk` recovers exactly the abstract `(ρ, t1)` and decoding `sk` recovers
exactly `(ρ, K, tr, s1, s2, t0)` — i.e. `pkDecode (pk) = (ρ, t1)` and `skDecode (sk) = (ρ, K, tr, s1, s2, t0)`.
This reduces to the EXISTING codec round-trip lemmas (`MlDsaCodec.pk_roundtrip` and the `BitPack`/`BitUnpack`
inverses) once the per-coefficient bounds (`t1[i] < 2^{10}`, `Power2Round` `t0 ∈ (−2^{d−1}, 2^{d−1}]`,
`ExpandS` `s ∈ [−η, η]`) are discharged over the `Id.run do` loops — that bound propagation is the remaining
work and is NOT discharged here.

Also OPEN (the larger goal): the ML-DSA EUF-CMA / correctness theorem (a signature under a freshly generated
`(pk, sk)` verifies for all messages) — out of scope for this lane. -/

end Dregg2.Crypto.MlDsaKeygen
