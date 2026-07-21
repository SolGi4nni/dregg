/-
# `Dregg2.Crypto.MlKemKeygen` — the REAL ML-KEM-768 KEY GENERATION (FIPS 203), EXECUTABLE `def`s.

BRICK K7 — the KEYGEN mirror of K4 (`MlKemDecaps`) / K5 (`MlKemEncaps`). K4 assembled the full-dimension FO
DECAPS and K5 the deterministic ENCAPS; this module builds the third and last ML-KEM leg — the DETERMINISTIC
KEY GENERATION from a 64-byte `(d ‖ z)` seed. It REUSES the existing full-dimension pieces (no reinvention):
`expandMatrix` / `samplePolyCBD` (K2 `MlKemSample`), `ntt` / `pointwiseNtt` / `addPoly` (K1 `MlKemRing`),
`byteEncode` / `ekEncode` (K3 `MlKemCodec`), and the `sha3_512` (`G`) / `sha3_256` (`H`) / `prf` (`PRF_η`)
already built in K4 (`MlKemDecaps`).

## ML-KEM-768 parameters (FIPS 203 §8): `k = 3`, `η1 = η2 = 2`, `n = 256`, `q = 3329`.

## K-PKE.KeyGen(d)  (FIPS 203, the deterministic PKE key generation)
```
1: (ρ,σ) ← G(d ‖ k)              -- G = SHA3-512 (64 B, split 32+32); k = 3 encoded as ONE byte
2: Â[i][j] ← SampleNTT(ρ ‖ j ‖ i)                 -- expandMatrix (Â[i][j] at index i·k+j)
3: for i<k:  s[i] ← SamplePolyCBD_η1(PRF_η1(σ, N)); N++
4: for i<k:  e[i] ← SamplePolyCBD_η1(PRF_η1(σ, N)); N++
5: ŝ ← NTT(s);  ê ← NTT(e)
6: t̂[i] ← Σⱼ Â[i][j] ∘ ŝ[j] + ê[i]               -- KeyGen uses Â (NOT the transpose Âᵀ that Encrypt uses)
7: ekPKE ← ByteEncode₁₂(t̂) ‖ ρ                    -- ekEncode (t̂, ρ)
8: dkPKE ← ByteEncode₁₂(ŝ)
```
Note the **final-FIPS-203** domain separation: step 1 appends the byte `k = 3` to `d` before `G`. (The IPD
draft did NOT append it; the ACVP anchor below is the FINAL standard, so a missing/ wrong byte breaks the KAT.)

## ML-KEM.KeyGen_internal(d, z)  (FIPS 203, the deterministic KEM wrapper)
```
1: (ekPKE, dkPKE) ← K-PKE.KeyGen(d)
2: ek ← ekPKE
3: dk ← dkPKE ‖ ek ‖ H(ek) ‖ z                    -- H = SHA3-256 (32 B)
4: return (ek, dk)
```
The KAT anchor (in `MlKemKeygenAcvp`) is the NIST ACVP `ML-KEM-keyGen-FIPS203` vector set, NOT a crate.

READ THE STATEMENTS, NOT THIS PROSE. The gates in `MlKemKeygenAcvp` are SINGLE-VECTOR `native_decide` KATs
(no `forall`): they show byte-exact agreement with the NIST reference on specific seeds — evidence, not a
for-all correctness proof. The for-all obligation (the byte↔ring KeyGen refinement) is stated EXPLICITLY at
the bottom of this file and is OPEN.

`native_decide` runs the COMPILED `def`s; its trusted base is `Lean.ofReduceBool` + `Lean.trustCompiler` — the
SAME residual K1–K6 already name. No `sorry`, no user `axiom`, no toy substitute.
-/
import Dregg2.Crypto.Keccak
import Dregg2.Crypto.MlKemRing
import Dregg2.Crypto.MlKemSample
import Dregg2.Crypto.MlKemCodec
import Dregg2.Crypto.MlKemDecaps

namespace Dregg2.Crypto.MlKemKeygen

open Dregg2.Crypto.MlKemRing (Poly zeroPoly ntt pointwiseNtt addPoly)
open Dregg2.Crypto.MlKemSample (expandMatrix samplePolyCBD)
open Dregg2.Crypto.MlKemCodec (paramK dCoeff polyBytes byteEncode ekEncode)
open Dregg2.Crypto.MlKemDecaps (sha3_256 sha3_512 prf hexEncode decodeHexChars)

/-! ## K-PKE.KeyGen (FIPS 203) — the deterministic PKE key generation from a 32-byte seed `d`. -/

/-- **`K-PKE.KeyGen(d)`** (FIPS 203). `(ρ,σ) = G(d ‖ k)` (`G = SHA3-512`, split 32+32, `k = 3` as one byte);
`Â = ExpandMatrix(ρ)`; sample `s` (`N = 0…k-1`) and `e` (`N = k…2k-1`) from `PRF_η1(σ,N)` (`η1 = 2`);
`ŝ = NTT(s)`, `ê = NTT(e)`; `t̂[i] = Σⱼ Â[i][j] ∘ ŝ[j] + ê[i]` (using `Â`, index `i·k+j` — NOT the `Âᵀ`
transpose that Encrypt uses); return `(ekPKE = ByteEncode₁₂(t̂) ‖ ρ, dkPKE = ByteEncode₁₂(ŝ))`. -/
def kpkeKeyGen (d : List UInt8) : (List UInt8 × List UInt8) := Id.run do
  let g := sha3_512 (d ++ [UInt8.ofNat paramK])        -- G(d ‖ k) → 64 bytes
  let rho := g.take 32
  let sigma := g.drop 32
  let aHat := expandMatrix rho                          -- Â[i][j] at index i·k+j
  -- sample s (η1) at N = 0..k-1, then e (η1) at N = k..2k-1; ML-KEM-768 has η1 = 2
  let mut s : Array Poly := #[]
  let mut n : Nat := 0
  for _ in [0:paramK] do
    s := s.push (samplePolyCBD 2 (prf 2 sigma n)); n := n + 1
  let mut e : Array Poly := #[]
  for _ in [0:paramK] do
    e := e.push (samplePolyCBD 2 (prf 2 sigma n)); n := n + 1
  -- ŝ = NTT(s), ê = NTT(e)
  let mut sHat : Array Poly := #[]
  for i in [0:paramK] do
    sHat := sHat.push (ntt s[i]!)
  let mut eHat : Array Poly := #[]
  for i in [0:paramK] do
    eHat := eHat.push (ntt e[i]!)
  -- t̂[i] = NTT-domain (Σⱼ Â[i][j] ∘ ŝ[j]) + ê[i]
  let mut tHat : Array Poly := #[]
  for i in [0:paramK] do
    let mut acc : Poly := zeroPoly
    for j in [0:paramK] do
      acc := addPoly acc (pointwiseNtt aHat[i * paramK + j]! sHat[j]!)
    tHat := tHat.push (addPoly acc eHat[i]!)
  -- ekPKE = ByteEncode₁₂(t̂) ‖ ρ  ;  dkPKE = ByteEncode₁₂(ŝ)
  let ek := ekEncode (tHat, rho)
  let mut dkPke : List UInt8 := []
  for i in [0:paramK] do
    dkPke := dkPke ++ byteEncode dCoeff sHat[i]!
  return (ek, dkPke)

/-! ## ML-KEM.KeyGen_internal (FIPS 203) — the deterministic KEM wrapper from a 64-byte `(d ‖ z)` seed. -/

/-- **`ML-KEM.KeyGen_internal(d, z)`** (FIPS 203). `(ekPKE, dkPKE) = K-PKE.KeyGen(d)`; `ek = ekPKE`;
`dk = dkPKE ‖ ek ‖ H(ek) ‖ z` (`H = SHA3-256`, 32 B). Input `dz` is the 64-byte concatenation `d ‖ z`
(`d = dz[0:32]`, `z = dz[32:64]`). Returns `(ek, dk)` — the 1184-byte encapsulation key and the 2400-byte
decapsulation key. -/
def mlkemKeygen (dz : List UInt8) : (List UInt8 × List UInt8) :=
  let d := dz.take 32
  let z := dz.drop 32
  let (ek, dkPke) := kpkeKeyGen d
  let dk := dkPke ++ ek ++ sha3_256 ek ++ z
  (ek, dk)

/-! ## THE `@[export]` FFI ENTRY (Rust → Lean) — the REAL, FULL-BYTE ML-KEM-768 KEY GENERATION over a byte wire.

BRICK K7's C-ABI entry — the KEYGEN analog of K6's `dregg_mlkem_decaps_real` / K5's `dregg_mlkem_encaps_real`.
The deployed hybrid-KEM setup (`dregg-pq`) currently produces the ML-KEM keypair by calling the `ml-kem`
crate's key generation. This export routes THAT call through the Lean-verified `mlkemKeygen` (proved byte-exact
vs the NIST ACVP vectors in `MlKemKeygenAcvp`), so the `ml-kem` crate leaves the node's KEM-KEYGEN TCB. The
caller supplies its own 64-byte `(d ‖ z)` seed (as the crate's randomized keygen samples internally); the
returned `(ek, dk)` are used verbatim and the crate's key generation is NOT called.

INSTALL PATH (do NOT wire this lane): register alongside the sibling exports in
`dregg-lean-ffi` (the crate that links the leanc-compiled metatheory and re-exports `dregg_mlkem_encaps_real` /
`dregg_mlkem_decaps_real`); the Rust seam swaps the `ml-kem` keygen call for `shadow_mlkem_keygen_real` once
the wire is confirmed byte-for-byte against the NIST vector (the KAT below already forces that). -/

/-- The real byte wire `hex(d ‖ z)` (128 hex chars = 64 bytes) the keygen FFI reads. -/
def realWireKeygen (dz : List UInt8) : String := hexEncode dz

/-- **FFI entry** (Rust→Lean) for the REAL, FULL-BYTE ML-KEM-768 KEYGEN (BRICK K7): parse the single hex field
`hex(d ‖ z)`, require exactly 64 decoded bytes, run the Lean-verified `mlkemKeygen`, and return
`hex(ek) hex(dk)` — the 1184-byte encapsulation key and the 2400-byte decapsulation key, two space-separated
lowercase-hex fields. Any malformed wire (non-hex, odd length, ≠ 64 bytes) fails CLOSED (`"ERR"`), which the
Rust caller treats as a keygen fault (fail-closed). -/
@[export dregg_mlkem_keygen_real]
def mlkemKeygenRealFFI (input : String) : String :=
  match decodeHexChars input.toList with
  | some dz =>
    if dz.length == 64 then
      let (ek, dk) := mlkemKeygen dz
      hexEncode ek ++ " " ++ hexEncode dk
    else "ERR"
  | none => "ERR"

-- A malformed wire fails CLOSED (interpreted `#guard`, fast): non-hex, odd-length hex, wrong seed length.
#guard mlkemKeygenRealFFI "zz" = "ERR"
#guard mlkemKeygenRealFFI "0" = "ERR"
#guard mlkemKeygenRealFFI "00" = "ERR"

/-! ## THE OPEN REFINEMENT OBLIGATION (stated, NOT proved — no `sorry`, just the named goal).

The KATs in `MlKemKeygenAcvp` are single-vector `native_decide` agreements with NIST; they are NOT a for-all
correctness proof. The genuine for-all refinement — that the BYTE-level `kpkeKeyGen` is the byte encoding of an
abstract RING-level KeyGen — is OPEN. Written out, the target is:

  Define the abstract ring-level generator
    `kpkeKeyGenRing (d) : Array Poly × Array Poly × List UInt8`   -- returns `(t̂, ŝ, ρ)`, NO ByteEncode
  (identical sampling/NTT/matmul, stopping BEFORE the byte codec). Then the OPEN goal is

    theorem kpkeKeyGen_refines_ring (d : List UInt8) :
        let (tHat, sHat, rho) := kpkeKeyGenRing d
        MlKemCodec.ekDecode (kpkeKeyGen d).1 = (tHat, rho)
        ∧ (∀ i, i < paramK →
             MlKemCodec.byteDecodeAt dCoeff (kpkeKeyGen d).2.toArray (i * polyBytes dCoeff) = sHat[i]!)

  i.e. decoding the emitted `ek` recovers exactly the abstract `t̂`/`ρ`, and decoding `dkPKE` recovers exactly
  the abstract `ŝ`. This is a REAL refinement (LHS = byte impl through the decoder, RHS = the abstract
  computation; it is NOT `rfl`). It reduces to the EXISTING codec round-trip lemmas in `MlKemCodecSpec`
  (`byteDecode₁₂_byteEncode₁₂ : byteDecode 12 (byteEncode 12 f) = f`, given `f.size = 256 ∧ ∀ j, f[j]! < q`)
  once one discharges the coefficient bounds `t̂[i]! < q` and `ŝ[i]! < q` — both hold because `addPoly` (via
  `addQ`) and `ntt` (via `addQ`/`subQ`/`mulModQ`) reduce every coefficient mod `q`, but that per-coefficient
  bound over the `Id.run do` loops is the remaining work and is NOT discharged here.

Also OPEN (the larger goal): the ML-KEM correctness theorem — that Decaps of a ciphertext Encaps'd under a
freshly generated `(ek, dk)` recovers the shared secret for all seeds — which is probabilistic (noise-bounded)
and out of scope for this lane. -/

end Dregg2.Crypto.MlKemKeygen
