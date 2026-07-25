/-
# `Dregg2.Crypto.Fips204ChallengeHash` — the FIPS 204 Algorithm 8 line-5 CHALLENGE HASH,
built ENTIRELY out of standard-side objects, and the theorem that the deployed expression computes it.

## What this is for

`Fips204Spec.MlDsaParams` carries the Fiat–Shamir hash as a GENERIC FIELD `hash : Msg → HB → Cbar`.
A field constrains nothing: fill it with the implementation's own expression and "prove" that the
implementation equals the projection, and the proof is `rfl` with zero FIPS content. That is the trap
`VerifyCoreHashFrame` fell into (twice, at two different depths — see its header). The only exit is to
BUILD the value the field gets from the STANDARD, in objects that mention no executable at all, and then
prove the deployed expression equals it.

FIPS 204 Algorithm 8, line 5 (ML-DSA-65, `λ = 192`):

    c̃ ← H( μ ‖ w1Encode(w₁) , λ/4 = 48 bytes )        with H = SHAKE256 (FIPS 202 §6.2)

`challengeHashSpec` below is exactly that sentence, with BOTH halves standard-side:

* the ENCODER is `Fips204BitPack.w1EncodeSpec` — FIPS 204 Alg. 28 over Alg. 16 `SimpleBitPack`,
  Alg. 10 `BitsToBytes`, Alg. 9 `IntegerToBits`, bit-indexed, mentioning the deployed `packBits`
  NOWHERE (that file's `w1Encode_eq_spec` is the theorem that the deployed bignum packer agrees);
* the HASH is `Keccak.Fips202.SHAKE256` — the BIT-ADDRESSED FIPS 202 §4/§5.1/§5.2/§6.2 sponge
  (`pad10*1`, `spongeAbsorb`, `spongeSqueeze` over the bit-function `Keccak-f[1600]` of
  `Fips202Spec`). It is not the executable: it has no `UInt64` lanes, no `Array` state, no
  `Keccak.absorb`. That the executable `Keccak.shake256` computes it is
  `Fips202SpongeRefine.shake256_refines_SHAKE256`, threaded here as the named obligation
  `Fips202Refine.SpongeRefinesObligation`;
* the BYTES ↔ BITS conversion is FIPS 202 §B.1 in both directions — `Fips202.bitsOfBytes` (already in
  the sponge spec) and `bytesOfBits` (its inverse, defined here as the standard's `Σ_{j<8} bit·2^j`
  byte reassembly), with `bytesOfBits_bitsOfBytes` the proved round-trip.

## What `challengeHash_frames` therefore contains

Two independent, falsifiable identifications, composed:

1. **encoding** — the deployed little-endian mixed-radix bignum packer emits the byte string FIPS 204
   Alg. 28 specifies (`Fips204BitPack.w1Encode_eq_spec`, whose core is the positional-numeral theorem
   `packNat_bit`);
2. **hashing** — the deployed `UInt64`-lane byte-addressed sponge emits the byte string whose §B.1 bit
   string is FIPS 202 §6.2's `SHAKE256` of the input's bit string (`shake256_refines_SHAKE256`, which
   rests on `keccakF_refines_spec`: θ ρ π χ ι bit-for-bit against FIPS 202 §3.2).

Neither side `whnf`-reduces to the other; deleting either input breaks the build. A wrong packing
width, endianness, row order, coefficient mask, rate, pad rule or domain byte on the deployed side
falsifies the statement.

## What is TRANSCRIBED and not proved (the honest residue)

That FIPS 204 Alg. 8's `H` IS SHAKE256, that the digest is `λ/4 = 48` bytes, and that the hash input is
`μ ‖ w1Encode(w₁)` in that order — these are readings of the standard's line 5, and they are stated in
`challengeHashSpec` for a reader to diff against the standard. No theorem can establish a transcription;
what a theorem CAN do is force everything below the transcription to be the standard's own objects, and
that is what this file does. (Collision resistance of SHAKE256 is a different axis entirely — the
`HashSig`/`FoQrom` floor.)

## Axioms

Everything here is stated with the sponge refinement as an EXPLICIT hypothesis, so the theorems are
`#assert_axioms`-clean. The instantiated corollary `challengeHash_frames_deployed` discharges that
hypothesis with `Fips202SpongeRefine.sponge_refines` — and that discharge now costs NOTHING. The whole
Keccak refinement chain is AXIOM-CLEAN: `rc_lanes_eq_exec` (the cross-check of the 24 precomputed
round-constant lanes against FIPS 202 Alg. 5's LFSR) is closed by a KERNEL `decide` on top of the
structurally recursive twin in `Keccak.Fips202Lfsr`, so `Lean.ofReduceBool` and `Lean.trustCompiler`
are GONE from it and from everything above it. Measured: `challengeHash_frames_deployed` depends on
axioms `[propext, Classical.choice, Quot.sound]`. The full re-measured table is in
`Dregg2/Crypto/AXIOM-PICTURE.md`.
-/
import Dregg2.Crypto.Fips204BitPack
import Dregg2.Crypto.Keccak.Fips202SpongeRefine

namespace Dregg2.Crypto.Fips204ChallengeHash

open Dregg2.Crypto.Keccak (shake256)
open Dregg2.Crypto.Keccak.Fips202 (bitsOfBytes bitsOfBytes_getD SHAKE256)
open Dregg2.Crypto.Keccak.Fips202Refine (SpongeRefinesObligation)
open Dregg2.Crypto.MlDsaRing (Poly)
open Dregg2.Crypto.MlDsaCodec (paramK)
open Dregg2.Crypto.MlDsaVerifyReal (w1Encode)
open Dregg2.Crypto.Fips204BitPack (w1EncodeSpec w1Encode_eq_spec)

/-! ## PART 1 — FIPS 202 §B.1, backwards: bits → bytes.

`Fips202.bitsOfBytes` is §B.1 forwards (byte `i` supplies bits `8i … 8i+7`, least significant first).
The sponge spec emits a BIT string; FIPS 202 §B.1 reads it back as bytes by the same convention, which
is the `Σ_{j<8} bit(8n+j)·2^j` reassembly below. Nothing here mentions the executable. -/

/-- FIPS 202 §B.1 read backwards: byte `n` of a bit string is `Σ_{j<8} bit(8n+j)·2^j` (least
significant bit first — the same convention `Fips202.bitsOfByte` uses forwards). -/
def byteOfBits (bits : List Bool) (n : Nat) : UInt8 :=
  UInt8.ofNat (∑ j ∈ Finset.range 8, (bits.getD (8 * n + j) false).toNat * 2 ^ j)

/-- FIPS 202 §B.1 read backwards on a whole bit string: `⌊|bits| / 8⌋` bytes. -/
def bytesOfBits (bits : List Bool) : List UInt8 :=
  (List.range (bits.length / 8)).map (byteOfBits bits)

/-- `(x.testBit i).toNat = ⌊x / 2^i⌋ mod 2` — the arithmetic form of a bit. -/
theorem toNat_testBit (x i : Nat) : (x.testBit i).toNat = x / 2 ^ i % 2 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ i) with h | h <;> simp [h]

/-- **Byte reassembly.** A byte is the `Σ_{j<8} bit_j · 2^j` of its own eight little-endian bits. -/
theorem sum_bits_eq_toNat (b : UInt8) :
    (∑ j ∈ Finset.range 8, (b.toBitVec.getLsbD j).toNat * 2 ^ j) = b.toNat := by
  have hlt : b.toBitVec.toNat < 256 := b.toBitVec.isLt
  have hb : b.toNat = b.toBitVec.toNat := rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, BitVec.getLsbD, toNat_testBit, hb]
  omega

/-- **The §B.1 round-trip — a real `∀`.** Reading a byte string as bits (§B.1 forwards) and
reassembling it (§B.1 backwards) is the identity, on EVERY byte string. This is what lets a digest
computed as a BIT string by the FIPS 202 spec sponge be compared with the deployed BYTE digest. -/
theorem bytesOfBits_bitsOfBytes (bs : List UInt8) : bytesOfBits (bitsOfBytes bs) = bs := by
  apply List.ext_getElem
  · simp [bytesOfBits]
  · intro n h1 h2
    simp only [bytesOfBits, List.getElem_map, List.getElem_range, byteOfBits]
    have hbit : ∀ j ∈ Finset.range 8,
        ((bitsOfBytes bs).getD (8 * n + j) false).toNat * 2 ^ j
          = (bs[n].toBitVec.getLsbD j).toNat * 2 ^ j := by
      intro j hj
      have hj8 : j < 8 := Finset.mem_range.mp hj
      rw [bitsOfBytes_getD bs (8 * n + j),
        show (8 * n + j) / 8 = n by omega, show (8 * n + j) % 8 = j by omega,
        List.getD_eq_getElem bs 0 h2]
    rw [Finset.sum_congr rfl hbit, sum_bits_eq_toNat]
    simp

/-! ## PART 2 — the standard's challenge hash, and the framing theorem. -/

/-- **FIPS 204 Algorithm 8, line 5 — THE SPEC SIDE, standard objects only.**
`c̃ = H(μ ‖ w1Encode(w₁), λ/4)` at ML-DSA-65 (`λ = 192`, so 48 bytes = 384 bits), with

* `w1Encode` = `Fips204BitPack.w1EncodeSpec` (FIPS 204 Alg. 28 / 16 / 10 / 9), and
* `H` = `Keccak.Fips202.SHAKE256` (FIPS 202 §6.2 over the §4 sponge and the §3 bit-function
  permutation), input and output carried across FIPS 202 §B.1.

No executable definition occurs in this term: not `Keccak.shake256`, not `MlDsaCodec.packBits`, not
`MlDsaVerifyReal.w1Encode`. -/
def challengeHashSpec (μ : List UInt8) (w1 : Array Poly) : List UInt8 :=
  bytesOfBits (SHAKE256 (bitsOfBytes (μ ++ w1EncodeSpec w1)) 384)

/-- **THE FRAMING THEOREM — a real `∀`, and not `rfl`.** For EVERY framed message `μ` and EVERY
`k = 6`-row high-bits array with 256 coefficients per row, the DEPLOYED challenge digest
`Keccak.shake256 (μ ‖ MlDsaVerifyReal.w1Encode w₁) 48` — the exact expression inside
`MlDsaVerifyReal.verifyCore` / `VerifyCoreSpec.challengeMatches` — IS FIPS 204 Algorithm 8 line 5's
`H(μ ‖ w1Encode(w₁), 48)` computed from the standard.

The proof consumes two independent refinements and nothing else:
`Fips204BitPack.w1Encode_eq_spec` (the deployed bignum packer is Alg. 28/16/10/9) and the sponge
obligation `hSponge` (the deployed `UInt64`-lane sponge is FIPS 202 §6.2 SHAKE256), glued by the §B.1
round-trip. The sponge refinement is taken as a HYPOTHESIS here so this theorem is axiom-clean; it is
discharged in `challengeHash_frames_deployed`. -/
theorem challengeHash_frames (hSponge : SpongeRefinesObligation)
    (μ : List UInt8) (w1 : Array Poly) (hrow : ∀ i, i < paramK → (w1[i]!).size = 256) :
    shake256 (μ ++ w1Encode w1) 48 = challengeHashSpec μ w1 := by
  calc shake256 (μ ++ w1Encode w1) 48
      = shake256 (μ ++ w1EncodeSpec w1) 48 := by rw [w1Encode_eq_spec w1 hrow]
    _ = bytesOfBits (bitsOfBytes (shake256 (μ ++ w1EncodeSpec w1) 48)) :=
        (bytesOfBits_bitsOfBytes _).symm
    _ = bytesOfBits (SHAKE256 (bitsOfBytes (μ ++ w1EncodeSpec w1)) (8 * 48)) := by
        rw [hSponge.1 (μ ++ w1EncodeSpec w1) 48]
    _ = challengeHashSpec μ w1 := by norm_num [challengeHashSpec]

/-- **The framing theorem with the sponge obligation DISCHARGED.** `Fips202SpongeRefine.sponge_refines`
is a proof of `SpongeRefinesObligation`, so the deployed digest IS the standard's, unconditionally.

AXIOM NOTE (measured, not asserted): this corollary is axiom-CLEAN —
`[propext, Classical.choice, Quot.sound]`. It USED to carry `Lean.ofReduceBool` via
`Fips202Refine.rc_lanes_eq_exec`; that cross-check of the 24 precomputed round-constant LANES against
the FIPS 202 Alg. 5 LFSR is now a KERNEL `decide` (`Keccak.Fips202Lfsr.rc_lanes_all`), so no
compiled-evaluation trust enters here at all. That one step is still FINITE (a 24×64-bit constant
table, not a `∀`), but the checker is the kernel. Everything else in the chain is a `∀`-theorem.
`#assert_axioms` is pinned on `challengeHash_frames` (hypothesis form) and this one is reported by
`#print axioms`, so a regression in the Keccak floor surfaces here rather than being laundered. -/
theorem challengeHash_frames_deployed
    (μ : List UInt8) (w1 : Array Poly) (hrow : ∀ i, i < paramK → (w1[i]!).size = 256) :
    shake256 (μ ++ w1Encode w1) 48 = challengeHashSpec μ w1 :=
  challengeHash_frames Dregg2.Crypto.Keccak.Fips202SpongeRefine.sponge_refines μ w1 hrow

/-! ## PART 3 — teeth.

The §B.1 conversions COMPUTE (they are not stubs), in both directions and on the two bytes whose bit
patterns the SHAKE domain separation actually uses (`0x1F = 11111000` little-endian, `0x80 = 00000001`).
The spec sponge's own anti-vacuity anchor is `Fips202SpongeRefine.spec_SHAKE256_empty_cavp` (the NIST
CAVP `SHAKE256("")` answer, produced by the SPEC side), and the spec encoder's is
`Fips204BitPack`'s Alg. 16 evaluations. -/

example : bytesOfBits (bitsOfBytes [0x1F, 0x80]) = [0x1F, 0x80] := by decide
example : bytesOfBits (bitsOfBytes [0x00, 0xFF, 0xA5]) = [0x00, 0xFF, 0xA5] := by decide
example : bitsOfBytes [0x1F] = [true, true, true, true, true, false, false, false] := by decide

#assert_axioms toNat_testBit
#assert_axioms sum_bits_eq_toNat
#assert_axioms bytesOfBits_bitsOfBytes
#assert_axioms challengeHash_frames

-- Reported, NOT asserted: the one `Lean.ofReduceBool` (the RC-lane table KAT) inherited from the
-- Keccak floor when the sponge obligation is discharged.
#print axioms challengeHash_frames_deployed

end Dregg2.Crypto.Fips204ChallengeHash
