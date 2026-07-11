/-
# `Dregg2.Crypto.MlDsaSigCodecClosed` — the ML-DSA signature codec round-trip, RESIDUAL-FREE.

`CodecRoundTrip.sigDecode_sigEncode` proved `sigDecode ∘ sigEncode = id` for all well-formed `(c̃, z, h)`
carrying ONE named hypothesis: `hhint : hintDecode (sigEncode …) hoff = some h` — the FIPS 204
`HintBitUnpack ∘ HintBitPack = id` round-trip on the hint region. `MlDsaHintCodec.hintDecode_hintEncode` /
`hintDecode_append` closed that direction as a real ∀-theorem (pure `Array`/`Nat` combinatorics). THIS module
discharges the hypothesis, giving the FULL signature codec round-trip with NO hint hypothesis — only the
structural well-formedness of `h` (`k = 6` size-256 `{0,1}` polys, cumulative set-bit weight `≤ ω`), exactly
the shape the deployed hint carries. The named `hhint` residual is gone.
-/
import Dregg2.Crypto.CodecRoundTrip
import Dregg2.Crypto.MlDsaHintCodec

namespace Dregg2.Crypto.MlDsaSigCodecClosed

open Dregg2.Crypto.MlDsaCodec
open Dregg2.Crypto.MlDsaRing (Poly q)

set_option maxRecDepth 8000

/-- `(sigEncode (c̃, z, h)).toArray = zPart ++ hintEncode h` (the `zPart ‖ hint` byte layout, as an array). -/
theorem sigEncode_toArray (ctilde : List UInt8) (z h : Array Poly) :
    (sigEncode (ctilde, z, h)).toArray
      = (List.foldl (fun out i => out ++ packBits (Dregg2.Crypto.CodecRoundTrip.zFieldsOf (z[i]!)) zBits)
          ctilde.toArray (List.range' 0 paramL 1)) ++ hintEncode h := by
  rw [Dregg2.Crypto.CodecRoundTrip.sigEncode_unfold]

/-- **THE FULL SIGNATURE CODEC ROUND-TRIP, RESIDUAL-FREE.** `sigDecode (sigEncode (c̃, z, h)) = (c̃, z, h)`
for all well-formed structured values — `c̃` length 48, `ℓ = 5` size-256 `z` polys in the `BitUnpack`
codomain, and a well-formed hint `h` (`k = 6` size-256 `{0,1}` polys, cumulative set-bit weight `≤ ω`). The
former `hhint` hint-decode hypothesis is DISCHARGED here by `MlDsaHintCodec.hintDecode_append` (the FIPS 204
`HintBitUnpack ∘ HintBitPack = id` round-trip). No hint assumption remains — the byte codec of Seam 1's VERIFY
direction is fully closed. -/
theorem sigDecode_sigEncode_closed (ctilde : List UInt8) (z h : Array Poly)
    (hct : ctilde.length = cTildeLen) (hz : z.size = paramL)
    (hzsz : ∀ i, i < paramL → (z[i]!).size = 256)
    (hzcod : ∀ i, i < paramL → ∀ j, j < 256 →
      ((z[i]!)[j]! ≤ gamma1 ∨ (q - gamma1 < (z[i]!)[j]! ∧ (z[i]!)[j]! < q)))
    (hhsz : h.size = paramK)
    (hhpsz : ∀ i, i < paramK → (h[i]!).size = 256)
    (hhbit : ∀ i, i < paramK → ∀ j, j < 256 → (h[i]!)[j]! = 0 ∨ (h[i]!)[j]! = 1)
    (hhwt : Dregg2.Crypto.MlDsaHintCodec.cw h paramK ≤ omega) :
    sigDecode (sigEncode (ctilde, z, h)) = (ctilde, z, h) := by
  apply Dregg2.Crypto.CodecRoundTrip.sigDecode_sigEncode ctilde z h hct hz hzsz hzcod
  have hblocksz : ∀ i, i < paramL →
      (packBits (Dregg2.Crypto.CodecRoundTrip.zFieldsOf (z[i]!)) zBits).size = zPolyBytes := by
    intro i hi
    rw [Dregg2.Crypto.VerifyCoreEqSpec.packBits_size, Dregg2.Crypto.CodecRoundTrip.zFieldsOf_size]; decide
  have hZsz := (Dregg2.Crypto.CodecRoundTrip.appendFold_spec
    (fun i => packBits (Dregg2.Crypto.CodecRoundTrip.zFieldsOf (z[i]!)) zBits) zPolyBytes
    ctilde.toArray paramL hblocksz).1
  have hctsz : ctilde.toArray.size = cTildeLen := by simp [hct]
  rw [hctsz] at hZsz
  rw [sigEncode_toArray]
  set zPart := List.foldl (fun out i => out ++ packBits (Dregg2.Crypto.CodecRoundTrip.zFieldsOf (z[i]!)) zBits)
    ctilde.toArray (List.range' 0 paramL 1) with hzP
  rw [show cTildeLen + paramL * zPolyBytes = zPart.size from hZsz.symm]
  exact Dregg2.Crypto.MlDsaHintCodec.hintDecode_append zPart h hhsz hhpsz hhbit hhwt

/-- **Non-vacuity**: the residual-free round-trip FIRES on the genuine `fips204` crate signature. -/
theorem sigDecode_sigEncode_closed_witness :
    sigDecode (sigEncode (sigDecode realSig.toList)) = sigDecode realSig.toList := by native_decide

#assert_axioms sigDecode_sigEncode_closed

end Dregg2.Crypto.MlDsaSigCodecClosed
