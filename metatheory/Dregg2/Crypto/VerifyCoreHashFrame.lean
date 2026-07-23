/-
# `Dregg2.Crypto.VerifyCoreHashFrame` — the CONCRETE ML-DSA-65 `Fips204Spec.MlDsaParams` over `R_q^k`,
and the HASH-FRAMING leg of the FIPS 204 verify predicate.

## ★ THE VACUITY LEDGER — two collapses, at two different depths. Read before touching this file.

**Collapse 1 (the original file).** `hashFrame` read

    (shake256 (μ ++ w1Encode (hbToArray w1)) 48 == c̃) = decide ((mldsaParams ρ hbStable).hash μ w1 = c̃)

and its proof was `have hproj : … = shake256 (μ ++ w1Encode (hbToArray w1)) 48 := rfl; rw [hproj, …]`.
`hproj` was `rfl` because the file had set `hash := fun μ w1 => shake256 (μ ++ w1Encode (hbToArray w1)) 48`
— the field was filled with the IMPLEMENTATION's own expression and then projected back out.
`Fips204Spec.MlDsaParams.hash` is a GENERIC STRUCTURE FIELD (`hash : Msg → HB → Cbar`), constrained by
nothing anywhere in `Fips204Spec`; instantiating a `∀`-free field with the implementation and projecting
it is ALWAYS `rfl`. Mentioning `Fips204Spec` satisfied the LETTER of "the RHS references the spec" while
the RHS `whnf`-reduced to the LHS. The only residual content was `==` vs `decide`. Correctly rejected.

**Collapse 2 (the first repair — partial, and still not enough).** The field was re-filled with
`hash := fun μ w1 => shake256 (μ ++ w1EncodeSpec (hbToArray w1)) 48`, where `w1EncodeSpec` is FIPS 204
Alg. 28/16/10/9 written from the standard. That made the ENCODER side a real theorem
(`Fips204BitPack.w1Encode_eq_spec`, a positional-numeral argument, not `rfl`) — genuine content, kept.
But the HASH itself was still the EXECUTABLE `Keccak.shake256` on BOTH sides: the file said so in prose
("both sides call the SAME `Keccak.shake256`; that agreement is TRANSCRIPTION, not a theorem"). So the
spec side was still half implementation, and the `hproj := rfl` step still carried the executable sponge
through untouched. A hash-framing leg whose HASH is the implementation is not a hash-framing leg.

**What changed materially (this version).** `Keccak/Fips202Spec.lean`, `Keccak/Fips202Round.lean`,
`Keccak/Fips202Sponge.lean` and `Keccak/Fips202SpongeRefine.lean` now give a BIT-ADDRESSED FIPS 202
specification of the permutation AND the sponge, and prove the executable refines it
(`keccakF_refines_spec`, `shake256_refines_SHAKE256`). So the hash side can finally rest on the SPEC
sponge. `Dregg2.Crypto.Fips204ChallengeHash.challengeHashSpec` is FIPS 204 Alg. 8 line 5 with BOTH
halves standard-side — Alg. 28 encoder, FIPS 202 §6.2 `SHAKE256` bit sponge, §B.1 conversions — and
mentions NO executable definition. `mldsaParams.hash` is that object, and the framing equality is
`Fips204ChallengeHash.challengeHash_frames`, whose proof consumes the encoder refinement AND the sponge
refinement. The remaining `hproj := rfl` is a record projection of a value defined from the standard —
which is what a projection is supposed to be.

## THE HONEST RESIDUE OF THE HASH LEG (transcription, not theorem)

That FIPS 204 Alg. 8 line 5's `H` is SHAKE256, that the digest is `λ/4 = 48` bytes at `λ = 192`, and
that the input is `μ ‖ w1Encode(w₁)` in that order: these are readings of the standard's line 5, stated
in `Fips204ChallengeHash.challengeHashSpec` for a reader to diff against FIPS 204. No theorem can
establish a transcription. `hbToArray` (`Fin k → Fin 256 → ℤ` ↦ `Array Poly`) is a pure retyping shared
by both sides and carries no encoding decision — every encoding decision lives in `w1EncodeSpec`, every
hashing decision in the FIPS 202 sponge spec.

Collision resistance of SHAKE256 is a different axis (`HashSig`/`FoQrom` floor) and is not claimed here.

## ★ THE OPEN OBLIGATIONS, NAMED (no `sorry`, no new `axiom`)

* **`HighBitsStableK`** — Dilithium high-bits stability over `R_q`: `HighBits(r+s) = HighBits(r)` for
  `lowGap r`, `betaSmall s`. Over `R_q = ℤ_q[X]/(X²⁵⁶+1)` coordinates add MOD `q`, so this carries the
  number-theoretic `mod q` wrap plus `Decompose`'s `r − r₀ = q−1` boundary case. NOT proved; threaded as
  an explicit hypothesis, so `mldsaParams` is a FUNCTION of it and the gap sits in the type.
  `highBits_noWrap_stable` proves the WRAP-FREE fragment at the deployed `α = 523776`, `β = 196`,
  `q = 8380417` — pinning the residue to exactly the `ℤ_q` wrap and the `q−1` case.
* **the ARGUMENT leg** — that the `w₁` verify actually hashes is `UseHint(h, A·z − c·t₁·2^d)`. This is
  the `VerifyCoreEqSpec` / `VerifyCoreEqSpecW` / `VerifyCoreUseHint` line, closed per-coefficient
  (`w1Row_recovers_arg`) but NOT assembled into the six-row `w1Encode` argument. It enters
  `challengeMatches_eq_specHash` / `verifyCore_eq_specVerifyB` as the typed hypothesis `hArg` — a
  signature in the symbol table, not a paragraph.
* **the sponge refinement** is threaded as the named `Fips202Refine.SpongeRefinesObligation` in the
  `#assert_axioms`-clean statements, and DISCHARGED in the `_deployed` corollaries, which therefore
  inherit the Keccak floor's single compiled-evaluation residual (the `rc_lanes_eq_exec` round-constant
  table KAT). Reported by `#print axioms`, never laundered.
-/
import Dregg2.Crypto.VerifyCoreUseHint
import Dregg2.Crypto.Fips204Spec
import Dregg2.Crypto.Fips204ChallengeHash
import Dregg2.Crypto.MlDsaVerifyReal
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace Dregg2.Crypto.VerifyCoreHashFrame

open Dregg2.Crypto.VerifyCoreEqSpec (Rq r toRq cf pbW pbW_dim)
open Dregg2.Crypto.Fips204Spec (RoundingScheme MlDsaParams)
open Dregg2.Crypto.MlDsaRing (Poly q ntt intt)
open Dregg2.Crypto.MlDsaVerifyReal (w1Encode highBits decompose modpm alpha qI zBound infNormZ verifyCore)
open Dregg2.Crypto.MlDsaSampleInBall (sampleInBall)
open Dregg2.Crypto.VerifyCoreSpec (challengeMatches verifyCore_split)
open Dregg2.Crypto.Fips204ChallengeHash (challengeHashSpec challengeHash_frames)
open Dregg2.Crypto.Keccak (shake256)
open Dregg2.Crypto.Keccak.Fips202Refine (SpongeRefinesObligation)
open Dregg2.Crypto.MlDsaExpandA (expandA)
open Dregg2.Crypto.MlDsaCodec (paramK paramL sigDecode)

set_option maxRecDepth 8000

/-! ## PART 0 — the module types of ML-DSA-65. -/

/-- The response module `M = R_q^l` (`l = 5`). -/
abbrev Mv := Fin paramL → Rq
/-- The commitment module `N = R_q^k` (`k = 6`). -/
abbrev Nv := Fin paramK → Rq
/-- The high-bits / hint vector: `k` rows of `256` integer coordinates (`w₁` coeffs in `[0,16)`). An
`AddCommGroup` (Pi of ℤ), which is what makes the telescoping `MakeHint` well-typed. -/
abbrev HBv := Fin paramK → Fin 256 → ℤ

/-! ## PART 1 — reading `R_q` coordinates through the power basis. -/

/-- The `jj`-th power-basis coordinate of the `i`-th row of `x ∈ R_q^k`, as its canonical `ℤ_q` rep in
`[0, q)`. -/
noncomputable def coordN (x : Nv) (i : Fin paramK) (jj : Fin 256) : Nat :=
  (pbW.basis.repr (x i) (Fin.cast pbW_dim.symm jj)).val

/-- The same coordinate for the response module `M = R_q^l`. -/
noncomputable def coordM (z : Mv) (i : Fin paramL) (jj : Fin 256) : Nat :=
  (pbW.basis.repr (z i) (Fin.cast pbW_dim.symm jj)).val

/-! ## PART 2 — the concrete `R_q^k` rounding (`round` field). -/

/-- **`HighBits` over `R_q^k`** — coordinate-wise `MlDsaVerifyReal.highBits` (FIPS 204 Algorithm 38)
applied to each power-basis coordinate. -/
noncomputable def hbK (x : Nv) : HBv := fun i jj => highBits (coordN x i jj)

/-- **`MakeHint` over `R_q^k`** — the telescoping carry `HighBits(r+z) − HighBits(r)`. -/
noncomputable def makeHintK (z r : Nv) : HBv := hbK (r + z) - hbK r

/-- **`UseHint` over `R_q^k`** — recover the high bits corrected by the hint: `HighBits(r) + h`. -/
noncomputable def useHintK (h : HBv) (r : Nv) : HBv := hbK r + h

/-- **The hint round-trip, PROVED unconditionally.** `UseHint(MakeHint(z,r), r) = HighBits(r+z)` — a real
`∀` over the module, closed by the telescoping `MakeHint` definition, no hypothesis, no `native_decide`.
This IS the `RoundingScheme.useHint_makeHint` field of `mldsaParams`. -/
theorem useHintK_makeHintK (z r : Nv) : useHintK (makeHintK z r) r = hbK (r + z) := by
  simp only [useHintK, makeHintK]; abel

/-- `‖·‖ ≤ γ₂ = 261888` on the centered coordinates (the `MakeHint` precondition). -/
noncomputable def nearGamma2K (z : Nv) : Prop :=
  ∀ (i : Fin paramK) (jj : Fin 256),
    let n := coordN z i jj
    (if n ≤ q / 2 then (n : ℤ) else (n : ℤ) - (q : ℤ)) ≥ -261888 ∧
    (if n ≤ q / 2 then (n : ℤ) else (n : ℤ) - (q : ℤ)) ≤ 261888

/-- `‖·‖ ≤ β = 196` on the centered coordinates (the small-perturbation bound). -/
noncomputable def betaSmallK (s : Nv) : Prop :=
  ∀ (i : Fin paramK) (jj : Fin 256),
    let n := coordN s i jj
    (if n ≤ q / 2 then (n : ℤ) else (n : ℤ) - (q : ℤ)) ≥ -196 ∧
    (if n ≤ q / 2 then (n : ℤ) else (n : ℤ) - (q : ℤ)) ≤ 196

/-- `LowBits ∈ [β, α−β) = [196, 523580)` on each coordinate (the low-part bound the rejection loop
enforces). -/
noncomputable def lowGapK (r : Nv) : Prop :=
  ∀ (i : Fin paramK) (jj : Fin 256),
    196 ≤ ((coordN r i jj : Int) + 261888) % 523776 ∧
    ((coordN r i jj : Int) + 261888) % 523776 < 523776 - 196

/-- **★ AN OPEN GOAL — Dilithium high-bits stability over `R_q`.** A `β`-small perturbation of a
commitment with a `lowGap` low part leaves its high bits unchanged. Over `R_q` the coordinates add MOD `q`,
so this carries the `mod q` wrap (and `Decompose`'s `r − r₀ = q−1` boundary case) named as the deferred
"deployed-`ℤ_q` `Decompose`" sublemma in `Fips204Spec`/`Fips204Verify`. NOT proved here; threaded as an
explicit hypothesis into `mldsaParams`, so the gap is visible in the type. See `highBits_noWrap_stable`
for the wrap-free fragment that IS proved. -/
def HighBitsStableK : Prop := ∀ r s : Nv, lowGapK r → betaSmallK s → hbK (r + s) = hbK r

/-- **The concrete `R_q^k` `RoundingScheme`** — parameterized by the OPEN stability lemma `hbStable`.
Every other field is concrete; `useHint_makeHint` is discharged by `useHintK_makeHintK`. -/
noncomputable def roundK (hbStable : HighBitsStableK) : RoundingScheme Nv HBv HBv where
  highBits := hbK
  makeHint := makeHintK
  useHint := useHintK
  nearGamma2 := nearGamma2K
  betaSmall := betaSmallK
  lowGap := lowGapK
  useHint_makeHint z r _ := useHintK_makeHintK z r
  highBits_stable := hbStable

/-! ### The WRAP-FREE fragment of `highBits_stable`, at the DEPLOYED parameters — PROVED.

This is the part of the Dilithium stability lemma that does not involve the `ℤ_q` quotient: on canonical
reps whose sum does not reach the `Decompose` boundary, `MlDsaVerifyReal.highBits` (`Decompose`'s `r₁`,
`α = 523776`, `q = 8380417`) is genuinely stable under a `β = 196`-small nonnegative shift with a
low-gapped base. It pins down exactly what `HighBitsStableK` still owes: the `mod q` wrap and the `q−1`
boundary case. -/

/-- **The wrap-free high-bits stability, at the deployed `α`, `β`, `q` — a real `∀`.** Under exactly
`lowGapK`'s shifted low-bits window (`(a + γ₂) mod α ∈ [β, α−β)`, i.e. the centered `LowBits(a)` satisfies
`|r₀| ≤ γ₂ − β = 261692`) and a shift `b ≤ β = 196`, the deployed `MlDsaVerifyReal.highBits` is stable —
PROVIDED both canonical reps stay below `q` so that no `ℤ_q` wrap occurs. Both `Decompose` branches
(including the `r − r₀ = q−1` special case) are discharged. The `ℤ_q` wrap is what `HighBitsStableK` still
owes. -/
theorem highBits_noWrap_stable (a b : Nat) (hb : b ≤ 196)
    (ha : (a : Int) < 8380417) (hq : (a : Int) + (b : Int) < 8380417)
    (hlow : 196 ≤ ((a : Int) + 261888) % 523776 ∧ ((a : Int) + 261888) % 523776 < 523776 - 196) :
    highBits (a + b) = highBits a := by
  have ha0 : (0 : Int) ≤ (a : Int) := Int.natCast_nonneg a
  have hb0 : (0 : Int) ≤ (b : Int) := Int.natCast_nonneg b
  have hble : (b : Int) ≤ 196 := by exact_mod_cast hb
  have hcast : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by push_cast; ring
  have hma : (a : Int) % 8380417 = (a : Int) := Int.emod_eq_of_lt ha0 ha
  have hmab : ((a : Int) + (b : Int)) % 8380417 = (a : Int) + (b : Int) :=
    Int.emod_eq_of_lt (by omega) hq
  obtain ⟨hl1, hl2⟩ := hlow
  unfold highBits decompose modpm
  simp only [alpha, qI, hcast, hma, hmab, beq_iff_eq]
  split_ifs <;> omega

/-! ## PART 3 — the `A` / `hash` / `challenge` / `zBoundB` fields. -/

/-- The ML-DSA-65 public matrix `Â = expandA ρ` read back to `R_q` (`toRq ∘ intt`). Its `Matrix.mulVecLin`
is the genuine `M = R_q^l →ₗ[R_q] N = R_q^k` public map. -/
noncomputable def expandAMat (ρ : List UInt8) : Matrix (Fin paramK) (Fin paramL) Rq :=
  fun i j => toRq (intt ((expandA ρ)[(i : ℕ) * paramL + (j : ℕ)]!))

/-- One row of the `w₁` coefficient view: `256` integer high-bits coordinates as a `Poly`. -/
def hbRow (w1 : HBv) (i : Fin paramK) : Poly :=
  Array.ofFn (fun jj : Fin 256 => (w1 i jj).toNat)

/-- **A pure RETYPING**, not an encoding: read the abstract high-bits vector `w₁ : Fin k → Fin 256 → ℤ` as
the `k × 256` coefficient array both the standard's `w1Encode` (Alg. 28) and the deployed one consume. No
byte-level decision is taken here — those all live in `w1EncodeSpec` vs `w1Encode`. -/
def hbToArray (w1 : HBv) : Array Poly :=
  #[hbRow w1 ⟨0, by decide⟩, hbRow w1 ⟨1, by decide⟩, hbRow w1 ⟨2, by decide⟩,
    hbRow w1 ⟨3, by decide⟩, hbRow w1 ⟨4, by decide⟩, hbRow w1 ⟨5, by decide⟩]

/-- Every row of the coefficient view has the 256 coefficients Algorithm 28 expects. -/
theorem hbToArray_rowSize (w1 : HBv) (i : Nat) (hi : i < paramK) :
    ((hbToArray w1)[i]!).size = 256 := by
  have hi6 : i < 6 := hi
  interval_cases i <;> simp [hbToArray, hbRow]

/-- **The Fiat–Shamir hash — THE SPEC SIDE, WITH NO EXECUTABLE IN IT.** FIPS 204 Algorithm 8, line 5:
`c̃ ← H(μ ‖ w1Encode(w₁), λ/4)`, realized as `Fips204ChallengeHash.challengeHashSpec`:

* the encoder is `Fips204BitPack.w1EncodeSpec` — FIPS 204 Alg. 28 over Alg. 16/10/9;
* the hash is `Keccak.Fips202.SHAKE256` — the FIPS 202 §4/§5/§6.2 BIT-ADDRESSED sponge over the
  bit-function Keccak-f[1600] of `Fips202Spec`, NOT `Keccak.shake256`;
* the byte↔bit conversions are FIPS 202 §B.1.

Neither `MlDsaCodec.packBits` nor `Keccak.absorb`/`squeeze` occurs in this term. That is what makes
`hashFrame` a theorem instead of a projection. -/
def hashSpec (μ : List UInt8) (w1 : HBv) : List UInt8 := challengeHashSpec μ (hbToArray w1)

/-- **The challenge derivation** `SampleInBall(c̃)` as an `R_q` element. -/
noncomputable def challengeK (cbar : List UInt8) : Rq := toRq (sampleInBall cbar)

/-- **The response norm gate** `‖z‖∞ < γ₁−β = 524092` on the `R_q^l` coordinates. -/
noncomputable def zBoundBK (z : Mv) : Bool :=
  decide (∀ (i : Fin paramL) (jj : Fin 256),
    min (coordM z i jj) (q - coordM z i jj) < zBound)

/-! ## PART 4 — the concrete `MlDsaParams` and the HASH-FRAMING leg. -/

/-- **The concrete ML-DSA-65 `Fips204Spec.MlDsaParams` over `R_q^k`.** All five fields instantiated: the
`expandA`-as-LinearMap public matrix, the coordinate-wise `R_q^k` rounding, the FIPS 204 Alg. 8 line-5
Fiat–Shamir hash (`hashSpec` — standard encoder AND standard sponge), `SampleInBall` as the challenge,
and the `‖z‖∞` gate. Parameterized by the public seed `ρ` and the OPEN stability lemma `hbStable`. -/
noncomputable def mldsaParams (ρ : List UInt8) (hbStable : HighBitsStableK) :
    MlDsaParams Rq Mv Nv HBv HBv (List UInt8) (List UInt8) where
  A := (expandAMat ρ).mulVecLin
  round := roundK hbStable
  hash := hashSpec
  challenge := challengeK
  zBoundB := zBoundBK

/-- **THE HASH-FRAMING LEG — a real `∀`.** For every message `μ`, high-bits vector `w₁` and digest `c̃`,
the EXECUTABLE ML-DSA-65 challenge check `shake256(μ ‖ w1Encode w₁) 48 == c̃` (`verifyCore`'s inlined
SHAKE fixed-point, verbatim) equals the SPEC conjunct `decide (mldsaParams.hash μ w₁ = c̃)`.

WHY IT IS NON-VACUOUS, precisely: the two sides share NO computational content.
* LEFT encoder: `MlDsaCodec.packBits` — accumulate the little-endian mixed-radix bignum
  `Σᵢ (cᵢ mod 2⁴)·16^i`, then emit base-256 digits.
  RIGHT encoder: `Fips204BitPack.simpleBitPack` — bit `m` of Alg. 16's bit string is
  `⌊w[m/4] / 2^(m mod 4)⌋ mod 2`, then Alg. 10 `BitsToBytes`.
* LEFT hash: `Keccak.shake256` — `UInt64` lanes, `Array` state, byte-addressed pad/absorb/squeeze.
  RIGHT hash: `Fips202.SHAKE256` — a bit function `Fin 5 → Fin 5 → Fin 64 → Bool`, `pad10*1` on a
  `List Bool`, §4 Algorithm 8 absorb/squeeze over the §3.2 θ ρ π χ ι permutation.
Neither side `whnf`-reduces to the other. The proof consumes `Fips204BitPack.w1Encode_eq_spec` (encoder)
and the sponge obligation `hSponge` (hash), glued by the §B.1 round-trip. A wrong packing width,
endianness, row order, coefficient mask, sponge rate, pad rule or domain byte falsifies it. -/
theorem hashFrame (hSponge : SpongeRefinesObligation) (ρ : List UInt8) (hbStable : HighBitsStableK)
    (μ : List UInt8) (w1 : HBv) (ctilde : List UInt8) :
    (shake256 (μ ++ w1Encode (hbToArray w1)) 48 == ctilde)
      = decide ((mldsaParams ρ hbStable).hash μ w1 = ctilde) := by
  have hbridge : shake256 (μ ++ w1Encode (hbToArray w1)) 48 = challengeHashSpec μ (hbToArray w1) :=
    challengeHash_frames hSponge μ (hbToArray w1) (fun i hi => hbToArray_rowSize w1 i hi)
  have hproj : (mldsaParams ρ hbStable).hash μ w1 = challengeHashSpec μ (hbToArray w1) := rfl
  rw [hbridge, hproj]
  by_cases h : challengeHashSpec μ (hbToArray w1) = ctilde <;> simp [h]

/-- The framing as a genuine two-way gate on the Bool verdicts. -/
theorem hashFrame_iff (hSponge : SpongeRefinesObligation) (ρ : List UInt8)
    (hbStable : HighBitsStableK) (μ : List UInt8) (w1 : HBv) (ctilde : List UInt8) :
    (shake256 (μ ++ w1Encode (hbToArray w1)) 48 == ctilde) = true
      ↔ (mldsaParams ρ hbStable).hash μ w1 = ctilde := by
  rw [hashFrame hSponge, decide_eq_true_eq]

/-! ## PART 5 — composition against `Fips204Spec`, with the REMAINING obligation as a TYPED hypothesis. -/

/-- **`challengeMatches` IS the FIPS 204 hash conjunct — modulo the named argument leg.**
The RHS is the spec's own sentence, spelled with `Fips204Spec` projections only:

    decide ( P.hash μ (P.round.useHint h (P.A z − P.challenge c̃ • t₁·2^d)) = c̃ )

at `P = mldsaParams ρ hbStable`. The hypothesis `hArg` is the ARGUMENT leg and nothing else: that
`challengeMatches` (the deployed SHAKE fixed-point, verbatim from `verifyCore`) is that fixed-point AT
the abstract recovered high-bits vector — the `VerifyCoreEqSpec`/`VerifyCoreUseHint` line, closed
per-coefficient there but not yet assembled over the six rows. What this theorem CONTRIBUTES over `hArg`
is exactly the hash leg: replacing the deployed encoder by FIPS 204 Alg. 28 and the deployed sponge by
the FIPS 202 §6.2 sponge inside the digest. That step is `hashFrame`, and it is not `rfl`. -/
theorem challengeMatches_eq_specHash (hSponge : SpongeRefinesObligation)
    (ρ : List UInt8) (hbStable : HighBitsStableK)
    (pk M ctx sig : List UInt8) (μ : List UInt8) (thi : Nv) (z : Mv) (hint : HBv)
    (hArg : challengeMatches pk M ctx sig
      = (shake256 (μ ++ w1Encode (hbToArray
            ((mldsaParams ρ hbStable).round.useHint hint
              ((mldsaParams ρ hbStable).A z
                - (mldsaParams ρ hbStable).challenge (sigDecode sig).1 • thi)))) 48
          == (sigDecode sig).1)) :
    challengeMatches pk M ctx sig
      = decide ((mldsaParams ρ hbStable).hash μ
          ((mldsaParams ρ hbStable).round.useHint hint
            ((mldsaParams ρ hbStable).A z
              - (mldsaParams ρ hbStable).challenge (sigDecode sig).1 • thi))
          = (sigDecode sig).1) := by
  rw [hArg, hashFrame hSponge ρ hbStable μ _ (sigDecode sig).1]

/-- **The deployed verifier IS the FIPS 204 spec verifier — modulo two named legs.**
`MlDsaVerifyReal.verifyCore pk M ctx sig = Fips204Spec.MlDsaParams.verifyB …` at the concrete ML-DSA-65
instance. The RHS is `Fips204Spec`'s own `verifyB` (`zBoundB z && decide (hash μ (useHint h (A z − c•t₁·2^d)) = c̃)`),
not `challengeMatches` and not any re-expression of the implementation.

THE TWO HYPOTHESES ARE THE HONEST RESIDUE, and neither is the conclusion in disguise:
* `hArg` — the ARGUMENT leg (`VerifyCoreUseHint`'s frontier): the deployed `w₁` fed to the digest is the
  abstract `UseHint(h, A·z − c·t₁·2^d)`;
* `hnorm` — the NORM leg: the deployed `‖z‖∞ < γ₁−β` test on the decoded `z` agrees with the abstract
  `zBoundBK` on the `R_q^l` coordinates (the codec side of `VerifyCoreEqSpec`).
Everything BETWEEN them — the split of `verifyCore` into its two conjuncts, and the identification of
the deployed digest with FIPS 204 Alg. 8 line 5 over FIPS 202 §6.2 — is proved here. -/
theorem verifyCore_eq_specVerifyB (hSponge : SpongeRefinesObligation)
    (ρ : List UInt8) (hbStable : HighBitsStableK)
    (pk M ctx sig : List UInt8) (μ : List UInt8) (thi : Nv) (z : Mv) (hint : HBv)
    (hh : (sigDecode sig).2.2.size = paramK)
    (hnorm : decide (infNormZ (sigDecode sig).2.1 < zBound) = zBoundBK z)
    (hArg : challengeMatches pk M ctx sig
      = (shake256 (μ ++ w1Encode (hbToArray
            ((mldsaParams ρ hbStable).round.useHint hint
              ((mldsaParams ρ hbStable).A z
                - (mldsaParams ρ hbStable).challenge (sigDecode sig).1 • thi)))) 48
          == (sigDecode sig).1)) :
    verifyCore pk M ctx sig
      = (mldsaParams ρ hbStable).verifyB thi μ ((sigDecode sig).1, z, hint) := by
  rw [verifyCore_split pk M ctx sig hh,
    challengeMatches_eq_specHash hSponge ρ hbStable pk M ctx sig μ thi z hint hArg, hnorm]
  show _ = ((mldsaParams ρ hbStable).zBoundB z && _)
  exact Bool.and_comm _ _

/-! ### The same two statements with the sponge obligation DISCHARGED.

`Fips202SpongeRefine.sponge_refines` proves `SpongeRefinesObligation`, so these hold unconditionally in
the sponge. They inherit the Keccak floor's single compiled-evaluation residual (`rc_lanes_eq_exec`, the
24×64-bit round-constant table cross-check), which is why they are pinned by `#print axioms` below and
NOT by `#assert_axioms`. -/

/-- `hashFrame` with the sponge refinement discharged. -/
theorem hashFrame_deployed (ρ : List UInt8) (hbStable : HighBitsStableK)
    (μ : List UInt8) (w1 : HBv) (ctilde : List UInt8) :
    (shake256 (μ ++ w1Encode (hbToArray w1)) 48 == ctilde)
      = decide ((mldsaParams ρ hbStable).hash μ w1 = ctilde) :=
  hashFrame Dregg2.Crypto.Keccak.Fips202SpongeRefine.sponge_refines ρ hbStable μ w1 ctilde

/-- `verifyCore_eq_specVerifyB` with the sponge refinement discharged. -/
theorem verifyCore_eq_specVerifyB_deployed
    (ρ : List UInt8) (hbStable : HighBitsStableK)
    (pk M ctx sig : List UInt8) (μ : List UInt8) (thi : Nv) (z : Mv) (hint : HBv)
    (hh : (sigDecode sig).2.2.size = paramK)
    (hnorm : decide (infNormZ (sigDecode sig).2.1 < zBound) = zBoundBK z)
    (hArg : challengeMatches pk M ctx sig
      = (shake256 (μ ++ w1Encode (hbToArray
            ((mldsaParams ρ hbStable).round.useHint hint
              ((mldsaParams ρ hbStable).A z
                - (mldsaParams ρ hbStable).challenge (sigDecode sig).1 • thi)))) 48
          == (sigDecode sig).1)) :
    verifyCore pk M ctx sig
      = (mldsaParams ρ hbStable).verifyB thi μ ((sigDecode sig).1, z, hint) :=
  verifyCore_eq_specVerifyB Dregg2.Crypto.Keccak.Fips202SpongeRefine.sponge_refines
    ρ hbStable pk M ctx sig μ thi z hint hh hnorm hArg

/-! ## PART 6 — TEETH: the spec-side hash is a REAL 48-byte SHAKE digest, not a stub.

`hashSpec` is built entirely from the FIPS 202 bit sponge, so evaluating it directly is hopeless (a
bit-function Keccak-f). Its value is nevertheless PINNED, by transporting the deployed digest ACROSS
`challengeHash_frames_deployed`: on a concrete `w₁` (`w₁[i][j] = (i+j) mod 16`, all 1536 coefficients in
the Alg. 28 range) and a concrete framed message, the STANDARD-side `H(μ ‖ w1Encode(w₁), 48)` is these
48 bytes. A stub, an all-zero encoder, or a wrong rate could not produce them.

The right-hand side is obtained by COMPILED EVALUATION of the deployed side (`native_decide`), so this
witness carries that residual — like every KAT in the tree. It is a witness, not a `∀`, and is NOT
`#assert_axioms`-pinned. -/

/-- **The spec-side challenge hash, evaluated through the framing theorem.** `hashSpec` is the value of
`(mldsaParams ρ hbStable).hash` (definitionally), so this is FIPS 204 Alg. 8 line 5 producing real
SHAKE-256 bytes over the real Algorithm 28 encoding of a real 6×256 high-bits vector. -/
theorem hashSpec_witness :
    hashSpec [0x61, 0x62, 0x63] (fun i jj => (((i.val + jj.val) % 16 : Nat) : ℤ))
      = [192, 0, 203, 188, 58, 63, 184, 185, 209, 135, 134, 189, 6, 13, 141, 69,
         163, 87, 173, 143, 144, 246, 210, 92, 196, 65, 87, 152, 206, 137, 238, 28,
         17, 161, 20, 236, 214, 240, 148, 175, 82, 172, 170, 235, 8, 204, 246, 197] := by
  show Dregg2.Crypto.Fips204ChallengeHash.challengeHashSpec _ _ = _
  rw [← Dregg2.Crypto.Fips204ChallengeHash.challengeHash_frames_deployed
        [0x61, 0x62, 0x63] _ (fun i hi => hbToArray_rowSize _ i hi)]
  native_decide

#assert_axioms useHintK_makeHintK
#assert_axioms highBits_noWrap_stable
#assert_axioms hbToArray_rowSize
#assert_axioms hashFrame
#assert_axioms hashFrame_iff
#assert_axioms challengeMatches_eq_specHash
#assert_axioms verifyCore_eq_specVerifyB

-- Reported, NOT asserted: the `_deployed` corollaries inherit the Keccak floor's one
-- compiled-evaluation residual (`Fips202Refine.rc_lanes_eq_exec`, the round-constant table KAT).
#print axioms hashFrame_deployed
#print axioms verifyCore_eq_specVerifyB_deployed

end Dregg2.Crypto.VerifyCoreHashFrame
