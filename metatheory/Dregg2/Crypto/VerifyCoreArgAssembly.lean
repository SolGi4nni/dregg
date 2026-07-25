/-
# `Dregg2.Crypto.VerifyCoreArgAssembly` — the ARGUMENT LEG, ASSEMBLED OVER THE `k = 6` ROWS.

`VerifyCoreHashFrame.verifyCore_eq_specVerifyB` identified the deployed ML-DSA-65 verifier with
`Fips204Spec.MlDsaParams.verifyB` MODULO TWO TYPED HYPOTHESES: `hArg` (the argument leg) and `hnorm`
(the norm leg). `VerifyCoreUseHint.w1Row_recovers_arg` closed the argument leg PER COEFFICIENT — but
per-coefficient is not the shape the hash frame consumes; the frame consumes an `hbToArray`-shaped
`Array Poly` of `k = 6` rows. THIS MODULE performs that assembly and DISCHARGES `hArg`.

## What is PROVEN (real `∀`-theorems, `#assert_axioms`-clean, no `sorry`, no new `axiom`)

* **`VerifyCoreArgRows.challengeMatches_rows` — THE ROW FOLD** (previous module). The deployed SHAKE
  fixed-point with verifyCore's four nested `do`-loops resolved: the `k`-row `Array.push` accumulator
  is replaced by any array whose `k` entries are `rowBody`, and `rowBody_eq_execRow` identifies that
  body with `w1Row h_i (wRowHat …)` — the shapes `VerifyCoreUseHint` / `VerifyCoreEqSpecW` reason about.
* **`rqMatvec_row` — THE ROW ALGEBRA.** The abstract `R_q` matvec of row `i`'s term list IS the `i`-th
  component of `A·z − c·t₁·2^d`, with `A = expandAMat ρ` applied through `Matrix.mulVecLin`. This is
  what turns a list-shaped executable accumulator into an application of the spec's `M →ₗ[R_q] N`.
* **`execRow_eq_hbRow` — THE PER-ROW ASSEMBLY.** verifyCore's row-`i` `w1'` polynomial IS the
  coefficient view (`hbRow`) of the abstract `UseHint(hint, A·z − c·t₁·2^d)` at row `i`. Composes
  `w1Row_getElem` (the loop spec), `wOne_recovers_hat` (the coordinate identity, hence
  `toRq_intt_matmul_row` and `expandA_is_matrix`), and `rqMatvec_row`.
* **`hArg_discharged`** — the six rows lifted through `w1Encode`. This IS `hArg`. No `packBits`
  reasoning enters: BOTH sides call the SAME `w1Encode`, so the rows are lifted by the `w1Encode`
  congruence. (The FIPS 204 Alg. 28 ENCODER refinement is a different leg entirely and already lives
  in `Fips204BitPack.w1Encode_eq_spec`, consumed by `Fips204ChallengeHash.challengeHash_frames`.)
* **`verifyCore_eq_specVerifyB_noArg`** — `verifyCore pk M ctx sig = (mldsaParams (pkDecode pk).1
  hbStable).verifyB (thiv pk) (muOf pk M ctx) ((sigDecode sig).1, zv sig, hintOf pk sig)`, WITHOUT
  `hArg` and WITHOUT `hSponge`. TWO fewer hypotheses than
  `VerifyCoreHashFrame.verifyCore_eq_specVerifyB`: the FIPS 202 sponge obligation is no longer
  threaded through the statement at all — it is APPLIED inside the proof, from
  `Fips202SpongeRefine.sponge_refines`, which proves `Fips202Refine.SpongeRefinesObligation`
  literally (`#print axioms` = the three kernel axioms, so nothing is inherited by taking it).

## ★ WHAT IS NOT CLAIMED — read before believing anything

**The abstract hint is a DIFFERENCE hint, and it is not a pure byte-decode.** `roundK.useHint h r =
HighBits r + h` is an ADDITIVE hint scheme (that additive shape is what lets `useHintK_makeHintK`
telescope unconditionally). So the abstract hint a signature carries is the CORRECTION the transmitted
`{0,1}` bit applies, which depends on the recovered argument as well as on the bytes: `hintOf` is
defined as `UseHint(h_i[jj], coord) − HighBits(coord)` and reads `argOf`. It is NOT recovered from `sig`
alone. What pins it down instead of leaving it free:
* `useHintK_hintOf` — the value the spec hashes is exactly FIPS 204 Algorithm 40 `UseHint` of the
  TRANSMITTED bit at the abstract coordinate. Nothing else is inserted.
* `hintOf_eq_zero_of_no_hint` — wherever the signature carries no hint bit, the abstract hint is `0`.
A signature-only hint decode would need `roundK` restated with a `{0,1}`-valued `Hint` type and Alg. 40
as its `useHint` field; that is a `Fips204Spec`-side redesign and it is NOT done. Named, not laundered.

**The remaining hypotheses.** `hh` (the hint decodes to `k` rows) is inherited from upstream. `hA`,
`hz`, `hc` are OPERATIONAL DECODE GUARDS: every `expandA ρ` entry in the row range is a
256-coefficient poly with coefficients `< q` (`MlDsaExpandA.expandA_shape` /
`rejNTTPoly_coeffs_in_range` prove exactly this by `native_decide` for the pinned test seed only — the
`∀ ρ` version is the sampler's shape obligation); the decoded response polynomials have 256
coefficients; `sampleInBall` returns 256 coefficients. `scaleT1` needs no guard — `scaleT1_size` is
PROVED. `sampleInBall`'s loop carries a `break`, so the `setIdxFold` argument does not apply to it and
it stays a named guard.

**NO LONGER OPEN.** `SpongeRefinesObligation` (the FIPS 202 pad10*1/absorb/squeeze refinement) used
to be threaded as a hypothesis and discharged only in the `_deployed` corollary. It is now applied
directly in `verifyCore_eq_specVerifyB_noArg`, because `Fips202SpongeRefine.sponge_refines` is a
proof of that exact `Prop` — same statement, no side conditions, kernel-clean — resting on
`Fips202Round.keccakF_refines_spec` and the sec. 4 sponge spec in `Keccak.Fips202Sponge`.

**STILL OPEN, untouched by this module:**
* **`hnorm`** — the deployed `‖z‖∞ < γ₁−β` test on the decoded byte-level `z` agrees with `zBoundBK` on
  the `R_q^l` coordinates. A codec statement; NOT discharged here.
* **`HighBitsStableK`** — Dilithium high-bits stability over `R_q` (the `mod q` wrap and `Decompose`'s
  `r − r₀ = q−1` boundary). Threaded as `hbStable`, so the gap sits in the type.
* collision resistance of SHAKE256 — the `HashSig`/`FoQrom` floor, a different axis entirely.
-/
import Dregg2.Crypto.VerifyCoreArgRows

namespace Dregg2.Crypto.VerifyCoreArgAssembly

open Dregg2.Crypto.MlDsaRing (Poly q zeroPoly ntt intt)
open Dregg2.Crypto.MlDsaVerifyReal (w1Encode useHint highBits scaleT1 infNormZ zBound verifyCore)
open Dregg2.Crypto.MlDsaCodec (paramK paramL pkDecode sigDecode)
open Dregg2.Crypto.MlDsaExpandA (expandA)
open Dregg2.Crypto.MlDsaSampleInBall (sampleInBall)
open Dregg2.Crypto.Keccak (shake256)
open Dregg2.Crypto.VerifyCoreSpec (challengeMatches)
open Dregg2.Crypto.VerifyCoreEqSpec
  (Rq toRq pbW pbW_dim w1Row w1Row_size w1Row_getElem wRowHat rqMatvec wOne_recovers_hat)
open Dregg2.Crypto.VerifyCoreHashFrame
  (Mv Nv HBv coordN hbK useHintK hbRow hbToArray expandAMat challengeK zBoundBK
   HighBitsStableK mldsaParams verifyCore_eq_specVerifyB)
open Dregg2.Crypto.VerifyCoreArgRows
  (arrExt ofFn_get! scaleT1_size muOf rowBody rowTerms execRow rowBody_eq_execRow
   challengeMatches_rows)

set_option maxRecDepth 20000

/-! ## PART 1 — the decoded objects, as elements of the abstract modules. -/

/-- The decoded response as an element of the abstract module `M = R_q^l`. -/
noncomputable def zv (sig : List UInt8) : Mv := fun j => toRq ((sigDecode sig).2.1[(j : ℕ)]!)

/-- The decoded high key `t₁·2^d` as an element of `N = R_q^k`. -/
noncomputable def thiv (pk : List UInt8) : Nv := fun i => toRq (scaleT1 ((pkDecode pk).2[(i : ℕ)]!))

/-- **The abstract recovery argument** `A·z − c·t₁·2^d ∈ R_q^k`, spelled with the spec's operations. -/
noncomputable def argOf (pk sig : List UInt8) : Nv :=
  (expandAMat (pkDecode pk).1).mulVecLin (zv sig) - challengeK (sigDecode sig).1 • thiv pk

/-- **The abstract (difference-form) hint** the `R_q^k` rounding scheme consumes: the FIPS 204 Alg. 40
correction the transmitted `{0,1}` hint bit applies at the recovered argument's coordinate. See the
header's "WHAT IS NOT CLAIMED" — this reads `argOf`, so it is not a decode of `sig` alone. -/
noncomputable def hintOf (pk sig : List UInt8) : HBv := fun i jj =>
  useHint (((sigDecode sig).2.2[(i : ℕ)]!)[(jj : ℕ)]!) (coordN (argOf pk sig) i jj)
    - highBits (coordN (argOf pk sig) i jj)

/-! ## PART 2 — the row ARGUMENT: the deployed row matvec IS the abstract `(A·z − c·t₁·2^d)_i`. -/

/-- **THE ROW ALGEBRA.** The abstract `R_q` matvec of row `i`'s term list is exactly the `i`-th
component of `A·z − c·t₁·2^d`, with `A = expandAMat ρ` read as an `R_q`-linear map. -/
theorem rqMatvec_row (pk sig : List UInt8) (i : Fin paramK) :
    rqMatvec ((rowTerms (expandA (pkDecode pk).1) (sigDecode sig).2.1 (i : ℕ)).map
        (fun t => (intt t.1, t.2)))
      (sampleInBall (sigDecode sig).1) (scaleT1 ((pkDecode pk).2[(i : ℕ)]!))
      = argOf pk sig i := by
  unfold argOf
  rw [Pi.sub_apply, Matrix.mulVecLin_apply]
  show _ = (fun j => expandAMat (pkDecode pk).1 i j) ⬝ᵥ (zv sig)
      - (challengeK (sigDecode sig).1 • thiv pk) i
  rw [dotProduct, Fin.sum_univ_def]
  unfold rqMatvec rowTerms zv thiv expandAMat challengeK
  simp [List.finRange, Pi.smul_apply, smul_eq_mul, paramL]

/-! ## PART 3 — the per-row assembly. -/

/-- Row `i`'s term list meets `wOne_recovers_hat`'s stored-`Â` guards. -/
theorem rowTerms_hAhat (aHat zp : Array Poly) (i : Fin paramK)
    (hA : ∀ n, n < paramK * paramL →
      (aHat[n]!).size = 256 ∧ ∀ (p : Nat), (aHat[n]!)[p]! < q) :
    ∀ t ∈ rowTerms aHat zp (i : ℕ), t.1.size = 256 ∧ (∀ (p : Nat), t.1[p]! < q) := by
  have hi : (i : ℕ) < 6 := i.isLt
  intro t ht
  simp only [rowTerms, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with h | h | h | h | h <;> subst h <;>
    exact hA _ (by simp only [paramK, paramL]; omega)

/-- Row `i`'s term list meets `wOne_recovers_hat`'s response-size guard. -/
theorem rowTerms_hz (aHat zp : Array Poly) (i : Nat)
    (hz : ∀ j, j < paramL → (zp[j]!).size = 256) :
    ∀ t ∈ rowTerms aHat zp i, t.2.size = 256 := by
  intro t ht
  simp only [rowTerms, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with h | h | h | h | h <;> subst h <;> exact hz _ (by decide)

/-- **THE PER-ROW ASSEMBLY.** verifyCore's row-`i` `w1'` polynomial IS the coefficient view of the
abstract `UseHint(hint, A·z − c·t₁·2^d)` at row `i`. -/
theorem execRow_eq_hbRow (pk sig : List UInt8) (i : Fin paramK)
    (hA : ∀ n, n < paramK * paramL →
      ((expandA (pkDecode pk).1)[n]!).size = 256
        ∧ ∀ (p : Nat), ((expandA (pkDecode pk).1)[n]!)[p]! < q)
    (hz : ∀ j, j < paramL → ((sigDecode sig).2.1[j]!).size = 256)
    (hc : (sampleInBall (sigDecode sig).1).size = 256) :
    execRow pk sig (i : ℕ) = hbRow (useHintK (hintOf pk sig) (argOf pk sig)) i := by
  have hAh := rowTerms_hAhat (expandA (pkDecode pk).1) (sigDecode sig).2.1 i hA
  have hzz := rowTerms_hz (expandA (pkDecode pk).1) (sigDecode sig).2.1 (i : ℕ) hz
  have hs := scaleT1_size ((pkDecode pk).2[(i : ℕ)]!)
  refine arrExt _ _ ?_ ?_
  · rw [show execRow pk sig (i : ℕ) = w1Row _ _ from rfl, w1Row_size]
    simp [hbRow]
  · intro jj hjj
    rw [show execRow pk sig (i : ℕ) = w1Row _ _ from rfl, w1Row_size] at hjj
    have hrec := wOne_recovers_hat
      (rowTerms (expandA (pkDecode pk).1) (sigDecode sig).2.1 (i : ℕ))
      (sampleInBall (sigDecode sig).1) (scaleT1 ((pkDecode pk).2[(i : ℕ)]!))
      hAh hzz hc hs (Fin.cast pbW_dim.symm ⟨jj, hjj⟩)
    rw [Fin.coe_cast] at hrec
    rw [rqMatvec_row pk sig i] at hrec
    show (w1Row _ _)[jj]! = _
    rw [w1Row_getElem _ _ jj hjj, hrec, hbRow, ofFn_get! _ jj hjj]
    show _ = ((hbK (argOf pk sig) + hintOf pk sig) i ⟨jj, hjj⟩).toNat
    simp only [Pi.add_apply, hintOf, hbK, coordN]
    ring_nf

/-- Row lookup in the `k`-row coefficient view. -/
theorem hbToArray_get (W : HBv) (i : Nat) (hi : i < paramK) :
    (hbToArray W)[i]! = hbRow W ⟨i, hi⟩ := by
  simp only [paramK] at hi
  interval_cases i <;> rfl

/-! ## PART 4 — `hArg`, DISCHARGED. -/

/-- **THE ARGUMENT LEG, ASSEMBLED OVER THE `k = 6` ROWS.** This is exactly the `hArg` hypothesis of
`VerifyCoreHashFrame.challengeMatches_eq_specHash` / `verifyCore_eq_specVerifyB`, at the decoded
instantiation. -/
theorem hArg_discharged (pk M ctx sig : List UInt8) (hbStable : HighBitsStableK)
    (hh : (sigDecode sig).2.2.size = paramK)
    (hA : ∀ n, n < paramK * paramL →
      ((expandA (pkDecode pk).1)[n]!).size = 256
        ∧ ∀ (p : Nat), ((expandA (pkDecode pk).1)[n]!)[p]! < q)
    (hz : ∀ j, j < paramL → ((sigDecode sig).2.1[j]!).size = 256)
    (hc : (sampleInBall (sigDecode sig).1).size = 256) :
    challengeMatches pk M ctx sig
      = (shake256 (muOf pk M ctx ++ w1Encode (hbToArray
            ((mldsaParams (pkDecode pk).1 hbStable).round.useHint (hintOf pk sig)
              ((mldsaParams (pkDecode pk).1 hbStable).A (zv sig)
                - (mldsaParams (pkDecode pk).1 hbStable).challenge (sigDecode sig).1
                  • thiv pk)))) 48
          == (sigDecode sig).1) := by
  have hrows : ∀ i, i < paramK →
      rowBody pk sig i = (hbToArray (useHintK (hintOf pk sig) (argOf pk sig)))[i]! := by
    intro i hi
    rw [rowBody_eq_execRow, hbToArray_get _ i hi]
    exact execRow_eq_hbRow pk sig ⟨i, hi⟩ hA hz hc
  have hproj : (mldsaParams (pkDecode pk).1 hbStable).round.useHint (hintOf pk sig)
      ((mldsaParams (pkDecode pk).1 hbStable).A (zv sig)
        - (mldsaParams (pkDecode pk).1 hbStable).challenge (sigDecode sig).1 • thiv pk)
      = useHintK (hintOf pk sig) (argOf pk sig) := rfl
  rw [challengeMatches_rows pk M ctx sig _ hh hrows, hproj]

/-- **THE DEPLOYED VERIFIER IS THE FIPS 204 SPEC VERIFIER — `hArg` GONE, `hSponge` GONE.**
The FIPS 202 sponge obligation is no longer a hypothesis: `Fips202SpongeRefine.sponge_refines`
proves `Fips202Refine.SpongeRefinesObligation` as stated, so it is supplied here. -/
theorem verifyCore_eq_specVerifyB_noArg
    (hbStable : HighBitsStableK) (pk M ctx sig : List UInt8)
    (hh : (sigDecode sig).2.2.size = paramK)
    (hA : ∀ n, n < paramK * paramL →
      ((expandA (pkDecode pk).1)[n]!).size = 256
        ∧ ∀ (p : Nat), ((expandA (pkDecode pk).1)[n]!)[p]! < q)
    (hz : ∀ j, j < paramL → ((sigDecode sig).2.1[j]!).size = 256)
    (hc : (sampleInBall (sigDecode sig).1).size = 256)
    (hnorm : decide (infNormZ (sigDecode sig).2.1 < zBound) = zBoundBK (zv sig)) :
    verifyCore pk M ctx sig
      = (mldsaParams (pkDecode pk).1 hbStable).verifyB (thiv pk) (muOf pk M ctx)
          ((sigDecode sig).1, zv sig, hintOf pk sig) :=
  verifyCore_eq_specVerifyB Dregg2.Crypto.Keccak.Fips202SpongeRefine.sponge_refines
    (pkDecode pk).1 hbStable pk M ctx sig (muOf pk M ctx)
    (thiv pk) (zv sig) (hintOf pk sig) hh hnorm
    (hArg_discharged pk M ctx sig hbStable hh hA hz hc)

/-- Retained NAME ONLY. The `_deployed` corollary existed to apply
`Fips202SpongeRefine.sponge_refines` to `verifyCore_eq_specVerifyB_noArg`'s `hSponge`; that
hypothesis is now gone from the main theorem, so this is literally the same statement, kept so the
name does not vanish from under any reader. Prefer `verifyCore_eq_specVerifyB_noArg`. -/
theorem verifyCore_eq_specVerifyB_noArg_deployed
    (hbStable : HighBitsStableK) (pk M ctx sig : List UInt8)
    (hh : (sigDecode sig).2.2.size = paramK)
    (hA : ∀ n, n < paramK * paramL →
      ((expandA (pkDecode pk).1)[n]!).size = 256
        ∧ ∀ (p : Nat), ((expandA (pkDecode pk).1)[n]!)[p]! < q)
    (hz : ∀ j, j < paramL → ((sigDecode sig).2.1[j]!).size = 256)
    (hc : (sampleInBall (sigDecode sig).1).size = 256)
    (hnorm : decide (infNormZ (sigDecode sig).2.1 < zBound) = zBoundBK (zv sig)) :
    verifyCore pk M ctx sig
      = (mldsaParams (pkDecode pk).1 hbStable).verifyB (thiv pk) (muOf pk M ctx)
          ((sigDecode sig).1, zv sig, hintOf pk sig) :=
  verifyCore_eq_specVerifyB_noArg hbStable pk M ctx sig hh hA hz hc hnorm

/-! ## PART 5 — TEETH: the abstract hint is FIPS 204 Alg. 40, not free choice. -/

/-- **The abstract hint is PINNED to FIPS 204 Algorithm 40.** The recovered high-bits vector the spec
hashes is `UseHint(h_i[jj], ·)` — the standard's own per-coefficient rounding — applied to the `jj`-th
power-basis coordinate of the abstract argument `A·z − c·t₁·2^d`. The additive form is bookkeeping for
`roundK`'s difference-hint convention; the VALUE is Algorithm 40's. -/
theorem useHintK_hintOf (pk sig : List UInt8) (i : Fin paramK) (jj : Fin 256) :
    useHintK (hintOf pk sig) (argOf pk sig) i jj
      = useHint (((sigDecode sig).2.2[(i : ℕ)]!)[(jj : ℕ)]!) (coordN (argOf pk sig) i jj) := by
  show (hbK (argOf pk sig) + hintOf pk sig) i jj = _
  simp only [Pi.add_apply, hbK, hintOf]
  ring

/-- **No transmitted hint bit ⇒ no correction.** If the signature's hint coefficient is not `1`, the
abstract hint at that coordinate is exactly `0` — so `hintOf` is not "whatever makes the equation
hold"; it is `0` wherever the signature carries no hint. -/
theorem hintOf_eq_zero_of_no_hint (pk sig : List UInt8) (i : Fin paramK) (jj : Fin 256)
    (hb : ((sigDecode sig).2.2[(i : ℕ)]!)[(jj : ℕ)]! ≠ 1) :
    hintOf pk sig i jj = 0 := by
  have hbf : ((((sigDecode sig).2.2[(i : ℕ)]!)[(jj : ℕ)]!) == 1) = false := by simpa using hb
  simp [hintOf, useHint, highBits, hbf]

#assert_axioms rqMatvec_row
#assert_axioms rowTerms_hAhat
#assert_axioms rowTerms_hz
#assert_axioms execRow_eq_hbRow
#assert_axioms hbToArray_get
#assert_axioms hArg_discharged
#assert_axioms verifyCore_eq_specVerifyB_noArg
#assert_axioms useHintK_hintOf
#assert_axioms hintOf_eq_zero_of_no_hint

-- Now ASSERTED, not merely reported: `verifyCore_eq_specVerifyB_noArg` APPLIES the Keccak sponge
-- refinement rather than assuming it, and the Keccak floor it thereby inherits is kernel-clean
-- (the last `native_decide` there died with `Fips202Lfsr`).
#assert_axioms verifyCore_eq_specVerifyB_noArg_deployed

#print axioms verifyCore_eq_specVerifyB_noArg
#print axioms verifyCore_eq_specVerifyB_noArg_deployed

end Dregg2.Crypto.VerifyCoreArgAssembly
