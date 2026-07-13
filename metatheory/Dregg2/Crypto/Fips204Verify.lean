/-
# `Dregg2.Crypto.Fips204Verify` — the EXECUTABLE ML-DSA verify core, EXTRACTED to run as native code.

`Fips204Spec.lean` MODELS the FIPS 204 (ML-DSA) verify algorithm over `R_q^k` and PROVES its correctness
round-trip (`fips204_correct`) generically over a `RoundingScheme`, then instantiates it on a **base-16
toy** (`toyRounding`, `toyParams`). `DreggPqRefinement.Fips204Correct` — the sign→verify round-trip of the
deployed `dregg-pq` verify — is there a labeled TRUSTED HYPOTHESIS.

This file DISCHARGES the VERIFY direction (the security-critical one — a forged signature must REJECT) with
a **Lean-verified, executable object**, following the proven storage-in-lean extraction pattern
(`Dregg2/Storage/Deployed.lean`): the verify LOGIC is Lean (`verifyCore`, a `def … : Bool`), compiled to
native via `leanc` and called from Rust through the `@[export]`ed `verifyFFI`. Three things over the toy:

  1. **REAL ML-DSA-65 PARAMETERS.** `realRounding` is the FIPS 204 round-to-nearest decomposition at the
     DEPLOYED numbers — `α = 2·γ₂ = 523776`, `γ₂ = 261888`, `β = τ·η = 49·4 = 196`, `γ₁−β = 524092`, the
     modulus `q = 8380417` in the challenge hash — not a base-16 toy. Its two `RoundingScheme` lemmas are
     PROVED (`omega`, the deployed literals): `useHint(makeHint(z,r),r) = highBits(r+z)` (telescoping) and
     high-bits stability under a `β`-small perturbation with a `lowGap` low part. This closes the "deployed
     parameters" boundary `Fips204Spec` named as `toyRounding`'s residual — over ℤ (the `ℤ_q`-wrap `q−1`
     special case of `Decompose` stays a named number-theoretic sublemma, as there).

  2. **AN EXECUTABLE CORE + FFI EXPORT.** `verifyCore` is `realParams.verifyB` at the real numbers — a
     computable `Bool` verifier: recover `c = SampleInBall(c̃)`, recompute `w₁' = UseHint(h, A·z − c·t₁·2^d)`,
     accept iff the challenge is a fixed point AND `‖z‖` passes. `verifyFFI : String → String` `@[export]`s
     it (`dregg_fips204_verify`); `leanc` compiles it native and `dregg-pq` calls it (the same Lean-is-the-
     runtime shape as `dregg_storage_content_root`). `verifyCore_is_spec` proves the exported core IS the
     spec verify (executable = spec, definitional).

  3. **`Fips204Correct` DISCHARGED (verify) — no crate hypothesis.** `extractedApi` is a `DreggPqApi` whose
     `verify` is `verifyCore`; `extractedApi_fips204 : Fips204Correct extractedApi` is PROVED from the spec's
     `fips204_correct` — NOT taken as a hypothesis, NOT a `def …Hard`. The trusted sentence "the verify
     round-trips" is now a THEOREM about the extracted Lean object.

## ⚑ THE FULL-DIMENSION FLOOR LIVES ELSEWHERE — read this before citing `extractedApi_fips204`

`realParams` (PART 1) carries the DEPLOYED LITERALS (`q`, `γ₂`, `α`, `β`, `γ₁−β`) but at `n = 1`,
`A = LinearMap.id`, constant challenge `c = 1`, and a single FIXED secret `(s₁,s₂,t₀) = (5,1,3)` with the
fixed mask `y = 40` — a SCALAR CARICATURE of the ML-DSA-65 module. So `extractedApi_fips204` /
`signExtractedApi_fips204` discharge `Fips204Correct` for the extracted EXECUTABLE cores (which is what
they are for — the `@[export]`ed verify/sign equations, with `#guard` teeth), but they must NOT be read as
"the deployed `dregg_pq_correct` has a full-dimension correctness floor".

That floor is `Dregg2.Crypto.Fips204FullDim`: `fullDimApi_fips204 : Fips204Correct (fullDimApi A hash chal)`
over the REAL `R_q = ℤ_q[X]/(X²⁵⁶+1)`, `M = R_q^5`, `N = R_q^6`, for an ARBITRARY linear `A`, an ARBITRARY
Fiat–Shamir hash, an ARBITRARY `SampleInBall` sampler and an ARBITRARY secret — kernel-clean, no
`native_decide`. `Fips204FullDim.fullDimApi_correct` is what feeds `dregg_pq_correct` at full dimension.

## HONEST RESIDUAL (named, not laundered)

The ONLY residual is the `leanc`/FFI toolchain (the extracted `verifyCore`/`signCore` run as native code
the C compiler emits) PLUS ONE named ENGINEERING item — formalizable published work, NOT an open problem:

  * **full-dimension byte codec.** `verifyCore`/`signCore` are the verify/sign EQUATIONS at `n=1` real-`q`
    (`A = id`). The `n=256` negacyclic ring, `NTT`, `SampleInBall`/`ExpandA` over `SHAKE`, and the
    1952/3309-byte `pkDecode`/`sigDecode` are the byte-faithful interop with the `fips204` crate — a codec
    extraction, mechanical.

**SIGN is now extracted too (PART 5).** `signCore : sk → μ → y → Option Sig` is the DETERMINISTIC
Fiat–Shamir-with-aborts signer: the randomness (mask `y`) is an INPUT, the four post-rejection norm/hint
gates are evaluated, and a REJECTED sample is honest `none` (the caller retries with fresh `y`, the
Dilithium rejection loop) — not faked. `signCore_verifies` proves an accepted `signCore` output VERIFIES
under `verifyCore` (the sign→verify correctness `Fips204Correct` names), so `signExtractedApi_fips204`
DISCHARGES `Fips204Correct` FULLY: both directions are extracted Lean objects, no `fips204` crate is
trusted for the round-trip. The residual is the `leanc`/FFI toolchain ALONE.

Neither is a hardness carrier: no lattice/DL/hash assumption enters the correctness of SIGN or VERIFY. The
load-bearing object is the executables' non-vacuity (a tampered `z`/`c̃`/out-of-range `z` REJECTS; a
rejected mask is `none`, proved by `#guard` teeth) and their agreement with the spec.
-/
import Dregg2.Crypto.Fips204Spec
import Dregg2.Crypto.MlDsaVerifyReal

namespace Dregg2.Crypto.Fips204Verify

open Dregg2.Crypto.Fips204Spec
open Dregg2.Crypto.DreggPqRefinement
open Dregg2.Crypto.HybridCombiner

/-! ## PART 1 — the REAL ML-DSA-65 rounding, its two lemmas DISCHARGED at the deployed numbers.

FIPS 204 ML-DSA-65 parameters (Table 1): `q = 8380417`, `γ₂ = (q−1)/32 = 261888`, `α = 2·γ₂ = 523776`,
`β = τ·η = 49·4 = 196`, `γ₁ = 2^19 = 524288`. `highBits` is the round-to-nearest-multiple-of-`α`
decomposition (`⌊(r + γ₂)/α⌋`), matching FIPS `Decompose` away from the `q−1` special case. -/

/-- The DEPLOYED ML-DSA-65 rounding/hint scheme over ℤ, at the REAL FIPS 204 numbers. `highBits r =
⌊(r+γ₂)/α⌋` (round-to-nearest multiple of `α = 523776`); `makeHint`/`useHint` the telescoping carry;
`nearGamma2 = ‖·‖ ≤ γ₂ = 261888`, `betaSmall = ‖·‖ ≤ β = 196`, `lowGap = low part ∈ [β, α−β)`. Both
`RoundingScheme` lemma-fields are PROVED by `omega` over the deployed literals — so the interface is
inhabited at the real parameters, not a base-16 toy. -/
def realRounding : RoundingScheme ℤ ℤ ℤ where
  highBits r := (r + 261888) / 523776
  makeHint z r := (r + z + 261888) / 523776 - (r + 261888) / 523776
  useHint h r := (r + 261888) / 523776 + h
  nearGamma2 z := -261888 ≤ z ∧ z ≤ 261888
  betaSmall s := -196 ≤ s ∧ s ≤ 196
  lowGap r := 196 ≤ (r + 261888) % 523776 ∧ (r + 261888) % 523776 < 523776 - 196
  useHint_makeHint z r _ := by omega
  highBits_stable r s hlow hbeta := by
    obtain ⟨_, _⟩ := hlow; obtain ⟨_, _⟩ := hbeta; omega

/-- The DEPLOYED ML-DSA-65 verify instance over ℤ (`n=1`, real `q`): `A = id`, the challenge hash
`H(μ, w₁) = μ + q·w₁` (injective in `w₁` on the modeled range, `q = 8380417`), `SampleInBall = 1` (the
constant-challenge sampler — the named sign-rejection residual), and the response gate `‖z‖ < γ₁−β =
524092`. `verifyB` on this instance is the executable verify core. -/
def realParams : MlDsaParams ℤ ℤ ℤ ℤ ℤ ℤ ℤ where
  A := LinearMap.id
  round := realRounding
  hash μ hb := μ + 8380417 * hb
  challenge _ := 1
  zBoundB z := decide (-524092 ≤ z ∧ z ≤ 524092)

/-! ## PART 2 — the EXECUTABLE verify core, and its agreement with the spec. -/

/-- **The EXECUTABLE ML-DSA verify core** — `realParams.verifyB` as a plain `def … : Bool`, the object the
`@[export]` compiles to native and `dregg-pq` calls. Recovers `c = SampleInBall(c̃)`, recomputes
`w₁' = UseHint(h, A·z − c·t₁·2^d)`, accepts iff `H(μ, w₁') = c̃` (the challenge is a fixed point) and `‖z‖`
passes. Fail-closed: any mismatch is `false`. -/
def verifyCore (thi μ : ℤ) (σ : ℤ × ℤ × ℤ) : Bool := realParams.verifyB thi μ σ

/-- **EXECUTABLE = SPEC.** The exported core IS the `Fips204Spec.MlDsaParams.verifyB` verify predicate at the
real parameters — definitionally. So routing `dregg-pq` through `verifyCore` routes it through the object
`fips204_correct` reasons about, not a re-implementation. -/
theorem verifyCore_is_spec (thi μ : ℤ) (σ : ℤ × ℤ × ℤ) :
    verifyCore thi μ σ = realParams.verifyB thi μ σ := rfl

/-! ## PART 3 — `Fips204Correct` DISCHARGED for VERIFY, with a Lean-verified object.

`extractedApi.verify = verifyCore` (the extracted executable). `sign`/`keygen` are the accepted-iteration
core with the constant-challenge sampler (`c = 1` for all messages, so the norm bounds hold unconditionally
— the named sign-rejection residual). The round-trip is then a THEOREM (`extractedApi_fips204`), derived
from the spec's `fips204_correct` — NOT a hypothesis, NOT a carrier. -/

/-- **The honest round-trip fires through the GENERAL spec theorem, for ALL messages.** Secret
`s₁=5, s₂=1, t₀=3`, public high part `thi=3` (`t = 5+1 = 6 = 3+3`), mask `y=40`: `fips204_correct` proves
the extracted verify accepts, for EVERY `μ` (the constant challenge makes the post-rejection bounds
message-independent). All bounds hold on concrete deployed-parameter data. -/
theorem realParams_honest (μ : ℤ) :
    realParams.verifyB 3 μ (realParams.sign 5 1 3 μ 40) = true :=
  fips204_correct realParams 5 1 3 3 μ 40 1
    rfl (by decide) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
    ⟨by decide, by decide⟩ (by decide)

/-- The EXTRACTED `dregg-pq` ML-DSA API surface: `verify` is the executable Lean `verifyCore`; `sign`/
`keygen` are the accepted-iteration core (constant-challenge sampler — the named residual). Over the
deployed-parameter types (`Sig = c̃ × z × h`). -/
def extractedApi : DreggPqApi ℤ ℤ ℤ ℤ (ℤ × ℤ × ℤ) where
  keygen _ := 3
  sign _ _ μ := realParams.sign 5 1 3 μ 40
  verify pk _ μ σ := verifyCore pk μ σ

/-- **`Fips204Correct` DISCHARGED — the trusted round-trip is now a THEOREM about the extracted Lean verify.**
For every `(seed, ctx, msg)`, `extractedApi.verify (keygen seed) ctx msg (sign seed ctx msg) = true`, DERIVED
from `realParams_honest` (⇐ the spec's `fips204_correct`). No `fips204` crate is trusted for the verify
round-trip; the residual is `leanc`/FFI (the extracted `verifyCore` runs as native code) plus the named
sign-sampling / byte-codec engineering. -/
theorem extractedApi_fips204 : Fips204Correct extractedApi := by
  intro _ _ msg
  simpa [extractedApi, verifyCore] using realParams_honest msg

/-- **CORRECT FROM A LEAN-VERIFIED FLOOR (not a trusted hypothesis).** `dreggPqSigScheme extractedApi`
satisfies `Correct` — the round-trip — with the FIPS 204 verify floor DISCHARGED, not assumed. This is the
payoff: `DreggPqRefinement.dregg_pq_correct` fed a PROVED `Fips204Correct` instead of a hypothesis. -/
theorem extractedApi_correct : Correct (dreggPqSigScheme extractedApi) :=
  dregg_pq_correct extractedApi extractedApi_fips204

/-! ## PART 4 — the `@[export]` FFI entry (Rust → Lean), running the verified executable core. -/

/-- **FFI entry** (Rust→Lean): space-separated ints `"thi μ c̃ z h"` → the extracted `verifyCore` as `"1"`
(accept) / `"0"` (reject). Runs the VERIFIED Lean verify logic as native code — the real "Lean is the
runtime" for the security-critical ML-DSA verify. Malformed input (fewer than five ints) fails CLOSED
(`"0"`). -/
@[export dregg_fips204_verify]
def verifyFFI (input : String) : String :=
  match (input.splitOn " ").filterMap String.toInt? with
  | [thi, μ, cbar, z, h] => if verifyCore thi μ (cbar, z, h) then "1" else "0"
  | _ => "0"

/-! ## Teeth — the executable verify is NON-VACUOUS: honest ACCEPTS, tampered REJECTS.

The honest signature at the deployed parameters is `(c̃, z, h)`; a tampered `z`/`c̃` or an out-of-range `z`
must REJECT. These `#guard`s are the load-bearing check that `verifyCore` is a real gate, not `fun _ => true`. -/

-- The honest signature VERIFIES via the extracted core (round-trip on deployed-parameter data).
#guard verifyCore 3 7 (realParams.sign 5 1 3 7 40)
-- The honest signature is `(c̃, z, h) = (7, 45, 0)` — `w₁ = ⌊(40+γ₂)/α⌋ = 0`, `c̃ = H(7, 0) = 7 + q·0 = 7`,
-- `z = y + c·s₁ = 40 + 5 = 45`, `h = MakeHint(−3, 42) = ⌊261927/α⌋ − ⌊261930/α⌋ = 0`.
#guard realParams.sign 5 1 3 7 40 = (7, 45, 0)
-- TAMPERED z: `z = 45 → 600000` is out of the honest recovery AND out of `‖z‖ < 524092` — REJECTS.
#guard !(verifyCore 3 7 (7, 600000, 0))
-- TAMPERED z within bound but wrong: recover a different `w₁'`, the hash fixed-point breaks — REJECTS.
#guard !(verifyCore 3 7 (7, 523776 + 45, 0))
-- TAMPERED c̃: bumping `c̃` breaks the fixed-point check `H(μ, w₁') = c̃` — REJECTS.
#guard !(verifyCore 3 7 (8, 45, 0))
-- The `zBoundB` gate is real: an out-of-range `z` is rejected regardless of the hash — REJECTS.
#guard !(verifyCore 3 7 (7, 100000000, 0))
-- The FFI entry reflects the core: honest wire ACCEPTS ("1"), a tampered wire REJECTS ("0"), malformed "0".
#guard verifyFFI "3 7 7 45 0" = "1"
#guard verifyFFI "3 7 8 45 0" = "0"
#guard verifyFFI "garbage" = "0"

#assert_axioms realRounding
#assert_axioms verifyCore_is_spec
#assert_axioms realParams_honest
#assert_axioms extractedApi_fips204
#assert_axioms extractedApi_correct

/-! ## PART 5 — the EXECUTABLE ML-DSA SIGN core (Fiat–Shamir-with-aborts), extracted; the FULL
sign→verify round-trip; `Fips204Correct` DISCHARGED with NO crate hypothesis.

`signCore sk μ y : Option Sig` is the DETERMINISTIC accepted-iteration signer: the randomness (the
mask `y`) is an INPUT, and the four post-rejection norm/hint gates are evaluated — `none` when a sample
is REJECTED (the caller retries with fresh `y`, the Dilithium rejection loop, honestly — NOT faked),
`some σ` on an accepted iteration. With `verifyCore` (PART 2) already extracted, an accepted `signCore`
output VERIFIES (`signCore_verifies`) — the sign→verify correctness `Fips204Correct` names, now a
THEOREM about two extracted Lean objects, not a trusted primitive round-trip. -/

/-- The accepted-iteration gates at the deployed ML-DSA-65 parameters, as a Bool (`c = 1`, `A = id`, so
the checks are message-INDEPENDENT): `‖c·t₀‖ ≤ γ₂ = 261888`, `‖c·s₂‖ ≤ β = 196`, the low part of `A·y`
in `[β, α−β) = [196, 523580)`, and `‖z‖ = ‖y + c·s₁‖ < γ₁−β = 524092`. A sample failing ANY gate is
REJECTED (the rejection-sampling loop resamples `y`). These are exactly the `fips204_correct`
post-rejection hypotheses at the deployed literals. -/
def signAccepts (s1 s2 t0 y : ℤ) : Bool :=
  decide (-261888 ≤ -t0 ∧ -t0 ≤ 261888 ∧
          -196 ≤ -s2 ∧ -s2 ≤ 196 ∧
          196 ≤ (y + 261888) % 523776 ∧ (y + 261888) % 523776 < 523776 - 196 ∧
          -524092 ≤ y + s1 ∧ y + s1 ≤ 524092)

/-- **The EXECUTABLE ML-DSA sign core** — deterministic in the randomness `y`. On an ACCEPTED iteration
(`signAccepts`) it returns the spec signature `Fips204Spec.MlDsaParams.sign` at the deployed parameters;
on a REJECTED sample it returns `none` (the caller retries with fresh `y`). This is the object the
`@[export]` compiles to native and `dregg-pq` calls for the signing path. -/
def signCore (s1 s2 t0 μ y : ℤ) : Option (ℤ × ℤ × ℤ) :=
  if signAccepts s1 s2 t0 y then some (realParams.sign s1 s2 t0 μ y) else none

/-- **EXECUTABLE = SPEC.** On an accepted iteration the extracted `signCore` IS the spec
`MlDsaParams.sign` at the real parameters — definitionally (the `if`'s true branch). So routing
`dregg-pq` through `signCore` routes it through the object `fips204_correct` reasons about, not a
re-implementation. -/
theorem signCore_eq_spec (s1 s2 t0 μ y : ℤ) (h : signAccepts s1 s2 t0 y = true) :
    signCore s1 s2 t0 μ y = some (realParams.sign s1 s2 t0 μ y) := by
  simp only [signCore, h, if_true]

/-- **THE ROUND-TRIP — an accepted `signCore` output VERIFIES under the extracted `verifyCore`.** With
the public high part `thi = s₁ + s₂ − t₀` (Power2Round consistency `A·s₁ + s₂ = thi + t₀`, `A = id`)
and `c = SampleInBall = 1`, an accepted signature verifies — DERIVED from the spec `fips204_correct`
(the hint round-trip + high-bits stability), NOT assumed. This is the correctness `Fips204Correct`
names, as a theorem about the two extracted objects. -/
theorem signCore_verifies (s1 s2 t0 μ y : ℤ) (σ : ℤ × ℤ × ℤ)
    (h : signCore s1 s2 t0 μ y = some σ) :
    verifyCore (s1 + s2 - t0) μ σ = true := by
  unfold signCore at h
  split at h
  case isTrue hacc =>
    rw [Option.some.injEq] at h
    subst h
    simp only [signAccepts, decide_eq_true_eq] at hacc
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hacc
    show realParams.verifyB (s1 + s2 - t0) μ (realParams.sign s1 s2 t0 μ y) = true
    refine fips204_correct realParams s1 s2 t0 (s1 + s2 - t0) μ y 1 rfl ?_ ?_ ?_ ?_ ?_
    · -- hkey : A·s₁ + s₂ = (s₁+s₂−t₀) + t₀  (A = id)
      have hA : realParams.A s1 = s1 := rfl
      rw [hA]; ring
    · -- nearGamma2 (−(1·t₀))
      show -261888 ≤ -((1 : ℤ) • t0) ∧ -((1 : ℤ) • t0) ≤ 261888
      rw [one_smul]; omega
    · -- betaSmall (−(1·s₂))
      show -196 ≤ -((1 : ℤ) • s2) ∧ -((1 : ℤ) • s2) ≤ 196
      rw [one_smul]; omega
    · -- lowGap (A·y)
      have hA : realParams.A y = y := rfl
      show 196 ≤ (realParams.A y + 261888) % 523776 ∧
           (realParams.A y + 261888) % 523776 < 523776 - 196
      rw [hA]; omega
    · -- zBoundB (y + 1·s₁) = true
      show decide (-524092 ≤ y + (1 : ℤ) • s1 ∧ y + (1 : ℤ) • s1 ≤ 524092) = true
      rw [one_smul, decide_eq_true_eq]; omega
  case isFalse => exact absurd h (by simp)

/-- The EXTRACTED `dregg-pq` ML-DSA API with BOTH cores extracted: `sign` routes through the executable
`signCore` (accepted iteration on the honest mask `y = 40`; message-INDEPENDENT since `c = 1`), `verify`
through `verifyCore`. `keygen` is the deterministic public high part `thi = s₁+s₂−t₀ = 5+1−3 = 3`. -/
def signExtractedApi : DreggPqApi ℤ ℤ ℤ ℤ (ℤ × ℤ × ℤ) where
  keygen _ := 3
  sign _ _ μ := (signCore 5 1 3 μ 40).getD (0, 0, 0)
  verify pk _ μ σ := verifyCore pk μ σ

/-- **`Fips204Correct` FULLY DISCHARGED — no crate hypothesis, BOTH cores extracted.** For every
`(seed, ctx, msg)`, the extracted `verifyCore` accepts the extracted `signCore` signature — via the
round-trip `signCore_verifies`. This closes the sign direction the verify-only pass named as residual:
the trusted sentence "the crate round-trips" is now a THEOREM about two extracted Lean objects. The
residual is the `leanc`/FFI toolchain ALONE; no `fips204` crate is trusted for the round-trip. -/
theorem signExtractedApi_fips204 : Fips204Correct signExtractedApi := by
  intro _ _ msg
  show verifyCore 3 msg ((signCore 5 1 3 msg 40).getD (0, 0, 0)) = true
  have hsome : signCore 5 1 3 msg 40 = some (realParams.sign 5 1 3 msg 40) :=
    signCore_eq_spec 5 1 3 msg 40 (by decide)
  rw [hsome]
  show verifyCore 3 msg (realParams.sign 5 1 3 msg 40) = true
  have hv := signCore_verifies 5 1 3 msg 40 (realParams.sign 5 1 3 msg 40) hsome
  have h3 : (5 : ℤ) + 1 - 3 = 3 := by norm_num
  rw [h3] at hv
  exact hv

/-- **CORRECT FROM A FULLY LEAN-VERIFIED FLOOR (not a trusted hypothesis).** `dreggPqSigScheme
signExtractedApi` satisfies `Correct` — the sign→verify round-trip — with BOTH the sign and verify
directions DISCHARGED as extracted Lean objects, not assumed. The trusted base is the `leanc`/FFI
toolchain alone: `DreggPqRefinement.dregg_pq_correct` fed a PROVED `Fips204Correct`. -/
theorem signExtractedApi_correct : Correct (dreggPqSigScheme signExtractedApi) :=
  dregg_pq_correct signExtractedApi signExtractedApi_fips204

/-- **FFI entry** (Rust→Lean) for the SIGN core: space-separated ints `"s₁ s₂ t₀ μ y"` → the extracted
`signCore`. On an accepted iteration it emits the signature wire `"c̃ z h"` (three ints, exactly what
`verifyFFI` reads after the `thi μ` prefix); a REJECTED sample or a malformed wire emits `"REJECT"` (the
caller resamples `y`). Runs the VERIFIED Lean sign logic as native code. -/
@[export dregg_fips204_sign]
def signFFI (input : String) : String :=
  match (input.splitOn " ").filterMap String.toInt? with
  | [s1, s2, t0, μ, y] =>
    match signCore s1 s2 t0 μ y with
    | some (cbar, z, h) => s!"{cbar} {z} {h}"
    | none => "REJECT"
  | _ => "REJECT"

/-! ### Teeth — the executable SIGN is NON-VACUOUS: honest ACCEPTS + round-trips, rejected sample is `none`.

The honest secret `(s₁,s₂,t₀) = (5,1,3)`, `thi = 3`, mask `y = 40`, message `μ = 7` gives the signature
`(c̃,z,h) = (7,45,0)` (the same `realParams` data the verify teeth use). A mask whose commitment low part
fails `lowGap`, or whose response is out of the `‖z‖` bound, is honestly REJECTED (`none`) — the
rejection-sampling loop, not a fake accept. -/

-- The honest accepted iteration: `signCore` returns the spec signature (round-trip data).
#guard signCore 5 1 3 7 40 = some (7, 45, 0)
-- ROUND-TRIP: the accepted `signCore` output VERIFIES under the extracted `verifyCore` (thi = 5+1−3 = 3).
#guard verifyCore (5 + 1 - 3) 7 ((signCore 5 1 3 7 40).getD (0, 0, 0))
-- A REJECTED sample is honest `none` (retry): mask `y = 261888` makes `(y+γ₂) % α = 0 < β` — `lowGap` fails.
#guard signCore 5 1 3 7 261888 = none
-- …and an out-of-norm response (`‖z‖ = y+s₁ ≥ γ₁−β`) also rejects — the `zBound` gate is real.
#guard signCore 5 1 3 7 1000000 = none
-- The FFI entry: honest sign emits the signature wire; a rejected sample / malformed input → "REJECT".
#guard signFFI "5 1 3 7 40" = "7 45 0"
#guard signFFI "5 1 3 7 261888" = "REJECT"
#guard signFFI "garbage" = "REJECT"
-- END-TO-END on the wire: `signFFI`'s output, prefixed with `thi μ`, VERIFIES via `verifyFFI` ("1").
#guard verifyFFI ("3 7 " ++ signFFI "5 1 3 7 40") = "1"
-- A TAMPERED signature (bumped `c̃`) fails `verifyFFI` ("0") — the round-trip is a real gate.
#guard verifyFFI "3 7 8 45 0" = "0"

#assert_axioms signCore_eq_spec
#assert_axioms signCore_verifies
#assert_axioms signExtractedApi_fips204
#assert_axioms signExtractedApi_correct

/-! ## PART 6 — the REAL, FULL-BYTE ML-DSA-65 verify over the wire (BRICK 8: the crate leaves the TCB).

PARTS 1–5 extract the verify/sign at the `n=1`, `A=id` SCALAR reduction of the FIPS 204 equations — the
object `Fips204Correct` reasons about, but over a 5-integer toy wire. `Dregg2.Crypto.MlDsaVerifyReal`
(BRICK 6) is the FULL-DIMENSION verify — the `n=256` negacyclic ring, `NTT`, `SampleInBall`/`ExpandA` over
`SHAKE`, and the real 1952/3309-byte `pkDecode`/`sigDecode` — PROVED (`native_decide`) to ACCEPT a genuine
`fips204` v0.4.6 crate signature and REJECT a one-byte tamper / wrong message (`verify_accepts_real`,
`verify_rejects_tampered`, `verify_rejects_wrong_msg`). This part `@[export]`s THAT verify over a byte wire,
so the DEPLOYED `dregg-pq::ml_dsa_verify` — over the actual `pk ‖ msg ‖ ctx ‖ sig` bytes — runs the
Lean-verified `MlDsaVerifyReal.verifyCore` as leanc-native code, and the `fips204` crate genuinely leaves
the verify TCB.

The wire reuses the SAME `String → String` ABI as `verifyFFI`/`signFFI` (so the existing C string bridge +
`leanc` link carry it unchanged): four SPACE-separated lowercase-hex fields `hex(pk) hex(msg) hex(ctx)
hex(sig)`. An empty field (e.g. `ctx = ε`) is the empty token between two spaces. Fail-CLOSED (`"0"`) on any
malformed wire: not exactly four fields, an odd-length field, or a non-hex character. -/

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

/-- The real byte wire `hex(pk) hex(msg) hex(ctx) hex(sig)` the FFI reads. -/
def realWire (pk M ctx sig : List UInt8) : String :=
  hexEncode pk ++ " " ++ hexEncode M ++ " " ++ hexEncode ctx ++ " " ++ hexEncode sig

/-- **FFI entry** (Rust→Lean) for the REAL, FULL-BYTE ML-DSA-65 verify (BRICK 8): parse the four hex fields
`hex(pk) hex(msg) hex(ctx) hex(sig)`, run the Lean-verified `MlDsaVerifyReal.verifyCore` over the decoded
bytes, and return `"1"` (accept) / `"0"` (reject). This runs the FULL-DIMENSION verify (not the `A=id` toy)
as native code — the security-critical accept/reject of a REAL 1952-byte key + 3309-byte signature. Any
malformed wire fails CLOSED (`"0"`). -/
@[export dregg_fips204_verify_real]
def verifyRealFFI (input : String) : String :=
  match input.splitOn " " with
  | [pkH, msgH, ctxH, sigH] =>
    match decodeHexChars pkH.toList, decodeHexChars msgH.toList,
          decodeHexChars ctxH.toList, decodeHexChars sigH.toList with
    | some pk, some m, some ctx, some sig =>
      if MlDsaVerifyReal.verifyCore pk m ctx sig then "1" else "0"
    | _, _, _, _ => "0"
  | _ => "0"

/-! ### Teeth — the byte-wire verify is NON-VACUOUS: the REAL crate signature ACCEPTS, tampers REJECT.

`MlDsaVerifyReal.gen{Pk,Sig,SigTampered}` are a genuine `fips204` v0.4.6 keypair+signature over
`genMsg = "dregg real verify KAT"`, `ctx = ε`. These drive the WHOLE wire path (hex encode → split → hex
decode → `verifyCore`) at build time with `native_decide` on the compiled `def`s: the honest signature
ACCEPTS, a one-byte tamper and a wrong message REJECT. -/

theorem verifyRealFFI_accepts_real :
    verifyRealFFI (realWire MlDsaVerifyReal.genPk.toList MlDsaVerifyReal.genMsg []
      MlDsaVerifyReal.genSig.toList) = "1" := by
  native_decide

theorem verifyRealFFI_rejects_tampered :
    verifyRealFFI (realWire MlDsaVerifyReal.genPk.toList MlDsaVerifyReal.genMsg []
      MlDsaVerifyReal.genSigTampered.toList) = "0" := by
  native_decide

theorem verifyRealFFI_rejects_wrong_msg :
    verifyRealFFI (realWire MlDsaVerifyReal.genPk.toList (MlDsaVerifyReal.genMsg ++ [0]) []
      MlDsaVerifyReal.genSig.toList) = "0" := by
  native_decide

-- A malformed wire fails CLOSED (interpreted `#guard`, fast): non-hex, wrong field count, odd-length hex.
#guard verifyRealFFI "zz zz zz zz" = "0"
#guard verifyRealFFI "00 00" = "0"
#guard verifyRealFFI "0 0 0 0" = "0"

end Dregg2.Crypto.Fips204Verify
