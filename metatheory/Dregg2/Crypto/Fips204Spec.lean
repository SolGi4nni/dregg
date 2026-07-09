/-
# `Dregg2.Crypto.Fips204Spec` — a Lean model of the FIPS 204 (ML-DSA) ALGORITHM, and its CORRECTNESS.

`DreggPqRefinement.lean` names the trusted floor precisely: `Fips204Correct api` — the sign→verify
round-trip of the `fips204` (ML-DSA-65) crate — is taken as a HYPOTHESIS, "exactly as the abstract
EUF-CMA game assumes ML-DSA is a signature scheme". This file is the BEACHHEAD toward discharging it:
it MODELS the FIPS 204 ML-DSA algorithm over the module `R_q^k` and PROVES its correctness round-trip
(`fips204_correct`), so the trusted sentence "the crate round-trips" is reduced to the smaller
"the crate implements THIS spec" (`fips204Correct_reduces`, `section Discharge`).

## Why ML-DSA is the hard case (and what this adds over `HermineThreshold`)

`HermineThreshold.verify` already models the lattice relation `A·z = w + c·t`, but Hermine/Raccoon uses
Fiat–Shamir WITHOUT aborts (noise-flooding) and NO rounding — signing is one linear map. FIPS 204 ML-DSA
is the DILITHIUM family, and its correctness rests on the two features Raccoon lacks:

* **Fiat–Shamir WITH aborts (rejection).** Signing loops, re-sampling the mask `y`, until the response
  `z = y + c·s₁` and the low part of `w − c·s₂` pass the norm bounds `‖z‖ < γ₁ − β`, `‖LowBits‖ < γ₂ − β`.
  We model the ACCEPTED iteration: the bounds are HYPOTHESES (`hz`, `hlow`, `hcs2`) — the post-rejection
  state. The loop that establishes them is the standard Dilithium rejection-termination fact, NAMED (not
  modeled) in the honest boundary below.
* **The high-bits / hint machinery** (`Power2Round`, `HighBits`, `LowBits`, `MakeHint`, `UseHint`). The
  public key carries only `t₁` (the high bits of `t = A·s₁ + s₂`); verification recovers the signer's
  `w₁ = HighBits(w)` from `A·z − c·t₁·2^d` USING the transmitted hint `h`. Correctness is the theorem that
  this recovery SUCCEEDS.

## The correctness argument (`fips204_correct`)

Two ingredients, cleanly separated:

1. **The algebraic identity (`az_identity`) — pure module algebra, PROVED unconditionally.**
   `A·z − c·t₁·2^d = w − c·s₂ + c·t₀`, where `t = t₁·2^d + t₀` (Power2Round) and `t = A·s₁ + s₂`,
   `w = A·y`, `z = y + c·s₁`. This is where the public high-bits key `t₁·2^d` and the secret low part `t₀`
   meet: the `c·A·s₁` terms cancel and the residue is exactly the perturbation the hint must correct.
2. **The two standard rounding lemmas (`RoundingScheme`), carried as an interface and DISCHARGED on a
   concrete instance.** `UseHint(MakeHint(z,r), r) = HighBits(r+z)` (hint round-trip) and
   `HighBits(r+s) = HighBits(r)` when `‖LowBits r‖ < γ₂−β` and `‖s‖ ≤ β` (high-bits stability under a small
   perturbation). Composed with the identity: `UseHint(h, A·z − c·t₁·2^d) = HighBits(w − c·s₂) = HighBits(w)
   = w₁`, so verify recomputes the SAME `w₁` the signer hashed — the round-trip closes.

These two are STANDARD Dilithium rounding lemmas, NOT hardness carriers (`#assert_axioms` never sees a
hypothesis, but there is none here of the `def …Hard` kind — the rounding facts are ∀-fields of a
`RoundingScheme` that we INSTANTIATE and PROVE for a concrete base-α decomposition, `toyRounding`, whose
two fields are closed by `omega`). So the correctness is not conditioned on an unproved rounding oracle:
it is generic over any `RoundingScheme`, and a real one is exhibited.

## HONEST BOUNDARY (named, not hidden)

* **crate ↔ spec.** This proves the SPEC's correctness. Discharging `DreggPqRefinement.Fips204Correct`
  fully requires that the `fips204` CRATE implements THIS algorithm (`fips204Correct_reduces` makes the
  gap a single hypothesis: the crate's honest output equals the modeled accepted iteration). That gap is
  crate↔spec — strictly smaller than crate↔nothing — and is the beachhead, not a closed door.
* **rejection termination.** The unconditional `Fips204Correct` (∀ seed/ctx/msg) also needs that the
  rejection loop ALWAYS terminates with the bounds satisfied — a standard Dilithium probabilistic
  termination lemma. We model the accepted iteration and take the bounds as hypotheses; the termination
  lemma is NAMED here, not proved.
* **deployed parameters.** `toyRounding` is a single-coefficient base-16 decomposition over `ℤ` (a small
  `(n,q)` toy, `n=1`, no `q`-reduction). The general FIPS 204 decompose at `n=256, q=8380417, γ₂=(q−1)/32`
  is the same two lemmas over `ℤ_q` — a number-theoretic sublemma, not a carrier — left for the next lane.

Mirrors the anchoring style of `CapabilityChain.lean` / `ConsensusSafety.lean`: the load-bearing object is
the theorem STATEMENT, and every seam is classified in prose.
-/
import Dregg2.Crypto.DreggPqRefinement
import Mathlib.Algebra.Module.LinearMap.Defs

namespace Dregg2.Crypto.Fips204Spec

open Dregg2.Crypto.DreggPqRefinement

/-! ## PART 1 — the rounding/hint interface: the two STANDARD Dilithium lemmas as an interface.

`RoundingScheme` bundles the FIPS 204 rounding operations — `highBits` (the `w₁` a verifier recomputes),
`makeHint`/`useHint` (the hint the signer sends and the verifier applies), and the three norm predicates
(`nearGamma2 ≈ ‖·‖ ≤ γ₂`, `betaSmall ≈ ‖·‖ ≤ β`, `lowGap ≈ ‖LowBits ·‖ < γ₂−β`) — together with the two
correctness lemmas of the Dilithium rounding: the hint round-trip and high-bits stability. It is an
INTERFACE (`fips204_correct` is generic over it), and it is INHABITED by a concrete decomposition
(`toyRounding`, PART 3) whose two lemma-fields are proved — so the correctness is not laundered through an
unproved rounding oracle. -/

/-- The FIPS 204 rounding/hint machinery over the commitment module `N`, as an interface carrying the two
standard Dilithium rounding lemmas. `HB` is the high-bits type (`w₁` lives here); `Hint` the hint type. -/
structure RoundingScheme (N : Type*) [AddCommGroup N] (HB Hint : Type*) where
  /-- `HighBits` — the high part of a commitment, hashed into the challenge. -/
  highBits : N → HB
  /-- `MakeHint z r` — the signer's hint correcting the low part (`z` the correction, `r` the base). -/
  makeHint : N → N → Hint
  /-- `UseHint h r` — the verifier recovers the high bits of `r` corrected by the hint `h`. -/
  useHint : Hint → N → HB
  /-- `‖·‖ ≤ γ₂` — the `MakeHint` precondition (the `‖c·t₀‖ < γ₂` check). -/
  nearGamma2 : N → Prop
  /-- `‖·‖ ≤ β` — the small-perturbation bound (here `‖c·s₂‖ ≤ β`). -/
  betaSmall : N → Prop
  /-- `‖LowBits ·‖ < γ₂ − β` — the low-part bound the rejection loop enforces on `w`. -/
  lowGap : N → Prop
  /-- **Standard Dilithium hint round-trip.** `UseHint(MakeHint(z,r), r) = HighBits(r + z)` whenever the
  correction `z` is `γ₂`-small. -/
  useHint_makeHint : ∀ z r : N, nearGamma2 z → useHint (makeHint z r) r = highBits (r + z)
  /-- **Standard Dilithium high-bits stability.** A `β`-small perturbation of a commitment with a
  low-gapped low part does not change its high bits: `HighBits(r + s) = HighBits(r)`. -/
  highBits_stable : ∀ r s : N, lowGap r → betaSmall s → highBits (r + s) = highBits r

/-! ## PART 2 — the ML-DSA algorithm over the module `R_q^k`, and its correctness.

`A : M →ₗ[R] N` is the public matrix (`M = R_q^l`, `N = R_q^k`); `R` the challenge ring (`R_q`). The
public key is `(A, t₁·2^d)` (we carry the high part `thi := t₁·2^d ∈ N` directly); the secret is
`(s₁, s₂, t₀)` with `t = A·s₁ + s₂ = thi + t₀` (Power2Round). Signing is the accepted iteration of
Fiat–Shamir-with-aborts; verification recovers `w₁` via the hint. -/

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {HB Hint Cbar Msg : Type*}

/-- The public parameters + rounding of an ML-DSA instance: the matrix `A`, the rounding/hint scheme, the
Fiat–Shamir hash `hash : Msg → HB → Cbar` (`H(μ ‖ w₁)`), the challenge derivation `challenge : Cbar → R`
(`SampleInBall`), and the response norm check `zBoundB` (`‖z‖ < γ₁ − β`, decidable Bool). -/
structure MlDsaParams (R M N HB Hint Cbar Msg : Type*)
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] where
  /-- The public matrix `A` (the `k×l` block over `R_q`). -/
  A : M →ₗ[R] N
  /-- The FIPS 204 rounding/hint machinery. -/
  round : RoundingScheme N HB Hint
  /-- The Fiat–Shamir hash `H(μ ‖ w₁)`. -/
  hash : Msg → HB → Cbar
  /-- `SampleInBall`: derive the challenge polynomial `c` from the hash digest. -/
  challenge : Cbar → R
  /-- The response norm gate `‖z‖ < γ₁ − β` (decidable). -/
  zBoundB : M → Bool

/-- **Sign — the accepted Fiat–Shamir-with-aborts iteration.** Given the secret `(s₁, s₂, t₀)` and a mask
`y` (the last, accepted sample of the rejection loop): commit `w = A·y`, hash `w₁ = HighBits(w)` to
`c̃ = H(μ, w₁)`, derive `c = SampleInBall(c̃)`, respond `z = y + c·s₁`, and build the hint
`h = MakeHint(−c·t₀, w − c·s₂ + c·t₀)`. The signature is `(c̃, z, h)`. (The norm gates that make this the
ACCEPTED iteration are the `fips204_correct` hypotheses.) -/
def MlDsaParams.sign (P : MlDsaParams R M N HB Hint Cbar Msg)
    (s1 : M) (s2 t0 : N) (μ : Msg) (y : M) : Cbar × M × Hint :=
  let w := P.A y
  let cbar := P.hash μ (P.round.highBits w)
  let c := P.challenge cbar
  (cbar, y + c • s1, P.round.makeHint (-(c • t0)) (w - c • s2 + c • t0))

/-- **Verify.** Recover the challenge `c = SampleInBall(c̃)`, recompute `w₁' = UseHint(h, A·z − c·t₁·2^d)`
(here `A·z − c·thi`), and accept iff `H(μ, w₁') = c̃` (the challenge is a fixed point) and `‖z‖` passes the
bound. Fail-closed: any mismatch is `false`. -/
def MlDsaParams.verifyB [DecidableEq Cbar] (P : MlDsaParams R M N HB Hint Cbar Msg)
    (thi : N) (μ : Msg) (σ : Cbar × M × Hint) : Bool :=
  let cbar := σ.1
  let z := σ.2.1
  let h := σ.2.2
  let c := P.challenge cbar
  let w1' := P.round.useHint h (P.A z - c • thi)
  P.zBoundB z && decide (P.hash μ w1' = cbar)

/-- **The algebraic core (pure module algebra, PROVED unconditionally).** With Power2Round consistency
`A·s₁ + s₂ = thi + t₀` (i.e. `t = t₁·2^d + t₀`), the verifier's recovery argument equals the signer's
perturbed commitment: `A·(y + c·s₁) − c·thi = A·y − c·s₂ + c·t₀`. The `c·A·s₁` terms cancel; the residue
`− c·s₂ + c·t₀` is exactly what the hint corrects. This is the leg that makes the high-bits key `thi = t₁·2^d`
and the secret `t₀` line up. -/
theorem az_identity (A : M →ₗ[R] N) (s1 : M) (s2 t0 thi : N) (y : M) (c : R)
    (hkey : A s1 + s2 = thi + t0) :
    A (y + c • s1) - c • thi = A y - c • s2 + c • t0 := by
  have hthi : thi = A s1 + s2 - t0 := by rw [hkey]; abel
  rw [map_add, map_smul, hthi, smul_sub, smul_add]
  abel

/-- **`fips204_correct` — THE CORRECTNESS ROUND-TRIP.** An honestly-generated ML-DSA signature verifies.
For the accepted signing iteration on mask `y` (so the post-rejection bounds hold: `nearGamma2 (−c·t₀)` is
the `‖c·t₀‖ < γ₂` gate, `betaSmall (−c·s₂)` the `‖c·s₂‖ ≤ β` bound, `lowGap (A·y)` the `‖LowBits w‖ < γ₂−β`
gate, `zBoundB z` the `‖z‖ < γ₁−β` gate), with `c = SampleInBall(H(μ, w₁))` the honest challenge and
Power2Round consistency `hkey`, the verifier ACCEPTS. The crux: the verifier recomputes
`UseHint(h, A·z − c·thi) = HighBits(w − c·s₂) = HighBits(w) = w₁` — the SAME high bits the signer hashed —
via `az_identity` and the two `RoundingScheme` lemmas. NON-VACUOUS: `zBoundB z` is a real Bool gate (a
tampered `z` fails it or the hash check), and the hash check binds `w₁'` to `w₁`. -/
theorem fips204_correct [DecidableEq Cbar] (P : MlDsaParams R M N HB Hint Cbar Msg)
    (s1 : M) (s2 t0 thi : N) (μ : Msg) (y : M) (c : R)
    (hc : c = P.challenge (P.hash μ (P.round.highBits (P.A y))))
    (hkey : P.A s1 + s2 = thi + t0)
    (hct0 : P.round.nearGamma2 (-(c • t0)))
    (hcs2 : P.round.betaSmall (-(c • s2)))
    (hlow : P.round.lowGap (P.A y))
    (hz : P.zBoundB (y + c • s1) = true) :
    P.verifyB thi μ (P.sign s1 s2 t0 μ y) = true := by
  -- The recovered high bits equal the signer's `w₁ = HighBits (A y)`.
  have hrecover :
      P.round.useHint
        (P.round.makeHint (-(c • t0)) (P.A y - c • s2 + c • t0))
        (P.A (y + c • s1) - c • thi)
        = P.round.highBits (P.A y) := by
    -- Rewrite the verifier's recovery target to the signer's perturbed commitment (algebra).
    rw [az_identity P.A s1 s2 t0 thi y c hkey]
    -- Hint round-trip: `UseHint(MakeHint(−c·t₀, r), r) = HighBits(r + (−c·t₀))`.
    rw [P.round.useHint_makeHint _ _ hct0]
    -- Simplify `(A y − c·s₂ + c·t₀) + (−c·t₀) = A y + (−c·s₂)`.
    have hsimp : (P.A y - c • s2 + c • t0) + (-(c • t0)) = P.A y + (-(c • s2)) := by abel
    rw [hsimp]
    -- High-bits stability: a `β`-small perturbation of the low-gapped `w` keeps `HighBits` fixed.
    exact P.round.highBits_stable _ _ hlow hcs2
  -- Discharge the two Bool conjuncts of `verifyB`.
  unfold MlDsaParams.verifyB MlDsaParams.sign
  simp only [← hc]
  rw [hrecover]
  simp only [hz, Bool.true_and, decide_eq_true_eq]

#assert_axioms az_identity
#assert_axioms fips204_correct

/-! ## PART 3 — a CONCRETE rounding, its two lemmas DISCHARGED, and TEETH.

`toyRounding` is a single-coefficient base-`16` decomposition over `ℤ` (a small `(n,q)` toy): `HighBits r =
⌊r/16⌋`, `MakeHint z r = HighBits(r+z) − HighBits r` (the carry), `UseHint h r = HighBits r + h`. Its two
`RoundingScheme` lemmas are PROVED (closed by `omega`, which models `ediv`/`emod` by the literal base), so
the interface is genuinely inhabited — the correctness of PART 2 is not laundered through an unproved
rounding oracle. -/

/-- The concrete base-16 rounding over `ℤ`. `nearGamma2 = ‖·‖ ≤ 8 (= γ₂)`, `betaSmall = ‖·‖ ≤ 2 (= β)`,
`lowGap = LowBits ∈ [β, α−β) = [2, 14)`. Both lemma-fields are discharged by `omega`. -/
def toyRounding : RoundingScheme ℤ ℤ ℤ where
  highBits r := r / 16
  makeHint z r := (r + z) / 16 - r / 16
  useHint h r := r / 16 + h
  nearGamma2 z := -8 ≤ z ∧ z ≤ 8
  betaSmall s := -2 ≤ s ∧ s ≤ 2
  lowGap r := 2 ≤ r % 16 ∧ r % 16 < 14
  useHint_makeHint z r _ := by omega
  highBits_stable r s hlow hbeta := by
    obtain ⟨_, _⟩ := hlow; obtain ⟨_, _⟩ := hbeta; omega

/-- The concrete ML-DSA toy: `A = id` (`a = 1`, so `A·y = y`), `hash μ w₁ = μ + 100·w₁` (injective in `w₁`
on the toy range), `challenge = 1` (`c = 1`), `‖z‖ < 1000` the response gate. -/
def toyParams : MlDsaParams ℤ ℤ ℤ ℤ ℤ ℤ ℤ where
  A := LinearMap.id
  round := toyRounding
  hash μ hb := μ + 100 * hb
  challenge _ := 1
  zBoundB z := decide (-1000 ≤ z ∧ z ≤ 1000)

/-! ### Teeth — the honest signature VERIFIES via `fips204_correct`; a tampered `z`/`c̃` FAILS. -/

/-- **The honest round-trip fires through the GENERAL theorem** (not just `decide`). Secret
`s₁=5, s₂=1, t₀=3`, public high part `thi=3` (so `t = 5+1 = 6 = 3+3`), mask `y=40`: `fips204_correct`
proves the modeled verify accepts. All post-rejection bounds hold on concrete data. -/
theorem toy_honest_verifies :
    toyParams.verifyB 3 7 (toyParams.sign 5 1 3 7 40) = true :=
  fips204_correct toyParams 5 1 3 3 7 40 1
    (by decide) (by decide) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
    ⟨by decide, by decide⟩ (by decide)

-- The honest signature VERIFIES (the modeled sign→verify round-trip, computed).
#guard toyParams.verifyB 3 7 (toyParams.sign 5 1 3 7 40)
-- The honest signature is `(c̃, z, h) = (207, 45, 0)` — `w₁ = ⌊40/16⌋ = 2`, `c̃ = 7 + 100·2 = 207`.
#guard toyParams.sign 5 1 3 7 40 = (207, 45, 0)
-- TAMPERED z: replacing `z = 45` with `60` makes the verifier recover `⌊57/16⌋ = 3 ≠ 2`, so the hash
-- check `H(7,3) = 307 ≠ 207 = c̃` fails — verify REJECTS.
#guard !(toyParams.verifyB 3 7 (207, 60, 0))
-- TAMPERED c̃: bumping `c̃ = 207` to `208` breaks the fixed-point check `H(7, w₁') = 207 ≠ 208` — REJECTS.
#guard !(toyParams.verifyB 3 7 (208, 45, 0))
-- The `zBoundB` gate is real: an out-of-range `z` is rejected regardless of the hash.
#guard !(toyParams.verifyB 3 7 (207, 100000, 0))

/-! ## PART 4 — `section Discharge`: reducing the trusted `Fips204Correct` to the crate↔spec gap.

The payoff: `DreggPqRefinement.Fips204Correct api` (the trusted round-trip hypothesis) is REDUCED to a
single named boundary — that the crate's honest output, per message, IS the modeled accepted iteration
(the crate↔spec refinement) with the post-rejection bounds holding (the rejection-termination lemma). No
lattice hardness enters; the reduction bottoms out at `fips204_correct` (PROVED). -/

section Discharge

variable {Seed PK : Type*}

/-- **`fips204Correct_reduces` — the beachhead.** The trusted `DreggPqRefinement.Fips204Correct api`
follows once, for EVERY `(seed, ctx, msg)`, the crate's honest `verify(keygen, sign)` output equals the
modeled `verifyB` on some accepted iteration whose post-rejection bounds hold. That hypothesis `real` is
exactly the crate↔spec refinement plus the rejection loop delivering the bounds — the two named,
non-hardness boundaries — strictly smaller than crate↔nothing. The conclusion is DERIVED from
`fips204_correct`, so no fresh assumption is introduced. -/
theorem fips204Correct_reduces [DecidableEq Cbar]
    (api : DreggPqApi Seed PK Ctx Msg (Cbar × M × Hint))
    (P : MlDsaParams R M N HB Hint Cbar Msg')
    (real : ∀ (seed : Seed) (ctx : Ctx) (msg : Msg),
      ∃ (s1 : M) (s2 t0 thi : N) (μ : Msg') (y : M) (c : R),
        c = P.challenge (P.hash μ (P.round.highBits (P.A y))) ∧
        P.A s1 + s2 = thi + t0 ∧
        P.round.nearGamma2 (-(c • t0)) ∧
        P.round.betaSmall (-(c • s2)) ∧
        P.round.lowGap (P.A y) ∧
        P.zBoundB (y + c • s1) = true ∧
        api.verify (api.keygen seed) ctx msg (api.sign seed ctx msg)
          = P.verifyB thi μ (P.sign s1 s2 t0 μ y)) :
    Fips204Correct api := by
  intro seed ctx msg
  obtain ⟨s1, s2, t0, thi, μ, y, c, hc, hkey, hct0, hcs2, hlow, hz, heq⟩ := real seed ctx msg
  rw [heq]
  exact fips204_correct P s1 s2 t0 thi μ y c hc hkey hct0 hcs2 hlow hz

end Discharge

#assert_axioms toy_honest_verifies
#assert_axioms toyRounding
#assert_axioms fips204Correct_reduces

end Dregg2.Crypto.Fips204Spec
