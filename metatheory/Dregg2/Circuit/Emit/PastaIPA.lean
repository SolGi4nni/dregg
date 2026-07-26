/-
# Dregg2.Circuit.Emit.PastaIPA — the IPA opening verifier, DEFERRAL-FIRST
(the cost center C9 of `docs/KIMCHI-VERIFY-SPEC.md`; task K4 of `docs/MINA-KIMCHI-VERIFIER-PLAN.md`).

## What this file IS (and the deferral it gets right)

Kimchi's polynomial commitment is an IPA/bulletproof over Pasta (NOT KZG). Its `SRS::verify`
(`poly-commitment/src/ipa.rs:301-502`) is dominated by ONE term: the s-vector MSM `⟨s, G⟩` with
`2^k = 65536` non-native Vesta scalar muls (`k = 16` for Mina's wrap SRS) — `10⁷–10⁸` gates, two
orders of magnitude beyond everything else in the whole verifier. **Pickles DEFERS it** (the `sg`
split, `ipa.rs:335-336`): the verifier accumulates the obligation across recursion and the giant
MSM is checked ONCE, outside the circuit. This is the entire "as gas-efficient as possible" answer
(`docs/…PLAN.md` "K5 design crux").

The mathematical fact that MAKES deferral sound — and this file's load-bearing theorem — is that
the `2^k`-entry s-vector is NOT independent data: it is exactly the **coefficient vector of the
`b`-polynomial**, which is fully determined by the `k` round challenges. So the in-circuit verifier
carries a COMPACT accumulator of `k` challenges (16 field elements), and the `2^k`-term MSM is
reconstructed from them at the single deferred check. `sVec_eq_bPoly` proves the identity:

  `Σ_{i<2^k} (sVec cs)[i] · xⁱ  =  ∏_{j<k} (1 + cs[j]·x^{2^{…}})`   (`b_poly` = `b_poly_coefficients`)

by induction on the challenge list — the tensor/doubling structure of `commitment.rs:426-476`.

## What is AUTHORED + built vs NAMED (honest scope)

AUTHORED + built: the `b`-poly evaluator (`bEval`) + the s-vector (`sVec`, the doubling recursion of
`b_poly_coefficients`) + the Horner `polyEval`; the **coefficient identity `sVec_eq_bPoly`** (the
deferral's justification, proved by induction, `#assert_axioms`-clean) with its helper algebra
(`polyEval_append`, `polyEval_map_mul`, `sVec_length`); the deferral accumulator `IpaDeferred` + the
round fold `absorbChallenges` + `deferredMsmSize` (the `2^k` vs `k` compression that IS the
deferral); KAT anchors (the identity + the accumulator sizes reduce in-kernel).

NAMED (the in-circuit round GADGET is composed from prior modules, not re-emitted here): each round
= a Poseidon challenge squeeze (K3 `PastaPoseidon`) + the `(uᵢ⁻¹·Lᵢ + uᵢ·Rᵢ)` fold (2 scalar muls
K4b `PastaScalarMul` + 1 RCB add K4a). The deferred `⟨s, G⟩` MSM cost (`2^k` scalar muls, `~10⁸`
gates) is NAMED, checked once outside recursion (§4). The full IPA accept equation (C9) is NOT
claimed proven — it is kernel-intractable (millions of gates); this file gets the DEFERRAL STRUCTURE
right and proves the identity that makes it sound.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/
`native_decide`. `#guard` KATs reduce in the kernel. NEW file; imports read-only
(`PastaScalarMul`, transitively K4a/K3/K2/K1); standalone (NOT imported by the truncated `Dregg2`
root; built directly as `Dregg2.Circuit.Emit.PastaIPA`).
-/
import Dregg2.Circuit.Emit.PastaScalarMul

namespace Dregg2.Circuit.Emit.PastaIPA

open Dregg2.Circuit.Emit.PastaField (pN)

set_option autoImplicit false

/-! ## §0 — The `b`-polynomial and the s-vector (the IPA folding, `commitment.rs:426-476`).

`bEval cs x` = `∏_j (1 + cs[j]·x^{2^{|rest|}})` — the b-polynomial evaluated at `x`, over the round
challenges `cs` (head = highest round, matching the fold's outer-to-inner order). `sVec cs` = its
`2^{|cs|}` coefficients, built by the DOUBLING recursion (`s ↦ s ++ (c · s)`) — the exact structure
of o1-labs `b_poly_coefficients`. `polyEval` is Horner (`Σ coeffs[i]·xⁱ`). -/

/-- The b-polynomial evaluated at `x` (product form; one factor per round challenge). -/
def bEval {F : Type} [CommRing F] (x : F) : List F → F
  | [] => 1
  | c :: rest => bEval x rest * (1 + c * x ^ (2 ^ rest.length))

/-- The s-vector: `2^{|cs|}` coefficients, by the doubling recursion (low half, then `c`·low half).
This is `commitment.rs:464-476` (`sᵢ = ∏_{j : bit j of i set} cs[j]`), in its recursive form. -/
def sVec {F : Type} [CommRing F] : List F → List F
  | [] => [1]
  | c :: rest => let s := sVec rest; s ++ s.map (fun z => z * c)

/-- Horner polynomial evaluation `Σ_i coeffs[i]·xⁱ`. -/
def polyEval {F : Type} [CommRing F] (x : F) : List F → F
  | [] => 0
  | c :: rest => c + x * polyEval x rest

/-! ## §1 — THE DEFERRAL IDENTITY: the s-vector is the b-poly coefficient vector.

This is why the accumulator can carry `k` challenges instead of the `2^k`-entry s-vector — the
`2^k`-term MSM `⟨s, G⟩` is reconstructible from the `k` challenges at the single deferred check. -/

/-- Horner splits over concatenation: `polyEval (a ++ b) = polyEval a + x^{|a|}·polyEval b`. -/
theorem polyEval_append {F : Type} [CommRing F] (x : F) (a b : List F) :
    polyEval x (a ++ b) = polyEval x a + x ^ a.length * polyEval x b := by
  induction a with
  | nil => simp [polyEval]
  | cons c rest ih =>
    simp only [List.cons_append, polyEval, ih, List.length_cons, pow_succ]
    ring

/-- Scaling every coefficient by `c` scales the evaluation by `c`. -/
theorem polyEval_map_mul {F : Type} [CommRing F] (x c : F) (a : List F) :
    polyEval x (a.map (fun z => z * c)) = c * polyEval x a := by
  induction a with
  | nil => simp [polyEval]
  | cons d rest ih =>
    simp only [List.map_cons, polyEval, ih]
    ring

/-- The s-vector has `2^{|cs|}` entries (the doubling). -/
theorem sVec_length {F : Type} [CommRing F] (cs : List F) : (sVec cs).length = 2 ^ cs.length := by
  induction cs with
  | nil => simp [sVec]
  | cons c rest ih =>
    simp only [sVec, List.length_append, List.length_map, ih, List.length_cons, pow_succ]
    ring

/-- **`sVec_eq_bPoly`** — the s-vector IS the coefficient vector of the b-polynomial:
`Σ_i (sVec cs)[i]·xⁱ = ∏_j (1 + cs[j]·x^{2^…})`. The deferral's soundness: the `2^k`-term MSM
`⟨s, G⟩` is fully determined by the `k` challenges, so it may be deferred and reconstructed once. -/
theorem sVec_eq_bPoly {F : Type} [CommRing F] (x : F) (cs : List F) :
    polyEval x (sVec cs) = bEval x cs := by
  induction cs with
  | nil => simp [sVec, polyEval, bEval]
  | cons c rest ih =>
    show polyEval x (sVec rest ++ (sVec rest).map (fun z => z * c)) = bEval x (c :: rest)
    rw [polyEval_append, polyEval_map_mul, sVec_length, ih]
    show bEval x rest + x ^ 2 ^ rest.length * (c * bEval x rest)
      = bEval x rest * (1 + c * x ^ 2 ^ rest.length)
    ring

#assert_axioms polyEval_append
#assert_axioms polyEval_map_mul
#assert_axioms sVec_length
#assert_axioms sVec_eq_bPoly

/-! ## §2 — The deferral accumulator (Pickles' `sg` split, the compact obligation).

The in-circuit verifier does NOT compute `⟨s, G⟩`. It accumulates the `k` round challenges (16
field elements) plus the `sg` commitment; the `2^k`-term MSM is the DEFERRED obligation, checked
once outside recursion. `deferredMsmSize` is the `2^k` term count the deferred check pays; the
accumulator's own size stays `k` — the compression that IS the deferral. -/

/-- The compact IPA deferral accumulator: the round challenges (in fold order) + the `sg` commitment
point (the split-off SRS combination whose `⟨s, G⟩` MSM is deferred). `F` = the scalar field, `Pt` =
a curve point (projective triple base or value). -/
structure IpaDeferred (F : Type) (Pt : Type) where
  /-- The `k` round challenges `uᵢ` (compact — `k = log₂(SRS)`, e.g. 16). -/
  chals : List F
  /-- The `sg` commitment (the deferred `⟨s, G⟩` collapses onto this across recursion). -/
  sg : Pt

/-- Absorb one round's challenge into the accumulator (append). The whole IPA rounds are this
folded — `k` rounds ⇒ `k` challenges. -/
def IpaDeferred.absorb {F Pt : Type} (d : IpaDeferred F Pt) (u : F) : IpaDeferred F Pt :=
  { d with chals := d.chals ++ [u] }

/-- Fold a whole round-challenge sequence into the accumulator (the log(n)-round loop). -/
def absorbChallenges {F Pt : Type} (d0 : IpaDeferred F Pt) (us : List F) : IpaDeferred F Pt :=
  us.foldl IpaDeferred.absorb d0

/-- After folding `us`, the accumulator holds exactly the starting challenges ++ `us` (the fold is
just accumulation — the round loop grows the compact challenge list by one per round). -/
theorem absorbChallenges_chals {F Pt : Type} (d0 : IpaDeferred F Pt) (us : List F) :
    (absorbChallenges d0 us).chals = d0.chals ++ us := by
  unfold absorbChallenges
  induction us generalizing d0 with
  | nil => simp
  | cons u rest ih =>
    rw [List.foldl_cons, ih]
    show (d0.chals ++ [u]) ++ rest = d0.chals ++ (u :: rest)
    rw [List.append_assoc]; rfl

/-- **The compact accumulator has `k` entries; the DEFERRED MSM it stands for has `2^k` terms.** -/
def deferredMsmSize {F Pt : Type} (d : IpaDeferred F Pt) : Nat := 2 ^ d.chals.length

/-- Starting empty, after `k` rounds the accumulator carries exactly `k` challenges, and the
deferred `⟨s, G⟩` it represents has `2^k` terms (`sVec_length`) — never materialized in-circuit. -/
theorem deferral_compression {F : Type} [CommRing F] {Pt : Type} (sg0 : Pt) (us : List F) :
    (absorbChallenges ⟨[], sg0⟩ us).chals.length = us.length ∧
    deferredMsmSize (absorbChallenges ⟨[], sg0⟩ us) = 2 ^ us.length ∧
    (sVec (absorbChallenges ⟨[], sg0⟩ us).chals).length = deferredMsmSize (absorbChallenges ⟨[], sg0⟩ us) := by
  have hc : (absorbChallenges (⟨[], sg0⟩ : IpaDeferred F Pt) us).chals = us := by
    rw [absorbChallenges_chals]; simp
  refine ⟨?_, ?_, ?_⟩ <;> simp only [deferredMsmSize, sVec_length, hc]

#assert_axioms absorbChallenges_chals
#assert_axioms deferral_compression

/-! ## §3 — KATs: the identity + the accumulator, in-kernel (small `k`), over ℤ.

The identity `Σ sᵢ xⁱ = ∏(1 + cᵢ x^{2^…})` reduces in the kernel for concrete small challenge
vectors — non-vacuity of `sVec_eq_bPoly` at real values (over ℤ for clean kernel reduction; the
theorem is over any `CommRing`, so the Fq = `ZMod pN` instance the verifier uses is covered). -/

/-- A concrete 3-round challenge vector. -/
def katChals : List ℤ := [7, 11, 13]

-- The identity holds at concrete points (both the derived-coeff sum and the product form agree).
#guard decide (polyEval (5 : ℤ) (sVec katChals) = bEval (5 : ℤ) katChals)
#guard decide (polyEval (2 : ℤ) (sVec katChals) = bEval (2 : ℤ) katChals)
-- The s-vector has 2^3 = 8 entries for 3 rounds; the accumulator itself carries 3.
#guard (sVec katChals).length == 8
#guard (absorbChallenges (⟨[], (0,0,0)⟩ : IpaDeferred ℤ (Nat×Nat×Nat)) katChals).chals.length == 3
#guard deferredMsmSize (absorbChallenges (⟨[], (0,0,0)⟩ : IpaDeferred ℤ (Nat×Nat×Nat)) katChals) == 8
-- b_poly_coefficients tensor structure: sVec [c] = [1, c] (one round), sVec [] = [1].
#guard sVec ([] : List ℤ) == [1]
#guard sVec ([9] : List ℤ) == [1, 9]
-- non-vacuity: a WRONG s-vector (bumped coeff) does NOT satisfy the identity.
#guard decide (polyEval (5 : ℤ) ((sVec katChals).set 3 0) ≠ bEval (5 : ℤ) katChals)

/-! ## §4 — Gate accounting: the CHEAP in-circuit round vs the DEFERRED `⟨s,G⟩` MSM.

**In-circuit, per proof** (`k = 16` rounds for Mina's wrap SRS):
  * `k` Poseidon challenge squeezes (K3, `PastaPoseidon`): `~16 · 3·10² ≈ 5·10³` gates;
  * the `(uᵢ⁻¹·Lᵢ + uᵢ·Rᵢ)` round fold: `2k = 32` GLV scalar muls (K4b, `~2.46M` each) — this is
    the dominant IN-circuit cost, `~8·10⁷`, but STILL bounded and one-shot per proof;
  * the `~50`-commitment combine + `b0`/`cip` field arithmetic (K1): `~10⁶`.

**DEFERRED (checked ONCE, outside recursion — the `sg` split)**:
  * the s-vector MSM `⟨s, G_SRS⟩` with `2^k = 65536` non-native Vesta scalar muls — `~10⁷–10⁸`
    gates. This is what `sVec_eq_bPoly` shows is reconstructible from the `k` accumulated
    challenges, so it is NEVER materialized in the recursive step: the accumulator carries `k = 16`
    field elements (`deferral_compression`), and the `65536`-term MSM is amortized across the
    recursion and discharged a single time at the terminal proof.

The deferral converts a per-recursion-step `10⁸`-gate MSM into a per-step `16`-element accumulation
plus ONE terminal `10⁸`-gate check — the whole "as gas-efficient as possible" lever. -/

/-- The Mina wrap-SRS round count (`k = log₂ 2^16`). -/
def kRounds : Nat := 16
/-- The deferred MSM term count at `k = 16`: `2^16 = 65536`. -/
def deferredTerms : Nat := 2 ^ kRounds

#guard deferredTerms == 65536
#guard kRounds == 16

/-! ## §5 — The PRECISE named residuals + the K5 continuation.

  1. **The in-circuit round GADGET is composed, not re-emitted here.** Each round = Poseidon
     squeeze (K3, forced by `PastaPoseidon.perm_forces`) + the `(uᵢ⁻¹·Lᵢ + uᵢ·Rᵢ)` fold (K4b
     `pallasLadder_forces` scalar muls + K4a `pallasCompleteAdd` add). The round's gate emission is
     the mechanical composition of those forced sub-gadgets; the deferral STRUCTURE + the identity
     that makes it sound are what this file adds. `to_field(endo_r)` (the 128-bit challenge → Fq
     map) rides K2's endo (`pallasEndo`, forced) + K3's transcript.
  2. **The full IPA accept equation (C9) is NOT proven** — the `msm(points, scalars) == 0` check
     (`ipa.rs:501`) is kernel-intractable (millions of gates). What is proven: the s-vector = b-poly
     coefficients (`sVec_eq_bPoly`), so the deferred `⟨s, G⟩` is soundly reconstructible from the
     compact challenge accumulator. Accept/reject on real fixtures is the K5 milestone.
  3. **The batching randomizers `rand_base`/`sg_rand_base`** are RNG-sampled in `ipa.rs:355-360`;
     in-circuit they must be Fiat–Shamir-derived (squeeze the fq-sponge after `delta`) — the
     `[R-design]` deviation named in `docs/KIMCHI-VERIFY-SPEC.md`. Not built here.
  4. **The shared K1–K4 residuals** — `z < p` canonical compare, `ℤ ↔ p_felt` field width, inherited
     modulus primality / RCB completeness / cofactor-1 — stand unchanged.

CONTINUATION (K5, `docs/KIMCHI-VERIFY-SPEC.md`): C1–C8 (transcript replay, the scalar checks, the
`f_comm`/`ft_comm` MSMs, `combined_inner_product`) compose K1–K3 + this file's scalar mul; C9 is
this deferral. The whole `to_batch` → `oracles` → `OpeningProof::verify` chain is the K5 build, of
which K4 supplies the curve/scalar-mul/deferral floor.
-/

end Dregg2.Circuit.Emit.PastaIPA
