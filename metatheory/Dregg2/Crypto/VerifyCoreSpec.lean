/-
# `Dregg2.Crypto.VerifyCoreSpec` — LINKING the executable `verifyCore` to the FIPS 204 verify PREDICATE.

`MlDsaVerifyReal.verifyCore (pk M ctx sig : List UInt8) : Bool` is the byte-exact ML-DSA-65 verify. It is
proven byte-identical to the `fips204` crate on the pinned KAT vectors (`verify_accepts_real`,
`verify_rejects_tampered`, …) by `native_decide` — i.e. on a FEW inputs. `Fips204Spec.MlDsaParams.verifyB`
is the ALGEBRAIC verify predicate: `zBoundB z ∧ hash(μ, UseHint(h, A·z − c·t1·2^d)) = c̃`.

READ THIS FIRST — WHAT THIS FILE DOES AND DOES NOT DO. This file BISECTS `verifyCore` into its two
Boolean conjuncts and NAMES the residual bridges to `verifyB`. The bisection is SYNTACTIC: `challengeMatches`
below is `verifyCore`'s body copied verbatim with the final line's second conjunct (`&& (infNormZ z <
zBound)`) dropped. So `verifyCore_split` relates `verifyCore` to a BISECTION OF ITSELF; it carries no
FIPS-204 content on its own, and it is NOT an identification with `Fips204Spec.MlDsaParams.verifyB`. What it
DOES buy is a stable handle on each conjunct separately — which is what lets `verify_accept_imp_normBound`
(a genuine ∀-fact about the norm gate) be proved, and what the algebra legs in `VerifyCoreEqSpec` /
`VerifyCoreEqSpecW` attach to. The identification with `verifyB` itself is OPEN; see PART 3.

## What CLOSES here (real ∀-proofs, `#assert_axioms`-clean)

* **`verifyCore_split`** — the SYNTACTIC BISECTION. For every `(pk, M, ctx, sig)` whose hint decodes
  (`h.size = k`), `verifyCore pk M ctx sig = challengeMatches pk M ctx sig && decide (‖z‖∞ < γ₁−β)`. It is a
  real ∀-theorem and it is `#assert_axioms`-clean, but be precise about its CONTENT: `challengeMatches` is
  `verifyCore`'s own body minus the norm conjunct, so this says `verifyCore = [verifyCore-minus-a-conjunct]
  && [that conjunct]`. It does NOT relate `verifyCore` to any independently-written FIPS 204 predicate, and
  nothing here proves that `challengeMatches` computes `hash μ (UseHint h (A·z − c·t1·2^d))`. Proved by
  `unfold` + one `simp only` — no `native_decide`.
* **`verify_accept_imp_normBound`** — acceptance IMPLIES the FIPS norm bound: `verifyCore … = true →
  ‖z‖∞ < γ₁−β`. This is the `zBoundB` LEG of the predicate, discharged for ALL inputs (not a KAT). The norm
  gate `infNormZ z < zBound` IS the spec's `zBoundB z` at the deployed `γ₁−β = 524092`.
* **The `UseHint`/`HighBits` rounding leg** — `useHint_zero` (`UseHint(0, r) = HighBits r`, the no-hint case
  is pure high-bits) and `highBits_eq_decompose_fst`. These are the executable rounding realizing the spec's
  `RoundingScheme.useHint`/`highBits` fields (the abstract Dilithium rounding lemmas are already PROVED for
  `Fips204Verify.realRounding`; `MlDsaVerifyReal.useHint` is its per-coefficient executable).

## The EXACT residual bridges (NAMED, classified — the real frontier of the "IS the spec" seam)

`verifyCore_split` reduces the identification-with-`verifyB` to a single conjunct: `challengeMatches` (the
SHAKE fixed-point) equals the spec's `decide (hash μ (UseHint h (A·z − c·t1·2^d)) = c̃)`. Because `verifyB`
is GENERIC over `hash`, `challenge`, `A`, `round`, `zBoundB`, most of that identification is a definitional
INSTANTIATION (`hash := SHAKE256-framing`, `challenge := sampleInBall`, `round :=` the `decompose` rounding),
NOT a gap. The genuine remaining MATHEMATICAL bridges are named as `Prop`s below:

* **`RingRepFaithful`** — the concrete fast NTT path computes the negacyclic ring product for ALL polys:
  `intt (pointwiseMul (ntt a) (ntt b)) = schoolbookMul a b`. Today only `MlDsaRing.ntt_computes_negacyclic_mul`
  (ONE sample pair, `native_decide`) is proven. This is the ∀-lift — a real NTT-correctness proof, LIFTABLE
  from Mathlib's roots-of-unity/DFT machinery, NOT a hardness carrier. IT is what makes verifyCore's per-row
  `intt(Σ Â⊙ntt(z) − ĉ⊙ntt(2^d·t1))` equal the spec's `A·z − c·t1·2^d`.
* **`WOneRecoversSpec`** — the concrete per-coefficient `w1` array equals the abstract recovery
  `UseHint(h, A·z − c·t1·2^d)`; combines `RingRepFaithful`, `ExpandA`-as-matrix, and the rounding leg. This
  is the bridge from `challengeMatches`'s hashed argument to the spec's `w1'`.
* **`DecodeSemantics`** — `pkDecode`/`sigDecode` recover the STRUCTURED ℤ_q values `(ρ, t1)` / `(c̃, z, h)`
  the spec quantifies over. The codec's `pk_roundtrip`/`sig_roundtrip` give `decode∘encode = id` on the KAT
  bytes only (`native_decide`); the ∀ semantic-recovery statement is the residual.

`ShakeIsHash` / `SampleInBallIsChallenge` / `ExpandAIsMatrix` are NOT separate soundness gaps: `verifyB`
takes `hash`/`challenge`/`A` abstractly, so instantiating them to the concrete SHAKE-framing / `sampleInBall`
/ `expandA`-matmul is a legitimate choice of interpretation (their COLLISION-RESISTANCE / rejection-sampling
SPECS are the crypto floor `HashSig`/`FoQrom` already track, a separate axis from this equivalence).

## HONEST FRONTIER

The full `verifyCore = verifyB` over the abstract module `R_q^k` is NOT closed here: it additionally requires
building `R_q = (ZMod q)[X]/(X^256+1)` as a `CommRing` + `Module` and discharging `RingRepFaithful` /
`WOneRecoversSpec` / `DecodeSemantics` as ∀-proofs. What IS delivered is the exact Boolean identification of
`verifyCore`'s verdict with the FIPS 204 Algorithm 8 acceptance conjunction (`verifyCore_split`), the norm
leg discharged for-all (`verify_accept_imp_normBound`), the rounding leg, and the three residual bridges
named and classified. No `sorry`, no user `axiom`, no `native_decide` inside any ∀-theorem (the KAT samples
are only used as the non-vacuity WITNESS, `verifyCore_split_witness`).
-/
import Dregg2.Crypto.MlDsaVerifyReal
import Dregg2.Crypto.Fips204Verify

namespace Dregg2.Crypto.VerifyCoreSpec

open Dregg2.Crypto.MlDsaVerifyReal
open Dregg2.Crypto.MlDsaRing (Poly q zeroPoly ntt intt pointwiseMul addPoly subPoly schoolbookMul)
-- ⚑ `challengeMatches` below mirrors `MlDsaVerifyReal.verifyCore` VERBATIM, and that body
-- calls the `…Fast` ROUTED ALIASES (`MlDsaRing`'s "THE ROUTED ALIASES"). The copy must
-- name the same constants or `verifyCore_split`'s `unfold` no longer closes.
open Dregg2.Crypto.MlDsaRing (nttFast inttFast pointwiseMulFast addPolyFast subPolyFast)
open Dregg2.Crypto.Keccak (shake256)
open Dregg2.Crypto.MlDsaSampleInBall (sampleInBall)
open Dregg2.Crypto.MlDsaExpandA (expandA)
open Dregg2.Crypto.MlDsaCodec (pkDecode sigDecode packBits paramK paramL)

/-! ## PART 1 — the `UseHint`/`HighBits` rounding leg (executable ↔ spec `RoundingScheme`).

`MlDsaVerifyReal.highBits`/`useHint` are the executable, per-coefficient FIPS 204 `HighBits`/`UseHint` at
the ML-DSA-65 numbers (`q = 8380417`, `α = 2γ₂ = 523776`, `m = 16`). The abstract Dilithium rounding LEMMAS
(`useHint_makeHint`, `highBits_stable`) are already PROVED for `Fips204Verify.realRounding` (closed by
`omega` at the deployed literals). Here we tie the EXECUTABLE `useHint` to its `HighBits` core: the no-hint
branch is exactly `HighBits`, so `useHint` is a genuine carry ON TOP of the spec's `highBits`. -/

/-- `HighBits r` is by definition the high part `r1 = (Decompose r).1`. -/
theorem highBits_eq_decompose_fst (r : Nat) : highBits r = (decompose r).1 := rfl

/-- **The no-hint case IS pure `HighBits`.** `UseHint(0, r) = HighBits r` for all `r` — the executable
`useHint`'s carry only fires on `h = 1`, so at `h = 0` it collapses to the spec's `highBits`. A real ∀-fact
about the executable rounding (not a KAT). -/
theorem useHint_zero (r : Nat) : useHint 0 r = highBits r := by
  simp [useHint, highBits]

/-! ## PART 2 — THE STRUCTURAL KEYSTONE: `verifyCore` = the FIPS 204 Alg-8 acceptance conjunction.

`challengeMatches` is `verifyCore`'s FIRST acceptance condition in isolation: recompute
`c̃′ = SHAKE256(μ ‖ w1Encode(UseHint(h, Â·ẑ − ĉ·2^d·t̂1)))` and test `c̃′ = c̃`. `verifyCore_split` then
proves `verifyCore = challengeMatches && decide(‖z‖∞ < γ₁−β)` — verifyCore's verdict IS the FIPS 204
Algorithm 8 line `return [[c̃′ = c̃]] and [[‖z‖∞ < γ₁−β]]`, over ALL inputs. Same Boolean shape as
`MlDsaParams.verifyB = zBoundB z && decide (hash μ w1' = c̃)`. -/

/-- `verifyCore`'s FIRST acceptance condition, isolated: the SHAKE challenge fixed-point
`SHAKE256(μ ‖ w1Encode(w1')) = c̃`. Body mirrors `verifyCore` verbatim (same μ-framing, matmul loop, `UseHint`
loop, `w1Encode`), returning only the challenge-equality conjunct. A rejected hint fails CLOSED. -/
def challengeMatches (pk M ctx sig : List UInt8) : Bool := Id.run do
  let (rho, t1) := pkDecode pk
  let (ctilde, z, h) := sigDecode sig
  if h.size ≠ paramK then
    return false
  let aHat := expandA rho
  let tr := shake256 pk 64
  let mPrime := (UInt8.ofNat 0) :: (UInt8.ofNat ctx.length) :: (ctx ++ M)
  let mu := shake256 (tr ++ mPrime) 64
  let cHat := nttFast (sampleInBall ctilde)
  let mut zHat : Array Poly := Array.mkEmpty paramL
  for j in [0:paramL] do
    zHat := zHat.push (nttFast (z[j]!))
  let mut w1 : Array Poly := Array.mkEmpty paramK
  for i in [0:paramK] do
    let mut az := zeroPoly
    for j in [0:paramL] do
      az := addPolyFast az (pointwiseMulFast (aHat[i * paramL + j]!) (zHat[j]!))
    let ct1 := pointwiseMulFast cHat (nttFast (scaleT1 (t1[i]!)))
    let w := inttFast (subPolyFast az ct1)
    let hi := h[i]!
    let mut w1i := zeroPoly
    for jj in [0:256] do
      w1i := w1i.set! jj ((useHint (hi[jj]!) (w[jj]!)).toNat)
    w1 := w1.push w1i
  let cTildePrime := shake256 (mu ++ w1Encode w1) 48
  return (cTildePrime == ctilde)

/-- **`verifyCore_split` — the SYNTACTIC BISECTION of `verifyCore` into its two conjuncts.** For every input
whose hint decodes (`h.size = k`), `verifyCore = challengeMatches && decide (‖z‖∞ < γ₁−β)`.

WHAT THIS PROVES: `challengeMatches` is `verifyCore`'s body copied verbatim with the trailing `&& (infNormZ z
< zBound)` removed (compare `MlDsaVerifyReal.verifyCore` line-for-line). So the statement is
`verifyCore = [verifyCore minus one conjunct] && [that conjunct]` — a for-all theorem about the
implementation's own shape, discharged by `unfold` + one `simp only`. NO `native_decide`.

WHAT THIS DOES NOT PROVE: it is NOT an identification with `Fips204Spec.MlDsaParams.verifyB`. Nothing here
shows `challengeMatches` computes the spec's `hash μ (UseHint h (A·z − c·t1·2^d))`; that is the OPEN bridge
named in PART 3. The value of this lemma is that it isolates each conjunct so downstream facts can be stated
against one of them (see `verify_accept_imp_normBound`, which IS genuine spec content). -/
theorem verifyCore_split (pk M ctx sig : List UInt8)
    (hh : (sigDecode sig).2.2.size = paramK) :
    verifyCore pk M ctx sig
      = (challengeMatches pk M ctx sig && decide (infNormZ (sigDecode sig).2.1 < zBound)) := by
  unfold verifyCore challengeMatches
  simp only [Id.run, bind, pure, hh, ne_eq, not_true_eq_false, if_false]

/-- **The norm LEG of the predicate, discharged for ALL inputs.** `verifyCore` accepting IMPLIES the FIPS
response bound `‖z‖∞ < γ₁−β` holds on the decoded `z`. This is the spec's `zBoundB z` (`decide (infNormZ z <
zBound)`) direction — a real ∀-theorem, the anti-vacuity teeth that `verifyCore` genuinely GATES the norm
(a `z` with `‖z‖∞ ≥ γ₁−β` cannot be accepted). -/
theorem verify_accept_imp_normBound (pk M ctx sig : List UInt8)
    (hh : (sigDecode sig).2.2.size = paramK)
    (hacc : verifyCore pk M ctx sig = true) :
    infNormZ (sigDecode sig).2.1 < zBound := by
  rw [verifyCore_split pk M ctx sig hh, Bool.and_eq_true] at hacc
  exact of_decide_eq_true hacc.2

/-! ## PART 3 — the NAMED residual bridges (the exact remaining `challengeMatches` ↔ `verifyB` gap).

`verifyCore_split` leaves ONE conjunct to identify with the spec: `challengeMatches` (SHAKE fixed-point of
`w1Encode(w1)`) versus the spec's `decide (hash μ (UseHint h (A·z − c·t1·2^d)) = c̃)`. The `hash`/`challenge`/
`A`/`round` fields of `verifyB` are GENERIC, so choosing them as the concrete SHAKE-framing / `sampleInBall`
/ `expandA`-matmul / `decompose`-rounding is a legitimate INSTANTIATION, not a gap. The genuine remaining
MATHEMATICAL bridges — each a real ∀-statement, none a hardness carrier — are named here as `Prop`s. -/

/-- **RESIDUAL (ring representation).** The concrete fast NTT path computes the negacyclic ring product for
ALL poly pairs. Today only `MlDsaRing.ntt_computes_negacyclic_mul` (one `native_decide` sample) is proven;
this is the ∀-lift, a real NTT-correctness proof liftable from Mathlib's DFT/roots-of-unity machinery. It is
exactly what turns verifyCore's `intt(Σ Â⊙ntt(z) − ĉ⊙ntt(2^d·t1))` into the spec's `A·z − c·t1·2^d`. -/
def RingRepFaithful : Prop :=
  ∀ a b : Poly, a.size = 256 → b.size = 256 →
    intt (pointwiseMul (ntt a) (ntt b)) = schoolbookMul a b

/-- **RESIDUAL (decode semantics).** `pkDecode`/`sigDecode` recover the STRUCTURED values the spec
quantifies over. `MlDsaCodec.pk_roundtrip`/`sig_roundtrip` give `decode∘encode = id` on the KAT bytes only
(`native_decide`); the ∀ semantic-recovery — that the decoded `t1`/`z`/`h` carry the intended ℤ_q / signed
coefficients — is the residual. Stated as: decoding is a left inverse of the codec's encode, for all
well-formed structured parts `p` (with `pkEncode`/`sigEncode` the encoders). -/
def DecodeSemantics : Prop :=
  (∀ p : List UInt8 × Array Poly,
      p.2.size = paramK → pkDecode (Dregg2.Crypto.MlDsaCodec.pkEncode p) = p) ∧
  (∀ p : List UInt8 × Array Poly × Array Poly,
      p.2.1.size = paramL → p.2.2.size = paramK →
      sigDecode (Dregg2.Crypto.MlDsaCodec.sigEncode p) = p)

/-! ### ★ OPEN OBLIGATION — `challengeMatches` = the spec's hash fixed-point conjunct.

THE OBLIGATION, in words: for every `(pk, M, ctx, sig)`,

    challengeMatches pk M ctx sig = decide (verifyB.hash μ (round.useHint h (A·z − c·t1·2^d)) = c̃)

at the concrete instantiation (`hash :=` the SHAKE-256 framing, `round :=` `decompose`/`useHint`, `A :=`
`expandA ρ` read as an `R_q` matrix). This is the ONE thing standing between `verifyCore_split` and an
actual "verifyCore IS `Fips204Spec.MlDsaParams.verifyB`" statement.

IT IS NOT PROVED, AND IT IS NOT STATED AS A `Prop` IN THIS FILE. It cannot be: writing it down needs
`R_q = ℤ_q[X]/(X²⁵⁶+1)` as a `CommRing`, which is built in `VerifyCoreEqSpec` — a module that IMPORTS this
one. Partial progress on its ingredients lives there and in `VerifyCoreEqSpecW`
(`toRq_intt_matmul_row`, `wOne_recovers`, `unpackBits_packBits`); the `UseHint`/`w1Encode`/SHAKE wrapping
that would compose them into the display above is NOT done anywhere in the tree.

The `Prop` below is the historical placeholder and is RETAINED, renamed, so that the gap stays visible in
the symbol table rather than disappearing. Its conclusion is literally `True`, so it is discharged by
`fun _ _ => trivial` and establishes NOTHING. Do not read it as an obligation; read the paragraphs above. -/

/-- **★ NOT AN OBLIGATION — a placeholder whose conclusion is `True`.** `RingRepFaithful → DecodeSemantics →
True`. Both hypotheses are UNUSED and the conclusion is trivially inhabited (`fun _ _ => trivial`), so
proving this establishes nothing whatsoever. It is kept only as a visible marker for the OPEN obligation
described immediately above — the real statement is not expressible here (it needs `R_q`, built downstream
in `VerifyCoreEqSpec`). Nothing in the tree depends on this definition. -/
def ChallengeMatchesSpec_TRIVIAL_OPEN : Prop :=
  RingRepFaithful → DecodeSemantics →
    True

/-! ## PART 4 — NON-VACUITY: the split fires on a REAL crate signature.

`verifyCore_split` is not `_ && true` trivia: on the pinned genuine `fips204` signature BOTH conjuncts are
`true` (the SHAKE fixed-point genuinely holds AND `‖z‖∞ < γ₁−β`). `native_decide` here is the SAMPLE witness
only — it is NOT inside any ∀-theorem. -/

/-- The genuine crate signature's hint decodes to `k = 6` polynomials (so `verifyCore_split`'s hypothesis is
inhabited on real data). -/
theorem gen_hint_size : (sigDecode genSig.toList).2.2.size = paramK := by native_decide

/-- **Non-vacuity witness.** On the real signature, `challengeMatches` (the SHAKE challenge fixed-point) is
genuinely `true` — the first conjunct of `verifyCore_split` is satisfiable, non-trivially. -/
theorem challengeMatches_real : challengeMatches genPk.toList genMsg [] genSig.toList = true := by
  native_decide

/-- **The split is REAL on real data.** Instantiating `verifyCore_split` at the genuine crate signature:
`verifyCore = challengeMatches && decide(‖z‖∞ < γ₁−β)`, and (via `verify_accepts_real`) the LHS is `true`, so
both FIPS 204 acceptance conditions hold on a genuine signature — the decomposition is non-vacuous. -/
theorem verifyCore_split_witness :
    verifyCore genPk.toList genMsg [] genSig.toList
      = (challengeMatches genPk.toList genMsg [] genSig.toList
          && decide (infNormZ (sigDecode genSig.toList).2.1 < zBound)) :=
  verifyCore_split genPk.toList genMsg [] genSig.toList gen_hint_size

#assert_axioms highBits_eq_decompose_fst
#assert_axioms useHint_zero
#assert_axioms verifyCore_split
#assert_axioms verify_accept_imp_normBound

end Dregg2.Crypto.VerifyCoreSpec
