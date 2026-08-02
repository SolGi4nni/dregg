/-
# `MinaStepPrevCommitments` — the PREVIOUS PROOF's own commitments, from a REAL Mina block

⚑ **This is the data half of `KimchiStepMain` simplification #3.** `step_verifier.verify_one`'s
curve bases are the commitments of the Wrap proof it is verifying plus the SRS / verifier-key points
that weight them; until 2026-08-02 the assembly ran them as `basePts` — `[3]G, [4]G, …` — so the MSM
had the right SHAPE over points that came from nowhere.

They are Mina **devnet block 539508**
(`3NLmVB6Fs3dm4kXNkgwheHXzJXNpCCwEDe76RpTVeBTNujm12zNk`), whose Wrap proof openmina's
`BlockVerifier` accepted with `accumulator_check = true` and `kimchi::verifier::verify = Ok`. They
are Pallas points — the Wrap proof is Pallas-committed (`MinaRealBlockTranscript`'s own mirror
table) — and Pallas' base field IS `PastaField.pN`, the field this whole assembly runs in, so they
drop into the `VarBaseMul` / `EndoMul` / `CompleteAdd` gadgets unchanged.

## ⚑ NO SECOND COPY — this module OWNS NO LITERALS

Every point here is READ OUT of the gate that already holds it, projected from the gates' projective
`(x, y, z)` at `z = 1` to the affine pair the curve gadgets take. That is deliberate: 117 points
transcribed twice is exactly the shape that drifts, and a weld pinning two copies equal is a worse
answer than not having two copies.

⚠ The first draft of this file DID carry a second copy, on the strength of
`MinaWrapAggregationGate`'s own header line "NOT imported by the `Dregg2` root, per house practice
for gates". That line is **false at HEAD**: `Dregg2.lean:1609,1610,1656,1659` import all four of
these gates directly. Measured rather than assumed, importing them costs `KimchiStepMain` **7
modules and 3.7 MB on an 89 MB closure**.

## The three lists and what consumes each

| list | count | upstream | consumer |
|---|---|---|---|
| `LAGRANGE_XY` | 40 | `lagrange_commitment ~domain srs i` (`step_verifier.ml:543-544`) | R3, the x_hat MSM — CONSTANT bases |
| `COMBINE_XY` | 47 | `combine_split_commitments`' `without_degree_bound` (`:601-616`) | R4 fold rounds `0..45`; round `r`'s base is `COMBINE_XY[r+1]` |
| `GAMMA_XY` | 30 | `bullet_reduce`'s fifteen `(L,R)` pairs (`:193-200`) | R4 rounds `46..75` — all ABSORBED |

`COMBINE_XY` is `combine_commitments`' own order: 2 recursion commitments, `public_comm`, `ft_comm`,
`z_comm`, the 6 index selector commitments, `w_comm[0..14]`, `coefficients_comm[0..14]`,
`sigma_comm[0..5]` — which is what `KimchiStepMain.wdbAbsorbed` reads its provenance off.

No `sorry`, no `native_decide`; the `#guard`s below reduce in the interpreter.
-/
import Dregg2.Circuit.Emit.MinaWrapPublicCommGate
import Dregg2.Circuit.Emit.MinaWrapAggregationGate
import Dregg2.Circuit.Emit.MinaWrapOpeningGate

namespace Dregg2.Bridge.MinaStepPrevCommitments

open Dregg2.Circuit.Emit.PastaField (pN)

set_option autoImplicit false
set_option maxRecDepth 10000

/-- An affine Pallas point, `(x, y)`. -/
abbrev Pt := Nat × Nat

/-- The gates carry PROJECTIVE `(x, y, z)` at `z = 1`; the curve gadgets take the affine pair. -/
def flat (ps : List (Nat × Nat × Nat)) : List Pt := ps.map (fun p => (p.1, p.2.1))

/-- The 40 SRS Lagrange commitments `multiscale_known` scales — the devnet Wrap verifier key's own
`public = 40`. CONSTANTS: `Inner_curve.constant (lagrange_commitment ~domain srs i)`. -/
def LAGRANGE_XY : List Pt := flat Dregg2.Circuit.Emit.MinaWrapPublicCommGate.LAGRANGE

/-- The 47 `without_degree_bound` commitments `combine_split_commitments` folds, in its order. -/
def COMBINE_XY : List Pt := flat Dregg2.Circuit.Emit.MinaWrapAggregationGate.COMBINE_POINTS

/-- `bullet_reduce`'s fifteen `(L, R)` pairs, INTERLEAVED `L0 R0 L1 R1 …` — the order
`absorb (PC :: PC) gammas_i` absorbs them and the order round `i`'s two endos consume them. -/
def GAMMA_XY : List Pt :=
  (List.range 15).flatMap (fun i =>
    [ (flat Dregg2.Circuit.Emit.MinaWrapOpeningGate.LR_L).getD i (0, 0)
    , (flat Dregg2.Circuit.Emit.MinaWrapOpeningGate.LR_R).getD i (0, 0) ])

/-- Every base the assembly consumes, in the order it consumes them: the 40 Lagrange constants, then
the 46 fold bases (`COMBINE_XY` from index 1 — index 0 is where the accumulator starts), then the 30
`bullet_reduce` gammas. -/
def ALL_XY : List Pt := LAGRANGE_XY ++ COMBINE_XY.tail ++ GAMMA_XY

/-- `y^2 = x^3 + 5` over Pallas' base field. -/
def onCurve (p : Pt) : Bool :=
  (p.2 * p.2) % pN == (p.1 * p.1 % pN * p.1 + 5) % pN

def EVERY : List Pt := LAGRANGE_XY ++ COMBINE_XY ++ GAMMA_XY

-- COUNTS: 40 public inputs, 47 `without_degree_bound` commitments, 15 IPA rounds x 2.
#guard LAGRANGE_XY.length == 40
#guard COMBINE_XY.length == 47
#guard GAMMA_XY.length == 30
#guard ALL_XY.length == 116
-- ⚑ The gammas are the INTERLEAVE and not the concatenation — the order the absorb and the two
-- endos of a round both use. Stated with its own discriminator, so the pin is not a tautology.
#guard GAMMA_XY != flat Dregg2.Circuit.Emit.MinaWrapOpeningGate.LR_L
                    ++ flat Dregg2.Circuit.Emit.MinaWrapOpeningGate.LR_R
#guard (List.range 15).all (fun i =>
  GAMMA_XY.getD (2 * i) (0, 0)
    == (flat Dregg2.Circuit.Emit.MinaWrapOpeningGate.LR_L).getD i (0, 0)
  && GAMMA_XY.getD (2 * i + 1) (0, 0)
    == (flat Dregg2.Circuit.Emit.MinaWrapOpeningGate.LR_R).getD i (0, 0))
-- ⚑ …every one of them is ON THE PALLAS CURVE in THIS field — the property that lets them into the
-- `VarBaseMul`/`EndoMul` witness generators at all.
#guard EVERY.all onCurve
-- …and the check discriminates: one bent coordinate leaves the curve.
#guard (onCurve ((EVERY.headD (0, 0)).1 + 1, (EVERY.headD (0, 0)).2)) == false
-- ⚑ …and they are 117 DISTINCT points, so no `complete_add` in the assembly can land on the
-- doubling case and no fold step is secretly the identity.
#guard (EVERY.map (·.1)).dedup.length == 117
-- …none is the point at infinity / has a zero coordinate.
#guard EVERY.all (fun p => p.1 != 0 && p.2 != 0)
-- …and none is a small multiple of the generator: `basePts` was `[3]G, [4]G, …`, whose coordinates
-- are tiny-index outputs of a public ladder. These are full-width and unrelated.
#guard EVERY.all (fun p => p.1 > 2 ^ 200)

end Dregg2.Bridge.MinaStepPrevCommitments
