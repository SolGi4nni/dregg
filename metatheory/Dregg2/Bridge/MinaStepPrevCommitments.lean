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

open Dregg2.Circuit.Emit.PastaField (pN qN)

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

/-! ## ⚑ THE PLONK INDEX — the 28 commitments `sponge_after_index` swallows

`step_verifier.ml:1149-1157`:

    let sponge_after_index index =
      let sponge = Sponge.create sponge_params in
      Array.iter (Types.index_to_field_elements ~g:Inner_curve.to_field_elements index)
        ~f:(fun x -> Sponge.absorb sponge (`Field x)) ;
      sponge

and `index` is `d.wrap_key` (`step_main.ml:61`) — **the same `Plonk_verification_key_evals.t` the
fold consumes as `~verification_key:m`**. `index_to_field_elements`
(`pickles_base/side_loaded_verification_key.ml:159-183`) is, verbatim,
`sigma_comm @ coefficients_comm @ [generic; psm; complete_add; mul; emul; endomul_scalar]` mapped
through `g` — 28 commitments, 56 field elements, IN THAT ORDER.

⚑ **27 of the 28 are ALREADY on disk here**, because `combine_split_commitments` consumes them:
`COMBINE_XY[41..46]` is `sigma_comm_init = sigma_comm[0..5]`, `COMBINE_XY[26..40]` is
`coefficients_comm[0..14]`, `COMBINE_XY[5..10]` is the six selector commitments
(`step_verifier.ml:583-617`). The 28th, `sigma_comm[6]`, is the one commitment the fold does NOT
carry — `Vector.split m.sigma_comm` hands it to `Common.ft_comm` as `sigma_comm_last`
(`common.ml:243-246`) — and `MinaWrapGroupGate.SIGMA6` is exactly that point, already read off the
devnet blockchain Wrap verifier index for the `ft_comm` rung. So this list, like every other one
here, owns NO literals.

⚠ MEASURED against a SECOND source, 2026-08-02: all 27 agree coordinate-for-coordinate with
`bridge/mina-zkapp/fixtures/mina-devnet-wrap-blockchain-vk.json` (kimchi's own
`devnet_blockchain_verifier_index.json`, 33-byte compressed Pallas points, `x` little-endian in
bytes 0-31 and the "y ≥ p/2" flag in byte 32). That is the independence gate: the aggregation gate's
47 points and o1-labs' published verifier index are two sources that could disagree and do not, so
`SIGMA6` — which only ONE of them carries — is the same key's seventh permutation commitment and
not a stray. -/

/-- The 28 plonk-index commitments in `index_to_field_elements` order: `sigma_comm[0..6]`,
`coefficients_comm[0..14]`, then generic / psm / complete_add / mul / emul / endomul_scalar. -/
def INDEX_XY : List Pt :=
  ((List.range 6).map (fun k => COMBINE_XY.getD (41 + k) (0, 0)))
  ++ [ ((Dregg2.Circuit.Emit.MinaWrapGroupGate.SIGMA6).1,
        (Dregg2.Circuit.Emit.MinaWrapGroupGate.SIGMA6).2.1) ]
  ++ ((List.range 15).map (fun k => COMBINE_XY.getD (26 + k) (0, 0)))
  ++ ((List.range 6).map (fun k => COMBINE_XY.getD (5 + k) (0, 0)))

/-- `sponge_after_index`'s 56 field elements, `Inner_curve.to_field_elements` flattened. -/
def INDEX_WORDS : List Nat := INDEX_XY.flatMap (fun p => [p.1, p.2])

/-- The block's 7 `t_comm` chunks — `receive without t_comm` (`step_verifier.ml:568`) absorbs them
and `Common.ft_comm`'s Horner consumes them. Named here because `KimchiStepMain` #5 is blocked on
that MSM and the DATA is not what blocks it. -/
def T_COMM_XY : List Pt := flat Dregg2.Circuit.Emit.MinaWrapGroupGate.TCHUNKS

/-- ⚑ `sg_old[0]` — the first of `Wrap_hack.Checked.pad_commitments`' two slots
(`step_verifier.ml:536-538`) and the point `combine_split_commitments` STARTS its accumulator at
(`~init`, `:606`). It is `COMBINE_XY`'s own head: the fold list begins at it, which is exactly why it
gets no fold ROUND while still being absorbed. -/
def SG_OLD0_XY : Pt := COMBINE_XY.headD (0, 0)

/-- ⚑ `opening.delta` — `absorb sponge PC delta` (`step_verifier.ml:321`) and the second operand of
`check_bulletproof`'s closing `lhs = Scalar_challenge.endo q c + delta` (`:325-327`). -/
def DELTA_XY : Pt :=
  ((Dregg2.Circuit.Emit.MinaWrapOpeningGate.DELTA).1,
   (Dregg2.Circuit.Emit.MinaWrapOpeningGate.DELTA).2.1)

/-! ## ⚑⚑ THE CLOSING SIDE OF THE SAME OPENING — `sg`, `z₁`, `z₂`

`DELTA_XY` above and `GAMMA_XY`'s fifteen `(L, R)` pairs are two of the four families
`check_bulletproof`'s closing equation reads. **The other two are here**, and they come off the same
object — `MinaWrapOpeningGate`'s `SG` / `Z1` / `Z2`, block 539508's own `opening.{sg, z1, z2}` — so
this module still owns no literals.

`step_verifier.ml:325-337` is the equation, and every operand of it now has a name in THIS module:

    lhs = Scalar_challenge.endo q c + delta                      -- `DELTA_XY`, `GAMMA_XY` inside `q`
    rhs = z₁·(sg + b·u) + z₂·H                                   -- `SG_XY`, `Z1`, `Z2`, `SRS_H_XY`

⚠ ⚑ **AND NAMING THEM HERE DOES NOT MAKE THEM THIS ASSEMBLY'S.** `KimchiStepMain` §19 emits that
equation over ITS OWN transcript's `c`, `u`, `b` and ξ-fold, and those are not block 539508's — three
of three measured apart in `KimchiStepMainPins19`. So `bpCloses` at `(SG_XY, Z1, Z2)` is **false**
there, and §19 still SOLVES its `G`. What this block retires is the diagnosis that used to be written
beside that solve — *"the assembly has no IPA opening to take a real `G` from"* — which was false at
HEAD: the opening is on disk, in a module `KimchiStepMainCore` already imports through this one. What
blocks it is the TRANSCRIPT, not the DATA, and the two are different pieces of work. -/

/-- ⚑ `opening.sg` — the IPA's final `G`. It is `check_bulletproof`'s `challenge_polynomial_commitment`
(`step_verifier.ml:333`, the point `z₁` scales) AND the commitment segment D forwards as the next
step's accumulator (`step_main.ml:525-566`, `step.rs:2848-2857`). ONE object in both roles, which is
why a `G` that closes the opening and a `G` that the chain carries cannot be two different points. -/
def SG_XY : Pt :=
  ((Dregg2.Circuit.Emit.MinaWrapOpeningGate.SG).1,
   (Dregg2.Circuit.Emit.MinaWrapOpeningGate.SG).2.1)

/-- `srs.h` — `Generators.h`, the blinding base `z₂` scales (`step_verifier.ml:336`). -/
def SRS_H_XY : Pt :=
  ((Dregg2.Circuit.Emit.MinaWrapOpeningGate.SRS_H).1,
   (Dregg2.Circuit.Emit.MinaWrapOpeningGate.SRS_H).2.1)

/-- `opening.z1` — the prover's first response scalar. A **Pallas SCALAR**, so it lives mod `qN` and
enters the step circuit as a `Shifted_value.Type2` split, not as a coordinate. -/
def Z1 : Nat := Dregg2.Circuit.Emit.MinaWrapOpeningGate.Z1

/-- `opening.z2` — the second response scalar, likewise mod `qN`. -/
def Z2 : Nat := Dregg2.Circuit.Emit.MinaWrapOpeningGate.Z2

/-- The 15 raw 128-bit prechallenges of `opening.prechallenges` — `bullet_reduce`'s own squeezes,
the challenges `GAMMA_XY`'s pairs are folded at, and the vector `accumulator_check` says `sg` is the
challenge-polynomial commitment OF. -/
def IPA_PRECHALS : List Nat := Dregg2.Circuit.Emit.MinaWrapOpeningGate.IPA_PRECHALS

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

-- ── ⚑ THE PLONK INDEX ─────────────────────────────────────────────────────────────────────────
-- 28 commitments, 56 field elements — `Plonk_verification_key_evals`' own field count
-- (`sigma_comm : Permuts_vec = 7`, `coefficients_comm : Columns_vec = 15`, six selectors).
#guard INDEX_XY.length == 28
#guard INDEX_WORDS.length == 56
#guard T_COMM_XY.length == 7
-- …every one on the Pallas curve in this field, distinct, finite, full-width.
#guard INDEX_XY.all onCurve
#guard T_COMM_XY.all onCurve
#guard (INDEX_XY.map (·.1)).dedup.length == 28
#guard INDEX_XY.all (fun p => p.1 != 0 && p.2 != 0 && p.1 > 2 ^ 200)
-- ⚑ …and the 27 the FOLD also carries are THE SAME POINTS, at the census indices
-- `step_verifier.ml:583-617` gives them. Stated index-by-index rather than as a set, because the
-- ORDER is what `index_to_field_elements` fixes and a permuted list would hash differently.
#guard (List.range 6).all (fun k => INDEX_XY.getD k (0, 0) == COMBINE_XY.getD (41 + k) (0, 0))
#guard (List.range 15).all (fun k =>
  INDEX_XY.getD (7 + k) (0, 0) == COMBINE_XY.getD (26 + k) (0, 0))
#guard (List.range 6).all (fun k =>
  INDEX_XY.getD (22 + k) (0, 0) == COMBINE_XY.getD (5 + k) (0, 0))
-- ⚑ …and the 28th is the one the fold does NOT carry: `sigma_comm[6]` is in no `COMBINE_XY` slot,
-- which is `Vector.split m.sigma_comm`'s own shape (`common.ml:243-246`). A pin that merely said
-- "28 points" would be satisfied by a duplicate; this one says the seventh is genuinely elsewhere.
#guard COMBINE_XY.all (fun p => p != INDEX_XY.getD 6 (0, 0))
#guard INDEX_XY.getD 6 (0, 0)
        == ((Dregg2.Circuit.Emit.MinaWrapGroupGate.SIGMA6).1,
            (Dregg2.Circuit.Emit.MinaWrapGroupGate.SIGMA6).2.1)
-- …and the index commitments are DISJOINT from `bullet_reduce`'s gammas and from the SRS Lagrange
-- constants — three different provenances, no accidental sharing.
#guard INDEX_XY.all (fun p => !(GAMMA_XY.contains p) && !(LAGRANGE_XY.contains p))
-- …and `t_comm` is a fourth: the prover's quotient commitment, in none of the other lists.
#guard T_COMM_XY.all (fun p => !(EVERY.contains p) && !(INDEX_XY.contains p))

/-! ## ⚑⚑ THE OPENING'S CLOSING SIDE, AS NAMED THEOREMS

⚑ `#guard`s above, theorems here, and the asymmetry is deliberate rather than sloppy: the guards are
a baselined block this module is not re-litigating, and every fact ADDED from 2026-08-08 is a named
term (`metatheory/docs/GUARD-DISCIPLINE.md`). All four are kernel `decide` — 255-bit `Nat` arithmetic
is exactly where the kernel still reaches. -/

/-- **`the_openings_points_are_real_and_five_distinct_points`** — `sg`, `delta` and `srs.h` are on
`y² = x³ + 5` over `Fp`, are finite, are full-width, and are distinct from each other AND from
`sg_old[0]` — the point `combine_split_commitments` STARTS its accumulator at.

⚑ **That last leg is the one worth having.** `sg_old[0]` and `sg` are both "the accumulator" in
English — one is the accumulator the previous proof handed in, the other is the accumulator this
proof hands on — and a lane that conflated them would produce an assembly whose `check_bulletproof`
closed against a commitment the fold had already consumed. They are two points and this says so. -/
theorem the_openings_points_are_real_and_five_distinct_points :
    (onCurve SG_XY && onCurve DELTA_XY && onCurve SRS_H_XY
      && [SG_XY, DELTA_XY, SRS_H_XY, SG_OLD0_XY].all (fun p => p.1 != 0 && p.2 != 0)
      && [SG_XY, DELTA_XY, SRS_H_XY, SG_OLD0_XY].all (fun p => p.1 > 2 ^ 200)
      && ([SG_XY, DELTA_XY, SRS_H_XY, SG_OLD0_XY].map (·.1)).dedup.length == 4) = true := by
  decide

/-- **`the_opening_is_a_provenance_the_absorbed_lists_do_not_carry`** — `sg` and `delta` are in NONE
of the four lists this module already had: not a Lagrange constant, not a `combine_split_commitments`
base, not a `bullet_reduce` gamma, not a plonk-index commitment, not a `t_comm` chunk.

⚠ ⚑ **Stated because "we already have the opening" was almost true and would have been wrong.** The
fold consumes `GAMMA_XY` — the opening's `L`/`R` — so a reader can conclude the opening is on disk
and stop. The two points the CLOSING equation needs are not in any absorbed list and were not on this
module's surface until 2026-08-08. -/
theorem the_opening_is_a_provenance_the_absorbed_lists_do_not_carry :
    ([SG_XY, DELTA_XY].all (fun p =>
        !(EVERY.contains p) && !(INDEX_XY.contains p) && !(T_COMM_XY.contains p))
      -- …and the check discriminates: a point that IS in a list is found.
      && EVERY.contains SG_OLD0_XY
      && INDEX_XY.contains (INDEX_XY.getD 6 (0, 0))) = true := by
  decide

/-- **`the_response_scalars_are_pallas_scalars_and_are_not_the_assemblys`** — `z₁`, `z₂` are reduced
non-zero elements of Pallas' SCALAR field `qN`, are distinct, and are full width.

⚑ The last clause is the anti-vacuity leg with a name: `KimchiStepMainCore.BP_Z1_VAL` and
`BP_Z2_VAL` — the two free witnesses §19 actually emits — are `987654321098765432109876543210` and
`555555555555555555555555555555`, decimal repunits under `2^100`. A pin that only said "the scalars
are in range" would be satisfied by those. This says the block's are not shaped like a chosen
numeral, so a later edit that reverts the fixture to a legible constant reds here. -/
theorem the_response_scalars_are_pallas_scalars_and_are_not_the_assemblys :
    (decide (0 < Z1) && decide (Z1 < qN) && decide (0 < Z2) && decide (Z2 < qN)
      && decide (Z1 != Z2)
      && decide (Z1 > 2 ^ 200) && decide (Z2 > 2 ^ 200)) = true := by
  decide

/-- **`the_fifteen_prechallenges_are_the_fifteen_gamma_rounds`** — `opening.prechallenges` has one
entry per `(L, R)` pair, every entry is a non-zero value below `2^128` (`Challenge.length`, so each
round-trips through the two `u64` limbs the wire carries), and no two rounds squeezed the same
challenge.

⚑ `accumulator_check` is the statement that `sg` is `⟨b_poly_coefficients(these), srs.g⟩`; this is
the shape leg of that claim, on the vector, in this module — the arithmetic leg is
`MinaWrapOpeningGate`'s deferred rung 5h and stays deferred. -/
theorem the_fifteen_prechallenges_are_the_fifteen_gamma_rounds :
    (IPA_PRECHALS.length == GAMMA_XY.length / 2
      && IPA_PRECHALS.length == 15
      && IPA_PRECHALS.all (fun c => c != 0 && c < 2 ^ 128)
      && IPA_PRECHALS.dedup.length == 15) = true := by
  decide

#assert_axioms the_openings_points_are_real_and_five_distinct_points
#assert_axioms the_opening_is_a_provenance_the_absorbed_lists_do_not_carry
#assert_axioms the_response_scalars_are_pallas_scalars_and_are_not_the_assemblys
#assert_axioms the_fifteen_prechallenges_are_the_fifteen_gamma_rounds

end Dregg2.Bridge.MinaStepPrevCommitments
