/-
`KimchiStepMain` pins — **§19b: THE BLOCK'S OWN OPENING IS ON DISK, AND IT DOES NOT CLOSE THIS
ASSEMBLY.**

⚑ NAMED THEOREMS, NOT `#guard` (`metatheory/docs/GUARD-DISCIPLINE.md`). This module adds no guard.

The values these are stated about are in `…Fixture`; the emission is in `…Core`; the block's opening
is in `Dregg2.Bridge.MinaStepPrevCommitments`, which `…Core` already imports.

# ⚑⚑ WHAT THIS SECTION RETIRES

`solveG`'s docblock and §18b's verdict both carried the same diagnosis, in the same words:

> *"The assembly has no IPA opening to take a real `G` from."*

**That was false at HEAD.** Mina devnet block 539508's `opening` — the very proof this assembly's
`stepBases` are the commitments of — has been fully extracted since `MinaWrapOpeningGate` landed:
`sg`, `z1`, `z2`, `delta`, the fifteen `(L, R)` pairs, `srs.h`, the fifteen prechallenges. Two of
those families are ALREADY CONSUMED by the emitted rows (`GAMMA_XY` is R4 rounds 46…75; `DELTA_XY`
is the absorbed `delta`), and `MinaStepPrevCommitments` now names the other two on its own surface
(`SG_XY`, `Z1`, `Z2`, `SRS_H_XY`) so that "it is not here" cannot be said again.

**What is actually missing is a TRANSCRIPT, not a datum**, and this section names the three cells
where the two transcripts come apart. That is a different piece of work, with a different owner, and
saying so is the point: an extraction lane cannot close slot 12, and a lane briefed to extract would
have found the data already there and had nothing to report.

# ⚑ THE SHAPE OF THE MISS

`check_bulletproof`'s closing equation (`step_verifier.ml:325-337`) is

    lhs = Scalar_challenge.endo q c + delta        rhs = z₁·(sg + b·u) + z₂·H

and the two sides read **seven** inputs. Measured on the committed shape `shapeStep`:

| input | this assembly | block 539508 | agree |
|---|---|---|---|
| `H` | `GENERATORS_H` | `SRS_H_XY` | ⚑ **YES** |
| the fold's BASES | `stepBases` | `LAGRANGE/COMBINE/GAMMA_XY` | ⚑ **YES**, by construction |
| `delta` | absorbed, unwired | `DELTA_XY` | **YES** as a datum |
| `t = challenge_fq()` | `uSqueezeVal` | `T_FQ` | **NO** |
| `u = group_map t` | `bpUOf` | `U_BASE` | **NO** (a function of the row above) |
| `b` | `bActualOf`, shifted | `B0` | **NO** |
| `(sg, z₁, z₂)` | SOLVED off `lhs` | `SG_XY`, `Z1`, `Z2` | — the thing at issue |

So the assembly holds the block's POINTS and squeezes its own SCALARS, and `lhs` is therefore this
assembly's `c·Q + delta` and not the block's. `bpCloses` at the block's own `(sg, z₁, z₂)` is
**false** below, and it is false for the reason the table gives rather than for an unlocated one.

⚠ ⚑ **AND THE ROUTE THAT LOOKS LIKE AN ESCAPE IS THE SAME WALL.** §19's rows are the `.opening`
rung's, and the rung that is EMITTED and PROVED is `.finalize` — so `equal_g` is not a constraint of
the step proof at all, and one could set `G := SG_XY`, leave `verified` the free witness it already
is at `.finalize`, and move segment D's word 54 onto the block's real accumulator. That closes
nothing: `messages_for_next_step_proof.challenge_polynomial_commitments[0]` on the wire is the WRAP
proof's kimchi recursion-slot commitment, which kimchi forces to `commit(b_poly(chals))` over the
slot's OWN challenges — and those challenges are tied, since 2026-08-06, to the step statement's
published words (`step_statement_prechallenges`, the tie slot 11 rests on). For that commitment to be
`SG_XY` the step circuit's published bulletproof challenges would have to BE block 539508's fifteen.
Which is the transcript again. **Every route to slot 12 terminates at the same place**, and the last
theorem here is the arity fact that decides which of them is even expressible.
-/
import Dregg2.Circuit.Emit.KimchiStepMainFixture

namespace Dregg2.Circuit.Emit.KimchiStepMain

open Dregg2.Circuit.Emit.KimchiComposeStepFragment (jOf onCurveA)
open Dregg2.Bridge.MinaStepPrevCommitments (SG_XY SRS_H_XY DELTA_XY Z1 Z2 IPA_PRECHALS)
open Dregg2.Circuit.Emit.MinaWrapOpeningGate (T_FQ B0 U_BASE)

set_option autoImplicit false
set_option maxRecDepth 100000

/-- `u_base`, affine — `MinaWrapOpeningGate` carries it projective at `z = 1`. -/
def U_BASE_A : Nat × Nat := (U_BASE.1, U_BASE.2.1)

/-- ⚑⚑ **(a) THE BLOCK'S OWN OPENING DOES NOT CLOSE THIS ASSEMBLY'S `check_bulletproof` — AND THE
SOLVE DOES.**

Both polarities in one statement, because either alone is worthless: a `false` on its own could be a
broken `bpCloses`, and a `true` on its own is what §17 already measured. Stated at `shapeStep`, the
COMMITTED shape — slot 12 is about that assembly and not about the smoke one.

⚑ **`H` is pinned equal in the same breath.** `GENERATORS_H` was measured off `SRS::<Pallas>::create`
and `SRS_H_XY` is read out of the block's own opening object; if those had disagreed, the `false`
below would have been about the wrong thing entirely and would have read as evidence for a much
larger gap than the one there is. -/
theorem the_blocks_own_opening_does_not_close_this_assemblys_transcript :
    (-- the block's `(sg, z₁, z₂)`, on this assembly's `lhs`: REFUSED.
     (bpCloses (bpUOf tStep) GENERATORS_H (bpLhsOf tStep) (jOf SG_XY) (bpBOf tStep) Z1 Z2) == false
     -- …and the SOLVE, on the same `lhs`: accepted. So the predicate discriminates.
     && bpCloses (bpUOf tStep) GENERATORS_H (bpLhsOf tStep) (jOf tStep.gXY) (bpBOf tStep)
          BP_Z1_VAL BP_Z2_VAL
     -- …and it is not `H` that differs: the two sources of `srs.h` are one point.
     && GENERATORS_H == SRS_H_XY
     -- …and `sg` is a real point of the field the ladder runs in, so "it was refused because the
     -- base is not on the curve" is excluded.
     && onCurveA SG_XY
     -- …and it is not the point the assembly emits, which is what makes the first leg a MISS rather
     -- than a tautology about two names for one number.
     && SG_XY != tStep.gXY) = true := by
  native_decide

#assert_compiled the_blocks_own_opening_does_not_close_this_assemblys_transcript

/-- ⚑⚑ **(b) THE THREE CELLS WHERE THE TWO TRANSCRIPTS COME APART, NAMED.**

`t` is `challenge_fq()`, the FULL squeeze that `group_map` is applied to; `u` is that map's output;
`b` is `advice.b`, R8's statement word. Every other operand of the closing equation is a point this
assembly takes from the block. So the miss in (a) is located at three cells and not "somewhere in the
sponge" — which is the difference between a next lane having a target and having a search.

⚠ `u` is a FUNCTION of `t`, so the second leg is not independent evidence; it is here because `u` is
what the ladder actually consumes, and a repair that moved `t` without moving `u` would be a repair
of the wrong cell.

⚑ **AND THE POSITIVE HALF IS IN THE SAME THEOREM**, because a section that only reported disagreement
would read as "the assembly has nothing of the block's" — which is the false diagnosis this module
exists to retire. `delta` and the thirty `bullet_reduce` gammas ARE the block's, exactly. -/
theorem the_two_transcripts_differ_at_t_and_u_and_b_and_nowhere_in_the_points :
    (-- ── the three that differ ──
     uSqueezeVal shapeStep tStep.sp != T_FQ
     && bpUOf tStep != U_BASE_A
     && bpBOf tStep != B0
     -- ── and what does NOT differ: the opening's own geometry ──
     && DELTA_XY == ((Dregg2.Circuit.Emit.MinaWrapOpeningGate.DELTA).1,
                     (Dregg2.Circuit.Emit.MinaWrapOpeningGate.DELTA).2.1)
     && Dregg2.Bridge.MinaStepPrevCommitments.GAMMA_XY.length == 30
     && IPA_PRECHALS.length == 15
     -- …and `t` is a full-width squeeze on both sides, so the miss is a VALUE miss and not a width
     -- one — a truncated `t` would be a different (and much cheaper) defect.
     && decide (uSqueezeVal shapeStep tStep.sp > 2 ^ 200)
     && decide (T_FQ > 2 ^ 200)) = true := by
  native_decide

#assert_compiled the_two_transcripts_differ_at_t_and_u_and_b_and_nowhere_in_the_points

/-- ⚑⚑ **(c) THE PUBLISHED STATEMENT CARRIES FIFTEEN OF SEGMENT D'S SIXTEEN, AND THE SIXTEENTH IS
`uChal 0`.**

Segment D absorbs `bRounds = 16` lifted challenges (`§18b`'s cone, family four). The marshaller's
`step_pre` — the step proof's own kimchi recursion prechallenges, and therefore the wire's
`messages_for_next_step_proof.old_bulletproof_challenges` — is also sixteen wide. Making the second
be the first is the half of slot 12 that needs no new arithmetic, and it needs the sixteen values to
be READABLE from the emitted artifact, the way `step_statement_prechallenges` reads the wrap side's
fifteen out of `public_input`.

**Fifteen of them are readable, at entries 48…62** — `32·1 + 16 + j`, the second per-proof block's
`deferred_values.bulletproof_challenges` — and they are `uChal 1 … uChal 15`, raw, below `2^128`, so
they drop into `[u64; 2]` unchanged. **`uChal 0` is published NOWHERE**, in raw or lifted form. So
`step_pre` cannot be an extraction at sixteen today: either the statement grows a word or the
sixteenth travels out of band, and that is a decision about the STATEMENT, not about the marshaller.

⚠ **The lifted values are in no published entry either**, which is the leg that says the wire must
carry PRECHALLENGES and let `ScalarChallenge::limbs_to_field` do the lift — as `extract_bulletproof`
(`util.rs:35-56`) in fact does. A `step_pre` filled with lifted values would be a 255-bit number in a
128-bit wire slot. -/
theorem the_published_statement_carries_fifteen_of_segment_ds_sixteen :
    (let pub := stepPublic tStep
     let raw : Nat → Nat := fun k => chalOf shapeStep tStep.sp (shapeStep.uChal k)
     let lif : Nat → Nat := fun k => liftOf shapeStep tStep.sp (shapeStep.uChal k)
     -- (1) entries 48…62 ARE `uChal 1 … uChal 15`, in order.
     (List.range 15).all (fun j => pub.getD (48 + j) 0 == (raw (j + 1) : Int))
     -- (2) …and all sixteen raw prechallenges fit the wire's two `u64` limbs.
     && (List.range 16).all (fun k => raw k < 2 ^ 128 && raw k != 0)
     -- (3) ⚑ …but `uChal 0` is in NO published entry — the one that cannot be read out.
     && (pub.contains (raw 0 : Int)) == false
     -- (4) …and NO lifted value is published, so the wire slot is a prechallenge slot.
     && (List.range 16).all (fun k => (pub.contains (lif k : Int)) == false)
     -- (5) …and the lift is not the identity here, or (4) would be (3) sixteen times over.
     && (List.range 16).all (fun k => lif k != raw k)
     -- (6) the shape the whole claim is about.
     && pub.length == 67 && shapeStep.bRounds == 16) = true := by
  native_decide

#assert_compiled the_published_statement_carries_fifteen_of_segment_ds_sixteen

end Dregg2.Circuit.Emit.KimchiStepMain
