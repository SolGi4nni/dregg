/-
# `Dregg2.Circuit.Emit.MinaWrapClosingAir` — ⚑⚑ THE IPA **CLOSING** CHECK, IN A CIRCUIT, WITH `sg`
GONE FROM IT.

## ⚑ SAY THE SUBSTRATE OUT LOUD (HOUSE LAW #1, at constraint #1)

**This is Lean-authored AIR.** Every leg, every column index, the routing tuple, the declared
manifest and all three emitted descriptors are authored here and go through
`EffectLower.lowerAir` of an `EffectAirIR.EffectAir`. There is no hand-written `VmConstraint2` in
this file and none in the Rust that consumes it: Rust parses the emitted bytes, fills trace CELLS,
proves, and folds.

## WHAT WAS OPEN, AND IT WAS THE LAST THING dregg TOOK ON TRUST ABOUT A MINA PROOF

`MinaWrapOpeningGate` (rung 5f) proves the IPA **opening relation (B)** on Mina devnet block
539508 — in the kernel, over the real group law, at the block's own transcript challenges. And
`MinaWrapVerifierAir.opening_is_vacuous_when_sg_is_free` is a theorem that (B) **refutes nothing**
while `sg` is a free witness: `sg` enters `rhs = z₁·(G + b·U) + z₂·H` linearly with a unit
coefficient, so the prover picks `sg := z₁⁻¹·(c·Q + delta − z₁·b₀·U − z₂·H)` and the check passes
at EVERY value of everything else. `pinned_sg_makes_the_opening_refute` is the pole that keeps that
from being a tautology.

`MinaAccumulatorAir` put the **STEP-side** accumulator check (`C == ⟨s(u⃗), srs_vesta.g⟩`) in a
circuit. The **closing group equation had no AIR at all** — `MinaWrapGroupGate` /
`MinaWrapOpeningGate` are value-layer `decide`. Nothing connected the two.

## ⚑ WHAT THE RELATION REQUIRES, READ AT SOURCE — and both halves are quoted

* `src/lib/pickles/wrap_verifier.ml`, `check_bulletproof` at **`:383`**; the equation is the
  comment at **`:422`** — *`(* c Q + delta = z1 (G + b U) + z2 H *)`* — with `lhs = endo q c +
  delta` (`:423-426`) and `rhs = z_1·(challenge_polynomial_commitment + b·U) + z_2·H`
  (`:427-435`). ⚠ `challenge_polynomial_commitment` (= `sg`), `z_1` and `z_2` arrive as fields of
  the `openings_proof` record: **free in the circuit, and that is FAITHFUL to upstream.** The gap
  was never that Mina fails to bind `sg`; it is that Mina binds it SOMEWHERE ELSE and dregg
  bound it nowhere.

  ⚠ **THESE FOUR LINE NUMBERS WERE WRONG UNTIL 2026-08-08 AND ARE FIXED FORWARD, NOT ANNOTATED.**
  This block cited `:564` / `:600-613`. In the checkout every other citation in this tree resolves
  against — `wrap_verifier.ml:395` is `Other_field.Packed.absorb_shifted` (`KimchiStepWrapChain`
  §4) and `:617` is the `x_hat` absorb (`EmitWrapMainJson:205`) — `:564` is inside the packed
  public-input MSM and `:600` is a `List.foldi` arm. A citation that resolves to the wrong line is
  the same defect class as a theorem about the wrong object, and it was found by running
  `git grep` on the numbers rather than on the prose.

* `poly-commitment/src/ipa.rs`, `SRS::verify`. Two independent randomisers are sampled at
  **`:356-357`** (`rand_base`, `sg_rand_base`) and the two statements are folded into ONE terminal
  MSM. The `sg` base carries scalar **`neg_rand_base_i * opening.z1 - sg_rand_base_i`**
  (**`:410-411`**), and the SRS bases carry `+ sg_rand_base_i · s_i` (**`:413-425`**), under the
  comment *"we also add `-sg_rand_base_i * G` to check correctness of sg"* (`:409`). That is the
  leg this file brings in. Upstream runs the same relation out-of-circuit on the Step side as
  `batch_dlog_accumulator_check`; on the Tock/Wrap side it is folded into `SRS::verify` itself.

* ⚑⚑ **AND WHERE `delta` ENTERS THE TRANSCRIPT — the citation §6 and §7 are about.** Two lines,
  adjacent, in both implementations, and the ORDER is the whole content:

  ```rust
  // poly-commitment/src/ipa.rs:382-383   (SRS::verify, the VERIFIER)
  sponge.absorb_g(&[opening.delta]);
  let c = ScalarChallenge::new(sponge.challenge()).to_field(&endo_r);
  ```
  ```rust
  // poly-commitment/src/ipa.rs:1047-1048 (SRS::open, the PROVER — the same pair)
  sponge.absorb_g(&[delta]);
  let c = ScalarChallenge::new(sponge.challenge()).to_field(&endo_r);
  ```
  ```ocaml
  (* src/lib/pickles/wrap_verifier.ml:420-421, INSIDE check_bulletproof *)
  absorb sponge PC delta ;
  let c = squeeze_scalar sponge in
  ```

  The absorb schedule that reaches those two lines is, in order: `absorb_fr(shift_scalar(cip))`
  (`ipa.rs:371`), `u_base := group_map(challenge_fq())` (`:373-377`),
  `OpeningProof::challenges` (`:379` → `:1266-1274`, which absorbs `L` then `R` and squeezes a
  prechallenge, fifteen times), **then `delta`, then `c`.** `absorb_g` of ONE Pallas point is a
  rate-2 absorb of its two `Fp` coordinates — i.e. exactly `perm(state + [x, y, 0])`, which is
  what `dregg-pasta-fp-absorb::v1` computes and what §7 binds against.

  ⚑ **`c` IS SQUEEZED FROM A SPONGE THAT ALREADY CONTAINS `delta`.** That is the entire reason a
  prover cannot pick `delta` after seeing `c`, and it is a FIAT–SHAMIR fact, not an algebraic one:
  no rearrangement of the closing equation can express it. `MinaWrapOpeningGate`'s
  `delta_leaves_the_prechallenges_alone` and `delta_moves_c_prime` are that ordering measured on
  block 539508's own transcript — at the VALUE layer, by `native_decide`, not in any AIR.

## ⚑⚑ THE MOVE, AND IT IS NOT A WEAKENING — §2 IS THE THEOREM

Read kimchi's combined residual as a function of the fold coefficient `ρ = sg_rand_base` at
`rand_base = 1`:

```text
    combined ρ  =  (c·Q + delta − z₁·sg − z₁b₀·U − z₂·H)   +   ρ·(⟨s,G⟩ − sg)
```

the first bracket is (B), the second is (A). **At `ρ = −z₁` the `sg` terms cancel exactly** —
`−z₁·sg` from (B) and `+z₁·sg` from (A) — and what is left is

```text
    combined (−z₁)  =  c·Q + delta − z₁·⟨s,G⟩ − z₁b₀·U − z₂·H
```

in which **`sg` does not occur at all.** `the_combined_check_is_constant_in_sg` states exactly
that, and `the_eliminated_check_is_the_conjunction` states that this is not a weakening: the
eliminated residual vanishes **iff** there EXISTS an `sg` satisfying (A) and (B) together. So the
elimination is the substitution `sg := ⟨s, srs.g⟩` that statement (A) licenses, and it is exact —
where upstream's random `ρ` carries a Schwartz–Zippel error term, this choice carries none.

⚑ And `the_eliminated_check_has_no_surjective_sg_map` is the direct refutation of the vacuity: the
hypothesis `opening_is_vacuous_when_sg_is_free` needs is that the `sg`-side map be SURJECTIVE. On
the eliminated check that map is CONSTANT, and a constant map into a type with two distinct
elements is not surjective. The vacuity theorem does not apply — not because its proof is wrong,
but because its premise is false here.

## THE AIR — the Pallas mirror of the accumulator's, and everything curve-free is REUSED

`sg` is a **Pallas** point (`opening.sg` of the Wrap/Tock proof), so coordinates reduce at `pN`
(Pallas base) and scalars at `qN` (Pallas scalar). `MinaAccumulatorAir` is the VESTA instance of
the same construction; this file is the Pallas one, and it imports rather than re-authors every leg
family that carries no prime: `inPinLegs`, `outPinLegs`, `dischargeLegs`, `ridxStartLeg`,
`ridxThreadLeg`, `addendLookupLeg`, `routedTables`, `coordLimb`, `declAddend`, `declaredChain`,
`Discharged`, `traceOf`. What is new is the row (`pallasCompleteAddSoundLegs`, so the gates are at
`pLimb`), the forcing chain at `pN`, and the MANIFEST.

Three descriptors, each pair an OLD-ADMITS / NEW-REJECTS exhibit:

* `dregg-mina-wrap-closing-seg::v1` — a SEGMENT of the closing chain, publishing its two
  endpoints. Says nothing about vanishing, because an intermediate segment must not.
* `dregg-mina-wrap-closing-final::v1` — the segment PLUS `MinaAccumulatorAir.dischargeLegs`: 64
  `.last` window gates forcing every limb of the terminal `X` and `Z` blocks to zero. That is the
  closing check.
* ⚑⚑ `dregg-mina-wrap-closing-srs::v1` — the SAME algebra over a manifest that is not a parameter:
  `closingAddends`, a TOTAL FUNCTION of the SRS generator list, the 15 endo-lifted IPA challenges,
  `z₁`, `z₂`, `b₀`, and the three group elements `delta`, `U`, `H`. ⚑ **`sg` IS NOT ONE OF ITS
  ARGUMENTS.** There is no path by which the emitter supplies it, and no slot in the chain for a
  prover to choose it.

The accumulator ENTERING row 0 is `c·Q`, published at `PI[0..95]` at full 256-bit width,
elementwise; the accumulator LEAVING the last row is published at `PI[96..191]` and forced to the
canonical point at infinity. A fold node `cb.connect`s a left child's outgoing 96 limbs to a right
child's incoming ones — the same shape `MinaAccumulatorAir` folds on, so the two chains compose
with one adapter.

## What is proved here

* `closing_combined_is_kimchis_fold` — the residual this file discharges IS `ipa.rs`'s combined
  scalar assignment at `rand_base = 1`, stated as an algebraic identity rather than asserted.
* ⚑⚑ `the_combined_check_is_constant_in_sg` / `the_eliminated_check_is_the_conjunction` /
  `the_eliminated_check_has_no_surjective_sg_map` — §2, the elimination and why it is exact.
* `the_eliminated_check_still_refutes` / `the_eliminated_check_is_satisfiable` — both poles, so §2
  is neither vacuous nor unsatisfiable.
* `closingSegAir_mainRailOk` / `closingFinalAir_mainRailOk` / `closingRoutedAir_mainRailOk` — the
  compiler accepts all three blocks.
* the widths, the PI counts, the constraint counts, and `the_closing_discharge_is_sixty_four_last_
  row_gates` — the selector census, so a `.last → .all` re-scope moves a number.
* ⚑ `closing_discharge_forced` — rows satisfied at `pLimb` + threads held + the discharge gates
  satisfied force the `n+1`-fold RCB chain of the trace's own addends, from the accumulator
  published at `PI[0..95]`, to be the point at infinity **mod the real Pallas-base prime**.
* ⚑⚑ `declAddend_of_closingAddends` — the value the chain folds at index `r` IS the declared
  addend of `closingAddends`, over ℤ with no canonicality envelope.
* ⚑⚑ `the_closing_manifest_carries_no_sg_slot` — the manifest's length is `3 + n`, one slot per
  non-`sg` term of the eliminated residual, and its three head entries are `delta`, `−(z₁b₀)·U`,
  `−z₂·H`. The `sg` slot of the un-eliminated relation is ABSENT rather than zeroed.

## ⚠ WHAT THIS DOES **NOT** ESTABLISH — read before quoting any of it

1. ⚑ **The scaling runs in the EMITTER, not in the AIR.** `closingAddends` computes `−z₁·s_r·G_r`
   as a Lean function at emission time; nothing in this descriptor re-derives it in-circuit. This
   is `MinaAccumulatorAir` §10's trichotomy verbatim — CIRCUIT (the deferred MSM,
   `PastaMsmBucketed.fused_at_step` at 1 474 800 complete additions on the unsound row), EMITTER
   (here), or NOWHERE — and there is no fourth place. What the elimination buys is that the object
   an emitter is trusted for no longer INCLUDES `sg`: it is a generator list, 15 field elements,
   three scalars and three points.
2. **`c·Q` enters as the published accumulator `PI[0..95]`, not as a derived value.** It is not
   free — the chain forces it to be the negation of the declared sum — but whether the `c·Q` a node
   compares against is the block's is a CONSUMER obligation, exactly `MinaAccumulatorAir`'s
   residual 1. Nothing here ties the chain to a Mina head.
3. ⚑⚑ **AND HERE IS WHERE THE VACUITY MOVED TO, SAID PLAINLY RATHER THAN LEFT TO BE FOUND.**
   Nothing here binds `delta`, `c`, `u⃗`, `z₁`, `z₂` or `b₀` to a transcript. `delta` is a DECLARED
   manifest slot and a prover-supplied group element, so a prover who may choose it freely can
   satisfy this check at every value of everything else — by `deltaFor`, which is the emitter's own
   function. **That is a free witness, and it is the same SHAPE as the one this file retires.**

   It is not the same HOLE, and the difference is the whole point of the file. `sg`'s binding is an
   ALGEBRAIC relation to the SRS (`sg = ⟨s, srs.g⟩`) which lives inside the closing equation and
   which nothing in dregg discharged; that one is closed here, by elimination. `delta`'s binding is
   a FIAT–SHAMIR relation — `SRS::verify` absorbs `delta` into the sponge before squeezing `c` — and
   it lives in the transcript.

   ⚑⚑ **UPDATED 2026-08-08 — §6 MEASURES IT AND §7 WELDS IT, AND THE RESIDUE MOVED RATHER THAN
   CLOSED.** This paragraph used to end *"the closing check in this AIR refutes a free `sg` and does
   NOT refute a free `delta`."* That is still true of `-seg`/`-final`/`-srs` and it is now an
   EQUATION rather than a sentence: `the_delta_shift_is_invisible` proves the residual sees `acc₀`
   and `delta` only through their SUM, so the forgery is a one-parameter family and every member is
   one addition away. `the_whole_shift_orbit_is_admitted` exhibits it at ℤ and
   `circuit/tests/mina_wrap_closing_air_proves.rs::the_transcript_ordered_chain_and_its_shift_both_
   prove` exhibits it as TWO REAL STARK PROOFS at Pallas.

   `dregg-mina-wrap-closing-fs::v1` (§7) refuses it: `delta`'s limbs are `.first`-pinned to the pair
   a `dregg-pasta-fp-absorb::v1` sub-proof absorbed, and the bind's commitment IS that program's
   192-lane public-input vector — no digest, no birthday bound. Both polarities run in release
   (`the_welded_air_admits_the_transcripts_own_delta` /
   `a_delta_that_closes_the_equation_but_is_not_the_transcripts_is_refused`, the second refused by
   `OodEvaluationMismatch` on a trace whose addend bus BALANCES, whose chain VANISHES, whose limbs
   are in-width and whose point is affine — so the pin is what spoke).

   ⚠ **AND SAY WHERE IT WENT.** `TR_IN` is a descriptor constant and `TR_OUT` a published witness,
   so the weld refuses a shifted `delta` against a FIXED descriptor and does not refuse a
   re-emission at a fresh `(TR_IN, delta, TR_OUT)` triple. **The residue is `c` — ONE published
   field element a consumer recomputes from `PI[192..223]`, against `MinaAccumulatorAir` residual
   1's `c·Q`.** That is a narrowing, not a closure: `delta` was a free GROUP ELEMENT chosen last,
   after seeing everything; `c` is a scalar the descriptor now publishes. Do not write "`delta` is
   bound."
4. **P10, the opening-soundness floor, is untouched.** That a prover which passes the closing check
   must KNOW an opening is the IPA/dlog extraction argument, undischarged here and everywhere in
   this stack. This file changes what the CHECK is, never what passing it proves.
5. **The routing half is `MinaAccumulatorAir` §8's and is NOT re-derived here at the Pallas
   descriptor.** §5 below emits the routed block and `decide`s its shape; the value-level bridge
   from a balanced lookup to "row `i`'s addend is the declared one" is stated there over
   `accRoutedDesc` and its proof is keyed to that object. Porting it is mechanical
   (`only_the_routing_leg_targets_the_addend_table` is a `decide` on this file's own constraint
   list, and every lemma after it is prime-free) and it is **undone work, not a theorem of the
   model**. Until it lands, `-srs` here has the standing of `-final` plus a declared manifest.

## Axiom hygiene

`#assert_axioms`-clean; no `sorry`/`admit`/`native_decide`; zero `#guard`s. NEW file, imports
read-only; NOT imported by the `Dregg2` root, per house practice for gates. Import line:
`import Dregg2.Circuit.Emit.MinaWrapClosingAir`
-/
import Dregg2.Circuit.Emit.MinaAccumulatorAir
import Dregg2.Circuit.Emit.MinaWrapVerifierSpongeFp

namespace Dregg2.Circuit.Emit.MinaWrapClosingAir

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 WindowExpr VmConstraint2)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg)
open Dregg2.Circuit.TableAirIR (RowSel)
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaFieldSound (SB SK sVal pLimb qLimb)
open Dregg2.Circuit.Emit.PastaCurve (CZm)
open Dregg2.Circuit.Emit.PastaCurveComplete (curveB3 rcbAddM)
open Dregg2.Circuit.Emit.PastaCurveSound
open Dregg2.Circuit.Emit.PastaLadderThread
open Dregg2.Circuit.Emit.MinaAccumulatorAir
  (ACC_IN_PI ACC_OUT_PI ACC_PI_COUNT inPinLegs outPinLegs dischargeLegs
   Pt3 coordLimb RIDX ROUTED_WIDTH ridxStartLeg ridxThreadLeg addendTuple addendLookupLeg
   routedTables Discharged sVal_eq_zero discharged_is_the_identity
   declVal declAddend declaredChain ptZ declAddend_of_getD bPolyCoeff)

set_option autoImplicit false
set_option maxRecDepth 40000

/-! ## §1 — ⚑ THE RELATION, AS AN ALGEBRAIC OBJECT.

Everything in this section is over an arbitrary `[CommRing F] [AddCommGroup A] [Module F A]`, so
nothing depends on Pasta, on a coordinate system or on the RCB formula. That is deliberate: the
elimination is a fact about the SHAPE of kimchi's fold, and stating it at the Pasta instance would
make it look like a property of this curve.

`wrap_verifier.ml:600`'s `c Q + delta = z1 (G + b U) + z2 H` moved to one side, with `G := sg`. -/

section Abstract

variable {F : Type} [CommRing F] {A : Type} [AddCommGroup A] [Module F A]

/-- ⚑ **STATEMENT (B), THE OPENING RELATION**, as a residual that the verifier requires to vanish.
`sg` is `openings_proof.challenge_polynomial_commitment` — a witness the prover supplies. -/
def closingResidual (c z1 z2 b0 : F) (Q delta U H sg : A) : A :=
  c • Q + delta - z1 • sg - (z1 * b0) • U - z2 • H

/-- ⚑ **STATEMENT (A), THE `sg` LEG**, likewise. `S` stands for `⟨s(u⃗), srs.g⟩` — the terminal MSM
over the `2^15` Wrap SRS generators. -/
def sgLegResidual (S sg : A) : A := S - sg

/-- ⚑⚑ **KIMCHI'S COMBINED RESIDUAL**, at `rand_base = 1` and `sg_rand_base = ρ`. This is
`ipa.rs:404-425` read as one group element rather than as a scalar array. -/
def combinedResidual (c z1 z2 b0 ρ : F) (Q delta U H sg S : A) : A :=
  closingResidual c z1 z2 b0 Q delta U H sg + ρ • sgLegResidual S sg

/-- ⚑ **THE `sg` BASE CARRIES `−(z₁ + ρ)`, WHICH IS `ipa.rs:411` AT `rand_base_i = 1`.**
`scalars.push(neg_rand_base_i * opening.z1 - sg_rand_base_i)` is `−(1·z₁) − ρ`; this states the
combined residual really does group that way, so the identification of `ρ` with `sg_rand_base` is
an equation rather than a comment. -/
theorem closing_combined_is_kimchis_fold (c z1 z2 b0 ρ : F) (Q delta U H sg S : A) :
    combinedResidual c z1 z2 b0 ρ Q delta U H sg S
      = c • Q + delta - (z1 * b0) • U - z2 • H + ρ • S + (-(z1 + ρ)) • sg := by
  unfold combinedResidual closingResidual sgLegResidual
  rw [smul_sub, neg_smul, add_smul]
  abel

/-! ### §1b — ⚑⚑ THE ELIMINATION. -/

/-- ⚑⚑ **AT `ρ = −z₁` THE CHECK DOES NOT MENTION `sg`.** Two arbitrary `sg` values, one residual.
This is the theorem that removes the free witness: there is no `sg`-side map left to be surjective,
because the map is constant. -/
theorem the_combined_check_is_constant_in_sg (c z1 z2 b0 : F) (Q delta U H S sg sg' : A) :
    combinedResidual c z1 z2 b0 (-z1) Q delta U H sg S
      = combinedResidual c z1 z2 b0 (-z1) Q delta U H sg' S := by
  rw [closing_combined_is_kimchis_fold, closing_combined_is_kimchis_fold]
  simp

/-- ⚑ **AND WHAT IT IS.** The eliminated residual is the opening relation with `sg` REPLACED by
`⟨s, srs.g⟩` — i.e. the substitution statement (A) licenses, performed rather than assumed. -/
theorem the_eliminated_check_is_the_substituted_opening (c z1 z2 b0 : F) (Q delta U H S sg : A) :
    combinedResidual c z1 z2 b0 (-z1) Q delta U H sg S
      = closingResidual c z1 z2 b0 Q delta U H S := by
  rw [closing_combined_is_kimchis_fold]
  have hz : (-(z1 + -z1) : F) = 0 := by ring
  rw [hz, zero_smul, add_zero]
  unfold closingResidual
  rw [neg_smul]
  abel

/-- ⚑⚑⚑ **THE ELIMINATION IS EXACT — IT IS THE CONJUNCTION, NOT A RELAXATION.**

The eliminated residual vanishes **iff** there exists an `sg` satisfying (A) and (B) TOGETHER. So
nothing is given up by dropping the variable: a prover who could pass the eliminated check can
exhibit the `sg` (namely `S`), and a prover who passes (A) ∧ (B) passes this.

⚠ Read against upstream: `SRS::verify` folds with a RANDOM `ρ`, whose soundness is statistical
(`PastaIpaDeferral.one_scalar_fold_is_refutable` exhibits two false claims whose single-scalar
batch vanishes). This choice of `ρ` is not a random fold at all — it is an exact elimination, and
it carries no error term. -/
theorem the_eliminated_check_is_the_conjunction (c z1 z2 b0 : F) (Q delta U H S : A) :
    combinedResidual c z1 z2 b0 (-z1) Q delta U H S S = 0
      ↔ ∃ sg, sgLegResidual S sg = 0 ∧ closingResidual c z1 z2 b0 Q delta U H sg = 0 := by
  rw [the_eliminated_check_is_the_substituted_opening]
  constructor
  · intro h
    exact ⟨S, by simp [sgLegResidual], h⟩
  · rintro ⟨sg, hA, hB⟩
    have : sg = S := by
      have := sub_eq_zero.mp hA
      exact this.symm
    rwa [this] at hB

/-- ⚑⚑ **THE VACUITY PREMISE, REFUTED.**

`MinaWrapVerifierAir.opening_is_vacuous_when_sg_is_free` needs the `sg`-side map to be SURJECTIVE —
`sg_side_is_surjective` discharges that hypothesis for the UN-eliminated check, where `sg` enters
linearly with a unit coefficient. On the eliminated check the map is constant, so it hits at most
one value and a type with two distinct elements defeats it.

⚠ This does not say the vacuity theorem is wrong. It says its premise does not hold of this
object, which is the only honest way to retire it. -/
theorem the_eliminated_check_has_no_surjective_sg_map
    (c z1 z2 b0 : F) (Q delta U H S : A) (a b : A) (hab : a ≠ b) :
    ¬ Function.Surjective
        (fun sg : A => combinedResidual c z1 z2 b0 (-z1) Q delta U H sg S) := by
  intro hsurj
  obtain ⟨sa, hsa⟩ := hsurj a
  obtain ⟨sb, hsb⟩ := hsurj b
  exact hab (hsa.symm.trans
    ((the_combined_check_is_constant_in_sg c z1 z2 b0 Q delta U H S sa sb).trans hsb))

end Abstract

/-! ### §1c — ⚑ BOTH POLES, AT ℤ, SO §1b IS NEITHER VACUOUS NOR UNSATISFIABLE.

`feedback-prove-the-floor-false`: a floor must be SATISFIABLE and REFUTABLE. A constant map is
trivially non-surjective, so on its own §1b would be compatible with the eliminated check being the
constant `0` — which would accept everything and be a worse vacuity than the one it retires. These
two exhibits at `F = A = ℤ` (scalar action is multiplication) say it is not. -/

/-- The eliminated residual at `F = A = ℤ`, written out so both poles are one `def` apart. `z₁ = 3`
so the elimination is not being exercised at the degenerate `z₁ = 0`, where `−z₁·sg` would drop out
for a reason that has nothing to do with §1b. -/
def zPole (delta sg : ℤ) : ℤ := combinedResidual (F := ℤ) (A := ℤ) 2 3 5 7 (-3) 11 delta 13 17 sg 19

/-- ⚑ **IT REFUTES.** So the check can say NO — a constant-in-`sg` map that were also constantly
`0` would accept everything and be a worse vacuity than the one §1b retires. -/
theorem the_eliminated_check_still_refutes : zPole 1 7 ≠ 0 := by
  simp [zPole, combinedResidual, closingResidual, sgLegResidual]

/-- …and it is SATISFIABLE: one value of `delta` makes it vanish, so the refusal is about the value
and not about the descriptor accepting nothing. -/
theorem the_eliminated_check_is_satisfiable : zPole 393 7 = 0 := by
  simp [zPole, combinedResidual, closingResidual, sgLegResidual]

/-- ⚑ **AND THE FREE `sg` MOVES NEITHER POLE** — `the_combined_check_is_constant_in_sg` made
concrete, at the same numbers the two poles are separated by. -/
theorem the_free_sg_moves_neither_pole :
    zPole 1 7 = zPole 1 99 ∧ zPole 393 7 = zPole 393 99 := by
  refine ⟨?_, ?_⟩ <;>
    simp [zPole, combinedResidual, closingResidual, sgLegResidual]

/-! ## §2 — THE THREE AIRS AND THE THREE DESCRIPTORS, AT PALLAS.

`MinaAccumulatorAir.accSegAir` is this block at `vestaCompleteAddSoundLegs`. `sg` and the Wrap SRS
generators are PALLAS points, so the row here is `pallasCompleteAddSoundLegs` — the same 4 476
constraints, at `pLimb` instead of `qLimb`. Every other leg family is imported unchanged, because
none of them mentions a prime. -/

/-- **A SEGMENT of the closing chain.** `PastaLadderThread.pallasThreadAir` — the sound Pallas RCB
row with the 96 `.transition` accumulator threads — plus the two published endpoints. -/
def closingSegAir : EffectAir :=
  { tables := rcbTables
  , legs := inputLimbLegs
      ++ (pallasCompleteAddSoundLegs ACC_X ACC_Y ACC_Z ADD_X ADD_Y ADD_Z IN_BASE).1
      ++ threadLegs ++ inPinLegs ++ outPinLegs }

/-- ⚑ **THE FINAL SEGMENT** — the same block, plus the 64 `.last` discharge gates. -/
def closingFinalAir : EffectAir :=
  { tables := rcbTables
  , legs := inputLimbLegs
      ++ (pallasCompleteAddSoundLegs ACC_X ACC_Y ACC_Z ADD_X ADD_Y ADD_Z IN_BASE).1
      ++ threadLegs ++ inPinLegs ++ outPinLegs ++ dischargeLegs }

/-- ⚑ **THE SEGMENT'S LEGS ARE A PREFIX OF THE FINAL'S.** Every forcing statement about the segment
applies to the final block unchanged — the discharge APPENDS, it does not re-author. -/
theorem closingFinalAir_extends_closingSegAir : closingSegAir.legs <+: closingFinalAir.legs :=
  ⟨dischargeLegs, by simp [closingSegAir, closingFinalAir, List.append_assoc]⟩

/-- ⚑ **THE SEGMENT IS `pallasThreadAir` PLUS PINS.** Not a look-alike: the row legs and the 96
threads are literally that object's, so `PastaLadderThread`'s forcing chain is about THIS block. -/
theorem closingSegAir_is_the_thread_row_plus_pins :
    closingSegAir.legs = pallasThreadAir.legs ++ (inPinLegs ++ outPinLegs) := by
  simp [closingSegAir, pallasThreadAir, List.append_assoc]

/-- ⚑ **THE COMPILER ACCEPTS BOTH BLOCKS.** The 96 threads are `.transition` (the only selector
admitting a `nxt` read) and the 64 discharge gates are `.last` with no `nxt` read. -/
theorem closingSegAir_mainRailOk : closingSegAir.mainRailOk = true := by decide

theorem closingFinalAir_mainRailOk : closingFinalAir.mainRailOk = true := by decide

/-- ⚑ **THE SELECTOR CENSUS.** 96 `.transition` threads and 64 `.last` discharge gates, and NONE at
`.all` or `.first`. `.last → .all` on the discharge refuses every intermediate row (a descriptor
accepting nothing); `.transition → .all` on the thread accepts strictly more. Neither moves a
constraint COUNT, so the counts are what keep a re-scope visible. -/
theorem the_closing_discharge_is_sixty_four_last_row_gates :
    closingFinalAir.windowCountSel RowSel.transition = 96
    ∧ closingFinalAir.windowCountSel RowSel.last = 64
    ∧ closingFinalAir.windowCountSel RowSel.all = 0
    ∧ closingFinalAir.windowCountSel RowSel.first = 0
    ∧ closingSegAir.windowCountSel RowSel.last = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The emitted SEGMENT descriptor. -/
def closingSegDesc : EffectVmDescriptor2 :=
  Dregg2.Circuit.Emit.EffectLower.lowerAir
    "dregg-mina-wrap-closing-seg::v1" RCB_WIDTH ACC_PI_COUNT [] closingSegAir

/-- The emitted FINAL descriptor. -/
def closingFinalDesc : EffectVmDescriptor2 :=
  Dregg2.Circuit.Emit.EffectLower.lowerAir
    "dregg-mina-wrap-closing-final::v1" RCB_WIDTH ACC_PI_COUNT [] closingFinalAir

/-- `4 476` sound row-local constraints + `96` accumulator threads + `192` endpoint pins. -/
theorem closingSegDesc_constraint_count :
    closingSegDesc.constraints.length = 4476 + 96 + 192 := by decide

/-- …and the final segment is that plus the `64` discharge gates. -/
theorem closingFinalDesc_constraint_count :
    closingFinalDesc.constraints.length = 4476 + 96 + 192 + 64 := by decide

theorem closingSegDesc_width : closingSegDesc.traceWidth = 3048 := rfl
theorem closingFinalDesc_width : closingFinalDesc.traceWidth = 3048 := rfl
theorem closingSegDesc_piCount : closingSegDesc.piCount = 192 := rfl
theorem closingFinalDesc_piCount : closingFinalDesc.piCount = 192 := rfl

/-- ⚑ **A NAME IS A KEY**, and this cone now has SIX descriptors over one algebra shape. A registry
lookup that resolved a Pallas closing block to a Vesta accumulator block would verify a Wrap
opening against Step-side gates and every count would still pass. -/
theorem the_closing_descriptors_do_not_share_a_name :
    closingSegDesc.name ≠ closingFinalDesc.name
    ∧ closingSegDesc.name ≠ MinaAccumulatorAir.accSegDesc.name
    ∧ closingFinalDesc.name ≠ MinaAccumulatorAir.accFinalDesc.name := by
  refine ⟨by decide, by decide, by decide⟩

/-- ⚑⚑ **THE COUNT CANNOT TELL THEM APART, AND THE PRIME CAN.** The Pallas closing block and the
Vesta accumulator block have the SAME constraint count, the SAME width and the SAME PI count: the
only thing separating them is the modulus the gate bodies reduce at, `pLimb` against `qLimb`. So a
shape check is NOT a descriptor check here, and a registry lookup that resolved one to the other
would verify a Wrap opening against Step-side gates with every number still passing.

⚠ Read what this does and does not say. `VmConstraint2` carries no `DecidableEq`, so the two
constraint LISTS are not compared here; what is compared is the limb list the two row families are
applied to. The legs are the same functions of that list — `pallasCompleteAddSoundLegs` and
`vestaCompleteAddSoundLegs` differ in nothing else — so this is the difference, but it is stated
one rail below the emitted bytes. Closing that gap is a `DecidableEq` derivation on
`VmConstraint2`, which is undone work and not a theorem of the model. -/
theorem the_count_cannot_tell_the_two_blocks_apart :
    (pLimb 4 = 237 ∧ qLimb 4 = 33 ∧ pLimb 4 ≠ qLimb 4)
    ∧ closingFinalDesc.constraints.length = MinaAccumulatorAir.accFinalDesc.constraints.length
    ∧ closingFinalDesc.traceWidth = MinaAccumulatorAir.accFinalDesc.traceWidth
    ∧ closingFinalDesc.piCount = MinaAccumulatorAir.accFinalDesc.piCount := by
  refine ⟨⟨by decide, by decide, by decide⟩, by decide, rfl, rfl⟩

/-! ## §3 — ⚑ THE DISCHARGE, FORCED, AT THE PALLAS BASE PRIME.

`PastaLadderThread.threadedLadder_forces` is already stated at `pN` — it is the ORIGINAL of which
`MinaAccumulatorAir.threadedLadderV_forces` is the Vesta twin. So this section needs only the two
moves that file adds on top: reach the LAST row's output (the `.transition` legs do not fire there),
and read the discharge. -/

/-- ⚑ **THE TERMINAL OUTPUT IS THE WHOLE CHAIN.** `threadedLadder_forces` stops at the accumulator
ENTERING row `n`; the discharge gates fire on row `n`'s OUTPUT. One more application of the row's
own forcing closes it — and this is exactly the seam where an off-by-one silently drops the final
addend. -/
theorem terminalClosingAccumulator_forces (tr : Trace) (n : Nat)
    (hrow : ∀ r, r ≤ n → RowSound tr r) (hthread : ∀ r, r < n → Threaded tr r) :
    CZ3 (pN : ℤ) (accOut tr n) (chainRef tr (n + 1)) := by
  have ih : CZ3 (pN : ℤ) (accIn tr n) (chainRef tr n) :=
    threadedLadder_forces tr n (fun r hr => hrow r (Nat.le_of_lt hr)) hthread
  have hrowf := row_forces tr n (hrow n (Nat.le_refl n))
  exact CZ3.trans hrowf
    (rcbTraceZ_congr (curveB3 : ℤ) ih.1 ih.2.1 ih.2.2 (CZm.refl _) (CZm.refl _) (CZm.refl _))

/-- ⚑⚑ **THE CLOSING CHECK, FORCED BY THE EMITTED CONSTRAINTS.**

`n+1` rows of deployed satisfaction at `pLimb`, `n` held threads, and the 64 discharge gates force
the `n+1`-fold RCB chain of the trace's own addends — starting from the accumulator published at
`PI[0..95]` — to be the point at infinity mod the real Pallas-base prime.

Read against the relation: with `acc_0 = c·Q` and the addends `delta`, `−(z₁b₀)·U`, `−z₂·H` and the
`−z₁·s_r·G_r`, this is `combinedResidual … (−z₁) … = O`, which §1b proves is (A) ∧ (B).

⚠ **IT SAYS NOTHING ABOUT WHAT THE ADDENDS ARE.** On `-final`, which declares no manifest, the
chain is the fold of whatever `ADD_X/Y/Z` the trace supplies. `-final` is kept as the OLD-ADMITS
pole of the routing pair, and §5 is the descriptor for which the stronger statement is available. -/
theorem closing_discharge_forced (tr : Trace) (n : Nat)
    (hrow : ∀ r, r ≤ n → RowSound tr r) (hthread : ∀ r, r < n → Threaded tr r)
    (hd : Discharged tr n) :
    CZm (pN : ℤ) (chainRef tr (n + 1)).1 0
    ∧ CZm (pN : ℤ) (chainRef tr (n + 1)).2.2 0 := by
  have hterm := terminalClosingAccumulator_forces tr n hrow hthread
  have hz := discharged_is_the_identity tr n hd
  refine ⟨?_, ?_⟩
  · have h := CZm.symm hterm.1
    rw [hz.1] at h
    exact CZm.symm (CZm.symm h)
  · have h := CZm.symm hterm.2.2
    rw [hz.2] at h
    exact CZm.symm (CZm.symm h)

/-! ### ⚠ THE NON-VACUITY OF `RowSound` IS WITNESSED BEHAVIOURALLY, NOT IN THIS KERNEL.

`closing_discharge_forced` would be vacuous if `RowSound` were unsatisfiable, and nothing here
proves it is not. What witnesses it is the deployed prover accepting the honest trace under
`dregg-mina-wrap-closing-final::v1`. That is behavioural evidence one rail down, and
`PastaLadderThread.threadedLadder_forces` and `MinaAccumulatorAir.accumulator_discharge_forced` have
exactly the same status — it is inherited, not newly conceded. ⚑ It is also UNDONE WORK wearing a
caveat: the thing worth building is a satisfiability lemma over `rcbSoundRow`, which would serve
every descriptor in this cone rather than one. -/

/-! ## §4 — ⚑⚑ THE MANIFEST, AND THE ARGUMENT IT DOES NOT HAVE.

Pallas: coordinates reduce at `pN` (the base field), scalars at `qN` (the scalar field). That is
the MIRROR of `MinaAccumulatorAir` §10, where the Vesta accumulator reduces coordinates at `qN` and
scalars at `pN`. Mixing the two is the silent wrong-field bug both comments exist to prevent. -/

/-- The identity in projective coordinates. -/
def OprojP : Pt3 := (0, 1, 0)

/-- Negation on Pallas: `−(X : Y : Z) = (X : −Y : Z)`. -/
def negP (P : Pt3) : Pt3 := (P.1, (pN - P.2.1 % pN) % pN, P.2.2)

/-- Every coordinate reduced at the PALLAS BASE prime, applied at the end of the derivation so the
declared point is CANONICAL by construction. -/
def redPtP (P : Pt3) : Pt3 := (P.1 % pN, P.2.1 % pN, P.2.2 % pN)

theorem redPtP_lt (P : Pt3) :
    (redPtP P).1 < pN ∧ (redPtP P).2.1 < pN ∧ (redPtP P).2.2 < pN := by
  have hp : 0 < pN := by decide
  exact ⟨Nat.mod_lt _ hp, Nat.mod_lt _ hp, Nat.mod_lt _ hp⟩

/-- One double-and-add step, LSB-first, over the SAME strongly-unified RCB formula the row computes
(`rcbAddM pN curveB3`), so nothing here is a second curve arithmetic. -/
def smulAuxP : Nat → Pt3 → Pt3 → Pt3
  | 0, _, acc => acc
  | (k + 1), P, acc =>
      smulAuxP ((k + 1) / 2) (rcbAddM pN curveB3 P P)
        (if (k + 1) % 2 = 1 then rcbAddM pN curveB3 acc P else acc)
  termination_by k => k
  decreasing_by exact Nat.div_lt_self (Nat.succ_pos _) (by decide)

/-- ⚑ `[k]·P` on Pallas. -/
def smulP (k : Nat) (P : Pt3) : Pt3 := smulAuxP k P OprojP

/-- The declared addend at a scalar and a point: `−k·P`, canonical. -/
def scaledNeg (k : Nat) (P : Pt3) : Pt3 := redPtP (negP (smulP k P))

/-- ⚑⚑⚑ **THE CLOSING MANIFEST — AND `sg` IS NOT AN ARGUMENT.**

The addends of `combinedResidual … (−z₁) …` with the accumulator entering at `c·Q`:

```text
    A_0 = delta          A_1 = −(z₁·b₀)·U          A_2 = −z₂·H
    A_{3+r} = −(z₁ · s_r) · G_r        s_r = b_poly_coefficients(u⃗)_r
```

Its inputs are a generator list, the endo-lifted IPA challenges, three scalars and three points.
**There is no `sg` parameter and no `sg` slot**, which is the whole content of §1b carried into the
emitted object: the emitter cannot supply `sg` and the prover has no addend to choose for it. -/
def srsSlots (Gs : List Pt3) (u : List Nat) (z1 n : Nat) : List Pt3 :=
  (List.range n).map (fun r => scaledNeg (z1 * bPolyCoeff qN u r % qN) (Gs.getD r (0, 0, 0)))

theorem srsSlots_length (Gs : List Pt3) (u : List Nat) (z1 n : Nat) :
    (srsSlots Gs u z1 n).length = n := by simp [srsSlots]

/-- ⚑ **SRS SLOT `r` IS `−(z₁·s_r)·G_r`.** No quantifier over the list: entry `r` IS the derivation
applied at `r`. -/
theorem srsSlot_at (Gs : List Pt3) (u : List Nat) (z1 n r : Nat) (hr : r < n) :
    (srsSlots Gs u z1 n).getD r (0, 0, 0)
      = scaledNeg (z1 * bPolyCoeff qN u r % qN) (Gs.getD r (0, 0, 0)) := by
  have hlt : r < (List.range n).length := by simpa using hr
  simp [srsSlots, List.getD, List.getElem?_map, List.getElem?_eq_getElem hlt, List.getElem_range]

def closingAddends (Gs : List Pt3) (u : List Nat) (z1 b0 z2 : Nat)
    (delta U H : Pt3) (n : Nat) : List Pt3 :=
  redPtP delta
    :: scaledNeg (z1 * b0 % qN) U
    :: scaledNeg (z2 % qN) H
    :: srsSlots Gs u z1 n

/-- ⚑ **THE MANIFEST CARRIES `3 + n` SLOTS — ONE PER NON-`sg` TERM.** The un-eliminated relation
has a fourth non-SRS addend, `−z₁·sg`; here it is ABSENT rather than zeroed, which matters because
a zeroed slot is a cell a prover fills. -/
theorem the_closing_manifest_carries_no_sg_slot
    (Gs : List Pt3) (u : List Nat) (z1 b0 z2 : Nat) (delta U H : Pt3) (n : Nat) :
    (closingAddends Gs u z1 b0 z2 delta U H n).length = 3 + n := by
  simp only [closingAddends, List.length_cons, srsSlots_length]
  omega

/-- ⚑ …and the three head entries are the three named group terms, in order. A silent reordering
here would fold `−z₂·H` where `delta` belongs and still balance, so the order is stated. -/
theorem the_closing_manifest_head_is_delta_then_bU_then_zH
    (Gs : List Pt3) (u : List Nat) (z1 b0 z2 : Nat) (delta U H : Pt3) (n : Nat) :
    (closingAddends Gs u z1 b0 z2 delta U H n).getD 0 (0, 0, 0) = redPtP delta
    ∧ (closingAddends Gs u z1 b0 z2 delta U H n).getD 1 (0, 0, 0)
        = scaledNeg (z1 * b0 % qN) U
    ∧ (closingAddends Gs u z1 b0 z2 delta U H n).getD 2 (0, 0, 0)
        = scaledNeg (z2 % qN) H := by
  refine ⟨rfl, rfl, rfl⟩

/-- ⚑ **SRS SLOT `r` IS `−(z₁·s_r)·G_r`.** No quantifier over the list: entry `3 + r` IS the
derivation applied at `r`. -/
theorem the_manifest_tail_is_the_srs_slots
    (Gs : List Pt3) (u : List Nat) (z1 b0 z2 : Nat) (delta U H : Pt3) (n : Nat) :
    (closingAddends Gs u z1 b0 z2 delta U H n).drop 3 = srsSlots Gs u z1 n := rfl

theorem the_srs_slot_is_the_scaled_generator
    (Gs : List Pt3) (u : List Nat) (z1 b0 z2 : Nat) (delta U H : Pt3) (n r : Nat) (hr : r < n) :
    (closingAddends Gs u z1 b0 z2 delta U H n).getD (r + 3) (0, 0, 0)
      = scaledNeg (z1 * bPolyCoeff qN u r % qN) (Gs.getD r (0, 0, 0)) := by
  show (srsSlots Gs u z1 n).getD r (0, 0, 0) = _
  exact srsSlot_at Gs u z1 n r hr

/-- ⚑ **EVERY SLOT IS CANONICAL AT `pN` BY CONSTRUCTION.** `scaledNeg` ends in `redPtP` and the
`delta` slot is `redPtP delta`, so no manifest entry can declare limbs an honest witness cannot
produce. This is what lets `declAddend` recompose without a modular envelope. -/
theorem every_closing_slot_is_canonical (k : Nat) (P : Pt3) :
    ((scaledNeg k P).1 < pN ∧ (scaledNeg k P).2.1 < pN ∧ (scaledNeg k P).2.2 < pN)
    ∧ ((redPtP P).1 < pN ∧ (redPtP P).2.1 < pN ∧ (redPtP P).2.2 < pN) :=
  ⟨redPtP_lt _, redPtP_lt _⟩

/-- ⚑⚑ **THE DECLARED ADDEND'S VALUE IS THE DERIVED POINT.** The three recompositions
`declaredChain` reads at index `3 + r` are the three coordinates of `−(z₁·s_r)·G_r` — over ℤ, with
no canonicality envelope, because `redPtP` reduced at `pN` and `pN < 2^256`. -/
theorem declAddend_of_closingAddends
    (Gs : List Pt3) (u : List Nat) (z1 b0 z2 : Nat) (delta U H : Pt3) (n r : Nat) (hr : r < n) :
    declAddend (closingAddends Gs u z1 b0 z2 delta U H n) (r + 3)
      = ptZ (scaledNeg (z1 * bPolyCoeff qN u r % qN) (Gs.getD r (0, 0, 0))) := by
  have hb := redPtP_lt (negP (smulP (z1 * bPolyCoeff qN u r % qN) (Gs.getD r (0, 0, 0))))
  have hpq : pN < qN := by decide
  exact declAddend_of_getD _ (r + 3) _
    (the_srs_slot_is_the_scaled_generator Gs u z1 b0 z2 delta U H n r hr)
    (lt_trans hb.1 hpq) (lt_trans hb.2.1 hpq) (lt_trans hb.2.2 hpq)

/-! ## §5 — ⚑ THE ROUTED DESCRIPTOR.

`MinaAccumulatorAir` §8's routing legs are prime-free — a row-index thread and one 97-wide
exact-public lookup on `RIDX + 1 ‖ ADD_X..ADD_X+95`. They are imported, not re-authored. -/

/-- **THE ROUTED CLOSING BLOCK.** `closingFinalAir`'s legs verbatim, plus the index origin, the
index thread and the one lookup. -/
def closingRoutedAir : EffectAir :=
  { tables := routedTables []
  , legs := closingFinalAir.legs ++ [ridxStartLeg, ridxThreadLeg, addendLookupLeg] }

/-- …and the same block over a DECLARED addend list. The legs do not depend on it. -/
def closingRoutedAirOn (As : List Pt3) : EffectAir :=
  { closingRoutedAir with tables := routedTables As }

theorem the_closing_legs_do_not_depend_on_the_manifest (As : List Pt3) :
    (closingRoutedAirOn As).legs = closingRoutedAir.legs := rfl

theorem closingRoutedAir_extends_closingFinalAir (As : List Pt3) :
    closingFinalAir.legs <+: (closingRoutedAirOn As).legs :=
  ⟨[ridxStartLeg, ridxThreadLeg, addendLookupLeg], rfl⟩

/-- ⚑ **THE COMPILER ACCEPTS THE ROUTED BLOCK.** -/
theorem closingRoutedAir_mainRailOk (As : List Pt3) : (closingRoutedAirOn As).mainRailOk = true := by
  show closingRoutedAir.mainRailOk = true
  decide

/-- The routed block, emitted under a given name. -/
def closingRoutedDescNamed (nm : String) (As : List Pt3) : EffectVmDescriptor2 :=
  Dregg2.Circuit.Emit.EffectLower.lowerAir nm ROUTED_WIDTH ACC_PI_COUNT [] (closingRoutedAirOn As)

/-- ⚑⚑ **THE EMITTED CLOSING DESCRIPTOR** — the routed algebra over the `sg`-free manifest. -/
def closingSrsDesc (Gs : List Pt3) (u : List Nat) (z1 b0 z2 : Nat)
    (delta U H : Pt3) (n : Nat) : EffectVmDescriptor2 :=
  closingRoutedDescNamed "dregg-mina-wrap-closing-srs::v1"
    (closingAddends Gs u z1 b0 z2 delta U H n)

theorem closingSrsDesc_name (Gs : List Pt3) (u : List Nat) (z1 b0 z2 : Nat)
    (delta U H : Pt3) (n : Nat) :
    (closingSrsDesc Gs u z1 b0 z2 delta U H n).name = "dregg-mina-wrap-closing-srs::v1" := rfl

/-- ⚑ **THE ALGEBRA IS ONE OBJECT AT EVERY MANIFEST.** Constraints, width, PI count and table ids
are fixed; only `.name` and the declared rows move. This is what makes `-srs` one AIR with a
per-block preprocessed matrix rather than a new circuit per block. -/
theorem the_closing_srs_descriptor_differs_only_in_its_name_and_its_manifest
    (Gs : List Pt3) (u : List Nat) (z1 b0 z2 : Nat) (delta U H : Pt3) (n : Nat) :
    (closingSrsDesc Gs u z1 b0 z2 delta U H n).constraints
        = (closingRoutedDescNamed "x" []).constraints
    ∧ (closingSrsDesc Gs u z1 b0 z2 delta U H n).traceWidth = ROUTED_WIDTH
    ∧ (closingSrsDesc Gs u z1 b0 z2 delta U H n).piCount = ACC_PI_COUNT
    ∧ ((closingSrsDesc Gs u z1 b0 z2 delta U H n).tables.map (·.id))
        = ((closingRoutedDescNamed "x" []).tables.map (·.id)) := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- `4 476 + 96 + 192 + 64` from `-final`, plus the index origin, the index thread and the lookup. -/
theorem closingRoutedDesc_constraint_count (As : List Pt3) :
    (closingRoutedDescNamed "x" As).constraints.length = 4476 + 96 + 192 + 64 + 3 := by
  show (closingRoutedDescNamed "x" []).constraints.length = _
  decide

theorem closingRoutedDesc_width (As : List Pt3) :
    (closingRoutedDescNamed "x" As).traceWidth = 3049 := rfl

/-- ⚑ **ONLY THE ROUTING LEG TARGETS THE ADDEND TABLE**, on THIS file's own constraint list. This
is the `decide` `MinaAccumulatorAir` §8b runs on the Vesta object; re-run here, because a
constraint list is not transferable between two descriptors that merely look alike, and it is the
hypothesis every routing lemma downstream stands on. -/
theorem only_the_closing_routing_leg_targets_the_addend_table :
    ((closingRoutedDescNamed "x" []).constraints.filter
      (fun c => ! MinaAccumulatorAir.notAddendLookup c)).length = 1 := by decide

/-! ## §6 — ⚑⚑⚑ THE FREE `delta`, AS AN EQUATION RATHER THAN AS A SENTENCE.

§"WHAT THIS DOES NOT ESTABLISH" item 3 says `delta` is free. That is prose. This section is the
equation, and it says something sharper than the prose did: **the check does not see `acc₀` and
`delta` separately — it sees only their SUM.** So there is not merely *a* forgery; there is a
one-parameter family of them, one per group element, and each member is reached by an addition.

    acc₀ ↦ acc₀ − Δ        delta ↦ delta + Δ        (every other slot untouched)

⚠ Read against `MinaAccumulatorAir` residual 1, which says whether the published `c·Q` is the
block's is a CONSUMER obligation. That residual and this one are THE SAME MOVE seen from two ends,
and neither is visible from inside the descriptor: a consumer that recomputes `c·Q` from a `c` it
trusts refuses the shift, and a consumer that reads `PI[0..95]` and the manifest does not.

⚑ And this is what §7 exists to kill: the shift moves `delta`, and §7's `.first` pins force
`delta`'s limbs to the pair a transcript absorb published. -/

section Shift

variable {F : Type} [CommRing F] {A : Type} [AddCommGroup A] [Module F A]

/-- ⚑ **THE ELIMINATED RESIDUAL WITH THE ACCUMULATOR AS ONE GROUP ELEMENT** — which is the shape the
descriptor actually publishes, at `PI[0..95]`. `c` and `Q` do not occur separately in any emitted
constraint of this file, so stating the residual at `(c, Q)` overstates what the object holds. -/
def closingResidualAt (z1 z2 b0 : F) (acc delta U H S : A) : A :=
  acc + delta - z1 • S - (z1 * b0) • U - z2 • H

/-- …and it IS §1's residual, by `rfl`, at `acc := c • Q`. So §6 is about the same object §1b is. -/
theorem closingResidualAt_is_the_published_shape (c z1 z2 b0 : F) (Q delta U H S : A) :
    closingResidualAt z1 z2 b0 (c • Q) delta U H S = closingResidual c z1 z2 b0 Q delta U H S :=
  rfl

/-- ⚑⚑⚑ **THE DELTA SHIFT IS INVISIBLE TO THE CLOSING CHECK.** Move the published accumulator down
by any group element and `delta` up by the same one: the residual is UNCHANGED, so the descriptor
accepts both. No hypotheses, no curve, no prime — it is a fact about the shape.

⚠ **AND UPSTREAM REFUSES IT, BY THE ORDERING AND ONLY BY THE ORDERING.** `ipa.rs:382-383` absorbs
`delta` and THEN squeezes `c`, so a forger who moves `delta` moves `c`, and `c·Q` moves with it —
in a direction no adversary controls. That is a Fiat–Shamir fact; no rearrangement of this equation
can express it, which is why the fix in §7 is a transcript weld and not an algebraic one. -/
theorem the_delta_shift_is_invisible (z1 z2 b0 : F) (acc delta U H S Δ : A) :
    closingResidualAt z1 z2 b0 (acc - Δ) (delta + Δ) U H S
      = closingResidualAt z1 z2 b0 acc delta U H S := by
  unfold closingResidualAt
  abel

/-- The same statement read as "only the sum matters": two `(acc, delta)` pairs with equal sums are
indistinguishable here. -/
theorem the_check_sees_only_the_sum (z1 z2 b0 : F) (acc acc' delta delta' U H S : A)
    (h : acc + delta = acc' + delta') :
    closingResidualAt z1 z2 b0 acc delta U H S = closingResidualAt z1 z2 b0 acc' delta' U H S := by
  unfold closingResidualAt
  rw [h]

end Shift

/-! ### §6b — ⚑ THE FORGERY EXHIBITED AT ℤ, so §6 is not a statement about an empty family.

`the_delta_shift_is_invisible` is an identity and would hold even if the residual were constantly
`0`, which §1c already refuted for the un-shifted family. These three re-run that refutation ON THE
SHIFTED FAMILY: every member of the shift orbit vanishes, the members are DISTINCT, and a move that
is NOT a shift still refutes. -/

/-- The eliminated residual at `F = A = ℤ`, at §1c's own numbers (`z₁ = 3`, `z₂ = 5`, `b₀ = 7`,
`U = 13`, `H = 17`, `S = 19`), with the accumulator `22 = c·Q` at `c = 2, Q = 11` and the honest
`delta = 393`, shifted by `t`. -/
def zShift (t : ℤ) : ℤ := closingResidualAt (F := ℤ) (A := ℤ) 3 5 7 (22 - t) (393 + t) 13 17 19

/-- ⚑⚑ **EVERY MEMBER OF THE SHIFT ORBIT IS ACCEPTED.** One theorem, all `t` — the forgery is not
one witness, it is a family indexed by the group. -/
theorem the_whole_shift_orbit_is_admitted (t : ℤ) : zShift t = 0 := by
  unfold zShift closingResidualAt
  simp only [smul_eq_mul]
  ring

/-- …and its members are DISTINCT, in BOTH coordinates, so "accepted at every `t`" is not "accepted
at one point named twice." -/
theorem the_shift_orbit_is_not_a_point :
    ((22 : ℤ) - 100 ≠ 22 - 0) ∧ ((393 : ℤ) + 100 ≠ 393 + 0) := by
  refine ⟨by decide, by decide⟩

/-- ⚑ **AND A MOVE THAT IS NOT A SHIFT STILL REFUTES.** Move `delta` alone — the accumulator
untouched — and the residual is non-zero. So §6 says the check is blind to ONE direction, not that
it is blind. -/
theorem a_delta_move_without_the_matching_accumulator_move_refutes :
    closingResidualAt (F := ℤ) (A := ℤ) 3 5 7 22 (393 + 100) 13 17 19 ≠ 0 := by
  unfold closingResidualAt
  decide

/-! ## §7 — ⚑⚑⚑ THE TRANSCRIPT WELD: `delta` STOPS BEING A SLOT AND BECOMES AN ABSORBED PAIR.

## The mechanism, and why it is the only one that could work here

`sg`'s binding was ALGEBRAIC — a relation inside the closing equation — so §1b closed it by
elimination, inside the equation. `delta`'s binding is not in the equation at all: it is
`ipa.rs:382-383`'s ordering. **A weld for it must name a HASH, and the hash is Poseidon over the
Pallas base field.** dregg has that as an emitted AIR already: `dregg-pasta-fp-absorb::v1`
(`MinaWrapVerifierSpongeFp.fpAbsorbDesc`) computes `perm(state + [x₀, x₁, 0])` at `pLimb`, and
`absorb_g` of ONE Pallas point is exactly a rate-2 absorb of its two affine coordinates. The
program needed no building.

## What this section adds to the routed block — four legs and a column block

1. ⚑ **64 `.first` gates pinning `delta`'s X and Y limbs** to the absorbed pair. These are the
   refusal: a shifted `delta` moves a limb and a `boundary` gate fires. They are NOT a pin against
   the manifest — that would be `feedback-a-pin-against-its-own-definition-is-decoration` — they
   are a pin against a value that is *also* named by leg 4's commitment.
2. **32 `.first` gates forcing `delta`'s projective `Z` to `1`.** `absorb_g` absorbs AFFINE
   coordinates, so an unnormalised representative would be a different absorbed pair for the same
   group element. Without these the weld would name a point and the chain would fold another.
3. **32 `.pin` legs publishing the squeeze**, at PI `192..223`. Published so a CONSUMER can compute
   `c = ScalarChallenge(low128(squeeze)).to_field(endo_r)` and compare it against the `c` it used to
   form `c·Q`. ⚠ That comparison is an EXECUTOR check and is named as one below.
4. ⚑⚑ **ONE `.proofBind`** whose commitment is `TR_IN ‖ ADD_X ‖ ADD_Y ‖ TR_OUT` — **192 lanes, the
   EXACT public-input vector of `dregg-pasta-fp-absorb::v1`, limb for limb, in the same 32×8-bit
   `pLimb` encoding.** Not a digest and not a re-encoding: `SPONGE_PI_COUNT = 6·SK = 192` and this
   commitment is `3·SK + 2·SK + SK`. There is no birthday bound because there is no hash between
   the two vectors.

⚑ **AND THE COMMIT NAMES THE CHAIN'S OWN CELLS.** `deltaCommitLanes` is `.var (ADD_X + j)` for
`j < 2·SK` — the SAME columns `addendTuple` reads at tuple positions `1 … 64` and the same ones
`pallasCompleteAddSoundLegs` folds as row 0's addend. `the_weld_names_the_chains_own_addend_cells`
is that as a theorem, because a weld against a COPY of `delta` would be co-occurrence.

## ⚠ WHAT THIS DOES NOT CLOSE — and one of them is where the residue moved to

a. ⚑⚑ **`TR_IN` IS A DESCRIPTOR CONSTANT AND `TR_OUT` IS A PUBLISHED WITNESS.** The AIR refuses a
   `delta` that is not the pair between them; it does NOT refuse a re-emission at a different
   `(TR_IN, delta, TR_OUT)` triple, because all three move together and the absorb sub-proof exists
   for any of them. **So the weld converts "the emitter may choose a group element `delta` freely,
   last, after seeing everything" into "the emitter must choose a transcript state and publish the
   scalar it squeezes."** The residue is `c`, ONE published field element, and the check that
   binds it is `c·Q` — `MinaAccumulatorAir` residual 1, the deferred MSM, CIRCUIT / EMITTER /
   NOWHERE with no fourth place. Say it that way; do not say `delta` is bound.
b. ✅ **CLOSED 2026-08-10 — and read what "closed" costs before quoting it.** This residual was
   *"the absorb descriptor's own soundness"*, and it was two obligations, not one.

   **Obligation 1 — the descriptor refines its AIR — closed 2026-08-09.**
   `MinaWrapVerifierSpongeFp.fpAbsorbDesc_certified`, produced by `lowerTiedAir` at zero moved
   bytes: the 858 emitted constraints FORCE every leg of `fpAbsorbAir`, in `AirLeg.forces` — the
   source's own vocabulary, never mentioning the lowering.

   **Obligation 2 — the AIR is the interpreter — closed 2026-08-10**, in `Emit.AirProgramRows`.
   The named absence was *"no theorem assembles them into 'row `k+1`'s register file is
   `stepRegsAt` of row `k`'s', and none inducts that over 2 048 rows"*. `step_of_row` is that
   theorem and `rows_track_the_interpreter` is that induction; `runs_the_program` is the
   end-of-program form, and `absorb_rows_force_the_permutation` composes it with
   `the_absorb_program_permutes_gen`, so **the emitted constraints — not `runProgAt` — reach
   `PastaPoseidonFq.Core.perm`.** The shape is the one this note predicted:
   `AirCrossRow.rcbSat_of_rows` / `scheduledRows_force_the_rcb_formula`.
   ⚑ It is MODULUS-GENERAL in `(pl, N)`, so one theorem serves phase 1 and phase 2, and
   `rowsForced_of_certified` connects any of the seven `programAir … ++ pins` descriptors to it by
   one `mem_append_left`.

   ⚠ **THREE PREMISES AND ONE BOUNDARY, and none of them is decoration.**
   `RangeTablesHonest` — the inherited `AirCrossRow.PoolsRanged` floor, now stated once per
   descriptor rather than per column pool, and still UNDONE WORK one rail below any leg;
   `RomFaithful` — `TableDef.publicContentsFaithful` at the ROM, the deployed verifier's own check;
   `Tracks` at row 0 — `programAir` pins no register column on the first row and a BOUNDARY must;
   and `transition_legs_are_vacuous_on_the_last_row` — a `.transition` leg claims nothing at
   `isLast = true`, so the last instruction's write is forced only when a row follows it.
   ⚠ And `AirProgramRows.register_column_is_not_ranged`: the machine range-checks `x`, `y`, `z`,
   the quotient and the two carry pools and NOT the register file, so a register column is pinned
   only mod `P` — which is why the bridge reads it as `regVal` (through `· % P`) and never as
   `sVal`. `PastaPoseidon.perm_forces` remains a constraint-level forcing theorem for an UNEMITTED
   9×30-limb gadget, and is still not what runs.

   So the verdict this note carried — *"the emitted constraints refine their AIR; the AIR is not
   yet proved to be the interpreter"* — is **retired**. Both halves hold.
c. **`z₁`, `z₂` and `b₀` are untouched, and that is not the same kind of gap.** A forger who moves
   `z₂` shifts the sum by `δ·H`; upstream refuses that by the dlog/extraction argument (P10), not by
   a transcript. P10 is a FLOOR and is undischarged here and everywhere in this stack. `delta`'s was
   NOT a floor — it was a mechanizable ordering — which is exactly why it was worth taking. -/

/-- ⚑ **THE ABSORB SUB-PROGRAM'S IDENTITY, AS NINE `Faithful9` LANES.** The key lanes of
`effect_vm_descriptor2_semantic_fingerprint(dregg-pasta-fp-absorb::v1)`.

⚠ Lean cannot compute blake3, so this is a TRANSCRIPTION, and a transcription is only a gate if
something recomputes it — `circuit/tests/mina_wrap_closing_air_proves.rs` recomputes the fingerprint from
`circuit/descriptors/by-name/pasta-fp-absorb.json`'s own bytes and asserts these nine numbers.
⚠ **FLAG DAY COUPLING:** re-emitting `pasta-fp-absorb.json` moves this literal and re-emits every
`-fs` descriptor. It is the same coupling `LINK_VK_LANES` and `CHAINLINK_VK_LANES` carry.

⚑⚑ **CORRECTED 2026-08-10 — THE DIVERGENCE THIS BLOCK WARNED ABOUT IS GONE, AND WHAT REPLACED IT IS
WORSE.**

Until today this block read *"AND THIS IS NOT THE NUMBER `LightClientMinaLinkAir.ABSORB_VK_LANES`
CARRIES — measured 2026-08-08, and that one is STALE. Its literal is `[446814635, 83884421, …]`"*.
`LightClientMinaLinkAir` has since moved to the nine below, so the two copies now AGREE — and the
warning became a statement about a tree that no longer existed, still sitting here asserting a
divergence no reader could reproduce. **A dated verdict about someone else's literal outlives the
literal**, which is the same failure the block was written to describe.

⚠ **BOTH COPIES WERE STALE TOGETHER.** Measured 2026-08-10 against HEAD (materialised with
`scripts/materialise-descriptors-at.sh HEAD`, so this is not a working-tree artifact):

    dregg-pasta-fp-absorb::v1   w=469 pi=192 cons=858
      fp=5c0973624f0a1686966e8d1e0c16894279154bfb98c14edaf51d268c61e2fd18
      lanes=[41093468, 279990907, 56337825, 304879677, 290952232, 13401509, 399993147,
             204571843, 1637858]

— not the old nine. Two agreeing transcriptions of a value that matches neither the artifact nor
each other's source are strictly LESS informative than one disagreeing pair, because the agreement
reads as corroboration. **Two sources for one derived value are not two witnesses; they are one
witness copied.** The literal below is that re-measurement, landed in the same flag day as
`LightClientMinaLinkAir.ABSORB_VK_LANES` and independently resolved by the pure-Lean all-pin gate.

⚑ This is not a local defect. `circuit/tests/vk_pin_closure_over_the_served_tree.rs` resolves EVERY
`vk_pin` the tree serves against the fingerprints of EVERY descriptor the tree serves — it needs no
per-pin map, so it cannot go stale by omission — and at HEAD **7 of 7 dangle**: every recursion bind
in the Mina chain attests a program no descriptor here has. The per-pin gates named above are real
but partial, each hand-written for one pin, so a pin added after its gate was written is ungated by
construction.

⚠ Fixing the VALUE requires the re-emit + VK rotation of the link, the head and the conjunction
chain performed by this flag day; changing the literal without that derived-artifact step would
leave the opposite half stale. -/
def ABSORB_VK_LANES : List ℤ :=
  [41093468, 279990907, 56337825, 304879677, 290952232, 13401509, 399993147, 204571843, 1637858]

/-- The bind's guard column — one past the routing's row index. -/
def DBIND : Nat := ROUTED_WIDTH

/-- The nine attested-program columns. -/
def FSVK (i : Nat) : Nat := ROUTED_WIDTH + 1 + i

/-- The 32 columns holding the squeezed sponge lane, PI-published at `192 … 223`. -/
def TROUT (j : Nat) : Nat := ROUTED_WIDTH + 10 + j

/-- The welded descriptor's declared trace width: the routed row, the guard, nine program lanes and
the squeeze. `3 049 → 3 091`, `+1.38 %`. -/
def FS_WIDTH : Nat := ROUTED_WIDTH + 10 + SK

/-- PI slot of the `j`-th squeeze limb — APPENDED, so no accumulator slot moves. -/
def FS_TROUT_PI (j : Nat) : Nat := ACC_PI_COUNT + j

/-- `192 + 32`. -/
def FS_PI_COUNT : Nat := ACC_PI_COUNT + SK

theorem the_weld_costs_forty_two_columns_and_thirty_two_public_inputs :
    FS_WIDTH = 3091 ∧ ROUTED_WIDTH = 3049 ∧ FS_PI_COUNT = 224 ∧ ACC_PI_COUNT = 192
    ∧ DBIND = 3049 ∧ FSVK 0 = 3050 ∧ TROUT 0 = 3059 ∧ FS_TROUT_PI 0 = 192 := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl, rfl, rfl⟩

/-- The guard is `1` on the first row. `.first` lowers to a `boundary`, whose body reads `loc`
alone. On later rows the guard is a free bit and the bind is inert there — a prover who sets it
makes an ADDITIONAL claim, never a weaker one. -/
def dbindStartLeg : AirLeg :=
  .window ⟨RowSel.first, WindowExpr.add (.loc DBIND) (.const (-1))⟩

/-- ⚑⚑ **THE PIN THAT REFUSES THE SHIFT.** Row 0's `j`-th addend limb equals the `j`-th limb of the
absorbed pair. `j < 2·SK` walks `ADD_X` then `ADD_Y`, because `ADD_Y = ADD_X + SK`. -/
def deltaPinLeg (d : Pt3) (j : Nat) : AirLeg :=
  .window ⟨RowSel.first,
    WindowExpr.add (.loc (ADD_X + j)) (.const (-(coordLimb d j : ℤ)))⟩

def deltaPinLegs (d : Pt3) : List AirLeg := (List.range (2 * SK)).map (deltaPinLeg d)

/-- ⚑ **AND THE AFFINE NORMALISATION.** `absorb_g` absorbs affine coordinates; a projective
representative with `Z ≠ 1` is the same group element and a DIFFERENT absorbed pair. -/
def deltaAffineLeg (j : Nat) : AirLeg :=
  .window ⟨RowSel.first,
    WindowExpr.add (.loc (ADD_Z + j)) (.const (if j = 0 then -1 else 0))⟩

def deltaAffineLegs : List AirLeg := (List.range SK).map deltaAffineLeg

/-- The squeeze, published. -/
def trOutPinLegs : List AirLeg :=
  (List.range SK).map (fun j => AirLeg.pin ⟨.first, TROUT j, FS_TROUT_PI j⟩)

/-- The incoming sponge state, as `3 · SK` descriptor CONSTANTS — the same status the salt lanes
have in `LightClientMinaLinkAir.seamCommitLanes`, and the same status this descriptor's manifest
has. A `Pt3` because a Poseidon state over `Fp` is three field elements and `coordLimb` already
decomposes exactly that. -/
def trInLanes (st : Pt3) : List Dregg2.Circuit.Expr :=
  (List.range (3 * SK)).map (fun j => Dregg2.Circuit.Expr.const (coordLimb st j : ℤ))

/-- ⚑⚑ **THE ABSORBED PAIR, NAMED AS THE CHAIN'S OWN CELLS** — not a copy of `delta`. -/
def deltaCommitLanes : List Dregg2.Circuit.Expr :=
  (List.range (2 * SK)).map (fun j => Dregg2.Circuit.Expr.var (ADD_X + j))

def trOutCommitLanes : List Dregg2.Circuit.Expr :=
  (List.range SK).map (fun j => Dregg2.Circuit.Expr.var (TROUT j))

def fsVkLanes : List Dregg2.Circuit.Expr :=
  (List.range 9).map (fun i => Dregg2.Circuit.Expr.var (FSVK i))

/-- ⚑⚑⚑ **THE DELTA-ABSORB BIND.** Guard `DBIND`; commitment `TR_IN ‖ delta.x ‖ delta.y ‖ squeeze`,
which IS `dregg-pasta-fp-absorb::v1`'s public-input vector; attested program the nine `FSVK`
columns, pinned to its fingerprint.

⚑ `bound := none`, for the reason `linkBindLeg` gives: `bound` forces `commit` to equal a row-local
expression, and every lane here is already a descriptor constant or a `.var` on this row. -/
def deltaAbsorbBindLeg (st : Pt3) : AirLeg :=
  .bind { guard  := .var DBIND
        , commit := trInLanes st ++ deltaCommitLanes ++ trOutCommitLanes
        , vk     := fsVkLanes
        , vkPin  := some ABSORB_VK_LANES
        -- ⚑ 2026-08-10: the `delta-absorb-pis` PORT. Its cover is the closing fold's connect,
        -- named here so the registry gate resolves it rather than a docblock asserting it.
        , bound  := .port ⟨"delta-absorb-pis", "dregg_circuit_prove::mina_wrap_closing_fold::connect_delta_absorb_pis"⟩ }

/-- ⚑ **THE WELDED BLOCK** — the routed block VERBATIM, plus the weld. -/
def closingFsAirOn (As : List Pt3) (d st : Pt3) : EffectAir :=
  { tables := routedTables As
  , legs := closingRoutedAir.legs ++ deltaPinLegs d ++ deltaAffineLegs
      ++ [dbindStartLeg] ++ trOutPinLegs ++ [deltaAbsorbBindLeg st] }

/-- ⚑ **THE ROUTED BLOCK'S LEGS ARE A PREFIX OF THE WELDED ONE'S.** Every forcing statement in
§3 and §5 applies unchanged; the weld APPENDS. -/
theorem closingFsAir_extends_closingRoutedAir (As : List Pt3) (d st : Pt3) :
    closingRoutedAir.legs <+: (closingFsAirOn As d st).legs :=
  ⟨deltaPinLegs d ++ deltaAffineLegs ++ [dbindStartLeg] ++ trOutPinLegs ++ [deltaAbsorbBindLeg st],
   by simp [closingFsAirOn, List.append_assoc]⟩

/-- ⚑ **THE COMPILER ACCEPTS THE WELDED BLOCK.** -/
theorem closingFsAir_mainRailOk (As : List Pt3) (d st : Pt3) :
    (closingFsAirOn As d st).mainRailOk = true := by
  have hR := closingRoutedAir_mainRailOk ([] : List Pt3)
  simp only [Dregg2.Circuit.EffectAirIR.EffectAir.mainRailOk, closingRoutedAirOn] at hR ⊢
  simp only [closingFsAirOn, List.all_append, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨hR, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;>
    simp [deltaPinLegs, deltaPinLeg, deltaAffineLegs, deltaAffineLeg, trOutPinLegs,
      dbindStartLeg, deltaAbsorbBindLeg, trInLanes, deltaCommitLanes, trOutCommitLanes,
      fsVkLanes, ABSORB_VK_LANES, List.all_eq_true,
      Dregg2.Circuit.EffectAirIR.AirLeg.mainRailOk,
      Dregg2.Circuit.EffectAirIR.WindowLeg.mainRailOk,
      Dregg2.Circuit.EffectAirIR.BindLeg.mainRailOk,
      Dregg2.Circuit.TableAirIR.readsNext,
      Dregg2.Circuit.DescriptorIR2.CommitBindingOf.isPort,
      Dregg2.Circuit.DescriptorIR2.PortCover.namesOk,
      Dregg2.Circuit.DescriptorIR2.PROOF_BIND_MIN_LANES, SK]

/-- ⚑⚑ **THE COMMITMENT IS THE SUB-PROGRAM'S PUBLIC-INPUT VECTOR, LANE FOR LANE.** `192` against
`MinaWrapVerifierSpongeFp.SPONGE_PI_COUNT`, in the same `32 × 8`-bit `pLimb` encoding. There is no
digest between the two vectors and therefore no birthday bound. -/
theorem the_weld_commit_is_the_absorb_programs_public_input_vector (st : Pt3) :
    (trInLanes st ++ deltaCommitLanes ++ trOutCommitLanes).length
      = Dregg2.Circuit.Emit.MinaWrapVerifierSpongeFp.SPONGE_PI_COUNT
    ∧ (trInLanes st).length = 3 * SK
    ∧ deltaCommitLanes.length = 2 * SK
    ∧ trOutCommitLanes.length = SK := by
  refine ⟨by simp [trInLanes, deltaCommitLanes, trOutCommitLanes,
                   Dregg2.Circuit.Emit.MinaWrapVerifierSpongeFp.SPONGE_PI_COUNT, SK],
          by simp [trInLanes], by simp [deltaCommitLanes], by simp [trOutCommitLanes]⟩

/-- ⚑⚑ **THE WELD NAMES THE CHAIN'S OWN ADDEND CELLS, NOT A COPY OF THEM.** Commit lane `3·SK + j`
is `.var (ADD_X + j)`, and `ADD_X + j` is the column `addendTuple` reads at tuple position `j + 1`.
So the object the bind commits to and the object the RCB row folds are ONE set of cells. -/
theorem the_weld_names_the_chains_own_addend_cells (j : Nat) (hj : j < 2 * SK) :
    deltaCommitLanes.getD j (.const 0) = Dregg2.Circuit.Expr.var (ADD_X + j)
    ∧ addendTuple.getD (j + 1) (.const 0) = Dregg2.Circuit.Expr.var (ADD_X + j) := by
  have h1 : j < (List.range (2 * SK)).length := by simpa using hj
  have h2 : j < (List.range (3 * SK)).length := by
    simp only [List.length_range]; omega
  refine ⟨?_, ?_⟩
  · simp [deltaCommitLanes, List.getD, List.getElem?_map, List.getElem?_eq_getElem h1,
      List.getElem_range]
  · simp [addendTuple, List.getD, List.getElem?_cons_succ, List.getElem?_map,
      List.getElem?_eq_getElem h2, List.getElem_range]

/-- ⚑ **THE REFUSAL, AS THE GATE BODY.** A row-0 addend limb that is not the absorbed pair's makes
the `.first` boundary body non-zero. No hypotheses beyond the move itself. -/
theorem the_delta_pin_refuses_a_moved_limb (d : Pt3) (j : Nat)
    (env : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv)
    (h : env.loc (ADD_X + j) ≠ (coordLimb d j : ℤ)) :
    (WindowExpr.add (.loc (ADD_X + j)) (.const (-(coordLimb d j : ℤ)))).eval env ≠ 0 := by
  intro hz
  apply h
  simp only [WindowExpr.eval] at hz
  linarith

/-- …and ACCEPTS the honest one, so the pin is not refusing everything. -/
theorem the_delta_pin_admits_the_absorbed_pair (d : Pt3) (j : Nat)
    (env : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv)
    (h : env.loc (ADD_X + j) = (coordLimb d j : ℤ)) :
    (WindowExpr.add (.loc (ADD_X + j)) (.const (-(coordLimb d j : ℤ)))).eval env = 0 := by
  simp only [WindowExpr.eval, h]
  ring

/-- ⚑ **THE SHIFT MOVES A PINNED LIMB, WHICH IS WHY §7 KILLS §6's FAMILY.** Two points whose `X`
differs below `2^8` differ in limb `0`, and limb `0` is pinned. Exhibited rather than asserted. -/
theorem the_shift_moves_a_pinned_limb :
    coordLimb (7, 11, 1) 0 ≠ coordLimb (8, 11, 1) 0 := by decide

/-- The welded descriptor, emitted under its own name. ⚑ It is a THIRD name over one algebra and a
registry that resolved it to `-srs` would verify a welded claim against an unwelded block. -/
def closingFsDescNamed (nm : String) (As : List Pt3) (d st : Pt3) : EffectVmDescriptor2 :=
  Dregg2.Circuit.Emit.EffectLower.lowerAir nm FS_WIDTH FS_PI_COUNT [] (closingFsAirOn As d st)

/-- ⚑⚑ **THE EMITTED WELDED DESCRIPTOR.** The `sg`-free manifest, the routed algebra, and `delta`
pinned to the pair a transcript absorb published. -/
def closingFsDesc (Gs : List Pt3) (u : List Nat) (z1 b0 z2 : Nat)
    (delta U H st : Pt3) (n : Nat) : EffectVmDescriptor2 :=
  closingFsDescNamed "dregg-mina-wrap-closing-fs::v1"
    (closingAddends Gs u z1 b0 z2 delta U H n) (redPtP delta) st

theorem closingFsDesc_name (Gs : List Pt3) (u : List Nat) (z1 b0 z2 : Nat)
    (delta U H st : Pt3) (n : Nat) :
    (closingFsDesc Gs u z1 b0 z2 delta U H st n).name = "dregg-mina-wrap-closing-fs::v1" := rfl

/-- ⚑ **THE PIN IS THE MANIFEST'S OWN SLOT 0.** `closingFsDesc` pins `redPtP delta`, which
`the_closing_manifest_head_is_delta_then_bU_then_zH` proves is manifest entry `0` — so the weld and
the routing name the same value and a disagreement between them is impossible by construction
rather than by a test. -/
theorem the_weld_pins_the_manifests_own_delta_slot
    (Gs : List Pt3) (u : List Nat) (z1 b0 z2 : Nat) (delta U H : Pt3) (n : Nat) :
    (closingAddends Gs u z1 b0 z2 delta U H n).getD 0 (0, 0, 0) = redPtP delta := rfl

/-- ⚑ **THE WELD IS 130 LEGS, AT EVERY MANIFEST AND EVERY TRANSCRIPT STATE.** 64 delta pins, 32
affine pins, the guard gate, 32 PI pins and ONE `proof_bind`. Stated on the LEG list because that
is the object whose length is independent of `d` and `st`; `closingFsDesc_constraint_count` is the
emitted-bytes twin at a concrete pair. -/
theorem the_weld_is_one_hundred_thirty_legs (As : List Pt3) (d st : Pt3) :
    (closingFsAirOn As d st).legs.length = closingRoutedAir.legs.length + 130
    ∧ (deltaPinLegs d).length = 64 ∧ deltaAffineLegs.length = 32
    ∧ trOutPinLegs.length = 32 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [closingFsAirOn, deltaPinLegs, deltaAffineLegs, trOutPinLegs, SK]

/-- `4 476 + 96 + 192 + 64 + 3` from `-srs`, plus the weld's 130. At a CONCRETE `(d, st)` because
`decide` needs a closed term; the general fact is `the_weld_is_one_hundred_thirty_legs`. -/
theorem closingFsDesc_constraint_count :
    (closingFsDescNamed "x" [] (0, 0, 0) (0, 0, 0)).constraints.length
      = 4476 + 96 + 192 + 64 + 3 + 64 + 32 + 1 + 32 + 1 := by decide

theorem closingFsDesc_width (As : List Pt3) (d st : Pt3) :
    (closingFsDescNamed "x" As d st).traceWidth = 3091 := rfl

theorem closingFsDesc_piCount (As : List Pt3) (d st : Pt3) :
    (closingFsDescNamed "x" As d st).piCount = 224 := rfl

/-- ⚑ **A NAME IS A KEY** — and this cone now has SEVEN descriptors over one algebra shape. -/
theorem the_welded_descriptor_does_not_share_a_name
    (Gs : List Pt3) (u : List Nat) (z1 b0 z2 : Nat) (delta U H st : Pt3) (n : Nat) :
    (closingFsDesc Gs u z1 b0 z2 delta U H st n).name ≠ closingSegDesc.name
    ∧ (closingFsDesc Gs u z1 b0 z2 delta U H st n).name ≠ closingFinalDesc.name
    ∧ (closingFsDesc Gs u z1 b0 z2 delta U H st n).name
        ≠ (closingSrsDesc Gs u z1 b0 z2 delta U H n).name := by
  rw [closingFsDesc_name, closingSrsDesc_name]
  refine ⟨by decide, by decide, by decide⟩

/-- ⚑⚑ **AND THE WELD IS VISIBLE IN THE SHAPE.** `-fs` and `-srs` do NOT have the same constraint
count, width or PI count — unlike the Pallas/Vesta pair of §2, where only the modulus separated
them. A shape check DOES tell a welded descriptor from an unwelded one. -/
theorem the_weld_is_visible_in_the_shape (As : List Pt3) (d st : Pt3) :
    (closingFsDescNamed "x" As d st).traceWidth ≠ (closingRoutedDescNamed "x" As).traceWidth
    ∧ (closingFsDescNamed "x" As d st).piCount ≠ (closingRoutedDescNamed "x" As).piCount
    ∧ (closingFsDescNamed "x" [] (0, 0, 0) (0, 0, 0)).constraints.length
        ≠ (closingRoutedDescNamed "x" ([] : List Pt3)).constraints.length := by
  refine ⟨?_, ?_, ?_⟩
  · rw [closingFsDesc_width, closingRoutedDesc_width]; decide
  · show (224 : Nat) ≠ 192; decide
  · rw [closingFsDesc_constraint_count, closingRoutedDesc_constraint_count]; decide

#assert_axioms closing_combined_is_kimchis_fold
#assert_axioms the_combined_check_is_constant_in_sg
#assert_axioms the_eliminated_check_is_the_substituted_opening
#assert_axioms the_eliminated_check_is_the_conjunction
#assert_axioms the_eliminated_check_has_no_surjective_sg_map
#assert_axioms the_eliminated_check_still_refutes
#assert_axioms the_eliminated_check_is_satisfiable
#assert_axioms the_free_sg_moves_neither_pole

#assert_axioms closingFinalAir_extends_closingSegAir
#assert_axioms closingSegAir_is_the_thread_row_plus_pins
#assert_axioms closingSegAir_mainRailOk
#assert_axioms closingFinalAir_mainRailOk
#assert_axioms the_closing_discharge_is_sixty_four_last_row_gates
#assert_axioms closingSegDesc_constraint_count
#assert_axioms closingFinalDesc_constraint_count
#assert_axioms the_closing_descriptors_do_not_share_a_name
#assert_axioms the_count_cannot_tell_the_two_blocks_apart

#assert_axioms terminalClosingAccumulator_forces
#assert_axioms closing_discharge_forced

#assert_axioms redPtP_lt
#assert_axioms the_closing_manifest_carries_no_sg_slot
#assert_axioms the_closing_manifest_head_is_delta_then_bU_then_zH
#assert_axioms srsSlots_length
#assert_axioms srsSlot_at
#assert_axioms the_manifest_tail_is_the_srs_slots
#assert_axioms the_srs_slot_is_the_scaled_generator
#assert_axioms every_closing_slot_is_canonical
#assert_axioms declAddend_of_closingAddends

#assert_axioms the_closing_legs_do_not_depend_on_the_manifest
#assert_axioms closingRoutedAir_extends_closingFinalAir
#assert_axioms closingRoutedAir_mainRailOk
#assert_axioms closingSrsDesc_name
#assert_axioms the_closing_srs_descriptor_differs_only_in_its_name_and_its_manifest
#assert_axioms closingRoutedDesc_constraint_count
#assert_axioms only_the_closing_routing_leg_targets_the_addend_table

#assert_axioms closingResidualAt_is_the_published_shape
#assert_axioms the_delta_shift_is_invisible
#assert_axioms the_check_sees_only_the_sum
#assert_axioms the_whole_shift_orbit_is_admitted
#assert_axioms the_shift_orbit_is_not_a_point
#assert_axioms a_delta_move_without_the_matching_accumulator_move_refutes

#assert_axioms the_weld_costs_forty_two_columns_and_thirty_two_public_inputs
#assert_axioms closingFsAir_extends_closingRoutedAir
#assert_axioms closingFsAir_mainRailOk
#assert_axioms the_weld_commit_is_the_absorb_programs_public_input_vector
#assert_axioms the_weld_names_the_chains_own_addend_cells
#assert_axioms the_delta_pin_refuses_a_moved_limb
#assert_axioms the_delta_pin_admits_the_absorbed_pair
#assert_axioms the_shift_moves_a_pinned_limb
#assert_axioms closingFsDesc_name
#assert_axioms the_weld_pins_the_manifests_own_delta_slot
#assert_axioms the_weld_is_one_hundred_thirty_legs
#assert_axioms closingFsDesc_constraint_count
#assert_axioms the_welded_descriptor_does_not_share_a_name
#assert_axioms the_weld_is_visible_in_the_shape

end Dregg2.Circuit.Emit.MinaWrapClosingAir
