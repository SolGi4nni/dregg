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

* `src/lib/pickles/wrap_verifier.ml`, `check_bulletproof` at **`:564`**; the equation is the
  comment at **`:600`** — *`(* c Q + delta = z1 (G + b U) + z2 H *)`* — with `lhs = endo q c +
  delta` (`:601-604`) and `rhs = z_1·(challenge_polynomial_commitment + b·U) + z_2·H`
  (`:605-613`). ⚠ `challenge_polynomial_commitment` (= `sg`), `z_1` and `z_2` arrive as fields of
  the `openings_proof` record: **free in the circuit, and that is FAITHFUL to upstream.** The gap
  was never that Mina fails to bind `sg`; it is that Mina binds it SOMEWHERE ELSE and dregg
  bound it nowhere.

* `poly-commitment/src/ipa.rs`, `SRS::verify`. Two independent randomisers are sampled at
  **`:356-357`** (`rand_base`, `sg_rand_base`) and the two statements are folded into ONE terminal
  MSM. The `sg` base carries scalar **`neg_rand_base_i * opening.z1 - sg_rand_base_i`**
  (**`:410-411`**), and the SRS bases carry `+ sg_rand_base_i · s_i` (**`:413-425`**), under the
  comment *"we also add `-sg_rand_base_i * G` to check correctness of sg"* (`:409`). That is the
  leg this file brings in. Upstream runs the same relation out-of-circuit on the Step side as
  `batch_dlog_accumulator_check`; on the Tock/Wrap side it is folded into `SRS::verify` itself.

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
3. **The challenges `u⃗` are not bound to a transcript by anything here**, in circuit exactly as
   natively. `MinaAccumulatorAir` residual 2, inherited unchanged.
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

end Dregg2.Circuit.Emit.MinaWrapClosingAir
