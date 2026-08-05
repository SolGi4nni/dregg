/-
# `Dregg2.Circuit.Emit.MinaWrapXiAggregateMsm` — the ξ-AGGREGATE, with the SCALAR MULTIPLICATION
INSIDE THE CIRCUIT.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored AIR.** The emitted object is
`PastaMsmBucketed.bucketedRowDesc N_PAD NBITS C GENS SCAL` — an `EffectVmDescriptor2` built by a
Lean `def` out of Lean-authored `VmConstraint2`s, whose first 42 constraints are
`PastaMsmWindowed.rowGates` verbatim (`bucketedRowDesc_extends_rowGates`), i.e. the same
`PastaCurveComplete.pallasCompleteAdd` the whole Pasta cone shares. This file authors **no new
gate**: it names a curve, a window, a generator list and a scalar list, and it proves things about
the resulting artifact. Rust parses the descriptor, fills trace CELLS and runs the deployed prover.
House Law #1.

## ⚑ THE DEFECT THIS FILE CLOSES, stated as it was found

`MinaWrapCommitStages.xiAggDesc` folds 47 terms — at full term count, with the real block's
points, against o1-labs' own aggregate. But its ROM immediates are `XI_TERMS`, and

```
def XI_TERMS : List Aff :=
  (List.range 47).map (fun i => toAff (MinaWrapGroupGate.smul (qpow XI i) …))
```

is **PRE-SCALED**: `MinaWrapGroupGate.smul` is a Lean REFERENCE FUNCTION, not a gate. The scalar
multiplication — the entire content of an MSM — happened before the descriptor existed. What that
descriptor forces is *"these 47 hardcoded points, added in this order, give this hardcoded point."*
A prover that wanted a different aggregate would change the ROM, and the ROM is the thing the
verifier reads.

Here the scalars are **not** applied in advance. `SCAL` carries the 47 powers of the block's real
`ξ` as NUMBERS; `GENS` carries the 47 unscaled commitments. The descriptor's `T_COVER` permutation
forces every `(window, generator)` pair to be consumed exactly once at the sweep level equal to its
declared digit, and the fused running sum

  `Σ_i s_i·P_i = Σ_{d=1}^{D} ( Σ_{i : d_i ≥ d} P_i )`

makes the accumulation the trace's own work. **`s_i·P_i` is computed by the AIR, not handed to it.**

## ⚠ THE GAPS THIS INHERITS, and they are inherited KNOWINGLY

Nothing below repairs these; they belong to `PastaMsmBucketed` and they travel with it.

1. **The digits are DECLARED, not DERIVED.** `T_COVER`'s manifest carries `digit_w(s_i)` as a
   descriptor parameter, so the artifact is SCALAR-SPECIALISED: it forces the trace to compute
   `Σ s_i·P_i` for the `s` the descriptor names, and says nothing about where that `s` came from.
   ⚑ What §2 *does* close is the weaker thing that was actually at risk: the declared digits
   **recompose to the real ξ powers with no truncation** (`the_declared_digits_recompose`), so a
   window count that silently dropped the top bits of a 255-bit scalar is refuted rather than
   assumed. Deriving `ξ^i` from `ξ` in-circuit is `MinaWrapCommitStages.xiChainProg`'s 46 multiplies
   — a DIFFERENT emitted object, and the two are not yet welded to each other. §4 prices that.
2. **The row template is `pallasCompleteAdd`.** Correct for this cone — the ξ-aggregate is a WRAP
   commitment combination over Pallas — but the Vesta swap `bucketedRowDescVesta` offers is not
   exercised here.
3. ⚑ **The rows are denominated in the UNSOUND `fpMulCore`.** `PastaMsmBucketed` §7.2 says so, and
   it must be repeated here rather than absorbed, because the cone this file joins
   (`MinaWrapCommitStages`) is emitted at `PastaFieldSound`. **That is a downgrade, and it is a
   downgrade to be STATED, not absorbed:** the ξ-aggregate now scales in-circuit at the cost of
   moving from the sound multiply to the oversized one. The 495-bit gate coefficients are why the
   Rust side must parse through `parse_vm_descriptor2_unsound_oversized`.

## The parameters, and why each is forced rather than chosen

`c = 2`, `nbits = 255`, `n = 59`. §1 proves the trace height is `8192`, a power of two, which the
deployed prover requires AND which a permutation manifest's length must equal. The 12 padding terms
carry scalar `0`; the fused identity's inner sums range over `d ≥ 1`, so a zero-digit term appears
in none of them and contributes nothing — `the_padding_contributes_nothing`.

## Axiom hygiene

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`/`admit`/
`native_decide`. Named theorems, not `#guard`s. NEW file; not imported by the `Dregg2` root, per
house practice for gates. Import line:
`import Dregg2.Circuit.Emit.MinaWrapXiAggregateMsm`
-/
import Dregg2.Circuit.Emit.PastaMsmBucketed
import Dregg2.Circuit.Emit.MinaWrapAggregationGate

namespace Dregg2.Circuit.Emit.MinaWrapXiAggregateMsm

open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2)
open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.PastaCurve (curveB)
open Dregg2.Circuit.Emit.PastaCurveComplete (Oproj projOnCurveM projEqM isInfM)
open Dregg2.Circuit.Emit.MinaWrapGroupGate (Pt smul padd msmComm)
open Dregg2.Circuit.Emit.MinaWrapAggregationGate (XI COMBINE_POINTS COMBINED_GOLD)
open Dregg2.Circuit.Emit.PastaMsmBucketed (windowsOf levelsOf fusedAdds bucketedRows termRows
  winLen scalarDigitC coverManifest srsManifest schedManifest bucketedRowDesc bucketedTables
  SCHED_TUP COVER_TUP SRS_TUP MAX_EP_ROWS MAX_EP_CELLS MAX_EP_ARITY)

set_option autoImplicit false
set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

/-! ## §1 — THE PARAMETERS, and the power-of-two height they are chosen to hit. -/

/-- The block's polyscale challenge, `q`-arithmetic. ⚑ `MinaWrapCommitStages`'s
`the_base_field_reduction_of_xi_squared_is_a_different_scalar` is the refutation that reading these
powers in the BASE field gives different scalars — the classic Pasta error, caught here once
already. -/
def qmul (x y : Nat) : Nat := (x * y) % PastaField.qN

def qpow (x : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => qmul (qpow x n) x

/-- The 47 real terms `combine_commitments` feeds the terminal MSM. -/
def N_REAL : Nat := 47

/-- The padded term count: 12 further terms at scalar `0`, so the height is a power of two. -/
def N_PAD : Nat := 59

/-- The window width. -/
def C : Nat := 2

/-- ⚑ **FULL-WIDTH Pasta scalars.** Not a reduced plane count — the ξ powers are 255-bit scalar
field elements and they enter at 255 bits. -/
def NBITS : Nat := 255

/-- The 47 powers `(ξ⁰, …, ξ⁴⁶)`, then 12 zeros. -/
def SCAL : List Nat :=
  ((List.range N_REAL).map (qpow XI)) ++ List.replicate (N_PAD - N_REAL) 0

/-- The 47 real commitments, then 12 repeats of the first — which the zero scalars annihilate. -/
def GENS : List Pt :=
  COMBINE_POINTS ++ List.replicate (N_PAD - N_REAL) (COMBINE_POINTS.getD 0 Oproj)

theorem lists_are_the_padded_length : SCAL.length = N_PAD ∧ GENS.length = N_PAD := by decide

/-- ⚑ **THE HEIGHT IS A POWER OF TWO**, which is what the whole padding exists for: the deployed
prover refuses a non-power-of-two base trace, AND an `exactPublicRows` manifest is a PERMUTATION,
so its length IS the trace height. `128` windows of `64` rows. -/
theorem the_height_is_eight_thousand_one_hundred_ninety_two :
    bucketedRows N_PAD NBITS C = 8192
      ∧ windowsOf NBITS C = 128 ∧ winLen N_PAD C = 64 ∧ levelsOf C = 3 := by decide

theorem the_height_is_a_power_of_two : bucketedRows N_PAD NBITS C = 2 ^ 13 := by decide

/-- ⚑ **AND THE WINDOWS COVER THE WHOLE SCALAR.** `128 · 2 = 256 ≥ 255`. This is the check that a
window count silently dropping a 255-bit scalar's top bits would fail — the digits are declared, so
nothing else would have noticed. -/
theorem the_windows_cover_the_whole_scalar : NBITS ≤ windowsOf NBITS C * C := by decide

/-! ## §2 — WHAT THE DESCRIPTOR DECLARES, welded to the block's own numbers. -/

/-- The emitted artifact. -/
def xiAggMsmDesc : EffectVmDescriptor2 := bucketedRowDesc N_PAD NBITS C GENS SCAL

/-- Recompose a term's declared `c`-bit digits, MSB-first, over every window the descriptor has. -/
def recompose (i : Nat) : Nat :=
  (List.range (windowsOf NBITS C)).foldl
    (fun acc w => acc * 2 ^ C + scalarDigitC SCAL NBITS C w i) 0

/-- ⚑ **THE DECLARED DIGITS RECOMPOSE TO THE DECLARED SCALARS — ALL 59, NO TRUNCATION.**

`T_COVER`'s manifest is the only place the scalars appear in the artifact, and it carries DIGITS.
This says those digits are the base-`2^C` digits of exactly the numbers `SCAL` names, over the
window count the descriptor actually has. Without it, "the digits are declared" would also permit
"the digits are the declared scalars' LOW 254 bits", which is a different MSM with the same
descriptor shape and no green anywhere would move. -/
theorem the_declared_digits_recompose :
    ((List.range N_PAD).all (fun i => decide (recompose i = SCAL.getD i 0))) = true := by decide

/-- ⚑ **AND THE DECLARED SCALARS ARE THE REAL ξ POWERS.** The first 47 entries are `ξ⁰ … ξ⁴⁶` at
the block's own challenge, in `q`. -/
theorem the_declared_scalars_are_the_xi_powers :
    ((List.range N_REAL).all (fun i => decide (SCAL.getD i 0 = qpow XI i))) = true := by decide

/-- ⚑ **AND THE PADDING IS INERT.** Every padding term carries scalar `0`, hence digit `0` in every
window; the fused identity's inner sums range over `d ≥ 1`, so a zero-digit term is in none of them.
The 12 extra rows per window buy the power-of-two height and nothing else. -/
theorem the_padding_contributes_nothing :
    ((List.range (N_PAD - N_REAL)).all
      (fun k => decide (SCAL.getD (N_REAL + k) 0 = 0)
        && ((List.range (windowsOf NBITS C)).all
              (fun w => decide (scalarDigitC SCAL NBITS C w (N_REAL + k) = 0))))) = true := by
  decide

/-- ⚑ **AND THE DECLARED GENERATORS ARE THE BLOCK'S OWN COMMITMENTS.** The first 47 entries of
`GENS` are `MinaWrapAggregationGate.COMBINE_POINTS` — the 2 recursion, `public_comm`, `ft_comm`,
`Z`, 6 index, 15 witness, 15 coefficient and 6 sigma commitments of Mina devnet block 539508. -/
theorem the_declared_generators_are_the_block_commitments :
    ((List.range N_REAL).all
      (fun i => decide (GENS.getD i Oproj = COMBINE_POINTS.getD i Oproj))) = true := by decide

/-- Every declared generator is a real Pallas point. -/
theorem every_declared_generator_is_on_pallas :
    (GENS.all (projOnCurveM pN curveB)) = true := by decide

/-! ## §3 — ⚑ THE WELD TO `COMBINED_GOLD`, AS A NAMED THEOREM.

Until this section the four folds of `MinaWrapCommitStages` matched o1-labs by **two adjacent
`IO.println`s** in `EmitCommitStages.lean` — a human reading two lines of stdout and agreeing they
were the same digits. A sibling lane's verdict on exactly that shape, and the reason it fixed a
transcription it had already checked by hand: *"one wrong digit would have given a self-consistent
tree — Lean proving the program computes ITS constants, the harness pinning ITS digest, every gate
green."* The printlns are deleted; these are what replaced them. -/

/-- The MSM the descriptor NAMES: `Σ SCAL_i · GENS_i`, by `MinaWrapGroupGate.msmComm`, which is
`PolyComm::multi_scalar_mul` in shape. -/
def declaredMsm : Pt := msmComm (SCAL.zip GENS)

/-- ⚑ **THE MSM THIS DESCRIPTOR NAMES IS o1-LABS' OWN AGGREGATE.**

`COMBINED_GOLD` is `Σᵢ ξⁱ·Cᵢ` as o1-labs' `PolyComm::multi_scalar_mul` computed it on Mina devnet
block 539508. This is 47 full 255-bit RCB ladders and 59 complete adds in the Lean kernel, over the
padded lists the DESCRIPTOR carries — not over a tidied copy of them.

⚑ It is also an INDEPENDENT route to that point. `MinaWrapAggregationGate.combinedComm_reproduces_
kimchi` reaches `COMBINED_GOLD` by `chunkedComm`, a HORNER fold (`res := res·ξ + c`) that never
forms a power of ξ at all. This one forms all 47 powers explicitly and multiplies each into its own
generator. Two different computations, one point: that is a gate, where a constant checked against
its own definition would have been decoration. -/
theorem the_declared_msm_is_o1_labs_aggregate :
    projEqM pN declaredMsm COMBINED_GOLD = true := by decide

/-- ⚑ …and it is a FINITE point on Pallas, so `projEqM` is not agreeing about the identity. -/
theorem the_aggregate_is_a_real_finite_pallas_point :
    projOnCurveM pN curveB COMBINED_GOLD = true ∧ isInfM pN COMBINED_GOLD = false := by decide

/-- ⚑ **AND THE WELD IS REFUTABLE.** One added to the challenge gives a different aggregate — so
`the_declared_msm_is_o1_labs_aggregate` is a claim the block's data can falsify, not a tautology
about whatever `declaredMsm` happens to be. -/
theorem a_perturbed_challenge_misses_the_aggregate :
    projEqM pN
      (msmComm ((((List.range N_REAL).map (qpow (XI + 1)))
        ++ List.replicate (N_PAD - N_REAL) 0).zip GENS)) COMBINED_GOLD = false := by decide

/-- ⚑ **AND A DROPPED TERM MISSES IT TOO.** The last real commitment's scalar zeroed — the shape a
prover that quietly omitted one generator would produce. -/
theorem a_dropped_term_misses_the_aggregate :
    projEqM pN (msmComm ((SCAL.set (N_REAL - 1) 0).zip GENS)) COMBINED_GOLD = false := by decide

/-! ## §4 — WHAT STILL HOLDS A VALUE NOTHING COMPUTES, at CURRENT resolution.

Read this before citing anything above.

⚑ **`ξ` ITSELF.** `SCAL` is the 47 powers as descriptor constants. `MinaWrapCommitStages.xiChainProg`
computes those same 47 powers IN-CIRCUIT from `ξ` as a public input, in 46 Pasta multiplies at
`qLimb` — but that is a SECOND emitted object, and nothing yet forces the powers the chain computes
to be the digits this manifest declares. The weld is a public-input equality between two descriptors
and it is NOT built. Until it is, this artifact scales by 47 numbers a verifier must be told.

⚑ **AND `ξ` IS ITSELF A TRANSCRIPT OUTPUT.** Even welded to the chain, `ξ` enters as a public input;
binding it to the Fq sponge's squeeze is `MinaWrapVerifierSponge`'s cone, not this one.

⚑ **THE UNSOUND MULTIPLY.** Stated in the header and repeated because it is the kind of thing that
gets absorbed: these rows are `fpMulCore`, not `PastaFieldSound`. `PastaMsmBucketed` §6d prices the
sound row at over a hundredfold the gate count. -/

/-- The declared cell budget, so the deployed caps are checked rather than assumed. -/
theorem the_manifests_fit_the_deployed_caps :
    bucketedRows N_PAD NBITS C ≤ MAX_EP_ROWS
      ∧ SCHED_TUP < MAX_EP_ARITY ∧ COVER_TUP < MAX_EP_ARITY ∧ SRS_TUP < MAX_EP_ARITY
      ∧ bucketedRows N_PAD NBITS C * (SCHED_TUP + COVER_TUP + SRS_TUP) ≤ MAX_EP_CELLS := by
  decide

/-- ⚑ **THE TERM ROWS ARE 92% OF THE TRACE**, and the rest is the fused collapse — the census that
says the padding is a rounding error and the object is really doing 7 552 conditional adds. -/
theorem the_term_rows_dominate :
    termRows N_PAD NBITS C = 7552 ∧ 100 * termRows N_PAD NBITS C > 92 * bucketedRows N_PAD NBITS C
      := by decide

/-- ⚑ **AND THE REAL WORK IS 47/59 OF THAT.** The 12 padding terms occupy 1 536 of the 7 552 term
rows; a reader pricing this object should price the real content. -/
theorem the_real_terms_are_forty_seven_fifty_ninths :
    windowsOf NBITS C * N_REAL = 6016 ∧ windowsOf NBITS C * (N_PAD - N_REAL) = 1536 := by decide

#assert_axioms lists_are_the_padded_length
#assert_axioms the_height_is_eight_thousand_one_hundred_ninety_two
#assert_axioms the_height_is_a_power_of_two
#assert_axioms the_windows_cover_the_whole_scalar
#assert_axioms the_declared_digits_recompose
#assert_axioms the_declared_scalars_are_the_xi_powers
#assert_axioms the_padding_contributes_nothing
#assert_axioms the_declared_generators_are_the_block_commitments
#assert_axioms every_declared_generator_is_on_pallas
#assert_axioms the_declared_msm_is_o1_labs_aggregate
#assert_axioms the_aggregate_is_a_real_finite_pallas_point
#assert_axioms a_perturbed_challenge_misses_the_aggregate
#assert_axioms a_dropped_term_misses_the_aggregate
#assert_axioms the_manifests_fit_the_deployed_caps
#assert_axioms the_term_rows_dominate
#assert_axioms the_real_terms_are_forty_seven_fifty_ninths

end Dregg2.Circuit.Emit.MinaWrapXiAggregateMsm
