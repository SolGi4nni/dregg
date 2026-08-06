/-
# Dregg2.Circuit.Emit.KimchiWrapMainPins05 — §15f — W-XHAT (the public-input MSM reductions)

⚑ **ONE MODULE OF THE `KimchiWrapMain` SPLIT.** The namespace is unchanged
(`Dregg2.Circuit.Emit.KimchiWrapMain`), so nothing here is renamed and no consumer moves; the file
boundary exists only so a pin re-elaborates without the emitter's 5,000 lines of `def` behind it.
The in-file rule that keeps it stable is the step side's: **a `def` goes in `…Core`/`…Fixture`, a
pin goes in its section's `…PinsNN`.**

⚠ The `set_option` block below is VERBATIM `KimchiWrapMain`'s and must stay that way. `set_option`
does not cross an import, and `KimchiWrapFinalizeSpongeGate` shipped four proofs as `sorryAx` --
each still landing in the environment with the right statement -- because a split dropped it.

Pins only. Every `def` this section had is in `…Fixture`; the namespace-wide axiom pin is in the
`KimchiWrapMain` umbrella, which imports every one of these.

-/
import Dregg2.Circuit.Emit.KimchiWrapMainFixture

namespace Dregg2.Circuit.Emit.KimchiWrapMain
open Dregg2.Circuit.Emit.KimchiTarget (KGateType K_PERMUTS)
open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.WitnessBuilder
  (VarEnv GateWitness gridAt envIndex envLookupAt gateVarWitnessAt compose)
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaPoseidonFq (fqParams rcsQ mdsQ)

set_option autoImplicit false
set_option maxRecDepth 100000
-- ⚠ §12/§14b reduce whole sponge trajectories IN THE KERNEL (`rfl`/`decide`), which is strictly
-- stronger than the `#guard`s they replace and correspondingly slower to elaborate.
set_option maxHeartbeats 4000000

/-! ### §15f — ⚑ **W-XHAT'S PINS, AS NAMED THEOREMS.**

Read off the EMITTED row list wherever the claim is about a row. Every one is kernel-clean and
accounted for by `#assert_namespace_axioms` below; there are no new `#guard`s in this section.

⚠ These reduce the smoke instance's x_hat rows, which is 77 five-bit chunks of Vesta ladder in the
kernel. That is the reason there are NINE of them and not thirty: each one is a real reduction of
the same object, and the marginal fact is not worth the marginal minute. MEASURED — the nine cost
+0.55 GiB of peak elaboration RSS (8.64 → 9.19 GiB) and no wall time at all. -/

/-- ⚑ **THE MEMO'S OBLIGATION, IN THE KERNEL.** `shapeSmoke.xhatXY` — the pair `schedule` hands the
transcript at `wrap_verifier.ml:617` — IS §15's MSM output. Without this the field would be a
fixture with a good docstring. (The wrap shape's copy is discharged by `EmitWrapMainJson`'s refusal
at every emission; 1805 chunks is out of the kernel's reach, and §24's is the file's one
`native_decide`.) -/
theorem xhat_smoke_shape_absorbs_the_msm_output :
    shapeSmoke.xhatXY = xhatOutOf shapeSmoke.xhatEntries := by rfl

/-- ⚑ **AND IT IS A DIFFERENT OBJECT FROM THE ONE THIS FILE USED TO ABSORB.** `RC_XHAT` is a real
accepted proof's public-input commitment, which stood in for `x_hat` through five rungs. The derived
pair is not it — so `w6_xhat` changed the transcript rather than confirming it, and every challenge
below the absorb moved. Saying that out loud is the point: a rung that "derives" a value it already
had would be deriving nothing. -/
theorem xhat_derived_is_not_the_old_fixture :
    shapeSmoke.xhatXY.1 ≠ RC_XHAT.getD 0 0 ∧ shapeSmoke.xhatXY.2 ≠ RC_XHAT.getD 1 0
    ∧ shapeWrap.xhatXY.1 ≠ RC_XHAT.getD 0 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ⚑ **DEFECT CLASS 1, IN A NEW PLACE AND IN THE PLACE THE STEP SIDE FOUND IT.**
`scale_fast_unpack` opens `let acc = ref (add_fast base base)` / `let n_acc = ref Field.zero`
(`plonk_curve_ops.ml:157-158`). Doubling is a bijection on the group, so a FREE `acc₀` lets a prover
steer the ladder's output to any point at all, and a free `n₀` lets him choose which bit vector the
ladder actually multiplied by. Per ladder this reads BOTH off the emitted rows: a `CompleteAdd` whose
two input point-pairs are the base's own cells and whose output is `acc₀`, and a `Generic` half
pinning `n₀` to zero. -/
theorem xhat_every_ladder_seed_is_pinned :
    (xhLadders shapeSmoke).all (fun k =>
      xhRows.any (fun w => w.kind == KGateType.completeAdd
        && w.perm == [ some (xA shapeSmoke tKey.sp k 0), some (xA shapeSmoke tKey.sp k 1)
                     , some (xA shapeSmoke tKey.sp k 0), some (xA shapeSmoke tKey.sp k 1)
                     , some (xAccX shapeSmoke tKey.sp k 0), some (xAccY shapeSmoke tKey.sp k 0)
                     , none ])
      && xhRows.any (fun w => w.kind == KGateType.generic
           && w.perm.contains (some (xCnt shapeSmoke tKey.sp k 0))
           && w.coeffs.contains 0)) = true := by decide

/-- ⚑ **DEFECT CLASS 2, BOTH HALVES, INSIDE THE LADDER.** `scale_fast2` asserts the top bits of
`s_div_2` zero (`plonk_curve_ops.ml:262-265`) — ONE bit at width 255 and THREE at width 128, because
a 128-bit entry's ladder actually runs at 130. Those cells live in chunk 0's NEXT row, which in the
`VarBaseMul` witness layout is ADVICE; an advice cell is in no σ class and cannot be asserted. This
says the emitter moved every one of them into a PERMUTATION column AND that a `Generic` half pins it
to zero. Emitting the split without them is the containment §13 refused to ship. -/
theorem xhat_top_bits_are_range_checked :
    (xhLadders shapeSmoke).all (fun k =>
      (List.range (xhatTopZeros (xhAt shapeSmoke k))).all (fun tt =>
        xhRows.any (fun w => w.kind == KGateType.zero
          && w.perm.contains (some (xZb shapeSmoke tKey.sp k tt)))
        && xhRows.any (fun w => w.kind == KGateType.generic
             && w.perm.contains (some (xZb shapeSmoke tKey.sp k tt))))) = true
  ∧ ((xhLadders shapeSmoke).map (fun k => xhatTopZeros (xhAt shapeSmoke k))) = [1, 3, 1] := by
  refine ⟨?_, ?_⟩ <;> decide

/-- ⚑ **DEFECT CLASS 4: NO BASE IS A FREE WITNESS.** Every entry's base — and every correction, and
`Generators.h` — is pinned by a `Generic` constant row to the value `MinaStepSrsLagrange` holds.
Before this rung the wrap side emitted no curve base at all; the step side's R3 spent a night with
all forty free.

⚠ SAY THE PIN'S REACH EXACTLY. `MinaStepSrsLagrangePin` closes `SRS::<Pallas>::create(16).g` against
the devnet blockchain Wrap SRS's **first sixteen generators, thirty-two coordinates**, by `decide`.
It does NOT observe the Vesta basis these bases actually come from (depth 65536); what it
establishes is that `SRS::create` — the one deterministic generic function both halves go through —
reproduces Mina's generators where an independent devnet dump exists to check it against. The step
from there to `LAGRANGE_XY` is an argument about that function, not a checked equality, and the pin
module says so in its own header. -/
theorem xhat_every_base_and_correction_is_pinned :
    (List.range (xhN shapeSmoke)).all (fun k =>
      xhHasConstRow (xA shapeSmoke tKey.sp k 0) (xA shapeSmoke tKey.sp k 1)
        (xhatBase (xhAt shapeSmoke k))) = true
  ∧ (xhLadders shapeSmoke).all (fun k =>
      xhHasConstRow (xA shapeSmoke tKey.sp k 2) (xA shapeSmoke tKey.sp k 3)
        (xhatCorr (xhAt shapeSmoke k))) = true
  ∧ xhHasConstRow (xhHVar shapeSmoke tKey.sp).1 (xhHVar shapeSmoke tKey.sp).2 XHAT_H = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ⚑ **THE CLOSING TIE.** `x_hat blinding`'s `CompleteAdd` writes its output into the very cells the
transcript absorbs at `wrap_verifier.ml:617` — not a σ class BETWEEN two variables but the same two
variables, which is the strongest form the tie can take. So the sponge cannot be fed an `x_hat` the
MSM did not produce. -/
theorem xhat_output_is_the_absorbed_word :
    ((xhRows.filter (fun w => w.kind == KGateType.completeAdd)).getLast?.map (fun w =>
        (w.perm.getD 4 none, w.perm.getD 5 none)))
      = some
          (some ((tKey.sp.evs.filter (fun e => e.isAbs && e.tag == T_XHAT)).getD 0 default).wordV,
           some ((tKey.sp.evs.filter (fun e => e.isAbs && e.tag == T_XHAT)).getD 1 default).wordV)
    := by decide

/-- ⚑ **DEFECT CLASS 3: THE CENSUS DID NOT MOVE, AND THE ENTRY SAYS WHY.** `x_hat` is still on
`WRAP_UNCONSUMED` because W-XHAT's 67 scalars are `exists ~request:Req.Proof_state`'s free witnesses
(§2c, §15c). Eight entries before this rung, eight after. -/
theorem xhat_does_not_move_the_unconsumed_census :
    WRAP_UNCONSUMED.length = 8
    ∧ WRAP_UNCONSUMED.getD 1 ""
        = "x_hat — MSM EMITTED at w6_xhat (§15); its 67 SCALARS are W-PREV's packed statement \
           words, and 64 of them are still free" := by
  refine ⟨rfl, ?_⟩
  decide

/-- The `w6_xhat` rung is a strict superset of `w5_key` and its length is the sum of its parts, the
WIRED and UNWIRED circuits differ ONLY in the probe rows' permutation columns, and `placeChecked`
accepts it with no inert public word. §12b's shape, at the rung that first emits curve gates. -/
theorem xhat_rung_is_a_ladder_step_and_places :
    (rungRows tKey .xhat true).length
      = (rungRows tKey .key true).length + xhRows.length
    ∧ (rungRows tKey .key true).length < (rungRows tKey .xhat true).length
    ∧ (((rungRows tKey .xhat true).zip (rungRows tKey .xhat false)).filter
        (fun p => p.1.perm != p.2.perm)).length
        = ((rungRows tKey .xhat true).filter (fun r => r.probe)).length
    ∧ refusalOf shapeSmoke .xhat (rungPub shapeSmoke .xhat)
        (wrapGates (rungRows tKey .xhat true)) = none
    ∧ inertSlotsAt shapeSmoke .xhat (wrapGates (rungRows tKey .xhat true))
        = wrapInertOk shapeSmoke .xhat := by
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  decide

/-- ⚑ **THE GATE CENSUS OF THE SUB-CIRCUIT.** Two rows per five-bit chunk (`VarBaseMul` + its `Zero`
tail, `varbasemul.rs:135-140`), and a `CompleteAdd` for every `add_fast` upstream makes: one seed and
one `G.negate` adjust and one fold add per ladder, one per `Cond_add`, `m − 1` for the correction
reduce, and one for `x_hat blinding`. A row-set that quietly stopped emitting one of them reds
here rather than in a conformance report six weeks out. -/
theorem xhat_gate_census :
    (xhRows.filter (fun r => r.kind == KGateType.varBaseMul)).length
      = xhTotalChunks shapeSmoke
    ∧ (xhRows.filter (fun r => r.kind == KGateType.completeAdd)).length
      = 3 * (xhLadders shapeSmoke).length
        + (xhN shapeSmoke - (xhLadders shapeSmoke).length)
        + ((xhLadders shapeSmoke).length - 1) + 1
    ∧ (xhRows.filter (fun r => r.kind == KGateType.poseidon)).length = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end Dregg2.Circuit.Emit.KimchiWrapMain
