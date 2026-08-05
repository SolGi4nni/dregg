/-
# Dregg2.Circuit.Emit.KimchiWrapMainPins01 — the CONSTANT PINS (§11, §11b endo scalar, §11c Branch_data.pack, §11d the field)

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

/-! ## §11 — the CONSTANT PINS, each against an INDEPENDENT source.

⚑ Defect class 4: "a constant pinned against its own definition is decoration; two INDEPENDENT
sources are a gate." Each pin below reads a value this file does not own.

### §11a — the Fq Poseidon constants.

The gate coefficients this file emits are `fq_kimchi`'s (`wrap_main_inputs.ml:12-13`,
`sponge/constants.ml:4011` `params_Pasta_q_kimchi`, 3×3 MDS and 55×3 round constants), NOT
`fp_kimchi`'s. A copy-paste of the step side's `rcsN` reds here, and so does a value that is not
reduced mod `qN`. -/

#guard poseidonRowCoeffsQ 0
       = (List.range 5).flatMap (fun i => (rcsQ.getD i []).map (fun n => (n : Int)))
#guard rcsQ.getD 0 [] != Dregg2.Circuit.Emit.PastaPoseidon.rcsN.getD 0 []
#guard mdsQ.getD 0 [] != Dregg2.Circuit.Emit.PastaPoseidon.mdsN.getD 0 []
#guard (poseidonRowCoeffsQ 0).length == 15
#guard (poseidonRowCoeffsQ 10).length == 15
#guard (poseidonRowCoeffsQ 0).all (fun c => decide (c ≥ 0) && decide (c < (qN : Int)))
#guard rcsQ.length == 55
#guard mdsQ.length == 3

/-! ### §11b — the endomorphism scalar.

`ENDO_Q` is `Endo.Step_inner_curve.scalar = Pasta_bindings.Pallas.endo_scalar ()` (`endo.ml:14-21`),
an element of `Backend.Tock.Field = Fq`, and `wrap_verifier.ml:134,143` is where the wrap circuit
scales `a₈` by it. `MinaRealBlockTranscript.ENDO_R` is the SAME Fq element arrived at independently
— the endo a real Mina Wrap proof's `ScalarChallenge::to_field` uses, validated THERE by
REPRODUCING that block's own α, ζ, v and u (`derived_alpha`, `derived_zeta`, `derived_v`,
`derived_u`). Two sources, one value.

⚠ ⚑ **AND GETTING IT BACKWARDS IS EASY, WHICH IS WHY BOTH DIRECTIONS ARE PINNED.**
`wrap_verifier.ml:121` instantiates the `Scalar_challenge` functor with **`Endo.Wrap_inner_curve`**
(Vesta's pair — `base ∈ Fq`, `scalar ∈ Fp`) for the in-circuit `endo`/`endo_inv` curve gadget, while
`:134` uses **`Endo.Step_inner_curve.scalar`** (Pallas's, in Fq) for `to_field_checked`. Two
different endos in one file, and only one of them is a scalar of this circuit's own field. -/

/-- ⚑ `ENDO_Q` against an INDEPENDENT source, both directions, and its defining algebraic property.

  * it IS `MinaRealBlockTranscript.ENDO_R`, arrived at by reproducing a real Mina Wrap proof's own
    α, ζ, v and u;
  * it is NOT the step side's `Endo.Wrap_inner_curve.scalar`, which lives in Fp
    (`bindings_js_test.ml:588-592`) — conflating the two is the `MinaWrapFtEval0Weld` defect, in the
    direction nothing had tested;
  * nor `Endo.Wrap_inner_curve.base`, the Fq element `wrap_verifier.ml:944`/`:121` uses for the CURVE
    endomorphism (`bindings_js_test.ml:583-587`). Both are Fq; only one is a scalar;
  * and it is a NONTRIVIAL cube root of unity in Fq — the property `endo_scalar` HAS
    (`poly-commitment/src/srs.rs:44-60`), checked rather than assumed. -/
theorem endo_q_is_pallas_endo_scalar :
    (ENDO_Q : Nat) = (Dregg2.Circuit.Emit.MinaRealBlockTranscript.ENDO_R).val
    ∧ ENDO_Q ≠ 8503465768106391777493614032514048814691664078728891710322960303815233784505
    ∧ ENDO_Q ≠ 2942865608506852014473558576493638302197734138389222805617480874486368177743
    ∧ qMul (qMul ENDO_Q ENDO_Q) ENDO_Q = 1
    ∧ ENDO_Q ≠ 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ### §11c — `Branch_data.Checked.pack`.

`branch_data.ml:95-101`: `pack = 4·domain_log2 + Impl.Field.pack (Vector.to_list
proofs_verified_mask)`, where `Field.pack` is `project`, LSB-first. ⚑ **The mask term is 0/2/3, not
0/1/2**, because `Prefix_mask.there` is `N0 ↦ [ff;ff] · N1 ↦ [ff;tt] · N2 ↦ [tt;tt]`
(`pickles_base/proofs_verified.ml:75-81`) and `wrap_main.ml:172-180` builds it as
`ones_vector ~first_zero:w |> Vector.rev = [w>1; w>0]`. §9's `maskBit` is that. -/

-- ⚑ **THE INDEPENDENT SOURCE IS A REAL DEVNET WRAP PROOF'S OWN PUBLIC WORD 29.**
-- `MinaWrapPublicCommGate.PUBLIC_INPUT` is the forty Fq words of a Mina devnet block's Wrap proof,
-- decoded off the wire; slot 29 IS `branch_data`. That block was proved at `proofs_verified = N2`
-- (mask `[tt;tt]`, packing to 3) over a `domain_log2 = 16` step domain, so
-- `Branch_data.Checked.pack` must give `3 + 4·16 = 67` — and it does, which is what makes this a
-- gate rather than a constant agreeing with itself.
/-- ⚑ `Branch_data.Checked.pack` against a REAL devnet Wrap proof's own public word 29, and the
0/2/3 mask shape at all three legal widths. A `[1;0]` mask — the packing `0/1/2` would produce — is
NOT reachable from `ones_vector ∘ rev`, which is exactly why `Prefix_mask.back` can `invalid_arg` on
it out of circuit and no gate refuses it in one. -/
theorem branch_data_packing_matches_a_real_wrap_proof :
    Dregg2.Circuit.Emit.MinaWrapPublicCommGate.PUBLIC_INPUT.getD 29 0 = 67
    ∧ branchDataPacked 3 16 = Dregg2.Circuit.Emit.MinaWrapPublicCommGate.PUBLIC_INPUT.getD 29 0
    ∧ (runBranch shapeSmoke 2 [0,1,2] [16,16,16]).packedV
        = Dregg2.Circuit.Emit.MinaWrapPublicCommGate.PUBLIC_INPUT.getD 29 0
    ∧ (List.range 3).map (fun w => maskBit 2 w 0 + 2 * maskBit 2 w 1) = [0, 2, 3]
    ∧ (runBranch shapeSmoke 0 [0,1,2] [16,16,16]).packedV = 64
    ∧ (runBranch shapeSmoke 1 [0,1,2] [16,16,16]).packedV = 66 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ### §11d — the field itself.

A wrap emission whose values were reduced mod `pN` would be accepted by nothing; this is the
tripwire that says which field the file is in.

⚑ **CONVERTED FROM FOUR `#guard`s.** They were four closed instances evaluated by
`unsafe evalExpr Bool`, leaving no term and invisible to the `#assert_namespace_axioms` sweep at the
foot of this file — a `native_decide` with the name, the term and the axiom record deleted. The
facts are pure `Fq` arithmetic on 254-bit literals and `decide` closes every one in the kernel, so
being guards bought nothing and cost the axiom accounting. -/

/-- **THE FIELD IS `Fq`, AND `Fq` IS A FIELD.** `qN ≠ pN` is the tripwire that says which of the two
Pasta primes this file reduces by — a wrap emission reduced mod `pN` is the one mistake that would
be accepted by nothing and visible in nothing. The other three are the ring identities the emitter
relies on every time it writes a negative coefficient as `qSub 0 k`. -/
theorem the_field_is_fq_and_wraps :
    qN ≠ pN
    ∧ qAdd (qN - 1) 1 = 0
    ∧ qMul (qN - 1) (qN - 1) = 1
    ∧ qSub 0 1 = qN - 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end Dregg2.Circuit.Emit.KimchiWrapMain
