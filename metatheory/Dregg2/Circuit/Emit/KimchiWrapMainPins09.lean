/-
# Dregg2.Circuit.Emit.KimchiWrapMainPins09 — §21a — W-WRAPHACK

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

/-! ### §21a — ⚑ THE PINS ON W-WRAPHACK, and the one that is the point. -/

/-- ⚑ **THE TAPE IS `to_field_elements`'s, AND THE ORDER IS THE FACT.**
`composition_types.ml:411-418` flattens the old bulletproof challenges FIRST and appends the
commitment's `[x; y]` LAST. The last conjunct is the red control: the same 32 values in the step
side's order give a DIFFERENT digest, so "absorbed the right values" and "absorbed them in the right
order" are two facts and this file checks both. -/
theorem wraphack_tape_is_the_challenges_then_the_commitment :
    WH_ROUNDS = 15 ∧ WH_PADDED = 2 ∧ WH_ABSORBS = 32
    ∧ (whTape (whOldChals 0) (whSgOld 0)).length = WH_ABSORBS
    ∧ (whTape (whOldChals 0) (whSgOld 0)).getD (WH_ABSORBS - 2) 0 = (whSgOld 0).1
    ∧ (whTape (whOldChals 0) (whSgOld 0)).getD (WH_ABSORBS - 1) 0 = (whSgOld 0).2
    ∧ ((List.range (WH_MLMB * WH_ROUNDS)).all (fun k =>
        (whTape (whOldChals 0) (whSgOld 0)).getD k 0 == whOldChal 0 k)) = true
    ∧ (whDigestOf (whOldChals 0) (whSgOld 0)
        == whDigestCommitmentFirst (whOldChals 0) (whSgOld 0)) = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ⚑ **THE FRONT PAD IS THE FRESH STATE, AND TWO EMITTED ROWS PIN IT.** `whPadVectors` is
`2 − max_proofs_verified` in general and `0` at the committed shape, so the opening state is
`Sponge.create`'s zeros — defect class 1 in the place `wrap_hack.ml:26-28` put it. The two `cConst 0`
rows are read off the EMITTED row list, exactly as `key_sponge_seed_is_pinned` does. -/
theorem wraphack_front_pad_is_the_fresh_state_and_the_rows_pin_it :
    whPadVectors WH_MLMB = 0 ∧ whPadVectors 1 = 1 ∧ whPadVectors 0 = 2
    ∧ ((whRows tWh true).getD 0 default).coeffs = cConst 0 ++ cConst 0
    ∧ ((whRows tWh true).getD 1 default).coeffs = cConst 0 ++ cNil
    ∧ ((whRows tWh true).getD 0 default).kind = KGateType.generic
    ∧ ((whRows tWh true).getD 1 default).kind = KGateType.generic := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ⚑ **THE ALIASING REFUTATION.** `baseWh` read `basePrev + nPrevVars` — which IS `baseFtc` — while
`rungsUpto .wraphack` contains `.ftcomm`, so two regions sat at one address in a circuit holding
both. This is the gate that says they no longer do, and it is stated over the EMITTED gates rather
than over the base arithmetic: **every external id `w8_ftcomm`'s whole rung references is strictly
below where W-WRAPHACK's region starts.** A base-vs-base equation would have been a pin against its
own definition; this one goes red if any row of any rung at or below `.ftcomm` reaches up. -/
theorem wraphack_region_is_above_ftcomms :
    baseWh shapeSmoke tWh.sp = baseFtc shapeSmoke tWh.sp + nFtcVars shapeSmoke tWh.sp
    ∧ baseFtc shapeSmoke tWh.sp < baseWh shapeSmoke tWh.sp
    ∧ ((externalRefs (wrapGates (rungRows tWh .ftcomm true))).all
        (fun i => decide (i < baseWh shapeSmoke tWh.sp))) = true := by
  refine ⟨rfl, by decide, rfl⟩

/-- The emitter's allocation FORMULA is what `runSpongeQ` actually allocates, for all three sponges
— so the three regions cannot silently overlap. -/
theorem wraphack_sponge_allocation :
    WH_PERMS = 16 ∧ WH_VARS = 115
    ∧ (whSpongeP tWh 0).next = WH_VARS
    ∧ (whSpongeP tWh 1).next = WH_VARS
    ∧ (whSpongeC tWh).next = WH_VARS := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- ⚑ **THE GATE: THE EMITTED SQUEEZE IS THE STATEMENT WORD.** §15c″ computes the three digests as
VALUES and `runSpongeQ` computes them again as a TRAJECTORY of emitted rows; this says the two agree.
A disagreement would make `whRows`' tie rows unsatisfiable and every rung at or above
`w11_wraphack` fail to prove — a red the harness finds, but a red here is cheaper and says which of
the two moved. -/
theorem wraphack_digest_is_the_statement_word :
    whDigestVal (whSpongeP tWh 0) = prevWordVal (PREV_MSG_NEXT_STEP + 1)
    ∧ whDigestVal (whSpongeP tWh 1) = prevWordVal (PREV_MSG_NEXT_STEP + 2)
    ∧ whDigestVal (whSpongeC tWh) = whCloseDigest := by
  refine ⟨rfl, rfl, rfl⟩

/-- ⚑ …and the sponge runs on the TRANSCRIPT's own `sg_old` values, not a second copy of them
(`~sg_old:prev_step_accs`, `wrap_main.ml:412` against `wrap_verifier.ml:538`). -/
theorem wraphack_absorbs_the_transcripts_own_sg_old :
    ((List.range shapeSmoke.prevs).all (fun p =>
      (whSgOld p).1 == itemVal T_SGOLD (2 * p) && (whSgOld p).2 == itemVal T_SGOLD (2 * p + 1)))
      = true
    ∧ ((whSpongeP tWh 0).evs.getD (WH_MLMB * WH_ROUNDS) default).word = itemVal T_SGOLD 0
    ∧ ((whSpongeP tWh 0).evs.getD (WH_MLMB * WH_ROUNDS + 1) default).word = itemVal T_SGOLD 1 := by
  refine ⟨rfl, rfl, rfl⟩

/-- ⚑ **RED CONTROL — the digest is a function of every input it absorbs.** Bending the first old
bulletproof challenge, the last one, or either coordinate of `sg_old` moves it. Without this the
theorem above is a number agreeing with a number. -/
theorem wraphack_digest_bends_at_every_probed_input :
    (whDigestOf (whOldChals 0) (whSgOld 0)
      == whDigestOf ((whOldChals 0).set 0 0) (whSgOld 0)) = false
    ∧ (whDigestOf (whOldChals 0) (whSgOld 0)
      == whDigestOf ((whOldChals 0).set (WH_MLMB * WH_ROUNDS - 1) 0) (whSgOld 0)) = false
    ∧ (whDigestOf (whOldChals 0) (whSgOld 0)
      == whDigestOf (whOldChals 0) (qAdd (whSgOld 0).1 1, (whSgOld 0).2)) = false
    ∧ (whDigestOf (whOldChals 0) (whSgOld 0)
      == whDigestOf (whOldChals 0) ((whSgOld 0).1, qAdd (whSgOld 0).2 1)) = false
    ∧ (whPrevDigest 0 == whPrevDigest 1) = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- ⚑ **WORD 11's OBJECT, CHECKED AGAINST A REAL DEVNET WRAP PROOF — not its slot.**

This module has already shipped the other mistake once: twenty exposed words carried the 255-bit
endo lift where `spec.ml:374-392` packs the raw 128-bit prechallenge, and **the only word with a
different width was the only correct one, which is why nothing caught it.** So the object is checked
here and the instrument is INDEPENDENT: `MinaWrapPublicCommGate.PUBLIC_INPUT` is a Mina devnet
block's own forty Fq wrap words, decoded off the wire. In it, slots 5–8 (`β γ α ζ`, `Challenge` and
`Scalar Challenge`) all fit in `Challenge.length = 128` bits, and slots 10 and 11 — the two
`B Digest`s, `sponge_digest_before_evaluations` and `messages_for_next_wrap_proof` — do NOT. That is
the width tell, measured on a real proof rather than derived from our own layout; and the value this
rung exposes at slot 11 is likewise a full `squeeze_field`, not a truncation of one. -/
theorem wraphack_word_11_is_a_digest_not_a_challenge :
    ((List.range 4).all (fun j =>
      decide (Dregg2.Circuit.Emit.MinaWrapPublicCommGate.PUBLIC_INPUT.getD (5 + j) 0
                < 2 ^ WQ_CHAL))) = true
    ∧ decide (Dregg2.Circuit.Emit.MinaWrapPublicCommGate.PUBLIC_INPUT.getD 10 0 < 2 ^ WQ_CHAL)
        = false
    ∧ decide (Dregg2.Circuit.Emit.MinaWrapPublicCommGate.PUBLIC_INPUT.getD 11 0 < 2 ^ WQ_CHAL)
        = false
    ∧ decide (whCloseDigest < 2 ^ WQ_CHAL) = false
    ∧ decide (whCloseDigest < qN) = true := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The rung's own public word: slot 11, tied to the closing sponge's squeeze. -/
theorem wraphack_public_word_11_is_the_closing_squeeze :
    rungPub shapeSmoke .wraphack = shapeSmoke.pubWords + 2
    ∧ (exposedVarsAt tWh .wraphack).getD (WH_PUB_SLOT shapeSmoke) default
        = whDigestVar (whSpongeC tWh)
    -- ⚠ the VALUE at that slot is `wraphack_digest_is_the_statement_word`'s third conjunct, stated
    -- there and not here: `wrapPublicAt` runs `envIndex` over `circuitEnvAt … .wraphack`, which
    -- carries every accumulator point and slope of §15's MSM, and reducing it blew 4 000 000
    -- heartbeats. That is the measurement the `circuitEnvAt` docblock above is about.
    ∧ (exposedVarsAt tWh .wraphack).length = shapeSmoke.pubWords + 2 := by
  refine ⟨rfl, rfl, rfl⟩

/-- The `w11_wraphack` rung is a strict superset of `w9_prev`, its length is the sum of its parts,
and the WIRED and UNWIRED emissions differ ONLY in the probe rows' permutation columns. -/
theorem wraphack_rung_extends_prev :
    (rungRows tWh .wraphack true).length
      = (rungRows tWh .prev true).length + (whRows tWh true).length
    ∧ (rungRows tWh .prev true).length < (rungRows tWh .wraphack true).length
    ∧ (((rungRows tWh .wraphack true).zip (rungRows tWh .wraphack false)).filter
        (fun p => p.1.perm != p.2.perm)).length
        = ((rungRows tWh .wraphack true).filter (fun r => r.probe)).length := by
  refine ⟨rfl, by decide, rfl⟩

/-- `placeChecked` ACCEPTS the `w11_wraphack` rung at its larger public size and no public word is
inert — and `w9_prev` is REFUSED at that size, because no `w9_prev` gate reads slot `pubWords + 1`.
That is what makes `AUXW`'s second reserved slot a gate rather than a comment. -/
theorem wraphack_rung_places_and_the_rung_below_it_does_not :
    refusalOf shapeSmoke (rungPub shapeSmoke .wraphack)
        (wrapGates (rungRows tWh .wraphack true)) = none
    ∧ inertPublicWords (rungPub shapeSmoke .wraphack)
        (wrapGates (rungRows tWh .wraphack true)) = []
    ∧ inertPublicWords (rungPub shapeSmoke .wraphack)
        (wrapGates (rungRows tWh .prev true)) = [WH_PUB_SLOT shapeSmoke] := by
  refine ⟨rfl, rfl, rfl⟩

/-- ⚑ **THE TWENTY-FOUR ARE DERIVED, AND TWENTY-FOUR IS NOT FORTY.** `WRAP_PINNED_SLOTS` is what
`wrap_main` actually constrains; `WRAP_UNPINNED` is the rest, by REASON and by owner. A run that
reads "public inputs: ours 24, mina 40" and calls the remaining sixteen a gap in this assembly would
be reading a deferred value and a zero pad as work. -/
theorem wraphack_closes_every_pinned_statement_word :
    WRAP_PINNED_WORDS = 24
    ∧ WRAP_PINNED_SLOTS.length = 24
    ∧ WRAP_PRIMARY_LEN - WRAP_PINNED_WORDS = 16
    ∧ WRAP_UNPINNED.length = 4
    ∧ rungPub shapeSmoke .wraphack = shapeSmoke.pubWords + 2 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- ⚠ ⚑ **THE CENSUS DID NOT MOVE, AND `sg_old`'s ENTRY IS REWRITTEN RATHER THAN STRUCK.**
W-WRAPHACK gives `sg_old` a real consumer — it is hashed into packed statement words 55/56, which the
x_hat MSM consumes as entries 65/66. It is still a FREE witness: the digest is a function of it, but
nothing forces the digest to any particular value, because what the MSM's output feeds is `x_hat`,
which is itself absorbed and unconsumed. A prover still chooses `sg_old` subject only to
`assert_on_curve`. Striking the entry here would be the metric-gaming this census exists to refuse.
The count stays **8**. -/
theorem wraphack_does_not_move_the_unconsumed_census :
    WRAP_UNCONSUMED.length = 8
    ∧ WRAP_UNCONSUMED_KEYS.getD 0 "" = "sg_old"
    ∧ WRAP_UNCONSUMED_KEYS.length = WRAP_UNCONSUMED.length := by
  refine ⟨rfl, rfl, rfl⟩

end Dregg2.Circuit.Emit.KimchiWrapMain
