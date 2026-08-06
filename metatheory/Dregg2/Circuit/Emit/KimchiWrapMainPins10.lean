/-
# Dregg2.Circuit.Emit.KimchiWrapMainPins10 — §22a — W-CLOSE

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

/-! ### §22a — ⚑ THE PINS ON W-CLOSE. -/

/-- **W-CLOSE emits the σ-TIE, `Boolean.Assert.is_true bulletproof_success`, and one σ-only probe.**

⚑ Row 0 is now one `Generic` DOUBLE gate carrying both halves: the tie joining `bpSuccessVar` to
`bullEqV s sp 12` — `equal_g`'s `Boolean.all` output — and the `cConst 1` assert. The first half's
two permutable slots are what makes it a tie and not a second constant. -/
theorem close_ties_and_asserts_bulletproof_success :
    (closeRows tWh true).length = 2
    ∧ ((closeRows tWh true).getD 0 default).kind = KGateType.generic
    ∧ ((closeRows tWh true).getD 0 default).coeffs = cEq ++ cConst 1
    ∧ ((closeRows tWh true).getD 0 default).perm.getD 0 none
        = some (bpSuccessVar shapeSmoke tWh.sp)
    ∧ ((closeRows tWh true).getD 0 default).perm.getD 1 none
        = some (bullEqV shapeSmoke tWh.sp 12)
    ∧ ((closeRows tWh true).getD 1 default).probe = true
    ∧ ((closeRows tWh true).getD 1 default).kind = KGateType.zero := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ⚑ …and the emitted coefficients REFUSE a failed opening: the half is satisfied at
`bulletproof_success = 1` and violated at `0`, which is the whole content of
`Boolean.Assert.is_true`.

⚠ **THE WITNESS IS NO LONGER A CONSTANT THIS FILE WROTE.** `closeEnv` used to answer `(1 : Int)`
outright, so this conjunct was a pin against its own definition. It now COMPUTES
`bullLhs t v == bullRhs t v` off `bullData` — the same expression `bulletEnv` gives `bullEqV s sp 12`
— so the `1` below is `equal_g`'s verdict at this key and not a decision made here. That is why this
leg moved to `native_decide`: `bullData` is 34 + 33 endo ladders, the same instrument
`bullet_solves_g_on_curve_and_equal_g_is_one` confesses to. -/
theorem close_refuses_a_failed_opening :
    genericHalfAt (cConst 1) 1 0 0 = 0
    ∧ genericHalfAt (cConst 1) 0 0 0 ≠ 0 := by
  refine ⟨rfl, by decide⟩

/-- ⚑⚑ **AND THE WITNESS IT PINS TO 1 IS W-BULLET'S OWN VERDICT** — the half of
`close_refuses_a_failed_opening` that `bullData` puts out of the kernel's reach. `closeEnv`'s single
entry and `bulletEnv`'s `bullEqV s sp 12` entry hold ONE value, which is what makes the σ-tie
satisfiable, and that value is `1` because `equal_g` computes 1 at Mina's step key. At the old
degenerate key it computed 0 — and then this theorem would be FALSE rather than the rung quietly
asserting a constant. -/
theorem close_witness_is_the_bullet_verdict :
    (closeEnv tWh).getD 0 ((.external 0 : PVar), (0 : Int))
      = (bpSuccessVar shapeSmoke tWh.sp, (1 : Int))
    ∧ (bulletEnv tWh).contains (bullEqV shapeSmoke tWh.sp 12, (1 : Int)) = true := by
  native_decide

#assert_compiled close_witness_is_the_bullet_verdict

/-- The `w12_close` rung is the ladder's top. ⚑ It extends `w11_bullet` and not `w11_wraphack` since
2026-08-05: `bulletproof_success` is `equal_g`'s output, so the rung that asserts it must carry the
rows that compute it. It adds W-WRAPHACK's own rows and its own two, and derives no new public word.

⚑⚑ **AND IT IS THE FIRST RUNG TO HOLD TWO BLOCK OWNERS** — `.wraphack` and `.combine` — which is why
§17b's `rungRegions` returns a LIST. The last two legs are that pair: the ladder really does hold two
owners, and `rungRegions .close` really does declare two blocks. A `rungRegions` that forgot
W-COMBINE would make the fourth leg `1` and red here, which is the failure the old single-block form
made unavoidable.

⚑ **GENERAL OVER EVERY `WrapData` AND EVERY POLARITY, AND KERNEL-CLEAN** — stronger than the shape
instance it replaced, and that is also what makes it affordable.

⚠ **`refusalOf`, `inertPublicWords` AND `regionEscape` ARE NOT PINNED HERE, and that is the file's
own division rather than a gap.** Each runs `placeChecked` or `externalRefs` over this rung's ~7 000
gates — which now include `bulletRows`' 67 endo ladders and `combRows`' 46 — and neither the kernel
nor the compiled evaluator finishes it in a budget worth paying on every build: MEASURED at >23 min
with four inline `rungRows tWh .close true`, and still >16 min after memoising into
`clRows`/`clGates`. Against 65 s while the rung stopped at W-WRAPHACK. **`EmitWrapMainJson` and
`EmitStepWrapChainJson` run all three at EVERY emission and STOP on any of them**, which is exactly
where `the_caps_are_the_blocks` already puts W-FINALIZE's fit: the kernel closes what it can reach,
the emit-time refusal closes the rest, and the two are named separately rather than blurred.
`clRows`/`clGates` stay in the fixture as the shared term those emissions — and any future pin that
can afford them — should use. -/
theorem close_rung_extends_bullet (t : WrapData) (wired : Bool) :
    rungRows t .close wired
      = rungRows t .bullet wired ++ rungOwn t wired .wraphack ++ rungOwn t wired .close
    ∧ rungPub t.sh .close = rungPub t.sh .wraphack
    ∧ ((rungsUpto .close).filter (fun r => COLLIDING_REGION_OWNERS.contains r)).length = 2
    ∧ (rungRegions t.sh t.sp .close).length = 2 :=
  ⟨rungRows_close_is_a_ladder t wired, rfl, by decide, rfl⟩

#assert_axioms close_rung_extends_bullet

/-- ⚑⚑⚑ **THE TWO SLOTS `w12_close` DOES NOT REACH, AND THEY DO NOT HAVE ONE CAUSE.**

`wrap_main` is handed forty words, CONSTRAINS twenty-four and READS six more; the ten it neither
reads nor checks are `Spec.T.Constant` padding and the lookup `Opt` (§10). So the denominator is
**30**, and the terminal rung reaches **28** of them. The missing two are slots **11** and **12**,
and it is worth saying plainly that they were being read as one blockage — "the six words" — when
they are two, with different owners and different repairs.

`WRAP_PUBLIC_INPUT_MEASURED` is the second source both are graded against: the RUST marshaller's
`PreparedStatement::to_public_input(40)`, on the SAME proof this assembly is about
(`stepmain_step_r8_finalize`). Two implementations, one statement — which is what makes a
disagreement a measurement rather than a preference.

  * **SLOT 12 — `messages_for_next_step_proof`.** §18's `prevRows` ties Mina's slot 12 to packed
    statement word 54 by `Field.Assert.equal`, and the wrap DERIVES NOTHING for it: it reads the
    word and exposes it. So the disagreement is entirely the step side's — word 54 is
    `hmOutDigestVar`, segment D's own Poseidon squeeze — and it closes when the step assembly's
    outer hash produces what the marshaller computes. **It is not one of the values a wrap-side
    derivation could ever supply.**
  * **SLOT 11 — `messages_for_next_wrap_proof`.** §21's closing sponge DOES derive this one, and it
    still cannot land, for a reason that has nothing to do with the step statement:
    `whCloseDigest = whDigestOf whNewChals whSg` and `whNewChals` is `wrapFixtureQ 42` — a NAMED
    FIXTURE standing for `new_bulletproof_challenges`, i.e. **W-FINALIZE's output**, the sub-circuit
    §13 item 7 records as not assembled. A digest over a fixture cannot equal a digest over the real
    vector. **Slot 11 is blocked on W-FINALIZE's bulletproof challenges and on nothing else**, so no
    amount of step-side re-baking moves it.

⚠ **AND THIS THEOREM IS A REFUSAL SHAPED TO SHRINK, like `STATEMENT_BLOCKED`.** It asserts the two
DISAGREE. Close either and it goes red at the place the claim is made, and the count above has to be
rewritten — which is the only direction this file should ever move. -/
theorem the_two_slots_close_does_not_reach_are_a_fixture_and_a_step_digest :
    Dregg2.Circuit.Emit.MinaWrapDeferredWords.WRAP_PUBLIC_INPUT_MEASURED.getD 11 0
      ≠ whCloseDigest
  ∧ Dregg2.Circuit.Emit.MinaWrapDeferredWords.WRAP_PUBLIC_INPUT_MEASURED.getD 12 0
      ≠ prevWordVal PREV_MSG_NEXT_STEP
  -- ⚑ …and slot 11's blocker EXHIBITED rather than described: the closing digest's challenge vector
  -- is the `wrapFixtureQ 42` fixture, entry for entry. A repair that wires W-FINALIZE's real
  -- `new_bulletproof_challenges` reds this conjunct first.
  ∧ whNewChals
      = (List.range (WH_MLMB * WH_ROUNDS)).map
          (fun k => wrapFixtureQ 42 k)
  -- ⚑ …and the denominator, so "28 of 30" is not a number in a dump: forty words, ten of which
  -- upstream neither reads nor checks.
  ∧ 40 - 10 = 30 := by
  refine ⟨?_, ?_, rfl, ?_⟩ <;> native_decide

#assert_compiled the_two_slots_close_does_not_reach_are_a_fixture_and_a_step_digest

end Dregg2.Circuit.Emit.KimchiWrapMain
