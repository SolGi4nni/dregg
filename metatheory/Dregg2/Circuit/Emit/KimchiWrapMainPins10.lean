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
rows that compute it. It adds W-WRAPHACK's own rows and its own two, derives no new public word, and
places — `refusalOf` and the empty `inertPublicWords` are what say the assembly is still sound with
two block owners live in one rung. -/
theorem close_rung_extends_bullet :
    (rungRows tWh .close true).length
      = (rungRows tWh .bullet true).length + (whRows tWh true).length + 2
    ∧ rungPub shapeSmoke .close = rungPub shapeSmoke .wraphack
    ∧ refusalOf shapeSmoke (rungPub shapeSmoke .close)
        (wrapGates (rungRows tWh .close true)) = none
    ∧ inertPublicWords (rungPub shapeSmoke .close)
        (wrapGates (rungRows tWh .close true)) = []
    ∧ regionEscape shapeSmoke tWh.sp .close
        (wrapGates (rungRows tWh .close true)) = none := by
  refine ⟨?_, rfl, ?_, ?_, ?_⟩ <;> native_decide

-- ⚠ ⚑ **THIS LEFT THE KERNEL WHEN `.bullet` CAME UNDER `.close`, AND THE REASON IS THE INSTRUMENT
-- AND NOT THE STATEMENT.** `rungRows tWh .close true` now contains `bulletRows`, which runs
-- `bullData` — 34 + 33 endo ladders and a `scale_fast` at 51 chunks — and §24c already records that
-- it times out at 4 000 000 heartbeats. Three of the four legs were `rfl` while the rung stopped at
-- W-WRAPHACK; they are the SAME facts about a longer row list. `#assert_compiled` records the trade
-- rather than hiding it, and the `rungPub` leg stays kernel-clean because it is shape arithmetic.
#assert_compiled close_rung_extends_bullet

end Dregg2.Circuit.Emit.KimchiWrapMain
