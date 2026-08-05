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

/-- **W-CLOSE emits `Boolean.Assert.is_true bulletproof_success` and one σ-only probe.** -/
theorem close_asserts_bulletproof_success :
    (closeRows tWh true).length = 2
    ∧ ((closeRows tWh true).getD 0 default).kind = KGateType.generic
    ∧ ((closeRows tWh true).getD 0 default).coeffs = cConst 1 ++ cNil
    ∧ ((closeRows tWh true).getD 0 default).perm.getD 0 none
        = some (bpSuccessVar shapeSmoke tWh.sp)
    ∧ ((closeRows tWh true).getD 1 default).probe = true
    ∧ ((closeRows tWh true).getD 1 default).kind = KGateType.zero := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- ⚑ …and the emitted coefficients REFUSE a failed opening: the half is satisfied at
`bulletproof_success = 1` and violated at `0`, which is the whole content of
`Boolean.Assert.is_true`. The honest witness this file emits is the `1`. -/
theorem close_refuses_a_failed_opening :
    genericHalfAt (cConst 1) 1 0 0 = 0
    ∧ genericHalfAt (cConst 1) 0 0 0 ≠ 0
    ∧ (closeEnv tWh).getD 0 ((.external 0 : PVar), (0 : Int))
        = (bpSuccessVar shapeSmoke tWh.sp, (1 : Int)) := by
  refine ⟨rfl, by decide, rfl⟩

/-- The `w12_close` rung is the ladder's top: two more rows, no new public word, and it places. -/
theorem close_rung_extends_wraphack :
    (rungRows tWh .close true).length = (rungRows tWh .wraphack true).length + 2
    ∧ rungPub shapeSmoke .close = rungPub shapeSmoke .wraphack
    ∧ refusalOf shapeSmoke (rungPub shapeSmoke .close)
        (wrapGates (rungRows tWh .close true)) = none
    ∧ inertPublicWords (rungPub shapeSmoke .close)
        (wrapGates (rungRows tWh .close true)) = [] := by
  refine ⟨rfl, rfl, rfl, rfl⟩

end Dregg2.Circuit.Emit.KimchiWrapMain
