import Reactor.Stage.NotAcceptable

/-!
# Reactor.Stage.NotAcceptableCorrect — the deployed 406 gate firing law, proven GENERAL

`Reactor.Stage.NotAcceptable.naGateStage` is wired into the deployed pipeline
(`Reactor.DeployPlus8`). Its firing was pinned only by CONCRETE witnesses
(`example : fires q0Ctx = true`, …) plus the abstract `naGate_fires`, which took
`fires c = true` as a HYPOTHESIS. This file closes the gap between the two with the
GENERAL positive firing law: EVERY on-route request all of whose served representations
are unacceptable is refused the `406`, and the refusal is SOUND (every served language
scored `0`).
-/

namespace Reactor.Stage.NotAcceptable

open Reactor.Pipeline
open Reactor.Stage.ContentLanguage (Lang qFor tagOf inScope)

/-- **The 406 gate fires, general.** For EVERY context on the negotiated route
(`inScope c = true`) all of whose served representations are unacceptable
(`allUnacceptable c.req = true`), the deployed gate refuses the request the
`406 Not Acceptable`, AND the refusal is genuinely sound: every served language scored
`0`. Generalises the concrete `fires` / `example` witnesses to an `∀`. -/
theorem naGate_refuses_when_none_acceptable (c : Ctx)
    (hs : inScope c = true) (ha : allUnacceptable c.req = true) :
    naGateStage.onRequest c = .respond notAcceptableResp
    ∧ ∀ l : Lang, qFor c.req (tagOf l) = 0 := by
  have hf : fires c = true := by
    unfold fires
    rw [hs, ha, Bool.and_self]
  exact ⟨naGate_fires c hf, allUnacceptable_sound c.req ha⟩

end Reactor.Stage.NotAcceptable

#print axioms Reactor.Stage.NotAcceptable.naGate_refuses_when_none_acceptable
