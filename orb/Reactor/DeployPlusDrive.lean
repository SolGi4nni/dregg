import Reactor.DeployPlus

/-!
# Reactor.DeployPlusDrive — my-hand driver: run the extended fold, SEE the wire bytes

Not a proof. This `#eval`s the extended deployed fold on two real deployed contexts
and renders the serialized HTTP/1.1 response as text, so the new response edges are
visible on the wire form the serializer produces:

* an OVER-LIMIT metered connection → `429` carrying `Retry-After: 1`;
* `GET /static/app.js` → `200` carrying `Cache-Control` + `Content-Location`.
-/

open Reactor.DeployPlus
open Reactor (serialize)

/-- Render a byte list as a String for display (ASCII wire dump). -/
def dump (bs : List UInt8) : String := String.fromUTF8! ⟨bs.toArray⟩

/-- The over-limit metered response (empty request, clean peer, over the rate cap). -/
#eval IO.println (dump (servePipelinePlusMetered
  Reactor.RateMeteredCorrect.cleanIp Reactor.Stage.Rate.rateCap []))

/-- The static GET response through the full extended fold. -/
#eval IO.println (dump (serialize (deployRespPlusOf staticCtx)))
