import Reactor.RateMeteredCorrect
import Reactor.Stage.RetryAfter
import Reactor.Stage.CacheControl
import Reactor.Stage.ContentLocation

/-!
# Reactor.DeployPlus — the deployed metered serve EXTENDED with three response edges

This composes the three new response-edge stages
(`Reactor.Stage.{RetryAfter,CacheControl,ContentLocation}`) onto the EXACT
`Reactor.Deploy.deployStagesFull2` fold the running `drorb_serve_metered` serves —
by PREPENDING them (so their `onResponse` runs OUTERMOST in the onion: they observe
the final built status and their headers survive every inner header-map rewrite).
`deployStagesFull2` is referenced read-only; nothing in the deployed literal is
edited, so every existing deployed proof stands.

The composition theorems here are stated over the REAL deployed fold (not a toy
chain):

* `deployPlusMetered_over_retryAfter` — on an OVER-LIMIT metered connection (the
  exact `429`-producing context `Reactor.RateMeteredCorrect.servePipelineFull2Metered_over_429`
  establishes), the extended fold's built response carries `Retry-After` — a REAL
  refinement over the deployed `429`. Pure kernel: axioms ⊆ {propext, Quot.sound}.
* `deployPlusOf_static_status` / `_cacheControl` / `_contentLocation` — on a
  concrete deployed `GET /static/app.js` context (a real accepted loopback peer,
  under the rate cap), the extended fold builds a `200` carrying `Cache-Control`
  and `Content-Location`. These are closed computations over the full 17-stage
  fold, discharged by `native_decide` (adds the `ofReduceBool` axiom — flagged).

The generic, tail-agnostic byte-effect theorems (over ANY chain) live in the three
stage files; here they are anchored to the deployed fold.
-/

namespace Reactor.DeployPlus

open Reactor.Pipeline
open Reactor (Response serialize)
open Reactor.Deploy (deployStagesFull2 appHandler ctxOfMetered)
open Reactor.Stage.RetryAfter (retryAfterStage retryAfterName retryAfterVal)
open Reactor.Stage.CacheControl (cacheControlStage cacheControlName cacheControlVal)
open Reactor.Stage.ContentLocation (contentLocationStage contentLocationName)
open Reactor.RateMeteredCorrect (cleanIp)

/-- **The extended deployed chain.** The three response-edge stages prepended to
the exact `deployStagesFull2` fold the running `drorb_serve_metered` serves. Head
placement ⇒ their `onResponse` is OUTERMOST (runs last in the onion), so they see
the final built status and their headers survive the inner rewrites. -/
def deployStagesPlus : List Stage :=
  [retryAfterStage, cacheControlStage, contentLocationStage] ++ deployStagesFull2

/-- The built response of the extended fold on a directly-supplied context (the
H3/native-dispatch shape). -/
def deployRespPlusOf (c : Ctx) : Response :=
  (runPipeline deployStagesPlus appHandler c).build

/-- The built response of the extended METERED fold — the connection-aware
IP-filter/rate context the dataplane threads in. -/
def deployRespPlusMetered (clientIp : Proto.Bytes) (connSeq : Nat) (input : Proto.Bytes) : Response :=
  deployRespPlusOf (ctxOfMetered clientIp connSeq input)

/-- The extended metered serve as wire bytes — the `servePipelineFull2Metered`
sibling with the three edges. This is what a re-pointed FFI export
(`drorb_serve_metered_plus`) would fold. -/
def servePipelinePlusMetered (clientIp : Proto.Bytes) (connSeq : Nat) (input : Proto.Bytes) : Proto.Bytes :=
  serialize (deployRespPlusMetered clientIp connSeq input)

/-! ## Retry-After over the deployed `429` (pure kernel) -/

/-- **The deployed rate-limit `429` gains its `Retry-After` back-off signal.** For a
clean accepted loopback peer whose connection is over the rate cap (the exact
context `servePipelineFull2Metered_over_429` proves builds a `429`), the extended
metered fold's response carries `Retry-After` (RFC 9110 §10.2.3). The two
representation-edge stages (`cacheControl`/`contentLocation`) are status-preserving,
so the `429` peels through them; `retryAfter` (outermost) then fires on it.
Axioms ⊆ {propext, Quot.sound}. -/
theorem deployPlusMetered_over_retryAfter (input : Proto.Bytes)
    (hadmin : Reactor.Deploy.isAdminPath
      (ctxOfMetered cleanIp Reactor.Stage.Rate.rateCap input).req = false)
    (hpriv : Reactor.Stage.BasicAuth.isProtectedPath
      (ctxOfMetered cleanIp Reactor.Stage.Rate.rateCap input).req = false) :
    (retryAfterName, retryAfterVal)
      ∈ (deployRespPlusMetered cleanIp Reactor.Stage.Rate.rateCap input).headers := by
  have h429 : (runPipeline deployStagesFull2 appHandler
      (ctxOfMetered cleanIp Reactor.Stage.Rate.rateCap input)).acc.status = 429 :=
    Reactor.RateMeteredCorrect.servePipelineFull2Metered_over_429 input hadmin hpriv
  have hstatus : (runPipeline (cacheControlStage :: contentLocationStage :: deployStagesFull2)
      appHandler (ctxOfMetered cleanIp Reactor.Stage.Rate.rateCap input)).acc.status = 429 := by
    rw [Reactor.Stage.CacheControl.cacheControlStage_preserves_status,
        Reactor.Stage.ContentLocation.contentLocationStage_preserves_status]
    exact h429
  show (retryAfterName, retryAfterVal)
    ∈ (runPipeline (retryAfterStage :: cacheControlStage :: contentLocationStage :: deployStagesFull2)
        appHandler (ctxOfMetered cleanIp Reactor.Stage.Rate.rateCap input)).build.headers
  exact Reactor.Stage.RetryAfter.retryAfterStage_429_present
    (cacheControlStage :: contentLocationStage :: deployStagesFull2) appHandler
    (ctxOfMetered cleanIp Reactor.Stage.Rate.rateCap input) hstatus

/-- A concrete non-vacuous witness: the empty over-limit request. -/
theorem deployPlusMetered_empty_over_retryAfter :
    (retryAfterName, retryAfterVal)
      ∈ (deployRespPlusMetered cleanIp Reactor.Stage.Rate.rateCap []).headers :=
  deployPlusMetered_over_retryAfter [] (by decide) (by decide)

/-! ## Cache-Control + Content-Location over a deployed static `200` (native_decide) -/

/-- A concrete deployed `GET /static/app.js` context: a real accepted loopback peer
(`cleanIp`), under the rate cap (`seq = 0`), dispatched to the static route. This is
the native-dispatch shape (`deployRespPlusOf`) — the same fold the TCP path runs. -/
def staticCtx : Ctx :=
  { input := []
    req := { method := "GET".toUTF8.toList
             target := "/static/app.js".toUTF8.toList
             version := []
             headers := [] }
    attrs := [ (Reactor.Stage.IpFilter.clientIpKey, cleanIp)
             , (Reactor.Stage.Rate.seqKey, ([] : List UInt8)) ] }

/-- The deployed static GET is answered `200` through the full extended fold. -/
theorem deployPlusOf_static_status : (deployRespPlusOf staticCtx).status = 200 := by
  native_decide

/-- **The deployed static `200` gains `Cache-Control`.** `GET /static/app.js` through
the full extended fold carries `Cache-Control: public, max-age=3600` (RFC 9111
§5.2). Closed computation over the 17-stage fold. -/
theorem deployPlusOf_static_cacheControl :
    (cacheControlName, cacheControlVal) ∈ (deployRespPlusOf staticCtx).headers := by
  native_decide

/-- **The deployed static `200` gains `Content-Location`.** `GET /static/app.js`
through the full extended fold carries `Content-Location: /static/app.js` (RFC 9110
§8.7), its value the exact request target. -/
theorem deployPlusOf_static_contentLocation :
    (contentLocationName, staticCtx.req.target) ∈ (deployRespPlusOf staticCtx).headers := by
  native_decide

/-- **No spurious back-off on the static `200`.** The extended fold's static `200`
carries NO `Retry-After` — the edge is a real conditional, not an always-on stamp. -/
theorem deployPlusOf_static_no_retryAfter :
    (retryAfterName, retryAfterVal) ∉ (deployRespPlusOf staticCtx).headers := by
  native_decide

#print axioms deployPlusMetered_over_retryAfter
#print axioms deployPlusMetered_empty_over_retryAfter
#print axioms deployPlusOf_static_status
#print axioms deployPlusOf_static_cacheControl
#print axioms deployPlusOf_static_contentLocation
#print axioms deployPlusOf_static_no_retryAfter

end Reactor.DeployPlus
