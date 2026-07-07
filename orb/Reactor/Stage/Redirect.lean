import Reactor.Pipeline
import Redirect

/-!
# Reactor.Stage.Redirect — a redirect GATE stage

A byte-driving pipeline stage that short-circuits a request matching a
configured redirect rule with a 3xx response carrying a `Location` header,
built by the REAL `Redirect` library (`Redirect.redirect` — status code +
`Location` template substitution, RFC 9110 §15.4).

This is a GATE: `onRequest` returns `.respond` for a matched request, so the
handler and every later stage are skipped and the redirect IS the emitted
response. The byte-effect is visible in the built pipeline output:

* `redirectStage_gate` — a matched request short-circuits: the pipeline output
  is exactly `ofResponse (redirectFor c.req)`, for ANY tail and handler.
* `redirectStage_status_is_redirect` — the emitted status is one of the four
  §15.4 redirect codes (301/302/307/308), via `Redirect.status_is_redirect`.
* `redirectStage_location_present` — the emitted response carries a `Location`
  header whose value is exactly the `Redirect`-rendered target location.

The response location is produced by `Redirect.redirect` rendering the
configured `Location` template against the request's own (decoded) target — a
real byte-effect, not an attachment.
-/

namespace Reactor.Stage.Redirect

open Reactor.Pipeline
open Proto (Bytes Request)

/-- The `Location` header name, `"Location"` in UTF-8 bytes. -/
def locationName : Bytes := "Location".toUTF8.toList

/-- The reason phrase stamped on the redirect response. -/
def redirectReason : Bytes := "Moved".toUTF8.toList

/-- The configured redirect status code (308 Permanent Redirect). -/
def ruleCode : _root_.Redirect.Code := .perm308

/-- The configured `Location` template: `https://new.example{path}`. The
`{path}` placeholder is substituted with the request's decoded target. -/
def ruleTemplate : List _root_.Redirect.Tok :=
  [.lit "https://new.example", .path]

/-- The request target this rule redirects: `/old`. -/
def ruleTarget : Bytes := "/old".toUTF8.toList

/-- Decode a raw target byte string to a `String` for template substitution. -/
def decodeTarget (b : Bytes) : String := String.fromUTF8! ⟨b.toArray⟩

/-- Lift a `Redirect.Resp` (the real library output — a 3xx status + rendered
`Location`) into the wire `Response` the serializer renders: the redirect
status, a reason phrase, and the single `Location` header. -/
def toResponse (rr : _root_.Redirect.Resp) : Response :=
  { status  := rr.status
    reason  := redirectReason
    headers := [(locationName, rr.location.toUTF8.toList)]
    body    := [] }

/-- The redirect response for a matched request: run the REAL
`Redirect.redirect` against the configured code/template and the request's own
(decoded) target, then lift it to a wire `Response`. -/
def redirectFor (req : Request) : Response :=
  toResponse (_root_.Redirect.redirect ruleCode ruleTemplate (decodeTarget req.target) "")

/-- **The redirect gate stage.** On the request phase it gates: a request whose
target matches `ruleTarget` short-circuits with the redirect `Response` (the
handler and every later stage skipped); any other request passes through
untouched. The response phase is the identity — a gate's byte-effect is entirely
in its `.respond`. -/
def redirectStage : Stage where
  name := "redirect"
  onRequest := fun c =>
    if c.req.target = ruleTarget then .respond (redirectFor c.req) else .continue c
  onResponse := fun _ b => b

/-- **The gate short-circuit.** A request matching the redirect rule makes the
pipeline output exactly `ofResponse (redirectFor c.req)` — the handler and every
stage in `rest` are skipped. Rides on `pipeline_gate_short_circuits`. -/
theorem redirectStage_gate (rest : List Stage) (handler : Ctx → Response) (c : Ctx)
    (hm : c.req.target = ruleTarget) :
    runPipeline (redirectStage :: rest) handler c
      = runResp rest c (ResponseBuilder.ofResponse (redirectFor c.req)) := by
  apply pipeline_gate_short_circuits
  show (if c.req.target = ruleTarget then _ else _) = _
  rw [if_pos hm]

/-- **Byte-effect (status).** The status genuinely emitted for a matched request
is one of the four §15.4 redirect codes — a real 3xx — PRESERVED through the inner
response onion (status-stable transforms) even as the redirect now carries the
response-transform headers (security headers etc.). Discharged by the REAL
`Redirect.status_is_redirect`. -/
theorem redirectStage_status_is_redirect (rest : List Stage) (handler : Ctx → Response)
    (c : Ctx) (hm : c.req.target = ruleTarget)
    (hst : ∀ t ∈ rest, Stage.statusStable t) :
    (runPipeline (redirectStage :: rest) handler c).build.status
      ∈ _root_.Redirect.redirectStatuses := by
  have hg : redirectStage.onRequest c = .respond (redirectFor c.req) := by
    show (if c.req.target = ruleTarget then _ else _) = _
    rw [if_pos hm]
  rw [pipeline_gate_status redirectStage rest handler c (redirectFor c.req) hg hst]
  exact _root_.Redirect.status_is_redirect ruleCode ruleTemplate (decodeTarget c.req.target) ""

/-- **Byte-effect (Location header).** The response genuinely emitted for a
matched request carries a `Location` header whose value is exactly the
`Redirect`-library-rendered target location. Stated with no inner transform tail
(the gate's own 3xx response); with a deployed transform tail the redirect ALSO
gains the response-transform headers, the Location among them (the hop-strip keeps
non-hop headers). -/
theorem redirectStage_location_present (handler : Ctx → Response)
    (c : Ctx) (hm : c.req.target = ruleTarget) :
    (locationName,
        (_root_.Redirect.redirect ruleCode ruleTemplate (decodeTarget c.req.target) "").location.toUTF8.toList)
      ∈ (runPipeline [redirectStage] handler c).build.headers := by
  rw [redirectStage_gate [] handler c hm, runResp_nil, build_ofResponse]
  exact List.mem_singleton.mpr rfl

end Reactor.Stage.Redirect
