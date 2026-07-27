import Reactor.Pipeline

/-!
# Reactor.Stage.DateHeader — the response-funnel finisher (Date + HEAD body strip)

The two response-side MUSTs the wave-4 RFC conformance probe
(`docs/engine/review/CONFORMANCE-PROBE.md`) found violated on the deployed serve,
both edges of the verified core rather than the core itself:

* **F1 — Date (RFC 7231 §7.1.1.2, MUST).** "An origin server with a clock MUST
  send a `Date` header field in all [2xx/3xx/4xx] responses." The deployed serve
  emits none. `dateStage` adds one at the response funnel. The VALUE is the
  current wall-clock time in RFC-1123 form — a runtime EFFECT (a time FFI), so it
  enters here as an opaque parameter `now : Bytes`; the proof establishes the
  header is PRESENT (name `Date`, value = whatever the clock effect produced),
  not its numeric value (which no pure proof can pin — see residual).

* **B1 — HEAD MUST NOT send a body (RFC 7231 §4.3.2, MUST).** The probe issues
  `HEAD /health` — the dynamic `/health` route, NOT the static-file lane that
  `Proto.HeadProven` already proves correct. The general handler returns a body
  regardless of method, so the body rides out on a HEAD response (a keep-alive
  desync hazard). `headStripStage` strips the body octets on a HEAD request at
  the funnel, keeping the head. `Proto.HeadProven` covers the static lane; this
  covers the general/dynamic funnel the probe actually hit.

## Content-Length residual (honest)

In `Reactor.Serialize` the `Content-Length` header is DERIVED from `body.length`
by the serializer (`build` pins `contentLength := body.length`). So a
body-stripped HEAD response serializes `Content-Length: 0`. That is
framing-SAFE (0 body octets, no desync — the B1 MUST + the probe's B1 check,
which asserts an empty body) but does not carry the would-be-GET length that RFC
7231 §8.6 recommends. Reporting the GET length on a HEAD needs the serializer to
accept an explicit length independent of the emitted body — a `Serialize`/`Deploy`
structural change, out of scope for an additive stage. Named in the report.

## What is proven

* `dateStage_adds_date` — for ANY clock value / tail / handler, the `Date` header
  (name + the effect's value) is present in the BUILT response.
* `dateStage_statusStable` — Date emission never changes the status.
* `headStripStage_strips_head_body` — on a HEAD request the built body is `[]`.
* `headStripStage_keeps_get_body` — on a non-HEAD request the response is
  untouched (non-vacuity: the strip is HEAD-specific, not a blanket wipe).
* `headStripStage_statusStable` — the strip never changes the status.
-/

namespace Reactor.Stage.DateHeader

open Reactor.Pipeline
open Proto (Bytes)

/-! ## F1 — the Date header -/

/-- `Date` header name (explicit ASCII: `D a t e`). -/
def dateName : Bytes := [68, 97, 116, 101]

/-- **The Date-emission stage.** Always passes the request phase; on the response
phase pushes `Date: <now>` onto the affine builder. `now` is the RFC-1123-rendered
current time — a runtime effect (the host clock FFI), opaque to the proof. -/
def dateStage (now : Bytes) : Stage where
  name := "date"
  onRequest := fun c => .continue c
  onResponse := fun _ b => b.addHeader (dateName, now)

theorem dateStage_statusStable (now : Bytes) : Stage.statusStable (dateStage now) := by
  intro c b
  show ((b.addHeader (dateName, now)).build).status = b.build.status
  rw [build_addHeader]

/-- The Date stage factors through `pipeline_stage_effect`. -/
theorem dateStage_effect (now : Bytes) (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    runPipeline (dateStage now :: rest) h c
      = (runPipeline rest h c).addHeader (dateName, now) :=
  pipeline_stage_effect (dateStage now) rest h c c rfl

/-- **F1.** The `Date` header — name and the clock effect's value — is present in
the BUILT response, for ANY clock value, tail, and handler. (The value is the
trusted time effect; presence + name is what is proven.) -/
theorem dateStage_adds_date (now : Bytes) (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    (dateName, now) ∈ ((runPipeline (dateStage now :: rest) h c).build).headers := by
  rw [dateStage_effect, build_addHeader]
  exact List.mem_append.mpr (Or.inr (by simp))

/-! ## B1 — HEAD body suppression -/

/-- `HEAD` method (ASCII). -/
def mHEAD : Bytes := [72, 69, 65, 68]
/-- `GET` method (ASCII) — a non-HEAD witness. -/
def mGET : Bytes := [71, 69, 84]

/-- Strip the message body, keeping the head (status line + header fields). -/
def stripBody (r : Response) : Response := { r with body := [] }

/-- **The HEAD body-strip stage.** Always passes the request phase; on the
response phase, when the request method is `HEAD`, replaces the body with the
empty byte string (the head — every header field — is untouched); otherwise the
response passes through unchanged. -/
def headStripStage : Stage where
  name := "head-strip"
  onRequest := fun c => .continue c
  onResponse := fun c b => if c.req.method == mHEAD then b.mapResp stripBody else b

theorem headStripStage_statusStable : Stage.statusStable headStripStage := by
  intro c b
  show ((if c.req.method == mHEAD then b.mapResp stripBody else b).build).status = b.build.status
  by_cases h : (c.req.method == mHEAD) = true
  · rw [if_pos h, build_mapResp]; rfl
  · rw [if_neg h]

/-- **B1.** On a HEAD request the BUILT response body is empty — the body octets
are stripped at the funnel (RFC 7231 §4.3.2), for any tail and handler. -/
theorem headStripStage_strips_head_body (c : Ctx) (rest : List Stage) (handler : Ctx → Response)
    (h : (c.req.method == mHEAD) = true) :
    ((runPipeline (headStripStage :: rest) handler c).build).body = [] := by
  rw [pipeline_stage_effect headStripStage rest handler c c rfl]
  show ((if c.req.method == mHEAD then (runPipeline rest handler c).mapResp stripBody
         else (runPipeline rest handler c)).build).body = []
  rw [if_pos h, build_mapResp]
  rfl

/-- **Non-vacuity.** On a non-HEAD request the strip is a no-op — the whole
response passes through. So `headStripStage` does not blanket-wipe bodies; it
discriminates on the method. -/
theorem headStripStage_keeps_get_body (c : Ctx) (rest : List Stage) (handler : Ctx → Response)
    (h : (c.req.method == mHEAD) = false) :
    (runPipeline (headStripStage :: rest) handler c).build
      = (runPipeline rest handler c).build := by
  rw [pipeline_stage_effect headStripStage rest handler c c rfl]
  show ((if c.req.method == mHEAD then (runPipeline rest handler c).mapResp stripBody
         else (runPipeline rest handler c)).build) = _
  rw [if_neg (by rw [h]; simp)]

/-! ## Concrete witnesses (evaluate on real bytes) -/

/-- A HEAD request. -/
def headCtx : Ctx := { input := [], req := { method := mHEAD } }
/-- A GET request. -/
def getCtx : Ctx := { input := [], req := { method := mGET } }

theorem headCtx_is_head : (headCtx.req.method == mHEAD) = true := by decide
theorem getCtx_not_head : (getCtx.req.method == mHEAD) = false := by decide

/-- `"ok"` — a concrete 2-octet body (matches the probe's `/health` body). -/
def okBody : Bytes := [111, 107]

/-- **B1 witness.** A HEAD response to a handler that returns a body has its body
stripped to `[]`. -/
theorem head_body_stripped :
    ((runPipeline [headStripStage] (fun _ => Reactor.ok200 okBody) headCtx).build).body = [] :=
  headStripStage_strips_head_body headCtx [] _ headCtx_is_head

/-- The same handler on a GET keeps the 2-octet body — the strip is HEAD-only. -/
theorem get_body_kept :
    ((runPipeline [headStripStage] (fun _ => Reactor.ok200 okBody) getCtx).build).body = okBody := by
  rw [headStripStage_keeps_get_body getCtx [] _ getCtx_not_head]
  rfl

/-! ## Executable sanity checks -/

/-- A concrete clock value (RFC 1123) — stands in for the time FFI in `#guard`. -/
def sampleNow : Bytes := "Sun, 06 Nov 1994 08:49:37 GMT".toUTF8.toList

#guard ((runPipeline [dateStage sampleNow] (fun _ => Reactor.ok200 okBody)
          getCtx).build).headers.contains (dateName, sampleNow)
#guard ((runPipeline [headStripStage] (fun _ => Reactor.ok200 okBody) headCtx).build).body.length == 0
#guard ((runPipeline [headStripStage] (fun _ => Reactor.ok200 okBody) getCtx).build).body.length == 2

/-! ## Axiom audit -/

#print axioms dateStage_adds_date
#print axioms dateStage_statusStable
#print axioms headStripStage_strips_head_body
#print axioms headStripStage_keeps_get_body
#print axioms headStripStage_statusStable
#print axioms head_body_stripped
#print axioms get_body_kept

end Reactor.Stage.DateHeader
