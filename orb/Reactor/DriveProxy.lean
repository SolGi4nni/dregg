import Reactor.Contract
import Reactor.ServeStep
import Reactor.ServeStream
import Reactor.DriveCache

/-!
# Reactor.DriveProxy — the Phase-2 effect-scheduler proof (`drive_proxy_refines`)

The proxy **effect program** is proven ONCE, in tree, exactly like the cache arm:
`Reactor.ServeStep.serveStep` / `resumeStep` decide the whole fabric (whether to
proxy, WHICH backend, what to serve on the upstream reply) and the proxy-arm
theorems fix its meaning:

* `serveStep_proxy_yields` — a proxy request `.yield`s `.proxyDial id input` to the
  proven-picked backend, with the full response-transform fold as its continuation;
* `serveStep_backend_up` — the yielded backend is genuinely up (`mask.testBit id`);
* `serveStep_proxy_resume` — resuming on the upstream reply `.done`s
  `proxyRespTransform input upstream` (the reply parsed, run through
  cors / gzip / security-headers / header, and re-serialized);
* `Reactor.ServeStream.proxy_emit_refines` — the STREAMED upstream body (bounded RSS,
  never buffered whole) is byte-equal to the buffered proxy delivery.

The **per-scheduler** obligation — the one thing the io_uring reactor adds — is a
REFINEMENT: the reactor's effect-driving loop feeds the upstream reply bytes into the
serve continuation. This file discharges it for the PROXY effect, following the
Phase-1 `Reactor.DriveCache` template exactly.

## The seam the driver crosses (identical to the cache arm)

`Reactor.Contract` is the copy-once WIRE reactor: `RingEvent.effectComplete` (added
additively in Phase 1) is the effect-completion edge. It is INERT at the wire FSM —
its result bytes do NOT belong to `Proto` — and is consumed HERE, threaded into
`resumeStep`. For a proxy the `effectComplete` payload is the UPSTREAM REPLY (the id
the reactor dialed via `connectUpstream` / `sendUpstream`, whose bytes the recv-loop
accumulated). The driver (`driveProxy`) is the SAME generic result-threading loop as
`driveCache` — the effect scheduler is generic; only the effect KIND (and the proven
arm theorems that give its meaning) differ. `driveProxy` reuses
`Reactor.DriveCache.resultsOf` verbatim.

## What `drive_proxy_refines` proves (and does not)

`drive_proxy_refines` proves the MODEL — the Contract reactor threading the upstream
reply CQE into the proven serve — drives the proxy effect faithfully:

* the reactor submits `.proxyDial id input` with the PROVEN-picked backend
  (`serveStep_proxy_yields`), and that backend is genuinely up
  (`serveStep_backend_up`);
* an `effectComplete upstream` carrying the upstream reply drives to
  `proxyRespTransform input upstream` — the reply parsed, transformed, re-serialized
  (`serveStep_proxy_resume`).

The bytes fed into the continuation are exactly the effect payload carried by the
ingress event (`resultsOf`), so this is a real refinement — the reactor feeds the
UPSTREAM's actual reply, not an invented one. `drive_proxy_batch` further composes the
proxy drive with `proxy_emit_refines`, so the reactor-driven (buffered) proxy response
equals the STREAMED emit (head chunk ++ paced upstream-body chunks) for any chunk size
— the design's `uring_serve = <streaming factor> ∘ resumeStep_semantics ∘
drive_effects_refines`, with `proxy_emit_refines` the proxy streaming factor (so a
native SQE proxy need not materialize the whole upstream body).

**The realization boundary (honest).** This proves the MODEL. The Rust io_uring proxy
dispatch (the `TAG_YIELD_PROXY` arm) REALIZES this model — it submits the connect /
send / recv SQEs on a second fd, accumulates the upstream reply, and delivers those
bytes to `drorb_serve_resume`. That realization is the SAME named gap as reactor-model
↔ `uring.rs` (it is NOT proven here; it is the model's realization boundary). The Rust
is not claimed proven.
-/

namespace Reactor.DriveProxy

open Proto (Bytes)
open Reactor (RingEvent)
open Reactor.ServeStep

/-- **The reactor's effect-driving loop over the PROXY serve program.** Identical in
shape to `Reactor.DriveCache.driveServe`: submit the serve's yielded effect and, on the
`effectComplete` CQE, feed the result bytes (here the UPSTREAM REPLY) into the
continuation. Because the continuation replay is pure (`resumeStep` re-runs `serveStep`
and feeds the recorded results — the defunctionalization-by-replay the FFI uses), the
reactor-driven outcome is exactly `resumeStep mask input (resultsOf events)`. Reuses
`Reactor.DriveCache.resultsOf` verbatim — the effect scheduler is generic; only the
effect kind differs. -/
def driveProxy (mask : Nat) (input : Bytes) (events : List RingEvent) : Step :=
  resumeStep mask input (Reactor.DriveCache.resultsOf events)

/-- The generic driver is the same loop the cache arm uses; the proxy is a different
effect KIND, not a different scheduler. -/
theorem driveProxy_eq_driveCache (mask : Nat) (input : Bytes) (events : List RingEvent) :
    driveProxy mask input events = Reactor.DriveCache.driveServe mask input events := rfl

/-- The built (parsed → transformed) proxy `Response` for an upstream reply — the value
`proxyRespTransform` re-serializes. Naming it lets the batch composition split it into
head + body via `serialize_split`. -/
def builtProxyResp (input upstream : Bytes) : Reactor.Response :=
  (Reactor.Pipeline.runPipeline proxyRespStages
    (fun _ => parseUpstream upstream) (Reactor.Deploy.ctxOf input)).build

/-- `proxyRespTransform` is exactly `serialize` of the built proxy response. -/
theorem proxyRespTransform_eq (input upstream : Bytes) :
    proxyRespTransform input upstream = Reactor.serialize (builtProxyResp input upstream) := rfl

/-! ## The proxy drive (reusing the proven serve program verbatim) -/

/-- **DIAL.** The reactor submits `.proxyDial id input`, receives `effectComplete
upstream` with the upstream reply, feeds it in, and drives to
`proxyRespTransformGated input upstream` — the reply REFUSED (`502`) if its head block
carries a bare LF (RFC 9112 §2.2), otherwise parsed, run through the full
response-transform fold, and re-serialized (`serveStep_proxy_resume`).

RESTATED under the seam gate: same theorem, over the object the resume now crosses. The
pre-gate statement survives as `drive_proxy_dial_clean` below. -/
theorem drive_proxy_dial (mask : Nat) (input upstream : Bytes) (id : BackendId)
    (h : isApiPath input = true)
    (hpick : Reactor.ProxyDial.pick mask (stickyKey input) = some id) :
    driveProxy mask input [RingEvent.effectComplete upstream]
      = .done (proxyRespTransformGated input upstream) := by
  unfold driveProxy
  rw [Reactor.DriveCache.resultsOf_lookup]
  exact serveStep_proxy_resume mask input upstream id h hpick

/-- **★ The reactor drive REFUSES a bare-LF upstream reply.** The bytes the reactor
`.done`s for an upstream head block with ambiguous line terminators are the `502 Bad
Gateway` response and nothing else — the crafted head never reaches the client through
this driver. -/
theorem drive_proxy_dial_rejected (mask : Nat) (input upstream : Bytes) (id : BackendId)
    (h : isApiPath input = true)
    (hpick : Reactor.ProxyDial.pick mask (stickyKey input) = some id)
    (hbare : Body.FrameRaw.noBareLF (upstreamHeadBlock upstream) = false) :
    driveProxy mask input [RingEvent.effectComplete upstream]
      = .done (gatewayError false) := by
  rw [drive_proxy_dial mask input upstream id h hpick,
      seamGate_bytes_rejected input upstream hbare]

/-- **★ No regression.** On an upstream head block with unambiguous terminators the
reactor drive produces exactly the pre-gate bytes — the ORIGINAL `drive_proxy_dial`
statement, under the hypothesis the gate admits on. -/
theorem drive_proxy_dial_clean (mask : Nat) (input upstream : Bytes) (id : BackendId)
    (h : isApiPath input = true)
    (hpick : Reactor.ProxyDial.pick mask (stickyKey input) = some id)
    (hclean : Body.FrameRaw.noBareLF (upstreamHeadBlock upstream) = true) :
    driveProxy mask input [RingEvent.effectComplete upstream]
      = .done (proxyRespTransform input upstream) := by
  rw [drive_proxy_dial mask input upstream id h hpick,
      seamGate_bytes_clean input upstream hclean]

/-- **THE PHASE-2 THEOREM — `drive_proxy_refines`.** For a proxy request whose proven
pick finds an eligible backend, the reactor threading the upstream-reply CQE into the
proven serve drives the proxy effect faithfully, all obligations at once:

1. it first submits `.proxyDial id input` with the PROVEN-picked backend
   (`serveStep_proxy_yields`);
2. that backend is genuinely up — `mask.testBit id = true` (`serveStep_backend_up`), so
   the routing hypothesis has a real forced consequence (not a self-contradictory,
   vacuously-dischargeable premise);
3. for ANY upstream reply, the `effectComplete upstream` drives to
   `proxyRespTransformGated input upstream` — the reply refused with a `502` if its head
   block carries a bare LF (RFC 9112 §2.2), otherwise parsed, transformed, re-serialized;
4. and the refusal is REAL: a bare-LF upstream head block drives to the `502` bytes.

The bytes fed into the continuation are the effect payload carried by the ingress event
(`resultsOf`), and the output is the proven proxy semantics — so the io_uring proxy
dispatch (modelled here) is a faithful interpreter of the proven serve program. Not
vacuous: the yield names a genuinely-up backend, and each upstream reply maps to a
specific, upstream-dependent transformed response (see the runnable checks: the
threaded response carries real HSTS, and the upstream body flows verbatim into the
streamed output). Reuses the proxy-arm theorems verbatim; only the driving is new. -/
theorem drive_proxy_refines (mask : Nat) (input : Bytes) (id : BackendId)
    (h : isApiPath input = true)
    (hpick : Reactor.ProxyDial.pick mask (stickyKey input) = some id) :
    serveStep mask input
        = .yield (.proxyDial id input) (fun up => .done (proxyRespTransformGated input up))
    ∧ mask.testBit id = true
    ∧ (∀ upstream : Bytes,
        driveProxy mask input [RingEvent.effectComplete upstream]
          = .done (proxyRespTransformGated input upstream))
    ∧ (∀ upstream : Bytes,
        Body.FrameRaw.noBareLF (upstreamHeadBlock upstream) = false →
        driveProxy mask input [RingEvent.effectComplete upstream]
          = .done (gatewayError false)) :=
  ⟨serveStep_proxy_yields mask input id h hpick,
   serveStep_backend_up mask input id hpick,
   fun upstream => drive_proxy_dial mask input upstream id h hpick,
   fun upstream hbare => drive_proxy_dial_rejected mask input upstream id h hpick hbare⟩

/-! ## Composing the drive refinement with the STREAMED proxy emit

The design's chain is `uring_serve = <streaming factor> ∘ resumeStep_semantics ∘
drive_effects_refines`. `drive_proxy_refines` is the `drive_effects_refines` factor;
`serveStep_proxy_resume` is the `resumeStep_semantics` it reuses; the proxy streaming
factor is `Reactor.ServeStream.proxy_emit_refines` (NOT `serveTrace_refines`, which is
the NON-proxy deployed serve — the proxy body is the upstream reply, not the deployed
fold). Here they compose: the reactor-driven (buffered) proxy response is byte-for-byte
the streamed emit — the head chunk (core-built) followed by the paced upstream-body
chunks — whatever the chunk size. So a native SQE proxy can STREAM the upstream body
(bounded RSS) and still deliver exactly the bytes this drive produces. -/

/-- **The reactor-driven proxy response equals the STREAMED emit, at any chunk size.**
The bytes the reactor produces after driving the proxy dial (`drive_proxy_dial`) are
exactly what a streaming proxy emits: the response HEAD as one chunk, then the upstream
body streamed host-side from a window `bodyWin` (whose bytes are the transformed
response body) paced into bounded `cfg.chunk` chunks (`proxy_emit_refines`). The only
hypothesis on the stream is that the body window carries the transformed body — the
faithfulness the shell's upstream-recv owes. Per-scheduler drive refinement composed
with the streamed-body refinement, end to end. -/
theorem drive_proxy_batch (cfg : ServeStream.ServeConfig) (mask : Nat)
    (input upstream : Bytes) (id : BackendId) (bodyWin : Datapath.SpanBytes)
    (h : isApiPath input = true)
    (hpick : Reactor.ProxyDial.pick mask (stickyKey input) = some id)
    (hclean : Body.FrameRaw.noBareLF (upstreamHeadBlock upstream) = true)
    (hbody : bodyWin.denote = (builtProxyResp input upstream).body) :
    (ServeStream.srcChunkList cfg (ServeStream.serveRespHead (builtProxyResp input upstream))
        (ServeStream.BodySrc.proxy bodyWin)).flatten
      = stepDone (driveProxy mask input [RingEvent.effectComplete upstream]) := by
  rw [drive_proxy_dial_clean mask input upstream id h hpick hclean,
    ServeStream.proxy_emit_refines, hbody]
  show ServeStream.serveRespHead (builtProxyResp input upstream)
        ++ (builtProxyResp input upstream).body
      = proxyRespTransform input upstream
  rw [proxyRespTransform_eq]
  exact (ServeStream.serialize_split (builtProxyResp input upstream)).symm

/-! ## Runnable checks — `driveProxy` is genuine (not constant), the transform is real -/

-- With no completion the reactor has driven nothing: it is still the initial serve
-- decision (so an UPSTREAM REPLY is genuinely REQUIRED to reach `.done` on a yield).
example (mask : Nat) (input : Bytes) : driveProxy mask input [] = serveStep mask input := by
  simp [driveProxy, resumeStep, Reactor.DriveCache.resultsOf]
-- Wire events carry NO effect result — `resultsOf` filters them out, keeping only the
-- `effectComplete` (upstream-reply) payload.
example (up : Bytes) :
    Reactor.DriveCache.resultsOf
        [RingEvent.writeReady, RingEvent.effectComplete up, RingEvent.sendComplete] = [up] := rfl
-- The threaded proxy response is a GENUINE transform, not a passthrough: for ANY
-- upstream reply it carries the real HSTS header (a proxied response gets security
-- headers like a normal one). So the continuation does real work.
example (input upstream : Bytes) :
    (Reactor.Stage.SecurityHeaders.hstsHeaderName, Reactor.Stage.SecurityHeaders.hstsHeaderVal)
      ∈ (builtProxyResp input upstream).headers :=
  proxyRespStages_hsts upstream (Reactor.Deploy.ctxOf input)
-- CONCRETE upstream-reply byte flow: the upstream body bytes ("BODY") appear verbatim,
-- in order, after the head ("HEAD") in the streamed proxy output (`proxy_emit_refines`)
-- — the streamed delivery reproduces the upstream reply exactly.
example (cfg : ServeStream.ServeConfig) :
    (ServeStream.srcChunkList cfg [72, 69, 65, 68]
        (ServeStream.BodySrc.proxy (Datapath.SpanBytes.full (ByteArray.mk #[66, 79, 68, 89])))).flatten
      = [72, 69, 65, 68, 66, 79, 68, 89] := by
  rw [ServeStream.proxy_emit_refines, Datapath.SpanBytes.denote_full]; rfl
-- The wire reactor is inert on an effect completion (no submission, no state change) —
-- the upstream reply is threaded to the serve, not the wire FSM.
example (cfg : Proto.Config) (s : Proto.State) (up : Bytes) :
    Reactor.step cfg s (.effectComplete up) = (s, []) := rfl

/-! ## The HEAD/BODY-SPLIT proxy drive (the native STREAMING prerequisite)

`drive_proxy_dial` feeds ONE `effectComplete upstream` carrying the WHOLE reply — the
native path must buffer the whole body. A native STREAMING io_uring proxy instead
delivers the core-decided response HEAD (`ServeStep.proxyRespHead`) as the first
completion and the transformed body as a SEQUENCE of body-chunk completions streamed
host-side (bounded RSS, never buffered whole). `driveProxyStream` threads that head +
body-chunk sequence through `ServeStep.proxyStreamResume`; `drive_proxy_stream_refines`
proves it reaches the SAME `.done` bytes as the buffered `drive_proxy_dial`. This is the
theorem a native SQE proxy realizes: it need not materialize the whole upstream body.

`drive_proxy_stream_emits` closes the loop through the Stage-3 streaming factor
`Reactor.ServeStream.proxy_emit_refines`: the actual streamed emit (the head chunk
followed by the paced body chunks, `srcChunkList`) is byte-for-byte the split drive's
result — so the streamed delivery equals the buffered proxy response at any chunk size.

**Residual (honest, carried from `ServeStep`).** `ServeStep.proxyRespHead` carries the
derived `Content-Length` (a function of the transformed body length; the gzip stage
genuinely re-encodes the body). So this proves head-FIRST delivery is faithful to the
buffered bytes, not yet head-BEFORE-body emission. The minimal additional lemma to
unlock true zero-buffer early-head streaming is a head that is independent of the body
bytes (upstream `Content-Length` trust + a body-length-preserving transform, or chunked
transfer-encoding) — the deferred scan-gated early-head obligation `ServeStream` names. -/

/-- Feeding a list of effect-result payloads as `effectComplete` events recovers exactly
those payloads through `resultsOf` (the wire events carry none). -/
theorem resultsOf_effectCompletes (rs : List Bytes) :
    Reactor.DriveCache.resultsOf (rs.map RingEvent.effectComplete) = rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    show r :: Reactor.DriveCache.resultsOf (rs.map RingEvent.effectComplete) = r :: rs
    rw [ih]

/-- **The reactor's HEAD/BODY-SPLIT proxy driver.** The first effect completion is the
core-decided response HEAD; the remaining completions are the transformed body streamed
as chunks. The reactor assembles `head ++ (body chunks)` via `ServeStep.proxyStreamResume`
— the streamed proxy response, the whole body never buffered in the core. Reuses
`Reactor.DriveCache.resultsOf` verbatim; the body chunks flow as ordinary completions. -/
def driveProxyStream (events : List RingEvent) : Step :=
  match Reactor.DriveCache.resultsOf events with
  | []             => .done []
  | head :: chunks => ServeStep.proxyStreamResume head chunks

/-- **THE HEAD/BODY-SPLIT PROXY DRIVE REFINEMENT — `drive_proxy_stream_refines`.** For a
proxy request whose proven pick finds an eligible backend, the reactor delivering the
core-decided response HEAD (`ServeStep.proxyRespHead`) as the first completion and the
transformed body as a SEQUENCE of streamed chunks (whose concatenation is the transformed
body) drives to the SAME `.done` bytes as the buffered whole-reply drive
(`drive_proxy_dial`) — `proxyRespTransform input upstream`, byte-for-byte. So a NATIVE
streaming io_uring proxy that never buffers the whole upstream body in the core realizes
exactly the proven proxy semantics. Faithful (proven EQUAL to the buffered drive),
non-vacuous (`hpick` forces `id` genuinely up; the head carries real HSTS; the body
chunks are the real transformed body split). -/
theorem drive_proxy_stream_refines (mask : Nat) (input upstream : Bytes) (id : BackendId)
    (chunks : List Bytes) (h : isApiPath input = true)
    (hpick : Reactor.ProxyDial.pick mask (stickyKey input) = some id)
    (hclean : Body.FrameRaw.noBareLF (ServeStep.upstreamHeadBlock upstream) = true)
    (hchunks : chunks.flatten = (ServeStep.proxyBuiltResp input upstream).body) :
    driveProxyStream (RingEvent.effectComplete (ServeStep.proxyRespHead input upstream)
        :: chunks.map RingEvent.effectComplete)
      = driveProxy mask input [RingEvent.effectComplete upstream] := by
  rw [drive_proxy_dial_clean mask input upstream id h hpick hclean]
  have hres : Reactor.DriveCache.resultsOf
      (RingEvent.effectComplete (ServeStep.proxyRespHead input upstream)
        :: chunks.map RingEvent.effectComplete)
      = ServeStep.proxyRespHead input upstream :: chunks :=
    resultsOf_effectCompletes (ServeStep.proxyRespHead input upstream :: chunks)
  unfold driveProxyStream
  rw [hres]
  exact ServeStep.proxyStreamResume_faithful input upstream chunks hchunks

/-- **The streamed proxy EMIT equals the split drive, at any chunk size.** The bytes a
native streaming proxy actually writes — the response HEAD as one chunk followed by the
upstream body streamed host-side from a window `bodyWin` (whose bytes are the transformed
response body) paced into bounded `cfg.chunk` chunks (`ServeStream.srcChunkList`) — are
byte-for-byte the split drive's result (`driveProxyStream` over the head completion + the
paced body chunks). Uses the Stage-3 streaming factor `proxy_emit_refines`. So the native
streamed delivery reproduces the buffered proxy response exactly, whatever the chunk size,
without ever materializing the whole upstream body in the core. -/
theorem drive_proxy_stream_emits (cfg : ServeStream.ServeConfig) (mask : Nat)
    (input upstream : Bytes) (id : BackendId) (bodyWin : Datapath.SpanBytes)
    (h : isApiPath input = true)
    (hpick : Reactor.ProxyDial.pick mask (stickyKey input) = some id)
    (hclean : Body.FrameRaw.noBareLF (ServeStep.upstreamHeadBlock upstream) = true)
    (hbody : bodyWin.denote = (ServeStep.proxyBuiltResp input upstream).body) :
    (ServeStream.srcChunkList cfg (ServeStep.proxyRespHead input upstream)
        (ServeStream.BodySrc.proxy bodyWin)).flatten
      = stepDone (driveProxyStream
          (RingEvent.effectComplete (ServeStep.proxyRespHead input upstream)
            :: (ServeStream.srcChunks cfg (ServeStream.BodySrc.proxy bodyWin)).map
                 RingEvent.effectComplete)) := by
  have hchunks : (ServeStream.srcChunks cfg (ServeStream.BodySrc.proxy bodyWin)).flatten
      = (ServeStep.proxyBuiltResp input upstream).body := by
    rw [ServeStream.srcChunks_flatten]
    show bodyWin.denote = _
    exact hbody
  rw [drive_proxy_stream_refines mask input upstream id _ h hpick hclean hchunks,
    drive_proxy_dial_clean mask input upstream id h hpick hclean]
  show (ServeStream.srcChunkList cfg (ServeStep.proxyRespHead input upstream)
      (ServeStream.BodySrc.proxy bodyWin)).flatten = proxyRespTransform input upstream
  rw [ServeStream.proxy_emit_refines, hbody]
  exact (ServeStep.proxyRespTransform_split input upstream).symm

-- The split drive with the head completion + a one-chunk body completion reaches the
-- buffered transform — an UPSTREAM-DEPENDENT response, not a constant.
example (input upstream : Bytes) (mask : Nat) (id : BackendId)
    (h : isApiPath input = true)
    (hpick : Reactor.ProxyDial.pick mask (stickyKey input) = some id)
    (hclean : Body.FrameRaw.noBareLF (ServeStep.upstreamHeadBlock upstream) = true) :
    driveProxyStream [RingEvent.effectComplete (ServeStep.proxyRespHead input upstream),
        RingEvent.effectComplete (ServeStep.proxyBuiltResp input upstream).body]
      = driveProxy mask input [RingEvent.effectComplete upstream] :=
  drive_proxy_stream_refines mask input upstream id
    [(ServeStep.proxyBuiltResp input upstream).body] h hpick hclean (by simp)

/-! ## Axiom audit -/

#print axioms drive_proxy_stream_refines
#print axioms drive_proxy_stream_emits
#print axioms resultsOf_effectCompletes

#print axioms drive_proxy_refines
#print axioms drive_proxy_dial
#print axioms drive_proxy_dial_rejected
#print axioms drive_proxy_dial_clean
#print axioms drive_proxy_batch

end Reactor.DriveProxy
