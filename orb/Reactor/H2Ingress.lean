import Reactor.Contract
import Reactor.H2
import Reactor.Deploy
import Reactor.H2Response
import H2.Conn

/-!
# Reactor.H2Ingress — making the real HTTP/2 engine EXECUTE at runtime (h2c)

The H2 engine can be installed in the config yet never entered at runtime.
`deployConfig.h2Feed` IS the real engine (`Reactor.H2.h2FeedFn` — real frame
decode + HPACK arena decode + per-stream FSM, `deploy_h2_real`), and the
composition seam `h2_seam_reactor` proves it dispatches. The deployed orb `main`
drives a **plainH1** connection (`Proto.Conn.mkPlain`), so on that binary the H2
engine is *installed but never entered* — runtime-dead. "Installed in the config"
is not "executed on an input."

This file provides the **h2c prior-knowledge** ingress (RFC 9113 §3.3,
"HTTP/2 with prior knowledge"): a connection that STARTS parked in `.plainH2`,
needing no TLS and no crypto. Feeding it a real HTTP/2 HEADERS frame drives the
bytes straight through the REAL `h2FeedFn` at runtime.

* `mkH2c` — a fresh h2c `Proto.Conn`: `proto := .plainH2 h2InitVal []`, unblocked,
  header deadline armed. The `.plainH2` sibling of `Conn.mkPlain`, the initial
  connection an `h2` server exe hangs off.

* `h2cHeadersFrame` — a concrete, on-wire h2c HEADERS frame: stream 1,
  `END_STREAM|END_HEADERS`, HPACK payload `[0x82, 0x84]` (indexed static 2 =
  `:method: GET`, indexed static 4 = `:path: /`).

* The `#guard` below is the **runtime execution proof**: it drives `Reactor.step`
  over `deployConfig` on that frame, from `mkH2c`, and checks the submissions
  carry a `dispatch` of the request the real HPACK decoder produced
  (`GET` / `/`). The `#guard` forces evaluation of `Reactor.step → Proto.step →
  onBytes(.plainH2) → runH2 → h2FeedFn → framePump → H2.decode → decodeHeaderBlock
  → Store.resolve` — the real engine, run on a real input. (Same evaluation
  mechanism the `H2.Hpack` wire vectors use.)

* `h2c_runtime_dispatch` — the theorem form: from `mkH2c`, on any well-formed
  HEADERS frame that fills the buffer and whose HPACK payload decodes to `d`, the
  deployed reactor emits exactly `[dispatch (requestOfDecoded d), recycleBuffer bid]`
  — the real `h2FeedFn` executed (via `h2_seam_reactor` over `deployConfig`), then
  the reactor's copy-once buffer recycle. Not a correspondence beside the pipeline:
  the equality is of `Reactor.step deployConfig`'s own output.

The shipped orb exe still DEFAULTS to H1 (`Arena.Orb.main` runs a plainH1
connection); this file makes the H2 path **runtime-reachable and kernel-executed**,
and exposes `mkH2c` so an h2 listener exe can later select it.
-/

namespace Reactor
namespace H2Ingress

open Proto (Bytes)

/-! ## The h2c initial connection -/

/-- **`mkH2c` — a fresh h2c (prior-knowledge) connection.** Parked directly in
`.plainH2` with the fresh real H2 engine (`h2InitVal`: empty frame buffer, empty
stream table), send path unblocked, receive armed, the header-read deadline
armed. This is the `.plainH2` sibling of `Proto.Conn.mkPlain` — an `h2` listener
exe binds to it so the deployed reactor enters the real H2 engine on the very
first recv. -/
def mkH2c : Proto.Conn :=
  { proto := .plainH2 Reactor.H2.h2InitVal []
    sendBlocked := false
    pendingSend := []
    recvArmed := true
    timers := [.header] }

/-- `mkH2c` is parked in `.plainH2` with the fresh engine (the entry precondition
of `h2_seam_reactor`). -/
theorem mkH2c_proto : mkH2c.proto = .plainH2 Reactor.H2.h2InitVal [] := rfl

/-- `mkH2c`'s send path is unblocked (so the dispatch is not diverted to the park
queue by the send-block gate). -/
theorem mkH2c_unblocked : mkH2c.sendBlocked = false := rfl

/-! ## A concrete on-wire h2c HEADERS frame -/

/-- A concrete HTTP/2 HEADERS frame, h2c prior-knowledge:

```text
00 00 02   length = 2
01         type   = 0x1 (HEADERS)
05         flags  = END_STREAM(0x1) | END_HEADERS(0x4)
00 00 00 01  stream id = 1
82 84      HPACK: indexed static 2 (:method: GET), indexed static 4 (:path: /)
```

11 octets total; `H2.decode` completes consuming all 11 (`n = bs.length`), and the
2-octet HPACK payload decodes to `:method: GET`, `:path: /`. -/
def h2cHeadersFrame : Proto.Bytes :=
  [0x00, 0x00, 0x02, 0x01, 0x05, 0x00, 0x00, 0x00, 0x01, 0x82, 0x84]

/-! ## The runtime execution proof -/

/-- Extract the first `dispatch`ed request from a submission list (the reactor's
copy-once recycle rides after it). Lets the `#guard` compare the decoded request
without needing `DecidableEq` on the whole `RingSubmission` list. -/
def dispatchedReq : List RingSubmission → Option Proto.Request
  | RingSubmission.dispatch req :: _ => some req
  | _ :: rest => dispatchedReq rest
  | [] => none

/-- The request the real HPACK decoder produces from `h2cHeadersFrame`: method
`GET`, target `/`, version `HTTP/2`, no regular headers. -/
def expectedH2cReq : Proto.Request :=
  { method  := (String.toUTF8 "GET").toList
    target  := (String.toUTF8 "/").toList
    version := (String.toUTF8 "HTTP/2").toList
    headers := [] }

/-! **RUNTIME EXECUTION PROOF (`#guard`, kernel-evaluated).** Driving the DEPLOYED
reactor (`Reactor.step deployConfig`) from the h2c connection `mkH2c` on the real
HEADERS frame runs the bytes through the REAL H2 engine (`h2FeedFn` → `H2.decode`
→ `decodeHeaderBlock` → `Store.resolve`) and dispatches the HPACK-decoded request.
This evaluates the real functions on a real input — not a correspondence theorem,
an execution. -/
#guard
  dispatchedReq
      (Reactor.step Reactor.Deploy.deployConfig
        (Proto.State.active mkH2c)
        (RingEvent.recvInto 0 h2cHeadersFrame)).2
    = some expectedH2cReq

/-! ## The theorem -/

/-- **`h2c_runtime_dispatch` — the deployed H2 engine executes and dispatches.**
From the h2c connection `mkH2c` (parked in `.plainH2` with the fresh real engine),
the DEPLOYED reactor over `deployConfig`, on a well-formed HEADERS frame `bs` that
fills the framer buffer (`n = bs.length`) and whose HPACK payload decodes to `d`,
emits exactly

```text
[ dispatch (requestOfDecoded d), recycleBuffer bid ]
```

— the dispatch of the HPACK-decoded request (the REAL `h2FeedFn` executed, via
`h2_seam_reactor` over `deployConfig`, whose `h2Feed` IS `h2FeedFn` by
`deploy_h2_real`), followed by the reactor's copy-once buffer recycle. The
equality is of `Reactor.step deployConfig`'s own output, so this is the deployed
path being driven, not an island beside it. -/
theorem h2c_runtime_dispatch (bid : Nat) (bs payload : Bytes) (sid n : Nat)
    (es eh : Bool) (d : H2.Hpack.Decoded)
    (hframe : H2.decode bs Reactor.H2.h2MaxFrameSize
      = .complete (.headers sid es eh payload) n)
    (hfill : n = bs.length)
    (hhpack : H2.Hpack.decodeHeaderBlock Reactor.H2.h2Huffman Reactor.H2.h2EmptyStore payload
      = .ok d) :
    (Reactor.step Reactor.Deploy.deployConfig (Proto.State.active mkH2c)
        (RingEvent.recvInto bid bs)).2
      = [ RingSubmission.dispatch (Reactor.H2.requestOfDecoded d)
        , RingSubmission.recycleBuffer bid ] := by
  have hseam := Reactor.H2.h2_seam_reactor (cfg := Reactor.Deploy.deployConfig)
    Reactor.Deploy.deploy_h2_real.1 bs payload sid n es eh d mkH2c
    hframe hfill hhpack mkH2c_proto mkH2c_unblocked
  show ((Proto.step Reactor.Deploy.deployConfig (Proto.State.active mkH2c)
        (Proto.Input.bytesReceived bs)).2.map ofOutput
      ++ [RingSubmission.recycleBuffer bid])
    = [ RingSubmission.dispatch (Reactor.H2.requestOfDecoded d)
      , RingSubmission.recycleBuffer bid ]
  rw [hseam]
  rfl

/-! ## The h2c serve — a complete HTTP/2 response over a real socket

`h2c_runtime_dispatch` proves the real H2 engine DECODES the request and
dispatches it. But a real HTTP/2 client (`curl --http2-prior-knowledge`) needs
more than a dispatched request: RFC 9113 §3.4 requires the server to send a
**connection preface** — "a potentially empty SETTINGS frame" — as the first
frame, and §6.5 requires each peer to ACK the other's SETTINGS. Until those
frames arrive the client blocks and the connection times out.

The h2c fork used to hand the h2c bytes to the HTTP/1.1 serializer, so an h2c
client that spoke HTTP/2 on the way in got `HTTP/1.1 … CRLF …` on the way out —
no SETTINGS frame, so a real H2 client never completes. This section closes that
gap: `serveH2c` drives the real H2 engine on the post-preface frames, routes the
decoded request through the deployed guarded application layer, and emits a
complete, spec-conformant HTTP/2 response byte stream:

```text
  server SETTINGS (empty)          -- RFC 9113 §3.4 server connection preface
  SETTINGS with ACK flag           -- RFC 9113 §6.5 acknowledge the peer's SETTINGS
  HEADERS  (HPACK :status, END_HEADERS)   -- RFC 9113 §6.2, the response head
  DATA     (body, END_STREAM)             -- RFC 9113 §6.1, the response body
```

The HEADERS+DATA frames are the REAL `Reactor.H2Response.encodeResponse`, which
`h2_response_roundtrip` proves decode back through the real H2 frame + HPACK
decoders to exactly the status and body they encode. -/

open Proto (Bytes)

/-- The octet length of the HTTP/2 connection preface
`PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n` (RFC 9113 §3.4). The host strips nothing; the
h2c fork hands `serveH2c` the whole opening burst (preface + first frames) and
this is where the preface is consumed before the frames are decoded. -/
def h2cPrefaceLen : Nat := 24

/-- The **server connection preface**: an empty SETTINGS frame (RFC 9113 §3.4,
§6.5). `00 00 00 | 04 | 00 | 00 00 00 00` — length 0, type SETTINGS (0x4),
flags 0, stream 0. This MUST be the first frame the server sends; a real H2
client blocks until it arrives. -/
def serverSettings : Bytes :=
  [0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00]

/-- A **SETTINGS ACK** (RFC 9113 §6.5): the ACK flag (0x1) set, empty payload,
stream 0 — acknowledges the client's SETTINGS frame. -/
def settingsAck : Bytes :=
  [0x00, 0x00, 0x00, 0x04, 0x01, 0x00, 0x00, 0x00, 0x00]

/-- The stream the first h2c request rides (RFC 9113 §5.1.1: client-initiated
streams are odd; prior-knowledge clients open on stream 1). The response frames
are emitted on the same stream. -/
def h2cStream : Nat := 1

/-- Decode the request the client sent, by driving the REAL H2 engine over the
post-preface frames: `Reactor.step deployConfig` from the h2c connection
`mkH2c`, then pull the dispatched request out of the reactor's submissions. The
client's SETTINGS / WINDOW_UPDATE frames produce no dispatch (they are control
frames); the HEADERS frame dispatches the HPACK-decoded request. `none` only if
no HEADERS frame completed in the burst. -/
def h2cRequestOf (post : Bytes) : Option Proto.Request :=
  dispatchedReq
    (Reactor.step Reactor.Deploy.deployConfig
      (Proto.State.active mkH2c)
      (RingEvent.recvInto 0 post)).2

/-- The deployed guarded response for a decoded request — the SAME gate order as
the shipped HTTP/1.1 guarded serve (`Reactor.Deploy.serveGuarded`): a
path-traversal target is refused `404`, an undeclared/denied target is refused
`403`, and everything else is answered by the REAL application router
(`Reactor.App.handle` over `demoApp`: `/health → 200 "ok"`, `/static → 200`,
default `404`). So an h2c request meets the identical routing + policy the H1
path enforces — the H2 path is not a bypass. -/
def guardedResponse (req : Proto.Request) : Response :=
  if Reactor.Deploy.targetEscapes req then
    Reactor.Deploy.traversalBlocked404
  else
    match Reactor.Deploy.deployDecisionOf req with
    | none   => Reactor.Deploy.forbidden403
    | some _ => Reactor.App.handle Reactor.App.demoApp req

/-- **The deployed application behind the H2 connection engine.** Build the
`Proto.Request` from the engine-validated request head and route it through the
**full deployed middleware fold** (`Reactor.Deploy.deployRespFull2Of` — the same
thirteen-stage `deployStagesFull2` pipeline the HTTP/1.1 dataplane runs: the
jwt/ipfilter/rate/cache/redirect gates, the traversal/policy gates, and the
cors/gzip/htmlrewrite/security-headers/header transforms), then hand back the
HPACK-encoded response head (`Reactor.H2Response.encodeHeaderBlock`, field names
lowercased per RFC 9113 §8.2.1) plus the body for the engine to frame and pace.
So an H2 `/health` carries `Strict-Transport-Security` and `Server`; an H2
request with `Accept-Encoding: gzip` gets `Content-Encoding: gzip`; an H2
`/admin` without a bearer token gets `401` — the H2 path is not a bypass. -/
def h2cHandler : H2.Conn.Handler := fun r =>
  let req : Proto.Request :=
    { method := r.method
      target := r.target
      version := Reactor.H2.h2Version
      headers := r.headers }
  let resp := Reactor.Deploy.deployRespFull2Of r.raw req
  { block := Reactor.H2Response.encodeHeaderBlock resp.status resp.headers
    body := resp.body }

/-- **`serveH2c` — the one-shot h2c serve.** Drive the full HTTP/2 connection
engine (`H2.Conn.feed` — preface validation, per-frame RFC 9113 §4–§6 rules,
CONTINUATION assembly, HPACK with the real decode-side dynamic table, the
per-stream FSM, SETTINGS/PING acknowledgement, flow-controlled response DATA)
over the whole opening burst, with the deployed middleware fold as the
application (`h2cHandler`). The output opens with the server SETTINGS preface
(§3.4) and acknowledges the client's SETTINGS (§6.5.3), so a real H2 client
(`curl --http2-prior-knowledge`) completes its GET against these bytes.

One-shot-host contract: this entry serves a single buffered burst and the host
closes after writing. If the burst carried no request at all (no HEADERS frame)
and no error was signalled, a `403` response is appended on stream 1 so a
prior-knowledge client that sent only control frames gets a well-formed HTTP/2
refusal rather than a hang. An interactive host threads the engine state through
`drorb_h2c_conn_feed` instead and needs no such fallback. -/
def serveH2c (input : Bytes) : Bytes :=
  let (st, out, _close) := H2.Conn.feed Reactor.H2.h2Huffman h2cHandler {} input
  if st.maxSid = 0 && !st.closed then
    out ++ Reactor.H2Response.encodeResponse h2cStream Reactor.Deploy.forbidden403
  else out

/-! ## The interactive host seam (C ABI)

The one-shot `serveH2c` answers a single buffered burst. A conformant HTTP/2
server must also answer frames that arrive AFTER its SETTINGS reached the peer
(PING liveness probes, SETTINGS synchronization, WINDOW_UPDATE-paced response
bodies, RFC 9113 §6.5.3/§6.7/§6.9) — that requires the host to keep the
connection open and thread the engine state across socket reads. These two
exports are that seam: the host owns the socket and the loop; every protocol
decision stays in the verified engine. -/

/-- `drorb_h2c_conn_init` — a fresh engine connection state for one accepted
socket. The host treats it as an opaque object and threads it through
`drorb_h2c_conn_feed`. -/
@[export drorb_h2c_conn_init]
def drorbH2cConnInit (_ : UInt8) : H2.Conn.ConnState := {}

/-- `drorb_h2c_conn_feed` — feed one socket read to the engine. Returns the
successor connection state and one ByteArray: octet 0 is the close flag
(1 = write the remaining octets, then close the socket cleanly), octets 1..
are the response frames to write. -/
@[export drorb_h2c_conn_feed]
def drorbH2cConnFeed (st : H2.Conn.ConnState) (input : ByteArray) :
    H2.Conn.ConnState × ByteArray :=
  let (st', out, close) := H2.Conn.feed Reactor.H2.h2Huffman h2cHandler st input.toList
  (st', ByteArray.mk (((if close then (1 : UInt8) else 0) :: out).toArray))

/-! ### Runtime execution proofs (`#guard`, kernel-evaluated)

These force evaluation of the whole h2c serve on real inputs — the real H2 frame
decode, the real HPACK arena decode, the real router, and the real response
encode — and check the bytes a real client would parse. -/

/-! The server preface decodes, through the REAL `H2.decode`, as an empty
SETTINGS frame on stream 0 (not an ACK) — the RFC 9113 §3.4 connection preface. -/
#guard H2.decode serverSettings Reactor.H2.h2MaxFrameSize
  = .complete (.settings 0 false []) 9

/-! The ACK decodes as a SETTINGS frame with the ACK flag set (RFC 9113 §6.5). -/
#guard H2.decode settingsAck Reactor.H2.h2MaxFrameSize
  = .complete (.settings 0 true []) 9

/-- An on-wire h2c HEADERS frame for `GET /health`, stream 1,
`END_STREAM|END_HEADERS`: HPACK `:method: GET` (indexed static 2, `0x82`),
`:scheme: http` (indexed static 6, `0x86` — the engine enforces the RFC 9113
§8.3.1 mandatory request pseudo-headers), then `:path` (literal without
indexing over static name 4, value `/health`). -/
def healthHeadersFrame : Bytes :=
  [0x00, 0x00, 0x0b, 0x01, 0x05, 0x00, 0x00, 0x00, 0x01,
   0x82, 0x86, 0x04, 0x07, 0x2f, 0x68, 0x65, 0x61, 0x6c, 0x74, 0x68]

/-! **The end-to-end h2c serve, kernel-evaluated.** A realistic opening burst —
the real 24-octet client connection preface (`H2.Conn.clientPreface`; the engine
VALIDATES it per RFC 9113 §3.4), the client's (empty) SETTINGS frame, then the
`GET /health` HEADERS frame — driven through `serveH2c` emits: the server
SETTINGS preface (9 octets), the SETTINGS ACK (9 octets), then a response that
decodes — through the REAL `Reactor.H2Response.decodeResponse` (real `H2.decode`
+ real `H2.Hpack.decodeHeaderBlock` + real arena `Store.resolve`) — back to
exactly status `200` and body `ok`: the deployed router's `/health` answer,
delivered as real HTTP/2 frames. This is the bytes a real H2 client completes
on. -/
#guard
  (Reactor.H2Response.decodeResponse
    ((serveH2c (H2.Conn.clientPreface
        ++ serverSettings ++ healthHeadersFrame)).drop 18))
    = some (Reactor.natToDec 200, (String.toUTF8 "ok").toList)

end H2Ingress
end Reactor
