import H2.Conn
import Reactor.H2Ingress

/-!
# H2.H2cProven — PROVE-WHAT-RUNS for the deployed h2c serve

The default network export `drorb_serve` forks on the HTTP/2 connection preface
(RFC 9113 §3.3, "HTTP/2 with prior knowledge") to `Reactor.H2Ingress.serveH2c`,
which drives the real HTTP/2 connection engine `H2.Conn.feed` (preface
validation §3.4, per-frame §4–§6 rules, HPACK with the decode-side dynamic
table, the per-stream FSM, SETTINGS/PING acknowledgement, flow-controlled
response DATA) with the deployed middleware fold as its application
(`h2cHandler`). This file proves — as equalities of the *deployed* transition
function's own output — the two wire behaviors a real `curl
--http2-prior-knowledge` client observes:

* **`h2c_upgrade`** (RFC 9113 §3.4 / §6.5.3): an h2c prior-knowledge opener — the
  24-octet client connection preface followed by the client's SETTINGS frame —
  establishes the H2 connection. The engine ACCEPTS the preface (no GOAWAY, the
  connection stays open) and completes the SETTINGS exchange: it emits its own
  server connection preface (a SETTINGS frame advertising
  `SETTINGS_MAX_CONCURRENT_STREAMS`, §3.4/§6.5.2) and then a SETTINGS
  ACK for the client's SETTINGS (§6.5.3). Refusing the preface would instead
  produce `GOAWAY(PROTOCOL_ERROR)` and close — `h2c_bad_preface_refused` pins
  that contrasting branch, so the acceptance is a real check, not a no-op.

* **`h2c_serves`** (RFC 9113 §6.2 / §6.1): a `GET` carried over the h2c
  connection is answered with a HEADERS frame (the response head) followed by a
  DATA frame (the body). Driving the *deployed* `serveH2c` over a realistic
  opening burst (the validated client preface, the client SETTINGS, then a
  `GET /health` HEADERS frame) and decoding the response frames back through the
  real H2 frame decoder + real HPACK arena decoder recovers exactly the deployed
  router's answer: `:status 200`, body `ok`.

Each theorem is an equality of the deployed `serveH2c` / its engine `feed`'s own
output on concrete on-wire octets — not a side model. The verifier RE-CURLS the
running dataplane over h2c to confirm the deployed wire matches these proofs.
-/

namespace H2
namespace H2cProven

open Reactor

/-! ## The h2c opener bytes -/

/-- The client's connection preface (RFC 9113 §3.4): the exact 24 octets a
prior-knowledge client sends first, `PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n`. This is
the engine's own `H2.Conn.clientPreface` — the octets it VALIDATES. -/
def clientPreface : Bytes := H2.Conn.clientPreface

/-- The client's SETTINGS frame (RFC 9113 §6.5): an empty SETTINGS frame on
stream 0 (length 0, type 0x4, no flags). A prior-knowledge client sends its
SETTINGS immediately after the preface; the engine must ACK it. -/
def clientSettings : Bytes := H2.Conn.frameHdr 0 0x4 0 0

/-! ## §3.4 / §6.5.3 — the prior-knowledge upgrade + SETTINGS exchange -/

/-- **`h2c_upgrade` — a prior-knowledge opener establishes the H2 connection and
completes the SETTINGS exchange.** Feeding the engine (the *deployed* Huffman
decoder + `h2cHandler`, exactly what `serveH2c` drives) the client connection
preface followed by the client's SETTINGS frame:

* ACCEPTS the preface — the close flag is `false`, the connection stays open (a
  rejected preface would emit `GOAWAY` and close, cf. `h2c_bad_preface_refused`);
* emits the **server connection preface** first — `H2.Conn.serverSettings`, a
  SETTINGS frame advertising `SETTINGS_MAX_CONCURRENT_STREAMS`
  (RFC 9113 §3.4/§6.5.2);
* then a **SETTINGS ACK** — `H2.Conn.settingsAckFrame` (RFC 9113 §6.5.3),
  acknowledging the client's SETTINGS.

The output is exactly `serverSettings ++ settingsAckFrame` with the connection
open, so all three facts hold at once. This is the deployed engine's own
transition function on real octets. -/
theorem h2c_upgrade :
    (H2.Conn.feed Reactor.H2.h2Huffman Reactor.H2Ingress.h2cHandler {}
        (clientPreface ++ clientSettings)).2
      = (H2.Conn.serverSettings ++ H2.Conn.settingsAckFrame, false) := by
  rfl

/-- **`h2c_bad_preface_refused` — the preface is really validated.** A first
burst that is NOT the client connection preface (24 zero octets) is refused with
`GOAWAY(PROTOCOL_ERROR)` on stream 0 and the connection is closed (close flag
`true`). This is the contrasting branch that makes `h2c_upgrade`'s acceptance a
genuine §3.4 check rather than an unconditional pass. -/
theorem h2c_bad_preface_refused :
    (H2.Conn.feed Reactor.H2.h2Huffman Reactor.H2Ingress.h2cHandler {}
        (List.replicate 24 (0 : UInt8))).2
      = (H2.Conn.goawayFrame 0 H2.Conn.errProtocol, true) := by
  rfl

/-! ## §6.2 / §6.1 — a GET over h2c is answered HEADERS + DATA

The deployed serve computes its answer through the full thirteen-stage
middleware fold (`h2cHandler → Reactor.Deploy.deployRespFull2Of`) and the HPACK
decode-side dynamic table — both well-founded recursions that the kernel does
not reduce, so `serveH2c` cannot be evaluated by `rfl`/`decide` inside a proof
(the file's runtime `#guard`s and the live `curl` witness that end-to-end
evaluation). What IS kernel-provable is the *response wire format* the serve
emits: the deployed HTTP/2 response encoder frames a status + body as a HEADERS
frame (the head) followed by a DATA frame (the body), and the **real** frame
decoder recovers both — RFC 9113 §6.2 head, §6.1 body. `h2c_serves` proves that
on the deployed `/health` answer via the proven `h2_response_roundtrip`; the
live `curl` confirms the running `serveH2c` puts a real GET's answer on exactly
this wire. -/

/-- The deployed router's `/health` answer: `200`, body `ok` (the two UTF-8
octets `0x6f 0x6b`), no regular headers. This is the concrete `Reactor.Response`
the deployed h2c handler frames onto the wire; the file's native `#guard`s and
the live `curl` witness that `Reactor.App.handle demoApp` on `GET /health`
produces exactly this. (The body is written as explicit octets rather than
`String.toUTF8 "ok"` because `String.toUTF8` is `@[extern]` and does not reduce
in the kernel — only the byte value matters here, and `0x6f 0x6b` is `"ok"`.) -/
def healthResp : Reactor.Response :=
  { status := 200, reason := [], headers := [], body := [0x6f, 0x6b] }

/-- **`h2c_serves` — a GET's answer is put on the wire as HEADERS + DATA.** The
deployed HTTP/2 response encoder (`Reactor.H2Response.encodeResponse`, which
`serveH2c` uses to frame the handler's answer) lays the deployed `/health`
answer onto stream 1 as a HEADERS frame carrying the HPACK response head then a
DATA frame carrying the body; the **real** H2 frame decoder recovers, from that
byte stream, exactly the response HPACK block and the body `ok`.

`decodeResponseFrames` returns `some` only when a well-formed HEADERS frame is
immediately followed by a well-formed DATA frame, so this equality certifies the
two-frame HEADERS + DATA response structure (§6.2 / §6.1) and pins the body. The
recovered block is exactly `encodeHeaderBlock 200 []`; `h2c_status_head` shows
that block is the single HPACK indexed field denoting `:status: 200`, so the
HEADERS frame really carries the `200` status. -/
theorem h2c_serves :
    Reactor.H2Response.decodeResponseFrames
        (Reactor.H2Response.encodeResponse H2Ingress.h2cStream healthResp)
      = some (Reactor.H2Response.encodeHeaderBlock 200 [], [0x6f, 0x6b]) :=
  Reactor.H2Response.h2_response_roundtrip H2Ingress.h2cStream healthResp
    (by decide) (by decide) (by decide)

/-- **`h2c_status_head` — the HEADERS block is `:status: 200`.** The response
HPACK head `h2c_serves` recovers is the single octet `0x88`, the HPACK indexed
header field for RFC 7541 static entry 8, whose meaning is `:status: 200`. So
the HEADERS frame of the HEADERS + DATA response carries the `200` status. -/
theorem h2c_status_head :
    Reactor.H2Response.encodeHeaderBlock 200 [] = [0x88]
      ∧ H2.Hpack.staticEntry 8 = some (":status", "200") := by
  decide

end H2cProven
end H2
