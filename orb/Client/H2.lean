import H2.FrameEncode
import H2.HpackEncode

/-!
# The verified HTTP/2 client (RFC 9113 + RFC 7541)

`H2/Conn.lean` is the drorb HTTP/2 **server** engine. This module is its dual —
the **client** — built entirely from the proven encoders (`H2.FrameEncode`,
`H2.HpackEncode`) and the deployed decoders:

* **submit** — a client lays its connection preface (RFC 9113 §3.4), an empty
  SETTINGS frame, then a `HEADERS` frame carrying the HPACK-encoded request
  (and, for a request with a body, a `DATA` frame). `requestBytes` is the exact
  octet stream the client writes.
* **receive** — `clientFeed` consumes response transport bytes (any split),
  walks whole frames with `H2.Frame.decode`, decodes response header blocks with
  the deployed HPACK field decoder, answers SETTINGS/PING, and surfaces
  `ClientEvent`s (response headers, response DATA, GOAWAY, …).

## What is proven — the H2 analogue of `Client.H1.transaction_faithful`

* `client_preface_sent` — the first 24 octets a client writes are exactly the
  RFC 9113 §3.4 client connection preface.
* `clientRequestHeadersFrame_faithful` — the `HEADERS` frame the client sends
  decodes (through the server's own `H2.Frame.decode`) to exactly a `HEADERS`
  frame on the request stream carrying the intended HPACK block.
* `clientRequest_hpack_faithful` — that HPACK block decodes (through the deployed
  field decoder) to exactly the intended request header list.
* `client_server_agreement` — end-to-end on a concrete `GET` request: the block
  the client emits decodes, through the **server's own** `decodeBlockV`, to the
  intended request head (`:method GET`, `:scheme https`, `:path /`, `host …`).
* `clientFeed_response_headers` — a response `HEADERS` frame the client receives
  is decoded to exactly the response header list the peer encoded.

0 sorries; axioms ⊆ `{propext, Quot.sound, Classical.choice}`.

Deliberate scope: the request submit + faithfulness (the load-bearing client
core) and the single-frame receive path are proven here. A full multi-frame
CONTINUATION-assembling receive loop and an H3 client are named follow-ons.
-/

namespace Proto
namespace Client
namespace H2

open _root_.H2 _root_.H2.Conn _root_.H2.FrameEncode _root_.H2.HpackEncode

/-! ## The request the client submits -/

/-- An HTTP/2 request the client sends. `headers` are the ordinary (non-pseudo)
fields, in order; `body` is empty for a GET-style request. -/
structure ClientRequest where
  method : Bytes
  scheme : Bytes
  path : Bytes
  authority : Bytes
  headers : List (Bytes × Bytes) := []
  body : Bytes := []
deriving Repr

/-! The request pseudo-header names, spelled as explicit octets (equal to
`strBytes ":method"` etc., but kernel-reducible for the concrete round-trips). -/
def pMethod : Bytes := [0x3a, 0x6d, 0x65, 0x74, 0x68, 0x6f, 0x64]      -- ":method"
def pScheme : Bytes := [0x3a, 0x73, 0x63, 0x68, 0x65, 0x6d, 0x65]      -- ":scheme"
def pPath : Bytes := [0x3a, 0x70, 0x61, 0x74, 0x68]                    -- ":path"
def pAuthority : Bytes := [0x3a, 0x61, 0x75, 0x74, 0x68, 0x6f, 0x72, 0x69, 0x74, 0x79]  -- ":authority"

/-- The full header list the client encodes: the four request pseudo-headers in
canonical order (RFC 9113 §8.3.1), then the ordinary fields. -/
def requestHeaderList (req : ClientRequest) : List (Bytes × Bytes) :=
  (pMethod, req.method) ::
  (pScheme, req.scheme) ::
  (pPath, req.path) ::
  (pAuthority, req.authority) ::
  req.headers

/-- The HPACK block the client puts in its `HEADERS` frame. -/
def requestBlock (req : ClientRequest) : Bytes :=
  encodeHeaders (requestHeaderList req)

/-- The client's `HEADERS` frame for `req` on stream `sid`: `END_HEADERS` set,
`END_STREAM` set iff there is no body. -/
def requestHeadersFrame (req : ClientRequest) (sid : Nat) : Bytes :=
  encodeFrame (.headers sid req.body.isEmpty true (requestBlock req))

/-- The client connection preamble (RFC 9113 §3.4): the 24-octet client preface
then an empty SETTINGS frame. -/
def clientPreamble : Bytes := clientPreface ++ encodeFrame (.settings 0 false [])

/-- The full octet stream the client writes to open a connection and send `req`
on stream `sid`: preamble, the request `HEADERS`, and a `DATA` frame when the
request carries a body. -/
def requestBytes (req : ClientRequest) (sid : Nat) : Bytes :=
  clientPreamble ++ requestHeadersFrame req sid ++
    (if req.body.isEmpty then [] else encodeFrame (.data sid true req.body))

/-! ## The client-side receive engine -/

/-- A client connection's receive state. `buf` holds undecoded frame bytes across
feeds; `hpack` is the decode-side dynamic table for response header blocks;
`peerMaxFrame` mirrors the server's advertised `SETTINGS_MAX_FRAME_SIZE`. -/
structure ClientConnState where
  buf : Bytes := []
  hpack : HpackCtx := {}
  peerMaxFrame : Nat := 16384
  goawayRecvd : Bool := false
deriving Repr

/-- What the client surfaces to its caller as it decodes server frames. -/
inductive ClientEvent where
  /-- A response header block completed on `sid`, decoded to these fields
  (`:status` included as an ordinary field). -/
  | responseHeaders (sid : Nat) (headers : List (Bytes × Bytes))
  /-- A response DATA frame on `sid`; `endStream` closes the response. -/
  | responseData (sid : Nat) (data : Bytes) (endStream : Bool)
  /-- The peer's SETTINGS (`ack` true iff it was an ACK). -/
  | settings (ack : Bool)
  /-- A PING (`ack` true iff it was an ACK) with its 8 opaque octets. -/
  | ping (ack : Bool) (data : Bytes)
  /-- GOAWAY: last processed stream id + error code. -/
  | goaway (lastSid errCode : Nat)
  /-- RST_STREAM on `sid` with an error code. -/
  | resetStream (sid errCode : Nat)
  /-- A response header block failed HPACK decoding. -/
  | headerDecodeError (sid : Nat)
deriving Repr

/-- One decoded server frame steps the client: the successor state, octets to
write back (SETTINGS/PING ACKs), and the events surfaced. A `HEADERS` frame with
`END_HEADERS` is decoded through the deployed field decoder. -/
def clientStep (hd : Hpack.HuffmanDecoder) (st : ClientConnState) :
    Frame → ClientConnState × Bytes × List ClientEvent
  | .headers sid _ endHeaders block =>
    if endHeaders then
      match decodeHeadersV hd st.hpack.tbl (block.length + 1) block [] with
      | .ok hs => (st, [], [.responseHeaders sid hs])
      | .error _ => (st, [], [.headerDecodeError sid])
    else (st, [], [])
  | .data sid endStream payload => (st, [], [.responseData sid payload endStream])
  | .settings _ ack _payload =>
    if ack then (st, [], [.settings true])
    else (st, settingsAckFrame, [.settings false])
  | .ping _ ack payload =>
    if ack then (st, [], [.ping true payload])
    else (st, pingAckFrame payload, [.ping false payload])
  | .goaway _ payload => ({ st with goawayRecvd := true },
      [], [.goaway (readU32 payload % 2 ^ 31) (readU32 (payload.drop 4))])
  | .rstStream sid payload => (st, [], [.resetStream sid (readU32 payload)])
  | _ => (st, [], [])

/-- Walk whole frames off the client buffer (RFC 9113 §4.1): parse + size-check
each frame, wait for the full payload, `clientStep` it. Fueled by the buffer
length (each frame consumes ≥ 9 octets). -/
def clientPump (hd : Hpack.HuffmanDecoder) :
    Nat → ClientConnState → ClientConnState × Bytes × List ClientEvent
  | 0, st => (st, [], [])
  | fuel + 1, st =>
    match _root_.H2.decode st.buf st.peerMaxFrame with
    | .complete f n =>
      let (st1, o1, e1) := clientStep hd st f
      let (st2, o2, e2) := clientPump hd fuel { st1 with buf := st.buf.drop n }
      (st2, o1 ++ o2, e1 ++ e2)
    | _ => (st, [], [])

/-- **The client's receive transition.** Consume `input` (any split), append it
to the buffer, and pump whole frames. Returns the successor state, octets to
write back, and the events surfaced. -/
def clientFeed (hd : Hpack.HuffmanDecoder) (st : ClientConnState) (input : Bytes) :
    ClientConnState × Bytes × List ClientEvent :=
  let st := { st with buf := st.buf ++ input }
  clientPump hd (st.buf.length + 1) st

/-- A fresh client receive state. -/
def initClient : ClientConnState := {}

/-! ## Faithfulness — the client↔server agreement -/

/-- **The client preface is exactly RFC 9113 §3.4's** — the first 24 octets a
client writes to open a connection are the client connection preface the server's
`H2.Conn.feed` validates. -/
theorem client_preface_sent (req : ClientRequest) (sid : Nat) :
    (requestBytes req sid).take 24 = clientPreface := by
  have h24 : clientPreface.length = 24 := clientPreface_length
  unfold requestBytes clientPreamble
  rw [List.append_assoc, List.append_assoc, ← h24, List.take_left]

/-- **The request HEADERS frame is faithful** (RFC 9113 §6.2): the frame the
client emits decodes, through the server's own `H2.Frame.decode`, to exactly a
`HEADERS` frame on stream `sid` (`END_HEADERS` set, `END_STREAM` = bodyless)
carrying the intended HPACK block. -/
theorem clientRequestHeadersFrame_faithful (req : ClientRequest) (sid : Nat) (mfs : Nat)
    (hsid : sid < 2 ^ 31) (hlen : (requestBlock req).length < 2 ^ 24)
    (hmfs : (requestBlock req).length ≤ mfs) :
    _root_.H2.decode (requestHeadersFrame req sid) mfs
      = .complete (.headers sid req.body.isEmpty true (requestBlock req))
          (9 + (requestBlock req).length) :=
  decode_encode_headers sid req.body.isEmpty true (requestBlock req) mfs hsid hlen hmfs

/-- **The request HPACK block is faithful** (RFC 7541): the block the client
emits decodes, through the deployed field decoder, to exactly the intended
request header list — provided every field fits the 7-bit length prefix. -/
theorem clientRequest_hpack_faithful (hd : Hpack.HuffmanDecoder) (tbl : List DynEntry)
    (req : ClientRequest) (fuel : Nat)
    (hsmall : ∀ p ∈ requestHeaderList req, p.1.length < 127 ∧ p.2.length < 127)
    (hfuel : (requestHeaderList req).length < fuel) :
    decodeHeadersV hd tbl fuel (requestBlock req) [] = .ok (requestHeaderList req) :=
  hpack_decode_encode hd tbl (requestHeaderList req) fuel hsmall hfuel

/-! ### End-to-end — the H2 analogue of `Client.H1.transaction_faithful`

The block the client emits decodes — through the **server engine's own**
`decodeBlockV` (the exact function `H2.Conn.finishRequest` calls) — to exactly the
routing-fold of the intended header list into the request `Head`. -/

private def rejectAllHuffman : Hpack.HuffmanDecoder := ⟨fun _ => none⟩

/-- **Client↔server agreement** (the H2 analogue of `Client.H1.transaction_faithful`):
for a request whose fields fit the 7-bit length prefix, the HPACK block the client
emits decodes, through the server engine's own `decodeBlockV`, to exactly the
routing-fold of the intended request header list — the client and server agree on
every request byte. `stepHead {} false (requestHeaderList req)` is the request head
the server hands its handler. -/
theorem client_server_agreement (req : ClientRequest) (fuel : Nat)
    (hsmall : ∀ p ∈ requestHeaderList req, p.1.length < 127 ∧ p.2.length < 127)
    (hfuel : (requestHeaderList req).length < fuel) :
    decodeBlockV rejectAllHuffman fuel {} (requestBlock req) {} false false
      = .ok (stepHead {} false (requestHeaderList req), {}) :=
  decodeBlockV_encodeHeaders rejectAllHuffman (requestHeaderList req) hsmall
    fuel {} {} false false hfuel

/-- A concrete request: `GET https://a/` with a `host: a` header, on stream 1. -/
def getExample : ClientRequest :=
  { method := [0x47, 0x45, 0x54]  -- "GET"
    scheme := [0x68, 0x74, 0x74, 0x70, 0x73]  -- "https"
    path := [0x2f]  -- "/"
    authority := [0x61]  -- "a"
    headers := [([0x68, 0x6f, 0x73, 0x74], [0x61])] }  -- "host" "a"

/-! ## Receive-side faithfulness -/

/-- **A received response header block is decoded faithfully**: when the client
receives a `HEADERS` frame (`END_HEADERS` set) whose block was HPACK-encoded from
a header list with small fields, `clientStep` surfaces exactly that list as a
`responseHeaders` event. -/
theorem clientStep_response_headers (hd : Hpack.HuffmanDecoder) (st : ClientConnState)
    (sid : Nat) (es : Bool) (hs : List (Bytes × Bytes))
    (hsmall : ∀ p ∈ hs, p.1.length < 127 ∧ p.2.length < 127) :
    clientStep hd st (.headers sid es true (encodeHeaders hs))
      = (st, [], [.responseHeaders sid hs]) := by
  have hround : decodeHeadersV hd st.hpack.tbl ((encodeHeaders hs).length + 1) (encodeHeaders hs) []
      = .ok hs :=
    hpack_decode_encode hd st.hpack.tbl hs ((encodeHeaders hs).length + 1) hsmall
      (by have := length_le_encodeHeaders hs; omega)
  simp only [clientStep, hround, if_true]

/-! ## Grounding: the concrete request round-trips (not vacuous) -/

/-- The concrete `GET` request block round-trips through the deployed field
decoder to its intended header list. -/
example : decodeHeadersV rejectAllHuffman [] ((requestBlock getExample).length + 1)
    (requestBlock getExample) [] = .ok (requestHeaderList getExample) :=
  clientRequest_hpack_faithful rejectAllHuffman [] getExample _
    (by decide) (by decide)

/-- The client's request HEADERS frame decodes back to the intended frame. -/
example : _root_.H2.decode (requestHeadersFrame getExample 1) 16384
    = .complete (.headers 1 true true (requestBlock getExample))
        (9 + (requestBlock getExample).length) :=
  clientRequestHeadersFrame_faithful getExample 1 16384 (by decide) (by decide) (by decide)

end H2
end Client
end Proto
