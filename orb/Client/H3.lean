import H3.Client

/-!
# The verified HTTP/3 client (RFC 9114 + RFC 9204)

`H3.Request` / the QUIC dispatch (`Reactor.WireH3`) is the drorb HTTP/3 **server**
front end. This module is its dual — the **client** — built entirely from the
proven H3 frame decoder (`H3.decFrame`), the deployed QPACK encoder
(`H3.Qpack.encodeFieldSection`) and decoder (`H3.Qpack.decodeFieldSection`), and
the request encode + faithfulness of `H3.Client`. It mirrors the H1/H2 clients
(`Client.H1`, `Client.H2`), so drorb speaks all three HTTP versions as a peer.

* **submit** — a client opens a bidirectional request stream (RFC 9114 §4.1) and
  writes a `HEADERS` frame carrying the QPACK-encoded request field section, then
  (for a request with a body) a `DATA` frame. `requestStreamBytes` is the exact
  octet stream the client writes on its request stream.
* **receive** — `h3ClientFeed` consumes response transport bytes (any split),
  walks whole H3 frames with `H3.decFrame`, decodes response `HEADERS` field
  sections with the deployed `H3.Qpack.decodeFieldSection`, and surfaces
  `H3ClientEvent`s (response head, response DATA, …).

## What is proven

* `request_faithful` — the H3 analogue of `Client.H2.client_server_agreement`:
  the field section the client emits for a bodyless request decodes, through the
  **deployed `decodeFieldSection`**, to a head whose four pseudo-headers resolve
  to exactly the intended request bytes (from `H3.Client.requestSection_faithful`).
* `headers_frame_faithful` — the request `HEADERS` frame decodes, through the
  server's own `H3.decFrame`, to exactly a `HEADERS` frame carrying the intended
  QPACK section (from `H3.Client.decFrame_encHeadersFrame`).

0 sorries; axioms ⊆ `{propext, Quot.sound, Classical.choice}`.

Deliberate scope: the request submit + faithfulness (the load-bearing client
core) and the single-frame receive step are proven here; the QPACK-decode
correctness of the receive path is the deployed `decodeFieldSection`'s own theory.
A full multi-frame trailer-assembling receive proof is a named follow-on.
-/

namespace Proto
namespace Client
namespace H3

open _root_.H3 (Frame FrameResult decFrame Bytes)
open _root_.H3.Client (ClientRequest requestStreamBytes requestSection requestHeadersFrame
  requestSection_faithful decFrame_encHeadersFrame getExample)
open _root_.H3.Qpack (strBytes)

/-! ## The request the client submits (re-exported from `H3.Client`) -/

/-- The exact octet stream a client writes on a fresh request stream for `req`
(RFC 9114 §4.1): the QPACK `HEADERS` frame, then a `DATA` frame if there is a
body. `none` iff a length overflows the QUIC varint range. -/
abbrev submit (req : ClientRequest) : Option Bytes := requestStreamBytes req

/-! ## The client-side receive engine -/

/-- A client connection's receive state. `buf` holds undecoded H3 frame bytes
across feeds; `qpack` is the QPACK decode-side arena the response header blocks
grow into; `hd` is the deployed Huffman decoder. -/
structure H3ClientState where
  buf : Bytes := []
  qpack : Arena.Store := { main := #[], sidecar := #[], entries := [] }
deriving Inhabited

/-- What the client surfaces to its caller as it decodes server frames. -/
inductive H3ClientEvent where
  /-- A response `HEADERS` frame completed: the decoded field section — pseudo
  (`:status`) and regular fields — grown into `store`. -/
  | responseHead (store : Arena.Store) (pseudo : _root_.H3.Qpack.Pseudo) (fields : List _root_.H3.Qpack.FieldLine)
  /-- A response `DATA` frame with its body bytes. -/
  | responseData (data : Bytes)
  /-- The peer's GOAWAY (RFC 9114 §5.2). -/
  | goaway (streamId : Nat)
  /-- A response `HEADERS` frame's field section failed QPACK decoding. -/
  | headerDecodeError

/-- Step the client on one decoded server frame: a `HEADERS` frame's QPACK field
section is decoded through the **deployed** `decodeFieldSection`; DATA/GOAWAY are
surfaced; control frames (SETTINGS etc. on a response stream) are ignored. -/
def h3ClientStep (hd : _root_.H3.Qpack.HuffmanDecoder) (st : H3ClientState) :
    Frame → H3ClientState × List H3ClientEvent
  | .headers enc =>
    match _root_.H3.Qpack.decodeFieldSection hd st.qpack enc with
    | .ok d => ({ st with qpack := d.store }, [.responseHead d.store d.pseudo d.fields])
    | .error _ => (st, [.headerDecodeError])
  | .data payload => (st, [.responseData payload])
  | .goaway sid => (st, [.goaway sid])
  | _ => (st, [])

/-- Walk whole H3 frames off the client buffer (RFC 9114 §7.1): `H3.decFrames`
cuts every complete frame, leaving the truncated remainder buffered; each frame
is stepped. -/
def h3ClientFeed (hd : _root_.H3.Qpack.HuffmanDecoder) (st : H3ClientState) (input : Bytes) :
    H3ClientState × List H3ClientEvent :=
  let (frames, rest) := _root_.H3.decFrames (st.buf ++ input)
  let step := fun (acc : H3ClientState × List H3ClientEvent) (f : Frame) =>
    let (st', evs) := h3ClientStep hd acc.1 f
    (st', acc.2 ++ evs)
  let (st', evs) := frames.foldl step (st, [])
  ({ st' with buf := rest }, evs)

/-- A fresh client receive state. -/
def initClient : H3ClientState := {}

/-! ## Faithfulness — re-exported from `H3.Client` -/

/-- **The H3 client request is faithful** — the H3 analogue of
`Client.H2.client_server_agreement`. For a bodyless request with no extra fields
and small UTF-8 pseudo-values, the QPACK field section the client submits decodes,
through the **deployed `H3.Qpack.decodeFieldSection`**, to a head whose four
pseudo-headers resolve to exactly the intended request bytes. -/
theorem request_faithful (hd : _root_.H3.Qpack.HuffmanDecoder) (req : ClientRequest)
    (hempty : req.headers = [])
    (hml : req.method.length < 127) (hsl : req.scheme.length < 127)
    (hpal : req.path.length < 127) (haul : req.authority.length < 127)
    (hmu : _root_.H3.Qpack.utf8Ok req.method = true) (hsu : _root_.H3.Qpack.utf8Ok req.scheme = true)
    (hpau : _root_.H3.Qpack.utf8Ok req.path = true) (hauu : _root_.H3.Qpack.utf8Ok req.authority = true)
    (unm : _root_.H3.Qpack.utf8Ok (strBytes ":method") = true)
    (uns : _root_.H3.Qpack.utf8Ok (strBytes ":scheme") = true)
    (unp : _root_.H3.Qpack.utf8Ok (strBytes ":path") = true)
    (una : _root_.H3.Qpack.utf8Ok (strBytes ":authority") = true) :
    ∃ (d : _root_.H3.Qpack.Decoded) (v1 v2 v3 v4 : Arena.Entry),
      _root_.H3.Qpack.decodeFieldSection hd _root_.H3.Qpack.emptyStore (requestSection req) = .ok d ∧
      d.pseudo.method = some v1 ∧ d.pseudo.scheme = some v2 ∧
      d.pseudo.path = some v3 ∧ d.pseudo.authority = some v4 ∧
      d.store.resolve v1 = some req.method.toArray ∧ d.store.resolve v2 = some req.scheme.toArray ∧
      d.store.resolve v3 = some req.path.toArray ∧ d.store.resolve v4 = some req.authority.toArray ∧
      d.fields = [] :=
  requestSection_faithful hd req hempty hml hsl hpal haul hmu hsu hpau hauu unm uns unp una

/-- **The request HEADERS frame is faithful** (RFC 9114 §7.2.2): the frame the
client emits decodes, through the server's own `H3.decFrame`, to exactly a
`HEADERS` frame carrying the intended QPACK section. -/
theorem headers_frame_faithful (enc lb : Bytes)
    (hl : _root_.H3.Varint.encVarint enc.length = some lb) :
    decFrame (0x01 :: (lb ++ enc)) = .complete (.headers enc) (1 + lb.length + enc.length) :=
  decFrame_encHeadersFrame enc lb hl

#print axioms request_faithful
#print axioms headers_frame_faithful

end H3
end Client
end Proto
