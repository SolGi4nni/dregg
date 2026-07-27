import Client.H2
import H2.FlowWindow
import H2.RespTrailers

/-!
# The HTTP/2 client **response receive** loop (RFC 9113 §4.3, §6.2, §6.1)

`Client/H2.lean` proves the request-submit side of the drorb HTTP/2 client and a
single-frame receive step (`clientStep`). This module completes the **receive**
side: a full multi-frame response-assembly loop that mirrors the drorb HTTP/2
**server** engine's header-block discipline (`H2.Conn.handleFrame` /
`H2.Conn.pump`, which this module does **not** modify):

* **CONTINUATION assembly** (RFC 9113 §4.3, §6.10): a `HEADERS` frame that does
  *not* set `END_HEADERS` opens a header block; only `CONTINUATION` frames on the
  same stream may follow, and their payloads accumulate onto the open fragment
  until an `END_HEADERS` closes it. The reassembled fragment is HPACK-decoded as
  a *single* block — exactly the server's `ContSt` rule, on the client side.
* **DATA reassembly** (RFC 9113 §6.1): response `DATA` frames surface their body
  octets in order; `END_STREAM` closes the response.

The loop walks whole frames off the buffer with the deployed `H2.Frame.decode`,
so it composes against the drorb HTTP/2 **server**'s own frame + HPACK encoders
(`H2.FrameEncode`, `H2.HpackEncode`) for an end-to-end client↔server receive
agreement.

## What is proven (0 sorries; axioms ⊆ `{propext, Quot.sound, Classical.choice}`)

* `h2_continuation_assembles` (RFC 9113 §4.3) — a response header block **split
  across a `HEADERS` + a `CONTINUATION` frame** decodes to exactly the same
  fields as the same block delivered in a single `END_HEADERS` `HEADERS` frame:
  the client reassembles the split block losslessly.
* `h2_client_receive_faithful` — end-to-end: for a response the drorb **server**
  serializes as `HEADERS(+CONTINUATION)` + `DATA(body, END_STREAM)` (the header
  block HPACK-encoded, and *split across the CONTINUATION boundary*), the client
  receive loop reassembles **exactly** the response the server sent — the header
  field list `hs` (`:status` + fields) and the body `body` — surfacing
  `[responseHeaders sid hs, responseData sid body true]`. Composes the server's
  `H2.FrameEncode`/`H2.HpackEncode` encode with the client's decode.

Grounded (non-vacuous) on a concrete `200` response (a `:status: 200` head plus a
`content-type` field and a body), reassembled into a `ClientResponse`.

## Follow-ons now closed (additive; the theorems above are unchanged)

The two named follow-ons are closed **alongside** the loop above, without
touching `stepFrame` / `pump` / `feed` / `h2_client_receive_faithful`:

* **Client-emitted flow-control `WINDOW_UPDATE`** (RFC 9113 §6.9): as the client
  consumes `N` octets of a received `DATA` frame it emits a `WINDOW_UPDATE(N)` at
  both the connection and the stream level to replenish the peer's send window
  (`windowUpdatesFor` / `windowUpdateFrame`). `client_sends_window_update` proves
  the emitted frame carries the increment `N` on the wire (`wuIncrement (be32 N) =
  N`) and — **composing `H2.FlowWindow.window_update_credits` and
  `H2.FlowWindow.Flow.strUpdate_WF`** — that crediting the peer's send `Flow` by
  it raises the window by exactly `N` and keeps it well-formed (never negative).
* **Trailer-section receive** (RFC 9113 §8.1): after the body `DATA` frames, a
  second `HEADERS` frame with `END_STREAM` carrying `grpc-status` / `grpc-message`
  is reassembled and surfaced into `ClientResponse.trailers`
  (`reassembleT` / `collectTrailers`). `h2_client_receive_trailers` proves a
  server wire `HEADERS + DATA + trailer-HEADERS(END_STREAM)` reassembles to the
  response **with the trailer block HPACK-decoded into `trailers`**, and —
  **composing `H2.RespTrailers.trailers_no_pseudo`** — that a `noPseudo` trailer
  section carries no pseudo-header field (RFC 9113 §8.1).
-/

namespace Proto
namespace Client
namespace H2Receive

open _root_.H2 _root_.H2.Conn _root_.H2.FrameEncode _root_.H2.HpackEncode

abbrev Bytes := List UInt8

/-! ## The receive state (mirrors the server's `H2.Conn.ConnState` header gate) -/

/-- An in-progress response header block (RFC 9113 §4.3): a `HEADERS` frame
arrived without `END_HEADERS`; only `CONTINUATION` frames on `sid` may follow,
accumulating onto `frag`. Mirrors the server's `H2.Conn.ContSt`. -/
structure OpenBlock where
  sid : Nat
  endStream : Bool
  frag : Bytes
deriving Repr

/-- A client response-receive state. `buf` holds undecoded frame bytes across
feeds; `cont` is the open header block (if any); `hpack` is the decode-side
dynamic table; `peerMaxFrame` mirrors the server's `SETTINGS_MAX_FRAME_SIZE`. -/
structure RState where
  buf : Bytes := []
  cont : Option OpenBlock := none
  hpack : List DynEntry := []
  peerMaxFrame : Nat := 16384
deriving Repr

/-- What the client surfaces to its caller as it reassembles the response. -/
inductive REvent where
  /-- A response header block completed on `sid`, HPACK-decoded to these fields
  (`:status` included as an ordinary field). -/
  | responseHeaders (sid : Nat) (headers : List (Bytes × Bytes))
  /-- A response `DATA` frame on `sid`; `endStream` closes the response. -/
  | responseData (sid : Nat) (data : Bytes) (endStream : Bool)
  /-- A completed header block failed HPACK decoding. -/
  | headerDecodeError (sid : Nat)
  /-- The RFC 9113 §4.3 header-block gate was violated (a non-CONTINUATION frame,
  or a CONTINUATION on the wrong stream, arrived while a block was open). -/
  | protocolError
deriving Repr, DecidableEq

/-- Finish a completed header block on `sid`: HPACK-decode the reassembled
fragment through the deployed field decoder and surface the response headers (or
a decode error). Clears the open block. -/
def finishHeaders (hd : Hpack.HuffmanDecoder) (st : RState) (sid : Nat) (frag : Bytes) :
    RState × List REvent :=
  match decodeHeadersV hd st.hpack (frag.length + 1) frag [] with
  | .ok hs => ({ st with cont := none }, [.responseHeaders sid hs])
  | .error _ => ({ st with cont := none }, [.headerDecodeError sid])

/-- Step the client on one decoded server frame (RFC 9113 §4.3 header-block gate
first, exactly as the server's `H2.Conn.handleFrame`): while a header block is
open, only a `CONTINUATION` on the same stream is legal and its payload
accumulates; otherwise a `HEADERS` opens/completes a block and `DATA` surfaces
body octets. -/
def stepFrame (hd : Hpack.HuffmanDecoder) (st : RState) (fr : Frame) :
    RState × List REvent :=
  match st.cont with
  | some c =>
    match fr with
    | .continuation sid eh payload =>
      if sid = c.sid then
        let frag := c.frag ++ payload
        if eh then finishHeaders hd st c.sid frag
        else ({ st with cont := some { c with frag := frag } }, [])
      else (st, [.protocolError])
    | _ => (st, [.protocolError])
  | none =>
    match fr with
    | .headers sid es eh block =>
      if eh then finishHeaders hd st sid block
      else ({ st with cont := some ⟨sid, es, block⟩ }, [])
    | .data sid es payload => (st, [.responseData sid payload es])
    | _ => (st, [])

/-- Walk whole frames off the client buffer (RFC 9113 §4.1): decode + size-check
each frame, wait for the full payload, `stepFrame` it. Fueled by the buffer
length (each frame consumes ≥ 9 octets). -/
def pump (hd : Hpack.HuffmanDecoder) : Nat → RState → RState × List REvent
  | 0, st => (st, [])
  | fuel + 1, st =>
    match _root_.H2.decode st.buf st.peerMaxFrame with
    | .complete f n =>
      let (st1, e1) := stepFrame hd st f
      let (st2, e2) := pump hd fuel { st1 with buf := st.buf.drop n }
      (st2, e1 ++ e2)
    | _ => (st, [])

/-- **The client's receive transition.** Consume `input` (any split), append it
to the buffer, and pump whole frames, reassembling the response. -/
def feed (hd : Hpack.HuffmanDecoder) (st : RState) (input : Bytes) :
    RState × List REvent :=
  let st := { st with buf := st.buf ++ input }
  pump hd (st.buf.length + 1) st

/-- A fresh client receive state. -/
def initR : RState := {}

/-! ## Reassembling a complete response -/

/-- A complete HTTP/2 response, as the client reassembles it: the `:status`
value bytes, the remaining header fields, and the concatenated body. -/
structure ClientResponse where
  status : Bytes
  headers : List (Bytes × Bytes)
  body : Bytes
  /-- The trailer section (RFC 9113 §8.1), if the response carried a post-DATA
  `END_STREAM` `HEADERS` block (e.g. gRPC `grpc-status`/`grpc-message`); empty
  when there is no trailer section. Populated by `reassembleT`. -/
  trailers : List (Bytes × Bytes) := []
deriving Repr, DecidableEq

/-- The `:status` pseudo-header name, as explicit octets. -/
def pStatus : Bytes := [0x3a, 0x73, 0x74, 0x61, 0x74, 0x75, 0x73]

/-- Concatenate the body octets from all `responseData` events, in order. -/
def collectBody : List REvent → Bytes
  | [] => []
  | .responseData _ d _ :: rest => d ++ collectBody rest
  | _ :: rest => collectBody rest

/-- The first completed response header block. -/
def firstHeaders : List REvent → Option (Nat × List (Bytes × Bytes))
  | [] => none
  | .responseHeaders sid hs :: _ => some (sid, hs)
  | _ :: rest => firstHeaders rest

/-- Split the `:status` value out of a response header list. -/
def splitStatus (hs : List (Bytes × Bytes)) : Bytes × List (Bytes × Bytes) :=
  match hs.find? (fun p => p.1 == pStatus) with
  | some p => (p.2, hs.filter (fun q => q.1 != pStatus))
  | none => ([], hs)

/-- Reassemble the surfaced events into a `ClientResponse` (status + fields +
body). `none` iff no response header block was surfaced. -/
def reassemble (evs : List REvent) : Option ClientResponse :=
  match firstHeaders evs with
  | none => none
  | some (_, hs) =>
    let (status, rest) := splitStatus hs
    some { status := status, headers := rest, body := collectBody evs }

/-! ## Frame-decode plumbing lemmas -/

/-- `parseHeader` reads only the first 9 octets, so it is unchanged by any suffix
appended after a buffer it already parses. -/
theorem parseHeader_prefix (bs rest : Bytes) (hdr : FrameHeader)
    (h : parseHeader bs = some hdr) : parseHeader (bs ++ rest) = some hdr := by
  rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ |
    ⟨b6, _ | ⟨b7, _ | ⟨b8, tl⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp_all [parseHeader, List.cons_append]

/-- **A completed frame decode is stable under a buffer suffix**: a frame the
decoder completes on `bs` it completes identically on `bs ++ rest` — the extra
bytes are the next frame, untouched. The engine of the walk over concatenated
frames. -/
theorem decode_prefix (bs rest : Bytes) (mfs : Nat) (f : Frame) (n : Nat)
    (h : _root_.H2.decode bs mfs = .complete f n) :
    _root_.H2.decode (bs ++ rest) mfs = .complete f n := by
  obtain ⟨hdr, hp, hle, hn, hlen⟩ := decode_complete_inv bs mfs f n h
  have hpay : ((bs ++ rest).drop 9).take hdr.length = (bs.drop 9).take hdr.length := by
    rw [List.drop_append_of_le_length (by omega : 9 ≤ bs.length),
        List.take_append_of_le_length (by rw [List.length_drop]; omega)]
  have key : _root_.H2.decode (bs ++ rest) mfs = _root_.H2.decode bs mfs := by
    unfold _root_.H2.decode
    rw [parseHeader_prefix bs rest hdr hp, hp]
    simp only [if_neg (show ¬ mfs < hdr.length by omega),
      if_neg (show ¬ (bs ++ rest).length < 9 + hdr.length by rw [List.length_append]; omega),
      if_neg (show ¬ bs.length < 9 + hdr.length by omega), hpay]
  rw [key, h]

/-- `HEADERS`/`CONTINUATION`/`DATA` encode to header + payload, so their wire
length is `9 + payload.length`. -/
theorem encodeFrame_headers_length (sid : Nat) (es eh : Bool) (p : Bytes) :
    (encodeFrame (.headers sid es eh p)).length = 9 + p.length := by
  simp only [encodeFrame]
  rw [List.length_append, FrameEncode.frameHdr_length]

theorem encodeFrame_continuation_length (sid : Nat) (eh : Bool) (p : Bytes) :
    (encodeFrame (.continuation sid eh p)).length = 9 + p.length := by
  simp only [encodeFrame]
  rw [List.length_append, FrameEncode.frameHdr_length]

theorem encodeFrame_data_length (sid : Nat) (es : Bool) (p : Bytes) :
    (encodeFrame (.data sid es p)).length = 9 + p.length := by
  simp only [encodeFrame]
  rw [List.length_append, FrameEncode.frameHdr_length]

/-- One `pump` step over a buffer whose head decodes to a complete frame. -/
theorem pump_succ_complete (hd : Hpack.HuffmanDecoder) (fuel : Nat) (st : RState)
    (f : Frame) (n : Nat) (hdec : _root_.H2.decode st.buf st.peerMaxFrame = .complete f n) :
    pump hd (fuel + 1) st =
      (let (st1, e1) := stepFrame hd st f
       let (st2, e2) := pump hd fuel { st1 with buf := st.buf.drop n }
       (st2, e1 ++ e2)) := by
  simp only [pump]
  rw [hdec]

/-- The event-list of one `pump` step over a completed frame: this frame's
events, then the rest of the walk. -/
theorem pump_succ_complete_snd (hd : Hpack.HuffmanDecoder) (fuel : Nat) (st : RState)
    (f : Frame) (n : Nat) (hdec : _root_.H2.decode st.buf st.peerMaxFrame = .complete f n) :
    (pump hd (fuel + 1) st).2 =
      (stepFrame hd st f).2 ++
        (pump hd fuel { (stepFrame hd st f).1 with buf := st.buf.drop n }).2 := by
  rw [pump_succ_complete hd fuel st f n hdec]

/-- `pump` on an empty buffer surfaces nothing (any fuel). -/
theorem pump_buf_nil (hd : Hpack.HuffmanDecoder) (fuel : Nat) (st : RState)
    (h : st.buf = []) : pump hd fuel st = (st, []) := by
  cases fuel with
  | zero => rfl
  | succ f =>
    simp only [pump]
    rw [h, show _root_.H2.decode ([] : Bytes) st.peerMaxFrame = .incomplete from rfl]

/-- Finishing a completed block whose fragment is `encodeHeaders hs` (small
fields, empty decode table) surfaces exactly `hs`. -/
theorem finishHeaders_encodeHeaders (hd : Hpack.HuffmanDecoder) (st : RState) (sid : Nat)
    (hs : List (Bytes × Bytes)) (hhpack : st.hpack = [])
    (hsmall : ∀ p ∈ hs, p.1.length < 127 ∧ p.2.length < 127) :
    finishHeaders hd st sid (encodeHeaders hs)
      = ({ st with cont := none }, [.responseHeaders sid hs]) := by
  unfold finishHeaders
  rw [hhpack, hpack_decode_encode hd [] hs ((encodeHeaders hs).length + 1) hsmall
    (by have := length_le_encodeHeaders hs; omega)]

/-! ## The server's response wire image (loopback) -/

/-- The exact octets a drorb HTTP/2 **server** serializes for a response on
stream `sid`: the response header block `encodeHeaders hs` **split across the
CONTINUATION boundary** at `n1` — a `HEADERS` frame (`END_HEADERS` clear) with
the first `n1` octets, a `CONTINUATION` frame (`END_HEADERS` set) with the rest —
then a `DATA` frame carrying `body` with `END_STREAM` set. At `n1 ≥ block.length`
the split degenerates to the whole block in one `HEADERS` + an empty
`CONTINUATION`; the theorem holds for every split point. -/
def serverWire (sid : Nat) (hs : List (Bytes × Bytes)) (body : Bytes) (n1 : Nat) : Bytes :=
  encodeFrame (.headers sid false false ((encodeHeaders hs).take n1))
    ++ (encodeFrame (.continuation sid true ((encodeHeaders hs).drop n1))
        ++ encodeFrame (.data sid true body))

/-! ## Per-frame step reductions -/

/-- `feed` from the fresh state is a pump over the input as the whole buffer. -/
theorem feed_initR (hd : Hpack.HuffmanDecoder) (input : Bytes) :
    feed hd initR input = pump hd (input.length + 1) ({ buf := input } : RState) := rfl

/-- A `HEADERS` frame without `END_HEADERS` (no block open) opens a block. -/
theorem stepFrame_headers_open (hd : Hpack.HuffmanDecoder) (st : RState) (sid : Nat)
    (es : Bool) (block : Bytes) (hcont : st.cont = none) :
    stepFrame hd st (Frame.headers sid es false block)
      = ({ st with cont := some ⟨sid, es, block⟩ }, []) := by
  simp only [stepFrame, hcont]; rfl

/-- A `DATA` frame (no block open) surfaces its body octets. -/
theorem stepFrame_data (hd : Hpack.HuffmanDecoder) (st : RState) (sid : Nat)
    (es : Bool) (payload : Bytes) (hcont : st.cont = none) :
    stepFrame hd st (Frame.data sid es payload)
      = (st, [.responseData sid payload es]) := by
  simp [stepFrame, hcont]

/-- A `CONTINUATION` frame with `END_HEADERS`, on the stream of the open block,
completes the block by finishing the accumulated fragment ++ this payload. -/
theorem stepFrame_continuation_end (hd : Hpack.HuffmanDecoder) (st : RState)
    (sid : Nat) (es : Bool) (b1 payload : Bytes) (hcont : st.cont = some ⟨sid, es, b1⟩) :
    stepFrame hd st (Frame.continuation sid true payload)
      = finishHeaders hd st sid (b1 ++ payload) := by
  simp [stepFrame, hcont]

/-- The event-list contribution of one completed frame, given its step outcome
and the events of the rest of the walk. -/
theorem pump_step_snd (hd : Hpack.HuffmanDecoder) (fuel : Nat) (st : RState) (f : Frame)
    (n : Nat) (e : List REvent) {st' : RState} {tail : List REvent}
    (hdec : _root_.H2.decode st.buf st.peerMaxFrame = .complete f n)
    (hstep : stepFrame hd st f = (st', e))
    (hrec : (pump hd fuel { st' with buf := st.buf.drop n }).2 = tail) :
    (pump hd (fuel + 1) st).2 = e ++ tail := by
  rw [pump_succ_complete hd fuel st f n hdec, hstep]
  show e ++ (pump hd fuel { st' with buf := st.buf.drop n }).2 = e ++ tail
  rw [hrec]

/-- **The receive run over a split HEADERS+CONTINUATION+DATA response.** Walking
`serverWire` off the buffer reassembles the split header block and the body,
surfacing exactly `[responseHeaders sid hs, responseData sid body true]`. -/
theorem pump_receive (hd : Hpack.HuffmanDecoder) (sid n1 : Nat)
    (hs : List (Bytes × Bytes)) (body : Bytes) (fuel : Nat) (hf : 3 ≤ fuel)
    (hsid : sid < 2 ^ 31)
    (hblk : (encodeHeaders hs).length ≤ 16384) (hbody : body.length ≤ 16384)
    (hsmall : ∀ p ∈ hs, p.1.length < 127 ∧ p.2.length < 127) :
    (pump hd fuel ({ buf := serverWire sid hs body n1 } : RState)).2
      = [.responseHeaders sid hs, .responseData sid body true] := by
  have h24 : (16384 : Nat) < 2 ^ 24 := by decide
  have hbt : ((encodeHeaders hs).take n1).length ≤ 16384 := by rw [List.length_take]; omega
  have hbd : ((encodeHeaders hs).drop n1).length ≤ 16384 := by rw [List.length_drop]; omega
  have hHlen : (encodeFrame (Frame.headers sid false false ((encodeHeaders hs).take n1))).length
      = 9 + ((encodeHeaders hs).take n1).length := encodeFrame_headers_length _ _ _ _
  have hClen : (encodeFrame (Frame.continuation sid true ((encodeHeaders hs).drop n1))).length
      = 9 + ((encodeHeaders hs).drop n1).length := encodeFrame_continuation_length _ _ _
  have hDlen : (encodeFrame (Frame.data sid true body)).length = 9 + body.length :=
    encodeFrame_data_length _ _ _
  -- Per-frame decodes.
  have hdecH : _root_.H2.decode (serverWire sid hs body n1) 16384
      = .complete (.headers sid false false ((encodeHeaders hs).take n1))
          (9 + ((encodeHeaders hs).take n1).length) := by
    unfold serverWire
    exact decode_prefix _ _ 16384 _ _
      (decode_encode_headers sid false false _ 16384 hsid (by omega) hbt)
  have hdecC : _root_.H2.decode
        (encodeFrame (Frame.continuation sid true ((encodeHeaders hs).drop n1))
          ++ encodeFrame (Frame.data sid true body)) 16384
      = .complete (.continuation sid true ((encodeHeaders hs).drop n1))
          (9 + ((encodeHeaders hs).drop n1).length) :=
    decode_prefix _ _ 16384 _ _
      (decode_encode_continuation sid true _ 16384 hsid (by omega) hbd)
  have hdecD : _root_.H2.decode (encodeFrame (Frame.data sid true body)) 16384
      = .complete (.data sid true body) (9 + body.length) :=
    decode_encode_data sid true body 16384 hsid (by omega) hbody
  -- Buffer remainders after each frame.
  have hdropH : (serverWire sid hs body n1).drop (9 + ((encodeHeaders hs).take n1).length)
      = encodeFrame (Frame.continuation sid true ((encodeHeaders hs).drop n1))
          ++ encodeFrame (Frame.data sid true body) := by
    unfold serverWire; rw [← hHlen]; exact List.drop_left
  have hdropC : (encodeFrame (Frame.continuation sid true ((encodeHeaders hs).drop n1))
        ++ encodeFrame (Frame.data sid true body)).drop (9 + ((encodeHeaders hs).drop n1).length)
      = encodeFrame (Frame.data sid true body) := by
    rw [← hClen]; exact List.drop_left
  have hdropD : (encodeFrame (Frame.data sid true body)).drop (9 + body.length) = [] := by
    rw [← hDlen]; exact List.drop_length
  have hjoin : (encodeHeaders hs).take n1 ++ (encodeHeaders hs).drop n1 = encodeHeaders hs :=
    List.take_append_drop n1 _
  -- Peel three complete frames, then the empty buffer.
  rcases fuel with _ | _ | _ | f
  · omega
  · omega
  · omega
  -- Frame 1: HEADERS (END_HEADERS clear) opens the block.
  refine pump_step_snd hd (f + 2) _ (Frame.headers sid false false ((encodeHeaders hs).take n1))
    (9 + ((encodeHeaders hs).take n1).length) [] hdecH
    (stepFrame_headers_open hd _ sid false _ rfl) ?_
  -- Frame 2: CONTINUATION (END_HEADERS set) completes the block to `hs`.
  refine pump_step_snd hd (f + 1) _ (Frame.continuation sid true ((encodeHeaders hs).drop n1))
    (9 + ((encodeHeaders hs).drop n1).length) [.responseHeaders sid hs]
    (by
      show _root_.H2.decode ((serverWire sid hs body n1).drop
        (9 + ((encodeHeaders hs).take n1).length)) 16384 = _
      rw [hdropH]; exact hdecC)
    (by rw [stepFrame_continuation_end hd _ sid false _ _ rfl, hjoin,
      finishHeaders_encodeHeaders hd _ sid hs rfl hsmall]) ?_
  -- Frame 3: DATA carries the body, END_STREAM closes.
  refine pump_step_snd hd f _ (Frame.data sid true body) (9 + body.length)
    [.responseData sid body true]
    (by
      show _root_.H2.decode (((serverWire sid hs body n1).drop
        (9 + ((encodeHeaders hs).take n1).length)).drop
        (9 + ((encodeHeaders hs).drop n1).length)) 16384 = _
      rw [hdropH, hdropC]; exact hdecD)
    (stepFrame_data hd _ sid true _ rfl) ?_
  -- Frame 4+: the buffer is empty.
  rw [pump_buf_nil hd f _ (by
    show (((serverWire sid hs body n1).drop (9 + ((encodeHeaders hs).take n1).length)).drop
        (9 + ((encodeHeaders hs).drop n1).length)).drop (9 + body.length) = []
    rw [hdropH, hdropC, hdropD])]

/-- A `HEADERS` frame with `END_HEADERS` (no block open) completes at once. -/
theorem stepFrame_headers_end (hd : Hpack.HuffmanDecoder) (st : RState) (sid : Nat)
    (es : Bool) (block : Bytes) (hcont : st.cont = none) :
    stepFrame hd st (Frame.headers sid es true block) = finishHeaders hd st sid block := by
  simp only [stepFrame, hcont]; rfl

/-- **The receive run over a split HEADERS+CONTINUATION (no body).** Surfaces
`[responseHeaders sid hs]`. -/
theorem pump_receive_split (hd : Hpack.HuffmanDecoder) (sid n1 : Nat)
    (hs : List (Bytes × Bytes)) (fuel : Nat) (hf : 2 ≤ fuel)
    (hsid : sid < 2 ^ 31) (hblk : (encodeHeaders hs).length ≤ 16384)
    (hsmall : ∀ p ∈ hs, p.1.length < 127 ∧ p.2.length < 127) :
    (pump hd fuel ({ buf := encodeFrame (.headers sid false false ((encodeHeaders hs).take n1))
        ++ encodeFrame (.continuation sid true ((encodeHeaders hs).drop n1)) } : RState)).2
      = [.responseHeaders sid hs] := by
  have h24 : (16384 : Nat) < 2 ^ 24 := by decide
  have hbt : ((encodeHeaders hs).take n1).length ≤ 16384 := by rw [List.length_take]; omega
  have hbd : ((encodeHeaders hs).drop n1).length ≤ 16384 := by rw [List.length_drop]; omega
  have hHlen : (encodeFrame (Frame.headers sid false false ((encodeHeaders hs).take n1))).length
      = 9 + ((encodeHeaders hs).take n1).length := encodeFrame_headers_length _ _ _ _
  have hClen : (encodeFrame (Frame.continuation sid true ((encodeHeaders hs).drop n1))).length
      = 9 + ((encodeHeaders hs).drop n1).length := encodeFrame_continuation_length _ _ _
  have hdecH : _root_.H2.decode (encodeFrame (Frame.headers sid false false ((encodeHeaders hs).take n1))
        ++ encodeFrame (Frame.continuation sid true ((encodeHeaders hs).drop n1))) 16384
      = .complete (.headers sid false false ((encodeHeaders hs).take n1))
          (9 + ((encodeHeaders hs).take n1).length) :=
    decode_prefix _ _ 16384 _ _
      (decode_encode_headers sid false false _ 16384 hsid (by omega) hbt)
  have hdecC : _root_.H2.decode (encodeFrame (Frame.continuation sid true ((encodeHeaders hs).drop n1))) 16384
      = .complete (.continuation sid true ((encodeHeaders hs).drop n1))
          (9 + ((encodeHeaders hs).drop n1).length) :=
    decode_encode_continuation sid true _ 16384 hsid (by omega) hbd
  have hdropH : (encodeFrame (Frame.headers sid false false ((encodeHeaders hs).take n1))
        ++ encodeFrame (Frame.continuation sid true ((encodeHeaders hs).drop n1))).drop
        (9 + ((encodeHeaders hs).take n1).length)
      = encodeFrame (Frame.continuation sid true ((encodeHeaders hs).drop n1)) := by
    rw [← hHlen]; exact List.drop_left
  have hdropC : (encodeFrame (Frame.continuation sid true ((encodeHeaders hs).drop n1))).drop
        (9 + ((encodeHeaders hs).drop n1).length) = [] := by
    rw [← hClen]; exact List.drop_length
  have hjoin : (encodeHeaders hs).take n1 ++ (encodeHeaders hs).drop n1 = encodeHeaders hs :=
    List.take_append_drop n1 _
  rcases fuel with _ | _ | f
  · omega
  · omega
  refine pump_step_snd hd (f + 1) _ (Frame.headers sid false false ((encodeHeaders hs).take n1))
    (9 + ((encodeHeaders hs).take n1).length) [] hdecH
    (stepFrame_headers_open hd _ sid false _ rfl) ?_
  refine pump_step_snd hd f _ (Frame.continuation sid true ((encodeHeaders hs).drop n1))
    (9 + ((encodeHeaders hs).drop n1).length) [.responseHeaders sid hs]
    (by
      show _root_.H2.decode ((encodeFrame (Frame.headers sid false false ((encodeHeaders hs).take n1))
          ++ encodeFrame (Frame.continuation sid true ((encodeHeaders hs).drop n1))).drop
          (9 + ((encodeHeaders hs).take n1).length)) 16384 = _
      rw [hdropH]; exact hdecC)
    (by rw [stepFrame_continuation_end hd _ sid false _ _ rfl, hjoin,
      finishHeaders_encodeHeaders hd _ sid hs rfl hsmall]) ?_
  · rw [pump_buf_nil hd f _ (by
      show ((encodeFrame (Frame.headers sid false false ((encodeHeaders hs).take n1))
          ++ encodeFrame (Frame.continuation sid true ((encodeHeaders hs).drop n1))).drop
          (9 + ((encodeHeaders hs).take n1).length)).drop
          (9 + ((encodeHeaders hs).drop n1).length) = []
      rw [hdropH, hdropC])]

/-- **The receive run over a single END_HEADERS HEADERS frame (no body).**
Surfaces `[responseHeaders sid hs]`. -/
theorem pump_receive_single (hd : Hpack.HuffmanDecoder) (sid : Nat)
    (hs : List (Bytes × Bytes)) (fuel : Nat) (hf : 1 ≤ fuel)
    (hsid : sid < 2 ^ 31) (hblk : (encodeHeaders hs).length ≤ 16384)
    (hsmall : ∀ p ∈ hs, p.1.length < 127 ∧ p.2.length < 127) :
    (pump hd fuel ({ buf := encodeFrame (.headers sid true true (encodeHeaders hs)) } : RState)).2
      = [.responseHeaders sid hs] := by
  have h24 : (16384 : Nat) < 2 ^ 24 := by decide
  have hHlen : (encodeFrame (Frame.headers sid true true (encodeHeaders hs))).length
      = 9 + (encodeHeaders hs).length := encodeFrame_headers_length _ _ _ _
  have hdecH : _root_.H2.decode (encodeFrame (Frame.headers sid true true (encodeHeaders hs))) 16384
      = .complete (.headers sid true true (encodeHeaders hs)) (9 + (encodeHeaders hs).length) :=
    decode_encode_headers sid true true _ 16384 hsid (by omega) hblk
  have hdropH : (encodeFrame (Frame.headers sid true true (encodeHeaders hs))).drop
      (9 + (encodeHeaders hs).length) = [] := by rw [← hHlen]; exact List.drop_length
  rcases fuel with _ | f
  · omega
  refine pump_step_snd hd f _ (Frame.headers sid true true (encodeHeaders hs))
    (9 + (encodeHeaders hs).length) [.responseHeaders sid hs] hdecH
    (by rw [stepFrame_headers_end hd _ sid true _ rfl,
      finishHeaders_encodeHeaders hd _ sid hs rfl hsmall]) ?_
  rw [pump_buf_nil hd f _ (by
    show (encodeFrame (Frame.headers sid true true (encodeHeaders hs))).drop
      (9 + (encodeHeaders hs).length) = []
    rw [hdropH])]

/-! ## The public receive-faithfulness theorems -/

/-- **Client↔server receive agreement** (the H2 analogue of
`Client.H1.transaction_faithful` for the response direction): for a response the
drorb **server** serializes as `HEADERS(+CONTINUATION)` + `DATA(body,
END_STREAM)` — the header block HPACK-encoded and **split across the CONTINUATION
boundary** at `n1` — the client receive loop reassembles **exactly** the response
the server sent: the header field list `hs` and the body `body`, surfaced as
`[responseHeaders sid hs, responseData sid body true]`. Composes the server's
`H2.FrameEncode`/`H2.HpackEncode` encode with the client's `H2.Frame.decode` +
HPACK decode. (`n1 ≥ block.length` gives the un-split whole-block case.) -/
theorem h2_client_receive_faithful (hd : Hpack.HuffmanDecoder) (sid n1 : Nat)
    (hs : List (Bytes × Bytes)) (body : Bytes)
    (hsid : sid < 2 ^ 31)
    (hblk : (encodeHeaders hs).length ≤ 16384) (hbody : body.length ≤ 16384)
    (hsmall : ∀ p ∈ hs, p.1.length < 127 ∧ p.2.length < 127) :
    (feed hd initR (serverWire sid hs body n1)).2
      = [.responseHeaders sid hs, .responseData sid body true] := by
  have hHlen : (encodeFrame (Frame.headers sid false false ((encodeHeaders hs).take n1))).length
      = 9 + ((encodeHeaders hs).take n1).length := encodeFrame_headers_length _ _ _ _
  have hbound : 3 ≤ (serverWire sid hs body n1).length + 1 := by
    have h1 : (encodeFrame (Frame.headers sid false false ((encodeHeaders hs).take n1))).length
        ≤ (serverWire sid hs body n1).length := by
      unfold serverWire; rw [List.length_append]; omega
    omega
  rw [feed_initR]
  exact pump_receive hd sid n1 hs body _ hbound hsid hblk hbody hsmall

/-- **CONTINUATION assembly is lossless** (RFC 9113 §4.3): a response header block
delivered **split** across a `HEADERS` frame (`END_HEADERS` clear) + a
`CONTINUATION` frame (`END_HEADERS` set) decodes to exactly the same fields as the
same block delivered whole in one `END_HEADERS` `HEADERS` frame. Both surface
`[responseHeaders sid hs]`. -/
theorem h2_continuation_assembles (hd : Hpack.HuffmanDecoder) (sid n1 : Nat)
    (hs : List (Bytes × Bytes))
    (hsid : sid < 2 ^ 31) (hblk : (encodeHeaders hs).length ≤ 16384)
    (hsmall : ∀ p ∈ hs, p.1.length < 127 ∧ p.2.length < 127) :
    (feed hd initR (encodeFrame (.headers sid false false ((encodeHeaders hs).take n1))
        ++ encodeFrame (.continuation sid true ((encodeHeaders hs).drop n1)))).2
      = (feed hd initR (encodeFrame (.headers sid true true (encodeHeaders hs)))).2 := by
  have hHlen : (encodeFrame (Frame.headers sid false false ((encodeHeaders hs).take n1))).length
      = 9 + ((encodeHeaders hs).take n1).length := encodeFrame_headers_length _ _ _ _
  have hH'len : (encodeFrame (Frame.headers sid true true (encodeHeaders hs))).length
      = 9 + (encodeHeaders hs).length := encodeFrame_headers_length _ _ _ _
  -- Split side.
  have hL : (feed hd initR (encodeFrame (.headers sid false false ((encodeHeaders hs).take n1))
      ++ encodeFrame (.continuation sid true ((encodeHeaders hs).drop n1)))).2
      = [.responseHeaders sid hs] := by
    rw [feed_initR]
    refine pump_receive_split hd sid n1 hs _ ?_ hsid hblk hsmall
    rw [List.length_append]; omega
  -- Single side.
  have hR : (feed hd initR (encodeFrame (.headers sid true true (encodeHeaders hs)))).2
      = [.responseHeaders sid hs] := by
    rw [feed_initR]
    refine pump_receive_single hd sid hs _ ?_ hsid hblk hsmall
    omega
  rw [hL, hR]

/-! ## Grounding — a concrete `200` response, not vacuous -/

/-- A concrete response header list: `:status 200` then a `ct: txt` field. -/
def resp200 : List (Bytes × Bytes) :=
  [(pStatus, [0x32, 0x30, 0x30]),        -- ":status" "200"
   ([0x63, 0x74], [0x74, 0x78, 0x74])]   -- "ct" "txt"

/-- A concrete response body, `hi`. -/
def resp200Body : Bytes := [0x68, 0x69]

/-- **Non-vacuous:** a real `200` response, its header block **split across a
CONTINUATION** at octet 3, is received back **exactly** — status + field + body —
by the client receive loop. -/
theorem receive_200_faithful (hd : Hpack.HuffmanDecoder) :
    (feed hd initR (serverWire 1 resp200 resp200Body 3)).2
      = [.responseHeaders 1 resp200, .responseData 1 resp200Body true] :=
  h2_client_receive_faithful hd 1 3 resp200 resp200Body
    (by decide) (by decide) (by decide) (by decide)

/-- …and reassembled into a complete `ClientResponse`: status `200`, the `ct`
header, body `hi`. -/
theorem reassemble_200 (hd : Hpack.HuffmanDecoder) :
    reassemble (feed hd initR (serverWire 1 resp200 resp200Body 3)).2
      = some { status := [0x32, 0x30, 0x30],
               headers := [([0x63, 0x74], [0x74, 0x78, 0x74])],
               body := resp200Body } := by
  rw [receive_200_faithful]; rfl

/-- Non-vacuous CONTINUATION-assembly: the concrete `200` head split at octet 3
across `HEADERS`+`CONTINUATION` reassembles to the same one `responseHeaders`
event as the whole-block delivery. -/
theorem continuation_assembles_200 (hd : Hpack.HuffmanDecoder) :
    (feed hd initR (encodeFrame (.headers 1 false false ((encodeHeaders resp200).take 3))
        ++ encodeFrame (.continuation 1 true ((encodeHeaders resp200).drop 3)))).2
      = (feed hd initR (encodeFrame (.headers 1 true true (encodeHeaders resp200)))).2 :=
  h2_continuation_assembles hd 1 3 resp200 (by decide) (by decide) (by decide)

/-! ## Follow-on 1 — client-emitted flow-control `WINDOW_UPDATE` (RFC 9113 §6.9)

As the client consumes the octets of a received `DATA` frame it must return that
credit to the peer so the peer's send window does not permanently shrink. It
emits a `WINDOW_UPDATE` frame carrying the consumed octet count as its 31-bit
increment, at both the connection (stream 0) and the stream level. -/

/-- The 4-octet big-endian `WINDOW_UPDATE` increment payload (RFC 9113 §6.9.1),
laid with the deployed frame-field encoder. -/
def wuPayload (n : Nat) : Bytes := _root_.H2.FrameEncode.be32 n

/-- The `WINDOW_UPDATE` frame the client emits on `sid` for an increment of `n`
octets (stream 0 = the connection level). -/
def windowUpdateFrame (sid n : Nat) : Frame := Frame.windowUpdate sid (wuPayload n)

/-- Read the 31-bit increment back off a 4-octet `WINDOW_UPDATE` payload
(big-endian), the inverse the peer applies. -/
def wuIncrement : Bytes → Nat
  | b0 :: b1 :: b2 :: b3 :: _ =>
    b0.toNat * 16777216 + b1.toNat * 65536 + b2.toNat * 256 + b3.toNat
  | _ => 0

/-- The increment the client lays reads back exactly (a 32-bit round-trip; a
consumed-octet count is always well within range). -/
theorem wuIncrement_wuPayload (n : Nat) (h : n < 4294967296) : wuIncrement (wuPayload n) = n := by
  simp only [wuPayload, _root_.H2.FrameEncode.be32, wuIncrement, UInt8.toNat_ofNat']
  omega

/-- The emitted `WINDOW_UPDATE` frame decodes back (via the deployed round-trip)
to a `WINDOW_UPDATE` on `sid` carrying the increment payload — the peer receives
exactly the credit the client returned. -/
theorem windowUpdateFrame_decode (sid n mfs : Nat) (hsid : sid < 2 ^ 31) (hmfs : 4 ≤ mfs) :
    _root_.H2.decode (encodeFrame (windowUpdateFrame sid n)) mfs
      = .complete (Frame.windowUpdate sid (wuPayload n)) 13 := by
  have hlen : (wuPayload n).length = 4 := rfl
  have h := _root_.H2.FrameEncode.decode_encode_windowUpdate sid (wuPayload n) mfs hsid
    (by rw [hlen]; decide) (by rw [hlen]; exact hmfs)
  rw [hlen] at h
  exact h

/-- The `WINDOW_UPDATE` frames the client emits while consuming a run of surfaced
receive events: for each `responseData` frame of `N > 0` octets it returns credit
`N` at the connection level (stream 0) and at the stream level. -/
def windowUpdatesFor (sid : Nat) : List REvent → List Frame
  | [] => []
  | .responseData s d _ :: rest =>
      (if d.length = 0 then [] else [windowUpdateFrame 0 d.length, windowUpdateFrame s d.length])
        ++ windowUpdatesFor sid rest
  | _ :: rest => windowUpdatesFor sid rest

open _root_.H2.FlowWindow (Flow window_update_credits)

/-- **`client_sends_window_update`** (RFC 9113 §6.9). Consuming a `DATA` frame of
`N > 0` octets on `sid`, the client:

1. emits a connection-level and a stream-level `WINDOW_UPDATE`, each carrying the
   increment `N` (`windowUpdatesFor`);
2. lays that increment `N` on the wire so the peer reads it back exactly
   (`wuIncrement (wuPayload N) = N`); and
3. crediting the peer's send `Flow` by `N` raises its stream window by **exactly**
   `N` and keeps the window well-formed — so the client replenishes precisely the
   consumed octets and never drives the peer's window negative.

Points 3 **compose the proven flow-control theorems**
`H2.FlowWindow.window_update_credits` and `H2.FlowWindow.Flow.strUpdate_WF`. -/
theorem client_sends_window_update (sid : Nat) (d : Bytes) (es : Bool)
    (f : Flow) (hne : 0 < d.length) (hlen : d.length < 4294967296) (hwf : f.WF)
    (hcap : f.strWindow + (d.length : Int) ≤ _root_.H2.Conn.maxWindow) :
    windowUpdatesFor sid [.responseData sid d es]
        = [windowUpdateFrame 0 d.length, windowUpdateFrame sid d.length]
    ∧ wuIncrement (wuPayload d.length) = d.length
    ∧ (f.strUpdate (d.length : Int)).strWindow = f.strWindow + (d.length : Int)
    ∧ (f.strUpdate (d.length : Int)).WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [windowUpdatesFor, if_neg (by omega : ¬ d.length = 0), List.append_nil]
  · exact wuIncrement_wuPayload d.length hlen
  · exact window_update_credits f (d.length : Int) (by exact_mod_cast hne) hcap
  · exact Flow.strUpdate_WF (d.length : Int) hwf

/-! ## Follow-on 2 — trailer-section receive (RFC 9113 §8.1) -/

open _root_.H2.RespTrailers (noPseudo trailers_no_pseudo grpcTrailers grpcTrailers_no_pseudo)

/-- Walk the surfaced events for a **trailer** header block: the *initial*
response header block arrives before any `DATA`; a header block that completes
*after* ≥ 1 `DATA` frame is the trailer section (RFC 9113 §8.1). Returns the
trailer fields, or `[]` if the response carried no post-DATA header block. -/
def collectTrailers : Bool → List REvent → List (Bytes × Bytes)
  | _,    [] => []
  | true, .responseHeaders _ hs :: _ => hs
  | _,    .responseData _ _ _ :: rest => collectTrailers true rest
  | seen, _ :: rest => collectTrailers seen rest

/-- Reassemble the surfaced events into a `ClientResponse` **including trailers**:
status + fields + body as `reassemble`, plus the post-DATA trailer block. -/
def reassembleT (evs : List REvent) : Option ClientResponse :=
  match firstHeaders evs with
  | none => none
  | some (_, hs) =>
    let (status, rest) := splitStatus hs
    some { status := status, headers := rest, body := collectBody evs,
           trailers := collectTrailers false evs }

/-- The exact octets a drorb HTTP/2 **server** serializes for a response that
finishes with a trailer section (RFC 9113 §8.1, the gRPC shape): a `HEADERS`
frame (`END_HEADERS`, `END_STREAM` **clear** — the stream stays open), a `DATA`
frame carrying `body` (`END_STREAM` clear), then a trailer `HEADERS` frame
(`END_STREAM` **set**) carrying the HPACK-encoded trailer block. -/
def serverWireTrailers (sid : Nat) (hs : List (Bytes × Bytes)) (body : Bytes)
    (tr : List (Bytes × Bytes)) : Bytes :=
  encodeFrame (.headers sid false true (encodeHeaders hs))
    ++ (encodeFrame (.data sid false body)
        ++ encodeFrame (.headers sid true true (encodeHeaders tr)))

/-- **The receive run over a response finished with trailers.** Walking
`serverWireTrailers` off the buffer surfaces the response head, the body, and the
trailer block as a *second* completed header block:
`[responseHeaders sid hs, responseData sid body false, responseHeaders sid tr]`. -/
theorem pump_receive_trailers (hd : Hpack.HuffmanDecoder) (sid : Nat)
    (hs : List (Bytes × Bytes)) (body : Bytes) (tr : List (Bytes × Bytes))
    (fuel : Nat) (hf : 3 ≤ fuel) (hsid : sid < 2 ^ 31)
    (hblk : (encodeHeaders hs).length ≤ 16384) (hbody : body.length ≤ 16384)
    (htr : (encodeHeaders tr).length ≤ 16384)
    (hsmall : ∀ p ∈ hs, p.1.length < 127 ∧ p.2.length < 127)
    (hsmallT : ∀ p ∈ tr, p.1.length < 127 ∧ p.2.length < 127) :
    (pump hd fuel ({ buf := serverWireTrailers sid hs body tr } : RState)).2
      = [.responseHeaders sid hs, .responseData sid body false, .responseHeaders sid tr] := by
  have h24 : (16384 : Nat) < 2 ^ 24 := by decide
  have hHlen : (encodeFrame (Frame.headers sid false true (encodeHeaders hs))).length
      = 9 + (encodeHeaders hs).length := encodeFrame_headers_length _ _ _ _
  have hDlen : (encodeFrame (Frame.data sid false body)).length = 9 + body.length :=
    encodeFrame_data_length _ _ _
  have hTlen : (encodeFrame (Frame.headers sid true true (encodeHeaders tr))).length
      = 9 + (encodeHeaders tr).length := encodeFrame_headers_length _ _ _ _
  -- Per-frame decodes.
  have hdecH : _root_.H2.decode (serverWireTrailers sid hs body tr) 16384
      = .complete (.headers sid false true (encodeHeaders hs)) (9 + (encodeHeaders hs).length) := by
    unfold serverWireTrailers
    exact decode_prefix _ _ 16384 _ _
      (decode_encode_headers sid false true _ 16384 hsid (by omega) hblk)
  have hdecD : _root_.H2.decode
        (encodeFrame (Frame.data sid false body)
          ++ encodeFrame (Frame.headers sid true true (encodeHeaders tr))) 16384
      = .complete (.data sid false body) (9 + body.length) :=
    decode_prefix _ _ 16384 _ _ (decode_encode_data sid false body 16384 hsid (by omega) hbody)
  have hdecT : _root_.H2.decode (encodeFrame (Frame.headers sid true true (encodeHeaders tr))) 16384
      = .complete (.headers sid true true (encodeHeaders tr)) (9 + (encodeHeaders tr).length) :=
    decode_encode_headers sid true true _ 16384 hsid (by omega) htr
  -- Buffer remainders after each frame.
  have hdropH : (serverWireTrailers sid hs body tr).drop (9 + (encodeHeaders hs).length)
      = encodeFrame (Frame.data sid false body)
          ++ encodeFrame (Frame.headers sid true true (encodeHeaders tr)) := by
    unfold serverWireTrailers; rw [← hHlen]; exact List.drop_left
  have hdropD : (encodeFrame (Frame.data sid false body)
        ++ encodeFrame (Frame.headers sid true true (encodeHeaders tr))).drop (9 + body.length)
      = encodeFrame (Frame.headers sid true true (encodeHeaders tr)) := by
    rw [← hDlen]; exact List.drop_left
  have hdropT : (encodeFrame (Frame.headers sid true true (encodeHeaders tr))).drop
      (9 + (encodeHeaders tr).length) = [] := by rw [← hTlen]; exact List.drop_length
  -- Peel three complete frames, then the empty buffer.
  rcases fuel with _ | _ | _ | f
  · omega
  · omega
  · omega
  -- Frame 1: response HEADERS (END_HEADERS, END_STREAM clear) completes the head.
  refine pump_step_snd hd (f + 2) _ (Frame.headers sid false true (encodeHeaders hs))
    (9 + (encodeHeaders hs).length) [.responseHeaders sid hs] hdecH
    (by rw [stepFrame_headers_end hd _ sid false _ rfl,
      finishHeaders_encodeHeaders hd _ sid hs rfl hsmall]) ?_
  -- Frame 2: DATA (END_STREAM clear) surfaces the body.
  refine pump_step_snd hd (f + 1) _ (Frame.data sid false body) (9 + body.length)
    [.responseData sid body false]
    (by
      show _root_.H2.decode ((serverWireTrailers sid hs body tr).drop
        (9 + (encodeHeaders hs).length)) 16384 = _
      rw [hdropH]; exact hdecD)
    (stepFrame_data hd _ sid false _ rfl) ?_
  -- Frame 3: trailer HEADERS (END_STREAM set) completes the trailer block.
  refine pump_step_snd hd f _ (Frame.headers sid true true (encodeHeaders tr))
    (9 + (encodeHeaders tr).length) [.responseHeaders sid tr]
    (by
      show _root_.H2.decode (((serverWireTrailers sid hs body tr).drop
        (9 + (encodeHeaders hs).length)).drop (9 + body.length)) 16384 = _
      rw [hdropH, hdropD]; exact hdecT)
    (by rw [stepFrame_headers_end hd _ sid true _ rfl,
      finishHeaders_encodeHeaders hd _ sid tr rfl hsmallT]) ?_
  -- Frame 4+: the buffer is empty.
  rw [pump_buf_nil hd f _ (by
    show (((serverWireTrailers sid hs body tr).drop (9 + (encodeHeaders hs).length)).drop
        (9 + body.length)).drop (9 + (encodeHeaders tr).length) = []
    rw [hdropH, hdropD, hdropT])]

/-- **`h2_client_receive_trailers`** (RFC 9113 §8.1). For a response the drorb
**server** serializes as `HEADERS + DATA + trailer-HEADERS(END_STREAM)` — the gRPC
`grpc-status` delivery shape — the client receive loop reassembles the response
**with its trailer block HPACK-decoded into `ClientResponse.trailers`** (status +
body from the head + DATA, trailers from the post-DATA header block). And, for a
`noPseudo` trailer section, **composing `H2.RespTrailers.trailers_no_pseudo`**, the
surfaced trailers carry no pseudo-header field. Composes the server's frame + HPACK
encode with the client's decode. -/
theorem h2_client_receive_trailers (hd : Hpack.HuffmanDecoder) (sid : Nat)
    (hs : List (Bytes × Bytes)) (body : Bytes) (tr : List (Bytes × Bytes))
    (hsid : sid < 2 ^ 31)
    (hblk : (encodeHeaders hs).length ≤ 16384) (hbody : body.length ≤ 16384)
    (htr : (encodeHeaders tr).length ≤ 16384)
    (hsmall : ∀ p ∈ hs, p.1.length < 127 ∧ p.2.length < 127)
    (hsmallT : ∀ p ∈ tr, p.1.length < 127 ∧ p.2.length < 127)
    (hnp : noPseudo tr = true) :
    reassembleT (feed hd initR (serverWireTrailers sid hs body tr)).2
        = some { status := (splitStatus hs).1, headers := (splitStatus hs).2,
                 body := body, trailers := tr }
    ∧ (∀ f ∈ tr, _root_.H2.PseudoHeader.isPseudoName f.1 = false) := by
  have hev : (feed hd initR (serverWireTrailers sid hs body tr)).2
      = [.responseHeaders sid hs, .responseData sid body false, .responseHeaders sid tr] := by
    have hbound : 3 ≤ (serverWireTrailers sid hs body tr).length + 1 := by
      have h1 : (encodeFrame (Frame.headers sid false true (encodeHeaders hs))).length
          ≤ (serverWireTrailers sid hs body tr).length := by
        unfold serverWireTrailers; rw [List.length_append]; omega
      have h2 : 9 ≤ (encodeFrame (Frame.headers sid false true (encodeHeaders hs))).length := by
        rw [encodeFrame_headers_length]; omega
      omega
    rw [feed_initR]
    exact pump_receive_trailers hd sid hs body tr _ hbound hsid hblk hbody htr hsmall hsmallT
  refine ⟨?_, (trailers_no_pseudo tr).mp hnp⟩
  rw [hev]
  simp only [reassembleT, firstHeaders, collectBody, collectTrailers, splitStatus,
    List.append_nil]

/-! ## Grounding — a concrete `200` response with a body and gRPC trailers -/

/-- The concrete gRPC trailer section: `grpc-status: 0`, `grpc-message: OK`. -/
def respTrailers200 : List (Bytes × Bytes) := grpcTrailers [0x30] [0x4f, 0x4b]

/-- **Non-vacuous (trailers):** a real `200` response with a body **and** a gRPC
trailer section is received back exactly — status + field + body **and the
`grpc-status`/`grpc-message` trailers** — reassembled into a `ClientResponse`, and
the surfaced trailers carry no pseudo-headers. -/
theorem receive_trailers_200 (hd : Hpack.HuffmanDecoder) :
    reassembleT (feed hd initR (serverWireTrailers 1 resp200 resp200Body respTrailers200)).2
        = some { status := [0x32, 0x30, 0x30],
                 headers := [([0x63, 0x74], [0x74, 0x78, 0x74])],
                 body := resp200Body, trailers := respTrailers200 }
    ∧ (∀ f ∈ respTrailers200, _root_.H2.PseudoHeader.isPseudoName f.1 = false) := by
  have h := h2_client_receive_trailers hd 1 resp200 resp200Body respTrailers200
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (grpcTrailers_no_pseudo [0x30] [0x4f, 0x4b])
  simpa [respTrailers200, resp200, splitStatus, pStatus] using h

/-- **Non-vacuous (WINDOW_UPDATE):** consuming the concrete `200` response body
(2 octets) really emits a connection- and stream-level `WINDOW_UPDATE(2)`, whose
increment reads back as `2`, and crediting a peer send window by it raises that
window by exactly `2` while keeping it well-formed. -/
theorem client_window_update_200 :
    windowUpdatesFor 1 [.responseData 1 resp200Body true]
        = [windowUpdateFrame 0 2, windowUpdateFrame 1 2]
    ∧ wuIncrement (wuPayload 2) = 2
    ∧ ((Flow.fresh 1000000 65535).strUpdate 2).strWindow = 65537
    ∧ ((Flow.fresh 1000000 65535).strUpdate 2).WF :=
  ⟨by decide,
   wuIncrement_wuPayload 2 (by decide),
   by rw [window_update_credits (Flow.fresh 1000000 65535) 2 (by decide) (by decide)]; decide,
   Flow.strUpdate_WF 2 (Flow.fresh_WF (by decide) (by decide) (by decide) (by decide))⟩

#print axioms h2_client_receive_faithful
#print axioms h2_continuation_assembles
#print axioms receive_200_faithful
#print axioms client_sends_window_update
#print axioms h2_client_receive_trailers
#print axioms receive_trailers_200
#print axioms client_window_update_200

end H2Receive
end Client
end Proto
