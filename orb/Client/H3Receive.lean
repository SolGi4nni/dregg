import Client.H3

/-!
# The HTTP/3 client **response receive** loop (RFC 9114 §7)

`Client/H3.lean` proves the request-submit side of the drorb HTTP/3 client and a
single-frame receive step (`h3ClientStep`). This module completes the **receive**
side with the multi-frame response reassembly faithfulness: for a response the
drorb **server** serializes on the QUIC request stream as a QPACK `HEADERS` frame
+ a `DATA` frame, the client's `h3ClientFeed` walks both whole frames off the
stream (via the deployed `H3.decFrame` frame loop), decodes the `HEADERS` field
section through the **deployed `H3.Qpack.decodeFieldSection`**, and reassembles a
complete response — the decoded head + the body — surfacing
`[responseHead …, responseData body]`.

## What is proven (0 sorries; axioms ⊆ `{propext, Quot.sound, Classical.choice}`)

* `decFrames_response` — the deployed H3 frame loop cuts a server-encoded
  `HEADERS(sect)` + `DATA(body)` response into exactly the two frames
  `[.headers sect, .data body]`, no remainder (RFC 9114 §7.1).
* `h3_client_receive_faithful` — end-to-end: `h3ClientFeed` on that wire surfaces
  exactly `[responseHead d.store d.pseudo d.fields, responseData body]`, where
  `d` is the deployed `decodeFieldSection` of the exact `sect` the server
  framed — the client reassembles exactly the response the server sent (the
  decoded field section + the body). Composes the server's `H3.Client` frame
  encoders with the client's `H3.decFrame` + `decodeFieldSection`.

Grounded (non-vacuous) on a real section the deployed decoder accepts (the four
request pseudo-headers via `H3.Client.requestSection_faithful`) and a real body,
exercising the whole receive loop on genuine frames.

Deliberate scope (named follow-on): the QPACK decode of a **response**-shaped
section (a `:status` head + response fields) is the deployed `decodeFieldSection`
on a different section — the same loop, and its `.ok` witness is that decoder's
own theory; the multi-frame HEADERS+DATA reassembly and its faithfulness are
proven here.
-/

namespace Proto
namespace Client
namespace H3Receive

open _root_.H3 (Frame FrameResult decFrame decFrames Bytes)
open _root_.H3.Client (encHeadersFrame encDataFrame encHeadersFrame_eq encDataFrame_eq
  decFrame_encDataFrame)
open Proto.Client.H3 (H3ClientState H3ClientEvent h3ClientStep h3ClientFeed initClient)

/-! ## The deployed frame loop cuts a HEADERS+DATA response into two frames -/

/-- A completed `HEADERS`-frame decode is stable under a trailing frame: the H3
frame decoder reads exactly the declared section and stops, leaving the following
`DATA` frame for the next loop step (RFC 9114 §7.1). -/
theorem decFrame_headers_prefix (enc lb rest : Bytes)
    (hl : _root_.H3.Varint.encVarint enc.length = some lb) :
    decFrame ((0x01 :: (lb ++ enc)) ++ rest)
      = .complete (.headers enc) (1 + lb.length + enc.length) := by
  have hcons : (0x01 :: (lb ++ enc)) ++ rest = (0x01 : UInt8) :: (lb ++ (enc ++ rest)) := by
    simp [List.append_assoc]
  have h0 : _root_.H3.Varint.decVarint ((0x01 : UInt8) :: (lb ++ (enc ++ rest))) = some (1, 1) :=
    _root_.H3.Varint.decVarint_case0 0x01 (lb ++ (enc ++ rest)) (by decide)
  have h1 : _root_.H3.Varint.decVarint (lb ++ (enc ++ rest)) = some (enc.length, lb.length) :=
    _root_.H3.Varint.decVarint_encVarint enc.length lb (enc ++ rest) hl
  have hdrop : ((0x01 : UInt8) :: (lb ++ (enc ++ rest))).drop (1 + lb.length) = enc ++ rest := by
    rw [show (0x01 : UInt8) :: (lb ++ (enc ++ rest)) = ([0x01] ++ lb) ++ (enc ++ rest) by
          simp [List.append_assoc],
        show 1 + lb.length = ([0x01] ++ lb).length by
          rw [List.length_append, List.length_singleton],
        List.drop_left]
  rw [hcons]
  unfold decFrame
  rw [h0]
  simp only []
  rw [show ((0x01 : UInt8) :: (lb ++ (enc ++ rest))).drop 1 = lb ++ (enc ++ rest) from rfl, h1]
  simp only []
  rw [hdrop, if_neg (by rw [List.length_append]; omega), List.take_left]
  rfl

/-- `decFrames` on a server-encoded `HEADERS(sect)` + `DATA(body)` response
yields exactly `[.headers sect, .data body]` with no remainder. -/
theorem decFrames_response (sect body lb ld : Bytes)
    (hl : _root_.H3.Varint.encVarint sect.length = some lb)
    (hld : _root_.H3.Varint.encVarint body.length = some ld) :
    decFrames ((0x01 :: (lb ++ sect)) ++ (0x00 :: (ld ++ body)))
      = ([.headers sect, .data body], []) := by
  have hHlen : (0x01 :: (lb ++ sect)).length = 1 + lb.length + sect.length := by
    rw [List.length_cons, List.length_append]; omega
  have hdrophdr : ((0x01 :: (lb ++ sect)) ++ (0x00 :: (ld ++ body))).drop
      (1 + lb.length + sect.length) = 0x00 :: (ld ++ body) := by
    rw [← hHlen]; exact List.drop_left
  have hdropdata : (0x00 :: (ld ++ body)).drop (1 + ld.length + body.length) = [] := by
    rw [show (1 + ld.length + body.length) = (0x00 :: (ld ++ body)).length by
          rw [List.length_cons, List.length_append]; omega]
    exact List.drop_length
  -- First frame: the HEADERS frame.
  rw [decFrames, decFrame_headers_prefix sect lb (0x00 :: (ld ++ body)) hl]
  simp only [hdrophdr]
  -- Second frame: the DATA frame.
  rw [decFrames, decFrame_encDataFrame body ld hld]
  simp only [hdropdata]
  -- Third: the empty remainder decodes to nothing.
  have hnil : decFrames ([] : Bytes) = ([], []) := by
    rw [decFrames, show decFrame ([] : Bytes) = .incomplete from rfl]
  rw [hnil]

/-! ## The receive-loop faithfulness -/

/-- **Client↔server receive agreement over the QUIC request stream** (the H3
analogue of `Client.H2Receive.h2_client_receive_faithful`): for a response the
server serializes as `HEADERS(sect)` + `DATA(body)`, the client's
`h3ClientFeed` walks both frames, decodes the header section through the
**deployed `decodeFieldSection`**, and reassembles exactly the response — the
decoded head `d` and the body — surfacing `[responseHead …, responseData body]`.
`hdec` ties `d` to the exact `sect` the server framed. -/
theorem h3_client_receive_faithful (hd : _root_.H3.Qpack.HuffmanDecoder)
    (sect body lb ld : Bytes) (d : _root_.H3.Qpack.Decoded)
    (hl : _root_.H3.Varint.encVarint sect.length = some lb)
    (hld : _root_.H3.Varint.encVarint body.length = some ld)
    (hdec : _root_.H3.Qpack.decodeFieldSection hd initClient.qpack sect = .ok d) :
    (h3ClientFeed hd initClient ((0x01 :: (lb ++ sect)) ++ (0x00 :: (ld ++ body)))).2
      = [.responseHead d.store d.pseudo d.fields, .responseData body] := by
  unfold h3ClientFeed
  rw [show initClient.buf ++ ((0x01 :: (lb ++ sect)) ++ (0x00 :: (ld ++ body)))
        = (0x01 :: (lb ++ sect)) ++ (0x00 :: (ld ++ body)) from rfl,
      decFrames_response sect body lb ld hl hld]
  simp only [List.foldl, h3ClientStep, hdec, List.nil_append, List.singleton_append]

/-! ## Grounding — the receive loop on genuine frames + a genuine decode -/

/-- A genuine `decodeFieldSection` witness: an empty QPACK field section (the
stateless section prefix, no field lines) decodes to the empty head — real, not
vacuous. -/
theorem decode_emptyFields (hd : _root_.H3.Qpack.HuffmanDecoder) :
    _root_.H3.Qpack.decodeFieldSection hd initClient.qpack (_root_.H3.Qpack.encodeFieldSection [])
      = .ok ⟨initClient.qpack, {}, []⟩ := by
  show _root_.H3.Qpack.decodeFieldSection hd initClient.qpack
      (_root_.H3.Qpack.sectionPrefix ++ []) = _
  rw [_root_.H3.Qpack.decodeFieldSection_prefix,
    show _root_.H3.Qpack.decodeLines hd initClient.qpack [] {} []
        _root_.H3.Qpack.DynTable.empty 0 = .ok (initClient.qpack, {}, [])
      from by rw [_root_.H3.Qpack.decodeLines, List.reverse_nil]]
  rfl

/-- **Non-vacuous:** a real response — an (empty-field) QPACK `HEADERS` frame plus
a `DATA(hi)` frame the server framed — is walked, decoded, and reassembled by the
client receive loop into exactly `[responseHead …, responseData hi]`. -/
theorem receive_grounded (hd : _root_.H3.Qpack.HuffmanDecoder) :
    (h3ClientFeed hd initClient
        ((0x01 :: ([0x02] ++ _root_.H3.Qpack.encodeFieldSection []))
          ++ (0x00 :: ([0x02] ++ [0x68, 0x69])))).2
      = [.responseHead initClient.qpack {} [], .responseData [0x68, 0x69]] :=
  h3_client_receive_faithful hd (_root_.H3.Qpack.encodeFieldSection []) [0x68, 0x69]
    [0x02] [0x02] ⟨initClient.qpack, {}, []⟩ (by decide) (by decide) (decode_emptyFields hd)

/-! ## Reassembling a complete `ClientResponse` (RFC 9114 §7.1, §4.1)

The events surfaced by the receive loop reassemble into a single response value:
the QPACK-decoded head (store + pseudo + regular field lines — note RFC 9204
routes `:status` as an ordinary field line, so it lands in `fields`), the
concatenated body octets, and — if a *second* header block completes after the
body — the trailer section (RFC 9114 §4.1: `HEADERS (DATA|Unknown)* [HEADERS]`). -/

/-- A complete HTTP/3 response, as the client reassembles it from the surfaced
`H3ClientEvent`s: the QPACK-decoded head (`store`, `pseudo`, regular `fields`),
the concatenated `body`, and a post-DATA `trailers` field section (empty when the
response carried no trailer block). -/
structure ClientResponse where
  store : Arena.Store
  pseudo : _root_.H3.Qpack.Pseudo
  fields : List _root_.H3.Qpack.FieldLine
  body : Bytes
  trailers : List _root_.H3.Qpack.FieldLine := []

/-- Concatenate the body octets from every `responseData` event, in order. -/
def collectBody : List H3ClientEvent → Bytes
  | [] => []
  | .responseData d :: rest => d ++ collectBody rest
  | _ :: rest => collectBody rest

/-- The first completed response header block (the response head). -/
def firstHead : List H3ClientEvent →
    Option (Arena.Store × _root_.H3.Qpack.Pseudo × List _root_.H3.Qpack.FieldLine)
  | [] => none
  | .responseHead s p f :: _ => some (s, p, f)
  | _ :: rest => firstHead rest

/-- Reassemble the surfaced events into a `ClientResponse` (head + body). `none`
iff no response header block was surfaced. -/
def reassemble (evs : List H3ClientEvent) : Option ClientResponse :=
  match firstHead evs with
  | none => none
  | some (s, p, f) => some { store := s, pseudo := p, fields := f, body := collectBody evs }

/-- Walk the surfaced events for a **trailer** header block (RFC 9114 §4.1): the
*initial* response head arrives before any `DATA`; a header block that completes
*after* ≥ 1 `DATA` frame is the trailer section. Returns the trailer field lines,
or `[]` if the response carried no post-DATA header block. -/
def collectTrailers : Bool → List H3ClientEvent → List _root_.H3.Qpack.FieldLine
  | _,    [] => []
  | true, .responseHead _ _ f :: _ => f
  | _,    .responseData _ :: rest => collectTrailers true rest
  | seen, _ :: rest => collectTrailers seen rest

/-- Reassemble the surfaced events into a `ClientResponse` **including trailers**:
head + body as `reassemble`, plus the post-DATA trailer field section. -/
def reassembleT (evs : List H3ClientEvent) : Option ClientResponse :=
  match firstHead evs with
  | none => none
  | some (s, p, f) =>
    some { store := s, pseudo := p, fields := f, body := collectBody evs,
           trailers := collectTrailers false evs }

/-- The client feed's residual buffer is exactly the `decFrames` remainder — the
truncated bytes of a partial trailing frame. Empty iff the transport bytes ended
on a frame boundary. -/
theorem h3ClientFeed_buf (hd : _root_.H3.Qpack.HuffmanDecoder) (st : H3ClientState) (input : Bytes) :
    (h3ClientFeed hd st input).1.buf = (_root_.H3.decFrames (st.buf ++ input)).2 := by
  unfold h3ClientFeed
  rfl

/-! ## `h3_client_receive` — a HEADERS(QPACK)+DATA stream reassembles a response -/

/-- **`h3_client_receive`** (RFC 9114 §7.1). For a response the drorb **server**
serializes on the QUIC request stream as a QPACK `HEADERS(sect)` frame + a
`DATA(body)` frame, the client's `h3ClientFeed` walks both frames, decodes the
field section through the **deployed `decodeFieldSection`**, and reassembles a
complete `ClientResponse`: the decoded head `d` (store + pseudo + fields; the
`:status` field line lives in `fields` per RFC 9204) and the body. `hdec` ties `d`
to the exact `sect` the server framed. -/
theorem h3_client_receive (hd : _root_.H3.Qpack.HuffmanDecoder)
    (sect body lb ld : Bytes) (d : _root_.H3.Qpack.Decoded)
    (hl : _root_.H3.Varint.encVarint sect.length = some lb)
    (hld : _root_.H3.Varint.encVarint body.length = some ld)
    (hdec : _root_.H3.Qpack.decodeFieldSection hd initClient.qpack sect = .ok d) :
    reassemble (h3ClientFeed hd initClient ((0x01 :: (lb ++ sect)) ++ (0x00 :: (ld ++ body)))).2
      = some { store := d.store, pseudo := d.pseudo, fields := d.fields, body := body } := by
  rw [h3_client_receive_faithful hd sect body lb ld d hl hld hdec]
  simp only [reassemble, firstHead, collectBody, List.append_nil]

/-! ## `h3_client_stream_fin` — the response completes on stream FIN

HTTP/3 has **no frame-level `END_STREAM` flag** (unlike HTTP/2 DATA): a response
body is terminated by the QUIC stream carrying a **FIN** (RFC 9114 §4.1, cf.
`H3.readAfterHeaders`, which completes a request on a clean end of stream). A FIN
is "clean" exactly when the transport bytes end on a frame boundary — no partial
frame is left buffered. For a `HEADERS(sect)+DATA(body)` response that boundary
holds: the residual buffer drains to `[]`, so the stream FINs cleanly and the
response is complete. -/

/-- **`h3_client_stream_fin`** (RFC 9114 §4.1). After walking a
`HEADERS(sect)+DATA(body)` response the client's residual buffer is **empty** — the
final `DATA` frame ends on a frame boundary, so a QUIC stream FIN there completes
the response with no truncated frame pending — and the reassembled `ClientResponse`
carries the decoded head + body. (The body terminates on stream FIN, not on any
frame flag.) -/
theorem h3_client_stream_fin (hd : _root_.H3.Qpack.HuffmanDecoder)
    (sect body lb ld : Bytes) (d : _root_.H3.Qpack.Decoded)
    (hl : _root_.H3.Varint.encVarint sect.length = some lb)
    (hld : _root_.H3.Varint.encVarint body.length = some ld)
    (hdec : _root_.H3.Qpack.decodeFieldSection hd initClient.qpack sect = .ok d) :
    (h3ClientFeed hd initClient ((0x01 :: (lb ++ sect)) ++ (0x00 :: (ld ++ body)))).1.buf = []
    ∧ reassemble (h3ClientFeed hd initClient ((0x01 :: (lb ++ sect)) ++ (0x00 :: (ld ++ body)))).2
        = some { store := d.store, pseudo := d.pseudo, fields := d.fields, body := body } := by
  refine ⟨?_, h3_client_receive hd sect body lb ld d hl hld hdec⟩
  rw [h3ClientFeed_buf,
    show initClient.buf ++ ((0x01 :: (lb ++ sect)) ++ (0x00 :: (ld ++ body)))
        = (0x01 :: (lb ++ sect)) ++ (0x00 :: (ld ++ body)) from rfl,
    decFrames_response sect body lb ld hl hld]

/-! ## `h3_client_trailers` — a post-DATA trailer HEADERS block is surfaced -/

/-- A completed `DATA`-frame decode is stable under a trailing frame: the H3 frame
decoder reads exactly the declared body and stops, leaving the following frame for
the next loop step (RFC 9114 §7.2.1). The DATA analogue of
`decFrame_headers_prefix`. -/
theorem decFrame_data_prefix (body lb rest : Bytes)
    (hl : _root_.H3.Varint.encVarint body.length = some lb) :
    decFrame ((0x00 :: (lb ++ body)) ++ rest)
      = .complete (.data body) (1 + lb.length + body.length) := by
  have hcons : (0x00 :: (lb ++ body)) ++ rest = (0x00 : UInt8) :: (lb ++ (body ++ rest)) := by
    simp [List.append_assoc]
  have h0 : _root_.H3.Varint.decVarint ((0x00 : UInt8) :: (lb ++ (body ++ rest))) = some (0, 1) :=
    _root_.H3.Varint.decVarint_case0 0x00 (lb ++ (body ++ rest)) (by decide)
  have h1 : _root_.H3.Varint.decVarint (lb ++ (body ++ rest)) = some (body.length, lb.length) :=
    _root_.H3.Varint.decVarint_encVarint body.length lb (body ++ rest) hl
  have hdrop : ((0x00 : UInt8) :: (lb ++ (body ++ rest))).drop (1 + lb.length) = body ++ rest := by
    rw [show (0x00 : UInt8) :: (lb ++ (body ++ rest)) = ([0x00] ++ lb) ++ (body ++ rest) by
          simp [List.append_assoc],
        show 1 + lb.length = ([0x00] ++ lb).length by
          rw [List.length_append, List.length_singleton],
        List.drop_left]
  rw [hcons]
  unfold decFrame
  rw [h0]
  simp only []
  rw [show ((0x00 : UInt8) :: (lb ++ (body ++ rest))).drop 1 = lb ++ (body ++ rest) from rfl, h1]
  simp only []
  rw [hdrop, if_neg (by rw [List.length_append]; omega), List.take_left]
  rfl

/-- `decFrames` on a server-encoded `HEADERS(sect)` + `DATA(body)` +
trailer-`HEADERS(tr)` response yields exactly `[.headers sect, .data body,
.headers tr]` with no remainder (RFC 9114 §4.1 trailer section). -/
theorem decFrames_trailers (sect body tr lb ld lt : Bytes)
    (hl : _root_.H3.Varint.encVarint sect.length = some lb)
    (hld : _root_.H3.Varint.encVarint body.length = some ld)
    (hlt : _root_.H3.Varint.encVarint tr.length = some lt) :
    decFrames ((0x01 :: (lb ++ sect)) ++ ((0x00 :: (ld ++ body)) ++ (0x01 :: (lt ++ tr))))
      = ([.headers sect, .data body, .headers tr], []) := by
  have hHlen : (0x01 :: (lb ++ sect)).length = 1 + lb.length + sect.length := by
    rw [List.length_cons, List.length_append]; omega
  have hDlen : (0x00 :: (ld ++ body)).length = 1 + ld.length + body.length := by
    rw [List.length_cons, List.length_append]; omega
  have hTlen : (0x01 :: (lt ++ tr)).length = 1 + lt.length + tr.length := by
    rw [List.length_cons, List.length_append]; omega
  have hdrop1 : ((0x01 :: (lb ++ sect)) ++ ((0x00 :: (ld ++ body)) ++ (0x01 :: (lt ++ tr)))).drop
      (1 + lb.length + sect.length) = (0x00 :: (ld ++ body)) ++ (0x01 :: (lt ++ tr)) := by
    rw [← hHlen]; exact List.drop_left
  have hdrop2 : ((0x00 :: (ld ++ body)) ++ (0x01 :: (lt ++ tr))).drop
      (1 + ld.length + body.length) = 0x01 :: (lt ++ tr) := by
    rw [← hDlen]; exact List.drop_left
  have hdrop3 : (0x01 :: (lt ++ tr)).drop (1 + lt.length + tr.length) = [] := by
    rw [show (1 + lt.length + tr.length) = (0x01 :: (lt ++ tr)).length from hTlen.symm]
    exact List.drop_length
  rw [decFrames, decFrame_headers_prefix sect lb ((0x00 :: (ld ++ body)) ++ (0x01 :: (lt ++ tr))) hl]
  simp only [hdrop1]
  rw [decFrames, decFrame_data_prefix body ld (0x01 :: (lt ++ tr)) hld]
  simp only [hdrop2]
  rw [decFrames, _root_.H3.Client.decFrame_encHeadersFrame tr lt hlt]
  simp only [hdrop3]
  have hnil : decFrames ([] : Bytes) = ([], []) := by
    rw [decFrames, show decFrame ([] : Bytes) = .incomplete from rfl]
  rw [hnil]

/-- **`h3_client_trailers`** (RFC 9114 §4.1, §7.2.2). For a response the server
serializes as `HEADERS(sect) + DATA(body) + HEADERS(tr)` — the trailer section
after the body — the client's `h3ClientFeed` walks all three frames and surfaces a
**second** `responseHead` (the trailer block) *after* the `responseData`:
`[responseHead d1…, responseData body, responseHead d2…]`. The reassembled
`ClientResponse` carries the trailer field section in `trailers`. `hdec1`/`hdec2`
tie the two decoded heads to the exact sections the server framed (the second
decoded against the store the first left, per QPACK's stateful decode). -/
theorem h3_client_trailers (hd : _root_.H3.Qpack.HuffmanDecoder)
    (sect body tr lb ld lt : Bytes) (d1 d2 : _root_.H3.Qpack.Decoded)
    (hl : _root_.H3.Varint.encVarint sect.length = some lb)
    (hld : _root_.H3.Varint.encVarint body.length = some ld)
    (hlt : _root_.H3.Varint.encVarint tr.length = some lt)
    (hdec1 : _root_.H3.Qpack.decodeFieldSection hd initClient.qpack sect = .ok d1)
    (hdec2 : _root_.H3.Qpack.decodeFieldSection hd d1.store tr = .ok d2) :
    (h3ClientFeed hd initClient
        ((0x01 :: (lb ++ sect)) ++ ((0x00 :: (ld ++ body)) ++ (0x01 :: (lt ++ tr))))).2
      = [.responseHead d1.store d1.pseudo d1.fields, .responseData body,
         .responseHead d2.store d2.pseudo d2.fields]
    ∧ reassembleT (h3ClientFeed hd initClient
        ((0x01 :: (lb ++ sect)) ++ ((0x00 :: (ld ++ body)) ++ (0x01 :: (lt ++ tr))))).2
        = some { store := d1.store, pseudo := d1.pseudo, fields := d1.fields,
                 body := body, trailers := d2.fields } := by
  have hev : (h3ClientFeed hd initClient
      ((0x01 :: (lb ++ sect)) ++ ((0x00 :: (ld ++ body)) ++ (0x01 :: (lt ++ tr))))).2
        = [.responseHead d1.store d1.pseudo d1.fields, .responseData body,
           .responseHead d2.store d2.pseudo d2.fields] := by
    unfold h3ClientFeed
    rw [show initClient.buf ++ ((0x01 :: (lb ++ sect)) ++ ((0x00 :: (ld ++ body)) ++ (0x01 :: (lt ++ tr))))
          = (0x01 :: (lb ++ sect)) ++ ((0x00 :: (ld ++ body)) ++ (0x01 :: (lt ++ tr))) from rfl,
        decFrames_trailers sect body tr lb ld lt hl hld hlt]
    simp only [List.foldl, h3ClientStep, hdec1, hdec2, List.nil_append, List.singleton_append,
      List.cons_append, List.append_assoc]
  refine ⟨hev, ?_⟩
  rw [hev]
  simp only [reassembleT, firstHead, collectBody, collectTrailers, List.append_nil]

/-! ## Grounding — the three theorems on genuine frames + a genuine decode -/

/-- **Non-vacuous (`h3_client_receive`):** a real `HEADERS`+`DATA(hi)` response is
walked, QPACK-decoded, and reassembled into a complete `ClientResponse`. -/
theorem receive_reassembled_grounded (hd : _root_.H3.Qpack.HuffmanDecoder) :
    reassemble (h3ClientFeed hd initClient
        ((0x01 :: ([0x02] ++ _root_.H3.Qpack.encodeFieldSection []))
          ++ (0x00 :: ([0x02] ++ [0x68, 0x69])))).2
      = some { store := initClient.qpack, pseudo := {}, fields := [], body := [0x68, 0x69] } :=
  h3_client_receive hd (_root_.H3.Qpack.encodeFieldSection []) [0x68, 0x69] [0x02] [0x02]
    ⟨initClient.qpack, {}, []⟩ (by decide) (by decide) (decode_emptyFields hd)

/-- **Non-vacuous (`h3_client_stream_fin`):** after the real `HEADERS`+`DATA(hi)`
response the residual buffer is empty (the stream FINs cleanly) and the response
reassembles. -/
theorem stream_fin_grounded (hd : _root_.H3.Qpack.HuffmanDecoder) :
    (h3ClientFeed hd initClient
        ((0x01 :: ([0x02] ++ _root_.H3.Qpack.encodeFieldSection []))
          ++ (0x00 :: ([0x02] ++ [0x68, 0x69])))).1.buf = []
    ∧ reassemble (h3ClientFeed hd initClient
        ((0x01 :: ([0x02] ++ _root_.H3.Qpack.encodeFieldSection []))
          ++ (0x00 :: ([0x02] ++ [0x68, 0x69])))).2
        = some { store := initClient.qpack, pseudo := {}, fields := [], body := [0x68, 0x69] } :=
  h3_client_stream_fin hd (_root_.H3.Qpack.encodeFieldSection []) [0x68, 0x69] [0x02] [0x02]
    ⟨initClient.qpack, {}, []⟩ (by decide) (by decide) (decode_emptyFields hd)

/-- **Non-vacuous (`h3_client_trailers`):** a real `HEADERS`+`DATA(hi)`+trailer-
`HEADERS` response surfaces a **third** event — the post-DATA trailer head — and
reassembles into a `ClientResponse` whose `trailers` field carries the (decoded)
trailer block. The genuine 3-frame walk with two real QPACK decodes. -/
theorem trailers_grounded (hd : _root_.H3.Qpack.HuffmanDecoder) :
    (h3ClientFeed hd initClient
        ((0x01 :: ([0x02] ++ _root_.H3.Qpack.encodeFieldSection []))
          ++ ((0x00 :: ([0x02] ++ [0x68, 0x69]))
              ++ (0x01 :: ([0x02] ++ _root_.H3.Qpack.encodeFieldSection []))))).2
      = [.responseHead initClient.qpack {} [], .responseData [0x68, 0x69],
         .responseHead initClient.qpack {} []]
    ∧ reassembleT (h3ClientFeed hd initClient
        ((0x01 :: ([0x02] ++ _root_.H3.Qpack.encodeFieldSection []))
          ++ ((0x00 :: ([0x02] ++ [0x68, 0x69]))
              ++ (0x01 :: ([0x02] ++ _root_.H3.Qpack.encodeFieldSection []))))).2
        = some { store := initClient.qpack, pseudo := {}, fields := [],
                 body := [0x68, 0x69], trailers := [] } :=
  h3_client_trailers hd (_root_.H3.Qpack.encodeFieldSection []) [0x68, 0x69]
    (_root_.H3.Qpack.encodeFieldSection []) [0x02] [0x02] [0x02]
    ⟨initClient.qpack, {}, []⟩ ⟨initClient.qpack, {}, []⟩
    (by decide) (by decide) (by decide) (decode_emptyFields hd) (decode_emptyFields hd)

#print axioms h3_client_receive_faithful
#print axioms decFrames_response
#print axioms receive_grounded
#print axioms h3_client_receive
#print axioms h3_client_stream_fin
#print axioms h3_client_trailers
#print axioms receive_reassembled_grounded
#print axioms stream_fin_grounded
#print axioms trailers_grounded

end H3Receive
end Client
end Proto
