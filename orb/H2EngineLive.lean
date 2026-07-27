/-
# H2EngineLive — driving the PROVEN H2 frame/HPACK/stream engine over the byte level

The `H2` foundation models the HTTP/2 protocol engine as sans-IO, proven Lean:

  * the **frame codec** (`H2.Frame.decode` / `H2.FrameEncode.encodeFrame`): the
    9-octet frame header (RFC 9113 §4.1), the frame taxonomy (§6), and the
    encode/decode round-trip `decode (encodeFrame f) mfs = .complete f …`
    (`decode_encode_frame`);
  * the **HPACK codec** (`H2.HpackEncode.encodeHeaders` /
    `H2.HpackEncode.decodeHeadersV`): a header list laid onto the wire as HPACK
    literal-without-indexing fields and recovered verbatim through the deployed
    field decoder (`hpack_decode_encode`, RFC 7541);
  * the **per-stream FSM** (`H2.Stream.step`): the total deterministic RFC 9113
    §5.1 transition, with the DATA-acceptance invariant
    (`recvData_accepted_legal`).

This layer is proven but **inert** beyond the deployed h2c path: nothing drives
the frame codec + HPACK codec + stream FSM together over real bytes in one
process. This lane isolates that inert, format-agnostic engine and drives the
WHOLE chain — encode a frame, decode it back; encode a header block, decode it
back through the deployed field decoder; run a stream through its FSM — with
**no crypto whatsoever**, so it runs under `lake env lean --run`.

## Honesty / realization boundary (the NetmapLive / DnsResolveLive discipline)

This is **drorb-native** and **pure**: the encoder and the decoder are our own
spec-conformant peers speaking the modelled HTTP/2 framing + HPACK (NOT a TLS/ALPN
`h2` session, NOT real curl/nghttp2 interop, which additionally needs the TLS
handshake and the Huffman table — the named residual). No socket, no FFI call:
the reused C objects are linked only to satisfy the shared executable link line
and are never invoked (calling crypto FFI would crash the pure-Lean interpreter).
Everything structural/codec here is the proven Lean; the gap the selftest
discharges by construction (not by proof) is that this exe faithfully CALLS the
proven Lean functions on real bytes. The faithfulness of the
frame-roundtrip + hpack-roundtrip + FSM-transition chain ITSELF is proven below
as `h2_engine_faithful`.

Usage:
  h2-engine-live selftest
-/
import H2.FrameEncode
import H2.HpackEncode
import H2.Stream

namespace H2EngineLive

open H2 H2.FrameEncode H2.HpackEncode H2.Stream

/-! ## §1  The faithfulness theorem

The running engine's three codec/FSM steps apply EXACTLY the proven decision:

* **frame** — for any `Frame f` whose stream id is a 31-bit value and whose
  payload fits `2^24` and the peer's `maxFrameSize` (an unknown type additionally
  classifying as unknown), decoding its encoding recovers the frame exactly
  (`decode_encode_frame`);
* **hpack** — for any header list whose names/values fit the 7-bit length prefix,
  decoding its HPACK encoding through the deployed field decoder returns the list
  (`hpack_decode_encode`);
* **stream** — a `recvData` event accepted by the per-stream step was taken from
  a state whose remote half is still open — `open` or `halfClosedLocal`
  (`recvData_accepted_legal`): DATA is never delivered to a remote-closed stream.

Not a `P → P`: the conclusion is three substantive equations/invariants over the
proven engine, each with real hypotheses (side conditions on the frame, the
7-bit small-field bound, the fuel bound, and a genuine FSM step). Inhabited: the
`example`s below instantiate it on concrete bytes, and the selftest witnesses
every conjunct on real wire octets. -/
theorem h2_engine_faithful
    -- frame side
    (f : Frame) (mfs : Nat)
    (hsid : encStreamId f < 2 ^ 31) (hlen : encPayloadLen f < 2 ^ 24)
    (hmfs : encPayloadLen f ≤ mfs)
    (hunk : ∀ t s l, f = .unknown t s l → isKnownType t = false ∧ t < 256)
    -- hpack side
    (hd : Hpack.HuffmanDecoder) (tbl : List Conn.DynEntry)
    (hs : List (Bytes × Bytes)) (fuel : Nat)
    (hsmall : ∀ p ∈ hs, p.1.length < 127 ∧ p.2.length < 127)
    (hfuel : hs.length < fuel)
    -- stream side
    (s s' : StreamState) (b : Bool) (hstep : step s (.recvData b) = .next s') :
    decode (encodeFrame f) mfs = .complete f (9 + encPayloadLen f)
      ∧ decodeHeadersV hd tbl fuel (encodeHeaders hs) [] = .ok hs
      ∧ (s = .open ∨ s = .halfClosedLocal) :=
  ⟨decode_encode_frame f mfs hsid hlen hmfs hunk,
   hpack_decode_encode hd tbl hs fuel hsmall hfuel,
   recvData_accepted_legal s s' b hstep⟩

/-! ### The three conjuncts, standalone (for reuse and grounding) -/

/-- **Frame codec round-trip** — decode inverts encode for a within-limit frame. -/
theorem h2_frame_roundtrip (f : Frame) (mfs : Nat)
    (hsid : encStreamId f < 2 ^ 31) (hlen : encPayloadLen f < 2 ^ 24)
    (hmfs : encPayloadLen f ≤ mfs)
    (hunk : ∀ t s l, f = .unknown t s l → isKnownType t = false ∧ t < 256) :
    decode (encodeFrame f) mfs = .complete f (9 + encPayloadLen f) :=
  decode_encode_frame f mfs hsid hlen hmfs hunk

/-- **HPACK codec round-trip** — the deployed field decoder recovers any
small-field header list from its encoding. -/
theorem h2_hpack_roundtrip (hd : Hpack.HuffmanDecoder) (tbl : List Conn.DynEntry)
    (hs : List (Bytes × Bytes)) (fuel : Nat)
    (hsmall : ∀ p ∈ hs, p.1.length < 127 ∧ p.2.length < 127)
    (hfuel : hs.length < fuel) :
    decodeHeadersV hd tbl fuel (encodeHeaders hs) [] = .ok hs :=
  hpack_decode_encode hd tbl hs fuel hsmall hfuel

/-- **Stream FSM valid-transition invariant** — an accepted `recvData` was taken
from a state whose remote half is open. -/
theorem h2_stream_recvData_legal (s s' : StreamState) (b : Bool)
    (hstep : step s (.recvData b) = .next s') :
    s = .open ∨ s = .halfClosedLocal :=
  recvData_accepted_legal s s' b hstep

/-! ### Concrete instantiations — the theorem is inhabited (not vacuous) -/

/-- A DATA frame on stream 1 (`END_STREAM` set) round-trips. -/
example : decode (encodeFrame (.data 1 true [0xaa, 0xbb, 0xcc])) 16384
    = .complete (.data 1 true [0xaa, 0xbb, 0xcc]) 12 :=
  h2_frame_roundtrip (.data 1 true [0xaa, 0xbb, 0xcc]) 16384
    (by decide) (by decide) (by decide) (by intro t s l h; cases h)

/-- A realistic request header list round-trips through the deployed decoder. -/
example : decodeHeadersV ⟨fun _ => none⟩ [] 8
    (encodeHeaders [([0x3a, 0x6d], [0x47]), ([0x68], [0x61])]) []
    = .ok [([0x3a, 0x6d], [0x47]), ([0x68], [0x61])] :=
  h2_hpack_roundtrip ⟨fun _ => none⟩ [] [([0x3a, 0x6d], [0x47]), ([0x68], [0x61])] 8
    (by decide) (by decide)

/-- `open + recvData` is accepted only because `open`'s remote half is open. -/
example (b : Bool) : (StreamState.open = .open ∨ StreamState.open = .halfClosedLocal) :=
  h2_stream_recvData_legal .open (if b then .halfClosedRemote else .open) b (by cases b <;> rfl)

/-! ## §2  Byte helpers (pure; mirrors NetmapLive) -/

def toHex (b : ByteArray) : String :=
  let d := "0123456789abcdef".toList.toArray
  b.toList.foldl (fun s x => s ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

def toHexL (b : Bytes) : String := toHex ⟨b.toArray⟩

/-- Render a byte list that is UTF-8 text as text, else hex. -/
def textOrHex (b : Bytes) : String := (String.fromUTF8? ⟨b.toArray⟩).getD (toHexL b)

/-- The always-reject Huffman decoder: the encoder never sets the Huffman flag,
so it is never consulted (no crypto, no table). -/
def rejectHuffman : Hpack.HuffmanDecoder := ⟨fun _ => none⟩

/-- The frame taxonomy label, for the report. -/
def frameLabel : Frame → String
  | .data _ _ _ => "DATA"
  | .headers _ _ _ _ => "HEADERS"
  | .priority _ _ => "PRIORITY"
  | .rstStream _ _ => "RST_STREAM"
  | .settings _ _ _ => "SETTINGS"
  | .pushPromise _ _ => "PUSH_PROMISE"
  | .ping _ _ _ => "PING"
  | .goaway _ _ => "GOAWAY"
  | .windowUpdate _ _ => "WINDOW_UPDATE"
  | .continuation _ _ _ => "CONTINUATION"
  | .unknown t _ _ => s!"UNKNOWN(0x{t})"

def stateLabel : StreamState → String
  | .idle => "idle"
  | .reservedLocal => "reservedLocal"
  | .reservedRemote => "reservedRemote"
  | .open => "open"
  | .halfClosedLocal => "halfClosedLocal"
  | .halfClosedRemote => "halfClosedRemote"
  | .closed => "closed"

/-! ## §3  The selftest — the H2 engine over the byte level, one process, NO crypto -/

def selftest : IO UInt32 := do
  IO.println "== h2-engine-live selftest : H2 frame/HPACK/stream engine, byte-level, NO crypto =="

  -- ── (a) FRAME CODEC: encode a batch of frames, decode each back ──
  IO.println s!"\n-- (a) frame codec : encode → decode round-trip --"
  let frames : List Frame :=
    [ .data 1 true [0xaa, 0xbb, 0xcc]
    , .headers 3 false true [0x82, 0x86]
    , .windowUpdate 1 [0x00, 0x00, 0x00, 0x40]
    , .ping 0 true [1, 2, 3, 4, 5, 6, 7, 8]
    , .rstStream 5 [0x00, 0x00, 0x00, 0x08]
    , .goaway 0 [0, 0, 0, 3, 0, 0, 0, 0]
    , .settings 0 false [] ]
  let mfs := 16384
  let mut frameOk := true
  for f in frames do
    let wire := encodeFrame f
    match decode wire mfs with
    | .complete f' n =>
      let ok := (f' == f) && (n == 9 + encPayloadLen f)
      frameOk := frameOk && ok
      IO.println s!"  {frameLabel f} : {wire.length}B  {toHexL (wire.take 12)}…  decode→ consumed {n}  match={ok}"
    | _ =>
      frameOk := false
      IO.eprintln s!"  {frameLabel f} : decode did NOT complete"
  IO.println s!"all frames round-tripped (decode∘encode = id)     : {frameOk}"

  -- ── (b) HPACK CODEC: encode a request header block, decode it back ──
  IO.println s!"\n-- (b) HPACK codec : encode → decode through the deployed field decoder --"
  let reqHeaders : List (Bytes × Bytes) :=
    [ ("!method".toUTF8.toList.set 0 0x3a, "GET".toUTF8.toList)     -- ":method" "GET"
    , ("!scheme".toUTF8.toList.set 0 0x3a, "https".toUTF8.toList)   -- ":scheme" "https"
    , ("!path".toUTF8.toList.set 0 0x3a, "/".toUTF8.toList)         -- ":path" "/"
    , ("host".toUTF8.toList, "a".toUTF8.toList) ]
  let hblock := encodeHeaders reqHeaders
  IO.println s!"  HPACK block : {hblock.length}B  {toHexL (hblock.take 16)}…"
  let hpackOk ←
    match decodeHeadersV rejectHuffman [] 32 hblock [] with
    | .ok decoded =>
      let ok := decoded == reqHeaders
      for (n, v) in decoded do
        IO.println s!"    field  {textOrHex n} : {textOrHex v}"
      pure ok
    | .error _ => do IO.eprintln "  HPACK decode FAILED"; pure false
  IO.println s!"header block round-tripped (decode∘encode = id)    : {hpackOk}"

  -- ── (c) STREAM FSM: drive a stream through a legal trajectory ──
  IO.println s!"\n-- (c) per-stream FSM : a request/response trajectory --"
  -- idle → (recvHeaders, no END_STREAM) open → (recvData END_STREAM) halfClosedRemote
  --      → (sendHeaders) halfClosedRemote → (sendData END_STREAM) closed
  let events : List Event :=
    [ .recvHeaders false, .recvData true, .sendHeaders false, .sendData true ]
  let mut st : StreamState := .idle
  IO.println s!"  start                         : {stateLabel st}"
  let mut fsmOk := true
  for e in events do
    match step st e with
    | .next st' =>
      IO.println s!"  {reprStr e} → {stateLabel st'}"
      st := st'
    | .streamClosed => fsmOk := false; IO.eprintln s!"  {reprStr e} → STREAM_CLOSED (unexpected)"
    | .protocolError => fsmOk := false; IO.eprintln s!"  {reprStr e} → PROTOCOL_ERROR (unexpected)"
  let endedClosed := st == .closed
  IO.println s!"trajectory reached closed                          : {endedClosed}"
  -- the safety invariant, byte-level: DATA into a remote-closed stream is refused
  let dataRefused := step .halfClosedRemote (.recvData false) == .streamClosed
  let closedAbsorbing := run .closed events == .closed
  IO.println s!"DATA into halfClosedRemote is STREAM_CLOSED        : {dataRefused}"
  IO.println s!"closed is absorbing over the whole event run       : {closedAbsorbing}"
  fsmOk := fsmOk && endedClosed && dataRefused && closedAbsorbing

  -- ── the faithfulness cross-check: witness `h2_engine_faithful` on concrete bytes ──
  IO.println s!"\n-- cross-check (realizes h2_engine_faithful) --"
  IO.println s!"frame roundtrip conjunct   : {frameOk}"
  IO.println s!"hpack roundtrip conjunct   : {hpackOk}"
  IO.println s!"stream FSM conjunct        : {fsmOk}"

  if frameOk && hpackOk && fsmOk then do
    IO.println "\nPASS — frames encoded+decoded; HPACK block encoded+decoded through the deployed"
    IO.println "       field decoder; stream driven through a legal FSM trajectory to closed;"
    IO.println "       the encode→decode + FSM chain equals the proven engine decision."
    IO.println "H2 ENGINE LIVE-WIRED (drorb-native, byte-level, NO crypto, verified codec+FSM)."
    return 0
  else do
    IO.eprintln "\nFAIL — a stage of the H2 engine pipeline did not cross-check."
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | _ => do
    IO.eprintln "usage: h2-engine-live selftest"
    return 1

end H2EngineLive

def main (args : List String) : IO UInt32 := H2EngineLive.main args
