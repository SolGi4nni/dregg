import H2.Frame
import H2.Hpack
import H2.Stream
import H2.Ext

/-!
# H2.Conn — the HTTP/2 connection engine (RFC 9113 + RFC 7541)

`H2/Frame.lean` decodes single frames, `H2/Hpack.lean` decodes header blocks,
`H2/Stream.lean` steps one stream's FSM. This module composes them into the
**connection-level** engine RFC 9113 actually specifies: a total transition
function

```
feed : HuffmanDecoder → Handler → ConnState → Bytes → ConnState × Bytes × Bool
```

that consumes raw transport bytes (any split), validates the client connection
preface (§3.4), walks whole frames as they complete, enforces the per-type
payload rules the frame layer deliberately deferred (§4.1–§6.10), assembles
CONTINUATION header blocks (§4.3, §6.10), decodes them through HPACK **with a
real decode-side dynamic table** (RFC 7541 §2.3.2/§4/§6.3 — insertion,
eviction, size updates with the position and bound rules), runs the per-stream
FSM, answers control frames (SETTINGS ACK §6.5.3, PING ACK §6.7), paces
response DATA under both flow-control windows (§5.2, §6.9), and surfaces every
error as the frame RFC 9113 §5.4 prescribes — `GOAWAY(code)` for connection
errors, `RST_STREAM(code)` for stream errors — with a close flag instead of a
torn socket.

The application is a parameter: `Handler` maps a validated request head to a
pre-encoded HPACK response block plus a body; the engine owns every
wire-protocol decision, the handler owns none of them.

## Behavior theorems

Each closes a named RFC obligation as a statement about `feed`/`handleFrame`
on the *engine's own* transition function (not a side model):

* `feed_ping_ack` (§6.7): a well-formed PING is answered by a PING ACK carrying
  the same 8 opaque octets, and the connection stays open.
* `feed_settings_ack` (§6.5.3): a SETTINGS frame (no ACK flag) is acknowledged
  — shown for the empty frame on a stream-less connection;
  `applySettings_initialWindow_last` adds the §6.5.3 last-value-wins rule for
  repeated `SETTINGS_INITIAL_WINDOW_SIZE` values.
* `feed_unknown_ignored` (§4.1/§5.5): a complete frame of unknown type produces
  no output, no close, and no stream-table change — ignored, not fatal.
* `feed_preface_invalid` (§3.4): a connection whose first octets differ from
  the client preface is refused with `GOAWAY(PROTOCOL_ERROR)` and closed.
* `feed_oversize_goaway` (§4.2): a frame whose declared length exceeds
  `SETTINGS_MAX_FRAME_SIZE` is refused with `GOAWAY(FRAME_SIZE_ERROR)`.
* `feed_hpack_error_goaway` (§4.3): a HEADERS frame whose block fails HPACK
  decoding is refused with `GOAWAY(COMPRESSION_ERROR)`.
* `sendChunks_*` (§6.9): the DATA pacer never emits beyond either window,
  never loses bytes (emitted + parked = offered), and parks everything when
  there is no credit — the engine-level image of `H2.FlowControl`.
-/

namespace H2
namespace Conn

/-! ## RFC 9113 §7 error codes -/

def errProtocol : Nat := 0x1
def errFlowControl : Nat := 0x3
def errStreamClosed : Nat := 0x5
def errFrameSize : Nat := 0x6
def errRefusedStream : Nat := 0x7
def errCompression : Nat := 0x9

/-! ## Our advertised limits (our SETTINGS declares the concurrency cap;
everything else stays at the RFC defaults) -/

/-- Our `SETTINGS_MAX_FRAME_SIZE` (RFC 9113 §4.2 default). -/
def ourMaxFrameSize : Nat := 16384

/-- Our `SETTINGS_HEADER_TABLE_SIZE` (RFC 7541 §6.3 bound on peer size
updates; RFC 9113 §6.5.2 default). -/
def ourHeaderTableSize : Nat := 4096

/-- Our `SETTINGS_MAX_CONCURRENT_STREAMS` (RFC 9113 §6.5.2, identifier 0x3):
the peer may hold at most this many streams out of the `closed` state at once.
Advertised in `serverSettings` and enforced at stream open (§5.1.2) — the
stream over the limit is refused with `RST_STREAM(REFUSED_STREAM)` (§5.4.2). -/
def ourMaxConcurrentStreams : Nat := 100

/-- The flow-control window cap (RFC 9113 §6.9.1). -/
def maxWindow : Int := 2 ^ 31 - 1

/-- The 24-octet client connection preface `PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n`
(RFC 9113 §3.4). -/
def clientPreface : Bytes :=
  [0x50, 0x52, 0x49, 0x20, 0x2a, 0x20, 0x48, 0x54,
   0x54, 0x50, 0x2f, 0x32, 0x2e, 0x30, 0x0d, 0x0a,
   0x0d, 0x0a, 0x53, 0x4d, 0x0d, 0x0a, 0x0d, 0x0a]

theorem clientPreface_length : clientPreface.length = 24 := rfl

/-! ## Wire encoders (the engine's outbound frames) -/

/-- Big-endian 16-bit. -/
def be16 (n : Nat) : Bytes := [UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)]

/-- Big-endian 24-bit (frame length field). -/
def be24 (n : Nat) : Bytes :=
  [UInt8.ofNat (n / 65536 % 256), UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)]

/-- Big-endian 32-bit. -/
def be32 (n : Nat) : Bytes :=
  [UInt8.ofNat (n / 16777216 % 256), UInt8.ofNat (n / 65536 % 256),
   UInt8.ofNat (n / 256 % 256), UInt8.ofNat (n % 256)]

/-- A 9-octet frame header (RFC 9113 §4.1); the stream id is masked to 31
bits (reserved bit clear on send). -/
def frameHdr (len ty fl sid : Nat) : Bytes :=
  be24 len ++ [UInt8.ofNat ty, UInt8.ofNat fl] ++ be32 (sid % 2 ^ 31)

/-- The server connection preface (§3.4/§6.5): a SETTINGS frame advertising
`SETTINGS_MAX_CONCURRENT_STREAMS` (identifier 0x3, one 6-octet entry, §6.5.1) —
the one non-default limit we declare, enforced at stream open (§5.1.2). -/
def serverSettings : Bytes :=
  frameHdr 6 0x4 0 0 ++ be16 0x3 ++ be32 ourMaxConcurrentStreams

/-- A SETTINGS ACK (§6.5.3). -/
def settingsAckFrame : Bytes := frameHdr 0 0x4 0x1 0

/-- A PING ACK carrying the peer's 8 opaque octets back (§6.7). -/
def pingAckFrame (data : Bytes) : Bytes := frameHdr 8 0x6 0x1 0 ++ data.take 8

/-- A GOAWAY on stream 0: last processed stream id + error code (§6.8). -/
def goawayFrame (lastSid code : Nat) : Bytes :=
  frameHdr 8 0x7 0 0 ++ be32 (lastSid % 2 ^ 31) ++ be32 code

/-- An RST_STREAM carrying an error code (§6.4). -/
def rstStreamFrame (sid code : Nat) : Bytes := frameHdr 4 0x3 0 sid ++ be32 code

/-- A response HEADERS frame: `END_HEADERS` set, `END_STREAM` clear (a DATA
frame always follows), carrying a pre-encoded HPACK block (§6.2). -/
def headersFrame (sid : Nat) (block : Bytes) : Bytes :=
  frameHdr block.length 0x1 0x4 sid ++ block

/-- A response DATA frame (§6.1). -/
def dataFrame (sid : Nat) (endStream : Bool) (body : Bytes) : Bytes :=
  frameHdr body.length 0x0 (if endStream then 0x1 else 0x0) sid ++ body

/-- Read a big-endian 32-bit word off the head of a payload (0 if short). -/
def readU32 : Bytes → Nat
  | a :: b :: c :: d :: _ =>
    a.toNat * 16777216 + b.toNat * 65536 + c.toNat * 256 + d.toNat
  | _ => 0

/-! ## The HPACK decode-side dynamic table (RFC 7541 §2.3.2, §4) -/

/-- One dynamic-table entry: name and value bytes. -/
abbrev DynEntry := Bytes × Bytes

/-- RFC 7541 §4.1: the size of an entry is name length + value length + 32. -/
def entrySize (e : DynEntry) : Nat := e.1.length + e.2.length + 32

/-- The total size of the dynamic table (§4.1). -/
def tblSize (tbl : List DynEntry) : Nat := tbl.foldl (fun a e => a + entrySize e) 0

/-- Evict oldest entries (the list tail) until the table fits `cap` (§4.3). -/
def trimTable : Nat → Nat → List DynEntry → List DynEntry
  | 0, _, _ => []
  | fuel + 1, cap, tbl =>
    if tblSize tbl ≤ cap then tbl else trimTable fuel cap tbl.dropLast

/-- Insert a new entry at the head of the table, evicting from the tail to
make room (§4.4). An entry larger than the whole table clears it and is not
inserted. -/
def insertEntry (cap : Nat) (tbl : List DynEntry) (e : DynEntry) : List DynEntry :=
  if cap < entrySize e then []
  else e :: trimTable (tbl.length + 1) (cap - entrySize e) tbl

/-- The decode-side HPACK context: the dynamic table and its current maximum
size (starts at our `SETTINGS_HEADER_TABLE_SIZE`; lowered/raised by §6.3 size
updates, never above our advertised bound). -/
structure HpackCtx where
  tbl : List DynEntry := []
  cap : Nat := 4096
deriving Repr, DecidableEq

/-- Resolve a header-field index against the address space of §2.3.3: index 0
is invalid, 1–61 the static table, 62+ the dynamic table (most recent first). -/
def tableEntry (tbl : List DynEntry) (idx : Nat) : Option DynEntry :=
  if idx = 0 then none
  else if idx ≤ 61 then
    (Hpack.staticEntry idx).map fun nv => (Hpack.strBytes nv.1, Hpack.strBytes nv.2)
  else tbl[idx - 62]?

/-! ## Decoding one field representation (RFC 7541 §6) -/

/-- One decoded field-representation step: a field line (with the §6.2.1
incremental-indexing insert flag), or a §6.3 dynamic-table size update. -/
inductive FieldStep where
  | fld (name value : Bytes) (insert : Bool)
  | sizeUpdate (newMax : Nat)
deriving Repr

/-- Decode the literal-field tail shared by §6.2.1/§6.2.2/§6.2.3: a name
(literal when `idx = 0`, table reference otherwise) then a literal value. -/
def litField (hd : Hpack.HuffmanDecoder) (tbl : List DynEntry) (idx : Nat)
    (body : Bytes) (base : Nat) (ins : Bool) :
    Except Hpack.Err (FieldStep × Nat) :=
  if idx = 0 then
    match Hpack.readStr hd body with
    | .error e => .error e
    | .ok (name, nm) =>
      match Hpack.readStr hd (body.drop nm) with
      | .error e => .error e
      | .ok (value, vm) => .ok (.fld name value ins, base + nm + vm)
  else
    match tableEntry tbl idx with
    | none => .error .staticIndex
    | some (name, _) =>
      match Hpack.readStr hd body with
      | .error e => .error e
      | .ok (value, vm) => .ok (.fld name value ins, base + vm)

/-- Decode one field representation off the head of `bs` (§6.1–§6.3),
resolving indices against the static + dynamic tables. -/
def decodeFieldV (hd : Hpack.HuffmanDecoder) (tbl : List DynEntry) :
    Bytes → Except Hpack.Err (FieldStep × Nat)
  | [] => .error .truncated
  | b :: rest =>
    if 0x80 ≤ b.toNat then
      -- Indexed header field (§6.1)
      match Hpack.decPrefixInt 7 b rest with
      | none => .error .truncated
      | some (idx, n) =>
        match tableEntry tbl idx with
        | some (name, value) => .ok (.fld name value false, 1 + n)
        | none => .error (if idx = 0 then .invalidIndex else .staticIndex)
    else if 0x40 ≤ b.toNat then
      -- Literal with incremental indexing (§6.2.1)
      match Hpack.decPrefixInt 6 b rest with
      | none => .error .truncated
      | some (idx, n) => litField hd tbl idx (rest.drop n) (1 + n) true
    else if 0x20 ≤ b.toNat then
      -- Dynamic table size update (§6.3)
      match Hpack.decPrefixInt 5 b rest with
      | none => .error .truncated
      | some (v, n) => .ok (.sizeUpdate v, 1 + n)
    else
      -- Literal without indexing / never indexed (§6.2.2/§6.2.3)
      match Hpack.decPrefixInt 4 b rest with
      | none => .error .truncated
      | some (idx, n) => litField hd tbl idx (rest.drop n) (1 + n) false

/-! ## Decoding + validating a whole request header block -/

/-- A decoded request head: routed pseudo-header values, regular fields in wire
order, and the §8.3 malformedness evidence the block decode gathered. -/
structure Head where
  method : Option Bytes := none
  path : Option Bytes := none
  scheme : Option Bytes := none
  authority : Option Bytes := none
  fields : List (Bytes × Bytes) := []
  /-- A pseudo-header appeared twice (RFC 9113 §8.3). -/
  dup : Bool := false
  /-- A pseudo-header appeared after a regular field (RFC 9113 §8.3). -/
  pseudoLate : Bool := false
  /-- Any request pseudo-header appeared at all (trailer validation §8.1). -/
  hasPseudo : Bool := false
deriving Repr

def strBytes (s : String) : Bytes := (String.toUTF8 s).toList

/-- Route one decoded field into the head. Known request pseudo-headers fill
their slots (tracking §8.3 duplication/ordering); everything else — including
unknown pseudo-names and `:status` — stays a regular field for the §8.3
validator to inspect. -/
def Head.addField (h : Head) (sawReg : Bool) (name value : Bytes) : Head :=
  if name = strBytes ":method" then
    { h with
        method := some value
        dup := h.dup || h.method.isSome
        pseudoLate := h.pseudoLate || sawReg
        hasPseudo := true }
  else if name = strBytes ":path" then
    { h with
        path := some value
        dup := h.dup || h.path.isSome
        pseudoLate := h.pseudoLate || sawReg
        hasPseudo := true }
  else if name = strBytes ":scheme" then
    { h with
        scheme := some value
        dup := h.dup || h.scheme.isSome
        pseudoLate := h.pseudoLate || sawReg
        hasPseudo := true }
  else if name = strBytes ":authority" then
    { h with
        authority := some value
        dup := h.dup || h.authority.isSome
        pseudoLate := h.pseudoLate || sawReg
        hasPseudo := true }
  else
    { h with fields := (name, value) :: h.fields }

/-- Decode a whole header block: walk field representations, apply §6.2.1
inserts and §6.3 size updates to the dynamic table (a size update after any
field line, or above our advertised `SETTINGS_HEADER_TABLE_SIZE`, is a decode
error — RFC 7541 §4.2/§6.3), and gather the validation evidence. Fueled by the
block length (every representation consumes ≥ 1 octet). -/
def decodeBlockV (hd : Hpack.HuffmanDecoder) :
    Nat → HpackCtx → Bytes → Head → Bool → Bool →
    Except Hpack.Err (Head × HpackCtx)
  | 0, _, _, _, _, _ => .error .truncated
  | fuel + 1, ctx, bs, acc, sawReg, seenField =>
    match bs with
    | [] => .ok ({ acc with fields := acc.fields.reverse }, ctx)
    | b :: rest =>
      match decodeFieldV hd ctx.tbl (b :: rest) with
      | .error e => .error e
      | .ok (step, n) =>
        let n := max n 1
        match step with
        | .sizeUpdate v =>
          if seenField then .error .dynamicUnsupported
          else if ourHeaderTableSize < v then .error .dynamicUnsupported
          else
            decodeBlockV hd fuel
              { tbl := trimTable (ctx.tbl.length + 1) v ctx.tbl, cap := v }
              ((b :: rest).drop n) acc sawReg seenField
        | .fld name value ins =>
          let ctx := if ins then
              { ctx with tbl := insertEntry ctx.cap ctx.tbl (name, value) }
            else ctx
          let isPseudo := name.head? = some 0x3a
          decodeBlockV hd fuel ctx ((b :: rest).drop n)
            (acc.addField sawReg name value)
            (sawReg || !isPseudo) true

/-! ## §8.3 request-head validation -/

def hasUpper (bs : Bytes) : Bool := bs.any fun b => 0x41 ≤ b.toNat && b.toNat ≤ 0x5A

def isPseudoName (bs : Bytes) : Bool := bs.head? == some 0x3a

/-- Connection-specific header fields prohibited in HTTP/2 (RFC 9113 §8.2.2). -/
def connSpecific (n : Bytes) : Bool :=
  n == strBytes "connection" || n == strBytes "keep-alive" ||
  n == strBytes "proxy-connection" || n == strBytes "transfer-encoding" ||
  n == strBytes "upgrade"

/-- Parse a decimal byte string (`content-length`); `none` on empty or
non-digit input. -/
def decDigits? (bs : Bytes) : Option Nat :=
  if bs.isEmpty then none
  else bs.foldl (init := some 0) fun acc b =>
    match acc with
    | none => none
    | some v =>
      if 0x30 ≤ b.toNat && b.toNat ≤ 0x39 then some (v * 10 + (b.toNat - 0x30))
      else none

/-- RFC 9113 §8.3.1: is this request head malformed? Duplicated or late
pseudo-headers, a missing/mangled mandatory pseudo-header, an empty `:path`,
an unknown or response pseudo-header (left in `fields`), an uppercase field
name, a connection-specific field, or `te` other than `trailers`. -/
def headMalformed (h : Head) : Bool :=
  h.dup || h.pseudoLate
  || h.method.isNone || h.scheme.isNone || h.path.isNone
  || h.path.getD [] == []
  || h.fields.any fun f =>
       hasUpper f.1 || isPseudoName f.1 || connSpecific f.1
       || (f.1 == strBytes "te" && f.2 != strBytes "trailers")

/-- A trailer block is malformed if it carries any pseudo-header
(RFC 9113 §8.1) or any §8.3-prohibited regular field. -/
def trailersMalformed (h : Head) : Bool :=
  h.hasPseudo
  || h.fields.any fun f => hasUpper f.1 || isPseudoName f.1 || connSpecific f.1

/-- The declared `content-length` of a request head, when present and
well-formed (§8.1.1). -/
def declaredLen (h : Head) : Option Nat :=
  match h.fields.find? (fun f => f.1 == strBytes "content-length") with
  | some f => decDigits? f.2
  | none => none

/-! ## The application boundary -/

/-- A validated request the engine hands to the application. `raw` carries the
assembled header-block octets (the closest wire image of the request head) for
hosts whose middleware keys on raw input bytes. -/
structure Req where
  method : Bytes
  target : Bytes
  headers : List (Bytes × Bytes)
  raw : Bytes := []
  /-- The assembled request DATA body (§6.1), accumulated across DATA frames and
  handed to the handler at END_STREAM. Empty for bodyless requests. Additive:
  the engine's own protocol decisions never read it; only the application does. -/
  body : Bytes := []
deriving Repr

/-- The application's answer: a pre-encoded HPACK response header block and the
response body. The engine frames both (HEADERS + paced DATA). -/
structure Rsp where
  block : Bytes
  body : Bytes
  /-- The response `:status` code the handler chose, surfaced NUMERICALLY for
  the reporting seam (`ReqObs.status`). Observation only: the engine frames the
  response from `block`/`body` and never reads this field, so it cannot change
  a served byte. Defaults to `0` so existing handlers are unaffected. -/
  status : Nat := 0
  /-- Keep the stream OPEN after this response (a `MapRequest{Stream:true}`
  long-poll): the final DATA carries NO `END_STREAM`, the stream is left
  `halfClosedRemote`, and the server may push further DATA frames on it. Defaults
  `false` so every existing handler frames a normal one-shot response. -/
  keepOpen : Bool := false
deriving Repr

/-- The application boundary: the engine owns the protocol, the handler owns
the content. -/
abbrev Handler := Req → Rsp

/-! ## Per-stream and connection state -/

/-- Per-stream engine state: the §5.1 FSM state, our send window for the
stream (§5.2), any flow-blocked response body (§6.9 — parked, not dropped),
the completed request head awaiting `END_STREAM`, and the §8.1.1
content-length accounting. -/
structure StreamRec where
  state : Stream.StreamState := .idle
  window : Int := 65535
  pending : Bytes := []
  req : Option Req := none
  clen : Option Nat := none
  recvd : Nat := 0
  /-- The initial HEADERS block on this stream has completed (RFC 9113 §8.1
  trailer detection). -/
  initialHeaders : Bool := false
  /-- At least one DATA frame has arrived on this stream (RFC 9113 §8.1). -/
  dataSeen : Bool := false
  /-- The DATA octets received on this stream so far (§6.1), assembled in order
  so the completed request body can be handed to the handler. -/
  body : Bytes := []
  /-- The Extensible Priority (RFC 9218 §4) parsed from this stream's `priority`
  request header; the RFC 9218 §4 default when absent. -/
  priority : Ext.Priority := {}
deriving Repr

/-- An in-progress header block (§4.3): HEADERS arrived without `END_HEADERS`;
only CONTINUATION frames on the same stream may follow. -/
structure ContSt where
  sid : Nat
  endStream : Bool
  /-- `true` when the open block is a trailer block on an open stream. -/
  trailer : Bool
  frag : Bytes
deriving Repr

/-- One request/response pair the engine dispatched, recorded so a HOST can
itemise h2-over-TLS traffic WITHOUT decoding HPACK: the request method and
`:path`, the response `:status`, the response body octet count, and the stream
id. Every field is a value `respond` ALREADY computed. -/
structure ReqObs where
  method : Bytes
  path : Bytes
  status : Nat
  respBytes : Nat
  stream : Nat
deriving Repr

/-- The connection state. `prefaceLeft` counts unconsumed client-preface
octets; `buf` holds undecoded frame bytes across feeds; `maxSid` is the
highest client stream id seen (idle-stream detection, §5.1.1); `initWindow`
and `peerMaxFrame` mirror the peer's SETTINGS; `connWindow` is our
connection-level send window. -/
structure ConnState where
  prefaceLeft : Nat := 24
  buf : Bytes := []
  streams : List (Nat × StreamRec) := []
  maxSid : Nat := 0
  cont : Option ContSt := none
  hpack : HpackCtx := {}
  initWindow : Int := 65535
  peerMaxFrame : Nat := 16384
  connWindow : Int := 65535
  closed : Bool := false
  /-- Extension-surface events (ORIGIN §RFC 8336, ALT-SVC §RFC 7838, trailers
  §RFC 9113 §8.1) recognized on this connection, oldest first. The engine's
  transition shape (`ConnState × Bytes × Bool`) is unchanged; a host reads these
  off the successor state. -/
  events : List Ext.Event := []
  /-- Served request/response observations (`ReqObs`), oldest first. A PURE
  reporting surface with the same discipline as `events`: `respond` appends one
  per dispatched request, and a host reads the suffix new since the last `feed`
  off the successor state to emit per-request telemetry. The engine itself never
  reads them, so no protocol decision or output byte depends on this list. -/
  observations : List ReqObs := []
deriving Repr

def getStream (st : ConnState) (sid : Nat) : Option StreamRec :=
  (st.streams.find? (fun q => q.1 == sid)).map (·.2)

def setStream (st : ConnState) (sid : Nat) (sr : StreamRec) : ConnState :=
  { st with streams := (sid, sr) :: st.streams.filter (fun q => q.1 != sid) }

/-- One engine step's outcome: successor state, output octets, close flag. -/
abbrev Out := ConnState × Bytes × Bool

/-- A connection error (RFC 9113 §5.4.1): emit `GOAWAY(code)` carrying the
highest processed stream id, drop the rest of the input, and close. -/
def connError (st : ConnState) (code : Nat) : Out :=
  ({ st with closed := true, buf := [], cont := none },
   goawayFrame st.maxSid code, true)

/-- A stream error (RFC 9113 §5.4.2): emit `RST_STREAM(sid, code)`, mark the
stream closed, and keep the connection alive. -/
def streamError (st : ConnState) (sid : Nat) (code : Nat) : Out :=
  let sr := (getStream st sid).getD {}
  (setStream st sid { sr with state := .closed, pending := [], req := none },
   rstStreamFrame sid code, false)

/-- The number of streams the peer currently holds out of the `closed` state —
the §5.1.2 concurrency measure our advertised
`SETTINGS_MAX_CONCURRENT_STREAMS` bounds (a stream whose response is fully
written leaves the count; a flow-blocked stream with a parked body stays). -/
def activeStreams (st : ConnState) : Nat :=
  (st.streams.filter (fun q => match q.2.state with
    | .closed => false
    | _ => true)).length

/-! ## The DATA pacer (§5.2, §6.9) -/

/-- The sendable credit: the smaller of the two windows, floored at zero. -/
def credit (connW strW : Int) : Nat :=
  let c := min connW strW
  if c ≤ 0 then 0 else c.toNat

/-- Emit as much of `body` as both windows and the peer's
`SETTINGS_MAX_FRAME_SIZE` allow, as whole DATA frames; `END_STREAM` rides the
frame that exhausts the body. Returns (frames, parked remainder, connection
window, stream window). Fuel ≥ body.length + 1 always suffices (every emitted
frame carries ≥ 1 octet). -/
def sendChunks : Nat → Nat → Int → Int → Nat → Bytes → Bytes × Bytes × Int × Int
  | 0, _, cw, sw, _, body => ([], body, cw, sw)
  | fuel + 1, sid, cw, sw, mf, body =>
    if body.isEmpty then ([], [], cw, sw)
    else
      let n := min (min (credit cw sw) mf) body.length
      if n = 0 then ([], body, cw, sw)
      else
        let chunk := body.take n
        let rest := body.drop n
        let (fs, rem, cw', sw') := sendChunks fuel sid (cw - n) (sw - n) mf rest
        (dataFrame sid rest.isEmpty chunk ++ fs, rem, cw', sw')

/-- Like `sendChunks` but NEVER sets `END_STREAM`: the response body is paced as
DATA frames on a stream that STAYS OPEN (a `MapRequest{Stream:true}` long-poll —
the server keeps pushing further MapResponses on the same stream). Any
flow-blocked remainder parks exactly as in `sendChunks`. -/
def sendChunksOpen : Nat → Nat → Int → Int → Nat → Bytes → Bytes × Bytes × Int × Int
  | 0, _, cw, sw, _, body => ([], body, cw, sw)
  | fuel + 1, sid, cw, sw, mf, body =>
    if body.isEmpty then ([], [], cw, sw)
    else
      let n := min (min (credit cw sw) mf) body.length
      if n = 0 then ([], body, cw, sw)
      else
        let chunk := body.take n
        let rest := body.drop n
        let (fs, rem, cw', sw') := sendChunksOpen fuel sid (cw - n) (sw - n) mf rest
        (dataFrame sid false chunk ++ fs, rem, cw', sw')

/-- Flush a stream's parked response body under the current windows. -/
def flushStream (st : ConnState) (sid : Nat) : ConnState × Bytes :=
  match getStream st sid with
  | none => (st, [])
  | some sr =>
    if sr.pending.isEmpty then (st, [])
    else
      let (fs, rest, cw', sw') :=
        sendChunks (sr.pending.length + 1) sid st.connWindow sr.window
          st.peerMaxFrame sr.pending
      let sr' := { sr with
        pending := rest
        window := sw'
        state := if rest.isEmpty then .closed else sr.state }
      ({ setStream st sid sr' with connWindow := cw' }, fs)

/-- Flush every stream with a parked body (after a window grows). -/
def flushAll (st : ConnState) : ConnState × Bytes :=
  let sids := (st.streams.filter (fun q => !q.2.pending.isEmpty)).map (·.1)
  sids.foldl
    (fun acc sid =>
      let (st', o) := flushStream acc.1 sid
      (st', acc.2 ++ o))
    (st, [])

/-! ## Responding -/

/-- Answer a completed request on `sid`: run the handler, frame the response
HEADERS, and pace the body DATA under both windows. The stream closes when the
body is fully emitted; a flow-blocked remainder parks on the stream. -/
def respond (handler : Handler) (st : ConnState) (sid : Nat) (req : Req) : Out :=
  let rec0 := (getStream st sid).getD {}
  let rsp := handler req
  let hf := headersFrame sid rsp.block
  -- Observation only (see `ReqObs`): record what this dispatch decided on the
  -- successor state so a host can itemise it. Prepended-list accounting stays
  -- oldest-first; the served frames below are unchanged by this.
  let obs : ReqObs :=
    { method := req.method, path := req.target, status := rsp.status
      respBytes := rsp.body.length, stream := sid }
  let st := { st with observations := st.observations ++ [obs] }
  if rsp.body.isEmpty then
    (setStream st sid { rec0 with state := .closed, req := none, pending := [] },
     hf ++ dataFrame sid true [], false)
  else if rsp.keepOpen then
    -- §6 long-poll: pace the body with NO `END_STREAM`; the stream stays
    -- `halfClosedRemote` (the client already ended its request) so the server
    -- can push further MapResponse DATA frames on it (`sendChunksOpen`).
    let (fs, rest, cw', sw') :=
      sendChunksOpen (rsp.body.length + 1) sid st.connWindow rec0.window
        st.peerMaxFrame rsp.body
    let sr' := { rec0 with
      state := .halfClosedRemote
      pending := rest
      window := sw'
      req := none }
    ({ setStream st sid sr' with connWindow := cw' }, hf ++ fs, false)
  else
    let (fs, rest, cw', sw') :=
      sendChunks (rsp.body.length + 1) sid st.connWindow rec0.window
        st.peerMaxFrame rsp.body
    let sr' := { rec0 with
      state := if rest.isEmpty then .closed else .halfClosedRemote
      pending := rest
      window := sw'
      req := none }
    ({ setStream st sid sr' with connWindow := cw' }, hf ++ fs, false)

/-! ## Completing a header block -/

/-- A freshly opened stream record under the current peer settings. -/
def freshStream (st : ConnState) (endStream : Bool) : StreamRec :=
  { state := Stream.stepState .idle (.recvHeaders endStream)
    window := st.initWindow }

/-- Finish an initial request header block on `sid` (END_HEADERS seen):
HPACK-decode with the connection's dynamic table, validate per §8.3, and
either answer now (`END_STREAM`), park the request head awaiting the body, or
reset the stream. -/
def finishRequest (hd : Hpack.HuffmanDecoder) (handler : Handler)
    (st : ConnState) (sid : Nat) (es : Bool) (frag : Bytes) : Out :=
  match decodeBlockV hd (frag.length + 1) st.hpack frag {} false false with
  | .error _ => connError st errCompression
  | .ok (head, ctx) =>
    let st := { st with cont := none, hpack := ctx, maxSid := max st.maxSid sid }
    let st := setStream st sid (freshStream st es)
    if headMalformed head then streamError st sid errProtocol
    else
      let req : Req :=
        { method := head.method.getD []
          target := head.path.getD []
          headers := head.fields
          raw := frag }
      let clen := declaredLen head
      if es then
        if clen.getD 0 ≠ 0 then streamError st sid errProtocol
        else respond handler st sid req
      else
        let rec0 := (getStream st sid).getD {}
        -- RFC 9218 §4: parse the `priority` request header onto the stream.
        let prio := match head.fields.find? (fun f => f.1 == strBytes "priority") with
          | some f => Ext.parsePriority f.2
          | none => {}
        (setStream st sid
          { rec0 with req := some req, clen := clen, initialHeaders := true, priority := prio },
         [], false)

/-- Finish a trailer block on `sid` (§8.1): must end the stream, must carry no
pseudo-header; then the parked request is answered, checking the §8.1.1
content-length accounting. -/
def finishTrailers (hd : Hpack.HuffmanDecoder) (handler : Handler)
    (st : ConnState) (sid : Nat) (es : Bool) (frag : Bytes) : Out :=
  match decodeBlockV hd (frag.length + 1) st.hpack frag {} false false with
  | .error _ => connError st errCompression
  | .ok (head, ctx) =>
    let st := { st with cont := none, hpack := ctx }
    if !es then connError st errProtocol
    else
      match getStream st sid with
      | none => connError st errProtocol
      | some sr =>
        let st := setStream st sid
          { sr with state := Stream.stepState sr.state (.recvHeaders true) }
        if trailersMalformed head then streamError st sid errProtocol
        else
          match sr.req with
          | none => streamError st sid errProtocol
          | some req =>
            match sr.clen with
            | some n =>
              if n ≠ sr.recvd then streamError st sid errProtocol
              else respond handler st sid { req with body := sr.body }
            | none => respond handler st sid { req with body := sr.body }

/-! ## Per-frame handling (§6) -/

/-- Strip the PADDED layout (§6.1/§6.2): `padLen` octet first, padding last.
`none` when the pad length is missing or eats the whole payload. -/
def stripPadding (padded : Bool) (payload : Bytes) : Option Bytes :=
  if padded then
    match payload with
    | p :: rest =>
      if rest.length < p.toNat then none
      else some (rest.take (rest.length - p.toNat))
    | [] => none
  else some payload

/-- Parse SETTINGS payload into (identifier, value) pairs (§6.5.1). -/
def settingsPairs : Bytes → List (Nat × Nat)
  | a :: b :: c :: d :: e :: f :: rest =>
    (a.toNat * 256 + b.toNat,
     c.toNat * 16777216 + d.toNat * 65536 + e.toNat * 256 + f.toNat)
      :: settingsPairs rest
  | _ => []

/-- Apply SETTINGS values in order (last value wins, §6.5.3). Errors carry the
§6.5.2 error code. `SETTINGS_INITIAL_WINDOW_SIZE` delta-adjusts every active
stream window (§6.9.2), rejecting a resulting window above the cap. -/
def applySettings : ConnState → List (Nat × Nat) → Except Nat ConnState
  | st, [] => .ok st
  | st, (sid, v) :: rest =>
    if sid = 0x2 then
      if v ≤ 1 then applySettings st rest else .error errProtocol
    else if sid = 0x4 then
      if maxWindow < (v : Int) then .error errFlowControl
      else
        let delta : Int := (v : Int) - st.initWindow
        let streams' := st.streams.map fun q => (q.1, { q.2 with window := q.2.window + delta })
        if streams'.any (fun q => maxWindow < q.2.window) then .error errFlowControl
        else applySettings { st with initWindow := (v : Int), streams := streams' } rest
    else if sid = 0x5 then
      if v < 16384 || 16777215 < v then .error errProtocol
      else applySettings { st with peerMaxFrame := v } rest
    else applySettings st rest

/-- Handle one complete frame. `hdr` is the parsed 9-octet header, `payload`
its full declared payload (already buffered). The §4.3 header-block gate runs
first: while a header block is open, only CONTINUATION on the same stream is
legal. -/
def handleFrame (hd : Hpack.HuffmanDecoder) (handler : Handler)
    (st : ConnState) (hdr : FrameHeader) (payload : Bytes) : Out :=
  match st.cont with
  | some c =>
    if hdr.frameType = 0x9 && hdr.streamId = c.sid then
      let eh := flagSet hdr.flags 2
      let frag := c.frag ++ payload
      if eh then
        if c.trailer then finishTrailers hd handler st c.sid c.endStream frag
        else finishRequest hd handler st c.sid c.endStream frag
      else ({ st with cont := some { c with frag := frag } }, [], false)
    else connError st errProtocol
  | none =>
    if hdr.frameType = 0x0 then
      -- DATA (§6.1)
      if hdr.streamId = 0 then connError st errProtocol
      else
        let es := flagSet hdr.flags 0
        match stripPadding (flagSet hdr.flags 3) payload with
        | none => connError st errProtocol
        | some data =>
          match getStream st hdr.streamId with
          | none =>
            if st.maxSid < hdr.streamId then connError st errProtocol
            else connError st errStreamClosed
          | some sr =>
            match Stream.step sr.state (.recvData es) with
            | .protocolError => connError st errProtocol
            | .streamClosed => connError st errStreamClosed
            | .next s' =>
              let sr := { sr with state := s', recvd := sr.recvd + data.length, dataSeen := true, body := sr.body ++ data }
              let st := setStream st hdr.streamId sr
              if es then
                match sr.req with
                | none => streamError st hdr.streamId errProtocol
                | some req =>
                  match sr.clen with
                  | some n =>
                    if n ≠ sr.recvd then streamError st hdr.streamId errProtocol
                    else respond handler st hdr.streamId { req with body := sr.body }
                  | none => respond handler st hdr.streamId { req with body := sr.body }
              else (st, [], false)
    else if hdr.frameType = 0x1 then
      -- HEADERS (§6.2)
      if hdr.streamId = 0 then connError st errProtocol
      else
        let es := flagSet hdr.flags 0
        let eh := flagSet hdr.flags 2
        let prio := flagSet hdr.flags 5
        match stripPadding (flagSet hdr.flags 3) payload with
        | none => streamError st hdr.streamId errProtocol
        | some body =>
          if prio && body.length < 5 then connError st errFrameSize
          else if prio && readU32 body % 2 ^ 31 = hdr.streamId then
            -- §5.3.1: a stream cannot depend on itself
            streamError st hdr.streamId errProtocol
          else
            let frag := if prio then body.drop 5 else body
            match getStream st hdr.streamId with
            | some sr =>
              match sr.state with
              | .open | .halfClosedLocal =>
                -- A second HEADERS on an open stream is a **trailer** block iff
                -- the initial HEADERS completed *and* ≥ 1 DATA frame arrived
                -- (RFC 9113 §8.1, `Ext.detectTrailers`); we surface it as an
                -- `Ext.Event.trailers`. A second header block without any body
                -- is not a valid trailer section — a connection error.
                if Ext.detectTrailers sr.initialHeaders sr.dataSeen then
                  let st := { st with events := st.events ++ [Ext.Event.trailers hdr.streamId] }
                  if eh then finishTrailers hd handler st hdr.streamId es frag
                  else ({ st with
                    cont := some ⟨hdr.streamId, es, true, frag⟩ }, [], false)
                else connError st errProtocol
              | .halfClosedRemote => connError st errStreamClosed
              | .closed => connError st errStreamClosed
              | _ => connError st errProtocol
            | none =>
              if hdr.streamId % 2 = 0 then connError st errProtocol
              else if hdr.streamId ≤ st.maxSid then connError st errProtocol
              else if ourMaxConcurrentStreams ≤ activeStreams st then
                -- §5.1.2: opening this stream would exceed our advertised
                -- `SETTINGS_MAX_CONCURRENT_STREAMS` — a STREAM error (§5.4.2):
                -- `RST_STREAM(REFUSED_STREAM)`; the connection stays healthy
                -- and the refused id is consumed (§5.1.1).
                streamError { st with maxSid := max st.maxSid hdr.streamId }
                  hdr.streamId errRefusedStream
              else if eh then finishRequest hd handler st hdr.streamId es frag
              else
                ({ st with
                    maxSid := max st.maxSid hdr.streamId
                    cont := some ⟨hdr.streamId, es, false, frag⟩ }, [], false)
    else if hdr.frameType = 0x2 then
      -- PRIORITY (§6.3): legal on any stream state, including idle and closed
      if hdr.streamId = 0 then connError st errProtocol
      else if hdr.length ≠ 5 then streamError st hdr.streamId errFrameSize
      else if readU32 payload % 2 ^ 31 = hdr.streamId then
        streamError st hdr.streamId errProtocol
      else (st, [], false)
    else if hdr.frameType = 0x3 then
      -- RST_STREAM (§6.4)
      if hdr.streamId = 0 then connError st errProtocol
      else if hdr.length ≠ 4 then connError st errFrameSize
      else
        match getStream st hdr.streamId with
        | none =>
          if st.maxSid < hdr.streamId then connError st errProtocol
          else (st, [], false)
        | some sr =>
          (setStream st hdr.streamId
            { sr with state := .closed, pending := [], req := none }, [], false)
    else if hdr.frameType = 0x4 then
      -- SETTINGS (§6.5)
      if hdr.streamId ≠ 0 then connError st errProtocol
      else if flagSet hdr.flags 0 then
        if hdr.length ≠ 0 then connError st errFrameSize else (st, [], false)
      else if hdr.length % 6 ≠ 0 then connError st errFrameSize
      else
        match applySettings st (settingsPairs payload) with
        | .error code => connError st code
        | .ok st' =>
          let (st'', flushed) := flushAll st'
          (st'', settingsAckFrame ++ flushed, false)
    else if hdr.frameType = 0x5 then
      -- PUSH_PROMISE from a client (§8.4): always a protocol error
      connError st errProtocol
    else if hdr.frameType = 0x6 then
      -- PING (§6.7)
      if hdr.streamId ≠ 0 then connError st errProtocol
      else if hdr.length ≠ 8 then connError st errFrameSize
      else if flagSet hdr.flags 0 then (st, [], false)
      else (st, pingAckFrame payload, false)
    else if hdr.frameType = 0x7 then
      -- GOAWAY (§6.8): the peer will open no new streams; existing processing
      -- continues (any error code is accepted, §7)
      if hdr.streamId ≠ 0 then connError st errProtocol
      else (st, [], false)
    else if hdr.frameType = 0x8 then
      -- WINDOW_UPDATE (§6.9)
      if hdr.length ≠ 4 then connError st errFrameSize
      else
        let inc : Int := (readU32 payload % 2 ^ 31 : Nat)
        if hdr.streamId = 0 then
          if inc = 0 then connError st errProtocol
          else if maxWindow < st.connWindow + inc then connError st errFlowControl
          else
            let (st', o) := flushAll { st with connWindow := st.connWindow + inc }
            (st', o, false)
        else
          match getStream st hdr.streamId with
          | none =>
            if st.maxSid < hdr.streamId then connError st errProtocol
            else (st, [], false)
          | some sr =>
            if inc = 0 then streamError st hdr.streamId errProtocol
            else if maxWindow < sr.window + inc then
              streamError st hdr.streamId errFlowControl
            else
              let (st', o) := flushStream
                (setStream st hdr.streamId { sr with window := sr.window + inc })
                hdr.streamId
              (st', o, false)
    else if hdr.frameType = 0x9 then
      -- CONTINUATION outside an open header block (§6.10)
      connError st errProtocol
    else if hdr.frameType = 0x0a then
      -- ALTSVC (RFC 7838 §4): advisory. Surface `(origin, alt-svc-value)` as an
      -- event. Per §4 an ALTSVC with an empty origin on stream 0, or a non-empty
      -- origin on a non-zero stream, is invalid and ignored; a malformed payload
      -- is ignored. Never a connection error.
      match Ext.decodeAltSvc payload with
      | some (origin, value) =>
        if (hdr.streamId == 0) == origin.isEmpty then (st, [], false)
        else ({ st with
          events := st.events ++ [Ext.Event.altSvc hdr.streamId origin value] }, [], false)
      | none => (st, [], false)
    else if hdr.frameType = 0x0c then
      -- ORIGIN (RFC 8336 §2): sent on stream 0 only; on any other stream it is
      -- invalid and MUST be ignored. Surface the declared origins as an event;
      -- a malformed payload is ignored. Never a connection error.
      if hdr.streamId ≠ 0 then (st, [], false)
      else
        match Ext.decodeOrigins (payload.length + 1) payload with
        | some origins => ({ st with
            events := st.events ++ [Ext.Event.origin origins] }, [], false)
        | none => (st, [], false)
    else
      -- Unknown/extension frame type: ignored (§4.1, §5.5)
      (st, [], false)

/-! ## The frame pump and the feed -/

/-- Walk whole frames off the connection buffer: parse the header, enforce our
`SETTINGS_MAX_FRAME_SIZE` (§4.2), wait for the full payload, dispatch. Fueled
by the buffer length (each frame consumes ≥ 9 octets). -/
def pump (hd : Hpack.HuffmanDecoder) (handler : Handler) :
    Nat → ConnState → Out
  | 0, st => (st, [], false)
  | fuel + 1, st =>
    match parseHeader st.buf with
    | none => (st, [], false)
    | some hdr =>
      if ourMaxFrameSize < hdr.length then connError st errFrameSize
      else if st.buf.length < 9 + hdr.length then (st, [], false)
      else
        let payload := (st.buf.drop 9).take hdr.length
        let st := { st with buf := st.buf.drop (9 + hdr.length) }
        let (st', o, close) := handleFrame hd handler st hdr payload
        if close then (st', o, true)
        else
          let (st'', o', close') := pump hd handler fuel st'
          (st'', o ++ o', close')

/-- **The engine's transition function.** Consume `input` (any split): validate
the remaining client-preface octets (§3.4 — a mismatch is refused with
`GOAWAY(PROTOCOL_ERROR)`), emit the server preface when the client preface
completes, then pump whole frames. Returns the successor state, the octets to
write, and whether the host must close after writing. -/
def feed (hd : Hpack.HuffmanDecoder) (handler : Handler)
    (st : ConnState) (input : Bytes) : Out :=
  if st.closed then (st, [], true)
  else if 0 < st.prefaceLeft then
    let n := min st.prefaceLeft input.length
    let got := input.take n
    let expect := (clientPreface.drop (clientPreface.length - st.prefaceLeft)).take n
    if got ≠ expect then
      ({ st with closed := true }, goawayFrame 0 errProtocol, true)
    else
      let st' := { st with
        prefaceLeft := st.prefaceLeft - n
        buf := st.buf ++ input.drop n }
      if st'.prefaceLeft = 0 then
        let (st'', o, close) := pump hd handler (st'.buf.length + 1) st'
        (st'', serverSettings ++ o, close)
      else (st', [], false)
  else
    let st' := { st with buf := st.buf ++ input }
    pump hd handler (st'.buf.length + 1) st'

/-- A fresh connection (preface unconsumed, empty dynamic table, default
windows). -/
def initState : ConnState := {}

/-! ## Behavior theorems (the named RFC obligations)

Each theorem is a statement about the engine's *own* transition function
(`feed` / `handleFrame` / `sendChunks`), not a side model. The connection is
"parked" when its preface is consumed, no partial frame is buffered, no header
block is open, and it is not closed — the state between whole frames. -/

/-- The encoded 9-octet header is 9 octets. -/
theorem frameHdr_length (len ty fl sid : Nat) : (frameHdr len ty fl sid).length = 9 := rfl

/-- `parseHeader` inverts `frameHdr`: the engine's own header encoder parses
back to exactly the fields it was given (length < 2^24, type/flags octets,
stream id < 2^31), for any following bytes. -/
theorem parseHeader_frameHdr (len ty fl sid : Nat) (rest : Bytes)
    (hlen : len < 2 ^ 24) (hty : ty < 256) (hfl : fl < 256) (hsid : sid < 2 ^ 31) :
    parseHeader (frameHdr len ty fl sid ++ rest)
      = some { length := len, frameType := ty, flags := fl, streamId := sid } := by
  simp only [frameHdr, be24, be32, List.cons_append, List.nil_append,
    parseHeader, parseHeaderAux, Option.some.injEq,
    FrameHeader.mk.injEq, UInt8.toNat_ofNat']
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- Pumping an empty buffer produces nothing and changes nothing. -/
theorem pump_nil (hd : Hpack.HuffmanDecoder) (handler : Handler)
    (fuel : Nat) (st : ConnState) (hbuf : st.buf = []) :
    pump hd handler fuel st = (st, [], false) := by
  cases fuel with
  | zero => rfl
  | succ n => unfold pump; rw [hbuf]; rfl

/-- **The single-frame feed step**: fed exactly one whole within-limit frame,
a parked connection performs exactly one `handleFrame` step — the successor
state, output octets, and close flag are the step's own (provided the step
leaves no buffered input, which every `handleFrame` branch does when fed a
whole frame). -/
theorem feed_single_frame (hd : Hpack.HuffmanDecoder) (handler : Handler)
    (st st' : ConnState) (o : Bytes) (close : Bool)
    (len ty fl sid : Nat) (payload : Bytes)
    (hclosed : st.closed = false) (hpre : st.prefaceLeft = 0) (hbuf : st.buf = [])
    (hlen : payload.length = len) (hsz : len ≤ ourMaxFrameSize) (hlen24 : len < 2 ^ 24)
    (hty : ty < 256) (hfl : fl < 256) (hsid : sid < 2 ^ 31)
    (hstep : handleFrame hd handler st ⟨len, ty, fl, sid⟩ payload = (st', o, close))
    (hbuf' : st'.buf = []) :
    feed hd handler st (frameHdr len ty fl sid ++ payload) = (st', o, close) := by
  have hin : (frameHdr len ty fl sid ++ payload).length = 9 + len := by
    simp [frameHdr, be24, be32, hlen]; omega
  have hdrop9 : (frameHdr len ty fl sid ++ payload).drop 9 = payload := by
    rw [← frameHdr_length len ty fl sid, List.drop_left]
  have hdropall : (frameHdr len ty fl sid ++ payload).drop (9 + len) = [] := by
    rw [← hin]; exact List.drop_length
  have htake : payload.take len = payload := by
    rw [← hlen]; exact List.take_length
  have hst : ({ st with buf := [] } : ConnState) = st := by rw [← hbuf]
  unfold feed
  rw [if_neg (by simp [hclosed]), if_neg (by simp [hpre]), hbuf]
  dsimp only [List.nil_append]
  rw [hin]
  unfold pump
  rw [parseHeader_frameHdr len ty fl sid payload hlen24 hty hfl hsid]
  dsimp only
  rw [if_neg (Nat.not_lt.mpr hsz), hin, if_neg (Nat.lt_irrefl _), hdrop9, htake,
    hdropall, hst, hstep]
  cases close with
  | true => rfl
  | false =>
    dsimp only
    rw [pump_nil hd handler _ st' hbuf', List.append_nil]
    rfl

/-- **§6.7 PING liveness**: a well-formed PING (stream 0, no ACK flag, 8 opaque
octets) fed to a parked connection is answered by exactly a PING ACK carrying
the same 8 octets; the connection stays open and the engine state is
unchanged. -/
theorem feed_ping_ack (hd : Hpack.HuffmanDecoder) (handler : Handler)
    (st : ConnState) (data : Bytes)
    (hclosed : st.closed = false) (hpre : st.prefaceLeft = 0) (hbuf : st.buf = [])
    (hcont : st.cont = none) (hdata : data.length = 8) :
    feed hd handler st (frameHdr 8 0x6 0 0 ++ data)
      = (st, pingAckFrame data, false) := by
  refine feed_single_frame hd handler st st (pingAckFrame data) false
    8 0x6 0 0 data hclosed hpre hbuf hdata (by decide) (by decide) (by decide)
    (by decide) (by decide) ?_ hbuf
  unfold handleFrame
  rw [hcont]
  rfl

/-- **§6.5.3 SETTINGS synchronization**: an empty SETTINGS frame (no ACK flag)
fed to a parked connection with no active streams is acknowledged — the output
is exactly a SETTINGS ACK, the connection stays open, and the state is
unchanged. -/
theorem feed_settings_ack (hd : Hpack.HuffmanDecoder) (handler : Handler)
    (st : ConnState)
    (hclosed : st.closed = false) (hpre : st.prefaceLeft = 0) (hbuf : st.buf = [])
    (hcont : st.cont = none) (hstreams : st.streams = []) :
    feed hd handler st (frameHdr 0 0x4 0 0)
      = (st, settingsAckFrame, false) := by
  have h := feed_single_frame hd handler st st settingsAckFrame false
    0 0x4 0 0 [] hclosed hpre hbuf rfl (by decide) (by decide) (by decide)
    (by decide) (by decide) ?_ hbuf
  · simpa using h
  · unfold handleFrame
    rw [hcont]
    show (let (st'', flushed) := flushAll st
          (st'', settingsAckFrame ++ flushed, false)) = (st, settingsAckFrame, false)
    have hflush : flushAll st = (st, []) := by
      unfold flushAll
      rw [hstreams]
      rfl
    rw [hflush]
    rfl

/-- **§4.1/§5.5 extension tolerance**: a complete frame of any unknown type is
ignored — no output, no close, no state change. Unknown ≠ fatal. -/
theorem feed_unknown_ignored (hd : Hpack.HuffmanDecoder) (handler : Handler)
    (st : ConnState) (len ty fl sid : Nat) (payload : Bytes)
    (hclosed : st.closed = false) (hpre : st.prefaceLeft = 0) (hbuf : st.buf = [])
    (hcont : st.cont = none)
    (hlen : payload.length = len) (hsz : len ≤ ourMaxFrameSize) (hlen24 : len < 2 ^ 24)
    (hty9 : 9 < ty) (hna : ty ≠ 0x0a) (hnc : ty ≠ 0x0c)
    (hty : ty < 256) (hfl : fl < 256) (hsid : sid < 2 ^ 31) :
    feed hd handler st (frameHdr len ty fl sid ++ payload) = (st, [], false) := by
  refine feed_single_frame hd handler st st [] false len ty fl sid payload
    hclosed hpre hbuf hlen hsz hlen24 hty hfl hsid ?_ hbuf
  unfold handleFrame
  rw [hcont]
  simp only []
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-! ### Extension-surface integration (ORIGIN / ALT-SVC / trailers)

Each theorem states that `handleFrame` — the per-frame core of `feed` — routes
the extension frame to its `Ext` codec and surfaces the corresponding
`Ext.Event` on the successor state, with the RFC-mandated validation. The
codecs' own faithfulness lives in `H2.Ext`; these tie them into the engine. -/

/-- **RFC 8336 ORIGIN integration**: an ORIGIN frame (type `0x0c`) on stream 0
whose payload decodes as origin entries surfaces exactly an `Ext.Event.origin`
carrying those origins — no output, no close. -/
theorem handleFrame_origin_event (hd : Hpack.HuffmanDecoder) (handler : Handler)
    (st : ConnState) (payload : Bytes) (origins : List Bytes)
    (hcont : st.cont = none)
    (hok : Ext.decodeOrigins (payload.length + 1) payload = some origins) :
    handleFrame hd handler st ⟨payload.length, 0x0c, 0, 0⟩ payload
      = ({ st with events := st.events ++ [Ext.Event.origin origins] }, [], false) := by
  unfold handleFrame
  rw [hcont]
  simp only [hok, Nat.reduceEqDiff, reduceIte, ne_eq, not_true]

/-- **RFC 7838 ALT-SVC integration**: an ALTSVC frame (type `0x0a`) whose payload
decodes as `(origin, value)`, with the §4 stream/origin combination valid (empty
origin iff non-zero stream), surfaces exactly an `Ext.Event.altSvc`. -/
theorem handleFrame_altsvc_event (hd : Hpack.HuffmanDecoder) (handler : Handler)
    (st : ConnState) (payload : Bytes) (origin value : Bytes) (sid : Nat)
    (hcont : st.cont = none)
    (hok : Ext.decodeAltSvc payload = some (origin, value))
    (hvalid : ((sid == 0) == origin.isEmpty) = false) :
    handleFrame hd handler st ⟨payload.length, 0x0a, 0, sid⟩ payload
      = ({ st with events := st.events ++ [Ext.Event.altSvc sid origin value] }, [], false) := by
  unfold handleFrame
  rw [hcont]
  simp only [hok, hvalid, Nat.reduceEqDiff, reduceIte, ne_eq, Bool.false_eq_true]

/-- **RFC 9113 §8.1 trailer integration**: a second HEADERS block on an open
stream that has both received its initial headers and seen data
(`Ext.detectTrailers` is true) is routed as a trailer section and surfaces an
`Ext.Event.trailers` — never mistaken for a second header block. Shown for a
CONTINUATION-pending block (`END_HEADERS` clear), so the routing is exhibited
without re-deriving HPACK. -/
theorem handleFrame_trailers_event (hd : Hpack.HuffmanDecoder) (handler : Handler)
    (st : ConnState) (sid : Nat) (payload : Bytes) (sr : StreamRec)
    (hcont : st.cont = none) (hsid : ¬ (sid = 0))
    (hget : getStream st sid = some sr)
    (hstate : sr.state = Stream.StreamState.open)
    (hinit : sr.initialHeaders = true) (hdata : sr.dataSeen = true) :
    handleFrame hd handler st ⟨payload.length, 0x1, 0, sid⟩ payload
      = ({ { st with events := st.events ++ [Ext.Event.trailers sid] } with
            cont := some ⟨sid, false, true, payload⟩ }, [], false) := by
  unfold handleFrame
  rw [hcont]
  simp only [show flagSet 0 0 = false from rfl, show flagSet 0 2 = false from rfl,
    show flagSet 0 3 = false from rfl, show flagSet 0 5 = false from rfl,
    stripPadding, Bool.false_and, hget, hstate, hinit, hdata, hsid,
    Ext.detectTrailers, Bool.and_self,
    Nat.reduceEqDiff, reduceIte, ne_eq, Bool.false_eq_true]

/-- **§3.4 preface validation**: a connection whose opening octets differ from
the client connection preface is refused with `GOAWAY(PROTOCOL_ERROR)` and
closed — never a torn socket. -/
theorem feed_preface_invalid (hd : Hpack.HuffmanDecoder) (handler : Handler)
    (input : Bytes)
    (hne : input.take (min 24 input.length)
      ≠ clientPreface.take (min 24 input.length)) :
    feed hd handler initState input
      = ({ initState with closed := true }, goawayFrame 0 errProtocol, true) := by
  unfold feed
  rw [show initState.closed = false from rfl]
  simp only [Bool.false_eq_true, if_false]
  rw [show initState.prefaceLeft = 24 from rfl, if_pos (by decide : 0 < 24),
    clientPreface_length]
  simp only [Nat.sub_self, List.drop_zero]
  rw [if_pos hne]

/-- **§4.2 frame-size enforcement**: a frame whose declared length exceeds our
advertised `SETTINGS_MAX_FRAME_SIZE` is refused with `GOAWAY(FRAME_SIZE_ERROR)`
and close, before any payload octet is read. -/
theorem feed_oversize_goaway (hd : Hpack.HuffmanDecoder) (handler : Handler)
    (st : ConnState) (len ty fl sid : Nat) (rest : Bytes)
    (hclosed : st.closed = false) (hpre : st.prefaceLeft = 0) (hbuf : st.buf = [])
    (hsz : ourMaxFrameSize < len) (hlen24 : len < 2 ^ 24)
    (hty : ty < 256) (hfl : fl < 256) (hsid : sid < 2 ^ 31) :
    feed hd handler st (frameHdr len ty fl sid ++ rest)
      = ({ st with closed := true, buf := [], cont := none },
         goawayFrame st.maxSid errFrameSize, true) := by
  unfold feed
  rw [if_neg (by simp [hclosed]), if_neg (by simp [hpre]), hbuf]
  dsimp only [List.nil_append]
  have hfuel : ∃ n, (frameHdr len ty fl sid ++ rest).length + 1 = n + 1 :=
    ⟨(frameHdr len ty fl sid ++ rest).length, rfl⟩
  unfold pump
  rw [parseHeader_frameHdr len ty fl sid rest hlen24 hty hfl hsid]
  dsimp only
  rw [if_pos hsz]
  rfl

/-- **§4.3 HPACK-error surfacing**: a HEADERS frame (END_HEADERS set, no
padding, no priority) opening a fresh stream, whose header block fails HPACK
decoding, is refused as a connection error: `GOAWAY(COMPRESSION_ERROR)` and
close (RFC 7541 §2.3.3/§4.2/§5.2/§6.3 decode errors all surface here). -/
theorem feed_hpack_error_goaway (hd : Hpack.HuffmanDecoder) (handler : Handler)
    (st : ConnState) (sid : Nat) (frag : Bytes) (e : Hpack.Err)
    (hclosed : st.closed = false) (hpre : st.prefaceLeft = 0) (hbuf : st.buf = [])
    (hcont : st.cont = none) (hstreams : st.streams = [])
    (hodd : sid % 2 = 1) (hmax : st.maxSid < sid) (hsid : sid < 2 ^ 31)
    (hsz : frag.length ≤ ourMaxFrameSize) (hlen24 : frag.length < 2 ^ 24)
    (hdec : decodeBlockV hd (frag.length + 1) st.hpack frag {} false false = .error e) :
    feed hd handler st (frameHdr frag.length 0x1 0x4 sid ++ frag)
      = ({ st with closed := true, buf := [], cont := none },
         goawayFrame st.maxSid errCompression, true) := by
  refine feed_single_frame hd handler st _ _ true frag.length 0x1 0x4 sid frag
    hclosed hpre hbuf rfl hsz hlen24 (by decide) (by decide) hsid ?_ rfl
  unfold handleFrame
  rw [hcont]
  simp only []
  rw [if_neg (by omega : ¬ (0x1 = 0x0)), if_neg (by omega : ¬ sid = 0)]
  simp only [show flagSet 0x4 0 = false from rfl, show flagSet 0x4 2 = true from rfl,
    show flagSet 0x4 3 = false from rfl, show flagSet 0x4 5 = false from rfl,
    stripPadding, Bool.false_and, Bool.false_eq_true, if_false]
  rw [show getStream st sid = none from by simp [getStream, hstreams]]
  simp only []
  rw [if_neg (by omega : ¬ sid % 2 = 0), if_neg (Nat.not_le.mpr hmax),
    if_neg (show ¬ ourMaxConcurrentStreams ≤ activeStreams st by
      unfold activeStreams; rw [hstreams]; decide)]
  show finishRequest hd handler st sid false frag
      = ({ st with closed := true, buf := [], cont := none },
         goawayFrame st.maxSid errCompression, true)
  unfold finishRequest
  rw [hdec]
  rfl

/-! ### §6.9 pacer obligations (`sendChunks`) -/

/-- **§6.9 zero-credit parking**: with no sendable credit the pacer emits
nothing and parks the whole body — bytes are never dropped on a closed
window. -/
theorem sendChunks_parks (fuel sid : Nat) (cw sw : Int) (mf : Nat) (body : Bytes)
    (h : credit cw sw = 0) :
    sendChunks fuel sid cw sw mf body = ([], body, cw, sw) := by
  cases fuel with
  | zero => rfl
  | succ n =>
    unfold sendChunks
    by_cases hb : body.isEmpty
    · rw [if_pos hb, List.isEmpty_iff.mp hb]
    · rw [if_neg hb,
        if_pos (show min (min (credit cw sw) mf) body.length = 0 by omega)]

/-- **§6.9 conservation + window accounting**: the pacer never loses bytes —
the parked remainder is at most the offered body, and BOTH windows decrease by
exactly the number of emitted octets (offered minus parked). -/
theorem sendChunks_accounting (fuel : Nat) :
    ∀ (sid : Nat) (cw sw : Int) (mf : Nat) (body fs rem : Bytes) (cw' sw' : Int),
    sendChunks fuel sid cw sw mf body = (fs, rem, cw', sw') →
    rem.length ≤ body.length
      ∧ cw' = cw - ((body.length - rem.length : Nat) : Int)
      ∧ sw' = sw - ((body.length - rem.length : Nat) : Int) := by
  induction fuel with
  | zero =>
    intro sid cw sw mf body fs rem cw' sw' h
    unfold sendChunks at h
    cases h
    simp
  | succ n ih =>
    intro sid cw sw mf body fs rem cw' sw' h
    unfold sendChunks at h
    by_cases hb : body.isEmpty
    · rw [if_pos hb] at h
      cases h
      simp [List.isEmpty_iff.mp hb]
    · rw [if_neg hb] at h
      by_cases h0 : min (min (credit cw sw) mf) body.length = 0
      · rw [if_pos h0] at h
        cases h
        simp
      · rw [if_neg h0] at h
        dsimp only at h
        rcases hrec : sendChunks n sid
            (cw - ↑(min (min (credit cw sw) mf) body.length))
            (sw - ↑(min (min (credit cw sw) mf) body.length)) mf
            (body.drop (min (min (credit cw sw) mf) body.length))
          with ⟨fs1, rem1, cw1, sw1⟩
        rw [hrec] at h
        dsimp only at h
        cases h
        obtain ⟨hle, hcw, hsw⟩ := ih _ _ _ _ _ _ _ _ _ hrec
        rw [List.length_drop] at hle hcw hsw
        have hmin : min (min (credit cw sw) mf) body.length ≤ body.length :=
          Nat.min_le_right _ _
        refine ⟨by omega, ?_, ?_⟩ <;> omega

/-- **§6.9 no-overdraw**: emission never drives either window below zero —
whatever the pacer emits was covered by the joint credit. -/
theorem sendChunks_no_overdraw (fuel : Nat) :
    ∀ (sid : Nat) (cw sw : Int) (mf : Nat) (body fs rem : Bytes) (cw' sw' : Int),
    sendChunks fuel sid cw sw mf body = (fs, rem, cw', sw') →
    (0 ≤ cw → 0 ≤ cw') ∧ (0 ≤ sw → 0 ≤ sw') := by
  induction fuel with
  | zero =>
    intro sid cw sw mf body fs rem cw' sw' h
    unfold sendChunks at h
    cases h
    exact ⟨id, id⟩
  | succ n ih =>
    intro sid cw sw mf body fs rem cw' sw' h
    unfold sendChunks at h
    by_cases hb : body.isEmpty
    · rw [if_pos hb] at h
      cases h
      exact ⟨id, id⟩
    · rw [if_neg hb] at h
      by_cases h0 : min (min (credit cw sw) mf) body.length = 0
      · rw [if_pos h0] at h
        cases h
        exact ⟨id, id⟩
      · rw [if_neg h0] at h
        dsimp only at h
        rcases hrec : sendChunks n sid
            (cw - ↑(min (min (credit cw sw) mf) body.length))
            (sw - ↑(min (min (credit cw sw) mf) body.length)) mf
            (body.drop (min (min (credit cw sw) mf) body.length))
          with ⟨fs1, rem1, cw1, sw1⟩
        rw [hrec] at h
        dsimp only at h
        cases h
        have hcpos : 0 < credit cw sw := by omega
        have hkey : (credit cw sw : Int) ≤ min cw sw := by
          simp only [credit] at hcpos ⊢
          by_cases hc : min cw sw ≤ 0
          · rw [if_pos hc] at hcpos; omega
          · rw [if_neg hc] at hcpos ⊢
            rw [Int.toNat_of_nonneg (by omega : (0 : Int) ≤ min cw sw)]
            exact Int.le_refl _
        have h1 : (0 : Int) ≤ cw - ↑(min (min (credit cw sw) mf) body.length) := by
          omega
        have h2 : (0 : Int) ≤ sw - ↑(min (min (credit cw sw) mf) body.length) := by
          omega
        obtain ⟨hc1, hc2⟩ := ih _ _ _ _ _ _ _ _ _ hrec
        exact ⟨fun _ => hc1 h1, fun _ => hc2 h2⟩

/-- **§6.5.3 last-value-wins**: multiple `SETTINGS_INITIAL_WINDOW_SIZE` values
in one SETTINGS frame leave the LAST value as the connection's initial window
(shown on a connection with no active streams; §6.9.2 delta-adjustment of live
streams is the `applySettings` 0x4 arm itself). -/
theorem applySettings_initialWindow_last (st : ConnState) (v1 v2 : Nat)
    (hstreams : st.streams = [])
    (h1 : (v1 : Int) ≤ maxWindow) (h2 : (v2 : Int) ≤ maxWindow) :
    applySettings st [(0x4, v1), (0x4, v2)]
      = .ok { st with initWindow := (v2 : Int), streams := [] } := by
  unfold applySettings
  rw [if_neg (by omega : ¬ (0x4 = 0x2)), if_pos rfl, if_neg (Int.not_lt.mpr h1), hstreams]
  simp only [List.map_nil, List.any_nil, Bool.false_eq_true, if_false]
  unfold applySettings
  rw [if_neg (by omega : ¬ (0x4 = 0x2))]
  simp only [if_true]
  rw [if_neg (Int.not_lt.mpr h2)]
  simp only [List.map_nil, List.any_nil, Bool.false_eq_true, if_false]
  unfold applySettings
  rfl

/-! ### Kernel-evaluated wire vectors for the control-frame behaviors

These force evaluation of `feed` on real octets — the decoder plugged in
rejects every Huffman string and the handler answers nothing, so the vectors
exercise only the engine's own control-frame logic. -/

private def guardHd : Hpack.HuffmanDecoder := ⟨fun _ => none⟩
private def guardHandler : Handler := fun _ => { block := [], body := [] }
private def guardReady : ConnState := { prefaceLeft := 0 }

/-! A PING (§6.7) is answered by a PING ACK echoing the 8 opaque octets. -/
#guard (feed guardHd guardHandler guardReady
    (frameHdr 8 0x6 0 0 ++ [1, 2, 3, 4, 5, 6, 7, 8])).2
  = (pingAckFrame [1, 2, 3, 4, 5, 6, 7, 8], false)

/-! An empty SETTINGS (§6.5.3) is acknowledged. -/
#guard (feed guardHd guardHandler guardReady (frameHdr 0 0x4 0 0)).2
  = (settingsAckFrame, false)

/-! An unknown frame type (§4.1/§5.5) is ignored, not fatal. -/
#guard (feed guardHd guardHandler guardReady
    (frameHdr 3 0x0B 0x7F 5 ++ [9, 9, 9])).2 = ([], false)

/-! An invalid connection preface (§3.4) is refused with
`GOAWAY(PROTOCOL_ERROR)` and close — `PRX` differs at the third octet. -/
#guard (feed guardHd guardHandler initState [0x50, 0x52, 0x58]).2
  = (goawayFrame 0 errProtocol, true)

/-! An oversize frame (§4.2) is refused with `GOAWAY(FRAME_SIZE_ERROR)`. -/
#guard (feed guardHd guardHandler guardReady (frameHdr 16385 0x0 0 1)).2
  = (goawayFrame 0 errFrameSize, true)

/-! ### Extension-surface wire vectors (end-to-end through `feed`) -/

/-! An ORIGIN frame (RFC 8336, type 0x0c) on stream 0 carrying origin `"a.io"`
surfaces exactly one `Ext.Event.origin` event on the successor state. -/
#guard (feed guardHd guardHandler guardReady
    (frameHdr 6 0x0c 0 0 ++ [0x00, 0x04, 0x61, 0x2e, 0x69, 0x6f])).1.events
  = [Ext.Event.origin [[0x61, 0x2e, 0x69, 0x6f]]]

/-! An ALTSVC frame (RFC 7838, type 0x0a) on stream 0 with origin `"x.io"` and
value `"h3"` surfaces exactly one `Ext.Event.altSvc` event. -/
#guard (feed guardHd guardHandler guardReady
    (frameHdr 8 0x0a 0 0 ++ [0x00, 0x04, 0x78, 0x2e, 0x69, 0x6f, 0x68, 0x33])).1.events
  = [Ext.Event.altSvc 0 [0x78, 0x2e, 0x69, 0x6f] [0x68, 0x33]]

/-! **RFC 9218 Extensible Priority end to end**: an initial HEADERS block on
stream 1 carrying `:method GET :scheme http :path /` (HPACK static 0x82/0x86/0x84)
and a literal `priority: u=1, i` header parks a request whose stream record
carries the parsed `Priority { urgency := 1, incremental := true }`. -/
#guard (getStream (feed guardHd guardHandler guardReady
    (frameHdr 20 0x1 0x04 1 ++
      [0x82, 0x86, 0x84,
       0x00, 0x08, 0x70, 0x72, 0x69, 0x6f, 0x72, 0x69, 0x74, 0x79,
       0x06, 0x75, 0x3d, 0x31, 0x2c, 0x20, 0x69])).1 1).map
    (fun sr => sr.priority) = some { urgency := 1, incremental := true }

/-! **Trailer detection end to end** (RFC 9113 §8.1): a real HEADERS(END_HEADERS,
no END_STREAM) → DATA → HEADERS(END_HEADERS+END_STREAM) sequence on stream 1.
The first HEADERS is the initial request (`:method GET :scheme http :path /`
via HPACK static indices 0x82/0x86/0x84), the DATA marks the stream body-bearing,
and the second HEADERS (a `x: y` literal block) is recognized as trailers — the
successor state carries exactly one `Ext.Event.trailers 1`. -/
#guard (feed guardHd guardHandler guardReady
    ((frameHdr 3 0x1 0x04 1 ++ [0x82, 0x86, 0x84]) ++
     (frameHdr 1 0x0 0 1 ++ [0xaa]) ++
     (frameHdr 5 0x1 0x05 1 ++ [0x00, 0x01, 0x78, 0x01, 0x79]))).1.events
  = [Ext.Event.trailers 1]

/-! ## §7.0d  Pruning a CONSUMED request body is unobservable to the engine

A host that drains completed requests off a long-lived connection wants to clear the
assembled `StreamRec.body` of every stream whose request was already dispatched — the
retained history is otherwise re-walked (and re-parsed) on every subsequent record, and
it is exactly the state a stale replay comes from (`ControlLive.pruneConsumed`).

The licence for doing that is NOT an enumeration of the places the engine reads
`StreamRec.body`; an enumeration breaks silently the moment a third read site is added.
It is the theorem below: **states that agree after pruning are indistinguishable to
`feed`** — same output octets, same close flag, and successor states that again agree
after pruning (`feed_congr`). Every read site is covered by construction, including any
added later, because the proof is over `feed`/`pump`/`handleFrame` themselves.

The relation is `pruneBodies st₁ = pruneBodies st₂` — "differ only in the bodies of
streams that are `.closed` with no parked request". `pruneOut` lifts the pruning to an
engine step's outcome (state pruned, octets and close flag untouched).
-/

/-- A stream record whose request body has already been dispatched. -/
def bodyConsumed (sr : StreamRec) : Bool := sr.state == .closed && sr.req.isNone

/-- Blind a record's body when (and only when) that body was already consumed. -/
def blindRec (sr : StreamRec) : StreamRec :=
  if bodyConsumed sr then { sr with body := [] } else sr

/-- Blinding lifted to a `(sid, record)` entry. -/
def blindPair (p : Nat × StreamRec) : Nat × StreamRec := (p.1, blindRec p.2)

/-- Clear the assembled request body of every already-dispatched stream. -/
def pruneBodies (st : ConnState) : ConnState :=
  { st with streams := st.streams.map blindPair }

/-- Blinding lifted to an engine step's outcome (state pruned, bytes and close
flag untouched). -/
def pruneOut (r : Out) : Out := (pruneBodies r.1, r.2.1, r.2.2)

/-! ### `blindRec` basics -/

theorem blindRec_of_not {sr : StreamRec} (h : bodyConsumed sr = false) : blindRec sr = sr := by
  simp [blindRec, h]

theorem blindRec_of {sr : StreamRec} (h : bodyConsumed sr = true) :
    blindRec sr = { sr with body := [] } := by
  simp [blindRec, h]

@[simp] theorem bodyConsumed_clear (sr : StreamRec) :
    bodyConsumed { sr with body := [] } = bodyConsumed sr := rfl

@[simp] theorem blindRec_state (sr : StreamRec) : (blindRec sr).state = sr.state := by
  by_cases h : bodyConsumed sr <;> simp [blindRec, h]

@[simp] theorem blindRec_req (sr : StreamRec) : (blindRec sr).req = sr.req := by
  by_cases h : bodyConsumed sr <;> simp [blindRec, h]

@[simp] theorem blindRec_window (sr : StreamRec) : (blindRec sr).window = sr.window := by
  by_cases h : bodyConsumed sr <;> simp [blindRec, h]

@[simp] theorem blindRec_pending (sr : StreamRec) : (blindRec sr).pending = sr.pending := by
  by_cases h : bodyConsumed sr <;> simp [blindRec, h]

@[simp] theorem blindRec_clen (sr : StreamRec) : (blindRec sr).clen = sr.clen := by
  by_cases h : bodyConsumed sr <;> simp [blindRec, h]

@[simp] theorem blindRec_recvd (sr : StreamRec) : (blindRec sr).recvd = sr.recvd := by
  by_cases h : bodyConsumed sr <;> simp [blindRec, h]

@[simp] theorem blindRec_initialHeaders (sr : StreamRec) :
    (blindRec sr).initialHeaders = sr.initialHeaders := by
  by_cases h : bodyConsumed sr <;> simp [blindRec, h]

@[simp] theorem blindRec_dataSeen (sr : StreamRec) : (blindRec sr).dataSeen = sr.dataSeen := by
  by_cases h : bodyConsumed sr <;> simp [blindRec, h]

@[simp] theorem blindRec_priority (sr : StreamRec) : (blindRec sr).priority = sr.priority := by
  by_cases h : bodyConsumed sr <;> simp [blindRec, h]

@[simp] theorem bodyConsumed_blindRec (sr : StreamRec) :
    bodyConsumed (blindRec sr) = bodyConsumed sr := by
  by_cases h : bodyConsumed sr <;> simp [blindRec, h]

@[simp] theorem blindPair_fst (p : Nat × StreamRec) : (blindPair p).1 = p.1 := rfl

@[simp] theorem blindPair_snd (p : Nat × StreamRec) : (blindPair p).2 = blindRec p.2 := rfl

theorem blindRec_idem (sr : StreamRec) : blindRec (blindRec sr) = blindRec sr := by
  by_cases h : bodyConsumed sr <;> simp [blindRec, h]

/-- **The shape of the relation on one record.** Two records with the same blinding
are either literally equal, or both already consumed and equal apart from the body. -/
theorem blindRec_cases {a b : StreamRec} (h : blindRec a = blindRec b) :
    a = b ∨ (bodyConsumed a = true ∧ bodyConsumed b = true ∧
      ({ a with body := ([] : Bytes) } = { b with body := ([] : Bytes) })) := by
  by_cases ha : bodyConsumed a = true
  · by_cases hb : bodyConsumed b = true
    · exact Or.inr ⟨ha, hb, by rw [blindRec_of ha, blindRec_of hb] at h; exact h⟩
    · rw [blindRec_of ha, blindRec_of_not (by simpa using hb)] at h
      exact absurd (by rw [← h]; simpa using ha) hb
  · by_cases hb : bodyConsumed b = true
    · rw [blindRec_of_not (by simpa using ha), blindRec_of hb] at h
      exact absurd (by rw [h]; simpa using hb) ha
    · exact Or.inl (by rw [blindRec_of_not (by simpa using ha),
        blindRec_of_not (by simpa using hb)] at h; exact h)

/-! ### The relation on connection states -/

/-- Two connection states are **prune-equal** when they differ only in the assembled
bodies of streams whose request was already dispatched. -/
abbrev RelSt (st₁ st₂ : ConnState) : Prop := pruneBodies st₁ = pruneBodies st₂

theorem pruneBodies_idem (st : ConnState) : pruneBodies (pruneBodies st) = pruneBodies st := by
  simp only [pruneBodies, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  simp [Function.comp, blindPair, blindRec_idem]

theorem RelSt.streams {st₁ st₂ : ConnState} (h : RelSt st₁ st₂) :
    st₁.streams.map blindPair = st₂.streams.map blindPair := congrArg ConnState.streams h

theorem RelSt.buf {st₁ st₂ : ConnState} (h : RelSt st₁ st₂) : st₁.buf = st₂.buf := by
  have h' := congrArg ConnState.buf h
  exact h'

theorem RelSt.maxSid {st₁ st₂ : ConnState} (h : RelSt st₁ st₂) : st₁.maxSid = st₂.maxSid := by
  have h' := congrArg ConnState.maxSid h
  exact h'

theorem RelSt.cont {st₁ st₂ : ConnState} (h : RelSt st₁ st₂) : st₁.cont = st₂.cont := by
  have h' := congrArg ConnState.cont h
  exact h'

theorem RelSt.hpack {st₁ st₂ : ConnState} (h : RelSt st₁ st₂) : st₁.hpack = st₂.hpack := by
  have h' := congrArg ConnState.hpack h
  exact h'

theorem RelSt.initWindow {st₁ st₂ : ConnState} (h : RelSt st₁ st₂) : st₁.initWindow = st₂.initWindow := by
  have h' := congrArg ConnState.initWindow h
  exact h'

theorem RelSt.peerMaxFrame {st₁ st₂ : ConnState} (h : RelSt st₁ st₂) : st₁.peerMaxFrame = st₂.peerMaxFrame := by
  have h' := congrArg ConnState.peerMaxFrame h
  exact h'

theorem RelSt.connWindow {st₁ st₂ : ConnState} (h : RelSt st₁ st₂) : st₁.connWindow = st₂.connWindow := by
  have h' := congrArg ConnState.connWindow h
  exact h'

theorem RelSt.closed {st₁ st₂ : ConnState} (h : RelSt st₁ st₂) : st₁.closed = st₂.closed := by
  have h' := congrArg ConnState.closed h
  exact h'

theorem RelSt.prefaceLeft {st₁ st₂ : ConnState} (h : RelSt st₁ st₂) : st₁.prefaceLeft = st₂.prefaceLeft := by
  have h' := congrArg ConnState.prefaceLeft h
  exact h'

theorem RelSt.events {st₁ st₂ : ConnState} (h : RelSt st₁ st₂) : st₁.events = st₂.events := by
  have h' := congrArg ConnState.events h
  exact h'

theorem RelSt.observations {st₁ st₂ : ConnState} (h : RelSt st₁ st₂) : st₁.observations = st₂.observations := by
  have h' := congrArg ConnState.observations h
  exact h'

/-- `getStream` sees the same record up to blinding. -/
theorem RelSt.get {st₁ st₂ : ConnState} (h : RelSt st₁ st₂) (sid : Nat) :
    (Conn.getStream st₁ sid).map blindRec = (Conn.getStream st₂ sid).map blindRec := by
  have key : ∀ st : ConnState,
      (Conn.getStream st sid).map blindRec
        = ((st.streams.map blindPair).find? (fun q => q.1 == sid)).map (·.2) := by
    intro st
    simp only [Conn.getStream, List.find?_map, Option.map_map]
    rfl
  rw [key st₁, key st₂, h.streams]


/-- The body-clearing view is a TOTAL invariant of the relation: two prune-equal
records agree on every field except the body. -/
theorem blind_eq_body_clear {a b : StreamRec} (h : blindRec a = blindRec b) :
    ({ a with body := ([] : Bytes) } : StreamRec) = { b with body := ([] : Bytes) } := by
  rcases blindRec_cases h with rfl | ⟨_, _, hab⟩
  · rfl
  · exact hab

@[simp] theorem blindRec_default : blindRec ({} : StreamRec) = ({} : StreamRec) := rfl

theorem getD_map_blindRec (o : Option StreamRec) :
    (o.map blindRec).getD {} = blindRec (o.getD {}) := by cases o <;> rfl

theorem RelSt.getD {st₁ st₂ : ConnState} (h : RelSt st₁ st₂) (sid : Nat) :
    blindRec ((Conn.getStream st₁ sid).getD {}) = blindRec ((Conn.getStream st₂ sid).getD {}) := by
  rw [← getD_map_blindRec, ← getD_map_blindRec, h.get sid]

/-! ### Pruning commutes with the state constructors -/

theorem pruneBodies_setStream (st : ConnState) (sid : Nat) (sr : StreamRec) :
    pruneBodies (Conn.setStream st sid sr)
      = Conn.setStream (pruneBodies st) sid (blindRec sr) := by
  simp only [pruneBodies, Conn.setStream, List.map_cons, List.filter_map]
  rfl

theorem RelSt.setStream {st₁ st₂ : ConnState} (h : RelSt st₁ st₂) (sid : Nat)
    {sr₁ sr₂ : StreamRec} (hr : blindRec sr₁ = blindRec sr₂) :
    RelSt (Conn.setStream st₁ sid sr₁) (Conn.setStream st₂ sid sr₂) := by
  show pruneBodies (Conn.setStream st₁ sid sr₁) = pruneBodies (Conn.setStream st₂ sid sr₂)
  rw [pruneBodies_setStream, pruneBodies_setStream, h, hr]

theorem getStream_setStream_self (st : ConnState) (sid : Nat) (sr : StreamRec) :
    Conn.getStream (Conn.setStream st sid sr) sid = some sr := by
  simp [Conn.getStream, Conn.setStream]

/-! ### The typed error exits -/

theorem RelSt.connError {st₁ st₂ : ConnState} (h : RelSt st₁ st₂) (c : Nat) :
    pruneOut (Conn.connError st₁ c) = pruneOut (Conn.connError st₂ c) := by
  have hst : pruneBodies { st₁ with closed := true, buf := [], cont := none }
      = pruneBodies { st₂ with closed := true, buf := [], cont := none } := by
    show ({ pruneBodies st₁ with closed := true, buf := [], cont := none } : ConnState)
      = { pruneBodies st₂ with closed := true, buf := [], cont := none }
    rw [h]
  simp only [pruneOut, Conn.connError]
  rw [hst, h.maxSid]

theorem RelSt.streamError {st₁ st₂ : ConnState} (h : RelSt st₁ st₂) (sid c : Nat) :
    pruneOut (Conn.streamError st₁ sid c) = pruneOut (Conn.streamError st₂ sid c) := by
  have hrec := blind_eq_body_clear (h.getD sid)
  have hblind : blindRec { (Conn.getStream st₁ sid).getD {} with
        state := .closed, pending := [], req := none }
      = blindRec { (Conn.getStream st₂ sid).getD {} with
        state := .closed, pending := [], req := none } := by
    rw [blindRec_of (by rfl), blindRec_of (by rfl)]
    exact congrArg (fun r : StreamRec => { r with state := .closed, pending := [], req := none })
      hrec
  simp only [pruneOut, Conn.streamError, Prod.mk.injEq, and_true]
  exact h.setStream sid hblind


/-- Intro rule for the relation: prune-equal streams and equal everything else. -/
theorem relSt_of_fields {sa sb : ConnState}
    (hs : sa.streams.map blindPair = sb.streams.map blindPair)
    (h1 : sa.prefaceLeft = sb.prefaceLeft) (h2 : sa.buf = sb.buf) (h3 : sa.maxSid = sb.maxSid)
    (h4 : sa.cont = sb.cont) (h5 : sa.hpack = sb.hpack) (h6 : sa.initWindow = sb.initWindow)
    (h7 : sa.peerMaxFrame = sb.peerMaxFrame) (h8 : sa.connWindow = sb.connWindow)
    (h9 : sa.closed = sb.closed) (h10 : sa.events = sb.events)
    (h11 : sa.observations = sb.observations) : RelSt sa sb := by
  show pruneBodies sa = pruneBodies sb
  unfold pruneBodies
  cases sa; cases sb; simp_all

/-- Tactic: close a `RelSt` goal between two states built from prune-equal states by
field updates, by checking the fields pointwise. -/
macro "prune_rel_fields " hh:term : tactic =>
  `(tactic| refine relSt_of_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp [RelSt.streams $hh, RelSt.prefaceLeft $hh, RelSt.buf $hh, RelSt.maxSid $hh,
        RelSt.cont $hh, RelSt.hpack $hh, RelSt.initWindow $hh, RelSt.peerMaxFrame $hh,
        RelSt.connWindow $hh, RelSt.closed $hh, RelSt.events $hh, RelSt.observations $hh])

theorem pruneOut_mk {s₁ s₂ : ConnState} {o : Bytes} {c : Bool} (h : RelSt s₁ s₂) :
    pruneOut (s₁, o, c) = pruneOut (s₂, o, c) := by
  simp only [pruneOut, h]

theorem RelSt.obsUpd {sa sb : ConnState} (h : RelSt sa sb) (l : List ReqObs) :
    RelSt { sa with observations := l } { sb with observations := l } := by
  show ({ pruneBodies sa with observations := l } : ConnState)
    = { pruneBodies sb with observations := l }
  rw [h]

theorem RelSt.cwUpd {sa sb : ConnState} (h : RelSt sa sb) (c : Int) :
    RelSt { sa with connWindow := c } { sb with connWindow := c } := by
  show ({ pruneBodies sa with connWindow := c } : ConnState)
    = { pruneBodies sb with connWindow := c }
  rw [h]

/-! ### `respond` -/

theorem respond_congr (handler : Handler) (sid : Nat) (req : Req) {sa sb : ConnState}
    (h : RelSt sa sb)
    (hrec : (Conn.getStream sa sid).getD {} = (Conn.getStream sb sid).getD {}) :
    pruneOut (Conn.respond handler sa sid req)
      = pruneOut (Conn.respond handler sb sid req) := by
  simp only [Conn.respond, hrec, h.connWindow, h.peerMaxFrame, h.observations]
  have base : ∀ (l : List ReqObs), RelSt
      { sa with peerMaxFrame := sb.peerMaxFrame, connWindow := sb.connWindow, observations := l }
      { sb with observations := l } := by
    intro l
    refine relSt_of_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp [h.streams, h.prefaceLeft, h.buf, h.maxSid, h.cont, h.hpack, h.initWindow,
        h.closed, h.events]
  split
  · exact pruneOut_mk ((base _).setStream sid rfl)
  · split
    · exact pruneOut_mk (((base _).setStream sid rfl).cwUpd _)
    · exact pruneOut_mk (((base _).setStream sid rfl).cwUpd _)


/-! ### List-shaped consequences of the relation -/

theorem RelSt.anyStreams {sa sb : ConnState} (h : RelSt sa sb) (Q : Nat × StreamRec → Bool)
    (hQ : ∀ p, Q (blindPair p) = Q p) : sa.streams.any Q = sb.streams.any Q := by
  have hh := congrArg (fun l => List.any l Q) h.streams
  simpa [List.any_map, Function.comp_def, hQ] using hh

theorem RelSt.countPStreams {sa sb : ConnState} (h : RelSt sa sb) (Q : Nat × StreamRec → Bool)
    (hQ : ∀ p, Q (blindPair p) = Q p) : sa.streams.countP Q = sb.streams.countP Q := by
  have hh := congrArg (fun l => List.countP Q l) h.streams
  simpa [List.countP_map, Function.comp_def, hQ] using hh

theorem RelSt.activeStreams {sa sb : ConnState} (h : RelSt sa sb) :
    Conn.activeStreams sa = Conn.activeStreams sb := by
  simp only [Conn.activeStreams, ← List.countP_eq_length_filter]
  exact h.countPStreams (fun q => match q.2.state with | .closed => false | _ => true)
    (by intro p; simp)

theorem RelSt.pendingSids {sa sb : ConnState} (h : RelSt sa sb) :
    (sa.streams.filter (fun q => !q.2.pending.isEmpty)).map (·.1)
      = (sb.streams.filter (fun q => !q.2.pending.isEmpty)).map (·.1) := by
  have hh := congrArg
    (fun l => (List.filter (fun q => !q.2.pending.isEmpty) l).map (·.1)) h.streams
  simpa [List.filter_map, List.map_map, Function.comp_def] using hh

/-! ### `flushStream` / `flushAll` -/

theorem flushStream_congr {sa sb : ConnState} (h : RelSt sa sb) (sid : Nat) :
    (Conn.flushStream sa sid).2 = (Conn.flushStream sb sid).2
      ∧ RelSt (Conn.flushStream sa sid).1 (Conn.flushStream sb sid).1 := by
  have hg := h.get sid
  unfold Conn.flushStream
  cases hga : Conn.getStream sa sid with
  | none =>
    cases hgb : Conn.getStream sb sid with
    | none => exact ⟨by first | rfl | exact True.intro, h⟩
    | some sr₂ => rw [hga, hgb] at hg; simp at hg
  | some sr₁ =>
    cases hgb : Conn.getStream sb sid with
    | none => rw [hga, hgb] at hg; simp at hg
    | some sr₂ =>
      rw [hga, hgb] at hg
      simp only [Option.map_some, Option.some.injEq] at hg
      have hpend : sr₁.pending = sr₂.pending := by
        have := congrArg StreamRec.pending hg
        simpa using this
      have hwin : sr₁.window = sr₂.window := by
        have := congrArg StreamRec.window hg
        simpa using this
      simp only [hpend, hwin, h.connWindow, h.peerMaxFrame]
      by_cases hpe : sr₂.pending.isEmpty
      · simp only [hpe, if_pos]
        exact ⟨by first | rfl | exact True.intro, h⟩
      · simp only [hpe, Bool.false_eq_true, if_false]
        refine ⟨by first | rfl | exact True.intro, ?_⟩
        refine RelSt.cwUpd (h.setStream sid ?_) _
        rcases blindRec_cases hg with rfl | ⟨hc₁, hc₂, hcl⟩
        · rfl
        · obtain ⟨s1, w1, p1, r1, c1, rc1, ih1, ds1, b1, pr1⟩ := sr₁
          obtain ⟨s2, w2, p2, r2, c2, rc2, ih2, ds2, b2, pr2⟩ := sr₂
          simp_all [blindRec, bodyConsumed]


theorem flushFold_congr : ∀ (l : List Nat) (a b : ConnState × Bytes),
    RelSt a.1 b.1 → a.2 = b.2 →
    (l.foldl (fun acc sid =>
        let (st', o) := Conn.flushStream acc.1 sid
        (st', acc.2 ++ o)) a).2
      = (l.foldl (fun acc sid =>
        let (st', o) := Conn.flushStream acc.1 sid
        (st', acc.2 ++ o)) b).2
    ∧ RelSt (l.foldl (fun acc sid =>
        let (st', o) := Conn.flushStream acc.1 sid
        (st', acc.2 ++ o)) a).1
      (l.foldl (fun acc sid =>
        let (st', o) := Conn.flushStream acc.1 sid
        (st', acc.2 ++ o)) b).1 := by
  intro l
  induction l with
  | nil => intro a b h1 h2; exact ⟨h2, h1⟩
  | cons sid t ih =>
    intro a b h1 h2
    simp only [List.foldl_cons]
    refine ih _ _ ?_ ?_
    · exact (flushStream_congr h1 sid).2
    · simp only []
      rw [h2, (flushStream_congr h1 sid).1]

theorem flushAll_congr {sa sb : ConnState} (h : RelSt sa sb) :
    (Conn.flushAll sa).2 = (Conn.flushAll sb).2
      ∧ RelSt (Conn.flushAll sa).1 (Conn.flushAll sb).1 := by
  unfold Conn.flushAll
  simp only [h.pendingSids]
  exact flushFold_congr _ (sa, []) (sb, []) h rfl

/-! ### `applySettings` -/

theorem any_of_map_blind {l₁ l₂ : List (Nat × StreamRec)}
    (h : l₁.map blindPair = l₂.map blindPair) (Q : Nat × StreamRec → Bool)
    (hQ : ∀ p, Q (blindPair p) = Q p) : l₁.any Q = l₂.any Q := by
  have hh := congrArg (fun l => List.any l Q) h
  simpa [List.any_map, Function.comp_def, hQ] using hh

theorem bumpStreams_congr {sa sb : ConnState} (h : RelSt sa sb) (d : Int) :
    (sa.streams.map (fun q => (q.1, { q.2 with window := q.2.window + d }))).map blindPair
      = (sb.streams.map (fun q => (q.1, { q.2 with window := q.2.window + d }))).map blindPair := by
  have hcomm : ∀ p : Nat × StreamRec,
      blindPair (p.1, { p.2 with window := p.2.window + d })
        = ((blindPair p).1, { (blindPair p).2 with window := (blindPair p).2.window + d }) := by
    intro p
    have hw : bodyConsumed { p.2 with window := p.2.window + d } = bodyConsumed p.2 := rfl
    by_cases hc : bodyConsumed p.2 = true
    · rw [blindPair, blindPair, blindRec_of hc, blindRec_of (hw.trans hc)]
    · have hc' : bodyConsumed p.2 = false := by simpa using hc
      rw [blindPair, blindPair, blindRec_of_not hc', blindRec_of_not (hw.trans hc')]
  simp only [List.map_map, Function.comp_def, hcomm]
  have hh := congrArg (fun l => l.map (fun q : Nat × StreamRec =>
    (q.1, { q.2 with window := q.2.window + d }))) h.streams
  simpa [List.map_map, Function.comp_def] using hh

theorem applySettings_congr : ∀ (l : List (Nat × Nat)) {sa sb : ConnState}, RelSt sa sb →
    (Conn.applySettings sa l).map pruneBodies = (Conn.applySettings sb l).map pruneBodies := by
  intro l
  induction l with
  | nil => intro sa sb h; simp only [Conn.applySettings, Except.map, h]
  | cons pr t ih =>
    intro sa sb h
    obtain ⟨sid, v⟩ := pr
    unfold Conn.applySettings
    by_cases h2 : sid = 0x2
    · simp only [h2, if_pos]
      by_cases hv : v ≤ 1
      · simp only [hv, if_pos]; exact ih h
      · simp only [hv, if_false]
    · simp only [h2, if_false]
      by_cases h4 : sid = 0x4
      · simp only [h4, if_pos]
        by_cases hw : maxWindow < (v : Int)
        · simp only [hw, if_pos]
        · simp only [hw, if_false, h.initWindow]
          have hb := bumpStreams_congr h ((v : Int) - sb.initWindow)
          have hany := any_of_map_blind hb (fun q => decide (maxWindow < q.2.window))
            (by intro p; simp)
          simp only [hany]
          by_cases hov : (sb.streams.map
              (fun q => (q.1, { q.2 with window := q.2.window + ((v : Int) - sb.initWindow) }))).any
              (fun q => decide (maxWindow < q.2.window)) = true
          · simp only [hov, if_pos]
          · simp only [hov]
            refine ih ?_
            refine relSt_of_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
              simp [hb, h.prefaceLeft, h.buf, h.maxSid, h.cont, h.hpack,
                h.peerMaxFrame, h.connWindow, h.closed, h.events, h.observations]
      · simp only [h4, if_false]
        by_cases h5 : sid = 0x5
        · simp only [h5, if_pos]
          by_cases hr : v < 16384 || 16777215 < v
          · simp only [hr, if_pos]
          · simp only [hr]
            refine ih ?_
            refine relSt_of_fields ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
              simp [h.streams, h.prefaceLeft, h.buf, h.maxSid, h.cont, h.hpack,
                h.initWindow, h.connWindow, h.closed, h.events, h.observations]
        · simp only [h5, if_false]
          exact ih h


/-! ### Generic non-`streams` state updates -/

theorem RelSt.upd {sa sb : ConnState} (h : RelSt sa sb) (U : ConnState → ConnState)
    (hU : ∀ s, pruneBodies (U s) = U (pruneBodies s)) : RelSt (U sa) (U sb) := by
  show pruneBodies (U sa) = pruneBodies (U sb)
  rw [hU, hU, h]

theorem state_req_of_bodyConsumed {a : StreamRec} (h : bodyConsumed a = true) :
    a.state = Stream.StreamState.closed ∧ a.req = none := by
  simp only [bodyConsumed, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at h
  exact h

theorem eq_of_blindRec_of_not_closed {a b : StreamRec} (h : blindRec a = blindRec b)
    (hs : a.state ≠ Stream.StreamState.closed) : a = b := by
  rcases blindRec_cases h with rfl | ⟨hc₁, _, _⟩
  · rfl
  · exact absurd (state_req_of_bodyConsumed hc₁).1 hs

theorem bodyConsumed_freshStream (st : ConnState) (es : Bool) :
    bodyConsumed (Conn.freshStream st es) = false := by
  cases es <;> rfl

/-! ### `finishRequest` -/

theorem finishRequest_congr (hd : Hpack.HuffmanDecoder) (handler : Handler)
    {sa sb : ConnState} (h : RelSt sa sb) (sid : Nat) (es : Bool) (frag : Bytes) :
    pruneOut (Conn.finishRequest hd handler sa sid es frag)
      = pruneOut (Conn.finishRequest hd handler sb sid es frag) := by
  unfold Conn.finishRequest
  simp only [h.hpack, h.maxSid, h.initWindow, Conn.freshStream]
  cases hdec : Conn.decodeBlockV hd (frag.length + 1) sb.hpack frag {} false false with
  | error e => exact h.connError _
  | ok hc =>
    obtain ⟨head, ctx⟩ := hc
    simp only []
    have hA : RelSt { sa with cont := none, hpack := ctx, maxSid := max sb.maxSid sid, initWindow := sb.initWindow } { sb with cont := none, hpack := ctx, maxSid := max sb.maxSid sid, initWindow := sb.initWindow } := by
      prune_rel_fields h
    have hA' := hA.setStream sid (rfl : blindRec
      ({ state := Stream.stepState Stream.StreamState.idle (Stream.Event.recvHeaders es),
         window := sb.initWindow } : StreamRec) = _)
    by_cases hm : Conn.headMalformed head = true
    · simp only [if_pos hm]
      exact hA'.streamError _ _
    · simp only [if_neg hm]
      by_cases hes : es = true
      · simp only [if_pos hes]
        by_cases hcl : (Conn.declaredLen head).getD 0 ≠ 0
        · simp only [if_pos hcl]
          exact hA'.streamError _ _
        · simp only [if_neg hcl]
          refine respond_congr handler sid _ hA' ?_
          rw [getStream_setStream_self, getStream_setStream_self]
      · simp only [if_neg hes]
        rw [getStream_setStream_self, getStream_setStream_self]
        exact pruneOut_mk (hA'.setStream sid rfl)

/-! ### `finishTrailers` -/

theorem finishTrailers_congr (hd : Hpack.HuffmanDecoder) (handler : Handler)
    {sa sb : ConnState} (h : RelSt sa sb) (sid : Nat) (es : Bool) (frag : Bytes) :
    pruneOut (Conn.finishTrailers hd handler sa sid es frag)
      = pruneOut (Conn.finishTrailers hd handler sb sid es frag) := by
  unfold Conn.finishTrailers
  simp only [h.hpack]
  cases hdec : Conn.decodeBlockV hd (frag.length + 1) sb.hpack frag {} false false with
  | error e => exact h.connError _
  | ok hc =>
    obtain ⟨head, ctx⟩ := hc
    simp only []
    have hA : RelSt { sa with cont := none, hpack := ctx } { sb with cont := none, hpack := ctx } :=
      h.upd (fun s => { s with cont := none, hpack := ctx }) (fun _ => rfl)
    by_cases hes : (!es) = true
    · simp only [if_pos hes]
      exact hA.connError _
    · simp only [if_neg hes]
      have hg := hA.get sid
      cases hga : Conn.getStream { sa with cont := none, hpack := ctx } sid with
      | none =>
        cases hgb : Conn.getStream { sb with cont := none, hpack := ctx } sid with
        | none => exact hA.connError _
        | some sr₂ => rw [hga, hgb] at hg; simp at hg
      | some sr₁ =>
        cases hgb : Conn.getStream { sb with cont := none, hpack := ctx } sid with
        | none => rw [hga, hgb] at hg; simp at hg
        | some sr₂ =>
          rw [hga, hgb] at hg
          simp only [Option.map_some, Option.some.injEq] at hg
          rcases blindRec_cases hg with rfl | ⟨hc₁, hc₂, hcl⟩
          · by_cases htm : Conn.trailersMalformed head = true
            · simp only [if_pos htm]; exact (hA.setStream sid rfl).streamError _ _
            · simp only [if_neg htm]
              cases hreq : sr₁.req with
              | none => exact (hA.setStream sid rfl).streamError _ _
              | some req =>
                cases hclen : sr₁.clen with
                | none =>
                  refine respond_congr handler sid _ (hA.setStream sid rfl) ?_
                  rw [getStream_setStream_self, getStream_setStream_self]
                | some n =>
                  by_cases hn : n ≠ sr₁.recvd
                  · simp only [if_pos hn]; exact (hA.setStream sid rfl).streamError _ _
                  · simp only [if_neg hn]
                    refine respond_congr handler sid _ (hA.setStream sid rfl) ?_
                    rw [getStream_setStream_self, getStream_setStream_self]
          · have hs₁ := state_req_of_bodyConsumed hc₁
            have hs₂ := state_req_of_bodyConsumed hc₂
            have hblind : blindRec { sr₁ with
                  state := Stream.stepState sr₁.state (Stream.Event.recvHeaders true),
                  req := none }
                = blindRec { sr₂ with
                  state := Stream.stepState sr₂.state (Stream.Event.recvHeaders true),
                  req := none } := by
              rw [hs₁.1, hs₂.1, Stream.stepState_closed]
              rw [blindRec_of (by simp [bodyConsumed]), blindRec_of (by simp [bodyConsumed])]
              exact congrArg (fun r : StreamRec => { r with
                state := Stream.StreamState.closed, req := none }) hcl
            by_cases htm : Conn.trailersMalformed head = true
            · simp only [if_pos htm, hs₁.2, hs₂.2]
              exact (hA.setStream sid hblind).streamError _ _
            · simp only [if_neg htm, hs₁.2, hs₂.2]
              exact (hA.setStream sid hblind).streamError _ _


theorem pruneOut_pair {A₁ A₂ : ConnState} {o₁ o₂ : Bytes} {c : Bool}
    (hs : RelSt A₁ A₂) (ho : o₁ = o₂) : pruneOut (A₁, o₁, c) = pruneOut (A₂, o₂, c) := by
  simp only [pruneOut, hs, ho]

theorem blindRec_window_upd {a b : StreamRec} (h : blindRec a = blindRec b) (w : Int) :
    blindRec { a with window := w } = blindRec { b with window := w } := by
  rcases blindRec_cases h with rfl | ⟨hc₁, hc₂, hcl⟩
  · rfl
  · rw [blindRec_of (show bodyConsumed { a with window := w } = true from hc₁),
        blindRec_of (show bodyConsumed { b with window := w } = true from hc₂)]
    exact congrArg (fun r : StreamRec => { r with window := w }) hcl

theorem blindRec_reset {a b : StreamRec} (h : blindRec a = blindRec b) :
    blindRec { a with state := Stream.StreamState.closed, pending := [], req := none }
      = blindRec { b with state := Stream.StreamState.closed, pending := [], req := none } := by
  rw [blindRec_of (by rfl), blindRec_of (by rfl)]
  exact congrArg
    (fun r : StreamRec => { r with state := Stream.StreamState.closed, pending := [], req := none })
    (blind_eq_body_clear h)

/-! ### The per-frame core -/

theorem handleFrame_congr (hd : Hpack.HuffmanDecoder) (handler : Handler)
    {sa sb : ConnState} (h : RelSt sa sb) (hdr : FrameHeader) (payload : Bytes) :
    pruneOut (Conn.handleFrame hd handler sa hdr payload)
      = pruneOut (Conn.handleFrame hd handler sb hdr payload) := by
  unfold Conn.handleFrame
  cases hcont : sa.cont with
  | some c =>
    have hcb : sb.cont = some c := by rw [← h.cont]; exact hcont
    simp only [hcb]
    by_cases hct : (decide (hdr.frameType = 0x9) && decide (hdr.streamId = c.sid)) = true
    · simp only [if_pos hct]
      by_cases heh : flagSet hdr.flags 2 = true
      · simp only [if_pos heh]
        by_cases htr : c.trailer = true
        · simp only [if_pos htr]; exact finishTrailers_congr hd handler h _ _ _
        · simp only [if_neg htr]; exact finishRequest_congr hd handler h _ _ _
      · simp only [if_neg heh]
        exact pruneOut_mk (h.upd
          (fun s => { s with cont := some { c with frag := c.frag ++ payload } }) (fun _ => rfl))
    · simp only [if_neg hct]; exact h.connError _
  | none =>
    have hcb : sb.cont = none := by rw [← h.cont]; exact hcont
    simp only [hcb]
    by_cases h0 : hdr.frameType = 0x0
    · -- DATA (§6.1)
      simp only [if_pos h0]
      by_cases hs0 : hdr.streamId = 0
      · simp only [if_pos hs0]; exact h.connError _
      · simp only [if_neg hs0]
        cases hsp : Conn.stripPadding (flagSet hdr.flags 3) payload with
        | none => exact h.connError _
        | some data =>
          simp only []
          have hg := h.get hdr.streamId
          cases hga : Conn.getStream sa hdr.streamId with
          | none =>
            cases hgb : Conn.getStream sb hdr.streamId with
            | none =>
              simp only []
              by_cases hm : sa.maxSid < hdr.streamId
              · simp only [if_pos hm,
                  if_pos (show sb.maxSid < hdr.streamId by rw [← h.maxSid]; exact hm)]
                exact h.connError _
              · simp only [if_neg hm,
                  if_neg (show ¬ sb.maxSid < hdr.streamId by rw [← h.maxSid]; exact hm)]
                exact h.connError _
            | some sr₂ => rw [hga, hgb] at hg; simp at hg
          | some sr₁ =>
            cases hgb : Conn.getStream sb hdr.streamId with
            | none => rw [hga, hgb] at hg; simp at hg
            | some sr₂ =>
              rw [hga, hgb] at hg
              simp only [Option.map_some, Option.some.injEq] at hg
              simp only []
              by_cases hclosed : sr₁.state = Stream.StreamState.closed
              · have hcl₂ : sr₂.state = Stream.StreamState.closed := by
                  have := congrArg StreamRec.state hg
                  simp only [blindRec_state] at this
                  rw [← this]; exact hclosed
                simp only [hclosed, hcl₂, Stream.recvData_closed]
                exact h.connError _
              · have heq : sr₁ = sr₂ := eq_of_blindRec_of_not_closed hg hclosed
                subst heq
                cases hstep : Stream.step sr₁.state
                    (Stream.Event.recvData (flagSet hdr.flags 0)) with
                | protocolError => exact h.connError _
                | streamClosed => exact h.connError _
                | next s' =>
                  by_cases hes : flagSet hdr.flags 0 = true
                  · simp only [if_pos hes]
                    cases hreq : sr₁.req with
                    | none => exact (h.setStream _ rfl).streamError _ _
                    | some req =>
                      cases hclen : sr₁.clen with
                      | none =>
                        refine respond_congr handler _ _ (h.setStream _ rfl) ?_
                        rw [getStream_setStream_self, getStream_setStream_self]
                      | some n =>
                        by_cases hn : n ≠ sr₁.recvd + data.length
                        · simp only [if_pos hn]; exact (h.setStream _ rfl).streamError _ _
                        · simp only [if_neg hn]
                          refine respond_congr handler _ _ (h.setStream _ rfl) ?_
                          rw [getStream_setStream_self, getStream_setStream_self]
                  · simp only [if_neg hes]
                    exact pruneOut_mk (h.setStream _ rfl)
    · simp only [if_neg h0]
      by_cases h1 : hdr.frameType = 0x1
      · -- HEADERS (§6.2)
        simp only [if_pos h1]
        by_cases hs0 : hdr.streamId = 0
        · simp only [if_pos hs0]; exact h.connError _
        · simp only [if_neg hs0]
          cases hsp : Conn.stripPadding (flagSet hdr.flags 3) payload with
          | none => exact h.streamError _ _
          | some body =>
            simp only []
            by_cases hp5 : (flagSet hdr.flags 5 && decide (body.length < 5)) = true
            · simp only [if_pos hp5]; exact h.connError _
            · simp only [if_neg hp5]
              by_cases hdep : (flagSet hdr.flags 5 &&
                  decide (Conn.readU32 body % 2 ^ 31 = hdr.streamId)) = true
              · simp only [if_pos hdep]; exact h.streamError _ _
              · simp only [if_neg hdep]
                have hg := h.get hdr.streamId
                cases hga : Conn.getStream sa hdr.streamId with
                | none =>
                  cases hgb : Conn.getStream sb hdr.streamId with
                  | some sr₂ => rw [hga, hgb] at hg; simp at hg
                  | none =>
                    simp only []
                    by_cases hev : hdr.streamId % 2 = 0
                    · simp only [if_pos hev]; exact h.connError _
                    · simp only [if_neg hev]
                      by_cases hle : hdr.streamId ≤ sa.maxSid
                      · simp only [if_pos hle,
                          if_pos (show hdr.streamId ≤ sb.maxSid by rw [← h.maxSid]; exact hle)]
                        exact h.connError _
                      · simp only [if_neg hle,
                          if_neg (show ¬ hdr.streamId ≤ sb.maxSid by rw [← h.maxSid]; exact hle)]
                        by_cases hcc : Conn.ourMaxConcurrentStreams ≤ Conn.activeStreams sa
                        · simp only [if_pos hcc, if_pos (show Conn.ourMaxConcurrentStreams
                            ≤ Conn.activeStreams sb by rw [← h.activeStreams]; exact hcc)]
                          exact (h.upd (fun s => { s with
                            maxSid := max s.maxSid hdr.streamId, cont := none })
                            (fun _ => rfl)).streamError _ _
                        · simp only [if_neg hcc, if_neg (show ¬ Conn.ourMaxConcurrentStreams
                            ≤ Conn.activeStreams sb by rw [← h.activeStreams]; exact hcc)]
                          by_cases heh : flagSet hdr.flags 2 = true
                          · simp only [if_pos heh]
                            exact finishRequest_congr hd handler h _ _ _
                          · simp only [if_neg heh]
                            exact pruneOut_mk (h.upd (fun s => { s with
                              maxSid := max s.maxSid hdr.streamId,
                              cont := some ⟨hdr.streamId, flagSet hdr.flags 0, false,
                                if flagSet hdr.flags 5 = true then body.drop 5 else body⟩ })
                              (fun _ => rfl))
                | some sr₁ =>
                  cases hgb : Conn.getStream sb hdr.streamId with
                  | none => rw [hga, hgb] at hg; simp at hg
                  | some sr₂ =>
                    rw [hga, hgb] at hg
                    simp only [Option.map_some, Option.some.injEq] at hg
                    simp only []
                    by_cases hclosed : sr₁.state = Stream.StreamState.closed
                    · have hcl₂ : sr₂.state = Stream.StreamState.closed := by
                        have := congrArg StreamRec.state hg
                        simp only [blindRec_state] at this
                        rw [← this]; exact hclosed
                      simp only [hclosed, hcl₂]
                      exact h.connError _
                    · have heq : sr₁ = sr₂ := eq_of_blindRec_of_not_closed hg hclosed
                      subst heq
                      cases hst : sr₁.state with
                      | idle => exact h.connError _
                      | reservedLocal => exact h.connError _
                      | reservedRemote => exact h.connError _
                      | halfClosedRemote => exact h.connError _
                      | closed => exact h.connError _
                      | «open» =>
                        by_cases hdt : Ext.detectTrailers sr₁.initialHeaders sr₁.dataSeen = true
                        · simp only [if_pos hdt]
                          have hev := h.upd (fun s => { s with
                            events := s.events ++ [Ext.Event.trailers hdr.streamId],
                            cont := none }) (fun _ => rfl)
                          by_cases heh : flagSet hdr.flags 2 = true
                          · simp only [if_pos heh]
                            exact finishTrailers_congr hd handler hev _ _ _
                          · simp only [if_neg heh]
                            exact pruneOut_mk (hev.upd (fun s => { s with
                              cont := some ⟨hdr.streamId, flagSet hdr.flags 0, true,
                                if flagSet hdr.flags 5 = true then body.drop 5 else body⟩ })
                              (fun _ => rfl))
                        · simp only [if_neg hdt]; exact h.connError _
                      | halfClosedLocal =>
                        by_cases hdt : Ext.detectTrailers sr₁.initialHeaders sr₁.dataSeen = true
                        · simp only [if_pos hdt]
                          have hev := h.upd (fun s => { s with
                            events := s.events ++ [Ext.Event.trailers hdr.streamId],
                            cont := none }) (fun _ => rfl)
                          by_cases heh : flagSet hdr.flags 2 = true
                          · simp only [if_pos heh]
                            exact finishTrailers_congr hd handler hev _ _ _
                          · simp only [if_neg heh]
                            exact pruneOut_mk (hev.upd (fun s => { s with
                              cont := some ⟨hdr.streamId, flagSet hdr.flags 0, true,
                                if flagSet hdr.flags 5 = true then body.drop 5 else body⟩ })
                              (fun _ => rfl))
                        · simp only [if_neg hdt]; exact h.connError _
      · simp only [if_neg h1]
        by_cases h2 : hdr.frameType = 0x2
        · -- PRIORITY (§6.3)
          simp only [if_pos h2]
          by_cases hs0 : hdr.streamId = 0
          · simp only [if_pos hs0]; exact h.connError _
          · simp only [if_neg hs0]
            by_cases hlen : hdr.length ≠ 5
            · simp only [if_pos hlen]; exact h.streamError _ _
            · simp only [if_neg hlen]
              by_cases hdep : Conn.readU32 payload % 2 ^ 31 = hdr.streamId
              · simp only [if_pos hdep]; exact h.streamError _ _
              · simp only [if_neg hdep]; exact pruneOut_mk h
        · simp only [if_neg h2]
          by_cases h3 : hdr.frameType = 0x3
          · -- RST_STREAM (§6.4)
            simp only [if_pos h3]
            by_cases hs0 : hdr.streamId = 0
            · simp only [if_pos hs0]; exact h.connError _
            · simp only [if_neg hs0]
              by_cases hlen : hdr.length ≠ 4
              · simp only [if_pos hlen]; exact h.connError _
              · simp only [if_neg hlen]
                have hg := h.get hdr.streamId
                cases hga : Conn.getStream sa hdr.streamId with
                | none =>
                  cases hgb : Conn.getStream sb hdr.streamId with
                  | some sr₂ => rw [hga, hgb] at hg; simp at hg
                  | none =>
                    simp only []
                    by_cases hm : sa.maxSid < hdr.streamId
                    · simp only [if_pos hm,
                        if_pos (show sb.maxSid < hdr.streamId by rw [← h.maxSid]; exact hm)]
                      exact h.connError _
                    · simp only [if_neg hm,
                        if_neg (show ¬ sb.maxSid < hdr.streamId by rw [← h.maxSid]; exact hm)]
                      exact pruneOut_mk h
                | some sr₁ =>
                  cases hgb : Conn.getStream sb hdr.streamId with
                  | none => rw [hga, hgb] at hg; simp at hg
                  | some sr₂ =>
                    rw [hga, hgb] at hg
                    simp only [Option.map_some, Option.some.injEq] at hg
                    simp only []
                    exact pruneOut_mk (h.setStream _ (blindRec_reset hg))
          · simp only [if_neg h3]
            by_cases h4 : hdr.frameType = 0x4
            · -- SETTINGS (§6.5)
              simp only [if_pos h4]
              by_cases hs0 : hdr.streamId ≠ 0
              · simp only [if_pos hs0]; exact h.connError _
              · simp only [if_neg hs0]
                by_cases hack : flagSet hdr.flags 0 = true
                · simp only [if_pos hack]
                  by_cases hlen : hdr.length ≠ 0
                  · simp only [if_pos hlen]; exact h.connError _
                  · simp only [if_neg hlen]; exact pruneOut_mk h
                · simp only [if_neg hack]
                  by_cases hlen : hdr.length % 6 ≠ 0
                  · simp only [if_pos hlen]; exact h.connError _
                  · simp only [if_neg hlen]
                    have hap := applySettings_congr (Conn.settingsPairs payload) h
                    cases hsa : Conn.applySettings sa (Conn.settingsPairs payload) with
                    | error e =>
                      cases hsb : Conn.applySettings sb (Conn.settingsPairs payload) with
                      | error e' =>
                        rw [hsa, hsb] at hap
                        simp only [Except.map] at hap
                        cases hap
                        exact h.connError _
                      | ok s' => rw [hsa, hsb] at hap; simp [Except.map] at hap
                    | ok s₁ =>
                      cases hsb : Conn.applySettings sb (Conn.settingsPairs payload) with
                      | error e' => rw [hsa, hsb] at hap; simp [Except.map] at hap
                      | ok s₂ =>
                        rw [hsa, hsb] at hap
                        simp only [Except.map, Except.ok.injEq] at hap
                        have hfl := flushAll_congr (sa := s₁) (sb := s₂) hap
                        exact pruneOut_pair hfl.2 (by rw [hfl.1])
            · simp only [if_neg h4]
              by_cases h5 : hdr.frameType = 0x5
              · simp only [if_pos h5]; exact h.connError _
              · simp only [if_neg h5]
                by_cases h6 : hdr.frameType = 0x6
                · -- PING (§6.7)
                  simp only [if_pos h6]
                  by_cases hs0 : hdr.streamId ≠ 0
                  · simp only [if_pos hs0]; exact h.connError _
                  · simp only [if_neg hs0]
                    by_cases hlen : hdr.length ≠ 8
                    · simp only [if_pos hlen]; exact h.connError _
                    · simp only [if_neg hlen]
                      by_cases hack : flagSet hdr.flags 0 = true
                      · simp only [if_pos hack]; exact pruneOut_mk h
                      · simp only [if_neg hack]; exact pruneOut_mk h
                · simp only [if_neg h6]
                  by_cases h7 : hdr.frameType = 0x7
                  · -- GOAWAY (§6.8)
                    simp only [if_pos h7]
                    by_cases hs0 : hdr.streamId ≠ 0
                    · simp only [if_pos hs0]; exact h.connError _
                    · simp only [if_neg hs0]; exact pruneOut_mk h
                  · simp only [if_neg h7]
                    by_cases h8 : hdr.frameType = 0x8
                    · -- WINDOW_UPDATE (§6.9)
                      simp only [if_pos h8]
                      by_cases hlen : hdr.length ≠ 4
                      · simp only [if_pos hlen]; exact h.connError _
                      · simp only [if_neg hlen]
                        by_cases hs0 : hdr.streamId = 0
                        · simp only [if_pos hs0]
                          by_cases hinc : ((Conn.readU32 payload % 2 ^ 31 : Nat) : Int) = 0
                          · simp only [if_pos hinc]; exact h.connError _
                          · simp only [if_neg hinc]
                            by_cases hov : Conn.maxWindow <
                                sa.connWindow + ((Conn.readU32 payload % 2 ^ 31 : Nat) : Int)
                            · simp only [if_pos hov, if_pos (show Conn.maxWindow <
                                sb.connWindow + ((Conn.readU32 payload % 2 ^ 31 : Nat) : Int) by
                                  rw [← h.connWindow]; exact hov)]
                              exact h.connError _
                            · simp only [if_neg hov, if_neg (show ¬ (Conn.maxWindow <
                                sb.connWindow + ((Conn.readU32 payload % 2 ^ 31 : Nat) : Int)) by
                                  rw [← h.connWindow]; exact hov)]
                              have hfl := flushAll_congr (h.upd (fun s => { s with
                                connWindow := s.connWindow +
                                  ((Conn.readU32 payload % 2 ^ 31 : Nat) : Int),
                                cont := none }) (fun _ => rfl))
                              exact pruneOut_pair hfl.2 (by rw [hfl.1])
                        · simp only [if_neg hs0]
                          have hg := h.get hdr.streamId
                          cases hga : Conn.getStream sa hdr.streamId with
                          | none =>
                            cases hgb : Conn.getStream sb hdr.streamId with
                            | some sr₂ => rw [hga, hgb] at hg; simp at hg
                            | none =>
                              simp only []
                              by_cases hm : sa.maxSid < hdr.streamId
                              · simp only [if_pos hm,
                                  if_pos (show sb.maxSid < hdr.streamId by
                                    rw [← h.maxSid]; exact hm)]
                                exact h.connError _
                              · simp only [if_neg hm,
                                  if_neg (show ¬ sb.maxSid < hdr.streamId by
                                    rw [← h.maxSid]; exact hm)]
                                exact pruneOut_mk h
                          | some sr₁ =>
                            cases hgb : Conn.getStream sb hdr.streamId with
                            | none => rw [hga, hgb] at hg; simp at hg
                            | some sr₂ =>
                              rw [hga, hgb] at hg
                              simp only [Option.map_some, Option.some.injEq] at hg
                              simp only []
                              have hw : sr₁.window = sr₂.window := by
                                have := congrArg StreamRec.window hg
                                simpa using this
                              simp only [hw]
                              by_cases hinc : ((Conn.readU32 payload % 2 ^ 31 : Nat) : Int) = 0
                              · simp only [if_pos hinc]; exact h.streamError _ _
                              · simp only [if_neg hinc]
                                by_cases hov : Conn.maxWindow <
                                    sr₂.window + ((Conn.readU32 payload % 2 ^ 31 : Nat) : Int)
                                · simp only [if_pos hov]; exact h.streamError _ _
                                · simp only [if_neg hov]
                                  have hfl := flushStream_congr
                                    (h.setStream hdr.streamId (blindRec_window_upd hg
                                      (sr₂.window +
                                        ((Conn.readU32 payload % 2 ^ 31 : Nat) : Int))))
                                    hdr.streamId
                                  exact pruneOut_pair hfl.2 (by rw [hfl.1])
                    · simp only [if_neg h8]
                      by_cases h9 : hdr.frameType = 0x9
                      · simp only [if_pos h9]; exact h.connError _
                      · simp only [if_neg h9]
                        by_cases ha : hdr.frameType = 0x0a
                        · -- ALTSVC (RFC 7838)
                          simp only [if_pos ha]
                          cases hal : Ext.decodeAltSvc payload with
                          | none => exact pruneOut_mk h
                          | some ov =>
                            obtain ⟨origin, value⟩ := ov
                            simp only []
                            by_cases hv : ((hdr.streamId == 0) == origin.isEmpty) = true
                            · simp only [if_pos hv]; exact pruneOut_mk h
                            · simp only [if_neg hv]
                              exact pruneOut_mk (h.upd (fun s => { s with
                                events := s.events ++
                                  [Ext.Event.altSvc hdr.streamId origin value],
                                cont := none }) (fun _ => rfl))
                        · simp only [if_neg ha]
                          by_cases hcx : hdr.frameType = 0x0c
                          · -- ORIGIN (RFC 8336)
                            simp only [if_pos hcx]
                            by_cases hs0 : hdr.streamId ≠ 0
                            · simp only [if_pos hs0]; exact pruneOut_mk h
                            · simp only [if_neg hs0]
                              cases hor : Ext.decodeOrigins (payload.length + 1) payload with
                              | none => exact pruneOut_mk h
                              | some origins =>
                                exact pruneOut_mk (h.upd (fun s => { s with
                                  events := s.events ++ [Ext.Event.origin origins],
                                  cont := none }) (fun _ => rfl))
                          · simp only [if_neg hcx]; exact pruneOut_mk h


/-! ### The frame pump and the whole feed -/

theorem pump_congr (hd : Hpack.HuffmanDecoder) (handler : Handler) :
    ∀ (fuel : Nat) {sa sb : ConnState}, RelSt sa sb →
      pruneOut (Conn.pump hd handler fuel sa) = pruneOut (Conn.pump hd handler fuel sb) := by
  intro fuel
  induction fuel with
  | zero => intro sa sb h; exact pruneOut_mk h
  | succ n ih =>
    intro sa sb h
    unfold Conn.pump
    simp only [h.buf]
    cases hph : parseHeader sb.buf with
    | none => exact pruneOut_mk h
    | some hdr =>
      simp only []
      by_cases hsz : Conn.ourMaxFrameSize < hdr.length
      · simp only [if_pos hsz]; exact h.connError _
      · simp only [if_neg hsz]
        by_cases hshort : sb.buf.length < 9 + hdr.length
        · simp only [if_pos hshort]; exact pruneOut_mk h
        · simp only [if_neg hshort]
          have hbuf : RelSt { sa with buf := sb.buf.drop (9 + hdr.length) } { sb with buf := sb.buf.drop (9 + hdr.length) } :=
            h.upd (fun s => { s with buf := sb.buf.drop (9 + hdr.length) }) (fun _ => rfl)
          have hcf := handleFrame_congr hd handler hbuf hdr ((sb.buf.drop 9).take hdr.length)
          simp only [pruneOut, Prod.mk.injEq] at hcf
          obtain ⟨hs, hb, hc⟩ := hcf
          simp only [hc]
          by_cases hclose : (Conn.handleFrame hd handler
              { sb with buf := sb.buf.drop (9 + hdr.length) } hdr
              ((sb.buf.drop 9).take hdr.length)).2.2 = true
          · simp only [if_pos hclose]
            exact pruneOut_pair hs hb
          · simp only [if_neg hclose]
            have hp := ih hs
            simp only [pruneOut, Prod.mk.injEq] at hp
            obtain ⟨hp1, hp2, hp3⟩ := hp
            simp only [pruneOut, hp1, hp2, hp3, hb]

/-- ★ **The engine cannot tell a pruned connection from an unpruned one.** If two
connection states differ ONLY in the assembled request bodies of streams whose request
was already dispatched (`bodyConsumed`), then feeding them the same octets produces
BYTE-IDENTICAL output, the SAME close decision, and successor states that again differ
only in consumed bodies. -/
theorem feed_congr (hd : Hpack.HuffmanDecoder) (handler : Handler)
    {sa sb : ConnState} (h : RelSt sa sb) (input : Bytes) :
    pruneOut (Conn.feed hd handler sa input) = pruneOut (Conn.feed hd handler sb input) := by
  unfold Conn.feed
  simp only [h.closed, h.prefaceLeft, h.buf]
  by_cases hcl : sb.closed = true
  · simp only [if_pos hcl]
    refine pruneOut_mk ?_
    prune_rel_fields h
  · simp only [if_neg hcl]
    by_cases hpre : 0 < sb.prefaceLeft
    · simp only [if_pos hpre]
      by_cases hgot : input.take (min sb.prefaceLeft input.length)
          ≠ (Conn.clientPreface.drop (Conn.clientPreface.length - sb.prefaceLeft)).take
              (min sb.prefaceLeft input.length)
      · simp only [if_pos hgot]
        refine pruneOut_mk ?_
        prune_rel_fields h
      · simp only [if_neg hgot]
        by_cases hdone : sb.prefaceLeft - min sb.prefaceLeft input.length = 0
        · simp only [if_pos hdone]
          have hst : RelSt { sa with prefaceLeft := sb.prefaceLeft - min sb.prefaceLeft input.length, buf := sb.buf ++ input.drop (min sb.prefaceLeft input.length), closed := sb.closed } { sb with prefaceLeft := sb.prefaceLeft - min sb.prefaceLeft input.length, buf := sb.buf ++ input.drop (min sb.prefaceLeft input.length) } := by
            prune_rel_fields h
          have hp := pump_congr hd handler
            ((sb.buf ++ input.drop (min sb.prefaceLeft input.length)).length + 1) hst
          simp only [pruneOut, Prod.mk.injEq] at hp
          obtain ⟨hp1, hp2, hp3⟩ := hp
          simp only [pruneOut, hp1, hp2, hp3]
        · simp only [if_neg hdone]
          refine pruneOut_mk ?_
          prune_rel_fields h
    · simp only [if_neg hpre]
      refine pump_congr hd handler ((sb.buf ++ input).length + 1) ?_
      prune_rel_fields h


/-! ### The headline forms -/

/-- ★ **Pruning commutes with the engine, up to pruning.** Running the engine on a state
whose consumed bodies were cleared emits the SAME octets and the same close decision, and
lands in a state that differs from the unpruned run only in consumed bodies. -/
theorem feed_pruneBodies (hd : Hpack.HuffmanDecoder) (handler : Handler)
    (st : ConnState) (input : Bytes) :
    pruneOut (Conn.feed hd handler (pruneBodies st) input)
      = pruneOut (Conn.feed hd handler st input) :=
  feed_congr hd handler (pruneBodies_idem st) input

/-- ★ **Not one served octet moves.** -/
theorem feed_pruneBodies_bytes (hd : Hpack.HuffmanDecoder) (handler : Handler)
    (st : ConnState) (input : Bytes) :
    (Conn.feed hd handler (pruneBodies st) input).2 = (Conn.feed hd handler st input).2 := by
  have h := feed_pruneBodies hd handler st input
  simp only [pruneOut, Prod.mk.injEq] at h
  exact Prod.ext h.2.1 h.2.2

/-- ★ …and the successor states agree once both are pruned. -/
theorem feed_pruneBodies_state (hd : Hpack.HuffmanDecoder) (handler : Handler)
    (st : ConnState) (input : Bytes) :
    pruneBodies (Conn.feed hd handler (pruneBodies st) input).1
      = pruneBodies (Conn.feed hd handler st input).1 := by
  have h := feed_pruneBodies hd handler st input
  simp only [pruneOut, Prod.mk.injEq] at h
  exact h.1

/-! ### Why the NAIVE commutation is the wrong statement

`feed cfg (pruneBodies st) = pruneBodies (feed cfg st)` — pruning pushed through the
engine with NO outer prune on the left — is FALSE, and it is false for a reason that has
nothing to do with the engine reading a pruned body: the engine CREATES consumed bodies
as it runs (a RST_STREAM, or a dispatched response, leaves `state = .closed`, `req = none`
and the assembled body still on the record). The right-hand side prunes those; the
left-hand side, whose prune ran BEFORE the step, cannot. The counterexample below is a
single RST_STREAM (no HPACK involved). -/

private def pruneHd : Hpack.HuffmanDecoder := ⟨fun _ => none⟩
private def pruneHandler : Handler := fun _ => { block := [], body := [] }

/-- One open stream carrying an assembled body: NOT consumed, so `pruneBodies` leaves it. -/
private def naiveSt : ConnState :=
  { prefaceLeft := 0, maxSid := 1,
    streams := [(1, { state := .open, req := none, body := [7] })] }

/-- A well-formed RST_STREAM(1, NO_ERROR): closes the stream, keeping its body. -/
private def naiveInput : Bytes := Conn.rstStreamFrame 1 0

/-- ★ The naive commutation FAILS: after the step the left side still carries the body the
right side has just pruned. (`decide` — the kernel evaluates both engine runs.) -/
theorem feed_pruneBodies_naive_false :
    (Conn.feed pruneHd pruneHandler (pruneBodies naiveSt) naiveInput).1.streams.map
        (fun p => p.2.body)
      ≠ (pruneBodies (Conn.feed pruneHd pruneHandler naiveSt naiveInput).1).streams.map
        (fun p => p.2.body) := by
  decide

/-- …and the two sides really are `[[7]]` vs `[[]]`. -/
example : (Conn.feed pruneHd pruneHandler (pruneBodies naiveSt) naiveInput).1.streams.map
    (fun p => p.2.body) = [[7]] := by decide

example : (pruneBodies (Conn.feed pruneHd pruneHandler naiveSt naiveInput).1).streams.map
    (fun p => p.2.body) = [[]] := by decide

#print axioms feed_congr
#print axioms feed_pruneBodies
#print axioms feed_pruneBodies_bytes
#print axioms feed_pruneBodies_naive_false

end Conn
end H2
