import H2.Frame
import H2.Hpack
import H2.Stream

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
def errCompression : Nat := 0x9

/-! ## Our advertised limits (we send an empty SETTINGS, so RFC defaults) -/

/-- Our `SETTINGS_MAX_FRAME_SIZE` (RFC 9113 §4.2 default). -/
def ourMaxFrameSize : Nat := 16384

/-- Our `SETTINGS_HEADER_TABLE_SIZE` (RFC 7541 §6.3 bound on peer size
updates; RFC 9113 §6.5.2 default). -/
def ourHeaderTableSize : Nat := 4096

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

/-- The server connection preface: an empty SETTINGS frame (§3.4/§6.5). -/
def serverSettings : Bytes := frameHdr 0 0x4 0 0

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
deriving Repr

/-- The application's answer: a pre-encoded HPACK response header block and the
response body. The engine frames both (HEADERS + paced DATA). -/
structure Rsp where
  block : Bytes
  body : Bytes
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
  if rsp.body.isEmpty then
    (setStream st sid { rec0 with state := .closed, req := none, pending := [] },
     hf ++ dataFrame sid true [], false)
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
        (setStream st sid { rec0 with req := some req, clen := clen }, [], false)

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
              else respond handler st sid req
            | none => respond handler st sid req

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
              let sr := { sr with state := s', recvd := sr.recvd + data.length }
              let st := setStream st hdr.streamId sr
              if es then
                match sr.req with
                | none => streamError st hdr.streamId errProtocol
                | some req =>
                  match sr.clen with
                  | some n =>
                    if n ≠ sr.recvd then streamError st hdr.streamId errProtocol
                    else respond handler st hdr.streamId req
                  | none => respond handler st hdr.streamId req
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
                -- a second HEADERS on an open stream: a trailer block (§8.1)
                if eh then finishTrailers hd handler st hdr.streamId es frag
                else ({ st with
                  cont := some ⟨hdr.streamId, es, true, frag⟩ }, [], false)
              | .halfClosedRemote => connError st errStreamClosed
              | .closed => connError st errStreamClosed
              | _ => connError st errProtocol
            | none =>
              if hdr.streamId % 2 = 0 then connError st errProtocol
              else if hdr.streamId ≤ st.maxSid then connError st errProtocol
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
    List.append_assoc, parseHeader, parseHeaderAux, Option.some.injEq,
    FrameHeader.mk.injEq, UInt8.toNat_ofNat]
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
    rw [← hin]; exact List.drop_length _
  have htake : payload.take len = payload := by
    rw [← hlen]; exact List.take_length _
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
    (hty9 : 9 < ty) (hty : ty < 256) (hfl : fl < 256) (hsid : sid < 2 ^ 31) :
    feed hd handler st (frameHdr len ty fl sid ++ payload) = (st, [], false) := by
  refine feed_single_frame hd handler st st [] false len ty fl sid payload
    hclosed hpre hbuf hlen hsz hlen24 hty hfl hsid ?_ hbuf
  unfold handleFrame
  rw [hcont]
  simp only [show (⟨len, ty, fl, sid⟩ : FrameHeader).frameType = ty from rfl]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]

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
  simp only [show (⟨frag.length, 0x1, 0x4, sid⟩ : FrameHeader).frameType = 0x1 from rfl,
    show (⟨frag.length, 0x1, 0x4, sid⟩ : FrameHeader).streamId = sid from rfl,
    show (⟨frag.length, 0x1, 0x4, sid⟩ : FrameHeader).flags = 0x4 from rfl]
  rw [if_neg (by omega : ¬ (0x1 = 0x0)), if_neg (by omega : ¬ sid = 0)]
  simp only [show flagSet 0x4 0 = false from rfl, show flagSet 0x4 2 = true from rfl,
    show flagSet 0x4 3 = false from rfl, show flagSet 0x4 5 = false from rfl,
    stripPadding, Bool.false_and, Bool.false_eq_true, if_false]
  rw [show getStream st sid = none from by simp [getStream, hstreams]]
  simp only []
  rw [if_neg (by omega : ¬ sid % 2 = 0), if_neg (Nat.not_le.mpr hmax)]
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
  simp only [if_pos rfl]
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

end Conn
end H2
