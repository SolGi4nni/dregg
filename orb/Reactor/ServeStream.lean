import Datapath.Serve
import Reactor.ServeStep
import Reactor.Deploy
import StaticFile

/-!
# Reactor.ServeStream — a sans-IO STREAMING serve (Stage 2: the general any-split
head-accumulation refinement + the bounded-chunk streaming response EMIT)

The deployed serve (`Reactor.Deploy.servePipelineFull2`) is a batch
`Bytes → Bytes`: it takes the WHOLE request as one materialized `List UInt8`, runs
the thirteen-stage fold, and returns the WHOLE response as one materialized
`List UInt8`. This module opens the streaming replacement — a re-entrant state
machine that consumes the request as a sequence of borrowed input windows and
produces the response as a sequence of emitted chunks, so neither the request nor
the response is ever fully materialized on the datapath.

It is shaped exactly like the existing sans-IO connection state machines in this
tree (`H2.Conn.feed`, `Reactor.ServeStep.serveStep`): a total, deterministic
transition function `serveStep : ServeConfig → ServeState → ServeIn →
ServeState × List ServeOut`, driven by an untrusted shell that only moves bytes
over sockets and pumps write-readiness. The effect/continuation seam
(`Reactor.ServeStep.Effect`, `awaitingEffect`) is reused verbatim so the proxy /
cache fabric decisions stay in proven code.

## Stage 1–2 scope (this file)

* the transition-system TYPES (`ServeIn`, `ServeOut`, `BodySrc`, `ServePhase`,
  `ServeState`);
* the `serveStep` transition — a real total function: `readingHead` accumulates
  every received window contiguously (`spanAppend`, denotation-correct) until the
  request stream ends (`eof`), then runs the UNCHANGED deployed fold
  (`runPipeline deployStagesFull2 appHandler (ctxOf …)`) on the accumulated bytes,
  emits the serialized response HEAD as one chunk, and paces the body out as
  bounded `cfg.chunk` chunks — one released per `writeReady` (`emittingBody`), the
  empty list completing the response with the keep-alive decision;
* **the bounded-chunk streaming EMIT** (Stage 2): `paceBody` cuts the response body
  into `≤ cfg.chunk` chunks and `paceBody_flatten` proves they concatenate back to
  the whole body; `emittingBody_drain` proves the `writeReady` pumps release exactly
  that concatenation; `serveChunkList` packages the head chunk + body chunks for the
  `drorb_serve_stream` export and `serveChunkList_flatten` proves the emitted stream
  is `serialize` of the deployed response — the batch bytes, byte-for-byte, whatever
  the chunk size;
* `serveTrace` — the byte trace of feeding the whole input as one window;
  `serveTrace_split` — the byte trace of feeding the input as ANY finite sequence
  of contiguous windows, then `eof`, then the body-draining `writeReady` pumps;
* **the general any-split refinement** (`serveTrace_refines`): for ANY windows
  whose denotations concatenate to `input`, driving the streaming machine reproduces
  the batch spec byte-for-byte — `serveTrace_split cfg windows =
  servePipelineFull2 input`. Its load-bearing lemmas are the split-independence of
  the contiguous accumulation (`accum_denote`), the split-independence of the
  incremental head-boundary scan (`headScan_split`), and the emit pacer's refinement
  (`bodyChunks_flatten` / `emittingBody_drain`).
* the whole-span north-star (`serveTrace_whole`) survives as the one-window
  (`k = 1`) instance.

Nothing here changes runtime behaviour on the default path: the deployed serve
(`servePipelineFull2`) and the deployed step machine (`Reactor.ServeStep.serveStep`)
are untouched; this module is additive, and the `drorb_serve_stream` export drives an
OPT-IN streamed-delivery path in the Rust shell that is byte-identical on the wire
(`serveChunkList_flatten`).

## Why the decision is taken on the FULL accumulation, not the head prefix

The batch spec `servePipelineFull2 input` runs the deployed fold on the *whole*
`input`: the deployed context carries `input` past the parse (`ctxOf`), and the
deployed correlation id seeds on every request byte
(`Reactor.Observe.seedOf input = input.map …`). So `deployRespOf` is a genuine
function of the whole request, not of the head prefix alone — a streaming serve
that computed its response the instant the `CRLFCRLF` head boundary arrived would
NOT be byte-equal to the batch spec on a request with a trailing body. This module
therefore accumulates the whole request and takes the decision on it, THEN streams
the computed response OUT as bounded chunks (response-out streaming, not
early-head-response). Narrowing the deployed decision to the head — the prerequisite
for scan-gated EARLY head-emission (respond before the body fully arrives) — is a
later obligation; the head scan's split-independence (`headScan_split`) is proved
here as its enabler.

## Deferred to later stages (stated, not `sorry`-d)

* **Scan-gated early head-emission** — responding before the request body fully
  arrives; needs the deployed decision narrowed to the head prefix (the enabler
  `headScan_split` is proved here).
* **Stage 3 (LANDED below)** — the non-`inline` body sources `staticFile` and
  `proxy`: their streaming-emit correctness (`staticFile_emit_refines` /
  `staticFile_deployed_emit_refines`, `proxy_emit_refines`). The core decides the head
  batch-small; the shell streams the body from its source without materializing it
  through the cons-list core. `computed` (chunk-safe gzip / html-rewrite over an inner
  source) remains a later stage — its length-changing arm is refinement-modulo-transfer
  -encoding.
* **Stage 4** — request-body streaming: the accumulation here materializes the
  whole request; large uploads stream the body past the head under a chunk pacer.
* **Stage 5** — zero-copy realization: the emitted chunks are owned `Bytes` today;
  Stage 5 emits borrowed `SpanBytes` (SendZc) over the real send buffer so the core
  no longer materializes the whole body either.
-/

namespace Reactor.ServeStream

open Proto (Bytes)
open Datapath (SpanBytes)

/-! ## The transition-system vocabulary (shaped like `H2.Conn` / `serveStep`) -/

/-- **An input to the streaming serve.** The shell feeds received bytes as a
borrowed window (`recv`), signals end-of-stream (`eof`), signals the socket is
writable (`writeReady` — the body pacer's clock), or returns the result bytes of a
yielded effect (`effectResult`). -/
inductive ServeIn where
  | recv (span : SpanBytes)
  | eof
  | writeReady
  | effectResult (bytes : Bytes)

/-- **An output of the streaming serve.** The shell writes a borrowed response
window (`emitSpan` — zero-copy, e.g. a static-file slice), writes owned response
bytes (`emitBytes`), is told nothing is ready yet (`needMore`), is asked to perform
one I/O and resume (`yieldEffect`, reusing `Reactor.ServeStep.Effect`), is told the
response is complete with the keep-alive decision (`done`), or is told to close the
connection (`close`). -/
inductive ServeOut where
  | emitSpan (span : SpanBytes)
  | emitBytes (bytes : Bytes)
  | needMore
  | yieldEffect (eff : Reactor.ServeStep.Effect)
  | done (keepAlive : Bool)
  | close

/-- **The source of a response body.** `inline` — owned bytes already computed (the
common case, and the only one Stage 0 proves). `staticFile` — a borrowed window into
a file mapping, streamed zero-copy host-side (Stage 3: the shell reads the file, the
core never materializes it). `proxy` — bytes arriving from an upstream, carried as a
borrowed window and paced through the effect seam (Stage 3: the shell streams the
upstream forward, the proven pick/breaker decides the head). `computed` — a body
transform (e.g. gzip / html-rewrite) layered over an inner source (later stage). -/
inductive BodySrc where
  | inline (bytes : Bytes)
  | staticFile (span : SpanBytes)
  | proxy (upstream : SpanBytes)
  | computed (xform : Bytes → Bytes) (src : BodySrc)

/-- **The phase of a streaming serve.** `idle` — before the first byte.
`readingHead acc` — accumulating request-head windows into `acc`, scanning for the
CRLFCRLF boundary. `emittingBody chunks keepAlive` — the response head has been
written and the body is being paced out as the bounded `chunks` (each `≤ cfg.chunk`
bytes); every `writeReady` releases the next chunk, and the empty list completes the
response with the `keepAlive` decision (Stage 2's pacer, shaped on
`H2.Conn.sendChunks`). `awaitingEffect k` — blocked on a yielded effect; `k` resumes
with the result bytes. `closing` — draining to close. -/
inductive ServePhase where
  | readingHead (acc : SpanBytes)
  | emittingBody (chunks : List Bytes) (keepAlive : Bool)
  | awaitingEffect (k : Bytes → ServePhase)
  | closing
  | idle

/-- **The streaming serve state.** The current `phase` and the most recent received
window (`recv`); the phase carries the accumulated head / pending body. -/
structure ServeState where
  phase : ServePhase
  recv : SpanBytes

/-- **The streaming serve configuration.** The health/breaker bitmask the proxy
branch keys on (as in `serveStep`), plus `chunk` — the bounded response-body chunk
size the emit pacer cuts at (Stage 2). `chunk = 0` is treated as `1` by the pacer
(`paceBody` floors it at one byte), so the pacer is total and never stalls. The
deployed fold itself is fixed (`deployStagesFull2`); later stages thread the DSL
deployment here. -/
structure ServeConfig where
  mask : Nat := 0
  /-- The bounded body-chunk size the emit pacer cuts the response body at
  (default 64 KiB — the `H2.Conn.sendChunks` DATA-frame regime). -/
  chunk : Nat := 65536

/-- The empty starting window (no bytes received yet). -/
def emptySpan : SpanBytes := SpanBytes.full ⟨#[]⟩

/-- The initial serve state: `idle`, nothing received. -/
def initState : ServeState := { phase := .idle, recv := emptySpan }

/-! ## The deployed response, split into a head and a body

The streaming serve emits the deployed response as a head chunk followed by a body
chunk. `deployRespOf` is the EXACT response the batch serve builds (so the two
cannot drift); `serveRespHead` is everything up to and including the blank-line
separator, and the body is `resp.body`. `serialize_split` proves the concatenation
is the batch serializer byte-for-byte. -/

/-- **The deployed response for these request bytes** — the built fold over the
UNCHANGED `deployStagesFull2`, keyed on the deployed `ctxOf`. This is precisely the
`Response` `servePipelineFull2` serializes, so the streaming trace and the batch
spec run the identical pipeline. -/
def deployRespOf (bytes : Bytes) : Reactor.Response :=
  (Reactor.Pipeline.runPipeline Reactor.Deploy.deployStagesFull2
    Reactor.Deploy.appHandler (Reactor.Deploy.ctxOf bytes)).build

/-- The serialized response HEAD (status line, header block, blank-line separator)
of a wire record — everything the serializer emits before the body. -/
def serveWireHead (w : Reactor.Wire) : Bytes :=
  Reactor.statusLine w ++ Reactor.crlf
    ++ Reactor.renderHeaders (Reactor.allHeaders w) ++ Reactor.crlf ++ Reactor.crlf

/-- The serialized response head of a `Response` (via its wire record). -/
def serveRespHead (resp : Reactor.Response) : Bytes := serveWireHead (Reactor.build resp)

/-- **The serializer splits as head ++ body.** The deployed serializer is exactly
the response head followed by the response body — the split point the streaming
emit cuts at. Definitional. -/
theorem serialize_split (resp : Reactor.Response) :
    Reactor.serialize resp = serveRespHead resp ++ resp.body := rfl

/-- **The batch serve is `serialize` of the deployed response.** `servePipelineFull2`
serializes exactly `deployRespOf` — the streaming serve and the batch spec share the
one pipeline run. Definitional. -/
theorem servePipelineFull2_eq (input : Bytes) :
    Reactor.Deploy.servePipelineFull2 input = Reactor.serialize (deployRespOf input) := rfl

/-- The keep-alive decision the deployed HTTP/1.1 parse resolves for these request
bytes (carried in `done`; not part of the emitted byte stream). -/
def keepAliveOf (bytes : Bytes) : Bool :=
  match Reactor.Config.h1ParseFn bytes with
  | .request _ _ ka => ka
  | _ => false

/-- **The head-complete projection** — the shape the roadmap names: run the deployed
fold over the request bytes and project the built response to
`(headBytes, BodySrc, keepAlive)`. Stage 0 realizes the body as `inline resp.body`;
Stage 3 replaces this with the real body source (static-file span / proxy). -/
def projectServe (bytes : Bytes) : Bytes × BodySrc × Bool :=
  let resp := deployRespOf bytes
  (serveRespHead resp, BodySrc.inline resp.body, keepAliveOf bytes)

/-- The bytes a body source denotes (its full contents). `inline` is its own
bytes; `staticFile` denotes its file window; `proxy` denotes its upstream window
(the bytes the backend returned, streamed host-side); `computed` maps its inner
source. -/
def bodyBytes : BodySrc → Bytes
  | .inline bs => bs
  | .staticFile span => span.denote
  | .proxy up => up.denote
  | .computed xform src => xform (bodyBytes src)

/-! ### The bounded body-emit pacer (Stage 2)

The response body is emitted not as one blob but as a sequence of bounded chunks,
each at most `sz` bytes — the streaming EMIT the roadmap names, shaped on the
`H2.Conn.sendChunks` DATA pacer. `paceBody` cuts the body into those chunks (`sz`
floored at one byte, so a `chunk = 0` config still makes progress); `fuel` bounds the
recursion (`body.length + 1` always drains, since every emitted chunk consumes ≥ 1
byte). The one load-bearing fact is `paceBody_flatten`: the chunks CONCATENATE back
to the whole body, losing and reordering nothing — so the paced emit is byte-equal to
the one-blob emit. -/
def paceBody (sz : Nat) : Nat → Bytes → List Bytes
  | 0,       _         => []
  | _ + 1,   []        => []
  | fuel + 1, (b :: bs) =>
      (b :: bs).take (max 1 sz) :: paceBody sz fuel ((b :: bs).drop (max 1 sz))

/-- **The paced chunks concatenate to the whole body.** Cutting `body` into bounded
`sz`-chunks and flattening them back yields `body` exactly — no byte is dropped,
duplicated, or reordered at a chunk boundary. Holds whenever the fuel covers the body
length (`body.length + 1` always does). This is the emit pacer's refinement lemma:
the streamed body equals the batch body. -/
theorem paceBody_flatten (sz fuel : Nat) (body : Bytes) (h : body.length ≤ fuel) :
    (paceBody sz fuel body).flatten = body := by
  induction fuel generalizing body with
  | zero =>
    cases body with
    | nil => rfl
    | cons b bs => simp only [List.length_cons] at h; omega
  | succ fuel ih =>
    cases body with
    | nil => rfl
    | cons b bs =>
      have hk : 1 ≤ max 1 sz := Nat.le_max_left 1 sz
      have hdrop : ((b :: bs).drop (max 1 sz)).length ≤ fuel := by
        rw [List.length_drop]
        have : (b :: bs).length ≤ fuel + 1 := h
        omega
      rw [paceBody, List.flatten_cons, ih _ hdrop, List.take_append_drop]

/-- **The paced body chunks for a request** — the deployed response body cut into
bounded `cfg.chunk` chunks (fuel `body.length + 1`, which always drains). Used by the
`readingHead`/`eof` transition and by the `drorb_serve_stream` export. -/
def bodyChunks (cfg : ServeConfig) (bytes : Bytes) : List Bytes :=
  paceBody cfg.chunk ((deployRespOf bytes).body.length + 1) (deployRespOf bytes).body

/-- **The paced body chunks flatten to the deployed body.** The `cfg.chunk`-bounded
emit stream for a request reassembles to exactly the deployed response body. -/
theorem bodyChunks_flatten (cfg : ServeConfig) (bytes : Bytes) :
    (bodyChunks cfg bytes).flatten = (deployRespOf bytes).body :=
  paceBody_flatten _ _ _ (Nat.le_succ _)

/-- **The emitted chunk stream for a request** — the response HEAD as one chunk,
followed by the deployed body cut into bounded `cfg.chunk` chunks. These are exactly
the byte chunks the streaming machine emits (the `emitBytes head` at `eof` then one
`emitBytes` per `writeReady`), packaged for the `drorb_serve_stream` export so the
shell can write them to the socket incrementally. -/
def serveChunkList (cfg : ServeConfig) (bytes : Bytes) : List Bytes :=
  serveRespHead (deployRespOf bytes) :: bodyChunks cfg bytes

/-- **THE EMIT REFINEMENT (chunk stream).** The concatenation of the emitted chunks
(the head chunk followed by the bounded body chunks) is exactly `serialize` of the
deployed response — i.e. the batch serve's bytes. So the streaming EMIT delivers the
identical response byte-for-byte, whatever the chunk size, and the export is a
drop-in for the batch `drorb_serve` on the response side. -/
theorem serveChunkList_flatten (cfg : ServeConfig) (bytes : Bytes) :
    (serveChunkList cfg bytes).flatten = Reactor.Deploy.servePipelineFull2 bytes := by
  rw [serveChunkList, List.flatten_cons, bodyChunks_flatten, ← serialize_split,
    servePipelineFull2_eq]

/-! ## Stage 3 — the non-`inline` body SOURCES stream host-side

Stage 2's `serveChunkList` cuts the deployed response body out of `deployRespOf`,
which MATERIALIZES `resp.body` in the core (fine for the small demo responses). A
LARGE local body — a multi-megabyte static file, or a proxied upstream — must not be
materialized through the cons-list core at all. Stage 3 is the clean cut the roadmap
names: the core DECIDES the response HEAD (batch-small — status line, headers,
Content-Length), and the SHELL streams the BODY from its source (`staticFile` — a
file window; `proxy` — an upstream window) without ever handing the whole body to the
core. Only the head crosses the FFI; the body bytes flow host-side.

The refinement extends by decoupling the emitted stream from `deployRespOf`: a body
SOURCE `src` paces its OWN denotation (`srcChunks`), and the emitted stream is the
core-built head chunk followed by the source's paced body chunks (`srcChunkList`).
`srcChunkList_flatten` proves that concatenates to `head ++ bodyBytes src` — the same
`paceBody_flatten` pacer, now over an arbitrary body source. Two instances close the
Stage-3 obligations byte-for-byte:

* **`staticFile_emit_refines`** — for a static-file response the core would produce,
  streaming the file host-side from a window `span` whose bytes are the response body
  reproduces `serialize resp` exactly (the head chunk ++ the paced file chunks). The
  concrete `staticFile_deployed_emit_refines` lands it on the REAL deployed static
  handler (`StaticFile.serveDeployed` — real bytes, entity-tag, Content-Length).
* **`proxy_emit_refines`** — for a proxied response the core decided the head of, the
  head chunk ++ the paced upstream-body chunks concatenate to `head ++ up.denote` —
  the exact bytes a body-buffering proxy would have returned. The proven pick/breaker
  (which decides the head, not the body) is untouched. -/

/-- **The paced chunks of a body SOURCE** — the source's denoted bytes cut into
bounded `cfg.chunk` chunks (fuel `length + 1`, which always drains). For a
`staticFile` this is the file window streamed host-side; for a `proxy` the upstream
window; for `inline` the owned bytes. The core never sees these bytes for the
non-`inline` sources — they flow host-side; this is their pure image. -/
def srcChunks (cfg : ServeConfig) (src : BodySrc) : List Bytes :=
  paceBody cfg.chunk ((bodyBytes src).length + 1) (bodyBytes src)

/-- **The paced source chunks flatten to the source's body.** No byte is dropped,
duplicated, or reordered at a chunk boundary — the streamed body equals the whole
source body, whatever the chunk size. -/
theorem srcChunks_flatten (cfg : ServeConfig) (src : BodySrc) :
    (srcChunks cfg src).flatten = bodyBytes src :=
  paceBody_flatten _ _ _ (Nat.le_succ _)

/-- **The emitted chunk stream for a head + a body SOURCE** — the core-built response
HEAD as one chunk, followed by the body source's paced chunks (streamed host-side for
`staticFile` / `proxy`). This is the Stage-3 shape: only `headBytes` is materialized
by the core; the body flows from its source. -/
def srcChunkList (cfg : ServeConfig) (headBytes : Bytes) (src : BodySrc) : List Bytes :=
  headBytes :: srcChunks cfg src

/-- **The emitted stream concatenates to head ++ body.** The head chunk followed by
the source's paced body chunks reassembles to `headBytes ++ bodyBytes src` — the head
the core built plus the body the shell streamed, byte-for-byte. -/
theorem srcChunkList_flatten (cfg : ServeConfig) (headBytes : Bytes) (src : BodySrc) :
    (srcChunkList cfg headBytes src).flatten = headBytes ++ bodyBytes src := by
  rw [srcChunkList, List.flatten_cons, srcChunks_flatten]

/-- **THE STAGE-3 STATIC-FILE EMIT REFINEMENT.** For a static-file response `resp`
the core DECIDES (its head + which file to serve), streaming that file host-side from
a window `span` whose bytes are the response body reproduces the batch serializer of
`resp` byte-for-byte: the head chunk (core-built, batch-small) followed by the paced
file-body chunks (streamed from `span`, never materialized through the cons-list core)
concatenate to `serialize resp`. So host-side file streaming is byte-equal to the
batch spec's static response, whatever the chunk size. The only hypothesis is that the
served window carries the response body (`span.denote = resp.body`) — the faithfulness
the shell's file read owes. -/
theorem staticFile_emit_refines (cfg : ServeConfig) (resp : Reactor.Response)
    (span : SpanBytes) (hspan : span.denote = resp.body) :
    (srcChunkList cfg (serveRespHead resp) (BodySrc.staticFile span)).flatten
      = Reactor.serialize resp := by
  rw [srcChunkList_flatten]
  show serveRespHead resp ++ span.denote = Reactor.serialize resp
  rw [hspan, serialize_split]

/-- **The Stage-3 static-file emit refinement on the DEPLOYED static handler.** The
concrete static-file response the deployed handler SELECTS (`StaticFile.serveDeployed`
— real bytes, a real content entity-tag, a real Content-Length, over the proven
conditional/range core `serveConditional`) streams host-side byte-for-byte: its head
(core-built) followed by the file window `span` (whose bytes are the response body)
paced into bounded chunks concatenates to `serialize` of that response. This is the
generic refinement instantiated on the real handler — the "proven = what the core
would serialize" the roadmap names, on a genuine (non-vacuous) static response. -/
theorem staticFile_deployed_emit_refines (cfg : ServeConfig)
    (segments : List String) (headers : List (Bytes × Bytes)) (span : SpanBytes)
    (hspan : span.denote = (StaticFile.serveDeployed segments headers).body) :
    (srcChunkList cfg (serveRespHead (StaticFile.serveDeployed segments headers))
      (BodySrc.staticFile span)).flatten
      = Reactor.serialize (StaticFile.serveDeployed segments headers) :=
  staticFile_emit_refines cfg _ span hspan

/-- **THE STAGE-3 PROXY EMIT REFINEMENT.** For a proxied response the core DECIDES the
HEAD of (the batch-small forward decision — the proven pick / breaker / affinity,
unchanged), the shell STREAMS the upstream body from a window `up` (bounded RSS, never
buffered whole): the head chunk followed by the paced upstream-body chunks concatenate
to `headBytes ++ up.denote` — exactly the bytes a body-buffering proxy would have
returned. So streamed proxy delivery is byte-equal to buffered proxy delivery,
whatever the chunk size, and the proven pick/breaker (which decides the head, not the
body) is untouched. -/
theorem proxy_emit_refines (cfg : ServeConfig) (headBytes : Bytes) (up : SpanBytes) :
    (srcChunkList cfg headBytes (BodySrc.proxy up)).flatten = headBytes ++ up.denote := by
  rw [srcChunkList_flatten]
  rfl

/-- **Contiguous accumulation** of a further received window onto the head
accumulator. In the model the extend materializes the concatenation; its
denotation is exactly the concatenation of the two windows' denotations
(`spanAppend_denote`), which is the only property Stage 1's refinement needs. The
Stage-5 zero-copy realization replaces this with a borrowed-buffer extend over the
real recv ring, preserving `denote (extend a b) = a.denote ++ b.denote`. -/
def spanAppend (a b : SpanBytes) : SpanBytes :=
  SpanBytes.full ⟨(a.denote ++ b.denote).toArray⟩

/-- **The accumulation denotes to the concatenation.** Appending window `b` onto
`a` yields the bytes `a.denote ++ b.denote` — no bytes are lost or reordered at a
recv boundary. This is the split-independence of one accumulation step. -/
theorem spanAppend_denote (a b : SpanBytes) :
    (spanAppend a b).denote = a.denote ++ b.denote := by
  unfold spanAppend
  rw [SpanBytes.denote_full]

/-- Fold a sequence of received windows onto a head accumulator, left to right —
the pure image of the shell's `readingHead` loop over successive `recv`s. -/
def accum (a : SpanBytes) : List SpanBytes → SpanBytes
  | [] => a
  | w :: ws => accum (spanAppend a w) ws

/-- **The accumulation is split-independent.** Folding ANY sequence of contiguous
windows onto `a` denotes to `a.denote` followed by the flat concatenation of the
windows' denotations — the accumulated bytes depend only on the total byte stream,
never on where the recv boundaries fell. -/
theorem accum_denote (a : SpanBytes) (ws : List SpanBytes) :
    (accum a ws).denote = a.denote ++ (ws.map SpanBytes.denote).flatten := by
  induction ws generalizing a with
  | nil => simp [accum]
  | cons w ws ih =>
    simp only [accum, ih, spanAppend_denote, List.map_cons, List.flatten_cons,
      List.append_assoc]

/-- The accumulation stays well-formed: appending is a full-buffer span (always
`Wf`), so folding preserves well-formedness from a well-formed seed. -/
theorem accum_wf {a : SpanBytes} (h : a.Wf) (ws : List SpanBytes) : (accum a ws).Wf := by
  induction ws generalizing a with
  | nil => exact h
  | cons w ws ih => exact ih (a := spanAppend a w) (SpanBytes.full_wf _)

/-! ## The streaming transition function -/

/-- **The sans-IO streaming serve step.** Total and deterministic, in the shape of
`H2.Conn.feed` / `Reactor.ServeStep.serveStep`:

* `idle`/`recv` — begin reading the head with this window (`readingHead`), and ask
  for more (`needMore`).
* `readingHead`/`recv` — accumulate a further window contiguously (`spanAppend`) —
  Stage 1's partial head reads across recv boundaries — and ask for more.
* `readingHead`/`eof` (and `idle`/`eof`) — the request stream ended: run the
  UNCHANGED deployed fold on the accumulated bytes, emit the serialized response HEAD
  as one chunk, and move to `emittingBody` carrying the body pre-cut into bounded
  `cfg.chunk` chunks (`bodyChunks`). The decision is taken on the full accumulation
  because the deployed response is a function of the whole request (see the note).
* `emittingBody (c :: rest)`/`writeReady` — the socket is writable: release the next
  bounded body chunk `c` and keep the remainder parked (the `sendChunks`-style pacer).
* `emittingBody []`/`writeReady` — the body is exhausted: signal the response is
  `done` with the keep-alive decision and move to `closing`.
* `awaitingEffect`/`effectResult` — resume the continuation with the effect result.

The proxy/cache routing rides `yieldEffect` + `awaitingEffect` (the seam already
proven in `Reactor.ServeStep`). -/
def serveStep (cfg : ServeConfig) (st : ServeState) (inp : ServeIn) :
    ServeState × List ServeOut :=
  match st.phase, inp with
  | .idle, .recv span =>
      ({ phase := .readingHead span, recv := span }, [ServeOut.needMore])
  | .idle, .eof =>
      ({ phase := .emittingBody (bodyChunks cfg emptySpan.denote) (keepAliveOf emptySpan.denote)
         recv := st.recv },
       [ServeOut.emitBytes (serveRespHead (deployRespOf emptySpan.denote))])
  | .readingHead acc, .recv span =>
      ({ phase := .readingHead (spanAppend acc span), recv := span }, [ServeOut.needMore])
  | .readingHead acc, .eof =>
      ({ phase := .emittingBody (bodyChunks cfg acc.denote) (keepAliveOf acc.denote)
         recv := st.recv },
       [ServeOut.emitBytes (serveRespHead (deployRespOf acc.denote))])
  | .emittingBody (c :: rest) ka, .writeReady =>
      ({ phase := .emittingBody rest ka, recv := st.recv }, [ServeOut.emitBytes c])
  | .emittingBody [] ka, .writeReady =>
      ({ phase := .closing, recv := st.recv }, [ServeOut.done ka])
  | .awaitingEffect k, .effectResult bytes =>
      ({ phase := k bytes, recv := st.recv }, [ServeOut.needMore])
  | _, _ => (st, [])

/-! ### The transition reductions (each `rfl`, for driving)

Each equation names one `serveStep` arm on a concrete `(phase, input)`; they are all
definitional and let the driver proofs reduce the machine step by step. -/

@[simp] theorem step_idle_recv (cfg : ServeConfig) (r span : SpanBytes) :
    serveStep cfg { phase := .idle, recv := r } (.recv span)
      = ({ phase := .readingHead span, recv := span }, [ServeOut.needMore]) := rfl

@[simp] theorem step_idle_eof (cfg : ServeConfig) (r : SpanBytes) :
    serveStep cfg { phase := .idle, recv := r } .eof
      = ({ phase := .emittingBody (bodyChunks cfg emptySpan.denote) (keepAliveOf emptySpan.denote)
           recv := r },
         [ServeOut.emitBytes (serveRespHead (deployRespOf emptySpan.denote))]) := rfl

@[simp] theorem step_readingHead_recv (cfg : ServeConfig) (r acc span : SpanBytes) :
    serveStep cfg { phase := .readingHead acc, recv := r } (.recv span)
      = ({ phase := .readingHead (spanAppend acc span), recv := span },
         [ServeOut.needMore]) := rfl

@[simp] theorem step_readingHead_eof (cfg : ServeConfig) (r acc : SpanBytes) :
    serveStep cfg { phase := .readingHead acc, recv := r } .eof
      = ({ phase := .emittingBody (bodyChunks cfg acc.denote) (keepAliveOf acc.denote)
           recv := r },
         [ServeOut.emitBytes (serveRespHead (deployRespOf acc.denote))]) := rfl

@[simp] theorem step_emittingBody_cons (cfg : ServeConfig) (r : SpanBytes)
    (c : Bytes) (rest : List Bytes) (ka : Bool) :
    serveStep cfg { phase := .emittingBody (c :: rest) ka, recv := r } .writeReady
      = ({ phase := .emittingBody rest ka, recv := r }, [ServeOut.emitBytes c]) := rfl

@[simp] theorem step_emittingBody_nil (cfg : ServeConfig) (r : SpanBytes) (ka : Bool) :
    serveStep cfg { phase := .emittingBody [] ka, recv := r } .writeReady
      = ({ phase := .closing, recv := r }, [ServeOut.done ka]) := rfl

/-! ## Driving the machine, and the byte trace -/

/-- The bytes one output denotes on the wire (`emitSpan` denotes its window,
`emitBytes` is its bytes; control outputs denote nothing). -/
def emitOf : ServeOut → Bytes
  | .emitSpan s => s.denote
  | .emitBytes bs => bs
  | _ => []

/-- The concatenation of the bytes a list of outputs denotes. -/
def emitsOf : List ServeOut → Bytes
  | [] => []
  | o :: os => emitOf o ++ emitsOf os

/-- Drive the machine through a list of inputs from a state, concatenating every
output emitted. This is the shell's forward loop, as a pure function over a recorded
input sequence. -/
def runInputs (cfg : ServeConfig) (st : ServeState) : List ServeIn → List ServeOut
  | [] => []
  | i :: is => let (st', o) := serveStep cfg st i; o ++ runInputs cfg st' is

/-- One `runInputs` step, as an explicit equation (the `let`-destructure of the
`serveStep` pair) — lets driver proofs advance the machine one input without a `simp`
that would over-unfold a symbolic `List.replicate` pump tail. -/
theorem runInputs_cons (cfg : ServeConfig) (st : ServeState) (i : ServeIn)
    (is : List ServeIn) :
    runInputs cfg st (i :: is)
      = (serveStep cfg st i).2 ++ runInputs cfg (serveStep cfg st i).1 is := rfl

/-- The emitted bytes distribute over output-list concatenation. -/
theorem emitsOf_append (xs ys : List ServeOut) :
    emitsOf (xs ++ ys) = emitsOf xs ++ emitsOf ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, emitsOf, ih, List.append_assoc]

/-- **The body pacer drains to the whole body.** From an `emittingBody chunks ka`
state, `chunks.length + 1` `writeReady` pumps release every bounded chunk in order
(one per pump) and then the terminating `done ka`, emitting exactly the concatenation
of the chunks — `chunks.flatten`. This is the streaming EMIT: the paced body reaches
the wire byte-for-byte, whatever the chunk size. -/
theorem emittingBody_drain (cfg : ServeConfig) (r : SpanBytes)
    (chunks : List Bytes) (ka : Bool) :
    emitsOf (runInputs cfg { phase := .emittingBody chunks ka, recv := r }
      (List.replicate (chunks.length + 1) ServeIn.writeReady))
      = chunks.flatten := by
  induction chunks generalizing r with
  | nil =>
    simp only [List.length_nil, List.replicate_succ, List.replicate_zero, runInputs,
      step_emittingBody_nil, emitsOf, emitOf, List.flatten_nil, List.append_nil]
  | cons c rest ih =>
    rw [List.length_cons, List.replicate_succ]
    simp only [runInputs, step_emittingBody_cons]
    rw [emitsOf_append, ih, List.flatten_cons]
    simp only [emitsOf, emitOf, List.append_nil]

/-! ## The general any-split refinement -/

/-- The whole-buffer span over `input` denotes back to `input`. -/
theorem denote_ofBytes (input : Bytes) :
    (SpanBytes.full ⟨input.toArray⟩).denote = input := by
  rw [Datapath.SpanBytes.denote_full]

/-- The empty starting window denotes to no bytes. -/
theorem emptySpan_denote : emptySpan.denote = [] := by
  rw [emptySpan, Datapath.SpanBytes.denote_full]

/-- **The `readingHead` drive is split-independent.** From a `readingHead a` state,
feeding ANY sequence of contiguous windows `ws` (as `recv`s) then `eof` then the
body-draining `writeReady` pumps emits exactly the batch serve's bytes on the
ACCUMULATED denotation `(accum a ws).denote`: every `recv` only extends the
accumulator (`needMore`, no bytes), `eof` completes the head over the whole
accumulation and emits the head chunk, and the `writeReady` pumps release the paced
body chunks (`emittingBody_drain`, `bodyChunks_flatten`) whose concatenation is the
body. Where the recv boundaries and the chunk cuts fell is invisible to the output —
only the total accumulated byte stream matters. -/
theorem serveTrace_split_drive (cfg : ServeConfig) (a r : SpanBytes) (ws : List SpanBytes) :
    emitsOf (runInputs cfg { phase := .readingHead a, recv := r }
      (ws.map ServeIn.recv ++ ServeIn.eof ::
        List.replicate ((bodyChunks cfg (accum a ws).denote).length + 1) ServeIn.writeReady))
      = Reactor.serialize (deployRespOf (accum a ws).denote) := by
  induction ws generalizing a r with
  | nil =>
    simp only [List.map_nil, List.nil_append, accum, runInputs, step_readingHead_eof]
    rw [emitsOf_append, emittingBody_drain, bodyChunks_flatten]
    simp only [emitsOf, emitOf, List.append_nil]
    rw [serialize_split]
  | cons w ws ih =>
    simp only [List.map_cons, List.cons_append, accum, runInputs, step_readingHead_recv,
      emitsOf, emitOf, List.nil_append]
    exact ih (spanAppend a w) w

/-- **The any-split byte trace.** Feed the request as ANY finite sequence of
contiguous received windows (`recv w₁ … recv wₖ`), then `eof`, then one `writeReady`
pump, and concatenate every emitted chunk's bytes. `windows = [full input]` is the
whole-span `serveTrace`. -/
def serveTrace_split (cfg : ServeConfig) (windows : List SpanBytes) : Bytes :=
  emitsOf (runInputs cfg initState
    (windows.map ServeIn.recv ++ ServeIn.eof ::
      List.replicate ((bodyChunks cfg ((windows.map SpanBytes.denote).flatten)).length + 1)
        ServeIn.writeReady))

/-- **The any-split trace is the batch serve on the accumulated bytes.** Whatever the
split, `serveTrace_split` emits `serialize (deployRespOf …)` on the flat
concatenation of the windows' denotations — the head accumulation, the deployed
decision, and the paced body emit depend only on the total request bytes, not the
recv boundaries. -/
theorem serveTrace_split_eq (cfg : ServeConfig) (windows : List SpanBytes) :
    serveTrace_split cfg windows
      = Reactor.serialize (deployRespOf ((windows.map SpanBytes.denote).flatten)) := by
  unfold serveTrace_split
  cases windows with
  | nil =>
    simp only [List.map_nil, List.nil_append, List.flatten_nil, emptySpan_denote,
      runInputs, initState, step_idle_eof]
    rw [emitsOf_append, emittingBody_drain, bodyChunks_flatten]
    simp only [emitsOf, emitOf, List.append_nil]
    rw [serialize_split]
  | cons w rest =>
    have hb : (List.map SpanBytes.denote (w :: rest)).flatten = (accum w rest).denote := by
      rw [accum_denote, List.map_cons, List.flatten_cons]
    rw [hb]
    simp only [List.map_cons, List.cons_append, runInputs, initState, step_idle_recv,
      emitsOf, emitOf, List.nil_append]
    exact serveTrace_split_drive cfg w w rest

/-- **The whole-span byte trace.** Feed the whole input as ONE received window, then
`eof`, then `writeReady` pumps enough to drain the paced body, and concatenate every
emitted chunk's bytes — the `k = 1` instance of `serveTrace_split`. This is the
streaming serve's output for a client that delivered the request in one read. -/
def serveTrace (cfg : ServeConfig) (input : Bytes) : Bytes :=
  serveTrace_split cfg [SpanBytes.full ⟨input.toArray⟩]

/-- **THE GENERAL ANY-SPLIT REFINEMENT.** For ANY sequence of contiguous received
windows whose denotations concatenate to `input` — an arbitrary split of the request
across reads, including partial head reads that straddle recv boundaries — driving
`[recv w₁, …, recv wₖ, eof, writeReady]` from `initState` reproduces the deployed
batch serve byte-for-byte:

    serveTrace_split cfg windows = servePipelineFull2 input

so every existing byte / status / gate theorem and the black-box conformance verdict
transfer to the streaming serve unchanged. The proof rests on two split-independence
facts: the contiguous accumulation denotes to the concatenation (`accum_denote`), and
the batch serve is `serialize` of the deployed response on those exact bytes
(`servePipelineFull2_eq`). No hypothesis on the input (head-only or otherwise) is
needed: the decision is taken on the full accumulation, which equals `input`. -/
theorem serveTrace_refines (cfg : ServeConfig) (input : Bytes) (windows : List SpanBytes)
    (hpart : (windows.map SpanBytes.denote).flatten = input) :
    serveTrace_split cfg windows = Reactor.Deploy.servePipelineFull2 input := by
  rw [serveTrace_split_eq, hpart]
  exact (servePipelineFull2_eq input).symm

/-- **THE NORTH-STAR THEOREM (whole-span).** Feeding the whole input as one received
window reproduces the deployed batch serve byte-for-byte — the one-window (`k = 1`)
instance of `serveTrace_refines`. -/
theorem serveTrace_whole (cfg : ServeConfig) (input : Bytes) :
    serveTrace cfg input = Reactor.Deploy.servePipelineFull2 input := by
  unfold serveTrace
  exact serveTrace_refines cfg input [SpanBytes.full ⟨input.toArray⟩] (by simp [denote_ofBytes])

/-- Driving a single window `s` (recv `s`, `eof`, then the body-draining `writeReady`
pumps) reproduces the batch serve on `s.denote` — the one-window instance, surfaced as
the named anchor. -/
theorem serve_drive_denote (cfg : ServeConfig) (s : SpanBytes) :
    serveTrace_split cfg [s] = Reactor.Deploy.servePipelineFull2 s.denote :=
  serveTrace_refines cfg s.denote [s] (by simp)

/-- The whole-span refinement over an arbitrary window (`k = 1`), retained name. -/
theorem serveTrace_refines_wholeSpan (cfg : ServeConfig) (s : SpanBytes) :
    serveTrace_split cfg [s] = Reactor.Deploy.servePipelineFull2 s.denote :=
  serve_drive_denote cfg s

/-! ## The incremental head-boundary scan is split-independent (the Stage-2 enabler)

Stage 1 completes the head at `eof` over the full accumulation (the deployed decision
reads the whole request — see the module note). Stage 2 will instead gate completion
on the incremental `CRLFCRLF` scan the instant the head boundary arrives. The fact
that makes that split-safe is proved here: the index-native `spanFindDoubleCrlf` over
the accumulated windows finds exactly the boundary the deployed framing scan finds on
the whole request, no matter how the head was split across recvs. -/

/-- **The head-boundary scan is split-independent.** On any accumulation of contiguous
windows onto a well-formed seed, the index-native dominant scan equals the deployed
parser's framing scan on the flat concatenation of the accumulated bytes: the head
boundary is found at the same offset regardless of the recv split. -/
theorem headScan_split (a : SpanBytes) (ws : List SpanBytes) (h : a.Wf) :
    Datapath.SpanBytes.spanFindDoubleCrlf (accum a ws)
      = Arena.Parse.findDoubleCrlf (a.denote ++ (ws.map SpanBytes.denote).flatten) := by
  rw [Datapath.SpanBytes.spanFindDoubleCrlf_eq_denote (accum a ws) (accum_wf h ws),
    accum_denote]

/-! ## Runnable checks and axiom audit -/

-- The head/body split is the serializer, byte-for-byte.
example (r : Reactor.Response) : Reactor.serialize r = serveRespHead r ++ r.body := rfl
-- The batch serve is `serialize` of the deployed response.
example (i : Bytes) : Reactor.Deploy.servePipelineFull2 i = Reactor.serialize (deployRespOf i) := rfl
-- The inline body denotes to its own bytes.
example (bs : Bytes) : bodyBytes (BodySrc.inline bs) = bs := rfl
-- The paced body chunks reassemble to the whole body (the emit pacer's refinement).
example (cfg : ServeConfig) (i : Bytes) : (bodyChunks cfg i).flatten = (deployRespOf i).body :=
  bodyChunks_flatten cfg i
-- The emitted chunk stream (head ++ paced body) concatenates to the batch serve bytes.
example (cfg : ServeConfig) (i : Bytes) :
    (serveChunkList cfg i).flatten = Reactor.Deploy.servePipelineFull2 i :=
  serveChunkList_flatten cfg i
-- Stage 3: a static-file body streamed host-side reassembles to head ++ file bytes.
example (cfg : ServeConfig) (h : Bytes) (span : SpanBytes) :
    (srcChunkList cfg h (BodySrc.staticFile span)).flatten = h ++ span.denote :=
  srcChunkList_flatten cfg h _
-- Stage 3: the static emit equals the serializer of the static-file response.
example (cfg : ServeConfig) (resp : Reactor.Response) (span : SpanBytes)
    (hspan : span.denote = resp.body) :
    (srcChunkList cfg (serveRespHead resp) (BodySrc.staticFile span)).flatten
      = Reactor.serialize resp :=
  staticFile_emit_refines cfg resp span hspan
-- Stage 3: a proxied body streamed host-side reassembles to head ++ upstream bytes.
example (cfg : ServeConfig) (h : Bytes) (up : SpanBytes) :
    (srcChunkList cfg h (BodySrc.proxy up)).flatten = h ++ up.denote :=
  proxy_emit_refines cfg h up
-- Accumulation is split-independent: two different splits of the same bytes accumulate
-- to the same denotation.
example (x y z : SpanBytes) (h : x.denote ++ y.denote = z.denote) :
    (accum emptySpan [x, y]).denote = (accum emptySpan [z]).denote := by
  rw [accum_denote, accum_denote]; simp [emptySpan_denote, h]

#print axioms serveTrace_refines
#print axioms serveTrace_split_eq
#print axioms accum_denote
#print axioms headScan_split
#print axioms serveTrace_whole
#print axioms serve_drive_denote
#print axioms serveTrace_refines_wholeSpan
#print axioms paceBody_flatten
#print axioms bodyChunks_flatten
#print axioms emittingBody_drain
#print axioms serveChunkList_flatten
#print axioms srcChunkList_flatten
#print axioms staticFile_emit_refines
#print axioms staticFile_deployed_emit_refines
#print axioms proxy_emit_refines

end Reactor.ServeStream
