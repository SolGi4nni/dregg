# FOOTGUN-MAP — ranked structural perf/safety hazards on the serve path

A footgun is **structure that permits a hazard**, not a bug in a value. Each entry
below names the file:line, the structure that permits the hazard, and the
by-construction fix that makes it impossible (fix-forward: reach for the bounded /
index-native primitive the tree already proves, never a patch or a revert).

Ranking key: **safety-crash > hot-path-List materialization > allocation-churn**.
A crash is total loss of the process; a hot-path List materialization taxes every
request; allocation churn taxes throughput.

The two known crashes are grounded first (F1, F2) because they are the top of the
ranking, then the remaining structural hazards.

---

## The one structural root of both crashes

Both known crashes are the **same class**: a `List UInt8` consumed by a
**non-tail-recursive** function whose recursion depth equals the input length.
Lean compiles `a :: f xs` and `(f xs).map g` strictly, so the recursive call is an
argument evaluated *before* the constructor/`map` — it builds one C stack frame per
input element. Depth = input length. At ~30 KiB the ~8 MiB thread stack is gone and
the whole `drorb-serve` process aborts (`fatal runtime error: stack overflow`).

The tree already contains the correct shape and *proves it equal*: the index-native
scanners in `Datapath/Scan.lean` (`scanDCrlf`, fuel-bounded, tail-recursive) and the
`@[csimp]` accumulator technique in `Arena/Parse.lean`
(`crlfPositions_eq_fast`, `parseHeaders_eq_fast`). The footgun is that the deployed
serve path does **not** route through them — it re-parses through the unbounded
list functions on every off-arm / default request.

---

## F1 — [SAFETY-CRASH] Large request head aborts the whole process (unbounded parse recursion)

**Rank: 1 (highest — unauthenticated single-packet remote process kill).**

**Root cause (precise).** The deployed serve — `servePipelineFull2`
(`Reactor/Deploy.lean:1535`) and every metered/config/conformant wrapper that folds
`deployStagesFull2` — builds its context with `ctxOf input.toList`
(`Reactor/Deploy.lean:1065`), which runs `deploySubs` → `Reactor.step deployConfig`
→ `Reactor.Config.h1ParseFn s.read` (`Reactor/Config.lean:81`) →
`Arena.Parse.parse` (`Arena/Parse.lean:436`). That parser is gated on two
**non-tail-recursive list walkers whose depth is the head length**:

- `findDoubleCrlf` — `Arena/Parse.lean:66`:
  ```
  | a :: rest@(b :: c :: d :: _) =>
    if … then some 0 else (findDoubleCrlf rest).map (· + 1)   -- recursion inside .map: NON-tail
  ```
  Depth = byte offset of the `CRLFCRLF` = the whole head. **No `@[csimp]` fast
  variant exists** — this is the framing scan and it runs on *every* request.
- `crlfPositionsGo` — `Arena/Parse.lean:95` (the `@[csimp]` "fast" `crlfPositions`):
  ```
  | i, a :: b :: rest => if … then i :: crlfPositionsGo (i+1) (b :: rest) else …  -- cons BEFORE recurse: NON-tail
  ```
  `crlfPositions_eq_fast` made it linear-*time* but left it linear-*stack*: it conses
  before recursing, depth = head length.

**Why the byte-count gate does not save it.** `deployConfig.maxHeaderBytes = 65536`
and `gateB` (`Datapath/ServeHeadIdx.lean:52`) only refuses `size > 65536`. The stack
is exhausted at ~30 KiB — *below* the 64 KiB byte gate — so the recursion overflows
before any size limit fires. Bisected: 28 KiB head survives, 32 KiB crashes
(`docs/engine/review/CONFORMANCE-EXT.md` Z1). A 32 KiB *body* with a small head is
fine — confirming the blow-up is the head-parse recursion, not body size.

**Why the index-native serve does not save it either.** `serveHeadIdx`
(`Datapath/ServeHeadIdx.lean:108`) *does* decide its arms with the fuel-bounded
`parseArr`/`scanDCrlf` (safe). But its `/bulk` and `/health` arms are the only ones
served densely; **every other request falls through to
`servePipelineFull2 input.toList`** (lines 119, 120, 122) — straight back into the
unbounded `Arena.Parse.parse`. The code comments name this "the standing off-arm
residual." A 32 KiB junk request passes `gateB`, is not a dense arm, and crashes.

**The structure that permits it.** A `List UInt8`-typed parse whose scanners recurse
to a depth equal to the input length, with no bound between the socket and the
recursion.

**By-construction fix (fix-forward, proof-preserving).**
1. Give `findDoubleCrlf` a `@[csimp]` fuel-/cursor tail-recursive implementation and
   give `crlfPositionsGo` an accumulator (tail) form — the *exact* pattern already
   used for `crlfPositions_eq_fast` / `parseHeaders_eq_fast` (`Arena/Parse.lean:160,
   418`): a new `findDoubleCrlfFast` + `@[csimp] findDoubleCrlf_eq_fast`, spec
   `findDoubleCrlf` untouched so every theorem over it stands. This makes **every
   caller** stack-safe with zero call-site edits. *Preferred*: it is the smallest
   surface and the proof technique is already in the file.
2. Better still, route the deployed off-arm/default serve through the **already-proven
   bounded** `parseArr` (`Datapath/IndexParse.lean:125`, whose `scanDCrlf` at
   `Datapath/Scan.lean:88` is fuel-bounded tail recursion) instead of
   `Arena.Parse.parse input.toList`. `parseArr_eq` (`IndexParse.lean:167`) and
   `parseIndexNative_refines` (`IndexParse.lean:222`) already prove byte-identity, so
   the ctx can be built index-native with no behavioural change. This removes the
   `input.toList` cons *and* the unbounded recursion in one move.

Gate: build green + `#print axioms` unchanged on the parse theorems + `cmp`
byte-identity of the served response on the existing demo requests + a 64 KiB-head
request now returns `431`/`414` instead of aborting.

---

## F2 — [SAFETY-CRASH] Large / fragmented WebSocket message overflows the serve stack (Autobahn 9.4.4)

**Rank: 2 (process kill on the WS data path; reproduces on 9.4.4).**

**Root cause (precise).** `run.log` shows `drorb-serve … has overflowed its stack /
fatal runtime error: stack overflow` right after `WS upgrade OK — connection open,
proven frame loop`. The WS data path is `drorbServeWsFrame`
(`Dataplane/Multi.lean:70`) → `Reactor.Ws.wsFeedFn` (`Reactor/Ws.lean:170`). Two
compounding structural hazards:

1. **Payload-length non-tail recursion.** Autobahn 9.4.x sends a large text message
   (9.4.4 ≈ 64 KiB+). Every byte-list transform over the payload recurses to
   depth = payload length:
   - `maskFrom` (unmask) — `Ws/Mask.lean:33`: `(b ^^^ key…) :: maskFrom key (i+1) bs`
     — cons before recurse, NON-tail, depth = payload.
   - reassembly concat `p.acc ++ f.payload` (`Ws/Reassembly.lean:64`) and
     `initial ++ mids.flatten ++ final` (`Reactor/Ws.lean:283`), plus
     `wsEncodeFn`'s `enc.2 ++ f.payload` (`Reactor/Ws.lean:185`) and the final
     `(out.frames.map wsEncodeFn).flatten` / `.toArray` (`Dataplane/Multi.lean:72-73`)
     — each a List `++`/`flatten`/`toList` linear in payload stack depth.
   - `frame.toList` (`Dataplane/Multi.lean:71`) marshals the whole ByteArray to a
     cons-list up front.
   For a 64 KiB+ payload these exceed the stack the same way F1 does.

2. **Fresh codec per recv (state loss + re-crossing the whole buffer).**
   `drorbServeWsFrame` starts from `({} : Proto.WsCodec)` — `recvBuf := []`,
   `reasm := .idle` — **every call** (`Dataplane/Multi.lean:71`), and the host
   `ws_frame_loop` (`blocking.rs:636`) hands each recv chunk to a *fresh* crossing
   (`blocking.rs:603` docstring admits "each chunk is fed to a fresh WebSocket
   codec"). So (a) a fragment split across TCP recvs **loses its reassembly state**
   (`decodeAll`'s leftover at `Reactor/Ws.lean:132` is discarded with the codec), and
   (b) when a large message *does* arrive whole in one recv, the entire payload
   crosses the List recursion of hazard (1) in a single call.

**The structure that permits it.** The proven WS engine is stateful and correct
(`WsCodec` carries `recvBuf`/`reasm`, `feedFrames_append` proves cross-feed
persistence, `Reactor/Ws.lean:217`) — but the export *throws the state away* each
call, and the payload transforms are List-recursion-per-byte.

**By-construction fix (fix-forward).**
1. **Persist the codec across recvs.** Add a stateful WS export (or an FFI-threaded
   `WsCodec` handle) so `recvBuf`/`reasm` survive between recvs — the proof
   `feedFrames_append` already justifies feeding batches incrementally. The host
   loop keeps one codec per connection instead of `{}` per recv. This directly
   realizes the `wsFeedFn_reasm` persistence the module already proves and closes the
   cross-recv fragment-loss correctness hole.
2. **Bound the per-byte recursion:** give `maskFrom` a `@[csimp]` tail/array
   implementation (accumulator or `Array.map` over the payload) with an
   `applyMask_eq_fast` bridge — same technique as F1, spec `maskFrom` untouched so
   `applyMask_involution` / `applyMask_length` stand. Cap the reassembled message
   length (RFC 6455 permits a max-message-size policy) so an attacker cannot force
   an unbounded concat.

Gate: 9.4.x cases return CLEAN close instead of `behavior=FAILED / stack overflow`;
`#print axioms` unchanged on the WS theorems; the `wsFeedFn` end-to-end `example`
(`Reactor/Ws.lean:386`) still `rfl`s.

---

## F3 — [HOT-PATH-List] Every request materializes the whole recv window as a cons-list

**Rank: 3 (taxes every single request; the dominant datapath cost).**

**Structure.** `Datapath/Span.lean` and the module docs are explicit: the deployed
serve is typed on `Proto.Bytes = List UInt8`, and `s.read` = `List.ofFn`
(`Span.lean:71`) conses **one heap cell per received byte** before a single byte is
parsed. Every deployed export begins `input.toList`:
`servePipelineFull2` via `ctxOf input.toList` (`Deploy.lean:1065`), the metered
exports (`Dataplane.lean:915, 972, 984`), `drorbUpgradeGate`
(`Multi.lean:256`), `drorbServeWsFrame` `frame.toList` (`Multi.lean:71`),
`drorbServeDatagram` `dg.toList` (`Multi.lean:140`).

**Why it is a footgun, not just slow.** The cons-list is *also* the substrate F1/F2
overflow on, and every downstream stage (parse, slice, gzip, html-rewrite, serialize)
re-walks it. It is the single structural reason the datapath cannot be zero-copy.

**By-construction fix.** The tree already proves the escape:
`parseIndexNative`/`parseArr` read the borrowed window **by index** with one
`Array.extract` (`spanArr`, `IndexParse.lean:199`, `O(len)` buffer copy, no per-byte
cons) and `parseArr_eq`/`parseIndexNative_refines` prove byte-identity. Wire the
deployed serve to build its ctx from `parseIndexNative`/`parseArr` (span in, no
`s.read`), so the `List UInt8` of the request appears only in the *spec* (the RHS of
the refinement), never computed. This is the "request-cons-removal seam" the module
docstring names as its purpose — it is proven and simply not yet on the deployed
path. Subsumes the F1 off-arm fix.

---

## F4 — [HOT-PATH-List] The 1 MiB `/bulk` body re-crossed as a List by the pipeline transforms (body-cliff)

**Rank: 4 (a per-request O(body) List cliff on the bulk route; partially dodged).**

**Structure.** `Reactor.App.bulkBody = List.replicate 1048576 0x61`
(`ServeDenseFullReal.lean:9`). In the *pure* `deployStagesFull2` fold the gzip stage
(`Reactor/Stage/Gzip.lean:78`, `gzipBody` → `Gzip.gzipStored r.body`) and the
html-rewrite stage re-cross the whole body as a `List UInt8`
(`gzipStored` at `Gzip.lean:167` is a `List` `++` chain over the body; `crc32` folds
it, `Gzip.lean:53`). Serializing then appends the body to the head — `serialize`'s
final `++` shares the right operand (`SerializeFast.lean` docstring), so serialize
itself is body-optimal, but the *transform stages upstream of it* are not.

**Current mitigation (and its limit).** `serveDenseIdx`/`serveHeadIdx` special-case
the `/bulk` arm to emit `bulkBodyDense` — a genuine `ByteArray`
(`ServeDenseFullReal.lean:96`, `Array.mkArray`, never a 1 MiB List) — appended to a
dense head (`ServeHeadIdx.lean:115`). So the body-cliff is dodged **only on the two
hardcoded dense arms**. Any other body-bearing route (config `respond`, static files,
vhost bodies, the 404 catch-all) still flows the `List UInt8` body through the full
transform fold. The dense arms are a per-route hand-collapse, not a structural
guarantee.

**By-construction fix.** Make the body a `ByteArray`-backed representation *through
the Stage pipeline*, not just at the two dense arms — i.e. lift the `ResponseBuilder`
body to a borrowed/owned `ByteArray` and prove the transform stages (gzip,
html-rewrite) operate on it index-native, mirroring `bulkBodyDense`'s
`Array.mkArray`-not-`List.replicate` move. Then no route materializes a large-body
List and the body-cliff is impossible by construction rather than dodged per route.
`ServePolyFull` is named in-tree as the open multi-file re-proof for exactly this.

---

## F5 — [HOT-PATH-List] Double head-materialization on the routing decision (off the dense arms)

**Rank: 5 (every routed request pays `arenaToProto`/`protoReqOf` at least once).**

**Structure.** `arenaToProto` (`Reactor/Config.lean:72`) → `protoReqOf`
(`Config.lean:51`) resolves **every** head field — method, target, version, and each
header name *and* value — back into fresh `List UInt8` via `resolveBytes`
(`Config.lean:42`), plus a keep-alive fold. `ServeHeadIdx.lean:8-12` documents that
the old dense serve paid this *twice* per request (once per arm guard) and at least
once just to route. The parsed `Proto.Request` fields are themselves `List`-typed
(named residual in `ServeDenseIdx.lean:57`).

**By-construction fix.** `bulkIdxB`/`healthIdxB` (`Datapath/HeadIdx.lean`) already
decide arms by **index probes** on the arena head — header names compared by index,
values/target resolved only on demand — and `bulkIdxB_eq`/`healthIdxB_eq` prove
decision-equality to the `protoReqOf` path. Extend the index-native head view to the
*general* routing decision (not just the two dense arms) so `arenaToProto` is never
called on the deciding path. This is the `HeadIdx` kit generalized; the equalities to
reuse are already proven.

---

## F6 — [ALLOC-CHURN] `String.fromUTF8?` + `.toList`/`.drop`/`.take` config re-marshalling per request

**Rank: 6 (every metered-config request re-lists and re-scans the config frame).**

**Structure.** `drorbServeMeteredCfg` (`Dataplane.lean:915`) does `input.toList`, then
`rest.take cfgLen` / `rest.drop cfgLen` (two O(n) list walks), then
`String.fromUTF8?` over the config bytes and `Dsl.Config.parseChars` + `parsePolicy`
— **per request**. `drorbServeMeteredCfgConformant` (`Dataplane.lean:1026`) re-frames
`cfgHead ++ req.toList` (another full concat) before calling the inner. The config is
fixed for the process lifetime but is re-parsed and re-listed on every request.

**By-construction fix.** Parse the config **once** at boot into an owned structure and
have the per-request seam take a borrowed request span + a reference to the pre-parsed
config, instead of re-marshalling a `cfgLen :: config :: request` frame each call.
The Rust host already caches `config::get()` (`blocking.rs:410`); the seam should
accept the already-parsed deployment rather than re-deriving it from bytes. Removes
the per-request `fromUTF8?`/`parseChars`/two-drop-take churn.

---

## F7 — [ALLOC-CHURN] Rate-gate `List.replicate seq 0` consed just to read its length

**Rank: 7 (a per-request O(seq) cons whose only use is `.length`).**

**Structure.** `ctxOfMetered` stashes the per-connection request index as
`List.replicate connSeq (0 : UInt8)` under `seqKey` (`Deploy.lean:1550`), and the rate
gate reads it back via `seqOf` = `.length` (`ServeMeteredHeadIdx.lean:81`). On a
long-lived keep-alive connection `connSeq` grows unboundedly, so request *N* conses an
*N*-element list purely to take its length.

**Current mitigation (and its limit).** `ServeMeteredHeadIdx.rateGateB`
(`ServeMeteredHeadIdx.lean:66`) decides the rate gate on `seq : Nat` directly (no
replicate) and `rate_admits_metered` proves it equals the ctx path — but this is only
used by the *index-native metered* serve; the deployed `servePipelineFull2Metered`
fold still builds `ctxOfMetered` with the replicate.

**By-construction fix.** Carry the standing count as a `Nat` attribute (not a
length-encoded list) in the metered ctx so no per-request replicate exists on any
path; `rateGateB`/`rate_admits_metered` already prove the `Nat`-direct gate is
equal — wire it as the deployed representation.

---

## F8 — [ALLOC-CHURN] Header canonicalization sidecar list-append (bounded, but quadratic-shaped)

**Rank: 8 (bounded by the 64-header cap, so DoS-safe; still a structural churn seam).**

**Structure.** The *spec* `canonNameEntry` (`Arena/Parse.lean:257`) grows the sidecar
with `sidecar ++ raw.map lowerByte` (copies the whole growing sidecar) and indexes it
by `sidecar.length` (walks it) — O(sidecar²) over a header run that lowercases.

**Already fixed by construction — noted for completeness.** `canonNameEntryAcc` /
`parseHeadersAcc` (`Arena/Parse.lean:271, 376`) thread a **flat `Array` sidecar**
(`Array.size` O(1), amortized-O(name) append) and `parseHeaders_eq_fast`
(`Arena/Parse.lean:418`) installs it as the `@[csimp]` compiled impl. `defaultMaxHeaders
= 64` (`Arena/Parse.lean:426`) caps the surface. This one is *not* an open footgun —
it is the reference pattern the F1/F2 tail-recursion fixes should copy. Listed so the
map is complete and to point at the canonical technique.

---

## Cross-cutting: the Rust host paths are NOT the crash surface

For the record (the crashes are Lean-side): the Rust framing `next_request`
(`http.rs:78`) uses iterative `windows(4)`/`windows(2)` scans and a hard
`REQUEST_CAP = 8 MiB` (`http.rs:14`) — bounded, no recursion. Per-request buffers are
pooled (`blocking.rs:154`, `PooledBuf`), so the Rust side allocates nothing
steady-state. The io_uring path has a genuine zero-copy borrow fast path
(`uring.rs:on_recv_br`, buffer-select + `next_request(slice)`). The host is the
**well-behaved** layer; every ranked footgun above is in the proven core's `List
UInt8` representation and its non-tail recursions. The single highest-leverage
structural change is F3 (span-native request representation), which subsumes F1's
off-arm fix and removes the substrate F1/F2/F4/F5 all overflow or re-walk.

---

## Top-5 structural rewrites (highest leverage first)

1. **Bounded framing scan (kills F1).** `@[csimp]` tail/fuel-cursor `findDoubleCrlf`
   + accumulator `crlfPositionsGo`, spec untouched — every parse caller becomes
   stack-safe with no call-site edits. Smallest surface, proof technique already in
   `Arena/Parse.lean`.
2. **Span-native deployed serve (kills F3, subsumes F1 off-arm + F5).** Build the
   deployed ctx from `parseArr`/`parseIndexNative` (index reads + one `Array.extract`)
   instead of `Arena.Parse.parse input.toList`; `parseArr_eq` /
   `parseIndexNative_refines` already prove byte-identity. The request `List` appears
   only in the spec.
3. **Stateful, bounded WebSocket data path (kills F2).** Persist `WsCodec`
   (`recvBuf`/`reasm`) across recvs via a stateful export (justified by
   `feedFrames_append`), `@[csimp]` tail `maskFrom`, and a max-message-size cap.
   Closes both the cross-recv fragment-loss correctness hole and the payload-recursion
   overflow.
4. **`ByteArray`-backed response body through the Stage pipeline (kills F4).** Lift
   the `ResponseBuilder` body off `List UInt8` so gzip/html-rewrite/serialize operate
   index-native for *every* route, generalizing the `bulkBodyDense` dodge into a
   structural guarantee (`ServePolyFull` is the named open re-proof).
5. **Boot-once owned config + `Nat` standing count (kills F6, F7).** Parse the
   deployment once at boot into an owned structure the per-request seam borrows, and
   carry the keep-alive index as a `Nat` (not `List.replicate`), removing the
   per-request `fromUTF8?`/re-frame churn and the O(seq) length-cons.

---

## Residuals / honesty

- No code was changed; this is a read-only map. The F1/F2 fixes are stated against the
  in-tree `@[csimp]` refinement pattern (`crlfPositions_eq_fast`,
  `parseHeaders_eq_fast`) which is the proven, byte-identity-preserving mechanism —
  but the tail-recursive `findDoubleCrlfFast`/`maskFromFast` and their `_eq_fast`
  bridges are *not yet written*; they are the fix, not a claim of one.
- F1's threshold (~30 KiB) and the 9.4.4 overflow are grounded in
  `docs/engine/review/CONFORMANCE-EXT.md` (Z1) and
  `conformance/ws/run.log` (`overflowed its stack`) respectively; the exact stack
  depth at which the default ~8 MiB thread stack is exhausted is
  frame-size-dependent, hence the ~28→32 KiB bisect band rather than a single number.
- The dense-arm mitigations (F4, F5, F7) are real and proven but per-route/hand-done;
  they reduce blast radius, they do not make the footgun structurally impossible. The
  ranking reflects the *structural* hazard that survives them.
