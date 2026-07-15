//! The Lean seam: boot the proven runtime and cross it, once per request.
//!
//! Every crossing is one call to the exported `drorb_serve`
//! (`ByteArray -> ByteArray`), the same proven pipeline the shipped binaries
//! run. The bytes read off the wire go in unchanged and the proven response
//! bytes come back unchanged; the host decides nothing about a request's
//! meaning.
//!
//! ## Concurrency model
//!
//! The Lean runtime is a process-global singleton: `initialize_Dataplane`
//! installs the module's top-level constants once, and there is no way to stand
//! up N independent runtimes in one process. So a per-worker runtime is not an
//! option, and rather than rely on the compiled serve being safe to call from
//! many threads (the closure inc/dec's runtime objects and the small allocator
//! keeps thread-local state), the host confines every seam crossing to a single
//! dedicated thread that owns the runtime. That thread runs [`lean_boot`] and is
//! the only thread that ever calls `drorb_serve`; correctness never depends on
//! the compiled serve being reentrant.
//!
//! IO concurrency lives elsewhere (the event loops in `blocking`/`uring`): many
//! connections read and write in parallel and funnel completed requests to this
//! one serve thread over a channel. The serve computation itself is serialized
//! on the runtime-owner thread — the deliberate trade, and the one shared
//! resource in an otherwise share-nothing design (see `SINGLE-OWNER` note in
//! [`spawn_serve_thread`]).
//!
//! `DRORB_SERVE_OWNERS=k` (opt-in, default 1) lifts that serialization for the
//! byte-serve seams: still ONE process-global runtime, but `k` owner threads
//! attached to it (`lean_initialize_thread`), each with its own job channel,
//! with every connection/shard pinned to one owner. The safety argument and its
//! limits are on [`spawn_attached_owner`].

use std::net::IpAddr;
use std::slice;
use std::sync::Arc;
use std::sync::mpsc::{Receiver, Sender, channel};

use crate::pool::{BufferPool, PooledBuf};

/// Opaque Lean heap object. We only ever hold `*mut LeanObject` and hand it
/// straight back across the FFI; its layout is the runtime's concern.
#[repr(C)]
struct LeanObject {
    _private: [u8; 0],
}

unsafe extern "C" {
    // Real exported runtime + module symbols (libleanshared / the drorb archive).
    fn lean_initialize_runtime_module();
    fn lean_io_mark_end_initialization();
    fn initialize_Dataplane(builtin: u8, world: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve] drorbServe : ByteArray -> ByteArray` — the proven
    /// pipeline (TCP byte stream: HTTP/1.1 + h2c fork to the real H2 engine).
    /// Consumes its argument, returns an owned ByteArray.
    fn drorb_serve(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_flat] drorbServeFlat : ByteArray -> ByteArray` — the
    /// A/B twin of `drorb_serve`, byte-identical for every input
    /// (`Dataplane.drorbServeFlat_eq`) but rendering the HTTP/1.1 response straight
    /// into a flat ByteArray (`Reactor.ServeArr.serveArr`), skipping the deployed
    /// path's response-head List round-trips. Same ABI as `drorb_serve`; selected
    /// on the `Seam::Http` path only when `DRORB_FLAT=1` so the flat vs. List
    /// materialization cost is measurable A/B in one binary.
    fn drorb_serve_flat(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_span] drorbServeFlatEcho : ByteArray -> ByteArray`
    /// (Datapath.ServeFlat) — the ASSEMBLED flat serve: index-native parse
    /// (`parseIndexNative`, no request cons) ⟶ flat security-header stage
    /// (`flatSecurityStage`, an `Array.push` fold) ⟶ flat `ByteArray` body (echoed
    /// request, never a `List`) ⟶ flat egress (`serializeFlatB`, bulk append). NO
    /// runtime `List UInt8` for the request, headers, or body. Byte-identical to
    /// `drorb_serve_span_list` (`Datapath.ServeFlat.serveFlatEcho_refines`). Same
    /// `ByteArray -> ByteArray` ABI as `drorb_serve`; selected on the metered serve
    /// path only when `DRORB_SPAN=1`, so the cons-free flat serve's cost is
    /// measurable A/B against its `List` twin (`DRORB_SPAN=2`).
    fn drorb_serve_span(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_span_list] drorbServeListEcho : ByteArray -> ByteArray`
    /// (Datapath.ServeFlat) — the bit-for-bit `List` TWIN of `drorb_serve_span`:
    /// the SAME response, computed the deployed cons-list way (`h1ParseFn s.read`
    /// conses the whole request, `Reactor.serialize` over a `List` header spine and
    /// an `input.data.toList` body cons, then `ByteArray.mk … .toArray`). The A/B
    /// control for the flat serve; selected when `DRORB_SPAN=2`.
    fn drorb_serve_span_list(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_full] drorbServeFlatFull : ByteArray -> ByteArray`
    /// (Datapath.ServeFlatFull) — the ASSEMBLED FULL flat serve: the REAL deployed
    /// 14-stage pipeline (`Reactor.ServeArr.respOf`, all of jwt/ipfilter/rate/cache/
    /// redirect/traversal/policy/headerRewrite/cors/gzip/htmlrewrite/security/header,
    /// real route table + handler — NOT the echo) rendered through the FLAT egress
    /// serializer `serializeFlatB` (flat `HdrBlock` header render + genuine `ByteArray`
    /// body, no response-head `List` spine / `body.toArray`-of-a-cons). BYTE-IDENTICAL
    /// to the deployed `drorb_serve` for every input, h2c fork AND the full HTTP/1.1
    /// fold (`Dataplane.serveFlatFull_eq_drorbServe`) — so it serves the SAME bytes as
    /// the deployed default, a deployed-representative flat serve (not the echo). Same
    /// `ByteArray -> ByteArray` ABI as `drorb_serve`; selected when `DRORB_SPAN=3`.
    fn drorb_serve_full(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_bodypoly] drorbServeBodyPolyArr : ByteArray -> ByteArray`
    /// (Datapath.ServeFlatBodyPoly) — the BODY-DENSE poly serve: parse (index-native) ⟶
    /// the compress codec-tag body stage ⟶ serialize, the BODY carried DENSE as a
    /// `ByteArray` through `servePoly`'s fold (`ByteSeq` instance = bulk `copySlice`
    /// append, the 8 KB body never a `List UInt8`). Byte-identical to its `List` twin
    /// `drorb_serve_bodypoly_list` (`serveBodyPoly_refines`) — the A/B isolates ONLY the
    /// body representation. Same `ByteArray -> ByteArray` ABI; selected when `DRORB_SPAN=5`.
    fn drorb_serve_bodypoly(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_bodypoly_list] drorbServeBodyPolyList : ByteArray -> ByteArray`
    /// (Datapath.ServeFlatBodyPoly) — the byte-identical `List` TWIN of
    /// `drorb_serve_bodypoly`: the SAME parse ⟶ codec-tag ⟶ serialize, but the body as
    /// `input.data.toList` (the 8 KB per-byte cons, K2) and the codec tag a `List` prepend.
    /// The cons-full control for the body-dense serve; selected when `DRORB_SPAN=6`.
    fn drorb_serve_bodypoly_list(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_poly] drorbServePolyFull : ByteArray -> ByteArray`
    /// (Datapath.ServePolyFull) — the FULL POLY serve: the REAL deployed 14-stage routed
    /// response rendered through the polymorphic egress fold (`HdrSeq.foldPush` header block
    /// over the flat `HdrBlock` + `ByteArray` body). Byte-identical to the deployed
    /// `drorb_serve` for every input (`Dataplane.servePolyFull_eq_drorbServe`), so it serves
    /// the SAME bytes as the deployed default — the deployed-representative full-poly serve.
    /// Same `ByteArray -> ByteArray` ABI as `drorb_serve`; selected when `DRORB_SPAN=7`.
    fn drorb_serve_poly(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_dense] drorbServeDenseArr : ByteArray -> ByteArray`
    /// (Datapath.ServeDense) — the GENUINELY-DENSE multi-stage serve FOLD: parse
    /// index-native (no `input.toList`) ⟶ a 3-stage response-transform header fold
    /// (`securityheaders`/`cors`/`header`) over the flat `HdrBlock` (`Array.push`/
    /// `Array.filter`) ⟶ `ByteArray`-body flat egress (`serializeFlatB`). Proven
    /// byte-identical to its `List` twin `drorb_serve_dense_list`
    /// (`serveDense_refines`); the A/B isolates ONLY the header/body representation.
    /// Same `ByteArray -> ByteArray` ABI; selected when `DRORB_SPAN=8`.
    fn drorb_serve_dense(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_dense_list] drorbServeDenseList : ByteArray -> ByteArray`
    /// (Datapath.ServeDense) — the bit-for-bit `List` TWIN of `drorb_serve_dense`: the
    /// SAME parse ⟶ 3-stage header fold ⟶ serialize, but the header block a
    /// `List (Bytes × Bytes)` and the body materialized as `input.data.toList` (the
    /// deployed cons way, K2). The cons-full control for the dense fold; selected when
    /// `DRORB_SPAN=9`.
    fn drorb_serve_dense_list(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_densefull] drorbServeDenseFull : ByteArray -> ByteArray`
    /// (Datapath.ServeDenseFull) — the dense serve that RUNS THE DEPLOYED BODY
    /// TRANSFORM DENSE: parse index-native ⟶ 3-stage header fold ⟶ the deployed
    /// html-rewrite body transform run over the `ByteArray` body BY INDEX
    /// (`rewriteBytesDense`, no `input.toList`; byte-identical to the deployed
    /// `rewriteBytes` by `rewriteBytesDense_refines`) ⟶ flat egress. Byte-identical
    /// to its `List` twin `drorb_serve_densefull_list` (`serveDenseFull_refines`).
    /// Same `ByteArray -> ByteArray` ABI; selected when `DRORB_SPAN=10`.
    fn drorb_serve_densefull(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_densefull_list] drorbServeDenseFullList : ByteArray ->
    /// ByteArray` (Datapath.ServeDenseFull) — the bit-for-bit `List` TWIN of
    /// `drorb_serve_densefull`: the SAME parse ⟶ 3-stage header fold ⟶ deployed body
    /// transform ⟶ serialize, but the header block a `List (Bytes × Bytes)` and the
    /// body the deployed `rewriteBytes input.data.toList` (the cons-list body walk +
    /// cons-list tokenizer, K2). The cons-full control for the dense body serve;
    /// selected when `DRORB_SPAN=11`.
    fn drorb_serve_densefull_list(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_densefull2] drorbServeDenseFull2 : ByteArray -> ByteArray`
    /// (Datapath.ServeDenseFull2) — the FULLY-DENSE-TOKENIZER serve: the SAME parse ⟶
    /// 3-stage header fold ⟶ deployed html-rewrite body transform ⟶ egress as
    /// `drorb_serve_densefull` (DRORB_SPAN=10), but the body runs through
    /// `rewriteBytesDense2`, whose TOKENIZER STATE is fully dense (`FStateD`: a
    /// `ByteArray` current run + `Array DToken` tokens) — NO token `List UInt8` / per-byte
    /// `cons` on the compute path (the last cons `rewriteBytesDense` still paid via the
    /// deployed `feedF`'s `curRev : List UInt8`). Byte-identical to the SAME `List` twin
    /// `drorb_serve_densefull_list` (`serveDenseFull2_refines`), so `=12` serves no byte
    /// differently from `=11`/`=10`. `=12` vs `=11` (List twin) is the full body-transform
    /// A/B (compare to the ~2.35× of `=10` vs `=11`); `=12` vs `=10` isolates the
    /// token-`List` increment. Same `ByteArray -> ByteArray` ABI; selected when DRORB_SPAN=12.
    fn drorb_serve_densefull2(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_gated] drorbServeGated : ByteArray -> ByteArray`
    /// (Datapath.ServeGated) — the CONTENT-TYPE-GATED serve: parse index-native ⟶
    /// 3-stage header fold ⟶ the body GATED on the response `Content-Type`. On
    /// `text/html` it runs the dense deployed html-rewrite (`rewriteBytesDense`, the
    /// same bytes `=10`); on ANYTHING ELSE (the common case: JSON / octet-stream /
    /// images) the body is the borrowed `ByteArray` handed STRAIGHT to the flat egress
    /// — NEVER tokenized, NEVER consed = a zero-copy passthrough. So a non-HTML body is
    /// NOT capped by the ~2.35× tokenizer ceiling and its `<`/`>` are preserved (the
    /// deployed unconditional serve corrupts them). Byte-identical to its `List` twin
    /// `drorb_serve_gated_list` (`serveGated_refines`). Same `ByteArray -> ByteArray`
    /// ABI; selected when DRORB_SPAN=13.
    fn drorb_serve_gated(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_gated_list] drorbServeGatedList : ByteArray -> ByteArray`
    /// (Datapath.ServeGated) — the byte-identical `List` twin of `drorb_serve_gated`:
    /// the SAME parse ⟶ 3-stage header fold ⟶ content-type-gated body, but with the
    /// header block a `List (Bytes × Bytes)` and the body materialised as a `List UInt8`
    /// (`rewriteBytes input.data.toList` on HTML, `input.data.toList` on passthrough).
    /// `=13` vs `=14` isolates ONLY the dense-vs-`List` representation cost on the gated
    /// common-case body path. Same `ByteArray -> ByteArray` ABI; selected when DRORB_SPAN=14.
    fn drorb_serve_gated_list(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_split_head] drorbServeSplitHead : ByteArray -> ByteArray`
    /// (Datapath.ServeSplit) — the ZERO-COPY-BODY split serve. Computes ONLY the
    /// response HEAD (status line + headers + Content-Length + the blank-line
    /// separator), densely; the body is NOT appended (the `serializeFlatB ... ++
    /// fbody.data` the gated serve `=13` still does is gone). The host writes this head
    /// THEN the borrowed request body straight to the socket via `writev` — the body is
    /// never copied into an output ByteArray. `Content-Length` is `input.size` (the echo
    /// body is the whole request buffer). Proven head ++ body = the appended serve and
    /// byte-identical to the deployed serialize (`serveSplit_reassemble`,
    /// `serveSplitHead_append_eq_serialize`). Selected when `DRORB_SPAN=15`; the shard
    /// splices the body (`crate::serve::is_split_span`).
    fn drorb_serve_split_head(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_ultra] drorbServeUltra : ByteArray -> ByteArray`
    /// (Datapath.ServeUltra) — the COMBINED fast serve exemplar: parse index-native
    /// ⟶ 3-stage dense header fold ⟶ content-type-GATED body (non-HTML = ZERO-COPY
    /// passthrough, `text/html` = the FULLY-DENSE tokenizer `rewriteBytesDense2`, NO
    /// token `List`) ⟶ flat egress (`serializeFlatB`). Same parse/gate/egress shape as
    /// `drorb_serve_gated` (`=13`) but the HTML branch runs the fully-dense tokenizer
    /// (`=12`'s `rewriteBytesDense2`) instead of `rewriteBytesDense`. Proven
    /// byte-identical to its `List` twin (`serveUltra_refines`) AND to the deployed
    /// gated serve `=13` (`serveUltra_eq_serveGated`). Same `ByteArray -> ByteArray`
    /// ABI; selected when `DRORB_SPAN=16`.
    fn drorb_serve_ultra(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_ultra_list] drorbServeUltraList : ByteArray -> ByteArray`
    /// (Datapath.ServeUltra) — the byte-identical `List` twin of `drorb_serve_ultra`:
    /// the SAME parse ⟶ 3-stage header fold ⟶ content-type gate, but the body is the
    /// deployed `rewriteBytes input.data.toList` (HTML) / `input.data.toList`
    /// (passthrough) and the response is rendered by the deployed `Reactor.serialize`.
    /// `=16` vs `=17` isolates the dense-vs-`List` cost on the combined gated path. Same
    /// `ByteArray -> ByteArray` ABI; selected when `DRORB_SPAN=17`.
    fn drorb_serve_ultra_list(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_dense_real] drorbServeDenseReal : ByteArray -> ByteArray`
    /// (Datapath.ServeDenseReal) — the RUNTIME-DENSE full serve, the deployed-`/bulk`
    /// body-cliff fix. Forks exactly as the deployed serve (h2c preface → real H2, else
    /// HTTP/1.1); on the H1 path a decidable guard (`BulkArm`, evaluated on the SMALL
    /// request) selects a plain `GET /bulk` on the admitted, non-gzip, non-CORS arm and
    /// emits the DENSE head (`renderHead` over the proven `HdrBlock` fold `denseHeadersBlock`
    /// — HEAD linchpin `denseHeaders_eq_deployed`) followed by the DENSE 1 MiB `Array` body
    /// (`bulkBodyDense`, `Array.mkArray`, NO per-byte `List` cons), bulk-appended; off the
    /// arm it is the deployed `servePipelineFull2` List serve. BYTE-IDENTICAL to the deployed
    /// `drorb_serve` for EVERY input (`Dataplane.serveDenseReal_eq_drorbServe`) — the `/bulk`
    /// dense arm serves the SAME bytes as the deployed List serve without ever consing the
    /// 1 MiB body. Same `ByteArray -> ByteArray` ABI as `drorb_serve`; selected when
    /// `DRORB_SPAN=18`. `=18` vs `=4` (deployed List serve) on `GET /bulk` is the
    /// dense-body-vs-List-body-cliff A/B.
    fn drorb_serve_dense_real(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_conformant] drorbServeConformant : ByteArray -> ByteArray`
    /// (Dataplane) — the RFC 7230/7231 CONFORMANCE serve: the deployed `drorbServe`
    /// wrapped by the proven conformance stages
    /// (`Reactor.ServeConformant.conformantServe`). Malformed requests short-circuit to
    /// their `4xx/5xx` (+Date) at the `validationStage` gate (missing/dup Host ⟶ 400,
    /// unknown method ⟶ 501, bad version ⟶ 505; absolute-form target normalized to
    /// origin-form); every other request routes through the UNCHANGED `drorbServe` and
    /// is post-processed with a `Date` header (F1) and, on `HEAD`, a body strip (B1).
    /// The inner `drorbServe` is byte-identical to the deployed serve — the dense/poly
    /// family is untouched. Same `ByteArray -> ByteArray` ABI as `drorb_serve`; selected
    /// on EVERY HTTP serve job when `DRORB_SPAN=19`. This is the serve the RFC
    /// conformance probe (`conformance/rfc_conformance.py`) drives to 17/17.
    fn drorb_serve_conformant(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_head_idx] serveHeadIdx : ByteArray -> ByteArray`
    /// (Datapath.ServeHeadIdx) — the INDEX-NATIVE-HEAD serve, THE DEPLOYED
    /// `Seam::Http` DEFAULT: ONE arena parse per request (`parseArr` off the
    /// borrowed window), BOTH dense arms decided by index probes on the arena head
    /// (`bulkIdxB`/`healthIdxB` — no `arenaToProto`/`protoReqOf` List
    /// materialization on the deciding path), the proven dense emitters on the
    /// arms; off both arms (and on the h2c preface) the deployed serve verbatim.
    /// Proven byte-identical to `drorb_serve` for EVERY input
    /// (`Dataplane.serveHeadIdx_eq_drorbServe` = `serveHeadIdx_refines` +
    /// `deployedServeRef_eq_drorbServe`), so the cutover changes NO served byte.
    /// Same `ByteArray -> ByteArray` ABI as `drorb_serve`; also selectable A/B when
    /// `DRORB_SPAN=24` (`=24` vs `=21` isolates the parse-once head read vs the
    /// double-parse index-decided serve; `=24` vs `=4` the whole index-native win).
    fn drorb_serve_head_idx(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_conformant_head_idx] drorbServeConformantHeadIdx :
    /// ByteArray -> ByteArray` (Dataplane) — the SAME RFC-conformance wrapper as
    /// `drorb_serve_conformant`, its inner swapped for the index-native-head serve
    /// (`drorb_serve_head_idx` above). THE DEPLOYED NON-METERED `Seam::Http`
    /// DEFAULT crossing (no `DRORB_SPAN`): proven byte-identical to
    /// `drorb_serve_conformant` for EVERY input
    /// (`Dataplane.serveConformantHeadIdx_eq_drorbServeConformant` — the wrapper
    /// consults its inner only pointwise), so the conformance edges (C1/C2/B2/G1/C3
    /// gate, Date F1, HEAD-strip B1) are untouched. Same ABI as `drorb_serve`.
    fn drorb_serve_conformant_head_idx(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_conformant_dense] serveConformantDenseIdx : ByteArray ->
    /// ByteArray` (Datapath.ServeConformantDense) — the SAME RFC-conformance wrapper as
    /// `drorb_serve_conformant`, its inner swapped for the index-decided DENSE serve
    /// (`Datapath.ServeDenseIdx.serveDenseIdx`): the h2c fork and the `/bulk`-arm guard
    /// are decided by INDEX PROBES off the borrowed window, and the dense arm emits the
    /// dense head (constant `x-upstream`, index-native `x-corr`) + the dense 1 MiB
    /// `Array` body — NO `input.toList` on the dense-arm compute path. Proven
    /// byte-identical to `drorb_serve_conformant` for EVERY input
    /// (`serveConformantDenseIdx_eq_drorbServeConformant`). Same ABI; selected when
    /// `DRORB_SPAN=20`. `=20` vs `=19` on `GET /bulk` isolates the inner body-cliff +
    /// arm-decision cost under the SAME conformance wrapper.
    fn drorb_serve_conformant_dense(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_dense_idx] serveDenseIdx : ByteArray -> ByteArray`
    /// (Datapath.ServeDenseIdx) — the BARE index-decided dense serve (no conformance
    /// wrapper): h2c fork + /bulk-arm guard decided by INDEX PROBES, dense head with
    /// constant x-upstream + index-native x-corr, dense 1 MiB body. Byte-identical to
    /// `drorb_serve` (serveDenseIdx_refines + deployedServeRef_eq_drorbServe). Selected
    /// when `DRORB_SPAN=21`. `=21` vs `=18` isolates the index-native arm decision +
    /// dense head scalars vs the List-decided arm with List scalars.
    fn drorb_serve_dense_idx(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_conformant_fast] serveConformantFastIdx : ByteArray ->
    /// ByteArray` (Datapath.ServeConformantFast) — the CONFORMANT-DENSE serve with the
    /// FUSED response post-processor: same conformance gates and same index-decided
    /// dense inner as `drorb_serve_conformant_dense` (`=20`), but the wrapper's
    /// `Date`-splice + `x-corr` head-scrub rewrite only the HEAD and attach the
    /// unchanged 1 MiB body ONCE (`ByteArray.copySlice`, `scrubDateBA`) instead of
    /// re-copying the full response in each post-processor (`injectDateBA` +
    /// `scrubCorrBA` — ~4 whole-body memcpys per `/bulk` hit). Byte-identity to `=20`
    /// is `#guard`-pinned (evaluator) on the real 1 MiB `/bulk` response + adversarial
    /// head shapes; the general fusion theorem is the named next rung. Same
    /// `ByteArray -> ByteArray` ABI; selected when `DRORB_SPAN=22`. `=22` vs `=20` on
    /// `GET /bulk` isolates the wrapper body-recopy cost; `=22` vs `=18` (bare dense)
    /// is the remaining conformance-wrapper overhead.
    fn drorb_serve_conformant_fast(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_conformant_zc] serveConformantZcIdx : ByteArray ->
    /// ByteArray` (Datapath.ServeZc) — the ZERO-COPY-BODY split of the fused
    /// conformant serve (`=22`): the response is 1-byte-TAGGED. `0x01 :: head`
    /// when the fast `/bulk` arm fires (the head already fused/scrubbed; the
    /// HOST attaches the process-static constant body by reference — the 1 MiB
    /// body never crosses the seam and is never copied), else `0x00 :: full`
    /// where `full` is byte-for-byte `drorb_serve_conformant_fast`. Reassembly
    /// identity is `#guard`-pinned on the same battery as the `=22` fusion
    /// guards. Same `ByteArray -> ByteArray` ABI; selected when `DRORB_SPAN=23`.
    /// `=23` vs `=22` on `GET /bulk` isolates the remaining whole-body copies
    /// (inner append + wrapper attach + host seam copy).
    fn drorb_serve_conformant_zc(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_bulk_body] bulkBodyForHost : ByteArray -> ByteArray`
    /// (Datapath.ServeZc) — the constant `/bulk` body, fetched ONCE at serve-thread
    /// boot to materialize the process-static send buffer the `=23` split arm
    /// gather-writes. The argument is ignored (uniform marshalling).
    fn drorb_bulk_body(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_metered] drorbServeMetered : ByteArray -> UInt64 ->
    /// ByteArray -> ByteArray` — the same deployed HTTP/1.1 fold as `drorb_serve`,
    /// but the host supplies the connection context the two metered gates read:
    /// `peer` (the client address, family-tagged bit-encoded per
    /// `Reactor.Stage.IpFilter.encodeAddr`) feeds the real IP-filter deny gate, and
    /// `seq` (the 0-based per-connection request index) feeds the real rate token
    /// bucket. Consumes both ByteArray arguments; returns an owned ByteArray. The C
    /// ABI passes `seq` as an unboxed `uint64_t` (leanc lowering).
    fn drorb_serve_metered(
        peer: *mut LeanObject,
        seq: u64,
        input: *mut LeanObject,
    ) -> *mut LeanObject;
    /// `@[export drorb_serve_pipeline_conformant] drorbServePipelineConformant :
    /// ByteArray -> UInt64 -> ByteArray -> ByteArray` (Dataplane) — THE consolidated
    /// deployed metered default. The proven RFC-conformance wrapper
    /// (`conformantServe`: 431 head limit -> validation gate -> framing gate -> Date ->
    /// `x-corr` scrub -> HEAD-strip) over the ONE flat consolidated pipeline
    /// (`Reactor.DeployPipeline.serveMeteredPipelineConformant` — the 43-stage
    /// ordered registry stated once, definitionally equal to the deployed onion),
    /// with the `/bulk` arm emitted DENSE (fully-stamped head + dense 1 MiB body, no
    /// per-byte `List` cons). Byte-identical to the pre-consolidation default for
    /// EVERY (peer, seq, input) (`serveMeteredPipelineConformant_eq_predecessor` /
    /// `_eq_deployed`). This is the SINGLE metered default crossing. Consumes both
    /// ByteArray arguments; `seq` crosses as an unboxed `uint64_t`.
    fn drorb_serve_pipeline_conformant(
        peer: *mut LeanObject,
        seq: u64,
        input: *mut LeanObject,
    ) -> *mut LeanObject;
    /// `@[export drorb_serve_metered_cfg] drorbServeMeteredCfg : ByteArray -> UInt64
    /// -> ByteArray -> ByteArray` (Dataplane) — the Braid-0 seam: the same metered
    /// gate chain as `drorb_serve_metered` (`peer`/`seq` in scope), but the request
    /// bytes are cfg-FRAMED `cfgLen(4 BE) :: config :: request`. The proven core
    /// parses `config` and serves through `servePipelineOfMetered (denoteOn
    /// defaultDeployment pc)` — the connection-aware fold over the CONFIG's route
    /// table. A routeless / empty config (`cfgLen = 0`) serves
    /// `servePipelineOfMetered defaultDeployment`, byte-identical to
    /// `drorb_serve_metered` (`servePipelineOfMetered_default`, `rfl`). Same ABI as
    /// `drorb_serve_metered`.
    fn drorb_serve_metered_cfg(
        peer: *mut LeanObject,
        seq: u64,
        input: *mut LeanObject,
    ) -> *mut LeanObject;
    /// `@[export drorb_serve_metered_braided] drorbServeMeteredBraided : ByteArray ->
    /// UInt64 -> ByteArray -> ByteArray` (Dataplane) — the metered fold over
    /// `Reactor.Deploy.braidedDeployment` (`defaultDeployment` with its middleware chain
    /// = `braidedChain`: the proven forward-auth gate + request-id echo at the head).
    /// Same ABI as `drorb_serve_metered` (`peer`/`seq` in scope, `input` the raw HTTP/1.1
    /// request — NOT cfg-framed). A request with no braid markers serves byte-for-byte
    /// `drorb_serve_metered` (`servePipelineOfMetered_braided_off_eq`); an `x-forward-auth`
    /// request short-circuits to the proven `401`, an `x-request-id` request is echoed.
    fn drorb_serve_metered_braided(
        peer: *mut LeanObject,
        seq: u64,
        input: *mut LeanObject,
    ) -> *mut LeanObject;
    /// `@[export drorb_serve_metered_conformant] drorbServeMeteredConformant : ByteArray
    /// -> UInt64 -> ByteArray -> ByteArray` (Dataplane) — the RFC-conformant DEFAULT
    /// metered serve: `Reactor.ServeConformant.conformantServe` wrapped around the plain
    /// metered fold `drorbServeMetered peer seq`. Validation (C1/C2/B2/G1/C3) runs FIRST,
    /// then the metered IP-filter/rate gates fire on the accepted request, then the
    /// response is finished with `Date` (F1) and, on `HEAD`, a body strip (B1). Same ABI
    /// as `drorb_serve_metered`; `input` the raw HTTP/1.1 request. This is the serve the
    /// deployed default (no `DRORB_SPAN`) crosses so every metered request is RFC-conformant.
    fn drorb_serve_metered_conformant(
        peer: *mut LeanObject,
        seq: u64,
        input: *mut LeanObject,
    ) -> *mut LeanObject;
    /// `@[export drorb_serve_metered_cfg_conformant] drorbServeMeteredCfgConformant :
    /// ByteArray -> UInt64 -> ByteArray -> ByteArray` (Dataplane) — the RFC-conformant
    /// DEFAULT config-driven metered serve (the seam the running Linux/io_uring default
    /// crosses). `input` is cfg-FRAMED `cfgLen(4 BE) :: config :: request`; the wrapper
    /// runs the conformance stages over the UNFRAMED request and re-frames the normalized
    /// request with the SAME cfgLen+config for the inner `drorbServeMeteredCfg`, so the
    /// config route table and the metered gates are untouched — only the RFC edges added.
    /// Same ABI as `drorb_serve_metered_cfg`.
    fn drorb_serve_metered_cfg_conformant(
        peer: *mut LeanObject,
        seq: u64,
        input: *mut LeanObject,
    ) -> *mut LeanObject;
    /// `@[export drorb_serve_metered_braided_conformant] drorbServeMeteredBraidedConformant
    /// : ByteArray -> UInt64 -> ByteArray -> ByteArray` (Dataplane) — the RFC-conformant
    /// metered BRAIDED serve (opt-in, `DRORB_BRAID`): `conformantServe` wrapped around
    /// `drorbServeMeteredBraided peer seq` (raw request `input`), so a braided deployment
    /// is ALSO RFC-conformant. Same ABI as `drorb_serve_metered_braided`.
    fn drorb_serve_metered_braided_conformant(
        peer: *mut LeanObject,
        seq: u64,
        input: *mut LeanObject,
    ) -> *mut LeanObject;
    /// `@[export drorb_serve_braided] drorbServeBraided : ByteArray -> ByteArray`
    /// (Dataplane) — the NON-metered braided serve (h2c fork + the braided HTTP/1.1
    /// fold). The `entry`-table twin of the metered braid; same ABI as `drorb_serve`.
    fn drorb_serve_braided(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_ws_frame]` (Dataplane.Multi) — one inbound masked
    /// WebSocket frame's bytes in; the proven `wsFeedFn`/`wsEncodeFn` echo bytes
    /// out. Same `ByteArray -> ByteArray` ABI as `drorb_serve`.
    fn drorb_serve_ws_frame(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_datagram]` (Dataplane.Multi) — one UDP datagram (a
    /// QUIC Initial packet) in; verified EverCrypt decrypt → proven H3 dispatch →
    /// served response bytes out (empty on any parse/AEAD-auth failure).
    fn drorb_serve_datagram(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_upgrade_gate]` (Dataplane.Multi) — a protocol-upgrade
    /// REQUEST's bytes in; the deployed `/admin` JWT auth gate runs on it. Returns
    /// the serialized 401 bytes if the upgrade targets a protected path with no /
    /// invalid credentials (the host writes them instead of 101), or EMPTY bytes
    /// if the upgrade is authorized (the host completes the RFC 6455 handshake).
    fn drorb_upgrade_gate(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_proxy_pick]` (Reactor.ProxyDial) — the proven reverse-proxy
    /// backend pick: `Proxy.selectChain` over the live-health-masked fleet,
    /// honouring health ejection, the circuit breaker, and sticky affinity. Input
    /// byte 0 = the health/breaker mask (bit `i` ⇒ backend `i` up), bytes 1.. =
    /// the sticky-affinity key; output = the decimal-ASCII chosen backend id, or
    /// EMPTY when no backend is eligible. Same `ByteArray -> ByteArray` ABI as
    /// `drorb_serve`; crossed only on the runtime-owner thread, then the host
    /// (`proxy_hook`/`proxy_dial`) dials the chosen backend off this thread.
    fn drorb_proxy_pick(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_lb_pick]` (Reactor.LoadBalance) - the proven CONFIG-POLICY +
    /// load-aware reverse-proxy pick: `Proxy.selectChain` for the config-declared LB
    /// policy chain over the live-health-masked, load-carrying fleet. Input frame:
    /// byte 0 = the config LB-policy byte (0 weighted round-robin, 1
    /// least-connections, 2 weighted-least-connections, else rendezvous hash), byte 1
    /// = the round counter, byte 2 = the health/breaker mask, byte 3 = the number `n`
    /// of per-backend load bytes, bytes 4..4+n = the live in-flight counts, the rest =
    /// the sticky-affinity key. Output = the decimal-ASCII chosen backend id, or EMPTY
    /// when no backend is eligible. Health ejection holds for EVERY policy byte
    /// (`Reactor.LoadBalance.pick_health_ejects`).
    fn drorb_lb_pick(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_step]` (Reactor.ServeStep) — the effect/continuation
    /// serve STEP: input byte 0 = the live health mask, bytes 1.. = the request;
    /// output is the encoded `Step` (byte 0 = tag: `0` DONE + response bytes, `1`
    /// YIELD proxyDial + backend-id byte + forward-request bytes). Same `ByteArray
    /// -> ByteArray` ABI, crossed on the runtime-owner thread.
    fn drorb_serve_step(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_proxy_stream_head]` drorbServeProxyStreamHead :
    /// ByteArray -> ByteArray (Dataplane) — the CL-trust streaming head seam. Input
    /// `reqLen(4 BE) :: request :: headLen(4 BE) :: upstreamHead :: bodyLen(4 BE)`;
    /// output the NON-GZIP transformed response head (proven a function of
    /// (request, upstream-head, body-LENGTH) — `Reactor.ServeStep.proxyRespHead_factors`),
    /// or EMPTY when the request accepts gzip (the head re-encodes; stay buffered).
    fn drorb_serve_proxy_stream_head(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_resume]` (Reactor.ServeStep) — resume the serve after
    /// the shell executed a yielded effect. Input frames the ORIGINAL request plus
    /// the effect result as `mask :: reqLen(4, big-endian) :: request :: result`;
    /// output is the resumed response bytes. Same ABI, same single-owner thread.
    fn drorb_serve_resume(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_step_cfg]` (Dataplane) — the config-driven serve STEP:
    /// input byte 0 = the deployment LB selector (`DRORB_LB_POLICY`), byte 1 = the
    /// health mask, bytes 2.. = the request. The proxy branch dials the backend the
    /// CONFIG-declared LB policy selects; selector `0` reproduces `drorb_serve_step`.
    fn drorb_serve_step_cfg(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_resume_cfg]` (Dataplane) — resume the config-driven
    /// serve: input byte 0 = the deployment LB selector, then the ORIGINAL
    /// `mask :: reqLen(4 BE) :: request :: result` frame. Replays
    /// `serveStepWith (deploymentDialChain sel)` so the resumed continuation matches
    /// the config chain the step used.
    fn drorb_serve_resume_cfg(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_l4_bind]` (Dataplane) — the layer-4 accept-surface
    /// projection: input byte 0 = the deployment selector; output = the newline-
    /// joined `bind\tpool\tmode\tid,id,…` lines the config DECLARES
    /// (`DeploymentConfig.l4Listeners`), empty for the default deployment.
    fn drorb_l4_bind(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_deployment_of_config]` (Dataplane) — parse an ARBITRARY
    /// textual `DeploymentConfig` (UTF-8 bytes in) into the running projections:
    /// output is `lb\t<policyByte>` then one `bind\tpool\tmode\tid,id,…` line per
    /// declared L4 listener, or EMPTY on a parse failure (the host then runs the
    /// byte-identical default). `Dsl.Config.parseChars` + `denoteOn defaultDeployment`.
    fn drorb_deployment_of_config(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_step_pol]` (Dataplane) — the effect/continuation STEP
    /// dialed by a config LB-policy byte: input byte 0 = the LB-policy byte (from
    /// `drorb_deployment_of_config`), byte 1 = the health mask, bytes 2.. = the
    /// request. The proxy branch dials the backend the parsed config's declared LB
    /// policy selects (`Dsl.Config.dialChainOfByte`).
    fn drorb_serve_step_pol(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_resume_pol]` (Dataplane) — resume the config-policy
    /// STEP: input byte 0 = the same LB-policy byte, then the ORIGINAL
    /// `mask :: reqLen(4 BE) :: request :: result` frame. Replays
    /// `serveStepWith (dialChainOfByte pol)` so the resumed continuation matches.
    fn drorb_serve_resume_pol(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_stream]` (Dataplane) — the streaming response-emit seam.
    /// Re-entrant by index: input `idx(4 BE) :: chunkSize(4 BE) :: request`; output
    /// `flags(1) :: chunkBytes`, where `flags` bit 0 = "more chunks follow" and bit 1
    /// = the keep-alive decision. Index 0 is the response HEAD chunk; 1.. are the
    /// bounded body chunks (`≤ chunkSize`). An EMPTY output means the index is past the
    /// last chunk. The chunks concatenate to the exact `drorb_serve` response
    /// (`serveChunkList_flatten`), so the host streams them out one at a time without
    /// ever holding the whole response. Same `ByteArray -> ByteArray` ABI, crossed on
    /// the runtime-owner thread.
    fn drorb_serve_stream(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_connect_gate]` (Reactor.Proxy.Connect) — the proven CONNECT
    /// tunnel admission gate. Input is UTF-8, newline-separated: line 0 = the
    /// `host:port` target, the remaining lines = the configured allow-list patterns
    /// (`*` = wildcard axis). Stance is default-deny. Output is a single byte: `1`
    /// ⇒ open the tunnel, `0` ⇒ refuse `403`. Same `ByteArray -> ByteArray` ABI.
    fn drorb_connect_gate(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_grpc_frame_len]` (Reactor.Proxy.Grpc) — parse a gRPC
    /// length-prefixed-message header. Input is at least the 5-byte header (flag +
    /// big-endian u32 length); output is the decimal-ASCII payload length so the
    /// host can find the message boundary / enforce max-message-size while
    /// streaming the h2 DATA through. EMPTY if fewer than 5 bytes.
    fn drorb_grpc_frame_len(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_static_resolve]` (Route.StaticResolve) — the static-file
    /// path decision: the relative target bytes (after the serving prefix) in;
    /// `0x01 ++ <resolved path, '/'-joined>` on accept, or the single byte `0x00`
    /// on reject (a decoded segment failed the UTF-8 gate) out. The resolution —
    /// split, percent-decode ONCE, clamped dot-segment walk — is the proven core's
    /// (`resolveRel_confined`: no input escapes a clean root, even under a
    /// `..`-popping filesystem walker), not a host reimplementation.
    fn drorb_static_resolve(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_static_decide]` (Route.StaticDecide) — the static lane's FULL
    /// response decision: `flags(1) :: len(8 BE) :: mtime(8 BE) :: nameLen(2 BE) ::
    /// name :: requestBytes` in (flags bit 0 = keep-alive intent, bit 1 = found);
    /// the encoded serving PLAN out — `1` a verbatim response (404 / 405 / 416 /
    /// 304 / every HEAD), `2` a 200 head to stream the whole file after, `3` a 206
    /// head plus one file window, `4` a 206 multipart/byteranges head plus per-part
    /// prefaces/windows and the closing tail. The method gate, the conditional
    /// (If-None-Match via the proven ConditionalRequest matcher + exact-date
    /// If-Modified-Since), the range parse/resolution, every header byte and every
    /// window bound are the core's (window_exact, partsWire_eq_multipartBody).
    /// EMPTY on a malformed frame (the host drops the connection).
    fn drorb_static_decide(input: *mut LeanObject) -> *mut LeanObject;
    /// `@[export drorb_serve_cfg]` (Dataplane) — serve one request under an operator
    /// config's ROUTE TABLE. Input framing `cfgLen(4 BE) :: configBytes ::
    /// requestBytes`; the proven `Dsl.Config.parseChars` parses the config and, when
    /// it declares routes, serves the request through `servePipelineOf (denoteOn
    /// defaultDeployment pc)` — the same fourteen-stage fold over the config's route
    /// table (redirect/respond/static answered directly). A parse failure / routeless
    /// config serves the byte-identical default. Same `ByteArray -> ByteArray` ABI.
    fn drorb_serve_cfg(input: *mut LeanObject) -> *mut LeanObject;

    /// `@[export drorb_tls_serve] Dataplane.Tls.drorbTlsServe : UInt32 ->
    /// ByteArray^8 -> IO Unit` — run one accepted TCP connection's whole VERIFIED
    /// TLS 1.3 server in-process: the RFC 8446 handshake
    /// (`TlsHandshake.serverStep`, presenting the certificate the proven
    /// `chooseCert` selects from the pool per the client's
    /// `signature_algorithms`), then the established record layer
    /// (`TlsHandshake.appStep`) serving each decrypted request through the SAME
    /// proven `drorb_serve` and sealing the response. `fd` is the connected
    /// socket (unboxed `uint32_t`), consumed and closed by the Lean side. The
    /// certificate material is owned ByteArrays it consumes: the Ed25519 default
    /// (`cert` DER end-entity, `seed` 32-byte RFC 8032 signing seed), then the
    /// optional ECDSA-P256 leaf (`ecdsa_cert` DER, `ecdsa_priv` 32-byte raw
    /// scalar) and RSA-PSS-2048 leaf (`rsa_cert` DER, `rsa_n`/`rsa_e`/`rsa_d`
    /// big-endian modulus / public / private exponent). An EMPTY ByteArray for a
    /// pool member means "absent". Returns the IO result object; crossed only on
    /// the runtime-owner thread, and BLOCKS it for the connection's lifetime (see
    /// `run_tls_conn`).
    fn drorb_tls_serve(
        fd: u32,
        cert: *mut LeanObject,
        seed: *mut LeanObject,
        ecdsa_cert: *mut LeanObject,
        ecdsa_priv: *mut LeanObject,
        rsa_cert: *mut LeanObject,
        rsa_n: *mut LeanObject,
        rsa_e: *mut LeanObject,
        rsa_d: *mut LeanObject,
        world: *mut LeanObject,
    ) -> *mut LeanObject;

    // Byte-marshalling adapter (ffi/drorb_ffi.c) for lean.h's inline sarray API.
    fn drorb_sarray_of_bytes(p: *const u8, n: usize) -> *mut LeanObject;
    fn drorb_sarray_len(o: *mut LeanObject) -> usize;
    fn drorb_sarray_ptr(o: *mut LeanObject) -> *const u8;
    fn drorb_obj_dec(o: *mut LeanObject);
    fn drorb_io_world() -> *mut LeanObject;
    fn drorb_io_ok(o: *mut LeanObject) -> i32;
}

/// Which proven seam a job crosses. All three are exported `ByteArray ->
/// ByteArray` functions with the SAME marshalling; they differ only in which
/// proven pipeline runs on the bytes. Every one is called on the single
/// runtime-owner thread.
#[derive(Clone, Copy, PartialEq)]
pub enum Seam {
    /// `drorb_serve` — the TCP byte-stream fork (HTTP/1.1 + h2c → real H2).
    Http,
    /// `drorb_serve_ws_frame` — the proven WebSocket frame engine (echo).
    WsFrame,
    /// `drorb_serve_datagram` — QUIC-Initial decrypt → proven H3 dispatch.
    Datagram,
    /// `drorb_upgrade_gate` — the deployed `/admin` JWT auth gate on a protocol
    /// upgrade request (401 bytes if refused, empty if authorized).
    UpgradeGate,
    /// `drorb_proxy_pick` — the proven reverse-proxy backend pick
    /// (`Reactor.ProxyDial`): `(mask, key)` bytes in, the chosen backend id (decimal
    /// ASCII) out, or empty when no backend is eligible.
    ProxyPick,
    /// `drorb_lb_pick` - the proven config-policy + load-aware reverse-proxy pick
    /// (`Reactor.LoadBalance`): `pol :: round :: mask :: n :: conns :: key` in, the
    /// chosen backend id (decimal ASCII) out, or empty when no backend is eligible.
    LbPick,
    /// `drorb_serve_step` — the effect/continuation serve STEP (`Reactor.ServeStep`):
    /// `mask :: request` in, the encoded `Step` out.
    ServeStep,
    /// `drorb_serve_resume` — resume the serve after a yielded effect: the framed
    /// `mask :: reqLen :: request :: result` in, the resumed response bytes out.
    ServeResume,
    /// `drorb_serve_proxy_stream_head` — the CL-trust streaming head seam:
    /// `reqLen(4 BE) :: request :: headLen(4 BE) :: upstreamHead :: bodyLen(4 BE)` in,
    /// the non-gzip transformed head out (empty ⇒ gzip, stay buffered).
    ServeProxyStreamHead,
    /// `drorb_serve_step_cfg` — the config-driven serve STEP: `sel :: mask ::
    /// request` in, the encoded `Step` out (config LB policy decides the backend).
    ServeStepCfg,
    /// `drorb_serve_resume_cfg` — resume the config-driven serve: `sel :: mask ::
    /// reqLen :: request :: result` in, the resumed response bytes out.
    ServeResumeCfg,
    /// `drorb_l4_bind` — the layer-4 accept-surface projection: `sel` in, the
    /// config's declared L4 bindings (newline/tab-joined) out.
    L4Bind,
    /// `drorb_deployment_of_config` — parse an arbitrary textual config: the config
    /// UTF-8 bytes in, `lb\t<byte>` + the declared L4 lines out (empty on failure).
    DeploymentOfConfig,
    /// `drorb_serve_step_pol` — the config-policy serve STEP: `pol :: mask ::
    /// request` in, the encoded `Step` out (the config LB byte decides the backend).
    ServeStepPol,
    /// `drorb_serve_resume_pol` — resume the config-policy serve: `pol :: mask ::
    /// reqLen :: request :: result` in, the resumed response bytes out.
    ServeResumePol,
    /// `drorb_serve_cfg` — serve under a config's route table: `cfgLen(4 BE) ::
    /// config :: request` in, the served response bytes out.
    ServeCfg,
    /// `drorb_serve_braided` / (metered) `drorb_serve_metered_braided` — serve over
    /// `braidedDeployment` (the forward-auth gate + request-id echo at the head of the
    /// deployed chain). On the metered path (a job tagged `ServeBraided` + `Some(meter)`)
    /// the raw request crosses `drorb_serve_metered_braided`; `entry` maps the non-metered
    /// variant to `drorb_serve_braided`.
    ServeBraided,
    /// `drorb_serve_stream` — the streaming response-emit seam: `idx(4 BE) ::
    /// chunkSize(4 BE) :: request` in, `flags(1) :: chunk` out (one bounded chunk per
    /// index; empty past the end). The host pulls chunks by index and writes each.
    ServeStream,
    /// `drorb_connect_gate` — the proven CONNECT admission gate: the newline-joined
    /// `target :: allow-patterns` in, a single verdict byte out (`1` tunnel, `0`
    /// refuse).
    ConnectGate,
    /// `drorb_grpc_frame_len` — the gRPC frame-header parse: the 5-byte header in,
    /// the decimal-ASCII payload length out (empty if short).
    GrpcFrameLen,
    /// `drorb_static_resolve` — the proven static-file path decision: the relative
    /// target bytes in, `0x01 ++ resolved` (accept) or `0x00` (reject) out.
    StaticResolve,
    /// `drorb_static_decide` — the proven static RESPONSE decision: the
    /// boundary-fact frame (flags/len/mtime/name + the raw request) in, the encoded
    /// serving plan out (verbatim reply / whole-file head / 206 window / 206
    /// multipart parts).
    StaticDecide,
}

/// Whether the `DRORB_FLAT` A/B switch selects the flat serve on the HTTP path.
/// Read once (env is fixed for the process lifetime); `1`/`true`/`yes`/`on` enable.
fn flat_serve_enabled() -> bool {
    use std::sync::OnceLock;
    static FLAT: OnceLock<bool> = OnceLock::new();
    *FLAT.get_or_init(|| {
        std::env::var("DRORB_FLAT")
            .map(|v| matches!(v.as_str(), "1" | "true" | "yes" | "on"))
            .unwrap_or(false)
    })
}

// The cake--pancake-compiled x64 machine-code /health responder, linked in as a
// runtime-free static library (`ffi/health/libhealthserve.a`: `health.S` from
// `cake --pancake` + the re-entrant driver `health_ffi.c`). It carries its own
// CakeML heap/GC — no `lean_boot`, no `drorb_sarray`, no Lean runtime. Present
// only when that library is linked (build.rs links it when it exists), which is
// the `DRORB_HEALTH_NATIVE` demo build.
#[cfg(drorb_health_native)]
unsafe extern "C" {
    /// `size_t health_serve(const uint8_t* req, size_t req_len, uint8_t* out,
    /// size_t out_cap)` — run the compiled responder once, in-process. Returns
    /// the number of response bytes written into `out` (379 for the exact
    /// `GET /health HTTP/1.1\r\nHost: x\r\n\r\n` request; 0 for anything else, so
    /// the caller falls through to the leanc path). Re-entrant: callable
    /// repeatedly on the single serve-owner thread (the only thread that touches
    /// its statics), exactly like `drorb_serve`.
    fn health_serve(req: *const u8, req_len: usize, out: *mut u8, out_cap: usize) -> usize;
    /// PROVENANCE counter, incremented ONLY inside `cake_ffireport_vec` (the FFI
    /// sink the compiled program calls to emit its response). Nonzero after a
    /// request proves the cake-compiled machine code executed on that request.
    static cake_health_report_count: u64;
}

/// The exact request the compiled /health responder is pinned to. Its golden
/// response embeds the request verbatim (the `x-corr` header echoes every request
/// byte), so the baked-in constant is byte-correct ONLY for this exact request;
/// the native path fires for nothing else (anything else falls through to leanc).
#[cfg(drorb_health_native)]
const HEALTH_EXACT_REQ: &[u8] = b"GET /health HTTP/1.1\r\nHost: x\r\n\r\n";

/// Whether `DRORB_HEALTH_NATIVE` routes the exact `/health` request to the
/// cake-compiled native responder. Default OFF (unset ⇒ nothing changes). Read
/// once; `1`/`true`/`yes`/`on` enable.
#[cfg(drorb_health_native)]
fn health_native_enabled() -> bool {
    use std::sync::OnceLock;
    static NATIVE: OnceLock<bool> = OnceLock::new();
    *NATIVE.get_or_init(|| {
        std::env::var("DRORB_HEALTH_NATIVE")
            .map(|v| matches!(v.as_str(), "1" | "true" | "yes" | "on"))
            .unwrap_or(false)
    })
}

/// Cheap, allocation-free predicate: would `req` be answered by the native path?
/// (native enabled AND the exact pinned request). Lets a caller skip taking a
/// response buffer entirely on the default path — zero per-request overhead when
/// the demo is off.
#[cfg(drorb_health_native)]
#[inline]
pub(crate) fn wants_native_health(req: &[u8]) -> bool {
    health_native_enabled() && req == HEALTH_EXACT_REQ
}

/// Non-demo builds: the native path is absent, so this is a compile-time `false`.
#[cfg(not(drorb_health_native))]
#[inline]
pub(crate) fn wants_native_health(_req: &[u8]) -> bool {
    false
}

/// If native /health is enabled AND `req` is the exact pinned request, answer it
/// from the cake--pancake-compiled x64 machine code (no Lean seam crossing) and
/// return `true`. Otherwise leave `out` untouched and return `false` so the caller
/// runs the normal leanc pipeline. Only ever invoked on the serve-owner thread.
#[cfg(drorb_health_native)]
pub(crate) fn serve_native_into(req: &[u8], out: &mut Vec<u8>) -> bool {
    if !wants_native_health(req) {
        return false;
    }
    // The pooled response buffer needs room for the whole constant response.
    out.clear();
    out.resize(512, 0);
    // SAFETY: `req` is a valid read-only slice; `out` is a live, owned buffer of
    // `out.len()` bytes. `health_serve` copies the response into it and returns
    // the byte count. Single-threaded on the serve owner (its C statics are
    // never touched concurrently), matching the `drorb_serve` discipline.
    let n = unsafe { health_serve(req.as_ptr(), req.len(), out.as_mut_ptr(), out.len()) };
    out.truncate(n);
    if n == 0 {
        return false; // compiled path declined (not the exact request) — fall through
    }
    // PROVENANCE: the compiled machine code ran to completion and reported its
    // bytes on the FFI trace; surface the counter on the demo path.
    // SAFETY: plain read of a C global on the single serve-owner thread.
    let served = unsafe { cake_health_report_count };
    eprintln!(
        "dataplane: /health answered by cake--pancake x64 machine code \
         ({n} bytes, cake_ffireport_vec fired {served} times)"
    );
    true
}

/// Non-demo builds (no `libhealthserve.a` linked): the native path is absent, so
/// this is a compile-time no-op and every request runs the leanc pipeline.
#[cfg(not(drorb_health_native))]
#[inline]
pub(crate) fn serve_native_into(_req: &[u8], _out: &mut Vec<u8>) -> bool {
    false
}

impl Seam {
    /// The exported entry for this seam.
    ///
    /// SAFETY: each is a real `@[export] ByteArray -> ByteArray` symbol in the
    /// drorb archive; the returned pointer is only ever invoked from the
    /// runtime-owner thread by [`serve_into`], with the same marshalling.
    fn entry(self) -> unsafe extern "C" fn(*mut LeanObject) -> *mut LeanObject {
        match self {
            Seam::Http => {
                // A/B seam: `DRORB_FLAT=1` selects the byte-identical flat serve
                // (`drorb_serve_flat`, proven `= drorb_serve`) so the flat vs. List
                // materialization stays measurable; unset selects the DEPLOYED
                // DEFAULT — the index-native-head serve (`drorb_serve_head_idx`,
                // proven `= drorb_serve` for every input by
                // `Dataplane.serveHeadIdx_eq_drorbServe`): parse ONCE off the
                // borrowed window, both dense arms index-decided, no head-List
                // materialization on the deciding path.
                if flat_serve_enabled() {
                    drorb_serve_flat
                } else {
                    drorb_serve_head_idx
                }
            }
            Seam::WsFrame => drorb_serve_ws_frame,
            Seam::Datagram => drorb_serve_datagram,
            Seam::UpgradeGate => drorb_upgrade_gate,
            Seam::ProxyPick => drorb_proxy_pick,
            Seam::LbPick => drorb_lb_pick,
            Seam::ServeStep => drorb_serve_step,
            Seam::ServeResume => drorb_serve_resume,
            Seam::ServeProxyStreamHead => drorb_serve_proxy_stream_head,
            Seam::ServeStepCfg => drorb_serve_step_cfg,
            Seam::ServeResumeCfg => drorb_serve_resume_cfg,
            Seam::L4Bind => drorb_l4_bind,
            Seam::DeploymentOfConfig => drorb_deployment_of_config,
            Seam::ServeStepPol => drorb_serve_step_pol,
            Seam::ServeResumePol => drorb_serve_resume_pol,
            Seam::ServeCfg => drorb_serve_cfg,
            Seam::ServeBraided => drorb_serve_braided,
            Seam::ServeStream => drorb_serve_stream,
            Seam::ConnectGate => drorb_connect_gate,
            Seam::GrpcFrameLen => drorb_grpc_frame_len,
            Seam::StaticResolve => drorb_static_resolve,
            Seam::StaticDecide => drorb_static_decide,
        }
    }
}

/// Bring up the Lean runtime and initialize the proven module. Must run once,
/// before any `drorb_serve` call, on the thread that will own the runtime.
fn lean_boot() {
    // SAFETY: the exact runtime-init sequence leanc emits for a module main:
    // init the runtime, run the module initializer once against a fresh IO
    // world, check it succeeded, drop the result, then mark init end. Called
    // exactly once, on the runtime-owner thread, before any `drorb_serve`.
    unsafe {
        lean_initialize_runtime_module();
        let res = initialize_Dataplane(1, drorb_io_world());
        if drorb_io_ok(res) == 0 {
            panic!("initialize_Dataplane returned an IO error");
        }
        drorb_obj_dec(res);
        lean_io_mark_end_initialization();
    }
}

/// The one and only seam crossing: run the proven pipeline over `req` and
/// append the response bytes into `out` (cleared first). `out` is a pooled
/// buffer, so no response `Vec` is allocated per request on the host side.
/// Only ever invoked from the runtime-owning serve thread.
fn serve_into(req: &[u8], seam: Seam, out: &mut Vec<u8>) {
    // SAFETY: `drorb_sarray_of_bytes` copies `req` into a fresh owned Lean
    // ByteArray (the runtime's per-call input alloc); the seam entry consumes it
    // and returns an owned ByteArray whose bytes we copy out before dropping our
    // reference with `drorb_obj_dec`. Pointers from `drorb_sarray_ptr` are valid
    // for `len` bytes until that dec. All calls are on the single runtime-owner
    // thread.
    unsafe {
        let input = drorb_sarray_of_bytes(req.as_ptr(), req.len());
        let output = (seam.entry())(input); // consumes `input`, returns owned ByteArray
        let len = drorb_sarray_len(output);
        out.clear();
        out.extend_from_slice(slice::from_raw_parts(drorb_sarray_ptr(output), len));
        drorb_obj_dec(output);
    }
}

/// Connection context the metered serve carries alongside the request bytes: the
/// client address the two connection-aware gates decide on, and the per-connection
/// request index the rate bucket depletes against. `Copy` and heap-free, so it
/// rides the serve channel without allocating.
#[derive(Clone, Copy)]
pub struct Meter {
    /// The client IP the IP-filter gate decides on (the accept peer, or the
    /// forwarded client address when the immediate peer is a trusted proxy).
    pub client: IpAddr,
    /// 0-based index of this request within its connection; the rate token bucket
    /// treats it as the standing depletion (`cap - seq` tokens remain).
    pub seq: u64,
}

/// Encode a client address into the attribute-byte shape the proven IP-filter gate
/// decodes (`Reactor.Stage.IpFilter.encodeAddr`): a family tag byte (`4` for IPv4,
/// `6` for IPv6) followed by one `0`/`1` byte per address bit, MSB-first per octet.
/// Writes into `buf` (large enough for the IPv6 case: `1 + 128`) and returns the
/// number of bytes written. No allocation.
fn encode_addr(client: IpAddr, buf: &mut [u8; 129]) -> usize {
    fn push_octets(octets: &[u8], buf: &mut [u8; 129], mut n: usize) -> usize {
        for &octet in octets {
            let mut bit = 7i32;
            while bit >= 0 {
                buf[n] = (octet >> bit) & 1;
                n += 1;
                bit -= 1;
            }
        }
        n
    }
    match client {
        IpAddr::V4(v4) => {
            buf[0] = 4;
            push_octets(&v4.octets(), buf, 1)
        }
        IpAddr::V6(v6) => {
            buf[0] = 6;
            push_octets(&v6.octets(), buf, 1)
        }
    }
}

/// The `DRORB_SPAN` A/B switch for the assembled flat serve (the cons-list-removal
/// measurement gate). Read once (env is fixed for the process lifetime):
/// `1` selects the cons-free flat serve (`drorb_serve_span`, the echo exemplar), `2`
/// its byte-identical `List` twin (`drorb_serve_span_list`), `3` the ASSEMBLED FULL
/// flat serve (`drorb_serve_full` — the REAL deployed 14-stage pipeline rendered flat,
/// byte-identical to the deployed `drorb_serve`), `5` the BODY-DENSE poly serve
/// (`drorb_serve_bodypoly` — the body carried dense as a `ByteArray` through the
/// `servePoly` fold + codec-tag stage), `6` its byte-identical `List` twin
/// (`drorb_serve_bodypoly_list`, the body cons control), anything else keeps the
/// deployed metered serve. Returns `None` on the default path so there is zero
/// per-request overhead when the measurement is off.
/// The parsed `DRORB_SPAN` value, read once (env is fixed for the process lifetime).
/// `None` when unset/unrecognized (the default deployed serve). Shared by
/// [`span_serve_seam`] (which entry function to cross) and [`is_split_span`] (whether
/// the shard splices the body).
fn span_number() -> Option<u8> {
    use std::sync::OnceLock;
    static SPAN: OnceLock<Option<u8>> = OnceLock::new();
    *SPAN.get_or_init(|| match std::env::var("DRORB_SPAN").ok().as_deref() {
        Some("1") => Some(1),
        Some("2") => Some(2),
        Some("3") => Some(3),
        Some("4") => Some(4),
        Some("5") => Some(5),
        Some("6") => Some(6),
        Some("7") => Some(7),
        Some("8") => Some(8),
        Some("9") => Some(9),
        Some("10") => Some(10),
        Some("11") => Some(11),
        Some("12") => Some(12),
        Some("13") => Some(13),
        Some("14") => Some(14),
        Some("15") => Some(15),
        Some("16") => Some(16),
        Some("17") => Some(17),
        Some("18") => Some(18),
        Some("19") => Some(19),
        Some("20") => Some(20),
        Some("21") => Some(21),
        Some("22") => Some(22),
        Some("23") => Some(23),
        Some("24") => Some(24),
        _ => None,
    })
}

/// True when `DRORB_SPAN=15` (the zero-copy-body split seam): the serve thread crosses
/// `drorb_serve_split_head` (head only), and the io_uring shard writes that head THEN the
/// borrowed request body via `writev` — the body is never appended into an output buffer.
/// The shard reads this at the response-staging point to select the split-write path.
pub fn is_split_span() -> bool {
    span_number() == Some(15)
}

/// True when `DRORB_SPAN=23` (the zero-copy STATIC-body split seam): the serve thread
/// crosses `drorb_serve_conformant_zc` (a 1-byte-tagged response); on the fast `/bulk`
/// arm only the HEAD comes back, and the io_uring shard gather-writes that head THEN
/// the process-static constant body — no whole-body copy anywhere on the serve path.
pub fn is_zc_split_span() -> bool {
    span_number() == Some(23)
}

/// The process-static `/bulk` body (`DRORB_SPAN=23`): rendered ONCE at serve-thread
/// boot from the proven constant (`drorb_bulk_body`) into a leaked, process-lifetime
/// buffer; every split response references it by pointer. Empty until initialized.
static BULK_STATIC_BODY: std::sync::OnceLock<&'static [u8]> = std::sync::OnceLock::new();

/// The static body buffer the `=23` split send gathers. Empty slice before
/// `init_static_bulk_body` has run (the serve thread initializes it at boot, before
/// any request crosses the `=23` seam).
pub fn static_bulk_body() -> &'static [u8] {
    BULK_STATIC_BODY.get().copied().unwrap_or(&[])
}

/// Fetch the constant body across the seam ONCE and leak it into the process-static
/// buffer. Runs on the runtime-owner serve thread, after `lean_boot`, before the job
/// loop — the ONE body copy left in the process's lifetime (not per request).
fn init_static_bulk_body() {
    let mut v: Vec<u8> = Vec::new();
    // SAFETY: same marshalling discipline as `serve_into` — an owned input sarray is
    // consumed by the export; the returned owned ByteArray's bytes are copied out
    // (once, at boot) before `drorb_obj_dec`. On the runtime-owner thread.
    unsafe {
        let dummy = [0u8; 1];
        let input = drorb_sarray_of_bytes(dummy.as_ptr(), 0);
        let output = drorb_bulk_body(input);
        let len = drorb_sarray_len(output);
        v.extend_from_slice(slice::from_raw_parts(drorb_sarray_ptr(output), len));
        drorb_obj_dec(output);
    }
    let _ = BULK_STATIC_BODY.set(Box::leak(v.into_boxed_slice()));
}

/// Marshal `req` across the tagged zero-copy split seam (`drorb_serve_conformant_zc`,
/// `DRORB_SPAN=23`) and copy the UNTAGGED payload into `out` (cleared first). Returns
/// `true` when the tag says HEAD-ONLY (`0x01`): `out` is the response head and the
/// caller must arrange the static body to follow; `false` means `out` is the full
/// response (byte-for-byte the `=22` serve). The tag is consumed here, off the copy
/// path (the payload copy starts one byte in — no extra move). Only ever invoked from
/// the runtime-owner serve thread.
fn serve_zc_into(req: &[u8], out: &mut Vec<u8>) -> bool {
    // SAFETY: identical discipline to `serve_into` — the input sarray is consumed by
    // the seam; the returned owned ByteArray's bytes are copied out before
    // `drorb_obj_dec`. All on the single runtime-owner thread.
    unsafe {
        let input = drorb_sarray_of_bytes(req.as_ptr(), req.len());
        let output = drorb_serve_conformant_zc(input);
        let len = drorb_sarray_len(output);
        let ptr = drorb_sarray_ptr(output);
        out.clear();
        let head_only = if len == 0 {
            false
        } else {
            out.extend_from_slice(slice::from_raw_parts(ptr.add(1), len - 1));
            *ptr == 1
        };
        drorb_obj_dec(output);
        head_only
    }
}

fn span_serve_seam() -> Option<unsafe extern "C" fn(*mut LeanObject) -> *mut LeanObject> {
    match span_number() {
        Some(1) => Some(drorb_serve_span),
        Some(2) => Some(drorb_serve_span_list),
        Some(3) => Some(drorb_serve_full),
        // The NON-metered full deployed `List` serve (`drorb_serve`) crossed through
        // the SAME non-metered span seam as `drorb_serve_full` — the clean, byte-
        // identical (`Dataplane.serveFlatFull_eq_drorbServe`) `List`-egress baseline
        // for the assembled full flat serve. `=3` vs `=4` isolates ONLY the flat-egress
        // effect (same 14-stage fold, same routing, same non-metered path); neither
        // rate-limits, so the A/B is apples-to-apples (unlike `=3` vs the metered `=0`).
        Some(4) => Some(drorb_serve),
        // The BODY-DENSE poly serve (`=5`) and its byte-identical `List` twin (`=6`) —
        // the SAME parse ⟶ codec-tag body stage ⟶ serialize, differing ONLY in whether the
        // body is carried dense (`ByteArray`, `=5`) or materialized as a `List UInt8`
        // (`=6`). `=5` vs `=6` isolates the deployed-body win: does carrying the 8 KB body
        // dense through the fold recover the ~3.4×-class body speedup.
        Some(5) => Some(drorb_serve_bodypoly),
        Some(6) => Some(drorb_serve_bodypoly_list),
        // The FULL POLY serve (`drorb_serve_poly` — the deployed 14-stage routed response
        // rendered through the polymorphic `HdrBlock`/`ByteArray` egress fold, byte-identical
        // to the deployed `drorb_serve`). `=7` vs `=4` (deployed `List`) isolates the
        // full-poly egress margin on the deployed-representative serve; both non-metered,
        // same routing, so the A/B is apples-to-apples.
        Some(7) => Some(drorb_serve_poly),
        // The GENUINELY-DENSE multi-stage serve FOLD (`drorb_serve_dense`, `=8`) and its
        // byte-identical `List` twin (`drorb_serve_dense_list`, `=9`) — the SAME parse ⟶
        // 3-stage header-transform fold ⟶ egress, differing ONLY in whether the header
        // block + body are carried dense (`HdrBlock`/`ByteArray`, `=8`) or materialized as
        // `List` (`=9`). `=8` vs `=9` isolates the dense-FOLD win on a large body: does
        // running the response-transform fold dense (not just the egress) recover the body
        // speedup the finale's List-fold-poly-egress (`=7`) could not.
        Some(8) => Some(drorb_serve_dense),
        Some(9) => Some(drorb_serve_dense_list),
        // The DENSE serve that RUNS THE DEPLOYED BODY TRANSFORM DENSE
        // (`drorb_serve_densefull`, `=10`) and its byte-identical `List` twin
        // (`drorb_serve_densefull_list`, `=11`) — the SAME parse ⟶ 3-stage header
        // fold ⟶ deployed html-rewrite body transform ⟶ egress, differing ONLY in
        // whether the body is run through the transform dense (`ByteArray`,
        // index-native `rewriteBytesDense`, `=10`) or consed (`List UInt8`, the
        // deployed `rewriteBytes input.data.toList`, `=11`). `=10` vs `=11` isolates
        // the deployed-body-transform representation cost on a LARGE HTML body: does
        // running the whole-body html-rewrite loop dense recover the body speedup.
        Some(10) => Some(drorb_serve_densefull),
        Some(11) => Some(drorb_serve_densefull_list),
        // The FULLY-DENSE-TOKENIZER serve (`drorb_serve_densefull2`, `=12`) — the SAME
        // parse ⟶ 3-stage header fold ⟶ deployed html-rewrite body transform ⟶ egress
        // as `=10`, but the tokenizer STATE is fully dense (`rewriteBytesDense2`,
        // `FStateD` over `ByteArray`/`Array`, NO per-byte token `cons`). Byte-identical
        // to the `List` twin `=11` (`serveDenseFull2_refines`). `=12` vs `=11` is the
        // full body-transform ratio (compare to `=10` vs `=11` = the ~2.35× the token
        // `List` capped); `=12` vs `=10` isolates the killed token-`List` increment.
        Some(12) => Some(drorb_serve_densefull2),
        // The CONTENT-TYPE-GATED serve (`drorb_serve_gated`, `=13`) and its byte-identical
        // `List` twin (`drorb_serve_gated_list`, `=14`) — the SAME parse ⟶ 3-stage header
        // fold ⟶ egress as `=10`/`=11`, but the body is GATED on the response `Content-Type`:
        // on `text/html` the dense deployed rewrite (same as `=10`), on ANYTHING ELSE the
        // body is a ZERO-COPY passthrough (borrowed `ByteArray` straight to egress, never
        // tokenized). `=13` vs `=11`/`=10` on a NON-HTML large body isolates the common-case
        // reshape win: the tokenize-everything ceiling (~2.35×) vanishes because the body
        // never enters the tokenizer. Drive with `-T application/octet-stream` (gate off,
        // passthrough) vs `-T text/html` (gate fires). `=13` vs `=14` isolates the dense-vs-
        // `List` cost on the gated path.
        Some(13) => Some(drorb_serve_gated),
        Some(14) => Some(drorb_serve_gated_list),
        // The ZERO-COPY-BODY split serve (`drorb_serve_split_head`, `=15`) — the serve
        // thread computes ONLY the response HEAD (no body append); the io_uring shard
        // writes head THEN the borrowed request body via `writev` (`stage_response` +
        // `is_split_span`). `=15` vs `=13` (gated, body appended once) on a LARGE body
        // isolates the body-append cost: the split never allocates/appends the body into
        // an output ByteArray, so it beats the append by one whole-body copy.
        Some(15) => Some(drorb_serve_split_head),
        // The COMBINED fast serve exemplar (`drorb_serve_ultra`, `=16`) and its byte-
        // identical `List` twin (`drorb_serve_ultra_list`, `=17`) — ALL the datapath wins
        // in ONE serve: parse index-native ⟶ 3-stage dense header fold ⟶ content-type-
        // GATED body (non-HTML = ZERO-COPY passthrough, `text/html` = the FULLY-DENSE
        // tokenizer `rewriteBytesDense2`, no token `List`) ⟶ flat egress. Same shape as
        // the gated serve `=13` but the HTML branch runs the fully-dense tokenizer (`=12`).
        // Proven byte-identical to its `List` twin (`=17`, `serveUltra_refines`) and to the
        // deployed gated serve `=13` (`serveUltra_eq_serveGated`). Drive with `-T
        // application/octet-stream` (gate off, passthrough) vs `-T text/html` (gate fires,
        // fully-dense tokenizer). `=16` vs the deployed `List` serve `=4` on a large body
        // is the headline combined win; `=16` vs `=17` isolates the dense-vs-`List` cost.
        Some(16) => Some(drorb_serve_ultra),
        Some(17) => Some(drorb_serve_ultra_list),
        // The RUNTIME-DENSE full serve (`drorb_serve_dense_real`, `=18`) — the deployed
        // `/bulk` body-cliff fix: on a plain `GET /bulk` it emits the DENSE head + DENSE
        // 1 MiB `Array` body (no per-byte `List` cons), byte-identical to the deployed serve
        // (`Dataplane.serveDenseReal_eq_drorbServe`); off the `/bulk` arm it is the deployed
        // List serve. `=18` vs the deployed List serve `=4` on `GET /bulk` isolates the
        // body-cliff: the deployed List serve materialises the 1 MiB response body as a
        // `List UInt8` (the ~51 MiB/s cliff), the dense serve never does.
        Some(18) => Some(drorb_serve_dense_real),
        // The RFC 7230/7231 CONFORMANCE serve (`drorb_serve_conformant`, `=19`) — the
        // deployed `drorbServe` wrapped by the proven conformance stages (request-line /
        // Host validation gate ⟶ unchanged inner serve ⟶ Date + HEAD-strip finisher).
        // Every HTTP serve job funnels through it, so the RFC probe
        // (`conformance/rfc_conformance.py`) sees the conformant behaviour on all seven
        // previously-failing checks (B1/B2/C1/C2/C3/F1/G1). `=19` vs `=4` (bare deployed
        // serve) is the conformance-wrapper delta.
        Some(19) => Some(drorb_serve_conformant),
        // The CONFORMANT-DENSE serve (`drorb_serve_conformant_dense`, `=20`) — the same
        // conformance wrapper as `=19`, inner swapped for the index-decided dense serve
        // (byte-identical, proven). `=20` vs `=19` on `GET /bulk` isolates the 1 MiB
        // List body-cliff + the List arm-decision under identical wrapper semantics.
        Some(20) => Some(drorb_serve_conformant_dense),
        // The BARE index-decided dense serve (`=21`) — `=21` vs `=18` isolates the
        // index-native arm decision + dense head scalars.
        Some(21) => Some(drorb_serve_dense_idx),
        // The FUSED-POSTPROCESS conformant-dense serve (`drorb_serve_conformant_fast`,
        // `=22`) — the same conformance wrapper + dense inner as `=20`, but the
        // `Date`-splice + `x-corr`-scrub rebuild only the head and attach the unchanged
        // body with ONE `copySlice` (single whole-body memcpy instead of ~4). `=22` vs
        // `=20` on `GET /bulk` isolates the wrapper's body-recopy cost.
        Some(22) => Some(drorb_serve_conformant_fast),
        // The BARE index-native-head serve (`drorb_serve_head_idx`, `=24`) — the
        // deployed `Seam::Http` default, surfaced as a span so it stays A/B-able:
        // `=24` vs `=21` isolates the parse-once head read (one `parseArr`, arms
        // decided on the arena head) vs the double-parse index-decided serve;
        // `=24` vs `=4` (deployed List serve) is the whole index-native win.
        Some(24) => Some(drorb_serve_head_idx),
        _ => None,
    }
}

/// Marshal `req` across a single-argument `ByteArray -> ByteArray` seam `entry` and
/// copy the response into `out` (cleared first) — the exact discipline of
/// [`serve_into`], but for a directly-supplied entry function (the `DRORB_SPAN` seam).
/// Only ever invoked from the runtime-owner serve thread.
fn serve_into_via(
    req: &[u8],
    entry: unsafe extern "C" fn(*mut LeanObject) -> *mut LeanObject,
    out: &mut Vec<u8>,
) {
    // SAFETY: identical discipline to `serve_into` — `drorb_sarray_of_bytes` copies
    // `req` into a fresh owned Lean ByteArray the seam consumes; the returned owned
    // ByteArray's bytes are copied out before `drorb_obj_dec`. All on the single
    // runtime-owner thread.
    unsafe {
        let input = drorb_sarray_of_bytes(req.as_ptr(), req.len());
        let output = entry(input);
        let len = drorb_sarray_len(output);
        out.clear();
        out.extend_from_slice(slice::from_raw_parts(drorb_sarray_ptr(output), len));
        drorb_obj_dec(output);
    }
}

/// The metered seam crossing: run the proven HTTP/1.1 fold over `req` with the
/// connection context `meter` in scope, so the real IP-filter and rate gates fire
/// on a genuine client address and per-connection sequence. Appends the response
/// bytes into `out` (cleared first). Only ever invoked from the runtime-owner
/// serve thread.
fn serve_metered_into(req: &[u8], meter: Meter, out: &mut Vec<u8>) {
    let mut peer_buf = [0u8; 129];
    let peer_len = encode_addr(meter.client, &mut peer_buf);
    // SAFETY: identical discipline to `serve_into` — both ByteArray arguments are
    // freshly allocated owned sarrays consumed by `drorb_serve_metered`; the
    // returned owned ByteArray's bytes are copied out before the `drorb_obj_dec`.
    // `seq` crosses as an unboxed `uint64_t`. All on the single runtime-owner
    // thread.
    unsafe {
        let peer = drorb_sarray_of_bytes(peer_buf.as_ptr(), peer_len);
        let input = drorb_sarray_of_bytes(req.as_ptr(), req.len());
        let output = drorb_serve_metered(peer, meter.seq, input);
        let len = drorb_sarray_len(output);
        out.clear();
        out.extend_from_slice(slice::from_raw_parts(drorb_sarray_ptr(output), len));
        drorb_obj_dec(output);
    }
}

/// The Braid-0 metered CONFIG seam crossing: run the proven metered fold over the
/// cfg-FRAMED request `req` (`cfgLen(4 BE) :: config :: request`) with the connection
/// context `meter` in scope, so the IP-filter and rate gates decide over the config's
/// deployment. With an empty/routeless config the served bytes are byte-identical to
/// `serve_metered_into` (`servePipelineOfMetered defaultDeployment` = the literal).
/// Appends the response into `out` (cleared first). Only ever invoked from the
/// runtime-owner serve thread.
fn serve_metered_cfg_into(req: &[u8], meter: Meter, out: &mut Vec<u8>) {
    let mut peer_buf = [0u8; 129];
    let peer_len = encode_addr(meter.client, &mut peer_buf);
    // SAFETY: identical discipline to `serve_metered_into` — both ByteArray arguments
    // are freshly allocated owned sarrays consumed by `drorb_serve_metered_cfg`; the
    // returned owned ByteArray's bytes are copied out before the `drorb_obj_dec`.
    // `seq` crosses as an unboxed `uint64_t`. All on the single runtime-owner thread.
    unsafe {
        let peer = drorb_sarray_of_bytes(peer_buf.as_ptr(), peer_len);
        let input = drorb_sarray_of_bytes(req.as_ptr(), req.len());
        let output = drorb_serve_metered_cfg(peer, meter.seq, input);
        let len = drorb_sarray_len(output);
        out.clear();
        out.extend_from_slice(slice::from_raw_parts(drorb_sarray_ptr(output), len));
        drorb_obj_dec(output);
    }
}

/// The metered BRAIDED seam crossing: run the proven metered fold over `req` (the RAW
/// HTTP/1.1 request — NOT cfg-framed) through `drorb_serve_metered_braided`, i.e. over
/// `Reactor.Deploy.braidedDeployment` — the connection-aware gate chain WITH the proven
/// forward-auth gate + request-id echo at the head. With no braid markers the served
/// bytes are byte-identical to `serve_metered_into`
/// (`servePipelineOfMetered_braided_off_eq`). Appends the response into `out` (cleared
/// first). Only ever invoked from the runtime-owner serve thread.
fn serve_metered_braided_into(req: &[u8], meter: Meter, out: &mut Vec<u8>) {
    let mut peer_buf = [0u8; 129];
    let peer_len = encode_addr(meter.client, &mut peer_buf);
    // SAFETY: identical discipline to `serve_metered_into` — both ByteArray arguments
    // are freshly allocated owned sarrays consumed by `drorb_serve_metered_braided`; the
    // returned owned ByteArray's bytes are copied out before the `drorb_obj_dec`. `seq`
    // crosses as an unboxed `uint64_t`. All on the single runtime-owner thread.
    unsafe {
        let peer = drorb_sarray_of_bytes(peer_buf.as_ptr(), peer_len);
        let input = drorb_sarray_of_bytes(req.as_ptr(), req.len());
        let output = drorb_serve_metered_braided(peer, meter.seq, input);
        let len = drorb_sarray_len(output);
        out.clear();
        out.extend_from_slice(slice::from_raw_parts(drorb_sarray_ptr(output), len));
        drorb_obj_dec(output);
    }
}

/// The DEPLOYED-DEFAULT metered seam crossing (RFC-conformant). Identical to
/// [`serve_metered_into`] but crosses `drorb_serve_metered_conformant` — the proven
/// `conformantServe` wrapper around the SAME `drorbServeMetered peer seq` fold: request
/// validation runs first, then the metered IP-filter/rate gates on the accepted request,
/// then the `Date`/`HEAD`-strip finisher. The gates are NOT bypassed — they compose with
/// the RFC edges. Only ever invoked from the runtime-owner serve thread. Retained proven
/// seam: the deployed default now crosses the byte-identical DENSE twin
/// ([`serve_metered_dense_conformant_into`]); this non-dense entry stays for a caller that
/// wants the plain (List body-cliff) metered-conformant fold.
#[allow(dead_code)]
fn serve_metered_conformant_into(req: &[u8], meter: Meter, out: &mut Vec<u8>) {
    let mut peer_buf = [0u8; 129];
    let peer_len = encode_addr(meter.client, &mut peer_buf);
    // SAFETY: identical discipline to `serve_metered_into` — both ByteArray arguments are
    // freshly allocated owned sarrays consumed by `drorb_serve_metered_conformant`; the
    // returned owned ByteArray's bytes are copied out before the `drorb_obj_dec`. `seq`
    // crosses as an unboxed `uint64_t`. All on the single runtime-owner thread.
    unsafe {
        let peer = drorb_sarray_of_bytes(peer_buf.as_ptr(), peer_len);
        let input = drorb_sarray_of_bytes(req.as_ptr(), req.len());
        let output = drorb_serve_metered_conformant(peer, meter.seq, input);
        let len = drorb_sarray_len(output);
        out.clear();
        out.extend_from_slice(slice::from_raw_parts(drorb_sarray_ptr(output), len));
        drorb_obj_dec(output);
    }
}

/// THE DEPLOYED-DEFAULT metered seam crossing (RFC-conformant, DENSE): the ONE
/// consolidated metered default. Crosses `drorb_serve_pipeline_conformant` — the
/// proven `conformantServe` wrapper over the single flat 43-stage pipeline
/// (`Reactor.DeployPipeline`, definitionally the deployed onion), `/bulk` emitted
/// DENSE (fully-stamped head + dense 1 MiB body, no per-byte `List` cons). Proven
/// byte-identical to the pre-consolidation default for EVERY (peer, seq, input)
/// (`serveMeteredPipelineConformant_eq_predecessor` / `_eq_deployed`). Both metered
/// default entries funnel here (the direct arm and the empty-config cfg divert), so
/// this one crossing covers them. `req` is the RAW HTTP/1.1 request (NOT cfg-framed).
/// Only ever invoked from the runtime-owner serve thread.
fn serve_metered_dense_conformant_into(req: &[u8], meter: Meter, out: &mut Vec<u8>) {
    let mut peer_buf = [0u8; 129];
    let peer_len = encode_addr(meter.client, &mut peer_buf);
    // SAFETY: identical discipline to `serve_metered_into` — both ByteArray arguments
    // are freshly allocated owned sarrays consumed by `drorb_serve_pipeline_conformant`;
    // the returned owned ByteArray's bytes are copied out before the `drorb_obj_dec`.
    // `seq` crosses as an unboxed `uint64_t`. All on the single runtime-owner thread.
    unsafe {
        let peer = drorb_sarray_of_bytes(peer_buf.as_ptr(), peer_len);
        let input = drorb_sarray_of_bytes(req.as_ptr(), req.len());
        let output = drorb_serve_pipeline_conformant(peer, meter.seq, input);
        let len = drorb_sarray_len(output);
        out.clear();
        out.extend_from_slice(slice::from_raw_parts(drorb_sarray_ptr(output), len));
        drorb_obj_dec(output);
    }
}

/// The DEPLOYED-DEFAULT config-driven metered seam crossing (RFC-conformant). Identical
/// to [`serve_metered_cfg_into`] but crosses `drorb_serve_metered_cfg_conformant` — the
/// `conformantServe` wrapper that validates the UNFRAMED request, then routes through the
/// SAME cfg-framed `drorbServeMeteredCfg peer seq` fold (config route table + metered
/// gates untouched), then applies the `Date`/`HEAD`-strip finisher. `req` is the cfg-FRAMED
/// `cfgLen(4 BE) :: config :: request`. Only ever invoked from the runtime-owner thread.
fn serve_metered_cfg_conformant_into(req: &[u8], meter: Meter, out: &mut Vec<u8>) {
    // DEPLOYED DEFAULT (no `DRORB_CONFIG`): the config frame is EMPTY (`cfgLen = 0`), so the
    // cfg-conformant fold is byte-identical to the plain metered-conformant serve
    // (`drorbServeMeteredCfg` empty-cfg = `servePipelineFull2Metered`,
    // `servePipelineOfMetered_default`). Route that common default to the DENSE
    // metered-conformant serve instead: byte-identical (`meteredDenseConformant_eq_meteredConformant`
    // ∘ `drorbServeMeteredDense_eq`) but dense on the `/bulk` body-cliff arm. Only the
    // empty-config default is diverted; a non-empty `DRORB_CONFIG` keeps the cfg route table.
    if req.len() >= 4 && req[0] == 0 && req[1] == 0 && req[2] == 0 && req[3] == 0 {
        // `cfgLen == 0`: the request bytes follow the 4-byte length prefix (no config body).
        serve_metered_dense_conformant_into(&req[4..], meter, out);
        return;
    }
    let mut peer_buf = [0u8; 129];
    let peer_len = encode_addr(meter.client, &mut peer_buf);
    // SAFETY: identical discipline to `serve_metered_cfg_into` — both ByteArray arguments
    // are freshly allocated owned sarrays consumed by `drorb_serve_metered_cfg_conformant`;
    // the returned owned ByteArray's bytes are copied out before the `drorb_obj_dec`.
    unsafe {
        let peer = drorb_sarray_of_bytes(peer_buf.as_ptr(), peer_len);
        let input = drorb_sarray_of_bytes(req.as_ptr(), req.len());
        let output = drorb_serve_metered_cfg_conformant(peer, meter.seq, input);
        let len = drorb_sarray_len(output);
        out.clear();
        out.extend_from_slice(slice::from_raw_parts(drorb_sarray_ptr(output), len));
        drorb_obj_dec(output);
    }
}

/// The metered BRAIDED seam crossing (RFC-conformant). Identical to
/// [`serve_metered_braided_into`] but crosses `drorb_serve_metered_braided_conformant`,
/// so an opt-in braided deployment is ALSO RFC-conformant (validation → the braided
/// metered fold → `Date`/`HEAD`-strip). Only ever invoked from the runtime-owner thread.
fn serve_metered_braided_conformant_into(req: &[u8], meter: Meter, out: &mut Vec<u8>) {
    let mut peer_buf = [0u8; 129];
    let peer_len = encode_addr(meter.client, &mut peer_buf);
    // SAFETY: identical discipline to `serve_metered_braided_into` — both ByteArray
    // arguments are freshly allocated owned sarrays consumed by
    // `drorb_serve_metered_braided_conformant`; the returned owned ByteArray's bytes are
    // copied out before the `drorb_obj_dec`.
    unsafe {
        let peer = drorb_sarray_of_bytes(peer_buf.as_ptr(), peer_len);
        let input = drorb_sarray_of_bytes(req.as_ptr(), req.len());
        let output = drorb_serve_metered_braided_conformant(peer, meter.seq, input);
        let len = drorb_sarray_len(output);
        out.clear();
        out.extend_from_slice(slice::from_raw_parts(drorb_sarray_ptr(output), len));
        drorb_obj_dec(output);
    }
}

/// One accepted TLS connection to terminate in-process: the raw connected
/// socket fd (the Lean side owns and closes it) plus the certificate pool the
/// verified handshake selects from and presents. The pool (`crate::tls::TlsCert`)
/// is shared (loaded once at boot), so a connection carries only a pointer.
pub struct TlsConn {
    pub fd: std::os::fd::RawFd,
    pub cert: Arc<crate::tls::TlsCert>,
}

/// Run one whole TLS connection over the verified TLS 1.3 server
/// (`drorb_tls_serve`). Only ever invoked from the runtime-owner serve thread;
/// it BLOCKS that thread for the connection's lifetime (handshake + record-layer
/// serve + close), since the compiled proven core is single-owner and the seam
/// does its own blocking socket I/O. A short per-record recv timeout (Lean side)
/// bounds how long a stalled peer can hold the thread. This head-of-line cost is
/// the honest first-cut trade; the follow-on is a per-record crossing that keeps
/// the socket I/O off the serve thread.
fn run_tls_conn(tls: &TlsConn) {
    // SAFETY: each pool member is copied into a fresh owned Lean ByteArray that
    // `drorb_tls_serve` consumes (an EMPTY vec yields an empty ByteArray = "this
    // pool member is absent"); `fd` crosses as an unboxed `uint32_t`; the returned
    // IO-result object is dropped with `drorb_obj_dec`. All on the single
    // runtime-owner thread. The Lean side closes `fd`.
    let p = &tls.cert;
    unsafe {
        let ba = |v: &[u8]| drorb_sarray_of_bytes(v.as_ptr(), v.len());
        let cert = ba(&p.cert_der);
        let seed = ba(&p.seed);
        let ecdsa_cert = ba(&p.ecdsa_cert);
        let ecdsa_priv = ba(&p.ecdsa_priv);
        let rsa_cert = ba(&p.rsa_cert);
        let rsa_n = ba(&p.rsa_n);
        let rsa_e = ba(&p.rsa_e);
        let rsa_d = ba(&p.rsa_d);
        let world = drorb_io_world();
        let res = drorb_tls_serve(
            tls.fd as u32,
            cert,
            seed,
            ecdsa_cert,
            ecdsa_priv,
            rsa_cert,
            rsa_n,
            rsa_e,
            rsa_d,
            world,
        );
        drorb_obj_dec(res);
    }
}

/// How a finished response is delivered back to the IO path that requested it.
pub enum ServeReply {
    /// Blocking thread-per-connection path: the worker blocks on this channel.
    Sync(Sender<PooledBuf>),
    /// io_uring path: the completed response is posted to the requesting
    /// shard's mailbox and the shard is woken through its eventfd.
    #[cfg(target_os = "linux")]
    Shard(Sender<ShardDone>, std::os::fd::RawFd, u32),
    /// kqueue reactor path (macOS/BSD): the completed response is posted to the
    /// requesting reactor's mailbox and the reactor is woken through its
    /// self-pipe (the second field is the pipe write end, the third the slot).
    #[cfg(any(
        target_os = "macos",
        target_os = "ios",
        target_os = "freebsd",
        target_os = "netbsd",
        target_os = "openbsd",
        target_os = "dragonfly"
    ))]
    Reactor(Sender<KqDone>, std::os::fd::RawFd, u32),
}

/// A response delivered to an io_uring shard: which connection it belongs to
/// and the pooled response bytes to write.
#[cfg(target_os = "linux")]
pub struct ShardDone {
    pub conn: u32,
    pub resp: PooledBuf,
    /// ZERO-COPY STATIC BODY (`DRORB_SPAN=23`): `resp` is the response HEAD only;
    /// the shard gather-writes it followed by the process-static constant body
    /// (`crate::serve::static_bulk_body`) — the body is never copied per request.
    pub split_static: bool,
}

/// A response delivered to a kqueue reactor: which connection it belongs to and
/// the pooled response bytes to write. The kqueue analogue of [`ShardDone`].
#[cfg(any(
    target_os = "macos",
    target_os = "ios",
    target_os = "freebsd",
    target_os = "netbsd",
    target_os = "openbsd",
    target_os = "dragonfly"
))]
pub struct KqDone {
    pub conn: u32,
    pub resp: PooledBuf,
}

/// A borrowed request view handed across the serve seam by the zero-copy io_uring
/// receive path: a raw pointer + length into a leased provided-buffer-ring slot.
/// The shard keeps the slot *leased* (does not recycle it) until the response
/// returns, so the pointed-to bytes stay valid for the whole serve crossing.
/// Read-only; the serve thread copies them once into the runtime's input
/// `ByteArray` at the FFI boundary (the intrinsic owned-ABI copy that can never
/// leave the shell) and never retains the pointer. Realizes the borrowed request
/// span of `Datapath/Span.lean` (`SpanBytes`): the request is named by an
/// `(off, len)` window over a shared buffer, not copied to be named.
#[cfg(target_os = "linux")]
pub struct BorrowedReq {
    ptr: *const u8,
    len: usize,
}

#[cfg(target_os = "linux")]
impl BorrowedReq {
    /// Wrap a leased-slot view as a borrowed request.
    ///
    /// # Safety
    ///
    /// `ptr` must be valid for reads of `len` bytes and remain valid until the
    /// io_uring shard recycles the leased slot — which happens only after this
    /// request's response returns, long after the serve thread has read the bytes.
    /// The serve thread must not retain the slice beyond one serve crossing.
    pub unsafe fn new(ptr: *const u8, len: usize) -> Self {
        BorrowedReq { ptr, len }
    }

    fn bytes(&self) -> &[u8] {
        // SAFETY: the constructor contract guarantees `ptr`/`len` name a valid
        // leased slot for the duration of this serve crossing.
        unsafe { slice::from_raw_parts(self.ptr, self.len) }
    }
}

// SAFETY: the pointer is only dereferenced on the serve thread; the io_uring
// shard guarantees the pointed-to leased slot outlives the serve crossing (the
// lease is recycled only after the response returns).
#[cfg(target_os = "linux")]
unsafe impl Send for BorrowedReq {}

/// The request bytes for one serve job: either an owned pooled buffer (the default
/// path and every non-zero-copy caller) or a borrowed view into a leased io_uring
/// provided-buffer slot (the zero-copy receive path). The serve seam reads either
/// through `bytes()`, so the crossing is byte-identical whichever representation
/// carries the request.
pub enum ReqBuf {
    /// An owned pooled request buffer (returned to the pool when the job drops).
    Pooled(PooledBuf),
    /// A borrowed view into a leased provided-buffer slot (no owned copy).
    #[cfg(target_os = "linux")]
    Borrowed(BorrowedReq),
}

impl ReqBuf {
    /// The request bytes, whichever representation carries them.
    fn bytes(&self) -> &[u8] {
        match self {
            ReqBuf::Pooled(b) => b,
            #[cfg(target_os = "linux")]
            ReqBuf::Borrowed(b) => b.bytes(),
        }
    }
}

/// A unit of work for the serve thread: request bytes, which proven seam to
/// cross, and where to deliver the response.
pub struct ServeJob {
    pub req: ReqBuf,
    pub seam: Seam,
    pub reply: ServeReply,
    /// When present (only on the `Seam::Http` byte-stream path), the connection
    /// context the metered serve reads: the request crosses `drorb_serve_metered`
    /// instead of `drorb_serve`, so the IP-filter and rate gates fire. `None`
    /// keeps the original non-metered `drorb_serve` behavior (h2c, WS, datagram,
    /// or any caller without a peer/sequence, e.g. the stdin orb).
    pub meter: Option<Meter>,
    /// When present, this job is NOT a byte-stream serve: the owner thread runs
    /// the verified TLS 1.3 server over `tls.fd` (`drorb_tls_serve`) instead, and
    /// signals completion on `reply`. `req`/`seam`/`meter` are unused.
    pub tls: Option<TlsConn>,
}

/// A cloneable handle the IO paths use to reach the serve thread.
#[derive(Clone)]
pub struct ServeGateway {
    tx: Sender<ServeJob>,
    pool: Arc<BufferPool>,
}

impl ServeGateway {
    /// The shared buffer pool. IO paths draw request/receive buffers from the
    /// same pool the serve thread draws response buffers from, so buffers
    /// recycle across the whole hot path.
    pub fn pool(&self) -> &Arc<BufferPool> {
        &self.pool
    }

    /// Submit one request across `seam` to the proven core. The response is
    /// delivered per `reply`. Returns `false` only if the serve thread is gone.
    pub fn submit(&self, req: PooledBuf, seam: Seam, reply: ServeReply) -> bool {
        self.tx
            .send(ServeJob {
                req: ReqBuf::Pooled(req),
                seam,
                reply,
                meter: None,
                tls: None,
            })
            .is_ok()
    }

    /// Submit one borrowed HTTP/1.1 request (the zero-copy io_uring receive path)
    /// across the byte-stream seam. Same delivery as [`submit`], but the request
    /// bytes are a borrowed view into a leased provided-buffer slot rather than an
    /// owned pooled buffer — no per-request request copy on the host side (copy #1
    /// removed). The serve crossing is byte-identical (`serve_into` reads the same
    /// bytes). Returns `false` only if the serve thread is gone. Retained
    /// non-metered zero-copy seam; the io_uring reactor now submits its borrowed
    /// requests through the metered [`submit_borrowed_metered`] /
    /// [`submit_borrowed_metered_braided`] so the connection gates fire.
    #[cfg(target_os = "linux")]
    #[allow(dead_code)]
    pub fn submit_borrowed(&self, req: BorrowedReq, reply: ServeReply) -> bool {
        self.tx
            .send(ServeJob {
                req: ReqBuf::Borrowed(req),
                seam: Seam::Http,
                reply,
                meter: None,
                tls: None,
            })
            .is_ok()
    }

    /// Submit one HTTP/1.1 request across the DIRECT metered seam: same delivery as
    /// [`submit`], but the request crosses `drorb_serve_metered` with `meter` in
    /// scope so the proven IP-filter and rate gates decide on the real client
    /// address and per-connection sequence. Returns `false` only if the serve
    /// thread is gone. Retained proven seam: since Braid 0 the default connection
    /// path serves through the config-driven [`submit_metered_cfg`] (which defaults
    /// to `defaultDeployment`, byte-identical); this direct entry stays for a caller
    /// with a peer/sequence but no deployment config to thread.
    #[allow(dead_code)]
    pub fn submit_metered(&self, req: PooledBuf, meter: Meter, reply: ServeReply) -> bool {
        self.tx
            .send(ServeJob {
                req: ReqBuf::Pooled(req),
                seam: Seam::Http,
                reply,
                meter: Some(meter),
                tls: None,
            })
            .is_ok()
    }

    /// Submit one HTTP/1.1 request across the Braid-0 metered CONFIG seam: `req` is
    /// cfg-FRAMED (`cfgLen(4 BE) :: config :: request`) and crosses
    /// `drorb_serve_metered_cfg` with `meter` in scope. Same delivery as
    /// [`submit_metered`], but the served fold flows through the operator's deployment
    /// config (or `defaultDeployment` for an empty/routeless config). Carried by
    /// tagging the job with `Seam::ServeCfg` + `Some(meter)`. Returns `false` only if
    /// the serve thread is gone.
    pub fn submit_metered_cfg(&self, req: PooledBuf, meter: Meter, reply: ServeReply) -> bool {
        self.tx
            .send(ServeJob {
                req: ReqBuf::Pooled(req),
                seam: Seam::ServeCfg,
                reply,
                meter: Some(meter),
                tls: None,
            })
            .is_ok()
    }

    /// Submit one HTTP/1.1 request across the metered BRAIDED seam: the RAW request
    /// crosses `drorb_serve_metered_braided` with `meter` in scope, so the metered gate
    /// chain over `braidedDeployment` (forward-auth gate + request-id echo at the head)
    /// decides. Carried by tagging the job with `Seam::ServeBraided` + `Some(meter)`.
    /// Returns `false` only if the serve thread is gone.
    pub fn submit_metered_braided(&self, req: PooledBuf, meter: Meter, reply: ServeReply) -> bool {
        self.tx
            .send(ServeJob {
                req: ReqBuf::Pooled(req),
                seam: Seam::ServeBraided,
                reply,
                meter: Some(meter),
                tls: None,
            })
            .is_ok()
    }

    /// Async metered CONFIG submit from RAW request bytes (the io_uring reactor
    /// path, which never blocks on a reply): frame `cfgLen(4 BE) :: config ::
    /// request` into a fresh pooled buffer and submit it across the Braid-0 metered
    /// cfg seam with `meter` in scope, delivering the response per `reply`. The async
    /// analogue of [`call_metered_cfg`]: same framing, same proven seam
    /// (`drorb_serve_metered_cfg`), no blocking recv. An EMPTY `config` frames
    /// `cfgLen = 0`, byte-identical to the direct `drorb_serve_metered`
    /// (`servePipelineOfMetered_default`). Returns `false` only if the serve thread
    /// is gone.
    pub fn submit_metered_cfg_bytes(
        &self,
        config: &[u8],
        req: &[u8],
        meter: Meter,
        reply: ServeReply,
    ) -> bool {
        let mut framed = self.pool.take();
        framed.clear();
        framed.extend_from_slice(&(config.len() as u32).to_be_bytes());
        framed.extend_from_slice(config);
        framed.extend_from_slice(req);
        self.submit_metered_cfg(framed, meter, reply)
    }

    /// Async metered BRAIDED submit from RAW request bytes (the io_uring reactor
    /// path): copy `req` into a fresh pooled buffer and submit it across the metered
    /// braided seam (`drorb_serve_metered_braided`, RAW — not cfg-framed) with
    /// `meter` in scope, delivering the response per `reply`. The async analogue of
    /// [`call_metered_braided`]. Returns `false` only if the serve thread is gone.
    pub fn submit_metered_braided_bytes(
        &self,
        req: &[u8],
        meter: Meter,
        reply: ServeReply,
    ) -> bool {
        let mut buf = self.pool.take();
        buf.clear();
        buf.extend_from_slice(req);
        self.submit_metered_braided(buf, meter, reply)
    }

    /// Async effect-seam STEP submit (the io_uring reactor path): frame
    /// `[prefix ::] mask :: request` into a fresh pooled buffer and submit it across
    /// the effect STEP seam (`drorb_serve_step` / `_cfg` / `_pol`, per `seam`) with
    /// NO `meter` (the metered gates run on the metered path; the effect seam decides
    /// proxy/cache), delivering the encoded `Step` per `reply`. The async analogue of
    /// the first `call_seam` in [`crate::interp::run_effect_serve`]: identical framing
    /// (`crate::interp::frame_step`), identical proven seam, no blocking recv. The
    /// reply is the encoded `Step`, decoded by the shard in `uring::on_wakeup`.
    /// Returns `false` only if the serve thread is gone.
    pub fn submit_step(
        &self,
        prefix: Option<u8>,
        mask: u8,
        req: &[u8],
        seam: Seam,
        reply: ServeReply,
    ) -> bool {
        let mut buf = self.pool.take();
        crate::interp::frame_step(prefix, mask, req, &mut buf);
        self.submit(buf, seam, reply)
    }

    /// Async CL-trust streaming-head submit (the io_uring reactor path): frame
    /// `reqLen(4 BE) :: request :: headLen(4 BE) :: upstreamHead :: bodyLen(4 BE)` into a
    /// fresh pooled buffer and cross `drorb_serve_proxy_stream_head`, delivering the
    /// transformed head (or EMPTY on a gzip reply) per `reply`. `body_len` is the
    /// upstream-declared `Content-Length`. Returns `false` only if the serve thread is
    /// gone.
    pub fn submit_proxy_stream_head(
        &self,
        req: &[u8],
        up_head: &[u8],
        body_len: usize,
        reply: ServeReply,
    ) -> bool {
        let mut buf = self.pool.take();
        buf.clear();
        buf.extend_from_slice(&(req.len() as u32).to_be_bytes());
        buf.extend_from_slice(req);
        buf.extend_from_slice(&(up_head.len() as u32).to_be_bytes());
        buf.extend_from_slice(up_head);
        buf.extend_from_slice(&(body_len as u32).to_be_bytes());
        self.submit(buf, Seam::ServeProxyStreamHead, reply)
    }

    /// Async effect-seam RESUME submit (the io_uring reactor path): frame
    /// `[prefix ::] mask :: reqLen(4 BE) :: request :: count :: (resultLen(4 BE) ::
    /// result)*` into a fresh pooled buffer and submit it across the effect RESUME
    /// seam (`drorb_serve_resume` / `_cfg` / `_pol`, per `seam`), delivering the next
    /// encoded `Step` per `reply`. The async analogue of the loop `call_seam` in
    /// [`crate::interp::run_effect_serve`]: identical framing
    /// (`crate::interp::frame_resume`, the SAME grown-result-list replay contract),
    /// no blocking recv. Returns `false` only if the serve thread is gone.
    pub fn submit_resume(
        &self,
        prefix: Option<u8>,
        mask: u8,
        req: &[u8],
        results: &[Vec<u8>],
        seam: Seam,
        reply: ServeReply,
    ) -> bool {
        let mut buf = self.pool.take();
        crate::interp::frame_resume(prefix, mask, req, results, &mut buf);
        self.submit(buf, seam, reply)
    }

    /// Submit one BORROWED HTTP/1.1 request (the zero-copy io_uring receive path)
    /// across the DIRECT metered seam (`drorb_serve_metered`, RAW request) with
    /// `meter` in scope, so the IP-filter and rate gates fire on the real client
    /// address / per-connection sequence with NO owned request copy (copy #1
    /// removed). Byte-identical to [`submit_metered_cfg_bytes`] with an empty config
    /// (`servePipelineOfMetered_default`), so it carries the no-config default
    /// connection path with the zero-copy borrow preserved. The direct metered seam
    /// takes the raw request unframed, so no in-slot prepend is needed. Returns
    /// `false` only if the serve thread is gone.
    #[cfg(target_os = "linux")]
    pub fn submit_borrowed_metered(
        &self,
        req: BorrowedReq,
        meter: Meter,
        reply: ServeReply,
    ) -> bool {
        self.tx
            .send(ServeJob {
                req: ReqBuf::Borrowed(req),
                seam: Seam::Http,
                reply,
                meter: Some(meter),
                tls: None,
            })
            .is_ok()
    }

    /// Submit one BORROWED HTTP/1.1 request across the metered BRAIDED seam
    /// (`drorb_serve_metered_braided`, RAW request) with `meter` in scope,
    /// zero-copy (no owned request copy). The braided seam takes the raw request
    /// unframed, so the borrowed view crosses directly. Returns `false` only if the
    /// serve thread is gone.
    #[cfg(target_os = "linux")]
    pub fn submit_borrowed_metered_braided(
        &self,
        req: BorrowedReq,
        meter: Meter,
        reply: ServeReply,
    ) -> bool {
        self.tx
            .send(ServeJob {
                req: ReqBuf::Borrowed(req),
                seam: Seam::ServeBraided,
                reply,
                meter: Some(meter),
                tls: None,
            })
            .is_ok()
    }

    /// Terminate one accepted TLS connection in-process on the verified TLS 1.3
    /// server: submit the connection fd + certificate material to the runtime-owner
    /// thread (which crosses `drorb_tls_serve`) and BLOCK until the whole
    /// connection — handshake, record-layer serve through the proven core, close —
    /// completes. The owner thread is held for that duration (see `run_tls_conn`).
    /// Returns once the connection is done (or immediately if the serve thread is
    /// gone). The Lean side owns and closes `fd`.
    pub fn serve_tls(&self, fd: std::os::fd::RawFd, cert: Arc<crate::tls::TlsCert>) {
        let (reply_tx, reply_rx) = channel::<PooledBuf>();
        let job = ServeJob {
            req: ReqBuf::Pooled(self.pool.take()),
            seam: Seam::Http,
            reply: ServeReply::Sync(reply_tx),
            meter: None,
            tls: Some(TlsConn { fd, cert }),
        };
        if self.tx.send(job).is_ok() {
            let _ = reply_rx.recv();
        }
    }

    /// Blocking convenience: submit `req` across `seam` and wait for the pooled
    /// response. `reply_tx`/`reply_rx` are the caller's own reusable channel
    /// (one per connection, reused across keep-alive requests — no per-request
    /// channel allocation on the hot path). Returns `None` if the serve thread
    /// is gone.
    pub fn call_seam(
        &self,
        req: PooledBuf,
        seam: Seam,
        reply_tx: &Sender<PooledBuf>,
        reply_rx: &Receiver<PooledBuf>,
    ) -> Option<PooledBuf> {
        if !self.submit(req, seam, ServeReply::Sync(reply_tx.clone())) {
            return None;
        }
        reply_rx.recv().ok()
    }

    /// Blocking HTTP call — the byte-stream `drorb_serve` seam.
    pub fn call(
        &self,
        req: PooledBuf,
        reply_tx: &Sender<PooledBuf>,
        reply_rx: &Receiver<PooledBuf>,
    ) -> Option<PooledBuf> {
        self.call_seam(req, Seam::Http, reply_tx, reply_rx)
    }

    /// Blocking config-route serve — cross `drorb_serve_cfg` with the operator
    /// config's route table in scope. Frames `cfgLen(4 BE) :: config :: request`
    /// into a fresh pooled buffer and serves the request through the config's
    /// declared routes (the proven core re-parses `config` and serves through
    /// `servePipelineOf (denoteOn defaultDeployment pc)`). Returns `None` if the
    /// serve thread is gone.
    pub fn call_cfg(
        &self,
        config: &[u8],
        req: &[u8],
        reply_tx: &Sender<PooledBuf>,
        reply_rx: &Receiver<PooledBuf>,
    ) -> Option<PooledBuf> {
        let mut framed = self.pool.take();
        framed.clear();
        framed.extend_from_slice(&(config.len() as u32).to_be_bytes());
        framed.extend_from_slice(config);
        framed.extend_from_slice(req);
        self.call_seam(framed, Seam::ServeCfg, reply_tx, reply_rx)
    }

    /// Cross the proven static-file path decision (`drorb_static_resolve`):
    /// the relative target bytes (after the serving prefix) in; on accept the
    /// '/'-joined resolved relative path out, `None` on reject (the core's
    /// UTF-8 gate refused a decoded segment — the caller answers `404`) or if
    /// the serve thread is gone. `reply_tx`/`reply_rx` are the caller's
    /// reusable per-connection channel.
    pub fn call_static_resolve(
        &self,
        rel: &[u8],
        reply_tx: &Sender<PooledBuf>,
        reply_rx: &Receiver<PooledBuf>,
    ) -> Option<Vec<u8>> {
        let mut framed = self.pool.take();
        framed.clear();
        framed.extend_from_slice(rel);
        let out = self.call_seam(framed, Seam::StaticResolve, reply_tx, reply_rx)?;
        match out.split_first() {
            Some((&1, resolved)) => Some(resolved.to_vec()),
            _ => None, // 0x00 (core reject) or an unexpected shape: fail safe
        }
    }

    /// Cross the proven static RESPONSE decision (`drorb_static_decide`,
    /// `Route.StaticDecide.staticDecideC`): the boundary-fact frame (found /
    /// keep-alive flags, file length, mtime, real file name, then the raw request
    /// bytes) in; the encoded serving plan out. `None` on an EMPTY output (a
    /// malformed frame — the caller drops the connection, never building response
    /// bytes itself) or a gone serve thread. `reply_tx`/`reply_rx` are the
    /// caller's reusable per-connection channel.
    pub fn call_static_decide(
        &self,
        frame: &[u8],
        reply_tx: &Sender<PooledBuf>,
        reply_rx: &Receiver<PooledBuf>,
    ) -> Option<Vec<u8>> {
        let mut framed = self.pool.take();
        framed.clear();
        framed.extend_from_slice(frame);
        let out = self.call_seam(framed, Seam::StaticDecide, reply_tx, reply_rx)?;
        if out.is_empty() {
            None
        } else {
            Some(out.to_vec())
        }
    }

    /// Blocking metered HTTP call — the byte-stream path through
    /// `drorb_serve_metered`, carrying the connection context `meter` (client
    /// address + per-connection sequence) so the proven IP-filter and rate gates
    /// fire. `reply_tx`/`reply_rx` are the caller's reusable per-connection
    /// channel. Returns `None` if the serve thread is gone. Retained proven seam;
    /// the default connection path uses [`call_metered_cfg`] since Braid 0.
    #[allow(dead_code)]
    pub fn call_metered(
        &self,
        req: PooledBuf,
        meter: Meter,
        reply_tx: &Sender<PooledBuf>,
        reply_rx: &Receiver<PooledBuf>,
    ) -> Option<PooledBuf> {
        if !self.submit_metered(req, meter, ServeReply::Sync(reply_tx.clone())) {
            return None;
        }
        reply_rx.recv().ok()
    }

    /// Blocking Braid-0 metered CONFIG call — the byte-stream path through
    /// `drorb_serve_metered_cfg`, carrying the connection context `meter` AND the
    /// operator `config` so the metered IP-filter and rate gates fire over the
    /// config's deployment. Frames `cfgLen(4 BE) :: config :: request` into a fresh
    /// pooled buffer; an EMPTY `config` (no `DRORB_CONFIG`) frames a `cfgLen = 0`
    /// header, and the proven core serves `servePipelineOfMetered defaultDeployment`
    /// — byte-identical to `call_metered` (`servePipelineOfMetered_default`, `rfl`).
    /// `reply_tx`/`reply_rx` are the caller's reusable per-connection channel. Returns
    /// `None` if the serve thread is gone.
    pub fn call_metered_cfg(
        &self,
        config: &[u8],
        req: &[u8],
        meter: Meter,
        reply_tx: &Sender<PooledBuf>,
        reply_rx: &Receiver<PooledBuf>,
    ) -> Option<PooledBuf> {
        let mut framed = self.pool.take();
        framed.clear();
        framed.extend_from_slice(&(config.len() as u32).to_be_bytes());
        framed.extend_from_slice(config);
        framed.extend_from_slice(req);
        if !self.submit_metered_cfg(framed, meter, ServeReply::Sync(reply_tx.clone())) {
            return None;
        }
        reply_rx.recv().ok()
    }

    /// Blocking metered BRAIDED call — the RAW request crosses
    /// `drorb_serve_metered_braided` with `meter` in scope, serving over
    /// `braidedDeployment` (the proven forward-auth gate + request-id echo composed at
    /// the head of the deployed metered chain). A request with no braid markers is
    /// byte-identical to [`call_metered`] (`servePipelineOfMetered_braided_off_eq`); an
    /// `x-forward-auth` request is refused `401`, an `x-request-id` request is echoed.
    /// `reply_tx`/`reply_rx` are the caller's reusable per-connection channel. Returns
    /// `None` if the serve thread is gone.
    pub fn call_metered_braided(
        &self,
        req: &[u8],
        meter: Meter,
        reply_tx: &Sender<PooledBuf>,
        reply_rx: &Receiver<PooledBuf>,
    ) -> Option<PooledBuf> {
        let mut buf = self.pool.take();
        buf.clear();
        buf.extend_from_slice(req);
        if !self.submit_metered_braided(buf, meter, ServeReply::Sync(reply_tx.clone())) {
            return None;
        }
        reply_rx.recv().ok()
    }
}

/// The serve-owner job loop: drain `rx`, cross each job's seam on the
/// CALLING thread, and deliver each response per its reply route. This is
/// the single-owner loop body, unchanged — it now runs on the primary
/// runtime-owner thread and on every attached owner thread
/// ([`spawn_attached_owner`]), so the caller must first make the calling
/// thread able to use the runtime: `lean_boot` (primary, exactly once per
/// process) or `lean_initialize_thread` (attached owners, after the primary
/// is up).
fn serve_owner_loop(rx: Receiver<ServeJob>, serve_pool: Arc<BufferPool>) {
    for job in rx {
        // A TLS connection: run the whole verified handshake + record-layer
        // serve on this owner thread, then signal completion. No response
        // bytes cross back (the seam wrote them straight to the socket).
        if let Some(tls) = &job.tls {
            run_tls_conn(tls);
            // (On non-Linux `ServeReply` has only the `Sync` variant, so
            // this pattern is irrefutable there; on Linux the io_uring
            // `Shard` variant makes it refutable — the TLS path always
            // delivers `Sync`.)
            #[allow(irrefutable_let_patterns)]
            if let ServeReply::Sync(tx) = job.reply {
                let _ = tx.send(serve_pool.take());
            }
            continue;
        }
        let mut resp = serve_pool.take();
        // ZERO-COPY STATIC BODY (`DRORB_SPAN=23`): set when `resp` is a
        // response HEAD whose (static, constant) body rides by reference.
        let mut split_static = false;
        // GEARS-ENMESH: the exact `GET /health` request, when
        // `DRORB_HEALTH_NATIVE=1`, is answered by cake--pancake-compiled
        // x64 machine code linked into this process (not the leanc serve).
        // `serve_native_into` returns `false` (leaving `resp` untouched)
        // for every other request and every non-demo build, so the leanc
        // pipeline below still runs for everything else.
        // CERTIFIED EXPORT-FUNCTION SERVE: the chosen route (`GET /`), when
        // `DRORB_CAKE_SERVE=1`, is answered by the certified export-function
        // machine code linked into this process (not the leanc serve).
        // `serve_cake_into` returns `false` (leaving `resp` untouched) for every
        // other request and every non-demo build, so the leanc pipeline below
        // still runs for everything else. Checked before the native /health path
        // and the deployed serve; all three defaults are byte-identical when their
        // flags are unset.
        if !crate::cake_serve::serve_cake_into(job.req.bytes(), &mut resp)
            && !serve_native_into(job.req.bytes(), &mut resp)
        {
            // DRORB_SPAN A/B chokepoint: when set, EVERY HTTP serve job (metered
            // direct/cfg/braided AND the plain `Seam::Http`) is diverted to the
            // assembled cons-free flat serve (`drorb_serve_span`, DRORB_SPAN=1) or
            // its byte-identical `List` twin (`drorb_serve_span_list`, =2) instead
            // of the deployed `drorb_serve_metered`. Gated to the HTTP serve seams
            // so the effect/proxy/ws/datagram seams are untouched. This is the one
            // place ALL serve jobs funnel through, so it catches whichever serve
            // path (borrowed-zero-copy metered, cfg fallback, …) the reactor chose.
            let is_http_serve = job.meter.is_some() || matches!(job.seam, Seam::Http);
            if is_zc_split_span() && is_http_serve {
                // ZERO-COPY STATIC BODY (`DRORB_SPAN=23`): the tagged split seam.
                // On the fast `/bulk` arm only the HEAD comes back (`true`); the
                // static constant body is attached by REFERENCE downstream — the
                // io_uring shard gather-writes head + static buffer, the non-shard
                // reply paths append it once below (correctness fallback).
                split_static = serve_zc_into(job.req.bytes(), &mut resp);
            } else if let (Some(span), true) = (span_serve_seam(), is_http_serve) {
                serve_into_via(job.req.bytes(), span, &mut resp);
            } else {
                // DEPLOYED DEFAULT (no DRORB_SPAN): every HTTP serve path is now
                // RFC 7230/7231-conformant. The metered variants cross their conformant
                // twin (`drorb_serve_metered_conformant` / `_cfg_conformant` /
                // `_braided_conformant`) — the proven `conformantServe` wrapper runs the
                // request-validation gate FIRST, then the SAME metered IP-filter/rate
                // fold (peer/seq in scope — the gates are composed WITH conformance, NOT
                // bypassed), then the Date (F1) / HEAD-strip (B1) finisher. The
                // non-metered plain HTTP seam crosses `drorb_serve_conformant` (the
                // wrapper over the non-metered `drorbServe`). The ws/datagram/effect-step
                // seams are untouched — they are not HTTP request→response byte serves.
                match job.meter {
                    // Braid 0: a metered job carrying the `ServeCfg` seam is the
                    // cfg-FRAMED metered serve; `ServeBraided` serves over the braided
                    // deployment; every other metered job is the plain metered serve —
                    // each now wrapped conformant.
                    Some(meter) => match job.seam {
                        // `Seam::ServeCfg` (the macOS/io_uring default): the cfg-conformant
                        // serve, which for the EMPTY-config default diverts to the DENSE
                        // metered-conformant serve (`/bulk` body-cliff fix) — byte-identical,
                        // gates + conformance intact.
                        Seam::ServeCfg => {
                            serve_metered_cfg_conformant_into(job.req.bytes(), meter, &mut resp)
                        }
                        Seam::ServeBraided => {
                            serve_metered_braided_conformant_into(job.req.bytes(), meter, &mut resp)
                        }
                        // The plain metered default (`Seam::Http` + meter, e.g. the io_uring
                        // borrowed-direct path): the DENSE metered-conformant serve —
                        // byte-identical to `drorb_serve_metered_conformant`
                        // (`meteredDenseConformant_eq_meteredConformant`) but dense on `/bulk`.
                        _ => serve_metered_dense_conformant_into(job.req.bytes(), meter, &mut resp),
                    },
                    None => match job.seam {
                        // The non-metered plain HTTP serve is made conformant too, so
                        // every deployed HTTP request is RFC-conformant regardless of the
                        // reactor path — and its INNER is now the index-native-head serve
                        // (`drorb_serve_conformant_head_idx`, proven byte-identical to
                        // `drorb_serve_conformant` by
                        // `Dataplane.serveConformantHeadIdx_eq_drorbServeConformant`).
                        // (This overrides the DRORB_FLAT A/B on THIS fallback path — a
                        // measurement lever, not the deployed default.)
                        Seam::Http => serve_into_via(
                            job.req.bytes(),
                            drorb_serve_conformant_head_idx,
                            &mut resp,
                        ),
                        _ => serve_into(job.req.bytes(), job.seam, &mut resp),
                    },
                }
            }
        }
        // `job.req` drops here: a pooled request buffer returns to the
        // pool; a borrowed view is a no-op drop (the shard owns the lease).
        match job.reply {
            ServeReply::Sync(tx) => {
                // Non-shard path: no gather-write available; reassemble (one
                // append) so the bytes served are identical either way.
                if split_static {
                    resp.extend_from_slice(static_bulk_body());
                }
                let _ = tx.send(resp);
            }
            #[cfg(target_os = "linux")]
            ServeReply::Shard(mailbox, efd, conn) => {
                if mailbox
                    .send(ShardDone {
                        conn,
                        resp,
                        split_static,
                    })
                    .is_ok()
                {
                    crate::uring::wake(efd);
                }
            }
            #[cfg(any(
                target_os = "macos",
                target_os = "ios",
                target_os = "freebsd",
                target_os = "netbsd",
                target_os = "openbsd",
                target_os = "dragonfly"
            ))]
            ServeReply::Reactor(mailbox, wake_fd, conn) => {
                // The kqueue reactor has no split-send path; reassemble (one
                // append) so the bytes served are identical either way.
                if split_static {
                    resp.extend_from_slice(static_bulk_body());
                }
                if mailbox.send(KqDone { conn, resp }).is_ok() {
                    crate::kqueue::wake(wake_fd);
                }
            }
        }
    }
}

/// Boot the runtime on a dedicated thread and return a gateway to it. Blocks
/// until the runtime is up so bind failures are reported before we accept.
///
/// SINGLE-OWNER: this thread is the sole caller of `drorb_serve`. Every request
/// from every connection/shard serializes here, so the steady-state throughput
/// ceiling is `1 / (serve latency)` — one core's worth of the proven pipeline,
/// however many IO cores feed it. The IO path (recv/send, framing, TLS) scales
/// across cores; the pure `ByteArray -> ByteArray` transform does not, because
/// the runtime is a process-global singleton. This is the honest bottleneck to
/// measure and, if it binds, to lift only by a design that admits multiple
/// runtime owners. That design now exists as an opt-in lever: [`serve_owner_set`]
/// attaches `DRORB_SERVE_OWNERS - 1` additional owner threads to the one booted
/// runtime (see [`spawn_attached_owner`] for the argument and its limits);
/// unset, this thread remains the sole caller, exactly as described above.
pub fn spawn_serve_thread(pool: Arc<BufferPool>) -> ServeGateway {
    let (tx, rx) = channel::<ServeJob>();
    let (ready_tx, ready_rx) = channel::<()>();
    let serve_pool = Arc::clone(&pool);
    std::thread::Builder::new()
        .name("drorb-serve".into())
        .spawn(move || {
            lean_boot();
            // ZERO-COPY STATIC BODY (`DRORB_SPAN=23`): materialize the process-static
            // constant body ONCE, before any request crosses the tagged split seam.
            if is_zc_split_span() {
                init_static_bulk_body();
            }
            let _ = ready_tx.send(());
            serve_owner_loop(rx, serve_pool);
        })
        .expect("failed to spawn the drorb serve thread");
    ready_rx
        .recv()
        .expect("serve thread died before finishing runtime init");
    ServeGateway { tx, pool }
}

// Attached-owner thread registration (exported by the runtime shared library).
// A thread the runtime did not create must register itself once, after the
// process-global runtime is initialized and before its first runtime call, so
// its thread-local allocator/state exist.
unsafe extern "C" {
    fn lean_initialize_thread();
}

/// How many serve-owner threads this deployment runs: `DRORB_SERVE_OWNERS`,
/// clamped to `1..=64`. Default (unset/unparsable) is `1` — exactly the
/// original single-owner model, so the lever is opt-in. Read once (env is
/// fixed for the process lifetime).
pub fn serve_owner_count() -> usize {
    use std::sync::OnceLock;
    static N: OnceLock<usize> = OnceLock::new();
    *N.get_or_init(|| {
        std::env::var("DRORB_SERVE_OWNERS")
            .ok()
            .and_then(|v| v.parse::<usize>().ok())
            .map(|n| n.clamp(1, 64))
            .unwrap_or(1)
    })
}

/// Spawn one ATTACHED serve-owner thread over the ALREADY-BOOTED process-global
/// runtime and return a gateway whose jobs cross the seam on that thread.
///
/// This lifts the SINGLE-OWNER ceiling (see [`spawn_serve_thread`]) without
/// pretending the runtime can be instantiated twice — it cannot (the module
/// initializer installs process-global constants once). There is still ONE
/// runtime; this adds more threads that call into it, each registered with
/// `lean_initialize_thread`. Why the byte-serve crossings tolerate that:
///
/// * every entry routed here is a pure `ByteArray -> ByteArray` export: each
///   call allocates its working objects on the calling thread's registered
///   allocator, and the input and response objects are created, consumed, and
///   dropped on that same thread — no heap object ever crosses between owner
///   threads;
/// * the only objects shared BETWEEN owner threads are the module's top-level
///   constants, and the generated module init marks every `_init_`-computed
///   global persistent (refcount ops on persistent objects are no-ops), so
///   concurrent calls never race an inc/dec on shared state;
/// * the C shims on these paths hold no mutable state: the byte-marshalling
///   adapter is stateless, and the verified-crypto dispatch table is populated
///   once by a loader constructor (read-only afterwards);
/// * thunk forcing and any object the runtime itself shares across threads use
///   the runtime's own atomic paths (the same machinery its task system relies
///   on).
///
/// NOT covered by that argument, so callers must NOT route them here (keep
/// them on the primary owner, as `main` wires them): the TLS connection seam
/// (an IO computation that blocks its owner for the connection lifetime), the
/// UDP/datagram listener, and the admin/config/reload crossings. The IO hosts
/// (`blocking::run`, `uring::run`) shard only connection byte-serve traffic
/// across attached owners; each connection (or shard) is pinned to ONE owner,
/// so per-connection request/response FIFO order is preserved.
///
/// Must be called only after the primary owner is up (enforced by taking its
/// gateway, which exists only after the boot handshake). Blocks until the new
/// thread has registered itself.
pub fn spawn_attached_owner(primary: &ServeGateway, idx: usize) -> ServeGateway {
    let (tx, rx) = channel::<ServeJob>();
    let (ready_tx, ready_rx) = channel::<()>();
    let serve_pool = Arc::clone(&primary.pool);
    std::thread::Builder::new()
        .name(format!("drorb-serve-{idx}"))
        .spawn(move || {
            // SAFETY: the caller holds the primary gateway, so `lean_boot` has
            // completed (runtime + module init done); registering this thread
            // before its first crossing is exactly the documented contract for
            // threads the runtime did not create.
            unsafe { lean_initialize_thread() };
            let _ = ready_tx.send(());
            serve_owner_loop(rx, serve_pool);
        })
        .expect("failed to spawn an attached serve-owner thread");
    ready_rx
        .recv()
        .expect("attached serve owner died during thread registration");
    ServeGateway {
        tx,
        pool: Arc::clone(&primary.pool),
    }
}

/// The deployment's serve-owner set: the primary runtime-owner gateway first,
/// then `serve_owner_count() - 1` attached owners. With `DRORB_SERVE_OWNERS`
/// unset this is exactly `vec![primary]` — no extra thread, no behavior
/// change. The IO hosts index into this set to pin each connection (blocking
/// path) or each reactor shard (io_uring path) to one owner.
pub fn serve_owner_set(primary: ServeGateway) -> Vec<ServeGateway> {
    let n = serve_owner_count();
    let mut owners = Vec::with_capacity(n);
    owners.push(primary);
    for i in 1..n {
        let gw = spawn_attached_owner(&owners[0], i);
        owners.push(gw);
    }
    if n > 1 {
        eprintln!(
            "dataplane: {n} serve owners (one runtime; {} attached crossing thread{})",
            n - 1,
            if n == 2 { "" } else { "s" }
        );
    }
    owners
}
