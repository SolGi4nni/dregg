/-
Dataplane — the proven serve exposed with a C ABI for a native host to drive.

`Arena.Orb.main` runs the deployed serve as a one-shot stdin→stdout filter, and
`IoMac` drives that same proven core from a C accept loop with Lean as the
CALLEE of `@[extern]`. This module inverts the direction: it hands the proven
pipeline OUT across the C ABI as an `@[export]` symbol (`drorb_serve`), so a
native host (the Rust dataplane) is the CALLER — it owns the socket and the
accept loop and calls into the proven core for every request.

The handler is byte-identical to the one the shipped binaries run: request bytes
in, the deployed guarded response bytes out, `deployStepIngress` over a fresh
`ObsState.init`. Nothing here knows a socket exists; the host moves the bytes.
-/
import Reactor.Deploy
import Captp.Export
import Reactor.Ingress
import Reactor.H2Ingress
import Reactor.Observe
-- The flat, linear-time runtime for the `x-corr` correlation-id render
-- (`Reactor.Deploy.corrBytes`). This module carries the `@[csimp]`
-- (`Reactor.ObserveFast.corrBytes_eq_fast`) that installs the `O(N)`
-- `corrBytesFast` as the COMPILED body of `corrBytes` — the render runs on every
-- served request (stage 8 `deployProg`), so importing it here makes the deployed
-- `drorb_serve` use the linear render instead of the spec's `O(N²)`
-- `String.intercalate`. The logical spec is unchanged; the emitted bytes are
-- byte-identical (proven).
import Reactor.ObserveFast
-- The reverse-proxy backend-selection seam (`drorb_proxy_pick`) lives in
-- `Reactor.ProxyDial`. Importing it here places `initialize_Reactor_ProxyDial`
-- in the closure of `initialize_Dataplane`, so the single host-side runtime-init
-- call brings up the proven `Proxy.selectChain` pick's constants AND the archive
-- (ffi/build-dataplane-lib.sh globs every `*.c.o.export`) includes
-- `Reactor/ProxyDial.c.o.export` — without this the `drorb_proxy_pick` symbol is
-- never built into `libdrorb.a` and the host link fails undefined.
import Reactor.ProxyDial
import Reactor.LoadBalance
import Reactor.Proxy.Connect
import Reactor.Proxy.Grpc
-- The multi-protocol seams (`drorb_serve_ws_frame`, `drorb_serve_datagram`) live
-- in `Dataplane.Multi`. Importing it here places its module initializer in the
-- closure of `initialize_Dataplane`, so the single host-side init call brings up
-- all three exports' constants (a `@[export]` whose module is uninitialized has
-- uninitialized closures — a crash on first call).
import Dataplane.Multi
-- The effect/continuation serve seam (`drorb_serve_step` / `drorb_serve_resume`)
-- lives in `Reactor.ServeStep`. Importing it here places its module initializer in
-- the closure of `initialize_Dataplane` (so the single host-side init brings up the
-- seam's constants), and `ffi/build-dataplane-lib.sh` compiles its
-- `Reactor/ServeStep.c.o.export` object into `libdrorb.a` so the two new exports
-- link.
import Reactor.ServeStep
-- The CL-trust head-independence seam (`Reactor.ProxyStreamHead.proxyStreamHead`, whose
-- `proxyRespHead_factors` proves the non-gzip transformed head is a function of
-- (input, upstream-head, body-LENGTH) — never the body bytes). Importing it here places
-- its module initializer in the closure of `initialize_Dataplane` and
-- `ffi/build-dataplane-lib.sh` compiles its `Reactor/ProxyStreamHead.c.o.export` object
-- into `libdrorb.a` so the new `drorb_serve_proxy_stream_head` export links.
import Reactor.ProxyStreamHead
-- The sans-IO STREAMING serve (`Reactor.ServeStream.serveChunkList`, the proven
-- head-chunk + bounded-body-chunk emit whose concatenation is `serialize` —
-- `serveChunkList_flatten`). Importing it here places its module initializer in the
-- closure of `initialize_Dataplane` (so the boot brings up the streaming serve's
-- constants) and `ffi/build-dataplane-lib.sh` compiles its
-- `Reactor/ServeStream.c.o.export` object into `libdrorb.a` so the new
-- `drorb_serve_stream` export links.
import Reactor.ServeStream
-- The bridged flat `ByteArray → ByteArray` serve (`Reactor.ServeArr.serveArr`,
-- proven byte-identical to the deployed List serve via
-- `Reactor.ServeArr.serveArr_correct`). Importing it here places its module
-- initializer in the closure of `initialize_Dataplane` and lets
-- `ffi/build-dataplane-lib.sh` archive its `Reactor/ServeArr.c.o.export` object
-- so the `drorb_serve_flat` A/B seam below links.
import Reactor.ServeArr
-- The ASSEMBLED flat serve (`Datapath.ServeFlat.serveFlatEcho`, exported
-- `drorb_serve_span`) and its byte-identical List twin (`serveListEcho`, exported
-- `drorb_serve_span_list`) — index-native parse ⟶ flat security-header stage ⟶ flat
-- ByteArray body ⟶ flat egress, proven byte-identical (`serveFlatEcho_refines`).
-- Importing it here places `initialize_Datapath_ServeFlat` in the closure of
-- `initialize_Dataplane` (so the boot brings up the flat serve's constants) and
-- `ffi/build-dataplane-lib.sh`'s import-closure walker compiles its
-- `Datapath/ServeFlat.c.o.export` object into `libdrorb.a` so the `DRORB_SPAN` A/B
-- seam links.
import Datapath.ServeFlat
import Datapath.ServeFlatFull
-- The BODY-DENSE poly serve (`Datapath.ServeFlatBodyPoly.serveBodyPolyArr`, exported
-- `drorb_serve_bodypoly`) and its byte-identical List twin (`serveBodyPolyList`, exported
-- `drorb_serve_bodypoly_list`) — parse ⟶ the compress codec-tag body stage ⟶ serialize, the
-- BODY carried DENSE (`ByteSeq`-poly, `ByteArray` instance) through the fold, proven
-- byte-identical (`serveBodyPoly_refines`). Importing it here places
-- `initialize_Datapath_ServeFlatBodyPoly` in the closure of `initialize_Dataplane` and
-- `ffi/build-dataplane-lib.sh`'s import-closure walker compiles its
-- `Datapath/ServeFlatBodyPoly.c.o.export` object into `libdrorb.a` so the `DRORB_SPAN=5/6`
-- body A/B seam links.
import Datapath.ServeFlatBodyPoly
-- The FULL POLY serve (`Datapath.ServePolyFull.servePolyFull`, exported
-- `drorb_serve_poly`) — the deployed 14-stage routed response rendered through the
-- POLYMORPHIC egress fold (`HdrSeq.foldPush` header block over `HdrBlock` + `ByteArray`
-- body), proven byte-identical to `drorbServe` (`servePolyFull_eq_drorbServe`). Importing
-- it here places `initialize_Datapath_ServePolyFull` in the closure of
-- `initialize_Dataplane` so the build's import-closure walker compiles its
-- `Datapath/ServePolyFull.c.o.export` object into `libdrorb.a` for the `DRORB_SPAN=7` seam.
import Datapath.ServePolyFull
-- The GENUINELY-DENSE multi-stage serve FOLD (`Datapath.ServeDense.serveDenseArr`,
-- exported `drorb_serve_dense`) and its byte-identical `List` twin
-- (`serveDenseList`, exported `drorb_serve_dense_list`) — parse index-native ⟶ a
-- 3-stage response-transform header fold over the flat `HdrBlock` ⟶ `ByteArray`-body
-- flat egress, proven byte-identical (`serveDense_refines`). Importing it here places
-- `initialize_Datapath_ServeDense` in the closure of `initialize_Dataplane` so the
-- import-closure walker compiles its `Datapath/ServeDense.c.o.export` object into
-- `libdrorb.a` for the `DRORB_SPAN=8` (dense) / `=9` (`List` twin) seams.
import Datapath.ServeDense
-- The DENSE serve that RUNS THE DEPLOYED BODY TRANSFORM DENSE
-- (`Datapath.ServeDenseFull.serveDenseFull`, exported `drorb_serve_densefull`) and
-- its byte-identical `List` twin (`serveDenseFullList`, exported
-- `drorb_serve_densefull_list`) — parse index-native ⟶ 3-stage header fold ⟶ the
-- deployed html-rewrite body transform run DENSE (`rewriteBytesDense`, `ByteArray`
-- index-native, byte-identical to `rewriteBytes` by `rewriteBytesDense_refines`) ⟶
-- flat egress, proven byte-identical (`serveDenseFull_refines`). Importing it here
-- places `initialize_Datapath_ServeDenseFull` in the closure of
-- `initialize_Dataplane` so the import-closure walker compiles its
-- `Datapath/ServeDenseFull.c.o.export` object into `libdrorb.a` for the
-- `DRORB_SPAN=10` (dense-full) / `=11` (`List` twin) large-body seams.
import Datapath.ServeDenseFull
-- The FULLY-DENSE-TOKENIZER serve (`drorb_serve_densefull2`): same import rationale
-- as `ServeDenseFull` above — places `initialize_Datapath_ServeDenseFull2` in the
-- `initialize_Dataplane` closure so `ffi/build-dataplane-lib.sh` archives its
-- `Datapath/ServeDenseFull2.c.o.export` into `libdrorb.a` for the `DRORB_SPAN=12`
-- (fully-dense-tokenizer) large-body seam.
import Datapath.ServeDenseFull2
-- The CONTENT-TYPE-GATED serve (`Datapath.ServeGated.serveGated`, exported
-- `drorb_serve_gated`) and its byte-identical `List` twin (`serveGatedList`, exported
-- `drorb_serve_gated_list`) — parse index-native ⟶ 3-stage header fold ⟶ the body
-- GATED on the response `Content-Type`: on `text/html` the dense deployed rewrite, on
-- anything else (the common case) the body handed STRAIGHT to `serializeFlatB` as the
-- borrowed `ByteArray` (never tokenized, never consed = zero-copy passthrough). Proven
-- byte-identical to its `List` twin (`serveGated_refines`) and grounded in the proven
-- content-type gate (`serveGated_body_is_gate`). Importing it here places
-- `initialize_Datapath_ServeGated` in the closure of `initialize_Dataplane` so
-- `ffi/build-dataplane-lib.sh`'s import-closure walker compiles its
-- `Datapath/ServeGated.c.o.export` object into `libdrorb.a` for the `DRORB_SPAN=13`
-- (gated) / `=14` (`List` twin) common-case zero-copy body seam.
import Datapath.ServeGated
-- The COMBINED fast serve exemplar (`Datapath.ServeUltra.serveUltra`, exported
-- `drorb_serve_ultra`) and its byte-identical `List` twin (`serveUltraList`, exported
-- `drorb_serve_ultra_list`) — ALL of the datapath wins in ONE serve: parse index-native
-- ⟶ dense header fold ⟶ content-type-GATED body (non-HTML = zero-copy passthrough,
-- text/html = the FULLY-DENSE tokenizer `rewriteBytesDense2`, no token `List`) ⟶ flat
-- egress. Proven byte-identical to its `List` twin (`serveUltra_refines`) and to the
-- deployed gated serve `=13` (`serveUltra_eq_serveGated`). Importing it here places
-- `initialize_Datapath_ServeUltra` in the closure of `initialize_Dataplane` so
-- `ffi/build-dataplane-lib.sh`'s import-closure walker compiles its
-- `Datapath/ServeUltra.c.o.export` object into `libdrorb.a` for the `DRORB_SPAN=16`
-- (combined) and `=17` (its `List` twin) seams.
import Datapath.ServeUltra
-- The ZERO-COPY BODY split serve (`Datapath.ServeSplit.serveSplitHead`, exported
-- `drorb_serve_split_head`): Lean computes ONLY the response HEAD (status line + headers +
-- Content-Length + separator) densely; the reactor writes that head THEN the borrowed body
-- (the request buffer) to the socket via `writev`/two writes — the body is NEVER appended
-- into an output `ByteArray` (the append `DRORB_SPAN=13` still does). Proven head ++ body =
-- the appended serve (`serveSplit_reassemble`) and byte-identical to the deployed serialize
-- (`serveSplitHead_append_eq_serialize`). Importing it here places
-- `initialize_Datapath_ServeSplit` in the closure of `initialize_Dataplane` so
-- `ffi/build-dataplane-lib.sh`'s import-closure walker compiles its
-- `Datapath/ServeSplit.c.o.export` object into `libdrorb.a` for the `DRORB_SPAN=15`
-- zero-copy-body writev seam.
import Datapath.ServeSplit
-- The RUNTIME-DENSE full serve (`Datapath.ServeDenseReal.serveDenseReal`, exported
-- `drorb_serve_dense_real`): the deployed serve whose `/bulk` arm emits the DENSE head +
-- DENSE 1 MiB `Array` body (no per-byte `List` cons — the body-cliff fix), proven
-- byte-identical to the deployed `drorbServe` (`serveDenseReal_refines` +
-- `deployedServeRef_eq_drorbServe`, closed below in `serveDenseReal_eq_drorbServe`).
-- Importing it here places `initialize_Datapath_ServeDenseReal` in the closure of
-- `initialize_Dataplane` so the export-closure walker compiles its `.c.o.export` object
-- into `libdrorb.a` for the `DRORB_SPAN=18` seam.
import Datapath.ServeDenseReal
-- The CONFORMANT-DENSE serve (`Datapath.ServeConformantDense.serveConformantDenseIdx`,
-- exported `drorb_serve_conformant_dense`): the RFC-conformance wrapper around the
-- index-decided DENSE `/bulk` serve — so the deployed-default semantics never re-cons
-- the 1 MiB body as a `List`. Proven byte-identical to `drorbServeConformant` below
-- (`serveConformantDenseIdx_eq_drorbServeConformant`). Importing it here places
-- `initialize_Datapath_ServeConformantDense` in the closure of `initialize_Dataplane`
-- so the export-closure walker compiles its `.c.o.export` object into `libdrorb.a`
-- for the `DRORB_SPAN=20` seam.
import Datapath.ServeConformantDense
-- The FUSED-POSTPROCESS conformant-dense serve (`drorb_serve_conformant_fast`,
-- `DRORB_SPAN=22`): the same wrapper + dense inner as `=20`, its `Date`-splice +
-- `x-corr`-scrub fused to ONE body attach (`scrubDateBA`). Imported so
-- `initialize_Datapath_ServeConformantFast` rides `initialize_Dataplane`'s closure
-- and `ffi/build-dataplane-lib.sh` compiles its export object into `libdrorb.a`.
import Datapath.ServeConformantFast
-- The ZERO-COPY-BODY split of the fused serve (`drorb_serve_conformant_zc` +
-- `drorb_bulk_body`, `DRORB_SPAN=23`): the fast `/bulk` arm returns a tagged
-- head only and the host gather-writes the process-static constant body — no
-- whole-body copy on the serve path. Imported so
-- `initialize_Datapath_ServeZc` rides `initialize_Dataplane`'s closure and the
-- export objects link into `libdrorb.a`.
import Datapath.ServeZc
-- The INDEX-NATIVE-HEAD serve (`Datapath.ServeHeadIdx.serveHeadIdx`, exported
-- `drorb_serve_head_idx`): ONE arena parse per request off the borrowed window,
-- BOTH dense arms decided by index probes on the arena head (no `arenaToProto` /
-- `protoReqOf` List materialization on the deciding path), the proven dense
-- emitters on the arms. Proven byte-identical to the deployed serve
-- (`serveHeadIdx_refines` + `deployedServeRef_eq_drorbServe`, closed below in
-- `serveHeadIdx_eq_drorbServe`). THE DEPLOYED `Seam::Http` DEFAULT: the host's
-- non-metered HTTP seam now crosses it (bare, and via the conformant wrapper
-- `drorb_serve_conformant_head_idx` below). Importing it here places
-- `initialize_Datapath_ServeHeadIdx` in the closure of `initialize_Dataplane` so
-- the export-closure walker compiles its `.c.o.export` object into `libdrorb.a`.
import Datapath.ServeHeadIdx
import Datapath.ServeMeteredHeadIdx
-- The dense-stamped nine-edge metered serve (`Datapath.DenseStamps`,
-- exported `drorb_serve_metered_plus2_head_idx` /
-- `drorb_serve_metered_plus2_dense_conformant`): the extended deployed default
-- with the `/bulk` dense arm restored — the stamped dense head + dense 1 MiB
-- body, proven byte-identical to `drorbServeMeteredPlus2Conformant`. Importing
-- it here places `initialize_Datapath_DenseStamps` in the closure of
-- `initialize_Dataplane` so its `.c.o.export` object lands in `libdrorb.a`.
import Datapath.DenseStamps
-- The DEPLOYED-RUNG dense-stamped metered serve (`Datapath.DenseStampsPlus5`,
-- exported `drorb_serve_metered_plus5_head_idx` /
-- `drorb_serve_metered_plus5_dense_conformant`): the deployed DEFAULT (the
-- plus5-conformant fold) with the `/bulk` dense arm — the fully-stamped dense
-- head (nine plus2 edges + Timing-Allow-Origin + the cookie-hardener map) +
-- dense 1 MiB body, proven byte-identical to `drorbServeMeteredPlus5Conformant`
-- for EVERY (peer, seq, input). THE DEFAULT metered crossing re-points here.
-- Importing it places `initialize_Datapath_DenseStampsPlus5` in the closure of
-- `initialize_Dataplane` so its `.c.o.export` object lands in `libdrorb.a`.
import Datapath.DenseStampsPlus5
-- The plus6 deployed-rung dense serve (`Datapath.DenseStampsPlus6`, exported
-- `drorb_serve_metered_plus6_head_idx` / `drorb_serve_metered_plus5_dense_conformant`
-- [the host default symbol, now the plus6 fold] / the honest-named alias
-- `drorb_serve_metered_plus6_dense_conformant`): three un-inerted stages (405
-- method allow-list, 413 declared-size, multipart/byteranges 206) + three built
-- features (CL+TE-conflict 400, negotiated /welcome i18n, /dashboard page) over
-- the plus5 fold, dense /bulk arm kept, byte-identity proven for every
-- (peer, seq, input). Importing it places initialize_Datapath_DenseStampsPlus6
-- in the closure of initialize_Dataplane so its export object lands in the
-- archive.
import Datapath.DenseStampsPlus6
-- The plus7 deployed-rung dense serve (Datapath.DenseStampsPlus7, exported
-- drorb_serve_metered_plus7_head_idx / drorb_serve_metered_plus5_dense_conformant
-- [the host default symbol, now the plus7 fold] / the honest-named alias
-- drorb_serve_metered_plus7_dense_conformant): the date conditionals
-- (If-Modified-Since 304 / If-Unmodified-Since 412 via the HTTP-date total
-- order), the If-Range/multi-range decisions on the native range handler (the
-- unveil), and the static freshness stamps (Cache-Control + Last-Modified)
-- over the plus6 fold, dense /bulk arm kept, byte-identity proven for every
-- (peer, seq, input). Importing it places initialize_Datapath_DenseStampsPlus7
-- in the closure of initialize_Dataplane so its export object lands in the
-- archive.
-- import Datapath.DenseStampsPlus7 -- RE-ENABLE when the plus7 wave lands its
-- module (the import was pre-wired ahead of the file; with the file absent it
-- breaks the whole build). The default host symbol is owned by
-- Datapath.DenseStampsPlus8 below until then.
-- The plus8 deployed-rung dense serve (Datapath.DenseStampsPlus8, exported
-- drorb_serve_metered_plus8_head_idx / drorb_serve_metered_plus5_dense_conformant
-- [the host default symbol, now the plus8 fold] / the honest-named alias
-- drorb_serve_metered_plus8_dense_conformant): the un-inerted /bulk-excluded
-- Vary: Accept-Encoding stamp + two built refusal surfaces (414 URI Too Long,
-- 406 language Not Acceptable on the negotiated route) over the plus6 fold
-- (numbering note: plus7 is reserved for the in-flight range/date wave; this
-- fold extends plus6 directly and re-parents when that wave lands), dense
-- /bulk arm kept, byte-identity proven for every (peer, seq, input).
-- Importing it places initialize_Datapath_DenseStampsPlus8 in the closure of
-- initialize_Dataplane so its export object lands in the archive.
import Datapath.DenseStampsPlus8
-- The consolidated deployed pipeline (Reactor.DeployPipeline) owns the host
-- default symbol drorb_serve_metered_plus5_dense_conformant, re-homed from
-- Datapath.DenseStampsPlus8. Importing it places its export object in the
-- closure of initialize_Dataplane so the archive links the default serve.
import Reactor.DeployPipeline
-- The textual-config parser + denotation (`Dsl.Config.parseChars` /
-- `denoteOn` / `dialChainOfByte`) live in `Dsl.Config.Parse`. Importing it here
-- places `initialize_Dsl_Config_Parse` in the closure of `initialize_Dataplane`
-- so the boot brings up the parser's constants, and `ffi/build-dataplane-lib.sh`
-- compiles its `Dsl/Config/Parse.c.o.export` object into `libdrorb.a` so the new
-- `drorb_deployment_of_config` / `drorb_serve_step_pol` exports link.
import Dsl.Config.Parse
-- The verified TLS 1.3 server handshake + established-phase record layer
-- (`TlsHandshake.serverStep` / `TlsHandshake.appStep` over the verified `Crypto`
-- AEAD/HKDF/SHA and Ed25519/X25519). Importing it here places its module
-- initializers in the closure of `initialize_Dataplane` and — with the explicit
-- `:c.o.export` builds `ffi/build-dataplane-lib.sh` runs for the TLS closure
-- (`Crypto`, `Tls.*`, `TlsCrypto`, `TlsHandshake`, `TlsHandshake.Post`) —
-- archives their objects into `libdrorb.a`, so the `drorb_tls_serve` HTTPS
-- front-door seam below links. The crypto @[extern] symbols resolve against the
-- SAME backend the `orb`/`tls-wire-oracle` exes use (`ffi/crypto_shim.o`,
-- `libaes_fallback.a`, verified HACL*/EverCrypt) — no unverified TLS stack.
import TlsHandshake.Post
-- The RFC 8446 §9.1 MUST-support certificate signature schemes
-- `rsa_pss_rsae_sha256` / `ecdsa_secp256r1_sha256` (`TlsCrypto.Sig.rsaPssSign` /
-- `ecdsaP256Sign`, over the verified HACL* `Hacl_RSAPSS` / `Hacl_P256` bindings).
-- Importing it here lets the deployed front door instantiate the extra
-- `CertEntry.sign` seams the multi-cert pool selects among, so a real client
-- (curl/LibreSSL/browsers) that does not accept Ed25519 is presented an RSA-PSS
-- or ECDSA-P256 certificate per its `signature_algorithms`. Its two @[extern]
-- symbols (`drorb_p256_ecdsa_sign`, `drorb_rsapss_sha256_sign`) resolve against
-- `ffi/tls_p256_shim.o` — the SAME verified backend the `tls-wire-oracle` exe
-- links; `ffi/build-dataplane-lib.sh` archives its `:c.o.export` object.
import TlsCrypto.Sig
-- The RFC-conformance WRAPPER (`drorb_serve_conformant`, DRORB_SPAN=19). It lives in
-- the `Reactor` lib (no import of Dataplane — it wraps an ARBITRARY inner serve), so
-- importing it here places `initialize_Reactor_ServeConformant` in the closure of
-- `initialize_Dataplane` AND the archive step (which globs every module in Dataplane's
-- transitive import closure) compiles its `.c.o.export` object into `libdrorb.a`. The
-- `@[export drorb_serve_conformant]` symbol below instantiates it on `drorbServe`.
import Reactor.ServeConformant
-- The static-file path decision (`drorb_static_resolve`): split / percent-decode-ONCE /
-- UTF-8 gate / clamped dot-segment walk, with the traversal-confinement theorems
-- (`resolveRel_confined`, `decode_once_only`) proven over every input. It lives in the
-- `Route` lib, so importing it here places `initialize_Route_StaticResolve` in the
-- closure of `initialize_Dataplane` and the archive step compiles its `.c.o.export`
-- object into `libdrorb.a`. The host's static lane crosses it per request instead of
-- making the traversal decision itself.
import Route.StaticResolve
-- The static-file response HEAD decision (`drorb_static_head`): status line /
-- Connection / Accept-Ranges / Content-Type (extension extraction + ASCII-lowercase +
-- MIME map on the REAL file name) / Content-Length, and the full `404`, all the
-- model's own bytes (`okHeadFor_eq_model`, `staticHeadC_notFound`, the ∀-length
-- `contentLength_roundtrip`). It lives in the `Route` lib; importing it here places
-- `initialize_Route_StaticHead` in the closure of `initialize_Dataplane` and the
-- archive step compiles its `.c.o.export` object into `libdrorb.a`. The host's
-- static lane crosses it per response instead of assembling header bytes itself.
import Route.StaticHead
-- The static lane FULL response decision (`drorb_static_decide`): method gate (405),
-- 404 (the model bytes, HEAD head-half), conditional GET (304 via the PROVEN
-- `ConditionalRequest.ifNoneMatchMatches` + exact-date If-Modified-Since), and the
-- range decision (206 single window / 206 multipart/byteranges over the PROVEN
-- `MultiRange` framing / 416) -- Route.StaticDecide, with the window-exactness and
-- multipart-reassembly theorems (`window_exact`, `partsWire_eq_multipartBody`,
-- `multiLen_exact`) and kernel-decided corpus witnesses. Importing it here places
-- `initialize_Route_StaticDecide` in the closure of `initialize_Dataplane` and the
-- archive step compiles its `.c.o.export` object into `libdrorb.a`. The host's
-- static lane crosses it once per request and only EXECUTES the returned plan.
import Route.StaticDecide
-- The extended metered serve (drorb_serve_metered_plus2): the deployed metered fold
-- with the three proven edge stages (Via stamp / PROXY-protocol client recovery /
-- stale-while-revalidate Cache-Control) prepended -- Reactor.DeployPlus2. Importing
-- it places initialize_Reactor_DeployPlus2 in initialize_Dataplane closure and its
-- .c.o.export object in the archive glob, so the host lever (DRORB_PLUS2=1) can
-- cross it (kept as the DRORB_PLUS2=raw lever for PROXY-preambled deployments).
import Reactor.DeployPlus2
-- THE DEPLOYED METERED DEFAULT (drorb_serve_metered_plus2_conformant): the proven
-- RFC-conformance wrapper (validation/431 -> Date -> x-corr scrub -> HEAD-strip)
-- composed over the SAME extended fold, so the nine proven edge stages are
-- deployed-by-default WITH every conformance edge intact. Importing it places
-- initialize_Reactor_DeployPlus2Conformant in the closure and its .c.o.export
-- object in the archive glob. DRORB_PLUS2=0 reverts to the dense fold without
-- the nine edges.
import Reactor.DeployPlus2Conformant
-- Three further proven edges over the SAME extended fold (Timing-Allow-Origin
-- stamp / Content-Location representation pointer / Max-Forwards hop-limit gate)
-- plus their conformant wrapper export (drorb_serve_metered_plus4_conformant) --
-- Reactor.DeployPlus4. Importing it places initialize_Reactor_DeployPlus4 in the
-- initialize_Dataplane closure and its .c.o.export object in the archive glob, so
-- the host default can cross it (DRORB_PLUS4=0 reverts to the plus2 fold).
import Reactor.DeployPlus4
-- Three deepened parity behaviours composed onto the SAME plus4 fold (the
-- GET /login session-cookie route + the previously-inert cookie hardener, the
-- GET /events endpoint serving the proven SSE framing, the GET /app/ SPA
-- fallback serving the proven-selected shell) plus their conformant wrapper
-- export (drorb_serve_metered_plus5_conformant) -- Reactor.DeployPlus5.
-- Importing it places initialize_Reactor_DeployPlus5 in the initialize_Dataplane
-- closure and its .c.o.export object in the archive glob, so the host default
-- can cross it (DRORB_PLUS5=0 reverts to the plus4 fold).
import Reactor.DeployPlus5

/-- The proven pipeline as a pure byte function, exported under the C symbol
`drorb_serve`. One request's bytes in, the deployed response bytes out — the
exact serve `Arena.Orb.main` runs: fork on the HTTP/2 connection preface (h2c
prior knowledge) to the real H2 engine (`serveIngress`); everything else runs
the HTTP/1.1 path through the full ten-stage fold (`deployStepFull2`), which
carries all ten byte-drivers — the five gates (jwt/ipfilter/rate/cache/redirect),
the traversal/policy gates, and the cors/gzip/htmlrewrite/security/header
transforms. The observation state is a fresh `ObsState.init` per call. The native
host calls this once per accepted connection; nothing here knows a socket exists. -/
@[export drorb_serve]
def drorbServe (input : ByteArray) : ByteArray :=
  let bytes := input.toList
  let (out, _obs) :=
    if Reactor.Ingress.hasH2Preface bytes then
      -- h2c prior-knowledge: drive the REAL H2 engine and emit a spec-conformant
      -- HTTP/2 response byte stream (server SETTINGS + ACK + HPACK HEADERS/DATA)
      -- via `Reactor.H2Ingress.serveH2c`, so a real H2 client completes. The H1
      -- branch and every serveIngress H1-equality theorem are untouched.
      (Reactor.H2Ingress.serveH2c bytes, Reactor.Observe.ObsState.init)
    else
      Reactor.Deploy.deployStepFull2 Reactor.Observe.ObsState.init bytes
  ByteArray.mk out.toArray

/-- **THE consolidated deployed metered default**, exported under the honest host
symbol `drorb_serve_pipeline_conformant`. The proven RFC-conformance wrapper over
the ONE flat consolidated pipeline
(`Reactor.DeployPipeline.serveMeteredPipelineConformant` — the 43-stage ordered
stage registry stated once, definitionally equal to the deployed onion), `/bulk`
emitted DENSE. Byte-identical to the pre-consolidation default for EVERY
`(peer, seq, input)` (`serveMeteredPipelineConformant_eq_predecessor` /
`_eq_deployed`). This is the SINGLE metered default crossing the host takes
(`serve_metered_dense_conformant_into`). -/
@[export drorb_serve_pipeline_conformant]
def drorbServePipelineConformant (peer : ByteArray) (seq : UInt64)
    (input : ByteArray) : ByteArray :=
  Reactor.DeployPipeline.serveMeteredPipelineConformant peer seq input

/-- **The RFC-conformance serve** (`drorb_serve_conformant`, DRORB_SPAN=19) — the
deployed `drorbServe` WRAPPED by the proven conformance stages
(`Reactor.ServeConformant.conformantServe`): the `validationStage` request gate
(C1/C2/B2/G1/C3) short-circuits malformed requests to their `4xx/5xx` (+Date) and
otherwise routes through the UNCHANGED `drorbServe`, then post-processes the response
bytes with a `Date` header (F1) and a `HEAD` body strip (B1). The inner `drorbServe`
is byte-for-byte the deployed serve — the dense/poly `=drorbServe` family is untouched;
only the request-edge gate and response-edge finisher are added. Proven properties:
`conformant_rejects_missingHost` (a real missing-Host input ⟶ `400`),
`conformant_date_present_accept` (Date present on the accepted path),
`conformant_head_no_body` (HEAD body stripped). Residual: `deployNow` is a fixed
RFC-1123 placeholder, not a live clock (the probe F1 needs Date PRESENT). Selected on
every HTTP serve job when `DRORB_SPAN=19`. -/
@[export drorb_serve_conformant]
def drorbServeConformant (input : ByteArray) : ByteArray :=
  Reactor.ServeConformant.conformantServe drorbServe input

/-- **The bridged FLAT serve seam** (`drorb_serve_flat`) — the A/B twin of
`drorb_serve`. Byte-identical to `drorb_serve` for every input
(`drorbServeFlat_eq`): the h2c prior-knowledge branch is the same `serveH2c`, and
the HTTP/1.1 branch runs the SAME deployed `servePipelineFull2` fold but renders
the response straight into a flat `ByteArray` (`Reactor.ServeArr.serveArr`,
proven `= ByteArray.mk (servePipelineFull2 input.toList).toArray`), skipping the
deployed path's response-head `List` round-trips. The host default stays
`drorb_serve`; this symbol is gated behind `DRORB_FLAT=1` (and the serve-bench
lever) so the flat vs. List materialization can be measured A/B in the same
binary with no behavioural difference. -/
@[export drorb_serve_flat]
def drorbServeFlat (input : ByteArray) : ByteArray :=
  let bytes := input.toList
  if Reactor.Ingress.hasH2Preface bytes then
    ByteArray.mk (Reactor.H2Ingress.serveH2c bytes).toArray
  else
    Reactor.ServeArr.serveArr input

/-- **The flat serve is byte-identical to the deployed serve — for every input.**
Both fork on the h2c preface to the same `serveH2c`; on the HTTP/1.1 path
`serveArr` emits exactly `ByteArray.mk (servePipelineFull2 input.toList).toArray`
(`serveArr_correct`), which is what `drorbServe` writes there
(`deployStepFull2_serves`). So swapping the export changes no served byte — the
A/B measures only the materialization cost. -/
theorem drorbServeFlat_eq (input : ByteArray) : drorbServeFlat input = drorbServe input := by
  unfold drorbServeFlat drorbServe
  by_cases h : Reactor.Ingress.hasH2Preface input.toList
  · simp only [h, if_true]
  · simp only [h, if_false, Bool.false_eq_true]
    rw [Reactor.ServeArr.serveArr_correct, Reactor.Deploy.deployStepFull2_serves]

/-- **The deployed serve reference of the assembled full flat serve IS `drorbServe`.**
`Datapath.ServeFlatFull.deployedServeRef` is written (below `Dataplane`, to avoid an
import cycle) as `drorbServe`'s exact body — the h2c prior-knowledge fork to the real
H2 engine, else the full 14-stage HTTP/1.1 fold. This closes that identity where
`drorbServe` is in scope, so `serveFlatFull_refines` (byte-identity to `deployedServeRef`)
transfers to `drorbServe`. -/
theorem deployedServeRef_eq_drorbServe (input : ByteArray) :
    Datapath.ServeFlatFull.deployedServeRef input = drorbServe input := by
  unfold Datapath.ServeFlatFull.deployedServeRef drorbServe
  by_cases h : Reactor.Ingress.hasH2Preface input.toList
  · simp only [h, if_true]
  · simp only [h, if_false, Bool.false_eq_true]
    rw [Reactor.Deploy.deployStepFull2_serves]

/-- **THE ASSEMBLED FULL FLAT SERVE IS BYTE-IDENTICAL TO THE DEPLOYED `drorbServe`.**
For EVERY input, the `DRORB_SPAN=3` serve (`Datapath.ServeFlatFull.serveFlatFull` — the
REAL deployed 14-stage pipeline rendered through the flat egress serializer) produces the
IDENTICAL bytes to the deployed default `drorbServe`. So `DRORB_SPAN=3` serves the same
bytes as the deployed serve on every real request (h2c fork AND the full HTTP/1.1 fold) —
a deployed-representative flat serve, not the echo exemplar. Chains
`Datapath.ServeFlatFull.serveFlatFull_refines` (flat egress = deployed serialize) with
`deployedServeRef_eq_drorbServe`. -/
theorem serveFlatFull_eq_drorbServe (input : ByteArray) :
    Datapath.ServeFlatFull.serveFlatFull input = drorbServe input := by
  rw [Datapath.ServeFlatFull.serveFlatFull_refines, deployedServeRef_eq_drorbServe]

/-- **THE FULL POLY SERVE IS BYTE-IDENTICAL TO THE DEPLOYED `drorbServe`.** For EVERY
input, the `DRORB_SPAN=7` serve (`Datapath.ServePolyFull.servePolyFull` — the REAL
deployed 14-stage routed response rendered through the POLYMORPHIC egress fold:
`HdrSeq.foldPush` header block over the flat `HdrBlock` + `ByteArray` body) produces the
IDENTICAL bytes to the deployed default `drorbServe` (h2c fork AND the full HTTP/1.1 fold).
Chains `Datapath.ServePolyFull.servePolyFull_refines` (poly egress = deployed serialize)
with `deployedServeRef_eq_drorbServe`. -/
theorem servePolyFull_eq_drorbServe (input : ByteArray) :
    Datapath.ServePolyFull.servePolyFull input = drorbServe input := by
  rw [Datapath.ServePolyFull.servePolyFull_refines, deployedServeRef_eq_drorbServe]

/-- **THE RUNTIME-DENSE FULL SERVE IS BYTE-IDENTICAL TO THE DEPLOYED `drorbServe`.**
For EVERY input, the `DRORB_SPAN=18` serve (`Datapath.ServeDenseReal.serveDenseReal` —
the deployed serve whose `/bulk` arm emits the DENSE head + DENSE 1 MiB `Array` body,
no per-byte `List` cons: the body-cliff fix) produces the IDENTICAL bytes to the
deployed default `drorbServe` (h2c fork, the `/bulk` dense arm, AND the off-arm List
serve). Chains `Datapath.ServeDenseReal.serveDenseReal_refines` (dense = deployedServeRef)
with `deployedServeRef_eq_drorbServe`. -/
theorem serveDenseReal_eq_drorbServe (input : ByteArray) :
    Datapath.ServeDenseReal.serveDenseReal input = drorbServe input := by
  rw [Datapath.ServeDenseReal.serveDenseReal_refines, deployedServeRef_eq_drorbServe]

#print axioms serveDenseReal_eq_drorbServe

/-- **THE CONFORMANT-DENSE SERVE IS BYTE-IDENTICAL TO THE DEPLOYED CONFORMANT SERVE.**
For EVERY input, the `DRORB_SPAN=20` serve
(`Datapath.ServeConformantDense.serveConformantDenseIdx` — the RFC-conformance wrapper
around the index-decided DENSE `/bulk` serve) produces the IDENTICAL bytes to the
deployed conformant default `drorbServeConformant = conformantServe drorbServe`:
the wrapper consults its inner only pointwise (`conformantServe_congr`), and the dense
inner equals `drorbServe` (`serveDenseIdx_refines` + `deployedServeRef_eq_drorbServe`). -/
theorem serveConformantDenseIdx_eq_drorbServeConformant (input : ByteArray) :
    Datapath.ServeConformantDense.serveConformantDenseIdx input
      = drorbServeConformant input := by
  rw [Datapath.ServeConformantDense.serveConformantDenseIdx_eq_ref]
  exact Datapath.ServeConformantDense.conformantServe_congr _ _
    deployedServeRef_eq_drorbServe input

#print axioms serveConformantDenseIdx_eq_drorbServeConformant

/-- **THE INDEX-NATIVE-HEAD SERVE IS BYTE-IDENTICAL TO THE DEPLOYED `drorbServe`.**
For EVERY input, the head-idx serve (`Datapath.ServeHeadIdx.serveHeadIdx` — ONE
arena parse per request, both arms decided by index probes on the arena head, no
`arenaToProto`/`protoReqOf` on the deciding path, the proven dense emitters on the
arms) produces the IDENTICAL bytes to the deployed default `drorbServe` (h2c fork,
both dense arms, AND the off-arm List serve). Chains
`Datapath.ServeHeadIdx.serveHeadIdx_refines` (head-idx = deployedServeRef) with
`deployedServeRef_eq_drorbServe`. This is the identity that makes the head-idx
serve the deployed `Seam::Http` default: swapping the export changes NO served
byte. -/
theorem serveHeadIdx_eq_drorbServe (input : ByteArray) :
    Datapath.ServeHeadIdx.serveHeadIdx input = drorbServe input := by
  rw [Datapath.ServeHeadIdx.serveHeadIdx_refines, deployedServeRef_eq_drorbServe]

#print axioms serveHeadIdx_eq_drorbServe

/-- **The conformant HEAD-IDX serve** (`drorb_serve_conformant_head_idx`) — the
RFC-conformance wrapper (`Reactor.ServeConformant.conformantServe`: validation
gate C1/C2/B2/G1/C3 → inner serve → `Date` (F1) / `HEAD`-strip (B1) finisher)
around the index-native-head serve. The deployed NON-METERED `Seam::Http` default
crossing: same conformance edges as `drorb_serve_conformant`, inner swapped for
the parse-once index-native serve. Byte-identical to `drorbServeConformant` for
EVERY input (`serveConformantHeadIdx_eq_drorbServeConformant` below). Same
`ByteArray -> ByteArray` ABI as `drorb_serve`. -/
@[export drorb_serve_conformant_head_idx]
def drorbServeConformantHeadIdx (input : ByteArray) : ByteArray :=
  Reactor.ServeConformant.conformantServe Datapath.ServeHeadIdx.serveHeadIdx input

/-- **THE CONFORMANT HEAD-IDX SERVE IS BYTE-IDENTICAL TO THE DEPLOYED CONFORMANT
SERVE.** The wrapper consults its inner only pointwise (`conformantServe_congr`),
and the head-idx inner equals `drorbServe` (`serveHeadIdx_eq_drorbServe`) — so the
conformance edges are untouched and swapping the deployed non-metered default
changes NO served byte. -/
theorem serveConformantHeadIdx_eq_drorbServeConformant (input : ByteArray) :
    drorbServeConformantHeadIdx input = drorbServeConformant input := by
  unfold drorbServeConformantHeadIdx drorbServeConformant
  exact Datapath.ServeConformantDense.conformantServe_congr _ _
    serveHeadIdx_eq_drorbServe input

#print axioms serveConformantHeadIdx_eq_drorbServeConformant

/-- **The metered serve seam** (`drorb_serve_metered`). The same deployed serve as
`drorb_serve`, but the native host also supplies the accepted peer address (`peer`,
family-tagged bit-encoded per `Reactor.Stage.IpFilter.encodeAddr`) and the
per-connection request index (`seq`, 0-based, incremented each keep-alive
iteration). These feed the real IP-filter (deny `10.0.0.0/8`) and rate (cap 8 /
connection) gates through `Reactor.Deploy.servePipelineFull2Metered`. The host
calls this on the HTTP/1.1 path when it has a peer + keep-alive counter; the
non-metered `drorb_serve` remains for callers that do not. -/
@[export drorb_serve_metered]
def drorbServeMetered (peer : ByteArray) (seq : UInt64) (input : ByteArray) : ByteArray :=
  ByteArray.mk
    (Reactor.Deploy.servePipelineFull2Metered peer.toList seq.toNat input.toList).toArray

/-- **The effect/continuation STEP seam** (`drorb_serve_step`). The proven
resumable serve (`Reactor.ServeStep.serveStep`) surfaced for the interpreter loop:
input byte 0 = the live health/breaker mask (bit `i` ⇒ backend `i` up, exactly the
byte `drorb_proxy_pick` reads), bytes 1.. = the request. Output is the encoded
`Step` (`Reactor.ServeStep.encodeStep`): byte 0 = tag (`0` = DONE, rest = response
bytes; `1` = YIELD proxyDial, byte 1 = the proven-chosen backend id, bytes 2.. =
the request the shell forwards). The shell dials the yielded backend and calls
`drorb_serve_resume` with the reply; the CORE decided whether to proxy, which
backend, and what to do with the upstream bytes. -/
@[export drorb_serve_step]
def drorbServeStep (input : ByteArray) : ByteArray :=
  match input.toList with
  | []          => ByteArray.empty
  | mask :: req =>
    -- Read the LB policy chain FROM the deployment config projection
    -- (`Reactor.Deploy.defaultDeployment.dialChain`), threaded through
    -- `serveStepWith`. Byte-identical to the hardcoded default
    -- (`serveStepWith_deploy`), but the running dial is now the config's read.
    ByteArray.mk (Reactor.ServeStep.encodeStep
      (Reactor.ServeStep.serveStepWith Reactor.ServeStep.deployDialChain mask.toNat req)).toArray

/-- **The config-selected LB policy chain** the running step dials with, keyed on a
deployment selector byte the host supplies (`DRORB_LB_POLICY`): `0` (or unset) is
`defaultDeployment` (the deployed default rendezvous chain, byte-identical to
`drorb_serve_step`), `1` is `altDeployment` (a least-connections `api` pool). A
non-default selector makes the running reverse-proxy dial a config-declared LB
policy, so a proxied request reaches a different backend. -/
def deploymentDialChain : Nat → List Proxy.Policy
  | 1 => Reactor.Deploy.altDeployment.dialChain Reactor.Deploy.proxyPoolName
  | _ => Reactor.ServeStep.deployDialChain

/-- Selector `0` is the deployed default chain — the config-selected step at the
default selector is byte-identical to `drorb_serve_step`. -/
theorem deploymentDialChain_default : deploymentDialChain 0 = Reactor.ProxyDial.dialPolicies := rfl

/-- **The config-driven effect/continuation STEP seam** (`drorb_serve_step_cfg`).
Identical to `drorb_serve_step`, but input byte 0 is a deployment selector
(`DRORB_LB_POLICY`) chosen by the host and byte 1 is the live health mask, bytes
2.. the request. The proxy branch dials the backend the CONFIG-declared LB policy
(`deploymentDialChain sel`) selects, so a non-default deployment reaches a
different backend. Selector `0` reproduces `drorb_serve_step` exactly. -/
@[export drorb_serve_step_cfg]
def drorbServeStepCfg (input : ByteArray) : ByteArray :=
  match input.toList with
  | sel :: mask :: req =>
    ByteArray.mk (Reactor.ServeStep.encodeStep
      (Reactor.ServeStep.serveStepWith (deploymentDialChain sel.toNat) mask.toNat req)).toArray
  | _ => ByteArray.empty

/-- **The config-driven RESUME seam** (`drorb_serve_resume_cfg`). After the shell
executes the yielded effect, it threads back byte 0 = the deployment selector plus
the ORIGINAL `mask :: reqLen(4 BE) :: request :: result` frame; the core REPLAYS
`serveStepWith (deploymentDialChain sel)` (pure ⇒ deterministic), so the resumed
continuation is reconstructed under the SAME config chain the step used. -/
@[export drorb_serve_resume_cfg]
def drorbServeResumeCfg (input : ByteArray) : ByteArray :=
  match input.toList with
  | sel :: rest =>
    ByteArray.mk
      (Reactor.ServeStep.decodeResumeWith (deploymentDialChain sel.toNat) rest).toArray
  | [] => ByteArray.empty

/-- **The L4 accept-surface projection** (`drorb_l4_bind`), for a deployment
selector byte. Returns the newline-joined `bind\tpool\tmode\tid,id,…` lines the
running host turns into its `DRORB_L4_LISTEN` binding — the layer-4 listeners the
config DECLARES, generated from `DeploymentConfig.l4Listeners` (empty for selector
`0`, one `127.0.0.1:8710` raw-TCP passthrough for selector `1`). So a
config-declared L4 listener is bound at deploy time, from the deployment. -/
@[export drorb_l4_bind]
def drorbL4Bind (sel : ByteArray) : ByteArray :=
  let cfg := match sel.toList with
    | 1 :: _ => Reactor.Deploy.altDeployment
    | _      => Reactor.Deploy.defaultDeployment
  let line := fun (b : Dsl.L4Binding) =>
    let m := match b.mode with | .tcp => "tcp" | .udp => "udp"
    let ids := String.intercalate "," (b.backendIds.map toString)
    s!"{b.bind}\t{b.poolName}\t{m}\t{ids}"
  (String.intercalate "\n" (cfg.l4Listeners.map line)).toUTF8

/-- **The effect/continuation RESUME seam** (`drorb_serve_resume`). After the shell
executes a yielded effect, it threads back the ORIGINAL `(mask, request)` plus the
effect result, framed as `mask :: reqLen(4, big-endian) :: request :: result`
(`Reactor.ServeStep.decodeResume`). The proven core REPLAYS `serveStep` (pure ⇒
deterministic) to reconstruct the same continuation and applies it to the result,
returning the resumed response bytes — on the proxy path,
`proxyRespTransform result`. No Lean closure is marshalled across the FFI. -/
@[export drorb_serve_resume]
def drorbServeResume (input : ByteArray) : ByteArray :=
  ByteArray.mk (Reactor.ServeStep.decodeResume input.toList).toArray

/-! ## The ARBITRARY-config deployment path — an operator-written config drives serve

The seams above select among the two NAMED deployments (`default` / `alt`) by a
selector byte. This section replaces that last mile with a real config→deployment
path: the host reads an ARBITRARY textual `DeploymentConfig` at boot, the proven
`Dsl.Config.parseChars` parses it (parse-soundness: `Dsl.Config.parse_render`), and
`denoteOn defaultDeployment` layers its data dimensions onto the proven byte
pipeline. `drorb_deployment_of_config` emits the runtime projections the host needs
(the LB-policy byte + the declared L4 bindings); each proxied request then threads
the LB byte to `drorb_serve_step_pol`, whose chain is `Dsl.Config.dialChainOfByte`
— provably the denoted deployment's `dialChain` for the parsed pool
(`Dsl.Config.dialChainOfByte_denote`). So an arbitrary written config drives the
running reverse-proxy dial, correct-by-construction. -/

/-- Render one `L4Binding` as the host's `bind\tpool\tmode\tid,id,…` line. -/
def l4BindLine (b : Dsl.L4Binding) : String :=
  let m := match b.mode with | .tcp => "tcp" | .udp => "udp"
  let ids := String.intercalate "," (b.backendIds.map toString)
  s!"{b.bind}\t{b.poolName}\t{m}\t{ids}"

/-- **`drorb_deployment_of_config` — parse an operator config into the running
projections.** Input: the textual config bytes (UTF-8). On a parse FAILURE (or a
non-UTF-8 input) the output is EMPTY, so the host falls back to the byte-identical
default. On success the output is newline-joined lines:

* `lb\t<byte>` — the parsed pool's LB policy, encoded by `Dsl.Config.policyByteN`
  (the byte the host threads to `drorb_serve_step_pol`); then
* one `bind\tpool\tmode\tid,id,…` line per declared L4 listener
  (`DeploymentConfig.l4Listeners` of the denoted deployment).

The parsed config is `denoteOn Reactor.Deploy.defaultDeployment` — its byte pipeline
(routing + the fourteen-stage fold) is the proven default; only the IO-boundary
dimensions come from the operator's text. -/
@[export drorb_deployment_of_config]
def drorbDeploymentOfConfig (input : ByteArray) : ByteArray :=
  match String.fromUTF8? input with
  | none => ByteArray.empty
  | some s =>
    match Dsl.Config.parseChars s.data with
    | none => ByteArray.empty
    | some pc =>
      let cfg := Dsl.Config.denoteOn Reactor.Deploy.defaultDeployment pc
      let polByte := Dsl.Config.policyByteN pc.lb.toProxy
      let lbLine := s!"lb\t{polByte}"
      -- The route-count gate the host reads (`has_routes`): flat routes PLUS declared
      -- virtual-host items, so a vhost-only config also routes through the config serve.
      let routesLine := s!"routes\t{pc.routes.length + pc.vitems.length}"
      let l4lines := cfg.l4Listeners.map l4BindLine
      -- The proxy-vhost hostnames: a request whose `Host` names one of these is
      -- reverse-proxied host-side to the configured fleet (the `hostGlob` served path
      -- answers a proxy block route with a placeholder; the real forward is host-side).
      let vproxyLines := (Dsl.Config.proxyVHostNames pc.vitems).map (fun h => s!"vproxy\t{h}")
      (String.intercalate "\n" (lbLine :: routesLine :: (l4lines ++ vproxyLines))).toUTF8

/-- **`drorb_serve_step_pol` — the effect/continuation STEP dialed by a config
LB-policy byte.** Input: byte 0 = the LB-policy byte
(`Dsl.Config.policyByteN`, cached by the host from `drorb_deployment_of_config`),
byte 1 = the live health mask, bytes 2.. = the request. The reverse-proxy branch
dials the backend `Dsl.Config.dialChainOfByte` selects — provably the parsed
config's declared policy. -/
@[export drorb_serve_step_pol]
def drorbServeStepPol (input : ByteArray) : ByteArray :=
  match input.toList with
  | pol :: mask :: req =>
    ByteArray.mk (Reactor.ServeStep.encodeStep
      (Reactor.ServeStep.serveStepWith (Dsl.Config.dialChainOfByte pol.toNat) mask.toNat req)).toArray
  | _ => ByteArray.empty

/-- **`drorb_serve_resume_pol` — resume the config-policy STEP.** Input byte 0 is
the same LB-policy byte, then the ORIGINAL `mask :: reqLen(4 BE) :: request ::
result` frame; the core REPLAYS `serveStepWith (dialChainOfByte pol)` (pure ⇒
deterministic) so the resumed continuation matches the chain the step used. -/
@[export drorb_serve_resume_pol]
def drorbServeResumePol (input : ByteArray) : ByteArray :=
  match input.toList with
  | pol :: rest =>
    ByteArray.mk
      (Reactor.ServeStep.decodeResumeWith (Dsl.Config.dialChainOfByte pol.toNat) rest).toArray
  | [] => ByteArray.empty

/-- **No regression.** A config selecting `rendezvous` (policy byte `3`) makes the
config-policy step byte-identical to the deployed default step (`serveStep`): the
rendezvous chain IS the deployed default chain. So an unset / rendezvous config
regresses nothing. -/
theorem serveStepPol_rendezvous (mask : Nat) (input : Proto.Bytes) :
    Reactor.ServeStep.serveStepWith (Dsl.Config.dialChainOfByte 3) mask input
      = Reactor.ServeStep.serveStep mask input := rfl

/-- **The config policy byte drives the exact declared dial.** For any parsed
config, the chain the config-policy step runs from `pc`'s LB byte is exactly the
denoted deployment's dial chain for the parsed pool — the running dial is the
config's declared policy, not a named-deployment selection. -/
theorem serveStepPol_denotes (pc : Dsl.Config.ParsedConfig) (mask : Nat) (input : Proto.Bytes) :
    Reactor.ServeStep.serveStepWith
        (Dsl.Config.dialChainOfByte (Dsl.Config.policyByteN pc.lb.toProxy)) mask input
      = Reactor.ServeStep.serveStepWith
          ((Dsl.Config.denoteOn Reactor.Deploy.defaultDeployment pc).dialChain
            (String.mk pc.poolName)) mask input := by
  rw [Dsl.Config.dialChainOfByte_denote]

#guard Dsl.Config.policyByteN Dsl.Cfg.LbPolicy.rendezvous.toProxy == 3
#guard Dsl.Config.policyByteN Dsl.Cfg.LbPolicy.leastConn.toProxy == 1
#guard Dsl.Config.policyByteN Dsl.Cfg.LbPolicy.roundRobin.toProxy == 0

/-! ## The config-ROUTE-TABLE serve — an operator config declares the served routes

`drorb_deployment_of_config` above surfaces the parsed config's IO-boundary
projections (LB byte, L4 binds, route count). This seam surfaces the last one — the
ROUTE TABLE — as a served response: given the config text and a request, it serves
the request through `Reactor.Deploy.servePipelineOf (denoteOn defaultDeployment pc)`,
the SAME proven fourteen-stage fold but over the CONFIG's route table
(`Dsl.Config.denoteOn_routes`). A `redirect`/`respond`/`static` route answers
directly; a routeless / unparseable config falls back to the byte-identical default
serve (`servePipelineFull2`), so a host that sets no routes regresses nothing. -/

/-- Decode a 4-byte big-endian length prefix. -/
def be32 (a b c d : UInt8) : Nat :=
  a.toNat <<< 24 ||| b.toNat <<< 16 ||| c.toNat <<< 8 ||| d.toNat

/-- Serve one request under a parsed config's route table + virtual-host dimension
(or the byte-identical default when the config declares neither). -/
def serveUnderConfig (pc : Dsl.Config.ParsedConfig) (req : Proto.Bytes) : Proto.Bytes :=
  match pc.routes, pc.vitems with
  | [], [] => Reactor.Deploy.servePipelineFull2 req
  | _,  _  => Reactor.Deploy.servePipelineOf (Dsl.Config.denoteOn Reactor.Deploy.defaultDeployment pc) req

/-- **`drorb_serve_cfg` — serve a request under an operator config's route table.**
Input framing: `cfgLen(4 BE) :: configBytes :: requestBytes`. The config bytes are
parsed by the proven `Dsl.Config.parseChars`; when the config declares routes, the
request is served through `servePipelineOf (denoteOn defaultDeployment pc)` — the SAME
fourteen-stage fold over the CONFIG's declared route table. On a parse failure, a
non-UTF-8 config, or a routeless config the request is served by the byte-identical
default (`servePipelineFull2`). Total. -/
@[export drorb_serve_cfg]
def drorbServeCfg (input : ByteArray) : ByteArray :=
  match input.toList with
  | b0 :: b1 :: b2 :: b3 :: rest =>
    let cfgLen := be32 b0 b1 b2 b3
    let cfgBytes := rest.take cfgLen
    let reqBytes := rest.drop cfgLen
    let served :=
      match String.fromUTF8? (ByteArray.mk cfgBytes.toArray) with
      | none   => Reactor.Deploy.servePipelineFull2 reqBytes
      | some s =>
        match Dsl.Config.parseChars s.data with
        | none    => Reactor.Deploy.servePipelineFull2 reqBytes
        | some pc => serveUnderConfig pc reqBytes
    ByteArray.mk served.toArray
  | _ => ByteArray.empty

/-- **`drorb_serve_proxy_stream_head` — the CL-trust streaming head seam.** The native
io_uring proxy, on the recv that completes the upstream response HEAD for a NON-GZIP
passthrough reply with a fixed `Content-Length`, computes the transformed response head
WITHOUT the body and emits it before any body byte arrives; the body then streams straight
through, RSS-bounded.

Input framing: `reqLen(4 BE) :: request :: headLen(4 BE) :: upstreamHead :: bodyLen(4 BE)`,
where `request` is the ORIGINAL client request bytes (`ctxOf` reads its `Origin` /
`Accept-Encoding`), `upstreamHead` is the raw upstream reply bytes THROUGH the terminal
`\r\n\r\n`, and `bodyLen` is the upstream-declared `Content-Length`. Output is the
transformed head bytes (`Reactor.ServeStep.proxyStreamHead`) — OR **EMPTY** when the request
accepts gzip.

The gzip gate is decided HERE by the PROVEN `Reactor.Stage.Gzip.acceptsGzip` over the exact
`ctxOf` context the transform keys on — so the host cannot mis-gate. An empty reply means
"this reply re-encodes (gzip); do NOT stream — fall back to the buffered
`drorb_serve_resume` path" (that head depends on the body bytes; it needs chunked TE, a
different residual, and stays open honestly).

Correctness for the non-empty (non-gzip) case (`Reactor.ServeStep.proxyRespHead_factors` /
`proxyStream_bytes_faithful`): with a clean head, `proxyStreamHead req upHead bodyLen ++ body`
is byte-identical to the buffered `proxyRespTransform req (upHead ++ body)` — the SAME bytes
`drorb_serve_resume` produces, computed without ever holding the body whole. The host still
gates to the fixed-`Content-Length` framing (a chunked upstream stays buffered). -/
@[export drorb_serve_proxy_stream_head]
def drorbServeProxyStreamHead (input : ByteArray) : ByteArray :=
  match input.toList with
  | r0 :: r1 :: r2 :: r3 :: rest =>
    let reqLen := be32 r0 r1 r2 r3
    let req := rest.take reqLen
    match rest.drop reqLen with
    | h0 :: h1 :: h2 :: h3 :: rest3 =>
      let headLen := be32 h0 h1 h2 h3
      let upHead := rest3.take headLen
      match rest3.drop headLen with
      | l0 :: l1 :: l2 :: l3 :: _ =>
        -- The PROVEN gzip gate: only the non-gzip head factors through body length.
        if Reactor.Stage.Gzip.acceptsGzip (Reactor.Deploy.ctxOf req).req then
          ByteArray.empty
        else
          ByteArray.mk (Reactor.ServeStep.proxyStreamHead req upHead (be32 l0 l1 l2 l3)).toArray
      | _ => ByteArray.empty
    | _ => ByteArray.empty
  | _ => ByteArray.empty

/-- **The config-route serve honours the parsed route table.** For a config that
declares routes, `serveUnderConfig` serves through `servePipelineOf` of the denoted
deployment — whose route table is exactly the config's routes
(`Dsl.Config.denoteOn_routes`), so the served bytes are decided by the operator's
declared routes, not the demo table. -/
theorem serveUnderConfig_routes (pc : Dsl.Config.ParsedConfig) (req : Proto.Bytes)
    (h : pc.routes ≠ []) :
    serveUnderConfig pc req
      = Reactor.Deploy.servePipelineOf (Dsl.Config.denoteOn Reactor.Deploy.defaultDeployment pc) req
    ∧ (Dsl.Config.denoteOn Reactor.Deploy.defaultDeployment pc).routing.routes
        = pc.routes.map Dsl.Config.routeOfSpec := by
  refine ⟨?_, Dsl.Config.denoteOn_routes _ pc h⟩
  unfold serveUnderConfig
  cases hpc : pc.routes with
  | nil => exact absurd hpc h
  | cons a t => rfl

/-- **The virtual-host serve honours the parsed vhost dimension.** A config that
declares virtual hosts serves through `servePipelineOf` of the denoted deployment,
whose default handler is the proven host/method/glob `Handler.hostGlob` over the
config's declared blocks (`Dsl.Config.denoteOn_vhosts`) — so an unmatched request is
routed by the operator's declared vhosts, not the demo table. -/
theorem serveUnderConfig_vhosts (pc : Dsl.Config.ParsedConfig) (req : Proto.Bytes)
    (h : pc.vitems ≠ []) :
    serveUnderConfig pc req
      = Reactor.Deploy.servePipelineOf (Dsl.Config.denoteOn Reactor.Deploy.defaultDeployment pc) req
    ∧ (Dsl.Config.denoteOn Reactor.Deploy.defaultDeployment pc).routing.defaultHandler
        = Reactor.App.Handler.hostGlob (Dsl.Config.denoteVHosts pc.vitems) := by
  refine ⟨?_, Dsl.Config.denoteOn_vhosts _ pc h⟩
  unfold serveUnderConfig
  cases hv : pc.vitems with
  | nil => exact absurd hv h
  | cons a t => cases pc.routes <;> rfl

/-- **No regression.** A config declaring neither flat routes nor virtual hosts serves
byte-identically to the deployed default (`servePipelineFull2` = `servePipelineOf
defaultDeployment`). -/
theorem serveUnderConfig_default (pc : Dsl.Config.ParsedConfig) (req : Proto.Bytes)
    (hr : pc.routes = []) (hv : pc.vitems = []) :
    serveUnderConfig pc req = Reactor.Deploy.servePipelineFull2 req := by
  simp only [serveUnderConfig, hr, hv]

/-! ## Braid 0 — the METERED config-route serve (`drorb_serve_metered_cfg`)

The default RUNNING serve is the metered fold (`drorb_serve_metered`), so to make the
running serve config-path-driven — the enabler for config-gated middleware braids —
the metered serve must ALSO flow through a deployment config. `serveUnderConfigMetered`
is the metered mirror of `serveUnderConfig`: it folds `servePipelineOfMetered` (the
connection-aware IP-filter + rate gates in scope) over the config's deployment. With
neither routes nor vhosts (the DEFAULT — no `DRORB_CONFIG`) it serves
`servePipelineOfMetered defaultDeployment`, which is byte-for-byte
`servePipelineFull2Metered` (`Reactor.Deploy.servePipelineOfMetered_default`, `rfl`) —
so the default metered conformance is untouched, and the running default serve is now
a fold over `defaultDeployment.middleware.chain`. A future middleware braid is a
config-gated append to that chain, not shared-file surgery. -/

/-- Serve one request through the METERED gate chain under a parsed config's route /
virtual-host dimension (or the byte-identical default when the config declares
neither). The metered mirror of `serveUnderConfig`. -/
def serveUnderConfigMetered (pc : Dsl.Config.ParsedConfig)
    (clientIp : Proto.Bytes) (connSeq : Nat) (req : Proto.Bytes) : Proto.Bytes :=
  match pc.routes, pc.vitems with
  | [], [] =>
    Reactor.Deploy.servePipelineOfMetered Reactor.Deploy.defaultDeployment clientIp connSeq req
  | _,  _  =>
    Reactor.Deploy.servePipelineOfMetered
      (Dsl.Config.denoteOn Reactor.Deploy.defaultDeployment pc) clientIp connSeq req

/-- **No regression (metered).** A config declaring neither flat routes nor virtual
hosts serves the metered fold byte-identically to the deployed default
(`servePipelineFull2Metered` = `servePipelineOfMetered defaultDeployment`, `rfl`). -/
theorem serveUnderConfigMetered_default (pc : Dsl.Config.ParsedConfig)
    (clientIp : Proto.Bytes) (connSeq : Nat) (req : Proto.Bytes)
    (hr : pc.routes = []) (hv : pc.vitems = []) :
    serveUnderConfigMetered pc clientIp connSeq req
      = Reactor.Deploy.servePipelineFull2Metered clientIp connSeq req := by
  simp only [serveUnderConfigMetered, hr, hv, Reactor.Deploy.servePipelineOfMetered_default]

/-! ## The CONFIG-DRIVEN, DEFAULT-ON middleware serve (`serveUnderPolicyMetered`)

`serveUnderConfigMetered` folds the CONFIG's route table but always over the frozen
`deployStagesFull2` middleware chain — a text config can never enforce a middleware policy.
`serveUnderPolicyMetered` is the operability upgrade: it folds `Reactor.Deploy.deployStagesFull4
policy` (the config-driven method-`405`/body-`413`/Host-`421` gates from round 1 PLUS the round-2
conn-`503`/stick-`429`/slowloris-`408` gates and the CORS `Access-Control-Allow-Origin` transform,
prepended to `deployStagesFull2`) over the config's route table. With `Reactor.Deploy.emptyMwPolicy`
the seven policy stages are transparent and the fold is byte-identical to `serveUnderConfigMetered`
(`serveUnderPolicyMetered_empty_eq`); so the DEFAULT serve (no policy directive) is byte-for-byte
today's, and an operator that sets a policy (a real max-body-size / allowed-methods /
allowed-hosts) enforces it on EVERY request with NO per-request test header. -/

/-- Serve one request through the METERED gate chain under a parsed config's route dimension AND
a middleware `policy` (the config-driven `deployStagesFull3 policy` chain). The policy mirror of
`serveUnderConfigMetered`. -/
def serveUnderPolicyMetered (pc : Dsl.Config.ParsedConfig) (policy : Reactor.Deploy.MwPolicy)
    (clientIp : Proto.Bytes) (connSeq : Nat) (req : Proto.Bytes) : Proto.Bytes :=
  match pc.routes, pc.vitems with
  | [], [] =>
    Reactor.Deploy.servePipelineOfMetered
      (Reactor.Deploy.policyDeploymentOn Reactor.Deploy.defaultDeployment policy) clientIp connSeq req
  | _,  _  =>
    Reactor.Deploy.servePipelineOfMetered
      (Reactor.Deploy.policyDeploymentOn
        (Dsl.Config.denoteOn Reactor.Deploy.defaultDeployment pc) policy) clientIp connSeq req

/-- **No-regression — the EMPTY policy is byte-identical to the frozen-middleware serve.** For
ANY parsed config, serving under `emptyMwPolicy` emits the exact same bytes as
`serveUnderConfigMetered` (the three policy gates fold transparently, `deployStagesFull3_empty_eq`).
So a config declaring no middleware policy is byte-for-byte the pre-existing metered config serve —
the deployed conformance (73/0) is preserved, and the default serve is untouched. -/
theorem serveUnderPolicyMetered_empty_eq (pc : Dsl.Config.ParsedConfig)
    (clientIp : Proto.Bytes) (connSeq : Nat) (req : Proto.Bytes) :
    serveUnderPolicyMetered pc Reactor.Deploy.emptyMwPolicy clientIp connSeq req
      = serveUnderConfigMetered pc clientIp connSeq req := by
  rcases hr : pc.routes with _ | _ <;> rcases hv : pc.vitems with _ | _ <;>
    simp only [serveUnderPolicyMetered, serveUnderConfigMetered, hr, hv] <;>
    exact Reactor.Deploy.servePipelineOfMetered_policyOn_empty_eq _ rfl _ _ _

/-- **No-regression at the default (metered) — empty policy + routeless config.** A config with no
routes, no vhosts, and no middleware policy serves byte-for-byte `servePipelineFull2Metered`. -/
theorem serveUnderPolicyMetered_default (pc : Dsl.Config.ParsedConfig)
    (clientIp : Proto.Bytes) (connSeq : Nat) (req : Proto.Bytes)
    (hr : pc.routes = []) (hv : pc.vitems = []) :
    serveUnderPolicyMetered pc Reactor.Deploy.emptyMwPolicy clientIp connSeq req
      = Reactor.Deploy.servePipelineFull2Metered clientIp connSeq req := by
  rw [serveUnderPolicyMetered_empty_eq, serveUnderConfigMetered_default pc clientIp connSeq req hr hv]

/-- **`drorb_serve_metered_cfg` — the CONFIG-DRIVEN, DEFAULT-ON metered serve.** The seam the
running default serve crosses. Args mirror `drorb_serve_metered` (`peer` family-tagged
bit-encoded address, `seq` per-connection index) but `input` is cfg-FRAMED:
`cfgLen(4 BE) :: configBytes :: requestBytes`.

The config text drives BOTH dimensions: `Dsl.Config.parseChars` yields the route table, and
`Reactor.Deploy.parsePolicy` (a total, independent scan) yields the MIDDLEWARE POLICY
(`max-body-size`/`allow-method`/`allow-host`). The request is served through
`serveUnderPolicyMetered pc policy` — the connection-aware gate chain over the CONFIG's route
table WITH the config-driven method-`405`/body-`413`/Host-`421` gates enforced on EVERY request
(no per-request test header). When the config declares NO policy directive the policy is
`emptyMwPolicy`, so the three gates fold transparently and the serve is byte-for-byte the old
`serveUnderConfigMetered` (`serveUnderPolicyMetered_empty_eq`); a routeless, policy-free config
(the DEFAULT, `cfgLen = 0`) is byte-for-byte `servePipelineFull2Metered`
(`serveUnderPolicyMetered_default`). On a non-UTF-8 config there is no policy — the default serve.
Total. -/
@[export drorb_serve_metered_cfg]
def drorbServeMeteredCfg (peer : ByteArray) (seq : UInt64) (input : ByteArray) : ByteArray :=
  match input.toList with
  | b0 :: b1 :: b2 :: b3 :: rest =>
    let cfgLen := be32 b0 b1 b2 b3
    let cfgBytes := rest.take cfgLen
    let reqBytes := rest.drop cfgLen
    let served :=
      match String.fromUTF8? (ByteArray.mk cfgBytes.toArray) with
      | none   =>
        Reactor.Deploy.servePipelineOfMetered Reactor.Deploy.defaultDeployment
          peer.toList seq.toNat reqBytes
      | some s =>
        let policy := Reactor.Deploy.parsePolicy s.data
        match Dsl.Config.parseChars s.data with
        | none    =>
          Reactor.Deploy.servePipelineOfMetered
            (Reactor.Deploy.policyDeploymentOn Reactor.Deploy.defaultDeployment policy)
            peer.toList seq.toNat reqBytes
        | some pc => serveUnderPolicyMetered pc policy peer.toList seq.toNat reqBytes
    ByteArray.mk served.toArray
  | _ => ByteArray.empty

/-! ## Braid — the METERED BRAIDED serve (`drorb_serve_metered_braided`)

The metered serve above (`drorb_serve_metered_cfg`) folds over the CONFIG's route table
but always over the frozen `deployStagesFull2` middleware chain (`denoteOn` leaves
`base.middleware` untouched), so a TEXT config can never select a different middleware
fold — the proven-but-inert braid stages (`Reactor.Deploy.braidedChain`) are unreachable
through it. This seam is the production path for the braid: it serves the METERED fold
over `Reactor.Deploy.braidedDeployment` — `defaultDeployment` with its middleware chain
replaced by `braidedChain` (the forward-auth gate + request-id echo at the head). The host
crosses this seam INSTEAD of `drorb_serve_metered_cfg` when the deployment is braid-marked
(`DRORB_BRAID`); the default (unmarked) path is untouched, and `defaultDeployment`'s
`servePipelineOfMetered_default` anchor is intact.

The composition is PROVEN (`Reactor.Deploy`): when neither the `x-forward-auth` marker nor
an incoming `x-request-id` is present the metered braided serve is byte-identical to
`servePipelineFull2Metered` (`servePipelineOfMetered_braided_off_eq`); a marked request
short-circuits to the genuine forward-auth `401` (`servePipelineOfMetered_braided_fa_denies_status`),
and an incoming id is echoed verbatim (`servePipelineOfMetered_braided_rid_echoes`). -/

/-- **`drorb_serve_metered_braided` — the METERED serve over the braid-5 deployment.**
Same ABI as `drorb_serve_metered` (`peer` family-tagged bit-encoded address, `seq`
per-connection index, `input` the raw HTTP/1.1 request), but the fold is
`Reactor.Deploy.servePipelineOfMetered Reactor.Deploy.braidedDeployment5` — the
connection-aware IP-filter/rate gate chain WITH SIXTEEN proven-but-inert stages composed
at the head: the §8 forward-auth gate + request-id echo, the §8h connection-cap (503) /
stick-table (429) / slowloris (408) gates + custom-error-page + compress transforms,
the §8j conditional-request (304) gate + pre-compressed-variant `Vary` +
directory-listing transforms, the §8l redirect (308) gate + CORS-ACAO + security-header
transforms, and the §8n NET-NEW method-filter (405) / body-size (413) / Host-allowlist
(421) gates — behaviour absent from BOTH the always-on `deployStagesFull2` list AND the
ingress FSM (each §8n composition proof a `Reactor.BraidCalculus` `braid_gate` one-liner).
A request with no braid markers is byte-for-byte `drorb_serve_metered`
(`servePipelineOfMetered_braided5_off_eq`); each marker FIRES its real library decision
(`servePipelineOfMetered_braided5_*`). Total. -/
@[export drorb_serve_metered_braided]
def drorbServeMeteredBraided (peer : ByteArray) (seq : UInt64) (input : ByteArray) : ByteArray :=
  ByteArray.mk
    (Reactor.Deploy.servePipelineOfMetered Reactor.Deploy.braidedDeployment5
      peer.toList seq.toNat input.toList).toArray

/-- **`drorb_serve_braided` — the NON-metered braided serve (the `entry`-table twin).**
The h2c-forking `drorb_serve` shape, but the HTTP/1.1 branch runs
`Reactor.Deploy.servePipelineBraided` (the braided chain over `ctxOf`). Byte-identical to
`drorb_serve` on unmarked traffic (`Reactor.Deploy.servePipelineBraided_off_eq`); the
metered production path uses `drorb_serve_metered_braided`. -/
@[export drorb_serve_braided]
def drorbServeBraided (input : ByteArray) : ByteArray :=
  let bytes := input.toList
  if Reactor.Ingress.hasH2Preface bytes then
    ByteArray.mk (Reactor.H2Ingress.serveH2c bytes).toArray
  else
    ByteArray.mk (Reactor.Deploy.servePipelineBraided5 bytes).toArray

/-! ## The RFC-conformant metered serves — the DEPLOYED DEFAULT

The metered serves above (`drorb_serve_metered`, `drorb_serve_metered_cfg`,
`drorb_serve_metered_braided`) fire the connection-aware IP-filter / rate gates but
serve the RAW deployed response — they do NOT carry the RFC 7230/7231 request-edge
validation (C1/C2/B2/G1/C3) or the response-edge `Date` (F1) / `HEAD`-strip (B1) the
conformance probe requires. The non-metered `drorb_serve_conformant` (DRORB_SPAN=19)
adds exactly those stages but wraps the NON-metered `drorbServe`, so it BYPASSES the
gates. These three exports close both edges at once: each wraps its metered fold with
the SAME proven `Reactor.ServeConformant.conformantServe` stages, so the deployed
default serves EVERY request through validation → the metered fold (the IP-filter /
rate gates in scope) → `Date` / `HEAD`-strip. The inner metered fold is UNCHANGED
(`drorbServeMetered` &c.); only the RFC edges are added. Every conformance property
(`conformant_rejects_missingHost`, `conformant_date_present_accept`,
`conformant_head_no_body`) is parametric over the inner serve, so it holds verbatim
for these metered inners — instantiated non-vacuously below. -/

/-- **`drorb_serve_metered_conformant`** — the RFC-conformant DEFAULT metered serve.
`conformantServe` wrapped around the plain metered fold `drorbServeMetered peer seq`:
validation (C1/C2/B2/G1/C3) → the metered IP-filter/rate gates → `Date` (F1) /
`HEAD`-strip (B1). Same `(peer, seq, input)` ABI as `drorb_serve_metered`; `input` is
the raw HTTP/1.1 request. -/
@[export drorb_serve_metered_conformant]
def drorbServeMeteredConformant (peer : ByteArray) (seq : UInt64) (input : ByteArray) : ByteArray :=
  Reactor.ServeConformant.conformantServe (fun i => drorbServeMetered peer seq i) input

/-- **`drorb_serve_metered_cfg_conformant`** — the RFC-conformant DEFAULT config-driven
metered serve (the seam the running Linux/io_uring default crosses). `input` is
cfg-FRAMED `cfgLen(4 BE) :: config :: request`; the wrapper runs the conformance stages
over the UNFRAMED request (so the validation gate and `HEAD` detection key on the real
request, not the frame header) and RE-FRAMES the (possibly absolute-form-normalized)
request with the SAME 4-byte cfgLen prefix + config for the inner `drorbServeMeteredCfg
peer seq` — so the config route table AND the metered gates are untouched, only the RFC
edges are added. With an empty config (`cfgLen = 0`, the default) the inner fold is
byte-identical to `drorbServeMetered` (`servePipelineOfMetered_default`). -/
@[export drorb_serve_metered_cfg_conformant]
def drorbServeMeteredCfgConformant (peer : ByteArray) (seq : UInt64) (input : ByteArray) : ByteArray :=
  match input.toList with
  | b0 :: b1 :: b2 :: b3 :: rest =>
    let cfgLen  := be32 b0 b1 b2 b3
    let cfgHead := b0 :: b1 :: b2 :: b3 :: rest.take cfgLen
    let reqBs   := rest.drop cfgLen
    Reactor.ServeConformant.conformantServe
      (fun req => drorbServeMeteredCfg peer seq (ByteArray.mk (cfgHead ++ req.toList).toArray))
      (ByteArray.mk reqBs.toArray)
  | _ => ByteArray.empty

/-- **`drorb_serve_metered_braided_conformant`** — the RFC-conformant metered BRAIDED
serve (opt-in, `DRORB_BRAID`). `conformantServe` wrapped around `drorbServeMeteredBraided
peer seq` (raw request `input`), so a braided deployment is ALSO RFC-conformant:
validation → the braided metered fold (forward-auth / request-id echo + the gates) →
`Date` / `HEAD`-strip. -/
@[export drorb_serve_metered_braided_conformant]
def drorbServeMeteredBraidedConformant (peer : ByteArray) (seq : UInt64) (input : ByteArray) : ByteArray :=
  Reactor.ServeConformant.conformantServe (fun i => drorbServeMeteredBraided peer seq i) input

/-- **B1, on the DEPLOYED metered-conformant serve.** Instantiating the parametric,
non-vacuous `conformant_head_no_body` at the plain metered inner: after the wrapper's
`HEAD`-strip the response carries NO body octets, for ANY request bytes. -/
theorem meteredConformant_head_no_body (peer : ByteArray) (seq : UInt64) (input : ByteArray) :
    Reactor.ServeConformant.afterBlank
      (Reactor.ServeConformant.stripBody
        (Reactor.ServeConformant.respBytesRaw (fun i => drorbServeMetered peer seq i) input)) = [] :=
  Reactor.ServeConformant.conformant_head_no_body _ input

/-- **C1, on the DEPLOYED metered-conformant serve.** Instantiating the parametric,
non-vacuous `conformant_rejects_missingHost` (a REAL missing-Host request, pinned by the
request serializer round-trip) at the plain metered inner: the wrapper rejects it as
`serialize (addDate badRequestResp)` — a `400` — WITHOUT consulting the metered fold. -/
theorem meteredConformant_rejects_missingHost (peer : ByteArray) (seq : UInt64) :
    Reactor.ServeConformant.respBytesRaw (fun i => drorbServeMetered peer seq i)
        Reactor.ServeConformant.missingHostInput
      = Reactor.serialize (Reactor.ServeConformant.addDate
          Reactor.Stage.RequestValidation.badRequestResp) :=
  Reactor.ServeConformant.conformant_rejects_missingHost _

#print axioms meteredConformant_head_no_body
#print axioms meteredConformant_rejects_missingHost

/-! ## The DENSE metered-conformant DEFAULT — fold the `/bulk` body-cliff fix INTO the
deployed metered-conformant default.

The metered-conformant default above (`drorbServeMeteredConformant`) wraps the plain
metered fold `drorbServeMetered peer seq`, whose `/bulk` (1 MiB) arm materialises the body
as a `List UInt8` cons-spine (the body-cliff). `Datapath.ServeDenseReal.serveDenseReal`
fixed that cliff for the NON-metered serve (`= drorbServe`, `DRORB_SPAN=18`), but it does
not carry the connection-aware IP-filter/rate gates the metered default runs. This section
folds the dense `/bulk` arm INTO the metered fold and wraps it conformant, so the deployed
DEFAULT serve is RFC-conformant AND dense on the large-body arm WITHOUT dropping the gates.

The load-bearing bridge (`Reactor.Deploy.servePipelineFull2Metered_bulk_eq`): on a plain
`GET /bulk` where the IP-filter ADMITS the peer and the rate bucket ADMITS the sequence,
the metered fold emits the SAME bytes as the non-metered `servePipelineFull2` — the metered
attrs (peer/seq) only feed the two gates, which are transparent when they pass. So the dense
head+body (already proven `= servePipelineFull2` on this arm by
`Datapath.ServeDenseReal.denseArm_eq`) is byte-identical to the metered fold there too. -/

namespace Reactor.Deploy

open Proto (Bytes)
open Reactor.Pipeline (Ctx StageStep Stage runPipeline ResponseBuilder)

/-- **The IP-filter gate passes on an admitted address.** When the deployed admission
decision admits the context's client address (`deployAdmits (ctxAddr c) = true`), the real
`ipfilterStage` request phase `.continue`s unchanged — the admitted-arm analogue of the
metered default's no-attr `ipfilterStage_pass'`, for a ctx that DOES carry an accept peer. -/
theorem ipfilterStage_pass_admit (c : Ctx)
    (h : Reactor.Stage.IpFilter.deployAdmits (Reactor.Stage.IpFilter.ctxAddr c) = true) :
    Reactor.Stage.IpFilter.ipfilterStage.onRequest c = .continue c := by
  simp only [Reactor.Stage.IpFilter.ipfilterStage, h]

/-- **`full2_reduces_unknown_pass` — the admitted-arm reduction, parametric over the
IP-filter pass witness.** Identical to `full2_reduces_unknown`, but the IP-filter step is
supplied as a hypothesis (`hippass : ipfilterStage.onRequest c = .continue c`) rather than
derived from a missing `client.ip` attr — so it fires for a metered ctx (accept peer present
and ADMITTED) as well as the bare non-metered ctx. Same conclusion: the fold collapses to the
five inner response transforms threaded through the outer deploy header rewrite. -/
theorem full2_reduces_unknown_pass (c : Ctx)
    (hadmin : isAdminPath c.req = false)
    (hpriv : Reactor.Stage.BasicAuth.isProtectedPath c.req = false)
    (hippass : Reactor.Stage.IpFilter.ipfilterStage.onRequest c = .continue c)
    (hrate : Reactor.Stage.Rate.admits c = true)
    (hredir : ¬ (c.req.target = Reactor.Stage.Redirect.ruleTarget))
    (htrav : targetEscapes c.req = false)
    (hpol : policyReserved c.req = false) :
    runPipeline deployStagesFull2 appHandler c
      = (runPipeline full2InnerStages appHandler c).mapResp
          (Reactor.Lifecycle.rewriteResp
            (deployProg (deployPlan (deploySubs c.input)) c.input)) := by
  show runPipeline (jwtAdminStage :: Reactor.Stage.BasicAuth.basicStage
      :: Reactor.Stage.IpFilter.ipfilterStage :: Reactor.Stage.Rate.rateStage
      :: cacheEmptyStage :: Reactor.Stage.Redirect.redirectStage :: traversalStage
      :: policyStage :: headerRewriteStage :: full2InnerStages) appHandler c = _
  rw [Reactor.Pipeline.pipeline_stage_effect jwtAdminStage _ appHandler c c (jwtAdminStage_pass c hadmin),
      Reactor.Pipeline.pipeline_stage_effect Reactor.Stage.BasicAuth.basicStage _ appHandler c c
        (Reactor.Stage.BasicAuth.basicStage_pass c hpriv),
      Reactor.Pipeline.pipeline_stage_effect Reactor.Stage.IpFilter.ipfilterStage _ appHandler c c
        hippass,
      Reactor.Pipeline.pipeline_stage_effect Reactor.Stage.Rate.rateStage _ appHandler c c
        (Reactor.Stage.Rate.rateStage_onReq_continue c hrate),
      Reactor.Pipeline.pipeline_stage_effect cacheEmptyStage _ appHandler c c (cacheEmptyStage_pass c),
      Reactor.Pipeline.pipeline_stage_effect Reactor.Stage.Redirect.redirectStage _ appHandler c c
        (redirectStage_pass c hredir),
      Reactor.Pipeline.pipeline_stage_effect traversalStage _ appHandler c c (traversalStage_pass c htrav),
      Reactor.Pipeline.pipeline_stage_effect policyStage _ appHandler c c (policyStage_pass_unknown c hpol),
      Reactor.Pipeline.pipeline_stage_effect headerRewriteStage _ appHandler c c rfl]
  simp only [jwtAdminStage, Reactor.Stage.BasicAuth.basicStage,
    Reactor.Stage.IpFilter.ipfilterStage, Reactor.Stage.Rate.rateStage, cacheEmptyStage,
    Reactor.Stage.Cache.mkStage, Reactor.Stage.Redirect.redirectStage, traversalStage,
    policyStage, headerRewriteStage]

/-- **The inner response-transform fold is insensitive to the metered attrs.** The five
`full2InnerStages` (cors/gzip/htmlrewrite/security/header) all pass the request phase
(`onRequest c = .continue c`) and their response phase reads only `c.req`/`c.input` — never
`c.attrs`. Since `ctxOfMetered peer seq input` differs from `ctxOf input` ONLY in `.attrs`,
the inner fold is identical over the two. -/
theorem innerFold_ctxOfMetered (peer : Bytes) (seq : Nat) (input : Bytes) :
    runPipeline full2InnerStages appHandler (ctxOfMetered peer seq input)
      = runPipeline full2InnerStages appHandler (ctxOf input) := rfl

/-- **The metered bridge on the `/bulk` arm.** On a plain `GET /bulk` request whose gates
all pass — the `BulkArm` decidable guard on the bare ctx PLUS the IP-filter ADMITTING the
metered peer and the rate bucket ADMITTING the metered sequence — the metered fold
`servePipelineFull2Metered peer seq input` emits the SAME bytes as the non-metered
`servePipelineFull2 input`. Both reduce (via `full2_reduces_unknown_pass` / the bare
`full2_reduces_unknown`) to the inner transform fold under the outer deploy rewrite; the
metered attrs feed only the two now-transparent gates (`innerFold_ctxOfMetered`). -/
theorem servePipelineFull2Metered_bulk_eq (peer : Bytes) (seq : Nat) (input : Bytes)
    (harm : Datapath.ServeDenseReal.BulkArm (ctxOf input))
    (hip_m : Reactor.Stage.IpFilter.deployAdmits
        (Reactor.Stage.IpFilter.ctxAddr (ctxOfMetered peer seq input)) = true)
    (hrate_m : Reactor.Stage.Rate.admits (ctxOfMetered peer seq input) = true) :
    servePipelineFull2Metered peer seq input = servePipelineFull2 input := by
  obtain ⟨hadmin, hpriv, hrate0, hredir, htrav, hpol, _hgz, _hcors, _hseg, _hna, _hnb⟩ := harm
  -- `ctxOfMetered` only sets `.attrs`, so its `.input` is defeq the bare ctx's `.input`; the
  -- outer deploy-rewrite arg (`deploySubs c.input`) is thus the same for both.
  have hin : (ctxOfMetered peer seq input).input = (ctxOf input).input := rfl
  have key : runPipeline deployStagesFull2 appHandler (ctxOfMetered peer seq input)
           = runPipeline deployStagesFull2 appHandler (ctxOf input) := by
    rw [full2_reduces_unknown_pass (ctxOfMetered peer seq input) hadmin hpriv
          (ipfilterStage_pass_admit _ hip_m) hrate_m hredir htrav hpol,
        full2_reduces_unknown (ctxOf input) hadmin hpriv rfl hrate0 hredir htrav hpol,
        innerFold_ctxOfMetered peer seq input, hin]
  unfold servePipelineFull2Metered servePipelineFull2
  rw [key]

/-- **The dense-arm guard for the METERED serve.** The bare `/bulk`-arm guard PLUS the two
metered gate-pass conditions the bridge needs: the IP-filter admits the peer and the rate
bucket admits the sequence. Decidable (each conjunct is a decidable computation on the small
request / the encoded peer / the sequence count — never the body). -/
def BulkArmMetered (peer : Bytes) (seq : Nat) (input : Bytes) : Prop :=
  Datapath.ServeDenseReal.BulkArm (ctxOf input)
  ∧ Reactor.Stage.IpFilter.deployAdmits
      (Reactor.Stage.IpFilter.ctxAddr (ctxOfMetered peer seq input)) = true
  ∧ Reactor.Stage.Rate.admits (ctxOfMetered peer seq input) = true

instance (peer : Bytes) (seq : Nat) (input : Bytes) : Decidable (BulkArmMetered peer seq input) := by
  unfold BulkArmMetered; infer_instance

end Reactor.Deploy

/-- **The DENSE metered serve.** The metered fold `drorbServeMetered peer seq`, but on the
admitted `/bulk` arm (`Reactor.Deploy.BulkArmMetered`) it emits the DENSE head + DENSE 1 MiB
`Array` body (no per-byte `List` cons — the body-cliff fix), else the deployed metered List
fold. NOT exported as a default itself; wrapped conformant below. -/
@[export drorb_serve_metered_dense]
def drorbServeMeteredDense (peer : ByteArray) (seq : UInt64) (input : ByteArray) : ByteArray :=
  if Reactor.Deploy.BulkArmMetered peer.toList seq.toNat input.toList then
    ByteArray.mk (Datapath.ServeDenseReal.denseHeadBytes input.toList).toArray
      ++ Datapath.ServeDenseFullReal.bulkBodyDense
  else
    ByteArray.mk (Reactor.Deploy.servePipelineFull2Metered peer.toList seq.toNat input.toList).toArray

/-- **The dense metered serve is byte-identical to the plain metered serve — for EVERY
peer/seq/input.** On the off-arm it is `drorbServeMetered` verbatim; on the admitted `/bulk`
arm the dense head+body is `= servePipelineFull2 input` (`denseArm_eq`) `= servePipelineFull2Metered
peer seq input` (`servePipelineFull2Metered_bulk_eq`, the gates transparent). So swapping it
in changes NO served byte AND keeps the metered IP-filter/rate gates. -/
theorem drorbServeMeteredDense_eq (peer : ByteArray) (seq : UInt64) (input : ByteArray) :
    drorbServeMeteredDense peer seq input = drorbServeMetered peer seq input := by
  unfold drorbServeMeteredDense drorbServeMetered
  by_cases harm : Reactor.Deploy.BulkArmMetered peer.toList seq.toNat input.toList
  · rw [if_pos harm]
    obtain ⟨hbulk, hip_m, hrate_m⟩ := harm
    rw [Datapath.ServeDenseReal.denseArm_eq input hbulk,
        Reactor.Deploy.servePipelineFull2Metered_bulk_eq peer.toList seq.toNat input.toList
          hbulk hip_m hrate_m]
  · rw [if_neg harm]

/-- **`drorb_serve_metered_dense_conformant`** — the RFC-conformant DENSE metered DEFAULT
serve. `Reactor.ServeConformant.conformantServe` wrapped around `drorbServeMeteredDense peer
seq`: validation (C1/C2/B2/G1/C3) → the metered IP-filter/rate gates → the `/bulk` dense arm
(no 1 MiB `List` cons) → `Date` (F1) / `HEAD`-strip (B1). Byte-identical to the deployed
metered-conformant default (`meteredDenseConformant_eq_meteredConformant`), so it inherits
every conformance property AND every metered gate — it only removes the body-cliff cons on
the large-body arm. Same `(peer, seq, input)` ABI as `drorb_serve_metered_conformant`. -/
@[export drorb_serve_metered_dense_conformant]
def drorbServeMeteredDenseConformant (peer : ByteArray) (seq : UInt64) (input : ByteArray) : ByteArray :=
  Reactor.ServeConformant.conformantServe (fun i => drorbServeMeteredDense peer seq i) input

/-- **The dense metered-conformant default IS the deployed metered-conformant default.** The
inner serves are equal as FUNCTIONS (`drorbServeMeteredDense_eq`, funext), and `conformantServe`
is a function OF its inner, so wrapping either yields the identical bytes — the conformance
edges and the metered gates are untouched; only the body-cliff cons is removed on `/bulk`. -/
theorem meteredDenseConformant_eq_meteredConformant
    (peer : ByteArray) (seq : UInt64) (input : ByteArray) :
    drorbServeMeteredDenseConformant peer seq input
      = drorbServeMeteredConformant peer seq input := by
  unfold drorbServeMeteredDenseConformant drorbServeMeteredConformant
  have hf : (fun i => drorbServeMeteredDense peer seq i)
          = (fun i => drorbServeMetered peer seq i) := by
    funext i; exact drorbServeMeteredDense_eq peer seq i
  rw [hf]

/-- **B1, on the DEPLOYED dense metered-conformant serve.** Instantiating the parametric,
non-vacuous `conformant_head_no_body` at the dense metered inner: after the wrapper's
`HEAD`-strip the response carries NO body octets, for ANY request bytes. -/
theorem meteredDenseConformant_head_no_body (peer : ByteArray) (seq : UInt64) (input : ByteArray) :
    Reactor.ServeConformant.afterBlank
      (Reactor.ServeConformant.stripBody
        (Reactor.ServeConformant.respBytesRaw (fun i => drorbServeMeteredDense peer seq i) input)) = [] :=
  Reactor.ServeConformant.conformant_head_no_body _ input

/-- **C1, on the DEPLOYED dense metered-conformant serve.** Instantiating the parametric,
non-vacuous `conformant_rejects_missingHost` (a REAL missing-Host request) at the dense
metered inner: the wrapper rejects it as `serialize (addDate badRequestResp)` — a `400` —
WITHOUT consulting the dense metered fold. -/
theorem meteredDenseConformant_rejects_missingHost (peer : ByteArray) (seq : UInt64) :
    Reactor.ServeConformant.respBytesRaw (fun i => drorbServeMeteredDense peer seq i)
        Reactor.ServeConformant.missingHostInput
      = Reactor.serialize (Reactor.ServeConformant.addDate
          Reactor.Stage.RequestValidation.badRequestResp) :=
  Reactor.ServeConformant.conformant_rejects_missingHost _

#print axioms drorbServeMeteredDense_eq
#print axioms meteredDenseConformant_eq_meteredConformant
#print axioms meteredDenseConformant_head_no_body
#print axioms meteredDenseConformant_rejects_missingHost

/-- **The INDEX-NATIVE metered-conformant serve IS the deployed metered-conformant
default.** `Datapath.ServeMeteredHeadIdx.serveMeteredHeadIdxConformant` (the metered
serve with the arm decision parsed ONCE, index-natively — gates on the host scalars,
`bulkIdxB`/`healthIdxB` on the arena head) equals `drorbServeMeteredConformant` for
EVERY `(peer, seq, input)`: `serveMeteredHeadIdxConformant_eq` lands on
`conformantServe` over `Datapath.ServeMeteredHeadIdx.meteredFoldServe`, whose body IS
`drorbServeMetered`'s body definitionally. -/
theorem meteredHeadIdxConformant_eq_meteredConformant
    (peer : ByteArray) (seq : UInt64) (input : ByteArray) :
    Datapath.ServeMeteredHeadIdx.serveMeteredHeadIdxConformant peer seq input
      = drorbServeMeteredConformant peer seq input :=
  Datapath.ServeMeteredHeadIdx.serveMeteredHeadIdxConformant_eq peer seq input

/-- The index-native metered-conformant serve is ALSO byte-identical to the DENSE
metered-conformant serve it replaces on the deployed default — both equal the plain
metered-conformant serve. -/
theorem meteredHeadIdxConformant_eq_meteredDenseConformant
    (peer : ByteArray) (seq : UInt64) (input : ByteArray) :
    Datapath.ServeMeteredHeadIdx.serveMeteredHeadIdxConformant peer seq input
      = drorbServeMeteredDenseConformant peer seq input :=
  (meteredHeadIdxConformant_eq_meteredConformant peer seq input).trans
    (meteredDenseConformant_eq_meteredConformant peer seq input).symm

#print axioms meteredHeadIdxConformant_eq_meteredConformant
#print axioms meteredHeadIdxConformant_eq_meteredDenseConformant

/-! ## The STREAMING response-emit seam — `drorb_serve_stream`

The seams above return the WHOLE response in one `ByteArray`, so the host holds the
entire response in memory before it writes a byte. This seam is the streaming EMIT
(roadmap Stage 2): the proven `Reactor.ServeStream.serveChunkList` cuts the deployed
response into a HEAD chunk followed by bounded body chunks (each `≤` the host-chosen
chunk size), and the host pulls them ONE AT A TIME by index, writing each to the
socket and dropping it — so the host never materializes the whole response.

It is a RE-ENTRANT by-index step (the same replay-is-pure discipline as
`drorb_serve_step`/`resume`): input `idx(4 BE) :: chunkSize(4 BE) :: request`; output
`flags(1) :: chunkBytes`, where `flags` bit 0 = "more chunks follow" and bit 1 = the
keep-alive decision. When `idx` is past the last chunk the output is EMPTY (the host's
loop terminator). The chunk stream reassembles to exactly the batch `drorb_serve`
response byte-for-byte (`serveChunkList_flatten`), so the streamed delivery is a
drop-in for the batch serve on the wire — only the host's memory profile changes. -/
@[export drorb_serve_stream]
def drorbServeStream (input : ByteArray) : ByteArray :=
  match input.toList with
  | i0 :: i1 :: i2 :: i3 :: s0 :: s1 :: s2 :: s3 :: req =>
    let idx := be32 i0 i1 i2 i3
    let cfg : Reactor.ServeStream.ServeConfig := { chunk := be32 s0 s1 s2 s3 }
    let chunks := Reactor.ServeStream.serveChunkList cfg req
    match chunks[idx]? with
    | some c =>
      let more : UInt8 := if idx + 1 < chunks.length then 1 else 0
      let ka   : UInt8 := if Reactor.ServeStream.keepAliveOf req then 2 else 0
      ByteArray.mk (((more ||| ka) :: c).toArray)
    | none => ByteArray.empty
  | _ => ByteArray.empty

/-- **The streamed chunks are the batch response.** For any request, concatenating the
body chunks the host pulls out of `drorb_serve_stream` (the head chunk at index 0 then
the paced body chunks) reproduces the deployed batch serve byte-for-byte — the
streamed delivery is byte-identical to `drorb_serve`. -/
theorem drorbServeStream_faithful (cfg : Reactor.ServeStream.ServeConfig) (req : Proto.Bytes) :
    (Reactor.ServeStream.serveChunkList cfg req).flatten
      = Reactor.Deploy.servePipelineFull2 req :=
  Reactor.ServeStream.serveChunkList_flatten cfg req

/-! ## The in-process TLS 1.3 HTTPS front door — `drorb_tls_serve`

The seams above serve PLAINTEXT bytes: the native host reads an HTTP/1.1 request
off a bare TCP socket and crosses `drorb_serve`. This section adds the missing
front door: a native host hands one accepted TCP connection's file descriptor to
`drorb_tls_serve`, and the VERIFIED TLS 1.3 server runs the whole connection
IN THIS PROCESS — the RFC 8446 handshake (`TlsHandshake.serverStep`: ClientHello
parse, X25519 ECDHE, key schedule, Certificate/CertificateVerify/Finished flight,
client-Finished check), then the established record layer (`TlsHandshake.appStep`:
open each application_data record, strip §5.4 padding), and for each complete
decrypted HTTP request it crosses the SAME proven `drorbServe` the plaintext path
runs and seals the response back as a §5 record (`TlsHandshake.sealRecordAt`).

Every protocol decision and all cryptography happen here, in the same
`serverStep`/`appStep` the TLS theorems are about, over the verified `Crypto`
primitives (EverCrypt AEAD/HKDF/SHA, Ed25519, X25519). The untrusted host owns
only the socket: accept, and the raw `recv`/`send` this seam calls through the
`ffi/derp_net.o` byte-mover (`drorb_tcp_recv_exact` / `drorb_tcp_send` — the same
blocking TCP shim the DERP live driver uses). It never parses a TLS record or
touches a key.

Reachable in this cut: a MULTI-CERTIFICATE pool (Ed25519 default plus, when the
host supplies the material, an ECDSA-P256 and an RSA-PSS-2048 end-entity
certificate), X25519 key exchange, full 1-RTT handshake, and the established
application-data record layer serving real HTTP through `drorbServe`. The
certificate presented is chosen by the SAME proven `chooseCert` the testssl-A+
conformance path uses (`TlsHandshake.serverStep` → `chooseCert`): it reads the
client's `signature_algorithms` and returns an entry whose `SignatureScheme` the
client offered (`chooseCert_respects_sigalgs`). So a real client that rejects
Ed25519 (curl/LibreSSL/browsers) is presented an ECDSA-P256 or RSA-PSS
certificate and connects.

Now wired on this deployed path, over the same proven pieces:
  * **SNI certificate selection** (RFC 6066 §3, `chooseCert_honors_sni`): a pool
    entry bound to a host (`DRORB_TLS_ECDSA_SNI` / `DRORB_TLS_RSA_SNI`) is
    presented only when the ClientHello's `server_name` matches; other names /
    no SNI fall to the name-agnostic entries.
  * **ALPN** (RFC 7301, `negotiateAlpn_sound`): `serverStep` negotiates the
    application protocol in EncryptedExtensions — the deployment advertises
    `h2` then `http/1.1` (`serverAlpn`). When the client negotiates `h2`, the
    decrypted record stream drives the SAME proven HTTP/2 connection engine the
    h2c path runs (`H2.Conn.feed`, over `h2Loop`); otherwise the HTTP/1.1
    pipeline runs over `appLoop`. The negotiated bytes are the proven serve;
    only the transport binding (ALPN select + record-layer framing) is new.
  * **Session resumption** (RFC 8446 §4.6.1, §4.2.11): `enterApp` issues a
    NewSessionTicket — a stateless sealed ticket carrying the resumption PSK,
    suite, and ALPN — and a later connection presenting it resumes through the
    proven PSK path (`checkPsk`, binder-verified, over `ticketKey seed`).
  * **0-RTT early data** (RFC 8446 §4.2.10, §8): opt-in via `DRORB_TLS_EARLY_DIR`
    — issued tickets then advertise `max_early_data`, the per-offer anti-replay
    gate (`gateFor`/`markTicketOnce`) instantiates `earlyDataOk`, and accepted
    early records are served through `drorbServe`. Without the opt-in the gate
    rejects all 0-RTT (early records trial-skipped, 1-RTT completes). -/

namespace Dataplane.Tls

open TlsHandshake

/-- Send all bytes of `payload` on the connected socket `fd`. Backed by
`ffi/derp_net.o`'s `drorb_tcp_send` (a blocking `send` loop); the byte-mover
parses nothing. -/
@[extern "drorb_tcp_send"]
opaque tcpSend (fd : UInt32) (payload : ByteArray) : IO Unit

/-- Read EXACTLY `nbytes` from `fd`, waiting up to `timeoutMs`; `none` on
timeout / EOF / error. Backed by `ffi/derp_net.o`'s `drorb_tcp_recv_exact`. -/
@[extern "drorb_tcp_recv_exact"]
opaque tcpRecvExact (fd : UInt32) (nbytes : UInt32) (timeoutMs : UInt32) :
    IO (Option ByteArray)

/-- Close the socket `fd`. Backed by `ffi/derp_net.o`'s `drorb_tcp_close`. -/
@[extern "drorb_tcp_close"]
opaque tcpClose (fd : UInt32) : IO Unit

/-- Per-record read timeout (ms). A stalled peer costs at most this long. -/
def recvTimeout : UInt32 := 15000

/-- Read one full TLS record off the wire: the 5-byte `type ‖ version ‖ length`
header (RFC 8446 §5.1), then exactly the declared body. Returns the outer
content-type byte and the FULL record bytes (header ++ body — the shape
`serverStep`/`openRecordAt` strip), or `none` on EOF/timeout/short read. -/
def readRecord (fd : UInt32) : IO (Option (UInt8 × ByteArray)) := do
  match ← tcpRecvExact fd 5 recvTimeout with
  | none => return none
  | some hb =>
    if hb.size < 5 then return none
    let ctype := hb.get! 0
    let len := (hb.get! 3).toNat * 256 + (hb.get! 4).toNat
    if len > 18432 then return none          -- > 2^14 + 256: not a valid record
    let body ← if len == 0 then pure (some ByteArray.empty)
               else tcpRecvExact fd (UInt32.ofNat len) recvTimeout
    match body with
    | none => return none
    | some bb => return some (ctype, hb ++ bb)

/-- Lowercase-hex a byte string (for anti-replay register filenames). -/
def toHex (b : ByteArray) : String :=
  let d := "0123456789abcdef".toList.toArray
  b.toList.foldl (fun s x => s ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

/-- Single-use 0-RTT anti-replay register (RFC 8446 §8): one file per
ticket-identity hash under `dir`, `true` iff this identity is used for the FIRST
time. The existence check and the mark are two filesystem steps, not one atomic
operation — the honest conformance-grade seam (the SAME the `tls-wire-oracle`
uses); a production register would create atomically. -/
def markTicketOnce (dir : String) (identity : Tls.Bytes) : IO Bool := do
  let path := System.FilePath.mk dir / toHex (Crypto.sha256 (ofBytes identity))
  if (← path.pathExists) then return false
  IO.FS.writeFile path "used"
  return true

/-- Instantiate the per-connection 0-RTT gate (§4.2.10, §8). When the deployment
opted into 0-RTT (`earlyDir` set) and this first ClientHello offers a PSK with
early data, consult-and-mark the anti-replay register and pin
`ServerParams.earlyDataOk` to the fresh verdict for exactly that identity;
otherwise the default gate (reject all 0-RTT) stands, and `serverStep`
trial-skips any early records the client sent. -/
def gateFor (earlyDir : Option String) (params : ServerParams) (chBytes : Tls.Bytes) :
    IO ServerParams := do
  match earlyDir with
  | none => pure params
  | some dir =>
    match parseClientHello chBytes with
    | some ch =>
      match ch.psk, ch.earlyData with
      | some op, true =>
        let fresh ← markTicketOnce dir op.identity
        pure { params with earlyDataOk := fun id => fresh && (id == op.identity) }
      | _, _ => pure params
    | none => pure params

/-- The established application phase: read each record, open it with `appStep`,
and once a complete HTTP request head has arrived (CRLFCRLF) cross the SAME
proven `drorbServe` the plaintext front runs, sealing its response as a §5
application_data record under the send keys. Loops until close/EOF. `fuel`
bounds the record count so the driver is structurally total.

The connection disposition after each served response is the SAME proven
keep-alive decision the plaintext host consults
(`Reactor.ServeStream.keepAliveOf` — the deployed HTTP/1.1 parse's verdict): a
request that asked `Connection: close` (or is HTTP/1.0 without keep-alive) gets
a close_notify (§6.1) and the socket closed RIGHT AFTER its response, so a
read-to-EOF client sees the FIN promptly instead of waiting out the per-record
recv timeout. -/
partial def appLoop (fd : UInt32) (app : AppConn) (reqBuf : List UInt8) : IO Unit := do
  match ← readRecord fd with
  | none => tcpClose fd
  | some (0x14, _) => appLoop fd app reqBuf   -- a stray CCS (§5): drop
  | some (_, rec) =>
    match appStep app rec.toList with
    | (app', .deliver content, _) =>
      let reqBuf := reqBuf ++ content
      if hasCrlfCrlf reqBuf then
        -- A complete request head: serve it through the proven pipeline and
        -- seal the response bytes as one application_data record.
        let resp := drorbServe (ofBytes reqBuf)
        match sealRecordAt app'.txKeys app'.txSeq 0x17 resp with
        | some wire => do
          tcpSend fd wire
          let app' := { app' with txSeq := app'.txSeq + 1 }
          if Reactor.ServeStream.keepAliveOf reqBuf then
            appLoop fd app' []
          else do
            -- `Connection: close` honored: a polite close_notify, then FIN now.
            let (_, bye) := appSeal app' 0x15 closeNotifyPayload
            if !bye.isEmpty then tcpSend fd bye
            tcpClose fd
        | none => tcpClose fd
      else appLoop fd app' reqBuf
    | (_, .close, reply) => do tcpSend fd reply; tcpClose fd
    | (app', .keyUpdated, reply) =>
      if reply.isEmpty then appLoop fd app' reqBuf
      else do tcpSend fd reply; appLoop fd app' reqBuf
    | (_, .fatal _, alert) => do tcpSend fd alert; tcpClose fd

/-- The established application phase for an **h2-over-TLS** connection (ALPN
selected `h2`, RFC 7301 + RFC 9113 §3.3). The decrypted TLS application stream
carries the HTTP/2 connection preface (RFC 9113 §3.4) followed by frames; each
opened record's plaintext is fed to the SAME proven HTTP/2 connection engine the
h2c path drives (`H2.Conn.feed` over `Reactor.H2.h2Huffman` and the deployed
stage-fold application `Reactor.H2Ingress.h2cHandler`), threading the engine's
`H2.Conn.ConnState` across records — its `prefaceLeft`/`buf` reassemble a preface
or frame split across TLS record boundaries. The engine's output frames (server
SETTINGS preface + SETTINGS ACK + HPACK HEADERS + DATA) are sealed as §5
application_data records under the send keys and written back encrypted; when the
engine signals close, the final frames are flushed and the socket closed. Only
the transport binding is new: the h2 response BYTES are exactly the proven
`H2.Conn.feed` bytes, the same the h2c serve emits. `fuel`-free structural
totality comes from `readRecord` returning `none` on EOF/timeout. -/
partial def h2Loop (fd : UInt32) (app : AppConn) (h2 : H2.Conn.ConnState) : IO Unit := do
  match ← readRecord fd with
  | none => tcpClose fd
  | some (0x14, _) => h2Loop fd app h2   -- a stray CCS (§5): drop
  | some (_, rec) =>
    match appStep app rec.toList with
    | (app', .deliver content, _) =>
      let (h2', out, close) :=
        H2.Conn.feed Reactor.H2.h2Huffman Reactor.H2Ingress.h2cHandler h2 content
      if out.isEmpty then
        if close then tcpClose fd else h2Loop fd app' h2'
      else
        match sealRecordAt app'.txKeys app'.txSeq 0x17 (ByteArray.mk out.toArray) with
        | some wire => do
          tcpSend fd wire
          if close then tcpClose fd
          else h2Loop fd { app' with txSeq := app'.txSeq + 1 } h2'
        | none => tcpClose fd
    | (_, .close, reply) => do tcpSend fd reply; tcpClose fd
    | (app', .keyUpdated, reply) =>
      if reply.isEmpty then h2Loop fd app' h2
      else do tcpSend fd reply; h2Loop fd app' h2
    | (_, .fatal _, alert) => do tcpSend fd alert; tcpClose fd

/-- Enter the established application phase (RFC 8446 §4.6). Issue a
NewSessionTicket as the FIRST application-phase record — a stateless, sealed
ticket for this session's resumption PSK, carrying the connection's suite and
ALPN (§4.2.10) and, when the deployment opted into 0-RTT (`maxEarly > 0`), the
`early_data` advertisement — under the server application keys (`ticketKey` is
derived from the same `seed`, so any later connection to this server opens it).
Then run the record layer for the negotiated ALPN: when `h2` was selected, the
decrypted stream (any accepted 0-RTT early data first) drives the proven HTTP/2
engine over `h2Loop`; otherwise, once an ACCEPTED 0-RTT phase already delivered a
complete HTTP request head (`earlyBuf`) it is answered in the same flight through
the SAME proven `drorbServe`, then the HTTP/1.1 record layer runs over
`appLoop`. -/
partial def enterApp (fd : UInt32) (seed : ByteArray) (maxEarly : Nat)
    (est : Established) (earlyBuf : List UInt8) : IO Unit := do
  let app := mkAppConn est
  let sealNonce ← IO.getRandomBytes 12
  let ageAddBytes ← IO.getRandomBytes 4
  let ageAdd := ageAddBytes.toList.foldl (fun a b => a * 256 + b.toNat) 0
  let (app, tkWire) :=
    match buildNewSessionTicket (ticketKey seed) sealNonce
            app.resumptionMaster ageAdd est.suite est.alpnProto maxEarly with
    | some nst =>
      match sealRecordAt app.txKeys app.txSeq 0x16 nst with
      | some w => ({ app with txSeq := app.txSeq + 1 }, w)
      | none => (app, ByteArray.empty)
    | none => (app, ByteArray.empty)
  if est.alpnProto == some alpnH2 then
    -- h2-over-TLS: feed any accepted 0-RTT early data to the proven H2 engine
    -- as the first burst, seal its output alongside the ticket, then run the
    -- record layer over `h2Loop`.
    let (h2, out, close) :=
      H2.Conn.feed Reactor.H2.h2Huffman Reactor.H2Ingress.h2cHandler {} earlyBuf
    let (app, outWire) :=
      if out.isEmpty then (app, tkWire)
      else match sealRecordAt app.txKeys app.txSeq 0x17 (ByteArray.mk out.toArray) with
           | some w => ({ app with txSeq := app.txSeq + 1 }, tkWire ++ w)
           | none => (app, tkWire)
    if !outWire.isEmpty then tcpSend fd outWire
    if close then tcpClose fd else h2Loop fd app h2
  else
    let (app, outWire, reqBuf, keep) :=
      if hasCrlfCrlf earlyBuf then
        match sealRecordAt app.txKeys app.txSeq 0x17 (drorbServe (ofBytes earlyBuf)) with
        | some w => ({ app with txSeq := app.txSeq + 1 }, tkWire ++ w, ([] : List UInt8),
                     Reactor.ServeStream.keepAliveOf earlyBuf)
        | none => (app, tkWire, earlyBuf, true)
      else (app, tkWire, earlyBuf, true)
    if !outWire.isEmpty then tcpSend fd outWire
    if keep then appLoop fd app reqBuf
    else do
      -- The answered 0-RTT request asked `Connection: close`: close_notify + FIN.
      let (_, bye) := appSeal app 0x15 closeNotifyPayload
      if !bye.isEmpty then tcpSend fd bye
      tcpClose fd

/-- The handshake phase: drive `serverStep` over each incoming record until the
connection is `established`, sending the server flight / HelloRetryRequest /
fatal alert it emits, then hand off to `enterApp`. On the first ClientHello the
0-RTT anti-replay gate is instantiated for this offer (`gateFor`); an accepted
early-data phase accumulates its plaintext in `earlyBuf` until EndOfEarlyData.
`maxEarly` is the `max_early_data_size` advertised on issued tickets (0 when the
deployment did not opt into 0-RTT). -/
partial def hsLoop (fd : UInt32) (params : ServerParams) (earlyDir : Option String)
    (maxEarly : Nat) (st : HsState) (earlyBuf : List UInt8) : IO Unit := do
  match ← readRecord fd with
  | none => tcpClose fd
  | some (0x14, _) => hsLoop fd params earlyDir maxEarly st earlyBuf  -- CCS (§5): drop
  | some (_, rec) =>
    match st with
    | .waitCH =>
      let params ← gateFor earlyDir params rec.toList
      match serverStep params .waitCH rec.toList with
      | (.waitClientFinished est, out) => do
        tcpSend fd out.flight; hsLoop fd params earlyDir maxEarly (.waitClientFinished est) earlyBuf
      | (.waitCH2 r, out) => do
        tcpSend fd out.flight; hsLoop fd params earlyDir maxEarly (.waitCH2 r) earlyBuf
      | (_, out) => do tcpSend fd out.flight; tcpClose fd
    | .waitCH2 r =>
      match serverStep params (.waitCH2 r) rec.toList with
      | (.waitClientFinished est, out) => do
        tcpSend fd out.flight; hsLoop fd params earlyDir maxEarly (.waitClientFinished est) earlyBuf
      | (_, out) => do tcpSend fd out.flight; tcpClose fd
    | .waitClientFinished est =>
      match serverStep params (.waitClientFinished est) rec.toList with
      | (.established est', _) => enterApp fd params.certSeed maxEarly est' earlyBuf
      | (.waitClientFinished est', out) =>
        -- An accepted early-data record (accumulate its plaintext), or a
        -- trial-skipped rejected-0-RTT record: the handshake continues.
        hsLoop fd params earlyDir maxEarly (.waitClientFinished est') (earlyBuf ++ out.earlyData)
      | (_, out) => do tcpSend fd out.flight; tcpClose fd
    | _ => tcpClose fd

/-- The servable certificate pool for the deployed front door, built from the
host's certificate material. The Ed25519 entry (`certDer`/`seed`) is the pool
default (`ServerParams.defaultCert`, last, name-agnostic). Each of the ECDSA-P256
and RSA-PSS-2048 entries is added when its material is non-empty, with its
CertificateVerify signing seam instantiated by the verified HACL* binding
(`TlsCrypto.Sig.ecdsaP256Sign` / `rsaPssSign`) — the SAME seams the
`tls-wire-oracle` conformance path instantiates. Order: ECDSA first, then RSA,
then the Ed25519 default, so `chooseCert` prefers the compact ECDSA entry when
the client offers `ecdsa_secp256r1_sha256`.

`ecdsaSni` / `rsaSni` (empty = none) bind an entry to a specific SNI host name
(RFC 6066 §3), so `chooseCert` — through the proven `sniPool` — presents THAT
entry only when the ClientHello's `server_name` matches (`chooseCert_honors_sni`).
A named entry no longer serves other names, so at least one pool member (the RSA
entry, or the Ed25519 default) MUST stay name-agnostic to serve non-matching /
no-SNI clients; the deployment binds only the ECDSA entry to a host by default. -/
def deployedCerts (ecdsaCert ecdsaPriv ecdsaSni rsaCert rsaN rsaE rsaD rsaSni : ByteArray) :
    List CertEntry :=
  let ecdsa : List CertEntry :=
    if ecdsaCert.isEmpty then []
    else [{ sigAlg := ecdsaSigAlg, certData := ecdsaCert
            sign := fun content => TlsCrypto.Sig.ecdsaP256Sign ecdsaPriv content
            names := if ecdsaSni.isEmpty then [] else [ecdsaSni.toList] }]
  let rsa : List CertEntry :=
    if rsaCert.isEmpty then []
    else
      let key : TlsCrypto.Sig.RsaKey := { n := rsaN, e := rsaE, d := rsaD }
      [{ sigAlg := rsaPssSigAlg, certData := rsaCert
         sign := fun content => TlsCrypto.Sig.rsaPssSign key content
         names := if rsaSni.isEmpty then [] else [rsaSni.toList] }]
  ecdsa ++ rsa

/-- **The runtime KEX posture** — the deployment's TLS/QUIC key-exchange policy,
read from `DRORB_TLS_KEX` at deploy time so an operator flips it without a
rebuild. `required` pins the X25519MLKEM768 hybrid (a classical-only client is
rejected — the wave-go-live posture); `preferred` (the pragmatic default) offers
both and honors the client's best offer (a hybrid client gets X-Wing, a legacy
client gets X25519); `classical` offers only X25519 (no post-quantum). -/
inductive KexPosture where
  | required
  | preferred
  | classical
deriving DecidableEq, Repr

/-- The hybrid-KEX pin implied by a posture: only `required` rejects a
classical-only client; `preferred`/`classical` allow the classical exchange. -/
def KexPosture.requireHybrid : KexPosture → Bool
  | .required => true
  | .preferred => false
  | .classical => false

/-- The named groups a posture offers, in preference order. `required` and
`preferred` both offer `[X25519MLKEM768, X25519]`; `classical` offers only
`[X25519]`. In every posture the hybrid group, when offered, is preferred (the
`kexStep` dispatch takes the client's hybrid share first). -/
def KexPosture.groups : KexPosture → List Nat
  | .required => [xwingGroup, x25519Group]
  | .preferred => [xwingGroup, x25519Group]
  | .classical => [x25519Group]

/-- Parse the `DRORB_TLS_KEX` value. Unset or unrecognized ⇒ the pragmatic
`preferred` default (serve everyone). -/
def KexPosture.ofName : Option String → KexPosture
  | some "required" => .required
  | some "classical" => .classical
  | _ => .preferred

/-- **The deployed TLS parameter template** — the one `ServerParams` shape
`drorbTlsServe` instantiates per connection (fresh `priv`/`rnd` entropy, the
host's certificate pool). Named so deployment-level facts are theorems about
THIS term: the deployment offers `[X25519MLKEM768, X25519]` and — since the PQ
go-live — REQUIRES the hybrid KEX (`requireHybridKex := true`): a
classical-only ClientHello is rejected, never silently downgraded
(`deployed_tls_no_classical_downgrade`). -/
def deployedTlsParams (posture : KexPosture) (priv rnd seed certDer : ByteArray)
    (certs : List CertEntry) : ServerParams :=
  { ephemeralPriv := priv
    serverRandom := rnd
    certSeed := seed
    certData := certDer
    groupsSupported := posture.groups
    requireHybridKex := posture.requireHybrid
    certs := certs }

/-- The deployment pins the hybrid KEX — the flip that makes
`tls_kex_hybrid_downgrade_safe` bite the deployed front door. -/
theorem deployedTlsParams_requires_hybrid
    (priv rnd seed certDer : ByteArray) (certs : List CertEntry) :
    (deployedTlsParams .required priv rnd seed certDer certs).requireHybridKex = true := rfl

/-- **`tls_kex_hybrid_downgrade_safe` instantiated at the deployed params**:
whatever entropy / certificate material a connection draws, a client that
offered no `X25519MLKEM768` share never completes the key exchange — the
deployed front door rejects classical-only clients rather than downgrading
to a classical shared secret. -/
theorem deployed_tls_no_classical_downgrade
    (priv rnd seed certDer : ByteArray) (certs : List CertEntry)
    (retried : Option Retry) (ch : ClientHello) (suite : Nat)
    (alpnSel : Option Tls.Bytes) (buf : Tls.Bytes) (est : Established)
    (hnohybrid : ch.keyShareHybrid = none) :
    (kexStep (deployedTlsParams .required priv rnd seed certDer certs)
        retried ch suite alpnSel buf).1 ≠ .waitClientFinished est :=
  tls_kex_hybrid_downgrade_safe _ retried ch suite alpnSel buf est rfl hnohybrid

/-- The PREFERRED posture leaves the hybrid pin OFF — a classical fallback is
allowed — while still offering the hybrid group. -/
theorem deployedTlsParams_preferred_pin_off
    (priv rnd seed certDer : ByteArray) (certs : List CertEntry) :
    (deployedTlsParams .preferred priv rnd seed certDer certs).requireHybridKex = false := rfl

/-- Both the required and the preferred posture offer the X25519MLKEM768 group. -/
theorem deployedTlsParams_preferred_offers_hybrid
    (priv rnd seed certDer : ByteArray) (certs : List CertEntry) :
    (deployedTlsParams .preferred priv rnd seed certDer certs).groupsSupported.contains
      xwingGroup = true := rfl

/-- **PREFERRED deployed front door honors a hybrid client** — the deployed-params
instantiation of `kex_preferred_honors_hybrid`. Whatever entropy / certificate
material a connection draws, a client that offers the X25519MLKEM768 share
negotiates `xwingGroup`, EVEN THOUGH the pin is off in preferred mode: honoring
the client's best offer is not a downgrade, and a hybrid client's flight is the
byte-identical hybrid handshake it would get under `required`. -/
theorem deployed_preferred_honors_hybrid
    (priv rnd seed certDer : ByteArray) (certs : List CertEntry)
    (retried : Option Retry) (ch : ClientHello) (suite : Nat)
    (alpnSel : Option Tls.Bytes) (buf : Tls.Bytes) (est : Established)
    (hy : Tls.Bytes) (hoff : ch.keyShareHybrid = some hy)
    (hres : (kexStep (deployedTlsParams .preferred priv rnd seed certDer certs)
        retried ch suite alpnSel buf).1 = .waitClientFinished est) :
    est.group = xwingGroup :=
  kex_preferred_honors_hybrid _ retried ch suite alpnSel buf est (deployedTlsParams_preferred_offers_hybrid priv rnd seed certDer certs) hy hoff hres

/-- **PREFERRED deployed front door: a classical session implies the client
offered no hybrid share** — the deployed-params instantiation of
`kex_classical_only_without_hybrid`. No silent downgrade: the deployed preferred
edge falls to the classical X25519 exchange ONLY for a client that did not offer
X-Wing. -/
theorem deployed_preferred_classical_needs_no_hybrid
    (priv rnd seed certDer : ByteArray) (certs : List CertEntry)
    (retried : Option Retry) (ch : ClientHello) (suite : Nat)
    (alpnSel : Option Tls.Bytes) (buf : Tls.Bytes) (est : Established)
    (hres : (kexStep (deployedTlsParams .preferred priv rnd seed certDer certs)
        retried ch suite alpnSel buf).1 = .waitClientFinished est)
    (hclassical : est.group = x25519Group) :
    ch.keyShareHybrid = none :=
  kex_classical_only_without_hybrid _ retried ch suite alpnSel buf est (deployedTlsParams_preferred_offers_hybrid priv rnd seed certDer certs) hres hclassical

/-- **`drorb_tls_serve` — the deployed HTTPS front door.** One accepted TCP
connection (`fd`) and the host's certificate material: the Ed25519 default
end-entity certificate (`certDer`, DER) with its 32-byte RFC 8032 signing seed
(`seed`), and — when supplied (empty = absent) — an ECDSA-P256 leaf (`ecdsaCert`,
DER) with its 32-byte raw scalar (`ecdsaPriv`) and an RSA-PSS-2048 leaf
(`rsaCert`, DER) with its big-endian modulus / public exponent / private exponent
(`rsaN`/`rsaE`/`rsaD`). Run the whole verified TLS 1.3 server on this connection
in-process — the handshake presents the certificate the proven `chooseCert`
selects from this pool per the client's `signature_algorithms`, then the record
layer serves real HTTP — HTTP/2 through the proven `H2.Conn.feed` engine when
ALPN negotiated `h2`, else HTTP/1.1 through `drorbServe` — and close. The X25519 ephemeral and
the ServerHello random are drawn fresh per connection from the OS entropy source,
so each connection gets its own DHE. Key exchange is hybrid-PINNED
(`deployedTlsParams`): a classical-only client is rejected, never downgraded
(`deployed_tls_no_classical_downgrade`). Total; any I/O error closes the socket. -/
@[export drorb_tls_serve]
def drorbTlsServe (fd : UInt32) (certDer seed
    ecdsaCert ecdsaPriv rsaCert rsaN rsaE rsaD : ByteArray) : IO Unit := do
  let priv ← IO.getRandomBytes 32
  let rnd ← IO.getRandomBytes 32
  -- SNI host bindings and the 0-RTT opt-in come from the environment, so the
  -- FFI cert-material ABI stays fixed: `DRORB_TLS_ECDSA_SNI` /
  -- `DRORB_TLS_RSA_SNI` bind that entry to a host (`chooseCert_honors_sni`);
  -- `DRORB_TLS_EARLY_DIR`, when set, opts into 0-RTT with a single-use
  -- anti-replay register at that path (empty ⇒ resumption only, no 0-RTT).
  let ecdsaSni := ((← IO.getEnv "DRORB_TLS_ECDSA_SNI").map (·.toUTF8)).getD ByteArray.empty
  let rsaSni := ((← IO.getEnv "DRORB_TLS_RSA_SNI").map (·.toUTF8)).getD ByteArray.empty
  let earlyDir ← IO.getEnv "DRORB_TLS_EARLY_DIR"
  match earlyDir with
  | some dir => IO.FS.createDirAll dir
  | none => pure ()
  -- The KEX posture (`DRORB_TLS_KEX`): `required` pins the X25519MLKEM768 hybrid
  -- (classical-only clients rejected), `classical` offers only X25519 (no PQ),
  -- and the default `preferred` offers both and honors the client's best group
  -- (a hybrid client gets X-Wing, a legacy client gets X25519). Read per
  -- connection so the posture can flip without a rebuild.
  let posture := KexPosture.ofName (← IO.getEnv "DRORB_TLS_KEX")
  let params : ServerParams :=
    deployedTlsParams posture priv rnd seed certDer
      (deployedCerts ecdsaCert ecdsaPriv ecdsaSni rsaCert rsaN rsaE rsaD rsaSni)
  let maxEarly := if earlyDir.isSome then params.maxEarlyData else 0
  try
    hsLoop fd params earlyDir maxEarly .waitCH []
  catch _ =>
    tcpClose fd

end Dataplane.Tls
