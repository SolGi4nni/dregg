#!/usr/bin/env bash
# Build libdrorb.a — the leanc-compiled proven serve as a static archive a
# native host links against.
#
# `lake build Dataplane:static` compiles the `@[export drorb_serve]` module and
# its transitive dependencies to Mach-O objects under .lake/build/ir/**/*.c.o.export.
# This script archives ALL of those objects into a single static library. The
# host linker pulls only the objects reachable from the symbols it references
# (drorb_serve, initialize_Dataplane and their closure) — the same object set the
# `orb-mac` exe links — so unreferenced modules (including the crypto seam, which
# the deployStepIngress path does not touch) are never pulled in.
#
# Re-run after changing Dataplane.lean or any module in its closure, then rebuild
# the Rust dataplane (crates/dataplane). Idempotent.
set -euo pipefail
cd "$(dirname "$0")/.."

# Compiles the Dataplane lib's own modules, including every `@[export]` defined in
# Dataplane.lean itself — `drorb_serve`, `drorb_serve_metered`, `drorb_serve_cfg`,
# and the Braid-0 `drorb_serve_metered_cfg` (the config-driven metered serve the
# running default now crosses). These ride this target's `.c.o.export`; no explicit
# per-symbol line is needed for them.
lake build Dataplane:static

# `Dataplane:static` compiles only the Dataplane lib's own modules
# (Dataplane, Dataplane.Multi) to objects; a transitive import contributes its
# `.olean` but not its `.c.o.export` object unless some `:static` target owns it.
# `Reactor.ProxyDial` (the `drorb_proxy_pick` reverse-proxy pick seam) is imported
# by Dataplane but lives in the `Reactor` lib, so compile its export object
# explicitly here — otherwise `drorb_proxy_pick` / `initialize_Reactor_ProxyDial`
# are absent from the archive and the host link fails undefined.
# CLOSURE-COMPLETE export build (the robust fix). The `:c.o.export` facet is
# per-module and NOT transitive, and a bare `lake build` does not emit it — so a
# hand-listed set of roots silently drifts out of date whenever Dataplane's import
# closure grows (a new braided stage, a new effect module). That gap stayed hidden
# for a long time because export objects ACCUMULATE in `.lake/build/ir` across
# incremental builds; only a true from-scratch `rm -rf .lake/build` exposes it
# (which is exactly what the CI honest-gate does). Fix: compute Dataplane's full
# transitive import closure and build every module's export facet. No hand-list to
# rot. Lib-only names (no module facet) fail harmlessly and are skipped.
python3 - <<'PYCLOSURE' > /tmp/drorb_dp_closure.txt
import re, os
def imports(mod):
    p = mod.replace('.', '/') + '.lean'
    return re.findall(r'^import\s+([A-Za-z0-9_.]+)', open(p).read(), re.M) if os.path.exists(p) else []
# Seed the closure from Dataplane AND the client/fetch export roots: the archive
# step globs EVERY *.c.o.export in .lake/build/ir, so any module built for another
# target (the fetch-client exe) is archived too — and its initialize_* references
# its imports (Client.H2Receive imports H2.RespTrailers/FlowWindow/PseudoHeader).
# Those H2 leaf modules are NOT in Dataplane's own closure, so unless we seed from
# the archived client roots their export objects are never built -> undefined
# symbol at the FROM-SCRATCH host link (a warm .lake cache masks it). The earlier
# per-module hand-list (b937721) was incomplete; seeding the closure is the durable fix.
# `Body.FrameRaw` (`drorb_frame_request`, the proven raw request-framing
# decision the host's http.rs crosses from its IO threads) is NOT in Dataplane's
# import closure — the serve modules never call it — so seed it too, else the
# export object and `initialize_Body_FrameRaw` are absent from the archive and
# the host link fails undefined.
# `Ws.Decode` (`drorb_ws_header` / `drorb_ws_close_ok`, the proven WebSocket
# frame-parse verdict + close-code registry the host frame codec crosses from
# its IO threads) is likewise NOT in the serve closure — seed it too.
# Ws.ReassemblyAdmit / Ws.ReassemblyClose (drorb_ws_admit / drorb_ws_utf8 /
# drorb_ws_close_body, the proven reassembly-admission, incremental-UTF-8, and
# close-body verdicts the host message engine crosses) are likewise NOT in the
# serve closure - seed them too (they pull Ws.Utf8 / Ws.Reassembly transitively).
# Ws.Encode (drorb_ws_encode_header / drorb_ws_encode_close, the proven outbound
# server-frame header + close-frame construction the host writes to the wire) is
# likewise NOT in the serve closure - seed it too.
seen, stack = set(), ['Dataplane', 'Client.FetchExport', 'Client.H2Receive', 'Client.Fetch', 'Client.H2', 'Client.H2Receive', 'Body.FrameRaw', 'Ws.Decode', 'Ws.ReassemblyAdmit', 'Ws.ReassemblyClose', 'Ws.Encode']
while stack:
    m = stack.pop()
    if m in seen: continue
    seen.add(m)
    stack += imports(m)
for m in sorted(m for m in seen if os.path.exists(m.replace('.', '/') + '.lean')):
    print(m)
PYCLOSURE
# The `+` prefix forces the MODULE target — needed for modules whose name collides
# with a `lean_lib` of the same name (BasicAuth, Cache, Cgi, Gzip, …), where a bare
# `Name:c.o.export` resolves the (facet-less) library and fails.
while IFS= read -r m; do
  lake build "+${m}:c.o.export" >/dev/null 2>&1 || true
done < /tmp/drorb_dp_closure.txt
echo "closure export build: $(wc -l < /tmp/drorb_dp_closure.txt | tr -d ' ') modules"

lake build Reactor.ProxyDial:c.o.export

# `Reactor.LoadBalance` (`drorb_lb_pick`, the config-policy + load-aware proxy
# pick) is imported by Dataplane but lives in the `Reactor` lib, so compile its
# export object explicitly - otherwise `drorb_lb_pick` / initialize_Reactor_LoadBalance
# are absent from the archive and the host link fails undefined.
lake build Reactor.LoadBalance:c.o.export

# `Reactor.ServeStep` (the `drorb_serve_step` / `drorb_serve_resume` effect/
# continuation seam) is likewise imported by Dataplane but lives in the `Reactor`
# lib, so compile its export object explicitly — otherwise the two new exports and
# `initialize_Reactor_ServeStep` are absent from the archive and the host link
# fails undefined.
lake build Reactor.ServeStep:c.o.export

# `Reactor.ProxyStreamHead` (the CL-trust head-independence seam behind
# `drorb_serve_proxy_stream_head`: `proxyStreamHead`, proven by `proxyRespHead_factors`
# to be a function of (input, upstream-head, body-LENGTH)) is imported by Dataplane but
# lives in the `Reactor` lib, so compile its export object explicitly — otherwise the new
# export and `initialize_Reactor_ProxyStreamHead` are absent from the archive and the host
# link fails undefined.
lake build Reactor.ProxyStreamHead:c.o.export

# `Reactor.ServeStream` (the sans-IO streaming serve behind `drorb_serve_stream`:
# `serveChunkList` / `paceBody` / `keepAliveOf`) is imported by Dataplane but lives in
# the `Reactor` lib, so compile its export object explicitly — otherwise the streaming
# serve's definitions and `initialize_Reactor_ServeStream` are absent from the archive
# and the host link fails undefined.
lake build Reactor.ServeStream:c.o.export

# `Reactor.ServeArr` (the bridged flat `ByteArray -> ByteArray` serve behind
# `drorb_serve_flat`: `serveArr` / `serializeArr`, proven byte-identical to the
# deployed List serve) is imported by Dataplane but lives in the `Reactor` lib, so
# compile its export object explicitly — otherwise `drorb_serve_flat` and
# `initialize_Reactor_ServeArr` are absent from the archive and the host link
# fails undefined.
lake build Reactor.ServeArr:c.o.export

# `Reactor.SerializeFast` (the flat ByteArray head-builder `serializeHeadAcc`, proven
# `serialize_eq_fast`) is imported by `Reactor.ServeArr`, so its export object
# (`initialize_Reactor_SerializeFast` / `serializeHeadAcc`) must be compiled explicitly too
# — otherwise a FROM-SCRATCH host link fails undefined (a warm .lake cache masks it).
lake build Reactor.SerializeFast:c.o.export

# `Client.H2Receive` (the H2 client receive loop, archived into libdrorb.a) imports
# `H2.FlowWindow` + `H2.RespTrailers` (the WINDOW_UPDATE + trailer-receive close) which
# transitively pull `H2.PseudoHeader` and the H2 frame/hpack/stream chain. These H2 leaf
# modules are NOT in the `Dataplane` serve closure the computed list walks, but their
# `initialize_H2_*` are referenced by the archived `Client.H2Receive` object — so build
# their export objects explicitly, else a FROM-SCRATCH host link fails undefined (a warm
# .lake cache masks it). The `+` prefix forces the MODULE target (H2 is also a lib name).
lake build +H2.FlowWindow:c.o.export +H2.RespTrailers:c.o.export +H2.PseudoHeader:c.o.export \
           +H2.Frame:c.o.export +H2.Hpack:c.o.export +H2.Stream:c.o.export +H2.Basic:c.o.export \
           +H2.Ext:c.o.export

# `Datapath.Serve` defines `Datapath.SpanBytes` (the borrowed-window type the streaming
# serve accumulates and paces over: `denote` / `full`) and its initializer. It is a new
# import of `Reactor.ServeStream` (not previously in the `drorb_serve` closure), so
# compile its export object explicitly — otherwise `initialize_Datapath_Serve` /
# `l_Datapath_SpanBytes_denote` / `l_Datapath_SpanBytes_full` are undefined at the host
# link. Its `Datapath` closure (`Span` — where `SpanBytes.denote`/`full` are defined —
# plus `Scan` / `Refine`) lives in the same lib and is likewise not in the prior
# `drorb_serve` closure, so compile each export object explicitly too.
lake build Datapath.Span:c.o.export
lake build Datapath.Scan:c.o.export
lake build Datapath.Refine:c.o.export
lake build Datapath.Serve:c.o.export

# `Datapath.Refine` imports the `Uring` recycle-conservation chain
# (`RecycleOnce` -> `Conservation` -> `Lts` -> `Basic`); their initializers are pulled
# into the `Datapath.Serve` closure the streaming serve depends on, so compile each
# export object explicitly (they are not in the prior `drorb_serve` closure).
lake build Uring.Basic:c.o.export
lake build Uring.Lts:c.o.export
lake build Uring.Conservation:c.o.export
lake build Uring.RecycleOnce:c.o.export

# `Dsl.Config.Parse` (the textual-config parser + `denoteOn` / `dialChainOfByte`,
# behind `drorb_deployment_of_config` / `drorb_serve_step_pol`) is imported by
# Dataplane but lives in the `Dsl` lib, so compile its export object explicitly —
# otherwise the config parser's definitions and `initialize_Dsl_Config_Parse` are
# absent from the archive and the host link fails undefined.
lake build Dsl.Config.Parse:c.o.export

# `Reactor.App` and `Reactor.ProxyServe` define / exhaustively match the `Handler`
# inductive (whose config-representable variants — proxy/redirect/respond/static —
# the config route table denotes). They live in the `Reactor` lib, so
# `Dataplane:static` does NOT rebuild their `.c.o.export` when only these change; a
# stale object would mis-tag a new `Handler` constructor at runtime (e.g. serve a
# config `redirect` route as the request-blind default). Compile them explicitly so
# the archived objects match the current `Handler` layout.
lake build Reactor.App:c.o.export
lake build Reactor.ProxyServe:c.o.export

# `Reactor.Deploy` carries the deployed serve folds — `servePipelineFull2`,
# `servePipelineFull2Metered`, the config-driven `servePipelineOf`, and the Braid-0
# `servePipelineOfMetered` (the config-driven METERED serve `drorb_serve_metered_cfg`
# crosses). It lives in the `Reactor` lib, so `Dataplane:static` contributes its
# `.olean` but NOT its `.c.o.export`; a stale object omits `servePipelineOfMetered`
# and the metered-cfg seam fails to link. Compile it explicitly.
lake build Reactor.Deploy:c.o.export

# `Reactor.ObserveFast` carries the `@[csimp]` that installs the O(N) `corrBytesFast`
# as the COMPILED body of `Reactor.Deploy.corrBytes` (the per-request `x-corr`
# render). It is imported by Dataplane but lives in the `Reactor` lib, so
# `Dataplane:static` contributes its `.olean` but NOT its `.c.o.export`. Without the
# object, `initialize_Dataplane` references an undefined `initialize_Reactor_ObserveFast`
# and the compiled `corrBytes` cannot reach `corrBytesFast`. Compile it explicitly.
lake build Reactor.ObserveFast:c.o.export

# `Reactor.Proxy.Connect` (`drorb_connect_gate`, the CONNECT admission gate) and
# `Reactor.Proxy.Grpc` (`drorb_grpc_frame_len`, the gRPC frame-header parse) are
# imported by Dataplane but live in the `Reactor` lib, so `Dataplane:static` does
# NOT rebuild their `.c.o.export`; compile each explicitly so the two exports and
# their `initialize_*` are archived and the host link resolves.
lake build Reactor.Proxy.Connect:c.o.export
lake build Reactor.Proxy.Grpc:c.o.export

# `Reactor.RouteMiddleware` (the per-route middleware gates: `bearerAuth` /
# `ipAllow` / `rate` / `deny`, and `mwOfClause` the config denotation calls) is
# imported by `Reactor.App` but lives in the `Reactor` lib, so `Dataplane:static`
# contributes its `.olean` but NOT its `.c.o.export`. A stale object would omit a
# newly wired gate (e.g. `mwOfClause`, `ipAllow`, `rate`) and the host link fails
# undefined. Compile it (and its proven-decision deps `IpFilter` / `Rate`)
# explicitly so the archived object matches the current middleware surface. Its
# proven-decision deps (`IpFilter` / `Rate`) are unchanged and already archived.
lake build Reactor.RouteMiddleware:c.o.export

# `Reactor.H2Response` and `Reactor.H2Ingress` (the h2c serve: `serveH2c` routes the
# decoded H2 request through the full 13-stage fold and `encodeResponse` emits the
# HTTP/2 frames) are imported by Dataplane but live in the `Reactor` lib, so their
# `.c.o.export` objects are NOT rebuilt by `Dataplane:static` when only these modules
# change — a stale object would silently ship the old h2c serve. Compile them
# explicitly so a rebuild picks up any change on the h2c response path.
lake build Reactor.H2Response:c.o.export
lake build Reactor.H2Ingress:c.o.export

# The verified TLS 1.3 server closure behind the `drorb_tls_serve` HTTPS front
# door (Dataplane imports `TlsHandshake.Post`). These modules live OUTSIDE the
# Dataplane lib, so `Dataplane:static` contributes their `.olean` but not their
# `.c.o.export` objects; compile each explicitly so the handshake + record layer
# and the verified `Crypto` primitives (the @[extern] seam) are archived and the
# new export links. `Crypto` also carries the @[extern] declarations the host's
# crypto backend (ffi/crypto_shim.o + libaes_fallback.a + libevercrypt.a) resolves.
# The `+Module` prefix forces the MODULE target's facet (not the same-named
# library's) for `Crypto` / `TlsCrypto` / `TlsHandshake`, which are each both a
# lean_lib and a module.
lake build +Crypto:c.o.export
lake build +Tls.Basic:c.o.export
lake build +Tls.Step:c.o.export
lake build +Tls.Theorems:c.o.export
lake build +TlsCrypto:c.o.export
# `TlsCrypto.Sig` — the RFC 8446 §9.1 RSA-PSS / ECDSA-P256 CertificateVerify
# signers the deployed multi-cert pool instantiates (`Dataplane.deployedCerts`).
# Its `.c.o.export` carries `TlsCrypto.Sig.ecdsaP256Sign` / `rsaPssSign` and the
# @[extern] declarations (`drorb_p256_ecdsa_sign`, `drorb_rsapss_sha256_sign`)
# resolved against `ffi/tls_p256_shim.o`.
lake build +TlsCrypto.Sig:c.o.export
lake build +TlsHandshake:c.o.export
lake build +TlsHandshake.Post:c.o.export

# The verified outbound (client) seam: `drorb_response_parse` /
# `drorb_request_serialize` (Client.H1) and their proven closure (the request
# serializer, response parser, and decimal inverse). These live in the
# `ProtoClient` lib, so `Dataplane:static` does not build their `.c.o.export`;
# compile each explicitly so the two client exports and their `initialize_*`
# are archived and the host's outbound path links.
lake build Proto.Decimal:c.o.export
lake build Proto.ResponseParse:c.o.export
lake build Proto.RequestSerialize:c.o.export
lake build Client.H1:c.o.export

# The verified H2 outbound (client) seam: `drorb_h2_request` /
# `drorb_h2_response` (Client.FetchExport) and their proven closure (the H2
# submit path `Client.H2`, the CONTINUATION-assembling receive `Client.H2Receive`,
# and the real HPACK Huffman decoder `H3.Qpack.huffmanDecode` from HuffmanCorrect).
# These live in the `ClientFetchExport` lib, so `Dataplane:static` does not build
# their `.c.o.export`; compile each explicitly so the two H2 client exports and
# their `initialize_*` are archived and the host's H2 outbound path links.
lake build H2.FrameEncode:c.o.export
lake build H2.HpackEncode:c.o.export
lake build Client.H2:c.o.export
# `H2.FlowWindow` (the HTTP/2 flow-control WINDOW_UPDATE accounting) and
# `H2.RespTrailers` (the response-trailer / gRPC-trailers assembly) are imported by
# `Client.H2Receive` but live in the `H2` lib, so `Dataplane:static` (and
# `Client.H2Receive:c.o.export`) do NOT build their `.c.o.export`; compile each
# explicitly so `initialize_H2_FlowWindow` / `initialize_H2_RespTrailers` /
# `H2.RespTrailers.grpcTrailers` are archived and `initialize_Client_H2Receive` links.
lake build H2.FlowWindow:c.o.export
lake build H2.RespTrailers:c.o.export
lake build Client.H2Receive:c.o.export
# `HuffmanCorrect` is both a lean_lib and a module (HuffmanCorrect.lean at the
# root), so force the MODULE target's facet with the `+` prefix (as the TLS
# targets do) — the library facet has no `c.o.export`.
lake build +HuffmanCorrect:c.o.export
lake build Client.FetchExport:c.o.export

out=".lake/build/lib/libdrorb.a"
rm -f "$out"
# All compiled Lean module objects (Mach-O, with exported symbols visible).
#
# `ar` names each member by BASENAME, so two modules with the same file name
# (`Arena/Parse` vs `Dsl/Config/Parse`, the many `Basic`/`Step`/`Theorems`
# modules, …) collide into same-named archive members. Apple ld64 keys members
# by name, so a symbol that lives ONLY in a shadowed same-named member can fail to
# resolve (undefined at link, even though `nm` shows it defined). Stage every
# object under a path-flattened UNIQUE name first, so no two members collide.
# A module that defines a top-level `main` (a live-selftest entry, e.g.
# `Route.StaticServe` — run via its own lean_exe / `lake env lean --run`)
# compiles to an object that DEFINES the C `main` symbol; archived as-is it
# collides with the host binary's own `main` at link. No archive member should
# ever export `main` to the host link, so localize it in the STAGED COPY (the
# exe targets link their own objects and are untouched). `objcopy -L` on an
# object without the symbol is a no-op.
stage="$(mktemp -d)"
while IFS= read -r -d '' f; do
  rel="${f#.lake/build/ir/}"
  staged="$stage/$(printf '%s' "$rel" | tr '/.' '__').o"
  cp "$f" "$staged"
  objcopy -L main "$staged"
done < <(find .lake/build/ir -name '*.c.o.export' -print0)
ar crs "$out" "$stage"/*.o
rm -rf "$stage"
echo "built $out ($(find .lake/build/ir -name '*.c.o.export' | wc -l | tr -d ' ') module objects)"
