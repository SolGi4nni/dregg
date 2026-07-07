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

lake build Dataplane:static

# `Dataplane:static` compiles only the Dataplane lib's own modules
# (Dataplane, Dataplane.Multi) to objects; a transitive import contributes its
# `.olean` but not its `.c.o.export` object unless some `:static` target owns it.
# `Reactor.ProxyDial` (the `drorb_proxy_pick` reverse-proxy pick seam) is imported
# by Dataplane but lives in the `Reactor` lib, so compile its export object
# explicitly here — otherwise `drorb_proxy_pick` / `initialize_Reactor_ProxyDial`
# are absent from the archive and the host link fails undefined.
lake build Reactor.ProxyDial:c.o.export

# `Reactor.ServeStep` (the `drorb_serve_step` / `drorb_serve_resume` effect/
# continuation seam) is likewise imported by Dataplane but lives in the `Reactor`
# lib, so compile its export object explicitly — otherwise the two new exports and
# `initialize_Reactor_ServeStep` are absent from the archive and the host link
# fails undefined.
lake build Reactor.ServeStep:c.o.export

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

# The QUIC/HTTP-3 datagram fork (`drorb_serve_datagram`, referenced by the Rust
# dataplane's UDP path) reaches the QUIC transport + HTTP/3 modules, which live
# outside the Dataplane lib, so `Dataplane:static` does not emit their
# `.c.o.export`. Compile them explicitly — otherwise the host link fails
# undefined on `Quic_step` / `H3_decFrame` / `QuicServer` / the QUIC header
# protection seam. (`+Name` forces the module facet where a same-named lib exists.)
lake build Reactor.Quic:c.o.export
lake build Reactor.QuicIngress:c.o.export
lake build +QuicHeaderProt:c.o.export
lake build +Quic:c.o.export
lake build Quic.Basic:c.o.export
lake build Quic.Fsm:c.o.export
lake build Quic.Theorems:c.o.export
lake build +H3:c.o.export
lake build H3.Frame:c.o.export
lake build H3.Request:c.o.export
lake build +QuicServer:c.o.export

out=".lake/build/lib/libdrorb.a"
rm -f "$out"
# All compiled Lean module objects (Mach-O, with exported symbols visible).
find .lake/build/ir -name '*.c.o.export' -print0 | xargs -0 ar crs "$out"
echo "built $out ($(find .lake/build/ir -name '*.c.o.export' | wc -l | tr -d ' ') module objects)"
