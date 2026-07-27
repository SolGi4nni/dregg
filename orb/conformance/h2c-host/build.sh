#!/usr/bin/env bash
# Build the interactive h2c conformance host against the verified engine.
#
# Prerequisite: ffi/build-dataplane-lib.sh (compiles the Lean modules and
# archives .lake/build/lib/libdrorb.a — includes the drorb_h2c_conn_init/feed
# exports from Reactor/H2Ingress.lean).
#
# Links the same inputs the Rust dataplane host links: libdrorb.a, the Lean
# runtime (libleanshared), and — because the deployed serve closure reaches the
# Jwt gate / CGI route / QUIC header protection — the crypto shim, the CGI
# shim, mac_udp.o, the AES fallback, and HACL*/EverCrypt when present.
# HACL_DIST overrides the EverCrypt dist path (defaults to
# $HOME/src/hacl-star/dist/gcc-compatible).
set -euo pipefail
cd "$(dirname "$0")/../.."

LEAN_PREFIX="$(lean --print-prefix)"
HACL="${HACL_DIST:-$HOME/src/hacl-star/dist/gcc-compatible}"

extras=()
[ -f ffi/crypto_shim.o ] && extras+=(ffi/crypto_shim.o)
[ -f ffi/cgi_exec.o ] && extras+=(ffi/cgi_exec.o)
[ -f ffi/mac_udp.o ] && extras+=(ffi/mac_udp.o)
# The archive now pulls in the whole Dataplane module (incl. the TLS 1.3 server
# and its socket seam), so the C host must also resolve the socket FFI shims
# (drorb_tcp_send/recv, from derp_net) and the cert-signing shims
# (drorb_p256_ecdsa_sign / drorb_rsapss_sha256_sign, from tls_p256_shim) even
# though the h2c feed loop itself never calls them — the linker resolves the
# whole archive. Compile them if the prebuilt objects are absent.
[ -f ffi/derp_net.o ] || cc -O2 -I"$LEAN_PREFIX/include" -c ffi/derp_net.c -o ffi/derp_net.o
[ -f ffi/tls_p256_shim.o ] || cc -O2 -I"$LEAN_PREFIX/include" -c ffi/tls_p256_shim.c -o ffi/tls_p256_shim.o
extras+=(ffi/derp_net.o ffi/tls_p256_shim.o)
[ -f target/release/libaes_fallback.a ] && extras+=(target/release/libaes_fallback.a)
[ -f "$HACL/libevercrypt.a" ] && extras+=("-L$HACL" -levercrypt)

cc -O2 -I"$LEAN_PREFIX/include" \
  -o conformance/h2c-host/h2c-host \
  conformance/h2c-host/h2c_host.c \
  .lake/build/lib/libdrorb.a \
  "${extras[@]}" \
  -L"$LEAN_PREFIX/lib/lean" -lleanshared \
  -Wl,-rpath,"$LEAN_PREFIX/lib/lean"

echo "built conformance/h2c-host/h2c-host"
