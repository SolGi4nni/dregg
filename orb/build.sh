#!/usr/bin/env bash
# Build the Orb: the leanc-compiled proven serve (libdrorb.a) + the native
# Rust dataplane that drives it over real sockets. Produces
# target/release/dataplane. Idempotent; re-run after editing sources.
set -euo pipefail
cd "$(dirname "$0")"

# --- Prerequisite: the F*-verified HACL*/EverCrypt crypto backend -------------
# Point HACL_DIST at a built hacl-star/dist/gcc-compatible (it provides
# libevercrypt.a + the headers). See README.md.
: "${HACL_DIST:?set HACL_DIST=/path/to/hacl-star/dist/gcc-compatible}"
export LIBRARY_PATH="$HACL_DIST${LIBRARY_PATH:+:$LIBRARY_PATH}"
export DYLD_LIBRARY_PATH="$HACL_DIST${DYLD_LIBRARY_PATH:+:$DYLD_LIBRARY_PATH}"

echo "==> 1/4  FFI shims the dataplane link pulls (crypto, signatures, cgi, derp, udp)"
bash ffi/build-aes-fallback.sh      # target/release/libaes_fallback.a
bash ffi/build-crypto-shim.sh       # ffi/crypto_shim.o
bash ffi/build-tls-p256-shim.sh     # ffi/tls_p256_shim.o
bash ffi/build-cgi-shim.sh          # ffi/cgi_exec.o
bash ffi/build-derp-net.sh          # ffi/derp_net.o  (TLS front door TCP byte-mover)
bash ffi/build-mac-multi.sh         # ffi/mac_udp.o   (macOS UDP shim)

echo "==> 2/4  the proven serve -> .lake/build/lib/libdrorb.a  (leanc; slow on a cold tree)"
# Compile the whole serve closure first via the native IO executable — its Lean
# import closure IS the serve's, so this populates every module object the archive
# needs. (build-dataplane-lib.sh then archives the export objects; on its own, cold,
# it only sees the handful of modules it names explicitly.)
case "$(uname)" in
  Darwin) lake build orb-mac ;;
  Linux)  lake build orb-linux ;;
  *) echo "unsupported OS — build the IO exe for your platform (see lakefile.toml)"; exit 1 ;;
esac
bash ffi/build-dataplane-lib.sh

echo "==> 3/4  the native dataplane host"
( cd crates/dataplane && cargo build --release )

echo "==> 4/4  done"
echo "binary: $(pwd)/target/release/dataplane"
echo "run:    DRORB_CONFIG=./sample.cfg ./target/release/dataplane 127.0.0.1:8080"
