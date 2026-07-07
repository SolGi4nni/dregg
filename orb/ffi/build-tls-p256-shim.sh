#!/usr/bin/env bash
# Compile the P-256 TLS key-exchange shim (ffi/tls_p256_shim.c) to the object
# file the TLS conformance executables (`tls-wire-oracle`,
# `tls-handshake-selftest`) link via moreLinkArgs. Same recipe and trust
# ledger as ffi/build-crypto-shim.sh: HACL* verified C, KaRaMeL runtime
# headers, the active Lean toolchain's lean.h. Idempotent.
set -euo pipefail
cd "$(dirname "$0")/.."

TOOLCHAIN_INC="$(lean --print-prefix 2>/dev/null || true)/include"
if [ ! -f "$TOOLCHAIN_INC/lean/lean.h" ]; then
  TOOLCHAIN_INC="$HOME/.elan/toolchains/leanprover--lean4---v4.17.0/include"
fi

HACL_DIST="${HACL_DIST:-$HOME/src/hacl-star/dist/gcc-compatible}"
KRML="${KRML:-$HOME/src/hacl-star/dist/karamel}"

if [ ! -f "$HACL_DIST/Hacl_P256.h" ]; then
  echo "error: Hacl_P256.h not found under HACL_DIST=$HACL_DIST" >&2
  exit 1
fi

cc -O2 -fPIC \
   -I"$TOOLCHAIN_INC" \
   -I"$HACL_DIST" \
   -I"$KRML/include" \
   -I"$KRML/krmllib/dist/minimal" \
   -c ffi/tls_p256_shim.c \
   -o ffi/tls_p256_shim.o

echo "built ffi/tls_p256_shim.o (HACL* P-256 backend)"
