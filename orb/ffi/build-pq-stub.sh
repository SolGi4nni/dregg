#!/usr/bin/env bash
# Compile ffi/pq_stub.c -> ffi/pq_stub.o: fail-closed post-quantum seam stubs
# (drorb_pq_ml_dsa_verify / drorb_pq_ml_kem_{encaps,decaps}) that the standalone
# pure-Lean serve exes link so the crypto-shim's PQ crossings resolve. The
# deployed dataplane binary links the REAL dregg-pq wire instead (not this object).
# Idempotent. No HACL/EverCrypt or Lean headers needed — pure C-ABI stubs.
set -euo pipefail
cd "$(dirname "$0")/.."
cc -O2 -fPIC -c ffi/pq_stub.c -o ffi/pq_stub.o
echo "built ffi/pq_stub.o (fail-closed PQ seam stubs for the standalone Lean serve exes)"
