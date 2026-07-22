#!/usr/bin/env bash
# The fail-closed fhEgg GPU correctness lane. Run on hbox, normally through:
#   scripts/hbuild gpu-e2e scripts/test-fhegg-wgpu-matrix.sh
set -euo pipefail

export DREGG_REQUIRE_WGPU=1

# Actual tfhe-rs default order and type boundary: KS -> transform PBS -> a
# reconstructed big-key FheUint32 that survives a subsequent high-level op.
cargo nextest run --release \
  -p fhegg-fhe \
  --test tfhe_high_level_wgpu \
  --no-capture

cargo nextest run --release \
  -p fhegg-fhe \
  --test wgpu_correctness_matrix \
  --run-ignored all \
  --no-capture

cargo nextest run --release \
  -p fhegg-fhe \
  --features amm-input-binding \
  --test private_book_bfv_wgpu_matrix \
  --run-ignored all \
  --no-capture
