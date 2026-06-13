#!/usr/bin/env bash
# build-image.sh — provision → relink → cargo → loader → add-payload, end to end,
# producing the bootable seL4 image that runs the VERIFIED executor turn.
#
#   ./scripts/build-image.sh
#   qemu-system-aarch64 -machine virt,virtualization=on -cpu cortex-a53 -m 3072M \
#     -nographic -serial mon:stdio -kernel out/dregg-executor-rootserver.img
#
# Prereqs: ../executor-pd/out (run that lane's closure + runtime build first),
# the aarch64-linux-gnu + aarch64-linux-musl cross GCCs, CMake+ninja, the vendored
# rust-sel4 at ~/sel4-sdk/rust-sel4, libclang.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$HERE/.."
OUT="$ROOT/out"
PFX="$ROOT/sel4-prefix"
RUST_SEL4="${RUST_SEL4:-/Users/ember/sel4-sdk/rust-sel4}"

echo "== [1/5] provision the seL4 substrate (kernel + seL4 musl + libsel4 headers) =="
bash "$HERE/provision-sel4.sh"

echo "== [2/5] relink the verified executor closure against the seL4 musl =="
bash "$HERE/relink-roottask.sh"

echo "== [3/5] cargo build the root-task PD (links the verified turn) =="
( cd "$ROOT"
  export SEL4_PREFIX="$PFX" SEL4_INCLUDE_DIRS="$PFX/libsel4/include"
  export SEL4_CONFIG="$PFX/libsel4/include/kernel/gen_config.json"
  export SEL4_PLATFORM_INFO="$PFX/support/platform_gen.yaml"
  export LIBCLANG_PATH=/opt/homebrew/opt/llvm/lib
  export CARGO_TARGET_DIR="$ROOT/target-roottask"
  cargo build --release
)
APP="$ROOT/target-roottask/aarch64-sel4-roottask-musl/release/dregg-executor-rootserver.elf"

echo "== [4/5] build the loader (+ add-payload tool) =="
bash "$HERE/build-loader.sh"
LOADER="$OUT/sel4-kernel-loader.elf"
ADDPAYLOAD="$OUT/loader-target/release/sel4-kernel-loader-add-payload"

echo "== [5/5] assemble the bootable image =="
"$ADDPAYLOAD" --loader "$LOADER" --sel4-prefix "$PFX" --app "$APP" \
  --out-file "$OUT/dregg-executor-rootserver.img"
echo "== DONE -> $OUT/dregg-executor-rootserver.img =="
ls -la "$OUT/dregg-executor-rootserver.img" | awk '{print "   size:", $5}'
echo "   boot: qemu-system-aarch64 -machine virt,virtualization=on -cpu cortex-a53 \\"
echo "           -m 3072M -nographic -serial mon:stdio -kernel $OUT/dregg-executor-rootserver.img"
