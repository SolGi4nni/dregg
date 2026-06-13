#!/usr/bin/env bash
# Build + test the cap-gradation bridge into a LOCAL target dir, so it never
# touches the repo-root ./target that a node lane owns. The bridge path-depends
# on the real dregg crates (cell/turn/types) for genuine attenuation; cargo
# builds those into THIS local target, not the root workspace's.
set -euo pipefail
cd "$(dirname "$0")"
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$PWD/target}"
echo "[firmament] CARGO_TARGET_DIR=$CARGO_TARGET_DIR"
cargo test "$@"
