#!/usr/bin/env bash
# ⚑ DOES **HEAD** BUILD — not your working tree.
#
# Measured 2026-07-31: `main` was broken at HEAD three separate times in one morning, and each time a
# `cargo check --workspace --all-targets` in the working tree reported **exit 0**.
#
# The reason is structural, not carelessness. In a shared-tree swarm the working tree is the UNION of
# every lane's in-flight work, so it routinely contains the fix for breakage you just committed, put
# there by a lane that hit it minutes earlier. **The working tree is systematically GREENER than HEAD**,
# and the more lanes are running the greener it is. That inverts the usual intuition, where the local
# tree is the risky one.
#
# The three, all found by a measurement lane building from a clean clone rather than by any local check:
#   * `perf/src/lib.rs` assigning a struct field deleted the same day (E0560)
#   * three `sdk/tests/*` doing the same, plus a `turn/tests/*` importing a deleted encoder (E0432)
#   * a `--only` commit that took a shared file's WHOLE content, shipping a sibling's Rust references
#     without the regenerated `layout_generated.rs` that defines them (E0425)
#
# ⚠ `--keep-going` is load-bearing. Without it a workspace check stops at the FIRST failing crate, so
# "I fixed the error" and "I fixed the errors" look identical — that is how the second break above hid
# four more behind one.
set -uo pipefail
cd "$(dirname "$0")/.."

REF="${1:-HEAD}"
SHA="$(git rev-parse "$REF")"
WORK="$(mktemp -d "${TMPDIR:-/tmp}/headbuild.XXXXXX")"
trap 'rm -rf "$WORK"' EXIT

echo "check-head-builds: cloning $REF ($(git rev-parse --short "$SHA")) into a detached checkout ..."
# `--shared` keeps this cheap: object storage is borrowed, only the worktree is new.
git clone --shared --quiet . "$WORK/tree" || { echo "check-head-builds: clone FAILED"; exit 2; }
git -C "$WORK/tree" checkout --quiet --detach "$SHA" || { echo "check-head-builds: checkout FAILED"; exit 2; }

# ⚠ `--workspace` is NOT runnable on Linux: `grain-verify-wasm` and `starbridge-web` declare `cdylib`
# and reach `dregg-lean-ffi`, whose rlib carries Lean's mimalloc with local-exec TLS —
# `rust-lld: relocation R_X86_64_TPOFF32 against _mi_heap_default cannot be used with -shared`, which
# is legal only in a main executable. CI's exclude set is mandatory, not incidental.
EXCLUDES=(--exclude deos-zed --exclude grain-verify-wasm --exclude starbridge-web)

LOG="$WORK/check.log"
( cd "$WORK/tree" && cargo check --workspace "${EXCLUDES[@]}" --all-targets --keep-going ) >"$LOG" 2>&1
rc=$?

if [ "$rc" -ne 0 ]; then
  echo
  echo "check-head-builds: FAIL — HEAD does not build, whatever your working tree says."
  echo
  grep -E "^error" "$LOG" | sort -u | head -40
  echo
  n=$(grep -cE "^error" "$LOG" || true)
  echo "  $n error line(s). Full log: $LOG (deleted on exit — copy it if you need it)"
  exit 1
fi
echo "check-head-builds: PASS — $(git rev-parse --short "$SHA") builds clean from a detached clone."
