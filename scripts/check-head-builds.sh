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

# ── SCOPE ─ this printf is the ONLY copy; it prints on every run, pass or fail. ───────
printf 'ANSWERS:         %s\nDOES NOT ANSWER: %s\n' \
  'does the named commit — cloned with --shared into a temp dir and checked out detached, so the shared working tree is never read — pass cargo check --workspace --all-targets --keep-going with the three cdylib members excluded, having actually compiled at least half as many units as the workspace has members?' \
  'whether HEAD is correct, or whether the working tree builds. It is a type-check only: no test is run, no binary is linked, and nothing is proved. The three excluded members (deos-zed, grain-verify-wasm, starbridge-web) are never checked at all, so a break confined to one of them is invisible here. And a green says the commit compiles, not that it behaves.'

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
  #  ⚑ KEEP THE LOG WHEN ASKED. The one thing a reader always wants after a red here is the FULL
  #  rustc output, and this script deleted it on exit — so the second run costs another whole
  #  workspace check to see what the first already knew.
  if [ -n "${HEADBUILD_KEEP_LOG:-}" ]; then
    cp "$LOG" "$HEADBUILD_KEEP_LOG" && echo "  copied to $HEADBUILD_KEEP_LOG"
  fi
  exit 1
fi

# ── ⚑ THE NON-VACUITY FLOOR ────────────────────────────────────────────────────────────────────
# "HEAD builds" is a NEGATIVE assertion — no errors — and every negative assertion passes just as
# happily over a workspace that compiled NOTHING. `cargo check` exits 0 and prints `Finished` when
# every unit is already fresh, so a target directory inherited from elsewhere (a stray
# `CARGO_TARGET_DIR` in the environment, a clone that landed on a warm cache) turns this whole gate
# into a no-op that reads exactly like a pass. That is the same shape as a lakefile glob that killed
# every build at [0/0] while 817 pins "ran".
#
# So: a clone with a FRESH target directory must compile essentially the whole workspace, and the
# floor is stated against the member count rather than a magic number. Measured 2026-08-06 on a
# clean clone: 226 workspace members, well over a thousand Compiling/Checking lines with deps.
units=$(grep -cE "^\s+(Compiling|Checking) " "$LOG" || true)
members=$(cd "$WORK/tree" && cargo metadata --no-deps --format-version 1 2>/dev/null \
            | python3 -c 'import json,sys; print(len(json.load(sys.stdin)["packages"]))' 2>/dev/null || echo 0)
FLOOR=$(( members > 0 ? members / 2 : 50 ))
if [ "$units" -lt "$FLOOR" ]; then
  echo
  echo "check-head-builds: FAIL (VACUOUS) — cargo reported success having compiled only $units unit(s)"
  echo "  against a floor of $FLOOR (half of $members workspace members). A fresh clone compiles"
  echo "  everything; a run this small did not check HEAD, it checked a cache. Suspect an inherited"
  echo "  CARGO_TARGET_DIR. A green over an empty population is the failure this floor refuses."
  exit 1
fi
echo "check-head-builds: PASS — $(git rev-parse --short "$SHA") builds clean from a detached clone"
echo "  ($units unit(s) compiled over $members workspace members; floor $FLOOR)."
