#!/usr/bin/env bash
# bootstrap.sh — from a fresh clone to a working verified-executor build, one command.
#
#   ./scripts/bootstrap.sh
#
# What this does (idempotent — every step skips itself when already satisfied):
#   1. checks the toolchain prerequisites (cargo, elan/lake) and TEACHES the fix when absent;
#   2. checks the mathlib checkout the Lean build requires (metatheory/lakefile.toml pins
#      mathlib as a LOCAL PATH dependency — a fresh machine does not have it);
#   3. `lake build`s the verified executor's FFI module (incremental; the FIRST run compiles
#      mathlib and takes a long time — see the note printed at that step);
#   4. seeds dregg-lean-ffi/libdregg_lean.a (the static archive of the compiled Lean kernel;
#      ~6000 objects, one-time — afterwards `cargo build` keeps it fresh automatically);
#   5. verifies the result by running the FFI smoke binary: Rust calls the PROVED Lean
#      kernel over the C ABI and asserts conservation/authority round-trips.
#
# Without this, `cargo build` still SUCCEEDS — but in a degraded "marshal-only" mode where
# `lean_available()` is false and the node falls back to the unverified Rust executor.
# The whole point of dregg is that the verified Lean executor IS the executor; run this once.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
META="$ROOT/metatheory"
ARCH="$ROOT/dregg-lean-ffi/libdregg_lean.a"

step()  { printf '\n==> %s\n' "$*"; }
die()   { printf '\nFATAL: %s\n' "$*" >&2; exit 1; }

# ── 1. prerequisites ─────────────────────────────────────────────────────────
step "Checking prerequisites"

command -v cargo >/dev/null 2>&1 || die "cargo not on PATH.
  Install Rust via rustup:  curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
  (the repo's rust-toolchain.toml pins the exact toolchain; rustup picks it up automatically)"

command -v lake >/dev/null 2>&1 || die "lake (the Lean 4 build tool) not on PATH.
  Install elan (the Lean toolchain manager):
      curl https://elan.lean-lang.org/elan-init.sh -sSf | sh     # or: brew install elan-init
  then re-open your shell (elan puts ~/.elan/bin on PATH) and re-run this script.
  elan will auto-install the pinned toolchain ($(cat "$META/lean-toolchain" 2>/dev/null || echo 'see metatheory/lean-toolchain')) on first use."

echo "  cargo: $(command -v cargo)"
echo "  lake:  $(command -v lake)"

# ── 2. the mathlib git dependency (portable — no host-specific path) ──────────
# metatheory/lakefile.toml requires mathlib as a PORTABLE `git`+`rev` dependency:
# `lake` fetches it into metatheory/.lake/packages/mathlib on ANY host, with no
# assumption about where breadstuffs was cloned. The FIRST fetch of mathlib's
# prebuilt oleans (`lake exe cache get`) is minutes; compiling mathlib from source
# (if the cache is unavailable) is hours.
#
# LOCAL FAST PATH: if you already have a warm mathlib checkout at the pinned rev,
# symlink it into the packages dir BEFORE the first build so lake reuses it:
#     ln -sfn /path/to/your/mathlib4 metatheory/.lake/packages/mathlib
step "Checking the mathlib git dependency"

# The pinned revision is the 40-hex sha in metatheory/lakefile.toml (the `rev =` line).
MATHLIB_REV="$(grep -oE '[0-9a-f]{40}' "$META/lakefile.toml" | head -1 || true)"
MATHLIB_DIR="$META/.lake/packages/mathlib"
echo "  mathlib pin: ${MATHLIB_REV:-<see metatheory/lakefile.toml>} (git dependency)"

# Pull mathlib's PREBUILT oleans if they are not already present (minutes, not the
# hours-long from-source compile). `lake exe cache get` also materialises the mathlib
# git checkout as a side effect on a fresh box. We only run it when the oleans are
# missing, so a warm/symlinked checkout (e.g. a maintainer's) is left untouched.
if [ ! -e "$MATHLIB_DIR/.lake/build/lib/lean/Mathlib.olean" ]; then
  step "Fetching prebuilt mathlib oleans (lake exe cache get — minutes; avoids the hours-long compile)"
  if ! ( cd "$META" && lake exe cache get ); then
    echo "  WARNING: 'lake exe cache get' did not complete. The next 'lake build' will fetch"
    echo "           mathlib and, if no prebuilt cache is available for this rev, COMPILE it"
    echo "           from source (hours). Re-run this script once network/cache is available."
  fi
else
  echo "  mathlib oleans: present ($MATHLIB_DIR) — skipping cache fetch"
fi

# ── 3. build the verified executor (Lean → C facets) ────────────────────────
step "lake build Dregg2.Exec.FFI (incremental; FIRST run compiles mathlib — long)"
( cd "$META" && lake build Dregg2.Exec.FFI ) \
  || die "lake build failed. Common causes:
  * mathlib checkout at the wrong revision (see the pin check above);
  * a partial earlier build — re-running this script resumes it (lake is incremental)."

# ── 4. seed the static archive (one-time) ────────────────────────────────────
if [ -f "$ARCH" ]; then
  step "libdregg_lean.a already present ($(du -h "$ARCH" | cut -f1 | tr -d ' ')) — skipping the seed"
  echo "  (this seed is read-only; cargo build copies it into OUT_DIR and keeps THAT copy's"
  echo "   Dregg2 objects fresh automatically. To re-seed from scratch — only needed when the"
  echo "   toolchain/mathlib pin changes — delete it and re-run, or run"
  echo "   dregg-lean-ffi/scripts/seed-dregg2-closure.sh directly.)"
else
  step "Seeding dregg-lean-ffi/libdregg_lean.a (one-time; compiles the whole closure)"
  "$ROOT/dregg-lean-ffi/scripts/seed-dregg2-closure.sh"
fi

# ── 5. verify: Rust calls the proved Lean kernel for real ───────────────────
step "Verification: cargo builds the FFI crate and the smoke binary round-trips the kernel"
CHECK_LOG="$(mktemp)"
# NOTE: the verification MUST pass `--features lean-lib` — that feature is what
# links `libdregg_lean.a` (without it the crate builds the degraded "marshal-only"
# path, and the smoke binary `dregg-lean-ffi` has `required-features = ["lean-lib"]`
# so it won't even be selected). Omitting the flag here false-fails a kernel that
# is in fact linkable (the Lunar Town Council Fork-B finding, 2026-06-22).
if ! ( cd "$ROOT" && cargo build -p dregg-lean-ffi --features lean-lib 2>&1 | tee "$CHECK_LOG" ); then
  die "cargo build -p dregg-lean-ffi --features lean-lib failed — see output above."
fi
if grep -q "marshal-only" "$CHECK_LOG"; then
  die "the FFI crate still built MARSHAL-ONLY (the Lean kernel is not linked).
  Read the cargo warnings above — they name the exact missing piece."
fi
( cd "$ROOT" && cargo run -q -p dregg-lean-ffi --features lean-lib --bin dregg-lean-ffi ) \
  || die "the FFI smoke binary failed — the linked Lean kernel did not round-trip."

step "DONE. The verified Lean executor is linked and answering."
echo "  Next: QUICKSTART.md (build the CLI, run a node, run the demo)."
