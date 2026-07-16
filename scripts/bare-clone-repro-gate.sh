#!/usr/bin/env bash
# bare-clone-repro-gate.sh — Rung D2, the load-bearing falsifier for "works on my machine".
#
# It proves the tree builds from a BARE CLONE into an EMPTY home with NO sibling ~/dev
# repos and NO warm cargo cache. Every reproducibility escape the design names —
# a [patch]-to-sibling `path = "../..."`, an UNPUSHED fork rev, a re-floated mutable
# branch ref, a Cargo.lock out of sync with the manifest — turns this RED instead of
# staying "green on ember's laptop".
#
# Grounding (file:line at authoring, HEAD 8cb566090):
#   - The design + gate contract: docs/reference/REPRODUCIBLE-BUILD-AND-FREEZE.md
#     Rung D2 (§4, lines 189-201) and the falsifier framing (§6, 267-274).
#   - The refs this must hold immutable: Cargo.toml
#       * plonky3-recursion pure git rev (no sibling [patch]) — Cargo.toml:157-162,236-239
#       * proof-systems fork rev c5305e63 — Cargo.toml:173-176
#       * ark-serialize MUTABLE BRANCH pin (the last non-immutable ref) — Cargo.toml:180-181
#       * in-repo vendored [patch] paths that MUST travel with the clone —
#         pathfinder_simd Cargo.toml:190, servo-paint :197, servo-net :200
#   - default-members = the light protocol/circuit spine (no gpui/servo/mozjs) —
#     Cargo.toml:19-23. `cargo build` with no `--workspace` operates on THESE.
#
# WHY --locked: without it CI can silently regenerate Cargo.lock, re-floating the
#   mutable ark-serialize branch instead of proving the COMMITTED lock resolves
#   (REPRODUCIBLE-BUILD-AND-FREEZE.md §2.2, ci.yml:25,80,104,113 lack it today).
#   `--locked` freezes every ref to the committed lock; a lock that drifts from the
#   manifest is then a RED, not a silent regen.
#
# ── modes ──
#   ./scripts/bare-clone-repro-gate.sh                # GATE: metadata + light-spine build, offline-isolated
#   ./scripts/bare-clone-repro-gate.sh --full         # + full `cargo build --workspace --locked` (heavy: the elephants)
#   ./scripts/bare-clone-repro-gate.sh --canary        # prove the gate BARKS: inject a sibling path, assert RED
#   ./scripts/bare-clone-repro-gate.sh --metadata-only # cheapest falsifier: resolve the graph under --locked, no compile
#   ./scripts/bare-clone-repro-gate.sh --source <dir|url>  # clone from here (default: this repo's git toplevel)
#   ./scripts/bare-clone-repro-gate.sh --keep          # don't delete the temp sandbox (for debugging a red)
#
# ── isolation the gate enforces (this is the whole point) ──
#   HOME       = a fresh EMPTY temp dir      → so ~/dev has NO sibling repos
#   $HOME/dev  = created EMPTY               → a `path = "../sibling"` escape cannot resolve
#   CARGO_HOME = a fresh EMPTY temp dir      → forces a REAL fetch of every git dep;
#                                              an UNPUSHED fork rev fails to fetch → RED
#   RUSTUP_HOME= preserved (the installed toolchain is not a reproducibility variable here)
#   rust-cache = NEVER restored (in CI: this job must not use Swatinem/rust-cache)
#
# The clone is BARE in the honest sense: it captures the committed HEAD, never the
# dirty working tree — a stranger gets commits, not your unsaved edits. Run it BEFORE
# you push (source defaults to your local HEAD) to catch an escape a push would ship.
set -uo pipefail

# ── locate the source repo (git toplevel of this script) ──────────────────────────
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SOURCE_REPO="$(git -C "$SCRIPT_DIR" rev-parse --show-toplevel 2>/dev/null || true)"

MODE="gate"        # gate | full | canary | metadata-only
KEEP=0
while [ $# -gt 0 ]; do
  case "$1" in
    --full)          MODE="full" ;;
    --canary)        MODE="canary" ;;
    --metadata-only) MODE="metadata-only" ;;
    --source)        shift; SOURCE_REPO="${1:?--source needs a path or URL}" ;;
    --keep)          KEEP=1 ;;
    -h|--help)       sed -n '2,40p' "${BASH_SOURCE[0]}"; exit 0 ;;
    *) echo "unknown arg: $1" >&2; exit 2 ;;
  esac
  shift
done

if [ -z "${SOURCE_REPO:-}" ]; then
  echo "FATAL: could not determine the source repo. Pass --source <dir|url>." >&2
  exit 2
fi

# ── the isolated sandbox ──────────────────────────────────────────────────────────
SANDBOX="$(mktemp -d "${TMPDIR:-/tmp}/bare-clone-repro.XXXXXX")"
cleanup() { [ "$KEEP" = 1 ] && { echo "── sandbox kept at: $SANDBOX"; return; }; rm -rf "$SANDBOX"; }
trap cleanup EXIT

FAKE_HOME="$SANDBOX/home"          # EMPTY home → no ~/dev siblings
FAKE_CARGO="$SANDBOX/cargo"        # EMPTY cargo home → real fetch of every git dep
CLONE="$SANDBOX/clone"            # the bare-cloned tree we build
mkdir -p "$FAKE_HOME/dev" "$FAKE_CARGO"

# Preserve the toolchain home so nightly (rust-toolchain.toml `channel = "nightly"`)
# resolves without a reinstall; the toolchain is not the reproducibility variable D2
# is testing — sibling paths and mutable refs are.
REAL_RUSTUP="${RUSTUP_HOME:-$HOME/.rustup}"

# Every cargo invocation runs under the isolated env. RUSTUP keeps the toolchain;
# HOME/CARGO_HOME are the empty ones that make the falsifier real.
run_cargo() {
  env -i \
    PATH="$PATH" \
    HOME="$FAKE_HOME" \
    CARGO_HOME="$FAKE_CARGO" \
    RUSTUP_HOME="$REAL_RUSTUP" \
    CARGO_TERM_COLOR="${CARGO_TERM_COLOR:-always}" \
    CARGO_INCREMENTAL=0 \
    CARGO_NET_GIT_FETCH_WITH_CLI="${CARGO_NET_GIT_FETCH_WITH_CLI:-false}" \
    ${CARGO_PROFILE_DEV_DEBUG:+CARGO_PROFILE_DEV_DEBUG="$CARGO_PROFILE_DEV_DEBUG"} \
    ${CARGO_PROFILE_TEST_DEBUG:+CARGO_PROFILE_TEST_DEBUG="$CARGO_PROFILE_TEST_DEBUG"} \
    cargo "$@"
}

echo "════════════════════════════════════════════════════════════════════════════════"
echo " bare-clone reproducibility gate (Rung D2)"
echo "   source repo : $SOURCE_REPO"
echo "   mode        : $MODE"
echo "   sandbox     : $SANDBOX"
echo "   HOME        : $FAKE_HOME        (empty; \$HOME/dev has no siblings)"
echo "   CARGO_HOME  : $FAKE_CARGO       (empty; forces a real fetch of every git dep)"
echo "════════════════════════════════════════════════════════════════════════════════"

# ── clone the COMMITTED HEAD (never the dirty working tree) ────────────────────────
# --no-local defeats git's local-clone hardlink optimization so the clone is a real,
# independent tree (no object sharing that could mask a source-path leak).
echo "── cloning committed HEAD into the empty sandbox ─────────────────────────────"
if ! git clone --no-local --quiet "$SOURCE_REPO" "$CLONE" 2>/dev/null; then
  # URLs / non-local sources can't use --no-local; fall back.
  git clone --quiet "$SOURCE_REPO" "$CLONE"
fi
CLONE_HEAD="$(git -C "$CLONE" rev-parse HEAD)"
echo "   cloned HEAD : $CLONE_HEAD"
# Pull LFS objects (staged TSV descriptor registries are LFS — REPRODUCIBLE-BUILD §2.1;
# a fresh clone needs them or the include_str! sites break). Best-effort: skip if no LFS.
if command -v git-lfs >/dev/null 2>&1; then
  ( cd "$CLONE" && git lfs pull >/dev/null 2>&1 || true )
fi
cd "$CLONE"

# ── canary: prove the gate can go RED (mirror-gates discipline) ────────────────────
# A gate that cannot bark is worse than none (scripts/check-mirror-gates.sh). We inject
# the exact escape D2 exists to catch — a [patch] pointing at a sibling path that does
# NOT exist in the empty ~/dev — and REQUIRE the resolve to fail.
if [ "$MODE" = "canary" ]; then
  echo "── canary: injecting a sibling-path [patch] that must NOT resolve ────────────"
  # The EXACT escape D2 exists to catch: re-point a plonky3 crate (real git dep,
  # Cargo.toml:213) at a sibling `path` that isn't in the empty ~/dev. A FRESH patch
  # table (the repo patches crates-io + proof-systems, NOT the Plonky3 URL), so this is
  # a real resolution failure, not a duplicate-key TOML error.
  cat >> Cargo.toml <<'CANARY'

# ── injected by bare-clone-repro-gate.sh --canary (NOT committed) ──
[patch."https://github.com/Plonky3/Plonky3"]
p3-air = { path = "../__canary_sibling_does_not_exist__/p3-air" }
CANARY
  # Resolve WITHOUT --locked so cargo proceeds to LOAD the sibling path (rather than
  # short-circuiting on the lock/manifest drift the injection also causes). The red we
  # require is "failed to load source for dependency `p3-air` ... does not exist" —
  # verified: `cargo metadata` (with deps) reds on exactly this; `--no-deps` does not.
  if run_cargo metadata --format-version 1 >/dev/null 2>"$SANDBOX/canary.err"; then
    echo
    echo "✗ CANARY FAILED: a sibling-path [patch] into an empty ~/dev RESOLVED anyway."
    echo "  The gate is NOT actually isolated — its GREEN would carry no information."
    echo "  (env leaked a real sibling, or CARGO_HOME/HOME isolation is broken.)"
    exit 1
  fi
  echo "   ✓ resolve failed as required. The load-bearing error:"
  grep -iE 'failed to load source|does not exist|No such file|__canary_sibling' "$SANDBOX/canary.err" \
    | head -4 | sed 's/^/     /' \
    || { echo "     (see full log:)"; tail -4 "$SANDBOX/canary.err" | sed 's/^/     /'; }
  echo
  echo "✓ CANARY PASSED: an injected sibling-path escape turns this gate RED."
  exit 0
fi

# ── stage 1: resolve the graph under --locked (the cheapest, sharpest falsifier) ──
# `cargo metadata --locked` resolves the ENTIRE workspace graph against the COMMITTED
# Cargo.lock, fetching every git dep into the fresh CARGO_HOME. This alone reds on:
#   * any [patch] with a `path = "../sibling"` that isn't in the (empty) ~/dev
#   * any git dep whose rev/branch isn't fetchable (an unpushed fork)
#   * a Cargo.lock that drifted from Cargo.toml (--locked refuses to regenerate)
echo "── stage 1: cargo metadata --locked (resolve the whole graph, offline-isolated) ──"
if ! run_cargo metadata --locked --format-version 1 >/dev/null; then
  echo
  echo "✗ RED at RESOLUTION. The committed Cargo.lock does not resolve from a bare clone"
  echo "  into an empty ~/dev. This is a reproducibility escape — a sibling path, an"
  echo "  unpushed rev, a re-floated branch, or a lock/manifest drift. Re-run with --keep"
  echo "  and inspect: cd $CLONE && cargo metadata --locked"
  exit 1
fi
echo "   ✓ the committed lock resolves with no sibling and no unpushed ref."

if [ "$MODE" = "metadata-only" ]; then
  echo
  echo "✓ GATE (metadata-only) GREEN for $CLONE_HEAD."
  exit 0
fi

# ── stage 2: compile the light protocol/circuit spine (default-members) ───────────
# `cargo build --locked` with no --workspace builds default-members only (Cargo.toml:19-23):
# the light spine, gpui/servo/mozjs-free, the set a stranger reproduces first. This is
# where the plonky3-recursion sibling-[patch] escape lived, so it is the load-bearing
# compile.
echo "── stage 2: cargo build --locked (default-members = the light spine) ─────────"
if ! run_cargo build --locked; then
  echo
  echo "✗ RED at COMPILE (light spine). The graph resolved but the tree does not build"
  echo "  from a bare clone. Re-run with --keep and inspect: cd $CLONE && cargo build --locked"
  exit 1
fi
echo "   ✓ the light spine compiles from a bare clone into an empty ~/dev."

# ── stage 3 (--full): the whole workspace, elephants included ─────────────────────
# `--workspace` pulls the gpui/servo/mozjs crates whose [patch] entries point at IN-REPO
# vendored dirs (pathfinder_simd, servo-paint, servo-net — Cargo.toml:190,197,200); those
# MUST travel with the clone. A missing vendored path reds here. HEAVY: this is the whole
# tree with no cache; provision disk + a long timeout (see the workflow / the runbook).
if [ "$MODE" = "full" ]; then
  echo "── stage 3: cargo build --workspace --locked (the elephants; heavy, no cache) ──"
  if ! run_cargo build --workspace --locked; then
    echo
    echo "✗ RED at COMPILE (--workspace). A whole-tree escape — most likely a vendored"
    echo "  [patch] path that did not travel with the clone. Re-run with --keep:"
    echo "  cd $CLONE && cargo build --workspace --locked"
    exit 1
  fi
  echo "   ✓ the whole workspace compiles from a bare clone."
fi

echo
echo "════════════════════════════════════════════════════════════════════════════════"
echo "✓ GATE GREEN for $CLONE_HEAD ($MODE)."
echo "  A stranger's bare clone into an empty ~/dev reproduces this build."
echo "════════════════════════════════════════════════════════════════════════════════"
