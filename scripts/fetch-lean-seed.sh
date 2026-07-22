#!/usr/bin/env bash
# fetch-lean-seed.sh — link a VERIFIED dregg-node in MINUTES by downloading a HEAD-matching,
# platform-native Lean seed archive from a GitHub release, instead of the long cold `lake`
# bootstrap that ./scripts/bootstrap.sh runs (the ~6000-object Dregg2+deps leanc compile —
# mathlib itself is NOT the cost: its prebuilt oleans arrive in minutes via `lake exe cache get`).
#
# WHAT THE SEED IS (and why fetching it is the highest-value self-host lever):
#   dregg-lean-ffi/libdregg_lean.a is a ~180 MB NATIVE static archive of the compiled Lean
#   executor + its ENTIRE mathlib/batteries/aesop/Qq dependency closure (~6000 objects). It is
#   gitignored (an architecture-native Mach-O/ELF blob — never a repo blob). A fresh clone that
#   runs `cargo build` WITHOUT it silently builds MARSHAL-ONLY (the UN-verified Rust executor).
#   Regenerating it from source is the expensive part of a verified build (thousands of leanc
#   compiles). This script downloads a prebuilt one instead.
#
# WHAT YOU STILL NEED (the seed is not self-sufficient):
#   * elan + the pinned Lean toolchain (metatheory/lean-toolchain) — the seed archive links
#     against the toolchain's Lean runtime/stdlib static libs. elan installs in minutes and does
#     NOT require compiling mathlib. Install it: curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
#   You do NOT need a mathlib checkout or compile (prebuilt oleans cover mathlib in minutes
#   anyway); the work the seed replaces is the long Dregg2-closure leanc compile.
#
# Usage:
#   scripts/fetch-lean-seed.sh                 # fetch + place the seed for this platform
#   scripts/fetch-lean-seed.sh --force         # re-fetch even if a seed is already present
#   scripts/fetch-lean-seed.sh --tag TAG       # override the release tag (default: the pin)
#   DREGG_SEED_TAG=TAG scripts/fetch-lean-seed.sh   # same, via env
#
# After this, build a verified node with:
#   DREGG_REQUIRE_LEAN=1 cargo build -p dregg-node --release
# (DREGG_REQUIRE_LEAN=1 makes the build FAIL LOUD rather than silently degrade to marshal-only.)
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
PIN="$ROOT/dregg-lean-ffi/lean-seed.pin"
DEST="$ROOT/dregg-lean-ffi/libdregg_lean.a"
KEYSH="$ROOT/scripts/lean-seed-key.sh"

FORCE=0
TAG_OVERRIDE="${DREGG_SEED_TAG:-}"
while [ $# -gt 0 ]; do
  case "$1" in
    --force) FORCE=1 ;;
    --tag)   TAG_OVERRIDE="${2:-}"; shift ;;
    -h|--help) sed -n '2,30p' "$0"; exit 0 ;;
    *) echo "unknown arg: $1" >&2; exit 2 ;;
  esac
  shift
done

say()  { printf '\n==> %s\n' "$*"; }
die()  { printf '\nFATAL: %s\n' "$*" >&2; exit 1; }
sha256_of() { if command -v sha256sum >/dev/null 2>&1; then sha256sum "$1" | cut -d' ' -f1; else shasum -a 256 "$1" | cut -d' ' -f1; fi; }

# ── read the pin ──────────────────────────────────────────────────────────────
[ -f "$PIN" ] || die "no pin at $PIN — is this a full checkout? (expected dregg-lean-ffi/lean-seed.pin)"
pin_get() { sed -n "s/^$1=//p" "$PIN" | head -1; }
PIN_TAG="$(pin_get TAG)"
PIN_TOOLCHAIN="$(pin_get LEAN_TOOLCHAIN)"
PIN_MATHLIB="$(pin_get MATHLIB_REV)"
PIN_DREGG="$(pin_get DREGG_TREE_HASH)"

TAG="${TAG_OVERRIDE:-$PIN_TAG}"

# ── compute this platform's expected asset + local provenance ─────────────────
[ -x "$KEYSH" ] || chmod +x "$KEYSH" 2>/dev/null || true
ASSET="$(bash "$KEYSH" --asset)"
eval "$(bash "$KEYSH" | sed 's/^/LOCAL_/')"   # LOCAL_KEY, LOCAL_PLATFORM, LOCAL_LEAN_TOOLCHAIN, LOCAL_MATHLIB_REV, LOCAL_DREGG_TREE_HASH
say "Platform $LOCAL_PLATFORM · toolchain $LOCAL_LEAN_TOOLCHAIN · seed key $LOCAL_KEY"
echo "    expected release asset: $ASSET"

# Warn (do not fail) if the committed pin drifted from the local source: the published seed may
# be stale relative to your checkout — the closure link may then need a warm local .lake.
if [ -n "$PIN_DREGG" ] && [ "$PIN_DREGG" != "$LOCAL_DREGG_TREE_HASH" ]; then
  echo "    WARNING: the pin's Dregg2 tree ($PIN_DREGG) != your checkout ($LOCAL_DREGG_TREE_HASH)."
  echo "             The pinned seed predates your Lean source; if the link fails on undefined"
  echo "             initializers, re-seed locally (./scripts/bootstrap.sh) or wait for a fresh seed."
fi

# ── already present? ──────────────────────────────────────────────────────────
if [ -f "$DEST" ] && [ "$FORCE" -eq 0 ]; then
  say "A seed is already present ($(du -h "$DEST" | cut -f1 | tr -d ' ')): $DEST"
  echo "    Leaving it (pass --force to re-fetch). Build with: DREGG_REQUIRE_LEAN=1 cargo build -p dregg-node --release"
  exit 0
fi

# ── no release cut yet ────────────────────────────────────────────────────────
if [ -z "$TAG" ]; then
  die "no published seed release for this repo yet (lean-seed.pin TAG is empty, and no --tag/\$DREGG_SEED_TAG given).

  The seed-fetch fast path needs a release to have been cut first. Two ways forward:

    (a) VERIFIED node the slow way — bootstrap the Lean seed locally (hours the first time,
        compiles mathlib):
            ./scripts/bootstrap.sh
        then:  DREGG_REQUIRE_LEAN=1 cargo build -p dregg-node --release

    (b) CUT a seed release so everyone else gets the fast path (needs a beefy build host —
        David's lassie): see docs/LEAN-SEED-ARTIFACT.md, section \"cutting a seed on lassie\".
        Once published + the pin is bumped, this script fetches it in minutes.

  Or build MARSHAL-ONLY (UN-verified Rust executor, fine for UI/dev) with a plain
  \`cargo build -p dregg-node\` and no seed."
fi

# ── download ──────────────────────────────────────────────────────────────────
command -v zstd >/dev/null 2>&1 || die "zstd not on PATH (needed to decompress the seed). Install: brew install zstd  /  apt-get install zstd"

TMP="$(mktemp -d "${TMPDIR:-/tmp}/dregg-seed.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
ZST="$TMP/$ASSET"
SUM="$TMP/$ASSET.sha256"

say "Fetching seed asset from release '$TAG' …"
REPO_SLUG="${DREGG_SEED_REPO:-}"   # e.g. owner/repo; default: infer from the git remote
if [ -z "$REPO_SLUG" ]; then
  origin="$(git -C "$ROOT" remote get-url origin 2>/dev/null || true)"
  REPO_SLUG="$(echo "$origin" | sed -E 's#(git@github.com:|https://github.com/)##; s#\.git$##')"
fi

fetched=0
if command -v gh >/dev/null 2>&1; then
  if gh release download "$TAG" ${REPO_SLUG:+--repo "$REPO_SLUG"} \
        --pattern "$ASSET" --pattern "$ASSET.sha256" --dir "$TMP" 2>/dev/null; then
    fetched=1
  fi
fi
if [ "$fetched" -eq 0 ]; then
  [ -n "$REPO_SLUG" ] || die "could not infer the GitHub repo (set \$DREGG_SEED_REPO=owner/repo)."
  base="https://github.com/$REPO_SLUG/releases/download/$TAG"
  echo "    gh unavailable/failed — falling back to curl from $base"
  curl -fSL "$base/$ASSET"        -o "$ZST" || die "download failed: $base/$ASSET
  (no asset named '$ASSET' on release '$TAG' — is a seed published for THIS platform + Lean HEAD?
   docs/LEAN-SEED-ARTIFACT.md explains the per-platform asset naming.)"
  curl -fSL "$base/$ASSET.sha256" -o "$SUM" || die "download of the checksum sidecar failed."
fi
[ -f "$ZST" ] || die "expected asset not present after download: $ZST"

# ── verify checksum ───────────────────────────────────────────────────────────
if [ -f "$SUM" ]; then
  want="$(awk '{print $1}' "$SUM" | head -1)"
  got="$(sha256_of "$ZST")"
  [ "$want" = "$got" ] || die "checksum MISMATCH for $ASSET
  expected $want
  got      $got
  Refusing to install a seed that does not match its published checksum (possible corruption/tamper)."
  echo "    checksum OK ($got)"
else
  echo "    WARNING: no .sha256 sidecar found for the asset — installing UNVERIFIED."
fi

# ── decompress + install atomically ──────────────────────────────────────────
say "Decompressing + installing → $DEST"
zstd -d -f -q "$ZST" -o "$TMP/libdregg_lean.a" || die "zstd decompress failed."
# Sanity: the archive must export both the load-bearing verified executor and
# every real PQ core. A core-less archive is not a verified-runtime seed: using
# it makes `dregg-pq` abort at first use (or requires the explicit unaudited
# escape hatch), even though the executor export alone is present.
NM="nm"; command -v nm >/dev/null 2>&1 || NM="llvm-nm"
if command -v "$NM" >/dev/null 2>&1; then
  # Read the symbol table ONCE into a variable, then match — do NOT pipe `$NM … | grep -q`.
  # Under this script's `set -o pipefail`, `grep -q` exits at the FIRST match and SIGPIPEs `$NM`
  # (exit 141), so pipefail reports the pipeline FAILED for a symbol that was FOUND. On a ~190MB
  # seed nm is always still writing when grep quits, so this fires EVERY time: the fast path died
  # with "lacks the verified-executor export" on a perfectly valid archive, and every consumer
  # silently fell through to building the corpus from source. It fails CLOSED, so it never risked
  # a bad install — it just made the good one impossible. (Same bug, same fix, as the export check
  # in .github/workflows/lean-seed.yml.)
  syms="$("$NM" "$TMP/libdregg_lean.a" 2>/dev/null || true)"
  for sym in \
    dregg_exec_full_forest_auth \
    dregg_fips204_verify_real \
    dregg_fips204_sign_real \
    dregg_mldsa_keygen_real \
    dregg_mlkem_encaps_real \
    dregg_mlkem_decaps_real \
    dregg_mlkem_keygen_real
  do
    case "$syms" in
      *"$sym"*) ;;
      *) die "the downloaded archive lacks required verified-runtime export '$sym' —
  it is not a valid current dregg seed (wrong/stale asset, or a corrupt/placeholder file). NOT installing." ;;
    esac
  done
  unset syms
  echo "    verified executor + all six real PQ exports present"
fi
mv -f "$TMP/libdregg_lean.a" "$DEST"

say "DONE — verified Lean seed installed ($(du -h "$DEST" | cut -f1 | tr -d ' '))."
cat <<EOF
  Next (build a VERIFIED node, failing loud on any silent marshal-only degrade):
      DREGG_REQUIRE_LEAN=1 cargo build -p dregg-node --release
  You need elan + the pinned toolchain on PATH (metatheory/lean-toolchain); the seed links
  against it. If \`lake env\` cannot be found, export the sysroot explicitly:
      export DREGG_LEAN_SYSROOT="\$(cd metatheory && lake env printenv LEAN_SYSROOT)"
EOF
