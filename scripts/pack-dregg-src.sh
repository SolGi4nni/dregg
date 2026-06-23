#!/usr/bin/env bash
# pack-dregg-src.sh — assemble the dregg SOURCE PAYLOAD that ships INSIDE deos so a
# running agent (a Claude logged into the embedded Hermes, or the cockpit itself)
# can READ the system it is trapped within. This is the carrier half of the
# self-describing vessel (docs/deos/SELF-DESCRIBING-VESSEL.md).
#
# WHAT IT IS: a compressed tarball (`dregg-src.tar.zst`) of the SOURCE that DEFINES
# the system — the Rust, the Lean (`metatheory/`, esp. CONSTRUCTIVE-KNOWLEDGE.md /
# DREGG-CALCULUS.md), the docs, the manifests, the scripts. NOT the build artifacts
# (`target/`, `.git/`, `node_modules`, the vendored caches, `*.crate`,
# `libdregg_lean.a`, images/binary blobs) — just the `.rs`/`.lean`/`.md`/`.toml`/
# `.sh`/`.py` that say what dregg IS.
#
# WHY git ls-files: the tracked set is ALREADY the no-artifacts set (`.gitignore`
# excludes `target/`, `node_modules`, `*.crate`, `*.zip`, the lean object caches,
# `metatheory/.lake`, …). Filtering it to the source extensions yields exactly the
# definitional corpus with zero artifact leakage and zero hand-maintained excludes.
#
# USAGE:
#   scripts/pack-dregg-src.sh [OUT_TARBALL] [MANIFEST_OUT]
#     OUT_TARBALL   default: starbridge-v2/dist/dregg-src.tar.zst
#     MANIFEST_OUT  default: alongside OUT_TARBALL as dregg-src.manifest.txt
#
# The AppImage job (.github/workflows/starbridge-v2-installers.yml) runs this and
# drops the tarball into AppDir/usr/share/dregg-src/ so the shipped image carries
# the source. At runtime `SourceVessel` (starbridge-v2/src/source_vessel.rs) finds
# + reads it as a cap-bounded READ surface.
set -euo pipefail

# Repo root = the dir holding this script's parent (scripts/ lives at the root).
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

OUT="${1:-$ROOT/starbridge-v2/dist/dregg-src.tar.zst}"
MANIFEST="${2:-${OUT%.tar.zst}.manifest.txt}"

mkdir -p "$(dirname "$OUT")"

# The definitional extensions — the files that DEFINE the system (not data/blobs).
# Add an extension here only if it carries DEFINITION (source/spec/doc/manifest),
# never generated data.
PATTERN='\.(rs|lean|md|toml|sh|py)$'

# The tracked source set (no artifacts, by construction — see header).
# `git ls-files -z` handles paths with spaces/newlines.
mapfile -d '' FILES < <(git ls-files -z | { grep -zE "$PATTERN" || true; })

if [ "${#FILES[@]}" -eq 0 ]; then
  echo "::error::pack-dregg-src: no source files matched $PATTERN — refusing to ship an empty vessel" >&2
  exit 1
fi

# The manifest: a plain newline-separated list of the bundled paths (the carrier's
# table of contents; SourceVessel can list it without unpacking the whole tarball).
printf '%s\n' "${FILES[@]}" | LC_ALL=C sort > "$MANIFEST"
N="$(wc -l < "$MANIFEST" | tr -d ' ')"

# Raw (uncompressed) byte total of the payload — the "tens of MB, not GB" check.
RAW="$(printf '%s\0' "${FILES[@]}" | xargs -0 stat -f '%z' 2>/dev/null | awk '{s+=$1} END {print s+0}' || \
       printf '%s\0' "${FILES[@]}" | xargs -0 stat -c '%s' 2>/dev/null | awk '{s+=$1} END {print s+0}')"

# Pack under a `dregg-src/` top prefix so an extract lands at `dregg-src/<path>`
# (a clean, self-naming root). `--files-from` reads the exact set; zstd -19 for a
# small carrier (the source is text → compresses hard).
TAR_LIST="$(mktemp)"
trap 'rm -f "$TAR_LIST"' EXIT
printf '%s\n' "${FILES[@]}" > "$TAR_LIST"

# GNU tar uses --transform; bsdtar (macOS) uses -s. Detect and branch so the
# top-level `dregg-src/` prefix lands on both.
if tar --version 2>/dev/null | grep -qi 'gnu tar'; then
  tar --transform 's,^,dregg-src/,' -cf - -T "$TAR_LIST" | zstd -19 -q -o "$OUT" -f
else
  tar -s ',^,dregg-src/,' -cf - -T "$TAR_LIST" | zstd -19 -q -o "$OUT" -f
fi

PACKED="$(stat -f '%z' "$OUT" 2>/dev/null || stat -c '%s' "$OUT")"

awk -v n="$N" -v raw="$RAW" -v packed="$PACKED" -v out="$OUT" 'BEGIN {
  printf "dregg-src payload assembled:\n"
  printf "  files   : %d definitional source files (.rs/.lean/.md/.toml/.sh/.py)\n", n
  printf "  raw     : %d bytes (%.1f MB) — the source that DEFINES the system, no artifacts\n", raw, raw/1048576
  printf "  packed  : %d bytes (%.1f MB) — %s\n", packed, packed/1048576, out
  printf "  ratio   : %.1fx\n", raw/packed
}'
