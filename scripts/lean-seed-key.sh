#!/usr/bin/env bash
# lean-seed-key.sh — compute the provenance + a content KEY for the Lean seed archive
# (dregg-lean-ffi/libdregg_lean.a), so a published seed can be matched to the Lean HEAD it
# was cut from. Shared by scripts/fetch-lean-seed.sh (which asset do I need?) and the
# .github/workflows/lean-seed.yml publish job (what do I name the asset I just built?).
#
# The seed is a NATIVE static archive (Mach-O on macOS, ELF on Linux) of the compiled Lean
# kernel + its whole mathlib/batteries/aesop/Qq dependency closure. Its validity depends on:
#   * the PLATFORM   (os + arch — a Mach-O arm64 archive cannot link into an ELF x86_64 build);
#   * the LEAN TOOLCHAIN (metatheory/lean-toolchain — the runtime/stdlib ABI);
#   * the MATHLIB pin (the dependency-closure revision the archive was compiled against);
#   * the Dregg2 SOURCE tree (the executor slice baked into the seed — used verbatim on the
#     seed-fetch path where the fresh clone has no warm .lake to re-splice from).
# The KEY is a short hash over exactly those inputs. Same key ⇒ interchangeable seed.
#
# Usage:
#   scripts/lean-seed-key.sh            # print KEY=… and each PROVENANCE line to stdout
#   scripts/lean-seed-key.sh --key      # print ONLY the short key (for scripting)
#   scripts/lean-seed-key.sh --asset    # print the canonical release-asset base name
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
META="$ROOT/metatheory"

# ── platform ────────────────────────────────────────────────────────────────
os="$(uname -s)"       # Darwin | Linux
arch="$(uname -m)"     # arm64 | x86_64 | aarch64
# normalise arch spellings so macOS `arm64` and Linux `aarch64` don't drift apart per-host.
case "$arch" in
  aarch64) arch="arm64" ;;
  amd64)   arch="x86_64" ;;
esac
platform="${os}-${arch}"

# ── lean toolchain ──────────────────────────────────────────────────────────
lean_toolchain="$(tr -d '[:space:]' < "$META/lean-toolchain" 2>/dev/null || echo unknown)"

# ── mathlib pin ─────────────────────────────────────────────────────────────
# The pinned revision is the 40-hex sha on the `rev = "…"` line of the mathlib `[[require]]`
# in metatheory/lakefile.toml (a portable git+rev require). Prefer that explicit assignment over
# any 40-hex that also appears in a comment; fall back to lake-manifest.json's mathlib entry.
mathlib_rev="$(grep -E '^[[:space:]]*rev[[:space:]]*=' "$META/lakefile.toml" 2>/dev/null \
  | grep -oE '[0-9a-f]{40}' | head -1 || true)"
if [ -z "${mathlib_rev:-}" ]; then
  # Fallback: any 40-hex in the lakefile (e.g. the pin comment), then the manifest.
  mathlib_rev="$(grep -oE '[0-9a-f]{40}' "$META/lakefile.toml" 2>/dev/null | head -1 || true)"
fi
if [ -z "${mathlib_rev:-}" ] && [ -f "$META/lake-manifest.json" ]; then
  mathlib_rev="$(grep -B4 '"name": *"mathlib"' "$META/lake-manifest.json" 2>/dev/null \
    | grep -oE '[0-9a-f]{40}' | head -1 || true)"
fi
mathlib_rev="${mathlib_rev:-unknown}"

# ── Dregg2 source tree hash ─────────────────────────────────────────────────
# Prefer git's own content hash of the subtree (deterministic, exact, free) — this is the
# common case for a fresh clone (clean tree). Fall back to hashing tracked file contents when
# the object is unavailable (shallow clone / detached working copy).
dregg_tree="$(git -C "$ROOT" rev-parse "HEAD:metatheory/Dregg2" 2>/dev/null || true)"
if [ -z "${dregg_tree:-}" ]; then
  if command -v shasum >/dev/null 2>&1; then
    dregg_tree="$(find "$META/Dregg2" -type f -name '*.lean' -print0 2>/dev/null \
      | sort -z | xargs -0 cat 2>/dev/null | shasum -a 256 | cut -c1-40 || echo unknown)"
  else
    dregg_tree="$(find "$META/Dregg2" -type f -name '*.lean' -print0 2>/dev/null \
      | sort -z | xargs -0 cat 2>/dev/null | sha256sum | cut -c1-40 || echo unknown)"
  fi
fi

# ── the key ─────────────────────────────────────────────────────────────────
sha() { if command -v sha256sum >/dev/null 2>&1; then sha256sum | cut -d' ' -f1; else shasum -a 256 | cut -d' ' -f1; fi; }
key="$(printf '%s\n%s\n%s\n%s\n' "$platform" "$lean_toolchain" "$mathlib_rev" "$dregg_tree" | sha | cut -c1-16)"

lean_tag="$(echo "$lean_toolchain" | sed 's#.*:##; s#[^A-Za-z0-9._-]#_#g')"   # v4.30.0
asset="libdregg_lean-${platform}-${lean_tag}-${key}.a.zst"

case "${1:-}" in
  --key)   printf '%s\n' "$key" ;;
  --asset) printf '%s\n' "$asset" ;;
  *)
    printf 'KEY=%s\n'            "$key"
    printf 'PLATFORM=%s\n'       "$platform"
    printf 'LEAN_TOOLCHAIN=%s\n' "$lean_toolchain"
    printf 'MATHLIB_REV=%s\n'    "$mathlib_rev"
    printf 'DREGG_TREE_HASH=%s\n' "$dregg_tree"
    printf 'ASSET=%s\n'          "$asset"
    ;;
esac
