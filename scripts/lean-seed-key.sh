#!/usr/bin/env bash
# lean-seed-key.sh — compute the provenance + a content KEY for the Lean seed archive
# (dregg-lean-ffi/libdregg_lean.a), so a published seed can be matched to the Lean HEAD it
# was cut from. Shared by scripts/fetch-lean-seed.sh (which asset do I need?), the
# .github/workflows/lean-seed.yml publish job (what do I name the asset I just built?), and
# — since 2026-08-07 — dregg-lean-ffi/build.rs, which accepts a key-matched seed as EVIDENCE
# that the archive was built from this checkout's Lean source (see `seed_key_evidence`).
#
# The seed is a NATIVE static archive (Mach-O on macOS, ELF on Linux) of the compiled Lean
# kernel + its whole mathlib/batteries/aesop/Qq dependency closure. Its validity depends on:
#   * the PLATFORM   (os + arch — a Mach-O arm64 archive cannot link into an ELF x86_64 build);
#   * the LEAN TOOLCHAIN (metatheory/lean-toolchain — the runtime/stdlib ABI);
#   * the MATHLIB pin (the dependency-closure revision the archive was compiled against);
#   * the Dregg2 FFI BOUNDARY CLOSURE — the in-tree modules whose compiled objects are the
#     archive's Dregg2 slice.
# The KEY is a short hash over exactly those inputs. Same key ⇒ interchangeable seed.
#
# ⚑ THE FOURTH INPUT CHANGED ON 2026-08-07, AND IT IS A FLAG DAY. It used to be
# `git rev-parse HEAD:metatheory/Dregg2` — the whole 2246-module tree. The archive does not
# contain the whole tree: `dregg-lean-ffi/build.rs` builds ONE target (`Dregg2.FFI`) and
# splices ONLY that module's import closure, and `scripts/check-lean-seed-closure.sh` checks
# the archive against exactly that closure. MEASURED 2026-08-07: 302 of 2246 Dregg2 modules
# are in the closure, and only 69 of the last 300 commits touching `metatheory/Dregg2/`
# (23.0%) touched one of them. So 77% of key invalidations were for source that provably
# cannot enter the archive — the key named the wrong resource, and it named it four times
# too broadly. Every asset published under the old scheme is unreachable by the new name;
# re-cut with `gh workflow run lean-seed.yml`.
#
# ⚑ AND IT IS A WORKTREE HASH, NOT A GIT HASH. The old input was the COMMITTED tree, so a
# checkout with uncommitted Lean edits computed the key of source it was not building, asked
# for that asset, and — if it existed — installed a seed that does not correspond to the
# files on disk. The closure hash below reads the FILES, so a dirty closure simply misses.
# That is the honest answer, and it is what lets build.rs treat a match as evidence at all.
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

sha()       { if command -v sha256sum >/dev/null 2>&1; then sha256sum | cut -d' ' -f1; else shasum -a 256 | cut -d' ' -f1; fi; }
sha_files() { if command -v sha256sum >/dev/null 2>&1; then xargs -0 sha256sum; else xargs -0 shasum -a 256; fi; }
die()       { printf 'lean-seed-key: FATAL: %s\n' "$*" >&2; exit 2; }

# ── Dregg2 FFI-boundary closure hash ────────────────────────────────────────
# The module set comes from `scripts/lean-ffi-closure.py`, which is ALREADY the single source
# of truth for "what belongs in the archive": `dregg-lean-ffi/scripts/seed-dregg2-closure.sh`
# picks the seed's members from it and `scripts/check-lean-seed-closure.sh` checks an archive
# against it. Computing the key from a SECOND walk of that graph is how the nine-root list
# drifted 95 modules short in the first place, so this one is derived, not retyped.
#
# IN-TREE ONLY. `lean-ffi-closure.py` also resolves modules out of `metatheory/.lake/packages`
# when a warm lake checkout is present, and skips them when it is not — so its raw output is
# HOST-DEPENDENT and unusable as a content key. We keep exactly the modules that resolve to a
# file under `metatheory/` itself. Those are the archive's Dregg2 slice; the dependency
# closure behind them is pinned by MATHLIB_REV + LEAN_TOOLCHAIN above, which is the correct
# granularity (the archive is reachability-GC'd against mathlib on purpose).
command -v python3 >/dev/null 2>&1 \
  || die "python3 is required to compute the FFI boundary closure (scripts/lean-ffi-closure.py).
  Refusing to fall back to a different hash: a host that computes a DIFFERENT key for the same
  source publishes under one name and fetches under another, which is a permanent phantom miss."
closure_mods="$(python3 "$ROOT/scripts/lean-ffi-closure.py" "$META" 2>/dev/null || true)"
[ -n "$closure_mods" ] || die "scripts/lean-ffi-closure.py produced NO modules for $META — the
  import walk is broken. A key computed over an empty closure would be identical for every
  source revision in the repo, which is worse than no key at all."

# ⚠ THE DOT→SLASH REWRITE MUST BE TOTAL. Lean allows «guillemet-quoted» identifiers, in which a
# literal `.` is part of the NAME rather than a separator. `sed 's#\.#/#g'` would rewrite such a
# module to a path that does not exist, `[ -f ]` would drop it, and it would vanish from the key —
# silently, so an edit to it would no longer invalidate a published seed and `build.rs` would
# accept that seed as evidence for source it does not cover. That is an unsoundness in the
# evidence, not a missing optimisation, so it fails CLOSED. Measured 2026-08-07: zero quoted
# identifiers in the closure and zero in the in-tree `.lean` paths, i.e. the rewrite is total
# today and this guard costs nothing until someone introduces one.
if printf '%s\n' "$closure_mods" | grep -q '«\|»'; then
  die "the Dregg2.FFI closure contains a «quoted» module name, which this key's dot→slash path
  rewrite cannot resolve. Such a module would be dropped from the hash SILENTLY, making the key
  blind to edits in it. Teach the rewrite to handle quoted identifiers before publishing again."
fi

# ⚠ BUILTINS ONLY IN THE LOOP. The raw closure is ~8800 modules on a warm lake checkout (mathlib
# dominates it), and a `$(printf|tr)` per module is ~17,600 forks — measured at 96 SECONDS, which
# would put a minute and a half onto every fetch, every publish, and every build.rs evidence check.
# `sed` rewrites the whole stream once; `[ -f ]` and `printf` inside the loop are bash builtins.
closure_rel="$(printf '%s\n' "$closure_mods" | sed 's#\.#/#g; s#$#.lean#' \
  | while IFS= read -r rel; do
      # `if`, not `[ … ] && printf`: with `set -o pipefail` the latter makes the WHOLE loop exit
      # non-zero whenever the LAST module tested is out-of-tree, which fails the assignment and
      # kills the script under `set -e` — with the value correctly computed and never printed.
      if [ -f "$META/$rel" ]; then printf '%s\n' "$rel"; fi
    done | LC_ALL=C sort)"
n_closure="$(printf '%s\n' "$closure_rel" | grep -c . || true)"
# MEASURED 2026-08-07: 302 in-tree modules in `Dregg2.FFI`'s closure. The floor is a broken-walk
# detector, not a budget — a real shrink below it should be argued for in the diff, not absorbed
# silently, because the failure mode is a key that stops distinguishing revisions.
if [ "${n_closure:-0}" -lt 100 ]; then
  die "only ${n_closure:-0} in-tree module(s) in the Dregg2.FFI closure (measured floor: 100, actual 2026-08-07: 302).
  The walk is broken or the boundary manifest lost its imports. Publishing/fetching on a
  degenerate closure would key every revision the same."
fi
closure_hash="$(cd "$META" && printf '%s\n' "$closure_rel" | tr '\n' '\0' | sha_files | sha | cut -c1-40)"

# ── the key ─────────────────────────────────────────────────────────────────
key="$(printf '%s\n%s\n%s\n%s\n' "$platform" "$lean_toolchain" "$mathlib_rev" "$closure_hash" | sha | cut -c1-16)"

lean_tag="$(echo "$lean_toolchain" | sed 's#.*:##; s#[^A-Za-z0-9._-]#_#g')"   # v4.30.0
asset="libdregg_lean-${platform}-${lean_tag}-${key}.a.zst"

case "${1:-}" in
  --key)   printf '%s\n' "$key" ;;
  --asset) printf '%s\n' "$asset" ;;
  *)
    printf 'KEY=%s\n'                "$key"
    printf 'PLATFORM=%s\n'           "$platform"
    printf 'LEAN_TOOLCHAIN=%s\n'     "$lean_toolchain"
    printf 'MATHLIB_REV=%s\n'        "$mathlib_rev"
    printf 'DREGG_CLOSURE_HASH=%s\n' "$closure_hash"
    printf 'DREGG_CLOSURE_MODULES=%s\n' "$n_closure"
    printf 'ASSET=%s\n'              "$asset"
    ;;
esac
