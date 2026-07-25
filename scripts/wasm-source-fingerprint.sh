#!/usr/bin/env bash
# Print the SOURCE FINGERPRINT of the browser wasm bundle: one sha256 over every
# build-relevant source file in `wasm`'s transitive LOCAL (path-dependency) crate
# graph, for the `wasm32-unknown-unknown` target.
#
# WHY THIS EXISTS (the wound it closes)
# ------------------------------------
# On 2026-07-25 the flagship `/descent/play` CTA was found serving a wasm bundle built
# 2026-07-20 21:46. Ten commits had touched `wasm/src` since, four of them the exact
# binding that page drives, INCLUDING a wire-format bump (`PORTABLE_VERSION` 1 -> 3).
# Nothing anywhere noticed: `descent_play.rs`'s module doc claimed "Missing/STALE wasm
# fails closed with a visible notice", and the missing half was real (an honest 503) but
# the STALE half did not exist — no mtime, no hash, no manifest, no check. A bundle five
# days behind a wire bump served a 200 and every settled run it exported was refused by
# the server it posted to.
#
# A gate that cannot go red is not a gate. This is the red-capable half:
# `scripts/build-web-artifacts.sh` RECORDS this fingerprint into
# `wasm/pkg/dregg-wasm-provenance.json` at build time, and
# `scripts/check-wasm-freshness.sh` RECOMPUTES it and refuses when they differ.
#
# WHAT IT COVERS, EXACTLY (stated so nobody has to guess)
# ------------------------------------------------------
# `cargo metadata --target wasm32-unknown-unknown` resolves the real wasm32 graph; every
# package with a `path` source (i.e. a local crate, in this repo OR the sibling
# `plonky3-recursion` checkout the `[patch]` points at) contributes its build-relevant
# files. `target/`, `pkg/`, `node_modules/` and `.git/` are excluded.
#
# Extensions are a deliberate SUPERSET of "code": `.json`/`.tsv`/`.csv`/`.bin` are in
# because this graph `include_str!`s ~31 MB of AIR descriptor registries out of
# `circuit/descriptors/`, and those bytes are shipped in the bundle's data section — a
# descriptor re-emission changes what the browser runs while no `.rs` file moves.
#
# Each package's top-level `tests/`, `benches/` and `examples/` are PRUNED — none of them
# link into the release `cdylib`, and in a live multi-lane tree they churn constantly, which
# would train everyone to ignore a red gate (the precise way a gate dies). What is NOT
# pruned is `#[cfg(test)]` code living inside `src/`; that stays a deliberate superset,
# because separating it needs a real parse and the direction to err is obvious: a false
# "rebuild it" costs a build, a false "it is current" is what shipped a five-day-old wire.
#
# Untracked files count (no `git ls-files`): a source file that is not committed yet still
# changes what a local build produces, and this fingerprint describes a BUILD, not a commit.
#
# WHERE TO RUN IT: CI and the deploy, against a fixed commit. In a working tree with
# several live lanes the fingerprint genuinely moves every few minutes — that is not
# noise, the bundle really is stale — but it makes this a poor dev-loop gate.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export ROOT

sha256_stdin() {
  if command -v sha256sum >/dev/null 2>&1; then sha256sum | awk '{print $1}'
  else shasum -a 256 | awk '{print $1}'; fi
}

# Local (path-dependency) package roots in the wasm32 graph, as resolved by cargo itself.
# `-C "$ROOT/wasm"` so this is the standalone wasm workspace's graph, not the root one.
package_roots() {
  cargo metadata \
    --manifest-path "$ROOT/wasm/Cargo.toml" \
    --format-version 1 \
    --filter-platform wasm32-unknown-unknown \
    2>/dev/null \
  | "$(command -v python3)" -c '
import json,os,sys
md=json.load(sys.stdin)
roots=set()
for p in md["packages"]:
    # A local crate has no registry/git source.
    if p.get("source") is None:
        roots.add(os.path.dirname(p["manifest_path"]))
for r in sorted(roots):
    print(r)
'
}

# Every build-relevant file under those roots, repo-root-relative where possible so the
# fingerprint does not move with the checkout location.
source_files() {
  while IFS= read -r root; do
    [ -d "$root" ] || continue
    find "$root" \
      \( -name target -o -name pkg -o -name node_modules -o -name .git \
         -o -path "$root/tests" -o -path "$root/benches" -o -path "$root/examples" \) -prune -o \
      -type f \( -name '*.rs' -o -name '*.toml' -o -name '*.lock' \
                 -o -name '*.json' -o -name '*.tsv' -o -name '*.csv' -o -name '*.bin' \) \
      -print
  done < <(package_roots)
}

# One digest over (relative path, content digest) pairs, sorted — so the fingerprint is
# order-independent and a RENAME registers as a change.
main() {
  local list
  list="$(source_files | sort -u)"
  [ -n "$list" ] || { echo "wasm-source-fingerprint: cargo metadata yielded NO local packages" >&2; exit 1; }

  local count
  count="$(printf '%s\n' "$list" | wc -l | tr -d ' ')"

  # A tiny graph means cargo metadata silently degraded (e.g. the plonky3-recursion
  # sibling checkout is missing and resolution half-failed). Fail LOUD: a fingerprint
  # over a truncated graph would compare equal forever and re-create the exact
  # can't-go-red hole this script exists to close.
  if [ "$count" -lt 200 ]; then
    echo "wasm-source-fingerprint: only $count source files in the wasm32 graph — that is" >&2
    echo "  implausibly small. cargo metadata probably failed to resolve (is the sibling" >&2
    echo "  ../plonky3-recursion checkout present, at the rev wasm/Cargo.toml pins?)." >&2
    exit 1
  fi

  # Hashed in ONE python pass, not a shasum subprocess per file: 2246 files x fork was
  # ~32s, which is slow enough that a build step would get commented out.
  local digest
  digest="$(printf '%s\n' "$list" | python3 -c '
import hashlib, os, sys
root = os.environ["ROOT"].rstrip("/") + "/"
outer = hashlib.sha256()
for line in sys.stdin:
    p = line.rstrip("\n")
    if not p:
        continue
    rel = p[len(root):] if p.startswith(root) else p
    h = hashlib.sha256()
    with open(p, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    outer.update(f"{rel}  {h.hexdigest()}\n".encode())
print(outer.hexdigest())
')"

  if [ "${1:-}" = "--verbose" ]; then
    echo "files: $count"
  fi
  echo "$digest"
}

main "$@"
