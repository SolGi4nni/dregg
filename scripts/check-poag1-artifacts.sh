#!/usr/bin/env bash
set -euo pipefail

# Reproduce the complete Lean-authored POAG1 bundle. SHA-256 is the one external
# primitive in this pipeline: it measures already-rendered bytes and supplies the
# full-width pins that Lean parses back into Core.ArtifactRef. The curator signs
# exact manifest bytes separately; this script never manufactures that signature,
# and check mode never treats an unsigned bundle as releaseable.

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
meta_root="$repo_root/metatheory"
checked_root="$repo_root/poa/artifacts/poag1"
mode="${1:-check}"
poa_root="${POA_ROOT:-}"
main_data_dir="${POA_MAIN_DATA_DIR:-$HOME/.dregg}"

case "$mode" in
  check|--update) ;;
  *)
    echo "usage: scripts/check-poag1-artifacts.sh [check|--update]" >&2
    exit 2
    ;;
esac

if [ -z "$poa_root" ]; then
  echo "POA_ROOT is required: POAG1 artifacts are emitted only after a PoA genesis exists" >&2
  exit 2
fi
devnet_manifest="$poa_root/poa-devnet.json"
if [ ! -f "$devnet_manifest" ]; then
  echo "missing authenticated PoA deployment manifest: $devnet_manifest" >&2
  exit 2
fi

# Re-derive the public deployment identity from the exact genesis bytes before
# allowing its federation id into a Lean MissionSpec.  A display label or an
# arbitrary 32-byte environment value is never accepted as chain identity.
node "$repo_root/scripts/poa-devnet-manifest.mjs" verify-public \
  --root "$poa_root" --main-data-dir "$main_data_dir" >/dev/null
federation_id="$(jq -er '
  select(.schema == "dregg-poa-devnet-manifest-v1") |
  select(.federation_id | test("^[0-9a-f]{64}$")) |
  .federation_id
' "$devnet_manifest")"

tmp_root="$(mktemp -d "${TMPDIR:-/tmp}/poag1.XXXXXXXX")"
trap 'rm -rf "$tmp_root"' EXIT

sha_file() {
  local path="$1"
  local value
  value="$(shasum -a 256 "$path" | awk '{print $1}')"
  printf 'sha256:%s' "$value"
}

be64() {
  printf '%016x' "$1" | xxd -r -p
}

source_files=(
  "Dregg2/Games/PathOfAngels/Core.lean"
  "Dregg2/Games/PathOfAngels/SignalTriangulation.lean"
  "Dregg2/Games/PathOfAngels/Emit.lean"
  "Dregg2/Games/PathOfAngels/EmitMain.lean"
)

source_sha="$(
  cd "$meta_root"
  for path in "${source_files[@]}"; do
    printf 'POAG1-SOURCE\0%s\0' "$path"
    command cat "$path"
    printf '\0'
  done | shasum -a 256 | awk '{printf "sha256:%s", $1}'
)"

export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
(
  cd "$meta_root"
  lake build Dregg2.Games.PathOfAngels.Emit
  POA_EMIT_MODE=signal POA_EMIT_OUT="$tmp_root" \
    lake env lean --run Dregg2/Games/PathOfAngels/EmitMain.lean
)

signal_sha="$(sha_file "$tmp_root/games/signal-triangulation.json")"
content_path="games/signal-triangulation.json"
content_path_bytes="$(printf '%s' "$content_path" | wc -c | tr -d ' ')"
content_bytes="$(wc -c < "$tmp_root/$content_path" | tr -d ' ')"
content_root_sha="$(
  {
    printf 'path-of-angels/content-root/v1\0'
    be64 1
    be64 "$content_path_bytes"
    printf '%s' "$content_path"
    be64 "$content_bytes"
    command cat "$tmp_root/$content_path"
  } | shasum -a 256 | awk '{printf "sha256:%s", $1}'
)"

(
  cd "$meta_root"
  POA_EMIT_MODE=artifacts POA_EMIT_OUT="$tmp_root" \
    POA_FEDERATION_ID="$federation_id" \
    POA_SOURCE_SHA256="$source_sha" POA_SIGNAL_SHA256="$signal_sha" \
    POA_CONTENT_ROOT_SHA256="$content_root_sha" \
    lake env lean --run Dregg2/Games/PathOfAngels/EmitMain.lean
)

schema_sha="$(sha_file "$tmp_root/schema.json")"
catalog_sha="$(sha_file "$tmp_root/catalog.json")"

(
  cd "$meta_root"
  POA_EMIT_MODE=bundle POA_EMIT_OUT="$tmp_root" \
    POA_FEDERATION_ID="$federation_id" \
    POA_SOURCE_SHA256="$source_sha" POA_SIGNAL_SHA256="$signal_sha" \
    POA_CONTENT_ROOT_SHA256="$content_root_sha" \
    POA_SCHEMA_SHA256="$schema_sha" POA_CATALOG_SHA256="$catalog_sha" \
    lake env lean --run Dregg2/Games/PathOfAngels/EmitMain.lean
)

test "$(sha_file "$tmp_root/schema.json")" = "$schema_sha"
test "$(sha_file "$tmp_root/catalog.json")" = "$catalog_sha"
test "$(sha_file "$tmp_root/games/signal-triangulation.json")" = "$signal_sha"

catalog_federations="$(jq -er '[.missions[].federation_id] | unique | .[]' "$tmp_root/catalog.json")"
if [ "$catalog_federations" != "$federation_id" ]; then
  echo "POAG1 mission federation_id does not equal authenticated PoA genesis" >&2
  exit 1
fi

expected=(
  "manifest.json"
  "schema.json"
  "catalog.json"
  "games/signal-triangulation.json"
)

if [ "$mode" = "--update" ]; then
  mkdir -p "$checked_root/games"
  for path in "${expected[@]}"; do
    cp "$tmp_root/$path" "$checked_root/$path"
  done
  if [ -f "$checked_root/manifest.sig.json" ]; then
    rm -f "$checked_root/manifest.sig.json"
    echo "POAG1 detached signature removed because manifest bytes changed; curator re-sign required"
  fi
  echo "POAG1 artifacts updated at $checked_root"
  echo "POAG1 release status: UNSIGNED; run the curator ceremony, then check with pinned epoch/counter"
  exit 0
fi

for path in "${expected[@]}"; do
  if ! cmp -s "$tmp_root/$path" "$checked_root/$path"; then
    echo "POAG1 drift: $path differs from the Lean emission" >&2
    diff -u "$checked_root/$path" "$tmp_root/$path" || true
    exit 1
  fi
done

unknown="$(
  cd "$checked_root"
  find . -type f ! -path './manifest.sig.json' -print | sed 's#^./##' | sort |
    while IFS= read -r path; do
      keep=false
      for wanted in "${expected[@]}"; do
        if [ "$path" = "$wanted" ]; then keep=true; break; fi
      done
      if [ "$keep" = false ]; then printf '%s\n' "$path"; fi
    done
)"
if [ -n "$unknown" ]; then
  echo "POAG1 checked directory contains unknown artifacts:" >&2
  echo "$unknown" >&2
  exit 1
fi

signature_path="$checked_root/manifest.sig.json"
curator_key_path="$repo_root/poa/config/curator-key.json"
[ -f "$signature_path" ] || {
  echo "POAG1 release refused: manifest.sig.json is absent" >&2
  exit 1
}
[ -f "$curator_key_path" ] || {
  echo "POAG1 release refused: external curator pin is absent at $curator_key_path" >&2
  exit 1
}
: "${POA_CONTENT_EPOCH:?POA_CONTENT_EPOCH deployment pin is required in check mode}"
: "${POA_CURATOR_COUNTER:?POA_CURATOR_COUNTER deployment pin is required in check mode}"

# Reuse the same strict parser and Web Crypto verifier exercised by the browser.
# Both rollback values are external release pins; reading them from the signature
# envelope itself would make a valid old epoch indistinguishable from the target.
POA_VERIFY_MANIFEST="$checked_root/manifest.json" \
POA_VERIFY_SIGNATURE="$signature_path" \
POA_VERIFY_KEY="$curator_key_path" \
POA_VERIFY_MODULE="$repo_root/poa-web/src/content-epoch.js" \
node --input-type=module - <<'NODE'
import { readFile } from "node:fs/promises";
import { pathToFileURL } from "node:url";

const decimalPin = (name) => {
  const raw = process.env[name];
  if (!/^(0|[1-9][0-9]*)$/.test(raw ?? "")) throw new Error(`${name} must be canonical decimal`);
  const value = Number(raw);
  if (!Number.isSafeInteger(value)) throw new Error(`${name} exceeds exact JSON integer range`);
  return value;
};
const { authenticateContentEpoch } = await import(pathToFileURL(process.env.POA_VERIFY_MODULE).href);
const verified = await authenticateContentEpoch({
  manifestBytes: new Uint8Array(await readFile(process.env.POA_VERIFY_MANIFEST)),
  signatureBytes: new Uint8Array(await readFile(process.env.POA_VERIFY_SIGNATURE)),
  keyBytes: new Uint8Array(await readFile(process.env.POA_VERIFY_KEY)),
  expectedContentEpoch: decimalPin("POA_CONTENT_EPOCH"),
  expectedCounter: decimalPin("POA_CURATOR_COUNTER"),
});
process.stdout.write(`POAG1 curator signature authenticated (activation=${verified.activationDigest})\n`);
NODE

echo "POAG1 artifacts reproduce exactly (federation=$federation_id source=$source_sha signal=$signal_sha content_root=$content_root_sha)"
