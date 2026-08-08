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
devnet_manifest="${POA_DEVNET_MANIFEST:-}"
main_data_dir="${POA_MAIN_DATA_DIR:-$HOME/.dregg}"

case "$mode" in
  check|--update) ;;
  *)
    echo "usage: scripts/check-poag1-artifacts.sh [check|--update]" >&2
    exit 2
    ;;
esac

if [ -n "$devnet_manifest" ]; then
  poa_root="$(cd "$(dirname "$devnet_manifest")" && pwd)"
elif [ -n "$poa_root" ]; then
  devnet_manifest="$poa_root/poa-devnet.json"
else
  echo "POA_ROOT or POA_DEVNET_MANIFEST is required: POAG1 emission is post-genesis" >&2
  exit 2
fi
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

# Every Lean file the emitted bytes are a function of. This list is ORDER-SENSITIVE
# (the digest frames each entry in sequence), so it is not sorted — appending is the
# safe edit and reordering is a flag day.
#
# ⚠ 2026-08-06: `BlackBoxReconstruction.lean`, `HiddenInstance.lean` and
# `SeedDraw.lean` were ALL THREE absent. Black Box's descriptor was already being
# emitted, and every catalog and schema entry names `HiddenInstance` as the module
# that draws a run's instance — yet any of them could have changed without the
# source digest moving. Enrolling Black Box in the bundle without also enrolling its
# kernel here would have shipped a pinned artifact whose rules were outside the pin.
#
# `SeedDraw` is the one that says how a bounded draw is taken from a run seed, by
# rejection sampling. `HiddenInstance.runSeedFor` — the derivation the schema names —
# consumes it, and so do `SalvageLock` and `BlackBoxReconstruction`. It is the rule
# that decides WHICH instance a player gets, so it is exactly as load-bearing as the
# kernels that call it, and it was covered by nothing.
#
# ⚠ The list is DEPENDENCY-ORDERED, not append-ordered: this commit is already a
# source-digest flag day (three files joined at once), so placing `SeedDraw.lean`
# next to `Core.lean` where it belongs cost nothing here. Once the bundle is
# re-emitted, appending is again the safe edit and reordering is again a flag day.
#
# ⚠ 2026-08-07: Deck Descent enrolled as the fifth game, which is a source-digest
# flag day again — `DeckDescent.lean` (the kernel), `DeckDescentEmit.lean` (the
# wire) and `EmitJson.lean` (the shared JSON/validator helpers `Emit.lean` now
# converges on) all joined the emitter's import closure at once. They are placed
# in dependency order for the same reason `SeedDraw.lean` was.
#
# ⚠ 2026-08-07, second flag day of the day: Artificer Logic and Vent Crawl enrolled
# as missions 6 and 7, so `ArtificerLogic.lean`, `ArtificerLogicEmit.lean`,
# `VentCrawl.lean` and `VentCrawlEmit.lean` joined the emitter's import closure.
# `VentCrawl.lean` also consumes `HiddenInstance` — for the DAY seed, drawn under a
# reserved sentinel key that is not a player, which is why its hidden table is
# shared across a slot rather than per-crawler.
#
# ⚠ 2026-08-08: `RelicNamespace.lean` joined — another source-digest flag day, and
# this one changes the CATALOG BYTES as well. Relic ids are one namespace shared by
# every mission (`WorldState.discoveredRelics` is a single `Finset RelicId`), and the
# seven-game bundle had Deck Descent claiming `{5,6,7,8}` while Artificer Logic and
# Vent Crawl claimed 6 and 7: relic 6 meant two things in one signed catalog. Every
# mission now owns the block `mission_id * 16 .. +15` and the emitter cannot render a
# mission that leaves its block. It sits next to `Core.lean` because that is what it
# extends; it imports nothing else.
#
# The invariant to preserve: this list must contain the TRANSITIVE closure of
# `Emit.lean`'s imports inside `Dregg2/Games/PathOfAngels/`. It now does.
source_files=(
  "Dregg2/Games/PathOfAngels/Core.lean"
  "Dregg2/Games/PathOfAngels/RelicNamespace.lean"
  "Dregg2/Games/PathOfAngels/SeedDraw.lean"
  "Dregg2/Games/PathOfAngels/SignalTriangulation.lean"
  "Dregg2/Games/PathOfAngels/RelayRepair.lean"
  "Dregg2/Games/PathOfAngels/SalvageLock.lean"
  "Dregg2/Games/PathOfAngels/BlackBoxReconstruction.lean"
  "Dregg2/Games/PathOfAngels/DeckDescent.lean"
  "Dregg2/Games/PathOfAngels/HiddenInstance.lean"
  "Dregg2/Games/PathOfAngels/ArtificerLogic.lean"
  "Dregg2/Games/PathOfAngels/VentCrawl.lean"
  "Dregg2/Games/PathOfAngels/FiniteTables.lean"
  "Dregg2/Games/PathOfAngels/EmitJson.lean"
  "Dregg2/Games/PathOfAngels/DeckDescentEmit.lean"
  "Dregg2/Games/PathOfAngels/ArtificerLogicEmit.lean"
  "Dregg2/Games/PathOfAngels/VentCrawlEmit.lean"
  "Dregg2/Games/PathOfAngels/Emit.lean"
  "Dregg2/Games/PathOfAngels/EmitMain.lean"
)

# ⚑ THE CHECK THAT WOULD HAVE CAUGHT `SeedDraw`.
#
# The list above was maintained by hand and drifted silently: a module can join the
# emitter's import graph and never join the digest, and NOTHING goes red — the bundle
# still emits, still pins, still verifies, and the pin simply stops covering one of
# the rules. That is a wound no downstream byte comparison can see, because every
# byte agrees with itself.
#
# So the closure is DERIVED here and compared to the list. Walk `EmitMain`'s imports
# transitively inside `Dregg2/Games/PathOfAngels/`; the set must equal `source_files`
# exactly. Missing means under-covered (the SeedDraw wound). Extra means the list
# names a file the emitter no longer reads, which makes the digest depend on
# something the bytes do not.
closure_work="$(mktemp "${TMPDIR:-/tmp}/poag1-closure.XXXXXXXX")"
closure_next="$(mktemp "${TMPDIR:-/tmp}/poag1-closure.XXXXXXXX")"
trap 'rm -rf "$tmp_root" "$closure_work" "$closure_next"' EXIT
printf 'EmitMain\n' > "$closure_work"
while :; do
  before="$(wc -l < "$closure_work" | tr -d ' ')"
  {
    cat "$closure_work"
    while read -r module; do
      grep -hoE '^import Dregg2\.Games\.PathOfAngels\.[A-Za-z0-9_]+' \
        "$meta_root/Dregg2/Games/PathOfAngels/$module.lean" 2>/dev/null \
        | sed 's/^import Dregg2\.Games\.PathOfAngels\.//' || true
    done < "$closure_work"
  } | LC_ALL=C sort -u > "$closure_next"
  mv "$closure_next" "$closure_work"
  after="$(wc -l < "$closure_work" | tr -d ' ')"
  [ "$before" = "$after" ] && break
done
declared_sources="$(
  printf '%s\n' "${source_files[@]}" \
    | sed 's|^Dregg2/Games/PathOfAngels/||; s|\.lean$||' \
    | LC_ALL=C sort -u
)"
if [ "$declared_sources" != "$(cat "$closure_work")" ]; then
  echo "POAG1 source_files is not the transitive import closure of EmitMain:" >&2
  diff <(printf '%s\n' "$declared_sources") "$closure_work" \
    --label declared-in-source_files --label reachable-from-EmitMain >&2 || true
  echo "a module reachable from the emitter and absent above is OUTSIDE the source digest" >&2
  exit 1
fi

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
  POA_EMIT_MODE=descriptors POA_EMIT_OUT="$tmp_root" \
    lake env lean --run Dregg2/Games/PathOfAngels/EmitMain.lean
)

artificer_sha="$(sha_file "$tmp_root/games/artificer-logic.json")"
blackbox_sha="$(sha_file "$tmp_root/games/black-box-reconstruction.json")"
descent_sha="$(sha_file "$tmp_root/games/deck-descent.json")"
relay_sha="$(sha_file "$tmp_root/games/relay-repair.json")"
salvage_sha="$(sha_file "$tmp_root/games/salvage-lock.json")"
signal_sha="$(sha_file "$tmp_root/games/signal-triangulation.json")"
vent_sha="$(sha_file "$tmp_root/games/vent-crawl.json")"
# ⚠ PATH-ASCENDING, and the content root's own framing says so
# (`entry_order: path_ascending` in schema.json). `games/artificer-logic.json` sorts
# FIRST — it took that slot from `games/black-box-reconstruction.json` when it
# enrolled — and `games/vent-crawl.json` is the only one that actually sorts last. A
# wrong order here does not fail: it silently computes a different content root,
# which the missions then bind and the curator then accepts.
content_paths=(
  "games/artificer-logic.json"
  "games/black-box-reconstruction.json"
  "games/deck-descent.json"
  "games/relay-repair.json"
  "games/salvage-lock.json"
  "games/signal-triangulation.json"
  "games/vent-crawl.json"
)
# The one place the ordering claim is CHECKED rather than asserted in a comment.
printf '%s\n' "${content_paths[@]}" | LC_ALL=C sort -c || {
  echo "content_paths is not path-ascending; the content root framing says it must be" >&2
  exit 1
}
content_root_sha="$(
  {
    printf 'path-of-angels/content-root/v1\0'
    be64 "${#content_paths[@]}"
    for content_path in "${content_paths[@]}"; do
      content_path_bytes="$(printf '%s' "$content_path" | wc -c | tr -d ' ')"
      content_bytes="$(wc -c < "$tmp_root/$content_path" | tr -d ' ')"
      be64 "$content_path_bytes"
      printf '%s' "$content_path"
      be64 "$content_bytes"
      command cat "$tmp_root/$content_path"
    done
  } | shasum -a 256 | awk '{printf "sha256:%s", $1}'
)"

(
  cd "$meta_root"
  POA_EMIT_MODE=artifacts POA_EMIT_OUT="$tmp_root" \
    POA_FEDERATION_ID="$federation_id" \
    POA_SOURCE_SHA256="$source_sha" POA_RELAY_SHA256="$relay_sha" \
    POA_SALVAGE_SHA256="$salvage_sha" POA_SIGNAL_SHA256="$signal_sha" \
    POA_BLACKBOX_SHA256="$blackbox_sha" POA_DECKDESCENT_SHA256="$descent_sha" \
    POA_ARTIFICER_SHA256="$artificer_sha" POA_VENTCRAWL_SHA256="$vent_sha" \
    POA_CONTENT_ROOT_SHA256="$content_root_sha" \
    lake env lean --run Dregg2/Games/PathOfAngels/EmitMain.lean
)

schema_sha="$(sha_file "$tmp_root/schema.json")"
catalog_sha="$(sha_file "$tmp_root/catalog.json")"

(
  cd "$meta_root"
  POA_EMIT_MODE=bundle POA_EMIT_OUT="$tmp_root" \
    POA_FEDERATION_ID="$federation_id" \
    POA_SOURCE_SHA256="$source_sha" POA_RELAY_SHA256="$relay_sha" \
    POA_SALVAGE_SHA256="$salvage_sha" POA_SIGNAL_SHA256="$signal_sha" \
    POA_BLACKBOX_SHA256="$blackbox_sha" POA_DECKDESCENT_SHA256="$descent_sha" \
    POA_ARTIFICER_SHA256="$artificer_sha" POA_VENTCRAWL_SHA256="$vent_sha" \
    POA_CONTENT_ROOT_SHA256="$content_root_sha" \
    POA_SCHEMA_SHA256="$schema_sha" POA_CATALOG_SHA256="$catalog_sha" \
    lake env lean --run Dregg2/Games/PathOfAngels/EmitMain.lean
)

test "$(sha_file "$tmp_root/schema.json")" = "$schema_sha"
test "$(sha_file "$tmp_root/catalog.json")" = "$catalog_sha"
test "$(sha_file "$tmp_root/games/artificer-logic.json")" = "$artificer_sha"
test "$(sha_file "$tmp_root/games/black-box-reconstruction.json")" = "$blackbox_sha"
test "$(sha_file "$tmp_root/games/deck-descent.json")" = "$descent_sha"
test "$(sha_file "$tmp_root/games/relay-repair.json")" = "$relay_sha"
test "$(sha_file "$tmp_root/games/salvage-lock.json")" = "$salvage_sha"
test "$(sha_file "$tmp_root/games/signal-triangulation.json")" = "$signal_sha"
test "$(sha_file "$tmp_root/games/vent-crawl.json")" = "$vent_sha"

catalog_federations="$(jq -er '[.missions[].federation_id] | unique | .[]' "$tmp_root/catalog.json")"
if [ "$catalog_federations" != "$federation_id" ]; then
  echo "POAG1 mission federation_id does not equal authenticated PoA genesis" >&2
  exit 1
fi

# Every file the checked-in bundle may contain. Anything present and absent from
# this list is refused below rather than ignored.
expected=(
  "manifest.json"
  "schema.json"
  "catalog.json"
  "games/artificer-logic.json"
  "games/black-box-reconstruction.json"
  "games/deck-descent.json"
  "games/relay-repair.json"
  "games/salvage-lock.json"
  "games/signal-triangulation.json"
  "games/vent-crawl.json"
)

# The emitted games and the measured games are the SAME set, derived independently:
# `content_paths` drives the content root, `expected` drives the checked-in tree.
# A game enrolled in one and forgotten in the other is caught here rather than by a
# content root that quietly stops covering an artifact.
emitted_games="$(cd "$tmp_root" && find games -type f -print | LC_ALL=C sort)"
declared_games="$(printf '%s\n' "${content_paths[@]}" | LC_ALL=C sort)"
if [ "$emitted_games" != "$declared_games" ]; then
  echo "POAG1 emitted game set differs from the content-root path set:" >&2
  diff <(printf '%s\n' "$declared_games") <(printf '%s\n' "$emitted_games") >&2 || true
  exit 1
fi

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

echo "POAG1 artifacts reproduce exactly (federation=$federation_id source=$source_sha artificer=$artificer_sha blackbox=$blackbox_sha descent=$descent_sha relay=$relay_sha salvage=$salvage_sha signal=$signal_sha vent=$vent_sha content_root=$content_root_sha)"
