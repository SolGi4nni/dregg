#!/usr/bin/env bash
# THE BROWSER-SURFACE TEETH: run the demos' own spines headless against a card-world
# wasm bundle and assert BOTH polarities — the verifying path verifies, the refusing
# path refuses.
#
# WHY THIS IS ITS OWN FILE
# -----------------------
# These two checks used to live inline in `scripts/build-pages-dist.sh`, i.e. they ran
# ONLY at ASSEMBLY time. That put them in the wrong place once the Pages deploy split
# into a fast content path and a heavy wasm path (`.github/workflows/pages-wasm.yml`):
#
#   * a genuine wasm/circuit break belongs to the run that BUILT the wasm — the heavy
#     workflow. It should go RED there, weekly, on its own schedule.
#   * the fast content path must NOT inherit that failure. A stale baked demo artifact
#     must never block a typo fix on the landing page. There it is reported as a
#     MARKER on the affected surface (see scripts/stamp-wasm-provenance.sh) and the
#     deploy proceeds.
#
# Same teeth, one source, two consumers with deliberately different polarity:
#   heavy wasm job     : `scripts/check-web-surface-teeth.sh wasm/pkg`   -> exit 1 = RED job
#   build-pages-dist.sh: full build  -> a failure ABORTS the assembly (unchanged)
#                        REUSE_WASM  -> a failure is RECORDED and marked in the site
#
# WHAT IT CHECKS
#   1. LIGHT-CLIENT FRESHNESS: the committed `site/light-client/history.json` aggregate
#      must ATTEST under this exact engine. A circuit/VK epoch that obsoletes the baked
#      artifact is caught here instead of shipping a demo the visitor's tab refuses.
#      Regenerate the aggregate with:
#        cargo run --release -p dregg-lightclient --bin produce_history_envelope \
#          --features prover -- 3 7 > site/light-client/history.json
#   2. TRANSCLUSION: a verified include SHOWS the committed bytes, a LIVE read FOLLOWS
#      an amend, a receipt-pinned backlink is recorded, and a byte-tamper forge is
#      REFUSED with the named ContentHashMismatch. A surface that stops refusing (or
#      stops verifying) is as broken as one that stops loading.
#
# USAGE
#   scripts/check-web-surface-teeth.sh [pkg-dir] [history-json]
#     pkg-dir       default ./wasm/pkg   — must contain dregg_wasm.js + dregg_wasm_bg.wasm
#     history-json  default ./site/light-client/history.json
#
# Exit 0 = both teeth green. Exit 1 = a tooth bit (message on stderr names which).
# Exit 2 = the bundle is ABSENT/unusable, i.e. there was nothing to test. Callers MUST
#          distinguish 2 from 1: 1 is "the surface is broken", 2 is "the surface is not
#          in this build at all", and those get different treatment in the site.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PKG="${1:-$ROOT/wasm/pkg}"
HISTORY="${2:-$ROOT/site/light-client/history.json}"

# Absolute, because the node snippets below `import()` the glue by path.
case "$PKG" in /*) ;; *) PKG="$(cd "$PKG" 2>/dev/null && pwd || echo "$PKG")" ;; esac

command -v node >/dev/null 2>&1 || {
  echo "check-web-surface-teeth: node is required to drive the wasm bundle" >&2; exit 2; }

if [ ! -s "$PKG/dregg_wasm.js" ] || [ ! -s "$PKG/dregg_wasm_bg.wasm" ]; then
  echo "check-web-surface-teeth: no card-world bundle at $PKG — nothing to test" >&2
  exit 2
fi
if [ ! -s "$HISTORY" ]; then
  echo "check-web-surface-teeth: no baked aggregate at $HISTORY — nothing to test" >&2
  exit 2
fi

# ── TOOTH 1: light-client freshness ──────────────────────────────────────────────
node --input-type=module -e "
import { readFileSync } from 'node:fs';
const m = await import('$PKG/dregg_wasm.js');
await m.default({ module_or_path: readFileSync('$PKG/dregg_wasm_bg.wasm') });
const baked = JSON.parse(readFileSync('$HISTORY', 'utf8'));
let v;
try { v = m.verify_devnet_history(JSON.stringify(baked.envelope), baked.anchor_hex); }
catch (e) { v = { aggregate_attested: false, named_floor: String(e?.message ?? e) }; }
if (!v.aggregate_attested) {
  console.error('TOOTH light-client-freshness: $HISTORY does NOT attest under this engine — the circuit/VK moved since the artifact was folded. Regenerate it (see the header of scripts/check-web-surface-teeth.sh). Refusal: ' + v.named_floor);
  process.exit(1);
}
console.log('light-client freshness tooth: the baked aggregate attests, legs 1+2 (' + v.num_turns + ' turns; finality_attested=' + v.finality_attested + ')');
"

# ── TOOTH 2: transclusion, both polarities ───────────────────────────────────────
node --input-type=module -e "
import { readFileSync } from 'node:fs';
const m = await import('$PKG/dregg_wasm.js');
await m.default({ module_or_path: readFileSync('$PKG/dregg_wasm_bg.wasm') });
const h = m.transclusion_create();
const body = '<h1>the charter</h1>';
m.transclusion_publish(h, 'constitution', body, 'dregg://constitution');
m.transclusion_publish(h, 'essay', '<p>an essay</p>', 'dregg://essay');
const q = m.transclusion_include_into(h, 'essay', 'constitution');
if (!q.verifies || q.text !== body || !q.finalized) {
  console.error('TOOTH transclusion: include did not verify the committed bytes: ' + JSON.stringify(q));
  process.exit(1);
}
const bl = m.transclusion_backlinks(h, 'constitution');
if (bl.count !== 1 || bl.observers[0].observer_name !== 'essay') {
  console.error('TOOTH transclusion: the include did not record a receipt-pinned backlink: ' + JSON.stringify(bl));
  process.exit(1);
}
const amended = '<h1>the charter, amended</h1>';
m.transclusion_amend(h, 'constitution', amended);
const live = m.transclusion_read_live(h, 'constitution');
if (live.text !== amended || !live.verifies) {
  console.error('TOOTH transclusion: the live read did not follow the amend: ' + JSON.stringify(live));
  process.exit(1);
}
const forge = m.transclusion_forge_attempt(h, 'constitution', '<h1>PWNED</h1>');
if (!forge.refused || forge.reason !== 'ContentHashMismatch') {
  console.error('TOOTH transclusion: the forge was NOT refused with ContentHashMismatch: ' + JSON.stringify(forge));
  process.exit(1);
}
console.log('transclusion tooth: include verifies + backlink pinned + live follows + the forge is refused (' + forge.reason + ')');
"
