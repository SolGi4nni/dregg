#!/usr/bin/env bash
# floor-census-v3-run.sh — run `#floor_census` (and optionally `#floor_ratchet`) over the LARGEST
# environment this tree can currently produce.
#
# `scripts/run_floor_census.lean` does `import Dregg2`, which needs a GREEN root. When the root is
# red on somebody else's in-flight work there is no `Dregg2.olean` and the census cannot run at
# all — which is how a measurement instrument ends up never being run. This driver takes the
# root's OWN import list and keeps the modules whose oleans exist, so the census measures the
# tree that elaborates and NAMES the modules it could not reach.
#
#   usage: metatheory/scripts/floor-census-v3-run.sh <out.tsv> [ratchet]
set -euo pipefail
cd "$(dirname "$0")/.."

OUT="${1:-/tmp/floor-census-v3.tsv}"
WANT_RATCHET="${2:-}"
LIB=".lake/build/lib/lean"
DRIVER="scripts/.floor_census_v3_driver.lean"

python3 - "$LIB" "$DRIVER" "$OUT" "$WANT_RATCHET" <<'PY'
import os, re, sys
lib, driver, out, want_ratchet = sys.argv[1:5]
mods, missing = [], []
for line in open('Dregg2.lean'):
    m = re.match(r'^import\s+([A-Za-z0-9_.À-￿]+)', line)
    if not m:
        continue
    mod = m.group(1)
    if os.path.exists(os.path.join(lib, mod.replace('.', os.sep) + '.olean')):
        mods.append(mod)
    else:
        missing.append(mod)
for extra in ('Dregg2.Verify.FloorCensus', 'Dregg2.Verify.FloorRatchet'):
    if extra not in mods and os.path.exists(
            os.path.join(lib, extra.replace('.', os.sep) + '.olean')):
        mods.append(extra)
with open(driver, 'w') as fh:
    for mod in mods:
        fh.write('import %s\n' % mod)
    fh.write('\n#floor_census "%s"\n' % out)
    if want_ratchet:
        fh.write('#floor_ratchet_floors\n#floor_ratchet\n')
print('MODULES-PRESENT %d' % len(mods))
print('MODULES-MISSING %d' % len(missing))
for mod in missing:
    print('MISSING %s' % mod)
PY

echo "=== elaborating driver"
exec lake env lean "$DRIVER"
