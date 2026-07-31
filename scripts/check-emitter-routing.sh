#!/usr/bin/env bash
# ⚑ EVERY Lean EMITTER MUST BE ROUTED, OR ITS ARTIFACT GOES STALE ON EVERY FLAG DAY.
#
# `scripts/emit_descriptors.py` carries an `EMITTERS` list. An `Emit*.lean` absent from it is never
# re-run by a geometry flag day, so the artifact it produced keeps whatever widths were current when
# somebody last ran it BY HAND — and the failure surfaces later as a test comparing a live descriptor
# against a months-old fixture, which reads as a stale test rather than a stale artifact.
#
# Measured 2026-07-31: THREE separate lanes hit this independently in one day, each rediscovering it
# from a different red:
#   * `circuit/tests/fixtures/{discharge,vault}-sat-v3-staged.json` went stale TWICE in two flag days
#     (`EmitDischargeVaultSat.lean` — unrouted), and a lane regenerated them by hand both times.
#   * `EmitExactNullifierAafiRotatedState.lean`'s 1274-constraint descriptor sits at
#     `staged-unregistered-no-vk` while a census concluded the arity-17 exit "is registration, not
#     authoring" — an artifact nothing re-emits.
#   * A fields-nonet lane found `circuit/staged-descriptors/fnsp-v3/*` "had simply been omitted from
#     the flag day".
#
# This gate does NOT force every emitter into the driver — several are genuinely one-shot goldens or
# probes, and sweeping them in would run 28 emitters on every flag day. It forces each one to be
# EXPLICIT: routed, or listed here with a reason. An emitter that is neither is the silent case.
set -uo pipefail
cd "$(dirname "$0")/.."

# Emitters deliberately NOT in the driver. Each needs a reason a reader can check.
# ⚠ Adding a name here without a reason is the move this gate exists to catch.
declare -A UNROUTED_OK=(
  [EmitCheck.lean]="a checker, not an emitter — produces no committed artifact"
  [EmitMarshalGolden.lean]="one-shot marshal golden; regenerated deliberately when the wire changes"
  [EmitAutomataflGolden.lean]="one-shot game golden, no rotated geometry in its output"
)

routed=$(python3 - <<'PY'
import pathlib, re
d = pathlib.Path("scripts/emit_descriptors.py").read_text()
m = re.search(r"EMITTERS = \[(.*?)\n\]", d, re.S)
for f in re.findall(r'"([^"]+\.lean)"', m.group(1) if m else ""):
    print(f.split("/")[-1])
PY
)

fail=0
while IFS= read -r p; do
  n="$(basename "$p")"
  grep -qx "$n" <<<"$routed" && continue
  [[ -v UNROUTED_OK["$n"] ]] && continue
  echo "  UNROUTED  $p"
  fail=$((fail + 1))
done < <(find metatheory -name 'Emit*.lean' -not -path '*/.lake/*' | sort)

if [ "$fail" -ne 0 ]; then
  cat <<'MSG'

check-emitter-routing: FAIL — the emitters above are in NEITHER the driver's EMITTERS list NOR the
allowlist in this script.

Each one is an artifact that a geometry flag day will silently leave behind. Either:
  * add it to `EMITTERS` in scripts/emit_descriptors.py (it re-emits with everything else), or
  * add it to UNROUTED_OK here WITH A REASON a reader can check.

"It has always been like that" is not a reason — three lanes rediscovered this in one day.
MSG
  exit 1
fi
echo "check-emitter-routing: PASS — every Lean emitter is routed or explicitly excused."
