#!/usr/bin/env bash
# check-blake3-differential.sh — the STANDING GATE for the pure-Lean BLAKE3.
#
# ⚑ WHY THIS IS A GATE AND NOT A ONE-TIME CHECK
#
# `Dregg2.Crypto.Blake3Compute.blake3Derive` exists so a descriptor fingerprint / `vk_pin` can be
# COMPUTED in Lean instead of read off a Rust tool and TYPED IN. The specific danger of that move is
# not effort — it is that a WRONG `blake3Derive` FAILS SILENTLY: every pin it produces would be
# self-consistent and wrong, which is *"two agreeing transcriptions are not two witnesses; they are
# one witness copied"*, generated at scale. So the differential has to run forever, not once.
#
# FOUR ARMS, each closing a different way the claim could be hollow:
#
#   1. CONTEXT STRINGS — Lean's `descriptor2FingerprintContext` / `airFingerprintContext` are read
#      out of the RUST sources and compared. These two strings are the only part of the fingerprint
#      that exists on both sides; derive-key mode makes the context part of the key, so a one-
#      character drift changes every pin and nothing else would notice.
#   2. KAT TABLE PROVENANCE — the 35 official vectors transcribed into `Blake3Kat.lean` are
#      re-derived from the BLAKE3 team's own committed `test_vectors.json` and compared literal for
#      literal. Without this arm the Lean theorems would pin the implementation against a table that
#      could itself be mistyped, which is the same defect one level up.
#   3. THE VECTORS THEMSELVES — `lake build` of `Dregg2.Crypto.Blake3Kat`, whose named theorems
#      (`native_decide` + `#assert_compiled`) run all 35 lengths in all THREE modes, plus the
#      falsifiers proving the chunk-boundary lengths and the mode flags are load-bearing.
#   4. THE DEPLOYED INPUTS — every DescriptorIR-v2 record this tree serves (158 at time of writing),
#      canonical bytes and Rust fingerprints regenerated FRESH by
#      `cargo run -p dregg-circuit --example descriptor_canonical_dump`, re-hashed by pure Lean.
#      Nothing is a committed fixture; there is no expected value stored anywhere to go stale.
#
# ⚠ `--self-test` is the RED ARM. It corrupts one expected fingerprint in an in-memory copy of the
# dump and FAILS if the differential stays green. A gate that cannot go red is not a gate, and this
# one's whole job is to be able to see a silent wrong hash.
#
#   scripts/check-blake3-differential.sh              # all four arms
#   scripts/check-blake3-differential.sh --self-test  # the red arm
#   scripts/check-blake3-differential.sh --fast       # arms 1+2 only: no Lean, no cargo, ~0.1s
#
# ⚑ WHY `--fast` EXISTS AND WHAT IT IS FOR. Arms 1 and 2 are the pure TRANSCRIPTION arms — two
# context strings and a 35-row table, the three things here that a human typed and that therefore
# rot. They cost nothing and belong in the cheap gate table. Arm 3 needs no row of its own at all:
# `Dregg2.Crypto.Blake3Kat` is rooted in `Dregg2.lean`, so its theorems run in the ordinary
# `lake build`. Arm 4 is the minute-scale one and rides `--all`.
#
# ⚠ NEVER runs a descriptor regen. It reads `circuit/descriptors/` and hashes what is there.
# `DREGG_DESCRIPTOR_ROOT` retargets it at a materialised tree:
#   DREGG_DESCRIPTOR_ROOT=$(scripts/materialise-descriptors-at.sh HEAD) scripts/check-blake3-differential.sh
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SELF_TEST=0
FAST=0
case "${1:-}" in
  --self-test) SELF_TEST=1 ;;
  --fast)      FAST=1 ;;
  "")          ;;
  *)           echo "unknown argument: $1" >&2; exit 2 ;;
esac

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

KAT_JSON="$ROOT/metatheory/tests/fixtures/blake3_official_test_vectors.json"
KAT_LEAN="$ROOT/metatheory/Dregg2/Crypto/Blake3Kat.lean"
LEAN_COMPUTE="$ROOT/metatheory/Dregg2/Crypto/Blake3Compute.lean"

# ── ARM 1: the two context strings, read out of Rust ─────────────────────────────────────────────
echo "== arm 1: derive-key context strings agree with the Rust sources"
python3 - "$ROOT" "$LEAN_COMPUTE" <<'PY'
import re, sys
root, lean_path = sys.argv[1], sys.argv[2]
lean = open(lean_path).read()

def lean_const(name):
    m = re.search(r'def %s : String :=\s*\n?\s*"([^"]*)"' % re.escape(name), lean)
    if not m:
        sys.exit("REFUSED: could not read Lean constant %s — the gate cannot compare what it cannot find" % name)
    return m.group(1)

rust_ir2 = open(root + "/circuit/src/descriptor_ir2_canonical.rs").read()
m = re.search(r'EFFECT_VM_DESCRIPTOR2_FINGERPRINT_CONTEXT: &str =\s*\n?\s*"([^"]*)"', rust_ir2)
if not m:
    sys.exit("REFUSED: EFFECT_VM_DESCRIPTOR2_FINGERPRINT_CONTEXT not found in descriptor_ir2_canonical.rs")
rust_ir2_ctx = m.group(1)

rust_air = open(root + "/circuit/src/air_descriptor.rs").read()
m = re.search(r'new_derive_key\("([^"]*)"\)', rust_air)
if not m:
    sys.exit("REFUSED: no new_derive_key context found in air_descriptor.rs")
rust_air_ctx = m.group(1)

pairs = [
    ("descriptor2FingerprintContext", lean_const("descriptor2FingerprintContext"), rust_ir2_ctx,
     "circuit/src/descriptor_ir2_canonical.rs"),
    ("airFingerprintContext", lean_const("airFingerprintContext"), rust_air_ctx,
     "circuit/src/air_descriptor.rs"),
]
bad = [p for p in pairs if p[1] != p[2]]
for name, l, r, src in pairs:
    print("   %-32s lean=%r rust=%r  (%s)  %s" % (name, l, r, src, "OK" if l == r else "MISMATCH"))
if bad:
    sys.exit("FAIL: %d derive-key context string(s) drifted. Derive-key mode folds the context into "
             "the KEY, so this moves EVERY fingerprint." % len(bad))
PY

# ── ARM 2: the KAT table in Lean is the BLAKE3 team's file ───────────────────────────────────────
echo "== arm 2: the 35 official vectors in Blake3Kat.lean are the committed test_vectors.json"
python3 - "$KAT_JSON" "$KAT_LEAN" <<'PY'
import json, re, sys
kat_json, kat_lean = sys.argv[1], sys.argv[2]
d = json.load(open(kat_json))
lean = open(kat_lean).read()

m = re.search(r'def officialKats[^\[]*\[(.*?)\n\]', lean, re.S)
if not m:
    sys.exit("REFUSED: officialKats table not found in Blake3Kat.lean")
rows = re.findall(r'\((\d+),\s*"([0-9a-f]+)",\s*"([0-9a-f]+)",\s*"([0-9a-f]+)"\)', m.group(1), re.S)
if len(rows) != len(d["cases"]):
    sys.exit("FAIL: Lean table has %d rows, test_vectors.json has %d" % (len(rows), len(d["cases"])))
for (n, h, k, dk), c in zip(rows, d["cases"]):
    if (int(n), h, k, dk) != (c["input_len"], c["hash"], c["keyed_hash"], c["derive_key"]):
        sys.exit("FAIL: Lean KAT row for input_len=%s does not match test_vectors.json" % n)

for name, want in (("officialKatKey", d["key"]), ("officialKatContext", d["context_string"])):
    m = re.search(r'def %s : String := "([^"]*)"' % name, lean)
    if not m or m.group(1) != want:
        sys.exit("FAIL: Lean %s does not match test_vectors.json (%r)" % (name, want))

lens = sorted(c["input_len"] for c in d["cases"])
for boundary in (63, 64, 65, 1023, 1024, 1025, 2048, 2049):
    if boundary not in lens:
        sys.exit("FAIL: chunk/block boundary length %d absent from the vector set" % boundary)
print("   %d official vectors, 3 modes each, block+chunk boundaries present, outputs %d bytes"
      % (len(rows), len(rows[0][1]) // 2))
PY

if [[ "$FAST" == "1" ]]; then
  echo "   (--fast: arms 3 and 4 skipped — arm 3 rides \`lake build\` via Dregg2.lean, arm 4 is the --all row)"
  exit 0
fi

# ── ARM 3: the vectors, as named theorems in the Lean build ──────────────────────────────────────
echo "== arm 3: Dregg2.Crypto.Blake3Kat (35 vectors x 3 modes + falsifiers, native_decide + #assert_compiled)"
(cd "$ROOT/metatheory" && lake build Dregg2.Crypto.Blake3Compute Dregg2.Crypto.Blake3Kat)

# ── ARM 4: every served descriptor, both sides recomputed ────────────────────────────────────────
echo "== arm 4: pure-Lean blake3Derive vs the deployed Rust fingerprint, over every served descriptor"
cargo run -q -p dregg-circuit --example descriptor_canonical_dump > "$TMP/dump.tsv" 2> "$TMP/dump.err" || {
  echo "FAIL: the descriptor dump refused"; cat "$TMP/dump.err"; exit 1; }
grep -F "descriptor_canonical_dump:" "$TMP/dump.err" | sed 's/^/   /'
ROWS="$(wc -l < "$TMP/dump.tsv" | tr -d ' ')"
echo "   dumped $ROWS ir:2 descriptors"

if [[ "$SELF_TEST" == "1" ]]; then
  # ⚑ THE RED ARM, one mutation PER HOP. Row 0's fingerprint breaks hop 1, row 1's first lane breaks
  # hop 2 — because a red that only exercised the hash would leave the lane encoder unfalsified, and
  # the lane packing is the half six files each carried their own copy of. Both are built
  # CONSTRUCTIVELY and asserted to have landed before any verdict is read: a mutation that quietly
  # became a no-op is how an adversary dies while its gate stays green
  # (`minted-a-falsifier-that-stopped-falsifying`).
  python3 - "$TMP/dump.tsv" "$TMP/dump-mutated.tsv" <<'PY'
import sys
src, dst = sys.argv[1], sys.argv[2]
lines = open(src).read().splitlines()
if len(lines) < 2:
    sys.exit("REFUSED: dump has %d rows, need 2 to mutate both hops" % len(lines))

f0 = lines[0].split("\t")
if len(f0) != 5 or len(f0[3]) != 64:
    sys.exit("REFUSED: dump row 0 is not <name>/<path>/<hex>/<64-hex>/<lanes>; the hop-1 mutation would be a no-op")
old_fp = f0[3]
f0[3] = ("1" if old_fp[0] != "1" else "2") + old_fp[1:]
assert f0[3] != old_fp, "hop-1 mutation was a no-op"
lines[0] = "\t".join(f0)

f1 = lines[1].split("\t")
if len(f1) != 5:
    sys.exit("REFUSED: dump row 1 has %d fields, expected 5" % len(f1))
lanes = f1[4].split(",")
if len(lanes) != 9:
    sys.exit("REFUSED: dump row 1 does not carry nine lanes; the hop-2 mutation would be a no-op")
old_lane = lanes[0]
lanes[0] = str((int(old_lane) + 1) % (1 << 29))
assert lanes[0] != old_lane, "hop-2 mutation was a no-op"
f1[4] = ",".join(lanes)
lines[1] = "\t".join(f1)

open(dst, "w").write("\n".join(lines) + "\n")
print("   hop-1 mutation %s: fingerprint %s... -> %s..." % (f0[0], old_fp[:12], f0[3][:12]))
print("   hop-2 mutation %s: lane0 %s -> %s" % (f1[0], old_lane, lanes[0]))
PY
  set +e
  (cd "$ROOT/metatheory" && lake env lean --run CheckBlake3Differential.lean "$TMP/dump-mutated.tsv") \
    > "$TMP/selftest.log" 2>&1
  RC=$?
  set -e
  if [[ "$RC" == "0" ]]; then
    echo "SELF-TEST FAILED: the differential stayed GREEN over a corrupted fingerprint."
    sed -n '1,20p' "$TMP/selftest.log"
    exit 1
  fi
  # ⚠ BOTH hops must be NAMED in the failure, not merely a nonzero exit — a refusal rendering as the
  # expected verdict is its own defect class, and a red reporting only hop 1 leaves hop 2
  # unfalsified.
  for want in "disagree between pure-Lean blake3Derive" "disagree between Lean keyToLanes9"; do
    grep -q "$want" "$TMP/selftest.log" || {
      echo "SELF-TEST FAILED: nonzero exit ($RC) but the log never says: $want"
      sed -n '1,30p' "$TMP/selftest.log"
      exit 1
    }
  done
  echo "   SELF-TEST PASSED: a corrupted fingerprint AND a corrupted lane each turn the differential red (exit $RC)"
  exit 0
fi

(cd "$ROOT/metatheory" && lake env lean --run CheckBlake3Differential.lean "$TMP/dump.tsv")
