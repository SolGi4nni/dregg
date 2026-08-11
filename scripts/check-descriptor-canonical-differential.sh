#!/usr/bin/env bash
# check-descriptor-canonical-differential.sh — the STANDING GATE for the pure-Lean canonical encoder.
#
# ⚑ WHY THIS IS A GATE AND NOT A ONE-TIME CHECK
#
# `Dregg2.Circuit.DescriptorCanonical.canonicalBytes` exists so a descriptor's protocol identity —
# and therefore its semantic fingerprint and its nine `vk_pin` lanes — can be COMPUTED from a Lean
# `EffectVmDescriptor2` term instead of read off a Rust tool and TYPED IN. The specific danger of
# that move is not effort: a WRONG ENCODER FAILS SILENTLY. Every fingerprint it produces would be
# self-consistent and wrong — *"two agreeing transcriptions are not two witnesses; they are one
# witness copied"* — so the differential has to run forever, not once.
#
# ⚠ THE ENCODER IS NOT `emitVmJson2`. That renders the JSON build artifact; this renders the fixed
# binary record the fingerprint is taken over. `by-name/accumulator-nonrev.json` is 10 229 JSON bytes
# and 2 646 canonical bytes, and the record opens `44 52 45 47 47 49 52 32` = "DREGGIR2". Three
# separate write-ups have asserted that the JSON emitter closes this hop; it does not.
#
# FOUR ARMS, each closing a different way the claim could be hollow:
#
#   1. THE PINNED CONSTANTS — magic, schema version, allocation bound, the BabyBear prime and the
#      vacuous-range width, read out of the RUST sources and compared with the Lean. A version bump
#      on one side alone rotates EVERY fingerprint and nothing else would notice.
#   2. THE LEAN BUILD — `Dregg2.Circuit.DescriptorCanonical` + `…Json`, whose named theorems carry
#      the fixed-width lemmas, the reader/emitter round trip, and the two FALSIFIER witnesses (each
#      wrong encoder shown silent on an easy descriptor and caught by a real feature).
#   3. THE DEPLOYED CORPUS — every DescriptorIR-v2 record this tree serves. Rust re-parses and
#      re-encodes each file; Lean re-parses and re-encodes THE SAME FILE; the canonical bytes are
#      compared byte for byte, and the fingerprint and the nine lanes are then recomputed FROM THE
#      LEAN BYTES. Nothing is a committed fixture — there is no expected value stored anywhere.
#   4. THE FALSIFIER CENSUS — the two wrong encoders must each AGREE with the truth on most of the
#      corpus and DIVERGE on at least one descriptor. Both halves are refusals: a falsifier that
#      diverges nowhere has become a no-op, and one that agrees nowhere is a different encoder rather
#      than a probe of one feature. (Enforced inside the driver; arm 3 reports the counts.)
#
# ⚠ `--self-test` is the RED ARM, and it has THREE mutations because the gate has three ways to be
# hollow: a corrupted canonical hex must turn the ENCODER comparison red, a corrupted fingerprint
# must turn the HASH comparison red, and a corpus with the falsifier-bearing descriptors removed must
# turn the FALSIFIER CENSUS red. Each mutation is built CONSTRUCTIVELY and asserted to have landed
# before any verdict is read: a mutation that quietly became a no-op is how an adversary dies while
# its gate stays green.
#
#   scripts/check-descriptor-canonical-differential.sh              # all four arms
#   scripts/check-descriptor-canonical-differential.sh --self-test  # the red arms
#   scripts/check-descriptor-canonical-differential.sh --fast       # arm 1 only: no Lean, no cargo
#
# ⚠ NEVER runs a descriptor regen. It reads `circuit/descriptors/` and encodes what is there.
# `DREGG_DESCRIPTOR_ROOT` retargets BOTH SIDES at a materialised tree together, which is what keeps
# the verdict a fact about two encoders rather than about two trees:
#   DREGG_DESCRIPTOR_ROOT=$(scripts/materialise-descriptors-at.sh HEAD) \
#     scripts/check-descriptor-canonical-differential.sh
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

DESC_ROOT="${DREGG_DESCRIPTOR_ROOT:-$ROOT/circuit/descriptors}"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

LEAN_ENC="$ROOT/metatheory/Dregg2/Circuit/DescriptorCanonical.lean"
LEAN_JSON="$ROOT/metatheory/Dregg2/Circuit/DescriptorCanonicalJson.lean"

# ── ARM 1: the pinned constants, read out of Rust ────────────────────────────────────────────────
echo "== arm 1: the record's pinned constants agree with the Rust sources"
python3 - "$ROOT" "$LEAN_ENC" "$LEAN_JSON" <<'PY'
import re, sys
root, enc_path, json_path = sys.argv[1], sys.argv[2], sys.argv[3]
enc, jsn = open(enc_path).read(), open(json_path).read()
rust_canon = open(root + "/circuit/src/descriptor_ir2_canonical.rs").read()
rust_ir2 = open(root + "/circuit/src/descriptor_ir2.rs").read()
rust_field = open(root + "/circuit/src/field.rs").read()

def need(pattern, text, what):
    m = re.search(pattern, text)
    if not m:
        sys.exit("REFUSED: could not read %s — the gate cannot compare what it cannot find" % what)
    return m.group(1)

# Lean: the magic as a byte list; render it as the ASCII string it stands for.
lean_magic_list = need(r'def CANONICAL_MAGIC : List Nat := \[([^\]]*)\]', enc, "Lean CANONICAL_MAGIC")
lean_magic = "".join(chr(int(x.strip(), 0)) for x in lean_magic_list.split(","))
rust_magic = need(r'EFFECT_VM_DESCRIPTOR2_CANONICAL_MAGIC: \[u8; 8\] = \*b"([^"]*)"', rust_canon,
                  "EFFECT_VM_DESCRIPTOR2_CANONICAL_MAGIC")

pairs = [
    ("magic", lean_magic, rust_magic, "circuit/src/descriptor_ir2_canonical.rs"),
    ("schema version",
     need(r'def CANONICAL_VERSION : Nat := (\d+)', enc, "Lean CANONICAL_VERSION"),
     need(r'EFFECT_VM_DESCRIPTOR2_CANONICAL_VERSION: u16 = (\d+)', rust_canon,
          "EFFECT_VM_DESCRIPTOR2_CANONICAL_VERSION"),
     "circuit/src/descriptor_ir2_canonical.rs"),
    ("max record bytes",
     str(eval(need(r'def MAX_CANONICAL_BYTES : Nat := (.+)', enc, "Lean MAX_CANONICAL_BYTES"))),
     str(eval(need(r'MAX_CANONICAL_EFFECT_VM_DESCRIPTOR2_BYTES: usize = (.+);', rust_canon,
                   "MAX_CANONICAL_EFFECT_VM_DESCRIPTOR2_BYTES").replace("_", ""))),
     "circuit/src/descriptor_ir2_canonical.rs"),
    ("vacuous range bits",
     need(r'def VACUOUS_RANGE_BITS : Nat := (\d+)', jsn, "Lean VACUOUS_RANGE_BITS"),
     need(r'pub const VACUOUS_RANGE_BITS: usize = (\d+);', rust_ir2, "VACUOUS_RANGE_BITS"),
     "circuit/src/descriptor_ir2.rs"),
    ("BabyBear prime",
     need(r'def BABYBEAR_P : Nat := (\d+)', jsn, "Lean BABYBEAR_P"),
     str(eval(need(r'pub const BABYBEAR_P: u32 = (.+);', rust_field, "BABYBEAR_P"))),
     "circuit/src/field.rs"),
]
bad = [p for p in pairs if str(p[1]) != str(p[2])]
for name, l, r, src in pairs:
    print("   %-20s lean=%r rust=%r  (%s)  %s" % (name, l, r, src, "OK" if str(l) == str(r) else "MISMATCH"))
if bad:
    sys.exit("FAIL: %d pinned constant(s) drifted. The schema version and the magic are INSIDE the "
             "record, so a one-sided change rotates EVERY fingerprint and refuses every old one."
             % len(bad))
PY

if [[ "$FAST" == "1" ]]; then
  echo "   (--fast: arms 2-4 skipped — arm 2 is a \`lake build\`, arms 3-4 are the --all row)"
  exit 0
fi

# ── ARM 2: the named theorems, in the Lean build ─────────────────────────────────────────────────
echo "== arm 2: Dregg2.Circuit.DescriptorCanonical{,Json} (fixed-width lemmas, round trip, falsifier witnesses)"
(cd "$ROOT/metatheory" && lake build Dregg2.Circuit.DescriptorCanonical Dregg2.Circuit.DescriptorCanonicalJson)

# ── ARM 3+4: every served descriptor, both sides recomputed from the same file ───────────────────
echo "== arm 3: Lean canonicalBytes vs the deployed Rust encoder, over every served descriptor"
cargo run -q -p dregg-circuit --example descriptor_canonical_dump > "$TMP/dump.tsv" 2> "$TMP/dump.err" || {
  echo "FAIL: the descriptor dump refused"; cat "$TMP/dump.err"; exit 1; }
grep -F "descriptor_canonical_dump:" "$TMP/dump.err" | sed 's/^/   /'
ROWS="$(wc -l < "$TMP/dump.tsv" | tr -d ' ')"
echo "   dumped $ROWS ir:2 descriptors"

run_driver() {  # <dump> <min-rows> -> exit code, log on stdout
  (cd "$ROOT/metatheory" && lake env lean --run CheckDescriptorCanonical.lean "$1" "$DESC_ROOT" "$2")
}

if [[ "$SELF_TEST" == "1" ]]; then
  # ⚑ RED ARM (a) + (b): one mutation PER HOP, both built CONSTRUCTIVELY and asserted to have
  # landed. Row 0's canonical hex breaks the ENCODER comparison; row 1's fingerprint breaks the
  # HASH comparison. A red that only exercised one would leave the other unfalsified.
  python3 - "$TMP/dump.tsv" "$TMP/dump-mutated.tsv" <<'PY'
import sys
src, dst = sys.argv[1], sys.argv[2]
lines = open(src).read().splitlines()
if len(lines) < 2:
    sys.exit("REFUSED: dump has %d rows, need 2 to mutate both hops" % len(lines))

f0 = lines[0].split("\t")
if len(f0) != 5 or len(f0[2]) < 64:
    sys.exit("REFUSED: dump row 0 is not <name>/<path>/<canonical hex>/<fp>/<lanes>; the encoder mutation would be a no-op")
old = f0[2]
# Flip one byte in the MIDDLE of the record, past the header, so the mutation exercises the
# byte-for-byte comparison rather than the magic.
mid = (len(old) // 2) & ~1
f0[2] = old[:mid] + ("1" if old[mid] != "1" else "2") + old[mid + 1:]
assert f0[2] != old, "encoder mutation was a no-op"
assert len(f0[2]) == len(old), "encoder mutation changed the record length"
lines[0] = "\t".join(f0)

f1 = lines[1].split("\t")
if len(f1) != 5 or len(f1[3]) != 64:
    sys.exit("REFUSED: dump row 1 has no 64-hex fingerprint; the hash mutation would be a no-op")
oldfp = f1[3]
f1[3] = ("1" if oldfp[0] != "1" else "2") + oldfp[1:]
assert f1[3] != oldfp, "hash mutation was a no-op"
lines[1] = "\t".join(f1)

open(dst, "w").write("\n".join(lines) + "\n")
print("   encoder mutation %s: canonical byte at hex offset %d flipped" % (f0[0], mid))
print("   hash mutation    %s: fingerprint %s... -> %s..." % (f1[0], oldfp[:12], f1[3][:12]))
PY
  set +e
  run_driver "$TMP/dump-mutated.tsv" 100 > "$TMP/selftest-ab.log" 2>&1
  RC=$?
  set -e
  if [[ "$RC" == "0" ]]; then
    echo "SELF-TEST FAILED: the differential stayed GREEN over a corrupted canonical record."
    sed -n '1,20p' "$TMP/selftest-ab.log"; exit 1
  fi
  for want in "disagree between the Lean canonical encoder" "fingerprints disagree"; do
    grep -q "$want" "$TMP/selftest-ab.log" || {
      echo "SELF-TEST FAILED: nonzero exit ($RC) but the log never says: $want"
      sed -n '1,40p' "$TMP/selftest-ab.log"; exit 1; }
  done
  echo "   RED ARM (a)+(b) PASSED: a corrupted canonical record AND a corrupted fingerprint each turn it red (exit $RC)"

  # ⚑ RED ARM (c): the FALSIFIER CENSUS must be able to go red. Strip every descriptor that carries
  # a chal_gate or a ported proof_bind and the two wrong encoders become no-ops on what is left —
  # which is exactly the state the census refuses. Without this arm, a falsifier that stopped
  # falsifying would leave the gate green and nothing would look.
  python3 - "$TMP/dump.tsv" "$TMP/dump-plain.tsv" "$DESC_ROOT" <<'PY'
import json, os, sys
src, dst, root = sys.argv[1], sys.argv[2], sys.argv[3]
kept, dropped = [], 0
for line in open(src).read().splitlines():
    f = line.split("\t")
    d = json.load(open(os.path.join(root, f[1])))
    cs = d["constraints"]
    has_chal = any(c["t"] == "chal_gate" for c in cs)
    has_port = any(c["t"] == "proof_bind" and c["bound"]["t"] == "port" for c in cs)
    if has_chal or has_port:
        dropped += 1
    else:
        kept.append(line)
if dropped == 0:
    sys.exit("REFUSED: no descriptor in the corpus carries a chal_gate or a ported proof_bind, so "
             "removing them is a no-op and this red arm would prove nothing")
if not kept:
    sys.exit("REFUSED: every descriptor carries one, so the filtered corpus is empty")
open(dst, "w").write("\n".join(kept) + "\n")
print("   falsifier-free corpus: %d rows kept, %d carriers dropped" % (len(kept), dropped))
PY
  set +e
  run_driver "$TMP/dump-plain.tsv" 10 > "$TMP/selftest-c.log" 2>&1
  RC=$?
  set -e
  if [[ "$RC" == "0" ]]; then
    echo "SELF-TEST FAILED: the falsifier census stayed GREEN on a corpus where both falsifiers are no-ops."
    sed -n '1,20p' "$TMP/selftest-c.log"; exit 1
  fi
  for want in "chalAsConst\` falsifier diverged on NONE" "portNamesElided\` falsifier diverged on NONE"; do
    grep -q "$want" "$TMP/selftest-c.log" || {
      echo "SELF-TEST FAILED: nonzero exit ($RC) but the log never says: $want"
      sed -n '1,40p' "$TMP/selftest-c.log"; exit 1; }
  done
  echo "   RED ARM (c) PASSED: a corpus that disarms both falsifiers turns the census red (exit $RC)"
  exit 0
fi

run_driver "$TMP/dump.tsv" 100
