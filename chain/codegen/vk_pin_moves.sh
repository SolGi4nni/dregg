#!/usr/bin/env bash
# ⚑ THE WHOLE TEST FOR THE VK PIN: regenerating the key MOVES it.
#
# Until 2026-07-28 both chains pinned their "verifying-key commitment" as
# `keccak256("dregg-settlement-vk-dev-setup")` — a hash of a LABEL. That value is
# 0x18f57474785bdd93ff7feb573dfadff69516035997115f2854c93f0f31e1ff76 for the dev key
# and for every key anyone will ever generate, so a VK regeneration left every chain's
# pin byte-identical: the one artifact whose whole job is to notice a key changed
# could not notice. This script is the demonstration that was impossible then.
#
# It never writes to the tree: `gen_verifiers.py --digest` prints and exits, so the
# perturbed spec lives only in a temp file.
#
#   Usage:  chain/codegen/vk_pin_moves.sh
set -euo pipefail

REPO="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$REPO"

SPEC=chain/codegen/dregg_vk.json
GEN="python3 chain/codegen/gen_verifiers.py"
OLD_LABEL_PIN=0x18f57474785bdd93ff7feb573dfadff69516035997115f2854c93f0f31e1ff76
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

fail() { echo "FAIL: $*" >&2; exit 1; }

echo "== [1/4] the committed pin is the digest of the committed key =="
PIN="$($GEN "$SPEC" --digest)"
echo "   VK_DIGEST = $PIN"
[ "$PIN" != "$OLD_LABEL_PIN" ] || fail "the pin is still the label hash"

echo "== [2/4] all three chains pin THAT value =="
# Solidity carries it as a 0x literal; the two Rust emitters as byte arrays.
BARE="${PIN#0x}"
grep -q "$BARE" chain/contracts/DreggSettlementVK.sol \
  || fail "chain/contracts/DreggSettlementVK.sol does not carry $PIN"
echo "   chain/contracts/DreggSettlementVK.sol OK"
python3 - "$BARE" solana-settlement/src/vk.rs cosmos-settlement/src/vk.rs <<'PY' || exit 1
import sys, pathlib, re
want = sys.argv[1]
for path in sys.argv[2:]:
    text = pathlib.Path(path).read_text()
    m = re.search(r"pub const VK_DIGEST: \[u8; 32\] = \[(.*?)\];", text, re.S)
    if not m:
        print(f"FAIL: {path} has no VK_DIGEST", file=sys.stderr); sys.exit(1)
    got = "".join(b[2:] for b in re.findall(r"0x[0-9a-fA-F]{2}", m.group(1)))
    if got != want:
        print(f"FAIL: {path} VK_DIGEST = {got} != spec digest {want}", file=sys.stderr)
        sys.exit(1)
    print(f"   {path} OK")
PY

echo "== [3/4] REGENERATING THE KEY MOVES THE PIN =="
# Perturb each VK component in turn — a real regeneration changes all of them, so
# moving on ANY single one is strictly stronger than "a new ceremony moves it".
for FIELD in alpha_g1 beta_neg_g2 gamma_neg_g2 delta_neg_g2 pedersen_g_g2 \
             pedersen_gsigma_g2 ic0_g1 ic_g1; do
  python3 - "$SPEC" "$TMP/perturbed.json" "$FIELD" <<'PY'
import json, sys
spec = json.load(open(sys.argv[1]))
vk = spec["vk"]
field = sys.argv[3]
target = vk[field][0] if field == "ic_g1" else vk[field]
# Bump the first Fq coordinate we find, keeping it a decimal string.
if "x" in target and isinstance(target["x"], dict):
    target["x"]["c0"] = str(int(target["x"]["c0"]) + 1)
else:
    target["x"] = str(int(target["x"]) + 1)
json.dump(spec, open(sys.argv[2], "w"), indent=2)
PY
  MOVED="$($GEN "$TMP/perturbed.json" --digest)"
  [ "$MOVED" != "$PIN" ] || fail "perturbing $FIELD did NOT move the pin"
  printf '   %-20s -> %s  (moved)\n' "$FIELD" "$MOVED"
done

# The statement width is part of the key's identity too.
python3 - "$SPEC" "$TMP/wider.json" <<'PY'
import json, sys
spec = json.load(open(sys.argv[1]))
spec["format"]["num_public_inputs"] += 1
json.dump(spec, open(sys.argv[2], "w"), indent=2)
PY
WIDER="$($GEN "$TMP/wider.json" --digest)"
[ "$WIDER" != "$PIN" ] || fail "num_public_inputs did NOT move the pin"
printf '   %-20s -> %s  (moved)\n' "num_public_inputs" "$WIDER"

echo "== [4/4] THE REFUTATION: the old label pin moved for NONE of them =="
echo "   keccak256(\"dregg-settlement-vk-dev-setup\") = $OLD_LABEL_PIN"
echo "   ...for every key above. 9 key changes, 0 detected — that was the defect."

echo ""
echo "VK PIN OK — the commitment is a function of the key, on all three chains."
