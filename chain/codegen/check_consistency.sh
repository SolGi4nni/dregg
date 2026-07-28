#!/usr/bin/env bash
# Cross-chain verifier consistency gate.
#
# Proves the ONE source (chain/codegen/dregg_vk.json) keeps the EVM / Solana /
# Cosmos dregg-settlement verifiers CONSISTENT — the exact property hand-porting
# cannot guarantee:
#
#   STRUCTURAL
#     1. codegen output == the committed vk.rs / VK artifacts   (no drift)
#     2. the generated Solidity VK block == the live gnark .sol (EVM in sync)
#     3. the vendored keccak256 == `cast keccak`                (the pin's hash)
#     4. THE VK PIN MOVES WHEN THE KEY DOES                     (vk_pin_moves.sh)
#     5. the Cosmos test fixture == the chain source fixture    (one proof)
#
#   RUNTIME  (the same real proof settlement_groth16.json on all three)
#     6. EVM    forge real-proof test  — accepts real, rejects tampered
#     7. Solana cargo test (alt_bn128) — accepts real, rejects forged
#     8. Cosmos cargo test (arkworks)  — accepts real, rejects tampered
#
# Rust builds route through WARM pbuild lanes (never a fresh lane). forge runs
# locally.
#
#   Usage:  chain/codegen/check_consistency.sh [solana_lane] [cosmos_lane]
set -euo pipefail

REPO="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$REPO"
SOLANA_LANE="${1:-solana-lock}"
COSMOS_LANE="${2:-treasury}"

echo "== [1/8] codegen drift check (spec -> 3 verifiers) =="
python3 chain/codegen/gen_verifiers.py --check

echo "== [2/8] EVM Solidity VK block == live gnark .sol =="
python3 - <<'PY'
import re, pathlib, sys
sol = pathlib.Path("chain/contracts/DreggGroth16Verifier25.sol").read_text()
gen = pathlib.Path("chain/contracts/DreggSettlementVK.sol").read_text()
c = lambda t: {k:int(v,0) for k,v in re.findall(r'uint256 constant (\w+) = (0x[0-9a-fA-F]+|\d+);', t)}
s, g = c(sol), c(gen)
bad = [k for k in g if s.get(k) != g[k]]
print(f"   {len(g)} VK constants; mismatches: {bad}")
sys.exit(1 if bad else 0)
PY

echo "== [3/8] the vendored keccak256 == cast keccak =="
# gen_verifiers.py carries its own Keccak-f[1600] (codegen must not need a pip
# dependency). It self-tests against published vectors on every run; this pins it
# against an INDEPENDENT implementation on the actual VK preimage, so the value all
# three chains install can never be a hash bug agreeing with itself.
python3 - <<'PY' > /tmp/dregg_vk_preimage.hex
import importlib.util, json, pathlib
spec = importlib.util.spec_from_file_location("gv", "chain/codegen/gen_verifiers.py")
gv = importlib.util.module_from_spec(spec); spec.loader.exec_module(gv)
s = json.loads(pathlib.Path("chain/codegen/dregg_vk.json").read_text())
print("0x" + gv.vk_preimage(s).hex())
PY
VENDORED="$(python3 chain/codegen/gen_verifiers.py chain/codegen/dregg_vk.json --digest)"
INDEPENDENT="$(cast keccak "$(cat /tmp/dregg_vk_preimage.hex)")"
rm -f /tmp/dregg_vk_preimage.hex
if [ "$VENDORED" != "$INDEPENDENT" ]; then
  echo "   MISMATCH: vendored $VENDORED vs cast keccak $INDEPENDENT" >&2
  exit 1
fi
echo "   $VENDORED (both implementations agree)"

echo "== [4/8] the VK pin MOVES when the key does =="
chain/codegen/vk_pin_moves.sh

echo "== [5/8] Cosmos fixture == chain source fixture =="
diff -q chain/test/fixtures/settlement_groth16.json \
        cosmos-settlement/tests/fixtures/settlement_groth16.json \
  && echo "   fixtures byte-identical"

echo "== [6/8] EVM forge real-proof test + the VK pin gate =="
( cd chain && forge test --match-contract "DreggSettlementRealProof|DreggSettlementVkPin" )

echo "== [7/8] Solana alt_bn128 verify (pbuild lane: ${SOLANA_LANE}) =="
scripts/pbuild "${SOLANA_LANE}" "cd solana-settlement && cargo test --release"

echo "== [8/8] Cosmos arkworks verify (pbuild lane: ${COSMOS_LANE}) =="
scripts/pbuild "${COSMOS_LANE}" "cd cosmos-settlement && cargo test --release"

echo ""
echo "CONSISTENCY OK — one spec, three chains, the same real proof verifies on all,"
echo "and the on-chain VK commitment is a function of the key rather than of a label."
