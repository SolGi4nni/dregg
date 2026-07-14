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
#     3. the Cosmos test fixture == the chain source fixture    (one proof)
#
#   RUNTIME  (the same real proof settlement_groth16.json on all three)
#     4. EVM    forge real-proof test  — accepts real, rejects tampered
#     5. Solana cargo test (alt_bn128) — accepts real, rejects forged
#     6. Cosmos cargo test (arkworks)  — accepts real, rejects tampered
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

echo "== [1/6] codegen drift check (spec -> 3 verifiers) =="
python3 chain/codegen/gen_verifiers.py --check

echo "== [2/6] EVM Solidity VK block == live gnark .sol =="
python3 - <<'PY'
import re, pathlib, sys
sol = pathlib.Path("chain/contracts/DreggGroth16Verifier25.sol").read_text()
gen = pathlib.Path("chain/codegen/out/DreggGroth16Verifier25.vk.sol").read_text()
c = lambda t: {k:int(v,0) for k,v in re.findall(r'uint256 constant (\w+) = (0x[0-9a-fA-F]+|\d+);', t)}
s, g = c(sol), c(gen)
bad = [k for k in g if s.get(k) != g[k]]
print(f"   {len(g)} VK constants; mismatches: {bad}")
sys.exit(1 if bad else 0)
PY

echo "== [3/6] Cosmos fixture == chain source fixture =="
diff -q chain/test/fixtures/settlement_groth16.json \
        cosmos-settlement/tests/fixtures/settlement_groth16.json \
  && echo "   fixtures byte-identical"

echo "== [4/6] EVM forge real-proof test =="
( cd chain && forge test --match-contract DreggSettlementRealProof )

echo "== [5/6] Solana alt_bn128 verify (pbuild lane: ${SOLANA_LANE}) =="
scripts/pbuild "${SOLANA_LANE}" "cd solana-settlement && cargo test --release"

echo "== [6/6] Cosmos arkworks verify (pbuild lane: ${COSMOS_LANE}) =="
scripts/pbuild "${COSMOS_LANE}" "cd cosmos-settlement && cargo test --release"

echo ""
echo "CONSISTENCY OK — one spec, three chains, the same real proof verifies on all."
