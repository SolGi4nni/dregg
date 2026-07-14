#!/usr/bin/env python3
"""Extract the canonical dregg Groth16 VK/format spec from the gnark output.

THE ONE SOURCE (bootstrap). The gnark trusted setup emits its verifying key baked
into `chain/contracts/DreggGroth16Verifier25.sol` (via
`groth16.VerifyingKey.ExportSolidity`, see chain/gnark/settlement_snark_test.go).
Historically each chain re-encoded that VK by hand (Cosmos) or by a chain-specific
script (Solana), which can DRIFT.

This script lifts the VK constants + the proof-format parameters ONCE into a single
chain-agnostic representation, `chain/codegen/dregg_vk.json`. That JSON is then the
sole input to `gen_verifiers.py`, which emits the EVM / Solana / Cosmos VK encodings
consistently by construction. Re-run this only when the gnark setup is regenerated
(a new VK); day-to-day the committed `dregg_vk.json` is the source.

  Usage:  python3 chain/codegen/extract_vk_spec.py \
              chain/contracts/DreggGroth16Verifier25.sol \
              chain/codegen/dregg_vk.json
"""
import json
import pathlib
import re
import sys

# BN254 scalar field order R (gnark/Solidity `R` constant), as the canonical decimal.
BN254_R = 21888242871839275222246405745257275088548364400416034343698204186575808495617
NUM_PUBLIC_INPUTS = 25
NUM_IC = 26  # PUB_0..PUB_25: 25 statement lanes + 1 commitment-hash base.


def main() -> None:
    sol_path = pathlib.Path(sys.argv[1])
    out_path = pathlib.Path(sys.argv[2])
    text = sol_path.read_text()

    def const(name: str) -> str:
        m = re.search(rf"uint256 constant {name} = (0x[0-9a-fA-F]+|\d+);", text)
        if not m:
            raise SystemExit(f"extract: missing constant {name} in {sol_path}")
        raw = m.group(1)
        return str(int(raw, 0))

    # Sanity: the Solidity R must equal the pinned BN254 scalar field.
    r_sol = int(const("R"))
    if r_sol != BN254_R:
        raise SystemExit(f"extract: Solidity R {r_sol} != pinned BN254 R {BN254_R}")

    def g1(px: str, py: str) -> dict:
        return {"x": const(px), "y": const(py)}

    # gnark/Solidity store G2 as (x.c0, x.c1, y.c0, y.c1); β/γ/δ are stored NEGATED.
    def g2(prefix: str) -> dict:
        return {
            "x": {"c0": const(f"{prefix}_X_0"), "c1": const(f"{prefix}_X_1")},
            "y": {"c0": const(f"{prefix}_Y_0"), "c1": const(f"{prefix}_Y_1")},
        }

    spec = {
        "schema": "dregg-groth16-vk/1",
        "curve": "bn254",
        "description": (
            "Canonical VK + proof-format spec for the dregg 25-lane whole-history "
            "settlement Groth16 (BN254, gnark, commit-based range checker). THE ONE "
            "SOURCE the EVM/Solana/Cosmos verifiers are generated from."
        ),
        "source": {
            "gnark": "chain/gnark/settlement_snark_test.go (ExportSolidity, dev ceremony)",
            "solidity": "chain/contracts/DreggGroth16Verifier25.sol",
            "vk_hash_domain": "dregg-settlement-vk-dev-setup",
        },
        "deployment": {
            "network": "base-sepolia",
            "address": "0x7FBe1D2505644e1e4D50a1B5Cf08d0AcbF60C7cD",
        },
        "format": {
            "num_public_inputs": NUM_PUBLIC_INPUTS,
            "num_ic_bases": NUM_IC,
            "scalar_field_r": str(BN254_R),
            "g2_stored_negated": ["beta", "gamma", "delta"],
            "g2_coord_order": "eip197: (x.c1, x.c0, y.c1, y.c0) on the wire; stored here as c0,c1",
            "commitment": {
                "count": 1,
                "fold": "h = keccak256(be32(C.x) || be32(C.y)) mod r",
                "pok_pairing": "e(C, GSigma) . e(pok, G) == 1",
            },
            "public_input_msm": (
                "L = IC0 + C + sum_{i<25} input_i * IC[i] + h * IC[25]"
            ),
            "groth16_pairing": (
                "e(A, B) . e(C, -delta) . e(alpha, -beta) . e(L, -gamma) == 1"
            ),
            "lane_order": {
                "genesis_root": [0, 8],
                "final_root": [8, 16],
                "num_turns": 16,
                "chain_digest": [17, 25],
            },
        },
        "vk": {
            "alpha_g1": g1("ALPHA_X", "ALPHA_Y"),
            "beta_neg_g2": g2("BETA_NEG"),
            "gamma_neg_g2": g2("GAMMA_NEG"),
            "delta_neg_g2": g2("DELTA_NEG"),
            "pedersen_g_g2": g2("PEDERSEN_G"),
            "pedersen_gsigma_g2": g2("PEDERSEN_GSIGMA"),
            "ic0_g1": g1("CONSTANT_X", "CONSTANT_Y"),
            "ic_g1": [g1(f"PUB_{i}_X", f"PUB_{i}_Y") for i in range(NUM_IC)],
        },
    }

    out_path.write_text(json.dumps(spec, indent=2) + "\n")
    print(f"extract: wrote {out_path} ({out_path.stat().st_size} bytes)")


if __name__ == "__main__":
    main()
