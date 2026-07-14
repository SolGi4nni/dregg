#!/usr/bin/env python3
"""Generate the EVM / Solana / Cosmos dregg-settlement VK encodings from ONE spec.

THE CODEGEN. Reads the single canonical spec `chain/codegen/dregg_vk.json` (the
gnark VK + the proof-format params, produced by `extract_vk_spec.py`) and emits the
verifying key in each chain's native encoding, so the three on-chain verifiers CANNOT
drift: a VK/format change is one edit to the spec + one `gen_verifiers.py` run.

Emits:
  * solana-settlement/src/vk.rs        Solana alt_bn128 byte layout
                                         G1 = X||Y (64 be); G2 = X_c1||X_c0||Y_c1||Y_c0
                                         (128, EIP-197); beta/gamma/delta pre-negated.
  * cosmos-settlement/src/vk.rs        arkworks BN254 decimal-string layout
                                         G1 = (x,y); G2 = ((x.c0,x.c1),(y.c0,y.c1)).
  * chain/codegen/out/DreggGroth16Verifier25.vk.sol
                                         the Solidity VK constant block (gnark order) —
                                         diff against DreggGroth16Verifier25.sol to
                                         catch EVM drift; also the injection body for
                                         the upgradeable-VK path.
  * chain/codegen/out/dregg_vk.evm.json
                                         the VK as the EVM injection vector (uint256
                                         words in gnark order) for an upgradeable
                                         setVerifyingKey(...) transaction.

The per-chain PAIRING BODY stays hand-written in each chain's crypto lib (EIP-197
precompiles / solana_bn254 syscalls / arkworks) — that logic is stable. What this
unifies is the drift-prone part: the VK constants + the format params, from one source.

  Usage:  python3 chain/codegen/gen_verifiers.py [chain/codegen/dregg_vk.json] [--check]

  --check  regenerate into temp files and diff against the committed outputs; exit 1
           on any difference (no files written). Used by the consistency gate.
"""
import json
import pathlib
import subprocess
import sys
import tempfile

REPO = pathlib.Path(__file__).resolve().parents[2]


def be32(dec: str) -> bytes:
    return int(dec).to_bytes(32, "big")


def g1_bytes(p: dict) -> bytes:
    """Solana G1: X(32 be) || Y(32 be)."""
    return be32(p["x"]) + be32(p["y"])


def g2_bytes_eip197(p: dict) -> bytes:
    """Solana/EIP-197 G2: X_c1 || X_c0 || Y_c1 || Y_c0 (imaginary first)."""
    return (
        be32(p["x"]["c1"]) + be32(p["x"]["c0"]) + be32(p["y"]["c1"]) + be32(p["y"]["c0"])
    )


def rust_byte_literal(b: bytes) -> str:
    return "[" + ", ".join(f"0x{x:02x}" for x in b) + "]"


# --- (a) Solana vk.rs --------------------------------------------------------

def emit_solana(spec: dict) -> str:
    vk = spec["vk"]
    L = []
    L.append("//! BN254 Groth16 verifying key for the dregg 25-lane settlement proof.")
    L.append("//!")
    L.append("//! GENERATED from the canonical spec `chain/codegen/dregg_vk.json` by")
    L.append("//! `chain/codegen/gen_verifiers.py` -- the ONE source the EVM/Solana/Cosmos")
    L.append("//! verifiers are all generated from (the SAME gnark VK the live EVM")
    L.append("//! DreggGroth16Verifier25 embeds, Base-Sepolia")
    L.append("//! 0x7FBe1D2505644e1e4D50a1B5Cf08d0AcbF60C7cD). The proof is chain-agnostic")
    L.append("//! BN254; only the on-chain verifier differs. Points are re-encoded for the")
    L.append("//! Solana `alt_bn128` syscalls: G1 = X||Y (64 be), G2 = X_c1||X_c0||Y_c1||Y_c0")
    L.append("//! (128, EIP-197 imaginary-first). BETA/GAMMA/DELTA are the pre-negated key")
    L.append("//! points (pairing eq e(A,B)e(C,-D)e(A,-B)e(L,-G)==1).")
    L.append("//!")
    L.append("//! DO NOT EDIT BY HAND -- regenerate with")
    L.append("//! `python3 chain/codegen/gen_verifiers.py`.")
    L.append("")
    L.append("/// Number of settlement public inputs (the pinned 25-lane statement).")
    L.append(f"pub const NUM_PUBLIC_INPUTS: usize = {spec['format']['num_public_inputs']};")
    L.append("")
    L.append("/// Groth16 alpha in G1 (64 bytes).")
    L.append(f"pub const ALPHA_G1: [u8; 64] = {rust_byte_literal(g1_bytes(vk['alpha_g1']))};")
    L.append("")
    L.append("/// Groth16 -beta in G2 (128 bytes, EIP-197).")
    L.append(f"pub const BETA_NEG_G2: [u8; 128] = {rust_byte_literal(g2_bytes_eip197(vk['beta_neg_g2']))};")
    L.append("")
    L.append("/// Groth16 -gamma in G2 (128 bytes, EIP-197).")
    L.append(f"pub const GAMMA_NEG_G2: [u8; 128] = {rust_byte_literal(g2_bytes_eip197(vk['gamma_neg_g2']))};")
    L.append("")
    L.append("/// Groth16 -delta in G2 (128 bytes, EIP-197).")
    L.append(f"pub const DELTA_NEG_G2: [u8; 128] = {rust_byte_literal(g2_bytes_eip197(vk['delta_neg_g2']))};")
    L.append("")
    L.append("/// Constant term (IC[0]) of the public-input MSM, G1 (64 bytes).")
    L.append(f"pub const CONSTANT_G1: [u8; 64] = {rust_byte_literal(g1_bytes(vk['ic0_g1']))};")
    L.append("")
    L.append("/// Public-input bases PUB_0..=PUB_25 (26 G1 points). PUB_0..=PUB_24 pair with the")
    L.append("/// 25 statement lanes; PUB_25 pairs with the gnark commitment-hash input.")
    n = len(vk["ic_g1"])
    L.append(f"pub const PUB: [[u8; 64]; {n}] = [")
    for p in vk["ic_g1"]:
        L.append(f"    {rust_byte_literal(g1_bytes(p))},")
    L.append("];")
    L.append("")
    L.append("/// Pedersen commitment key G in G2 (128 bytes, EIP-197).")
    L.append(f"pub const PEDERSEN_G_G2: [u8; 128] = {rust_byte_literal(g2_bytes_eip197(vk['pedersen_g_g2']))};")
    L.append("")
    L.append("/// Pedersen commitment key GSigma in G2 (128 bytes, EIP-197).")
    L.append(f"pub const PEDERSEN_GSIGMA_G2: [u8; 128] = {rust_byte_literal(g2_bytes_eip197(vk['pedersen_gsigma_g2']))};")
    L.append("")
    return "\n".join(L) + "\n"


# --- (b) Cosmos vk.rs --------------------------------------------------------

def g1_str(p: dict) -> str:
    return f'(\n    "{p["x"]}",\n    "{p["y"]}",\n)'


def g2_str(p: dict) -> str:
    return (
        "(\n"
        f'    ("{p["x"]["c0"]}", "{p["x"]["c1"]}"),\n'
        f'    ("{p["y"]["c0"]}", "{p["y"]["c1"]}"),\n'
        ")"
    )


def emit_cosmos(spec: dict) -> str:
    vk = spec["vk"]
    L = []
    L.append("//! Verification key constants for the dregg settlement Groth16 circuit (25 lanes).")
    L.append("//!")
    L.append("//! GENERATED -- do not hand-edit. Emitted from the canonical spec")
    L.append("//! `chain/codegen/dregg_vk.json` by `chain/codegen/gen_verifiers.py` -- the ONE")
    L.append("//! source the EVM/Solana/Cosmos verifiers are all generated from (the SAME gnark")
    L.append("//! VK the EVM `DreggGroth16Verifier25` bakes in). The G2 points are stored")
    L.append("//! PRE-NEGATED (BETA_NEG/GAMMA_NEG/DELTA_NEG), so the pairing product is checked")
    L.append("//! == 1 in GT, mirroring the EIP-197 precompile call. Coordinate order matches")
    L.append("//! Solidity: G2 stores (x.c0, x.c1, y.c0, y.c1).")
    L.append("//!")
    L.append("//! Regenerate with `python3 chain/codegen/gen_verifiers.py`.")
    L.append("")
    L.append("/// A G1 point as decimal strings (x, y) in Fq.")
    L.append("pub type G1Str = (&'static str, &'static str);")
    L.append("/// A G2 point as ((x.c0, x.c1), (y.c0, y.c1)) decimal strings in Fq2.")
    L.append("pub type G2Str = ((&'static str, &'static str), (&'static str, &'static str));")
    L.append("")
    L.append(f"pub const ALPHA_G1: G1Str = {g1_str(vk['alpha_g1'])};")
    L.append(f"pub const BETA_NEG_G2: G2Str = {g2_str(vk['beta_neg_g2'])};")
    L.append(f"pub const GAMMA_NEG_G2: G2Str = {g2_str(vk['gamma_neg_g2'])};")
    L.append(f"pub const DELTA_NEG_G2: G2Str = {g2_str(vk['delta_neg_g2'])};")
    L.append(f"pub const PEDERSEN_G_G2: G2Str = {g2_str(vk['pedersen_g_g2'])};")
    L.append(f"pub const PEDERSEN_GSIGMA_G2: G2Str = {g2_str(vk['pedersen_gsigma_g2'])};")
    L.append(f"pub const CONSTANT_G1: G1Str = {g1_str(vk['ic0_g1'])};")
    L.append("")
    L.append("/// K[0] (constant) is CONSTANT_G1; PUB_G1[i] is the IC point for public input i")
    L.append("/// (i in 0..25) plus PUB_G1[25] which multiplies the folded commitment hash.")
    n = len(vk["ic_g1"])
    L.append(f"pub const PUB_G1: [G1Str; {n}] = [")
    for p in vk["ic_g1"]:
        L.append(f"    {g1_str(p)},")
    L.append("];")
    L.append("")
    return "\n".join(L) + "\n"


# --- (c) EVM Solidity VK constant block + (d) injection JSON ------------------

def emit_evm_sol(spec: dict) -> str:
    vk = spec["vk"]
    L = []
    L.append("// SPDX-License-Identifier: MIT")
    L.append("// GENERATED VK constant block -- chain/codegen/gen_verifiers.py from")
    L.append("// chain/codegen/dregg_vk.json. This is the verifying-key half of the gnark")
    L.append("// DreggGroth16Verifier25.sol. Diff it against that contract to detect EVM VK")
    L.append("// drift; use it as the injection body for an upgradeable-VK verifier.")
    L.append("pragma solidity ^0.8.0;")
    L.append("")
    L.append("library DreggSettlementVK {")

    def c(name, dec):
        L.append(f"    uint256 constant {name} = {dec};")

    a = vk["alpha_g1"]
    c("ALPHA_X", a["x"]); c("ALPHA_Y", a["y"])
    for nm, key in (("BETA_NEG", "beta_neg_g2"), ("GAMMA_NEG", "gamma_neg_g2"),
                    ("DELTA_NEG", "delta_neg_g2"), ("PEDERSEN_G", "pedersen_g_g2"),
                    ("PEDERSEN_GSIGMA", "pedersen_gsigma_g2")):
        p = vk[key]
        c(f"{nm}_X_0", p["x"]["c0"]); c(f"{nm}_X_1", p["x"]["c1"])
        c(f"{nm}_Y_0", p["y"]["c0"]); c(f"{nm}_Y_1", p["y"]["c1"])
    ic0 = vk["ic0_g1"]
    c("CONSTANT_X", ic0["x"]); c("CONSTANT_Y", ic0["y"])
    for i, p in enumerate(vk["ic_g1"]):
        c(f"PUB_{i}_X", p["x"]); c(f"PUB_{i}_Y", p["y"])
    L.append("}")
    L.append("")
    return "\n".join(L)


def emit_evm_json(spec: dict) -> str:
    """The VK as the EVM injection vector (uint256 words, gnark order) for an
    upgradeable setVerifyingKey(...) transaction, plus the format params."""
    vk = spec["vk"]
    words = []
    a = vk["alpha_g1"]
    words += [a["x"], a["y"]]
    for key in ("beta_neg_g2", "gamma_neg_g2", "delta_neg_g2", "pedersen_g_g2", "pedersen_gsigma_g2"):
        p = vk[key]
        words += [p["x"]["c0"], p["x"]["c1"], p["y"]["c0"], p["y"]["c1"]]
    ic0 = vk["ic0_g1"]
    words += [ic0["x"], ic0["y"]]
    for p in vk["ic_g1"]:
        words += [p["x"], p["y"]]
    payload = {
        "schema": "dregg-groth16-vk-evm-injection/1",
        "curve": "bn254",
        "note": "uint256 words in gnark ExportSolidity order: alpha(2) | beta_neg,gamma_neg,delta_neg,pedersen_g,pedersen_gsigma (4 each) | constant(2) | pub_0..pub_25(2 each). Feed to an upgradeable setVerifyingKey; the on-chain contract recomputes the VK commitment.",
        "num_public_inputs": spec["format"]["num_public_inputs"],
        "vk_hash_domain": spec["source"]["vk_hash_domain"],
        "word_count": len(words),
        "words": words,
    }
    return json.dumps(payload, indent=2) + "\n"


# --- driver ------------------------------------------------------------------

def rustfmt(text: str) -> str:
    with tempfile.NamedTemporaryFile("w", suffix=".rs", delete=False) as f:
        f.write(text)
        tmp = f.name
    try:
        subprocess.run(["rustfmt", "--edition", "2021", tmp], check=True,
                       capture_output=True)
        return pathlib.Path(tmp).read_text()
    finally:
        pathlib.Path(tmp).unlink(missing_ok=True)


def targets(spec: dict) -> dict:
    return {
        REPO / "solana-settlement/src/vk.rs": rustfmt(emit_solana(spec)),
        REPO / "cosmos-settlement/src/vk.rs": rustfmt(emit_cosmos(spec)),
        REPO / "chain/codegen/out/DreggGroth16Verifier25.vk.sol": emit_evm_sol(spec),
        REPO / "chain/codegen/out/dregg_vk.evm.json": emit_evm_json(spec),
    }


def main() -> None:
    args = [a for a in sys.argv[1:] if a != "--check"]
    check = "--check" in sys.argv[1:]
    spec_path = pathlib.Path(args[0]) if args else REPO / "chain/codegen/dregg_vk.json"
    spec = json.loads(spec_path.read_text())

    outs = targets(spec)
    if check:
        drift = []
        for path, content in outs.items():
            existing = path.read_text() if path.exists() else None
            if existing != content:
                drift.append(path)
        if drift:
            print("gen_verifiers --check: DRIFT in:")
            for p in drift:
                print(f"  {p.relative_to(REPO)}")
            sys.exit(1)
        print(f"gen_verifiers --check: OK -- all {len(outs)} targets match the spec.")
        return

    for path, content in outs.items():
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)
        print(f"wrote {path.relative_to(REPO)} ({len(content)} bytes)")


if __name__ == "__main__":
    main()
