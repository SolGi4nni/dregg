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
  * chain/contracts/DreggSettlementVK.sol
                                         the Solidity VK constant block (gnark order) +
                                         `digest()`, which recomputes VK_DIGEST from
                                         those very constants on-chain. Diff the
                                         constants against DreggGroth16Verifier25.sol
                                         to catch EVM drift; also the injection body
                                         for the upgradeable-VK path.
  * chain/codegen/out/dregg_vk.evm.json
                                         the VK as the EVM injection vector (uint256
                                         words in gnark order) for an upgradeable
                                         setVerifyingKey(...) transaction.

THE VK DIGEST (`VK_DIGEST`). Every chain pins a "verifying-key commitment" so a key
swap is DETECTABLE on-chain. Until 2026-07-28 that pin was
`keccak256("dregg-settlement-vk-dev-setup")` — a hash of a LABEL, constant under every
possible regeneration of the key, i.e. the one artifact whose job is to notice a key
changed could not notice. It is now `vk_digest()` below: keccak256 over a
domain-tagged, canonical serialization of the ACTUAL key material, so any change to
any VK word moves it. Definition (`chain/codegen/dregg_vk.json` `schema` is the tag):

    VK_DIGEST = keccak256(
          ascii(schema)                 # "dregg-groth16-vk/1"
       || u32be(num_public_inputs)      # 25
       || u32be(num_ic_bases)           # 26
       || W[0] .. W[75]                 # 76 x 32-byte big-endian Fq coordinates
    )

    W = alpha.x, alpha.y,
        beta_neg  (x.c1, x.c0, y.c1, y.c0),   # EIP-197 imaginary-first, the wire order
        gamma_neg (x.c1, x.c0, y.c1, y.c0),
        delta_neg (x.c1, x.c0, y.c1, y.c0),
        pedersen_g(x.c1, x.c0, y.c1, y.c0),
        pedersen_gsigma(x.c1, x.c0, y.c1, y.c0),
        ic0.x, ic0.y,
        ic[0].x, ic[0].y, ... ic[25].x, ic[25].y

The negated G2 points are what each chain actually stores, and negation is a bijection,
so digesting the stored form binds the key exactly as tightly as digesting the original.
Solana recomputes this from its own `vk.rs` constants (`vk_digest::compute`), Solidity
from `DreggSettlementVK.digest()`; both are asserted equal to the emitted `VK_DIGEST`.

The per-chain PAIRING BODY stays hand-written in each chain's crypto lib (EIP-197
precompiles / solana_bn254 syscalls / arkworks) — that logic is stable. What this
unifies is the drift-prone part: the VK constants + the format params, from one source.

  Usage:  python3 chain/codegen/gen_verifiers.py [chain/codegen/dregg_vk.json] [--check]
          python3 chain/codegen/gen_verifiers.py [spec.json] --digest

  --check   regenerate into temp files and diff against the committed outputs; exit 1
            on any difference (no files written). Used by the consistency gate.
  --digest  print the VK_DIGEST for the given spec and exit. Writes NOTHING, so it is
            safe to point at a perturbed copy of the spec — which is how
            `chain/codegen/vk_pin_moves.sh` demonstrates that regenerating the key
            moves the pin.
"""
import json
import pathlib
import subprocess
import sys
import tempfile

REPO = pathlib.Path(__file__).resolve().parents[2]

# --- keccak256 -----------------------------------------------------------------
# Vendored, dependency-free Keccak-f[1600] / keccak256 (FIPS-202 permutation with
# the ORIGINAL 0x01 padding, i.e. Ethereum's keccak256, NOT hashlib's sha3_256,
# which pads 0x06 and produces a different digest). Codegen must not acquire a
# pip dependency, and `self_test_keccak()` checks it against published vectors on
# every run — `check_consistency.sh` additionally cross-checks it against
# `cast keccak`, so a wrong hash here cannot pass silently.

_KECCAK_RC = (
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
    0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
)
_KECCAK_ROT = (
    (0, 36, 3, 41, 18),
    (1, 44, 10, 45, 2),
    (62, 6, 43, 15, 61),
    (28, 55, 25, 21, 56),
    (27, 20, 39, 8, 14),
)
_M64 = (1 << 64) - 1


def _rol(v: int, n: int) -> int:
    return ((v << n) | (v >> (64 - n))) & _M64 if n else v


def _keccak_f1600(a):
    for rnd in range(24):
        # theta
        c = [a[x][0] ^ a[x][1] ^ a[x][2] ^ a[x][3] ^ a[x][4] for x in range(5)]
        d = [c[(x - 1) % 5] ^ _rol(c[(x + 1) % 5], 1) for x in range(5)]
        a = [[a[x][y] ^ d[x] for y in range(5)] for x in range(5)]
        # rho + pi
        b = [[0] * 5 for _ in range(5)]
        for x in range(5):
            for y in range(5):
                b[y][(2 * x + 3 * y) % 5] = _rol(a[x][y], _KECCAK_ROT[x][y])
        # chi
        a = [
            [b[x][y] ^ ((~b[(x + 1) % 5][y] & _M64) & b[(x + 2) % 5][y]) for y in range(5)]
            for x in range(5)
        ]
        # iota
        a[0][0] ^= _KECCAK_RC[rnd]
    return a


def keccak256(data: bytes) -> bytes:
    rate = 136  # 1088 bits, the keccak256 rate
    # Original Keccak padding: 0x01 ... 0x80 (Ethereum), not FIPS-202's 0x06.
    padded = bytearray(data)
    padded.append(0x01)
    while len(padded) % rate != 0:
        padded.append(0x00)
    padded[-1] |= 0x80

    a = [[0] * 5 for _ in range(5)]
    for off in range(0, len(padded), rate):
        block = padded[off:off + rate]
        for i in range(rate // 8):
            lane = int.from_bytes(block[i * 8:i * 8 + 8], "little")
            a[i % 5][i // 5] ^= lane
        a = _keccak_f1600(a)

    out = bytearray()
    for i in range(4):  # 4 lanes = 32 bytes
        out += a[i % 5][i // 5].to_bytes(8, "little")
    return bytes(out)


def self_test_keccak() -> None:
    """Published keccak256 vectors. Runs on every invocation — a broken hash here
    would silently mint a wrong pin on every chain at once."""
    # Every value below was taken from `cast keccak` (foundry 1.7.1) on 2026-07-28,
    # and covers both padding boundaries: 135 B (padding fits the block), 136 B
    # (exactly the rate, forcing a second permutation), 272 B (two full blocks).
    vectors = (
        (b"", "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"),
        (b"abc", "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"),
        (b"a" * 135, "34367dc248bbd832f4e3e69dfaac2f92638bd0bbd18f2912ba4ef454919cf446"),
        (b"a" * 136, "a6c4d403279fe3e0af03729caada8374b5ca54d8065329a3ebcaeb4b60aa386e"),
        (b"a" * 272, "cf7fcd4f705ee749930d19ca84561a9bf62516bd90a471545fa2f49fdc7e63c8"),
        (bytes(range(256)),
         "dc924469b334aed2a19fac7252e9961aea41f8d91996366029dbe0884229bf36"),
    )
    for msg, want in vectors:
        got = keccak256(msg).hex()
        if got != want:
            raise SystemExit(
                f"keccak256 self-test FAILED for {len(msg)}-byte input: "
                f"got {got}, want {want}"
            )


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


# --- the VK digest: the on-chain pin, a function OF THE KEY -------------------

# The G2 points, in the fixed order every emitter uses. One list so the Rust,
# Solidity and Python encodings cannot drift apart.
G2_ORDER = ("beta_neg_g2", "gamma_neg_g2", "delta_neg_g2",
            "pedersen_g_g2", "pedersen_gsigma_g2")


def vk_preimage(spec: dict) -> bytes:
    """The exact bytes hashed to produce VK_DIGEST (see the module docstring)."""
    vk = spec["vk"]
    fmt = spec["format"]
    n_ic = len(vk["ic_g1"])
    if fmt["num_ic_bases"] != n_ic:
        raise SystemExit(
            f"spec inconsistent: format.num_ic_bases={fmt['num_ic_bases']} but "
            f"len(vk.ic_g1)={n_ic}"
        )
    out = bytearray()
    out += spec["schema"].encode("ascii")
    out += int(fmt["num_public_inputs"]).to_bytes(4, "big")
    out += n_ic.to_bytes(4, "big")
    out += g1_bytes(vk["alpha_g1"])
    for key in G2_ORDER:
        out += g2_bytes_eip197(vk[key])
    out += g1_bytes(vk["ic0_g1"])
    for p in vk["ic_g1"]:
        out += g1_bytes(p)
    return bytes(out)


def vk_digest(spec: dict) -> bytes:
    return keccak256(vk_preimage(spec))


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
    L.append("/// THE VK COMMITMENT — keccak256 over the canonical serialization of the")
    L.append("/// verifying key ABOVE (see `chain/codegen/gen_verifiers.py`). Every chain pins")
    L.append("/// this value; `crate::vk_digest::compute()` recomputes it from these very")
    L.append("/// constants and `vk_digest::tests` asserts the two agree, so NO VK byte can")
    L.append("/// change without moving the pin.")
    L.append("///")
    L.append("/// It replaced `keccak256(\"dregg-settlement-vk-dev-setup\")` on 2026-07-28 — a")
    L.append("/// hash of a LABEL, which was byte-identical under every regeneration of the key.")
    L.append(f"pub const VK_DIGEST: [u8; 32] = {rust_byte_literal(vk_digest(spec))};")
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
    L.append("/// THE VK COMMITMENT — keccak256 over the canonical serialization of the")
    L.append("/// verifying key ABOVE, byte-identical to the Solana `vk::VK_DIGEST` and the")
    L.append("/// Solidity `DreggSettlementVK.VK_DIGEST` (all three are emitted from the one")
    L.append("/// spec `chain/codegen/dregg_vk.json`). Pinned at instantiate.")
    L.append("///")
    L.append("/// It replaced `keccak256(\"dregg-settlement-vk-dev-setup\")` on 2026-07-28 — a")
    L.append("/// hash of a LABEL, which was byte-identical under every regeneration of the key.")
    L.append(f"pub const VK_DIGEST: [u8; 32] = {rust_byte_literal(vk_digest(spec))};")
    L.append("")
    return "\n".join(L) + "\n"


# --- (c) EVM Solidity VK constant block + (d) injection JSON ------------------

EVM_G2_NAMES = (("BETA_NEG", "beta_neg_g2"), ("GAMMA_NEG", "gamma_neg_g2"),
                ("DELTA_NEG", "delta_neg_g2"), ("PEDERSEN_G", "pedersen_g_g2"),
                ("PEDERSEN_GSIGMA", "pedersen_gsigma_g2"))


def evm_digest_word_names(spec: dict) -> list:
    """The constant names, in the VK_DIGEST word order, so `digest()` hashes the
    SAME 76 words `vk_preimage` does."""
    names = ["ALPHA_X", "ALPHA_Y"]
    for nm, _key in EVM_G2_NAMES:
        # EIP-197 imaginary-first, matching g2_bytes_eip197.
        names += [f"{nm}_X_1", f"{nm}_X_0", f"{nm}_Y_1", f"{nm}_Y_0"]
    names += ["CONSTANT_X", "CONSTANT_Y"]
    for i in range(len(spec["vk"]["ic_g1"])):
        names += [f"PUB_{i}_X", f"PUB_{i}_Y"]
    return names


def emit_evm_sol(spec: dict) -> str:
    vk = spec["vk"]
    fmt = spec["format"]
    digest = vk_digest(spec)
    words = evm_digest_word_names(spec)
    L = []
    L.append("// SPDX-License-Identifier: MIT")
    L.append("// GENERATED -- chain/codegen/gen_verifiers.py from chain/codegen/dregg_vk.json.")
    L.append("// DO NOT EDIT BY HAND.")
    L.append("//")
    L.append("// The verifying-key half of the gnark DreggGroth16Verifier25.sol, plus the VK")
    L.append("// COMMITMENT the settlement stack pins. `check_consistency.sh` diffs these")
    L.append("// constants against the live gnark verifier to detect EVM VK drift, and this is")
    L.append("// also the injection body for an upgradeable-VK verifier.")
    L.append("//")
    L.append("// WHY digest() EXISTS. Until 2026-07-28 the on-chain VK pin was")
    L.append("// keccak256(\"dregg-settlement-vk-dev-setup\") -- a hash of a LABEL. It was")
    L.append("// byte-identical under every possible regeneration of the key, so the one")
    L.append("// artifact whose whole job is to notice a key changed could not notice.")
    L.append("// VK_DIGEST is keccak256 over the canonical serialization of the ACTUAL key")
    L.append("// constants below, and digest() recomputes it from them ON-CHAIN, so the pin")
    L.append("// is a FUNCTION OF THE KEY and moves whenever any VK word moves.")
    L.append("pragma solidity ^0.8.0;")
    L.append("")
    L.append("library DreggSettlementVK {")

    def c(name, dec):
        L.append(f"    uint256 constant {name} = {dec};")

    a = vk["alpha_g1"]
    c("ALPHA_X", a["x"]); c("ALPHA_Y", a["y"])
    for nm, key in EVM_G2_NAMES:
        p = vk[key]
        c(f"{nm}_X_0", p["x"]["c0"]); c(f"{nm}_X_1", p["x"]["c1"])
        c(f"{nm}_Y_0", p["y"]["c0"]); c(f"{nm}_Y_1", p["y"]["c1"])
    ic0 = vk["ic0_g1"]
    c("CONSTANT_X", ic0["x"]); c("CONSTANT_Y", ic0["y"])
    for i, p in enumerate(vk["ic_g1"]):
        c(f"PUB_{i}_X", p["x"]); c(f"PUB_{i}_Y", p["y"])
    L.append("")
    L.append("    // ─── The VK commitment ────────────────────────────────────────────────")
    L.append("")
    L.append("    /// Domain tag = the spec schema; a schema bump moves the pin too.")
    L.append(f'    string constant DIGEST_DOMAIN = "{spec["schema"]}";')
    L.append(f"    uint32 constant NUM_PUBLIC_INPUTS = {fmt['num_public_inputs']};")
    L.append(f"    uint32 constant NUM_IC_BASES = {len(vk['ic_g1'])};")
    L.append("")
    L.append("    /// keccak256 of the canonical VK serialization -- the value every chain")
    L.append("    /// pins (byte-identical to Solana `vk::VK_DIGEST` and Cosmos `vk::VK_DIGEST`).")
    L.append(f"    bytes32 constant VK_DIGEST =")
    L.append(f"        0x{digest.hex()};")
    L.append("")
    L.append(f"    /// The {len(words)} VK coordinates in the digest's pinned order:")
    L.append("    /// alpha(2) | beta_neg,gamma_neg,delta_neg,pedersen_g,pedersen_gsigma")
    L.append("    /// (4 each, EIP-197 imaginary-first) | ic0(2) | ic[i](2 each).")
    L.append(f"    function words() internal pure returns (uint256[] memory w) {{")
    L.append(f"        w = new uint256[]({len(words)});")
    for i, nm in enumerate(words):
        L.append(f"        w[{i}] = {nm};")
    L.append("    }")
    L.append("")
    L.append("    /// Recompute VK_DIGEST from the constants above. `digest() == VK_DIGEST` is")
    L.append("    /// the whole claim: the pin cannot stay still while the key moves.")
    L.append("    function digest() internal pure returns (bytes32) {")
    L.append("        return keccak256(")
    L.append("            abi.encodePacked(")
    L.append("                DIGEST_DOMAIN,")
    L.append("                NUM_PUBLIC_INPUTS,")
    L.append("                NUM_IC_BASES,")
    L.append("                abi.encodePacked(words())")
    L.append("            )")
    L.append("        );")
    L.append("    }")
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
        "num_ic_bases": len(vk["ic_g1"]),
        "vk_digest": "0x" + vk_digest(spec).hex(),
        "vk_digest_note": "keccak256 over the canonical VK serialization (see gen_verifiers.py). THE pin: a function of the key, not of a label. Byte-identical to DreggSettlementVK.VK_DIGEST, Solana vk::VK_DIGEST and Cosmos vk::VK_DIGEST.",
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
        # In contracts/, not codegen/out/, so forge COMPILES it: `digest()` has to
        # run on-chain for the pin to be checkable, and DreggSettlementVKPin.t.sol
        # asserts digest() == VK_DIGEST. (It lived in codegen/out/ until 2026-07-28,
        # where nothing could compile it.)
        REPO / "chain/contracts/DreggSettlementVK.sol": emit_evm_sol(spec),
        REPO / "chain/codegen/out/dregg_vk.evm.json": emit_evm_json(spec),
    }


def main() -> None:
    flags = {"--check", "--digest"}
    args = [a for a in sys.argv[1:] if a not in flags]
    check = "--check" in sys.argv[1:]
    digest_only = "--digest" in sys.argv[1:]
    spec_path = pathlib.Path(args[0]) if args else REPO / "chain/codegen/dregg_vk.json"
    spec = json.loads(spec_path.read_text())

    self_test_keccak()

    if digest_only:
        # Writes NOTHING: safe to point at a perturbed copy of the spec, which is
        # how vk_pin_moves.sh shows a regenerated key moves the pin.
        print("0x" + vk_digest(spec).hex())
        return

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
