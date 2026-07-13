#!/usr/bin/env python3
"""Generate solana-settlement/src/vk.rs from chain/contracts/DreggGroth16Verifier25.sol.

This is the EVM -> Solana VK conversion. The proof is chain-agnostic BN254; only the
on-chain verifier differs. We lift the gnark-embedded VK constants verbatim from the
Solidity verifier and re-encode them in the byte layout the Solana `alt_bn128` syscalls
(and their host ark-bn254 twin) expect:

  * G1 point  -> 64 bytes: X(32 be) || Y(32 be)
  * G2 point  -> 128 bytes EIP-197 order: X_c1 || X_c0 || Y_c1 || Y_c0   (imaginary first)

The Solidity verifier already stores BETA/GAMMA/DELTA *negated* (BETA_NEG_...), matching
the pairing equation e(A,B)e(C,-d)e(a,-b)e(L,-g)==1, and orders its G2 pairing words as
X_1,X_0,Y_1,Y_0 -- which is exactly EIP-197 -- so we lift them directly.
"""
import re, sys, pathlib

SOL = pathlib.Path(sys.argv[1])
OUT = pathlib.Path(sys.argv[2])
text = SOL.read_text()

def const(name):
    m = re.search(rf'uint256 constant {name} = (\d+);', text)
    if not m:
        raise SystemExit(f"missing constant {name}")
    return int(m.group(1))

def be32(x):
    return x.to_bytes(32, 'big')

def g1(name_x, name_y):
    return be32(const(name_x)) + be32(const(name_y))

# G2 in EIP-197 order X_1||X_0||Y_1||Y_0 from the _0/_1 sol constants.
def g2(prefix):
    return (be32(const(f'{prefix}_X_1')) + be32(const(f'{prefix}_X_0'))
            + be32(const(f'{prefix}_Y_1')) + be32(const(f'{prefix}_Y_0')))

def rust_bytes(b):
    return "[" + ", ".join(f"0x{x:02x}" for x in b) + "]"

alpha = g1('ALPHA_X', 'ALPHA_Y')
beta_neg = g2('BETA_NEG')
gamma_neg = g2('GAMMA_NEG')
delta_neg = g2('DELTA_NEG')
constant = g1('CONSTANT_X', 'CONSTANT_Y')
pub = [g1(f'PUB_{i}_X', f'PUB_{i}_Y') for i in range(26)]  # PUB_0..PUB_25
ped_g = g2('PEDERSEN_G')
ped_gsigma = g2('PEDERSEN_GSIGMA')

lines = []
lines.append("//! BN254 Groth16 verifying key for the dregg 25-lane settlement proof.")
lines.append("//!")
lines.append("//! GENERATED from `chain/contracts/DreggGroth16Verifier25.sol` by")
lines.append("//! `scripts/gen_vk.py` -- the SAME gnark VK the live EVM DreggGroth16Verifier25")
lines.append("//! embeds (Base-Sepolia 0x7FBe1D2505644e1e4D50a1B5Cf08d0AcbF60C7cD). The proof is")
lines.append("//! chain-agnostic BN254; only the on-chain verifier differs. Points are re-encoded")
lines.append("//! for the Solana `alt_bn128` syscalls: G1 = X||Y (64 be), G2 = X_c1||X_c0||Y_c1||Y_c0")
lines.append("//! (128, EIP-197 imaginary-first). BETA/GAMMA/DELTA are the pre-negated key points")
lines.append("//! (pairing eq e(A,B)e(C,-D)e(A,-B)e(L,-G)==1), lifted verbatim from the .sol.")
lines.append("//!")
lines.append("//! DO NOT EDIT BY HAND -- regenerate with `python3 scripts/gen_vk.py`.")
lines.append("")
lines.append("/// Number of settlement public inputs (the pinned 25-lane statement).")
lines.append("pub const NUM_PUBLIC_INPUTS: usize = 25;")
lines.append("")
lines.append("/// Groth16 alpha in G1 (64 bytes).")
lines.append(f"pub const ALPHA_G1: [u8; 64] = {rust_bytes(alpha)};")
lines.append("")
lines.append("/// Groth16 -beta in G2 (128 bytes, EIP-197).")
lines.append(f"pub const BETA_NEG_G2: [u8; 128] = {rust_bytes(beta_neg)};")
lines.append("")
lines.append("/// Groth16 -gamma in G2 (128 bytes, EIP-197).")
lines.append(f"pub const GAMMA_NEG_G2: [u8; 128] = {rust_bytes(gamma_neg)};")
lines.append("")
lines.append("/// Groth16 -delta in G2 (128 bytes, EIP-197).")
lines.append(f"pub const DELTA_NEG_G2: [u8; 128] = {rust_bytes(delta_neg)};")
lines.append("")
lines.append("/// Constant term (IC[0]) of the public-input MSM, G1 (64 bytes).")
lines.append(f"pub const CONSTANT_G1: [u8; 64] = {rust_bytes(constant)};")
lines.append("")
lines.append("/// Public-input bases PUB_0..=PUB_25 (26 G1 points). PUB_0..=PUB_24 pair with the")
lines.append("/// 25 statement lanes; PUB_25 pairs with the gnark commitment-hash input.")
lines.append("pub const PUB: [[u8; 64]; 26] = [")
for p in pub:
    lines.append(f"    {rust_bytes(p)},")
lines.append("];")
lines.append("")
lines.append("/// Pedersen commitment key G in G2 (128 bytes, EIP-197).")
lines.append(f"pub const PEDERSEN_G_G2: [u8; 128] = {rust_bytes(ped_g)};")
lines.append("")
lines.append("/// Pedersen commitment key GSigma in G2 (128 bytes, EIP-197).")
lines.append(f"pub const PEDERSEN_GSIGMA_G2: [u8; 128] = {rust_bytes(ped_gsigma)};")
lines.append("")

OUT.write_text("\n".join(lines) + "\n")
print(f"wrote {OUT} ({OUT.stat().st_size} bytes)")
