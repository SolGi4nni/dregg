//! On-chain BN254 Groth16 verification of the dregg 25-lane settlement proof,
//! via the Solana `alt_bn128` syscalls (`solana_bn254::prelude`) -- the SAME
//! proof/VK the EVM `DreggGroth16Verifier25` checks with the EIP-196/197
//! pairing precompiles.
//!
//! This is a gnark Groth16 with a **Pedersen commitment** (the wrap circuit's
//! commit-based range checker): the proof carries an extra commitment G1 point
//! plus a proof-of-knowledge, and a 26th "public" input derived by hashing the
//! commitment. We mirror `DreggGroth16Verifier25.verifyProof` exactly:
//!
//!   1. Verify the Pedersen commitment PoK:
//!        e(commitment, GSigma) . e(pok, G) == 1                       (2-pair pairing)
//!   2. Derive the commitment-hash input:
//!        s = keccak256(commitment_x || commitment_y) mod R
//!   3. Public-input MSM (`publicInputMSM`):
//!        L = CONSTANT + commitment + sum_i input_i . PUB_i + s . PUB_25
//!   4. Groth16 pairing:
//!        e(A, B) . e(C, -delta) . e(alpha, -beta) . e(L, -gamma) == 1  (4-pair pairing)
//!
//! `solana_bn254::prelude` runs these on the real `sol_alt_bn128_*` syscalls
//! on-chain (`target_os = "solana"`) and on the identical ark-bn254 arithmetic
//! off-chain (host tests / `solana-program-test`) -- one code path, two backends.

use solana_bn254::prelude::{alt_bn128_addition, alt_bn128_multiplication, alt_bn128_pairing};
use solana_program::keccak;

use crate::vk;

/// BN254 scalar field order R (big-endian), from the EVM verifier's `R` constant.
/// The commitment-hash input and every public input must be a reduced Fr element.
pub const R_BE: [u8; 32] = [
    0x30, 0x64, 0x4e, 0x72, 0xe1, 0x31, 0xa0, 0x29, 0xb8, 0x50, 0x45, 0xb6, 0x81, 0x81, 0x58, 0x5d,
    0x28, 0x33, 0xe8, 0x48, 0x79, 0xb9, 0x70, 0x91, 0x43, 0xe1, 0xf5, 0x93, 0xf0, 0x00, 0x00, 0x01,
];

/// Why a Groth16 verification was rejected. Fail-closed: any arithmetic error, a
/// failed commitment PoK, or a failed pairing rejects the proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Groth16Error {
    /// A public input is not a reduced scalar-field element (`>= R`).
    PublicInputNotInField,
    /// An `alt_bn128` group operation failed (off-curve point / bad encoding).
    GroupOp,
    /// The Pedersen commitment proof-of-knowledge pairing did not equal one.
    CommitmentInvalid,
    /// The Groth16 pairing equation did not equal one.
    ProofInvalid,
}

/// A decoded Groth16 proof in the syscall byte layout (EIP-197 / big-endian).
pub struct Proof {
    /// A in G1 (64 bytes: X || Y).
    pub a: [u8; 64],
    /// B in G2 (128 bytes: X_c1 || X_c0 || Y_c1 || Y_c0).
    pub b: [u8; 128],
    /// C in G1 (64 bytes).
    pub c: [u8; 64],
    /// The Pedersen commitment in G1 (64 bytes).
    pub commitment: [u8; 64],
    /// The Pedersen commitment proof-of-knowledge in G1 (64 bytes).
    pub commitment_pok: [u8; 64],
}

/// A pairing check over `input` (a sequence of G1||G2 elements): true iff the
/// product of pairings equals one (the syscall returns big-endian `1`).
fn pairing_is_one(input: &[u8]) -> Result<bool, Groth16Error> {
    let out = alt_bn128_pairing(input).map_err(|_| Groth16Error::GroupOp)?;
    // 32-byte big-endian: 1 on success, 0 otherwise.
    Ok(out.len() == 32 && out[..31].iter().all(|&b| b == 0) && out[31] == 1)
}

/// EC add of two 64-byte G1 points -> 64-byte G1 point.
fn g1_add(p: &[u8; 64], q: &[u8; 64]) -> Result<[u8; 64], Groth16Error> {
    let mut input = [0u8; 128];
    input[..64].copy_from_slice(p);
    input[64..].copy_from_slice(q);
    let out = alt_bn128_addition(&input).map_err(|_| Groth16Error::GroupOp)?;
    to_g1(&out)
}

/// EC scalar-mul of a 64-byte G1 point by a 32-byte big-endian scalar -> G1.
fn g1_mul(p: &[u8; 64], scalar_be: &[u8; 32]) -> Result<[u8; 64], Groth16Error> {
    let mut input = [0u8; 96];
    input[..64].copy_from_slice(p);
    input[64..].copy_from_slice(scalar_be);
    let out = alt_bn128_multiplication(&input).map_err(|_| Groth16Error::GroupOp)?;
    to_g1(&out)
}

fn to_g1(bytes: &[u8]) -> Result<[u8; 64], Groth16Error> {
    if bytes.len() != 64 {
        return Err(Groth16Error::GroupOp);
    }
    let mut out = [0u8; 64];
    out.copy_from_slice(bytes);
    Ok(out)
}

/// `a < b` for 32-byte big-endian integers.
fn lt_be(a: &[u8; 32], b: &[u8; 32]) -> bool {
    for i in 0..32 {
        if a[i] != b[i] {
            return a[i] < b[i];
        }
    }
    false
}

/// `a -= R` in place (32-byte big-endian). Caller guarantees `a >= R`.
fn sub_r_in_place(a: &mut [u8; 32]) {
    let mut borrow = 0i16;
    for i in (0..32).rev() {
        let v = a[i] as i16 - R_BE[i] as i16 - borrow;
        if v < 0 {
            a[i] = (v + 256) as u8;
            borrow = 1;
        } else {
            a[i] = v as u8;
            borrow = 0;
        }
    }
}

/// Reduce a 256-bit big-endian value mod R. keccak output is < 2^256 and
/// 2^256 / R < 5, so at most a few subtractions of R (no bignum dependency).
fn reduce_mod_r(mut x: [u8; 32]) -> [u8; 32] {
    // 2^256 < 5*R, so <= 4 subtractions suffice; the loop is bounded regardless.
    for _ in 0..8 {
        if lt_be(&x, &R_BE) {
            break;
        }
        sub_r_in_place(&mut x);
    }
    x
}

/// The public-input MSM (`DreggGroth16Verifier25.publicInputMSM`):
///   L = CONSTANT + commitment + sum_{i<25} input_i . PUB_i + s . PUB_25
/// where `s` is the commitment-hash input. Every statement input is checked
/// `< R` (fail-closed parity with the EVM `lt(s, R)` guard).
fn public_input_msm(
    inputs: &[[u8; 32]; vk::NUM_PUBLIC_INPUTS],
    commitment_hash: &[u8; 32],
    commitment: &[u8; 64],
) -> Result<[u8; 64], Groth16Error> {
    let mut acc = vk::CONSTANT_G1;
    acc = g1_add(&acc, commitment)?;
    for (i, input) in inputs.iter().enumerate() {
        if !lt_be(input, &R_BE) {
            return Err(Groth16Error::PublicInputNotInField);
        }
        let term = g1_mul(&vk::PUB[i], input)?;
        acc = g1_add(&acc, &term)?;
    }
    // The 26th base pairs with the commitment-hash input (already reduced < R).
    let term = g1_mul(&vk::PUB[25], commitment_hash)?;
    acc = g1_add(&acc, &term)?;
    Ok(acc)
}

/// Verify the dregg settlement Groth16 proof against the pinned VK.
///
/// Returns `Ok(())` iff the Pedersen commitment PoK AND the Groth16 pairing both
/// hold for the given 25-lane statement -- i.e. the SAME acceptance condition as
/// the on-chain EVM `DreggGroth16Verifier25.verifyProof`.
pub fn verify(
    proof: &Proof,
    inputs: &[[u8; 32]; vk::NUM_PUBLIC_INPUTS],
) -> Result<(), Groth16Error> {
    // (1) Pedersen commitment proof-of-knowledge:
    //     e(commitment, GSigma) . e(pok, G) == 1
    let mut ck = [0u8; 2 * 192];
    ck[0..64].copy_from_slice(&proof.commitment);
    ck[64..192].copy_from_slice(&vk::PEDERSEN_GSIGMA_G2);
    ck[192..256].copy_from_slice(&proof.commitment_pok);
    ck[256..384].copy_from_slice(&vk::PEDERSEN_G_G2);
    if !pairing_is_one(&ck)? {
        return Err(Groth16Error::CommitmentInvalid);
    }

    // (2) commitment-hash input: keccak256(commitment_x || commitment_y) mod R.
    let h = keccak::hashv(&[&proof.commitment]);
    let commitment_hash = reduce_mod_r(h.0);

    // (3) public-input MSM.
    let l_pub = public_input_msm(inputs, &commitment_hash, &proof.commitment)?;

    // (4) Groth16 pairing:
    //     e(A, B) . e(C, -delta) . e(alpha, -beta) . e(L, -gamma) == 1
    let mut pin = [0u8; 4 * 192];
    // e(A, B)
    pin[0..64].copy_from_slice(&proof.a);
    pin[64..192].copy_from_slice(&proof.b);
    // e(C, -delta)
    pin[192..256].copy_from_slice(&proof.c);
    pin[256..384].copy_from_slice(&vk::DELTA_NEG_G2);
    // e(alpha, -beta)
    pin[384..448].copy_from_slice(&vk::ALPHA_G1);
    pin[448..576].copy_from_slice(&vk::BETA_NEG_G2);
    // e(L, -gamma)
    pin[576..640].copy_from_slice(&l_pub);
    pin[640..768].copy_from_slice(&vk::GAMMA_NEG_G2);
    if !pairing_is_one(&pin)? {
        return Err(Groth16Error::ProofInvalid);
    }
    Ok(())
}
