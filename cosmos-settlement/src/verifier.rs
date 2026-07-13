//! A real BN254 Groth16 verifier (with the gnark Pedersen-commitment gate),
//! implemented with arkworks — the Cosmos-runtime twin of the gnark-generated
//! EVM verifier `chain/contracts/DreggGroth16Verifier25.sol`.
//!
//! This verifies the SAME proof the EVM verifier verifies (same VK, same 25-lane
//! statement, same fixture `chain/test/fixtures/settlement_groth16.json`). It is a
//! faithful re-expression in Rust of the two precompile pairing checks the Solidity
//! contract performs, so a dregg settlement proof is checked natively inside a
//! CosmWasm contract (Rust/wasm) rather than by an EVM precompile.
//!
//! Two checks, both mirroring the Solidity `verifyProof`:
//!   1. Pedersen commitment:  e(C, Gσ) · e(pok, G) == 1_GT
//!   2. Groth16 pairing:      e(A, B) · e(C, -δ) · e(α, -β) · e(L, -γ) == 1_GT
//!      where  L = K0 + commitment + Σ_{i<25} input[i]·IC[i] + h·IC[25]
//!      and    h = keccak256( be32(C.x) ‖ be32(C.y) ) mod r   (the commitment fold).
//!
//! Groth16 soundness for this circuit rests on a SINGLE-PARTY dev trusted setup
//! (the same ceremony as the EVM verifier) — real circuit, real verifier, dev
//! ceremony; not a production MPC ceremony. See the module docs in `lib.rs`.

use core::str::FromStr;

use ark_bn254::{Bn254, Fq, Fq2, Fr, G1Affine, G2Affine};
use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInteger, PrimeField};
use ark_std::Zero;
use sha3::{Digest, Keccak256};

use crate::vk;

/// The pinned public-statement width: 25 BabyBear lanes.
pub const NUM_LANES: usize = 25;

/// Why a proof was rejected. Every arm is a genuine cryptographic reject — no
/// arm is ever returned for a valid proof over the pinned statement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum VerifyError {
    /// A supplied curve point (proof A/B/C, commitment, or pok) is malformed:
    /// a coordinate is not a field element, the point is not on the curve, or
    /// it is not in the prime-order subgroup.
    BadPoint(&'static str),
    /// A public input lane is not a canonical field element.
    BadInput,
    /// The Pedersen-commitment pairing check failed (check 1).
    CommitmentInvalid,
    /// The Groth16 pairing equation failed (check 2).
    ProofInvalid,
}

impl core::fmt::Display for VerifyError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            VerifyError::BadPoint(w) => write!(f, "malformed curve point: {w}"),
            VerifyError::BadInput => write!(f, "non-canonical public input"),
            VerifyError::CommitmentInvalid => write!(f, "pedersen commitment check failed"),
            VerifyError::ProofInvalid => write!(f, "groth16 pairing check failed"),
        }
    }
}

/// The proof, as the fixture / calldata carries it: decimal strings for the
/// curve coordinates (BN254 base-field integers) and the 25 public lanes.
///
/// Layout mirrors `chain/test/fixtures/settlement_groth16.json`:
///   proof         = [A.x, A.y, B.x.c1, B.x.c0, B.y.c1, B.y.c0, C.x, C.y]
///   commitments   = [Cm.x, Cm.y]        (exactly ONE Pedersen commitment)
///   commitment_pok= [Pok.x, Pok.y]
pub struct RawProof<'a> {
    pub proof: [&'a str; 8],
    pub commitments: [&'a str; 2],
    pub commitment_pok: [&'a str; 2],
}

/// Parse a base-field coordinate given as either a `0x`-prefixed big-endian hex
/// string (the fixture / calldata form) or a decimal string. Hex is the native
/// encoding of `chain/test/fixtures/settlement_groth16.json`.
fn fq(s: &str) -> Result<Fq, VerifyError> {
    if let Some(h) = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")) {
        let padded = if h.len() % 2 == 1 {
            let mut p = String::with_capacity(h.len() + 1);
            p.push('0');
            p.push_str(h);
            p
        } else {
            h.to_string()
        };
        let bytes = hex::decode(padded).map_err(|_| VerifyError::BadPoint("bad hex coordinate"))?;
        Ok(Fq::from_be_bytes_mod_order(&bytes))
    } else {
        Fq::from_str(s).map_err(|_| VerifyError::BadPoint("coordinate not in Fq"))
    }
}

/// A G1 point supplied in the proof: parsed, then checked on-curve AND in the
/// prime-order subgroup (BN254 G1 is prime-order so the subgroup check is
/// implied by on-curve, but we assert it explicitly for defence in depth).
fn g1_checked(x: &str, y: &str, what: &'static str) -> Result<G1Affine, VerifyError> {
    let p = G1Affine::new_unchecked(fq(x)?, fq(y)?);
    if !p.is_on_curve() || !p.is_in_correct_subgroup_assuming_on_curve() {
        return Err(VerifyError::BadPoint(what));
    }
    Ok(p)
}

/// A G2 point supplied in the proof (only B). Fq2 order matches the EIP-197 /
/// Solidity encoding: the two coordinates are (c1, c0) = (imaginary, real).
fn g2_checked_c1c0(
    x_c1: &str,
    x_c0: &str,
    y_c1: &str,
    y_c0: &str,
    what: &'static str,
) -> Result<G2Affine, VerifyError> {
    let x = Fq2::new(fq(x_c0)?, fq(x_c1)?);
    let y = Fq2::new(fq(y_c0)?, fq(y_c1)?);
    let p = G2Affine::new_unchecked(x, y);
    if !p.is_on_curve() || !p.is_in_correct_subgroup_assuming_on_curve() {
        return Err(VerifyError::BadPoint(what));
    }
    Ok(p)
}

/// A trusted VK G1 point (decimal strings, on-curve by construction).
fn vk_g1(p: vk::G1Str) -> G1Affine {
    G1Affine::new_unchecked(
        Fq::from_str(p.0).expect("vk Fq"),
        Fq::from_str(p.1).expect("vk Fq"),
    )
}

/// A trusted VK G2 point stored as ((x.c0, x.c1), (y.c0, y.c1)) decimal strings.
fn vk_g2(p: vk::G2Str) -> G2Affine {
    let x = Fq2::new(
        Fq::from_str(p.0 .0).expect("vk Fq"),
        Fq::from_str(p.0 .1).expect("vk Fq"),
    );
    let y = Fq2::new(
        Fq::from_str(p.1 .0).expect("vk Fq"),
        Fq::from_str(p.1 .1).expect("vk Fq"),
    );
    G2Affine::new_unchecked(x, y)
}

/// 32-byte big-endian encoding of an Fq element (matches `abi.encodePacked(uint256)`).
fn fq_be32(v: &Fq) -> [u8; 32] {
    let bytes = v.into_bigint().to_bytes_be();
    // BN254 Fq is 4 limbs => to_bytes_be yields exactly 32 bytes.
    let mut out = [0u8; 32];
    let n = bytes.len().min(32);
    out[32 - n..].copy_from_slice(&bytes[bytes.len() - n..]);
    out
}

/// The gnark commitment fold, exactly as the Solidity verifier computes it:
///   publicCommitments[0] = uint256(keccak256(be32(C.x) ‖ be32(C.y))) mod r
/// (the `publicAndCommitmentCommitted` tail is empty for this circuit).
fn commitment_fold(commitment: &G1Affine) -> Fr {
    // Affine coordinates (the commitment is checked on-curve + in-subgroup and,
    // being a Groth16 Pedersen commitment, is not the point at infinity).
    let cx = commitment.x;
    let cy = commitment.y;
    let mut hasher = Keccak256::new();
    hasher.update(fq_be32(&cx));
    hasher.update(fq_be32(&cy));
    let digest = hasher.finalize();
    Fr::from_be_bytes_mod_order(&digest)
}

/// Verify a dregg settlement Groth16 proof against the pinned 25-lane statement.
///
/// `inputs` are the 25 public lanes as `u64` (each a canonical BabyBear value in
/// the deployed statement; we accept any value < the scalar field r, mirroring the
/// Solidity `lt(s, R)` guard — the contract layer additionally pins BabyBear
/// canonicality, exactly like `DreggSettlement.sol`).
///
/// Returns `Ok(())` iff BOTH pairing checks pass. Any failure is a hard reject.
pub fn verify(raw: &RawProof, inputs: &[u64; NUM_LANES]) -> Result<(), VerifyError> {
    // --- Parse + subgroup-check every proof-supplied point. ---
    let a = g1_checked(raw.proof[0], raw.proof[1], "A")?;
    let b = g2_checked_c1c0(raw.proof[2], raw.proof[3], raw.proof[4], raw.proof[5], "B")?;
    let c = g1_checked(raw.proof[6], raw.proof[7], "C")?;
    let commitment = g1_checked(raw.commitments[0], raw.commitments[1], "commitment")?;
    let pok = g1_checked(raw.commitment_pok[0], raw.commitment_pok[1], "pok")?;

    // --- Check 1: the Pedersen commitment gate.  e(C, Gσ) · e(pok, G) == 1. ---
    let gsigma = vk_g2(vk::PEDERSEN_GSIGMA_G2);
    let g = vk_g2(vk::PEDERSEN_G_G2);
    let commit_check = Bn254::multi_pairing([commitment, pok], [gsigma, g]);
    if !commit_check.is_zero() {
        return Err(VerifyError::CommitmentInvalid);
    }

    // --- Fold the commitment into the public-input MSM (the 26th IC term). ---
    let h = commitment_fold(&commitment);

    // L = K0 + commitment + Σ_{i<25} input[i]·IC[i] + h·IC[25]
    let mut l = vk_g1(vk::CONSTANT_G1).into_group();
    l += commitment.into_group();
    for (i, &lane) in inputs.iter().enumerate() {
        let s = Fr::from(lane);
        l += vk_g1(vk::PUB_G1[i]) * s;
    }
    l += vk_g1(vk::PUB_G1[NUM_LANES]) * h;
    let l = l.into_affine();

    // --- Check 2: the Groth16 pairing equation.
    //     e(A, B) · e(C, -δ) · e(α, -β) · e(L, -γ) == 1. ---
    let alpha = vk_g1(vk::ALPHA_G1);
    let beta_neg = vk_g2(vk::BETA_NEG_G2);
    let gamma_neg = vk_g2(vk::GAMMA_NEG_G2);
    let delta_neg = vk_g2(vk::DELTA_NEG_G2);

    let groth_check = Bn254::multi_pairing([a, c, alpha, l], [b, delta_neg, beta_neg, gamma_neg]);
    if !groth_check.is_zero() {
        return Err(VerifyError::ProofInvalid);
    }
    Ok(())
}
