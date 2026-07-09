//! The random oracles TRaccoon names, realized with blake3, plus the reference
//! samplers:
//!
//! * [`commit`]   — `H_com(w_i, msg, S)`, the round-1 nonce commitment. Binding
//!   `w_i` *before* it is revealed in round 2 is the whole point of the commit
//!   round (NIST slide: "We commit to `w_i` before revealing it to avoid ROS
//!   attacks [DEF+19, BLL+22]").
//! * [`challenge`] — `c ← H(vk, msg, w)`, a FIXED-WEIGHT ternary challenge:
//!   exactly `ω` nonzero coefficients, each `±1` (`‖c‖∞ = 1`, `‖c‖₀ = ω`).
//! * [`mask_cell`] — a fresh per-session uniform mask `m_{i,j}` derived from the
//!   symmetric key shared by parties `i,j` (NIST slide "Our idea": users `(i,j)`
//!   share a symmetric key and can generate a fresh `m_{i,j}` each session). It
//!   is DIRECTIONAL: `m_{i,j} ≠ m_{j,i}`, but both parties can compute both
//!   (they share the seed). Row/column sums are assembled in [`crate::threshold`].
//!
//! FLAG (reference samplers): [`sample_small`] draws coefficients in `[−η, η]`
//! by reducing XOF bytes mod `2η+1` — slightly biased and not constant-time; the
//! masks are drawn UNIFORM over `R_q` (perfect statistical hiding of the large
//! `c·λ_{i,S}·s_i` term — the simplest correct choice). Production TRaccoon uses
//! discrete-GAUSSIAN masks whose exactness feeds the Hint-MLWE → MLWE reduction
//! [KLSS23] that the security proof rests on. See the crate boundary doc.

use crate::linalg::PolyVec;
use crate::ring::{Poly, N, Q};

/// A blake3 XOF reader over a domain tag and a sequence of byte chunks. Each
/// part is length-prefixed so the concatenation is injective (no ambiguity).
fn xof(domain: &str, parts: &[&[u8]]) -> blake3::OutputReader {
    let mut h = blake3::Hasher::new();
    h.update(domain.as_bytes());
    for p in parts {
        h.update(&(p.len() as u64).to_le_bytes());
        h.update(p);
    }
    h.finalize_xof()
}

fn next_u64(r: &mut blake3::OutputReader) -> u64 {
    use std::io::Read;
    let mut b = [0u8; 8];
    r.read_exact(&mut b).unwrap();
    u64::from_le_bytes(b)
}

/// Sample a length-`len` vector of "small" `R_q` elements: each coefficient is
/// drawn from `[−eta, eta]`. Deterministic from `(domain, seed)`.
pub fn sample_small(domain: &str, seed: &[u8], len: usize, eta: u64) -> PolyVec {
    let mut r = xof(domain, &[seed]);
    let modulus = 2 * eta + 1;
    PolyVec(
        (0..len)
            .map(|_| {
                let mut coeffs = [0u64; N];
                for c in coeffs.iter_mut() {
                    let v = next_u64(&mut r) % modulus; // in [0, 2eta]
                    let centered = v as i64 - eta as i64; // in [-eta, eta]
                    *c = centered.rem_euclid(Q as i64) as u64;
                }
                Poly { coeffs }
            })
            .collect(),
    )
}

/// A uniform `R_q^{len}` vector from `(domain, seed)` — used to fill the public
/// matrix `A` and (crucially) the one-time masks, which must be uniform to hide
/// the large `c·λ_{i,S}·s_i` share term.
pub fn sample_uniform(domain: &str, seed: &[u8], len: usize) -> PolyVec {
    let mut r = xof(domain, &[seed]);
    PolyVec(
        (0..len)
            .map(|_| {
                let mut coeffs = [0u64; N];
                for c in coeffs.iter_mut() {
                    *c = next_u64(&mut r) % Q;
                }
                Poly { coeffs }
            })
            .collect(),
    )
}

/// `H_com(w_i, msg, S)`: the round-1 commitment to a party's nonce commitment
/// `w_i`. Returns a 32-byte digest. Binds `w_i` together with the message and
/// the (ordered) active signer set `S`.
pub fn commit(index: usize, w_bytes: &[u8], msg: &[u8], set: &[usize]) -> [u8; 32] {
    let set_bytes = encode_set(set);
    let mut h = blake3::Hasher::new();
    h.update(b"traccoon/H_com");
    for part in [&(index as u64).to_le_bytes()[..], w_bytes, msg, &set_bytes] {
        h.update(&(part.len() as u64).to_le_bytes());
        h.update(part);
    }
    *h.finalize().as_bytes()
}

/// `c ← H(vk, msg, w)`: a fixed-weight ternary challenge with exactly `omega`
/// nonzero coefficients, each `±1`. `‖c‖∞ = 1`, `‖c‖₀ = omega`.
pub fn challenge(vk: &[u8], msg: &[u8], w_bytes: &[u8], omega: usize) -> Poly {
    assert!(omega <= N, "challenge weight cannot exceed N");
    let mut r = xof("traccoon/H/challenge", &[vk, msg, w_bytes]);
    let mut coeffs = [0u64; N];
    let mut placed = 0;
    // Rejection placement: put omega ±1's into distinct positions.
    while placed < omega {
        let raw = next_u64(&mut r);
        let pos = (raw >> 1) as usize % N;
        if coeffs[pos] == 0 {
            coeffs[pos] = if raw & 1 == 0 { 1 } else { Q - 1 };
            placed += 1;
        }
    }
    Poly { coeffs }
}

/// A fresh per-session uniform mask cell `m_{from,to} ∈ R_q^d`, derived from the
/// symmetric seed `pairwise_seed` shared by the two parties and the session id
/// `sid`. DIRECTIONAL: the ordered `(from, to)` is folded in, so
/// `m_{i,j} ≠ m_{j,i}` even though both use the same shared seed.
pub fn mask_cell(pairwise_seed: &[u8], sid: &[u8], from: usize, to: usize, d: usize) -> PolyVec {
    let mut buf = Vec::new();
    buf.extend_from_slice(pairwise_seed);
    buf.extend_from_slice(sid);
    buf.extend_from_slice(&(from as u64).to_le_bytes());
    buf.extend_from_slice(&(to as u64).to_le_bytes());
    sample_uniform("traccoon/mask-cell", &buf, d)
}

/// Canonical little-endian encoding of the (sorted) active signer set.
pub fn encode_set(set: &[usize]) -> Vec<u8> {
    let mut sorted = set.to_vec();
    sorted.sort_unstable();
    let mut out = Vec::with_capacity(sorted.len() * 8);
    for i in sorted {
        out.extend_from_slice(&(i as u64).to_le_bytes());
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn challenge_is_fixed_weight_ternary() {
        let c = challenge(b"vk", b"msg", b"w", 19);
        assert_eq!(c.norm_inf(), 1, "challenge is ternary ‖c‖∞ = 1");
        assert_eq!(c.weight(), 19, "challenge has exactly ω nonzeros");
    }

    #[test]
    fn commit_binds_its_inputs() {
        let a = commit(1, b"w-a", b"msg", &[1, 2, 3]);
        assert_ne!(
            a,
            commit(1, b"w-b", b"msg", &[1, 2, 3]),
            "different w → different com"
        );
        assert_ne!(
            a,
            commit(1, b"w-a", b"msg2", &[1, 2, 3]),
            "different msg → different com"
        );
        assert_ne!(
            a,
            commit(1, b"w-a", b"msg", &[1, 2, 4]),
            "different set → different com"
        );
        assert_eq!(
            a,
            commit(1, b"w-a", b"msg", &[3, 2, 1]),
            "set order does not matter"
        );
    }

    #[test]
    fn mask_cells_are_directional() {
        // Same shared seed, opposite direction → different masks.
        let ij = mask_cell(b"seed-1-2", b"sid", 1, 2, 4);
        let ji = mask_cell(b"seed-1-2", b"sid", 2, 1, 4);
        assert_ne!(ij, ji, "m_{{i,j}} ≠ m_{{j,i}}");
        // Fresh per session.
        let ij2 = mask_cell(b"seed-1-2", b"sid-2", 1, 2, 4);
        assert_ne!(ij, ij2, "different session → fresh mask");
    }
}
