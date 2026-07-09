//! The TRaccoon `T`-of-`N` threshold signature: KeyGen, the **3-round** Sign
//! ceremony, and Verify — mapped symbol-for-symbol to the NIST-slides protocol
//! (final "Second attempt / Threshold Raccoon").
//!
//! ## KeyGen — `vk = [A | I]·sk`
//!
//! Raccoon is "Schnorr over lattices". The public key is `vk = t = Â·sk` where
//! `Â = [A | I] ∈ R_q^{k×d}` (`d = ℓ+k`) and `sk ∈ R_q^d` is SHORT. Writing
//! `sk = (s₁, s₂)`, `t = A·s₁ + s₂` — an MLWE sample whose error `s₂` is folded
//! into the secret as the identity block. `sk` is Shamir-shared over `R_q`
//! ([`crate::shamir`]) into `s_1,…,s_N`. This "error-in-the-key" shape is why
//! verification needs NO rounding and NO hint (contrast Dilithium/Tanuki): the
//! error is carried inside `z` and the algebra closes exactly.
//!
//! ## The three rounds — and what each one CLOSES
//!
//! | round | message (per party `i`) | what it closes |
//! |-------|-------------------------|----------------|
//! | **1 — commit** | `com_i = H_com(w_i, msg, S)` where `w_i = Â·r_i` (short nonce `r_i`); and the row-mask `m_i = Σ_{j∈S} m_{i,j}` | **Rushing / ROS.** Committing to `w_i` *before* anyone reveals theirs stops a rushing adversary from choosing its nonce as a function of the others (the ROS attack [DEF+19, BLL+22] that breaks a naive 2-round transpose). This is the extra round vs. a 2-round scheme. |
//! | **2 — reveal** | `w_i` (opens the round-1 commitment) | **Binding.** Everyone checks `com_j = H_com(w_j, msg, S)`; a party that swaps its nonce after seeing the others is caught here ([`check_openings`]). |
//! | **3 — respond** | `z_i = r_i + c·λ_{i,S}·s_i + m*_i` with the column-mask `m*_i = Σ_{j∈S} m_{j,i}` | **Share leakage (the lattice-specific attack).** `r_i` is short but `c·λ_{i,S}·s_i` is large, so `z_i` alone would leak `s_i` over many sessions. The fresh one-time mask `m*_i` blinds it; because `Σ_i m_i = Σ_i m*_i` (both equal the grand sum of the mask matrix) the masks cancel in the aggregate `z = Σ_i (z_i − m_i)`. |
//!
//! **Combine / Verify.** `z = Σ_{i∈S} (z_i − m_i) = (Σ r_i) + c·sk = r + c·sk`,
//! a short vector. `σ = (c, z)`. Verify recomputes `w' = Â·z − c·t = Â·r = w`
//! and asserts `H(vk,msg,w') = c` and `‖z‖ ≤ B`.
//!
//! ## The masks in detail (NIST slide "Our idea")
//!
//! Every ordered pair `(i,j)` of parties has a fresh per-session cell
//! `m_{i,j} ∈ R_q^d` derived from the symmetric key they share ([`crate::hash::mask_cell`]).
//! Party `i` broadcasts its **row** sum `m_i = Σ_{j∈S} m_{i,j}` in round 1 and
//! uses its **column** sum `m*_i = Σ_{j∈S} m_{j,i}` in round 3. Since the row
//! sums and column sums of a matrix have the same total,
//! `Σ_{i∈S} m_i = Σ_{i∈S} m*_i`, so `Σ_i (m*_i − m_i) = 0`.

use crate::hash;
use crate::linalg::{PolyMatrix, PolyVec};
use crate::ring::Poly;
use crate::shamir::{self, lagrange_coeff};

/// Reference parameter set (DOCUMENTED, illustrative — NOT the NIST-grade
/// parameter-searched sets).
#[derive(Clone, Copy, Debug)]
pub struct Params {
    /// MLWE height `k` (rows of `A`, and `t ∈ R_q^k`).
    pub k: usize,
    /// MLWE width `ℓ` (columns of `A`).
    pub l: usize,
    /// Total parties `N`.
    pub parties: usize,
    /// Threshold `T`.
    pub threshold: usize,
    /// Challenge Hamming weight `ω` (`‖c‖₀ = ω`, ternary `±1`).
    pub omega: usize,
    /// Secret-key half-width `η_s` (`‖sk‖∞ ≤ η_s`).
    pub eta_s: u64,
    /// Nonce half-width `η_r` (`‖r_i‖∞ ≤ η_r`).
    pub eta_r: u64,
    /// Acceptance bound `B` on the final `‖z‖∞`. Reference/correctness bound:
    /// honest signatures pass with wide margin and garbage/reused-mask responses
    /// fail. FLAG: NOT the security-derived `B` (see the crate boundary doc).
    pub z_bound: u64,
}

impl Params {
    /// The reference set: `k=ℓ=4` (module `d=8`), `N=5`, `T=3`, `ω=19`,
    /// `η_s=η_r=2`, `B=4096`. Honest `‖z‖∞ ≤ T·η_r + ω·η_s ≈ 44 ≪ B ≪ q/2`.
    pub fn reference() -> Self {
        Params {
            k: 4,
            l: 4,
            parties: 5,
            threshold: 3,
            omega: 19,
            eta_s: 2,
            eta_r: 2,
            z_bound: 4096,
        }
    }
    /// Module dimension `d = ℓ + k`.
    pub fn d(&self) -> usize {
        self.l + self.k
    }
}

/// The public verification key `vk = (Â, t)` with `Â = [A | I]`, `t = Â·sk`.
#[derive(Clone, Debug)]
pub struct PublicKey {
    pub params: Params,
    /// The augmented matrix `Â = [A | I] ∈ R_q^{k×d}`.
    pub a_hat: PolyMatrix,
    /// `t = Â·sk ∈ R_q^k`.
    pub t: PolyVec,
}

impl PublicKey {
    /// The stable byte encoding of `vk` hashed by the random oracles.
    pub fn vk_bytes(&self) -> Vec<u8> {
        let mut v = self.a_hat.to_bytes();
        v.extend_from_slice(&self.t.to_bytes());
        v
    }
}

/// A signer's long-term key material: its Shamir share and the symmetric mask
/// setup. FLAG (trusted dealer): in this reference the dealer hands every signer
/// a common `mask_master` from which the pairwise seeds are derived; real
/// TRaccoon distributes only a party's own pairwise symmetric keys (or runs a
/// DKG). See the crate boundary doc.
#[derive(Clone, Debug)]
pub struct SignerKey {
    pub index: usize,
    pub share: PolyVec,
    pub mask_master: [u8; 32],
}

/// KeyGen: sample short `sk ∈ R_q^d`, build `Â = [A|I]` from `key_seed`, set
/// `t = Â·sk`, and Shamir-share `sk` into `N` signer keys. Deterministic from
/// `key_seed` (reference — real KeyGen samples fresh CSPRNG entropy / runs DKG).
pub fn keygen(params: Params, key_seed: u64) -> (PublicKey, Vec<SignerKey>) {
    let d = params.d();
    let seed_bytes = key_seed.to_le_bytes();

    // A ∈ R_q^{k×ℓ}, uniform from the seed; then Â = [A | I_k].
    let a_entries = hash::sample_uniform("traccoon/keygen/A", &seed_bytes, params.k * params.l);
    let a_hat = PolyMatrix::from_fn(params.k, d, |r, c| {
        if c < params.l {
            a_entries.0[r * params.l + c]
        } else if c - params.l == r {
            Poly::constant(1) // identity block
        } else {
            Poly::ZERO
        }
    });

    // sk ∈ R_q^d short; t = Â·sk.
    let sk = hash::sample_small("traccoon/keygen/sk", &seed_bytes, d, params.eta_s);
    let t = a_hat.mul_vec(&sk);

    // Shamir-share sk. Common mask master (reference trusted dealer).
    let shares = shamir::share(&sk, params.threshold, params.parties, key_seed ^ 0x5A5A5A5A);
    let mut mask_master = [0u8; 32];
    mask_master.copy_from_slice(
        blake3::hash(&[b"traccoon/mask-master".as_ref(), &seed_bytes].concat()).as_bytes(),
    );

    let signers = shares
        .into_iter()
        .map(|sh| SignerKey {
            index: sh.index,
            share: sh.value,
            mask_master,
        })
        .collect();

    (PublicKey { params, a_hat, t }, signers)
}

// ----------------------------------------------------------------------------
// Session id + pairwise mask seeds
// ----------------------------------------------------------------------------

/// The session id binds `(vk, msg, S)`; the per-session masks are fresh in it.
pub fn session_id(pk: &PublicKey, msg: &[u8], set: &[usize]) -> Vec<u8> {
    let mut h = blake3::Hasher::new();
    h.update(b"traccoon/sid");
    for part in [&pk.vk_bytes()[..], msg, &hash::encode_set(set)] {
        h.update(&(part.len() as u64).to_le_bytes());
        h.update(part);
    }
    h.finalize().as_bytes().to_vec()
}

/// The symmetric seed shared by parties `i` and `j` (unordered), derived from
/// the common `mask_master`.
fn pairwise_seed(mask_master: &[u8; 32], i: usize, j: usize) -> Vec<u8> {
    let (a, b) = if i < j { (i, j) } else { (j, i) };
    blake3::hash(
        &[
            mask_master.as_ref(),
            &(a as u64).to_le_bytes(),
            &(b as u64).to_le_bytes(),
        ]
        .concat(),
    )
    .as_bytes()
    .to_vec()
}

/// Party `i`'s ROW-mask `m_i = Σ_{j∈S, j≠i} m_{i,j}` (broadcast in round 1).
fn row_mask(key: &SignerKey, set: &[usize], sid: &[u8], d: usize) -> PolyVec {
    let mut acc = PolyVec::zero(d);
    for &j in set {
        if j == key.index {
            continue;
        }
        let seed = pairwise_seed(&key.mask_master, key.index, j);
        acc = acc.add(&hash::mask_cell(&seed, sid, key.index, j, d));
    }
    acc
}

/// Party `i`'s COLUMN-mask `m*_i = Σ_{j∈S, j≠i} m_{j,i}` (used in round 3).
fn col_mask(key: &SignerKey, set: &[usize], sid: &[u8], d: usize) -> PolyVec {
    let mut acc = PolyVec::zero(d);
    for &j in set {
        if j == key.index {
            continue;
        }
        let seed = pairwise_seed(&key.mask_master, key.index, j);
        acc = acc.add(&hash::mask_cell(&seed, sid, j, key.index, d));
    }
    acc
}

// ----------------------------------------------------------------------------
// Round messages + per-signer session state
// ----------------------------------------------------------------------------

/// Round 1 broadcast: the nonce commitment `com_i` and the row-mask `m_i`.
#[derive(Clone, Debug)]
pub struct Round1Msg {
    pub index: usize,
    pub com: [u8; 32],
    pub row_mask: PolyVec,
}

/// Round 2 broadcast: the opened nonce commitment `w_i`.
#[derive(Clone, Debug)]
pub struct Round2Msg {
    pub index: usize,
    pub w: PolyVec,
}

/// Round 3 broadcast: the masked partial response `z_i`.
#[derive(Clone, Debug)]
pub struct Round3Msg {
    pub index: usize,
    pub z: PolyVec,
}

/// A party's secret ephemeral state carried across the three rounds.
#[derive(Clone, Debug)]
pub struct SignerState {
    pub index: usize,
    r: PolyVec, // the short nonce r_i
    w: PolyVec, // w_i = Â·r_i
    sid: Vec<u8>,
    set: Vec<usize>,
}

/// The final signature `σ = (c, z)`.
#[derive(Clone, Debug)]
pub struct Signature {
    pub c: Poly,
    pub z: PolyVec,
}

impl Signature {
    /// Serialized size in bytes at these reference params (`c` as `N` coeffs +
    /// `z` as `d·N` coeffs, 8 bytes each). Purely informational — the paper's
    /// packed size is ~13 KiB with bit-packing we do not implement.
    pub fn size_bytes(&self) -> usize {
        self.c.to_bytes().len() + self.z.to_bytes().len()
    }
}

// ----------------------------------------------------------------------------
// The three rounds
// ----------------------------------------------------------------------------

/// **Round 1 (commit).** Sample the short nonce `r_i`, form `w_i = Â·r_i`,
/// commit to it, and compute the row-mask. `nonce_seed` seeds the reference
/// nonce sampler (real signing draws fresh CSPRNG entropy each session).
pub fn round1(
    pk: &PublicKey,
    key: &SignerKey,
    msg: &[u8],
    set: &[usize],
    nonce_seed: u64,
) -> (SignerState, Round1Msg) {
    let d = pk.params.d();
    let sid = session_id(pk, msg, set);
    let mut ns = Vec::new();
    ns.extend_from_slice(&nonce_seed.to_le_bytes());
    ns.extend_from_slice(&(key.index as u64).to_le_bytes());
    ns.extend_from_slice(&sid);
    let r = hash::sample_small("traccoon/nonce", &ns, d, pk.params.eta_r);
    let w = pk.a_hat.mul_vec(&r);
    let com = hash::commit(key.index, &w.to_bytes(), msg, set);
    let rm = row_mask(key, set, &sid, d);
    let state = SignerState {
        index: key.index,
        r,
        w: w.clone(),
        sid,
        set: set.to_vec(),
    };
    (
        state,
        Round1Msg {
            index: key.index,
            com,
            row_mask: rm,
        },
    )
}

/// **Round 2 (reveal).** Open the commitment by broadcasting `w_i`.
pub fn round2(state: &SignerState) -> Round2Msg {
    Round2Msg {
        index: state.index,
        w: state.w.clone(),
    }
}

/// Everyone checks every opened `w_j` against its round-1 commitment. Returns
/// `Err(index)` for the first party whose reveal does not match its commitment —
/// this is the **binding** check that catches a rushing party (round 1 → 2).
pub fn check_openings(
    round1: &[Round1Msg],
    round2: &[Round2Msg],
    msg: &[u8],
    set: &[usize],
) -> Result<(), usize> {
    for r2 in round2 {
        let r1 = round1
            .iter()
            .find(|m| m.index == r2.index)
            .unwrap_or_else(|| panic!("no round-1 message for signer {}", r2.index));
        let expected = hash::commit(r2.index, &r2.w.to_bytes(), msg, set);
        if expected != r1.com {
            return Err(r2.index);
        }
    }
    Ok(())
}

/// The aggregate nonce commitment `w = Σ_{i∈S} w_i`.
pub fn aggregate_w(round2: &[Round2Msg], k: usize) -> PolyVec {
    let mut acc = PolyVec::zero(k);
    for m in round2 {
        acc = acc.add(&m.w);
    }
    acc
}

/// The session challenge `c = H(vk, msg, w)`.
pub fn compute_challenge(pk: &PublicKey, msg: &[u8], w: &PolyVec) -> Poly {
    hash::challenge(&pk.vk_bytes(), msg, &w.to_bytes(), pk.params.omega)
}

/// **Round 3 (masked respond).** `z_i = r_i + c·λ_{i,S}·s_i + m*_i`.
pub fn round3(pk: &PublicKey, key: &SignerKey, state: &SignerState, c: &Poly) -> Round3Msg {
    let d = pk.params.d();
    let lam = lagrange_coeff(key.index, &state.set); // λ_{i,S}, a constant poly
    let c_lam = c.mul(&lam);
    let share_term = key.share.scale(&c_lam); // c·λ_{i,S}·s_i
    let mstar = col_mask(key, &state.set, &state.sid, d);
    let z = state.r.add(&share_term).add(&mstar);
    Round3Msg {
        index: key.index,
        z,
    }
}

/// **Combine.** `z = Σ_{i∈S} (z_i − m_i)`, `σ = (c, z)`. The row-masks `m_i`
/// come from the round-1 broadcasts.
pub fn combine(round1: &[Round1Msg], round3: &[Round3Msg], c: Poly, d: usize) -> Signature {
    let mut z = PolyVec::zero(d);
    for r3 in round3 {
        let r1 = round1
            .iter()
            .find(|m| m.index == r3.index)
            .unwrap_or_else(|| panic!("no round-1 message for signer {}", r3.index));
        z = z.add(&r3.z.sub(&r1.row_mask));
    }
    Signature { c, z }
}

/// Verify `σ = (c, z)` for `msg`: recompute `w' = Â·z − c·t`, assert
/// `H(vk,msg,w') = c`, and check `‖z‖∞ ≤ B`.
pub fn verify(pk: &PublicKey, msg: &[u8], sig: &Signature) -> bool {
    if sig.z.norm_inf() > pk.params.z_bound {
        return false;
    }
    let az = pk.a_hat.mul_vec(&sig.z);
    let ct = pk.t.scale(&sig.c);
    let w_prime = az.sub(&ct);
    let c_prime = hash::challenge(&pk.vk_bytes(), msg, &w_prime.to_bytes(), pk.params.omega);
    c_prime == sig.c
}

/// Honest end-to-end driver: run the 3-round ceremony among the signers whose
/// indices are `set`, and return the signature. `session_nonce` seeds the
/// reference nonce samplers. Panics if any opening check fails (honest run).
pub fn run_session(
    pk: &PublicKey,
    keys: &[SignerKey],
    set: &[usize],
    msg: &[u8],
    session_nonce: u64,
) -> Signature {
    let by_index = |i: usize| {
        keys.iter()
            .find(|k| k.index == i)
            .expect("signer key present")
    };

    // Round 1.
    let mut states = Vec::new();
    let mut r1 = Vec::new();
    for &i in set {
        let (st, m) = round1(pk, by_index(i), msg, set, session_nonce);
        states.push(st);
        r1.push(m);
    }
    // Round 2.
    let r2: Vec<Round2Msg> = states.iter().map(round2).collect();
    check_openings(&r1, &r2, msg, set).expect("honest openings must verify");

    // Challenge from the aggregate w.
    let w = aggregate_w(&r2, pk.params.k);
    let c = compute_challenge(pk, msg, &w);

    // Round 3.
    let r3: Vec<Round3Msg> = set
        .iter()
        .map(|&i| {
            let st = states.iter().find(|s| s.index == i).unwrap();
            round3(pk, by_index(i), st, &c)
        })
        .collect();

    combine(&r1, &r3, c, pk.params.d())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn honest_threshold_signature_verifies() {
        let params = Params::reference();
        let (pk, keys) = keygen(params, 0xA11CE);
        let msg = b"attack at dawn";
        // Several distinct T-of-N signer sets all produce verifying signatures.
        for set in [vec![1, 2, 3], vec![2, 4, 5], vec![1, 3, 5]] {
            let sig = run_session(
                &pk,
                &keys,
                &set,
                msg,
                0xC0DE_u64.wrapping_add(set[0] as u64),
            );
            assert!(
                verify(&pk, msg, &sig),
                "honest T-of-N signature must verify for set {set:?}"
            );
        }
    }

    #[test]
    fn signature_is_short() {
        let params = Params::reference();
        let (pk, keys) = keygen(params, 7);
        let sig = run_session(&pk, &keys, &[1, 2, 3], b"m", 42);
        // The masks cancelled: ‖z‖∞ is small (≈ T·η_r + ω·η_s), far below B.
        assert!(sig.z.norm_inf() <= params.z_bound, "‖z‖ within bound");
        assert!(
            sig.z.norm_inf() < 200,
            "aggregate z is genuinely short after unmasking"
        );
    }
}
