//! The Tanuki two-round threshold signature, mapped onto slide 10 (Fig.1,
//! "Tanuki Signing (Draft)") of the NIST MPTS-2026 talk. Line references below
//! are to that figure.
//!
//! ```text
//!   KeyGen                          Offline (Sign1, round 1, preprocessable)
//!   1: (s,e) ← SampleKey            1: R_i ← SampleR
//!   2: t ← ⌊A·s + e⌉                2: E_i ← SampleE
//!   3: (s_1..s_n) ← ShamirShare(s)  3: W_i ← A·R_i + E_i        (W_i ∈ R_q^{k×rep})
//!   4: (sd_1..sd_n) ← SeedGen         broadcast W_i
//!
//!   Online (Sign2, round 2)                     Finalize / Verify
//!   1: ssid ← (T, (W)_{j∈T}, m)                 z ← Σ_{j∈T} z_j; hint h
//!   2: b ← G(vk, ssid)                          σ = (c, z, h)
//!   3: W ← Σ_{j∈T} W_j                          Verify: w' ← ⌊A·z − c·t⌉ + h
//!   4: w ← ⌊W·b⌉                                        c =? H(vk, m, w')
//!   5: c ← H(vk, m, w)                                  ‖z‖,‖h‖ ≤ bounds
//!   6: m_i ← MaskGen(sd_i, ssid)     (Σ_{j∈T} m_j = 0)
//!   7: z_i ← c·λ_{T,i}·s_i + R_i·b + m_i         (z_i ∈ R_q^ℓ)
//! ```
//!
//! Correctness (why `Verify` accepts an honest `σ`): the masks cancel and the
//! shares reconstruct, so
//!   `z = Σ z_j = c·s + R·b`  where `R = Σ R_j`, `W = A·R + E` (`E = Σ E_j`).
//! Then, with `t = ⌊A·s + e⌉` and `ξ = 1` (this reference's scale-keeping
//! rounding),
//!   `A·z − c·t = W·b + δ`,   `δ = −E·b − c·e + c·ρ_t`   (all small),
//! where `ρ_t = (A·s+e) − t` is the key's rounding error. So `⌊A·z − c·t⌉`
//! and `w = ⌊W·b⌉` differ only by the small hint `h = w − ⌊A·z − c·t⌉`, and
//! `w' = ⌊A·z − c·t⌉ + h = w`, making `c = H(vk, m, w')` hold. Both `z` and `h`
//! are short (that is what the norm bounds check).

use crate::hash;
use crate::linalg::{PolyMatrix, PolyVec};
use crate::ring::Poly;
use crate::shamir::{self, Share};

/// Reference scheme parameters (DOCUMENTED, not NIST-audit-grade — see the crate
/// boundary doc). Dimensions `k, ℓ, rep`; signer count `n`, threshold `t`;
/// challenge weight `ω`; small-element half-widths `η`.
#[derive(Clone, Debug)]
pub struct Params {
    pub k: usize,       // rows of A / codomain rank
    pub ell: usize,     // cols of A / secret rank
    pub rep: usize,     // replication columns of the wide commitment / |b|
    pub n: usize,       // number of signers
    pub t: usize,       // threshold
    pub omega: usize,   // challenge Hamming weight
    pub eta_s: u64,     // secret half-width
    pub eta_e: u64,     // key-error half-width
    pub eta_r: u64,     // commitment-randomness half-width
    pub eta_ecomm: u64, // commitment-error half-width
    /// Acceptance bounds (‖z‖∞, ‖h‖∞). Calibrated so honest signatures pass with
    /// margin AND a random/forged response is rejected; NOT security-derived.
    pub z_bound: u64,
    pub h_bound: u64,
}

impl Params {
    /// The reference parameter set used by the tests.
    pub fn reference() -> Self {
        Params {
            k: 4,
            ell: 4,
            rep: 4,
            n: 5,
            t: 3,
            omega: 20,
            eta_s: 2,
            eta_e: 2,
            eta_r: 2,
            eta_ecomm: 2,
            z_bound: 512,
            h_bound: 2048,
        }
    }
}

/// The public verification key `vk = (A, t)`.
#[derive(Clone, Debug)]
pub struct VerifyingKey {
    pub a: PolyMatrix, // A ∈ R_q^{k×ℓ}
    pub t: PolyVec,    // t = ⌊A·s + e⌉ ∈ R_q^k
}

impl VerifyingKey {
    /// Canonical byte encoding hashed by `G`/`H` (binds A and t).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = self.a.to_bytes();
        for p in &self.t.0 {
            for &c in &p.coeffs {
                out.extend_from_slice(&c.to_le_bytes());
            }
        }
        out
    }
}

/// One signer's secret material: its Shamir share `s_i` and the mask master seed.
///
/// FLAG (trusted-dealer reference): all signers hold the same `master_seed` and
/// derive pairwise seeds `sd_{i,j}` from it. Real Tanuki distributes only the
/// pairwise seeds a party shares (its row), never a global master; `SeedGen` /
/// key distribution is a trusted-dealer stand-in here.
#[derive(Clone, Debug)]
pub struct SignerKey {
    pub index: usize,
    pub share: PolyVec, // s_i ∈ R_q^ℓ
    pub master_seed: [u8; 32],
}

/// KeyGen output: the public `vk` and every signer's secret key.
pub struct KeyPackage {
    pub params: Params,
    pub vk: VerifyingKey,
    pub signer_keys: Vec<SignerKey>,
}

/// Derive the pairwise PRF seed `sd_{i,j} = sd_{j,i}` from the shared master seed.
fn pairwise_seed(master: &[u8; 32], i: usize, j: usize) -> Vec<u8> {
    let (a, b) = if i < j { (i, j) } else { (j, i) };
    let mut h = blake3::Hasher::new();
    h.update(b"tanuki/SeedGen/pairwise");
    h.update(master);
    h.update(&(a as u32).to_le_bytes());
    h.update(&(b as u32).to_le_bytes());
    h.finalize().as_bytes().to_vec()
}

/// KeyGen (Fig.1 KeyGen box). Trusted-dealer reference: samples `A`, the short
/// `(s, e)`, forms the rounded key `t = ⌊A·s + e⌉`, Shamir-shares `s`, and
/// generates the mask master seed. `master_key_seed` seeds all reference sampling.
pub fn keygen(params: &Params, master_key_seed: &[u8]) -> KeyPackage {
    // A ∈ R_q^{k×ℓ}, uniform from a public seed.
    let a = {
        let flat = hash::sample_uniform("tanuki/keygen/A", master_key_seed, params.k * params.ell);
        PolyMatrix::from_fn(params.k, params.ell, |r, c| flat.0[r * params.ell + c])
    };
    // (s, e) ← SampleKey: short secret and error.
    let mut s_seed = master_key_seed.to_vec();
    s_seed.extend_from_slice(b"/s");
    let s = hash::sample_small("tanuki/keygen/s", &s_seed, params.ell, params.eta_s);
    let mut e_seed = master_key_seed.to_vec();
    e_seed.extend_from_slice(b"/e");
    let e = hash::sample_small("tanuki/keygen/e", &e_seed, params.k, params.eta_e);
    // t ← ⌊A·s + e⌉ (rounded MLWE key).
    let t = a.mul_vec(&s).add(&e).round_drop();

    // Shamir-share s.
    let coeff_seed = u64::from_le_bytes(
        blake3::hash(master_key_seed).as_bytes()[..8]
            .try_into()
            .unwrap(),
    );
    let shares: Vec<Share> = shamir::share(&s, params.t, params.n, coeff_seed);

    // Mask master seed.
    let master_seed: [u8; 32] =
        *blake3::hash(&[master_key_seed, b"/mask-master"].concat()).as_bytes();

    let signer_keys = shares
        .into_iter()
        .map(|sh| SignerKey {
            index: sh.index,
            share: sh.value,
            master_seed,
        })
        .collect();

    KeyPackage {
        params: params.clone(),
        vk: VerifyingKey { a, t },
        signer_keys,
    }
}

// ============================================================================
// Round 1 — Offline (Sign1)
// ============================================================================

/// The public round-1 broadcast: the wide commitment `W_i ∈ R_q^{k×rep}`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Round1Public {
    pub index: usize,
    pub w_i: PolyMatrix,
}

/// The secret round-1 state a signer keeps for round 2: its commitment
/// randomness `R_i ∈ R_q^{ℓ×rep}`.
#[derive(Clone, Debug)]
pub struct Round1Secret {
    pub index: usize,
    pub r_i: PolyMatrix,
}

/// Sign1 (Fig.1 Offline box). Samples `R_i`, `E_i`, and broadcasts
/// `W_i = A·R_i + E_i` IN THE CLEAR (no hash commitment — the Tanuki/Ringtail
/// rushing defense is the hashed `b`-aggregation of round 2, not commit-reveal).
/// `nonce` gives a fresh per-session randomness seed.
pub fn sign1(
    params: &Params,
    vk: &VerifyingKey,
    index: usize,
    nonce: &[u8],
) -> (Round1Public, Round1Secret) {
    let mut r_seed = nonce.to_vec();
    r_seed.extend_from_slice(b"/R");
    r_seed.extend_from_slice(&(index as u32).to_le_bytes());
    let r_flat = hash::sample_small_flat(
        "tanuki/sign1/R",
        &r_seed,
        params.ell * params.rep,
        params.eta_r,
    );
    let r_i = PolyMatrix::from_fn(params.ell, params.rep, |r, c| r_flat[r * params.rep + c]);

    let mut e_seed = nonce.to_vec();
    e_seed.extend_from_slice(b"/E");
    e_seed.extend_from_slice(&(index as u32).to_le_bytes());
    let e_flat = hash::sample_small_flat(
        "tanuki/sign1/E",
        &e_seed,
        params.k * params.rep,
        params.eta_ecomm,
    );
    let e_i = PolyMatrix::from_fn(params.k, params.rep, |r, c| e_flat[r * params.rep + c]);

    // W_i = A·R_i + E_i  (k×rep).
    let w_i = vk.a.matmul(&r_i).add(&e_i);

    (Round1Public { index, w_i }, Round1Secret { index, r_i })
}

// ============================================================================
// Session binding: ssid = (T, {W_j}_{j∈T}, m)
// ============================================================================

/// Canonical `ssid` encoding: the sorted signer set `T`, each `W_j` (in index
/// order), and the message `m`. This is what `b ← G(vk, ssid)` binds, so a
/// swapped `W_j` (or a different `T`/`m`) changes `b` and hence the signature.
fn encode_ssid(round1: &[Round1Public], msg: &[u8]) -> Vec<u8> {
    let mut sorted: Vec<&Round1Public> = round1.iter().collect();
    sorted.sort_by_key(|r| r.index);
    let mut out = Vec::new();
    out.extend_from_slice(b"tanuki/ssid/v1");
    out.extend_from_slice(&(sorted.len() as u32).to_le_bytes());
    for r in &sorted {
        out.extend_from_slice(&(r.index as u32).to_le_bytes());
        out.extend_from_slice(&r.w_i.to_bytes());
    }
    out.extend_from_slice(&(msg.len() as u64).to_le_bytes());
    out.extend_from_slice(msg);
    out
}

/// The signer set `T` (sorted indices) implied by a round-1 broadcast set.
fn signer_set(round1: &[Round1Public]) -> Vec<usize> {
    let mut set: Vec<usize> = round1.iter().map(|r| r.index).collect();
    set.sort_unstable();
    set
}

/// Bytes of a `PolyVec` for hashing (`w` feeds `H`).
fn polyvec_bytes(v: &PolyVec) -> Vec<u8> {
    let mut out = Vec::new();
    for p in &v.0 {
        for &c in &p.coeffs {
            out.extend_from_slice(&c.to_le_bytes());
        }
    }
    out
}

// ============================================================================
// Round 2 — Online (Sign2)
// ============================================================================

/// The public round-2 broadcast: `z_i ∈ R_q^ℓ`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Round2Public {
    pub index: usize,
    pub z_i: PolyVec,
}

/// Sign2 (Fig.1 Online box) for signer `index`, given all round-1 broadcasts
/// `round1` (which fix `T` and `{W_j}`) and the message. Returns `z_i`.
pub fn sign2(
    params: &Params,
    vk: &VerifyingKey,
    key: &SignerKey,
    secret: &Round1Secret,
    round1: &[Round1Public],
    msg: &[u8],
) -> Round2Public {
    assert_eq!(key.index, secret.index);
    let set = signer_set(round1);
    let ssid = encode_ssid(round1, msg);
    let vk_bytes = vk.to_bytes();

    // b ← G(vk, ssid).
    let b = hash::agg_vector(&vk_bytes, &ssid, params.rep);
    // W ← Σ_{j∈T} W_j ; w ← ⌊W·b⌉.
    let w = aggregate_w(round1).mul_vec(&b).round_drop();
    // c ← H(vk, m, w).
    let c = hash::challenge(&vk_bytes, msg, &polyvec_bytes(&w), params.omega);

    // m_i ← MaskGen(sd_i, ssid).
    let master = key.master_seed;
    let pw = |i: usize, j: usize| pairwise_seed(&master, i, j);
    let m_i = hash::mask_gen(key.index, &set, &pw, &ssid, params.ell);

    // z_i ← c·λ_{T,i}·s_i + R_i·b + m_i.
    let lambda = shamir::lagrange_coeff(key.index, &set);
    let c_lambda = c.mul(&lambda);
    let term_key = key.share.scale(&c_lambda);
    let term_commit = secret.r_i.mul_vec(&b);
    let z_i = term_key.add(&term_commit).add(&m_i);

    Round2Public {
        index: key.index,
        z_i,
    }
}

/// `W ← Σ_{j∈T} W_j`.
fn aggregate_w(round1: &[Round1Public]) -> PolyMatrix {
    let mut it = round1.iter();
    let first = it.next().expect("non-empty signer set");
    let mut acc = first.w_i.clone();
    for r in it {
        acc = acc.add(&r.w_i);
    }
    acc
}

// ============================================================================
// Finalize + Verify
// ============================================================================

/// A Tanuki signature `σ = (c, z, h)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Signature {
    pub c: Poly,    // the challenge
    pub z: PolyVec, // z = Σ z_j ∈ R_q^ℓ
    pub h: PolyVec, // hint h ∈ R_q^k reconciling the two roundings
}

/// Finalize (Fig.1 Finalize box): combine the round-2 shares into `σ = (c, z, h)`.
/// The combiner re-derives `b`, `W`, `w` (it holds all `W_j` and the message),
/// sums the `z_j`, and computes the hint `h = w − ⌊A·z − c·t⌉`.
pub fn finalize(
    params: &Params,
    vk: &VerifyingKey,
    round1: &[Round1Public],
    round2: &[Round2Public],
    msg: &[u8],
) -> Signature {
    let ssid = encode_ssid(round1, msg);
    let vk_bytes = vk.to_bytes();
    let b = hash::agg_vector(&vk_bytes, &ssid, params.rep);
    let w = aggregate_w(round1).mul_vec(&b).round_drop();
    let c = hash::challenge(&vk_bytes, msg, &polyvec_bytes(&w), params.omega);

    // z = Σ_{j∈T} z_j.
    let mut z = PolyVec::zero(params.ell);
    for r in round2 {
        z = z.add(&r.z_i);
    }

    // h = w − ⌊A·z − c·t⌉.
    let partial = vk.a.mul_vec(&z).sub(&vk.t.scale(&c)).round_drop();
    let h = w.sub(&partial);

    Signature { c, z, h }
}

/// Verify (Fig.1 / slide 7 Raccoon check): recompute `w' = ⌊A·z − c·t⌉ + h`,
/// require `c = H(vk, m, w')`, and check the norm bounds on `z` and `h`.
pub fn verify(params: &Params, vk: &VerifyingKey, msg: &[u8], sig: &Signature) -> bool {
    // Norm bounds (‖z‖∞, ‖h‖∞) — the lattice-soundness leg.
    if sig.z.norm_inf() > params.z_bound {
        return false;
    }
    if sig.h.norm_inf() > params.h_bound {
        return false;
    }
    // w' ← ⌊A·z − c·t⌉ + h.
    let partial = vk.a.mul_vec(&sig.z).sub(&vk.t.scale(&sig.c)).round_drop();
    let w_prime = partial.add(&sig.h);
    // c =? H(vk, m, w').
    let vk_bytes = vk.to_bytes();
    let c_check = hash::challenge(&vk_bytes, msg, &polyvec_bytes(&w_prime), params.omega);
    c_check == sig.c
}

// ============================================================================
// One-call reference ceremony (drives the full two rounds; used by tests)
// ============================================================================

/// Run the full honest ceremony with the signer subset `signers` (indices into
/// `keys.signer_keys`) on `msg`, returning the finalized signature and the
/// round-1 broadcasts (so tests can tamper with them). `nonce_base` seeds the
/// per-signer offline randomness.
pub fn run_ceremony(
    keys: &KeyPackage,
    signer_positions: &[usize],
    msg: &[u8],
    nonce_base: &[u8],
) -> (Signature, Vec<Round1Public>) {
    let params = &keys.params;
    // Round 1 (offline).
    let mut r1_pub = Vec::new();
    let mut r1_sec = Vec::new();
    for &pos in signer_positions {
        let key = &keys.signer_keys[pos];
        let mut nonce = nonce_base.to_vec();
        nonce.extend_from_slice(&(key.index as u32).to_le_bytes());
        let (pubm, sec) = sign1(params, &keys.vk, key.index, &nonce);
        r1_pub.push(pubm);
        r1_sec.push(sec);
    }
    // Round 2 (online).
    let mut r2_pub = Vec::new();
    for (n, &pos) in signer_positions.iter().enumerate() {
        let key = &keys.signer_keys[pos];
        let z_i = sign2(params, &keys.vk, key, &r1_sec[n], &r1_pub, msg);
        r2_pub.push(z_i);
    }
    let sig = finalize(params, &keys.vk, &r1_pub, &r2_pub, msg);
    (sig, r1_pub)
}
