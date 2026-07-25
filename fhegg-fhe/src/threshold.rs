//! REAL no-viewer — the n-of-n collective threshold-decrypt with PROVEN smudging (the keystone).
//!
//! Interface fixed in `docs/deos/FHEGG-PROTOTYPE-INTERFACES.md` §1. This file is OWNED by the `threshold`
//! swarm lane. Anchor: fhe.rs `mbfv` (`DecryptionShare`/`PublicKeyShare`/`CommonRandomPoly`) is the crypto
//! oracle; the smudging bound is proven in `metatheory/Bfv/Smudging.lean` — NOT fhe.rs mbfv's fresh-noise TODO.
//!
//! ## What is anchored where (read before touching)
//!
//! * **Collective keygen** rides fhe.rs `mbfv` DIRECTLY: a public CRP seed + one
//!   `PublicKeyShare` per party, aggregated into a real fhe.rs `PublicKey` ("Protocol 1:
//!   EncKeyGen" of [Mouchet et al. 2020](https://eprint.iacr.org/2020/304.pdf)). The production
//!   API is party-owned: each [`ThresholdParty`] independently samples and retains its ternary
//!   secret share, while the [`KeygenCoordinator`] receives only [`PublicKeyContribution`] wire
//!   objects. The collective secret key `s = Σ sᵢ` is never constructed by that API.
//!   This is process-shaped custody, not a network protocol: authenticating the public seed and
//!   messages, persistent secret storage, and malicious-party defenses remain host obligations.
//! * **Partial decryption is OURS**, because fhe.rs `mbfv::DecryptionShare` samples its share error at
//!   the FRESH-noise variance with the literal source comment "TODO this should be exponential in
//!   ciphertext noise!" (`fhe-0.1.1/src/mbfv/secret_key_switch.rs`) — the exact hole this module exists
//!   to close — and its `h_share` is `pub(crate)`, so the error cannot be topped up from outside. We
//!   compute the share `hᵢ = sᵢ·c1 + eᵢ` ourselves over the parsed [`LeanCiphertext`] RNS rows
//!   (negacyclic ternary convolution, the same power-basis representation `bfv_lean` folds in), with
//!   `eᵢ` a SMUDGING noise sampled uniformly from `[-2^b, 2^b]`, `b ≥` [`MIN_SMUDGE_BITS`].
//! * **Combine** sums the shares into `c0' = c0 + Σ hᵢ` (our RNS arithmetic) and then delegates the
//!   rounding/scale step to fhe.rs itself: a ciphertext `(c0', c1)` decrypted under the ALL-ZERO
//!   secret key is exactly the final step of fhe.rs's own `Aggregate<DecryptionShare> for Plaintext`
//!   (`c0 + c1·0`, scale by `t/q`, round). Any error in our share arithmetic that survives this path
//!   is a wrong plaintext under a REAL library — agreement cannot be faked. The tests additionally
//!   pin our combine against (a) the joint-key `s = Σ sᵢ` fhe.rs decrypt and (b) fhe.rs mbfv's own
//!   `DecryptionShare` aggregation over the same key shares.
//!
//! ## The smudging bound (the coordinate with `metatheory/Bfv/Smudging.lean`)
//!
//! The share of an honest party leaks `eᵢ + (ciphertext noise contribution)` to a coalition of the
//! other `n-1` parties (who can subtract everything else they know). Smudging hides that leak
//! statistically: `SD(e_ct + e_smudge, e_smudge) ≤ B_ct / 2^b` for `e_smudge` uniform on `[-2^b, 2^b]`,
//! so `b ≥ log2(B_ct) + λ` gives statistical distance `≤ 2^-λ`.
//!
//! Deployed numbers, PINNED to `metatheory/Bfv/Smudging.lean`'s export (lane 1b, landed mid-swarm):
//! `Bfv.Smudging.smudgeBits = 80` — the smudge is uniform on `[-2^80, 2^80]` (the EXACT distribution
//! [`ThresholdParty::partial_decrypt`] samples; the theorems are about that distribution and no
//! other). Both jaws are proved on the real degree-4096 parameters:
//! * hiding (`deployed_smudge_hides`): against the deployed fold envelope's ciphertext noise
//!   `≤ 2^32` (4096 orders × `B_fresh ≈ 2^20`), a `2^80` smudge hides the secret term to
//!   statistical distance `≤ 2^-48`;
//! * correctness (`deployed_smudged_decrypt_exact`): 16 parties' worth of `2^80` smudge
//!   (`≤ 2^84` total) plus the `2^32` fold noise still decrypts EXACTLY (margin `≈ 2^88`);
//! * failing side (`deployed_smudge_floor_leaks`): a `2^15` smudge on the same envelope leaks
//!   TOTALLY (sd = 1) — the bound is a real cliff, not a safety margin.

use std::sync::Arc;

use fhe::bfv::{BfvParameters, Ciphertext, Encoding, PublicKey, SecretKey};
use fhe::mbfv::{Aggregate, CommonRandomPoly, PublicKeyShare};
use fhe_traits::{DeserializeParametrized, FheDecoder, FheDecrypter, Serialize as FheSerialize};
use rand_09::rngs::StdRng;
use rand_09::{Rng, RngCore, SeedableRng};
use sha2::{Digest, Sha256};

use crate::additive::pick_params;
use crate::bfv_lean::{LeanCiphertext, RnsPoly};

/// Crash-tolerant `t < n` Shamir custody and opening.  The original API in
/// this module remains the smaller, independently tested n-of-n construction.
pub mod quorum;
/// Honest n-of-n multiparty BFV relinearization-key generation.  Each party
/// retains the same secret share used by collective key generation; only the
/// two public fhe.rs protocol-round shares reach the coordinator.
pub mod relin;

pub type Result<T> = std::result::Result<T, ThresholdError>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ThresholdError {
    QuorumTooSmall {
        have: usize,
        need: usize,
    },
    ParamMismatch,
    SmudgeTooSmall,
    SmudgeTooLarge,
    InvalidParty {
        party: usize,
        n_parties: usize,
    },
    InvalidCustodySeed,
    MalformedWire,
    /// The collective public key failed its acceptance gate: a fresh trial value encrypted to it did not
    /// decrypt back to itself under the full quorum. Fail closed — a corrupt collective key (a malformed
    /// party contribution slips past aggregation, which checks c1==CRP + level but NO c0 well-formedness) is
    /// refused, never used. Detection under an honest coordinator, not attribution.
    AcceptanceFailed {
        trial: usize,
    },
}

/// SMUDGE-BOUND-PIN: minimum admissible smudging bit-width `b` (noise uniform on `[-2^b, 2^b]`),
/// pinned to `Bfv.Smudging.smudgeBits = 80` (`metatheory/Bfv/Smudging.lean`, the deployed export):
/// hides the secret term to statistical distance `≤ 2^-48` against the `2^32` fold envelope
/// (`deployed_smudge_hides`), while `deployed_smudge_floor_leaks` proves a sub-bound smudge leaks.
pub const MIN_SMUDGE_BITS: u32 = 80;

/// Correctness ceiling: `Bfv.Smudging.deployed_smudged_decrypt_exact` proves the decrypt margin
/// holds for TOTAL smudge `≤ 2^84` (= 16 parties × `2^80`) plus the `2^32` fold envelope.
/// [`ThresholdParty::partial_decrypt`] enforces the per-party form
/// `smudge_bits + ceil(log2(n)) ≤ 84`.
pub const MAX_SMUDGE_BITS_TOTAL: u32 = 84;

fn ceil_log2_parties(n: usize) -> Option<u32> {
    (n != 0).then(|| usize::BITS - (n - 1).leading_zeros())
}

/// One party's share of the collective secret key (party-local in the production API).
///
/// `coeffs` (ternary, self-sampled) is the secret; it is deliberately private to this module.
/// NAMED GAP: no zeroize-on-drop (the crate has no `zeroize` dep and lanes may not add deps).
struct KeyShare {
    coeffs: Vec<i64>,
    /// This party's index in `0..n_parties`.
    pub party: usize,
    /// The quorum size n fixed at keygen (n-of-n: all shares are needed).
    pub n_parties: usize,
}

/// One party's SMUDGED partial decryption of the folded aggregate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecryptShare {
    /// `hᵢ = sᵢ·c1 + eᵢ` as RNS rows (one row per ciphertext modulus, power-basis order).
    h: Vec<Vec<u64>>,
    /// The ciphertext this share decrypts (mirrors mbfv's `SecretKeySwitchShare::ct`); combine
    /// refuses shares over different ciphertexts.
    ct: LeanCiphertext,
    party: usize,
    n_parties: usize,
    smudge_bits: u32,
}

impl DecryptShare {
    /// Party identifier carried by this public decryption-share message.
    pub fn party(&self) -> usize {
        self.party
    }

    /// n-of-n quorum size carried by this public decryption-share message.
    pub fn n_parties(&self) -> usize {
        self.n_parties
    }

    /// Smudging width claimed by this share; [`combine`] enforces the Lean-pinned floor.
    pub fn smudge_bits(&self) -> u32 {
        self.smudge_bits
    }

    /// Exact public ciphertext this share was computed over. Boundary protocols
    /// use this to bind a full quorum to their session target; equality among the
    /// shares alone is not sufficient.
    pub fn ciphertext(&self) -> &LeanCiphertext {
        &self.ct
    }

    /// Public RNS rows `hᵢ = sᵢ·c1 + eᵢ` transmitted to the coordinator.
    pub fn h_rows(&self) -> &[Vec<u64>] {
        &self.h
    }

    /// Encode the complete public decryption-share message for an external transport.
    /// This is a framing codec only: it does not authenticate the sender or prove share validity.
    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let ct_bytes = self.ct.to_fhe_bytes();
        let coefficient_count = self.h.iter().map(Vec::len).sum::<usize>();
        let mut out = Vec::with_capacity(64 + ct_bytes.len() + coefficient_count * 8);
        out.extend_from_slice(b"FHDSv001");
        out.extend_from_slice(&(self.party as u64).to_le_bytes());
        out.extend_from_slice(&(self.n_parties as u64).to_le_bytes());
        out.extend_from_slice(&self.smudge_bits.to_le_bytes());
        out.extend_from_slice(&self.ct.plain_bound.to_le_bytes());
        out.extend_from_slice(&(ct_bytes.len() as u64).to_le_bytes());
        out.extend_from_slice(&ct_bytes);
        for row in &self.h {
            for &coefficient in row {
                out.extend_from_slice(&coefficient.to_le_bytes());
            }
        }
        out
    }

    /// Parse a public decryption-share message after transport.
    ///
    /// Structural and parameter checks happen here; quorum, duplicate-party, ciphertext equality,
    /// and the Lean smudging floor remain fail-closed in [`combine`].
    pub fn from_wire_bytes(bytes: &[u8], params: &BfvParams) -> Result<Self> {
        let mut i = 0usize;
        if take_wire::<8>(bytes, &mut i)? != *b"FHDSv001" {
            return Err(ThresholdError::MalformedWire);
        }
        let party = usize::try_from(u64::from_le_bytes(take_wire::<8>(bytes, &mut i)?))
            .map_err(|_| ThresholdError::MalformedWire)?;
        let n_parties = usize::try_from(u64::from_le_bytes(take_wire::<8>(bytes, &mut i)?))
            .map_err(|_| ThresholdError::MalformedWire)?;
        let smudge_bits = u32::from_le_bytes(take_wire::<4>(bytes, &mut i)?);
        let plain_bound = u64::from_le_bytes(take_wire::<8>(bytes, &mut i)?);
        let ct_len = usize::try_from(u64::from_le_bytes(take_wire::<8>(bytes, &mut i)?))
            .map_err(|_| ThresholdError::MalformedWire)?;
        let ct_end = i
            .checked_add(ct_len)
            .filter(|&end| end <= bytes.len())
            .ok_or(ThresholdError::MalformedWire)?;
        let ct = LeanCiphertext::from_fhe_bytes(
            &bytes[i..ct_end],
            params.moduli(),
            params.degree(),
            plain_bound,
        )
        .map_err(|_| ThresholdError::MalformedWire)?;
        i = ct_end;

        if n_parties == 0 || party >= n_parties {
            return Err(ThresholdError::InvalidParty { party, n_parties });
        }
        let expected_coefficients = params
            .moduli()
            .len()
            .checked_mul(params.degree())
            .ok_or(ThresholdError::MalformedWire)?;
        let expected_bytes = expected_coefficients
            .checked_mul(8)
            .ok_or(ThresholdError::MalformedWire)?;
        if bytes.len().checked_sub(i) != Some(expected_bytes) {
            return Err(ThresholdError::MalformedWire);
        }
        let mut h = Vec::with_capacity(params.moduli().len());
        for &q in params.moduli() {
            let mut row = Vec::with_capacity(params.degree());
            for _ in 0..params.degree() {
                let coefficient = u64::from_le_bytes(take_wire::<8>(bytes, &mut i)?);
                if coefficient >= q {
                    return Err(ThresholdError::MalformedWire);
                }
                row.push(coefficient);
            }
            h.push(row);
        }
        if i != bytes.len() {
            return Err(ThresholdError::MalformedWire);
        }
        Ok(Self {
            h,
            ct,
            party,
            n_parties,
            smudge_bits,
        })
    }
}

/// The collective public key everyone encrypts to — a REAL fhe.rs `PublicKey`, aggregated from
/// per-party mbfv `PublicKeyShare`s.
#[derive(Clone)]
pub struct CollectivePublicKey {
    /// Use with `fhe_traits::FheEncrypter` exactly like a single-party key.
    pub pk: PublicKey,
}

/// BFV parameter handle (degree/moduli/t) — the fold set for this prototype.
#[derive(Clone)]
pub struct BfvParams {
    arc: Arc<BfvParameters>,
}

/// Public key-generation session data.
///
/// The seed deterministically expands to the common random polynomial through the pinned
/// `rand_09::rngs::StdRng` implementation. It is public and safe to broadcast. A real deployment
/// must agree/authenticate this value; this module does not provide a beacon or transport.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KeygenSession {
    n_parties: usize,
    crp_seed: [u8; 32],
}

impl KeygenSession {
    /// Start a key-generation session with an OS-random public CRP seed.
    pub fn random(n_parties: usize) -> Result<Self> {
        if n_parties == 0 {
            return Err(ThresholdError::QuorumTooSmall { have: 0, need: 1 });
        }
        if MIN_SMUDGE_BITS + ceil_log2_parties(n_parties).expect("nonzero") > MAX_SMUDGE_BITS_TOTAL
        {
            return Err(ThresholdError::SmudgeTooLarge);
        }
        let mut crp_seed = [0u8; 32];
        rand_09::rng().fill_bytes(&mut crp_seed);
        Ok(Self {
            n_parties,
            crp_seed,
        })
    }

    /// Re-enter a session from public wire data.
    pub fn from_seed(n_parties: usize, crp_seed: [u8; 32]) -> Result<Self> {
        if n_parties == 0 {
            return Err(ThresholdError::QuorumTooSmall { have: 0, need: 1 });
        }
        if MIN_SMUDGE_BITS + ceil_log2_parties(n_parties).expect("nonzero") > MAX_SMUDGE_BITS_TOTAL
        {
            return Err(ThresholdError::SmudgeTooLarge);
        }
        Ok(Self {
            n_parties,
            crp_seed,
        })
    }

    pub fn n_parties(&self) -> usize {
        self.n_parties
    }

    pub fn crp_seed(&self) -> [u8; 32] {
        self.crp_seed
    }

    fn common_random_poly(&self, params: &BfvParams) -> CommonRandomPoly {
        let mut rng = StdRng::from_seed(self.crp_seed);
        CommonRandomPoly::new(params.arc(), &mut rng).expect("CRP sampling from public seed")
    }
}

/// Public contribution emitted by one party during key generation.
///
/// `public_key_bytes` is a singleton fhe.rs public key whose `c0` is this party's EncKeyGen
/// share and whose `c1` is the session CRP. It contains no secret-key coefficients.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PublicKeyContribution {
    session: KeygenSession,
    party: usize,
    public_key_bytes: Vec<u8>,
}

impl PublicKeyContribution {
    pub fn session(&self) -> &KeygenSession {
        &self.session
    }

    pub fn party(&self) -> usize {
        self.party
    }

    /// Canonical fhe.rs `PublicKey` bytes carrying this public contribution.
    pub fn public_key_bytes(&self) -> &[u8] {
        &self.public_key_bytes
    }

    /// Encode this public contribution for an external transport.
    /// This framing is not an authentication mechanism.
    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(64 + self.public_key_bytes.len());
        out.extend_from_slice(b"FHPKv001");
        out.extend_from_slice(&(self.party as u64).to_le_bytes());
        out.extend_from_slice(&(self.session.n_parties as u64).to_le_bytes());
        out.extend_from_slice(&self.session.crp_seed);
        out.extend_from_slice(&(self.public_key_bytes.len() as u64).to_le_bytes());
        out.extend_from_slice(&self.public_key_bytes);
        out
    }

    /// Decode the public contribution framing after transport.
    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self> {
        let mut i = 0usize;
        if take_wire::<8>(bytes, &mut i)? != *b"FHPKv001" {
            return Err(ThresholdError::MalformedWire);
        }
        let party = usize::try_from(u64::from_le_bytes(take_wire::<8>(bytes, &mut i)?))
            .map_err(|_| ThresholdError::MalformedWire)?;
        let n_parties = usize::try_from(u64::from_le_bytes(take_wire::<8>(bytes, &mut i)?))
            .map_err(|_| ThresholdError::MalformedWire)?;
        let crp_seed = take_wire::<32>(bytes, &mut i)?;
        let pk_len = usize::try_from(u64::from_le_bytes(take_wire::<8>(bytes, &mut i)?))
            .map_err(|_| ThresholdError::MalformedWire)?;
        let end = i
            .checked_add(pk_len)
            .filter(|&end| end == bytes.len())
            .ok_or(ThresholdError::MalformedWire)?;
        Self::from_wire_parts(
            KeygenSession::from_seed(n_parties, crp_seed)?,
            party,
            bytes[i..end].to_vec(),
        )
    }

    /// Reconstruct the public message after transport. Cryptographic/parameter validation is
    /// performed by [`KeygenCoordinator::finish`].
    pub fn from_wire_parts(
        session: KeygenSession,
        party: usize,
        public_key_bytes: Vec<u8>,
    ) -> Result<Self> {
        if party >= session.n_parties {
            return Err(ThresholdError::InvalidParty {
                party,
                n_parties: session.n_parties,
            });
        }
        if public_key_bytes.is_empty() {
            return Err(ThresholdError::MalformedWire);
        }
        Ok(Self {
            session,
            party,
            public_key_bytes,
        })
    }
}

fn take_wire<const N: usize>(bytes: &[u8], i: &mut usize) -> Result<[u8; N]> {
    let end = i
        .checked_add(N)
        .filter(|&end| end <= bytes.len())
        .ok_or(ThresholdError::MalformedWire)?;
    let out = bytes[*i..end]
        .try_into()
        .map_err(|_| ThresholdError::MalformedWire)?;
    *i = end;
    Ok(out)
}

/// A party-local threshold state. It intentionally has no `Clone`, `Debug`, or secret accessor.
/// Construct this inside the party process and keep it there.
pub struct ThresholdParty {
    key_share: KeyShare,
    /// Retained public identity of the key-generation ceremony that created
    /// `key_share`.  Descendant protocol modules use it to prevent a share
    /// from being replayed into a different collective-key session.
    keygen_session: KeygenSession,
}

impl ThresholdParty {
    /// Independently sample this party's secret share and emit only its public EncKeyGen message.
    pub fn join(
        session: &KeygenSession,
        party: usize,
        params: &BfvParams,
    ) -> Result<(Self, PublicKeyContribution)> {
        let mut rng = rand_09::rng();
        Self::join_with_rng(session, party, params, &mut rng)
    }

    /// Reconstructible party-local key generation from an independently
    /// custodied 32-byte root. The root is domain-separated by the complete
    /// public ceremony identity, party index, and BFV parameter set before it
    /// seeds key-share and public-contribution sampling. Consequently the same
    /// inputs reproduce the exact `ThresholdParty` and public contribution
    /// after a process restart, while another ceremony or party gets unrelated
    /// randomness.
    ///
    /// This is a custody boundary, not a shared dealer: every party must keep a
    /// distinct, high-entropy root outside the coordinator process. The root is
    /// never retained in `ThresholdParty` or emitted on a wire. An all-zero root
    /// is refused as an obvious deployment misconfiguration.
    pub fn join_seeded(
        session: &KeygenSession,
        party: usize,
        params: &BfvParams,
        custody_root: &[u8; 32],
    ) -> Result<(Self, PublicKeyContribution)> {
        if custody_root.iter().all(|byte| *byte == 0) {
            return Err(ThresholdError::InvalidCustodySeed);
        }
        let seed = threshold_party_seed(session, party, params, custody_root)?;
        let mut rng = StdRng::from_seed(seed);
        Self::join_with_rng(session, party, params, &mut rng)
    }

    fn join_with_rng<R: RngCore + rand_09::CryptoRng>(
        session: &KeygenSession,
        party: usize,
        params: &BfvParams,
        rng: &mut R,
    ) -> Result<(Self, PublicKeyContribution)> {
        if party >= session.n_parties {
            return Err(ThresholdError::InvalidParty {
                party,
                n_parties: session.n_parties,
            });
        }

        let coeffs = (0..params.degree())
            .map(|_| rng.random_range(-1i64..=1))
            .collect::<Vec<_>>();
        let key_share = KeyShare {
            coeffs,
            party,
            n_parties: session.n_parties,
        };
        let sk = sk_from_coeffs(&key_share.coeffs, params.arc());
        let pk_share = PublicKeyShare::new(&sk, session.common_random_poly(params), rng)
            .expect("mbfv PublicKeyShare");
        // A singleton aggregation is a public wire container for (p0_i, CRP). The coordinator
        // later sums only p0_i and keeps one CRP, exactly matching mbfv's Aggregate impl.
        let singleton_pk =
            PublicKey::from_shares([pk_share]).expect("singleton public contribution");
        let contribution = PublicKeyContribution {
            session: session.clone(),
            party,
            public_key_bytes: singleton_pk.to_bytes(),
        };
        Ok((
            Self {
                key_share,
                keygen_session: session.clone(),
            },
            contribution,
        ))
    }

    pub fn party(&self) -> usize {
        self.key_share.party
    }

    /// Produce the only secret-dependent object that leaves this party after keygen.
    /// The exact Lean-pinned smudging floor and total correctness ceiling are both enforced here.
    pub fn partial_decrypt(&self, ct: &LeanCiphertext, smudge_bits: u32) -> Result<DecryptShare> {
        if smudge_bits < MIN_SMUDGE_BITS {
            return Err(ThresholdError::SmudgeTooSmall);
        }
        let log2_n =
            ceil_log2_parties(self.key_share.n_parties).ok_or(ThresholdError::ParamMismatch)?;
        if smudge_bits
            .checked_add(log2_n)
            .map_or(true, |total| total > MAX_SMUDGE_BITS_TOTAL)
        {
            return Err(ThresholdError::SmudgeTooLarge);
        }
        Ok(partial_decrypt_inner(&self.key_share, ct, smudge_bits))
    }
}

fn threshold_party_seed(
    session: &KeygenSession,
    party: usize,
    params: &BfvParams,
    custody_root: &[u8; 32],
) -> Result<[u8; 32]> {
    if party >= session.n_parties {
        return Err(ThresholdError::InvalidParty {
            party,
            n_parties: session.n_parties,
        });
    }
    let mut hash = Sha256::new();
    hash.update(b"fhegg/threshold-party-custody/v1");
    hash.update(custody_root);
    hash.update((session.n_parties as u64).to_le_bytes());
    hash.update(session.crp_seed);
    hash.update((party as u64).to_le_bytes());
    hash.update((params.degree() as u64).to_le_bytes());
    hash.update(params.plaintext_modulus().to_le_bytes());
    hash.update((params.moduli().len() as u64).to_le_bytes());
    for modulus in params.moduli() {
        hash.update(modulus.to_le_bytes());
    }
    Ok(hash.finalize().into())
}

/// Coordinator state for the public half of n-of-n key generation.
///
/// This type has no method capable of accepting a [`KeyShare`] or [`ThresholdParty`].
pub struct KeygenCoordinator {
    session: KeygenSession,
    params: BfvParams,
    contributions: Vec<PublicKeyContribution>,
}

impl KeygenCoordinator {
    pub fn new(session: KeygenSession, params: BfvParams) -> Self {
        Self {
            session,
            params,
            contributions: Vec::new(),
        }
    }

    /// Accept one public contribution. Duplicate, out-of-session, and out-of-range parties fail.
    pub fn accept(&mut self, contribution: PublicKeyContribution) -> Result<()> {
        if contribution.session != self.session || contribution.party >= self.session.n_parties {
            return Err(ThresholdError::ParamMismatch);
        }
        if self
            .contributions
            .iter()
            .any(|c| c.party == contribution.party)
        {
            return Err(ThresholdError::ParamMismatch);
        }
        self.contributions.push(contribution);
        Ok(())
    }

    /// Finish only after every party contributed exactly once.
    pub fn finish(self) -> Result<CollectivePublicKey> {
        aggregate_public_contributions(&self.session, &self.contributions, &self.params)
    }
}

/// **The collective-key acceptance gate (roadmap Build 5, Tier-0 — the keygen analog of the relin gate).**
///
/// [`KeygenCoordinator::finish`] aggregates the party contributions but verifies only `c1 == CRP` +
/// `level == 0` — NOT the well-formedness of each `c0_i`. A malformed/biased contribution (a large-norm `c0`)
/// therefore silently corrupts the collective key: `finish()` returns `Ok`, and the fault surfaces only as
/// garbage at every encrypt/decrypt under the key, unattributably. This gate catches that fail-closed:
/// `trials` (at least 4) fresh random values are encrypted to the collective key and must decrypt — via the
/// full quorum — back to themselves; a corrupt key yields a mismatch and is refused with
/// [`ThresholdError::AcceptanceFailed`].
///
/// DETECTION under an honest coordinator, NOT attribution — a real Tier-0 stopgap for the keygen
/// malformed-share gap, subsumed once the per-contribution ZK well-formedness proof (roadmap Build 5)
/// attributes a bad share to its party. Adds no new crypto: reuses the collective encrypt + the threshold
/// `partial_decrypt`/`combine`. Fresh per-call randomness so a corrupt key cannot be tuned to pass a fixed
/// vector.
pub fn collective_key_acceptance_gate(
    cpk: &CollectivePublicKey,
    params: &BfvParams,
    parties: &[ThresholdParty],
    trials: usize,
) -> Result<()> {
    use fhe::bfv::Plaintext;
    use fhe_traits::{FheEncoder, FheEncrypter};
    use rand_09::Rng;

    let t = params.plaintext_modulus();
    let mut rng = rand_09::rng();
    for trial in 0..trials.max(4) {
        let m = rng.random_range(0..t.min(1_000_000));
        let pt = Plaintext::try_encode(&[m], Encoding::simd(), params.arc())
            .map_err(|_| ThresholdError::ParamMismatch)?;
        let ct = cpk
            .pk
            .try_encrypt(&pt, &mut rand_09::rng())
            .map_err(|_| ThresholdError::ParamMismatch)?;
        let lean =
            LeanCiphertext::from_fhe_bytes(&ct.to_bytes(), params.moduli(), params.degree(), m)
                .map_err(|_| ThresholdError::MalformedWire)?;
        let shares = parties
            .iter()
            .map(|p| p.partial_decrypt(&lean, MIN_SMUDGE_BITS))
            .collect::<Result<Vec<_>>>()?;
        let opened = combine(&shares, params)?;
        if opened.first().copied() != Some(m) {
            return Err(ThresholdError::AcceptanceFailed { trial });
        }
    }
    Ok(())
}

impl BfvParams {
    /// The pinned fold parameter set (degree-4096, 128-bit HE-standard moduli, t ≈ 2^20) — the
    /// same set `bfv_lean`'s oracle tests assert against.
    pub fn fold_set() -> Self {
        let arc = pick_params(20);
        Self { arc }
    }

    /// Degree-8192 128-bit parameter set for the depth-three distributed
    /// correlation circuit.  The degree-4096 additive-fold set is intentionally
    /// optimized for additions and does not retain enough measured noise
    /// headroom for a full 129-candidate sacrifice row.
    pub fn correlation_set() -> Self {
        let arc = BfvParameters::default_parameters_128(20)
            .expect("128-bit BFV params")
            .nth(3)
            .expect("degree-8192 parameter set");
        Self { arc }
    }

    pub fn is_correlation_set(&self) -> bool {
        let expected = Self::correlation_set();
        self.degree() == expected.degree()
            && self.plaintext_modulus() == expected.plaintext_modulus()
            && self.moduli() == expected.moduli()
    }

    pub fn arc(&self) -> &Arc<BfvParameters> {
        &self.arc
    }
    pub fn degree(&self) -> usize {
        self.arc.degree()
    }
    pub fn moduli(&self) -> &[u64] {
        self.arc.moduli()
    }
    pub fn plaintext_modulus(&self) -> u64 {
        self.arc.plaintext()
    }
}

// ---------------------------------------------------------------------------
// SecretKey construction through fhe.rs's own PUBLIC serialization API
// ---------------------------------------------------------------------------
// fhe.rs's `SecretKey::new` is pub(crate); the PUBLIC way to build a key from chosen coefficients
// is its proto codec: `message SecretKey { repeated sint64 coeffs = 1 }` (zigzag, packed) via
// `DeserializeParametrized::from_bytes`. We encode that message ourselves (same from-scratch
// proto3 discipline as `bfv_lean`).

fn push_varint(out: &mut Vec<u8>, mut v: u64) {
    loop {
        let byte = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            out.push(byte);
            return;
        }
        out.push(byte | 0x80);
    }
}

fn zigzag(v: i64) -> u64 {
    ((v << 1) ^ (v >> 63)) as u64
}

/// Build a real fhe.rs `SecretKey` with the given coefficients, through the public proto codec.
fn sk_from_coeffs(coeffs: &[i64], par: &Arc<BfvParameters>) -> SecretKey {
    let mut payload = Vec::with_capacity(coeffs.len() * 2);
    for &c in coeffs {
        push_varint(&mut payload, zigzag(c));
    }
    let mut bytes = Vec::with_capacity(payload.len() + 4);
    bytes.push(0x0a); // field 1, wire type 2 (packed sint64)
    push_varint(&mut bytes, payload.len() as u64);
    bytes.extend_from_slice(&payload);
    SecretKey::from_bytes(&bytes, par).expect("fhe.rs accepts our packed-sint64 SecretKey proto")
}

// ---------------------------------------------------------------------------
// RNS helpers (same representation bfv_lean owns: power-basis residue rows)
// ---------------------------------------------------------------------------

#[inline]
fn add_mod(a: u64, b: u64, q: u64) -> u64 {
    let s = a + b; // both < q < 2^38: no overflow
    if s >= q {
        s - q
    } else {
        s
    }
}

#[inline]
fn sub_mod(a: u64, b: u64, q: u64) -> u64 {
    if a >= b {
        a - b
    } else {
        a + q - b
    }
}

/// Negacyclic (mod `X^n + 1`) product `s · c` for a TERNARY `s` (coeffs in {-1,0,1}), one RNS row.
/// Multiplication-free: each nonzero `s[a]` adds/subtracts a rotated copy of `c`, with the
/// wrap-around sign flip of the negacyclic ring.
fn ternary_negacyclic_mul(s: &[i64], c: &[u64], q: u64) -> Vec<u64> {
    let n = s.len();
    debug_assert_eq!(n, c.len());
    let mut acc = vec![0u64; n];
    for (a, &sa) in s.iter().enumerate() {
        if sa == 0 {
            continue;
        }
        debug_assert!(sa == 1 || sa == -1, "key share must be ternary");
        let positive = sa == 1;
        for (b, &cb) in c.iter().enumerate() {
            let j = a + b;
            // X^{a+b} = -X^{a+b-n} when a+b >= n
            let (idx, add) = if j < n {
                (j, positive)
            } else {
                (j - n, !positive)
            };
            acc[idx] = if add {
                add_mod(acc[idx], cb, q)
            } else {
                sub_mod(acc[idx], cb, q)
            };
        }
    }
    acc
}

// ---------------------------------------------------------------------------
// the protocol
// ---------------------------------------------------------------------------

/// Extract the single Ciphertext field from fhe.rs's `PublicKey` protobuf.
fn public_key_ciphertext_bytes(public_key_bytes: &[u8]) -> Result<&[u8]> {
    let mut i = 0usize;
    let tag = read_varint(public_key_bytes, &mut i)?;
    if tag != 0x0a {
        return Err(ThresholdError::MalformedWire);
    }
    let len = usize::try_from(read_varint(public_key_bytes, &mut i)?)
        .map_err(|_| ThresholdError::MalformedWire)?;
    let end = i
        .checked_add(len)
        .filter(|&end| end == public_key_bytes.len())
        .ok_or(ThresholdError::MalformedWire)?;
    Ok(&public_key_bytes[i..end])
}

fn read_varint(bytes: &[u8], i: &mut usize) -> Result<u64> {
    let mut value = 0u64;
    let mut shift = 0u32;
    loop {
        let byte = *bytes.get(*i).ok_or(ThresholdError::MalformedWire)?;
        *i += 1;
        if shift >= 64 {
            return Err(ThresholdError::MalformedWire);
        }
        value |= u64::from(byte & 0x7f) << shift;
        if byte & 0x80 == 0 {
            return Ok(value);
        }
        shift += 7;
    }
}

fn public_key_as_lean(public_key_bytes: &[u8], params: &BfvParams) -> Result<LeanCiphertext> {
    // First let fhe.rs validate the outer key and its parameter/context invariants.
    PublicKey::from_bytes(public_key_bytes, params.arc())
        .map_err(|_| ThresholdError::MalformedWire)?;
    let ct_bytes = public_key_ciphertext_bytes(public_key_bytes)?;
    LeanCiphertext::from_fhe_bytes(ct_bytes, params.moduli(), params.degree(), 0)
        .map_err(|_| ThresholdError::MalformedWire)
}

fn wrap_public_key_ciphertext(ciphertext_bytes: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(ciphertext_bytes.len() + 8);
    out.push(0x0a); // PublicKey field 1, length-delimited Ciphertext
    push_varint(&mut out, ciphertext_bytes.len() as u64);
    out.extend_from_slice(ciphertext_bytes);
    out
}

/// Aggregate only public EncKeyGen messages. This reproduces fhe.rs's
/// `Aggregate<PublicKeyShare>`: sum each p0_i while retaining exactly one shared CRP as c1.
fn aggregate_public_contributions(
    session: &KeygenSession,
    contributions: &[PublicKeyContribution],
    params: &BfvParams,
) -> Result<CollectivePublicKey> {
    if contributions.len() < session.n_parties {
        return Err(ThresholdError::QuorumTooSmall {
            have: contributions.len(),
            need: session.n_parties,
        });
    }
    if contributions.len() > session.n_parties {
        return Err(ThresholdError::ParamMismatch);
    }

    let mut parties = contributions.iter().map(|c| c.party).collect::<Vec<_>>();
    parties.sort_unstable();
    parties.dedup();
    if parties != (0..session.n_parties).collect::<Vec<_>>() {
        return Err(ThresholdError::ParamMismatch);
    }

    // Derive the expected public CRP independently. A zero-secret singleton contribution is a
    // convenient public fhe.rs container whose c1 is exactly that CRP; its randomized c0 is
    // discarded. This binds every contribution to the advertised session seed.
    let zero_sk = sk_from_coeffs(&vec![0; params.degree()], params.arc());
    let mut rng = rand_09::rng();
    let expected_share =
        PublicKeyShare::new(&zero_sk, session.common_random_poly(params), &mut rng)
            .expect("zero-secret CRP witness");
    let expected_pk =
        PublicKey::from_shares([expected_share]).expect("zero-secret singleton public key");
    let expected = public_key_as_lean(&expected_pk.to_bytes(), params)?;
    let expected_crp = &expected.polys[1];

    let mut c0 = params
        .moduli()
        .iter()
        .map(|_| vec![0u64; params.degree()])
        .collect::<Vec<_>>();
    for contribution in contributions {
        if contribution.session != *session {
            return Err(ThresholdError::ParamMismatch);
        }
        let share = public_key_as_lean(&contribution.public_key_bytes, params)?;
        if share.level != 0 || share.polys[1] != *expected_crp {
            return Err(ThresholdError::ParamMismatch);
        }
        for (row, (share_row, &q)) in c0
            .iter_mut()
            .zip(share.polys[0].rows.iter().zip(params.moduli().iter()))
        {
            for (coefficient, &share_coefficient) in row.iter_mut().zip(share_row.iter()) {
                *coefficient = add_mod(*coefficient, share_coefficient, q);
            }
        }
    }

    let aggregate = LeanCiphertext {
        moduli: params.moduli().to_vec(),
        degree: params.degree(),
        level: 0,
        variable_time: false,
        polys: vec![RnsPoly { rows: c0 }, expected_crp.clone()],
        plain_bound: 0,
    };
    let public_key_bytes = wrap_public_key_ciphertext(&aggregate.to_fhe_bytes());
    let pk = PublicKey::from_bytes(&public_key_bytes, params.arc())
        .map_err(|_| ThresholdError::MalformedWire)?;
    Ok(CollectivePublicKey { pk })
}

/// Unit-test oracle helper only. Production callers must keep each [`ThresholdParty`] in its own
/// custody domain and pass public contributions through [`KeygenCoordinator`].
#[cfg(test)]
fn collective_keygen_for_test(
    n: usize,
    params: &BfvParams,
) -> (CollectivePublicKey, Vec<KeyShare>) {
    let session = KeygenSession::random(n).expect("test keygen session");
    let mut coordinator = KeygenCoordinator::new(session.clone(), params.clone());
    let mut key_shares = Vec::with_capacity(n);
    for party in 0..n {
        let (party_state, contribution) =
            ThresholdParty::join(&session, party, params).expect("test party joins");
        coordinator.accept(contribution).expect("test contribution");
        key_shares.push(party_state.key_share);
    }
    let cpk = coordinator.finish().expect("test public key aggregation");
    (cpk, key_shares)
}

/// One party's SMUDGED partial decrypt; smudge_bits ≥ the Bfv/Smudging.lean bound or it is unsound.
///
/// Computes `hᵢ = sᵢ·c1 + eᵢ` with `eᵢ` uniform on `[-2^smudge_bits, 2^smudge_bits]` — the SAME
/// integer noise element reduced into every RNS row (one ring element, not per-row noise).
///
/// A sub-bound `smudge_bits` is accepted HERE (a single honest party cannot know what the others
/// sampled) and refused at [`combine`], which is the enforcement point ([`ThresholdError::SmudgeTooSmall`]).
/// Widths whose n-party TOTAL would breach the proven `2^84` decrypt-margin budget
/// (`Bfv.Smudging.deployed_smudged_decrypt_exact`) panic loudly instead of silently mis-clearing.
fn partial_decrypt_inner(share: &KeyShare, ct: &LeanCiphertext, smudge_bits: u32) -> DecryptShare {
    let log2_n = ceil_log2_parties(share.n_parties).expect("key share has nonzero quorum");
    assert!(
        smudge_bits
            .checked_add(log2_n)
            .is_some_and(|total| total <= MAX_SMUDGE_BITS_TOTAL),
        "smudge_bits {smudge_bits} with n={} parties exceeds the proven 2^{MAX_SMUDGE_BITS_TOTAL} \
         total-smudge decrypt-margin budget",
        share.n_parties
    );
    assert_eq!(
        ct.polys.len(),
        2,
        "fold-path ciphertexts have exactly 2 polys"
    );
    assert_eq!(ct.degree, share.coeffs.len(), "degree mismatch");
    assert_eq!(
        ct.moduli.len(),
        ct.polys[1].rows.len(),
        "row/moduli mismatch"
    );

    let mut rng = rand_09::rng();
    // One integer smudge polynomial, coefficients uniform on [-2^b, 2^b].
    let half: u128 = 1u128 << smudge_bits;
    let smudge: Vec<i128> = (0..ct.degree)
        .map(|_| rng.random_range(0..=(half << 1)) as i128 - half as i128)
        .collect();

    let h: Vec<Vec<u64>> = ct
        .moduli
        .iter()
        .enumerate()
        .map(|(i, &q)| {
            let mut row = ternary_negacyclic_mul(&share.coeffs, &ct.polys[1].rows[i], q);
            for (rj, &e) in row.iter_mut().zip(smudge.iter()) {
                let em = e.rem_euclid(q as i128) as u64;
                *rj = add_mod(*rj, em, q);
            }
            row
        })
        .collect();

    DecryptShare {
        h,
        ct: ct.clone(),
        party: share.party,
        n_parties: share.n_parties,
        smudge_bits,
    }
}

/// Combine n partial decrypts → plaintext. Refuses < n shares or param disagreement.
///
/// Returns the full SIMD slot vector (degree entries; callers slice their live prefix).
pub fn combine(shares: &[DecryptShare], params: &BfvParams) -> Result<Vec<u64>> {
    let first = shares
        .first()
        .ok_or(ThresholdError::QuorumTooSmall { have: 0, need: 1 })?;
    let need = first.n_parties;

    // Every share must be over the SAME ciphertext, quorum and parameter set.
    for s in shares {
        if s.n_parties != need
            || s.ct != first.ct
            || s.h.len() != s.ct.moduli.len()
            || s.h
                .iter()
                .zip(s.ct.moduli.iter())
                .any(|(row, &q)| row.len() != s.ct.degree || row.iter().any(|&x| x >= q))
        {
            return Err(ThresholdError::ParamMismatch);
        }
    }
    if first.ct.moduli != params.moduli() || first.ct.degree != params.degree() {
        return Err(ThresholdError::ParamMismatch);
    }
    if shares.len() > need {
        // Extra/duplicate shares would double-count noise masks; refuse rather than guess.
        return Err(ThresholdError::ParamMismatch);
    }
    // n-of-n: every party exactly once.
    let mut parties: Vec<usize> = shares.iter().map(|s| s.party).collect();
    parties.sort_unstable();
    parties.dedup();
    if parties.iter().any(|&p| p >= need) {
        return Err(ThresholdError::ParamMismatch);
    }
    if parties.len() < need {
        return Err(ThresholdError::QuorumTooSmall {
            have: parties.len(),
            need,
        });
    }
    // The no-viewer property is only as strong as the weakest smudge (module doc / Smudging.lean).
    if shares.iter().any(|s| s.smudge_bits < MIN_SMUDGE_BITS) {
        return Err(ThresholdError::SmudgeTooSmall);
    }
    let log2_n = ceil_log2_parties(need).ok_or(ThresholdError::ParamMismatch)?;
    if shares.iter().any(|s| {
        s.smudge_bits
            .checked_add(log2_n)
            .map_or(true, |total| total > MAX_SMUDGE_BITS_TOTAL)
    }) {
        return Err(ThresholdError::SmudgeTooLarge);
    }

    // c0' = c0 + Σ hᵢ (our RNS arithmetic, same add discipline as bfv_lean::fold_add).
    let mut c0 = first.ct.polys[0].rows.clone();
    for s in shares {
        for (row, (hrow, &q)) in c0.iter_mut().zip(s.h.iter().zip(first.ct.moduli.iter())) {
            for (rj, &hj) in row.iter_mut().zip(hrow.iter()) {
                *rj = add_mod(*rj, hj, q);
            }
        }
    }

    // (c0', c1) decrypted under the all-zero key is exactly the tail of fhe.rs mbfv's own
    // Aggregate<DecryptionShare>: phase = c0' + c1·0, then the t/q scale + round. fhe.rs is the
    // authority for that rounding — we hand it our bytes.
    let combined = LeanCiphertext {
        polys: vec![
            RnsPoly { rows: c0 },
            RnsPoly {
                rows: first.ct.polys[1].rows.clone(),
            },
        ],
        ..first.ct.clone()
    };
    let fhe_ct = Ciphertext::from_bytes(&combined.to_fhe_bytes(), params.arc())
        .expect("fhe.rs accepts our re-serialized combined ciphertext");
    let zero_sk = sk_from_coeffs(&vec![0i64; params.degree()], params.arc());
    let pt = zero_sk
        .try_decrypt(&fhe_ct)
        .expect("zero-key scale/round of the combined ciphertext");
    let slots = Vec::<u64>::try_decode(&pt, Encoding::simd_at_level(first.ct.level as usize))
        .expect("simd decode");
    Ok(slots)
}

// ---------------------------------------------------------------------------
// tests — fhe.rs is the ORACLE; nothing here verifies us against ourselves alone
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use fhe::bfv::Plaintext;
    use fhe::mbfv::{AggregateIter, DecryptionShare as MbfvDecryptionShare};
    use fhe_traits::{FheEncoder, FheEncrypter, Serialize as FheSerialize};

    use crate::bfv_lean::fold;

    fn encrypt_slots(
        cpk: &CollectivePublicKey,
        params: &BfvParams,
        slots: &[u64],
        plain_bound: u64,
    ) -> LeanCiphertext {
        let mut rng = rand_09::rng();
        let pt = Plaintext::try_encode(slots, Encoding::simd(), params.arc()).expect("encode");
        let ct = cpk.pk.try_encrypt(&pt, &mut rng).expect("encrypt");
        LeanCiphertext::from_fhe_bytes(
            &ct.to_bytes(),
            params.moduli(),
            params.degree(),
            plain_bound,
        )
        .expect("parse")
    }

    /// The public-message coordinator must be byte-identical to fhe.rs's native
    /// `Aggregate<PublicKeyShare>` over the same shares, not merely self-consistent.
    #[test]
    fn public_contribution_aggregation_matches_native_mbfv() {
        let params = BfvParams::fold_set();
        let session = KeygenSession::from_seed(3, [0x5a; 32]).expect("session");
        let mut rng = rand_09::rng();
        let mut native_shares = Vec::new();
        let mut contributions = Vec::new();

        for party in 0..session.n_parties() {
            let mut coeffs = vec![0i64; params.degree()];
            coeffs[party] = 1;
            coeffs[params.degree() - 1 - party] = -1;
            let sk = sk_from_coeffs(&coeffs, params.arc());
            let share = PublicKeyShare::new(&sk, session.common_random_poly(&params), &mut rng)
                .expect("native public-key share");
            native_shares.push(share.clone());
            let singleton = PublicKey::from_shares([share]).expect("singleton contribution");
            contributions.push(PublicKeyContribution {
                session: session.clone(),
                party,
                public_key_bytes: singleton.to_bytes(),
            });
        }

        let native = PublicKey::from_shares(native_shares).expect("native mbfv aggregate");
        // `PublicKeyShare::new` leaves its internal p0 variable-time flag enabled; the public
        // `PublicKey::from_bytes` boundary (used by the coordinator) deliberately disables it.
        // Normalize the native oracle through that same public boundary before byte comparison.
        let native = PublicKey::from_bytes(&native.to_bytes(), params.arc())
            .expect("native aggregate normalizes through public codec");
        let ours = aggregate_public_contributions(&session, &contributions, &params)
            .expect("public-message aggregate");
        assert_eq!(
            ours.pk.to_bytes(),
            native.to_bytes(),
            "coordinator aggregation must be exactly fhe.rs mbfv aggregation"
        );
    }

    /// Both objects that cross a process boundary have canonical round-tripping codecs, and
    /// malformed/session/duplicate/CRP-confused inputs fail closed.
    #[test]
    fn public_wire_roundtrips_and_keygen_refusals_have_teeth() {
        let params = BfvParams::fold_set();
        let session = KeygenSession::from_seed(2, [7; 32]).expect("session");
        let (party0, contribution0) = ThresholdParty::join(&session, 0, &params).expect("party 0");
        let (_party1, contribution1) = ThresholdParty::join(&session, 1, &params).expect("party 1");

        let contribution_wire = contribution0.to_wire_bytes();
        let contribution0_roundtrip =
            PublicKeyContribution::from_wire_bytes(&contribution_wire).expect("PK wire roundtrip");
        assert_eq!(contribution0_roundtrip, contribution0);
        assert_eq!(
            PublicKeyContribution::from_wire_bytes(
                &contribution_wire[..contribution_wire.len() - 1]
            ),
            Err(ThresholdError::MalformedWire)
        );

        let mut incomplete = KeygenCoordinator::new(session.clone(), params.clone());
        incomplete
            .accept(contribution0.clone())
            .expect("first contribution");
        assert!(matches!(
            incomplete.finish(),
            Err(ThresholdError::QuorumTooSmall { have: 1, need: 2 })
        ));

        let mut duplicate = KeygenCoordinator::new(session.clone(), params.clone());
        duplicate
            .accept(contribution0.clone())
            .expect("first contribution");
        assert_eq!(
            duplicate.accept(contribution0.clone()),
            Err(ThresholdError::ParamMismatch),
            "duplicate party must not count twice"
        );

        let other_session = KeygenSession::from_seed(2, [8; 32]).expect("other session");
        let (_other_party, other_contribution) =
            ThresholdParty::join(&other_session, 1, &params).expect("other-session party");
        let mut session_mismatch = KeygenCoordinator::new(session.clone(), params.clone());
        assert_eq!(
            session_mismatch.accept(other_contribution.clone()),
            Err(ThresholdError::ParamMismatch)
        );

        // Stronger CRP mutation: forge the public envelope's session label to the accepted one,
        // while retaining public-key bytes generated under the other CRP. `accept` can only check
        // metadata; `finish` derives the advertised CRP and refuses the cryptographic mismatch.
        let mut crp_mismatch = KeygenCoordinator::new(session.clone(), params.clone());
        crp_mismatch.accept(contribution0.clone()).expect("party 0");
        crp_mismatch
            .accept(PublicKeyContribution {
                session: session.clone(),
                party: 1,
                public_key_bytes: other_contribution.public_key_bytes,
            })
            .expect("metadata is superficially in-session");
        assert!(matches!(
            crp_mismatch.finish(),
            Err(ThresholdError::ParamMismatch)
        ));

        // Decrypt-share wire roundtrip uses a real secret-dependent message and preserves every
        // public field byte-for-byte. Truncation and non-canonical RNS residues are rejected.
        let cpk =
            aggregate_public_contributions(&session, &[contribution0, contribution1], &params)
                .expect("collective key");
        let ct = encrypt_slots(&cpk, &params, &vec![11; params.degree()], 11);
        let share = party0
            .partial_decrypt(&ct, MIN_SMUDGE_BITS)
            .expect("valid decrypt share");
        let share_wire = share.to_wire_bytes();
        assert_eq!(
            DecryptShare::from_wire_bytes(&share_wire, &params).expect("share wire roundtrip"),
            share
        );
        assert_eq!(
            DecryptShare::from_wire_bytes(&share_wire[..share_wire.len() - 1], &params),
            Err(ThresholdError::MalformedWire)
        );

        let mut noncanonical = share_wire;
        let coefficient_offset = noncanonical.len() - params.moduli().len() * params.degree() * 8;
        noncanonical[coefficient_offset..coefficient_offset + 8]
            .copy_from_slice(&params.moduli()[0].to_le_bytes());
        assert_eq!(
            DecryptShare::from_wire_bytes(&noncanonical, &params),
            Err(ThresholdError::MalformedWire)
        );
    }

    /// Durable custody does not require serializing a raw BFV share: each
    /// party can reconstruct its exact opaque state and public DKG message from
    /// its own secret root after restart, then decrypt under the unchanged
    /// collective key.
    #[test]
    fn seeded_party_restart_reconstructs_collective_key_and_decrypts() {
        let params = BfvParams::fold_set();
        let session = KeygenSession::from_seed(3, [0x73; 32]).expect("public ceremony");
        let roots = [[0xa1; 32], [0xa2; 32], [0xa3; 32]];

        let mut first_parties = Vec::new();
        let mut first_contributions = Vec::new();
        for (party, root) in roots.iter().enumerate() {
            let (state, contribution) = ThresholdParty::join_seeded(&session, party, &params, root)
                .expect("first process joins");
            first_parties.push(state);
            first_contributions.push(contribution);
        }
        let mut first_coordinator = KeygenCoordinator::new(session.clone(), params.clone());
        for contribution in first_contributions.iter().cloned() {
            first_coordinator.accept(contribution).expect("first DKG");
        }
        let first_key = first_coordinator.finish().expect("first collective key");
        drop(first_parties);

        let mut restarted_parties = Vec::new();
        let mut restarted_contributions = Vec::new();
        for (party, root) in roots.iter().enumerate() {
            let (state, contribution) = ThresholdParty::join_seeded(&session, party, &params, root)
                .expect("restarted process joins");
            restarted_parties.push(state);
            restarted_contributions.push(contribution);
        }
        assert_eq!(restarted_contributions, first_contributions);
        let mut restarted_coordinator = KeygenCoordinator::new(session.clone(), params.clone());
        for contribution in restarted_contributions {
            restarted_coordinator
                .accept(contribution)
                .expect("restarted DKG");
        }
        let restarted_key = restarted_coordinator
            .finish()
            .expect("restarted collective key");
        assert_eq!(restarted_key.pk.to_bytes(), first_key.pk.to_bytes());

        let ciphertext = encrypt_slots(&first_key, &params, &vec![42; params.degree()], 42);
        let shares = restarted_parties
            .iter()
            .map(|party| party.partial_decrypt(&ciphertext, MIN_SMUDGE_BITS))
            .collect::<Result<Vec<_>>>()
            .expect("restarted parties produce shares");
        let opening = combine(&shares, &params).expect("restarted quorum opens");
        assert_eq!(opening[0], 42);

        assert!(matches!(
            ThresholdParty::join_seeded(&session, 0, &params, &[0; 32]),
            Err(ThresholdError::InvalidCustodySeed)
        ));
        let (_, other_contribution) =
            ThresholdParty::join_seeded(&session, 0, &params, &[0xb1; 32])
                .expect("different custody root");
        assert_ne!(other_contribution, first_contributions[0]);
    }

    /// Our zigzag/packed-sint64 SecretKey proto must round-trip through fhe.rs's OWN codec:
    /// build from chosen coeffs, serialize with fhe.rs, byte-compare to our encoding.
    #[test]
    fn sk_proto_roundtrips_through_fhe_rs() {
        let params = BfvParams::fold_set();
        let mut coeffs = vec![0i64; params.degree()];
        coeffs[0] = 1;
        coeffs[1] = -1;
        coeffs[7] = 1;
        coeffs[params.degree() - 1] = -1;
        let sk = sk_from_coeffs(&coeffs, params.arc());
        // fhe.rs re-serializes what it decoded from us; prost's packed sint64 encoding must
        // equal ours byte-for-byte (same message, canonical packed encoding).
        let mut ours = Vec::new();
        let mut payload = Vec::new();
        for &c in &coeffs {
            push_varint(&mut payload, zigzag(c));
        }
        ours.push(0x0a);
        push_varint(&mut ours, payload.len() as u64);
        ours.extend_from_slice(&payload);
        assert_eq!(
            sk.to_bytes(),
            ours,
            "prost disagrees with our sint64 packing"
        );
    }

    /// Monomial ground truth for the negacyclic convolution: X^1 · c rotates with the wrap-around
    /// SIGN FLIP; a sign error here is invisible to small-noise decrypts, so pin it directly.
    #[test]
    fn negacyclic_monomial_rotation() {
        let q = crate::bfv_lean::FOLD_MODULI[0];
        let n = 8;
        let c: Vec<u64> = (1..=n as u64).collect();
        // s = X^1
        let mut s = vec![0i64; n];
        s[1] = 1;
        let got = ternary_negacyclic_mul(&s, &c, q);
        let mut want = vec![0u64; n];
        want[0] = q - c[n - 1]; // -c[n-1] wraps negacyclically
        for j in 1..n {
            want[j] = c[j - 1];
        }
        assert_eq!(got, want);
        // s = -1 (constant): negation
        let mut sneg = vec![0i64; n];
        sneg[0] = -1;
        let gotneg = ternary_negacyclic_mul(&sneg, &c, q);
        let wantneg: Vec<u64> = c.iter().map(|&x| q - x).collect();
        assert_eq!(gotneg, wantneg);
    }

    /// THE MAIN TOOTH: n parties collective-keygen (real mbfv), encrypt to the collective key,
    /// fold with bfv_lean, n smudged partial-decrypts, combine == the plaintext sums — pinned
    /// against BOTH fhe.rs oracles: the joint-key decrypt AND fhe.rs mbfv's own DecryptionShare
    /// aggregation over the same key shares. Agreement with a real library cannot be faked.
    #[test]
    fn n_of_n_collective_decrypt_matches_fhe_rs_oracles() {
        let params = BfvParams::fold_set();
        let t = params.plaintext_modulus();
        let n = 3;
        let (cpk, key_shares) = collective_keygen_for_test(n, &params);

        // Three bucket-increment style vectors, folded homomorphically.
        let k = 16;
        let mk = |base: u64| -> Vec<u64> {
            let mut v = vec![0u64; params.degree()];
            for (i, slot) in v.iter_mut().take(k).enumerate() {
                *slot = base + i as u64;
            }
            v
        };
        let (v1, v2, v3) = (mk(10), mk(300), mk(71));
        let cts = [
            encrypt_slots(&cpk, &params, &v1, 10 + k as u64),
            encrypt_slots(&cpk, &params, &v2, 300 + k as u64),
            encrypt_slots(&cpk, &params, &v3, 71 + k as u64),
        ];
        let folded = fold(&cts, t).expect("fold under budget");

        // n smudged partial decrypts + combine.
        let shares: Vec<DecryptShare> = key_shares
            .iter()
            .map(|ks| partial_decrypt_inner(ks, &folded, 80))
            .collect();
        let got = combine(&shares, &params).expect("full quorum combines");
        let expected: Vec<u64> = v1
            .iter()
            .zip(&v2)
            .zip(&v3)
            .map(|((a, b), c)| (a + b + c) % t)
            .collect();
        assert_eq!(&got[..], &expected[..], "combine != plaintext sums");

        // ORACLE 1: the joint key s = Σ sᵢ decrypts the same folded ciphertext to the same slots
        // through fhe.rs's normal single-key decrypt.
        let mut joint = vec![0i64; params.degree()];
        for ks in &key_shares {
            for (j, &c) in ks.coeffs.iter().enumerate() {
                joint[j] += c;
            }
        }
        let joint_sk = sk_from_coeffs(&joint, params.arc());
        let fhe_folded =
            Ciphertext::from_bytes(&folded.to_fhe_bytes(), params.arc()).expect("bytes");
        let pt = joint_sk.try_decrypt(&fhe_folded).expect("joint decrypt");
        let oracle1 = Vec::<u64>::try_decode(&pt, Encoding::simd()).expect("decode");
        assert_eq!(
            &got[..],
            &oracle1[..],
            "combine != fhe.rs joint-key decrypt"
        );

        // ORACLE 2: fhe.rs mbfv's OWN DecryptionShare aggregation over the same key shares.
        let mut rng = rand_09::rng();
        let arc_ct = std::sync::Arc::new(fhe_folded);
        let pt2: Plaintext = key_shares
            .iter()
            .map(|ks| {
                let sk = sk_from_coeffs(&ks.coeffs, params.arc());
                MbfvDecryptionShare::new(&sk, &arc_ct, &mut rng)
            })
            .aggregate()
            .expect("mbfv aggregate");
        let oracle2 = Vec::<u64>::try_decode(&pt2, Encoding::simd()).expect("decode");
        assert_eq!(&got[..], &oracle2[..], "combine != fhe.rs mbfv aggregation");
    }

    /// n-of-n means n: k < n shares REFUSE (and a duplicated share is not a quorum).
    #[test]
    fn quorum_below_n_refused() {
        let params = BfvParams::fold_set();
        let n = 3;
        let (cpk, key_shares) = collective_keygen_for_test(n, &params);
        let ct = encrypt_slots(&cpk, &params, &vec![5u64; params.degree()], 5);
        let shares: Vec<DecryptShare> = key_shares
            .iter()
            .map(|ks| partial_decrypt_inner(ks, &ct, MIN_SMUDGE_BITS))
            .collect();

        assert_eq!(
            combine(&shares[..2], &params),
            Err(ThresholdError::QuorumTooSmall { have: 2, need: 3 })
        );
        assert_eq!(
            combine(&[], &params),
            Err(ThresholdError::QuorumTooSmall { have: 0, need: 1 })
        );
        // A duplicate does not smuggle a quorum: {s0, s0, s1} has 2 distinct parties.
        let dup = vec![shares[0].clone(), shares[0].clone(), shares[1].clone()];
        assert_eq!(
            combine(&dup, &params),
            Err(ThresholdError::QuorumTooSmall { have: 2, need: 3 })
        );
        // And the full quorum still works (the refusals above are not a broken combine).
        assert!(combine(&shares, &params).is_ok());
    }

    /// The Lean-bound enforcement point: any share smudged below MIN_SMUDGE_BITS is refused.
    #[test]
    fn smudge_below_lean_bound_refused() {
        let params = BfvParams::fold_set();
        let (cpk, key_shares) = collective_keygen_for_test(2, &params);
        let ct = encrypt_slots(&cpk, &params, &vec![9u64; params.degree()], 9);
        let mut shares: Vec<DecryptShare> = key_shares
            .iter()
            .map(|ks| partial_decrypt_inner(ks, &ct, MIN_SMUDGE_BITS))
            .collect();
        // One under-smudged share poisons the quorum.
        shares[1] = partial_decrypt_inner(&key_shares[1], &ct, MIN_SMUDGE_BITS - 1);
        assert_eq!(
            combine(&shares, &params),
            Err(ThresholdError::SmudgeTooSmall)
        );
    }

    /// Shares over DIFFERENT ciphertexts never combine.
    #[test]
    fn cross_ciphertext_shares_refused() {
        let params = BfvParams::fold_set();
        let (cpk, key_shares) = collective_keygen_for_test(2, &params);
        let ct_a = encrypt_slots(&cpk, &params, &vec![1u64; params.degree()], 1);
        let ct_b = encrypt_slots(&cpk, &params, &vec![2u64; params.degree()], 2);
        let shares = vec![
            partial_decrypt_inner(&key_shares[0], &ct_a, MIN_SMUDGE_BITS),
            partial_decrypt_inner(&key_shares[1], &ct_b, MIN_SMUDGE_BITS),
        ];
        assert_eq!(
            combine(&shares, &params),
            Err(ThresholdError::ParamMismatch)
        );
    }

    // ------------------------------------------------------------------
    // THE NO-VIEWER STATISTICAL TOOTH
    // ------------------------------------------------------------------
    // The (n-1)-share aggregate c0 + Σ_{i≠j} hᵢ = Δm + e_ct − s_j·c1 + smudges is masked by the
    // MISSING party's RLWE term s_j·c1. Measured claim (each of these CAN fail):
    //   (a) its CRT-reconstructed coefficients are indistinguishable between m = 0 and m = random
    //       (plaintext-independent: nothing about m leaks before the last share), and
    //   (b) indistinguishable between smudge widths 80 and 82 (smudge-independent: the partial
    //       view's shape is the missing mask, not our noise knob), while
    //   (c) the FULL n-share aggregate of m = 0 is grossly DISTINGUISHABLE from any partial one
    //       (coefficients collapse to ±noise around 0 mod q) — the positive control proving the
    //       statistic has teeth: the flip from "uniform garbage" to "structured plaintext"
    //       happens EXACTLY at the n-th share.
    // Statistic: total-variation distance between 16-bin histograms of coeff·16/q over the 4096
    // coefficients. Two independent uniform samples of 4096 over 16 bins sit near TV ≈ 0.04;
    // thresholds 0.15 / 0.5 are far from both sides' expectations.

    /// CRT-combine one coefficient's RNS residues to `x mod q` (q = Πqᵢ ≈ 2^109 fits u128).
    struct Crt {
        q: u128,
        c: Vec<u128>, // c_i = M_i · (M_i^{-1} mod q_i), M_i = q / q_i
    }
    impl Crt {
        fn new(moduli: &[u64]) -> Self {
            let q: u128 = moduli.iter().map(|&m| m as u128).product();
            let c = moduli
                .iter()
                .map(|&m| {
                    let big_m = q / m as u128;
                    let inv = modpow_u64((big_m % m as u128) as u64, m - 2, m); // qᵢ prime
                    (big_m * inv as u128) % q // < 2^109 · 1 before mod: big_m < 2^74, inv < 2^37
                })
                .collect();
            Self { q, c }
        }
        fn combine(&self, residues: &[u64]) -> u128 {
            let mut acc = 0u128;
            for (&r, &c) in residues.iter().zip(self.c.iter()) {
                acc = (acc + mulmod_u128(c, r, self.q)) % self.q;
            }
            acc
        }
    }

    fn modpow_u64(b: u64, mut e: u64, m: u64) -> u64 {
        let mut acc: u128 = 1;
        let mut bb: u128 = b as u128 % m as u128;
        while e > 0 {
            if e & 1 == 1 {
                acc = acc * bb % m as u128;
            }
            bb = bb * bb % m as u128;
            e >>= 1;
        }
        acc as u64
    }

    /// `a·b mod q` for a,q < 2^110, b < 2^64 — shift-add (the 128×64 product overflows u128).
    fn mulmod_u128(mut a: u128, mut b: u64, q: u128) -> u128 {
        let mut acc = 0u128;
        a %= q;
        while b > 0 {
            if b & 1 == 1 {
                acc = (acc + a) % q;
            }
            a = (a + a) % q;
            b >>= 1;
        }
        acc
    }

    /// The aggregate c0 + Σ hᵢ over the given shares, CRT-combined per coefficient.
    fn aggregate_coeffs(shares: &[DecryptShare], crt: &Crt) -> Vec<u128> {
        let ct = &shares[0].ct;
        let nmod = ct.moduli.len();
        let mut rows = ct.polys[0].rows.clone();
        for s in shares {
            for i in 0..nmod {
                let q = ct.moduli[i];
                for (rj, &hj) in rows[i].iter_mut().zip(s.h[i].iter()) {
                    *rj = add_mod(*rj, hj, q);
                }
            }
        }
        (0..ct.degree)
            .map(|j| {
                let residues: Vec<u64> = (0..nmod).map(|i| rows[i][j]).collect();
                crt.combine(&residues)
            })
            .collect()
    }

    fn hist16(coeffs: &[u128], q: u128) -> [f64; 16] {
        let mut h = [0f64; 16];
        for &x in coeffs {
            let bin = ((x * 16) / q).min(15) as usize;
            h[bin] += 1.0;
        }
        let n = coeffs.len() as f64;
        for b in h.iter_mut() {
            *b /= n;
        }
        h
    }

    fn tv(a: &[f64; 16], b: &[f64; 16]) -> f64 {
        0.5 * a
            .iter()
            .zip(b.iter())
            .map(|(x, y)| (x - y).abs())
            .sum::<f64>()
    }

    #[test]
    fn no_viewer_partial_aggregate_is_plaintext_and_smudge_independent() {
        let params = BfvParams::fold_set();
        let t = params.plaintext_modulus();
        let n = 3;
        let (cpk, key_shares) = collective_keygen_for_test(n, &params);
        let crt = Crt::new(params.moduli());
        // CRT sanity pin: a small integer reconstructs to itself.
        {
            let v = 123_456_789u64;
            let residues: Vec<u64> = params.moduli().iter().map(|&m| v % m).collect();
            assert_eq!(crt.combine(&residues), v as u128);
        }

        let mut rng = rand_09::rng();
        let zeros = vec![0u64; params.degree()];
        let randoms: Vec<u64> = (0..params.degree())
            .map(|_| rng.random_range(0..t))
            .collect();
        let ct_zero = encrypt_slots(&cpk, &params, &zeros, 0);
        let ct_rand = encrypt_slots(&cpk, &params, &randoms, t - 1);

        let mk_shares = |ct: &LeanCiphertext, bits: u32| -> Vec<DecryptShare> {
            key_shares
                .iter()
                .map(|ks| partial_decrypt_inner(ks, ct, bits))
                .collect()
        };
        let sh_zero_min = mk_shares(&ct_zero, MIN_SMUDGE_BITS);
        let sh_zero_82 = mk_shares(&ct_zero, 82);
        let sh_rand_min = mk_shares(&ct_rand, MIN_SMUDGE_BITS);

        // Partial (n-1 shares: the coalition's view) vs full (all n).
        let p_zero_min = hist16(&aggregate_coeffs(&sh_zero_min[..n - 1], &crt), crt.q);
        let p_zero_82 = hist16(&aggregate_coeffs(&sh_zero_82[..n - 1], &crt), crt.q);
        let p_rand_min = hist16(&aggregate_coeffs(&sh_rand_min[..n - 1], &crt), crt.q);
        let f_zero_min = hist16(&aggregate_coeffs(&sh_zero_min, &crt), crt.q);

        // (a) plaintext-independence of the coalition view
        let tv_plain = tv(&p_zero_min, &p_rand_min);
        // (b) smudge-independence of the coalition view
        let tv_smudge = tv(&p_zero_min, &p_zero_82);
        // (c) positive control / failing side: the FULL aggregate is structured (m=0 collapses
        //     coefficients to ±total-noise ≈ 2^82 around 0 mod q ≈ 2^109: bins 0/15 only).
        let tv_full = tv(&f_zero_min, &p_zero_min);

        assert!(
            tv_plain < 0.15,
            "coalition view leaks the plaintext: TV(m=0, m=rand) = {tv_plain}"
        );
        assert!(
            tv_smudge < 0.15,
            "coalition view depends on the smudge width: TV(b=80, b=82) = {tv_smudge}"
        );
        assert!(
            tv_full > 0.5,
            "positive control FAILED — the statistic cannot even see the full-aggregate structure \
             (TV = {tv_full}); the two small-TV assertions above would be vacuous"
        );
        // And the structured full aggregate really is the plaintext: same shares combine to m.
        let got = combine(&sh_zero_min, &params).expect("combine");
        assert_eq!(&got[..], &zeros[..]);
    }
}
