//! The Dark Pool — an AMM `x·y=k` with HIDDEN reserves (THE-DARK-BAZAAR.md, the walk stone).
//!
//! Hidden reserves need a product of two SECRETS, so this rides ct×ct multiply (`crate::bfv_mul`, oracle-
//! anchored to fhe.rs Multiplicator). OWNED by the `dark-amm` lane. Signatures frozen here; implement bodies.
//!
//! # What this stone IS (scoped honestly)
//!
//! **Verify-not-find.** Under FHE nobody can *compute* the swap output `dy = ⌊y·dx/(x+dx)⌋` from the
//! encrypted reserves — that is a division by an encrypted quantity, a deep circuit far past the depth-1
//! budget. But the constant-product invariant is *verifiable* with exactly ONE ct×ct multiply:
//!
//! ```text
//!   Enc(x) --(+ dx, plaintext add, EXACT)--> Enc(x+dx)   ┐
//!                                                        ├── bfv_mul ──> Enc((x+dx)·(y−dy))
//!   Enc(y) --(− dy, plaintext sub, EXACT)--> Enc(y−dy)   ┘
//! ```
//!
//! and the privacy boundary decides only whether that product equals the public invariant target `k`.
//! The preferred path masks the decrypt into party-local mod-`t` shares and uses
//! [`crate::mpc_party::PartyMpcSession::equality`]; the legacy oracle path can still open the product
//! directly for differential tests. So the roles are:
//!
//! * the **LP** (pool creator) initialized the reserves, so it legitimately knows them and — because
//!   `dx`/`dy` are public in this first stone — can track them and QUOTE `dy` (the "finder");
//! * the **house** holds only ciphertexts + the public `k` and ENFORCES the invariant homomorphically
//!   (the "verifier") — it can never see the reserves it is enforcing the curve on;
//! * the **privacy boundary** threshold-masks the single invariant product into party shares, then MPC
//!   reveals one pass/fail bit. [`DarkPool::commit_private_decision`] consumes that candidate-bound bit;
//!   neither a successful nor refused call receives the product.
//!
//! Reserve ciphertexts are only ever touched by PLAINTEXT ops (`ct ± Plaintext` — exact in BFV, zero
//! noise growth), so repeated swaps do NOT accumulate noise on the pool state; the ct×ct product is a
//! per-swap ephemeral. The 3-swap chain test validates this by execution.
//!
//! A restarted house can reconstruct that evaluation state from
//! [`DarkPoolPublicHostMaterial`] without possessing a BFV secret key.  The
//! carrier authenticates neither its storage origin nor the claim that the
//! initial ciphertext openings multiply to `k`: a deployment must bind the
//! first accepted carrier to trusted pool-creation evidence and protect later
//! carriers against rollback. Candidate evaluation remains separate from the
//! collective final equality/decryption decision.
//!
//! # What stays OUT OF SCOPE (named, not hidden)
//!
//! * **Private `dx` / `dy` are now executable** through
//!   [`DarkPool::try_private_swap_proposed`]: the house adds/subtracts encrypted
//!   trade amounts and opens only the invariant product.  The older public-quote
//!   API remains for differential testing and LP-operated pools.  The private
//!   path is still not a complete user-balance protocol: its declared amount
//!   bounds need ingest range proofs, and a liquidity provider must produce the
//!   quote outside this verifier without disclosing it to the house.
//! * **Floor-division swaps.** Acceptance here is EXACT: the product must decrypt to exactly `k`, so
//!   only swaps where `(x+dx) | y·dx` are accepted (`NoExactQuote` otherwise). Generic floor swaps
//!   satisfy `k ≤ (x+dx)(y−dy) < k + (x+dx)`, and checking that upper bound against an ENCRYPTED
//!   `x+dx` is a homomorphic comparison this stone does not have (the MPC-boundary machinery).
//! * **The mod-t forgery margin.** Acceptance is equality mod t. An adversary who already KNOWS the
//!   reserves may be able to craft a wrapped `dy` whose junk product lands on `k mod t`; a blind
//!   adversary hits a ~1/t window. Range proofs at ingest remain required. The new masked party-MPC
//!   decision closes raw-residue disclosure in the semi-honest protocol; the older scalar-injection
//!   `commit_private` API remains as a differential oracle and does reveal `P` on refusal.
//! * **Noise-budget proof.** The single multiply rides `bfv_mul`'s measured budget
//!   (`noise_growth_measured`) and the Lean bound (`metatheory/Bfv/Mul.lean`); no new Lean here.
//! * **Threshold relin-key generation.** The legacy n-of-n collective path now runs fhe.rs's two-round
//!   multiparty protocol in [`crate::threshold::relin`] over the exact party-owned key shares, so no
//!   assembled secret key is needed to generate the Dark AMM's `RelinearizationKey`. It remains an
//!   honest, in-memory, unauthenticated n-of-n ceremony: malicious-share proofs, persistence, and a
//!   dropout-tolerant `t<n` relin protocol are still open.
//! * **Scale.** The wrap guard demands `bound_x'·bound_y' < t ≈ 2^20`, so reserves live in a small
//!   universe (≲1015·1015). Bigger pools need a larger t or CRT limbs. Also: declared caps are PUBLIC
//!   — an LP must declare loose caps, not the exact reserves.
//! * **Fees / slippage curve** — none; pure constant-product.

use std::fmt;
use std::sync::Arc;

use fhe::bfv::{BfvParameters, Ciphertext, Encoding, Plaintext, PublicKey, RelinearizationKey};
use fhe_traits::{DeserializeParametrized, FheEncoder, FheEncrypter, Serialize as FheSerialize};
use sha2::{Digest, Sha256};

use crate::bfv_mul::{BfvMulError, BoundedCiphertext, MulEngine};
use crate::mpc_party::DistributedDecisionRun;

const PUBLIC_HOST_MAGIC: &[u8; 8] = b"FHDAP002";
const PUBLIC_HOST_CHECKSUM_DOMAIN: &[u8] = b"fhegg/dark-amm/public-host-material/v2";
const PUBLIC_HOST_PARAMETER_DOMAIN: &[u8] = b"fhegg/dark-amm/public-host-parameters/v2";
const PRIVATE_DECISION_CARRIER_MAGIC: &[u8; 8] = b"FHDPW001";
const PRIVATE_DECISION_CARRIER_CHECKSUM_DOMAIN: &[u8] =
    b"fhegg/dark-amm/private-decision-carrier/v1";
const MAX_PUBLIC_KEY_BYTES: usize = 16 * 1024 * 1024;
const MAX_RELINEARIZATION_KEY_BYTES: usize = 192 * 1024 * 1024;
const MAX_POOL_CIPHERTEXT_BYTES: usize = 16 * 1024 * 1024;
/// Fixed allocation ceiling for the complete public-only restart carrier.
pub const MAX_DARK_AMM_PUBLIC_HOST_MATERIAL_BYTES: usize = 224 * 1024 * 1024;
/// Allocation ceiling for the invariant plus exact encrypted post-state handed
/// from a secretless table to an independent collective decision worker.
pub const MAX_PRIVATE_DECISION_CARRIER_BYTES: usize = 3 * MAX_POOL_CIPHERTEXT_BYTES + 1024;

/// Errors — every refusal is loud and NAMES what was refused.
#[derive(Debug)]
pub enum DarkAmmError {
    /// A zero dx (or a quoted zero dy) is not a swap.
    ZeroAmount,
    /// This pool object has no LP view (house-side copy) — it can VERIFY a
    /// proposed swap but cannot QUOTE one. Use `try_swap_proposed`.
    QuoteUnavailable,
    /// The constant-product quote for this dx is not exact: `(x+dx) ∤ y·dx`.
    /// Floor swaps are the named out-of-scope; the floor quote and remainder
    /// are reported so the refusal is informative.
    NoExactQuote {
        dx: u64,
        dy_floor: u64,
        remainder: u64,
    },
    /// The proposed dy exceeds the pool's PUBLIC reserve cap — refused before
    /// touching any ciphertext.
    DyExceedsCap { dy: u64, cap_y: u64 },
    /// A bound/cap computation left the plaintext domain (≥ t or u64 overflow).
    CapOverflow { detail: &'static str },
    /// Pool construction rejected.
    InvalidInit { reason: &'static str },
    /// The wrapped `bfv_mul` engine refused (wrap guard) or fhe.rs failed.
    Mul(BfvMulError),
    /// The decrypt boundary opened the invariant product and it was NOT k:
    /// the proposed swap does not lie on the constant-product curve.
    InvariantViolated { decrypted: u64, k: u64 },
    /// The masked MPC boundary returned only `false`; no rejected invariant
    /// residue is surfaced in this error.
    InvariantDecisionRefused,
    /// A valid decision for another candidate/session cannot authorize this
    /// state transition.
    InvariantDecisionContextMismatch,
    /// The frozen `swap()` entry point was handed a plaintext modulus that is
    /// not the engine's.
    ParamMismatch { expected_t: u64, got_t: u64 },
    /// A private-amount commit would make the LP's local plaintext quote view
    /// stale. Private swaps are therefore admitted only by a stripped
    /// house-side verifier, which never retained the reserves.
    PrivateSwapRequiresHouseView,
    /// A fhe.rs encode operation failed (its error text carried through).
    Fhe(String),
    /// A public-only restart carrier was malformed, non-canonical, or publicly
    /// inconsistent. No secret-key check is implied by this refusal.
    MalformedPublicHostMaterial { reason: String },
    /// The carrier names a different BFV parameter identity than the exact
    /// parameter handle supplied by the restoring process.
    PublicHostParameterMismatch,
}

impl fmt::Display for DarkAmmError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ZeroAmount => write!(f, "zero-amount swap refused"),
            Self::QuoteUnavailable => write!(
                f,
                "no LP view on this pool object: it can verify a proposed swap, not quote one"
            ),
            Self::NoExactQuote {
                dx,
                dy_floor,
                remainder,
            } => write!(
                f,
                "no exact constant-product quote for dx={dx}: floor dy={dy_floor} leaves remainder \
                 {remainder}; floor swaps are out of scope for the exact-acceptance stone"
            ),
            Self::DyExceedsCap { dy, cap_y } => {
                write!(f, "proposed dy={dy} exceeds the public reserve cap {cap_y}")
            }
            Self::CapOverflow { detail } => write!(f, "cap arithmetic left the domain: {detail}"),
            Self::InvalidInit { reason } => write!(f, "pool init refused: {reason}"),
            Self::Mul(e) => write!(f, "ct×ct multiply refused/failed: {e}"),
            Self::InvariantViolated { decrypted, k } => write!(
                f,
                "invariant violated: (x+dx)·(y−dy) decrypted to {decrypted}, expected k={k}; \
                 swap refused"
            ),
            Self::InvariantDecisionRefused => {
                write!(f, "private invariant decision refused; swap held")
            }
            Self::InvariantDecisionContextMismatch => write!(
                f,
                "private invariant decision is bound to another candidate/session"
            ),
            Self::ParamMismatch { expected_t, got_t } => write!(
                f,
                "plaintext modulus mismatch: engine t={expected_t}, caller passed t={got_t}"
            ),
            Self::PrivateSwapRequiresHouseView => write!(
                f,
                "private-amount swap requires a house-side pool with no plaintext LP view"
            ),
            Self::Fhe(e) => write!(f, "fhe.rs operation failed: {e}"),
            Self::MalformedPublicHostMaterial { reason } => {
                write!(f, "malformed Dark AMM public host material: {reason}")
            }
            Self::PublicHostParameterMismatch => write!(
                f,
                "Dark AMM public host material belongs to a different BFV parameter set"
            ),
        }
    }
}

impl std::error::Error for DarkAmmError {}

impl From<BfvMulError> for DarkAmmError {
    fn from(e: BfvMulError) -> Self {
        Self::Mul(e)
    }
}

/// The PLAINTEXT constant-product AMM — the differential oracle AND the LP's
/// quoting view. Deliberately boring: this is the cleartext truth the FHE path
/// must match exactly.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PlainAmm {
    pub x: u64,
    pub y: u64,
    pub k: u64,
}

impl PlainAmm {
    pub fn new(x0: u64, y0: u64) -> Self {
        Self {
            x: x0,
            y: y0,
            k: x0 * y0,
        }
    }

    /// The canonical floor quote: `dy = ⌊y·dx/(x+dx)⌋` and the division
    /// remainder `r = y·dx − dy·(x+dx)`, so `(x+dx)(y−dy) = k + r`.
    pub fn quote_floor(&self, dx: u64) -> (u64, u64) {
        let num = (self.y as u128) * (dx as u128);
        let den = (self.x as u128) + (dx as u128);
        let dy = num / den;
        let r = num % den;
        (dy as u64, r as u64)
    }

    /// The exact quote: `Some(dy)` iff the floor quote has remainder 0, i.e.
    /// the post-swap product is EXACTLY k.
    pub fn quote_exact(&self, dx: u64) -> Option<u64> {
        let (dy, r) = self.quote_floor(dx);
        (r == 0 && dy > 0).then_some(dy)
    }

    /// Apply a swap to the plaintext view.
    pub fn apply(&mut self, dx: u64, dy: u64) {
        self.x += dx;
        self.y -= dy;
    }
}

/// The house-visible encrypted pool state: two `BoundedCiphertext` reserves.
/// Bounds are PUBLIC declared caps (loose, never the exact reserves).
#[derive(Clone, Debug)]
pub struct PoolCiphertexts {
    pub ct_x: BoundedCiphertext,
    pub ct_y: BoundedCiphertext,
}

/// Canonical public-only restart material for one encrypted Dark AMM host.
///
/// It contains the collective public key, public relinearization key, public
/// invariant/caps, and the two reserve ciphertexts. It contains no
/// [`fhe::bfv::SecretKey`], decryption share, reserve opening, amount opening,
/// or equality result. Restoring this value enables homomorphic candidate
/// construction only; a separate collective boundary must still decide the
/// candidate invariant before commit.
#[derive(Clone, PartialEq, Eq)]
pub struct DarkPoolPublicHostMaterial {
    degree: u64,
    modulus_count: u64,
    plaintext_modulus: u64,
    parameter_digest: [u8; 32],
    k: u64,
    cap_x: u64,
    cap_y: u64,
    public_key_bytes: Vec<u8>,
    relinearization_key_bytes: Vec<u8>,
    ct_x_bytes: Vec<u8>,
    ct_y_bytes: Vec<u8>,
}

impl fmt::Debug for DarkPoolPublicHostMaterial {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("DarkPoolPublicHostMaterial")
            .field("degree", &self.degree)
            .field("modulus_count", &self.modulus_count)
            .field("plaintext_modulus", &self.plaintext_modulus)
            .field("k", &self.k)
            .field("cap_x", &self.cap_x)
            .field("cap_y", &self.cap_y)
            .field("public_key_bytes", &self.public_key_bytes.len())
            .field(
                "relinearization_key_bytes",
                &self.relinearization_key_bytes.len(),
            )
            .field("ct_x_bytes", &self.ct_x_bytes.len())
            .field("ct_y_bytes", &self.ct_y_bytes.len())
            .finish()
    }
}

impl DarkPoolPublicHostMaterial {
    /// Construct and validate a public-only carrier from live public objects.
    /// All objects are re-decoded against `params` before this succeeds, so a
    /// caller cannot smuggle an object tied to another fhe.rs parameter Arc.
    pub fn try_new(
        params: &Arc<BfvParameters>,
        public_key: &PublicKey,
        relinearization_key: &RelinearizationKey,
        k: u64,
        state: &PoolCiphertexts,
    ) -> Result<Self, DarkAmmError> {
        let material = Self {
            degree: params.degree() as u64,
            modulus_count: params.moduli().len() as u64,
            plaintext_modulus: params.plaintext(),
            parameter_digest: public_host_parameter_digest(params),
            k,
            cap_x: state.ct_x.plain_bound,
            cap_y: state.ct_y.plain_bound,
            public_key_bytes: public_key.to_bytes(),
            relinearization_key_bytes: relinearization_key.to_bytes(),
            ct_x_bytes: state.ct_x.ct.to_bytes(),
            ct_y_bytes: state.ct_y.ct.to_bytes(),
        };
        material.decode_public_objects(params)?;
        if material.to_wire_bytes().len() > MAX_DARK_AMM_PUBLIC_HOST_MATERIAL_BYTES {
            return Err(malformed_public_host(
                "encoded material exceeds the fixed allocation ceiling",
            ));
        }
        Ok(material)
    }

    pub const fn k(&self) -> u64 {
        self.k
    }

    pub const fn cap_x(&self) -> u64 {
        self.cap_x
    }

    pub const fn cap_y(&self) -> u64 {
        self.cap_y
    }

    pub const fn parameter_digest(&self) -> [u8; 32] {
        self.parameter_digest
    }

    /// Canonical collective public-key encoding carried by this validated
    /// material.  Exposing the public object bytes avoids downstream protocols
    /// re-parsing version-specific carrier offsets to bind their custody policy.
    pub fn public_key_bytes(&self) -> &[u8] {
        &self.public_key_bytes
    }

    /// Canonical public relinearization-key encoding carried by this validated
    /// material.  Like [`public_key_bytes`](Self::public_key_bytes), this is
    /// public protocol identity, never secret key material.
    pub fn relinearization_key_bytes(&self) -> &[u8] {
        &self.relinearization_key_bytes
    }

    /// Digest of the complete canonical public carrier, useful as a storage or
    /// protocol binding. It is not a proof that the ciphertexts encrypt an
    /// initial state whose product is `k`.
    pub fn material_digest(&self) -> [u8; 32] {
        let wire = self.to_wire_bytes();
        let mut hash = Sha256::new();
        hash.update(b"fhegg/dark-amm/public-host-material-digest/v2");
        hash.update((wire.len() as u64).to_le_bytes());
        hash.update(wire);
        hash.finalize().into()
    }

    /// Strict bounded public wire. The trailing checksum detects corruption;
    /// it is public and provides no rollback or authenticity guarantee.
    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(
            128 + self.public_key_bytes.len()
                + self.relinearization_key_bytes.len()
                + self.ct_x_bytes.len()
                + self.ct_y_bytes.len(),
        );
        out.extend_from_slice(PUBLIC_HOST_MAGIC);
        put_public_host_u64(&mut out, self.degree);
        put_public_host_u64(&mut out, self.modulus_count);
        put_public_host_u64(&mut out, self.plaintext_modulus);
        out.extend_from_slice(&self.parameter_digest);
        put_public_host_u64(&mut out, self.k);
        put_public_host_u64(&mut out, self.cap_x);
        put_public_host_u64(&mut out, self.cap_y);
        put_public_host_bytes(&mut out, &self.public_key_bytes);
        put_public_host_bytes(&mut out, &self.relinearization_key_bytes);
        put_public_host_bytes(&mut out, &self.ct_x_bytes);
        put_public_host_bytes(&mut out, &self.ct_y_bytes);
        let checksum = public_host_checksum(&out);
        out.extend_from_slice(&checksum);
        out
    }

    /// Parse, dimension-check, and canonically re-decode every fhe.rs public
    /// object under the caller's exact parameter handle.
    pub fn from_wire_bytes(
        bytes: &[u8],
        params: &Arc<BfvParameters>,
    ) -> Result<Self, DarkAmmError> {
        if bytes.len() > MAX_DARK_AMM_PUBLIC_HOST_MATERIAL_BYTES {
            return Err(malformed_public_host(format!(
                "wire is {} bytes; maximum is {MAX_DARK_AMM_PUBLIC_HOST_MATERIAL_BYTES}",
                bytes.len()
            )));
        }
        if bytes.len() < 8 + 6 * 8 + 32 + 4 * 8 + 32 {
            return Err(malformed_public_host("truncated fixed header"));
        }
        let content_end = bytes.len() - 32;
        let expected = public_host_checksum(&bytes[..content_end]);
        if bytes[content_end..] != expected {
            return Err(malformed_public_host("checksum mismatch"));
        }
        let mut input = PublicHostReader::new(&bytes[..content_end]);
        if input.array::<8>()? != *PUBLIC_HOST_MAGIC {
            return Err(malformed_public_host("wrong version magic"));
        }
        let material = Self {
            degree: input.u64()?,
            modulus_count: input.u64()?,
            plaintext_modulus: input.u64()?,
            parameter_digest: input.array()?,
            k: input.u64()?,
            cap_x: input.u64()?,
            cap_y: input.u64()?,
            public_key_bytes: input.bytes(MAX_PUBLIC_KEY_BYTES)?.to_vec(),
            relinearization_key_bytes: input.bytes(MAX_RELINEARIZATION_KEY_BYTES)?.to_vec(),
            ct_x_bytes: input.bytes(MAX_POOL_CIPHERTEXT_BYTES)?.to_vec(),
            ct_y_bytes: input.bytes(MAX_POOL_CIPHERTEXT_BYTES)?.to_vec(),
        };
        input.finish()?;
        material.decode_public_objects(params)?;
        if material.to_wire_bytes() != bytes {
            return Err(malformed_public_host("wire is not canonical"));
        }
        Ok(material)
    }

    fn decode_public_objects(
        &self,
        params: &Arc<BfvParameters>,
    ) -> Result<(PublicKey, RelinearizationKey, PoolCiphertexts), DarkAmmError> {
        if self.degree != params.degree() as u64
            || self.modulus_count != params.moduli().len() as u64
            || self.plaintext_modulus != params.plaintext()
            || self.parameter_digest != public_host_parameter_digest(params)
        {
            return Err(DarkAmmError::PublicHostParameterMismatch);
        }
        validate_public_host_caps(self.k, self.cap_x, self.cap_y, self.plaintext_modulus)?;

        let public_key = PublicKey::from_bytes(&self.public_key_bytes, params)
            .map_err(|error| malformed_public_host(format!("public key decode failed: {error}")))?;
        let relinearization_key =
            RelinearizationKey::from_bytes(&self.relinearization_key_bytes, params).map_err(
                |error| {
                    malformed_public_host(format!("relinearization key decode failed: {error}"))
                },
            )?;
        let ct_x = Ciphertext::from_bytes(&self.ct_x_bytes, params).map_err(|error| {
            malformed_public_host(format!("reserve-x ciphertext decode failed: {error}"))
        })?;
        let ct_y = Ciphertext::from_bytes(&self.ct_y_bytes, params).map_err(|error| {
            malformed_public_host(format!("reserve-y ciphertext decode failed: {error}"))
        })?;
        if public_key.to_bytes() != self.public_key_bytes
            || relinearization_key.to_bytes() != self.relinearization_key_bytes
            || ct_x.to_bytes() != self.ct_x_bytes
            || ct_y.to_bytes() != self.ct_y_bytes
        {
            return Err(malformed_public_host(
                "one or more fhe.rs public objects are not canonically encoded",
            ));
        }
        // This validates that the relinearization key has the required public
        // shape for the pinned parameter set. Without a decryption/proof
        // boundary it cannot prove that pk, rk, and reserve ciphertexts share
        // one secret-key domain; that trust seam is documented explicitly.
        MulEngine::new(&relinearization_key, params)?;
        Ok((
            public_key,
            relinearization_key,
            PoolCiphertexts {
                ct_x: BoundedCiphertext::new(ct_x, self.cap_x),
                ct_y: BoundedCiphertext::new(ct_y, self.cap_y),
            },
        ))
    }
}

fn validate_public_host_caps(
    k: u64,
    cap_x: u64,
    cap_y: u64,
    plaintext_modulus: u64,
) -> Result<(), DarkAmmError> {
    if k == 0 || cap_x == 0 || cap_y == 0 {
        return Err(malformed_public_host(
            "k and both public caps must be nonzero",
        ));
    }
    if cap_x >= plaintext_modulus || cap_y >= plaintext_modulus {
        return Err(malformed_public_host(
            "a public reserve cap leaves the BFV plaintext domain",
        ));
    }
    let cap_product = (cap_x as u128) * (cap_y as u128);
    if cap_product >= plaintext_modulus as u128 {
        return Err(malformed_public_host(
            "cap_x*cap_y reaches the BFV plaintext modulus",
        ));
    }
    if k as u128 > cap_product {
        return Err(malformed_public_host(
            "public k exceeds the product of declared reserve caps",
        ));
    }
    Ok(())
}

/// A pool with encrypted reserves (x, y) and the public invariant target k = x·y.
pub struct DarkPool {
    params: Arc<BfvParameters>,
    public_key: PublicKey,
    relinearization_key: RelinearizationKey,
    engine: MulEngine,
    state: PoolCiphertexts,
    /// The public constant-product target. Public by design: acceptance is
    /// "the product ciphertext decrypts to exactly this".
    pub k: u64,
    /// The LP's plaintext tracking view (quoting leg). `None` on a house-side
    /// object: the house can verify, never quote — and never sees reserves.
    lp_view: Option<PlainAmm>,
}

impl fmt::Debug for DarkPool {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // MulEngine (fhe.rs Multiplicator) has no Debug; print the public face.
        f.debug_struct("DarkPool")
            .field("k", &self.k)
            .field("cap_x", &self.state.ct_x.plain_bound)
            .field("cap_y", &self.state.ct_y.plain_bound)
            .field("has_lp_view", &self.lp_view.is_some())
            .finish_non_exhaustive()
    }
}

/// A swap: dx in of asset X, dy out of asset Y, priced by the invariant on ENCRYPTED reserves.
/// `outcome` is `Ok(AppliedSwap)` — the candidate post-state plus the encrypted invariant product
/// the decrypt boundary must check — or the loud, named refusal.
pub struct SwapResult {
    pub outcome: Result<AppliedSwap, DarkAmmError>,
}

/// A verified-shape swap candidate. NOT yet committed: the decrypt boundary
/// must open `invariant` and see exactly `k` (`check_invariant`), then the
/// pool owner calls `DarkPool::commit`.
#[derive(Debug)]
pub struct AppliedSwap {
    pub dx: u64,
    pub dy: u64,
    /// The public invariant target the product must decrypt to.
    pub k: u64,
    /// Enc((x+dx)·(y−dy)) — the ct×ct product (relinearized, wrap-guarded).
    /// This is the ONLY ciphertext the decrypt boundary opens.
    pub invariant: BoundedCiphertext,
    /// Candidate post-swap encrypted reserves (plaintext-op descendants of the
    /// current state; committed only after the invariant check passes).
    pub state_after: PoolCiphertexts,
}

/// Candidate private-amount state transition.  Unlike [`AppliedSwap`], this
/// object contains no plaintext `dx` or `dy`; even its `Debug` surface exposes
/// only public caps and the already-public invariant target.
pub struct PrivateAppliedSwap {
    /// Enc((x+dx)·(y−dy)); an honest transition opens to the public `k`.
    pub invariant: BoundedCiphertext,
    /// Candidate encrypted reserve state, committed only after the invariant
    /// boundary accepts.
    state_after: PoolCiphertexts,
    k: u64,
    /// Exact encrypted pre-state this proposal was evaluated from. This keeps
    /// a later valid decision from installing a stale candidate after the pool
    /// has already advanced.
    state_before_digest: [u8; 32],
}

impl fmt::Debug for PrivateAppliedSwap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PrivateAppliedSwap")
            .field("k", &self.k)
            .field("cap_x_after", &self.state_after.ct_x.plain_bound)
            .field("cap_y_after", &self.state_after.ct_y.plain_bound)
            .finish_non_exhaustive()
    }
}

impl PrivateAppliedSwap {
    pub fn check_invariant(&self, decrypted_slot0: u64) -> Result<(), DarkAmmError> {
        if decrypted_slot0 != self.k {
            return Err(DarkAmmError::InvariantViolated {
                decrypted: decrypted_slot0,
                k: self.k,
            });
        }
        Ok(())
    }

    /// Public routing nonce for the masked-decrypt → party-MPC equality round.
    /// It commits the exact pre-state, invariant ciphertext, and candidate
    /// post-state, so a one-bit decision from another proposal or pool revision
    /// cannot be replayed here.
    pub fn decision_session_nonce(&self) -> [u8; 32] {
        let invariant = self.invariant.ct.to_bytes();
        let state_x = self.state_after.ct_x.ct.to_bytes();
        let state_y = self.state_after.ct_y.ct.to_bytes();
        private_candidate_nonce_from_parts(
            self.k,
            self.state_before_digest,
            [
                (self.invariant.plain_bound, &invariant),
                (self.state_after.ct_x.plain_bound, &state_x),
                (self.state_after.ct_y.plain_bound, &state_y),
            ],
        )
    }

    /// Construct the exact public carrier an out-of-process custodian needs.
    /// The supplied committed material is independently decoded and must be
    /// the candidate's actual encrypted pre-state.
    pub fn public_decision_carrier(
        &self,
        params: &Arc<BfvParameters>,
        committed_material: &DarkPoolPublicHostMaterial,
    ) -> Result<PrivateAppliedSwapDecisionCarrier, PrivateDecisionCarrierError> {
        PrivateAppliedSwapDecisionCarrier::from_candidate(params, committed_material, self)
    }
}

/// Strict transport failures for one encrypted private-swap candidate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrivateDecisionCarrierError {
    TooLarge,
    InvalidWire(String),
    ParameterMismatch,
    CommittedPreStateMismatch,
}

impl fmt::Display for PrivateDecisionCarrierError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TooLarge => write!(f, "private decision carrier exceeds its allocation limit"),
            Self::InvalidWire(reason) => {
                write!(f, "invalid private decision carrier: {reason}")
            }
            Self::ParameterMismatch => {
                write!(
                    f,
                    "private decision carrier belongs to different BFV parameters"
                )
            }
            Self::CommittedPreStateMismatch => write!(
                f,
                "private decision carrier does not descend from the committed public material"
            ),
        }
    }
}

impl std::error::Error for PrivateDecisionCarrierError {}

/// Complete public encrypted candidate handed to a collective decision worker.
///
/// This type deliberately cannot be converted into [`PrivateAppliedSwap`]. A
/// host must reconstruct its own candidate from the proved encrypted request;
/// otherwise a caller could pair `Enc(k)` with an unrelated post-state. The
/// carrier exists only so custodians can verify the candidate nonce and decide
/// its exact invariant ciphertext.
#[derive(Clone, PartialEq, Eq)]
pub struct PrivateAppliedSwapDecisionCarrier {
    degree: u64,
    modulus_count: u64,
    plaintext_modulus: u64,
    parameter_digest: [u8; 32],
    k: u64,
    state_before_digest: [u8; 32],
    invariant_bound: u64,
    invariant_bytes: Vec<u8>,
    state_x_bound: u64,
    state_x_bytes: Vec<u8>,
    state_y_bound: u64,
    state_y_bytes: Vec<u8>,
    candidate_nonce: [u8; 32],
}

impl fmt::Debug for PrivateAppliedSwapDecisionCarrier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PrivateAppliedSwapDecisionCarrier")
            .field("k", &self.k)
            .field("invariant_bound", &self.invariant_bound)
            .field("invariant_bytes", &self.invariant_bytes.len())
            .field("state_x_bound", &self.state_x_bound)
            .field("state_x_bytes", &self.state_x_bytes.len())
            .field("state_y_bound", &self.state_y_bound)
            .field("state_y_bytes", &self.state_y_bytes.len())
            .field("candidate_nonce", &self.candidate_nonce)
            .finish()
    }
}

impl PrivateAppliedSwapDecisionCarrier {
    fn from_candidate(
        params: &Arc<BfvParameters>,
        committed_material: &DarkPoolPublicHostMaterial,
        candidate: &PrivateAppliedSwap,
    ) -> Result<Self, PrivateDecisionCarrierError> {
        let carrier = Self {
            degree: params.degree() as u64,
            modulus_count: params.moduli().len() as u64,
            plaintext_modulus: params.plaintext(),
            parameter_digest: public_host_parameter_digest(params),
            k: candidate.k,
            state_before_digest: candidate.state_before_digest,
            invariant_bound: candidate.invariant.plain_bound,
            invariant_bytes: candidate.invariant.ct.to_bytes(),
            state_x_bound: candidate.state_after.ct_x.plain_bound,
            state_x_bytes: candidate.state_after.ct_x.ct.to_bytes(),
            state_y_bound: candidate.state_after.ct_y.plain_bound,
            state_y_bytes: candidate.state_after.ct_y.ct.to_bytes(),
            candidate_nonce: candidate.decision_session_nonce(),
        };
        carrier.validate(params)?;
        carrier.validate_committed_pre_state(params, committed_material)?;
        if carrier.to_wire_bytes()?.len() > MAX_PRIVATE_DECISION_CARRIER_BYTES {
            return Err(PrivateDecisionCarrierError::TooLarge);
        }
        Ok(carrier)
    }

    pub const fn public_k(&self) -> u64 {
        self.k
    }

    pub const fn state_before_digest(&self) -> [u8; 32] {
        self.state_before_digest
    }

    pub const fn candidate_nonce(&self) -> [u8; 32] {
        self.candidate_nonce
    }

    pub const fn parameter_digest(&self) -> [u8; 32] {
        self.parameter_digest
    }

    pub const fn invariant_bound(&self) -> u64 {
        self.invariant_bound
    }

    pub fn invariant(
        &self,
        params: &Arc<BfvParameters>,
    ) -> Result<BoundedCiphertext, PrivateDecisionCarrierError> {
        self.validate_parameter_identity(params)?;
        Ok(BoundedCiphertext::new(
            decode_private_candidate_ciphertext(&self.invariant_bytes, params)?,
            self.invariant_bound,
        ))
    }

    /// Bind this carrier to independently obtained, canonical committed
    /// material. A material digest in an outer task is therefore not trusted
    /// without also checking the exact pre-state supplied by the table.
    pub fn validate_committed_pre_state(
        &self,
        params: &Arc<BfvParameters>,
        material: &DarkPoolPublicHostMaterial,
    ) -> Result<(), PrivateDecisionCarrierError> {
        let (_, _, state) = material
            .decode_public_objects(params)
            .map_err(|_| PrivateDecisionCarrierError::ParameterMismatch)?;
        if material.k != self.k
            || material.parameter_digest != self.parameter_digest
            || encrypted_pool_state_digest(material.k, &state) != self.state_before_digest
        {
            return Err(PrivateDecisionCarrierError::CommittedPreStateMismatch);
        }
        Ok(())
    }

    pub fn matches_candidate(&self, candidate: &PrivateAppliedSwap) -> bool {
        self.k == candidate.k
            && self.state_before_digest == candidate.state_before_digest
            && self.invariant_bound == candidate.invariant.plain_bound
            && self.invariant_bytes == candidate.invariant.ct.to_bytes()
            && self.state_x_bound == candidate.state_after.ct_x.plain_bound
            && self.state_x_bytes == candidate.state_after.ct_x.ct.to_bytes()
            && self.state_y_bound == candidate.state_after.ct_y.plain_bound
            && self.state_y_bytes == candidate.state_after.ct_y.ct.to_bytes()
            && self.candidate_nonce == candidate.decision_session_nonce()
    }

    pub fn to_wire_bytes(&self) -> Result<Vec<u8>, PrivateDecisionCarrierError> {
        let total = 8usize
            .checked_add(3 * 8 + 4 * 32 + 7 * 8)
            .and_then(|fixed| fixed.checked_add(self.invariant_bytes.len()))
            .and_then(|len| len.checked_add(self.state_x_bytes.len()))
            .and_then(|len| len.checked_add(self.state_y_bytes.len()))
            .ok_or(PrivateDecisionCarrierError::TooLarge)?;
        if total > MAX_PRIVATE_DECISION_CARRIER_BYTES {
            return Err(PrivateDecisionCarrierError::TooLarge);
        }
        let mut out = Vec::with_capacity(total);
        out.extend_from_slice(PRIVATE_DECISION_CARRIER_MAGIC);
        put_public_host_u64(&mut out, self.degree);
        put_public_host_u64(&mut out, self.modulus_count);
        put_public_host_u64(&mut out, self.plaintext_modulus);
        out.extend_from_slice(&self.parameter_digest);
        put_public_host_u64(&mut out, self.k);
        out.extend_from_slice(&self.state_before_digest);
        put_public_host_u64(&mut out, self.invariant_bound);
        put_public_host_bytes(&mut out, &self.invariant_bytes);
        put_public_host_u64(&mut out, self.state_x_bound);
        put_public_host_bytes(&mut out, &self.state_x_bytes);
        put_public_host_u64(&mut out, self.state_y_bound);
        put_public_host_bytes(&mut out, &self.state_y_bytes);
        out.extend_from_slice(&self.candidate_nonce);
        out.extend_from_slice(&private_decision_carrier_checksum(&out));
        Ok(out)
    }

    pub fn from_wire_bytes(
        bytes: &[u8],
        params: &Arc<BfvParameters>,
    ) -> Result<Self, PrivateDecisionCarrierError> {
        if bytes.len() > MAX_PRIVATE_DECISION_CARRIER_BYTES {
            return Err(PrivateDecisionCarrierError::TooLarge);
        }
        const MIN_BYTES: usize = 8 + 3 * 8 + 4 * 32 + 7 * 8;
        if bytes.len() < MIN_BYTES {
            return Err(invalid_private_carrier("truncated fixed header"));
        }
        let content_end = bytes.len() - 32;
        if bytes[content_end..] != private_decision_carrier_checksum(&bytes[..content_end]) {
            return Err(invalid_private_carrier("checksum mismatch"));
        }
        let mut input = PrivateCarrierReader::new(&bytes[..content_end]);
        if input.array::<8>()? != *PRIVATE_DECISION_CARRIER_MAGIC {
            return Err(invalid_private_carrier("wrong version magic"));
        }
        let carrier = Self {
            degree: input.u64()?,
            modulus_count: input.u64()?,
            plaintext_modulus: input.u64()?,
            parameter_digest: input.array()?,
            k: input.u64()?,
            state_before_digest: input.array()?,
            invariant_bound: input.u64()?,
            invariant_bytes: input.bytes(MAX_POOL_CIPHERTEXT_BYTES)?.to_vec(),
            state_x_bound: input.u64()?,
            state_x_bytes: input.bytes(MAX_POOL_CIPHERTEXT_BYTES)?.to_vec(),
            state_y_bound: input.u64()?,
            state_y_bytes: input.bytes(MAX_POOL_CIPHERTEXT_BYTES)?.to_vec(),
            candidate_nonce: input.array()?,
        };
        input.finish()?;
        carrier.validate(params)?;
        if carrier.to_wire_bytes()? != bytes {
            return Err(invalid_private_carrier("wire is not canonical"));
        }
        Ok(carrier)
    }

    fn validate(&self, params: &Arc<BfvParameters>) -> Result<(), PrivateDecisionCarrierError> {
        self.validate_parameter_identity(params)?;
        if self.k == 0
            || self.k >= self.plaintext_modulus
            || self.invariant_bound >= self.plaintext_modulus
            || self.state_x_bound >= self.plaintext_modulus
            || self.state_y_bound >= self.plaintext_modulus
        {
            return Err(invalid_private_carrier(
                "public value or bound leaves the plaintext domain",
            ));
        }
        for bytes in [
            &self.invariant_bytes,
            &self.state_x_bytes,
            &self.state_y_bytes,
        ] {
            decode_private_candidate_ciphertext(bytes, params)?;
        }
        let expected_nonce = private_candidate_nonce_from_parts(
            self.k,
            self.state_before_digest,
            [
                (self.invariant_bound, &self.invariant_bytes),
                (self.state_x_bound, &self.state_x_bytes),
                (self.state_y_bound, &self.state_y_bytes),
            ],
        );
        if self.candidate_nonce != expected_nonce {
            return Err(invalid_private_carrier(
                "candidate nonce does not commit the exact carrier",
            ));
        }
        Ok(())
    }

    fn validate_parameter_identity(
        &self,
        params: &Arc<BfvParameters>,
    ) -> Result<(), PrivateDecisionCarrierError> {
        if self.degree != params.degree() as u64
            || self.modulus_count != params.moduli().len() as u64
            || self.plaintext_modulus != params.plaintext()
            || self.parameter_digest != public_host_parameter_digest(params)
        {
            return Err(PrivateDecisionCarrierError::ParameterMismatch);
        }
        Ok(())
    }
}

impl AppliedSwap {
    /// The acceptance rule at the decrypt boundary: the opened slot-0 value of
    /// `invariant` must be EXACTLY k. The caller supplies the decrypted value
    /// (test: sk decrypt; production: threshold combine) — this module never
    /// holds key material.
    pub fn check_invariant(&self, decrypted_slot0: u64) -> Result<(), DarkAmmError> {
        if decrypted_slot0 != self.k {
            return Err(DarkAmmError::InvariantViolated {
                decrypted: decrypted_slot0,
                k: self.k,
            });
        }
        Ok(())
    }
}

impl DarkPool {
    /// LP-side pool creation: encrypt the initial reserves under the pool's
    /// public key, declare PUBLIC loose caps, publish k = x0·y0.
    ///
    /// Refuses loudly when: a reserve is 0; a reserve exceeds its declared cap
    /// (the cap must actually bound the ciphertext slot or the wrap guard is
    /// unsound); or the cap product already reaches t (no swap could ever be
    /// verified).
    #[allow(clippy::too_many_arguments)]
    pub fn init<R: rand_09::RngCore + rand_09::CryptoRng>(
        params: &Arc<BfvParameters>,
        pk: &PublicKey,
        rk: &RelinearizationKey,
        x0: u64,
        y0: u64,
        cap_x: u64,
        cap_y: u64,
        rng: &mut R,
    ) -> Result<Self, DarkAmmError> {
        let engine = MulEngine::new(rk, params)?;
        let t = engine.plaintext_modulus();
        if x0 == 0 || y0 == 0 {
            return Err(DarkAmmError::InvalidInit {
                reason: "empty reserve",
            });
        }
        if x0 > cap_x || y0 > cap_y {
            return Err(DarkAmmError::InvalidInit {
                reason: "reserve exceeds its declared public cap (cap would be an unsound bound)",
            });
        }
        if (cap_x as u128) * (cap_y as u128) >= t as u128 {
            return Err(DarkAmmError::InvalidInit {
                reason: "cap_x·cap_y >= t: the invariant product could wrap; no swap verifiable",
            });
        }
        // caps < t ⇒ k = x0·y0 ≤ cap_x·cap_y < t: representable, exact.
        let k = x0 * y0;
        let encrypt = |v: u64, rng: &mut R| -> Result<_, DarkAmmError> {
            let pt = Plaintext::try_encode(&[v], Encoding::simd(), params)
                .map_err(|e| DarkAmmError::Fhe(e.to_string()))?;
            pk.try_encrypt(&pt, rng)
                .map_err(|e| DarkAmmError::Fhe(e.to_string()))
        };
        let ct_x = BoundedCiphertext::new(encrypt(x0, rng)?, cap_x);
        let ct_y = BoundedCiphertext::new(encrypt(y0, rng)?, cap_y);
        Ok(Self {
            params: params.clone(),
            public_key: pk.clone(),
            relinearization_key: rk.clone(),
            engine,
            state: PoolCiphertexts { ct_x, ct_y },
            k,
            lp_view: Some(PlainAmm::new(x0, y0)),
        })
    }

    /// Drop the LP view — what the HOUSE holds: ciphertexts, caps, k. It can
    /// verify proposed swaps but cannot quote (and cannot see reserves).
    pub fn strip_lp_view(&mut self) {
        self.lp_view = None;
    }

    /// The encrypted reserves (for the decrypt boundary / differential tests).
    pub fn reserve_cts(&self) -> &PoolCiphertexts {
        &self.state
    }

    pub fn plaintext_modulus(&self) -> u64 {
        self.engine.plaintext_modulus()
    }

    /// Snapshot exactly the public evaluation state needed by a secretless
    /// host process after restart.
    pub fn public_host_material(&self) -> Result<DarkPoolPublicHostMaterial, DarkAmmError> {
        DarkPoolPublicHostMaterial::try_new(
            &self.params,
            &self.public_key,
            &self.relinearization_key,
            self.k,
            &self.state,
        )
    }

    /// Restore an evaluation-only house process from canonical public
    /// material. The resulting pool has no LP plaintext view and this API
    /// accepts no secret key. Candidate commit still requires a separately
    /// verified scalar opening or collective decision capability.
    pub fn restore_public_host(
        params: &Arc<BfvParameters>,
        material: &DarkPoolPublicHostMaterial,
    ) -> Result<Self, DarkAmmError> {
        let (public_key, relinearization_key, state) = material.decode_public_objects(params)?;
        let engine = MulEngine::new(&relinearization_key, params)?;
        Ok(Self {
            params: params.clone(),
            public_key,
            relinearization_key,
            engine,
            state,
            k: material.k,
            lp_view: None,
        })
    }

    fn scalar_pt(&self, v: u64) -> Result<Plaintext, DarkAmmError> {
        Plaintext::try_encode(&[v], Encoding::simd(), &self.params)
            .map_err(|e| DarkAmmError::Fhe(e.to_string()))
    }

    /// HOUSE-side verification leg: given a public (dx, dy) proposal, compute
    /// the candidate post-state by EXACT plaintext ops and the invariant
    /// product by ONE wrap-guarded ct×ct multiply. Touches no plaintext
    /// reserve. Refusals: zero amounts, dy over the public cap, cap overflow,
    /// wrap guard.
    pub fn try_swap_proposed(&self, dx: u64, dy: u64) -> Result<AppliedSwap, DarkAmmError> {
        let t = self.engine.plaintext_modulus();
        if dx == 0 || dy == 0 {
            return Err(DarkAmmError::ZeroAmount);
        }
        let cap_y = self.state.ct_y.plain_bound;
        if dy > cap_y {
            return Err(DarkAmmError::DyExceedsCap { dy, cap_y });
        }
        let cap_x_after = self
            .state
            .ct_x
            .plain_bound
            .checked_add(dx)
            .filter(|&b| b < t)
            .ok_or(DarkAmmError::CapOverflow {
                detail: "cap_x + dx >= t",
            })?;
        // dy ≤ cap_y checked above; honest reserves y ≤ cap_y give y−dy ≤ cap_y−dy.
        // (A dishonest dy > y wraps the slot mod t, the declared bound is then
        // unsound, the product is junk, and the invariant check refuses — the
        // residual mod-t forgery margin is named in the module doc.)
        let cap_y_after = cap_y - dy;

        // The public legs: EXACT plaintext add/sub on the ciphertexts.
        let new_x = BoundedCiphertext::new(&self.state.ct_x.ct + &self.scalar_pt(dx)?, cap_x_after);
        let new_y = BoundedCiphertext::new(&self.state.ct_y.ct - &self.scalar_pt(dy)?, cap_y_after);

        // The secret×secret leg: ONE wrap-guarded ct×ct multiply (fhe.rs
        // Multiplicator underneath — the oracle-anchored engine).
        let invariant = self.engine.multiply(&new_x, &new_y)?;

        Ok(AppliedSwap {
            dx,
            dy,
            k: self.k,
            invariant,
            state_after: PoolCiphertexts {
                ct_x: new_x,
                ct_y: new_y,
            },
        })
    }

    /// HOUSE-side hidden-amount verification. `encrypted_dx` and
    /// `encrypted_dy` are ciphertexts under the pool key with public inclusive
    /// bounds; their values never enter this API. The candidate computes
    ///
    /// `Enc(x') = Enc(x) + Enc(dx)` and `Enc(y') = Enc(y) - Enc(dy)`,
    ///
    /// then one ct×ct product `Enc(x'·y')`. Only that product is opened, and an
    /// honest swap reveals the already-public `k`.
    ///
    /// The bounds are declarations, not proofs. A production ingress must bind
    /// them with the repository's range-proof machinery; until then a malicious
    /// wrapped input retains the mod-t forgery residual named in the module doc.
    pub fn try_private_swap_proposed(
        &self,
        encrypted_dx: &BoundedCiphertext,
        encrypted_dy: &BoundedCiphertext,
    ) -> Result<PrivateAppliedSwap, DarkAmmError> {
        let t = self.engine.plaintext_modulus();
        let cap_x_after = self
            .state
            .ct_x
            .plain_bound
            .checked_add(encrypted_dx.plain_bound)
            .filter(|&bound| bound < t)
            .ok_or(DarkAmmError::CapOverflow {
                detail: "cap_x + cap_dx >= t",
            })?;

        // For honest 0 <= dy <= y, y-dy remains in [0, cap_y]. We cannot
        // subtract `cap_dy` from the upper bound: dy may be zero. The range and
        // no-overdraw premises are the named ingest proof residual; the
        // invariant equality catches ordinary violations before mutation.
        if encrypted_dy.plain_bound >= t {
            return Err(DarkAmmError::CapOverflow {
                detail: "cap_dy >= t",
            });
        }
        let cap_y_after = self.state.ct_y.plain_bound;
        let new_x = BoundedCiphertext::new(&self.state.ct_x.ct + &encrypted_dx.ct, cap_x_after);
        let new_y = BoundedCiphertext::new(&self.state.ct_y.ct - &encrypted_dy.ct, cap_y_after);
        let invariant = self.engine.multiply(&new_x, &new_y)?;
        Ok(PrivateAppliedSwap {
            invariant,
            state_after: PoolCiphertexts {
                ct_x: new_x,
                ct_y: new_y,
            },
            k: self.k,
            state_before_digest: encrypted_pool_state_digest(self.k, &self.state),
        })
    }

    /// LP-side full leg: quote dy from the LP view (EXACT quotes only), then
    /// run the house verification leg on it.
    pub fn try_swap(&self, dx: u64) -> Result<AppliedSwap, DarkAmmError> {
        if dx == 0 {
            return Err(DarkAmmError::ZeroAmount);
        }
        let lp = self
            .lp_view
            .as_ref()
            .ok_or(DarkAmmError::QuoteUnavailable)?;
        let (dy_floor, remainder) = lp.quote_floor(dx);
        let dy = lp.quote_exact(dx).ok_or(DarkAmmError::NoExactQuote {
            dx,
            dy_floor,
            remainder,
        })?;
        self.try_swap_proposed(dx, dy)
    }

    /// Commit a checked swap: the caller passes the decrypt boundary's opened
    /// slot-0 value of `swap.invariant`; iff it is exactly k, the encrypted
    /// state advances (and the LP view, if any, tracks).
    pub fn commit(
        &mut self,
        swap: &AppliedSwap,
        decrypted_invariant_slot0: u64,
    ) -> Result<(), DarkAmmError> {
        swap.check_invariant(decrypted_invariant_slot0)?;
        self.state = swap.state_after.clone();
        if let Some(lp) = self.lp_view.as_mut() {
            lp.apply(swap.dx, swap.dy);
        }
        Ok(())
    }

    /// Commit a hidden-amount transition after the invariant boundary accepts.
    /// A pool retaining the LP's plaintext quote view refuses: it cannot update
    /// that view without learning the amounts, and silently letting it drift
    /// would make subsequent public quotes unsound.
    pub fn commit_private(
        &mut self,
        swap: PrivateAppliedSwap,
        decrypted_invariant_slot0: u64,
    ) -> Result<(), DarkAmmError> {
        self.preflight_private_candidate(&swap)?;
        swap.check_invariant(decrypted_invariant_slot0)?;
        self.state = swap.state_after;
        Ok(())
    }

    /// Commit from the masked party-MPC boundary without ever receiving the
    /// invariant product. The decision token is constructed only by a complete
    /// [`crate::mpc_party`] equality quorum and is consumed here. Its session
    /// nonce must commit this exact candidate.
    ///
    /// This closes raw-product disclosure in the semi-honest process-shaped
    /// protocol. It does not prove malicious parties supplied shares derived
    /// from the candidate ciphertext; authenticated input/share validity is the
    /// remaining MPC hardening seam.
    pub fn commit_private_decision(
        &mut self,
        swap: PrivateAppliedSwap,
        decision: DistributedDecisionRun,
    ) -> Result<(), DarkAmmError> {
        self.preflight_private_candidate(&swap)?;
        if decision.session_nonce() != swap.decision_session_nonce() {
            return Err(DarkAmmError::InvariantDecisionContextMismatch);
        }
        if !decision.is_equal() {
            return Err(DarkAmmError::InvariantDecisionRefused);
        }
        self.state = swap.state_after;
        Ok(())
    }

    /// Refuse every pool/candidate mismatch that could otherwise occur after
    /// an external replay guard accepts an attested decision.
    pub(crate) fn preflight_private_candidate(
        &self,
        swap: &PrivateAppliedSwap,
    ) -> Result<(), DarkAmmError> {
        if self.lp_view.is_some() {
            return Err(DarkAmmError::PrivateSwapRequiresHouseView);
        }
        if swap.k != self.k
            || swap.state_before_digest != encrypted_pool_state_digest(self.k, &self.state)
        {
            return Err(DarkAmmError::InvariantDecisionContextMismatch);
        }
        Ok(())
    }

    /// Install a candidate only after `preflight_private_candidate` and every
    /// external authorization check have succeeded. Deliberately infallible so
    /// no new refusal can occur after replay state is consumed.
    pub(crate) fn install_preflighted_private_candidate(&mut self, swap: &PrivateAppliedSwap) {
        self.state = swap.state_after.clone();
    }
}

/// Price a swap on hidden reserves: enforce (x+dx)·(y−dy) == k homomorphically (the ct×ct multiply is the
/// point — reserves never revealed). Returns dy (or the encrypted price), plus the updated encrypted pool.
pub fn swap(pool: &DarkPool, dx_plain: u64, t: u64) -> SwapResult {
    let expected_t = pool.plaintext_modulus();
    if t != expected_t {
        return SwapResult {
            outcome: Err(DarkAmmError::ParamMismatch {
                expected_t,
                got_t: t,
            }),
        };
    }
    SwapResult {
        outcome: pool.try_swap(dx_plain),
    }
}

fn malformed_public_host(reason: impl Into<String>) -> DarkAmmError {
    DarkAmmError::MalformedPublicHostMaterial {
        reason: reason.into(),
    }
}

fn encrypted_pool_state_digest(k: u64, state: &PoolCiphertexts) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update(b"fhegg/dark-amm/encrypted-pool-state/v1");
    hash.update(k.to_le_bytes());
    for bounded in [&state.ct_x, &state.ct_y] {
        let bytes = bounded.ct.to_bytes();
        hash.update(bounded.plain_bound.to_le_bytes());
        hash.update((bytes.len() as u64).to_le_bytes());
        hash.update(bytes);
    }
    hash.finalize().into()
}

fn private_candidate_nonce_from_parts(
    k: u64,
    state_before_digest: [u8; 32],
    parts: [(u64, &[u8]); 3],
) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update(b"fhegg/dark-amm-private-invariant-decision/v2");
    hash.update(k.to_le_bytes());
    hash.update(state_before_digest);
    for (bound, bytes) in parts {
        hash.update(bound.to_le_bytes());
        hash.update((bytes.len() as u64).to_le_bytes());
        hash.update(bytes);
    }
    hash.finalize().into()
}

fn private_decision_carrier_checksum(content: &[u8]) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update(PRIVATE_DECISION_CARRIER_CHECKSUM_DOMAIN);
    hash.update((content.len() as u64).to_le_bytes());
    hash.update(content);
    hash.finalize().into()
}

fn invalid_private_carrier(reason: impl Into<String>) -> PrivateDecisionCarrierError {
    PrivateDecisionCarrierError::InvalidWire(reason.into())
}

fn decode_private_candidate_ciphertext(
    bytes: &[u8],
    params: &Arc<BfvParameters>,
) -> Result<Ciphertext, PrivateDecisionCarrierError> {
    let ciphertext = Ciphertext::from_bytes(bytes, params)
        .map_err(|error| invalid_private_carrier(format!("ciphertext decode failed: {error}")))?;
    if ciphertext.to_bytes() != bytes {
        return Err(invalid_private_carrier(
            "ciphertext is not canonically encoded",
        ));
    }
    Ok(ciphertext)
}

fn public_host_parameter_digest(params: &BfvParameters) -> [u8; 32] {
    // Hash fhe.rs's complete canonical parameter encoding, not merely the
    // arithmetic dimensions used by evaluation.  In particular, that encoding
    // also carries the error variance; omitting it would let a carrier created
    // under one encryption/noise policy restart under another while claiming an
    // exact parameter identity.
    let bytes = params.to_bytes();
    let mut hash = Sha256::new();
    hash.update(PUBLIC_HOST_PARAMETER_DOMAIN);
    hash.update((bytes.len() as u64).to_le_bytes());
    hash.update(bytes);
    hash.finalize().into()
}

fn public_host_checksum(content: &[u8]) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update(PUBLIC_HOST_CHECKSUM_DOMAIN);
    hash.update((content.len() as u64).to_le_bytes());
    hash.update(content);
    hash.finalize().into()
}

fn put_public_host_u64(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_public_host_bytes(out: &mut Vec<u8>, bytes: &[u8]) {
    put_public_host_u64(out, bytes.len() as u64);
    out.extend_from_slice(bytes);
}

struct PublicHostReader<'a> {
    bytes: &'a [u8],
    offset: usize,
}

struct PrivateCarrierReader<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> PrivateCarrierReader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn array<const N: usize>(&mut self) -> Result<[u8; N], PrivateDecisionCarrierError> {
        let end = self
            .offset
            .checked_add(N)
            .filter(|end| *end <= self.bytes.len())
            .ok_or_else(|| invalid_private_carrier("truncated field"))?;
        let value = self.bytes[self.offset..end]
            .try_into()
            .map_err(|_| invalid_private_carrier("invalid fixed-width field"))?;
        self.offset = end;
        Ok(value)
    }

    fn u64(&mut self) -> Result<u64, PrivateDecisionCarrierError> {
        Ok(u64::from_le_bytes(self.array()?))
    }

    fn bytes(&mut self, max: usize) -> Result<&'a [u8], PrivateDecisionCarrierError> {
        let len = usize::try_from(self.u64()?)
            .map_err(|_| invalid_private_carrier("length does not fit usize"))?;
        if len > max {
            return Err(invalid_private_carrier(format!(
                "field length {len} exceeds maximum {max}"
            )));
        }
        let end = self
            .offset
            .checked_add(len)
            .filter(|end| *end <= self.bytes.len())
            .ok_or_else(|| invalid_private_carrier("truncated length-delimited field"))?;
        let value = &self.bytes[self.offset..end];
        self.offset = end;
        Ok(value)
    }

    fn finish(self) -> Result<(), PrivateDecisionCarrierError> {
        if self.offset == self.bytes.len() {
            Ok(())
        } else {
            Err(invalid_private_carrier("trailing bytes"))
        }
    }
}

impl<'a> PublicHostReader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn array<const N: usize>(&mut self) -> Result<[u8; N], DarkAmmError> {
        let end = self
            .offset
            .checked_add(N)
            .filter(|end| *end <= self.bytes.len())
            .ok_or_else(|| malformed_public_host("truncated field"))?;
        let value = self.bytes[self.offset..end]
            .try_into()
            .map_err(|_| malformed_public_host("invalid fixed-width field"))?;
        self.offset = end;
        Ok(value)
    }

    fn u64(&mut self) -> Result<u64, DarkAmmError> {
        Ok(u64::from_le_bytes(self.array()?))
    }

    fn bytes(&mut self, max: usize) -> Result<&'a [u8], DarkAmmError> {
        let len = usize::try_from(self.u64()?)
            .map_err(|_| malformed_public_host("length does not fit usize"))?;
        if len > max {
            return Err(malformed_public_host(format!(
                "field length {len} exceeds maximum {max}"
            )));
        }
        let end = self
            .offset
            .checked_add(len)
            .filter(|end| *end <= self.bytes.len())
            .ok_or_else(|| malformed_public_host("truncated length-delimited field"))?;
        let value = &self.bytes[self.offset..end];
        self.offset = end;
        Ok(value)
    }

    fn finish(self) -> Result<(), DarkAmmError> {
        if self.offset == self.bytes.len() {
            Ok(())
        } else {
            Err(malformed_public_host("trailing bytes"))
        }
    }
}

// ---------------------------------------------------------------------------
// THE TEETH — fhe.rs is the oracle: encrypt with real fhe.rs, swap through the
// engine, decrypt with real fhe.rs, and DIFFERENTIALLY match the plaintext
// constant-product AMM exactly. If the homomorphic invariant or the state
// update is wrong in any way, fhe.rs decrypts a different number and the test
// is RED — agreement with a real BFV library cannot be faked.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod tests {
    use super::*;
    use std::thread;
    use std::time::Duration;

    use ed25519_dalek::SigningKey;
    use fhe::bfv::SecretKey;
    use fhe_traits::{FheDecoder, FheDecrypter};
    use rand::rngs::StdRng as MpcRng;
    use rand::SeedableRng as MpcSeedableRng;
    use rand_09::rngs::StdRng;
    use rand_09::SeedableRng;

    use crate::additive::pick_params;
    use crate::attestation::{
        AuthenticatedQuorumVerifier, ComputationIntegrityEvidence, ComputationIntegrityResidual,
        InMemoryReplayGuard,
    };
    use crate::bfv_lean::{FOLD_DEGREE, FOLD_MODULI};
    use crate::decision_attestation::{AttestedDecisionReceipt, ExpectedDecisionContext};
    use crate::mpc_party::{
        local_channels, run_party_equality, trusted_dealer_triples, DistributedDecisionRun,
        PartyEqualityInput, PartyMpcSession,
    };

    struct Fixture {
        params: Arc<BfvParameters>,
        sk: SecretKey,
        pk: PublicKey,
        rk: RelinearizationKey,
        rng: StdRng,
        t: u64,
    }

    fn fixture(seed: u64) -> Fixture {
        let params = pick_params(20);
        // Pin the parameter facts (same discipline as bfv_mul_oracle): if the
        // default set drifts we fail LOUDLY instead of testing another scheme.
        assert_eq!(params.degree(), FOLD_DEGREE, "degree drifted");
        assert_eq!(params.moduli(), &FOLD_MODULI, "RNS moduli drifted");
        let t = params.plaintext();
        assert_eq!(t, 1_032_193, "plaintext modulus drifted");
        let mut rng = StdRng::seed_from_u64(seed);
        let sk = SecretKey::random(&params, &mut rng);
        let pk = PublicKey::new(&sk, &mut rng);
        let rk = RelinearizationKey::new(&sk, &mut rng).expect("relin key");
        Fixture {
            params,
            sk,
            pk,
            rk,
            rng,
            t,
        }
    }

    /// The modeled decrypt boundary: open slot 0 with the real fhe.rs sk.
    /// (Production: the threshold committee — the `threshold.rs` lane.)
    fn open_slot0(fx: &Fixture, ct: &Ciphertext) -> u64 {
        let pt = fx.sk.try_decrypt(ct).expect("fhe.rs decrypt");
        Vec::<u64>::try_decode(&pt, Encoding::simd()).expect("simd decode")[0]
    }

    fn pool(fx: &mut Fixture, x0: u64, y0: u64, cap_x: u64, cap_y: u64) -> DarkPool {
        let mut rng = StdRng::seed_from_u64(0xDA12_0000 ^ x0 ^ (y0 << 20));
        let _ = &mut fx.rng; // fixture rng reserved for key material
        DarkPool::init(&fx.params, &fx.pk, &fx.rk, x0, y0, cap_x, cap_y, &mut rng)
            .expect("pool init")
    }

    fn encrypted_amount(fx: &mut Fixture, value: u64, declared_bound: u64) -> BoundedCiphertext {
        let pt =
            Plaintext::try_encode(&[value], Encoding::simd(), &fx.params).expect("amount encode");
        let ct = fx.pk.try_encrypt(&pt, &mut fx.rng).expect("amount encrypt");
        BoundedCiphertext::new(ct, declared_bound)
    }

    fn share_mod_t(value: u64, t: u64, n: usize, rng: &mut MpcRng) -> Vec<u64> {
        let mut shares = (0..n - 1)
            .map(|_| rand::Rng::gen_range(rng, 0..t))
            .collect::<Vec<_>>();
        let partial = shares.iter().fold(0u64, |acc, &share| (acc + share) % t);
        shares.push((value + t - partial) % t);
        shares
    }

    /// Test/process harness for the real party-owned decision circuit. The
    /// direct-peer API receives one local residue share per thread; this helper
    /// knows the scalars only to create a differential oracle sharing.
    fn invariant_decision(
        nonce: [u8; 32],
        left: u64,
        right: u64,
        t: u64,
        seed: u64,
    ) -> DistributedDecisionRun {
        invariant_decision_with_session(nonce, left, right, t, seed).1
    }

    fn invariant_decision_with_session(
        nonce: [u8; 32],
        left: u64,
        right: u64,
        t: u64,
        seed: u64,
    ) -> (PartyMpcSession, DistributedDecisionRun) {
        const N: usize = 3;
        const BITS: usize = 17; // public pool bound is below 2^17 in these vectors
        let session = PartyMpcSession::equality(nonce, N, BITS, t, Duration::from_secs(2))
            .expect("decision session");
        let mut rng = MpcRng::seed_from_u64(seed);
        let left = share_mod_t(left, t, N, &mut rng);
        let right = share_mod_t(right, t, N, &mut rng);
        let inputs = (0..N)
            .map(|party| {
                let mut party_rng = MpcRng::seed_from_u64(seed ^ 0xd00d_0000 ^ party as u64);
                PartyEqualityInput::new(&session, party, left[party], right[party], &mut party_rng)
                    .expect("party-local decision ingress")
            })
            .collect::<Vec<_>>();
        let triples = trusted_dealer_triples(&session, &mut rng).expect("shape-only triples");
        let (coordinator, endpoints) = local_channels(&session);
        let parties = inputs
            .into_iter()
            .zip(triples)
            .zip(endpoints)
            .map(|((input, triples), endpoint)| {
                thread::spawn(move || run_party_equality(input, triples, endpoint))
            })
            .collect::<Vec<_>>();
        let run = coordinator
            .coordinate_equality(&session)
            .expect("full decision quorum");
        for party in parties {
            party.join().unwrap().unwrap();
        }
        (session, run)
    }

    /// The genuinely dark amount path: neither dx nor dy enters the verifier
    /// API as plaintext. The house computes the encrypted post-state, opens
    /// only the already-public invariant k, and commits exact hidden reserves.
    #[test]
    fn encrypted_amount_swap_reveals_only_the_invariant_and_commits() {
        let mut fx = fixture(0xDA10);
        let mut p = pool(&mut fx, 100, 900, 400, 1000);
        p.strip_lp_view();
        let dx = encrypted_amount(&mut fx, 50, 50);
        let dy = encrypted_amount(&mut fx, 300, 300);

        let applied = p
            .try_private_swap_proposed(&dx, &dy)
            .expect("hidden exact swap shape");
        let public_debug = format!("{applied:?}");
        assert!(!public_debug.contains("dx"));
        assert!(!public_debug.contains("dy"));
        assert!(!public_debug.contains("amount"));

        // Candidate production is non-mutating until the invariant opens.
        assert_eq!(open_slot0(&fx, &p.reserve_cts().ct_x.ct), 100);
        assert_eq!(open_slot0(&fx, &p.reserve_cts().ct_y.ct), 900);
        let opened = open_slot0(&fx, &applied.invariant.ct);
        assert_eq!(opened, p.k, "the only opened scalar is public k");
        p.commit_private(applied, opened)
            .expect("verified private swap commits");
        assert_eq!(open_slot0(&fx, &p.reserve_cts().ct_x.ct), 150);
        assert_eq!(open_slot0(&fx, &p.reserve_cts().ct_y.ct), 600);
    }

    /// Preferred private commit: the product is represented by party-local
    /// shares and the house receives only a candidate-bound equality token.
    /// The wrong proposal returns a residue-free error and cannot mutate state.
    #[test]
    fn encrypted_amount_swap_commits_from_one_masked_decision_bit() {
        let mut fx = fixture(0xDA13);
        let mut p = pool(&mut fx, 100, 900, 400, 1000);
        p.strip_lp_view();
        let dx = encrypted_amount(&mut fx, 50, 50);
        let dy = encrypted_amount(&mut fx, 300, 300);
        let applied = p.try_private_swap_proposed(&dx, &dy).unwrap();
        let opened_oracle = open_slot0(&fx, &applied.invariant.ct);
        let decision = invariant_decision(
            applied.decision_session_nonce(),
            opened_oracle,
            p.k,
            fx.t,
            0xda13,
        );
        assert!(decision.is_equal());
        p.commit_private_decision(applied, decision)
            .expect("one candidate-bound bit commits");
        assert_eq!(open_slot0(&fx, &p.reserve_cts().ct_x.ct), 150);
        assert_eq!(open_slot0(&fx, &p.reserve_cts().ct_y.ct), 600);

        let mut bad = pool(&mut fx, 100, 900, 400, 1000);
        bad.strip_lp_view();
        let dx = encrypted_amount(&mut fx, 50, 50);
        let wrong_dy = encrypted_amount(&mut fx, 301, 301);
        let candidate = bad.try_private_swap_proposed(&dx, &wrong_dy).unwrap();
        let wrong_product = open_slot0(&fx, &candidate.invariant.ct);
        let refused = invariant_decision(
            candidate.decision_session_nonce(),
            wrong_product,
            bad.k,
            fx.t,
            0xda14,
        );
        assert!(!refused.is_equal());
        let error = bad
            .commit_private_decision(candidate, refused)
            .expect_err("wrong invariant decision holds state");
        assert!(matches!(error, DarkAmmError::InvariantDecisionRefused));
        assert!(!error.to_string().contains(&wrong_product.to_string()));
        assert_eq!(open_slot0(&fx, &bad.reserve_cts().ct_x.ct), 100);
        assert_eq!(open_slot0(&fx, &bad.reserve_cts().ct_y.ct), 900);
    }

    /// Real party-MPC transcript -> configured threshold-roster signatures ->
    /// strict transport/replay gate -> atomic candidate commit.
    #[test]
    fn encrypted_swap_decision_is_quorum_attested_before_commit() {
        let mut fx = fixture(0xDA16);
        let mut p = pool(&mut fx, 100, 900, 400, 1000);
        p.strip_lp_view();
        let dx = encrypted_amount(&mut fx, 50, 50);
        let dy = encrypted_amount(&mut fx, 300, 300);
        let candidate = p.try_private_swap_proposed(&dx, &dy).unwrap();
        let candidate_nonce = candidate.decision_session_nonce();
        let opened_oracle = open_slot0(&fx, &candidate.invariant.ct);
        let (session, decision) =
            invariant_decision_with_session(candidate_nonce, opened_oracle, p.k, fx.t, 0xda16);

        let keys = vec![
            SigningKey::from_bytes(&[21; 32]),
            SigningKey::from_bytes(&[22; 32]),
            SigningKey::from_bytes(&[23; 32]),
        ];
        let verifier = AuthenticatedQuorumVerifier::new(
            keys.iter()
                .map(|key| key.verifying_key().to_bytes())
                .collect(),
            2,
        )
        .unwrap();
        let context = ExpectedDecisionContext {
            session: &session,
            roster_digest: verifier.roster_digest(),
            transcript: &decision.transcript,
            equal: decision.is_equal(),
        };
        let draft = AttestedDecisionReceipt::issue(
            &context,
            ComputationIntegrityEvidence::BindingOnly(
                ComputationIntegrityResidual::OutputOnlySelfAssertion,
            ),
        )
        .unwrap();
        let signatures = vec![
            verifier
                .sign_claim(&draft.claim_digest(), 0, &keys[0])
                .unwrap(),
            verifier
                .sign_claim(&draft.claim_digest(), 2, &keys[2])
                .unwrap(),
        ];
        let evidence = verifier
            .assemble_evidence(&draft.claim_digest(), &signatures)
            .unwrap();
        let receipt = AttestedDecisionReceipt::issue(&context, evidence).unwrap();
        let receipt =
            AttestedDecisionReceipt::from_wire_bytes(&receipt.to_wire_bytes().unwrap()).unwrap();
        receipt
            .verify_full(&context, &verifier, &mut InMemoryReplayGuard::default())
            .unwrap();

        assert_eq!(receipt.claim.session_nonce, candidate_nonce);
        assert!(receipt.claim.equal);
        p.commit_private_decision(candidate, decision).unwrap();
        assert_eq!(open_slot0(&fx, &p.reserve_cts().ct_x.ct), 150);
        assert_eq!(open_slot0(&fx, &p.reserve_cts().ct_y.ct), 600);
    }

    #[test]
    fn private_decision_is_bound_to_the_exact_candidate() {
        let mut fx = fixture(0xDA15);
        let mut p = pool(&mut fx, 100, 900, 400, 1000);
        p.strip_lp_view();
        let dx = encrypted_amount(&mut fx, 50, 50);
        let dy = encrypted_amount(&mut fx, 300, 300);
        let candidate = p.try_private_swap_proposed(&dx, &dy).unwrap();
        let decision = invariant_decision([0x99; 32], p.k, p.k, fx.t, 0xda15);
        assert!(matches!(
            p.commit_private_decision(candidate, decision),
            Err(DarkAmmError::InvariantDecisionContextMismatch)
        ));
        assert_eq!(open_slot0(&fx, &p.reserve_cts().ct_x.ct), 100);
        assert_eq!(open_slot0(&fx, &p.reserve_cts().ct_y.ct), 900);
    }

    /// Encrypted amounts are not accepted on signer faith: a wrong encrypted
    /// output makes the actual ct×ct invariant decrypt differently and cannot
    /// mutate the pool.
    #[test]
    fn wrong_encrypted_amount_is_refused_and_private_state_holds() {
        let mut fx = fixture(0xDA11);
        let mut p = pool(&mut fx, 100, 900, 400, 1000);
        p.strip_lp_view();
        let dx = encrypted_amount(&mut fx, 50, 50);
        let wrong_dy = encrypted_amount(&mut fx, 301, 301);
        let applied = p
            .try_private_swap_proposed(&dx, &wrong_dy)
            .expect("bounded ciphertext shape");
        let opened = open_slot0(&fx, &applied.invariant.ct);
        assert_eq!(opened, 150 * 599);
        assert_ne!(opened, p.k);
        assert!(p.commit_private(applied, opened).is_err());
        assert_eq!(open_slot0(&fx, &p.reserve_cts().ct_x.ct), 100);
        assert_eq!(open_slot0(&fx, &p.reserve_cts().ct_y.ct), 900);
    }

    /// Keeping a local plaintext LP view while accepting an opaque amount
    /// would silently desynchronize the quoting state; the API refuses instead.
    #[test]
    fn private_amount_commit_requires_a_blind_house_view() {
        let mut fx = fixture(0xDA12);
        let mut p = pool(&mut fx, 100, 900, 400, 1000);
        let dx = encrypted_amount(&mut fx, 50, 50);
        let dy = encrypted_amount(&mut fx, 300, 300);
        let applied = p.try_private_swap_proposed(&dx, &dy).unwrap();
        let opened = open_slot0(&fx, &applied.invariant.ct);
        assert!(matches!(
            p.commit_private(applied, opened),
            Err(DarkAmmError::PrivateSwapRequiresHouseView)
        ));
        assert_eq!(open_slot0(&fx, &p.reserve_cts().ct_x.ct), 100);
        assert_eq!(open_slot0(&fx, &p.reserve_cts().ct_y.ct), 900);
    }

    /// THE LOAD-BEARING TOOTH: one exact swap through the frozen `swap()`
    /// entry point, DIFFERENTIALLY validated against the plaintext
    /// constant-product AMM: the quoted dy, the decrypted invariant product,
    /// and the decrypted post-swap reserves all match the cleartext x·y=k
    /// computation exactly.
    #[test]
    fn oracle_exact_swap_matches_plaintext_amm() {
        let mut fx = fixture(0xDA1);
        let (x0, y0) = (100u64, 900u64);
        let mut p = pool(&mut fx, x0, y0, 400, 1000);
        assert_eq!(p.k, 90_000);

        // The plaintext oracle.
        let mut plain = PlainAmm::new(x0, y0);
        let dx = 50u64;
        let (dy_floor, r) = plain.quote_floor(dx);
        assert_eq!((dy_floor, r), (300, 0), "chosen dx must be an exact case");

        // The FHE swap through the FROZEN entry point.
        let res = swap(&p, dx, fx.t);
        let applied = res.outcome.expect("exact swap must verify in shape");
        assert_eq!(
            applied.dy, dy_floor,
            "quoted dy differs from the plaintext AMM"
        );

        // The decrypt boundary opens ONLY the invariant product: exactly k.
        let opened = open_slot0(&fx, &applied.invariant.ct);
        assert_eq!(opened, p.k, "(x+dx)·(y−dy) decrypted off the invariant");
        applied.check_invariant(opened).expect("acceptance");
        p.commit(&applied, opened).expect("commit");

        // Differential: decrypted post-swap reserves == plaintext AMM's.
        plain.apply(dx, dy_floor);
        assert_eq!((plain.x, plain.y), (150, 600));
        let st = p.reserve_cts();
        assert_eq!(open_slot0(&fx, &st.ct_x.ct), plain.x, "post-swap x differs");
        assert_eq!(open_slot0(&fx, &st.ct_y.ct), plain.y, "post-swap y differs");
        // And the plaintext invariant really is preserved.
        assert_eq!(plain.x * plain.y, p.k);
    }

    /// REPEATED SWAPS: a 3-swap exact chain (100,900)→(150,600)→(180,500)→
    /// (300,300). Every hop: invariant decrypts to exactly k; final reserves
    /// decrypt to the plaintext AMM's. This also witnesses by execution that
    /// plaintext-op-only state updates do not accumulate decrypt-breaking
    /// noise across swaps.
    #[test]
    fn oracle_multi_swap_chain() {
        let mut fx = fixture(0xDA2);
        let (x0, y0) = (100u64, 900u64);
        let mut p = pool(&mut fx, x0, y0, 400, 1000);
        let mut plain = PlainAmm::new(x0, y0);

        for dx in [50u64, 30, 120] {
            let dy = plain.quote_exact(dx).expect("chain chosen exact");
            let applied = p.try_swap(dx).expect("swap shape");
            assert_eq!(applied.dy, dy, "dx={dx}: dy differs from plaintext AMM");
            let opened = open_slot0(&fx, &applied.invariant.ct);
            assert_eq!(opened, p.k, "dx={dx}: invariant product != k");
            p.commit(&applied, opened).expect("commit");
            plain.apply(dx, dy);
        }
        assert_eq!((plain.x, plain.y), (300, 300));
        let st = p.reserve_cts();
        assert_eq!(open_slot0(&fx, &st.ct_x.ct), 300);
        assert_eq!(open_slot0(&fx, &st.ct_y.ct), 300);
    }

    /// FAILING SIDE — the invariant check BITES: dy off by ±1 decrypts to a
    /// value ≠ k and is REFUSED; the pool state does not advance. This is the
    /// tooth that a faked/trivial invariant cannot pass.
    #[test]
    fn wrong_dy_is_refused_and_state_holds() {
        let mut fx = fixture(0xDA3);
        let mut p = pool(&mut fx, 100, 900, 400, 1000);
        let k = p.k;

        for bad_dy in [299u64, 301] {
            let applied = p.try_swap_proposed(50, bad_dy).expect("shape passes");
            let opened = open_slot0(&fx, &applied.invariant.ct);
            assert_ne!(opened, k, "bad dy={bad_dy} must not satisfy the invariant");
            // 150·(900−299)=90150, 150·(900−301)=89850 — well-formed WRONG products.
            let expected = 150 * (900 - bad_dy);
            assert_eq!(opened, expected, "the oracle sees the exact wrong product");
            let err = p.commit(&applied, opened).expect_err("must refuse");
            assert!(
                matches!(err, DarkAmmError::InvariantViolated { decrypted, k: kk }
                    if decrypted == expected && kk == k),
                "wrong refusal: {err}"
            );
        }
        // State held: reserves unchanged.
        let st = p.reserve_cts();
        assert_eq!(open_slot0(&fx, &st.ct_x.ct), 100);
        assert_eq!(open_slot0(&fx, &st.ct_y.ct), 900);
    }

    /// FAILING SIDE — a dy > y (overdraw under the public cap) wraps the slot
    /// mod t; the junk product cannot decrypt to k and the swap is refused.
    #[test]
    fn overdraw_dy_wraps_and_is_refused() {
        let mut fx = fixture(0xDA4);
        let mut p = pool(&mut fx, 100, 900, 400, 1000);
        // dy=950 ≤ cap_y=1000 passes the public cap check, but y−dy = −50
        // wraps to t−50 in plaintext space.
        let applied = p.try_swap_proposed(50, 950).expect("shape passes");
        let opened = open_slot0(&fx, &applied.invariant.ct);
        // 150·(t−50) mod t = (150·1032143) mod 1032193 — junk, and ≠ k.
        let expected = ((150u128 * (fx.t as u128 - 50)) % fx.t as u128) as u64;
        assert_eq!(opened, expected, "wrap arithmetic witness");
        assert_ne!(opened, p.k);
        assert!(
            p.commit(&applied, opened).is_err(),
            "overdraw must be refused"
        );
    }

    /// The wrap-guard DISCIPLINE is inherited from bfv_mul: a swap whose
    /// declared post-swap cap product reaches t is refused BEFORE any
    /// ciphertext math (loud, named), and pool init refuses caps that could
    /// never verify a swap.
    #[test]
    fn wrap_guard_and_init_refusals() {
        let mut fx = fixture(0xDA5);
        // init: caps whose product reaches t are refused outright.
        let mut rng = StdRng::seed_from_u64(7);
        let err = DarkPool::init(&fx.params, &fx.pk, &fx.rk, 100, 900, 1016, 1016, &mut rng)
            .expect_err("cap product >= t must be refused at init");
        assert!(
            matches!(err, DarkAmmError::InvalidInit { .. }),
            "wrong refusal: {err}"
        );

        // swap: cap_x grows with dx until the multiply guard trips.
        let p = pool(&mut fx, 100, 900, 700, 1000);
        // (700+600)·(1000−300) = 910000 < t would pass, so push dy small:
        // (700+600)·(1000−1) = 1298700 ≥ t → WrapRefused from bfv_mul.
        let err = p.try_swap_proposed(600, 1).expect_err("guard must refuse");
        assert!(
            matches!(err, DarkAmmError::Mul(BfvMulError::WrapRefused { .. })),
            "wrong refusal: {err}"
        );
    }

    /// Quoting refusals: non-exact dx is NAMED (floor quote + remainder
    /// reported), zero amounts are refused, and a house-side pool (LP view
    /// stripped) can verify but not quote.
    #[test]
    fn quote_refusals_are_loud_and_named() {
        let mut fx = fixture(0xDA6);
        let mut p = pool(&mut fx, 100, 900, 400, 1000);

        // dx=7: y·dx = 6300, x+dx = 107 → floor 58 r 94: not exact.
        let err = p.try_swap(7).expect_err("inexact dx must be refused");
        assert!(
            matches!(
                err,
                DarkAmmError::NoExactQuote {
                    dx: 7,
                    dy_floor: 58,
                    remainder: 94
                }
            ),
            "wrong refusal: {err}"
        );

        assert!(matches!(
            swap(&p, 0, fx.t).outcome,
            Err(DarkAmmError::ZeroAmount)
        ));
        assert!(matches!(
            swap(&p, 50, fx.t + 1).outcome,
            Err(DarkAmmError::ParamMismatch { .. })
        ));

        // House-side: verify works, quote does not.
        p.strip_lp_view();
        assert!(matches!(
            p.try_swap(50),
            Err(DarkAmmError::QuoteUnavailable)
        ));
        let applied = p
            .try_swap_proposed(50, 300)
            .expect("house can still verify");
        assert_eq!(open_slot0(&fx, &applied.invariant.ct), p.k);
    }

    /// The plaintext reference itself: floor-quote arithmetic pins (the
    /// oracle must be right before it can judge the FHE path).
    #[test]
    fn plain_amm_quote_pins() {
        let amm = PlainAmm::new(100, 900);
        assert_eq!(amm.quote_floor(50), (300, 0));
        assert_eq!(amm.quote_exact(50), Some(300));
        assert_eq!(amm.quote_floor(7), (58, 94)); // 6300 = 58·107 + 94
        assert_eq!(amm.quote_exact(7), None);
        // Constant-product identity: (x+dx)(y−dy) = k + r, for both cases.
        for dx in [50u64, 7] {
            let (dy, r) = amm.quote_floor(dx);
            assert_eq!((amm.x + dx) * (amm.y - dy), amm.k + r);
        }
        // dy=0 quotes are not swaps.
        let tiny = PlainAmm::new(1000, 1);
        assert_eq!(tiny.quote_exact(1), None);
    }
}
