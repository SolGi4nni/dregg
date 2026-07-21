//! A hosted, game-facing Dark Pool table over the executable encrypted-amount
//! constant-product path in [`fhegg_fhe::dark_amm`].
//!
//! An external producer receives [`DarkAmmPublicSession`] (the BFV public key,
//! fixed parameter identity, public invariant, loose caps, session binding, and
//! next sequence), encrypts `dx` and `dy` locally, and submits only the canonical
//! [`EncryptedSwapRequest`] bytes. Legacy mode computes the candidate reserve
//! transition homomorphically, opens the invariant product, and mutates iff it
//! equals the already-public `k`. Proof-required mode instead accepts only a
//! versioned [`ProvedEncryptedSwapRequest`]: it first verifies the HidingFri
//! transition receipt and exact current root, then runs the same encrypted
//! candidate decision, and advances ciphertext state + root + sequence only
//! when both agree. Same-opening-required mode is a hard v3 boundary around
//! that v2 body plus a quorum-authenticated [`AmmSameOpeningReceipt`]. The host
//! reconstructs the exact BFV ciphertexts, proof, statement, single-host BFV
//! identity, and issuer policy before any candidate-state mutation. The
//! ordinary deos surface shows the accepted encrypted move count without
//! showing either amount or reserve.
//!
//! # Honest deployment grade
//!
//! This is the executable integration stone, not the final no-viewer boundary:
//! the demo offering retains one deployment BFV secret key and relinearization
//! key supplied from protected host configuration. It decrypts only the candidate product
//! in the operation path, but key custody technically permits it to decrypt the
//! reserve ciphertexts.  A refused proposal's raw product is visible inside the
//! host process (it is not returned in the public refusal).  Request bounds are
//! caller declarations, not range proofs, and there is not yet a proof that the
//! submitted ciphertexts use this table's public key. The hiding receipt proves
//! private constant-product semantics and root continuity. v2 does not prove
//! that its amounts are the same openings as the BFV ciphertexts. v3 requires
//! Tier-1 issuer-visible authenticated exact-opening evidence, but does not
//! make the host key threshold-held. Those residuals are deliberately repeated
//! in the operation disclosures below.

use std::fmt;
use std::sync::Arc;

use deos_view::ViewNode;
use dregg_circuit_prove::dark_amm_private::{
    DarkAmmPrivateZkProof, PRIVATE_SCALAR_BOUND,
    PUBLIC_INPUT_COUNT as PRIVATE_AMM_PUBLIC_INPUT_COUNT,
    PublicStatement as PrivateAmmPublicStatement, RULE_ID as PRIVATE_AMM_RULE_ID,
    state_root as private_amm_state_root, verify_zk as verify_private_amm_zk,
};
use dreggnet_offerings::{
    Action, BinaryOperationDescriptor, BinaryOperationError, BinaryOperationReceipt,
    BinaryOperationReplayMaterial, DreggIdentity, Offering, OfferingError, Outcome, RunCost,
    SessionConfig, Surface, VerifyReport,
};
use ed25519_dalek::SigningKey;
use fhe::bfv::{
    BfvParameters, Ciphertext, Encoding, Plaintext, PublicKey, RelinearizationKey, SecretKey,
};
use fhe_traits::{
    DeserializeParametrized, FheDecoder, FheDecrypter, FheEncoder, FheEncrypter, Serialize,
};
use fhegg_fhe::additive::pick_params;
use fhegg_fhe::amm_same_opening::{
    AmmPrivacyTier, AmmSameOpeningContext, AmmSameOpeningReceipt, ExactBfvAmountOpening,
    Tier1SameOpeningAuthority, Tier1SameOpeningEndorsement, canonical_bfv_parameters_digest,
};
use fhegg_fhe::attestation::{AuthenticatedQuorumVerifier, InMemoryReplayGuard, ReplayGuard};
use fhegg_fhe::bfv_mul::{BoundedCiphertext, MulEngine};
use fhegg_fhe::dark_amm::{DarkPool, PrivateAppliedSwap};
use fhegg_fhe::threshold::{BfvParams, CollectivePublicKey, KeygenSession};
use rand_09::rngs::StdRng;
use rand_09::{CryptoRng, RngCore, SeedableRng};

/// Stable catalog key for the private constant-product table.
pub const DARK_AMM_OFFERING_KEY: &str = "dark-pool";
/// Stable generic binary-operation identity.
pub const DARK_AMM_OPERATION: &str = "dark-bazaar.private-amm-swap.v1";
/// Exact media type for [`EncryptedSwapRequest::to_wire_bytes`].
pub const DARK_AMM_MEDIA_TYPE: &str = "application/vnd.dregg.dark-amm-swap.v1";
/// Proof-required operation. This name is deliberately distinct from the
/// legacy encrypted-only demo: accepting v1 never implies this v2 receipt was
/// checked.
pub const DARK_AMM_PROVED_OPERATION: &str = "dark-bazaar.private-amm-swap.proved.v2";
/// Exact media type for [`ProvedEncryptedSwapRequest::to_wire_bytes`].
pub const DARK_AMM_PROVED_MEDIA_TYPE: &str = "application/vnd.dregg.dark-amm-swap.proved.v2";
/// Exact-opening-required operation. This is deliberately a new protocol
/// identity: neither v1 nor proved-v2 bytes are ever reinterpreted as v3.
pub const DARK_AMM_SAME_OPENING_OPERATION: &str =
    "dark-bazaar.private-amm-swap.proved.same-opening.v3";
/// Exact media type for [`SameOpeningProvedEncryptedSwapRequest::to_wire_bytes`].
pub const DARK_AMM_SAME_OPENING_MEDIA_TYPE: &str =
    "application/vnd.dregg.dark-amm-swap.proved.same-opening.v3";
/// The two BFV ciphertexts are currently roughly hundreds of KiB; retain a
/// fixed adversarial cap independent of any declared wire lengths.
pub const MAX_DARK_AMM_REQUEST_BYTES: usize = 16 * 1024 * 1024;
/// Exact security account painted by every frontend beside the uploader.
pub const DARK_AMM_DISCLOSURE: &str = "Encrypted-amount Dark Pool demo: the request contains BFV ciphertexts for dx and dy, loose public amount bounds, a pool/session binding, and a sequence number; it contains no plaintext amount or reserve. The host applies the swap only when the homomorphic post-reserve product opens to public k. Demo-grade boundary: this host retains one BFV secret key and relinearization key, so this is not yet threshold/no-viewer custody; a rejected proposal's raw product is visible inside the host process (but is not returned by the API). Bounds are caller-declared, not range-proved, and no ZK proof yet binds each ciphertext to this pool key. Durable replay retains the canonical ciphertext request and authenticated actor, never plaintext amounts, reserve openings, or secret key material.";
/// Exact security account for the proof-required operation. The proof makes
/// hidden constant-product semantics and state-root continuity authoritative;
/// the BFV ciphertext/proof same-opening relation remains explicitly absent.
pub const DARK_AMM_PROVED_DISCLOSURE: &str = "Shielded Dark Pool receipt: a HidingFri proof verifies the exact hidden constant-product transition and advances a public eight-felt state root; encrypted dx/dy drive the existing BFV candidate path only after the proof, session, rule, k, sequence, and old root verify. The request and durable journal reveal neither reserve nor exact amount (loose amount bounds remain public). Residual boundary: no proof yet establishes that the BFV ciphertexts and HidingFri witness have the same dx/dy opening. The current host retains one BFV secret key, which technically permits decrypting reserve/amount ciphertexts, and the operation path inspects the raw candidate product; this is not threshold/no-viewer custody. The host separately requires the encrypted candidate to preserve public k; proof success alone never mutates it.";
/// Exact security account for strict v3 exact-opening-required operation.
pub const DARK_AMM_SAME_OPENING_DISCLOSURE: &str = "Tier-1 exact-opening Dark Pool receipt: a HidingFri proof verifies the hidden constant-product transition, and a configured threshold of authenticated issuers attests that the exact BFV dx/dy ciphertexts open to that proof's dx/dy witness. Each issuer is trusted with the full private witness and deterministic encryption seeds; this is issuer-visible authenticated same-opening, not lattice zero knowledge against the issuers. The host reconstructs and pins the complete request, proof, statement, session, sequence, roots, k, both public BFV wrap-safety bounds, single-host BFV public identity, and ordered issuer roster before mutation. The issuer reference refuses a bound below its witnessed amount, while the hiding relation proves the actual ten-bit amounts and no-overdraw; this bound guarantee therefore has the same explicit Tier-1 issuer trust as the opening guarantee. The durable journal contains only the canonical v3 request and public receipt. Current BFV custody is explicitly n=1/opening-threshold=1: this host retains one secret and relinearization key and can technically decrypt reserves/amounts; it is not threshold/no-viewer custody, and rejected candidate products remain host-visible.";

const REQUEST_MAGIC: &[u8; 8] = b"DBAMv001";
const PROVED_REQUEST_MAGIC: &[u8; 8] = b"DBAMv002";
const SAME_OPENING_REQUEST_MAGIC: &[u8; 8] = b"DBAMv003";
const STATEMENT_MAGIC: &[u8; 8] = b"DBASv001";
const PRIVATE_STATE_MAGIC: &[u8; 8] = b"DBAOv001";
const PRIVATE_AUTHORITY_MAGIC: &[u8; 8] = b"DBAAv001";
const PUBLIC_MAGIC: &[u8; 8] = b"DBAPv003";
const HOST_KEY_MAGIC: &[u8; 8] = b"DBAKv001";
const MAX_CIPHERTEXT_BYTES: usize = 3 * 1024 * 1024;
const MAX_PROOF_BYTES: usize = 8 * 1024 * 1024;
const MAX_SAME_OPENING_RECEIPT_BYTES: usize = 16 * 1024;
const MAX_HOST_KEY_MATERIAL_BYTES: usize = 128 * 1024 * 1024;
const BABYBEAR_P: u32 = 2_013_265_921;
const PRIVATE_STATE_WIRE_BYTES: usize = 116;
const PRIVATE_AUTHORITY_WIRE_BYTES: usize = 312;

/// Errors at the producer/configuration boundary. Hosted request errors are
/// mapped into [`BinaryOperationError`] with no decrypted value in the text.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DarkAmmGameError {
    /// A fixed field or length made the wire non-canonical or unsafe to allocate.
    Malformed(String),
    /// A public configuration or honest producer input was inadmissible.
    Refused(String),
    /// The underlying BFV library refused an operation.
    Fhe(String),
}

impl fmt::Display for DarkAmmGameError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Malformed(reason) => write!(f, "malformed Dark Pool object: {reason}"),
            Self::Refused(reason) => write!(f, "Dark Pool request refused: {reason}"),
            Self::Fhe(reason) => write!(f, "BFV operation failed: {reason}"),
        }
    }
}

impl std::error::Error for DarkAmmGameError {}

/// Deployment-owned BFV custody material for one hosted Dark Pool service.
///
/// This value contains the secret key and relinearization key. It deliberately
/// has no `Debug` implementation. [`Self::to_secret_wire_bytes`] exists so an
/// operator can place the canonical bytes in a secret store and reconstruct the
/// same key after process restart; those bytes must never be served to a client
/// or written to the operation journal. External producers receive only
/// [`DarkAmmPublicSession`].
#[derive(Clone)]
pub struct DarkAmmHostKeyMaterial {
    secret_key: SecretKey,
    public_key: PublicKey,
    relinearization_key: RelinearizationKey,
}

impl DarkAmmHostKeyMaterial {
    /// Seed the caller-controlled portions of demo key generation. This is a
    /// convenience, not a reproducible derivation: fhe.rs also obtains one
    /// compressed-key seed from the operating system. Persist the returned
    /// [`Self::to_secret_wire_bytes`] for restart.
    pub fn generate_for_demo(seed: [u8; 32]) -> Result<Self, DarkAmmGameError> {
        let mut rng = StdRng::from_seed(seed);
        Self::generate(&mut rng)
    }

    /// Generate a fresh deployment key using caller-owned cryptographic
    /// randomness. fhe.rs additionally sources its compressed public-key seed
    /// from the operating system internally, so the result must be persisted;
    /// attempting to re-run key generation from the same RNG seed is not a
    /// restart mechanism.
    pub fn generate<R: RngCore + CryptoRng>(rng: &mut R) -> Result<Self, DarkAmmGameError> {
        let params = pick_params(20);
        let secret_key = SecretKey::random(&params, rng);
        let public_key = PublicKey::new(&secret_key, rng);
        let relinearization_key = RelinearizationKey::new(&secret_key, rng)
            .map_err(|error| DarkAmmGameError::Fhe(error.to_string()))?;
        let material = Self {
            secret_key,
            public_key,
            relinearization_key,
        };
        material.validate(&params)?;
        Ok(material)
    }

    /// Canonical SECRET deployment wire. This includes all key material and is
    /// for a protected operator key store only.
    pub fn to_secret_wire_bytes(&self) -> Vec<u8> {
        let secret = self.secret_key.to_bytes();
        let public = self.public_key.to_bytes();
        let relin = self.relinearization_key.to_bytes();
        let mut out = Vec::with_capacity(32 + secret.len() + public.len() + relin.len());
        out.extend_from_slice(HOST_KEY_MAGIC);
        put_bytes(&mut out, &secret);
        put_bytes(&mut out, &public);
        put_bytes(&mut out, &relin);
        out
    }

    /// Restore and algebraically validate a canonical secret deployment wire.
    pub fn from_secret_wire_bytes(bytes: &[u8]) -> Result<Self, DarkAmmGameError> {
        if bytes.len() > MAX_HOST_KEY_MATERIAL_BYTES {
            return Err(DarkAmmGameError::Malformed(format!(
                "host key material is {} bytes; maximum is {MAX_HOST_KEY_MATERIAL_BYTES}",
                bytes.len()
            )));
        }
        let mut input = Reader::new(bytes);
        if input.array::<8>()? != *HOST_KEY_MAGIC {
            return Err(DarkAmmGameError::Malformed(
                "wrong host-key magic".to_string(),
            ));
        }
        let secret_bytes = input.bytes(MAX_CIPHERTEXT_BYTES)?.to_vec();
        let public_bytes = input.bytes(MAX_CIPHERTEXT_BYTES)?.to_vec();
        let relin_bytes = input.bytes(MAX_HOST_KEY_MATERIAL_BYTES)?.to_vec();
        input.finish()?;
        let params = pick_params(20);
        let secret_key = SecretKey::from_bytes(&secret_bytes, &params)
            .map_err(|error| DarkAmmGameError::Fhe(error.to_string()))?;
        let public_key = PublicKey::from_bytes(&public_bytes, &params)
            .map_err(|error| DarkAmmGameError::Fhe(error.to_string()))?;
        let relinearization_key = RelinearizationKey::from_bytes(&relin_bytes, &params)
            .map_err(|error| DarkAmmGameError::Fhe(error.to_string()))?;
        if secret_key.to_bytes() != secret_bytes
            || public_key.to_bytes() != public_bytes
            || relinearization_key.to_bytes() != relin_bytes
        {
            return Err(DarkAmmGameError::Malformed(
                "non-canonical host key encoding".to_string(),
            ));
        }
        let material = Self {
            secret_key,
            public_key,
            relinearization_key,
        };
        material.validate(&params)?;
        if material.to_secret_wire_bytes() != bytes {
            return Err(DarkAmmGameError::Malformed(
                "host key wire is not canonical".to_string(),
            ));
        }
        Ok(material)
    }

    fn validate(&self, params: &Arc<BfvParameters>) -> Result<(), DarkAmmGameError> {
        // A tiny encrypted product proves that pk, sk, and the relinearization
        // key belong together. Type-valid but cross-deployment key substitution
        // is therefore a boot refusal, not a pool that can never accept.
        let mut rng = rand_09::rng();
        let encrypt = |value: u64,
                       rng: &mut rand_09::rngs::ThreadRng|
         -> Result<BoundedCiphertext, DarkAmmGameError> {
            let plaintext = Plaintext::try_encode(&[value], Encoding::simd(), params)
                .map_err(|error| DarkAmmGameError::Fhe(error.to_string()))?;
            self.public_key
                .try_encrypt(&plaintext, rng)
                .map(|ciphertext| BoundedCiphertext::new(ciphertext, value))
                .map_err(|error| DarkAmmGameError::Fhe(error.to_string()))
        };
        let lhs = encrypt(2, &mut rng)?;
        let rhs = encrypt(3, &mut rng)?;
        let product = MulEngine::new(&self.relinearization_key, params)
            .map_err(|error| DarkAmmGameError::Fhe(error.to_string()))?
            .multiply(&lhs, &rhs)
            .map_err(|error| DarkAmmGameError::Fhe(error.to_string()))?;
        let plaintext = self
            .secret_key
            .try_decrypt(&product.ct)
            .map_err(|error| DarkAmmGameError::Fhe(error.to_string()))?;
        let slots = Vec::<u64>::try_decode(&plaintext, Encoding::simd())
            .map_err(|error| DarkAmmGameError::Fhe(error.to_string()))?;
        if slots.first().copied() != Some(6) {
            return Err(DarkAmmGameError::Refused(
                "host public/secret/relinearization keys do not form one BFV custody set"
                    .to_string(),
            ));
        }
        Ok(())
    }

    fn rebound(
        &self,
        params: &Arc<BfvParameters>,
    ) -> Result<(SecretKey, PublicKey, RelinearizationKey), DarkAmmGameError> {
        // fhe.rs uses Arc pointer identity (not structural parameter equality)
        // in arithmetic assertions. Re-parse every deployment key against the
        // exact Arc the new session/pool owns.
        let secret_key = SecretKey::from_bytes(&self.secret_key.to_bytes(), params)
            .map_err(|error| DarkAmmGameError::Fhe(error.to_string()))?;
        let public_key = PublicKey::from_bytes(&self.public_key.to_bytes(), params)
            .map_err(|error| DarkAmmGameError::Fhe(error.to_string()))?;
        let relinearization_key =
            RelinearizationKey::from_bytes(&self.relinearization_key.to_bytes(), params)
                .map_err(|error| DarkAmmGameError::Fhe(error.to_string()))?;
        Ok((secret_key, public_key, relinearization_key))
    }
}

/// Public material an operator distributes to external swap producers.
///
/// It intentionally contains no secret key, relinearization key, reserve
/// ciphertext, reserve opening, or prior request body.  `next_sequence` is a
/// public anti-replay cursor and therefore changes after every accepted swap.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DarkAmmProofContext {
    receipt_session: u32,
    rule: u32,
    current_root: [u32; 8],
}

impl DarkAmmProofContext {
    pub const fn receipt_session(&self) -> u32 {
        self.receipt_session
    }

    pub const fn rule(&self) -> u32 {
        self.rule
    }

    pub const fn current_root(&self) -> [u32; 8] {
        self.current_root
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DarkAmmPublicSession {
    session_id: [u8; 32],
    parameter_digest: [u8; 32],
    public_key_digest: [u8; 32],
    public_key_bytes: Vec<u8>,
    plaintext_modulus: u64,
    degree: usize,
    k: u64,
    cap_x: u64,
    cap_y: u64,
    next_sequence: u64,
    proof_context: Option<DarkAmmProofContext>,
}

impl DarkAmmPublicSession {
    /// Construct the public producer view for a proof-required collective-key
    /// table.  This contains only authenticated/public DKG material; it does
    /// not imply that a particular relinearization key or initial encrypted
    /// reserve carrier was honestly generated.  The collective host boundary
    /// validates those separately.
    #[allow(clippy::too_many_arguments)]
    pub fn try_from_collective(
        session_id: [u8; 32],
        params: &BfvParams,
        keygen: &KeygenSession,
        collective: &CollectivePublicKey,
        k: u64,
        cap_x: u64,
        cap_y: u64,
        next_sequence: u64,
        current_root: [u32; 8],
    ) -> Result<Self, DarkAmmGameError> {
        if keygen.n_parties() == 0 {
            return Err(DarkAmmGameError::Refused(
                "collective BFV identity has no parties".to_string(),
            ));
        }
        validate_root(current_root)?;
        let public_key_bytes = collective.pk.to_bytes();
        let rebound = PublicKey::from_bytes(&public_key_bytes, params.arc())
            .map_err(|error| DarkAmmGameError::Fhe(error.to_string()))?;
        if rebound.to_bytes() != public_key_bytes {
            return Err(DarkAmmGameError::Malformed(
                "collective public key is not canonically encoded".to_string(),
            ));
        }
        let plaintext_modulus = params.plaintext_modulus();
        if k == 0
            || cap_x == 0
            || cap_y == 0
            || (cap_x as u128) * (cap_y as u128) >= plaintext_modulus as u128
        {
            return Err(DarkAmmGameError::Refused(
                "collective invariant/caps leave the exact BFV domain".to_string(),
            ));
        }
        Ok(Self {
            session_id,
            parameter_digest: parameter_digest_for(params.arc()),
            public_key_digest: *blake3::hash(&public_key_bytes).as_bytes(),
            public_key_bytes,
            plaintext_modulus,
            degree: params.degree(),
            k,
            cap_x,
            cap_y,
            next_sequence,
            proof_context: Some(DarkAmmProofContext {
                receipt_session: receipt_session_for(&session_id),
                rule: PRIVATE_AMM_RULE_ID,
                current_root,
            }),
        })
    }

    /// Opaque binding to this table's seed, parameters, key, and public curve.
    pub const fn session_id(&self) -> [u8; 32] {
        self.session_id
    }

    /// Canonical BabyBear session value used by the private-AMM receipt. It is
    /// derivable before an initial root is installed, avoiding a configuration
    /// cycle for external proof producers.
    pub fn private_amm_receipt_session(&self) -> u32 {
        receipt_session_for(&self.session_id)
    }

    /// Digest of the exact BFV public key accepted by this table.
    pub const fn public_key_digest(&self) -> [u8; 32] {
        self.public_key_digest
    }

    /// Canonical fhe.rs public-key bytes for an external encryptor.
    pub fn public_key_bytes(&self) -> &[u8] {
        &self.public_key_bytes
    }

    /// Public constant-product target.
    pub const fn k(&self) -> u64 {
        self.k
    }

    /// Sequence the next request must bind.
    pub const fn next_sequence(&self) -> u64 {
        self.next_sequence
    }

    /// Present only for an explicitly proof-required table. Legacy v1 tables
    /// return `None` and must not be described as receipt-verified.
    pub const fn proof_context(&self) -> Option<DarkAmmProofContext> {
        self.proof_context
    }

    /// Advance a previously distributed public context to a known public
    /// sequence cursor. The host remains authoritative and refuses stale or
    /// skipped values; this helper contains no key or state mutation.
    pub fn at_sequence(mut self, next_sequence: u64) -> Self {
        self.next_sequence = next_sequence;
        self
    }

    /// Advance a proof-required producer context using an accepted receipt's
    /// public new root. This is an offline convenience; the host independently
    /// enforces both values against its authoritative cursor.
    pub fn at_proof_cursor(
        mut self,
        next_sequence: u64,
        current_root: [u32; 8],
    ) -> Result<Self, DarkAmmGameError> {
        validate_root(current_root)?;
        let proof = self.proof_context.as_mut().ok_or_else(|| {
            DarkAmmGameError::Refused(
                "cannot install a proof cursor on a legacy encrypted-only context".to_string(),
            )
        })?;
        proof.current_root = current_root;
        self.next_sequence = next_sequence;
        Ok(self)
    }

    /// Strict distributable wire form for an offline producer.
    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(208 + self.public_key_bytes.len());
        out.extend_from_slice(PUBLIC_MAGIC);
        out.extend_from_slice(&self.session_id);
        out.extend_from_slice(&self.parameter_digest);
        out.extend_from_slice(&self.public_key_digest);
        put_u64(&mut out, self.plaintext_modulus);
        put_u64(&mut out, self.degree as u64);
        put_u64(&mut out, self.k);
        put_u64(&mut out, self.cap_x);
        put_u64(&mut out, self.cap_y);
        put_u64(&mut out, self.next_sequence);
        match self.proof_context {
            Some(proof) => {
                put_u64(&mut out, 1);
                put_u32(&mut out, proof.receipt_session);
                put_u32(&mut out, proof.rule);
                for lane in proof.current_root {
                    put_u32(&mut out, lane);
                }
            }
            None => put_u64(&mut out, 0),
        }
        put_bytes(&mut out, &self.public_key_bytes);
        out
    }

    /// Decode the strict public producer context and pin it to the repository's
    /// current BFV parameter set.
    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self, DarkAmmGameError> {
        let mut input = Reader::new(bytes);
        let magic = input.array::<8>()?;
        if magic != *PUBLIC_MAGIC {
            return Err(DarkAmmGameError::Malformed(
                "wrong public-session magic".to_string(),
            ));
        }
        let session_id = input.array()?;
        let parameter_digest = input.array()?;
        let public_key_digest = input.array()?;
        let plaintext_modulus = input.u64()?;
        let degree_u64 = input.u64()?;
        let degree = usize::try_from(degree_u64).map_err(|_| {
            DarkAmmGameError::Malformed("BFV degree does not fit usize".to_string())
        })?;
        let k = input.u64()?;
        let cap_x = input.u64()?;
        let cap_y = input.u64()?;
        let next_sequence = input.u64()?;
        let proof_context = match input.u64()? {
            0 => None,
            1 => {
                let receipt_session = input.u32()?;
                let rule = input.u32()?;
                let mut current_root = [0u32; 8];
                for lane in &mut current_root {
                    *lane = input.u32()?;
                }
                let proof = DarkAmmProofContext {
                    receipt_session,
                    rule,
                    current_root,
                };
                if proof.receipt_session >= BABYBEAR_P
                    || proof.rule != PRIVATE_AMM_RULE_ID
                    || proof.current_root.iter().any(|lane| *lane >= BABYBEAR_P)
                {
                    return Err(DarkAmmGameError::Refused(
                        "public proof context is noncanonical or names the wrong rule".to_string(),
                    ));
                }
                Some(proof)
            }
            other => {
                return Err(DarkAmmGameError::Malformed(format!(
                    "unknown public proof-context tag {other}"
                )));
            }
        };
        let public_key_bytes = input.bytes(MAX_CIPHERTEXT_BYTES)?.to_vec();
        input.finish()?;

        let params = pick_params(20);
        if plaintext_modulus != params.plaintext()
            || degree != params.degree()
            || parameter_digest != parameter_digest_for(&params)
        {
            return Err(DarkAmmGameError::Refused(
                "public session does not use the pinned Dark Pool BFV parameters".to_string(),
            ));
        }
        if *blake3::hash(&public_key_bytes).as_bytes() != public_key_digest {
            return Err(DarkAmmGameError::Malformed(
                "public-key digest mismatch".to_string(),
            ));
        }
        let key = PublicKey::from_bytes(&public_key_bytes, &params)
            .map_err(|error| DarkAmmGameError::Fhe(error.to_string()))?;
        if key.to_bytes() != public_key_bytes {
            return Err(DarkAmmGameError::Malformed(
                "non-canonical public-key bytes".to_string(),
            ));
        }
        if cap_x == 0
            || cap_y == 0
            || k == 0
            || (cap_x as u128) * (cap_y as u128) >= plaintext_modulus as u128
        {
            return Err(DarkAmmGameError::Refused(
                "public invariant/caps leave the exact BFV domain".to_string(),
            ));
        }
        Ok(Self {
            session_id,
            parameter_digest,
            public_key_digest,
            public_key_bytes,
            plaintext_modulus,
            degree,
            k,
            cap_x,
            cap_y,
            next_sequence,
            proof_context,
        })
    }
}

/// Durable private opening of one proof-authoritative AMM state.
///
/// The wire is fixed-width and checksummed, and binds both the full hosted
/// session id and its BabyBear receipt-session projection. It deliberately has
/// no `Debug` implementation. Files carrying this value must be owner-only;
/// [`Self::from_wire_bytes`] validates content, while the CLI validates file
/// type and permissions before calling it.
#[derive(Clone, PartialEq, Eq)]
pub struct DarkAmmPrivateState {
    session_id: [u8; 32],
    receipt_session: u32,
    k: u32,
    x: u16,
    y: u16,
    blind: [u32; 8],
}

impl DarkAmmPrivateState {
    /// Initialize an old-state opening from an operator-published context.
    pub fn try_new(
        public: &DarkAmmPublicSession,
        x: u16,
        y: u16,
        blind: [u32; 8],
    ) -> Result<Self, DarkAmmGameError> {
        let k = u32::try_from(public.k).map_err(|_| {
            DarkAmmGameError::Refused("public k cannot enter the private receipt field".to_string())
        })?;
        let state = Self {
            session_id: public.session_id,
            receipt_session: public.private_amm_receipt_session(),
            k,
            x,
            y,
            blind,
        };
        state.validate_internal()?;
        state.validate_against_public(public, false)?;
        Ok(state)
    }

    pub const fn session_id(&self) -> [u8; 32] {
        self.session_id
    }

    pub const fn receipt_session(&self) -> u32 {
        self.receipt_session
    }

    pub const fn k(&self) -> u32 {
        self.k
    }

    pub const fn x(&self) -> u16 {
        self.x
    }

    pub const fn y(&self) -> u16 {
        self.y
    }

    pub fn root(&self) -> Result<[u32; 8], DarkAmmGameError> {
        private_amm_state_root(self.receipt_session, self.k, self.x, self.y, self.blind)
            .map_err(DarkAmmGameError::Refused)
    }

    /// Require that this private opening is exactly the current state named by
    /// a proof-required public context.
    pub fn validate_for_proof_context(
        &self,
        public: &DarkAmmPublicSession,
    ) -> Result<(), DarkAmmGameError> {
        self.validate_against_public(public, true)
    }

    /// Derive the exact transition witness and successor opening. The current
    /// blind is always reused as `old_blind`; callers supply only a freshly
    /// sampled successor blind. A transition whose successor cannot itself be
    /// a canonical ten-bit old state is refused before proving.
    pub fn transition(
        &self,
        dx: u16,
        dy: u16,
        next_blind: [u32; 8],
    ) -> Result<
        (
            dregg_circuit_prove::dark_amm_private::PrivateAmmWitness,
            Self,
        ),
        DarkAmmGameError,
    > {
        self.validate_internal()?;
        let witness = dregg_circuit_prove::dark_amm_private::PrivateAmmWitness::try_new(
            self.x, self.y, dx, dy, self.blind, next_blind,
        )
        .map_err(DarkAmmGameError::Refused)?;
        if witness.post_x() >= PRIVATE_SCALAR_BOUND {
            return Err(DarkAmmGameError::Refused(format!(
                "successor x={} cannot be the next canonical ten-bit private state",
                witness.post_x()
            )));
        }
        let next = Self {
            session_id: self.session_id,
            receipt_session: self.receipt_session,
            k: self.k,
            x: witness.post_x(),
            y: witness.post_y(),
            blind: next_blind,
        };
        next.validate_internal()?;
        Ok((witness, next))
    }

    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(PRIVATE_STATE_WIRE_BYTES);
        out.extend_from_slice(PRIVATE_STATE_MAGIC);
        out.extend_from_slice(&self.session_id);
        put_u32(&mut out, self.receipt_session);
        put_u32(&mut out, self.k);
        put_u16(&mut out, self.x);
        put_u16(&mut out, self.y);
        for lane in self.blind {
            put_u32(&mut out, lane);
        }
        let checksum = private_state_checksum(&out);
        out.extend_from_slice(&checksum);
        debug_assert_eq!(out.len(), PRIVATE_STATE_WIRE_BYTES);
        out
    }

    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self, DarkAmmGameError> {
        if bytes.len() != PRIVATE_STATE_WIRE_BYTES {
            return Err(DarkAmmGameError::Malformed(format!(
                "private state wire is {} bytes; expected {PRIVATE_STATE_WIRE_BYTES}",
                bytes.len()
            )));
        }
        let content_end = PRIVATE_STATE_WIRE_BYTES - 32;
        let expected = private_state_checksum(&bytes[..content_end]);
        let actual: [u8; 32] = bytes[content_end..]
            .try_into()
            .expect("fixed checksum width");
        if actual != expected {
            return Err(DarkAmmGameError::Malformed(
                "private state checksum mismatch".to_string(),
            ));
        }
        let mut input = Reader::new(&bytes[..content_end]);
        if input.array::<8>()? != *PRIVATE_STATE_MAGIC {
            return Err(DarkAmmGameError::Malformed(
                "wrong private-state version magic".to_string(),
            ));
        }
        let session_id = input.array()?;
        let receipt_session = input.u32()?;
        let k = input.u32()?;
        let x = input.u16()?;
        let y = input.u16()?;
        let mut blind = [0u32; 8];
        for lane in &mut blind {
            *lane = input.u32()?;
        }
        input.finish()?;
        let state = Self {
            session_id,
            receipt_session,
            k,
            x,
            y,
            blind,
        };
        state.validate_internal()?;
        if state.to_wire_bytes() != bytes {
            return Err(DarkAmmGameError::Malformed(
                "private state wire is not canonical".to_string(),
            ));
        }
        Ok(state)
    }

    fn validate_internal(&self) -> Result<(), DarkAmmGameError> {
        if self.receipt_session != receipt_session_for(&self.session_id) {
            return Err(DarkAmmGameError::Refused(
                "private state receipt session does not match its hosted session id".to_string(),
            ));
        }
        if self.x >= PRIVATE_SCALAR_BOUND || self.y >= PRIVATE_SCALAR_BOUND {
            return Err(DarkAmmGameError::Refused(
                "private state reserves are outside the canonical ten-bit old-state range"
                    .to_string(),
            ));
        }
        self.root()?;
        Ok(())
    }

    fn validate_against_public(
        &self,
        public: &DarkAmmPublicSession,
        require_proof_context: bool,
    ) -> Result<(), DarkAmmGameError> {
        self.validate_internal()?;
        if self.session_id != public.session_id
            || self.receipt_session != public.private_amm_receipt_session()
            || u64::from(self.k) != public.k
        {
            return Err(DarkAmmGameError::Refused(
                "private state does not match the public session and invariant".to_string(),
            ));
        }
        match public.proof_context {
            Some(context) => {
                if context.receipt_session != self.receipt_session
                    || context.rule != PRIVATE_AMM_RULE_ID
                    || context.current_root != self.root()?
                {
                    return Err(DarkAmmGameError::Refused(
                        "private state opening does not match the proof context's current root"
                            .to_string(),
                    ));
                }
            }
            None if require_proof_context => {
                return Err(DarkAmmGameError::Refused(
                    "public context is legacy encrypted-only, not proof-required".to_string(),
                ));
            }
            None => {}
        }
        Ok(())
    }
}

fn private_state_checksum(content: &[u8]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-dark-amm-private-state-v1");
    hasher.update(content);
    *hasher.finalize().as_bytes()
}

/// Owning, canonical request created outside the host. The ciphertext payloads
/// are fhe.rs's parameterized canonical encoding; no plaintext amount is
/// carried alongside them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EncryptedSwapRequest {
    session_id: [u8; 32],
    public_key_digest: [u8; 32],
    sequence: u64,
    dx_bound: u64,
    dy_bound: u64,
    encrypted_dx: Vec<u8>,
    encrypted_dy: Vec<u8>,
}

impl EncryptedSwapRequest {
    /// Public anti-replay cursor bound by this request.
    pub const fn sequence(&self) -> u64 {
        self.sequence
    }

    /// Canonical, versioned, length-delimited transport bytes.
    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(112 + self.encrypted_dx.len() + self.encrypted_dy.len());
        out.extend_from_slice(REQUEST_MAGIC);
        out.extend_from_slice(&self.session_id);
        out.extend_from_slice(&self.public_key_digest);
        put_u64(&mut out, self.sequence);
        put_u64(&mut out, self.dx_bound);
        put_u64(&mut out, self.dy_bound);
        put_bytes(&mut out, &self.encrypted_dx);
        put_bytes(&mut out, &self.encrypted_dy);
        out
    }

    /// Strict bounded decode. Parameterized ciphertext validation happens at
    /// the host or producer boundary where the pinned parameters are present.
    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self, DarkAmmGameError> {
        if bytes.len() > MAX_DARK_AMM_REQUEST_BYTES {
            return Err(DarkAmmGameError::Malformed(format!(
                "request is {} bytes; maximum is {MAX_DARK_AMM_REQUEST_BYTES}",
                bytes.len()
            )));
        }
        let mut input = Reader::new(bytes);
        if input.array::<8>()? != *REQUEST_MAGIC {
            return Err(DarkAmmGameError::Malformed(
                "wrong encrypted-swap magic".to_string(),
            ));
        }
        let request = Self {
            session_id: input.array()?,
            public_key_digest: input.array()?,
            sequence: input.u64()?,
            dx_bound: input.u64()?,
            dy_bound: input.u64()?,
            encrypted_dx: input.bytes(MAX_CIPHERTEXT_BYTES)?.to_vec(),
            encrypted_dy: input.bytes(MAX_CIPHERTEXT_BYTES)?.to_vec(),
        };
        input.finish()?;
        Ok(request)
    }

    fn bounded_ciphertexts(
        &self,
        params: &Arc<BfvParameters>,
    ) -> Result<(BoundedCiphertext, BoundedCiphertext), DarkAmmGameError> {
        let decode = |bytes: &[u8], bound| -> Result<BoundedCiphertext, DarkAmmGameError> {
            let ciphertext = Ciphertext::from_bytes(bytes, params)
                .map_err(|error| DarkAmmGameError::Fhe(error.to_string()))?;
            if ciphertext.to_bytes() != bytes {
                return Err(DarkAmmGameError::Malformed(
                    "non-canonical BFV ciphertext bytes".to_string(),
                ));
            }
            Ok(BoundedCiphertext::new(ciphertext, bound))
        };
        Ok((
            decode(&self.encrypted_dx, self.dx_bound)?,
            decode(&self.encrypted_dy, self.dy_bound)?,
        ))
    }
}

/// Versioned proof-required request. The encrypted candidate and the exact
/// 19-felt receipt statement travel together, but the disclosure is explicit:
/// the current proof does not yet prove they share the same dx/dy opening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProvedEncryptedSwapRequest {
    encrypted: EncryptedSwapRequest,
    statement: PrivateAmmPublicStatement,
    proof_bytes: Vec<u8>,
}

impl ProvedEncryptedSwapRequest {
    pub const fn sequence(&self) -> u64 {
        self.encrypted.sequence
    }

    pub const fn statement(&self) -> PrivateAmmPublicStatement {
        self.statement
    }

    pub fn proof_bytes(&self) -> &[u8] {
        &self.proof_bytes
    }

    /// Exact hosted table named by the encrypted v1 body.
    pub const fn hosted_session(&self) -> [u8; 32] {
        self.encrypted.session_id
    }

    /// Digest of the exact BFV public key named by the encrypted v1 body.
    pub const fn public_key_digest(&self) -> [u8; 32] {
        self.encrypted.public_key_digest
    }

    /// Public no-wrap cap carried for the encrypted `dx` amount.
    pub const fn dx_bound(&self) -> u64 {
        self.encrypted.dx_bound
    }

    /// Public no-wrap cap carried for the encrypted `dy` amount.
    pub const fn dy_bound(&self) -> u64 {
        self.encrypted.dy_bound
    }

    /// Strictly decode the two public BFV ciphertext objects against an exact
    /// parameter handle. Their plaintexts remain encrypted.
    pub fn bounded_ciphertexts(
        &self,
        params: &Arc<BfvParameters>,
    ) -> Result<(BoundedCiphertext, BoundedCiphertext), DarkAmmGameError> {
        self.encrypted.bounded_ciphertexts(params)
    }

    /// Strictly decode the public HidingFri proof carried by this request.
    pub fn decoded_private_amm_proof(&self) -> Result<DarkAmmPrivateZkProof, DarkAmmGameError> {
        decode_canonical_private_amm_proof(&self.proof_bytes)
    }

    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let encrypted = self.encrypted.to_wire_bytes();
        let mut out = Vec::with_capacity(
            112 + encrypted.len() + PRIVATE_AMM_PUBLIC_INPUT_COUNT * 4 + self.proof_bytes.len(),
        );
        out.extend_from_slice(PROVED_REQUEST_MAGIC);
        put_bytes(&mut out, &encrypted);
        for value in self.statement.as_u32_array() {
            put_u32(&mut out, value);
        }
        put_bytes(&mut out, &self.proof_bytes);
        out
    }

    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self, DarkAmmGameError> {
        if bytes.len() > MAX_DARK_AMM_REQUEST_BYTES {
            return Err(DarkAmmGameError::Malformed(format!(
                "proved request is {} bytes; maximum is {MAX_DARK_AMM_REQUEST_BYTES}",
                bytes.len()
            )));
        }
        let mut input = Reader::new(bytes);
        if input.array::<8>()? != *PROVED_REQUEST_MAGIC {
            return Err(DarkAmmGameError::Malformed(
                "wrong proved encrypted-swap magic".to_string(),
            ));
        }
        let encrypted =
            EncryptedSwapRequest::from_wire_bytes(input.bytes(MAX_DARK_AMM_REQUEST_BYTES)?)?;
        let mut values = [0u32; PRIVATE_AMM_PUBLIC_INPUT_COUNT];
        for value in &mut values {
            *value = input.u32()?;
        }
        let statement = PrivateAmmPublicStatement::try_from_u32s(&values)
            .map_err(DarkAmmGameError::Malformed)?;
        let proof_bytes = input.bytes(MAX_PROOF_BYTES)?.to_vec();
        input.finish()?;
        Ok(Self {
            encrypted,
            statement,
            proof_bytes,
        })
    }
}

/// Strict v3 request: the complete canonical proved-v2 body plus a Tier-1
/// quorum receipt for its exact BFV/proof openings.
///
/// The nested version is intentional. A decoder must see `DBAMv003` first and
/// then independently decode an exact `DBAMv002` body; v2 can therefore never
/// acquire v3 meaning through content negotiation or a permissive fallback.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SameOpeningProvedEncryptedSwapRequest {
    proved: ProvedEncryptedSwapRequest,
    same_opening_receipt: AmmSameOpeningReceipt,
}

impl SameOpeningProvedEncryptedSwapRequest {
    /// Wrap already-assembled issuer evidence without changing the proved-v2
    /// body. The configured host independently verifies every binding.
    pub fn new(
        proved: ProvedEncryptedSwapRequest,
        same_opening_receipt: AmmSameOpeningReceipt,
    ) -> Self {
        Self {
            proved,
            same_opening_receipt,
        }
    }

    pub const fn sequence(&self) -> u64 {
        self.proved.sequence()
    }

    pub fn proved_request(&self) -> &ProvedEncryptedSwapRequest {
        &self.proved
    }

    pub fn same_opening_receipt(&self) -> &AmmSameOpeningReceipt {
        &self.same_opening_receipt
    }

    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let proved = self.proved.to_wire_bytes();
        let receipt = self.same_opening_receipt.to_wire_bytes();
        let mut out = Vec::with_capacity(24 + proved.len() + receipt.len());
        out.extend_from_slice(SAME_OPENING_REQUEST_MAGIC);
        put_bytes(&mut out, &proved);
        put_bytes(&mut out, &receipt);
        out
    }

    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self, DarkAmmGameError> {
        if bytes.len() > MAX_DARK_AMM_REQUEST_BYTES {
            return Err(DarkAmmGameError::Malformed(format!(
                "same-opening request is {} bytes; maximum is {MAX_DARK_AMM_REQUEST_BYTES}",
                bytes.len()
            )));
        }
        let mut input = Reader::new(bytes);
        if input.array::<8>()? != *SAME_OPENING_REQUEST_MAGIC {
            return Err(DarkAmmGameError::Malformed(
                "wrong same-opening encrypted-swap magic".to_string(),
            ));
        }
        let proved =
            ProvedEncryptedSwapRequest::from_wire_bytes(input.bytes(MAX_DARK_AMM_REQUEST_BYTES)?)?;
        let receipt_bytes = input.bytes(MAX_SAME_OPENING_RECEIPT_BYTES)?;
        let same_opening_receipt =
            AmmSameOpeningReceipt::from_wire_bytes(receipt_bytes).map_err(|error| {
                DarkAmmGameError::Malformed(format!(
                    "same-opening receipt failed strict decoding: {error}"
                ))
            })?;
        input.finish()?;
        if same_opening_receipt.to_wire_bytes() != receipt_bytes {
            return Err(DarkAmmGameError::Malformed(
                "same-opening receipt is not canonically encoded".to_string(),
            ));
        }
        Ok(Self {
            proved,
            same_opening_receipt,
        })
    }
}

/// Canonical standalone file representation for an already-produced exact
/// public statement. It can be paired with the proof's raw postcard bytes by
/// `dark-amm-tool proved-swap` without giving the CLI any private witness.
pub fn private_amm_statement_to_wire(statement: PrivateAmmPublicStatement) -> Vec<u8> {
    let mut out = Vec::with_capacity(8 + PRIVATE_AMM_PUBLIC_INPUT_COUNT * 4);
    out.extend_from_slice(STATEMENT_MAGIC);
    for value in statement.as_u32_array() {
        put_u32(&mut out, value);
    }
    out
}

pub fn private_amm_statement_from_wire(
    bytes: &[u8],
) -> Result<PrivateAmmPublicStatement, DarkAmmGameError> {
    let mut input = Reader::new(bytes);
    if input.array::<8>()? != *STATEMENT_MAGIC {
        return Err(DarkAmmGameError::Malformed(
            "wrong private-AMM statement magic".to_string(),
        ));
    }
    let mut values = [0u32; PRIVATE_AMM_PUBLIC_INPUT_COUNT];
    for value in &mut values {
        *value = input.u32()?;
    }
    input.finish()?;
    PrivateAmmPublicStatement::try_from_u32s(&values).map_err(DarkAmmGameError::Malformed)
}

fn decode_canonical_private_amm_proof(
    proof_bytes: &[u8],
) -> Result<DarkAmmPrivateZkProof, DarkAmmGameError> {
    if proof_bytes.len() > MAX_PROOF_BYTES {
        return Err(DarkAmmGameError::Malformed(format!(
            "private AMM proof is {} bytes; maximum is {MAX_PROOF_BYTES}",
            proof_bytes.len()
        )));
    }
    let proof =
        DarkAmmPrivateZkProof::from_postcard(proof_bytes).map_err(DarkAmmGameError::Malformed)?;
    if proof.to_postcard().map_err(DarkAmmGameError::Malformed)? != proof_bytes {
        return Err(DarkAmmGameError::Malformed(
            "private AMM proof is not canonically encoded".to_string(),
        ));
    }
    Ok(proof)
}

/// Owning reconstruction of every live object used by the same-opening claim.
/// Keeping this internal prevents callers from supplying a ciphertext or key
/// object independently of the canonical hosted v2 body and public session.
struct SameOpeningPublicObjects {
    params: BfvParams,
    keygen: KeygenSession,
    collective: CollectivePublicKey,
    dx_ciphertext: Ciphertext,
    dy_ciphertext: Ciphertext,
    proof: DarkAmmPrivateZkProof,
}

fn reconstruct_same_opening_objects(
    public: &DarkAmmPublicSession,
    request: &ProvedEncryptedSwapRequest,
) -> Result<SameOpeningPublicObjects, DarkAmmGameError> {
    if request.encrypted.session_id != public.session_id
        || request.encrypted.public_key_digest != public.public_key_digest
        || request.encrypted.sequence != public.next_sequence
    {
        return Err(DarkAmmGameError::Refused(
            "same-opening body names a different hosted session, key, or sequence".to_string(),
        ));
    }
    validate_statement_against_context(
        request.statement,
        public.proof_context.ok_or_else(|| {
            DarkAmmGameError::Refused(
                "same-opening requires a proof-root-enabled public session".to_string(),
            )
        })?,
        public.k,
    )?;

    let params = BfvParams::fold_set();
    if public.parameter_digest != parameter_digest_for(params.arc())
        || public.degree != params.degree()
        || public.plaintext_modulus != params.plaintext_modulus()
    {
        return Err(DarkAmmGameError::Refused(
            "public session is outside the pinned same-opening BFV parameter set".to_string(),
        ));
    }
    let public_key = PublicKey::from_bytes(&public.public_key_bytes, params.arc())
        .map_err(|error| DarkAmmGameError::Fhe(error.to_string()))?;
    if public_key.to_bytes() != public.public_key_bytes
        || *blake3::hash(&public_key.to_bytes()).as_bytes() != public.public_key_digest
    {
        return Err(DarkAmmGameError::Malformed(
            "same-opening public key is not canonical or digest-matched".to_string(),
        ));
    }
    let decode_ciphertext = |bytes: &[u8]| -> Result<Ciphertext, DarkAmmGameError> {
        let ciphertext = Ciphertext::from_bytes(bytes, params.arc())
            .map_err(|error| DarkAmmGameError::Fhe(error.to_string()))?;
        if ciphertext.to_bytes() != bytes {
            return Err(DarkAmmGameError::Malformed(
                "same-opening ciphertext is not canonically encoded".to_string(),
            ));
        }
        Ok(ciphertext)
    };
    let dx_ciphertext = decode_ciphertext(&request.encrypted.encrypted_dx)?;
    let dy_ciphertext = decode_ciphertext(&request.encrypted.encrypted_dy)?;
    let proof = decode_canonical_private_amm_proof(&request.proof_bytes)?;

    // The current host really owns one ordinary BFV secret key. The public
    // marker is reproducible from the hosted session + exact public key and
    // deliberately yields n=1/opening_threshold=1 in BfvPublicIdentity. It is
    // not a claim that this key arose from distributed key generation.
    let mut marker = blake3::Hasher::new_derive_key("dregg-dark-amm-single-host-keygen-marker-v1");
    marker.update(&public.session_id);
    marker.update(&public.public_key_digest);
    let keygen = KeygenSession::from_seed(1, *marker.finalize().as_bytes())
        .map_err(|error| DarkAmmGameError::Refused(format!("{error:?}")))?;

    Ok(SameOpeningPublicObjects {
        params,
        keygen,
        collective: CollectivePublicKey { pk: public_key },
        dx_ciphertext,
        dy_ciphertext,
        proof,
    })
}

fn verify_same_opening_receipt<R: ReplayGuard>(
    public: &DarkAmmPublicSession,
    request: &ProvedEncryptedSwapRequest,
    receipt: &AmmSameOpeningReceipt,
    verifier: &AuthenticatedQuorumVerifier,
    replay: &mut R,
) -> Result<[u8; 32], DarkAmmGameError> {
    let objects = reconstruct_same_opening_objects(public, request)?;
    let expected = AmmSameOpeningContext {
        privacy_tier: AmmPrivacyTier::Tier1IssuerVisible,
        hosted_session: public.session_id,
        sequence: request.encrypted.sequence,
        dx_bound: request.encrypted.dx_bound,
        dy_bound: request.encrypted.dy_bound,
        params: &objects.params,
        keygen: &objects.keygen,
        collective: &objects.collective,
        dx_ciphertext: &objects.dx_ciphertext,
        dy_ciphertext: &objects.dy_ciphertext,
        proof: &objects.proof,
        statement: request.statement,
    };
    receipt
        .verify(&expected, verifier, replay)
        .map(|verified| verified.claim_digest())
        .map_err(|error| {
            DarkAmmGameError::Refused(format!(
                "Tier-1 same-opening receipt verification failed: {error}"
            ))
        })
}

/// Owner-only bridge material for independently endorsing one exact request.
///
/// This object retains the complete HidingFri witness and the two independent
/// BFV encryption seeds used by [`produce_proved_encrypted_swap_seeded`]. Its
/// three digests pin the exact statement, proof, and hosted request emitted in
/// the same atomic bundle. It deliberately has no `Debug` or `Clone`
/// implementation. The checksum detects storage corruption; it is not a MAC.
/// A caller handing this object to a Tier-1 same-opening authority is handing
/// that authority the private transition.
pub struct DarkAmmPrivateSwapAuthority {
    hosted_session: [u8; 32],
    sequence: u64,
    witness: dregg_circuit_prove::dark_amm_private::PrivateAmmWitness,
    dx_encryption_seed: [u8; 32],
    dy_encryption_seed: [u8; 32],
    statement_digest: [u8; 32],
    proof_digest: [u8; 32],
    request_digest: [u8; 32],
}

impl DarkAmmPrivateSwapAuthority {
    #[allow(clippy::too_many_arguments)]
    pub fn try_new(
        public: &DarkAmmPublicSession,
        witness: dregg_circuit_prove::dark_amm_private::PrivateAmmWitness,
        dx_encryption_seed: [u8; 32],
        dy_encryption_seed: [u8; 32],
        request: &ProvedEncryptedSwapRequest,
    ) -> Result<Self, DarkAmmGameError> {
        let authority = Self {
            hosted_session: public.session_id,
            sequence: public.next_sequence,
            witness,
            dx_encryption_seed,
            dy_encryption_seed,
            statement_digest: *blake3::hash(&private_amm_statement_to_wire(request.statement))
                .as_bytes(),
            proof_digest: *blake3::hash(&request.proof_bytes).as_bytes(),
            request_digest: *blake3::hash(&request.to_wire_bytes()).as_bytes(),
        };
        authority.validate_bundle(public, request)?;
        Ok(authority)
    }

    /// Reconstruct the exact private witness to give an explicitly trusted
    /// Tier-1 issuer. The returned clone contains both state openings.
    pub fn witness(&self) -> dregg_circuit_prove::dark_amm_private::PrivateAmmWitness {
        self.witness.clone()
    }

    /// Plaintext and deterministic fhe.rs/StdRng encryption seed for `dx`.
    /// This is secret issuer input, not public receipt material.
    pub const fn dx_opening_material(&self) -> (u16, [u8; 32]) {
        (self.witness.dx, self.dx_encryption_seed)
    }

    /// Plaintext and deterministic fhe.rs/StdRng encryption seed for `dy`.
    /// This is secret issuer input, not public receipt material.
    pub const fn dy_opening_material(&self) -> (u16, [u8; 32]) {
        (self.witness.dy, self.dy_encryption_seed)
    }

    /// Rebuild every public binding before the private material is endorsed.
    pub fn validate_bundle(
        &self,
        public: &DarkAmmPublicSession,
        request: &ProvedEncryptedSwapRequest,
    ) -> Result<(), DarkAmmGameError> {
        if self.hosted_session != public.session_id
            || self.sequence != public.next_sequence
            || request.encrypted.session_id != self.hosted_session
            || request.encrypted.sequence != self.sequence
        {
            return Err(DarkAmmGameError::Refused(
                "private authority names a different hosted session or sequence".to_string(),
            ));
        }
        validate_statement_against_context(
            request.statement,
            public.proof_context.ok_or_else(|| {
                DarkAmmGameError::Refused(
                    "public session is legacy encrypted-only, not proof-required".to_string(),
                )
            })?,
            public.k,
        )?;
        let reconstructed = dregg_circuit_prove::dark_amm_private::statement(
            request.statement.session,
            &self.witness,
        )
        .map_err(DarkAmmGameError::Refused)?;
        if reconstructed != request.statement
            || self.statement_digest
                != *blake3::hash(&private_amm_statement_to_wire(request.statement)).as_bytes()
            || self.proof_digest != *blake3::hash(&request.proof_bytes).as_bytes()
            || self.request_digest != *blake3::hash(&request.to_wire_bytes()).as_bytes()
        {
            return Err(DarkAmmGameError::Refused(
                "private authority does not bind the supplied witness/statement/proof/request"
                    .to_string(),
            ));
        }
        let regenerated = produce_encrypted_swap_with_seeds(
            public,
            u64::from(self.witness.dx),
            u64::from(self.witness.dy),
            request.encrypted.dx_bound,
            request.encrypted.dy_bound,
            self.dx_encryption_seed,
            self.dy_encryption_seed,
        )?;
        if regenerated != request.encrypted {
            return Err(DarkAmmGameError::Refused(
                "private authority BFV seeds do not reproduce the exact hosted request".to_string(),
            ));
        }
        Ok(())
    }

    /// Produce one issuer's authenticated same-opening endorsement after
    /// independently reconstructing the exact public key, ciphertexts, proof,
    /// statement, and visible n=1 host-key identity from the bundle.
    ///
    /// Calling this method gives `signing_key`'s Tier-1 issuer the full private
    /// witness and both deterministic encryption seeds held by `self`.
    pub fn endorse_same_opening(
        &self,
        public: &DarkAmmPublicSession,
        request: &ProvedEncryptedSwapRequest,
        authority: &Tier1SameOpeningAuthority,
        signer_index: usize,
        signing_key: &SigningKey,
    ) -> Result<Tier1SameOpeningEndorsement, DarkAmmGameError> {
        self.validate_bundle(public, request)?;
        let objects = reconstruct_same_opening_objects(public, request)?;
        let expected = AmmSameOpeningContext {
            privacy_tier: AmmPrivacyTier::Tier1IssuerVisible,
            hosted_session: public.session_id,
            sequence: request.encrypted.sequence,
            dx_bound: request.encrypted.dx_bound,
            dy_bound: request.encrypted.dy_bound,
            params: &objects.params,
            keygen: &objects.keygen,
            collective: &objects.collective,
            dx_ciphertext: &objects.dx_ciphertext,
            dy_ciphertext: &objects.dy_ciphertext,
            proof: &objects.proof,
            statement: request.statement,
        };
        let (dx, dx_seed) = self.dx_opening_material();
        let (dy, dy_seed) = self.dy_opening_material();
        authority
            .endorse(
                &expected,
                &self.witness,
                &ExactBfvAmountOpening::new(dx, dx_seed),
                &ExactBfvAmountOpening::new(dy, dy_seed),
                signer_index,
                signing_key,
            )
            .map_err(|error| {
                DarkAmmGameError::Refused(format!(
                    "Tier-1 same-opening endorsement refused: {error}"
                ))
            })
    }

    /// Assemble a strict v3 wrapper and verify it once against an ephemeral
    /// replay guard. The hosted verifier performs the same check again against
    /// its transactional session guard before mutation.
    pub fn assemble_same_opening_request(
        &self,
        public: &DarkAmmPublicSession,
        request: ProvedEncryptedSwapRequest,
        authority: &Tier1SameOpeningAuthority,
        endorsements: &[Tier1SameOpeningEndorsement],
    ) -> Result<SameOpeningProvedEncryptedSwapRequest, DarkAmmGameError> {
        self.validate_bundle(public, &request)?;
        let receipt = authority.assemble_receipt(endorsements).map_err(|error| {
            DarkAmmGameError::Refused(format!(
                "Tier-1 same-opening receipt assembly refused: {error}"
            ))
        })?;
        let mut replay = InMemoryReplayGuard::default();
        verify_same_opening_receipt(
            public,
            &request,
            &receipt,
            authority.verifier(),
            &mut replay,
        )?;
        Ok(SameOpeningProvedEncryptedSwapRequest::new(request, receipt))
    }

    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(PRIVATE_AUTHORITY_WIRE_BYTES);
        out.extend_from_slice(PRIVATE_AUTHORITY_MAGIC);
        out.extend_from_slice(&self.hosted_session);
        put_u64(&mut out, self.sequence);
        for value in [
            self.witness.x,
            self.witness.y,
            self.witness.dx,
            self.witness.dy,
        ] {
            put_u16(&mut out, value);
        }
        for blind in [self.witness.old_blind, self.witness.new_blind] {
            for lane in blind {
                put_u32(&mut out, lane);
            }
        }
        out.extend_from_slice(&self.dx_encryption_seed);
        out.extend_from_slice(&self.dy_encryption_seed);
        out.extend_from_slice(&self.statement_digest);
        out.extend_from_slice(&self.proof_digest);
        out.extend_from_slice(&self.request_digest);
        let checksum = private_authority_checksum(&out);
        out.extend_from_slice(&checksum);
        debug_assert_eq!(out.len(), PRIVATE_AUTHORITY_WIRE_BYTES);
        out
    }

    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self, DarkAmmGameError> {
        if bytes.len() != PRIVATE_AUTHORITY_WIRE_BYTES {
            return Err(DarkAmmGameError::Malformed(format!(
                "private authority wire is {} bytes; expected {PRIVATE_AUTHORITY_WIRE_BYTES}",
                bytes.len()
            )));
        }
        let content_end = PRIVATE_AUTHORITY_WIRE_BYTES - 32;
        if bytes[content_end..] != private_authority_checksum(&bytes[..content_end]) {
            return Err(DarkAmmGameError::Malformed(
                "private authority checksum mismatch".to_string(),
            ));
        }
        let mut input = Reader::new(&bytes[..content_end]);
        if input.array::<8>()? != *PRIVATE_AUTHORITY_MAGIC {
            return Err(DarkAmmGameError::Malformed(
                "wrong private-authority version magic".to_string(),
            ));
        }
        let hosted_session = input.array()?;
        let sequence = input.u64()?;
        let x = input.u16()?;
        let y = input.u16()?;
        let dx = input.u16()?;
        let dy = input.u16()?;
        let mut old_blind = [0u32; 8];
        let mut new_blind = [0u32; 8];
        for lane in &mut old_blind {
            *lane = input.u32()?;
        }
        for lane in &mut new_blind {
            *lane = input.u32()?;
        }
        let authority = Self {
            hosted_session,
            sequence,
            witness: dregg_circuit_prove::dark_amm_private::PrivateAmmWitness::try_new(
                x, y, dx, dy, old_blind, new_blind,
            )
            .map_err(DarkAmmGameError::Refused)?,
            dx_encryption_seed: input.array()?,
            dy_encryption_seed: input.array()?,
            statement_digest: input.array()?,
            proof_digest: input.array()?,
            request_digest: input.array()?,
        };
        input.finish()?;
        if authority.to_wire_bytes() != bytes {
            return Err(DarkAmmGameError::Malformed(
                "private authority wire is not canonical".to_string(),
            ));
        }
        Ok(authority)
    }
}

impl Drop for DarkAmmPrivateSwapAuthority {
    fn drop(&mut self) {
        self.hosted_session.fill(0);
        self.witness.x = 0;
        self.witness.y = 0;
        self.witness.dx = 0;
        self.witness.dy = 0;
        self.witness.old_blind.fill(0);
        self.witness.new_blind.fill(0);
        self.dx_encryption_seed.fill(0);
        self.dy_encryption_seed.fill(0);
        self.statement_digest.fill(0);
        self.proof_digest.fill(0);
        self.request_digest.fill(0);
    }
}

fn private_authority_checksum(content: &[u8]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-dark-amm-private-authority-v1");
    hasher.update(content);
    *hasher.finalize().as_bytes()
}

/// Attach already-produced hiding receipt material to a freshly encrypted
/// candidate. This helper verifies the receipt before writing a request; the
/// host verifies it independently again before any mutation.
pub fn produce_proved_encrypted_swap<R: RngCore + CryptoRng>(
    public: &DarkAmmPublicSession,
    dx: u64,
    dy: u64,
    dx_bound: u64,
    dy_bound: u64,
    statement: PrivateAmmPublicStatement,
    proof_bytes: Vec<u8>,
    rng: &mut R,
) -> Result<ProvedEncryptedSwapRequest, DarkAmmGameError> {
    let proof_context = public.proof_context.ok_or_else(|| {
        DarkAmmGameError::Refused(
            "public session is legacy encrypted-only, not proof-required".to_string(),
        )
    })?;
    validate_statement_against_context(statement, proof_context, public.k)?;
    let proof = decode_canonical_private_amm_proof(&proof_bytes)?;
    verify_private_amm_zk(&proof, statement).map_err(DarkAmmGameError::Refused)?;
    let encrypted = produce_encrypted_swap(public, dx, dy, dx_bound, dy_bound, rng)?;
    Ok(ProvedEncryptedSwapRequest {
        encrypted,
        statement,
        proof_bytes,
    })
}

/// Proof-required producer with independent deterministic BFV openings.
///
/// Each 32-byte seed starts a fresh `rand_09::rngs::StdRng` for exactly one
/// fhe.rs public-key encryption. This is the same pinned construction consumed
/// by fhEgg's Tier-1 `ExactBfvAmountOpening`; retaining the seeds lets an issuer
/// reproduce the exact ciphertext bytes without reproving or re-encrypting the
/// hosted request.
#[allow(clippy::too_many_arguments)]
pub fn produce_proved_encrypted_swap_seeded(
    public: &DarkAmmPublicSession,
    dx: u64,
    dy: u64,
    dx_bound: u64,
    dy_bound: u64,
    statement: PrivateAmmPublicStatement,
    proof_bytes: Vec<u8>,
    dx_encryption_seed: [u8; 32],
    dy_encryption_seed: [u8; 32],
) -> Result<ProvedEncryptedSwapRequest, DarkAmmGameError> {
    let proof_context = public.proof_context.ok_or_else(|| {
        DarkAmmGameError::Refused(
            "public session is legacy encrypted-only, not proof-required".to_string(),
        )
    })?;
    validate_statement_against_context(statement, proof_context, public.k)?;
    let proof = decode_canonical_private_amm_proof(&proof_bytes)?;
    verify_private_amm_zk(&proof, statement).map_err(DarkAmmGameError::Refused)?;
    let encrypted = produce_encrypted_swap_with_seeds(
        public,
        dx,
        dy,
        dx_bound,
        dy_bound,
        dx_encryption_seed,
        dy_encryption_seed,
    )?;
    Ok(ProvedEncryptedSwapRequest {
        encrypted,
        statement,
        proof_bytes,
    })
}

fn validate_statement_against_context(
    statement: PrivateAmmPublicStatement,
    context: DarkAmmProofContext,
    k: u64,
) -> Result<(), DarkAmmGameError> {
    let expected_k = u32::try_from(k).map_err(|_| {
        DarkAmmGameError::Refused("public k cannot enter the private receipt field".to_string())
    })?;
    if statement.session != context.receipt_session {
        return Err(DarkAmmGameError::Refused(
            "private receipt names a different hosted session".to_string(),
        ));
    }
    if statement.rule != context.rule || statement.rule != PRIVATE_AMM_RULE_ID {
        return Err(DarkAmmGameError::Refused(
            "private receipt names a different transition rule".to_string(),
        ));
    }
    if statement.k != expected_k {
        return Err(DarkAmmGameError::Refused(
            "private receipt names a different public invariant".to_string(),
        ));
    }
    if statement.old_root != context.current_root {
        return Err(DarkAmmGameError::Refused(
            "private receipt old root is not the table's current root".to_string(),
        ));
    }
    Ok(())
}

/// Encrypt an honest proposed swap outside the host. Loose bounds may be wider
/// than the actual values; equality is checked homomorphically by the host.
pub fn produce_encrypted_swap<R: RngCore + CryptoRng>(
    public: &DarkAmmPublicSession,
    dx: u64,
    dy: u64,
    dx_bound: u64,
    dy_bound: u64,
    rng: &mut R,
) -> Result<EncryptedSwapRequest, DarkAmmGameError> {
    let (params, public_key) = validate_encrypted_swap_inputs(public, dx, dy, dx_bound, dy_bound)?;
    Ok(EncryptedSwapRequest {
        session_id: public.session_id,
        public_key_digest: public.public_key_digest,
        sequence: public.next_sequence,
        dx_bound,
        dy_bound,
        encrypted_dx: encrypt_private_amount(&params, &public_key, dx, rng)?,
        encrypted_dy: encrypt_private_amount(&params, &public_key, dy, rng)?,
    })
}

#[allow(clippy::too_many_arguments)]
pub fn produce_encrypted_swap_with_seeds(
    public: &DarkAmmPublicSession,
    dx: u64,
    dy: u64,
    dx_bound: u64,
    dy_bound: u64,
    dx_encryption_seed: [u8; 32],
    dy_encryption_seed: [u8; 32],
) -> Result<EncryptedSwapRequest, DarkAmmGameError> {
    let (params, public_key) = validate_encrypted_swap_inputs(public, dx, dy, dx_bound, dy_bound)?;
    let mut dx_rng = StdRng::from_seed(dx_encryption_seed);
    let mut dy_rng = StdRng::from_seed(dy_encryption_seed);
    Ok(EncryptedSwapRequest {
        session_id: public.session_id,
        public_key_digest: public.public_key_digest,
        sequence: public.next_sequence,
        dx_bound,
        dy_bound,
        encrypted_dx: encrypt_private_amount(&params, &public_key, dx, &mut dx_rng)?,
        encrypted_dy: encrypt_private_amount(&params, &public_key, dy, &mut dy_rng)?,
    })
}

fn validate_encrypted_swap_inputs(
    public: &DarkAmmPublicSession,
    dx: u64,
    dy: u64,
    dx_bound: u64,
    dy_bound: u64,
) -> Result<(Arc<BfvParameters>, PublicKey), DarkAmmGameError> {
    if dx == 0 || dy == 0 {
        return Err(DarkAmmGameError::Refused(
            "the honest producer refuses a zero-amount swap".to_string(),
        ));
    }
    if dx > dx_bound || dy > dy_bound {
        return Err(DarkAmmGameError::Refused(
            "actual amount exceeds its public declared bound".to_string(),
        ));
    }
    if dx_bound == 0
        || dy_bound == 0
        || dx_bound >= public.plaintext_modulus
        || dy_bound >= public.plaintext_modulus
    {
        return Err(DarkAmmGameError::Refused(
            "declared amount bound leaves the BFV plaintext domain".to_string(),
        ));
    }
    let params = pick_params(20);
    if parameter_digest_for(&params) != public.parameter_digest {
        return Err(DarkAmmGameError::Refused(
            "producer parameter identity differs from the table".to_string(),
        ));
    }
    let public_key = PublicKey::from_bytes(&public.public_key_bytes, &params)
        .map_err(|error| DarkAmmGameError::Fhe(error.to_string()))?;
    Ok((params, public_key))
}

fn encrypt_private_amount<R: RngCore + CryptoRng>(
    params: &Arc<BfvParameters>,
    public_key: &PublicKey,
    value: u64,
    rng: &mut R,
) -> Result<Vec<u8>, DarkAmmGameError> {
    let plaintext = Plaintext::try_encode(&[value], Encoding::simd(), params)
        .map_err(|error| DarkAmmGameError::Fhe(error.to_string()))?;
    public_key
        .try_encrypt(&plaintext, rng)
        .map(|ciphertext| ciphertext.to_bytes())
        .map_err(|error| DarkAmmGameError::Fhe(error.to_string()))
}

/// Deterministic convenience for offline tools and reproducible integration
/// tests. Production callers should generally supply an OS-seeded CSPRNG to
/// [`produce_encrypted_swap`].
pub fn produce_encrypted_swap_seeded(
    public: &DarkAmmPublicSession,
    dx: u64,
    dy: u64,
    dx_bound: u64,
    dy_bound: u64,
    encryption_seed: [u8; 32],
) -> Result<EncryptedSwapRequest, DarkAmmGameError> {
    let mut rng = StdRng::from_seed(encryption_seed);
    produce_encrypted_swap(public, dx, dy, dx_bound, dy_bound, &mut rng)
}

#[derive(Clone)]
struct AcceptedSwap {
    operation: &'static str,
    canonical_request: Vec<u8>,
    actor: DreggIdentity,
    receipt: BinaryOperationReceipt,
}

/// Publicly renderable state of one hosted private pool. Hidden reserves and
/// key material have no getters or Debug implementation.
pub struct DarkAmmGameSession {
    seed: u64,
    params: Arc<BfvParameters>,
    secret_key: SecretKey,
    pool: DarkPool,
    public: DarkAmmPublicSession,
    same_opening_replay: InMemoryReplayGuard,
    accepted: Vec<AcceptedSwap>,
}

impl DarkAmmGameSession {
    /// Current public producer context. Clone it after each accepted operation
    /// to obtain the next sequence number.
    pub fn public_session(&self) -> DarkAmmPublicSession {
        self.public.clone()
    }

    /// Number of encrypted swaps admitted by the invariant gate.
    pub fn accepted_swaps(&self) -> usize {
        self.accepted.len()
    }
}

/// A hosted private constant-product table. Deployment key material is supplied
/// explicitly and must be restored from protected storage after a restart; it
/// is never emitted by the offering or placed in the operation journal.
pub struct DarkAmmGameOffering {
    key_material: DarkAmmHostKeyMaterial,
    x0: u64,
    y0: u64,
    cap_x: u64,
    cap_y: u64,
    initial_root: Option<[u32; 8]>,
    same_opening_verifier: Option<AuthenticatedQuorumVerifier>,
}

impl DarkAmmGameOffering {
    /// The fixed end-to-end demo pool: hidden `(100, 900)`, public `k=90000`,
    /// and loose caps `(300, 1000)` supporting multiple exact swaps.
    pub fn demo(key_material: DarkAmmHostKeyMaterial) -> Self {
        Self {
            key_material,
            x0: 100,
            y0: 900,
            cap_x: 300,
            cap_y: 1000,
            initial_root: None,
            same_opening_verifier: None,
        }
    }

    /// The same fixed demo pool, but with the legacy proofless operation
    /// disabled and a caller-owned hidden-state commitment installed as the
    /// mandatory first root cursor.
    pub fn demo_proof_required(
        key_material: DarkAmmHostKeyMaterial,
        initial_root: [u32; 8],
    ) -> Result<Self, DarkAmmGameError> {
        validate_root(initial_root)?;
        Ok(Self {
            key_material,
            x0: 100,
            y0: 900,
            cap_x: 300,
            cap_y: 1000,
            initial_root: Some(initial_root),
            same_opening_verifier: None,
        })
    }

    /// The fixed demo pool with a hard v3-only boundary. The ordered issuer
    /// roster and threshold are host policy; v1 and proved-v2 are not exposed
    /// and are rejected as unknown operations.
    pub fn demo_same_opening_required(
        key_material: DarkAmmHostKeyMaterial,
        initial_root: [u32; 8],
        ordered_authority_keys: Vec<[u8; 32]>,
        authority_threshold: usize,
    ) -> Result<Self, DarkAmmGameError> {
        validate_root(initial_root)?;
        let same_opening_verifier = AuthenticatedQuorumVerifier::new(
            ordered_authority_keys,
            authority_threshold,
        )
        .map_err(|error| {
            DarkAmmGameError::Refused(format!("invalid same-opening issuer policy: {error}"))
        })?;
        Ok(Self {
            key_material,
            x0: 100,
            y0: 900,
            cap_x: 300,
            cap_y: 1000,
            initial_root: Some(initial_root),
            same_opening_verifier: Some(same_opening_verifier),
        })
    }

    /// Construct a host with explicit hidden initial reserves and public caps.
    /// Admissibility is checked again while opening each session.
    pub fn configured(
        key_material: DarkAmmHostKeyMaterial,
        x0: u64,
        y0: u64,
        cap_x: u64,
        cap_y: u64,
    ) -> Self {
        Self {
            key_material,
            x0,
            y0,
            cap_x,
            cap_y,
            initial_root: None,
            same_opening_verifier: None,
        }
    }

    /// Explicit-reserve proof-required constructor. The caller is responsible
    /// for making `initial_root` the HidingFri commitment to `(x0,y0)` under
    /// the returned session binding; the first receipt proves that opening.
    pub fn configured_proof_required(
        key_material: DarkAmmHostKeyMaterial,
        x0: u64,
        y0: u64,
        cap_x: u64,
        cap_y: u64,
        initial_root: [u32; 8],
    ) -> Result<Self, DarkAmmGameError> {
        validate_root(initial_root)?;
        Ok(Self {
            key_material,
            x0,
            y0,
            cap_x,
            cap_y,
            initial_root: Some(initial_root),
            same_opening_verifier: None,
        })
    }

    /// Explicit-reserve v3-only constructor with a configured exact-opening
    /// issuer policy.
    #[allow(clippy::too_many_arguments)]
    pub fn configured_same_opening_required(
        key_material: DarkAmmHostKeyMaterial,
        x0: u64,
        y0: u64,
        cap_x: u64,
        cap_y: u64,
        initial_root: [u32; 8],
        ordered_authority_keys: Vec<[u8; 32]>,
        authority_threshold: usize,
    ) -> Result<Self, DarkAmmGameError> {
        validate_root(initial_root)?;
        let same_opening_verifier = AuthenticatedQuorumVerifier::new(
            ordered_authority_keys,
            authority_threshold,
        )
        .map_err(|error| {
            DarkAmmGameError::Refused(format!("invalid same-opening issuer policy: {error}"))
        })?;
        Ok(Self {
            key_material,
            x0,
            y0,
            cap_x,
            cap_y,
            initial_root: Some(initial_root),
            same_opening_verifier: Some(same_opening_verifier),
        })
    }

    /// Reconstruct the public encryption context an operator publishes for a
    /// seeded session without exposing the derived secret key.
    pub fn public_session_for_seed(
        &self,
        seed: u64,
    ) -> Result<DarkAmmPublicSession, DarkAmmGameError> {
        let params = pick_params(20);
        let (_, public_key, _) = self.key_material.rebound(&params)?;
        self.public_context(seed, &params, &public_key, 0, self.cap_x, self.cap_y)
    }

    fn public_context(
        &self,
        seed: u64,
        params: &Arc<BfvParameters>,
        public_key: &PublicKey,
        next_sequence: u64,
        cap_x: u64,
        cap_y: u64,
    ) -> Result<DarkAmmPublicSession, DarkAmmGameError> {
        let public_key_bytes = public_key.to_bytes();
        if public_key_bytes.len() > MAX_CIPHERTEXT_BYTES {
            return Err(DarkAmmGameError::Refused(
                "public key exceeds the transport allocation cap".to_string(),
            ));
        }
        let public_key_digest = *blake3::hash(&public_key_bytes).as_bytes();
        let parameter_digest = parameter_digest_for(params);
        let k = self.x0.checked_mul(self.y0).ok_or_else(|| {
            DarkAmmGameError::Refused("initial invariant overflows u64".to_string())
        })?;
        let mut binding = blake3::Hasher::new_derive_key("dregg-dark-amm-public-session-v1");
        binding.update(&seed.to_le_bytes());
        binding.update(&parameter_digest);
        binding.update(&public_key_digest);
        binding.update(&k.to_le_bytes());
        binding.update(&self.cap_x.to_le_bytes());
        binding.update(&self.cap_y.to_le_bytes());
        let session_id = *binding.finalize().as_bytes();
        let proof_context = self.initial_root.map(|current_root| DarkAmmProofContext {
            receipt_session: receipt_session_for(&session_id),
            rule: PRIVATE_AMM_RULE_ID,
            current_root,
        });
        Ok(DarkAmmPublicSession {
            session_id,
            parameter_digest,
            public_key_digest,
            public_key_bytes,
            plaintext_modulus: params.plaintext(),
            degree: params.degree(),
            k,
            cap_x,
            cap_y,
            next_sequence,
            proof_context,
        })
    }

    fn open_session(&self, seed: u64) -> Result<DarkAmmGameSession, DarkAmmGameError> {
        let params = pick_params(20);
        let (secret_key, public_key, relinearization_key) = self.key_material.rebound(&params)?;
        let public = self.public_context(seed, &params, &public_key, 0, self.cap_x, self.cap_y)?;
        // Fresh encryption randomness is intentional. Replay requires the same
        // custody key and semantic initial reserves, not byte-identical reserve
        // ciphertexts; using public deterministic randomness here would destroy
        // reserve confidentiality.
        let mut pool_rng = rand_09::rng();
        let mut pool = DarkPool::init(
            &params,
            &public_key,
            &relinearization_key,
            self.x0,
            self.y0,
            self.cap_x,
            self.cap_y,
            &mut pool_rng,
        )
        .map_err(|error| DarkAmmGameError::Refused(error.to_string()))?;
        pool.strip_lp_view();
        Ok(DarkAmmGameSession {
            seed,
            params,
            secret_key,
            pool,
            public,
            same_opening_replay: InMemoryReplayGuard::default(),
            accepted: Vec::new(),
        })
    }

    fn validate_request(
        &self,
        session: &DarkAmmGameSession,
        payload: &[u8],
    ) -> Result<(EncryptedSwapRequest, BoundedCiphertext, BoundedCiphertext), BinaryOperationError>
    {
        let request = EncryptedSwapRequest::from_wire_bytes(payload)
            .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
        if request.to_wire_bytes() != payload {
            return Err(BinaryOperationError::Malformed(
                "encrypted swap is not canonically encoded".to_string(),
            ));
        }
        if request.session_id != session.public.session_id {
            return Err(BinaryOperationError::Refused(
                "encrypted swap belongs to a different pool session".to_string(),
            ));
        }
        if request.public_key_digest != session.public.public_key_digest {
            return Err(BinaryOperationError::Refused(
                "encrypted swap names a different pool public key".to_string(),
            ));
        }
        if request.sequence != session.public.next_sequence {
            return Err(BinaryOperationError::Refused(format!(
                "encrypted swap sequence mismatch: expected {}, claimed {}",
                session.public.next_sequence, request.sequence
            )));
        }
        if request.dx_bound == 0
            || request.dy_bound == 0
            || request.dx_bound >= session.public.plaintext_modulus
            || request.dy_bound >= session.public.plaintext_modulus
        {
            return Err(BinaryOperationError::Refused(
                "declared amount bounds leave the BFV plaintext domain".to_string(),
            ));
        }
        let (dx, dy) = request
            .bounded_ciphertexts(&session.params)
            .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
        Ok((request, dx, dy))
    }

    fn apply_request(
        &self,
        session: &mut DarkAmmGameSession,
        payload: &[u8],
        actor: DreggIdentity,
    ) -> Result<BinaryOperationReceipt, BinaryOperationError> {
        let (request, encrypted_dx, encrypted_dy) = self.validate_request(session, payload)?;
        let next_sequence = session.public.next_sequence.checked_add(1).ok_or_else(|| {
            BinaryOperationError::Refused("encrypted swap sequence exhausted".to_string())
        })?;
        let next_cap_x = session
            .public
            .cap_x
            .checked_add(request.dx_bound)
            .filter(|bound| *bound < session.public.plaintext_modulus)
            .ok_or_else(|| {
                BinaryOperationError::Refused(
                    "public x-cap would leave the BFV plaintext domain".to_string(),
                )
            })?;
        let candidate = session
            .pool
            .try_private_swap_proposed(&encrypted_dx, &encrypted_dy)
            .map_err(|error| BinaryOperationError::Refused(error.to_string()))?;
        let opened = open_invariant(&session.secret_key, &candidate).map_err(|error| {
            BinaryOperationError::Refused(format!("invariant decrypt boundary failed: {error}"))
        })?;
        if opened != session.public.k {
            // Do not echo `opened`: the current single-key host observed it,
            // but the HTTP/bot refusal need not amplify that residual.
            return Err(BinaryOperationError::Refused(
                "encrypted swap failed the constant-product equality; state is unchanged (the current demo host inspected the raw rejected product)"
                    .to_string(),
            ));
        }
        session
            .pool
            .commit_private(candidate, opened)
            .map_err(|error| BinaryOperationError::Refused(error.to_string()))?;

        let canonical_request = request.to_wire_bytes();
        let request_digest = *blake3::hash(&canonical_request).as_bytes();
        let mut receipt_hash =
            blake3::Hasher::new_derive_key("dregg-dark-amm-operation-receipt-v1");
        receipt_hash.update(&session.public.session_id);
        receipt_hash.update(&dark_amm_player_binding(session.public.session_id, &actor));
        receipt_hash.update(&request.sequence.to_le_bytes());
        receipt_hash.update(&request_digest);
        let receipt_id = *receipt_hash.finalize().as_bytes();
        session.public.next_sequence = next_sequence;
        session.public.cap_x = next_cap_x;
        // The current encrypted-state API conservatively retains cap_y after
        // a private subtraction because dy may be zero.
        let receipt = BinaryOperationReceipt {
            operation: DARK_AMM_OPERATION.to_string(),
            receipt_id,
            public_fields: vec![
                ("sequence".to_string(), request.sequence.to_string()),
                ("invariant".to_string(), session.public.k.to_string()),
                ("requestDigest".to_string(), hex32(&request_digest)),
                (
                    "acceptedSwaps".to_string(),
                    session.public.next_sequence.to_string(),
                ),
            ],
        };
        session.accepted.push(AcceptedSwap {
            operation: DARK_AMM_OPERATION,
            canonical_request,
            actor,
            receipt: receipt.clone(),
        });
        Ok(receipt)
    }

    fn validate_proved_request(
        &self,
        session: &DarkAmmGameSession,
        payload: &[u8],
    ) -> Result<
        (
            ProvedEncryptedSwapRequest,
            BoundedCiphertext,
            BoundedCiphertext,
        ),
        BinaryOperationError,
    > {
        let request = ProvedEncryptedSwapRequest::from_wire_bytes(payload)
            .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
        if request.to_wire_bytes() != payload {
            return Err(BinaryOperationError::Malformed(
                "proved encrypted swap is not canonically encoded".to_string(),
            ));
        }
        let context = session.public.proof_context.ok_or_else(|| {
            BinaryOperationError::Refused(
                "this table is legacy encrypted-only and cannot accept proved-v2 requests"
                    .to_string(),
            )
        })?;
        validate_statement_against_context(request.statement, context, session.public.k)
            .map_err(|error| BinaryOperationError::Refused(error.to_string()))?;
        let proof = decode_canonical_private_amm_proof(&request.proof_bytes)
            .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
        verify_private_amm_zk(&proof, request.statement).map_err(|error| {
            BinaryOperationError::Refused(format!(
                "private AMM hiding receipt verification failed: {error}"
            ))
        })?;
        let encrypted_wire = request.encrypted.to_wire_bytes();
        let (_, encrypted_dx, encrypted_dy) = self.validate_request(session, &encrypted_wire)?;
        Ok((request, encrypted_dx, encrypted_dy))
    }

    fn apply_proved_request(
        &self,
        session: &mut DarkAmmGameSession,
        payload: &[u8],
        actor: DreggIdentity,
    ) -> Result<BinaryOperationReceipt, BinaryOperationError> {
        // All public pins and the hiding proof are checked before constructing,
        // opening, or committing an encrypted candidate.
        let (request, encrypted_dx, encrypted_dy) =
            self.validate_proved_request(session, payload)?;
        let next_sequence = session.public.next_sequence.checked_add(1).ok_or_else(|| {
            BinaryOperationError::Refused("encrypted swap sequence exhausted".to_string())
        })?;
        let next_cap_x = session
            .public
            .cap_x
            .checked_add(request.encrypted.dx_bound)
            .filter(|bound| *bound < session.public.plaintext_modulus)
            .ok_or_else(|| {
                BinaryOperationError::Refused(
                    "public x-cap would leave the BFV plaintext domain".to_string(),
                )
            })?;
        let candidate = session
            .pool
            .try_private_swap_proposed(&encrypted_dx, &encrypted_dy)
            .map_err(|error| BinaryOperationError::Refused(error.to_string()))?;
        let opened = open_invariant(&session.secret_key, &candidate).map_err(|error| {
            BinaryOperationError::Refused(format!("invariant decrypt boundary failed: {error}"))
        })?;
        if opened != session.public.k {
            return Err(BinaryOperationError::Refused(
                "encrypted candidate failed the public constant-product equality after the hiding receipt verified; state and root are unchanged (BFV/proof same-opening is not yet proved)"
                    .to_string(),
            ));
        }
        session
            .pool
            .commit_private(candidate, opened)
            .map_err(|error| BinaryOperationError::Refused(error.to_string()))?;

        let canonical_request = request.to_wire_bytes();
        let request_digest = *blake3::hash(&canonical_request).as_bytes();
        let statement_wire = private_amm_statement_to_wire(request.statement);
        let statement_digest = *blake3::hash(&statement_wire).as_bytes();
        let proof_digest = *blake3::hash(&request.proof_bytes).as_bytes();
        let mut receipt_hash =
            blake3::Hasher::new_derive_key("dregg-dark-amm-proved-operation-receipt-v2");
        receipt_hash.update(&session.public.session_id);
        receipt_hash.update(&dark_amm_player_binding(session.public.session_id, &actor));
        receipt_hash.update(&request.encrypted.sequence.to_le_bytes());
        receipt_hash.update(&statement_digest);
        receipt_hash.update(&proof_digest);
        receipt_hash.update(&request_digest);
        let receipt_id = *receipt_hash.finalize().as_bytes();

        let context = session
            .public
            .proof_context
            .as_mut()
            .expect("proved validation required a proof context");
        context.current_root = request.statement.new_root;
        session.public.next_sequence = next_sequence;
        session.public.cap_x = next_cap_x;
        let receipt = BinaryOperationReceipt {
            operation: DARK_AMM_PROVED_OPERATION.to_string(),
            receipt_id,
            public_fields: vec![
                (
                    "sequence".to_string(),
                    request.encrypted.sequence.to_string(),
                ),
                ("invariant".to_string(), session.public.k.to_string()),
                ("statementDigest".to_string(), hex32(&statement_digest)),
                ("proofDigest".to_string(), hex32(&proof_digest)),
                ("requestDigest".to_string(), hex32(&request_digest)),
                ("newRoot".to_string(), hex_root(&request.statement.new_root)),
                (
                    "acceptedSwaps".to_string(),
                    session.public.next_sequence.to_string(),
                ),
            ],
        };
        session.accepted.push(AcceptedSwap {
            operation: DARK_AMM_PROVED_OPERATION,
            canonical_request,
            actor,
            receipt: receipt.clone(),
        });
        Ok(receipt)
    }

    fn validate_same_opening_request<R: ReplayGuard>(
        &self,
        session: &DarkAmmGameSession,
        payload: &[u8],
        replay: &mut R,
    ) -> Result<
        (
            SameOpeningProvedEncryptedSwapRequest,
            BoundedCiphertext,
            BoundedCiphertext,
            [u8; 32],
        ),
        BinaryOperationError,
    > {
        let request = SameOpeningProvedEncryptedSwapRequest::from_wire_bytes(payload)
            .map_err(|error| BinaryOperationError::Malformed(error.to_string()))?;
        if request.to_wire_bytes() != payload {
            return Err(BinaryOperationError::Malformed(
                "same-opening encrypted swap is not canonically encoded".to_string(),
            ));
        }
        let verifier = self.same_opening_verifier.as_ref().ok_or_else(|| {
            BinaryOperationError::Refused(
                "this table is not configured for proved same-opening v3".to_string(),
            )
        })?;
        let proved_wire = request.proved.to_wire_bytes();
        let (proved, encrypted_dx, encrypted_dy) =
            self.validate_proved_request(session, &proved_wire)?;
        let claim_digest = verify_same_opening_receipt(
            &session.public,
            &proved,
            &request.same_opening_receipt,
            verifier,
            replay,
        )
        .map_err(|error| BinaryOperationError::Refused(error.to_string()))?;
        Ok((request, encrypted_dx, encrypted_dy, claim_digest))
    }

    fn apply_same_opening_request(
        &self,
        session: &mut DarkAmmGameSession,
        payload: &[u8],
        actor: DreggIdentity,
    ) -> Result<BinaryOperationReceipt, BinaryOperationError> {
        // Receipt replay is transactional with the candidate mutation. A
        // rejected proof/candidate never consumes the live hosted replay slot.
        let mut next_replay = session.same_opening_replay.clone();
        let (request, encrypted_dx, encrypted_dy, same_opening_claim_digest) =
            self.validate_same_opening_request(session, payload, &mut next_replay)?;
        let next_sequence = session.public.next_sequence.checked_add(1).ok_or_else(|| {
            BinaryOperationError::Refused("encrypted swap sequence exhausted".to_string())
        })?;
        let next_cap_x = session
            .public
            .cap_x
            .checked_add(request.proved.encrypted.dx_bound)
            .filter(|bound| *bound < session.public.plaintext_modulus)
            .ok_or_else(|| {
                BinaryOperationError::Refused(
                    "public x-cap would leave the BFV plaintext domain".to_string(),
                )
            })?;
        let candidate = session
            .pool
            .try_private_swap_proposed(&encrypted_dx, &encrypted_dy)
            .map_err(|error| BinaryOperationError::Refused(error.to_string()))?;
        let opened = open_invariant(&session.secret_key, &candidate).map_err(|error| {
            BinaryOperationError::Refused(format!("invariant decrypt boundary failed: {error}"))
        })?;
        if opened != session.public.k {
            return Err(BinaryOperationError::Refused(
                "same-opening-authorized encrypted candidate failed the public constant-product equality; state, root, and receipt replay cursor are unchanged"
                    .to_string(),
            ));
        }
        session
            .pool
            .commit_private(candidate, opened)
            .map_err(|error| BinaryOperationError::Refused(error.to_string()))?;

        let canonical_request = request.to_wire_bytes();
        let request_digest = *blake3::hash(&canonical_request).as_bytes();
        let statement_wire = private_amm_statement_to_wire(request.proved.statement);
        let statement_digest = *blake3::hash(&statement_wire).as_bytes();
        let proof_digest = *blake3::hash(&request.proved.proof_bytes).as_bytes();
        let mut receipt_hash =
            blake3::Hasher::new_derive_key("dregg-dark-amm-same-opening-operation-receipt-v3");
        receipt_hash.update(&session.public.session_id);
        receipt_hash.update(&dark_amm_player_binding(session.public.session_id, &actor));
        receipt_hash.update(&request.proved.encrypted.sequence.to_le_bytes());
        receipt_hash.update(&statement_digest);
        receipt_hash.update(&proof_digest);
        receipt_hash.update(&same_opening_claim_digest);
        receipt_hash.update(&request_digest);
        let receipt_id = *receipt_hash.finalize().as_bytes();

        let context = session
            .public
            .proof_context
            .as_mut()
            .expect("same-opening validation required a proof context");
        context.current_root = request.proved.statement.new_root;
        session.public.next_sequence = next_sequence;
        session.public.cap_x = next_cap_x;
        session.same_opening_replay = next_replay;
        let receipt = BinaryOperationReceipt {
            operation: DARK_AMM_SAME_OPENING_OPERATION.to_string(),
            receipt_id,
            public_fields: vec![
                (
                    "sequence".to_string(),
                    request.proved.encrypted.sequence.to_string(),
                ),
                ("invariant".to_string(), session.public.k.to_string()),
                ("statementDigest".to_string(), hex32(&statement_digest)),
                ("proofDigest".to_string(), hex32(&proof_digest)),
                (
                    "sameOpeningClaimDigest".to_string(),
                    hex32(&same_opening_claim_digest),
                ),
                ("requestDigest".to_string(), hex32(&request_digest)),
                (
                    "newRoot".to_string(),
                    hex_root(&request.proved.statement.new_root),
                ),
                (
                    "bfvCustody".to_string(),
                    "n=1/opening-threshold=1".to_string(),
                ),
                (
                    "acceptedSwaps".to_string(),
                    session.public.next_sequence.to_string(),
                ),
            ],
        };
        session.accepted.push(AcceptedSwap {
            operation: DARK_AMM_SAME_OPENING_OPERATION,
            canonical_request,
            actor,
            receipt: receipt.clone(),
        });
        Ok(receipt)
    }
}

impl Offering for DarkAmmGameOffering {
    type Session = DarkAmmGameSession;

    fn open(&self, cfg: SessionConfig) -> Result<Self::Session, OfferingError> {
        self.open_session(cfg.seed.unwrap_or(1))
            .map_err(|error| OfferingError::Deploy(error.to_string()))
    }

    fn actions(&self, _session: &Self::Session) -> Vec<Action> {
        Vec::new()
    }

    fn advance(
        &self,
        _session: &mut Self::Session,
        _input: Action,
        _actor: DreggIdentity,
    ) -> Outcome {
        Outcome::Refused(
            "this Dark Pool accepts only its encrypted binary-operation affordance".to_string(),
        )
    }

    fn verify(&self, session: &Self::Session) -> VerifyReport {
        let mut replay = match self.open_session(session.seed) {
            Ok(replay) => replay,
            Err(error) => return VerifyReport::broken(0, error.to_string()),
        };
        for (index, accepted) in session.accepted.iter().enumerate() {
            let result = match accepted.operation {
                DARK_AMM_OPERATION => self.apply_request(
                    &mut replay,
                    &accepted.canonical_request,
                    accepted.actor.clone(),
                ),
                DARK_AMM_PROVED_OPERATION => self.apply_proved_request(
                    &mut replay,
                    &accepted.canonical_request,
                    accepted.actor.clone(),
                ),
                DARK_AMM_SAME_OPENING_OPERATION => self.apply_same_opening_request(
                    &mut replay,
                    &accepted.canonical_request,
                    accepted.actor.clone(),
                ),
                operation => Err(BinaryOperationError::UnknownOperation(
                    operation.to_string(),
                )),
            };
            match result {
                Ok(receipt) if receipt == accepted.receipt => {}
                Ok(_) => {
                    return VerifyReport::broken(
                        index,
                        "encrypted-swap replay produced a different public receipt",
                    );
                }
                Err(error) => {
                    return VerifyReport::broken(
                        index,
                        format!("encrypted-swap replay refused: {error}"),
                    );
                }
            }
        }
        let mut report = VerifyReport::ok(session.accepted.len());
        report.detail = if self.same_opening_verifier.is_some() {
            format!(
                "{} exact-opening Dark Pool swap(s) re-verified from HidingFri proofs, Tier-1 quorum receipts, and canonical encrypted requests; issuer-visible witness and single-host n=1 BFV custody remain disclosed",
                session.accepted.len()
            )
        } else if self.initial_root.is_some() {
            format!(
                "{} shielded Dark Pool swap(s) re-verified from hiding receipts and canonical encrypted requests; BFV same-opening and threshold custody remain residual",
                session.accepted.len()
            )
        } else {
            format!(
                "{} encrypted Dark Pool swap(s) re-verified from canonical ciphertext requests; demo single-key boundary",
                session.accepted.len()
            )
        };
        report
    }

    fn render(&self, session: &Self::Session) -> Surface {
        Surface(ViewNode::Section {
            title: "The Dark Bazaar — encrypted constant-product table".to_string(),
            tag: "accent".to_string(),
            children: vec![
                ViewNode::Section {
                    title: "Private pool state".to_string(),
                    tag: "genuine".to_string(),
                    children: vec![
                        ViewNode::Text(format!(
                            "{} encrypted swap(s) accepted · public invariant k={} · next sequence {}",
                            session.accepted.len(),
                            session.public.k,
                            session.public.next_sequence
                        )),
                        ViewNode::Text(format!(
                            "pool session {} · public key {}",
                            short_hex(&session.public.session_id),
                            short_hex(&session.public.public_key_digest)
                        )),
                        ViewNode::Text(
                            "Reserve x, reserve y, dx, and dy are absent from this public surface."
                                .to_string(),
                        ),
                        if let Some(proof) = session.public.proof_context {
                            ViewNode::Text(format!(
                                "{} · rule {} · current root {}",
                                if self.same_opening_verifier.is_some() {
                                    "Hiding + Tier-1 exact-opening receipts required"
                                } else {
                                    "Hiding receipt required"
                                },
                                proof.rule,
                                short_root(&proof.current_root)
                            ))
                        } else {
                            ViewNode::Text(
                                "Legacy encrypted-only mode · no hiding receipt claimed."
                                    .to_string(),
                            )
                        },
                    ],
                },
                ViewNode::Section {
                    title: "Boundary".to_string(),
                    tag: "muted".to_string(),
                    children: vec![ViewNode::Text(
                        if self.same_opening_verifier.is_some() {
                            DARK_AMM_SAME_OPENING_DISCLOSURE
                        } else if session.public.proof_context.is_some() {
                            DARK_AMM_PROVED_DISCLOSURE
                        } else {
                            DARK_AMM_DISCLOSURE
                        }
                        .to_string(),
                    )],
                },
            ],
        })
    }

    fn binary_operations(&self, _session: &Self::Session) -> Vec<BinaryOperationDescriptor> {
        if self.same_opening_verifier.is_some() {
            vec![BinaryOperationDescriptor {
                name: DARK_AMM_SAME_OPENING_OPERATION.to_string(),
                title: "Verify proof + Tier-1 exact openings and apply the encrypted Dark Pool candidate"
                    .to_string(),
                input_media_type: DARK_AMM_SAME_OPENING_MEDIA_TYPE.to_string(),
                max_input_bytes: MAX_DARK_AMM_REQUEST_BYTES,
                disclosure: DARK_AMM_SAME_OPENING_DISCLOSURE.to_string(),
            }]
        } else if self.initial_root.is_some() {
            vec![BinaryOperationDescriptor {
                name: DARK_AMM_PROVED_OPERATION.to_string(),
                title: "Verify a hiding receipt and apply its encrypted Dark Pool candidate"
                    .to_string(),
                input_media_type: DARK_AMM_PROVED_MEDIA_TYPE.to_string(),
                max_input_bytes: MAX_DARK_AMM_REQUEST_BYTES,
                disclosure: DARK_AMM_PROVED_DISCLOSURE.to_string(),
            }]
        } else {
            vec![BinaryOperationDescriptor {
                name: DARK_AMM_OPERATION.to_string(),
                title: "Submit an encrypted Dark Pool swap".to_string(),
                input_media_type: DARK_AMM_MEDIA_TYPE.to_string(),
                max_input_bytes: MAX_DARK_AMM_REQUEST_BYTES,
                disclosure: DARK_AMM_DISCLOSURE.to_string(),
            }]
        }
    }

    fn binary_operation_replay_material(
        &self,
        session: &Self::Session,
        name: &str,
        payload: &[u8],
    ) -> Result<Option<BinaryOperationReplayMaterial>, BinaryOperationError> {
        match name {
            DARK_AMM_OPERATION if self.initial_root.is_none() => {
                let (request, _, _) = self.validate_request(session, payload)?;
                Ok(Some(BinaryOperationReplayMaterial::new(
                    request.to_wire_bytes(),
                    DARK_AMM_DISCLOSURE,
                )))
            }
            DARK_AMM_PROVED_OPERATION if self.initial_root.is_some() => {
                if self.same_opening_verifier.is_some() {
                    return Err(BinaryOperationError::UnknownOperation(name.to_string()));
                }
                let (request, _, _) = self.validate_proved_request(session, payload)?;
                Ok(Some(BinaryOperationReplayMaterial::new(
                    request.to_wire_bytes(),
                    DARK_AMM_PROVED_DISCLOSURE,
                )))
            }
            DARK_AMM_SAME_OPENING_OPERATION if self.same_opening_verifier.is_some() => {
                // Descriptor/journal preflight must not consume the live replay
                // cursor. invoke performs the same verification against a
                // clone and commits that clone only with the state transition.
                let mut replay = session.same_opening_replay.clone();
                let (request, _, _, _) =
                    self.validate_same_opening_request(session, payload, &mut replay)?;
                Ok(Some(BinaryOperationReplayMaterial::new(
                    request.to_wire_bytes(),
                    DARK_AMM_SAME_OPENING_DISCLOSURE,
                )))
            }
            _ => Err(BinaryOperationError::UnknownOperation(name.to_string())),
        }
    }

    fn invoke_binary_operation(
        &self,
        session: &mut Self::Session,
        name: &str,
        payload: &[u8],
        actor: DreggIdentity,
    ) -> Result<BinaryOperationReceipt, BinaryOperationError> {
        match name {
            DARK_AMM_OPERATION if self.initial_root.is_none() => {
                self.apply_request(session, payload, actor)
            }
            DARK_AMM_PROVED_OPERATION if self.initial_root.is_some() => {
                if self.same_opening_verifier.is_some() {
                    return Err(BinaryOperationError::UnknownOperation(name.to_string()));
                }
                self.apply_proved_request(session, payload, actor)
            }
            DARK_AMM_SAME_OPENING_OPERATION if self.same_opening_verifier.is_some() => {
                self.apply_same_opening_request(session, payload, actor)
            }
            _ => Err(BinaryOperationError::UnknownOperation(name.to_string())),
        }
    }

    fn price(&self, _input: &Action) -> RunCost {
        RunCost::free()
    }
}

fn open_invariant(
    secret_key: &SecretKey,
    candidate: &PrivateAppliedSwap,
) -> Result<u64, DarkAmmGameError> {
    let plaintext = secret_key
        .try_decrypt(&candidate.invariant.ct)
        .map_err(|error| DarkAmmGameError::Fhe(error.to_string()))?;
    let slots = Vec::<u64>::try_decode(&plaintext, Encoding::simd())
        .map_err(|error| DarkAmmGameError::Fhe(error.to_string()))?;
    slots.first().copied().ok_or_else(|| {
        DarkAmmGameError::Malformed("decrypted invariant has no SIMD slot".to_string())
    })
}

/// Bind a routed player to one pool's public cryptographic identity without
/// publishing that player in the operation's small public consequence fields.
///
/// The length prefix is load-bearing: [`DreggIdentity`] is an opaque string,
/// so concatenating it with future receipt material without a boundary would
/// make distinct tuples share one transcript. Every Dark AMM receipt family
/// absorbs this same digest before its request/proof-specific material. This
/// makes a durable operation-journal actor substitution reproduce a different
/// receipt and therefore fail exact replay verification.
fn dark_amm_player_binding(session_id: [u8; 32], actor: &DreggIdentity) -> [u8; 32] {
    let actor = actor.as_str().as_bytes();
    let mut binding = blake3::Hasher::new_derive_key("dregg-dark-amm-player-operation-binding-v1");
    binding.update(DARK_AMM_OFFERING_KEY.as_bytes());
    binding.update(&session_id);
    binding.update(&(actor.len() as u64).to_le_bytes());
    binding.update(actor);
    *binding.finalize().as_bytes()
}

fn parameter_digest_for(params: &BfvParameters) -> [u8; 32] {
    canonical_bfv_parameters_digest(params)
}

fn receipt_session_for(session_id: &[u8; 32]) -> u32 {
    u32::from_le_bytes(session_id[..4].try_into().expect("fixed prefix")) % BABYBEAR_P
}

fn validate_root(root: [u32; 8]) -> Result<(), DarkAmmGameError> {
    if let Some((lane, value)) = root
        .into_iter()
        .enumerate()
        .find(|(_, value)| *value >= BABYBEAR_P)
    {
        return Err(DarkAmmGameError::Refused(format!(
            "initial private-AMM root lane {lane}={value} is noncanonical"
        )));
    }
    Ok(())
}

fn hex_root(root: &[u32; 8]) -> String {
    root.iter()
        .map(|lane| format!("{lane:08x}"))
        .collect::<Vec<_>>()
        .join(":")
}

fn short_root(root: &[u32; 8]) -> String {
    format!("{:08x}…{:08x}", root[0], root[7])
}

fn put_u32(out: &mut Vec<u8>, value: u32) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_u16(out: &mut Vec<u8>, value: u16) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_u64(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_le_bytes());
}

fn put_bytes(out: &mut Vec<u8>, bytes: &[u8]) {
    put_u64(out, bytes.len() as u64);
    out.extend_from_slice(bytes);
}

struct Reader<'a> {
    bytes: &'a [u8],
    position: usize,
}

impl<'a> Reader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, position: 0 }
    }

    fn array<const N: usize>(&mut self) -> Result<[u8; N], DarkAmmGameError> {
        let end = self
            .position
            .checked_add(N)
            .ok_or_else(|| DarkAmmGameError::Malformed("wire position overflow".to_string()))?;
        let slice = self.bytes.get(self.position..end).ok_or_else(|| {
            DarkAmmGameError::Malformed("truncated fixed-width field".to_string())
        })?;
        self.position = end;
        Ok(slice.try_into().expect("length checked"))
    }

    fn u64(&mut self) -> Result<u64, DarkAmmGameError> {
        Ok(u64::from_le_bytes(self.array()?))
    }

    fn u32(&mut self) -> Result<u32, DarkAmmGameError> {
        Ok(u32::from_le_bytes(self.array()?))
    }

    fn u16(&mut self) -> Result<u16, DarkAmmGameError> {
        Ok(u16::from_le_bytes(self.array()?))
    }

    fn bytes(&mut self, max: usize) -> Result<&'a [u8], DarkAmmGameError> {
        let len_u64 = self.u64()?;
        let len = usize::try_from(len_u64).map_err(|_| {
            DarkAmmGameError::Malformed("declared length does not fit usize".to_string())
        })?;
        if len > max {
            return Err(DarkAmmGameError::Malformed(format!(
                "declared byte field is {len}; maximum is {max}"
            )));
        }
        let end = self
            .position
            .checked_add(len)
            .ok_or_else(|| DarkAmmGameError::Malformed("wire position overflow".to_string()))?;
        let slice = self
            .bytes
            .get(self.position..end)
            .ok_or_else(|| DarkAmmGameError::Malformed("truncated byte field".to_string()))?;
        self.position = end;
        Ok(slice)
    }

    fn finish(self) -> Result<(), DarkAmmGameError> {
        if self.position == self.bytes.len() {
            Ok(())
        } else {
            Err(DarkAmmGameError::Malformed(
                "trailing bytes after canonical object".to_string(),
            ))
        }
    }
}

fn hex32(bytes: &[u8; 32]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn short_hex(bytes: &[u8; 32]) -> String {
    let full = hex32(bytes);
    format!("{}…{}", &full[..12], &full[52..])
}
