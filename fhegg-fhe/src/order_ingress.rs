//! Authenticated, replay-resistant ingress for trader-encrypted fhEgg orders.
//!
//! The plaintext [`Order`](crate::Order) exists only at
//! [`SignedOrderSubmission::encrypt_and_sign`], which is intended to run in the
//! trader process.  The clearing coordinator parses a strict wire envelope,
//! verifies its Ed25519 attribution and public session binding, rejects a reused
//! `(trader, sequence)` source id, and receives only a
//! [`CollectiveOrderRow`](crate::additive::CollectiveOrderRow).  Accepted rows
//! are sorted canonically before folding, and the returned input bindings cover
//! both the exact ciphertext and its authenticated source message for inclusion
//! in an [`AttestedClearingReceipt`](crate::attestation::AttestedClearingReceipt).
//!
//! # Honest boundary
//!
//! Signatures prove attribution, session agreement, and exact-byte integrity;
//! they are not a proof of plaintext validity.  The optional
//! [`OrderEncryptionOpening`] path is stronger but deliberately not ZK: an
//! operator that already knows the order can reproduce the exact randomized
//! BFV encryption and obtain a non-serializable
//! [`VerifiedOrderSourceBinding`].  It closes same-opening and unary-row
//! well-formedness for that operator-visible ingress tier.  A house-blind
//! deployment still needs a lattice ZK encryption/range proof.  Asset ownership
//! remains a separate ledger-source obligation.

use std::collections::HashSet;
use std::fmt;

use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use fhe_traits::Serialize as FheSerialize;
use rand_09::RngCore;
use sha2::{Digest, Sha256};

use crate::additive::{
    encrypt_collective_order_with_seed, CollectiveFoldError, CollectiveIngressTiming,
    CollectiveOrderRow,
};
use crate::attestation::{BfvPublicIdentity, Digest32, InputDigest};
use crate::bfv_lean::LeanCiphertext;
use crate::threshold::{BfvParams, CollectivePublicKey};
use crate::{Order, Side};

const SESSION_DOMAIN: &[u8] = b"fhegg/order-ingress/session/v1";
const MESSAGE_DOMAIN: &[u8] = b"fhegg/order-ingress/message/v1";
const SIGNATURE_DOMAIN: &[u8] = b"fhegg/order-ingress/signature/v1";
const ENCRYPTION_RANDOMNESS_DOMAIN: &[u8] = b"fhegg/order-ingress/encryption-randomness/v1";
const VERIFIED_SOURCE_DOMAIN: &[u8] = b"fhegg/order-ingress/verified-source/v1";
const SOURCE_CERTIFICATE_DOMAIN: &[u8] = b"fhegg/order-ingress/source-certificate/v1";
const LISTING_CERTIFICATE_DOMAIN: &[u8] = b"fhegg/order-ingress/listing-certificate/v1";
const SOURCE_ACTOR_DOMAIN: &[u8] = b"fhegg/order-ingress/market-actor/v1";
const WIRE_MAGIC: &[u8; 8] = b"FHORv001";
const CERTIFICATE_WIRE_MAGIC: &[u8; 8] = b"FHSCv001";
const LISTING_CERTIFICATE_WIRE_MAGIC: &[u8; 8] = b"FHLCv001";

fn digest_parts(domain: &[u8], parts: &[&[u8]]) -> Digest32 {
    let mut hasher = Sha256::new();
    hasher.update((domain.len() as u64).to_be_bytes());
    hasher.update(domain);
    for part in parts {
        hasher.update((part.len() as u64).to_be_bytes());
        hasher.update(part);
    }
    hasher.finalize().into()
}

#[allow(clippy::too_many_arguments)]
fn verified_source_digest(
    session_nonce: &Digest32,
    session_digest: &Digest32,
    trader: usize,
    sequence: u64,
    side_tag: u8,
    limit: usize,
    qty: u16,
    message_digest: &Digest32,
    ciphertext_digest: &Digest32,
) -> Digest32 {
    let trader = (trader as u64).to_be_bytes();
    let sequence = sequence.to_be_bytes();
    let side = [side_tag];
    let limit = (limit as u64).to_be_bytes();
    let qty = u64::from(qty).to_be_bytes();
    digest_parts(
        VERIFIED_SOURCE_DOMAIN,
        &[
            session_nonce,
            session_digest,
            &trader,
            &sequence,
            &side,
            &limit,
            &qty,
            message_digest,
            ciphertext_digest,
        ],
    )
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OrderIngressSession {
    nonce: Digest32,
    k: usize,
    degree: usize,
    plaintext_modulus: u64,
    moduli_digest: Digest32,
    collective_public_key_digest: Digest32,
    encryption_domain_digest: Digest32,
    digest: Digest32,
}

impl OrderIngressSession {
    pub fn new(
        nonce: Digest32,
        k: usize,
        params: &BfvParams,
        public_key: &CollectivePublicKey,
    ) -> Result<Self> {
        if k == 0 || k > params.degree() {
            return Err(OrderIngressError::InvalidParameters);
        }
        let mut moduli = Vec::with_capacity(8 + params.moduli().len() * 8);
        moduli.extend_from_slice(&(params.moduli().len() as u64).to_be_bytes());
        for &modulus in params.moduli() {
            moduli.extend_from_slice(&modulus.to_be_bytes());
        }
        let moduli_digest = digest_parts(SESSION_DOMAIN, &[b"moduli", &moduli]);
        let collective_public_key_digest = digest_parts(
            SESSION_DOMAIN,
            &[b"collective-public-key", &public_key.pk.to_bytes()],
        );
        let encryption_domain_digest =
            BfvPublicIdentity::encryption_domain_digest_from_public(params, public_key);
        let k_bytes = (k as u64).to_be_bytes();
        let digest = digest_parts(
            SESSION_DOMAIN,
            &[&nonce, &k_bytes, &encryption_domain_digest],
        );
        Ok(Self {
            nonce,
            k,
            degree: params.degree(),
            plaintext_modulus: params.plaintext_modulus(),
            moduli_digest,
            collective_public_key_digest,
            encryption_domain_digest,
            digest,
        })
    }

    pub fn nonce(&self) -> Digest32 {
        self.nonce
    }

    pub fn buckets(&self) -> usize {
        self.k
    }

    pub fn digest(&self) -> Digest32 {
        self.digest
    }

    /// Reconstruct the exact ingress-session digest from the independently
    /// retained BFV identity in a clearing claim. This is the relying-market
    /// join that prevents a certificate opened under one public key or
    /// parameter set from authorizing a computation under another.
    pub fn digest_for_bfv_identity(
        nonce: Digest32,
        k: usize,
        bfv: &BfvPublicIdentity,
    ) -> Result<Digest32> {
        let degree =
            usize::try_from(bfv.degree).map_err(|_| OrderIngressError::InvalidParameters)?;
        if k == 0 || k > degree {
            return Err(OrderIngressError::InvalidParameters);
        }
        let k_bytes = (k as u64).to_be_bytes();
        Ok(digest_parts(
            SESSION_DOMAIN,
            &[&nonce, &k_bytes, &bfv.encryption_domain_digest()],
        ))
    }

    fn matches_params(&self, params: &BfvParams) -> bool {
        if self.degree != params.degree() || self.plaintext_modulus != params.plaintext_modulus() {
            return false;
        }
        let mut moduli = Vec::with_capacity(8 + params.moduli().len() * 8);
        moduli.extend_from_slice(&(params.moduli().len() as u64).to_be_bytes());
        for &modulus in params.moduli() {
            moduli.extend_from_slice(&modulus.to_be_bytes());
        }
        self.moduli_digest == digest_parts(SESSION_DOMAIN, &[b"moduli", &moduli])
    }
}

/// Secret verifier opening for one randomized BFV encryption.
///
/// This is not a zero-knowledge proof.  Revealing it to a verifier that knows a
/// candidate order lets that verifier reproduce and compare the complete
/// ciphertext.  It is intended for today's explicitly operator-visible CRAWL
/// boundary and must not be placed in public receipts or durable public replay
/// material.
#[derive(Clone, Copy)]
pub struct OrderEncryptionOpening {
    seed: Digest32,
}

impl OrderEncryptionOpening {
    /// Deterministic constructor for reproducible trader clients and tests.  A
    /// production trader should supply a fresh uniformly random seed.
    pub const fn from_seed(seed: Digest32) -> Self {
        Self { seed }
    }
}

/// Capability-like result of checking signature attribution and reproducing
/// the exact BFV ciphertext from one plaintext order and randomness opening.
///
/// Fields are private and there is no wire decoder: safe Rust callers can only
/// obtain this value from [`AuthenticatedOrderBook::accept_opened`].  It is
/// evidence local to the verifier, not a transferable ZK proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifiedOrderSourceBinding {
    session_nonce: Digest32,
    session_digest: Digest32,
    trader: usize,
    sequence: u64,
    side_tag: u8,
    limit: usize,
    qty: u16,
    message_digest: Digest32,
    ciphertext_digest: Digest32,
    binding_digest: Digest32,
}

impl VerifiedOrderSourceBinding {
    pub const fn session_nonce(&self) -> Digest32 {
        self.session_nonce
    }

    pub const fn session_digest(&self) -> Digest32 {
        self.session_digest
    }

    pub const fn trader(&self) -> usize {
        self.trader
    }

    pub const fn sequence(&self) -> u64 {
        self.sequence
    }

    pub const fn side(&self) -> Side {
        match self.side_tag {
            0 => Side::Bid,
            _ => Side::Ask,
        }
    }

    pub const fn limit(&self) -> usize {
        self.limit
    }

    pub const fn qty(&self) -> u16 {
        self.qty
    }

    pub const fn message_digest(&self) -> Digest32 {
        self.message_digest
    }

    pub const fn ciphertext_digest(&self) -> Digest32 {
        self.ciphertext_digest
    }

    /// Domain-separated digest placed inside the market's sealed commitment.
    /// It covers the exact signed source, exact ciphertext, and the plaintext
    /// order whose encryption was reproduced locally.
    pub const fn binding_digest(&self) -> Digest32 {
        self.binding_digest
    }

    /// Issue a transferable attestation from the operator that performed the
    /// exact reencryption check.  This is an ordinary signature under a relying-
    /// market-selected source-verifier key, not a ZK proof and not a trader
    /// self-assertion.  It deliberately reveals the already operator-visible
    /// order tuple but never the encryption randomness opening.
    pub fn certify_for_market(
        &self,
        actor_identity: &[u8],
        source_verifier: &SigningKey,
    ) -> OrderSourceCertificate {
        let mut certificate = OrderSourceCertificate {
            session_nonce: self.session_nonce,
            session_digest: self.session_digest,
            actor_digest: digest_parts(SOURCE_ACTOR_DOMAIN, &[actor_identity]),
            trader: self.trader,
            sequence: self.sequence,
            side_tag: self.side_tag,
            limit: self.limit,
            qty: self.qty,
            message_digest: self.message_digest,
            ciphertext_digest: self.ciphertext_digest,
            binding_digest: self.binding_digest,
            signature: [0; 64],
        };
        certificate.signature = source_verifier
            .sign(&certificate.signing_message())
            .to_bytes();
        certificate
    }

    /// Issue the listing-side analogue, additionally binding the exact asset
    /// identifier into the configured source verifier's signature. The nested
    /// order certificate still proves only that this verifier performed the
    /// operator-visible exact-opening check; neither signature is a ZK proof.
    pub fn certify_listing_for_market(
        &self,
        actor_identity: &[u8],
        asset: Digest32,
        source_verifier: &SigningKey,
    ) -> ListingOrderSourceCertificate {
        let source = self.certify_for_market(actor_identity, source_verifier);
        let mut certificate = ListingOrderSourceCertificate {
            asset,
            source,
            signature: [0; 64],
        };
        certificate.signature = source_verifier
            .sign(&certificate.signing_message())
            .to_bytes();
        certificate
    }
}

/// Replayable certificate that a configured source verifier performed the
/// operator-visible exact-encryption opening check.
///
/// It is safe to persist because it contains only public digests plus the order
/// tuple already visible to the current CRAWL operator; the BFV randomness
/// opening is absent.  Its security is the honesty and key custody of the
/// configured source verifier, not zero knowledge.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OrderSourceCertificate {
    session_nonce: Digest32,
    session_digest: Digest32,
    actor_digest: Digest32,
    trader: usize,
    sequence: u64,
    side_tag: u8,
    limit: usize,
    qty: u16,
    message_digest: Digest32,
    ciphertext_digest: Digest32,
    binding_digest: Digest32,
    signature: [u8; 64],
}

impl OrderSourceCertificate {
    pub const fn session_nonce(&self) -> Digest32 {
        self.session_nonce
    }

    pub const fn session_digest(&self) -> Digest32 {
        self.session_digest
    }

    pub const fn trader(&self) -> usize {
        self.trader
    }

    pub const fn sequence(&self) -> u64 {
        self.sequence
    }

    pub const fn side(&self) -> Side {
        match self.side_tag {
            0 => Side::Bid,
            _ => Side::Ask,
        }
    }

    pub const fn limit(&self) -> usize {
        self.limit
    }

    pub const fn qty(&self) -> u16 {
        self.qty
    }

    pub const fn message_digest(&self) -> Digest32 {
        self.message_digest
    }

    pub const fn ciphertext_digest(&self) -> Digest32 {
        self.ciphertext_digest
    }

    pub const fn binding_digest(&self) -> Digest32 {
        self.binding_digest
    }

    pub fn actor_matches(&self, actor_identity: &[u8]) -> bool {
        self.actor_digest == digest_parts(SOURCE_ACTOR_DOMAIN, &[actor_identity])
    }

    pub fn verify(&self, source_verifier: &VerifyingKey) -> Result<()> {
        let expected_binding = verified_source_digest(
            &self.session_nonce,
            &self.session_digest,
            self.trader,
            self.sequence,
            self.side_tag,
            self.limit,
            self.qty,
            &self.message_digest,
            &self.ciphertext_digest,
        );
        if self.binding_digest != expected_binding {
            return Err(OrderIngressError::InvalidSourceCertificate);
        }
        source_verifier
            .verify_strict(
                &self.signing_message(),
                &Signature::from_bytes(&self.signature),
            )
            .map_err(|_| OrderIngressError::InvalidSourceCertificate)
    }

    fn unsigned_wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(251);
        out.extend_from_slice(CERTIFICATE_WIRE_MAGIC);
        out.extend_from_slice(&self.session_nonce);
        out.extend_from_slice(&self.session_digest);
        out.extend_from_slice(&self.actor_digest);
        out.extend_from_slice(&(self.trader as u64).to_be_bytes());
        out.extend_from_slice(&self.sequence.to_be_bytes());
        out.push(self.side_tag);
        out.extend_from_slice(&(self.limit as u64).to_be_bytes());
        out.extend_from_slice(&self.qty.to_be_bytes());
        out.extend_from_slice(&self.message_digest);
        out.extend_from_slice(&self.ciphertext_digest);
        out.extend_from_slice(&self.binding_digest);
        out
    }

    fn signing_message(&self) -> Digest32 {
        digest_parts(SOURCE_CERTIFICATE_DOMAIN, &[&self.unsigned_wire_bytes()])
    }

    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = self.unsigned_wire_bytes();
        out.extend_from_slice(&self.signature);
        out
    }

    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self> {
        let mut cursor = 0usize;
        if take::<8>(bytes, &mut cursor)? != *CERTIFICATE_WIRE_MAGIC {
            return Err(OrderIngressError::MalformedWire);
        }
        let session_nonce = take::<32>(bytes, &mut cursor)?;
        let session_digest = take::<32>(bytes, &mut cursor)?;
        let actor_digest = take::<32>(bytes, &mut cursor)?;
        let trader = usize::try_from(u64::from_be_bytes(take::<8>(bytes, &mut cursor)?))
            .map_err(|_| OrderIngressError::MalformedWire)?;
        let sequence = u64::from_be_bytes(take::<8>(bytes, &mut cursor)?);
        let side_tag = take::<1>(bytes, &mut cursor)?[0];
        if side_tag > 1 {
            return Err(OrderIngressError::MalformedWire);
        }
        let limit = usize::try_from(u64::from_be_bytes(take::<8>(bytes, &mut cursor)?))
            .map_err(|_| OrderIngressError::MalformedWire)?;
        let qty = u16::from_be_bytes(take::<2>(bytes, &mut cursor)?);
        let message_digest = take::<32>(bytes, &mut cursor)?;
        let ciphertext_digest = take::<32>(bytes, &mut cursor)?;
        let binding_digest = take::<32>(bytes, &mut cursor)?;
        let signature = take::<64>(bytes, &mut cursor)?;
        if cursor != bytes.len() {
            return Err(OrderIngressError::MalformedWire);
        }
        Ok(Self {
            session_nonce,
            session_digest,
            actor_digest,
            trader,
            sequence,
            side_tag,
            limit,
            qty,
            message_digest,
            ciphertext_digest,
            binding_digest,
            signature,
        })
    }
}

/// Replayable listing-source certificate: an exact opened encrypted ask plus
/// the concrete asset identifier the seller is offering.
///
/// The nested [`OrderSourceCertificate`] binds actor/session/order/ciphertext;
/// an additional source-verifier signature binds the asset to that exact
/// certificate. It contains no BFV randomness opening and makes no ZK claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ListingOrderSourceCertificate {
    asset: Digest32,
    source: OrderSourceCertificate,
    signature: [u8; 64],
}

impl ListingOrderSourceCertificate {
    pub const fn asset(&self) -> Digest32 {
        self.asset
    }

    pub const fn session_nonce(&self) -> Digest32 {
        self.source.session_nonce()
    }

    pub const fn session_digest(&self) -> Digest32 {
        self.source.session_digest()
    }

    pub const fn side(&self) -> Side {
        self.source.side()
    }

    pub const fn limit(&self) -> usize {
        self.source.limit()
    }

    pub const fn qty(&self) -> u16 {
        self.source.qty()
    }

    pub const fn message_digest(&self) -> Digest32 {
        self.source.message_digest()
    }

    pub const fn ciphertext_digest(&self) -> Digest32 {
        self.source.ciphertext_digest()
    }

    pub const fn binding_digest(&self) -> Digest32 {
        self.source.binding_digest()
    }

    pub fn actor_matches(&self, actor_identity: &[u8]) -> bool {
        self.source.actor_matches(actor_identity)
    }

    pub fn verify(&self, source_verifier: &VerifyingKey) -> Result<()> {
        self.source.verify(source_verifier)?;
        source_verifier
            .verify_strict(
                &self.signing_message(),
                &Signature::from_bytes(&self.signature),
            )
            .map_err(|_| OrderIngressError::InvalidSourceCertificate)
    }

    fn signing_message(&self) -> Digest32 {
        digest_parts(
            LISTING_CERTIFICATE_DOMAIN,
            &[&self.asset, &self.source.to_wire_bytes()],
        )
    }

    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let source = self.source.to_wire_bytes();
        let mut out = Vec::with_capacity(8 + 32 + source.len() + 64);
        out.extend_from_slice(LISTING_CERTIFICATE_WIRE_MAGIC);
        out.extend_from_slice(&self.asset);
        out.extend_from_slice(&source);
        out.extend_from_slice(&self.signature);
        out
    }

    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self> {
        const PREFIX: usize = 8 + 32;
        const SIGNATURE: usize = 64;
        if bytes.len() <= PREFIX + SIGNATURE || bytes[..8] != *LISTING_CERTIFICATE_WIRE_MAGIC {
            return Err(OrderIngressError::MalformedWire);
        }
        let asset = bytes[8..PREFIX]
            .try_into()
            .map_err(|_| OrderIngressError::MalformedWire)?;
        let source_end = bytes.len() - SIGNATURE;
        let source = OrderSourceCertificate::from_wire_bytes(&bytes[PREFIX..source_end])?;
        let signature = bytes[source_end..]
            .try_into()
            .map_err(|_| OrderIngressError::MalformedWire)?;
        Ok(Self {
            asset,
            source,
            signature,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OrderIngressError {
    InvalidParameters,
    EmptyRoster,
    RosterTooLarge,
    InvalidPublicKey { trader: usize },
    DuplicatePublicKey { trader: usize },
    InvalidTrader { trader: usize, roster_len: usize },
    SessionMismatch,
    DuplicateSource { trader: usize, sequence: u64 },
    InvalidSignature { trader: usize },
    EncryptionOpeningMismatch { trader: usize },
    DuplicatePrivateBookEncryptionSeed,
    InvalidSourceCertificate,
    MalformedWire,
    Fold(CollectiveFoldError),
}

impl fmt::Display for OrderIngressError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "authenticated order ingress error: {self:?}")
    }
}

impl std::error::Error for OrderIngressError {}

impl From<CollectiveFoldError> for OrderIngressError {
    fn from(value: CollectiveFoldError) -> Self {
        Self::Fold(value)
    }
}

pub type Result<T> = std::result::Result<T, OrderIngressError>;

/// A strict signed ciphertext envelope.  No plaintext order fields are stored.
#[derive(Clone, Debug)]
pub struct SignedOrderSubmission {
    session_digest: Digest32,
    trader: usize,
    sequence: u64,
    side: Side,
    ciphertext: LeanCiphertext,
    signature: [u8; 64],
}

impl SignedOrderSubmission {
    /// Trader-local encryption and signing.  The plaintext order is consumed by
    /// this call and is absent from the returned object and wire bytes.
    pub fn encrypt_and_sign(
        session: &OrderIngressSession,
        trader: usize,
        sequence: u64,
        order: &Order,
        params: &BfvParams,
        public_key: &CollectivePublicKey,
        signing_key: &SigningKey,
    ) -> Result<(Self, CollectiveIngressTiming)> {
        let mut seed = [0u8; 32];
        rand_09::rng().fill_bytes(&mut seed);
        let (submission, _, timing) = Self::encrypt_and_sign_with_opening(
            session,
            trader,
            sequence,
            order,
            params,
            public_key,
            signing_key,
            OrderEncryptionOpening::from_seed(seed),
        )?;
        Ok((submission, timing))
    }

    /// Trader-local encryption that additionally returns the secret exact-
    /// reencryption opening.  The submission remains the same public wire shape;
    /// the opening is never serialized into it.
    pub fn encrypt_and_sign_openable(
        session: &OrderIngressSession,
        trader: usize,
        sequence: u64,
        order: &Order,
        params: &BfvParams,
        public_key: &CollectivePublicKey,
        signing_key: &SigningKey,
    ) -> Result<(Self, OrderEncryptionOpening, CollectiveIngressTiming)> {
        let mut seed = [0u8; 32];
        rand_09::rng().fill_bytes(&mut seed);
        Self::encrypt_and_sign_with_opening(
            session,
            trader,
            sequence,
            order,
            params,
            public_key,
            signing_key,
            OrderEncryptionOpening::from_seed(seed),
        )
    }

    /// Deterministic form for clients that own their randomness source.  Reusing
    /// an opening is discouraged; the actual RNG seed is additionally derived
    /// from the session/trader/sequence tuple.
    pub fn encrypt_and_sign_with_opening(
        session: &OrderIngressSession,
        trader: usize,
        sequence: u64,
        order: &Order,
        params: &BfvParams,
        public_key: &CollectivePublicKey,
        signing_key: &SigningKey,
        opening: OrderEncryptionOpening,
    ) -> Result<(Self, OrderEncryptionOpening, CollectiveIngressTiming)> {
        let rebuilt = OrderIngressSession::new(session.nonce, session.k, params, public_key)?;
        if &rebuilt != session {
            return Err(OrderIngressError::SessionMismatch);
        }
        let rng_seed = encryption_rng_seed(session, trader, sequence, opening);
        let (row, timing) =
            encrypt_collective_order_with_seed(order, session.k, params, public_key, rng_seed)?;
        let mut submission = Self {
            session_digest: session.digest,
            trader,
            sequence,
            side: row.side(),
            ciphertext: row.into_ciphertext(),
            signature: [0; 64],
        };
        submission.signature = signing_key.sign(&submission.signing_message()).to_bytes();
        Ok((submission, opening, timing))
    }

    /// Trader-local ingress for the canonical side-hiding private-book row.
    ///
    /// Unlike [`Self::encrypt_and_sign_with_opening`], this does **not** create
    /// the older side-specific unary ciphertext.  The returned submission
    /// carries the exact nine-live-slot ciphertext later consumed by the
    /// private-root Bulletproof and by `fold_private_book_ciphertexts`.
    /// `encryption_seed` is deliberately returned only by caller custody; it is
    /// never serialized into the signed submission.
    #[cfg(feature = "amm-input-binding")]
    #[allow(clippy::too_many_arguments)]
    pub fn encrypt_and_sign_private_book_row(
        session: &OrderIngressSession,
        trader: usize,
        sequence: u64,
        private_order: dregg_circuit_prove::dark_bazaar_private::PrivateOrder,
        encryption_seed: Digest32,
        params: &BfvParams,
        public_key: &CollectivePublicKey,
        signing_key: &SigningKey,
    ) -> Result<Self> {
        use dregg_circuit_prove::dark_bazaar_private::{self, Side as PrivateSide};

        if session.k != dark_bazaar_private::PRICE_COUNT
            || trader >= dark_bazaar_private::ORDER_COUNT
        {
            return Err(OrderIngressError::InvalidParameters);
        }
        let rebuilt = OrderIngressSession::new(session.nonce, session.k, params, public_key)?;
        if &rebuilt != session {
            return Err(OrderIngressError::SessionMismatch);
        }
        let side = match private_order.side {
            PrivateSide::Bid => Side::Bid,
            PrivateSide::Ask => Side::Ask,
        };
        let ciphertext = crate::private_book_relation::encrypt_private_book_row(
            trader,
            private_order,
            encryption_seed,
            params,
            public_key,
        )
        .map_err(|_| OrderIngressError::EncryptionOpeningMismatch { trader })?;
        let mut submission = Self {
            session_digest: session.digest,
            trader,
            sequence,
            side,
            ciphertext,
            signature: [0; 64],
        };
        submission.signature = signing_key.sign(&submission.signing_message()).to_bytes();
        Ok(submission)
    }

    pub fn trader(&self) -> usize {
        self.trader
    }

    pub fn sequence(&self) -> u64 {
        self.sequence
    }

    pub fn side(&self) -> Side {
        self.side
    }

    pub fn ciphertext(&self) -> &LeanCiphertext {
        &self.ciphertext
    }

    fn side_tag(&self) -> u8 {
        match self.side {
            Side::Bid => 0,
            Side::Ask => 1,
        }
    }

    fn message_digest(&self) -> Digest32 {
        let trader = (self.trader as u64).to_be_bytes();
        let sequence = self.sequence.to_be_bytes();
        let side = [self.side_tag()];
        let plain_bound = self.ciphertext.plain_bound.to_be_bytes();
        let ciphertext = self.ciphertext.to_fhe_bytes();
        digest_parts(
            MESSAGE_DOMAIN,
            &[
                &self.session_digest,
                &trader,
                &sequence,
                &side,
                &plain_bound,
                &ciphertext,
            ],
        )
    }

    fn signing_message(&self) -> Digest32 {
        digest_parts(SIGNATURE_DOMAIN, &[&self.message_digest()])
    }

    fn verify_encryption_opening(
        &self,
        order: &Order,
        opening: OrderEncryptionOpening,
        session: &OrderIngressSession,
        params: &BfvParams,
        public_key: &CollectivePublicKey,
    ) -> Result<VerifiedOrderSourceBinding> {
        let rebuilt = OrderIngressSession::new(session.nonce, session.k, params, public_key)?;
        if &rebuilt != session || self.session_digest != session.digest {
            return Err(OrderIngressError::SessionMismatch);
        }
        let rng_seed = encryption_rng_seed(session, self.trader, self.sequence, opening);
        let (expected, _) =
            encrypt_collective_order_with_seed(order, session.k, params, public_key, rng_seed)?;
        let exact = self.side_tag()
            == match order.side {
                Side::Bid => 0,
                Side::Ask => 1,
            }
            && self.ciphertext.plain_bound == u64::from(order.qty)
            && self.ciphertext.to_fhe_bytes() == expected.ciphertext().to_fhe_bytes();
        if !exact {
            return Err(OrderIngressError::EncryptionOpeningMismatch {
                trader: self.trader,
            });
        }

        let message_digest = self.message_digest();
        let ciphertext_digest = InputDigest::ciphertext(&self.ciphertext).digest;
        let binding_digest = verified_source_digest(
            &session.nonce,
            &self.session_digest,
            self.trader,
            self.sequence,
            self.side_tag(),
            order.limit,
            order.qty,
            &message_digest,
            &ciphertext_digest,
        );
        Ok(VerifiedOrderSourceBinding {
            session_nonce: session.nonce,
            session_digest: self.session_digest,
            trader: self.trader,
            sequence: self.sequence,
            side_tag: self.side_tag(),
            limit: order.limit,
            qty: order.qty,
            message_digest,
            ciphertext_digest,
            binding_digest,
        })
    }

    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let ciphertext = self.ciphertext.to_fhe_bytes();
        let mut out = Vec::with_capacity(145 + ciphertext.len());
        out.extend_from_slice(WIRE_MAGIC);
        out.extend_from_slice(&self.session_digest);
        out.extend_from_slice(&(self.trader as u64).to_be_bytes());
        out.extend_from_slice(&self.sequence.to_be_bytes());
        out.push(self.side_tag());
        out.extend_from_slice(&self.ciphertext.plain_bound.to_be_bytes());
        out.extend_from_slice(&(ciphertext.len() as u64).to_be_bytes());
        out.extend_from_slice(&ciphertext);
        out.extend_from_slice(&self.signature);
        out
    }

    pub fn from_wire_bytes(
        bytes: &[u8],
        session: &OrderIngressSession,
        params: &BfvParams,
    ) -> Result<Self> {
        if !session.matches_params(params) {
            return Err(OrderIngressError::InvalidParameters);
        }
        let mut cursor = 0usize;
        if take::<8>(bytes, &mut cursor)? != *WIRE_MAGIC {
            return Err(OrderIngressError::MalformedWire);
        }
        let session_digest = take::<32>(bytes, &mut cursor)?;
        if session_digest != session.digest {
            return Err(OrderIngressError::SessionMismatch);
        }
        let trader = usize::try_from(u64::from_be_bytes(take::<8>(bytes, &mut cursor)?))
            .map_err(|_| OrderIngressError::MalformedWire)?;
        let sequence = u64::from_be_bytes(take::<8>(bytes, &mut cursor)?);
        let side = match take::<1>(bytes, &mut cursor)?[0] {
            0 => Side::Bid,
            1 => Side::Ask,
            _ => return Err(OrderIngressError::MalformedWire),
        };
        let plain_bound = u64::from_be_bytes(take::<8>(bytes, &mut cursor)?);
        let ciphertext_len = usize::try_from(u64::from_be_bytes(take::<8>(bytes, &mut cursor)?))
            .map_err(|_| OrderIngressError::MalformedWire)?;
        let ciphertext_end = cursor
            .checked_add(ciphertext_len)
            .filter(|&end| end <= bytes.len())
            .ok_or(OrderIngressError::MalformedWire)?;
        let ciphertext = LeanCiphertext::from_fhe_bytes(
            &bytes[cursor..ciphertext_end],
            params.moduli(),
            params.degree(),
            plain_bound,
        )
        .map_err(|_| OrderIngressError::MalformedWire)?;
        cursor = ciphertext_end;
        let signature = take::<64>(bytes, &mut cursor)?;
        if cursor != bytes.len() {
            return Err(OrderIngressError::MalformedWire);
        }
        Ok(Self {
            session_digest,
            trader,
            sequence,
            side,
            ciphertext,
            signature,
        })
    }
}

fn encryption_rng_seed(
    session: &OrderIngressSession,
    trader: usize,
    sequence: u64,
    opening: OrderEncryptionOpening,
) -> Digest32 {
    digest_parts(
        ENCRYPTION_RANDOMNESS_DOMAIN,
        &[
            &opening.seed,
            &session.digest,
            &(trader as u64).to_be_bytes(),
            &sequence.to_be_bytes(),
        ],
    )
}

fn take<const N: usize>(bytes: &[u8], cursor: &mut usize) -> Result<[u8; N]> {
    let end = cursor
        .checked_add(N)
        .filter(|&end| end <= bytes.len())
        .ok_or(OrderIngressError::MalformedWire)?;
    let value = bytes[*cursor..end]
        .try_into()
        .map_err(|_| OrderIngressError::MalformedWire)?;
    *cursor = end;
    Ok(value)
}

/// Authenticated coordinator state.  It has no API accepting a plaintext order.
pub struct AuthenticatedOrderBook {
    session: OrderIngressSession,
    ordered_public_keys: Vec<[u8; 32]>,
    seen_sources: HashSet<(usize, u64)>,
    accepted: Vec<SignedOrderSubmission>,
    #[cfg(feature = "amm-input-binding")]
    private_book_sources: HashSet<(usize, u64)>,
    #[cfg(feature = "amm-input-binding")]
    private_book_seeds: HashSet<Digest32>,
}

impl AuthenticatedOrderBook {
    pub fn new(session: OrderIngressSession, ordered_public_keys: Vec<[u8; 32]>) -> Result<Self> {
        if ordered_public_keys.is_empty() {
            return Err(OrderIngressError::EmptyRoster);
        }
        if ordered_public_keys.len() > u32::MAX as usize {
            return Err(OrderIngressError::RosterTooLarge);
        }
        let mut seen = HashSet::with_capacity(ordered_public_keys.len());
        for (trader, key) in ordered_public_keys.iter().enumerate() {
            let verifying = VerifyingKey::from_bytes(key)
                .map_err(|_| OrderIngressError::InvalidPublicKey { trader })?;
            if verifying.is_weak() {
                return Err(OrderIngressError::InvalidPublicKey { trader });
            }
            if !seen.insert(*key) {
                return Err(OrderIngressError::DuplicatePublicKey { trader });
            }
        }
        Ok(Self {
            session,
            ordered_public_keys,
            seen_sources: HashSet::new(),
            accepted: Vec::new(),
            #[cfg(feature = "amm-input-binding")]
            private_book_sources: HashSet::new(),
            #[cfg(feature = "amm-input-binding")]
            private_book_seeds: HashSet::new(),
        })
    }

    fn validate_submission(&self, submission: &SignedOrderSubmission) -> Result<()> {
        if submission.session_digest != self.session.digest {
            return Err(OrderIngressError::SessionMismatch);
        }
        let key = self.ordered_public_keys.get(submission.trader).ok_or(
            OrderIngressError::InvalidTrader {
                trader: submission.trader,
                roster_len: self.ordered_public_keys.len(),
            },
        )?;
        let verifying =
            VerifyingKey::from_bytes(key).map_err(|_| OrderIngressError::InvalidPublicKey {
                trader: submission.trader,
            })?;
        verifying
            .verify_strict(
                &submission.signing_message(),
                &Signature::from_bytes(&submission.signature),
            )
            .map_err(|_| OrderIngressError::InvalidSignature {
                trader: submission.trader,
            })?;
        let source = (submission.trader, submission.sequence);
        if self.seen_sources.contains(&source) {
            return Err(OrderIngressError::DuplicateSource {
                trader: source.0,
                sequence: source.1,
            });
        }
        // Strict shape/canonicality check happens after attribution, so an
        // invalid row remains attributable to its signer in caller logs.
        CollectiveOrderRow::from_lean(
            submission.side,
            submission.ciphertext.clone(),
            self.session.k,
        )?;
        Ok(())
    }

    pub fn accept(&mut self, submission: SignedOrderSubmission) -> Result<()> {
        self.validate_submission(&submission)?;
        self.seen_sources
            .insert((submission.trader, submission.sequence));
        self.accepted.push(submission);
        Ok(())
    }

    /// Verify attribution plus an exact operator-visible encryption opening,
    /// then accept the ciphertext and return a non-transferable source-binding
    /// token.  A substituted plaintext, randomness opening, ciphertext, session,
    /// or public key is refused before the source sequence is consumed.
    pub fn accept_opened(
        &mut self,
        submission: SignedOrderSubmission,
        order: &Order,
        opening: OrderEncryptionOpening,
        params: &BfvParams,
        public_key: &CollectivePublicKey,
    ) -> Result<VerifiedOrderSourceBinding> {
        self.validate_submission(&submission)?;
        let binding = submission.verify_encryption_opening(
            order,
            opening,
            &self.session,
            params,
            public_key,
        )?;
        self.seen_sources
            .insert((submission.trader, submission.sequence));
        self.accepted.push(submission);
        Ok(binding)
    }

    /// Finish canonical private-book ingress without retyping the side-hiding
    /// ciphertexts as legacy [`CollectiveOrderRow`] values.
    ///
    /// The proof worker already retains the exact [`PrivateBookCiphertexts`]
    /// that these inputs identify. Returning only signed message/ciphertext
    /// digests prevents an accidental call to the older side-partitioning fold,
    /// which would interpret the packed ask lanes incorrectly. Every accepted
    /// submission must have passed [`Self::accept_private_book_opened`].
    #[cfg(feature = "amm-input-binding")]
    pub fn finish_private_book_source_inputs(mut self) -> Result<Vec<InputDigest>> {
        if self.accepted.is_empty()
            || self.accepted.len() > dregg_circuit_prove::dark_bazaar_private::ORDER_COUNT
            || self.accepted.iter().any(|submission| {
                !self
                    .private_book_sources
                    .contains(&(submission.trader, submission.sequence))
            })
        {
            return Err(OrderIngressError::InvalidParameters);
        }
        self.accepted
            .sort_by_key(|submission| (submission.trader, submission.sequence));
        let mut ordered_inputs = Vec::with_capacity(self.accepted.len() * 2);
        for submission in self.accepted {
            ordered_inputs.push(InputDigest::commitment(submission.message_digest()));
            ordered_inputs.push(InputDigest::ciphertext(&submission.ciphertext));
        }
        Ok(ordered_inputs)
    }

    /// Accept one exact canonical private-book ciphertext after verifying both
    /// trader attribution and deterministic BFV reencryption.
    ///
    /// The resulting source certificate API is intentionally the same one used
    /// by the live Dark Bazaar board, so its WriteOnce seal can bind the exact
    /// proof row instead of a second side-specific encoding.  The current game
    /// still exposes its public one-unit side/value through the action/certificate;
    /// this method closes ciphertext equality, not that separate UI disclosure.
    #[cfg(feature = "amm-input-binding")]
    pub fn accept_private_book_opened(
        &mut self,
        submission: SignedOrderSubmission,
        private_order: dregg_circuit_prove::dark_bazaar_private::PrivateOrder,
        encryption_seed: Digest32,
        params: &BfvParams,
        public_key: &CollectivePublicKey,
    ) -> Result<VerifiedOrderSourceBinding> {
        use dregg_circuit_prove::dark_bazaar_private::{self, Side as PrivateSide};

        self.validate_submission(&submission)?;
        if self.session.k != dark_bazaar_private::PRICE_COUNT
            || submission.trader >= dark_bazaar_private::ORDER_COUNT
        {
            return Err(OrderIngressError::InvalidParameters);
        }
        let expected = crate::private_book_relation::encrypt_private_book_row(
            submission.trader,
            private_order,
            encryption_seed,
            params,
            public_key,
        )
        .map_err(|_| OrderIngressError::EncryptionOpeningMismatch {
            trader: submission.trader,
        })?;
        let side_tag = match private_order.side {
            PrivateSide::Bid => 0,
            PrivateSide::Ask => 1,
        };
        let exact = submission.side_tag() == side_tag
            && submission.ciphertext.plain_bound
                == crate::private_book_relation::PRIVATE_BOOK_PUBLIC_BOUND
            && submission.ciphertext.to_fhe_bytes() == expected.to_fhe_bytes();
        if !exact {
            return Err(OrderIngressError::EncryptionOpeningMismatch {
                trader: submission.trader,
            });
        }
        if self.private_book_seeds.contains(&encryption_seed) {
            return Err(OrderIngressError::DuplicatePrivateBookEncryptionSeed);
        }

        let message_digest = submission.message_digest();
        let ciphertext_digest = InputDigest::ciphertext(&submission.ciphertext).digest;
        let binding_digest = verified_source_digest(
            &self.session.nonce,
            &submission.session_digest,
            submission.trader,
            submission.sequence,
            side_tag,
            private_order.limit as usize,
            u16::from(private_order.qty),
            &message_digest,
            &ciphertext_digest,
        );
        let binding = VerifiedOrderSourceBinding {
            session_nonce: self.session.nonce,
            session_digest: submission.session_digest,
            trader: submission.trader,
            sequence: submission.sequence,
            side_tag,
            limit: private_order.limit as usize,
            qty: u16::from(private_order.qty),
            message_digest,
            ciphertext_digest,
            binding_digest,
        };
        self.seen_sources
            .insert((submission.trader, submission.sequence));
        self.private_book_sources
            .insert((submission.trader, submission.sequence));
        self.private_book_seeds.insert(encryption_seed);
        self.accepted.push(submission);
        Ok(binding)
    }

    pub fn finish(mut self) -> AuthenticatedOrderBatch {
        self.accepted
            .sort_by_key(|submission| (submission.trader, submission.sequence));
        let mut rows = Vec::with_capacity(self.accepted.len());
        let mut ordered_inputs = Vec::with_capacity(self.accepted.len() * 2);
        for submission in self.accepted {
            ordered_inputs.push(InputDigest::commitment(submission.message_digest()));
            ordered_inputs.push(InputDigest::ciphertext(&submission.ciphertext));
            rows.push(
                CollectiveOrderRow::from_lean(
                    submission.side,
                    submission.ciphertext,
                    self.session.k,
                )
                .expect("accepted row was already strictly validated"),
            );
        }
        AuthenticatedOrderBatch {
            rows,
            ordered_inputs,
        }
    }
}

/// Canonically ordered encrypted rows plus their attestation bindings.
pub struct AuthenticatedOrderBatch {
    rows: Vec<CollectiveOrderRow>,
    ordered_inputs: Vec<InputDigest>,
}

impl AuthenticatedOrderBatch {
    pub fn len(&self) -> usize {
        self.rows.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    pub fn ordered_inputs(&self) -> &[InputDigest] {
        &self.ordered_inputs
    }

    pub fn into_parts(self) -> (Vec<CollectiveOrderRow>, Vec<InputDigest>) {
        (self.rows, self.ordered_inputs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::threshold::{KeygenCoordinator, KeygenSession, ThresholdParty};

    fn collective_key(params: &BfvParams, seed: Digest32) -> (KeygenSession, CollectivePublicKey) {
        let session = KeygenSession::from_seed(1, seed).unwrap();
        let (party, contribution) = ThresholdParty::join(&session, 0, params).unwrap();
        let mut coordinator = KeygenCoordinator::new(session.clone(), params.clone());
        coordinator.accept(contribution).unwrap();
        drop(party);
        (session, coordinator.finish().unwrap())
    }

    #[test]
    fn exact_opening_and_source_certificate_refuse_order_ciphertext_actor_and_signature_substitution(
    ) {
        let params = BfvParams::fold_set();
        let (keygen, collective) = collective_key(&params, [0x21; 32]);
        let ingress = OrderIngressSession::new([0x31; 32], 4, &params, &collective).unwrap();
        let bfv = BfvPublicIdentity::from_public(&params, &keygen, &collective);
        assert_eq!(
            ingress.digest(),
            OrderIngressSession::digest_for_bfv_identity([0x31; 32], 4, &bfv).unwrap()
        );
        let (_, wrong_collective) = collective_key(&params, [0x22; 32]);
        let wrong_bfv = BfvPublicIdentity::from_public(&params, &keygen, &wrong_collective);
        assert_ne!(
            ingress.digest(),
            OrderIngressSession::digest_for_bfv_identity([0x31; 32], 4, &wrong_bfv).unwrap(),
            "a certificate from another collective key must not join this clearing"
        );
        let trader_key = SigningKey::from_bytes(&[0x41; 32]);
        let source_verifier = SigningKey::from_bytes(&[0x51; 32]);
        let order = Order {
            side: Side::Bid,
            limit: 3,
            qty: 1,
        };
        let opening = OrderEncryptionOpening::from_seed([0x61; 32]);
        let (submission, _, _) = SignedOrderSubmission::encrypt_and_sign_with_opening(
            &ingress,
            0,
            7,
            &order,
            &params,
            &collective,
            &trader_key,
            opening,
        )
        .unwrap();

        let mut book = AuthenticatedOrderBook::new(
            ingress.clone(),
            vec![trader_key.verifying_key().to_bytes()],
        )
        .unwrap();
        let substituted_order = Order {
            side: Side::Bid,
            limit: 2,
            qty: 1,
        };
        assert_eq!(
            book.accept_opened(
                submission.clone(),
                &substituted_order,
                opening,
                &params,
                &collective,
            ),
            Err(OrderIngressError::EncryptionOpeningMismatch { trader: 0 })
        );

        // A separately valid ciphertext still cannot open as the original
        // order, even with a fresh valid trader signature.
        let (other_ciphertext, _, _) = SignedOrderSubmission::encrypt_and_sign_with_opening(
            &ingress,
            0,
            7,
            &substituted_order,
            &params,
            &collective,
            &trader_key,
            OrderEncryptionOpening::from_seed([0x62; 32]),
        )
        .unwrap();
        assert_eq!(
            book.accept_opened(other_ciphertext, &order, opening, &params, &collective),
            Err(OrderIngressError::EncryptionOpeningMismatch { trader: 0 })
        );

        let binding = book
            .accept_opened(submission, &order, opening, &params, &collective)
            .expect("the exact signed encryption opens");
        let certificate = binding.certify_for_market(b"alice", &source_verifier);
        let wire = certificate.to_wire_bytes();
        let decoded = OrderSourceCertificate::from_wire_bytes(&wire).unwrap();
        decoded.verify(&source_verifier.verifying_key()).unwrap();
        assert!(decoded.actor_matches(b"alice"));
        assert!(!decoded.actor_matches(b"mallory"));

        let listing = binding.certify_listing_for_market(b"alice", [0x71; 32], &source_verifier);
        let listing_wire = listing.to_wire_bytes();
        let decoded_listing =
            ListingOrderSourceCertificate::from_wire_bytes(&listing_wire).unwrap();
        decoded_listing
            .verify(&source_verifier.verifying_key())
            .unwrap();
        assert_eq!(decoded_listing.asset(), [0x71; 32]);
        let mut substituted_asset = listing_wire;
        substituted_asset[8] ^= 1;
        let substituted_asset =
            ListingOrderSourceCertificate::from_wire_bytes(&substituted_asset).unwrap();
        assert_eq!(
            substituted_asset.verify(&source_verifier.verifying_key()),
            Err(OrderIngressError::InvalidSourceCertificate)
        );

        // Even a valid verifier signature cannot bless a certificate whose
        // advertised binding digest is inconsistent with its signed fields.
        let mut inconsistent = decoded.clone();
        inconsistent.binding_digest[0] ^= 1;
        inconsistent.signature = source_verifier
            .sign(&inconsistent.signing_message())
            .to_bytes();
        assert_eq!(
            inconsistent.verify(&source_verifier.verifying_key()),
            Err(OrderIngressError::InvalidSourceCertificate)
        );

        let mut tampered = wire;
        *tampered.last_mut().unwrap() ^= 1;
        let tampered = OrderSourceCertificate::from_wire_bytes(&tampered).unwrap();
        assert_eq!(
            tampered.verify(&source_verifier.verifying_key()),
            Err(OrderIngressError::InvalidSourceCertificate)
        );
    }
}
