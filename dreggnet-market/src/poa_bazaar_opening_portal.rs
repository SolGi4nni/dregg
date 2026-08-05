//! Native opening-aware ingress for the Lean-owned Path of Angels Bazaar.
//!
//! The payload consumed here composes two attestations under a deployment-
//! selected source-verifier key:
//!
//! 1. fhEgg's [`OrderSourceCertificate`] says that the verifier checked the
//!    trader signature and reproduced the exact BFV encryption for one order;
//! 2. this certificate binds that source result to the complete PoA envelope
//!    coordinates: actor, round, batch, nullifier, ciphertext commitment and
//!    signature commitment, plus the exact V1 slot/order.
//!
//! The exchange certificate composes exactly four of those openings with the
//! complete `BookBindingKey` identity and two ordinary expedition `UnitKey`s.
//! Its canonical asset tag has no relic branch.  Cross-round, cross-batch,
//! cross-opening-session and duplicate-transcript substitutions refuse before
//! an opaque verified result is created.
//!
//! No Bazaar transition or V1 clearing relation is reimplemented in Rust.  A
//! successful result is suitable only as native input to Lean's dependent
//! opening portals; Lean must still check the exact book root, derived order
//! nullifiers, crossing output, custody head and one-shot settlement.  The
//! verifier that issues this evidence sees each plaintext order and encryption
//! opening.  This is the `openingAwareJudge` tier, not house-blind or
//! zero-knowledge ingress.  The certificate wire itself repeats side, quantity
//! and limit, so it is a private verifier-to-local-Lean transport: it must not
//! be published, logged, or placed in the public EventBatch.

use std::fmt;

use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use fhegg_fhe::{Side as FheggSide, order_ingress::OrderSourceCertificate};

const STATEMENT_MAGIC: &[u8; 8] = b"POAENV01";
const CERTIFICATE_MAGIC: &[u8; 8] = b"POAOPN01";
const EXCHANGE_CERTIFICATE_MAGIC: &[u8; 8] = b"POAXCH01";
const WIRE_VERSION: u16 = 1;
const CERTIFICATE_DOMAIN: &str = "dregg.poa-bazaar.opening-aware-certificate.v1";
const EXCHANGE_CERTIFICATE_DOMAIN: &str =
    "dregg.poa-bazaar.ordinary-exchange-opening-certificate.v1";
const BOOK_BINDING_DOMAIN: &str = "dregg.poa-bazaar.opening-aware-book-binding.v1";
const SOURCE_CERTIFICATE_LEN: usize = 291;
const STATEMENT_WIRE_LEN: usize = 8 + 2 + 32 + 8 + 32 + 32 + 8 + 8 + 32 + 32 + 32 + 32;
const OPENING_CERTIFICATE_WIRE_LEN: usize =
    8 + 2 + 2 + STATEMENT_WIRE_LEN + 4 + 2 + SOURCE_CERTIFICATE_LEN + 64;
const BATCH_KEY_WIRE_LEN: usize = 32 + 32 + 8 + 8 + 32;
const ORDINARY_UNIT_KEY_WIRE_LEN: usize = 1 + 32 + 32 + 8 + 8;
const BOOK_BINDING_WIRE_LEN: usize = 8 + BATCH_KEY_WIRE_LEN * 2 + 32;
const OPENING_COUNT: usize = 4;
const OPERATOR_VISIBLE_PRIVACY_TAG: u8 = 0;
const ORDINARY_PART_TAG: u8 = 0;
const BABYBEAR_MODULUS: u32 = 2_013_265_921;

/// Fixed wire image of `BazaarGame.EnvelopeStatement` for V1.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactEnvelopeStatementV1 {
    actor: [u8; 32],
    round: u64,
    federation_id: [u8; 32],
    content_session: [u8; 32],
    content_epoch: u64,
    batch_id: u64,
    source_root: [u8; 32],
    nullifier: [u8; 32],
    ciphertext_commitment: [u8; 32],
    signature_commitment: [u8; 32],
}

impl ExactEnvelopeStatementV1 {
    #[allow(clippy::too_many_arguments)]
    pub const fn new(
        actor: [u8; 32],
        round: u64,
        federation_id: [u8; 32],
        content_session: [u8; 32],
        content_epoch: u64,
        batch_id: u64,
        source_root: [u8; 32],
        nullifier: [u8; 32],
        ciphertext_commitment: [u8; 32],
        signature_commitment: [u8; 32],
    ) -> Self {
        Self {
            actor,
            round,
            federation_id,
            content_session,
            content_epoch,
            batch_id,
            source_root,
            nullifier,
            ciphertext_commitment,
            signature_commitment,
        }
    }

    pub const fn actor(&self) -> [u8; 32] {
        self.actor
    }

    pub const fn round(&self) -> u64 {
        self.round
    }

    pub const fn federation_id(&self) -> [u8; 32] {
        self.federation_id
    }

    pub const fn content_session(&self) -> [u8; 32] {
        self.content_session
    }

    pub const fn content_epoch(&self) -> u64 {
        self.content_epoch
    }

    pub const fn batch_id(&self) -> u64 {
        self.batch_id
    }

    pub const fn source_root(&self) -> [u8; 32] {
        self.source_root
    }

    pub const fn nullifier(&self) -> [u8; 32] {
        self.nullifier
    }

    pub const fn ciphertext_commitment(&self) -> [u8; 32] {
        self.ciphertext_commitment
    }

    pub const fn signature_commitment(&self) -> [u8; 32] {
        self.signature_commitment
    }

    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(STATEMENT_WIRE_LEN);
        out.extend_from_slice(STATEMENT_MAGIC);
        out.extend_from_slice(&WIRE_VERSION.to_be_bytes());
        out.extend_from_slice(&self.actor);
        out.extend_from_slice(&self.round.to_be_bytes());
        out.extend_from_slice(&self.federation_id);
        out.extend_from_slice(&self.content_session);
        out.extend_from_slice(&self.content_epoch.to_be_bytes());
        out.extend_from_slice(&self.batch_id.to_be_bytes());
        out.extend_from_slice(&self.source_root);
        out.extend_from_slice(&self.nullifier);
        out.extend_from_slice(&self.ciphertext_commitment);
        out.extend_from_slice(&self.signature_commitment);
        out
    }

    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self, BazaarOpeningError> {
        if bytes.len() != STATEMENT_WIRE_LEN {
            return Err(BazaarOpeningError::MalformedWire("statement length"));
        }
        let mut cursor = 0usize;
        if take::<8>(bytes, &mut cursor)? != *STATEMENT_MAGIC {
            return Err(BazaarOpeningError::MalformedWire("statement magic"));
        }
        if u16::from_be_bytes(take::<2>(bytes, &mut cursor)?) != WIRE_VERSION {
            return Err(BazaarOpeningError::UnsupportedVersion);
        }
        let statement = Self {
            actor: take::<32>(bytes, &mut cursor)?,
            round: u64::from_be_bytes(take::<8>(bytes, &mut cursor)?),
            federation_id: take::<32>(bytes, &mut cursor)?,
            content_session: take::<32>(bytes, &mut cursor)?,
            content_epoch: u64::from_be_bytes(take::<8>(bytes, &mut cursor)?),
            batch_id: u64::from_be_bytes(take::<8>(bytes, &mut cursor)?),
            source_root: take::<32>(bytes, &mut cursor)?,
            nullifier: take::<32>(bytes, &mut cursor)?,
            ciphertext_commitment: take::<32>(bytes, &mut cursor)?,
            signature_commitment: take::<32>(bytes, &mut cursor)?,
        };
        debug_assert_eq!(cursor, bytes.len());
        Ok(statement)
    }
}

/// Fixed wire image of `DarkBazaar.BatchKey`.
///
/// `BookBindingKey` carries both the intake batch and the V1 claim batch.  The
/// current Lean game accepts a book only when those keys are equal; retaining
/// both on the wire makes a cross-claim substitution visible rather than
/// normalizing it away.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExactBatchKeyV1 {
    federation_id: [u8; 32],
    content_session: [u8; 32],
    content_epoch: u64,
    batch_id: u64,
    source_root: [u8; 32],
}

impl ExactBatchKeyV1 {
    pub const fn new(
        federation_id: [u8; 32],
        content_session: [u8; 32],
        content_epoch: u64,
        batch_id: u64,
        source_root: [u8; 32],
    ) -> Self {
        Self {
            federation_id,
            content_session,
            content_epoch,
            batch_id,
            source_root,
        }
    }

    pub const fn federation_id(&self) -> [u8; 32] {
        self.federation_id
    }

    pub const fn content_session(&self) -> [u8; 32] {
        self.content_session
    }

    pub const fn content_epoch(&self) -> u64 {
        self.content_epoch
    }

    pub const fn batch_id(&self) -> u64 {
        self.batch_id
    }

    pub const fn source_root(&self) -> [u8; 32] {
        self.source_root
    }

    fn matches_statement(&self, statement: &ExactEnvelopeStatementV1) -> bool {
        self.federation_id == statement.federation_id
            && self.content_session == statement.content_session
            && self.content_epoch == statement.content_epoch
            && self.batch_id == statement.batch_id
            && self.source_root == statement.source_root
    }

    fn to_bytes(self) -> [u8; BATCH_KEY_WIRE_LEN] {
        let mut out = [0u8; BATCH_KEY_WIRE_LEN];
        let mut cursor = 0usize;
        put(&mut out, &mut cursor, &self.federation_id);
        put(&mut out, &mut cursor, &self.content_session);
        put(&mut out, &mut cursor, &self.content_epoch.to_be_bytes());
        put(&mut out, &mut cursor, &self.batch_id.to_be_bytes());
        put(&mut out, &mut cursor, &self.source_root);
        debug_assert_eq!(cursor, out.len());
        out
    }

    fn from_bytes(bytes: [u8; BATCH_KEY_WIRE_LEN]) -> Result<Self, BazaarOpeningError> {
        let mut cursor = 0usize;
        let value = Self {
            federation_id: take::<32>(&bytes, &mut cursor)?,
            content_session: take::<32>(&bytes, &mut cursor)?,
            content_epoch: u64::from_be_bytes(take::<8>(&bytes, &mut cursor)?),
            batch_id: u64::from_be_bytes(take::<8>(&bytes, &mut cursor)?),
            source_root: take::<32>(&bytes, &mut cursor)?,
        };
        debug_assert_eq!(cursor, bytes.len());
        Ok(value)
    }
}

/// Exact ordinary expedition-part identity.  The leading wire tag is fixed to
/// ordinary salvage.  A story-relic tag has no decoder branch and therefore
/// cannot be smuggled into this custody path even when its numeric id matches a
/// part id.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExactOrdinaryUnitKeyV1 {
    runtime_receipt: [u8; 32],
    source_batch: [u8; 32],
    part: u64,
    serial: u64,
}

impl ExactOrdinaryUnitKeyV1 {
    pub const fn new(
        runtime_receipt: [u8; 32],
        source_batch: [u8; 32],
        part: u64,
        serial: u64,
    ) -> Self {
        Self {
            runtime_receipt,
            source_batch,
            part,
            serial,
        }
    }

    pub const fn runtime_receipt(&self) -> [u8; 32] {
        self.runtime_receipt
    }

    pub const fn source_batch(&self) -> [u8; 32] {
        self.source_batch
    }

    pub const fn part(&self) -> u64 {
        self.part
    }

    pub const fn serial(&self) -> u64 {
        self.serial
    }

    fn to_bytes(self) -> [u8; ORDINARY_UNIT_KEY_WIRE_LEN] {
        let mut out = [0u8; ORDINARY_UNIT_KEY_WIRE_LEN];
        let mut cursor = 0usize;
        put(&mut out, &mut cursor, &[ORDINARY_PART_TAG]);
        put(&mut out, &mut cursor, &self.runtime_receipt);
        put(&mut out, &mut cursor, &self.source_batch);
        put(&mut out, &mut cursor, &self.part.to_be_bytes());
        put(&mut out, &mut cursor, &self.serial.to_be_bytes());
        debug_assert_eq!(cursor, out.len());
        out
    }

    fn from_bytes(bytes: [u8; ORDINARY_UNIT_KEY_WIRE_LEN]) -> Result<Self, BazaarOpeningError> {
        let mut cursor = 0usize;
        if take::<1>(&bytes, &mut cursor)?[0] != ORDINARY_PART_TAG {
            return Err(BazaarOpeningError::RelicIngressUnsupported);
        }
        let value = Self {
            runtime_receipt: take::<32>(&bytes, &mut cursor)?,
            source_batch: take::<32>(&bytes, &mut cursor)?,
            part: u64::from_be_bytes(take::<8>(&bytes, &mut cursor)?),
            serial: u64::from_be_bytes(take::<8>(&bytes, &mut cursor)?),
        };
        debug_assert_eq!(cursor, bytes.len());
        Ok(value)
    }
}

/// Exact non-transcript portion of `BazaarGame.BookBindingKey`.
///
/// The four transcript statements are carried by the enclosing exchange
/// certificate and are exposed by the verified result.  The constructor checks
/// the current game's `claimKey = batchKey` requirement and the faithful eight
/// little-endian BabyBear lanes of the private-book commitment.  It does not
/// run the V1 clearing relation; Lean must still authorize that exact root and
/// four-order witness.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExactBookBindingV1 {
    round: u64,
    batch_key: ExactBatchKeyV1,
    claim_key: ExactBatchKeyV1,
    private_book_commitment: [u8; 32],
}

impl ExactBookBindingV1 {
    pub fn new(
        round: u64,
        batch_key: ExactBatchKeyV1,
        claim_key: ExactBatchKeyV1,
        private_book_commitment: [u8; 32],
    ) -> Result<Self, BazaarOpeningError> {
        if batch_key != claim_key {
            return Err(BazaarOpeningError::BookClaimMismatch);
        }
        validate_private_root(&private_book_commitment)?;
        Ok(Self {
            round,
            batch_key,
            claim_key,
            private_book_commitment,
        })
    }

    pub const fn round(&self) -> u64 {
        self.round
    }

    pub const fn batch_key(&self) -> ExactBatchKeyV1 {
        self.batch_key
    }

    pub const fn claim_key(&self) -> ExactBatchKeyV1 {
        self.claim_key
    }

    pub const fn private_book_commitment(&self) -> [u8; 32] {
        self.private_book_commitment
    }

    fn to_bytes(self) -> [u8; BOOK_BINDING_WIRE_LEN] {
        let mut out = [0u8; BOOK_BINDING_WIRE_LEN];
        let mut cursor = 0usize;
        put(&mut out, &mut cursor, &self.round.to_be_bytes());
        put(&mut out, &mut cursor, &self.batch_key.to_bytes());
        put(&mut out, &mut cursor, &self.claim_key.to_bytes());
        put(&mut out, &mut cursor, &self.private_book_commitment);
        debug_assert_eq!(cursor, out.len());
        out
    }

    fn from_bytes(bytes: [u8; BOOK_BINDING_WIRE_LEN]) -> Result<Self, BazaarOpeningError> {
        let mut cursor = 0usize;
        let round = u64::from_be_bytes(take::<8>(&bytes, &mut cursor)?);
        let batch_key =
            ExactBatchKeyV1::from_bytes(take::<BATCH_KEY_WIRE_LEN>(&bytes, &mut cursor)?)?;
        let claim_key =
            ExactBatchKeyV1::from_bytes(take::<BATCH_KEY_WIRE_LEN>(&bytes, &mut cursor)?)?;
        let private_book_commitment = take::<32>(&bytes, &mut cursor)?;
        debug_assert_eq!(cursor, bytes.len());
        Self::new(round, batch_key, claim_key, private_book_commitment)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OpeningSideV1 {
    Bid,
    Ask,
}

impl OpeningSideV1 {
    const fn tag(self) -> u8 {
        match self {
            Self::Bid => 0,
            Self::Ask => 1,
        }
    }

    fn from_tag(tag: u8) -> Result<Self, BazaarOpeningError> {
        match tag {
            0 => Ok(Self::Bid),
            1 => Ok(Self::Ask),
            _ => Err(BazaarOpeningError::MalformedWire("order side")),
        }
    }
}

/// Exact fixed-shape private order carried into Lean's V1 authorization.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OpeningOrderV1 {
    slot: u8,
    side: OpeningSideV1,
    quantity: u8,
    limit: u8,
}

impl OpeningOrderV1 {
    pub fn new(
        slot: u8,
        side: OpeningSideV1,
        quantity: u8,
        limit: u8,
    ) -> Result<Self, BazaarOpeningError> {
        if slot >= 4 {
            return Err(BazaarOpeningError::UnsupportedOrder("slot"));
        }
        if quantity == 0 || quantity > 15 {
            return Err(BazaarOpeningError::UnsupportedOrder("quantity"));
        }
        if limit >= 4 {
            return Err(BazaarOpeningError::UnsupportedOrder("limit"));
        }
        Ok(Self {
            slot,
            side,
            quantity,
            limit,
        })
    }

    pub const fn slot(&self) -> u8 {
        self.slot
    }

    pub const fn side(&self) -> OpeningSideV1 {
        self.side
    }

    pub const fn quantity(&self) -> u8 {
        self.quantity
    }

    pub const fn limit(&self) -> u8 {
        self.limit
    }

    fn to_bytes(self) -> [u8; 4] {
        [self.slot, self.side.tag(), self.quantity, self.limit]
    }

    fn from_bytes(bytes: [u8; 4]) -> Result<Self, BazaarOpeningError> {
        Self::new(
            bytes[0],
            OpeningSideV1::from_tag(bytes[1])?,
            bytes[2],
            bytes[3],
        )
    }
}

/// Private host-local evidence for both current opening-aware Lean portals.
/// Its wire contains the operator-visible order tuple and is not a public
/// receipt.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BazaarOpeningCertificateV1 {
    statement: ExactEnvelopeStatementV1,
    order: OpeningOrderV1,
    source: OrderSourceCertificate,
    signature: [u8; 64],
}

impl BazaarOpeningCertificateV1 {
    /// Issue only after fhEgg's exact-opening certificate verifies and matches
    /// every game-facing field that it can independently constrain.
    pub fn issue(
        statement: ExactEnvelopeStatementV1,
        order: OpeningOrderV1,
        source: OrderSourceCertificate,
        source_verifier: &SigningKey,
    ) -> Result<Self, BazaarOpeningError> {
        validate_source(&statement, order, &source, &source_verifier.verifying_key())?;
        let mut certificate = Self {
            statement,
            order,
            source,
            signature: [0; 64],
        };
        certificate.signature = source_verifier
            .sign(&certificate.signing_message())
            .to_bytes();
        Ok(certificate)
    }

    pub fn statement(&self) -> &ExactEnvelopeStatementV1 {
        &self.statement
    }

    pub const fn order(&self) -> OpeningOrderV1 {
        self.order
    }

    pub fn source(&self) -> &OrderSourceCertificate {
        &self.source
    }

    /// Verify the configured source key, exact BFV-opening certificate, full
    /// PoA binding signature and all redundant equality checks.
    pub fn verify(
        &self,
        source_verifier: &VerifyingKey,
    ) -> Result<VerifiedBazaarOpeningV1, BazaarOpeningError> {
        validate_source(&self.statement, self.order, &self.source, source_verifier)?;
        source_verifier
            .verify_strict(
                &self.signing_message(),
                &Signature::from_bytes(&self.signature),
            )
            .map_err(|_| BazaarOpeningError::InvalidPortalSignature)?;
        Ok(VerifiedBazaarOpeningV1 {
            statement: self.statement.clone(),
            order: self.order,
            source_binding_digest: self.source.binding_digest(),
        })
    }

    fn unsigned_wire_bytes(&self) -> Vec<u8> {
        let statement = self.statement.to_wire_bytes();
        let source = self.source.to_wire_bytes();
        debug_assert_eq!(statement.len(), STATEMENT_WIRE_LEN);
        debug_assert_eq!(source.len(), SOURCE_CERTIFICATE_LEN);
        let mut out = Vec::with_capacity(8 + 2 + 2 + statement.len() + 4 + 2 + source.len());
        out.extend_from_slice(CERTIFICATE_MAGIC);
        out.extend_from_slice(&WIRE_VERSION.to_be_bytes());
        out.extend_from_slice(&(statement.len() as u16).to_be_bytes());
        out.extend_from_slice(&statement);
        out.extend_from_slice(&self.order.to_bytes());
        out.extend_from_slice(&(source.len() as u16).to_be_bytes());
        out.extend_from_slice(&source);
        out
    }

    fn signing_message(&self) -> [u8; 32] {
        blake3::derive_key(CERTIFICATE_DOMAIN, &self.unsigned_wire_bytes())
    }

    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = self.unsigned_wire_bytes();
        out.extend_from_slice(&self.signature);
        out
    }

    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self, BazaarOpeningError> {
        let mut cursor = 0usize;
        if take::<8>(bytes, &mut cursor)? != *CERTIFICATE_MAGIC {
            return Err(BazaarOpeningError::MalformedWire("certificate magic"));
        }
        if u16::from_be_bytes(take::<2>(bytes, &mut cursor)?) != WIRE_VERSION {
            return Err(BazaarOpeningError::UnsupportedVersion);
        }
        let statement_len = u16::from_be_bytes(take::<2>(bytes, &mut cursor)?) as usize;
        if statement_len != STATEMENT_WIRE_LEN {
            return Err(BazaarOpeningError::MalformedWire("statement length"));
        }
        let statement_end = cursor
            .checked_add(statement_len)
            .filter(|end| *end <= bytes.len())
            .ok_or(BazaarOpeningError::MalformedWire("truncated statement"))?;
        let statement = ExactEnvelopeStatementV1::from_wire_bytes(&bytes[cursor..statement_end])?;
        cursor = statement_end;
        let order = OpeningOrderV1::from_bytes(take::<4>(bytes, &mut cursor)?)?;
        let source_len = u16::from_be_bytes(take::<2>(bytes, &mut cursor)?) as usize;
        if source_len != SOURCE_CERTIFICATE_LEN {
            return Err(BazaarOpeningError::MalformedWire(
                "source certificate length",
            ));
        }
        let source_end = cursor
            .checked_add(source_len)
            .filter(|end| *end <= bytes.len())
            .ok_or(BazaarOpeningError::MalformedWire(
                "truncated source certificate",
            ))?;
        let source = OrderSourceCertificate::from_wire_bytes(&bytes[cursor..source_end])
            .map_err(|_| BazaarOpeningError::InvalidSourceCertificate)?;
        cursor = source_end;
        let signature = take::<64>(bytes, &mut cursor)?;
        if cursor != bytes.len() {
            return Err(BazaarOpeningError::MalformedWire("trailing bytes"));
        }
        Ok(Self {
            statement,
            order,
            source,
            signature,
        })
    }
}

/// Opaque successful result.  Its constructor is private and there is no
/// deserializer; callers obtain it only by verifying the complete certificate.
#[derive(Clone, Debug)]
pub struct VerifiedBazaarOpeningV1 {
    statement: ExactEnvelopeStatementV1,
    order: OpeningOrderV1,
    source_binding_digest: [u8; 32],
}

impl VerifiedBazaarOpeningV1 {
    pub fn statement(&self) -> &ExactEnvelopeStatementV1 {
        &self.statement
    }

    pub const fn order(&self) -> OpeningOrderV1 {
        self.order
    }

    pub const fn source_binding_digest(&self) -> [u8; 32] {
        self.source_binding_digest
    }
}

/// Private operator-visible binding for one ordinary-part exchange and
/// the exact four source openings which form its `BookBindingKey` transcript.
///
/// This certificate is deliberately not named a settlement authorization.  It
/// does not replace Lean's `V1.Authorization`: after this verifier returns its
/// opaque result, Lean must still check the exact private root, nullifier image,
/// crossing output and custody transition.  What this value closes is the
/// native join that Lean cannot observe by itself: the two serialized ordinary
/// `UnitKey`s and exchange parties are signed together with one exact four-slot
/// opening-aware book.  The certificate does not authenticate mint provenance
/// or current custody; the finalized ordinary-salvage transaction must consume
/// its independent canonical-load and finalized-carrier capabilities.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BazaarExchangeOpeningCertificateV1 {
    exchange_id: [u8; 32],
    seller: [u8; 32],
    buyer: [u8; 32],
    offered: ExactOrdinaryUnitKeyV1,
    requested: ExactOrdinaryUnitKeyV1,
    book: ExactBookBindingV1,
    openings: [BazaarOpeningCertificateV1; OPENING_COUNT],
    signature: [u8; 64],
}

impl BazaarExchangeOpeningCertificateV1 {
    #[allow(clippy::too_many_arguments)]
    pub fn issue(
        exchange_id: [u8; 32],
        seller: [u8; 32],
        buyer: [u8; 32],
        offered: ExactOrdinaryUnitKeyV1,
        requested: ExactOrdinaryUnitKeyV1,
        book: ExactBookBindingV1,
        mut openings: [BazaarOpeningCertificateV1; OPENING_COUNT],
        source_verifier: &SigningKey,
    ) -> Result<Self, BazaarOpeningError> {
        openings.sort_by_key(|opening| opening.order.slot);
        validate_exchange(
            seller,
            buyer,
            offered,
            requested,
            &book,
            &openings,
            &source_verifier.verifying_key(),
        )?;
        let mut certificate = Self {
            exchange_id,
            seller,
            buyer,
            offered,
            requested,
            book,
            openings,
            signature: [0; 64],
        };
        certificate.signature = source_verifier
            .sign(&certificate.signing_message())
            .to_bytes();
        Ok(certificate)
    }

    pub const fn exchange_id(&self) -> [u8; 32] {
        self.exchange_id
    }

    pub const fn seller(&self) -> [u8; 32] {
        self.seller
    }

    pub const fn buyer(&self) -> [u8; 32] {
        self.buyer
    }

    pub const fn offered(&self) -> ExactOrdinaryUnitKeyV1 {
        self.offered
    }

    pub const fn requested(&self) -> ExactOrdinaryUnitKeyV1 {
        self.requested
    }

    pub const fn book(&self) -> ExactBookBindingV1 {
        self.book
    }

    pub fn openings(&self) -> &[BazaarOpeningCertificateV1; OPENING_COUNT] {
        &self.openings
    }

    pub fn verify(
        &self,
        source_verifier: &VerifyingKey,
    ) -> Result<VerifiedBazaarExchangeOpeningV1, BazaarOpeningError> {
        let openings = validate_exchange(
            self.seller,
            self.buyer,
            self.offered,
            self.requested,
            &self.book,
            &self.openings,
            source_verifier,
        )?;
        source_verifier
            .verify_strict(
                &self.signing_message(),
                &Signature::from_bytes(&self.signature),
            )
            .map_err(|_| BazaarOpeningError::InvalidExchangeSignature)?;
        let book_binding_digest = book_binding_digest(&self.book, &self.openings);
        Ok(VerifiedBazaarExchangeOpeningV1 {
            exchange_id: self.exchange_id,
            seller: self.seller,
            buyer: self.buyer,
            offered: self.offered,
            requested: self.requested,
            book: self.book,
            openings,
            book_binding_digest,
        })
    }

    fn unsigned_wire_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(
            8 + 2
                + 1
                + 32 * 3
                + ORDINARY_UNIT_KEY_WIRE_LEN * 2
                + BOOK_BINDING_WIRE_LEN
                + OPENING_COUNT * (2 + OPENING_CERTIFICATE_WIRE_LEN),
        );
        out.extend_from_slice(EXCHANGE_CERTIFICATE_MAGIC);
        out.extend_from_slice(&WIRE_VERSION.to_be_bytes());
        out.push(OPERATOR_VISIBLE_PRIVACY_TAG);
        out.extend_from_slice(&self.exchange_id);
        out.extend_from_slice(&self.seller);
        out.extend_from_slice(&self.buyer);
        out.extend_from_slice(&self.offered.to_bytes());
        out.extend_from_slice(&self.requested.to_bytes());
        out.extend_from_slice(&self.book.to_bytes());
        for opening in &self.openings {
            let wire = opening.to_wire_bytes();
            debug_assert_eq!(wire.len(), OPENING_CERTIFICATE_WIRE_LEN);
            out.extend_from_slice(&(wire.len() as u16).to_be_bytes());
            out.extend_from_slice(&wire);
        }
        out
    }

    fn signing_message(&self) -> [u8; 32] {
        blake3::derive_key(EXCHANGE_CERTIFICATE_DOMAIN, &self.unsigned_wire_bytes())
    }

    pub fn to_wire_bytes(&self) -> Vec<u8> {
        let mut out = self.unsigned_wire_bytes();
        out.extend_from_slice(&self.signature);
        out
    }

    pub fn from_wire_bytes(bytes: &[u8]) -> Result<Self, BazaarOpeningError> {
        let mut cursor = 0usize;
        if take::<8>(bytes, &mut cursor)? != *EXCHANGE_CERTIFICATE_MAGIC {
            return Err(BazaarOpeningError::MalformedWire(
                "exchange certificate magic",
            ));
        }
        if u16::from_be_bytes(take::<2>(bytes, &mut cursor)?) != WIRE_VERSION {
            return Err(BazaarOpeningError::UnsupportedVersion);
        }
        if take::<1>(bytes, &mut cursor)?[0] != OPERATOR_VISIBLE_PRIVACY_TAG {
            return Err(BazaarOpeningError::HouseBlindUnsupported);
        }
        let exchange_id = take::<32>(bytes, &mut cursor)?;
        let seller = take::<32>(bytes, &mut cursor)?;
        let buyer = take::<32>(bytes, &mut cursor)?;
        let offered = ExactOrdinaryUnitKeyV1::from_bytes(take::<ORDINARY_UNIT_KEY_WIRE_LEN>(
            bytes,
            &mut cursor,
        )?)?;
        let requested = ExactOrdinaryUnitKeyV1::from_bytes(take::<ORDINARY_UNIT_KEY_WIRE_LEN>(
            bytes,
            &mut cursor,
        )?)?;
        let book =
            ExactBookBindingV1::from_bytes(take::<BOOK_BINDING_WIRE_LEN>(bytes, &mut cursor)?)?;
        let mut openings = Vec::with_capacity(OPENING_COUNT);
        for _ in 0..OPENING_COUNT {
            let len = u16::from_be_bytes(take::<2>(bytes, &mut cursor)?) as usize;
            if len != OPENING_CERTIFICATE_WIRE_LEN {
                return Err(BazaarOpeningError::MalformedWire(
                    "nested opening certificate length",
                ));
            }
            let end = cursor
                .checked_add(len)
                .filter(|end| *end <= bytes.len())
                .ok_or(BazaarOpeningError::MalformedWire(
                    "truncated nested opening certificate",
                ))?;
            openings.push(BazaarOpeningCertificateV1::from_wire_bytes(
                &bytes[cursor..end],
            )?);
            cursor = end;
        }
        let signature = take::<64>(bytes, &mut cursor)?;
        if cursor != bytes.len() {
            return Err(BazaarOpeningError::MalformedWire(
                "exchange certificate trailing bytes",
            ));
        }
        let openings: [BazaarOpeningCertificateV1; OPENING_COUNT] = openings
            .try_into()
            .map_err(|_| BazaarOpeningError::MalformedWire("opening count"))?;
        if openings
            .iter()
            .enumerate()
            .any(|(slot, opening)| usize::from(opening.order.slot) != slot)
        {
            return Err(BazaarOpeningError::NonCanonicalOpeningOrder);
        }
        Ok(Self {
            exchange_id,
            seller,
            buyer,
            offered,
            requested,
            book,
            openings,
            signature,
        })
    }
}

/// Opaque result of verifying both signature layers and every equality needed
/// to join an ordinary exchange to one four-opening book.  There is no public
/// constructor or wire decoder for this authority-bearing type.
#[derive(Clone, Debug)]
pub struct VerifiedBazaarExchangeOpeningV1 {
    exchange_id: [u8; 32],
    seller: [u8; 32],
    buyer: [u8; 32],
    offered: ExactOrdinaryUnitKeyV1,
    requested: ExactOrdinaryUnitKeyV1,
    book: ExactBookBindingV1,
    openings: [VerifiedBazaarOpeningV1; OPENING_COUNT],
    book_binding_digest: [u8; 32],
}

impl VerifiedBazaarExchangeOpeningV1 {
    pub const fn exchange_id(&self) -> [u8; 32] {
        self.exchange_id
    }

    pub const fn seller(&self) -> [u8; 32] {
        self.seller
    }

    pub const fn buyer(&self) -> [u8; 32] {
        self.buyer
    }

    pub const fn offered(&self) -> ExactOrdinaryUnitKeyV1 {
        self.offered
    }

    pub const fn requested(&self) -> ExactOrdinaryUnitKeyV1 {
        self.requested
    }

    pub const fn book(&self) -> ExactBookBindingV1 {
        self.book
    }

    pub fn openings(&self) -> &[VerifiedBazaarOpeningV1; OPENING_COUNT] {
        &self.openings
    }

    pub const fn book_binding_digest(&self) -> [u8; 32] {
        self.book_binding_digest
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BazaarOpeningError {
    MalformedWire(&'static str),
    UnsupportedVersion,
    UnsupportedOrder(&'static str),
    HouseBlindUnsupported,
    RelicIngressUnsupported,
    NonCanonicalPrivateRoot,
    InvalidSourceCertificate,
    ActorMismatch,
    SlotMismatch,
    OrderMismatch,
    CiphertextCommitmentMismatch,
    SignatureCommitmentMismatch,
    InvalidPortalSignature,
    InvalidExchangeSignature,
    SameParty,
    SameUnit,
    BookClaimMismatch,
    BookRoundMismatch,
    BookBatchMismatch,
    NonCanonicalOpeningOrder,
    DuplicateOpeningNullifier,
    DuplicateOpeningStatement,
    OpeningSessionMismatch,
}

impl fmt::Display for BazaarOpeningError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MalformedWire(reason) => write!(f, "malformed PoA Bazaar opening wire: {reason}"),
            Self::UnsupportedVersion => write!(f, "unsupported PoA Bazaar opening version"),
            Self::UnsupportedOrder(reason) => write!(f, "unsupported V1 order: {reason}"),
            Self::HouseBlindUnsupported => write!(
                f,
                "house-blind privacy is not implemented by the opening-aware portal"
            ),
            Self::RelicIngressUnsupported => {
                write!(f, "story relics have no ordinary-salvage exchange ingress")
            }
            Self::NonCanonicalPrivateRoot => {
                write!(f, "private-book root has a non-canonical BabyBear lane")
            }
            Self::InvalidSourceCertificate => write!(f, "invalid fhEgg source certificate"),
            Self::ActorMismatch => write!(f, "source certificate actor mismatch"),
            Self::SlotMismatch => write!(f, "source certificate slot mismatch"),
            Self::OrderMismatch => write!(f, "source certificate order mismatch"),
            Self::CiphertextCommitmentMismatch => {
                write!(f, "source certificate ciphertext commitment mismatch")
            }
            Self::SignatureCommitmentMismatch => {
                write!(f, "source certificate signature commitment mismatch")
            }
            Self::InvalidPortalSignature => write!(f, "invalid PoA Bazaar portal signature"),
            Self::InvalidExchangeSignature => {
                write!(f, "invalid PoA Bazaar exchange-opening signature")
            }
            Self::SameParty => write!(f, "ordinary exchange parties must be distinct"),
            Self::SameUnit => write!(f, "ordinary exchange units must be distinct"),
            Self::BookClaimMismatch => {
                write!(
                    f,
                    "opening-aware claim key does not equal its intake batch key"
                )
            }
            Self::BookRoundMismatch => write!(f, "opening belongs to another Bazaar round"),
            Self::BookBatchMismatch => write!(f, "opening belongs to another Bazaar batch"),
            Self::NonCanonicalOpeningOrder => {
                write!(
                    f,
                    "four opening certificates are not in canonical slot order"
                )
            }
            Self::DuplicateOpeningNullifier => {
                write!(f, "opening-aware book repeats an order nullifier")
            }
            Self::DuplicateOpeningStatement => {
                write!(f, "opening-aware book repeats an envelope statement")
            }
            Self::OpeningSessionMismatch => {
                write!(f, "opening certificates come from different fhEgg sessions")
            }
        }
    }
}

impl std::error::Error for BazaarOpeningError {}

fn validate_source(
    statement: &ExactEnvelopeStatementV1,
    order: OpeningOrderV1,
    source: &OrderSourceCertificate,
    source_verifier: &VerifyingKey,
) -> Result<(), BazaarOpeningError> {
    source
        .verify(source_verifier)
        .map_err(|_| BazaarOpeningError::InvalidSourceCertificate)?;
    if !source.actor_matches(&statement.actor) {
        return Err(BazaarOpeningError::ActorMismatch);
    }
    if source.trader() != usize::from(order.slot) {
        return Err(BazaarOpeningError::SlotMismatch);
    }
    let source_side = match source.side() {
        FheggSide::Bid => OpeningSideV1::Bid,
        FheggSide::Ask => OpeningSideV1::Ask,
    };
    if source_side != order.side
        || source.limit() != usize::from(order.limit)
        || source.qty() != u16::from(order.quantity)
    {
        return Err(BazaarOpeningError::OrderMismatch);
    }
    if source.ciphertext_digest() != statement.ciphertext_commitment {
        return Err(BazaarOpeningError::CiphertextCommitmentMismatch);
    }
    if source.message_digest() != statement.signature_commitment {
        return Err(BazaarOpeningError::SignatureCommitmentMismatch);
    }
    Ok(())
}

fn validate_private_root(root: &[u8; 32]) -> Result<(), BazaarOpeningError> {
    if root.chunks_exact(4).any(|lane| {
        u32::from_le_bytes(lane.try_into().expect("four-byte lane")) >= BABYBEAR_MODULUS
    }) {
        Err(BazaarOpeningError::NonCanonicalPrivateRoot)
    } else {
        Ok(())
    }
}

fn validate_exchange(
    seller: [u8; 32],
    buyer: [u8; 32],
    offered: ExactOrdinaryUnitKeyV1,
    requested: ExactOrdinaryUnitKeyV1,
    book: &ExactBookBindingV1,
    openings: &[BazaarOpeningCertificateV1; OPENING_COUNT],
    source_verifier: &VerifyingKey,
) -> Result<[VerifiedBazaarOpeningV1; OPENING_COUNT], BazaarOpeningError> {
    if seller == buyer {
        return Err(BazaarOpeningError::SameParty);
    }
    if offered == requested {
        return Err(BazaarOpeningError::SameUnit);
    }
    if book.batch_key != book.claim_key {
        return Err(BazaarOpeningError::BookClaimMismatch);
    }
    validate_private_root(&book.private_book_commitment)?;

    let first_session_nonce = openings[0].source.session_nonce();
    let first_session_digest = openings[0].source.session_digest();
    let mut verified = Vec::with_capacity(OPENING_COUNT);
    for (slot, opening) in openings.iter().enumerate() {
        if usize::from(opening.order.slot) != slot {
            return Err(BazaarOpeningError::NonCanonicalOpeningOrder);
        }
        if opening.statement.round != book.round {
            return Err(BazaarOpeningError::BookRoundMismatch);
        }
        if !book.batch_key.matches_statement(&opening.statement) {
            return Err(BazaarOpeningError::BookBatchMismatch);
        }
        if opening.source.session_nonce() != first_session_nonce
            || opening.source.session_digest() != first_session_digest
        {
            return Err(BazaarOpeningError::OpeningSessionMismatch);
        }
        if openings[..slot]
            .iter()
            .any(|prior| prior.statement == opening.statement)
        {
            return Err(BazaarOpeningError::DuplicateOpeningStatement);
        }
        if openings[..slot]
            .iter()
            .any(|prior| prior.statement.nullifier == opening.statement.nullifier)
        {
            return Err(BazaarOpeningError::DuplicateOpeningNullifier);
        }
        verified.push(opening.verify(source_verifier)?);
    }
    verified
        .try_into()
        .map_err(|_| BazaarOpeningError::MalformedWire("opening count"))
}

fn book_binding_digest(
    book: &ExactBookBindingV1,
    openings: &[BazaarOpeningCertificateV1; OPENING_COUNT],
) -> [u8; 32] {
    let mut bytes = Vec::with_capacity(BOOK_BINDING_WIRE_LEN + OPENING_COUNT * STATEMENT_WIRE_LEN);
    bytes.extend_from_slice(&book.to_bytes());
    for opening in openings {
        bytes.extend_from_slice(&opening.statement.to_wire_bytes());
    }
    blake3::derive_key(BOOK_BINDING_DOMAIN, &bytes)
}

fn put<const N: usize>(out: &mut [u8], cursor: &mut usize, value: &[u8; N]) {
    let end = *cursor + N;
    out[*cursor..end].copy_from_slice(value);
    *cursor = end;
}

fn take<const N: usize>(bytes: &[u8], cursor: &mut usize) -> Result<[u8; N], BazaarOpeningError> {
    let end = cursor
        .checked_add(N)
        .filter(|end| *end <= bytes.len())
        .ok_or(BazaarOpeningError::MalformedWire("truncated field"))?;
    let value = bytes[*cursor..end]
        .try_into()
        .map_err(|_| BazaarOpeningError::MalformedWire("field width"))?;
    *cursor = end;
    Ok(value)
}
