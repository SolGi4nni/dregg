//! Hiding-proof authorization for the real Dark Bazaar settlement.
//!
//! This module joins the Lean-emitted fixed `N=4,K=4` private-order relation in
//! `dregg-circuit-prove` to the existing [`crate::DarkBazaarSession`]. It does
//! not create a second ledger or a toy settlement: after verification, the
//! normal executor-backed `SETTLE` path closes/reveals the sealed-auction board,
//! folds the conserved award ring, and records its real resolve turn. Existing
//! [`crate::DarkBazaarSession::settle_winning_asset`] then crosses a Descent (or
//! other provenance-carrying) asset through `TradeWorld` to that same winner.
//!
//! The fixed relation is an exact encoding of this crate's one-unit first-price
//! auction for up to three bids: every bid is `(Bid, qty=1, limit=value)` and a
//! synthetic ask is `(Ask, qty=1, limit=highest_bid)`. Therefore its lowest
//! maximum-volume clearing is exactly `(p*, V*) = (highest_bid, 1)`. Values must
//! fit the current four-price family (`0..4`); wider books fail closed.
//!
//! # Honest privacy and source boundary
//!
//! [`DarkBazaarSession::prepare_private_clearing_zk`] builds the witness in this
//! process. `HidingFriPcs` hides it from proof consumers, while this trace-building
//! process still sees every bid: this is Tier-1/operator-visible, not Tier-0
//! no-single-viewer clearing. The public eight-felt root is binding to the proved
//! private book, but the current descriptor does not prove that this Poseidon root
//! opens the auction cell's independent BLAKE3 seals. Production callers must pin
//! [`PrivateClearingExpectation::order_root`] through their authenticated source
//! registry/FHE-MPC transcript. That cross-commitment relation remains explicit,
//! rather than being implied by this API.

#[path = "private_batch_optimizer.rs"]
pub mod batch_optimizer;

use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};

use dregg_circuit_prove::dark_bazaar_private::{
    self, DarkBazaarPrivateZkProof, PrivateBookWitness, PrivateOrder, PublicStatement, Side,
};
use dreggnet_offerings::{DreggIdentity, Outcome};
use starbridge_sealed_auction::Phase;

use crate::{DarkBazaarOffering, DarkBazaarSession};

/// BabyBear's canonical modulus. Kept local so the market need not depend on
/// `dregg-circuit` merely to derive its stable public session tag.
const BABYBEAR_P: u64 = 2_013_265_921;

/// Domain for deriving a fixed-family public session felt from the offering's
/// replay-stable `SessionConfig::seed`.
const SESSION_DOMAIN: &str = "dreggnet-market/dark-bazaar-private/session/v1";
const PRIVATE_INPUT_DOMAIN: &str = "dregg.private-bazaar-private-input.v1";
const BLIND_FINGERPRINT_DOMAIN: &str = "dregg.private-bazaar-commitment-blind.v1";
const BINDING_CHECKSUM_DOMAIN: &str = "dregg.private-bazaar-commitment-binding.v1";
const BINDING_MAGIC: &[u8; 8] = b"DBCB0001";
const BINDING_RECORD_LEN: usize = 8 + 32 + 4 + 4 + 32 + (8 * 4) + 32;

/// The exact private-book family the Lean-emitted descriptor proves.
///
/// `metatheory/Market/DarkBazaarPrivateDescriptor.lean` fixes `ORDER_COUNT = 4`,
/// `PRICE_COUNT = 4` and `QTY_BITS = 4`, and emits
/// `circuit/descriptors/by-name/dark-bazaar-private-n4k4.json`. One of the four
/// committed order slots is always this crate's synthetic top-price ask, so at
/// most three real sealed bids fit inside the proved family. A larger book is
/// simply not covered by that descriptor: production ingress refuses it rather
/// than clearing it unproved.
pub const PROVEN_MAX_SEALED_BIDS: usize = dark_bazaar_private::ORDER_COUNT - 1;

/// Bid limits must be members of the proved four-bucket price family `0..=3`.
pub const PROVEN_PRICE_BUCKETS: usize = dark_bazaar_private::PRICE_COUNT;

/// Public values pinned independently of the proof being verified.
///
/// In a product deployment `order_root` comes from an authenticated source
/// registry (or a jointly endorsed FHE/MPC transcript), while price and volume
/// come from the settlement policy. Passing a root copied from an untrusted
/// proof provides proof validity but no external source provenance.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrivateClearingExpectation {
    /// Faithful eight-felt Poseidon commitment to the private fixed book.
    pub order_root: [u32; dark_bazaar_private::DIGEST_WIDTH],
    /// Expected first-price clear, in the current price family `0..4`.
    pub price: u32,
    /// Expected one-unit cleared volume. The live auction settles one asset.
    pub volume: u32,
}

impl PrivateClearingExpectation {
    /// Capture an expectation from a statement at the point where a trusted
    /// source registry accepts it. Do not use this as authentication by itself.
    pub const fn from_statement(statement: PublicStatement) -> Self {
        Self {
            order_root: statement.order_root,
            price: statement.p_star,
            volume: statement.v_star,
        }
    }
}

/// A hiding proof paired with the exact caller-supplied public statement it is
/// intended to authorize. Fields are private so verification cannot accidentally
/// mix the proof with a statement without going through the named constructor.
pub struct PrivateClearingAuthorization {
    proof: DarkBazaarPrivateZkProof,
    statement: PublicStatement,
}

impl PrivateClearingAuthorization {
    /// Pair an externally produced hiding proof with its claimed public values.
    /// No validation happens until [`DarkBazaarOffering::verify_private_clearing`].
    pub const fn new(proof: DarkBazaarPrivateZkProof, statement: PublicStatement) -> Self {
        Self { proof, statement }
    }

    /// The only values revealed by the fixed relation.
    pub const fn statement(&self) -> PublicStatement {
        self.statement
    }

    /// Consume this authorization and replace only its public statement. This is
    /// deliberately useful to exercise fail-closed verifier teeth without any
    /// ability to alter the opaque proof.
    pub fn with_statement(self, statement: PublicStatement) -> Self {
        Self {
            proof: self.proof,
            statement,
        }
    }
}

/// Evidence that the hiding relation authorized the real executor settlement.
#[derive(Clone, Debug)]
pub struct PrivateClearingReceipt {
    /// The exact verified public statement.
    pub statement: PublicStatement,
    /// The existing sealed-auction actor selected by the real tie policy.
    pub winner: DreggIdentity,
    /// The existing executor's resolve turn, not a synthetic receipt.
    pub settlement_turn: dregg_app_framework::TurnReceipt,
}

/// A worker-private sealed ingress book already gated to the proven family.
///
/// The scale gate lives at CONSTRUCTION, deliberately: a book outside the proved
/// `N=4,K=4` shape must be refused while the executor board is still untouched,
/// not after three BID turns have already landed on it. There is no constructor
/// that admits an out-of-family book, so no production caller can run the
/// Lean-descriptor relation on input the descriptor does not cover.
///
/// Bid limits are worker-private. `Debug` prints only the arity.
#[derive(Clone, PartialEq, Eq)]
pub struct PrivateSealedIngressBook {
    bids: Vec<(DreggIdentity, i64)>,
}

impl std::fmt::Debug for PrivateSealedIngressBook {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PrivateSealedIngressBook")
            .field("bids", &self.bids.len())
            .field("limits", &"<worker-private>")
            .finish()
    }
}

impl PrivateSealedIngressBook {
    /// Accept exactly the books the emitted `N=4,K=4` descriptor proves, and
    /// refuse every other book by name. A caller holding this value knows its
    /// contents are inside the proved family; a caller that could not build one
    /// has no other route onto the private clearing path.
    pub fn new(bids: Vec<(DreggIdentity, i64)>) -> Result<Self, PrivateClearingError> {
        if bids.is_empty() {
            return Err(PrivateClearingError::NoBids);
        }
        if bids.len() > PROVEN_MAX_SEALED_BIDS {
            return Err(PrivateClearingError::TooManyBids(bids.len()));
        }
        for (actor, limit) in &bids {
            if actor.0.is_empty() {
                return Err(PrivateClearingError::EmptyIngressBidder);
            }
            if *limit < 0 || *limit >= PROVEN_PRICE_BUCKETS as i64 {
                return Err(PrivateClearingError::PriceOutsideFixedFamily(i128::from(
                    *limit,
                )));
            }
        }
        Ok(Self { bids })
    }

    /// How many sealed bids this ingress book carries. Never zero.
    pub fn len(&self) -> usize {
        self.bids.len()
    }

    /// Always false: an empty book is refused at construction.
    pub const fn is_empty(&self) -> bool {
        false
    }

    /// Worker-only: the sealed bids in exact ingress order. The private clearing
    /// worker places these as real executor BID turns; nothing on a frontend
    /// action path holds this value.
    #[doc(hidden)]
    pub fn sealed_bids(&self) -> &[(DreggIdentity, i64)] {
        &self.bids
    }

    /// The exact canonical fixed-family order records this book will commit:
    /// one qty-1 bid per sealed bid in ingress order, then the deterministic
    /// synthetic ask at the top bid. This mirrors `private_orders` over the
    /// live market, but is derivable BEFORE any BID turn lands, which is what
    /// lets a contradicting durable binding be refused on an untouched board.
    ///
    /// The two derivations are pinned to each other on every production settle
    /// by [`PrivateClearingCommitmentBinding::matches_ingress_book`], so a drift
    /// between them fails closed instead of going unnoticed.
    #[doc(hidden)]
    pub fn canonical_orders(&self) -> Vec<PrivateOrder> {
        let top = self
            .bids
            .iter()
            .map(|(_, limit)| *limit)
            .max()
            .expect("a sealed ingress book is nonempty by construction");
        let mut orders = Vec::with_capacity(self.bids.len() + 1);
        for (_, limit) in &self.bids {
            orders.push(PrivateOrder::bid(1, *limit as u8));
        }
        orders.push(PrivateOrder::ask(1, top as u8));
        orders
    }
}

/// Worker-private durable binding between one commitment blind and one exact
/// canonical private book. Fields have no public accessors: frontends never
/// receive the blind or private-input digest.
#[derive(Clone, PartialEq, Eq)]
pub struct PrivateClearingCommitmentBinding {
    market_instance_id: [u8; 32],
    proof_session: u32,
    rule: u32,
    private_input_digest: [u8; 32],
    blinding: [u32; dark_bazaar_private::DIGEST_WIDTH],
}

impl std::fmt::Debug for PrivateClearingCommitmentBinding {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PrivateClearingCommitmentBinding")
            .field("market_instance_id", &self.market_instance_id)
            .field("proof_session", &self.proof_session)
            .field("rule", &self.rule)
            .field("private_input_digest", &"<worker-private>")
            .field("blinding", &"<worker-private>")
            .finish()
    }
}

impl PrivateClearingCommitmentBinding {
    fn new(
        session: &DarkBazaarSession,
        market_instance_id: [u8; 32],
        blinding: [u32; dark_bazaar_private::DIGEST_WIDTH],
    ) -> Result<Self, PrivateClearingError> {
        if market_instance_id == [0; 32] {
            return Err(PrivateClearingError::InvalidMarketInstance);
        }
        // The witness constructor is the canonical field-range check for all
        // blind lanes. Building it also checks the current fixed book shape.
        let orders = private_orders(session)?;
        PrivateBookWitness::try_from_orders_with_blinding(&orders, blinding)
            .map_err(PrivateClearingError::InvalidProof)?;
        Ok(Self {
            market_instance_id,
            proof_session: session.private_proof_session(),
            rule: dark_bazaar_private::RULE_ID,
            private_input_digest: private_input_digest(&orders),
            blinding,
        })
    }

    fn validate(
        &self,
        session: &DarkBazaarSession,
        market_instance_id: [u8; 32],
    ) -> Result<Vec<PrivateOrder>, PrivateClearingError> {
        let orders = private_orders(session)?;
        if self.market_instance_id != market_instance_id
            || self.proof_session != session.private_proof_session()
            || self.rule != dark_bazaar_private::RULE_ID
            || self.private_input_digest != private_input_digest(&orders)
        {
            return Err(PrivateClearingError::CommitmentBindingMismatch);
        }
        Ok(orders)
    }

    fn blind_fingerprint(&self) -> [u8; 32] {
        blind_fingerprint(self.blinding)
    }

    /// This durable binding names exactly the canonical record the given ingress
    /// book derives. Checked on every production settle so the pre-mutation
    /// ingress derivation and the live-market derivation cannot silently
    /// diverge: a drift becomes a refusal, not a wrong commitment.
    #[doc(hidden)]
    pub fn matches_ingress_book(&self, book: &PrivateSealedIngressBook) -> bool {
        self.private_input_digest == private_input_digest(&book.canonical_orders())
    }

    fn encode(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(BINDING_RECORD_LEN);
        out.extend_from_slice(BINDING_MAGIC);
        out.extend_from_slice(&self.market_instance_id);
        out.extend_from_slice(&self.proof_session.to_be_bytes());
        out.extend_from_slice(&self.rule.to_be_bytes());
        out.extend_from_slice(&self.private_input_digest);
        for lane in self.blinding {
            out.extend_from_slice(&lane.to_be_bytes());
        }
        let checksum = binding_checksum(&out);
        out.extend_from_slice(&checksum);
        out
    }

    fn decode(bytes: &[u8]) -> Result<Self, PrivateClearingError> {
        if bytes.len() != BINDING_RECORD_LEN || &bytes[..8] != BINDING_MAGIC {
            return Err(PrivateClearingError::CorruptCommitmentBinding);
        }
        if binding_checksum(&bytes[..BINDING_RECORD_LEN - 32]) != bytes[BINDING_RECORD_LEN - 32..] {
            return Err(PrivateClearingError::CorruptCommitmentBinding);
        }
        let mut blinding = [0u32; dark_bazaar_private::DIGEST_WIDTH];
        for (index, lane) in blinding.iter_mut().enumerate() {
            let offset = 80 + index * 4;
            *lane = u32::from_be_bytes(
                bytes[offset..offset + 4]
                    .try_into()
                    .expect("fixed commitment-binding length checked"),
            );
        }
        let binding = Self {
            market_instance_id: bytes[8..40]
                .try_into()
                .expect("fixed commitment-binding length checked"),
            proof_session: u32::from_be_bytes(
                bytes[40..44]
                    .try_into()
                    .expect("fixed commitment-binding length checked"),
            ),
            rule: u32::from_be_bytes(
                bytes[44..48]
                    .try_into()
                    .expect("fixed commitment-binding length checked"),
            ),
            private_input_digest: bytes[48..80]
                .try_into()
                .expect("fixed commitment-binding length checked"),
            blinding,
        };
        if binding.market_instance_id == [0; 32]
            || binding.private_input_digest == [0; 32]
            || binding.rule != dark_bazaar_private::RULE_ID
            || binding
                .blinding
                .iter()
                .any(|lane| u64::from(*lane) >= BABYBEAR_P)
        {
            return Err(PrivateClearingError::CorruptCommitmentBinding);
        }
        Ok(binding)
    }
}

/// Durable worker-only registry enforcing one blind per exact private input
/// claim and one bound commitment per market instance.
#[derive(Clone, Debug)]
pub struct PrivateClearingCommitmentStore {
    root: PathBuf,
}

impl PrivateClearingCommitmentStore {
    pub fn open(root: impl AsRef<Path>) -> Result<Self, PrivateClearingError> {
        let root = root.as_ref().to_path_buf();
        fs::create_dir_all(root.join("by-market"))
            .map_err(|error| PrivateClearingError::commitment_io("create market index", error))?;
        fs::create_dir_all(root.join("by-blind"))
            .map_err(|error| PrivateClearingError::commitment_io("create blind index", error))?;
        Ok(Self { root })
    }

    /// Load the existing binding for `market_instance_id`, or atomically bind a
    /// new caller-supplied blind. Existing bindings need no blind supplied after
    /// restart. A blind already reserved for different market/session/rule/order
    /// bytes is refused globally.
    fn market_path(&self, market_instance_id: [u8; 32]) -> PathBuf {
        self.root
            .join("by-market")
            .join(format!("{}.binding", hex32(market_instance_id)))
    }

    /// Refuse an ingress book that this market's durable binding already
    /// contradicts, while the executor board is still untouched.
    ///
    /// This is the restart/substitution tooth: after a crash the worker replays
    /// its private inputs into a freshly listed market, and a substituted book
    /// must be refused before a single BID turn commits, not after. `Ok(())`
    /// with no stored binding means this is a first claim, and the binding is
    /// created from the live market later in the same settle.
    #[doc(hidden)]
    pub fn precheck_untouched_ingress(
        &self,
        market_instance_id: [u8; 32],
        book: &PrivateSealedIngressBook,
    ) -> Result<(), PrivateClearingError> {
        if market_instance_id == [0; 32] {
            return Err(PrivateClearingError::InvalidMarketInstance);
        }
        let market_path = self.market_path(market_instance_id);
        if !market_path.exists() {
            return Ok(());
        }
        let binding = read_binding(&market_path)?;
        if binding.market_instance_id != market_instance_id
            || binding.rule != dark_bazaar_private::RULE_ID
            || !binding.matches_ingress_book(book)
        {
            return Err(PrivateClearingError::CommitmentBindingMismatch);
        }
        Ok(())
    }

    pub fn bind_or_load(
        &self,
        session: &DarkBazaarSession,
        market_instance_id: [u8; 32],
        new_blinding: Option<[u32; dark_bazaar_private::DIGEST_WIDTH]>,
    ) -> Result<PrivateClearingCommitmentBinding, PrivateClearingError> {
        let market_path = self.market_path(market_instance_id);
        if market_path.exists() {
            let binding = read_binding(&market_path)?;
            binding.validate(session, market_instance_id)?;
            if new_blinding.is_some_and(|candidate| candidate != binding.blinding) {
                return Err(PrivateClearingError::CommitmentAlreadyBound);
            }
            verify_blind_reservation(&self.root, &binding)?;
            return Ok(binding);
        }

        let blinding = new_blinding.ok_or(PrivateClearingError::CommitmentBindingNotFound)?;
        let binding = PrivateClearingCommitmentBinding::new(session, market_instance_id, blinding)?;
        write_new_or_verify_binding(
            &blind_path(&self.root, binding.blind_fingerprint()),
            &binding.encode(),
            PrivateClearingError::CommitmentBlindAlreadyUsed,
        )?;
        write_new_or_verify_binding(
            &market_path,
            &binding.encode(),
            PrivateClearingError::CommitmentAlreadyBound,
        )?;
        Ok(binding)
    }
}

impl PrivateClearingReceipt {
    /// Reconstruct the narrow canonical receipt shape carried by the private
    /// Bazaar worker spool.  The spool owns the byte schema; this constructor
    /// exists here because [`PublicStatement`] deliberately belongs to the
    /// proving crate and is not re-exported as an ambient wire type.
    ///
    /// This is not a verifier or a public ingestion surface.  It performs the
    /// statement/finality shape checks that can be made without the live market;
    /// the worker still rejoins the result to the exact hosted market receipt
    /// before it can mint any consequence authority.
    #[doc(hidden)]
    pub fn from_worker_spool_v1_parts(
        session: u32,
        rule: u32,
        order_root: [u32; dark_bazaar_private::DIGEST_WIDTH],
        price: u32,
        volume: u32,
        winner: DreggIdentity,
        settlement_turn: dregg_app_framework::TurnReceipt,
    ) -> Result<Self, PrivateClearingError> {
        let statement = PublicStatement {
            session,
            rule,
            order_root,
            p_star: price,
            v_star: volume,
        };
        if u64::from(statement.session) >= BABYBEAR_P
            || statement.rule != dark_bazaar_private::RULE_ID
            || statement.p_star as usize >= dark_bazaar_private::PRICE_COUNT
            || statement.v_star != 1
            || statement
                .order_root
                .iter()
                .any(|lane| u64::from(*lane) >= BABYBEAR_P)
        {
            return Err(PrivateClearingError::InvalidWorkerSpoolReceipt(
                "public statement is outside the fixed Dark Bazaar field/rule/shape".to_owned(),
            ));
        }
        if winner.0.is_empty() {
            return Err(PrivateClearingError::InvalidWorkerSpoolReceipt(
                "winner is empty".to_owned(),
            ));
        }
        if settlement_turn.finality != dregg_turn::Finality::Final
            || settlement_turn.turn_hash == [0; 32]
            || settlement_turn.receipt_hash() == [0; 32]
        {
            return Err(PrivateClearingError::InvalidWorkerSpoolReceipt(
                "settlement turn is not final canonical evidence".to_owned(),
            ));
        }
        Ok(Self {
            statement,
            winner,
            settlement_turn,
        })
    }

    /// Rejoin a decoded worker-spool envelope to the exact proof-verified
    /// semantic claim and terminal receipt currently held by the live market.
    /// Timestamp, signature, and receipt-chain bytes are issuance evidence, not
    /// semantic identity, but must still match the current live issuance.
    #[doc(hidden)]
    pub fn validate_worker_spool_live_settlement(
        &self,
        session: &DarkBazaarSession,
    ) -> Result<(), PrivateClearingError> {
        let semantic = session
            .verified_private_clearing_receipt
            .as_ref()
            .ok_or_else(|| {
                PrivateClearingError::InvalidWorkerSpoolReceipt(
                    "live market has no proof-verified private settlement".to_owned(),
                )
            })?;
        let clearing = session.clearing().ok_or_else(|| {
            PrivateClearingError::InvalidWorkerSpoolReceipt("live market is not settled".to_owned())
        })?;
        let live_turn = session.market.receipts.last().ok_or_else(|| {
            PrivateClearingError::InvalidWorkerSpoolReceipt(
                "live market has no terminal settlement receipt".to_owned(),
            )
        })?;
        if semantic.statement != self.statement
            || semantic.winner != self.winner
            || self.statement.session != session.private_proof_session()
            || self.statement.v_star != 1
            || session.winning_actor() != Some(&self.winner)
            || u32::try_from(clearing.price()).ok() != Some(self.statement.p_star)
            || !clearing.conserved()
            || live_turn.turn_hash != self.settlement_turn.turn_hash
            || live_turn.receipt_hash() != self.settlement_turn.receipt_hash()
            || self.settlement_turn.turn_hash == [0; 32]
        {
            return Err(PrivateClearingError::InvalidWorkerSpoolReceipt(
                "receipt does not match the current live proof-verified settlement".to_owned(),
            ));
        }
        Ok(())
    }

    /// The verified first-price clearing value.
    pub const fn price(&self) -> u32 {
        self.statement.p_star
    }

    /// The verified fixed-book cleared volume.
    pub const fn volume(&self) -> u32 {
        self.statement.v_star
    }
}

/// Named fail-closed reasons for private settlement authorization.
#[derive(Debug)]
pub enum PrivateClearingError {
    /// LIST has not created the executor-backed auction cell.
    NotListed,
    /// A previous clear is terminal.
    AlreadySettled,
    /// Private settlement starts only from the untouched commit phase.
    PhaseNotCommit(Option<Phase>),
    /// There is no demand to clear.
    NoBids,
    /// The fixed `N=4` book reserves one slot for the synthetic ask.
    TooManyBids(usize),
    /// The top bid cannot be represented by the current four-price family.
    PriceOutsideFixedFamily(i128),
    /// A sealed ingress bid named no bidder.
    EmptyIngressBidder,
    /// The reserve tooth would refuse this auction after reveal.
    BelowReserve { high: i128, reserve: i128 },
    /// The proof names a different replay-stable market session.
    SessionMismatch { expected: u32, claimed: u32 },
    /// The proof is not for the installed Dark Bazaar clearing rule.
    RuleMismatch { expected: u32, claimed: u32 },
    /// The proof's faithful root is not the independently pinned source root.
    RootMismatch,
    /// The proof's public clearing price differs from policy/live auction state.
    PriceMismatch { expected: u32, claimed: u32 },
    /// The proof's public volume differs from the one-unit live settlement.
    VolumeMismatch { expected: u32, claimed: u32 },
    /// The opaque HidingFriPcs proof did not verify against the supplied statement.
    InvalidProof(String),
    /// The already-authorized real executor path nevertheless refused.
    SettlementRefused(String),
    /// The executor landed but its recorded winner/price diverged from preflight.
    PostSettlementMismatch(&'static str),
    /// A zero market identity cannot name a durable private claim.
    InvalidMarketInstance,
    /// The stored blind is bound to different market/session/rule/order bytes.
    CommitmentBindingMismatch,
    /// A persisted commitment binding is malformed or has failed its checksum.
    CorruptCommitmentBinding,
    /// This market already has a different worker-private commitment binding.
    CommitmentAlreadyBound,
    /// This blind has already been reserved for a different private claim.
    CommitmentBlindAlreadyUsed,
    /// No durable binding exists and the caller did not supply a new blind.
    CommitmentBindingNotFound,
    /// The deployment-owned fixed worker-spool codec supplied a noncanonical
    /// public statement or non-final settlement envelope.
    InvalidWorkerSpoolReceipt(String),
    /// Durable worker-private commitment storage failed.
    CommitmentIo {
        operation: &'static str,
        detail: String,
    },
}

impl PrivateClearingError {
    fn commitment_io(operation: &'static str, error: io::Error) -> Self {
        Self::CommitmentIo {
            operation,
            detail: error.to_string(),
        }
    }
}

impl std::fmt::Display for PrivateClearingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotListed => write!(f, "nothing is listed yet"),
            Self::AlreadySettled => write!(f, "the Dark Bazaar session is already settled"),
            Self::PhaseNotCommit(phase) => write!(
                f,
                "private settlement requires an untouched COMMIT phase, found {phase:?}"
            ),
            Self::NoBids => write!(f, "no sealed bids were placed"),
            Self::TooManyBids(found) => write!(
                f,
                "{found} bids plus the award ask exceed fixed N={} capacity",
                dark_bazaar_private::ORDER_COUNT
            ),
            Self::PriceOutsideFixedFamily(price) => write!(
                f,
                "top bid {price} is outside fixed K={} price family",
                dark_bazaar_private::PRICE_COUNT
            ),
            Self::EmptyIngressBidder => {
                write!(f, "a sealed ingress bid named no bidder")
            }
            Self::BelowReserve { high, reserve } => write!(
                f,
                "top bid {high} is below reserve {reserve}; no sale may settle"
            ),
            Self::SessionMismatch { expected, claimed } => write!(
                f,
                "private proof session mismatch: expected {expected}, claimed {claimed}"
            ),
            Self::RuleMismatch { expected, claimed } => write!(
                f,
                "private proof rule mismatch: expected {expected}, claimed {claimed}"
            ),
            Self::RootMismatch => write!(
                f,
                "private proof order root differs from the pinned source root"
            ),
            Self::PriceMismatch { expected, claimed } => write!(
                f,
                "private proof price mismatch: expected {expected}, claimed {claimed}"
            ),
            Self::VolumeMismatch { expected, claimed } => write!(
                f,
                "private proof volume mismatch: expected {expected}, claimed {claimed}"
            ),
            Self::InvalidProof(why) => write!(f, "private clearing proof refused: {why}"),
            Self::SettlementRefused(why) => {
                write!(f, "authorized executor settlement refused: {why}")
            }
            Self::PostSettlementMismatch(why) => {
                write!(f, "authorized settlement diverged after landing: {why}")
            }
            Self::InvalidMarketInstance => {
                write!(f, "private commitment requires a nonzero market identity")
            }
            Self::CommitmentBindingMismatch => write!(
                f,
                "private commitment binding does not match this market/session/rule/order book"
            ),
            Self::CorruptCommitmentBinding => {
                write!(f, "private commitment binding record is corrupt")
            }
            Self::CommitmentAlreadyBound => {
                write!(
                    f,
                    "market already has a different private commitment binding"
                )
            }
            Self::CommitmentBlindAlreadyUsed => write!(
                f,
                "private commitment blind is already bound to a different claim"
            ),
            Self::CommitmentBindingNotFound => write!(
                f,
                "private commitment binding does not exist and no new blind was supplied"
            ),
            Self::InvalidWorkerSpoolReceipt(why) => {
                write!(f, "private worker spool receipt refused: {why}")
            }
            Self::CommitmentIo { operation, detail } => {
                write!(
                    f,
                    "private commitment storage failed to {operation}: {detail}"
                )
            }
        }
    }
}

impl std::error::Error for PrivateClearingError {}

/// The real auction result known before mutation: highest bid with the exact
/// seal-ordered tie policy used by `Auction::winner` after reveals.
struct LiveClear {
    price: u32,
    winner: DreggIdentity,
}

impl DarkBazaarSession {
    /// Stable canonical BabyBear session id used by the fixed private relation.
    /// It re-derives from the same seed as the market session and is independent
    /// of process-local randomness.
    pub fn private_proof_session(&self) -> u32 {
        let mut hasher = blake3::Hasher::new_derive_key(SESSION_DOMAIN);
        hasher.update(&self.market.seed.to_le_bytes());
        let digest = hasher.finalize();
        let mut low = [0u8; 8];
        low.copy_from_slice(&digest.as_bytes()[..8]);
        (u64::from_le_bytes(low) % BABYBEAR_P) as u32
    }

    /// Produce the hiding proof for the exact private bids currently held by
    /// this Tier-1 session. The witness contains one qty-1 bid per sealed-auction
    /// bid and the deterministic top-price ask that makes the relation exactly
    /// encode this crate's first-price award.
    ///
    /// The returned root still needs independent authenticated pinning before a
    /// remote verifier should treat it as source provenance.
    pub fn prepare_private_clearing_zk(
        &self,
    ) -> Result<PrivateClearingAuthorization, PrivateClearingError> {
        let orders = private_orders(self)?;
        let (proof, statement) =
            dark_bazaar_private::prove_orders_zk(self.private_proof_session(), &orders)
                .map_err(PrivateClearingError::InvalidProof)?;
        Ok(PrivateClearingAuthorization::new(proof, statement))
    }

    /// Re-prove the exact private book under its worker-owned durable binding.
    ///
    /// A durable private worker uses this when reconstructing an already
    /// accepted semantic claim after restart: it persists the eight private
    /// blind limbs beside its private inputs, then creates a fresh hiding proof
    /// and executor receipt for the same `(session, order_root, p*, V*)`.
    /// The opaque binding is revalidated against the market identity and exact
    /// current book before its blind can be used. Callers cannot pass an
    /// unbound raw blind through this API.
    pub fn prepare_private_clearing_zk_with_binding(
        &self,
        market_instance_id: [u8; 32],
        binding: &PrivateClearingCommitmentBinding,
    ) -> Result<PrivateClearingAuthorization, PrivateClearingError> {
        let orders = binding.validate(self, market_instance_id)?;
        let witness = PrivateBookWitness::try_from_orders_with_blinding(&orders, binding.blinding)
            .map_err(PrivateClearingError::InvalidProof)?;
        let (proof, statement) =
            dark_bazaar_private::prove_zk(self.private_proof_session(), &witness)
                .map_err(PrivateClearingError::InvalidProof)?;
        Ok(PrivateClearingAuthorization::new(proof, statement))
    }

    /// Derive the public values a production worker should pin, WITHOUT proving
    /// and without reading any proof.
    ///
    /// The eight-felt root is committed here from the worker's own private book
    /// and its own durable blind; the price comes from the live sealed auction's
    /// exact tie policy; the volume is the one-unit settlement policy. This is
    /// the difference between authenticating a source and copying a number out
    /// of the artifact under test: [`PrivateClearingExpectation::from_statement`]
    /// gives proof validity only, while this expectation is independent evidence
    /// that the verified proof is about *this* market's book.
    pub fn private_clearing_expectation_with_binding(
        &self,
        market_instance_id: [u8; 32],
        binding: &PrivateClearingCommitmentBinding,
    ) -> Result<PrivateClearingExpectation, PrivateClearingError> {
        let orders = binding.validate(self, market_instance_id)?;
        let witness = PrivateBookWitness::try_from_orders_with_blinding(&orders, binding.blinding)
            .map_err(PrivateClearingError::InvalidProof)?;
        let committed = dark_bazaar_private::statement(self.private_proof_session(), &witness)
            .map_err(PrivateClearingError::InvalidProof)?;
        let live = live_clear(self)?;
        if committed.p_star != live.price {
            return Err(PrivateClearingError::PriceMismatch {
                expected: live.price,
                claimed: committed.p_star,
            });
        }
        if committed.v_star != 1 {
            return Err(PrivateClearingError::VolumeMismatch {
                expected: 1,
                claimed: committed.v_star,
            });
        }
        Ok(PrivateClearingExpectation {
            order_root: committed.order_root,
            price: live.price,
            volume: 1,
        })
    }
}

fn private_orders(session: &DarkBazaarSession) -> Result<Vec<PrivateOrder>, PrivateClearingError> {
    let live = live_clear(session)?;
    let mut orders = Vec::with_capacity(session.market.bids.len() + 1);
    for placed in &session.market.bids {
        orders.push(PrivateOrder::bid(1, placed.bid.value as u8));
    }
    orders.push(PrivateOrder::ask(1, live.price as u8));
    Ok(orders)
}

/// Hash the exact fixed-width canonical order record consumed by the relation.
/// Canonical zero-quantity padding is included, so alternative variable-length
/// encodings cannot alias the worker's persisted claim.
fn private_input_digest(orders: &[PrivateOrder]) -> [u8; 32] {
    let witness = PrivateBookWitness::try_from_orders_with_blinding(orders, [0; 8])
        .expect("private orders are validated before commitment binding");
    let mut hasher = blake3::Hasher::new_derive_key(PRIVATE_INPUT_DOMAIN);
    hasher.update(&(dark_bazaar_private::ORDER_COUNT as u64).to_be_bytes());
    for order in witness.orders {
        hasher.update(&[match order.side {
            Side::Bid => 0,
            Side::Ask => 1,
        }]);
        hasher.update(&[order.qty, order.limit]);
    }
    *hasher.finalize().as_bytes()
}

fn blind_fingerprint(blinding: [u32; dark_bazaar_private::DIGEST_WIDTH]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key(BLIND_FINGERPRINT_DOMAIN);
    for lane in blinding {
        hasher.update(&lane.to_be_bytes());
    }
    *hasher.finalize().as_bytes()
}

fn binding_checksum(bytes: &[u8]) -> [u8; 32] {
    *blake3::Hasher::new_derive_key(BINDING_CHECKSUM_DOMAIN)
        .update(bytes)
        .finalize()
        .as_bytes()
}

fn blind_path(root: &Path, fingerprint: [u8; 32]) -> PathBuf {
    root.join("by-blind")
        .join(format!("{}.binding", hex32(fingerprint)))
}

fn verify_blind_reservation(
    root: &Path,
    binding: &PrivateClearingCommitmentBinding,
) -> Result<(), PrivateClearingError> {
    let reserved = read_binding(&blind_path(root, binding.blind_fingerprint()))?;
    if &reserved == binding {
        Ok(())
    } else {
        Err(PrivateClearingError::CommitmentBlindAlreadyUsed)
    }
}

fn write_new_or_verify_binding(
    path: &Path,
    expected: &[u8],
    collision: PrivateClearingError,
) -> Result<(), PrivateClearingError> {
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    match options.open(path) {
        Ok(mut file) => {
            file.write_all(expected)
                .map_err(|error| PrivateClearingError::commitment_io("write binding", error))?;
            file.sync_all()
                .map_err(|error| PrivateClearingError::commitment_io("sync binding", error))?;
            sync_binding_parent(path)
        }
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
            let mut found = Vec::new();
            File::open(path)
                .and_then(|mut file| file.read_to_end(&mut found))
                .map_err(|error| {
                    PrivateClearingError::commitment_io("read existing binding", error)
                })?;
            if found == expected {
                Ok(())
            } else {
                Err(collision)
            }
        }
        Err(error) => Err(PrivateClearingError::commitment_io("create binding", error)),
    }
}

fn read_binding(path: &Path) -> Result<PrivateClearingCommitmentBinding, PrivateClearingError> {
    let bytes = fs::read(path)
        .map_err(|error| PrivateClearingError::commitment_io("read binding", error))?;
    PrivateClearingCommitmentBinding::decode(&bytes)
}

fn sync_binding_parent(path: &Path) -> Result<(), PrivateClearingError> {
    let parent = path
        .parent()
        .ok_or(PrivateClearingError::CorruptCommitmentBinding)?;
    File::open(parent)
        .and_then(|directory| directory.sync_all())
        .map_err(|error| PrivateClearingError::commitment_io("sync binding directory", error))
}

fn hex32(bytes: [u8; 32]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(64);
    for byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}

impl DarkBazaarOffering {
    /// Verify a private clearing authorization and every public join without
    /// submitting a turn or otherwise mutating the market session.
    pub fn verify_private_clearing(
        &self,
        session: &DarkBazaarSession,
        authorization: &PrivateClearingAuthorization,
        expected: PrivateClearingExpectation,
    ) -> Result<(), PrivateClearingError> {
        let live = live_clear(session)?;
        let statement = authorization.statement;
        let expected_session = session.private_proof_session();

        if statement.session != expected_session {
            return Err(PrivateClearingError::SessionMismatch {
                expected: expected_session,
                claimed: statement.session,
            });
        }
        if statement.rule != dark_bazaar_private::RULE_ID {
            return Err(PrivateClearingError::RuleMismatch {
                expected: dark_bazaar_private::RULE_ID,
                claimed: statement.rule,
            });
        }
        if statement.order_root != expected.order_root {
            return Err(PrivateClearingError::RootMismatch);
        }
        if statement.p_star != expected.price {
            return Err(PrivateClearingError::PriceMismatch {
                expected: expected.price,
                claimed: statement.p_star,
            });
        }
        if statement.v_star != expected.volume {
            return Err(PrivateClearingError::VolumeMismatch {
                expected: expected.volume,
                claimed: statement.v_star,
            });
        }
        if statement.p_star != live.price {
            return Err(PrivateClearingError::PriceMismatch {
                expected: live.price,
                claimed: statement.p_star,
            });
        }
        if statement.v_star != 1 {
            return Err(PrivateClearingError::VolumeMismatch {
                expected: 1,
                claimed: statement.v_star,
            });
        }

        dark_bazaar_private::verify_zk(&authorization.proof, statement)
            .map_err(PrivateClearingError::InvalidProof)
    }

    /// Verify the hiding proof and all public joins, then drive the existing
    /// executor-backed `SETTLE` action. Verification and preflight finish before
    /// the first close/reveal/resolve mutation is submitted.
    pub fn settle_private_verified(
        &self,
        session: &mut DarkBazaarSession,
        authorization: PrivateClearingAuthorization,
        expected: PrivateClearingExpectation,
    ) -> Result<PrivateClearingReceipt, PrivateClearingError> {
        self.verify_private_clearing(session, &authorization, expected)?;
        let preflight = live_clear(session)?;

        let settlement_turn = match self.market.do_settle(&mut session.market) {
            Outcome::Landed {
                receipt,
                ended: true,
            } => receipt,
            Outcome::Landed { ended: false, .. } => {
                return Err(PrivateClearingError::PostSettlementMismatch(
                    "SETTLE landed without ending the auction",
                ));
            }
            Outcome::Refused(why) => return Err(PrivateClearingError::SettlementRefused(why)),
        };

        let clearing = session.market.clearing.as_ref().ok_or(
            PrivateClearingError::PostSettlementMismatch("no clearing was recorded"),
        )?;
        if clearing.winner.value != i128::from(authorization.statement.p_star) {
            return Err(PrivateClearingError::PostSettlementMismatch(
                "recorded winning price differs from verified p*",
            ));
        }
        let winner = session.winning_actor().cloned().ok_or(
            PrivateClearingError::PostSettlementMismatch("recorded winning handle has no actor"),
        )?;
        if winner != preflight.winner {
            return Err(PrivateClearingError::PostSettlementMismatch(
                "winner differs from preflight under the sealed-auction tie policy",
            ));
        }

        let receipt = PrivateClearingReceipt {
            statement: authorization.statement,
            winner,
            settlement_turn,
        };
        session.verified_private_clearing_receipt = Some(receipt.clone());
        Ok(receipt)
    }
}

/// Preflight the live single-unit auction without closing the commit phase or
/// revealing a bid. Every known refusal is resolved before proof verification
/// can authorize mutation.
fn live_clear(session: &DarkBazaarSession) -> Result<LiveClear, PrivateClearingError> {
    if !session.market.is_listed() {
        return Err(PrivateClearingError::NotListed);
    }
    if session.market.is_settled() {
        return Err(PrivateClearingError::AlreadySettled);
    }
    let phase = session.market.phase();
    if phase != Some(Phase::Commit) || session.market.onledger_phase() != Some(0) {
        return Err(PrivateClearingError::PhaseNotCommit(phase));
    }
    if session.market.bids.is_empty() {
        return Err(PrivateClearingError::NoBids);
    }
    if session.market.bids.len() + 1 > dark_bazaar_private::ORDER_COUNT {
        return Err(PrivateClearingError::TooManyBids(session.market.bids.len()));
    }

    // `Auction::winner` iterates a seal-keyed BTreeMap and `max_by_key(value)`
    // selects the last equal maximum. This tuple reproduces that exact policy.
    let placed = session
        .market
        .bids
        .iter()
        .max_by_key(|placed| (placed.bid.value, placed.seal()))
        .expect("nonempty above");
    let high = placed.bid.value;
    let price = u32::try_from(high)
        .ok()
        .filter(|price| (*price as usize) < dark_bazaar_private::PRICE_COUNT)
        .ok_or(PrivateClearingError::PriceOutsideFixedFamily(high))?;
    if high < session.market.reserve {
        return Err(PrivateClearingError::BelowReserve {
            high,
            reserve: session.market.reserve,
        });
    }

    Ok(LiveClear {
        price,
        winner: placed.who.clone(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_offerings::{Action, Offering, SessionConfig};

    use crate::{TURN_BID, TURN_LIST};

    fn actor(name: &str) -> DreggIdentity {
        DreggIdentity(name.to_string())
    }

    fn listed_two_bid_session(offering: &DarkBazaarOffering, seed: u64) -> DarkBazaarSession {
        let mut session = offering
            .open(SessionConfig::with_seed(seed))
            .expect("open Dark Bazaar");
        assert!(
            offering
                .advance(
                    &mut session,
                    Action::new("list", TURN_LIST, 1, true),
                    actor("seller"),
                )
                .landed()
        );
        assert!(
            offering
                .advance(
                    &mut session,
                    Action::new("bid", TURN_BID, 2, true),
                    actor("alice"),
                )
                .landed()
        );
        assert!(
            offering
                .advance(
                    &mut session,
                    Action::new("bid", TURN_BID, 3, true),
                    actor("bob"),
                )
                .landed()
        );
        session
    }

    #[test]
    fn hiding_proof_fail_closes_every_public_join_before_real_settlement() {
        crate::support::install_verified_settlement_gate();
        let offering = DarkBazaarOffering::new();
        let mut session = listed_two_bid_session(&offering, 0xD4_42);
        let mut authorization = session
            .prepare_private_clearing_zk()
            .expect("Tier-1 hiding proof");
        let statement = authorization.statement();
        assert_eq!(statement.session, session.private_proof_session());
        assert_eq!((statement.p_star, statement.v_star), (3, 1));
        let expected = PrivateClearingExpectation::from_statement(statement);
        let receipts_before = session.market.receipts_len();

        authorization.statement.session ^= 1;
        assert!(matches!(
            offering.verify_private_clearing(&session, &authorization, expected),
            Err(PrivateClearingError::SessionMismatch { .. })
        ));
        authorization.statement = statement;

        authorization.statement.rule += 1;
        assert!(matches!(
            offering.verify_private_clearing(&session, &authorization, expected),
            Err(PrivateClearingError::RuleMismatch { .. })
        ));
        authorization.statement = statement;

        let mut wrong_root = expected;
        wrong_root.order_root[0] ^= 1;
        assert!(matches!(
            offering.verify_private_clearing(&session, &authorization, wrong_root),
            Err(PrivateClearingError::RootMismatch)
        ));

        let mut wrong_price = expected;
        wrong_price.price = 2;
        assert!(matches!(
            offering.verify_private_clearing(&session, &authorization, wrong_price),
            Err(PrivateClearingError::PriceMismatch { .. })
        ));

        let mut wrong_volume = expected;
        wrong_volume.volume = 2;
        assert!(matches!(
            offering.verify_private_clearing(&session, &authorization, wrong_volume),
            Err(PrivateClearingError::VolumeMismatch { .. })
        ));

        // Make the independently expected root agree with a tampered public
        // statement. The cheap join passes; proof verification itself refuses.
        authorization.statement.order_root[0] ^= 1;
        let tampered = PrivateClearingExpectation::from_statement(authorization.statement);
        assert!(matches!(
            offering.verify_private_clearing(&session, &authorization, tampered),
            Err(PrivateClearingError::InvalidProof(_))
        ));
        authorization.statement = statement;

        assert_eq!(session.market.receipts_len(), receipts_before);
        assert_eq!(session.market.phase(), Some(Phase::Commit));
        assert!(!session.is_settled());

        let receipt = offering
            .settle_private_verified(&mut session, authorization, expected)
            .expect("proof-authorized real settlement");
        assert_eq!(receipt.price(), 3);
        assert_eq!(receipt.volume(), 1);
        assert_eq!(receipt.winner, actor("bob"));
        assert!(session.is_settled());
        assert_eq!(session.clearing().expect("clear").price(), 3);
        assert!(session.clearing().expect("clear").conserved());
    }

    #[test]
    fn durable_blind_is_exactly_bound_and_stabilizes_only_the_same_claim() {
        crate::support::install_verified_settlement_gate();
        let temp = tempfile::tempdir().unwrap();
        let store = PrivateClearingCommitmentStore::open(temp.path()).unwrap();
        let offering = DarkBazaarOffering::new();
        let mut session = listed_two_bid_session(&offering, 0xD4_43);
        let market_id = [0x41; 32];
        let blind = [0x00C0_FFEE; dark_bazaar_private::DIGEST_WIDTH];

        let first = store
            .bind_or_load(&session, market_id, Some(blind))
            .expect("bind exact private book");
        let loaded = store
            .bind_or_load(&session, market_id, None)
            .expect("load durable binding without resupplying blind");
        assert_eq!(loaded, first);

        let first_orders = first.validate(&session, market_id).unwrap();
        let first_witness =
            PrivateBookWitness::try_from_orders_with_blinding(&first_orders, first.blinding)
                .unwrap();
        let loaded_orders = loaded.validate(&session, market_id).unwrap();
        let loaded_witness =
            PrivateBookWitness::try_from_orders_with_blinding(&loaded_orders, loaded.blinding)
                .unwrap();
        let first_statement =
            dark_bazaar_private::statement(session.private_proof_session(), &first_witness)
                .unwrap();
        let loaded_statement =
            dark_bazaar_private::statement(session.private_proof_session(), &loaded_witness)
                .unwrap();
        assert_eq!(first_statement.order_root, loaded_statement.order_root);

        // The same canonical book under a different blind is a distinct claim.
        let second_session = listed_two_bid_session(&offering, 0xD4_43);
        let second_market_id = [0x42; 32];
        let second = store
            .bind_or_load(
                &second_session,
                second_market_id,
                Some([0x000B_AA42; dark_bazaar_private::DIGEST_WIDTH]),
            )
            .unwrap();
        let second_orders = second.validate(&second_session, second_market_id).unwrap();
        let second_witness =
            PrivateBookWitness::try_from_orders_with_blinding(&second_orders, second.blinding)
                .unwrap();
        let second_statement =
            dark_bazaar_private::statement(second_session.private_proof_session(), &second_witness)
                .unwrap();
        assert_ne!(first_statement.order_root, second_statement.order_root);

        // Changing even one private order invalidates the market binding.
        assert!(
            offering
                .advance(
                    &mut session,
                    Action::new("changed bid", TURN_BID, 1, true),
                    actor("carol"),
                )
                .landed()
        );
        assert!(matches!(
            store.bind_or_load(&session, market_id, None),
            Err(PrivateClearingError::CommitmentBindingMismatch)
        ));

        // The blind reservation is global: another market cannot reuse it for
        // the changed book (nor for any other market-bound claim).
        assert!(matches!(
            store.bind_or_load(&session, [0x43; 32], Some(blind)),
            Err(PrivateClearingError::CommitmentBlindAlreadyUsed)
        ));
    }

    #[test]
    fn fixed_family_refuses_before_proving() {
        crate::support::install_verified_settlement_gate();
        let offering = DarkBazaarOffering::new();
        let mut too_many = listed_two_bid_session(&offering, 7);
        assert!(
            offering
                .advance(
                    &mut too_many,
                    Action::new("third bid", TURN_BID, 1, true),
                    actor("carol"),
                )
                .landed()
        );
        assert!(
            offering
                .advance(
                    &mut too_many,
                    Action::new("fourth bid", TURN_BID, 1, true),
                    actor("dave"),
                )
                .landed()
        );
        assert!(matches!(
            too_many.prepare_private_clearing_zk(),
            Err(PrivateClearingError::TooManyBids(4))
        ));

        let mut wide = offering
            .open(SessionConfig::with_seed(8))
            .expect("open wide");
        assert!(
            offering
                .advance(
                    &mut wide,
                    Action::new("list", TURN_LIST, 0, true),
                    actor("seller"),
                )
                .landed()
        );
        assert!(
            offering
                .advance(
                    &mut wide,
                    Action::new("wide bid", TURN_BID, 4, true),
                    actor("alice"),
                )
                .landed()
        );
        assert!(matches!(
            wide.prepare_private_clearing_zk(),
            Err(PrivateClearingError::PriceOutsideFixedFamily(4))
        ));
    }

    /// MAKE THE ANTI-DRIFT GUARD FIRE.
    ///
    /// `matches_ingress_book` pins the pre-mutation ingress derivation of the
    /// canonical order record against the live-market derivation the durable
    /// binding was built from. A guard that cannot go red is not a guard, so
    /// this exercises BOTH polarities directly against a real binding: the exact
    /// book agrees, and every other in-family book disagrees.
    #[test]
    fn ingress_book_pinning_agrees_only_with_the_exact_bound_book() {
        crate::support::install_verified_settlement_gate();
        let offering = DarkBazaarOffering::new();
        // Bids of 2 (alice) then 3 (bob), in that ingress order.
        let session = listed_two_bid_session(&offering, 0x1_1CE);
        let binding = PrivateClearingCommitmentBinding::new(&session, [0x5A; 32], [3; 8])
            .expect("bind the live two-bid book");

        let exact = PrivateSealedIngressBook::new(vec![(actor("alice"), 2), (actor("bob"), 3)])
            .expect("in-family");
        assert!(
            binding.matches_ingress_book(&exact),
            "the exact bound book must agree, or the production settle would refuse every honest \
             replay"
        );

        // RED: a different limit.
        let changed_limit =
            PrivateSealedIngressBook::new(vec![(actor("alice"), 1), (actor("bob"), 3)])
                .expect("in-family");
        assert!(!binding.matches_ingress_book(&changed_limit));

        // RED: the same limits in a different ingress order. Order is part of
        // the committed record, so a permutation is a different private book.
        let permuted = PrivateSealedIngressBook::new(vec![(actor("bob"), 3), (actor("alice"), 2)])
            .expect("in-family");
        assert!(
            !binding.matches_ingress_book(&permuted),
            "ingress order is committed; a permutation must not pass as the bound book"
        );

        // RED: a dropped bid.
        let shorter = PrivateSealedIngressBook::new(vec![(actor("bob"), 3)]).expect("in-family");
        assert!(!binding.matches_ingress_book(&shorter));
    }
}
