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

use dregg_circuit_prove::dark_bazaar_private::{
    self, DarkBazaarPrivateZkProof, PrivateOrder, PublicStatement,
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

impl PrivateClearingReceipt {
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
        let live = live_clear(self)?;
        let mut orders = Vec::with_capacity(self.market.bids.len() + 1);
        for placed in &self.market.bids {
            orders.push(PrivateOrder::bid(1, placed.bid.value as u8));
        }
        orders.push(PrivateOrder::ask(1, live.price as u8));
        let (proof, statement) =
            dark_bazaar_private::prove_orders_zk(self.private_proof_session(), &orders)
                .map_err(PrivateClearingError::InvalidProof)?;
        Ok(PrivateClearingAuthorization::new(proof, statement))
    }
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

        Ok(PrivateClearingReceipt {
            statement: authorization.statement,
            winner,
            settlement_turn,
        })
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
    fn fixed_family_refuses_before_proving() {
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
}
