//! Source-bound fhEgg ask/bid ingress for the current operator-visible Dark Bazaar.
//!
//! A trader first produces a signed BFV row plus a private
//! [`OrderEncryptionOpening`]. A configured ingress verifier calls
//! [`AuthenticatedOrderBook::accept_opened`], which deterministically reproduces
//! the complete BFV encryption and checks the exact unary order. The verifier
//! then issues an [`OrderSourceCertificate`] for a bidder or a
//! [`ListingOrderSourceCertificate`] that additionally binds the seller's exact
//! asset. These certificates contain no encryption randomness and are safe to
//! replay through the ordinary offering move log.
//!
//! The market first commits the exact seller ask/asset source into a reserved
//! WriteOnce auction slot, then commits each
//! `Bid::seal_with_source(verified_binding_digest)` into its real bidder slot.
//! Consequently the sealed board and the exact signed message/ciphertext inputs
//! are no longer independent objects: substituting the asset, order, ciphertext,
//! actor, certificate, or source digest changes a checked seal.
//! Settlement also reconstructs the ingress-session digest from its independent
//! BFV identity, so a certificate from another collective key or parameter set
//! cannot be paired with the same ciphertext digest.
//!
//! This is a sound same-opening boundary for today's **operator-visible** CRAWL,
//! under the configured source verifier's honesty and Ed25519 key custody. It is
//! not zero knowledge: the verifier sees the order and encryption-randomness
//! opening while checking it. A no-single-viewer deployment still needs the
//! dedicated lattice encryption/range proof; a signature is never described as
//! that proof here.

use dreggnet_offerings::{Action, DreggIdentity, Outcome};
use ed25519_dalek::VerifyingKey;
use fhegg_fhe::order_ingress::{ListingOrderSourceCertificate, OrderSourceCertificate};
use starbridge_sealed_auction::{Phase, commit_bid_effects};

use crate::{
    DarkBazaarOffering, DarkBazaarSession, FHEGG_LISTING_SOURCE_SLOT, FheggBidSourceBinding,
    FheggListingSourceBinding, TURN_BID_FHEGG, TURN_BIND_FHEGG_SUPPLY,
};

const INGRESS_DOMAIN: &str = "dreggnet-market/fhegg/order-ingress/v1";
const MAX_CERTIFICATE_HEX: usize = 2_048;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FheggSourceBindingError {
    NotListed,
    SourceVerifierMissing,
    InvalidSourceVerifier,
    MissingCertificate,
    MalformedCertificate,
    InvalidCertificate,
    ActorMismatch,
    SessionMismatch,
    ListingSourceMissing,
    ListingAlreadyBound,
    BidsAlreadyPlaced,
    SellerMismatch,
    ListingNotInCommitPhase,
    NotOneUnitAsk,
    ListingValueMismatch { listed: i128, certified: usize },
    NotOneUnitBid,
    BidValueMismatch { action: i64, certified: usize },
}

impl std::fmt::Display for FheggSourceBindingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "fhEgg source binding refused: {self:?}")
    }
}

impl std::error::Error for FheggSourceBindingError {}

impl DarkBazaarSession {
    /// Stable pre-board nonce for encrypted order ingress. Unlike the final
    /// settlement nonce, this contains only listing genesis, avoiding a cycle in
    /// which ciphertexts would be needed before their own board commitment.
    pub fn fhegg_order_ingress_nonce(&self) -> Result<[u8; 32], FheggSourceBindingError> {
        if !self.market.is_listed() {
            return Err(FheggSourceBindingError::NotListed);
        }
        let seller = self
            .market
            .seller
            .as_ref()
            .ok_or(FheggSourceBindingError::NotListed)?;
        let mut hasher = blake3::Hasher::new_derive_key(INGRESS_DOMAIN);
        hasher.update(&self.market.seed.to_be_bytes());
        hasher.update(&self.market.reserve.to_be_bytes());
        hasher.update(&(seller.0.len() as u64).to_be_bytes());
        hasher.update(seller.0.as_bytes());
        Ok(*hasher.finalize().as_bytes())
    }
}

impl DarkBazaarOffering {
    /// Install the independent key whose signatures attest that exact BFV
    /// reencryption was checked. The computation-integrity quorum and this
    /// ingress verifier are deliberately separate policies.
    pub fn with_fhegg_source_verifier(
        mut self,
        verifying_key: [u8; 32],
    ) -> Result<Self, FheggSourceBindingError> {
        let key = VerifyingKey::from_bytes(&verifying_key)
            .map_err(|_| FheggSourceBindingError::InvalidSourceVerifier)?;
        if key.is_weak() {
            return Err(FheggSourceBindingError::InvalidSourceVerifier);
        }
        self.fhegg_source_verifier = Some(verifying_key);
        Ok(self)
    }

    /// Build the replayable frontend-neutral move that carries a public source
    /// certificate. No plaintext encryption opening is included.
    pub fn fhegg_source_bound_bid_action(
        value: i64,
        certificate: &OrderSourceCertificate,
    ) -> Action {
        Action::new(
            "Place a source-bound encrypted bid",
            TURN_BID_FHEGG,
            value,
            true,
        )
        .with_text(hex_encode(&certificate.to_wire_bytes()))
    }

    /// Build the replayable seller move that freezes an exact encrypted ask and
    /// its concrete asset identifier into the reserved WriteOnce board slot.
    pub fn fhegg_listing_source_action(certificate: &ListingOrderSourceCertificate) -> Action {
        Action::new(
            "Bind the exact encrypted listing source",
            TURN_BIND_FHEGG_SUPPLY,
            i64::try_from(certificate.limit()).unwrap_or(i64::MAX),
            true,
        )
        .with_text(hex_encode(&certificate.to_wire_bytes()))
    }

    pub(crate) fn advance_fhegg_listing_source(
        &self,
        session: &mut DarkBazaarSession,
        input: &Action,
        actor: DreggIdentity,
    ) -> Outcome {
        let source = match self.verify_listing_source(session, input, &actor) {
            Ok(source) => source,
            Err(error) => return Outcome::Refused(error.to_string()),
        };
        let Some(cell) = session.market.auction_cell else {
            return Outcome::Refused(FheggSourceBindingError::NotListed.to_string());
        };
        let Some(seal) = session.market.fhegg_listing_source_seal_for(&source) else {
            return Outcome::Refused(FheggSourceBindingError::NotListed.to_string());
        };
        let action = session.market.cclerk.make_action(
            cell,
            "commit_bid",
            commit_bid_effects(cell, FHEGG_LISTING_SOURCE_SLOT, &seal),
        );
        let receipt = match session
            .market
            .executor
            .submit_action(&session.market.cclerk, action)
        {
            Ok(receipt) => receipt,
            Err(error) => {
                return Outcome::Refused(format!(
                    "fhEgg listing-source WriteOnce commit was refused: {error}"
                ));
            }
        };
        session.market.fhegg_listing_source = Some(source);
        session.market.receipts.push(receipt.clone());
        Outcome::Landed {
            receipt,
            ended: false,
        }
    }

    pub(crate) fn advance_fhegg_source_bound_bid(
        &self,
        session: &mut DarkBazaarSession,
        input: &Action,
        actor: DreggIdentity,
    ) -> Outcome {
        match self.verify_source_bound_bid(session, input, &actor) {
            Ok(source) => {
                self.market
                    .do_bid_with_source(&mut session.market, input, actor, Some(source))
            }
            Err(error) => Outcome::Refused(error.to_string()),
        }
    }

    fn verify_source_bound_bid(
        &self,
        session: &DarkBazaarSession,
        input: &Action,
        actor: &DreggIdentity,
    ) -> Result<FheggBidSourceBinding, FheggSourceBindingError> {
        if session.market.fhegg_listing_source.is_none() {
            return Err(FheggSourceBindingError::ListingSourceMissing);
        }
        let key_bytes = self
            .fhegg_source_verifier
            .ok_or(FheggSourceBindingError::SourceVerifierMissing)?;
        let key = VerifyingKey::from_bytes(&key_bytes)
            .map_err(|_| FheggSourceBindingError::InvalidSourceVerifier)?;
        let text = input
            .text
            .as_deref()
            .ok_or(FheggSourceBindingError::MissingCertificate)?;
        let wire = hex_decode(text)?;
        let certificate = OrderSourceCertificate::from_wire_bytes(&wire)
            .map_err(|_| FheggSourceBindingError::MalformedCertificate)?;
        certificate
            .verify(&key)
            .map_err(|_| FheggSourceBindingError::InvalidCertificate)?;
        if !certificate.actor_matches(actor.0.as_bytes()) {
            return Err(FheggSourceBindingError::ActorMismatch);
        }
        if certificate.session_nonce() != session.fhegg_order_ingress_nonce()? {
            return Err(FheggSourceBindingError::SessionMismatch);
        }
        if !matches!(certificate.side(), fhegg_fhe::Side::Bid) || certificate.qty() != 1 {
            return Err(FheggSourceBindingError::NotOneUnitBid);
        }
        if usize::try_from(input.arg).ok() != Some(certificate.limit()) {
            return Err(FheggSourceBindingError::BidValueMismatch {
                action: input.arg,
                certified: certificate.limit(),
            });
        }
        Ok(FheggBidSourceBinding {
            session_digest: certificate.session_digest(),
            binding_digest: certificate.binding_digest(),
            message_digest: certificate.message_digest(),
            ciphertext_digest: certificate.ciphertext_digest(),
        })
    }

    fn verify_listing_source(
        &self,
        session: &DarkBazaarSession,
        input: &Action,
        actor: &DreggIdentity,
    ) -> Result<FheggListingSourceBinding, FheggSourceBindingError> {
        if !session.market.is_listed() {
            return Err(FheggSourceBindingError::NotListed);
        }
        if session.market.fhegg_listing_source.is_some() {
            return Err(FheggSourceBindingError::ListingAlreadyBound);
        }
        if !session.market.bids.is_empty() {
            return Err(FheggSourceBindingError::BidsAlreadyPlaced);
        }
        if session.market.phase() != Some(Phase::Commit) {
            return Err(FheggSourceBindingError::ListingNotInCommitPhase);
        }
        if session.market.seller.as_ref() != Some(actor) {
            return Err(FheggSourceBindingError::SellerMismatch);
        }
        let key_bytes = self
            .fhegg_source_verifier
            .ok_or(FheggSourceBindingError::SourceVerifierMissing)?;
        let key = VerifyingKey::from_bytes(&key_bytes)
            .map_err(|_| FheggSourceBindingError::InvalidSourceVerifier)?;
        let text = input
            .text
            .as_deref()
            .ok_or(FheggSourceBindingError::MissingCertificate)?;
        let wire = hex_decode(text)?;
        let certificate = ListingOrderSourceCertificate::from_wire_bytes(&wire)
            .map_err(|_| FheggSourceBindingError::MalformedCertificate)?;
        certificate
            .verify(&key)
            .map_err(|_| FheggSourceBindingError::InvalidCertificate)?;
        if !certificate.actor_matches(actor.0.as_bytes()) {
            return Err(FheggSourceBindingError::ActorMismatch);
        }
        if certificate.session_nonce() != session.fhegg_order_ingress_nonce()? {
            return Err(FheggSourceBindingError::SessionMismatch);
        }
        if !matches!(certificate.side(), fhegg_fhe::Side::Ask) || certificate.qty() != 1 {
            return Err(FheggSourceBindingError::NotOneUnitAsk);
        }
        if usize::try_from(session.market.reserve).ok() != Some(certificate.limit())
            || usize::try_from(input.arg).ok() != Some(certificate.limit())
        {
            return Err(FheggSourceBindingError::ListingValueMismatch {
                listed: session.market.reserve,
                certified: certificate.limit(),
            });
        }
        Ok(FheggListingSourceBinding {
            asset: certificate.asset(),
            session_digest: certificate.session_digest(),
            binding_digest: certificate.binding_digest(),
            message_digest: certificate.message_digest(),
            ciphertext_digest: certificate.ciphertext_digest(),
        })
    }
}

fn hex_encode(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for &byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}

fn hex_decode(text: &str) -> Result<Vec<u8>, FheggSourceBindingError> {
    if text.len() > MAX_CERTIFICATE_HEX || !text.len().is_multiple_of(2) {
        return Err(FheggSourceBindingError::MalformedCertificate);
    }
    let bytes = text.as_bytes();
    let mut out = Vec::with_capacity(bytes.len() / 2);
    for pair in bytes.chunks_exact(2) {
        let high = hex_nibble(pair[0]).ok_or(FheggSourceBindingError::MalformedCertificate)?;
        let low = hex_nibble(pair[1]).ok_or(FheggSourceBindingError::MalformedCertificate)?;
        out.push((high << 4) | low);
    }
    Ok(out)
}

fn hex_nibble(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_offerings::{Offering, SessionConfig};
    use ed25519_dalek::SigningKey;
    use fhegg_fhe::attestation::{BfvPublicIdentity, InputDigest};
    use fhegg_fhe::order_ingress::{
        AuthenticatedOrderBook, OrderEncryptionOpening, OrderIngressSession, SignedOrderSubmission,
    };
    use fhegg_fhe::threshold::{
        BfvParams, CollectivePublicKey, KeygenCoordinator, KeygenSession, ThresholdParty,
    };
    use fhegg_fhe::{Order, Side};

    use crate::fhegg_settlement::FheggSettlementError;
    use crate::{TURN_BID, TURN_LIST, TURN_SETTLE};

    fn collective_key(params: &BfvParams, seed: [u8; 32]) -> (KeygenSession, CollectivePublicKey) {
        let keygen = KeygenSession::from_seed(1, seed).unwrap();
        let (party, contribution) = ThresholdParty::join(&keygen, 0, params).unwrap();
        let mut coordinator = KeygenCoordinator::new(keygen.clone(), params.clone());
        coordinator.accept(contribution).unwrap();
        drop(party);
        (keygen, coordinator.finish().unwrap())
    }

    #[test]
    fn exact_source_certificate_commits_the_real_board_and_refuses_every_substitution() {
        crate::support::install_verified_settlement_gate();
        let source_verifier = SigningKey::from_bytes(&[0x21; 32]);
        let offering = DarkBazaarOffering::new()
            .with_fhegg_source_verifier(source_verifier.verifying_key().to_bytes())
            .unwrap();
        let mut market = offering.open(SessionConfig::with_seed(0xB1_D5)).unwrap();
        assert!(
            offering
                .advance(
                    &mut market,
                    Action::new("list", TURN_LIST, 1, true),
                    DreggIdentity("seller".into()),
                )
                .landed()
        );

        let params = BfvParams::fold_set();
        let (keygen, collective) = collective_key(&params, [0x11; 32]);
        let ingress = OrderIngressSession::new(
            market.fhegg_order_ingress_nonce().unwrap(),
            4,
            &params,
            &collective,
        )
        .unwrap();
        let trader_key = SigningKey::from_bytes(&[0x31; 32]);
        let ask = Order {
            side: Side::Ask,
            limit: 1,
            qty: 1,
        };
        let ask_opening = OrderEncryptionOpening::from_seed([0x40; 32]);
        let (ask_submission, _, _) = SignedOrderSubmission::encrypt_and_sign_with_opening(
            &ingress,
            0,
            0,
            &ask,
            &params,
            &collective,
            &trader_key,
            ask_opening,
        )
        .unwrap();
        let bid = Order {
            side: Side::Bid,
            limit: 3,
            qty: 1,
        };
        let bid_opening = OrderEncryptionOpening::from_seed([0x41; 32]);
        let (bid_submission, _, _) = SignedOrderSubmission::encrypt_and_sign_with_opening(
            &ingress,
            0,
            1,
            &bid,
            &params,
            &collective,
            &trader_key,
            bid_opening,
        )
        .unwrap();
        let mut book =
            AuthenticatedOrderBook::new(ingress, vec![trader_key.verifying_key().to_bytes()])
                .unwrap();
        let ask_binding = book
            .accept_opened(ask_submission, &ask, ask_opening, &params, &collective)
            .unwrap();
        let asset = [0xA5; 32];
        let listing_certificate =
            ask_binding.certify_listing_for_market(b"seller", asset, &source_verifier);
        let listing_action = DarkBazaarOffering::fhegg_listing_source_action(&listing_certificate);

        let bid_binding = book
            .accept_opened(bid_submission, &bid, bid_opening, &params, &collective)
            .unwrap();
        let bid_certificate = bid_binding.certify_for_market(b"alice", &source_verifier);
        let action = DarkBazaarOffering::fhegg_source_bound_bid_action(3, &bid_certificate);

        // Source-bound demand is fail-closed until the seller freezes the exact
        // ask and asset into the board's reserved WriteOnce slot.
        assert!(matches!(
            offering.advance(
                &mut market,
                action.clone(),
                DreggIdentity("alice".into())
            ),
            Outcome::Refused(reason) if reason.contains("ListingSourceMissing")
        ));

        let mut wrong_listing_value = listing_action.clone();
        wrong_listing_value.arg = 2;
        assert!(matches!(
            offering.advance(
                &mut market,
                wrong_listing_value,
                DreggIdentity("seller".into())
            ),
            Outcome::Refused(_)
        ));
        assert!(matches!(
            offering.advance(
                &mut market,
                listing_action.clone(),
                DreggIdentity("mallory".into())
            ),
            Outcome::Refused(reason) if reason.contains("SellerMismatch")
        ));
        let mut substituted_asset = listing_action.clone();
        let mut listing_wire = hex_decode(substituted_asset.text.as_deref().unwrap()).unwrap();
        listing_wire[8] ^= 1;
        substituted_asset.text = Some(hex_encode(&listing_wire));
        assert!(matches!(
            offering.advance(
                &mut market,
                substituted_asset,
                DreggIdentity("seller".into())
            ),
            Outcome::Refused(reason) if reason.contains("InvalidCertificate")
        ));

        // A separately valid listing certificate from another session cannot
        // bind this listing even when every other field agrees.
        let wrong_ingress = OrderIngressSession::new([0x99; 32], 4, &params, &collective).unwrap();
        let wrong_opening = OrderEncryptionOpening::from_seed([0x42; 32]);
        let (wrong_submission, _, _) = SignedOrderSubmission::encrypt_and_sign_with_opening(
            &wrong_ingress,
            0,
            0,
            &ask,
            &params,
            &collective,
            &trader_key,
            wrong_opening,
        )
        .unwrap();
        let mut wrong_book =
            AuthenticatedOrderBook::new(wrong_ingress, vec![trader_key.verifying_key().to_bytes()])
                .unwrap();
        let wrong_binding = wrong_book
            .accept_opened(wrong_submission, &ask, wrong_opening, &params, &collective)
            .unwrap();
        let wrong_session_certificate =
            wrong_binding.certify_listing_for_market(b"seller", asset, &source_verifier);
        assert!(matches!(
            offering.advance(
                &mut market,
                DarkBazaarOffering::fhegg_listing_source_action(&wrong_session_certificate),
                DreggIdentity("seller".into())
            ),
            Outcome::Refused(reason) if reason.contains("SessionMismatch")
        ));

        assert!(
            offering
                .advance(
                    &mut market,
                    listing_action.clone(),
                    DreggIdentity("seller".into()),
                )
                .landed()
        );
        assert!(matches!(
            offering.advance(
                &mut market,
                listing_action,
                DreggIdentity("seller".into())
            ),
            Outcome::Refused(reason) if reason.contains("ListingAlreadyBound")
        ));

        let mut wrong_value = action.clone();
        wrong_value.arg = 2;
        assert!(matches!(
            offering.advance(&mut market, wrong_value, DreggIdentity("alice".into())),
            Outcome::Refused(_)
        ));
        let mut wrong_actor = action.clone();
        wrong_actor.label = "wrong actor".into();
        assert!(matches!(
            offering.advance(&mut market, wrong_actor, DreggIdentity("mallory".into())),
            Outcome::Refused(_)
        ));
        let mut bad_certificate = action.clone();
        let text = bad_certificate.text.as_mut().unwrap();
        let replacement = if text.ends_with('0') { '1' } else { '0' };
        text.pop();
        text.push(replacement);
        assert!(matches!(
            offering.advance(&mut market, bad_certificate, DreggIdentity("alice".into())),
            Outcome::Refused(_)
        ));

        assert!(
            offering
                .advance(&mut market, action, DreggIdentity("alice".into()))
                .landed()
        );
        let exact_inputs = market.fhegg_bound_order_inputs().unwrap();
        market
            .verify_fhegg_bound_order_inputs(&exact_inputs)
            .unwrap();
        let bfv = BfvPublicIdentity::from_public(&params, &keygen, &collective);
        market.verify_fhegg_source_bfv_identity(&bfv, 4).unwrap();
        let (_, wrong_collective) = collective_key(&params, [0x12; 32]);
        let wrong_bfv = BfvPublicIdentity::from_public(&params, &keygen, &wrong_collective);
        assert_eq!(
            market.verify_fhegg_source_bfv_identity(&wrong_bfv, 4),
            Err(FheggSettlementError::ListingSourceBfvDomainMismatch)
        );
        let mut substituted = exact_inputs;
        substituted[1] = InputDigest::ciphertext_bytes(b"unrelated valid ciphertext");
        assert!(matches!(
            market.verify_fhegg_bound_order_inputs(&substituted),
            Err(FheggSettlementError::ListingSourceInputPairCount { found: 0 })
        ));

        let mut duplicated = market.fhegg_bound_order_inputs().unwrap();
        duplicated.extend_from_slice(&duplicated[..2].to_vec());
        assert_eq!(
            market.verify_fhegg_bound_order_inputs(&duplicated),
            Err(FheggSettlementError::ListingSourceInputPairCount { found: 2 })
        );

        // The source digest is part of the actual WriteOnce seal. Corrupting
        // that cell field is detected by the same preflight used at settlement.
        let cell = market.market.auction_cell.unwrap();
        let slot = market.market.bids[0].slot;
        market.market.executor.with_ledger_mut(|ledger| {
            ledger.get_mut(&cell).unwrap().state.fields[FHEGG_LISTING_SOURCE_SLOT][0] ^= 1;
        });
        assert_eq!(
            market.fhegg_source_commitment(),
            Err(FheggSettlementError::ListingSourceBoardMismatch)
        );
        market.market.executor.with_ledger_mut(|ledger| {
            ledger.get_mut(&cell).unwrap().state.fields[FHEGG_LISTING_SOURCE_SLOT][0] ^= 1;
        });
        market.market.executor.with_ledger_mut(|ledger| {
            ledger.get_mut(&cell).unwrap().state.fields[slot][0] ^= 1;
        });
        assert!(matches!(
            market.fhegg_source_commitment(),
            Err(FheggSettlementError::SourceBoardMismatch { slot: found }) if found == slot
        ));
        market.market.executor.with_ledger_mut(|ledger| {
            ledger.get_mut(&cell).unwrap().state.fields[slot][0] ^= 1;
        });

        // The source-bound asset cannot be swapped for another after the clear.
        assert!(
            offering
                .advance(
                    &mut market,
                    Action::new("settle", TURN_SETTLE, 0, true),
                    DreggIdentity("seller".into()),
                )
                .landed()
        );
        let mut empty_world = dreggnet_trade::TradeWorld::new();
        assert!(matches!(
            market
                .market
                .settle_winning_asset(&mut empty_world, dreggnet_trade::AssetId([0xA6; 32])),
            Err(crate::asset_backed::AssetBackedError::SourceAssetMismatch {
                expected,
                provided,
            }) if expected == dreggnet_trade::AssetId(asset)
                && provided == dreggnet_trade::AssetId([0xA6; 32])
        ));

        // Legacy demand cannot retroactively acquire a seller source: its
        // first commit slot is already occupied and fhEgg settlement remains
        // fail-closed rather than synthesizing supply from LIST metadata.
        let mut legacy = offering.open(SessionConfig::with_seed(0xB1_D5)).unwrap();
        assert!(
            offering
                .advance(
                    &mut legacy,
                    Action::new("list", TURN_LIST, 1, true),
                    DreggIdentity("seller".into()),
                )
                .landed()
        );
        assert!(
            offering
                .advance(
                    &mut legacy,
                    Action::new("legacy bid", TURN_BID, 3, true),
                    DreggIdentity("alice".into()),
                )
                .landed()
        );
        assert_eq!(
            legacy.fhegg_source_commitment(),
            Err(FheggSettlementError::UnboundListingSource)
        );
        assert!(matches!(
            offering.advance(
                &mut legacy,
                DarkBazaarOffering::fhegg_listing_source_action(&listing_certificate),
                DreggIdentity("seller".into()),
            ),
            Outcome::Refused(reason) if reason.contains("BidsAlreadyPlaced")
        ));
    }
}
