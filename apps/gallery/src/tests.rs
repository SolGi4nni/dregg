//! Integration tests covering the full gallery lifecycle.
//!
//! Tests: register → auction → bid → reveal → settle → provenance check

#[cfg(test)]
mod tests {
    use dregg_app_framework::{CellId, EngineConfig, DreggEngine};

    use crate::artwork::ArtworkRegistry;
    use crate::auction::AuctionEngine;
    use crate::bidding::CommitRevealBidding;
    use crate::provenance::ProvenanceRegistry;
    use crate::settlement::AtomicSettlement;
    use crate::{compute_bid_commitment, id_to_hex, verify_bid_reveal};

    /// Helper: create a test engine.
    fn test_engine() -> DreggEngine {
        DreggEngine::new(EngineConfig::new(1000))
    }

    /// Helper: create a deterministic CellId from a byte.
    fn cell(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    #[test]
    fn test_bid_commitment_verify() {
        let bidder = cell(0xAA);
        let amount = 5000u64;
        let nonce = [0xBB; 32];

        let commitment = compute_bid_commitment(&bidder, amount, &nonce);
        assert!(verify_bid_reveal(&commitment, &bidder, amount, &nonce));

        // Wrong amount should fail.
        assert!(!verify_bid_reveal(&commitment, &bidder, 4999, &nonce));

        // Wrong nonce should fail.
        assert!(!verify_bid_reveal(
            &commitment,
            &bidder,
            amount,
            &[0xCC; 32]
        ));

        // Wrong bidder should fail.
        assert!(!verify_bid_reveal(&commitment, &cell(0xDD), amount, &nonce));
    }

    #[test]
    fn test_commit_reveal_bidding() {
        let reserve = 1000;
        let mut bidding = CommitRevealBidding::new(reserve);

        let bidder1 = cell(0x01);
        let bidder2 = cell(0x02);
        let nonce1 = [0x11; 32];
        let nonce2 = [0x22; 32];
        let amount1 = 5000u64;
        let amount2 = 7000u64;

        let commitment1 = compute_bid_commitment(&bidder1, amount1, &nonce1);
        let commitment2 = compute_bid_commitment(&bidder2, amount2, &nonce2);

        // Submit commitments.
        bidding
            .submit_commitment(commitment1, bidder1, [0xE1; 32], 10)
            .unwrap();
        bidding
            .submit_commitment(commitment2, bidder2, [0xE2; 32], 11)
            .unwrap();

        assert_eq!(bidding.commitment_count(), 2);

        // Duplicate commitment from same bidder should fail.
        let dup_result = bidding.submit_commitment([0xFF; 32], bidder1, [0xE3; 32], 12);
        assert!(dup_result.is_err());

        // Reveal bids.
        bidding
            .reveal_bid(commitment1, bidder1, amount1, nonce1)
            .unwrap();
        bidding
            .reveal_bid(commitment2, bidder2, amount2, nonce2)
            .unwrap();

        assert_eq!(bidding.reveal_count(), 2);

        // Wrong reveal should fail.
        // (already revealed, but testing wrong amount on a fresh engine)
        let mut bidding2 = CommitRevealBidding::new(reserve);
        let commitment3 = compute_bid_commitment(&cell(0x03), 3000, &[0x33; 32]);
        bidding2
            .submit_commitment(commitment3, cell(0x03), [0xE4; 32], 20)
            .unwrap();
        let bad_reveal = bidding2.reveal_bid(commitment3, cell(0x03), 9999, [0x33; 32]);
        assert!(bad_reveal.is_err());

        // Determine winner.
        let winner = bidding.determine_winner().unwrap();
        assert_eq!(winner.amount, 7000);
        assert_eq!(winner.bidder.as_bytes(), bidder2.as_bytes());

        // Losers.
        let losers = bidding.losing_bids();
        assert_eq!(losers.len(), 1);
        assert_eq!(losers[0].bidder.as_bytes(), bidder1.as_bytes());
    }

    #[test]
    fn test_bid_below_reserve() {
        let mut bidding = CommitRevealBidding::new(1000);
        let bidder = cell(0x01);
        let nonce = [0x11; 32];
        let amount = 500u64; // below reserve

        let commitment = compute_bid_commitment(&bidder, amount, &nonce);
        bidding
            .submit_commitment(commitment, bidder, [0xE1; 32], 10)
            .unwrap();

        let result = bidding.reveal_bid(commitment, bidder, amount, nonce);
        assert!(result.is_err());
        assert!(
            result
                .unwrap_err()
                .to_string()
                .contains("below reserve price")
        );
    }

    #[tokio::test]
    async fn test_artwork_registration() {
        let mut engine = test_engine();
        let registry = ArtworkRegistry::new();
        let artist = cell(0xAA);
        let image_hash = [0xBB; 32];

        let artwork_id = registry
            .register(
                &mut engine,
                "Test Artwork".to_string(),
                "A beautiful test piece".to_string(),
                image_hash,
                artist,
                1000,
                vec!["test".to_string()],
                5,
            )
            .await
            .unwrap();

        // Verify it exists.
        let artwork = registry.get(&artwork_id).await.unwrap();
        assert_eq!(artwork.title, "Test Artwork");
        assert_eq!(artwork.artist.as_bytes(), artist.as_bytes());
        assert_eq!(artwork.current_owner.as_bytes(), artist.as_bytes());
        assert_eq!(artwork.reserve_price, 1000);

        // Duplicate registration should fail.
        let dup = registry
            .register(
                &mut engine,
                "Test Artwork".to_string(),
                "duplicate".to_string(),
                image_hash,
                artist,
                2000,
                vec![],
                6,
            )
            .await;
        assert!(dup.is_err());
    }

    #[tokio::test]
    async fn test_full_auction_lifecycle() {
        let mut engine = test_engine();
        let artwork_registry = ArtworkRegistry::new();
        let auction_engine = AuctionEngine::new();
        let provenance_registry = ProvenanceRegistry::new();

        let artist = cell(0xAA);
        let bidder1 = cell(0x01);
        let bidder2 = cell(0x02);

        // Set initial height.
        auction_engine.set_height(10).await;

        // Register artwork.
        let artwork_id = artwork_registry
            .register(
                &mut engine,
                "Moon Over River".to_string(),
                "A luminous moon reflected in water".to_string(),
                [0xCC; 32],
                artist,
                1000,
                vec!["landscape".to_string()],
                10,
            )
            .await
            .unwrap();

        provenance_registry
            .record_registration(artwork_id, artist, 10)
            .await;

        // Create auction (10 blocks bidding, 5 blocks reveal).
        let auction_id = auction_engine
            .create_auction(artwork_id, artist, 1000, 10, 5)
            .await
            .unwrap();

        // Submit bids.
        let nonce1 = [0x11; 32];
        let nonce2 = [0x22; 32];
        let amount1 = 5000u64;
        let amount2 = 7500u64;

        let commitment1 = compute_bid_commitment(&bidder1, amount1, &nonce1);
        let commitment2 = compute_bid_commitment(&bidder2, amount2, &nonce2);

        auction_engine
            .submit_bid(&auction_id, commitment1, bidder1, [0xE1; 32])
            .await
            .unwrap();
        auction_engine
            .submit_bid(&auction_id, commitment2, bidder2, [0xE2; 32])
            .await
            .unwrap();

        // Advance to reveal phase.
        auction_engine.set_height(21).await; // past bidding_end_height (10 + 10 = 20)
        let new_phase = auction_engine.advance_phase(&auction_id).await;
        assert!(new_phase.is_some());

        // Reveal bids.
        auction_engine
            .reveal_bid(&auction_id, commitment1, bidder1, amount1, nonce1)
            .await
            .unwrap();
        auction_engine
            .reveal_bid(&auction_id, commitment2, bidder2, amount2, nonce2)
            .await
            .unwrap();

        // Advance to settling phase.
        auction_engine.set_height(26).await; // past reveal_end_height (20 + 5 = 25)
        auction_engine.advance_phase(&auction_id).await;

        // Settle.
        let phase = auction_engine
            .settle(&auction_id, &mut engine)
            .await
            .unwrap();
        match &phase {
            crate::AuctionPhase::Settled {
                winner,
                winning_bid,
                receipt_hash,
            } => {
                assert_eq!(winner.as_bytes(), bidder2.as_bytes());
                assert_eq!(*winning_bid, 7500);
                assert_ne!(*receipt_hash, [0u8; 32]);

                // Update provenance.
                provenance_registry
                    .record_transfer(
                        &artwork_id,
                        artist,
                        *winner,
                        *winning_bid,
                        26,
                        *receipt_hash,
                    )
                    .await;
            }
            _ => panic!("expected Settled phase, got {:?}", phase),
        }

        // Verify provenance chain.
        let chain = provenance_registry.get_chain(&artwork_id).await;
        assert_eq!(chain.len(), 2);
        assert_eq!(chain[0].from.as_bytes(), artist.as_bytes());
        assert_eq!(chain[0].to.as_bytes(), artist.as_bytes());
        assert_eq!(chain[0].price, 0); // registration
        assert_eq!(chain[1].from.as_bytes(), artist.as_bytes());
        assert_eq!(chain[1].to.as_bytes(), bidder2.as_bytes());
        assert_eq!(chain[1].price, 7500);

        // Verify chain integrity.
        assert!(provenance_registry.verify_chain(&artwork_id).await);

        // Verify current owner.
        let owner = provenance_registry
            .current_owner(&artwork_id)
            .await
            .unwrap();
        assert_eq!(owner.as_bytes(), bidder2.as_bytes());
    }

    #[tokio::test]
    async fn test_auction_no_bids() {
        let auction_engine = AuctionEngine::new();
        let artist = cell(0xAA);

        auction_engine.set_height(10).await;

        let auction_id = auction_engine
            .create_auction([0xBB; 32], artist, 1000, 10, 5)
            .await
            .unwrap();

        // Advance past bidding without any bids.
        auction_engine.set_height(21).await;
        let phase = auction_engine.advance_phase(&auction_id).await;
        assert_eq!(phase, Some(crate::AuctionPhase::NoBids));
    }

    #[tokio::test]
    async fn test_provenance_chain_integrity() {
        let registry = ProvenanceRegistry::new();
        let artwork_id = [0xAA; 32];
        let artist = cell(0x01);
        let buyer1 = cell(0x02);
        let buyer2 = cell(0x03);

        registry.record_registration(artwork_id, artist, 1).await;
        registry
            .record_transfer(&artwork_id, artist, buyer1, 1000, 10, [0xA1; 32])
            .await;
        registry
            .record_transfer(&artwork_id, buyer1, buyer2, 2000, 20, [0xA2; 32])
            .await;

        assert!(registry.verify_chain(&artwork_id).await);
        assert_eq!(registry.transfer_count(&artwork_id).await, 3);

        let owner = registry.current_owner(&artwork_id).await.unwrap();
        assert_eq!(owner.as_bytes(), buyer2.as_bytes());
    }

    #[test]
    fn test_settlement_receipt_deterministic() {
        let artwork_id = [0xAA; 32];
        let artist = cell(0x01);
        let winner = cell(0x02);
        let amount = 5000u64;

        // Same inputs should produce same receipt.
        let receipt1 = settlement_receipt(&artwork_id, &artist, &winner, amount);
        let receipt2 = settlement_receipt(&artwork_id, &artist, &winner, amount);
        assert_eq!(receipt1, receipt2);

        // Different inputs should produce different receipt.
        let receipt3 = settlement_receipt(&artwork_id, &artist, &winner, 5001);
        assert_ne!(receipt1, receipt3);
    }

    /// Helper to compute a settlement receipt hash.
    fn settlement_receipt(
        artwork_id: &[u8; 32],
        artist: &CellId,
        winner: &CellId,
        amount: u64,
    ) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-gallery-settlement-receipt-v1");
        hasher.update(artwork_id);
        hasher.update(artist.as_bytes());
        hasher.update(winner.as_bytes());
        hasher.update(&amount.to_le_bytes());
        *hasher.finalize().as_bytes()
    }
}
