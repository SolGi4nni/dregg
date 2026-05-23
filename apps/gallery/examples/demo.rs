//! Headless demo: register artwork, run auction, settle.
//!
//! Demonstrates the full gallery lifecycle without a frontend:
//! 1. Register an artwork
//! 2. Create an auction
//! 3. Two bidders place commitments
//! 4. Advance to reveal phase
//! 5. Bidders reveal their bids
//! 6. Settle: winner gets artwork, loser gets refund
//! 7. Verify provenance chain
//!
//! ## Running
//!
//! ```bash
//! cargo run -p pyana-gallery --example demo
//! ```

use pyana_app_framework::{CellId, EngineConfig, PyanaEngine};

use pyana_gallery::artwork::ArtworkRegistry;
use pyana_gallery::auction::AuctionEngine;
use pyana_gallery::provenance::ProvenanceRegistry;
use pyana_gallery::{AuctionPhase, compute_bid_commitment, id_to_hex};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Pyana Gallery: Commit-Reveal Auction Demo ===\n");

    let mut engine = PyanaEngine::new(EngineConfig::new(1000));
    let artwork_registry = ArtworkRegistry::new();
    let auction_engine = AuctionEngine::new();
    let provenance_registry = ProvenanceRegistry::new();

    // Participants.
    let artist = CellId::from_bytes([0xAA; 32]);
    let bidder_alice = CellId::from_bytes([0x01; 32]);
    let bidder_bob = CellId::from_bytes([0x02; 32]);

    println!("[1] Registering artwork...");
    println!("    Artist: {}", id_to_hex(artist.as_bytes()));

    auction_engine.set_height(10).await;

    let artwork_id = artwork_registry
        .register(
            &mut engine,
            "Moonrise Over the Federation".to_string(),
            "A luminous digital painting of interconnected nodes under a rising moon.".to_string(),
            *blake3::hash(b"moonrise-image-data").as_bytes(),
            artist,
            2000, // reserve: 2000 units
            vec![
                "digital".to_string(),
                "landscape".to_string(),
                "federation".to_string(),
            ],
            10,
        )
        .await?;

    provenance_registry
        .record_registration(artwork_id, artist, 10)
        .await;

    println!("    Artwork ID: {}", id_to_hex(&artwork_id));
    println!("    Reserve price: 2000");
    println!();

    // =========================================================================
    // Step 2: Create auction
    // =========================================================================
    println!("[2] Creating auction...");
    println!("    Bidding duration: 20 blocks");
    println!("    Reveal duration: 10 blocks");

    let auction_id = auction_engine
        .create_auction(artwork_id, artist, 2000, 20, 10)
        .await?;

    println!("    Auction ID: {}", id_to_hex(&auction_id));
    println!("    Phase: bidding (blocks 10-30)");
    println!("    Reveal: blocks 30-40");
    println!();

    // =========================================================================
    // Step 3: Bidders place commitments
    // =========================================================================
    println!("[3] Bidders placing commitments (amounts HIDDEN)...");

    let alice_nonce = *blake3::hash(b"alice-secret-nonce").as_bytes();
    let bob_nonce = *blake3::hash(b"bob-secret-nonce").as_bytes();
    let alice_amount = 5000u64;
    let bob_amount = 7500u64;

    let alice_commitment = compute_bid_commitment(&bidder_alice, alice_amount, &alice_nonce);
    let bob_commitment = compute_bid_commitment(&bidder_bob, bob_amount, &bob_nonce);

    println!(
        "    Alice commitment: {} (hides bid of {})",
        &id_to_hex(&alice_commitment)[..16],
        alice_amount
    );
    println!(
        "    Bob commitment:   {} (hides bid of {})",
        &id_to_hex(&bob_commitment)[..16],
        bob_amount
    );
    println!("    (Observer sees only hashes — cannot determine bid amounts)");

    auction_engine
        .submit_bid(&auction_id, alice_commitment, bidder_alice, [0xE1; 32])
        .await?;
    auction_engine
        .submit_bid(&auction_id, bob_commitment, bidder_bob, [0xE2; 32])
        .await?;

    println!("    Both commitments accepted.");
    println!();

    // =========================================================================
    // Step 4: Advance to reveal phase
    // =========================================================================
    println!("[4] Advancing to reveal phase...");
    auction_engine.set_height(31).await; // past bidding end (10 + 20 = 30)
    let new_phase = auction_engine.advance_phase(&auction_id).await;
    println!("    Phase: {:?}", new_phase);
    println!();

    // =========================================================================
    // Step 5: Bidders reveal
    // =========================================================================
    println!("[5] Bidders revealing their bids...");

    auction_engine
        .reveal_bid(
            &auction_id,
            alice_commitment,
            bidder_alice,
            alice_amount,
            alice_nonce,
        )
        .await?;
    println!("    Alice revealed: {} units", alice_amount);

    auction_engine
        .reveal_bid(
            &auction_id,
            bob_commitment,
            bidder_bob,
            bob_amount,
            bob_nonce,
        )
        .await?;
    println!("    Bob revealed: {} units", bob_amount);
    println!();

    // =========================================================================
    // Step 6: Settle
    // =========================================================================
    println!("[6] Advancing to settlement and executing...");
    auction_engine.set_height(41).await; // past reveal end (30 + 10 = 40)
    auction_engine.advance_phase(&auction_id).await;

    let result = auction_engine.settle(&auction_id, &mut engine).await?;

    match &result {
        AuctionPhase::Settled {
            winner,
            winning_bid,
            receipt_hash,
        } => {
            println!("    SETTLED!");
            println!("    Winner: {}", id_to_hex(winner.as_bytes()));
            println!("    Winning bid: {}", winning_bid);
            println!("    Receipt: {}", &id_to_hex(receipt_hash)[..16]);

            // Record provenance.
            provenance_registry
                .record_transfer(
                    &artwork_id,
                    artist,
                    *winner,
                    *winning_bid,
                    41,
                    *receipt_hash,
                )
                .await;

            // Update artwork ownership.
            artwork_registry
                .transfer_ownership(&artwork_id, *winner)
                .await;
        }
        _ => {
            println!("    Unexpected result: {:?}", result);
            return Err("Settlement failed".into());
        }
    }
    println!();

    // =========================================================================
    // Step 7: Verify provenance
    // =========================================================================
    println!("[7] Verifying provenance chain...");

    let chain = provenance_registry.get_chain(&artwork_id).await;
    println!("    Chain length: {} entries", chain.len());
    for (i, entry) in chain.iter().enumerate() {
        println!(
            "    [{}] {} -> {} (price: {}, block: {})",
            i,
            &id_to_hex(entry.from.as_bytes())[..8],
            &id_to_hex(entry.to.as_bytes())[..8],
            entry.price,
            entry.block_height,
        );
    }

    let chain_valid = provenance_registry.verify_chain(&artwork_id).await;
    println!(
        "    Chain integrity: {}",
        if chain_valid { "VALID" } else { "BROKEN" }
    );

    let current_owner = provenance_registry
        .current_owner(&artwork_id)
        .await
        .unwrap();
    println!("    Current owner: {}", id_to_hex(current_owner.as_bytes()));
    assert_eq!(current_owner.as_bytes(), bidder_bob.as_bytes());
    println!();

    // =========================================================================
    // Summary
    // =========================================================================
    println!("=== Demo Complete ===\n");
    println!("What was demonstrated:");
    println!("  1. Artwork registration with content-addressed ID");
    println!("  2. Commit-reveal auction (bids hidden until reveal phase)");
    println!("  3. Atomic settlement via TurnComposer (payment + ownership transfer)");
    println!("  4. Provenance chain tracking ownership history");
    println!("  5. Escrow-based bidding with refunds for losers");
    println!();
    println!("Pyana primitives used:");
    println!("  - Cells (artwork identity)");
    println!("  - Capabilities (ownership as delegatable capability)");
    println!("  - Commit-Reveal (BLAKE3 bid commitments)");
    println!("  - Escrow (bidder funds locked during auction)");
    println!("  - TurnComposer (atomic multi-party settlement)");
    println!("  - TemporalPredicate (block-height phase enforcement)");

    Ok(())
}
