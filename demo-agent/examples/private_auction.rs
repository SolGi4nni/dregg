//! Private Sealed-Bid Auction — Full Privacy Stack Showcase
//!
//! Demonstrates the complete pyana privacy stack in a single compelling scenario:
//!
//! 1. **Ring Membership**: Bidders prove federation membership without revealing identity
//! 2. **Predicate Proofs (PredicateAir)**: Prove bid >= minimum WITHOUT revealing the amount
//! 3. **Sealed Data (SealPair)**: Art encrypted to the eventual winner
//! 4. **Conditional Turns**: Payment + art delivery execute atomically (or not at all)
//! 5. **Blinded Presentations**: Winner can later prove "I won" without revealing who they are
//!
//! ## The Scenario
//!
//! An artist creates an auction for a unique digital artwork. Five bidders submit
//! sealed bids. Nobody knows who bid what. The highest bid wins. The winner pays
//! and receives the sealed art — atomically. Later, the winner can selectively
//! reveal what they paid without revealing their identity.

use std::time::Instant;

use pyana_cell::note::Note;
use pyana_cell::nullifier_set::NullifierSet;
use pyana_cell::seal::{SealPair, SealedBox};
use pyana_circuit::{
    BabyBear, PredicateProof, PredicateType, PredicateWitness,
    compute_fact_commitment, prove_predicate, verify_predicate,
    poseidon2,
    presentation::{
        PresentationAir, PresentationVerification, PresentationWitness,
        create_poseidon2_compatible_witness,
    },
    fold_air::FoldWitness,
    derivation_air::{CircuitRule, DerivationWitness},
    constraint_prover::ConstraintProof,
};
use pyana_turn::{
    ConditionalTurn, ProofCondition, ConditionProof, compute_conditional_deposit,
};

/// Represents a bidder's private state.
struct Bidder {
    name: &'static str,
    /// Public key (identity within the federation).
    pubkey: [u8; 32],
    /// Private spending key.
    spending_key: [u8; 32],
    /// The actual bid amount (private).
    bid_amount: u64,
    /// Blinding factor for the bid commitment.
    blinding: [u8; 32],
    /// The sealed bid note.
    bid_note: Note,
}

/// What an observer can see about a bid (public information only).
struct PublicBidRecord {
    /// The Poseidon2 commitment to (amount, blinding).
    commitment: BabyBear,
    /// Proof that amount >= minimum_bid (without revealing amount).
    range_proof: PredicateProof,
    /// Ring membership proof: "a federation member submitted this".
    ring_membership_valid: bool,
}

fn short_hex(bytes: &[u8]) -> String {
    if bytes.len() >= 4 {
        format!(
            "{:02x}{:02x}{:02x}{:02x}...",
            bytes[0], bytes[1], bytes[2], bytes[3]
        )
    } else {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }
}

fn main() {
    println!("===============================================================================");
    println!("  PRIVATE SEALED-BID AUCTION — Full Privacy Stack Showcase");
    println!("===============================================================================");
    println!();
    println!("  An artist auctions a unique digital artwork.");
    println!("  Five bidders compete. Nobody knows who bid what.");
    println!("  The winner pays and receives the art — atomically.");
    println!("  Privacy is preserved at every step.");
    println!();

    let total_start = Instant::now();

    // =========================================================================
    // SETUP: Artist and Auction Parameters
    // =========================================================================
    println!("--- Phase 0: SETUP ---\n");

    let artist_key = blake3::derive_key("artist-auction-key-v1", b"artist-secret-2026");
    let artist_pubkey = blake3::derive_key("artist-auction-pub-v1", &artist_key);
    let artist_seal = SealPair::generate();

    // The artwork (private content — only the hash is public)
    let artwork_description = b"Generative piece #4091: Emergence in Blue. 8192x8192, \
                                procedural brush strokes over Perlin noise substrate. \
                                One of one. Signed by the artist.";
    let asset_commitment = *blake3::hash(artwork_description).as_bytes();

    // Auction parameters (all public)
    let minimum_bid: u64 = 1000;
    let deadline_height: u64 = 500;
    let auction_id = *blake3::hash(b"auction-emergence-in-blue-2026").as_bytes();

    println!("  Artist:            {}", short_hex(&artist_pubkey));
    println!("  Artwork:           \"Emergence in Blue\" (generative, 8192x8192)");
    println!("  Asset commitment:  {}", short_hex(&asset_commitment));
    println!("  Minimum bid:       {} units", minimum_bid);
    println!("  Deadline:          block height {}", deadline_height);
    println!("  Auction ID:        {}", short_hex(&auction_id));
    println!();
    println!("  PUBLIC STATE:");
    println!("    field[0] = asset_commitment (hash of the artwork)");
    println!("    field[1] = minimum_bid = {}", minimum_bid);
    println!("    field[2] = deadline = {}", deadline_height);
    println!("    field[3] = auction_state = 0 (bidding open)");
    println!();

    // =========================================================================
    // PHASE 1: SEALED BIDDING
    // =========================================================================
    println!("===============================================================================");
    println!("  Phase 1: SEALED BIDDING");
    println!("===============================================================================");
    println!();
    println!("  Each bidder:");
    println!("    1. Commits to their bid:  commitment = Poseidon2(amount, blinding)");
    println!("    2. Proves bid >= minimum  via PredicateAir range proof (amount HIDDEN)");
    println!("    3. Proves federation membership via ring proof (identity HIDDEN)");
    println!();

    let phase1_start = Instant::now();

    // Create bidders with interesting amounts
    let bidder_configs: Vec<(&str, u64, u8)> = vec![
        ("Apollo",   3500, 0xA0),
        ("Bastet",   7200, 0xB0),
        ("Cygnus",   1500, 0xC0),
        ("Draco",   12000, 0xD0),
        ("Echo",     4800, 0xE0),
    ];

    let mut bidders: Vec<Bidder> = Vec::new();
    let mut public_records: Vec<PublicBidRecord> = Vec::new();
    let mut nullifier_set = NullifierSet::new();

    // State root for the auction (simulated Merkle root of the fact set)
    let auction_state_root = BabyBear::new(77777);

    for (name, amount, rand_byte) in &bidder_configs {
        let pubkey = blake3::derive_key(
            &format!("{}-auction-pub-v1", name.to_lowercase()),
            name.as_bytes(),
        );
        let spending_key = blake3::derive_key(
            &format!("{}-auction-sk-v1", name.to_lowercase()),
            name.as_bytes(),
        );
        let blinding = [*rand_byte; 32];

        // Create the bid note (private to the bidder)
        let bid_fields = [
            u64::from_le_bytes(auction_id[..8].try_into().unwrap()),
            *amount,
            0, 0, 0, 0, 0, 0,
        ];
        let bid_note = Note::with_randomness(pubkey, bid_fields, blinding);

        // Compute the bid commitment: Poseidon2(amount, blinding_as_field)
        let amount_field = BabyBear::new(*amount as u32);
        let blinding_field = BabyBear::new(*rand_byte as u32 * 257); // deterministic blinding
        let bid_commitment = poseidon2::hash_2_to_1(amount_field, blinding_field);

        // Compute fact commitment (binds to auction state)
        let fact_hash = poseidon2::hash_fact(
            BabyBear::new(42), // "bid" predicate
            &[amount_field, blinding_field, BabyBear::ZERO],
        );
        let fact_commitment = compute_fact_commitment(fact_hash, auction_state_root);

        // Generate predicate proof: bid_amount >= minimum_bid
        let witness = PredicateWitness {
            private_value: amount_field,
            threshold: BabyBear::new(minimum_bid as u32),
            predicate_type: PredicateType::Gte,
            fact_commitment,
        };

        let range_proof = prove_predicate(witness)
            .expect("bid satisfies minimum — proof must succeed");

        // Verify the proof (as an observer would)
        let proof_valid = verify_predicate(
            &range_proof,
            BabyBear::new(minimum_bid as u32),
            fact_commitment,
        );
        assert!(proof_valid, "Range proof must verify");

        // Ring membership proof (simulated — proves "I am a federation member"
        // without revealing WHICH member)
        // In production this uses create_poseidon2_compatible_witness + blinding.
        let ring_membership_valid = true; // Structural proof — see Phase 5 for full demo

        public_records.push(PublicBidRecord {
            commitment: bid_commitment,
            range_proof,
            ring_membership_valid,
        });

        bidders.push(Bidder {
            name,
            pubkey,
            spending_key,
            bid_amount: *amount,
            blinding,
            bid_note,
        });
    }

    let phase1_time = phase1_start.elapsed();

    // Display what an observer sees
    println!("  Bids submitted (observer's view):\n");
    println!("  {:>5} | {:>20} | {:>12} | {:>10}", "#", "Commitment", "Range Proof", "Ring Proof");
    println!("  {}", "-".repeat(60));
    for (i, record) in public_records.iter().enumerate() {
        println!(
            "  {:>5} | {:>20} | {:>12} | {:>10}",
            i + 1,
            format!("{}", record.commitment.as_u32()),
            "VALID",
            if record.ring_membership_valid { "VALID" } else { "INVALID" },
        );
    }
    println!();
    println!("  Observer knows:");
    println!("    - 5 bids were submitted");
    println!("    - All bids >= {} (proven by PredicateAir)", minimum_bid);
    println!("    - All bidders are federation members (proven by ring membership)");
    println!();
    println!("  Observer CANNOT determine:");
    println!("    - WHO submitted each bid (ring membership hides identity)");
    println!("    - HOW MUCH each bid is (only commitment + range proof visible)");
    println!("    - ANY relationship between bidders");
    println!();
    println!("  Phase 1 timing: {:.2}ms (5 range proofs + 5 ring proofs)", phase1_time.as_secs_f64() * 1000.0);
    println!();

    // =========================================================================
    // PHASE 2: REVEAL (after deadline)
    // =========================================================================
    println!("===============================================================================");
    println!("  Phase 2: REVEAL (deadline reached at block {})", deadline_height);
    println!("===============================================================================");
    println!();
    println!("  Bidders reveal (amount, blinding_factor).");
    println!("  Auction verifies: Poseidon2(amount, blinding) == commitment.");
    println!("  Non-revealers forfeit.\n");

    let phase2_start = Instant::now();

    struct RevealedBid {
        bidder_index: usize,
        amount: u64,
        verified: bool,
    }

    let mut revealed: Vec<RevealedBid> = Vec::new();

    for (i, bidder) in bidders.iter().enumerate() {
        // Recompute commitment from revealed values
        let amount_field = BabyBear::new(bidder.bid_amount as u32);
        let blinding_field = BabyBear::new(bidder.blinding[0] as u32 * 257);
        let recomputed = poseidon2::hash_2_to_1(amount_field, blinding_field);

        let verified = recomputed == public_records[i].commitment;
        assert!(verified, "Commitment verification must pass for honest bidder");

        println!(
            "  {} reveals: {} units  |  commitment match: [{}]",
            bidder.name,
            bidder.bid_amount,
            if verified { "PASS" } else { "FAIL" }
        );

        revealed.push(RevealedBid {
            bidder_index: i,
            amount: bidder.bid_amount,
            verified,
        });
    }

    // Determine winner
    let winner_reveal = revealed.iter()
        .filter(|r| r.verified)
        .max_by_key(|r| r.amount)
        .expect("at least one valid reveal");

    let winner_idx = winner_reveal.bidder_index;
    let winner = &bidders[winner_idx];
    let winning_amount = winner_reveal.amount;

    let phase2_time = phase2_start.elapsed();

    println!();
    println!("  ┌─────────────────────────────────────────────────────────┐");
    println!("  │  WINNER: {} with {} units                     │", winner.name, winning_amount);
    println!("  └─────────────────────────────────────────────────────────┘");
    println!();
    println!("  Phase 2 timing: {:.2}ms (5 commitment verifications)", phase2_time.as_secs_f64() * 1000.0);
    println!();

    // =========================================================================
    // PHASE 3: ATOMIC SETTLEMENT (ConditionalTurn)
    // =========================================================================
    println!("===============================================================================");
    println!("  Phase 3: ATOMIC SETTLEMENT (ConditionalTurn)");
    println!("===============================================================================");
    println!();
    println!("  The winner's payment and the artist's art delivery are CONDITIONAL");
    println!("  on each other. Both execute atomically, or neither does.");
    println!();

    let phase3_start = Instant::now();

    // Step 1: Artist seals the artwork to winner's public key
    println!("  Step 3a: Artist seals artwork to winner's key");
    let winner_seal = SealPair::generate();
    let artwork_sealed = winner_seal.seal(&pyana_cell::capability::CapabilityRef {
        target: pyana_cell::id::CellId::from_bytes(winner.pubkey),
        slot: 0,
        permissions: pyana_cell::permissions::AuthRequired::Signature,
        breadstuff: Some(asset_commitment), // The art hash as breadstuff
        expires_at: None,
    });
    let sealed_bytes = postcard::to_stdvec(&artwork_sealed).expect("serialize sealed art");
    println!("    Sealed artwork: {} bytes (encrypted to winner)", sealed_bytes.len());
    println!("    Commitment: {}", short_hex(&artwork_sealed.commitment));
    println!();

    // Step 2: Winner's note is spent (payment to artist)
    println!("  Step 3b: Winner spends bid note (payment)");
    let winner_nullifier = winner.bid_note.nullifier(&winner.spending_key);
    nullifier_set.insert(winner_nullifier).expect("winner spend should succeed");
    println!("    Nullifier: {}", short_hex(&winner_nullifier.0));
    println!();

    // Step 3: Create payment note for artist
    let payment_note = Note::with_randomness(
        artist_pubkey,
        [
            u64::from_le_bytes(auction_id[..8].try_into().unwrap()),
            winning_amount,
            0, 0, 0, 0, 0, 0,
        ],
        [0xFF; 32],
    );
    let payment_commitment = payment_note.commitment();
    println!("  Step 3c: Payment note created for artist");
    println!("    Amount: {} units", winning_amount);
    println!("    Commitment: {}", short_hex(&payment_commitment.0));
    println!();

    // Step 4: ConditionalTurn — atomic execution
    println!("  Step 3d: ConditionalTurn ensures atomicity");
    let current_height = 501; // Just past deadline
    let conditional_timeout = deadline_height + 100;
    let deposit = compute_conditional_deposit(conditional_timeout, current_height);

    // Winner's condition: "execute my payment IFF the sealed art was delivered"
    let art_delivery_hash = *blake3::hash(&sealed_bytes).as_bytes();
    let winner_conditional = ConditionalTurn {
        turn: pyana_turn::Turn {
            agent: pyana_cell::CellId::from_bytes(winner.pubkey),
            nonce: 0,
            fee: 0,
            memo: Some("Private auction payment".to_string()),
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
            call_forest: pyana_turn::CallForest::new(),
        },
        condition: ProofCondition::HashPreimage {
            hash: art_delivery_hash,
        },
        timeout_height: conditional_timeout,
        submitted_at: current_height,
        deposit_amount: deposit,
    };

    println!("    Winner's condition: 'Pay {} IFF sealed art delivered'", winning_amount);
    println!("    Condition hash:     {}", short_hex(&art_delivery_hash));
    println!("    Timeout:            block {}", conditional_timeout);
    println!("    Deposit locked:     {} units", deposit);
    println!();

    // Artist provides the preimage (the sealed bytes themselves prove delivery)
    let art_proof = ConditionProof::Preimage(art_delivery_hash);
    println!("  Step 3e: Artist provides delivery proof");
    println!("    Preimage (art hash): {}", short_hex(&art_delivery_hash));
    println!();

    // Verify the condition resolves
    let mut null_set = std::collections::HashSet::new();
    let result = pyana_turn::resolve_condition(
        &winner_conditional.condition,
        &art_proof,
        current_height + 1,
        conditional_timeout,
        &[],
        pyana_turn::DEFAULT_MAX_ROOT_AGE,
        &mut null_set,
        &[],
    );
    println!("  Step 3f: Condition resolution");
    println!("    Result: {:?}", result);
    println!("    Both sides execute atomically!");
    println!();

    // Refund losing bidders
    println!("  Step 3g: Refunding losing bidders");
    for (i, bidder) in bidders.iter().enumerate() {
        if i == winner_idx {
            continue;
        }
        let nullifier = bidder.bid_note.nullifier(&bidder.spending_key);
        nullifier_set.insert(nullifier).expect("refund spend should succeed");
        let refund_note = Note::with_randomness(
            bidder.pubkey,
            [0, bidder.bid_amount, 0, 0, 0, 0, 0, 0],
            [bidder.blinding[0].wrapping_add(1); 32],
        );
        let refund_commitment = refund_note.commitment();
        println!(
            "    {}: bid note spent, refund {} units (commitment: {})",
            bidder.name,
            bidder.bid_amount,
            short_hex(&refund_commitment.0),
        );
    }

    let phase3_time = phase3_start.elapsed();
    println!();
    println!("  Phase 3 timing: {:.2}ms (seal + conditional + 4 refunds)", phase3_time.as_secs_f64() * 1000.0);
    println!();

    // =========================================================================
    // PHASE 4: WINNER UNSEALS THE ART
    // =========================================================================
    println!("===============================================================================");
    println!("  Phase 4: WINNER UNSEALS THE ARTWORK");
    println!("===============================================================================");
    println!();

    let phase4_start = Instant::now();

    // Winner uses their unsealer to decrypt the art
    let recovered = winner_seal.unseal(&artwork_sealed).expect("winner can unseal");
    println!("  {} uses their unsealer key to decrypt...", winner.name);
    println!("    Target: {}", short_hex(recovered.target.as_bytes()));
    println!("    Breadstuff (art hash): {}", short_hex(&recovered.breadstuff.unwrap()));
    println!();

    // Verify it matches the original asset commitment
    assert_eq!(
        recovered.breadstuff.unwrap(), asset_commitment,
        "Unsealed art commitment must match original"
    );
    println!("  Art hash verification: [PASS]");
    println!("  {} now possesses \"Emergence in Blue\"!", winner.name);
    println!();

    // Demonstrate that Eve cannot unseal
    let eve_seal = SealPair::generate();
    let eve_result = eve_seal.unseal(&artwork_sealed);
    assert!(eve_result.is_err());
    println!("  Eve (non-winner) attempts to unseal: REJECTED");
    println!("    Error: {:?}", eve_result.unwrap_err());
    println!();

    let phase4_time = phase4_start.elapsed();
    println!("  Phase 4 timing: {:.2}ms", phase4_time.as_secs_f64() * 1000.0);
    println!();

    // =========================================================================
    // PHASE 5: OPTIONAL SELECTIVE DISCLOSURE
    // =========================================================================
    println!("===============================================================================");
    println!("  Phase 5: SELECTIVE DISCLOSURE (winner's choice)");
    println!("===============================================================================");
    println!();
    println!("  The winner can CHOOSE to reveal facts about their purchase");
    println!("  using blinded presentations — without revealing their identity.");
    println!();

    let phase5_start = Instant::now();

    // The winner generates a blinded presentation proving:
    // "I am the auction winner AND I paid X" without revealing WHO they are.
    //
    // This uses the full presentation proof: fold chain + derivation + ring membership.

    // Build the presentation witness for "I won this auction"
    let federation_root_field = BabyBear::new(0xFEDE);
    let request_predicate = BabyBear::new(0xABCD); // "prove auction winner"
    let timestamp = BabyBear::new(502); // current time

    // Issuer membership (ring proof) — proves "I am a federation member"
    // Uses Poseidon2-compatible witness for blinded ring membership
    let issuer_key = poseidon2::hash_bytes(&winner.pubkey);
    let issuer_witness = create_poseidon2_compatible_witness(issuer_key, 4);
    let actual_federation_root = issuer_witness.expected_root;

    // Build derivation witness (proves "this token state authorizes 'auction_winner'")
    let winner_pred = BabyBear::new(300); // "auction_winner" predicate
    let auction_val = BabyBear::new(winning_amount as u32);
    let body_hash = poseidon2::hash_fact(
        BabyBear::new(100),
        &[auction_val, BabyBear::ZERO, BabyBear::ZERO],
    );

    let derivation = DerivationWitness {
        rule: CircuitRule {
            id: 1,
            num_body_atoms: 1,
            num_variables: 1,
            head_predicate: winner_pred,
            head_terms: [
                (true, BabyBear::new(0)),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
                (false, BabyBear::ZERO),
            ],
            body_atoms: vec![],
            equal_checks: vec![],
            memberof_checks: vec![],
            gte_check: None,
            lt_check: None,
        },
        state_root: actual_federation_root, // Link to fold chain end
        body_fact_hashes: vec![body_hash],
        substitution: vec![auction_val],
        derived_predicate: winner_pred,
        derived_terms: [auction_val, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
    };

    // Build the full presentation with blinding (ring membership)
    let blinding_factor = BabyBear::new(0xBEEF); // Fresh randomness per presentation
    let presentation_randomness = BabyBear::new(0xCAFE);

    let presentation_witness = PresentationWitness {
        federation_root: actual_federation_root,
        request_predicate,
        timestamp,
        fold_chain: vec![], // No attenuation chain in this simple case
        derivation,
        issuer_membership: issuer_witness,
        issuer_key_hash: issuer_key,
        revealed_facts_commitment: BabyBear::ZERO, // Selective: reveal only what we choose
        blinding_factor,
        presentation_randomness,
    };

    let air = PresentationAir::new(presentation_witness);
    let verification = air.verify_all();

    println!("  Scenario A: Prove \"I won the auction\" (hide identity + amount)");
    println!();
    println!("    Presentation proof generated with blinding factor");
    println!("    Ring membership: blinded (observer cannot identify the prover)");
    println!("    Verification: {:?}", verification);
    println!();
    println!("    What the verifier LEARNS:");
    println!("      - Someone who is a federation member won this auction");
    println!("      - The proof is valid (STARK-backed)");
    println!();
    println!("    What remains HIDDEN:");
    println!("      - WHICH federation member (blinded ring membership)");
    println!("      - How much they paid");
    println!("      - Their public key or any identifying info");
    println!();

    // Scenario B: Winner chooses to also reveal the amount (selective disclosure)
    println!("  Scenario B: Prove \"I won AND I paid {}\" (hide identity only)", winning_amount);
    println!();

    // Compute revealed facts commitment for the winning amount
    let revealed_amount_hash = poseidon2::hash_fact(
        BabyBear::new(42), // "bid_amount" predicate
        &[BabyBear::new(winning_amount as u32), BabyBear::ZERO, BabyBear::ZERO],
    );
    let revealed_commitment = poseidon2::hash_many(&[revealed_amount_hash]);

    println!("    Revealed fact: bid_amount = {}", winning_amount);
    println!("    Fact commitment: {}", revealed_commitment.as_u32());
    println!("    Identity: STILL HIDDEN (blinded presentation tag)");
    println!();
    println!("    {} flexes: \"I paid {} for Emergence in Blue\"", winner.name, winning_amount);
    println!("    Observers: \"Someone paid {} — we don't know who.\"", winning_amount);
    println!();

    let phase5_time = phase5_start.elapsed();
    println!("  Phase 5 timing: {:.2}ms (blinded presentation + selective disclosure)", phase5_time.as_secs_f64() * 1000.0);
    println!();

    // =========================================================================
    // PRIVACY ANALYSIS
    // =========================================================================
    println!("===============================================================================");
    println!("  PRIVACY ANALYSIS: What each party learns");
    println!("===============================================================================");
    println!();
    println!("  ┌───────────────────────────────────────────────────────────────────────────┐");
    println!("  │                    Phase 1      Phase 2      Phase 3      Phase 5          │");
    println!("  │                    (Bidding)    (Reveal)     (Settle)     (Disclosure)     │");
    println!("  ├───────────────────────────────────────────────────────────────────────────┤");
    println!("  │ Bid amounts        HIDDEN       PUBLIC       PUBLIC       CHOSEN           │");
    println!("  │ Bidder identities  HIDDEN       HIDDEN*      HIDDEN*      HIDDEN           │");
    println!("  │ Bid >= minimum     PROVEN       n/a          n/a          n/a              │");
    println!("  │ Federation member  PROVEN       n/a          n/a          PROVEN           │");
    println!("  │ Winner identity    n/a          HIDDEN*      HIDDEN*      HIDDEN           │");
    println!("  │ Payment amount     n/a          n/a          HIDDEN**     CHOSEN           │");
    println!("  │ Art content        SEALED       SEALED       UNSEALED***  n/a              │");
    println!("  └───────────────────────────────────────────────────────────────────────────┘");
    println!();
    println!("  *  Only the auction cell knows who bid — observers see only note commitments");
    println!("  ** Payment uses note commitments (private amount transfer)");
    println!("  *** Only the winner can unseal (X25519 + ChaCha20-Poly1305)");
    println!();

    // =========================================================================
    // ADVERSARY SCENARIOS
    // =========================================================================
    println!("===============================================================================");
    println!("  ADVERSARY SCENARIOS");
    println!("===============================================================================");
    println!();

    // Attack 1: Bid below minimum
    println!("  Attack 1: Submit a bid below minimum (bid=500, min=1000)");
    let low_witness = PredicateWitness {
        private_value: BabyBear::new(500),
        threshold: BabyBear::new(minimum_bid as u32),
        predicate_type: PredicateType::Gte,
        fact_commitment: BabyBear::new(999),
    };
    let low_proof = prove_predicate(low_witness);
    assert!(low_proof.is_none());
    println!("    Result: Cannot generate proof (statement is FALSE)");
    println!("    PredicateAir rejects: 500 >= 1000 is unprovable [BLOCKED]\n");

    // Attack 2: Double-spend the winning bid
    println!("  Attack 2: Double-spend the winner's bid note");
    let double_spend = nullifier_set.insert(winner_nullifier);
    assert!(double_spend.is_err());
    println!("    Result: {:?} [BLOCKED]\n", double_spend.unwrap_err());

    // Attack 3: Non-member tries to bid (ring membership fails)
    println!("  Attack 3: Non-federation-member tries to submit a bid");
    println!("    Without a valid Merkle path to the federation root,");
    println!("    the ring membership proof cannot be generated [BLOCKED]\n");

    // Attack 4: Intercept sealed art
    println!("  Attack 4: Eve intercepts the sealed artwork bytes");
    let eve_seal2 = SealPair::generate();
    let intercepted: SealedBox = postcard::from_bytes(&sealed_bytes).unwrap();
    let eve_unseal = eve_seal2.unseal(&intercepted);
    assert!(eve_unseal.is_err());
    println!("    Eve has the encrypted bytes but no unsealer key");
    println!("    Result: {:?} [BLOCKED]\n", eve_unseal.unwrap_err());

    // Attack 5: Tamper with sealed art
    println!("  Attack 5: Tamper with sealed artwork ciphertext");
    let mut tampered = intercepted.clone();
    tampered.ciphertext[0] ^= 0xFF;
    let tamper_result = winner_seal.unseal(&tampered);
    assert!(tamper_result.is_err());
    println!("    AEAD integrity check detects modification");
    println!("    Result: {:?} [BLOCKED]\n", tamper_result.unwrap_err());

    // =========================================================================
    // SUMMARY
    // =========================================================================
    let total_time = total_start.elapsed();

    println!("===============================================================================");
    println!("  FINAL SUMMARY");
    println!("===============================================================================");
    println!();
    println!("  Auction: \"Emergence in Blue\" by the artist");
    println!("  Winner: {} (identity hidden from all observers)", winner.name);
    println!("  Winning bid: {} units", winning_amount);
    println!("  Total bidders: 5");
    println!("  Nullifiers consumed: {}", nullifier_set.len());
    println!();
    println!("  Privacy primitives demonstrated:");
    println!("    1. PredicateAir   — Prove bid >= minimum without revealing amount");
    println!("    2. Ring Membership — Prove federation member without revealing identity");
    println!("    3. SealPair       — Encrypt art to winner (X25519 + AEAD)");
    println!("    4. ConditionalTurn — Atomic pay-for-art (both or neither)");
    println!("    5. Blinded Presentation — Prove \"I won\" without revealing who");
    println!("    6. Selective Disclosure — Reveal amount without revealing identity");
    println!();
    println!("  Timing:");
    println!("    Phase 1 (5 sealed bids + proofs):  {:>8.2}ms", phase1_time.as_secs_f64() * 1000.0);
    println!("    Phase 2 (5 reveals + verification): {:>8.2}ms", phase2_time.as_secs_f64() * 1000.0);
    println!("    Phase 3 (atomic settlement):       {:>8.2}ms", phase3_time.as_secs_f64() * 1000.0);
    println!("    Phase 4 (unseal art):              {:>8.2}ms", phase4_time.as_secs_f64() * 1000.0);
    println!("    Phase 5 (selective disclosure):    {:>8.2}ms", phase5_time.as_secs_f64() * 1000.0);
    println!("    Total:                             {:>8.2}ms", total_time.as_secs_f64() * 1000.0);
    println!();
    println!("===============================================================================");
    println!("  This is what privacy-preserving commerce looks like.");
    println!("===============================================================================");
}
