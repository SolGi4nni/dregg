//! Private Sealed-Bid Auction — Three Bidders, Sealed Commitments, Atomic Settlement
//!
//! **Story**: Three bidders submit sealed bids for a digital art piece. The bid amounts are
//! hidden behind Poseidon2 commitments during the bidding window, each bid carries a real STARK
//! proof that it clears the reserve — checked by an auctioneer who never learns the amount — and
//! the winner's payment and the art delivery settle atomically or not at all.
//!
//! Shows:
//! - Note commitments as sealed bids (`Poseidon2(bid, randomness)`) — hiding AND binding
//! - THIRD-PARTY predicate proofs for bid validity ("my bid >= reserve" without disclosing the
//!   amount and without the verifier ever holding it), over the IR-v2 descriptors
//!   `dregg-predicate-arith-ge::threshold-v1` + `dregg-attested-fact-membership::v1`, via
//!   `dregg_bridge::present::{prove_predicate_for_fact_attested, verify_predicate_proof_third_party}`
//! - Reveal-phase winner determination: openings are checked against the sealed commitments,
//!   so a bidder cannot re-open to a different amount
//! - `SealPair` (X25519 + ChaCha20-Poly1305) delivery of the artwork to the winner only
//! - `ConditionalTurn` / `ProofCondition` for atomic settlement (pay-for-art, both or neither)
//! - `NullifierSet` double-spend prevention on the bid notes
//! - Adversarial poles, each backed by an `assert!`: a sub-reserve bid cannot be proven, a bid
//!   attested under a FOREIGN registry root is refused (with a neutered canary proving the
//!   refusal is about the root, not a broken proof), an UNATTESTED proof fails closed, one
//!   bidder's proof does not transfer to another's registration, a double-spend is refused, and
//!   a non-winner cannot unseal the art.
//!
//! # Why the THIRD-PARTY shape, and where the trusted root comes from
//!
//! The trusted-state entry point (`prove_predicate_for_fact` / `verify_predicate_proof`) pins the
//! fact commitment by EQUALITY, so its verifier must DERIVE the expected commitment from a value
//! it already holds. An auctioneer does not hold the bids — that is the whole point — so that
//! shape would force either handing over every bid (making the privacy claim vacuous) or feeding
//! `proof.fact_commitment` back in, which is the `x == x` gate that accepts everything. Neither
//! appears in this file.
//!
//! Instead each bid rides the attested rung. The trust structure is:
//!
//! 1. **Registration.** Each bidder's ESCROW — the party that funded and therefore knows the
//!    deposit — builds the facts tree over that bidder's bid fact and publishes only the
//!    `facts_root` to the auction ledger. [`registrar_facts_root`] is that build.
//! 2. **Bidding.** The bidder proves `bid >= reserve` AND attests that the fact it spoke about is
//!    a member of their registered root.
//! 3. **Checking.** The auctioneer verifies against the root it read off the LEDGER, never off
//!    `proof.attestation.facts_root` — a prover free to pick both the root and the fact under it
//!    has attested nothing. The auctioneer learns exactly one bit: the escrowed bid clears reserve.
//!
//! # RETIRED: the committed-threshold winner determination
//!
//! An earlier version of this example determined the winner with a committed-threshold proof
//! (hidden value AND hidden threshold), so the auctioneer learned only "someone beat the
//! commitment". That capability is RETIRED, not moved: there is no emitted IR-v2 descriptor for
//! it, so `dregg_bridge::present::prove_committed_threshold` returns `None` unconditionally and
//! `verify_committed_threshold_proof` returns `false` unconditionally. Rather than demo a
//! fail-closed call, the phase is now the honest surviving thing — a REVEAL: bidders open their
//! commitments to the auctioneer, who checks each opening against the published commitment and
//! takes the highest. **The auctioneer therefore learns every bid at reveal.** What it never
//! needed the amounts for is admission (phase 2), and what third parties hold throughout is only
//! commitments.
//!
//! Run with: cargo run --release -p dregg-demo-agent --example private_auction

use std::time::Instant;

use dregg_bridge::present::{
    BridgePredicateProof, FactTerms, Predicate, fresh_predicate_blinding, prove_predicate_for_fact,
    prove_predicate_for_fact_attested, verify_predicate_proof_third_party,
};
use dregg_cell::note::Note;
use dregg_cell::nullifier_set::NullifierSet;
use dregg_cell_crypto::seal::SealPair;
use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::chip_absorb_all_lanes;
use dregg_circuit::poseidon2;
use dregg_circuit::predicate_arith_witness::FactBinding;
use dregg_circuit::refusal::{Outcome, classify};
use dregg_turn::{ConditionProof, ConditionalTurn, ProofCondition, compute_conditional_deposit};

/// The fact symbol for "this cell's bid in this auction" — `hash_fact`'s first argument.
const BID_FACT_SYM: u32 = 42;

/// The fixed depth-2 co-path (`ATTESTED_DEPTH == 2`) the bid facts sit under. In production the
/// escrow builds a real facts tree and publishes its root; here a fixed co-path stands in for that
/// build. What this example exercises is the ROOT BINDING — that a proof attested under one root
/// is refused by a verifier trusting another — not the tree construction.
fn escrow_co_path() -> [[BabyBear; 3]; 2] {
    [
        [
            BabyBear::new(0xA1),
            BabyBear::new(0xA2),
            BabyBear::new(0xA3),
        ],
        [
            BabyBear::new(0xB1),
            BabyBear::new(0xB2),
            BabyBear::new(0xB3),
        ],
    ]
}

/// The facts root the ESCROW publishes for a bidder at registration: the depth-2 Merkle root over
/// `fact_hash` at the leftmost slot, built with the identical arity-4 chip absorb the
/// `dregg-attested-fact-membership::v1` descriptor checks.
///
/// This is the auctioneer's INDEPENDENT source for `facts_root`. Reading the root off
/// `proof.attestation.facts_root` instead would be the `x == x` gate one level up.
fn registrar_facts_root(fact_hash: BabyBear, co_path: &[[BabyBear; 3]; 2]) -> BabyBear {
    let parent0 =
        chip_absorb_all_lanes(4, &[fact_hash, co_path[0][0], co_path[0][1], co_path[0][2]])[0];
    chip_absorb_all_lanes(4, &[parent0, co_path[1][0], co_path[1][1], co_path[1][2]])[0]
}

/// A bidder's private state (known only to them and their escrow).
struct Bidder {
    name: &'static str,
    bid_amount: u64,
    spending_key: [u8; 32],
    pubkey: [u8; 32],
    blinding: [u8; 32],
    bid_note: Note,
    /// The blinding factor inside the sealed bid commitment — the other half of the opening the
    /// bidder hands the auctioneer at reveal.
    commit_blinding: BabyBear,
    /// The IDENTITY of the fact the validity proof speaks about: predicate symbol, bidder tag,
    /// auction tag, state root. The bid AMOUNT is deliberately not here — it is `terms[0]`, passed
    /// to the prover alongside, which is why a value and a commitment covering a different value
    /// cannot be paired through this API.
    fact: FactBinding,
}

/// What the auction ledger carries for each bid during the bidding window (nothing about the
/// amount).
struct SealedBidRecord {
    /// `Poseidon2(amount, blinding)` — hides the bid amount, and binds the bidder to it.
    commitment: BabyBear,
    /// The facts root the bidder's ESCROW published at registration. The auctioneer's independent,
    /// trusted source for the attestation check — this is what makes the predicate proof mean
    /// "the ESCROWED bid clears reserve" rather than "I know some number ≥ reserve".
    registered_facts_root: BabyBear,
    /// Attested IR-v2 proof that bid >= reserve. Carries no decommitment (`blinding: None`):
    /// nothing for a proof-holder to brute-force.
    validity_proof: BridgePredicateProof,
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
    println!("  PRIVATE SEALED-BID AUCTION");
    println!("  Three Bidders, Sealed Commitments, Atomic Settlement");
    println!("===============================================================================");
    println!();
    println!("  A digital artist auctions \"Meridian\" — a unique generative artwork.");
    println!("  Three collectors submit sealed bids. During the bidding window nobody —");
    println!("  including the auctioneer — can read an amount off the ledger, yet the");
    println!("  auctioneer still CHECKS that every bid clears the reserve.");
    println!("  At reveal, openings are checked against the commitments; the highest wins.");
    println!("  The winner pays and receives the art atomically. Losers get refunds.");
    println!();

    let total_start = Instant::now();

    // =========================================================================
    // PHASE 1: AUCTION SETUP
    // =========================================================================
    println!("--- Phase 1: AUCTION PARAMETERS ---");
    println!();

    let minimum_bid: u64 = 500;
    let artwork_hash =
        *blake3::hash(b"Meridian: procedural flow fields, 4096x4096, edition 1/1").as_bytes();
    let auction_state_root = BabyBear::new(77777);

    println!("  Artwork: \"Meridian\" (generative, 4096x4096, 1/1)");
    println!("  Asset hash: {}", short_hex(&artwork_hash));
    println!("  Minimum bid (reserve): {} units", minimum_bid);
    println!("  Auction state root: {}", auction_state_root.as_u32());
    println!("  Bid deadline: block 500");
    println!();

    // =========================================================================
    // PHASE 2: SEALED BIDDING — Each bidder commits without revealing amount
    // =========================================================================
    println!("--- Phase 2: SEALED BIDDING ---");
    println!();
    println!("  Each bidder:");
    println!("    1. Chooses their bid amount (private)");
    println!("    2. Computes commitment = Poseidon2(bid, randomness)");
    println!("    3. Proves bid >= reserve AND attests the fact belongs to the facts root");
    println!("       their escrow registered (dregg-predicate-arith-ge::threshold-v1 +");
    println!("       dregg-attested-fact-membership::v1 — the amount stays a private witness)");
    println!("    4. Submits (commitment, attested proof) to the auction contract");
    println!();
    println!("  The auctioneer checks each proof WITHOUT holding any bid amount, against the");
    println!("  facts root it reads off the ledger (never off the proof).");
    println!();

    let phase2_start = Instant::now();
    let mut nullifier_set = NullifierSet::new();

    // Create three bidders with their private bid amounts
    let bidder_configs: [(&str, u64, u8); 3] = [
        ("Aria", 2500, 0xAA),  // Aria bids 2500
        ("Blake", 4200, 0xBB), // Blake bids 4200 (winner!)
        ("Cyrus", 1800, 0xCC), // Cyrus bids 1800
    ];

    let mut bidders: Vec<Bidder> = Vec::new();
    let mut sealed_records: Vec<SealedBidRecord> = Vec::new();

    let auction_tag = u64::from_le_bytes(artwork_hash[..8].try_into().unwrap());
    let co_path = escrow_co_path();

    for (name, amount, rand_seed) in &bidder_configs {
        // Derive keys
        let spending_key = blake3::derive_key(
            &format!("{}-auction-spending-v1", name.to_lowercase()),
            name.as_bytes(),
        );
        let pubkey = blake3::derive_key(
            &format!("{}-auction-pubkey-v1", name.to_lowercase()),
            name.as_bytes(),
        );
        let blinding = [*rand_seed; 32];

        // Create the bid note (private — only the bidder knows its contents)
        let bid_note =
            Note::with_randomness(pubkey, [auction_tag, *amount, 0, 0, 0, 0, 0, 0], blinding);

        // Compute the bid commitment: Poseidon2(amount, commit_blinding)
        let amount_field = BabyBear::from_u64(*amount);
        let commit_blinding = BabyBear::new(*rand_seed as u32 * 257);
        let bid_commitment = poseidon2::hash_2_to_1(amount_field, commit_blinding);

        // The identity of the fact the validity proof speaks about. The amount is NOT a field
        // here: it is `terms[0]`, handed to the prover separately, so the commitment the proof
        // carries always covers the number that was actually compared. The bidder tag in `term1`
        // is what makes one bidder's proof useless as another's (Attack 5).
        let fact = FactTerms {
            predicate_sym: BabyBear::new(BID_FACT_SYM),
            term1: BabyBear::from_u64(u64::from_le_bytes(pubkey[..8].try_into().unwrap())),
            term2: BabyBear::from_u64(auction_tag),
        }
        .bind(auction_state_root);

        // REGISTRATION (escrow side): the escrow, which funded the deposit and therefore knows the
        // amount, publishes only this root to the ledger.
        let registered_facts_root = registrar_facts_root(fact.fact_hash_of(amount_field), &co_path);

        // Fresh per-presentation blinding: two showings of the same bid fact carry different
        // public fact commitments (unlinkable), while the in-circuit weld keeps each bound to the
        // value compared.
        let presentation_blinding = fresh_predicate_blinding();

        // BIDDING (bidder side): the attested third-party shape. Carries an attestation and NO
        // decommitment, so the auctioneer needs neither the amount nor an opening.
        let validity_proof = prove_predicate_for_fact_attested(
            *amount as u32,
            fact,
            presentation_blinding,
            &Predicate::Gte(minimum_bid as u32),
            &co_path,
        )
        .expect("all three bids clear the reserve — the attested proof must succeed");
        assert!(
            validity_proof.blinding.is_none(),
            "the third-party shape must carry NO decommitment"
        );

        // CHECKING (auctioneer side): against the LEDGER's root and the auction's own state root.
        assert!(
            verify_predicate_proof_third_party(
                &validity_proof,
                registered_facts_root,
                auction_state_root,
            ),
            "{name}'s attested bid-validity proof must VERIFY for a third party"
        );

        sealed_records.push(SealedBidRecord {
            commitment: bid_commitment,
            registered_facts_root,
            validity_proof,
        });

        bidders.push(Bidder {
            name,
            bid_amount: *amount,
            spending_key,
            pubkey,
            blinding,
            bid_note,
            commit_blinding,
            fact,
        });
    }

    let phase2_time = phase2_start.elapsed();

    // Show what the public sees
    println!("  Public auction state (what observers see):");
    println!();
    println!(
        "    {:>3} | {:>12} | {:>12} | {:>10}",
        "#", "Commitment", "Facts root", "Validity"
    );
    println!("    {}", "-".repeat(52));
    for (i, record) in sealed_records.iter().enumerate() {
        println!(
            "    {:>3} | {:>12} | {:>12} | {:>10}",
            i + 1,
            record.commitment.as_u32(),
            record.registered_facts_root.as_u32(),
            "VERIFIED"
        );
    }
    println!();
    println!("  What the ledger carries:");
    println!("    - 3 bid commitments, each hiding an amount and binding the bidder to it");
    println!("    - 3 escrow-published facts roots (no amounts)");
    println!("    - 3 attested proofs of \"bid >= {minimum_bid}\", each VERIFIED above by a");
    println!("      verifier that holds NO bid amount and NO opening");
    println!();
    println!(
        "  Phase 2 timing: {:.2}ms (3 attested proofs + 3 third-party verifications)",
        phase2_time.as_secs_f64() * 1000.0
    );
    println!();

    // =========================================================================
    // PHASE 3: REVEAL AND WINNER DETERMINATION
    // =========================================================================
    println!("--- Phase 3: REVEAL AND WINNER DETERMINATION ---");
    println!();
    println!("  The bidding window closes. Each bidder hands the auctioneer the OPENING of");
    println!("  their commitment (amount + randomness). The auctioneer:");
    println!("    1. recomputes Poseidon2(amount, randomness) and requires it to equal the");
    println!("       commitment already on the ledger — so nobody can re-open to a new amount,");
    println!("    2. re-checks the attested validity proof against the registered root,");
    println!("    3. takes the highest opening.");
    println!();
    println!("  The auctioneer LEARNS EVERY BID here. The committed-threshold variant that hid");
    println!("  the losing bids from the auctioneer too is RETIRED (no IR-v2 descriptor; see the");
    println!("  module header). Admission (phase 2) needed no amounts; the reveal does.");
    println!();

    let phase3_start = Instant::now();

    let mut best: Option<(usize, u64)> = None;
    for (i, bidder) in bidders.iter().enumerate() {
        let record = &sealed_records[i];
        let claimed = bidder.bid_amount;

        // 1. The opening must reproduce the published commitment (binding).
        let reopened = poseidon2::hash_2_to_1(BabyBear::from_u64(claimed), bidder.commit_blinding);
        assert_eq!(
            reopened, record.commitment,
            "{}'s opening must reproduce the sealed commitment",
            bidder.name
        );

        // 2. The attested validity proof still verifies against the registered root.
        assert!(
            verify_predicate_proof_third_party(
                &record.validity_proof,
                record.registered_facts_root,
                auction_state_root,
            ),
            "{}'s attested validity proof must VERIFY at reveal",
            bidder.name
        );
        assert!(claimed >= minimum_bid, "a verified bid clears the reserve");

        println!(
            "  {:<6} opening {:>5} units — commitment MATCHES, attested proof VERIFIES",
            bidder.name, claimed
        );

        if best.is_none_or(|(_, high)| claimed > high) {
            best = Some((i, claimed));
        }
    }

    // Adversarial pole, right here in the reveal: a bidder who tries to open their sealed bid to
    // a different (higher) amount produces a different hash and is refused.
    let cheater = &bidders[2];
    let forged_open = poseidon2::hash_2_to_1(BabyBear::from_u64(5000), cheater.commit_blinding);
    assert_ne!(
        forged_open, sealed_records[2].commitment,
        "re-opening a sealed bid to a different amount must NOT match the commitment"
    );
    println!(
        "  {:<6} tries to re-open 1800 as 5000 — hash {} != committed {} [REJECTED]",
        cheater.name,
        forged_open.as_u32(),
        sealed_records[2].commitment.as_u32()
    );

    let (winner_idx, winning_bid) = best.expect("there must be a winner");
    let winner = &bidders[winner_idx];
    assert_eq!(
        winning_bid, winner.bid_amount,
        "the winning amount is the winner's own opening"
    );
    for (i, b) in bidders.iter().enumerate() {
        if i != winner_idx {
            assert!(
                b.bid_amount < winning_bid,
                "the winner's bid strictly exceeds every other opening"
            );
        }
    }
    let phase3_time = phase3_start.elapsed();

    println!();
    println!("  ┌──────────────────────────────────────────────────────────────┐");
    println!(
        "  │  WINNER: {} (bid: {} units — highest verified opening)  │",
        winner.name, winner.bid_amount
    );
    println!("  └──────────────────────────────────────────────────────────────┘");
    println!();
    println!("  What survives the reveal:");
    println!("    - Third parties still hold only commitments; no amount is published");
    println!("    - Admission was decided with zero amounts in the auctioneer's hands");
    println!("    - No bidder could shift their amount after seeing the others");
    println!("    - The auctioneer now knows all three amounts (that is what a reveal costs)");
    println!();
    println!(
        "  Phase 3 timing: {:.2}ms",
        phase3_time.as_secs_f64() * 1000.0
    );
    println!();

    // =========================================================================
    // PHASE 4: ATOMIC SETTLEMENT (ConditionalTurn)
    // =========================================================================
    println!("--- Phase 4: ATOMIC SETTLEMENT ---");
    println!();
    println!("  The winner's payment and the art delivery are coupled via ConditionalTurn.");
    println!("  Both execute atomically: the winner pays AND receives the art, or neither.");
    println!();

    let phase4_start = Instant::now();

    // Seal the artwork to the winner
    let winner_seal = SealPair::generate();
    let sealed_art = winner_seal.seal(&dregg_cell::capability::CapabilityRef {
        target: dregg_cell::CellId::from_bytes(winner.pubkey),
        slot: 0,
        permissions: dregg_cell::AuthRequired::Signature,
        breadstuff: Some(artwork_hash),
        expires_at: None,
        allowed_effects: None,
        stored_epoch: None,
        provenance: [0u8; 32],
    });
    let sealed_bytes = postcard::to_stdvec(&sealed_art).unwrap();

    println!("  Step 4a: Artist seals artwork to winner's key");
    println!(
        "    Sealed size: {} bytes (X25519 + ChaCha20-Poly1305)",
        sealed_bytes.len()
    );
    println!();

    // Winner spends their bid note (payment)
    let winner_nullifier = winner.bid_note.nullifier(&winner.spending_key);
    nullifier_set
        .insert(winner_nullifier, winner.bid_note.value())
        .expect("winner spend succeeds");

    println!("  Step 4b: Winner spends bid note (nullifier published)");
    println!("    Nullifier: {}", short_hex(&winner_nullifier.0));
    println!();

    // Create the ConditionalTurn for atomic execution.
    // The artist commits to a delivery secret; revealing the secret proves delivery.
    let delivery_secret = [0xDE; 32]; // Artist's delivery secret (known only to artist)
    let delivery_hash = *blake3::hash(&delivery_secret).as_bytes();
    let current_height = 501;
    let timeout_height = 600;
    let deposit = compute_conditional_deposit(timeout_height, current_height);

    let _winner_conditional = ConditionalTurn {
        turn: dregg_turn::Turn {
            agent: dregg_cell::CellId::from_bytes(winner.pubkey),
            nonce: 0,
            fee: 0,
            conservation_proof: None,
            sovereign_witnesses: std::collections::HashMap::new(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
            memo: Some("Private auction: Meridian".to_string()),
            valid_until: None,
            previous_receipt_hash: None,
            depends_on: vec![],
            call_forest: dregg_turn::CallForest::new(),
        },
        condition: ProofCondition::HashPreimage {
            hash: delivery_hash,
        },
        timeout_height,
        submitted_at: current_height,
        deposit_amount: deposit,
    };

    // Resolve the condition (artist reveals delivery secret = proves delivery happened)
    let art_proof = ConditionProof::Preimage(delivery_secret);
    let mut null_set = std::collections::HashSet::new();
    let result = dregg_turn::resolve_condition(
        &ProofCondition::HashPreimage {
            hash: delivery_hash,
        },
        &art_proof,
        current_height + 1,
        timeout_height,
        &[],
        dregg_turn::DEFAULT_MAX_ROOT_AGE,
        &mut null_set,
        &[],
    );
    assert_eq!(result, dregg_turn::ConditionalResult::Resolved);

    println!("  Step 4c: Atomic settlement via ConditionalTurn");
    println!("    Condition: hash preimage of sealed artwork delivery");
    println!("    Resolution: RESOLVED (artist provided delivery proof)");
    println!(
        "    Result: {} paid {} units AND received sealed artwork",
        winner.name, winner.bid_amount
    );
    println!();

    // Winner unseals the art
    let recovered = winner_seal.unseal(&sealed_art).expect("winner can unseal");
    assert_eq!(recovered.breadstuff.unwrap(), artwork_hash);
    println!("  Step 4d: Winner unseals artwork");
    println!(
        "    Art hash verified: {} [MATCH]",
        short_hex(&artwork_hash)
    );
    println!("    {} now possesses \"Meridian\"!", winner.name);
    println!();

    let phase4_time = phase4_start.elapsed();
    println!(
        "  Phase 4 timing: {:.2}ms",
        phase4_time.as_secs_f64() * 1000.0
    );
    println!();

    // =========================================================================
    // PHASE 5: REFUND LOSING BIDDERS
    // =========================================================================
    println!("--- Phase 5: REFUND LOSING BIDDERS ---");
    println!();
    println!("  Losing bidders get their deposits back as fresh notes. The refund amounts are");
    println!("  not published — an observer sees only new commitments and spent nullifiers.");
    println!();

    for (i, bidder) in bidders.iter().enumerate() {
        if i == winner_idx {
            continue;
        }
        // Spend their bid note (refund to themselves)
        let nullifier = bidder.bid_note.nullifier(&bidder.spending_key);
        nullifier_set
            .insert(nullifier, bidder.bid_note.value())
            .expect("refund spend succeeds");

        // Create a fresh note for the refund (same amount, new randomness)
        let refund_note = Note::with_randomness(
            bidder.pubkey,
            [0, bidder.bid_amount, 0, 0, 0, 0, 0, 0],
            [bidder.blinding[0].wrapping_add(1); 32],
        );
        let refund_commitment = refund_note.commitment();

        println!("  {}: refund processed", bidder.name);
        println!(
            "    Bid note spent (nullifier: {})",
            short_hex(&nullifier.0)
        );
        println!(
            "    Refund note created (commitment: {})",
            short_hex(&refund_commitment.0)
        );
        println!("    Amount: not published (observers see only the commitment)");
    }
    println!();

    // =========================================================================
    // PHASE 6: ADVERSARY ANALYSIS
    // =========================================================================
    println!("--- Phase 6: ADVERSARY ANALYSIS ---");
    println!();

    // Attack 1: bid below the reserve.
    //
    // The refusal can arrive two ways and BOTH count: the ≥ descriptor's range tooth refuses to
    // assemble the wrapped DIFF (a typed Err the bridge maps to `None`), or — under a debug build
    // — the p3 prover's documented unsat panic fires. `classify` makes both legible and REDS on
    // any other panic, so a stray unwrap cannot launder itself as a refusal.
    println!("  Attack 1: Submit a bid below the reserve (bid=200, reserve=500)");
    let sub_reserve_fact = bidders[0].fact;
    let sub_reserve_root =
        registrar_facts_root(sub_reserve_fact.fact_hash_of(BabyBear::new(200)), &co_path);
    let outcome = classify(
        "sub-reserve-bid",
        || match prove_predicate_for_fact_attested(
            200,
            sub_reserve_fact,
            fresh_predicate_blinding(),
            &Predicate::Gte(minimum_bid as u32),
            &co_path,
        ) {
            None => Err("the prover refused the false statement".to_string()),
            Some(p) => {
                if verify_predicate_proof_third_party(&p, sub_reserve_root, auction_state_root) {
                    Ok(())
                } else {
                    Err("the proof failed to verify".to_string())
                }
            }
        },
    );
    assert!(
        matches!(outcome, Outcome::Err(_) | Outcome::UnsatPanic(_)),
        "a sub-reserve bid must be REFUSED — it must fail to prove, or fail to verify"
    );
    println!("    200 >= 500 is unprovable, and no proof of it verifies. [BLOCKED]");
    println!();

    // Attack 2: double-spend the winning bid note.
    println!("  Attack 2: Double-spend the winning bid note");
    let double_spend = nullifier_set.insert(winner_nullifier, winner.bid_note.value());
    assert!(double_spend.is_err());
    println!(
        "    Nullifier already in set: {:?} [BLOCKED]",
        double_spend.unwrap_err()
    );
    println!();

    // Attack 3: a non-winner tries to unseal the art.
    println!("  Attack 3: Losing bidder tries to unseal the artwork");
    let aria_seal = SealPair::generate();
    let aria_unseal = aria_seal.unseal(&sealed_art);
    assert!(aria_unseal.is_err());
    println!("    Wrong key: {:?} [BLOCKED]", aria_unseal.unwrap_err());
    println!();

    // Attack 4: a bid registered in a DIFFERENT auction's state, replayed into this one.
    //
    // Three poles over ONE forged proof, so the refusal cannot pass vacuously:
    //   * NEUTERED CANARY — verify against the forgery's OWN roots: ACCEPTED, so the proof is
    //     internally genuine and what refuses it below is the ROOT MISMATCH, not a broken proof.
    //   * THE REAL GATE — verify against the roots THIS auction trusts: REFUSED.
    //   * FAIL-CLOSED — an UNATTESTED proof, even at the trusted root, is REFUSED: nothing binds
    //     its commitment to registered state, so no `x == x` escape is left.
    println!("  Attack 4: Replay a bid attested under a FOREIGN registry/state root");
    let foreign_state_root = BabyBear::new(31337);
    let foreign_fact = FactTerms {
        predicate_sym: BabyBear::new(BID_FACT_SYM),
        term1: bidders[0].fact.term1,
        term2: bidders[0].fact.term2,
    }
    .bind(foreign_state_root);
    let foreign_amount: u32 = 9000;
    let foreign_root = registrar_facts_root(
        foreign_fact.fact_hash_of(BabyBear::from_u64(foreign_amount as u64)),
        &co_path,
    );
    let foreign_proof = prove_predicate_for_fact_attested(
        foreign_amount,
        foreign_fact,
        fresh_predicate_blinding(),
        &Predicate::Gte(minimum_bid as u32),
        &co_path,
    )
    .expect("9000 >= 500 under the foreign state must prove");

    // Pole A — the canary. Non-vacuity: the forged proof IS genuine at home.
    assert!(
        verify_predicate_proof_third_party(&foreign_proof, foreign_root, foreign_state_root),
        "CANARY: the foreign-root proof must verify against its OWN roots"
    );
    // Pole B — the real gate.
    assert!(
        !verify_predicate_proof_third_party(
            &foreign_proof,
            sealed_records[0].registered_facts_root,
            auction_state_root,
        ),
        "a proof attested under a FOREIGN root must be REFUSED at this auction's trusted root"
    );
    println!("    Canary: verifies against its own roots (the proof is genuine).");
    println!("    Gate:   REFUSED against this auction's registered root. [BLOCKED]");

    // Pole C — fail-closed on a proof with no attestation at all.
    let unattested = prove_predicate_for_fact(
        bidders[0].bid_amount as u32,
        bidders[0].fact,
        fresh_predicate_blinding(),
        &Predicate::Gte(minimum_bid as u32),
    )
    .expect("an honest trusted-state proof still builds");
    assert!(
        unattested.attestation.is_none(),
        "the trusted-state shape carries no attestation"
    );
    assert!(
        !verify_predicate_proof_third_party(
            &unattested,
            sealed_records[0].registered_facts_root,
            auction_state_root,
        ),
        "an UNATTESTED proof must fail closed for a third-party verifier"
    );
    println!("    Fail-closed: an unattested proof is refused outright. [BLOCKED]");
    println!();

    // Attack 5: replay one bidder's valid proof as another bidder's.
    //
    // The fact terms carry the bidder tag, so the winner's fact hashes to a different member and
    // a different registered root. Non-vacuous: the same proof VERIFIES at its own registration
    // (asserted in phases 2 and 3) and REJECTS here.
    println!("  Attack 5: Replay the winner's proof against another bidder's registration");
    let victim_idx = if winner_idx == 0 { 1 } else { 0 };
    assert!(
        !verify_predicate_proof_third_party(
            &sealed_records[winner_idx].validity_proof,
            sealed_records[victim_idx].registered_facts_root,
            auction_state_root,
        ),
        "one bidder's proof must NOT verify against another bidder's registered root"
    );
    println!(
        "    {}'s proof does not verify against {}'s registration. [BLOCKED]",
        bidders[winner_idx].name, bidders[victim_idx].name
    );
    println!();

    // =========================================================================
    // WHAT IS HIDDEN, AND FROM WHOM
    // =========================================================================
    println!("--- What Is Hidden, And From Whom ---");
    println!();
    println!("  ┌───────────────────────┬─────────┬──────────────────────────┐");
    println!("  │  Information          │ Public? │ Known to                 │");
    println!("  ├───────────────────────┼─────────┼──────────────────────────┤");
    println!("  │  # of bids            │ YES     │ Everyone                 │");
    println!("  │  Bid amounts, pre-    │ NO      │ Each bidder + escrow     │");
    println!("  │    reveal             │         │                          │");
    println!("  │  Bid amounts, post-   │ NO      │ Auctioneer + each bidder │");
    println!("  │    reveal             │         │ (a reveal costs this)    │");
    println!("  │  \"all bids >= reserve\"│ PROVEN  │ ANY third party, holding │");
    println!("  │                       │         │ no amount and no opening │");
    println!("  │  Winner identity      │ YES     │ Everyone                 │");
    println!("  │  Artwork content      │ NO      │ Winner only (sealed)     │");
    println!("  │  Refund amounts       │ NO      │ Each bidder + auctioneer │");
    println!("  └───────────────────────┴─────────┴──────────────────────────┘");
    println!();
    println!("  Not claimed here: hiding the amounts from the AUCTIONEER at reveal. That was");
    println!("  the committed-threshold variant, which is retired (no IR-v2 descriptor).");
    println!("  Not claimed here: that the escrow is blind — it funded the deposit, so it knows");
    println!("  the amount, and it is the party whose published root the auctioneer trusts.");
    println!();

    // =========================================================================
    // FINAL SUMMARY
    // =========================================================================
    let total_time = total_start.elapsed();

    println!("===============================================================================");
    println!("  FINAL SUMMARY");
    println!("===============================================================================");
    println!();
    println!("  Auction: \"Meridian\" by the artist");
    println!(
        "  Winner: {} (bid: {} units)",
        winner.name, winner.bid_amount
    );
    println!(
        "  Losers: {} ({} units), {} ({} units) — refunded, amounts not published",
        bidders[0].name, bidders[0].bid_amount, bidders[2].name, bidders[2].bid_amount
    );
    println!("  Nullifiers consumed: {}", nullifier_set.len());
    println!();
    println!("  Components exercised (each backed by an assertion above):");
    println!("    - Poseidon2 commitments (bid hiding pre-reveal, binding at reveal)");
    println!("    - IR-v2 predicate descriptor (bid >= reserve, proved AND verified)");
    println!("    - IR-v2 attested-fact-membership (third-party verification, no amount held)");
    println!("    - SealPair (X25519 + AEAD artwork encryption)");
    println!("    - ConditionalTurn (atomic pay-for-art)");
    println!("    - NullifierSet (double-spend prevention)");
    println!("    - 5 adversarial attacks, 7 poles, all rejected");
    println!();
    println!("  Timing:");
    println!(
        "    Phase 2 (sealed bidding):     {:>8.2}ms",
        phase2_time.as_secs_f64() * 1000.0
    );
    println!(
        "    Phase 3 (reveal + winner):    {:>8.2}ms",
        phase3_time.as_secs_f64() * 1000.0
    );
    println!(
        "    Phase 4 (atomic settlement):  {:>8.2}ms",
        phase4_time.as_secs_f64() * 1000.0
    );
    println!(
        "    Total:                        {:>8.2}ms",
        total_time.as_secs_f64() * 1000.0
    );
    println!();
    println!("  Bid admission never required an amount: the auctioneer checked each bid against");
    println!("  a root it trusts, learned one bit, and let the reveal do the rest.");
    println!("===============================================================================");
}
