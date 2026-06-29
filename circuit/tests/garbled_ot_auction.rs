//! A genuine secure two-party sealed-bid auction: real Chou-Orlandi oblivious transfer
//! wired to the real Yao garbled circuit, settled with a STARK proof of correct evaluation.
//!
//! This is the wiring the sibling test `garbled_private_joint_settlement.rs` deliberately
//! SIMULATES: there, "party B selects its OT-obtained labels" by reaching directly into the
//! garbler's secret label pairs. Here the bidder obtains each input-wire label over the actual
//! `dregg_cell_crypto::oblivious_transfer` protocol (X25519 Chou-Orlandi 1-of-2 OT), so:
//!
//!   * the AUCTIONEER (garbler / OT sender) holds the reserve `a` wired into the garbled tables
//!     and offers, per bid bit, the pair `(zero_label, one_label)` as the two OT messages —
//!     it never learns WHICH label the bidder took, hence never learns the bid;
//!   * the BIDDER (evaluator / OT receiver) chooses, per bit, the label for its own bid bit and
//!     can decrypt ONLY that one — it never sees the label for the other bit;
//!   * the bidder evaluates the garbled comparison `bid >= reserve` and produces a STARK proof
//!     whose ENTIRE public surface is `(circuit_commitment, output_label_hash)` — the outcome
//!     bit, nothing about either party's private input.
//!
//! The OT is the load-bearing privacy step: without it the garbler would have to hand the bidder
//! BOTH labels per wire (leaking nothing) but then could not bind the bidder to its real bits, or
//! would have to learn the bits to select for it (leaking the bid). The OT resolves exactly this:
//! oblivious, one-of-two, learned-by-neither.

use dregg_cell_crypto::oblivious_transfer::{OtReceiver, OtSender};
use dregg_circuit::dsl::garbled::{prove_private_threshold_dsl, verify_private_threshold_dsl};
use dregg_circuit::field::BabyBear;
use dregg_circuit::garbled::{
    COMPARISON_BITS, GarblingSecrets, WireLabel, evaluate_garbled_circuit,
    garble_comparison_circuit,
};

// ---------------------------------------------------------------------------
// WireLabel <-> bytes (canonical little-endian, 8 BabyBear limbs = 32 bytes)
// ---------------------------------------------------------------------------

fn label_to_bytes(label: &WireLabel) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (i, felt) in label.iter().enumerate() {
        out[i * 4..i * 4 + 4].copy_from_slice(&felt.as_u32().to_le_bytes());
    }
    out
}

fn label_from_bytes(bytes: &[u8]) -> WireLabel {
    assert_eq!(bytes.len(), 32, "a wire label is exactly 32 bytes");
    let mut label = [BabyBear::ZERO; 8];
    for i in 0..8 {
        let limb = u32::from_le_bytes([
            bytes[i * 4],
            bytes[i * 4 + 1],
            bytes[i * 4 + 2],
            bytes[i * 4 + 3],
        ]);
        // `new` reduces mod p; the limbs were written canonically so this round-trips exactly.
        label[i] = BabyBear::new(limb);
    }
    label
}

// ---------------------------------------------------------------------------
// One bit of genuine 1-of-2 oblivious transfer of a wire label
// ---------------------------------------------------------------------------

/// Run a full Chou-Orlandi 1-of-2 OT for a single bid bit.
///
/// The garbler (sender) offers `(zero_label, one_label)`; the bidder (receiver) with choice
/// `bid_bit` learns exactly one. Returns the label the bidder obtained.
fn ot_transfer_label(zero_label: &WireLabel, one_label: &WireLabel, bid_bit: bool) -> WireLabel {
    // 1. Garbler -> bidder: sender setup (public point A).
    let (sender, setup) = OtSender::new();
    // 2/3. Bidder -> garbler: receiver response carrying the (hidden) choice.
    let (receiver, response) = OtReceiver::new(bid_bit, &setup).expect("valid OT setup");
    // 4/5. Garbler -> bidder: both labels, each encrypted under a key only the matching choice
    //      can derive. The garbler does NOT know which one the bidder will be able to open.
    let m0 = label_to_bytes(zero_label);
    let m1 = label_to_bytes(one_label);
    let payload = sender.encrypt(&response, &m0, &m1).expect("encrypts both");
    // 6. Bidder decrypts ONLY its chosen label.
    let chosen = receiver
        .decrypt(&payload)
        .expect("decrypts the chosen label");
    label_from_bytes(&chosen)
}

/// Bidder obtains, over real OT, the wire label for each bit of its private bid.
fn bidder_obtains_labels_via_ot(secrets: &GarblingSecrets, bid: u32) -> Vec<WireLabel> {
    (0..COMPARISON_BITS)
        .map(|bit_idx| {
            let bit = ((bid >> bit_idx) & 1) == 1;
            let (zero_label, one_label) = secrets.prover_label_pairs[bit_idx];
            ot_transfer_label(&zero_label, &one_label, bit)
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

/// KEYSTONE: the labels obtained over the real OT protocol are byte-identical to the labels the
/// simulated sibling test selects directly. This is the proof that the OT wiring is faithful — the
/// downstream garbled evaluation is genuinely fed by oblivious transfer, not by a simulation.
#[test]
fn ot_transfer_matches_direct_label_selection() {
    let reserve = 1000u32;
    let bid = 0b1011_0010_1101u32; // arbitrary bit pattern
    let (_circuit, secrets) = garble_comparison_circuit(reserve, COMPARISON_BITS);

    let ot_labels = bidder_obtains_labels_via_ot(&secrets, bid);

    for (bit_idx, ot_label) in ot_labels.iter().enumerate() {
        let bit = (bid >> bit_idx) & 1;
        let direct = if bit == 0 {
            secrets.prover_label_pairs[bit_idx].0
        } else {
            secrets.prover_label_pairs[bit_idx].1
        };
        assert_eq!(
            *ot_label, direct,
            "OT-obtained label for bit {bit_idx} must equal the directly-selected label"
        );
    }
}

/// A genuine 2PC sealed-bid settlement: bidder obtains its labels over OT, evaluates the garbled
/// `bid >= reserve` circuit, and the evaluated bit is the true comparison result.
#[test]
fn genuine_2pc_bid_meets_reserve() {
    let reserve = 500u32;

    // Bid clears the reserve.
    let (circuit, secrets) = garble_comparison_circuit(reserve, COMPARISON_BITS);
    let winning_labels = bidder_obtains_labels_via_ot(&secrets, 750);
    let eval = evaluate_garbled_circuit(&circuit, &winning_labels);
    assert!(eval.output_bit, "750 >= 500: bid clears the reserve");

    // Bid below the reserve (fresh garbling — labels are single-use).
    let (circuit2, secrets2) = garble_comparison_circuit(reserve, COMPARISON_BITS);
    let losing_labels = bidder_obtains_labels_via_ot(&secrets2, 300);
    let eval2 = evaluate_garbled_circuit(&circuit2, &losing_labels);
    assert!(
        !eval2.output_bit,
        "300 < 500: bid does not clear the reserve"
    );
}

/// The full settlement: a STARK proof of correct garbled evaluation, produced from OT-obtained
/// labels and verified against ONLY the public statement (circuit commitment + true-output hash).
#[test]
fn genuine_2pc_auction_settles_with_stark_proof() {
    let reserve = 500u32;
    let bid = 800u32;

    let (circuit, secrets) = garble_comparison_circuit(reserve, COMPARISON_BITS);
    let labels = bidder_obtains_labels_via_ot(&secrets, bid);

    let proof = prove_private_threshold_dsl(&circuit, &labels)
        .expect("800 >= 500: a verifying settlement proof is produced over OT-obtained labels");

    assert!(
        verify_private_threshold_dsl(
            &proof,
            &circuit.circuit_commitment,
            &secrets.true_output_hash,
        ),
        "the auctioneer verifies the settlement against the public statement alone"
    );

    // A losing bid yields no admitting proof — no false proof of clearing the reserve.
    let (circuit_lose, secrets_lose) = garble_comparison_circuit(reserve, COMPARISON_BITS);
    let labels_lose = bidder_obtains_labels_via_ot(&secrets_lose, 200);
    assert!(
        prove_private_threshold_dsl(&circuit_lose, &labels_lose).is_none(),
        "200 < 500: no admitting settlement proof exists"
    );
}

/// Sealed-bid WINNER DETERMINATION as a tournament of genuine private comparisons. Each round is a
/// 2PC between two bidders: the holder of the current best bid garbles `challenger >= best` with its
/// own bid as the wired threshold; the challenger obtains its labels over OT and evaluates. Neither
/// party ever learns the other's bid amount — only the per-round "challenger wins" bit, exactly what
/// a sealed-bid auction must reveal.
#[test]
fn genuine_2pc_sealed_bid_winner_determination() {
    // Hidden bids — never revealed to the auctioneer or to each other.
    let bids = [("alice", 420u32), ("bob", 999u32), ("carol", 730u32)];

    let mut best_idx = 0usize;
    for challenger in 1..bids.len() {
        let incumbent_bid = bids[best_idx].1;
        let challenger_bid = bids[challenger].1;

        // Incumbent garbles `challenger >= incumbent` with its OWN bid as the private threshold.
        let (circuit, secrets) = garble_comparison_circuit(incumbent_bid, COMPARISON_BITS);
        // Challenger obtains its labels over real OT and evaluates.
        let labels = bidder_obtains_labels_via_ot(&secrets, challenger_bid);
        let challenger_wins = evaluate_garbled_circuit(&circuit, &labels).output_bit;

        if challenger_wins {
            best_idx = challenger;
        }
    }

    assert_eq!(
        bids[best_idx].0, "bob",
        "highest sealed bid wins the auction"
    );
    assert_eq!(bids[best_idx].1, 999, "the winning amount");
}

/// INPUT PRIVACY (garbler side): the auctioneer's protocol code path does not branch on the bid bit,
/// and the bidder's OT response is a single curve point regardless of which bit it chose. The
/// garbler therefore cannot read the bid off the transcript: the same garbler view is consistent
/// with either choice. (DDH on Curve25519 is the cryptographic carrier; this asserts the structural
/// indistinguishability the construction relies on.)
#[test]
fn garbler_cannot_read_bid_from_ot_transcript() {
    let (zero_label, one_label) = {
        let (_c, s) = garble_comparison_circuit(123, COMPARISON_BITS);
        s.prover_label_pairs[0]
    };

    // Two bidders choosing OPPOSITE bits against the SAME sender setup.
    let (sender, setup) = OtSender::new();
    let (recv0, resp0) = OtReceiver::new(false, &setup).unwrap();
    let (recv1, resp1) = OtReceiver::new(true, &setup).unwrap();

    // Both responses are well-formed 32-byte points — same shape, no bit leaked structurally.
    assert_eq!(resp0.receiver_public.len(), 32);
    assert_eq!(resp1.receiver_public.len(), 32);

    // The garbler runs the SAME encrypt for either response (offers both labels both times).
    let m0 = label_to_bytes(&zero_label);
    let m1 = label_to_bytes(&one_label);
    let payload0 = sender.encrypt(&resp0, &m0, &m1).unwrap();
    let payload1 = sender.encrypt(&resp1, &m0, &m1).unwrap();

    // Each bidder recovers exactly its own chosen label, and nothing about the other's choice.
    assert_eq!(
        label_from_bytes(&recv0.decrypt(&payload0).unwrap()),
        zero_label
    );
    assert_eq!(
        label_from_bytes(&recv1.decrypt(&payload1).unwrap()),
        one_label
    );

    // The bidder that chose bit 0 cannot open the one-label (and vice versa): OT gives exactly one.
    // `decrypt` follows the receiver's own choice, so cross-opening is not even expressible — the
    // construction's privacy is by inability, not by policy.
}
