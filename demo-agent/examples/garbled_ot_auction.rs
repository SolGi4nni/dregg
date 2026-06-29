//! A genuine secure two-party sealed-bid auction over REAL oblivious transfer + Yao garbled
//! circuits — the runnable face of `circuit/tests/garbled_ot_auction.rs`.
//!
//! Unlike `private_auction.rs` (committed-threshold STARK proofs over Poseidon2 commitments), this
//! demo runs the actual 2PC MPC: the auctioneer garbles `bid >= reserve` with the reserve wired in;
//! each bidder obtains the wire labels for its own bid bits over Chou-Orlandi 1-of-2 oblivious
//! transfer (so the auctioneer never learns the bid); the bidder evaluates the garbled circuit and
//! settles with a STARK proof of correct evaluation whose only public surface is the outcome bit.
//!
//! Run with:  `cargo run -p dregg-demo-agent --example garbled_ot_auction`

use dregg_cell_crypto::oblivious_transfer::{OtReceiver, OtSender};
use dregg_circuit::dsl::garbled::{prove_private_threshold_dsl, verify_private_threshold_dsl};
use dregg_circuit::field::BabyBear;
use dregg_circuit::garbled::{
    COMPARISON_BITS, GarblingSecrets, WireLabel, evaluate_garbled_circuit,
    garble_comparison_circuit,
};

fn label_to_bytes(label: &WireLabel) -> [u8; 32] {
    let mut out = [0u8; 32];
    for (i, felt) in label.iter().enumerate() {
        out[i * 4..i * 4 + 4].copy_from_slice(&felt.as_u32().to_le_bytes());
    }
    out
}

fn label_from_bytes(bytes: &[u8]) -> WireLabel {
    let mut label = [BabyBear::ZERO; 8];
    for i in 0..8 {
        let limb = u32::from_le_bytes([
            bytes[i * 4],
            bytes[i * 4 + 1],
            bytes[i * 4 + 2],
            bytes[i * 4 + 3],
        ]);
        label[i] = BabyBear::new(limb);
    }
    label
}

/// One bit of genuine Chou-Orlandi 1-of-2 OT of a wire label.
fn ot_transfer_label(zero_label: &WireLabel, one_label: &WireLabel, bid_bit: bool) -> WireLabel {
    let (sender, setup) = OtSender::new();
    let (receiver, response) = OtReceiver::new(bid_bit, &setup).expect("valid OT setup");
    let payload = sender
        .encrypt(
            &response,
            &label_to_bytes(zero_label),
            &label_to_bytes(one_label),
        )
        .expect("encrypts both labels");
    label_from_bytes(
        &receiver
            .decrypt(&payload)
            .expect("decrypts the chosen label"),
    )
}

/// Bidder obtains, over real OT, the label for every bit of its private bid.
fn bidder_obtains_labels_via_ot(secrets: &GarblingSecrets, bid: u32) -> Vec<WireLabel> {
    (0..COMPARISON_BITS)
        .map(|bit_idx| {
            let bit = ((bid >> bit_idx) & 1) == 1;
            let (zero_label, one_label) = secrets.prover_label_pairs[bit_idx];
            ot_transfer_label(&zero_label, &one_label, bit)
        })
        .collect()
}

fn main() {
    println!("== genuine 2PC sealed-bid auction (real OT + Yao garbled circuit + STARK) ==\n");

    let reserve = 500u32;
    println!("Auctioneer's reserve (private, wired into the garbled tables): hidden");
    println!("Bidders' amounts (private, transferred bit-by-bit over OT):    hidden\n");

    // --- Stage 1: each bidder privately checks it clears the reserve, settling with a STARK proof.
    let bidders = [("alice", 420u32), ("bob", 999u32), ("carol", 730u32)];
    let mut qualified: Vec<(&str, u32)> = Vec::new();
    for (name, bid) in bidders {
        let (circuit, secrets) = garble_comparison_circuit(reserve, COMPARISON_BITS);
        let labels = bidder_obtains_labels_via_ot(&secrets, bid);
        match prove_private_threshold_dsl(&circuit, &labels) {
            Some(proof) => {
                let ok = verify_private_threshold_dsl(
                    &proof,
                    &circuit.circuit_commitment,
                    &secrets.true_output_hash,
                );
                println!(
                    "  {name}: clears reserve — STARK settlement proof {}",
                    if ok { "VERIFIES" } else { "FAILS" }
                );
                qualified.push((name, bid));
            }
            None => println!("  {name}: below reserve — no admitting proof (cannot fake clearing)"),
        }
    }

    // --- Stage 2: winner determination as a tournament of genuine private comparisons over OT.
    let mut best = qualified[0];
    for &(name, bid) in &qualified[1..] {
        let (circuit, secrets) = garble_comparison_circuit(best.1, COMPARISON_BITS);
        let labels = bidder_obtains_labels_via_ot(&secrets, bid);
        if evaluate_garbled_circuit(&circuit, &labels).output_bit {
            best = (name, bid);
        }
    }

    println!(
        "\nWinner: {} — determined without any party revealing a bid amount.",
        best.0
    );
    println!("Only the per-comparison outcome bit was ever disclosed. ( ⌐■_■ )");
}
