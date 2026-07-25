//! A genuine secure two-party sealed-bid auction over REAL oblivious transfer + Yao garbled
//! circuits — the runnable face of `circuit/tests/garbled_ot_auction.rs`.
//!
//! Unlike `private_auction.rs` (predicate STARK proofs over Poseidon2 commitments), this demo runs
//! the actual 2PC MPC: the auctioneer garbles `bid >= reserve` with the reserve wired in; each
//! bidder obtains the wire labels for its own bid bits over Chou-Orlandi 1-of-2 oblivious transfer
//! (so the auctioneer never learns the bid); the bidder evaluates the garbled circuit, and the
//! ONLY thing that ever becomes public is the one outcome bit.
//!
//! # What this demo does NOT do any more (retired capability, stated plainly)
//!
//! It used to additionally settle each comparison with `dregg_circuit::dsl::garbled::
//! {prove,verify}_private_threshold_dsl` — a STARK proving that the garbled circuit was evaluated
//! CORRECTLY, so a bidder could not lie about its own outcome bit. Those entry points were deleted
//! with the hand-STARK engine, and no IR-v2 descriptor has been emitted for the garbled-evaluation
//! relation (it is absent from `dregg_circuit::descriptor_by_name`), so there is nothing to call.
//!
//! The consequence is REAL and worth naming: without that proof the outcome bit is only as
//! trustworthy as the evaluator. The OT still hides the bid and the garbled tables still hide the
//! reserve — the PRIVACY property is intact and is what this demo now shows — but the INTEGRITY
//! property (an evaluator cannot misreport) rests on the garbling secrets held by the auctioneer,
//! who re-decodes the output label here, rather than on a proof a third party could check.
//!
//! Run with:  `cargo run -p dregg-demo-agent --example garbled_ot_auction`

use dregg_cell_crypto::oblivious_transfer::{OtReceiver, OtSender};
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
    println!("== genuine 2PC sealed-bid auction (real OT + Yao garbled circuit) ==\n");

    let reserve = 500u32;
    println!("Auctioneer's reserve (private, wired into the garbled tables): hidden");
    println!("Bidders' amounts (private, transferred bit-by-bit over OT):    hidden\n");

    // --- Stage 1: each bidder privately checks it clears the reserve.
    //
    // The comparison really runs: the bidder never sends its bid (only OT choice bits) and the
    // auctioneer never sends the reserve (only garbled tables). The outcome bit is the whole
    // public surface.
    let bidders = [("alice", 420u32), ("bob", 999u32), ("carol", 730u32)];
    let mut qualified: Vec<(&str, u32)> = Vec::new();
    for (name, bid) in bidders {
        let (circuit, secrets) = garble_comparison_circuit(reserve, COMPARISON_BITS);
        let labels = bidder_obtains_labels_via_ot(&secrets, bid);
        let result = evaluate_garbled_circuit(&circuit, &labels);

        // SELF-CHECK, not a print. The whole point of the 2PC is that it computes the SAME answer
        // the parties would get by revealing everything to a trusted third party — so the demo
        // fails loudly if the garbled evaluation ever disagrees with the plaintext comparison.
        // This is what makes the run above evidence rather than narration.
        assert_eq!(
            result.output_bit,
            bid >= reserve,
            "{name}: garbled evaluation ({}) disagreed with the plaintext comparison \
             ({bid} >= {reserve} is {}) — the 2PC computed the WRONG answer",
            result.output_bit,
            bid >= reserve
        );
        // The output LABEL must be the genuine decoding, not merely a bit that happens to match:
        // the evaluator ends holding exactly one of the two output labels, and which one it holds
        // is what the auctioneer decodes.
        let expected_label = if result.output_bit {
            circuit.output_label_true
        } else {
            circuit.output_label_false
        };
        assert_eq!(
            result.output_label, expected_label,
            "{name}: evaluator's output label is not the garbler's label for that outcome"
        );

        if result.output_bit {
            println!("  {name}: clears reserve (outcome bit disclosed; amount never sent)");
            qualified.push((name, bid));
        } else {
            println!("  {name}: below reserve (outcome bit disclosed; amount never sent)");
        }
    }
    assert!(
        !qualified.is_empty(),
        "no bidder cleared the reserve — the tournament below has nothing to run on"
    );

    // --- Stage 2: winner determination as a tournament of genuine private comparisons over OT.
    let mut best = qualified[0];
    for &(name, bid) in &qualified[1..] {
        let (circuit, secrets) = garble_comparison_circuit(best.1, COMPARISON_BITS);
        let labels = bidder_obtains_labels_via_ot(&secrets, bid);
        if evaluate_garbled_circuit(&circuit, &labels).output_bit {
            best = (name, bid);
        }
    }

    // SELF-CHECK: the tournament of private comparisons must land on the same winner that a
    // trusted third party holding every bid in the clear would pick. A tournament of `>=`
    // comparisons is only correct if it actually selects the maximum, so this is the assertion
    // that makes "determined without revealing a bid" a claim about a CORRECT determination.
    let plaintext_winner = qualified
        .iter()
        .copied()
        .max_by_key(|&(_, bid)| bid)
        .expect("qualified is non-empty");
    assert_eq!(
        best.1, plaintext_winner.1,
        "the OT/garbled tournament picked {} ({}) but the true maximum bid is {} ({})",
        best.0, best.1, plaintext_winner.0, plaintext_winner.1
    );

    println!(
        "\nWinner: {} — determined without any party revealing a bid amount.",
        best.0
    );
    println!("Only the per-comparison outcome bit was ever disclosed. ( ⌐■_■ )");
    println!(
        "\nIntegrity note: the outcome bits above are decoded by the garbler from its own secrets.\n\
         The STARK that used to prove each garbled evaluation CORRECT is retired (no IR-v2\n\
         descriptor for the garbled-evaluation relation), so a third party cannot re-check them."
    );
}
