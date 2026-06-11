//! Demoable end-to-end run of the sealed-intent multi-agent coordination app.
//!
//! Scenario: three AI agents bid (sealed) for a single compute slot. Each commits a hash of its bid
//! BEFORE anyone reveals, so no agent can peek at or front-run another's bid. After the commit phase
//! closes, the agents reveal; the highest bid wins; the award settles atomically through the VERIFIED
//! per-asset executor. The demo also shows the teeth: a non-committed party is rejected, and a
//! late-switched bid (peeking-then-changing) no longer matches its commitment.
//!
//! Run with: `cargo run -p starbridge-sealed-auction --example sealed_compute_auction`

use starbridge_sealed_auction::{AssetId, Auction, Bid, CellId, Phase, fund_ledger};

const PAY: AssetId = [0u8; 32];
const TOKEN: AssetId = {
    let mut a = [0u8; 32];
    a[0] = 1;
    a
};

const ALICE: CellId = 10;
const BOB: CellId = 11;
const CAROL: CellId = 12;
const SELLER: CellId = 1;
const SLOT: CellId = 2;

fn main() {
    println!("=== Sealed-intent multi-agent coordination: a sealed-bid compute auction ===\n");

    // Three agents privately decide their bids for the compute slot.
    let alice = Bid::new(ALICE, 30, 0xA1A1);
    let bob = Bid::new(BOB, 50, 0xB0B0); // the top bid
    let carol = Bid::new(CAROL, 40, 0xCACA);

    let mut auction = Auction::new(SELLER, SLOT, PAY, TOKEN);

    // ---- COMMIT phase ----
    println!("COMMIT phase — agents broadcast only the hash of their bid:");
    for (name, bid) in [("alice", &alice), ("bob", &bob), ("carol", &carol)] {
        auction.commit(bid.seal()).unwrap();
        let s = bid.seal();
        println!(
            "  {name} committed seal {:02x}{:02x}{:02x}{:02x}…",
            s[0], s[1], s[2], s[3]
        );
    }
    println!("  (no value is visible — no peeking, no front-running)\n");

    // A reveal before the phase closes is rejected.
    assert_eq!(auction.phase, Phase::Commit);
    assert!(auction.reveal(bob).is_err());
    println!("Tooth: a reveal BEFORE the commit phase closes is rejected.\n");

    // ---- close commit, REVEAL phase ----
    auction.seal_commit_phase();
    println!("REVEAL phase opened. Agents now reveal their bids:");
    for (name, bid) in [("alice", &alice), ("bob", &bob), ("carol", &carol)] {
        auction.reveal(*bid).unwrap();
        println!("  {name} revealed value {}", bid.value);
    }
    println!();

    // Tooth: a non-committed outsider cannot reveal.
    let outsider = Bid::new(13, 999, 1);
    assert!(auction.reveal(outsider).is_err());
    println!("Tooth: a NON-COMMITTED party (bidding 999!) cannot reveal — it never sealed a bid.");

    // Tooth: bob cannot peek then switch to a higher bid — the changed bid doesn't match his seal.
    let bob_switched = Bid::new(BOB, 70, 0xB0B0);
    assert!(auction.reveal(bob_switched).is_err());
    println!("Tooth: bob CANNOT switch to a higher bid after peeking — the changed bid no longer");
    println!(
        "       matches his sealed commitment (collision-resistance binds the seal to one bid).\n"
    );

    // ---- SETTLE through the verified executor ----
    let winner = auction.winner().unwrap();
    println!(
        "Winner: agent {} with the top bid {} (sealed-bid first-price).",
        winner.bidder, winner.value
    );

    // Fund a ledger: bob can pay, the slot holds the compute-token, seller is live to receive.
    let ledger = fund_ledger(&[
        (BOB, PAY, 100),
        (SELLER, PAY, 0),
        (SLOT, TOKEN, 100),
        (BOB, TOKEN, 0),
    ]);
    let pay_total = ledger.total_asset(&PAY);
    let token_total = ledger.total_asset(&TOKEN);

    let (post, w) = auction.settle(&ledger).unwrap();
    println!("\nSETTLED atomically through the verified per-asset executor:");
    println!(
        "  seller (cell {SELLER}) was paid          : {}",
        post.get(SELLER, &PAY)
    );
    println!(
        "  winner (cell {}) paid                  : {}",
        w.bidder,
        100 - post.get(BOB, &PAY)
    );
    println!(
        "  winner (cell {}) received compute-token: {}",
        w.bidder,
        post.get(BOB, &TOKEN)
    );
    println!(
        "  slot (cell {SLOT}) delivered             : {}",
        100 - post.get(SLOT, &TOKEN)
    );

    // Conservation: no value minted or burned.
    assert_eq!(post.total_asset(&PAY), pay_total);
    assert_eq!(post.total_asset(&TOKEN), token_total);
    println!(
        "\nValue-neutral: total PAY {pay_total} and total TOKEN {token_total} preserved (no mint/burn)."
    );
    assert_eq!(auction.phase, Phase::Settled);
    println!("\nThe award is final. ( ⌐■_■ )");
}
