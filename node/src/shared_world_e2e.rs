//! shared_world_e2e.rs — TWO IDENTITIES, ONE LIVE SHARED WORLD, PROVEN BY CO-ACTING.
//!
//! The first REAL rung of MULTI-PERSON deos, proven headless (like `mud_client_e2e`): TWO
//! distinct key-ceremony identities connect to ONE shared world hosted in a node, and:
//!
//!   1. PRESENCE — each identity flips its seat's present flag (a signed turn) → a watcher
//!      reading the ledger sees BOTH are present (the presence readout);
//!   2. A ACTS, B OBSERVES IT LIVE — B subscribes to the node's receipt event stream, A
//!      posts to the SHARED board, and B's stream YIELDS A's receipt (attributed to A's
//!      identity cell) → B re-reads the board and sees A's value. The world updated for B,
//!      not just the actor — the load-bearing live-sync bit;
//!   3. B FIRES BACK, A OBSERVES IT LIVE — symmetric: A's stream yields B's receipt and A
//!      re-reads B's value off the SHARED board. The shared state evolves for BOTH;
//!   4. ATTRIBUTION — every observed receipt carries `agent` (which identity acted) +
//!      `turn_hash` (the receipt); the board's two lanes hold A's vs B's last value;
//!   5. THE OVER-REACH (the refusal) — identity B fires `touch-private` over a cell only A
//!      holds a cap on; B can SEE the verb but the executor REFUSES the B-signed write,
//!      leaving the cell untouched — while A's own touch of the same cell commits.
//!
//! Every accepted turn is a real signed `/turns/submit` on the ONE ledger; live sync runs
//! over the genuine `/api/events/stream` SSE — the same wires a cockpit would drive.
#![cfg(all(test, feature = "deos-host"))]

use std::time::Duration;

use dregg_sdk_net::ReceiptStream;

use crate::shared_world::{SharedClient, boot_shared_world};

/// Pull the next receipt off a live stream, bounded so a stuck stream fails the test
/// instead of hanging. Returns the receipt's firing identity (`agent`) + turn hash hex.
async fn next_receipt_within(
    stream: &mut ReceiptStream,
    within: Duration,
) -> Option<(dregg_types::CellId, String)> {
    let r = tokio::time::timeout(within, stream.next()).await.ok()??;
    Some((r.agent, dregg_types::hex_encode(&r.turn_hash)))
}

/// Drain a stream until a receipt attributed to `actor` arrives (skipping any earlier
/// presence/post receipts that may still be in flight), bounded by `within`. Returns the
/// matching receipt's turn hash, or `None` if it never arrives in time.
async fn await_receipt_from(
    stream: &mut ReceiptStream,
    actor: dregg_types::CellId,
    within: Duration,
) -> Option<String> {
    let deadline = tokio::time::Instant::now() + within;
    loop {
        let remaining = deadline.saturating_duration_since(tokio::time::Instant::now());
        if remaining.is_zero() {
            return None;
        }
        let (agent, turn_hash) = next_receipt_within(stream, remaining).await?;
        if agent == actor {
            return Some(turn_hash);
        }
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 4)]
async fn two_identities_co_inhabit_one_live_shared_world() {
    // ── CONNECT ── boot ONE shared world; build TWO clients, each a DISTINCT identity. ──
    let session = boot_shared_world("shared-world-alice", "shared-world-bob")
        .await
        .expect("boot the shared world");
    let alice = SharedClient::seat_a(&session);
    let bob = SharedClient::seat_b(&session);

    // The two identities are genuinely distinct cells on the one ledger.
    assert_ne!(
        alice.identity(),
        bob.identity(),
        "Alice and Bob are distinct key-ceremony identities"
    );

    // Both discover the SAME shared-world surface (one space, not two forks).
    let a_verbs = alice
        .discover(&session.server_cell_hex)
        .await
        .expect("Alice discovers the shared world");
    let b_verbs = bob
        .discover(&session.server_cell_hex)
        .await
        .expect("Bob discovers the shared world");
    for verb in ["present", "post", "touch-private"] {
        assert!(a_verbs.iter().any(|v| v == verb), "Alice sees `{verb}`");
        assert!(b_verbs.iter().any(|v| v == verb), "Bob sees `{verb}`");
    }

    // ── (1) PRESENCE ── each identity announces itself; both flags flip on the ledger. ──
    assert!(
        !alice.a_present().await.expect("a present pre"),
        "nobody is present before connecting"
    );
    assert!(
        alice.present().await.expect("Alice presents").accepted,
        "Alice's present turn commits"
    );
    assert!(
        bob.present().await.expect("Bob presents").accepted,
        "Bob's present turn commits"
    );
    // EITHER client reads the SAME shared presence state — both seats are present.
    assert!(
        bob.a_present().await.expect("a present post"),
        "Bob sees Alice present (shared presence)"
    );
    assert!(
        alice.b_present().await.expect("b present post"),
        "Alice sees Bob present (shared presence)"
    );

    // ── (2) A ACTS, B OBSERVES IT LIVE ──────────────────────────────────────────────────
    // Bob subscribes to ALICE'S live turns on the shared world BEFORE Alice acts.
    let mut bob_feed = bob.subscribe_to_identity(alice.identity());
    // Tiny settle so the SSE subscription is established (it tails from the current head).
    tokio::time::sleep(Duration::from_millis(400)).await;

    let alice_post = alice
        .post(11)
        .await
        .expect("Alice posts to the shared board");
    assert!(
        alice_post.accepted,
        "Alice's post commits on the shared ledger; error={:?}",
        alice_post.error
    );

    // BOB OBSERVES ALICE'S TURN LIVE — the receipt arrives on Bob's stream, attributed to
    // Alice's identity. This is the load-bearing live-sync proof.
    let observed = await_receipt_from(&mut bob_feed, alice.identity(), Duration::from_secs(10))
        .await
        .expect("Bob's live stream delivers Alice's post receipt");
    assert_eq!(
        Some(&observed),
        alice_post.turn_hash.as_ref(),
        "the receipt Bob observed live IS Alice's committed post (same turn hash)"
    );
    // Having been woken live, Bob re-reads the SHARED board and sees Alice's value.
    assert_eq!(
        bob.board_last_from_a().await.expect("board lane A"),
        11,
        "Bob sees Alice's posted value on the shared board (the world updated for the watcher)"
    );
    assert_eq!(
        bob.board_count().await.expect("board count after A"),
        1,
        "the shared post count advanced for both"
    );

    // ── (3) B FIRES BACK, A OBSERVES IT LIVE ────────────────────────────────────────────
    let mut alice_feed = alice.subscribe_to_identity(bob.identity());
    tokio::time::sleep(Duration::from_millis(400)).await;

    let bob_post = bob.post(22).await.expect("Bob posts to the shared board");
    assert!(
        bob_post.accepted,
        "Bob's post commits; error={:?}",
        bob_post.error
    );
    let observed_b = await_receipt_from(&mut alice_feed, bob.identity(), Duration::from_secs(10))
        .await
        .expect("Alice's live stream delivers Bob's post receipt");
    assert_eq!(
        Some(&observed_b),
        bob_post.turn_hash.as_ref(),
        "the receipt Alice observed live IS Bob's committed post"
    );
    assert_eq!(
        alice.board_last_from_b().await.expect("board lane B"),
        22,
        "Alice sees Bob's posted value on the shared board"
    );

    // ── (4) ATTRIBUTION + SHARED EVOLUTION ──────────────────────────────────────────────
    // The one shared board carries BOTH identities' contributions, each in its own lane,
    // and the shared count reflects both co-acts — the state evolved for everyone.
    assert_eq!(
        alice.board_count().await.expect("final count"),
        2,
        "two co-acts (one each) landed on the one shared board"
    );
    assert_eq!(alice.board_last_from_a().await.unwrap(), 11);
    assert_eq!(alice.board_last_from_b().await.unwrap(), 22);
    // The two observed receipts were attributed to DISTINCT identities (real attribution).
    assert_ne!(
        alice_post.turn_hash, bob_post.turn_hash,
        "the two posts are distinct receipted turns"
    );

    // ── (5) THE OVER-REACH (the refusal) ────────────────────────────────────────────────
    // Bob can SEE `touch-private` but holds NO cap over PRIVATE-A: the executor refuses.
    assert!(
        !bob.private_touched().await.expect("private pre"),
        "PRIVATE-A starts untouched"
    );
    let bob_reach = bob
        .touch_private()
        .await
        .expect("Bob attempts the over-reach");
    assert!(
        !bob_reach.accepted,
        "Bob CANNOT write PRIVATE-A (no cap held); outcome={bob_reach:?}"
    );
    assert!(
        !bob.private_touched().await.expect("private after refusal"),
        "the refused over-reach left PRIVATE-A untouched on the ledger"
    );
    // …while ALICE, who WAS granted the cap, writes the same cell successfully — proving
    // the refusal was authority, not a broken affordance.
    let alice_touch = alice
        .touch_private()
        .await
        .expect("Alice touches PRIVATE-A");
    assert!(
        alice_touch.accepted,
        "Alice (capped) writes PRIVATE-A; error={:?}",
        alice_touch.error
    );
    assert!(
        alice.private_touched().await.expect("private after Alice"),
        "Alice's authorized touch flipped PRIVATE-A on the ledger"
    );
}
