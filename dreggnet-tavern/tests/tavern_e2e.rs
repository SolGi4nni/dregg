//! tavern_e2e.rs — N IDENTITIES, ONE PERSISTENT TAVERN, PROVEN BY CO-INHABITING IT.
//!
//! The shared hub / tavern re-homes the deployed live-co-inhabitance rung (`shared_world`)
//! onto a social BETWEEN-RUNS place, and this drives it end-to-end, headless, over the real
//! node wire:
//!
//!   0. UN-FAKEABLE PRESENCE (the negative) — before anyone enters, a patron tries to flip
//!      ANOTHER patron's presence seat. It is REFUSED by the executor's authority gate (no
//!      cap held), and that seat stays empty — you cannot fake being online as someone else;
//!   1. PRESENCE — N distinct key-ceremony identities ENTER; each seat's PRESENT flag flips,
//!      attributed. A patron's own enter commits (it holds its own seat's cap);
//!   2. THE LFG BOARD — each `post` is a real attributed turn on the ONE shared board; the
//!      shared count advances for everyone and each patron's lane carries its own value;
//!   3. LIVE SYNC — patron B subscribes to patron A's live turns; A posts; B's stream YIELDS
//!      A's receipt (attributed to A) and B re-reads A's value off the shared board — the
//!      tavern updated for the WATCHER, not just the actor;
//!   4. THE PARTY-UP HOOK — patrons join the shared party roster; a formed party is the
//!      roster carrying every joiner's attributed marker;
//!   5. THE MARKET STALL + THE OVER-REACH (the refusal, NON-VACUOUS) — a patron `list`s on
//!      its OWN private stall (commits); a DIFFERENT patron `poke_stall`s that same stall and
//!      is REFUSED (no cap held), leaving it unchanged — while the OWNER pokes its own stall
//!      successfully, proving the refusal was authority, not a broken affordance.
//!
//! Every accepted turn is a real signed `/turns/submit` on the ONE ledger; live sync runs
//! over the genuine `/api/events/stream` SSE.
//!
//! One consolidated test (not several) on purpose: the deos-host SpiderMonkey runtime is a
//! process-global the host thread never drops, so the process must `_exit(0)` at the end of a
//! green run to skip the engine's crashing teardown (see the module docs). A single test makes
//! that exit deterministic.

use std::time::Duration;

use dregg_sdk_net::ReceiptStream;

use dreggnet_tavern::{Patron, boot_tavern};

/// Pull the next receipt off a live stream, bounded so a stuck stream fails the test instead
/// of hanging. Returns the receipt's firing identity (`agent`) + turn hash hex.
async fn next_receipt_within(
    stream: &mut ReceiptStream,
    within: Duration,
) -> Option<(dregg_types::CellId, String)> {
    let r = tokio::time::timeout(within, stream.next()).await.ok()??;
    Some((r.agent, dregg_types::hex_encode(&r.turn_hash)))
}

/// Drain a stream until a receipt attributed to `actor` arrives, bounded by `within`.
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
async fn n_patrons_co_inhabit_one_persistent_tavern() {
    // ── OPEN THE TAVERN ── boot ONE tavern hosting N=3 DISTINCT key-ceremony identities. ──
    let session = boot_tavern(&["tavern-alice", "tavern-bob", "tavern-cara"])
        .await
        .expect("boot the tavern");
    assert_eq!(session.patron_count(), 3, "the tavern hosts three patrons");

    let alice = Patron::seat(&session, 0);
    let bob = Patron::seat(&session, 1);
    let cara = Patron::seat(&session, 2);

    // The three identities are genuinely distinct cells on the one ledger.
    assert_ne!(alice.identity(), bob.identity());
    assert_ne!(bob.identity(), cara.identity());
    assert_ne!(alice.identity(), cara.identity());

    // All three discover the SAME tavern surface (one place, not three forks).
    let verbs = alice
        .discover(&session.server_cell_hex)
        .await
        .expect("Alice discovers the tavern");
    for verb in ["enter", "post", "list", "party_up", "poke_stall"] {
        assert!(
            verbs.iter().any(|v| v == verb),
            "the tavern advertises `{verb}`"
        );
    }

    // ── (0) UN-FAKEABLE PRESENCE (the negative, NON-VACUOUS) ──────────────────────────
    // Nobody is present yet. Bob tries to flip ALICE'S seat (index 0) — he signs AS Bob and
    // holds no cap over seat 0, so the executor REFUSES it, and Alice's seat stays empty.
    // You cannot fake being online as someone else.
    for i in 0..3 {
        assert!(
            !alice.present(i).await.expect("seat pre"),
            "seat {i} empty before anyone enters"
        );
    }
    let forged = bob.poke_seat(0).await.expect("Bob forges Alice's presence");
    assert!(
        !forged.accepted,
        "Bob CANNOT flip Alice's seat (no cap); outcome={forged:?}"
    );
    assert!(
        !bob.present(0).await.expect("seat 0 after forge"),
        "Alice's seat STILL empty — presence un-fakeable"
    );

    // ── (1) PRESENCE ── each identity ENTERS its OWN seat; each flag flips, attributed. ──
    assert!(
        alice.enter().await.expect("Alice enters").accepted,
        "Alice's enter commits"
    );
    assert!(
        bob.enter().await.expect("Bob enters").accepted,
        "Bob's enter commits"
    );
    assert!(
        cara.enter().await.expect("Cara enters").accepted,
        "Cara's enter commits"
    );
    // ANY patron reads the SAME shared presence state — all three seats are present.
    for i in 0..3 {
        assert!(
            cara.present(i).await.expect("present post"),
            "patron {i} is present in the tavern"
        );
    }

    // ── (2) THE LFG BOARD ── each post a real attributed turn on the ONE shared board. ──
    // Bob subscribes to ALICE'S live turns BEFORE she posts (the live-sync setup).
    let mut bob_feed = bob.subscribe_to_identity(alice.identity());
    tokio::time::sleep(Duration::from_millis(400)).await;

    let alice_post = alice.post(11).await.expect("Alice posts LFG");
    assert!(
        alice_post.accepted,
        "Alice's board post commits; error={:?}",
        alice_post.error
    );

    // ── (3) LIVE SYNC ── Bob observes Alice's post live, then re-reads the shared board. ──
    let observed = await_receipt_from(&mut bob_feed, alice.identity(), Duration::from_secs(10))
        .await
        .expect("Bob's live stream delivers Alice's post receipt");
    assert_eq!(
        Some(&observed),
        alice_post.turn_hash.as_ref(),
        "the receipt Bob observed live IS Alice's committed post (same turn hash)"
    );
    assert_eq!(
        bob.board_last_from(0).await.expect("lane 0"),
        11,
        "Bob sees Alice's value (world updated for the watcher)"
    );
    assert_eq!(
        bob.board_count().await.expect("count"),
        1,
        "the shared post count advanced for both"
    );

    // Cara posts too; the one shared board carries every patron's contribution in its lane.
    assert!(
        cara.post(33).await.expect("Cara posts").accepted,
        "Cara's post commits"
    );
    assert_eq!(
        alice.board_last_from(2).await.expect("lane 2"),
        33,
        "Alice sees Cara's value on the shared board"
    );
    assert_eq!(
        alice.board_count().await.expect("count2"),
        2,
        "two co-acts landed on the one board"
    );

    // ── (4) THE PARTY-UP HOOK ── patrons form a party; the roster carries each joiner. ──
    assert_eq!(
        alice.party_size().await.expect("party pre"),
        0,
        "no party formed yet"
    );
    assert!(
        alice.party_up(7).await.expect("Alice party_up").accepted,
        "Alice joins the party"
    );
    assert!(
        bob.party_up(8).await.expect("Bob party_up").accepted,
        "Bob joins the party"
    );
    assert_eq!(
        cara.party_size().await.expect("party size"),
        2,
        "a party of two has formed on the roster"
    );
    assert_eq!(
        cara.party_member(0).await.expect("member 0"),
        7,
        "Alice's attributed party marker"
    );
    assert_eq!(
        cara.party_member(1).await.expect("member 1"),
        8,
        "Bob's attributed party marker"
    );
    assert_eq!(
        cara.party_member(2).await.expect("member 2"),
        0,
        "Cara has not joined"
    );

    // ── (5) MARKET STALL + THE OVER-REACH (non-vacuous) ──────────────────────────────
    // Alice lists on her OWN stall (index 0) — she holds the cap, so it commits.
    assert!(
        !bob.stall_listed(0).await.expect("stall pre"),
        "Alice's stall starts empty"
    );
    let alice_list = alice.list(500).await.expect("Alice lists");
    assert!(
        alice_list.accepted,
        "Alice's own-stall listing commits; error={:?}",
        alice_list.error
    );
    assert!(
        cara.stall_listed(0).await.expect("stall listed"),
        "Alice's stall now carries a listing"
    );
    assert_eq!(
        cara.stall_price(0).await.expect("stall price"),
        500,
        "the listed price is on the shared ledger"
    );

    // THE OVER-REACH: Bob pokes ALICE'S stall (index 0). Bob holds NO cap over it — REFUSED.
    let bob_reach = bob
        .poke_stall(0, 999)
        .await
        .expect("Bob attempts the over-reach");
    assert!(
        !bob_reach.accepted,
        "Bob CANNOT write Alice's private stall (no cap); outcome={bob_reach:?}"
    );
    // The refused over-reach left Alice's stall UNCHANGED (still her price, non-vacuous).
    assert_eq!(
        cara.stall_price(0).await.expect("stall after refusal"),
        500,
        "the refused poke left Alice's stall untouched"
    );

    // …while ALICE, who owns the stall, pokes it successfully — proving the refusal was
    // AUTHORITY, not a broken affordance (the non-vacuity control).
    let alice_poke = alice
        .poke_stall(0, 777)
        .await
        .expect("Alice pokes her own stall");
    assert!(
        alice_poke.accepted,
        "Alice (capped) writes her own stall; error={:?}",
        alice_poke.error
    );
    assert_eq!(
        cara.stall_price(0).await.expect("stall after owner"),
        777,
        "the owner's authorized poke landed"
    );

    // The whole suite is green. Exit the process cleanly WITHOUT the deos-host SpiderMonkey
    // runtime's crashing global teardown (a `pthread_mutex_destroy` SIGSEGV on the never-
    // dropped engine — unrelated to correctness; see the module docs). `_exit(0)` skips the
    // C++ static destructors so a passing run reports success.
    use std::io::Write;
    println!("TAVERN_E2E_ALL_ASSERTIONS_PASSED — exiting cleanly (skipping deos-host teardown)");
    std::io::stdout().flush().ok();
    unsafe {
        libc::_exit(0);
    }
}
