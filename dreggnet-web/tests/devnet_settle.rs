//! # `devnet_settle` — DRIVE the Descent adventure against a REAL running dregg node.
//!
//! The non-vacuous proof that `dreggnet-web` runs the games AGAINST A DEVNET: a Descent run
//! submitted through the web surface's verify-gate is SETTLED onto a running node's ledger via
//! [`NodeTarget::Federation`] — a real committed turn on-chain (an `EmitEvent`-of-commitment the
//! node signs as operator + finalizes on `GET /api/receipts`), not just in-process.
//!
//! * The [`local_mode_settle_is_an_in_process_noop`] test always runs (no node needed): it proves
//!   the DEFAULT ([`NodeTarget::Local`]) settle is a no-op (`Ok(None)`) — the committed suite +
//!   the node-free demo are unaffected. This is the non-vacuity anchor: the SAME run in Local mode
//!   stays in-process.
//! * The [`federation_settle_lands_a_turn_on_a_running_node`] test is DEVNET-GATED and therefore
//!   `#[ignore]`d. It opens the demo day, submits the demo WINNING run through the verify-gate,
//!   settles it, and asserts the node accepted + FINALIZED the turn — `NodeTarget::route` returns
//!   `Ok(Some(Landed))` only after confirming the turn hash is on the node's `GET /api/receipts`
//!   log.
//!
//! ⚑ WHY `#[ignore]` AND NOT AN EARLY RETURN. Both gated tests below used to open with
//! `let Ok(..) = std::env::var(..) else { return };` — which reports `ok` in a run where they did
//! nothing at all. A default run therefore counted two greens for a devnet drive and a bootstrap
//! print that had not happened. `#[ignore]` is the honest encoding of the same gate: the harness
//! prints a line naming what was skipped and why, the count of passing tests stops including them,
//! and running them deliberately with the env var absent now FAILS instead of quietly passing.

use dregg_node_target::NodeTarget;
use dreggnet_web::demo_win_for_seed;
use dreggnet_web::descent::DescentState;
use procgen_dregg::daily_seed;

/// DEVNET BOOTSTRAP HELPER (env-gated): print the node operator's own agent cell id, derived from
/// its cipherclerk pubkey exactly as `node/src/api.rs` does (`CellId::derive_raw(pubkey,
/// blake3("default"))`). A fresh node's operator cell is not materialized until it receives value,
/// so the games' anchor (an operator `EmitEvent`) is refused ("cell not found") until this cell is
/// faucet-materialized once — the one-time devnet bring-up step. Run with `DREGG_OP_PUBKEY=<hex>`.
#[test]
#[ignore = "devnet bring-up helper, not a gate: prints the operator cell id. \
            DREGG_OP_PUBKEY=<hex> cargo test -p dreggnet-web --test devnet_settle -- --ignored \
            print_operator_cell_id --nocapture"]
fn print_operator_cell_id() {
    let pk_hex = std::env::var("DREGG_OP_PUBKEY")
        .expect("DREGG_OP_PUBKEY=<hex> — this helper is #[ignore]d precisely because it needs it");
    let pk: Vec<u8> = (0..pk_hex.len() / 2)
        .map(|i| u8::from_str_radix(&pk_hex[2 * i..2 * i + 2], 16).unwrap())
        .collect();
    let token = blake3::hash(b"default");
    let mut buf = Vec::with_capacity(64);
    buf.extend_from_slice(&pk);
    buf.extend_from_slice(token.as_bytes());
    let id = blake3::derive_key("dregg-cell-id-v1", &buf);
    let hex: String = id.iter().map(|b| format!("{b:02x}")).collect();
    println!("operator_cell_id={hex}");
}

/// The demo day's seed (the same fixed seed [`dreggnet_web::build_demo_descent`] uses — a warden-HP-45
/// day whose winning line replays clean).
fn demo_seed() -> procgen_dregg::CommittedSeed {
    daily_seed(&[3; 32])
}

/// LOCAL (default) settle is an in-process no-op — the run ranks in-process, nothing leaves the
/// process. This is the non-vacuity control: the exact same run + settle in Federation mode lands
/// a turn on the node (the gated test below), while here it stays in-process (`Ok(None)`).
#[test]
fn local_mode_settle_is_an_in_process_noop() {
    let seed = demo_seed();
    let (moves, level, class) = demo_win_for_seed(seed);
    let state = DescentState::new(); // NodeTarget::Local by default
    assert!(!state.settles_to_a_node(), "Local is the default");
    state.open_day("today", seed);
    let run_id = "local-demo";
    let turns = state
        .submit_run("today", run_id, "ember", level, class, &moves)
        .expect("the demo winning run re-executes to the hoard + no-cheat-verifies");
    assert!(turns >= 1);
    // Local settle: a no-op — nothing submitted anywhere.
    let landed = state
        .settle_run("today", run_id)
        .expect("Local settle never errors");
    assert!(
        landed.is_none(),
        "Local mode keeps the run in-process — no node turn"
    );
}

/// DEVNET-DRIVEN: a submitted Descent run is anchored on the running node's ledger. Needs a node
/// at `DREGG_NODE_URL`, so the committed suite reports it as ignored rather than as a pass.
#[test]
#[ignore = "needs a running dregg node: DREGG_NODE_URL=<url> cargo test -p dreggnet-web \
            --test devnet_settle -- --ignored federation_settle --nocapture"]
fn federation_settle_lands_a_turn_on_a_running_node() {
    let url = std::env::var("DREGG_NODE_URL")
        .expect("DREGG_NODE_URL — this test is #[ignore]d precisely because it needs a live node");
    assert!(
        !url.trim().is_empty(),
        "DREGG_NODE_URL is set but empty — name a running node"
    );

    // Build a Federation target from the env (the real HTTP transport at DREGG_NODE_URL).
    let target = NodeTarget::from_env().expect("DREGG_NODE_URL builds a Federation target");
    assert!(target.is_federation(), "DREGG_NODE_URL → Federation");

    let seed = demo_seed();
    let (moves, level, class) = demo_win_for_seed(seed);
    let state = DescentState::new().with_node_target(target);
    assert!(state.settles_to_a_node());
    state.open_day("today", seed);

    // Submit the demo WINNING run through the verify-gate (re-executed to the hoard + no-cheat-verified).
    let run_id = "devnet-demo-win";
    let turns = state
        .submit_run("today", run_id, "ember", level, class, &moves)
        .expect("the demo winning run ranks");
    eprintln!("ranked in-process: {turns} verified turns");

    // SETTLE it: submit the run's winning turn to the node + confirm it LANDED on /api/receipts.
    // `route` returns Ok(Some) ONLY after the node accepted it AND it is present on the node's
    // finalized receipt log — so this IS the on-ledger proof (non-vacuous).
    let landed = state
        .settle_run("today", run_id)
        .expect("the run settles onto the running node")
        .expect("Federation mode returns the node's landed receipt (not a Local no-op)");
    let hash_hex: String = landed
        .node_turn_hash
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
    eprintln!("LANDED on the node's ledger: turn_hash={hash_hex}  (node={url})");

    // An UNFINISHED / losing run is refused by the verify-gate BEFORE it can rank — so it never
    // reaches settle, and the node is never touched for a non-win (fail-closed). A truncated move
    // sequence does not reach the hoard, so submit_run rejects it.
    let short: Vec<usize> = moves.iter().copied().take(1).collect();
    let refused = state.submit_run("today", "devnet-demo-lose", "ember", level, class, &short);
    assert!(
        refused.is_err(),
        "an unfinished run is refused by re-execution (never settles to the node)"
    );
}
