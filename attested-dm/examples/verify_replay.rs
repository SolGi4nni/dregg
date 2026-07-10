//! THE RE-EXECUTION LIGHT CLIENT — replay the game, do not merely inspect hashes.
//!
//! Run: `cargo run -p attested-dm --example verify_replay`
//!
//! `GameSession::verify()` authenticates the recorded chain (untampered history). It does NOT
//! prove each recorded effect was the *rule-correct* resolution of its bound action — a hash-valid
//! chain can still carry an effect the resolver would never produce. `verify_replay()` closes that
//! gap: it reconstructs the genesis world, recovers each turn's bound typed action, re-runs the
//! SAME `resolve_action`, and checks the resolver's effect equals the one the entry recorded.
//!
//! This example plays a real winning dungeon (both tiers pass), then hand-forges ONE entry — a
//! `Move` that records handing the player a crown — and re-links the chain so integrity STILL
//! passes. Replay catches the forgery the chain-only check misses.
//!
//! Honest scope: this is the trust-minimized RE-EXECUTION layer (the verifier runs the real
//! resolver as an executable specification) — NOT a succinct/zk proof. Its assumption is "the
//! resolver is the rules," not "the prover is sound."

use attested_dm::{
    chain_receipt_id, genesis_prev, sunken_vault, verify_ledger_replay, GameSession, GameStatus,
    LedgerEntry, PlayResult, ReplayMismatch, WorldEffect,
};

/// Re-link a mutated ledger into an internally-consistent hash chain (recompute every seq / prev /
/// receipt) — what a forger who understands the chain does so `verify()` still passes.
fn relink(ledger: &mut [LedgerEntry]) {
    let mut prev = genesis_prev();
    for (i, e) in ledger.iter_mut().enumerate() {
        e.seq = i as u64;
        e.prev = prev;
        e.receipt = chain_receipt_id(
            e.seq,
            &e.prev,
            &e.narration,
            &e.effect,
            &e.prompt_binding,
            &e.game_binding,
            &e.attestation,
        );
        prev = e.receipt;
    }
}

const SOLVE: &[&str] = &[
    "go north",
    "take lantern",
    "go down",
    "go down",
    "take rusted_key",
    "go north",
    "use rusted_key on iron_door",
    "go east",
    "take sword",
    "go north",
    "attack warden",
    "go east",
    "take amulet",
    "go up",
];

fn main() {
    println!("== THE RE-EXECUTION LIGHT CLIENT (attested-dm) ==\n");

    let mut game = GameSession::open(sunken_vault());
    for cmd in SOLVE {
        match game.command("hero", cmd) {
            PlayResult::Landed { .. } => {}
            other => panic!("the winning script should land `{cmd}`, got {other:?}"),
        }
    }
    assert_eq!(game.status(), GameStatus::Won);
    let turns = game.world().ledger.len();

    // ── The honest playthrough: BOTH independent claims hold. ──
    let report = game.verify_report();
    match (&report.chain, &report.replay) {
        (Ok(()), Ok(())) => {
            println!("  honest winning playthrough of THE SUNKEN VAULT ({turns} turns):");
            println!(
                "    chain:  valid  (the recorded history is untampered — a valid hash chain)"
            );
            println!("    replay: valid  ({turns} turns, the resolver reproduced every effect)");
        }
        (c, r) => panic!("an honest playthrough must pass both tiers: chain={c:?} replay={r:?}"),
    }

    // ── The forged variant: a Move that records a GrantItem, re-linked so integrity passes. ──
    println!("\n  now forge ONE effect and re-link the chain (the AI tries to invent an outcome):");
    let map = game.map().clone();
    let config = game.dm().config().clone();
    let mut forged = game.world().clone();

    // Entry #2 is "go down" into the dark stair — honest effect AdvanceScene("dark_stair").
    const FORGED_SEQ: usize = 2;
    let honest_effect = forged.ledger[FORGED_SEQ].effect.clone();
    forged.ledger[FORGED_SEQ].effect = Some(WorldEffect::GrantItem("crown".into()));
    relink(&mut forged.ledger);
    println!(
        "    forged turn #{FORGED_SEQ}: recorded effect {:?}  ->  {:?}",
        honest_effect, forged.ledger[FORGED_SEQ].effect
    );

    // Integrity STILL passes — it recomputes the receipt over the recorded (forged) effect.
    let chain = forged.verify_ledger(&config);
    print!("    chain:  ");
    match &chain {
        Ok(()) => {
            println!("valid  (integrity accepts the re-linked forgery — the gap replay closes)")
        }
        Err(e) => println!("BROKEN — {e}"),
    }

    // Re-execution CATCHES it — the resolver yields AdvanceScene, not GrantItem.
    let replay = verify_ledger_replay(&map, &forged.ledger);
    print!("    replay: ");
    match &replay {
        Ok(()) => println!("valid  (unexpected!)"),
        Err(ReplayMismatch::Effect {
            seq,
            action,
            expected,
            recorded,
        }) => println!(
            "CAUGHT at turn #{seq} [{}]: resolver yields {expected:?} but the entry recorded \
             {recorded:?}",
            action.label()
        ),
        Err(other) => println!("CAUGHT: {other}"),
    }

    assert!(chain.is_ok(), "integrity accepts the re-linked chain");
    assert!(replay.is_err(), "replay rejects the forged effect");

    println!(
        "\n  the AI may invent the story, but it cannot invent the outcome:\n  \
         a chain-only check passed the forgery; re-execution rejected it."
    );
}
