//! The UGC flywheel, end to end:
//!
//! ```text
//! cargo run -p ugc-dregg --example leaderboard
//! ```
//!
//! Publish a universe, submit a REAL win (accepted + ranked) and a CHEAT (rejected on
//! replay), then print the verifiable leaderboard — every entry independently
//! re-verifiable. A daily procgen universe (content-addressed by a committed seed)
//! is published and won too.

use dungeon_on_dregg::{
    CH_CLAIM, CH_DESCEND, CH_LEAVE_LANTERN, CH_RETREAT, CH_TAKE_LANTERN, DUNGEON,
};
use ugc_dregg::{Completion, Provenance, Registry, Universe, WinCondition, record_playthrough};

fn main() {
    println!("═══════════════════════════════════════════════════════════════════");
    println!(" ugc-dregg · a UGC registry + a NO-CHEAT verifiable leaderboard");
    println!("═══════════════════════════════════════════════════════════════════\n");

    let mut reg = Registry::new();

    // ── PUBLISH an authored universe (the real salt-shore dungeon) ─────────────────
    let salt_shore = Universe::authored(
        "The Salt Shore Descent",
        "attested-dm-salvage",
        DUNGEON,
        WinCondition::ended_with(&[("gold", 500)]),
    )
    .expect("the salt-shore dungeon is a valid, deployable universe");
    let shore_id = reg.publish(salt_shore.clone());
    println!("── PUBLISH ──");
    println!("  authored universe: {}", salt_shore.name());
    println!("    author:   {}", salt_shore.author());
    println!("    id:       {shore_id}   (content-addressed — same world, same id)");
    println!("    win:      scene ENDED and gold == 500 (the hoard seized)\n");

    // ── SUBMIT a REAL winning playthrough (accepted + ranked) ──────────────────────
    println!("── SUBMIT completions (each re-verified by replay before it ranks) ──\n");

    let ada = record_playthrough(&salt_shore, &[CH_TAKE_LANTERN, CH_DESCEND, CH_CLAIM])
        .expect("ada's honest win drives cleanly");
    match reg.submit(Completion {
        universe: shore_id,
        player: "ada".into(),
        play: ada,
        claimed_turns: 3,
    }) {
        Ok(a) => println!(
            "  ✓ ada (3 moves): ACCEPTED — re-executed to the win, ranked #{}",
            a.rank
        ),
        Err(e) => println!("  ✗ ada: rejected — {e}"),
    }

    // A second real win, slower (a detour): take, retreat, take again, descend, claim.
    let bran = record_playthrough(
        &salt_shore,
        &[
            CH_TAKE_LANTERN,
            CH_RETREAT,
            CH_TAKE_LANTERN,
            CH_DESCEND,
            CH_CLAIM,
        ],
    )
    .expect("bran's slower but real win");
    match reg.submit(Completion {
        universe: shore_id,
        player: "bran".into(),
        play: bran,
        claimed_turns: 5,
    }) {
        Ok(a) => println!(
            "  ✓ bran (5 moves): ACCEPTED — a real win with a detour, ranked #{}",
            a.rank
        ),
        Err(e) => println!("  ✗ bran: rejected — {e}"),
    }

    // ── SUBMIT a CHEAT (edited moves that never reach the win) — REJECTED ───────────
    let mut forged = record_playthrough(&salt_shore, &[CH_TAKE_LANTERN, CH_DESCEND, CH_CLAIM])
        .expect("record an honest win to forge");
    forged.steps[0].choice_index = CH_LEAVE_LANTERN; // retcon: never took the lantern
    match reg.submit(Completion {
        universe: shore_id,
        player: "mallory".into(),
        play: forged,
        claimed_turns: 3,
    }) {
        Ok(a) => println!(
            "  ?! mallory: ACCEPTED (should not happen) rank #{}",
            a.rank
        ),
        Err(e) => println!("  ✗ mallory (forged moves): REJECTED — {e}"),
    }

    // ── A tampered RESULT on an otherwise-honest win — REJECTED ────────────────────
    let honest = record_playthrough(&salt_shore, &[CH_TAKE_LANTERN, CH_DESCEND, CH_CLAIM])
        .expect("honest win");
    match reg.submit(Completion {
        universe: shore_id,
        player: "liar".into(),
        play: honest,
        claimed_turns: 1, // lies: really 3
    }) {
        Ok(a) => println!("  ?! liar: ACCEPTED (should not happen) rank #{}", a.rank),
        Err(e) => println!("  ✗ liar (tampered result): REJECTED — {e}"),
    }

    // ── The verifiable leaderboard ─────────────────────────────────────────────────
    print_board(&reg, shore_id, &salt_shore.name());

    // ── A DAILY procgen universe — content-addressed by a committed seed ───────────
    println!("\n── A DAILY universe (procgen, content-addressed by a committed seed) ──\n");
    let epoch = [0x5eu8; 32]; // a day's committed epoch value (a beacon output)
    let daily = Universe::daily("procgen-daily", &epoch).expect("the daily universe publishes");
    let daily_id = reg.publish(daily.clone());
    if let Provenance::Procgen { committed_seed } = daily.provenance() {
        let seed_hex: String = committed_seed[..8]
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        println!("  {}", daily.name());
        println!("    id:            {daily_id}");
        println!(
            "    committed seed: {seed_hex}…  → regenerates byte-for-byte: {}",
            daily.regenerates_from_seed()
        );
    }
    let rooms = daily.source().matches("=== room").count();
    let moves = vec![0usize; rooms]; // one winning move per room (take-key, onward…, descend, seize)
    let play = record_playthrough(&daily, &moves).expect("the generated dungeon is winnable");
    match reg.submit(Completion {
        universe: daily_id,
        player: "explorer".into(),
        play,
        claimed_turns: moves.len(),
    }) {
        Ok(a) => println!(
            "    ✓ explorer ({} moves): ACCEPTED — won the generated dungeon, ranked #{}",
            moves.len(),
            a.rank
        ),
        Err(e) => println!("    ✗ explorer: rejected — {e}"),
    }
    print_board(&reg, daily_id, &daily.name());

    // ── Honest scope ───────────────────────────────────────────────────────────────
    println!("\n── Honest scope ──");
    println!("  • verification is O(N) REPLAY — a re-verifier re-executes every move.");
    println!("    The succinct light client (sub-linear win-verification) is a separate,");
    println!("    Lane-D-blocked workstream and is NOT claimed here.");
    println!("  • author identity is a NAME, not yet a verified signing key (signatures");
    println!("    are a named follow-up); the registry is in-memory (no persistence);");
    println!("    nothing rate-limits or stakes a submission (anti-sybil is future work).");
    println!("  • the no-cheat property — a ranked completion PROVABLY reaches the win —");
    println!("    holds regardless: every entry above re-executes to a real win state.");
}

fn print_board(reg: &Registry, id: ugc_dregg::UniverseId, name: &str) {
    println!("\n── LEADERBOARD · {name} (every entry independently re-verifiable) ──\n");
    let board = reg.leaderboard(id);
    if board.is_empty() {
        println!("    (no accepted completions)");
        return;
    }
    for (i, e) in board.iter().enumerate() {
        // Independently re-verify each entry right here (the stranger's re-execution).
        let ok = reg.reverify_entry(id, &e.completion_id).is_ok();
        let cid: String = e.completion_id[..6]
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect();
        println!(
            "    #{rank}  {player:<10} {turns} turns   [completion {cid}…]  re-verify: {verdict}",
            rank = i + 1,
            player = e.player,
            turns = e.turns,
            verdict = if ok { "PASS ✓" } else { "FAIL ✗" },
        );
    }
}
