//! DRIVE the COLLECTIVE on the REAL substrate and PRINT the proof:
//!   * a crowd's ballots are real cap-bounded turns on the real `collective_choice`
//!     engine (WriteOnce ballots + Monotonic tally + the polis `AffineLe` quorum gate);
//!   * the quorum-certified winner FIRES a real `WorldCell` turn on the game executor —
//!     the crowd decides, the world resolves the decided `Command` (receipt printed);
//!   * a sub-quorum round does NOT move the world (no world turn);
//!   * a quorum-certified but ILLEGAL command (descend an unlit stair) is a REAL game-
//!     executor refusal — the crowd cannot vote past the `CellProgram` gate.
//!
//! Run:  cargo run -p dungeon-on-dregg --example collective

use dungeon_on_dregg::collective::{CollectiveRound, Proposal, QUORUM, ROSTER, seat_pk};
use dungeon_on_dregg::narrator::Command;
use dungeon_on_dregg::{
    CH_DESCEND, CH_LEAVE_LANTERN, KP_PRESS_ON, KP_TRADE_BLOWS, ROOM_ANTECHAMBER, ROOM_SHORE,
    choice_at, deploy, deploy_keep, keep_scene, scene as salt_scene,
};
use spween_dregg::Value;

fn hx(b: &[u8; 32]) -> String {
    b.iter()
        .take(8)
        .map(|x| format!("{x:02x}"))
        .collect::<String>()
}

fn main() {
    println!(
        "=== THE COLLECTIVE — a crowd's quorum-certified vote fires a REAL WorldCell turn ===\n"
    );
    println!("roster (5 seats, demo identities blake3(name)); quorum M = {QUORUM} (majority):");
    for name in ROSTER {
        println!("  {name:<9} pk=blake3(name)={}…", hx(&seat_pk(name)));
    }
    println!("  (identity is DEMO-grade; the custody-key binding is the named production gap)\n");

    // ── LEGAL: a quorum-certified vote fires a real world turn ──────────────────────
    println!("--- ROUND 1 — the gate-warden bars the way (crowd decides, world resolves) ---");
    let s = keep_scene();
    let mut world = deploy_keep(30);
    world.seed_var("hp", Value::Int(50)); // the fight begins at 50 HP.
    let mut round = CollectiveRound::open(
        "The gate-warden bars the way — what does the party do?",
        vec![
            Proposal::new("Trade blows with the gate-warden", Command::trade_blows()),
            Proposal::new("Press past into the plundered hall", Command::press_on()),
        ],
    )
    .expect("the round opens");
    println!("question: {}", round.question());
    for (i, p) in round.proposals().iter().enumerate() {
        println!("  option {i}: {}", p.label);
    }

    // The crowd casts real ballots (each a cap-bounded WriteOnce turn on the vote engine).
    let ballots = [
        ("Bramwen", KP_TRADE_BLOWS),
        ("Corvin", KP_TRADE_BLOWS),
        ("Della", KP_PRESS_ON),
        ("Ferro", KP_TRADE_BLOWS),
    ];
    for (seat, opt) in ballots {
        let r = round
            .cast(seat, opt)
            .unwrap_or_else(|e| panic!("{seat} votes: {e}"));
        println!(
            "  BALLOT {seat:<9} -> option {opt}   (real turn={}…)",
            hx(&r.turn_hash)
        );
    }
    let tally = round.tally().expect("tally");
    println!(
        "tally (monotone verified board): {:?}   total={}",
        tally.per_option, tally.total
    );
    println!(
        "light-client recompute agrees: {}",
        round.light_client_tally().expect("lc") == tally
    );

    // THE SEAM: the crowd decides (quorum cert), the world resolves the decided command.
    let cert = round
        .resolve_into_world(&world, &s)
        .expect("the quorum-certified winner fires a real world turn");
    println!("\nQUORUM CERTIFICATE (the AffineLe gate admitted the decision-turn):");
    println!(
        "  winner = option {} ({} votes) at quorum-met total {}",
        cert.decision.winner, cert.decision.winner_tally, cert.decision.total
    );
    println!("  certified command = {:?}", cert.command);
    println!("REAL WORLD RECEIPT (the game executor committed the decided command):");
    println!(
        "  turn={}…  pre={}…  post={}…",
        hx(&cert.receipt.turn_hash),
        hx(&cert.receipt.pre_state_hash),
        hx(&cert.receipt.post_state_hash)
    );
    println!(
        "  the world resolved trade-blows: hp is now {} (50 -> 30, a real state transition)\n",
        world.read_var("hp")
    );

    // ── SUB-QUORUM: the world does not move ─────────────────────────────────────────
    println!("--- ROUND 2 — sub-quorum: only 2 of 5 seats vote (below M={QUORUM}) ---");
    let mut world2 = deploy_keep(31);
    world2.seed_var("hp", Value::Int(50));
    let mut round2 = CollectiveRound::open(
        "The gate-warden bars the way — what does the party do?",
        vec![
            Proposal::new("Trade blows with the gate-warden", Command::trade_blows()),
            Proposal::new("Press past into the plundered hall", Command::press_on()),
        ],
    )
    .expect("round opens");
    round2
        .cast("Bramwen", KP_TRADE_BLOWS)
        .expect("Bramwen votes");
    round2.cast("Corvin", KP_TRADE_BLOWS).expect("Corvin votes");
    println!(
        "tally total = {} (below quorum)",
        round2.tally().expect("tally").total
    );
    match round2.resolve_into_world(&world2, &s) {
        Err(e) => println!("  resolve_into_world REFUSED: {e}"),
        Ok(_) => println!("  !! sub-quorum unexpectedly moved the world"),
    }
    println!(
        "  anti-ghost: hp still {} — the world did NOT move\n",
        world2.read_var("hp")
    );

    // ── ILLEGAL: quorum-certified but the executor refuses ──────────────────────────
    println!("--- ROUND 3 — the crowd votes to descend an UNLIT stair (illegal) ---");
    let ss = salt_scene();
    let world3 = deploy(32);
    let leave = choice_at(&ss, ROOM_SHORE, CH_LEAVE_LANTERN);
    world3
        .apply_choice(ROOM_SHORE, CH_LEAVE_LANTERN, &leave)
        .expect("step north empty-handed");
    println!("  the party is in the antechamber, UNLIT (has_lantern=0)");
    let mut round3 = CollectiveRound::open(
        "The dark stair drops away — do we descend, or retreat?",
        vec![
            Proposal::new(
                "Descend the dark stair",
                Command::at(ROOM_ANTECHAMBER, CH_DESCEND),
            ),
            Proposal::new("Retreat to the shore", Command::at(ROOM_ANTECHAMBER, 1)),
        ],
    )
    .expect("round opens");
    for seat in ["Bramwen", "Corvin", "Della"] {
        round3
            .cast(seat, 0)
            .unwrap_or_else(|e| panic!("{seat} votes: {e}"));
    }
    println!(
        "  tally: {:?} — the crowd reached quorum for DESCEND",
        round3.tally().expect("tally").per_option
    );
    let winner = round3.resolve().expect("resolve").expect("quorum reached");
    println!("  QUORUM-CERTIFIED command = {:?}", winner.command);
    match round3.resolve_into_world(&world3, &ss) {
        Err(e) => println!("  the GAME executor REFUSED the certified command: {e}"),
        Ok(_) => println!("  !! the vote pushed an unlit descent past the executor"),
    }
    println!(
        "  anti-ghost: still passage {:?}, depth {}, has_lantern {} — the vote is NOT power\n",
        world3.read_passage(),
        world3.read_var("depth"),
        world3.read_var("has_lantern")
    );

    println!("=== the crowd DECIDES (real quorum-certified vote); the world RESOLVES the ===");
    println!("=== decided Command on the real executor. Sub-quorum doesn't move the world; ===");
    println!("=== a voted-for illegal Command is a real executor refusal. Vote is not power. ===");
}
