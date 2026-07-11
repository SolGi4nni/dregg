//! DRIVE the COLLECTIVE on the REAL substrate and PRINT the proof:
//!   * each seat is bound to a REAL ed25519 CUSTODY keypair (the same classical signature
//!     the executor authorizes turns with); a ballot is authenticated by that signature,
//!     not by a name — a correctly-signed ballot is admitted, a FORGED/wrong-key signature
//!     is REJECTED (`BadSignature`, nothing commits);
//!   * a crowd's signed ballots are real cap-bounded turns on the real `collective_choice`
//!     engine (WriteOnce ballots + Monotonic tally + the polis `AffineLe` quorum gate);
//!   * the quorum-certified winner FIRES a real `WorldCell` turn on the game executor —
//!     the crowd decides, the world resolves the decided `Command` (receipt printed);
//!   * a sub-quorum round does NOT move the world (no world turn);
//!   * a quorum-certified but ILLEGAL command (descend an unlit stair) is a REAL game-
//!     executor refusal — the crowd cannot vote past the `CellProgram` gate.
//!
//! Run:  cargo run -p dungeon-on-dregg --example collective

use dungeon_on_dregg::collective::{
    CollectiveRound, Custodian, Proposal, QUORUM, SignedBallot, demo_custodians,
};
use dungeon_on_dregg::narrator::Command;
use dungeon_on_dregg::{
    CH_DESCEND, CH_LEAVE_LANTERN, KP_PRESS_ON, KP_TRADE_BLOWS, ROOM_ANTECHAMBER, ROOM_SHORE,
    choice_at, deploy, deploy_keep, keep_scene, scene as salt_scene,
};
use spween_dregg::Value;

fn hx8(b: &[u8]) -> String {
    b.iter().take(8).map(|x| format!("{x:02x}")).collect()
}

fn main() {
    println!(
        "=== THE COLLECTIVE — seats hold REAL custody keys; a SIGNED ballot fires a WorldCell turn ===\n"
    );

    // Each seat is bound to a real ed25519 custody keypair (the demo keyring derives the
    // secret deterministically from the name so this run is reproducible; a production seat
    // generates its own). The PUBLIC key is the seat's electorate identity.
    let custodians = demo_custodians();
    println!("roster (5 seats, REAL ed25519 custody keys); quorum M = {QUORUM} (majority):");
    for c in &custodians {
        println!(
            "  {:<9} custody pk (ed25519) = {}…",
            c.name(),
            hx8(c.public_key().as_bytes())
        );
    }
    println!("  (a ballot is authenticated by the seat's SIGNATURE over its pk — not by a name)\n");

    let seat = |name: &str| Custodian::demo(name);

    // ── LEGAL: a quorum-certified vote of SIGNED ballots fires a real world turn ─────────
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

    // Each seat SIGNS its ballot with its custody key; the round admits it only if the
    // signature verifies against the registered public key.
    let poll = round.poll();
    let ballots = [
        ("Bramwen", KP_TRADE_BLOWS),
        ("Corvin", KP_TRADE_BLOWS),
        ("Della", KP_PRESS_ON),
        ("Ferro", KP_TRADE_BLOWS),
    ];
    for (name, opt) in ballots {
        let signed = seat(name).sign_ballot(poll, opt);
        let r = round
            .cast(&signed)
            .unwrap_or_else(|e| panic!("{name} votes: {e}"));
        println!(
            "  BALLOT {name:<9} -> option {opt}   sig={}…  (real turn={}…)",
            hx8(&signed.signature.0),
            hx8(&r.turn_hash)
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
        hx8(&cert.receipt.turn_hash),
        hx8(&cert.receipt.pre_state_hash),
        hx8(&cert.receipt.post_state_hash)
    );
    println!(
        "  the world resolved trade-blows: hp is now {} (50 -> 30, a real state transition)\n",
        world.read_var("hp")
    );

    // ── FORGED: a wrong signature is REJECTED (identity is a signature, not a name) ──────
    println!("--- IDENTITY TOOTH — a FORGED ballot for a seated seat is rejected ---");
    let mut round_forge = CollectiveRound::open(
        "The gate-warden bars the way — what does the party do?",
        vec![
            Proposal::new("Trade blows with the gate-warden", Command::trade_blows()),
            Proposal::new("Press past into the plundered hall", Command::press_on()),
        ],
    )
    .expect("round opens");
    let bramwen_pk = seat("Bramwen").public_key();
    // (1) A garbage signature stamped with Bramwen's real public key.
    let forged = SignedBallot {
        voter_pk: bramwen_pk,
        option: KP_TRADE_BLOWS,
        signature: dregg_types::Signature([0x7u8; 64]),
    };
    println!(
        "  forged ballot: claims Bramwen's pk {}…, garbage sig {}…",
        hx8(bramwen_pk.as_bytes()),
        hx8(&forged.signature.0)
    );
    match round_forge.cast(&forged) {
        Err(e) => println!("  REJECTED: {e}"),
        Ok(_) => println!("  !! a forged ballot was admitted (BUG)"),
    }
    // (2) An IMPOSTOR: Mallory produces a GENUINE ed25519 signature — by the WRONG key —
    // and stamps Bramwen's public key on it. It does not verify against Bramwen's key.
    let mallory = Custodian::generate("Mallory");
    let impostor = SignedBallot {
        voter_pk: bramwen_pk,
        option: KP_TRADE_BLOWS,
        signature: mallory.sign_raw(bramwen_pk.as_bytes()),
    };
    match round_forge.cast(&impostor) {
        Err(e) => println!("  IMPOSTOR (Mallory signs as Bramwen) REJECTED: {e}"),
        Ok(_) => println!("  !! an impostor ballot was admitted (BUG)"),
    }
    println!(
        "  anti-ghost: tally total still {} — no forged/impostor ballot moved the board\n",
        round_forge.tally().expect("tally").total
    );

    // ── SUB-QUORUM: the world does not move ─────────────────────────────────────────────
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
    let poll2 = round2.poll();
    round2
        .cast(&seat("Bramwen").sign_ballot(poll2, KP_TRADE_BLOWS))
        .expect("Bramwen votes");
    round2
        .cast(&seat("Corvin").sign_ballot(poll2, KP_TRADE_BLOWS))
        .expect("Corvin votes");
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

    // ── ILLEGAL: quorum-certified but the executor refuses ──────────────────────────────
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
    let poll3 = round3.poll();
    for name in ["Bramwen", "Corvin", "Della"] {
        round3
            .cast(&seat(name).sign_ballot(poll3, 0))
            .unwrap_or_else(|e| panic!("{name} votes: {e}"));
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

    println!("=== seats hold REAL custody keys: a ballot is authenticated by a SIGNATURE, ===");
    println!("=== not a name (forged/impostor rejected). The crowd DECIDES (real quorum-  ===");
    println!("=== certified vote of signed ballots); the world RESOLVES the decided Command ===");
    println!("=== on the real executor. Sub-quorum doesn't move the world; a voted-for     ===");
    println!("=== illegal Command is a real executor refusal. Vote is not power.           ===");
}
