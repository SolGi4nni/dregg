//! DRIVE the dungeon on the real dregg executor and PRINT the proof:
//!   * the installed gate is a real `StateConstraint::FieldGte` tooth;
//!   * a legal playthrough lands real `TurnReceipt`s whose hashes chain (pre==prev.post);
//!   * an illegal descent (no lantern) is a REAL executor refusal — reason printed
//!     verbatim — that commits nothing.
//!
//! Run:  cargo run -p dungeon-on-dregg --example descend

use dungeon_on_dregg::{
    CH_CLAIM, CH_DESCEND, CH_LEAVE_LANTERN, CH_TAKE_LANTERN, ROOM_ANTECHAMBER, ROOM_SHORE,
    compiled, deploy, descend_gate_constraints, scene,
};
use spween_dregg::{Driver, verify, verify_chain_linkage};

fn hx(b: &[u8; 32]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect::<String>()
}

fn main() {
    let s = scene();

    println!("=== THE SALT SHORE DESCENT — a dungeon on the REAL dregg executor ===\n");

    // ── 0. The gate is a real executor-enforced CellProgram tooth ───────────────
    let story = compiled();
    println!("world-cell slot layout (dungeon state on real cell fields):");
    println!("  passage(room) -> slot 0");
    for (name, slot) in &story.var_slots {
        println!("  {name:<12} -> slot {slot}");
    }
    println!("\ninstalled gate on the `antechamber -> dark_stair` descent (kernel teeth):");
    for c in descend_gate_constraints(&story) {
        println!("  {c:?}");
    }
    println!("  ^ the executor re-checks THIS on the descend move's post-state.\n");

    // ── 1. Legal playthrough over the stock runtime: a real receipt chain ───────
    println!("--- LEGAL PLAYTHROUGH (take lantern -> descend -> claim) ---");
    let mut driver = Driver::start(deploy(5), &s).expect("start");
    let genesis = driver.genesis().expect("genesis receipt").clone();
    println!(
        "genesis     turn={}  pre={}  post={}",
        &hx(&genesis.turn_hash)[..16],
        &hx(&genesis.pre_state_hash)[..16],
        &hx(&genesis.post_state_hash)[..16],
    );

    for (label, ch) in [
        ("take-lantern", CH_TAKE_LANTERN),
        ("descend     ", CH_DESCEND),
        ("claim-hoard ", CH_CLAIM),
    ] {
        let step = driver.advance(ch).expect("legal move commits");
        let r = &step.receipt;
        println!(
            "{label} turn={}  pre={}  post={}   (in `{}`)",
            &hx(&r.turn_hash)[..16],
            &hx(&r.pre_state_hash)[..16],
            &hx(&r.post_state_hash)[..16],
            step.passage,
        );
    }
    assert!(driver.is_ended());
    println!(
        "final gold in the cell: {}",
        driver.world().read_var("gold")
    );

    let play = driver.playthrough();
    verify_chain_linkage(&play).expect("chain links");
    verify(deploy(5), &s, &play).expect("replay-verifies");
    println!(
        "\nreceipt chain ({} receipts) links cleanly AND re-verifies by replay: OK",
        play.receipts().len()
    );
    // Show the un-retconnable link explicitly.
    let rs = play.receipts();
    for i in 1..rs.len() {
        assert_eq!(rs[i].pre_state_hash, rs[i - 1].post_state_hash);
    }
    println!("every receipt: pre_state_hash == previous.post_state_hash  (verified)\n");

    // ── 2. Illegal descent: a REAL executor refusal, nothing commits ────────────
    println!("--- ILLEGAL MOVE (descend the dark stair with NO lantern) ---");
    let world = deploy(3);
    let leave = dungeon_on_dregg::choice_at(&s, ROOM_SHORE, CH_LEAVE_LANTERN);
    world
        .apply_choice(ROOM_SHORE, CH_LEAVE_LANTERN, &leave)
        .expect("stepping north empty-handed is ungated");
    println!(
        "walked to the antechamber empty-handed (has_lantern={}, room slot={:?})",
        world.read_var("has_lantern"),
        world.read_passage()
    );

    let descend = dungeon_on_dregg::choice_at(&s, ROOM_ANTECHAMBER, CH_DESCEND);
    match world.apply_choice(ROOM_ANTECHAMBER, CH_DESCEND, &descend) {
        Ok(r) => panic!(
            "BUG: unlit descent committed a receipt {}",
            hx(&r.turn_hash)
        ),
        Err(e) => println!("executor REFUSED the descent, verbatim:\n  {e}"),
    }
    // Anti-ghost: the refused turn wrote nothing.
    assert_eq!(world.read_passage(), Some(1), "still in the antechamber");
    assert_eq!(world.read_var("depth"), 0);
    assert_eq!(world.read_var("has_lantern"), 0);
    println!("anti-ghost: still in the antechamber, depth=0, no lantern — NOTHING committed.");

    println!("\n=== all teeth held: real receipts, real gate, real refusal ===");
}
