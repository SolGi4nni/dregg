//! DRIVE the MULTI-CELL world on the REAL executor and PRINT the proof:
//!   * a universe as a GRAPH of real cells — room A (shore), the item (lantern) on its
//!     OWN cell, room B (the gated stair) — each a distinct real cell in one ledger;
//!   * a REAL CROSS-CELL gate: room B's `ObservedFieldEquals` reads the lantern's
//!     finalized owner slot on ANOTHER cell, admitted by the executor's
//!     `FinalizedRootAuthority` (built from the committed ledger) + a Merkle-open
//!     witness — NOT a host `if`;
//!   * the gate REFUSES room B's action until the lantern is taken on its own cell
//!     (a real executor refusal across cells, fail-closed);
//!   * after a real `take` turn on the lantern + the finalized-root witness, room B's
//!     gated action COMMITS (a real cross-cell turn, receipt printed);
//!   * a FORGED open (stripped witness / divergent value) is refused (fail-closed);
//!   * the item's own `WriteOnce` refuses a rival's conflicting claim (first-grabber).
//!
//! Run:  cargo run -p dungeon-on-dregg --example multicell

use dungeon_on_dregg::multicell::{DOOR_SLOT, OWNER_SLOT, World};

fn hx(b: &[u8; 32]) -> String {
    b.iter()
        .take(10)
        .map(|x| format!("{x:02x}"))
        .collect::<String>()
}

fn slot(v: Option<[u8; 32]>) -> String {
    match v {
        Some(f) if f == [0u8; 32] => "· (empty)".to_string(),
        Some(f) => format!("{}…", hx(&f)),
        None => "<absent>".to_string(),
    }
}

fn main() {
    println!("=== THE MULTI-CELL WORLD — a real CROSS-CELL gate on the real executor ===\n");

    let world = World::deploy();
    println!("the universe is a GRAPH of real cells (one shared executor ledger):");
    println!(
        "  driver (player) cell : {}…",
        hx(world.driver().as_bytes())
    );
    println!(
        "  room A  — shore      : {}…  (where the lantern lies)",
        hx(world.shore().as_bytes())
    );
    println!(
        "  item    — lantern    : {}…  (its OWN cell; OWNER slot is WriteOnce)",
        hx(world.lantern().as_bytes())
    );
    println!(
        "  room B  — stair      : {}…  (GATED on the lantern via ObservedFieldEquals)",
        hx(world.stair().as_bytes())
    );
    println!();
    println!("the cross-cell gate installed on room B (a kernel predicate, NOT a host if):");
    println!(
        "  ObservedFieldEquals {{ local=room_B.DOOR, source=lantern.OWNER, at_root={}… }}",
        hx(&world.gate_root())
    );
    println!("  the executor rebuilds the FinalizedRootAuthority from the COMMITTED ledger:");
    println!("    it admits iff the lantern is AT that finalized root AND DOOR == lantern.OWNER.");
    println!();

    // A real ungated turn on room A.
    let r = world.enter_shore().expect("entering room A commits");
    println!(
        "[turn] enter room A (shore)            → committed  receipt={}…",
        hx(&r.turn_hash)
    );
    println!();

    // ── REFUSAL: the cross-cell gate refuses before the peer item is taken ──────────
    println!("--- the cross-cell gate REFUSES until the PEER item is taken ---");
    println!(
        "  lantern.OWNER = {}   lantern live root = {}…",
        slot(world.read(world.lantern(), OWNER_SLOT as usize)),
        hx(&world.lantern_root())
    );
    println!("  (lantern is NOT at the gate root ⇒ the authority has no binding ⇒ fail-closed)");
    match world.open_stair_honest() {
        Ok(r) => println!("  UNEXPECTED commit {}…", hx(&r.turn_hash)),
        Err(e) => println!("  [turn] open room B's stair            → REFUSED across cells: {e}"),
    }
    println!(
        "  room B.DOOR after refusal = {}  (anti-ghost: nothing committed)",
        slot(world.read(world.stair(), DOOR_SLOT as usize))
    );
    println!();

    // ── COMMIT: take the lantern on its own cell, then the gate opens ───────────────
    println!("--- take the lantern on its OWN cell (a real turn), then the gate opens ---");
    let take = world.take_lantern().expect("taking the lantern commits");
    println!(
        "  [turn] take the lantern (item cell)   → committed  receipt={}…",
        hx(&take.turn_hash)
    );
    println!(
        "  lantern.OWNER = {}   lantern live root = {}…",
        slot(world.read(world.lantern(), OWNER_SLOT as usize)),
        hx(&world.lantern_root())
    );
    println!("  (the lantern is now AT the finalized gate root — the peer condition is met)");
    let open = world
        .open_stair_honest()
        .expect("the gated cross-cell open commits");
    println!(
        "  [turn] open room B's stair            → COMMITTED across cells  receipt={}…",
        hx(&open.turn_hash)
    );
    println!(
        "  room B.DOOR = {}  (opened to the lantern's owner — read from ANOTHER cell)",
        slot(world.read(world.stair(), DOOR_SLOT as usize))
    );
    println!();
    println!("  the two receipts land on DISTINCT cells (a cross-cell chain):");
    println!("    take (on lantern) receipt = {}…", hx(&take.turn_hash));
    println!("    open (on room B)  receipt = {}…", hx(&open.turn_hash));
    println!();

    // ── FORGERIES: fail-closed ──────────────────────────────────────────────────────
    println!("--- forged cross-cell claims are refused (fail-closed) ---");
    let fresh = World::deploy();
    fresh.take_lantern().expect("take the lantern");
    match fresh.open_stair(fresh.tag(), false) {
        Ok(r) => println!("  UNEXPECTED commit {}…", hx(&r.turn_hash)),
        Err(e) => println!("  stripped witness (no Merkle-open blob) → REFUSED: {e}"),
    }
    let mut wrong = fresh.tag();
    wrong[1] ^= 0xAA;
    match fresh.open_stair(wrong, true) {
        Ok(r) => println!("  UNEXPECTED commit {}…", hx(&r.turn_hash)),
        Err(e) => println!("  divergent DOOR value (≠ lantern.OWNER)  → REFUSED: {e}"),
    }
    println!();

    // ── The item cell's own first-grabber tooth ────────────────────────────────────
    println!("--- the item's own WriteOnce: first-grabber-wins on the contested resource ---");
    let contested = World::deploy();
    let first = contested.take_lantern().expect("the first grabber commits");
    println!(
        "  [turn] first grabber takes the lantern → committed  receipt={}…",
        hx(&first.turn_hash)
    );
    match contested.rival_take_lantern() {
        Ok(r) => println!("  UNEXPECTED rival commit {}…", hx(&r.turn_hash)),
        Err(e) => println!("  [turn] a rival's conflicting claim     → REFUSED by WriteOnce: {e}"),
    }
    println!(
        "  lantern.OWNER = {}  (still the first grabber — anti-ghost)",
        slot(contested.read(contested.lantern(), OWNER_SLOT as usize))
    );
    println!("  (genuinely-CONCURRENT divergent claims merge settlement-soundly via");
    println!("   starbridge_v2::branch_stitch_session — the mud-dregg precedent — where a");
    println!("   contested take is a real #-conflict; this drives the serialized tooth it rides.)");
    println!();
    println!("=== the cross-cell gate is a REAL executor predicate: room B opened because item A");
    println!(
        "    was taken on ANOTHER cell — driven, refused fail-closed, committed with witness. ==="
    );
}
