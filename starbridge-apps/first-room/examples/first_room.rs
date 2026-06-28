//! THE FIRST ROOM — runnable. `cargo run -p starbridge-first-room --example first_room`
//!
//! Stands up the first room of the living world and prints the in-room transcript: the colonist does
//! its mandated job step-by-step (each a receipted turn), finishes, the escrow releases, it is PAID;
//! then the try-to-cheat battery — each cheat REFUSED in-band by the real executor, rendered in-room
//! with the receipt-why. Everything here flows through ONE real EmbeddedExecutor; nothing is faked.

use starbridge_first_room::scenario::{davids_door, run_first_room};

fn main() {
    let t = run_first_room();
    let room = t.room.render();

    println!("╔══════════════════════════════════════════════════════════════════════╗");
    println!("║  THE FIRST ROOM OF THE LIVING WORLD — \"{}\"", room.name);
    println!("║  a persistent place; its inhabitants act ONLY through a mandate proven  ║");
    println!("║  safe-forever. one real executor, one ledger — every step a real turn.  ║");
    println!("╚══════════════════════════════════════════════════════════════════════╝");
    println!();

    for inh in &room.inhabitants {
        println!("┌─ {} [{}]", inh.name, inh.short);
        println!("│   mandate: {}", inh.mandate);
        if !inh.committed_actions.is_empty() {
            println!("│   ── genuine actions (committed, receipted) ──");
            for a in &inh.committed_actions {
                let r = &a.receipt_hash;
                let rh = if *r == [0u8; 32] {
                    "(economy event)".to_string()
                } else {
                    format!("receipt {:02x}{:02x}{:02x}{:02x}…", r[0], r[1], r[2], r[3])
                };
                println!("│      ✓ {}  [{}]", a.summary, rh);
            }
        }
        if inh.paid > 0 {
            println!(
                "│   💰 PAID: {} (the conserved reward, released on completion)",
                inh.paid
            );
        }
        if !inh.refusals.is_empty() {
            println!("│   ── in-room refusals (the anti-ghost tooth, surfaced) ──");
            for r in &inh.refusals {
                println!("│      ✗ tried to {}", r.attempted);
                println!("│          → {}", r.reason);
            }
        }
        println!("└─");
        println!();
    }

    println!("── THE CYCLE ──────────────────────────────────────────────────────────");
    println!("  reward escrowed (conserved pool) : {}", t.funded_reward);
    print!("  job (gather→make→hand-off)       : ");
    for (i, s) in t.job_steps.iter().enumerate() {
        if i > 0 {
            print!(" → ");
        }
        print!("{:?}(spend {}/9)", s.verb, s.spend_after);
    }
    println!();
    println!("  job done                          : {}", t.job_done);
    println!(
        "  PAID — colonist HOLDS (a REAL Transfer): {}  (== escrowed: {})",
        t.paid,
        t.paid == t.funded_reward && t.conserved
    );
    println!(
        "  value conserved (escrow Σ + CREDIT Σδ=0): {}",
        t.conserved && t.credit_conserved
    );
    println!();

    println!("── THE TRY-TO-CHEAT BATTERY (each REFUSED in-band) ──────────────────────");
    for c in &t.cheats {
        let mark = if c.provably_refused() {
            "REFUSED ✓"
        } else {
            "!!! NOT REFUSED !!!"
        };
        println!("  [{}]  {}", mark, c.class.label());
        println!("        tooth: {}", c.class.tooth());
        println!("        why:   {}", c.reason);
    }
    println!();

    println!("── DAVID'S DOOR ─────────────────────────────────────────────────────────");
    println!("  {}", davids_door());
    println!();

    let holds = t.first_room_holds();
    println!("════════════════════════════════════════════════════════════════════════");
    println!("  THE FIRST ROOM HOLDS: {}", holds);
    println!("  (job done + colonist HOLDS the reward in full + escrow Σ conserving + CREDIT Σδ=0");
    println!("   + every cheat provably refused)");
    println!("════════════════════════════════════════════════════════════════════════");
    println!();

    // The composed room ALSO ships as a renderer-independent `deos.ui.*` CARD (the one modern-app
    // axis that fits a composition exemplar): a rich, legible composed-room view-tree.
    let card_json = starbridge_first_room::room_card_json(&room);
    println!(
        "── THE COMPOSED-ROOM CARD (deos.ui.* JSON, {} bytes) ──",
        card_json.len()
    );
    println!("  {card_json}");

    if !holds {
        std::process::exit(1);
    }
}
