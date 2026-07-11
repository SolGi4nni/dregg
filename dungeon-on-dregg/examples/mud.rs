//! A 2-player (well, 3) session on the REAL shared multi-cell world.
//!
//! Run: `cargo run -p dungeon-on-dregg --example mud`
//!
//! Several player-cells inhabit ONE living world. Each MOVES via a real cap-bounded turn
//! (a real `TurnReceipt`). Two players reach for the SAME lantern: the first commits
//! (`WriteOnce` owner), the second is a REAL executor refusal — one owner, anti-ghost. A
//! move a player holds no cap for is a real `CapabilityNotHeld` refusal. Then the CONCURRENT
//! face: the two grabs on divergent forks are a real `#`-conflict at the stitch.

use dungeon_on_dregg::mud::{
    Command, CommandOutcome, MudWorld, SLOT_OWNER, SLOT_PRESENCE, actor_tag,
};
use starbridge_v2::branch_stitch_session::BranchStitchSession;
use starbridge_v2::world::short;

fn tag8(t: [u8; 32]) -> String {
    t.iter().take(6).map(|b| format!("{b:02x}")).collect()
}

fn report(who: &str, verb: &str, out: &CommandOutcome) {
    match out {
        CommandOutcome::Committed { receipt } => {
            println!("   ✓ {who} {verb} — COMMITTED, receipt {}…", tag8(*receipt));
        }
        CommandOutcome::Refused { reason } => {
            println!("   ✗ {who} {verb} — REFUSED: {reason}");
        }
    }
}

fn main() {
    println!(
        "\n=== dungeon-on-dregg · mud — a multi-player SHARED WORLD on the real substrate ==="
    );
    println!(
        "several player-cells, ONE living world · real cap-bounded turns · contested item, one owner\n"
    );

    let mut mud = MudWorld::new();
    let l = mud.layout();
    println!("── the world: three player-cells inhabit one shared ledger ─────────────────────");
    println!(
        "   alice  = {}   (may act: plaza, north_walk, lantern)",
        short(&l.alice)
    );
    println!(
        "   bob    = {}   (may act: plaza, south_vault, lantern)",
        short(&l.bob)
    );
    println!(
        "   carol  = {}   (may act: plaza, lantern)",
        short(&l.carol)
    );
    println!(
        "   lantern= {}   (the ONE contested item — WriteOnce owner)\n",
        short(&l.lantern)
    );

    println!("── each player MOVES via a real turn on the ONE world ──────────────────────────");
    report(
        "alice",
        "go plaza",
        &mud.issue(l.alice, &Command::Go { room: l.plaza }),
    );
    report(
        "bob",
        "go south_vault",
        &mud.issue(
            l.bob,
            &Command::Go {
                room: l.south_vault,
            },
        ),
    );
    report(
        "carol",
        "go plaza",
        &mud.issue(l.carol, &Command::Go { room: l.plaza }),
    );
    println!(
        "   → the ONE shared world now holds: south_vault.presence = bob({}…)",
        tag8(mud.field(l.south_vault, SLOT_PRESENCE).unwrap())
    );

    println!("\n── an UNAUTHORIZED move is a real CapabilityNotHeld refusal ─────────────────────");
    report(
        "carol",
        "go north_walk (no cap — alice's room)",
        &mud.issue(l.carol, &Command::Go { room: l.north_walk }),
    );
    report(
        "alice",
        "FORCE bob's cell (forging bob's move, no cap)",
        &mud.issue(
            l.alice,
            &Command::Force {
                target: l.bob,
                value: actor_tag(l.alice),
            },
        ),
    );

    println!("\n── the CONTESTED item: two players reach for the ONE lantern ────────────────────");
    report(
        "alice",
        "take lantern",
        &mud.issue(l.alice, &Command::Take { item: l.lantern }),
    );
    report(
        "bob",
        "take lantern (the SAME one)",
        &mud.issue(l.bob, &Command::Take { item: l.lantern }),
    );
    report(
        "carol",
        "take lantern (the SAME one)",
        &mud.issue(l.carol, &Command::Take { item: l.lantern }),
    );
    let owner = mud.field(l.lantern, SLOT_OWNER).unwrap();
    println!(
        "   → the lantern has exactly ONE owner: {}… {}",
        tag8(owner),
        if owner == actor_tag(l.alice) {
            "(alice, the first grabber — anti-ghost)"
        } else {
            "(?!)"
        }
    );

    println!(
        "\n── the CONCURRENT face: both grab the lantern on DIVERGENT forks → a `#`-conflict ─"
    );
    let (world, l) = MudWorld::new().into_parts();
    let session = BranchStitchSession::open(world, l.focus(), 3);
    let mut a = session.fork();
    a.drive(a.turn(
        l.alice,
        l.lower(l.alice, &Command::Take { item: l.lantern }),
    ))
    .expect("alice grabs on her fork");
    let mut b = session.fork();
    b.drive(b.turn(l.bob, l.lower(l.bob, &Command::Take { item: l.lantern })))
        .expect("bob grabs on his fork");
    let v = session.stitch(&a, &b);
    println!(
        "   stitch settles? {}  (fail-closed — a real conflict cannot silently merge)",
        v.settles()
    );
    println!("   settled_root: {:?}", v.settled_root.map(|r| tag8(r)));
    println!(
        "   conflict address(es): {:?}  ← the exact contested lantern.owner, both readings kept",
        v.state_conflicts
    );

    println!(
        "\n=== multiple player-cells · one shared world · contested item = one owner / real `#` — REAL ===\n"
    );
}
