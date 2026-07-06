//! THE PLAYABLE ARC — the four teeth of `mud-dregg`, each a real dregg mechanism, shared by
//! the `main` narration and the acceptance tests.
//!
//!   TOOTH 1 · rooms are cells + a command is a verifiable turn (it re-verifies, state moves).
//!   TOOTH 2 · a FORGED move is REFUSED — a command the actor's cap does not authorize is a
//!             real `CapabilityNotHeld` executor refusal, not app bookkeeping.
//!   TOOTH 3 · two players FORK → EXPLORE → STITCH, disjoint edits MERGE clean (both present).
//!   TOOTH 4 · a REAL CONFLICT is REFUSED — two players grabbing the ONE sword write the same
//!             address, a `#`-conflict held fail-closed (a conflict object, never silent LWW).
//!
//! Teeth 3+4 are the dreggic core: the divergent player-timelines ARE the proven
//! distributed-time-travel config lattice `(E, ≤, #)` (`DISTRIBUTED-TIMETRAVEL-SEMANTICS.md`
//! §2.1) — a fork picks a configuration, a stitch is the conflict-free union, and a genuine
//! `#`-conflict cannot silently merge (Settlement Soundness, proven axiom-clean at
//! `metatheory/Metatheory/SettlementSoundness.lean:153`). We drive the LIVE gate via
//! [`BranchStitchSession`], the operable shadow of that proof.

use starbridge_v2::branch_stitch_session::BranchStitchSession;

use dregg_turn::umem::UKey;

use crate::dungeon::{actor_tag, Command, Dungeon, Layout, WorldCell, SLOT_OWNER, SLOT_PRESENCE};

/// TOOTH 1 — rooms are cells; a command is a verifiable turn. Alice `go`es into the hall: a
/// real signed turn lands (re-verifies with a receipt) and the hall CELL's presence slot now
/// records her — the world state moved through a turn, on the ledger, not by fiat.
pub fn tooth_rooms_are_cells_commands_are_turns() {
    let mut dungeon = Dungeon::new();
    let l = dungeon.layout();

    // The hall IS a cell in the world ledger (a room = a cell).
    assert!(
        dungeon.world().ledger().get(&l.hall).is_some(),
        "the hall is a real cell in the ledger (a room is a cell)"
    );
    // Its presence slot starts empty.
    assert_eq!(
        dungeon.field(l.hall, SLOT_PRESENCE),
        Some([0u8; 32]),
        "the hall presence slot starts empty"
    );

    // `alice: go hall` — a cap-bounded turn.
    let out = dungeon.issue(l.alice, &Command::Go { room: l.hall });
    assert!(
        out.committed(),
        "alice may act in the hall — the command commits as a real receipted turn: {out:?}"
    );

    // The turn re-verified (a real receipt) AND the room cell's state advanced to record her.
    assert_eq!(
        dungeon.field(l.hall, SLOT_PRESENCE),
        Some(actor_tag(l.alice)),
        "the hall CELL now records alice's presence — the command moved world state via a turn"
    );
}

/// TOOTH 2 — a FORGED move is REFUSED. Alice tries to force BOB's character to move (a command
/// on a cell she holds no cap to) — the exact "you cannot cast another player's move" property.
/// The real executor refuses it (`CapabilityNotHeld`); nothing is applied. A second forge — Alice
/// reaching into the cavern (outside her mandate) — is refused the same way.
pub fn tooth_forged_move_refused() {
    let mut dungeon = Dungeon::new();
    let l = dungeon.layout();

    // Alice tries to FORGE Bob's move — drive Bob's character cell directly. She holds no cap
    // to `bob`, so it is refused.
    let forged = dungeon.issue(
        l.alice,
        &Command::Force {
            target: l.bob,
            value: actor_tag(l.alice),
        },
    );
    assert!(
        forged.refused(),
        "alice cannot forge bob's move — an ungranted target is a real executor refusal: {forged:?}"
    );
    if let crate::dungeon::CommandOutcome::Refused { reason } = &forged {
        assert!(
            reason.to_lowercase().contains("cap"),
            "the refusal is a capability refusal (CapabilityNotHeld), got: {reason}"
        );
    }
    // Bob's character was NOT moved — the forge left no trace.
    assert_eq!(
        dungeon.field(l.bob, SLOT_PRESENCE),
        Some([0u8; 32]),
        "the forged move applied nothing — bob's cell is untouched"
    );

    // A second forge: alice reaching into the cavern (outside her mandate) — refused too.
    let reach = dungeon.issue(l.alice, &Command::Go { room: l.cavern });
    assert!(
        reach.refused(),
        "alice cannot act in the cavern (no cap) — refused: {reach:?}"
    );
    assert_eq!(
        dungeon.field(l.cavern, SLOT_PRESENCE),
        Some([0u8; 32]),
        "the cavern is untouched by the over-reach"
    );
}

/// A `UKey` for a cell's state field (the universal-memory address a stitch merges/collides on).
fn field_key(cell: dregg_cell::CellId, slot: u64) -> UKey {
    UKey::Field { cell, slot }
}

/// TOOTH 3 — FORK → EXPLORE → STITCH, disjoint edits MERGE clean. Alice and Bob each fork the
/// dungeon into their own divergent timeline (a configuration of the lattice), explore
/// privately (Alice acts in the hall, Bob in the cavern — DISJOINT addresses), and stitch back:
/// the conflict-free union LANDS, both players' edits present, main untouched until applied.
pub fn tooth_fork_explore_stitch_disjoint_merges() {
    let (world, l): (_, Layout) = Dungeon::new().into_parts();
    let session = BranchStitchSession::open(world, l.focus(), 3);

    // Alice forks her own timeline and explores the hall.
    let mut alice = session.fork();
    alice
        .drive(alice.turn(l.alice, l.lower(l.alice, &Command::Go { room: l.hall })))
        .expect("alice explores her own branch — a real verified turn");

    // Bob forks his own timeline and explores the cavern (a DISJOINT address).
    let mut bob = session.fork();
    bob.drive(bob.turn(l.bob, l.lower(l.bob, &Command::Go { room: l.cavern })))
        .expect("bob explores his own branch");

    // Stitch the two divergent timelines under the settlement-sound gate.
    let v = session.stitch(&alice, &bob);
    assert!(
        v.settles(),
        "disjoint edits settle — the conflict-free union lands: {:?}",
        v.state_conflicts
    );
    assert!(
        v.settled_root.is_some(),
        "a settled stitch has a binding merged root"
    );
    // BOTH players' edits are present in the merge (co-drive, never last-writer-wins).
    assert!(
        v.merged.contains(&field_key(l.hall, SLOT_PRESENCE as u64)),
        "alice's hall edit is in the merge"
    );
    assert!(
        v.merged
            .contains(&field_key(l.cavern, SLOT_PRESENCE as u64)),
        "bob's cavern edit is in the merge"
    );
    // Divergence was imaginary until applied — main stayed pristine.
    assert_eq!(
        session.base().ledger().get(&l.hall).unwrap().state.fields[SLOT_PRESENCE],
        [0u8; 32],
        "main untouched — the timelines were imaginary until a verdict is applied"
    );
}

/// TOOTH 4 — a REAL CONFLICT is REFUSED. Alice and Bob each fork and BOTH grab the ONE sword
/// (`take sword` — the SAME entity's owner slot). At stitch this is a `#`-conflict: the two
/// timelines cannot silently merge. The stitch is WITHHELD fail-closed, surfaced as a conflict
/// object naming the exact contested address — both readings kept, never a silent overwrite.
/// This IS the config-lattice / Settlement-Soundness tooth biting.
pub fn tooth_real_conflict_refused() {
    let (world, l): (_, Layout) = Dungeon::new().into_parts();
    let session = BranchStitchSession::open(world, l.focus(), 3);

    // Alice forks and takes the sword.
    let mut alice = session.fork();
    alice
        .drive(alice.turn(
            l.alice,
            l.lower(l.alice, &Command::Take { entity: l.sword }),
        ))
        .expect("alice grabs the sword on her branch");

    // Bob forks and ALSO takes the (one) sword — same entity, same owner slot.
    let mut bob = session.fork();
    bob.drive(bob.turn(l.bob, l.lower(l.bob, &Command::Take { entity: l.sword })))
        .expect("bob grabs the sword on his branch");

    let v = session.stitch(&alice, &bob);
    assert!(
        !v.settles(),
        "two players grabbing the one sword is a genuine conflict — the stitch does NOT settle"
    );
    assert!(
        v.settled_root.is_none(),
        "no settled root while the conflict is live (fail-closed)"
    );
    assert_eq!(
        v.state_conflicts,
        vec![field_key(l.sword, SLOT_OWNER as u64)],
        "the conflict names the EXACT contested address (sword.owner) — both readings kept, no silent LWW"
    );
    // The two readings are genuinely distinct (alice vs bob) — a real `#`, not a coincidence.
    assert_ne!(
        actor_tag(l.alice),
        actor_tag(l.bob),
        "the two grabs carry distinct owner tags — a genuine value collision"
    );
}

/// Run the whole playable arc — narrated for the demo binary, asserted for the tests. Each tooth
/// asserts internally; a panic here is a real broken guarantee.
pub fn run_arc() {
    println!(
        "\n=== mud-dregg — the multiplayer dungeon where the timelines ARE the proven lattice ==="
    );
    println!("rooms are cells · commands are verifiable turns · fork→stitch divergent play, conflicts REFUSED\n");

    println!("── TOOTH 1 · rooms are cells; a command is a verifiable turn ───────────────────");
    tooth_rooms_are_cells_commands_are_turns();
    println!("   ✓ the hall is a cell; `alice: go hall` committed as a real receipted turn; the room-cell state moved");

    println!("\n── TOOTH 2 · a forged move is REFUSED (nobody casts another player's move) ──────");
    tooth_forged_move_refused();
    println!("   ✓ alice forging bob's move (and reaching the cavern she has no cap to) — REFUSED by the real executor");

    println!("\n── TOOTH 3 · fork → explore → stitch: disjoint edits MERGE clean ────────────────");
    tooth_fork_explore_stitch_disjoint_merges();
    println!("   ✓ alice (hall) + bob (cavern) forked divergent timelines; the conflict-free union LANDED, both present, main pristine");

    println!("\n── TOOTH 4 · a real conflict is REFUSED (the `#` of the config lattice) ─────────");
    tooth_real_conflict_refused();
    println!("   ✓ both grabbed the ONE sword — a `#`-conflict held fail-closed at sword.owner; a conflict object, never silent last-writer-wins");

    println!("\n=== rooms-as-cells · commands-as-turns · divergent-timelines-as-the-lattice — REAL ===\n");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn t1_rooms_are_cells_commands_are_turns() {
        tooth_rooms_are_cells_commands_are_turns();
    }

    #[test]
    fn t2_forged_move_refused() {
        tooth_forged_move_refused();
    }

    #[test]
    fn t3_fork_explore_stitch_disjoint_merges() {
        tooth_fork_explore_stitch_disjoint_merges();
    }

    #[test]
    fn t4_real_conflict_refused() {
        tooth_real_conflict_refused();
    }

    /// The whole arc as one acceptance test.
    #[test]
    fn the_playable_arc() {
        run_arc();
    }
}
