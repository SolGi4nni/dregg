//! DECISION 1 (ember's DECIDED "Both") — the membrane is a PER-REALM PROPERTY,
//! not one fixed engine policy. Each realm DECLARES how its instances observe it:
//!
//!   * [`Membrane::PinAtBirth`]  — the instance snapshots the realm root at open;
//!     concurrent realm changes are INVISIBLE until settle (deterministic /
//!     replayable — a fair daily seed).
//!   * [`Membrane::MovingParent`] — the instance tracks the realm HEAD;
//!     concurrent realm changes are VISIBLE live (a persistent shared town).
//!
//! Driven here: same crate, each realm declares which; the property is
//! load-bearing (flip the membrane, and the SAME instance's visible parent
//! flips — the canary). Plus the settle-back semantics MovingParent forces: the
//! additive settle is conflict-free (a commutative accumulator — two concurrent
//! settles both land), and the OCC settle DETECTS a lost-update conflict against
//! a moved head (the conflict-resolution policy is named as ember's open call).

use dregg_turn::action::Effect;
use realm_model::identity::{Surface, SurfaceRef};
use realm_model::instance::field as ifield;
use realm_model::realm::Membrane;
use realm_model::{RealmWorld, Refused, RulesetRoot, pack_u64};

fn ruleset(name: &str) -> RulesetRoot {
    *blake3::hash(name.as_bytes()).as_bytes()
}

/// Stand a bound actor + a listed law up on a fresh world (shared setup).
fn actor_and_law(world: &mut RealmWorld) -> (SurfaceRef, RulesetRoot) {
    let me = world.mint_identity("resident", "seed-resident").unwrap();
    let actor = SurfaceRef::new(Surface::Native, "resident#1");
    world.bind_surface(&me, actor.clone()).unwrap();
    (actor, ruleset("town-law-v1"))
}

/// Advance the realm head by opening a throwaway instance, earning `amount`, and
/// settling it back (the additive, catalog-gated settle path).
fn advance_realm(
    world: &mut RealmWorld,
    realm: &dregg_cell::CellId,
    actor: &SurfaceRef,
    law: RulesetRoot,
    seed: &str,
    amount: u64,
) {
    let inst = world.open_instance(realm, seed).unwrap();
    world
        .play(actor.clone(), inst.id, law, ifield::RESULT, amount)
        .unwrap();
    world.settle_instance(actor.clone(), inst.id, law).unwrap();
}

/// The load-bearing property + canary: two realms IDENTICAL but for their
/// membrane; an open instance in each; an identical concurrent realm advance.
/// The PinAtBirth instance does NOT see it (stays 0); the MovingParent instance
/// DOES (jumps to the new head). Flip the membrane -> visibility flips.
#[test]
fn membrane_is_per_realm_and_load_bearing() {
    let mut world = RealmWorld::new();
    let (actor, law) = actor_and_law(&mut world);

    // Two realms differing ONLY in their declared membrane.
    let pinned = world
        .create_realm_with_membrane("descent-daily", Membrane::PinAtBirth)
        .unwrap();
    let living = world
        .create_realm_with_membrane("hearthspire", Membrane::MovingParent)
        .unwrap();
    world.list_ruleset(&pinned.id, law).unwrap();
    world.list_ruleset(&living.id, law).unwrap();

    // The membrane is COMMITTED realm state, read off the cell (the authority).
    assert_eq!(world.membrane_of(&pinned.id), Membrane::PinAtBirth);
    assert_eq!(world.membrane_of(&living.id), Membrane::MovingParent);

    // An instance opens in each realm while the realm head is still 0.
    let obs_pinned = world.open_instance(&pinned.id, "run-A").unwrap();
    let obs_living = world.open_instance(&living.id, "plot-A").unwrap();
    assert_eq!(world.visible_parent(&obs_pinned.id), 0);
    assert_eq!(world.visible_parent(&obs_living.id), 0);

    // CONCURRENTLY advance BOTH realms by the SAME amount (a neighbor settles),
    // while both observer instances remain OPEN.
    advance_realm(&mut world, &pinned.id, &actor, law, "neighbor-P", 50);
    advance_realm(&mut world, &living.id, &actor, law, "neighbor-L", 50);
    assert_eq!(
        world.realm_hoard(&pinned.id),
        50,
        "pinned realm head advanced"
    );
    assert_eq!(
        world.realm_hoard(&living.id),
        50,
        "living realm head advanced"
    );

    // THE PROPERTY: the SAME concurrent change is invisible to the PinAtBirth
    // instance (deterministic) and visible to the MovingParent instance (live).
    assert_eq!(
        world.visible_parent(&obs_pinned.id),
        0,
        "PinAtBirth: the open instance does NOT see the concurrent realm change"
    );
    assert_eq!(
        world.visible_parent(&obs_living.id),
        50,
        "MovingParent: the open instance DOES see the concurrent realm change (live)"
    );

    // The pinned-realm instance's committed snapshot really is frozen at 0.
    assert_eq!(world.instance_parent_pin(&obs_pinned.id), 0);
}

/// The CANARY, sharpened: the ONLY thing that changes the visibility outcome is
/// the realm's membrane. Rebuild the exact same scenario under MovingParent and
/// the previously-invisible change becomes visible — the property is genuinely
/// load-bearing, not incidental.
#[test]
fn flipping_the_membrane_flips_visibility() {
    // A helper that runs the identical scenario under a given membrane and
    // returns what the open observer instance sees after a concurrent advance.
    fn observed_under(membrane: Membrane) -> u64 {
        let mut world = RealmWorld::new();
        let (actor, law) = actor_and_law(&mut world);
        let realm = world.create_realm_with_membrane("world", membrane).unwrap();
        world.list_ruleset(&realm.id, law).unwrap();
        let obs = world.open_instance(&realm.id, "observer").unwrap();
        advance_realm(&mut world, &realm.id, &actor, law, "mover", 77);
        world.visible_parent(&obs.id)
    }

    let pinned_view = observed_under(Membrane::PinAtBirth);
    let moving_view = observed_under(Membrane::MovingParent);
    assert_eq!(pinned_view, 0, "PinAtBirth hides the concurrent advance");
    assert_eq!(moving_view, 77, "MovingParent shows the concurrent advance");
    assert_ne!(
        pinned_view, moving_view,
        "the realm's membrane is the ONLY difference — it is load-bearing"
    );
}

/// The additive settle is a COMMUTATIVE accumulator: two instances that both
/// settle into a live MovingParent realm both land — no lost update, no conflict.
/// This is the non-conflicting case the model DRIVES.
#[test]
fn moving_parent_additive_settles_are_conflict_free() {
    let mut world = RealmWorld::new();
    let (actor, law) = actor_and_law(&mut world);
    let realm = world
        .create_realm_with_membrane("bazaar", Membrane::MovingParent)
        .unwrap();
    world.list_ruleset(&realm.id, law).unwrap();

    // Two instances open concurrently (both see head 0 live).
    let a = world.open_instance(&realm.id, "stall-a").unwrap();
    let b = world.open_instance(&realm.id, "stall-b").unwrap();
    world
        .play(actor.clone(), a.id, law, ifield::RESULT, 30)
        .unwrap();
    world
        .play(actor.clone(), b.id, law, ifield::RESULT, 12)
        .unwrap();

    // Both settle. The additive settle reads the LIVE head and adds — commutative,
    // so BOTH deltas land regardless of order (no lost update).
    world.settle_instance(actor.clone(), a.id, law).unwrap();
    // b saw head 0 live at open; it now sees 30 live (MovingParent) — and its
    // additive settle still composes cleanly.
    assert_eq!(world.visible_parent(&b.id), 30, "b sees a's settle live");
    world.settle_instance(actor.clone(), b.id, law).unwrap();
    assert_eq!(
        world.realm_hoard(&realm.id),
        42,
        "both concurrent settles landed (30 + 12) — conflict-free accumulator"
    );
}

/// The settle-back conflict MovingParent forces for a NON-commutative result:
/// the OCC settle carries the head its result was computed against; if the head
/// MOVED, the settle is REFUSED (detection), leaving the ledger unchanged. The
/// non-conflicting settle (head unchanged) lands. The resolution policy once a
/// conflict is detected is ember's open call (named on `SettleConflict`).
#[test]
fn moving_parent_occ_settle_detects_a_moved_head() {
    let mut world = RealmWorld::new();
    let (actor, law) = actor_and_law(&mut world);
    let realm = world
        .create_realm_with_membrane("keep", Membrane::MovingParent)
        .unwrap();
    world.list_ruleset(&realm.id, law).unwrap();

    // Bring the head to a known value.
    advance_realm(&mut world, &realm.id, &actor, law, "seed-head", 100);
    assert_eq!(world.realm_hoard(&realm.id), 100);

    // An instance computes a NON-commutative result against head = 100.
    let c = world.open_instance(&realm.id, "scribe").unwrap();
    world
        .play(actor.clone(), c.id, law, ifield::RESULT, 5)
        .unwrap();
    let expected_head = world.realm_hoard(&realm.id); // 100

    // A neighbor settles underneath it: the head MOVES to 130.
    advance_realm(&mut world, &realm.id, &actor, law, "usurper", 30);
    assert_eq!(world.realm_hoard(&realm.id), 130);

    // The OCC settle against the STALE head is refused (conflict detected) — the
    // concurrent advance is NOT silently clobbered/lost.
    let conflict = world.settle_instance_expecting(actor.clone(), c.id, law, expected_head);
    assert!(
        matches!(
            conflict,
            Err(Refused::SettleConflict { expected_head: e, found_head: f, .. })
                if e == 100 && f == 130
        ),
        "OCC settle against a moved head must be refused; got {conflict:?}"
    );
    // Nothing committed: the neighbor's 130 stands, the instance is still open.
    assert_eq!(
        world.realm_hoard(&realm.id),
        130,
        "conflict left the head intact"
    );
    assert_eq!(
        world.instance_status(&c.id),
        realm_model::instance::InstanceStatus::Open,
        "conflicted instance is not finalized"
    );

    // Re-based against the CURRENT head, the same OCC settle lands.
    let head_now = world.realm_hoard(&realm.id); // 130
    world
        .settle_instance_expecting(actor.clone(), c.id, law, head_now)
        .expect("OCC settle against the live head lands");
    assert_eq!(
        world.realm_hoard(&realm.id),
        135,
        "rebased settle applied (130 + 5)"
    );
}

/// A PinAtBirth realm keeps its committed determinism end-to-end: an in-instance
/// turn still cannot forge the realm cell (the scope membrane), and the pinned
/// snapshot is unaffected by a concurrent settle.
#[test]
fn pin_at_birth_stays_deterministic_and_scoped() {
    let mut world = RealmWorld::new();
    let (actor, law) = actor_and_law(&mut world);
    let realm = world
        .create_realm_with_membrane("daily", Membrane::PinAtBirth)
        .unwrap();
    world.list_ruleset(&realm.id, law).unwrap();

    let run = world.open_instance(&realm.id, "seed-2026-07-16").unwrap();
    // A concurrent advance the pinned run must never observe.
    advance_realm(&mut world, &realm.id, &actor, law, "elsewhere", 999);
    assert_eq!(
        world.visible_parent(&run.id),
        0,
        "the daily run sees its pinned world, not the moved realm"
    );

    // The scope membrane still holds under PinAtBirth: a direct realm write fails.
    let reach = world.admit(realm_model::RealmTurn {
        actor: actor.clone(),
        instance: run.id,
        ruleset_root: law,
        effects: vec![Effect::SetField {
            cell: realm.id,
            index: realm_model::realm::field::HOARD,
            value: pack_u64(1),
        }],
    });
    assert!(matches!(reach, Err(Refused::OutsideInstanceScope { .. })));
}
