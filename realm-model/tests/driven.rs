//! The DRIVEN prototype — each of the three §9 decisions proven by RUNNING it
//! against real cell-backed state. Engine-general throughout: a realm is "a
//! realm", an identity is "a principal", a ruleset is an opaque 32-byte root.
//!
//!   1. a persistent REALM outlives an INSTANCE (§9.4): an instance settles a
//!      result back, then a NEW instance sees it.
//!   2. ONE identity acts across two instances/surfaces (§9.5): the same durable
//!      canonical identity, different surface bindings, resolves the same.
//!   3. the CATALOG gates which `ruleset_root` a turn may use (§9.2): an unlisted
//!      root is refused, a listed one admitted — committed law, with the canary
//!      (unlist a listed root -> now refused).

use realm_model::identity::{Surface, SurfaceRef};
use realm_model::instance::InstanceStatus;
use realm_model::{RealmTurn, RealmWorld, Refused, RulesetRoot};

use dregg_turn::action::Effect;
use realm_model::pack_u64;

fn ruleset(name: &str) -> RulesetRoot {
    *blake3::hash(name.as_bytes()).as_bytes()
}

/// §9.4 — the persistent realm outlives its instances; a result settles back;
/// a fresh instance pins the NEW durable value.
#[test]
fn realm_persists_across_instances() {
    let mut world = RealmWorld::new();

    let player = world.mint_identity("player-one", "seed-p1").unwrap();
    world
        .bind_surface(&player, SurfaceRef::new(Surface::Discord, "p1#0001"))
        .unwrap();
    let actor = SurfaceRef::new(Surface::Discord, "p1#0001");

    let realm = world.create_realm("the-burrow").unwrap();
    let law = ruleset("descent-v1");
    world.list_ruleset(&realm.id, law).unwrap();

    // The realm starts empty and durable.
    assert_eq!(world.realm_hoard(&realm.id), 0, "fresh realm hoard is 0");
    assert_eq!(world.realm_epoch(&realm.id), 0);

    // ── INSTANCE A: opens (pins parent=0), plays a result, settles it back. ──
    let inst_a = world.open_instance(&realm.id, "day-1").unwrap();
    assert_eq!(inst_a.parent_pin, 0, "instance A pinned parent hoard = 0");
    assert_eq!(world.instance_status(&inst_a.id), InstanceStatus::Open);

    // Play: the instance earns a certified result of 40 (scoped scratch write).
    world
        .play(
            actor.clone(),
            inst_a.id,
            law,
            realm_model::instance::field::RESULT,
            40,
        )
        .unwrap();
    assert_eq!(
        world.instance_result(&inst_a.id),
        40,
        "result staged in scratch"
    );

    // Settle: the result crosses the membrane into the persistent realm.
    world
        .settle_instance(actor.clone(), inst_a.id, law)
        .unwrap();
    assert_eq!(
        world.realm_hoard(&realm.id),
        40,
        "realm accrued the settled result"
    );
    assert_eq!(world.realm_epoch(&realm.id), 1, "realm epoch advanced");
    assert_eq!(
        world.instance_status(&inst_a.id),
        InstanceStatus::Finalized,
        "instance A is spent"
    );

    // A finalized instance cannot act again (its scratch is disposable/closed).
    let reuse = world.play(
        actor.clone(),
        inst_a.id,
        law,
        realm_model::instance::field::RESULT,
        999,
    );
    assert!(
        matches!(reuse, Err(Refused::InstanceFinalized(_))),
        "a finalized instance refuses further turns; got {reuse:?}"
    );

    // ── INSTANCE B: a NEW instance sees the persisted realm state at birth. ──
    let inst_b = world.open_instance(&realm.id, "day-2").unwrap();
    assert_eq!(
        inst_b.parent_pin, 40,
        "the NEW instance pinned the PERSISTED realm value (40), not 0 — persistence is real"
    );
    assert_ne!(
        inst_a.id, inst_b.id,
        "instances are distinct scoped children (fresh scratch cell each)"
    );

    // Instance B settles too — the realm keeps accruing (durable, cross-session).
    world
        .play(
            actor.clone(),
            inst_b.id,
            law,
            realm_model::instance::field::RESULT,
            5,
        )
        .unwrap();
    world.settle_instance(actor, inst_b.id, law).unwrap();
    assert_eq!(
        world.realm_hoard(&realm.id),
        45,
        "realm outlived both instances, accruing 40+5"
    );
    assert_eq!(world.realm_epoch(&realm.id), 2);
}

/// §9.5 — one canonical identity spans two surfaces AND two instances; the
/// surface binding is DERIVED (points at the identity), not primary.
#[test]
fn one_identity_across_surfaces_and_instances() {
    let mut world = RealmWorld::new();

    // The canonical identity exists FIRST, independent of any surface.
    let me = world.mint_identity("pip", "seed-pip").unwrap();

    // Two DIFFERENT surfaces bind onto the SAME canonical identity.
    let discord = SurfaceRef::new(Surface::Discord, "pip#1234");
    let web = SurfaceRef::new(Surface::Web, "sess-deadbeef");
    world.bind_surface(&me, discord.clone()).unwrap();
    world.bind_surface(&me, web.clone()).unwrap();

    // Both surfaces resolve to the SAME canonical id (the binding is derived).
    let via_discord = world.resolve_surface(&discord).expect("discord resolves");
    let via_web = world.resolve_surface(&web).expect("web resolves");
    assert_eq!(
        via_discord.id, me.id,
        "discord surface resolves to canonical id"
    );
    assert_eq!(via_web.id, me.id, "web surface resolves to canonical id");
    assert_eq!(
        via_discord.id, via_web.id,
        "ONE identity across two surfaces — not two parallel per-surface identities"
    );

    // An UNBOUND surface resolves to nothing — a surface id is NOT itself an
    // identity (the §9.5 refusal: the first Discord id is not the world identity).
    let stranger = SurfaceRef::new(Surface::Telegram, "unknown-999");
    assert!(
        world.resolve_surface(&stranger).is_none(),
        "an unbound surface is not an identity"
    );

    // The same identity acts in TWO instances of a realm, arriving on a
    // DIFFERENT surface each time — every receipt attributes the SAME canonical id.
    let realm = world.create_realm("commons").unwrap();
    let law = ruleset("commons-v1");
    world.list_ruleset(&realm.id, law).unwrap();
    let inst_1 = world.open_instance(&realm.id, "room-a").unwrap();
    let inst_2 = world.open_instance(&realm.id, "room-b").unwrap();

    let r1 = world
        .play(
            discord,
            inst_1.id,
            law,
            realm_model::instance::field::RESULT,
            7,
        )
        .unwrap();
    let r2 = world
        .play(web, inst_2.id, law, realm_model::instance::field::RESULT, 9)
        .unwrap();
    assert_eq!(
        r1.actor_identity, me.id,
        "instance-1 turn attributed to canonical id"
    );
    assert_eq!(
        r2.actor_identity, me.id,
        "instance-2 turn attributed to canonical id"
    );
    assert_eq!(
        r1.actor_identity, r2.actor_identity,
        "cross-instance, cross-surface: one durable principal"
    );
}

/// §9.2 — the catalog is committed law: an unlisted ruleset_root is refused; a
/// listed one admitted. Canary: unlist a listed root -> refused (non-vacuous).
#[test]
fn catalog_is_committed_law() {
    let mut world = RealmWorld::new();

    let player = world.mint_identity("caller", "seed-caller").unwrap();
    let actor = SurfaceRef::new(Surface::Web, "caller-sess");
    world.bind_surface(&player, actor.clone()).unwrap();

    let realm = world.create_realm("lawful-realm").unwrap();
    let inst = world.open_instance(&realm.id, "match-1").unwrap();

    let listed = ruleset("approved-law-v1");
    let unlisted = ruleset("rogue-law-v1");

    // Only `listed` is committed as active law.
    world.list_ruleset(&realm.id, listed).unwrap();
    assert!(world.is_listed(&realm.id, &listed));
    assert!(!world.is_listed(&realm.id, &unlisted));

    let mk = |root: RulesetRoot| RealmTurn {
        actor: actor.clone(),
        instance: inst.id,
        ruleset_root: root,
        effects: vec![Effect::SetField {
            cell: inst.id,
            index: realm_model::instance::field::RESULT,
            value: pack_u64(1),
        }],
    };

    // A turn citing the UNLISTED root is REFUSED — committed law, not host config.
    let refused = world.admit(mk(unlisted));
    assert!(
        matches!(
            refused,
            Err(Refused::RulesetNotInCatalog { ruleset_root, .. }) if ruleset_root == unlisted
        ),
        "unlisted ruleset_root refused; got {refused:?}"
    );
    // ...and it committed NOTHING.
    assert_eq!(
        world.instance_result(&inst.id),
        0,
        "refused turn changed no state"
    );

    // A turn citing the LISTED root is ADMITTED, and its receipt COMMITS the root.
    let ok = world.admit(mk(listed)).expect("listed ruleset admitted");
    assert_eq!(
        ok.ruleset_root, listed,
        "the receipt commits the cited law (§9.2)"
    );
    assert_eq!(
        world.instance_result(&inst.id),
        1,
        "admitted turn committed"
    );

    // CANARY — unlist the previously-listed root; the SAME turn is now refused.
    // Proves the gate reads live committed catalog state, not a compile-time set.
    world.unlist_ruleset(&realm.id, listed).unwrap();
    assert!(
        !world.is_listed(&realm.id, &listed),
        "root no longer active law"
    );
    let after_unlist = world.admit(mk(listed));
    assert!(
        matches!(after_unlist, Err(Refused::RulesetNotInCatalog { .. })),
        "unlisting a root refuses future turns citing it (canary); got {after_unlist:?}"
    );
}

/// The membrane: an ordinary in-instance turn may NOT reach the durable realm
/// cell — only the settle path crosses back. (The §9.4 "what persists vs what
/// resets" boundary, enforced.)
#[test]
fn instance_scope_membrane_holds() {
    let mut world = RealmWorld::new();
    let player = world.mint_identity("m", "seed-m").unwrap();
    let actor = SurfaceRef::new(Surface::Native, "m-local");
    world.bind_surface(&player, actor.clone()).unwrap();

    let realm = world.create_realm("membrane-realm").unwrap();
    let law = ruleset("law");
    world.list_ruleset(&realm.id, law).unwrap();
    let inst = world.open_instance(&realm.id, "s1").unwrap();

    // A turn trying to write the REALM cell directly (bypassing settle) is refused.
    let reach = world.admit(RealmTurn {
        actor: actor.clone(),
        instance: inst.id,
        ruleset_root: law,
        effects: vec![Effect::SetField {
            cell: realm.id,
            index: realm_model::realm::field::HOARD,
            value: pack_u64(1_000_000),
        }],
    });
    assert!(
        matches!(reach, Err(Refused::OutsideInstanceScope { .. })),
        "an in-instance turn cannot forge the durable realm hoard; got {reach:?}"
    );
    assert_eq!(
        world.realm_hoard(&realm.id),
        0,
        "realm hoard untouched by the refused reach"
    );
}
