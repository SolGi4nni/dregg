//! Integration tests for the DATA-DRIVEN faction layer: an N-faction [`Roster`] generates the
//! same real executor teeth the inline feud proves, the canonical [`FactionStanding`] reader is
//! what a gate reads, standing persists across a save/load (the `WriteOnce` seal survives), and
//! the standing surface renders as a `deos_view::ViewNode`.

use deos_view::ViewNode;
use dregg_app_framework::{Effect, StateConstraint, field_from_u64};
use dreggnet_faction::roster::{
    FactionDef, LINES_PER_FACTION, betrayed_var, ceiling_var, quest_var, rep_var,
};
use dreggnet_faction::standing::{StandingSnapshot, StandingStore, read_standing};
use dreggnet_faction::surface::{standing_bars, standing_bars_of};
use dreggnet_faction::{
    ROOM_HALL, Roster, case_constraints, choice_at, hall_method, slot_case_constraints,
};
use spween::Scene;
use spween_dregg::{WorldCell, WorldError};

/// A three-faction roster: two rivals (embers/tide) + one unaligned (grove, no rival cap).
fn tri_roster() -> Roster {
    Roster {
        id: "tri-feud".to_string(),
        title: "The Three Banners".to_string(),
        intro: "Three banners hang over the gate.".to_string(),
        factions: vec![
            FactionDef::new(
                "embers",
                "the Embers",
                "The eternal flame names you kin.",
                Some("tide"),
            ),
            FactionDef::new(
                "tide",
                "the Tide",
                "The grey wave draws back for you.",
                Some("embers"),
            ),
            FactionDef::new(
                "grove",
                "the Grove",
                "The wardens of the wood keep no rival.",
                None,
            ),
        ],
    }
}

fn commit(world: &WorldCell, scene: &Scene, index: usize) {
    let choice = choice_at(scene, ROOM_HALL, index);
    world
        .apply_choice(ROOM_HALL, index, &choice)
        .unwrap_or_else(|e| panic!("hall line {index} should commit: {e}"));
}

fn try_apply(world: &WorldCell, scene: &Scene, index: usize) -> Result<(), WorldError> {
    let choice = choice_at(scene, ROOM_HALL, index);
    world.apply_choice(ROOM_HALL, index, &choice).map(|_| ())
}

#[test]
fn roster_validates_and_rejects_a_dangling_rival() {
    assert!(Roster::ashenmoor().validate().is_ok());
    assert!(tri_roster().validate().is_ok());

    let bad = Roster {
        id: "bad".to_string(),
        title: "Bad".to_string(),
        intro: String::new(),
        factions: vec![FactionDef::new("a", "A", "", Some("ghost"))],
    };
    assert!(
        bad.validate().is_err(),
        "a rival that is not in the roster is rejected"
    );

    let dup = Roster {
        id: "dup".to_string(),
        title: "Dup".to_string(),
        intro: String::new(),
        factions: vec![
            FactionDef::new("a", "A", "", None),
            FactionDef::new("a", "A2", "", None),
        ],
    };
    assert!(dup.validate().is_err(), "duplicate keys are rejected");
}

/// The generated program carries the SAME real teeth per faction — Monotonic rep, the
/// FieldGte threshold gate, the FieldEquals betrayal seal + WriteOnce unlock, and (for a rivaled
/// faction) the cross-slot FieldLteOther ceiling cap. Data in, real kernel predicates out.
#[test]
fn generated_teeth_are_real_per_faction() {
    let roster = tri_roster();
    let story = roster.compile();

    // Line layout is contiguous per faction.
    assert_eq!(roster.lines("tide").pledge, LINES_PER_FACTION);
    assert_eq!(roster.lines("grove").pledge, 2 * LINES_PER_FACTION);

    for f in &roster.factions {
        let lines = roster.lines(&f.key);
        let rep = *story.var_slots.get(&rep_var(&f.key)).unwrap() as u8;
        let quest = *story.var_slots.get(&quest_var(&f.key)).unwrap() as u8;
        let betrayed = *story.var_slots.get(&betrayed_var(&f.key)).unwrap() as u8;

        let pledge = case_constraints(&story, &hall_method(lines.pledge));
        assert!(
            pledge
                .iter()
                .any(|c| matches!(c, StateConstraint::Monotonic { index } if *index == rep)),
            "{}: pledge carries Monotonic(rep); got {pledge:?}",
            f.key
        );

        // The cross-slot ceiling cap — present exactly for a rivaled faction.
        let ceiling = *story.var_slots.get(&ceiling_var(&f.key)).unwrap() as u8;
        let has_cap = pledge.iter().any(|c| matches!(c,
            StateConstraint::FieldLteOther { index, other, .. } if *index == rep && *other == ceiling));
        assert!(
            has_cap,
            "{}: pledge gated by cross-slot FieldLteOther(rep <= ceiling); got {pledge:?}",
            f.key
        );

        let trial = case_constraints(&story, &hall_method(lines.trial));
        assert!(
            trial.iter().any(|c| matches!(c,
                StateConstraint::FieldGte { index, value } if *index == rep && *value == field_from_u64(f.threshold))),
            "{}: trial gated FieldGte(rep, threshold); got {trial:?}",
            f.key
        );
        assert!(
            trial.iter().any(|c| matches!(c,
                StateConstraint::FieldEquals { index, value } if *index == betrayed && *value == field_from_u64(0))),
            "{}: trial sealed by FieldEquals(betrayed, 0); got {trial:?}",
            f.key
        );
        assert!(
            trial
                .iter()
                .any(|c| matches!(c, StateConstraint::WriteOnce { index } if *index == quest)),
            "{}: trial unlock is WriteOnce(quest); got {trial:?}",
            f.key
        );

        let betray = case_constraints(&story, &hall_method(lines.betray));
        assert!(
            betray
                .iter()
                .any(|c| matches!(c, StateConstraint::WriteOnce { index } if *index == betrayed)),
            "{}: betrayal is WriteOnce(betrayed); got {betray:?}",
            f.key
        );

        // THE SLOT-BOUND TEETH — bound to the WRITE, not the authoring method (the shape a
        // stapled write would otherwise slip). These come from the SAME shared author the inline
        // feud calls, so the deployed roster carries them per faction, per this faction's
        // `threshold` — not `crate::REP_THRESHOLD`.
        let unlock = slot_case_constraints(&story, quest);
        assert!(
            unlock.iter().any(|c| matches!(c,
                StateConstraint::FieldGte { index, value } if *index == rep && *value == field_from_u64(f.threshold))),
            "{}: SlotChanged(quest) carries FieldGte(rep, threshold={}); got {unlock:?}",
            f.key,
            f.threshold
        );
        assert!(
            unlock
                .iter()
                .any(|c| matches!(c, StateConstraint::WriteOnce { index } if *index == quest)),
            "{}: SlotChanged(quest) is WriteOnce(quest); got {unlock:?}",
            f.key
        );
        let ratchet = slot_case_constraints(&story, rep);
        assert!(
            ratchet
                .iter()
                .any(|c| matches!(c, StateConstraint::Monotonic { index } if *index == rep)),
            "{}: SlotChanged(rep) carries Monotonic(rep); got {ratchet:?}",
            f.key
        );
        let seal = slot_case_constraints(&story, betrayed);
        assert!(
            seal.iter()
                .any(|c| matches!(c, StateConstraint::WriteOnce { index } if *index == betrayed)),
            "{}: SlotChanged(betrayed) is WriteOnce(betrayed); got {seal:?}",
            f.key
        );
    }
}

/// THE DRIVEN FALSIFIER (ported from the inline feud to the DEPLOYED roster): an unlock write
/// STAPLED onto a pledge cannot claim the trial reward below the standing bar — on the program a
/// consumer actually deploys via [`Roster::deploy`]. Run against a rivaled faction (embers) and,
/// via [`tri_roster`], the unaligned (`rival: None`) grove.
///
/// Before the shared slot-bound teeth were installed on `Roster::compile`, the trial's
/// `FieldGte(rep, threshold)` was compiled ONLY onto the trial's `MethodIs` case, so a stapled
/// `SetField(<key>_quest, 1)` onto a pledge unlocked the content with `rep < threshold` — a live
/// hole on the deployed roster (the feud's tested twin had the teeth; the roster did not).
#[test]
fn a_stapled_roster_unlock_cannot_ride_a_pledge() {
    fn check(roster: &Roster, key: &str, seed: u8) {
        let scene = roster.scene();
        let story = roster.compile();
        let world = roster.deploy(seed);
        let cell = world.cell_id();
        let lines = roster.lines(key);
        let f = roster.faction(key).unwrap();
        let rep = *story.var_slots.get(&rep_var(key)).unwrap() as u8;
        let quest = *story.var_slots.get(&quest_var(key)).unwrap() as u8;

        // Staple the unlock onto a first pledge (rep 0 -> 1), below the threshold.
        let staple = world.apply_raw(
            &hall_method(lines.pledge),
            vec![
                Effect::SetField {
                    cell,
                    index: rep as usize,
                    value: field_from_u64(1),
                },
                Effect::SetField {
                    cell,
                    index: quest as usize,
                    value: field_from_u64(1),
                },
            ],
        );
        assert!(
            matches!(staple, Err(WorldError::Refused(_))),
            "{key}: a stapled unlock on a pledge (rep 1 < threshold {}) must be REFUSED; got {staple:?}",
            f.threshold
        );
        assert_eq!(
            world.read_var(&quest_var(key)),
            0,
            "{key}: anti-ghost — no forged unlock"
        );

        // THE GATE IS A BAR, NOT A BAN: earned standing still clears the trial.
        for _ in 0..f.threshold {
            commit(&world, &scene, lines.pledge);
        }
        assert_eq!(
            world.read_var(&rep_var(key)),
            f.threshold,
            "{key}: standing earned"
        );
        commit(&world, &scene, lines.trial);
        assert_eq!(
            world.read_var(&quest_var(key)),
            1,
            "{key}: earned standing still unlocks the trial"
        );
    }

    check(&Roster::ashenmoor(), "embers", 41);
    // The unaligned (rival: None) faction exercises the no-ceiling path.
    check(&tri_roster(), "grove", 43);
}

/// THE DRIVEN RATCHET FALSIFIER (ported to the deployed roster): a `rep` write-DOWN stapled onto a
/// NON-pledge method (a betrayal) is refused — earned standing is never un-earned, whoever authored
/// the change. Without the shared `SlotChanged(rep)` ratchet on `Roster::compile`, the `Monotonic`
/// bound only to the pledge/renounce `MethodIs` cases and a stapled write-down escaped it.
#[test]
fn a_roster_rep_write_down_cannot_ride_a_nonpledge_method() {
    let roster = tri_roster();
    let scene = roster.scene();
    let story = roster.compile();
    let world = roster.deploy(42);
    let cell = world.cell_id();
    let el = roster.lines("embers");
    let rep = *story.var_slots.get(&rep_var("embers")).unwrap() as u8;

    // Earn standing (two pledges -> rep 2).
    commit(&world, &scene, el.pledge);
    commit(&world, &scene, el.pledge);
    assert_eq!(world.read_var("rep_embers"), 2, "standing earned");

    // Staple a write-DOWN onto a betrayal turn (its case constrains only the betrayal slot).
    let write_down = world.apply_raw(
        &hall_method(el.betray),
        vec![Effect::SetField {
            cell,
            index: rep as usize,
            value: field_from_u64(0),
        }],
    );
    assert!(
        matches!(write_down, Err(WorldError::Refused(_))),
        "a rep write-down (2 -> 0) stapled onto a betrayal must be REFUSED; got {write_down:?}"
    );
    assert_eq!(
        world.read_var("rep_embers"),
        2,
        "anti-ghost: the standing stands"
    );
}

/// Standing accrues per faction and the canonical reader reflects it; the threshold gate, the
/// cross-slot rival cap, and the betrayal seal are all executor-refereed on the generated world
/// (non-vacuous, driven both ways).
///
/// The Embers and the Tide are RIVALS, so the standing you can hold with each is coupled: every
/// Ember pledge decrements `tide_ceiling`. Reaching the Embers threshold (rep 2) therefore lowers
/// the Tide's ceiling to 1 — below the Tide's own threshold — so the two rivals cannot BOTH be
/// maxed on one world. That is the feud, and the executor enforces it. The betrayal-seal leg
/// therefore runs on the UNALIGNED Grove (no rival, never capped), the only faction that can reach
/// qualifying standing here and so make "the seal beats the standing bar" a NON-vacuous claim.
#[test]
fn standing_accrues_gates_and_seals_on_the_generated_world() {
    let roster = tri_roster();
    let scene = roster.scene();
    let world = roster.deploy(20);
    let embers = roster.faction("embers").unwrap();
    let el = roster.lines("embers");

    // Below threshold: the trial is refused (anti-ghost) and the reader agrees.
    assert!(!read_standing(&world, embers).content_available());
    assert!(matches!(
        try_apply(&world, &scene, el.trial),
        Err(WorldError::Refused(_))
    ));

    // Two pledges clear the threshold; the reader now says content is available.
    commit(&world, &scene, el.pledge);
    commit(&world, &scene, el.pledge);
    let st = read_standing(&world, embers);
    assert_eq!(st.rep, 2);
    assert!(st.content_available(), "standing cleared the threshold");
    assert_eq!(st.label(), "trusted");

    // The trial now commits; the reader flips to unlocked.
    commit(&world, &scene, el.trial);
    assert!(read_standing(&world, embers).unlocked);

    // THE RIVAL CAP BITES (driven, non-vacuous): pledging the Embers to rep 2 lowered the Tide's
    // ceiling from TRUST_CEILING to 1 (each Ember pledge decrements `tide_ceiling`). The Tide will
    // still take you to rep 1 — but the SECOND Tide pledge, which would push `rep_tide` to 2 over
    // its now-lowered ceiling of 1, is REFUSED by the cross-slot FieldLteOther(rep_tide <=
    // tide_ceiling). Rivals cannot BOTH be maxed on one world.
    let tl = roster.lines("tide");
    assert_eq!(
        world.read_var(&ceiling_var("tide")),
        1,
        "the Embers pledges lowered the rival Tide ceiling to 1"
    );
    commit(&world, &scene, tl.pledge); // rep_tide 0 -> 1, within the lowered ceiling
    assert_eq!(
        world.read_var(&rep_var("tide")),
        1,
        "the Tide takes you to rep 1"
    );
    let capped = try_apply(&world, &scene, tl.pledge); // rep_tide 1 -> 2 would break the cap
    assert!(
        matches!(capped, Err(WorldError::Refused(_))),
        "the rival cap bites: a Tide pledge past the Embers-lowered ceiling is refused; got {capped:?}"
    );
    assert_eq!(
        world.read_var(&rep_var("tide")),
        1,
        "anti-ghost: the refused pledge did not raise standing"
    );

    // Betray the UNALIGNED Grove (no rival, so never capped) AT qualifying standing → its content
    // seals DESPITE the standing (the seal beats the bar — non-vacuous: the Grove really did reach
    // available content first).
    let grove = roster.faction("grove").unwrap();
    let gl = roster.lines("grove");
    commit(&world, &scene, gl.pledge);
    commit(&world, &scene, gl.pledge);
    let gs = read_standing(&world, grove);
    assert_eq!(gs.rep, 2);
    assert!(
        gs.content_available(),
        "the unaligned Grove reached qualifying standing, uncapped"
    );
    commit(&world, &scene, gl.betray);
    let gs = read_standing(&world, grove);
    assert!(gs.betrayed);
    assert!(
        !gs.content_available(),
        "a betrayed faction seals despite standing"
    );
    assert!(matches!(
        try_apply(&world, &scene, gl.trial),
        Err(WorldError::Refused(_))
    ));
}

/// The cross-faction cap bites for a rivaled pair but an UNALIGNED faction is never capped —
/// the data-driven rival relationship is real.
#[test]
fn rival_pair_caps_but_unaligned_faction_does_not() {
    let roster = tri_roster();
    let scene = roster.scene();
    let world = roster.deploy(21);
    let el = roster.lines("embers");
    let tl = roster.lines("tide");
    let gl = roster.lines("grove");

    // Pledge the Embers to the hilt — drops tide_ceiling to 0.
    for _ in 0..roster.faction("embers").unwrap().trust_ceiling {
        commit(&world, &scene, el.pledge);
    }
    assert_eq!(
        world.read_var(&ceiling_var("tide")),
        0,
        "rival ceiling capped"
    );

    // The Tide pledge is now refused (the cross-slot cap bites).
    assert!(matches!(
        try_apply(&world, &scene, tl.pledge),
        Err(WorldError::Refused(_))
    ));
    assert_eq!(
        world.read_var(&rep_var("tide")),
        0,
        "the rival will not have you"
    );

    // The Grove has no rival, so no Ember pledge ever capped it — it still accepts a pledge.
    commit(&world, &scene, gl.pledge);
    assert_eq!(
        world.read_var(&rep_var("grove")),
        1,
        "the unaligned faction is uncapped"
    );
}

/// Standing PERSISTS per-identity: capture → JSON → reload → restore rebuilds the world at the
/// saved standing, and the reinstated WriteOnce seal still bites (a betrayed faction stays sealed
/// across a save/load — persistence is real, not decorative).
#[test]
fn standing_persists_across_a_save_and_load() {
    let roster = tri_roster();
    let scene = roster.scene();

    // Earn: pledge Embers to threshold + unlock the trial; pledge then betray the Tide.
    let world = roster.deploy(22);
    let el = roster.lines("embers");
    let tl = roster.lines("tide");
    commit(&world, &scene, el.pledge);
    commit(&world, &scene, el.pledge);
    commit(&world, &scene, el.trial);
    commit(&world, &scene, tl.pledge);
    commit(&world, &scene, tl.betray);

    // Persist under an identity, round-trip the whole store through JSON.
    let mut store = StandingStore::new();
    store.record_world("player:ember", &world, &roster);
    let json = store.to_json();
    let reloaded = StandingStore::from_json(&json).expect("store parses");
    let snap = reloaded.get("player:ember").expect("identity persisted");
    assert_eq!(snap.roster_id, roster.id);

    // Restore onto a FRESH world (different seed) — the standing reinstates.
    let restored = snap
        .restore(&roster, 99)
        .expect("restore matches the roster");
    let embers = roster.faction("embers").unwrap();
    let tide = roster.faction("tide").unwrap();
    assert_eq!(
        read_standing(&restored, embers),
        *snap.faction("embers").unwrap()
    );
    assert!(
        read_standing(&restored, embers).unlocked,
        "the unlock persisted"
    );
    assert!(
        read_standing(&restored, tide).betrayed,
        "the betrayal persisted"
    );

    // THE TEETH SURVIVE: the restored Tide trial is refused (the seal bites in the new world),
    // and a recant cannot un-set the reinstated WriteOnce betrayal.
    assert!(matches!(
        try_apply(&restored, &scene, tl.trial),
        Err(WorldError::Refused(_))
    ));
    assert!(matches!(
        try_apply(&restored, &scene, tl.recant),
        Err(WorldError::Refused(_))
    ));

    // A snapshot is not portable to a different roster (the slots would not line up).
    assert!(snap.restore(&Roster::ashenmoor(), 1).is_err());
}

/// The standing surface renders as a real `deos_view::ViewNode` — a section of one bar per faction
/// (the do-once read-surface).
#[test]
fn standing_surface_renders_a_bar_per_faction() {
    let roster = tri_roster();
    let scene = roster.scene();
    let world = roster.deploy(23);
    commit(&world, &scene, roster.lines("embers").pledge);

    let node = standing_bars(&world, &roster);
    let ViewNode::Section {
        title, children, ..
    } = &node
    else {
        panic!("the standing surface is a Section; got {node:?}");
    };
    assert!(title.contains("Standing"));
    let [ViewNode::Table(rows)] = children.as_slice() else {
        panic!("the section holds a table of standing rows");
    };
    assert_eq!(rows.len(), roster.factions.len(), "one bar per faction");

    // Each row carries a Progress bar (the standing bar).
    for row in rows {
        let ViewNode::Row(cells) = row else {
            panic!("a standing row is a Row");
        };
        assert!(
            cells.iter().any(|c| matches!(c, ViewNode::Progress { .. })),
            "a standing row carries a Progress bar; got {cells:?}"
        );
    }

    // The direct constructor renders too (the render-only path a frontend calls).
    let direct = standing_bars_of(
        &dreggnet_faction::standing::read_all(&world, &roster),
        "Standing",
    );
    assert!(matches!(direct, ViewNode::Section { .. }));
}
