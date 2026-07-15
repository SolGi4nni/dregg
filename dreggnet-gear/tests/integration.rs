//! Integration tests for `dreggnet-gear` — the cross-module flows a single unit test cannot
//! reach: the craft→gear→equip pipe end to end, a multi-slot set-bonus over a whole loadout,
//! a respec round-trip on the talent tree, and the loadout/talent Offerings driven as a
//! frontend would drive them.

use dreggnet_gear::gear::Armory;
use dreggnet_gear::multislot::MultiLoadout;
use dreggnet_gear::offering::{
    LoadoutOffering, TURN_CLAIM, TURN_EQUIP, TURN_RESPEC, TURN_USE, TalentTreeOffering,
};
use dreggnet_gear::statblock::{GearSlot, Rarity, StatBlock};
use dreggnet_gear::talents::{
    self, IRONHIDE, claim_talent_gen, generation, has_talent_gen, respec,
};
use dreggnet_gear::{Gear, Loadout};

use dreggnet_offerings::{Action, DreggIdentity, Offering, SessionConfig};

use dungeon_on_dregg::meta;
use dungeon_on_dregg::progression::{self, MAGE};

// ── 1. The craft→gear pipe, end to end ───────────────────────────────────────────────────────

/// A LEGENDARY craft of a "greatblade" recipe lowers to a Legendary WEAPON stat block, forges
/// as a real owned asset, and that forged gear EQUIPS + unlocks its cross-cell ability — the
/// full craft→gear→equip pipe, driven on the real executor.
#[test]
fn a_legendary_craft_forges_gear_that_equips() {
    // A craft outcome, in the primitive shape `dreggnet-craft` passes across the (cycle-free)
    // pipe: quality tag 3 (legendary), a weapon recipe, a top roll, a content commitment.
    let quality_tag = 3u8; // legendary
    let recipe = "forge:greatblade";
    let roll = 98u64;
    let commitment = blake3::hash(b"craft:greatblade:legendary")
        .as_bytes()
        .to_vec();

    let stats = StatBlock::from_forge(quality_tag, recipe, roll, &commitment);
    assert_eq!(
        stats.rarity,
        Rarity::Legendary,
        "legendary craft → Legendary gear"
    );
    assert_eq!(stats.slot, GearSlot::Weapon, "a greatblade forges a weapon");
    assert!(stats.might > stats.ward, "a weapon is might-forward");

    // Deterministic: the same craft outcome always lowers to the same block.
    assert_eq!(
        stats,
        StatBlock::from_forge(quality_tag, recipe, roll, &commitment)
    );

    // Forge it as owned gear + drive the equip loop.
    let mut armory = Armory::new();
    armory.pubkey_of("smith");
    let gear: Gear = armory.forge_from_craft("smith", quality_tag, recipe, roll, &commitment);
    assert_eq!(
        gear.stats, stats,
        "the forged gear carries the crafted block"
    );
    assert!(
        armory.verify_provenance(&gear).verified,
        "the crafted gear's provenance verifies"
    );

    let mut loadout = Loadout::new(armory, gear, None);
    assert!(
        loadout.gate.use_ability_honest().is_err(),
        "the crafted gear's ability is refused before equip"
    );
    loadout
        .equip("smith")
        .expect("the smith equips its crafted gear");
    loadout
        .gate
        .use_ability_honest()
        .expect("the crafted gear unlocks its cross-cell ability");
    assert!(loadout.gate.ability_unlocked());
}

/// The craft→gear pipe classifies non-weapon recipes into the right slots, and a lower quality
/// tier forges a lower rarity — the mapping is a real function of the craft outcome.
#[test]
fn the_craft_pipe_maps_slot_and_rarity() {
    let commit = vec![1, 2, 3, 4, 5, 6, 7, 8];
    let armor = StatBlock::from_forge(1, "forge:plate", 40, &commit);
    assert_eq!(armor.slot, GearSlot::Armor);
    assert_eq!(armor.rarity, Rarity::Uncommon);
    assert!(armor.ward > armor.might, "armor is ward-forward");

    let trinket = StatBlock::from_forge(2, "forge:amulet", 70, &commit);
    assert_eq!(trinket.slot, GearSlot::Trinket);
    assert_eq!(trinket.rarity, Rarity::Rare);
    assert!(trinket.guile > trinket.might, "a trinket is guile-forward");
}

// ── 2. A whole loadout's set bonus ────────────────────────────────────────────────────────────

/// A three-piece loadout (weapon + armor + trinket) fires its SET BONUS only when the WHOLE
/// set is equipped — the real multi-peer `ObservedFieldEquals` conjunction over a full loadout.
#[test]
fn a_full_loadout_fires_its_set_bonus() {
    let mut armory = Armory::new();
    armory.pubkey_of("hero");
    let mut lo = MultiLoadout::new();
    lo.equip_piece(
        GearSlot::Weapon,
        armory.forge("hero", StatBlock::weapon(Rarity::Legendary, 15, 0xF1A3E)),
    )
    .unwrap();
    lo.equip_piece(
        GearSlot::Armor,
        armory.forge("hero", StatBlock::armor(Rarity::Rare, 11, 0xA12)),
    )
    .unwrap();
    lo.equip_piece(
        GearSlot::Trinket,
        armory.forge("hero", StatBlock::trinket(Rarity::Rare, 8, 0x7)),
    )
    .unwrap();
    assert_eq!(lo.filled(), 3);

    let gate = lo.deploy_set_bonus();
    // Equip two of three → still refused.
    gate.equip(0).unwrap();
    gate.equip(1).unwrap();
    assert!(
        gate.use_set_bonus().is_err(),
        "a 2/3 loadout has no set bonus"
    );
    // The full set → the bonus fires.
    gate.equip(2).unwrap();
    gate.use_set_bonus()
        .expect("the full loadout fires the set bonus");
    assert!(gate.set_bonus_active());
}

// ── 3. A respec round-trip on the talent tree ─────────────────────────────────────────────────

/// A hero claims a talent, respecs (clearing it), and re-claims in the new generation — a full
/// respec round-trip on the real hero cell.
#[test]
fn a_respec_round_trip() {
    let world = talents::deploy_respec_hero(0x33);
    progression::choose_class(&world, MAGE).unwrap();
    progression::perish(&world).unwrap();
    meta::grant_echoes(&world, 6).unwrap(); // 40 echoes

    claim_talent_gen(&world, IRONHIDE).expect("claim Ironhide in gen 0");
    assert!(has_talent_gen(&world, IRONHIDE));
    assert_eq!(generation(&world), 0);

    respec(&world).expect("respec");
    assert_eq!(generation(&world), 1);
    assert!(!has_talent_gen(&world, IRONHIDE), "respec cleared it");

    claim_talent_gen(&world, IRONHIDE).expect("re-claim in gen 1");
    assert!(has_talent_gen(&world, IRONHIDE));
}

// ── 4. The Offerings, driven as a frontend would ──────────────────────────────────────────────

/// The loadout Offering opens, equips, and uses the ability through the generic `advance` seam
/// (the same path every frontend drives), and its render is a real `ViewNode` tree.
#[test]
fn the_loadout_offering_is_frontend_drivable() {
    let off = LoadoutOffering::new();
    let mut s = off.open(SessionConfig::with_seed(5)).expect("open");
    let who = DreggIdentity("player".into());

    assert!(
        !off.advance(&mut s, Action::new("", TURN_USE, 0, true), who.clone())
            .landed(),
        "ability refused before equip"
    );
    assert!(
        off.advance(&mut s, Action::new("", TURN_EQUIP, 0, true), who.clone())
            .landed()
    );
    assert!(
        off.advance(&mut s, Action::new("", TURN_USE, 0, true), who)
            .landed()
    );
    assert!(off.verify(&s).verified);
    // Actions surface the cap tooth: after equip+use both are disabled.
    let acts = off.actions(&s);
    assert!(
        acts.iter().all(|a| !a.enabled),
        "no further moves are enabled"
    );
}

/// The talent Offering claims + respecs through `advance`, and refuses an over-price / wrong
/// affordance — the no-P2W teeth ride into the surface unchanged.
#[test]
fn the_talent_offering_is_frontend_drivable() {
    let off = TalentTreeOffering::new();
    let mut s = off.open(SessionConfig::with_seed(1)).expect("open");
    let who = DreggIdentity("player".into());
    assert!(s.echoes() >= 30);

    // Claim Ironhide (index 0).
    assert!(
        off.advance(&mut s, Action::new("", TURN_CLAIM, 0, true), who.clone())
            .landed()
    );
    assert!(s.has(talents::TALENT_TREE[0]));

    // Respec clears it.
    assert!(
        off.advance(&mut s, Action::new("", TURN_RESPEC, 0, true), who.clone())
            .landed()
    );
    assert_eq!(s.generation(), 1);
    assert!(!s.has(talents::TALENT_TREE[0]));

    // A Warrior-only talent (index 3) is refused for this Mage.
    assert!(
        !off.advance(&mut s, Action::new("", TURN_CLAIM, 3, true), who)
            .landed()
    );
    assert!(off.verify(&s).verified);
}
