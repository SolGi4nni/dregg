use dungeon_on_dregg::campaign::{
    CampaignAction, CampaignConfig, CampaignError, CampaignRecord, CampaignSession, DescentAction,
    RelicState, RelicUse, bound_campaign_narration, bound_relic_context,
};
use dungeon_on_dregg::progression::MAGE;

const CROWNED_LINE: [DescentAction; 18] = [
    DescentAction::Delve,
    DescentAction::Smite,
    DescentAction::Loot { relic: 1 },
    DescentAction::Unlock { way: 2 },
    DescentAction::Delve,
    DescentAction::Smite,
    DescentAction::Loot { relic: 2 },
    DescentAction::Unlock { way: 3 },
    DescentAction::Delve,
    DescentAction::Smite,
    DescentAction::Smite,
    DescentAction::Loot { relic: 3 },
    DescentAction::Unlock { way: 4 },
    DescentAction::Delve,
    DescentAction::Smite,
    DescentAction::Smite,
    DescentAction::Loot { relic: 0 },
    DescentAction::Flee,
];

fn open(seed: u8) -> CampaignSession {
    CampaignSession::open(CampaignConfig::new(seed, "cmr://hero", MAGE))
        .expect("the coherent campaign deploys")
}

fn play_crown(session: &mut CampaignSession) {
    for (index, command) in CROWNED_LINE.into_iter().enumerate() {
        let event = session
            .advance(
                CampaignAction::Descent(command),
                format!("The expedition advances through beat {index}."),
            )
            .unwrap_or_else(|error| panic!("crowned move {index} refused: {error}"));
        let primary = event.receipts.first().expect("every move has a receipt");
        assert_eq!(
            bound_campaign_narration(primary),
            Some(event.narration_commitment),
            "narration is carried by the exact Descent turn"
        );
    }
}

#[test]
fn one_campaign_persists_character_world_relics_and_bazaar_vow() {
    let mut campaign = open(41);
    let start = campaign.projection().unwrap();
    assert_eq!(start.location, "keep");
    assert_eq!(start.hero_class, MAGE);
    assert_eq!(start.hero_level, 1);
    assert_eq!(start.hero_xp, 0);
    assert_eq!(start.relics, [RelicState::Unbanked; 8]);

    play_crown(&mut campaign);
    let crowned = campaign.projection().unwrap();
    assert_eq!(crowned.cleared_locations, ["keep"]);
    assert_eq!(crowned.hero_xp, 100);
    for relic in 0..=3 {
        assert_eq!(crowned.relics[relic], RelicState::Banked);
    }

    campaign
        .advance(
            CampaignAction::LevelUp,
            "The hard-won lesson settles into practiced instinct.",
        )
        .expect("the crowned XP admits level two");
    let travel = campaign
        .advance(
            CampaignAction::Travel {
                destination: "bazaar".to_string(),
            },
            "The Crown opens the old road to the Ossuary Bazaar.",
        )
        .expect("the executor-cleared road admits travel");
    assert_eq!(
        bound_campaign_narration(&travel.receipts[0]),
        Some(travel.narration_commitment)
    );

    let use_ = RelicUse::BazaarOrder {
        market: [0xBA; 32],
        order: [0x0D; 32],
    };
    let vowed = campaign
        .advance(
            CampaignAction::BindRelic {
                relic: 0,
                use_: use_.clone(),
            },
            "The Crown is placed in escrow beneath the bone chandeliers.",
        )
        .expect("a banked relic may make one Bazaar vow");
    let grant = vowed.grant.as_ref().expect("the vow exports a grant");
    assert_eq!(grant.use_, use_);
    assert_eq!(
        grant.reliquary_receipt_hash,
        vowed.receipts[0].receipt_hash()
    );
    assert_eq!(
        bound_campaign_narration(&vowed.receipts[0]),
        Some(vowed.narration_commitment)
    );
    assert_ne!(bound_relic_context(&vowed.receipts[0]), Some([0; 32]));

    let head = campaign.projection().unwrap();
    assert_eq!(head.location, "bazaar");
    assert_eq!(head.hero_level, 2);
    assert_eq!(head.hero_xp, 100);
    assert_eq!(head.relics[0], RelicState::BazaarBound);
    assert_eq!(head.relics[1], RelicState::Banked);
    assert_eq!(head.descent_depth, 0, "travel starts a new expedition");

    let bound_head = campaign.root();
    let bound_revision = campaign.revision();
    for substituted in [
        use_.clone(),
        RelicUse::BazaarOrder {
            market: [0xBA; 32],
            order: [0x0E; 32],
        },
        RelicUse::RaidSeat {
            session: [8; 32],
            seat: 2,
        },
    ] {
        assert!(matches!(
            campaign.advance(
                CampaignAction::BindRelic {
                    relic: 0,
                    use_: substituted,
                },
                "A second claim on one relic."
            ),
            Err(CampaignError::Refused(_))
        ));
        assert_eq!(campaign.root(), bound_head, "a refusal is anti-ghost");
        assert_eq!(campaign.revision(), bound_revision);
    }

    let record = campaign.export_record().unwrap();
    let bytes = record.to_json().expect("the complete campaign is durable");
    let restored = CampaignRecord::from_json(&bytes).expect("durable bytes decode");
    assert_eq!(restored.root, campaign.root());
    assert_eq!(restored.projection, head);
}

#[test]
fn replay_and_every_progress_substitution_refuse_without_minting() {
    let mut campaign = open(73);
    let untouched = campaign.root();
    assert!(matches!(
        campaign.advance(
            CampaignAction::BindRelic {
                relic: 0,
                use_: RelicUse::RaidSeat {
                    session: [7; 32],
                    seat: 2,
                },
            },
            "A counterfeit vow."
        ),
        Err(CampaignError::Refused(_))
    ));
    assert_eq!(campaign.root(), untouched);
    assert_eq!(campaign.revision(), 0);
    assert_eq!(
        campaign.projection().unwrap().relics[0],
        RelicState::Unbanked
    );

    campaign
        .advance(
            CampaignAction::Descent(DescentAction::Delve),
            "The first step descends into the Keep.",
        )
        .expect("one real move lands");

    let authentic = campaign.export_record().unwrap();
    CampaignSession::verify(&authentic).expect("the authentic record replays");

    let mut wrong_move = authentic.clone();
    wrong_move.events[0].action = CampaignAction::Descent(DescentAction::Flee);
    assert!(CampaignSession::resume(&wrong_move).is_err());

    let mut wrong_narration = authentic.clone();
    wrong_narration.events[0].narration.push_str(" Retconned.");
    assert!(CampaignSession::resume(&wrong_narration).is_err());

    let mut wrong_receipt = authentic.clone();
    wrong_receipt.events[0].receipts[0].turn_hash[0] ^= 1;
    assert!(CampaignSession::resume(&wrong_receipt).is_err());

    let mut forged_xp = authentic.clone();
    forged_xp.projection.hero_xp += 10_000;
    assert!(CampaignSession::resume(&forged_xp).is_err());

    let mut forged_event_xp = authentic.clone();
    forged_event_xp.events[0].projection.hero_xp += 10_000;
    assert!(CampaignSession::resume(&forged_event_xp).is_err());
}

#[test]
fn terminal_without_crown_mints_no_character_world_or_relic_progress() {
    let mut campaign = open(99);
    campaign
        .advance(
            CampaignAction::Descent(DescentAction::Flee),
            "The traveller banks an empty pack and returns alive.",
        )
        .expect("an empty retreat is a lawful terminal turn");
    let settled = campaign.projection().unwrap();
    assert!(settled.descent_terminal);
    assert!(settled.cleared_locations.is_empty());
    assert_eq!(settled.hero_xp, 0);
    assert_eq!(settled.hero_level, 1);
    assert_eq!(settled.relics, [RelicState::Unbanked; 8]);

    let head = campaign.root();
    for action in [
        CampaignAction::LevelUp,
        CampaignAction::Travel {
            destination: "bazaar".to_string(),
        },
        CampaignAction::BindRelic {
            relic: 0,
            use_: RelicUse::BazaarOrder {
                market: [1; 32],
                order: [2; 32],
            },
        },
    ] {
        assert!(matches!(
            campaign.advance(action, "A progress claim without its cause."),
            Err(CampaignError::Refused(_))
        ));
        assert_eq!(campaign.root(), head);
        assert_eq!(campaign.revision(), 1);
    }

    let record = campaign.export_record().unwrap();
    CampaignSession::verify(&record).expect("the non-crowned terminal record replays exactly");
}
