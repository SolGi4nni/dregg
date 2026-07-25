use dreggnet_party::Role;
use dreggnet_party::encounter::{EncounterError, MAX_ENCOUNTER_EVENTS, PartyArenaEncounter};
use dreggnet_party::lobby::PartyLobby;
use dungeon_on_dregg::combat::{Arena, WARDEN, is_hero};

/// The host-private custody root a resume needs. A host that persists an `EncounterRecord`
/// stores this beside it in its OWN storage — it is key material and never enters the record.
fn host_root(encounter: &PartyArenaEncounter) -> [u8; 32] {
    encounter
        .custody_root()
        .expect("a locally-custodied party carries its custody root")
}

fn roster() -> [String; 4] {
    ["alice", "bob", "cara", "devi"].map(str::to_string)
}

fn hero_first_seed() -> u8 {
    (0..=u8::MAX)
        .find(|seed| is_hero(Arena::deploy(*seed).active()))
        .expect("some deterministic Arena seed starts with a hero")
}

fn launch_live_party(seed: u8) -> PartyArenaEncounter {
    let roster = roster();
    let mut lobby = PartyLobby::new("gate-assault", "alice").expect("live lobby");
    for (role, identity) in Role::ALL.into_iter().zip(roster.iter()) {
        lobby.claim(identity.as_str(), role).expect("claim role");
        lobby
            .set_ready(identity.as_str(), true)
            .expect("ready role");
    }
    let launch = lobby.launch("alice").expect("ready leader launches");
    assert!(launch.receipt.launched);
    PartyArenaEncounter::from_party(launch.party, "alice", seed)
        .expect("the launched capability-seated party enters the Arena")
}

fn resolve_warden(encounter: &mut PartyArenaEncounter) {
    encounter.vote("alice", 0).expect("tank ballot");
    encounter.vote("bob", 0).expect("scout ballot");
    encounter
        .vote("cara", 0)
        .expect("mage ballot reaches quorum");
    encounter.resolve("alice").expect("leader resolves quorum");
    assert_eq!(encounter.target(), Some(WARDEN));
}

#[test]
fn signed_fork_and_role_cap_receipts_authorize_a_real_arena_turn_and_resume() {
    let seed = hero_first_seed();
    let mut encounter = launch_live_party(seed);
    let genesis_root = encounter.root();

    // An outsider cannot manufacture a signed party ballot, and the refusal is
    // anti-ghost at the encounter boundary.
    assert!(matches!(
        encounter.vote("mallory", 0),
        Err(EncounterError::Unseated(actor)) if actor == "mallory"
    ));
    assert_eq!(encounter.root(), genesis_root);
    assert_eq!(encounter.revision(), 0);

    encounter.vote("alice", 0).expect("tank ballot");
    encounter.vote("bob", 0).expect("scout ballot");
    let before_subquorum = encounter.root();
    assert!(matches!(
        encounter.resolve("alice"),
        Err(EncounterError::ForkRefused(reason)) if reason.contains("quorum")
    ));
    assert_eq!(
        encounter.root(),
        before_subquorum,
        "sub-quorum is anti-ghost"
    );

    let ballot = encounter.vote("cara", 0).expect("mage ballot");
    assert_eq!(
        ballot
            .ballot
            .as_ref()
            .map(|ballot| ballot.signature.0.len()),
        Some(64),
        "the exact custody-signed ballot is retained"
    );
    assert!(
        ballot
            .vote_receipt
            .as_ref()
            .is_some_and(|receipt| receipt.turn_hash != [0u8; 32]),
        "the real vote-engine turn receipt is retained too"
    );
    let before_nonleader = encounter.root();
    assert!(matches!(
        encounter.resolve("bob"),
        Err(EncounterError::LeaderOnly)
    ));
    assert_eq!(encounter.root(), before_nonleader);

    let resolution = encounter.resolve("alice").expect("leader resolves quorum");
    assert_eq!(resolution.target, Some(WARDEN));
    assert_eq!(
        resolution
            .party_receipt
            .as_ref()
            .and_then(|receipt| receipt.executor_signature.as_ref())
            .map(Vec::len),
        Some(64),
        "the certified fork's party-world transition is executor-signed"
    );

    // Alice is the Tank but asks to fire the Scout's tactic. There is no
    // application-level role mirror: the forged move reaches the real party
    // world and its missing capability refuses it before Arena state changes.
    let arena_before_forge = encounter.arena().world.snapshot();
    let root_before_forge = encounter.root();
    assert!(matches!(
        encounter.contribute("alice", Role::Scout),
        Err(EncounterError::PartyRefused(reason)) if reason.to_ascii_lowercase().contains("cap")
    ));
    assert_eq!(encounter.arena().world.snapshot(), arena_before_forge);
    assert_eq!(encounter.root(), root_before_forge);

    // The identical Scout tactic by the actual Scout lands its capability turn,
    // then mechanically damages the quorum-selected Warden in the real Arena.
    let hp_before = encounter.arena().hp(WARDEN);
    let event = encounter
        .contribute("bob", Role::Scout)
        .expect("the Scout's authorized strike lands")
        .clone();
    assert!(encounter.arena().hp(WARDEN) < hp_before);
    assert_eq!(event.target, Some(WARDEN));
    for receipt in [&event.party_receipt, &event.arena_receipt] {
        let receipt = receipt.as_ref().expect("both complete turns are retained");
        assert_ne!(receipt.turn_hash, [0u8; 32]);
        assert_ne!(receipt.pre_state_hash, receipt.post_state_hash);
    }
    assert_ne!(
        event.party_receipt.as_ref().unwrap().turn_hash,
        event.arena_receipt.as_ref().unwrap().turn_hash
    );

    // Once-per-encounter WriteOnce is not a UI dim: replaying Bob's role reaches
    // the party executor, refuses, and cannot produce a second Arena strike.
    let after_first = encounter.arena().world.snapshot();
    let root_after_first = encounter.root();
    assert!(matches!(
        encounter.contribute("bob", Role::Scout),
        Err(EncounterError::PartyRefused(reason)) if reason.to_ascii_lowercase().contains("write-once")
    ));
    assert_eq!(encounter.arena().world.snapshot(), after_first);
    assert_eq!(encounter.root(), root_after_first);

    // Restart re-drives all three engines and can continue from the exact state.
    let record = encounter.export_record();
    let mut resumed = PartyArenaEncounter::resume(&record, host_root(&encounter))
        .expect("semantic replay resumes");
    assert_eq!(resumed.root(), encounter.root());
    assert_eq!(
        resumed.arena().world.snapshot(),
        encounter.arena().world.snapshot()
    );
    assert_eq!(
        resumed.party().read_field(resumed.party().layout().gate, 0),
        encounter
            .party()
            .read_field(encounter.party().layout().gate, 0)
    );
    assert_eq!(
        resumed.party().read_field(resumed.party().layout().lock, 0),
        encounter
            .party()
            .read_field(encounter.party().layout().lock, 0)
    );

    if is_hero(resumed.arena().active()) {
        let role = if resumed.party().seat_index_for("alice").is_some() {
            Role::Tank
        } else {
            unreachable!()
        };
        resumed
            .contribute("alice", role)
            .expect("a resumed hero turn continues");
    } else {
        resumed
            .advance_enemy("alice")
            .expect("a resumed enemy turn continues");
    }
    assert_eq!(resumed.revision(), record.events.len() as u64 + 1);
}

#[test]
fn replay_refuses_receipt_state_actor_and_root_forgeries() {
    let seed = hero_first_seed();
    let mut encounter = PartyArenaEncounter::new(roster(), "alice", seed).expect("encounter");
    resolve_warden(&mut encounter);
    encounter
        .contribute("bob", Role::Scout)
        .expect("authorized Arena strike");
    let authentic = encounter.export_record();
    PartyArenaEncounter::resume(&authentic, host_root(&encounter))
        .expect("authentic record replays");
    PartyArenaEncounter::resume_at(
        &authentic,
        host_root(&encounter),
        encounter.revision(),
        encounter.root(),
    )
    .expect("the authentic latest anchor resumes");

    let mut forged_receipt = authentic.clone();
    forged_receipt
        .events
        .last_mut()
        .unwrap()
        .arena_receipt
        .as_mut()
        .unwrap()
        .post_state_hash[0] ^= 1;
    assert!(matches!(
        PartyArenaEncounter::resume(&forged_receipt, host_root(&encounter)),
        Err(EncounterError::ReplayDiverged { detail, .. }) if detail.contains("root")
    ));

    let mut forged_state = authentic.clone();
    forged_state.events.last_mut().unwrap().arena_state[0] ^= 1;
    assert!(matches!(
        PartyArenaEncounter::resume(&forged_state, host_root(&encounter)),
        Err(EncounterError::ReplayDiverged { detail, .. }) if detail.contains("root")
    ));

    let mut forged_actor = authentic.clone();
    let last = forged_actor.events.last_mut().unwrap();
    if let dreggnet_party::encounter::EncounterCommand::Contribute { actor, .. } = &mut last.command
    {
        *actor = "alice".to_string();
    } else {
        panic!("last event is the contribution");
    }
    assert!(matches!(
        PartyArenaEncounter::resume(&forged_actor, host_root(&encounter)),
        Err(EncounterError::ReplayDiverged { .. })
    ));

    let mut forged_root = authentic.clone();
    forged_root.events.last_mut().unwrap().root[0] ^= 1;
    assert!(matches!(
        PartyArenaEncounter::resume(&forged_root, host_root(&encounter)),
        Err(EncounterError::ReplayDiverged { detail, .. }) if detail.contains("root")
    ));

    let mut forged_ballot = authentic.clone();
    forged_ballot.events[0].ballot.as_mut().unwrap().signature.0[0] ^= 1;
    assert!(matches!(
        PartyArenaEncounter::resume(&forged_ballot, host_root(&encounter)),
        Err(EncounterError::ReplayDiverged { detail, .. }) if detail.contains("root")
    ));

    let mut forged_vote_receipt = authentic.clone();
    forged_vote_receipt.events[0]
        .vote_receipt
        .as_mut()
        .unwrap()
        .post_state_hash[0] ^= 1;
    assert!(matches!(
        PartyArenaEncounter::resume(&forged_vote_receipt, host_root(&encounter)),
        Err(EncounterError::ReplayDiverged { detail, .. }) if detail.contains("root")
    ));

    let mut truncated = authentic.clone();
    truncated.events.pop();
    PartyArenaEncounter::resume(&truncated, host_root(&encounter))
        .expect("a valid prefix is semantically valid");
    assert!(matches!(
        PartyArenaEncounter::resume_at(&truncated, host_root(&encounter), encounter.revision(), encounter.root()),
        Err(EncounterError::InvalidRecord(reason)) if reason.contains("anchored latest")
    ));
}

#[test]
fn event_bound_is_part_of_restart_validation() {
    let seed = hero_first_seed();
    let encounter = PartyArenaEncounter::new(roster(), "alice", seed).expect("encounter");
    let mut record = encounter.export_record();
    // The specific event bodies do not matter: the size gate fires before replay.
    let sample = {
        let mut source = PartyArenaEncounter::new(roster(), "alice", seed).unwrap();
        source.vote("alice", 0).unwrap().clone()
    };
    record.events = vec![sample; MAX_ENCOUNTER_EVENTS + 1];
    assert!(matches!(
        PartyArenaEncounter::resume(&record, host_root(&encounter)),
        Err(EncounterError::InvalidRecord(reason)) if reason.contains("exceeds")
    ));
}
