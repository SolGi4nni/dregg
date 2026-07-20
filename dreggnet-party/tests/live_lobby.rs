use dreggnet_party::lobby::{LobbyCommand, LobbyRefusal, PartyLobby};
use dreggnet_party::{PartyMove, Role};

const LEADER: &str = "player:alice";

fn ready_roster() -> PartyLobby {
    let mut lobby = PartyLobby::new("dark-bazaar:table-7", LEADER).expect("open lobby");
    for (identity, role) in [
        (LEADER, Role::Tank),
        ("player:bob", Role::Scout),
        ("player:carol", Role::Mage),
        ("player:dana", Role::Healer),
    ] {
        lobby.claim(identity, role).expect("claim distinct role");
        lobby
            .set_ready(identity, true)
            .expect("ready occupied role");
    }
    lobby
}

/// Formation is real gameplay setup: four authenticated identities claim distinct
/// roles, ready, and launch into the cap-seated party. Their chosen names survive
/// into the shared world and each role's real executor mandate still bites.
#[test]
fn ready_lobby_launches_the_real_cap_seated_party() {
    let mut lobby = ready_roster();
    assert!(lobby.ready_to_launch());
    assert_eq!(lobby.occupied_count(), 4);
    assert_eq!(lobby.ready_count(), 4);

    let launch = lobby.launch(LEADER).expect("leader launches ready roster");
    assert!(launch.receipt.launched);
    assert!(lobby.launched());
    assert_eq!(launch.party.seat_count(), 4);
    assert_eq!(launch.party.seat(0).role(), Role::Tank);
    assert_eq!(launch.party.seat(0).name(), LEADER);
    assert_eq!(launch.party.seat(1).name(), "player:bob");
    assert_eq!(launch.party.seat(2).name(), "player:carol");
    assert_eq!(launch.party.seat(3).name(), "player:dana");

    let mut party = launch.party;
    assert!(
        party.act_in_role_as(LEADER).committed(),
        "the claimed tank drives its real capability-bound move"
    );
    assert!(
        party.act_as(LEADER, PartyMove::DisarmLock).refused(),
        "the tank still cannot forge the scout's capability"
    );
    let before_focus = party.focus_spent();
    let outsider = party.act_in_role_as("spectator:eve");
    assert!(outsider.refused());
    assert!(outsider.reason().unwrap().contains("holds no party seat"));
    assert_eq!(
        party.focus_spent(),
        before_focus,
        "an outsider refusal changes no shared game resource"
    );
}

/// Every refusal is anti-ghost: role theft, double seating, premature launch,
/// and non-leader launch leave the revision and hash-chain root untouched.
#[test]
fn refused_lobby_commands_are_anti_ghost() {
    let mut lobby = PartyLobby::new("raid:9", LEADER).expect("open");
    lobby.claim(LEADER, Role::Tank).expect("leader takes tank");

    for attempt in [
        ("role theft", "player:bob", Some(Role::Tank)),
        ("double seating", LEADER, Some(Role::Scout)),
        ("spectator ready", "spectator:eve", None),
    ] {
        let before_revision = lobby.revision();
        let before_root = lobby.root();
        let refusal = match attempt.2 {
            Some(role) => lobby.claim(attempt.1, role).unwrap_err(),
            None => lobby.set_ready(attempt.1, true).unwrap_err(),
        };
        assert!(matches!(
            refusal,
            LobbyRefusal::RoleTaken(_) | LobbyRefusal::AlreadySeated(_) | LobbyRefusal::NotSeated
        ));
        assert_eq!(lobby.revision(), before_revision, "{}", attempt.0);
        assert_eq!(lobby.root(), before_root, "{}", attempt.0);
    }
    let before_revision = lobby.revision();
    let before_root = lobby.root();
    assert!(matches!(
        lobby.launch(LEADER),
        Err(LobbyRefusal::IncompleteRoster { occupied: 1 })
    ));
    assert_eq!(lobby.revision(), before_revision);
    assert_eq!(lobby.root(), before_root);

    let mut ready = ready_roster();
    let before_revision = ready.revision();
    let before_root = ready.root();
    assert!(matches!(
        ready.launch("player:bob"),
        Err(LobbyRefusal::LeaderOnly)
    ));
    assert_eq!(ready.revision(), before_revision);
    assert_eq!(ready.root(), before_root);
}

/// The public journal is semantic, not a trusted roster snapshot: an honest log
/// replays, while changing one role claim leaves later claimed roots inconsistent.
#[test]
fn lobby_record_replays_and_a_tampered_role_claim_breaks() {
    let lobby = ready_roster();
    let record = lobby.export_record();
    let anchored_revision = lobby.revision();
    let anchored_root = lobby.root();
    let report = PartyLobby::verify_record(&record);
    assert!(report.verified, "{}", report.detail);
    assert_eq!(report.events, 8);

    let mut truncated = record.clone();
    truncated.events.pop();
    assert!(
        PartyLobby::verify_record(&truncated).verified,
        "an honest prefix is an internally valid history"
    );
    let report = PartyLobby::verify_record_at(&truncated, anchored_revision, anchored_root);
    assert!(!report.verified, "the anchored check refuses rollback");
    assert!(report.detail.contains("valid prefix"));

    let mut tampered = record;
    tampered.events[2].command = LobbyCommand::Claim(Role::Healer);
    let report = PartyLobby::verify_record(&tampered);
    assert!(!report.verified, "a changed semantic event must not replay");
    assert!(
        report.detail.contains("mismatch") || report.detail.contains("refused"),
        "the break is explained: {}",
        report.detail
    );
}

/// Leaving is a pre-launch role handoff: it removes readiness, lets a new
/// identity claim the exact role, and remains replay-verifiable.
#[test]
fn a_player_can_leave_and_a_replacement_can_ready_the_role() {
    let mut lobby = PartyLobby::new("match:handoff", LEADER).expect("open");
    lobby.claim("player:bob", Role::Mage).expect("claim");
    lobby.set_ready("player:bob", true).expect("ready");
    let left = lobby.leave("player:bob").expect("leave before launch");
    assert_eq!(left.occupied, 0);
    assert_eq!(left.ready, 0);
    assert!(lobby.seat(Role::Mage).is_none());

    lobby
        .claim("player:carol", Role::Mage)
        .expect("replacement claims role");
    assert_eq!(
        lobby.seat(Role::Mage).map(|seat| seat.identity()),
        Some("player:carol")
    );
    assert!(lobby.verify().verified);
}
