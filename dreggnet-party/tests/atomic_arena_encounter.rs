use std::sync::atomic::{AtomicU64, Ordering};

use dreggnet_party::Role;
use dreggnet_party::encounter::{
    ContributionCheckpoint, ContributionCommitHook, ContributionRecovery, EncounterError,
    FileContributionJournal, PartyArenaEncounter, PreparedContribution,
};
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

fn resolved_encounter() -> PartyArenaEncounter {
    let mut encounter =
        PartyArenaEncounter::new(roster(), "alice", hero_first_seed()).expect("encounter");
    for actor in ["alice", "bob", "cara"] {
        encounter.vote(actor, 0).expect("target ballot");
    }
    encounter.resolve("alice").expect("quorum target");
    assert_eq!(encounter.target(), Some(WARDEN));
    encounter
}

#[derive(Debug)]
struct FailAt(ContributionCheckpoint);

impl ContributionCommitHook for FailAt {
    fn checkpoint(&mut self, point: ContributionCheckpoint) -> Result<(), String> {
        if point == self.0 {
            Err("simulated process death".to_string())
        } else {
            Ok(())
        }
    }
}

#[test]
fn party_only_and_complete_but_unpublished_candidates_never_escape() {
    for crash_point in [
        ContributionCheckpoint::AfterParty,
        ContributionCheckpoint::AfterArena,
        ContributionCheckpoint::BeforePublish,
    ] {
        let mut encounter = resolved_encounter();
        let before_record = encounter.export_record();
        let before_root = encounter.root();
        let before_revision = encounter.revision();
        let before_party_root = encounter.party().world().state_root();
        let before_party_receipts = encounter.party().world().receipts().len();
        let before_arena = encounter.arena().world.snapshot();
        let before_hp = encounter.arena().hp(WARDEN);

        assert!(matches!(
            encounter.contribute_with_hook("bob", Role::Scout, &mut FailAt(crash_point)),
            Err(EncounterError::CommitInterrupted { point, .. }) if point == crash_point
        ));

        assert_eq!(encounter.root(), before_root);
        assert_eq!(encounter.revision(), before_revision);
        assert_eq!(encounter.party().world().state_root(), before_party_root);
        assert_eq!(
            encounter.party().world().receipts().len(),
            before_party_receipts
        );
        assert_eq!(encounter.arena().world.snapshot(), before_arena);
        assert_eq!(encounter.arena().hp(WARDEN), before_hp);
        assert_eq!(
            encounter.export_record().events.len(),
            before_record.events.len()
        );

        // The same command remains admissible because no role mark or tactical
        // transition leaked out of the failed detached candidate.
        let event = encounter
            .contribute("bob", Role::Scout)
            .expect("retry publishes both legs");
        assert!(event.party_receipt.is_some());
        assert!(event.arena_receipt.is_some());
        assert_eq!(encounter.revision(), before_revision + 1);
        assert!(encounter.arena().hp(WARDEN) < before_hp);
    }
}

#[test]
fn prepared_wire_is_bounded_checksummed_and_compare_and_swap() {
    let mut encounter = resolved_encounter();
    let before_root = encounter.root();
    let before_revision = encounter.revision();
    let before_party = encounter.party().world().state_root();
    let before_arena = encounter.arena().world.snapshot();

    let prepared = encounter
        .prepare_contribution("bob", Role::Scout)
        .expect("both detached legs validate");
    assert_eq!(encounter.root(), before_root, "prepare is non-mutating");
    assert_eq!(encounter.revision(), before_revision);
    assert_eq!(encounter.party().world().state_root(), before_party);
    assert_eq!(encounter.arena().world.snapshot(), before_arena);

    let wire = prepared.to_wire_bytes().expect("canonical prepared wire");
    assert_eq!(
        PreparedContribution::from_wire_bytes(&wire).expect("round trip"),
        prepared
    );
    let mut corrupt = wire.clone();
    corrupt[20] ^= 1;
    assert!(matches!(
        PreparedContribution::from_wire_bytes(&corrupt),
        Err(EncounterError::MalformedPrepared(reason)) if reason.contains("checksum")
    ));

    encounter
        .commit_prepared(&prepared)
        .expect("exact-head compare-and-swap publishes");
    let committed_root = encounter.root();
    assert_ne!(committed_root, before_root);
    assert!(matches!(
        encounter.commit_prepared(&prepared),
        Err(EncounterError::StalePrepared)
    ));

    let mut forged = prepared.clone();
    forged.actor = "alice".to_string();
    assert!(matches!(
        PartyArenaEncounter::recover_prepared(
            &encounter.export_record(),
            host_root(&encounter),
            &forged
        ),
        Err(EncounterError::MalformedPrepared(_))
    ));
}

#[test]
fn restart_recovery_completes_or_recognizes_exact_command_and_refuses_conflict() {
    let base = resolved_encounter();
    let base_record = base.export_record();
    let prepared = base
        .prepare_contribution("bob", Role::Scout)
        .expect("prepare scout contribution");

    let (applied, outcome) =
        PartyArenaEncounter::recover_prepared(&base_record, host_root(&base), &prepared)
            .expect("old exact base completes after restart");
    assert_eq!(outcome, ContributionRecovery::Applied);
    assert_eq!(applied.revision(), prepared.base_revision + 1);
    assert_eq!(
        applied.events().last().unwrap().command,
        dreggnet_party::encounter::EncounterCommand::Contribute {
            actor: "bob".to_string(),
            role: Role::Scout,
        }
    );

    let committed_record = applied.export_record();
    let (recovered, outcome) =
        PartyArenaEncounter::recover_prepared(&committed_record, host_root(&base), &prepared)
            .expect("restart after record persistence is idempotent");
    assert_eq!(outcome, ContributionRecovery::AlreadyCommitted);
    assert_eq!(recovered.root(), applied.root());
    assert_eq!(recovered.revision(), applied.revision());

    let mut conflict =
        PartyArenaEncounter::resume(&base_record, host_root(&base)).expect("base resumes");
    conflict
        .contribute("alice", Role::Tank)
        .expect("a different valid command occupies the next revision");
    assert!(matches!(
        PartyArenaEncounter::recover_prepared(
            &conflict.export_record(),
            host_root(&conflict),
            &prepared
        ),
        Err(EncounterError::StalePrepared)
    ));
}

#[test]
fn file_journal_survives_both_sides_of_record_persistence() {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let directory = std::env::temp_dir().join(format!(
        "dregg-party-arena-journal-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    let journal = FileContributionJournal::open(&directory).expect("journal directory");

    let base = resolved_encounter();
    let base_record = base.export_record();
    let prepared = base
        .prepare_contribution_durable("bob", Role::Scout, &journal)
        .expect("validate and fsync scout contribution");
    base.prepare_contribution_durable("bob", Role::Scout, &journal)
        .expect("idempotent durable reservation");
    assert_eq!(journal.load().expect("load intent"), Some(prepared.clone()));

    let conflicting = base
        .prepare_contribution("alice", Role::Tank)
        .expect("a distinct command also validates at this head");
    assert!(matches!(
        journal.reserve(&conflicting),
        Err(EncounterError::Journal(reason)) if reason.contains("already reserved")
    ));

    // Crash after intent fsync, before any encounter-record write.
    let (applied, _loaded, phase) =
        PartyArenaEncounter::recover_journaled(&base_record, host_root(&base), &journal)
            .expect("journal recovery")
            .expect("outstanding command");
    assert_eq!(phase, ContributionRecovery::Applied);

    // Model the host's durable EncounterRecord replacement, followed by a crash
    // before clearing the intent. The next process recognizes, never duplicates.
    let durable_after = applied.export_record();
    let (same, loaded, phase) =
        PartyArenaEncounter::recover_journaled(&durable_after, host_root(&applied), &journal)
            .expect("journal recovery")
            .expect("outstanding command");
    assert_eq!(phase, ContributionRecovery::AlreadyCommitted);
    assert_eq!(same.root(), applied.root());
    journal
        .clear(&loaded)
        .expect("clear exact incorporated intent");
    assert_eq!(journal.load().expect("empty journal"), None);

    drop(journal);
    std::fs::remove_dir_all(directory).expect("remove isolated test journal");
}
