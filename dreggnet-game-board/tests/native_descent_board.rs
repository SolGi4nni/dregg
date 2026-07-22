//! FAST: native Descent season admission and restart are exact fresh replay,
//! with hostile actor/completion/record/snapshot substitutions refusing.

use dreggnet_game_board::native_descent_board::{
    NATIVE_DESCENT_BOARD_ASSURANCE, NativeBoardError, NativeDescentSeasonBoard,
};
use dreggnet_offerings::native_descent::{
    NativeDescentCompletion, NativeDescentOffering, NativeDescentRecord,
};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, RecordVerify, SessionConfig};

const CROWNED_LINE: [(&str, i64); 18] = [
    ("delve", 0),
    ("smite", 0),
    ("loot", 1),
    ("unlock", 2),
    ("delve", 0),
    ("smite", 0),
    ("loot", 2),
    ("unlock", 3),
    ("delve", 0),
    ("smite", 0),
    ("smite", 0),
    ("loot", 3),
    ("unlock", 4),
    ("delve", 0),
    ("smite", 0),
    ("smite", 0),
    ("loot", 0),
    ("flee", 0),
];

fn actor(name: &str) -> DreggIdentity {
    DreggIdentity(name.to_string())
}

fn action(
    offering: &NativeDescentOffering,
    session: &dreggnet_offerings::native_descent::NativeDescentSession,
    turn: &str,
    arg: i64,
) -> Action {
    offering
        .actions(session)
        .into_iter()
        .find(|candidate| candidate.turn == turn && candidate.arg == arg)
        .unwrap_or_else(|| panic!("native surface omitted {turn}({arg})"))
}

fn played(
    raw_seed: u64,
    who: &DreggIdentity,
    line: &[(&str, i64)],
) -> (NativeDescentRecord, NativeDescentCompletion) {
    let offering = NativeDescentOffering::new();
    let mut session = offering
        .open(SessionConfig::with_seed(raw_seed))
        .expect("native world opens");
    for &(turn, arg) in line {
        let input = action(&offering, &session, turn, arg);
        assert!(input.enabled, "driven command {turn}({arg}) is enabled");
        match offering.advance(&mut session, input, who.clone()) {
            Outcome::Landed { .. } => {}
            Outcome::Refused(reason) => panic!("legal native command refused: {reason}"),
        }
    }
    let completion = session
        .completion()
        .cloned()
        .expect("driven line banks a completion");
    (offering.export_record(&session), completion)
}

fn short_banked_line() -> Vec<(&'static str, i64)> {
    vec![("delve", 0), ("smite", 0), ("loot", 1), ("flee", 0)]
}

#[test]
fn exact_native_replay_ranks_crown_relics_depth_and_turns() {
    let alice = actor("alice-cipherclerk");
    let bob = actor("bob-cipherclerk");
    let (short_record, short_completion) = played(7, &alice, &short_banked_line());
    let (crown_record, crown_completion) = played(7, &bob, &CROWNED_LINE);

    let mut board = NativeDescentSeasonBoard::open(42, 7).expect("season opens");
    assert_eq!(board.assurance(), NATIVE_DESCENT_BOARD_ASSURANCE);
    assert!(board.assurance().contains("replay-verified"));
    assert!(board.assurance().contains("not a succinct FULL-STARK"));

    let short = board
        .submit(alice.clone(), &short_record, &short_completion)
        .expect("fresh replay accepts the banked run");
    assert_eq!(short.rank, 1);
    assert!(!short.standing.crowned);
    assert_eq!(short.standing.banked_relics, vec![1]);
    assert_eq!(short.standing.peak_depth, 1);
    assert_eq!(short.standing.turns, 4);

    let crown = board
        .submit(bob.clone(), &crown_record, &crown_completion)
        .expect("fresh replay accepts the crowned run");
    assert_eq!(
        crown.rank, 1,
        "a crowned settlement outranks a short retreat"
    );
    assert!(crown.standing.crowned);
    assert_eq!(crown.standing.banked_relics, vec![0, 1, 2, 3]);
    assert_eq!(crown.standing.peak_depth, 4);
    assert_eq!(crown.standing.turns, 18);

    let standings = board.leaderboard();
    assert_eq!(standings.len(), 2);
    assert_eq!(standings[0].player, bob);
    assert_eq!(standings[1].player, alice);
    assert_eq!(
        board
            .reverify(&standings[0].completion_root)
            .expect("retained witness independently replays"),
        standings[0]
    );
    assert!(matches!(
        board.reverify(&[0xAA; 32]),
        Err(NativeBoardError::UnknownCompletion)
    ));
}

#[test]
fn duplicate_actor_completion_and_world_substitutions_are_anti_ghost() {
    let alice = actor("alice-cipherclerk");
    let mallory = actor("mallory-cipherclerk");
    let (record, completion) = played(7, &alice, &CROWNED_LINE);
    let mut board = NativeDescentSeasonBoard::open(42, 7).expect("season opens");

    assert!(matches!(
        board.submit(mallory, &record, &completion),
        Err(NativeBoardError::PlayerSubstitution)
    ));
    assert!(board.leaderboard().is_empty(), "substitution is anti-ghost");

    let mut wrong_completion = completion.clone();
    wrong_completion.root[0] ^= 1;
    assert!(matches!(
        board.submit(alice.clone(), &record, &wrong_completion),
        Err(NativeBoardError::CompletionSubstitution)
    ));
    assert!(board.leaderboard().is_empty());

    let mut wrong_revision = completion.clone();
    wrong_revision.revision -= 1;
    assert!(matches!(
        board.submit(alice.clone(), &record, &wrong_revision),
        Err(NativeBoardError::CompletionSubstitution)
    ));

    let mut tampered_record = record.clone();
    tampered_record.events[0].post.depth ^= 1;
    assert!(matches!(
        board.submit(alice.clone(), &tampered_record, &completion),
        Err(NativeBoardError::ReplayRefused(_))
    ));

    board
        .submit(alice.clone(), &record, &completion)
        .expect("authentic run accepts after hostile attempts");
    assert!(matches!(
        board.submit(alice, &record, &completion),
        Err(NativeBoardError::DuplicateCompletion)
    ));
    assert_eq!(board.leaderboard().len(), 1, "duplicate is anti-ghost");

    let (foreign_record, foreign_completion) = played(19, &actor("foreign"), &short_banked_line());
    assert!(matches!(
        board.submit(actor("foreign"), &foreign_record, &foreign_completion),
        Err(NativeBoardError::WrongWorldSeed { .. })
    ));
}

#[test]
fn canonical_restart_redrives_runs_and_refuses_tampered_witnesses() {
    let alice = actor("alice-cipherclerk");
    let bob = actor("bob-cipherclerk");
    let (alice_record, alice_completion) = played(7, &alice, &CROWNED_LINE);
    let (bob_record, bob_completion) = played(7, &bob, &short_banked_line());

    let mut first = NativeDescentSeasonBoard::open(42, 7).expect("season opens");
    first
        .submit(alice.clone(), &alice_record, &alice_completion)
        .expect("Alice accepts");
    first
        .submit(bob.clone(), &bob_record, &bob_completion)
        .expect("Bob accepts");
    let snapshot = first.export_canonical();

    let restarted = NativeDescentSeasonBoard::import_canonical(&snapshot)
        .expect("every archived witness freshly replays");
    assert_eq!(restarted.season(), first.season());
    assert_eq!(restarted.leaderboard(), first.leaderboard());
    assert_eq!(restarted.export_canonical(), snapshot);

    // Canonical bytes are insertion-order independent.
    let mut reverse = NativeDescentSeasonBoard::open(42, 7).expect("season opens");
    reverse
        .submit(bob, &bob_record, &bob_completion)
        .expect("Bob accepts");
    reverse
        .submit(alice, &alice_record, &alice_completion)
        .expect("Alice accepts");
    assert_eq!(reverse.export_canonical(), snapshot);

    let mut corrupt = snapshot.clone();
    corrupt[20] ^= 1;
    assert!(matches!(
        NativeDescentSeasonBoard::import_canonical(&corrupt),
        Err(NativeBoardError::SnapshotDigestMismatch)
    ));
}

#[test]
fn recomputing_the_snapshot_digest_does_not_bypass_native_replay() {
    let alice = actor("alice-cipherclerk");
    let (record, completion) = played(7, &alice, &CROWNED_LINE);
    let mut board = NativeDescentSeasonBoard::open(42, 7).expect("season opens");
    board
        .submit(alice.clone(), &record, &completion)
        .expect("authentic run accepts");
    let snapshot = board.export_canonical();

    // Header = magic/version/season/seed/genesis/count. The sole entry then
    // begins actor-len/actor/command-count; change its first command from
    // `delve(0)` to `smite(0)`, and recompute the public corruption digest.
    let first_entry = 8 + 1 + 8 + 1 + 32 + 4;
    let command_tag = first_entry + 2 + alice.as_str().len() + 2;
    assert_eq!(snapshot[command_tag], 0, "first command is delve");

    let mut substituted = snapshot.clone();
    substituted[command_tag] = 2;
    refresh_snapshot_digest(&mut substituted);

    assert!(matches!(
        NativeDescentSeasonBoard::import_canonical(&substituted),
        Err(NativeBoardError::ReplayRefused(_)) | Err(NativeBoardError::CompletionSubstitution)
    ));

    let mut target_wide_relic = snapshot;
    target_wide_relic[command_tag] = 3;
    target_wide_relic[command_tag + 1..command_tag + 9].fill(0xff);
    refresh_snapshot_digest(&mut target_wide_relic);
    match NativeDescentSeasonBoard::import_canonical(&target_wide_relic) {
        Err(NativeBoardError::MalformedSnapshot(reason)) => {
            assert!(
                reason.contains("action wire"),
                "unexpected refusal: {reason}"
            )
        }
        Err(other) => panic!("target-wide relic id failed at the wrong boundary: {other}"),
        Ok(_) => panic!("target-wide relic id was accepted from the stable action wire"),
    }
}

fn refresh_snapshot_digest(snapshot: &mut [u8]) {
    let body_len = snapshot.len() - 32;
    let mut hasher = blake3::Hasher::new_derive_key("dregg.native-descent-board.snapshot.v2");
    hasher.update(&snapshot[..body_len]);
    let digest = *hasher.finalize().as_bytes();
    snapshot[body_len..].copy_from_slice(&digest);
}
