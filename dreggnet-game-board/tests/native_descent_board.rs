//! FAST: native Descent season admission and restart are exact fresh replay,
//! with hostile actor/completion/record/snapshot substitutions refusing.

use dreggnet_game_board::native_descent_board::{
    NATIVE_DESCENT_BOARD_ASSURANCE, NativeBoardError, NativeDescentSeasonBoard,
    SNAPSHOT_DIGEST_DOMAIN,
};
use dreggnet_offerings::native_descent::{
    NativeDescentCompletion, NativeDescentOffering, NativeDescentRecord,
};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, RecordVerify, SessionConfig};
use dungeon_on_dregg::descent::{
    ASCEND, DELVE, FLEE, FLOORS, LOOT, SMITE, crowned_line, day_world,
};

/// The family index the `raw_seed` world deploys on. `NativeDescentOffering::new()` binds
/// `DayBinding::SeedDerived`, so the MAP — and therefore every driven tape below — is a function
/// of the session seed, not a constant.
fn day_of(raw_seed: u64) -> usize {
    NativeDescentOffering::new()
        .open(SessionConfig::with_seed(raw_seed))
        .expect("native world opens")
        .game()
        .day()
}

/// ⚑ THIS seed's crowned line, regenerated from the map the session actually deploys on.
///
/// This used to be an eighteen-entry literal. That tape was true of the single hard-coded dungeon
/// that predated the day-seeded draw and false on most of the sixteen maps that exist now — seed 7
/// draws a floor-1 guardian that takes TWO blows, so its third command `loot(1)` was offered but
/// DISABLED and all five tests in this file died on `driven command loot(1) is enabled`. It also
/// predated the climb: `flee` now demands `depth == 0`, so a tape that banks from below is refused
/// outright. `descent::crowned_line` mirrors the Lean `crownedRun` off the day's own `DayWorld`,
/// and `dungeon-on-dregg`'s `every_days_crowned_line_banks_the_prize_within_the_light` proves the
/// derived tape banks the prize inside the light on all sixteen draws.
fn crowned_for(raw_seed: u64) -> Vec<(&'static str, i64)> {
    crowned_line(day_of(raw_seed))
}

/// A SHORT banked run on `raw_seed`'s map — the non-crowned run the leaderboard tests need the
/// crowned one to outrank. Fell floor 1's guardian (however many blows THIS day's map asks for),
/// take the way-2 key, climb out, bank.
///
/// Relic 1 is the way-2 key and the draw guarantees `homes(keyFor w) < w`, so it always lies on
/// floor 1 — asserted here rather than assumed.
fn short_banked_for(raw_seed: u64) -> Vec<(&'static str, i64)> {
    short_banked_on(day_of(raw_seed))
}

/// The same short banked run, for a map named by family index directly — the beacon-bound path
/// deploys on the DAY's map, not the one seed 7 derives.
fn short_banked_on(day: usize) -> Vec<(&'static str, i64)> {
    let world = day_world(day);
    assert_eq!(
        world.homes[1], 1,
        "the way-2 key is minted on floor 1 on every day the draw can produce"
    );
    let mut line = vec![(DELVE, 0)];
    line.extend(std::iter::repeat_n((SMITE, 0), world.guard_hp(1) as usize));
    line.push((LOOT, 1));
    line.push((ASCEND, 0));
    line.push((FLEE, 0));
    line
}

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

#[test]
fn exact_native_replay_ranks_crown_relics_depth_and_turns() {
    let alice = actor("alice-cipherclerk");
    let bob = actor("bob-cipherclerk");
    let short_line = short_banked_for(7);
    let crowned = crowned_for(7);
    let (short_record, short_completion) = played(7, &alice, &short_line);
    let (crown_record, crown_completion) = played(7, &bob, &crowned);

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
    assert_eq!(
        short.standing.turns,
        short_line.len(),
        "a run is ranked on the commands it actually landed"
    );

    let crown = board
        .submit(bob.clone(), &crown_record, &crown_completion)
        .expect("fresh replay accepts the crowned run");
    assert_eq!(
        crown.rank, 1,
        "a crowned settlement outranks a short retreat"
    );
    assert!(crown.standing.crowned);
    // Day-independent, and the whole content of "crowned": THE PRIZE (relic 0) is banked and the
    // run stood on the deepest floor. It read `[0, 1, 2, 3]` back when turning a key kept it —
    // `unlock` now sets the key down in the door it opened (`HUNG + depth`) and `flee` promotes
    // `CARRIED` and only `CARRIED`, so the reference crowned line brings home the prize alone.
    assert_eq!(crown.standing.banked_relics, vec![0]);
    assert_eq!(crown.standing.peak_depth, FLOORS);
    assert_eq!(crown.standing.turns, crowned.len());
    assert!(
        crown.standing.turns > short.standing.turns,
        "the crowned line is the longer run"
    );

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
    let (record, completion) = played(7, &alice, &crowned_for(7));
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

    let (foreign_record, foreign_completion) = played(19, &actor("foreign"), &short_banked_for(19));
    assert!(matches!(
        board.submit(actor("foreign"), &foreign_record, &foreign_completion),
        Err(NativeBoardError::WrongWorldSeed { .. })
    ));
}

#[test]
fn canonical_restart_redrives_runs_and_refuses_tampered_witnesses() {
    let alice = actor("alice-cipherclerk");
    let bob = actor("bob-cipherclerk");
    let (alice_record, alice_completion) = played(7, &alice, &crowned_for(7));
    let (bob_record, bob_completion) = played(7, &bob, &short_banked_for(7));

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
    let (record, completion) = played(7, &alice, &crowned_for(7));
    let mut board = NativeDescentSeasonBoard::open(42, 7).expect("season opens");
    board
        .submit(alice.clone(), &record, &completion)
        .expect("authentic run accepts");
    let snapshot = board.export_canonical();

    // The sole entry then begins actor-len/actor/command-count; change its first command from
    // `delve(0)` to `smite(0)`, and recompute the public corruption digest.
    //
    // ⚑ This sum was `8 + 1 + 8 + 1 + 32 + 4` and silently DROPPED the 32-byte day-seed the season
    // gained when runs became beacon-bound (`export_canonical` writes magic, version, season_id,
    // seed, day_seed, genesis_root, count — two 32-byte fields, not one). It pointed 32 bytes short
    // and read a genesis-root byte. Spelled out per field so the next header change moves it.
    let first_entry = 8   // SNAPSHOT_MAGIC
        + 1               // SNAPSHOT_VERSION
        + 8               // season_id: u64
        + 1               // seed: u8
        + 32              // day_seed
        + 32              // genesis_root
        + 4; // entry count: u32
    let command_tag = first_entry + 2 + alice.as_str().len() + 2;
    assert_eq!(snapshot[command_tag], 0, "first command is delve");

    let mut substituted = snapshot.clone();
    substituted[command_tag] = 2;
    refresh_snapshot_digest(&mut substituted);

    match NativeDescentSeasonBoard::import_canonical(&substituted).map(|_| ()) {
        Err(NativeBoardError::ReplayRefused(_)) | Err(NativeBoardError::CompletionSubstitution) => {
        }
        other => panic!("a substituted first command must not import: {other:?}"),
    }

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
    let mut hasher = blake3::Hasher::new_derive_key(SNAPSHOT_DIGEST_DOMAIN);
    hasher.update(&snapshot[..body_len]);
    let digest = *hasher.finalize().as_bytes();
    snapshot[body_len..].copy_from_slice(&digest);
}

// ── A SEASON IS A DAY'S BOARD ────────────────────────────────────────────────────────

/// Play `line` on a world whose banked-relic provenance root is `day`'s verified beacon day —
/// exactly what a live daily surface's runs carry.
fn played_on_day(
    raw_seed: u64,
    day: procgen_dregg::CommittedSeed,
    who: &DreggIdentity,
    line: &[(&str, i64)],
) -> (NativeDescentRecord, NativeDescentCompletion) {
    let offering = NativeDescentOffering::on_day(day);
    let mut session = offering
        .open(SessionConfig::with_seed(raw_seed))
        .expect("native world opens on the day");
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

/// ⚑ A live daily run belongs to ITS day's season — admitted, re-drivable, and restartable
/// there, and refused by a board over another provenance root.
///
/// The board rebuilds runs by re-opening and re-driving their commands (`reverify`,
/// `import_canonical`), which only re-derives on the season's own run day-seed. So the season
/// carries that day-seed, admission requires the run to name it, and a mismatch is refused at
/// the door rather than admitted into an entry the board cannot re-drive.
#[test]
fn a_beacon_bound_run_belongs_to_its_days_season_and_no_other() {
    let beacon = procgen_dregg::beacon::pinned_fallback_beacon();
    let day = beacon.seed().expect("the pinned published round verifies");
    let alice = actor("alice-cipherclerk");
    // The beacon-bound world deploys on the BEACON's map, which is generally not the one seed 7
    // derives — so the tape has to come from that day's own `DayWorld`.
    let beacon_day = NativeDescentOffering::on_day(day)
        .open(SessionConfig::with_seed(7))
        .expect("native world opens on the day")
        .game()
        .day();
    let (record, completion) = played_on_day(7, day, &alice, &short_banked_on(beacon_day));

    // The run's provenance root is the day's, not the deploy seed's.
    assert_ne!(
        record.day_seed,
        *NativeDescentOffering::new()
            .open(SessionConfig::with_seed(7))
            .expect("seed-derived world opens")
            .day_seed(),
        "a beacon-bound run must not carry the pre-computable provenance root"
    );

    // The fixture (seed-derived) season refuses it: same world seed, different day.
    let mut seed_derived = NativeDescentSeasonBoard::open(42, 7).expect("season opens");
    assert_eq!(
        seed_derived.submit(alice.clone(), &record, &completion),
        Err(NativeBoardError::WrongSeasonDay),
        "a run from another provenance day is another season's run"
    );

    // Its OWN day's season admits it, re-drives it, and survives a canonical restart.
    let mut board =
        NativeDescentSeasonBoard::open_on_day(42, 7, record.day_seed).expect("the day's season");
    assert_eq!(board.season().day_seed, record.day_seed);
    let accepted = board
        .submit(alice.clone(), &record, &completion)
        .expect("the day's season admits its own run");
    assert_eq!(
        board
            .reverify(&accepted.standing.completion_root)
            .expect("the archived run re-drives under the season's day"),
        accepted.standing,
        "reverify must re-derive the same standing — it re-opens on the season's day-seed"
    );
    let restarted = NativeDescentSeasonBoard::import_canonical(&board.export_canonical())
        .expect("the snapshot carries the season's day and restarts on it");
    assert_eq!(restarted.season(), board.season());
    assert_eq!(restarted.leaderboard(), board.leaderboard());
}
