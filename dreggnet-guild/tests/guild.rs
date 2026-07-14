//! # Guilds, DRIVEN end-to-end on the real substrate (not named).
//!
//! Every tooth is exercised through the real executor / verifier / escrow capacity,
//! with the non-vacuous other side asserted:
//!
//! * MEMBERSHIP IS THE CAP SET — a member's guild-state write COMMITS; a non-member's
//!   identical write is a real `CapabilityNotHeld` refusal (anti-ghost: nothing lands).
//! * THE LEADERBOARD SUMS UN-FORGEABLE CLEARS — a real winning playthrough counts; a
//!   FORGED (non-winning) completion is rejected by the no-cheat verify and inflates
//!   nothing; a non-member's clear is refused at the board.
//! * THE TREASURY IS ESCROW-CUSTODIED — a member's contribution locks into custody; an
//!   OFFICER (non-depositor) cannot abscond (real `NotYourLeg` refusal); the rightful
//!   depositor reclaims and is made whole.
//! * GUILD-VS-GUILD — the guild with more PROVEN clears out-ranks one that tried to pad
//!   with a forged clear.
//! * GOVERNANCE — a quorum-certified officer election; below quorum no officer is
//!   seated; a forged ballot signature is refused.

use dregg_cell::Cell;
use dregg_types::CellId as EscrowCellId;

use dreggnet_offerings::DreggIdentity;
use dreggnet_offerings::character::CharacterSheet;
use dungeon_on_dregg::{CH_CLAIM, CH_DESCEND, CH_TAKE_LANTERN, DUNGEON};
use ugc_dregg::{Completion, RejectReason, Universe, WinCondition, record_playthrough};

use dreggnet_guild::governance::{CollectiveError, Custodian, OfficerElection, Seat, SignedBallot};
use dreggnet_guild::treasury::{
    EscrowError, EscrowTerms, GuildTreasury, Leg, LegRequirement, MarketError, Side,
};
use dreggnet_guild::versus::{Standing, rank_guilds};
use dreggnet_guild::{ClearError, Guild};

// ── The driven no-cheat universe: the built-in salt-shore dungeon (win = gold==500). ──

fn salt_shore() -> Universe {
    Universe::authored(
        "The Salt Shore Descent",
        "guild-fixture",
        DUNGEON,
        WinCondition::ended_with(&[("gold", 500)]),
    )
    .expect("the salt-shore dungeon is a valid, deployable universe")
}

/// The minimal winning move sequence (take the lantern, descend the gate, claim).
const WIN_MOVES: [usize; 3] = [CH_TAKE_LANTERN, CH_DESCEND, CH_CLAIM];

fn who(s: &str) -> DreggIdentity {
    DreggIdentity(s.to_string())
}

// ═══════════════════════════════════════════════════════════════════════════════
// 1. Membership IS the capability set.
// ═══════════════════════════════════════════════════════════════════════════════

/// A member's write to the shared guild cell COMMITS (they hold the guild cap); a
/// NON-member's identical write is a real `CapabilityNotHeld` refusal — anti-ghost, the
/// guild cell is untouched by the refused reach.
#[test]
fn membership_is_a_capability_a_non_member_is_refused() {
    let mut guild = Guild::form("The Iron Wardens");
    let alice = who("player-alice");

    // Joining IS a capability grant.
    let alice_cell = guild.admit(&alice);
    assert!(guild.is_member(&alice), "alice joined the guild");

    // A member acts on guild state — a real committed, receipted turn.
    let out = guild.act_on_guild(alice_cell);
    assert!(out.committed(), "a member may act on guild state: {out:?}");
    assert_ne!(
        out.receipt().unwrap(),
        [0u8; 32],
        "a genuine receipted turn"
    );
    let after_member = guild.presence();
    assert!(
        after_member.is_some_and(|p| p != [0u8; 32]),
        "the member's write landed on the guild cell"
    );

    // A NON-member (a real cell in the same world, but holding no guild cap) is refused.
    let stranger = guild.install_stranger();
    let refused = guild.act_on_guild(stranger);
    assert!(
        refused.refused(),
        "a non-member cannot act on guild state: {refused:?}"
    );
    assert!(
        refused.reason().unwrap().to_lowercase().contains("cap"),
        "the refusal is a capability refusal, got: {}",
        refused.reason().unwrap()
    );

    // Anti-ghost: the refused non-member write changed nothing (the guild cell still
    // holds the member's tag, not the stranger's).
    assert_eq!(
        guild.presence(),
        after_member,
        "the non-member's refused write left the guild cell untouched"
    );
}

// ═══════════════════════════════════════════════════════════════════════════════
// 2. The leaderboard SUMS un-forgeable clears (a forged clear counts for nothing).
// ═══════════════════════════════════════════════════════════════════════════════

/// A real winning playthrough is a verified clear that RAISES the guild aggregate; a
/// FORGED (non-winning) completion claiming a win is rejected by the no-cheat verify and
/// adds NOTHING; a non-member's clear is refused at the board.
#[test]
fn leaderboard_sums_verified_clears_a_forged_clear_cannot_inflate() {
    let universe = salt_shore();
    let mut guild = Guild::form("The Verdant Pact");
    let bram = who("player-bram");
    let della = who("player-della");
    guild.admit(&bram);
    guild.admit(&della);

    // A GENUINE winning playthrough — accepted, and it raises the aggregate.
    let honest = record_playthrough(&universe, &WIN_MOVES).expect("the honest win drives cleanly");
    let turns = guild
        .board_mut()
        .record_clear(
            &bram,
            &universe,
            &Completion {
                universe: universe.id(),
                player: "bram".into(),
                play: honest.clone(),
                claimed_turns: WIN_MOVES.len(),
            },
        )
        .expect("a real winning clear is accepted");
    assert_eq!(turns, WIN_MOVES.len(), "the verified turns-to-win");
    assert_eq!(
        guild.stats().verified_clears,
        1,
        "the guild has one proven clear"
    );

    // A FORGED clear — an incomplete playthrough (only the first move) that never reaches
    // the win, but claims victory. The no-cheat verify REJECTS it (DidNotWin); the guild
    // aggregate does not move.
    let incomplete =
        record_playthrough(&universe, &[CH_TAKE_LANTERN]).expect("the partial run drives");
    let forged = guild.board_mut().record_clear(
        &della,
        &universe,
        &Completion {
            universe: universe.id(),
            player: "della".into(),
            play: incomplete,
            claimed_turns: 1,
        },
    );
    assert!(
        matches!(forged, Err(ClearError::NoCheat(RejectReason::DidNotWin))),
        "a forged (non-winning) clear is rejected by the no-cheat verify, got {forged:?}"
    );
    assert_eq!(
        guild.stats().verified_clears,
        1,
        "the forged clear inflated nothing — still one proven clear"
    );

    // A non-member's clear is refused at the board (only the cap set counts).
    let outsider = who("player-outsider");
    let refused = guild.board_mut().record_clear(
        &outsider,
        &universe,
        &Completion {
            universe: universe.id(),
            player: "outsider".into(),
            play: honest,
            claimed_turns: WIN_MOVES.len(),
        },
    );
    assert!(
        matches!(refused, Err(ClearError::NotAMember(_))),
        "a non-member's clear cannot inflate the guild, got {refused:?}"
    );
    assert_eq!(guild.stats().verified_clears, 1, "still one proven clear");
}

/// The survivor board leans on the WriteOnce-final `dead` flag: a live character
/// (`dead == 0`) counts; a dead one does not — and (per the character store) a dead
/// character cannot un-die to re-enter the board.
#[test]
fn survivor_board_counts_only_live_characters() {
    let mut guild = Guild::form("The Deathless");
    let hardy = who("player-hardy");
    let fallen = who("player-fallen");
    guild.admit(&hardy);
    guild.admit(&fallen);

    let alive = CharacterSheet {
        dead: 0,
        ..CharacterSheet::default()
    };
    let dead = CharacterSheet {
        dead: 1,
        ..CharacterSheet::default()
    };

    assert!(
        guild.board_mut().record_survivor(&hardy, &alive).unwrap(),
        "a live character is a survivor"
    );
    assert!(
        !guild.board_mut().record_survivor(&fallen, &dead).unwrap(),
        "a dead character is not a survivor"
    );
    assert_eq!(
        guild.stats().survivors,
        1,
        "exactly one survivor — the dead character cannot pad the board"
    );
}

// ═══════════════════════════════════════════════════════════════════════════════
// 3. The treasury is escrow-custodied — no officer can abscond.
// ═══════════════════════════════════════════════════════════════════════════════

const CONTRIB_ASSET: [u8; 32] = [0x2A; 32];
const MATCH_ASSET: [u8; 32] = [0x2B; 32];
const MEMBER_PK: [u8; 32] = [0x11; 32];
const MATCH_PK: [u8; 32] = [0x12; 32];
const OFFICER_PK: [u8; 32] = [0x13; 32];

fn wallet(pk: [u8; 32], asset: [u8; 32], balance: i64) -> Cell {
    Cell::with_balance(pk, asset, balance)
}
fn party(pk: [u8; 32], asset: [u8; 32]) -> EscrowCellId {
    Cell::with_balance(pk, asset, 0).id()
}

/// A member's contribution locks into escrow custody (value leaves their wallet,
/// conserved, and the commitment moves — witnessed). An OFFICER (a non-depositor) trying
/// to reclaim the member's contribution is a real `NotYourLeg` refusal — no abscond. The
/// rightful depositor reclaims and is made whole (the non-vacuous contrast).
#[test]
fn treasury_is_escrow_custodied_no_officer_can_abscond() {
    let member = party(MEMBER_PK, CONTRIB_ASSET);
    let matcher = party(MATCH_PK, MATCH_ASSET);
    let officer = party(OFFICER_PK, CONTRIB_ASSET);

    let terms = EscrowTerms::swap(
        LegRequirement::new(member, EscrowCellId::from_bytes(CONTRIB_ASSET), 100),
        LegRequirement::new(matcher, EscrowCellId::from_bytes(MATCH_ASSET), 250),
    );
    let mut treasury = GuildTreasury::open(terms);

    let mut member_wallet = wallet(MEMBER_PK, CONTRIB_ASSET, 100);

    // Contribute: the member locks their leg into custody.
    let before = treasury.commitment();
    treasury
        .contribute(
            Side::A,
            &Leg::new(member, EscrowCellId::from_bytes(CONTRIB_ASSET), 100),
            &mut member_wallet,
        )
        .expect("the member's conforming contribution locks");
    assert_ne!(
        before,
        treasury.commitment(),
        "the contribution re-seals the commitment"
    );
    assert_eq!(
        member_wallet.state.balance(),
        0,
        "value left the wallet into custody"
    );
    assert_eq!(
        treasury.custody_a(),
        100,
        "the contribution is held in custody"
    );

    // THE ANTI-ABSCOND TOOTH: an officer (non-depositor) cannot pull the contribution.
    let mut officer_wallet = wallet(OFFICER_PK, CONTRIB_ASSET, 0);
    let abscond = treasury.attempt_abscond(Side::A, officer, &mut officer_wallet);
    assert_eq!(
        abscond,
        Err(MarketError::Escrow(EscrowError::NotYourLeg(Side::A))),
        "an officer cannot abscond with a member's contribution"
    );
    assert_eq!(
        officer_wallet.state.balance(),
        0,
        "anti-ghost: the officer got nothing"
    );
    assert_eq!(treasury.custody_a(), 100, "the treasury is intact");

    // Non-vacuous: the rightful depositor reclaims their own contribution and is made whole.
    let reclaimed = treasury
        .reclaim(Side::A, member, &mut member_wallet)
        .expect("the depositor reclaims their own contribution");
    assert_eq!(reclaimed, 100);
    assert_eq!(
        member_wallet.state.balance(),
        100,
        "the member is made whole"
    );
    assert_eq!(
        treasury.custody_a(),
        0,
        "custody drained by the rightful reclaim"
    );
}

// ═══════════════════════════════════════════════════════════════════════════════
// 4. Guild-vs-guild by aggregate PROVEN stats.
// ═══════════════════════════════════════════════════════════════════════════════

/// Two guilds are ranked by aggregate proven clears; a guild cannot climb by padding a
/// forged clear (which the board never admitted).
#[test]
fn guild_vs_guild_ranks_by_proven_stats_padding_does_not_help() {
    let universe = salt_shore();

    // Guild A: two members each land a real verified clear.
    let mut a = Guild::form("Guild A");
    for name in ["a-one", "a-two"] {
        let id = who(name);
        a.admit(&id);
        let play = record_playthrough(&universe, &WIN_MOVES).unwrap();
        a.board_mut()
            .record_clear(
                &id,
                &universe,
                &Completion {
                    universe: universe.id(),
                    player: name.into(),
                    play,
                    claimed_turns: WIN_MOVES.len(),
                },
            )
            .expect("a real clear");
    }

    // Guild B: one real clear, and a FORGED clear that the no-cheat verify rejects.
    let mut b = Guild::form("Guild B");
    let b_one = who("b-one");
    b.admit(&b_one);
    let play = record_playthrough(&universe, &WIN_MOVES).unwrap();
    b.board_mut()
        .record_clear(
            &b_one,
            &universe,
            &Completion {
                universe: universe.id(),
                player: "b-one".into(),
                play,
                claimed_turns: WIN_MOVES.len(),
            },
        )
        .expect("a real clear");
    // The pad attempt: an incomplete playthrough claiming a win — rejected, counts nothing.
    let incomplete = record_playthrough(&universe, &[CH_TAKE_LANTERN]).unwrap();
    let padded = b.board_mut().record_clear(
        &b_one,
        &universe,
        &Completion {
            universe: universe.id(),
            player: "b-one".into(),
            play: incomplete,
            claimed_turns: 1,
        },
    );
    assert!(
        padded.is_err(),
        "the pad attempt is rejected by the no-cheat verify"
    );

    assert_eq!(a.stats().verified_clears, 2);
    assert_eq!(
        b.stats().verified_clears,
        1,
        "B's forged clear did not count"
    );
    assert_eq!(
        rank_guilds(&a.stats(), &b.stats()),
        Standing::First,
        "the guild with more PROVEN clears ranks higher — you cannot pad with fakes"
    );
}

// ═══════════════════════════════════════════════════════════════════════════════
// 5. Governance — a quorum-certified officer election.
// ═══════════════════════════════════════════════════════════════════════════════

fn seats(names: &[&str]) -> (Vec<Custodian>, Vec<Seat>) {
    let custodians: Vec<Custodian> = names.iter().map(|n| Custodian::demo(*n)).collect();
    let seated: Vec<Seat> = custodians.iter().map(|c| c.seat()).collect();
    (custodians, seated)
}

/// A quorum of guild seats elects an officer; below quorum no officer is seated; a
/// forged ballot signature is refused (the collective teeth carry straight over).
#[test]
fn governance_elects_an_officer_by_quorum_certified_vote() {
    let (custodians, seated) = seats(&["Bramwen", "Corvin", "Della", "Ferro", "Wisp"]);
    let federation = [0xC7; 32];

    // Candidates: two members stand for officer. Option 0 = Bramwen, option 1 = Corvin.
    let candidates = vec!["Bramwen".to_string(), "Corvin".to_string()];
    let mut election = OfficerElection::open(
        "Who leads the guild?",
        candidates,
        &seated,
        3, // quorum M
        federation,
    )
    .expect("the election opens");
    let poll = election.poll();

    // Below quorum: two signed ballots — no officer is seated.
    election
        .cast(&custodians[0].sign_ballot(poll, 0))
        .expect("Bramwen's seat votes");
    election
        .cast(&custodians[1].sign_ballot(poll, 0))
        .expect("Corvin's seat votes");
    assert!(
        election.elect().expect("resolve query").is_none(),
        "below quorum, no officer is seated"
    );

    // A forged ballot signature is refused (a seated seat's key, a garbage signature).
    let forged = SignedBallot {
        voter_pk: custodians[2].public_key(),
        option: 0,
        signature: dregg_types::Signature([0x9; 64]),
    };
    match election.cast(&forged) {
        Err(CollectiveError::BadSignature) => {}
        other => panic!("a forged ballot must be BadSignature, got {other:?}"),
    }

    // A third genuine ballot reaches quorum — Bramwen (option 0) is elected officer.
    election
        .cast(&custodians[2].sign_ballot(poll, 0))
        .expect("Della's seat votes");
    let officer = election
        .elect()
        .expect("resolve")
        .expect("quorum reached — an officer is seated");
    assert_eq!(officer.name, "Bramwen", "the certified officer");
    assert_eq!(officer.votes, 3, "three ballots named the officer");
}
