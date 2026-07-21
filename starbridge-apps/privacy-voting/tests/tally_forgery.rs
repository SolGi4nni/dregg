//! THE TALLY-BINDING TOOTH (flipped 2026-07-17, acc/voting-fix): the poll's
//! tally board is now BALLOT-BOUND at the executor. The 2026-07-17 4swarm
//! fic-apps forgery — `record_tally` writing an arbitrary caller-supplied
//! `new_tally` gated only by `Signature` + `Monotonic`, so a poll operator
//! could post ANY tally ≥ current with ZERO ballots cast — is REFUSED.
//!
//! THE FIX (ported from `collective-choice`'s `CountGe` quorum gate, at its
//! weighted-poll floor of 1): each tally slot carries an
//! `AnyOf[Immutable, CountGe{1, ballots_slot}]` caveat in the poll's
//! `CellProgram`. A turn that MOVES a tally must EXHIBIT — as its unique
//! `Cleartext` witness blob, a postcard `Vec<[u8; 32]>` — a NON-EMPTY set of
//! distinct ballot-cell ids whose canonical sorted-set commitment
//! ([`dregg_cell::count_ge_set_commitment`]) opens the choice's ballot-set
//! commitment slot's NEW value. A witness-less or empty-set tally write is a
//! fail-closed EXECUTOR refusal, and every counted-ballot claim becomes an
//! on-ledger-openable commitment (tamper-EVIDENT, as the crate docs claim).
//!
//! RESIDUAL, honestly pinned below (`residual_*` — passes while the gap is
//! open; flip it when the primitive lands): the tally VALUE is not bound to
//! the exhibited set's SIZE. `StateConstraint::CountGe`'s threshold is a
//! program-build-time CONSTANT, and the executor has NO atom relating a slot's
//! numeric value to the distinct-count of the exhibited/committed set — the
//! missing primitive is a slot-valued-threshold CountGe (e.g.
//! `CountGeSlot { count_index, set_commitment_slot }`: exhibited distinct set
//! opens `new[set_commitment_slot]` AND `|set| >= u64(new[count_index])`), or
//! equivalently a `SimpleStateConstraint::Witnessed` so a Custom dynamic-count
//! predicate could compose under `AnyOf[Immutable, …]`. Also named: set
//! ELEMENTS are not verified to be real factory-born ballot cells that voted
//! this choice — the SAME honest scope `StateConstraint::CountGe` documents
//! and the SAME residual `collective-choice`'s quorum gate carries (full
//! closure is the ZK tally tier the crate docs already name).

use std::collections::BTreeSet;

use dregg_app_framework::{AgentCipherclerk, AppCipherclerk, EmbeddedExecutor, field_from_u64};
use starbridge_privacy_voting::{
    TALLY_YES_BALLOTS_SLOT, TALLY_YES_SLOT, VOTE_YES, build_cast_vote_action,
    build_record_tally_action, seed_ballot, seed_poll,
};

/// THE FLIPPED TOOTH: a zero-ballot tally forgery is REFUSED by the executor.
///
/// Before the fix this exact turn COMMITTED (the characterization this test
/// used to pin). Now: no ballot exists, no exhibit is carried — the poll
/// program's `CountGe` tally-binding gate refuses the turn fail-closed, and
/// the board stays at zero.
#[test]
fn poll_operator_forges_a_tally_with_zero_ballots_cast() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x9au8; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");

    // Open a poll. NO ballot is minted, NO `cast_vote` is ever submitted.
    seed_poll(&executor, "did the community approve X?");
    let poll = cclerk.cell_id();

    // The tally board starts empty.
    assert_eq!(
        executor.cell_state(poll).unwrap().fields[TALLY_YES_SLOT],
        field_from_u64(0),
        "genesis tally is zero"
    );

    // Forgery attempt 1 — the EMPTY exhibited set: the operator posts a YES
    // tally of 1_000_000 "backed" by zero ballots. `CountGe{threshold: 1}`
    // refuses: the exhibited set has 0 distinct elements.
    let no_ballots = BTreeSet::new();
    let forged = build_record_tally_action(&cclerk, poll, VOTE_YES, 1_000_000, &no_ballots);
    let err = executor
        .submit_action(&cclerk, forged)
        .expect_err("FLIPPED: an unbacked tally must be REFUSED by the ballot-binding gate");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("countge") || msg.contains("count-ge") || msg.contains("program"),
        "the refusal must cite the ballot-binding gate, got: {msg}"
    );

    // Forgery attempt 2 — the WITNESS-LESS raw write (the ORIGINAL pinned
    // forgery shape: a bare `SetField` on the tally slot). Refused fail-closed
    // (the CountGe gate demands the Cleartext exhibit).
    let raw = cclerk.make_action(
        poll,
        "record_tally",
        vec![dregg_app_framework::Effect::SetField {
            cell: poll,
            index: TALLY_YES_SLOT as u64,
            value: field_from_u64(1_000_000),
        }],
    );
    executor
        .submit_action(&cclerk, raw)
        .expect_err("FLIPPED: a witness-less tally write must be REFUSED fail-closed");

    // The board did not move — a million phantom YES votes never happened.
    assert_eq!(
        executor.cell_state(poll).unwrap().fields[TALLY_YES_SLOT],
        field_from_u64(0),
        "the refused forgeries committed nothing"
    );

    // THE HONEST HALF OF THE TOOTH: a LEGITIMATE ballot-backed tally still
    // commits. Seed the companion ballot, cast a real vote on it, then record
    // the tally exhibiting that ballot's id.
    let ballot = seed_ballot(&executor, &cclerk, poll);
    let vote = build_cast_vote_action(&cclerk, ballot, poll, VOTE_YES);
    executor
        .submit_action(&cclerk, vote)
        .expect("a real vote commits on the ballot");

    let counted: BTreeSet<[u8; 32]> = [ballot.as_bytes().to_owned()].into_iter().collect();
    let legit = build_record_tally_action(&cclerk, poll, VOTE_YES, 1, &counted);
    executor
        .submit_action(&cclerk, legit)
        .expect("a ballot-backed tally of 1 commits");

    let state = executor.cell_state(poll).unwrap();
    assert_eq!(
        state.fields[TALLY_YES_SLOT],
        field_from_u64(1),
        "the legitimate tally advanced to 1"
    );
    // The counted ballot set is committed on-ledger — openable by anyone
    // holding the set (the tamper-evidence the README promises).
    assert_eq!(
        state.fields[TALLY_YES_BALLOTS_SLOT],
        dregg_cell::count_ge_set_commitment(&counted),
        "the ballot-set commitment rides the same committed turn"
    );
}

/// RESIDUAL (characterization — passes while the gap is OPEN; if a
/// slot-valued-threshold CountGe lands and the poll program binds tally VALUE
/// to exhibited-set SIZE, this test goes red and must be flipped like its
/// sibling above): an operator exhibiting ONE ballot-shaped id can still post
/// an arbitrarily large tally in one turn. The executor enforces "a moving
/// tally exhibits a non-empty committed ballot set", not
/// "tally <= |exhibited set|" — the threshold is a program-time constant.
/// See the module docs for the precisely-named missing primitive.
#[test]
fn residual_one_exhibited_ballot_still_admits_an_inflated_tally_value() {
    let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x9bu8; 32]);
    let executor = EmbeddedExecutor::new(&cclerk, "default");
    seed_poll(&executor, "residual?");
    let poll = cclerk.cell_id();

    // One fabricated 32-byte "ballot id" — never a real ballot cell.
    let one: BTreeSet<[u8; 32]> = [[0xffu8; 32]].into_iter().collect();
    let inflated = build_record_tally_action(&cclerk, poll, VOTE_YES, 1_000_000, &one);
    executor.submit_action(&cclerk, inflated).expect(
        "RESIDUAL OPEN: tally value is not yet bound to the exhibited set's size \
         (this committing is the pinned gap — flip this test when the \
         slot-valued-threshold CountGe primitive lands)",
    );
    assert_eq!(
        executor.cell_state(poll).unwrap().fields[TALLY_YES_SLOT],
        field_from_u64(1_000_000),
        "the inflated value committed — the residual is open, on-ledger-evident \
         (the 1-element commitment sits next to the million-vote tally)"
    );
}
