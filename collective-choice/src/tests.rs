//! The teeth. Each test drives a real turn through the embedded verified
//! executor, so every refusal below is an executor `= none` (or an engine gate),
//! not a mock.

use super::*;
use dregg_intent::agent_mandate::{Auth, Caveat};

const ALICE: [u8; 32] = [1u8; 32];
const BOB: [u8; 32] = [2u8; 32];
const CAROL: [u8; 32] = [3u8; 32];
const DAVE: [u8; 32] = [4u8; 32];

fn engine() -> CollectiveChoice {
    CollectiveChoice::new([9u8; 32])
}

fn spec(question: &str, options: usize, electorate: Vec<[u8; 32]>, quorum: u64) -> PollSpec {
    PollSpec {
        question: question.into(),
        options: (0..options).map(|i| format!("option-{i}")).collect(),
        electorate,
        quorum_m: quorum,
    }
}

// ── one-vote / double-refused (the nullifier bites) ─────────────────────────

#[test]
fn eligible_votes_once_double_vote_refused_by_nullifier() {
    let mut e = engine();
    let poll = e.open_poll(spec("ship it?", 2, vec![ALICE], 1)).unwrap();
    let cap = e.issue_ballot(poll, ALICE).unwrap();

    // First vote: accepted; the tally records it.
    e.cast(poll, &cap, 0).expect("first vote commits");
    assert_eq!(e.tally(poll).unwrap().per_option, vec![1, 0]);

    // Second vote on the same ballot: REFUSED by the nullifier set (the
    // consumed-ballot-proof depth of one-vote).
    match e.cast(poll, &cap, 1) {
        Err(VoteError::DoubleVote) => {}
        other => panic!("double vote must be refused by the nullifier, got {other:?}"),
    }
    // The board did not move.
    assert_eq!(e.tally(poll).unwrap().per_option, vec![1, 0]);
}

// ── ineligible voter (no electorate cap) is refused ─────────────────────────

#[test]
fn ineligible_voter_cannot_get_a_ballot() {
    let mut e = engine();
    let poll = e
        .open_poll(spec("members only?", 2, vec![ALICE], 1))
        .unwrap();
    // Alice is in the electorate; Bob is not.
    assert!(e.issue_ballot(poll, ALICE).is_ok());
    match e.issue_ballot(poll, BOB) {
        Err(VoteError::Ineligible) => {}
        other => panic!("a non-electorate voter must be refused, got {other:?}"),
    }
}

// ── tally is verifiable (light client recomputes) + forge refused ───────────

#[test]
fn tally_is_light_client_verifiable_and_a_forge_is_refused() {
    let mut e = engine();
    let poll = e
        .open_poll(spec("what next?", 3, vec![ALICE, BOB, CAROL], 1))
        .unwrap();
    for v in [ALICE, BOB, CAROL] {
        let cap = e.issue_ballot(poll, v).unwrap();
        // Alice + Bob pick option 0, Carol picks option 2.
        let opt = if v == CAROL { 2 } else { 0 };
        e.cast(poll, &cap, opt).expect("vote commits");
    }

    // The executor's stored monotone tally and the light-client recompute AGREE
    // — nobody stuffed the board.
    let stored = e.tally(poll).unwrap();
    let recomputed = e.light_client_tally(poll).unwrap();
    assert_eq!(stored, recomputed);
    assert_eq!(stored.per_option, vec![2, 0, 1]);
    assert_eq!(stored.total, 3);

    // FORGE: try to shrink option-0's tally 2 → 1 directly on the poll cell. The
    // `Monotonic(TALLY_0)` caveat is re-enforced by the executor — REFUSED.
    let poll_cell = poll.0;
    let forge = build_tally_bump(&e.clerk, poll_cell, 0, 1);
    let err = e
        .exec
        .submit_action(&e.clerk, forge)
        .expect_err("a tally decrease must be refused");
    let msg = format!("{err}").to_lowercase();
    assert!(
        msg.contains("monotonic") || msg.contains("program"),
        "forge must cite the Monotonic caveat, got: {msg}"
    );
    // The board is unchanged after the refused forge.
    assert_eq!(e.tally(poll).unwrap().per_option, vec![2, 0, 1]);
}

// ── SECURITY: a single actor CANNOT forge a quorum (the CountGe gate) ────────
//
// Before the fix, the quorum was `AffineLe { M·RESOLVED − Σ TALLY ≤ 0 }` over
// `Monotonic` tally slots. `Monotonic` admits a single `0 → M` jump, so ONE
// actor authoring ONE tally-bump turn armed `RESOLVED` with ZERO distinct
// voters (driven: the pre-fix build resolved here). The `CountGe` gate now
// guards `RESOLVED` on the DISTINCT quorum-approver set, so the same attack is
// refused while a genuine quorum of M distinct voters still resolves.

#[test]
fn forged_quorum_single_actor_inflating_a_tally_slot_is_refused() {
    let mut e = engine();
    // Quorum M = 3 over a 3-voter electorate. We cast NO real votes — there are
    // ZERO distinct approvers.
    let poll = e
        .open_poll(spec("forge?", 2, vec![ALICE, BOB, CAROL], 3))
        .unwrap();
    let poll_cell = poll.0;

    // The raw tally board is still `Monotonic` (it is the human-readable count,
    // no longer the gate): a single `0 -> M` jump on ONE slot is still ACCEPTED
    // at the tally level. This is precisely the arithmetic aliasing the old gate
    // trusted.
    let forge = build_tally_bump(&e.clerk, poll_cell, 0, 3);
    e.exec
        .submit_action(&e.clerk, forge)
        .expect("Monotonic still admits the raw tally jump");
    assert_eq!(e.tally(poll).unwrap().per_option, vec![3, 0]);

    // But `resolve` is now gated by `CountGe` over the DISTINCT quorum-approver
    // set. No genuine votes were cast, so the exhibited set is empty and does
    // not open the (untouched) commitment slot — the decision-turn is REFUSED.
    assert!(
        e.resolve(poll).unwrap().is_none(),
        "FORGED QUORUM MUST BE REFUSED: inflating a tally slot cannot arm RESOLVED"
    );

    // Inflating a SECOND slot (one actor writing multiple slots to fake M) also
    // fails to resolve — the gate reads distinct voters, not the tally sum.
    let forge2 = build_tally_bump(&e.clerk, poll_cell, 1, 3);
    e.exec.submit_action(&e.clerk, forge2).unwrap();
    assert!(
        e.resolve(poll).unwrap().is_none(),
        "spreading the forge across slots still cannot arm RESOLVED"
    );
}

#[test]
fn genuine_quorum_of_m_distinct_voters_still_resolves() {
    let mut e = engine();
    // M = 3 distinct voters is the genuine quorum.
    let poll = e
        .open_poll(spec("proceed?", 2, vec![ALICE, BOB, CAROL], 3))
        .unwrap();

    // Two distinct voters: below quorum, still refused (the CountGe exhibit has
    // 2 < 3 distinct elements).
    for v in [ALICE, BOB] {
        let cap = e.issue_ballot(poll, v).unwrap();
        e.cast(poll, &cap, 0).unwrap();
    }
    assert!(
        e.resolve(poll).unwrap().is_none(),
        "2 < 3 distinct voters must not resolve"
    );

    // The third DISTINCT voter reaches quorum — the decision-turn now commits.
    let c = e.issue_ballot(poll, CAROL).unwrap();
    e.cast(poll, &c, 0).unwrap();
    let decision = e
        .resolve(poll)
        .unwrap()
        .expect("3 distinct voters exhibit the CountGe quorum — RESOLVED arms");
    assert_eq!(decision.winner, 0);
    assert_eq!(decision.winner_tally, 3);
}

// ── quorum gate: resolve only certifies at threshold ────────────────────────

#[test]
fn quorum_affine_le_gates_resolution() {
    let mut e = engine();
    // Quorum M = 2 over a 3-voter electorate.
    let poll = e
        .open_poll(spec("proposal?", 2, vec![ALICE, BOB, CAROL], 2))
        .unwrap();

    // One vote: below quorum. The decision-turn is REFUSED by the quorum
    // `AffineLe` (`2·RESOLVED − Σ TALLY ≤ 0` fails for RESOLVED=1, ΣTALLY=1).
    let a = e.issue_ballot(poll, ALICE).unwrap();
    e.cast(poll, &a, 0).unwrap();
    assert!(
        e.resolve(poll).unwrap().is_none(),
        "below quorum must not resolve"
    );

    // A second vote reaches quorum: the decision-turn now COMMITS.
    let b = e.issue_ballot(poll, BOB).unwrap();
    e.cast(poll, &b, 0).unwrap();
    let decision = e
        .resolve(poll)
        .unwrap()
        .expect("at quorum the decision-turn commits");
    assert_eq!(decision.winner, 0);
    assert_eq!(decision.winner_tally, 2);
    assert_eq!(decision.total, 2);

    // Idempotent once resolved.
    assert!(e.resolve(poll).unwrap().is_some());
}

// ── delegation (liquid democracy): counts once + cannot amplify ─────────────

#[test]
fn delegated_vote_counts_once_and_cannot_amplify() {
    let mut e = engine();
    let poll = e
        .open_poll(spec("delegate?", 2, vec![ALICE, BOB], 1))
        .unwrap();

    // Alice holds a ballot cap and delegates it to Dave (a delegate need not be
    // in the electorate — that is the point of liquid democracy).
    let alice_cap = e.issue_ballot(poll, ALICE).unwrap();
    let dave_cap = e.delegate(&alice_cap, DAVE);

    // Dave votes with the delegated cap on Alice's ballot: counts ONCE.
    e.cast(poll, &dave_cap, 1).expect("delegate's vote commits");
    assert_eq!(e.tally(poll).unwrap().per_option, vec![0, 1]);

    // Alice can no longer also vote her ballot — the delegated vote already
    // consumed it (exactly once, at the nullifier depth).
    match e.cast(poll, &alice_cap, 0) {
        Err(VoteError::DoubleVote) => {}
        other => panic!("a delegated ballot must count exactly once, got {other:?}"),
    }

    // NON-AMPLIFICATION: the delegate tree never out-authorizes the delegator.
    let tree = CollectiveChoice::delegation_tree(&alice_cap, &dave_cap);
    assert!(
        tree.no_amplify(),
        "no descendant may out-authorize the root"
    );
    assert!(
        tree.well_attenuated(&[CAST_METHOD]),
        "every edge must be a genuine strict attenuation"
    );

    // Even when a delegate REQUESTS wider rights and a bigger budget,
    // `sub_delegate` can only narrow: the child gets `keep ∩ requested`,
    // `min(budget, ..)`, never more.
    let mut greedy: Rights = BTreeSet::new();
    greedy.insert(Auth::Read);
    greedy.insert(Auth::Write);
    greedy.insert(Auth::Grant);
    let amplified = alice_cap.mandate.sub_delegate(
        CellId::from_bytes(DAVE),
        &greedy,
        1_000_000,
        &Caveat::any(),
    );
    assert!(
        !amplified.keep.contains(&Auth::Grant) && !amplified.keep.contains(&Auth::Write),
        "a sub-delegation cannot add rights the delegator never held"
    );
    assert!(
        amplified.budget <= alice_cap.mandate.budget,
        "a sub-delegation cannot raise the budget"
    );
}

// ── the per-option gate (the constitutional threshold shape) ─────────────────

#[test]
fn gated_poll_refuses_resolution_until_the_gated_option_reaches_m() {
    let mut e = engine();
    // Gate on option 1 ("approve") with M = 2, over a 3-voter electorate.
    let poll = e
        .open_poll_gated(spec("enact?", 2, vec![ALICE, BOB, CAROL], 2), 1)
        .unwrap();

    // TWO votes land on option 0 — total (2) reaches M, but the GATED option has
    // 0. The old Σ-TALLY gate would arm RESOLVED here; the per-option gate
    // (`2·RESOLVED − TALLY_1 ≤ 0`) refuses the decision-turn.
    let a = e.issue_ballot(poll, ALICE).unwrap();
    e.cast(poll, &a, 0).unwrap();
    let b = e.issue_ballot(poll, BOB).unwrap();
    e.cast(poll, &b, 0).unwrap();
    assert_eq!(e.tally(poll).unwrap().total, 2);
    assert!(
        e.resolve(poll).unwrap().is_none(),
        "M ballots on OTHER options must not arm a per-option-gated RESOLVED"
    );

    // Votes on the gated option itself... one is still below M.
    let c = e.issue_ballot(poll, CAROL).unwrap();
    e.cast(poll, &c, 1).unwrap();
    assert!(
        e.resolve(poll).unwrap().is_none(),
        "gated option at 1 < M must still refuse"
    );
}

#[test]
fn gated_poll_resolves_once_the_gated_option_itself_reaches_m() {
    let mut e = engine();
    let poll = e
        .open_poll_gated(spec("enact?", 2, vec![ALICE, BOB, CAROL], 2), 1)
        .unwrap();
    for v in [ALICE, BOB] {
        let cap = e.issue_ballot(poll, v).unwrap();
        e.cast(poll, &cap, 1).unwrap();
    }
    let decision = e
        .resolve(poll)
        .unwrap()
        .expect("gated option at M commits the decision-turn");
    assert_eq!(decision.winner, 1);
    assert_eq!(decision.winner_tally, 2);
}

#[test]
fn gated_poll_with_out_of_range_gate_is_refused() {
    let mut e = engine();
    match e.open_poll_gated(spec("bad gate", 2, vec![ALICE], 1), 2) {
        Err(VoteError::BadPollSpec(_)) => {}
        other => panic!("an out-of-range gate option must be refused, got {other:?}"),
    }
}

// ── WEIGHTED casts (the holding-weight ballot) ──────────────────────────────
//
// A holding-weight ballot is worth its GRANTED weight W (in deployment the
// Lean-proven `grantWeightCore` verdict): `cast_weighted` bumps the option's
// `Monotonic` tally slot by exactly W through a real executor turn, under the
// SAME one-ballot-per-voter gates as `cast` (WriteOnce(VOTE) + the nullifier).
// Lean mirror: `Dregg2.Apps.MultisigVote` §10 (`castVoteW`).

#[test]
fn weighted_cast_bumps_the_tally_by_exactly_the_granted_weight() {
    let mut e = engine();
    let poll = e
        .open_poll_weighted(spec("weighted?", 2, vec![], 100))
        .unwrap();
    let cap = e.issue_ballot(poll, ALICE).unwrap();
    e.cast_weighted(poll, &cap, 1, 77)
        .expect("weighted cast commits");
    // The board moved by exactly 77 — not 1, not 0.
    assert_eq!(e.tally(poll).unwrap().per_option, vec![0, 77]);
    // The light client replaying the cast log agrees with the stored board.
    assert_eq!(e.light_client_tally(poll).unwrap(), e.tally(poll).unwrap());
}

#[test]
fn weighted_double_cast_by_the_same_voter_is_refused_and_the_board_unmoved() {
    let mut e = engine();
    let poll = e
        .open_poll_weighted(spec("double?", 2, vec![], 100))
        .unwrap();
    let cap = e.issue_ballot(poll, ALICE).unwrap();
    e.cast_weighted(poll, &cap, 0, 50)
        .expect("first weighted cast commits");
    // A second cast on the same ballot — at ANY weight, any option — dies at
    // the nullifier. Weights change what a ballot is worth, never how many
    // ballots a voter has.
    match e.cast_weighted(poll, &cap, 1, 999) {
        Err(VoteError::DoubleVote) => {}
        other => panic!("second weighted cast must be refused, got {other:?}"),
    }
    assert_eq!(e.tally(poll).unwrap().per_option, vec![50, 0]);
}

#[test]
fn zero_weight_cast_is_refused_and_does_not_burn_the_ballot() {
    let mut e = engine();
    let poll = e.open_poll_weighted(spec("zero?", 2, vec![], 10)).unwrap();
    let cap = e.issue_ballot(poll, ALICE).unwrap();
    // A zero-weight cast is refused OUTRIGHT: no tally move…
    match e.cast_weighted(poll, &cap, 0, 0) {
        Err(VoteError::ZeroWeight) => {}
        other => panic!("a zero-weight cast must be refused, got {other:?}"),
    }
    assert_eq!(e.tally(poll).unwrap().per_option, vec![0, 0]);
    // …and crucially the ballot is NOT consumed — a later genuine grant still
    // casts (the refusal fired before the nullifier / WriteOnce turn).
    e.cast_weighted(poll, &cap, 0, 50)
        .expect("the zero-weight refusal must not burn the ballot");
    assert_eq!(e.tally(poll).unwrap().per_option, vec![50, 0]);
}

#[test]
fn weight_conservation_board_equals_the_sum_of_granted_weights() {
    let mut e = engine();
    let poll = e
        .open_poll_weighted(spec("conserve?", 2, vec![], 500))
        .unwrap();
    // Three voters with grants 50 / 100 / 25 — the board must be EXACTLY their
    // sum, per option and in total, and the light-client replay must agree.
    for (v, w, opt) in [(ALICE, 50u64, 0usize), (BOB, 100, 0), (CAROL, 25, 1)] {
        let cap = e.issue_ballot(poll, v).unwrap();
        e.cast_weighted(poll, &cap, opt, w)
            .expect("weighted cast commits");
    }
    let stored = e.tally(poll).unwrap();
    assert_eq!(stored.per_option, vec![150, 25]);
    assert_eq!(
        stored.total, 175,
        "tally total = Σ granted weights of counted ballots"
    );
    assert_eq!(e.light_client_tally(poll).unwrap(), stored);
}

#[test]
fn weighted_quorum_resolves_on_weight_not_headcount() {
    let mut e = engine();
    // Weight quorum 120. One voter of weight 50: below quorum — the AffineLe
    // refuses the decision-turn.
    let poll = e
        .open_poll_weighted(spec("weight quorum?", 2, vec![], 120))
        .unwrap();
    let a = e.issue_ballot(poll, ALICE).unwrap();
    e.cast_weighted(poll, &a, 0, 50).unwrap();
    assert!(
        e.resolve(poll).unwrap().is_none(),
        "50 < 120 weight must not resolve"
    );
    // A second voter of weight 100 clears the WEIGHT quorum with only TWO
    // distinct voters — the gate reads weight, not headcount.
    let b = e.issue_ballot(poll, BOB).unwrap();
    e.cast_weighted(poll, &b, 0, 100).unwrap();
    let decision = e
        .resolve(poll)
        .unwrap()
        .expect("150 >= 120 weight resolves");
    assert_eq!(decision.winner, 0);
    assert_eq!(decision.winner_tally, 150);
}

#[test]
fn one_whale_is_a_legitimate_weight_quorum() {
    let mut e = engine();
    let poll = e
        .open_poll_weighted(spec("whale?", 2, vec![], 120))
        .unwrap();
    // ONE voter whose grant (150) clears the whole weight quorum: resolves with
    // a single distinct approver (the CountGe exhibits one GENUINE voter; the
    // AffineLe reads the weight). This is exactly what a distinct-voter quorum
    // would refuse — the weighted poll is a different, deliberate gate.
    let cap = e.issue_ballot(poll, ALICE).unwrap();
    e.cast_weighted(poll, &cap, 1, 150).unwrap();
    let decision = e.resolve(poll).unwrap().expect("one whale >= 120 resolves");
    assert_eq!(decision.winner, 1);
    assert_eq!(decision.winner_tally, 150);
}

#[test]
fn weighted_poll_with_no_genuine_voter_still_cannot_resolve() {
    let mut e = engine();
    // The CountGe floor survives weighting: with ZERO casts, a forged tally
    // jump on the Monotonic slot cannot arm RESOLVED (no distinct approver to
    // exhibit), exactly as in the unweighted engine.
    let poll = e
        .open_poll_weighted(spec("forge weighted?", 2, vec![], 100))
        .unwrap();
    let forge = build_tally_bump(&e.clerk, poll.0, 0, 500);
    e.exec
        .submit_action(&e.clerk, forge)
        .expect("Monotonic still admits the raw jump");
    assert!(
        e.resolve(poll).unwrap().is_none(),
        "a forged weighted tally with zero genuine voters must not resolve"
    );
}

#[test]
fn weighted_poll_mints_ballots_dynamically_closed_polls_still_refuse() {
    let mut e = engine();
    // A weighted (holding-weight) poll's eligibility is the caller's verified
    // grant, so the ballot mint is DYNAMIC: DAVE was never pre-enrolled.
    let weighted = e
        .open_poll_weighted(spec("dynamic?", 2, vec![], 10))
        .unwrap();
    let cap = e.issue_ballot(weighted, DAVE).expect("dynamic mint");
    e.cast_weighted(weighted, &cap, 0, 10).unwrap();
    // The closed-electorate poll is unchanged: a non-member is still refused.
    let closed = e.open_poll(spec("closed?", 2, vec![ALICE], 1)).unwrap();
    match e.issue_ballot(closed, DAVE) {
        Err(VoteError::Ineligible) => {}
        other => panic!("closed-electorate polls must still refuse, got {other:?}"),
    }
}

#[test]
fn weighted_gated_poll_gates_on_the_gated_options_weight() {
    let mut e = engine();
    // Gate on option 1 with weight quorum 100 (the constitutional Threshold
    // shape, weighted): weight landing on OTHER options never arms RESOLVED.
    let poll = e
        .open_poll_weighted_gated(spec("enact weighted?", 2, vec![], 100), 1)
        .unwrap();
    let a = e.issue_ballot(poll, ALICE).unwrap();
    e.cast_weighted(poll, &a, 0, 500).unwrap();
    assert!(
        e.resolve(poll).unwrap().is_none(),
        "500 weight on the OTHER option must not arm a gated RESOLVED"
    );
    let b = e.issue_ballot(poll, BOB).unwrap();
    e.cast_weighted(poll, &b, 1, 100).unwrap();
    let decision = e
        .resolve(poll)
        .unwrap()
        .expect("the gated option at 100 >= 100 weight resolves");
    assert_eq!(decision.winner, 0, "winner is argmax (500 on option 0)");
}

#[test]
fn unweighted_cast_is_exactly_weight_one() {
    let mut e = engine();
    let poll = e.open_poll(spec("unit?", 2, vec![ALICE, BOB], 2)).unwrap();
    let a = e.issue_ballot(poll, ALICE).unwrap();
    e.cast(poll, &a, 0).unwrap();
    let b = e.issue_ballot(poll, BOB).unwrap();
    e.cast_weighted(poll, &b, 0, 1).unwrap();
    // `cast` and `cast_weighted(_, 1)` are the same law: the board counts 2.
    assert_eq!(e.tally(poll).unwrap().per_option, vec![2, 0]);
    assert_eq!(e.light_client_tally(poll).unwrap().total, 2);
}

#[test]
fn weighted_tally_overflow_is_refused_without_burning_the_ballot() {
    let mut e = engine();
    let poll = e
        .open_poll_weighted(spec("overflow tally?", 2, vec![], 10))
        .unwrap();
    // A whale nearly fills option 0's u64 tally domain.
    let a = e.issue_ballot(poll, ALICE).unwrap();
    e.cast_weighted(poll, &a, 0, u64::MAX - 10).unwrap();
    // BOB's bump would exceed u64 — refused fail-closed (never wrapped or
    // saturated), BEFORE the ballot turn…
    let b = e.issue_ballot(poll, BOB).unwrap();
    match e.cast_weighted(poll, &b, 0, 20) {
        Err(VoteError::Executor(m)) => assert!(m.contains("overflow"), "got: {m}"),
        other => panic!("an overflowing bump must be refused, got {other:?}"),
    }
    // …so BOB's ballot is NOT burned: the same cap still casts on the other
    // option's (unfilled) slot.
    e.cast_weighted(poll, &b, 1, 5)
        .expect("the overflow refusal must not burn the ballot");
    assert_eq!(e.tally(poll).unwrap().per_option, vec![u64::MAX - 10, 5]);
}

#[test]
fn weighted_quorum_above_i64_max_is_refused_at_open() {
    // The AffineLe coefficient is an i64: a weight quorum above i64::MAX would
    // wrap NEGATIVE and make the quorum gate vacuously true. Refused at open,
    // fail-closed.
    let mut e = engine();
    match e.open_poll_weighted(spec("overflow?", 2, vec![], u64::MAX)) {
        Err(VoteError::BadPollSpec(_)) => {}
        other => panic!("an i64-overflowing weight quorum must be refused, got {other:?}"),
    }
}

// ── the shape spween-dregg / dregg-governance consume ───────────────────────

#[test]
fn vote_engine_trait_is_object_consumable() {
    // Both lanes hold a `&mut dyn VoteEngine<Error = VoteError>` — open, cast,
    // tally, resolve, nothing more.
    let mut e = engine();
    let poll = e.open_poll(spec("branch?", 3, vec![ALICE], 1)).unwrap();
    let cap = e.issue_ballot(poll, ALICE).unwrap();
    let dyn_engine: &mut dyn VoteEngine<Error = VoteError> = &mut e;
    dyn_engine.cast(poll, &cap, 2).unwrap();
    assert_eq!(dyn_engine.tally(poll).unwrap().per_option, vec![0, 0, 1]);
    assert!(dyn_engine.resolve(poll).unwrap().is_some());
}
