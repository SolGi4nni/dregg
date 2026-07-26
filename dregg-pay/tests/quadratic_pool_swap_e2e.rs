//! End-to-end driven test of the **quadratically-weighted, all-or-nothing, market-price**
//! pile→fuel swap — the shape ember specified:
//!
//! > "the votes should be quadratic weighted on how much they paid into the
//! > proposed-to-be-swapped-pool, and it should be all-or-nothing swap at market price
//! > accepting whatever slippage"
//!
//! MOCK/devnet only: no real funds, no network, no key held by `dregg-pay` (the operator's
//! signer is a throwaway `MockSigner`, and mainnet remains an operator-config flip).
//!
//! The chain driven here is: **contribute → pin the pool → propose → weighted vote →
//! authorize → sign → swap → retire the pool**, with an adversarial pole for every new
//! rule:
//!
//! * a contributor's weight is `isqrt(what they paid)` — quadratic, not linear;
//! * someone who paid NOTHING is refused a ballot outright;
//! * a contribution made after the pin buys no weight and does not grow the amount;
//! * below the WEIGHT quorum there is no authorization, so no swap can execute;
//! * a pile short of the whole pool refuses entirely — no partial fill;
//! * the market authorization carries NO floor, so a fill a floored proposal would have
//!   refused executes anyway — and the receipt records what the slippage was;
//! * a pool is retired exactly once.
//!
//! Run: `cargo test -p dregg-pay --test quadratic_pool_swap_e2e -- --test-threads=4`.

use dregg_pay::{
    Asset, ContributionOutcome, DepositAddress, GovernanceAuthority, InMemoryTreasuryStore,
    JupiterSwap, LiquidityGovernance, MARKET_MIN_OUT, MockSigner, MockSwapVenue, PayConfig,
    PaymentReceived, PaymentRef, PoolError, SwapError, SwapPool, Treasury, UserId,
    quadratic_weight,
};

/// Per-user HD-derived deposit addresses — this crate's per-user identity, and directly
/// the 32-byte voter key.
const ALICE: DepositAddress = DepositAddress([0xA1u8; 32]);
const BOB: DepositAddress = DepositAddress([0xB2u8; 32]);
const CAROL: DepositAddress = DepositAddress([0xC3u8; 32]);
/// A freeloader: in the system, never paid into the pile.
const MALLORY: DepositAddress = DepositAddress([0x77u8; 32]);

fn config() -> PayConfig {
    // THROWAWAY seed, MOCK $DREGG + MOCK USDC mints — never mainnet.
    let seed = *b"dregg-pay QUADRATIC throwaway seed - not real!!!";
    let mut c = PayConfig::devnet_mock(seed, [0x11u8; 32], DepositAddress([0xEEu8; 32]), 1_000_000);
    c.usdc_mint = [0x22u8; 32];
    c
}

fn payment(user: &str, addr: DepositAddress, amount: u64, reference: &str) -> PaymentReceived {
    PaymentReceived {
        user: UserId::from(user),
        deposit_address: addr,
        asset: Asset::Dregg,
        amount,
        reference: PaymentRef(reference.to_string()),
    }
}

/// alice 1M (weight 1000), bob 4M (weight 2000), carol 9M (weight 3000).
/// Pool total 14M atomic `$DREGG`; total weight 6000.
fn funded_pool() -> (SwapPool, Treasury<InMemoryTreasuryStore>) {
    let pool = SwapPool::new();
    let treasury = Treasury::new(InMemoryTreasuryStore::new(), 6);
    for (user, addr, amount, reference) in [
        ("alice", ALICE, 1_000_000u64, "tx-alice-1"),
        ("bob", BOB, 4_000_000, "tx-bob-1"),
        ("carol", CAROL, 9_000_000, "tx-carol-1"),
    ] {
        assert!(matches!(
            pool.record_payment(&payment(user, addr, amount, reference), &treasury),
            ContributionOutcome::Contributed { .. }
        ));
    }
    assert_eq!(treasury.dregg_balance(), 14_000_000, "the pile accumulated");
    assert_eq!(pool.total(), 14_000_000, "and it is fully attributed");
    (pool, treasury)
}

#[test]
fn quadratic_pool_vote_authorizes_an_all_or_nothing_market_swap() {
    let c = config();
    println!("\n=== quadratic pool swap — contribute → pin → vote → market swap ===");

    let (pool, treasury) = funded_pool();
    let authority = GovernanceAuthority::from_seed([7u8; 32]);
    let mut gov = LiquidityGovernance::new([9u8; 32], authority, c.mint, c.usdc_mint);
    let authority_pk = gov.authority_public_key();

    // ── 1. PIN the pool. The snapshot is the electorate, the weights, AND the amount. ──
    let pinned = pool.snapshot();
    assert_eq!(pinned.total(), 14_000_000);
    assert_eq!(pinned.total_weight(), Some(6_000));
    for (addr, paid, weight) in pinned.contributors() {
        println!("  contributor {addr} paid {paid} → weight {weight}");
        assert_eq!(weight, quadratic_weight(paid));
    }

    // THE QUADRATIC RULE: bob paid 4× alice and votes with 2×; carol paid 9× and votes
    // with 3×. A linear weight would read 4× and 9×.
    assert_eq!(pinned.weight(&ALICE), 1_000);
    assert_eq!(pinned.weight(&BOB), 2_000);
    assert_eq!(pinned.weight(&CAROL), 3_000);
    assert_eq!(
        pinned.weight(&BOB),
        2 * pinned.weight(&ALICE),
        "4× the stake is 2× the vote, not 4×"
    );

    // ── 2. PROPOSE at a WEIGHT quorum of 4000 (an operator parameter, chosen here only
    //       to sit strictly between the 3000 of alice+bob and the 6000 of everyone). ──
    let proposal = gov
        .propose_market_swap("swap the whole pool to fuel at market?", pinned, 4_000)
        .unwrap();
    assert_eq!(
        proposal.amount(),
        14_000_000,
        "ALL of the pool, not an operator-chosen slice"
    );

    // ── 3. VOTE. Weight comes from the pinned pool, never from the voter. ──
    let a = gov.issue_pool_ballot(&proposal, ALICE).unwrap();
    let b = gov.issue_pool_ballot(&proposal, BOB).unwrap();
    let cc = gov.issue_pool_ballot(&proposal, CAROL).unwrap();

    assert_eq!(gov.vote_market(&proposal, &a, true).unwrap(), 1_000);
    assert!(
        gov.finalize_market_swap(&proposal).unwrap().is_none(),
        "1000 weight < 4000 quorum must not authorize"
    );
    assert_eq!(gov.vote_market(&proposal, &b, true).unwrap(), 2_000);
    assert!(
        gov.finalize_market_swap(&proposal).unwrap().is_none(),
        "3000 weight is still below the 4000 quorum"
    );
    assert_eq!(gov.vote_market(&proposal, &cc, true).unwrap(), 3_000);

    let tally = gov.market_tally(&proposal).unwrap();
    println!("weighted tally [reject, approve] = {:?}", tally.per_option);
    assert_eq!(
        tally.per_option,
        vec![0, 6_000],
        "the board holds WEIGHT, not a headcount of 3"
    );

    // A double vote on the same ballot is a real executor refusal, at any weight.
    assert!(
        gov.vote_market(&proposal, &a, true).is_err(),
        "one ballot, one cast — a second is refused"
    );
    assert_eq!(
        gov.market_tally(&proposal).unwrap().per_option,
        vec![0, 6_000],
        "the refused double vote added nothing"
    );

    // ── 4. AUTHORIZE: market price means NO floor. ──
    let auth = gov
        .finalize_market_swap(&proposal)
        .unwrap()
        .expect("6000 >= 4000 weight authorizes");
    assert_eq!(auth.amount, 14_000_000, "all or nothing");
    assert_eq!(
        auth.min_out, MARKET_MIN_OUT,
        "market price: no slippage floor is minted"
    );
    assert_eq!(MARKET_MIN_OUT, 0);
    assert!(auth.verify(&authority_pk));

    // ── 5. SIGN + EXECUTE at whatever the venue gives. ──
    let venue = MockSwapVenue::new(5, 1_000); // $0.005/$DREGG → 70_000 atomic USDC
    let swap = JupiterSwap::new(venue, c.mint, c.usdc_mint, authority_pk);
    let signer = MockSigner::from_seed([8u8; 32]); // operator-held; NEVER in dregg-pay
    let out = swap.execute(&auth, &signer, &treasury).unwrap();
    println!(
        "swap: {} $DREGG → {} USDC (quoted {}, slippage {} bps)",
        out.dregg_in, out.usdc_out, out.quoted_out, out.slippage_bps
    );
    assert_eq!(out.dregg_in, 14_000_000);
    assert_eq!(out.usdc_out, 70_000);
    assert_eq!(out.quoted_out, 70_000, "the receipt carries the quote");
    assert_eq!(out.slippage_bps, 0, "…and the realized slippage against it");
    assert_eq!(treasury.dregg_balance(), 0, "the whole pool went");
    assert_eq!(treasury.usdc_balance(), 70_000, "fuel filled");

    // ── 6. RETIRE the pool — once. ──
    assert_eq!(pool.close(&proposal.pool).unwrap(), 1);
    assert_eq!(pool.total(), 0, "the swapped pool is retired");
    assert_eq!(pool.contributed(&CAROL), 0);
    assert!(
        matches!(
            pool.close(&proposal.pool),
            Err(PoolError::StaleSnapshot { .. })
        ),
        "one passed vote cannot retire the ledger twice"
    );
    println!("=== quadratic pool swap invariants held ===\n");
}

#[test]
fn a_non_contributor_is_refused_a_ballot_and_never_reaches_the_board() {
    // THE ELIGIBILITY POLE: weight is a function of contribution, so zero contribution is
    // zero weight, and zero weight is not a vote — it is a refusal, before any ballot is
    // minted.
    let c = config();
    let (pool, _treasury) = funded_pool();
    let mut gov = LiquidityGovernance::new(
        [9u8; 32],
        GovernanceAuthority::from_seed([7u8; 32]),
        c.mint,
        c.usdc_mint,
    );
    let proposal = gov
        .propose_market_swap("swap?", pool.snapshot(), 1)
        .unwrap();

    assert_eq!(proposal.weight_of(&MALLORY), 0, "she paid nothing");
    assert!(
        matches!(
            gov.issue_pool_ballot(&proposal, MALLORY),
            Err(dregg_pay::GovernanceError::NoContribution { .. })
        ),
        "a non-contributor must not even be issued a ballot"
    );
    assert_eq!(
        gov.market_tally(&proposal).unwrap().per_option,
        vec![0, 0],
        "nothing reached the board"
    );

    // And she cannot ride a real contributor's ballot: the weight is recomputed from the
    // ballot's OWN voter identity against the pinned pool, never supplied by the caller.
    let alice_ballot = gov.issue_pool_ballot(&proposal, ALICE).unwrap();
    assert_eq!(
        gov.vote_market(&proposal, &alice_ballot, true).unwrap(),
        1_000
    );
    assert_eq!(
        gov.market_tally(&proposal).unwrap().per_option,
        vec![0, 1_000],
        "alice's ballot is worth alice's stake and nothing more"
    );
}

#[test]
fn an_empty_pool_cannot_be_proposed() {
    // Fail closed: an empty pool would mint an authorization for zero at a quorum nobody
    // could reach.
    let c = config();
    let pool = SwapPool::new();
    let mut gov = LiquidityGovernance::new(
        [9u8; 32],
        GovernanceAuthority::from_seed([7u8; 32]),
        c.mint,
        c.usdc_mint,
    );
    assert!(matches!(
        gov.propose_market_swap("swap nothing?", pool.snapshot(), 1),
        Err(dregg_pay::GovernanceError::EmptyPool)
    ));
    // And a zero WEIGHT quorum is refused by the engine — it would pass unconditionally.
    let (funded, _t) = funded_pool();
    assert!(matches!(
        gov.propose_market_swap("swap?", funded.snapshot(), 0),
        Err(dregg_pay::GovernanceError::Vote(_))
    ));
}

#[test]
fn a_contribution_after_the_pin_buys_no_weight_and_does_not_grow_the_amount() {
    // THE PIN POLE: seeing a vote in flight and buying in must not buy influence over it,
    // and must not enlarge what the vote authorizes.
    let c = config();
    let (pool, treasury) = funded_pool();
    let mut gov = LiquidityGovernance::new(
        [9u8; 32],
        GovernanceAuthority::from_seed([7u8; 32]),
        c.mint,
        c.usdc_mint,
    );
    let proposal = gov
        .propose_market_swap("swap the pool?", pool.snapshot(), 1_000)
        .unwrap();

    // Mallory buys in AFTER the proposal opened — a huge stake, far outweighing everyone.
    assert!(matches!(
        pool.record_payment(
            &payment("mallory", MALLORY, 900_000_000, "tx-mallory-late"),
            &treasury
        ),
        ContributionOutcome::Contributed { .. }
    ));
    assert_eq!(pool.weight(&MALLORY), 30_000, "live, she would dominate");

    // …but not in THIS proposal.
    assert_eq!(proposal.weight_of(&MALLORY), 0, "the pin holds");
    assert!(gov.issue_pool_ballot(&proposal, MALLORY).is_err());
    assert_eq!(
        proposal.amount(),
        14_000_000,
        "the authorized amount did not grow with the late payment"
    );

    // The passed vote authorizes exactly the pinned pool, leaving the late contribution
    // in the pile for the NEXT pool.
    let a = gov.issue_pool_ballot(&proposal, ALICE).unwrap();
    gov.vote_market(&proposal, &a, true).unwrap();
    let auth = gov.finalize_market_swap(&proposal).unwrap().unwrap();
    assert_eq!(auth.amount, 14_000_000);

    let swap = JupiterSwap::new(
        MockSwapVenue::new(5, 1_000),
        c.mint,
        c.usdc_mint,
        gov.authority_public_key(),
    );
    let signer = MockSigner::from_seed([8u8; 32]);
    swap.execute(&auth, &signer, &treasury).unwrap();
    assert_eq!(
        treasury.dregg_balance(),
        900_000_000,
        "the late contribution stayed in the pile"
    );
    pool.close(&proposal.pool).unwrap();
    assert_eq!(
        pool.contributed(&MALLORY),
        900_000_000,
        "and stayed attributed to her, for the next pool"
    );
    assert_eq!(pool.contributed(&ALICE), 0, "whose share was retired");
}

#[test]
fn below_the_weight_quorum_there_is_no_authorization_and_no_swap() {
    // THE QUORUM POLE. Note the quorum is WEIGHT: three voters totalling 3000 weight fail
    // a 4000-weight quorum, which a headcount rule of 3 would have passed.
    let c = config();
    let (pool, treasury) = funded_pool();
    let mut gov = LiquidityGovernance::new(
        [9u8; 32],
        GovernanceAuthority::from_seed([7u8; 32]),
        c.mint,
        c.usdc_mint,
    );
    let proposal = gov
        .propose_market_swap("swap the pool?", pool.snapshot(), 4_000)
        .unwrap();

    let a = gov.issue_pool_ballot(&proposal, ALICE).unwrap();
    let b = gov.issue_pool_ballot(&proposal, BOB).unwrap();
    gov.vote_market(&proposal, &a, true).unwrap();
    gov.vote_market(&proposal, &b, true).unwrap();
    assert_eq!(
        gov.market_tally(&proposal).unwrap().per_option,
        vec![0, 3_000]
    );
    assert!(
        gov.finalize_market_swap(&proposal).unwrap().is_none(),
        "3000 approve-weight < 4000 quorum: NO authorization"
    );

    // A REJECT majority-by-weight likewise never arms the APPROVE-gated authorization.
    let cc = gov.issue_pool_ballot(&proposal, CAROL).unwrap();
    gov.vote_market(&proposal, &cc, false).unwrap();
    assert_eq!(
        gov.market_tally(&proposal).unwrap().per_option,
        vec![3_000, 3_000]
    );
    assert!(
        gov.finalize_market_swap(&proposal).unwrap().is_none(),
        "REJECT weight must not authorize a swap"
    );
    assert_eq!(
        treasury.dregg_balance(),
        14_000_000,
        "with no authorization the treasury cannot move at all"
    );
}

#[test]
fn a_short_pile_refuses_the_whole_swap_rather_than_filling_part_of_it() {
    // THE ALL-OR-NOTHING POLE: the pool is swapped whole or not at all. A pile that has
    // been drawn down (an OTC fill, say) below the authorized pool refuses the ENTIRE
    // swap — it does not sell what is left.
    let c = config();
    let (pool, treasury) = funded_pool();
    let mut gov = LiquidityGovernance::new(
        [9u8; 32],
        GovernanceAuthority::from_seed([7u8; 32]),
        c.mint,
        c.usdc_mint,
    );
    let proposal = gov
        .propose_market_swap("swap the pool?", pool.snapshot(), 1_000)
        .unwrap();
    let a = gov.issue_pool_ballot(&proposal, ALICE).unwrap();
    gov.vote_market(&proposal, &a, true).unwrap();
    let auth = gov.finalize_market_swap(&proposal).unwrap().unwrap();
    assert_eq!(auth.amount, 14_000_000);

    // The pile is drawn down between the vote and the settlement.
    treasury.withdraw_dregg(4_000_000).unwrap();
    assert_eq!(treasury.dregg_balance(), 10_000_000);

    let swap = JupiterSwap::new(
        MockSwapVenue::new(5, 1_000),
        c.mint,
        c.usdc_mint,
        gov.authority_public_key(),
    );
    let signer = MockSigner::from_seed([8u8; 32]);
    assert_eq!(
        swap.execute(&auth, &signer, &treasury),
        Err(SwapError::PileShort {
            needed: 14_000_000,
            available: 10_000_000
        }),
        "all or nothing: a 10M pile does not part-fill a 14M authorization",
    );
    assert_eq!(treasury.dregg_balance(), 10_000_000, "nothing moved");
    assert_eq!(treasury.usdc_balance(), 0, "no fuel was realized");
    // And the pool ledger is untouched, so the contributors keep their standing.
    assert_eq!(pool.total(), 14_000_000);
}

#[test]
fn the_market_proposal_fills_where_a_floored_one_would_have_refused() {
    // THE MARKET-PRICE POLE, sharpened: the same venue, the same pool, the same voters.
    // The market authorization (min_out = 0) executes into a catastrophic fill and
    // RECORDS it; a floored authorization over the identical setup refuses and moves
    // nothing. If MARKET_MIN_OUT ever stopped being 0, the first half fails.
    let c = config();
    let authority_seed = [7u8; 32];
    let signer = MockSigner::from_seed([8u8; 32]);
    // A venue filling at a tenth of the reference rate — a 90% haircut.
    let venue_rate = (5u128, 10_000u128);

    // ── the MARKET path ──
    let (pool, treasury) = funded_pool();
    let mut gov = LiquidityGovernance::new(
        [9u8; 32],
        GovernanceAuthority::from_seed(authority_seed),
        c.mint,
        c.usdc_mint,
    );
    let proposal = gov
        .propose_market_swap("dump the pool at market?", pool.snapshot(), 1_000)
        .unwrap();
    let a = gov.issue_pool_ballot(&proposal, ALICE).unwrap();
    gov.vote_market(&proposal, &a, true).unwrap();
    let market_auth = gov.finalize_market_swap(&proposal).unwrap().unwrap();
    assert_eq!(market_auth.min_out, 0, "no floor was minted");

    let swap = JupiterSwap::new(
        MockSwapVenue::new(venue_rate.0, venue_rate.1),
        c.mint,
        c.usdc_mint,
        gov.authority_public_key(),
    );
    let out = swap.execute(&market_auth, &signer, &treasury).unwrap();
    println!(
        "market fill: {} USDC for {} $DREGG (quoted {}, slippage {} bps)",
        out.usdc_out, out.dregg_in, out.quoted_out, out.slippage_bps
    );
    assert_eq!(out.usdc_out, 7_000, "filled at the bad market price anyway");
    assert_eq!(out.quoted_out, 7_000);
    assert_eq!(treasury.dregg_balance(), 0);
    assert_eq!(treasury.usdc_balance(), 7_000);

    // ── the FLOORED path, same everything ──
    let (_pool2, treasury2) = funded_pool();
    let mut gov2 = LiquidityGovernance::new(
        [9u8; 32],
        GovernanceAuthority::from_seed(authority_seed),
        c.mint,
        c.usdc_mint,
    );
    let floored = gov2
        .propose(
            "swap 14M with a floor?",
            14_000_000,
            60_000,
            vec![ALICE.0],
            1,
        )
        .unwrap();
    let fb = gov2.issue_ballot(&floored, ALICE.0).unwrap();
    gov2.vote(&floored, &fb, true).unwrap();
    let floored_auth = gov2.finalize(&floored).unwrap().unwrap();
    assert_eq!(floored_auth.min_out, 60_000);

    let swap2 = JupiterSwap::new(
        MockSwapVenue::new(venue_rate.0, venue_rate.1),
        c.mint,
        c.usdc_mint,
        gov2.authority_public_key(),
    );
    assert_eq!(
        swap2.execute(&floored_auth, &signer, &treasury2),
        Err(SwapError::SlippageExceeded {
            realized: 7_000,
            min_out: 60_000
        }),
        "the floored proposal refuses the very fill the market one accepted",
    );
    assert_eq!(treasury2.dregg_balance(), 14_000_000, "nothing moved");
}
