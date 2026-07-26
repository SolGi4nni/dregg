//! **The whole treasury path as ONE flow**, driven end to end: a real observed payment →
//! a real credited run → a real pinned pool → a real weighted vote → a real (mock-signed)
//! swap → fuel the runs can actually burn.
//!
//! MOCK/devnet only: a throwaway seed, mock mints, a simulated chain, an operator-held
//! `MockSigner`. No real funds, no network, no key in `dregg-pay`.
//!
//! # Why this flow has to exist at all
//!
//! `dregg-pay`'s treasury is deliberately asymmetric: a `$DREGG`-paid run BURNS USD fuel
//! (`Treasury::spend_inference_usd`) while only growing the illiquid pile. Run that long
//! enough and the tank empties while the pile grows — every run then refuses with
//! `InsufficientFuel` on top of a treasury that is nominally rich. This test drives
//! exactly that dead end, and then drives the machinery that gets out of it. The swap is
//! not a feature bolted on the side; it is the only thing that makes the dual-asset
//! economics terminate.
//!
//! # The chain driven here
//!
//! 1. **Contribute** — `$DREGG` lands on HD-derived deposit addresses, is OBSERVED by a
//!    `Watcher`, credits run-credits through the `CreditLedger`, and is attributed +
//!    banked through `SwapPool::record_payment` (one gate over the pile AND the
//!    electorate).
//! 2. **Starve** — the fuel tank empties; a run refuses, fail-closed.
//! 3. **Pin + propose** — a `PoolSnapshot` fixes electorate, weights, and the
//!    all-or-nothing amount.
//! 4. **Vote** — quadratically weighted, over the real `collective-choice` executor.
//! 5. **Authorize + sign + swap** — a passed vote mints the only `SwapAuthorization`
//!    there is; the operator signs; the pile becomes fuel.
//! 6. **Run again** — the very call that refused in (2) now funds.
//! 7. **Retire, and refuse the replays** — the pool retires exactly once, the spent
//!    authorization refuses a second swap, and a fresh handle over the same store (the
//!    restart) still refuses both.
//!
//! Run: `cargo test -p dregg-pay --test treasury_swap_flow_e2e -- --test-threads=4`.

use std::sync::Arc;

use dregg_pay::{
    Asset, ContributionOutcome, CreditLedger, CreditOutcome, DepositAddress,
    DepositAddressProvider, GovernanceAuthority, GovernanceError, HdDeposit, InMemoryPoolStore,
    InMemoryStore, InMemoryTreasuryStore, JupiterSwap, LiquidityGovernance, MARKET_MIN_OUT,
    MockChain, MockSigner, MockSwapVenue, MockWatcher, PayConfig, PoolError, PoolSnapshot,
    SwapError, SwapPool, Treasury, TreasuryError, UserId, Watcher, quadratic_weight,
};

/// Atomic `$DREGG` per one run credit.
const PRICE_PER_RUN: u64 = 1_000_000;
/// What one real-AI run costs in USD — the fuel it burns whatever it was paid in.
const RUN_COST_USD: f64 = 0.01;
/// The mock venue's rate: `dregg_in * 5 / 1000` atomic USDC (`$0.005`/`$DREGG` at (6,6)).
const VENUE_NUM: u128 = 5;
const VENUE_DEN: u128 = 1_000;

fn config() -> PayConfig {
    // THROWAWAY seed, MOCK mints — never mainnet.
    let seed = *b"dregg-pay TREASURY FLOW throwaway seed - not real";
    let mut c = PayConfig::devnet_mock(
        seed,
        [0x11u8; 32],
        DepositAddress([0xEEu8; 32]),
        PRICE_PER_RUN,
    );
    c.usdc_mint = [0x22u8; 32];
    c
}

/// Everything a deployment holds: the deposit source, the watcher over a simulated chain,
/// the run-credit ledger, the two-balance treasury, and the pool over a store that is
/// SHARED (the stand-in for a durable one — a second handle is "after the restart").
struct Deployment {
    config: PayConfig,
    hd: HdDeposit,
    chain: MockChain,
    watcher: MockWatcher,
    ledger: CreditLedger<InMemoryStore>,
    treasury: Treasury<InMemoryTreasuryStore>,
    pool_store: Arc<InMemoryPoolStore>,
    pool: SwapPool<Arc<InMemoryPoolStore>>,
}

impl Deployment {
    fn new() -> Self {
        let config = config();
        let hd = HdDeposit::new(&config);
        let chain = MockChain::new();
        let pool_store = Arc::new(InMemoryPoolStore::new());
        Deployment {
            watcher: MockWatcher::for_asset(chain.clone(), Asset::Dregg),
            ledger: CreditLedger::new(InMemoryStore::new(), config.price_per_run),
            treasury: Treasury::new(InMemoryTreasuryStore::new(), config.usdc_decimals),
            pool: SwapPool::over(Arc::clone(&pool_store)),
            pool_store,
            chain,
            hd,
            config,
        }
    }

    fn address(&self, user: &str) -> DepositAddress {
        self.hd.deposit_address(&UserId::from(user))
    }

    /// A REAL contribution: `$DREGG` lands on the user's derived deposit address, the
    /// watcher observes it, the ledger credits runs, and the pool banks + attributes it.
    /// Returns `(runs credited, contribution outcome)`.
    fn contribute(&self, user: &str, atomic_dregg: u64) -> (u64, ContributionOutcome) {
        let id = UserId::from(user);
        let addr = self.address(user);
        self.chain.credit_onchain(&addr, atomic_dregg);
        let payments = self.watcher.poll(&id, &addr).expect("mock watcher poll");
        assert_eq!(payments.len(), 1, "one deposit, one observed payment");
        let payment = &payments[0];
        assert_eq!(payment.user, id, "attribution is automatic");
        assert_eq!(payment.deposit_address, addr);

        let credited = match self.ledger.credit(payment) {
            CreditOutcome::Credited { runs, .. } => runs,
            CreditOutcome::BelowOneRun { .. } => 0,
            other => panic!("unexpected credit outcome: {other:?}"),
        };
        let banked = self.pool.record_payment(payment, &self.treasury);
        (credited, banked)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// The flow
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn a_starved_treasury_votes_its_pile_into_fuel_and_the_runs_resume() {
    let d = Deployment::new();
    println!("\n=== treasury flow: contribute → starve → vote → swap → run ===");

    // ── 0. The operator seeds a small fuel tank: $0.02, exactly two runs' worth. ──
    d.treasury.deposit_usdc(20_000);
    assert_eq!(d.treasury.usdc_balance(), 20_000);
    assert_eq!(d.treasury.dregg_balance(), 0, "the pile starts empty");

    // ── 1. CONTRIBUTE. Three players pay in `$DREGG`, on REAL derived addresses. ──
    // alice 1M (weight 1000), bob 4M (weight 2000), carol 9M (weight 3000).
    for (user, amount, expect_runs) in [("alice", 1_000_000u64, 1u64), ("bob", 4_000_000, 4)] {
        let (runs, banked) = d.contribute(user, amount);
        assert_eq!(runs, expect_runs, "{user} bought {expect_runs} runs");
        assert!(matches!(banked, ContributionOutcome::Contributed { .. }));
    }
    let (carol_runs, carol_banked) = d.contribute("carol", 9_000_000);
    assert_eq!(carol_runs, 9);
    assert_eq!(
        carol_banked,
        ContributionOutcome::Contributed {
            contributed_total: 9_000_000,
            pool_total: 14_000_000,
            weight: 3_000,
        }
    );
    assert_eq!(d.treasury.dregg_balance(), 14_000_000, "the pile grew");
    assert_eq!(d.pool.total(), 14_000_000, "and is FULLY attributed");
    assert_eq!(
        d.treasury.dregg_balance(),
        d.pool.total(),
        "the aggregate pile and the sum of the electorate's stakes are one number",
    );
    // Re-polling the same chain state observes nothing new — the watcher-level dedup.
    assert!(
        d.watcher
            .poll(&UserId::from("alice"), &d.address("alice"))
            .unwrap()
            .is_empty()
    );

    // ── 2. STARVE. Every run burns USD fuel — including the `$DREGG`-paid ones. ──
    assert_eq!(
        d.treasury.spend_inference_usd(RUN_COST_USD).unwrap(),
        10_000
    );
    assert_eq!(d.treasury.spend_inference_usd(RUN_COST_USD).unwrap(), 0);
    let starved = d.treasury.spend_inference_usd(RUN_COST_USD);
    assert_eq!(
        starved,
        Err(TreasuryError::InsufficientFuel {
            needed: 10_000,
            available: 0
        }),
        "THE DEAD END: 14M atomic $DREGG in the pile and not one more run can be funded",
    );
    assert_eq!(
        d.treasury.dregg_balance(),
        14_000_000,
        "the pile is untouched"
    );
    println!(
        "  starved: pile={} fuel={} — {starved:?}",
        d.treasury.dregg_balance(),
        d.treasury.usdc_balance()
    );

    // ── 3. PIN + PROPOSE. The snapshot fixes electorate, weights, and the amount. ──
    let authority = GovernanceAuthority::from_seed([7u8; 32]);
    let mut gov = LiquidityGovernance::new([9u8; 32], authority, d.config.mint, d.config.usdc_mint);
    let authority_pk = gov.authority_public_key();

    let pinned: PoolSnapshot = d.pool.snapshot();
    assert_eq!(pinned.epoch(), 0);
    assert_eq!(pinned.total(), 14_000_000);
    assert_eq!(pinned.total_weight(), Some(6_000));
    assert_eq!(
        pinned.user(&d.address("carol")),
        Some(&UserId::from("carol")),
        "the pin carries who each stake belongs to, for the receipt",
    );
    // Quadratic: bob paid 4× alice and votes 2×, carol 9× and votes 3×.
    assert_eq!(pinned.weight(&d.address("alice")), 1_000);
    assert_eq!(pinned.weight(&d.address("bob")), 2_000);
    assert_eq!(pinned.weight(&d.address("carol")), 3_000);

    // A weight quorum of 4000 — reachable only by more than alice+bob together.
    let proposal = gov
        .propose_market_swap("swap the whole pool to fuel at market?", pinned, 4_000)
        .unwrap();
    assert_eq!(proposal.amount(), 14_000_000, "ALL of the pool");

    // ── 4. VOTE. ──
    // A non-contributor is refused a ballot before one is minted (zero stake, zero weight).
    let mallory = DepositAddress([0x77u8; 32]);
    assert_eq!(proposal.weight_of(&mallory), 0);
    assert!(matches!(
        gov.issue_pool_ballot(&proposal, mallory),
        Err(GovernanceError::NoContribution { .. })
    ));

    let a = gov
        .issue_pool_ballot(&proposal, d.address("alice"))
        .unwrap();
    let b = gov.issue_pool_ballot(&proposal, d.address("bob")).unwrap();
    let c = gov
        .issue_pool_ballot(&proposal, d.address("carol"))
        .unwrap();
    assert_eq!(gov.vote_market(&proposal, &a, true).unwrap(), 1_000);
    assert_eq!(gov.vote_market(&proposal, &b, true).unwrap(), 2_000);
    assert!(
        gov.finalize_market_swap(&proposal).unwrap().is_none(),
        "3000 approve-weight is below the 4000 quorum: NO authorization",
    );
    assert_eq!(gov.vote_market(&proposal, &c, true).unwrap(), 3_000);
    assert_eq!(
        gov.market_tally(&proposal).unwrap().per_option,
        vec![0, 6_000],
        "the board holds WEIGHT, not a headcount",
    );

    // ── 5. AUTHORIZE + SIGN + SWAP. ──
    let auth = gov
        .finalize_market_swap(&proposal)
        .unwrap()
        .expect("6000 >= 4000 weight authorizes");
    assert_eq!(auth.amount, 14_000_000, "all or nothing");
    assert_eq!(auth.min_out, MARKET_MIN_OUT, "market price, no floor");
    assert!(auth.verify(&authority_pk));

    let swap = JupiterSwap::new(
        MockSwapVenue::new(VENUE_NUM, VENUE_DEN),
        d.config.mint,
        d.config.usdc_mint,
        authority_pk,
    );
    // The operator's key. NEVER held by dregg-pay.
    let signer = MockSigner::from_seed([8u8; 32]);
    let out = swap.execute(&auth, &signer, &d.treasury).unwrap();
    println!(
        "  swap: {} $DREGG → {} USDC (quoted {}, slippage {} bps)",
        out.dregg_in, out.usdc_out, out.quoted_out, out.slippage_bps
    );
    assert_eq!(out.dregg_in, 14_000_000);
    assert_eq!(out.usdc_out, 70_000);
    assert_eq!(out.pile_after, 0);
    assert_eq!(out.fuel_after, 70_000);

    // ── 6. RUN AGAIN. The exact call that refused in step 2 now funds. ──
    let resumed = d.treasury.spend_inference_usd(RUN_COST_USD);
    assert_eq!(
        resumed,
        Ok(60_000),
        "the vote turned an illiquid pile into runs — this is the whole point",
    );
    assert!(starved.is_err() && resumed.is_ok(), "the polarity flipped");
    // Seven more runs are funded from what the pool bought.
    for _ in 0..6 {
        d.treasury.spend_inference_usd(RUN_COST_USD).unwrap();
    }
    assert_eq!(d.treasury.usdc_balance(), 0);
    assert!(d.treasury.spend_inference_usd(RUN_COST_USD).is_err());

    // ── 7. RETIRE — once — and refuse both replays. ──
    assert_eq!(d.pool.close(&proposal.pool).unwrap(), 1, "epoch bumped");
    assert_eq!(d.pool.total(), 0, "the swapped pool is retired");
    assert_eq!(d.pool.contributed(&d.address("carol")), 0);
    assert_eq!(
        d.pool.close(&proposal.pool),
        Err(PoolError::StaleSnapshot {
            snapshot_epoch: 0,
            pool_epoch: 1
        }),
        "one passed vote cannot retire the ledger twice",
    );
    // …and the passed vote cannot buy a SECOND swap either.
    d.treasury.deposit_dregg(14_000_000); // pretend the pile refilled
    assert_eq!(
        swap.execute(&auth, &signer, &d.treasury),
        Err(SwapError::AuthorizationSpent {
            poll_id: auth.poll_id
        }),
        "one passed vote, one swap — even with a pile that could cover another",
    );
    assert_eq!(
        d.treasury.dregg_balance(),
        14_000_000,
        "the replay moved nothing"
    );
    println!("=== treasury flow held end to end ===\n");
}

#[test]
fn a_retired_pool_cannot_be_voted_again_and_survives_a_restart() {
    // THE PERSISTENCE POLE ON THE FLOW. The pool's state — attribution, dedup set, AND
    // epoch — lives in the store, so a fresh handle (the process after a restart) inherits
    // the retirement instead of resetting it. Without that, a restart would resurrect an
    // already-swapped electorate and let it authorize a second swap of a pile it no longer
    // owns.
    let d = Deployment::new();
    d.contribute("alice", 1_000_000);
    d.contribute("bob", 4_000_000);

    let authority = GovernanceAuthority::from_seed([7u8; 32]);
    let mut gov = LiquidityGovernance::new([9u8; 32], authority, d.config.mint, d.config.usdc_mint);
    let proposal = gov
        .propose_market_swap("swap?", d.pool.snapshot(), 1_000)
        .unwrap();
    let a = gov
        .issue_pool_ballot(&proposal, d.address("alice"))
        .unwrap();
    gov.vote_market(&proposal, &a, true).unwrap();
    let auth = gov.finalize_market_swap(&proposal).unwrap().unwrap();

    let swap = JupiterSwap::new(
        MockSwapVenue::new(VENUE_NUM, VENUE_DEN),
        d.config.mint,
        d.config.usdc_mint,
        gov.authority_public_key(),
    );
    let signer = MockSigner::from_seed([8u8; 32]);
    swap.execute(&auth, &signer, &d.treasury).unwrap();
    d.pool.close(&proposal.pool).unwrap();
    assert_eq!(d.pool.epoch(), 1);

    // ── "the process restarts": a brand-new pool handle over the SAME store. ──
    let after_restart: SwapPool<Arc<InMemoryPoolStore>> = SwapPool::over(Arc::clone(&d.pool_store));
    assert_eq!(after_restart.epoch(), 1, "the epoch is not reset");
    assert_eq!(after_restart.total(), 0, "the retired stake stays retired");
    assert_eq!(after_restart.contributed(&d.address("alice")), 0);
    assert_eq!(
        after_restart.close(&proposal.pool),
        Err(PoolError::StaleSnapshot {
            snapshot_epoch: 0,
            pool_epoch: 1
        }),
        "the retire-exactly-once tooth is DURABLE, not a per-process latch",
    );

    // A new proposal over the post-restart pool has nothing to swap and no electorate.
    let mut gov2 = LiquidityGovernance::new(
        [9u8; 32],
        GovernanceAuthority::from_seed([7u8; 32]),
        d.config.mint,
        d.config.usdc_mint,
    );
    assert!(matches!(
        gov2.propose_market_swap("again?", after_restart.snapshot(), 1),
        Err(GovernanceError::EmptyPool)
    ));

    // A fresh contribution opens a NEW pool at the bumped epoch, and it votes normally.
    d.contribute("carol", 9_000_000);
    assert_eq!(after_restart.total(), 9_000_000);
    let next = after_restart.snapshot();
    assert_eq!(next.epoch(), 1, "the new pool is epoch 1, not epoch 0");
    assert_eq!(
        next.contributor_count(),
        1,
        "only the post-retirement payer"
    );
    assert_eq!(
        next.weight(&d.address("carol")),
        quadratic_weight(9_000_000)
    );
    assert_eq!(
        next.weight(&d.address("alice")),
        0,
        "a swapped-out contributor buys no weight in the next pool",
    );
    // And the OLD snapshot cannot retire this one either — its epoch is stale forever.
    assert!(matches!(
        after_restart.close(&proposal.pool),
        Err(PoolError::StaleSnapshot { .. })
    ));
}

#[test]
fn credits_and_pool_weight_are_two_different_ledgers_over_one_payment() {
    // A guard against the confusion this whole design exists to avoid: run CREDITS are
    // spendable budget (they go DOWN as you play); pool STAKE is a record of contribution
    // (it does not). Spending every credit must not disenfranchise the contributor, and
    // buying credits with USDC must not buy pile weight.
    let d = Deployment::new();
    let alice = UserId::from("alice");
    let (runs, _) = d.contribute("alice", 4_000_000);
    assert_eq!(runs, 4);
    assert_eq!(d.ledger.balance(&alice), 4);
    assert_eq!(d.pool.contributed(&d.address("alice")), 4_000_000);
    assert_eq!(d.pool.weight(&d.address("alice")), 2_000);

    // Play all four runs down to nothing.
    for _ in 0..4 {
        d.ledger.debit(&alice).unwrap();
    }
    assert_eq!(d.ledger.balance(&alice), 0);
    assert_eq!(
        d.pool.weight(&d.address("alice")),
        2_000,
        "spending your credits does not spend your VOTE — stake is not budget",
    );

    // USDC is FUEL, not pile: it credits runs and buys no weight at all.
    let usdc_watcher = MockWatcher::for_asset(d.chain.clone(), Asset::Usdc);
    let bob_addr = d.address("bob");
    d.chain.credit_onchain(&bob_addr, 9_000_000);
    let payments = usdc_watcher.poll(&UserId::from("bob"), &bob_addr).unwrap();
    assert_eq!(
        d.pool.record_payment(&payments[0], &d.treasury),
        ContributionOutcome::FuelNotPool,
    );
    assert_eq!(d.treasury.usdc_balance(), 9_000_000, "the tank filled");
    assert_eq!(d.pool.contributed(&bob_addr), 0);
    assert_eq!(
        d.pool.weight(&bob_addr),
        0,
        "USDC funds the runs; it does not vote on the pile",
    );
    assert_eq!(d.pool.total(), 4_000_000, "the pool is alice's stake alone");
}
