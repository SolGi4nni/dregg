//! End-to-end driven test of the full "B" payment backend on the MOCK/devnet path.
//!
//! Exercises the whole flow with NO real funds and NO network:
//!   deposit-address derivation (deterministic + per-user unique + pluggable trait)
//!   → attributed payment observation → credit at the configured price
//!   → idempotent re-observe (no double-credit) → debit (spend + empty-fails)
//!   → sweep to the (mock) treasury.
//!
//! Run: `cargo test -p dregg-pay --test e2e_mock -- --nocapture` to see the printout.

use dregg_pay::{
    CreditLedger, CreditOutcome, DebitError, DepositAddress, DepositAddressProvider, HdDeposit,
    InMemoryStore, MockChain, MockSweeper, MockWatcher, PayConfig, Sweeper, UserId, Watcher,
};

#[test]
fn full_b_backend_driven_end_to_end() {
    // ── config: THROWAWAY test seed + MOCK mint + MOCK treasury (never mainnet) ──
    let seed = *b"dregg-pay E2E throwaway seed - not a real key!!!";
    let mock_mint = [0x11u8; 32];
    let treasury = DepositAddress([0xEEu8; 32]);
    let price_per_run: u64 = 1_000_000; // 1,000,000 atomic $DREGG = 1 run
    let config = PayConfig::devnet_mock(seed, mock_mint, treasury, price_per_run);

    println!("\n=== dregg-pay B backend — driven end-to-end (mock/devnet) ===");
    println!("network            : {:?}", config.network);
    println!("price_per_run      : {price_per_run} atomic $DREGG");
    println!("treasury (mock)    : {treasury}");

    // ── 1. deposit-address derivation (pluggable provider trait) ──
    let provider: &dyn DepositAddressProvider = &HdDeposit::new(&config);
    let alice = UserId::from("alice");
    let bob = UserId::from("bob");

    let alice_addr = provider.deposit_address(&alice);
    let bob_addr = provider.deposit_address(&bob);
    let alice_addr_again = provider.deposit_address(&alice);

    println!("\n-- deposit addresses (SLIP-0010 m/44'/501'/index') --");
    println!("alice  : {alice_addr}");
    println!("bob    : {bob_addr}");
    println!("alice' : {alice_addr_again}  (re-derived)");

    assert_eq!(
        alice_addr, alice_addr_again,
        "same user MUST derive the same address"
    );
    assert_ne!(
        alice_addr, bob_addr,
        "different users MUST derive different addresses"
    );

    // ── shared mock chain + the watcher/sweeper over it ──
    let chain = MockChain::new();
    let watcher = MockWatcher::new(chain.clone());
    let ledger = CreditLedger::new(InMemoryStore::new(), price_per_run);
    let sweeper = MockSweeper::new(chain.clone(), treasury);

    // ── 2. a $DREGG payment lands on alice's deposit address (5 runs' worth) ──
    let paid = 5_000_000u64;
    chain.credit_onchain(&alice_addr, paid);
    println!("\n-- payment observed --");
    let observed = watcher.poll(&alice, &alice_addr).expect("poll ok");
    assert_eq!(observed.len(), 1, "exactly one payment observed");
    let payment = observed[0].clone();
    println!(
        "observed {} atomic $DREGG to alice's address (ref {})",
        payment.amount, payment.reference
    );
    assert_eq!(
        payment.user, alice,
        "attribution: payment credited to alice"
    );
    assert_eq!(payment.amount, paid);

    // ── 3. credit at the configured price ──
    let outcome = ledger.credit(&payment);
    println!("credit outcome     : {outcome:?}");
    match outcome {
        CreditOutcome::Credited {
            runs, new_balance, ..
        } => {
            assert_eq!(runs, 5, "5,000,000 / 1,000,000 = 5 runs");
            assert_eq!(new_balance, 5);
        }
        other => panic!("expected Credited, got {other:?}"),
    }
    assert_eq!(ledger.balance(&alice), 5);

    // ── 4. idempotency: re-observing / re-crediting the SAME payment does NOT double-credit ──
    let re_credit = ledger.credit(&payment);
    println!("re-credit (same ref): {re_credit:?}");
    assert_eq!(re_credit, CreditOutcome::AlreadyCredited);
    assert_eq!(
        ledger.balance(&alice),
        5,
        "balance unchanged after re-credit"
    );
    // watcher-level dedup too: polling again with no new payment yields nothing.
    assert!(watcher.poll(&alice, &alice_addr).unwrap().is_empty());

    // ── 5. debit spends credits; an empty balance fails ──
    println!("\n-- debits --");
    for expected_remaining in (0..5).rev() {
        let remaining = ledger.debit(&alice).expect("debit ok while credits remain");
        println!("debit alice -> {remaining} credits left");
        assert_eq!(remaining, expected_remaining);
    }
    let empty = ledger.debit(&alice);
    println!("debit alice (empty): {empty:?}");
    assert_eq!(
        empty,
        Err(DebitError::InsufficientCredits {
            user: alice.clone()
        })
    );

    // bob never paid ⇒ bob cannot debit.
    assert_eq!(
        ledger.debit(&bob),
        Err(DebitError::InsufficientCredits { user: bob.clone() })
    );

    // ── 6. sweep alice's deposit balance to the (mock) treasury ──
    println!("\n-- sweep --");
    assert_eq!(
        chain.balance(&alice_addr),
        paid,
        "deposit still on-chain pre-sweep"
    );
    let swept = sweeper.sweep(&alice, &alice_addr).expect("sweep ok");
    println!(
        "swept {} atomic $DREGG {} -> treasury {} (ref {:?})",
        swept.amount, swept.from, swept.to, swept.reference
    );
    assert_eq!(swept.amount, paid);
    assert_eq!(swept.to, treasury);
    assert_eq!(chain.balance(&alice_addr), 0, "deposit drained after sweep");
    assert_eq!(
        chain.balance(&treasury),
        paid,
        "treasury received the funds"
    );

    println!(
        "\n=== all invariants held: deterministic addrs, attributed credit, idempotent, debit gate, sweep ===\n"
    );
}
