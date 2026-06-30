//! The bridge concurrency DOUBLE-MINT soundness proof
//! (`docs/deos/BRIDGE-ARCHITECTURE-SOUNDNESS.md` §3).
//!
//! THE BUG (closed here): `MirrorState` / `StripeMirrorState` held the backing
//! relationship (`currently_locked`/`live_supply`/the `seen_*` replay set) as
//! IN-MEMORY, PER-RELAYER Rust fields. Two relayers, each with their own
//! `MirrorState` and a copy of the mirror's mint-cap, each saw a fresh replay
//! set and each minted against the SAME lock / payment — `2·amount` circulating
//! against `amount` of real backing.
//!
//! THE FIX (proven below): the consume-once event id and the supply ledger move
//! into COMMITTED dregg state. The `lock_id` / `payment_intent_id` becomes a
//! domain-separated nullifier consumed against the SAME committed
//! `note_nullifiers` set `Effect::NoteSpend` rides; the supply lives in a
//! committed cell; both are gated inside one atomic
//! `TurnExecutor::bridge_mint_against_lock`. The executor's per-turn
//! serialization is now the global serialization point.
//!
//! Each test runs TWO independent relayers (two `MirrorState`s) against the SAME
//! shared committed state and the SAME event, and asserts: the FIRST mint
//! commits (nullifier consumed, ledger debited, conserving mint applied); the
//! SECOND is REFUSED by the committed nullifier; and `live_supply ≤
//! currently_locked` holds as a committed-state invariant.

use dregg_bridge::midnight::EpochKey;
use dregg_bridge::solana_mirror::{MirrorConfig, MirrorState, SolanaLockAttestation};
use dregg_bridge::stripe_mirror::{
    StripeMirrorConfig, StripeMirrorState, StripePaymentAttestation,
};
use dregg_cell::Nullifier;
use dregg_cell::{AuthRequired, Cell, CellId, EFFECT_MINT, Ledger, Permissions};
use dregg_turn::{
    BridgeEscrowRecord, BridgeMintError, BridgeMintRequest, ComputronCosts, TurnExecutor,
    escrow_nullifier_for, new_mirror_ledger_cell, read_supply,
};
use ed25519_dalek::SigningKey;

/// Record the INDEPENDENT escrow leg (raising committed `currently_locked`) that a
/// consensus-verified lock backs, before the mint draws against it. The escrow
/// nullifier is domain-separated from the mint nullifier so the same lock records
/// its escrow once and mints once.
fn record_escrow(
    exec: &TurnExecutor,
    ledger: &mut Ledger,
    ledger_cell: CellId,
    mint_nullifier: Nullifier,
    escrowed: u64,
) {
    exec.bridge_record_escrow(
        ledger,
        &BridgeEscrowRecord {
            ledger_cell,
            escrow_nullifier: escrow_nullifier_for(&mint_nullifier),
            escrowed,
            consensus_verified: true,
        },
    )
    .expect("the independently-verified escrow leg is recorded");
}

// ── shared cell/ledger scaffolding (mirrors conservation_mint_property.rs) ──

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn pk(seed: u8) -> [u8; 32] {
    let mut p = [0u8; 32];
    p[0] = seed;
    p[31] = seed.wrapping_mul(37).wrapping_add(1);
    p
}

fn open_cell(seed: u8, token_id: [u8; 32], balance: i64) -> Cell {
    let mut cell = Cell::with_balance(pk(seed), token_id, balance);
    cell.permissions = open_permissions();
    cell
}

/// The deterministic per-asset well id — mirrors `derive_issuer_well`.
fn derived_well_id(token_id: &[u8; 32]) -> CellId {
    let well_pubkey = blake3::derive_key("dregg-issuer-well-key-v1", token_id);
    CellId::derive_raw(&well_pubkey, token_id)
}

/// Build a ledger with: a fresh recipient (asset class `token`), an `issuer`
/// holding the mirror asset's control-grade mint-cap (the shared bridge cap),
/// and the committed mirror-ledger cell. Returns `(ledger, recipient, issuer,
/// ledger_cell)`.
fn scaffold(token: [u8; 32]) -> (Ledger, CellId, CellId, CellId) {
    let well_id = derived_well_id(&token);

    let recipient = open_cell(1, token, 0);
    let recipient_id = recipient.id();

    let mut issuer = open_cell(2, token, 0);
    issuer
        .capabilities
        .grant_faceted(well_id, AuthRequired::None, EFFECT_MINT)
        .expect("grant mint-cap to the bridge cell");
    let issuer_id = issuer.id();

    // The committed mirror-ledger cell lives in a DISTINCT token domain (it is a
    // scalar supply store, not a well).
    let ledger_cell = new_mirror_ledger_cell(pk(9), [0x44u8; 32]);
    let ledger_cell_id = ledger_cell.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(recipient).unwrap();
    ledger.insert_cell(issuer).unwrap();
    ledger.insert_cell(ledger_cell).unwrap();

    (ledger, recipient_id, issuer_id, ledger_cell_id)
}

// ───────────────────────────── Solana mirror ──────────────────────────────

const SPL_MINT: [u8; 32] = [0xABu8; 32];

fn solana_oracle() -> SigningKey {
    SigningKey::from_bytes(&[7u8; 32])
}

fn solana_config(token: [u8; 32], o: &SigningKey) -> MirrorConfig {
    MirrorConfig {
        spl_mint: SPL_MINT,
        asset: token,
        oracle_keys: vec![EpochKey {
            from_epoch: 0,
            to_epoch: None,
            pubkey: o.verifying_key().to_bytes(),
        }],
        min_amount: 1,
        max_amount: 1_000_000,
        // The committed path here goes through the trusted-oracle `verify_lock`
        // (no inclusion proof), so the vault binding is not exercised; placeholders.
        vault_account: [0u8; 32],
        lock_program: [0u8; 32],
        pinned_anchor_epoch: None,
        pinned_anchor_root: None,
    }
}

#[test]
fn two_solana_relayers_one_lock_only_one_mint() {
    let token = [0x77u8; 32];
    let (mut ledger, recipient, issuer, ledger_cell) = scaffold(token);
    let exec = TurnExecutor::new(ComputronCosts::zero());

    let o = solana_oracle();
    // TWO independent relayers — each its own in-memory MirrorState, both holding
    // (a copy of) the shared mint-cap on `issuer`. This is exactly the bug
    // scenario: per-relayer RAM, shared cap.
    let relayer_a = MirrorState::new(solana_config(token, &o));
    let relayer_b = MirrorState::new(solana_config(token, &o));

    // ONE real Solana lock event (one lock_id, one backing of `amount`),
    // observed by BOTH relayers.
    let amount = 500u64;
    let att = SolanaLockAttestation::create([0x11u8; 32], SPL_MINT, amount, recipient, 0, &o);

    // Both relayers verify the SAME lock → the SAME committed nullifier.
    let va = relayer_a
        .verify_lock(&att)
        .expect("relayer A verifies the lock");
    let vb = relayer_b
        .verify_lock(&att)
        .expect("relayer B verifies the lock");
    assert_eq!(
        va.lock_nullifier, vb.lock_nullifier,
        "the same lock_id yields the same committed consume-once nullifier"
    );

    // The INDEPENDENT escrow leg is recorded once (raising committed
    // currently_locked), from the consensus-verified lock — the mint draws
    // against it.
    record_escrow(&exec, &mut ledger, ledger_cell, va.lock_nullifier, amount);

    // Relayer A lands the committed bridge mint FIRST: nullifier consumed, the
    // committed ledger cell debited, the conserving Effect::Mint applied.
    let req_a = BridgeMintRequest {
        actor: issuer,
        ledger_cell,
        lock_nullifier: va.lock_nullifier,
        recipient: va.recipient,
        amount: va.amount,
        consensus_verified: true,
    };
    let receipt = exec
        .bridge_mint_against_lock(&mut ledger, &req_a)
        .expect("the first relayer's mint commits");
    assert_eq!(receipt.currently_locked, amount);
    assert_eq!(receipt.live_supply, amount);

    // Relayer B races the SAME lock — REFUSED by COMMITTED state, despite its own
    // fresh in-memory MirrorState. THIS is the closed double-mint.
    let req_b = BridgeMintRequest {
        actor: issuer,
        ledger_cell,
        lock_nullifier: vb.lock_nullifier,
        recipient: vb.recipient,
        amount: vb.amount,
        consensus_verified: true,
    };
    assert_eq!(
        exec.bridge_mint_against_lock(&mut ledger, &req_b)
            .unwrap_err(),
        BridgeMintError::DuplicateLock,
        "the second relayer is refused by the committed nullifier — no double-mint"
    );

    // COMMITTED-STATE invariant: live_supply ≤ currently_locked, and exactly ONE
    // mint's worth circulates against ONE mint's worth of backing.
    let (locked, live) = read_supply(ledger.get(&ledger_cell).unwrap());
    assert_eq!(locked, amount, "currently_locked credited exactly once");
    assert_eq!(live, amount, "live_supply raised exactly once");
    assert!(live <= locked, "live_supply ≤ currently_locked (committed)");

    // The recipient was credited exactly once; the well carries −amount.
    assert_eq!(
        ledger.get(&recipient).unwrap().state.balance(),
        amount as i64,
        "recipient credited a single mint"
    );
    assert_eq!(
        ledger
            .get(&derived_well_id(&token))
            .unwrap()
            .state
            .balance(),
        -(amount as i64),
        "well debited a single mint's −supply (conservation)"
    );
}

#[test]
fn solana_distinct_locks_both_mint_and_conserve() {
    // Liveness: two DIFFERENT locks (different lock_ids) both mint — the gate is
    // per-lock, not a blanket lock-out. The committed ledger accumulates both.
    let token = [0x78u8; 32];
    let (mut ledger, recipient, issuer, ledger_cell) = scaffold(token);
    let exec = TurnExecutor::new(ComputronCosts::zero());
    let o = solana_oracle();
    let relayer = MirrorState::new(solana_config(token, &o));

    for (lid, amt) in [(0x21u8, 300u64), (0x22u8, 200u64)] {
        let att = SolanaLockAttestation::create([lid; 32], SPL_MINT, amt, recipient, 0, &o);
        let v = relayer.verify_lock(&att).expect("verify");
        record_escrow(&exec, &mut ledger, ledger_cell, v.lock_nullifier, amt);
        exec.bridge_mint_against_lock(
            &mut ledger,
            &BridgeMintRequest {
                actor: issuer,
                ledger_cell,
                lock_nullifier: v.lock_nullifier,
                recipient: v.recipient,
                amount: v.amount,
                consensus_verified: true,
            },
        )
        .expect("each distinct lock mints");
    }

    let (locked, live) = read_supply(ledger.get(&ledger_cell).unwrap());
    assert_eq!(locked, 500);
    assert_eq!(live, 500);
    assert!(live <= locked);
    assert_eq!(ledger.get(&recipient).unwrap().state.balance(), 500);
}

// ───────────────────────────── Stripe mirror ──────────────────────────────

fn stripe_config(token: [u8; 32]) -> StripeMirrorConfig {
    StripeMirrorConfig {
        asset: token,
        webhook_secret: b"whsec_test".to_vec(),
        currency: "usd".to_string(),
        min_cents: 50,
        max_cents: 1_000_000_00,
    }
}

fn stripe_att(pi_id: &str, cents: u64, recipient: CellId) -> StripePaymentAttestation {
    StripePaymentAttestation {
        payment_intent_id: pi_id.to_string(),
        amount_cents: cents,
        currency: "usd".to_string(),
        recipient,
        event_type: "payment_intent.succeeded".to_string(),
    }
}

#[test]
fn two_stripe_relayers_one_payment_only_one_mint() {
    let token = [0x88u8; 32];
    let (mut ledger, recipient, issuer, ledger_cell) = scaffold(token);
    let exec = TurnExecutor::new(ComputronCosts::zero());

    // TWO independent relayers, one verified payment (one payment_intent_id).
    let relayer_a = StripeMirrorState::new(stripe_config(token));
    let relayer_b = StripeMirrorState::new(stripe_config(token));

    let cents = 5000u64;
    let att = stripe_att("pi_double", cents, recipient);

    let va = relayer_a.verify_payment(&att).expect("relayer A verifies");
    let vb = relayer_b.verify_payment(&att).expect("relayer B verifies");
    assert_eq!(
        va.payment_nullifier, vb.payment_nullifier,
        "the same payment_intent_id yields the same committed nullifier"
    );

    record_escrow(&exec, &mut ledger, ledger_cell, va.payment_nullifier, cents);
    let req_a = BridgeMintRequest {
        actor: issuer,
        ledger_cell,
        lock_nullifier: va.payment_nullifier,
        recipient: va.recipient,
        amount: va.amount,
        consensus_verified: true,
    };
    let receipt = exec
        .bridge_mint_against_lock(&mut ledger, &req_a)
        .expect("the first relayer's mint commits");
    assert_eq!(receipt.live_supply, cents);

    // The second relayer (or a Stripe webhook retry / sibling charge.succeeded)
    // is refused by the committed nullifier.
    let req_b = BridgeMintRequest {
        actor: issuer,
        ledger_cell,
        lock_nullifier: vb.payment_nullifier,
        recipient: vb.recipient,
        amount: vb.amount,
        consensus_verified: true,
    };
    assert_eq!(
        exec.bridge_mint_against_lock(&mut ledger, &req_b)
            .unwrap_err(),
        BridgeMintError::DuplicateLock,
        "the second relayer is refused by committed state — no double-mint"
    );

    let (locked, live) = read_supply(ledger.get(&ledger_cell).unwrap());
    assert_eq!(locked, cents);
    assert_eq!(live, cents);
    assert!(live <= locked, "live_supply ≤ currently_locked (committed)");
    assert_eq!(
        ledger.get(&recipient).unwrap().state.balance(),
        cents as i64,
        "recipient credited a single payment"
    );
}

#[test]
fn unauthorized_bridge_mint_is_refused_and_rolls_back() {
    // Defence: the bridge cell still needs the mint-cap. An actor WITHOUT it is
    // refused, the lock nullifier is NOT consumed (rollback), and the committed
    // ledger is untouched — so the authorized relayer can still mint the SAME
    // lock afterwards (proving the failed attempt burned nothing).
    let token = [0x99u8; 32];
    let (mut ledger, recipient, issuer, ledger_cell) = scaffold(token);
    let exec = TurnExecutor::new(ComputronCosts::zero());
    let o = solana_oracle();
    let relayer = MirrorState::new(solana_config(token, &o));

    // A bystander cell holding NO mint-cap.
    let bystander = open_cell(5, token, 0);
    let bystander_id = bystander.id();
    ledger.insert_cell(bystander).unwrap();

    let att = SolanaLockAttestation::create([0x33u8; 32], SPL_MINT, 400, recipient, 0, &o);
    let v = relayer.verify_lock(&att).expect("verify");

    // The escrow leg is recorded (locked=400) so the conservation check passes and
    // the refusal we exercise is genuinely the MISSING-MINT-CAP one, not a draw
    // exceeding the backing.
    record_escrow(&exec, &mut ledger, ledger_cell, v.lock_nullifier, 400);

    let bad = BridgeMintRequest {
        actor: bystander_id,
        ledger_cell,
        lock_nullifier: v.lock_nullifier,
        recipient: v.recipient,
        amount: v.amount,
        consensus_verified: true,
    };
    assert!(
        matches!(
            exec.bridge_mint_against_lock(&mut ledger, &bad),
            Err(BridgeMintError::MintFailed(_))
        ),
        "a mint without the mint-cap must be refused"
    );

    // The mint leg rolled back: live_supply is still 0 AND the mint nullifier was
    // freed. The independently-recorded escrow (locked=400) is untouched.
    let (locked, live) = read_supply(ledger.get(&ledger_cell).unwrap());
    assert_eq!(
        (locked, live),
        (400, 0),
        "refused mint left live_supply at 0 (mint leg rolled back); escrow backing intact"
    );

    // The authorized issuer (granted the mint-cap by `scaffold`) can now mint the
    // SAME lock — proving the failed attempt did not burn the nullifier.
    let good = BridgeMintRequest {
        actor: issuer,
        ledger_cell,
        lock_nullifier: v.lock_nullifier,
        recipient: v.recipient,
        amount: v.amount,
        consensus_verified: true,
    };
    exec.bridge_mint_against_lock(&mut ledger, &good)
        .expect("the same lock mints once the authorized relayer runs (nullifier was rolled back)");
    let (locked, live) = read_supply(ledger.get(&ledger_cell).unwrap());
    assert_eq!((locked, live), (400, 400));
}
