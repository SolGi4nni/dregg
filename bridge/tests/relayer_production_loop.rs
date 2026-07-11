//! The **production observation→mint LOOP** wired through the geyser-feed seam.
//!
//! [`SolanaRelayer::scan_to_mint_requests`] scans the lock program for finalized
//! locks and, for each one, fetches its [`ConsensusEvidence`] through the
//! [`ConsensusEvidenceSource`] seam (the geyser feed), re-observes it to
//! [`LockProofTrust::ConsensusVerified`] against the tracked stake table, and
//! drives it through the unified [`InterchainAdapter`] trust dial
//! ([`ObservedLock::to_bridge_mint_request_via_adapter`]) to a committed-mint
//! request — so a scan of on-chain locks actually produces mint requests down the
//! trust-dial path.
//!
//! Both polarities run by DEFAULT:
//!
//! 1. **A lock WITH consensus evidence, for THIS federation ⟹ a mint-ready
//!    request** the committed [`TurnExecutor::bridge_mint_against_lock`] accepts
//!    (Σδ = 0).
//! 2. **A lock WITHOUT consensus evidence (the feed has none) ⟹ a `StructureOnly`
//!    request** carrying `consensus_verified = false`; the committed mint refuses it
//!    with `TrustTooLow`. The loop does NOT mint it.
//! 3. **A lock addressed to a DIFFERENT federation ⟹ refused before minting** with
//!    [`AdapterWiringError::WrongDestinationFederation`].
//! 4. **One scan, heterogeneous ⟹ mixed entries**: the bridge vault lock mints
//!    while a program-owned account that is NOT the bridge vault surfaces as a typed
//!    [`RelayerError::NotBridgeVault`] observe-refusal — in the SAME scan.
//!
//! # The named live residual (NOT faked here)
//!
//! The [`ConsensusEvidenceSource`] production impl is a live geyser / snapshot vote
//! feed (Yellowstone gRPC geyser, or a validator snapshot's vote-account + Tower
//! state) — it is NOT built in the relayer module, and this test does NOT stand up a
//! real geyser stream. [`MockConsensusFeed`] holds pre-assembled evidence keyed by
//! `lock_id`; whatever it yields is still cross-checked against the on-chain account
//! and re-counted against the stake table by `verify_lock_proof_consensus`, so a
//! lying feed is refused exactly as a lying geyser would be. The wire-format
//! ingestion (parsing real vote `Transaction`s, sourcing the `EpochStakeTable`) is
//! the honest remaining adapter layer named in
//! `docs/deos/TRUSTLESS-SOLANA-BRIDGE.md`.

use dregg_bridge::action_binding::PortableActionBinding;
use dregg_bridge::solana_consensus::{BankHashComponents, EpochStakeTable, ValidatorVote};
use dregg_bridge::solana_mirror::MirrorConfig;
use dregg_bridge::solana_relayer::{
    AdapterWiringError, LoopEntry, MockConsensusFeed, MockSolanaRpc, ObservedLock, RelayerError,
    RpcAccount, SolanaRelayer,
};
use dregg_bridge::solana_trustless::{ConsensusEvidence, LockProofTrust};
use dregg_bridge::solana_wire::{accounts_merkle_node, encode_lock_record, solana_account_hash};
use dregg_cell::{AuthRequired, Cell, CellId, EFFECT_MINT, Ledger, Permissions};
use dregg_turn::{
    BridgeMintError, ComputronCosts, TurnExecutor, new_mirror_ledger_cell, read_supply,
};
use ed25519_dalek::SigningKey;

const SPL_MINT: [u8; 32] = [0xABu8; 32];
const MIRROR_ASSET: [u8; 32] = [0x77u8; 32];
const VAULT: [u8; 32] = [0x22u8; 32];
const LOCK_PROGRAM: [u8; 32] = [0x07u8; 32];
/// The federation THIS relayer serves.
const THIS_FEDERATION: [u8; 32] = [0x5Au8; 32];
/// A DIFFERENT federation — a binding addressed here must NOT be credited on ours.
const OTHER_FEDERATION: [u8; 32] = [0xE7u8; 32];
/// The stake-table epoch the consensus fixtures vote under.
const EPOCH: u64 = 5;

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

fn derived_well_id(token_id: &[u8; 32]) -> CellId {
    let well_pubkey = blake3::derive_key("dregg-issuer-well-key-v1", token_id);
    CellId::derive_raw(&well_pubkey, token_id)
}

/// `(ledger, recipient, issuer-holding-the-mint-cap, committed-ledger-cell)`.
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

    let ledger_cell = new_mirror_ledger_cell(pk(9), [0x44u8; 32]);
    let ledger_cell_id = ledger_cell.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(recipient).unwrap();
    ledger.insert_cell(issuer).unwrap();
    ledger.insert_cell(ledger_cell).unwrap();

    (ledger, recipient_id, issuer_id, ledger_cell_id)
}

fn config() -> MirrorConfig {
    MirrorConfig {
        spl_mint: SPL_MINT,
        asset: MIRROR_ASSET,
        oracle_keys: vec![],
        min_amount: 1,
        max_amount: 1_000_000,
        vault_account: VAULT,
        lock_program: LOCK_PROGRAM,
        pinned_anchor_epoch: None,
        pinned_anchor_root: None,
    }
}

fn vk(seed: u8) -> SigningKey {
    SigningKey::from_bytes(&[seed; 32])
}

/// Three validators, 400/400/200 stake. The first two (800/1000 = 80%) clear 2/3.
fn stake_table() -> EpochStakeTable {
    EpochStakeTable::from_entries(
        EPOCH,
        [
            (vk(11).verifying_key().to_bytes(), 400),
            (vk(12).verifying_key().to_bytes(), 400),
            (vk(13).verifying_key().to_bytes(), 200),
        ],
    )
}

/// Consensus evidence consistent with the relayer's single-leaf accounts hash over
/// the REAL finalized vault account, signed by ≥ 2/3 of [`stake_table`]. This is
/// what the live geyser feed would deliver; the mock feed hands it back verbatim and
/// the real verify still cross-checks it against the on-chain account.
fn consensus_for(
    account: &RpcAccount,
    lock_id: [u8; 32],
    recipient: CellId,
    amount: u64,
) -> ConsensusEvidence {
    let vault_data = encode_lock_record(&lock_id, &recipient, amount);
    let leaf = solana_account_hash(
        account.lamports,
        &account.owner,
        account.executable,
        account.rent_epoch,
        &vault_data,
        &VAULT,
    );
    let accounts_hash = accounts_merkle_node(&[leaf]);
    let slot = 12_345u64;
    let bank_components = BankHashComponents {
        parent_bank_hash: [0x01u8; 32],
        accounts_hash,
        signature_count: 2,
        last_blockhash: [0u8; 32],
    };
    let bank_hash = bank_components.compute();
    let votes = vec![
        ValidatorVote::sign(&vk(11), slot, bank_hash),
        ValidatorVote::sign(&vk(12), slot, bank_hash),
    ];
    ConsensusEvidence {
        slot,
        bank_hash,
        epoch: EPOCH,
        voted_stake: 800,
        total_stake: 1000,
        votes,
        bank_components,
        poh: None,
    }
}

/// A `PortableActionBinding` for the observed lock, addressed to `destination`.
///
/// The adapter's `into_mint_request` decision + the relayer's destination check read
/// only the plaintext limbs (nullifier / amount / destination), so an empty
/// `proof_bytes` is a faithful fixture (as in `interchain_adapter`'s own unit tests)
/// — we do not run the STARK prover here.
fn binding_for(nullifier: [u8; 32], amount: u64, destination: [u8; 32]) -> PortableActionBinding {
    PortableActionBinding {
        nullifier,
        recipient: [0x33u8; 32],
        destination_federation: destination,
        amount,
        proof_bytes: Vec::new(),
    }
}

/// A binding lookup addressing every observed lock to `destination` (the relayed
/// cross-chain message the feed pairs with each lock).
fn bindings_to(destination: [u8; 32]) -> impl Fn(&ObservedLock) -> Option<PortableActionBinding> {
    move |lock: &ObservedLock| Some(binding_for(lock.nullifier.0, lock.amount, destination))
}

// ─────────────────────────────────────────────────────────────────────────────
// (1) A finalized lock WITH consensus evidence, for THIS federation ⟹ the loop
//     produces a mint-ready request that the committed mint accepts (Σδ = 0).
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn loop_mints_consensus_verified_lock_for_this_federation() {
    let (mut ledger, recipient, issuer, ledger_cell) = scaffold(MIRROR_ASSET);
    let exec = TurnExecutor::new(ComputronCosts::zero());
    let amount = 500u64;
    let lock_id = [0x11u8; 32];

    let account =
        MockSolanaRpc::lock_account(LOCK_PROGRAM, 1_000_000, 0, lock_id, recipient, amount);
    let mut rpc = MockSolanaRpc::new(100, 105, 110);
    rpc.insert_finalized(VAULT, account.clone());
    let relayer = SolanaRelayer::new(config(), rpc);

    // The geyser feed delivers the vote set + bank hash for this lock's slot.
    let mut feed = MockConsensusFeed::new();
    feed.insert(lock_id, consensus_for(&account, lock_id, recipient, amount));

    // THE LOOP: scan → per-lock fetch evidence → re-observe at consensus → route
    // through the adapter trust dial → a committed-mint request.
    let entries = relayer
        .scan_to_mint_requests(
            &feed,
            bindings_to(THIS_FEDERATION),
            &stake_table(),
            false,
            THIS_FEDERATION,
            issuer,
            ledger_cell,
        )
        .expect("the scan RPC succeeds");
    assert_eq!(entries.len(), 1, "one bridge-vault lock in the scan");

    // The single entry is a mint-READY request: consensus_verified came from the
    // trust dial (ConsensusVerified), not a hand-set bool.
    let req = entries[0]
        .mint_ready()
        .expect("a consensus-verified lock for this federation is mint-ready");
    assert!(req.consensus_verified);
    assert_eq!(req.amount, amount);
    assert_eq!(req.recipient, recipient);

    // The INDEPENDENT consensus-verified escrow leg raises the committed backing
    // (BR-2/BR-3): a separate consensus observation, exactly as production records
    // escrow apart from the mint. Then the committed mint DRAWS against it.
    let escrow_observed = relayer
        .observe_vault_lock_consensus(
            consensus_for(&account, lock_id, recipient, amount),
            &stake_table(),
            false,
        )
        .expect("the escrow leg is independently consensus-verified");
    assert_eq!(escrow_observed.trust, LockProofTrust::ConsensusVerified);
    exec.bridge_record_escrow(&mut ledger, &escrow_observed.to_escrow_record(ledger_cell))
        .expect("consensus-verified escrow recorded");

    let receipt = exec
        .bridge_mint_against_lock(&mut ledger, req)
        .expect("the loop-built request mints conserving mirror credit");
    assert_eq!(receipt.currently_locked, amount);
    assert_eq!(receipt.live_supply, amount);

    let (locked, live) = read_supply(ledger.get(&ledger_cell).unwrap());
    assert_eq!((locked, live), (amount, amount));
    assert!(
        live <= locked,
        "live supply never exceeds the locked backing"
    );
    assert_eq!(
        ledger.get(&recipient).unwrap().state.balance(),
        amount as i64,
        "recipient credited exactly the locked amount"
    );
    assert_eq!(
        ledger
            .get(&derived_well_id(&MIRROR_ASSET))
            .unwrap()
            .state
            .balance(),
        -(amount as i64),
        "the issuer well carries the conserving −supply (Σδ = 0)"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// (2) A finalized lock WITHOUT consensus evidence (the feed has none) ⟹ a
//     StructureOnly request the committed mint refuses with TrustTooLow. NOT minted.
//
//     Under the single-vault escrow binding the vault holds one lock at a time, so
//     this polarity is a distinct scan of the SAME production-loop method; test (4)
//     proves multi-entry scan handling.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn loop_refuses_structure_only_lock_trust_too_low() {
    let (mut ledger, recipient, issuer, ledger_cell) = scaffold(MIRROR_ASSET);
    let exec = TurnExecutor::new(ComputronCosts::zero());
    let amount = 500u64;
    let lock_id = [0x11u8; 32];

    let mut rpc = MockSolanaRpc::new(100, 105, 110);
    rpc.insert_finalized(
        VAULT,
        MockSolanaRpc::lock_account(LOCK_PROGRAM, 1_000_000, 0, lock_id, recipient, amount),
    );
    let relayer = SolanaRelayer::new(config(), rpc);

    // The geyser feed has delivered NOTHING for this lock — plain-RPC observation
    // only, exactly what a forged/MITM node can fabricate. Stays StructureOnly.
    let feed = MockConsensusFeed::new();

    let entries = relayer
        .scan_to_mint_requests(
            &feed,
            bindings_to(THIS_FEDERATION),
            &stake_table(),
            false,
            THIS_FEDERATION,
            issuer,
            ledger_cell,
        )
        .expect("the scan RPC succeeds");
    assert_eq!(entries.len(), 1);

    // The loop DID build a request (the adapter path builds even StructureOnly), but
    // it is NOT mint-ready: consensus_verified = false.
    assert!(
        entries[0].mint_ready().is_none(),
        "a StructureOnly lock is never mint-ready"
    );
    let req = entries[0]
        .request()
        .expect("the request still builds (the committed gate refuses it, not the adapter)");
    assert!(
        !req.consensus_verified,
        "a StructureOnly dial reaches the Rpc rung ⟹ consensus_verified = false"
    );

    // The committed mint refuses it BEFORE any state changes.
    assert_eq!(
        exec.bridge_mint_against_lock(&mut ledger, req).unwrap_err(),
        BridgeMintError::TrustTooLow,
        "an RPC-only (StructureOnly) lock CANNOT mint — the trustless invariant"
    );
    let (locked, live) = read_supply(ledger.get(&ledger_cell).unwrap());
    assert_eq!((locked, live), (0, 0), "no unbacked supply was created");
    assert_eq!(ledger.get(&recipient).unwrap().state.balance(), 0);
}

// ─────────────────────────────────────────────────────────────────────────────
// (2b) A LYING feed — the untrusted geyser source delivers evidence signed by only
//      a 40% minority (below the 2/3 super-majority). The loop RE-OBSERVES on-chain
//      and re-counts the real stake, so the lie is refused (LoopEntry::Observe) and
//      NOTHING mints. The feed is untrusted; the on-chain re-count is the check.
// ─────────────────────────────────────────────────────────────────────────────

/// Consensus evidence for `lock_id` signed by a single 40%-stake validator — a feed
/// that LIES about having a super-majority. Same account/bank binding as
/// `consensus_for`; only the vote set is sub-threshold.
fn consensus_for_liar(
    account: &RpcAccount,
    lock_id: [u8; 32],
    recipient: CellId,
    amount: u64,
) -> ConsensusEvidence {
    let mut ev = consensus_for(account, lock_id, recipient, amount);
    ev.votes = vec![ValidatorVote::sign(&vk(11), ev.slot, ev.bank_hash)]; // 400/1000 = 40%
    ev
}

#[test]
fn loop_refuses_a_lying_feed_below_supermajority() {
    let (mut ledger, recipient, _issuer, ledger_cell) = scaffold(MIRROR_ASSET);
    let exec = TurnExecutor::new(ComputronCosts::zero());
    let amount = 500u64;
    let lock_id = [0x11u8; 32];

    let account =
        MockSolanaRpc::lock_account(LOCK_PROGRAM, 1_000_000, 0, lock_id, recipient, amount);
    let mut rpc = MockSolanaRpc::new(100, 105, 110);
    rpc.insert_finalized(VAULT, account.clone());
    let relayer = SolanaRelayer::new(config(), rpc);

    // The feed LIES: it delivers evidence, but signed by a 40% minority.
    let mut feed = MockConsensusFeed::new();
    feed.insert(
        lock_id,
        consensus_for_liar(&account, lock_id, recipient, amount),
    );

    let entries = relayer
        .scan_to_mint_requests(
            &feed,
            bindings_to(THIS_FEDERATION),
            &stake_table(),
            false,
            THIS_FEDERATION,
            recipient, // issuer cell unused on this path
            ledger_cell,
        )
        .expect("the scan RPC succeeds");
    assert_eq!(entries.len(), 1);

    // The on-chain re-observation re-counts the real stake and REFUSES the lie: the
    // entry is an Observe-error, not a mintable request.
    assert!(
        matches!(entries[0], LoopEntry::Observe(_)),
        "a sub-super-majority feed is refused at re-observation, not turned into a mint",
    );
    assert!(
        entries[0].mint_ready().is_none(),
        "a lying feed is never mint-ready"
    );
    assert!(
        entries[0].request().is_none(),
        "no mint request is built from a refused observation"
    );

    // Nothing moved.
    let (locked, live) = read_supply(ledger.get(&ledger_cell).unwrap());
    assert_eq!(
        (locked, live),
        (0, 0),
        "a lying feed creates no backing and no supply"
    );
    // The committed gate is never even reached; assert supply is untouched via a fresh read.
    let _ = &mut ledger;
    let _ = &exec;
}

// ─────────────────────────────────────────────────────────────────────────────
// (3) A consensus-verified lock addressed to a DIFFERENT federation ⟹ the loop
//     refuses it before any mint (WrongDestinationFederation).
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn loop_refuses_wrong_federation_lock() {
    let (ledger, recipient, issuer, ledger_cell) = scaffold(MIRROR_ASSET);
    let amount = 500u64;
    let lock_id = [0x11u8; 32];

    let account =
        MockSolanaRpc::lock_account(LOCK_PROGRAM, 1_000_000, 0, lock_id, recipient, amount);
    let mut rpc = MockSolanaRpc::new(100, 105, 110);
    rpc.insert_finalized(VAULT, account.clone());
    let relayer = SolanaRelayer::new(config(), rpc);

    // Genuine consensus evidence exists — the ONLY defect is the binding's
    // destination federation.
    let mut feed = MockConsensusFeed::new();
    feed.insert(lock_id, consensus_for(&account, lock_id, recipient, amount));

    let entries = relayer
        .scan_to_mint_requests(
            &feed,
            bindings_to(OTHER_FEDERATION),
            &stake_table(),
            false,
            THIS_FEDERATION,
            issuer,
            ledger_cell,
        )
        .expect("the scan RPC succeeds");
    assert_eq!(entries.len(), 1);

    match &entries[0] {
        LoopEntry::Refused(AdapterWiringError::WrongDestinationFederation { expected, found }) => {
            assert_eq!(*expected, THIS_FEDERATION);
            assert_eq!(*found, OTHER_FEDERATION);
        }
        other => panic!("expected WrongDestinationFederation refusal, got {other:?}"),
    }
    // No request was produced, so there is nothing to mint.
    assert!(entries[0].request().is_none());
    let (locked, live) = read_supply(ledger.get(&ledger_cell).unwrap());
    assert_eq!((locked, live), (0, 0), "no supply moved");
    assert_eq!(ledger.get(&recipient).unwrap().state.balance(), 0);
}

// ─────────────────────────────────────────────────────────────────────────────
// (4) One scan, heterogeneous: the bridge vault lock mints while a program-owned
//     account that is NOT the bridge vault is refused as NotBridgeVault — in the
//     SAME scan. Proves the loop drives a mixed-outcome scan, not a single lock.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn loop_over_heterogeneous_scan_mints_vault_and_refuses_foreign() {
    let (mut ledger, recipient, issuer, ledger_cell) = scaffold(MIRROR_ASSET);
    let exec = TurnExecutor::new(ComputronCosts::zero());
    let amount = 500u64;
    let vault_lock = [0x11u8; 32];
    let foreign_lock = [0x12u8; 32];
    // A program-owned account that is NOT the configured vault pubkey.
    let foreign_account_pubkey = [0x33u8; 32];

    let vault_account =
        MockSolanaRpc::lock_account(LOCK_PROGRAM, 1_000_000, 0, vault_lock, recipient, amount);
    let mut rpc = MockSolanaRpc::new(100, 105, 110);
    rpc.insert_finalized(VAULT, vault_account.clone());
    // Owned by the SAME lock program (so getProgramAccounts returns it) but at a
    // different pubkey than the configured vault — the scan must refuse it.
    rpc.insert_finalized(
        foreign_account_pubkey,
        MockSolanaRpc::lock_account(LOCK_PROGRAM, 1_000_000, 0, foreign_lock, recipient, amount),
    );
    let relayer = SolanaRelayer::new(config(), rpc);

    let mut feed = MockConsensusFeed::new();
    feed.insert(
        vault_lock,
        consensus_for(&vault_account, vault_lock, recipient, amount),
    );

    let entries = relayer
        .scan_to_mint_requests(
            &feed,
            bindings_to(THIS_FEDERATION),
            &stake_table(),
            false,
            THIS_FEDERATION,
            issuer,
            ledger_cell,
        )
        .expect("the scan RPC succeeds");
    assert_eq!(entries.len(), 2, "both program-owned accounts are scanned");

    // BTreeMap order: VAULT (0x22..) sorts before the foreign account (0x33..).
    let vault_req = entries[0]
        .mint_ready()
        .expect("the bridge vault lock is mint-ready");
    assert_eq!(vault_req.amount, amount);

    match &entries[1] {
        LoopEntry::Observe(RelayerError::NotBridgeVault) => {}
        other => panic!("expected NotBridgeVault for the foreign account, got {other:?}"),
    }

    // The mint-ready vault request mints against its independent escrow leg.
    let escrow_observed = relayer
        .observe_vault_lock_consensus(
            consensus_for(&vault_account, vault_lock, recipient, amount),
            &stake_table(),
            false,
        )
        .expect("escrow leg consensus-verified");
    exec.bridge_record_escrow(&mut ledger, &escrow_observed.to_escrow_record(ledger_cell))
        .expect("escrow recorded");
    let receipt = exec
        .bridge_mint_against_lock(&mut ledger, vault_req)
        .expect("the loop-built vault request mints");
    assert_eq!(receipt.live_supply, amount);
    assert_eq!(receipt.currently_locked, amount);
    assert_eq!(
        ledger.get(&recipient).unwrap().state.balance(),
        amount as i64
    );
}
