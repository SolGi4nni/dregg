//! The live-relayer round-trip soundness proof — with the BR-1/BR-2/BR-3 fix.
//!
//! This proves the OFF-CHAIN relayer drives the full inbound bridge against a
//! (mock) Solana RPC, and that the red-team's unbacked-mint path is closed:
//!
//! 1. **A `StructureOnly` observation CANNOT mint** (BR-1). The plain-RPC verify a
//!    forged/MITM RPC can fabricate reaches only `LockProofTrust::StructureOnly`,
//!    so `to_bridge_mint_request` carries `consensus_verified = false` and the
//!    committed `bridge_mint_against_lock` refuses it with `TrustTooLow`. The same
//!    StructureOnly evidence cannot even raise the escrow backing.
//! 2. **A `ConsensusVerified` observation mints conserving credit** (the sound
//!    path): the relayer verifies the lock to `ConsensusVerified` against a stake
//!    table (`observe_vault_lock_consensus` — the previously-dead consensus
//!    machinery, now on the live path), records the INDEPENDENT escrow leg, and
//!    the mint DRAWS against it (Σδ=0, recipient credited, well debited).
//! 3. **Conservation BITES** (BR-2, now non-vacuous): a mint whose draw exceeds
//!    the independently-recorded escrow is refused with `InsufficientLocked`.
//! 4. **The double-mint nullifier holds**: a second relayer racing the same lock
//!    is refused by the committed nullifier.
//! 5. **TLS is the default transport** (BR-3): a plaintext `http://` RPC endpoint
//!    is refused; plaintext is an explicit loopback-only dev opt-in.
//!
//! The fully-trustless in-circuit witness of Solana consensus (so a dregg LIGHT
//! client, not a re-executing relayer, sees the backing) is the circuit swarm's
//! G1 VK-epoch (`dregg_circuit::bridge_action_air`) — out of scope here.

use dregg_bridge::solana_consensus::{BankHashComponents, EpochStakeTable, ValidatorVote};
use dregg_bridge::solana_mirror::MirrorConfig;
use dregg_bridge::solana_relayer::{
    JsonRpcTransport, MockSolanaRpc, RelayerError, RpcAccount, RpcError, SolanaJsonRpc,
    SolanaRelayer,
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

/// Consensus evidence CONSISTENT with the relayer's single-leaf accounts hash over
/// the REAL finalized vault account (so `bank_components.accounts_hash` matches the
/// inclusion the relayer builds itself), signed by ≥2/3 of [`stake_table`]. This is
/// the snapshot/geyser bundle a real operator supplies; the relayer cross-checks it.
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

// ─────────────────────────────────────────────────────────────────────────────
// (1) BR-1: a StructureOnly observation (the forged/MITM-RPC shape) CANNOT mint.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn structure_only_observation_cannot_mint() {
    let (mut ledger, recipient, issuer, ledger_cell) = scaffold(MIRROR_ASSET);
    let exec = TurnExecutor::new(ComputronCosts::zero());
    let amount = 500u64;
    let lock_id = [0x11u8; 32];

    // A lock that LOOKS finalized over a plain RPC — exactly what a lying/MITM RPC
    // can fabricate. The relayer reaches only StructureOnly here.
    let mut rpc = MockSolanaRpc::new(100, 105, 110);
    rpc.insert_finalized(
        VAULT,
        MockSolanaRpc::lock_account(LOCK_PROGRAM, 1_000_000, 0, lock_id, recipient, amount),
    );
    let relayer = SolanaRelayer::new(config(), rpc);
    let observed = relayer
        .observe_vault_lock()
        .expect("the structure-only observe still surfaces the lock");
    assert_eq!(observed.trust, LockProofTrust::StructureOnly);

    // The escrow leg from a StructureOnly observation is REFUSED — it cannot raise
    // the backing it would then mint against.
    assert_eq!(
        exec.bridge_record_escrow(&mut ledger, &observed.to_escrow_record(ledger_cell))
            .unwrap_err(),
        BridgeMintError::TrustTooLow,
        "a StructureOnly observation cannot record escrow backing"
    );

    // And the committed mint itself REFUSES it (TrustTooLow) — the PoC unbacked
    // mint is closed. No state moved.
    let req = observed.to_bridge_mint_request(issuer, ledger_cell);
    assert!(!req.consensus_verified);
    assert_eq!(
        exec.bridge_mint_against_lock(&mut ledger, &req)
            .unwrap_err(),
        BridgeMintError::TrustTooLow,
        "a StructureOnly (RPC-trust-only) proof CANNOT mint"
    );
    let (locked, live) = read_supply(ledger.get(&ledger_cell).unwrap());
    assert_eq!((locked, live), (0, 0), "no unbacked supply was created");
    assert_eq!(ledger.get(&recipient).unwrap().state.balance(), 0);
}

// ─────────────────────────────────────────────────────────────────────────────
// (2) The sound path: ConsensusVerified → escrow → conserving mint.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn relayer_consensus_lock_to_conserving_mint() {
    let (mut ledger, recipient, issuer, ledger_cell) = scaffold(MIRROR_ASSET);
    let exec = TurnExecutor::new(ComputronCosts::zero());
    let amount = 500u64;
    let lock_id = [0x11u8; 32];

    let account =
        MockSolanaRpc::lock_account(LOCK_PROGRAM, 1_000_000, 0, lock_id, recipient, amount);
    let mut rpc = MockSolanaRpc::new(100, 105, 110);
    rpc.insert_finalized(VAULT, account.clone());
    let relayer = SolanaRelayer::new(config(), rpc);

    // ── (a) verify the lock to ConsensusVerified against the stake table ───────
    let consensus = consensus_for(&account, lock_id, recipient, amount);
    let observed = relayer
        .observe_vault_lock_consensus(consensus, &stake_table(), false)
        .expect("the relayer verifies the finalized lock to consensus");
    assert_eq!(observed.trust, LockProofTrust::ConsensusVerified);
    assert_eq!(observed.amount, amount);

    // ── (b) record the INDEPENDENT escrow leg (raises currently_locked) ───────
    let escrow = exec
        .bridge_record_escrow(&mut ledger, &observed.to_escrow_record(ledger_cell))
        .expect("consensus-verified escrow recorded");
    assert_eq!(escrow.currently_locked, amount);
    let (locked, live) = read_supply(ledger.get(&ledger_cell).unwrap());
    assert_eq!(
        (locked, live),
        (amount, 0),
        "escrow raised locked, no live yet"
    );

    // ── (c) the mint DRAWS against the escrow (Σδ=0) ───────────────────────────
    let req = observed.to_bridge_mint_request(issuer, ledger_cell);
    assert!(req.consensus_verified);
    let receipt = exec
        .bridge_mint_against_lock(&mut ledger, &req)
        .expect("the consensus-verified lock mints conserving mirror credit");
    assert_eq!(receipt.currently_locked, amount);
    assert_eq!(receipt.live_supply, amount);

    let (locked, live) = read_supply(ledger.get(&ledger_cell).unwrap());
    assert_eq!((locked, live), (amount, amount));
    assert!(live <= locked);
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
        "the issuer well carries the conserving −supply (Σδ=0)"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// (3) BR-2: conservation is non-vacuous — a draw exceeding the backing is refused.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn mint_exceeding_locked_is_refused() {
    let (mut ledger, recipient, issuer, ledger_cell) = scaffold(MIRROR_ASSET);
    let exec = TurnExecutor::new(ComputronCosts::zero());

    // Lock A: amount 500, escrow recorded + minted → locked=500, live=500.
    let lock_a = [0x11u8; 32];
    let acct_a = MockSolanaRpc::lock_account(LOCK_PROGRAM, 1_000_000, 0, lock_a, recipient, 500);
    let mut rpc = MockSolanaRpc::new(100, 105, 110);
    rpc.insert_finalized(VAULT, acct_a.clone());
    let relayer = SolanaRelayer::new(config(), rpc);
    let observed_a = relayer
        .observe_vault_lock_consensus(
            consensus_for(&acct_a, lock_a, recipient, 500),
            &stake_table(),
            false,
        )
        .unwrap();
    exec.bridge_record_escrow(&mut ledger, &observed_a.to_escrow_record(ledger_cell))
        .unwrap();
    exec.bridge_mint_against_lock(
        &mut ledger,
        &observed_a.to_bridge_mint_request(issuer, ledger_cell),
    )
    .unwrap();
    let (locked, live) = read_supply(ledger.get(&ledger_cell).unwrap());
    assert_eq!((locked, live), (500, 500));

    // Lock B: a DISTINCT consensus-verified lock for 100 — but its escrow leg is
    // NOT recorded (the inflation shape). The mint draws against the backing that
    // is fully committed to lock A → live 500 + 100 > locked 500 → REFUSED.
    let lock_b = [0x22u8; 32];
    let acct_b = MockSolanaRpc::lock_account(LOCK_PROGRAM, 1_000_000, 0, lock_b, recipient, 100);
    let mut rpc_b = MockSolanaRpc::new(100, 105, 110);
    rpc_b.insert_finalized(VAULT, acct_b.clone());
    let relayer_b = SolanaRelayer::new(config(), rpc_b);
    let observed_b = relayer_b
        .observe_vault_lock_consensus(
            consensus_for(&acct_b, lock_b, recipient, 100),
            &stake_table(),
            false,
        )
        .unwrap();
    let req_b = observed_b.to_bridge_mint_request(issuer, ledger_cell);
    assert!(
        req_b.consensus_verified,
        "lock B IS consensus-verified — the refusal is conservation, not trust"
    );
    assert_eq!(
        exec.bridge_mint_against_lock(&mut ledger, &req_b)
            .unwrap_err(),
        BridgeMintError::InsufficientLocked {
            live: 500,
            locked: 500,
            amount: 100,
        },
        "a mint exceeding the independently-recorded escrow is refused (conservation bites)"
    );
    // Supply unchanged after the refused over-mint.
    let (locked, live) = read_supply(ledger.get(&ledger_cell).unwrap());
    assert_eq!((locked, live), (500, 500), "no unbacked supply created");

    // Recording lock B's escrow first makes the SAME mint succeed → conservation
    // is a real, two-sided constraint (the backstop is reachable BOTH ways).
    exec.bridge_record_escrow(&mut ledger, &observed_b.to_escrow_record(ledger_cell))
        .unwrap();
    exec.bridge_mint_against_lock(
        &mut ledger,
        &observed_b.to_bridge_mint_request(issuer, ledger_cell),
    )
    .expect("once its escrow is recorded, lock B mints");
    let (locked, live) = read_supply(ledger.get(&ledger_cell).unwrap());
    assert_eq!((locked, live), (600, 600));
}

// ─────────────────────────────────────────────────────────────────────────────
// (4) The double-mint nullifier holds across independent relayers.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn second_relayer_racing_same_lock_is_refused() {
    let (mut ledger, recipient, issuer, ledger_cell) = scaffold(MIRROR_ASSET);
    let exec = TurnExecutor::new(ComputronCosts::zero());
    let amount = 500u64;
    let lock_id = [0x11u8; 32];
    let account =
        MockSolanaRpc::lock_account(LOCK_PROGRAM, 1_000_000, 0, lock_id, recipient, amount);

    let mut rpc = MockSolanaRpc::new(100, 105, 110);
    rpc.insert_finalized(VAULT, account.clone());
    let relayer = SolanaRelayer::new(config(), rpc);
    let observed = relayer
        .observe_vault_lock_consensus(
            consensus_for(&account, lock_id, recipient, amount),
            &stake_table(),
            false,
        )
        .unwrap();
    exec.bridge_record_escrow(&mut ledger, &observed.to_escrow_record(ledger_cell))
        .unwrap();
    exec.bridge_mint_against_lock(
        &mut ledger,
        &observed.to_bridge_mint_request(issuer, ledger_cell),
    )
    .expect("first mint commits");

    // A SECOND relayer independently observes + consensus-verifies the SAME lock.
    let mut rpc2 = MockSolanaRpc::new(100, 105, 110);
    rpc2.insert_finalized(VAULT, account.clone());
    let relayer2 = SolanaRelayer::new(config(), rpc2);
    let observed2 = relayer2
        .observe_vault_lock_consensus(
            consensus_for(&account, lock_id, recipient, amount),
            &stake_table(),
            false,
        )
        .unwrap();
    assert_eq!(observed2.nullifier, observed.nullifier);

    // Its escrow leg is refused (the lock's escrow was already recorded once)…
    assert_eq!(
        exec.bridge_record_escrow(&mut ledger, &observed2.to_escrow_record(ledger_cell))
            .unwrap_err(),
        BridgeMintError::DuplicateLock,
        "the escrow nullifier refuses recording the same lock's backing twice"
    );
    // …and its mint is refused by the committed mint nullifier — no double-mint.
    assert_eq!(
        exec.bridge_mint_against_lock(
            &mut ledger,
            &observed2.to_bridge_mint_request(issuer, ledger_cell)
        )
        .unwrap_err(),
        BridgeMintError::DuplicateLock,
        "the committed mint nullifier refuses the second mint of the same lock"
    );
    let (locked, live) = read_supply(ledger.get(&ledger_cell).unwrap());
    assert_eq!((locked, live), (amount, amount));
}

// ─────────────────────────────────────────────────────────────────────────────
// (5) BR-3: TLS is the default transport; plaintext is loopback-only opt-in.
// ─────────────────────────────────────────────────────────────────────────────

struct NoTransport;
impl JsonRpcTransport for NoTransport {
    fn post(&self, _url: &str, _body: &str) -> Result<String, RpcError> {
        Err(RpcError::Transport("unused".into()))
    }
}

#[test]
fn default_transport_requires_tls() {
    // A plaintext public RPC endpoint is REFUSED by the default constructor.
    assert!(
        matches!(
            SolanaJsonRpc::new("http://api.mainnet-beta.solana.com", NoTransport),
            Err(RpcError::Transport(_))
        ),
        "plaintext http:// is refused by the TLS-default constructor (BR-3)"
    );
    // https:// is accepted.
    assert!(SolanaJsonRpc::new("https://api.mainnet-beta.solana.com", NoTransport).is_ok());

    // The explicit local-dev opt-in permits ONLY loopback plaintext.
    assert!(SolanaJsonRpc::new_plaintext_local_dev("http://127.0.0.1:8899", NoTransport).is_ok());
    assert!(SolanaJsonRpc::new_plaintext_local_dev("http://localhost:8899", NoTransport).is_ok());
    assert!(
        matches!(
            SolanaJsonRpc::new_plaintext_local_dev("http://evil.example.com:8899", NoTransport),
            Err(RpcError::Transport(_))
        ),
        "the local-dev opt-in refuses a non-loopback plaintext endpoint (BR-3)"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// Observe-time refusals (unchanged: refused BEFORE any mint).
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn relayer_refuses_unescrowed_lock_round_trip() {
    // A finalized account owned by an ATTACKER program (the self-asserted-blob
    // attack, BR-2-B). It never reaches the mint.
    let recipient = CellId::from_bytes(pk(1));
    let account =
        MockSolanaRpc::lock_account([0x99u8; 32], 1_000_000, 0, [0x33u8; 32], recipient, 500);
    let mut rpc = MockSolanaRpc::new(100, 105, 110);
    rpc.insert_finalized(VAULT, account.clone());
    let relayer = SolanaRelayer::new(config(), rpc);
    assert_eq!(
        relayer
            .observe_vault_lock_consensus(
                consensus_for(&account, [0x33u8; 32], recipient, 500),
                &stake_table(),
                false
            )
            .unwrap_err(),
        RelayerError::NotBridgeVault,
        "an un-escrowed lock is refused before any mint"
    );
}

#[test]
fn relayer_refuses_unfinalized_lock_round_trip() {
    // The lock is visible at confirmed but NOT finalized — never minted against.
    let recipient = CellId::from_bytes(pk(1));
    let mut rpc = MockSolanaRpc::new(100, 105, 110);
    rpc.insert_confirmed_only(
        VAULT,
        MockSolanaRpc::lock_account(LOCK_PROGRAM, 1_000_000, 0, [0x55u8; 32], recipient, 500),
    );
    let relayer = SolanaRelayer::new(config(), rpc);
    assert_eq!(
        relayer.observe_vault_lock().unwrap_err(),
        RelayerError::NotFinalized,
        "an un-finalized lock is refused before any mint"
    );
}
