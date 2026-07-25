//! The live EVM inbound-relayer round-trip soundness proof.
//!
//! This proves the OFF-CHAIN Ethereum relayer drives the full inbound bridge
//! against a (mock) Ethereum JSON-RPC — the watching service the library was
//! missing (the `ethereum` module was outbound settlement only):
//!
//! 1. a finalized `Deposit` into the bridge contract → the relayer observes it
//!    ([`EthRelayer::observe_deposits`]), verifying finality + the
//!    escrow-to-contract binding (BR-2-B) + receipt inclusion;
//! 2. THE forged-inbound-message fix (finding #1): an RPC-only observation
//!    ([`EthDepositTrust::RpcStructureOnly`]) is FAIL-CLOSED — both the mint leg and
//!    the escrow leg DERIVE `consensus_verified = false`, so the committed
//!    `bridge_mint_against_lock` / `bridge_record_escrow` refuse it with
//!    `TrustTooLow`. A lying/MITM RPC that fabricates a `Deposit` log + receipt +
//!    finalized head mints NOTHING and draws NO escrow;
//! 3. only a light-client-verified deposit ([`EthDepositTrust::LightClientVerified`]
//!    — the test's verified-path equivalent until the full `eth_lightclient` wiring
//!    lands) mints CONSERVING mirror credit through the committed,
//!    multi-relayer-safe path (Σδ=0, consume-once nullifier);
//! 4. a SECOND relayer racing the same verified deposit is REFUSED by the committed
//!    nullifier (no double-mint);
//! 5. a deposit from an attacker contract is refused at observe;
//! 6. an un-finalized deposit (a lying RPC leaks it) is refused at observe.
//!
//! The mock RPC models the real finalized/safe/latest split, so the finality gate
//! is genuinely exercised; the same `observe → BridgeMintRequest` path runs against
//! the live `EthJsonRpc` client in production (the only swap is the [`EthRpc`]
//! impl). The in-circuit witness of EVM finality (so a dregg LIGHT client, not a
//! re-executing relayer, sees the backing) is the circuit swarm's VK-epoch
//! (`dregg_circuit::bridge_action_witness`) — out of scope here.

use dregg_bridge::ethereum_relayer::{
    EthBridgeConfig, EthDepositTrust, EthRelayer, EthRelayerError, MockEthRpc,
    eth_deposit_nullifier,
};
use dregg_cell::{AuthRequired, Cell, CellId, EFFECT_MINT, Ledger, Permissions};
use dregg_turn::{
    BridgeMintError, ComputronCosts, TurnExecutor, new_mirror_ledger_cell, read_supply,
};

const CONTRACT: [u8; 20] = [0x11u8; 20];
const ATTACKER: [u8; 20] = [0x99u8; 20];
const MIRROR_ASSET: [u8; 32] = [0x77u8; 32];

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

fn config() -> EthBridgeConfig {
    EthBridgeConfig::new(CONTRACT, 1, 1_000_000, 0)
}

fn tx(n: u8) -> [u8; 32] {
    let mut t = [0u8; 32];
    t[0] = n;
    t[31] = n.wrapping_mul(7).wrapping_add(3);
    t
}

/// THE FALSIFIER (finding #1): a deposit backed only by RPC data — no light-client
/// verification — is REFUSED. Both the escrow leg and the mint leg carry
/// `consensus_verified = false` (DERIVED from `RpcStructureOnly`, never hard-coded
/// `true`), so the committed executor refuses each with `TrustTooLow`: NO mint, NO
/// escrow draw, NO unbacked supply. This is the forged-inbound-message bridge drain,
/// closed — a lying/MITM/compromised RPC that fabricates a `Deposit` log + matching
/// receipt + finalized head can no longer mint attacker `$DREGG`.
#[test]
fn rpc_only_forged_deposit_is_refused() {
    let (mut ledger, recipient, issuer, ledger_cell) = scaffold(MIRROR_ASSET);
    let exec = TurnExecutor::new(ComputronCosts::zero());
    let amount = 500u64;
    let lock_id = [0x11u8; 32];

    // Exactly what a lying/MITM RPC fabricates: a "finalized" Deposit + a matching
    // success receipt over plain RPC. The relayer's structural gates (contract
    // address, topic, finality tag, receipt inclusion) all PASS — they are RPC-only.
    let mut rpc = MockEthRpc::new(100, 105, 110);
    rpc.insert_deposit(MockEthRpc::deposit_log(
        CONTRACT,
        lock_id,
        recipient,
        amount,
        90,
        tx(1),
        0,
    ));
    let relayer = EthRelayer::new(config(), rpc);
    let observed = relayer.observe_deposits().expect("scan")[0]
        .as_ref()
        .expect(
            "the structural verify still SURFACES the deposit (the gate refuses, not the observe)",
        )
        .clone();

    // It reaches only the fail-closed RPC grade.
    assert_eq!(observed.trust, EthDepositTrust::RpcStructureOnly);

    // The escrow leg cannot raise the backing (consensus_verified = false).
    assert!(!observed.to_escrow_record(ledger_cell).consensus_verified);
    assert_eq!(
        exec.bridge_record_escrow(&mut ledger, &observed.to_escrow_record(ledger_cell))
            .unwrap_err(),
        BridgeMintError::TrustTooLow,
        "an RPC-only deposit cannot record escrow backing"
    );

    // And the committed mint itself REFUSES it (TrustTooLow) — the drain is closed.
    let req = observed.to_bridge_mint_request(issuer, ledger_cell);
    assert!(!req.consensus_verified);
    assert_eq!(
        exec.bridge_mint_against_lock(&mut ledger, &req)
            .unwrap_err(),
        BridgeMintError::TrustTooLow,
        "an RPC-only (forged/MITM) deposit CANNOT mint"
    );

    // Nothing moved: no backing, no supply, no recipient credit.
    let (locked, live) = read_supply(ledger.get(&ledger_cell).unwrap());
    assert_eq!((locked, live), (0, 0), "no unbacked supply was created");
    assert_eq!(ledger.get(&recipient).unwrap().state.balance(), 0);
}

#[test]
fn relayer_deposit_to_finalized_to_conserving_mint() {
    let (mut ledger, recipient, issuer, ledger_cell) = scaffold(MIRROR_ASSET);
    let exec = TurnExecutor::new(ComputronCosts::zero());
    let amount = 500u64;
    let lock_id = [0x11u8; 32];

    // A REAL finalized Deposit into the bridge contract (block 90, finalized 100).
    let mut rpc = MockEthRpc::new(100, 105, 110);
    rpc.insert_deposit(MockEthRpc::deposit_log(
        CONTRACT,
        lock_id,
        recipient,
        amount,
        90,
        tx(1),
        0,
    ));

    // ── (1) the relayer WATCHES + VERIFIES the finalized deposit ─────────────
    let relayer = EthRelayer::new(config(), rpc);
    let results = relayer.observe_deposits().expect("scan");
    assert_eq!(results.len(), 1);
    let observed_rpc = results[0]
        .as_ref()
        .expect("the relayer observes the finalized deposit")
        .clone();
    assert_eq!(observed_rpc.amount, amount);
    assert_eq!(observed_rpc.recipient, recipient);
    assert_eq!(observed_rpc.finalized_block, 100);
    // The RPC-only observe is fail-closed and cannot mint (see the falsifier above).
    assert_eq!(observed_rpc.trust, EthDepositTrust::RpcStructureOnly);

    // The TEST'S VERIFIED-PATH EQUIVALENT: promote the SAME observed deposit to the
    // light-client-verified grade the full `eth_lightclient` wiring will produce
    // (EIP-1186 MPT inclusion under a beacon-finalized + sync-committee-verified
    // execution state root). Only this grade may mint.
    let mut observed = observed_rpc.clone();
    observed.trust = EthDepositTrust::LightClientVerified;

    // ── (2) MINT through the committed, conserving, multi-relayer-safe path ──
    // The INDEPENDENT escrow leg (raising committed currently_locked) is recorded
    // first; the mint DRAWS against it (non-vacuous conservation, red-team BR-2).
    exec.bridge_record_escrow(&mut ledger, &observed.to_escrow_record(ledger_cell))
        .expect("the verified deposit's escrow backing is recorded");
    let req = observed.to_bridge_mint_request(issuer, ledger_cell);
    assert!(req.consensus_verified);
    let receipt = exec
        .bridge_mint_against_lock(&mut ledger, &req)
        .expect("the verified deposit mints conserving mirror credit");
    assert_eq!(receipt.amount, amount);
    assert_eq!(receipt.currently_locked, amount);
    assert_eq!(receipt.live_supply, amount);

    // Conservation: live_supply ≤ currently_locked; recipient credited once.
    let (locked, live) = read_supply(ledger.get(&ledger_cell).unwrap());
    assert_eq!((locked, live), (amount, amount));
    assert!(live <= locked);
    assert_eq!(
        ledger.get(&recipient).unwrap().state.balance(),
        amount as i64,
        "recipient credited exactly the deposited amount"
    );

    // ── (3) a SECOND relayer racing the SAME deposit is refused (no double-mint) ─
    let mut rpc2 = MockEthRpc::new(100, 105, 110);
    rpc2.insert_deposit(MockEthRpc::deposit_log(
        CONTRACT,
        lock_id,
        recipient,
        amount,
        90,
        tx(1),
        0,
    ));
    let relayer2 = EthRelayer::new(config(), rpc2);
    let observed2_rpc = relayer2.observe_deposits().expect("scan")[0]
        .as_ref()
        .expect("a second relayer independently observes the same deposit")
        .clone();
    assert_eq!(
        observed2_rpc.nullifier,
        eth_deposit_nullifier(&CONTRACT, &lock_id),
        "the same deposit yields the same committed consume-once nullifier"
    );
    let mut observed2 = observed2_rpc;
    observed2.trust = EthDepositTrust::LightClientVerified;
    let req2 = observed2.to_bridge_mint_request(issuer, ledger_cell);
    assert_eq!(
        exec.bridge_mint_against_lock(&mut ledger, &req2)
            .unwrap_err(),
        BridgeMintError::DuplicateLock,
        "the committed nullifier refuses the second mint of the same deposit"
    );
    // Supply unchanged after the refused double-mint.
    let (locked, live) = read_supply(ledger.get(&ledger_cell).unwrap());
    assert_eq!((locked, live), (amount, amount));
}

#[test]
fn relayer_refuses_attacker_contract_round_trip() {
    // A finalized Deposit emitted by an ATTACKER contract (BR-2-B). It never
    // reaches the mint: the scan filters by the bridge address, and the direct
    // verify proves the explicit refusal.
    let recipient = CellId::from_bytes(pk(1));
    let mut rpc = MockEthRpc::new(100, 105, 110);
    rpc.insert_deposit(MockEthRpc::deposit_log(
        ATTACKER,
        [0x33u8; 32],
        recipient,
        500,
        90,
        tx(3),
        0,
    ));
    let relayer = EthRelayer::new(config(), rpc);
    assert!(
        relayer.observe_deposits().expect("scan").is_empty(),
        "an attacker-contract deposit is not even surfaced by the bridge-address scan"
    );
    let attacker_log =
        MockEthRpc::deposit_log(ATTACKER, [0x33u8; 32], recipient, 500, 90, tx(3), 0);
    assert_eq!(
        relayer
            .verify_finalized_log(&attacker_log, 100)
            .unwrap_err(),
        EthRelayerError::NotBridgeContract,
        "an un-escrowed deposit is refused before any mint"
    );
}

#[test]
fn relayer_refuses_unfinalized_deposit_round_trip() {
    // The deposit is at block 120 while the finalized head is 100 — a lying RPC
    // leaks it, and the defensive per-log finality re-check refuses it.
    let recipient = CellId::from_bytes(pk(1));
    let mut rpc = MockEthRpc::new(100, 105, 110);
    rpc.insert_deposit(MockEthRpc::deposit_log(
        CONTRACT,
        [0x55u8; 32],
        recipient,
        500,
        120,
        tx(5),
        0,
    ));
    rpc.set_leak_unfinalized(true);
    let relayer = EthRelayer::new(config(), rpc);
    let results = relayer.observe_deposits().expect("scan");
    assert!(
        matches!(
            results[0],
            Err(EthRelayerError::NotFinalized {
                block: 120,
                finalized: 100
            })
        ),
        "an un-finalized deposit is refused before any mint"
    );
}
