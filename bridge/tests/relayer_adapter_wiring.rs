//! The **live Solana relayer wired through the `InterchainAdapter` trust dial.**
//!
//! [`ObservedLock::to_bridge_mint_request_via_adapter`] routes an observed lock
//! through the unified [`DialAdapter<LockProofTrust>`] path, so
//! `consensus_verified` is `TrustRung::reached_consensus()` of the lock's dial —
//! NEVER a hand-set bool — and carries the named caller-responsibility
//! destination-federation check the chain-agnostic adapter does not perform.
//!
//! Both polarities run by DEFAULT:
//!
//! 1. **`ConsensusVerified` for THIS federation ⟹ mints** (the accept). A finalized
//!    lock verified to [`LockProofTrust::ConsensusVerified`], with a binding
//!    addressed to this federation, yields `consensus_verified = true` (through the
//!    rung, not a comparison) and mints conserving credit through the committed
//!    [`TurnExecutor::bridge_mint_against_lock`] (Σδ = 0).
//! 2. **`StructureOnly` ⟹ `TrustTooLow`** (the load-bearing reject). The SAME lock
//!    observed over a plain RPC reaches only [`LockProofTrust::StructureOnly`],
//!    which the adapter maps to the fail-closed `Rpc` rung, so the request carries
//!    `consensus_verified = false` and the committed mint refuses it. No supply
//!    moves.
//! 3. **A binding for a DIFFERENT federation is refused BEFORE minting** (the
//!    destination check). A `ConsensusVerified` lock whose binding is addressed to
//!    another federation is rejected with
//!    [`AdapterWiringError::WrongDestinationFederation`] — never credited here.
//! 4. **A binding that does not describe the observed lock is refused** (the
//!    consistency tooth): a mismatched amount/nullifier yields
//!    [`AdapterWiringError::BindingMismatch`].

use dregg_bridge::action_binding::PortableActionBinding;
use dregg_bridge::solana_consensus::{BankHashComponents, EpochStakeTable, ValidatorVote};
use dregg_bridge::solana_mirror::MirrorConfig;
use dregg_bridge::solana_relayer::{AdapterWiringError, MockSolanaRpc, RpcAccount, SolanaRelayer};
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
/// The federation THIS relayer serves — the binding's `destination_federation`
/// must equal it or the mint request is refused before minting.
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
/// the REAL finalized vault account, signed by ≥ 2/3 of [`stake_table`].
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
/// The statement-bound adapter reads the plaintext nullifier, recipient, amount,
/// and destination; an empty `proof_bytes` is therefore a focused fixture for the
/// request-construction boundary under test.  Proof verification is exercised by
/// the action-binding suite, not duplicated here.
fn binding_for(
    nullifier: [u8; 32],
    recipient: CellId,
    amount: u64,
    destination: [u8; 32],
) -> PortableActionBinding {
    PortableActionBinding {
        nullifier,
        recipient: recipient.0,
        destination_federation: destination,
        amount,
        proof_bytes: Vec::new(),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// (1) ConsensusVerified for THIS federation ⟹ the adapter path mints (Σδ = 0).
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn adapter_path_consensus_lock_for_this_federation_mints() {
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
        .expect("the relayer verifies the finalized lock to consensus");
    assert_eq!(observed.trust, LockProofTrust::ConsensusVerified);

    // Drive the UNIFIED adapter path with a binding addressed to THIS federation.
    let binding = binding_for(
        observed.nullifier.0,
        observed.recipient,
        amount,
        THIS_FEDERATION,
    );
    let req = observed
        .to_bridge_mint_request_via_adapter(binding, THIS_FEDERATION, issuer, ledger_cell)
        .expect("a consensus-verified lock for this federation builds a mint request");

    // consensus_verified came from TrustRung::reached_consensus(), not a hand bool.
    assert!(
        req.consensus_verified,
        "the ConsensusVerified dial reaches the Proof rung ⟹ consensus_verified = true"
    );
    assert_eq!(req.amount, amount);
    assert_eq!(req.recipient, recipient);
    assert_eq!(req.lock_nullifier, observed.nullifier);

    // Record the independent escrow leg, then the committed mint DRAWS against it.
    exec.bridge_record_escrow(&mut ledger, &observed.to_escrow_record(ledger_cell))
        .expect("consensus-verified escrow recorded");
    let receipt = exec
        .bridge_mint_against_lock(&mut ledger, &req)
        .expect("the adapter-built request mints conserving mirror credit");
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
// (2) StructureOnly ⟹ consensus_verified = false ⟹ TrustTooLow (load-bearing).
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn adapter_path_structure_only_lock_cannot_mint() {
    let (mut ledger, recipient, issuer, ledger_cell) = scaffold(MIRROR_ASSET);
    let exec = TurnExecutor::new(ComputronCosts::zero());
    let amount = 500u64;
    let lock_id = [0x11u8; 32];

    // The SAME finalized account, observed over a plain RPC (no vote set / stake
    // table) — exactly what a forged/MITM node can fabricate. Only StructureOnly.
    let mut rpc = MockSolanaRpc::new(100, 105, 110);
    rpc.insert_finalized(
        VAULT,
        MockSolanaRpc::lock_account(LOCK_PROGRAM, 1_000_000, 0, lock_id, recipient, amount),
    );
    let relayer = SolanaRelayer::new(config(), rpc);
    let observed = relayer
        .observe_vault_lock()
        .expect("the plain-RPC observe still surfaces the finalized lock");
    assert_eq!(observed.trust, LockProofTrust::StructureOnly);

    // Even for THIS federation, the StructureOnly dial maps to the fail-closed Rpc
    // rung, so the adapter sets consensus_verified = false.
    let binding = binding_for(
        observed.nullifier.0,
        observed.recipient,
        amount,
        THIS_FEDERATION,
    );
    let req = observed
        .to_bridge_mint_request_via_adapter(binding, THIS_FEDERATION, issuer, ledger_cell)
        .expect("the request still BUILDS (the committed gate, not the adapter, refuses it)");
    assert!(
        !req.consensus_verified,
        "a StructureOnly dial reaches the Rpc rung ⟹ consensus_verified = false"
    );

    // The committed mint refuses it BEFORE touching any state.
    assert_eq!(
        exec.bridge_mint_against_lock(&mut ledger, &req)
            .unwrap_err(),
        BridgeMintError::TrustTooLow,
        "an RPC-only (StructureOnly) lock CANNOT mint — the trustless invariant"
    );
    let (locked, live) = read_supply(ledger.get(&ledger_cell).unwrap());
    assert_eq!((locked, live), (0, 0), "no unbacked supply was created");
    assert_eq!(ledger.get(&recipient).unwrap().state.balance(), 0);
}

// ─────────────────────────────────────────────────────────────────────────────
// (3) A binding for a DIFFERENT federation is refused BEFORE any mint.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn adapter_path_wrong_federation_refused_before_minting() {
    let (ledger, recipient, issuer, ledger_cell) = scaffold(MIRROR_ASSET);
    let exec = TurnExecutor::new(ComputronCosts::zero());
    let amount = 500u64;
    let lock_id = [0x11u8; 32];

    let account =
        MockSolanaRpc::lock_account(LOCK_PROGRAM, 1_000_000, 0, lock_id, recipient, amount);
    let mut rpc = MockSolanaRpc::new(100, 105, 110);
    rpc.insert_finalized(VAULT, account.clone());
    let relayer = SolanaRelayer::new(config(), rpc);

    // A genuinely consensus-verified lock — the ONLY defect is the destination.
    let observed = relayer
        .observe_vault_lock_consensus(
            consensus_for(&account, lock_id, recipient, amount),
            &stake_table(),
            false,
        )
        .expect("a consensus-verified lock");
    assert_eq!(observed.trust, LockProofTrust::ConsensusVerified);

    // The binding is addressed to a DIFFERENT federation than this relayer serves.
    let binding = binding_for(
        observed.nullifier.0,
        observed.recipient,
        amount,
        OTHER_FEDERATION,
    );
    let err = observed
        .to_bridge_mint_request_via_adapter(binding, THIS_FEDERATION, issuer, ledger_cell)
        .expect_err("a lock destined for another federation is not credited here");
    assert_eq!(
        err,
        AdapterWiringError::WrongDestinationFederation {
            expected: THIS_FEDERATION,
            found: OTHER_FEDERATION,
        },
        "the destination-federation check (the named caller responsibility) refuses it"
    );

    // Nothing minted, nothing escrowed — the refusal was before any state change.
    let (locked, live) = read_supply(ledger.get(&ledger_cell).unwrap());
    assert_eq!((locked, live), (0, 0), "no supply moved");
    assert_eq!(ledger.get(&recipient).unwrap().state.balance(), 0);
    // And there is no way to reach the committed mint without a request.
    let _ = &exec; // exec is held to prove no mint call was needed to reject.
}

// ─────────────────────────────────────────────────────────────────────────────
// (4) A binding that does not describe the observed lock is refused.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn adapter_path_mismatched_binding_refused() {
    let (_ledger, recipient, issuer, ledger_cell) = scaffold(MIRROR_ASSET);
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
        .expect("a consensus-verified lock");

    // A binding for THIS federation but a DIFFERENT amount than the observed lock:
    // a caller cannot pair this lock's trust dial with an unrelated amount.
    let wrong_amount = binding_for(
        observed.nullifier.0,
        observed.recipient,
        amount + 1,
        THIS_FEDERATION,
    );
    assert_eq!(
        observed
            .to_bridge_mint_request_via_adapter(wrong_amount, THIS_FEDERATION, issuer, ledger_cell)
            .unwrap_err(),
        AdapterWiringError::BindingMismatch,
        "a binding whose amount disagrees with the observed lock is refused"
    );

    // A binding with a DIFFERENT nullifier is likewise refused.
    let wrong_nf = binding_for([0x9Cu8; 32], observed.recipient, amount, THIS_FEDERATION);
    assert_eq!(
        observed
            .to_bridge_mint_request_via_adapter(wrong_nf, THIS_FEDERATION, issuer, ledger_cell)
            .unwrap_err(),
        AdapterWiringError::BindingMismatch,
        "a binding whose nullifier disagrees with the observed lock is refused"
    );

    // A binding for the right lock and federation cannot redirect its credit.
    let wrong_recipient = binding_for(
        observed.nullifier.0,
        CellId([0x9Du8; 32]),
        amount,
        THIS_FEDERATION,
    );
    assert_eq!(
        observed
            .to_bridge_mint_request_via_adapter(
                wrong_recipient,
                THIS_FEDERATION,
                issuer,
                ledger_cell,
            )
            .unwrap_err(),
        AdapterWiringError::BindingMismatch,
        "a proof-bound recipient cannot be substituted at request construction"
    );
}
