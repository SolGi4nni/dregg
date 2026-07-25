//! FALSIFIER for the weak-subjectivity committee store (interchain finding #13).
//!
//! The verify-core is sound *given* the right committee; finding #13 is that the
//! committee + `genesis_validators_root` were BARE CALLER ARGS, so an RPC-supplied
//! 512-key committee could mint `ConsensusProven` and make the 2/3-of-512 BLS floor
//! vacuous. [`WeakSubjectivityStore`] pins the trust root and only advances the
//! committee by a cryptographic rotation from the pinned genesis. This test proves,
//! on the SAME real mainnet fixture the sound-verify `end_to_end.rs` uses:
//!
//!   ACCEPT — a committee REACHED BY a valid `verify_committee_update` from the pinned
//!            genesis checkpoint verifies the real update and mints `ConsensusProven`
//!            (the committee came from the store, never from the caller).
//!   REJECT — an arbitrary / RPC-supplied 512-key committee that is NOT chained from
//!            the pinned genesis is refused at the rotation gate, is never installed,
//!            and `verify` then fails closed (no `ConsensusProven`).
//!   REJECT — a `genesis_validators_root` mismatch refuses the real signature.
//!   REJECT — a non-chained NEXT committee is refused by `advance` even after a
//!            genuinely-signed finalized update; the store's committee is unchanged.
//!   REJECT — even a governance-pinned FORGED genesis committee cannot verify a real
//!            signature (the BLS floor holds).

#[path = "fixtures/e2e_mainnet.rs"]
#[allow(dead_code)]
mod e2e;

use eth_lightclient::evm::{verify_erc20_holding_finalized, AccountClaim, HoldingTrust, Uint256};
use eth_lightclient::execution::ExecutionPayloadHeader;
use eth_lightclient::finality::{FinalizedExecution, LightClientHeader, LightClientUpdate};
use eth_lightclient::store::{StoreError, WeakSubjectivityStore};
use eth_lightclient::{
    BeaconBlockHeader, Error, SyncAggregate, SyncCommittee, SYNC_COMMITTEE_SIZE,
};

// -------------------- hex helpers (same as end_to_end.rs) --------------------

fn h32(s: &str) -> [u8; 32] {
    hex::decode(s).expect("hex32").try_into().expect("32 bytes")
}
fn h20(s: &str) -> [u8; 20] {
    hex::decode(s).expect("hex20").try_into().expect("20 bytes")
}
fn h48(s: &str) -> [u8; 48] {
    hex::decode(s).expect("hex48").try_into().expect("48 bytes")
}
fn h64(s: &str) -> [u8; 64] {
    hex::decode(s).expect("hex64").try_into().expect("64 bytes")
}
fn h96(s: &str) -> [u8; 96] {
    hex::decode(s).expect("hex96").try_into().expect("96 bytes")
}
fn h256(s: &str) -> [u8; 256] {
    hex::decode(s)
        .expect("hex256")
        .try_into()
        .expect("256 bytes")
}
fn branch(list: &[&str]) -> Vec<[u8; 32]> {
    list.iter().map(|s| h32(s)).collect()
}
fn nodes(list: &[&str]) -> Vec<Vec<u8>> {
    list.iter().map(|s| hex::decode(s).expect("node")).collect()
}
fn u256(s: &str) -> Uint256 {
    Uint256::from_str_radix(s, 16).expect("u256 hex")
}

// -------------------- fixture assembly --------------------

fn gvr() -> [u8; 32] {
    h32(e2e::GENESIS_VALIDATORS_ROOT)
}

/// The REAL period-1800 mainnet sync committee (512 compressed G1 pubkeys + aggregate).
fn real_committee() -> SyncCommittee {
    let pubkeys: Vec<[u8; 48]> = e2e::COMMITTEE_PUBKEYS.iter().map(|s| h48(s)).collect();
    assert_eq!(pubkeys.len(), SYNC_COMMITTEE_SIZE);
    SyncCommittee {
        pubkeys,
        aggregate_pubkey: h48(e2e::COMMITTEE_AGGREGATE_PUBKEY),
    }
}

/// An arbitrary "RPC-supplied" 512-key committee that is NOT the one the pinned
/// genesis commits: the real committee rotated by one position, so every key is a
/// well-formed 48-byte value but the committee's SSZ hash_tree_root differs from what
/// the rotation branch proves (the exact shape a hostile/forged committee takes).
fn forged_committee() -> SyncCommittee {
    let mut c = real_committee();
    c.pubkeys.rotate_left(1);
    c
}

fn attested_header() -> BeaconBlockHeader {
    BeaconBlockHeader {
        slot: e2e::ATTESTED_SLOT,
        proposer_index: e2e::ATTESTED_PROPOSER,
        parent_root: h32(e2e::ATTESTED_PARENT_ROOT),
        state_root: h32(e2e::ATTESTED_STATE_ROOT),
        body_root: h32(e2e::ATTESTED_BODY_ROOT),
    }
}

fn finalized_beacon() -> BeaconBlockHeader {
    BeaconBlockHeader {
        slot: e2e::FIN_SLOT,
        proposer_index: e2e::FIN_PROPOSER,
        parent_root: h32(e2e::FIN_PARENT_ROOT),
        state_root: h32(e2e::FIN_STATE_ROOT),
        body_root: h32(e2e::FIN_BODY_ROOT),
    }
}

fn execution_header() -> ExecutionPayloadHeader {
    ExecutionPayloadHeader {
        parent_hash: h32(e2e::EX_PARENT_HASH),
        fee_recipient: h20(e2e::EX_FEE_RECIPIENT),
        state_root: h32(e2e::EX_STATE_ROOT),
        receipts_root: h32(e2e::EX_RECEIPTS_ROOT),
        logs_bloom: h256(e2e::EX_LOGS_BLOOM),
        prev_randao: h32(e2e::EX_PREV_RANDAO),
        block_number: e2e::EX_BLOCK_NUMBER,
        gas_limit: e2e::EX_GAS_LIMIT,
        gas_used: e2e::EX_GAS_USED,
        timestamp: e2e::EX_TIMESTAMP,
        extra_data: hex::decode(e2e::EX_EXTRA_DATA).expect("extra_data hex"),
        base_fee_per_gas: h32(e2e::EX_BASE_FEE_LE32),
        block_hash: h32(e2e::EX_BLOCK_HASH),
        transactions_root: h32(e2e::EX_TRANSACTIONS_ROOT),
        withdrawals_root: h32(e2e::EX_WITHDRAWALS_ROOT),
        blob_gas_used: e2e::EX_BLOB_GAS_USED,
        excess_blob_gas: e2e::EX_EXCESS_BLOB_GAS,
    }
}

fn sync_aggregate() -> SyncAggregate {
    SyncAggregate {
        sync_committee_bits: h64(e2e::SYNC_COMMITTEE_BITS),
        sync_committee_signature: h96(e2e::SYNC_COMMITTEE_SIGNATURE),
    }
}

fn update() -> LightClientUpdate {
    LightClientUpdate {
        attested_header: attested_header(),
        finalized_header: LightClientHeader {
            beacon: finalized_beacon(),
            execution: execution_header(),
            execution_branch: branch(e2e::EXECUTION_BRANCH),
        },
        finality_branch: branch(e2e::FINALITY_BRANCH),
        sync_aggregate: sync_aggregate(),
    }
}

fn account_claim() -> AccountClaim {
    AccountClaim {
        nonce: e2e::ACCT_NONCE,
        balance: u256(e2e::ACCT_BALANCE_HEX),
        storage_hash: h32(e2e::ACCT_STORAGE_HASH),
        code_hash: h32(e2e::ACCT_CODE_HASH),
    }
}

/// Mint the WETH holding from a store-verified `FinalizedExecution` (the consumer-side
/// step that would produce `ConsensusProven`).
fn mint_holding(finalized: &FinalizedExecution) -> HoldingTrust {
    let holding = verify_erc20_holding_finalized(
        finalized,
        &nodes(e2e::ACCOUNT_PROOF),
        &nodes(e2e::STORAGE_PROOF),
        h20(e2e::TOKEN),
        h20(e2e::HOLDER),
        e2e::BALANCES_SLOT,
        &account_claim(),
        u256(e2e::EXPECTED_BALANCE_HEX),
    )
    .expect("holding must prove at the store-verified finalized root");
    holding.trust
}

// ==================== ACCEPT ====================

/// The genesis anchor is a governance-pinned checkpoint STATE ROOT (the period-1799
/// attested state root — a constant, not an RPC value). The current committee is
/// REACHED by a valid `verify_committee_update` from it, and only then does the store
/// verify the real update and mint `ConsensusProven`. The committee `verify` used came
/// from the store's rotation chain, never from the caller.
#[test]
fn genesis_checkpoint_bootstrap_then_verify_mints_consensus_proven() {
    let mut store = WeakSubjectivityStore::pin_checkpoint(
        h32(e2e::PREV_ATTESTED_STATE_ROOT), // governance WS checkpoint (period-1799 state)
        gvr(),
        1799,
    );

    // Fail-closed before any committee is chained in.
    assert!(!store.has_trusted_committee());
    assert_eq!(
        store.verify(&update(), e2e::FORK_VERSION).unwrap_err(),
        StoreError::NoTrustedCommittee,
        "an un-bootstrapped store must refuse to verify anything"
    );

    // Reach the current committee by a REAL rotation from the pinned genesis.
    store
        .bootstrap_committee(real_committee(), &branch(e2e::COMMITTEE_BRANCH))
        .expect("the real period-1800 committee chains from the pinned checkpoint");
    assert!(store.has_trusted_committee());
    assert_eq!(store.current_period(), 1800);

    // The store verifies the real update with ITS committee + ITS pinned gvr.
    let finalized = store
        .verify(&update(), e2e::FORK_VERSION)
        .expect("the store-committee must verify the real mainnet update");
    assert_eq!(finalized.execution_state_root(), h32(e2e::EX_STATE_ROOT));

    // -> a genuine ConsensusProven holding, anchored to the store-verified root.
    assert_eq!(mint_holding(&finalized), HoldingTrust::ConsensusProven);
}

// ==================== REJECT ====================

/// An arbitrary / RPC-supplied 512-key committee that is NOT chained from the pinned
/// genesis is refused at the rotation gate, is never installed, and `verify` then
/// fails closed — no `ConsensusProven`. This is the forged-committee drain, closed.
#[test]
fn rpc_supplied_forged_committee_not_chained_is_refused() {
    let mut store =
        WeakSubjectivityStore::pin_checkpoint(h32(e2e::PREV_ATTESTED_STATE_ROOT), gvr(), 1799);

    // The forged committee's rotation branch does not reconstruct the pinned state root.
    let err = store
        .bootstrap_committee(forged_committee(), &branch(e2e::COMMITTEE_BRANCH))
        .unwrap_err();
    assert!(
        matches!(err, StoreError::UnchainedCommittee(Error::BadMerkleBranch)),
        "a non-chained committee must be refused at the rotation gate, got {err:?}"
    );

    // It was never installed -> verify still fails closed. No path to a holding.
    assert!(!store.has_trusted_committee());
    assert_eq!(
        store.verify(&update(), e2e::FORK_VERSION).unwrap_err(),
        StoreError::NoTrustedCommittee
    );
}

/// A `genesis_validators_root` mismatch (pinned wrong) changes the signing domain, so
/// the real signature refuses — the pinned gvr is a real discriminator, and the SAME
/// committee + update verify only under the correct pinned root.
#[test]
fn genesis_validators_root_mismatch_refused() {
    let mut wrong = gvr();
    wrong[0] ^= 0x01;

    let store_wrong =
        WeakSubjectivityStore::pin_genesis_committee(real_committee(), wrong, 1800).unwrap();
    assert_eq!(
        store_wrong
            .verify(&update(), e2e::FORK_VERSION)
            .unwrap_err(),
        StoreError::Verify(Error::BadSignature),
        "a wrong pinned genesis_validators_root must refuse the real signature"
    );

    // Same committee + same update, correct pinned root -> accepts (gvr is the discriminator).
    let store_ok =
        WeakSubjectivityStore::pin_genesis_committee(real_committee(), gvr(), 1800).unwrap();
    let finalized = store_ok
        .verify(&update(), e2e::FORK_VERSION)
        .expect("the correct pinned gvr verifies the real update");
    assert_eq!(mint_holding(&finalized), HoldingTrust::ConsensusProven);
}

/// `advance` refuses a NEXT committee that does not chain from the current trusted
/// committee — even though the finalized update itself is genuinely signed by the
/// current committee. The store's committee is left UNCHANGED and still verifies.
#[test]
fn advance_refuses_next_committee_not_chained_from_current() {
    let mut store =
        WeakSubjectivityStore::pin_genesis_committee(real_committee(), gvr(), 1800).unwrap();

    // The real update is genuinely signed by the current committee (verify_finalized_update
    // passes inside advance), but the offered next committee + branch do not reconstruct
    // the state root that update attested -> the rotation gate refuses.
    let err = store
        .advance(
            &update(),
            forged_committee(),
            &branch(e2e::COMMITTEE_BRANCH),
            e2e::FORK_VERSION,
        )
        .unwrap_err();
    assert!(
        matches!(err, StoreError::UnchainedCommittee(_)),
        "a non-chained next committee must be refused even after a signed update, got {err:?}"
    );

    // The store did not rotate: it still holds and verifies with the real committee.
    assert_eq!(store.current_period(), 1800);
    assert_eq!(
        store.current_committee().map(|c| c.pubkeys.clone()),
        Some(real_committee().pubkeys)
    );
    assert!(store.verify(&update(), e2e::FORK_VERSION).is_ok());
}

/// Even a governance-pinned FORGED genesis committee cannot verify a real signature:
/// the BLS floor holds regardless of how the committee entered the store. A forged
/// committee never signed the real header, so `verify` refuses at the BLS gate.
#[test]
fn pinned_forged_genesis_committee_cannot_verify() {
    let store =
        WeakSubjectivityStore::pin_genesis_committee(forged_committee(), gvr(), 1800).unwrap();
    assert_eq!(
        store.verify(&update(), e2e::FORK_VERSION).unwrap_err(),
        StoreError::Verify(Error::BadSignature),
        "a forged pinned committee must not be able to mint ConsensusProven"
    );
}

/// A committee of the wrong size is rejected at the store boundary (fail-closed),
/// never reaching the verify-core.
#[test]
fn wrong_size_committee_refused_at_boundary() {
    let mut short = real_committee();
    short.pubkeys.truncate(511);
    assert_eq!(
        WeakSubjectivityStore::pin_genesis_committee(short, gvr(), 1800).unwrap_err(),
        StoreError::WrongCommitteeSize { got: 511 }
    );
}
