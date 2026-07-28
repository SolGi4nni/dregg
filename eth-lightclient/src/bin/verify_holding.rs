//! `verify_holding` — a RUNNING Ethereum light-client binary built from the
//! verified rules in this crate. It follows the beacon-header trust chain and
//! settles an ERC-20 holding, entirely from the verified verification core:
//!
//!   1. verify_sync_aggregate        REAL BLS: the mainnet period-1800 sync
//!      |                            committee's 512 pubkeys verify the REAL
//!      |                            aggregate G2 signature over the REAL
//!      |                            attested header (397/512 participation).
//!   2. verify_committee_update      the committee itself is Merkle-proven under
//!      |                            the previous period's attested state root —
//!      |                            the rotation step a live LC uses to learn it.
//!   3. verify_finalized_update      REAL finality branch (depth 7, post-Electra)
//!      |                            + REAL execution branch (depth 4)
//!      |                            -> FinalizedExecution (the finalized EVM root).
//!   4. verify_erc20_holding_finalized  REAL EIP-1186 eth_getProof at that finalized
//!                                   execution root -> HoldingTrust::ConsensusProven.
//!
//! Every artifact is EXTERNAL mainnet data captured live from public nodes
//! (provenance: `tests/fixtures/e2e_mainnet.rs`) — the committee pubkeys, the
//! aggregate signature, both Merkle branches, and the MPT proofs were produced
//! by Ethereum itself, not by this crate. The bin is fully OFFLINE (the fixture
//! is a real captured mainnet checkpoint compiled in); pass `--rpc <URL>` is NOT
//! needed — a live LC would swap the compiled checkpoint for a `beacon_getState`
//! + `eth_getProof` fetch behind the SAME verified rules.
//!
//! Run:  cargo run -p eth-lightclient --bin verify_holding
//! Exit: 0 iff the whole chain verifies AND the tamper canary is refused.

// The real captured mainnet checkpoint (same fixture the end_to_end.rs test drives).
#[path = "../../tests/fixtures/e2e_mainnet.rs"]
#[allow(dead_code)]
mod e2e;

use eth_lightclient::evm::{
    verify_erc20_holding_finalized, AccountClaim, HoldingTrust, ProvenErc20Holding, Uint256,
};
use eth_lightclient::execution::ExecutionPayloadHeader;
use eth_lightclient::finality::{
    verify_finalized_update, FinalizedExecution, LightClientHeader, LightClientUpdate,
};
use eth_lightclient::store::WeakSubjectivityStore;
use eth_lightclient::{
    verify_sync_aggregate, BeaconBlockHeader, SyncAggregate, SyncCommittee, SYNC_COMMITTEE_SIZE,
};

// -------------------- hex helpers (same as the tests) --------------------

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

fn committee_pubkeys() -> Vec<[u8; 48]> {
    let pks: Vec<[u8; 48]> = e2e::COMMITTEE_PUBKEYS.iter().map(|s| h48(s)).collect();
    assert_eq!(pks.len(), SYNC_COMMITTEE_SIZE);
    pks
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

/// Participation count from the 512-bit sync-committee bitfield.
fn participation(bits: &[u8; 64]) -> u32 {
    bits.iter().map(|b| b.count_ones()).sum()
}

/// Render a WETH (18-decimal) balance as a human string, best-effort.
fn weth(bal: &Uint256) -> String {
    // 1e18 as Uint256.
    let scale = Uint256::from(1_000_000_000_000_000_000u128);
    let whole = *bal / scale;
    let frac = (*bal % scale).to_string();
    let frac = format!("{:0>18}", frac); // left-pad to 18 decimals
    format!("{whole}.{frac} WETH")
}

fn main() {
    println!("eth-lightclient · verify_holding");
    println!("  a running Ethereum light client built from the verified rules");
    println!("  fixture: REAL mainnet checkpoint (tests/fixtures/e2e_mainnet.rs), offline\n");

    let committee = committee_pubkeys();
    let upd = update();

    // ---- step 1: REAL BLS over the REAL attested header --------------------
    let part = participation(&h64(e2e::SYNC_COMMITTEE_BITS));
    print!(
        "1. verify_sync_aggregate  (slot {}, {}/{} participation) ... ",
        e2e::ATTESTED_SLOT,
        part,
        SYNC_COMMITTEE_SIZE
    );
    verify_sync_aggregate(
        &attested_header(),
        &sync_aggregate(),
        &committee,
        e2e::FORK_VERSION,
        gvr(),
    )
    .expect("real mainnet sync-committee BLS aggregate must verify");
    println!("OK (real BLS12-381 aggregate accepted)");

    // ---- step 2: the committee is reached from a PINNED anchor, not accepted --
    //
    // This is the step that decides whether any of the rest means anything. The pin is the
    // period-1799 beacon state root as a GOVERNANCE CONSTANT (in a deployment: config /
    // a checkpoint-sync provider the operator chose), and `bootstrap_committee` proves the
    // 512-key committee is the `next_sync_committee` that state commits. A committee an RPC
    // merely ASSERTED cannot get in here — its rotation branch does not reconstruct the pin.
    print!("2. WeakSubjectivityStore::bootstrap_committee (pinned anchor -> committee) ... ");
    // 1799 = the sync-committee period of `PREV_ATTESTED_STATE_ROOT`; it commits the period-1800
    // committee this fixture carries (the same pin `tests/weak_subjectivity_store.rs` uses).
    let mut store =
        WeakSubjectivityStore::pin_checkpoint(h32(e2e::PREV_ATTESTED_STATE_ROOT), gvr(), 1799);
    store
        .bootstrap_committee(
            SyncCommittee {
                pubkeys: committee.clone(),
                aggregate_pubkey: h48(e2e::COMMITTEE_AGGREGATE_PUBKEY),
            },
            &branch(e2e::COMMITTEE_BRANCH),
        )
        .expect("committee rotation Merkle proof must verify against the pinned checkpoint");
    println!("OK (SSZ next_sync_committee branch accepted under the pin)");

    // ---- step 3: finality + execution branch -> finalized EVM state root ----
    //
    // The committee handed to the gate is the STORE's — `TrustedCommittee` cannot be built
    // from a bare `&[[u8; 48]]` without saying `new_unchecked` out loud.
    print!("3. verify_finalized_update (finality depth 7 + execution depth 4) ... ");
    let trusted = store
        .trusted_committee()
        .expect("the store bootstrapped a committee above");
    let finalized: FinalizedExecution = verify_finalized_update(&upd, &trusted, e2e::FORK_VERSION)
        .expect("finalized update must verify");
    println!("OK");
    println!(
        "     finalized execution: block {}  state_root 0x{}",
        e2e::EX_BLOCK_NUMBER,
        hex::encode(&h32(e2e::EX_STATE_ROOT)[..8])
    );

    // ---- step 4: EIP-1186 proof at the finalized root -> the holding --------
    print!(
        "4. verify_erc20_holding_finalized (WETH holder 0x{}) ... ",
        hex::encode(h20(e2e::HOLDER))
    );
    let holding: ProvenErc20Holding = verify_erc20_holding_finalized(
        &finalized,
        &nodes(e2e::ACCOUNT_PROOF),
        &nodes(e2e::STORAGE_PROOF),
        h20(e2e::TOKEN),
        h20(e2e::HOLDER),
        e2e::BALANCES_SLOT,
        &account_claim(),
        u256(e2e::EXPECTED_BALANCE_HEX),
    )
    .expect("holding must verify at the finalized root");
    println!("OK");

    assert_eq!(
        holding.trust,
        HoldingTrust::ConsensusProven,
        "holding must be ConsensusProven (anchored to the finalized root)"
    );
    let bal = u256(e2e::EXPECTED_BALANCE_HEX);
    println!(
        "\n   SETTLED HOLDING (trust = ConsensusProven):\n     {} at Ethereum block {}",
        weth(&bal),
        e2e::EX_BLOCK_NUMBER
    );

    // ---- reject canary: a wrong claimed balance must fail closed at the MPT --
    print!("\n5. reject canary: forged balance (+1 wei) must be REFUSED ... ");
    let mut forged = bal;
    forged = forged + Uint256::from(1u128);
    let refused = verify_erc20_holding_finalized(
        &finalized,
        &nodes(e2e::ACCOUNT_PROOF),
        &nodes(e2e::STORAGE_PROOF),
        h20(e2e::TOKEN),
        h20(e2e::HOLDER),
        e2e::BALANCES_SLOT,
        &account_claim(),
        forged,
    );
    if refused.is_ok() {
        eprintln!("SECURITY FAILURE: a forged balance was accepted");
        std::process::exit(2);
    }
    println!("REFUSED (fail-closed at the storage-trie gate)");

    println!("\nALL GATES PASSED — a real WETH holding settled from a real mainnet");
    println!("sync-committee signature, verified end-to-end by the light-client rules.");
}
