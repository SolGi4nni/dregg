//! REAL end-to-end mainnet validation — one composed chain, genuine chain data at
//! EVERY link:
//!
//!   verify_sync_aggregate            REAL BLS: the period-1800 mainnet sync committee's
//!     |                              512 pubkeys (from the period-1799 update's
//!     |                              next_sync_committee) verify the REAL aggregate G2
//!     |                              signature over the REAL attested header (397/512).
//!   verify_finalized_update          + REAL finality branch (depth 7, post-Electra)
//!     |                              + REAL execution branch (depth 4)
//!     |                              -> FinalizedExecution (the finalized EVM state root)
//!   verify_erc20_holding_finalized   REAL EIP-1186 eth_getProof for a WETH holder at the
//!                                    finalized execution block -> HoldingTrust::ConsensusProven
//!
//! Every artifact is EXTERNAL mainnet data captured live from public nodes (fixture
//! provenance in `fixtures/e2e_mainnet.rs`): the committee pubkeys, the aggregate
//! signature, both branches, and the MPT proofs were all produced by Ethereum itself,
//! not by this crate — so the accept is external conformance, not a round-trip. This is
//! the composed-chain validation the per-link KATs (`kat_bls.rs`, `finality_kat.rs`,
//! `evm_holding.rs`) do not give: here the SAME sync-committee signature flows through
//! to the SAME minted holding.
//!
//! Also proven on real data: the committee itself is Merkle-proven
//! (`verify_committee_update`) under the previous period's update — the rotation step a
//! live light client would have used to learn this committee.
//!
//! REJECT (fail-closed, all default-run): sub-2/3 participation, a tampered aggregate
//! signature, a rotated (wrong) committee, a tampered attested header, and a wrong fork
//! version all refuse at the BLS gate BEFORE any holding can be minted; after a genuine
//! BLS accept, a tampered finality branch / execution payload still refuses; and a wrong
//! claimed balance refuses at the MPT gate even under the genuinely-verified state root.

#[path = "fixtures/e2e_mainnet.rs"]
#[allow(dead_code)]
mod e2e;

use eth_lightclient::evm::{
    verify_erc20_holding_finalized, AccountClaim, Erc20ProofError, HoldingTrust, Uint256,
};
use eth_lightclient::execution::ExecutionPayloadHeader;
use eth_lightclient::finality::{
    verify_finalized_update, FinalizedExecution, LightClientHeader, LightClientUpdate,
};
use eth_lightclient::{
    verify_committee_update, verify_sync_aggregate, BeaconBlockHeader, Error, SyncAggregate,
    SyncCommittee, TrustedCommittee, SYNC_COMMITTEE_SIZE,
};

// -------------------- hex helpers --------------------

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

/// The REAL period-1800 mainnet sync committee (512 compressed G1 pubkeys).
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

/// The REAL mainnet sync aggregate: 397/512 participation + the aggregate G2 signature.
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

/// Run the FULL verified chain and mint the holding (the accept path, factored so the
/// accept test and the tamper tests share it).
fn run_chain(
    update: &LightClientUpdate,
    committee: &[[u8; 48]],
) -> Result<eth_lightclient::evm::ProvenErc20Holding, String> {
    let finalized: FinalizedExecution = verify_finalized_update(
        update,
        &TrustedCommittee::new_unchecked(committee, gvr()),
        e2e::FORK_VERSION,
    )
    .map_err(|e| format!("light-client gate refused: {e:?}"))?;
    verify_erc20_holding_finalized(
        &finalized,
        &nodes(e2e::ACCOUNT_PROOF),
        &nodes(e2e::STORAGE_PROOF),
        h20(e2e::TOKEN),
        h20(e2e::HOLDER),
        e2e::BALANCES_SLOT,
        &account_claim(),
        u256(e2e::EXPECTED_BALANCE_HEX),
    )
    .map_err(|e| format!("holding gate refused: {e:?}"))
}

// -------------------- ACCEPT: the real composed chain --------------------

/// THE end-to-end accept: a genuine mainnet sync-committee BLS signature (real 512-key
/// committee, 397/512 participation) verifies the attested header; the real finality +
/// execution branches advance to the finalized EVM state root; the real EIP-1186 proof
/// chain mints a ConsensusProven WETH holding at that root. One unbroken chain of
/// external mainnet data.
#[test]
fn real_mainnet_chain_bls_to_finality_to_consensus_proven_holding() {
    let committee = committee_pubkeys();

    // Link 1 in isolation first (pinpoints a BLS failure distinctly from the branches):
    // the REAL committee verifies the REAL aggregate over the REAL attested header.
    verify_sync_aggregate(
        &attested_header(),
        &sync_aggregate(),
        &committee,
        e2e::FORK_VERSION,
        gvr(),
    )
    .expect("real mainnet sync-committee BLS aggregate must verify");

    // The composed chain: BLS -> finality branch -> execution branch -> FinalizedExecution.
    let finalized = verify_finalized_update(
        &update(),
        &TrustedCommittee::new_unchecked(&committee, gvr()),
        e2e::FORK_VERSION,
    )
    .expect("real mainnet finalized update must verify end-to-end");
    assert_eq!(finalized.finalized_slot(), e2e::FIN_SLOT);
    assert_eq!(
        finalized.finalized_beacon_root(),
        finalized_beacon().hash_tree_root()
    );
    assert_eq!(finalized.execution_block_number(), e2e::EX_BLOCK_NUMBER);
    assert_eq!(finalized.execution_state_root(), h32(e2e::EX_STATE_ROOT));
    assert_eq!(finalized.execution_timestamp(), e2e::EX_TIMESTAMP);

    // -> the real eth_getProof chain against the CONSENSUS-VERIFIED state root.
    let holding = verify_erc20_holding_finalized(
        &finalized,
        &nodes(e2e::ACCOUNT_PROOF),
        &nodes(e2e::STORAGE_PROOF),
        h20(e2e::TOKEN),
        h20(e2e::HOLDER),
        e2e::BALANCES_SLOT,
        &account_claim(),
        u256(e2e::EXPECTED_BALANCE_HEX),
    )
    .expect("real WETH holding must prove against the consensus-verified state root");

    assert_eq!(holding.trust, HoldingTrust::ConsensusProven);
    assert!(holding.is_consensus_proven());
    assert_eq!(holding.balance, u256(e2e::EXPECTED_BALANCE_HEX));
    assert_eq!(holding.token, h20(e2e::TOKEN));
    assert_eq!(holding.holder, h20(e2e::HOLDER));
    assert_eq!(holding.block_number, e2e::EX_BLOCK_NUMBER);
    assert_eq!(holding.state_root, h32(e2e::EX_STATE_ROOT));

    // And it converts to consensus_proven governance fields.
    let fields = holding.to_foreign_fields().expect("WETH balance fits u128");
    assert!(fields.consensus_proven);
    assert_eq!(fields.snapshot, e2e::EX_BLOCK_NUMBER);
}

/// The committee itself is Merkle-proven on real data: the period-1799 update's
/// `next_sync_committee_branch` proves this exact 512-key committee (its SSZ HTR)
/// under that update's attested state root — the rotation step a live light client
/// would have used to LEARN the committee the accept test verifies with.
#[test]
fn real_committee_is_merkle_proven_under_previous_period_update() {
    let committee = SyncCommittee {
        pubkeys: committee_pubkeys(),
        aggregate_pubkey: h48(e2e::COMMITTEE_AGGREGATE_PUBKEY),
    };
    let cb = branch(e2e::COMMITTEE_BRANCH);
    verify_committee_update(&committee, &cb, &h32(e2e::PREV_ATTESTED_STATE_ROOT))
        .expect("real next_sync_committee branch must prove the real committee");
}

// -------------------- REJECT: the chain fails closed at the BLS gate --------------------

/// Sub-2/3 participation: mask the REAL bitfield down to 341 participants (threshold is
/// 342). The whole chain refuses at the BLS gate — no FinalizedExecution, so no path to
/// a holding: an under-signed update can never mint.
#[test]
fn subquorum_participation_fails_closed_before_any_holding() {
    let mut upd = update();
    let mut remaining = 341usize;
    for i in 0..SYNC_COMMITTEE_SIZE {
        if upd.sync_aggregate.participated(i) {
            if remaining > 0 {
                remaining -= 1;
            } else {
                upd.sync_aggregate.sync_committee_bits[i / 8] &= !(1 << (i % 8));
            }
        }
    }
    assert_eq!(upd.sync_aggregate.count(), 341);
    let err = run_chain(&upd, &committee_pubkeys()).unwrap_err();
    assert!(
        err.contains("InsufficientParticipation"),
        "expected the 2/3 floor to refuse, got: {err}"
    );
}

/// A tampered aggregate signature (one bit flipped in the REAL G2 aggregate): the BLS
/// gate refuses and the chain never reaches the branches or the MPT.
#[test]
fn tampered_aggregate_signature_fails_closed() {
    let mut upd = update();
    upd.sync_aggregate.sync_committee_signature[50] ^= 0x01;
    let err = run_chain(&upd, &committee_pubkeys()).unwrap_err();
    assert!(
        err.contains("BadSignature"),
        "expected BLS refusal, got: {err}"
    );
}

/// The WRONG committee (the real 512 keys rotated by one): every key is a valid G1
/// point, participation is ≥ 2/3, but the aggregate no longer matches — the signature
/// is bound to the exact participating key set.
#[test]
fn rotated_committee_fails_closed() {
    let mut committee = committee_pubkeys();
    committee.rotate_left(1);
    let err = run_chain(&update(), &committee).unwrap_err();
    assert!(
        err.contains("BadSignature"),
        "expected BLS refusal, got: {err}"
    );
}

/// A tampered ATTESTED header (slot + 1): the real signature is over the real header;
/// any header change changes the signing root and the BLS gate refuses — the update's
/// authority is bound to exactly the header the committee signed.
#[test]
fn tampered_attested_header_fails_closed() {
    let mut upd = update();
    upd.attested_header.slot += 1;
    let err = run_chain(&upd, &committee_pubkeys()).unwrap_err();
    assert!(
        err.contains("BadSignature"),
        "expected BLS refusal, got: {err}"
    );
}

/// A wrong fork version (Electra's 0x05000000 instead of Fulu's 0x06000000) changes the
/// signing domain, so the same real signature refuses — cross-fork domain separation.
#[test]
fn wrong_fork_version_fails_closed() {
    let r = verify_sync_aggregate(
        &attested_header(),
        &sync_aggregate(),
        &committee_pubkeys(),
        [0x05, 0x00, 0x00, 0x00],
        gvr(),
    );
    assert_eq!(r, Err(Error::BadSignature));
}

// ---- REJECT: after a GENUINE BLS accept, the later links still fail closed ----

/// Tampered finality branch under a genuinely-verified signature: the real BLS accept
/// runs first and PASSES, then the finality gate refuses — a correctly-signed update
/// still cannot smuggle in an unproven finalized header.
#[test]
fn genuine_bls_accept_then_tampered_finality_branch_fails() {
    let mut upd = update();
    upd.finality_branch[3][7] ^= 0x01;
    let r = verify_finalized_update(
        &upd,
        &TrustedCommittee::new_unchecked(&committee_pubkeys(), gvr()),
        e2e::FORK_VERSION,
    );
    assert_eq!(r.unwrap_err(), Error::BadFinalityBranch);
}

/// Tampered execution payload (state_root bit-flip) under a genuinely-verified
/// signature + finality branch: the execution gate refuses — the EVM state root cannot
/// be substituted even inside an otherwise-valid update.
#[test]
fn genuine_bls_accept_then_tampered_execution_state_root_fails() {
    let mut upd = update();
    upd.finalized_header.execution.state_root[0] ^= 0x01;
    let r = verify_finalized_update(
        &upd,
        &TrustedCommittee::new_unchecked(&committee_pubkeys(), gvr()),
        e2e::FORK_VERSION,
    );
    assert_eq!(r.unwrap_err(), Error::BadExecutionBranch);
}

/// A wrong claimed balance against the GENUINELY consensus-verified state root: the
/// light-client chain accepts, then the MPT gate refuses — consensus authority does not
/// let a prover overstate a holding.
#[test]
fn genuine_consensus_root_then_wrong_balance_fails_at_mpt_gate() {
    let finalized = verify_finalized_update(
        &update(),
        &TrustedCommittee::new_unchecked(&committee_pubkeys(), gvr()),
        e2e::FORK_VERSION,
    )
    .expect("the real update verifies");
    let inflated = u256(e2e::EXPECTED_BALANCE_HEX) + Uint256::from(1u64);
    let r = verify_erc20_holding_finalized(
        &finalized,
        &nodes(e2e::ACCOUNT_PROOF),
        &nodes(e2e::STORAGE_PROOF),
        h20(e2e::TOKEN),
        h20(e2e::HOLDER),
        e2e::BALANCES_SLOT,
        &account_claim(),
        inflated,
    );
    assert_eq!(r.unwrap_err(), Erc20ProofError::StorageProofInvalid);
}
