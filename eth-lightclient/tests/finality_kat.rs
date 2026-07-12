//! Finality-following — REAL external accept-KAT.
//!
//! ACCEPT: genuine Ethereum mainnet beacon `light_client/finality_update` data (fork
//! `fulu`, post-Electra), captured from a public beacon node. It validates, against
//! REAL chain data (not a round-trip):
//!   * the `BeaconBlockHeader` SSZ `hash_tree_root`,
//!   * `verify_finality_branch` at the post-Electra depth 7 / subtree index 41,
//!   * the 17-field `ExecutionPayloadHeader` SSZ `hash_tree_root`, and
//!   * `verify_execution_payload` at EXECUTION_PAYLOAD_GINDEX 25 / depth 4,
//! recovering the finalized EVM execution `state_root` — which MATCHES the WETH
//! proof-of-holdings fixture block, so the two real fixtures chain end-to-end
//! (finalized beacon header -> execution state root -> ERC-20 holding).
//!
//! REJECT (all default-run): a tampered finality branch node, a tampered finalized
//! header (incl. swapping the execution state_root — proving it is BOUND into the leaf),
//! a wrong attested state root, a wrong branch length, a tampered execution branch, and
//! a fail-closed composed `verify_finalized_update` when the sync aggregate is bad.

#[path = "fixtures/finality.rs"]
mod fin;
// Only STATE_ROOT is used here (the end-to-end chain assertion); the rest of the WETH
// fixture is exercised by evm_holding.rs.
#[allow(dead_code)]
#[path = "fixtures/weth.rs"]
mod weth;

use eth_lightclient::execution::{verify_execution_payload, ExecutionPayloadHeader};
use eth_lightclient::finality::{
    verify_finality_branch, verify_finalized_update, LightClientHeader, LightClientUpdate,
    FINALIZED_ROOT_DEPTH_ELECTRA,
};
use eth_lightclient::{BeaconBlockHeader, Error, SyncAggregate, SYNC_COMMITTEE_SIZE};

fn h32(s: &str) -> [u8; 32] {
    let v = hex::decode(s).expect("hex32");
    let mut a = [0u8; 32];
    a.copy_from_slice(&v);
    a
}
fn h20(s: &str) -> [u8; 20] {
    let v = hex::decode(s).expect("hex20");
    let mut a = [0u8; 20];
    a.copy_from_slice(&v);
    a
}
fn h256(s: &str) -> [u8; 256] {
    let v = hex::decode(s).expect("hex256");
    let mut a = [0u8; 256];
    a.copy_from_slice(&v);
    a
}
fn branch(list: &[&str]) -> Vec<[u8; 32]> {
    list.iter().map(|s| h32(s)).collect()
}

fn attested_header() -> BeaconBlockHeader {
    BeaconBlockHeader {
        slot: fin::ATTESTED_SLOT,
        proposer_index: fin::ATTESTED_PROPOSER,
        parent_root: h32(fin::ATTESTED_PARENT_ROOT),
        state_root: h32(fin::ATTESTED_STATE_ROOT),
        body_root: h32(fin::ATTESTED_BODY_ROOT),
    }
}
fn finalized_beacon() -> BeaconBlockHeader {
    BeaconBlockHeader {
        slot: fin::FIN_SLOT,
        proposer_index: fin::FIN_PROPOSER,
        parent_root: h32(fin::FIN_PARENT_ROOT),
        state_root: h32(fin::FIN_STATE_ROOT),
        body_root: h32(fin::FIN_BODY_ROOT),
    }
}
fn execution_header() -> ExecutionPayloadHeader {
    ExecutionPayloadHeader {
        parent_hash: h32(fin::EX_PARENT_HASH),
        fee_recipient: h20(fin::EX_FEE_RECIPIENT),
        state_root: h32(fin::EX_STATE_ROOT),
        receipts_root: h32(fin::EX_RECEIPTS_ROOT),
        logs_bloom: h256(fin::EX_LOGS_BLOOM),
        prev_randao: h32(fin::EX_PREV_RANDAO),
        block_number: fin::EX_BLOCK_NUMBER,
        gas_limit: fin::EX_GAS_LIMIT,
        gas_used: fin::EX_GAS_USED,
        timestamp: fin::EX_TIMESTAMP,
        extra_data: hex::decode(fin::EX_EXTRA_DATA).expect("extra_data hex"),
        base_fee_per_gas: h32(fin::EX_BASE_FEE_LE32),
        block_hash: h32(fin::EX_BLOCK_HASH),
        transactions_root: h32(fin::EX_TRANSACTIONS_ROOT),
        withdrawals_root: h32(fin::EX_WITHDRAWALS_ROOT),
        blob_gas_used: fin::EX_BLOB_GAS_USED,
        excess_blob_gas: fin::EX_EXCESS_BLOB_GAS,
    }
}

// -------------------- ACCEPT (real chain data) --------------------

#[test]
fn real_finality_branch_accepts_post_electra() {
    // Depth 7 (post-Electra). Validates the BeaconBlockHeader HTR + gindex 169/index 41.
    let fb = branch(fin::FINALITY_BRANCH);
    assert_eq!(fb.len(), FINALIZED_ROOT_DEPTH_ELECTRA);
    verify_finality_branch(&finalized_beacon(), &fb, &h32(fin::ATTESTED_STATE_ROOT))
        .expect("real post-Electra finality branch must verify");
}

#[test]
fn real_execution_payload_accepts_and_recovers_state_root() {
    // Validates the 17-field ExecutionPayloadHeader HTR against the real execution
    // branch + body_root, recovering the finalized EVM state root.
    let eb = branch(fin::EXECUTION_BRANCH);
    let sr = verify_execution_payload(&execution_header(), &eb, &h32(fin::FIN_BODY_ROOT))
        .expect("real execution branch must verify");
    assert_eq!(sr, h32(fin::EX_STATE_ROOT));
}

#[test]
fn finality_chains_end_to_end_into_the_weth_holding_fixture() {
    // The finalized beacon header's recovered execution state root is EXACTLY the state
    // root the WETH proof-of-holdings fixture proves against — the two independent real
    // fixtures form one chain: finalized beacon header -> execution state root -> ERC-20.
    let eb = branch(fin::EXECUTION_BRANCH);
    let sr = verify_execution_payload(&execution_header(), &eb, &h32(fin::FIN_BODY_ROOT)).unwrap();
    assert_eq!(sr, h32(weth::STATE_ROOT));
}

// -------------------- REJECT (fail-closed) --------------------

#[test]
fn tampered_finality_branch_node_rejects() {
    let mut fb = branch(fin::FINALITY_BRANCH);
    fb[3][7] ^= 0x01;
    assert_eq!(
        verify_finality_branch(&finalized_beacon(), &fb, &h32(fin::ATTESTED_STATE_ROOT)),
        Err(Error::BadFinalityBranch)
    );
}

#[test]
fn tampered_finalized_header_rejects() {
    // Change the finalized beacon state_root -> different leaf -> branch fails.
    let mut fh = finalized_beacon();
    fh.state_root[0] ^= 0x01;
    let fb = branch(fin::FINALITY_BRANCH);
    assert_eq!(
        verify_finality_branch(&fh, &fb, &h32(fin::ATTESTED_STATE_ROOT)),
        Err(Error::BadFinalityBranch)
    );
}

#[test]
fn wrong_attested_state_root_rejects() {
    let mut asr = h32(fin::ATTESTED_STATE_ROOT);
    asr[0] ^= 0x01;
    let fb = branch(fin::FINALITY_BRANCH);
    assert_eq!(
        verify_finality_branch(&finalized_beacon(), &fb, &asr),
        Err(Error::BadFinalityBranch)
    );
}

#[test]
fn wrong_finality_branch_length_rejects() {
    let fb = branch(fin::FINALITY_BRANCH);
    let short = &fb[..fb.len() - 2]; // length 5 — neither 6 nor 7
    assert!(matches!(
        verify_finality_branch(&finalized_beacon(), short, &h32(fin::ATTESTED_STATE_ROOT)),
        Err(Error::WrongBranchLength { .. })
    ));
}

#[test]
fn swapped_execution_state_root_rejects() {
    // The soundness property: you cannot substitute the EVM state root without breaking
    // the execution branch — it is bound into the ExecutionPayloadHeader HTR leaf.
    let mut ex = execution_header();
    ex.state_root[0] ^= 0x01;
    let eb = branch(fin::EXECUTION_BRANCH);
    assert_eq!(
        verify_execution_payload(&ex, &eb, &h32(fin::FIN_BODY_ROOT)),
        Err(Error::BadExecutionBranch)
    );
}

#[test]
fn tampered_execution_branch_node_rejects() {
    let mut eb = branch(fin::EXECUTION_BRANCH);
    eb[1][3] ^= 0x01;
    assert_eq!(
        verify_execution_payload(&execution_header(), &eb, &h32(fin::FIN_BODY_ROOT)),
        Err(Error::BadExecutionBranch)
    );
}

#[test]
fn wrong_execution_branch_length_rejects() {
    let eb = branch(fin::EXECUTION_BRANCH);
    let short = &eb[..eb.len() - 1];
    assert!(matches!(
        verify_execution_payload(&execution_header(), short, &h32(fin::FIN_BODY_ROOT)),
        Err(Error::WrongBranchLength { .. })
    ));
}

#[test]
fn wrong_execution_body_root_rejects() {
    let mut body = h32(fin::FIN_BODY_ROOT);
    body[0] ^= 0x01;
    let eb = branch(fin::EXECUTION_BRANCH);
    assert_eq!(
        verify_execution_payload(&execution_header(), &eb, &body),
        Err(Error::BadExecutionBranch)
    );
}

#[test]
fn composed_update_fails_closed_on_bad_sync_aggregate() {
    // verify_finalized_update runs the sync-aggregate BLS FIRST. With a bogus committee
    // + full participation but a garbage signature, it must fail closed BEFORE ever
    // trusting the (real) finality/execution branches — no partial advance.
    let update = LightClientUpdate {
        attested_header: attested_header(),
        finalized_header: LightClientHeader {
            beacon: finalized_beacon(),
            execution: execution_header(),
            execution_branch: branch(fin::EXECUTION_BRANCH),
        },
        finality_branch: branch(fin::FINALITY_BRANCH),
        sync_aggregate: SyncAggregate {
            sync_committee_bits: [0xFFu8; SYNC_COMMITTEE_SIZE / 8],
            sync_committee_signature: [0u8; 96], // not a valid G2 point
        },
    };
    let committee = vec![[0x01u8; 48]; SYNC_COMMITTEE_SIZE]; // not on-curve
    let fork_version = [0x06, 0x00, 0x00, 0x00];
    let gvr = h32("4b363db94e286120d76eb905340fdd4e54bfe9f06bf33ff6cf5ad27f511bfe95");
    let r = verify_finalized_update(&update, &committee, fork_version, gvr);
    assert!(
        r.is_err(),
        "bad sync aggregate must fail the composed update, got {r:?}"
    );
}

#[test]
fn composed_update_fails_closed_on_subquorum() {
    // Sub-2/3 participation must fail closed even before signature work.
    let mut bits = [0u8; SYNC_COMMITTEE_SIZE / 8];
    // Set only 300 bits (< 342 threshold).
    for i in 0..300 {
        bits[i / 8] |= 1 << (i % 8);
    }
    let update = LightClientUpdate {
        attested_header: attested_header(),
        finalized_header: LightClientHeader {
            beacon: finalized_beacon(),
            execution: execution_header(),
            execution_branch: branch(fin::EXECUTION_BRANCH),
        },
        finality_branch: branch(fin::FINALITY_BRANCH),
        sync_aggregate: SyncAggregate {
            sync_committee_bits: bits,
            sync_committee_signature: [0xC0u8; 96],
        },
    };
    let committee = vec![[0x01u8; 48]; SYNC_COMMITTEE_SIZE];
    let gvr = [0x42u8; 32];
    assert!(matches!(
        verify_finalized_update(&update, &committee, [0x06, 0, 0, 0], gvr),
        Err(Error::InsufficientParticipation { .. })
    ));
}
