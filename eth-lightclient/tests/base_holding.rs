//! Base (OP-stack L2) proof-of-holdings — the L1-light-client × MPT composition.
//!
//! ACCEPT: a REAL external fixture — Base mainnet output 12086 (the last
//! legacy-oracle output) opened out of REAL finalized Ethereum L1 mainnet state,
//! bound to Base block 21756600's REAL output-root preimage, with a REAL WETH
//! holding proof on Base at that block (see tests/fixtures/base_mainnet.rs for
//! provenance). This is SPEC conformance against both chains, not a round-trip.
//!
//! The output-root preimage field order is additionally pinned against an
//! EXTERNAL KAT from kona-protocol 0.4.5 (`src/output_root.rs`,
//! `test_hash_output_root`) — an independent OP-stack implementation.
//!
//! REJECT (all default-run): a forged L2 state root (output-root recompute
//! fails), swapped preimage fields (field-order adversary), a wrong version byte,
//! a tampered L1 output-root storage proof, a tampered L1 oracle account proof, a
//! wrong output index, a tampered metadata slot (forged L2 block number), a zero
//! output root, an L2 proof against the wrong L2 state root, and a tampered L2
//! holding proof. Every one must fail closed — never mint a holding.

#[path = "fixtures/base_mainnet.rs"]
mod fx;

use eth_lightclient::base::{
    compute_op_output_root_v0, l2_output_meta_slot, l2_output_root_slot, pack_output_meta,
    verify_base_erc20_holding, verify_l1_committed_output_root, verify_op_output_root,
    BaseProofError, L2StateCommitment, OpOutputAnchor, L2_OUTPUT_ORACLE_L2_OUTPUTS_SLOT,
    OUTPUT_ROOT_VERSION_V0,
};
use eth_lightclient::evm::{AccountClaim, Erc20ProofError, HoldingTrust, Uint256, CHAIN_TAG_EVM};
use eth_lightclient::finality::FinalizedExecution;

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
fn nodes(list: &[&str]) -> Vec<Vec<u8>> {
    list.iter()
        .map(|s| hex::decode(s).expect("hex node"))
        .collect()
}
fn u256(s: &str) -> Uint256 {
    Uint256::from_str_radix(s, 16).expect("u256 hex")
}

/// The real finalized-L1 carrier. `new_unchecked` here stands in for the
/// sync-committee finality path (which has its own KATs in finality_kat.rs); the
/// state root/number/hash are the REAL L1 mainnet block 25514490's.
fn l1_finalized() -> FinalizedExecution {
    FinalizedExecution::new_unchecked(
        0,         // beacon slot: not exercised by this composition
        [0u8; 32], // beacon root: not exercised by this composition
        fx::L1_BLOCK_NUMBER,
        h32(fx::L1_BLOCK_HASH),
        h32(fx::L1_STATE_ROOT),
        0, // execution timestamp: not exercised by the legacy-oracle composition
    )
}

fn anchor() -> OpOutputAnchor {
    OpOutputAnchor {
        oracle_address: h20(fx::ORACLE_ADDRESS),
        oracle_account: AccountClaim {
            nonce: fx::ORACLE_NONCE,
            balance: u256(fx::ORACLE_BALANCE_HEX),
            storage_hash: h32(fx::ORACLE_STORAGE_HASH),
            code_hash: h32(fx::ORACLE_CODE_HASH),
        },
        oracle_account_proof: nodes(fx::ORACLE_ACCOUNT_PROOF),
        l2_outputs_slot: fx::L2_OUTPUTS_SLOT,
        l2_outputs_length: fx::L2_OUTPUTS_LENGTH,
        outputs_length_slot_proof: nodes(fx::OUTPUTS_LENGTH_SLOT_PROOF),
        output_index: fx::OUTPUT_INDEX,
        output_root: h32(fx::OUTPUT_ROOT),
        timestamp: fx::OUTPUT_TIMESTAMP,
        l2_block_number: fx::OUTPUT_L2_BLOCK_NUMBER,
        output_root_slot_proof: nodes(fx::OUTPUT_ROOT_SLOT_PROOF),
        output_meta_slot_proof: nodes(fx::OUTPUT_META_SLOT_PROOF),
    }
}

fn l2_commitment() -> L2StateCommitment {
    L2StateCommitment {
        version: OUTPUT_ROOT_VERSION_V0,
        l2_state_root: h32(fx::L2_STATE_ROOT),
        l2_withdrawal_storage_root: h32(fx::L2_WITHDRAWAL_STORAGE_ROOT),
        l2_block_hash: h32(fx::L2_BLOCK_HASH),
    }
}

fn token_account() -> AccountClaim {
    AccountClaim {
        nonce: fx::TOKEN_NONCE,
        balance: u256(fx::TOKEN_BALANCE_HEX),
        storage_hash: h32(fx::TOKEN_STORAGE_HASH),
        code_hash: h32(fx::TOKEN_CODE_HASH),
    }
}

/// The whole composition, parameterized so reject tests perturb one input each.
fn run(
    l1: &FinalizedExecution,
    anchor: &OpOutputAnchor,
    commitment: &L2StateCommitment,
    l2_account_proof: &[Vec<u8>],
    l2_storage_proof: &[Vec<u8>],
    token_account: &AccountClaim,
    balance: Uint256,
) -> Result<eth_lightclient::evm::ProvenErc20Holding, BaseProofError> {
    verify_base_erc20_holding(
        l1,
        anchor,
        commitment,
        l2_account_proof,
        l2_storage_proof,
        h20(fx::TOKEN),
        h20(fx::HOLDER),
        fx::BALANCES_SLOT,
        token_account,
        balance,
    )
}

fn run_default() -> Result<eth_lightclient::evm::ProvenErc20Holding, BaseProofError> {
    run(
        &l1_finalized(),
        &anchor(),
        &l2_commitment(),
        &nodes(fx::L2_ACCOUNT_PROOF),
        &nodes(fx::L2_STORAGE_PROOF),
        &token_account(),
        u256(fx::EXPECTED_BALANCE_HEX),
    )
}

// ---------------------------------------------------------------------------
// The output-root core: external KATs
// ---------------------------------------------------------------------------

/// EXTERNAL KAT from kona-protocol 0.4.5 (src/output_root.rs, test_hash_output_root):
/// OutputRoot::from_parts(pad32(0xbeef), pad32(0xbabe), pad32(0xc0de)).hash()
/// = 0x0c39fb…0d11. An independent OP-stack implementation pins our preimage
/// layout: version(32 zeros) ‖ state_root ‖ withdrawal_storage_root ‖ block_hash.
#[test]
fn output_root_matches_kona_protocol_kat() {
    let mut sr = [0u8; 32];
    sr[30..].copy_from_slice(&[0xbe, 0xef]);
    let mut wr = [0u8; 32];
    wr[30..].copy_from_slice(&[0xba, 0xbe]);
    let mut bh = [0u8; 32];
    bh[30..].copy_from_slice(&[0xc0, 0xde]);
    let expected = h32("0c39fb6b07cf6694b13e63e59f7b15255be1c93a4d6d3e0da6c99729647c0d11");
    assert_eq!(compute_op_output_root_v0(sr, wr, bh), expected);
    assert_eq!(
        verify_op_output_root(OUTPUT_ROOT_VERSION_V0, sr, wr, bh, expected),
        Ok(())
    );
}

/// EXTERNAL KAT from Base MAINNET itself: output 12086's on-chain root recomputes
/// exactly from Base block 21756600's real (stateRoot, messagePasserStorageRoot,
/// blockHash). This is the field order proven against the live chain.
#[test]
fn output_root_matches_base_mainnet_output_12086() {
    let recomputed = compute_op_output_root_v0(
        h32(fx::L2_STATE_ROOT),
        h32(fx::L2_WITHDRAWAL_STORAGE_ROOT),
        h32(fx::L2_BLOCK_HASH),
    );
    assert_eq!(recomputed, h32(fx::OUTPUT_ROOT));
}

/// FIELD-ORDER ADVERSARY: swapping any two preimage fields must change the root
/// (i.e. the accept above is evidence of ORDER, not just of content). All three
/// pairwise swaps of the real Base preimage must be rejected.
#[test]
fn output_root_swapped_fields_reject() {
    let sr = h32(fx::L2_STATE_ROOT);
    let wr = h32(fx::L2_WITHDRAWAL_STORAGE_ROOT);
    let bh = h32(fx::L2_BLOCK_HASH);
    let trusted = h32(fx::OUTPUT_ROOT);
    for (a, b, c) in [(wr, sr, bh), (bh, wr, sr), (sr, bh, wr)] {
        let r = verify_op_output_root(OUTPUT_ROOT_VERSION_V0, a, b, c, trusted);
        assert!(
            matches!(r, Err(BaseProofError::OutputRootMismatch { .. })),
            "swapped preimage fields must not recompute the output root"
        );
    }
}

#[test]
fn output_root_wrong_version_rejects() {
    let sr = h32(fx::L2_STATE_ROOT);
    let wr = h32(fx::L2_WITHDRAWAL_STORAGE_ROOT);
    let bh = h32(fx::L2_BLOCK_HASH);
    // Version 1 in the low byte (the plausible "next version") and a poisoned high
    // byte both refuse — BEFORE any hashing that might collide layouts.
    for byte_ix in [31usize, 0usize] {
        let mut v = [0u8; 32];
        v[byte_ix] = 1;
        let r = verify_op_output_root(v, sr, wr, bh, h32(fx::OUTPUT_ROOT));
        assert!(
            matches!(r, Err(BaseProofError::UnsupportedOutputRootVersion { .. })),
            "non-v0 version must be refused"
        );
    }
}

#[test]
fn output_root_zero_trusted_root_rejects() {
    let r = verify_op_output_root(
        OUTPUT_ROOT_VERSION_V0,
        h32(fx::L2_STATE_ROOT),
        h32(fx::L2_WITHDRAWAL_STORAGE_ROOT),
        h32(fx::L2_BLOCK_HASH),
        [0u8; 32],
    );
    assert_eq!(r, Err(BaseProofError::ZeroOutputRoot));
}

// ---------------------------------------------------------------------------
// The L1 anchor: slot math + committed-output opening
// ---------------------------------------------------------------------------

/// The Solidity dynamic-array slot math, pinned against the well-known constant
/// keccak256(uint256(3)) = 0xc2575a…f85b (independently recomputed via foundry
/// `cast keccak`) and the REAL slot eth_getProof served for l2Outputs[12086].
#[test]
fn l2_outputs_slot_math_matches_mainnet() {
    // Array data base slot for a dynamic array declared at slot 3.
    let base = h32("c2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b");
    assert_eq!(
        l2_output_root_slot(L2_OUTPUT_ORACLE_L2_OUTPUTS_SLOT, 0),
        base
    );
    // The REAL slots the L1 node served proofs for (base + 2*12086, +1).
    assert_eq!(
        l2_output_root_slot(3, fx::OUTPUT_INDEX),
        h32("c2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f7256c7")
    );
    assert_eq!(
        l2_output_meta_slot(3, fx::OUTPUT_INDEX),
        h32("c2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f7256c8")
    );
}

/// The packed OutputProposal metadata word, pinned against the REAL slot value L1
/// mainnet holds for output 12086: timestamp in the LOW 16 bytes, l2BlockNumber in
/// the HIGH 16 bytes.
#[test]
fn output_meta_packing_matches_mainnet() {
    let expected = u256("14bfab8000000000000000000000000672256c7");
    assert_eq!(
        pack_output_meta(fx::OUTPUT_TIMESTAMP, fx::OUTPUT_L2_BLOCK_NUMBER),
        expected
    );
}

#[test]
fn l1_committed_output_root_accepts() {
    let committed = verify_l1_committed_output_root(&l1_finalized(), &anchor())
        .expect("real L1 storage proof of Base output 12086 must verify");
    assert_eq!(committed.output_root, h32(fx::OUTPUT_ROOT));
    assert_eq!(committed.l2_block_number, fx::OUTPUT_L2_BLOCK_NUMBER);
    assert_eq!(committed.timestamp, fx::OUTPUT_TIMESTAMP);
}

// ---------------------------------------------------------------------------
// The full composition: accept
// ---------------------------------------------------------------------------

#[test]
fn real_base_weth_holding_accepts_consensus_proven() {
    let proven = run_default().expect("the full real Base mainnet chain must verify");
    assert_eq!(proven.trust, HoldingTrust::ConsensusProven);
    assert!(proven.is_consensus_proven());
    assert_eq!(proven.balance, u256(fx::EXPECTED_BALANCE_HEX));
    assert_eq!(proven.token, h20(fx::TOKEN));
    assert_eq!(proven.holder, h20(fx::HOLDER));
    // The holding is anchored at the L2 state root and the L1-PROVEN L2 block
    // number (never caller-claimed).
    assert_eq!(proven.state_root, h32(fx::L2_STATE_ROOT));
    assert_eq!(proven.block_number, fx::OUTPUT_L2_BLOCK_NUMBER);

    // The governance edge: EVM family tag (Base = ChainId::Evm(8453) downstream).
    let fields = proven.to_foreign_fields().expect("fits u128");
    assert_eq!(fields.chain_tag, CHAIN_TAG_EVM);
    assert!(fields.consensus_proven);
    assert_eq!(fields.amount, 2388840386918579889861u128);
    assert_eq!(fields.snapshot, fx::OUTPUT_L2_BLOCK_NUMBER);
    let mut want_holder = [0u8; 32];
    want_holder[12..].copy_from_slice(&h20(fx::HOLDER));
    assert_eq!(fields.holder, want_holder);
}

// ---------------------------------------------------------------------------
// The full composition: rejects (one perturbation each)
// ---------------------------------------------------------------------------

#[test]
fn forged_l2_state_root_rejects() {
    // The attack this module exists to stop: a VALID-LOOKING L2 state root that L1
    // never committed. The output-root recompute must refuse it.
    let mut c = l2_commitment();
    c.l2_state_root[7] ^= 0x01;
    let r = run(
        &l1_finalized(),
        &anchor(),
        &c,
        &nodes(fx::L2_ACCOUNT_PROOF),
        &nodes(fx::L2_STORAGE_PROOF),
        &token_account(),
        u256(fx::EXPECTED_BALANCE_HEX),
    );
    assert!(matches!(r, Err(BaseProofError::OutputRootMismatch { .. })));
}

#[test]
fn wrong_version_byte_rejects_through_composition() {
    let mut c = l2_commitment();
    c.version[31] = 1;
    let r = run(
        &l1_finalized(),
        &anchor(),
        &c,
        &nodes(fx::L2_ACCOUNT_PROOF),
        &nodes(fx::L2_STORAGE_PROOF),
        &token_account(),
        u256(fx::EXPECTED_BALANCE_HEX),
    );
    assert!(matches!(
        r,
        Err(BaseProofError::UnsupportedOutputRootVersion { .. })
    ));
}

#[test]
fn tampered_l1_output_root_slot_proof_rejects() {
    let mut a = anchor();
    let last = a.output_root_slot_proof.len() - 1;
    a.output_root_slot_proof[last][9] ^= 0x01;
    let r = run(
        &l1_finalized(),
        &a,
        &l2_commitment(),
        &nodes(fx::L2_ACCOUNT_PROOF),
        &nodes(fx::L2_STORAGE_PROOF),
        &token_account(),
        u256(fx::EXPECTED_BALANCE_HEX),
    );
    assert_eq!(r, Err(BaseProofError::L1OutputRootSlotProofInvalid));
}

#[test]
fn forged_output_root_value_rejects() {
    // Claim a DIFFERENT output root at the same slot: the L1 storage trie does not
    // commit to it (this is what stops a fabricated "trusted" root wholesale).
    let mut a = anchor();
    a.output_root[0] ^= 0x01;
    let r = run(
        &l1_finalized(),
        &a,
        &l2_commitment(),
        &nodes(fx::L2_ACCOUNT_PROOF),
        &nodes(fx::L2_STORAGE_PROOF),
        &token_account(),
        u256(fx::EXPECTED_BALANCE_HEX),
    );
    assert_eq!(r, Err(BaseProofError::L1OutputRootSlotProofInvalid));
}

#[test]
fn tampered_l1_oracle_account_proof_rejects() {
    let mut a = anchor();
    let last = a.oracle_account_proof.len() - 1;
    a.oracle_account_proof[last][11] ^= 0x01;
    let r = run(
        &l1_finalized(),
        &a,
        &l2_commitment(),
        &nodes(fx::L2_ACCOUNT_PROOF),
        &nodes(fx::L2_STORAGE_PROOF),
        &token_account(),
        u256(fx::EXPECTED_BALANCE_HEX),
    );
    assert_eq!(r, Err(BaseProofError::L1OracleAccountProofInvalid));
}

#[test]
fn wrong_l1_state_root_rejects() {
    // A FinalizedExecution whose L1 state root is not the one the account proof
    // commits to — the composition must bind the light-client root, not any
    // caller-claimed one.
    let mut sr = h32(fx::L1_STATE_ROOT);
    sr[0] ^= 0x01;
    let l1 = FinalizedExecution::new_unchecked(
        0,
        [0u8; 32],
        fx::L1_BLOCK_NUMBER,
        h32(fx::L1_BLOCK_HASH),
        sr,
        0,
    );
    let r = run(
        &l1,
        &anchor(),
        &l2_commitment(),
        &nodes(fx::L2_ACCOUNT_PROOF),
        &nodes(fx::L2_STORAGE_PROOF),
        &token_account(),
        u256(fx::EXPECTED_BALANCE_HEX),
    );
    assert_eq!(r, Err(BaseProofError::L1OracleAccountProofInvalid));
}

#[test]
fn wrong_output_index_rejects() {
    // A DIFFERENT in-bounds index (12085 vs 12086) derives different element slots;
    // the storage proof captured for 12086's slots cannot open them. (Distinct from
    // the out-of-bounds case, which the length bounds-check refuses earlier.)
    let mut a = anchor();
    a.output_index -= 1;
    let r = run(
        &l1_finalized(),
        &a,
        &l2_commitment(),
        &nodes(fx::L2_ACCOUNT_PROOF),
        &nodes(fx::L2_STORAGE_PROOF),
        &token_account(),
        u256(fx::EXPECTED_BALANCE_HEX),
    );
    assert_eq!(r, Err(BaseProofError::L1OutputRootSlotProofInvalid));
}

#[test]
fn out_of_bounds_output_index_rejects() {
    // A stale/deleted output: index == the PROVEN current length (12087 is one past
    // the last valid index 12086). deleteL2Outputs shrinks the length without
    // zeroing element storage, so the bounds check — not just a slot read — is what
    // refuses a challenger-deleted (disputed) output.
    let mut a = anchor();
    a.output_index = fx::L2_OUTPUTS_LENGTH; // == length ⇒ out of bounds
    let r = verify_l1_committed_output_root(&l1_finalized(), &a);
    assert_eq!(
        r,
        Err(BaseProofError::OutputIndexOutOfBounds {
            index: fx::L2_OUTPUTS_LENGTH,
            length: fx::L2_OUTPUTS_LENGTH,
        })
    );
}

#[test]
fn tampered_outputs_length_proof_rejects() {
    // A forged current length (claiming a longer array than L1 commits) must fail
    // the length-slot proof — you cannot manufacture bounds room for a deleted
    // output.
    let mut a = anchor();
    a.l2_outputs_length += 1000;
    let r = verify_l1_committed_output_root(&l1_finalized(), &a);
    assert_eq!(r, Err(BaseProofError::L1OutputsLengthProofInvalid));
}

#[test]
fn forged_l2_block_number_rejects() {
    // The snapshot height is L1-anchored: claiming a different l2BlockNumber
    // changes the packed metadata word and the meta-slot proof refuses.
    let mut a = anchor();
    a.l2_block_number += 1;
    let r = run(
        &l1_finalized(),
        &a,
        &l2_commitment(),
        &nodes(fx::L2_ACCOUNT_PROOF),
        &nodes(fx::L2_STORAGE_PROOF),
        &token_account(),
        u256(fx::EXPECTED_BALANCE_HEX),
    );
    assert_eq!(r, Err(BaseProofError::L1OutputMetaSlotProofInvalid));
}

#[test]
fn zero_output_root_rejects() {
    // A zero root is what an unset/out-of-bounds l2Outputs element reads as.
    let mut a = anchor();
    a.output_root = [0u8; 32];
    let r = run(
        &l1_finalized(),
        &a,
        &l2_commitment(),
        &nodes(fx::L2_ACCOUNT_PROOF),
        &nodes(fx::L2_STORAGE_PROOF),
        &token_account(),
        u256(fx::EXPECTED_BALANCE_HEX),
    );
    assert_eq!(r, Err(BaseProofError::ZeroOutputRoot));
}

#[test]
fn l2_proof_against_wrong_l2_state_root_rejects() {
    // An L2 account proof that does not open under the BOUND l2_state_root (here:
    // its terminal node tampered — equivalently, a proof captured against some
    // other L2 state). The L2 MPT link must refuse.
    let mut ap = nodes(fx::L2_ACCOUNT_PROOF);
    let last = ap.len() - 1;
    ap[last][10] ^= 0x01;
    let r = run(
        &l1_finalized(),
        &anchor(),
        &l2_commitment(),
        &ap,
        &nodes(fx::L2_STORAGE_PROOF),
        &token_account(),
        u256(fx::EXPECTED_BALANCE_HEX),
    );
    assert_eq!(
        r,
        Err(BaseProofError::L2Holding(
            Erc20ProofError::AccountProofInvalid
        ))
    );
}

#[test]
fn wrong_l2_balance_rejects() {
    let bad = u256(fx::EXPECTED_BALANCE_HEX) + Uint256::from(1u8);
    let r = run(
        &l1_finalized(),
        &anchor(),
        &l2_commitment(),
        &nodes(fx::L2_ACCOUNT_PROOF),
        &nodes(fx::L2_STORAGE_PROOF),
        &token_account(),
        bad,
    );
    assert_eq!(
        r,
        Err(BaseProofError::L2Holding(
            Erc20ProofError::StorageProofInvalid
        ))
    );
}

#[test]
fn tampered_l2_storage_proof_rejects() {
    let mut sp = nodes(fx::L2_STORAGE_PROOF);
    let last = sp.len() - 1;
    sp[last][6] ^= 0x01;
    let r = run(
        &l1_finalized(),
        &anchor(),
        &l2_commitment(),
        &nodes(fx::L2_ACCOUNT_PROOF),
        &sp,
        &token_account(),
        u256(fx::EXPECTED_BALANCE_HEX),
    );
    assert_eq!(
        r,
        Err(BaseProofError::L2Holding(
            Erc20ProofError::StorageProofInvalid
        ))
    );
}

/// The mapping slot key our verifier derives must equal the key Base's
/// eth_getProof was actually queried with (the Solidity mapping layout on L2).
#[test]
fn l2_balance_slot_key_matches_real_getproof_key() {
    let key = eth_lightclient::evm::erc20_balance_slot_key(&h20(fx::HOLDER), fx::BALANCES_SLOT);
    assert_eq!(key, h32(fx::STORAGE_SLOT_KEY));
}
