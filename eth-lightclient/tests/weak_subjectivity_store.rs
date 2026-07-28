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

use blst::min_pk::{AggregateSignature, SecretKey, Signature};
use eth_lightclient::evm::{verify_erc20_holding_finalized, AccountClaim, HoldingTrust, Uint256};
use eth_lightclient::execution::{
    compute_branch_root, ExecutionPayloadHeader, EXECUTION_PAYLOAD_SUBTREE_INDEX,
};
use eth_lightclient::finality::{
    verify_finalized_update, FinalizedExecution, LightClientHeader, LightClientUpdate,
    FINALIZED_ROOT_SUBTREE_INDEX,
};
use eth_lightclient::store::{StoreError, WeakSubjectivityStore};
use eth_lightclient::{
    compute_signing_root, BeaconBlockHeader, Error, SyncAggregate, SyncCommittee, TrustedCommittee,
    DST, SYNC_COMMITTEE_SIZE,
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

// ============================================================================
// THE ATTACK, MADE CONCRETE — a forged committee that GENUINELY SIGNS
// ============================================================================
//
// Every REJECT above refuses a committee that could never have verified anyway: the forged
// committee is the real one rotated by a position, so it never signed the real header and
// `blst` says no. That is a real property, but it is NOT the attack, and a reader could come
// away believing the BLS floor is what stops a hostile committee. It is not. The attack is:
//
//   the attacker GENERATES 512 keypairs, keeps the secrets, invents an update whose branches
//   all reconstruct, and signs it with all 512 of their own keys.
//
// Every cryptographic check then PASSES — the committee is exactly 512, the bitfield is 512,
// participation is 512/512, the aggregate signature verifies against those pubkeys, the finality
// branch folds to the attested state root, the execution branch folds to the finalized body
// root. `verifyFinalizedUpdate` is TRUE. The verified Lean gate ACCEPTS, correctly, because
// everything it decides over is true. The only false thing is the premise that those pubkeys
// were the Ethereum sync committee, and that premise is not a cryptographic object — it is a
// trust anchor, and it lives entirely in how the caller obtained the committee.
//
// So these two tests are stated as a MATCHED PAIR over the SAME forged update, differing in
// exactly one thing: where the committee came from. Un-anchored, the drain succeeds and the
// attacker's chosen EVM state root comes back in a `FinalizedExecution`. Anchored to the
// weak-subjectivity store, it is refused — and the honest update is still admitted in the same
// test, so a refusal cannot be passing for the wrong reason.

/// The attacker's own 512-key sync committee. They hold every secret, so they can produce a
/// genuine BLS12-381 aggregate over any header they like.
fn attacker_keys() -> Vec<SecretKey> {
    (0..SYNC_COMMITTEE_SIZE as u32)
        .map(|i| {
            let mut ikm = [0u8; 32];
            ikm[..4].copy_from_slice(&i.to_be_bytes());
            ikm[4] = 0xF0; // domain-separated from every honest fixture IKM
            SecretKey::key_gen(&ikm, &[]).expect("blst key_gen")
        })
        .collect()
}

fn attacker_pubkeys(keys: &[SecretKey]) -> Vec<[u8; 48]> {
    keys.iter().map(|k| k.sk_to_pk().compress()).collect()
}

/// The attacker's chosen EVM world-state root — the payload of the drain. Anything anchored to
/// this root (an ERC-20 balance, a bridge deposit record) is whatever the attacker says it is.
const ATTACKER_EXECUTION_STATE_ROOT: [u8; 32] = [0xEE; 32];

/// A fully SELF-CONSISTENT forged `LightClientUpdate`, signed by `keys`.
///
/// The attacker does not have to break any hash: they pick the branches FIRST and derive the
/// roots that those branches fold to (`compute_branch_root`), then put those roots in the
/// headers. Both SSZ reconstructions therefore hold by construction, at the admissible depths
/// (7 finality / 4 execution). Then all 512 of their keys sign the attested header under the
/// REAL fork version and the REAL pinned `genesis_validators_root`, so the signing domain is
/// correct too. Nothing here is malformed and nothing here is a near-miss.
fn forged_update(keys: &[SecretKey]) -> LightClientUpdate {
    // (1) The attacker's execution payload, carrying the state root they want believed.
    let mut execution = execution_header();
    execution.state_root = ATTACKER_EXECUTION_STATE_ROOT;
    execution.block_hash = [0xED; 32];

    // (2) An execution branch they CHOOSE, and the body root it folds to.
    let execution_branch: Vec<[u8; 32]> = (0..4u8).map(|i| [0xB0 | i; 32]).collect();
    let body_root = compute_branch_root(
        &execution.hash_tree_root(),
        &execution_branch,
        EXECUTION_PAYLOAD_SUBTREE_INDEX,
    );

    // (3) The forged finalized beacon header carrying that body root.
    let fin_beacon = BeaconBlockHeader {
        slot: e2e::FIN_SLOT,
        proposer_index: 999_999,
        parent_root: [0xA1; 32],
        state_root: [0xA2; 32],
        body_root,
    };

    // (4) A finality branch they CHOOSE (depth 7, Electra), and the attested state root it
    //     folds to — so `finality_branch_reconstructs` is true.
    let finality_branch: Vec<[u8; 32]> = (0..7u8).map(|i| [0xC0 | i; 32]).collect();
    let attested_state_root = compute_branch_root(
        &fin_beacon.hash_tree_root(),
        &finality_branch,
        FINALIZED_ROOT_SUBTREE_INDEX,
    );
    let attested = BeaconBlockHeader {
        slot: e2e::ATTESTED_SLOT,
        proposer_index: 999_998,
        parent_root: [0xA3; 32],
        state_root: attested_state_root,
        body_root: [0xA4; 32],
    };

    // (5) All 512 attacker keys sign it, under the REAL domain (correct fork version + the
    //     correct pinned gvr) — so not even the domain is wrong.
    let signing_root = compute_signing_root(&attested, e2e::FORK_VERSION, gvr());
    let sigs: Vec<Signature> = keys
        .iter()
        .map(|k| k.sign(&signing_root, DST, &[]))
        .collect();
    let refs: Vec<&Signature> = sigs.iter().collect();
    let sig = AggregateSignature::aggregate(&refs, true)
        .expect("attacker aggregate")
        .to_signature()
        .compress();

    LightClientUpdate {
        attested_header: attested,
        finalized_header: LightClientHeader {
            beacon: fin_beacon,
            execution,
            execution_branch,
        },
        finality_branch,
        sync_aggregate: SyncAggregate {
            sync_committee_bits: [0xFF; SYNC_COMMITTEE_SIZE / 8], // 512/512 participation
            sync_committee_signature: sig,
        },
    }
}

/// **POLE A — the drain, un-anchored.** With the committee supplied as a bare caller claim
/// (now spelled [`TrustedCommittee::new_unchecked`], previously just the second argument), the
/// verified gate ACCEPTS the forgery and hands back the attacker's chosen EVM state root.
///
/// This assertion is the point of the whole pair: it proves the un-anchored path is a REAL
/// capability with a REAL consequence, not a theoretical worry. A test suite that only ever
/// showed refusals would be satisfied by a gate that refuses everything, and would tell you
/// nothing about whether the anchor is what is doing the work.
#[test]
fn unanchored_committee_ADMITS_a_fully_forged_update() {
    let keys = attacker_keys();
    let pubkeys = attacker_pubkeys(&keys);
    let forged = forged_update(&keys);

    let finalized = verify_finalized_update(
        &forged,
        &TrustedCommittee::new_unchecked(&pubkeys, gvr()),
        e2e::FORK_VERSION,
    )
    .expect(
        "the forgery is cryptographically PERFECT relative to the attacker's own committee — \
         if this refuses, the fixture stopped modelling the attack and the anchored REJECT \
         below proves nothing",
    );

    assert_eq!(
        finalized.execution_state_root(),
        ATTACKER_EXECUTION_STATE_ROOT,
        "the un-anchored path returns the ATTACKER's EVM state root as consensus-verified"
    );
}

/// **POLE B — the SAME forgery, anchored.** One thing changes: the committee comes from a
/// weak-subjectivity store pinned to a governance checkpoint instead of from the caller. Three
/// refusals and one admission, all in this one process, so no assertion can pass because the
/// rule never ran:
///
///   * the attacker's committee cannot be INSTALLED (its rotation branch does not reconstruct
///     the pinned checkpoint state root) — `UnchainedCommittee`;
///   * a store that therefore has no committee yields no witness at all — `NoTrustedCommittee`,
///     so there is no anchored spelling of Pole A's `Ok`;
///   * a store holding the REAL committee refuses the forged update — `BadSignature`, because
///     the real committee did not sign it;
///   * …and that SAME store still ADMITS the honest mainnet update, at the real state root.
#[test]
fn anchored_committee_REFUSES_the_same_forged_update() {
    let keys = attacker_keys();
    let forged = forged_update(&keys);
    let attacker_committee = SyncCommittee {
        pubkeys: attacker_pubkeys(&keys),
        aggregate_pubkey: h48(e2e::COMMITTEE_AGGREGATE_PUBKEY),
    };

    // (1) The attacker's committee cannot be installed under the governance pin.
    let mut store =
        WeakSubjectivityStore::pin_checkpoint(h32(e2e::PREV_ATTESTED_STATE_ROOT), gvr(), 1799);
    let err = store
        .bootstrap_committee(attacker_committee, &branch(e2e::COMMITTEE_BRANCH))
        .unwrap_err();
    assert!(
        matches!(err, StoreError::UnchainedCommittee(Error::BadMerkleBranch)),
        "an attacker-generated committee must not chain from the pinned checkpoint, got {err:?}"
    );

    // (2) …so no anchored witness exists at all. Pole A's `Ok` has no anchored spelling.
    assert!(matches!(
        store.trusted_committee().map(|_| ()),
        Err(StoreError::NoTrustedCommittee)
    ));
    assert_eq!(
        store.verify(&forged, e2e::FORK_VERSION).unwrap_err(),
        StoreError::NoTrustedCommittee
    );

    // (3) A store holding the REAL committee refuses the forged update outright: the real
    //     committee never signed it.
    let real_store =
        WeakSubjectivityStore::pin_genesis_committee(real_committee(), gvr(), 1800).unwrap();
    assert_eq!(
        real_store.verify(&forged, e2e::FORK_VERSION).unwrap_err(),
        StoreError::Verify(Error::BadSignature),
        "the anchored committee must refuse the attacker's update"
    );

    // (4) ACCEPT, in the SAME process and through the SAME store: the honest mainnet update
    //     still verifies to the REAL execution state root. The refusals above are therefore a
    //     discrimination, not a gate that has degenerated into refusing everything.
    let honest = real_store
        .verify(&update(), e2e::FORK_VERSION)
        .expect("the anchored store must still ADMIT the honest mainnet update");
    assert_eq!(honest.execution_state_root(), h32(e2e::EX_STATE_ROOT));
    assert_ne!(
        honest.execution_state_root(),
        ATTACKER_EXECUTION_STATE_ROOT,
        "accept and refuse must land on different roots — otherwise the pair is vacuous"
    );
}
