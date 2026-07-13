//! **Robinhood Chain inbound proof-of-holdings** (EIP-1186) — a REAL tokenized-stock
//! (TSLA) balance on Robinhood Chain testnet (chain id 46630, an EVM Arbitrum-Orbit L2),
//! proven INTO dregg through the SAME audited light-client verifier the Ethereum/Base
//! lanes use. Because Robinhood Chain is EVM, `eth-lightclient`'s EIP-1186 storage-proof
//! machinery works directly; the only Robinhood-specific glue is the WIDE balance-slot
//! key ([`verify_erc20_holding_wide`]) for its OZ-v5 ERC-7201 namespaced-storage tokens.
//!
//! ACCEPT: a genuine `eth_getProof` for holder `0x8b251ADF…` at a recent Robinhood-testnet
//! block (`fixtures/robinhood_tsla.rs`, captured from the live public RPC). This proves
//! SPEC conformance — real MPT nodes, the real account+storage tries under the real
//! Robinhood-Chain state root — not a round-trip.
//!
//! REJECT (both polarities, all default-run): a tampered account node, a tampered storage
//! node, a wrong balance, a wrong contract, a forged/wrong state root, the WRONG (small
//! `u64`) balances-slot form, a zero balance (Nomad-law), and an empty proof. Every one
//! must fail closed — never mint a `ProvenErc20Holding`.
//!
//! ## Trust anchor (honest)
//!
//! The proof is verified against a Robinhood-Chain **state root supplied to the verifier**.
//! Robinhood Chain is an Arbitrum-Orbit L2 — there is NO Altair beacon / sync committee —
//! so the mint is [`HoldingTrust::StructureOnly`] (`consensus_proven == false`): the
//! near-term anchor is **weak-subjectivity** (trust a checkpointed/recent Robinhood root).
//! The trustless upgrade is to verify that L2 root against its **L1 (Ethereum)
//! Arbitrum-rollup anchor** (the output root posted to L1, opened with this same EIP-1186
//! machinery). This test does NOT claim the L1-trustless rung; it proves the MPT chain
//! under the supplied root and reports `StructureOnly`, fail-closed.

#[path = "fixtures/robinhood_tsla.rs"]
mod tsla;

use eth_lightclient::evm::{
    erc20_balance_slot_key, erc20_balance_slot_key_wide, verify_erc20_holding_wide, AccountClaim,
    Erc20ProofError, HoldingTrust, ProvenErc20Holding, Uint256, CHAIN_TAG_EVM,
};

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
fn account_claim() -> AccountClaim {
    AccountClaim {
        nonce: tsla::ACCT_NONCE,
        balance: u256(tsla::ACCT_BALANCE_HEX),
        storage_hash: h32(tsla::ACCT_STORAGE_HASH),
        code_hash: h32(tsla::ACCT_CODE_HASH),
    }
}

/// The whole wide verify, parameterized so reject tests perturb one input each.
#[allow(clippy::too_many_arguments)]
fn run(
    state_root: [u8; 32],
    account_proof: &[Vec<u8>],
    storage_proof: &[Vec<u8>],
    token: [u8; 20],
    holder: [u8; 20],
    base_slot: [u8; 32],
    account: &AccountClaim,
    balance: Uint256,
) -> Result<ProvenErc20Holding, Erc20ProofError> {
    verify_erc20_holding_wide(
        state_root,
        account_proof,
        storage_proof,
        token,
        holder,
        base_slot,
        account,
        balance,
        tsla::BLOCK_NUMBER,
    )
}

/// The real TSLA holding on Robinhood Chain verifies — 5.0 TSLA (5e18 atomic) for the
/// faucet-funded holder, under the genuine Robinhood-testnet state root.
#[test]
fn real_robinhood_tsla_holding_accepts() {
    let proven = run(
        h32(tsla::STATE_ROOT),
        &nodes(tsla::ACCOUNT_PROOF),
        &nodes(tsla::STORAGE_PROOF),
        h20(tsla::TOKEN),
        h20(tsla::HOLDER),
        h32(tsla::BALANCES_BASE_SLOT),
        &account_claim(),
        u256(tsla::EXPECTED_BALANCE_HEX),
    )
    .expect("real Robinhood testnet TSLA EIP-1186 proof must verify");

    assert_eq!(proven.balance, u256(tsla::EXPECTED_BALANCE_HEX));
    assert_eq!(proven.balance, Uint256::from(5_000_000_000_000_000_000u64)); // 5.0 TSLA
    assert_eq!(proven.token, h20(tsla::TOKEN));
    assert_eq!(proven.holder, h20(tsla::HOLDER));
    assert_eq!(proven.state_root, h32(tsla::STATE_ROOT));
    assert_eq!(proven.block_number, tsla::BLOCK_NUMBER);

    // HONEST trust grade: verified against a SUPPLIED Robinhood-Chain root (no Altair
    // sync committee on an Arbitrum-Orbit L2) → StructureOnly / weak-subjectivity.
    assert_eq!(proven.trust, HoldingTrust::StructureOnly);
    assert!(!proven.is_consensus_proven());
}

/// The wide slot-key must equal the key `eth_getProof` was actually queried with — the
/// OZ-v5 ERC-7201 `mapping(address=>uint256)` layout, proven against the real node.
#[test]
fn wide_balance_slot_key_matches_real_getproof_key() {
    let key = erc20_balance_slot_key_wide(&h20(tsla::HOLDER), &h32(tsla::BALANCES_BASE_SLOT));
    assert_eq!(key, h32(tsla::STORAGE_SLOT_KEY));
}

/// The Robinhood token does NOT use a small `u64` base slot — the narrow helper (slots
/// 0..3) computes a DIFFERENT key, so the narrow verify path could never open this
/// balance. This pins WHY the wide glue is load-bearing, not cosmetic.
#[test]
fn narrow_u64_slot_key_does_not_match() {
    for slot in 0u64..=9 {
        assert_ne!(
            erc20_balance_slot_key(&h20(tsla::HOLDER), slot),
            h32(tsla::STORAGE_SLOT_KEY),
            "no small-u64 slot reproduces the ERC-7201 namespaced key"
        );
    }
}

/// The chain-agnostic edge fields carry the EVM family tag + the real balance, ready for
/// the governance join. (The FULL Evm(46630) network id is supplied relayer-side; the
/// edge tag alone is the family byte.)
#[test]
fn real_holding_converts_to_evm_foreign_fields() {
    let proven = run(
        h32(tsla::STATE_ROOT),
        &nodes(tsla::ACCOUNT_PROOF),
        &nodes(tsla::STORAGE_PROOF),
        h20(tsla::TOKEN),
        h20(tsla::HOLDER),
        h32(tsla::BALANCES_BASE_SLOT),
        &account_claim(),
        u256(tsla::EXPECTED_BALANCE_HEX),
    )
    .expect("accepts");
    let fields = proven.to_foreign_fields().expect("5e18 fits u128");
    assert_eq!(fields.chain_tag, CHAIN_TAG_EVM);
    assert_eq!(fields.amount, 5_000_000_000_000_000_000u128);
    assert_eq!(fields.snapshot, tsla::BLOCK_NUMBER);
    // 20-byte token/holder left-padded into 32; low 20 bytes are the address.
    assert_eq!(&fields.asset[12..], &h20(tsla::TOKEN));
    assert_eq!(&fields.holder[12..], &h20(tsla::HOLDER));
    assert!(
        !fields.consensus_proven,
        "weak-subjectivity: fail-closed to false"
    );
}

// --------------------------------------------------------------------------
// REJECT — both polarities. A tampered proof / wrong balance / forged root must
// NEVER mint a holding.
// --------------------------------------------------------------------------

#[test]
fn tampered_account_node_rejects() {
    let mut ap = nodes(tsla::ACCOUNT_PROOF);
    let last = ap.len() - 1;
    ap[last][10] ^= 0x01;
    assert_eq!(
        run(
            h32(tsla::STATE_ROOT),
            &ap,
            &nodes(tsla::STORAGE_PROOF),
            h20(tsla::TOKEN),
            h20(tsla::HOLDER),
            h32(tsla::BALANCES_BASE_SLOT),
            &account_claim(),
            u256(tsla::EXPECTED_BALANCE_HEX),
        ),
        Err(Erc20ProofError::AccountProofInvalid)
    );
}

#[test]
fn tampered_storage_node_rejects() {
    let mut sp = nodes(tsla::STORAGE_PROOF);
    let last = sp.len() - 1;
    sp[last][8] ^= 0x01;
    assert_eq!(
        run(
            h32(tsla::STATE_ROOT),
            &nodes(tsla::ACCOUNT_PROOF),
            &sp,
            h20(tsla::TOKEN),
            h20(tsla::HOLDER),
            h32(tsla::BALANCES_BASE_SLOT),
            &account_claim(),
            u256(tsla::EXPECTED_BALANCE_HEX),
        ),
        Err(Erc20ProofError::StorageProofInvalid)
    );
}

#[test]
fn wrong_balance_rejects() {
    // One atomic unit off the proven 5e18: the storage trie does not commit to it.
    let bad = u256(tsla::EXPECTED_BALANCE_HEX) + Uint256::from(1u8);
    assert_eq!(
        run(
            h32(tsla::STATE_ROOT),
            &nodes(tsla::ACCOUNT_PROOF),
            &nodes(tsla::STORAGE_PROOF),
            h20(tsla::TOKEN),
            h20(tsla::HOLDER),
            h32(tsla::BALANCES_BASE_SLOT),
            &account_claim(),
            bad,
        ),
        Err(Erc20ProofError::StorageProofInvalid)
    );
}

#[test]
fn wrong_contract_rejects() {
    let mut other = h20(tsla::TOKEN);
    other[0] ^= 0xFF;
    assert_eq!(
        run(
            h32(tsla::STATE_ROOT),
            &nodes(tsla::ACCOUNT_PROOF),
            &nodes(tsla::STORAGE_PROOF),
            other,
            h20(tsla::HOLDER),
            h32(tsla::BALANCES_BASE_SLOT),
            &account_claim(),
            u256(tsla::EXPECTED_BALANCE_HEX),
        ),
        Err(Erc20ProofError::AccountProofInvalid)
    );
}

#[test]
fn forged_state_root_rejects() {
    // A state root that is NOT the one the account proof commits to — the light client
    // must bind the real Robinhood-Chain state root, not a forged one.
    let mut sr = h32(tsla::STATE_ROOT);
    sr[0] ^= 0x01;
    assert_eq!(
        run(
            sr,
            &nodes(tsla::ACCOUNT_PROOF),
            &nodes(tsla::STORAGE_PROOF),
            h20(tsla::TOKEN),
            h20(tsla::HOLDER),
            h32(tsla::BALANCES_BASE_SLOT),
            &account_claim(),
            u256(tsla::EXPECTED_BALANCE_HEX),
        ),
        Err(Erc20ProofError::AccountProofInvalid)
    );
}

#[test]
fn wrong_base_slot_rejects() {
    // Perturb the ERC-7201 namespace base slot → a different storage key → the storage
    // proof does not open it.
    let mut base = h32(tsla::BALANCES_BASE_SLOT);
    base[0] ^= 0x01;
    assert_eq!(
        run(
            h32(tsla::STATE_ROOT),
            &nodes(tsla::ACCOUNT_PROOF),
            &nodes(tsla::STORAGE_PROOF),
            h20(tsla::TOKEN),
            h20(tsla::HOLDER),
            base,
            &account_claim(),
            u256(tsla::EXPECTED_BALANCE_HEX),
        ),
        Err(Erc20ProofError::StorageProofInvalid)
    );
}

#[test]
fn zero_balance_rejects_nomad_law() {
    assert_eq!(
        run(
            h32(tsla::STATE_ROOT),
            &nodes(tsla::ACCOUNT_PROOF),
            &nodes(tsla::STORAGE_PROOF),
            h20(tsla::TOKEN),
            h20(tsla::HOLDER),
            h32(tsla::BALANCES_BASE_SLOT),
            &account_claim(),
            Uint256::ZERO,
        ),
        Err(Erc20ProofError::ZeroBalance)
    );
}

#[test]
fn empty_storage_proof_rejects() {
    assert_eq!(
        run(
            h32(tsla::STATE_ROOT),
            &nodes(tsla::ACCOUNT_PROOF),
            &[],
            h20(tsla::TOKEN),
            h20(tsla::HOLDER),
            h32(tsla::BALANCES_BASE_SLOT),
            &account_claim(),
            u256(tsla::EXPECTED_BALANCE_HEX),
        ),
        Err(Erc20ProofError::StorageProofInvalid)
    );
}
