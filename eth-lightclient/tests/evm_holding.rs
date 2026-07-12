//! EVM proof-of-holdings (EIP-1186) — the ETH/Base analog of the non-custodial Solana
//! `prove_holding_consensus`.
//!
//! ACCEPT: a REAL external fixture — a genuine `eth_getProof` for a WETH holder at a
//! FINALIZED Ethereum mainnet block (captured from a public full node). This proves
//! SPEC conformance (real MPT nodes, real account+storage tries), not a round-trip.
//!
//! REJECT (all default-run, both polarities): a tampered account node, a tampered
//! storage node, a wrong balance, a wrong contract, a wrong balances-slot, a state root
//! that is not the one the proof commits to, a zero balance (Nomad-law), and an empty
//! proof. Every one must fail closed — never mint a `ProvenErc20Holding`.

#[path = "fixtures/weth.rs"]
mod weth;

use eth_lightclient::evm::{
    erc20_balance_slot_key, verify_erc20_holding, AccountClaim, Erc20ProofError, Uint256,
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
        nonce: weth::ACCT_NONCE,
        balance: u256(weth::ACCT_BALANCE_HEX),
        storage_hash: h32(weth::ACCT_STORAGE_HASH),
        code_hash: h32(weth::ACCT_CODE_HASH),
    }
}

/// The whole verify, parameterized so reject tests perturb one input each.
#[allow(clippy::too_many_arguments)]
fn run(
    state_root: [u8; 32],
    account_proof: &[Vec<u8>],
    storage_proof: &[Vec<u8>],
    token: [u8; 20],
    holder: [u8; 20],
    slot: u64,
    account: &AccountClaim,
    balance: Uint256,
) -> Result<eth_lightclient::evm::ProvenErc20Holding, Erc20ProofError> {
    verify_erc20_holding(
        state_root,
        account_proof,
        storage_proof,
        token,
        holder,
        slot,
        account,
        balance,
        weth::BLOCK_NUMBER,
    )
}

#[test]
fn real_weth_holding_accepts() {
    let proven = run(
        h32(weth::STATE_ROOT),
        &nodes(weth::ACCOUNT_PROOF),
        &nodes(weth::STORAGE_PROOF),
        h20(weth::TOKEN),
        h20(weth::HOLDER),
        weth::BALANCES_SLOT,
        &account_claim(),
        u256(weth::EXPECTED_BALANCE_HEX),
    )
    .expect("real mainnet WETH EIP-1186 proof must verify");

    assert_eq!(proven.balance, u256(weth::EXPECTED_BALANCE_HEX));
    assert_eq!(proven.token, h20(weth::TOKEN));
    assert_eq!(proven.holder, h20(weth::HOLDER));
    assert_eq!(proven.state_root, h32(weth::STATE_ROOT));
    assert_eq!(proven.block_number, weth::BLOCK_NUMBER);
}

/// The computed slot key must equal the key `eth_getProof` was actually queried with —
/// this is the Solidity `mapping(address=>uint256)` layout, proven against a real node.
#[test]
fn balance_slot_key_matches_real_getproof_key() {
    let key = erc20_balance_slot_key(&h20(weth::HOLDER), weth::BALANCES_SLOT);
    assert_eq!(key, h32(weth::STORAGE_SLOT_KEY));
}

#[test]
fn tampered_account_node_rejects() {
    let mut ap = nodes(weth::ACCOUNT_PROOF);
    let last = ap.len() - 1;
    ap[last][10] ^= 0x01;
    let r = run(
        h32(weth::STATE_ROOT),
        &ap,
        &nodes(weth::STORAGE_PROOF),
        h20(weth::TOKEN),
        h20(weth::HOLDER),
        weth::BALANCES_SLOT,
        &account_claim(),
        u256(weth::EXPECTED_BALANCE_HEX),
    );
    assert_eq!(r, Err(Erc20ProofError::AccountProofInvalid));
}

#[test]
fn tampered_storage_node_rejects() {
    let mut sp = nodes(weth::STORAGE_PROOF);
    let last = sp.len() - 1;
    sp[last][8] ^= 0x01;
    let r = run(
        h32(weth::STATE_ROOT),
        &nodes(weth::ACCOUNT_PROOF),
        &sp,
        h20(weth::TOKEN),
        h20(weth::HOLDER),
        weth::BALANCES_SLOT,
        &account_claim(),
        u256(weth::EXPECTED_BALANCE_HEX),
    );
    assert_eq!(r, Err(Erc20ProofError::StorageProofInvalid));
}

#[test]
fn wrong_balance_rejects() {
    // A balance one wei off the proven value: the storage trie does not commit to it.
    let bad = u256(weth::EXPECTED_BALANCE_HEX) + Uint256::from(1u8);
    let r = run(
        h32(weth::STATE_ROOT),
        &nodes(weth::ACCOUNT_PROOF),
        &nodes(weth::STORAGE_PROOF),
        h20(weth::TOKEN),
        h20(weth::HOLDER),
        weth::BALANCES_SLOT,
        &account_claim(),
        bad,
    );
    assert_eq!(r, Err(Erc20ProofError::StorageProofInvalid));
}

#[test]
fn wrong_contract_rejects() {
    // Point the SAME account proof at a different token address: the account key
    // keccak(other) does not trace this proof. Fail closed (the Solana owner-forgery
    // lesson: the balance is only authoritative under the RIGHT contract).
    let mut other = h20(weth::TOKEN);
    other[0] ^= 0xFF;
    let r = run(
        h32(weth::STATE_ROOT),
        &nodes(weth::ACCOUNT_PROOF),
        &nodes(weth::STORAGE_PROOF),
        other,
        h20(weth::HOLDER),
        weth::BALANCES_SLOT,
        &account_claim(),
        u256(weth::EXPECTED_BALANCE_HEX),
    );
    assert_eq!(r, Err(Erc20ProofError::AccountProofInvalid));
}

#[test]
fn wrong_balances_slot_rejects() {
    // Slot 4 instead of the real slot 3 → a different storage key → the storage proof
    // does not open it.
    let r = run(
        h32(weth::STATE_ROOT),
        &nodes(weth::ACCOUNT_PROOF),
        &nodes(weth::STORAGE_PROOF),
        h20(weth::TOKEN),
        h20(weth::HOLDER),
        weth::BALANCES_SLOT + 1,
        &account_claim(),
        u256(weth::EXPECTED_BALANCE_HEX),
    );
    assert_eq!(r, Err(Erc20ProofError::StorageProofInvalid));
}

#[test]
fn wrong_state_root_rejects() {
    // A state root that is NOT the one the account proof commits to (the light client
    // must bind the verified finalized state root, not any RPC-claimed one).
    let mut sr = h32(weth::STATE_ROOT);
    sr[0] ^= 0x01;
    let r = run(
        sr,
        &nodes(weth::ACCOUNT_PROOF),
        &nodes(weth::STORAGE_PROOF),
        h20(weth::TOKEN),
        h20(weth::HOLDER),
        weth::BALANCES_SLOT,
        &account_claim(),
        u256(weth::EXPECTED_BALANCE_HEX),
    );
    assert_eq!(r, Err(Erc20ProofError::AccountProofInvalid));
}

#[test]
fn tampered_storage_hash_rejects() {
    // Perturbing the account's claimed storageHash changes the RLP account leaf, so the
    // ACCOUNT proof fails first — binding storageHash to the state root (you cannot
    // substitute a storage trie whose root the account does not commit to).
    let mut acct = account_claim();
    acct.storage_hash[0] ^= 0x01;
    let r = run(
        h32(weth::STATE_ROOT),
        &nodes(weth::ACCOUNT_PROOF),
        &nodes(weth::STORAGE_PROOF),
        h20(weth::TOKEN),
        h20(weth::HOLDER),
        weth::BALANCES_SLOT,
        &acct,
        u256(weth::EXPECTED_BALANCE_HEX),
    );
    assert_eq!(r, Err(Erc20ProofError::AccountProofInvalid));
}

#[test]
fn zero_balance_rejects_nomad_law() {
    let r = run(
        h32(weth::STATE_ROOT),
        &nodes(weth::ACCOUNT_PROOF),
        &nodes(weth::STORAGE_PROOF),
        h20(weth::TOKEN),
        h20(weth::HOLDER),
        weth::BALANCES_SLOT,
        &account_claim(),
        Uint256::ZERO,
    );
    assert_eq!(r, Err(Erc20ProofError::ZeroBalance));
}

#[test]
fn empty_account_proof_rejects_nomad_law() {
    let r = run(
        h32(weth::STATE_ROOT),
        &[],
        &nodes(weth::STORAGE_PROOF),
        h20(weth::TOKEN),
        h20(weth::HOLDER),
        weth::BALANCES_SLOT,
        &account_claim(),
        u256(weth::EXPECTED_BALANCE_HEX),
    );
    assert_eq!(r, Err(Erc20ProofError::AccountProofInvalid));
}

#[test]
fn empty_storage_proof_rejects_nomad_law() {
    let r = run(
        h32(weth::STATE_ROOT),
        &nodes(weth::ACCOUNT_PROOF),
        &[],
        h20(weth::TOKEN),
        h20(weth::HOLDER),
        weth::BALANCES_SLOT,
        &account_claim(),
        u256(weth::EXPECTED_BALANCE_HEX),
    );
    assert_eq!(r, Err(Erc20ProofError::StorageProofInvalid));
}
