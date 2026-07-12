//! The EVM → chain-agnostic foreign-holding EDGE (`ForeignHoldingFields`), driven by
//! the REAL mainnet WETH EIP-1186 fixture.
//!
//! Both polarities, default-run:
//! - ACCEPT: a normal balance converts with the correct 20 → 32 left-zero padding,
//!   `chain_tag = 1` (dregg-governance `ChainId::Evm`), snapshot = block number; the
//!   consensus-anchored path (`verify_erc20_holding_finalized`) yields
//!   `consensus_proven = true`.
//! - REJECT: a `U256` balance above `u128::MAX` REFUSES (never truncates); a
//!   structure-only holding (bare caller-asserted root) yields
//!   `consensus_proven = false`; the finalized path fails closed on a root the
//!   proof does not commit to.

// The fixture module is shared with evm_holding.rs; not every constant is used here.
#[allow(dead_code)]
#[path = "fixtures/weth.rs"]
mod weth;

use eth_lightclient::evm::{
    pad_address_32, verify_erc20_holding, verify_erc20_holding_finalized, AccountClaim,
    ForeignFieldsError, HoldingTrust, ProvenErc20Holding, Uint256, CHAIN_TAG_EVM,
};
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

fn account_claim() -> AccountClaim {
    AccountClaim {
        nonce: weth::ACCT_NONCE,
        balance: u256(weth::ACCT_BALANCE_HEX),
        storage_hash: h32(weth::ACCT_STORAGE_HASH),
        code_hash: h32(weth::ACCT_CODE_HASH),
    }
}

/// A `FinalizedExecution` whose execution state root is the fixture's — standing in
/// for the output of `verify_finalized_update` (exercised in finality_kat.rs).
fn finalized_at_fixture_root() -> FinalizedExecution {
    // `new_unchecked`: the test asserts this root stands in for a verified update's
    // output. External code CANNOT build a FinalizedExecution by struct literal — the
    // private `_verified` seal forces this loud, greppable call.
    FinalizedExecution::new_unchecked(
        0,
        [0u8; 32],
        weth::BLOCK_NUMBER,
        [0u8; 32],
        h32(weth::STATE_ROOT),
    )
}

fn structure_only_holding() -> ProvenErc20Holding {
    verify_erc20_holding(
        h32(weth::STATE_ROOT),
        &nodes(weth::ACCOUNT_PROOF),
        &nodes(weth::STORAGE_PROOF),
        h20(weth::TOKEN),
        h20(weth::HOLDER),
        weth::BALANCES_SLOT,
        &account_claim(),
        u256(weth::EXPECTED_BALANCE_HEX),
        weth::BLOCK_NUMBER,
    )
    .expect("real mainnet WETH EIP-1186 proof must verify")
}

/// ACCEPT: a normal balance converts, with the documented 20 → 32 LEFT-ZERO padding
/// (12 zero bytes then the address), chain_tag 1, snapshot = block number.
#[test]
fn normal_balance_converts_with_left_zero_padding() {
    let fields = structure_only_holding()
        .to_foreign_fields()
        .expect("a u128-range balance must convert");

    assert_eq!(fields.chain_tag, CHAIN_TAG_EVM);
    assert_eq!(
        fields.chain_tag, 1,
        "must match dregg-governance ChainId::Evm.tag()"
    );

    // holder: [0..12] zero, [12..32] the 20-byte address.
    let holder20 = h20(weth::HOLDER);
    assert_eq!(&fields.holder[..12], &[0u8; 12]);
    assert_eq!(&fields.holder[12..], &holder20[..]);
    // asset: same convention for the token contract address.
    let token20 = h20(weth::TOKEN);
    assert_eq!(&fields.asset[..12], &[0u8; 12]);
    assert_eq!(&fields.asset[12..], &token20[..]);
    // The helper agrees with the field-level assertion.
    assert_eq!(fields.holder, pad_address_32(&holder20));
    assert_eq!(fields.asset, pad_address_32(&token20));

    assert_eq!(
        Uint256::from(fields.amount),
        u256(weth::EXPECTED_BALANCE_HEX)
    );
    assert_eq!(fields.snapshot, weth::BLOCK_NUMBER);
}

/// REJECT: a U256 balance above u128::MAX REFUSES with a typed error — it is NEVER
/// truncated into a small `amount`.
#[test]
fn balance_above_u128_max_refuses_never_truncates() {
    let mut holding = structure_only_holding();
    let over = Uint256::from(u128::MAX) + Uint256::from(1u8);
    holding.balance = over;
    assert_eq!(
        holding.to_foreign_fields(),
        Err(ForeignFieldsError::AmountOverflowsU128 { balance: over })
    );

    // And the worst case: U256::MAX must also refuse (a truncation bug would map it
    // to u128::MAX or wrap it small).
    holding.balance = Uint256::MAX;
    assert_eq!(
        holding.to_foreign_fields(),
        Err(ForeignFieldsError::AmountOverflowsU128 {
            balance: Uint256::MAX
        })
    );
}

/// BOUNDARY: exactly u128::MAX still converts (the refusal starts one above).
#[test]
fn balance_exactly_u128_max_converts() {
    let mut holding = structure_only_holding();
    holding.balance = Uint256::from(u128::MAX);
    let fields = holding.to_foreign_fields().expect("u128::MAX fits");
    assert_eq!(fields.amount, u128::MAX);
}

/// REJECT polarity of the trust edge: a structure-only holding (bare caller-asserted
/// root) converts to `consensus_proven: false` — it grants ZERO weight downstream.
#[test]
fn structure_only_holding_yields_consensus_proven_false() {
    let holding = structure_only_holding();
    assert_eq!(holding.trust, HoldingTrust::StructureOnly);
    assert!(!holding.is_consensus_proven());
    let fields = holding.to_foreign_fields().expect("converts");
    assert!(
        !fields.consensus_proven,
        "a structure-only holding must NEVER convert to consensus_proven=true"
    );
}

/// ACCEPT polarity of the trust edge: the consensus-anchored path (state root taken
/// from the light client's FinalizedExecution, never the caller's claim) mints
/// ConsensusProven and converts to `consensus_proven: true`.
#[test]
fn finalized_path_yields_consensus_proven_true() {
    let holding = verify_erc20_holding_finalized(
        &finalized_at_fixture_root(),
        &nodes(weth::ACCOUNT_PROOF),
        &nodes(weth::STORAGE_PROOF),
        h20(weth::TOKEN),
        h20(weth::HOLDER),
        weth::BALANCES_SLOT,
        &account_claim(),
        u256(weth::EXPECTED_BALANCE_HEX),
    )
    .expect("the fixture proof must verify against its own finalized root");

    assert_eq!(holding.trust, HoldingTrust::ConsensusProven);
    assert!(holding.is_consensus_proven());
    assert_eq!(holding.block_number, weth::BLOCK_NUMBER);
    assert_eq!(holding.state_root, h32(weth::STATE_ROOT));

    let fields = holding.to_foreign_fields().expect("converts");
    assert!(fields.consensus_proven);
    assert_eq!(fields.snapshot, weth::BLOCK_NUMBER);
}

/// REJECT: the finalized path is fail-closed too — a FinalizedExecution whose state
/// root the account proof does not commit to refuses (no ConsensusProven minting off
/// a mismatched anchor).
#[test]
fn finalized_path_wrong_root_rejects() {
    let mut finalized = finalized_at_fixture_root();
    finalized.execution_state_root[0] ^= 0x01;
    let r = verify_erc20_holding_finalized(
        &finalized,
        &nodes(weth::ACCOUNT_PROOF),
        &nodes(weth::STORAGE_PROOF),
        h20(weth::TOKEN),
        h20(weth::HOLDER),
        weth::BALANCES_SLOT,
        &account_claim(),
        u256(weth::EXPECTED_BALANCE_HEX),
    );
    assert!(r.is_err(), "a mismatched finalized root must fail closed");
}
