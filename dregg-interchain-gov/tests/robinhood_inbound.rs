//! # Robinhood Chain INBOUND — a real tokenized-asset holding proven INTO dregg
//!
//! This is the light-client (inbound) leg for **Robinhood Chain** (chain id 46630, an EVM
//! Arbitrum-Orbit L2 for tokenized stocks/RWA): a REAL `eth_getProof` for holder
//! `0x8b251ADF…`'s **TSLA** (Tesla) tokenized-stock balance on the Robinhood testnet is
//! verified through `eth-lightclient`'s EIP-1186 machinery into a `ProvenErc20Holding`,
//! then joined — through the SAME compiled seam the Ethereum/Base lanes use
//! ([`evm_holding_to_governance`]) — into a dregg-side [`ProvenForeignHolding`] tagged
//! `ChainId::Evm(46630)`. dregg can now reason about the Robinhood-Chain asset as
//! first-class state.
//!
//! Non-custodial: this is a READ proof over the holder's own balance slot in the token
//! contract's storage trie. Nothing is moved, wrapped, or escrowed.
//!
//! ## Trust anchor (honest — the load-bearing grading)
//!
//! * **Now — weak-subjectivity.** The EIP-1186 chain is verified against a Robinhood-Chain
//!   state root **supplied to the verifier** (a checkpointed/recent root). Robinhood Chain
//!   is an Arbitrum-Orbit L2 with **no Altair sync committee**, so the holding mints as
//!   [`HoldingTrust::StructureOnly`] and the governance fact arrives `consensus_proven ==
//!   false` — ZERO governance weight, fail-closed. This is exactly the same rung
//!   `eth-lightclient`'s bare-root `verify_erc20_holding` occupies, applied honestly to an
//!   L2 whose root we trust by subjectivity, not by re-deriving consensus.
//! * **Trustless upgrade (named, NOT built here) — L1 Arbitrum-rollup anchor.** The
//!   trustless rung verifies the L2 state root against its **L1 (Ethereum) rollup anchor**:
//!   the L2 output/state root Robinhood's Orbit chain posts to its L1 rollup contract,
//!   opened with THIS same EIP-1186 account+storage machinery (`verify_evm_account_proof` /
//!   `verify_evm_storage_slot` against a light-client-verified Ethereum L1 state root, à la
//!   the OP-stack `crate::base` output-root anchor). Only that rung earns
//!   `consensus_proven == true`. This test does not claim it.
//!
//! ## Composition (the payoff — sketched, not built)
//!
//! A `ProvenForeignHolding { chain: Evm(46630), asset: TSLA, amount: 5e18, … }` is the
//! dregg-side handle on a Robinhood-Chain tokenized asset. From here it composes onto the
//! existing towers exactly as any proven holding does:
//! - **DrEX cross-margin / provably-solvent lending** — the proven balance is collateral
//!   whose existence is a math fact, not a custodial IOU; the solvency tower sums proven
//!   holdings (per-chain nullifier-scoped, so a Robinhood TSLA holding and an Ethereum one
//!   are distinct facts that both count) against liabilities.
//! - **DrEX tradeable state** — a mandate/turn can reference the holding as owned state and
//!   price against it, with the `consensus_proven` verdict gating how much authority it
//!   carries (weak-subjectivity holdings inform, L1-anchored holdings settle).
//!
//! ACCEPT + REJECT (both polarities) run by default.

#[path = "../../eth-lightclient/tests/fixtures/robinhood_tsla.rs"]
mod tsla;

use dregg_governance::proven_foreign_holding::ChainId;
use dregg_interchain_gov::{evm_holding_to_governance, JoinError};
use eth_lightclient::evm::{
    verify_erc20_holding_wide, AccountClaim, Erc20ProofError, HoldingTrust, ProvenErc20Holding,
    Uint256,
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

/// Verify the REAL Robinhood-testnet TSLA proof into a `ProvenErc20Holding` (the edge
/// output), with `state_root` optionally forged for the reject polarity.
fn prove(state_root: [u8; 32]) -> Result<ProvenErc20Holding, Erc20ProofError> {
    verify_erc20_holding_wide(
        state_root,
        &nodes(tsla::ACCOUNT_PROOF),
        &nodes(tsla::STORAGE_PROOF),
        h20(tsla::TOKEN),
        h20(tsla::HOLDER),
        h32(tsla::BALANCES_BASE_SLOT),
        &account_claim(),
        u256(tsla::EXPECTED_BALANCE_HEX),
        tsla::BLOCK_NUMBER,
    )
}

/// ACCEPT: the real Robinhood-Chain TSLA holding joins into a dregg `ProvenForeignHolding`
/// tagged `Evm(46630)` — the inbound leg, end to end.
#[test]
fn real_robinhood_tsla_holding_joins_into_dregg() {
    let holding = prove(h32(tsla::STATE_ROOT)).expect("real Robinhood TSLA proof verifies");
    assert_eq!(holding.trust, HoldingTrust::StructureOnly);

    let fact = evm_holding_to_governance(&holding, tsla::CHAIN_ID)
        .expect("EVM holding joins into a governance fact");

    // The dregg-side fact names Robinhood Chain specifically (Evm(46630)) — not just
    // "an EVM chain" — so it occupies its own nullifier space.
    assert_eq!(fact.chain, ChainId::Evm(46630));
    assert_eq!(fact.chain, ChainId::Evm(tsla::CHAIN_ID));
    // 5.0 TSLA (5e18 atomic units), the real faucet-dropped balance.
    assert_eq!(fact.amount, 5_000_000_000_000_000_000u128);
    assert_eq!(fact.snapshot, tsla::BLOCK_NUMBER);
    // Holder / asset are the 20-byte address/contract, left-padded into 32.
    assert_eq!(&fact.holder[12..], &h20(tsla::HOLDER));
    assert_eq!(&fact.asset[12..], &h20(tsla::TOKEN));

    // HONEST verdict carried through the whole join: weak-subjectivity → ZERO weight.
    assert!(
        !fact.is_consensus_proven(),
        "an Arbitrum-Orbit L2 root verified by subjectivity is fail-closed to unproven"
    );
}

/// The Robinhood holding gets its OWN per-poll nullifier, distinct from the same holder's
/// same-asset holding on a DIFFERENT EVM network — a holder on Robinhood Chain and on
/// Ethereum are two facts that both count, and neither occupies the other's slot.
#[test]
fn robinhood_nullifier_is_network_scoped() {
    let holding = prove(h32(tsla::STATE_ROOT)).expect("verifies");
    let rh = evm_holding_to_governance(&holding, tsla::CHAIN_ID).expect("joins");

    // Deterministic.
    assert_eq!(rh.nullifier_key(), rh.nullifier_key());

    // Same holder+asset, a different EVM network (Ethereum id 1) → distinct nullifier.
    let on_eth = dregg_governance::proven_foreign_holding::ProvenForeignHolding {
        chain: ChainId::Evm(1),
        ..rh
    };
    assert_ne!(
        rh.nullifier_key(),
        on_eth.nullifier_key(),
        "Robinhood Chain (46630) and Ethereum (1) are distinct consensus domains"
    );
}

/// REJECT (polarity 1): a FORGED Robinhood-Chain state root fails at the EIP-1186 account
/// proof — no `ProvenErc20Holding` is minted, so nothing can join into dregg.
#[test]
fn forged_root_never_produces_a_dregg_fact() {
    let mut sr = h32(tsla::STATE_ROOT);
    sr[0] ^= 0x01;
    assert_eq!(prove(sr), Err(Erc20ProofError::AccountProofInvalid));
}

/// REJECT (polarity 2): the real holding paired with the WRONG network FAMILY (a Cosmos
/// chain) is refused at the join's family gate — the edge produced an EVM family tag, so a
/// relayer naming a non-EVM network cannot mis-attribute the Robinhood asset.
#[test]
fn wrong_network_family_is_refused_at_the_join() {
    let holding = prove(h32(tsla::STATE_ROOT)).expect("verifies");
    let fields = holding.to_foreign_fields().expect("fields");
    // Drive the EVM edge fields down a Cosmos network: the join's family gate refuses.
    let r = dregg_interchain_gov::evm_fields_to_holding(&fields, ChainId::cosmos("cosmoshub-4"));
    assert_eq!(
        r,
        Err(JoinError::WrongNetworkFamily {
            edge_tag: eth_lightclient::evm::CHAIN_TAG_EVM,
            network_family: 2,
        })
    );
}
