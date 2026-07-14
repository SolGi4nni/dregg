//! The non-custodial MULTICHAIN TREASURY VIEW, driven through the REAL join seam.
//!
//! `dregg-interchain-gov` compiles the light-client edges (`eth-lightclient` /
//! `cosmos-lightclient` / the Solana bridge) into one [`ProvenForeignHolding`] fact. The
//! same facts governance points at a VOTER's address, this test points at the TREASURY's
//! own addresses and feeds `dregg_pay::TreasuryView` — so the treasury proves "we hold X
//! USDC on Base, Y on Cosmos" trustlessly, no new custody.
//!
//! This is the thin CONSUMER: the join functions (`evm_fields_to_holding`,
//! `cosmos_fields_to_holding`) are the real cross-chain read seam; the treasury view
//! binds each proven fact to a declared position and sums only the ones that bind.

use dregg_governance::proven_foreign_holding::ChainId;
use dregg_interchain_gov::{cosmos_fields_to_holding, evm_fields_to_holding, JoinError};
use dregg_pay::multichain::{HoldingRejection, TreasurySlot, TreasuryView};

// The treasury's OWN addresses per chain (32-byte, chain-scoped). NEVER real mainnet
// values — throwaway fixtures.
const TREASURY_BASE: [u8; 32] = [0x11; 32];
const TREASURY_COSMOS: [u8; 32] = [0x33; 32];
const USDC_ON_BASE: [u8; 32] = [0xAA; 32];
const ATOM_ON_HUB: [u8; 32] = [0xCC; 32];

fn treasury_view() -> TreasuryView {
    TreasuryView::new(vec![
        TreasurySlot::new(ChainId::BASE, TREASURY_BASE, USDC_ON_BASE, "USDC on Base"),
        TreasurySlot::new(
            ChainId::cosmos("cosmoshub-4"),
            TREASURY_COSMOS,
            ATOM_ON_HUB,
            "ATOM on Cosmos Hub",
        ),
    ])
}

/// The whole path: real EVM + Cosmos edge fields → the join seam → the treasury view.
/// Both are pointed at the treasury's addresses, so both bind and the total is their sum.
#[test]
fn treasury_view_proves_cross_chain_holdings_through_the_join() {
    // A Base (EVM) light-client field set, pointed at the treasury's Base address.
    let base_fields = eth_lightclient::evm::ForeignHoldingFields {
        chain_tag: eth_lightclient::evm::CHAIN_TAG_EVM,
        holder: TREASURY_BASE,
        asset: USDC_ON_BASE,
        amount: 5_000_000, // 5 USDC (6 decimals)
        snapshot: 21_000_000,
        consensus_proven: true,
    };
    let base_holding =
        evm_fields_to_holding(&base_fields, ChainId::BASE).expect("EVM fields join to a fact");

    // A Cosmos Hub field set, pointed at the treasury's Cosmos address.
    let cosmos_fields = cosmos_lightclient::ForeignHoldingFields {
        chain_tag: cosmos_lightclient::COSMOS_CHAIN_TAG,
        holder: TREASURY_COSMOS,
        asset: ATOM_ON_HUB,
        amount: 42_000_000,
        snapshot: 19_500_000,
        consensus_proven: true,
    };
    let cosmos_holding = cosmos_fields_to_holding(&cosmos_fields, "cosmoshub-4")
        .expect("Cosmos fields join to a fact");

    let held = treasury_view().proven_holdings(&[base_holding, cosmos_holding]);

    // Non-vacuous: both proven facts are counted, on 2 distinct chains.
    assert_eq!(held.holdings.len(), 2);
    assert!(held.rejected.is_empty());
    assert_eq!(held.chains_proven(), 2);
    assert_eq!(held.amount_on(ChainId::BASE), 5_000_000);
    assert_eq!(held.amount_on(ChainId::cosmos("cosmoshub-4")), 42_000_000);
    // The total is exactly the sum of the proven per-chain holdings.
    assert_eq!(held.total_amount(), 5_000_000 + 42_000_000);
}

/// A REAL joined fact for someone ELSE's address (not the treasury) is refused by the
/// view — the join succeeds (it is a valid proof of the attacker's balance), but it does
/// not bind to any of the treasury's declared positions.
#[test]
fn a_joined_fact_for_a_foreign_address_is_rejected_by_the_view() {
    let attacker = [0xEE; 32];
    let base_fields = eth_lightclient::evm::ForeignHoldingFields {
        chain_tag: eth_lightclient::evm::CHAIN_TAG_EVM,
        holder: attacker,
        asset: USDC_ON_BASE,
        amount: 9_999_999_999,
        snapshot: 21_000_000,
        consensus_proven: true,
    };
    let holding = evm_fields_to_holding(&base_fields, ChainId::BASE).expect("joins fine");

    let held = treasury_view().proven_holdings(&[holding]);
    assert!(held.holdings.is_empty(), "not the treasury's address");
    assert_eq!(held.total_amount(), 0);
    assert_eq!(held.rejected.len(), 1);
    assert_eq!(held.rejected[0].reason, HoldingRejection::NotOurPosition);
}

/// A wrong CHAIN_TAG never even reaches the treasury view: the join seam's tag tooth
/// (`from_foreign_fields`) refuses to mint a fact whose edge tag disagrees with the
/// supplied network family. This is the "wrong chain_tag rejected" case, caught upstream.
#[test]
fn a_wrong_chain_tag_is_rejected_at_the_join_before_the_view() {
    // A Cosmos edge byte (tag 2) forced down the EVM join with a Base network (family 1).
    let mismatched = eth_lightclient::evm::ForeignHoldingFields {
        chain_tag: cosmos_lightclient::COSMOS_CHAIN_TAG, // 2 — wrong for an EVM network
        holder: TREASURY_BASE,
        asset: USDC_ON_BASE,
        amount: 1,
        snapshot: 1,
        consensus_proven: true,
    };
    let joined = evm_fields_to_holding(&mismatched, ChainId::BASE);
    assert!(
        matches!(joined, Err(JoinError::ChainTag(_))),
        "the join's tag tooth refuses a wrong chain_tag; no fact is minted for the view"
    );
}

/// An unproven (structure-only) joined fact for the treasury's OWN address is refused —
/// the view states only balances a real consensus proof backs. Fail closed.
#[test]
fn an_unproven_joined_fact_is_rejected_fail_closed() {
    let base_fields = eth_lightclient::evm::ForeignHoldingFields {
        chain_tag: eth_lightclient::evm::CHAIN_TAG_EVM,
        holder: TREASURY_BASE,
        asset: USDC_ON_BASE,
        amount: 5_000_000,
        snapshot: 21_000_000,
        consensus_proven: false, // a structure-only RPC echo — carried, never asserted
    };
    let holding = evm_fields_to_holding(&base_fields, ChainId::BASE).expect("joins");
    let held = treasury_view().proven_holdings(&[holding]);
    assert!(held.holdings.is_empty());
    assert_eq!(held.rejected[0].reason, HoldingRejection::Unproven);
}
