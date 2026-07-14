//! [`TreasuryView`] — the NON-CUSTODIAL multichain treasury view.
//!
//! The [`Treasury`](crate::treasury::Treasury) is the operator's Solana-only accounting
//! object (fuel + pile). But the treasury's *actual* value lives on more than one chain:
//! USDC on Base, `$DREGG` on Solana, a denom on a Cosmos hub. There is already a whole
//! non-custodial machinery that PROVES what an account holds on a foreign chain — the
//! per-chain light clients (`eth-lightclient` / `cosmos-lightclient` / the Solana bridge)
//! render a [`ProvenForeignHolding`] fact, and `dregg-interchain-gov` compiles all three
//! lanes into one. Governance points those facts at *voters'* addresses to weight a vote.
//!
//! This view points the SAME facts at the TREASURY's own addresses, so the treasury can
//! state — trustlessly, with a real consensus proof behind every number — "we provably
//! hold X USDC on Base, Y `$DREGG` on Solana, Z on Cosmos". It is a **view, not a mover**:
//! nothing is escrowed, wrapped, or transferred. No new custody. A holding is COUNTED only
//! when the fact binds to an address the treasury declared it owns, for the asset it
//! declared, on the chain it declared — and only when a real consensus proof backs it.
//! Anything else (a fact for someone else's address, a chain the treasury does not track,
//! a structure-only RPC echo) is REJECTED, never counted.
//!
//! ```no_run
//! # use dregg_pay::multichain::{TreasuryView, TreasurySlot};
//! # use dregg_governance::proven_foreign_holding::{ChainId, ProvenForeignHolding};
//! let view = TreasuryView::new(vec![
//!     TreasurySlot::new(ChainId::BASE, [0x11; 32], [0xAA; 32], "USDC on Base"),
//!     TreasurySlot::new(ChainId::Solana, [0x22; 32], [0xBB; 32], "$DREGG on Solana"),
//! ]);
//! // `facts` come from the light clients (via dregg-interchain-gov), pointed at the
//! // treasury's addresses. `held.total_amount()` is the proven cross-chain total.
//! # let facts: Vec<ProvenForeignHolding> = vec![];
//! let held = view.proven_holdings(&facts);
//! ```

use std::collections::HashSet;

use dregg_governance::proven_foreign_holding::{ChainId, ProvenForeignHolding};

/// One tracked treasury position: the treasury holds `asset` at its own `address` on
/// `chain`. A [`ProvenForeignHolding`] fact is counted against this slot only when its
/// `chain`, `holder`, and `asset` all match — the trustless binding "this is OUR balance
/// of OUR asset on OUR address", not someone else's.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TreasurySlot {
    /// The chain this position lives on (Solana / an EVM network / a Cosmos network).
    pub chain: ChainId,
    /// The treasury's OWN address on `chain` (32-byte, chain-scoped: a Solana wallet
    /// pubkey, or a left-zero-padded 20-byte EVM/Cosmos address — the same convention
    /// [`ProvenForeignHolding::holder`] uses).
    pub address: [u8; 32],
    /// The asset held at this position (the SPL mint on Solana, the padded token
    /// address on EVM, the denom commitment on Cosmos — matching
    /// [`ProvenForeignHolding::asset`]).
    pub asset: [u8; 32],
    /// A human label for statements/telemetry, e.g. `"USDC on Base"`.
    pub label: String,
}

impl TreasurySlot {
    /// Declare a tracked position.
    pub fn new(
        chain: ChainId,
        address: [u8; 32],
        asset: [u8; 32],
        label: impl Into<String>,
    ) -> Self {
        TreasurySlot {
            chain,
            address,
            asset,
            label: label.into(),
        }
    }

    /// Does `fact` bind to THIS position — same chain, same (our) address, same asset?
    fn matches(&self, fact: &ProvenForeignHolding) -> bool {
        self.chain == fact.chain && self.address == fact.holder && self.asset == fact.asset
    }
}

/// Why a [`ProvenForeignHolding`] fact was NOT counted toward the treasury's holdings.
/// Every variant is fail-closed: a rejected fact contributes ZERO to the total, exactly
/// like the Nomad-law verdict the governance weight path enforces.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HoldingRejection {
    /// The treasury tracks no position on this fact's chain — an untracked (or wrong)
    /// chain. Counting it would attribute a foreign balance to a treasury that never
    /// declared holdings there.
    UntrackedChain,
    /// The treasury tracks this chain, but no declared position matches the fact's
    /// (address, asset) pair: the fact proves that SOMEONE ELSE'S address — or the
    /// treasury's address for an asset the treasury does not track here — holds a
    /// balance. A forged/mismatched holding: refused.
    NotOurPosition,
    /// The fact matches a declared position but carries no real consensus proof
    /// (`consensus_proven == false` — a structure-only RPC echo). Fail closed: the
    /// treasury states only PROVEN balances.
    Unproven,
    /// The exact same (chain, holder, asset) fact was already counted in this view — a
    /// duplicate presentation. Counted once (its [`nullifier_key`] deduplicates), so a
    /// re-presented proof cannot inflate the total.
    ///
    /// [`nullifier_key`]: ProvenForeignHolding::nullifier_key
    AlreadyCounted,
}

impl std::fmt::Display for HoldingRejection {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            HoldingRejection::UntrackedChain => "chain not tracked by this treasury",
            HoldingRejection::NotOurPosition => {
                "holding is not the treasury's declared (address, asset) position"
            }
            HoldingRejection::Unproven => "no consensus proof backs this holding (fail closed)",
            HoldingRejection::AlreadyCounted => "duplicate holding — counted once",
        };
        f.write_str(s)
    }
}

/// A single COUNTED position: the treasury provably holds `amount` atomic units of
/// `asset` at `address` on `chain`, proven at `snapshot`, backed by a real consensus
/// proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProvenChainHolding {
    /// The chain this proven balance lives on.
    pub chain: ChainId,
    /// The treasury's address the balance was proven at.
    pub address: [u8; 32],
    /// The asset held.
    pub asset: [u8; 32],
    /// The proven balance, atomic units.
    pub amount: u128,
    /// The finalized snapshot (slot / block / height) it was proven at.
    pub snapshot: u64,
    /// The declaring slot's label.
    pub label: String,
}

/// A rejected fact and the reason it was not counted (for observability / auditing a
/// statement).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RejectedHolding {
    /// The fact that was refused.
    pub fact: ProvenForeignHolding,
    /// Why.
    pub reason: HoldingRejection,
}

/// The result of ingesting cross-chain proof-of-holdings facts: the treasury's PROVEN
/// per-chain holdings plus the rejected facts. The trustless cross-chain treasury
/// statement.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MultichainHoldings {
    /// The counted positions, one per matched+proven fact.
    pub holdings: Vec<ProvenChainHolding>,
    /// The facts that were refused, with reasons.
    pub rejected: Vec<RejectedHolding>,
}

impl MultichainHoldings {
    /// The raw atomic sum of every proven per-chain holding. NOTE: this is a raw atomic
    /// sum across (possibly) different assets/decimals — it is the count the treasury
    /// proved, not a USD valuation (that needs per-asset decimals × an oracle, which is
    /// a pricing concern, not this view's). Use [`amount_on`](Self::amount_on) /
    /// [`amount_of`](Self::amount_of) for a single asset's honest total.
    pub fn total_amount(&self) -> u128 {
        self.holdings.iter().map(|h| h.amount).sum()
    }

    /// The number of distinct chains the treasury proved a holding on.
    pub fn chains_proven(&self) -> usize {
        self.holdings
            .iter()
            .map(|h| h.chain)
            .collect::<HashSet<_>>()
            .len()
    }

    /// The total proven atomic balance on a single chain (across all its counted assets).
    pub fn amount_on(&self, chain: ChainId) -> u128 {
        self.holdings
            .iter()
            .filter(|h| h.chain == chain)
            .map(|h| h.amount)
            .sum()
    }

    /// The total proven atomic balance of a single (chain, asset) position.
    pub fn amount_of(&self, chain: ChainId, asset: &[u8; 32]) -> u128 {
        self.holdings
            .iter()
            .filter(|h| h.chain == chain && &h.asset == asset)
            .map(|h| h.amount)
            .sum()
    }

    /// True iff at least one holding was proven (a non-vacuous statement).
    pub fn is_non_empty(&self) -> bool {
        !self.holdings.is_empty()
    }
}

/// The non-custodial multichain treasury view: a set of declared per-chain positions,
/// against which cross-chain proof-of-holdings facts are bound and counted.
#[derive(Clone, Debug)]
pub struct TreasuryView {
    slots: Vec<TreasurySlot>,
}

impl TreasuryView {
    /// A view over the treasury's declared positions (its addresses + assets per chain).
    pub fn new(slots: Vec<TreasurySlot>) -> Self {
        TreasuryView { slots }
    }

    /// The declared positions.
    pub fn slots(&self) -> &[TreasurySlot] {
        &self.slots
    }

    /// Ingest cross-chain proof-of-holdings facts (each a [`ProvenForeignHolding`] the
    /// light clients rendered, pointed at the treasury's addresses) and produce the
    /// proven cross-chain treasury statement.
    ///
    /// A fact is COUNTED iff it binds to a declared position (same chain, same treasury
    /// address, same asset) AND carries a real consensus proof AND has not already been
    /// counted in this call. Everything else is rejected, fail-closed, with a reason:
    ///
    /// - a fact on a chain the treasury does not track → [`HoldingRejection::UntrackedChain`];
    /// - a fact for a non-treasury address, or the treasury's address but an asset it
    ///   does not track here → [`HoldingRejection::NotOurPosition`] (the forged/mismatched
    ///   case);
    /// - a matched position with no consensus proof → [`HoldingRejection::Unproven`];
    /// - the same (chain, holder, asset) presented twice → counted once, the rest
    ///   [`HoldingRejection::AlreadyCounted`].
    ///
    /// The result's [`total_amount`](MultichainHoldings::total_amount) is exactly the sum
    /// of the counted per-chain holdings.
    pub fn proven_holdings(&self, facts: &[ProvenForeignHolding]) -> MultichainHoldings {
        let mut out = MultichainHoldings::default();
        let mut seen: HashSet<[u8; 32]> = HashSet::new();

        for fact in facts {
            // Find a declared position this fact binds to.
            let matched = self.slots.iter().find(|s| s.matches(fact));
            let Some(slot) = matched else {
                // No exact match. Distinguish "we don't track this chain at all" from
                // "we track this chain but this isn't our position" so a forged holder /
                // untracked asset is legible.
                let reason = if self.slots.iter().any(|s| s.chain == fact.chain) {
                    HoldingRejection::NotOurPosition
                } else {
                    HoldingRejection::UntrackedChain
                };
                out.rejected.push(RejectedHolding {
                    fact: *fact,
                    reason,
                });
                continue;
            };

            // Fail closed on an unproven fact even for our own position.
            if !fact.is_consensus_proven() {
                out.rejected.push(RejectedHolding {
                    fact: *fact,
                    reason: HoldingRejection::Unproven,
                });
                continue;
            }

            // Deduplicate: the same proven (chain, holder, asset) counts once. A
            // re-presented proof cannot inflate the total (Nomad-law, mirrors the
            // governance nullifier).
            if !seen.insert(fact.nullifier_key()) {
                out.rejected.push(RejectedHolding {
                    fact: *fact,
                    reason: HoldingRejection::AlreadyCounted,
                });
                continue;
            }

            out.holdings.push(ProvenChainHolding {
                chain: fact.chain,
                address: fact.holder,
                asset: fact.asset,
                amount: fact.amount,
                snapshot: fact.snapshot,
                label: slot.label.clone(),
            });
        }

        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Distinct fixture addresses/assets — NEVER real mainnet values.
    const BASE_TREASURY: [u8; 32] = [0x11; 32];
    const SOLANA_TREASURY: [u8; 32] = [0x22; 32];
    const COSMOS_TREASURY: [u8; 32] = [0x33; 32];
    const USDC_ON_BASE: [u8; 32] = [0xAA; 32];
    const DREGG_ON_SOLANA: [u8; 32] = [0xBB; 32];
    const DENOM_ON_COSMOS: [u8; 32] = [0xCC; 32];

    fn view() -> TreasuryView {
        TreasuryView::new(vec![
            TreasurySlot::new(ChainId::BASE, BASE_TREASURY, USDC_ON_BASE, "USDC on Base"),
            TreasurySlot::new(
                ChainId::Solana,
                SOLANA_TREASURY,
                DREGG_ON_SOLANA,
                "$DREGG on Solana",
            ),
            TreasurySlot::new(
                ChainId::cosmos("cosmoshub-4"),
                COSMOS_TREASURY,
                DENOM_ON_COSMOS,
                "ATOM on Cosmos Hub",
            ),
        ])
    }

    fn fact(
        chain: ChainId,
        holder: [u8; 32],
        asset: [u8; 32],
        amount: u128,
        consensus_proven: bool,
    ) -> ProvenForeignHolding {
        ProvenForeignHolding {
            chain,
            holder,
            asset,
            amount,
            snapshot: 100,
            consensus_proven,
        }
    }

    #[test]
    fn proven_facts_for_our_addresses_are_counted_and_summed() {
        // Honest facts on >=2 chains, each pointed at the treasury's OWN address.
        let facts = vec![
            fact(ChainId::BASE, BASE_TREASURY, USDC_ON_BASE, 5_000_000, true),
            fact(
                ChainId::Solana,
                SOLANA_TREASURY,
                DREGG_ON_SOLANA,
                900_000_000,
                true,
            ),
            fact(
                ChainId::cosmos("cosmoshub-4"),
                COSMOS_TREASURY,
                DENOM_ON_COSMOS,
                42_000_000,
                true,
            ),
        ];
        let held = view().proven_holdings(&facts);

        // Non-vacuous: every honest fact is counted.
        assert_eq!(held.holdings.len(), 3);
        assert!(held.rejected.is_empty());
        assert!(held.is_non_empty());
        assert_eq!(held.chains_proven(), 3);

        // Per-chain proven balances.
        assert_eq!(held.amount_on(ChainId::BASE), 5_000_000);
        assert_eq!(held.amount_on(ChainId::Solana), 900_000_000);
        assert_eq!(held.amount_on(ChainId::cosmos("cosmoshub-4")), 42_000_000);

        // The total is EXACTLY the sum of the proven per-chain holdings.
        assert_eq!(held.total_amount(), 5_000_000 + 900_000_000 + 42_000_000);
    }

    #[test]
    fn a_holding_for_a_wrong_address_is_rejected() {
        // A fact that proves SOMEONE ELSE holds USDC on Base — not the treasury. Forged
        // from the treasury's point of view: refused, not counted.
        let attacker = [0xEE; 32];
        let facts = vec![fact(ChainId::BASE, attacker, USDC_ON_BASE, 9_999_999, true)];
        let held = view().proven_holdings(&facts);
        assert!(held.holdings.is_empty(), "not our address → not counted");
        assert_eq!(held.total_amount(), 0);
        assert_eq!(held.rejected.len(), 1);
        assert_eq!(held.rejected[0].reason, HoldingRejection::NotOurPosition);
    }

    #[test]
    fn a_holding_on_an_untracked_chain_is_rejected() {
        // A fact on Ethereum — the treasury declared positions on Base/Solana/Cosmos
        // only. Even for an amount and a plausible address, an untracked chain is refused.
        let facts = vec![fact(
            ChainId::ETHEREUM,
            BASE_TREASURY,
            USDC_ON_BASE,
            1_000_000,
            true,
        )];
        let held = view().proven_holdings(&facts);
        assert!(held.holdings.is_empty());
        assert_eq!(held.rejected.len(), 1);
        assert_eq!(held.rejected[0].reason, HoldingRejection::UntrackedChain);
    }

    #[test]
    fn a_wrong_chain_tag_holding_cannot_bind_to_our_position() {
        // "Wrong chain_tag": the treasury holds USDC at BASE_TREASURY on Base. A fact
        // carrying the SAME address+asset but stamped Cosmos (a different family) can
        // never match the Base slot — it is bound to the wrong chain and refused. (The
        // fact itself is internally tag-consistent: `ProvenForeignHolding` cannot even be
        // constructed with a `chain` whose family byte disagrees — see
        // `from_foreign_fields`. So the only way a wrong-tag holding reaches the view is
        // as a wrong-CHAIN fact, which does not bind.)
        let facts = vec![fact(
            ChainId::cosmos("cosmoshub-4"),
            BASE_TREASURY, // the treasury's BASE address, but presented under Cosmos
            USDC_ON_BASE,
            7_777,
            true,
        )];
        let held = view().proven_holdings(&facts);
        assert!(
            held.holdings.is_empty(),
            "wrong chain family → does not bind"
        );
        assert_eq!(held.rejected.len(), 1);
        // It lands on the Cosmos slot's chain, but neither address nor asset match that
        // slot → NotOurPosition (a Cosmos chain IS tracked, just not this position).
        assert_eq!(held.rejected[0].reason, HoldingRejection::NotOurPosition);
    }

    #[test]
    fn an_unproven_holding_for_our_address_is_rejected_fail_closed() {
        // Our address, our asset, our chain — but a structure-only RPC echo
        // (consensus_proven == false). Fail closed: the treasury states only PROVEN
        // balances.
        let facts = vec![fact(
            ChainId::BASE,
            BASE_TREASURY,
            USDC_ON_BASE,
            5_000_000,
            false,
        )];
        let held = view().proven_holdings(&facts);
        assert!(held.holdings.is_empty());
        assert_eq!(held.rejected.len(), 1);
        assert_eq!(held.rejected[0].reason, HoldingRejection::Unproven);
    }

    #[test]
    fn a_wrong_asset_at_our_address_is_rejected() {
        // The treasury's Base address, but an asset it does not track there (a random
        // airdropped token). Not the position the treasury declared → refused.
        let junk_token = [0x77; 32];
        let facts = vec![fact(ChainId::BASE, BASE_TREASURY, junk_token, 1, true)];
        let held = view().proven_holdings(&facts);
        assert!(held.holdings.is_empty());
        assert_eq!(held.rejected[0].reason, HoldingRejection::NotOurPosition);
    }

    #[test]
    fn a_re_presented_proof_is_counted_once() {
        // The same proven holding presented twice must not inflate the total.
        let f = fact(ChainId::BASE, BASE_TREASURY, USDC_ON_BASE, 5_000_000, true);
        let held = view().proven_holdings(&[f, f]);
        assert_eq!(held.holdings.len(), 1, "counted once");
        assert_eq!(held.total_amount(), 5_000_000, "no inflation");
        assert_eq!(held.rejected.len(), 1);
        assert_eq!(held.rejected[0].reason, HoldingRejection::AlreadyCounted);
    }

    #[test]
    fn honest_and_forged_facts_mixed_counts_only_the_honest() {
        // A realistic batch: two honest treasury holdings + one attacker fact + one
        // untracked chain. Only the honest two count; the total is their sum.
        let attacker = [0xEE; 32];
        let facts = vec![
            fact(ChainId::BASE, BASE_TREASURY, USDC_ON_BASE, 3_000_000, true),
            fact(ChainId::BASE, attacker, USDC_ON_BASE, 1_000_000_000, true), // forged
            fact(
                ChainId::Solana,
                SOLANA_TREASURY,
                DREGG_ON_SOLANA,
                4_000_000,
                true,
            ),
            fact(ChainId::ETHEREUM, BASE_TREASURY, USDC_ON_BASE, 500, true), // untracked
        ];
        let held = view().proven_holdings(&facts);
        assert_eq!(held.holdings.len(), 2);
        assert_eq!(held.total_amount(), 3_000_000 + 4_000_000);
        assert_eq!(held.rejected.len(), 2);
    }
}
