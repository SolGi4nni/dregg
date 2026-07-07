//! The **fund** — the trade loop that cannot lie about what it did.
//!
//! Each [`Fund::step`]:
//!  1. gathers the mandate's assets at ATTESTED prices (a [`MarketView`]);
//!  2. asks the [`Brain`] for a decision, and turns that decision into an ATTESTED turn
//!     (`deos-hermes::AttestationCarrier::attest_turn`) — the model reasoned from real,
//!     injection-free market data;
//!  3. enforces the mandate as CAPS: a disallowed asset or an over-position fill is REFUSED
//!     before any state change (not a soft check);
//!  4. verifies the chosen price's zkOracle attestation and SIMULATES a fill at that attested
//!     price — drawing the bounded budget down; an over-budget draw is REFUSED;
//!  5. commits the trade as an on-ledger R2 turn on a real [`LocalNode`], binding a receipt
//!     that folds the decision attestation + the price attestation + the fill.
//!
//! The on-ledger binding rides a HASH-CHAIN accumulator: turn `k` witnesses
//! `acc_k = H(acc_{k-1} ‖ decision_commit ‖ price_commit ‖ fill)` at `grain-turn::ATTESTATION_SLOT`.
//! The single readable final slot therefore commits to the WHOLE ordered trade sequence, so a
//! third party recomputing `acc` from the published records and comparing to the on-ledger
//! witness catches any forged, altered, dropped, reordered, or backdated trade.
//!
//! ⚑ PAPER-ONLY. `simulate_fill` moves numbers in this process. There is NO exchange order,
//!   no custody, no real money anywhere in this file or its dependencies' paths reached here.

use agent_platform::{LocalNode, NodeMinter};
use deos_hermes::{AnthropicConfig, AttestationCarrier, ProveError, attestation_commitment};
use dregg_agent::agent::GrainTurnMinter;
use dregg_node_target::{NodeTarget, SubmittedTurn};

use crate::brain::{Brain, Decision, MarketView, Side};
use crate::mandate::{Mandate, MandateViolation};
use crate::oracle::{
    AttestedPrice, EndpointConfig, PriceError, PriceOracle, ZkPriceError, verify_attested_price,
};

/// Domain separator for the trade-commitment hash chain.
const TRADE_COMMIT_DOMAIN: &[u8] = b"auditable-fund-trade-commitment-chain-v1";

/// **The trade-commitment fold** — `acc' = H(domain ‖ prev ‖ decision_commit ‖ price_commit ‖
/// side ‖ asset ‖ qty ‖ price ‖ cash_after ‖ position_after)`. Order-sensitive and total: any
/// change to any trade (or its order) changes every subsequent `acc`. Shared verbatim by the
/// fund (to bind) and the audit (to recompute), so the on-ledger witness and the recomputation
/// agree iff the published record set is exactly the one that was minted.
pub(crate) fn fold_commitment(
    prev: [u8; 32],
    decision_commit: [u8; 32],
    price_commit: Option<[u8; 32]>,
    side: Side,
    asset: &str,
    qty: i64,
    price: i64,
    cash_after: i64,
    position_after: i64,
) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(TRADE_COMMIT_DOMAIN);
    h.update(&prev);
    h.update(&decision_commit);
    match price_commit {
        Some(c) => {
            h.update(&[1u8]);
            h.update(&c);
        }
        None => {
            h.update(&[0u8]);
        }
    }
    h.update(&[side.tag()]);
    h.update(&(asset.len() as u64).to_le_bytes());
    h.update(asset.as_bytes());
    h.update(&qty.to_le_bytes());
    h.update(&price.to_le_bytes());
    h.update(&cash_after.to_le_bytes());
    h.update(&position_after.to_le_bytes());
    *h.finalize().as_bytes()
}

/// One committed decision — the auditable unit of the fund's track record. Every field is
/// re-derivable / re-verifiable by a third party: the decision & price attestations verify,
/// the fill re-derives against the running book, and `commit_after` recomputes.
#[derive(Clone, Debug)]
pub struct TradeRecord {
    /// 1-based sequence number.
    pub seq: u64,
    /// Buy / sell / hold.
    pub side: Side,
    /// The asset (empty for a hold).
    pub asset: String,
    /// Units traded (0 for a hold).
    pub qty: i64,
    /// The attested price the fill executed at (0 for a hold).
    pub price: i64,
    /// Cash after this fill.
    pub cash_after: i64,
    /// Position in `asset` after this fill.
    pub position_after: i64,
    /// The exact injection-free field the decision attestation bound (the model's words).
    pub decision_text: String,
    /// The decision's zkOracle attestation (authentic ∧ well-formed ∧ injection-free turn).
    pub decision_att: deos_hermes::ZkOracleAttestation,
    /// The attested price used for the fill (`None` for a hold).
    pub price_att: Option<AttestedPrice>,
    /// The on-ledger turn hash this decision landed as (a member of the node's finalized log).
    pub turn_hash: [u8; 32],
    /// The trade-commitment accumulator AFTER folding this record (the on-ledger witness for
    /// the LAST record).
    pub commit_after: [u8; 32],
}

/// The fund's exportable, third-party-auditable track record: the mandate, the ordered
/// decision records, the live finalized [`LocalNode`] (the light-client-verifiable ledger),
/// and the on-ledger trade-commitment witness read off that ledger.
#[derive(Clone)]
pub struct TrackRecord {
    /// The node domain.
    pub domain: String,
    /// The mandate the fund traded under.
    pub mandate: Mandate,
    /// The ordered per-decision records.
    pub records: Vec<TradeRecord>,
    /// The finalized ledger — a third party runs `node.verify()` (light-client) and
    /// `node.contains(turn_hash)` (membership) against it, trusting no operator.
    pub node: LocalNode,
    /// The trade-commitment accumulator WITNESSED on the finalized ledger's
    /// `ATTESTATION_SLOT` (read via `NodeMinter::attestation_slot`). The audit recomputes the
    /// fold over `records` and refuses any mismatch.
    pub on_ledger_commitment: Option<[u8; 32]>,
}

/// The auditable fund. Holds the mandate-as-caps, the decision attestation carrier, the pinned
/// oracle anchor it trusts, the on-ledger node + minter, and the simulated book.
pub struct Fund {
    mandate: Mandate,
    carrier: AttestationCarrier,
    oracle_config: EndpointConfig,
    node: LocalNode,
    minter: NodeMinter,
    cash: i64,
    positions: std::collections::BTreeMap<String, i64>,
    acc: [u8; 32],
    seq: u64,
    records: Vec<TradeRecord>,
    /// Where each landed trade turn ALSO routes. [`NodeTarget::Local`] (default) keeps the
    /// track record on this in-process [`LocalNode`]; [`NodeTarget::Federation`] additionally
    /// submits each landed trade turn to a real `DREGG_NODE_URL` node and confirms it landed.
    node_target: NodeTarget,
}

impl Fund {
    /// Open a fund on a fresh node under `mandate`. `decision_seed` derives the fund's
    /// decision attestation notary; `oracle_config` is the notary anchor of the price oracle
    /// the fund trusts (its public key — the fund fills only at prices attested under it). The
    /// node minter is admitted under a rate-`max_turns` `ToolGrant`, so the executor refuses
    /// the (max_turns+1)-th on-ledger turn host-side.
    pub fn open(
        domain: &str,
        mandate: Mandate,
        decision_seed: &[u8; 32],
        oracle_config: EndpointConfig,
    ) -> Result<Fund, FundError> {
        let node = LocalNode::new(domain);
        let minter = NodeMinter::open(node.clone(), mandate.max_turns)
            .map_err(|e| FundError::Ledger(format!("open node minter: {e:?}")))?;
        let carrier = AttestationCarrier::from_seed(decision_seed);
        let cash = mandate.budget;
        Ok(Fund {
            mandate,
            carrier,
            oracle_config,
            node,
            minter,
            cash,
            positions: std::collections::BTreeMap::new(),
            acc: [0u8; 32],
            seq: 0,
            records: Vec::new(),
            node_target: NodeTarget::Local,
        })
    }

    /// **Make this fund federation-capable.** By default the fund runs `Local` (the track
    /// record lives on the in-process [`LocalNode`] only). Pass a [`NodeTarget::Federation`]
    /// (e.g. from [`NodeTarget::from_env`], reading `DREGG_NODE_URL`) to ALSO submit each
    /// landed trade turn to a real federation node and confirm it landed — one flip from
    /// replicating the record onto a live federation.
    pub fn with_node_target(mut self, target: NodeTarget) -> Self {
        self.node_target = target;
        self
    }

    /// The pinned anchor of THIS fund's decision attestations — a verifier checks each
    /// record's `decision_att` against it. (Public; the fund's decision-notary key.)
    pub fn decision_config(&self) -> &AnthropicConfig {
        self.carrier.config()
    }

    /// Current cash (drawn down by buys, released by sells).
    pub fn cash(&self) -> i64 {
        self.cash
    }

    /// Current position in `asset`.
    pub fn position(&self, asset: &str) -> i64 {
        *self.positions.get(asset).unwrap_or(&0)
    }

    /// The finalized node (the verifiable ledger).
    pub fn node(&self) -> LocalNode {
        self.node.clone()
    }

    /// The trade-commitment currently witnessed on the finalized ledger's `ATTESTATION_SLOT`.
    pub fn on_ledger_commitment(&self) -> Option<[u8; 32]> {
        self.minter.attestation_slot()
    }

    /// **One trade turn.** Gather attested prices → decide → attest the decision → enforce the
    /// mandate caps → verify the price + simulate the fill (draw the bounded budget) → land the
    /// trade as an on-ledger R2 turn bound to the decision + price + fill. Returns the landed
    /// turn's outcome, or a [`FundError`] (in which case NO turn landed and the fund's state is
    /// unchanged — the cap gate refused).
    pub fn step(
        &mut self,
        oracle: &impl PriceOracle,
        brain: &mut impl Brain,
    ) -> Result<StepOutcome, FundError> {
        // 1. Gather the mandate's assets at attested prices.
        let mut prices = std::collections::BTreeMap::new();
        for asset in &self.mandate.allowed_assets {
            let ap = oracle.price(asset).map_err(FundError::Oracle)?;
            prices.insert(asset.clone(), ap);
        }
        let view = MarketView { prices };

        // 2. Decide, and ATTEST the decision (the jailed+attested brain turn — modeled carrier).
        let decision = brain.decide(&view);
        let (decision_att, decision_field) = self
            .carrier
            .attest_turn(&decision.text())
            .map_err(FundError::Attest)?;

        // 3. Enforce the mandate CAPS and compute the prospective fill (all refusals here
        //    happen BEFORE any state mutation or on-ledger turn).
        let (price_att, price, new_cash, new_pos) = self.plan_fill(&decision, &view)?;

        // 4. Fold the trade commitment and BIND it onto the on-ledger turn.
        let decision_commit = attestation_commitment(&decision_att);
        let price_commit = price_att
            .as_ref()
            .map(|ap| attestation_commitment(&ap.attestation));
        let new_acc = fold_commitment(
            self.acc,
            decision_commit,
            price_commit,
            decision.side,
            &decision.asset,
            decision.qty,
            price,
            new_cash,
            new_pos,
        );
        self.minter.bind_attestation(new_acc);

        // 5. Land the trade as a genuine R2 kernel turn on the node. `Err` = the executor
        //    refused host-side (over the rate budget) → nothing mutates, no receipt.
        let turn_hash = self
            .minter
            .mint_turn(&decision.label(), 1, (self.seq as i64) + 1, new_acc)
            .map_err(FundError::Ledger)?;

        // 5b. FEDERATION SEAM: in `Local` mode this is a no-op; in `Federation` mode the
        //     landed trade turn is ALSO submitted to the real node + confirmed landed. A
        //     rejected / unreachable / non-landing submit fails the step fail-closed (the
        //     book is NOT committed below), so a trade that did not replicate is not
        //     recorded as if it had.
        self.node_target
            .route(&SubmittedTurn::new(
                self.node.domain().to_string(),
                turn_hash,
            ))
            .map_err(|e| FundError::Federation(e.to_string()))?;

        // 6. COMMIT the simulated book (only after the turn landed).
        self.cash = new_cash;
        if !matches!(decision.side, Side::Hold) {
            self.positions.insert(decision.asset.clone(), new_pos);
        }
        self.acc = new_acc;
        self.seq += 1;

        let record = TradeRecord {
            seq: self.seq,
            side: decision.side,
            asset: decision.asset.clone(),
            qty: decision.qty,
            price,
            cash_after: new_cash,
            position_after: new_pos,
            decision_text: String::from_utf8_lossy(&decision_field).into_owned(),
            decision_att,
            price_att,
            turn_hash,
            commit_after: new_acc,
        };
        self.records.push(record);

        Ok(StepOutcome {
            seq: self.seq,
            side: decision.side,
            turn_hash,
            cash_after: new_cash,
            position_after: new_pos,
        })
    }

    /// Enforce the mandate caps and verify the price; return the price attestation, fill price,
    /// and prospective post-fill cash + position. Every refusal is a hard cap, not a soft check.
    fn plan_fill(
        &self,
        decision: &Decision,
        view: &MarketView,
    ) -> Result<(Option<AttestedPrice>, i64, i64, i64), FundError> {
        match decision.side {
            // A hold is still an attested, on-ledger turn — but no fill, no draw.
            Side::Hold => Ok((None, 0, self.cash, self.position(&decision.asset))),
            Side::Buy | Side::Sell => {
                // MANDATE CAP: the asset must be allowed.
                if !self.mandate.allows(&decision.asset) {
                    return Err(FundError::Mandate(MandateViolation::AssetNotAllowed(
                        decision.asset.clone(),
                    )));
                }
                // The price MUST be attested and prove the amount (else: unattested-price refusal).
                let ap = view
                    .prices
                    .get(&decision.asset)
                    .cloned()
                    .ok_or_else(|| FundError::NoQuote(decision.asset.clone()))?;
                // Re-verify the attestation and BIND the fill to the notarized amount (in cents).
                let price = verify_attested_price(&ap, &self.oracle_config)
                    .map_err(FundError::UnattestedPrice)?;
                let cur = self.position(&decision.asset);

                match decision.side {
                    Side::Buy => {
                        let new_pos = cur + decision.qty;
                        // MANDATE CAP: position bound.
                        if new_pos.abs() > self.mandate.max_position {
                            return Err(FundError::Mandate(MandateViolation::PositionExceeded {
                                asset: decision.asset.clone(),
                                would: new_pos,
                                max: self.mandate.max_position,
                            }));
                        }
                        let cost = decision.qty.checked_mul(price).ok_or(FundError::Overflow)?;
                        // BUDGET CAP (the bounded lease): a draw the budget cannot cover is refused.
                        if cost > self.cash {
                            return Err(FundError::OverBudget {
                                need: cost,
                                have: self.cash,
                            });
                        }
                        Ok((Some(ap), price, self.cash - cost, new_pos))
                    }
                    Side::Sell => {
                        // No shorting in paper mode: cannot sell more than held.
                        if decision.qty > cur {
                            return Err(FundError::Mandate(
                                MandateViolation::InsufficientPosition {
                                    asset: decision.asset.clone(),
                                    have: cur,
                                    sell: decision.qty,
                                },
                            ));
                        }
                        let new_pos = cur - decision.qty;
                        let proceeds =
                            decision.qty.checked_mul(price).ok_or(FundError::Overflow)?;
                        Ok((Some(ap), price, self.cash + proceeds, new_pos))
                    }
                    Side::Hold => unreachable!(),
                }
            }
        }
    }

    /// Export the third-party-auditable track record: the mandate, the records, the finalized
    /// node, and the on-ledger commitment read off the real ledger.
    pub fn export(&self) -> TrackRecord {
        TrackRecord {
            domain: self.node.domain().to_string(),
            mandate: self.mandate.clone(),
            records: self.records.clone(),
            node: self.node.clone(),
            on_ledger_commitment: self.minter.attestation_slot(),
        }
    }
}

/// The outcome of one landed trade turn.
#[derive(Clone, Copy, Debug)]
pub struct StepOutcome {
    /// The 1-based sequence number of this decision.
    pub seq: u64,
    /// The side taken.
    pub side: Side,
    /// The on-ledger turn hash it landed as.
    pub turn_hash: [u8; 32],
    /// Cash after this turn.
    pub cash_after: i64,
    /// Position after this turn (in the traded asset; unchanged for a hold).
    pub position_after: i64,
}

/// Why a fund step refused. Every variant means NO turn landed and NO state changed.
#[derive(Clone, Debug)]
pub enum FundError {
    /// The price oracle could not quote a mandate asset (unknown asset / bad session).
    Oracle(ZkPriceError),
    /// A gathered market view was missing a quote for a traded asset (internal inconsistency).
    NoQuote(String),
    /// The decision attestation prover refused.
    Attest(ProveError),
    /// A mandate cap was breached (disallowed asset / over-position / oversell).
    Mandate(MandateViolation),
    /// The chosen price is not provably attested (a price the fund cannot prove).
    UnattestedPrice(PriceError),
    /// The bounded budget cannot cover the buy (over-budget lease refusal).
    OverBudget {
        /// The cash the buy needs.
        need: i64,
        /// The cash available.
        have: i64,
    },
    /// The executor refused the on-ledger turn host-side (over the rate budget / insolvent).
    Ledger(String),
    /// A configured [`NodeTarget::Federation`] node refused the landed trade turn or could
    /// not confirm it landed (a rejected / unreachable / non-landing submit). Fail-closed:
    /// the book is NOT committed, so a trade that did not replicate is not recorded.
    Federation(String),
    /// An arithmetic overflow computing a fill (defensive).
    Overflow,
}

impl core::fmt::Display for FundError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            FundError::Oracle(e) => write!(f, "oracle: {e}"),
            FundError::NoQuote(a) => write!(f, "no attested quote gathered for `{a}`"),
            FundError::Attest(e) => write!(f, "decision attestation refused: {e:?}"),
            FundError::Mandate(v) => write!(f, "mandate refused: {v}"),
            FundError::UnattestedPrice(e) => write!(f, "unattested price refused: {e}"),
            FundError::OverBudget { need, have } => {
                write!(f, "over budget: buy needs {need}, only {have} available")
            }
            FundError::Ledger(e) => write!(f, "on-ledger turn refused: {e}"),
            FundError::Federation(e) => write!(f, "federation routing failed: {e}"),
            FundError::Overflow => write!(f, "fill arithmetic overflow"),
        }
    }
}

impl std::error::Error for FundError {}
