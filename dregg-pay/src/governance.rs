//! [`LiquidityGovernance`] — the collective-governed **liquidity vote** that authorizes a
//! pile→fuel swap. The vote is the authorization; a passed vote (and ONLY a passed vote)
//! yields the [`SwapAuthorization`] that [`crate::swap::JupiterSwap::execute`] requires.
//!
//! # The flow: vote → authorize → sign → execute
//!
//! 1. **Propose.** The operator opens a liquidity-event proposal over
//!    [`collective_choice`] — a per-option-gated poll ([`CollectiveChoice::open_poll_gated`])
//!    whose gated option is `APPROVE`, with a holder electorate and a quorum `M`. This is
//!    the SAME quorum engine the bot's `/party` uses (poll → write-once ballots → monotone
//!    tally → the quorum `AffineLe` gate).
//! 2. **Vote.** Each holder casts a single-use ballot (`WriteOnce(VOTE)` + a nullifier —
//!    a double vote is a real executor refusal).
//! 3. **Authorize.** [`LiquidityGovernance::finalize`] resolves the poll. A passed vote
//!    (APPROVE reached quorum) mints a [`SwapAuthorization`] stamped by the operator's
//!    [`GovernanceAuthority`]; a below-quorum vote yields `None` — NO authorization.
//! 4. **Sign + execute.** The operator signs the swap tx and [`crate::swap::JupiterSwap`]
//!    executes against the authorization (see [`crate::swap`]).
//!
//! An unauthorized swap (no authorization) or a failed-quorum vote therefore cannot move
//! the treasury — the refusal is a real quorum gate, not a flag.
//!
//! # Two proposal shapes
//!
//! * **The floored proposal** ([`LiquidityGovernance::propose`]) — one vote per holder in
//!   a fixed electorate, an operator-chosen `amount`, and a `min_out` slippage floor the
//!   swap refuses to fill below.
//! * **The market-price pool proposal** ([`LiquidityGovernance::propose_market_swap`]) —
//!   the shape ember specified. Three differences, each load-bearing:
//!   1. **Quadratic weight over the pool.** A voter's weight is
//!      `isqrt(atomic $DREGG they paid into the pool being swapped)`
//!      ([`quadratic_weight`](crate::pool::quadratic_weight)), read from a
//!      [`PoolSnapshot`] pinned when the proposal opened. Someone who contributed nothing
//!      has weight zero and is refused a ballot. `quorum_m` is therefore a **weight**
//!      quorum, not a headcount.
//!   2. **All or nothing.** The amount is the pool's whole total — not an operator
//!      parameter. There is no partial fill and no per-voter opt-out of a slice.
//!   3. **Market price, slippage accepted.** The minted authorization carries
//!      [`MARKET_MIN_OUT`] (`0`): no floor, so the swap executes at whatever the venue
//!      quotes. The realised slippage is still *measured* — the swap receipt carries the
//!      quoted amount and [`SwapOutcome::slippage_bps`](crate::swap::SwapOutcome) beside
//!      the realised one. Accepting slippage is not the same as not looking at it.

use collective_choice::{
    BallotCap, CollectiveChoice, Decision, PollId, PollSpec, Tally, VoteEngine, VoteError,
};

use crate::config::DepositAddress;
use crate::pool::PoolSnapshot;
use crate::swap::{GovernanceAuthority, SwapAuthorization};

/// The `REJECT` ballot option (index 0).
pub const REJECT_OPTION: usize = 0;
/// The `APPROVE` ballot option (index 1) — the poll is per-option-gated on THIS option,
/// so the decision-turn commits only once APPROVE itself reaches quorum.
pub const APPROVE_OPTION: usize = 1;

/// A liquidity-event proposal: swap `amount` atomic `$DREGG` out of the pile with a
/// `min_out` atomic USDC slippage floor, pending a holder vote at quorum `quorum_m`.
#[derive(Clone, Debug)]
pub struct LiquidityProposal {
    /// The poll the holders vote in.
    pub poll: PollId,
    /// Atomic `$DREGG` the proposal would swap out of the pile.
    pub amount: u64,
    /// The minimum atomic USDC the swap must realize (the authorized slippage floor).
    pub min_out: u64,
    /// The quorum threshold `M` — APPROVE must reach this for the proposal to pass.
    pub quorum_m: u64,
}

/// The `min_out` a **market-price** swap authorization carries: `0` — NO slippage floor.
///
/// ember specified an all-or-nothing swap "at market price accepting whatever slippage",
/// so a market proposal must not mint a floor that could make the authorized swap refuse
/// to fill. With `min_out = 0` the executor's
/// [`SwapError::SlippageExceeded`](crate::swap::SwapError) branch cannot fire and the swap
/// realizes whatever the venue gives. The slippage is still MEASURED and reported on the
/// receipt ([`SwapOutcome::slippage_bps`](crate::swap::SwapOutcome)) — accepted, not
/// unobserved. The floored path ([`LiquidityGovernance::propose`]) is untouched and still
/// mints a real floor.
pub const MARKET_MIN_OUT: u64 = 0;

/// A **market-price, all-or-nothing** liquidity proposal over a pinned contribution pool.
///
/// The pool snapshot is the whole proposal: it fixes WHO may vote and at what quadratic
/// weight, and it fixes the amount (the pool's total — all of it or none of it). Nothing
/// contributed after the pin enters either.
#[derive(Clone, Debug)]
pub struct MarketSwapProposal {
    /// The weighted poll the contributors vote in.
    pub poll: PollId,
    /// The PINNED pool — the electorate, the weights, and the amount.
    pub pool: PoolSnapshot,
    /// The **weight** quorum: `Σ isqrt(contribution)` over APPROVE voters must reach this
    /// for the proposal to pass. An operator parameter, exactly as `quorum_m` is on the
    /// floored path — this module chooses no threshold for the operator.
    pub quorum_weight: u64,
}

impl MarketSwapProposal {
    /// The ALL-OR-NOTHING amount: the pool's entire total, in atomic `$DREGG`.
    pub fn amount(&self) -> u64 {
        self.pool.total()
    }

    /// A contributor's quadratic weight in this proposal — `isqrt` of what they paid into
    /// the pinned pool. Zero for anyone who paid nothing.
    pub fn weight_of(&self, who: &DepositAddress) -> u64 {
        self.pool.weight(who)
    }
}

/// Why a governance action was refused.
#[derive(Clone, Debug)]
pub enum GovernanceError {
    /// The underlying vote engine refused (bad spec, ineligible voter, double vote, an
    /// executor caveat, …).
    Vote(VoteError),
    /// A market-price proposal was opened over an EMPTY pool — nobody has contributed, so
    /// there is nothing to swap and no electorate to swap it. Fail closed: an empty pool
    /// would otherwise mint an authorization for zero at a quorum nobody can reach.
    EmptyPool,
    /// The would-be voter contributed NOTHING to the pinned pool, so their quadratic
    /// weight is `isqrt(0) = 0`. Refused before any ballot exists — a worthless ballot is
    /// never minted, and a non-contributor can never be issued one.
    NoContribution {
        /// The address that holds no share of this pool.
        who: DepositAddress,
    },
}

impl std::fmt::Display for GovernanceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GovernanceError::Vote(e) => write!(f, "liquidity vote refused: {e}"),
            GovernanceError::EmptyPool => {
                write!(f, "liquidity vote refused: the contribution pool is empty")
            }
            GovernanceError::NoContribution { who } => write!(
                f,
                "liquidity vote refused: {who} contributed nothing to this pool (weight 0)"
            ),
        }
    }
}

impl std::error::Error for GovernanceError {}

impl From<VoteError> for GovernanceError {
    fn from(e: VoteError) -> Self {
        GovernanceError::Vote(e)
    }
}

/// The collective-governed liquidity-vote authority. Wraps the [`CollectiveChoice`]
/// quorum engine (the vote) and the operator's [`GovernanceAuthority`] (the attestation
/// that turns a passed vote into a swap-executable [`SwapAuthorization`]). Holds the mint
/// pair so the minted authorization binds them.
pub struct LiquidityGovernance {
    engine: CollectiveChoice,
    authority: GovernanceAuthority,
    dregg_mint: [u8; 32],
    usdc_mint: [u8; 32],
}

impl LiquidityGovernance {
    /// Stand up a liquidity-vote authority: a fresh collective-choice engine under
    /// `federation_id`, the operator's certification `authority`, and the `$DREGG`/USDC
    /// mint pair (from [`PayConfig`](crate::config::PayConfig)) the authorization binds.
    pub fn new(
        federation_id: [u8; 32],
        authority: GovernanceAuthority,
        dregg_mint: [u8; 32],
        usdc_mint: [u8; 32],
    ) -> Self {
        LiquidityGovernance {
            engine: CollectiveChoice::new(federation_id),
            authority,
            dregg_mint,
            usdc_mint,
        }
    }

    /// The governance authority public key — what a [`crate::swap::JupiterSwap`] is
    /// configured with to verify authorizations minted here.
    pub fn authority_public_key(&self) -> [u8; 32] {
        self.authority.public_key()
    }

    /// Open a liquidity-event proposal: a REJECT/APPROVE poll gated on APPROVE, over the
    /// holder `electorate`, at quorum `quorum_m`. Returns the proposal handle voters and
    /// [`LiquidityGovernance::finalize`] operate on.
    pub fn propose(
        &mut self,
        question: impl Into<String>,
        amount: u64,
        min_out: u64,
        electorate: Vec<[u8; 32]>,
        quorum_m: u64,
    ) -> Result<LiquidityProposal, GovernanceError> {
        let spec = PollSpec {
            question: question.into(),
            options: vec!["reject".to_string(), "approve".to_string()],
            electorate,
            quorum_m,
        };
        let poll = self.engine.open_poll_gated(spec, APPROVE_OPTION)?;
        Ok(LiquidityProposal {
            poll,
            amount,
            min_out,
            quorum_m,
        })
    }

    /// Mint (or return) a holder's single-use ballot cap. A voter not in the proposal's
    /// electorate is refused ([`VoteError::Ineligible`]) — holding a cap IS eligibility.
    pub fn issue_ballot(
        &mut self,
        proposal: &LiquidityProposal,
        voter_pk: [u8; 32],
    ) -> Result<BallotCap, GovernanceError> {
        Ok(self.engine.issue_ballot(proposal.poll, voter_pk)?)
    }

    /// Cast one holder's vote — `approve = true` votes APPROVE, `false` votes REJECT. A
    /// double vote on the same ballot is a real refusal (the nullifier / `WriteOnce`).
    pub fn vote(
        &mut self,
        proposal: &LiquidityProposal,
        ballot: &BallotCap,
        approve: bool,
    ) -> Result<(), GovernanceError> {
        let option = if approve {
            APPROVE_OPTION
        } else {
            REJECT_OPTION
        };
        self.engine.cast(proposal.poll, ballot, option)?;
        Ok(())
    }

    /// The live monotone tally (`[reject, approve]`) a light client can recompute.
    pub fn tally(&self, proposal: &LiquidityProposal) -> Result<Tally, GovernanceError> {
        Ok(self.engine.tally(proposal.poll)?)
    }

    /// Read the certified decision, if the proposal has resolved (APPROVE at quorum).
    /// `Ok(None)` below quorum — the quorum `AffineLe` refused the decision-turn.
    pub fn decision(
        &mut self,
        proposal: &LiquidityProposal,
    ) -> Result<Option<Decision>, GovernanceError> {
        Ok(self.engine.resolve(proposal.poll)?)
    }

    /// **The authorization gate.** Resolve the proposal and, ONLY if APPROVE reached
    /// quorum (a passed vote), mint the [`SwapAuthorization`] stamped by the governance
    /// authority. A below-quorum vote — or one where APPROVE did not win — yields `None`:
    /// no authorization, so no swap can execute.
    pub fn finalize(
        &mut self,
        proposal: &LiquidityProposal,
    ) -> Result<Option<SwapAuthorization>, GovernanceError> {
        // The quorum `AffineLe` is the REAL gate: `resolve` returns `Some` only once the
        // gated APPROVE option reaches `M`. Below quorum → `None` → no authorization.
        let Some(decision) = self.engine.resolve(proposal.poll)? else {
            return Ok(None);
        };
        // Defensive: the gated poll commits on APPROVE≥M, but a contested board (REJECT
        // strictly higher) is not a mandate to move the treasury — require APPROVE to be
        // the winner at quorum.
        if decision.winner != APPROVE_OPTION || decision.winner_tally < proposal.quorum_m {
            return Ok(None);
        }
        let poll_id = *blake3::hash(proposal.poll.0.as_bytes().as_slice()).as_bytes();
        Ok(Some(self.authority.authorize(
            proposal.amount,
            proposal.min_out,
            self.dregg_mint,
            self.usdc_mint,
            poll_id,
        )))
    }

    // ─────────────────────────────────────────────────────────────────────────
    // The market-price, quadratically-weighted, all-or-nothing pool proposal
    // ─────────────────────────────────────────────────────────────────────────

    /// **Open a market-price pool swap proposal.** `pool` is a
    /// [`SwapPool::snapshot`](crate::pool::SwapPool::snapshot) pinned NOW: it fixes the
    /// electorate (the contributors), each one's quadratic weight, and the amount (the
    /// pool's whole total — all or nothing).
    ///
    /// The poll is a WEIGHTED poll gated on APPROVE, so `quorum_weight` is a weight
    /// threshold in the executor's in-cell `AffineLe` and only APPROVE weight arms the
    /// decision-turn. The electorate is pinned into the poll cell's electorate-root
    /// commitment.
    ///
    /// Fails closed on an EMPTY pool ([`GovernanceError::EmptyPool`]) and on
    /// `quorum_weight == 0` (the engine's [`VoteError::BadPollSpec`] — a zero quorum would
    /// pass unconditionally).
    pub fn propose_market_swap(
        &mut self,
        question: impl Into<String>,
        pool: PoolSnapshot,
        quorum_weight: u64,
    ) -> Result<MarketSwapProposal, GovernanceError> {
        if pool.total() == 0 || pool.contributor_count() == 0 {
            return Err(GovernanceError::EmptyPool);
        }
        let spec = PollSpec {
            question: question.into(),
            options: vec!["reject".to_string(), "approve".to_string()],
            electorate: pool.electorate(),
            quorum_m: quorum_weight,
        };
        let poll = self.engine.open_poll_weighted_gated(spec, APPROVE_OPTION)?;
        Ok(MarketSwapProposal {
            poll,
            pool,
            quorum_weight,
        })
    }

    /// Mint a contributor's single-use ballot for a market proposal.
    ///
    /// **Eligibility IS contribution**: a `who` with no share of the pinned pool has
    /// quadratic weight `isqrt(0) = 0` and is refused
    /// ([`GovernanceError::NoContribution`]) before any ballot is minted. A weighted poll
    /// has a dynamic electorate at the engine, so this check is the eligibility gate, and
    /// the engine's own [`VoteError::ZeroWeight`] sits beneath it as a second floor.
    pub fn issue_pool_ballot(
        &mut self,
        proposal: &MarketSwapProposal,
        who: DepositAddress,
    ) -> Result<BallotCap, GovernanceError> {
        if proposal.weight_of(&who) == 0 {
            return Err(GovernanceError::NoContribution { who });
        }
        Ok(self.engine.issue_ballot(proposal.poll, who.0)?)
    }

    /// Cast one contributor's **quadratically weighted** vote. The weight is recomputed
    /// from the PINNED pool against the ballot's own voter identity — it is never taken
    /// from the caller, so a voter cannot name their own weight.
    ///
    /// Returns the weight actually cast. A double vote on the same ballot is a real
    /// executor refusal (the ballot's `WriteOnce(VOTE)` + the engine nullifier), at any
    /// weight.
    pub fn vote_market(
        &mut self,
        proposal: &MarketSwapProposal,
        ballot: &BallotCap,
        approve: bool,
    ) -> Result<u64, GovernanceError> {
        let who = DepositAddress(ballot.voter_pk);
        let weight = proposal.weight_of(&who);
        if weight == 0 {
            return Err(GovernanceError::NoContribution { who });
        }
        let option = if approve {
            APPROVE_OPTION
        } else {
            REJECT_OPTION
        };
        self.engine
            .cast_weighted(proposal.poll, ballot, option, weight)?;
        Ok(weight)
    }

    /// The live weighted tally (`[reject_weight, approve_weight]`).
    pub fn market_tally(&self, proposal: &MarketSwapProposal) -> Result<Tally, GovernanceError> {
        Ok(self.engine.tally(proposal.poll)?)
    }

    /// **The market-price authorization gate.** Resolve the weighted proposal and, ONLY if
    /// APPROVE reached the weight quorum, mint the [`SwapAuthorization`] for:
    ///
    /// * `amount` = the pinned pool's WHOLE total (all or nothing), and
    /// * `min_out` = [`MARKET_MIN_OUT`] (`0`) — market price, whatever slippage.
    ///
    /// Below quorum — or with REJECT winning — yields `None`: no authorization, so no swap
    /// can execute.
    pub fn finalize_market_swap(
        &mut self,
        proposal: &MarketSwapProposal,
    ) -> Result<Option<SwapAuthorization>, GovernanceError> {
        let Some(decision) = self.engine.resolve(proposal.poll)? else {
            return Ok(None);
        };
        if decision.winner != APPROVE_OPTION || decision.winner_tally < proposal.quorum_weight {
            return Ok(None);
        }
        let poll_id = *blake3::hash(proposal.poll.0.as_bytes().as_slice()).as_bytes();
        Ok(Some(self.authority.authorize(
            proposal.amount(),
            MARKET_MIN_OUT,
            self.dregg_mint,
            self.usdc_mint,
            poll_id,
        )))
    }
}
