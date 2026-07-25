//! # dregg-governance — governance and community are ONE primitive, on ONE engine
//!
//! ember's unifying insight, made concrete: **a federation governing itself, a
//! community poll, and a story's collective-choice are the SAME thing — a group
//! verifiably deciding what happens next over shared state.** That one primitive
//! is [`collective_choice::VoteEngine`], the **executor-backed** engine, and
//! every face in this crate is driven through it.
//!
//! ```text
//!                  ┌──────────────────────────────────────────┐
//!                  │   collective_choice::CollectiveChoice     │
//!                  │   (the VERIFIED EXECUTOR substrate)       │
//!                  │   WriteOnce(VOTE) ballots · Monotonic     │
//!                  │   tallies · AffineLe + CountGe quorum ·   │
//!                  │   Mandate::sub_delegate · nullifiers      │
//!                  └──────────────────────────────────────────┘
//!            ┌──────────────────────┼──────────────────────┐
//!  federation self-governance   community poll         story branch-vote
//!  (governance.rs ≡              (community.rs)         (CYOA — same engine;
//!   substrate.rs)                anyone · verifiable ·   `spween-dregg`)
//!  committee · 2n/3+1 ·          delegatable
//!  auto-enact (reactor.rs)
//! ```
//!
//! ## Every gate below is an EXECUTOR gate
//!
//! - **Federation self-governance** ([`governance::FederationGovernance`], which
//!   *is* [`substrate::ExecutorGovernance`]) — the committee votes on a proposal
//!   (admit/evict a validator, amend the threshold). Eligibility is holding a
//!   ballot cap minted only to a constitutional participant; one-vote is the
//!   ballot's `WriteOnce(VOTE)` + the engine nullifier; the constitutional
//!   `required_votes_for` (2n/3+1, honoring the H-rule) is baked in as the
//!   **in-cell per-option `AffineLe` gate**, and arming `RESOLVED` must
//!   additionally EXHIBIT `required` distinct approvers through the `CountGe`
//!   gate. [`reactor::GovernanceEnactReactor`] auto-enacts on the real
//!   [`dregg_blocklace::constitution::ConstitutionManager`] only when the
//!   executor's decision-turn commits AND the constitution independently agrees.
//! - **Community polls** ([`community::CommunityPolls`]) — a general poll on the
//!   same engine: verifiable (the executor's stored monotone tally and the
//!   light-client replay agree), delegatable (liquid democracy through the
//!   **Lean-mirrored** [`dregg_intent::agent_mandate::Mandate::sub_delegate`] —
//!   the one non-amplifying lattice, reused, not re-implemented).
//!
//! ## The demoted host ballot box
//!
//! [`HostBallotBox`] (below) is **NOT** a governance substrate and no marquee
//! path runs on it. It is a host-side, in-memory causal-log derivation aid:
//! content-addressed [`VoteBlock`]s, a [`BallotLog::causal_root`], and the
//! `derive_tally`/`verify_tally` light-client recompute. It is retained for
//! exactly two reasons, both named:
//!
//! 1. the **weighted** holding-weight ballot ([`holding_weight`]) — the executor
//!    engine's `cast` bumps a tally by exactly one per ballot and takes no weight
//!    argument, so a weight-`W` ballot has no executor expression yet (see the
//!    residual note on [`holding_weight::HoldingWeightRegistry::grant_and_cast`]);
//! 2. out-of-lane consumers that still name the old shape.
//!
//! Its gates are ordinary Rust bookkeeping. Do not add a governance face to it.

use std::collections::{BTreeMap, BTreeSet, HashSet};

pub mod community;
pub mod governance;
pub mod holding_weight;
pub mod proven_foreign_holding;
pub mod reactor;
pub mod substrate;

/// A voter's public-key identity (an ed25519 key, matching the constitution's
/// `[u8; 32]` participant keys).
pub type VoterId = [u8; 32];

/// A blake3 content hash (a ballot-block id, or the causal root of a log).
pub type BlockHash = [u8; 32];

/// An option index within a poll: `0` is the first option in [`PollSpec::options`].
///
/// For a governance proposal the two options are `{REJECT, APPROVE}`; for a
/// community poll they are the poll's own choices; for a CYOA branch-vote they
/// are the story's available branches.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct OptionId(pub u64);

/// The `reject` option of a two-option governance proposal.
pub const REJECT: OptionId = OptionId(0);
/// The `approve` option of a two-option governance proposal.
pub const APPROVE: OptionId = OptionId(1);

/// A poll identity: a content hash over the poll's question, options, electorate,
/// and a caller nonce.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct PollId(pub [u8; 32]);

// ─── Electorate ─────────────────────────────────────────────────────────────

/// Who may vote in a poll.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Electorate {
    /// Anyone may cast (a public community poll).
    Open,
    /// Only members of this set may cast (a federation committee, a named
    /// electorate). Mirrors the constitution's participant set / the
    /// governed-namespace `governance_committee_root`.
    Closed(BTreeSet<VoterId>),
}

impl Electorate {
    /// Is `voter` eligible to cast in this electorate?
    pub fn eligible(&self, voter: &VoterId) -> bool {
        match self {
            Electorate::Open => true,
            Electorate::Closed(set) => set.contains(voter),
        }
    }

    /// The size of a closed electorate (`None` for an open one) — the `n` the
    /// supermajority threshold is computed over.
    pub fn size(&self) -> Option<usize> {
        match self {
            Electorate::Open => None,
            Electorate::Closed(set) => Some(set.len()),
        }
    }
}

// ─── Decision rule ──────────────────────────────────────────────────────────

/// How a poll decides — the quorum/threshold gate applied at
/// [`HostVoteEngine::resolve`]. **Host-side Rust comparisons**, not a gate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DecisionRule {
    /// A specific `option` must reach `min` weight of distinct approving voters.
    /// The federation face uses this with the constitutional `required_votes_for`
    /// as `min` (which encodes the 2n/3+1 supermajority and the H-rule).
    Threshold { option: OptionId, min: u64 },
    /// The constitutional `⌊2n/3⌋ + 1` supermajority of the (closed) electorate on
    /// [`APPROVE`], computed via THE one quorum formula
    /// [`dregg_blocklace::supermajority_threshold`].
    Supermajority,
    /// The option with the most weight wins, once `quorum` total ballots are in
    /// (a community plurality poll).
    Plurality { quorum: u64 },
}

// ─── Poll specification ─────────────────────────────────────────────────────

/// The immutable terms of a poll: the question, the named options, who may vote,
/// how it decides, whether passing enacts, and a caller nonce (so two polls with
/// otherwise-identical terms get distinct ids).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PollSpec {
    /// Human-readable question.
    pub question: String,
    /// The named options; index `i` is [`OptionId(i)`](OptionId).
    pub options: Vec<String>,
    /// Who may vote.
    pub electorate: Electorate,
    /// The quorum/threshold gate.
    pub rule: DecisionRule,
    /// Whether a decided poll should auto-enact (governance polls do; a plain
    /// community opinion poll need not).
    pub enact_on_pass: bool,
    /// Disambiguating nonce folded into the [`PollId`].
    pub nonce: u64,
}

impl PollSpec {
    /// The content-addressed id of this poll.
    pub fn id(&self) -> PollId {
        let mut h = blake3::Hasher::new_derive_key("dregg-governance-poll-id-v1");
        h.update(self.question.as_bytes());
        h.update(&(self.options.len() as u64).to_be_bytes());
        for o in &self.options {
            h.update(&(o.len() as u64).to_be_bytes());
            h.update(o.as_bytes());
        }
        match &self.electorate {
            Electorate::Open => {
                h.update(b"open");
            }
            Electorate::Closed(set) => {
                h.update(b"closed");
                h.update(&(set.len() as u64).to_be_bytes());
                for v in set {
                    h.update(v);
                }
            }
        }
        h.update(&self.nonce.to_be_bytes());
        PollId(*h.finalize().as_bytes())
    }
}

// ─── Votes are blocks ───────────────────────────────────────────────────────

/// A single ballot, expressed as a content-addressed block that references the
/// prior ballot in its causal past — exactly the constitution's "votes are
/// blocks" shape (`constitution.rs`: a `MembershipVote` is a block payload
/// referencing the proposal block in its causal past). Because a ballot is a
/// block, no operator can silently drop it: dropping one changes the log's
/// committed [`BallotLog::causal_root`], and any peer holding the block re-derives
/// the same tally.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VoteBlock {
    /// The poll this ballot is cast in.
    pub poll: PollId,
    /// The casting voter.
    pub voter: VoterId,
    /// The chosen option.
    pub choice: OptionId,
    /// The voter's weight (1 for one-member-one-vote; more for a liquid-democracy
    /// delegate carrying delegated weight).
    pub weight: u64,
    /// The id of the block this ballot references in its causal past (the log tip
    /// at cast time), or `None` for the first ballot.
    pub causal_prev: Option<BlockHash>,
}

impl VoteBlock {
    /// The block's content-addressed id (its blake3 hash).
    pub fn id(&self) -> BlockHash {
        let mut h = blake3::Hasher::new_derive_key("dregg-governance-vote-block-v1");
        h.update(&self.poll.0);
        h.update(&self.voter);
        h.update(&self.choice.0.to_be_bytes());
        h.update(&self.weight.to_be_bytes());
        match self.causal_prev {
            Some(p) => {
                h.update(&[1u8]);
                h.update(&p);
            }
            None => {
                h.update(&[0u8]);
            }
        }
        *h.finalize().as_bytes()
    }
}

/// An append-only causal log of ballot blocks — the uncensorable ballot box.
#[derive(Clone, Debug, Default)]
pub struct BallotLog {
    blocks: Vec<VoteBlock>,
}

impl BallotLog {
    /// A fresh, empty log.
    pub fn new() -> Self {
        BallotLog::default()
    }

    /// The id of the most-recent block (what the next ballot references), or
    /// `None` if the log is empty.
    pub fn tip(&self) -> Option<BlockHash> {
        self.blocks.last().map(|b| b.id())
    }

    /// Append a ballot block.
    pub fn append(&mut self, block: VoteBlock) {
        self.blocks.push(block);
    }

    /// The ballot blocks, in causal order.
    pub fn blocks(&self) -> &[VoteBlock] {
        &self.blocks
    }

    /// How many ballots the log holds.
    pub fn len(&self) -> usize {
        self.blocks.len()
    }

    /// Is the log empty?
    pub fn is_empty(&self) -> bool {
        self.blocks.is_empty()
    }

    /// The committed causal root: a blake3 fold over every block id in causal
    /// order. **Any** dropped, added, or reordered ballot changes this root — the
    /// digest a light client re-derives to detect a censoring or ballot-stuffing
    /// operator.
    pub fn causal_root(&self) -> BlockHash {
        let mut h = blake3::Hasher::new_derive_key("dregg-governance-ballot-log-v1");
        for b in &self.blocks {
            h.update(&b.id());
        }
        *h.finalize().as_bytes()
    }
}

// ─── Tally and resolution ───────────────────────────────────────────────────

/// A re-derivable count over a poll's ballot log.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tally {
    /// The poll tallied.
    pub poll: PollId,
    /// Weight per option (a valid, distinct-voter, eligible tally).
    pub per_option: BTreeMap<OptionId, u64>,
    /// How many distinct eligible voters were counted.
    pub distinct_voters: usize,
    /// The causal root of the log this tally was derived over — the light-client
    /// witness that binds the tally to an exact, complete ballot set.
    pub causal_root: BlockHash,
}

/// The outcome of applying a poll's [`DecisionRule`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Resolution {
    /// The rule is not yet satisfied (below threshold / below quorum).
    Pending,
    /// The poll is decided; `winner` is the winning option and `enact` says
    /// whether it should auto-enact (from [`PollSpec::enact_on_pass`]).
    Decided { winner: OptionId, enact: bool },
}

/// Why a [`HostVoteEngine::cast`] was refused (or that it was accepted).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CastOutcome {
    /// The ballot was recorded.
    Accepted,
    /// No such poll is open on this engine.
    RefusedUnknownPoll,
    /// The voter is not in the poll's electorate (the non-committee refusal).
    RefusedNotEligible,
    /// The voter has already cast in this poll (the one-vote / distinct-voter
    /// refusal).
    RefusedDoubleVote,
    /// The chosen option index is out of range for this poll.
    RefusedUnknownOption,
}

// ═══════════════════════════════════════════════════════════════════════════
//  DEMOTED — the host ballot box. NOT a governance substrate.
// ═══════════════════════════════════════════════════════════════════════════
//
// Everything from here down is host-side, in-memory Rust bookkeeping. It used
// to be the marquee governance engine, which made this crate DUAL-FACED: a real
// verified weld (`substrate.rs`) sat behind a side door while the front door ran
// a parallel twin whose quorum / double-vote / threshold gates were Rust `if`s
// and a `HashSet`. The front door now runs on the verified executor
// (`collective_choice::CollectiveChoice`); this box is what is left over.
//
// What it still legitimately IS: a causal-log derivation aid. `derive_tally` /
// `verify_tally` over a `BallotLog` is a light-client recompute, and
// `BallotLog::causal_root` is the digest that catches a censoring operator.
// Those are real, and they are not a claim about executor enforcement.
//
// What it is NOT: an eligibility, one-vote, or quorum gate anyone should rely
// on. `HostBallotBox::cast`'s refusals are `HashSet::contains` and a `>=`. Do
// not hang a governance face on it. See the crate docs for the two named
// reasons it is retained.

/// The host ballot box's interface — **the demoted twin of
/// [`collective_choice::VoteEngine`]**, kept only for the derivation aid and the
/// weighted holding-weight ballot. The real one-trait-three-faces primitive is
/// `collective_choice::VoteEngine`; drive that.
pub trait HostVoteEngine {
    /// Open a poll; returns its content-addressed id.
    fn open_poll(&mut self, spec: PollSpec) -> PollId;

    /// Cast one ballot (as a causal block) into an open poll.
    fn cast(&mut self, poll: PollId, block: VoteBlock) -> CastOutcome;

    /// The current tally over the poll's ballot log (`None` if no such poll).
    fn tally(&self, poll: PollId) -> Option<Tally>;

    /// Apply the poll's decision rule to the current tally.
    fn resolve(&self, poll: PollId) -> Resolution;
}

// ─── HostBallotBox — the demoted in-memory box ──────────────────────────────

/// The live state of one open poll on the demoted [`HostBallotBox`].
#[derive(Clone, Debug)]
pub struct PollState {
    /// The poll's immutable terms.
    pub spec: PollSpec,
    /// The causal ballot log.
    pub log: BallotLog,
    /// Distinct voters who have cast. **Host-side bookkeeping** — a plain
    /// `HashSet`, not a gate anything should trust. The real one-vote tooth is
    /// the executor's `WriteOnce(VOTE)` ballot + engine nullifier.
    voted: HashSet<VoterId>,
}

/// **The demoted host ballot box.** An in-memory causal ballot log with a
/// light-client-recomputable tally.
///
/// This is *not* a verified substrate and no marquee governance path runs on it
/// — see the DEMOTED banner above. The governance front door
/// ([`governance::FederationGovernance`]) and the community face
/// ([`community::CommunityPolls`]) both drive
/// [`collective_choice::CollectiveChoice`], where a double vote dies at a
/// nullifier and quorum is an in-cell `AffineLe` + `CountGe`, not a `HashSet`
/// and a `>=`.
///
/// What is genuinely useful here: [`Self::derive_tally`] /
/// [`Self::verify_tally`] over a [`BallotLog`] — the auditor's from-scratch
/// recompute, and [`BallotLog::causal_root`], the digest that catches a dropped
/// ballot.
#[derive(Clone, Debug, Default)]
pub struct HostBallotBox {
    polls: BTreeMap<PollId, PollState>,
}

impl HostBallotBox {
    /// A fresh box with no open polls.
    pub fn new() -> Self {
        HostBallotBox::default()
    }

    /// Read a poll's live state.
    pub fn poll_state(&self, poll: PollId) -> Option<&PollState> {
        self.polls.get(&poll)
    }

    /// Build the next ballot block for `voter` in `poll`, referencing the current
    /// log tip in its causal past. Returns `None` if the poll is unknown.
    pub fn next_block(
        &self,
        poll: PollId,
        voter: VoterId,
        choice: OptionId,
        weight: u64,
    ) -> Option<VoteBlock> {
        let st = self.polls.get(&poll)?;
        Some(VoteBlock {
            poll,
            voter,
            choice,
            weight,
            causal_prev: st.log.tip(),
        })
    }

    /// Re-derive the tally over `log` under `spec` **from scratch**, re-validating
    /// every block (eligibility, known option, distinct voter). This is the
    /// light-client / auditor path: a stuffed ballot (ineligible voter) is
    /// ignored, a double vote counts once, so a claimed tally that counted them
    /// mismatches this honest derivation.
    pub fn derive_tally(poll: PollId, spec: &PollSpec, log: &BallotLog) -> Tally {
        let mut per_option: BTreeMap<OptionId, u64> = BTreeMap::new();
        let mut seen: HashSet<VoterId> = HashSet::new();
        for b in log.blocks() {
            if b.poll != poll {
                continue;
            }
            if !spec.electorate.eligible(&b.voter) {
                continue; // a stuffed, ineligible ballot never counts
            }
            if (b.choice.0 as usize) >= spec.options.len() {
                continue; // an unknown option never counts
            }
            if !seen.insert(b.voter) {
                continue; // one vote per voter — first ballot wins
            }
            // saturating_add, never wrapping: a per-option tally that would
            // overflow u64 caps at the ceiling instead of wrapping to a small
            // value in release (a wrap could make the true-largest option LOSE
            // the `max_by` winner election below in `resolve`).
            let slot = per_option.entry(b.choice).or_insert(0);
            *slot = slot.saturating_add(b.weight);
        }
        Tally {
            poll,
            per_option,
            distinct_voters: seen.len(),
            causal_root: log.causal_root(),
        }
    }

    /// **Light-client tally verification.** Recompute the tally over `log` under
    /// `spec` and check it equals `claimed` — including the causal root. A tally
    /// over a censored (dropped-ballot) or stuffed log is caught here; this is the
    /// "the tally is a light-client-checkable turn" property. `committed_root` is
    /// the ballot-set digest the verifier independently knows (from consensus): a
    /// dropped ballot makes `log.causal_root() != committed_root`, so the check
    /// fails even if the operator re-signed a self-consistent shrunken tally.
    pub fn verify_tally(
        spec: &PollSpec,
        log: &BallotLog,
        claimed: &Tally,
        committed_root: BlockHash,
    ) -> bool {
        let recomputed = Self::derive_tally(claimed.poll, spec, log);
        &recomputed == claimed && recomputed.causal_root == committed_root
    }
}

impl HostVoteEngine for HostBallotBox {
    fn open_poll(&mut self, spec: PollSpec) -> PollId {
        let id = spec.id();
        self.polls.entry(id).or_insert(PollState {
            spec,
            log: BallotLog::new(),
            voted: HashSet::new(),
        });
        id
    }

    fn cast(&mut self, poll: PollId, block: VoteBlock) -> CastOutcome {
        let st = match self.polls.get_mut(&poll) {
            Some(s) => s,
            None => return CastOutcome::RefusedUnknownPoll,
        };
        if block.poll != poll {
            return CastOutcome::RefusedUnknownPoll;
        }
        if !st.spec.electorate.eligible(&block.voter) {
            return CastOutcome::RefusedNotEligible;
        }
        if (block.choice.0 as usize) >= st.spec.options.len() {
            return CastOutcome::RefusedUnknownOption;
        }
        if st.voted.contains(&block.voter) {
            return CastOutcome::RefusedDoubleVote;
        }
        st.voted.insert(block.voter);
        st.log.append(block);
        CastOutcome::Accepted
    }

    fn tally(&self, poll: PollId) -> Option<Tally> {
        let st = self.polls.get(&poll)?;
        Some(Self::derive_tally(poll, &st.spec, &st.log))
    }

    fn resolve(&self, poll: PollId) -> Resolution {
        let st = match self.polls.get(&poll) {
            Some(s) => s,
            None => return Resolution::Pending,
        };
        let tally = Self::derive_tally(poll, &st.spec, &st.log);
        let enact = st.spec.enact_on_pass;
        match st.spec.rule {
            DecisionRule::Threshold { option, min } => {
                let got = tally.per_option.get(&option).copied().unwrap_or(0);
                if got >= min {
                    Resolution::Decided {
                        winner: option,
                        enact,
                    }
                } else {
                    Resolution::Pending
                }
            }
            DecisionRule::Supermajority => {
                let n = st.spec.electorate.size().unwrap_or(0);
                let need = dregg_blocklace::supermajority_threshold(n) as u64;
                let approvals = tally.per_option.get(&APPROVE).copied().unwrap_or(0);
                if approvals >= need {
                    Resolution::Decided {
                        winner: APPROVE,
                        enact,
                    }
                } else {
                    Resolution::Pending
                }
            }
            DecisionRule::Plurality { quorum } => {
                // checked fold: an overflowing total is not a valid quorum result.
                // Refuse (stay Pending) rather than let a release build wrap the
                // total below `quorum` and either bypass or spuriously arm the gate.
                let total = match tally
                    .per_option
                    .values()
                    .try_fold(0u64, |acc, &w| acc.checked_add(w))
                {
                    Some(t) => t,
                    None => return Resolution::Pending,
                };
                if total < quorum {
                    return Resolution::Pending;
                }
                // The option with the most weight wins (lowest id breaks ties).
                let winner = tally
                    .per_option
                    .iter()
                    .max_by(|a, b| a.1.cmp(b.1).then(b.0.cmp(a.0)))
                    .map(|(opt, _)| *opt);
                match winner {
                    Some(w) => Resolution::Decided { winner: w, enact },
                    None => Resolution::Pending,
                }
            }
        }
    }
}

// ─── Compatibility aliases for the demoted box ──────────────────────────────
//
// The old marquee names. They now point at the DEMOTED host ballot box and exist
// only so out-of-lane consumers keep compiling. Nothing in this crate's
// governance or community face uses them; new code should name
// `collective_choice::{CollectiveChoice, VoteEngine}` (the verified engine) or
// `HostBallotBox`/`HostVoteEngine` (the derivation aid), never these.

/// The pre-weld name of [`HostBallotBox`]. **Demoted alias** — it does not name
/// [`collective_choice::CollectiveChoice`], which is the real engine every
/// governance path in this crate now runs on.
pub type CollectiveChoice = HostBallotBox;

/// The pre-weld name of [`HostVoteEngine`]. **Demoted alias** — the real
/// one-primitive trait is [`collective_choice::VoteEngine`].
pub use self::HostVoteEngine as VoteEngine;

#[cfg(test)]
mod tests {
    use super::*;

    fn voter(b: u8) -> VoterId {
        [b; 32]
    }

    fn open_community(engine: &mut HostBallotBox, options: &[&str], quorum: u64) -> PollId {
        engine.open_poll(PollSpec {
            question: "lunch?".into(),
            options: options.iter().map(|s| s.to_string()).collect(),
            electorate: Electorate::Open,
            rule: DecisionRule::Plurality { quorum },
            enact_on_pass: false,
            nonce: 0,
        })
    }

    fn cast(engine: &mut HostBallotBox, poll: PollId, v: u8, choice: u64) -> CastOutcome {
        let block = engine
            .next_block(poll, voter(v), OptionId(choice), 1)
            .unwrap();
        engine.cast(poll, block)
    }

    #[test]
    fn plurality_poll_tallies_and_resolves() {
        let mut e = HostBallotBox::new();
        let poll = open_community(&mut e, &["ramen", "tacos"], 3);
        assert_eq!(cast(&mut e, poll, 1, 0), CastOutcome::Accepted);
        assert_eq!(cast(&mut e, poll, 2, 1), CastOutcome::Accepted);
        // below quorum → pending
        assert_eq!(e.resolve(poll), Resolution::Pending);
        assert_eq!(cast(&mut e, poll, 3, 1), CastOutcome::Accepted);
        assert_eq!(
            e.resolve(poll),
            Resolution::Decided {
                winner: OptionId(1),
                enact: false
            }
        );
    }

    // FALSIFIER: a Plurality quorum whose TOTAL weight would overflow u64 is
    // REFUSED (stays Pending), never wrapped. Two options each carry a
    // near-ceiling weight: each per-option tally is a valid u64, but their sum
    // overflows. A plain `.values().sum()` wraps in release to a small value
    // (here ~9.2e18) that still clears `quorum`, so the old code would spuriously
    // DECIDE a winner off a wrapped total. The checked fold must instead refuse.
    #[test]
    fn plurality_quorum_total_overflow_is_refused_not_wrapped() {
        const BIG: u64 = 0xC000_0000_0000_0000; // ~1.38e19; BIG + BIG overflows u64
        assert!(
            BIG.checked_add(BIG).is_none(),
            "test premise: BIG + BIG must overflow u64"
        );

        let mut e = HostBallotBox::new();
        let poll = open_community(&mut e, &["ramen", "tacos"], 3);

        let b0 = e.next_block(poll, voter(1), OptionId(0), BIG).unwrap();
        assert_eq!(e.cast(poll, b0), CastOutcome::Accepted);
        let b1 = e.next_block(poll, voter(2), OptionId(1), BIG).unwrap();
        assert_eq!(e.cast(poll, b1), CastOutcome::Accepted);

        // The summed total overflows u64 -> the quorum gate cannot be trusted, so
        // resolution REFUSES (Pending) rather than deciding off a wrapped total.
        assert_eq!(
            e.resolve(poll),
            Resolution::Pending,
            "an overflowing plurality total must refuse resolution, not wrap below/above quorum"
        );
    }

    #[test]
    fn one_vote_per_voter() {
        let mut e = HostBallotBox::new();
        let poll = open_community(&mut e, &["a", "b"], 10);
        assert_eq!(cast(&mut e, poll, 1, 0), CastOutcome::Accepted);
        assert_eq!(cast(&mut e, poll, 1, 1), CastOutcome::RefusedDoubleVote);
        assert_eq!(e.tally(poll).unwrap().distinct_voters, 1);
    }

    #[test]
    fn unknown_option_and_unknown_poll_refused() {
        let mut e = HostBallotBox::new();
        let poll = open_community(&mut e, &["a", "b"], 10);
        assert_eq!(cast(&mut e, poll, 1, 7), CastOutcome::RefusedUnknownOption);
        let bogus = PollId([9u8; 32]);
        let block = VoteBlock {
            poll: bogus,
            voter: voter(1),
            choice: OptionId(0),
            weight: 1,
            causal_prev: None,
        };
        assert_eq!(e.cast(bogus, block), CastOutcome::RefusedUnknownPoll);
    }

    #[test]
    fn each_ballot_references_the_causal_tip() {
        // votes-are-blocks: each block's causal_prev is the previous block's id.
        let mut e = HostBallotBox::new();
        let poll = open_community(&mut e, &["a", "b"], 10);
        let b1 = e.next_block(poll, voter(1), OptionId(0), 1).unwrap();
        assert_eq!(b1.causal_prev, None);
        e.cast(poll, b1.clone()).assert_accepted();
        let b2 = e.next_block(poll, voter(2), OptionId(1), 1).unwrap();
        assert_eq!(b2.causal_prev, Some(b1.id()));
    }

    impl CastOutcome {
        fn assert_accepted(self) {
            assert_eq!(self, CastOutcome::Accepted);
        }
    }
}
