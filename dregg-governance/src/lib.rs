//! # dregg-governance — governance and community are ONE primitive
//!
//! ember's unifying insight, made concrete: **a federation governing itself, a
//! community poll, and a story's collective-choice are the SAME thing — a group
//! verifiably deciding what happens next over shared state.** This crate surfaces
//! that one primitive, the [`VoteEngine`], for two governance *faces*, and notes
//! (in code and in a shared-shape test) that it is the *identical* shape a
//! choose-your-own-adventure branch-vote uses.
//!
//! ```text
//!                         ┌───────────────────────────┐
//!                         │        VoteEngine          │
//!                         │  open_poll · cast · tally  │
//!                         │         · resolve          │
//!                         └───────────────────────────┘
//!            ┌──────────────────────┼──────────────────────┐
//!  federation self-governance   community poll         story branch-vote
//!  (governance.rs)              (community.rs)          (CYOA — same shape;
//!  committee · 2n/3+1 ·          anyone · verifiable ·   `tests/teeth.rs`)
//!  auto-enact (reactor.rs)       delegatable · uncensorable
//! ```
//!
//! ## What each face is
//!
//! - **Federation self-governance** ([`governance`]) — the committee votes on a
//!   proposal (admit/evict a validator, amend the threshold, amend routes). It
//!   ties directly to the REAL [`dregg_blocklace::constitution`]: the electorate
//!   is the constitution's current participant set, the threshold is the
//!   constitutional `required_votes_for` (the 2n/3+1 supermajority, honoring the
//!   H-rule), each cast mirrors into the real distinct-voter `VoteTracker`, and a
//!   [`reactor::GovernanceEnactReactor`] **auto-enacts** the proposal on the real
//!   `ConstitutionManager` the instant quorum is met. The federation governs
//!   itself, verifiably and uncensorably.
//! - **Community polls** ([`community`]) — a general poll anyone can run:
//!   verifiable (the tally is a light-client-recomputable derivation over the
//!   ballot log), delegatable (liquid democracy via non-amplifying
//!   [`community::VoteCap`] attenuation), and uncensorable (votes are content-
//!   addressed blocks in a causal log, so a dropped ballot changes the committed
//!   [`BallotLog::causal_root`] and is caught).
//!
//! ## The unification
//!
//! Both faces are the SAME [`CollectiveChoice`] object driven through the SAME
//! four [`VoteEngine`] methods. A governance proposal is a poll over
//! `{reject, approve}`; a community poll is a poll over arbitrary options; a CYOA
//! branch-vote is a poll over the story's available branches. Options differ;
//! the engine does not. See `tests/teeth.rs::same_vote_engine_drives_all_three_faces`.
//!
//! ## `VoteEngine` and the wider `collective-choice` — RECONCILED
//!
//! The `collective-choice` crate's **executor-backed engine is the canonical
//! vote substrate**: every ballot there is a real verified turn (a `WriteOnce`
//! ballot cell, a `Monotonic` tally, an in-cell `AffineLe` quorum gate, a
//! nullifier set). The constitution face runs over it via [`substrate`]
//! ([`substrate::ExecutorGovernance`] + [`substrate::ExecutorEnactReactor`]):
//! a proposal opens an executor poll whose per-option `AffineLe` gate IS the
//! constitutional `required_votes_for`, votes are ballot-cap turns, and the
//! reactor auto-enacts on the real `ConstitutionManager`.
//!
//! The [`VoteEngine`] trait and [`CollectiveChoice`] object in THIS file remain
//! the in-memory causal-log face (defined from the census shape,
//! `docs/deos/STARBRIDGE-APPS-CENSUS.md` §2): content-addressed `VoteBlock`s,
//! the light-client-recomputable `derive_tally`/`verify_tally` path, and the
//! shared-shape demonstration that governance, community polls, and CYOA
//! branch-votes (`docs/deos/SPWEEN-ON-DREGG.md` §4.2) are one primitive.

use std::collections::{BTreeMap, BTreeSet, HashSet};

pub mod community;
pub mod governance;
pub mod holding_weight;
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

/// How a poll decides — the quorum/threshold gate applied at [`VoteEngine::resolve`].
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
    /// community opinion poll need not). Read by [`reactor::GovernanceEnactReactor`].
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

/// Why a [`VoteEngine::cast`] was refused (or that it was accepted).
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

// ─── The VoteEngine trait — the ONE primitive ───────────────────────────────

/// The collective-choice interface. **One trait, three faces**: a federation
/// governance proposal, a community poll, and a CYOA story branch-vote are all
/// driven through these four methods. Defined locally from the census shape
/// (`STARBRIDGE-APPS-CENSUS.md` §2: `open_poll / cast / tally / resolve`); the
/// reconciliation point with a shared `collective-choice` crate.
pub trait VoteEngine {
    /// Open a poll; returns its content-addressed id.
    fn open_poll(&mut self, spec: PollSpec) -> PollId;

    /// Cast one ballot (as a causal block) into an open poll.
    fn cast(&mut self, poll: PollId, block: VoteBlock) -> CastOutcome;

    /// The current tally over the poll's ballot log (`None` if no such poll).
    fn tally(&self, poll: PollId) -> Option<Tally>;

    /// Apply the poll's decision rule to the current tally.
    fn resolve(&self, poll: PollId) -> Resolution;
}

// ─── CollectiveChoice — the shared engine ───────────────────────────────────

/// The live state of one open poll.
#[derive(Clone, Debug)]
pub struct PollState {
    /// The poll's immutable terms.
    pub spec: PollSpec,
    /// The causal ballot log.
    pub log: BallotLog,
    /// Distinct voters who have cast (the one-vote-per-voter set — the in-cell
    /// analogue of the `VoteTracker` `HashSet`).
    voted: HashSet<VoterId>,
}

/// **The one collective-choice engine.** Holds a set of open polls and drives
/// them through the [`VoteEngine`] interface. The federation self-governance face
/// and the community-poll face both build on THIS object — that is the whole
/// point: governance and community (and stories) are one primitive.
#[derive(Clone, Debug, Default)]
pub struct CollectiveChoice {
    polls: BTreeMap<PollId, PollState>,
}

impl CollectiveChoice {
    /// A fresh engine with no open polls.
    pub fn new() -> Self {
        CollectiveChoice::default()
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
            *per_option.entry(b.choice).or_insert(0) += b.weight;
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

impl VoteEngine for CollectiveChoice {
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
                let total: u64 = tally.per_option.values().sum();
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

#[cfg(test)]
mod tests {
    use super::*;

    fn voter(b: u8) -> VoterId {
        [b; 32]
    }

    fn open_community(engine: &mut CollectiveChoice, options: &[&str], quorum: u64) -> PollId {
        engine.open_poll(PollSpec {
            question: "lunch?".into(),
            options: options.iter().map(|s| s.to_string()).collect(),
            electorate: Electorate::Open,
            rule: DecisionRule::Plurality { quorum },
            enact_on_pass: false,
            nonce: 0,
        })
    }

    fn cast(engine: &mut CollectiveChoice, poll: PollId, v: u8, choice: u64) -> CastOutcome {
        let block = engine
            .next_block(poll, voter(v), OptionId(choice), 1)
            .unwrap();
        engine.cast(poll, block)
    }

    #[test]
    fn plurality_poll_tallies_and_resolves() {
        let mut e = CollectiveChoice::new();
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

    #[test]
    fn one_vote_per_voter() {
        let mut e = CollectiveChoice::new();
        let poll = open_community(&mut e, &["a", "b"], 10);
        assert_eq!(cast(&mut e, poll, 1, 0), CastOutcome::Accepted);
        assert_eq!(cast(&mut e, poll, 1, 1), CastOutcome::RefusedDoubleVote);
        assert_eq!(e.tally(poll).unwrap().distinct_voters, 1);
    }

    #[test]
    fn unknown_option_and_unknown_poll_refused() {
        let mut e = CollectiveChoice::new();
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
        let mut e = CollectiveChoice::new();
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
