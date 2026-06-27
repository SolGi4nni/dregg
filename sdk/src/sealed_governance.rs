//! # sealed_governance — commit→reveal governance where NO ONE can peek early.
//!
//! Sealed-bid AUCTIONS and sealed BALLOTS where the commit-reveal boundary is
//! enforced by a COMMON SECRET, not by an honest collector. Each participant
//! seals their bid/ballot to a council's group public key
//! ([`crate::council_seal`]); the seals are COLLECTED during an open window; at
//! the reveal boundary a `K`-of-`N` quorum OPENS them together
//! (threshold-decrypt). Below `K`, the seals are *information-theoretically
//! nothing* (`subThreshold_secret_blind`): no front-running, no early tally
//! bias, no peeking auctioneer — the cliff IS the commit-reveal gate.
//!
//! ## Why this is strictly stronger than a hash commitment
//!
//! The classic commit→reveal (`metatheory/Dregg2/Intent/SealedAuction.lean`,
//! `intent/src/commit_reveal_fulfillment.rs`) seals a bid as `H(bidder ‖ value
//! ‖ nonce)` and relies on each bidder to *choose to reveal*. That binds the
//! value (collision-resistance) and hides it (the nonce's entropy) — but the
//! COLLECTOR, holding all commitments, learns nothing only because it lacks the
//! nonces; a bidder who reveals early, or colludes, leaks their own bid, and a
//! non-revealing bidder simply withholds (the classic selective-abort). Here the
//! ciphertext is sealed to a THRESHOLD KEY no party holds: even the collector
//! who holds EVERY sealed submission cannot open ONE of them below quorum, and a
//! committed submission is openable BY THE QUORUM whether or not its author
//! cooperates — selective non-reveal is removed, because revealing is the
//! council's K-of-N act, not the participant's. The hiding is
//! information-theoretic below `K`, not merely entropy-of-a-nonce.
//!
//! ## What it welds (census-first; reinvents no crypto, adds no executor verb)
//!
//! Pure orchestration over two existing organs:
//!
//! - [`crate::council_seal`] — the threshold seal (`Council::genesis` /
//!   [`seal`](crate::council_seal::seal) / [`Council::open`]). This carries the
//!   whole crypto floor AND the proven cliff (its `subthreshold_coalition_learns_nothing`
//!   test is the FALSE polarity this module rides). No new pairing code here.
//! - [`crate::beacon_cell`] — the unbiasable reveal-beacon, for the *tie-break*
//!   / draw randomness a contested governance outcome needs (the reveal
//!   randomness is itself a common-secret cliff: unpredictable below `K`).
//!
//! ## The two protocol objects
//!
//! - [`SealedAuction`] — first-price sealed-bid: bidders seal bids during the
//!   `Collecting` window; the quorum opens them at `Revealing`; the winner is the
//!   highest opened bid, with ties broken by an unbiasable beacon draw. The
//!   winner is PROVABLE from the opened bids (anyone can re-run [`AuctionOutcome::recompute`]).
//! - [`SealedBallot`] — sealed-ballot election: voters seal ballots; the quorum
//!   tallies them at close. The base form is roster-bound (one vote per
//!   registered voter); the unlinkable extension ([`SealedBallot::new_unlinkable`]
//!   + [`seal_unlinkable_ballot`]) binds an anonymous eligibility nullifier INTO
//!   the seal plaintext so the OPENED ballot cannot be linked to the voter who
//!   cast it (vote privacy survives the reveal), AND so the nullifier is
//!   opened-and-verified at tally — a borrowed valid nullifier cannot ride a
//!   substituted choice.
//!
//! ## Both-polarity guarantees (the tests at the bottom)
//!
//! - TRUE: a sealed auction opens at quorum and the winner is provable; a sealed
//!   ballot tallies correctly at quorum.
//! - FALSE (the cliff): a sub-threshold coalition — INCLUDING the collector
//!   holding every sealed submission — opens NOTHING, so it cannot front-run a
//!   bid or bias a tally early.
//! - FALSE (phase gate): a reveal attempted before the window CLOSES is refused;
//!   a submission after close is refused. The phase is a real gate, not decor.
//! - FALSE (binding): a submission cannot be swapped after collection — the
//!   submission set is fingerprinted into the ceremony transcript, so a tampered
//!   set is caught at reveal.
//! - FALSE (ballot substitution): an unlinkable ballot's eligibility nullifier is
//!   sealed INTO its plaintext (covered by the AEAD tag) and re-verified at tally
//!   against the dedup'd public copy, so a valid borrowed nullifier cannot be
//!   paired with a substituted choice — the mismatch is `NullifierMismatch`.

use crate::council_seal::{Council, CouncilSealError, OpenContribution, SealedPayload, seal};
use dregg_federation::beacon::BeaconCommittee;

/// Domain tag for a ceremony's submission-set fingerprint (the anti-swap tooth).
const TRANSCRIPT_CONTEXT: &str = "dregg-sealed-governance:transcript v1";
/// Domain tag for an unlinkable ballot's eligibility-token nullifier.
const NULLIFIER_CONTEXT: &str = "dregg-sealed-governance:nullifier v1";

/// Where a ceremony is in its commit→reveal lifecycle. The gate that makes
/// "no reveal before close" enforceable rather than decorative.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    /// The open submission window: sealed submissions are accepted; NOTHING
    /// opens (the council does not contribute until close).
    Collecting,
    /// The window is CLOSED: no new submissions; the quorum opens the collected
    /// set and the outcome is computed.
    Revealing,
}

/// Errors a sealed-governance ceremony can raise.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GovernanceError {
    /// A seal failed to open at the reveal boundary (forwarded from the seal
    /// organ): below quorum (`BelowThreshold` — the cliff), a tampered seal, or
    /// wrong council/label (`OpenFailed`).
    Seal(CouncilSealError),
    /// A submission was attempted outside the `Collecting` phase, or a reveal
    /// outside `Revealing`. The phase gate, fail-closed.
    WrongPhase,
    /// The submission-set fingerprint at reveal does not match the transcript
    /// recorded at close — a submission was swapped/added/dropped after
    /// collection. The anti-swap tooth.
    TranscriptMismatch,
    /// A revealed payload did not decode to a valid ballot/bid (the council
    /// opened it, but the plaintext is malformed). Fail-closed: a malformed
    /// submission is dropped, never counted as a default value.
    MalformedSubmission,
    /// An unlinkable ballot re-used an eligibility nullifier (double-vote). The
    /// one-vote-per-eligibility tooth.
    DoubleVote,
    /// An unlinkable ballot's SEALED nullifier (bound into the seal plaintext and
    /// covered by the AEAD tag) does not match the public nullifier that was
    /// dedup-checked at collection. A nullifier↔ballot substitution: the attacker
    /// paired a valid (dedup-passing) public nullifier with a seal carrying a
    /// DIFFERENT (or no) nullifier and a substituted choice. The ballot-binding
    /// tooth — the opened ballot is rejected at tally, never counted.
    NullifierMismatch,
    /// A voter not on the election roster attempted to cast (no eligibility
    /// commitment `H(secret)` in the roster). The roster/eligibility tooth —
    /// refused at cast, before any seal is admitted ([`PolisElection::cast`]).
    Ineligible,
    /// The ceremony has no submissions to reveal.
    Empty,
}

impl std::fmt::Display for GovernanceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GovernanceError::Seal(e) => write!(f, "sealed-governance seal error: {e}"),
            GovernanceError::WrongPhase => {
                write!(f, "sealed-governance wrong phase for this action")
            }
            GovernanceError::TranscriptMismatch => {
                write!(
                    f,
                    "sealed-governance transcript mismatch: the submission set was altered"
                )
            }
            GovernanceError::MalformedSubmission => {
                write!(
                    f,
                    "sealed-governance malformed submission (opened, but not a valid bid/ballot)"
                )
            }
            GovernanceError::DoubleVote => {
                write!(f, "sealed-governance double vote (nullifier re-use)")
            }
            GovernanceError::NullifierMismatch => write!(
                f,
                "sealed-governance nullifier mismatch: the sealed ballot's bound nullifier does not match its claimed eligibility token (ballot substitution)"
            ),
            GovernanceError::Ineligible => write!(
                f,
                "sealed-governance ineligible voter: no roster eligibility commitment"
            ),
            GovernanceError::Empty => write!(f, "sealed-governance ceremony is empty"),
        }
    }
}

impl std::error::Error for GovernanceError {}

impl From<CouncilSealError> for GovernanceError {
    fn from(e: CouncilSealError) -> Self {
        GovernanceError::Seal(e)
    }
}

/// One collected sealed submission: the opaque payload plus a stable submission
/// id (the seal's own `seal_id`). The id lets a transcript pin the SET of
/// submissions without revealing any of them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Submission {
    /// The sealed payload — opaque below the council's quorum.
    pub sealed: SealedPayload,
}

impl Submission {
    /// The submission's stable public id (the seal's content fingerprint).
    pub fn id(&self) -> [u8; 32] {
        self.sealed.seal_id()
    }
}

/// The transcript fingerprint of a SET of submissions: a sorted blake3 fold over
/// their ids. Order-independent (sorting the ids first), so the collector cannot
/// bias the outcome by reordering; tamper-evident, so a swapped/added/dropped
/// submission changes the fingerprint and is caught at reveal.
fn transcript(submissions: &[Submission]) -> [u8; 32] {
    let mut ids: Vec<[u8; 32]> = submissions.iter().map(Submission::id).collect();
    ids.sort_unstable();
    let mut h = blake3::Hasher::new_derive_key(TRANSCRIPT_CONTEXT);
    h.update(&(ids.len() as u64).to_be_bytes());
    for id in &ids {
        h.update(id);
    }
    *h.finalize().as_bytes()
}

// =============================================================================
// Sealed-bid AUCTION
// =============================================================================

/// A bid: who is bidding (an opaque 32-byte party id) and the bid amount.
/// Sealed to the council, so the amount is hidden below quorum.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Bid {
    /// The bidder's party id (carried in the sealed plaintext, revealed only at
    /// quorum — so even the bidder set is hidden below `K`).
    pub bidder: [u8; 32],
    /// The bid amount.
    pub amount: u64,
}

impl Bid {
    /// Serialize a bid into the seal plaintext: `bidder ‖ amount` (40 bytes).
    fn to_plaintext(self) -> Vec<u8> {
        let mut v = Vec::with_capacity(40);
        v.extend_from_slice(&self.bidder);
        v.extend_from_slice(&self.amount.to_be_bytes());
        v
    }

    /// Parse a bid from a revealed plaintext. `None` if malformed (fail-closed —
    /// a malformed reveal is DROPPED, never counted as a zero bid).
    fn from_plaintext(bytes: &[u8]) -> Option<Bid> {
        if bytes.len() != 40 {
            return None;
        }
        let mut bidder = [0u8; 32];
        bidder.copy_from_slice(&bytes[..32]);
        let amount = u64::from_be_bytes(bytes[32..40].try_into().ok()?);
        Some(Bid { bidder, amount })
    }
}

/// Seal a bid to an auction council under the auction's label. The bidder needs
/// ONLY the council's public committee — it cannot itself open the seal, and no
/// other bidder (nor the collector) can peek. `seed` is the bidder's local
/// entropy (a production bidder draws it from the OS).
pub fn seal_bid(
    committee: &BeaconCommittee,
    auction_label: &[u8],
    bid: Bid,
    seed: [u8; 32],
) -> Submission {
    Submission {
        sealed: seal(committee, auction_label, &bid.to_plaintext(), seed),
    }
}

/// A sealed-bid first-price auction: a council (the seal), a label (the auction
/// id / domain-separator), a phase, and the collected sealed bids.
pub struct SealedAuction {
    council: Council,
    label: Vec<u8>,
    phase: Phase,
    submissions: Vec<Submission>,
    /// The submission-set fingerprint recorded at CLOSE (the anti-swap anchor).
    /// `None` until [`SealedAuction::close`].
    closed_transcript: Option<[u8; 32]>,
}

impl SealedAuction {
    /// Open a fresh auction over a council, under a domain-separating `label`.
    pub fn new(council: Council, label: &[u8]) -> Self {
        Self {
            council,
            label: label.to_vec(),
            phase: Phase::Collecting,
            submissions: Vec::new(),
            closed_transcript: None,
        }
    }

    /// The public committee a bidder seals to.
    pub fn committee(&self) -> &BeaconCommittee {
        self.council.committee()
    }

    /// The auction label (domain-separator) bids must seal under.
    pub fn label(&self) -> &[u8] {
        &self.label
    }

    /// The current phase.
    pub fn phase(&self) -> Phase {
        self.phase
    }

    /// **COLLECT** a sealed bid. Only legal during `Collecting` (the window).
    /// The bid is opaque — the auction learns nothing about the amount until
    /// close. Fail-closed outside the window (`WrongPhase`).
    pub fn collect(&mut self, submission: Submission) -> Result<(), GovernanceError> {
        if self.phase != Phase::Collecting {
            return Err(GovernanceError::WrongPhase);
        }
        self.submissions.push(submission);
        Ok(())
    }

    /// **CLOSE** the submission window: `Collecting → Revealing`. Records the
    /// submission-set fingerprint as the anti-swap anchor. After this, no bid
    /// may be added (the gate) and the set is pinned (the tooth).
    pub fn close(&mut self) -> Result<(), GovernanceError> {
        if self.phase != Phase::Collecting {
            return Err(GovernanceError::WrongPhase);
        }
        self.closed_transcript = Some(transcript(&self.submissions));
        self.phase = Phase::Revealing;
        Ok(())
    }

    /// **REVEAL** the auction at quorum: the council OPENS every collected bid
    /// and the outcome is computed. Only legal after `close` (`Revealing`).
    ///
    /// `contributors` is the set of guardian slots forming the quorum (any
    /// `K`-subset). `beacon_randomness` is an unbiasable draw (e.g. from
    /// [`crate::beacon_cell`]) used ONLY to break exact ties — supplying it
    /// after close means no bidder could have aimed a tie to their advantage.
    ///
    /// Below `K` this returns `Seal(BelowThreshold)`: the cliff. A swapped set is
    /// `TranscriptMismatch`. A malformed reveal is DROPPED (never a phantom zero
    /// bid).
    pub fn reveal(
        &self,
        contributors: &[usize],
        beacon_randomness: [u8; 32],
    ) -> Result<AuctionOutcome, GovernanceError> {
        if self.phase != Phase::Revealing {
            return Err(GovernanceError::WrongPhase);
        }
        if self.submissions.is_empty() {
            return Err(GovernanceError::Empty);
        }
        // Anti-swap: the set being revealed MUST be the set that was closed.
        let now = transcript(&self.submissions);
        if self.closed_transcript != Some(now) {
            return Err(GovernanceError::TranscriptMismatch);
        }

        // Open every sealed bid at the quorum. The FIRST open exercises the cliff
        // for all of them (same council, same label): below K, this errors.
        let mut bids: Vec<(Bid, [u8; 32])> = Vec::with_capacity(self.submissions.len());
        for s in &self.submissions {
            let contribs: Vec<OpenContribution> = contributors
                .iter()
                .map(|&who| self.council.contribute_open(who, &s.sealed))
                .collect();
            let plaintext = self.council.open(&s.sealed, &contribs)?;
            // A malformed reveal is dropped (fail-closed), not counted as zero.
            if let Some(bid) = Bid::from_plaintext(&plaintext) {
                bids.push((bid, s.id()));
            }
        }
        if bids.is_empty() {
            return Err(GovernanceError::MalformedSubmission);
        }

        Ok(AuctionOutcome::recompute(bids, beacon_randomness))
    }
}

/// The provable outcome of a sealed auction: the opened bids and the winner.
/// Anyone can re-run [`AuctionOutcome::recompute`] over the opened bids and the
/// (after-close) beacon draw to confirm the winner — the outcome is a FUNCTION
/// of the revealed data, not an auctioneer's say-so.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AuctionOutcome {
    /// Every opened bid (bidder + amount), each tagged with its submission id.
    pub bids: Vec<(Bid, [u8; 32])>,
    /// The winning bid (highest amount; ties broken by the beacon draw).
    pub winner: Bid,
    /// The winning submission's id — the public link from outcome to the exact
    /// sealed submission that won.
    pub winner_id: [u8; 32],
}

impl AuctionOutcome {
    /// Recompute the winner from opened bids and an unbiasable tie-break draw.
    /// First-price: the highest amount wins. Exact ties are broken by ranking
    /// each tied bid's submission id XOR-folded with `beacon_randomness` — a
    /// draw no one could steer, because the randomness is fixed AFTER the seals
    /// are committed (the beacon cliff). Deterministic, so any verifier with the
    /// same opened bids + draw recomputes the identical winner.
    pub fn recompute(
        mut bids: Vec<(Bid, [u8; 32])>,
        beacon_randomness: [u8; 32],
    ) -> AuctionOutcome {
        debug_assert!(!bids.is_empty());
        // Stable canonical order first (by id) so the recompute is reproducible.
        bids.sort_by_key(|a| a.1);

        let tie_key = |id: &[u8; 32]| -> [u8; 32] {
            let mut k = [0u8; 32];
            for i in 0..32 {
                k[i] = id[i] ^ beacon_randomness[i];
            }
            k
        };

        let (winner, winner_id) = bids
            .iter()
            .max_by(|a, b| {
                a.0.amount
                    .cmp(&b.0.amount)
                    // tie-break on the unbiasable key (after-close draw)
                    .then_with(|| tie_key(&a.1).cmp(&tie_key(&b.1)))
            })
            .map(|(bid, id)| (*bid, *id))
            .expect("non-empty");

        AuctionOutcome {
            bids,
            winner,
            winner_id,
        }
    }
}

// =============================================================================
// Sealed BALLOT
// =============================================================================

/// A ballot: a choice index (which option the voter selects). Sealed to the
/// tally council so no official sees a vote before quorum.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Ballot {
    /// The selected option's index.
    pub choice: u32,
}

impl Ballot {
    /// Roster-bound plaintext: `choice` (4 bytes). The voter is bound externally
    /// (the roster c-list), so no nullifier travels in the seal.
    fn to_plaintext(self) -> Vec<u8> {
        self.choice.to_be_bytes().to_vec()
    }

    fn from_plaintext(bytes: &[u8]) -> Option<Ballot> {
        if bytes.len() != 4 {
            return None;
        }
        Some(Ballot {
            choice: u32::from_be_bytes(bytes.try_into().ok()?),
        })
    }

    /// Unlinkable plaintext: `choice` (4 bytes) ‖ `nullifier` (32 bytes) = 36
    /// bytes. The nullifier is sealed INTO the plaintext (covered by the AEAD
    /// tag), so it is opened-and-verified at tally — a substituted choice cannot
    /// ride a borrowed, valid nullifier. This format is DISTINCT from the
    /// roster-bound 4-byte format, so the two modes never alias.
    fn to_unlinkable_plaintext(self, nullifier: &[u8; 32]) -> Vec<u8> {
        let mut v = Vec::with_capacity(36);
        v.extend_from_slice(&self.choice.to_be_bytes());
        v.extend_from_slice(nullifier);
        v
    }

    /// Parse the unlinkable `(choice, bound_nullifier)` plaintext. `None` if
    /// malformed (fail-closed — a malformed reveal is dropped, never counted).
    fn from_unlinkable_plaintext(bytes: &[u8]) -> Option<(Ballot, [u8; 32])> {
        if bytes.len() != 36 {
            return None;
        }
        let choice = u32::from_be_bytes(bytes[..4].try_into().ok()?);
        let mut nullifier = [0u8; 32];
        nullifier.copy_from_slice(&bytes[4..36]);
        Some((Ballot { choice }, nullifier))
    }
}

/// Seal a roster-bound ballot to a tally council under the election's label.
/// For UNLINKABLE elections use [`seal_unlinkable_ballot`], which binds the
/// eligibility nullifier into the seal plaintext.
pub fn seal_ballot(
    committee: &BeaconCommittee,
    election_label: &[u8],
    ballot: Ballot,
    seed: [u8; 32],
) -> Submission {
    Submission {
        sealed: seal(committee, election_label, &ballot.to_plaintext(), seed),
    }
}

/// Seal an UNLINKABLE ballot: the eligibility `nullifier` is bound INTO the seal
/// plaintext (`choice ‖ nullifier`, covered by the AEAD tag). At tally the quorum
/// opens this and re-checks the bound nullifier against the public nullifier that
/// passed dedup at collection (`SealedBallot::tally`). This is what defeats
/// ballot substitution: a valid (dedup-passing) public nullifier cannot be paired
/// with a seal carrying a different/absent nullifier and a substituted choice —
/// the mismatch is caught at tally (`NullifierMismatch`). Returns the
/// [`UnlinkableSubmission`] ready to hand to [`SealedBallot::collect_unlinkable`].
pub fn seal_unlinkable_ballot(
    committee: &BeaconCommittee,
    election_label: &[u8],
    ballot: Ballot,
    nullifier: [u8; 32],
    seed: [u8; 32],
) -> UnlinkableSubmission {
    UnlinkableSubmission {
        submission: Submission {
            sealed: seal(
                committee,
                election_label,
                &ballot.to_unlinkable_plaintext(&nullifier),
                seed,
            ),
        },
        nullifier,
    }
}

/// An UNLINKABLE sealed ballot: the sealed ballot PLUS an anonymous eligibility
/// nullifier. The nullifier is `H(eligibility_secret ‖ election_label)` — it
/// proves the voter is eligible exactly ONCE for THIS election (re-use is
/// caught, `DoubleVote`) without naming the voter. After the quorum opens the
/// ballots, the tally has the CHOICE but not the identity: the opened ballot
/// carries only the nullifier, which is unlinkable to the eligibility secret
/// (one-way blake3) and unique per election.
///
/// CRITICAL: the `nullifier` here is the PUBLIC copy used for dedup at
/// collection; it is ALSO bound INSIDE `submission`'s sealed plaintext (via
/// [`seal_unlinkable_ballot`], covered by the AEAD tag). At tally the quorum
/// opens the seal and re-checks the bound nullifier against this public copy —
/// so a borrowed valid nullifier cannot be paired with a substituted ballot.
/// Construct via [`seal_unlinkable_ballot`], never by hand, so the two stay bound.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnlinkableSubmission {
    /// The sealed ballot — with the eligibility nullifier bound into its sealed
    /// plaintext (so it is opened-and-verified at tally).
    pub submission: Submission,
    /// The per-election eligibility nullifier (anonymous one-time spend token),
    /// public copy for collection-time dedup. Must equal the nullifier bound
    /// inside `submission` (enforced at tally).
    pub nullifier: [u8; 32],
}

/// Derive the per-election eligibility nullifier from a voter's eligibility
/// secret. Same secret + same election ⇒ same nullifier (double-vote caught);
/// different elections ⇒ different nullifiers (cross-election unlinkable); the
/// secret is not recoverable from the nullifier (one-way).
pub fn eligibility_nullifier(eligibility_secret: &[u8; 32], election_label: &[u8]) -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key(NULLIFIER_CONTEXT);
    h.update(eligibility_secret);
    h.update(&(election_label.len() as u64).to_be_bytes());
    h.update(election_label);
    *h.finalize().as_bytes()
}

/// A sealed-ballot election: a tally council, a label, a phase, and the
/// collected sealed ballots. The `unlinkable` flag selects whether ballots are
/// roster-bound (caller dedups voters externally) or carry anonymous
/// eligibility nullifiers (this ceremony dedups them — one vote per
/// eligibility, voter unlinked).
pub struct SealedBallot {
    council: Council,
    label: Vec<u8>,
    phase: Phase,
    submissions: Vec<Submission>,
    /// For the unlinkable mode: the spent nullifiers, parallel to `submissions`.
    /// Empty in roster-bound mode.
    nullifiers: Vec<[u8; 32]>,
    unlinkable: bool,
    closed_transcript: Option<[u8; 32]>,
}

impl SealedBallot {
    /// A roster-bound election: the caller guarantees one submission per
    /// registered voter (e.g. a polis council c-list). Ballots are sealed; no
    /// official peeks before quorum.
    pub fn new(council: Council, label: &[u8]) -> Self {
        Self {
            council,
            label: label.to_vec(),
            phase: Phase::Collecting,
            submissions: Vec::new(),
            nullifiers: Vec::new(),
            unlinkable: false,
            closed_transcript: None,
        }
    }

    /// An UNLINKABLE election: ballots carry anonymous eligibility nullifiers;
    /// THIS ceremony enforces one-vote-per-eligibility (double-vote caught at
    /// collection) while the opened ballot cannot be linked to the voter.
    pub fn new_unlinkable(council: Council, label: &[u8]) -> Self {
        let mut b = Self::new(council, label);
        b.unlinkable = true;
        b
    }

    /// The public committee a voter seals to.
    pub fn committee(&self) -> &BeaconCommittee {
        self.council.committee()
    }

    /// The election label.
    pub fn label(&self) -> &[u8] {
        &self.label
    }

    /// The current phase.
    pub fn phase(&self) -> Phase {
        self.phase
    }

    /// Whether this is an unlinkable election.
    pub fn is_unlinkable(&self) -> bool {
        self.unlinkable
    }

    /// **COLLECT** a roster-bound sealed ballot. Roster-bound mode only.
    /// Fail-closed outside `Collecting` (`WrongPhase`).
    pub fn collect(&mut self, submission: Submission) -> Result<(), GovernanceError> {
        if self.unlinkable {
            return Err(GovernanceError::WrongPhase);
        }
        if self.phase != Phase::Collecting {
            return Err(GovernanceError::WrongPhase);
        }
        self.submissions.push(submission);
        Ok(())
    }

    /// **COLLECT** an unlinkable sealed ballot, enforcing one-vote-per-
    /// eligibility. The nullifier is checked for re-use (`DoubleVote`) and
    /// recorded; the sealed ballot itself is opaque (the choice is hidden below
    /// quorum, AND the nullifier does not reveal the voter). Unlinkable mode
    /// only; fail-closed outside `Collecting`.
    ///
    /// Dedup here is only HALF the tooth: the recorded public nullifier is
    /// re-verified at [`SealedBallot::tally`] against the nullifier bound INSIDE
    /// the seal (use [`seal_unlinkable_ballot`] to construct the submission). A
    /// ballot whose sealed-in nullifier disagrees with this dedup'd copy is
    /// rejected at tally (`NullifierMismatch`) — so dedup-passing here does NOT by
    /// itself admit the choice; the binding closes the substitution gap.
    pub fn collect_unlinkable(
        &mut self,
        ballot: UnlinkableSubmission,
    ) -> Result<(), GovernanceError> {
        if !self.unlinkable {
            return Err(GovernanceError::WrongPhase);
        }
        if self.phase != Phase::Collecting {
            return Err(GovernanceError::WrongPhase);
        }
        if self.nullifiers.contains(&ballot.nullifier) {
            return Err(GovernanceError::DoubleVote);
        }
        self.nullifiers.push(ballot.nullifier);
        self.submissions.push(ballot.submission);
        Ok(())
    }

    /// **CLOSE** the voting window: `Collecting → Revealing`. Pins the ballot
    /// set's fingerprint (anti-swap).
    pub fn close(&mut self) -> Result<(), GovernanceError> {
        if self.phase != Phase::Collecting {
            return Err(GovernanceError::WrongPhase);
        }
        self.closed_transcript = Some(transcript(&self.submissions));
        self.phase = Phase::Revealing;
        Ok(())
    }

    /// **TALLY** the election at quorum: the council opens every ballot and the
    /// per-choice counts are computed. Only legal after `close`. Below `K` this
    /// is `Seal(BelowThreshold)` (the cliff — no early tally). A swapped set is
    /// `TranscriptMismatch`. A malformed ballot is DROPPED (never counted as a
    /// phantom choice 0).
    ///
    /// UNLINKABLE mode additionally re-verifies, for EVERY counted ballot, that
    /// the nullifier bound INSIDE the sealed plaintext matches the public
    /// nullifier that was dedup-checked at collection. A nullifier↔ballot
    /// substitution (a valid borrowed nullifier paired with a seal carrying a
    /// different/absent nullifier and a substituted choice) is REJECTED here with
    /// `NullifierMismatch` — fail-closed for the whole tally, so a substitution
    /// cannot slip a forged choice in alongside honest ballots. The bound check
    /// is what makes the collection-time dedup actually load-bearing at the count.
    pub fn tally(&self, contributors: &[usize]) -> Result<BallotOutcome, GovernanceError> {
        if self.phase != Phase::Revealing {
            return Err(GovernanceError::WrongPhase);
        }
        if self.submissions.is_empty() {
            return Err(GovernanceError::Empty);
        }
        let now = transcript(&self.submissions);
        if self.closed_transcript != Some(now) {
            return Err(GovernanceError::TranscriptMismatch);
        }

        let mut tallies: std::collections::BTreeMap<u32, u64> = std::collections::BTreeMap::new();
        let mut counted = 0u64;
        // `nullifiers` is position-parallel to `submissions` (both pushed together
        // in `collect_unlinkable`), and we iterate `submissions` in that same
        // insertion order, so index `i` lines a seal up with its public nullifier.
        for (i, s) in self.submissions.iter().enumerate() {
            let contribs: Vec<OpenContribution> = contributors
                .iter()
                .map(|&who| self.council.contribute_open(who, &s.sealed))
                .collect();
            let plaintext = self.council.open(&s.sealed, &contribs)?;
            if self.unlinkable {
                // The seal carries `choice ‖ bound_nullifier`. A malformed reveal
                // is dropped; a well-formed one whose bound nullifier disagrees
                // with the dedup'd public nullifier is a SUBSTITUTION — reject the
                // whole tally (fail-closed), never silently count the forged choice.
                match Ballot::from_unlinkable_plaintext(&plaintext) {
                    None => continue, // malformed: dropped, never a phantom choice
                    Some((ballot, bound_nullifier)) => {
                        let claimed = self
                            .nullifiers
                            .get(i)
                            .ok_or(GovernanceError::NullifierMismatch)?;
                        if &bound_nullifier != claimed {
                            return Err(GovernanceError::NullifierMismatch);
                        }
                        *tallies.entry(ballot.choice).or_insert(0) += 1;
                        counted += 1;
                    }
                }
            } else {
                // Roster-bound: a malformed ballot is dropped, never a phantom choice 0.
                if let Some(ballot) = Ballot::from_plaintext(&plaintext) {
                    *tallies.entry(ballot.choice).or_insert(0) += 1;
                    counted += 1;
                }
            }
        }
        if counted == 0 {
            return Err(GovernanceError::MalformedSubmission);
        }
        Ok(BallotOutcome { tallies, counted })
    }
}

/// The provable outcome of a sealed-ballot election: per-choice counts. Anyone
/// who saw the opened ballots can recompute it; the tally council cannot bias it
/// (every ballot is the unique threshold-opening of its seal).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BallotOutcome {
    /// Per-choice vote counts (choice index → count). Ordered (BTreeMap).
    pub tallies: std::collections::BTreeMap<u32, u64>,
    /// Total well-formed ballots counted.
    pub counted: u64,
}

impl BallotOutcome {
    /// The winning choice (most votes; ties broken toward the lower choice index
    /// for determinism). `None` if no votes.
    pub fn winner(&self) -> Option<u32> {
        self.tallies
            .iter()
            .max_by(|a, b| a.1.cmp(b.1).then_with(|| b.0.cmp(a.0)))
            .map(|(&choice, _)| choice)
    }
}

// =============================================================================
// PolisElection — the runnable governance APP: a roster-gated unlinkable election
// =============================================================================

/// Domain tag for a voter's roster eligibility commitment.
const ROSTER_CONTEXT: &str = "dregg-sealed-governance:roster v1";

/// A runnable polis election: an eligibility ROSTER (who may vote) WELDED onto
/// the unlinkable sealed-ballot ceremony ([`SealedBallot`]) and the unbiasable
/// beacon for sortition tie-breaks.
///
/// This is the governance APP the organs were built for. A citizen proves
/// eligibility by holding a secret whose commitment `H(secret)` is on the
/// roster; they cast an UNLINKABLE sealed ballot (an anonymous per-election
/// nullifier, not their identity, travels in the seal); the quorum tallies at
/// close. The four governance teeth all fail-closed:
///
/// - an INELIGIBLE voter (no roster commitment) is refused at cast
///   ([`PolisElection::cast`] returns [`GovernanceError::Ineligible`]);
/// - a DOUBLE VOTE (nullifier reuse) is refused at cast;
/// - an EARLY PEEK (sub-quorum tally) opens NOTHING (the common-secret cliff);
/// - a BALLOT SUBSTITUTION (a sealed nullifier disagreeing with the dedup'd
///   public one) is rejected at tally.
///
/// ## On-ledger lift (what the cell-program app commits)
///
/// Here the roster is a `Vec` of commitments so the ineligible-voter polarity
/// is exhibitable without the executor. The cell-program election cell commits
/// the roster as a Merkle ROOT and checks eligibility as an in-circuit
/// `MerkleMembership` witness (`cell/src/nullifier_set.rs`), so the tally leaves
/// a light-client receipt. The crypto and the nullifier semantics are identical;
/// the lift moves the roster check from this `contains` to a witnessed predicate.
pub struct PolisElection {
    /// Per-eligible-voter commitment `H(eligibility_secret)`. The on-ledger app
    /// stores the Merkle root of this set in the election cell's program.
    roster: Vec<[u8; 32]>,
    /// The unlinkable sealed-ballot ceremony this election drives.
    ballot: SealedBallot,
    /// The election label (domain separator for nullifiers + seals).
    label: Vec<u8>,
}

impl PolisElection {
    /// Open a roster-gated unlinkable election over a tally `council`, under
    /// `label`, with the given eligibility commitments (`Self::roster_commit`
    /// of each eligible voter's secret).
    pub fn new(council: Council, label: &[u8], roster: Vec<[u8; 32]>) -> Self {
        Self {
            roster,
            ballot: SealedBallot::new_unlinkable(council, label),
            label: label.to_vec(),
        }
    }

    /// The eligibility commitment for a voter's secret: `H(eligibility_secret)`.
    /// One-way (the secret is not recoverable) and the roster stores these, never
    /// the secrets themselves.
    pub fn roster_commit(secret: &[u8; 32]) -> [u8; 32] {
        let mut h = blake3::Hasher::new_derive_key(ROSTER_CONTEXT);
        h.update(secret);
        *h.finalize().as_bytes()
    }

    /// The public committee a voter seals to (no secret material).
    pub fn committee(&self) -> &BeaconCommittee {
        self.ballot.committee()
    }

    /// The election label.
    pub fn label(&self) -> &[u8] {
        &self.label
    }

    /// The current phase.
    pub fn phase(&self) -> Phase {
        self.ballot.phase()
    }

    /// **CAST** an eligible, unlinkable sealed vote. The ELIGIBILITY gate
    /// (roster membership) is checked FIRST — an ineligible voter is refused
    /// (`Ineligible`) before any seal is admitted. Then the unlinkable
    /// ceremony's nullifier dedup catches double-votes (`DoubleVote`). The
    /// opened ballot is unlinkable to the voter (only the anonymous nullifier
    /// travels in the seal).
    pub fn cast(
        &mut self,
        secret: &[u8; 32],
        choice: u32,
        seed: [u8; 32],
    ) -> Result<(), GovernanceError> {
        if !self.roster.contains(&Self::roster_commit(secret)) {
            return Err(GovernanceError::Ineligible);
        }
        let nullifier = eligibility_nullifier(secret, &self.label);
        let committee = self.ballot.committee().clone();
        let sealed =
            seal_unlinkable_ballot(&committee, &self.label, Ballot { choice }, nullifier, seed);
        self.ballot.collect_unlinkable(sealed)
    }

    /// **CLOSE** the voting window (`Collecting → Revealing`); pins the ballot
    /// set (anti-swap).
    pub fn close(&mut self) -> Result<(), GovernanceError> {
        self.ballot.close()
    }

    /// **TALLY** at quorum. Below `K` this is the cliff (`BelowThreshold`); a
    /// substitution is `NullifierMismatch`; otherwise the per-choice counts.
    pub fn tally(&self, quorum: &[usize]) -> Result<BallotOutcome, GovernanceError> {
        self.ballot.tally(quorum)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn council(seed: u8) -> Council {
        Council::genesis(5, 3, [seed; 32]).unwrap()
    }

    // -------------------------------------------------------------------------
    // Sealed-bid AUCTION
    // -------------------------------------------------------------------------

    /// TRUE polarity: a sealed auction opens at quorum and the winner is PROVABLE
    /// (recomputable from the opened bids).
    #[test]
    fn auction_reveals_and_winner_is_provable() {
        let mut auction = SealedAuction::new(council(11), b"auction:lot-7");
        let committee = auction.committee().clone();
        let label = auction.label().to_vec();

        let alice = Bid {
            bidder: [1u8; 32],
            amount: 100,
        };
        let bob = Bid {
            bidder: [2u8; 32],
            amount: 250,
        };
        let carol = Bid {
            bidder: [3u8; 32],
            amount: 175,
        };

        auction
            .collect(seal_bid(&committee, &label, alice, [10u8; 32]))
            .unwrap();
        auction
            .collect(seal_bid(&committee, &label, bob, [20u8; 32]))
            .unwrap();
        auction
            .collect(seal_bid(&committee, &label, carol, [30u8; 32]))
            .unwrap();

        auction.close().unwrap();

        let outcome = auction.reveal(&[0, 1, 2], [0u8; 32]).unwrap();
        assert_eq!(outcome.winner, bob, "highest bid (bob, 250) wins");
        assert_eq!(outcome.bids.len(), 3, "all three bids opened");

        // PROVABLE: an independent verifier recomputes the same winner from the
        // opened bids alone — no auctioneer say-so.
        let recheck = AuctionOutcome::recompute(outcome.bids.clone(), [0u8; 32]);
        assert_eq!(recheck.winner, outcome.winner);
        assert_eq!(recheck.winner_id, outcome.winner_id);

        // A DIFFERENT quorum subset opens to the SAME outcome (BLS uniqueness —
        // the subset cannot steer who wins).
        let outcome2 = auction.reveal(&[2, 3, 4], [0u8; 32]).unwrap();
        assert_eq!(outcome2.winner, bob);
        assert_eq!(outcome2.winner_id, outcome.winner_id);
    }

    /// FALSE polarity (THE CLIFF): a sub-threshold coalition — even one holding
    /// EVERY sealed bid (the collector) — opens NOTHING. No early peek, no
    /// front-running. This is `subThreshold_secret_blind` at the governance layer.
    #[test]
    fn subthreshold_coalition_cannot_peek_bids() {
        let mut auction = SealedAuction::new(council(22), b"auction:secret");
        let committee = auction.committee().clone();
        let label = auction.label().to_vec();
        auction
            .collect(seal_bid(
                &committee,
                &label,
                Bid {
                    bidder: [9u8; 32],
                    amount: 9999,
                },
                [1u8; 32],
            ))
            .unwrap();
        auction.close().unwrap();

        // 2 of 5 (below K=3) — the collector holds the sealed bid but cannot open it.
        let r = auction.reveal(&[0, 1], [0u8; 32]);
        assert_eq!(
            r.err(),
            Some(GovernanceError::Seal(CouncilSealError::BelowThreshold)),
            "a sub-threshold coalition (incl. the collector) cannot open ANY bid"
        );
        // A single guardian gets nothing either.
        assert_eq!(
            auction.reveal(&[2], [0u8; 32]).err(),
            Some(GovernanceError::Seal(CouncilSealError::BelowThreshold))
        );
    }

    /// FALSE polarity (PHASE GATE): a reveal before close is refused; a bid after
    /// close is refused. The phase is a real gate.
    #[test]
    fn auction_phase_gate_bites() {
        let mut auction = SealedAuction::new(council(33), b"auction:phase");
        let committee = auction.committee().clone();
        let label = auction.label().to_vec();
        let sub = seal_bid(
            &committee,
            &label,
            Bid {
                bidder: [5u8; 32],
                amount: 5,
            },
            [1u8; 32],
        );
        auction.collect(sub.clone()).unwrap();

        // Reveal before close: refused.
        assert_eq!(
            auction.reveal(&[0, 1, 2], [0u8; 32]).err(),
            Some(GovernanceError::WrongPhase),
            "cannot reveal before the window closes"
        );

        auction.close().unwrap();
        // Bid after close: refused.
        assert_eq!(
            auction.collect(sub).err(),
            Some(GovernanceError::WrongPhase),
            "cannot submit a bid after the window closes"
        );
        // Double close: refused.
        assert_eq!(auction.close().err(), Some(GovernanceError::WrongPhase));
    }

    /// FALSE polarity (ANTI-SWAP): a submission swapped after close is caught at
    /// reveal by the transcript fingerprint.
    #[test]
    fn auction_swapped_set_is_caught() {
        let mut auction = SealedAuction::new(council(44), b"auction:swap");
        let committee = auction.committee().clone();
        let label = auction.label().to_vec();
        auction
            .collect(seal_bid(
                &committee,
                &label,
                Bid {
                    bidder: [1u8; 32],
                    amount: 10,
                },
                [1u8; 32],
            ))
            .unwrap();
        auction.close().unwrap();

        // Forge a swapped set: replace the collected bid with a new (lower) one.
        let mut tampered = SealedAuction::new(council(44), b"auction:swap");
        tampered.phase = Phase::Revealing;
        tampered.closed_transcript = auction.closed_transcript; // pin the ORIGINAL fingerprint
        tampered.submissions = vec![seal_bid(
            &committee,
            &label,
            Bid {
                bidder: [1u8; 32],
                amount: 1,
            },
            [9u8; 32],
        )];

        assert_eq!(
            tampered.reveal(&[0, 1, 2], [0u8; 32]).err(),
            Some(GovernanceError::TranscriptMismatch),
            "a submission swapped after close is caught at reveal"
        );
    }

    /// Determinism + unbiasable tie-break: two EQUAL top bids are resolved by the
    /// after-close beacon draw — deterministically, so any verifier agrees, and
    /// the SAME draw always picks the same winner.
    #[test]
    fn auction_ties_broken_by_beacon() {
        let mut auction = SealedAuction::new(council(55), b"auction:tie");
        let committee = auction.committee().clone();
        let label = auction.label().to_vec();
        let a = Bid {
            bidder: [1u8; 32],
            amount: 500,
        };
        let b = Bid {
            bidder: [2u8; 32],
            amount: 500,
        };
        auction
            .collect(seal_bid(&committee, &label, a, [1u8; 32]))
            .unwrap();
        auction
            .collect(seal_bid(&committee, &label, b, [2u8; 32]))
            .unwrap();
        auction.close().unwrap();

        let draw = [0x5au8; 32];
        let o1 = auction.reveal(&[0, 1, 2], draw).unwrap();
        let o2 = auction.reveal(&[2, 3, 4], draw).unwrap();
        // Same draw ⇒ same winner regardless of quorum subset.
        assert_eq!(
            o1.winner, o2.winner,
            "the tie-break is a function of the draw"
        );
        assert!(o1.winner == a || o1.winner == b);
        // Recompute agrees.
        assert_eq!(
            AuctionOutcome::recompute(o1.bids.clone(), draw).winner,
            o1.winner
        );
    }

    /// A malformed reveal (a non-bid plaintext sealed under the auction label) is
    /// DROPPED — never counted as a zero bid. (Here: a single malformed seal ⇒
    /// the reveal reports MalformedSubmission rather than a phantom winner.)
    #[test]
    fn auction_malformed_reveal_dropped() {
        let mut auction = SealedAuction::new(council(66), b"auction:malformed");
        let committee = auction.committee().clone();
        // A seal of a 3-byte payload — not a 40-byte bid.
        auction
            .collect(Submission {
                sealed: seal(&committee, b"auction:malformed", b"xyz", [7u8; 32]),
            })
            .unwrap();
        auction.close().unwrap();
        assert_eq!(
            auction.reveal(&[0, 1, 2], [0u8; 32]).err(),
            Some(GovernanceError::MalformedSubmission),
            "a malformed reveal is dropped, never a phantom zero bid"
        );
    }

    // -------------------------------------------------------------------------
    // Sealed BALLOT
    // -------------------------------------------------------------------------

    /// TRUE polarity: a sealed ballot tallies correctly at quorum, and the
    /// winning choice is provable.
    #[test]
    fn ballot_tallies_at_quorum() {
        let mut election = SealedBallot::new(council(77), b"election:budget");
        let committee = election.committee().clone();
        let label = election.label().to_vec();

        // 3 votes for choice 1, 2 votes for choice 0.
        for (i, choice) in [1u32, 1, 1, 0, 0].iter().enumerate() {
            let seed = [(i as u8) + 1; 32];
            election
                .collect(seal_ballot(
                    &committee,
                    &label,
                    Ballot { choice: *choice },
                    seed,
                ))
                .unwrap();
        }
        election.close().unwrap();

        let outcome = election.tally(&[0, 1, 2]).unwrap();
        assert_eq!(outcome.counted, 5);
        assert_eq!(outcome.tallies.get(&1), Some(&3));
        assert_eq!(outcome.tallies.get(&0), Some(&2));
        assert_eq!(outcome.winner(), Some(1), "choice 1 wins with 3 votes");
    }

    /// FALSE polarity (THE CLIFF): a sub-threshold coalition cannot tally early —
    /// no early bias.
    #[test]
    fn ballot_subthreshold_cannot_tally() {
        let mut election = SealedBallot::new(council(88), b"election:secret");
        let committee = election.committee().clone();
        let label = election.label().to_vec();
        election
            .collect(seal_ballot(
                &committee,
                &label,
                Ballot { choice: 1 },
                [1u8; 32],
            ))
            .unwrap();
        election.close().unwrap();
        assert_eq!(
            election.tally(&[0, 1]).err(),
            Some(GovernanceError::Seal(CouncilSealError::BelowThreshold)),
            "a sub-threshold coalition cannot tally early"
        );
    }

    /// UNLINKABLE extension: an unlinkable ballot tallies the CHOICE at quorum
    /// while the opened ballot carries only an anonymous nullifier — the vote is
    /// not linkable to the voter's eligibility secret.
    #[test]
    fn unlinkable_ballot_tallies_without_linking_voter() {
        let mut election = SealedBallot::new_unlinkable(council(99), b"election:anon");
        let committee = election.committee().clone();
        let label = election.label().to_vec();

        // Three eligible voters with distinct secrets.
        for (i, (secret, choice)) in [([10u8; 32], 2u32), ([20u8; 32], 2), ([30u8; 32], 5)]
            .iter()
            .enumerate()
        {
            let nullifier = eligibility_nullifier(secret, &label);
            let unlinkable = seal_unlinkable_ballot(
                &committee,
                &label,
                Ballot { choice: *choice },
                nullifier,
                [(i as u8) + 1; 32],
            );
            election.collect_unlinkable(unlinkable).unwrap();
        }
        election.close().unwrap();

        let outcome = election.tally(&[0, 1, 2]).unwrap();
        assert_eq!(outcome.counted, 3);
        assert_eq!(outcome.tallies.get(&2), Some(&2), "two votes for choice 2");
        assert_eq!(outcome.tallies.get(&5), Some(&1), "one vote for choice 5");

        // The nullifier does NOT reveal the voter: it is a one-way function of the
        // secret, and the same secret in a DIFFERENT election yields a different
        // nullifier (cross-election unlinkable).
        let n_here = eligibility_nullifier(&[10u8; 32], b"election:anon");
        let n_other = eligibility_nullifier(&[10u8; 32], b"election:other");
        assert_ne!(
            n_here, n_other,
            "nullifiers are per-election (cross-election unlinkable)"
        );
    }

    /// UNLINKABLE double-vote tooth: the SAME eligibility secret cannot vote
    /// twice in one election — the nullifier re-use is caught at collection.
    #[test]
    fn unlinkable_double_vote_rejected() {
        let mut election = SealedBallot::new_unlinkable(council(101), b"election:double");
        let committee = election.committee().clone();
        let label = election.label().to_vec();
        let secret = [42u8; 32];
        let nullifier = eligibility_nullifier(&secret, &label);

        election
            .collect_unlinkable(seal_unlinkable_ballot(
                &committee,
                &label,
                Ballot { choice: 0 },
                nullifier,
                [1u8; 32],
            ))
            .unwrap();
        // Same secret ⇒ same nullifier ⇒ rejected (one vote per eligibility).
        let again = election.collect_unlinkable(seal_unlinkable_ballot(
            &committee,
            &label,
            Ballot { choice: 1 },
            nullifier,
            [2u8; 32],
        ));
        assert_eq!(
            again.err(),
            Some(GovernanceError::DoubleVote),
            "one vote per eligibility — nullifier re-use is caught"
        );
    }

    /// BOTH-POLARITY (the ballot-substitution tooth): the nullifier is bound INTO
    /// the seal plaintext and re-verified at tally.
    ///
    /// TRUE: a genuine unlinkable ballot — built by `seal_unlinkable_ballot`, so
    /// its public nullifier equals its sealed-in nullifier — tallies under its
    /// real choice.
    ///
    /// FALSE (the attack from the bug report): an attacker pairs a VALID
    /// (dedup-passing) public nullifier with a hand-forged seal carrying a
    /// SUBSTITUTED `Ballot{choice:999}` and a DIFFERENT bound nullifier. Collection
    /// dedup accepts the public nullifier (it is fresh + valid), but at tally the
    /// opened seal's bound nullifier disagrees with the dedup'd public copy ⇒
    /// `NullifierMismatch`, the whole tally is rejected. The forged choice is
    /// NEVER counted. Before this fix the substitution tallied silently.
    #[test]
    fn unlinkable_ballot_substitution_rejected() {
        let label: &[u8] = b"election:substitution";

        // ---- TRUE polarity: genuine bound ballot tallies under its real choice.
        {
            let mut election = SealedBallot::new_unlinkable(council(110), label);
            let committee = election.committee().clone();
            let nullifier = eligibility_nullifier(&[7u8; 32], label);
            election
                .collect_unlinkable(seal_unlinkable_ballot(
                    &committee,
                    label,
                    Ballot { choice: 3 },
                    nullifier,
                    [1u8; 32],
                ))
                .unwrap();
            election.close().unwrap();
            let outcome = election.tally(&[0, 1, 2]).unwrap();
            assert_eq!(outcome.counted, 1);
            assert_eq!(
                outcome.tallies.get(&3),
                Some(&1),
                "genuine bound ballot tallies"
            );
        }

        // ---- FALSE polarity: a valid public nullifier paired with a seal that
        // binds a DIFFERENT nullifier and a substituted choice. The seal opens
        // fine (it is a valid seal), the public nullifier passes dedup, but the
        // bound nullifier ≠ the claimed one ⇒ tally rejects.
        {
            let mut election = SealedBallot::new_unlinkable(council(110), label);
            let committee = election.committee().clone();

            // The attacker holds (or observed) a valid eligibility nullifier.
            let valid_nullifier = eligibility_nullifier(&[7u8; 32], label);

            // They seal choice 999 but bind a WRONG nullifier inside the plaintext
            // (they cannot bind `valid_nullifier` without it being the real one —
            // here we model the seal carrying any nullifier other than the claimed),
            // then attach `valid_nullifier` as the public dedup token.
            let forged_inner = seal_unlinkable_ballot(
                &committee,
                label,
                Ballot { choice: 999 },
                [0xABu8; 32], // bound nullifier inside the seal: NOT valid_nullifier
                [9u8; 32],
            );
            let attack = UnlinkableSubmission {
                submission: forged_inner.submission, // seal binds 0xAB..
                nullifier: valid_nullifier,          // public claim: a valid token
            };

            // Collection accepts: the public nullifier is fresh + valid (dedup
            // cannot see inside the seal).
            election.collect_unlinkable(attack).unwrap();
            election.close().unwrap();

            // Tally REJECTS: the opened seal's bound nullifier (0xAB..) disagrees
            // with the dedup'd public nullifier (valid_nullifier).
            assert_eq!(
                election.tally(&[0, 1, 2]).err(),
                Some(GovernanceError::NullifierMismatch),
                "a nullifier↔ballot substitution is rejected at tally — choice 999 never counts"
            );
        }

        // ---- FALSE polarity (the EXACT bug-report shape): a seal made with the
        // OLD nullifier-unbound path (`seal_ballot`, choice 999) paired with a
        // valid public nullifier. Its plaintext is 4 bytes, not the 36-byte
        // bound format ⇒ dropped as malformed ⇒ the lone ballot count is 0 ⇒
        // MalformedSubmission, never a phantom choice-999 tally.
        {
            let mut election = SealedBallot::new_unlinkable(council(111), label);
            let committee = election.committee().clone();
            let valid_nullifier = eligibility_nullifier(&[8u8; 32], label);
            let unbound = UnlinkableSubmission {
                submission: seal_ballot(&committee, label, Ballot { choice: 999 }, [3u8; 32]),
                nullifier: valid_nullifier,
            };
            election.collect_unlinkable(unbound).unwrap();
            election.close().unwrap();
            assert_eq!(
                election.tally(&[0, 1, 2]).err(),
                Some(GovernanceError::MalformedSubmission),
                "an unbound (nullifier-not-sealed) ballot is dropped, never tallied as choice 999"
            );
        }
    }

    /// Mode discipline: roster-bound `collect` refuses on an unlinkable election
    /// and vice-versa (the two intake paths are not interchangeable).
    #[test]
    fn ballot_mode_discipline() {
        let mut roster = SealedBallot::new(council(102), b"e:r");
        let committee = roster.committee().clone();
        let bad = election_submission(&committee, b"e:r");
        // collect_unlinkable on a roster-bound election: refused.
        assert_eq!(
            roster
                .collect_unlinkable(UnlinkableSubmission {
                    submission: bad.clone(),
                    nullifier: [0u8; 32],
                })
                .err(),
            Some(GovernanceError::WrongPhase)
        );

        let mut anon = SealedBallot::new_unlinkable(council(103), b"e:a");
        let committee2 = anon.committee().clone();
        // collect (roster) on an unlinkable election: refused.
        assert_eq!(
            anon.collect(election_submission(&committee2, b"e:a")).err(),
            Some(GovernanceError::WrongPhase)
        );
    }

    fn election_submission(committee: &BeaconCommittee, label: &[u8]) -> Submission {
        seal_ballot(committee, label, Ballot { choice: 0 }, [7u8; 32])
    }

    // -------------------------------------------------------------------------
    // PolisElection — the roster-gated runnable governance app
    // -------------------------------------------------------------------------

    fn polis_fixture() -> (PolisElection, [[u8; 32]; 3]) {
        let council = council(7);
        let secrets = [[1u8; 32], [2u8; 32], [3u8; 32]];
        let roster: Vec<[u8; 32]> = secrets.iter().map(PolisElection::roster_commit).collect();
        (
            PolisElection::new(council, b"polis:budget-2026", roster),
            secrets,
        )
    }

    /// TRUE polarity: three eligible voters cast unlinkable sealed votes; the
    /// quorum tallies them; any quorum subset opens the SAME tally.
    #[test]
    fn polis_genuine_election_tallies() {
        let (mut e, s) = polis_fixture();
        e.cast(&s[0], 1, [10u8; 32]).unwrap();
        e.cast(&s[1], 1, [20u8; 32]).unwrap();
        e.cast(&s[2], 0, [30u8; 32]).unwrap();
        e.close().unwrap();

        let outcome = e.tally(&[0, 1, 2]).unwrap();
        assert_eq!(outcome.counted, 3);
        assert_eq!(outcome.winner(), Some(1), "choice 1 wins 2-1");

        // A DIFFERENT quorum subset opens to the SAME tally (BLS uniqueness).
        let outcome2 = e.tally(&[2, 3, 4]).unwrap();
        assert_eq!(outcome2.tallies, outcome.tallies);
    }

    /// FALSE polarity (eligibility tooth): a voter NOT on the roster is refused
    /// at cast, before any seal is admitted.
    #[test]
    fn polis_ineligible_voter_rejected() {
        let (mut e, _s) = polis_fixture();
        let stranger = [0xEEu8; 32]; // not in the roster
        assert_eq!(
            e.cast(&stranger, 1, [99u8; 32]).err(),
            Some(GovernanceError::Ineligible),
            "a non-roster voter cannot cast"
        );
        // The election is unaffected: a real voter still tallies.
        e.cast(&_s[0], 1, [10u8; 32]).unwrap();
        e.close().unwrap();
        assert_eq!(e.tally(&[0, 1, 2]).unwrap().counted, 1);
    }

    /// FALSE polarity (double-vote tooth): the same eligibility secret cannot
    /// vote twice — caught at cast.
    #[test]
    fn polis_double_vote_rejected() {
        let (mut e, s) = polis_fixture();
        e.cast(&s[0], 1, [10u8; 32]).unwrap();
        assert_eq!(
            e.cast(&s[0], 0, [11u8; 32]).err(),
            Some(GovernanceError::DoubleVote),
            "same secret ⇒ same nullifier ⇒ rejected"
        );
    }

    /// FALSE polarity (THE CLIFF): a sub-threshold tally opens NOTHING — no
    /// official peeks a running count before quorum.
    #[test]
    fn polis_early_peek_opens_nothing() {
        let (mut e, s) = polis_fixture();
        e.cast(&s[0], 1, [10u8; 32]).unwrap();
        e.cast(&s[1], 0, [20u8; 32]).unwrap();
        e.close().unwrap();
        assert_eq!(
            e.tally(&[0, 1]).err(),
            Some(GovernanceError::Seal(CouncilSealError::BelowThreshold)),
            "a sub-threshold coalition cannot tally early"
        );
    }
}
