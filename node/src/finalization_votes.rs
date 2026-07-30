//! Quorum finalization votes — the explicit signed-vote agreement layer.
//!
//! # Why this exists (the soundness gap it closes)
//!
//! The blocklace finality executor computes finality **unilaterally per node**:
//! each node runs `ordering::tau` over its own view of the DAG and decides "this
//! block is Ordered" on its own. At n=1 (solo) that is the whole story. At n≥2 a
//! node that has locally finalized a block cannot, from the DAG alone, *know*
//! that the rest of the committee agrees it is final — the DAG-derived ack count
//! (`FinalityTracker::record_ack`) is still a function of THIS node's view.
//!
//! This module adds the missing message exchange: when a node finalizes a
//! turn-bearing block locally (it reaches `Ordered`, which subsumes local
//! `Attested`), it gossips a **signed** [`FinalizationVote`] (carried as a
//! `BlocklaceGossipMessage::FinalizationVote` on the blocklace topic — the
//! proven-bidirectional dissemination channel). Every node collects votes keyed
//! by *distinct verified signer* and only declares a block **consensus-wide
//! Attested** once it holds `2f+1` distinct-signer votes for it. That is the
//! step from "I think it is final" to "a quorum has signed that it is final": a
//! portable, verifiable certificate of agreement rather than a per-node guess.
//!
//! The collector is a pure value (no I/O), so the threshold-gating logic is
//! exercised by unit tests without a running node (see the tests at the bottom).
//! The gossip wiring lives in [`crate::blocklace_sync`].

use std::collections::{HashMap, HashSet, VecDeque};

use dregg_blocklace::finality::{BlockId, FinalityLevel};

/// THEME-2 #5 RESOURCE BOUND — the default cap on how many outstanding vote
/// records a SINGLE committee member may occupy in the collector.
///
/// `record` accepts any hybrid-signed vote from an enrolled member over an
/// ATTACKER-CHOSEN `block_id` (the collector does not — and cannot cheaply —
/// require the block to exist in the local lace), so a single Byzantine member
/// can sign votes for unlimited fabricated `block_id`s, each a fresh `votes` map
/// entry. This caps that: a member may occupy at most this many outstanding vote
/// slots; the (cap+1)th evicts the member's OWN oldest *lonely, un-attested* vote
/// — a `block_id` NO OTHER member has voted for and that is not consensus-attested
/// (exactly the shape of a fabricated block: a real finalizing block draws votes
/// from many members and is never lonely). The eviction is isolated to the
/// over-budget member and never removes a vote another member cast, a vote for a
/// consensus-attested block, or a vote for a block more than one member shares —
/// so a legit block still reaches quorum on the honest supermajority even while a
/// Byzantine member is being trimmed (see the falsifier). Generous so honest
/// members never approach it in normal operation.
pub const MAX_VOTES_PER_MEMBER: usize = 4096;
use dregg_federation::frost::{MlDsaPublicKey, MlDsaSigningKey};
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};

/// A signed assertion by one committee member that it has locally finalized a
/// block to (at least) `level` over committed state root `merkle_root`.
///
/// The signature is over
/// [`dregg_types::finalization_vote_signing_message`] =
/// `dregg-finalization-vote-v3 || block_id || merkle_root`, so it binds the
/// voter to *this* block at *this* finalized state root. That `merkle_root`
/// binding (N3 committee-restart fix, `VOTE_DOMAIN` v1→v2) is what turns a
/// quorum of these votes INTO the restart anchor: the same signatures a full
/// node collects for consensus-wide attestation are, verbatim, the
/// `finalization_quorum` a committee node re-verifies on restart.
///
/// The `level` is retained as a struct field (the collector gates on
/// `>= Attested`) but is deliberately NOT part of the signed message: a
/// finalization vote is only ever emitted at `Ordered`, and `Attested`/`Ordered`
/// count identically toward quorum, so binding the level added no safety while
/// binding the `merkle_root` — the finalized state itself — is strictly
/// stronger and is what the restart anchor needs.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize, PartialEq, Eq)]
pub struct FinalizationVote {
    /// The block this vote attests.
    pub block_id: BlockId,
    /// The finality level the voter asserts (`Attested` or `Ordered`; a vote is
    /// only emitted once the block is at least locally `Attested`).
    pub level: FinalityLevel,
    /// The committed state root (`canonical_ledger_root` at finalization) this
    /// vote attests. Bound into the signed message so the vote is verifiably
    /// about a specific finalized state — a quorum of these IS the attested
    /// root's restart-anchor quorum.
    pub merkle_root: [u8; 32],
    /// The voter's federation Ed25519 public key (the committee identity, the
    /// same key space as `Block::creator`).
    pub voter: [u8; 32],
    /// Ed25519 signature over [`Self::signing_message`]. Wrapped in
    /// [`dregg_types::Signature`] for length-checked serde of the 64 bytes
    /// (serde derives only auto-cover arrays up to length 32).
    pub signature: dregg_types::Signature,
    /// ML-DSA-65 (FIPS 204) signature over the SAME [`Self::signing_message`] —
    /// the POST-QUANTUM half of the hybrid finalization vote. A quorum is
    /// counted only when BOTH this and `signature` verify (classical ∧ pq), so a
    /// quantum adversary that breaks ed25519 entirely still cannot forge
    /// finality. Bound to `frost::HYBRID_PQ_CTX`. ~3.3 KB; not part of the ed25519
    /// signed message (it signs the same canonical bytes independently).
    pub pq_signature: Vec<u8>,
    /// A per-EMISSION liveness counter that makes every (re-)emitted vote
    /// BYTE-UNIQUE — the same defence `BlocklaceGossipMessage::Frontier` uses.
    /// It is NOT part of the signed message: a re-emit of the same vote carries
    /// the SAME signature and voter (so distinct-signer counting is unchanged),
    /// but a fresh `nonce` so the gossip layer's hash-dedup (`seen`) does not
    /// collapse the re-emit. Without it, a vote dropped on its first delivery
    /// (consumed into the receiver's `seen` before dispatch, or lost to the
    /// one-shot eager-push race) can NEVER be re-delivered: every byte-identical
    /// re-emit hashes the same and is dropped at the `seen` gate. The nonce
    /// defeats that so the catch-up re-emit actually reaches a peer that missed
    /// the vote, letting it cross quorum.
    pub nonce: u64,
}

impl FinalizationVote {
    /// The exact bytes a vote signs / verifies against: the shared
    /// [`dregg_types::finalization_vote_signing_message`] over the block id and
    /// the finalized `merkle_root`. Using the shared builder makes these bytes
    /// byte-identical to what the persistence layer reconstructs in
    /// `StoredAttestedRoot::verify_finalization_quorum`, so a gossiped vote's
    /// signature is a valid persisted quorum signature with no format drift.
    pub fn signing_message(block_id: &BlockId, merkle_root: &[u8; 32]) -> Vec<u8> {
        dregg_types::finalization_vote_signing_message(&block_id.0, merkle_root)
    }

    /// Construct a signed vote for `block_id` at `level` over finalized state
    /// root `merkle_root`, using `signing_key`. Each call stamps a fresh
    /// liveness `nonce` so re-emissions are byte-unique (see the `nonce` field);
    /// the nonce is outside the signed message.
    pub fn sign(
        signing_key: &SigningKey,
        pq_key: &MlDsaSigningKey,
        block_id: BlockId,
        level: FinalityLevel,
        merkle_root: [u8; 32],
    ) -> Option<Self> {
        let msg = Self::signing_message(&block_id, &merkle_root);
        let sig: Signature = signing_key.sign(&msg);
        // ML-DSA-65 over the SAME canonical bytes (the post-quantum half). Fails
        // only on an OS-entropy failure during hedged signing — treat as a
        // transient inability to vote (the caller skips this emission).
        let pq_signature = pq_key.sign(&msg)?;
        Some(FinalizationVote {
            block_id,
            level,
            merkle_root,
            voter: signing_key.verifying_key().to_bytes(),
            signature: dregg_types::Signature(sig.to_bytes()),
            pq_signature,
            nonce: fresh_nonce(),
        })
    }

    /// Verify the ed25519 (CLASSICAL) half only, against the declared `voter`
    /// key. Retained for the restart-anchor path; consensus quorum counting uses
    /// [`Self::verify_hybrid`], which additionally checks the post-quantum half.
    pub fn verify(&self) -> bool {
        let Ok(vk) = VerifyingKey::from_bytes(&self.voter) else {
            return false;
        };
        let sig = Signature::from_bytes(&self.signature.0);
        let msg = Self::signing_message(&self.block_id, &self.merkle_root);
        vk.verify_strict(&msg, &sig).is_ok()
    }

    /// Verify the ML-DSA-65 (POST-QUANTUM) half against the voter's committee PQ
    /// key `pq_pubkey`, over the same canonical bytes.
    pub fn verify_pq(&self, pq_pubkey: &MlDsaPublicKey) -> bool {
        let msg = Self::signing_message(&self.block_id, &self.merkle_root);
        pq_pubkey.verify(&msg, &self.pq_signature)
    }

    /// Full HYBRID verification: `classical ∧ pq`. A vote counts toward quorum
    /// only when BOTH halves verify, so breaking ed25519 alone cannot forge
    /// finality. `pq_pubkey` is the voter's ML-DSA-65 committee key.
    pub fn verify_hybrid(&self, pq_pubkey: &MlDsaPublicKey) -> bool {
        self.verify() && self.verify_pq(pq_pubkey)
    }
}

/// A strictly-monotonic per-process counter stamped into each emitted vote so
/// repeated (re-emitted) votes are byte-unique and never collapse under the
/// gossip layer's hash-dedup. Mirrors `blocklace_sync::frontier_nonce`. Public
/// so re-emission / frontier-piggyback can stamp a fresh nonce onto a stored
/// signed vote without re-signing (the nonce is outside the signed message).
pub fn fresh_nonce() -> u64 {
    static VOTE_NONCE: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    VOTE_NONCE.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
}

/// Collects finalization votes and gates consensus-wide finality on a quorum of
/// distinct verified signers.
///
/// `committee` is the set of admissible signer keys (the federation members); a
/// vote whose `voter` is not in the committee is rejected, so a Sybil cannot
/// inflate a quorum. `quorum_threshold` is `2f+1 = supermajority_threshold(n)`.
///
/// The collector is monotone: once a block crosses the threshold it stays
/// consensus-attested, and recording the same signer twice for a block is a
/// no-op (distinct-signer counting). It holds no I/O and is fully unit-testable.
#[derive(Clone, Debug)]
pub struct VoteCollector {
    /// Admissible signers (committee members). Votes from non-members are dropped.
    committee: HashSet<[u8; 32]>,
    /// The committee's ML-DSA-65 keys, indexed by the member's ed25519 key — the
    /// POST-QUANTUM half of the hybrid quorum. `record` counts a vote only when
    /// its `pq_signature` verifies under the voter's key here (classical ∧ pq),
    /// so a quantum adversary who breaks ed25519 still cannot assemble a quorum.
    pq_committee: HashMap<[u8; 32], MlDsaPublicKey>,
    /// Quorum threshold (2f+1).
    quorum_threshold: usize,
    /// Per-block map of distinct member signer → the FIRST verified vote we
    /// recorded from that signer for the block: its `(signature, merkle_root)`.
    ///
    /// Retaining the signature bytes (not just the signer key) is the net-new
    /// data of the N3 committee-restart fix (Fix B): once a block crosses
    /// quorum, [`Self::assembled_quorum`] hands back the >=threshold
    /// `(voter, signature)` pairs so they can be persisted as the attested
    /// root's `finalization_quorum` and re-verified on restart. First-write-wins
    /// per signer means an equivocating member (a second, differing vote) cannot
    /// displace its counted vote or be counted twice.
    ///
    /// The stored triple is `(ed25519 signature, merkle_root, ML-DSA-65 pq
    /// signature)`: retaining `pq_signature` is what lets `assembled_quorum` hand
    /// back the HYBRID signature so the persisted quorum re-verifies BOTH halves
    /// on restart (the voter's ML-DSA pubkey is looked up from `pq_committee`).
    votes: HashMap<BlockId, HashMap<[u8; 32], (dregg_types::Signature, [u8; 32], Vec<u8>)>>,
    /// Blocks that have crossed the quorum threshold (consensus-wide Attested).
    attested: HashSet<BlockId>,
    /// THEME-2 #5 — per-member eviction bookkeeping: for each member, the
    /// `block_id`s it has an outstanding vote for, in insertion order (front =
    /// oldest). Bounded at `max_votes_per_member` per member by
    /// [`Self::enforce_member_cap`], which pops the oldest entry on overflow —
    /// dropping the underlying vote ONLY when that oldest entry is a lonely,
    /// un-attested (i.e. fabricated-shaped) vote, else merely un-tracking a
    /// safe/attested/shared vote from the eviction queue. Keyed by member, so the
    /// index can never exceed `max_votes_per_member × committee_size`.
    voted_blocks: HashMap<[u8; 32], VecDeque<BlockId>>,
    /// The per-member outstanding-vote cap (defaults to [`MAX_VOTES_PER_MEMBER`]).
    max_votes_per_member: usize,
}

/// The outcome of recording one vote.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RecordOutcome {
    /// The vote was rejected (bad signature, non-member signer).
    Rejected,
    /// The vote was counted but the block has not yet reached quorum.
    Counted { distinct_votes: usize },
    /// The vote was counted AND the block JUST crossed the quorum threshold on
    /// this vote (the consensus-wide Attested transition fires exactly once).
    ReachedQuorum { distinct_votes: usize },
    /// The vote was counted and the block was ALREADY consensus-attested (a
    /// later confirming vote; idempotent).
    AlreadyQuorum { distinct_votes: usize },
}

impl VoteCollector {
    /// Build a collector for the given committee (ed25519 signer set + aligned
    /// ML-DSA-65 key map) and quorum threshold.
    pub fn new(
        committee: impl IntoIterator<Item = [u8; 32]>,
        pq_committee: HashMap<[u8; 32], MlDsaPublicKey>,
        quorum_threshold: usize,
    ) -> Self {
        VoteCollector {
            committee: committee.into_iter().collect(),
            pq_committee,
            quorum_threshold,
            votes: HashMap::new(),
            attested: HashSet::new(),
            voted_blocks: HashMap::new(),
            max_votes_per_member: MAX_VOTES_PER_MEMBER,
        }
    }

    /// Override the per-member outstanding-vote cap (THEME-2 #5). Builder-style;
    /// the default is [`MAX_VOTES_PER_MEMBER`]. Lower values let tests exercise the
    /// eviction path without thousands of real hybrid signatures.
    pub fn with_vote_cap(mut self, cap: usize) -> Self {
        self.max_votes_per_member = cap.max(1);
        self
    }

    /// THEME-2 #5 — the number of distinct `block_id`s currently tracked (the
    /// collector's `votes`-map footprint). Bounded by the per-member cap times the
    /// committee size plus the honest chain's in-flight blocks.
    pub fn tracked_block_count(&self) -> usize {
        self.votes.len()
    }

    /// THEME-2 #5 — record that `member` cast a fresh vote for `new_block`, and
    /// enforce the per-member cap. On overflow, pop the member's OLDEST tracked
    /// block and, if that block is a lonely (single-voter) un-attested vote,
    /// evict the underlying vote; an attested / multi-voter / already-gone entry
    /// is only un-tracked (its vote is retained — it is either consensus-valuable
    /// or amortized across other voters, never the fabricated-flood vector).
    /// Exactly one queue slot is freed per overflow, so the queue length can never
    /// exceed the cap, and only a member's own lonely-un-attested vote is ever
    /// dropped — never a vote needed to reach or persist a quorum.
    fn enforce_member_cap(&mut self, member: [u8; 32], new_block: BlockId) {
        {
            let dq = self.voted_blocks.entry(member).or_default();
            dq.push_back(new_block);
            if dq.len() <= self.max_votes_per_member {
                return;
            }
        }
        while self
            .voted_blocks
            .get(&member)
            .is_some_and(|d| d.len() > self.max_votes_per_member)
        {
            let Some(oldest) = self
                .voted_blocks
                .get_mut(&member)
                .and_then(|d| d.pop_front())
            else {
                break;
            };
            let signers = self.votes.get(&oldest);
            let member_present = signers.is_some_and(|s| s.contains_key(&member));
            if !member_present || self.attested.contains(&oldest) {
                // Stale queue entry (vote already gone) or a consensus-attested
                // vote — un-track it for eviction; never drop an attested vote.
                continue;
            }
            let lonely = signers.is_some_and(|s| s.len() == 1);
            if lonely {
                // FABRICATED-FLOOD VICTIM: this member is the only voter for an
                // un-attested block — the exact shape of a signed vote over a
                // never-finalizing block_id. Drop it.
                if let Some(s) = self.votes.get_mut(&oldest) {
                    s.remove(&member);
                    if s.is_empty() {
                        self.votes.remove(&oldest);
                    }
                }
            }
            // Otherwise (shared, un-attested): a real block accruing a quorum from
            // several members — un-track from THIS member's eviction queue but
            // keep the vote (it is not the flood vector and is amortized).
        }
    }

    /// Replace the committee (e.g. after an epoch transition) without dropping
    /// already-accumulated votes; re-counting against the new membership happens
    /// implicitly on the next vote.
    pub fn set_committee(
        &mut self,
        committee: impl IntoIterator<Item = [u8; 32]>,
        pq_committee: HashMap<[u8; 32], MlDsaPublicKey>,
    ) {
        self.committee = committee.into_iter().collect();
        self.pq_committee = pq_committee;
    }

    /// LIVE EPOCH TRANSITION: atomically replace BOTH the admissible signer set
    /// AND the quorum threshold when a validator-set reconfiguration finalizes.
    ///
    /// A membership change shifts two coupled quantities at once — who may vote
    /// (the committee) and how many distinct votes finalize a block (the
    /// supermajority of the NEW count). Setting them together is what makes the
    /// new validator's votes count *and* the threshold track the new membership
    /// from the epoch boundary forward, in one step.
    ///
    /// MONOTONE-SAFE across the boundary: blocks already consensus-attested under
    /// the old committee STAY attested (the `attested` set is sticky); only future
    /// `record` calls gate on the new committee/threshold. The reconfiguration
    /// itself is authorized by the OLD committee's quorum (the constitution
    /// `apply_if_passed` gate + tau finality), so there is no instant in which an
    /// unattested committee holds finalization authority — the epoch-handoff
    /// no-gap property (`EpochReconfig.lean::epoch_handoff_no_gap`).
    pub fn reconfigure(
        &mut self,
        committee: impl IntoIterator<Item = [u8; 32]>,
        pq_committee: HashMap<[u8; 32], MlDsaPublicKey>,
        quorum_threshold: usize,
    ) {
        self.committee = committee.into_iter().collect();
        self.pq_committee = pq_committee;
        self.quorum_threshold = quorum_threshold;
    }

    /// The current admissible committee size (number of distinct signer keys).
    pub fn committee_size(&self) -> usize {
        self.committee.len()
    }

    /// Whether a given key is currently an admissible (committee) signer.
    pub fn is_committee_member(&self, key: &[u8; 32]) -> bool {
        self.committee.contains(key)
    }

    /// The ML-DSA-65 key this collector holds for `member`, if any. Used by the
    /// live epoch transition to CARRY a continuing member's PQ key across a
    /// reconfigure (e.g. our own locally-derived key on a bootstrap node that
    /// no genesis committee lists). `None` = this member's votes cannot count.
    pub fn pq_key(&self, member: &[u8; 32]) -> Option<&MlDsaPublicKey> {
        self.pq_committee.get(member)
    }

    /// The quorum threshold this collector enforces.
    pub fn quorum_threshold(&self) -> usize {
        self.quorum_threshold
    }

    /// Number of distinct member votes recorded for a block.
    pub fn vote_count(&self, block_id: &BlockId) -> usize {
        self.votes.get(block_id).map_or(0, |s| s.len())
    }

    /// Has the given signer already voted for this block? Used to gate
    /// re-broadcasting our OWN vote so an n-member committee emits exactly n
    /// votes per finalized block (no re-emit storm).
    pub fn has_voted(&self, block_id: &BlockId, signer: &[u8; 32]) -> bool {
        self.votes
            .get(block_id)
            .is_some_and(|s| s.contains_key(signer))
    }

    /// The assembled restart-anchor quorum for `block_id`, if a supermajority of
    /// distinct committee members have signed the SAME finalized `merkle_root`.
    ///
    /// Returns `Some((merkle_root, sigs))` where `sigs` is the set of
    /// [`dregg_persist::QuorumSignature`]s from `>= quorum_threshold` distinct
    /// committee signers who all attested `merkle_root` — exactly the record the
    /// persistence layer stores as `StoredAttestedRoot::finalization_quorum` and
    /// re-verifies via `verify_finalization_quorum`. Returns `None` while the
    /// quorum is still forming, or if the votes recorded for the block are split
    /// across roots (a fork) with no single root reaching the threshold.
    ///
    /// Each returned signature is HYBRID: it carries BOTH the ed25519 and the
    /// ML-DSA-65 half, PLUS the voter's ML-DSA-65 public key (looked up from the
    /// collector's `pq_committee`, option (a)), so the persisted quorum
    /// re-verifies the full hybrid on restart with no committee PQ-key history. A
    /// recorded signer whose ML-DSA key is no longer in `pq_committee` (e.g. after
    /// a reconfigure) is dropped from the assembled quorum — fail-closed: if that
    /// drops it below threshold, no quorum is produced.
    ///
    /// Only distinct signers who agree on ONE root count toward that root, so a
    /// genuine >=threshold quorum over the finalized state is required — this
    /// never fabricates a quorum a restart would then reject.
    pub fn assembled_quorum(
        &self,
        block_id: &BlockId,
    ) -> Option<([u8; 32], Vec<dregg_persist::QuorumSignature>)> {
        let signers = self.votes.get(block_id)?;
        // Group distinct signers by the root they attested; pick a root that a
        // supermajority of distinct signers agreed on.
        let mut by_root: HashMap<[u8; 32], Vec<dregg_persist::QuorumSignature>> = HashMap::new();
        for (voter, (sig, root, pq_sig)) in signers {
            // The voter's ML-DSA committee key rides ALONGSIDE the signature so
            // the persisted quorum re-verifies its PQ half self-contained.
            let Some(pq_pk) = self.pq_committee.get(voter) else {
                continue;
            };
            by_root
                .entry(*root)
                .or_default()
                .push(dregg_persist::QuorumSignature {
                    voter: dregg_types::PublicKey(*voter),
                    signature: sig.clone(),
                    ml_dsa_pubkey: pq_pk.0.to_vec(),
                    pq_signature: pq_sig.clone(),
                });
        }
        let (root, members) = by_root
            .into_iter()
            .find(|(_, members)| members.len() >= self.quorum_threshold)?;
        Some((root, members))
    }

    /// Has this block reached consensus-wide Attested (a quorum of distinct
    /// member signers)?
    pub fn is_consensus_attested(&self, block_id: &BlockId) -> bool {
        self.attested.contains(block_id)
    }

    /// All blocks that have reached consensus-wide Attested.
    pub fn consensus_attested(&self) -> impl Iterator<Item = &BlockId> {
        self.attested.iter()
    }

    /// Record a vote. The signature is verified and the signer must be a
    /// committee member; otherwise the vote is [`RecordOutcome::Rejected`] and
    /// nothing changes. A verified member vote is counted by distinct signer,
    /// and the outcome reports whether THIS vote crossed the quorum threshold.
    pub fn record(&mut self, vote: &FinalizationVote) -> RecordOutcome {
        // A vote must be at least Attested to count toward consensus-wide
        // attestation; a Bilateral/Local "vote" is not a finality assertion.
        if vote.level < FinalityLevel::Attested {
            return RecordOutcome::Rejected;
        }
        if !self.committee.contains(&vote.voter) {
            return RecordOutcome::Rejected;
        }
        // HYBRID: the voter must carry an ML-DSA committee key, and BOTH the
        // ed25519 and the ML-DSA halves must verify (classical ∧ pq). A vote
        // missing its PQ key or failing either half never counts toward quorum.
        let Some(pq_pubkey) = self.pq_committee.get(&vote.voter) else {
            return RecordOutcome::Rejected;
        };

        // ⚑ AN ALREADY-COUNTED (block, voter) PAIR IS INERT — DO NOT PAY FOR IT AGAIN.
        //
        // The tally below is FIRST-WRITE-WINS per signer (`or_insert`), so a second
        // copy of a (block_id, voter) pair cannot change `distinct_votes`, cannot
        // displace the stored signature, and cannot alter `verified_quorum_reached`.
        // Verifying it is pure waste — and it is not small waste: `verify_hybrid` is
        // ed25519 AND ML-DSA-65, and the ML-DSA half runs through the extracted Lean
        // verify core over the C ABI. Measured on hbox at n=4 on 2026-07-30: 376-1880
        // ms PER VOTE.
        //
        // And repeats are the OVERWHELMING majority of what arrives.
        // `reemit_pending_votes` re-broadcasts every pending vote once per cadence
        // tick for 30 sweeps, AND `frontier_votes` piggybacks the same set onto EVERY
        // outgoing frontier. `blocklace_sync`'s funnel scheduler dedupes standalone
        // `FinalizationVote` messages within a drained batch — but the frontier
        // piggyback bypasses that entirely and is the far bigger carrier: 8-19 votes
        // on EVERY inbound frontier, verified serially before `handle_frontier` even
        // runs. Measured: `Frontier` handling averaged 2889 ms (max 7264 ms) on the
        // ONE serial funnel consumer, 69 s of a 150 s run, which starved the
        // round-cohort block deliveries the supermajority gate needs and degraded
        // inter-round latency to 13 s -> 20 s -> 33 s -> 60 s until a client turn
        // could not close its wave inside any reasonable window.
        //
        // NOTHING ABOUT VERIFICATION IS RELAXED. Every vote that is ever COUNTED
        // still passes the identical hybrid check — this arm is reached only when a
        // verified vote from this signer for this block is ALREADY in the tally. The
        // outcomes returned are exactly the ones the full path would have returned
        // for the same inert repeat, so caller metrics are unchanged.
        if let Some(signers) = self.votes.get(&vote.block_id)
            && signers.contains_key(&vote.voter)
        {
            let distinct_votes = signers.len();
            return if self.attested.contains(&vote.block_id) {
                RecordOutcome::AlreadyQuorum { distinct_votes }
            } else {
                RecordOutcome::Counted { distinct_votes }
            };
        }

        if !vote.verify_hybrid(pq_pubkey) {
            return RecordOutcome::Rejected;
        }

        let signers = self.votes.entry(vote.block_id).or_default();
        // First-write-wins per signer: an equivocating member cannot displace
        // the vote already counted for it, nor be counted twice. Retain the
        // ML-DSA (pq) signature too, so the assembled quorum carries BOTH halves.
        let is_fresh = !signers.contains_key(&vote.voter);
        signers.entry(vote.voter).or_insert((
            vote.signature.clone(),
            vote.merkle_root,
            vote.pq_signature.clone(),
        ));
        let distinct_votes = signers.len();
        // THEME-2 #5: enforce the per-member outstanding-vote cap on a genuinely
        // new (voter, block) pair. A re-emit of an already-counted vote is inert
        // here (first-write-wins), so the cap tracks only fresh occupancy.
        if is_fresh {
            self.enforce_member_cap(vote.voter, vote.block_id);
        }
        let already = self.attested.contains(&vote.block_id);

        if already {
            return RecordOutcome::AlreadyQuorum { distinct_votes };
        }
        // TWIN-DELETION (#11): the AUTHORITATIVE consensus-attested decision is the VERIFIED
        // finalization-quorum rule (`Dregg2.Distributed.FinalizationQuorum.quorumRoot` — a
        // supermajority of DISTINCT signers agreeing on ONE finalized root, carried by the
        // `quorum_no_conflict` safety theorem), routed through the proven
        // `verified_finalization_quorum` export — NOT the bare `distinct_votes >= threshold` count,
        // which ignores root agreement (the "attested on distinct count while ignoring root
        // agreement" finding). `distinct_votes >= quorum_threshold` is a cheap NECESSARY pre-check
        // (below it no single root can reach threshold), so the verified gate is queried only when a
        // quorum could actually exist — no per-vote FFI below threshold.
        if distinct_votes >= self.quorum_threshold && self.verified_quorum_reached(&vote.block_id) {
            self.attested.insert(vote.block_id);
            RecordOutcome::ReachedQuorum { distinct_votes }
        } else {
            RecordOutcome::Counted { distinct_votes }
        }
    }

    /// Whether the VERIFIED finalization-quorum rule (`FinalizationQuorum.quorumRoot`) declares a
    /// consensus quorum for `block_id` — a supermajority of distinct committee signers agreeing on
    /// ONE finalized `merkle_root`. The block's already-deduped tally (first-write-wins per signer,
    /// exactly `record`'s `or_insert`) is marshalled to the Lean wire and decided by the proven
    /// `verified_finalization_quorum` export (`Ok(Some(root))` ⇒ quorum; `Ok(None)` ⇒ no quorum:
    /// split roots or below threshold).
    ///
    /// FAIL-CLOSED / labeled-unaudited when the archive lacks the export (`Err`): the Rust
    /// root-agreement sibling [`Self::assembled_quorum`] decides ONLY on a genuinely no-Lean build
    /// (`!finalization_quorum_available()` — a full node is refused to start on this at the `lib.rs`
    /// verified-consensus hard-check) or under the explicit `DREGG_ALLOW_UNVERIFIED_CONSENSUS=1`
    /// escape; otherwise NO quorum is declared. On the deployed verified-role node the export is
    /// present, so the bare-Rust twin never decides consensus attestation.
    fn verified_quorum_reached(&self, block_id: &BlockId) -> bool {
        let Some(wire) = self.marshal_quorum_wire(block_id) else {
            return false;
        };
        match dregg_lean_ffi::distributed_ffi::verified_finalization_quorum(&wire) {
            // The verified `quorumRoot` reached a supermajority on one root (consensus-attested).
            Ok(Some(_root)) => true,
            // The verified rule declined: below threshold, or votes split across roots (no fork
            // attestation) — `quorum_no_conflict` guarantees at most one root can ever cross.
            Ok(None) => false,
            // Archive lacks the finalization-quorum export.
            Err(_) => {
                if quorum_rust_fallback_allowed(
                    dregg_lean_ffi::distributed_ffi::finalization_quorum_available(),
                    allow_unverified_consensus(),
                ) {
                    // Labeled-unaudited (no-Lean build / operator opt-in): the Rust root-agreement
                    // sibling — the differential twin of `quorumRoot` — decides.
                    self.assembled_quorum(block_id).is_some()
                } else {
                    // FAIL CLOSED on a live full node: no verified quorum decision ⇒ no attestation.
                    false
                }
            }
        }
    }

    /// Marshal `block_id`'s deduped tally to the verified-quorum wire
    /// (`"n=<committee>;V=<signer>:<root>,..."`, the grammar `FinalizationQuorum.decodeQuorumWire`
    /// mirrors). `n` is the committee size (the Lean gate derives `superMajority(n)` from it — the
    /// SAME threshold `quorum_threshold` carries). Each distinct signer gets a unique wire id, and
    /// roots are interned to ids by first appearance; the decision depends only on which signers share
    /// a root (root EQUALITY), so any injective interning yields the identical verdict. `None` when
    /// no votes are recorded for the block. The tally is already committee-filtered (non-members are
    /// rejected in `record` before insertion) and deduped (first-write-wins per signer).
    fn marshal_quorum_wire(&self, block_id: &BlockId) -> Option<String> {
        let signers = self.votes.get(block_id)?;
        let mut root_ids: HashMap<[u8; 32], u64> = HashMap::new();
        let mut entries: Vec<String> = Vec::with_capacity(signers.len());
        for (signer_id, (_voter, (_sig, root, _pq))) in signers.iter().enumerate() {
            let next_root = root_ids.len() as u64;
            let root_id = *root_ids.entry(*root).or_insert(next_root);
            entries.push(format!("{signer_id}:{root_id}"));
        }
        Some(format!(
            "n={};V={}",
            self.committee.len(),
            entries.join(",")
        ))
    }
}

/// The `DREGG_ALLOW_UNVERIFIED_CONSENSUS` labeled-unaudited escape (the SAME variable the node's
/// startup marshal-only tripwire and verified-consensus hard-check read). Deciding the finalization
/// quorum with the un-verified Rust `VoteCollector` tally instead of the proven `quorumRoot` is a
/// DELIBERATE opt-in — `true` only when the operator set it to a truthy value.
fn allow_unverified_consensus() -> bool {
    matches!(
        std::env::var("DREGG_ALLOW_UNVERIFIED_CONSENSUS")
            .ok()
            .as_deref(),
        Some("1") | Some("true") | Some("TRUE") | Some("on") | Some("ON")
    )
}

/// TWIN-DELETION (#11): whether the Rust `VoteCollector` root-agreement decision may stand in for the
/// verified `quorumRoot` when the export is absent. Allowed ONLY on a genuinely no-Lean build
/// (`!finalization_quorum_available` — a full node is refused to start in this state at the `lib.rs`
/// hard-check unless opted in) OR under `DREGG_ALLOW_UNVERIFIED_CONSENSUS=1`. On a Lean-linked full
/// node the export is present, so this path is unreachable and the verified gate always decides.
fn quorum_rust_fallback_allowed(
    finalization_quorum_available: bool,
    allow_unverified: bool,
) -> bool {
    !finalization_quorum_available || allow_unverified
}

#[cfg(test)]
mod tests {
    use super::*;

    fn keypair(seed: u8) -> SigningKey {
        SigningKey::from_bytes(&[seed; 32])
    }

    fn pk(sk: &SigningKey) -> [u8; 32] {
        sk.verifying_key().to_bytes()
    }

    /// The seed's ML-DSA-65 keypair — derived from the SAME `[seed; 32]` bytes
    /// as the ed25519 key, exactly the production derivation (`genesis.rs`
    /// publishes the public half; `blocklace_sync` re-derives from `node.key`).
    fn pq_keypair(seed: u8) -> (MlDsaPublicKey, MlDsaSigningKey) {
        MlDsaSigningKey::from_seed(&[seed; 32])
    }

    /// Sign a HYBRID vote as the member with key seed `seed` (both halves).
    fn signed_vote(
        seed: u8,
        blk: BlockId,
        level: FinalityLevel,
        root: [u8; 32],
    ) -> FinalizationVote {
        let sk = keypair(seed);
        let pq = pq_keypair(seed);
        FinalizationVote::sign(&sk, &pq.1, blk, level, root)
            .expect("hedged ML-DSA signing fails only on an OS-entropy failure")
    }

    /// The (ed25519 committee, ML-DSA committee map) for a set of member
    /// seeds — index-aligned by construction, as genesis publishes them.
    fn committee_of(seeds: &[u8]) -> (Vec<[u8; 32]>, HashMap<[u8; 32], MlDsaPublicKey>) {
        let mut eds = Vec::with_capacity(seeds.len());
        let mut pq = HashMap::new();
        for &s in seeds {
            let ed = pk(&keypair(s));
            eds.push(ed);
            pq.insert(ed, pq_keypair(s).0);
        }
        (eds, pq)
    }

    /// A fixed finalized state root the votes in a test attest — all votes for
    /// the same block must agree on it to form a quorum (the real finalizer
    /// binds `canonical_ledger_root`).
    const TEST_ROOT: [u8; 32] = [0x5A; 32];

    #[test]
    fn vote_roundtrip_signs_and_verifies() {
        let sk = keypair(7);
        let (pq_pk, _) = pq_keypair(7);
        let v = signed_vote(7, BlockId([9; 32]), FinalityLevel::Ordered, TEST_ROOT);
        assert!(v.verify());
        assert!(v.verify_pq(&pq_pk));
        assert!(v.verify_hybrid(&pq_pk));
        assert_eq!(v.voter, pk(&sk));
    }

    #[test]
    fn tampered_vote_fails_verification() {
        let (pq_pk, _) = pq_keypair(7);
        let mut v = signed_vote(7, BlockId([9; 32]), FinalityLevel::Ordered, TEST_ROOT);
        // Flip the block id: NEITHER half matches the message any more.
        v.block_id = BlockId([10; 32]);
        assert!(!v.verify());
        assert!(!v.verify_pq(&pq_pk));
        assert!(!v.verify_hybrid(&pq_pk));
    }

    #[test]
    fn merkle_root_is_bound_into_the_signature() {
        // N3 fix: the finalized state root is in the signed message. A vote
        // whose `merkle_root` is rewritten no longer verifies — so a persisted
        // quorum signature is verifiably about a SPECIFIC finalized root. Both
        // hybrid halves sign the same canonical bytes, so BOTH break.
        let (pq_pk, _) = pq_keypair(7);
        let mut v = signed_vote(7, BlockId([9; 32]), FinalityLevel::Ordered, TEST_ROOT);
        assert!(v.verify_hybrid(&pq_pk));
        v.merkle_root = [0xFF; 32];
        assert!(
            !v.verify(),
            "rewriting the attested merkle_root breaks the ed25519 signature"
        );
        assert!(
            !v.verify_pq(&pq_pk),
            "rewriting the attested merkle_root breaks the ML-DSA signature"
        );
    }

    #[test]
    fn level_is_not_bound_and_downgrade_is_harmless() {
        // The level is NOT in the signed message (only >= Attested gates the
        // collector). Rewriting Ordered→Attested leaves both signatures valid
        // and the vote still counts — deliberate: both levels finalize
        // identically, and the security-bearing binding is the merkle_root,
        // not the level.
        let (pq_pk, _) = pq_keypair(7);
        let mut v = signed_vote(7, BlockId([9; 32]), FinalityLevel::Ordered, TEST_ROOT);
        v.level = FinalityLevel::Attested;
        assert!(v.verify_hybrid(&pq_pk));
    }

    /// THE HYBRID TEETH: a vote whose ML-DSA half is WRONG is rejected even
    /// though its ed25519 half is perfectly valid — the collector never counts
    /// a classical-only vote toward quorum (the quantum adversary who breaks
    /// ed25519 gains nothing).
    #[test]
    fn valid_ed25519_with_forged_pq_half_is_rejected() {
        let (eds, pq) = committee_of(&[1, 2]);
        let mut col = VoteCollector::new(eds, pq, 2);
        let blk = BlockId([7; 32]);

        let mut v = signed_vote(1, blk, FinalityLevel::Ordered, TEST_ROOT);
        // Corrupt the PQ half only: the ed25519 half REMAINS valid.
        v.pq_signature[0] ^= 0xFF;
        assert!(
            v.verify(),
            "precondition: the classical half alone still verifies"
        );
        assert_eq!(
            col.record(&v),
            RecordOutcome::Rejected,
            "a vote with a forged ML-DSA half must NEVER count, even with a valid ed25519 half"
        );
        assert_eq!(col.vote_count(&blk), 0);

        // An empty PQ signature is equally rejected.
        let mut v2 = signed_vote(2, blk, FinalityLevel::Ordered, TEST_ROOT);
        v2.pq_signature = Vec::new();
        assert!(v2.verify());
        assert_eq!(col.record(&v2), RecordOutcome::Rejected);
        assert_eq!(col.vote_count(&blk), 0);
    }

    /// FAIL-CLOSED: a committee with NO configured ML-DSA keys (hybrid
    /// unconfigured — the empty `known_federation_ml_dsa_keys` default) counts
    /// NO votes and forms NO quorum. There is no silent ed25519-only downgrade.
    #[test]
    fn missing_pq_committee_key_fail_closed() {
        let (eds, _) = committee_of(&[1, 2]);
        let mut col = VoteCollector::new(eds, HashMap::new(), 2);
        let blk = BlockId([7; 32]);

        let v = signed_vote(1, blk, FinalityLevel::Ordered, TEST_ROOT);
        assert!(v.verify_hybrid(&pq_keypair(1).0), "the vote itself is good");
        assert_eq!(
            col.record(&v),
            RecordOutcome::Rejected,
            "a member with no known ML-DSA key must not count toward quorum"
        );
        assert_eq!(col.vote_count(&blk), 0);
        assert!(!col.is_consensus_attested(&blk));
    }

    #[test]
    fn assembled_quorum_yields_the_persistable_committee_sigs() {
        // Once a supermajority of distinct members have signed the SAME finalized
        // root, the collector hands back exactly the (voter, signature) pairs the
        // persistence layer stores as `finalization_quorum` — and those sigs
        // verify against the shared preimage, so they re-anchor a restart.
        let (committee, pq) = committee_of(&[1, 2, 3]);
        let quorum = dregg_blocklace::ordering::supermajority_threshold(3); // = 3
        let mut col = VoteCollector::new(committee, pq, quorum);
        let blk = BlockId([42; 32]);

        // Below quorum: nothing to persist yet.
        col.record(&signed_vote(1, blk, FinalityLevel::Ordered, TEST_ROOT));
        col.record(&signed_vote(2, blk, FinalityLevel::Ordered, TEST_ROOT));
        assert!(col.assembled_quorum(&blk).is_none());

        // The third distinct signer completes the quorum.
        col.record(&signed_vote(3, blk, FinalityLevel::Ordered, TEST_ROOT));
        let (root, sigs) = col.assembled_quorum(&blk).expect("quorum assembled");
        assert_eq!(root, TEST_ROOT);
        assert_eq!(sigs.len(), 3);

        // The assembled sigs verify against the shared finalization-vote preimage
        // (i.e. they are valid persisted `finalization_quorum` signatures) — BOTH
        // the ed25519 half AND the carried ML-DSA-65 half (the hybrid quorum).
        let msg = dregg_types::finalization_vote_signing_message(&blk.0, &TEST_ROOT);
        for qs in &sigs {
            assert!(
                qs.voter.verify(&msg, &qs.signature),
                "assembled quorum ed25519 half must verify"
            );
            let pk_bytes: [u8; 1952] = qs
                .ml_dsa_pubkey
                .as_slice()
                .try_into()
                .expect("carried ML-DSA pubkey is 1952 bytes");
            assert!(
                MlDsaPublicKey(pk_bytes).verify(&msg, &qs.pq_signature),
                "assembled quorum ML-DSA half must verify against the carried pubkey"
            );
        }
    }

    #[test]
    fn assembled_quorum_requires_agreement_on_one_root() {
        // Distinct signers split across two different roots (a fork) — no single
        // root reaches the threshold, so NO quorum is assembled: the collector
        // never fabricates an anchor the restart would reject.
        let (committee, pq) = committee_of(&[1, 2, 3]);
        let quorum = dregg_blocklace::ordering::supermajority_threshold(3); // = 3
        let mut col = VoteCollector::new(committee, pq, quorum);
        let blk = BlockId([42; 32]);
        let root_x = [0x11; 32];
        let root_y = [0x22; 32];

        col.record(&signed_vote(1, blk, FinalityLevel::Ordered, root_x));
        col.record(&signed_vote(2, blk, FinalityLevel::Ordered, root_x));
        col.record(&signed_vote(3, blk, FinalityLevel::Ordered, root_y));
        // 2 for root_x, 1 for root_y — neither reaches 3.
        assert!(col.assembled_quorum(&blk).is_none());
    }

    /// THE PHASE-2 PROOF: votes drive consensus-wide agreement, gated at 2f+1
    /// distinct signers. A 3-member committee (quorum = supermajority(3) = 3)
    /// only marks a block consensus-attested once ALL three distinct, verified
    /// member votes land — not before, and Byzantine/duplicate votes do not
    /// shortcut it.
    #[test]
    fn quorum_of_distinct_signers_drives_consensus_attested() {
        let (committee, pq) = committee_of(&[1, 2, 3]);
        let quorum = dregg_blocklace::ordering::supermajority_threshold(3); // = 3
        let mut col = VoteCollector::new(committee, pq, quorum);

        let blk = BlockId([42; 32]);

        // First vote: counted, not yet quorum.
        let o1 = col.record(&signed_vote(1, blk, FinalityLevel::Ordered, TEST_ROOT));
        assert_eq!(o1, RecordOutcome::Counted { distinct_votes: 1 });
        assert!(!col.is_consensus_attested(&blk));

        // The SAME signer voting again does not advance the count.
        let dup = col.record(&signed_vote(1, blk, FinalityLevel::Attested, TEST_ROOT));
        assert_eq!(dup, RecordOutcome::Counted { distinct_votes: 1 });

        // Second distinct signer: still short of quorum (3).
        let o2 = col.record(&signed_vote(2, blk, FinalityLevel::Ordered, TEST_ROOT));
        assert_eq!(o2, RecordOutcome::Counted { distinct_votes: 2 });
        assert!(!col.is_consensus_attested(&blk));

        // Third distinct signer: crosses the quorum exactly here.
        let o3 = col.record(&signed_vote(3, blk, FinalityLevel::Ordered, TEST_ROOT));
        assert_eq!(o3, RecordOutcome::ReachedQuorum { distinct_votes: 3 });
        assert!(col.is_consensus_attested(&blk));
    }

    #[test]
    fn non_member_and_forged_votes_are_rejected() {
        let (committee, pq) = committee_of(&[1, 2]);
        let quorum = dregg_blocklace::ordering::supermajority_threshold(2); // = 2
        let mut col = VoteCollector::new(committee, pq, quorum);
        let blk = BlockId([7; 32]);

        // A non-member's well-formed hybrid vote is rejected and does not count.
        let outc = col.record(&signed_vote(99, blk, FinalityLevel::Ordered, TEST_ROOT));
        assert_eq!(outc, RecordOutcome::Rejected);
        assert_eq!(col.vote_count(&blk), 0);

        // A forged ed25519 signature from a member key is rejected (even though
        // the ML-DSA half is genuine — hybrid means BOTH halves must verify).
        let mut forged = signed_vote(1, blk, FinalityLevel::Ordered, TEST_ROOT);
        forged.signature = dregg_types::Signature([0u8; 64]);
        assert_eq!(col.record(&forged), RecordOutcome::Rejected);
        assert_eq!(col.vote_count(&blk), 0);

        // Two honest member votes reach quorum.
        assert!(matches!(
            col.record(&signed_vote(1, blk, FinalityLevel::Ordered, TEST_ROOT)),
            RecordOutcome::Counted { distinct_votes: 1 }
        ));
        assert!(matches!(
            col.record(&signed_vote(2, blk, FinalityLevel::Ordered, TEST_ROOT)),
            RecordOutcome::ReachedQuorum { distinct_votes: 2 }
        ));
        assert!(col.is_consensus_attested(&blk));

        // A further confirming vote after quorum is idempotent.
        let again = col.record(&signed_vote(1, blk, FinalityLevel::Attested, TEST_ROOT));
        assert!(matches!(again, RecordOutcome::AlreadyQuorum { .. }));
    }

    /// TWO-NODE SIMULATION: model the exact cross-node exchange the live node
    /// performs — each node signs its own vote for the SAME finalized block and
    /// gossips it; each node's collector records its own vote plus the peer's.
    /// Neither node is consensus-attested on its own vote alone; BOTH cross
    /// quorum exactly when they hold the other's vote too. This is the
    /// agreement property the gossip wiring delivers (here without the network),
    /// proving the vote-collection logic GATES consensus-wide finality on a
    /// genuine quorum of distinct signers — independent of the gossip transport.
    #[test]
    fn two_nodes_reach_consensus_attested_by_exchanging_votes() {
        let (committee, pq) = committee_of(&[11, 22]);
        let quorum = dregg_blocklace::ordering::supermajority_threshold(2); // = 2
        let blk = BlockId([77; 32]);

        // Each node has its own collector over the same committee.
        let mut node_a = VoteCollector::new(committee.clone(), pq.clone(), quorum);
        let mut node_b = VoteCollector::new(committee, pq, quorum);

        // Both finalize `blk` locally and sign their own HYBRID vote (the emit step).
        let vote_a = signed_vote(11, blk, FinalityLevel::Ordered, TEST_ROOT);
        let vote_b = signed_vote(22, blk, FinalityLevel::Ordered, TEST_ROOT);

        // Each records its OWN vote first.
        assert_eq!(
            node_a.record(&vote_a),
            RecordOutcome::Counted { distinct_votes: 1 }
        );
        assert_eq!(
            node_b.record(&vote_b),
            RecordOutcome::Counted { distinct_votes: 1 }
        );
        assert!(!node_a.is_consensus_attested(&blk));
        assert!(!node_b.is_consensus_attested(&blk));

        // Gossip exchange: A receives B's vote, B receives A's vote. Each now
        // holds 2 distinct signed votes → consensus-wide Attested on BOTH.
        assert_eq!(
            node_a.record(&vote_b),
            RecordOutcome::ReachedQuorum { distinct_votes: 2 }
        );
        assert_eq!(
            node_b.record(&vote_a),
            RecordOutcome::ReachedQuorum { distinct_votes: 2 }
        );
        assert!(node_a.is_consensus_attested(&blk));
        assert!(node_b.is_consensus_attested(&blk));
    }

    /// THE FUNNEL INVARIANT (the n=2 self-emit/gossip race fix): `record`
    /// returns `ReachedQuorum` EXACTLY ONCE — on whichever vote crosses the
    /// threshold — and `AlreadyQuorum` thereafter. This is the property
    /// `blocklace_sync::record_finalization_vote` relies on to fire the
    /// consensus-wide Attested transition exactly once whether the crossing vote
    /// is the node's OWN (self-emit) or the PEER's (received). The live bug was
    /// NOT here (the collector is correct) but in the node routing the self-vote
    /// through a path that DISCARDED this outcome — so when the peer's vote
    /// landed first, the self-record crossed quorum and the transition was
    /// swallowed. This test pins the contract that record surfaces the crossing
    /// on whichever vote is second, so BOTH funnel call-sites can act on it.
    #[test]
    fn quorum_crossing_is_reported_on_whichever_vote_is_second() {
        let (committee, pq) = committee_of(&[11, 22]);
        let quorum = dregg_blocklace::ordering::supermajority_threshold(2); // = 2
        let blk = BlockId([77; 32]);
        let vote_a = signed_vote(11, blk, FinalityLevel::Ordered, TEST_ROOT);
        let vote_b = signed_vote(22, blk, FinalityLevel::Ordered, TEST_ROOT);

        // Case 1: PEER vote first, then SELF vote crosses (the race that broke the
        // live node — the self-record was the threshold-crosser).
        let mut col = VoteCollector::new(committee.clone(), pq.clone(), quorum);
        assert_eq!(
            col.record(&vote_b),
            RecordOutcome::Counted { distinct_votes: 1 }
        );
        assert_eq!(
            col.record(&vote_a),
            RecordOutcome::ReachedQuorum { distinct_votes: 2 },
            "the SECOND distinct vote (here the self vote) must report the crossing"
        );
        // A confirming vote after the crossing is idempotent (AlreadyQuorum).
        assert!(matches!(
            col.record(&vote_b),
            RecordOutcome::AlreadyQuorum { .. }
        ));

        // Case 2: SELF vote first, then PEER vote crosses (the orientation that
        // already worked). The crossing is reported symmetrically.
        let mut col2 = VoteCollector::new(committee, pq, quorum);
        assert_eq!(
            col2.record(&vote_a),
            RecordOutcome::Counted { distinct_votes: 1 }
        );
        assert_eq!(
            col2.record(&vote_b),
            RecordOutcome::ReachedQuorum { distinct_votes: 2 }
        );
    }

    #[test]
    fn bilateral_level_votes_do_not_count() {
        let (committee, pq) = committee_of(&[1]);
        let mut col = VoteCollector::new(committee, pq, 1);
        let blk = BlockId([5; 32]);
        // A "vote" below Attested is not a finality assertion.
        let v = signed_vote(1, blk, FinalityLevel::Bilateral, TEST_ROOT);
        assert_eq!(col.record(&v), RecordOutcome::Rejected);
        assert_eq!(col.vote_count(&blk), 0);
    }

    /// LIVE EPOCH TRANSITION — ADD. Before the reconfigure, a vote from the
    /// newly-added validator is REJECTED (not yet a committee member). After the
    /// finalized membership change reconfigures the collector to the new
    /// committee + new threshold, that same validator's vote COUNTS, and the
    /// threshold has advanced to the supermajority of the larger set. This is the
    /// "the new validator's votes count from epoch N+1" property.
    #[test]
    fn reconfigure_admits_new_validator_and_advances_threshold() {
        let d = keypair(4); // the validator added live
        let blk = BlockId([42; 32]);

        // Epoch N: a 3-member committee, quorum = supermajority(3) = 3.
        let (c3, pq3) = committee_of(&[1, 2, 3]);
        let q3 = dregg_blocklace::ordering::supermajority_threshold(3);
        let mut col = VoteCollector::new(c3, pq3, q3);
        assert_eq!(col.quorum_threshold(), 3);
        assert!(!col.is_committee_member(&pk(&d)));

        // D is not yet a member: its vote is rejected and never counts.
        assert_eq!(
            col.record(&signed_vote(4, blk, FinalityLevel::Ordered, TEST_ROOT)),
            RecordOutcome::Rejected
        );
        assert_eq!(col.vote_count(&blk), 0);

        // Epoch N+1: the membership change finalized — reconfigure to the new
        // 4-member committee (ed25519 + ML-DSA keys), quorum = supermajority(4) = 3.
        let (c4, pq4) = committee_of(&[1, 2, 3, 4]);
        let q4 = dregg_blocklace::ordering::supermajority_threshold(4);
        col.reconfigure(c4, pq4, q4);
        assert_eq!(col.committee_size(), 4);
        assert_eq!(col.quorum_threshold(), 3);
        assert!(col.is_committee_member(&pk(&d)));

        // D's vote now counts toward consensus-wide finality.
        assert_eq!(
            col.record(&signed_vote(4, blk, FinalityLevel::Ordered, TEST_ROOT)),
            RecordOutcome::Counted { distinct_votes: 1 }
        );
    }

    /// LIVE EPOCH TRANSITION — REMOVE. After a validator is removed from the
    /// committee, its finalization vote no longer counts (Sybil/ghost protection:
    /// a departed member cannot keep contributing to quorum), and the quorum
    /// threshold shrinks to the supermajority of the smaller set.
    #[test]
    fn reconfigure_drops_removed_validator() {
        let d = keypair(4);
        let blk = BlockId([7; 32]);

        let (c4, pq4) = committee_of(&[1, 2, 3, 4]);
        let q4 = dregg_blocklace::ordering::supermajority_threshold(4);
        let mut col = VoteCollector::new(c4, pq4, q4);

        // Remove D: epoch N+1 committee is {a,b,c}, quorum = supermajority(3) = 3.
        let (c3, pq3) = committee_of(&[1, 2, 3]);
        let q3 = dregg_blocklace::ordering::supermajority_threshold(3);
        col.reconfigure(c3, pq3, q3);
        assert_eq!(col.committee_size(), 3);
        assert_eq!(col.quorum_threshold(), 3);
        assert!(!col.is_committee_member(&pk(&d)));

        // D (removed) can no longer contribute to quorum.
        assert_eq!(
            col.record(&signed_vote(4, blk, FinalityLevel::Ordered, TEST_ROOT)),
            RecordOutcome::Rejected
        );
        // The three continuing members still finalize.
        assert!(matches!(
            col.record(&signed_vote(1, blk, FinalityLevel::Ordered, TEST_ROOT)),
            RecordOutcome::Counted { distinct_votes: 1 }
        ));
        assert!(matches!(
            col.record(&signed_vote(2, blk, FinalityLevel::Ordered, TEST_ROOT)),
            RecordOutcome::Counted { distinct_votes: 2 }
        ));
        assert!(matches!(
            col.record(&signed_vote(3, blk, FinalityLevel::Ordered, TEST_ROOT)),
            RecordOutcome::ReachedQuorum { distinct_votes: 3 }
        ));
    }

    /// TWIN-DELETION (#11) FAIL-CLOSED gate: on a Lean-linked full node the Rust `VoteCollector`
    /// root-agreement twin is FORBIDDEN as the quorum decider (the verified `quorumRoot` export
    /// decides); it stands in ONLY on a genuinely no-Lean build (no `dregg_finalization_quorum`
    /// export, which a full node is refused to start on) or under the explicit
    /// `DREGG_ALLOW_UNVERIFIED_CONSENSUS` escape. Pins the exact gate `record` uses on the no-export
    /// branch.
    #[test]
    fn rust_quorum_twin_forbidden_on_verified_full_node() {
        // Live verified-role node: the verified `dregg_finalization_quorum` export IS linked, no
        // escape — the Rust twin must not decide, so a no-export branch would fail closed.
        assert!(
            !quorum_rust_fallback_allowed(true, false),
            "the Rust VoteCollector quorum twin must NEVER decide consensus attestation on a \
             Lean-linked full node without the escape"
        );
        // Deliberate opt-in: the Rust twin is a labeled fallback.
        assert!(quorum_rust_fallback_allowed(true, true));
        // Genuinely no-Lean build: the Rust root-agreement decision is the only decider available.
        assert!(quorum_rust_fallback_allowed(false, false));
        assert!(quorum_rust_fallback_allowed(false, true));
    }

    /// TWIN-DELETION (#11) — the LIVE `record()` decision now enforces ROOT AGREEMENT (the
    /// `quorum_no_conflict` safety property `quorumRoot` proves), not the bare distinct-signer count.
    /// Distinct signers split across two roots — enough distinct votes to clear the threshold count,
    /// but NO single root reaching it — must NOT mark the block consensus-attested. Before the twin
    /// deletion `record` marked attested on `distinct_votes >= threshold` alone (ignoring root
    /// agreement); now the attested transition routes through the verified quorum rule (here, under
    /// `no-lean-link`, its Rust root-agreement sibling), so the split does NOT attest and only a
    /// genuine single-root supermajority does.
    #[test]
    fn record_requires_root_agreement_not_bare_distinct_count() {
        // n=4, threshold superMajority(4) = 3.
        let (committee, pq) = committee_of(&[1, 2, 3, 4]);
        let quorum = dregg_blocklace::ordering::supermajority_threshold(4);
        assert_eq!(quorum, 3);
        let mut col = VoteCollector::new(committee, pq, quorum);
        let blk = BlockId([0xC0; 32]);
        let root_x = [0x11; 32];
        let root_y = [0x22; 32];

        // Three DISTINCT signers (>= threshold 3 by count) but SPLIT 2/1 across roots.
        assert!(matches!(
            col.record(&signed_vote(1, blk, FinalityLevel::Ordered, root_x)),
            RecordOutcome::Counted { distinct_votes: 1 }
        ));
        assert!(matches!(
            col.record(&signed_vote(2, blk, FinalityLevel::Ordered, root_x)),
            RecordOutcome::Counted { distinct_votes: 2 }
        ));
        let split = col.record(&signed_vote(3, blk, FinalityLevel::Ordered, root_y));
        assert_eq!(
            split,
            RecordOutcome::Counted { distinct_votes: 3 },
            "3 distinct signers split 2/1 across roots must NOT reach quorum — no single root has a \
             supermajority (the old bare-count `>= threshold` would have WRONGLY attested here)"
        );
        assert!(
            !col.is_consensus_attested(&blk),
            "root-split votes must never mark a block consensus-attested"
        );

        // A third signer AGREEING on root_x completes a genuine single-root supermajority.
        let crossed = col.record(&signed_vote(4, blk, FinalityLevel::Ordered, root_x));
        assert_eq!(
            crossed,
            RecordOutcome::ReachedQuorum { distinct_votes: 4 },
            "three distinct signers agreeing on ONE root (root_x) is the verified quorum"
        );
        assert!(col.is_consensus_attested(&blk));
    }

    /// PIECE-2B — THE NO-DRIFT DIFFERENTIAL. The Rust `VoteCollector`'s quorum
    /// decision (`assembled_quorum`: distinct signers per root >= superMajority)
    /// is the SAME decision `Dregg2.Distributed.FinalizationQuorum.quorumRoot`
    /// proves sound + conflict-free and `dregg_lean_ffi::
    /// verified_finalization_quorum` exports. This test ties them: many tallies
    /// — targeted edges (exactly-threshold, one-below, unanimous, split vote,
    /// duplicate signers, an equivocating signer, empty, n=1) plus deterministic
    /// pseudo-random ones — are driven through BOTH the real collector (real
    /// hybrid-signed votes) AND the verified Lean gate over the marshalled
    /// tally, asserting the decided root (or none) AGREES on every case. Drift
    /// between the hand-Rust decision and the proven Lean rule is a test
    /// failure, with NO per-vote FFI cost on the hot path (the differential is
    /// test-only; the collector stays pure Rust at runtime).
    ///
    /// MARSHALLING. The Lean wire (`decodeQuorumWire`) is
    /// `"n=<committee>;V=<signer>:<root>,..."` with `Sig = Root = Nat`; the
    /// documented wire contract is the collector's ALREADY-DEDUPED tally
    /// (first-write-wins per signer — exactly `record`'s `or_insert`). So the
    /// test interns the 32-byte keys/roots to stable u64 ids (signer = its pool
    /// index, root = its pool index) and applies the SAME first-write-wins
    /// dedup to the raw emission sequence it feeds the collector — the identical
    /// tally, two deciders. Self-skips when the archive lacks the export — unless
    /// `DREGG_TEST_REQUIRE_LEAN=1`, under which the absent export PANICS.
    #[test]
    fn quorum_decision_matches_verified_lean_gate() {
        if !dregg_lean_ffi::demand_lean(
            dregg_lean_ffi::distributed_ffi::finalization_quorum_available(),
            "the Lean finalization-quorum export (finalization_quorum_available()==false)",
        ) {
            return;
        }

        /// The root pool: stable id `r` ↔ the 32-byte root `[r+1; 32]`.
        fn root_hash(r: u64) -> [u8; 32] {
            [(r + 1) as u8; 32]
        }
        fn root_id(hash: &[u8; 32]) -> u64 {
            u64::from(hash[0]) - 1
        }

        /// Run ONE tally through both deciders and assert agreement.
        /// `votes` is the raw emission sequence of `(signer_index, root_id)`;
        /// signer index `i` is committee seed `i+1` and doubles as its interned
        /// wire id.
        fn check_case(n: usize, votes: &[(usize, u64)], label: &str) {
            let seeds: Vec<u8> = (1..=n as u8).collect();
            let (committee, pq) = committee_of(&seeds);
            let threshold = dregg_blocklace::ordering::supermajority_threshold(n);
            let mut col = VoteCollector::new(committee, pq, threshold);
            let blk = BlockId([0xEE; 32]);

            // Drive the REAL collector with real hybrid-signed votes.
            for &(signer, root) in votes {
                let outcome = col.record(&signed_vote(
                    seeds[signer],
                    blk,
                    FinalityLevel::Ordered,
                    root_hash(root),
                ));
                assert_ne!(
                    outcome,
                    RecordOutcome::Rejected,
                    "{label}: a genuine member vote must never be rejected"
                );
            }
            let rust_decision: Option<u64> = col
                .assembled_quorum(&blk)
                .map(|(root, _sigs)| root_id(&root));

            // Marshal the SAME tally for the verified Lean gate: first-write-wins
            // per signer (the collector's record contract = the documented wire
            // input), keys interned to their stable pool-index ids.
            let mut seen: HashSet<usize> = HashSet::new();
            let mut tally: Vec<(usize, u64)> = Vec::new();
            for &(signer, root) in votes {
                if seen.insert(signer) {
                    tally.push((signer, root));
                }
            }
            let wire = format!(
                "n={n};V={}",
                tally
                    .iter()
                    .map(|(s, r)| format!("{s}:{r}"))
                    .collect::<Vec<_>>()
                    .join(",")
            );
            let lean_decision =
                dregg_lean_ffi::distributed_ffi::verified_finalization_quorum(&wire)
                    .expect("the verified quorum gate ran");

            assert_eq!(
                rust_decision, lean_decision,
                "{label}: the Rust collector's quorum decision must agree with \
                 the verified Lean quorumRoot (wire: {wire})"
            );
        }

        // ── Targeted edges. superMajority(4) = 3. ──
        check_case(4, &[], "empty tally");
        check_case(4, &[(0, 0), (1, 0)], "one below threshold (2 of 3)");
        check_case(4, &[(0, 0), (1, 0), (2, 0)], "exactly threshold (3 of 3)");
        check_case(4, &[(0, 0), (1, 0), (2, 0), (3, 0)], "unanimous");
        check_case(4, &[(0, 0), (1, 0), (2, 1), (3, 1)], "split vote 2/2");
        check_case(
            4,
            &[(0, 0), (0, 0), (1, 0)],
            "duplicate signer does not double-count",
        );
        check_case(
            4,
            &[(0, 0), (0, 1), (1, 0), (2, 0)],
            "equivocating signer counts once, first-write-wins (quorum forms)",
        );
        check_case(
            4,
            &[(0, 1), (0, 0), (1, 0), (2, 0)],
            "equivocating signer's FIRST root is the counted one (no quorum)",
        );
        check_case(1, &[(0, 0)], "n=1 solo committee (threshold 1)");
        check_case(1, &[], "n=1 empty");
        check_case(
            6,
            &[(0, 0), (1, 0), (2, 0), (3, 0), (4, 0)],
            "n=6 exactly threshold 5",
        );

        // ── Deterministic pseudo-random tallies (xorshift64). ──
        let mut state: u64 = 0x9E37_79B9_7F4A_7C15;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for case in 0..48u32 {
            let n = 1 + (next() % 7) as usize; // committee of 1..=7
            let vote_count = (next() % (2 * n as u64 + 1)) as usize; // 0..=2n
            let votes: Vec<(usize, u64)> = (0..vote_count)
                .map(|_| ((next() % n as u64) as usize, next() % 3))
                .collect();
            check_case(n, &votes, &format!("random case {case} (n={n})"));
        }
    }

    /// THEME-2 #5 FALSIFIER — both directions. A Byzantine committee member
    /// signing votes for N ≫ cap FABRICATED block_ids stays BOUNDED (its
    /// occupancy never exceeds the per-member cap); AND a legit block still
    /// reaches consensus-wide quorum on the honest supermajority even while that
    /// Byzantine member is being flood-evicted — the eviction never touches a vote
    /// another member cast or a block accruing a real quorum.
    #[test]
    fn byzantine_member_flood_stays_bounded_and_honest_quorum_still_finalizes() {
        let (committee, pq) = committee_of(&[1, 2, 3, 4]);
        let quorum = dregg_blocklace::ordering::supermajority_threshold(4); // = 3
        // Small cap so the flood is cheap (no thousands of real ML-DSA signs);
        // the eviction logic is identical at MAX_VOTES_PER_MEMBER.
        let cap = 8usize;
        let mut col = VoteCollector::new(committee, pq, quorum).with_vote_cap(cap);

        // A legit block the HONEST members (2,3,4) finalize on the same root.
        let legit = BlockId([200; 32]);
        for m in [2u8, 3, 4] {
            col.record(&signed_vote(m, legit, FinalityLevel::Ordered, TEST_ROOT));
        }
        assert!(
            col.is_consensus_attested(&legit),
            "the honest supermajority (3 of 4) finalizes the legit block"
        );

        // Byzantine member 1 floods 30 ≫ cap votes over distinct FABRICATED
        // block_ids — each a valid hybrid signature, each lonely (only member 1).
        for i in 1u8..=30 {
            let fabricated = BlockId([i; 32]);
            let outcome = col.record(&signed_vote(
                1,
                fabricated,
                FinalityLevel::Ordered,
                TEST_ROOT,
            ));
            assert_ne!(
                outcome,
                RecordOutcome::Rejected,
                "a well-formed member vote is accepted (then capped, not rejected)"
            );
        }

        // BOUNDED: member 1's fabricated votes are hard-capped. The only tracked
        // blocks are the legit one plus at most `cap` of member 1's fakes.
        assert!(
            col.tracked_block_count() <= cap + 1,
            "a Byzantine flood of {} fabricated votes must stay bounded, tracked = {}",
            30,
            col.tracked_block_count()
        );

        // LIVENESS PRESERVED: the legit block is STILL consensus-attested — the
        // flood/eviction never disturbed the honest quorum's votes.
        assert!(
            col.is_consensus_attested(&legit),
            "the legit block stays finalized through the Byzantine flood"
        );
        // And a fresh legit block finalizes AFTER the flood, too.
        let legit2 = BlockId([201; 32]);
        for m in [2u8, 3, 4] {
            col.record(&signed_vote(m, legit2, FinalityLevel::Ordered, TEST_ROOT));
        }
        assert!(
            col.is_consensus_attested(&legit2),
            "a new legit block still reaches quorum after the flood"
        );
    }

    /// MONOTONE-SAFE BOUNDARY. A block already consensus-attested under the old
    /// committee STAYS attested after a reconfigure — the epoch boundary never
    /// retroactively un-finalizes a block (no safety violation across the
    /// handoff).
    #[test]
    fn reconfigure_preserves_prior_attestation() {
        let blk = BlockId([9; 32]);

        let (c2, pq2) = committee_of(&[1, 2]);
        let q2 = dregg_blocklace::ordering::supermajority_threshold(2);
        let mut col = VoteCollector::new(c2, pq2, q2);
        col.record(&signed_vote(1, blk, FinalityLevel::Ordered, TEST_ROOT));
        assert!(matches!(
            col.record(&signed_vote(2, blk, FinalityLevel::Ordered, TEST_ROOT)),
            RecordOutcome::ReachedQuorum { .. }
        ));
        assert!(col.is_consensus_attested(&blk));

        // A later membership change (add c, d) must not un-attest the block.
        let (c4, pq4) = committee_of(&[1, 2, 3, 4]);
        let q4 = dregg_blocklace::ordering::supermajority_threshold(4);
        col.reconfigure(c4, pq4, q4);
        assert!(
            col.is_consensus_attested(&blk),
            "a block finalized in the old epoch stays finalized across the boundary"
        );
    }
}
