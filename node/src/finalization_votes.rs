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

use std::collections::{HashMap, HashSet};

use dregg_blocklace::finality::{BlockId, FinalityLevel};
use dregg_federation::frost::{MlDsaPublicKey, MlDsaSigningKey};
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};

/// A signed assertion by one committee member that it has locally finalized a
/// block to (at least) `level` over committed state root `merkle_root`.
///
/// The signature is over
/// [`dregg_types::finalization_vote_signing_message`] =
/// `dregg-finalization-vote-v2 || block_id || merkle_root`, so it binds the
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
    votes: HashMap<BlockId, HashMap<[u8; 32], (dregg_types::Signature, [u8; 32])>>,
    /// Blocks that have crossed the quorum threshold (consensus-wide Attested).
    attested: HashSet<BlockId>,
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
        }
    }

    /// Replace the committee (e.g. after an epoch transition) without dropping
    /// already-accumulated votes; re-counting against the new membership happens
    /// implicitly on the next vote.
    #[allow(dead_code)] // collector query/maintenance API; exercised by tests
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
    #[allow(dead_code)] // collector query/maintenance API; exercised by tests
    pub fn committee_size(&self) -> usize {
        self.committee.len()
    }

    /// Whether a given key is currently an admissible (committee) signer.
    #[allow(dead_code)] // collector query/maintenance API; exercised by tests
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
    #[allow(dead_code)] // collector query/maintenance API; exercised by tests
    pub fn quorum_threshold(&self) -> usize {
        self.quorum_threshold
    }

    /// Number of distinct member votes recorded for a block.
    #[allow(dead_code)] // collector query/maintenance API; exercised by tests
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
    /// `(voter, signature)` pairs from `>= quorum_threshold` distinct committee
    /// signers who all attested `merkle_root` — exactly the record the
    /// persistence layer stores as `StoredAttestedRoot::finalization_quorum` and
    /// re-verifies via `verify_finalization_quorum`. Returns `None` while the
    /// quorum is still forming, or if the votes recorded for the block are split
    /// across roots (a fork) with no single root reaching the threshold.
    ///
    /// Only distinct signers who agree on ONE root count toward that root, so a
    /// genuine >=threshold quorum over the finalized state is required — this
    /// never fabricates a quorum a restart would then reject.
    pub fn assembled_quorum(
        &self,
        block_id: &BlockId,
    ) -> Option<(
        [u8; 32],
        Vec<(dregg_types::PublicKey, dregg_types::Signature)>,
    )> {
        let signers = self.votes.get(block_id)?;
        // Group distinct signers by the root they attested; pick a root that a
        // supermajority of distinct signers agreed on.
        let mut by_root: HashMap<[u8; 32], Vec<([u8; 32], dregg_types::Signature)>> =
            HashMap::new();
        for (voter, (sig, root)) in signers {
            by_root
                .entry(*root)
                .or_default()
                .push((*voter, sig.clone()));
        }
        let (root, members) = by_root
            .into_iter()
            .find(|(_, members)| members.len() >= self.quorum_threshold)?;
        let sigs = members
            .into_iter()
            .map(|(voter, sig)| (dregg_types::PublicKey(voter), sig))
            .collect();
        Some((root, sigs))
    }

    /// Has this block reached consensus-wide Attested (a quorum of distinct
    /// member signers)?
    #[allow(dead_code)] // collector query/maintenance API; exercised by tests
    pub fn is_consensus_attested(&self, block_id: &BlockId) -> bool {
        self.attested.contains(block_id)
    }

    /// All blocks that have reached consensus-wide Attested.
    #[allow(dead_code)] // collector query/maintenance API; exercised by tests
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
        if !vote.verify_hybrid(pq_pubkey) {
            return RecordOutcome::Rejected;
        }

        let signers = self.votes.entry(vote.block_id).or_default();
        // First-write-wins per signer: an equivocating member cannot displace
        // the vote already counted for it, nor be counted twice.
        signers
            .entry(vote.voter)
            .or_insert((vote.signature.clone(), vote.merkle_root));
        let distinct_votes = signers.len();
        let already = self.attested.contains(&vote.block_id);

        if already {
            return RecordOutcome::AlreadyQuorum { distinct_votes };
        }
        if distinct_votes >= self.quorum_threshold {
            self.attested.insert(vote.block_id);
            RecordOutcome::ReachedQuorum { distinct_votes }
        } else {
            RecordOutcome::Counted { distinct_votes }
        }
    }
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
        // (i.e. they are valid persisted `finalization_quorum` signatures).
        let msg = dregg_types::finalization_vote_signing_message(&blk.0, &TEST_ROOT);
        for (voter_pk, sig) in &sigs {
            assert!(
                voter_pk.verify(&msg, sig),
                "assembled quorum sig must verify"
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
