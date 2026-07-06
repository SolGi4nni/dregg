//! committee_replay.rs — boot-time derivation of the CURRENT federation
//! committee from the persisted blocklace: the constitution as a PURE VIEW of
//! the chain, never a second source of truth.
//!
//! WHY THIS EXISTS. Membership is amended ON-CHAIN (`MembershipAction` blocks →
//! quorum votes → `blocklace_sync::apply_passed_proposal` → the live epoch
//! transition), and the `federation_id` is INTENTIONALLY stable across
//! amendments so bots / bridges / light clients never re-point. But the runtime
//! `ConstitutionManager` was rebuilt fresh from the genesis committee on every
//! boot, and the executed-identity cursor (correctly, for turns) never re-serves
//! already-executed membership blocks — so a restart silently REVERTED the
//! committee to genesis: an admitted validator's finalization votes stopped
//! counting, the threshold regressed, and the signed-anchor recovery check
//! (`state.rs::verify_signed_anchor_and_rollback`, the N3 Fix-B weld) verified a
//! root quorum-signed by the AMENDED committee against the genesis key set —
//! fail-closing an honest node. That reversion is why operator adds still
//! leaned on the disruptive genesis re-roll. This module closes it: the boot
//! committee is DERIVED from the finalized membership history, so the amended
//! committee survives restart and the re-roll becomes a recovery tool, not the
//! join path.
//!
//! HOW. [`derive_from_lace`] folds the finalized membership blocks over a fresh
//! `ConstitutionManager`, in the same order the executor served them: the
//! `ordering::tau` order computed with the committee AS OF each amendment.
//! Because tau's leader election depends on the participant set, each applied
//! amendment triggers an order recompute, and the walk continues over the
//! not-yet-folded identities — exactly the shifting-order-absorbed-by-identity
//! discipline the live executor's cursor uses (`TauPrefixMonotone`). The loop
//! terminates: every recompute is preceded by a fresh amendment, and amendments
//! are bounded by the membership blocks in the lace.
//!
//! The fold itself ([`fold_membership_block`]) is the PURE twin of
//! `blocklace_sync::execute_finalized_membership` — proposal registration, the
//! proposer's implicit self-vote, Approve/Reject votes, quorum application. No
//! gossip, no devnet auto-approve, no live reconfigure. Replay can never widen
//! authority: every vote counted here was a signed, finalized on-chain block,
//! and eligibility is enforced by the same `ConstitutionManager` quorum rule
//! the live path uses.

use std::collections::HashSet;

use dregg_blocklace::constitution::{
    ConstitutionManager, LeaveReason, MembershipProposal, MembershipVote,
};
use dregg_blocklace::finality::{BlockId, Blocklace, MembershipAction, Payload};
use dregg_blocklace::ordering::tau;

/// The committee derived from the chain at boot.
#[derive(Debug, Clone)]
pub struct DerivedCommittee {
    /// The current participant set (the committee the node must boot into).
    pub participants: Vec<[u8; 32]>,
    /// The BFT threshold for that set (`⌊2n/3⌋ + 1`).
    pub threshold: usize,
    /// The constitution version (0 = genesis, +1 per applied amendment).
    pub version: u64,
    /// Every committee the constitution passed through, genesis first. A
    /// persisted attested root may be quorum-signed by ANY of these (whichever
    /// was current when it was persisted), so the signed-anchor recovery check
    /// accepts a quorum from any historical committee — all of them are
    /// unforgeable to the offline-tamper adversary the anchor defends against
    /// (it holds no committee keys of any epoch).
    pub history: Vec<Vec<[u8; 32]>>,
    /// How many amendments applied during replay (0 = genesis committee).
    pub amendments: usize,
}

impl DerivedCommittee {
    fn genesis(cm: &ConstitutionManager) -> Self {
        DerivedCommittee {
            participants: cm.participants().to_vec(),
            threshold: cm.threshold(),
            version: cm.version(),
            history: vec![cm.participants().to_vec()],
            amendments: 0,
        }
    }
}

/// Fold ONE finalized membership block into the constitution — the pure twin of
/// `blocklace_sync::execute_finalized_membership` (same calls, same order, no
/// side effects). Returns `true` when this block's vote PASSED a proposal and
/// the constitution was amended.
pub fn fold_membership_block(
    cm: &mut ConstitutionManager,
    block_id: BlockId,
    creator: [u8; 32],
    action: &MembershipAction,
) -> bool {
    match action {
        MembershipAction::Join { node_id } => {
            cm.submit_proposal(
                block_id,
                MembershipProposal::Join {
                    node_key: *node_id,
                    justification: vec![],
                },
            );
            // The proposer implicitly votes for their own join (counted only if
            // the proposer is a current participant — the manager's rule).
            let vote = MembershipVote {
                proposal_block: block_id,
                approve: true,
            };
            match cm.submit_vote(&vote, creator) {
                Some(passed) => cm.apply_if_passed(&passed),
                None => false,
            }
        }
        MembershipAction::Leave { node_id } => {
            cm.submit_proposal(
                block_id,
                MembershipProposal::Leave {
                    node_key: *node_id,
                    reason: LeaveReason::Voluntary,
                },
            );
            let vote = MembershipVote {
                proposal_block: block_id,
                approve: true,
            };
            match cm.submit_vote(&vote, creator) {
                Some(passed) => cm.apply_if_passed(&passed),
                None => false,
            }
        }
        MembershipAction::Approve { proposal_block } => {
            let vote = MembershipVote {
                proposal_block: *proposal_block,
                approve: true,
            };
            match cm.submit_vote(&vote, creator) {
                Some(passed) => cm.apply_if_passed(&passed),
                None => false,
            }
        }
        MembershipAction::Reject { proposal_block } => {
            let vote = MembershipVote {
                proposal_block: *proposal_block,
                approve: false,
            };
            cm.submit_vote(&vote, creator);
            false
        }
    }
}

/// The finalized order of the lace under `participants`, as BlockIds of the
/// FINALITY lace. Mirrors `poll_finalized_blocks` exactly: the solo (n ≤ 1)
/// path orders every actionable block by sequence; the multi-party path runs
/// `ordering::tau` over the unsigned ordering projection and maps back. The
/// solo sort adds `(creator, id)` tiebreaks for determinism (a solo committee
/// has one creator, so this only disambiguates pathological inputs).
fn finalized_order(lace: &Blocklace, participants: &[[u8; 32]]) -> Vec<BlockId> {
    if participants.len() <= 1 {
        let mut v: Vec<(u64, [u8; 32], BlockId)> = lace
            .iter()
            .filter_map(|(id, b)| match &b.payload {
                Payload::Turn(_)
                | Payload::TurnBundle(_)
                | Payload::MembershipVote { .. }
                | Payload::Checkpoint { .. } => Some((b.seq, b.creator, *id)),
                _ => None,
            })
            .collect();
        v.sort_unstable();
        v.into_iter().map(|(_, _, id)| id).collect()
    } else {
        let (ordering_lace, back) = crate::blocklace_sync::build_ordering_blocklace(lace);
        tau(&ordering_lace, participants)
            .into_iter()
            .filter_map(|oid| back.get(&oid).copied())
            .collect()
    }
}

/// Derive the current committee (and its version history) from the persisted
/// lace, starting from the genesis committee. See the module docs for the
/// order/recompute discipline.
///
/// Returns the summary AND the replayed `ConstitutionManager` itself: the
/// manager carries the IN-FLIGHT proposal/vote state (a proposal that had
/// gathered votes but had not passed at shutdown). The consensus boot must
/// seed from this manager, not a fresh one — a fresh manager would drop those
/// votes, making the pending proposal unpassable on the restarted node while
/// its peers (which never restarted) can still pass it: a committee divergence.
///
/// Fast path: a lace with no membership blocks returns the genesis committee
/// without computing any order (the overwhelmingly common boot).
pub fn derive_from_lace(
    lace: &Blocklace,
    genesis_committee: &[[u8; 32]],
    timeout_waves: u64,
) -> (DerivedCommittee, ConstitutionManager) {
    let mut cm = ConstitutionManager::from_participants(genesis_committee.to_vec(), timeout_waves);

    let has_membership = lace
        .iter()
        .any(|(_, b)| matches!(b.payload, Payload::MembershipVote { .. }));
    if !has_membership {
        let summary = DerivedCommittee::genesis(&cm);
        return (summary, cm);
    }

    let mut history = vec![cm.participants().to_vec()];
    let mut folded: HashSet<BlockId> = HashSet::new();
    let mut amendments = 0usize;

    loop {
        let participants = cm.participants().to_vec();
        let order = finalized_order(lace, &participants);
        let mut amended_this_pass = false;

        for id in order {
            if folded.contains(&id) {
                continue;
            }
            let Some(block) = lace.get(&id) else { continue };
            let Payload::MembershipVote { action } = &block.payload else {
                continue;
            };
            let action = action.clone();
            let creator = block.creator;
            folded.insert(id);
            if fold_membership_block(&mut cm, id, creator, &action) {
                amendments += 1;
                history.push(cm.participants().to_vec());
                amended_this_pass = true;
                // The participant set changed: the tau order (leader election)
                // may shift for everything not yet folded. Recompute and
                // continue over the not-yet-folded identities — the same
                // shifted-order-by-identity absorption the live cursor does.
                break;
            }
        }

        if !amended_this_pass {
            break;
        }
    }

    let summary = DerivedCommittee {
        participants: cm.participants().to_vec(),
        threshold: cm.threshold(),
        version: cm.version(),
        history,
        amendments,
    };
    (summary, cm)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_blocklace::finality::Block;
    use dregg_blocklace::ordering::supermajority_threshold;
    use ed25519_dalek::SigningKey;

    fn keypair(seed: u8) -> SigningKey {
        SigningKey::from_bytes(&[seed; 32])
    }

    fn pk(sk: &SigningKey) -> [u8; 32] {
        sk.verifying_key().to_bytes()
    }

    /// A lace owned by `owner` that accepts hand-built rounds from a set of
    /// signers via `receive_block`.
    fn lace_for(owner: &SigningKey, quorum: usize) -> Blocklace {
        Blocklace::new(owner.clone(), quorum)
    }

    /// Build one fully-connected round: every signer produces one block at
    /// `seq` referencing every block of the previous round. `payloads` maps a
    /// signer index to a payload; everyone else emits `Payload::Ack`.
    fn round(
        lace: &mut Blocklace,
        signers: &[&SigningKey],
        seq: u64,
        prev: &[BlockId],
        payloads: &[(usize, Payload)],
    ) -> Vec<BlockId> {
        let mut ids = Vec::new();
        for (i, sk) in signers.iter().enumerate() {
            let payload = payloads
                .iter()
                .find(|(idx, _)| *idx == i)
                .map(|(_, p)| p.clone())
                .unwrap_or(Payload::Ack);
            let block = Block::new(sk, seq, payload, prev.to_vec());
            let id = block.id();
            lace.receive_block(block).expect("receive hand-built block");
            ids.push(id);
        }
        ids
    }

    /// n=3 committee; A proposes Join(D); B and C approve on-chain; quorum
    /// (3-of-3) passes → the derived committee is {A,B,C,D} at version 1 and
    /// the history carries both committees.
    #[test]
    fn quorum_join_survives_replay() {
        let (a, b, c, d) = (keypair(1), keypair(2), keypair(3), keypair(4));
        let signers = [&a, &b, &c];
        let genesis: Vec<[u8; 32]> = vec![pk(&a), pk(&b), pk(&c)];
        let q = supermajority_threshold(3);
        assert_eq!(q, 3);

        let mut lace = lace_for(&a, q);
        let r1 = round(&mut lace, &signers, 0, &[], &[]);
        let r2 = round(&mut lace, &signers, 1, &r1, &[]);

        // Round 3: A proposes Join(D).
        let join_payload = Payload::MembershipVote {
            action: MembershipAction::Join { node_id: pk(&d) },
        };
        let r3 = round(&mut lace, &signers, 2, &r2, &[(0, join_payload)]);
        let join_block_id = r3[0];

        // Round 4: B and C approve the proposal.
        let approve = |pb: BlockId| Payload::MembershipVote {
            action: MembershipAction::Approve { proposal_block: pb },
        };
        let r4 = round(
            &mut lace,
            &signers,
            3,
            &r3,
            &[(1, approve(join_block_id)), (2, approve(join_block_id))],
        );

        // Enough further rounds for the wave containing r3/r4 to super-ratify.
        let r5 = round(&mut lace, &signers, 4, &r4, &[]);
        let r6 = round(&mut lace, &signers, 5, &r5, &[]);
        let r7 = round(&mut lace, &signers, 6, &r6, &[]);
        let _ = round(&mut lace, &signers, 7, &r7, &[]);

        let (derived, _cm) = derive_from_lace(&lace, &genesis, 1000);
        assert_eq!(
            derived.participants.len(),
            4,
            "join must survive replay: derived committee {:?} (amendments {})",
            derived.participants.len(),
            derived.amendments
        );
        assert!(derived.participants.contains(&pk(&d)), "D admitted");
        assert_eq!(derived.version, 1);
        assert_eq!(derived.amendments, 1);
        assert_eq!(derived.threshold, supermajority_threshold(4));
        assert_eq!(derived.history.len(), 2, "genesis + amended");
        assert_eq!(derived.history[0].len(), 3);
        assert_eq!(derived.history[1].len(), 4);
    }

    /// Under-quorum: only B approves (2-of-3 votes incl. proposer < 3) — the
    /// committee must NOT change. The replay is exactly as authority-gated as
    /// the live path.
    #[test]
    fn under_quorum_join_does_not_apply() {
        let (a, b, c, d) = (keypair(1), keypair(2), keypair(3), keypair(4));
        let signers = [&a, &b, &c];
        let genesis: Vec<[u8; 32]> = vec![pk(&a), pk(&b), pk(&c)];

        let mut lace = lace_for(&a, 3);
        let r1 = round(&mut lace, &signers, 0, &[], &[]);
        let join_payload = Payload::MembershipVote {
            action: MembershipAction::Join { node_id: pk(&d) },
        };
        let r2 = round(&mut lace, &signers, 1, &r1, &[(0, join_payload)]);
        let join_block_id = r2[0];
        let approve = Payload::MembershipVote {
            action: MembershipAction::Approve {
                proposal_block: join_block_id,
            },
        };
        let r3 = round(&mut lace, &signers, 2, &r2, &[(1, approve)]);
        let r4 = round(&mut lace, &signers, 3, &r3, &[]);
        let r5 = round(&mut lace, &signers, 4, &r4, &[]);
        let _ = round(&mut lace, &signers, 5, &r5, &[]);

        let (derived, _cm) = derive_from_lace(&lace, &genesis, 1000);
        assert_eq!(
            derived.participants.len(),
            3,
            "under-quorum join must not apply"
        );
        assert!(!derived.participants.contains(&pk(&d)));
        assert_eq!(derived.version, 0);
        assert_eq!(derived.amendments, 0);
        assert_eq!(derived.history.len(), 1);
    }

    /// No membership blocks → the genesis fast path (no ordering work at all).
    #[test]
    fn no_membership_blocks_is_genesis_fast_path() {
        let (a, b, c) = (keypair(1), keypair(2), keypair(3));
        let signers = [&a, &b, &c];
        let genesis: Vec<[u8; 32]> = vec![pk(&a), pk(&b), pk(&c)];

        let mut lace = lace_for(&a, 3);
        let r1 = round(&mut lace, &signers, 0, &[], &[]);
        let _ = round(&mut lace, &signers, 1, &r1, &[]);

        let (derived, _cm) = derive_from_lace(&lace, &genesis, 1000);
        assert_eq!(derived.participants.len(), 3);
        assert_eq!(derived.version, 0);
        assert_eq!(derived.amendments, 0);
    }

    /// Solo (n=1) committee: the owner's own Join proposal passes at
    /// threshold 1 (the proposer self-vote) — the derived committee is the
    /// pair, and the walk terminates (no oscillation between the solo and
    /// multi-party ordering paths).
    #[test]
    fn solo_join_derives_pair_and_terminates() {
        let (a, b) = (keypair(1), keypair(2));
        let genesis: Vec<[u8; 32]> = vec![pk(&a)];

        let mut lace = lace_for(&a, 1);
        // Solo blocks via the owner's own add_block (auto-preds, signed).
        lace.add_block(Payload::Ack);
        lace.add_block(Payload::MembershipVote {
            action: MembershipAction::Join { node_id: pk(&b) },
        });
        lace.add_block(Payload::Ack);

        let (derived, _cm) = derive_from_lace(&lace, &genesis, 1000);
        assert_eq!(
            derived.participants.len(),
            2,
            "solo self-quorum join applies"
        );
        assert!(derived.participants.contains(&pk(&b)));
        assert_eq!(derived.version, 1);
        assert_eq!(derived.amendments, 1);
    }
}
