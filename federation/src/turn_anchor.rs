//! **THE PER-TURN ANCHOR** — the committee-signed statement a stranger obtains so that
//! re-verifying a served full-turn STARK is a check against something, instead of a check
//! against the artifact's own claims.
//!
//! # The hole this closes
//!
//! `dregg_sdk::verify_full_turn_bound` takes `expected_turn_hash` / `expected_old_commit` /
//! `expected_new_commit` FROM THE CALLER. Until this type existed, the only production surface
//! serving proofs to a third party (`GET /api/turn/{hash}/proof`) served
//! `{turn_hash, proof_status, proof_len, proof_hex}` and nothing else, so the discord bot's
//! `/proof turn` read the before/after anchors OUT of the artifact and handed them straight back
//! — the two endpoint `CommitmentMismatch` teeth compared `x != x` and structurally could not
//! fire. The turn hash came from the REQUEST URL, which is better (it is not read out of the
//! artifact) but is still whatever the caller typed at a node that may be lying.
//!
//! A [`TurnAnchorV1`] is a **projection of state the federation already signed**. It invents no
//! new authority: every byte in it is either recomputable by the holder or covered by a
//! signature the committee already produced on the finalized path. It is deliberately NOT a
//! node-signed envelope around values the node computed — that would reproduce the same defect
//! one layer out.
//!
//! # The chain of custody, and exactly how far it reaches
//!
//! ```text
//!   committee member's ed25519 signature
//!     over AttestedRoot::signing_message()          <- `quorum_signatures`
//!        which absorbs `receipt_stream_root`
//!     = merkle_root_of_receipt_hashes([receipt_hash])   (ONE leaf per finalized block:
//!                                                        node/src/blocklace_sync.rs:9685-9695)
//!        which absorbs `receipt_hash`
//!     = TurnReceipt::receipt_hash()  (domain `dregg-receipt-v5`)
//!        which absorbs `turn_hash`, `pre_state_hash`, `post_state_hash`, `effects_hash`, `agent`
//! ```
//!
//! So a valid anchor says: *at least `threshold` distinct members of the committee you named
//! signed a statement that this exact receipt — hence this exact turn hash — is the receipt
//! stream of the finalized block `block_id` at height `height`, whose post-state canonical
//! ledger root is `merkle_root`.*
//!
//! ## ⚑ WHAT THE 8-FELT STATE ANCHORS IN HERE ARE — AND ARE NOT
//!
//! `TurnReceipt::{pre,post}_state_hash` are the AIR-bound chip 8-felt consensus commitment
//! (`dregg_turn::state_commit`, packed by `Faithful8::to_bytes32`), so this anchor DOES carry a
//! committee-signed 8-felt per-turn state commit pair. **It is NOT the pair the full-turn proof
//! publishes**, and it must never be handed to `verify_full_turn_bound` as
//! `expected_old_commit` / `expected_new_commit` — doing so refuses every honest proof.
//!
//! Measured, both causes independently sufficient
//! (`turn/tests/receipt_state_commit_is_not_the_proof_state_commit.rs`):
//!
//! * **`iroot`.** The receipt anchor pins `state_commit::consensus_ctx`'s
//!   `iroot = rotation_witness::empty_iroot()` deliberately (a receipt cannot bind the
//!   commitment its own hash is computed from). The proof's rotation witness folds the REAL
//!   receipt chain (`node/src/turn_proving.rs:9317` threads `[receipt.receipt_hash()]`).
//! * **`cells_root`.** The receipt anchor folds the WHOLE ledger
//!   (`state_commit::consensus_ctx` -> `rotation_witness::cells_root(ledger)`); the proof's
//!   witness folds a SINGLE-CELL context ledger holding only the actor
//!   (`node/src/turn_proving.rs::rotation_witness_for_self_sovereign_impl`, `ctx_ledger`).
//!
//! They are two different commitments of the same transition. Aligning them is real work on the
//! consensus anchor (it moves what the committee signs AND what the proof publishes); it is
//! priced in `docs/DESIGN-pi-authority.md` and NOT done here. What this anchor therefore
//! delivers to a proof re-verifier is the **turn identity**, which every effect-vm leg publishes
//! at `pi::TURN_HASH_BASE` and which `verify_full_turn_bound` compares as a required argument.
//!
//! ## ⚑ WHAT THE >=THRESHOLD COMMITTEE QUORUM COVERS, AND WHAT IT DOES NOT
//!
//! Two different quorum legs ride an `AttestedRoot`, over two different preimages:
//!
//! | leg | preimage | reaches the turn? |
//! |---|---|---|
//! | `quorum_signatures` (ed25519) | [`AttestedRoot::signing_message`] — absorbs `receipt_stream_root` | **yes** |
//! | `hybrid_quorum` (ed25519 ∧ ML-DSA-65) | [`dregg_types::finalization_vote_signing_message`] — `(block_id, merkle_root)` only | **no** |
//!
//! [`TurnAnchorV1::verify`] gates acceptance on the FIRST leg, because it is the only one whose
//! preimage reaches the receipt. The second leg is verified and REPORTED
//! ([`VerifiedTurnAnchor::position_quorum_met`]) because it is what pins the block into
//! consensus, but it can never stand in for the first: a signature over `(block_id, merkle_root)`
//! says nothing about which receipt that block carried.
//!
//! ⚠ On the live path `quorum_signatures` receives exactly ONE push — the local node's
//! (`node/src/blocklace_sync.rs:9761`) — so this anchor VERIFIES on a threshold-1 federation and
//! REFUSES on a larger committee until a committee vote covers `receipt_stream_root`. That
//! refusal is deliberate and load-bearing: it is the difference between "the committee said so"
//! and "the node said so", and it must fail loudly rather than be labelled away.
//!
//! # The roster is the caller's, never the anchor's
//!
//! [`TurnAnchorV1::verify`] takes the committee it should judge against as an ARGUMENT. The
//! anchor carries a roster only as a convenience for a caller with no configured one, and using
//! it means trusting the server that served the anchor — [`TurnAnchorV1::served_committee`] is
//! named so that call sites cannot pretend otherwise.

use serde::{Deserialize, Serialize};

use dregg_turn::TurnReceipt;
use dregg_types::{
    AttestedRoot, FederationId, PublicKey, finalization_vote_signing_message,
    merkle_root_of_receipt_hashes,
};

use crate::frost::MlDsaPublicKey;
use crate::receipt::verify_hybrid_quorum_sigs;

/// Wire protocol tag. A decoder that does not recognise it REFUSES rather than guessing.
pub const TURN_ANCHOR_PROTOCOL_V1: &str = "DTA1";

/// The committee an anchor is judged against: ed25519 identities, the index-aligned enrolled
/// ML-DSA-65 roster, and the threshold. This is the caller's trust root, supplied out of band
/// (genesis / operator config) — never read out of the anchor being checked.
#[derive(Clone, Debug, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct AnchorCommittee {
    /// The committee's ed25519 identities.
    pub ed25519: Vec<PublicKey>,
    /// The genesis-enrolled ML-DSA-65 roster, aligned index-for-index with `ed25519`. May be
    /// empty; the hybrid position leg is then skipped rather than downgraded to ed25519-only.
    pub ml_dsa: Vec<Vec<u8>>,
    /// Signatures required for a quorum. Zero is not an authority.
    pub threshold: usize,
    /// The federation this roster belongs to. An anchor attested by a different federation is
    /// refused — a roster is only a trust root for its own federation.
    pub federation_id: FederationId,
}

/// **The per-turn anchor.** Everything a stranger needs to convince themselves, from a committee
/// roster they already trust, that a given turn hash is the turn the federation finalized at a
/// given chain position.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TurnAnchorV1 {
    /// [`TURN_ANCHOR_PROTOCOL_V1`]. Refused when unrecognised.
    pub protocol: String,
    /// The turn this anchor is for. Redundant with `receipt.turn_hash` ON PURPOSE: the two are
    /// compared, so a receipt served under the wrong turn's anchor is a named refusal rather
    /// than a silent substitution.
    pub turn_hash: [u8; 32],
    /// The canonical receipt, whole, so the holder recomputes `receipt_hash()` itself instead of
    /// being told it. This is the object the attestation's `receipt_stream_root` roots.
    pub receipt: TurnReceipt,
    /// The attested-root height this turn committed at.
    pub height: u64,
    /// The blocklace block that carried it.
    pub block_id: [u8; 32],
    /// The committee-signed attestation at `height`, carrying BOTH quorum legs.
    pub attested: AttestedRoot,
    /// The roster the SERVER claims. Present only so a caller with no configured committee can
    /// proceed knowingly; see [`TurnAnchorV1::served_committee`].
    pub served_committee: AnchorCommittee,
}

/// Why an anchor was refused. Every arm is a distinct, nameable failure — an anchor never fails
/// "generically", because the whole point is that a holder can say what did not hold.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TurnAnchorError {
    /// The `protocol` tag is not [`TURN_ANCHOR_PROTOCOL_V1`].
    UnknownProtocol(String),
    /// The caller supplied no committee (empty roster, or `threshold == 0`). A vacuous quorum is
    /// not an authority.
    NoCommittee { members: usize, threshold: usize },
    /// The attestation was produced by a different federation than the roster belongs to.
    FederationMismatch {
        anchor: FederationId,
        committee: FederationId,
    },
    /// The carried receipt is for a different turn than the anchor claims.
    ReceiptIsForAnotherTurn { anchor: [u8; 32], receipt: [u8; 32] },
    /// The attestation is not at the height/block the anchor claims.
    ChainPositionMismatch {
        anchor_height: u64,
        attested_height: u64,
        anchor_block: [u8; 32],
        attested_block: Option<[u8; 32]>,
    },
    /// The attestation carries no `receipt_stream_root` at all (a legacy v3 root). There is
    /// nothing binding a receipt to it, so it cannot anchor a turn.
    AttestationBindsNoReceiptStream,
    /// The receipt does not hash into the attestation's `receipt_stream_root`.
    ReceiptNotInAttestedStream {
        receipt_hash: [u8; 32],
        recomputed_stream_root: [u8; 32],
        attested_stream_root: [u8; 32],
    },
    /// Fewer than `threshold` distinct committee members signed the preimage that reaches the
    /// receipt. This is the refusal that separates "the committee said so" from "the node said
    /// so" — see the module docs.
    ReceiptQuorumNotMet { signers: usize, threshold: usize },
}

impl std::fmt::Display for TurnAnchorError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnknownProtocol(p) => write!(
                f,
                "unknown turn-anchor protocol `{p}` (expected `{TURN_ANCHOR_PROTOCOL_V1}`)"
            ),
            Self::NoCommittee { members, threshold } => write!(
                f,
                "no committee to judge against: {members} members, threshold {threshold}"
            ),
            Self::FederationMismatch { anchor, committee } => write!(
                f,
                "the attestation is federation {} but the roster is for {}",
                hex::encode(anchor.0),
                hex::encode(committee.0)
            ),
            Self::ReceiptIsForAnotherTurn { anchor, receipt } => write!(
                f,
                "the anchor claims turn {} but carries the receipt of turn {}",
                hex::encode(anchor),
                hex::encode(receipt)
            ),
            Self::ChainPositionMismatch {
                anchor_height,
                attested_height,
                anchor_block,
                attested_block,
            } => write!(
                f,
                "the anchor claims height {anchor_height} block {} but the attestation is height \
                 {attested_height} block {}",
                hex::encode(anchor_block),
                attested_block.map(hex::encode).unwrap_or("none".into())
            ),
            Self::AttestationBindsNoReceiptStream => write!(
                f,
                "the attestation carries no receipt_stream_root, so no signature over it reaches \
                 any receipt"
            ),
            Self::ReceiptNotInAttestedStream {
                receipt_hash,
                recomputed_stream_root,
                attested_stream_root,
            } => write!(
                f,
                "receipt {} roots to {} but the attestation binds {}",
                hex::encode(receipt_hash),
                hex::encode(recomputed_stream_root),
                hex::encode(attested_stream_root)
            ),
            Self::ReceiptQuorumNotMet { signers, threshold } => write!(
                f,
                "only {signers} distinct committee signature(s) cover this receipt; {threshold} \
                 required. The >=threshold hybrid vote quorum signs (block_id, merkle_root) only \
                 and does NOT reach the receipt, so it cannot stand in"
            ),
        }
    }
}

impl std::error::Error for TurnAnchorError {}

/// What a verified anchor establishes. Constructed ONLY by [`TurnAnchorV1::verify`], so holding
/// one is evidence the checks ran.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedTurnAnchor {
    /// **The value to hand `verify_full_turn_bound` as `expected_turn_hash`.** It came out of a
    /// committee-signed receipt, not out of any artifact and not out of a URL.
    pub turn_hash: [u8; 32],
    /// The receipt hash this holder RECOMPUTED (never the served claim).
    pub receipt_hash: [u8; 32],
    /// The finalized height and block.
    pub height: u64,
    pub block_id: [u8; 32],
    /// The post-state canonical ledger root (BLAKE3 whole-image) the attestation binds.
    pub ledger_root: [u8; 32],
    /// The committee-signed 8-felt consensus state commits from the receipt.
    ///
    /// ⚠ **NOT the full-turn proof's published anchors** — see the module docs. Report them,
    /// never pass them to `verify_full_turn_bound`.
    pub receipt_pre_state_commit: [u8; 32],
    pub receipt_post_state_commit: [u8; 32],
    /// Distinct committee members whose signature covers the RECEIPT (over
    /// `AttestedRoot::signing_message`). `>= threshold`, or `verify` would have refused.
    pub receipt_quorum_signers: usize,
    /// Did a `>= threshold` HYBRID (ed25519 ∧ ML-DSA-65, enrolled-key pinned) committee quorum
    /// cover the CHAIN POSITION `(block_id, merkle_root)`? Decided by the ONE shared rule,
    /// [`crate::receipt::verify_hybrid_quorum_sigs`]. Reported, never gating — this preimage
    /// does not reach the receipt, so it can neither establish nor stand in for the turn.
    pub position_quorum_met: bool,
    /// The threshold the roster declared.
    pub threshold: usize,
}

impl TurnAnchorV1 {
    /// **Verify this anchor against a committee the CALLER trusts.**
    ///
    /// Every step is recomputation or signature checking; nothing is taken on the server's word.
    /// Acceptance requires `>= threshold` distinct committee signatures over the preimage that
    /// reaches the receipt — see the module docs for why the hybrid vote quorum cannot substitute.
    pub fn verify(
        &self,
        committee: &AnchorCommittee,
    ) -> Result<VerifiedTurnAnchor, TurnAnchorError> {
        if self.protocol != TURN_ANCHOR_PROTOCOL_V1 {
            return Err(TurnAnchorError::UnknownProtocol(self.protocol.clone()));
        }
        if committee.ed25519.is_empty() || committee.threshold == 0 {
            return Err(TurnAnchorError::NoCommittee {
                members: committee.ed25519.len(),
                threshold: committee.threshold,
            });
        }
        if self.attested.federation_id != committee.federation_id {
            return Err(TurnAnchorError::FederationMismatch {
                anchor: self.attested.federation_id,
                committee: committee.federation_id,
            });
        }
        // The receipt must be THIS turn's. Checked before anything derived from it, so a
        // substituted receipt is named rather than surfacing as a stream mismatch.
        if self.receipt.turn_hash != self.turn_hash {
            return Err(TurnAnchorError::ReceiptIsForAnotherTurn {
                anchor: self.turn_hash,
                receipt: self.receipt.turn_hash,
            });
        }
        if self.attested.height != self.height
            || self.attested.blocklace_block_id != Some(self.block_id)
        {
            return Err(TurnAnchorError::ChainPositionMismatch {
                anchor_height: self.height,
                attested_height: self.attested.height,
                anchor_block: self.block_id,
                attested_block: self.attested.blocklace_block_id,
            });
        }

        // RECOMPUTE the receipt hash and the singleton stream root; never read either.
        let receipt_hash = self.receipt.receipt_hash();
        let recomputed = merkle_root_of_receipt_hashes(&[receipt_hash]);
        let Some(attested_stream_root) = self.attested.receipt_stream_root else {
            return Err(TurnAnchorError::AttestationBindsNoReceiptStream);
        };
        if recomputed != attested_stream_root {
            return Err(TurnAnchorError::ReceiptNotInAttestedStream {
                receipt_hash,
                recomputed_stream_root: recomputed,
                attested_stream_root,
            });
        }

        // LEG 1 (gating): committee signatures over the preimage that absorbs
        // `receipt_stream_root`, hence this receipt, hence this turn hash.
        let receipt_message = self.attested.signing_message();
        let mut receipt_signers: std::collections::HashSet<[u8; 32]> = Default::default();
        for (pk, sig) in &self.attested.quorum_signatures {
            if committee.ed25519.contains(pk) && pk.verify(&receipt_message, sig) {
                receipt_signers.insert(pk.0);
            }
        }
        if receipt_signers.len() < committee.threshold {
            return Err(TurnAnchorError::ReceiptQuorumNotMet {
                signers: receipt_signers.len(),
                threshold: committee.threshold,
            });
        }

        // LEG 2 (reported, never gating): the HYBRID vote quorum over the CHAIN POSITION. Its
        // preimage is `(block_id, merkle_root)` and reaches no receipt.
        let position_quorum_met = self.position_quorum_met(committee);

        Ok(VerifiedTurnAnchor {
            turn_hash: self.turn_hash,
            receipt_hash,
            height: self.height,
            block_id: self.block_id,
            ledger_root: self.attested.merkle_root,
            receipt_pre_state_commit: self.receipt.pre_state_hash,
            receipt_post_state_commit: self.receipt.post_state_hash,
            receipt_quorum_signers: receipt_signers.len(),
            position_quorum_met,
            threshold: committee.threshold,
        })
    }

    /// Did a `>= threshold` HYBRID committee quorum sign the finalization-vote preimage
    /// `(block_id, merkle_root)`?
    ///
    /// Delegates to [`crate::receipt::verify_hybrid_quorum_sigs`] — the ONE place the
    /// `classical ∧ pq`, enrolled-key-pinned rule lives — so this can never drift from the rule
    /// the restart anchor and the cross-fed verifier apply. Fail-closed on a misaligned or empty
    /// enrolled ML-DSA roster (that function refuses rather than downgrading to ed25519-only)
    /// and on an undecodable enrolled key.
    fn position_quorum_met(&self, committee: &AnchorCommittee) -> bool {
        let Some(block_id) = self.attested.blocklace_block_id else {
            return false;
        };
        let enrolled: Vec<MlDsaPublicKey> = committee
            .ml_dsa
            .iter()
            .filter_map(|k| <[u8; dregg_pq::ML_DSA_PK_LEN]>::try_from(k.as_slice()).ok())
            .map(MlDsaPublicKey)
            .collect();
        // A key that did not decode drops out above, which shortens the roster and makes
        // `verify_hybrid_quorum_sigs`'s length-alignment guard refuse the whole leg.
        let vote_message = finalization_vote_signing_message(&block_id, &self.attested.merkle_root);
        verify_hybrid_quorum_sigs(
            &self.attested.hybrid_quorum,
            &vote_message,
            &committee.ed25519,
            &enrolled,
            committee.threshold,
        )
    }

    /// The roster the SERVER claims, for a caller that has none configured.
    ///
    /// ⚠ Verifying against this is verifying against the server: it can name any committee it
    /// likes, including one it wholly controls. The method is named for what it is so no call
    /// site can present the result as committee-verified without saying where the roster came
    /// from. Prefer a roster from genesis or operator config.
    pub fn served_committee(&self) -> &AnchorCommittee {
        &self.served_committee
    }
}
