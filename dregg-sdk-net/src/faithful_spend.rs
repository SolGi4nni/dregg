//! Target-independent faithful-note and nullifier synchronization.
//!
//! A wallet never asks a node for the position or Merkle path of its note.
//! Instead it incrementally mirrors the one global append-only commitment
//! sequence, authenticates the node-author root history against pinned trust,
//! and constructs membership locally.  The already-public nullifier log is
//! mirrored in the same way, so even the future FNF2 nullifier/value/asset and
//! successor planning stay entirely inside the wallet.
//!
//! Honest trust label: FNHR edges are hybrid-authenticated by one pinned node
//! author today, not a federation quorum.  The mirrored `StoredAttestedRoot`
//! coordinates are served over the authenticated node transport but are not
//! independently re-verifiable here because current finalization votes bind
//! `(block_id, ledger_root)`, not the faithful note/nullifier roots.  Local
//! recomposition detects inconsistency; it does not manufacture federation
//! finality.  That widening remains a named protocol follow-up.

use std::collections::BTreeSet;

use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_commit::poseidon2_tree::{
    Poseidon2NoteProof16, Poseidon2NoteTree16, commitment_to_lanes16, note_leaf16, note_node8,
};
use dregg_federation::frost::MlDsaPublicKey;
use dregg_sdk::error::SdkError;
use dregg_sdk::privacy::{
    FaithfulHiddenSpendProof, FaithfulNoteOpening, build_faithful_hidden_spend_proof,
};
use dregg_turn::faithful_note_spend::FaithfulNoteSpendProofCarrier;
use dregg_types::{HybridQuorumSig, PublicKey};
use serde::{Deserialize, Serialize};

use crate::NodeHttpClient;

const MIRROR_PROTOCOL: &str = "dregg-faithful-note-mirror-v1";
const FAITHFUL_NOTE_DEPTH: usize = 16;
const COMMITMENT_PAGE_SIZE: usize = 256;
const HISTORY_PAGE_SIZE: usize = 16;
const MAX_DEPTH16_NOTE_COUNT: u64 = 1u64 << 32;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FaithfulPriorSpend {
    #[serde(with = "lower_hex32")]
    pub nullifier: [u8; 32],
    pub value: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FaithfulPriorSpendContext {
    #[serde(with = "lower_hex32")]
    pub nullifier: [u8; 32],
    pub value: u64,
    pub successor_nullifier_root8: [u32; 8],
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FaithfulNoteMirrorRequest {
    pub commitment_cursor: u64,
    pub history_cursor: u64,
    pub nullifier_cursor: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FaithfulNoteMirrorAnchor {
    #[serde(with = "lower_hex32")]
    pub session_id: [u8; 32],
    #[serde(with = "lower_hex32")]
    pub federation_id: [u8; 32],
    pub committee_epoch: u64,
    pub height: u64,
    pub note_count: u64,
    pub root8: [u32; 8],
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FaithfulNoteMirrorRecord {
    #[serde(with = "lower_hex32")]
    pub session_id: [u8; 32],
    #[serde(with = "lower_hex32")]
    pub federation_id: [u8; 32],
    pub committee_epoch: u64,
    pub previous_height: u64,
    pub height: u64,
    pub previous_note_count: u64,
    pub note_count: u64,
    pub predecessor_root8: [u32; 8],
    pub successor_root8: [u32; 8],
    #[serde(with = "lower_hex32")]
    pub block_id: [u8; 32],
    pub hybrid_quorum: Vec<HybridQuorumSig>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FaithfulNoteMirrorHead {
    pub history_records: u64,
    pub height: u64,
    pub note_count: u64,
    pub root8: [u32; 8],
    pub nullifier_count: u64,
    /// Node-served coordinate from its locally verified attested head.  See
    /// module trust boundary: this is transport-authenticated, not yet bound by
    /// a client-verifiable federation signature over this exact root.
    pub attested_nullifier_root8: [u32; 8],
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FaithfulNullifierMirrorRecord {
    #[serde(with = "lower_hex32")]
    pub nullifier: [u8; 32],
    pub value: u64,
    pub seq: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FaithfulNoteMirrorResponse {
    pub protocol: String,
    pub commitment_cursor: u64,
    pub next_commitment_cursor: u64,
    pub history_cursor: u64,
    pub next_history_cursor: u64,
    pub nullifier_cursor: u64,
    pub next_nullifier_cursor: u64,
    #[serde(with = "lower_hex32_vec")]
    pub commitments: Vec<[u8; 32]>,
    pub nullifiers: Vec<FaithfulNullifierMirrorRecord>,
    pub anchor: FaithfulNoteMirrorAnchor,
    pub history: Vec<FaithfulNoteMirrorRecord>,
    pub head: FaithfulNoteMirrorHead,
    pub head_hybrid_quorum: Vec<HybridQuorumSig>,
    pub complete: bool,
    pub privacy: String,
}

/// Pinned trust for the current node-authenticated FNHR segment.
///
/// Current FNHR records carry a one-node hybrid author signature, not a
/// federation finalization quorum.  The self-carried ML-DSA key is therefore
/// never trusted: both author rosters and the external anchor are pinned here.
#[derive(Clone, Debug)]
pub struct FaithfulNoteMirrorTrust {
    pub anchor: FaithfulNoteMirrorAnchor,
    pub author_committee: Vec<PublicKey>,
    pub author_ml_dsa_committee: Vec<MlDsaPublicKey>,
    pub threshold: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalFaithfulNoteWitness {
    position: u64,
    note_count: u64,
    root_height: u64,
    historical_note_root: [u32; 8],
    membership: Poseidon2NoteProof16,
}

impl LocalFaithfulNoteWitness {
    pub fn position(&self) -> u64 {
        self.position
    }

    pub fn root_height(&self) -> u64 {
        self.root_height
    }

    pub fn note_count(&self) -> u64 {
        self.note_count
    }
}

/// Incremental global mirror.  There is intentionally no API that fetches a
/// page for a target commitment; synchronization starts at zero and follows
/// every server continuation.
#[derive(Clone, Debug, Default)]
pub struct FaithfulNoteMirror {
    commitments: Vec<[u8; 32]>,
    history: Vec<FaithfulNoteMirrorRecord>,
    nullifiers: Vec<FaithfulNullifierMirrorRecord>,
    anchor: Option<FaithfulNoteMirrorAnchor>,
    head: Option<FaithfulNoteMirrorHead>,
}

impl FaithfulNoteMirror {
    pub fn commitment_cursor(&self) -> u64 {
        self.commitments.len() as u64
    }

    pub fn history_cursor(&self) -> u64 {
        self.history.len() as u64
    }

    pub fn nullifier_cursor(&self) -> u64 {
        self.nullifiers.len() as u64
    }

    pub fn head(&self) -> Option<&FaithfulNoteMirrorHead> {
        self.head.as_ref()
    }

    fn expected_history_head(&self) -> Option<(u64, u64, [u32; 8])> {
        self.history
            .last()
            .map(|record| (record.height, record.note_count, record.successor_root8))
            .or_else(|| {
                self.anchor
                    .as_ref()
                    .map(|anchor| (anchor.height, anchor.note_count, anchor.root8))
            })
    }

    /// Apply exactly the next global page and authenticate every included FNHR
    /// record. Missing, duplicated, reordered, or target-jumped pages refuse.
    pub fn apply_page(
        &mut self,
        page: FaithfulNoteMirrorResponse,
        trust: &FaithfulNoteMirrorTrust,
    ) -> Result<bool, SdkError> {
        if page.protocol != MIRROR_PROTOCOL {
            return Err(refusal("unknown faithful mirror protocol"));
        }
        if trust.threshold == 0
            || trust.author_committee.is_empty()
            || trust.threshold > trust.author_committee.len()
            || trust.author_committee.len() != trust.author_ml_dsa_committee.len()
            || page.anchor != trust.anchor
        {
            return Err(refusal("faithful mirror trust/anchor mismatch"));
        }
        if let Some(anchor) = &self.anchor {
            if anchor != &page.anchor {
                return Err(refusal("faithful mirror segment/anchor changed"));
            }
        }
        if page.commitment_cursor != self.commitment_cursor()
            || page.history_cursor != self.history_cursor()
            || page.nullifier_cursor != self.nullifier_cursor()
        {
            return Err(refusal(
                "faithful mirror page did not continue the complete local prefix",
            ));
        }
        let commitment_page_len = u64::try_from(page.commitments.len())
            .map_err(|_| refusal("commitment page length does not fit u64"))?;
        let history_page_len = u64::try_from(page.history.len())
            .map_err(|_| refusal("history page length does not fit u64"))?;
        let nullifier_page_len = u64::try_from(page.nullifiers.len())
            .map_err(|_| refusal("nullifier page length does not fit u64"))?;
        let expected_next_commitment = page.commitment_cursor.checked_add(commitment_page_len);
        let expected_next_history = page.history_cursor.checked_add(history_page_len);
        let expected_next_nullifier = page.nullifier_cursor.checked_add(nullifier_page_len);
        if page.commitments.len() > COMMITMENT_PAGE_SIZE
            || page.history.len() > HISTORY_PAGE_SIZE
            || page.nullifiers.len() > COMMITMENT_PAGE_SIZE
            || expected_next_commitment != Some(page.next_commitment_cursor)
            || expected_next_history != Some(page.next_history_cursor)
            || expected_next_nullifier != Some(page.next_nullifier_cursor)
        {
            return Err(refusal(
                "faithful mirror page has invalid fixed-page framing",
            ));
        }
        validate_root8("mirror anchor", page.anchor.root8)?;
        validate_root8("mirror head", page.head.root8)?;
        validate_root8(
            "mirror attested nullifier",
            page.head.attested_nullifier_root8,
        )?;
        if !dregg_federation::receipt::verify_hybrid_quorum_sigs(
            &page.head_hybrid_quorum,
            &mirror_head_signing_message(&page.anchor, &page.head),
            &trust.author_committee,
            &trust.author_ml_dsa_committee,
            trust.threshold,
        ) {
            return Err(refusal(
                "faithful mirror head failed pinned FNMS-v1 hybrid authentication",
            ));
        }
        if page.head.note_count > MAX_DEPTH16_NOTE_COUNT
            || page.next_commitment_cursor > page.head.note_count
            || page.next_history_cursor > page.head.history_records
            || page.next_nullifier_cursor > page.head.nullifier_count
        {
            return Err(refusal(
                "faithful mirror continuation exceeds its sealed head",
            ));
        }
        if (page.next_commitment_cursor < page.head.note_count
            && page.commitments.len() != COMMITMENT_PAGE_SIZE)
            || (page.next_history_cursor < page.head.history_records
                && page.history.len() != HISTORY_PAGE_SIZE)
            || (page.next_nullifier_cursor < page.head.nullifier_count
                && page.nullifiers.len() != COMMITMENT_PAGE_SIZE)
        {
            return Err(refusal(
                "nonterminal faithful mirror page is shorter than its fixed protocol size",
            ));
        }
        if !page.complete
            && page.commitments.is_empty()
            && page.history.is_empty()
            && page.nullifiers.is_empty()
        {
            return Err(refusal("nonterminal faithful mirror page made no progress"));
        }

        // Validate the page completely before mutating the mirror.  Cloning the
        // accumulated prefix here would make a fresh sync quadratic, so carry
        // only the page-sized history frontier and allocate a combined prefix
        // once, on the terminal root check.
        let mut expected_history_head = self.expected_history_head().or(Some((
            page.anchor.height,
            page.anchor.note_count,
            page.anchor.root8,
        )));
        for record in &page.history {
            validate_history_record(record, &trust.anchor, expected_history_head)?;
            if !dregg_federation::receipt::verify_hybrid_quorum_sigs(
                &record.hybrid_quorum,
                &history_signing_message(record),
                &trust.author_committee,
                &trust.author_ml_dsa_committee,
                trust.threshold,
            ) {
                return Err(refusal(
                    "faithful mirror history record failed pinned hybrid author authentication",
                ));
            }
            expected_history_head =
                Some((record.height, record.note_count, record.successor_root8));
        }
        for (offset, record) in page.nullifiers.iter().enumerate() {
            let offset = u64::try_from(offset)
                .map_err(|_| refusal("nullifier page offset does not fit u64"))?;
            let expected_seq = page
                .nullifier_cursor
                .checked_add(offset)
                .ok_or_else(|| refusal("nullifier sequence cannot advance"))?;
            if record.seq != expected_seq {
                return Err(refusal(
                    "faithful nullifier mirror sequence is not dense and ordered",
                ));
            }
        }

        let expected_head =
            expected_history_head.ok_or_else(|| refusal("faithful mirror has no anchor"))?;
        if page.complete {
            if page.next_commitment_cursor != page.head.note_count
                || page.next_history_cursor != page.head.history_records
                || page.next_nullifier_cursor != page.head.nullifier_count
                || expected_head != (page.head.height, page.head.note_count, page.head.root8)
            {
                return Err(refusal(
                    "complete faithful mirror page disagrees with history head",
                ));
            }
            let all_commitments: Vec<_> = self
                .commitments
                .iter()
                .chain(&page.commitments)
                .copied()
                .collect();
            let mut tree =
                Poseidon2NoteTree16::from_commitments(&all_commitments, FAITHFUL_NOTE_DEPTH);
            let local_root = tree.root().limbs().map(BabyBear::as_u32);
            if local_root != page.head.root8 {
                return Err(refusal(
                    "complete faithful mirror commitments do not reconstruct the authenticated root",
                ));
            }
            let records: Vec<_> = self
                .nullifiers
                .iter()
                .chain(&page.nullifiers)
                .map(|record| {
                    (
                        dregg_cell::note::Nullifier(record.nullifier),
                        record.value,
                        record.seq,
                    )
                })
                .collect();
            let nullifier_set = dregg_cell::nullifier_set::NullifierSet::from_records(records)
                .map_err(|error| {
                    refusal_owned(format!(
                        "faithful nullifier mirror cannot be reconstructed: {error}"
                    ))
                })?;
            if nullifier_set
                .faithful_root8_exact()
                .limbs()
                .map(BabyBear::as_u32)
                != page.head.attested_nullifier_root8
            {
                return Err(refusal(
                    "faithful nullifier mirror does not reconstruct the attested root",
                ));
            }
        }

        self.anchor.get_or_insert_with(|| page.anchor.clone());
        self.history.extend(page.history);
        self.commitments.extend(page.commitments);
        self.nullifiers.extend(page.nullifiers);
        self.head = Some(page.head);
        Ok(page.complete)
    }

    /// Construct a depth-16 membership witness locally at one authenticated
    /// historical root. Duplicate commitments are refused as ambiguous.
    pub fn membership_for_commitment(
        &self,
        commitment: [u8; 32],
        root_height: u64,
        historical_note_root: [u32; 8],
    ) -> Result<LocalFaithfulNoteWitness, SdkError> {
        validate_root8("selected historical note", historical_note_root)?;
        let (height, note_count, root) = self
            .history
            .iter()
            .find(|record| {
                record.height == root_height && record.successor_root8 == historical_note_root
            })
            .map(|record| (record.height, record.note_count, record.successor_root8))
            .or_else(|| {
                self.anchor.as_ref().and_then(|anchor| {
                    (anchor.height == root_height && anchor.root8 == historical_note_root)
                        .then_some((anchor.height, anchor.note_count, anchor.root8))
                })
            })
            .ok_or_else(|| refusal("selected root is absent from authenticated local history"))?;
        let count = usize::try_from(note_count)
            .map_err(|_| refusal("selected note count does not fit usize"))?;
        if count > self.commitments.len() {
            return Err(refusal("local mirror has not reached the selected root"));
        }
        let positions: Vec<usize> = self.commitments[..count]
            .iter()
            .enumerate()
            .filter_map(|(position, candidate)| (*candidate == commitment).then_some(position))
            .collect();
        let [position] = positions.as_slice() else {
            return Err(refusal(if positions.is_empty() {
                "commitment is absent from the selected local prefix"
            } else {
                "commitment occurs at multiple positions in the selected local prefix"
            }));
        };
        let mut tree =
            Poseidon2NoteTree16::from_commitments(&self.commitments[..count], FAITHFUL_NOTE_DEPTH);
        if tree.root().limbs().map(BabyBear::as_u32) != root {
            return Err(refusal(
                "selected local prefix does not reconstruct its history root",
            ));
        }
        let membership = tree
            .prove_membership(*position)
            .ok_or_else(|| refusal("local tree could not prove an inserted commitment"))?;
        Ok(LocalFaithfulNoteWitness {
            position: *position as u64,
            note_count,
            root_height: height,
            historical_note_root: root,
            membership,
        })
    }

    /// Assemble every public FNSP input locally.  No HTTP request carries the
    /// future nullifier, value, asset, note position, commitment, or path.
    pub fn prover_context_for_opening(
        &self,
        local: LocalFaithfulNoteWitness,
        opening: &FaithfulNoteOpening,
        prior_spends: &[FaithfulPriorSpend],
    ) -> Result<FaithfulSpendProverContext, SdkError> {
        let head = self
            .head
            .as_ref()
            .ok_or_else(|| refusal("faithful mirror has no synchronized head"))?;
        let authenticated_note_count = self
            .history
            .iter()
            .find(|record| {
                record.height == local.root_height
                    && record.successor_root8 == local.historical_note_root
            })
            .map(|record| record.note_count)
            .or_else(|| {
                self.anchor.as_ref().and_then(|anchor| {
                    (anchor.height == local.root_height
                        && anchor.root8 == local.historical_note_root)
                        .then_some(anchor.note_count)
                })
            });
        let local_count = usize::try_from(local.note_count)
            .map_err(|_| refusal("local witness note count does not fit usize"))?;
        let local_position = usize::try_from(local.position)
            .map_err(|_| refusal("local witness position does not fit usize"))?;
        if self.commitment_cursor() != head.note_count
            || self.history_cursor() != head.history_records
            || self.nullifier_cursor() != head.nullifier_count
            || authenticated_note_count != Some(local.note_count)
            || local_count > self.commitments.len()
            || local_position >= local_count
            || local.membership.positions.len() != FAITHFUL_NOTE_DEPTH
            || local.membership.siblings.len() != FAITHFUL_NOTE_DEPTH
            || local
                .membership
                .positions
                .iter()
                .enumerate()
                .any(|(level, position)| {
                    *position >= 4 || *position != ((local.position >> (2 * level)) & 3) as u8
                })
            || recompose_membership(&local.membership) != local.historical_note_root
        {
            return Err(refusal(
                "faithful mirror is incomplete or local membership is not bound to an authenticated mirror root",
            ));
        }
        let mut selected_tree = Poseidon2NoteTree16::from_commitments(
            &self.commitments[..local_count],
            FAITHFUL_NOTE_DEPTH,
        );
        if selected_tree.root().limbs().map(BabyBear::as_u32) != local.historical_note_root
            || commitment_to_lanes16(&self.commitments[local_position]) != local.membership.leaf
        {
            return Err(refusal(
                "local witness does not open the authenticated commitment prefix at its claimed position",
            ));
        }

        let mut fields = [0u64; 8];
        fields[0] = opening.asset_type;
        fields[1] = opening.value;
        let note = dregg_cell::note::Note::with_nonce(
            opening.owner,
            fields,
            opening.randomness,
            opening.creation_nonce,
        );
        if commitment_to_lanes16(&note.faithful_commitment_v2().0) != local.membership.leaf {
            return Err(refusal(
                "private opening does not match the locally selected commitment",
            ));
        }
        let nullifier = note.faithful_nullifier_v2(&opening.spending_key).0;
        if nullifier == [0; 32] {
            return Err(refusal("derived FNF2 nullifier is all zero"));
        }

        let records: Vec<_> = self
            .nullifiers
            .iter()
            .map(|record| {
                (
                    dregg_cell::note::Nullifier(record.nullifier),
                    record.value,
                    record.seq,
                )
            })
            .collect();
        let mut nullifier_set = dregg_cell::nullifier_set::NullifierSet::from_records(records)
            .map_err(|error| {
                refusal_owned(format!(
                    "faithful nullifier mirror cannot be reconstructed: {error}"
                ))
            })?;
        if nullifier_set
            .faithful_root8_exact()
            .limbs()
            .map(BabyBear::as_u32)
            != head.attested_nullifier_root8
        {
            return Err(refusal(
                "local nullifier mirror is not bound to the mirrored attested head",
            ));
        }

        let mut seen = BTreeSet::new();
        let mut prior_context = Vec::with_capacity(prior_spends.len());
        for (index, prior) in prior_spends.iter().enumerate() {
            if prior.nullifier == [0; 32] || !seen.insert(prior.nullifier) {
                return Err(refusal_owned(format!(
                    "prior spend {index} is zero or duplicated"
                )));
            }
            nullifier_set
                .insert(dregg_cell::note::Nullifier(prior.nullifier), prior.value)
                .map_err(|_| refusal("prior nullifier is already spent"))?;
            prior_context.push(FaithfulPriorSpendContext {
                nullifier: prior.nullifier,
                value: prior.value,
                successor_nullifier_root8: nullifier_set
                    .faithful_root8_exact()
                    .limbs()
                    .map(BabyBear::as_u32),
            });
        }
        if !seen.insert(nullifier) {
            return Err(refusal(
                "current nullifier duplicates an ordered prior spend",
            ));
        }
        let prefix_nullifier_root = nullifier_set
            .faithful_root8_exact()
            .limbs()
            .map(BabyBear::as_u32);
        nullifier_set
            .insert(dregg_cell::note::Nullifier(nullifier), opening.value)
            .map_err(|_| refusal("current nullifier is already spent"))?;

        Ok(FaithfulSpendProverContext {
            history_records: head.history_records,
            note_count: local.note_count,
            position: local.position,
            nullifier,
            value: opening.value,
            asset_type: opening.asset_type,
            prior_spends: prior_context,
            prefix_nullifier_root,
            membership: local.membership,
            historical_note_root: (local.root_height, local.historical_note_root),
            planned_successor_nullifier_root: nullifier_set
                .faithful_root8_exact()
                .limbs()
                .map(BabyBear::as_u32),
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FaithfulSpendProverContext {
    pub history_records: u64,
    pub note_count: u64,
    pub position: u64,
    pub nullifier: [u8; 32],
    pub value: u64,
    pub asset_type: u64,
    pub prior_spends: Vec<FaithfulPriorSpendContext>,
    pub prefix_nullifier_root: [u32; 8],
    pub membership: Poseidon2NoteProof16,
    pub historical_note_root: (u64, [u32; 8]),
    pub planned_successor_nullifier_root: [u32; 8],
}

impl FaithfulSpendProverContext {
    pub fn into_prover_inputs(self) -> (Poseidon2NoteProof16, (u64, [u32; 8]), [u32; 8]) {
        (
            self.membership,
            self.historical_note_root,
            self.planned_successor_nullifier_root,
        )
    }

    pub fn validate_prior_note_spend_effects(
        &self,
        prior_note_spends: &[dregg_turn::Effect],
    ) -> Result<(), SdkError> {
        if prior_note_spends.len() != self.prior_spends.len() {
            return Err(refusal("earlier NoteSpend count does not match local plan"));
        }
        let historical_root_bytes = root8_to_bytes(self.historical_note_root.1);
        for (index, (effect, echoed)) in
            prior_note_spends.iter().zip(&self.prior_spends).enumerate()
        {
            let dregg_turn::Effect::NoteSpend {
                nullifier,
                note_tree_root,
                value,
                spending_proof,
                value_commitment,
                ..
            } = effect
            else {
                return Err(refusal("earlier planned entry is not a NoteSpend"));
            };
            let carrier = FaithfulNoteSpendProofCarrier::decode(spending_proof)
                .map_err(|_| refusal("earlier NoteSpend has invalid FNSP carrier"))?;
            if nullifier.0 != echoed.nullifier
                || *value != echoed.value
                || *note_tree_root != historical_root_bytes
                || carrier.root_height() != self.historical_note_root.0
                || carrier.successor_nullifier_root()
                    != root8_to_bytes(echoed.successor_nullifier_root8)
                || value_commitment.is_some()
            {
                return Err(refusal_owned(format!(
                    "earlier NoteSpend {index} does not match the ordered local plan"
                )));
            }
        }
        Ok(())
    }

    pub fn prove(
        self,
        opening: &FaithfulNoteOpening,
    ) -> Result<FaithfulHiddenSpendProof, SdkError> {
        if opening.value != self.value || opening.asset_type != self.asset_type {
            return Err(refusal(
                "private opening value/asset does not match the local plan",
            ));
        }
        let mut fields = [0u64; 8];
        fields[0] = opening.asset_type;
        fields[1] = opening.value;
        let note = dregg_cell::note::Note::with_nonce(
            opening.owner,
            fields,
            opening.randomness,
            opening.creation_nonce,
        );
        if note.faithful_nullifier_v2(&opening.spending_key).0 != self.nullifier
            || commitment_to_lanes16(&note.faithful_commitment_v2().0) != self.membership.leaf
        {
            return Err(refusal(
                "private opening does not match the locally mirrored note/nullifier",
            ));
        }
        build_faithful_hidden_spend_proof(
            opening,
            &self.membership,
            self.historical_note_root,
            self.planned_successor_nullifier_root,
        )
    }

    pub fn prove_note_spend_effect(
        self,
        opening: &FaithfulNoteOpening,
    ) -> Result<dregg_turn::Effect, SdkError> {
        Ok(self.prove(opening)?.into_note_spend_effect())
    }
}

impl NodeHttpClient {
    /// Synchronize every missing global page.  There is no target-page method:
    /// a fresh mirror necessarily starts at zero and an existing mirror follows
    /// only its exact next cursors.
    pub async fn sync_faithful_note_mirror(
        &self,
        mirror: &mut FaithfulNoteMirror,
        trust: &FaithfulNoteMirrorTrust,
    ) -> Result<(), SdkError> {
        // One O(n) snapshot makes the *entire* network sync transactional.  A
        // malicious/broken peer cannot feed valid-looking intermediate pages,
        // fail terminal root authentication, and leave the caller's durable
        // mirror poisoned for its next peer.
        let mut candidate = mirror.clone();
        loop {
            let request = FaithfulNoteMirrorRequest {
                commitment_cursor: candidate.commitment_cursor(),
                history_cursor: candidate.history_cursor(),
                nullifier_cursor: candidate.nullifier_cursor(),
            };
            let response = self
                .http_client()
                .post(format!(
                    "{}/api/notes/faithful-spend/mirror",
                    self.base_url()
                ))
                .json(&request)
                .send()
                .await
                .map_err(|error| refusal_owned(format!("mirror request failed: {error}")))?;
            let status = response.status();
            if !status.is_success() {
                return Err(http_refusal("mirror", status, response).await);
            }
            let page = response
                .json::<FaithfulNoteMirrorResponse>()
                .await
                .map_err(|error| refusal_owned(format!("parse mirror page: {error}")))?;
            if candidate.apply_page(page, trust)? {
                *mirror = candidate;
                return Ok(());
            }
        }
    }
}

#[derive(Debug, Deserialize)]
struct ErrorResponse {
    error: String,
}

async fn http_refusal(
    surface: &str,
    status: reqwest::StatusCode,
    response: reqwest::Response,
) -> SdkError {
    let reason = response
        .json::<ErrorResponse>()
        .await
        .map(|body| body.error)
        .unwrap_or_else(|_| "malformed error response".to_string());
    refusal_owned(format!("faithful {surface} returned {status}: {reason}"))
}

fn validate_history_record(
    record: &FaithfulNoteMirrorRecord,
    anchor: &FaithfulNoteMirrorAnchor,
    previous: Option<(u64, u64, [u32; 8])>,
) -> Result<(), SdkError> {
    validate_root8("history predecessor", record.predecessor_root8)?;
    validate_root8("history successor", record.successor_root8)?;
    let Some((previous_height, previous_count, previous_root)) = previous else {
        return Err(refusal("history record has no pinned predecessor"));
    };
    let expected_height = previous_height
        .checked_add(1)
        .ok_or_else(|| refusal("history predecessor height cannot advance"))?;
    if record.session_id != anchor.session_id
        || record.federation_id != anchor.federation_id
        || record.committee_epoch != anchor.committee_epoch
        || record.previous_height != previous_height
        || record.height != expected_height
        || record.previous_note_count != previous_count
        || record.predecessor_root8 != previous_root
        || record.note_count < previous_count
        || ((record.note_count != previous_count)
            != (record.successor_root8 != record.predecessor_root8))
    {
        return Err(refusal(
            "history record is not an exact append-only extension",
        ));
    }
    Ok(())
}

fn history_signing_message(record: &FaithfulNoteMirrorRecord) -> [u8; 208] {
    let mut out = [0u8; 208];
    out[0..4].copy_from_slice(b"FNHR");
    out[4..6].copy_from_slice(&1u16.to_le_bytes());
    out[6..8].copy_from_slice(&0u16.to_le_bytes());
    out[8..40].copy_from_slice(&record.session_id);
    out[40..72].copy_from_slice(&record.federation_id);
    out[72..80].copy_from_slice(&record.committee_epoch.to_le_bytes());
    out[80..88].copy_from_slice(&record.previous_height.to_le_bytes());
    out[88..96].copy_from_slice(&record.height.to_le_bytes());
    out[96..104].copy_from_slice(&record.previous_note_count.to_le_bytes());
    out[104..112].copy_from_slice(&record.note_count.to_le_bytes());
    out[112..144].copy_from_slice(&root8_to_bytes(record.predecessor_root8));
    out[144..176].copy_from_slice(&root8_to_bytes(record.successor_root8));
    out[176..208].copy_from_slice(&record.block_id);
    out
}

fn mirror_head_signing_message(
    anchor: &FaithfulNoteMirrorAnchor,
    head: &FaithfulNoteMirrorHead,
) -> [u8; 176] {
    let mut out = [0u8; 176];
    out[0..4].copy_from_slice(b"FNMS");
    out[4..6].copy_from_slice(&1u16.to_le_bytes());
    out[6..8].copy_from_slice(&0u16.to_le_bytes());
    out[8..40].copy_from_slice(&anchor.session_id);
    out[40..72].copy_from_slice(&anchor.federation_id);
    out[72..80].copy_from_slice(&anchor.committee_epoch.to_le_bytes());
    out[80..88].copy_from_slice(&head.history_records.to_le_bytes());
    out[88..96].copy_from_slice(&head.height.to_le_bytes());
    out[96..104].copy_from_slice(&head.note_count.to_le_bytes());
    out[104..136].copy_from_slice(&root8_to_bytes(head.root8));
    out[136..144].copy_from_slice(&head.nullifier_count.to_le_bytes());
    out[144..176].copy_from_slice(&root8_to_bytes(head.attested_nullifier_root8));
    out
}

fn root8_to_bytes(root: [u32; 8]) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    for (lane, value) in root.into_iter().enumerate() {
        bytes[4 * lane..4 * lane + 4].copy_from_slice(&value.to_le_bytes());
    }
    bytes
}

fn validate_root8(name: &str, root: [u32; 8]) -> Result<(), SdkError> {
    if let Some((lane, value)) = root
        .into_iter()
        .enumerate()
        .find(|(_, value)| *value >= BABYBEAR_P)
    {
        return Err(refusal_owned(format!(
            "{name} root lane {lane}={value} is noncanonical for BabyBear"
        )));
    }
    Ok(())
}

fn recompose_membership(proof: &Poseidon2NoteProof16) -> [u32; 8] {
    let mut current = note_leaf16(&proof.leaf);
    for (siblings, &position) in proof.siblings.iter().zip(&proof.positions) {
        let mut children = [[BabyBear::ZERO; 8]; 4];
        let mut sibling = 0;
        for child in 0..4u8 {
            if child == position {
                children[child as usize] = current;
            } else {
                children[child as usize] = siblings[sibling];
                sibling += 1;
            }
        }
        current = note_node8(&children);
    }
    current.map(BabyBear::as_u32)
}

fn refusal(reason: &'static str) -> SdkError {
    refusal_owned(reason.to_string())
}

fn refusal_owned(reason: String) -> SdkError {
    SdkError::Wire(format!("faithful spend refused: {reason}"))
}

mod lower_hex32 {
    use serde::de::Error as _;
    use serde::{Deserialize, Deserializer, Serializer};

    pub fn serialize<S>(bytes: &[u8; 32], serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&hex::encode(bytes))
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<[u8; 32], D::Error>
    where
        D: Deserializer<'de>,
    {
        let text = String::deserialize(deserializer)?;
        if text.len() != 64
            || !text
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        {
            return Err(D::Error::custom(
                "expected 64 lowercase hexadecimal characters",
            ));
        }
        hex::decode(text)
            .map_err(D::Error::custom)?
            .try_into()
            .map_err(|_| D::Error::custom("expected exactly 32 decoded bytes"))
    }
}

mod lower_hex32_vec {
    use serde::de::Error as _;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S>(values: &[[u8; 32]], serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        values
            .iter()
            .map(hex::encode)
            .collect::<Vec<_>>()
            .serialize(serializer)
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<Vec<[u8; 32]>, D::Error>
    where
        D: Deserializer<'de>,
    {
        Vec::<String>::deserialize(deserializer)?
            .into_iter()
            .map(|text| {
                if text.len() != 64
                    || !text
                        .bytes()
                        .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
                {
                    return Err(D::Error::custom(
                        "expected 64 lowercase hexadecimal characters",
                    ));
                }
                hex::decode(text)
                    .map_err(D::Error::custom)?
                    .try_into()
                    .map_err(|_| D::Error::custom("expected exactly 32 decoded bytes"))
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn serve_json_pages(
        pages: Vec<FaithfulNoteMirrorResponse>,
    ) -> (String, std::thread::JoinHandle<()>) {
        use std::io::{Read, Write};

        let listener = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
        listener.set_nonblocking(true).unwrap();
        let address = listener.local_addr().unwrap();
        let handle = std::thread::spawn(move || {
            for page in pages {
                let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
                let (mut stream, _) = loop {
                    match listener.accept() {
                        Ok(connection) => break connection,
                        Err(error)
                            if error.kind() == std::io::ErrorKind::WouldBlock
                                && std::time::Instant::now() < deadline =>
                        {
                            std::thread::sleep(std::time::Duration::from_millis(10));
                        }
                        Err(_) => return,
                    }
                };
                stream
                    .set_read_timeout(Some(std::time::Duration::from_secs(5)))
                    .unwrap();
                let mut request = [0u8; 4096];
                let _ = stream.read(&mut request).unwrap();
                let body = serde_json::to_vec(&page).unwrap();
                write!(
                    stream,
                    "HTTP/1.1 200 OK\r\ncontent-type: application/json\r\ncontent-length: {}\r\nconnection: close\r\n\r\n",
                    body.len()
                )
                .unwrap();
                stream.write_all(&body).unwrap();
                stream.flush().unwrap();
            }
        });
        (format!("http://{address}"), handle)
    }

    fn sign_head(
        seed: [u8; 32],
        anchor: &FaithfulNoteMirrorAnchor,
        head: &FaithfulNoteMirrorHead,
    ) -> (HybridQuorumSig, PublicKey, MlDsaPublicKey) {
        let signing_key = dregg_types::SigningKey::from_bytes(&seed);
        let public_key = signing_key.public_key();
        let (pq_public_key, pq_signing_key) =
            dregg_federation::frost::MlDsaSigningKey::from_seed(&seed);
        let message = mirror_head_signing_message(anchor, head);
        (
            HybridQuorumSig {
                pubkey: public_key,
                signature: dregg_types::sign(&signing_key, &message),
                ml_dsa_pubkey: pq_public_key.0.to_vec(),
                pq_signature: pq_signing_key.sign(&message).expect("ML-DSA test signing"),
            },
            public_key,
            pq_public_key,
        )
    }

    fn empty_signed_page() -> (
        FaithfulNoteMirrorResponse,
        FaithfulNoteMirrorTrust,
        [u8; 32],
    ) {
        let seed = [0x71; 32];
        let mut note_tree = Poseidon2NoteTree16::new();
        let note_root = note_tree.root().limbs().map(BabyBear::as_u32);
        let nullifier_root = dregg_cell::nullifier_set::NullifierSet::new()
            .faithful_root8_exact()
            .limbs()
            .map(BabyBear::as_u32);
        let anchor = FaithfulNoteMirrorAnchor {
            session_id: [0x11; 32],
            federation_id: [0x22; 32],
            committee_epoch: 9,
            height: 41,
            note_count: 0,
            root8: note_root,
        };
        let head = FaithfulNoteMirrorHead {
            history_records: 0,
            height: anchor.height,
            note_count: 0,
            root8: note_root,
            nullifier_count: 0,
            attested_nullifier_root8: nullifier_root,
        };
        let (signature, public_key, pq_public_key) = sign_head(seed, &anchor, &head);
        let page = FaithfulNoteMirrorResponse {
            protocol: MIRROR_PROTOCOL.to_string(),
            commitment_cursor: 0,
            next_commitment_cursor: 0,
            history_cursor: 0,
            next_history_cursor: 0,
            nullifier_cursor: 0,
            next_nullifier_cursor: 0,
            commitments: Vec::new(),
            nullifiers: Vec::new(),
            anchor: anchor.clone(),
            history: Vec::new(),
            head,
            head_hybrid_quorum: vec![signature],
            complete: true,
            privacy: "test fixture".to_string(),
        };
        let trust = FaithfulNoteMirrorTrust {
            anchor,
            author_committee: vec![public_key],
            author_ml_dsa_committee: vec![pq_public_key],
            threshold: 1,
        };
        (page, trust, seed)
    }

    #[test]
    fn only_supported_http_request_has_three_global_cursors_and_no_target() {
        let request = FaithfulNoteMirrorRequest {
            commitment_cursor: 256,
            history_cursor: 16,
            nullifier_cursor: 256,
        };
        let json = serde_json::to_value(&request).unwrap();
        assert_eq!(json.as_object().unwrap().len(), 3);
        assert_eq!(json["commitment_cursor"], 256);
        assert_eq!(json["history_cursor"], 16);
        assert_eq!(json["nullifier_cursor"], 256);
        assert!(json.get("position").is_none());
        assert!(json.get("commitment").is_none());
        assert!(json.get("leaf").is_none());
        assert!(json.get("membership").is_none());
        assert!(json.get("siblings").is_none());
        assert!(json.get("nullifier").is_none());
        assert!(json.get("value").is_none());
        assert!(json.get("asset_type").is_none());
        assert!(
            serde_json::from_value::<FaithfulNoteMirrorRequest>(serde_json::json!({
                "commitment_cursor": 0,
                "history_cursor": 0,
                "nullifier_cursor": 0,
                "target_commitment": hex::encode([0xAA; 32]),
            }))
            .is_err(),
            "target-specific extensions must fail closed instead of being ignored"
        );
    }

    #[test]
    fn opening_membership_and_nullifier_successor_are_assembled_locally() {
        let opening = FaithfulNoteOpening {
            spending_key: [0x31; 32],
            owner: dregg_cell::note::Note::faithful_owner_v2(&[0x31; 32]),
            value: 50,
            asset_type: 2,
            creation_nonce: [0x32; 32],
            randomness: [0x33; 32],
        };
        let mut fields = [0u64; 8];
        fields[0] = opening.asset_type;
        fields[1] = opening.value;
        let note = dregg_cell::note::Note::with_nonce(
            opening.owner,
            fields,
            opening.randomness,
            opening.creation_nonce,
        );
        let commitment = note.faithful_commitment_v2().0;
        let commitments = vec![[0x11; 32], commitment, [0x22; 32]];
        let mut tree = Poseidon2NoteTree16::from_commitments(&commitments, FAITHFUL_NOTE_DEPTH);
        let root = tree.root().limbs().map(BabyBear::as_u32);
        let empty_nullifier_root = dregg_cell::nullifier_set::NullifierSet::new()
            .faithful_root8_exact()
            .limbs()
            .map(BabyBear::as_u32);
        let anchor = FaithfulNoteMirrorAnchor {
            session_id: [1; 32],
            federation_id: [2; 32],
            committee_epoch: 3,
            height: 12,
            note_count: commitments.len() as u64,
            root8: root,
        };
        let mirror = FaithfulNoteMirror {
            commitments,
            history: Vec::new(),
            nullifiers: Vec::new(),
            anchor: Some(anchor),
            head: Some(FaithfulNoteMirrorHead {
                history_records: 0,
                height: 12,
                note_count: 3,
                root8: root,
                nullifier_count: 0,
                attested_nullifier_root8: empty_nullifier_root,
            }),
        };
        let local = mirror
            .membership_for_commitment(commitment, 12, root)
            .unwrap();
        let context = mirror
            .prover_context_for_opening(local, &opening, &[])
            .unwrap();
        assert_eq!(context.position, 1);
        assert_eq!(
            context.nullifier,
            note.faithful_nullifier_v2(&opening.spending_key).0
        );
        assert_ne!(
            context.planned_successor_nullifier_root,
            empty_nullifier_root
        );
    }

    #[test]
    fn signed_empty_head_applies_and_tampered_head_refuses() {
        let (page, trust, _) = empty_signed_page();
        let mut mirror = FaithfulNoteMirror::default();
        assert!(mirror.apply_page(page.clone(), &trust).unwrap());
        assert_eq!(mirror.head(), Some(&page.head));

        let mut tampered = page;
        tampered.head.height += 1;
        let mut fresh = FaithfulNoteMirror::default();
        assert!(fresh.apply_page(tampered, &trust).is_err());
        assert!(fresh.head().is_none());
    }

    #[test]
    fn rejected_terminal_page_is_transactional_without_cloning_the_prefix() {
        let (mut page, trust, seed) = empty_signed_page();
        page.nullifiers.push(FaithfulNullifierMirrorRecord {
            nullifier: [0x44; 32],
            value: 17,
            seq: 0,
        });
        page.next_nullifier_cursor = 1;
        page.head.nullifier_count = 1;
        // Canonical but deliberately not the root reconstructed by the row.
        page.head.attested_nullifier_root8 = [1; 8];
        page.head_hybrid_quorum = vec![sign_head(seed, &page.anchor, &page.head).0];

        let mut mirror = FaithfulNoteMirror::default();
        assert!(mirror.apply_page(page, &trust).is_err());
        assert_eq!(mirror.commitment_cursor(), 0);
        assert_eq!(mirror.history_cursor(), 0);
        assert_eq!(mirror.nullifier_cursor(), 0);
        assert!(mirror.anchor.is_none());
        assert!(mirror.head.is_none());
    }

    #[test]
    fn fixed_pages_refuse_short_nonterminal_and_no_progress() {
        let (mut short, trust, seed) = empty_signed_page();
        short.commitments.push([0x33; 32]);
        short.next_commitment_cursor = 1;
        short.head.note_count = (COMMITMENT_PAGE_SIZE + 1) as u64;
        short.complete = false;
        short.head_hybrid_quorum = vec![sign_head(seed, &short.anchor, &short.head).0];
        assert!(
            FaithfulNoteMirror::default()
                .apply_page(short, &trust)
                .is_err()
        );

        let (mut stalled, trust, _) = empty_signed_page();
        stalled.complete = false;
        assert!(
            FaithfulNoteMirror::default()
                .apply_page(stalled, &trust)
                .is_err()
        );
    }

    #[test]
    fn history_segment_splice_and_height_overflow_refuse() {
        let (_, trust, _) = empty_signed_page();
        let anchor = &trust.anchor;
        let record = FaithfulNoteMirrorRecord {
            session_id: [0x99; 32],
            federation_id: anchor.federation_id,
            committee_epoch: anchor.committee_epoch,
            previous_height: anchor.height,
            height: anchor.height + 1,
            previous_note_count: anchor.note_count,
            note_count: anchor.note_count,
            predecessor_root8: anchor.root8,
            successor_root8: anchor.root8,
            block_id: [0x55; 32],
            hybrid_quorum: Vec::new(),
        };
        assert!(
            validate_history_record(
                &record,
                anchor,
                Some((anchor.height, anchor.note_count, anchor.root8)),
            )
            .is_err()
        );
        assert!(
            validate_history_record(
                &record,
                anchor,
                Some((u64::MAX, anchor.note_count, anchor.root8)),
            )
            .is_err()
        );
    }

    #[tokio::test]
    async fn later_terminal_failure_leaves_caller_mirror_unchanged() {
        let (mut page, mut trust, seed) = empty_signed_page();
        let commitments = vec![[0x33; 32]; COMMITMENT_PAGE_SIZE + 1];
        let mut tree = Poseidon2NoteTree16::from_commitments(&commitments, FAITHFUL_NOTE_DEPTH);
        let root = tree.root().limbs().map(BabyBear::as_u32);
        page.anchor.note_count = commitments.len() as u64;
        page.anchor.root8 = root;
        page.head.note_count = commitments.len() as u64;
        page.head.root8 = root;
        trust.anchor = page.anchor.clone();
        page.commitments = commitments[..COMMITMENT_PAGE_SIZE].to_vec();
        page.next_commitment_cursor = COMMITMENT_PAGE_SIZE as u64;
        page.complete = false;
        page.head_hybrid_quorum = vec![sign_head(seed, &page.anchor, &page.head).0];

        let mut terminal = page.clone();
        terminal.commitment_cursor = COMMITMENT_PAGE_SIZE as u64;
        terminal.next_commitment_cursor = commitments.len() as u64;
        terminal.commitments = vec![[0x44; 32]];
        terminal.complete = true;

        let (base_url, server) = serve_json_pages(vec![page, terminal]);
        let client = NodeHttpClient::new(base_url);
        let mut mirror = FaithfulNoteMirror::default();
        assert!(
            client
                .sync_faithful_note_mirror(&mut mirror, &trust)
                .await
                .is_err()
        );
        server.join().unwrap();
        assert_eq!(mirror.commitment_cursor(), 0);
        assert_eq!(mirror.history_cursor(), 0);
        assert_eq!(mirror.nullifier_cursor(), 0);
        assert!(mirror.anchor.is_none());
        assert!(mirror.head.is_none());
    }

    #[test]
    fn duplicate_and_reordered_pages_refuse_without_advancing_prefix() {
        let (mut first, mut trust, seed) = empty_signed_page();
        let commitments = vec![[0x53; 32]; COMMITMENT_PAGE_SIZE + 1];
        let mut tree = Poseidon2NoteTree16::from_commitments(&commitments, FAITHFUL_NOTE_DEPTH);
        let root = tree.root().limbs().map(BabyBear::as_u32);
        first.anchor.note_count = commitments.len() as u64;
        first.anchor.root8 = root;
        first.head.note_count = commitments.len() as u64;
        first.head.root8 = root;
        trust.anchor = first.anchor.clone();
        first.commitments = commitments[..COMMITMENT_PAGE_SIZE].to_vec();
        first.next_commitment_cursor = COMMITMENT_PAGE_SIZE as u64;
        first.complete = false;
        first.head_hybrid_quorum = vec![sign_head(seed, &first.anchor, &first.head).0];

        let mut terminal = first.clone();
        terminal.commitment_cursor = COMMITMENT_PAGE_SIZE as u64;
        terminal.next_commitment_cursor = commitments.len() as u64;
        terminal.commitments = vec![commitments[COMMITMENT_PAGE_SIZE]];
        terminal.complete = true;

        let mut mirror = FaithfulNoteMirror::default();
        assert!(!mirror.apply_page(first.clone(), &trust).unwrap());
        assert_eq!(mirror.commitment_cursor(), COMMITMENT_PAGE_SIZE as u64);
        assert!(mirror.apply_page(first, &trust).is_err());
        assert_eq!(mirror.commitment_cursor(), COMMITMENT_PAGE_SIZE as u64);

        let mut fresh = FaithfulNoteMirror::default();
        assert!(fresh.apply_page(terminal.clone(), &trust).is_err());
        assert_eq!(fresh.commitment_cursor(), 0);
        assert!(mirror.apply_page(terminal, &trust).unwrap());
        assert_eq!(mirror.commitment_cursor(), commitments.len() as u64);
    }
}
