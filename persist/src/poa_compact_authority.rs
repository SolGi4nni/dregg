//! Compaction-stable authority for finalized Path of Angels sidecars.
//!
//! A ledger checkpoint subsumes the cell write-set of a finalized turn, but it does not subsume
//! the turn/receipt coordinates which authenticate PoA journals.  Deleting a [`CommitRecord`]
//! while retaining only its block id therefore degrades an exact carrier check into membership in
//! an unrelated set.  This module keeps a bounded certificate for every compacted record:
//!
//! * every scalar field of the original generic commit;
//! * a digest of the removed write set;
//! * the covering checkpoint coordinate; and
//! * the exact key + wire digest of every PoA sidecar at that ordinal.
//!
//! Certificates form one dense predecessor-digest chain. Before deletion, a real enrolled hybrid
//! quorum signs the exact terminal head together with the deployment/federation, compacted range,
//! and canonical checkpoint bytes/root. Re-sealing local frames cannot forge that external anchor;
//! omission or invention of a sidecar disagrees with the certificate captured before removal.

use std::collections::{BTreeMap, BTreeSet};

use dregg_federation::frost::MlDsaPublicKey;
use dregg_types::{HybridQuorumSig, PublicKey};
use redb::{
    ReadTransaction, ReadableTable, ReadableTableMetadata, TableDefinition, WriteTransaction,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{CommitRecord, PersistentStore, Result, StoreError, tables};

pub(crate) const POA_COMPACT_AUTHORITY_CERTIFICATES_V1: TableDefinition<u64, &[u8]> =
    TableDefinition::new("poa_compact_authority_certificates_v1");
pub(crate) const POA_COMPACT_AUTHORITY_HEAD_V1: TableDefinition<&str, &[u8]> =
    TableDefinition::new("poa_compact_authority_head_v1");
pub(crate) const POA_COMPACT_CHECKPOINT_ANCHORS_V1: TableDefinition<u64, &[u8]> =
    TableDefinition::new("poa_compact_checkpoint_anchors_v1");

const HEAD_KEY: &str = "head";
const CERT_MAGIC: [u8; 4] = *b"PCC1";
const HEAD_MAGIC: [u8; 4] = *b"PCH1";
const ANCHOR_MAGIC: [u8; 4] = *b"PCA1";
const FRAME_VERSION: u8 = 1;
const FRAME_HEADER_LEN: usize = 12;
const FRAME_SEAL_LEN: usize = 32;
const MAX_FRAME_BYTES: usize = 4 * 1024 * 1024;
const MAX_ANCHOR_COMMITTEE_MEMBERS: usize = 128;
const CERTIFICATE_DIGEST_DOMAIN: &[u8] = b"dregg-poa-compact-authority-certificate-v1\0";
const FRAME_SEAL_DOMAIN: &[u8] = b"dregg-poa-compact-authority-frame-v1\0";
const CHECKPOINT_WIRE_DOMAIN: &[u8] = b"dregg-poa-compact-checkpoint-wire-v1\0";
const CHECKPOINT_ANCHOR_DOMAIN: &[u8] = b"dregg-poa-compact-checkpoint-anchor-v1\0";
const WRITE_SET_DOMAIN: &[u8] = b"dregg-poa-compact-authority-write-set-v1\0";
const SIDECAR_KEY_DOMAIN: &[u8] = b"dregg-poa-compact-authority-sidecar-key-v1\0";
const SIDECAR_WIRE_DOMAIN: &[u8] = b"dregg-poa-compact-authority-sidecar-wire-v1\0";

const SIGNAL_KIND: u8 = 1;
const EVENT_V1_KIND: u8 = 2;
const EVENT_BATCH_V2_KIND: u8 = 3;
const HOLDING_KIND: u8 = 4;
const META_POA_COMPACT_AUTHORITY_SCHEMA_V1: &str = "poa_compact_authority_schema_v1";
const POA_COMPACT_AUTHORITY_SCHEMA_V1: u64 = 1;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct CompactPoaSidecarIdentityV1 {
    kind: u8,
    key_digest: [u8; 32],
    wire_digest: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct CompactCommitAuthorityCertificateV1 {
    predecessor_certificate_digest: [u8; 32],
    ordinal: u64,
    height: u64,
    block_id: [u8; 32],
    block_executed_up_to: u64,
    turn_hash: [u8; 32],
    creator: [u8; 32],
    receipt_hash: [u8; 32],
    ledger_root: [u8; 32],
    write_set_digest: [u8; 32],
    covering_checkpoint_height: u64,
    covering_checkpoint_wire_digest: [u8; 32],
    covering_checkpoint_ledger_root: [u8; 32],
    poa_sidecars: Vec<CompactPoaSidecarIdentityV1>,
}

/// The exact statement a finalized hybrid committee signs before any commit row is deleted.
///
/// `certificate_head` is the digest of the last certificate after extending the dense chain
/// through `new_floor`. The checkpoint digest is over the exact canonical postcard bytes stored
/// in `LEDGER_CHECKPOINTS`; the root is independently reconstructed from those bytes.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PoaCompactCheckpointStatementV1 {
    federation_id: [u8; 32],
    deployment_id: [u8; 32],
    committee_epoch: u64,
    old_floor: u64,
    new_floor: u64,
    checkpoint_height: u64,
    checkpoint_wire_digest: [u8; 32],
    checkpoint_ledger_root: [u8; 32],
    certificate_count: u64,
    certificate_head: [u8; 32],
}

/// A genuine classical-and-post-quantum quorum over one compaction statement.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SignedPoaCompactCheckpointAnchorV1 {
    statement: PoaCompactCheckpointStatementV1,
    hybrid_quorum: Vec<HybridQuorumSig>,
}

/// One independently trusted hybrid committee authorized to sign PoA compaction anchors.
///
/// This value is deliberately **not** decoded from the ledger database. Production callers derive
/// it from their authenticated deployment/genesis configuration and supply it both when compacting
/// and when reopening a compacted store. A roster carried by a stored anchor is only redundant
/// evidence and must equal this root byte-for-byte.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoaCompactTrustRootV1 {
    deployment_id: [u8; 32],
    federation_id: [u8; 32],
    committee_epoch: u64,
    committee: Vec<PublicKey>,
    ml_dsa_committee: Vec<MlDsaPublicKey>,
    threshold: usize,
}

/// Caller-supplied authenticated committee history for one deployment.
///
/// Rotation is append-only from the database's point of view: every stored anchor must resolve to
/// an exact root in this external policy, and anchor epochs may never decrease. Removing an older
/// root makes a store containing an anchor from that epoch fail closed. Adding a future epoch is
/// therefore meaningful only after the deployment's independent genesis/configuration authority
/// authenticates that update; the PCC tables cannot install or update this policy.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoaCompactTrustPolicyV1 {
    deployment_id: [u8; 32],
    roots_by_epoch: BTreeMap<u64, PoaCompactTrustRootV1>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct StoredPoaCompactCheckpointAnchorV1 {
    signed: SignedPoaCompactCheckpointAnchorV1,
    committee: Vec<PublicKey>,
    ml_dsa_committee: Vec<Vec<u8>>,
    threshold: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct CheckpointIdentityV1 {
    height: u64,
    wire_digest: [u8; 32],
    ledger_root: [u8; 32],
}

/// The immutable finalized coordinates PoA semantic replay is allowed to consume.
///
/// A value comes either from a live [`CommitRecord`] or from its audited compact certificate.
/// The write set deliberately remains represented by its digest: callers which need to re-apply
/// cells must use the live record, while an exact retry supplies the original record and proves
/// that complete write set against this digest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FinalizedCommitAuthorityV1 {
    ordinal: u64,
    height: u64,
    block_id: [u8; 32],
    block_executed_up_to: u64,
    turn_hash: [u8; 32],
    creator: [u8; 32],
    receipt_hash: [u8; 32],
    ledger_root: [u8; 32],
    write_set_digest: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct CompactAuthorityHeadV1 {
    next_ordinal: u64,
    certificate_digest: [u8; 32],
}

impl PoaCompactCheckpointStatementV1 {
    pub fn signing_message(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(CHECKPOINT_ANCHOR_DOMAIN.len() + 8 * 6 + 32 * 5);
        out.extend_from_slice(CHECKPOINT_ANCHOR_DOMAIN);
        out.extend_from_slice(&self.federation_id);
        out.extend_from_slice(&self.deployment_id);
        out.extend_from_slice(&self.committee_epoch.to_le_bytes());
        out.extend_from_slice(&self.old_floor.to_le_bytes());
        out.extend_from_slice(&self.new_floor.to_le_bytes());
        out.extend_from_slice(&self.checkpoint_height.to_le_bytes());
        out.extend_from_slice(&self.checkpoint_wire_digest);
        out.extend_from_slice(&self.checkpoint_ledger_root);
        out.extend_from_slice(&self.certificate_count.to_le_bytes());
        out.extend_from_slice(&self.certificate_head);
        out
    }

    pub const fn federation_id(&self) -> [u8; 32] {
        self.federation_id
    }

    pub const fn deployment_id(&self) -> [u8; 32] {
        self.deployment_id
    }

    pub const fn committee_epoch(&self) -> u64 {
        self.committee_epoch
    }

    pub const fn old_floor(&self) -> u64 {
        self.old_floor
    }

    pub const fn new_floor(&self) -> u64 {
        self.new_floor
    }

    pub const fn checkpoint_height(&self) -> u64 {
        self.checkpoint_height
    }

    pub const fn checkpoint_wire_digest(&self) -> [u8; 32] {
        self.checkpoint_wire_digest
    }

    pub const fn checkpoint_ledger_root(&self) -> [u8; 32] {
        self.checkpoint_ledger_root
    }

    pub const fn certificate_count(&self) -> u64 {
        self.certificate_count
    }

    pub const fn certificate_head(&self) -> [u8; 32] {
        self.certificate_head
    }

    fn validate_shape(&self) -> Result<()> {
        if self.federation_id == [0; 32]
            || self.deployment_id == [0; 32]
            || self.checkpoint_wire_digest == [0; 32]
            || self.checkpoint_ledger_root == [0; 32]
            || self.certificate_head == [0; 32]
            || self.old_floor >= self.new_floor
            || self.certificate_count != self.new_floor
        {
            return Err(integrity(
                "PoA compact checkpoint statement is malformed or vacuous",
            ));
        }
        Ok(())
    }
}

impl SignedPoaCompactCheckpointAnchorV1 {
    pub fn new(
        statement: PoaCompactCheckpointStatementV1,
        hybrid_quorum: Vec<HybridQuorumSig>,
    ) -> Self {
        Self {
            statement,
            hybrid_quorum,
        }
    }

    pub const fn statement(&self) -> &PoaCompactCheckpointStatementV1 {
        &self.statement
    }

    pub fn hybrid_quorum(&self) -> &[HybridQuorumSig] {
        &self.hybrid_quorum
    }
}

impl PoaCompactTrustRootV1 {
    pub fn new(
        deployment_id: [u8; 32],
        federation_id: [u8; 32],
        committee_epoch: u64,
        committee: Vec<PublicKey>,
        ml_dsa_committee: Vec<MlDsaPublicKey>,
        threshold: usize,
    ) -> Result<Self> {
        let root = Self {
            deployment_id,
            federation_id,
            committee_epoch,
            committee,
            ml_dsa_committee,
            threshold,
        };
        root.validate()?;
        Ok(root)
    }

    fn validate(&self) -> Result<()> {
        if self.deployment_id == [0; 32] || self.federation_id == [0; 32] {
            return Err(integrity(
                "PoA compact trust root has a vacuous deployment or federation id",
            ));
        }
        if self.committee.is_empty()
            || self.committee.len() > MAX_ANCHOR_COMMITTEE_MEMBERS
            || self.committee.len() != self.ml_dsa_committee.len()
        {
            return Err(integrity(
                "PoA compact trust root committee is empty, oversized, or misaligned",
            ));
        }
        if self.threshold == 0
            || self.threshold > self.committee.len()
            || self.threshold != dregg_federation::quorum_threshold(self.committee.len())
        {
            return Err(integrity("PoA compact trust root threshold is invalid"));
        }
        let distinct_classical: BTreeSet<[u8; 32]> =
            self.committee.iter().map(|key| key.0).collect();
        let distinct_pq: BTreeSet<Vec<u8>> = self
            .ml_dsa_committee
            .iter()
            .map(|key| key.0.to_vec())
            .collect();
        if distinct_classical.len() != self.committee.len()
            || distinct_pq.len() != self.ml_dsa_committee.len()
        {
            return Err(integrity(
                "PoA compact trust root roster contains duplicate identities",
            ));
        }
        let derived_federation = dregg_federation::derive_federation_id_hybrid_with_epoch(
            &self.committee,
            &self.ml_dsa_committee,
            self.committee_epoch,
        );
        if derived_federation != self.federation_id {
            return Err(integrity(
                "PoA compact trust root federation id does not bind its exact hybrid roster",
            ));
        }
        Ok(())
    }

    pub const fn deployment_id(&self) -> [u8; 32] {
        self.deployment_id
    }

    pub const fn federation_id(&self) -> [u8; 32] {
        self.federation_id
    }

    pub const fn committee_epoch(&self) -> u64 {
        self.committee_epoch
    }

    pub fn committee(&self) -> &[PublicKey] {
        &self.committee
    }

    pub fn ml_dsa_committee(&self) -> &[MlDsaPublicKey] {
        &self.ml_dsa_committee
    }

    pub const fn threshold(&self) -> usize {
        self.threshold
    }
}

impl PoaCompactTrustPolicyV1 {
    pub fn new(roots: Vec<PoaCompactTrustRootV1>) -> Result<Self> {
        let Some(first) = roots.first() else {
            return Err(integrity("PoA compact trust policy is empty"));
        };
        let deployment_id = first.deployment_id;
        let mut roots_by_epoch = BTreeMap::new();
        for root in roots {
            root.validate()?;
            if root.deployment_id != deployment_id {
                return Err(integrity(
                    "PoA compact trust policy mixes deployment identities",
                ));
            }
            let epoch = root.committee_epoch;
            if roots_by_epoch.insert(epoch, root).is_some() {
                return Err(integrity(
                    "PoA compact trust policy contains two roots for one committee epoch",
                ));
            }
        }
        Ok(Self {
            deployment_id,
            roots_by_epoch,
        })
    }

    pub const fn deployment_id(&self) -> [u8; 32] {
        self.deployment_id
    }

    pub fn root_at_epoch(&self, committee_epoch: u64) -> Option<&PoaCompactTrustRootV1> {
        self.roots_by_epoch.get(&committee_epoch)
    }

    /// The currently active root. Older roots remain solely so stored authority and exact retries
    /// can be replay-audited; they do not authorize a fresh destructive operation.
    pub fn latest_root(&self) -> &PoaCompactTrustRootV1 {
        self.roots_by_epoch
            .last_key_value()
            .map(|(_, root)| root)
            .expect("validated PoA compact trust policy is non-empty")
    }

    pub(crate) fn root_for_statement(
        &self,
        statement: &PoaCompactCheckpointStatementV1,
    ) -> Result<&PoaCompactTrustRootV1> {
        if statement.deployment_id != self.deployment_id {
            return Err(integrity(
                "PoA compact anchor deployment is not authorized by the external trust policy",
            ));
        }
        let root = self
            .roots_by_epoch
            .get(&statement.committee_epoch)
            .ok_or_else(|| {
                integrity(
                    "PoA compact anchor committee epoch is absent from the external trust policy",
                )
            })?;
        if statement.federation_id != root.federation_id {
            return Err(integrity(
                "PoA compact anchor self-carried federation/roster identity does not equal its external trust root",
            ));
        }
        Ok(root)
    }

    pub(crate) fn active_root_for_new_statement(
        &self,
        statement: &PoaCompactCheckpointStatementV1,
    ) -> Result<&PoaCompactTrustRootV1> {
        let root = self.root_for_statement(statement)?;
        if root.committee_epoch != self.latest_root().committee_epoch {
            return Err(integrity(
                "PoA compact fresh anchor uses a retired committee epoch; historical roots authorize replay audit and exact retry only",
            ));
        }
        Ok(root)
    }
}

impl StoredPoaCompactCheckpointAnchorV1 {
    pub(crate) fn new(
        signed: SignedPoaCompactCheckpointAnchorV1,
        trust_root: &PoaCompactTrustRootV1,
    ) -> Result<Self> {
        trust_root.validate()?;
        let threshold = u64::try_from(trust_root.threshold)
            .map_err(|_| integrity("PoA compact anchor threshold does not fit u64"))?;
        let stored = Self {
            signed,
            committee: trust_root.committee.clone(),
            ml_dsa_committee: trust_root
                .ml_dsa_committee
                .iter()
                .map(|key| key.0.to_vec())
                .collect(),
            threshold,
        };
        stored.verify_against(trust_root)?;
        Ok(stored)
    }

    fn decode_ml_dsa_committee(&self) -> Result<Vec<MlDsaPublicKey>> {
        self.ml_dsa_committee
            .iter()
            .map(|bytes| {
                bytes
                    .as_slice()
                    .try_into()
                    .map(MlDsaPublicKey)
                    .map_err(|_| integrity("PoA compact anchor ML-DSA key has wrong width"))
            })
            .collect()
    }

    fn verify(&self) -> Result<()> {
        self.signed.statement.validate_shape()?;
        if self.committee.is_empty()
            || self.committee.len() > MAX_ANCHOR_COMMITTEE_MEMBERS
            || self.committee.len() != self.ml_dsa_committee.len()
        {
            return Err(integrity(
                "PoA compact anchor committee is empty, oversized, or misaligned",
            ));
        }
        let threshold = usize::try_from(self.threshold)
            .map_err(|_| integrity("PoA compact anchor threshold does not fit usize"))?;
        if threshold == 0
            || threshold > self.committee.len()
            || threshold != dregg_federation::quorum_threshold(self.committee.len())
        {
            return Err(integrity("PoA compact anchor threshold is invalid"));
        }
        let ml_dsa_committee = self.decode_ml_dsa_committee()?;
        let derived_federation = dregg_federation::derive_federation_id_hybrid_with_epoch(
            &self.committee,
            &ml_dsa_committee,
            self.signed.statement.committee_epoch,
        );
        if derived_federation != self.signed.statement.federation_id {
            return Err(integrity(
                "PoA compact anchor federation id does not bind its enrolled hybrid roster",
            ));
        }
        if !dregg_federation::receipt::verify_hybrid_quorum_sigs(
            &self.signed.hybrid_quorum,
            &self.signed.statement.signing_message(),
            &self.committee,
            &ml_dsa_committee,
            threshold,
        ) {
            return Err(integrity(
                "PoA compact checkpoint anchor hybrid quorum is invalid",
            ));
        }
        Ok(())
    }

    fn verify_against(&self, trust_root: &PoaCompactTrustRootV1) -> Result<()> {
        trust_root.validate()?;
        if self.signed.statement.deployment_id != trust_root.deployment_id
            || self.signed.statement.federation_id != trust_root.federation_id
            || self.signed.statement.committee_epoch != trust_root.committee_epoch
            || self.committee != trust_root.committee
            || self.threshold
                != u64::try_from(trust_root.threshold)
                    .map_err(|_| integrity("PoA compact trust threshold does not fit u64"))?
            || self.ml_dsa_committee.len() != trust_root.ml_dsa_committee.len()
            || !self
                .ml_dsa_committee
                .iter()
                .zip(&trust_root.ml_dsa_committee)
                .all(|(stored, trusted)| stored.as_slice() == trusted.0.as_slice())
        {
            return Err(integrity(
                "PoA compact anchor self-carried roster does not equal its external trust root",
            ));
        }
        self.verify()
    }
}

impl CompactCommitAuthorityCertificateV1 {
    pub(crate) fn authority(&self) -> FinalizedCommitAuthorityV1 {
        FinalizedCommitAuthorityV1 {
            ordinal: self.ordinal,
            height: self.height,
            block_id: self.block_id,
            block_executed_up_to: self.block_executed_up_to,
            turn_hash: self.turn_hash,
            creator: self.creator,
            receipt_hash: self.receipt_hash,
            ledger_root: self.ledger_root,
            write_set_digest: self.write_set_digest,
        }
    }

    pub(crate) fn matches_record(&self, record: &CommitRecord) -> Result<bool> {
        Ok(self.ordinal == record.ordinal
            && self.height == record.height
            && self.block_id == record.block_id
            && self.block_executed_up_to == record.block_executed_up_to
            && self.turn_hash == record.turn_hash
            && self.creator == record.creator
            && self.receipt_hash == record.receipt_hash
            && self.ledger_root == record.ledger_root
            && self.write_set_digest == write_set_digest(record)?)
    }

    pub(crate) fn matches_signal(
        &self,
        ordinal: u64,
        turn_hash: [u8; 32],
        receipt_hash: [u8; 32],
    ) -> bool {
        self.ordinal == ordinal && self.turn_hash == turn_hash && self.receipt_hash == receipt_hash
    }

    pub(crate) fn matches_block_carrier(
        &self,
        ordinal: u64,
        block_id: [u8; 32],
        turn_hash: [u8; 32],
        receipt_hash: [u8; 32],
    ) -> bool {
        self.ordinal == ordinal
            && self.block_id == block_id
            && self.turn_hash == turn_hash
            && self.receipt_hash == receipt_hash
    }

    pub(crate) fn has_sidecar(&self, identity: &CompactPoaSidecarIdentityV1) -> bool {
        self.poa_sidecars.iter().any(|stored| stored == identity)
    }

    fn digest(&self) -> Result<[u8; 32]> {
        Ok(sha256_domain(
            CERTIFICATE_DIGEST_DOMAIN,
            &postcard::to_stdvec(self)
                .map_err(|error| StoreError::Serialization(error.to_string()))?,
        ))
    }

    fn validate(&self) -> Result<()> {
        if self.covering_checkpoint_height <= self.height {
            return Err(integrity(
                "PoA compact authority certificate is not below its covering checkpoint",
            ));
        }
        if self.covering_checkpoint_wire_digest == [0; 32]
            || self.covering_checkpoint_ledger_root == [0; 32]
        {
            return Err(integrity(
                "PoA compact authority certificate has a vacuous checkpoint identity",
            ));
        }
        if self.ordinal == 0 && self.predecessor_certificate_digest != [0; 32] {
            return Err(integrity(
                "first PoA compact authority certificate has a predecessor",
            ));
        }
        let mut previous_kind = 0;
        for sidecar in &self.poa_sidecars {
            sidecar.validate()?;
            if sidecar.kind <= previous_kind {
                return Err(integrity(
                    "PoA compact authority sidecar identities are not unique and ordered",
                ));
            }
            previous_kind = sidecar.kind;
        }
        Ok(())
    }
}

impl FinalizedCommitAuthorityV1 {
    pub(crate) fn from_record(record: &CommitRecord) -> Result<Self> {
        Ok(Self {
            ordinal: record.ordinal,
            height: record.height,
            block_id: record.block_id,
            block_executed_up_to: record.block_executed_up_to,
            turn_hash: record.turn_hash,
            creator: record.creator,
            receipt_hash: record.receipt_hash,
            ledger_root: record.ledger_root,
            write_set_digest: write_set_digest(record)?,
        })
    }

    pub const fn ordinal(&self) -> u64 {
        self.ordinal
    }

    pub const fn height(&self) -> u64 {
        self.height
    }

    pub const fn block_id(&self) -> [u8; 32] {
        self.block_id
    }

    pub const fn block_executed_up_to(&self) -> u64 {
        self.block_executed_up_to
    }

    pub const fn turn_hash(&self) -> [u8; 32] {
        self.turn_hash
    }

    pub const fn creator(&self) -> [u8; 32] {
        self.creator
    }

    pub const fn receipt_hash(&self) -> [u8; 32] {
        self.receipt_hash
    }

    pub const fn ledger_root(&self) -> [u8; 32] {
        self.ledger_root
    }

    pub const fn write_set_digest(&self) -> [u8; 32] {
        self.write_set_digest
    }
}

impl CompactPoaSidecarIdentityV1 {
    fn new(kind: u8, key: &[u8], wire: &[u8]) -> Result<Self> {
        let identity = Self {
            kind,
            key_digest: sha256_domain(SIDECAR_KEY_DOMAIN, key),
            wire_digest: sha256_domain(SIDECAR_WIRE_DOMAIN, wire),
        };
        identity.validate()?;
        Ok(identity)
    }

    fn validate(&self) -> Result<()> {
        if !(SIGNAL_KIND..=HOLDING_KIND).contains(&self.kind)
            || self.key_digest == [0; 32]
            || self.wire_digest == [0; 32]
        {
            return Err(integrity("PoA compact sidecar identity is malformed"));
        }
        Ok(())
    }
}

pub(crate) fn initialize_poa_compact_authority_tables_v1_in(
    write: &WriteTransaction,
) -> Result<()> {
    let _ = write.open_table(POA_COMPACT_AUTHORITY_CERTIFICATES_V1)?;
    let _ = write.open_table(POA_COMPACT_AUTHORITY_HEAD_V1)?;
    let _ = write.open_table(POA_COMPACT_CHECKPOINT_ANCHORS_V1)?;
    Ok(())
}

/// Capture the to-be-deleted generic records and all exact PoA sidecars in the same compaction
/// writer. `META_COMMIT_COMPACTED` advances only after this succeeds.
pub(crate) fn stage_compacted_commit_authority_prefix_in(
    write: &WriteTransaction,
    old_floor: u64,
    checkpoint: CheckpointIdentityV1,
    records: &[CommitRecord],
    anchor: StoredPoaCompactCheckpointAnchorV1,
) -> Result<()> {
    initialize_poa_compact_authority_tables_v1_in(write)?;
    anchor.verify()?;
    let audited = load_audited_certificates_in_write(write, old_floor)?;
    let mut predecessor_digest = audited
        .last_key_value()
        .map(|(_, certificate)| certificate.digest())
        .transpose()?
        .unwrap_or([0; 32]);
    let mut block_ids: BTreeSet<[u8; 32]> = audited
        .values()
        .map(|certificate| certificate.block_id)
        .collect();
    let mut encoded = Vec::with_capacity(records.len());
    for (offset, record) in records.iter().enumerate() {
        let offset = u64::try_from(offset)
            .map_err(|_| integrity("PoA compact authority offset does not fit u64"))?;
        let expected = old_floor
            .checked_add(offset)
            .ok_or_else(|| integrity("PoA compact authority ordinal overflow"))?;
        if record.ordinal != expected {
            return Err(integrity(
                "PoA compact authority input is not the exact dense doomed prefix",
            ));
        }
        if !block_ids.insert(record.block_id) {
            return Err(integrity(
                "PoA compact authority cannot represent duplicate applied block ids",
            ));
        }
        let certificate = CompactCommitAuthorityCertificateV1 {
            predecessor_certificate_digest: predecessor_digest,
            ordinal: record.ordinal,
            height: record.height,
            block_id: record.block_id,
            block_executed_up_to: record.block_executed_up_to,
            turn_hash: record.turn_hash,
            creator: record.creator,
            receipt_hash: record.receipt_hash,
            ledger_root: record.ledger_root,
            write_set_digest: write_set_digest(record)?,
            covering_checkpoint_height: checkpoint.height,
            covering_checkpoint_wire_digest: checkpoint.wire_digest,
            covering_checkpoint_ledger_root: checkpoint.ledger_root,
            poa_sidecars: capture_sidecars_in_write(write, record.ordinal)?,
        };
        certificate.validate()?;
        let frame = encode_frame(CERT_MAGIC, &certificate)?;
        predecessor_digest = certificate.digest()?;
        encoded.push((record.ordinal, frame));
    }
    {
        let mut certificates = write.open_table(POA_COMPACT_AUTHORITY_CERTIFICATES_V1)?;
        for (ordinal, frame) in &encoded {
            if certificates.get(*ordinal)?.is_some() {
                return Err(integrity(
                    "PoA compact authority certificate ordinal is already occupied",
                ));
            }
            certificates.insert(*ordinal, frame.as_slice())?;
        }
        let next_ordinal =
            old_floor
                .checked_add(u64::try_from(records.len()).map_err(|_| {
                    integrity("PoA compact authority record count does not fit u64")
                })?)
                .ok_or_else(|| integrity("PoA compact authority head overflow"))?;
        let head = CompactAuthorityHeadV1 {
            next_ordinal,
            certificate_digest: predecessor_digest,
        };
        let expected_statement = PoaCompactCheckpointStatementV1 {
            federation_id: anchor.signed.statement.federation_id,
            deployment_id: anchor.signed.statement.deployment_id,
            committee_epoch: anchor.signed.statement.committee_epoch,
            old_floor,
            new_floor: next_ordinal,
            checkpoint_height: checkpoint.height,
            checkpoint_wire_digest: checkpoint.wire_digest,
            checkpoint_ledger_root: checkpoint.ledger_root,
            certificate_count: next_ordinal,
            certificate_head: predecessor_digest,
        };
        if anchor.signed.statement != expected_statement {
            return Err(integrity(
                "PoA compact checkpoint anchor does not name the exact transaction preview",
            ));
        }
        let head_frame = encode_frame(HEAD_MAGIC, &head)?;
        let mut heads = write.open_table(POA_COMPACT_AUTHORITY_HEAD_V1)?;
        heads.insert(HEAD_KEY, head_frame.as_slice())?;
        let anchor_frame = encode_frame(ANCHOR_MAGIC, &anchor)?;
        let mut anchors = write.open_table(POA_COMPACT_CHECKPOINT_ANCHORS_V1)?;
        if let Some((_, previous_frame)) = anchors.last()? {
            let previous: StoredPoaCompactCheckpointAnchorV1 =
                decode_frame(ANCHOR_MAGIC, previous_frame.value())?;
            if anchor.signed.statement.committee_epoch < previous.signed.statement.committee_epoch {
                return Err(integrity(
                    "PoA compact checkpoint anchor committee epoch regressed",
                ));
            }
        }
        if anchors.get(next_ordinal)?.is_some() {
            return Err(integrity(
                "PoA compact checkpoint anchor floor is already occupied",
            ));
        }
        anchors.insert(next_ordinal, anchor_frame.as_slice())?;
    }
    Ok(())
}

pub(crate) fn require_exact_compacted_record_in(
    write: &WriteTransaction,
    compacted_floor: u64,
    expected_ordinal: u64,
    supplied: &CommitRecord,
) -> Result<()> {
    let certificates = load_audited_certificates_in_write(write, compacted_floor)?;
    if supplied.ordinal != expected_ordinal {
        return Err(integrity(
            "compacted replay supplied a CommitRecord for a different ordinal",
        ));
    }
    let certificate = certificates
        .get(&expected_ordinal)
        .ok_or_else(|| integrity("compacted replay has no authority certificate"))?;
    if !certificate.matches_record(supplied)? {
        return Err(integrity(
            "compacted replay differs from its complete authority certificate",
        ));
    }
    let current_sidecars = capture_sidecars_in_write(write, expected_ordinal)?;
    if current_sidecars != certificate.poa_sidecars {
        return Err(integrity(
            "compacted replay PoA sidecars differ from its authority certificate",
        ));
    }
    Ok(())
}

pub(crate) fn load_audited_certificates_in_read(
    read: &ReadTransaction,
    compacted_floor: u64,
) -> Result<BTreeMap<u64, CompactCommitAuthorityCertificateV1>> {
    let certificates = read.open_table(POA_COMPACT_AUTHORITY_CERTIFICATES_V1)?;
    let heads = read.open_table(POA_COMPACT_AUTHORITY_HEAD_V1)?;
    audit_certificate_tables(&certificates, &heads, compacted_floor)
}

pub(crate) fn load_audited_certificates_in_write(
    write: &WriteTransaction,
    compacted_floor: u64,
) -> Result<BTreeMap<u64, CompactCommitAuthorityCertificateV1>> {
    let certificates = write.open_table(POA_COMPACT_AUTHORITY_CERTIFICATES_V1)?;
    let heads = write.open_table(POA_COMPACT_AUTHORITY_HEAD_V1)?;
    audit_certificate_tables(&certificates, &heads, compacted_floor)
}

pub(crate) fn required_checkpoint_heights_in_read(read: &ReadTransaction) -> Result<BTreeSet<u64>> {
    let compacted_floor = read
        .open_table(tables::METADATA)?
        .get(tables::META_COMMIT_COMPACTED)?
        .map(|value| value.value())
        .unwrap_or(0);
    Ok(load_audited_certificates_in_read(read, compacted_floor)?
        .into_values()
        .map(|certificate| certificate.covering_checkpoint_height)
        .collect())
}

fn checkpoint_identity_in_read(
    read: &ReadTransaction,
    height: u64,
) -> Result<CheckpointIdentityV1> {
    let table = read.open_table(tables::LEDGER_CHECKPOINTS)?;
    let bytes = table
        .get(height)?
        .ok_or_else(|| integrity("PoA compact anchor names an absent ledger checkpoint"))?;
    checkpoint_identity_from_wire(height, bytes.value())
}

pub(crate) fn checkpoint_identity_in_write(
    write: &WriteTransaction,
    height: u64,
) -> Result<CheckpointIdentityV1> {
    let table = write.open_table(tables::LEDGER_CHECKPOINTS)?;
    let bytes = table
        .get(height)?
        .ok_or_else(|| integrity("PoA compact anchor names an absent ledger checkpoint"))?;
    checkpoint_identity_from_wire(height, bytes.value())
}

fn checkpoint_identity_from_wire(height: u64, wire: &[u8]) -> Result<CheckpointIdentityV1> {
    let checkpoint: crate::LedgerCheckpoint = postcard::from_bytes(wire)?;
    if checkpoint.height != height {
        return Err(integrity(
            "ledger checkpoint key and encoded height disagree",
        ));
    }
    let canonical = postcard::to_stdvec(&checkpoint)
        .map_err(|error| StoreError::Serialization(error.to_string()))?;
    if canonical != wire {
        return Err(integrity("ledger checkpoint wire is not canonical"));
    }
    let ledger = crate::ledger_store::checkpoint_to_ledger_snapshot(&checkpoint);
    Ok(CheckpointIdentityV1 {
        height,
        wire_digest: sha256_domain(CHECKPOINT_WIRE_DOMAIN, wire),
        ledger_root: crate::canonical_ledger_root(&ledger),
    })
}

fn preview_statement_in_read(
    read: &ReadTransaction,
    height: u64,
    federation_id: [u8; 32],
    deployment_id: [u8; 32],
    committee_epoch: u64,
) -> Result<Option<PoaCompactCheckpointStatementV1>> {
    if height == 0 {
        return Ok(None);
    }
    let (old_floor, checkpoint_height) = {
        let metadata = read.open_table(tables::METADATA)?;
        (
            metadata
                .get(tables::META_COMMIT_COMPACTED)?
                .map(|value| value.value())
                .unwrap_or(0),
            metadata
                .get(tables::META_LATEST_LEDGER_CHECKPOINT_HEIGHT)?
                .map(|value| value.value())
                .unwrap_or(0),
        )
    };
    if checkpoint_height < height {
        return Ok(None);
    }
    let checkpoint = checkpoint_identity_in_read(read, checkpoint_height)?;
    let audited = load_audited_certificates_in_read(read, old_floor)?;
    let mut predecessor_digest = audited
        .last_key_value()
        .map(|(_, certificate)| certificate.digest())
        .transpose()?
        .unwrap_or([0; 32]);
    let mut block_ids: BTreeSet<[u8; 32]> = audited
        .values()
        .map(|certificate| certificate.block_id)
        .collect();
    let log = read.open_table(tables::COMMIT_LOG)?;
    let mut count = 0_u64;
    for entry in log.iter()? {
        let (_, wire) = entry.map_err(|error| StoreError::Database(error.to_string()))?;
        let record = crate::commit_log::decode_commit_record(wire.value())?;
        if record.height >= height {
            break;
        }
        let expected = old_floor
            .checked_add(count)
            .ok_or_else(|| integrity("PoA compact preview ordinal overflow"))?;
        if record.ordinal != expected {
            return Err(integrity(
                "PoA compact preview did not find the exact dense doomed prefix",
            ));
        }
        if !block_ids.insert(record.block_id) {
            return Err(integrity(
                "PoA compact preview found duplicate applied block ids",
            ));
        }
        let certificate = CompactCommitAuthorityCertificateV1 {
            predecessor_certificate_digest: predecessor_digest,
            ordinal: record.ordinal,
            height: record.height,
            block_id: record.block_id,
            block_executed_up_to: record.block_executed_up_to,
            turn_hash: record.turn_hash,
            creator: record.creator,
            receipt_hash: record.receipt_hash,
            ledger_root: record.ledger_root,
            write_set_digest: write_set_digest(&record)?,
            covering_checkpoint_height: checkpoint.height,
            covering_checkpoint_wire_digest: checkpoint.wire_digest,
            covering_checkpoint_ledger_root: checkpoint.ledger_root,
            poa_sidecars: capture_sidecars_in_read(read, record.ordinal)?,
        };
        certificate.validate()?;
        predecessor_digest = certificate.digest()?;
        count = count
            .checked_add(1)
            .ok_or_else(|| integrity("PoA compact preview count overflow"))?;
    }
    if count == 0 {
        return Ok(None);
    }
    let new_floor = old_floor
        .checked_add(count)
        .ok_or_else(|| integrity("PoA compact preview floor overflow"))?;
    let statement = PoaCompactCheckpointStatementV1 {
        federation_id,
        deployment_id,
        committee_epoch,
        old_floor,
        new_floor,
        checkpoint_height: checkpoint.height,
        checkpoint_wire_digest: checkpoint.wire_digest,
        checkpoint_ledger_root: checkpoint.ledger_root,
        certificate_count: new_floor,
        certificate_head: predecessor_digest,
    };
    statement.validate_shape()?;
    Ok(Some(statement))
}

#[cfg(any(test, feature = "test-support"))]
fn test_poa_compact_trust_material_v1() -> Result<(
    PoaCompactTrustPolicyV1,
    dregg_types::SigningKey,
    dregg_federation::frost::MlDsaSigningKey,
)> {
    #[cfg(test)]
    dregg_pq_testkit::install_or_panic();
    let seed = [0xC7; 32];
    let signing_key = dregg_types::SigningKey::from_bytes(&seed);
    let public_key = signing_key.public_key();
    let (ml_dsa_public, ml_dsa_signing) =
        dregg_federation::frost::MlDsaSigningKey::from_seed(&seed);
    let committee_epoch = 0;
    let federation_id = dregg_federation::derive_federation_id_hybrid_with_epoch(
        std::slice::from_ref(&public_key),
        std::slice::from_ref(&ml_dsa_public),
        committee_epoch,
    );
    let root = PoaCompactTrustRootV1::new(
        [0xD7; 32],
        federation_id,
        committee_epoch,
        vec![public_key],
        vec![ml_dsa_public],
        1,
    )?;
    Ok((
        PoaCompactTrustPolicyV1::new(vec![root])?,
        signing_key,
        ml_dsa_signing,
    ))
}

impl PersistentStore {
    pub(crate) fn enforce_poa_compact_authority_schema_v1(&self) -> Result<()> {
        let read = self.db.begin_read()?;
        let (installed, compacted_floor) = {
            let metadata = read.open_table(tables::METADATA)?;
            (
                metadata
                    .get(META_POA_COMPACT_AUTHORITY_SCHEMA_V1)?
                    .map(|value| value.value()),
                metadata
                    .get(tables::META_COMMIT_COMPACTED)?
                    .map(|value| value.value())
                    .unwrap_or(0),
            )
        };
        drop(read);
        match installed {
            Some(POA_COMPACT_AUTHORITY_SCHEMA_V1) => return Ok(()),
            Some(version) => {
                return Err(integrity(format!(
                    "PoA compact authority schema {version} is incompatible with required v1; re-genesis is required"
                )));
            }
            None if compacted_floor != 0 => {
                return Err(integrity(
                    "positive commit compaction floor predates signed PoA compact authority v1; re-genesis is required",
                ));
            }
            None => {}
        }
        let write = self.db.begin_write()?;
        {
            let mut metadata = write.open_table(tables::METADATA)?;
            metadata.insert(
                META_POA_COMPACT_AUTHORITY_SCHEMA_V1,
                POA_COMPACT_AUTHORITY_SCHEMA_V1,
            )?;
        }
        write.commit()?;
        Ok(())
    }

    /// Prepare the exact statement an independently trusted committee must sign before compaction.
    pub fn prepare_poa_compact_checkpoint_statement_v1(
        &self,
        height: u64,
        trust_root: &PoaCompactTrustRootV1,
    ) -> Result<Option<PoaCompactCheckpointStatementV1>> {
        trust_root.validate()?;
        let read = self.db.begin_read()?;
        preview_statement_in_read(
            &read,
            height,
            trust_root.federation_id,
            trust_root.deployment_id,
            trust_root.committee_epoch,
        )
    }

    /// Return whether `anchor` is the exact already-committed anchor at its signed floor.
    ///
    /// This is the response-loss/restart tooth for an operator ceremony.  A caller which lost the
    /// success response may submit the same quorum again and learn that the exact bytes already
    /// landed.  A merely valid signature over a different statement at an old floor does not count
    /// as a retry.  The complete compact authority is audited against the independently supplied
    /// policy before the comparison, so a locally resealed or policy-substituted database cannot
    /// manufacture an affirmative answer.
    pub fn has_exact_poa_compact_checkpoint_anchor_v1(
        &self,
        anchor: &SignedPoaCompactCheckpointAnchorV1,
        trust_policy: &PoaCompactTrustPolicyV1,
    ) -> Result<bool> {
        let trust_root = trust_policy.root_for_statement(anchor.statement())?;
        let expected = StoredPoaCompactCheckpointAnchorV1::new(anchor.clone(), trust_root)?;
        self.audit_poa_compact_authority_v1(Some(trust_policy))?;
        let read = self.db.begin_read()?;
        let anchors = read.open_table(POA_COMPACT_CHECKPOINT_ANCHORS_V1)?;
        let Some(frame) = anchors.get(anchor.statement().new_floor())? else {
            return Ok(false);
        };
        let stored: StoredPoaCompactCheckpointAnchorV1 = decode_frame(ANCHOR_MAGIC, frame.value())?;
        stored.verify_against(trust_root)?;
        Ok(stored == expected)
    }

    /// Fixture-only real hybrid ceremony used by compaction/reopen regression tests.
    #[cfg(any(test, feature = "test-support"))]
    pub fn compact_below_with_test_poa_anchor_v1(&self, height: u64) -> Result<u64> {
        #[cfg(test)]
        dregg_pq_testkit::install_or_panic();
        let (policy, signing_key, ml_dsa_signing) = test_poa_compact_trust_material_v1()?;
        let trust_root = policy
            .root_at_epoch(0)
            .ok_or_else(|| integrity("test PoA compact trust root is absent"))?;
        let Some(statement) =
            self.prepare_poa_compact_checkpoint_statement_v1(height, trust_root)?
        else {
            return Ok(0);
        };
        let message = statement.signing_message();
        let quorum = vec![HybridQuorumSig {
            pubkey: signing_key.public_key(),
            signature: dregg_types::sign(&signing_key, &message),
            ml_dsa_pubkey: trust_root.ml_dsa_committee[0].0.to_vec(),
            pq_signature: ml_dsa_signing
                .sign(&message)
                .ok_or_else(|| integrity("test PoA compact anchor ML-DSA signing failed"))?,
        }];
        self.compact_below_with_poa_anchor_v1(
            height,
            SignedPoaCompactCheckpointAnchorV1::new(statement, quorum),
            &policy,
        )
    }

    /// Fixture-only external policy for compaction/reopen regression tests.
    #[cfg(any(test, feature = "test-support"))]
    pub fn test_poa_compact_trust_policy_v1() -> Result<PoaCompactTrustPolicyV1> {
        test_poa_compact_trust_material_v1().map(|(policy, _, _)| policy)
    }

    /// Reopen a fixture store with the independently supplied test policy.
    #[cfg(any(test, feature = "test-support"))]
    pub fn open_with_test_poa_compact_trust_v1(path: &std::path::Path) -> Result<Self> {
        let policy = Self::test_poa_compact_trust_policy_v1()?;
        Self::open_with_poa_compact_trust_v1(path, &policy)
    }

    pub(crate) fn audit_poa_compact_authority_v1(
        &self,
        trust_policy: Option<&PoaCompactTrustPolicyV1>,
    ) -> Result<()> {
        let read = self.db.begin_read()?;
        let compacted_floor = read
            .open_table(tables::METADATA)?
            .get(tables::META_COMMIT_COMPACTED)?
            .map(|value| value.value())
            .unwrap_or(0);
        let certificates = load_audited_certificates_in_read(&read, compacted_floor)?;
        let mut certificate_block_ids = BTreeSet::new();
        for (ordinal, certificate) in &certificates {
            if capture_sidecars_in_read(&read, *ordinal)? != certificate.poa_sidecars {
                return Err(integrity(
                    "compacted PoA sidecars disagree with the authority certificate",
                ));
            }
            let checkpoint =
                checkpoint_identity_in_read(&read, certificate.covering_checkpoint_height)?;
            if checkpoint.wire_digest != certificate.covering_checkpoint_wire_digest
                || checkpoint.ledger_root != certificate.covering_checkpoint_ledger_root
            {
                return Err(integrity(
                    "compacted authority certificate disagrees with its exact checkpoint bytes/root",
                ));
            }
            if !certificate_block_ids.insert(certificate.block_id) {
                return Err(integrity(
                    "compacted authority certificates contain a duplicate block id",
                ));
            }
        }

        let compacted_ids = read.open_table(tables::COMMIT_COMPACTED_BLOCK_IDS)?;
        if compacted_ids.len()? != compacted_floor {
            return Err(integrity(
                "compacted block-id set cardinality disagrees with compact authority",
            ));
        }
        let mut stored_block_ids = BTreeSet::new();
        for row in compacted_ids.iter()? {
            let (block_id, _) = row.map_err(|error| StoreError::Database(error.to_string()))?;
            stored_block_ids.insert(*block_id.value());
        }
        if stored_block_ids != certificate_block_ids {
            return Err(integrity(
                "compacted block-id set is not exactly the authority-certificate projection",
            ));
        }

        let anchors = read.open_table(POA_COMPACT_CHECKPOINT_ANCHORS_V1)?;
        if compacted_floor == 0 {
            if !anchors.is_empty()? {
                return Err(integrity(
                    "empty compact authority unexpectedly has checkpoint anchors",
                ));
            }
            return Ok(());
        }
        let trust_policy = trust_policy.ok_or_else(|| {
            integrity(
                "compacted PoA authority has no caller-supplied external deployment trust policy",
            )
        })?;
        let mut expected_old_floor = 0_u64;
        let mut previous_committee_epoch = None;
        for row in anchors.iter()? {
            let (new_floor, frame) =
                row.map_err(|error| StoreError::Database(error.to_string()))?;
            let new_floor = new_floor.value();
            let anchor: StoredPoaCompactCheckpointAnchorV1 =
                decode_frame(ANCHOR_MAGIC, frame.value())?;
            let statement = &anchor.signed.statement;
            let trust_root = trust_policy.root_for_statement(statement)?;
            anchor.verify_against(trust_root)?;
            if new_floor != statement.new_floor
                || statement.old_floor != expected_old_floor
                || statement.new_floor > compacted_floor
                || statement.certificate_count != statement.new_floor
            {
                return Err(integrity(
                    "PoA compact checkpoint anchors do not partition the dense compact prefix",
                ));
            }
            if previous_committee_epoch.is_some_and(|previous| statement.committee_epoch < previous)
            {
                return Err(integrity(
                    "PoA compact checkpoint anchor committee epoch regressed",
                ));
            }
            previous_committee_epoch = Some(statement.committee_epoch);
            let tail = certificates
                .get(&(statement.new_floor - 1))
                .ok_or_else(|| integrity("PoA compact anchor tail certificate is absent"))?;
            if tail.digest()? != statement.certificate_head {
                return Err(integrity(
                    "PoA compact anchor signature does not bind the certificate-chain tail",
                ));
            }
            let checkpoint = checkpoint_identity_in_read(&read, statement.checkpoint_height)?;
            if checkpoint.wire_digest != statement.checkpoint_wire_digest
                || checkpoint.ledger_root != statement.checkpoint_ledger_root
            {
                return Err(integrity(
                    "PoA compact anchor disagrees with its exact checkpoint bytes/root",
                ));
            }
            for ordinal in statement.old_floor..statement.new_floor {
                let certificate = certificates
                    .get(&ordinal)
                    .ok_or_else(|| integrity("PoA compact anchor range has a certificate gap"))?;
                if certificate.covering_checkpoint_height != statement.checkpoint_height
                    || certificate.covering_checkpoint_wire_digest
                        != statement.checkpoint_wire_digest
                    || certificate.covering_checkpoint_ledger_root
                        != statement.checkpoint_ledger_root
                {
                    return Err(integrity(
                        "PoA compact anchor range does not share its signed checkpoint identity",
                    ));
                }
            }
            expected_old_floor = statement.new_floor;
        }
        if expected_old_floor != compacted_floor {
            return Err(integrity(
                "PoA compact authority prefix is not completely covered by signed anchors",
            ));
        }
        Ok(())
    }
}

fn audit_certificate_tables(
    certificates: &impl ReadableTable<u64, &'static [u8]>,
    heads: &impl ReadableTable<&'static str, &'static [u8]>,
    compacted_floor: u64,
) -> Result<BTreeMap<u64, CompactCommitAuthorityCertificateV1>> {
    if certificates.len()? != compacted_floor {
        return Err(integrity(
            "PoA compact authority certificate count disagrees with compaction floor",
        ));
    }
    if heads.len()? > 1 {
        return Err(integrity("PoA compact authority has multiple heads"));
    }
    if compacted_floor == 0 {
        if heads.get(HEAD_KEY)?.is_some() {
            return Err(integrity(
                "empty PoA compact authority unexpectedly has a head",
            ));
        }
        return Ok(BTreeMap::new());
    }

    let mut decoded = BTreeMap::new();
    let mut expected_ordinal = 0_u64;
    let mut predecessor_digest = [0; 32];
    for entry in certificates.iter()? {
        let (ordinal, frame) = entry?;
        if ordinal.value() != expected_ordinal {
            return Err(integrity(
                "PoA compact authority certificate ordinals are not dense",
            ));
        }
        let certificate: CompactCommitAuthorityCertificateV1 =
            decode_frame(CERT_MAGIC, frame.value())?;
        certificate.validate()?;
        if certificate.ordinal != expected_ordinal
            || certificate.predecessor_certificate_digest != predecessor_digest
        {
            return Err(integrity(
                "PoA compact authority certificate chain is disconnected",
            ));
        }
        predecessor_digest = certificate.digest()?;
        decoded.insert(expected_ordinal, certificate);
        expected_ordinal = expected_ordinal
            .checked_add(1)
            .ok_or_else(|| integrity("PoA compact authority audit ordinal overflow"))?;
    }
    if expected_ordinal != compacted_floor {
        return Err(integrity(
            "PoA compact authority chain length disagrees with floor",
        ));
    }
    let head_frame = heads
        .get(HEAD_KEY)?
        .ok_or_else(|| integrity("PoA compact authority head is absent"))?;
    let head: CompactAuthorityHeadV1 = decode_frame(HEAD_MAGIC, head_frame.value())?;
    if head.next_ordinal != compacted_floor || head.certificate_digest != predecessor_digest {
        return Err(integrity(
            "PoA compact authority head disagrees with certificate-chain tail",
        ));
    }
    Ok(decoded)
}

fn capture_sidecars_in_write(
    write: &WriteTransaction,
    ordinal: u64,
) -> Result<Vec<CompactPoaSidecarIdentityV1>> {
    capture_sidecars_from_tables(
        ordinal,
        &write.open_table(tables::POA_SIGNAL_BY_COMMIT_ORDINAL_V1)?,
        &write.open_table(tables::POA_SIGNAL_TRANSITIONS_V1)?,
        &write.open_table(crate::poa_event_store::POA_EVENT_BY_COMMIT_ORDINAL_V1)?,
        &write.open_table(crate::poa_event_store::POA_EVENTS_V1)?,
        &write.open_table(crate::poa_event_batch_v2::POA_EVENT_BATCH_MANIFESTS_V2)?,
        &write.open_table(
            crate::poa_holding_consumption::POA_HOLDING_CONSUMPTION_BY_COMMIT_ORDINAL_V1,
        )?,
        &write.open_table(crate::poa_holding_consumption::POA_HOLDING_CONSUMPTIONS_V1)?,
    )
}

fn capture_sidecars_in_read(
    read: &ReadTransaction,
    ordinal: u64,
) -> Result<Vec<CompactPoaSidecarIdentityV1>> {
    capture_sidecars_from_tables(
        ordinal,
        &read.open_table(tables::POA_SIGNAL_BY_COMMIT_ORDINAL_V1)?,
        &read.open_table(tables::POA_SIGNAL_TRANSITIONS_V1)?,
        &read.open_table(crate::poa_event_store::POA_EVENT_BY_COMMIT_ORDINAL_V1)?,
        &read.open_table(crate::poa_event_store::POA_EVENTS_V1)?,
        &read.open_table(crate::poa_event_batch_v2::POA_EVENT_BATCH_MANIFESTS_V2)?,
        &read.open_table(
            crate::poa_holding_consumption::POA_HOLDING_CONSUMPTION_BY_COMMIT_ORDINAL_V1,
        )?,
        &read.open_table(crate::poa_holding_consumption::POA_HOLDING_CONSUMPTIONS_V1)?,
    )
}

#[allow(clippy::too_many_arguments)]
fn capture_sidecars_from_tables(
    ordinal: u64,
    signal_by_ordinal: &impl ReadableTable<u64, &'static [u8; 40]>,
    signals: &impl ReadableTable<&'static [u8; 40], &'static [u8]>,
    event_by_ordinal: &impl ReadableTable<u64, &'static [u8; 40]>,
    events: &impl ReadableTable<&'static [u8; 40], &'static [u8]>,
    batches: &impl ReadableTable<u64, &'static [u8]>,
    holding_by_ordinal: &impl ReadableTable<u64, &'static [u8; 32]>,
    holdings: &impl ReadableTable<&'static [u8; 32], &'static [u8]>,
) -> Result<Vec<CompactPoaSidecarIdentityV1>> {
    let mut identities = Vec::with_capacity(4);
    if let Some(key) = signal_by_ordinal.get(ordinal)? {
        let key = *key.value();
        let wire = signals
            .get(&key)?
            .ok_or_else(|| integrity("PoA Signal compact capture found an orphan reverse index"))?;
        identities.push(CompactPoaSidecarIdentityV1::new(
            SIGNAL_KIND,
            &key,
            wire.value(),
        )?);
    }
    if let Some(key) = event_by_ordinal.get(ordinal)? {
        let key = *key.value();
        let wire = events
            .get(&key)?
            .ok_or_else(|| integrity("PoA event compact capture found an orphan reverse index"))?;
        identities.push(CompactPoaSidecarIdentityV1::new(
            EVENT_V1_KIND,
            &key,
            wire.value(),
        )?);
    }
    if let Some(wire) = batches.get(ordinal)? {
        identities.push(CompactPoaSidecarIdentityV1::new(
            EVENT_BATCH_V2_KIND,
            &ordinal.to_le_bytes(),
            wire.value(),
        )?);
    }
    if let Some(key) = holding_by_ordinal.get(ordinal)? {
        let key = *key.value();
        let wire = holdings.get(&key)?.ok_or_else(|| {
            integrity("PoA holding compact capture found an orphan reverse index")
        })?;
        identities.push(CompactPoaSidecarIdentityV1::new(
            HOLDING_KIND,
            &key,
            wire.value(),
        )?);
    }
    Ok(identities)
}

pub(crate) fn signal_identity(key: &[u8; 40], wire: &[u8]) -> Result<CompactPoaSidecarIdentityV1> {
    CompactPoaSidecarIdentityV1::new(SIGNAL_KIND, key, wire)
}

pub(crate) fn event_v1_identity(
    key: &[u8; 40],
    wire: &[u8],
) -> Result<CompactPoaSidecarIdentityV1> {
    CompactPoaSidecarIdentityV1::new(EVENT_V1_KIND, key, wire)
}

pub(crate) fn event_batch_v2_identity(
    ordinal: u64,
    wire: &[u8],
) -> Result<CompactPoaSidecarIdentityV1> {
    CompactPoaSidecarIdentityV1::new(EVENT_BATCH_V2_KIND, &ordinal.to_le_bytes(), wire)
}

pub(crate) fn holding_identity(key: &[u8; 32], wire: &[u8]) -> Result<CompactPoaSidecarIdentityV1> {
    CompactPoaSidecarIdentityV1::new(HOLDING_KIND, key, wire)
}

fn write_set_digest(record: &CommitRecord) -> Result<[u8; 32]> {
    let bytes = postcard::to_stdvec(&(&record.touched_cells, &record.removed))
        .map_err(|error| StoreError::Serialization(error.to_string()))?;
    Ok(sha256_domain(WRITE_SET_DOMAIN, &bytes))
}

fn encode_frame<T: Serialize>(magic: [u8; 4], value: &T) -> Result<Vec<u8>> {
    let payload =
        postcard::to_stdvec(value).map_err(|error| StoreError::Serialization(error.to_string()))?;
    if payload.is_empty() || payload.len() > MAX_FRAME_BYTES {
        return Err(integrity("PoA compact authority frame exceeds bound"));
    }
    let payload_len = u32::try_from(payload.len())
        .map_err(|_| integrity("PoA compact authority frame length exceeds u32"))?;
    let mut frame = Vec::with_capacity(FRAME_HEADER_LEN + payload.len() + FRAME_SEAL_LEN);
    frame.extend_from_slice(&magic);
    frame.push(FRAME_VERSION);
    frame.extend_from_slice(&[0; 3]);
    frame.extend_from_slice(&payload_len.to_le_bytes());
    frame.extend_from_slice(&payload);
    frame.extend_from_slice(&sha256_domain(FRAME_SEAL_DOMAIN, &frame));
    Ok(frame)
}

fn decode_frame<T: for<'de> Deserialize<'de> + Serialize>(
    magic: [u8; 4],
    frame: &[u8],
) -> Result<T> {
    if frame.len() < FRAME_HEADER_LEN + FRAME_SEAL_LEN
        || frame[..4] != magic
        || frame[4] != FRAME_VERSION
        || frame[5..8] != [0; 3]
    {
        return Err(integrity("PoA compact authority frame header is invalid"));
    }
    let payload_len = u32::from_le_bytes(
        frame[8..12]
            .try_into()
            .map_err(|_| integrity("PoA compact authority frame length is malformed"))?,
    ) as usize;
    let expected = FRAME_HEADER_LEN
        .checked_add(payload_len)
        .and_then(|length| length.checked_add(FRAME_SEAL_LEN))
        .ok_or_else(|| integrity("PoA compact authority frame length overflow"))?;
    if payload_len == 0 || payload_len > MAX_FRAME_BYTES || expected != frame.len() {
        return Err(integrity("PoA compact authority frame length mismatch"));
    }
    let payload_end = frame.len() - FRAME_SEAL_LEN;
    if sha256_domain(FRAME_SEAL_DOMAIN, &frame[..payload_end]).as_slice() != &frame[payload_end..] {
        return Err(integrity("PoA compact authority frame seal mismatch"));
    }
    let payload = &frame[FRAME_HEADER_LEN..payload_end];
    let decoded: T = postcard::from_bytes(payload)
        .map_err(|error| StoreError::Serialization(error.to_string()))?;
    if postcard::to_stdvec(&decoded)
        .map_err(|error| StoreError::Serialization(error.to_string()))?
        != payload
    {
        return Err(integrity("PoA compact authority frame is not canonical"));
    }
    Ok(decoded)
}

fn sha256_domain(domain: &[u8], bytes: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(domain);
    hasher.update(bytes);
    hasher.finalize().into()
}

fn integrity(message: impl Into<String>) -> StoreError {
    StoreError::Integrity(message.into())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::LedgerCheckpoint;
    use dregg_cell::Ledger;

    fn trust_material(
        seed: u8,
        deployment_id: [u8; 32],
        committee_epoch: u64,
    ) -> (
        PoaCompactTrustRootV1,
        dregg_types::SigningKey,
        dregg_federation::frost::MlDsaSigningKey,
    ) {
        dregg_pq_testkit::install_or_panic();
        let seed = [seed; 32];
        let signing_key = dregg_types::SigningKey::from_bytes(&seed);
        let public_key = signing_key.public_key();
        let (ml_dsa_public, ml_dsa_signing) =
            dregg_federation::frost::MlDsaSigningKey::from_seed(&seed);
        let federation_id = dregg_federation::derive_federation_id_hybrid_with_epoch(
            std::slice::from_ref(&public_key),
            std::slice::from_ref(&ml_dsa_public),
            committee_epoch,
        );
        (
            PoaCompactTrustRootV1::new(
                deployment_id,
                federation_id,
                committee_epoch,
                vec![public_key],
                vec![ml_dsa_public],
                1,
            )
            .unwrap(),
            signing_key,
            ml_dsa_signing,
        )
    }

    fn sign_statement(
        statement: PoaCompactCheckpointStatementV1,
        signing_key: &dregg_types::SigningKey,
        ml_dsa_signing: &dregg_federation::frost::MlDsaSigningKey,
        trust_root: &PoaCompactTrustRootV1,
    ) -> SignedPoaCompactCheckpointAnchorV1 {
        let message = statement.signing_message();
        SignedPoaCompactCheckpointAnchorV1::new(
            statement,
            vec![HybridQuorumSig {
                pubkey: signing_key.public_key(),
                signature: dregg_types::sign(signing_key, &message),
                ml_dsa_pubkey: trust_root.ml_dsa_committee[0].0.to_vec(),
                pq_signature: ml_dsa_signing.sign(&message).unwrap(),
            }],
        )
    }

    fn compact_with_material(
        store: &PersistentStore,
        height: u64,
        policy: &PoaCompactTrustPolicyV1,
        trust_root: &PoaCompactTrustRootV1,
        signing_key: &dregg_types::SigningKey,
        ml_dsa_signing: &dregg_federation::frost::MlDsaSigningKey,
    ) -> Result<u64> {
        let Some(statement) =
            store.prepare_poa_compact_checkpoint_statement_v1(height, trust_root)?
        else {
            return Ok(0);
        };
        store.compact_below_with_poa_anchor_v1(
            height,
            sign_statement(statement, signing_key, ml_dsa_signing, trust_root),
            policy,
        )
    }

    fn record(ordinal: u64, ledger_root: [u8; 32]) -> CommitRecord {
        let tag = u8::try_from(ordinal + 1).unwrap();
        CommitRecord {
            ordinal,
            height: ordinal + 1,
            block_id: [tag; 32],
            block_executed_up_to: ordinal + 1,
            turn_hash: [tag.wrapping_add(0x20); 32],
            creator: [tag.wrapping_add(0x40); 32],
            receipt_hash: [tag.wrapping_add(0x60); 32],
            ledger_root,
            touched_cells: Vec::new(),
            removed: Vec::new(),
        }
    }

    fn compact_three(path: &std::path::Path) -> PersistentStore {
        let store = PersistentStore::open(path).unwrap();
        let empty_root = crate::canonical_ledger_root(&Ledger::new());
        for ordinal in 0..4 {
            store
                .commit_finalized_turn(ordinal, &record(ordinal, empty_root))
                .unwrap();
        }
        store
            .store_ledger_checkpoint_snapshot(&LedgerCheckpoint {
                height: 4,
                cells: Vec::new(),
                sovereign_commitments: Vec::new(),
                sovereign_registrations: Vec::new(),
            })
            .unwrap();
        assert_eq!(store.compact_below_with_test_poa_anchor_v1(4).unwrap(), 3);
        let policy = PersistentStore::test_poa_compact_trust_policy_v1().unwrap();
        store.audit_poa_compact_authority_v1(Some(&policy)).unwrap();
        store
    }

    #[test]
    fn unsigned_checkpoint_cannot_delete_a_finalized_prefix() {
        let store = PersistentStore::open_in_memory().unwrap();
        let empty_root = crate::canonical_ledger_root(&Ledger::new());
        for ordinal in 0..2 {
            store
                .commit_finalized_turn(ordinal, &record(ordinal, empty_root))
                .unwrap();
        }
        store
            .store_ledger_checkpoint_snapshot(&LedgerCheckpoint {
                height: 2,
                cells: Vec::new(),
                sovereign_commitments: Vec::new(),
                sovereign_registrations: Vec::new(),
            })
            .unwrap();
        assert_eq!(store.compact_below(2).unwrap(), 0);
        assert_eq!(store.commit_compacted_floor().unwrap(), 0);
        assert!(store.commit_record_at(0).unwrap().is_some());
        let policy = PersistentStore::test_poa_compact_trust_policy_v1().unwrap();
        assert!(
            store
                .prepare_poa_compact_checkpoint_statement_v1(2, policy.root_at_epoch(0).unwrap(),)
                .unwrap()
                .is_some()
        );
    }

    #[test]
    fn compacted_store_fails_closed_without_external_trust_policy() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("missing-external-trust.redb");
        drop(compact_three(&path));

        let error = match PersistentStore::open(&path) {
            Ok(_) => panic!("plain open accepted self-carried compact-anchor trust"),
            Err(error) => error.to_string(),
        };
        assert!(error.contains("no caller-supplied external"), "{error}");
        PersistentStore::open_with_test_poa_compact_trust_v1(&path)
            .expect("the deployment-authenticated external policy reopens the store");
    }

    #[test]
    fn pcc_referenced_checkpoint_rejects_differing_same_height_write_before_mutation() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("referenced-checkpoint-write.redb");
        let store = compact_three(&path);
        let original = LedgerCheckpoint {
            height: 4,
            cells: Vec::new(),
            sovereign_commitments: Vec::new(),
            sovereign_registrations: Vec::new(),
        };
        store
            .store_ledger_checkpoint_snapshot(&original)
            .expect("identical referenced checkpoint retry is idempotent");
        let mut substituted = original;
        substituted
            .sovereign_commitments
            .push(([0xA1; 32], [0xA2; 32]));
        let error = store
            .store_ledger_checkpoint_snapshot(&substituted)
            .unwrap_err()
            .to_string();
        assert!(
            error.contains("already bound to different exact bytes"),
            "{error}"
        );
        let policy = PersistentStore::test_poa_compact_trust_policy_v1().unwrap();
        store
            .audit_poa_compact_authority_v1(Some(&policy))
            .expect("refused overwrite left signed checkpoint authority intact");
        drop(store);
        PersistentStore::open_with_poa_compact_trust_v1(&path, &policy)
            .expect("refused overwrite cannot poison the next reopen");
    }

    #[test]
    fn positive_pre_certificate_floor_requires_explicit_regenesis() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("pre-pcc-floor.redb");
        {
            let store = PersistentStore::open(&path).unwrap();
            let write = store.db.begin_write().unwrap();
            {
                let mut metadata = write.open_table(tables::METADATA).unwrap();
                metadata
                    .remove(META_POA_COMPACT_AUTHORITY_SCHEMA_V1)
                    .unwrap();
                metadata.insert(tables::META_COMMIT_COMPACTED, 1).unwrap();
            }
            write.commit().unwrap();
        }
        let error = match PersistentStore::open(&path) {
            Ok(_) => panic!("open accepted an unversioned positive compaction floor"),
            Err(error) => error.to_string(),
        };
        assert!(
            error.contains("predates signed PoA compact authority v1"),
            "{error}"
        );
        assert!(error.contains("re-genesis"), "{error}");
    }

    #[test]
    fn resealed_intermediate_certificate_cannot_disconnect_hidden_history() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("resealed-intermediate.redb");
        let store = compact_three(&path);

        let write = store.db.begin_write().unwrap();
        {
            let mut certificates = write
                .open_table(POA_COMPACT_AUTHORITY_CERTIFICATES_V1)
                .unwrap();
            let frame = certificates.get(1).unwrap().unwrap().value().to_vec();
            let mut certificate: CompactCommitAuthorityCertificateV1 =
                decode_frame(CERT_MAGIC, &frame).unwrap();
            certificate.creator[0] ^= 1;
            let coherently_resealed = encode_frame(CERT_MAGIC, &certificate).unwrap();
            certificates
                .insert(1, coherently_resealed.as_slice())
                .unwrap();
        }
        write.commit().unwrap();

        let policy = PersistentStore::test_poa_compact_trust_policy_v1().unwrap();
        let error = store
            .audit_poa_compact_authority_v1(Some(&policy))
            .unwrap_err()
            .to_string();
        assert!(error.contains("chain is disconnected"), "{error}");
        drop(store);
        assert!(
            PersistentStore::open_with_test_poa_compact_trust_v1(&path).is_err(),
            "open-time audit must refuse a validly framed, resealed intermediate substitution"
        );
    }

    #[test]
    fn finalized_authority_view_is_exact_across_compaction_and_reopen() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("authority-view.redb");
        let empty_root = crate::canonical_ledger_root(&Ledger::new());
        let expected = record(1, empty_root);
        {
            let store = compact_three(&path);
            let authority = store.finalized_commit_authority_at(1).unwrap().unwrap();
            assert_eq!(
                authority,
                FinalizedCommitAuthorityV1::from_record(&expected).unwrap()
            );
        }
        let reopened = PersistentStore::open_with_test_poa_compact_trust_v1(&path).unwrap();
        let authority = reopened.finalized_commit_authority_at(1).unwrap().unwrap();
        assert_eq!(
            authority,
            FinalizedCommitAuthorityV1::from_record(&expected).unwrap()
        );
        assert!(
            reopened.commit_finalized_turn(0, &expected).is_err(),
            "a certificate for ordinal one cannot authorize a retry claiming ordinal zero"
        );
        let exact_zero = record(0, empty_root);
        assert_eq!(reopened.commit_finalized_turn(0, &exact_zero).unwrap(), 0);
    }

    #[test]
    fn signed_anchor_detects_exact_checkpoint_wire_substitution() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("checkpoint-wire-substitution.redb");
        let store = compact_three(&path);
        let write = store.db.begin_write().unwrap();
        {
            let mut checkpoints = write.open_table(tables::LEDGER_CHECKPOINTS).unwrap();
            let wire = checkpoints.get(4).unwrap().unwrap().value().to_vec();
            let mut checkpoint: LedgerCheckpoint = postcard::from_bytes(&wire).unwrap();
            checkpoint
                .sovereign_commitments
                .push(([0xA1; 32], [0xA2; 32]));
            let substituted = postcard::to_stdvec(&checkpoint).unwrap();
            checkpoints.insert(4, substituted.as_slice()).unwrap();
        }
        write.commit().unwrap();
        drop(store);
        let error = match PersistentStore::open_with_test_poa_compact_trust_v1(&path) {
            Ok(_) => panic!("open accepted substituted checkpoint wire"),
            Err(error) => error.to_string(),
        };
        assert!(error.contains("checkpoint bytes/root"), "{error}");
    }

    #[test]
    fn locally_resealed_anchor_with_forged_quorum_is_refused() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("forged-anchor.redb");
        let store = compact_three(&path);
        let write = store.db.begin_write().unwrap();
        {
            let mut anchors = write.open_table(POA_COMPACT_CHECKPOINT_ANCHORS_V1).unwrap();
            let frame = anchors.get(3).unwrap().unwrap().value().to_vec();
            let mut anchor: StoredPoaCompactCheckpointAnchorV1 =
                decode_frame(ANCHOR_MAGIC, &frame).unwrap();
            anchor.signed.hybrid_quorum[0].signature.0[0] ^= 1;
            let resealed = encode_frame(ANCHOR_MAGIC, &anchor).unwrap();
            anchors.insert(3, resealed.as_slice()).unwrap();
        }
        write.commit().unwrap();
        drop(store);
        let error = match PersistentStore::open_with_test_poa_compact_trust_v1(&path) {
            Ok(_) => panic!("open accepted a locally resealed forged anchor"),
            Err(error) => error.to_string(),
        };
        assert!(error.contains("hybrid quorum is invalid"), "{error}");
    }

    #[test]
    fn attacker_roster_cannot_coherently_replace_certificate_suffix_head_and_anchor() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("attacker-roster-coherent-rewrite.redb");
        let store = compact_three(&path);
        let honest_policy = PersistentStore::test_poa_compact_trust_policy_v1().unwrap();
        let (attacker_root, attacker_signing, attacker_ml_dsa_signing) =
            trust_material(0xA8, honest_policy.deployment_id(), 0);
        let attacker_policy = PoaCompactTrustPolicyV1::new(vec![attacker_root.clone()]).unwrap();

        // Rewrite one certificate and every digest downstream of it, the terminal PCH1 head, and
        // the PCA1 statement. The replacement anchor carries a fully valid Ed25519+ML-DSA
        // signature under a fresh attacker-selected roster. Every same-database relation is now
        // coherent; only the independent deployment trust root distinguishes it from history.
        let write = store.db.begin_write().unwrap();
        let mut predecessor = [0; 32];
        let mut rewritten = Vec::new();
        {
            let certificates = write
                .open_table(POA_COMPACT_AUTHORITY_CERTIFICATES_V1)
                .unwrap();
            for ordinal in 0..3 {
                let frame = certificates
                    .get(ordinal)
                    .unwrap()
                    .expect("certificate")
                    .value()
                    .to_vec();
                let mut certificate: CompactCommitAuthorityCertificateV1 =
                    decode_frame(CERT_MAGIC, &frame).unwrap();
                certificate.predecessor_certificate_digest = predecessor;
                if ordinal == 1 {
                    certificate.creator[0] ^= 0x5A;
                }
                predecessor = certificate.digest().unwrap();
                rewritten.push((ordinal, encode_frame(CERT_MAGIC, &certificate).unwrap()));
            }
        }
        {
            let mut certificates = write
                .open_table(POA_COMPACT_AUTHORITY_CERTIFICATES_V1)
                .unwrap();
            for (ordinal, frame) in &rewritten {
                certificates.insert(*ordinal, frame.as_slice()).unwrap();
            }
        }
        {
            let head = CompactAuthorityHeadV1 {
                next_ordinal: 3,
                certificate_digest: predecessor,
            };
            let frame = encode_frame(HEAD_MAGIC, &head).unwrap();
            write
                .open_table(POA_COMPACT_AUTHORITY_HEAD_V1)
                .unwrap()
                .insert(HEAD_KEY, frame.as_slice())
                .unwrap();
        }
        {
            let mut anchors = write.open_table(POA_COMPACT_CHECKPOINT_ANCHORS_V1).unwrap();
            let frame = anchors.get(3).unwrap().unwrap().value().to_vec();
            let old: StoredPoaCompactCheckpointAnchorV1 =
                decode_frame(ANCHOR_MAGIC, &frame).unwrap();
            let mut statement = old.signed.statement;
            statement.federation_id = attacker_root.federation_id();
            statement.certificate_head = predecessor;
            let signed = sign_statement(
                statement,
                &attacker_signing,
                &attacker_ml_dsa_signing,
                &attacker_root,
            );
            let replacement =
                StoredPoaCompactCheckpointAnchorV1::new(signed, &attacker_root).unwrap();
            let frame = encode_frame(ANCHOR_MAGIC, &replacement).unwrap();
            anchors.insert(3, frame.as_slice()).unwrap();
        }
        write.commit().unwrap();

        store
            .audit_poa_compact_authority_v1(Some(&attacker_policy))
            .expect("the coherent rewrite is self-consistent under the attacker policy");
        let error = store
            .audit_poa_compact_authority_v1(Some(&honest_policy))
            .unwrap_err()
            .to_string();
        assert!(
            error.contains(
                "self-carried federation/roster identity does not equal its external trust root"
            ),
            "{error}"
        );
        drop(store);
        let error = match PersistentStore::open_with_poa_compact_trust_v1(&path, &honest_policy) {
            Ok(_) => panic!("expected deployment policy accepted attacker-selected roster"),
            Err(error) => error.to_string(),
        };
        assert!(
            error.contains(
                "self-carried federation/roster identity does not equal its external trust root"
            ),
            "{error}"
        );
    }

    #[test]
    fn external_policy_rejects_cross_deployment_federation_and_epoch_substitution() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("trust-coordinate-substitution.redb");
        let store = compact_three(&path);
        let policy = PersistentStore::test_poa_compact_trust_policy_v1().unwrap();
        let root = policy.root_at_epoch(0).unwrap();
        let (_, signing, ml_dsa_signing) = test_poa_compact_trust_material_v1().unwrap();
        let frame = store
            .db
            .begin_read()
            .unwrap()
            .open_table(POA_COMPACT_CHECKPOINT_ANCHORS_V1)
            .unwrap()
            .get(3)
            .unwrap()
            .unwrap()
            .value()
            .to_vec();
        let original: StoredPoaCompactCheckpointAnchorV1 =
            decode_frame(ANCHOR_MAGIC, &frame).unwrap();

        let mut cross_deployment = original.clone();
        let mut statement = cross_deployment.signed.statement.clone();
        statement.deployment_id = [0xE1; 32];
        cross_deployment.signed = sign_statement(statement, &signing, &ml_dsa_signing, root);
        let error = policy
            .root_for_statement(&cross_deployment.signed.statement)
            .unwrap_err()
            .to_string();
        assert!(error.contains("deployment is not authorized"), "{error}");

        let mut cross_federation = original.clone();
        let mut statement = cross_federation.signed.statement.clone();
        statement.federation_id = [0xE2; 32];
        cross_federation.signed = sign_statement(statement, &signing, &ml_dsa_signing, root);
        let error = policy
            .root_for_statement(&cross_federation.signed.statement)
            .unwrap_err()
            .to_string();
        assert!(
            error.contains("does not equal its external trust root"),
            "{error}"
        );

        let mut cross_epoch = original;
        let mut statement = cross_epoch.signed.statement.clone();
        statement.committee_epoch = 1;
        statement.federation_id = dregg_federation::derive_federation_id_hybrid_with_epoch(
            root.committee(),
            root.ml_dsa_committee(),
            1,
        );
        cross_epoch.signed = sign_statement(statement, &signing, &ml_dsa_signing, root);
        let error = policy
            .root_for_statement(&cross_epoch.signed.statement)
            .unwrap_err()
            .to_string();
        assert!(error.contains("epoch is absent"), "{error}");
    }

    #[test]
    fn trust_policy_rotation_history_is_external_unique_and_deployment_scoped() {
        let (root_0, _, _) = trust_material(0xB0, [0xD5; 32], 0);
        let (root_1, _, _) = trust_material(0xB1, [0xD5; 32], 1);
        let policy = PoaCompactTrustPolicyV1::new(vec![root_0.clone(), root_1.clone()]).unwrap();
        assert_eq!(policy.root_at_epoch(0), Some(&root_0));
        assert_eq!(policy.root_at_epoch(1), Some(&root_1));

        let duplicate = PoaCompactTrustPolicyV1::new(vec![root_0.clone(), root_0.clone()])
            .unwrap_err()
            .to_string();
        assert!(
            duplicate.contains("two roots for one committee epoch"),
            "{duplicate}"
        );

        let (foreign_deployment, _, _) = trust_material(0xB2, [0xD6; 32], 2);
        let mixed = PoaCompactTrustPolicyV1::new(vec![root_0, foreign_deployment])
            .unwrap_err()
            .to_string();
        assert!(mixed.contains("mixes deployment identities"), "{mixed}");
    }

    #[test]
    fn externally_authorized_rotation_advances_but_cannot_regress_or_drop_history() {
        let deployment = [0xD8; 32];
        let (root_0, signing_0, ml_dsa_signing_0) = trust_material(0xC0, deployment, 0);
        let (root_1, signing_1, ml_dsa_signing_1) = trust_material(0xC1, deployment, 1);
        let epoch_0_policy = PoaCompactTrustPolicyV1::new(vec![root_0.clone()]).unwrap();
        let full_policy =
            PoaCompactTrustPolicyV1::new(vec![root_0.clone(), root_1.clone()]).unwrap();
        let store = PersistentStore::open_in_memory().unwrap();
        let empty_root = crate::canonical_ledger_root(&Ledger::new());
        for ordinal in 0..6 {
            store
                .commit_finalized_turn(ordinal, &record(ordinal, empty_root))
                .unwrap();
        }

        for height in [3, 5, 6] {
            store
                .store_ledger_checkpoint_snapshot(&LedgerCheckpoint {
                    height,
                    cells: Vec::new(),
                    sovereign_commitments: Vec::new(),
                    sovereign_registrations: Vec::new(),
                })
                .unwrap();
        }
        let epoch_0_statement = store
            .prepare_poa_compact_checkpoint_statement_v1(3, &root_0)
            .unwrap()
            .unwrap();
        let epoch_0_anchor =
            sign_statement(epoch_0_statement, &signing_0, &ml_dsa_signing_0, &root_0);
        let retired_error = store
            .compact_below_with_poa_anchor_v1(3, epoch_0_anchor.clone(), &full_policy)
            .unwrap_err()
            .to_string();
        assert!(
            retired_error.contains("retired committee epoch"),
            "{retired_error}"
        );
        assert_eq!(store.commit_compacted_floor().unwrap(), 0);

        assert_eq!(
            store
                .compact_below_with_poa_anchor_v1(3, epoch_0_anchor.clone(), &epoch_0_policy,)
                .unwrap(),
            2
        );
        // Once exact bytes are stored, historical policy material remains usable for response-loss
        // retry even though it can no longer authorize any new floor.
        assert_eq!(
            store
                .compact_below_with_poa_anchor_v1(3, epoch_0_anchor, &full_policy)
                .unwrap(),
            0
        );
        assert_eq!(
            compact_with_material(
                &store,
                5,
                &full_policy,
                &root_1,
                &signing_1,
                &ml_dsa_signing_1,
            )
            .unwrap(),
            2
        );
        store
            .audit_poa_compact_authority_v1(Some(&full_policy))
            .unwrap();

        let floor_before = store.commit_compacted_floor().unwrap();
        let error = compact_with_material(
            &store,
            6,
            &full_policy,
            &root_0,
            &signing_0,
            &ml_dsa_signing_0,
        )
        .unwrap_err()
        .to_string();
        assert!(error.contains("retired committee epoch"), "{error}");
        assert_eq!(store.commit_compacted_floor().unwrap(), floor_before);
        assert!(store.commit_record_at(floor_before).unwrap().is_some());

        let new_only = PoaCompactTrustPolicyV1::new(vec![root_1]).unwrap();
        let error = store
            .audit_poa_compact_authority_v1(Some(&new_only))
            .unwrap_err()
            .to_string();
        assert!(error.contains("epoch is absent"), "{error}");
    }
}
