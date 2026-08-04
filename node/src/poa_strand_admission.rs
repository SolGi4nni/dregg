//! Path of Angels' dormant, durable F-4 admission boundary.
//!
//! This module deliberately stops one step short of changing the live blocklace committee.  It
//! owns the pieces that can be made true independently and tested now:
//!
//! * a PoA-specific policy, absent/dormant by default and fixed at two rooted vouchers;
//! * a vouch row signed both for the generic F-4 edge and for the exact PoA deployment domain,
//!   federation id, and per-voucher sequence;
//! * crash-safe storage of rows attributed to finalized block identities, with replay refusal and
//!   full authenticated revalidation on restart; and
//! * a projection whose only non-seed authority is the Lean
//!   `Dregg2.Distributed.StrandAdmission.admitted` export.  There is no bond-row type or ingestion
//!   method in this boundary.
//!
//! It is NOT yet the live admission path.  The current constitution changes its production quorum
//! as soon as a Join proposal passes, while `poll_finalized_blocks` applies admission later.  Merely
//! replacing that poll-time filter would let a ratified-but-unadmitted candidate raise the producer
//! quorum and halt the old admitted committee.  The cutover therefore also has to split
//! constitutional candidates from the admitted consensus roster; until then callers see
//! [`PoaProjection::Dormant`] unless an explicitly persisted policy says `enforce = true`, and no
//! production caller consumes this projection.

use std::collections::{HashMap, HashSet};

use dregg_federation::admission::{AdmissionRegistry, Vouch};
use dregg_persist::PersistentStore;
use dregg_types::{PublicKey, Signature, SigningKey};
use serde::{Deserialize, Serialize};

/// The exact deployment domain emitted and checked by `scripts/poa-devnet-manifest.mjs`.
pub const POA_DEPLOYMENT_DOMAIN_V1: &str = "pathofangels.network/federation/v1";
/// PoA's fixed positive-N rooted-vouch threshold.
pub const POA_VOUCH_THRESHOLD: usize = 2;
/// This boundary has no bond carrier or ingestion API.  `true` is a review/test-visible policy pin.
pub const POA_BOND_ADMISSION_DISABLED: bool = true;

const CONFIG_KEY: &str = "poa_strand_admission_snapshot_v1";
const FORMAT_VERSION: u16 = 1;
const CONTEXT_SIGNATURE_DOMAIN: &[u8] = b"path-of-angels-strand-vouch-row-v1";

/// Persisted PoA admission policy.  `enforce` is false in the staged/default form and changing it
/// is an explicit durable operation; there is no environment-variable bypass in this module.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PoaAdmissionPolicyV1 {
    format_version: u16,
    deployment_domain: String,
    federation_id: [u8; 32],
    /// Strictly ascending, duplicate-free genesis trust roots.
    seeds: Vec<[u8; 32]>,
    /// Persisted for auditability and rejected unless exactly [`POA_VOUCH_THRESHOLD`].
    vouch_threshold: u16,
    /// Persisted for an explicit, reviewable activation rather than an ambient env switch.
    enforce: bool,
    /// Must remain false.  No bond rows exist in the snapshot format.
    bond_admission: bool,
}

impl PoaAdmissionPolicyV1 {
    /// Construct a staged (dormant) policy for one exact PoA federation.
    pub fn dormant(
        federation_id: [u8; 32],
        seeds: impl IntoIterator<Item = [u8; 32]>,
    ) -> Result<Self, PoaAdmissionError> {
        Self::new(false, federation_id, seeds)
    }

    /// Construct an explicitly enforced policy for boundary testing and the eventual cutover.
    /// Persisting this does not by itself change the live node: no production caller consumes the
    /// projection until the candidate/active-roster split described in the module docs lands.
    pub fn enforced(
        federation_id: [u8; 32],
        seeds: impl IntoIterator<Item = [u8; 32]>,
    ) -> Result<Self, PoaAdmissionError> {
        Self::new(true, federation_id, seeds)
    }

    fn new(
        enforce: bool,
        federation_id: [u8; 32],
        seeds: impl IntoIterator<Item = [u8; 32]>,
    ) -> Result<Self, PoaAdmissionError> {
        let mut seeds: Vec<_> = seeds.into_iter().collect();
        seeds.sort_unstable();
        seeds.dedup();
        let policy = Self {
            format_version: FORMAT_VERSION,
            deployment_domain: POA_DEPLOYMENT_DOMAIN_V1.to_owned(),
            federation_id,
            seeds,
            vouch_threshold: POA_VOUCH_THRESHOLD as u16,
            enforce,
            bond_admission: false,
        };
        policy.validate()?;
        Ok(policy)
    }

    fn validate(&self) -> Result<(), PoaAdmissionError> {
        if self.format_version != FORMAT_VERSION {
            return Err(PoaAdmissionError::UnsupportedFormat(self.format_version));
        }
        if self.deployment_domain != POA_DEPLOYMENT_DOMAIN_V1 {
            return Err(PoaAdmissionError::WrongDeploymentDomain);
        }
        if self.federation_id == [0; 32] {
            return Err(PoaAdmissionError::InvalidPolicy(
                "federation id must be nonzero",
            ));
        }
        if self.seeds.is_empty() {
            return Err(PoaAdmissionError::InvalidPolicy(
                "at least one genesis seed is required",
            ));
        }
        if self.seeds.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(PoaAdmissionError::InvalidPolicy(
                "genesis seeds must be strictly ascending and duplicate-free",
            ));
        }
        if usize::from(self.vouch_threshold) != POA_VOUCH_THRESHOLD {
            return Err(PoaAdmissionError::InvalidPolicy(
                "PoA admission requires exactly two rooted vouchers",
            ));
        }
        if self.bond_admission {
            return Err(PoaAdmissionError::InvalidPolicy(
                "PoA bond admission is disabled until a slashable quote-asset lock exists",
            ));
        }
        Ok(())
    }

    pub fn federation_id(&self) -> [u8; 32] {
        self.federation_id
    }

    pub fn seeds(&self) -> &[[u8; 32]] {
        &self.seeds
    }

    pub fn enforce(&self) -> bool {
        self.enforce
    }
}

/// A vouch with two signature layers:
///
/// * `vouch_signature` is the generic F-4 signature consumed by [`AdmissionRegistry`];
/// * `context_signature` binds that same edge to PoA's deployment domain, federation id, and a
///   strictly increasing voucher-local sequence, so it cannot be replayed from another deployment.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PoaVouchRowV1 {
    format_version: u16,
    deployment_domain: String,
    federation_id: [u8; 32],
    pub voucher: [u8; 32],
    pub candidate: [u8; 32],
    pub sequence: u64,
    vouch_signature: Signature,
    context_signature: Signature,
}

impl PoaVouchRowV1 {
    /// Sign a deployment-bound vouch row.  Sequences are voucher-local and start at one.
    pub fn create(
        voucher_key: &SigningKey,
        candidate: [u8; 32],
        sequence: u64,
        federation_id: [u8; 32],
    ) -> Result<Self, PoaAdmissionError> {
        let voucher = *voucher_key.public_key().as_bytes();
        let generic_message = Vouch::signing_message(&PublicKey(voucher), &PublicKey(candidate));
        let vouch_signature = dregg_types::sign(voucher_key, &generic_message);
        let context_message = context_signing_message(
            POA_DEPLOYMENT_DOMAIN_V1,
            &federation_id,
            &voucher,
            &candidate,
            sequence,
            &vouch_signature,
        );
        let context_signature = dregg_types::sign(voucher_key, &context_message);
        let row = Self {
            format_version: FORMAT_VERSION,
            deployment_domain: POA_DEPLOYMENT_DOMAIN_V1.to_owned(),
            federation_id,
            voucher,
            candidate,
            sequence,
            vouch_signature,
            context_signature,
        };
        row.validate(POA_DEPLOYMENT_DOMAIN_V1, federation_id)?;
        Ok(row)
    }

    fn validate(
        &self,
        deployment_domain: &str,
        federation_id: [u8; 32],
    ) -> Result<(), PoaAdmissionError> {
        if self.format_version != FORMAT_VERSION {
            return Err(PoaAdmissionError::UnsupportedFormat(self.format_version));
        }
        if self.deployment_domain != deployment_domain {
            return Err(PoaAdmissionError::WrongDeploymentDomain);
        }
        if self.federation_id != federation_id {
            return Err(PoaAdmissionError::WrongFederation);
        }
        if self.sequence == 0 {
            return Err(PoaAdmissionError::InvalidVouch(
                "voucher-local sequence must be positive",
            ));
        }
        if self.voucher == self.candidate {
            return Err(PoaAdmissionError::InvalidVouch(
                "a strand cannot vouch for itself",
            ));
        }
        let generic = Vouch {
            voucher: PublicKey(self.voucher),
            candidate: PublicKey(self.candidate),
            signature: self.vouch_signature,
        };
        if !generic.verify_sig() {
            return Err(PoaAdmissionError::InvalidSignature);
        }
        let context_message = context_signing_message(
            &self.deployment_domain,
            &self.federation_id,
            &self.voucher,
            &self.candidate,
            self.sequence,
            &self.vouch_signature,
        );
        if !PublicKey(self.voucher).verify(&context_message, &self.context_signature) {
            return Err(PoaAdmissionError::InvalidContextSignature);
        }
        Ok(())
    }

    fn generic_vouch(&self) -> Vouch {
        Vouch {
            voucher: PublicKey(self.voucher),
            candidate: PublicKey(self.candidate),
            signature: self.vouch_signature,
        }
    }
}

fn context_signing_message(
    deployment_domain: &str,
    federation_id: &[u8; 32],
    voucher: &[u8; 32],
    candidate: &[u8; 32],
    sequence: u64,
    vouch_signature: &Signature,
) -> Vec<u8> {
    let domain = deployment_domain.as_bytes();
    let mut message = Vec::with_capacity(
        CONTEXT_SIGNATURE_DOMAIN.len() + 4 + domain.len() + 32 + 32 + 32 + 8 + 64,
    );
    message.extend_from_slice(CONTEXT_SIGNATURE_DOMAIN);
    message.extend_from_slice(&(domain.len() as u32).to_le_bytes());
    message.extend_from_slice(domain);
    message.extend_from_slice(federation_id);
    message.extend_from_slice(voucher);
    message.extend_from_slice(candidate);
    message.extend_from_slice(&sequence.to_le_bytes());
    message.extend_from_slice(&vouch_signature.0);
    message
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct StoredPoaVouchRowV1 {
    /// Identity in the finalized blocklace order that authorized this durable row.
    source_block_id: [u8; 32],
    row: PoaVouchRowV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct DurablePoaAdmissionV1 {
    format_version: u16,
    policy: PoaAdmissionPolicyV1,
    /// Finalized-order append order.  Per-voucher sequences must increase in this order.
    rows: Vec<StoredPoaVouchRowV1>,
}

impl DurablePoaAdmissionV1 {
    fn validate(&self) -> Result<(), PoaAdmissionError> {
        if self.format_version != FORMAT_VERSION {
            return Err(PoaAdmissionError::UnsupportedFormat(self.format_version));
        }
        self.policy.validate()?;
        let mut sources = HashSet::with_capacity(self.rows.len());
        let mut last_sequence = HashMap::<[u8; 32], u64>::new();
        for stored in &self.rows {
            if stored.source_block_id == [0; 32] {
                return Err(PoaAdmissionError::InvalidVouch(
                    "finalized source block id must be nonzero",
                ));
            }
            if !sources.insert(stored.source_block_id) {
                return Err(PoaAdmissionError::SourceBlockConflict);
            }
            stored
                .row
                .validate(&self.policy.deployment_domain, self.policy.federation_id)?;
            let previous = last_sequence.entry(stored.row.voucher).or_insert(0);
            if stored.row.sequence <= *previous {
                return Err(PoaAdmissionError::Replay);
            }
            *previous = stored.row.sequence;
        }
        Ok(())
    }
}

/// Result of adding one finalized row.  Reprocessing the same block after a crash is idempotent;
/// replaying the row in a different block is an error.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PersistVouchOutcome {
    Stored,
    AlreadyStored,
}

/// Projection is typed so dormant state cannot be mistaken for an identity verdict.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PoaProjection {
    Dormant,
    Enforced(Vec<[u8; 32]>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PoaAdmissionError {
    Store(String),
    Corrupt(String),
    UnsupportedFormat(u16),
    InvalidPolicy(&'static str),
    InvalidVouch(&'static str),
    WrongDeploymentDomain,
    WrongFederation,
    InvalidSignature,
    InvalidContextSignature,
    SourceBlockConflict,
    Replay,
    PolicyConflict,
    LeanUnavailable,
}

impl std::fmt::Display for PoaAdmissionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Store(reason) => write!(f, "PoA admission store error: {reason}"),
            Self::Corrupt(reason) => write!(f, "corrupt PoA admission snapshot: {reason}"),
            Self::UnsupportedFormat(version) => {
                write!(f, "unsupported PoA admission format {version}")
            }
            Self::InvalidPolicy(reason) => write!(f, "invalid PoA admission policy: {reason}"),
            Self::InvalidVouch(reason) => write!(f, "invalid PoA vouch: {reason}"),
            Self::WrongDeploymentDomain => write!(f, "PoA vouch deployment domain mismatch"),
            Self::WrongFederation => write!(f, "PoA vouch federation id mismatch"),
            Self::InvalidSignature => write!(f, "invalid generic F-4 vouch signature"),
            Self::InvalidContextSignature => {
                write!(f, "invalid PoA deployment-context vouch signature")
            }
            Self::SourceBlockConflict => write!(f, "finalized source block identity conflict"),
            Self::Replay => write!(f, "replayed or non-monotonic PoA vouch sequence"),
            Self::PolicyConflict => write!(f, "a different PoA admission policy is already stored"),
            Self::LeanUnavailable => write!(
                f,
                "verified Lean dregg_strand_admit export unavailable; refusing PoA admission"
            ),
        }
    }
}

impl std::error::Error for PoaAdmissionError {}

fn encode(snapshot: &DurablePoaAdmissionV1) -> Result<Vec<u8>, PoaAdmissionError> {
    postcard::to_allocvec(snapshot).map_err(|error| PoaAdmissionError::Corrupt(error.to_string()))
}

fn decode(bytes: &[u8]) -> Result<DurablePoaAdmissionV1, PoaAdmissionError> {
    let snapshot: DurablePoaAdmissionV1 = postcard::from_bytes(bytes)
        .map_err(|error| PoaAdmissionError::Corrupt(error.to_string()))?;
    snapshot.validate()?;
    Ok(snapshot)
}

fn load(store: &PersistentStore) -> Result<Option<DurablePoaAdmissionV1>, PoaAdmissionError> {
    let bytes = store
        .get_config(CONFIG_KEY)
        .map_err(|error| PoaAdmissionError::Store(error.to_string()))?;
    bytes.as_deref().map(decode).transpose()
}

fn enforcement_uses_lean(enforce: bool, lean_available: bool) -> Result<bool, PoaAdmissionError> {
    match (enforce, lean_available) {
        (false, _) => Ok(false),
        (true, true) => Ok(true),
        (true, false) => Err(PoaAdmissionError::LeanUnavailable),
    }
}

/// Persist a complete staged or enforced policy.  Re-installing the byte-identical policy is
/// idempotent; changing roots/domain/federation/mode requires a separate, future consensus action
/// and is refused here rather than silently rewriting the trust root.
pub fn install_policy(
    store: &PersistentStore,
    policy: PoaAdmissionPolicyV1,
) -> Result<(), PoaAdmissionError> {
    policy.validate()?;
    if let Some(existing) = load(store)? {
        if existing.policy == policy {
            return Ok(());
        }
        return Err(PoaAdmissionError::PolicyConflict);
    }
    let snapshot = DurablePoaAdmissionV1 {
        format_version: FORMAT_VERSION,
        policy,
        rows: Vec::new(),
    };
    store
        .set_config(CONFIG_KEY, &encode(&snapshot)?)
        .map_err(|error| PoaAdmissionError::Store(error.to_string()))
}

/// Persist one already-finalized vouch row before acknowledging its source block.  The method does
/// not decide finality; `source_block_id` must come from the finality executor.  One redb
/// transaction replaces the validated snapshot, so a restart observes either the old complete set
/// or the new complete set.
pub fn persist_finalized_vouch(
    store: &PersistentStore,
    source_block_id: [u8; 32],
    row: PoaVouchRowV1,
) -> Result<PersistVouchOutcome, PoaAdmissionError> {
    if source_block_id == [0; 32] {
        return Err(PoaAdmissionError::InvalidVouch(
            "finalized source block id must be nonzero",
        ));
    }
    let mut snapshot = load(store)?.ok_or(PoaAdmissionError::InvalidPolicy(
        "no PoA admission policy is installed",
    ))?;
    row.validate(
        &snapshot.policy.deployment_domain,
        snapshot.policy.federation_id,
    )?;

    if let Some(existing) = snapshot
        .rows
        .iter()
        .find(|stored| stored.source_block_id == source_block_id)
    {
        return if existing.row == row {
            Ok(PersistVouchOutcome::AlreadyStored)
        } else {
            Err(PoaAdmissionError::SourceBlockConflict)
        };
    }
    if snapshot
        .rows
        .iter()
        .filter(|stored| stored.row.voucher == row.voucher)
        .any(|stored| stored.row.sequence >= row.sequence)
    {
        return Err(PoaAdmissionError::Replay);
    }
    snapshot.rows.push(StoredPoaVouchRowV1 {
        source_block_id,
        row,
    });
    snapshot.validate()?;
    store
        .set_config(CONFIG_KEY, &encode(&snapshot)?)
        .map_err(|error| PoaAdmissionError::Store(error.to_string()))?;
    Ok(PersistVouchOutcome::Stored)
}

/// Revalidate the complete durable registry and, only for an explicitly enforced policy, project
/// candidates through the Lean F-4 export.  Runtime deployment coordinates must exactly match the
/// persisted ones.  Missing/corrupt state and missing Lean are errors for the caller to halt on;
/// there is no Rust admission fallback and no bond path.
pub fn project_admitted(
    store: &PersistentStore,
    runtime_deployment_domain: &str,
    runtime_federation_id: [u8; 32],
    candidates: &[[u8; 32]],
) -> Result<PoaProjection, PoaAdmissionError> {
    let Some(snapshot) = load(store)? else {
        return Ok(PoaProjection::Dormant);
    };
    if snapshot.policy.deployment_domain != runtime_deployment_domain {
        return Err(PoaAdmissionError::WrongDeploymentDomain);
    }
    if snapshot.policy.federation_id != runtime_federation_id {
        return Err(PoaAdmissionError::WrongFederation);
    }
    if !enforcement_uses_lean(
        snapshot.policy.enforce,
        dregg_lean_ffi::strand_admit_available(),
    )? {
        return Ok(PoaProjection::Dormant);
    }

    // No bond rows exist in the durable format and this module never calls `add_bond`.  MAX is an
    // additional belt, not the mechanism: absence of a bond ingestion surface is the real policy.
    let mut registry = AdmissionRegistry::new(
        snapshot.policy.seeds.iter().copied().map(PublicKey),
        POA_VOUCH_THRESHOLD,
        u64::MAX,
    );
    for stored in &snapshot.rows {
        if !registry.add_vouch(stored.row.generic_vouch()) {
            return Err(PoaAdmissionError::InvalidSignature);
        }
    }
    let candidates: Vec<PublicKey> = candidates.iter().copied().map(PublicKey).collect();
    let admitted = registry
        .admitted_participants(&candidates)
        .into_iter()
        .map(|key| *key.as_bytes())
        .collect();
    Ok(PoaProjection::Enforced(admitted))
}

/// Read the authenticated durable vouch edges for diagnostics/operator tooling.  The return value
/// is available only after the whole snapshot validates; corrupt state never degrades to empty.
pub fn durable_vouch_edges(
    store: &PersistentStore,
) -> Result<Vec<([u8; 32], [u8; 32], u64)>, PoaAdmissionError> {
    Ok(load(store)?
        .map(|snapshot| {
            snapshot
                .rows
                .into_iter()
                .map(|stored| {
                    (
                        stored.row.voucher,
                        stored.row.candidate,
                        stored.row.sequence,
                    )
                })
                .collect()
        })
        .unwrap_or_default())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    fn key() -> (SigningKey, [u8; 32]) {
        let (secret, public) = dregg_types::generate_keypair();
        (secret, *public.as_bytes())
    }

    fn source(byte: u8) -> [u8; 32] {
        [byte; 32]
    }

    fn installed(store: &PersistentStore, federation: [u8; 32], seeds: &[[u8; 32]], enforce: bool) {
        let policy = if enforce {
            PoaAdmissionPolicyV1::enforced(federation, seeds.iter().copied())
        } else {
            PoaAdmissionPolicyV1::dormant(federation, seeds.iter().copied())
        }
        .unwrap();
        install_policy(store, policy).unwrap();
    }

    fn require_lean_admission() {
        crate::install_verified_distributed_gates();
        assert!(
            dregg_lean_ffi::strand_admit_available(),
            "this boundary test requires the closure-complete Lean admission export"
        );
    }

    #[test]
    fn absent_and_staged_policies_are_explicitly_dormant() {
        let store = PersistentStore::open_in_memory().unwrap();
        let federation = [0x44; 32];
        let (_, seed) = key();
        let (_, stranger) = key();
        assert_eq!(
            project_admitted(
                &store,
                POA_DEPLOYMENT_DOMAIN_V1,
                federation,
                &[seed, stranger]
            )
            .unwrap(),
            PoaProjection::Dormant
        );
        installed(&store, federation, &[seed], false);
        assert_eq!(
            project_admitted(
                &store,
                POA_DEPLOYMENT_DOMAIN_V1,
                federation,
                &[seed, stranger]
            )
            .unwrap(),
            PoaProjection::Dormant
        );
    }

    #[test]
    fn enforced_policy_refuses_when_lean_authority_is_unavailable() {
        assert_eq!(enforcement_uses_lean(false, false), Ok(false));
        assert_eq!(enforcement_uses_lean(false, true), Ok(false));
        assert_eq!(enforcement_uses_lean(true, true), Ok(true));
        assert_eq!(
            enforcement_uses_lean(true, false),
            Err(PoaAdmissionError::LeanUnavailable)
        );
    }

    #[test]
    fn authenticated_rows_survive_restart_and_drive_n2_transitive_lean_closure() {
        require_lean_admission();
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("poa-admission.redb");
        let federation = [0x45; 32];
        let (sk_a, a) = key();
        let (sk_b, b) = key();
        let (sk_first, first) = key();
        let (_, second) = key();

        {
            let store = PersistentStore::open(&path).unwrap();
            installed(&store, federation, &[a, b], true);
            persist_finalized_vouch(
                &store,
                source(1),
                PoaVouchRowV1::create(&sk_a, first, 1, federation).unwrap(),
            )
            .unwrap();
            persist_finalized_vouch(
                &store,
                source(2),
                PoaVouchRowV1::create(&sk_b, first, 1, federation).unwrap(),
            )
            .unwrap();
            persist_finalized_vouch(
                &store,
                source(3),
                PoaVouchRowV1::create(&sk_a, second, 2, federation).unwrap(),
            )
            .unwrap();
            persist_finalized_vouch(
                &store,
                source(4),
                PoaVouchRowV1::create(&sk_first, second, 1, federation).unwrap(),
            )
            .unwrap();
        }

        let restarted = PersistentStore::open(&path).unwrap();
        let projection = project_admitted(
            &restarted,
            POA_DEPLOYMENT_DOMAIN_V1,
            federation,
            &[a, b, first, second],
        )
        .unwrap();
        assert_eq!(
            projection,
            PoaProjection::Enforced(vec![a, b, first, second]),
            "the second generation needs the first generation's newly rooted vouch"
        );
        assert_eq!(durable_vouch_edges(&restarted).unwrap().len(), 4);
    }

    #[test]
    fn replay_and_source_identity_conflicts_refuse() {
        let store = PersistentStore::open_in_memory().unwrap();
        let federation = [0x46; 32];
        let (sk_a, a) = key();
        let (_, b) = key();
        let (_, c) = key();
        installed(&store, federation, &[a], true);
        let row = PoaVouchRowV1::create(&sk_a, b, 1, federation).unwrap();
        assert_eq!(
            persist_finalized_vouch(&store, source(1), row.clone()).unwrap(),
            PersistVouchOutcome::Stored
        );
        assert_eq!(
            persist_finalized_vouch(&store, source(1), row.clone()).unwrap(),
            PersistVouchOutcome::AlreadyStored,
            "crash replay of the same finalized identity is idempotent"
        );
        assert_eq!(
            persist_finalized_vouch(&store, source(2), row),
            Err(PoaAdmissionError::Replay),
            "the same voucher-local sequence cannot be replayed in another block"
        );
        let different = PoaVouchRowV1::create(&sk_a, c, 2, federation).unwrap();
        assert_eq!(
            persist_finalized_vouch(&store, source(1), different),
            Err(PoaAdmissionError::SourceBlockConflict),
            "one finalized identity cannot authorize two row bodies"
        );
    }

    #[test]
    fn wrong_domain_and_wrong_federation_rows_refuse() {
        let store = PersistentStore::open_in_memory().unwrap();
        let federation = [0x47; 32];
        let other_federation = [0x48; 32];
        let (sk_a, a) = key();
        let (_, candidate) = key();
        installed(&store, federation, &[a], true);

        let wrong_federation =
            PoaVouchRowV1::create(&sk_a, candidate, 1, other_federation).unwrap();
        assert_eq!(
            persist_finalized_vouch(&store, source(1), wrong_federation),
            Err(PoaAdmissionError::WrongFederation)
        );

        let mut wrong_domain = PoaVouchRowV1::create(&sk_a, candidate, 1, federation).unwrap();
        wrong_domain.deployment_domain = "main.dregg.example/federation/v1".into();
        assert_eq!(
            persist_finalized_vouch(&store, source(2), wrong_domain),
            Err(PoaAdmissionError::WrongDeploymentDomain)
        );

        assert_eq!(
            project_admitted(
                &store,
                "another.application/federation/v1",
                federation,
                &[a, candidate]
            ),
            Err(PoaAdmissionError::WrongDeploymentDomain)
        );
        assert_eq!(
            project_admitted(
                &store,
                POA_DEPLOYMENT_DOMAIN_V1,
                other_federation,
                &[a, candidate]
            ),
            Err(PoaAdmissionError::WrongFederation)
        );
    }

    #[test]
    fn forged_generic_or_context_signature_refuses_before_persistence() {
        let store = PersistentStore::open_in_memory().unwrap();
        let federation = [0x4a; 32];
        let (sk_a, a) = key();
        let (_, candidate) = key();
        installed(&store, federation, &[a], true);

        let mut forged_generic = PoaVouchRowV1::create(&sk_a, candidate, 1, federation).unwrap();
        forged_generic.vouch_signature.0[0] ^= 1;
        assert_eq!(
            persist_finalized_vouch(&store, source(1), forged_generic),
            Err(PoaAdmissionError::InvalidSignature)
        );

        let mut forged_context = PoaVouchRowV1::create(&sk_a, candidate, 1, federation).unwrap();
        forged_context.context_signature.0[0] ^= 1;
        assert_eq!(
            persist_finalized_vouch(&store, source(2), forged_context),
            Err(PoaAdmissionError::InvalidContextSignature)
        );
        assert!(durable_vouch_edges(&store).unwrap().is_empty());
    }

    #[test]
    fn rootless_sybil_ring_cannot_bootstrap_and_no_bond_surface_exists() {
        require_lean_admission();
        assert!(POA_BOND_ADMISSION_DISABLED);
        let store = PersistentStore::open_in_memory().unwrap();
        let federation = [0x49; 32];
        let (_, seed) = key();
        let (sk_x, x) = key();
        let (sk_y, y) = key();
        let (sk_z, z) = key();
        installed(&store, federation, &[seed], true);

        // Each Sybil gets two distinct ring vouches, but not one voucher is rooted at the seed.
        let rows = [
            PoaVouchRowV1::create(&sk_y, x, 1, federation).unwrap(),
            PoaVouchRowV1::create(&sk_z, x, 1, federation).unwrap(),
            PoaVouchRowV1::create(&sk_x, y, 1, federation).unwrap(),
            PoaVouchRowV1::create(&sk_z, y, 2, federation).unwrap(),
            PoaVouchRowV1::create(&sk_x, z, 2, federation).unwrap(),
            PoaVouchRowV1::create(&sk_y, z, 2, federation).unwrap(),
        ];
        for (index, row) in rows.into_iter().enumerate() {
            persist_finalized_vouch(&store, source((index + 1) as u8), row).unwrap();
        }

        let PoaProjection::Enforced(admitted) = project_admitted(
            &store,
            POA_DEPLOYMENT_DOMAIN_V1,
            federation,
            &[seed, x, y, z],
        )
        .unwrap() else {
            panic!("policy is explicitly enforced")
        };
        assert_eq!(admitted, vec![seed]);
        assert_eq!(
            admitted.into_iter().collect::<BTreeSet<_>>(),
            BTreeSet::from([seed])
        );
    }

    #[test]
    fn corrupted_snapshot_refuses_instead_of_becoming_empty() {
        let store = PersistentStore::open_in_memory().unwrap();
        store.set_config(CONFIG_KEY, b"not-postcard").unwrap();
        assert!(matches!(
            durable_vouch_edges(&store),
            Err(PoaAdmissionError::Corrupt(_))
        ));
    }
}
