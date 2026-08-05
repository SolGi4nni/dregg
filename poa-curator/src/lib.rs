//! Sentyr-facing curation over the Lean-emitted POAG1 content bundle.
//!
//! This is intentionally an authority/IO edge, not a second game engine. The
//! bundle's mission specs, beta discoveries, contribution previews, and world
//! states are retained as the exact JSON emitted by Lean. Rust verifies the
//! byte-pinned container, selects values, and delegates signatures to the
//! canonical `dregg-types` Ed25519 primitive.

pub mod authority_export;
pub mod companion;
pub mod signal_replay;

use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, OpenOptions};
use std::io::Read;
use std::path::{Component, Path, PathBuf};

#[cfg(unix)]
use std::os::unix::fs::OpenOptionsExt;

use dregg_types::{PublicKey, Signature, SigningKey};
use serde::de::{MapAccess, SeqAccess, Visitor};
use serde::{Deserialize, Deserializer, Serialize};
use serde_json::Value;
use sha2::{Digest as _, Sha256};
use thiserror::Error;

pub const POAG1_FORMAT: &str = "POAG1";
pub const POAG1_SCHEMA_VERSION: u64 = 1;
pub const POAG1_AUTHORITY: &str = "Dregg2.Games.PathOfAngels";
pub const CONTENT_EPOCH_SCHEMA: &str = "POA-CONTENT-EPOCH-SIGNATURE-V1";
pub const CURATOR_KEY_SCHEMA: &str = "POA-CURATOR-KEY-V1";
pub const CANON_DECISION_SCHEMA: &str = "POA-CANON-DECISION-V1";
pub const DETACHED_SIGNATURE_FILENAME: &str = "manifest.sig.json";
pub const POA_DEPLOYMENT_MANIFEST_SCHEMA: &str = "dregg-poa-devnet-manifest-v1";
pub const POA_DEPLOYMENT_DOMAIN: &str = "pathofangels.network/federation/v1";
pub const POA_EPOCH_PREVIEW_SCHEMA: &str = "POA-EPOCH-PREVIEW-V1";

/// Canonical semantic image of the only operator policy accepted by the v1
/// Path of Angels production federation. The manifest itself may use any JSON
/// whitespace/key order, but this policy value may not be weakened or grown.
pub const POA_PRODUCTION_POLICY_CANONICAL: &str = "{\"admission\":\"committee-ratified-manual-v1\",\"allow_unverified_consensus\":false,\"auto_approve_joins\":false,\"descriptor_pinned\":true,\"f4_transitive_vouch_rows_live\":false,\"faucet_http\":false,\"follower_first\":true,\"generic_genesis_value_issued\":false,\"objective_vouch_admission_ready\":false,\"prove_turns\":true,\"public_private_activity_counts\":false,\"require_lean\":true,\"shares_main_identity\":false,\"shares_main_storage\":false,\"strand_admission_gate\":true}";
pub const POA_SIGNAL_DEPLOYMENT_IDENTITY_DOMAIN: &str = "POA-SIGNAL-DEPLOYMENT-IDENTITY-V2";
const ML_DSA_65_PUBLIC_KEY_BYTES: usize = 1952;
const FEDERATION_ID_DOMAIN: &str = "dregg-fed-id-v1";

const CONTENT_EPOCH_DOMAIN: &[u8] = b"pathofangels.network/content-epoch/v1\0";
const CANON_DECISION_DOMAIN: &[u8] = b"pathofangels.network/canon-promotion/v1\0";
const CONTENT_ROOT_DOMAIN: &[u8] = b"path-of-angels/content-root/v1\0";
const ACTIVATION_DIGEST_DOMAIN: &[u8] = b"pathofangels.network/activation-digest/v1\0";
const MAX_MANIFEST_BYTES: u64 = 1024 * 1024;
const MAX_ARTIFACT_BYTES: u64 = 16 * 1024 * 1024;
const MAX_MISSIONS_PER_EPOCH: usize = 3;
const MAX_FIXTURES_PER_EPOCH: usize = 24;
const MAX_FIXTURES_PER_MISSION: usize = 8;
const MAX_DISCOVERIES_PER_MISSION: usize = 8;
const MAX_RELICS_PER_MISSION: usize = 16;
const SCHEMA_PATH: &str = "schema.json";
const CATALOG_PATH: &str = "catalog.json";
const SIGNAL_PATH: &str = "games/signal-triangulation.json";
const SUPPORTED_GAME_PATHS: [&str; MAX_MISSIONS_PER_EPOCH] = [
    "games/relay-repair.json",
    "games/salvage-lock.json",
    SIGNAL_PATH,
];

#[derive(Debug, Error)]
pub enum CuratorError {
    #[error("I/O at {path}: {source}")]
    Io {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
    #[error("JSON refused in {path}: {reason}")]
    Json { path: PathBuf, reason: String },
    #[error("POAG1 manifest refused: {0}")]
    Manifest(String),
    #[error("POAG1 artifact {path} refused: {reason}")]
    Artifact { path: String, reason: String },
    #[error("POAG1 catalog refused: {0}")]
    Catalog(String),
    #[error("PoA deployment binding refused: {0}")]
    Deployment(String),
    #[error("mission {0} is not present in the emitted catalog")]
    UnknownMission(u64),
    #[error("preview fixture {0} is not present in the emitted catalog")]
    UnknownFixture(String),
    #[error("artifact is not predeclared for mission {mission_id}: {artifact:?}")]
    DiscoveryNotAllowed {
        mission_id: u64,
        artifact: ArtifactRef,
    },
    #[error("the requested beta-discovery list contains a duplicate exact artifact")]
    DuplicateDiscovery,
    #[error("hex field {field} is malformed; expected {bytes} lowercase bytes")]
    MalformedHex { field: &'static str, bytes: usize },
    #[error("content-epoch envelope refused: {0}")]
    ContentEpoch(String),
    #[error("Lean mission activation refused: {0}")]
    Activation(String),
    #[error("canon decision refused: {0}")]
    CanonDecision(String),
    #[error("Lean canon admission refused: {0}")]
    CanonAdmission(String),
    #[error("signature did not verify under the externally pinned curator key")]
    BadSignature,
}

fn io_error(path: &Path, source: std::io::Error) -> CuratorError {
    CuratorError::Io {
        path: path.to_path_buf(),
        source,
    }
}

/// The strict five-field pin emitted for every POAG1 artifact.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ArtifactPin {
    pub path: String,
    pub media_type: String,
    pub bytes: u64,
    pub sha256: String,
    pub fnv1a64: String,
}

/// The strict POAG1 manifest. Unknown fields are a version mismatch, not hints.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Poag1Manifest {
    pub format: String,
    pub schema_version: u64,
    pub source_digest: String,
    pub authority: String,
    pub artifacts: Vec<ArtifactPin>,
}

/// Exact runtime projection of Lean's `ArtifactRef`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ArtifactRef {
    pub mission_id: u64,
    pub artifact_id: u64,
    pub source_digest: String,
    pub content_digest: String,
}

impl ArtifactRef {
    fn validate(&self) -> Result<(), CuratorError> {
        parse_sha256(&self.source_digest, "source_digest")?;
        parse_sha256(&self.content_digest, "content_digest")?;
        Ok(())
    }
}

/// A Lean-emitted bounded preview. The three semantic values stay opaque here:
/// displaying them is safe; recomputing `applyContribution` in Rust is not.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct EmittedPreview {
    pub fixture_id: String,
    pub base_world: Value,
    pub contribution: Value,
    pub preview_world: Value,
}

/// A review draft containing only values selected from the authenticated POAG1
/// catalog. `mission_spec` is the exact Lean-emitted mission record.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct CuratorDraft {
    pub manifest_sha256: String,
    pub source_digest: String,
    pub mission_id: u64,
    pub mission_spec: Value,
    pub predeclared_beta_discoveries: Vec<ArtifactRef>,
    pub preview: Option<EmittedPreview>,
}

/// Deterministic, review-only projection of one authenticated content epoch.
/// It contains no secret material and is not a mission-activation token.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct EpochPreview {
    pub schema: String,
    pub manifest_sha256: String,
    pub source_digest: String,
    pub content_root: String,
    pub content_epoch: u64,
    pub deployment_id: String,
    pub federation_id: String,
    pub signature_status: EpochPreviewSignatureStatus,
    pub signature_epoch: Option<u64>,
    pub signature_counter: Option<u64>,
    pub notice: String,
    pub missions: Vec<MissionPreview>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum EpochPreviewSignatureStatus {
    Absent,
    Valid,
}

/// Sentyr-facing review fields selected from one exact authenticated mission.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct MissionPreview {
    pub mission_id: u64,
    pub title: String,
    pub ruleset: String,
    pub action_cap: u64,
    pub privacy_grade: String,
    pub reward_class: String,
    pub budget: MissionBudgetPreview,
    pub allowed_relics: Vec<u64>,
    pub beta_artifacts: Vec<ArtifactRef>,
    pub descriptor_path: String,
    pub content_visibility: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct MissionBudgetPreview {
    pub intel: u64,
    pub supplies: u64,
    pub cohesion: u64,
    pub influence: u64,
    pub score: u64,
    pub relics: u64,
}

/// Loaded and byte-verified POAG1 bundle.
#[derive(Clone, Debug)]
pub struct Poag1Bundle {
    manifest_path: PathBuf,
    manifest_bytes: Vec<u8>,
    manifest_sha256: String,
    manifest: Poag1Manifest,
    artifacts: BTreeMap<String, Vec<u8>>,
    schema: Value,
    catalog: Value,
    game_descriptors: BTreeMap<String, Value>,
    content_root: String,
    content_epoch: u64,
    missions: BTreeMap<u64, MissionIndex>,
    fixtures: BTreeMap<String, FixtureIndex>,
}

/// Deployment identity read from the separately generated `poa-devnet.json`.
/// This is a binding input, not a second verifier for the genesis descriptor:
/// operators must still run `scripts/poa-devnet.sh verify` first.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoaDeploymentScope {
    deployment_id: String,
    federation_id: String,
    genesis_sha256: String,
    manifest_sha256: String,
    policy_sha256: String,
    deployment_digest: String,
    validator_public_keys: Vec<[u8; 32]>,
    verified: Option<VerifiedDeploymentArtifacts>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct VerifiedDeploymentArtifacts {
    root: PathBuf,
    manifest_bytes: Vec<u8>,
    genesis_bytes: Vec<u8>,
    nodes: Vec<PoaNodeScope>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct PoaNodeScope {
    index: usize,
    public_key: String,
    data_dir: String,
    http_bind: String,
    http_port: u16,
    gossip_host: String,
    gossip_port: u16,
    gossip_peers: Vec<String>,
}

impl PoaDeploymentScope {
    pub fn load(path: impl AsRef<Path>) -> Result<Self, CuratorError> {
        let path = path.as_ref();
        let bytes = read_regular_bounded(path, 1024 * 1024)?;
        let value = parse_strict_json(&bytes).map_err(|reason| CuratorError::Json {
            path: path.to_path_buf(),
            reason,
        })?;
        let object = value
            .as_object()
            .ok_or_else(|| CuratorError::Deployment("poa-devnet.json is not an object".into()))?;
        require_exact_object_keys(
            object,
            &[
                "schema",
                "deployment_domain",
                "deployment_id",
                "federation_id",
                "committee_epoch",
                "threshold",
                "genesis_sha256",
                "descriptor",
                "policy",
                "nodes",
            ],
            "poa-devnet.json",
        )
        .map_err(CuratorError::Deployment)?;
        if object.get("schema").and_then(Value::as_str) != Some(POA_DEPLOYMENT_MANIFEST_SCHEMA) {
            return Err(CuratorError::Deployment(
                "unknown poa-devnet.json schema".into(),
            ));
        }
        if object.get("deployment_domain").and_then(Value::as_str) != Some(POA_DEPLOYMENT_DOMAIN) {
            return Err(CuratorError::Deployment(
                "poa-devnet.json has the wrong deployment domain".into(),
            ));
        }
        let deployment_id = object
            .get("deployment_id")
            .and_then(Value::as_str)
            .ok_or_else(|| CuratorError::Deployment("deployment_id is absent".into()))?;
        parse_hex_array::<32>(deployment_id, "deployment_id")?;
        let federation_id = object
            .get("federation_id")
            .and_then(Value::as_str)
            .ok_or_else(|| CuratorError::Deployment("federation_id is absent".into()))?;
        parse_hex_array::<32>(federation_id, "federation_id")?;
        let genesis_sha256 = object
            .get("genesis_sha256")
            .and_then(Value::as_str)
            .ok_or_else(|| CuratorError::Deployment("genesis_sha256 is absent".into()))?;
        parse_hex_array::<32>(genesis_sha256, "genesis_sha256")?;
        let manifest_sha256 = hex_encode(&sha256_raw(&bytes));
        let policy_bytes = canonical_production_policy_bytes()?;
        let policy_sha256 = hex_encode(&sha256_raw(&policy_bytes));
        let deployment_digest =
            derive_signal_deployment_digest(deployment_id, &manifest_sha256, &policy_sha256);
        let validator_public_keys = manifest_validator_public_keys(object)?;
        Ok(Self {
            deployment_id: deployment_id.to_owned(),
            federation_id: federation_id.to_owned(),
            genesis_sha256: genesis_sha256.to_owned(),
            manifest_sha256,
            policy_sha256,
            deployment_digest,
            validator_public_keys,
            verified: None,
        })
    }

    /// Load the public deployment manifest and verify that it names these exact
    /// genesis bytes and the committee identity contained in them.
    ///
    /// This is the in-process counterpart of the identity-bearing portion of
    /// `scripts/poa-devnet-manifest.mjs verify-public`. It deliberately does not
    /// inspect operator seed files or a main-network data directory: those are
    /// deployment-topology checks, while this token binds the exact immutable
    /// manifest/genesis pair consumed by content activation.
    pub fn load_verified(
        manifest_path: impl AsRef<Path>,
        genesis_path: impl AsRef<Path>,
        main_data_dir: impl AsRef<Path>,
    ) -> Result<Self, CuratorError> {
        let manifest_path = manifest_path.as_ref();
        let genesis_path = genesis_path.as_ref();
        let manifest_bytes = read_regular_bounded(manifest_path, 1024 * 1024)?;
        let manifest = parse_strict_json(&manifest_bytes).map_err(|reason| CuratorError::Json {
            path: manifest_path.to_path_buf(),
            reason,
        })?;
        let manifest = manifest
            .as_object()
            .ok_or_else(|| CuratorError::Deployment("poa-devnet.json is not an object".into()))?;
        require_exact_object_keys(
            manifest,
            &[
                "schema",
                "deployment_domain",
                "deployment_id",
                "federation_id",
                "committee_epoch",
                "threshold",
                "genesis_sha256",
                "descriptor",
                "policy",
                "nodes",
            ],
            "poa-devnet.json",
        )
        .map_err(CuratorError::Deployment)?;
        if manifest.get("schema").and_then(Value::as_str) != Some(POA_DEPLOYMENT_MANIFEST_SCHEMA)
            || manifest.get("deployment_domain").and_then(Value::as_str)
                != Some(POA_DEPLOYMENT_DOMAIN)
        {
            return Err(CuratorError::Deployment(
                "poa-devnet.json has the wrong production schema/domain".into(),
            ));
        }
        let deployment_id = manifest_hex32(manifest, "deployment_id")?;
        let federation_id = manifest_hex32(manifest, "federation_id")?;
        let pinned_genesis_sha256 = manifest_hex32(manifest, "genesis_sha256")?;
        verify_production_policy(manifest.get("policy"))?;
        if manifest.get("descriptor").and_then(Value::as_str) != Some("bundle/genesis.json") {
            return Err(CuratorError::Deployment(
                "poa-devnet.json descriptor is not bundle/genesis.json".into(),
            ));
        }
        let manifest_root = manifest_path.parent().ok_or_else(|| {
            CuratorError::Deployment("poa-devnet.json has no containing directory".into())
        })?;
        let root =
            fs::canonicalize(manifest_root).map_err(|error| io_error(manifest_root, error))?;
        let main_root = fs::canonicalize(main_data_dir.as_ref())
            .map_err(|error| io_error(main_data_dir.as_ref(), error))?;
        if paths_overlap(&root, &main_root) {
            return Err(CuratorError::Deployment(
                "PoA deployment root and main data directory are not disjoint".into(),
            ));
        }
        let expected_genesis = fs::canonicalize(root.join("bundle/genesis.json"))
            .map_err(|error| io_error(&manifest_root.join("bundle/genesis.json"), error))?;
        let supplied_genesis =
            fs::canonicalize(genesis_path).map_err(|error| io_error(genesis_path, error))?;
        if supplied_genesis != expected_genesis {
            return Err(CuratorError::Deployment(
                "supplied genesis is not the manifest's exact descriptor path".into(),
            ));
        }

        let genesis_bytes = read_regular_bounded(&supplied_genesis, MAX_ARTIFACT_BYTES)?;
        let actual_genesis_sha256 = hex_encode(&sha256_raw(&genesis_bytes));
        if actual_genesis_sha256 != pinned_genesis_sha256 {
            return Err(CuratorError::Deployment(
                "poa-devnet.json does not pin the supplied genesis bytes".into(),
            ));
        }
        let genesis = parse_strict_json(&genesis_bytes).map_err(|reason| CuratorError::Json {
            path: supplied_genesis.clone(),
            reason,
        })?;
        let genesis = genesis
            .as_object()
            .ok_or_else(|| CuratorError::Deployment("genesis.json is not an object".into()))?;
        if genesis.get("deployment_domain").and_then(Value::as_str) != Some(POA_DEPLOYMENT_DOMAIN) {
            return Err(CuratorError::Deployment(
                "genesis.json has the wrong deployment domain".into(),
            ));
        }
        if genesis.get("federation_id").and_then(Value::as_str) != Some(&federation_id) {
            return Err(CuratorError::Deployment(
                "genesis.json federation differs from poa-devnet.json".into(),
            ));
        }
        let genesis_epoch = genesis
            .get("committee_epoch")
            .and_then(Value::as_u64)
            .unwrap_or(0);
        let manifest_epoch = manifest
            .get("committee_epoch")
            .and_then(Value::as_u64)
            .ok_or_else(|| CuratorError::Deployment("manifest committee_epoch is absent".into()))?;
        if genesis_epoch != manifest_epoch {
            return Err(CuratorError::Deployment(
                "manifest committee epoch differs from genesis.json".into(),
            ));
        }
        let genesis_threshold = genesis
            .get("threshold")
            .and_then(Value::as_u64)
            .filter(|value| *value > 0)
            .ok_or_else(|| CuratorError::Deployment("genesis threshold is not positive".into()))?;
        if manifest.get("threshold").and_then(Value::as_u64) != Some(genesis_threshold) {
            return Err(CuratorError::Deployment(
                "manifest threshold differs from genesis.json".into(),
            ));
        }
        let validators = verify_genesis_economy_and_committee(
            genesis,
            &federation_id,
            genesis_epoch,
            genesis_threshold,
        )?;
        let validator_public_keys = validators
            .iter()
            .map(|validator| parse_hex_array::<32>(&validator.public_key, "validator public_key"))
            .collect::<Result<Vec<_>, _>>()?;
        let nodes = verify_public_topology(manifest, &validators)?;
        let deployment_preimage = format!(
            "{POA_DEPLOYMENT_DOMAIN}\0{}\0{}",
            federation_id, pinned_genesis_sha256
        );
        if hex_encode(&sha256_raw(deployment_preimage.as_bytes())) != deployment_id {
            return Err(CuratorError::Deployment(
                "deployment_id does not rederive from domain, federation, and genesis bytes".into(),
            ));
        }
        verify_main_identity_isolation(&root, &main_root, genesis)?;

        let manifest_sha256 = hex_encode(&sha256_raw(&manifest_bytes));
        let policy_sha256 = hex_encode(&sha256_raw(&canonical_production_policy_bytes()?));
        let deployment_digest =
            derive_signal_deployment_digest(&deployment_id, &manifest_sha256, &policy_sha256);
        Ok(Self {
            deployment_id,
            federation_id,
            genesis_sha256: pinned_genesis_sha256,
            manifest_sha256,
            policy_sha256,
            deployment_digest,
            validator_public_keys,
            verified: Some(VerifiedDeploymentArtifacts {
                root,
                manifest_bytes,
                genesis_bytes,
                nodes,
            }),
        })
    }

    pub fn deployment_id(&self) -> &str {
        &self.deployment_id
    }

    pub fn federation_id(&self) -> &str {
        &self.federation_id
    }

    pub fn genesis_sha256(&self) -> &str {
        &self.genesis_sha256
    }

    pub fn manifest_sha256(&self) -> &str {
        &self.manifest_sha256
    }

    pub fn policy_sha256(&self) -> &str {
        &self.policy_sha256
    }

    /// Identity persisted in `PoaSignalHeadV1`. Unlike the public deployment
    /// id, this binds the exact manifest bytes and the immutable production
    /// policy digest as well as the manifest-pinned genesis identity.
    pub fn deployment_digest(&self) -> &str {
        &self.deployment_digest
    }

    /// Exact ordered Ed25519 committee roster pinned by this deployment.
    /// Authority exports are accepted only when their node signature verifies
    /// under one of these keys; the export's self-declared key is never a trust
    /// root.
    pub fn validator_public_keys(&self) -> &[[u8; 32]] {
        &self.validator_public_keys
    }

    pub fn verified_manifest_bytes(&self) -> Result<&[u8], CuratorError> {
        self.verified
            .as_ref()
            .map(|verified| verified.manifest_bytes.as_slice())
            .ok_or_else(|| CuratorError::Deployment("deployment scope is not verified".into()))
    }

    pub fn verified_genesis_bytes(&self) -> Result<&[u8], CuratorError> {
        self.verified
            .as_ref()
            .map(|verified| verified.genesis_bytes.as_slice())
            .ok_or_else(|| CuratorError::Deployment("deployment scope is not verified".into()))
    }

    /// Bind one serving directory to the retained authenticated descriptor and
    /// exact manifest-derived operator configuration. The authoritative
    /// genesis path is never re-read, closing an A-then-B tuple race.
    pub fn verify_serving_data_dir(
        &self,
        data_dir: impl AsRef<Path>,
        runtime_genesis_bytes: Option<&[u8]>,
    ) -> Result<usize, CuratorError> {
        let verified = self
            .verified
            .as_ref()
            .ok_or_else(|| CuratorError::Deployment("deployment scope is not verified".into()))?;
        let data_dir = fs::canonicalize(data_dir.as_ref())
            .map_err(|error| io_error(data_dir.as_ref(), error))?;
        let (node, expected_dir) = verified
            .nodes
            .iter()
            .find_map(|node| {
                let expected = verified.root.join(&node.data_dir);
                fs::canonicalize(&expected)
                    .ok()
                    .filter(|candidate| *candidate == data_dir)
                    .map(|candidate| (node, candidate))
            })
            .ok_or_else(|| {
                CuratorError::Deployment(
                    "serving data directory is not an exact manifest node path".into(),
                )
            })?;
        if !expected_dir.starts_with(&verified.root) || expected_dir.join(".devnet").exists() {
            return Err(CuratorError::Deployment(
                "serving data directory escapes PoA root or carries .devnet".into(),
            ));
        }
        let owned;
        let runtime = match runtime_genesis_bytes {
            Some(bytes) => bytes,
            None => {
                owned =
                    read_regular_bounded(&expected_dir.join("genesis.json"), MAX_ARTIFACT_BYTES)?;
                &owned
            }
        };
        if runtime != verified.genesis_bytes {
            return Err(CuratorError::Deployment(
                "serving genesis bytes differ from the retained authenticated descriptor".into(),
            ));
        }
        let expected_operator = operator_config(self, verified, node);
        let operator_path = expected_dir.join("operator.env");
        let actual_operator = read_regular_bounded(&operator_path, 64 * 1024)?;
        if actual_operator != expected_operator.as_bytes() {
            return Err(CuratorError::Deployment(format!(
                "{} differs from exact manifest-derived production policy",
                operator_path.display()
            )));
        }
        Ok(node.index)
    }
}

#[derive(Clone, Debug)]
struct ValidatorIdentity {
    public_key: String,
    hybrid_id: [u8; 32],
}

fn canonical_production_policy_bytes() -> Result<Vec<u8>, CuratorError> {
    let policy: Value = serde_json::from_str(POA_PRODUCTION_POLICY_CANONICAL).map_err(|error| {
        CuratorError::Deployment(format!("invalid compiled PoA policy: {error}"))
    })?;
    serde_json::to_vec(&policy).map_err(|error| {
        CuratorError::Deployment(format!("cannot encode compiled PoA policy: {error}"))
    })
}

fn verify_production_policy(policy: Option<&Value>) -> Result<(), CuratorError> {
    let expected: Value =
        serde_json::from_str(POA_PRODUCTION_POLICY_CANONICAL).map_err(|error| {
            CuratorError::Deployment(format!("invalid compiled PoA policy: {error}"))
        })?;
    if policy != Some(&expected) {
        return Err(CuratorError::Deployment(
            "public manifest carries an unknown or weakened PoA operator policy".into(),
        ));
    }
    Ok(())
}

fn derive_signal_deployment_digest(
    deployment_id: &str,
    manifest_sha256: &str,
    policy_sha256: &str,
) -> String {
    let preimage = format!(
        "{POA_SIGNAL_DEPLOYMENT_IDENTITY_DOMAIN}\0{deployment_id}\0{manifest_sha256}\0{policy_sha256}"
    );
    hex_encode(&sha256_raw(preimage.as_bytes()))
}

fn manifest_hex32(
    object: &serde_json::Map<String, Value>,
    field: &'static str,
) -> Result<String, CuratorError> {
    let value = object
        .get(field)
        .and_then(Value::as_str)
        .ok_or_else(|| CuratorError::Deployment(format!("{field} is absent")))?;
    parse_hex_array::<32>(value, field)?;
    Ok(value.to_owned())
}

fn paths_overlap(left: &Path, right: &Path) -> bool {
    left.starts_with(right) || right.starts_with(left)
}

fn verify_genesis_economy_and_committee(
    genesis: &serde_json::Map<String, Value>,
    federation_id: &str,
    committee_epoch: u64,
    threshold: u64,
) -> Result<Vec<ValidatorIdentity>, CuratorError> {
    require_exact_object_keys(
        genesis,
        &[
            "checkpoint_interval",
            "committee_epoch",
            "consensus_genesis_unix_seconds",
            "consensus_time_mode",
            "deployment_domain",
            "epoch_length",
            "federation_id",
            "fee_well",
            "genesis_moves",
            "initial_cells",
            "issuer_well",
            "threshold",
            "validators",
        ],
        "PoA genesis.json",
    )
    .map_err(CuratorError::Deployment)?;
    let values = genesis
        .get("validators")
        .and_then(Value::as_array)
        .filter(|values| !values.is_empty())
        .ok_or_else(|| CuratorError::Deployment("genesis validators are absent".into()))?;
    let expected_threshold = values.len() - values.len().saturating_sub(1) / 3;
    if threshold as usize != expected_threshold {
        return Err(CuratorError::Deployment(format!(
            "genesis threshold {threshold} is not the full BFT threshold {expected_threshold}"
        )));
    }

    let mut ed_seen = BTreeSet::new();
    let mut ml_seen = BTreeSet::new();
    let mut hybrid_seen = BTreeSet::new();
    let mut validators = Vec::with_capacity(values.len());
    for (index, value) in values.iter().enumerate() {
        let validator = value.as_object().ok_or_else(|| {
            CuratorError::Deployment(format!("genesis validator {index} is not an object"))
        })?;
        require_exact_object_keys(
            validator,
            &[
                "name",
                "public_key",
                "xmss_root",
                "ml_dsa_public_key",
                "hybrid_id",
            ],
            "genesis validator",
        )
        .map_err(CuratorError::Deployment)?;
        if validator.get("name").and_then(Value::as_str) != Some(&format!("node-{index}")) {
            return Err(CuratorError::Deployment(format!(
                "genesis validator {index} has a non-canonical name"
            )));
        }
        let public_key = validator
            .get("public_key")
            .and_then(Value::as_str)
            .ok_or_else(|| CuratorError::Deployment("validator public_key is absent".into()))?;
        let public_key_bytes = parse_hex_array::<32>(public_key, "validator.public_key")?;
        let xmss = validator
            .get("xmss_root")
            .and_then(Value::as_str)
            .ok_or_else(|| CuratorError::Deployment("validator xmss_root is absent".into()))?;
        parse_hex_array::<32>(xmss, "validator.xmss_root")?;
        let ml_hex = validator
            .get("ml_dsa_public_key")
            .and_then(Value::as_str)
            .ok_or_else(|| CuratorError::Deployment("validator ML-DSA key is absent".into()))?;
        let ml_dsa_public_key =
            parse_lower_hex(ml_hex, ML_DSA_65_PUBLIC_KEY_BYTES, "validator ML-DSA key")?;
        let declared_hybrid = validator
            .get("hybrid_id")
            .and_then(Value::as_str)
            .ok_or_else(|| CuratorError::Deployment("validator hybrid_id is absent".into()))?;
        let declared_hybrid = parse_hex_array::<32>(declared_hybrid, "validator.hybrid_id")?;
        let derived_hybrid =
            dregg_types::hybrid_id_commitment(&public_key_bytes, &ml_dsa_public_key);
        if declared_hybrid != derived_hybrid {
            return Err(CuratorError::Deployment(format!(
                "genesis validator {index} hybrid_id does not bind its Ed25519+ML-DSA keys"
            )));
        }
        if !ed_seen.insert(public_key_bytes)
            || !ml_seen.insert(ml_dsa_public_key.clone())
            || !hybrid_seen.insert(derived_hybrid)
        {
            return Err(CuratorError::Deployment(
                "genesis committee contains duplicate Ed25519, ML-DSA, or hybrid identities".into(),
            ));
        }
        validators.push(ValidatorIdentity {
            public_key: public_key.to_owned(),
            hybrid_id: derived_hybrid,
        });
    }
    let derived_federation = derive_hybrid_federation_id(&validators, committee_epoch);
    if hex_encode(&derived_federation) != federation_id {
        return Err(CuratorError::Deployment(
            "declared federation_id does not match the exact hybrid committee and epoch".into(),
        ));
    }

    let initial = genesis
        .get("initial_cells")
        .and_then(Value::as_array)
        .filter(|cells| cells.len() == 2)
        .ok_or_else(|| {
            CuratorError::Deployment(
                "PoA genesis must contain exactly its issuer and fee wells".into(),
            )
        })?;
    let mut initial_ids = BTreeSet::new();
    let mut initial_public = BTreeSet::new();
    for (index, value) in initial.iter().enumerate() {
        let cell = value.as_object().ok_or_else(|| {
            CuratorError::Deployment(format!("initial cell {index} is not an object"))
        })?;
        require_exact_object_keys(
            cell,
            &[
                "id",
                "public_key",
                "token_id",
                "balance",
                "ml_dsa_public_key",
            ],
            "PoA initial cell",
        )
        .map_err(CuratorError::Deployment)?;
        let id = manifest_value_hex32(cell, "id", "initial_cell.id")?;
        let public = manifest_value_hex32(cell, "public_key", "initial_cell.public_key")?;
        manifest_value_hex32(cell, "token_id", "initial_cell.token_id")?;
        let ml = cell
            .get("ml_dsa_public_key")
            .and_then(Value::as_str)
            .ok_or_else(|| CuratorError::Deployment("initial cell ML-DSA key is absent".into()))?;
        parse_lower_hex(ml, ML_DSA_65_PUBLIC_KEY_BYTES, "initial cell ML-DSA key")?;
        if cell.get("balance").and_then(Value::as_u64) != Some(0)
            || !initial_ids.insert(id)
            || !initial_public.insert(public)
        {
            return Err(CuratorError::Deployment(
                "PoA initial wells must be distinct and carry zero generic value".into(),
            ));
        }
    }
    let issuer = manifest_value_hex32(genesis, "issuer_well", "issuer_well")?;
    let fee = manifest_value_hex32(genesis, "fee_well", "fee_well")?;
    if issuer == fee || !initial_ids.contains(&issuer) || !initial_ids.contains(&fee) {
        return Err(CuratorError::Deployment(
            "issuer_well/fee_well do not name the two exact initial cells".into(),
        ));
    }
    if genesis
        .get("genesis_moves")
        .and_then(Value::as_array)
        .is_none_or(|moves| !moves.is_empty())
        || genesis
            .get("starbridge_cells")
            .is_some_and(|value| value.as_array().is_none_or(|cells| !cells.is_empty()))
    {
        return Err(CuratorError::Deployment(
            "PoA genesis must have no generic moves or Starbridge demo catalog".into(),
        ));
    }
    Ok(validators)
}

fn derive_hybrid_federation_id(validators: &[ValidatorIdentity], committee_epoch: u64) -> [u8; 32] {
    let mut ids: Vec<[u8; 32]> = validators
        .iter()
        .map(|validator| validator.hybrid_id)
        .collect();
    ids.sort();
    let mut hasher = blake3::Hasher::new_derive_key(FEDERATION_ID_DOMAIN);
    hasher.update(&(ids.len() as u64).to_le_bytes());
    for id in ids {
        hasher.update(&id);
    }
    hasher.update(&committee_epoch.to_le_bytes());
    *hasher.finalize().as_bytes()
}

fn verify_public_topology(
    manifest: &serde_json::Map<String, Value>,
    validators: &[ValidatorIdentity],
) -> Result<Vec<PoaNodeScope>, CuratorError> {
    let values = manifest
        .get("nodes")
        .and_then(Value::as_array)
        .ok_or_else(|| CuratorError::Deployment("manifest nodes are absent".into()))?;
    if values.len() != validators.len() {
        return Err(CuratorError::Deployment(
            "manifest/genesis committee cardinality is inconsistent".into(),
        ));
    }
    let mut nodes = Vec::with_capacity(values.len());
    let mut ports = BTreeSet::new();
    let mut hosts = Vec::with_capacity(values.len());
    for (index, value) in values.iter().enumerate() {
        let node = value.as_object().ok_or_else(|| {
            CuratorError::Deployment(format!("manifest node {index} is not an object"))
        })?;
        require_exact_object_keys(
            node,
            &["index", "name", "public_key", "data_dir", "http", "gossip"],
            "manifest node",
        )
        .map_err(CuratorError::Deployment)?;
        if node.get("index").and_then(Value::as_u64) != Some(index as u64)
            || node.get("name").and_then(Value::as_str) != Some(&format!("node-{index}"))
            || node.get("public_key").and_then(Value::as_str)
                != Some(validators[index].public_key.as_str())
        {
            return Err(CuratorError::Deployment(format!(
                "manifest node {index} differs from the ordered genesis committee"
            )));
        }
        let data_dir = format!("nodes/node-{index}");
        if node.get("data_dir").and_then(Value::as_str) != Some(data_dir.as_str()) {
            return Err(CuratorError::Deployment(format!(
                "manifest node {index} data_dir is not canonical"
            )));
        }
        let http = exact_child_object(node, "http", &["bind", "port"])?;
        let http_bind = http.get("bind").and_then(Value::as_str).unwrap_or_default();
        let http_port = valid_port(http.get("port"), "manifest HTTP port")?;
        if http_bind != "127.0.0.1" {
            return Err(CuratorError::Deployment(
                "PoA public HTTP endpoint must bind 127.0.0.1".into(),
            ));
        }
        let gossip = exact_child_object(node, "gossip", &["advertised_host", "port", "peers"])?;
        let gossip_host = gossip
            .get("advertised_host")
            .and_then(Value::as_str)
            .filter(|host| valid_advertised_host(host))
            .ok_or_else(|| CuratorError::Deployment("invalid advertised gossip host".into()))?;
        let gossip_port = valid_port(gossip.get("port"), "manifest gossip port")?;
        if !ports.insert(http_port) || !ports.insert(gossip_port) {
            return Err(CuratorError::Deployment(
                "public HTTP and gossip ports overlap".into(),
            ));
        }
        let peers = gossip
            .get("peers")
            .and_then(Value::as_array)
            .ok_or_else(|| CuratorError::Deployment("manifest gossip peers are absent".into()))?
            .iter()
            .map(|peer| {
                peer.as_str()
                    .map(str::to_owned)
                    .ok_or_else(|| CuratorError::Deployment("gossip peer is not a string".into()))
            })
            .collect::<Result<Vec<_>, _>>()?;
        hosts.push(gossip_host.to_owned());
        nodes.push(PoaNodeScope {
            index,
            public_key: validators[index].public_key.clone(),
            data_dir,
            http_bind: http_bind.to_owned(),
            http_port,
            gossip_host: gossip_host.to_owned(),
            gossip_port,
            gossip_peers: peers,
        });
    }
    let http_base = nodes.first().map(|node| node.http_port).unwrap_or(0);
    let gossip_base = nodes.first().map(|node| node.gossip_port).unwrap_or(0);
    let distinct_hosts: BTreeSet<_> = hosts.iter().collect();
    if distinct_hosts.len() > 1 && hosts.iter().any(|host| is_loopback_host(host)) {
        return Err(CuratorError::Deployment(
            "multi-host topology advertises a loopback address".into(),
        ));
    }
    for (index, node) in nodes.iter().enumerate() {
        if u32::from(node.http_port) != u32::from(http_base) + index as u32
            || u32::from(node.gossip_port) != u32::from(gossip_base) + index as u32
        {
            return Err(CuratorError::Deployment(
                "manifest endpoint ranges are not consecutive".into(),
            ));
        }
        let expected: Vec<String> = hosts
            .iter()
            .enumerate()
            .filter(|(peer, _)| *peer != index)
            .map(|(peer, host)| format!("{host}:{}", u32::from(gossip_base) + peer as u32))
            .collect();
        if node.gossip_peers != expected {
            return Err(CuratorError::Deployment(format!(
                "manifest node {index} gossip peers are not the exact advertised mesh"
            )));
        }
    }
    Ok(nodes)
}

fn exact_child_object<'a>(
    parent: &'a serde_json::Map<String, Value>,
    field: &str,
    keys: &[&str],
) -> Result<&'a serde_json::Map<String, Value>, CuratorError> {
    let child = parent
        .get(field)
        .and_then(Value::as_object)
        .ok_or_else(|| CuratorError::Deployment(format!("{field} is not an object")))?;
    require_exact_object_keys(child, keys, field).map_err(CuratorError::Deployment)?;
    Ok(child)
}

fn valid_port(value: Option<&Value>, label: &str) -> Result<u16, CuratorError> {
    let port = value
        .and_then(Value::as_u64)
        .filter(|port| (1024..=65535).contains(port));
    port.map(|port| port as u16)
        .ok_or_else(|| CuratorError::Deployment(format!("{label} is outside 1024..65535")))
}

fn valid_advertised_host(host: &str) -> bool {
    !host.is_empty()
        && host
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'-'))
}

fn is_loopback_host(host: &str) -> bool {
    host == "localhost" || host == "127.0.0.1" || host.starts_with("127.")
}

fn manifest_value_hex32(
    object: &serde_json::Map<String, Value>,
    key: &str,
    label: &'static str,
) -> Result<[u8; 32], CuratorError> {
    let value = object
        .get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| CuratorError::Deployment(format!("{key} is absent")))?;
    parse_hex_array::<32>(value, label)
}

fn parse_lower_hex(value: &str, bytes: usize, label: &str) -> Result<Vec<u8>, CuratorError> {
    if value.len() != bytes * 2
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(CuratorError::Deployment(format!(
            "{label} is not exactly {bytes} lowercase bytes"
        )));
    }
    Ok(value
        .as_bytes()
        .chunks_exact(2)
        .map(|pair| (hex_nibble(pair[0]) << 4) | hex_nibble(pair[1]))
        .collect())
}

fn verify_main_identity_isolation(
    poa_root: &Path,
    main_root: &Path,
    poa_genesis: &serde_json::Map<String, Value>,
) -> Result<(), CuratorError> {
    if poa_root.join("bundle/faucet.key").exists() {
        return Err(CuratorError::Deployment(
            "PoA empty-economy genesis must not emit a faucet key".into(),
        ));
    }
    let main_genesis_path = main_root.join("genesis.json");
    if main_genesis_path.exists() {
        let bytes = read_regular_bounded(&main_genesis_path, MAX_ARTIFACT_BYTES)?;
        let main = parse_strict_json(&bytes).map_err(|reason| CuratorError::Json {
            path: main_genesis_path,
            reason,
        })?;
        let main = main
            .as_object()
            .ok_or_else(|| CuratorError::Deployment("main genesis is not an object".into()))?;
        if main.get("federation_id").and_then(Value::as_str)
            == poa_genesis.get("federation_id").and_then(Value::as_str)
        {
            return Err(CuratorError::Deployment(
                "PoA federation identity is copied from the main federation".into(),
            ));
        }
        let poa_public = genesis_public_identities(poa_genesis);
        let main_public = genesis_public_identities(main);
        if !poa_public.is_disjoint(&main_public) {
            return Err(CuratorError::Deployment(
                "PoA validator or well identity is reused by the main genesis".into(),
            ));
        }
    }
    let poa_keys = collect_key_digests(&poa_root.join("bundle"))?;
    let main_keys = collect_key_digests(main_root)?;
    if !poa_keys.is_disjoint(&main_keys) {
        return Err(CuratorError::Deployment(
            "PoA key bytes are reused from the main data directory".into(),
        ));
    }
    Ok(())
}

fn genesis_public_identities(genesis: &serde_json::Map<String, Value>) -> BTreeSet<String> {
    ["validators", "initial_cells"]
        .into_iter()
        .filter_map(|field| genesis.get(field).and_then(Value::as_array))
        .flatten()
        .filter_map(|row| row.get("public_key").and_then(Value::as_str))
        .map(str::to_owned)
        .collect()
}

fn collect_key_digests(root: &Path) -> Result<BTreeSet<[u8; 32]>, CuratorError> {
    fn visit(path: &Path, output: &mut BTreeSet<[u8; 32]>) -> Result<(), CuratorError> {
        if !path.exists() {
            return Ok(());
        }
        for entry in fs::read_dir(path).map_err(|error| io_error(path, error))? {
            let entry = entry.map_err(|error| io_error(path, error))?;
            let ty = entry
                .file_type()
                .map_err(|error| io_error(&entry.path(), error))?;
            if ty.is_symlink() {
                continue;
            }
            if ty.is_dir() {
                visit(&entry.path(), output)?;
            } else if ty.is_file()
                && entry.path().extension().and_then(|value| value.to_str()) == Some("key")
            {
                let bytes = read_regular_bounded(&entry.path(), 4096)?;
                if bytes.len() == 32 {
                    output.insert(sha256_raw(&bytes));
                }
            }
        }
        Ok(())
    }
    let mut output = BTreeSet::new();
    visit(root, &mut output)?;
    Ok(output)
}

fn operator_config(
    scope: &PoaDeploymentScope,
    verified: &VerifiedDeploymentArtifacts,
    node: &PoaNodeScope,
) -> String {
    let data_dir = verified.root.join(&node.data_dir);
    format!(
        "POA_DEPLOYMENT_DOMAIN={}\nPOA_DEPLOYMENT_ID={}\nPOA_FEDERATION_ID={}\nPOA_NODE_INDEX={}\nPOA_DATA_DIR={}\nPOA_HTTP_BIND={}\nPOA_HTTP_PORT={}\nPOA_GOSSIP_PORT={}\nPOA_GOSSIP_HOST={}\nPOA_FEDERATION_PEERS={}\nPOA_PROVE_TURNS=1\nPOA_ENABLE_FAUCET=0\nPOA_AUTO_APPROVE_JOINS=0\nDREGG_REQUIRE_LEAN=1\nDREGG_STRAND_ADMISSION_GATE=1\nDREGG_ALLOW_UNVERIFIED_CONSENSUS=0\nDREGG_STATUS_EXPOSE_COUNTS=0\nDREGG_SEED_DEMO_LEASE=0\n",
        POA_DEPLOYMENT_DOMAIN,
        scope.deployment_id,
        scope.federation_id,
        node.index,
        data_dir.display(),
        node.http_bind,
        node.http_port,
        node.gossip_port,
        node.gossip_host,
        node.gossip_peers.join(","),
    )
}

/// A content bundle whose mission federation has been compared with the
/// independently generated PoA deployment descriptor.
#[derive(Clone, Debug)]
pub struct DeploymentBoundBundle<'a> {
    bundle: &'a Poag1Bundle,
    deployment: PoaDeploymentScope,
}

impl DeploymentBoundBundle<'_> {
    pub fn bundle(&self) -> &Poag1Bundle {
        self.bundle
    }

    pub fn deployment(&self) -> &PoaDeploymentScope {
        &self.deployment
    }

    /// Project an authenticated but unsigned work-in-progress epoch for human
    /// review. This never searches for an adjacent signature and cannot imply
    /// activation.
    pub fn unsigned_epoch_preview(&self) -> Result<EpochPreview, CuratorError> {
        self.build_epoch_preview(None)
    }

    fn build_epoch_preview(
        &self,
        verified: Option<&ContentEpochEnvelope>,
    ) -> Result<EpochPreview, CuratorError> {
        let mut missions = Vec::with_capacity(self.bundle.missions.len());
        for (&mission_id, mission) in &self.bundle.missions {
            let exact = mission.exact_json.as_object().ok_or_else(|| {
                CuratorError::Catalog(format!("mission {mission_id} is not an object"))
            })?;
            let descriptor_path = preview_string(exact, mission_id, "descriptor_path")?;
            let descriptor = self
                .bundle
                .game_descriptors
                .get(descriptor_path)
                .and_then(Value::as_object)
                .ok_or_else(|| {
                    CuratorError::Catalog(format!(
                        "mission {mission_id} has no authenticated descriptor object"
                    ))
                })?;
            let content_visibility = match descriptor.get("security") {
                None => None,
                Some(security) => {
                    let security = security.as_object().ok_or_else(|| {
                        CuratorError::Catalog(format!(
                            "mission {mission_id} descriptor security is not an object"
                        ))
                    })?;
                    let visibility = security
                        .get("target_visibility")
                        .and_then(Value::as_str)
                        .filter(|value| !value.is_empty())
                        .ok_or_else(|| {
                            CuratorError::Catalog(format!(
                                "mission {mission_id} descriptor security lacks target_visibility"
                            ))
                        })?;
                    Some(visibility.to_owned())
                }
            };
            let budget = exact
                .get("budget")
                .and_then(Value::as_object)
                .ok_or_else(|| {
                    CuratorError::Catalog(format!("mission {mission_id} budget is not an object"))
                })?;
            let allowed_relics = exact
                .get("allowed_relics")
                .and_then(Value::as_array)
                .ok_or_else(|| {
                    CuratorError::Catalog(format!(
                        "mission {mission_id} allowed_relics is not an array"
                    ))
                })?
                .iter()
                .map(|value| {
                    value.as_u64().ok_or_else(|| {
                        CuratorError::Catalog(format!(
                            "mission {mission_id} has a non-u64 allowed relic"
                        ))
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;
            missions.push(MissionPreview {
                mission_id,
                title: preview_string(exact, mission_id, "title")?.to_owned(),
                ruleset: preview_string(exact, mission_id, "ruleset")?.to_owned(),
                action_cap: preview_u64(exact, mission_id, "action_limit")?,
                privacy_grade: preview_string(exact, mission_id, "privacy_grade")?.to_owned(),
                reward_class: preview_string(exact, mission_id, "reward_class")?.to_owned(),
                budget: MissionBudgetPreview {
                    intel: preview_u64(budget, mission_id, "intel")?,
                    supplies: preview_u64(budget, mission_id, "supplies")?,
                    cohesion: preview_u64(budget, mission_id, "cohesion")?,
                    influence: preview_u64(budget, mission_id, "influence")?,
                    score: preview_u64(budget, mission_id, "score")?,
                    relics: preview_u64(budget, mission_id, "relics")?,
                },
                allowed_relics,
                beta_artifacts: mission.allowed_beta_discoveries.clone(),
                descriptor_path: descriptor_path.to_owned(),
                content_visibility,
            });
        }

        let (signature_status, signature_epoch, signature_counter, notice) = match verified {
            None => (
                EpochPreviewSignatureStatus::Absent,
                None,
                None,
                "UNSIGNED WIP: no detached signature was supplied or verified; this preview is not an activation",
            ),
            Some(envelope) => (
                EpochPreviewSignatureStatus::Valid,
                Some(envelope.content_epoch),
                Some(envelope.counter),
                "SIGNATURE VERIFIED: this review preview is not a Lean mission activation",
            ),
        };
        Ok(EpochPreview {
            schema: POA_EPOCH_PREVIEW_SCHEMA.into(),
            manifest_sha256: self.bundle.manifest_sha256.clone(),
            source_digest: self.bundle.manifest.source_digest.clone(),
            content_root: self.bundle.content_root.clone(),
            content_epoch: self.bundle.content_epoch,
            deployment_id: self.deployment.deployment_id.clone(),
            federation_id: self.deployment.federation_id.clone(),
            signature_status,
            signature_epoch,
            signature_counter,
            notice: notice.into(),
            missions,
        })
    }
}

fn preview_string<'a>(
    object: &'a serde_json::Map<String, Value>,
    mission_id: u64,
    field: &str,
) -> Result<&'a str, CuratorError> {
    object.get(field).and_then(Value::as_str).ok_or_else(|| {
        CuratorError::Catalog(format!("mission {mission_id} {field} is not a string"))
    })
}

fn preview_u64(
    object: &serde_json::Map<String, Value>,
    mission_id: u64,
    field: &str,
) -> Result<u64, CuratorError> {
    object
        .get(field)
        .and_then(Value::as_u64)
        .ok_or_else(|| CuratorError::Catalog(format!("mission {mission_id} {field} is not a u64")))
}

#[derive(Clone, Debug)]
struct MissionIndex {
    exact_json: Value,
    federation_id: String,
    content_root: String,
    content_session: String,
    run_seed: String,
    allowed_beta_discoveries: Vec<ArtifactRef>,
}

#[derive(Clone, Debug)]
struct FixtureIndex {
    mission_id: u64,
    base_world: Value,
    contribution: Value,
    preview_world: Value,
}

struct CatalogIndex {
    missions: BTreeMap<u64, MissionIndex>,
    fixtures: BTreeMap<String, FixtureIndex>,
    content_epoch: u64,
}

impl Poag1Bundle {
    /// Load and authenticate every byte named by a POAG1 v1 manifest.
    pub fn load(manifest_path: impl AsRef<Path>) -> Result<Self, CuratorError> {
        let manifest_path = manifest_path.as_ref().to_path_buf();
        let manifest_bytes = read_regular_bounded(&manifest_path, MAX_MANIFEST_BYTES)?;
        let manifest_value =
            parse_strict_json(&manifest_bytes).map_err(|reason| CuratorError::Json {
                path: manifest_path.clone(),
                reason,
            })?;
        let manifest: Poag1Manifest =
            serde_json::from_value(manifest_value).map_err(|e| CuratorError::Json {
                path: manifest_path.clone(),
                reason: e.to_string(),
            })?;
        let game_paths = validate_manifest(&manifest)?;

        let root = manifest_path.parent().ok_or_else(|| {
            CuratorError::Manifest("manifest path has no containing directory".into())
        })?;
        let canonical_root = fs::canonicalize(root).map_err(|e| io_error(root, e))?;

        let mut artifacts = BTreeMap::new();
        for pin in &manifest.artifacts {
            let artifact_path = root.join(&pin.path);
            let lexical_metadata = fs::symlink_metadata(&artifact_path)
                .map_err(|error| io_error(&artifact_path, error))?;
            if lexical_metadata.file_type().is_symlink() || !lexical_metadata.is_file() {
                return Err(CuratorError::Artifact {
                    path: pin.path.clone(),
                    reason: "manifest artifact is not a regular non-symlink file".into(),
                });
            }
            let canonical =
                fs::canonicalize(&artifact_path).map_err(|e| io_error(&artifact_path, e))?;
            if !canonical.starts_with(&canonical_root) {
                return Err(CuratorError::Artifact {
                    path: pin.path.clone(),
                    reason: "canonical path escapes the manifest directory".into(),
                });
            }
            // Open the canonicalized path itself. Combined with `O_NOFOLLOW`
            // in `read_regular_bounded`, this closes the final-component
            // symlink swap between containment checking and opening.
            let bytes = read_regular_bounded(&canonical, MAX_ARTIFACT_BYTES)?;
            if bytes.len() as u64 != pin.bytes {
                return Err(CuratorError::Artifact {
                    path: pin.path.clone(),
                    reason: format!("byte length {} != pinned {}", bytes.len(), pin.bytes),
                });
            }
            let actual_sha = sha256_tagged(&bytes);
            if actual_sha != pin.sha256 {
                return Err(CuratorError::Artifact {
                    path: pin.path.clone(),
                    reason: format!("SHA-256 {actual_sha} != pinned {}", pin.sha256),
                });
            }
            let actual_fnv = fnv1a64_hex(&bytes);
            if actual_fnv != pin.fnv1a64 {
                return Err(CuratorError::Artifact {
                    path: pin.path.clone(),
                    reason: format!("FNV-1a {actual_fnv} != pinned {}", pin.fnv1a64),
                });
            }
            artifacts.insert(pin.path.clone(), bytes);
        }

        let schema = parse_artifact_json(&manifest_path, &artifacts, SCHEMA_PATH, "POAG1-SCHEMA")?;
        validate_schema_contract(&schema, &game_paths)?;
        let catalog =
            parse_artifact_json(&manifest_path, &artifacts, CATALOG_PATH, "POAG1-CATALOG")?;
        let mut game_descriptors = BTreeMap::new();
        let mut descriptor_digests = BTreeMap::new();
        for path in &game_paths {
            let descriptor = parse_artifact_json(&manifest_path, &artifacts, path, "POAG1-GAME")?;
            game_descriptors.insert(path.clone(), descriptor);
            descriptor_digests.insert(
                path.clone(),
                sha256_tagged(
                    artifacts
                        .get(path)
                        .expect("validated manifest path was loaded"),
                ),
            );
        }
        let content_root = content_root_v1(&artifacts, &game_paths)?;
        let index = index_catalog(
            &catalog,
            &content_root,
            &manifest.source_digest,
            &game_descriptors,
            &descriptor_digests,
        )?;

        Ok(Self {
            manifest_path,
            manifest_sha256: sha256_tagged(&manifest_bytes),
            manifest_bytes,
            manifest,
            artifacts,
            schema,
            catalog,
            game_descriptors,
            content_root,
            content_epoch: index.content_epoch,
            missions: index.missions,
            fixtures: index.fixtures,
        })
    }

    pub fn manifest_path(&self) -> &Path {
        &self.manifest_path
    }

    pub fn manifest_bytes(&self) -> &[u8] {
        &self.manifest_bytes
    }

    pub fn manifest_sha256(&self) -> &str {
        &self.manifest_sha256
    }

    pub fn manifest(&self) -> &Poag1Manifest {
        &self.manifest
    }

    pub fn schema(&self) -> &Value {
        &self.schema
    }

    pub fn catalog(&self) -> &Value {
        &self.catalog
    }

    pub fn signal_triangulation(&self) -> &Value {
        self.game_descriptors
            .get(SIGNAL_PATH)
            .expect("Signal is required in every POAG1 v1 epoch")
    }

    pub fn game_descriptor(&self, path: &str) -> Option<&Value> {
        self.game_descriptors.get(path)
    }

    pub fn game_paths(&self) -> impl ExactSizeIterator<Item = &str> {
        self.game_descriptors.keys().map(String::as_str)
    }

    pub fn content_root(&self) -> &str {
        &self.content_root
    }

    pub fn content_epoch(&self) -> u64 {
        self.content_epoch
    }

    pub fn artifact_bytes(&self, path: &str) -> Option<&[u8]> {
        self.artifacts.get(path).map(Vec::as_slice)
    }

    /// Bind every emitted mission to the fresh federation recorded by the
    /// deployment kit. Content signing and runtime activation require the
    /// returned token, preventing a plausible-but-wrong catalog federation
    /// from being signed accidentally.
    pub fn bind_deployment(
        &self,
        deployment_manifest: impl AsRef<Path>,
    ) -> Result<DeploymentBoundBundle<'_>, CuratorError> {
        let deployment = PoaDeploymentScope::load(deployment_manifest)?;
        self.bind_deployment_scope(deployment)
    }

    /// Bind to a deployment scope already verified by the caller's required
    /// ceremony (normally [`PoaDeploymentScope::load_verified`]).
    pub fn bind_deployment_scope(
        &self,
        deployment: PoaDeploymentScope,
    ) -> Result<DeploymentBoundBundle<'_>, CuratorError> {
        if self.missions.is_empty() {
            return Err(CuratorError::Deployment(
                "authenticated catalog contains no missions".into(),
            ));
        }
        for (mission_id, mission) in &self.missions {
            if mission.federation_id != deployment.federation_id {
                return Err(CuratorError::Deployment(format!(
                    "mission {mission_id} federation {} != deployed federation {}",
                    mission.federation_id, deployment.federation_id
                )));
            }
        }
        Ok(DeploymentBoundBundle {
            bundle: self,
            deployment,
        })
    }

    /// Select a MissionSpec, exact beta discoveries, and an optional bounded
    /// preview from authenticated Lean output. No semantic delta is calculated
    /// in this function.
    pub fn prepare_mission(
        &self,
        mission_id: u64,
        discoveries: &[ArtifactRef],
        fixture_id: Option<&str>,
    ) -> Result<CuratorDraft, CuratorError> {
        let mission = self
            .missions
            .get(&mission_id)
            .ok_or(CuratorError::UnknownMission(mission_id))?;

        let mut seen = BTreeSet::new();
        for artifact in discoveries {
            artifact.validate()?;
            if !seen.insert(artifact.clone()) {
                return Err(CuratorError::DuplicateDiscovery);
            }
            if !mission.allowed_beta_discoveries.contains(artifact) {
                return Err(CuratorError::DiscoveryNotAllowed {
                    mission_id,
                    artifact: artifact.clone(),
                });
            }
        }

        let preview = fixture_id
            .map(|id| {
                let fixture = self
                    .fixtures
                    .get(id)
                    .ok_or_else(|| CuratorError::UnknownFixture(id.to_owned()))?;
                if fixture.mission_id != mission_id {
                    return Err(CuratorError::Catalog(format!(
                        "fixture {id} belongs to mission {}, not {mission_id}",
                        fixture.mission_id
                    )));
                }
                Ok(EmittedPreview {
                    fixture_id: id.to_owned(),
                    base_world: fixture.base_world.clone(),
                    contribution: fixture.contribution.clone(),
                    preview_world: fixture.preview_world.clone(),
                })
            })
            .transpose()?;

        Ok(CuratorDraft {
            manifest_sha256: self.manifest_sha256.clone(),
            source_digest: self.manifest.source_digest.clone(),
            mission_id,
            mission_spec: mission.exact_json.clone(),
            predeclared_beta_discoveries: discoveries.to_vec(),
            preview,
        })
    }

    fn is_predeclared_beta_artifact(&self, artifact: &ArtifactRef) -> bool {
        self.missions
            .get(&artifact.mission_id)
            .is_some_and(|mission| mission.allowed_beta_discoveries.contains(artifact))
    }

    fn mission_scope(&self, mission_id: u64) -> Option<(&str, &str, &str)> {
        self.missions.get(&mission_id).map(|mission| {
            (
                mission.federation_id.as_str(),
                mission.content_root.as_str(),
                mission.content_session.as_str(),
            )
        })
    }
}

/// Public key pin distributed outside the fetched POAG1 bundle.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CuratorKeyPin {
    pub schema: String,
    pub curator_pubkey: String,
}

impl CuratorKeyPin {
    pub fn new(public_key: &PublicKey) -> Self {
        Self {
            schema: CURATOR_KEY_SCHEMA.into(),
            curator_pubkey: public_key.hex(),
        }
    }

    pub fn public_key(&self) -> Result<PublicKey, CuratorError> {
        if self.schema != CURATOR_KEY_SCHEMA {
            return Err(CuratorError::ContentEpoch(format!(
                "key-pin schema {} != {CURATOR_KEY_SCHEMA}",
                self.schema
            )));
        }
        Ok(PublicKey(parse_hex_array::<32>(
            &self.curator_pubkey,
            "curator_pubkey",
        )?))
    }

    /// Load the external pin from a regular non-symlink file. The path must be
    /// configured independently from the fetched POAG1 bundle.
    pub fn load(path: impl AsRef<Path>) -> Result<Self, CuratorError> {
        let path = path.as_ref();
        let bytes = read_regular_bounded(path, 16 * 1024)?;
        let pin: CuratorKeyPin =
            serde_json::from_slice(&bytes).map_err(|e| CuratorError::Json {
                path: path.to_path_buf(),
                reason: e.to_string(),
            })?;
        pin.public_key()?;
        Ok(pin)
    }
}

/// Detached signature over the exact POAG1 manifest bytes.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ContentEpochEnvelope {
    pub schema: String,
    pub manifest_sha256: String,
    pub curator_pubkey: String,
    pub content_epoch: u64,
    pub counter: u64,
    pub signature: String,
}

impl ContentEpochEnvelope {
    /// Load a detached envelope with duplicate-key and unknown-field refusal.
    pub fn load(path: impl AsRef<Path>) -> Result<Self, CuratorError> {
        let path = path.as_ref();
        let bytes = read_regular_bounded(path, 64 * 1024)?;
        let value = parse_strict_json(&bytes).map_err(|reason| CuratorError::Json {
            path: path.to_path_buf(),
            reason,
        })?;
        serde_json::from_value(value).map_err(|error| CuratorError::Json {
            path: path.to_path_buf(),
            reason: error.to_string(),
        })
    }

    /// Verify using an external key pin and exact expected epoch/counter. A
    /// caller must persist/advance the counter after acceptance.
    pub fn verify(
        &self,
        bound: &DeploymentBoundBundle<'_>,
        key_pin: &CuratorKeyPin,
        expected_epoch: u64,
        expected_counter: u64,
    ) -> Result<VerifiedContentEpoch<'_>, CuratorError> {
        let bundle = bound.bundle;
        if self.schema != CONTENT_EPOCH_SCHEMA {
            return Err(CuratorError::ContentEpoch(
                "unknown signature schema".into(),
            ));
        }
        if self.manifest_sha256 != bundle.manifest_sha256 {
            return Err(CuratorError::ContentEpoch(
                "manifest digest does not name the loaded exact bytes".into(),
            ));
        }
        if self.content_epoch != expected_epoch {
            return Err(CuratorError::ContentEpoch(format!(
                "content epoch {} != expected {expected_epoch}",
                self.content_epoch
            )));
        }
        if self.content_epoch != bundle.content_epoch {
            return Err(CuratorError::ContentEpoch(format!(
                "signed content epoch {} != authenticated catalog epoch {}",
                self.content_epoch, bundle.content_epoch
            )));
        }
        if self.counter != expected_counter {
            return Err(CuratorError::ContentEpoch(format!(
                "counter {} != expected {expected_counter}",
                self.counter
            )));
        }
        let pinned = key_pin.public_key()?;
        if self.curator_pubkey != pinned.hex() {
            return Err(CuratorError::ContentEpoch(
                "bundle-adjacent curator key differs from external pin".into(),
            ));
        }
        let signature = Signature(parse_hex_array::<64>(&self.signature, "signature")?);
        let message = content_epoch_signing_message(
            self.content_epoch,
            self.counter,
            bundle.manifest_bytes(),
        );
        if !dregg_types::verify(&pinned, &message, &signature) {
            return Err(CuratorError::BadSignature);
        }
        Ok(VerifiedContentEpoch {
            envelope: self,
            pinned_key: pinned,
            signed_digest: self.signed_digest()?,
        })
    }

    /// Digest used by a canon decision to bind this exact signed content epoch.
    pub fn signed_digest(&self) -> Result<[u8; 32], CuratorError> {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(ACTIVATION_DIGEST_DOMAIN);
        push_frame(&mut bytes, self.schema.as_bytes());
        bytes.extend_from_slice(&parse_sha256(&self.manifest_sha256, "manifest_sha256")?);
        bytes.extend_from_slice(&parse_hex_array::<32>(
            &self.curator_pubkey,
            "curator_pubkey",
        )?);
        bytes.extend_from_slice(&self.content_epoch.to_be_bytes());
        bytes.extend_from_slice(&self.counter.to_be_bytes());
        bytes.extend_from_slice(&parse_hex_array::<64>(&self.signature, "signature")?);
        Ok(sha256_raw(&bytes))
    }
}

/// Proof-by-construction that the detached envelope was checked against the
/// loaded exact bundle, external curator key, and caller-owned epoch/counter.
/// There is no public constructor; canon APIs require this token rather than a
/// merely well-shaped `ContentEpochEnvelope`.
#[derive(Clone, Debug)]
pub struct VerifiedContentEpoch<'a> {
    envelope: &'a ContentEpochEnvelope,
    pinned_key: PublicKey,
    signed_digest: [u8; 32],
}

impl VerifiedContentEpoch<'_> {
    pub fn envelope(&self) -> &ContentEpochEnvelope {
        self.envelope
    }

    pub fn public_key(&self) -> PublicKey {
        self.pinned_key
    }

    /// Exact detached activation digest consumed by the Lean mission runtime
    /// and `CanonAdmission`, encoded using the shared lowercase SHA-256 codec.
    pub fn activation_digest(&self) -> String {
        format!("sha256:{}", hex_encode(&self.signed_digest))
    }

    /// Project the same exact bundle as a signature-verified review document.
    /// The returned JSON remains descriptive and is not a Lean activation.
    pub fn epoch_preview(
        &self,
        bound: &DeploymentBoundBundle<'_>,
    ) -> Result<EpochPreview, CuratorError> {
        if self.envelope.manifest_sha256 != bound.bundle.manifest_sha256 {
            return Err(CuratorError::ContentEpoch(
                "verified signature does not name the previewed exact manifest bytes".into(),
            ));
        }
        if self.envelope.content_epoch != bound.bundle.content_epoch {
            return Err(CuratorError::ContentEpoch(
                "verified signature epoch does not name the previewed catalog epoch".into(),
            ));
        }
        bound.build_epoch_preview(Some(self.envelope))
    }

    /// Ask the live Lean adapter to admit the exact authenticated mission
    /// template hydrated with this detached activation. The returned token has
    /// no public constructor and is required by canon signing.
    pub fn activate_mission<'a>(
        &self,
        bound: &DeploymentBoundBundle<'a>,
        mission_id: u64,
        oracle: &impl MissionActivationOracle,
    ) -> Result<VerifiedMissionActivation<'a>, CuratorError> {
        let mission = bound
            .bundle
            .missions
            .get(&mission_id)
            .ok_or(CuratorError::UnknownMission(mission_id))?;
        let template_epoch = mission
            .exact_json
            .get("epoch")
            .and_then(Value::as_u64)
            .ok_or_else(|| CuratorError::Catalog(format!("mission {mission_id} lacks epoch")))?;
        if template_epoch != self.envelope.content_epoch {
            return Err(CuratorError::ContentEpoch(format!(
                "mission {mission_id} epoch {template_epoch} != signed content epoch {}",
                self.envelope.content_epoch
            )));
        }
        let activation = mission
            .exact_json
            .get("activation")
            .and_then(Value::as_object)
            .ok_or_else(|| {
                CuratorError::Catalog(format!("mission {mission_id} lacks activation marker"))
            })?;
        if activation.len() != 2
            || activation.get("state").and_then(Value::as_str)
                != Some("detached-signature-required")
            || activation.get("digest_source").and_then(Value::as_str) != Some(CONTENT_EPOCH_SCHEMA)
        {
            return Err(CuratorError::Catalog(format!(
                "mission {mission_id} activation marker is not the POAG1 v1 detached-signature contract"
            )));
        }
        let config = ActivatedMissionConfig {
            manifest_sha256: bound.bundle.manifest_sha256.clone(),
            deployment_id: bound.deployment.deployment_id.clone(),
            mission_template: mission.exact_json.clone(),
            mission_id,
            federation_id: mission.federation_id.clone(),
            content_root: mission.content_root.clone(),
            activation_digest: self.activation_digest(),
            content_session: mission.content_session.clone(),
            content_epoch: self.envelope.content_epoch,
            curator_key: self.pinned_key.hex(),
        };
        oracle.admit(&config).map_err(CuratorError::Activation)?;
        Ok(VerifiedMissionActivation {
            bundle: bound.bundle,
            config,
        })
    }
}

/// The complete runtime hydration request: the exact authenticated Lean-emitted
/// template plus only those fields that necessarily live outside its content
/// root. Adapters must ingest this object into Lean and issue the opaque
/// activation witness for this exact closed configuration.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct ActivatedMissionConfig {
    pub manifest_sha256: String,
    pub deployment_id: String,
    pub mission_template: Value,
    pub mission_id: u64,
    pub federation_id: String,
    pub content_root: String,
    pub activation_digest: String,
    pub content_session: String,
    pub content_epoch: u64,
    pub curator_key: String,
}

/// Live bridge to Lean's opaque activation witness. There is intentionally no
/// Rust fallback and no permissive implementation in this crate.
pub trait MissionActivationOracle {
    fn admit(&self, config: &ActivatedMissionConfig) -> Result<(), String>;
}

/// Proof-by-construction that Lean admitted this exact authenticated mission
/// configuration. Canon construction requires this token.
#[derive(Clone, Debug)]
pub struct VerifiedMissionActivation<'a> {
    bundle: &'a Poag1Bundle,
    config: ActivatedMissionConfig,
}

impl VerifiedMissionActivation<'_> {
    pub fn config(&self) -> &ActivatedMissionConfig {
        &self.config
    }
}

/// A signer supplied by an existing dregg key-custody surface. This wrapper
/// never reads, derives, exports, or persists key material.
pub struct CuratorSigner<'a> {
    key: &'a SigningKey,
}

impl<'a> CuratorSigner<'a> {
    pub fn new(key: &'a SigningKey) -> Self {
        Self { key }
    }

    pub fn public_key(&self) -> PublicKey {
        self.key.public_key()
    }

    pub fn sign_content_epoch(
        &self,
        bound: &DeploymentBoundBundle<'_>,
        content_epoch: u64,
        counter: u64,
    ) -> Result<ContentEpochEnvelope, CuratorError> {
        let bundle = bound.bundle;
        if content_epoch != bundle.content_epoch {
            return Err(CuratorError::ContentEpoch(format!(
                "requested content epoch {content_epoch} != authenticated catalog epoch {}",
                bundle.content_epoch
            )));
        }
        let message =
            content_epoch_signing_message(content_epoch, counter, bundle.manifest_bytes());
        let signature = dregg_types::sign(self.key, &message);
        Ok(ContentEpochEnvelope {
            schema: CONTENT_EPOCH_SCHEMA.into(),
            manifest_sha256: bundle.manifest_sha256.clone(),
            curator_pubkey: self.key.public_key().hex(),
            content_epoch,
            counter,
            signature: hex_encode(&signature.0),
        })
    }

    pub fn sign_canon_decision(
        &self,
        decision: CanonDecision,
        admission: &impl CanonAdmissionOracle,
    ) -> Result<SignedCanonDecision, CuratorError> {
        admission
            .admit(&decision)
            .map_err(CuratorError::CanonAdmission)?;
        let signature = dregg_types::sign(self.key, &decision.signing_message());
        Ok(SignedCanonDecision {
            decision,
            curator_pubkey: self.key.public_key().hex(),
            signature: hex_encode(&signature.0),
        })
    }
}

/// Exact canon operation. Supersession marks the exact target superseded; a
/// replacement, if any, is promoted by a distinct decision and receipt.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CanonAction {
    Promote,
    Supersede,
}

/// Exact runtime projection of Lean's `CanonAdmission`. These fields, in this
/// order, are the admission state the curator signature binds.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CanonAdmission {
    pub federation_id: String,
    pub content_root: String,
    pub activation_digest: String,
    pub content_session: String,
    pub content_epoch: u64,
    pub curator_key: String,
    pub expected_revision: u64,
    pub previous_curator_counter: u64,
    pub curator_counter: u64,
}

impl CanonAdmission {
    fn validate_shape(&self) -> Result<(), CuratorError> {
        parse_hex_array::<32>(&self.federation_id, "federation_id")?;
        parse_sha256(&self.content_root, "content_root")?;
        parse_sha256(&self.activation_digest, "activation_digest")?;
        parse_hex_array::<32>(&self.content_session, "content_session")?;
        parse_hex_array::<32>(&self.curator_key, "curator_key")?;
        if self.previous_curator_counter.checked_add(1) != Some(self.curator_counter) {
            return Err(CuratorError::CanonDecision(
                "curator_counter must equal previous_curator_counter + 1".into(),
            ));
        }
        Ok(())
    }
}

/// The live bridge to Lean's `CanonAdmission.accepts`/current `CanonState`. There
/// is intentionally no permissive implementation in this crate. A node adapter
/// must require beta for promotion, alpha for supersession, and exact current
/// revision before returning `Ok(())`.
pub trait CanonAdmissionOracle {
    fn admit(&self, decision: &CanonDecision) -> Result<(), String>;
}

/// Signed decision payload. The artifact carries both source and content
/// digests; display ids alone are never promotable.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CanonDecision {
    pub schema: String,
    pub admission: CanonAdmission,
    pub action: CanonAction,
    pub artifact: ArtifactRef,
}

impl CanonDecision {
    pub fn new(
        activation: &VerifiedMissionActivation<'_>,
        expected_revision: u64,
        previous_curator_counter: u64,
        curator_counter: u64,
        action: CanonAction,
        artifact: ArtifactRef,
    ) -> Result<Self, CuratorError> {
        let bundle = activation.bundle;
        artifact.validate()?;
        if artifact.mission_id != activation.config.mission_id {
            return Err(CuratorError::CanonDecision(
                "artifact mission differs from the Lean-admitted activated mission".into(),
            ));
        }
        if action == CanonAction::Promote && !bundle.is_predeclared_beta_artifact(&artifact) {
            return Err(CuratorError::CanonDecision(
                "promotion target is not an exact predeclared beta artifact in the authenticated catalog"
                    .into(),
            ));
        }
        if action == CanonAction::Promote {
            let (emitted_federation, emitted_root, _) =
                bundle
                    .mission_scope(artifact.mission_id)
                    .ok_or(CuratorError::UnknownMission(artifact.mission_id))?;
            if activation.config.federation_id != emitted_federation
                || activation.config.content_root != emitted_root
            {
                return Err(CuratorError::CanonDecision(
                    "promotion scope differs from authenticated mission federation/content root"
                        .into(),
                ));
            }
        }
        let admission = CanonAdmission {
            federation_id: activation.config.federation_id.clone(),
            content_root: activation.config.content_root.clone(),
            activation_digest: activation.config.activation_digest.clone(),
            content_session: activation.config.content_session.clone(),
            content_epoch: activation.config.content_epoch,
            curator_key: activation.config.curator_key.clone(),
            expected_revision,
            previous_curator_counter,
            curator_counter,
        };
        admission.validate_shape()?;
        Ok(Self {
            schema: CANON_DECISION_SCHEMA.into(),
            admission,
            action,
            artifact,
        })
    }

    fn signing_message(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(CANON_DECISION_DOMAIN);
        push_frame(&mut out, self.admission.federation_id.as_bytes());
        push_frame(&mut out, self.admission.content_root.as_bytes());
        push_frame(&mut out, self.admission.activation_digest.as_bytes());
        push_frame(&mut out, self.admission.content_session.as_bytes());
        out.extend_from_slice(&self.admission.content_epoch.to_be_bytes());
        push_frame(&mut out, self.admission.curator_key.as_bytes());
        out.extend_from_slice(&self.admission.expected_revision.to_be_bytes());
        out.extend_from_slice(&self.admission.previous_curator_counter.to_be_bytes());
        out.extend_from_slice(&self.admission.curator_counter.to_be_bytes());
        out.push(match self.action {
            CanonAction::Promote => 1,
            CanonAction::Supersede => 2,
        });
        out.extend_from_slice(&self.artifact.mission_id.to_be_bytes());
        out.extend_from_slice(&self.artifact.artifact_id.to_be_bytes());
        push_frame(&mut out, self.artifact.source_digest.as_bytes());
        push_frame(&mut out, self.artifact.content_digest.as_bytes());
        out
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SignedCanonDecision {
    pub decision: CanonDecision,
    pub curator_pubkey: String,
    pub signature: String,
}

impl SignedCanonDecision {
    pub fn verify(
        &self,
        activation: &VerifiedMissionActivation<'_>,
        expected_previous_counter: u64,
        expected_counter: u64,
        expected_revision: u64,
        oracle: &impl CanonAdmissionOracle,
    ) -> Result<(), CuratorError> {
        let bundle = activation.bundle;
        if self.decision.schema != CANON_DECISION_SCHEMA {
            return Err(CuratorError::CanonDecision(
                "unknown decision schema".into(),
            ));
        }
        self.decision.artifact.validate()?;
        self.decision.admission.validate_shape()?;
        if self.decision.artifact.mission_id != activation.config.mission_id {
            return Err(CuratorError::CanonDecision(
                "artifact mission differs from the Lean-admitted activated mission".into(),
            ));
        }
        if self.decision.admission.federation_id != activation.config.federation_id
            || self.decision.admission.content_root != activation.config.content_root
            || self.decision.admission.activation_digest != activation.config.activation_digest
            || self.decision.admission.content_session != activation.config.content_session
            || self.decision.admission.content_epoch != activation.config.content_epoch
            || self.decision.admission.curator_key != activation.config.curator_key
        {
            return Err(CuratorError::CanonDecision(
                "decision scope differs from the Lean-admitted activated mission".into(),
            ));
        }
        if self.decision.admission.previous_curator_counter != expected_previous_counter
            || self.decision.admission.curator_counter != expected_counter
        {
            return Err(CuratorError::CanonDecision("counter mismatch".into()));
        }
        if self.decision.admission.expected_revision != expected_revision {
            return Err(CuratorError::CanonDecision(
                "canon revision mismatch".into(),
            ));
        }
        if self.decision.action == CanonAction::Promote {
            if !bundle.is_predeclared_beta_artifact(&self.decision.artifact) {
                return Err(CuratorError::CanonDecision(
                    "deserialized promotion target is not predeclared by authenticated catalog"
                        .into(),
                ));
            }
            let (federation, root, content_session) = bundle
                .mission_scope(self.decision.artifact.mission_id)
                .ok_or(CuratorError::UnknownMission(
                    self.decision.artifact.mission_id,
                ))?;
            if self.decision.admission.federation_id != federation
                || self.decision.admission.content_root != root
                || self.decision.admission.content_session != content_session
            {
                return Err(CuratorError::CanonDecision(
                    "promotion admission scope differs from authenticated mission".into(),
                ));
            }
        }
        let pinned = PublicKey(parse_hex_array::<32>(
            &activation.config.curator_key,
            "curator_key",
        )?);
        if self.curator_pubkey != activation.config.curator_key {
            return Err(CuratorError::CanonDecision(
                "decision key differs from external pin".into(),
            ));
        }
        let signature = Signature(parse_hex_array::<64>(&self.signature, "signature")?);
        if !dregg_types::verify(&pinned, &self.decision.signing_message(), &signature) {
            return Err(CuratorError::BadSignature);
        }
        oracle
            .admit(&self.decision)
            .map_err(CuratorError::CanonAdmission)?;
        Ok(())
    }
}

/// Domain-separated exact-byte message shared with web/extension verifiers.
pub fn content_epoch_signing_message(epoch: u64, counter: u64, manifest: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(CONTENT_EPOCH_DOMAIN.len() + 24 + manifest.len());
    out.extend_from_slice(CONTENT_EPOCH_DOMAIN);
    out.extend_from_slice(&epoch.to_be_bytes());
    out.extend_from_slice(&counter.to_be_bytes());
    out.extend_from_slice(&(manifest.len() as u64).to_be_bytes());
    out.extend_from_slice(manifest);
    out
}

fn validate_manifest(manifest: &Poag1Manifest) -> Result<Vec<String>, CuratorError> {
    if manifest.format != POAG1_FORMAT {
        return Err(CuratorError::Manifest(format!(
            "format {} != {POAG1_FORMAT}",
            manifest.format
        )));
    }
    if manifest.schema_version != POAG1_SCHEMA_VERSION {
        return Err(CuratorError::Manifest(format!(
            "schema version {} != {POAG1_SCHEMA_VERSION}",
            manifest.schema_version
        )));
    }
    if manifest.authority != POAG1_AUTHORITY {
        return Err(CuratorError::Manifest(format!(
            "authority {} != {POAG1_AUTHORITY}",
            manifest.authority
        )));
    }
    parse_sha256(&manifest.source_digest, "source_digest")?;
    let minimum_artifacts = 3;
    let maximum_artifacts = 2 + MAX_MISSIONS_PER_EPOCH;
    if !(minimum_artifacts..=maximum_artifacts).contains(&manifest.artifacts.len()) {
        return Err(CuratorError::Manifest(format!(
            "artifact set has {}, expected {minimum_artifacts}..={maximum_artifacts}",
            manifest.artifacts.len(),
        )));
    }

    if manifest.artifacts[0].path != SCHEMA_PATH || manifest.artifacts[1].path != CATALOG_PATH {
        return Err(CuratorError::Manifest(format!(
            "artifact order must begin [{SCHEMA_PATH:?}, {CATALOG_PATH:?}]"
        )));
    }
    let game_paths: Vec<String> = manifest.artifacts[2..]
        .iter()
        .map(|pin| pin.path.clone())
        .collect();
    if !game_paths.iter().any(|path| path == SIGNAL_PATH) {
        return Err(CuratorError::Manifest(
            "every POAG1 v1 epoch must retain Signal Triangulation".into(),
        ));
    }
    if !game_paths.windows(2).all(|pair| pair[0] < pair[1]) {
        return Err(CuratorError::Manifest(
            "game artifacts must be strictly path-ascending after schema/catalog".into(),
        ));
    }

    let mut seen = BTreeSet::new();
    for pin in &manifest.artifacts {
        validate_relative_path(&pin.path)?;
        if !seen.insert(pin.path.as_str()) {
            return Err(CuratorError::Manifest(format!(
                "duplicate artifact path {}",
                pin.path
            )));
        }
        parse_sha256(&pin.sha256, "artifact.sha256")?;
        if pin.fnv1a64.len() != 16
            || !pin
                .fnv1a64
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        {
            return Err(CuratorError::Manifest(format!(
                "artifact {} has noncanonical fnv1a64",
                pin.path
            )));
        }
        let expected_media_type = if pin.path == SCHEMA_PATH {
            "application/schema+json"
        } else if pin.path == CATALOG_PATH || SUPPORTED_GAME_PATHS.contains(&pin.path.as_str()) {
            "application/json"
        } else {
            return Err(CuratorError::Manifest(format!(
                "unknown artifact {}",
                pin.path
            )));
        };
        if pin.media_type != expected_media_type {
            return Err(CuratorError::Manifest(format!(
                "artifact {} media type {} != {}",
                pin.path, pin.media_type, expected_media_type
            )));
        }
    }
    Ok(game_paths)
}

fn validate_relative_path(path: &str) -> Result<(), CuratorError> {
    let candidate = Path::new(path);
    if candidate.as_os_str().is_empty()
        || candidate.is_absolute()
        || candidate
            .components()
            .any(|component| !matches!(component, Component::Normal(_)))
    {
        return Err(CuratorError::Manifest(format!(
            "artifact path is not a canonical relative path: {path}"
        )));
    }
    Ok(())
}

fn read_regular_bounded(path: &Path, limit: u64) -> Result<Vec<u8>, CuratorError> {
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    options.custom_flags(libc::O_NOFOLLOW);

    // One descriptor owns the type check, size check, and bounded read. This
    // avoids the classic stat-then-open race and refuses a final symlink on
    // Unix even if an attacker swaps the path while it is being inspected.
    let file = options.open(path).map_err(|e| io_error(path, e))?;
    let metadata = file.metadata().map_err(|e| io_error(path, e))?;
    if !metadata.is_file() {
        return Err(CuratorError::Artifact {
            path: path.display().to_string(),
            reason: "not a regular non-symlink file".into(),
        });
    }
    if metadata.len() > limit {
        return Err(CuratorError::Artifact {
            path: path.display().to_string(),
            reason: format!("{} bytes exceeds limit {limit}", metadata.len()),
        });
    }
    let mut bytes = Vec::with_capacity(metadata.len().min(limit) as usize);
    file.take(limit.saturating_add(1))
        .read_to_end(&mut bytes)
        .map_err(|e| io_error(path, e))?;
    if bytes.len() as u64 > limit {
        return Err(CuratorError::Artifact {
            path: path.display().to_string(),
            reason: format!("file grew beyond limit {limit} while being read"),
        });
    }
    Ok(bytes)
}

fn parse_artifact_json(
    manifest_path: &Path,
    artifacts: &BTreeMap<String, Vec<u8>>,
    path: &str,
    expected_format: &str,
) -> Result<Value, CuratorError> {
    let bytes = artifacts.get(path).ok_or_else(|| CuratorError::Artifact {
        path: path.into(),
        reason: "required artifact is absent after manifest validation".into(),
    })?;
    let value = parse_strict_json(bytes).map_err(|reason| CuratorError::Json {
        path: manifest_path.parent().unwrap_or(Path::new(".")).join(path),
        reason,
    })?;
    let object = value.as_object().ok_or_else(|| CuratorError::Artifact {
        path: path.into(),
        reason: "top-level JSON value is not an object".into(),
    })?;
    if object.get("format").and_then(Value::as_str) != Some(expected_format) {
        return Err(CuratorError::Artifact {
            path: path.into(),
            reason: format!("format is not {expected_format}"),
        });
    }
    if object.get("schema_version").and_then(Value::as_u64) != Some(POAG1_SCHEMA_VERSION) {
        return Err(CuratorError::Artifact {
            path: path.into(),
            reason: "schema_version is not 1".into(),
        });
    }
    Ok(value)
}

fn validate_schema_contract(schema: &Value, game_paths: &[String]) -> Result<(), CuratorError> {
    let object = schema
        .as_object()
        .ok_or_else(|| CuratorError::Catalog("POAG1 schema is not an object".into()))?;
    require_exact_object_keys(
        object,
        &["format", "schema_version", "contract"],
        "POAG1 schema",
    )
    .map_err(CuratorError::Catalog)?;
    let contract = object
        .get("contract")
        .and_then(Value::as_object)
        .ok_or_else(|| CuratorError::Catalog("POAG1 schema contract is not an object".into()))?;
    require_exact_object_keys(
        contract,
        &[
            "manifest_required",
            "artifact_pin_required",
            "source_digest_pattern",
            "artifact_sha256_pattern",
            "bytes32_pattern",
            "fnv1a64_pattern",
            "content_root",
            "activation_digest",
            "unknown_fields",
            "unknown_artifacts",
        ],
        "POAG1 schema contract",
    )
    .map_err(CuratorError::Catalog)?;
    require_exact_string_array(
        contract.get("manifest_required"),
        &[
            "format",
            "schema_version",
            "source_digest",
            "authority",
            "artifacts",
        ],
        "manifest_required",
    )?;
    require_exact_string_array(
        contract.get("artifact_pin_required"),
        &["path", "media_type", "bytes", "sha256", "fnv1a64"],
        "artifact_pin_required",
    )?;
    for (field, expected) in [
        ("source_digest_pattern", "^sha256:[0-9a-f]{64}$"),
        ("artifact_sha256_pattern", "^sha256:[0-9a-f]{64}$"),
        ("bytes32_pattern", "^[0-9a-f]{64}$"),
        ("fnv1a64_pattern", "^[0-9a-f]{16}$"),
        ("unknown_fields", "reject"),
        ("unknown_artifacts", "reject"),
    ] {
        if contract.get(field).and_then(Value::as_str) != Some(expected) {
            return Err(CuratorError::Catalog(format!(
                "POAG1 schema {field} differs from v1"
            )));
        }
    }

    let root = contract
        .get("content_root")
        .and_then(Value::as_object)
        .ok_or_else(|| CuratorError::Catalog("content_root contract is not an object".into()))?;
    require_exact_object_keys(
        root,
        &["algorithm", "domain", "framing", "entry_order", "paths"],
        "content_root contract",
    )
    .map_err(CuratorError::Catalog)?;
    if root.get("algorithm").and_then(Value::as_str) != Some("sha256")
        || root.get("domain").and_then(Value::as_str) != Some("path-of-angels/content-root/v1\0")
        || root.get("framing").and_then(Value::as_str)
            != Some(
                "file_count_be64 || (path_len_be64 || path_utf8 || content_len_be64 || content_bytes)*",
            )
        || root.get("entry_order").and_then(Value::as_str) != Some("path_ascending")
    {
        return Err(CuratorError::Catalog(
            "content_root contract differs from POAG1 v1".into(),
        ));
    }
    let schema_paths = root
        .get("paths")
        .and_then(Value::as_array)
        .ok_or_else(|| CuratorError::Catalog("content_root.paths is not an array".into()))?;
    let schema_paths: Vec<&str> = schema_paths
        .iter()
        .map(|path| {
            path.as_str().ok_or_else(|| {
                CuratorError::Catalog("content_root.paths contains a non-string".into())
            })
        })
        .collect::<Result<_, _>>()?;
    if schema_paths != game_paths.iter().map(String::as_str).collect::<Vec<_>>() {
        return Err(CuratorError::Catalog(
            "content_root.paths does not exactly equal the canonical manifest game order".into(),
        ));
    }

    let activation = contract
        .get("activation_digest")
        .and_then(Value::as_object)
        .ok_or_else(|| CuratorError::Catalog("activation_digest is not an object".into()))?;
    require_exact_object_keys(
        activation,
        &["algorithm", "domain", "framing", "location"],
        "activation_digest contract",
    )
    .map_err(CuratorError::Catalog)?;
    if activation.get("algorithm").and_then(Value::as_str) != Some("sha256")
        || activation.get("domain").and_then(Value::as_str)
            != Some("pathofangels.network/activation-digest/v1\0")
        || activation.get("framing").and_then(Value::as_str)
            != Some(
                "schema_len_be64 || schema_utf8 || manifest_sha256_raw32 || curator_pubkey_raw32 || content_epoch_be64 || counter_be64 || signature_raw64",
            )
        || activation.get("location").and_then(Value::as_str)
            != Some("detached verified activation; excluded from manifest preimage")
    {
        return Err(CuratorError::Catalog(
            "activation_digest contract differs from POAG1 v1".into(),
        ));
    }
    Ok(())
}

fn require_exact_string_array(
    value: Option<&Value>,
    expected: &[&str],
    field: &str,
) -> Result<(), CuratorError> {
    let actual = value
        .and_then(Value::as_array)
        .ok_or_else(|| CuratorError::Catalog(format!("{field} is not an array")))?;
    let actual: Vec<&str> = actual
        .iter()
        .map(|value| {
            value
                .as_str()
                .ok_or_else(|| CuratorError::Catalog(format!("{field} contains a non-string")))
        })
        .collect::<Result<_, _>>()?;
    if actual != expected {
        return Err(CuratorError::Catalog(format!(
            "{field} differs from the exact ordered POAG1 v1 contract"
        )));
    }
    Ok(())
}

fn validate_game_descriptor_mission_match(
    descriptor_path: &str,
    descriptor: &Value,
    mission: &serde_json::Map<String, Value>,
    mission_id: u64,
) -> Result<(), CuratorError> {
    let descriptor = descriptor
        .as_object()
        .ok_or_else(|| CuratorError::Artifact {
            path: descriptor_path.into(),
            reason: "game descriptor is not an object".into(),
        })?;
    let expected_game_id = descriptor_path
        .strip_prefix("games/")
        .and_then(|path| path.strip_suffix(".json"))
        .expect("supported game paths have canonical names");
    if descriptor.get("game_id").and_then(Value::as_str) != Some(expected_game_id) {
        return Err(CuratorError::Catalog(format!(
            "mission {mission_id} descriptor game_id does not match {descriptor_path}"
        )));
    }
    for field in ["ruleset", "engine_module", "run_seed"] {
        let descriptor_value = descriptor.get(field).and_then(Value::as_str);
        let mission_value = mission.get(field).and_then(Value::as_str);
        if descriptor_value.is_none() || descriptor_value != mission_value {
            return Err(CuratorError::Catalog(format!(
                "mission {mission_id} {field} differs from {descriptor_path}"
            )));
        }
    }
    if descriptor.get("action_limit").and_then(Value::as_u64)
        != mission.get("action_limit").and_then(Value::as_u64)
    {
        return Err(CuratorError::Catalog(format!(
            "mission {mission_id} action_limit differs from {descriptor_path}"
        )));
    }
    Ok(())
}

fn index_catalog(
    catalog: &Value,
    authenticated_content_root: &str,
    authenticated_source_digest: &str,
    authenticated_game_descriptors: &BTreeMap<String, Value>,
    authenticated_descriptor_digests: &BTreeMap<String, String>,
) -> Result<CatalogIndex, CuratorError> {
    let object = catalog
        .as_object()
        .ok_or_else(|| CuratorError::Catalog("catalog is not an object".into()))?;
    require_exact_object_keys(
        object,
        &["format", "schema_version", "missions", "fixtures"],
        "POAG1 catalog",
    )
    .map_err(CuratorError::Catalog)?;
    let mission_values = object
        .get("missions")
        .and_then(Value::as_array)
        .ok_or_else(|| CuratorError::Catalog("missions is not an array".into()))?;
    if !(1..=MAX_MISSIONS_PER_EPOCH).contains(&mission_values.len()) {
        return Err(CuratorError::Catalog(format!(
            "missions has {}, expected 1..={MAX_MISSIONS_PER_EPOCH}",
            mission_values.len()
        )));
    }
    if mission_values.len() != authenticated_game_descriptors.len() {
        return Err(CuratorError::Catalog(
            "mission count does not equal authenticated game descriptor count".into(),
        ));
    }
    let mut missions = BTreeMap::new();
    let mut previous_mission_id = None;
    let mut content_epoch = None;
    let mut descriptor_paths = BTreeSet::new();
    let mut content_sessions = BTreeSet::new();
    let mut run_seeds = BTreeSet::new();
    let mut all_artifacts = BTreeSet::new();
    for mission in mission_values {
        let obj = mission
            .as_object()
            .ok_or_else(|| CuratorError::Catalog("mission is not an object".into()))?;
        require_exact_object_keys(
            obj,
            &[
                "mission_id",
                "title",
                "engine_module",
                "ruleset",
                "reward_class",
                "action_limit",
                "privacy_grade",
                "ballot_regime",
                "epoch",
                "federation_id",
                "content_root",
                "activation",
                "content_session",
                "run_seed",
                "budget",
                "allowed_relics",
                "descriptor_path",
                "allowed_beta_discoveries",
            ],
            "POAG1 mission",
        )
        .map_err(CuratorError::Catalog)?;
        let mission_id = obj
            .get("mission_id")
            .and_then(Value::as_u64)
            .ok_or_else(|| CuratorError::Catalog("mission_id is not a u64".into()))?;
        if previous_mission_id.is_some_and(|previous| mission_id <= previous) {
            return Err(CuratorError::Catalog(
                "missions must be strictly mission_id-ascending".into(),
            ));
        }
        previous_mission_id = Some(mission_id);
        let epoch = obj.get("epoch").and_then(Value::as_u64).ok_or_else(|| {
            CuratorError::Catalog(format!("mission {mission_id} epoch is not a u64"))
        })?;
        if content_epoch.is_some_and(|expected| epoch != expected) {
            return Err(CuratorError::Catalog(format!(
                "mission {mission_id} epoch {epoch} differs from the epoch's other missions"
            )));
        }
        content_epoch.get_or_insert(epoch);
        for field in [
            "title",
            "engine_module",
            "ruleset",
            "reward_class",
            "privacy_grade",
            "ballot_regime",
        ] {
            if obj
                .get(field)
                .and_then(Value::as_str)
                .is_none_or(str::is_empty)
            {
                return Err(CuratorError::Catalog(format!(
                    "mission {mission_id} {field} is not a nonempty string"
                )));
            }
        }
        obj.get("action_limit")
            .and_then(Value::as_u64)
            .ok_or_else(|| {
                CuratorError::Catalog(format!("mission {mission_id} action_limit is not a u64"))
            })?;
        let federation_id = obj
            .get("federation_id")
            .and_then(Value::as_str)
            .ok_or_else(|| CuratorError::Catalog("federation_id is not a string".into()))?;
        parse_hex_array::<32>(federation_id, "federation_id")?;
        let content_root = obj
            .get("content_root")
            .and_then(Value::as_str)
            .ok_or_else(|| CuratorError::Catalog("content_root is not a string".into()))?;
        parse_sha256(content_root, "content_root")?;
        if content_root != authenticated_content_root {
            return Err(CuratorError::Catalog(format!(
                "mission {mission_id} content_root does not bind the authenticated game artifacts"
            )));
        }
        let content_session = obj
            .get("content_session")
            .and_then(Value::as_str)
            .ok_or_else(|| CuratorError::Catalog("content_session is not a string".into()))?;
        parse_hex_array::<32>(content_session, "content_session")?;
        if !content_sessions.insert(content_session.to_owned()) {
            return Err(CuratorError::Catalog(format!(
                "mission {mission_id} reuses another mission's content_session"
            )));
        }
        let run_seed = obj
            .get("run_seed")
            .and_then(Value::as_str)
            .ok_or_else(|| CuratorError::Catalog("run_seed is not a string".into()))?;
        parse_hex_array::<32>(run_seed, "run_seed")?;
        if !run_seeds.insert(run_seed.to_owned()) {
            return Err(CuratorError::Catalog(format!(
                "mission {mission_id} reuses another mission's run_seed"
            )));
        }
        let activation = obj
            .get("activation")
            .and_then(Value::as_object)
            .ok_or_else(|| CuratorError::Catalog("activation is not an object".into()))?;
        require_exact_object_keys(
            activation,
            &["state", "digest_source"],
            "mission activation",
        )
        .map_err(CuratorError::Catalog)?;
        if activation.get("state").and_then(Value::as_str) != Some("detached-signature-required")
            || activation.get("digest_source").and_then(Value::as_str) != Some(CONTENT_EPOCH_SCHEMA)
        {
            return Err(CuratorError::Catalog(format!(
                "mission {mission_id} has a non-v1 activation marker"
            )));
        }
        let budget = obj
            .get("budget")
            .and_then(Value::as_object)
            .ok_or_else(|| CuratorError::Catalog("budget is not an object".into()))?;
        require_exact_object_keys(
            budget,
            &[
                "intel",
                "supplies",
                "cohesion",
                "influence",
                "score",
                "relics",
            ],
            "mission budget",
        )
        .map_err(CuratorError::Catalog)?;
        if budget.values().any(|value| value.as_u64().is_none()) {
            return Err(CuratorError::Catalog(format!(
                "mission {mission_id} budget contains a non-u64 value"
            )));
        }
        let descriptor_path = obj
            .get("descriptor_path")
            .and_then(Value::as_str)
            .ok_or_else(|| CuratorError::Catalog("descriptor_path is not a string".into()))?;
        if !SUPPORTED_GAME_PATHS.contains(&descriptor_path) {
            return Err(CuratorError::Catalog(format!(
                "mission {mission_id} names unsupported descriptor {descriptor_path}"
            )));
        }
        let descriptor = authenticated_game_descriptors
            .get(descriptor_path)
            .ok_or_else(|| {
                CuratorError::Catalog(format!(
                    "mission {mission_id} names unpinned descriptor {descriptor_path}"
                ))
            })?;
        if !descriptor_paths.insert(descriptor_path.to_owned()) {
            return Err(CuratorError::Catalog(format!(
                "descriptor {descriptor_path} is assigned to more than one mission"
            )));
        }
        validate_game_descriptor_mission_match(descriptor_path, descriptor, obj, mission_id)?;
        let allowed_relics = obj
            .get("allowed_relics")
            .and_then(Value::as_array)
            .ok_or_else(|| {
                CuratorError::Catalog(format!("mission {mission_id} lacks allowed_relics"))
            })?;
        if allowed_relics.len() > MAX_RELICS_PER_MISSION {
            return Err(CuratorError::Catalog(format!(
                "mission {mission_id} has {} allowed relics, maximum is {MAX_RELICS_PER_MISSION}",
                allowed_relics.len()
            )));
        }
        let mut relics = BTreeSet::new();
        let mut previous_relic = None;
        for relic in allowed_relics {
            let relic = relic.as_u64().ok_or_else(|| {
                CuratorError::Catalog(format!("mission {mission_id} has nonnumeric allowed relic"))
            })?;
            if previous_relic.is_some_and(|previous| relic <= previous) || !relics.insert(relic) {
                return Err(CuratorError::Catalog(format!(
                    "mission {mission_id} allowed_relics must be strictly ascending; saw {relic}"
                )));
            }
            previous_relic = Some(relic);
        }
        let allowed_values = obj
            .get("allowed_beta_discoveries")
            .and_then(Value::as_array)
            .ok_or_else(|| {
                CuratorError::Catalog(format!(
                    "mission {mission_id} lacks allowed_beta_discoveries"
                ))
            })?;
        if !(1..=MAX_DISCOVERIES_PER_MISSION).contains(&allowed_values.len()) {
            return Err(CuratorError::Catalog(format!(
                "mission {mission_id} allowed_beta_discoveries has {}, expected 1..={MAX_DISCOVERIES_PER_MISSION}",
                allowed_values.len()
            )));
        }
        let descriptor_digest = authenticated_descriptor_digests
            .get(descriptor_path)
            .expect("descriptor digest set matches authenticated descriptors");
        let mut allowed_beta_discoveries = Vec::with_capacity(allowed_values.len());
        let mut unique = BTreeSet::new();
        let mut previous_artifact = None;
        for artifact in allowed_values {
            let artifact: ArtifactRef = serde_json::from_value(artifact.clone()).map_err(|e| {
                CuratorError::Catalog(format!(
                    "mission {mission_id} has malformed artifact ref: {e}"
                ))
            })?;
            artifact.validate()?;
            if artifact.mission_id != mission_id {
                return Err(CuratorError::Catalog(format!(
                    "mission {mission_id} contains artifact for mission {}",
                    artifact.mission_id
                )));
            }
            if artifact.source_digest != authenticated_source_digest
                || artifact.content_digest != *descriptor_digest
            {
                return Err(CuratorError::Catalog(format!(
                    "mission {mission_id} artifact does not bind the authenticated source and descriptor bytes"
                )));
            }
            if previous_artifact
                .as_ref()
                .is_some_and(|previous| artifact <= *previous)
                || !unique.insert(artifact.clone())
            {
                return Err(CuratorError::Catalog(format!(
                    "mission {mission_id} artifact refs must be unique and strictly ascending"
                )));
            }
            if !all_artifacts.insert(artifact.clone()) {
                return Err(CuratorError::Catalog(
                    "the same exact artifact ref appears in more than one mission".into(),
                ));
            }
            previous_artifact = Some(artifact.clone());
            allowed_beta_discoveries.push(artifact);
        }
        if missions
            .insert(
                mission_id,
                MissionIndex {
                    exact_json: mission.clone(),
                    federation_id: federation_id.to_owned(),
                    content_root: content_root.to_owned(),
                    content_session: content_session.to_owned(),
                    run_seed: run_seed.to_owned(),
                    allowed_beta_discoveries,
                },
            )
            .is_some()
        {
            return Err(CuratorError::Catalog(format!(
                "duplicate mission_id {mission_id}"
            )));
        }
    }

    let authenticated_paths: BTreeSet<String> =
        authenticated_game_descriptors.keys().cloned().collect();
    if descriptor_paths != authenticated_paths {
        return Err(CuratorError::Catalog(
            "catalog missions do not cover every authenticated descriptor exactly once".into(),
        ));
    }

    let mut fixtures = BTreeMap::new();
    if let Some(fixture_values) = object.get("fixtures") {
        let fixture_values = fixture_values
            .as_array()
            .ok_or_else(|| CuratorError::Catalog("fixtures is not an array".into()))?;
        if fixture_values.len() > MAX_FIXTURES_PER_EPOCH {
            return Err(CuratorError::Catalog(format!(
                "fixtures has {}, maximum is {MAX_FIXTURES_PER_EPOCH}",
                fixture_values.len()
            )));
        }
        let mut previous_fixture_key: Option<(u64, String)> = None;
        let mut fixture_counts = BTreeMap::<u64, usize>::new();
        for fixture in fixture_values {
            let obj = fixture
                .as_object()
                .ok_or_else(|| CuratorError::Catalog("fixture is not an object".into()))?;
            require_exact_object_keys(
                obj,
                &[
                    "id",
                    "mission_id",
                    "run_seed",
                    "base_world",
                    "contribution",
                    "preview_world",
                ],
                "POAG1 fixture",
            )
            .map_err(CuratorError::Catalog)?;
            let id = obj
                .get("id")
                .and_then(Value::as_str)
                .filter(|id| !id.is_empty())
                .ok_or_else(|| CuratorError::Catalog("fixture id is empty or absent".into()))?;
            let mission_id = obj
                .get("mission_id")
                .and_then(Value::as_u64)
                .ok_or_else(|| CuratorError::Catalog(format!("fixture {id} lacks mission_id")))?;
            if !missions.contains_key(&mission_id) {
                return Err(CuratorError::Catalog(format!(
                    "fixture {id} names unknown mission {mission_id}"
                )));
            }
            let key = (mission_id, id.to_owned());
            if previous_fixture_key
                .as_ref()
                .is_some_and(|previous| key <= *previous)
            {
                return Err(CuratorError::Catalog(
                    "fixtures must be strictly ordered by (mission_id, id)".into(),
                ));
            }
            previous_fixture_key = Some(key);
            let count = fixture_counts.entry(mission_id).or_default();
            *count += 1;
            if *count > MAX_FIXTURES_PER_MISSION {
                return Err(CuratorError::Catalog(format!(
                    "mission {mission_id} has more than {MAX_FIXTURES_PER_MISSION} fixtures"
                )));
            }
            let fixture_seed = obj
                .get("run_seed")
                .and_then(Value::as_str)
                .ok_or_else(|| CuratorError::Catalog(format!("fixture {id} lacks run_seed")))?;
            parse_hex_array::<32>(fixture_seed, "fixture.run_seed")?;
            if fixture_seed != missions[&mission_id].run_seed {
                return Err(CuratorError::Catalog(format!(
                    "fixture {id} run_seed differs from mission {mission_id}"
                )));
            }
            let field = |name: &'static str| {
                obj.get(name)
                    .cloned()
                    .ok_or_else(|| CuratorError::Catalog(format!("fixture {id} lacks {name}")))
            };
            let indexed = FixtureIndex {
                mission_id,
                base_world: field("base_world")?,
                contribution: field("contribution")?,
                preview_world: field("preview_world")?,
            };
            if fixtures.insert(id.to_owned(), indexed).is_some() {
                return Err(CuratorError::Catalog(format!("duplicate fixture id {id}")));
            }
        }
    }
    Ok(CatalogIndex {
        missions,
        fixtures,
        content_epoch: content_epoch.expect("nonempty mission list was checked"),
    })
}

/// POAG1 v1 content root. Schema/catalog/manifest envelopes are intentionally
/// excluded, avoiding a self-hash cycle; only the bounded canonical game
/// descriptor set participates. `semantic_paths` is already checked strictly
/// ascending against both manifest and schema.
fn content_root_v1(
    artifacts: &BTreeMap<String, Vec<u8>>,
    semantic_paths: &[String],
) -> Result<String, CuratorError> {
    let mut preimage = Vec::new();
    preimage.extend_from_slice(CONTENT_ROOT_DOMAIN);
    preimage.extend_from_slice(&(semantic_paths.len() as u64).to_be_bytes());
    for path in semantic_paths {
        let contents = artifacts.get(path).ok_or_else(|| CuratorError::Artifact {
            path: path.clone(),
            reason: "content-root input is absent".into(),
        })?;
        push_frame(&mut preimage, path.as_bytes());
        push_frame(&mut preimage, contents);
    }
    Ok(sha256_tagged(&preimage))
}

fn require_exact_object_keys(
    object: &serde_json::Map<String, Value>,
    expected: &[&str],
    context: &str,
) -> Result<(), String> {
    let actual: BTreeSet<&str> = object.keys().map(String::as_str).collect();
    let expected: BTreeSet<&str> = expected.iter().copied().collect();
    if actual == expected {
        return Ok(());
    }
    let missing: Vec<_> = expected.difference(&actual).copied().collect();
    let unknown: Vec<_> = actual.difference(&expected).copied().collect();
    Err(format!(
        "{context} keys differ from v1 (missing={missing:?}, unknown={unknown:?})"
    ))
}

fn manifest_validator_public_keys(
    manifest: &serde_json::Map<String, Value>,
) -> Result<Vec<[u8; 32]>, CuratorError> {
    let nodes = manifest
        .get("nodes")
        .and_then(Value::as_array)
        .ok_or_else(|| CuratorError::Deployment("manifest validator roster is absent".into()))?;
    let mut keys = Vec::with_capacity(nodes.len());
    let mut distinct = BTreeSet::new();
    for (index, node) in nodes.iter().enumerate() {
        let key = node
            .as_object()
            .and_then(|node| node.get("public_key"))
            .and_then(Value::as_str)
            .ok_or_else(|| {
                CuratorError::Deployment(format!(
                    "manifest node {index} validator public_key is absent"
                ))
            })?;
        let key = parse_hex_array::<32>(key, "validator public_key")?;
        if !distinct.insert(key) {
            return Err(CuratorError::Deployment(
                "manifest validator roster contains a duplicate key".into(),
            ));
        }
        keys.push(key);
    }
    Ok(keys)
}

fn parse_sha256(value: &str, field: &'static str) -> Result<[u8; 32], CuratorError> {
    let hex = value
        .strip_prefix("sha256:")
        .ok_or(CuratorError::MalformedHex { field, bytes: 32 })?;
    parse_hex_array::<32>(hex, field)
}

fn parse_hex_array<const N: usize>(
    value: &str,
    field: &'static str,
) -> Result<[u8; N], CuratorError> {
    if value.len() != N * 2
        || !value
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err(CuratorError::MalformedHex { field, bytes: N });
    }
    let mut out = [0u8; N];
    for (i, pair) in value.as_bytes().chunks_exact(2).enumerate() {
        out[i] = (hex_nibble(pair[0]) << 4) | hex_nibble(pair[1]);
    }
    Ok(out)
}

fn hex_nibble(value: u8) -> u8 {
    match value {
        b'0'..=b'9' => value - b'0',
        b'a'..=b'f' => value - b'a' + 10,
        _ => unreachable!("validated lowercase hex before decoding"),
    }
}

fn hex_encode(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(HEX[(byte >> 4) as usize] as char);
        out.push(HEX[(byte & 0x0f) as usize] as char);
    }
    out
}

fn sha256_raw(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}

fn sha256_tagged(bytes: &[u8]) -> String {
    format!("sha256:{}", hex_encode(&sha256_raw(bytes)))
}

pub fn fnv1a64_hex(bytes: &[u8]) -> String {
    let mut hash = 0xcbf29ce484222325u64;
    for byte in bytes {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    format!("{hash:016x}")
}

fn push_frame(out: &mut Vec<u8>, bytes: &[u8]) {
    out.extend_from_slice(&(bytes.len() as u64).to_be_bytes());
    out.extend_from_slice(bytes);
}

/// Deserialize JSON while rejecting duplicate object keys at every depth.
fn parse_strict_json(bytes: &[u8]) -> Result<Value, String> {
    let mut deserializer = serde_json::Deserializer::from_slice(bytes);
    let strict = StrictValue::deserialize(&mut deserializer).map_err(|e| e.to_string())?;
    deserializer.end().map_err(|e| e.to_string())?;
    Ok(strict.0)
}

struct StrictValue(Value);

impl<'de> Deserialize<'de> for StrictValue {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_any(StrictValueVisitor)
    }
}

struct StrictValueVisitor;

impl<'de> Visitor<'de> for StrictValueVisitor {
    type Value = StrictValue;

    fn expecting(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("a JSON value without duplicate object keys")
    }

    fn visit_bool<E>(self, value: bool) -> Result<Self::Value, E> {
        Ok(StrictValue(Value::Bool(value)))
    }

    fn visit_i64<E>(self, value: i64) -> Result<Self::Value, E> {
        Ok(StrictValue(Value::Number(value.into())))
    }

    fn visit_u64<E>(self, value: u64) -> Result<Self::Value, E> {
        Ok(StrictValue(Value::Number(value.into())))
    }

    fn visit_f64<E>(self, value: f64) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        serde_json::Number::from_f64(value)
            .map(Value::Number)
            .map(StrictValue)
            .ok_or_else(|| E::custom("non-finite JSON number"))
    }

    fn visit_str<E>(self, value: &str) -> Result<Self::Value, E> {
        Ok(StrictValue(Value::String(value.to_owned())))
    }

    fn visit_string<E>(self, value: String) -> Result<Self::Value, E> {
        Ok(StrictValue(Value::String(value)))
    }

    fn visit_none<E>(self) -> Result<Self::Value, E> {
        Ok(StrictValue(Value::Null))
    }

    fn visit_unit<E>(self) -> Result<Self::Value, E> {
        Ok(StrictValue(Value::Null))
    }

    fn visit_some<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
    where
        D: Deserializer<'de>,
    {
        StrictValue::deserialize(deserializer)
    }

    fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let mut values = Vec::new();
        while let Some(value) = sequence.next_element::<StrictValue>()? {
            values.push(value.0);
        }
        Ok(StrictValue(Value::Array(values)))
    }

    fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
    where
        A: MapAccess<'de>,
    {
        let mut values = serde_json::Map::new();
        while let Some((key, value)) = map.next_entry::<String, StrictValue>()? {
            if values.insert(key.clone(), value.0).is_some() {
                return Err(serde::de::Error::custom(format!(
                    "duplicate JSON object key {key:?}"
                )));
            }
        }
        Ok(StrictValue(Value::Object(values)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Copy)]
    struct GameSpec {
        mission_id: u64,
        artifact_id: u64,
        path: &'static str,
        title: &'static str,
        engine: &'static str,
        ruleset: &'static str,
        action_limit: u64,
        session_byte: u8,
        seed_byte: u8,
    }

    const SIGNAL: GameSpec = GameSpec {
        mission_id: 7,
        artifact_id: 447,
        path: SIGNAL_PATH,
        title: "Deck 447 intercept",
        engine: "Dregg2.Games.PathOfAngels.SignalTriangulation",
        ruleset: "signal-v1",
        action_limit: 5,
        session_byte: 0x55,
        seed_byte: 0x66,
    };
    const RELAY: GameSpec = GameSpec {
        mission_id: 8,
        artifact_id: 448,
        path: "games/relay-repair.json",
        title: "Relay Repair",
        engine: "Dregg2.Games.PathOfAngels.RelayRepair",
        ruleset: "relay-v1",
        action_limit: 4,
        session_byte: 0x56,
        seed_byte: 0x67,
    };
    const SALVAGE: GameSpec = GameSpec {
        mission_id: 9,
        artifact_id: 449,
        path: "games/salvage-lock.json",
        title: "Salvage Lock",
        engine: "Dregg2.Games.PathOfAngels.SalvageLock",
        ruleset: "salvage-v1",
        action_limit: 12,
        session_byte: 0x57,
        seed_byte: 0x68,
    };

    struct ExactAdmission {
        action: CanonAction,
        artifact: ArtifactRef,
        revision: u64,
    }

    struct ExactActivation;
    struct MultiActivation;

    impl MissionActivationOracle for ExactActivation {
        fn admit(&self, config: &ActivatedMissionConfig) -> Result<(), String> {
            if config.mission_id == 7
                && config.mission_template["mission_id"] == 7
                && config.federation_id == hex_encode(&[0x33; 32])
                && config.content_session == hex_encode(&[0x55; 32])
                && config.activation_digest.starts_with("sha256:")
            {
                Ok(())
            } else {
                Err("test Lean activation adapter refused config".into())
            }
        }
    }

    impl MissionActivationOracle for MultiActivation {
        fn admit(&self, config: &ActivatedMissionConfig) -> Result<(), String> {
            if [SIGNAL, RELAY, SALVAGE].iter().any(|spec| {
                config.mission_id == spec.mission_id
                    && config.mission_template["descriptor_path"] == spec.path
                    && config.content_epoch == 2
            }) {
                Ok(())
            } else {
                Err("test Lean multi-mission adapter refused config".into())
            }
        }
    }

    impl CanonAdmissionOracle for ExactAdmission {
        fn admit(&self, decision: &CanonDecision) -> Result<(), String> {
            if decision.action == self.action
                && decision.artifact == self.artifact
                && decision.admission.expected_revision == self.revision
            {
                Ok(())
            } else {
                Err("test canon state does not admit this exact transition".into())
            }
        }
    }

    fn digest(byte: u8) -> String {
        format!("sha256:{}", hex_encode(&[byte; 32]))
    }

    fn artifact_ref(content: u8) -> ArtifactRef {
        ArtifactRef {
            mission_id: 7,
            artifact_id: 447,
            source_digest: digest(0x11),
            content_digest: digest(content),
        }
    }

    fn allowed_artifact_ref() -> ArtifactRef {
        artifact_for(SIGNAL)
    }

    fn artifact_for(spec: GameSpec) -> ArtifactRef {
        ArtifactRef {
            mission_id: spec.mission_id,
            artifact_id: spec.artifact_id,
            source_digest: digest(0x11),
            content_digest: sha256_tagged(&game_bytes(spec)),
        }
    }

    fn write_bundle(root: &Path) -> PathBuf {
        write_bundle_with_games(root, &[SIGNAL])
    }

    fn game_bytes(spec: GameSpec) -> Vec<u8> {
        let game_id = spec
            .path
            .strip_prefix("games/")
            .unwrap()
            .strip_suffix(".json")
            .unwrap();
        serde_json::to_vec(&serde_json::json!({
            "format": "POAG1-GAME",
            "schema_version": 1,
            "game_id": game_id,
            "ruleset": spec.ruleset,
            "engine_module": spec.engine,
            "action_limit": spec.action_limit,
            "run_seed": hex_encode(&[spec.seed_byte; 32]),
            "definition": {"owned_by": "Lean"}
        }))
        .unwrap()
    }

    fn schema_bytes(game_paths: &[String]) -> Vec<u8> {
        serde_json::to_vec(&serde_json::json!({
            "format": "POAG1-SCHEMA",
            "schema_version": 1,
            "contract": {
                "manifest_required": ["format", "schema_version", "source_digest", "authority", "artifacts"],
                "artifact_pin_required": ["path", "media_type", "bytes", "sha256", "fnv1a64"],
                "source_digest_pattern": "^sha256:[0-9a-f]{64}$",
                "artifact_sha256_pattern": "^sha256:[0-9a-f]{64}$",
                "bytes32_pattern": "^[0-9a-f]{64}$",
                "fnv1a64_pattern": "^[0-9a-f]{16}$",
                "content_root": {
                    "algorithm": "sha256",
                    "domain": "path-of-angels/content-root/v1\0",
                    "framing": "file_count_be64 || (path_len_be64 || path_utf8 || content_len_be64 || content_bytes)*",
                    "entry_order": "path_ascending",
                    "paths": game_paths
                },
                "activation_digest": {
                    "algorithm": "sha256",
                    "domain": "pathofangels.network/activation-digest/v1\0",
                    "framing": "schema_len_be64 || schema_utf8 || manifest_sha256_raw32 || curator_pubkey_raw32 || content_epoch_be64 || counter_be64 || signature_raw64",
                    "location": "detached verified activation; excluded from manifest preimage"
                },
                "unknown_fields": "reject",
                "unknown_artifacts": "reject"
            }
        }))
        .unwrap()
    }

    fn write_bundle_with_games(root: &Path, specs: &[GameSpec]) -> PathBuf {
        fs::create_dir_all(root.join("games")).unwrap();
        let mut semantic_artifacts = BTreeMap::new();
        for spec in specs {
            semantic_artifacts.insert(spec.path.to_owned(), game_bytes(*spec));
        }
        let game_paths: Vec<String> = semantic_artifacts.keys().cloned().collect();
        let schema = schema_bytes(&game_paths);
        let content_root = content_root_v1(&semantic_artifacts, &game_paths).unwrap();
        let missions: Vec<Value> = specs
            .iter()
            .map(|spec| serde_json::json!({
                "mission_id": spec.mission_id,
                "title": spec.title,
                "engine_module": spec.engine,
                "ruleset": spec.ruleset,
                "reward_class": "non-economic-demo",
                "action_limit": spec.action_limit,
                "privacy_grade": "public",
                "ballot_regime": "none",
                "epoch": 2,
                "federation_id": hex_encode(&[0x33; 32]),
                "content_root": content_root,
                "content_session": hex_encode(&[spec.session_byte; 32]),
                "run_seed": hex_encode(&[spec.seed_byte; 32]),
                "activation": {"state": "detached-signature-required", "digest_source": CONTENT_EPOCH_SCHEMA},
                "budget": {"intel": 3, "supplies": 1, "cohesion": 0, "influence": 0, "score": 50, "relics": 1},
                "allowed_relics": [spec.artifact_id],
                "descriptor_path": spec.path,
                "allowed_beta_discoveries": [artifact_for(*spec)]
            }))
            .collect();
        let fixtures: Vec<Value> = specs
            .iter()
            .map(|spec| {
                serde_json::json!({
                    "id": format!("fixture-{:02}", spec.mission_id),
                    "mission_id": spec.mission_id,
                    "run_seed": hex_encode(&[spec.seed_byte; 32]),
                    "base_world": {"intel": 10, "sequence": 2},
                    "contribution": {"intel": 3, "relics": [spec.artifact_id]},
                    "preview_world": {"intel": 13, "sequence": 3}
                })
            })
            .collect();
        let catalog = serde_json::to_vec(&serde_json::json!({
            "format": "POAG1-CATALOG",
            "schema_version": 1,
            "missions": missions,
            "fixtures": fixtures
        }))
        .unwrap();

        let mut files = vec![
            (SCHEMA_PATH.to_owned(), "application/schema+json", schema),
            (CATALOG_PATH.to_owned(), "application/json", catalog),
        ];
        files.extend(
            semantic_artifacts
                .into_iter()
                .map(|(path, bytes)| (path, "application/json", bytes)),
        );
        for (path, _, bytes) in &files {
            fs::write(root.join(path), bytes).unwrap();
        }
        let artifacts: Vec<Value> = files
            .iter()
            .map(|(path, media_type, bytes)| {
                serde_json::json!({
                    "path": path,
                    "media_type": media_type,
                    "bytes": bytes.len(),
                    "sha256": sha256_tagged(bytes),
                    "fnv1a64": fnv1a64_hex(bytes)
                })
            })
            .collect();
        let manifest = serde_json::to_vec(&serde_json::json!({
            "format": POAG1_FORMAT,
            "schema_version": POAG1_SCHEMA_VERSION,
            "source_digest": digest(0x11),
            "authority": POAG1_AUTHORITY,
            "artifacts": artifacts
        }))
        .unwrap();
        let path = root.join("manifest.json");
        fs::write(&path, manifest).unwrap();
        path
    }

    fn bind_bundle<'a>(bundle: &'a Poag1Bundle, root: &Path) -> DeploymentBoundBundle<'a> {
        let deployment = root.join("poa-devnet.json");
        fs::write(
            &deployment,
            serde_json::to_vec(&serde_json::json!({
                "schema": POA_DEPLOYMENT_MANIFEST_SCHEMA,
                "deployment_domain": POA_DEPLOYMENT_DOMAIN,
                "deployment_id": hex_encode(&[0x77; 32]),
                "federation_id": hex_encode(&[0x33; 32]),
                "committee_epoch": 0,
                "threshold": 1,
                "genesis_sha256": hex_encode(&[0x88; 32]),
                "descriptor": "bundle/genesis.json",
                "policy": {},
                "nodes": []
            }))
            .unwrap(),
        )
        .unwrap();
        bundle.bind_deployment(deployment).unwrap()
    }

    #[test]
    fn loads_exact_bundle_and_prepares_only_emitted_preview() {
        let temp = tempfile::tempdir().unwrap();
        let path = write_bundle(temp.path());
        let bundle = Poag1Bundle::load(&path).unwrap();
        let allowed = allowed_artifact_ref();
        let draft = bundle
            .prepare_mission(7, std::slice::from_ref(&allowed), Some("fixture-07"))
            .unwrap();
        assert_eq!(draft.predeclared_beta_discoveries, vec![allowed]);
        assert_eq!(draft.mission_spec["action_limit"], 5);
        assert_eq!(draft.preview.unwrap().preview_world["intel"], 13);
    }

    #[test]
    fn checked_in_epoch_one_bundle_remains_accepted() {
        let repo = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
        let manifest = repo.join("poa/artifacts/poag1/manifest.json");
        let bundle = Poag1Bundle::load(&manifest).unwrap();
        assert_eq!(bundle.content_epoch(), 1);
        assert_eq!(
            bundle.game_paths().collect::<Vec<_>>(),
            SUPPORTED_GAME_PATHS
        );
        assert_eq!(
            bundle.signal_triangulation()["game_id"],
            "signal-triangulation"
        );
    }

    #[test]
    fn checked_in_epoch_one_replacement_requires_counter_two() {
        let repo = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
        let bundle = Poag1Bundle::load(repo.join("poa/artifacts/poag1/manifest.json")).unwrap();
        let bound = bundle
            .bind_deployment(repo.join("poa/deployments/epoch-1/poa-devnet.json"))
            .unwrap();
        let key = SigningKey::from_bytes(&[0x43; 32]);
        let signer = CuratorSigner::new(&key);
        let pin = CuratorKeyPin::new(&key.public_key());

        let counter_one = signer.sign_content_epoch(&bound, 1, 1).unwrap();
        assert!(matches!(
            counter_one.verify(&bound, &pin, 1, 2),
            Err(CuratorError::ContentEpoch(reason)) if reason == "counter 1 != expected 2"
        ));

        let counter_two = signer.sign_content_epoch(&bound, 1, 2).unwrap();
        counter_two.verify(&bound, &pin, 1, 2).unwrap();
        assert!(signer.sign_content_epoch(&bound, 2, 2).is_err());
    }

    #[test]
    fn loads_bounded_three_mission_epoch_with_one_to_one_descriptors() {
        let temp = tempfile::tempdir().unwrap();
        let manifest = write_bundle_with_games(temp.path(), &[SIGNAL, RELAY, SALVAGE]);
        let bundle = Poag1Bundle::load(manifest).unwrap();
        assert_eq!(bundle.content_epoch(), 2);
        assert_eq!(
            bundle.game_paths().collect::<Vec<_>>(),
            SUPPORTED_GAME_PATHS
        );
        for spec in [SIGNAL, RELAY, SALVAGE] {
            let draft = bundle
                .prepare_mission(
                    spec.mission_id,
                    &[artifact_for(spec)],
                    Some(&format!("fixture-{:02}", spec.mission_id)),
                )
                .unwrap();
            assert_eq!(draft.mission_spec["descriptor_path"], spec.path);
        }
    }

    #[test]
    fn one_signature_activates_each_exact_mission_and_canons_relay() {
        let temp = tempfile::tempdir().unwrap();
        let manifest = write_bundle_with_games(temp.path(), &[SIGNAL, RELAY, SALVAGE]);
        let bundle = Poag1Bundle::load(manifest).unwrap();
        let bound = bind_bundle(&bundle, temp.path());
        let key = SigningKey::from_bytes(&[0x63; 32]);
        let signer = CuratorSigner::new(&key);
        let pin = CuratorKeyPin::new(&key.public_key());
        let envelope = signer.sign_content_epoch(&bound, 2, 5).unwrap();
        let verified = envelope.verify(&bound, &pin, 2, 5).unwrap();
        for spec in [SIGNAL, RELAY, SALVAGE] {
            verified
                .activate_mission(&bound, spec.mission_id, &MultiActivation)
                .unwrap();
        }

        let relay_activation = verified
            .activate_mission(&bound, RELAY.mission_id, &MultiActivation)
            .unwrap();
        let relay_artifact = artifact_for(RELAY);
        let admission = ExactAdmission {
            action: CanonAction::Promote,
            artifact: relay_artifact.clone(),
            revision: 0,
        };
        let decision = CanonDecision::new(
            &relay_activation,
            0,
            5,
            6,
            CanonAction::Promote,
            relay_artifact,
        )
        .unwrap();
        signer
            .sign_canon_decision(decision, &admission)
            .unwrap()
            .verify(&relay_activation, 5, 6, 0, &admission)
            .unwrap();
    }

    #[test]
    fn hostile_fourth_mission_and_excess_fixtures_refuse() {
        let fourth = GameSpec {
            mission_id: 10,
            artifact_id: 450,
            session_byte: 0x58,
            seed_byte: 0x69,
            ..SIGNAL
        };
        let too_many_missions = tempfile::tempdir().unwrap();
        let manifest =
            write_bundle_with_games(too_many_missions.path(), &[SIGNAL, RELAY, SALVAGE, fourth]);
        assert!(matches!(
            Poag1Bundle::load(&manifest),
            Err(CuratorError::Catalog(_))
        ));

        let too_many_fixtures = tempfile::tempdir().unwrap();
        let manifest = write_bundle(too_many_fixtures.path());
        mutate_json(too_many_fixtures.path().join(CATALOG_PATH), |catalog| {
            let fixture = catalog["fixtures"][0].clone();
            let fixtures = catalog["fixtures"].as_array_mut().unwrap();
            fixtures.clear();
            for index in 0..=MAX_FIXTURES_PER_EPOCH {
                let mut next = fixture.clone();
                next["id"] = Value::String(format!("fixture-{index:02}"));
                fixtures.push(next);
            }
        });
        repin_manifest(too_many_fixtures.path(), &manifest);
        assert!(matches!(
            Poag1Bundle::load(&manifest),
            Err(CuratorError::Catalog(_))
        ));
    }

    #[test]
    fn hostile_cross_mission_epoch_identity_and_fixture_seed_refuse() {
        let epoch_mismatch = tempfile::tempdir().unwrap();
        let manifest = write_bundle_with_games(epoch_mismatch.path(), &[SIGNAL, RELAY, SALVAGE]);
        mutate_json(epoch_mismatch.path().join(CATALOG_PATH), |catalog| {
            catalog["missions"][1]["epoch"] = Value::from(3);
        });
        repin_manifest(epoch_mismatch.path(), &manifest);
        assert!(matches!(
            Poag1Bundle::load(&manifest),
            Err(CuratorError::Catalog(_))
        ));

        let duplicate_session = tempfile::tempdir().unwrap();
        let manifest = write_bundle_with_games(duplicate_session.path(), &[SIGNAL, RELAY, SALVAGE]);
        mutate_json(duplicate_session.path().join(CATALOG_PATH), |catalog| {
            catalog["missions"][1]["content_session"] =
                catalog["missions"][0]["content_session"].clone();
        });
        repin_manifest(duplicate_session.path(), &manifest);
        assert!(matches!(
            Poag1Bundle::load(&manifest),
            Err(CuratorError::Catalog(_))
        ));

        let fixture_seed = tempfile::tempdir().unwrap();
        let manifest = write_bundle(fixture_seed.path());
        mutate_json(fixture_seed.path().join(CATALOG_PATH), |catalog| {
            catalog["fixtures"][0]["run_seed"] = Value::String(hex_encode(&[0x99; 32]));
        });
        repin_manifest(fixture_seed.path(), &manifest);
        assert!(matches!(
            Poag1Bundle::load(&manifest),
            Err(CuratorError::Catalog(_))
        ));
    }

    #[test]
    fn hostile_duplicate_mission_and_descriptor_assignments_refuse() {
        let duplicate_id = tempfile::tempdir().unwrap();
        let manifest = write_bundle_with_games(duplicate_id.path(), &[SIGNAL, RELAY, SALVAGE]);
        mutate_json(duplicate_id.path().join(CATALOG_PATH), |catalog| {
            catalog["missions"][1]["mission_id"] = Value::from(SIGNAL.mission_id);
        });
        repin_manifest(duplicate_id.path(), &manifest);
        assert!(matches!(
            Poag1Bundle::load(&manifest),
            Err(CuratorError::Catalog(_))
        ));

        let duplicate_descriptor = tempfile::tempdir().unwrap();
        let manifest =
            write_bundle_with_games(duplicate_descriptor.path(), &[SIGNAL, RELAY, SALVAGE]);
        mutate_json(duplicate_descriptor.path().join(CATALOG_PATH), |catalog| {
            catalog["missions"][1]["descriptor_path"] = Value::String(SIGNAL.path.into());
        });
        repin_manifest(duplicate_descriptor.path(), &manifest);
        assert!(matches!(
            Poag1Bundle::load(&manifest),
            Err(CuratorError::Catalog(_))
        ));
    }

    #[test]
    fn hostile_unknown_catalog_field_and_artifact_refuse() {
        let unknown_field = tempfile::tempdir().unwrap();
        let manifest = write_bundle(unknown_field.path());
        mutate_json(unknown_field.path().join(CATALOG_PATH), |catalog| {
            catalog["missions"][0]["surprise"] = Value::Bool(true);
        });
        repin_manifest(unknown_field.path(), &manifest);
        assert!(matches!(
            Poag1Bundle::load(&manifest),
            Err(CuratorError::Catalog(_))
        ));

        let unknown_artifact = tempfile::tempdir().unwrap();
        let manifest = write_bundle(unknown_artifact.path());
        mutate_json(&manifest, |value| {
            value["artifacts"][2]["path"] = Value::String("games/unbounded-surprise.json".into());
        });
        assert!(matches!(
            Poag1Bundle::load(&manifest),
            Err(CuratorError::Manifest(_))
        ));
    }

    #[test]
    fn hostile_manifest_catalog_and_schema_order_refuse() {
        let manifest_order = tempfile::tempdir().unwrap();
        let manifest = write_bundle_with_games(manifest_order.path(), &[SIGNAL, RELAY, SALVAGE]);
        mutate_json(&manifest, |value| {
            value["artifacts"].as_array_mut().unwrap().swap(2, 3);
        });
        assert!(matches!(
            Poag1Bundle::load(&manifest),
            Err(CuratorError::Manifest(_))
        ));

        let catalog_order = tempfile::tempdir().unwrap();
        let manifest = write_bundle_with_games(catalog_order.path(), &[SIGNAL, RELAY, SALVAGE]);
        mutate_json(catalog_order.path().join(CATALOG_PATH), |catalog| {
            catalog["missions"].as_array_mut().unwrap().swap(0, 1);
        });
        repin_manifest(catalog_order.path(), &manifest);
        assert!(matches!(
            Poag1Bundle::load(&manifest),
            Err(CuratorError::Catalog(_))
        ));

        let schema_order = tempfile::tempdir().unwrap();
        let manifest = write_bundle_with_games(schema_order.path(), &[SIGNAL, RELAY, SALVAGE]);
        mutate_json(schema_order.path().join(SCHEMA_PATH), |schema| {
            schema["contract"]["content_root"]["paths"]
                .as_array_mut()
                .unwrap()
                .swap(0, 1);
        });
        repin_manifest(schema_order.path(), &manifest);
        assert!(matches!(
            Poag1Bundle::load(&manifest),
            Err(CuratorError::Catalog(_))
        ));
    }

    #[test]
    fn self_consistently_repinned_descriptor_tamper_still_refuses() {
        let temp = tempfile::tempdir().unwrap();
        let manifest = write_bundle(temp.path());
        let descriptor_path = temp.path().join(SIGNAL_PATH);
        mutate_json(&descriptor_path, |descriptor| {
            descriptor["ruleset"] = Value::String("attacker-rules-v1".into());
        });
        let descriptor_bytes = fs::read(&descriptor_path).unwrap();
        let mut semantic_artifacts = BTreeMap::new();
        semantic_artifacts.insert(SIGNAL_PATH.to_owned(), descriptor_bytes.clone());
        let game_paths = vec![SIGNAL_PATH.to_owned()];
        let new_root = content_root_v1(&semantic_artifacts, &game_paths).unwrap();
        mutate_json(temp.path().join(CATALOG_PATH), |catalog| {
            catalog["missions"][0]["content_root"] = Value::String(new_root);
            catalog["missions"][0]["allowed_beta_discoveries"][0]["content_digest"] =
                Value::String(sha256_tagged(&descriptor_bytes));
        });
        repin_manifest(temp.path(), &manifest);
        assert!(matches!(
            Poag1Bundle::load(&manifest),
            Err(CuratorError::Catalog(_))
        ));
    }

    #[test]
    fn deployment_binding_refuses_a_catalog_for_another_federation() {
        let temp = tempfile::tempdir().unwrap();
        let bundle = Poag1Bundle::load(write_bundle(temp.path())).unwrap();
        let deployment = temp.path().join("wrong-devnet.json");
        fs::write(
            &deployment,
            serde_json::to_vec(&serde_json::json!({
                "schema": POA_DEPLOYMENT_MANIFEST_SCHEMA,
                "deployment_domain": POA_DEPLOYMENT_DOMAIN,
                "deployment_id": hex_encode(&[0x77; 32]),
                "federation_id": hex_encode(&[0x34; 32]),
                "committee_epoch": 0,
                "threshold": 1,
                "genesis_sha256": hex_encode(&[0x88; 32]),
                "descriptor": "bundle/genesis.json",
                "policy": {},
                "nodes": []
            }))
            .unwrap(),
        )
        .unwrap();
        assert!(matches!(
            bundle.bind_deployment(deployment),
            Err(CuratorError::Deployment(_))
        ));
    }

    #[cfg(unix)]
    #[test]
    fn artifact_symlink_is_refused_even_when_its_target_is_inside_bundle() {
        use std::os::unix::fs::symlink;

        let temp = tempfile::tempdir().unwrap();
        let manifest = write_bundle(temp.path());
        let game = temp.path().join("games/signal-triangulation.json");
        let target = temp.path().join("games/signal-target.json");
        fs::rename(&game, &target).unwrap();
        symlink(&target, &game).unwrap();
        assert!(matches!(
            Poag1Bundle::load(manifest),
            Err(CuratorError::Artifact { .. })
        ));
    }

    #[test]
    fn byte_drift_and_repinning_without_curator_key_both_refuse() {
        let temp = tempfile::tempdir().unwrap();
        let path = write_bundle(temp.path());
        let original = Poag1Bundle::load(&path).unwrap();
        let original_bound = bind_bundle(&original, temp.path());
        let curator_key = SigningKey::from_bytes(&[0x41; 32]);
        let pin = CuratorKeyPin::new(&curator_key.public_key());
        let signed = CuratorSigner::new(&curator_key)
            .sign_content_epoch(&original_bound, 2, 9)
            .unwrap();
        signed.verify(&original_bound, &pin, 2, 9).unwrap();

        // Exact bytes changed while the old manifest pins remain: loader refuses.
        fs::write(
            temp.path().join("games/signal-triangulation.json"),
            br#"{"format":"POAG1-GAME","schema_version":1,"game":"attacker"}"#,
        )
        .unwrap();
        assert!(Poag1Bundle::load(&path).is_err());

        // The attacker re-pins every changed byte and signs with their own key.
        let repinned_path = write_bundle(temp.path());
        let mut catalog: Value =
            serde_json::from_slice(&fs::read(temp.path().join("catalog.json")).unwrap()).unwrap();
        catalog["missions"][0]["title"] = Value::String("attacker payload".into());
        let catalog_bytes = serde_json::to_vec(&catalog).unwrap();
        fs::write(temp.path().join("catalog.json"), catalog_bytes).unwrap();
        // Rebuild pins around the attacker's internally consistent payload.
        let repinned_path = repin_manifest(temp.path(), &repinned_path);
        let attacker_bundle = Poag1Bundle::load(&repinned_path).unwrap();
        let attacker_bound = bind_bundle(&attacker_bundle, temp.path());
        let attacker_key = SigningKey::from_bytes(&[0x42; 32]);
        let attacker_sig = CuratorSigner::new(&attacker_key)
            .sign_content_epoch(&attacker_bound, 2, 9)
            .unwrap();
        assert!(attacker_sig.verify(&attacker_bound, &pin, 2, 9).is_err());
    }

    fn repin_manifest(root: &Path, manifest_path: &Path) -> PathBuf {
        let mut manifest: Value =
            serde_json::from_slice(&fs::read(manifest_path).unwrap()).unwrap();
        for pin in manifest["artifacts"].as_array_mut().unwrap() {
            let path = pin["path"].as_str().unwrap();
            let bytes = fs::read(root.join(path)).unwrap();
            pin["bytes"] = Value::from(bytes.len() as u64);
            pin["sha256"] = Value::String(sha256_tagged(&bytes));
            pin["fnv1a64"] = Value::String(fnv1a64_hex(&bytes));
        }
        fs::write(manifest_path, serde_json::to_vec(&manifest).unwrap()).unwrap();
        manifest_path.to_path_buf()
    }

    fn mutate_json(path: impl AsRef<Path>, mutate: impl FnOnce(&mut Value)) {
        let path = path.as_ref();
        let mut value: Value = serde_json::from_slice(&fs::read(path).unwrap()).unwrap();
        mutate(&mut value);
        fs::write(path, serde_json::to_vec(&value).unwrap()).unwrap();
    }

    #[test]
    fn epoch_signature_refuses_wrong_epoch_counter_key_and_exact_bytes() {
        let temp = tempfile::tempdir().unwrap();
        let bundle = Poag1Bundle::load(write_bundle(temp.path())).unwrap();
        let bound = bind_bundle(&bundle, temp.path());
        let key = SigningKey::from_bytes(&[0x51; 32]);
        let signer = CuratorSigner::new(&key);
        let pin = CuratorKeyPin::new(&key.public_key());
        let envelope = signer.sign_content_epoch(&bound, 2, 33).unwrap();
        envelope.verify(&bound, &pin, 2, 33).unwrap();
        assert!(envelope.verify(&bound, &pin, 3, 33).is_err());
        assert!(envelope.verify(&bound, &pin, 2, 34).is_err());
        assert!(signer.sign_content_epoch(&bound, 12, 33).is_err());
        let wrong_pin = CuratorKeyPin::new(&SigningKey::from_bytes(&[0x52; 32]).public_key());
        assert!(envelope.verify(&bound, &wrong_pin, 2, 33).is_err());

        let mut changed = bundle.manifest_bytes().to_vec();
        changed.push(b'\n');
        let message = content_epoch_signing_message(2, 33, &changed);
        let signature = Signature(parse_hex_array::<64>(&envelope.signature, "signature").unwrap());
        assert!(!dregg_types::verify(
            &key.public_key(),
            &message,
            &signature
        ));
    }

    #[test]
    fn canon_decision_binds_action_revision_epoch_and_exact_artifact() {
        let temp = tempfile::tempdir().unwrap();
        let bundle = Poag1Bundle::load(write_bundle(temp.path())).unwrap();
        let bound = bind_bundle(&bundle, temp.path());
        let key = SigningKey::from_bytes(&[0x61; 32]);
        let signer = CuratorSigner::new(&key);
        let pin = CuratorKeyPin::new(&key.public_key());
        let epoch = signer.sign_content_epoch(&bound, 2, 8).unwrap();
        let verified_epoch = epoch.verify(&bound, &pin, 2, 8).unwrap();
        let activation = verified_epoch
            .activate_mission(&bound, 7, &ExactActivation)
            .unwrap();
        let artifact = allowed_artifact_ref();
        let admission = ExactAdmission {
            action: CanonAction::Promote,
            artifact: artifact.clone(),
            revision: 3,
        };
        let decision =
            CanonDecision::new(&activation, 3, 8, 9, CanonAction::Promote, artifact).unwrap();
        let signed = signer.sign_canon_decision(decision, &admission).unwrap();
        signed.verify(&activation, 8, 9, 3, &admission).unwrap();

        let mut tampered = signed.clone();
        tampered.decision.artifact.content_digest = digest(0x23);
        assert!(tampered.verify(&activation, 8, 9, 3, &admission).is_err());
        let mut superseded = signed.clone();
        superseded.decision.action = CanonAction::Supersede;
        assert!(superseded.verify(&activation, 8, 9, 3, &admission).is_err());
        assert!(signed.verify(&activation, 8, 9, 4, &admission).is_err());
    }

    #[test]
    fn arbitrary_artifact_cannot_be_constructed_as_a_promotion() {
        let temp = tempfile::tempdir().unwrap();
        let bundle = Poag1Bundle::load(write_bundle(temp.path())).unwrap();
        let bound = bind_bundle(&bundle, temp.path());
        let key = SigningKey::from_bytes(&[0x62; 32]);
        let pin = CuratorKeyPin::new(&key.public_key());
        let epoch = CuratorSigner::new(&key)
            .sign_content_epoch(&bound, 2, 1)
            .unwrap();
        let verified_epoch = epoch.verify(&bound, &pin, 2, 1).unwrap();
        let activation = verified_epoch
            .activate_mission(&bound, 7, &ExactActivation)
            .unwrap();
        assert!(matches!(
            CanonDecision::new(
                &activation,
                0,
                1,
                2,
                CanonAction::Promote,
                artifact_ref(0x99),
            ),
            Err(CuratorError::CanonDecision(_))
        ));
    }

    #[test]
    fn catalog_refuses_unpredeclared_or_duplicate_discoveries() {
        let temp = tempfile::tempdir().unwrap();
        let bundle = Poag1Bundle::load(write_bundle(temp.path())).unwrap();
        assert!(matches!(
            bundle.prepare_mission(7, &[artifact_ref(0x23)], None),
            Err(CuratorError::DiscoveryNotAllowed { .. })
        ));
        let exact = allowed_artifact_ref();
        assert!(matches!(
            bundle.prepare_mission(7, &[exact.clone(), exact], None),
            Err(CuratorError::DuplicateDiscovery)
        ));
    }

    #[test]
    fn strict_json_rejects_duplicate_keys_at_any_depth() {
        let error =
            parse_strict_json(br#"{"format":"POAG1-SCHEMA","nested":{"x":1,"x":2}}"#).unwrap_err();
        assert!(error.contains("duplicate JSON object key"));
    }

    #[test]
    fn content_epoch_message_layout_is_pinned_by_hand() {
        let message = content_epoch_signing_message(1, 2, b"abc");
        let mut expected = b"pathofangels.network/content-epoch/v1\0".to_vec();
        expected.extend_from_slice(&1u64.to_be_bytes());
        expected.extend_from_slice(&2u64.to_be_bytes());
        expected.extend_from_slice(&3u64.to_be_bytes());
        expected.extend_from_slice(b"abc");
        assert_eq!(message, expected);
    }

    #[test]
    fn shared_content_epoch_vector_matches_bytes_key_and_signature() {
        let vector: Value =
            serde_json::from_str(include_str!("../test-vectors/content-epoch-v1.json")).unwrap();
        let manifest = vector["manifest_utf8"].as_str().unwrap().as_bytes();
        let epoch = vector["content_epoch"].as_u64().unwrap();
        let counter = vector["counter"].as_u64().unwrap();
        let message = content_epoch_signing_message(epoch, counter, manifest);
        assert_eq!(
            hex_encode(&message),
            vector["message_hex"].as_str().unwrap()
        );
        assert_eq!(
            sha256_tagged(manifest),
            vector["manifest_sha256"].as_str().unwrap()
        );

        let seed = parse_hex_array::<32>(vector["seed_hex"].as_str().unwrap(), "seed").unwrap();
        let key = SigningKey::from_bytes(&seed);
        assert_eq!(
            key.public_key().hex(),
            vector["curator_pubkey"].as_str().unwrap()
        );
        let signature = dregg_types::sign(&key, &message);
        assert_eq!(
            hex_encode(&signature.0),
            vector["signature"].as_str().unwrap()
        );
        assert!(dregg_types::verify(&key.public_key(), &message, &signature));

        let envelope = ContentEpochEnvelope {
            schema: CONTENT_EPOCH_SCHEMA.into(),
            manifest_sha256: vector["manifest_sha256"].as_str().unwrap().into(),
            curator_pubkey: vector["curator_pubkey"].as_str().unwrap().into(),
            content_epoch: epoch,
            counter,
            signature: vector["signature"].as_str().unwrap().into(),
        };
        assert_eq!(
            format!("sha256:{}", hex_encode(&envelope.signed_digest().unwrap())),
            vector["activation_digest"].as_str().unwrap()
        );
    }

    #[test]
    fn shared_canon_promotion_vector_matches_bytes_key_and_signature() {
        let vector: Value =
            serde_json::from_str(include_str!("../test-vectors/canon-promotion-v1.json")).unwrap();
        let artifact: ArtifactRef = serde_json::from_value(vector["artifact"].clone()).unwrap();
        let decision = CanonDecision {
            schema: CANON_DECISION_SCHEMA.into(),
            admission: serde_json::from_value(vector["admission"].clone()).unwrap(),
            action: CanonAction::Promote,
            artifact,
        };
        let message = decision.signing_message();
        assert_eq!(
            hex_encode(&message),
            vector["message_hex"].as_str().unwrap()
        );
        let seed = parse_hex_array::<32>(vector["seed_hex"].as_str().unwrap(), "seed").unwrap();
        let key = SigningKey::from_bytes(&seed);
        assert_eq!(
            key.public_key().hex(),
            vector["curator_pubkey"].as_str().unwrap()
        );
        let signature = dregg_types::sign(&key, &message);
        assert_eq!(
            hex_encode(&signature.0),
            vector["signature"].as_str().unwrap()
        );
        assert!(dregg_types::verify(&key.public_key(), &message, &signature));
    }

    #[test]
    fn production_deployment_verifier_matches_js_identity_vectors() {
        let repo = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
        let main = tempfile::tempdir().unwrap();
        let scope = PoaDeploymentScope::load_verified(
            repo.join("poa/deployments/epoch-1/poa-devnet.json"),
            repo.join("poa/deployments/epoch-1/bundle/genesis.json"),
            main.path(),
        )
        .unwrap();
        assert_eq!(
            scope.manifest_sha256(),
            "427a7a33ae19e450e2b9eb86453ac247b94d47725e29f8d470f0e9cad8073510"
        );
        assert_eq!(
            scope.policy_sha256(),
            "8346263cf2fd50210353dca763dfb8f1271e1154e766ca93553ef3abc12a65ca"
        );
        assert_eq!(
            scope.deployment_digest(),
            "5891c919acca76af3c553d157768d9f274b71610ed3b09bb09c954da2c7aa67e"
        );
    }

    #[test]
    fn production_deployment_refuses_weakened_policy_and_main_identity_reuse() {
        let repo = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
        let root = tempfile::tempdir().unwrap();
        let main = tempfile::tempdir().unwrap();
        fs::create_dir_all(root.path().join("bundle")).unwrap();
        let manifest_path = root.path().join("poa-devnet.json");
        let genesis_path = root.path().join("bundle/genesis.json");
        fs::copy(
            repo.join("poa/deployments/epoch-1/poa-devnet.json"),
            &manifest_path,
        )
        .unwrap();
        fs::copy(
            repo.join("poa/deployments/epoch-1/bundle/genesis.json"),
            &genesis_path,
        )
        .unwrap();

        let mut weakened: Value =
            serde_json::from_slice(&fs::read(&manifest_path).unwrap()).unwrap();
        weakened["policy"]["prove_turns"] = Value::Bool(false);
        fs::write(&manifest_path, serde_json::to_vec(&weakened).unwrap()).unwrap();
        let error = PoaDeploymentScope::load_verified(&manifest_path, &genesis_path, main.path())
            .unwrap_err()
            .to_string();
        assert!(error.contains("weakened"), "{error}");

        fs::copy(
            repo.join("poa/deployments/epoch-1/poa-devnet.json"),
            &manifest_path,
        )
        .unwrap();
        fs::copy(&genesis_path, main.path().join("genesis.json")).unwrap();
        let error = PoaDeploymentScope::load_verified(&manifest_path, &genesis_path, main.path())
            .unwrap_err()
            .to_string();
        assert!(error.contains("copied from the main federation"), "{error}");
    }
}
