//! Sentyr-facing curation over the Lean-emitted POAG1 content bundle.
//!
//! This is intentionally an authority/IO edge, not a second game engine. The
//! bundle's mission specs, beta discoveries, contribution previews, and world
//! states are retained as the exact JSON emitted by Lean. Rust verifies the
//! byte-pinned container, selects values, and delegates signatures to the
//! canonical `dregg-types` Ed25519 primitive.

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

const CONTENT_EPOCH_DOMAIN: &[u8] = b"pathofangels.network/content-epoch/v1\0";
const CANON_DECISION_DOMAIN: &[u8] = b"pathofangels.network/canon-promotion/v1\0";
const CONTENT_ROOT_DOMAIN: &[u8] = b"path-of-angels/content-root/v1\0";
const ACTIVATION_DIGEST_DOMAIN: &[u8] = b"pathofangels.network/activation-digest/v1\0";
const MAX_MANIFEST_BYTES: u64 = 1024 * 1024;
const MAX_ARTIFACT_BYTES: u64 = 16 * 1024 * 1024;

const REQUIRED_ARTIFACTS: [(&str, &str, &str); 3] = [
    ("schema.json", "application/schema+json", "POAG1-SCHEMA"),
    ("catalog.json", "application/json", "POAG1-CATALOG"),
    (
        "games/signal-triangulation.json",
        "application/json",
        "POAG1-GAME",
    ),
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
    signal_triangulation: Value,
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
        Ok(Self {
            deployment_id: deployment_id.to_owned(),
            federation_id: federation_id.to_owned(),
        })
    }

    pub fn deployment_id(&self) -> &str {
        &self.deployment_id
    }

    pub fn federation_id(&self) -> &str {
        &self.federation_id
    }
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
}

#[derive(Clone, Debug)]
struct MissionIndex {
    exact_json: Value,
    federation_id: String,
    content_root: String,
    content_session: String,
    allowed_beta_discoveries: Vec<ArtifactRef>,
}

#[derive(Clone, Debug)]
struct FixtureIndex {
    mission_id: u64,
    base_world: Value,
    contribution: Value,
    preview_world: Value,
}

type CatalogIndex = (BTreeMap<u64, MissionIndex>, BTreeMap<String, FixtureIndex>);

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
        validate_manifest(&manifest)?;

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

        let schema =
            parse_artifact_json(&manifest_path, &artifacts, "schema.json", "POAG1-SCHEMA")?;
        let catalog =
            parse_artifact_json(&manifest_path, &artifacts, "catalog.json", "POAG1-CATALOG")?;
        let signal_triangulation = parse_artifact_json(
            &manifest_path,
            &artifacts,
            "games/signal-triangulation.json",
            "POAG1-GAME",
        )?;
        let content_root = content_root_v1(&artifacts)?;
        let signal_digest = sha256_tagged(
            artifacts
                .get("games/signal-triangulation.json")
                .expect("required artifact set was checked"),
        );
        let (missions, fixtures) = index_catalog(
            &catalog,
            &content_root,
            &manifest.source_digest,
            &signal_digest,
        )?;

        Ok(Self {
            manifest_path,
            manifest_sha256: sha256_tagged(&manifest_bytes),
            manifest_bytes,
            manifest,
            artifacts,
            schema,
            catalog,
            signal_triangulation,
            missions,
            fixtures,
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
        &self.signal_triangulation
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
    ) -> ContentEpochEnvelope {
        let bundle = bound.bundle;
        let message =
            content_epoch_signing_message(content_epoch, counter, bundle.manifest_bytes());
        let signature = dregg_types::sign(self.key, &message);
        ContentEpochEnvelope {
            schema: CONTENT_EPOCH_SCHEMA.into(),
            manifest_sha256: bundle.manifest_sha256.clone(),
            curator_pubkey: self.key.public_key().hex(),
            content_epoch,
            counter,
            signature: hex_encode(&signature.0),
        }
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

fn validate_manifest(manifest: &Poag1Manifest) -> Result<(), CuratorError> {
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
    if manifest.artifacts.len() != REQUIRED_ARTIFACTS.len() {
        return Err(CuratorError::Manifest(format!(
            "artifact set has {}, expected exactly {}",
            manifest.artifacts.len(),
            REQUIRED_ARTIFACTS.len()
        )));
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
        let expected = REQUIRED_ARTIFACTS
            .iter()
            .find(|(path, _, _)| *path == pin.path)
            .ok_or_else(|| CuratorError::Manifest(format!("unknown artifact {}", pin.path)))?;
        if pin.media_type != expected.1 {
            return Err(CuratorError::Manifest(format!(
                "artifact {} media type {} != {}",
                pin.path, pin.media_type, expected.1
            )));
        }
    }
    Ok(())
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

fn index_catalog(
    catalog: &Value,
    authenticated_content_root: &str,
    authenticated_source_digest: &str,
    authenticated_signal_digest: &str,
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
    let mut missions = BTreeMap::new();
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
        obj.get("epoch").and_then(Value::as_u64).ok_or_else(|| {
            CuratorError::Catalog(format!("mission {mission_id} epoch is not a u64"))
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
        let run_seed = obj
            .get("run_seed")
            .and_then(Value::as_str)
            .ok_or_else(|| CuratorError::Catalog("run_seed is not a string".into()))?;
        parse_hex_array::<32>(run_seed, "run_seed")?;
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
        let descriptor_path = obj
            .get("descriptor_path")
            .and_then(Value::as_str)
            .ok_or_else(|| CuratorError::Catalog("descriptor_path is not a string".into()))?;
        if descriptor_path != "games/signal-triangulation.json" {
            return Err(CuratorError::Catalog(format!(
                "mission {mission_id} names unpinned descriptor {descriptor_path}"
            )));
        }
        let allowed_relics = obj
            .get("allowed_relics")
            .and_then(Value::as_array)
            .ok_or_else(|| {
                CuratorError::Catalog(format!("mission {mission_id} lacks allowed_relics"))
            })?;
        let mut relics = BTreeSet::new();
        for relic in allowed_relics {
            let relic = relic.as_u64().ok_or_else(|| {
                CuratorError::Catalog(format!("mission {mission_id} has nonnumeric allowed relic"))
            })?;
            if !relics.insert(relic) {
                return Err(CuratorError::Catalog(format!(
                    "mission {mission_id} has duplicate allowed relic {relic}"
                )));
            }
        }
        let allowed_values = obj
            .get("allowed_beta_discoveries")
            .and_then(Value::as_array)
            .ok_or_else(|| {
                CuratorError::Catalog(format!(
                    "mission {mission_id} lacks allowed_beta_discoveries"
                ))
            })?;
        let mut allowed_beta_discoveries = Vec::with_capacity(allowed_values.len());
        let mut unique = BTreeSet::new();
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
                || artifact.content_digest != authenticated_signal_digest
            {
                return Err(CuratorError::Catalog(format!(
                    "mission {mission_id} artifact does not bind the authenticated source and descriptor bytes"
                )));
            }
            if !unique.insert(artifact.clone()) {
                return Err(CuratorError::Catalog(format!(
                    "mission {mission_id} has duplicate artifact ref"
                )));
            }
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

    let mut fixtures = BTreeMap::new();
    if let Some(fixture_values) = object.get("fixtures") {
        let fixture_values = fixture_values
            .as_array()
            .ok_or_else(|| CuratorError::Catalog("fixtures is not an array".into()))?;
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
    Ok((missions, fixtures))
}

/// POAG1 v1 content root. Schema/catalog/manifest envelopes are intentionally
/// excluded, avoiding a self-hash cycle; only executable game program/assets
/// participate. V1 admits exactly the one required signal descriptor.
fn content_root_v1(artifacts: &BTreeMap<String, Vec<u8>>) -> Result<String, CuratorError> {
    let semantic_paths = ["games/signal-triangulation.json"];
    let mut preimage = Vec::new();
    preimage.extend_from_slice(CONTENT_ROOT_DOMAIN);
    preimage.extend_from_slice(&(semantic_paths.len() as u64).to_be_bytes());
    for path in semantic_paths {
        let contents = artifacts.get(path).ok_or_else(|| CuratorError::Artifact {
            path: path.into(),
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

    const TEST_GAME: &[u8] =
        br#"{"format":"POAG1-GAME","schema_version":1,"game":"signal-triangulation"}"#;

    struct ExactAdmission {
        action: CanonAction,
        artifact: ArtifactRef,
        revision: u64,
    }

    struct ExactActivation;

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
        ArtifactRef {
            mission_id: 7,
            artifact_id: 447,
            source_digest: digest(0x11),
            content_digest: sha256_tagged(TEST_GAME),
        }
    }

    fn write_bundle(root: &Path) -> PathBuf {
        fs::create_dir_all(root.join("games")).unwrap();
        let schema = br#"{"format":"POAG1-SCHEMA","schema_version":1,"definitions":{}}"#;
        let game = TEST_GAME;
        let mut semantic_artifacts = BTreeMap::new();
        semantic_artifacts.insert("games/signal-triangulation.json".to_owned(), game.to_vec());
        let content_root = content_root_v1(&semantic_artifacts).unwrap();
        let catalog = serde_json::to_vec(&serde_json::json!({
            "format": "POAG1-CATALOG",
            "schema_version": 1,
            "missions": [{
                "mission_id": 7,
                "title": "Deck 447 intercept",
                "engine_module": "Dregg2.Games.PathOfAngels.SignalTriangulation",
                "ruleset": "signal-triangulation-v1",
                "reward_class": "non-economic-demo",
                "action_limit": 5,
                "privacy_grade": "public",
                "ballot_regime": "none",
                "epoch": 2,
                "federation_id": hex_encode(&[0x33; 32]),
                "content_root": content_root,
                "content_session": hex_encode(&[0x55; 32]),
                "run_seed": hex_encode(&[0x66; 32]),
                "activation": {
                    "state": "detached-signature-required",
                    "digest_source": "POA-CONTENT-EPOCH-SIGNATURE-V1"
                },
                "budget": {"intel": 3, "supplies": 1, "cohesion": 0, "influence": 0, "score": 50, "relics": 1},
                "allowed_relics": [99],
                "descriptor_path": "games/signal-triangulation.json",
                "allowed_beta_discoveries": [allowed_artifact_ref()]
            }],
            "fixtures": [{
                "id": "solved-one",
                "mission_id": 7,
                "run_seed": hex_encode(&[0x66; 32]),
                "base_world": {"intel": 10, "sequence": 2},
                "contribution": {"intel": 3, "relics": [99]},
                "preview_world": {"intel": 13, "sequence": 3}
            }]
        }))
        .unwrap();

        let files = [
            ("schema.json", "application/schema+json", schema.as_slice()),
            ("catalog.json", "application/json", catalog.as_slice()),
            ("games/signal-triangulation.json", "application/json", game),
        ];
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
            "format": "POAG1",
            "schema_version": 1,
            "source_digest": digest(0x11),
            "authority": "Dregg2.Games.PathOfAngels",
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
            .prepare_mission(7, std::slice::from_ref(&allowed), Some("solved-one"))
            .unwrap();
        assert_eq!(draft.predeclared_beta_discoveries, vec![allowed]);
        assert_eq!(draft.mission_spec["action_limit"], 5);
        assert_eq!(draft.preview.unwrap().preview_world["intel"], 13);
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
        let signed = CuratorSigner::new(&curator_key).sign_content_epoch(&original_bound, 4, 9);
        signed.verify(&original_bound, &pin, 4, 9).unwrap();

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
        let attacker_sig =
            CuratorSigner::new(&attacker_key).sign_content_epoch(&attacker_bound, 4, 9);
        assert!(attacker_sig.verify(&attacker_bound, &pin, 4, 9).is_err());
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

    #[test]
    fn epoch_signature_refuses_wrong_epoch_counter_key_and_exact_bytes() {
        let temp = tempfile::tempdir().unwrap();
        let bundle = Poag1Bundle::load(write_bundle(temp.path())).unwrap();
        let bound = bind_bundle(&bundle, temp.path());
        let key = SigningKey::from_bytes(&[0x51; 32]);
        let signer = CuratorSigner::new(&key);
        let pin = CuratorKeyPin::new(&key.public_key());
        let envelope = signer.sign_content_epoch(&bound, 12, 33);
        envelope.verify(&bound, &pin, 12, 33).unwrap();
        assert!(envelope.verify(&bound, &pin, 13, 33).is_err());
        assert!(envelope.verify(&bound, &pin, 12, 34).is_err());
        let wrong_pin = CuratorKeyPin::new(&SigningKey::from_bytes(&[0x52; 32]).public_key());
        assert!(envelope.verify(&bound, &wrong_pin, 12, 33).is_err());

        let mut changed = bundle.manifest_bytes().to_vec();
        changed.push(b'\n');
        let message = content_epoch_signing_message(12, 33, &changed);
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
        let epoch = signer.sign_content_epoch(&bound, 2, 8);
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
        let epoch = CuratorSigner::new(&key).sign_content_epoch(&bound, 2, 1);
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
}
