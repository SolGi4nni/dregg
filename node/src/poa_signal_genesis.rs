//! Operator-only activation of the Lean-emitted Path of Angels Signal head.
//!
//! This module owns ceremony plumbing, not game semantics. It authenticates the
//! exact deployment/genesis/content tuple with `poa-curator`, asks the one Lean
//! NetworkGenesis export for the complete head image, byte-canonically parses
//! that direct reply, and performs one atomic empty-or-identical store change.

use std::fs;
use std::path::{Path, PathBuf};

use dregg_lean_ffi::poa_network_genesis_ffi::{
    PoaNetworkGenesisVerdict, evaluate_poa_network_genesis, poa_network_genesis_available,
};
use dregg_persist::{PersistentStore, PoaSignalGenesisInitOutcome, PoaSignalHeadV1};
use poa_curator::{
    ContentEpochEnvelope, CuratorKeyPin, DeploymentBoundBundle, PoaDeploymentScope, Poag1Bundle,
    VerifiedContentEpoch,
};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use sha2::{Digest as _, Sha256};

const SIGNAL_MISSION_ID: u64 = 1;
const SIGNAL_PATH: &str = "games/signal-triangulation.json";
const INPUT_FORMAT: &str = "POA-SIGNAL-GENESIS-IN-2";
const OUTPUT_FORMAT: &str = "POA-SIGNAL-GENESIS-OUT-2";
const ZERO_HEX: &str = "0000000000000000000000000000000000000000000000000000000000000000";
/// `Emit.UNBOUND_RUN_SEED` — the run-seed slot of a template mission: thirty-two
/// zero bytes, meaning "no live draw has happened". It is not a seed and draws
/// nothing; `Judged.admissionChecks` refuses it outright as a live seed.
///
/// Spelled separately from [`ZERO_HEX`] on purpose. They are equal today and mean
/// different things, and a reader who sees `ZERO_HEX` here would reasonably think
/// the field was merely unset.
const UNBOUND_RUN_SEED: &str = ZERO_HEX;
/// `Emit.UNBOUND_TARGET` — the non-playable target paired with
/// [`UNBOUND_RUN_SEED`] in `Emit.signalTemplateConfig`.
///
/// This is not content and is deliberately not read from the public Signal
/// descriptor: publishing a live target publishes the answer. Lean independently
/// rebuilds the template config and requires this exact value, while judged play
/// replaces both target and run seed from the committed slot secret and player key.
const UNBOUND_TARGET: SignalCode = SignalCode {
    low: 0,
    mid: 0,
    high: 0,
};

#[derive(Clone, Debug)]
pub struct PoaSignalGenesisArgs {
    pub data_dir: PathBuf,
    pub deployment_manifest: PathBuf,
    pub genesis: PathBuf,
    pub main_data_dir: PathBuf,
    pub poag1_manifest: PathBuf,
    pub content_envelope: PathBuf,
    pub curator_key_pin: PathBuf,
    pub expected_content_epoch: u64,
    pub expected_activation_counter: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PoaSignalGenesisReport {
    pub outcome: PoaSignalGenesisInitOutcome,
    pub authority_id: [u8; 32],
    pub deployment_digest: [u8; 32],
    pub head_digest: [u8; 32],
}

/// Run the production ceremony. Missing Lean linkage is a named refusal and
/// happens before the persistent store is opened.
pub fn initialize_poa_signal_genesis(
    args: &PoaSignalGenesisArgs,
) -> Result<PoaSignalGenesisReport, String> {
    initialize_poa_signal_genesis_with(args, |wire| {
        if !poa_network_genesis_available() {
            return Err("dregg_poa_network_genesis is absent; PoA Signal genesis refuses".into());
        }
        match evaluate_poa_network_genesis(wire)? {
            PoaNetworkGenesisVerdict::Emitted(output) => Ok(output),
            PoaNetworkGenesisVerdict::Rejected => {
                Err("Lean refused the authenticated PoA Signal genesis tuple".into())
            }
        }
    })
}

/// Rebind an installed PoA head to the exact immutable runtime artifacts on
/// every boot. Generic nodes with no PoA head need no PoA environment. Once a
/// head exists, both paths are mandatory: silently falling back to the mutable
/// data-dir genesis would let a restart reinterpret the persisted authority.
pub fn verify_poa_signal_boot_from_env(
    store: &PersistentStore,
    data_dir: &Path,
    active_federation_id: [u8; 32],
    runtime_genesis_bytes: &[u8],
) -> Result<(), String> {
    let Some(head) = store
        .load_singular_poa_signal_head()
        .map_err(|error| format!("PoA Signal boot audit failed: {error}"))?
    else {
        return Ok(());
    };
    let manifest = std::env::var_os("POA_DEPLOYMENT_MANIFEST")
        .map(PathBuf::from)
        .ok_or_else(|| {
            "persisted PoA Signal head requires POA_DEPLOYMENT_MANIFEST at boot".to_owned()
        })?;
    let main_data_dir = std::env::var_os("POA_MAIN_DATA_DIR")
        .map(PathBuf::from)
        .ok_or_else(|| "persisted PoA Signal head requires POA_MAIN_DATA_DIR at boot".to_owned())?;
    verify_poa_signal_boot_identity(
        &head,
        data_dir,
        active_federation_id,
        runtime_genesis_bytes,
        &manifest,
        &main_data_dir,
    )?;
    let replay =
        crate::poa_signal_adapter::audit_persisted_signal_semantics(store, head.authority_id())
            .map_err(|error| format!("PoA Signal semantic boot replay refused: {error}"))?;
    tracing::info!(
        transitions = replay.transition_count,
        retained_genesis = %dregg_types::hex_encode(&replay.retained_genesis_digest),
        rebuilt_head = %dregg_types::hex_encode(&replay.rebuilt_head_digest),
        "rebuilt persisted PoA Signal history through native Lean"
    );
    Ok(())
}

fn verify_poa_signal_boot_identity(
    head: &PoaSignalHeadV1,
    data_dir: &Path,
    active_federation_id: [u8; 32],
    runtime_genesis_bytes: &[u8],
    manifest_path: &Path,
    main_data_dir: &Path,
) -> Result<(), String> {
    let root = manifest_path
        .parent()
        .ok_or_else(|| "PoA deployment manifest has no root".to_owned())?;
    let genesis_path = root.join("bundle/genesis.json");
    let deployment = PoaDeploymentScope::load_verified(manifest_path, &genesis_path, main_data_dir)
        .map_err(|error| format!("PoA boot deployment tuple refused: {error}"))?;
    deployment
        .verify_serving_data_dir(data_dir, Some(runtime_genesis_bytes))
        .map_err(|error| format!("PoA boot serving directory refused: {error}"))?;
    let expected_authority = parse_hex32(deployment.federation_id(), "deployment federation_id")?;
    let expected_deployment = parse_hex32(deployment.deployment_digest(), "deployment digest")?;
    if active_federation_id != expected_authority
        || head.authority_id() != expected_authority
        || head.deployment_digest() != expected_deployment
    {
        return Err(
            "persisted PoA Signal head does not bind the current exact manifest/genesis identity"
                .into(),
        );
    }
    Ok(())
}

fn initialize_poa_signal_genesis_with(
    args: &PoaSignalGenesisArgs,
    evaluate: impl FnOnce(&str) -> Result<String, String>,
) -> Result<PoaSignalGenesisReport, String> {
    let data_metadata = fs::metadata(&args.data_dir)
        .map_err(|error| format!("PoA data directory is unavailable: {error}"))?;
    if !data_metadata.is_dir() {
        return Err("PoA data path is not a directory".into());
    }

    let deployment = PoaDeploymentScope::load_verified(
        &args.deployment_manifest,
        &args.genesis,
        &args.main_data_dir,
    )
    .map_err(|error| format!("PoA deployment/genesis tuple refused: {error}"))?;
    deployment
        .verify_serving_data_dir(&args.data_dir, None)
        .map_err(|error| format!("PoA serving directory refused: {error}"))?;

    let bundle = Poag1Bundle::load(&args.poag1_manifest)
        .map_err(|error| format!("POAG1 bundle refused: {error}"))?;
    let bound = bundle
        .bind_deployment_scope(deployment)
        .map_err(|error| format!("POAG1 deployment binding refused: {error}"))?;
    let envelope = ContentEpochEnvelope::load(&args.content_envelope)
        .map_err(|error| format!("PoA content envelope refused: {error}"))?;
    let key_pin = CuratorKeyPin::load(&args.curator_key_pin)
        .map_err(|error| format!("PoA curator key pin refused: {error}"))?;
    let verified = envelope
        .verify(
            &bound,
            &key_pin,
            args.expected_content_epoch,
            args.expected_activation_counter,
        )
        .map_err(|error| format!("PoA content signature refused: {error}"))?;

    let input = build_network_genesis_input(&bound, &verified)?;
    let emitted = evaluate(&input)?;
    let output = parse_exact_network_genesis_output(&emitted)?;
    output.binds_exact_tuple(&bound, &verified)?;
    let head = output.into_head()?;

    // Opening occurs only after every immutable byte and the Lean export have
    // been accepted. The Signal slot ceremony verifies its envelope against the
    // store's independently persisted curator pin; installing only the head
    // leaves an apparently initialized authority that can never open a slot.
    // Pin first: if the subsequent singular-head check refuses a nonempty store,
    // the only retained mutation is this already signature-authenticated,
    // immutable trust root. No Signal state becomes playable. Both operations
    // are exact-retry safe.
    let store = PersistentStore::open(&args.data_dir.join("dregg.redb"))
        .map_err(|error| format!("failed to open PoA store: {error}"))?;
    store
        .install_poa_world_curator_pin_v1(verified.public_key().0)
        .map_err(|error| format!("PoA curator pin installation refused: {error}"))?;
    let outcome = store
        .initialize_poa_signal_head_if_empty_or_identical(&head)
        .map_err(|error| format!("PoA Signal store initialization refused: {error}"))?;
    store
        .audit_poa_signal_state()
        .map_err(|error| format!("PoA Signal post-initialization audit failed: {error}"))?;
    Ok(PoaSignalGenesisReport {
        outcome,
        authority_id: head.authority_id(),
        deployment_digest: head.deployment_digest(),
        head_digest: head.digest(),
    })
}

#[derive(Serialize)]
struct GenesisInput {
    format: &'static str,
    deployment: GenesisDeployment,
    content: GenesisContent,
    config: SignalConfig,
    initial: InitialState,
}

#[derive(Serialize)]
struct GenesisDeployment {
    schema: &'static str,
    deployment_domain: &'static str,
    deployment_id: String,
    deployment_digest: String,
    federation_id: String,
    genesis_sha256: String,
    manifest_sha256: String,
    policy_sha256: String,
}

#[derive(Serialize)]
struct GenesisContent {
    signature_schema: String,
    manifest_sha256: String,
    content_root: String,
    activation_digest: String,
    source_digest: String,
    signal_content_digest: String,
    curator_key: String,
    content_epoch: u64,
    activation_counter: u64,
}

#[derive(Serialize)]
struct SignalConfig {
    /// ⚑ The game tag `GameConfigWire.toJson` emits first. Genesis installs the very
    /// bytes `NetworkJudgeWire.decodeGameConfig` will later re-decode, so an untagged
    /// blob installed here would be a head no judge could read.
    game: &'static str,
    target: SignalCode,
    mission: SignalMission,
    reward: Contribution,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
struct SignalCode {
    low: u64,
    mid: u64,
    high: u64,
}

#[derive(Serialize)]
struct SignalMission {
    mission_id: u64,
    artifact: SignalArtifact,
    epoch: u64,
    federation_id: String,
    content_root: String,
    activation_digest: String,
    content_session: String,
    run_seed: String,
    budget: MissionBudget,
    allowed_relics: Vec<u64>,
    privacy: String,
    ballot: String,
}

#[derive(Serialize)]
struct SignalArtifact {
    mission_id: u64,
    artifact_id: u64,
    source_digest: String,
    content_digest: String,
}

#[derive(Clone, Serialize)]
struct MissionBudget {
    intel: u64,
    supplies: u64,
    cohesion: u64,
    influence: u64,
    score: u64,
    relics: u64,
}

#[derive(Serialize)]
struct Contribution {
    intel: u64,
    supplies: u64,
    cohesion: u64,
    influence: u64,
    score: u64,
    relics: Vec<u64>,
}

#[derive(Serialize)]
struct InitialState {
    world: EmptyWorld,
    known: Vec<Value>,
    alpha: Vec<Value>,
    superseded: Vec<Value>,
    consumed_runs: Vec<Value>,
    player_counters: Vec<Value>,
    canon_revision: u64,
    curator_counter: u64,
    transition_count: u64,
    last_transition_digest: &'static str,
}

#[derive(Serialize)]
struct EmptyWorld {
    intel: u64,
    supplies: u64,
    cohesion: u64,
    influence: u64,
    score: u64,
    discovered_relics: Vec<u64>,
    beta_artifacts: Vec<Value>,
    sequence: u64,
}

fn build_network_genesis_input(
    bound: &DeploymentBoundBundle<'_>,
    verified: &VerifiedContentEpoch<'_>,
) -> Result<String, String> {
    let bundle = bound.bundle();
    let mission = bundle
        .catalog()
        .get("missions")
        .and_then(Value::as_array)
        .and_then(|missions| {
            missions.iter().find(|mission| {
                mission.get("mission_id").and_then(Value::as_u64) == Some(SIGNAL_MISSION_ID)
            })
        })
        .and_then(Value::as_object)
        .ok_or_else(|| "authenticated POAG1 catalog lacks Signal mission 1".to_owned())?;
    let descriptor = bundle
        .signal_triangulation()
        .as_object()
        .ok_or_else(|| "authenticated Signal descriptor is not an object".to_owned())?;
    let target = template_target_for_authenticated_descriptor(descriptor)?;
    let discoveries = mission
        .get("allowed_beta_discoveries")
        .and_then(Value::as_array)
        .filter(|values| values.len() == 1)
        .ok_or_else(|| "Signal mission must carry one authenticated beta artifact".to_owned())?;
    let artifact = discoveries[0]
        .as_object()
        .ok_or_else(|| "Signal beta artifact is not an object".to_owned())?;
    let artifact = SignalArtifact {
        mission_id: required_u64(artifact, "mission_id")?,
        artifact_id: required_u64(artifact, "artifact_id")?,
        source_digest: bare_sha(required_str(artifact, "source_digest")?, "artifact source")?,
        content_digest: bare_sha(
            required_str(artifact, "content_digest")?,
            "artifact content",
        )?,
    };
    let budget_object = mission
        .get("budget")
        .and_then(Value::as_object)
        .ok_or_else(|| "Signal mission budget is not an object".to_owned())?;
    let budget = MissionBudget {
        intel: required_u64(budget_object, "intel")?,
        supplies: required_u64(budget_object, "supplies")?,
        cohesion: required_u64(budget_object, "cohesion")?,
        influence: required_u64(budget_object, "influence")?,
        score: required_u64(budget_object, "score")?,
        relics: required_u64(budget_object, "relics")?,
    };
    let allowed_relics = mission
        .get("allowed_relics")
        .and_then(Value::as_array)
        .ok_or_else(|| "Signal allowed_relics is not an array".to_owned())?
        .iter()
        .map(|value| {
            value
                .as_u64()
                .ok_or_else(|| "Signal allowed relic is not a u64".to_owned())
        })
        .collect::<Result<Vec<_>, _>>()?;
    let signal_content_digest = bundle
        .manifest()
        .artifacts
        .iter()
        .find(|pin| pin.path == SIGNAL_PATH)
        .map(|pin| bare_sha(&pin.sha256, "Signal artifact digest"))
        .transpose()?
        .ok_or_else(|| "POAG1 manifest does not pin Signal descriptor".to_owned())?;

    let input = GenesisInput {
        format: INPUT_FORMAT,
        deployment: GenesisDeployment {
            schema: poa_curator::POA_DEPLOYMENT_MANIFEST_SCHEMA,
            deployment_domain: poa_curator::POA_DEPLOYMENT_DOMAIN,
            deployment_id: bound.deployment().deployment_id().to_owned(),
            deployment_digest: bound.deployment().deployment_digest().to_owned(),
            federation_id: bound.deployment().federation_id().to_owned(),
            genesis_sha256: bound.deployment().genesis_sha256().to_owned(),
            manifest_sha256: bound.deployment().manifest_sha256().to_owned(),
            policy_sha256: bound.deployment().policy_sha256().to_owned(),
        },
        content: GenesisContent {
            signature_schema: verified.envelope().schema.clone(),
            manifest_sha256: bare_sha(bundle.manifest_sha256(), "manifest digest")?,
            content_root: bare_sha(bundle.content_root(), "content root")?,
            activation_digest: bare_sha(&verified.activation_digest(), "activation digest")?,
            source_digest: bare_sha(&bundle.manifest().source_digest, "source digest")?,
            signal_content_digest,
            curator_key: verified.envelope().curator_pubkey.clone(),
            content_epoch: verified.envelope().content_epoch,
            activation_counter: verified.envelope().counter,
        },
        config: SignalConfig {
            game: crate::poa_signal_adapter::POA_GAME_TAG_SIGNAL,
            // Genesis authenticates a mission TEMPLATE, not a live instance.
            // Lean's `expectedConfig` independently emits the same sentinel and
            // compares the complete config byte-for-byte. The slot ceremony
            // installs the commitment/secret separately; judged play then derives
            // and substitutes this player's live target and run seed through Lean.
            target,
            mission: SignalMission {
                mission_id: required_u64(mission, "mission_id")?,
                artifact,
                epoch: required_u64(mission, "epoch")?,
                federation_id: required_str(mission, "federation_id")?.to_owned(),
                content_root: bare_sha(required_str(mission, "content_root")?, "mission root")?,
                activation_digest: bare_sha(&verified.activation_digest(), "activation digest")?,
                content_session: required_str(mission, "content_session")?.to_owned(),
                // ⚠ NOT read from the catalog: the catalog no longer carries a run
                // seed, because genesis describes a mission TEMPLATE and a template
                // has no instance. Lean's `expectedConfig` builds the genesis config
                // with `Emit.UNBOUND_RUN_SEED` and compares it byte-for-byte, so this
                // must be exactly that sentinel — thirty-two zero bytes, meaning "no
                // live draw has happened". The live seed is drawn per run by
                // `HiddenInstance.runSeedFor` and never appears in an artifact.
                run_seed: UNBOUND_RUN_SEED.to_owned(),
                budget: budget.clone(),
                allowed_relics: allowed_relics.clone(),
                privacy: required_str(mission, "privacy_grade")?.to_owned(),
                ballot: required_str(mission, "ballot_regime")?.to_owned(),
            },
            reward: Contribution {
                intel: budget.intel,
                supplies: budget.supplies,
                cohesion: budget.cohesion,
                influence: budget.influence,
                score: budget.score,
                relics: allowed_relics,
            },
        },
        initial: InitialState {
            world: EmptyWorld {
                intel: 0,
                supplies: 0,
                cohesion: 0,
                influence: 0,
                score: 0,
                discovered_relics: Vec::new(),
                beta_artifacts: Vec::new(),
                sequence: 0,
            },
            known: Vec::new(),
            alpha: Vec::new(),
            superseded: Vec::new(),
            consumed_runs: Vec::new(),
            player_counters: Vec::new(),
            canon_revision: 0,
            curator_counter: 0,
            transition_count: 0,
            last_transition_digest: ZERO_HEX,
        },
    };
    serde_json::to_string(&input)
        .map_err(|error| format!("cannot encode Lean genesis wire: {error}"))
}

fn template_target_for_authenticated_descriptor(
    descriptor: &serde_json::Map<String, Value>,
) -> Result<SignalCode, String> {
    if descriptor.contains_key("target") {
        return Err(
            "authenticated Signal descriptor publishes a target; a public target is the answer"
                .to_owned(),
        );
    }
    Ok(UNBOUND_TARGET)
}

fn required_u64(object: &serde_json::Map<String, Value>, field: &str) -> Result<u64, String> {
    object
        .get(field)
        .and_then(Value::as_u64)
        .ok_or_else(|| format!("authenticated Signal {field} is not a u64"))
}

fn required_str<'a>(
    object: &'a serde_json::Map<String, Value>,
    field: &str,
) -> Result<&'a str, String> {
    object
        .get(field)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("authenticated Signal {field} is not a string"))
}

fn bare_sha(value: &str, label: &str) -> Result<String, String> {
    let bare = value
        .strip_prefix("sha256:")
        .ok_or_else(|| format!("{label} is not a tagged SHA-256 digest"))?;
    parse_hex32(bare, label)?;
    Ok(bare.to_owned())
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct GenesisOutput {
    format: String,
    authority_id: String,
    deployment_digest: String,
    declared_deployment_id: String,
    deployment_genesis_sha256: String,
    deployment_manifest_sha256: String,
    deployment_policy_sha256: String,
    manifest_sha256: String,
    content_root: String,
    activation_digest: String,
    curator_key: String,
    content_epoch: u64,
    activation_counter: u64,
    transition_count: u64,
    world_sequence: u64,
    canon_revision: u64,
    last_transition_digest: String,
    config_json: String,
    canon_json: String,
    config_sha256: String,
    canon_sha256: String,
    authority_lanes9: [u64; 9],
    deployment_lanes9: [u64; 9],
    deployment_genesis_lanes9: [u64; 9],
    manifest_lanes9: [u64; 9],
    content_root_lanes9: [u64; 9],
    activation_lanes9: [u64; 9],
    curator_key_lanes9: [u64; 9],
    config_sha256_lanes9: [u64; 9],
    canon_sha256_lanes9: [u64; 9],
}

fn parse_exact_network_genesis_output(bytes: &str) -> Result<GenesisOutput, String> {
    let output: GenesisOutput = serde_json::from_str(bytes)
        .map_err(|error| format!("Lean NetworkGenesis output syntax refused: {error}"))?;
    let canonical = serde_json::to_string(&output)
        .map_err(|error| format!("cannot re-encode Lean NetworkGenesis output: {error}"))?;
    if canonical != bytes {
        return Err("Lean NetworkGenesis output is not the exact canonical byte encoding".into());
    }
    Ok(output)
}

impl GenesisOutput {
    fn binds_exact_tuple(
        &self,
        bound: &DeploymentBoundBundle<'_>,
        verified: &VerifiedContentEpoch<'_>,
    ) -> Result<(), String> {
        let bundle = bound.bundle();
        let expected_manifest = bare_sha(bundle.manifest_sha256(), "manifest digest")?;
        let expected_root = bare_sha(bundle.content_root(), "content root")?;
        let expected_activation = bare_sha(&verified.activation_digest(), "activation digest")?;
        if self.format != OUTPUT_FORMAT
            || self.authority_id != bound.deployment().federation_id()
            || self.deployment_digest != bound.deployment().deployment_digest()
            || self.declared_deployment_id != bound.deployment().deployment_id()
            || self.deployment_genesis_sha256 != bound.deployment().genesis_sha256()
            || self.deployment_manifest_sha256 != bound.deployment().manifest_sha256()
            || self.deployment_policy_sha256 != bound.deployment().policy_sha256()
            || self.manifest_sha256 != expected_manifest
            || self.content_root != expected_root
            || self.activation_digest != expected_activation
            || self.curator_key != verified.envelope().curator_pubkey
            || self.content_epoch != verified.envelope().content_epoch
            || self.activation_counter != verified.envelope().counter
        {
            return Err(
                "Lean NetworkGenesis output does not bind the verified external tuple".into(),
            );
        }
        if self.transition_count != 0
            || self.world_sequence != 0
            || self.canon_revision != 0
            || self.last_transition_digest != ZERO_HEX
        {
            return Err("Lean NetworkGenesis output is not a zero-history head".into());
        }
        if sha256_hex(self.config_json.as_bytes()) != self.config_sha256
            || sha256_hex(self.canon_json.as_bytes()) != self.canon_sha256
        {
            return Err("Lean NetworkGenesis config/Canon byte digest mismatch".into());
        }
        Ok(())
    }

    fn into_head(self) -> Result<PoaSignalHeadV1, String> {
        PoaSignalHeadV1::genesis(
            parse_hex32(&self.authority_id, "authority_id")?,
            parse_hex32(&self.deployment_digest, "deployment_digest")?,
            self.world_sequence,
            self.canon_revision,
            self.config_json.into_bytes(),
            self.canon_json.into_bytes(),
        )
        .map_err(|error| format!("Lean-emitted PoA Signal head refused by storage codec: {error}"))
    }
}

fn parse_hex32(value: &str, label: &str) -> Result<[u8; 32], String> {
    if value.len() != 64
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(format!("{label} is not exactly 32 lowercase hex bytes"));
    }
    let mut output = [0u8; 32];
    for (index, pair) in value.as_bytes().chunks_exact(2).enumerate() {
        output[index] = (hex_nibble(pair[0]) << 4) | hex_nibble(pair[1]);
    }
    Ok(output)
}

fn hex_nibble(value: u8) -> u8 {
    match value {
        b'0'..=b'9' => value - b'0',
        b'a'..=b'f' => value - b'a' + 10,
        _ => unreachable!("hex was validated"),
    }
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest: [u8; 32] = Sha256::digest(bytes).into();
    let mut output = String::with_capacity(64);
    for byte in digest {
        use std::fmt::Write as _;
        write!(&mut output, "{byte:02x}").expect("writing to String cannot fail");
    }
    output
}

/// ⚑⚑ THE STALE CALLER/CALLEE SPLIT THIS MODULE CLOSED.
///
/// Six tests here were red on 2026-08-07 for THREE stacked causes. Two are fixed in the commit
/// that wrote this note; the third is a live design change and is the poa-signal lane's.
///
///  1. FIXED — the fixture wrote `POA_DATA_DIR=/var/folders/…` from a raw `tempfile::tempdir()`
///     while the manifest-derived policy image spells the canonical `/private/var/…`, so a
///     byte-exact operator.env comparison failed on ONE line and reported
///     "differs from exact manifest-derived production policy". A path mismatch wearing a policy
///     verdict. `prepare_deployment` now derives every path from the canonical root, and
///     `poa_curator::first_operator_difference` makes that refusal name the differing line.
///  2. FIXED — `expected_activation_counter` was hardcoded `2` beside an artifact that carries
///     8 (`4002060a2`, Black Box enrolled and the curator re-signed). Read from the envelope now,
///     with `a_wrong_activation_counter_is_refused` keeping the leg able to go red.
///  3. CLOSED HERE. `build_network_genesis_input` read `descriptor["target"]` — three bands —
///     and refused because the shipped descriptor has no `target`. That absence is DELIBERATE:
///     `4db8ec12e` ("the games stop publishing their own answers") deleted it when Signal moved
///     `signal-v1 → signal-v2`, because a published target IS the published answer. The run seed
///     is now per-run and unpredictable, derived through `dregg_poa_signal_slot_derive` from a
///     curator-held per-slot secret whose commitment is published before the slot opens.
///
///     The semantic answer was already named in Lean: `Emit.signalTemplateConfig` pairs
///     `UNBOUND_RUN_SEED` with `UNBOUND_TARGET = [0,0,0]`, and `NetworkGenesis.expectedConfig`
///     requires that exact complete config. `Judged.admissionChecks` refuses the unbound seed, so
///     this value can never be played. A live slot is stored separately; the judge derives and
///     substitutes the player-specific seed and target from its committed secret. Rust now sends
///     that named template sentinel, and refuses a descriptor that regresses by publishing a
///     target. Lean still owns the byte-exact acceptance decision.
///
///     ⚠ It is a CALLER/CALLEE SPLIT, and it was invisible for two days because causes 1 and 2
///     refused first. That is the whole reason those two were worth fixing: the red now names
///     the thing that was actually broken.
#[cfg(test)]
mod tests {
    use super::*;
    use dregg_persist::CommitRecord;

    fn repo() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .unwrap()
            .to_path_buf()
    }

    struct PreparedDeployment {
        _root: tempfile::TempDir,
        main: tempfile::TempDir,
        data_dir: PathBuf,
        manifest: PathBuf,
        genesis: PathBuf,
    }

    fn prepare_deployment() -> PreparedDeployment {
        let root = tempfile::tempdir().unwrap();
        let main = tempfile::tempdir().unwrap();
        // ⚑ CANONICALIZED, and it is not tidiness. `poa_curator::operator_config` spells
        // `POA_DATA_DIR` as `verified.root.join(node.data_dir)` over a root that resolved through
        // `fs::canonicalize`, and `verify_serving_data_dir` compares operator.env BYTE-EXACTLY.
        // On macOS `tempfile::tempdir()` hands back `/var/folders/…` while the same directory
        // canonicalizes to `/private/var/folders/…`, so a fixture built from the raw handle wrote
        // one line the production image could never match — and all six tests in this module
        // failed reporting `operator.env differs from exact manifest-derived production policy`,
        // which is a policy verdict for a symlink prefix. Deriving every path here from the
        // canonical root makes the fixture spell what production spells. It relaxes NOTHING: the
        // comparison in `poa-curator` is still byte-exact, and its refusal now names the differing
        // line so this cannot be mis-diagnosed again.
        let root_path = fs::canonicalize(root.path()).unwrap();
        fs::create_dir_all(root_path.join("bundle")).unwrap();
        fs::create_dir_all(root_path.join("nodes/node-0")).unwrap();
        let manifest = root_path.join("poa-devnet.json");
        let genesis = root_path.join("bundle/genesis.json");
        fs::copy(
            repo().join("poa/deployments/epoch-1/poa-devnet.json"),
            &manifest,
        )
        .unwrap();
        fs::copy(
            repo().join("poa/deployments/epoch-1/bundle/genesis.json"),
            &genesis,
        )
        .unwrap();
        let data_dir = root_path.join("nodes/node-0");
        fs::copy(&genesis, data_dir.join("genesis.json")).unwrap();
        let manifest_json: Value = serde_json::from_slice(&fs::read(&manifest).unwrap()).unwrap();
        let node = &manifest_json["nodes"][0];
        let operator = format!(
            "POA_DEPLOYMENT_DOMAIN={}\nPOA_DEPLOYMENT_ID={}\nPOA_FEDERATION_ID={}\nPOA_NODE_INDEX=0\nPOA_DATA_DIR={}\nPOA_HTTP_BIND={}\nPOA_HTTP_PORT={}\nPOA_GOSSIP_PORT={}\nPOA_GOSSIP_HOST={}\nPOA_FEDERATION_PEERS={}\nPOA_PROVE_TURNS=1\nPOA_ENABLE_FAUCET=0\nPOA_AUTO_APPROVE_JOINS=0\nDREGG_REQUIRE_LEAN=1\nDREGG_STRAND_ADMISSION_GATE=1\nDREGG_ALLOW_UNVERIFIED_CONSENSUS=0\nDREGG_STATUS_EXPOSE_COUNTS=0\nDREGG_SEED_DEMO_LEASE=0\n",
            manifest_json["deployment_domain"].as_str().unwrap(),
            manifest_json["deployment_id"].as_str().unwrap(),
            manifest_json["federation_id"].as_str().unwrap(),
            data_dir.display(),
            node["http"]["bind"].as_str().unwrap(),
            node["http"]["port"].as_u64().unwrap(),
            node["gossip"]["port"].as_u64().unwrap(),
            node["gossip"]["advertised_host"].as_str().unwrap(),
            node["gossip"]["peers"]
                .as_array()
                .unwrap()
                .iter()
                .map(|peer| peer.as_str().unwrap())
                .collect::<Vec<_>>()
                .join(","),
        );
        fs::write(data_dir.join("operator.env"), operator).unwrap();
        PreparedDeployment {
            _root: root,
            main,
            data_dir,
            manifest,
            genesis,
        }
    }

    /// The shipped envelope's own `(content_epoch, counter)`.
    ///
    /// ⚑ THESE WERE HARDCODED `(1, 2)` AND THE ARTIFACT MOVED TO COUNTER 8 (`4002060a2`, Black Box
    /// enrolled and the curator re-signed) — six tests in this module red for a reason unrelated to
    /// anything any of them checks, and stale again the moment the next content lands. A number that
    /// lives in a signed artifact must be READ FROM IT, never repeated beside it.
    ///
    /// ⚠ AND READING IT IS ONLY SAFE BECAUSE OF `a_wrong_activation_counter_is_refused` BELOW.
    /// `expected_activation_counter` is the caller-owned ANTI-ROLLBACK value and `verify` has no
    /// other check on `counter`, so sourcing it from the envelope makes that comparison trivially
    /// true for every happy-path fixture here. The negative test is what keeps the leg able to go
    /// red at THIS boundary; do not keep one without the other.
    ///
    /// (`expected_content_epoch` is different in kind: `verify` independently requires
    /// `envelope.content_epoch == bundle.content_epoch`, the authenticated catalog's, so reading it
    /// from the envelope leaves the epoch bound to the bundle either way. `poa-curator`'s
    /// `checked_in_epoch_one_replacement_requires_counter_two` covers the counter leg inside
    /// `verify` over a self-signed envelope; what it cannot cover is the node's WIRING of it.)
    fn shipped_epoch_and_counter() -> (u64, u64) {
        let envelope =
            ContentEpochEnvelope::load(repo().join("poa/artifacts/poag1/manifest.sig.json"))
                .expect("the shipped content envelope must load");
        (envelope.content_epoch, envelope.counter)
    }

    fn args(deployment: &PreparedDeployment) -> PoaSignalGenesisArgs {
        let repo = repo();
        let (expected_content_epoch, expected_activation_counter) = shipped_epoch_and_counter();
        PoaSignalGenesisArgs {
            data_dir: deployment.data_dir.clone(),
            deployment_manifest: deployment.manifest.clone(),
            genesis: deployment.genesis.clone(),
            main_data_dir: deployment.main.path().to_path_buf(),
            poag1_manifest: repo.join("poa/artifacts/poag1/manifest.json"),
            content_envelope: repo.join("poa/artifacts/poag1/manifest.sig.json"),
            curator_key_pin: repo.join("poa/config/curator-key.json"),
            expected_content_epoch,
            expected_activation_counter,
        }
    }

    /// ⚑ THE LEG `shipped_epoch_and_counter` WOULD OTHERWISE DISARM, at the node boundary.
    ///
    /// `expected_activation_counter` is the operator's anti-rollback claim: it is the ONLY thing
    /// constraining `counter`, because unlike `content_epoch` it is cross-checked against nothing
    /// in the bundle. If the ceremony stopped forwarding it — or forwarded a value it read back
    /// out of the same envelope it is judging — a curator replaying an OLD signed epoch would
    /// activate, and every happy-path test here would still be green.
    ///
    /// So this hands `run_poa_signal_genesis` a counter that is deliberately not the shipped one
    /// and asserts the refusal NAMES both numbers. Both directions are driven — one below and one
    /// above — because a comparison that had degenerated into `>=` or `<=` would still refuse one
    /// of them, and refusing one is not refusing a rollback.
    #[test]
    fn a_wrong_activation_counter_is_refused() {
        let deployment = prepare_deployment();
        let (_, shipped) = shipped_epoch_and_counter();

        for wrong in [shipped - 1, shipped + 1] {
            let mut args = args(&deployment);
            args.expected_activation_counter = wrong;
            let error = initialize_poa_signal_genesis_with(&args, fixture_evaluator)
                .expect_err("a counter that is not the signed one must REFUSE activation");
            assert!(
                error.contains(&format!("counter {shipped} != expected {wrong}")),
                "the refusal must name the signed counter AND the expected one, so an operator \
                 can tell a rollback attempt from a mis-typed argument. Got: {error}"
            );
        }

        // ...and the SHIPPED counter gets past this leg, so the assertions above are a
        // discrimination and not a gate that refuses everything.
        //
        // ⚠ Deliberately "does not fail ON THE COUNTER" rather than "installs". The fixture
        // evaluator below is byte-pinned to one historical deployment/content tuple, while this
        // leg deliberately reads the currently shipped signed envelope. Coupling the anti-rollback
        // tooth to a fixture regeneration would take it red for an unrelated reason and make the
        // discrimination above harder to read.
        let shipped_run = initialize_poa_signal_genesis_with(&args(&deployment), fixture_evaluator);
        if let Err(error) = &shipped_run {
            assert!(
                !error.contains("!= expected"),
                "the SHIPPED counter must pass the anti-rollback comparison — if it does not, the \
                 two refusals above prove nothing about the counter. Got: {error}"
            );
        }
    }

    /// The pair really is read from the artifact and not from a constant that happens to agree
    /// today. `4002060a2` moved the counter to 8 and six tests went red against a hardcoded 2;
    /// this asserts the fixture tracks the file rather than a number someone typed.
    #[test]
    fn the_expected_pair_is_the_shipped_envelopes_own() {
        let raw: Value = serde_json::from_slice(
            &fs::read(repo().join("poa/artifacts/poag1/manifest.sig.json")).unwrap(),
        )
        .unwrap();
        let (epoch, counter) = shipped_epoch_and_counter();
        assert_eq!(epoch, raw["content_epoch"].as_u64().unwrap());
        assert_eq!(counter, raw["counter"].as_u64().unwrap());
        assert!(
            counter >= 1,
            "a zero activation counter would make the anti-rollback claim vacuous"
        );
    }

    #[test]
    fn template_target_shipped_descriptor_is_target_free_and_a_published_answer_refuses() {
        let descriptor: Value = serde_json::from_slice(
            &fs::read(repo().join("poa/artifacts/poag1/games/signal-triangulation.json")).unwrap(),
        )
        .unwrap();
        let descriptor = descriptor.as_object().unwrap();
        assert_eq!(
            template_target_for_authenticated_descriptor(descriptor).unwrap(),
            UNBOUND_TARGET,
            "a target-free public descriptor must receive only Lean's non-playable template sentinel"
        );

        let mut published_answer = descriptor.clone();
        published_answer.insert("target".to_owned(), serde_json::json!([1, 2, 3]));
        let error = template_target_for_authenticated_descriptor(&published_answer)
            .expect_err("publishing the answer must refuse genesis");
        assert!(error.contains("public target is the answer"), "{error}");
    }

    fn fixture_evaluator(wire: &str) -> Result<String, String> {
        let expected =
            include_str!("../../dregg-lean-ffi/tests/fixtures/poa-network-genesis-input-v1.json")
                .trim_end();
        if wire != expected {
            return Err("generated ceremony wire differs from frozen Lean input".into());
        }
        Ok(
            include_str!("../../dregg-lean-ffi/tests/fixtures/poa-network-genesis-output-v1.json")
                .trim_end()
                .to_owned(),
        )
    }

    #[test]
    fn exact_tuple_installs_and_crash_reopens_the_same_head() {
        let deployment = prepare_deployment();
        let report =
            initialize_poa_signal_genesis_with(&args(&deployment), fixture_evaluator).unwrap();
        assert_eq!(report.outcome, PoaSignalGenesisInitOutcome::Installed);

        let reopened = PersistentStore::open(&deployment.data_dir.join("dregg.redb")).unwrap();
        let head = reopened
            .load_poa_signal_head(report.authority_id)
            .unwrap()
            .unwrap();
        assert_eq!(head.digest(), report.head_digest);
        reopened.audit_poa_signal_state().unwrap();
        drop(reopened);

        let retry =
            initialize_poa_signal_genesis_with(&args(&deployment), fixture_evaluator).unwrap();
        assert_eq!(retry.outcome, PoaSignalGenesisInitOutcome::AlreadyIdentical);
        assert_eq!(retry.head_digest, report.head_digest);
    }

    #[test]
    fn template_target_linked_lean_export_drives_the_real_store_ceremony() {
        let deployment = prepare_deployment();
        let report = initialize_poa_signal_genesis(&args(&deployment)).unwrap();
        assert_eq!(report.outcome, PoaSignalGenesisInitOutcome::Installed);
        let reopened = PersistentStore::open(&deployment.data_dir.join("dregg.redb")).unwrap();
        let head = reopened
            .load_poa_signal_head(report.authority_id)
            .unwrap()
            .unwrap();
        assert_eq!(head.digest(), report.head_digest);
        let config: Value = serde_json::from_slice(head.config()).unwrap();
        assert_eq!(
            config["game"],
            crate::poa_signal_adapter::POA_GAME_TAG_SIGNAL
        );
        assert_eq!(
            config["target"],
            serde_json::json!({"low": 0, "mid": 0, "high": 0})
        );
        assert_eq!(config["mission"]["run_seed"], UNBOUND_RUN_SEED);
        assert_eq!(
            config["mission"]["federation_id"],
            dregg_types::hex_encode(&report.authority_id)
        );
        assert_eq!(
            reopened.load_poa_world_curator_pin_v1().unwrap(),
            Some(
                CuratorKeyPin::load(repo().join("poa/config/curator-key.json"))
                    .unwrap()
                    .public_key()
                    .unwrap()
                    .0
            ),
            "Signal genesis must persist the independently authenticated curator pin needed by the slot ceremony"
        );

        let canon: Value = serde_json::from_slice(head.canon()).unwrap();
        assert_eq!(
            canon["federation_id"],
            dregg_types::hex_encode(&report.authority_id)
        );
        assert_eq!(canon["content_epoch"], 1);
        assert_eq!(canon["world"]["sequence"], 0);
        assert_eq!(canon["revision"], 0);
    }

    #[test]
    fn nonempty_generic_store_refuses_without_losing_the_commit() {
        let deployment = prepare_deployment();
        let store = PersistentStore::open(&deployment.data_dir.join("dregg.redb")).unwrap();
        let record = CommitRecord {
            ordinal: 0,
            height: 1,
            block_id: [1; 32],
            block_executed_up_to: 1,
            turn_hash: [2; 32],
            creator: [3; 32],
            receipt_hash: [4; 32],
            ledger_root: [5; 32],
            touched_cells: Vec::new(),
            removed: Vec::new(),
        };
        store.commit_finalized_turn(0, &record).unwrap();
        drop(store);

        let error =
            initialize_poa_signal_genesis_with(&args(&deployment), fixture_evaluator).unwrap_err();
        assert!(
            error.contains("before the first finalized commit"),
            "{error}"
        );
        let reopened = PersistentStore::open(&deployment.data_dir.join("dregg.redb")).unwrap();
        assert_eq!(reopened.commit_cursor().unwrap(), 1);
        assert!(
            reopened
                .load_poa_signal_head(
                    parse_hex32(
                        "4ea83e8ebf4f590eace11c9ffd6d6607a4afb15e5a00cd7b9e04890dab6bfc5a",
                        "fixture authority",
                    )
                    .unwrap()
                )
                .unwrap()
                .is_none()
        );
    }

    #[test]
    fn tuple_drift_refuses_before_lean_or_store_open() {
        let deployment = prepare_deployment();
        let mut genesis = fs::read(&deployment.genesis).unwrap();
        genesis.push(b' ');
        fs::write(&deployment.genesis, &genesis).unwrap();
        fs::write(deployment.data_dir.join("genesis.json"), genesis).unwrap();
        let error = initialize_poa_signal_genesis_with(&args(&deployment), |_| {
            panic!("Lean must not be called for a drifted deployment tuple")
        })
        .unwrap_err();
        assert!(error.contains("does not pin"), "{error}");
        assert!(!deployment.data_dir.join("dregg.redb").exists());
    }

    #[test]
    fn weakened_production_policy_refuses_before_lean_or_store_open() {
        let deployment = prepare_deployment();
        let mut manifest: Value =
            serde_json::from_slice(&fs::read(&deployment.manifest).unwrap()).unwrap();
        manifest["policy"]["require_lean"] = Value::Bool(false);
        fs::write(
            &deployment.manifest,
            serde_json::to_vec_pretty(&manifest).unwrap(),
        )
        .unwrap();
        let error = initialize_poa_signal_genesis_with(&args(&deployment), |_| {
            panic!("Lean must not be called for weakened operator policy")
        })
        .unwrap_err();
        assert!(error.contains("weakened"), "{error}");
        assert!(!deployment.data_dir.join("dregg.redb").exists());
    }

    #[test]
    fn declared_federation_must_rederive_from_hybrid_committee() {
        let deployment = prepare_deployment();
        let mut genesis: Value =
            serde_json::from_slice(&fs::read(&deployment.genesis).unwrap()).unwrap();
        let substituted = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
        genesis["federation_id"] = Value::String(substituted.into());
        let genesis_bytes = serde_json::to_vec(&genesis).unwrap();
        fs::write(&deployment.genesis, &genesis_bytes).unwrap();
        fs::write(deployment.data_dir.join("genesis.json"), &genesis_bytes).unwrap();
        let genesis_sha = sha256_hex(&genesis_bytes);
        let mut manifest: Value =
            serde_json::from_slice(&fs::read(&deployment.manifest).unwrap()).unwrap();
        manifest["federation_id"] = Value::String(substituted.into());
        manifest["genesis_sha256"] = Value::String(genesis_sha.clone());
        manifest["deployment_id"] = Value::String(sha256_hex(
            format!(
                "{}\0{}\0{}",
                poa_curator::POA_DEPLOYMENT_DOMAIN,
                substituted,
                genesis_sha
            )
            .as_bytes(),
        ));
        fs::write(&deployment.manifest, serde_json::to_vec(&manifest).unwrap()).unwrap();
        let error = initialize_poa_signal_genesis_with(&args(&deployment), |_| {
            panic!("Lean must not be called for unreachable declared federation")
        })
        .unwrap_err();
        assert!(error.contains("hybrid committee"), "{error}");
    }

    #[test]
    fn retained_genesis_bytes_close_authoritative_path_rotation() {
        let deployment = prepare_deployment();
        let scope = PoaDeploymentScope::load_verified(
            &deployment.manifest,
            &deployment.genesis,
            deployment.main.path(),
        )
        .unwrap();
        let mut rotated = fs::read(&deployment.genesis).unwrap();
        rotated.push(b' ');
        // Both mutable paths now agree on B, but the verifier token retained A.
        fs::write(&deployment.genesis, &rotated).unwrap();
        fs::write(deployment.data_dir.join("genesis.json"), &rotated).unwrap();
        let error = scope
            .verify_serving_data_dir(&deployment.data_dir, None)
            .unwrap_err()
            .to_string();
        assert!(
            error.contains("retained authenticated descriptor"),
            "{error}"
        );
    }

    #[test]
    fn exact_manifest_byte_drift_is_not_an_idempotent_retry() {
        let deployment = prepare_deployment();
        let installed = initialize_poa_signal_genesis(&args(&deployment)).unwrap();
        assert_eq!(installed.outcome, PoaSignalGenesisInitOutcome::Installed);
        let mut manifest = fs::read(&deployment.manifest).unwrap();
        manifest.push(b'\n');
        fs::write(&deployment.manifest, manifest).unwrap();
        let error = initialize_poa_signal_genesis(&args(&deployment)).unwrap_err();
        assert!(error.contains("different authority head"), "{error}");
        let store = PersistentStore::open(&deployment.data_dir.join("dregg.redb")).unwrap();
        let head = store
            .load_poa_signal_head(installed.authority_id)
            .unwrap()
            .unwrap();
        assert_eq!(head.digest(), installed.head_digest);
    }

    #[tokio::test]
    async fn node_state_restart_refuses_runtime_genesis_drift_with_same_committee() {
        let deployment = prepare_deployment();
        let installed = initialize_poa_signal_genesis(&args(&deployment)).unwrap();
        drop(PersistentStore::open(&deployment.data_dir.join("dregg.redb")).unwrap());

        // Construct the same full NodeState restart path that opens/recovery-
        // audits dregg.redb. The boot weld then consumes the exact bytes the
        // runtime genesis parser consumed, rather than rereading a pathname.
        let node = crate::state::NodeState::new_with_key_file(
            &deployment.data_dir,
            Vec::new(),
            "node.key",
        )
        .unwrap();
        let original = fs::read(deployment.data_dir.join("genesis.json")).unwrap();
        {
            let state = node.read().await;
            let head = state
                .store
                .load_singular_poa_signal_head()
                .unwrap()
                .unwrap();
            verify_poa_signal_boot_identity(
                &head,
                &deployment.data_dir,
                installed.authority_id,
                &original,
                &deployment.manifest,
                deployment.main.path(),
            )
            .unwrap();
        }

        let mut drifted = original;
        drifted.push(b' '); // semantic committee is unchanged; exact runtime image is not.
        fs::write(deployment.data_dir.join("genesis.json"), &drifted).unwrap();
        let state = node.read().await;
        let head = state
            .store
            .load_singular_poa_signal_head()
            .unwrap()
            .unwrap();
        let error = verify_poa_signal_boot_identity(
            &head,
            &deployment.data_dir,
            installed.authority_id,
            &drifted,
            &deployment.manifest,
            deployment.main.path(),
        )
        .unwrap_err();
        assert!(
            error.contains("retained authenticated descriptor"),
            "{error}"
        );
    }

    #[test]
    fn missing_export_refuses_before_store_open() {
        let deployment = prepare_deployment();
        let error = initialize_poa_signal_genesis_with(&args(&deployment), |_| {
            Err("dregg_poa_network_genesis is absent".into())
        })
        .unwrap_err();
        assert!(error.contains("is absent"), "{error}");
        assert!(!deployment.data_dir.join("dregg.redb").exists());
    }
}
