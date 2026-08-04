//! Non-authoritative Path of Angels Signal transport adapter.
//!
//! This module classifies the reserved SDK event, constructs the complete
//! canonical Lean wire from a host-only context, invokes the Lean evaluator,
//! and strictly parses its canonical reply.  It does not load persistence,
//! derive finality, execute a turn, or commit the successor.  Consequently a
//! successful [`evaluate_signal_claim`] is an evaluated candidate, never a
//! finalized receipt.

use std::fmt;

use dregg_sdk::poa_signal::{
    SignalClaimError, SignalClaimV1, SignalCode, SignalEventRoute, classify_signal_event,
};
use dregg_turn::Effect;
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};

const SIGNAL_INPUT_FORMAT: &str = "POA-SIGNAL-IN-1";
const SIGNAL_OUTPUT_FORMAT: &str = "POA-SIGNAL-OUT-1";
const LEAN_SIGNAL_WIRE_BYTES: usize = 16 * 1024 * 1024;
const METRIC_LIMIT: u64 = 1_000_000;
const RELIC_LIMIT: usize = 64;
const MISSION_RELIC_LIMIT: usize = 4096;
const WORLD_RELIC_LIMIT: usize = 4096;
const ARTIFACT_LIMIT: usize = 4096;
const RECEIPT_LIMIT: usize = 16_384;
const COUNTER_LIMIT: usize = 16_384;
const SIGNAL_ACTION_LIMIT: usize = 5;

/// Node-side routing result.  A malformed reserved event is returned as an
/// error and can never be reconsidered as ordinary event traffic.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SignalEffectRoute {
    Ordinary,
    Signal(SignalClaimV1),
}

/// Classify one effect at the reserved PoA boundary.
pub fn classify_signal_effect(effect: &Effect) -> Result<SignalEffectRoute, SignalAdapterError> {
    let Effect::EmitEvent { event, .. } = effect else {
        return Ok(SignalEffectRoute::Ordinary);
    };
    match classify_signal_event(event).map_err(SignalAdapterError::Claim)? {
        SignalEventRoute::Ordinary => Ok(SignalEffectRoute::Ordinary),
        SignalEventRoute::Signal(claim) => Ok(SignalEffectRoute::Signal(claim)),
    }
}

/// Exact, parsed `POA-SIGNAL-IN-1` bytes.
#[derive(Clone, Debug)]
pub struct CanonicalSignalInput {
    bytes: String,
    dto: SignalInputDto,
}

impl CanonicalSignalInput {
    pub fn parse(bytes: &str) -> Result<Self, SignalAdapterError> {
        let dto: SignalInputDto = parse_exact(bytes, "Signal input")?;
        validate_input(&dto)?;
        Ok(Self {
            bytes: bytes.to_owned(),
            dto,
        })
    }

    pub fn as_str(&self) -> &str {
        &self.bytes
    }

    /// Drop the request entirely, retaining only the state a future finalized
    /// adapter must derive from persistence/finality.
    pub fn authority_context(&self) -> SignalAuthorityContext {
        SignalAuthorityContext {
            config: self.dto.config.clone(),
            world: self.dto.world.clone(),
            canon: self.dto.canon.clone(),
            carrier: self.dto.carrier.clone(),
        }
    }
}

/// Exact, parsed `POA-SIGNAL-OUT-1` bytes returned by Lean.
#[derive(Clone, Debug)]
pub struct CanonicalSignalOutput {
    bytes: String,
    dto: SignalOutputDto,
}

impl CanonicalSignalOutput {
    pub fn parse(bytes: &str) -> Result<Self, SignalAdapterError> {
        let dto: SignalOutputDto = parse_exact(bytes, "Signal output")?;
        validate_output(&dto)?;
        Ok(Self {
            bytes: bytes.to_owned(),
            dto,
        })
    }

    pub fn as_str(&self) -> &str {
        &self.bytes
    }

    /// The mission id in the Lean-emitted receipt (inspection only).
    pub fn mission_id(&self) -> u64 {
        self.dto.receipt.mission.mission_id
    }
}

/// Host-only pieces used to construct a complete judge input.
///
/// The sole constructor currently discards the request from an already strict
/// canonical input.  A later authoritative adapter may construct this from
/// persisted state and an authenticated finalized turn; this slice does not.
#[derive(Clone, Debug)]
pub struct SignalAuthorityContext {
    config: SignalConfigDto,
    world: WorldStateDto,
    canon: CanonStateDto,
    carrier: FinalizedCarrierDto,
}

/// A side-effect-free evaluated candidate.  Possession of this value is not
/// evidence that its context came from finality or that its successor committed.
#[derive(Clone, Debug)]
pub struct EvaluatedSignalCandidate {
    input: CanonicalSignalInput,
    output: CanonicalSignalOutput,
}

impl EvaluatedSignalCandidate {
    pub fn input(&self) -> &CanonicalSignalInput {
        &self.input
    }

    pub fn output(&self) -> &CanonicalSignalOutput {
        &self.output
    }
}

/// Build the canonical Lean input while deriving every authority-bearing
/// request field from the host context.  The public claim contributes exactly
/// `mission_id` and one code.
pub fn prepare_signal_input(
    context: &SignalAuthorityContext,
    claim: SignalClaimV1,
) -> Result<CanonicalSignalInput, SignalAdapterError> {
    let mission_id = u64::from(claim.mission_id());
    if context.config.mission.mission_id != mission_id {
        return Err(SignalAdapterError::MissionMismatch {
            claimed: mission_id,
            active: context.config.mission.mission_id,
        });
    }
    let code = claim.code();
    let dto = SignalInputDto {
        format: SIGNAL_INPUT_FORMAT.to_owned(),
        config: context.config.clone(),
        world: context.world.clone(),
        canon: context.canon.clone(),
        carrier: context.carrier.clone(),
        request: SignalRequestDto {
            mission_id,
            federation_id: context.carrier.federation_id.clone(),
            content_root: context.carrier.content_root.clone(),
            activation_digest: context.carrier.activation_digest.clone(),
            content_session: context.carrier.content_session.clone(),
            content_epoch: context.carrier.content_epoch,
            run_seed: context.config.mission.run_seed.clone(),
            actor_root: context.carrier.actor_root.clone(),
            player_key: context.carrier.player_key.clone(),
            previous_player_counter: context.carrier.current_player_counter,
            expected_world_sequence: context.world.sequence,
            expected_canon_revision: context.canon.revision,
            actions: vec![SignalCodeDto::from(code)],
        },
    };
    validate_input(&dto)?;
    let bytes =
        serde_json::to_string(&dto).map_err(|error| SignalAdapterError::Json(error.to_string()))?;
    CanonicalSignalInput::parse(&bytes)
}

/// Invoke the existing Lean FFI and strictly parse its exact reply.
///
/// This function is intentionally pure with respect to node state: it neither
/// executes nor persists the returned successor.
pub fn evaluate_signal_claim(
    context: &SignalAuthorityContext,
    claim: SignalClaimV1,
) -> Result<EvaluatedSignalCandidate, SignalAdapterError> {
    let input = prepare_signal_input(context, claim)?;
    let verdict = dregg_lean_ffi::poa_ffi::judge_poa_signal(input.as_str())
        .map_err(SignalAdapterError::LeanTransport)?;
    let bytes = match verdict {
        dregg_lean_ffi::poa_ffi::PoaSignalVerdict::Accepted(bytes) => bytes,
        dregg_lean_ffi::poa_ffi::PoaSignalVerdict::Rejected => {
            return Err(SignalAdapterError::LeanRejected);
        }
    };
    let output = CanonicalSignalOutput::parse(&bytes)?;
    validate_evaluation_binding(&input.dto, &output.dto)?;
    Ok(EvaluatedSignalCandidate { input, output })
}

/// Transport-layer failures.  None authorizes ordinary-event fallback.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SignalAdapterError {
    Claim(SignalClaimError),
    WireTooLarge { what: &'static str, bytes: usize },
    Json(String),
    Noncanonical(&'static str),
    InvalidField(&'static str),
    MissionMismatch { claimed: u64, active: u64 },
    LeanTransport(String),
    LeanRejected,
    OutputBinding(&'static str),
}

impl fmt::Display for SignalAdapterError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Claim(error) => write!(f, "{error}"),
            Self::WireTooLarge { what, bytes } => {
                write!(f, "{what} is {bytes} bytes, above the 16 MiB Lean limit")
            }
            Self::Json(error) => write!(f, "invalid Signal JSON: {error}"),
            Self::Noncanonical(what) => write!(f, "{what} is not exact canonical JSON"),
            Self::InvalidField(field) => write!(f, "invalid Signal field: {field}"),
            Self::MissionMismatch { claimed, active } => {
                write!(
                    f,
                    "claimed mission {claimed} is not active mission {active}"
                )
            }
            Self::LeanTransport(error) => write!(f, "Lean Signal transport unavailable: {error}"),
            Self::LeanRejected => write!(f, "Lean rejected the Signal transition"),
            Self::OutputBinding(reason) => write!(f, "Lean Signal output binding failed: {reason}"),
        }
    }
}

impl std::error::Error for SignalAdapterError {}

fn parse_exact<T>(bytes: &str, what: &'static str) -> Result<T, SignalAdapterError>
where
    T: DeserializeOwned + Serialize,
{
    if bytes.len() > LEAN_SIGNAL_WIRE_BYTES {
        return Err(SignalAdapterError::WireTooLarge {
            what,
            bytes: bytes.len(),
        });
    }
    let dto: T =
        serde_json::from_str(bytes).map_err(|error| SignalAdapterError::Json(error.to_string()))?;
    let encoded =
        serde_json::to_string(&dto).map_err(|error| SignalAdapterError::Json(error.to_string()))?;
    if encoded != bytes {
        return Err(SignalAdapterError::Noncanonical(what));
    }
    Ok(dto)
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ArtifactRefDto {
    mission_id: u64,
    artifact_id: u64,
    source_digest: String,
    content_digest: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct BudgetDto {
    intel: u64,
    supplies: u64,
    cohesion: u64,
    influence: u64,
    score: u64,
    relics: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct MissionDto {
    mission_id: u64,
    artifact: ArtifactRefDto,
    epoch: u64,
    federation_id: String,
    content_root: String,
    activation_digest: String,
    content_session: String,
    run_seed: String,
    budget: BudgetDto,
    allowed_relics: Vec<u64>,
    privacy: String,
    ballot: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ContributionDto {
    intel: u64,
    supplies: u64,
    cohesion: u64,
    influence: u64,
    score: u64,
    relics: Vec<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct SignalCodeDto {
    low: u64,
    mid: u64,
    high: u64,
}

impl From<SignalCode> for SignalCodeDto {
    fn from(code: SignalCode) -> Self {
        Self {
            low: u64::from(code.low()),
            mid: u64::from(code.mid()),
            high: u64::from(code.high()),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct SignalConfigDto {
    target: SignalCodeDto,
    mission: MissionDto,
    reward: ContributionDto,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct WorldStateDto {
    intel: u64,
    supplies: u64,
    cohesion: u64,
    influence: u64,
    score: u64,
    discovered_relics: Vec<u64>,
    beta_artifacts: Vec<ArtifactRefDto>,
    sequence: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ReceiptKeyDto {
    federation_id: String,
    content_session: String,
    content_epoch: u64,
    player_key: String,
    player_counter: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct PlayerCounterRowDto {
    federation_id: String,
    content_session: String,
    content_epoch: u64,
    player_key: String,
    value: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct CanonStateDto {
    federation_id: String,
    content_root: String,
    activation_digest: String,
    content_session: String,
    content_epoch: u64,
    curator_key: String,
    world: WorldStateDto,
    known: Vec<ArtifactRefDto>,
    alpha: Vec<ArtifactRefDto>,
    superseded: Vec<ArtifactRefDto>,
    consumed_runs: Vec<ReceiptKeyDto>,
    player_counters: Vec<PlayerCounterRowDto>,
    revision: u64,
    curator_counter: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct FinalizedCarrierDto {
    federation_id: String,
    content_root: String,
    activation_digest: String,
    content_session: String,
    content_epoch: u64,
    actor_root: String,
    player_key: String,
    current_player_counter: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct SignalRequestDto {
    mission_id: u64,
    federation_id: String,
    content_root: String,
    activation_digest: String,
    content_session: String,
    content_epoch: u64,
    run_seed: String,
    actor_root: String,
    player_key: String,
    previous_player_counter: u64,
    expected_world_sequence: u64,
    expected_canon_revision: u64,
    actions: Vec<SignalCodeDto>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct SignalInputDto {
    format: String,
    config: SignalConfigDto,
    world: WorldStateDto,
    canon: CanonStateDto,
    carrier: FinalizedCarrierDto,
    request: SignalRequestDto,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct SignalReceiptDto {
    mission: MissionDto,
    federation_id: String,
    content_root: String,
    activation_digest: String,
    content_session: String,
    content_epoch: u64,
    actor_root: String,
    player_key: String,
    previous_player_counter: u64,
    player_counter: u64,
    run_seed: String,
    pre_world: WorldStateDto,
    post_world: WorldStateDto,
    contribution: ContributionDto,
    transcript_digest: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct SignalOutputDto {
    format: String,
    receipt: SignalReceiptDto,
    successor_world: WorldStateDto,
    successor_canon: CanonStateDto,
}

fn validate_input(input: &SignalInputDto) -> Result<(), SignalAdapterError> {
    if input.format != SIGNAL_INPUT_FORMAT {
        return Err(SignalAdapterError::InvalidField("input format"));
    }
    validate_config(&input.config)?;
    validate_world(&input.world)?;
    validate_canon(&input.canon)?;
    validate_carrier(&input.carrier)?;
    validate_request(&input.request)
}

fn validate_output(output: &SignalOutputDto) -> Result<(), SignalAdapterError> {
    if output.format != SIGNAL_OUTPUT_FORMAT {
        return Err(SignalAdapterError::InvalidField("output format"));
    }
    validate_mission(&output.receipt.mission)?;
    for (name, digest) in [
        ("receipt federation_id", &output.receipt.federation_id),
        ("receipt content_root", &output.receipt.content_root),
        (
            "receipt activation_digest",
            &output.receipt.activation_digest,
        ),
        ("receipt content_session", &output.receipt.content_session),
        ("receipt actor_root", &output.receipt.actor_root),
        ("receipt player_key", &output.receipt.player_key),
        ("receipt run_seed", &output.receipt.run_seed),
        (
            "receipt transcript_digest",
            &output.receipt.transcript_digest,
        ),
    ] {
        validate_digest(name, digest)?;
    }
    validate_world(&output.receipt.pre_world)?;
    validate_world(&output.receipt.post_world)?;
    validate_contribution(&output.receipt.contribution)?;
    validate_world(&output.successor_world)?;
    validate_canon(&output.successor_canon)
}

/// Transport binding only: this checks copies/equalities the Lean output is
/// required to preserve, without reimplementing its game or Canon transition.
fn validate_evaluation_binding(
    input: &SignalInputDto,
    output: &SignalOutputDto,
) -> Result<(), SignalAdapterError> {
    let request = &input.request;
    let receipt = &output.receipt;
    let bindings_hold = receipt.mission == input.config.mission
        && receipt.mission.mission_id == request.mission_id
        && receipt.federation_id == request.federation_id
        && receipt.content_root == request.content_root
        && receipt.activation_digest == request.activation_digest
        && receipt.content_session == request.content_session
        && receipt.content_epoch == request.content_epoch
        && receipt.actor_root == request.actor_root
        && receipt.player_key == request.player_key
        && receipt.previous_player_counter == request.previous_player_counter
        && receipt.player_counter.checked_sub(1) == Some(request.previous_player_counter)
        && receipt.run_seed == request.run_seed
        && receipt.pre_world == input.world
        && output.successor_world == receipt.post_world
        && output.successor_canon.world == receipt.post_world;
    if !bindings_hold {
        return Err(SignalAdapterError::OutputBinding(
            "receipt/successor does not preserve the exact judged input bindings",
        ));
    }
    Ok(())
}

fn validate_config(config: &SignalConfigDto) -> Result<(), SignalAdapterError> {
    validate_code(&config.target)?;
    validate_mission(&config.mission)?;
    validate_contribution(&config.reward)
}

fn validate_mission(mission: &MissionDto) -> Result<(), SignalAdapterError> {
    validate_id("mission mission_id", mission.mission_id)?;
    validate_artifact(&mission.artifact)?;
    validate_digest("mission federation_id", &mission.federation_id)?;
    validate_digest("mission content_root", &mission.content_root)?;
    validate_digest("mission activation_digest", &mission.activation_digest)?;
    validate_digest("mission content_session", &mission.content_session)?;
    validate_digest("mission run_seed", &mission.run_seed)?;
    validate_budget(&mission.budget)?;
    validate_sorted_ids(
        "mission allowed_relics",
        &mission.allowed_relics,
        MISSION_RELIC_LIMIT,
    )?;
    if !matches!(
        mission.privacy.as_str(),
        "public"
            | "operator-visible-hiding-fri"
            | "process-separated-threshold"
            | "independent-operator-threshold"
    ) {
        return Err(SignalAdapterError::InvalidField("mission privacy"));
    }
    if !matches!(
        mission.ballot.as_str(),
        "none"
            | "one-player-one-voice"
            | "one-wallet-one-voice"
            | "capped-choir"
            | "prediction-oracle"
    ) {
        return Err(SignalAdapterError::InvalidField("mission ballot"));
    }
    Ok(())
}

fn validate_artifact(artifact: &ArtifactRefDto) -> Result<(), SignalAdapterError> {
    validate_id("artifact mission_id", artifact.mission_id)?;
    validate_id("artifact artifact_id", artifact.artifact_id)?;
    validate_digest("artifact source_digest", &artifact.source_digest)?;
    validate_digest("artifact content_digest", &artifact.content_digest)
}

fn validate_budget(budget: &BudgetDto) -> Result<(), SignalAdapterError> {
    validate_metrics(
        budget.intel,
        budget.supplies,
        budget.cohesion,
        budget.influence,
        budget.score,
    )?;
    if budget.relics > RELIC_LIMIT as u64 {
        return Err(SignalAdapterError::InvalidField("budget relics"));
    }
    Ok(())
}

fn validate_contribution(contribution: &ContributionDto) -> Result<(), SignalAdapterError> {
    validate_metrics(
        contribution.intel,
        contribution.supplies,
        contribution.cohesion,
        contribution.influence,
        contribution.score,
    )?;
    validate_sorted_ids("contribution relics", &contribution.relics, RELIC_LIMIT)
}

fn validate_world(world: &WorldStateDto) -> Result<(), SignalAdapterError> {
    validate_metrics(
        world.intel,
        world.supplies,
        world.cohesion,
        world.influence,
        world.score,
    )?;
    validate_sorted_ids(
        "world discovered_relics",
        &world.discovered_relics,
        WORLD_RELIC_LIMIT,
    )?;
    validate_sorted_artifacts(
        "world beta_artifacts",
        &world.beta_artifacts,
        ARTIFACT_LIMIT,
    )
}

fn validate_canon(canon: &CanonStateDto) -> Result<(), SignalAdapterError> {
    for (name, digest) in [
        ("canon federation_id", &canon.federation_id),
        ("canon content_root", &canon.content_root),
        ("canon activation_digest", &canon.activation_digest),
        ("canon content_session", &canon.content_session),
        ("canon curator_key", &canon.curator_key),
    ] {
        validate_digest(name, digest)?;
    }
    validate_world(&canon.world)?;
    validate_sorted_artifacts("canon known", &canon.known, ARTIFACT_LIMIT)?;
    validate_sorted_artifacts("canon alpha", &canon.alpha, ARTIFACT_LIMIT)?;
    validate_sorted_artifacts("canon superseded", &canon.superseded, ARTIFACT_LIMIT)?;
    if canon.consumed_runs.len() > RECEIPT_LIMIT
        || !canon
            .consumed_runs
            .windows(2)
            .all(|pair| receipt_key(&pair[0]) < receipt_key(&pair[1]))
    {
        return Err(SignalAdapterError::InvalidField("canon consumed_runs"));
    }
    for receipt in &canon.consumed_runs {
        validate_digest("consumed federation_id", &receipt.federation_id)?;
        validate_digest("consumed content_session", &receipt.content_session)?;
        validate_digest("consumed player_key", &receipt.player_key)?;
    }
    if canon.player_counters.len() > COUNTER_LIMIT
        || !canon
            .player_counters
            .windows(2)
            .all(|pair| counter_key(&pair[0]) < counter_key(&pair[1]))
        || canon.player_counters.iter().any(|row| row.value == 0)
    {
        return Err(SignalAdapterError::InvalidField("canon player_counters"));
    }
    for row in &canon.player_counters {
        validate_digest("counter federation_id", &row.federation_id)?;
        validate_digest("counter content_session", &row.content_session)?;
        validate_digest("counter player_key", &row.player_key)?;
    }
    Ok(())
}

fn validate_carrier(carrier: &FinalizedCarrierDto) -> Result<(), SignalAdapterError> {
    for (name, digest) in [
        ("carrier federation_id", &carrier.federation_id),
        ("carrier content_root", &carrier.content_root),
        ("carrier activation_digest", &carrier.activation_digest),
        ("carrier content_session", &carrier.content_session),
        ("carrier actor_root", &carrier.actor_root),
        ("carrier player_key", &carrier.player_key),
    ] {
        validate_digest(name, digest)?;
    }
    Ok(())
}

fn validate_request(request: &SignalRequestDto) -> Result<(), SignalAdapterError> {
    validate_id("request mission_id", request.mission_id)?;
    for (name, digest) in [
        ("request federation_id", &request.federation_id),
        ("request content_root", &request.content_root),
        ("request activation_digest", &request.activation_digest),
        ("request content_session", &request.content_session),
        ("request run_seed", &request.run_seed),
        ("request actor_root", &request.actor_root),
        ("request player_key", &request.player_key),
    ] {
        validate_digest(name, digest)?;
    }
    if request.actions.len() > SIGNAL_ACTION_LIMIT {
        return Err(SignalAdapterError::InvalidField("request actions"));
    }
    request.actions.iter().try_for_each(validate_code)
}

fn validate_code(code: &SignalCodeDto) -> Result<(), SignalAdapterError> {
    if code.low > 5 || code.mid > 5 || code.high > 5 {
        return Err(SignalAdapterError::InvalidField("Signal code band"));
    }
    Ok(())
}

fn validate_metrics(
    intel: u64,
    supplies: u64,
    cohesion: u64,
    influence: u64,
    score: u64,
) -> Result<(), SignalAdapterError> {
    if [intel, supplies, cohesion, influence, score]
        .into_iter()
        .any(|value| value > METRIC_LIMIT)
    {
        return Err(SignalAdapterError::InvalidField("metric"));
    }
    Ok(())
}

fn validate_id(name: &'static str, id: u64) -> Result<(), SignalAdapterError> {
    if id > u64::from(u32::MAX) {
        return Err(SignalAdapterError::InvalidField(name));
    }
    Ok(())
}

fn validate_digest(name: &'static str, digest: &str) -> Result<(), SignalAdapterError> {
    if digest.len() != 64
        || !digest
            .as_bytes()
            .iter()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(byte))
    {
        return Err(SignalAdapterError::InvalidField(name));
    }
    Ok(())
}

fn validate_sorted_ids(
    name: &'static str,
    ids: &[u64],
    limit: usize,
) -> Result<(), SignalAdapterError> {
    if ids.len() > limit
        || ids.iter().any(|id| *id > u64::from(u32::MAX))
        || !ids.windows(2).all(|pair| pair[0] < pair[1])
    {
        return Err(SignalAdapterError::InvalidField(name));
    }
    Ok(())
}

fn validate_sorted_artifacts(
    name: &'static str,
    artifacts: &[ArtifactRefDto],
    limit: usize,
) -> Result<(), SignalAdapterError> {
    for artifact in artifacts {
        validate_artifact(artifact)?;
    }
    if artifacts.len() > limit
        || !artifacts
            .windows(2)
            .all(|pair| artifact_key(&pair[0]) < artifact_key(&pair[1]))
    {
        return Err(SignalAdapterError::InvalidField(name));
    }
    Ok(())
}

fn artifact_key(artifact: &ArtifactRefDto) -> (u64, u64, &str, &str) {
    (
        artifact.mission_id,
        artifact.artifact_id,
        &artifact.source_digest,
        &artifact.content_digest,
    )
}

fn receipt_key(receipt: &ReceiptKeyDto) -> (&str, &str, u64, &str, u64) {
    (
        &receipt.federation_id,
        &receipt.content_session,
        receipt.content_epoch,
        &receipt.player_key,
        receipt.player_counter,
    )
}

fn counter_key(row: &PlayerCounterRowDto) -> (&str, &str, u64, &str) {
    (
        &row.federation_id,
        &row.content_session,
        row.content_epoch,
        &row.player_key,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::{CellId, field_from_u64};
    use dregg_sdk::poa_signal::{SIGNAL_CLAIM_TOPIC_V1, signal_claim_event};
    use dregg_turn::action::{Event, symbol};

    const INPUT_FILE: &str =
        include_str!("../../dregg-lean-ffi/tests/fixtures/poa-signal-input-v1.json");
    const OUTPUT_FILE: &str =
        include_str!("../../dregg-lean-ffi/tests/fixtures/poa-signal-output-v1.json");

    fn fixture(bytes: &'static str) -> &'static str {
        bytes.strip_suffix('\n').expect("one fixture newline")
    }

    fn claim() -> SignalClaimV1 {
        SignalClaimV1::new(1, SignalCode::new(2, 4, 1).unwrap()).unwrap()
    }

    #[test]
    fn reserved_route_is_exact_and_malformed_is_irrevocable() {
        let event = signal_claim_event(claim());
        let effect = Effect::EmitEvent {
            cell: CellId::from_bytes([9; 32]),
            event,
        };
        assert_eq!(
            classify_signal_effect(&effect),
            Ok(SignalEffectRoute::Signal(claim()))
        );

        let malformed = Effect::EmitEvent {
            cell: CellId::from_bytes([9; 32]),
            event: Event::new(symbol(SIGNAL_CLAIM_TOPIC_V1), vec![field_from_u64(1)]),
        };
        assert!(matches!(
            classify_signal_effect(&malformed),
            Err(SignalAdapterError::Claim(
                SignalClaimError::MalformedReserved(_)
            ))
        ));
    }

    #[test]
    fn canonical_dtos_round_trip_exactly_and_reject_reordering() {
        let input = CanonicalSignalInput::parse(fixture(INPUT_FILE)).unwrap();
        assert_eq!(input.as_str(), fixture(INPUT_FILE));
        let output = CanonicalSignalOutput::parse(fixture(OUTPUT_FILE)).unwrap();
        assert_eq!(output.as_str(), fixture(OUTPUT_FILE));

        let reordered = fixture(INPUT_FILE).replacen(
            "{\"format\":\"POA-SIGNAL-IN-1\",\"config\":",
            "{\"config\":",
            1,
        );
        let reordered =
            reordered.replacen("\"world\":", "\"format\":\"POA-SIGNAL-IN-1\",\"world\":", 1);
        assert!(matches!(
            CanonicalSignalInput::parse(&reordered),
            Err(SignalAdapterError::Noncanonical(_))
        ));
    }

    #[test]
    fn public_claim_cannot_substitute_authority_fields() {
        let parsed = CanonicalSignalInput::parse(fixture(INPUT_FILE)).unwrap();
        let context = parsed.authority_context();
        let prepared = prepare_signal_input(&context, claim()).unwrap();
        let request = &prepared.dto.request;

        assert_eq!(request.federation_id, context.carrier.federation_id);
        assert_eq!(request.content_root, context.carrier.content_root);
        assert_eq!(request.activation_digest, context.carrier.activation_digest);
        assert_eq!(request.content_session, context.carrier.content_session);
        assert_eq!(request.content_epoch, context.carrier.content_epoch);
        assert_eq!(request.actor_root, context.carrier.actor_root);
        assert_eq!(request.player_key, context.carrier.player_key);
        assert_eq!(
            request.previous_player_counter,
            context.carrier.current_player_counter
        );
        assert_eq!(request.run_seed, context.config.mission.run_seed);
        assert_eq!(request.expected_world_sequence, context.world.sequence);
        assert_eq!(request.expected_canon_revision, context.canon.revision);
        assert_eq!(request.actions, vec![SignalCodeDto::from(claim().code())]);
        assert_eq!(prepared.as_str(), fixture(INPUT_FILE));
    }

    #[test]
    fn exact_output_parser_does_not_make_a_substituted_reply_acceptable() {
        let input = CanonicalSignalInput::parse(fixture(INPUT_FILE)).unwrap();
        let honest = CanonicalSignalOutput::parse(fixture(OUTPUT_FILE)).unwrap();
        validate_evaluation_binding(&input.dto, &honest.dto).unwrap();

        let mut substituted_dto = honest.dto.clone();
        substituted_dto.receipt.player_key = "ff".repeat(32);
        let substituted_bytes = serde_json::to_string(&substituted_dto).unwrap();
        let substituted = CanonicalSignalOutput::parse(&substituted_bytes)
            .expect("the transport parser alone is not semantic authority");
        assert!(matches!(
            validate_evaluation_binding(&input.dto, &substituted.dto),
            Err(SignalAdapterError::OutputBinding(_))
        ));
    }

    #[test]
    fn substituted_mission_refuses_before_ffi() {
        let parsed = CanonicalSignalInput::parse(fixture(INPUT_FILE)).unwrap();
        let context = parsed.authority_context();
        let other = SignalClaimV1::new(2, claim().code()).unwrap();
        assert!(matches!(
            prepare_signal_input(&context, other),
            Err(SignalAdapterError::MissionMismatch {
                claimed: 2,
                active: 1
            })
        ));
    }

    #[test]
    fn linked_lean_candidate_is_exact_but_not_committed() {
        if !dregg_lean_ffi::demand_lean(
            dregg_lean_ffi::poa_ffi::poa_signal_judge_available(),
            "the internal PoA Signal judge export",
        ) {
            return;
        }
        let parsed = CanonicalSignalInput::parse(fixture(INPUT_FILE)).unwrap();
        let candidate = evaluate_signal_claim(&parsed.authority_context(), claim()).unwrap();
        assert_eq!(candidate.input().as_str(), fixture(INPUT_FILE));
        assert_eq!(candidate.output().as_str(), fixture(OUTPUT_FILE));
    }
}
