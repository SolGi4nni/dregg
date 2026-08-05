//! Read-only semantic replay of caller-supplied Path of Angels Signal wires.
//!
//! Rust checks the claimed storage envelope and exact byte bindings; every game
//! transition is rerun by Lean's sole Signal judge. This proves semantic
//! self-consistency only. The bundle contains no SignedTurn, executor receipt,
//! signer reconstruction, or durable CommitRecord evidence and therefore
//! authenticates neither finality nor provenance. There is no Rust semantic
//! fallback and no promotion-authority path in this module.

use std::fs::OpenOptions;
use std::io::Read;
use std::path::{Path, PathBuf};

#[cfg(unix)]
use std::os::unix::fs::OpenOptionsExt;

use serde::{Deserialize, Serialize};
use serde_json::value::RawValue;
use sha2::{Digest as _, Sha256};
use thiserror::Error;

pub const EXACT_REPLAY_BUNDLE_FORMAT_V1: &str = "POA-SIGNAL-EXACT-REPLAY-BUNDLE-1";
pub const REPLAY_REPORT_FORMAT_V1: &str = "POA-SIGNAL-REPLAY-REPORT-1";
pub const SEMANTIC_REVIEW_FORMAT_V1: &str = "POA-SIGNAL-SEMANTIC-REVIEW-1";

const HEAD_MAGIC: [u8; 4] = *b"PSHD";
const TRANSITION_MAGIC: [u8; 4] = *b"PSTR";
const WIRE_VERSION: u8 = 1;
const HEADER_LEN: usize = 8;
const HEAD_FIXED_LEN: usize = HEADER_LEN + 32 + 32 + 8 + 8 + 8 + 32 + 4 + 4;
const TRANSITION_FIXED_LEN: usize =
    HEADER_LEN + 32 + 8 + 8 + 32 + 32 + 32 + 32 + 32 + 32 + 32 + 4 + 4 + 4 + 4;
const SEAL_LEN: usize = 32;
const MAX_SIGNAL_IMAGE_BYTES: usize = 16 * 1024 * 1024;
const MAX_BUNDLE_BYTES: u64 = 512 * 1024 * 1024;
const MAX_TRANSITIONS_PER_BUNDLE: usize = 65_536;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExactReplayBundleV1 {
    pub format: String,
    pub authority_id: String,
    pub deployment_digest: String,
    pub genesis_head_wire_hex: String,
    pub transition_wires_hex: Vec<String>,
    pub expected_head_digest: String,
}

/// Machine-readable semantic replay report. No field is a finality claim.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ReplayReportV1 {
    pub format: &'static str,
    pub status: &'static str,
    pub authority_status: &'static str,
    pub claimed_authority_id: String,
    pub claimed_deployment_digest: String,
    pub semantic_transitions_replayed: u64,
    pub native_lean_transitions_replayed: u64,
    pub first_claimed_commit_ordinal: Option<u64>,
    pub last_claimed_commit_ordinal: Option<u64>,
    pub replayed_head_digest: String,
    pub transition_count: u64,
    pub world_sequence: u64,
    pub canon_revision: u64,
    pub last_transition_digest: String,
    pub config_sha256: String,
    pub canon_sha256: String,
    pub exact_wire_bytes_replayed: u64,
    pub semantic_judge: &'static str,
}

/// Deterministic semantic inspection of one caller-supplied transition. All
/// turn/receipt/signer coordinates are explicitly unverified claims.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct SemanticEventReviewV1 {
    pub sequence: u64,
    pub claimed_commit_ordinal: u64,
    pub claimed_turn_hash: String,
    pub claimed_receipt_hash: String,
    pub predecessor_head_digest: String,
    pub successor_head_digest: String,
    pub transition_digest: String,
    pub judge_input_digest: String,
    pub judge_output_digest: String,
    pub claimed_federation_id: String,
    pub claimed_actor_root: String,
    pub claimed_signer: String,
    pub mission_id: u64,
    pub receipt: serde_json::Value,
    pub beta_artifacts_added: Vec<ObservedArtifactV1>,
    pub exact_judge_input: String,
    pub exact_judge_output: String,
}

/// Exact artifact identity as it appears on the semantically accepted wire.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct ObservedArtifactV1 {
    pub mission_id: u64,
    pub artifact_id: u64,
    pub source_digest: String,
    pub content_digest: String,
}

#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct SignalSemanticReviewV1 {
    pub format: &'static str,
    pub status: &'static str,
    pub authority_status: &'static str,
    pub source_bundle_sha256: String,
    pub replay: ReplayReportV1,
    pub events: Vec<SemanticEventReviewV1>,
    pub beta_artifacts_observed: Vec<SemanticBetaObservationV1>,
    pub editorial_authority: &'static str,
    pub required_authority_bridge: &'static str,
}

/// Semantic beta observation only. It is not finalized provenance, promotion
/// evidence, a `CanonDecision`, or a curator capability.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SemanticBetaObservationV1 {
    pub artifact: ObservedArtifactV1,
    pub first_observed_sequence: u64,
    pub first_observed_transition_digest: String,
    pub replayed_head_digest: String,
    pub replayed_canon_revision: u64,
    pub evidence_status: &'static str,
    pub authorization_status: &'static str,
}

#[derive(Debug, Error)]
pub enum ReplayError {
    #[error("cannot read exact replay bundle {path}: {source}")]
    Io {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
    #[error("exact replay bundle refused: {0}")]
    Bundle(String),
    #[error("transition {sequence} refused: {reason}")]
    Transition { sequence: u64, reason: String },
    #[error("native Lean Signal judge unavailable or failed at transition {sequence}: {reason}")]
    LeanTransport { sequence: u64, reason: String },
    #[error("native Lean refused recorded transition {0}")]
    LeanRejected(u64),
    #[error("native Lean output mismatch at transition {0}")]
    LeanMismatch(u64),
    #[error("semantic history projection refused: {0}")]
    Projection(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Head {
    wire: Vec<u8>,
    authority_id: [u8; 32],
    deployment_digest: [u8; 32],
    transition_count: u64,
    world_sequence: u64,
    canon_revision: u64,
    last_transition_digest: [u8; 32],
    config: Vec<u8>,
    canon: Vec<u8>,
}

impl Head {
    fn digest(&self) -> [u8; 32] {
        head_seal(&self.wire[..self.wire.len() - SEAL_LEN])
    }
}

#[derive(Clone, Debug)]
struct Transition {
    authority_id: [u8; 32],
    sequence: u64,
    commit_ordinal: u64,
    turn_hash: [u8; 32],
    receipt_hash: [u8; 32],
    predecessor_head_digest: [u8; 32],
    successor_head_digest: [u8; 32],
    transition_digest: [u8; 32],
    judge_input_digest: [u8; 32],
    judge_output_digest: [u8; 32],
    predecessor: Head,
    successor: Head,
    judge_input: Vec<u8>,
    judge_output: Vec<u8>,
}

struct SemanticallyReplayedHistory {
    report: ReplayReportV1,
    source_bundle_sha256: [u8; 32],
    current: Head,
    transitions: Vec<Transition>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct JudgeInputEnvelope {
    format: String,
    config: Box<RawValue>,
    world: Box<RawValue>,
    canon: Box<RawValue>,
    carrier: Box<RawValue>,
    slot_state: SlotStateEnvelope,
    request: Box<RawValue>,
}

/// The slot state as a REVIEW surface: slot and commitment, and no secret.
///
/// ⚠ `secret` is deserialized into [`serde::de::IgnoredAny`], which consumes the
/// value and binds nothing. This is a structural drop, not a redaction: there is no
/// field holding the bytes, so no future formatter, `Debug` impl or report field can
/// reach them, and the struct cannot derive `Serialize` at all because `IgnoredAny`
/// does not implement it. A `Box<RawValue>` here — the obvious choice, matching
/// every sibling field — would have retained the secret verbatim and turned every
/// archived review artifact into key material at rest.
///
/// A reviewer does not need it. What a review establishes is that the served
/// instance matched the PUBLISHED commitment, and slot + commitment say that. The
/// secret would let a reviewer re-derive the seed, but re-derivation is
/// `dregg_poa_signal_slot_derive` run against a secret the reviewer holds — not one
/// read out of a report.
///
/// The field is still required and still `deny_unknown_fields`: an envelope that
/// omits `secret`, or carries anything else, is refused. Dropping the value is not
/// the same as not checking the shape.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct SlotStateEnvelope {
    slot: u64,
    secret: serde::de::IgnoredAny,
    commitment: String,
}

/// The two instance fields a client states. Deliberately partial: the request has
/// many more, and this is only the slot binding.
#[derive(Deserialize)]
struct RequestSlotBinding {
    slot: u64,
    slot_commitment: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct JudgeOutputEnvelope {
    format: String,
    receipt: Box<RawValue>,
    successor_world: Box<RawValue>,
    successor_canon: Box<RawValue>,
}

/// Read and replay one bounded exact bundle. Symlinks are refused on Unix so a
/// privileged operator cannot be raced onto a different input after review.
pub fn replay_exact_bundle_file(path: impl AsRef<Path>) -> Result<ReplayReportV1, ReplayError> {
    let bytes = read_bundle_file(path.as_ref())?;
    replay_exact_bundle_bytes(&bytes)
}

/// Project caller-supplied transitions after native Lean semantic replay.
pub fn export_semantic_review_file(
    path: impl AsRef<Path>,
) -> Result<SignalSemanticReviewV1, ReplayError> {
    let bytes = read_bundle_file(path.as_ref())?;
    export_semantic_review_bytes(&bytes)
}

fn read_bundle_file(path: &Path) -> Result<Vec<u8>, ReplayError> {
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    options.custom_flags(libc::O_NOFOLLOW);
    let file = options.open(path).map_err(|source| ReplayError::Io {
        path: path.to_path_buf(),
        source,
    })?;
    let metadata = file.metadata().map_err(|source| ReplayError::Io {
        path: path.to_path_buf(),
        source,
    })?;
    if !metadata.is_file() {
        return Err(ReplayError::Bundle("input is not a regular file".into()));
    }
    if metadata.len() > MAX_BUNDLE_BYTES {
        return Err(ReplayError::Bundle(format!(
            "input exceeds the {MAX_BUNDLE_BYTES}-byte bundle cap"
        )));
    }
    let mut bytes = Vec::with_capacity(metadata.len() as usize);
    file.take(MAX_BUNDLE_BYTES + 1)
        .read_to_end(&mut bytes)
        .map_err(|source| ReplayError::Io {
            path: path.to_path_buf(),
            source,
        })?;
    if bytes.len() as u64 > MAX_BUNDLE_BYTES {
        return Err(ReplayError::Bundle(format!(
            "input exceeds the {MAX_BUNDLE_BYTES}-byte bundle cap"
        )));
    }
    Ok(bytes)
}

/// Replay one serialized bundle through the linked native Lean semantic judge.
pub fn replay_exact_bundle_bytes(bytes: &[u8]) -> Result<ReplayReportV1, ReplayError> {
    replay_exact_bundle_with(bytes, native_judge)
}

pub fn export_semantic_review_bytes(bytes: &[u8]) -> Result<SignalSemanticReviewV1, ReplayError> {
    let history = verify_exact_bundle_with(bytes, native_judge)?;
    project_semantic_history(history)
}

fn native_judge(input: &str) -> Result<Option<String>, String> {
    match dregg_lean_ffi::poa_ffi::judge_poa_signal(input) {
        Ok(dregg_lean_ffi::poa_ffi::PoaSignalVerdict::Accepted(output)) => {
            Ok(Some(output.into_string()))
        }
        Ok(dregg_lean_ffi::poa_ffi::PoaSignalVerdict::Rejected) => Ok(None),
        Err(reason) => Err(reason),
    }
}

fn project_semantic_history(
    history: SemanticallyReplayedHistory,
) -> Result<SignalSemanticReviewV1, ReplayError> {
    let mut events = Vec::with_capacity(history.transitions.len());
    let mut first_observed = std::collections::BTreeMap::<ObservedArtifactV1, (u64, String)>::new();

    for transition in &history.transitions {
        let input: serde_json::Value = serde_json::from_slice(&transition.judge_input)
            .map_err(|error| ReplayError::Projection(format!("judge input JSON: {error}")))?;
        let output: serde_json::Value = serde_json::from_slice(&transition.judge_output)
            .map_err(|error| ReplayError::Projection(format!("judge output JSON: {error}")))?;
        let predecessor_canon: serde_json::Value =
            serde_json::from_slice(&transition.predecessor.canon).map_err(|error| {
                ReplayError::Projection(format!("predecessor Canon JSON: {error}"))
            })?;
        let carrier = object_field(&input, "carrier")?;
        let receipt = output
            .get("receipt")
            .cloned()
            .ok_or_else(|| ReplayError::Projection("judge output lacks receipt".into()))?;
        let mission_id = receipt
            .get("mission")
            .and_then(|mission| mission.get("mission_id"))
            .and_then(serde_json::Value::as_u64)
            .ok_or_else(|| ReplayError::Projection("receipt lacks mission_id".into()))?;
        let before = artifact_set(
            predecessor_canon
                .get("world")
                .and_then(|world| world.get("beta_artifacts"))
                .ok_or_else(|| {
                    ReplayError::Projection("predecessor Canon lacks world.beta_artifacts".into())
                })?,
        )?;
        let after = artifact_set(
            output
                .get("successor_canon")
                .and_then(|canon| canon.get("world"))
                .and_then(|world| world.get("beta_artifacts"))
                .ok_or_else(|| {
                    ReplayError::Projection(
                        "judge output lacks successor_canon.world.beta_artifacts".into(),
                    )
                })?,
        )?;
        let added: Vec<_> = after.difference(&before).cloned().collect();
        for artifact in &added {
            first_observed
                .entry(artifact.clone())
                .or_insert_with(|| (transition.sequence, hex32(transition.transition_digest)));
        }
        events.push(SemanticEventReviewV1 {
            sequence: transition.sequence,
            claimed_commit_ordinal: transition.commit_ordinal,
            claimed_turn_hash: hex32(transition.turn_hash),
            claimed_receipt_hash: hex32(transition.receipt_hash),
            predecessor_head_digest: hex32(transition.predecessor_head_digest),
            successor_head_digest: hex32(transition.successor_head_digest),
            transition_digest: hex32(transition.transition_digest),
            judge_input_digest: hex32(transition.judge_input_digest),
            judge_output_digest: hex32(transition.judge_output_digest),
            claimed_federation_id: string_field(carrier, "federation_id")?.to_owned(),
            claimed_actor_root: string_field(carrier, "actor_root")?.to_owned(),
            claimed_signer: string_field(carrier, "player_key")?.to_owned(),
            mission_id,
            receipt,
            beta_artifacts_added: added,
            exact_judge_input: String::from_utf8(transition.judge_input.clone()).map_err(|_| {
                ReplayError::Projection("replayed judge input ceased to be UTF-8".into())
            })?,
            exact_judge_output: String::from_utf8(transition.judge_output.clone()).map_err(
                |_| ReplayError::Projection("replayed judge output ceased to be UTF-8".into()),
            )?,
        });
    }

    let final_canon: serde_json::Value = serde_json::from_slice(&history.current.canon)
        .map_err(|error| ReplayError::Projection(format!("current Canon JSON: {error}")))?;
    let final_world = object_field(&final_canon, "world")?;
    let final_beta = artifact_set(final_world.get("beta_artifacts").ok_or_else(|| {
        ReplayError::Projection("current Canon lacks world.beta_artifacts".into())
    })?)?;
    let final_alpha =
        artifact_set(final_canon.get("alpha").ok_or_else(|| {
            ReplayError::Projection("current Canon lacks alpha artifacts".into())
        })?)?;
    let final_superseded = artifact_set(final_canon.get("superseded").ok_or_else(|| {
        ReplayError::Projection("current Canon lacks superseded artifacts".into())
    })?)?;
    let mut beta_artifacts_observed = Vec::new();
    for artifact in final_beta {
        if final_alpha.contains(&artifact) || final_superseded.contains(&artifact) {
            continue;
        }
        let Some((sequence, transition_digest)) = first_observed.get(&artifact) else {
            // Genesis beta entries have no transition-level semantic observation
            // and are deliberately absent from this event-derived review.
            continue;
        };
        beta_artifacts_observed.push(SemanticBetaObservationV1 {
            artifact,
            first_observed_sequence: *sequence,
            first_observed_transition_digest: transition_digest.clone(),
            replayed_head_digest: history.report.replayed_head_digest.clone(),
            replayed_canon_revision: history.report.canon_revision,
            evidence_status: "semantic_observation_only_unverified_carrier",
            authorization_status: "unavailable_missing_finality_authority_evidence",
        });
    }

    Ok(SignalSemanticReviewV1 {
        format: SEMANTIC_REVIEW_FORMAT_V1,
        status: "semantic_review_only",
        authority_status: "unverified_no_signed_turn_or_commit_evidence",
        source_bundle_sha256: format!("sha256:{}", hex32(history.source_bundle_sha256)),
        replay: history.report,
        events,
        beta_artifacts_observed,
        editorial_authority: "none; semantic review cannot produce promotion evidence or construct CuratorCapability",
        required_authority_bridge: "node must reconstruct the exact carrier from a finalized SignedTurn, executor receipt, signer, and durable CommitRecord",
    })
}

fn artifact_set(
    value: &serde_json::Value,
) -> Result<std::collections::BTreeSet<ObservedArtifactV1>, ReplayError> {
    let rows = value
        .as_array()
        .ok_or_else(|| ReplayError::Projection("artifact collection is not an array".into()))?;
    rows.iter()
        .map(|row| {
            let artifact = ObservedArtifactV1 {
                mission_id: u64_field(row, "mission_id")?,
                artifact_id: u64_field(row, "artifact_id")?,
                source_digest: string_field(row, "source_digest")?.to_owned(),
                content_digest: string_field(row, "content_digest")?.to_owned(),
            };
            for (field, digest) in [
                ("source_digest", artifact.source_digest.as_str()),
                ("content_digest", artifact.content_digest.as_str()),
            ] {
                parse_hex32(digest, field).map_err(|error| {
                    ReplayError::Projection(format!("artifact {field}: {error}"))
                })?;
            }
            Ok(artifact)
        })
        .collect()
}

fn object_field<'a>(
    value: &'a serde_json::Value,
    key: &str,
) -> Result<&'a serde_json::Value, ReplayError> {
    value
        .get(key)
        .filter(|value| value.is_object())
        .ok_or_else(|| ReplayError::Projection(format!("field {key:?} is not an object")))
}

fn string_field<'a>(value: &'a serde_json::Value, key: &str) -> Result<&'a str, ReplayError> {
    value
        .get(key)
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| ReplayError::Projection(format!("field {key:?} is not a string")))
}

fn u64_field(value: &serde_json::Value, key: &str) -> Result<u64, ReplayError> {
    value
        .get(key)
        .and_then(serde_json::Value::as_u64)
        .ok_or_else(|| ReplayError::Projection(format!("field {key:?} is not a u64")))
}

fn replay_exact_bundle_with<F>(bytes: &[u8], mut judge: F) -> Result<ReplayReportV1, ReplayError>
where
    F: FnMut(&str) -> Result<Option<String>, String>,
{
    Ok(verify_exact_bundle_with(bytes, &mut judge)?.report)
}

fn verify_exact_bundle_with<F>(
    bytes: &[u8],
    mut judge: F,
) -> Result<SemanticallyReplayedHistory, ReplayError>
where
    F: FnMut(&str) -> Result<Option<String>, String>,
{
    if bytes.len() as u64 > MAX_BUNDLE_BYTES {
        return Err(ReplayError::Bundle(format!(
            "input exceeds the {MAX_BUNDLE_BYTES}-byte bundle cap"
        )));
    }
    let bundle: ExactReplayBundleV1 = strict_json(bytes, "bundle")?;
    if bundle.format != EXACT_REPLAY_BUNDLE_FORMAT_V1 {
        return Err(ReplayError::Bundle(format!(
            "wrong format {:?}",
            bundle.format
        )));
    }
    if bundle.transition_wires_hex.len() > MAX_TRANSITIONS_PER_BUNDLE {
        return Err(ReplayError::Bundle(format!(
            "more than {MAX_TRANSITIONS_PER_BUNDLE} transitions"
        )));
    }
    let authority_id = parse_hex32(&bundle.authority_id, "authority_id")?;
    let deployment_digest = parse_hex32(&bundle.deployment_digest, "deployment_digest")?;
    let expected_head_digest = parse_hex32(&bundle.expected_head_digest, "expected_head_digest")?;
    let genesis_wire = decode_hex(
        &bundle.genesis_head_wire_hex,
        "genesis_head_wire_hex",
        MAX_SIGNAL_IMAGE_BYTES + HEAD_FIXED_LEN + SEAL_LEN,
    )?;
    let genesis = decode_head(genesis_wire).map_err(ReplayError::Bundle)?;
    if genesis.transition_count != 0 || genesis.last_transition_digest != [0; 32] {
        return Err(ReplayError::Bundle(
            "genesis head is not a zero-transition head".into(),
        ));
    }
    if genesis.authority_id != authority_id || genesis.deployment_digest != deployment_digest {
        return Err(ReplayError::Bundle(
            "bundle selector disagrees with genesis authority/deployment".into(),
        ));
    }

    let mut current = genesis;
    let mut previous_commit_ordinal = None;
    let mut first_commit_ordinal = None;
    let mut exact_wire_bytes = current.wire.len() as u64;
    let mut semantically_replayed_transitions =
        Vec::with_capacity(bundle.transition_wires_hex.len());

    for (index, encoded) in bundle.transition_wires_hex.iter().enumerate() {
        let expected_sequence = u64::try_from(index)
            .ok()
            .and_then(|index| index.checked_add(1))
            .ok_or_else(|| ReplayError::Bundle("transition sequence overflow".into()))?;
        let wire = decode_hex(
            encoded,
            "transition_wires_hex entry",
            (MAX_SIGNAL_IMAGE_BYTES * 4) + TRANSITION_FIXED_LEN + SEAL_LEN + (HEAD_FIXED_LEN * 2),
        )
        .map_err(|error| ReplayError::Transition {
            sequence: expected_sequence,
            reason: error.to_string(),
        })?;
        exact_wire_bytes = exact_wire_bytes
            .checked_add(wire.len() as u64)
            .ok_or_else(|| ReplayError::Bundle("replayed byte count overflow".into()))?;
        let transition = decode_transition(wire).map_err(|reason| ReplayError::Transition {
            sequence: expected_sequence,
            reason,
        })?;
        if transition.sequence != expected_sequence {
            return Err(ReplayError::Transition {
                sequence: expected_sequence,
                reason: format!(
                    "gap or reorder: encoded sequence is {}",
                    transition.sequence
                ),
            });
        }
        if transition.authority_id != authority_id {
            return Err(ReplayError::Transition {
                sequence: expected_sequence,
                reason: "authority id changed".into(),
            });
        }
        if transition.predecessor.wire != current.wire {
            return Err(ReplayError::Transition {
                sequence: expected_sequence,
                reason: "exact predecessor wire does not equal prior chain head".into(),
            });
        }
        if transition.successor.deployment_digest != deployment_digest {
            return Err(ReplayError::Transition {
                sequence: expected_sequence,
                reason: "deployment digest changed".into(),
            });
        }
        if previous_commit_ordinal.is_some_and(|previous| transition.commit_ordinal <= previous) {
            return Err(ReplayError::Transition {
                sequence: expected_sequence,
                reason: "commit ordinals are not strictly increasing".into(),
            });
        }

        verify_judge_state_binding(&transition).map_err(|reason| ReplayError::Transition {
            sequence: expected_sequence,
            reason,
        })?;
        let input =
            std::str::from_utf8(&transition.judge_input).map_err(|_| ReplayError::Transition {
                sequence: expected_sequence,
                reason: "judge input is not UTF-8".into(),
            })?;
        let replayed = judge(input).map_err(|reason| ReplayError::LeanTransport {
            sequence: expected_sequence,
            reason,
        })?;
        let Some(replayed) = replayed else {
            return Err(ReplayError::LeanRejected(expected_sequence));
        };
        if replayed.as_bytes() != transition.judge_output {
            return Err(ReplayError::LeanMismatch(expected_sequence));
        }

        first_commit_ordinal.get_or_insert(transition.commit_ordinal);
        previous_commit_ordinal = Some(transition.commit_ordinal);
        current = transition.successor.clone();
        semantically_replayed_transitions.push(transition);
    }

    if current.digest() != expected_head_digest {
        return Err(ReplayError::Bundle(format!(
            "deterministic replay head {} disagrees with expected {}",
            hex32(current.digest()),
            bundle.expected_head_digest
        )));
    }
    if current.transition_count != bundle.transition_wires_hex.len() as u64 {
        return Err(ReplayError::Bundle(
            "final head transition count disagrees with bundle cardinality".into(),
        ));
    }

    let report = ReplayReportV1 {
        format: REPLAY_REPORT_FORMAT_V1,
        status: "semantic_review_only",
        authority_status: "unverified_no_signed_turn_or_commit_evidence",
        claimed_authority_id: hex32(authority_id),
        claimed_deployment_digest: hex32(deployment_digest),
        semantic_transitions_replayed: current.transition_count,
        native_lean_transitions_replayed: current.transition_count,
        first_claimed_commit_ordinal: first_commit_ordinal,
        last_claimed_commit_ordinal: previous_commit_ordinal,
        replayed_head_digest: hex32(current.digest()),
        transition_count: current.transition_count,
        world_sequence: current.world_sequence,
        canon_revision: current.canon_revision,
        last_transition_digest: hex32(current.last_transition_digest),
        config_sha256: hex32(sha256(&current.config)),
        canon_sha256: hex32(sha256(&current.canon)),
        exact_wire_bytes_replayed: exact_wire_bytes,
        semantic_judge: "Dregg2.Games.PathOfAngels.NetworkJudge.signalJudgeFFI",
    };
    Ok(SemanticallyReplayedHistory {
        report,
        source_bundle_sha256: sha256(bytes),
        current,
        transitions: semantically_replayed_transitions,
    })
}

fn decode_head(wire: Vec<u8>) -> Result<Head, String> {
    if wire.len() < HEAD_FIXED_LEN + SEAL_LEN {
        return Err("head wire is truncated".into());
    }
    if wire[..4] != HEAD_MAGIC || wire[4] != WIRE_VERSION || wire[5..8] != [0; 3] {
        return Err("head wire has wrong magic, version, or reserved bytes".into());
    }
    let payload_end = wire.len() - SEAL_LEN;
    if head_seal(&wire[..payload_end]).as_slice() != &wire[payload_end..] {
        return Err("head wire seal mismatch".into());
    }
    let config_len = u32_at(&wire, 128)? as usize;
    let canon_len = u32_at(&wire, 132)? as usize;
    let image_len = config_len
        .checked_add(canon_len)
        .ok_or("head image length overflow")?;
    if image_len > MAX_SIGNAL_IMAGE_BYTES {
        return Err("head config+Canon exceeds the wire cap".into());
    }
    let expected = HEAD_FIXED_LEN
        .checked_add(image_len)
        .and_then(|length| length.checked_add(SEAL_LEN))
        .ok_or("head wire length overflow")?;
    if expected != wire.len() {
        return Err("head wire has trailing or missing bytes".into());
    }
    if config_len == 0 || canon_len == 0 {
        return Err("head config and Canon must both be non-empty".into());
    }
    let config_end = HEAD_FIXED_LEN + config_len;
    let head = Head {
        authority_id: array_at(&wire, 8)?,
        deployment_digest: array_at(&wire, 40)?,
        transition_count: u64_at(&wire, 72)?,
        world_sequence: u64_at(&wire, 80)?,
        canon_revision: u64_at(&wire, 88)?,
        last_transition_digest: array_at(&wire, 96)?,
        config: wire[HEAD_FIXED_LEN..config_end].to_vec(),
        canon: wire[config_end..payload_end].to_vec(),
        wire,
    };
    if (head.transition_count == 0) != (head.last_transition_digest == [0; 32]) {
        return Err("head transition count/last digest invariant failed".into());
    }
    let canon: serde_json::Value =
        strict_json(&head.canon, "head Canon").map_err(|error| error.to_string())?;
    if json_u64(&canon, "revision")? != head.canon_revision
        || json_u64(
            canon.get("world").ok_or("head Canon is missing world")?,
            "sequence",
        )? != head.world_sequence
    {
        return Err("head scalar projection disagrees with exact Canon bytes".into());
    }
    Ok(head)
}

fn decode_transition(wire: Vec<u8>) -> Result<Transition, String> {
    if wire.len() < TRANSITION_FIXED_LEN + SEAL_LEN {
        return Err("transition wire is truncated".into());
    }
    if wire[..4] != TRANSITION_MAGIC || wire[4] != WIRE_VERSION || wire[5..8] != [0; 3] {
        return Err("transition wire has wrong magic, version, or reserved bytes".into());
    }
    let payload_end = wire.len() - SEAL_LEN;
    if transition_seal(&wire[..payload_end]).as_slice() != &wire[payload_end..] {
        return Err("transition wire seal mismatch".into());
    }
    let lengths = [
        u32_at(&wire, 280)? as usize,
        u32_at(&wire, 284)? as usize,
        u32_at(&wire, 288)? as usize,
        u32_at(&wire, 292)? as usize,
    ];
    let expected = lengths
        .into_iter()
        .try_fold(TRANSITION_FIXED_LEN, |total, length| {
            total.checked_add(length)
        })
        .and_then(|length| length.checked_add(SEAL_LEN))
        .ok_or("transition wire length overflow")?;
    if expected != wire.len() {
        return Err("transition wire has trailing or missing bytes".into());
    }
    let mut cursor = TRANSITION_FIXED_LEN;
    let predecessor_wire = take_vec(&wire, &mut cursor, lengths[0])?;
    let successor_wire = take_vec(&wire, &mut cursor, lengths[1])?;
    let judge_input = take_vec(&wire, &mut cursor, lengths[2])?;
    let judge_output = take_vec(&wire, &mut cursor, lengths[3])?;
    if cursor != payload_end {
        return Err("transition payload length mismatch".into());
    }
    if judge_input.is_empty()
        || judge_output.is_empty()
        || judge_input.len() > MAX_SIGNAL_IMAGE_BYTES
        || judge_output.len() > MAX_SIGNAL_IMAGE_BYTES
    {
        return Err("judge input/output is empty or exceeds the wire cap".into());
    }
    let transition = Transition {
        authority_id: array_at(&wire, 8)?,
        sequence: u64_at(&wire, 40)?,
        commit_ordinal: u64_at(&wire, 48)?,
        turn_hash: array_at(&wire, 56)?,
        receipt_hash: array_at(&wire, 88)?,
        predecessor_head_digest: array_at(&wire, 120)?,
        successor_head_digest: array_at(&wire, 152)?,
        transition_digest: array_at(&wire, 184)?,
        judge_input_digest: array_at(&wire, 216)?,
        judge_output_digest: array_at(&wire, 248)?,
        predecessor: decode_head(predecessor_wire)?,
        successor: decode_head(successor_wire)?,
        judge_input,
        judge_output,
    };
    validate_transition(&transition)?;
    Ok(transition)
}

fn validate_transition(transition: &Transition) -> Result<(), String> {
    let predecessor = &transition.predecessor;
    let successor = &transition.successor;
    if transition.sequence == 0 {
        return Err("transition sequence is zero".into());
    }
    if predecessor.authority_id != transition.authority_id
        || successor.authority_id != transition.authority_id
        || predecessor.deployment_digest != successor.deployment_digest
        || predecessor.config != successor.config
        || predecessor.digest() != transition.predecessor_head_digest
        || successor.digest() != transition.successor_head_digest
    {
        return Err("transition head identity/digest/config mismatch".into());
    }
    if predecessor.transition_count.checked_add(1) != Some(transition.sequence)
        || successor.transition_count != transition.sequence
        || predecessor.world_sequence.checked_add(1) != Some(successor.world_sequence)
        || predecessor.canon_revision.checked_add(1) != Some(successor.canon_revision)
    {
        return Err("transition does not advance sequence/revision exactly once".into());
    }
    if sha256(&transition.judge_input) != transition.judge_input_digest
        || sha256(&transition.judge_output) != transition.judge_output_digest
    {
        return Err("judge byte digest mismatch".into());
    }
    let expected = transition_core_digest(
        transition.authority_id,
        transition.sequence,
        transition.commit_ordinal,
        transition.turn_hash,
        transition.receipt_hash,
        transition.predecessor_head_digest,
        successor,
        transition.judge_input_digest,
        transition.judge_output_digest,
    );
    if expected != transition.transition_digest
        || successor.last_transition_digest != transition.transition_digest
    {
        return Err("transition-chain digest mismatch".into());
    }
    Ok(())
}

fn verify_judge_state_binding(transition: &Transition) -> Result<(), String> {
    let input: JudgeInputEnvelope =
        strict_json(&transition.judge_input, "judge input").map_err(|error| error.to_string())?;
    let output: JudgeOutputEnvelope =
        strict_json(&transition.judge_output, "judge output").map_err(|error| error.to_string())?;
    if input.format != "POA-SIGNAL-IN-1" || output.format != "POA-SIGNAL-OUT-1" {
        return Err("judge input/output format marker mismatch".into());
    }
    // Touch every strict field so future edits cannot accidentally make the
    // top-level envelope partial while retaining `deny_unknown_fields`.
    let _ = (
        &input.world,
        &input.carrier,
        &input.request,
        &output.receipt,
    );
    // The instance binding a reviewer CAN check without the secret: the slot and
    // commitment the client stated must be the node's own slot state. That the
    // commitment opens the secret, and that the run seed is its derivation, are
    // `Judged.admissionChecks` — re-established by the native re-judge, not here.
    let request_slot: RequestSlotBinding = serde_json::from_str(input.request.get())
        .map_err(|error| format!("judge input request slot binding refused: {error}"))?;
    if request_slot.slot != input.slot_state.slot
        || request_slot.slot_commitment != input.slot_state.commitment
    {
        return Err("judge input request does not name the node's slot state".into());
    }
    if input.config.get().as_bytes() != transition.predecessor.config
        || input.canon.get().as_bytes() != transition.predecessor.canon
    {
        return Err("judge input config/Canon is not the exact predecessor head image".into());
    }
    if output.successor_canon.get().as_bytes() != transition.successor.canon {
        return Err("judge output successor Canon is not the exact successor head image".into());
    }
    let successor_world: serde_json::Value = serde_json::from_str(output.successor_world.get())
        .map_err(|error| format!("successor_world JSON refused: {error}"))?;
    let successor_canon: serde_json::Value = serde_json::from_str(output.successor_canon.get())
        .map_err(|error| format!("successor_canon JSON refused: {error}"))?;
    if json_u64(&successor_world, "sequence")? != transition.successor.world_sequence
        || json_u64(&successor_canon, "revision")? != transition.successor.canon_revision
    {
        return Err("judge output scalar projection disagrees with successor head".into());
    }
    Ok(())
}

fn strict_json<T: for<'de> Deserialize<'de>>(bytes: &[u8], what: &str) -> Result<T, ReplayError> {
    let mut deserializer = serde_json::Deserializer::from_slice(bytes);
    let value = T::deserialize(&mut deserializer)
        .map_err(|error| ReplayError::Bundle(format!("{what} JSON refused: {error}")))?;
    deserializer
        .end()
        .map_err(|error| ReplayError::Bundle(format!("{what} has trailing bytes: {error}")))?;
    Ok(value)
}

fn json_u64(value: &serde_json::Value, key: &str) -> Result<u64, String> {
    value
        .get(key)
        .and_then(serde_json::Value::as_u64)
        .ok_or_else(|| format!("JSON field {key:?} is missing or not a u64"))
}

fn transition_core_digest(
    authority_id: [u8; 32],
    sequence: u64,
    commit_ordinal: u64,
    turn_hash: [u8; 32],
    receipt_hash: [u8; 32],
    predecessor_head_digest: [u8; 32],
    successor: &Head,
    judge_input_digest: [u8; 32],
    judge_output_digest: [u8; 32],
) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-poa-signal-transition-core-v1");
    hasher.update(&authority_id);
    hasher.update(&sequence.to_le_bytes());
    hasher.update(&commit_ordinal.to_le_bytes());
    hasher.update(&turn_hash);
    hasher.update(&receipt_hash);
    hasher.update(&predecessor_head_digest);
    hasher.update(&successor.world_sequence.to_le_bytes());
    hasher.update(&successor.canon_revision.to_le_bytes());
    hasher.update(&sha256(&successor.config));
    hasher.update(&sha256(&successor.canon));
    hasher.update(&judge_input_digest);
    hasher.update(&judge_output_digest);
    *hasher.finalize().as_bytes()
}

fn head_seal(bytes: &[u8]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-poa-signal-head-wire-v1");
    hasher.update(bytes);
    *hasher.finalize().as_bytes()
}

fn transition_seal(bytes: &[u8]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-poa-signal-transition-wire-v1");
    hasher.update(bytes);
    *hasher.finalize().as_bytes()
}

fn sha256(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}

fn parse_hex32(value: &str, field: &str) -> Result<[u8; 32], ReplayError> {
    let decoded = decode_hex(value, field, 32)?;
    decoded
        .try_into()
        .map_err(|_| ReplayError::Bundle(format!("{field} must be 64 lowercase hex digits")))
}

fn decode_hex(value: &str, field: &str, max_bytes: usize) -> Result<Vec<u8>, ReplayError> {
    if !value.len().is_multiple_of(2) || value.len() / 2 > max_bytes {
        return Err(ReplayError::Bundle(format!(
            "{field} has odd length or exceeds its byte cap"
        )));
    }
    let mut output = Vec::with_capacity(value.len() / 2);
    for pair in value.as_bytes().chunks_exact(2) {
        let high = lower_hex_nibble(pair[0])
            .ok_or_else(|| ReplayError::Bundle(format!("{field} is not lowercase hexadecimal")))?;
        let low = lower_hex_nibble(pair[1])
            .ok_or_else(|| ReplayError::Bundle(format!("{field} is not lowercase hexadecimal")))?;
        output.push((high << 4) | low);
    }
    Ok(output)
}

fn lower_hex_nibble(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        _ => None,
    }
}

fn hex32(bytes: [u8; 32]) -> String {
    let mut output = String::with_capacity(64);
    for byte in bytes {
        output.push(char::from(b"0123456789abcdef"[(byte >> 4) as usize]));
        output.push(char::from(b"0123456789abcdef"[(byte & 0x0f) as usize]));
    }
    output
}

fn u64_at(bytes: &[u8], offset: usize) -> Result<u64, String> {
    Ok(u64::from_le_bytes(array_at(bytes, offset)?))
}

fn u32_at(bytes: &[u8], offset: usize) -> Result<u32, String> {
    Ok(u32::from_le_bytes(array_at(bytes, offset)?))
}

fn array_at<const N: usize>(bytes: &[u8], offset: usize) -> Result<[u8; N], String> {
    bytes
        .get(offset..offset.checked_add(N).ok_or("wire offset overflow")?)
        .ok_or_else(|| "wire is truncated".to_owned())?
        .try_into()
        .map_err(|_| "wire fixed-width field is truncated".to_owned())
}

fn take_vec(bytes: &[u8], cursor: &mut usize, length: usize) -> Result<Vec<u8>, String> {
    let end = cursor.checked_add(length).ok_or("wire cursor overflow")?;
    let value = bytes
        .get(*cursor..end)
        .ok_or_else(|| "wire payload is truncated".to_owned())?
        .to_vec();
    *cursor = end;
    Ok(value)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn head_wire(
        authority: [u8; 32],
        deployment: [u8; 32],
        transition_count: u64,
        world_sequence: u64,
        canon_revision: u64,
        last_transition_digest: [u8; 32],
        config: &[u8],
        canon: &[u8],
    ) -> Vec<u8> {
        let mut wire = Vec::new();
        wire.extend_from_slice(&HEAD_MAGIC);
        wire.push(WIRE_VERSION);
        wire.extend_from_slice(&[0; 3]);
        wire.extend_from_slice(&authority);
        wire.extend_from_slice(&deployment);
        wire.extend_from_slice(&transition_count.to_le_bytes());
        wire.extend_from_slice(&world_sequence.to_le_bytes());
        wire.extend_from_slice(&canon_revision.to_le_bytes());
        wire.extend_from_slice(&last_transition_digest);
        wire.extend_from_slice(&(config.len() as u32).to_le_bytes());
        wire.extend_from_slice(&(canon.len() as u32).to_le_bytes());
        wire.extend_from_slice(config);
        wire.extend_from_slice(canon);
        let seal = head_seal(&wire);
        wire.extend_from_slice(&seal);
        wire
    }

    fn transition_wire(
        predecessor_wire: Vec<u8>,
        sequence: u64,
        commit_ordinal: u64,
        judge_input: Vec<u8>,
        judge_output: Vec<u8>,
        successor_canon: Vec<u8>,
    ) -> Vec<u8> {
        let predecessor = decode_head(predecessor_wire.clone()).unwrap();
        let input_digest = sha256(&judge_input);
        let output_digest = sha256(&judge_output);
        let successor_without_digest = head_wire(
            predecessor.authority_id,
            predecessor.deployment_digest,
            sequence,
            predecessor.world_sequence + 1,
            predecessor.canon_revision + 1,
            [0; 32],
            &predecessor.config,
            &successor_canon,
        );
        let successor = decode_head(successor_without_digest).unwrap_err();
        assert!(successor.contains("transition count/last digest"));
        // `transition_core_digest` ignores the successor's last digest. Build a
        // temporary logical successor to derive it, then seal the real head.
        let temporary = Head {
            wire: Vec::new(),
            authority_id: predecessor.authority_id,
            deployment_digest: predecessor.deployment_digest,
            transition_count: sequence,
            world_sequence: predecessor.world_sequence + 1,
            canon_revision: predecessor.canon_revision + 1,
            last_transition_digest: [1; 32],
            config: predecessor.config.clone(),
            canon: successor_canon.clone(),
        };
        let turn_hash = [0x31; 32];
        let receipt_hash = [0x41; 32];
        let digest = transition_core_digest(
            predecessor.authority_id,
            sequence,
            commit_ordinal,
            turn_hash,
            receipt_hash,
            predecessor.digest(),
            &temporary,
            input_digest,
            output_digest,
        );
        let successor_wire = head_wire(
            predecessor.authority_id,
            predecessor.deployment_digest,
            sequence,
            predecessor.world_sequence + 1,
            predecessor.canon_revision + 1,
            digest,
            &predecessor.config,
            &successor_canon,
        );
        let successor = decode_head(successor_wire.clone()).unwrap();

        let parts = [
            predecessor_wire.as_slice(),
            successor_wire.as_slice(),
            judge_input.as_slice(),
            judge_output.as_slice(),
        ];
        let mut wire = Vec::new();
        wire.extend_from_slice(&TRANSITION_MAGIC);
        wire.push(WIRE_VERSION);
        wire.extend_from_slice(&[0; 3]);
        wire.extend_from_slice(&predecessor.authority_id);
        wire.extend_from_slice(&sequence.to_le_bytes());
        wire.extend_from_slice(&commit_ordinal.to_le_bytes());
        wire.extend_from_slice(&turn_hash);
        wire.extend_from_slice(&receipt_hash);
        wire.extend_from_slice(&predecessor.digest());
        wire.extend_from_slice(&successor.digest());
        wire.extend_from_slice(&digest);
        wire.extend_from_slice(&input_digest);
        wire.extend_from_slice(&output_digest);
        for part in parts {
            wire.extend_from_slice(&(part.len() as u32).to_le_bytes());
        }
        for part in parts {
            wire.extend_from_slice(part);
        }
        let seal = transition_seal(&wire);
        wire.extend_from_slice(&seal);
        wire
    }

    fn judge_pair(config: &str, canon: &str, sequence: u64, revision: u64) -> (Vec<u8>, Vec<u8>) {
        // `slot_state` carries a secret on the real wire; this skeleton uses an
        // obviously-fake one, and `SlotStateEnvelope` discards it either way.
        let input = format!(
            "{{\"format\":\"POA-SIGNAL-IN-1\",\"config\":{config},\"world\":{{}},\"canon\":{canon},\
             \"carrier\":{{}},\"slot_state\":{{\"slot\":9,\"secret\":\"{secret}\",\"commitment\":\"{commitment}\"}},\
             \"request\":{{\"slot\":9,\"slot_commitment\":\"{commitment}\"}}}}",
            secret = "77".repeat(32),
            commitment = "bc".repeat(32),
        );
        let successor_canon =
            format!("{{\"world\":{{\"sequence\":{sequence}}},\"revision\":{revision}}}");
        let output = format!(
            "{{\"format\":\"POA-SIGNAL-OUT-1\",\"receipt\":{{}},\"successor_world\":{{\"sequence\":{sequence}}},\"successor_canon\":{successor_canon}}}"
        );
        (input.into_bytes(), output.into_bytes())
    }

    fn two_transition_bundle() -> (Vec<u8>, Vec<Vec<u8>>) {
        let authority = [0x11; 32];
        let deployment = [0x22; 32];
        let config = br#"{"target":"fixture"}"#;
        let canon0 = br#"{"world":{"sequence":0},"revision":0}"#;
        let genesis = head_wire(authority, deployment, 0, 0, 0, [0; 32], config, canon0);
        let (input1, output1) = judge_pair(
            std::str::from_utf8(config).unwrap(),
            std::str::from_utf8(canon0).unwrap(),
            1,
            1,
        );
        let canon1 = br#"{"world":{"sequence":1},"revision":1}"#.to_vec();
        let transition1 = transition_wire(genesis.clone(), 1, 10, input1, output1, canon1.clone());
        let head1 = decode_transition(transition1.clone())
            .unwrap()
            .successor
            .wire;
        let (input2, output2) = judge_pair(
            std::str::from_utf8(config).unwrap(),
            std::str::from_utf8(&canon1).unwrap(),
            2,
            2,
        );
        let canon2 = br#"{"world":{"sequence":2},"revision":2}"#.to_vec();
        let transition2 = transition_wire(head1, 2, 12, input2, output2, canon2);
        (genesis, vec![transition1, transition2])
    }

    fn bundle_bytes(genesis: &[u8], transitions: &[Vec<u8>]) -> Vec<u8> {
        let genesis = decode_head(genesis.to_vec()).unwrap();
        let final_head = transitions
            .last()
            .map(|wire| decode_transition(wire.clone()).unwrap().successor)
            .unwrap_or_else(|| genesis.clone());
        serde_json::to_vec(&ExactReplayBundleV1 {
            format: EXACT_REPLAY_BUNDLE_FORMAT_V1.into(),
            authority_id: hex32(genesis.authority_id),
            deployment_digest: hex32(genesis.deployment_digest),
            genesis_head_wire_hex: bytes_hex(&genesis.wire),
            transition_wires_hex: transitions.iter().map(|wire| bytes_hex(wire)).collect(),
            expected_head_digest: hex32(final_head.digest()),
        })
        .unwrap()
    }

    fn fake_replay(bytes: &[u8]) -> Result<ReplayReportV1, ReplayError> {
        replay_exact_bundle_with(bytes, |input| {
            let input: JudgeInputEnvelope = serde_json::from_str(input).unwrap();
            let canon: serde_json::Value = serde_json::from_str(input.canon.get()).unwrap();
            let revision = json_u64(&canon, "revision").unwrap() + 1;
            let sequence = json_u64(canon.get("world").unwrap(), "sequence").unwrap() + 1;
            let (_, output) = judge_pair(input.config.get(), input.canon.get(), sequence, revision);
            Ok(Some(String::from_utf8(output).unwrap()))
        })
    }

    fn bytes_hex(bytes: &[u8]) -> String {
        let mut output = String::with_capacity(bytes.len() * 2);
        for &byte in bytes {
            output.push(char::from(b"0123456789abcdef"[(byte >> 4) as usize]));
            output.push(char::from(b"0123456789abcdef"[(byte & 0xf) as usize]));
        }
        output
    }

    #[test]
    fn exact_bundle_replays_to_deterministic_head() {
        let (genesis, transitions) = two_transition_bundle();
        let report = fake_replay(&bundle_bytes(&genesis, &transitions)).unwrap();
        assert_eq!(report.status, "semantic_review_only");
        assert_eq!(
            report.authority_status,
            "unverified_no_signed_turn_or_commit_evidence"
        );
        assert_eq!(report.semantic_transitions_replayed, 2);
        assert_eq!(report.first_claimed_commit_ordinal, Some(10));
        assert_eq!(report.last_claimed_commit_ordinal, Some(12));
        assert_eq!(report.world_sequence, 2);
        assert_eq!(report.canon_revision, 2);
    }

    fn signal_bundle(judge_input: &[u8], judge_output: &[u8]) -> Vec<u8> {
        let input: JudgeInputEnvelope = serde_json::from_slice(judge_input).unwrap();
        let output: JudgeOutputEnvelope = serde_json::from_slice(judge_output).unwrap();
        let canon: serde_json::Value = serde_json::from_str(input.canon.get()).unwrap();
        let authority = [0x51; 32];
        let deployment = [0x61; 32];
        let genesis = head_wire(
            authority,
            deployment,
            0,
            json_u64(canon.get("world").unwrap(), "sequence").unwrap(),
            json_u64(&canon, "revision").unwrap(),
            [0; 32],
            input.config.get().as_bytes(),
            input.canon.get().as_bytes(),
        );
        let transition = transition_wire(
            genesis.clone(),
            1,
            7,
            judge_input.to_vec(),
            judge_output.to_vec(),
            output.successor_canon.get().as_bytes().to_vec(),
        );
        bundle_bytes(&genesis, &[transition])
    }

    fn checked_in_signal_bundle() -> (Vec<u8>, String) {
        let judge_input =
            include_bytes!("../../dregg-lean-ffi/tests/fixtures/poa-signal-input-v1.json")
                .strip_suffix(b"\n")
                .expect("committed Signal fixture has one file newline");
        let judge_output =
            include_bytes!("../../dregg-lean-ffi/tests/fixtures/poa-signal-output-v1.json")
                .strip_suffix(b"\n")
                .expect("committed Signal fixture has one file newline");
        (
            signal_bundle(judge_input, judge_output),
            String::from_utf8(judge_output.to_vec()).unwrap(),
        )
    }

    /// ⚠ THE SECRET MUST NOT REACH THE REVIEW SURFACE.
    ///
    /// `slot_state` on the judge wire carries the curator's per-slot SECRET. A
    /// review report needs to establish that the served instance matched the
    /// PUBLISHED commitment, and slot + commitment say that; the secret adds
    /// nothing a reviewer can check that the commitment does not, and it would turn
    /// every archived review artifact into key material at rest.
    ///
    /// So `SlotStateEnvelope` deserializes `secret` into `serde::de::IgnoredAny`.
    /// This test pins BOTH halves against the real committed fixture, and needs no
    /// Lean archive, so it gates the change on any machine:
    ///
    /// * the envelope still ACCEPTS the full wire shape (the field is required and
    ///   `deny_unknown_fields` still applies — dropping a value is not the same as
    ///   not checking the shape), and
    /// * slot and commitment survive, so the reviewable binding is intact.
    ///
    /// The structural half is enforced by the compiler rather than here: there is no
    /// field holding the secret, so no formatter can reach it, and `IgnoredAny` has
    /// no `Serialize` impl, so this struct cannot be made to print one.
    #[test]
    fn the_review_envelope_takes_the_slot_state_and_drops_the_secret() {
        let judge_input =
            include_bytes!("../../dregg-lean-ffi/tests/fixtures/poa-signal-input-v1.json")
                .strip_suffix(b"\n")
                .expect("committed Signal fixture has one file newline");
        let input: JudgeInputEnvelope = serde_json::from_slice(judge_input)
            .expect("the review envelope must accept the real POA-SIGNAL-IN-1 wire");

        assert_eq!(input.slot_state.slot, 9);
        assert_eq!(
            input.slot_state.commitment,
            "bc7742888f4ed90ace371abf4b0be7dec5e22d47723bcfd01903a8aa2332a491"
        );

        // The fixture's secret, which must appear nowhere the envelope can reach.
        let secret = "77".repeat(32);
        assert!(
            String::from_utf8_lossy(judge_input).contains(&secret),
            "fixture no longer carries the secret this test is about; fix the test"
        );
        // `slot_state` is a typed value now, so the only strings it holds are these.
        assert_ne!(input.slot_state.commitment, secret);

        // A wire MISSING the secret is still refused: the shape is checked even
        // though the value is discarded.
        let without_secret =
            String::from_utf8_lossy(judge_input).replace(&format!(r#""secret":"{secret}","#), "");
        assert!(
            serde_json::from_str::<JudgeInputEnvelope>(&without_secret).is_err(),
            "the envelope accepted a slot_state with no secret; the shape is not being checked"
        );
    }

    #[test]
    fn checked_in_signal_fixture_replays_through_native_lean() {
        let (bundle, _) = checked_in_signal_bundle();
        let report = replay_exact_bundle_bytes(&bundle).unwrap();
        assert_eq!(report.status, "semantic_review_only");
        assert_eq!(report.native_lean_transitions_replayed, 1);
        assert_eq!(report.transition_count, 1);
    }

    #[test]
    fn self_consistent_fixture_projects_semantic_review_without_finality() {
        let (bundle, judge_output) = checked_in_signal_bundle();
        let history =
            verify_exact_bundle_with(&bundle, |_| Ok(Some(judge_output.clone()))).unwrap();
        let review = project_semantic_history(history).unwrap();
        assert_eq!(review.status, "semantic_review_only");
        assert_eq!(
            review.authority_status,
            "unverified_no_signed_turn_or_commit_evidence"
        );
        assert_eq!(review.events.len(), 1);
        assert_eq!(review.events[0].mission_id, 1);
        assert_eq!(review.events[0].claimed_commit_ordinal, 7);
        assert_eq!(review.events[0].beta_artifacts_added.len(), 1);
        assert_eq!(review.beta_artifacts_observed.len(), 1);
        assert_eq!(
            review.beta_artifacts_observed[0].authorization_status,
            "unavailable_missing_finality_authority_evidence"
        );
        let rendered = serde_json::to_string(&review.beta_artifacts_observed[0]).unwrap();
        assert!(!rendered.contains("signature"));
        assert!(!rendered.contains("promotion"));
        assert!(!rendered.contains("finalized"));
        assert!(!rendered.contains("provenance"));
        assert!(!rendered.contains("\"action\""));
    }

    #[test]
    fn hostile_self_consistent_forged_carrier_is_never_reported_as_finality() {
        let original_input = std::str::from_utf8(
            include_bytes!("../../dregg-lean-ffi/tests/fixtures/poa-signal-input-v1.json")
                .strip_suffix(b"\n")
                .expect("committed Signal fixture has one file newline"),
        )
        .unwrap();
        let original_actor_root = "44".repeat(32);
        let forged_actor_root = "ab".repeat(32);
        let forged_input = original_input.replace(&original_actor_root, &forged_actor_root);
        assert_eq!(forged_input.matches(&forged_actor_root).count(), 2);

        // The Lean judge authenticates game semantics, not the origin of this
        // carrier. A hostile caller can therefore make a self-consistent actor
        // claim which Lean accepts and faithfully copies into the receipt.
        let forged_output = native_judge(&forged_input)
            .expect("native Lean judge is linked")
            .expect("self-consistent forged carrier remains semantically valid");
        assert!(forged_output.contains(&forged_actor_root));

        let bundle = signal_bundle(forged_input.as_bytes(), forged_output.as_bytes());
        let history = verify_exact_bundle_with(&bundle, |actual| {
            assert_eq!(actual, forged_input);
            Ok(Some(forged_output.clone()))
        })
        .unwrap();
        let review = project_semantic_history(history).unwrap();
        assert_eq!(review.status, "semantic_review_only");
        assert_eq!(
            review.authority_status,
            "unverified_no_signed_turn_or_commit_evidence"
        );
        assert_eq!(review.events[0].claimed_actor_root, forged_actor_root);
        assert_eq!(
            review.beta_artifacts_observed[0].authorization_status,
            "unavailable_missing_finality_authority_evidence"
        );
    }

    #[test]
    fn corruption_is_refused_before_semantic_replay() {
        let (genesis, mut transitions) = two_transition_bundle();
        let last = transitions[0].len() - 1;
        transitions[0][last] ^= 1;
        let error = fake_replay(&bundle_bytes_with_expected_from_second(
            &genesis,
            &transitions,
        ))
        .unwrap_err();
        assert!(error.to_string().contains("seal mismatch"));
    }

    #[test]
    fn a_transition_gap_is_refused() {
        let (genesis, transitions) = two_transition_bundle();
        let error = fake_replay(&bundle_bytes(
            &genesis,
            std::slice::from_ref(&transitions[1]),
        ))
        .unwrap_err();
        assert!(error.to_string().contains("gap or reorder"));
    }

    #[test]
    fn reordered_transitions_are_refused() {
        let (genesis, mut transitions) = two_transition_bundle();
        transitions.swap(0, 1);
        let error = fake_replay(&bundle_bytes_with_expected_from_second(
            &genesis,
            &transitions,
        ))
        .unwrap_err();
        assert!(error.to_string().contains("gap or reorder"));
    }

    fn bundle_bytes_with_expected_from_second(genesis: &[u8], transitions: &[Vec<u8>]) -> Vec<u8> {
        let genesis_head = decode_head(genesis.to_vec()).unwrap();
        let expected = transitions
            .iter()
            .find_map(|wire| decode_transition(wire.clone()).ok())
            .map_or_else(
                || genesis_head.digest(),
                |transition| transition.successor.digest(),
            );
        serde_json::to_vec(&ExactReplayBundleV1 {
            format: EXACT_REPLAY_BUNDLE_FORMAT_V1.into(),
            authority_id: hex32(genesis_head.authority_id),
            deployment_digest: hex32(genesis_head.deployment_digest),
            genesis_head_wire_hex: bytes_hex(genesis),
            transition_wires_hex: transitions.iter().map(|wire| bytes_hex(wire)).collect(),
            expected_head_digest: hex32(expected),
        })
        .unwrap()
    }
}
