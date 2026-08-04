//! Read-only replay of exact durable Path of Angels Signal wires.
//!
//! The bundle deliberately carries the sealed bytes written by `dregg-persist`,
//! not a lossy public API projection. Rust checks the storage envelope and exact
//! byte bindings; every game transition is rerun by Lean's sole Signal judge.
//! There is no Rust game-semantic fallback.

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

/// Machine-readable success report. Any mismatch is an error and produces no
/// success report, so `status = "verified"` has one unambiguous meaning.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ReplayReportV1 {
    pub format: &'static str,
    pub status: &'static str,
    pub authority_id: String,
    pub deployment_digest: String,
    pub transitions_verified: u64,
    pub lean_transitions_verified: u64,
    pub first_commit_ordinal: Option<u64>,
    pub last_commit_ordinal: Option<u64>,
    pub head_digest: String,
    pub transition_count: u64,
    pub world_sequence: u64,
    pub canon_revision: u64,
    pub last_transition_digest: String,
    pub config_sha256: String,
    pub canon_sha256: String,
    pub exact_wire_bytes_replayed: u64,
    pub semantic_authority: &'static str,
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

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct JudgeInputEnvelope {
    format: String,
    config: Box<RawValue>,
    world: Box<RawValue>,
    canon: Box<RawValue>,
    carrier: Box<RawValue>,
    request: Box<RawValue>,
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
    let path = path.as_ref();
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
    replay_exact_bundle_bytes(&bytes)
}

/// Replay one serialized bundle through the linked native Lean authority.
pub fn replay_exact_bundle_bytes(bytes: &[u8]) -> Result<ReplayReportV1, ReplayError> {
    replay_exact_bundle_with(
        bytes,
        |input| match dregg_lean_ffi::poa_ffi::judge_poa_signal(input) {
            Ok(dregg_lean_ffi::poa_ffi::PoaSignalVerdict::Accepted(output)) => Ok(Some(output)),
            Ok(dregg_lean_ffi::poa_ffi::PoaSignalVerdict::Rejected) => Ok(None),
            Err(reason) => Err(reason),
        },
    )
}

fn replay_exact_bundle_with<F>(bytes: &[u8], mut judge: F) -> Result<ReplayReportV1, ReplayError>
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
        current = transition.successor;
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

    Ok(ReplayReportV1 {
        format: REPLAY_REPORT_FORMAT_V1,
        status: "verified",
        authority_id: hex32(authority_id),
        deployment_digest: hex32(deployment_digest),
        transitions_verified: current.transition_count,
        lean_transitions_verified: current.transition_count,
        first_commit_ordinal,
        last_commit_ordinal: previous_commit_ordinal,
        head_digest: hex32(current.digest()),
        transition_count: current.transition_count,
        world_sequence: current.world_sequence,
        canon_revision: current.canon_revision,
        last_transition_digest: hex32(current.last_transition_digest),
        config_sha256: hex32(sha256(&current.config)),
        canon_sha256: hex32(sha256(&current.canon)),
        exact_wire_bytes_replayed: exact_wire_bytes,
        semantic_authority: "Dregg2.Games.PathOfAngels.NetworkJudge.signalJudgeFFI",
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
        let input = format!(
            "{{\"format\":\"POA-SIGNAL-IN-1\",\"config\":{config},\"world\":{{}},\"canon\":{canon},\"carrier\":{{}},\"request\":{{}}}}"
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
        assert_eq!(report.status, "verified");
        assert_eq!(report.transitions_verified, 2);
        assert_eq!(report.first_commit_ordinal, Some(10));
        assert_eq!(report.last_commit_ordinal, Some(12));
        assert_eq!(report.world_sequence, 2);
        assert_eq!(report.canon_revision, 2);
    }

    #[test]
    fn checked_in_signal_fixture_replays_through_native_lean() {
        let judge_input_file =
            include_bytes!("../../dregg-lean-ffi/tests/fixtures/poa-signal-input-v1.json");
        let judge_output_file =
            include_bytes!("../../dregg-lean-ffi/tests/fixtures/poa-signal-output-v1.json");
        let judge_input = judge_input_file
            .strip_suffix(b"\n")
            .expect("committed Signal fixture has one file newline");
        let judge_output = judge_output_file
            .strip_suffix(b"\n")
            .expect("committed Signal fixture has one file newline");
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
        let report = replay_exact_bundle_bytes(&bundle_bytes(&genesis, &[transition])).unwrap();
        assert_eq!(report.status, "verified");
        assert_eq!(report.lean_transitions_verified, 1);
        assert_eq!(report.transition_count, 1);
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
