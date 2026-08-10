//! Portable, fail-closed verification of one rostered node's durable view of a
//! Path of Angels Signal transition.
//!
//! The node exports public replay material only: exact `SignedTurn`, exact
//! executor receipt, exact Lean wires, and a projection plus digest of the
//! durable commit record. Private cell snapshots and capability witnesses never
//! cross this boundary.
//!
//! This format deliberately carries no carrying-block quorum certificate,
//! threshold/hybrid federation attestation, externally anchored deployment
//! manifest pin, or proof that the self-carried ML-DSA key was enrolled in the
//! actor cell. Verification therefore proves only consistency of exact bytes
//! with one roster-selected node's attestation and durable view. It is not
//! independently verifiable federation finality or permission to promote beta
//! material to canon.

use std::path::Path;

use base64::Engine as _;
use base64::engine::general_purpose::STANDARD as BASE64;
use dregg_sdk::SignedTurn;
use dregg_turn::{Finality, TurnReceipt};
use dregg_types::{PublicKey, Signature, SigningKey};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use sha2::{Digest as _, Sha256};
use thiserror::Error;

use crate::{
    PoaDeploymentScope, hex_encode, parse_hex_array, parse_strict_json, read_regular_bounded,
};

pub const POA_SIGNAL_AUTHORITY_EXPORT_FORMAT_V1: &str = "POA-SIGNAL-NODE-ENVELOPE-V1";
pub const POA_SIGNAL_AUTHORITY_EXPORT_SCHEMA_VERSION_V1: u64 = 1;
const SIGNING_DOMAIN: &[u8] = b"pathofangels.network/signal-node-envelope/v1\0";
const MAX_EXACT_COMPONENT_BYTES: usize = 16 * 1024 * 1024;
const MAX_AUTHORITY_EXPORT_BYTES: u64 = 64 * 1024 * 1024;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PublicCommitProjectionV1 {
    pub ordinal: u64,
    pub height: u64,
    pub block_id: String,
    pub block_executed_up_to: u64,
    pub turn_hash: String,
    pub creator: String,
    pub receipt_hash: String,
    pub ledger_root: String,
    /// SHA-256 over the exact redb value. The node signature authenticates it;
    /// the value itself stays private because it contains cell snapshots.
    pub exact_record_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PoaSignalAuthorityExportV1 {
    pub format: String,
    pub schema_version: u64,
    pub authority_id: String,
    pub deployment_digest: String,
    pub federation_id: String,
    pub sequence: u64,
    pub mission_id: u64,
    pub content_root: String,
    pub activation_digest: String,
    pub content_session: String,
    pub content_epoch: u64,
    pub player_key: String,
    pub actor_root: String,
    pub transition_digest: String,
    pub predecessor_head_digest: String,
    pub successor_head_digest: String,
    pub judge_input_sha256: String,
    pub judge_output_sha256: String,
    pub judge_input_base64: String,
    pub judge_output_base64: String,
    pub commit: PublicCommitProjectionV1,
    pub signed_turn_sha256: String,
    pub signed_turn_postcard_base64: String,
    pub signer: String,
    pub receipt_bytes_sha256: String,
    pub receipt_postcard_base64: String,
    pub executor_public_key: String,
    pub export_signature: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct VerifiedAuthorityExportV1 {
    pub authority_id: String,
    pub deployment_digest: String,
    pub sequence: u64,
    pub mission_id: u64,
    pub content_root: String,
    pub activation_digest: String,
    pub content_session: String,
    pub content_epoch: u64,
    pub player_key: String,
    pub actor_root: String,
    pub transition_digest: String,
    pub commit_ordinal: u64,
    pub block_id: String,
    pub turn_hash: String,
    pub receipt_hash: String,
    pub executor_public_key: String,
    /// The verifier uses the roster supplied by its caller. V1 does not know
    /// whether the exact deployment manifest digest was pinned out of band.
    deployment_manifest_externally_pinned: bool,
    /// The SignedTurn's self-carried ML-DSA signature was checked, but V1 does
    /// not carry an actor-cell enrollment witness for that key.
    actor_pq_enrollment_verified: bool,
    /// The exact judge configuration was replayed through Lean, but the V1
    /// verifier does not bind all of its mission/config fields to an
    /// independently authenticated catalog descriptor.
    authenticated_mission_config_bound: bool,
    /// This is intentionally false in V1: the format has no portable quorum or
    /// threshold/hybrid certificate for the carrying block.
    federation_finality_verified: bool,
}

impl VerifiedAuthorityExportV1 {
    /// V1 has no externally anchored manifest pin. This getter is deliberately
    /// read-only: callers cannot mint a stronger verification result.
    pub const fn deployment_manifest_externally_pinned(&self) -> bool {
        self.deployment_manifest_externally_pinned
    }

    /// V1 verifies the carried key's signature, not actor-cell enrollment.
    pub const fn actor_pq_enrollment_verified(&self) -> bool {
        self.actor_pq_enrollment_verified
    }

    /// V1 does not bind every judged config field to authenticated catalog
    /// mission bytes.
    pub const fn authenticated_mission_config_bound(&self) -> bool {
        self.authenticated_mission_config_bound
    }

    /// V1 carries no independently verifiable federation-finality certificate.
    pub const fn federation_finality_verified(&self) -> bool {
        self.federation_finality_verified
    }
}

#[derive(Debug, Error)]
pub enum AuthorityExportError {
    #[error("node envelope I/O refused: {0}")]
    Io(String),
    #[error("node envelope JSON refused: {0}")]
    Json(String),
    #[error("node envelope schema refused: {0}")]
    Schema(String),
    #[error("node envelope cryptography refused: {0}")]
    Crypto(String),
    #[error("node envelope binding refused: {0}")]
    Binding(String),
    #[error("node envelope Lean replay refused: {0}")]
    Lean(String),
}

impl PoaSignalAuthorityExportV1 {
    pub fn seal(&mut self, key: &SigningKey) -> Result<(), AuthorityExportError> {
        if self.executor_public_key != key.public_key().hex() {
            return Err(AuthorityExportError::Crypto(
                "sealing key differs from executor_public_key".into(),
            ));
        }
        self.export_signature.clear();
        let signature = dregg_types::sign(key, &self.signing_message()?);
        self.export_signature = hex_encode(&signature.0);
        Ok(())
    }

    fn signing_message(&self) -> Result<Vec<u8>, AuthorityExportError> {
        let mut out = Vec::with_capacity(4096);
        out.extend_from_slice(SIGNING_DOMAIN);
        frame(&mut out, self.format.as_bytes());
        scalar(&mut out, self.schema_version);
        for value in [
            &self.authority_id,
            &self.deployment_digest,
            &self.federation_id,
        ] {
            frame(&mut out, value.as_bytes());
        }
        scalar(&mut out, self.sequence);
        scalar(&mut out, self.mission_id);
        for value in [
            &self.content_root,
            &self.activation_digest,
            &self.content_session,
        ] {
            frame(&mut out, value.as_bytes());
        }
        scalar(&mut out, self.content_epoch);
        for value in [
            &self.player_key,
            &self.actor_root,
            &self.transition_digest,
            &self.predecessor_head_digest,
            &self.successor_head_digest,
            &self.judge_input_sha256,
            &self.judge_output_sha256,
        ] {
            frame(&mut out, value.as_bytes());
        }
        frame(
            &mut out,
            &decode_component(&self.judge_input_base64, "judge input")?,
        );
        frame(
            &mut out,
            &decode_component(&self.judge_output_base64, "judge output")?,
        );
        scalar(&mut out, self.commit.ordinal);
        scalar(&mut out, self.commit.height);
        frame(&mut out, self.commit.block_id.as_bytes());
        scalar(&mut out, self.commit.block_executed_up_to);
        for value in [
            &self.commit.turn_hash,
            &self.commit.creator,
            &self.commit.receipt_hash,
            &self.commit.ledger_root,
            &self.commit.exact_record_sha256,
            &self.signed_turn_sha256,
        ] {
            frame(&mut out, value.as_bytes());
        }
        frame(
            &mut out,
            &decode_component(&self.signed_turn_postcard_base64, "SignedTurn")?,
        );
        frame(&mut out, self.signer.as_bytes());
        frame(&mut out, self.receipt_bytes_sha256.as_bytes());
        frame(
            &mut out,
            &decode_component(&self.receipt_postcard_base64, "receipt")?,
        );
        frame(&mut out, self.executor_public_key.as_bytes());
        Ok(out)
    }
}

pub fn load_authority_export_file(
    path: impl AsRef<Path>,
) -> Result<PoaSignalAuthorityExportV1, AuthorityExportError> {
    let bytes = read_regular_bounded(path.as_ref(), MAX_AUTHORITY_EXPORT_BYTES)
        .map_err(|error| AuthorityExportError::Io(error.to_string()))?;
    let value = parse_strict_json(&bytes).map_err(AuthorityExportError::Json)?;
    serde_json::from_value(value).map_err(|error| AuthorityExportError::Json(error.to_string()))
}

pub fn verify_authority_export_file(
    path: impl AsRef<Path>,
    deployment: &PoaDeploymentScope,
) -> Result<VerifiedAuthorityExportV1, AuthorityExportError> {
    let export = load_authority_export_file(path)?;
    verify_authority_export(&export, deployment)
}

/// Verify exact bytes, signatures, Lean replay, deployment membership and the
/// attesting node's durable commit projection.
///
/// Success is **not** a provenance, identity-enrollment, mission-activation, or
/// federation-finality result. The returned limitation flags are false by
/// construction. A caller must not turn success here into promotion authority.
pub fn verify_authority_export(
    export: &PoaSignalAuthorityExportV1,
    deployment: &PoaDeploymentScope,
) -> Result<VerifiedAuthorityExportV1, AuthorityExportError> {
    if export.format != POA_SIGNAL_AUTHORITY_EXPORT_FORMAT_V1
        || export.schema_version != POA_SIGNAL_AUTHORITY_EXPORT_SCHEMA_VERSION_V1
        || export.sequence == 0
    {
        return Err(AuthorityExportError::Schema(
            "unknown format/schema or zero transition sequence".into(),
        ));
    }
    for (field, value) in [
        ("authority_id", &export.authority_id),
        ("deployment_digest", &export.deployment_digest),
        ("federation_id", &export.federation_id),
        ("content_root", &export.content_root),
        ("activation_digest", &export.activation_digest),
        ("content_session", &export.content_session),
        ("player_key", &export.player_key),
        ("actor_root", &export.actor_root),
        ("transition_digest", &export.transition_digest),
        ("predecessor_head_digest", &export.predecessor_head_digest),
        ("successor_head_digest", &export.successor_head_digest),
        ("judge_input_sha256", &export.judge_input_sha256),
        ("judge_output_sha256", &export.judge_output_sha256),
        ("commit.block_id", &export.commit.block_id),
        ("commit.turn_hash", &export.commit.turn_hash),
        ("commit.creator", &export.commit.creator),
        ("commit.receipt_hash", &export.commit.receipt_hash),
        ("commit.ledger_root", &export.commit.ledger_root),
        (
            "commit.exact_record_sha256",
            &export.commit.exact_record_sha256,
        ),
        ("signed_turn_sha256", &export.signed_turn_sha256),
        ("signer", &export.signer),
        ("receipt_bytes_sha256", &export.receipt_bytes_sha256),
        ("executor_public_key", &export.executor_public_key),
    ] {
        parse_hex32(value, field)?;
    }
    if export.authority_id != export.federation_id
        || export.federation_id != deployment.federation_id()
        || export.deployment_digest != deployment.deployment_digest()
    {
        return Err(AuthorityExportError::Binding(
            "authority/deployment binding differs from the signed deployment".into(),
        ));
    }

    let executor = parse_hex32(&export.executor_public_key, "executor_public_key")?;
    if !deployment.validator_public_keys().contains(&executor) {
        return Err(AuthorityExportError::Crypto(
            "export signer is not in the deployment validator roster".into(),
        ));
    }
    let export_signature = parse_hex_array::<64>(&export.export_signature, "export_signature")
        .map_err(|error| AuthorityExportError::Schema(error.to_string()))?;
    if !PublicKey(executor).verify(&export.signing_message()?, &Signature(export_signature)) {
        return Err(AuthorityExportError::Crypto(
            "node-envelope signature is invalid".into(),
        ));
    }

    let signed_bytes = decode_component(&export.signed_turn_postcard_base64, "SignedTurn")?;
    require_sha256(&signed_bytes, &export.signed_turn_sha256, "SignedTurn")?;
    let (signed, remainder): (SignedTurn, &[u8]) = postcard::take_from_bytes(&signed_bytes)
        .map_err(|error| AuthorityExportError::Schema(format!("SignedTurn: {error}")))?;
    if !remainder.is_empty()
        || postcard::to_stdvec(&signed).ok().as_deref() != Some(signed_bytes.as_slice())
    {
        return Err(AuthorityExportError::Schema(
            "SignedTurn is not one exact canonical postcard value".into(),
        ));
    }
    let turn_hash = signed.turn.hash();
    if !signed.signer.verify(&turn_hash, &signed.signature)
        || signed.signer.hex() != export.signer
        || signed.signer.hex() != export.player_key
        || signed.turn.agent != dregg_sdk::poa_signal::signal_player_cell(&signed.signer.0)
    {
        return Err(AuthorityExportError::Crypto(
            "SignedTurn signer, agent, player, or Ed25519 signature disagrees".into(),
        ));
    }
    if signed.pq_signer.is_empty() || signed.pq_signature.is_empty() {
        return Err(AuthorityExportError::Crypto(
            "PoA carrier lacks the required ML-DSA half".into(),
        ));
    }
    if matches!(
        dregg_sdk::install_verified_mldsa_verify_core(),
        dregg_pq::MlDsaVerifyCoreInstall::ExportAbsent
    ) {
        return Err(AuthorityExportError::Crypto(
            "Lean-verified full-byte ML-DSA verifier export is absent".into(),
        ));
    }
    if !dregg_turn::pq::ml_dsa_verify(&signed.pq_signer, &turn_hash, &signed.pq_signature) {
        return Err(AuthorityExportError::Crypto(
            "SignedTurn ML-DSA signature is invalid".into(),
        ));
    }
    let claim = dregg_sdk::poa_signal::claim_from_exact_signal_turn(&signed.turn)
        .map_err(|error| AuthorityExportError::Schema(error.to_string()))?;

    let receipt_bytes = decode_component(&export.receipt_postcard_base64, "receipt")?;
    require_sha256(
        &receipt_bytes,
        &export.receipt_bytes_sha256,
        "receipt bytes",
    )?;
    let (receipt, remainder): (TurnReceipt, &[u8]) = postcard::take_from_bytes(&receipt_bytes)
        .map_err(|error| AuthorityExportError::Schema(format!("receipt: {error}")))?;
    if !remainder.is_empty()
        || postcard::to_stdvec(&receipt).ok().as_deref() != Some(receipt_bytes.as_slice())
    {
        return Err(AuthorityExportError::Schema(
            "receipt is not one exact canonical postcard value".into(),
        ));
    }
    if receipt.finality != Finality::Final
        || receipt.turn_hash != turn_hash
        || receipt.forest_hash != signed.turn.call_forest.compute_hash()
        || receipt.action_count != signed.turn.call_forest.action_count()
        || receipt.agent != signed.turn.agent
        || receipt.federation_id != parse_hex32(&export.federation_id, "federation_id")?
        || receipt.pre_state_hash != parse_hex32(&export.actor_root, "actor_root")?
        || receipt.routing_directives.len() != 0
        || receipt.introduction_exports.len() != 0
        || receipt.derivation_records.len() != 0
        || receipt.consumed_capabilities.len() != 0
        || receipt.was_encrypted
        || receipt.was_burn
    {
        return Err(AuthorityExportError::Binding(
            "receipt is not the public exact Signal receipt with a Final executor marker".into(),
        ));
    }
    dregg_turn::verify_receipt_signature_with_keys(&receipt, &[executor])
        .map_err(|error| AuthorityExportError::Crypto(error.to_string()))?;

    let receipt_hash = receipt.receipt_hash();
    if export.commit.turn_hash != hex_encode(&turn_hash)
        || export.commit.receipt_hash != hex_encode(&receipt_hash)
        || export.commit.creator != hex_encode(signed.turn.agent.as_bytes())
    {
        return Err(AuthorityExportError::Binding(
            "durable commit projection disagrees with exact turn/receipt".into(),
        ));
    }

    let judge_input = decode_component(&export.judge_input_base64, "judge input")?;
    let judge_output = decode_component(&export.judge_output_base64, "judge output")?;
    require_sha256(&judge_input, &export.judge_input_sha256, "judge input")?;
    require_sha256(&judge_output, &export.judge_output_sha256, "judge output")?;
    let input_text = std::str::from_utf8(&judge_input)
        .map_err(|_| AuthorityExportError::Schema("judge input is not UTF-8".into()))?;
    let output_text = std::str::from_utf8(&judge_output)
        .map_err(|_| AuthorityExportError::Schema("judge output is not UTF-8".into()))?;
    let replayed = dregg_lean_ffi::poa_ffi::judge_poa_signal(input_text)
        .map_err(AuthorityExportError::Lean)?;
    match replayed {
        dregg_lean_ffi::poa_ffi::PoaSignalVerdict::Accepted(bytes)
            if bytes.as_str().as_bytes() == judge_output => {}
        dregg_lean_ffi::poa_ffi::PoaSignalVerdict::Accepted(_) => {
            return Err(AuthorityExportError::Lean(
                "native Lean output differs from the exported exact output".into(),
            ));
        }
        dregg_lean_ffi::poa_ffi::PoaSignalVerdict::Rejected => {
            return Err(AuthorityExportError::Lean(
                "native Lean rejected the exported exact input".into(),
            ));
        }
    }
    let input = parse_strict_json(input_text.as_bytes()).map_err(AuthorityExportError::Json)?;
    let output = parse_strict_json(output_text.as_bytes()).map_err(AuthorityExportError::Json)?;
    verify_judge_bindings(export, &input, &output, claim)?;

    Ok(VerifiedAuthorityExportV1 {
        authority_id: export.authority_id.clone(),
        deployment_digest: export.deployment_digest.clone(),
        sequence: export.sequence,
        mission_id: export.mission_id,
        content_root: export.content_root.clone(),
        activation_digest: export.activation_digest.clone(),
        content_session: export.content_session.clone(),
        content_epoch: export.content_epoch,
        player_key: export.player_key.clone(),
        actor_root: export.actor_root.clone(),
        transition_digest: export.transition_digest.clone(),
        commit_ordinal: export.commit.ordinal,
        block_id: export.commit.block_id.clone(),
        turn_hash: export.commit.turn_hash.clone(),
        receipt_hash: export.commit.receipt_hash.clone(),
        executor_public_key: export.executor_public_key.clone(),
        deployment_manifest_externally_pinned: false,
        actor_pq_enrollment_verified: false,
        authenticated_mission_config_bound: false,
        federation_finality_verified: false,
    })
}

fn verify_judge_bindings(
    export: &PoaSignalAuthorityExportV1,
    input: &Value,
    output: &Value,
    claim: dregg_sdk::poa_signal::SignalClaimV1,
) -> Result<(), AuthorityExportError> {
    if value_str(input, &["format"]) != Some("POA-RUN-IN-1")
        || value_str(output, &["format"]) != Some("POA-RUN-OUT-1")
    {
        return Err(AuthorityExportError::Schema(
            "judge input/output format is unknown".into(),
        ));
    }
    for base in [["request"], ["carrier"]] {
        for (name, expected) in [
            ("federation_id", export.federation_id.as_str()),
            ("content_root", export.content_root.as_str()),
            ("activation_digest", export.activation_digest.as_str()),
            ("content_session", export.content_session.as_str()),
            ("player_key", export.player_key.as_str()),
            ("actor_root", export.actor_root.as_str()),
        ] {
            if value_str(input, &[base[0], name]) != Some(expected) {
                return Err(AuthorityExportError::Binding(format!(
                    "judge {}.{name} differs from node envelope",
                    base[0]
                )));
            }
        }
        if value_u64(input, &[base[0], "content_epoch"]) != Some(export.content_epoch) {
            return Err(AuthorityExportError::Binding(format!(
                "judge {}.content_epoch differs from node envelope",
                base[0]
            )));
        }
    }
    if value_u64(input, &["request", "mission_id"]) != Some(export.mission_id)
        || u64::from(claim.mission_id()) != export.mission_id
    {
        return Err(AuthorityExportError::Binding(
            "exact Signal claim mission differs from judged mission".into(),
        ));
    }
    // The judged transcript is the WHOLE played game, round for round, in order —
    // not the solving code alone. Before 2026-08-07 this required exactly one
    // action, because a claim carried exactly one code; an export whose judge input
    // held five rounds would have been refused as "action is absent", which is the
    // shape of a check that outlives the wire it was written for.
    let transcript = claim.transcript();
    let actions = value_at(input, &["request", "actions"])
        .and_then(Value::as_array)
        .filter(|actions| actions.len() == transcript.len())
        .ok_or_else(|| {
            AuthorityExportError::Binding(
                "judged transcript is absent or is a different length than the exact claim".into(),
            )
        })?;
    for (action, code) in actions.iter().zip(transcript) {
        if action.get("low").and_then(Value::as_u64) != Some(u64::from(code.low()))
            || action.get("mid").and_then(Value::as_u64) != Some(u64::from(code.mid()))
            || action.get("high").and_then(Value::as_u64) != Some(u64::from(code.high()))
        {
            return Err(AuthorityExportError::Binding(
                "exact Signal claim transcript differs from the judged actions".into(),
            ));
        }
    }
    for (name, expected) in [
        ("federation_id", export.federation_id.as_str()),
        ("content_root", export.content_root.as_str()),
        ("activation_digest", export.activation_digest.as_str()),
        ("content_session", export.content_session.as_str()),
        ("player_key", export.player_key.as_str()),
        ("actor_root", export.actor_root.as_str()),
    ] {
        if value_str(output, &["receipt", name]) != Some(expected) {
            return Err(AuthorityExportError::Binding(format!(
                "Lean receipt.{name} differs from node envelope"
            )));
        }
    }
    if value_u64(output, &["receipt", "content_epoch"]) != Some(export.content_epoch)
        || value_u64(output, &["receipt", "mission", "mission_id"]) != Some(export.mission_id)
    {
        return Err(AuthorityExportError::Binding(
            "Lean receipt epoch/mission differs from node envelope".into(),
        ));
    }
    Ok(())
}

fn parse_hex32(value: &str, field: &'static str) -> Result<[u8; 32], AuthorityExportError> {
    parse_hex_array::<32>(value, field)
        .map_err(|error| AuthorityExportError::Schema(error.to_string()))
}

fn decode_component(value: &str, name: &str) -> Result<Vec<u8>, AuthorityExportError> {
    if value.len() > (MAX_EXACT_COMPONENT_BYTES * 4 / 3 + 8) {
        return Err(AuthorityExportError::Schema(format!(
            "{name} exceeds the exact component bound"
        )));
    }
    let bytes = BASE64
        .decode(value)
        .map_err(|_| AuthorityExportError::Schema(format!("{name} is not canonical base64")))?;
    if bytes.len() > MAX_EXACT_COMPONENT_BYTES || BASE64.encode(&bytes) != value {
        return Err(AuthorityExportError::Schema(format!(
            "{name} is not bounded canonical base64"
        )));
    }
    Ok(bytes)
}

fn require_sha256(bytes: &[u8], expected: &str, name: &str) -> Result<(), AuthorityExportError> {
    if hex_encode(&Sha256::digest(bytes)) != expected {
        return Err(AuthorityExportError::Crypto(format!(
            "{name} SHA-256 differs from exact bytes"
        )));
    }
    Ok(())
}

fn value_at<'a>(value: &'a Value, path: &[&str]) -> Option<&'a Value> {
    path.iter().try_fold(value, |value, key| value.get(*key))
}

fn value_str<'a>(value: &'a Value, path: &[&str]) -> Option<&'a str> {
    value_at(value, path).and_then(Value::as_str)
}

fn value_u64(value: &Value, path: &[&str]) -> Option<u64> {
    value_at(value, path).and_then(Value::as_u64)
}

fn frame(out: &mut Vec<u8>, bytes: &[u8]) {
    out.extend_from_slice(&(bytes.len() as u64).to_be_bytes());
    out.extend_from_slice(bytes);
}

fn scalar(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_be_bytes());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn component_codec_refuses_noncanonical_and_oversized_base64() {
        assert_eq!(decode_component("AQ==", "x").unwrap(), vec![1]);
        assert!(decode_component("AQ", "x").is_err());
        assert!(decode_component(&"A".repeat(MAX_EXACT_COMPONENT_BYTES * 2), "x").is_err());
    }

    fn unsigned_fixture(executor_public_key: String) -> PoaSignalAuthorityExportV1 {
        let zero = "00".repeat(32);
        let empty_sha = hex_encode(&Sha256::digest([]));
        PoaSignalAuthorityExportV1 {
            format: POA_SIGNAL_AUTHORITY_EXPORT_FORMAT_V1.into(),
            schema_version: POA_SIGNAL_AUTHORITY_EXPORT_SCHEMA_VERSION_V1,
            authority_id: zero.clone(),
            deployment_digest: zero.clone(),
            federation_id: zero.clone(),
            sequence: 1,
            mission_id: 2,
            content_root: zero.clone(),
            activation_digest: zero.clone(),
            content_session: zero.clone(),
            content_epoch: 3,
            player_key: zero.clone(),
            actor_root: zero.clone(),
            transition_digest: zero.clone(),
            predecessor_head_digest: zero.clone(),
            successor_head_digest: zero.clone(),
            judge_input_sha256: empty_sha.clone(),
            judge_output_sha256: empty_sha.clone(),
            judge_input_base64: String::new(),
            judge_output_base64: String::new(),
            commit: PublicCommitProjectionV1 {
                ordinal: 4,
                height: 5,
                block_id: zero.clone(),
                block_executed_up_to: 6,
                turn_hash: zero.clone(),
                creator: zero.clone(),
                receipt_hash: zero.clone(),
                ledger_root: zero.clone(),
                exact_record_sha256: zero.clone(),
            },
            signed_turn_sha256: empty_sha.clone(),
            signed_turn_postcard_base64: String::new(),
            signer: zero,
            receipt_bytes_sha256: empty_sha,
            receipt_postcard_base64: String::new(),
            executor_public_key,
            export_signature: String::new(),
        }
    }

    #[test]
    fn node_seal_binds_exact_bytes_and_durable_commit_coordinates() {
        let key = SigningKey::from_bytes(&[0x41; 32]);
        let mut export = unsigned_fixture(key.public_key().hex());
        export.seal(&key).unwrap();
        let signature =
            Signature(parse_hex_array::<64>(&export.export_signature, "export_signature").unwrap());
        assert!(
            key.public_key()
                .verify(&export.signing_message().unwrap(), &signature)
        );

        export.commit.ordinal += 1;
        assert!(
            !key.public_key()
                .verify(&export.signing_message().unwrap(), &signature)
        );
        export.commit.ordinal -= 1;
        export.judge_input_base64 = BASE64.encode(b"substituted judge bytes");
        assert!(
            !key.public_key()
                .verify(&export.signing_message().unwrap(), &signature)
        );
    }
}
