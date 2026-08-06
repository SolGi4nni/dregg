//! The operator ceremony that opens one Path of Angels Signal slot.
//!
//! # Why opening a slot is a curator act
//!
//! The live run seed is `HiddenInstance.runSeedFor ⟨secret, slot, playerKey⟩ ctx`.
//! Every validator judging a run derives it independently, so every validator must
//! hold the SAME secret. A secret minted per node — from the node signing key, from
//! local entropy, from anything the node owns — gives each validator a different
//! instance, and the federation then does not merely fail to agree: it agrees on
//! *different answers*, each node believing itself correct. That is strictly worse
//! than having no instance at all, because it settles.
//!
//! So the secret is curator-held, and the node never mints one. Opening a slot
//! requires the curator key. That is correct rather than inconvenient: opening a
//! slot is an editorial act, and the curator already owns content epochs and signs
//! activations.
//!
//! # The ceremony: two node commands with a curator signature between them
//!
//! ```text
//! 0. the curator draws a 32-byte slot secret OFF-LINE          (curator, no node)
//! 1. dregg-node poa-slot-opening-preview …  → commitment + the exact signing message
//! 2. the curator signs that message with the pinned Ed25519 key    (CURATOR KEY)
//!                                                              → slot-opening.json
//! 3. dregg-node init-poa-signal-slot …      → verify, then install
//! ```
//!
//! Step 1 needs no key. Step 2 is the ONLY step that touches the curator key, and
//! it happens off the node — this module, like `poa_galley_genesis`, deliberately
//! never mints a curator signature. Step 3 needs no key either: it verifies one.
//!
//! Step 1 exists so the curator never has to re-implement `HiddenInstance.commit`
//! or the canonical statement encoding: the node computes the commitment with the
//! same Lean export that will verify it, and prints the exact bytes to sign.
//!
//! # Exactly what the curator ceremony must emit
//!
//! One file. The curator never sees the database.
//!
//! ```json
//! {
//!   "schema": "POA-SLOT-OPENING-ENVELOPE-V1",
//!   "statement": {
//!     "schema": "POA-SLOT-OPENING-STATEMENT-1",
//!     "authority_id": "<hex32>", "mission_id": 1,
//!     "slot": 9, "commitment": "<hex32>"
//!   },
//!   "curator_key": "<hex32, equal to the installed pin>",
//!   "signature": "<hex64>"
//! }
//! ```
//!
//! `statement` must be copied verbatim from the preview. The `signature` is Ed25519
//! over **the preview's `signing_message` bytes** — canonical, compact, key-ordered
//! JSON:
//!
//! ```json
//! {"schema":"POA-SLOT-OPENING-STATEMENT-1","authority_id":"…","mission_id":1,"slot":9,"commitment":"…"}
//! ```
//!
//! Signing anything else — the envelope file, a pretty-printed statement, a digest
//! of the statement — produces a signature `install_poa_signal_slot_v1` refuses. The
//! preview's `signing_message_sha256` is there so the two sides can compare one
//! number before the key is touched.
//!
//! # What the node refuses
//!
//! * A signature that does not verify against the installed curator pin.
//! * A secret that does not open the published commitment — checked by CALLING
//!   Lean, inside `install_poa_signal_slot_v1`, where no caller can route around it.
//! * A slot that does not strictly advance the authority's open slot.
//! * Substitution of the secret, commitment or key of an already-installed slot. An
//!   identical retry succeeds; ceremonies get re-run.
//!
//! # ⚠ Publish the commitment before the slot opens
//!
//! Installing the secret is not publication. The signed opening must reach players
//! BEFORE they play, or the commitment binds nothing: a commitment revealed
//! afterwards is compatible with any instance the operator likes. The bundle cannot
//! carry it — the bundle is signed once per content epoch and slots open afterwards
//! — which is exactly why the slot opening is separately signed.

use std::fs;
use std::path::{Path, PathBuf};

use dregg_persist::{
    PersistentStore, PoaSlotInstallStatusV1, PoaSlotOpeningStatementV1,
    SignedPoaSlotOpeningEnvelopeV1,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};

/// Schema of the preview document this module emits for the curator to sign.
pub const PREVIEW_SCHEMA: &str = "POA-SLOT-OPENING-PREVIEW-V1";
/// Schema of the signed envelope document the curator ceremony must emit.
pub const ENVELOPE_SCHEMA: &str = "POA-SLOT-OPENING-ENVELOPE-V1";

/// Inputs shared by the preview and the install.
#[derive(Clone, Debug)]
pub struct PoaSlotOpeningArgs {
    pub data_dir: PathBuf,
    /// Federation id of the Signal authority this slot belongs to.
    pub authority_id: String,
    pub mission_id: u64,
    /// The beacon slot being opened. Must strictly advance the open slot.
    pub slot: u64,
    /// File holding the curator's 32-byte slot secret as 64 lowercase hex.
    ///
    /// ⚠ Key material. It is read, used, and never echoed: no preview field, no
    /// report field, no log line renders it.
    pub secret_file: PathBuf,
}

/// What the preview tells the curator.
#[derive(Clone, Debug, Serialize, Deserialize)]
struct PreviewDocument {
    schema: String,
    statement: StatementDocument,
    signing_message: String,
    signing_message_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct StatementDocument {
    schema: String,
    authority_id: String,
    mission_id: u64,
    slot: u64,
    commitment: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct EnvelopeDocument {
    schema: String,
    statement: StatementDocument,
    curator_key: String,
    signature: String,
}

/// Report returned by a successful install.
#[derive(Clone, Debug)]
pub struct PoaSlotOpeningReport {
    pub status: PoaSlotInstallStatusV1,
    pub slot: u64,
    pub mission_id: u64,
    pub commitment: String,
}

/// Step 1: compute the commitment and print the exact bytes the curator signs.
///
/// Needs the secret and the node's Lean archive. Needs NO curator key, touches no
/// database, and writes nothing durable.
pub fn preview_poa_slot_opening(args: &PoaSlotOpeningArgs) -> Result<String, String> {
    let authority_id = parse_hex32(&args.authority_id, "authority_id")?;
    let secret = read_secret(&args.secret_file)?;
    let commitment = derive_commitment(secret, args.slot)?;

    let statement =
        PoaSlotOpeningStatementV1::new(authority_id, args.mission_id, args.slot, commitment);
    let signing_message = statement
        .signing_message()
        .map_err(|error| format!("cannot build the slot-opening signing message: {error}"))?;
    let signing_message = String::from_utf8(signing_message)
        .map_err(|_| "PoA slot-opening signing message is not UTF-8".to_owned())?;

    let preview = PreviewDocument {
        schema: PREVIEW_SCHEMA.to_owned(),
        statement: StatementDocument {
            schema: dregg_persist::POA_SLOT_OPENING_STATEMENT_SCHEMA_V1.to_owned(),
            authority_id: hex(&authority_id),
            mission_id: args.mission_id,
            slot: args.slot,
            commitment: hex(&commitment),
        },
        signing_message_sha256: hex(&sha256(signing_message.as_bytes())),
        signing_message,
    };
    serde_json::to_string_pretty(&preview)
        .map_err(|error| format!("cannot encode the slot-opening preview: {error}"))
}

/// Step 3: verify the curator signature and the secret, then install both.
///
/// Needs no curator key. Every check that matters lives in
/// `install_poa_signal_slot_v1`, so a caller cannot reach storage around them.
pub fn initialize_poa_signal_slot(
    args: &PoaSlotOpeningArgs,
    signed_opening: &Path,
) -> Result<PoaSlotOpeningReport, String> {
    let authority_id = parse_hex32(&args.authority_id, "authority_id")?;
    let secret = read_secret(&args.secret_file)?;
    let document = load_envelope_document(signed_opening)?;

    if document.statement.schema != dregg_persist::POA_SLOT_OPENING_STATEMENT_SCHEMA_V1 {
        return Err("slot-opening statement has a foreign schema".to_owned());
    }
    let statement_authority = parse_hex32(&document.statement.authority_id, "authority_id")?;
    let commitment = parse_hex32(&document.statement.commitment, "commitment")?;
    if statement_authority != authority_id
        || document.statement.mission_id != args.mission_id
        || document.statement.slot != args.slot
    {
        return Err(
            "the signed slot opening does not name the coordinates this command was given"
                .to_owned(),
        );
    }
    let curator_key = parse_hex32(&document.curator_key, "curator_key")?;
    let signature = parse_hex64(&document.signature, "signature")?;

    let statement = PoaSlotOpeningStatementV1::new(
        authority_id,
        document.statement.mission_id,
        document.statement.slot,
        commitment,
    );
    let envelope = SignedPoaSlotOpeningEnvelopeV1::new(statement, curator_key, signature);

    let store = PersistentStore::open(&args.data_dir)
        .map_err(|error| format!("cannot open the PoA node store: {error}"))?;
    let status = store
        .install_poa_signal_slot_v1(&envelope, secret)
        .map_err(|error| format!("PoA slot install refused: {error}"))?;

    Ok(PoaSlotOpeningReport {
        status,
        slot: document.statement.slot,
        mission_id: document.statement.mission_id,
        commitment: hex(&commitment),
    })
}

/// Ask Lean for `HiddenInstance.commit secret slot`.
///
/// ⚠ There is no Rust fallback and there must never be one. Absent the export this
/// refuses, and the operator cannot open a slot — which is the correct outcome: a
/// commitment the node computed with an unproven second implementation of the
/// sponge is a commitment nobody can check.
pub(crate) fn derive_commitment(secret: [u8; 32], slot: u64) -> Result<[u8; 32], String> {
    let zero = hex(&[0u8; 32]);
    let wire = format!(
        "{{\"format\":\"{}\",\"slot\":{},\"secret\":\"{}\",\"mission_id\":0,\"epoch\":0,\
         \"federation_id\":\"{zero}\",\"content_session\":\"{zero}\",\"player_key\":\"{zero}\"}}",
        dregg_lean_ffi::poa_slot_derive_ffi::SLOT_DERIVE_INPUT_FORMAT,
        slot,
        hex(&secret),
    );
    let reply = dregg_lean_ffi::poa_slot_derive_ffi::derive_poa_slot_instance(&wire)
        .map_err(|error| format!("cannot derive the slot commitment: {error}"))?
        .ok_or_else(|| {
            "Lean refused the slot commitment derivation for this secret and slot".to_owned()
        })?;
    let parsed: serde_json::Value = serde_json::from_str(&reply)
        .map_err(|error| format!("Lean slot derivation reply is not JSON: {error}"))?;
    let commitment = parsed
        .get("commitment")
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| "Lean slot derivation reply lacks a commitment".to_owned())?;
    parse_hex32(commitment, "derived commitment")
}

/// Read the curator's slot secret. Refuses anything that is not exactly 64 hex
/// characters so a truncated or line-wrapped file cannot become a short secret.
fn read_secret(path: &Path) -> Result<[u8; 32], String> {
    let raw = fs::read_to_string(path)
        .map_err(|error| format!("cannot read the slot secret {}: {error}", path.display()))?;
    let trimmed = raw.trim();
    if trimmed.len() != 64 {
        return Err(format!(
            "the slot secret in {} is {} characters; it must be exactly 64 lowercase hex",
            path.display(),
            trimmed.len()
        ));
    }
    parse_hex32(trimmed, "slot secret")
}

fn load_envelope_document(path: &Path) -> Result<EnvelopeDocument, String> {
    let raw = fs::read_to_string(path)
        .map_err(|error| format!("cannot read {}: {error}", path.display()))?;
    let document: EnvelopeDocument = serde_json::from_str(&raw)
        .map_err(|error| format!("{} is not a slot-opening envelope: {error}", path.display()))?;
    if document.schema != ENVELOPE_SCHEMA {
        return Err(format!(
            "{} has schema {:?}, expected {ENVELOPE_SCHEMA}",
            path.display(),
            document.schema
        ));
    }
    Ok(document)
}

fn parse_hex32(value: &str, label: &str) -> Result<[u8; 32], String> {
    let bytes = parse_hex(value, 32, label)?;
    let mut out = [0u8; 32];
    out.copy_from_slice(&bytes);
    Ok(out)
}

fn parse_hex64(value: &str, label: &str) -> Result<[u8; 64], String> {
    let bytes = parse_hex(value, 64, label)?;
    let mut out = [0u8; 64];
    out.copy_from_slice(&bytes);
    Ok(out)
}

fn parse_hex(value: &str, length: usize, label: &str) -> Result<Vec<u8>, String> {
    if value.len() != length * 2
        || !value
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err(format!(
            "{label} must be exactly {} lowercase hex characters",
            length * 2
        ));
    }
    (0..length)
        .map(|i| {
            u8::from_str_radix(&value[i * 2..i * 2 + 2], 16)
                .map_err(|_| format!("{label} is not hex"))
        })
        .collect()
}

fn hex(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(char::from_digit(u32::from(byte >> 4), 16).unwrap_or('0'));
        out.push(char::from_digit(u32::from(byte & 0x0f), 16).unwrap_or('0'));
    }
    out
}

fn sha256(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_short_or_wrapped_secret_is_refused() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("secret.hex");
        fs::write(&path, "abcd").unwrap();
        assert!(read_secret(&path).unwrap_err().contains("64 lowercase hex"));
    }

    #[test]
    fn a_trailing_newline_is_tolerated_but_uppercase_is_not() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("secret.hex");
        fs::write(&path, format!("{}\n", "ab".repeat(32))).unwrap();
        assert_eq!(read_secret(&path).unwrap(), [0xab; 32]);

        fs::write(&path, "AB".repeat(32)).unwrap();
        assert!(read_secret(&path).is_err());
    }

    /// The statement encoding is the thing the curator signs. If it drifts, every
    /// previously signed opening silently stops verifying, so it is pinned here
    /// against a literal rather than against its own constructor.
    #[test]
    fn the_signing_message_is_the_documented_canonical_bytes() {
        let statement = PoaSlotOpeningStatementV1::new([0x44; 32], 1, 9, [0xbc; 32]);
        let message = String::from_utf8(statement.signing_message().unwrap()).unwrap();
        assert_eq!(
            message,
            format!(
                "{{\"schema\":\"POA-SLOT-OPENING-STATEMENT-1\",\"authority_id\":\"{}\",\
                 \"mission_id\":1,\"slot\":9,\"commitment\":\"{}\"}}",
                "44".repeat(32),
                "bc".repeat(32)
            )
        );
    }

    /// Absent the Lean export the ceremony refuses rather than inventing a
    /// commitment. This is the test that would go red if someone "fixed" the gap
    /// by writing the sponge in Rust.
    #[test]
    fn without_the_lean_export_the_commitment_cannot_be_derived() {
        if dregg_lean_ffi::poa_slot_derive_ffi::poa_slot_derive_available() {
            return;
        }
        let error = derive_commitment([0x77; 32], 9).unwrap_err();
        assert!(
            error.contains("not exported by the linked archive"),
            "unexpected error: {error}"
        );
    }
}
