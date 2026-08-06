//! Curator-side signing of `POA-WORLD-ACTIVATION-STATEMENT-1`.
//!
//! # Why this lives here and not in the node
//!
//! `install_poa_world_activation_v1` verifies the envelope against the pin the
//! store already trusts. That check is only worth something if the envelope was
//! produced somewhere the node cannot reach — which is the whole point of the
//! preview / sign / init split, and the reason `poa_galley_genesis` deliberately
//! never mints a curator signature. The node prints the bytes; the curator, holding
//! the key, signs them; the node verifies and installs.
//!
//! # ⚠ Why the canonical bytes are RE-DERIVED here instead of imported
//!
//! `PoaWorldActivationStatementV1::signing_message` lives in `dregg-persist`, and
//! `dregg-persist` depends on `dregg-lean-ffi` — so importing it would make this
//! offline signing tool require a linked Lean archive on the machine that holds the
//! curator key. That is the wrong dependency for a tool whose entire job is to run
//! somewhere isolated.
//!
//! So the statement encoding is written out again here. That is a second
//! implementation, and it is deliberate rather than accidental: [`sign_world_activation`]
//! recomputes the bytes from the preview's STRUCTURED fields and refuses if they
//! differ from the `signing_message` the node printed. Two independent derivations
//! that must agree at the moment of signing is a gate; taking the node's string on
//! faith would collapse it to one source, and signing a string nobody re-derived is
//! how a curator signs something other than what they were shown.
//!
//! Drift between the two implementations therefore cannot ship silently: it stops
//! the next signing operation.

use std::path::Path;

use dregg_types::{PublicKey, Signature, SigningKey};
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};

use crate::CuratorError;

pub const PREVIEW_SCHEMA: &str = "POA-WORLD-ACTIVATION-PREVIEW-V1";
pub const ENVELOPE_SCHEMA: &str = "POA-WORLD-ACTIVATION-ENVELOPE-V1";
pub const STATEMENT_SCHEMA: &str = "POA-WORLD-ACTIVATION-STATEMENT-1";

const ADVANCE: &str = "advance";
const ROLLBACK: &str = "rollback";
const MAX_DOCUMENT_BYTES: u64 = 64 * 1024;

/// The world identity, exactly as both the preview and the envelope spell it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WorldDocument {
    pub federation_id: String,
    pub content_root: String,
    pub activation_digest: String,
    pub content_session: String,
    pub content_epoch: u64,
}

/// `POA-WORLD-ACTIVATION-PREVIEW-V1`, as emitted by `dregg-node
/// poa-galley-world-preview`.
///
/// Mirrors that command's `PreviewDocument`, which is `Serialize`-only and lives in
/// the node crate. `deny_unknown_fields` means a preview that grew a field this
/// tool does not understand is refused rather than partially read.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PreviewDocument {
    pub schema: String,
    pub statement_schema: String,
    pub world: WorldDocument,
    pub counter: u64,
    pub predecessor_head: String,
    pub kind: String,
    pub rollback_target: Option<String>,
    pub curator_key: String,
    pub signing_message: String,
    pub signing_message_sha256: String,
}

/// `POA-WORLD-ACTIVATION-ENVELOPE-V1` — the document `dregg-node
/// init-poa-galley-world` consumes.
///
/// ⚠ This is NOT `SignedPoaWorldActivationEnvelopeV1`'s own serde shape. That
/// struct holds `[u8; 32]` / `Vec<u8>`, which serde_json renders as arrays of
/// numbers; the node's installer parses this flat, hex-spelled document instead and
/// builds the persist type from it. Checked against
/// `node/src/poa_galley_genesis.rs::EnvelopeDocument`, not assumed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EnvelopeDocument {
    pub schema: String,
    pub world: WorldDocument,
    pub counter: u64,
    pub predecessor_head: String,
    pub kind: String,
    pub rollback_target: Option<String>,
    pub curator_key: String,
    pub signature: String,
}

/// ⚠ THE FIELD ORDER OF THESE TWO STRUCTS IS THE SIGNED MESSAGE.
///
/// `signing_message()` is `serde_json::to_vec` of exactly this shape, and a derived
/// `Serialize` emits declaration order. Reordering a field here changes the bytes
/// the curator signs, which makes every previously signed activation unverifiable
/// and every new one refused by the node. It is not style.
///
/// Transcribed from `persist/src/poa_world_activation.rs`'s `JsonStatement` /
/// `JsonWorld`.
#[derive(Serialize)]
struct StatementJson<'a> {
    schema: &'static str,
    world: StatementWorldJson<'a>,
    counter: u64,
    predecessor_head: &'a str,
    kind: &'a str,
    rollback_target: Option<&'a str>,
}

#[derive(Serialize)]
struct StatementWorldJson<'a> {
    federation_id: &'a str,
    content_root: &'a str,
    activation_digest: &'a str,
    content_session: &'a str,
    content_epoch: u64,
}

/// What a successful signing produced, for the caller to report.
#[derive(Clone, Debug)]
pub struct SignedWorldActivation {
    pub envelope: EnvelopeDocument,
    pub signing_message: String,
    pub signing_message_sha256: String,
}

fn catalog(message: impl Into<String>) -> CuratorError {
    CuratorError::Catalog(message.into())
}

fn require_hex32(value: &str, field: &'static str) -> Result<[u8; 32], CuratorError> {
    crate::parse_hex_array::<32>(value, field)
}

/// Re-derive the exact canonical bytes the curator's signature covers.
///
/// This mirrors `PoaWorldActivationStatementV1::new` + `signing_message`, INCLUDING
/// its refusals: a zero identity, a zero counter, an `advance` carrying a rollback
/// target, or a `rollback` without one. A tool that signed a statement the store
/// would refuse to install is a tool that produces useless signatures, and worse,
/// one that would let an operator believe a ceremony completed.
pub fn statement_signing_message(
    world: &WorldDocument,
    counter: u64,
    predecessor_head: &str,
    kind: &str,
    rollback_target: Option<&str>,
) -> Result<Vec<u8>, CuratorError> {
    let federation_id = require_hex32(&world.federation_id, "world.federation_id")?;
    let content_root = require_hex32(&world.content_root, "world.content_root")?;
    let activation_digest = require_hex32(&world.activation_digest, "world.activation_digest")?;
    let content_session = require_hex32(&world.content_session, "world.content_session")?;
    // `validate_world`: no zero identity, no zero epoch.
    if federation_id == [0; 32]
        || content_root == [0; 32]
        || activation_digest == [0; 32]
        || content_session == [0; 32]
        || world.content_epoch == 0
    {
        return Err(catalog("PoA active world contains a zero identity"));
    }
    if counter == 0 {
        return Err(catalog("PoA world activation counter must be nonzero"));
    }
    let _ = require_hex32(predecessor_head, "predecessor_head")?;
    match (kind, rollback_target) {
        (ADVANCE, Some(_)) => return Err(catalog("PoA advance carries a rollback target")),
        (ROLLBACK, None) => return Err(catalog("PoA rollback omitted its target")),
        (ADVANCE, None) | (ROLLBACK, Some(_)) => {}
        (other, _) => {
            return Err(catalog(format!(
                "PoA world activation kind {other:?} is neither advance nor rollback"
            )));
        }
    }
    if let Some(target) = rollback_target {
        let _ = require_hex32(target, "rollback_target")?;
    }

    serde_json::to_vec(&StatementJson {
        schema: STATEMENT_SCHEMA,
        world: StatementWorldJson {
            federation_id: &world.federation_id,
            content_root: &world.content_root,
            activation_digest: &world.activation_digest,
            content_session: &world.content_session,
            content_epoch: world.content_epoch,
        },
        counter,
        predecessor_head,
        kind,
        rollback_target,
    })
    .map_err(|error| catalog(format!("PoA activation statement JSON failed: {error}")))
}

fn load_document<T: serde::de::DeserializeOwned>(
    path: &Path,
    what: &str,
) -> Result<T, CuratorError> {
    let metadata = std::fs::metadata(path)
        .map_err(|error| catalog(format!("{what} is unavailable: {error}")))?;
    if !metadata.is_file() {
        return Err(catalog(format!("{what} is not a regular file")));
    }
    if metadata.len() == 0 || metadata.len() > MAX_DOCUMENT_BYTES {
        return Err(catalog(format!("{what} is empty or exceeds 64 KiB")));
    }
    let bytes =
        std::fs::read(path).map_err(|error| catalog(format!("{what} is unreadable: {error}")))?;
    serde_json::from_slice(&bytes)
        .map_err(|error| catalog(format!("{what} is not the exact document: {error}")))
}

/// Sign one activation preview.
///
/// The secret must derive the pinned key, and the pin must be the key the preview
/// names — otherwise the operator is signing a statement addressed to a different
/// curator, which the node would refuse after the fact rather than before.
pub fn sign_world_activation(
    secret: &SigningKey,
    pin: &PublicKey,
    preview: &PreviewDocument,
) -> Result<SignedWorldActivation, CuratorError> {
    if preview.schema != PREVIEW_SCHEMA {
        return Err(catalog(format!(
            "preview schema is {:?}, expected {PREVIEW_SCHEMA}",
            preview.schema
        )));
    }
    if preview.statement_schema != STATEMENT_SCHEMA {
        return Err(catalog(format!(
            "preview statement schema is {:?}, expected {STATEMENT_SCHEMA}",
            preview.statement_schema
        )));
    }
    if secret.public_key() != *pin {
        return Err(catalog("secret key does not match the external public pin"));
    }
    let pin_hex = crate::hex_encode(&pin.0);
    if preview.curator_key != pin_hex {
        return Err(catalog(format!(
            "preview names curator key {} but the pin is {pin_hex}; refusing to sign an \
             activation addressed to another curator",
            preview.curator_key
        )));
    }

    // ⚠ The independent derivation. The preview's own `signing_message` string is
    // NOT trusted: it is recomputed from the structured fields and compared.
    let derived = statement_signing_message(
        &preview.world,
        preview.counter,
        &preview.predecessor_head,
        &preview.kind,
        preview.rollback_target.as_deref(),
    )?;
    let derived_text = String::from_utf8(derived.clone())
        .map_err(|_| catalog("re-derived signing message is not UTF-8"))?;
    if derived_text != preview.signing_message {
        return Err(catalog(format!(
            "the preview's signing_message is not what its own fields derive; refusing to sign \
             bytes nobody re-derived.\n  preview:  {}\n  derived:  {derived_text}",
            preview.signing_message
        )));
    }
    let derived_sha = crate::hex_encode(&Sha256::digest(&derived));
    if derived_sha != preview.signing_message_sha256 {
        return Err(catalog(format!(
            "preview signing_message_sha256 is {} but the derived message hashes to {derived_sha}",
            preview.signing_message_sha256
        )));
    }

    let signature = dregg_types::sign(secret, &derived);
    // Self-verify before writing, exactly as `sign-content` does. A signature this
    // tool cannot itself check is one the operator would only discover at install.
    if !pin.verify(&derived, &signature) {
        return Err(catalog("self-verification of the fresh signature failed"));
    }

    Ok(SignedWorldActivation {
        envelope: EnvelopeDocument {
            schema: ENVELOPE_SCHEMA.to_owned(),
            world: preview.world.clone(),
            counter: preview.counter,
            predecessor_head: preview.predecessor_head.clone(),
            kind: preview.kind.clone(),
            rollback_target: preview.rollback_target.clone(),
            curator_key: pin_hex,
            signature: crate::hex_encode(&signature.0),
        },
        signing_message: derived_text,
        signing_message_sha256: derived_sha,
    })
}

/// Verify a signed envelope against the pin, re-deriving the message the same way.
///
/// Cheap, and it means an operator can check before touching the node rather than
/// discovering a bad ceremony at install time.
pub fn verify_world_activation(
    pin: &PublicKey,
    envelope: &EnvelopeDocument,
) -> Result<String, CuratorError> {
    if envelope.schema != ENVELOPE_SCHEMA {
        return Err(catalog(format!(
            "envelope schema is {:?}, expected {ENVELOPE_SCHEMA}",
            envelope.schema
        )));
    }
    let named = require_hex32(&envelope.curator_key, "curator_key")?;
    if named != pin.0 {
        return Err(catalog(
            "envelope names a curator key that is not the external pin",
        ));
    }
    let message = statement_signing_message(
        &envelope.world,
        envelope.counter,
        &envelope.predecessor_head,
        &envelope.kind,
        envelope.rollback_target.as_deref(),
    )?;
    let raw = crate::parse_hex_array::<64>(&envelope.signature, "signature")?;
    if !pin.verify(&message, &Signature(raw)) {
        return Err(catalog("activation signature verification failed"));
    }
    Ok(crate::hex_encode(&Sha256::digest(&message)))
}

/// Load a preview document from disk.
pub fn load_preview(path: &Path) -> Result<PreviewDocument, CuratorError> {
    load_document(path, "PoA activation preview")
}

/// Load a signed envelope document from disk.
pub fn load_envelope(path: &Path) -> Result<EnvelopeDocument, CuratorError> {
    load_document(path, "PoA activation envelope")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn world() -> WorldDocument {
        WorldDocument {
            federation_id: "4e".repeat(32),
            content_root: "2c".repeat(32),
            activation_digest: "60".repeat(32),
            content_session: "50".repeat(32),
            content_epoch: 1,
        }
    }

    fn preview_for(secret: &SigningKey) -> PreviewDocument {
        let world = world();
        let message =
            statement_signing_message(&world, 1, &"00".repeat(32), ADVANCE, None).unwrap();
        PreviewDocument {
            schema: PREVIEW_SCHEMA.to_owned(),
            statement_schema: STATEMENT_SCHEMA.to_owned(),
            world,
            counter: 1,
            predecessor_head: "00".repeat(32),
            kind: ADVANCE.to_owned(),
            rollback_target: None,
            curator_key: crate::hex_encode(&secret.public_key().0),
            signing_message: String::from_utf8(message.clone()).unwrap(),
            signing_message_sha256: crate::hex_encode(&Sha256::digest(&message)),
        }
    }

    /// ⚠ THE CANONICAL BYTES, pinned against a literal.
    ///
    /// This is the one thing in this module that cannot be checked against
    /// `dregg-persist` at compile time, because importing it would drag a Lean
    /// archive into the signing tool. So it is pinned here by hand, transcribed
    /// from `JsonStatement` / `JsonWorld`. If the persist encoding ever changes,
    /// THIS is the test that has to be updated deliberately — and the
    /// preview-vs-derived comparison in `sign_world_activation` is what catches it
    /// in the field, at the moment of signing, before a bad signature exists.
    #[test]
    fn the_signing_message_is_the_documented_canonical_bytes() {
        let message =
            statement_signing_message(&world(), 1, &"00".repeat(32), ADVANCE, None).unwrap();
        assert_eq!(
            String::from_utf8(message).unwrap(),
            format!(
                "{{\"schema\":\"POA-WORLD-ACTIVATION-STATEMENT-1\",\"world\":{{\
                 \"federation_id\":\"{fed}\",\"content_root\":\"{root}\",\
                 \"activation_digest\":\"{act}\",\"content_session\":\"{ses}\",\
                 \"content_epoch\":1}},\"counter\":1,\"predecessor_head\":\"{pred}\",\
                 \"kind\":\"advance\",\"rollback_target\":null}}",
                fed = "4e".repeat(32),
                root = "2c".repeat(32),
                act = "60".repeat(32),
                ses = "50".repeat(32),
                pred = "00".repeat(32),
            )
        );
    }

    #[test]
    fn a_signed_preview_verifies_and_produces_the_installer_shape() {
        let secret = SigningKey::from_bytes(&[0x41; 32]);
        let pin = secret.public_key();
        let preview = preview_for(&secret);
        let signed = sign_world_activation(&secret, &pin, &preview).unwrap();

        assert_eq!(signed.envelope.schema, ENVELOPE_SCHEMA);
        assert_eq!(signed.envelope.world, preview.world);
        assert_eq!(signed.envelope.rollback_target, None);
        assert_eq!(signed.signing_message, preview.signing_message);
        assert_eq!(
            verify_world_activation(&pin, &signed.envelope).unwrap(),
            preview.signing_message_sha256
        );

        // The emitted document must round-trip through the installer's grammar:
        // `deny_unknown_fields` on both sides makes this a real shape check.
        let bytes = serde_json::to_vec(&signed.envelope).unwrap();
        let reparsed: EnvelopeDocument = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(reparsed, signed.envelope);
    }

    /// ⚠ THE POINT OF THE WHOLE MODULE: a preview whose printed
    /// `signing_message` disagrees with its own structured fields must not be
    /// signed. Without this, the curator signs whatever string it is handed.
    #[test]
    fn a_preview_whose_message_does_not_match_its_fields_is_refused() {
        let secret = SigningKey::from_bytes(&[0x41; 32]);
        let pin = secret.public_key();

        let mut tampered = preview_for(&secret);
        tampered.signing_message = tampered.signing_message.replace(
            &format!("\"content_epoch\":{}", tampered.world.content_epoch),
            "\"content_epoch\":9",
        );
        let error = sign_world_activation(&secret, &pin, &tampered).unwrap_err();
        assert!(
            format!("{error}").contains("is not what its own fields derive"),
            "unexpected error: {error}"
        );

        // And the reverse: fields moved, message left alone.
        let mut moved = preview_for(&secret);
        moved.counter = 4;
        let error = sign_world_activation(&secret, &pin, &moved).unwrap_err();
        assert!(
            format!("{error}").contains("is not what its own fields derive"),
            "unexpected error: {error}"
        );

        // A stale sha with a consistent message is still a refusal.
        let mut bad_sha = preview_for(&secret);
        bad_sha.signing_message_sha256 = "ab".repeat(32);
        let error = sign_world_activation(&secret, &pin, &bad_sha).unwrap_err();
        assert!(
            format!("{error}").contains("hashes to"),
            "unexpected error: {error}"
        );
    }

    #[test]
    fn a_foreign_key_or_pin_is_refused_before_any_signature_exists() {
        let secret = SigningKey::from_bytes(&[0x41; 32]);
        let other = SigningKey::from_bytes(&[0x42; 32]);
        let preview = preview_for(&secret);

        // Secret that does not derive the pin.
        let error = sign_world_activation(&other, &secret.public_key(), &preview).unwrap_err();
        assert!(
            format!("{error}").contains("does not match the external public pin"),
            "unexpected error: {error}"
        );

        // Right secret, but the preview was addressed to someone else.
        let error = sign_world_activation(&other, &other.public_key(), &preview).unwrap_err();
        assert!(
            format!("{error}").contains("addressed to another curator"),
            "unexpected error: {error}"
        );
    }

    #[test]
    fn a_statement_the_store_would_refuse_is_never_signed() {
        let zero = "00".repeat(32);
        let mut zero_world = world();
        zero_world.federation_id = zero.clone();
        assert!(
            statement_signing_message(&zero_world, 1, &zero, ADVANCE, None).is_err(),
            "a zero identity was encoded"
        );

        let mut zero_epoch = world();
        zero_epoch.content_epoch = 0;
        assert!(statement_signing_message(&zero_epoch, 1, &zero, ADVANCE, None).is_err());

        assert!(
            statement_signing_message(&world(), 0, &zero, ADVANCE, None).is_err(),
            "a zero counter was encoded"
        );
        assert!(
            statement_signing_message(&world(), 1, &zero, ADVANCE, Some(&zero)).is_err(),
            "an advance carrying a rollback target was encoded"
        );
        assert!(
            statement_signing_message(&world(), 1, &zero, ROLLBACK, None).is_err(),
            "a rollback without a target was encoded"
        );
        assert!(
            statement_signing_message(&world(), 1, &zero, "sideways", None).is_err(),
            "an unknown kind was encoded"
        );
    }

    #[test]
    fn a_tampered_envelope_does_not_verify() {
        let secret = SigningKey::from_bytes(&[0x41; 32]);
        let pin = secret.public_key();
        let signed = sign_world_activation(&secret, &pin, &preview_for(&secret)).unwrap();

        let mut moved = signed.envelope.clone();
        moved.counter = 2;
        assert!(verify_world_activation(&pin, &moved).is_err());

        let mut relabelled = signed.envelope.clone();
        relabelled.world.content_root = "ff".repeat(32);
        assert!(verify_world_activation(&pin, &relabelled).is_err());

        let mut foreign = signed.envelope.clone();
        foreign.curator_key =
            crate::hex_encode(&SigningKey::from_bytes(&[0x42; 32]).public_key().0);
        assert!(verify_world_activation(&pin, &foreign).is_err());
    }
}
