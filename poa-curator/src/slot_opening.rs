//! Curator-side signing of `POA-SLOT-OPENING-STATEMENT-1`.
//!
//! # The step this file exists to fill
//!
//! Opening a Signal slot is a three-step ceremony (`node/src/poa_signal_slot_ceremony.rs`):
//!
//! ```text
//! 0. the curator draws a 32-byte slot secret OFF-LINE          (curator, no node)
//! 1. dregg-node poa-slot-opening-preview …  → commitment + the exact signing message
//! 2. the curator signs that message with the pinned Ed25519 key    (CURATOR KEY)
//! 3. dregg-node init-poa-signal-slot …      → verify, then install
//! ```
//!
//! Steps 1 and 3 shipped. **Step 2 had no tooling at all** — no command anywhere in
//! this crate produced a `POA-SLOT-OPENING-ENVELOPE-V1`, so the ceremony could not
//! be completed except by hand-minting an Ed25519 signature over bytes nobody
//! re-derived. Until this file, no Signal slot could be opened, and because
//! `blocklace_sync` refuses to judge a scored run when no slot is open
//! (`load_poa_signal_open_slot_v1` → `None` → refuse), **no judged run could settle.**
//!
//! # ⚠ Why the canonical bytes are RE-DERIVED here instead of imported
//!
//! `PoaSlotOpeningStatementV1::signing_message` lives in `dregg-persist`, and
//! `dregg-persist` depends on `dregg-lean-ffi` — importing it would make this offline
//! signing tool require a linked Lean archive on the machine holding the curator key.
//! That is the wrong dependency for a tool whose whole job is to run somewhere
//! isolated.
//!
//! So the statement encoding is written out again here, deliberately rather than
//! accidentally: [`sign_slot_opening`] recomputes the bytes from the preview's
//! STRUCTURED fields and refuses if they differ from the `signing_message` the node
//! printed. Two independent derivations that must agree at the moment of signing is a
//! gate; taking the node's string on faith would collapse it to one source, and
//! signing a string nobody re-derived is how a curator signs something other than
//! what they were shown. Drift between the two implementations cannot ship silently:
//! it stops the next signing operation.
//!
//! # ⚠ One check this tool CANNOT make, stated plainly
//!
//! `sign_world_activation` refuses a preview addressed to a different curator,
//! because `POA-WORLD-ACTIVATION-PREVIEW-V1` carries a `curator_key` field. The slot
//! preview does **not** carry one (`node/src/poa_signal_slot_ceremony.rs`'s
//! `PreviewDocument` is `schema` / `statement` / `signing_message` /
//! `signing_message_sha256`). There is therefore nothing in a slot preview to compare
//! a pin against, and this tool cannot detect that it was handed another curator's
//! preview. It is not a check that was omitted; it is one the document shape does not
//! support. The node still refuses at install (`verify_signature` compares the
//! envelope's key against the store's installed pin), so the failure is late rather
//! than absent.

use std::path::Path;

use dregg_types::{PublicKey, Signature, SigningKey};
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};

use crate::CuratorError;

pub const PREVIEW_SCHEMA: &str = "POA-SLOT-OPENING-PREVIEW-V1";
pub const ENVELOPE_SCHEMA: &str = "POA-SLOT-OPENING-ENVELOPE-V1";
pub const STATEMENT_SCHEMA: &str = "POA-SLOT-OPENING-STATEMENT-1";

const MAX_DOCUMENT_BYTES: u64 = 64 * 1024;

/// The slot coordinates, exactly as both the preview and the envelope spell them.
///
/// Transcribed from `node/src/poa_signal_slot_ceremony.rs`'s `StatementDocument`,
/// which is also `deny_unknown_fields`: a document that grew a field is refused
/// rather than partially read.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StatementDocument {
    pub schema: String,
    pub authority_id: String,
    pub mission_id: u64,
    pub slot: u64,
    pub commitment: String,
}

/// `POA-SLOT-OPENING-PREVIEW-V1`, as emitted by `dregg-node poa-slot-opening-preview`.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PreviewDocument {
    pub schema: String,
    pub statement: StatementDocument,
    pub signing_message: String,
    pub signing_message_sha256: String,
}

/// `POA-SLOT-OPENING-ENVELOPE-V1` — the document `dregg-node init-poa-signal-slot`
/// consumes.
///
/// ⚠ This is NOT `SignedPoaSlotOpeningEnvelopeV1`'s own serde shape. That struct
/// holds `[u8; 32]` / `Vec<u8>`, which serde_json renders as arrays of numbers; the
/// node's installer parses this flat, hex-spelled document instead and builds the
/// persist type from it. Checked against `node/src/poa_signal_slot_ceremony.rs`'s
/// `EnvelopeDocument`, not assumed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EnvelopeDocument {
    pub schema: String,
    pub statement: StatementDocument,
    pub curator_key: String,
    pub signature: String,
}

/// What a successful signing produced, for the caller to report.
#[derive(Clone, Debug)]
pub struct SignedSlotOpening {
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
/// ⚠ THE LITERAL BELOW IS THE SIGNED MESSAGE. It mirrors
/// `PoaSlotOpeningStatementV1::signing_message` (`persist/src/poa_signal_slot.rs`),
/// which is a `format!` rather than a serde encoding — so this side is a `format!`
/// too. Changing the key order, the spacing, or the hex case here changes the bytes
/// the curator signs, which makes every previously signed opening unverifiable and
/// every new one refused by the node. It is not style.
///
/// The hex fields are re-parsed rather than passed through: `parse_hex_array` accepts
/// only exactly 64 lowercase hex characters, which is the same alphabet the node's
/// `parse_hex` enforces. An uppercase or short `authority_id` would otherwise be
/// signed verbatim here and refused at install.
pub fn statement_signing_message(statement: &StatementDocument) -> Result<Vec<u8>, CuratorError> {
    if statement.schema != STATEMENT_SCHEMA {
        return Err(catalog(format!(
            "slot opening statement schema is {:?}, expected {STATEMENT_SCHEMA}",
            statement.schema
        )));
    }
    let authority_id = require_hex32(&statement.authority_id, "statement.authority_id")?;
    let commitment = require_hex32(&statement.commitment, "statement.commitment")?;

    Ok(format!(
        "{{\"schema\":\"{}\",\"authority_id\":\"{}\",\"mission_id\":{},\"slot\":{},\"commitment\":\"{}\"}}",
        STATEMENT_SCHEMA,
        crate::hex_encode(&authority_id),
        statement.mission_id,
        statement.slot,
        crate::hex_encode(&commitment),
    )
    .into_bytes())
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

/// Sign one slot-opening preview.
///
/// The secret must derive the pinned key. Unlike world activation there is no
/// preview-names-this-curator check available — see the module header for why, and
/// why that is a document-shape fact rather than a missing check.
pub fn sign_slot_opening(
    secret: &SigningKey,
    pin: &PublicKey,
    preview: &PreviewDocument,
) -> Result<SignedSlotOpening, CuratorError> {
    if preview.schema != PREVIEW_SCHEMA {
        return Err(catalog(format!(
            "preview schema is {:?}, expected {PREVIEW_SCHEMA}",
            preview.schema
        )));
    }
    if secret.public_key() != *pin {
        return Err(catalog("secret key does not match the external public pin"));
    }

    // ⚠ The independent derivation. The preview's own `signing_message` string is
    // NOT trusted: it is recomputed from the structured fields and compared.
    let derived = statement_signing_message(&preview.statement)?;
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
    // Self-verify before writing, exactly as `sign-content` and
    // `sign-world-activation` do. A signature this tool cannot itself check is one
    // the operator would only discover at install.
    if !pin.verify(&derived, &signature) {
        return Err(catalog("self-verification of the fresh signature failed"));
    }

    Ok(SignedSlotOpening {
        envelope: EnvelopeDocument {
            schema: ENVELOPE_SCHEMA.to_owned(),
            statement: preview.statement.clone(),
            curator_key: crate::hex_encode(&pin.0),
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
pub fn verify_slot_opening(
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
    let message = statement_signing_message(&envelope.statement)?;
    let raw = crate::parse_hex_array::<64>(&envelope.signature, "signature")?;
    if !pin.verify(&message, &Signature(raw)) {
        return Err(catalog("slot opening signature verification failed"));
    }
    Ok(crate::hex_encode(&Sha256::digest(&message)))
}

/// Load a preview document from disk.
pub fn load_preview(path: &Path) -> Result<PreviewDocument, CuratorError> {
    load_document(path, "PoA slot opening preview")
}

/// Load a signed envelope document from disk.
pub fn load_envelope(path: &Path) -> Result<EnvelopeDocument, CuratorError> {
    load_document(path, "PoA slot opening envelope")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn statement() -> StatementDocument {
        StatementDocument {
            schema: STATEMENT_SCHEMA.to_owned(),
            authority_id: "44".repeat(32),
            mission_id: 1,
            slot: 9,
            commitment: "bc".repeat(32),
        }
    }

    fn keypair() -> (SigningKey, PublicKey) {
        let secret = dregg_types::SigningKey::from_bytes(&[7u8; 32]);
        let pin = secret.public_key();
        (secret, pin)
    }

    fn preview_for(statement: StatementDocument) -> PreviewDocument {
        let message = statement_signing_message(&statement).expect("derivable");
        PreviewDocument {
            schema: PREVIEW_SCHEMA.to_owned(),
            signing_message: String::from_utf8(message.clone()).expect("utf8"),
            signing_message_sha256: crate::hex_encode(&Sha256::digest(&message)),
            statement,
        }
    }

    /// The bytes the curator signs, pinned against a LITERAL rather than against the
    /// constructor that produces them.
    ///
    /// This is the same literal `poa_signal_slot_ceremony`'s
    /// `the_signing_message_is_the_documented_canonical_bytes` pins on the node side,
    /// and that is the entire point: two crates that never call each other, asserting
    /// the same bytes. A pin against its own definition would be decoration.
    #[test]
    fn the_signing_message_is_the_documented_canonical_bytes() {
        let message = statement_signing_message(&statement()).expect("derivable");
        assert_eq!(
            String::from_utf8(message).expect("utf8"),
            format!(
                "{{\"schema\":\"POA-SLOT-OPENING-STATEMENT-1\",\"authority_id\":\"{}\",\
                 \"mission_id\":1,\"slot\":9,\"commitment\":\"{}\"}}",
                "44".repeat(32),
                "bc".repeat(32)
            )
        );
    }

    #[test]
    fn a_signed_opening_verifies_against_the_pin() {
        let (secret, pin) = keypair();
        let signed = sign_slot_opening(&secret, &pin, &preview_for(statement())).expect("signs");
        assert_eq!(signed.envelope.schema, ENVELOPE_SCHEMA);
        assert_eq!(signed.envelope.curator_key, crate::hex_encode(&pin.0));
        assert_eq!(signed.envelope.statement, statement());
        let sha = verify_slot_opening(&pin, &signed.envelope).expect("verifies");
        assert_eq!(sha, signed.signing_message_sha256);
    }

    /// ⚑ THE GATE THIS FILE EXISTS FOR. A preview whose `signing_message` does not
    /// match what its own structured fields derive is refused — the curator never
    /// signs bytes nobody re-derived.
    ///
    /// The hostile input is built CONSTRUCTIVELY from the honest preview (mutate the
    /// field, then assert the mutation actually changed it) rather than by
    /// string-replacing a literal that may have left the fixture.
    #[test]
    fn a_preview_whose_message_disagrees_with_its_fields_is_refused() {
        let (secret, pin) = keypair();
        let honest = preview_for(statement());

        let mut hostile = preview_for(statement());
        hostile.statement.slot = 10;
        assert_ne!(
            hostile.statement.slot, honest.statement.slot,
            "the mutation must actually change the slot, or this test asserts nothing"
        );
        // Keep the message/sha the node printed for slot 9 while the fields say 10 —
        // the exact substitution the independent derivation exists to catch.
        hostile.signing_message = honest.signing_message.clone();
        hostile.signing_message_sha256 = honest.signing_message_sha256.clone();
        assert_ne!(
            hostile.signing_message,
            preview_for(hostile.statement.clone()).signing_message,
            "the hostile preview must actually be inconsistent"
        );

        let error = sign_slot_opening(&secret, &pin, &hostile).expect_err("must refuse");
        assert!(
            error.to_string().contains("nobody re-derived"),
            "unexpected error: {error}"
        );
    }

    /// The sha is a second, independent handle on the same bytes; a preview whose
    /// digest disagrees is refused even when the message text matches.
    #[test]
    fn a_preview_with_a_wrong_message_digest_is_refused() {
        let (secret, pin) = keypair();
        let mut hostile = preview_for(statement());
        let honest_sha = hostile.signing_message_sha256.clone();
        hostile.signing_message_sha256 = crate::hex_encode(&Sha256::digest(b"not the message"));
        assert_ne!(
            hostile.signing_message_sha256, honest_sha,
            "the mutation must actually change the digest"
        );
        let error = sign_slot_opening(&secret, &pin, &hostile).expect_err("must refuse");
        assert!(
            error.to_string().contains("hashes to"),
            "unexpected error: {error}"
        );
    }

    #[test]
    fn a_secret_that_is_not_the_pin_cannot_sign() {
        let (secret, _) = keypair();
        let other = dregg_types::SigningKey::from_bytes(&[9u8; 32]).public_key();
        let error =
            sign_slot_opening(&secret, &other, &preview_for(statement())).expect_err("must refuse");
        assert!(
            error
                .to_string()
                .contains("does not match the external public pin"),
            "unexpected error: {error}"
        );
    }

    #[test]
    fn a_foreign_preview_or_statement_schema_is_refused() {
        let (secret, pin) = keypair();
        let mut wrong_preview = preview_for(statement());
        wrong_preview.schema = "POA-WORLD-ACTIVATION-PREVIEW-V1".to_owned();
        assert!(sign_slot_opening(&secret, &pin, &wrong_preview).is_err());

        let mut foreign = statement();
        foreign.schema = "POA-WORLD-ACTIVATION-STATEMENT-1".to_owned();
        assert!(statement_signing_message(&foreign).is_err());
    }

    /// Uppercase hex is refused rather than signed verbatim: the node's `parse_hex`
    /// accepts only lowercase, so a signature over uppercase bytes would verify here
    /// and be refused at install.
    ///
    /// ⚑ The first draft of this test uppercased `authority_id`, which is `"44"`
    /// repeated — all digits, so `to_uppercase()` returned the SAME string and the
    /// test asserted nothing about case at all. It only failed because the honest
    /// value is accepted. Every mutation below therefore asserts it actually
    /// mutated before the verdict is read.
    #[test]
    fn uppercase_or_short_hex_is_refused_not_normalized() {
        let base = statement();

        let mut upper = base.clone();
        upper.commitment = base.commitment.to_uppercase();
        assert_ne!(
            upper.commitment, base.commitment,
            "the uppercase mutation must actually change the string, or this asserts nothing"
        );
        assert!(statement_signing_message(&upper).is_err());

        let mut short = base.clone();
        short.commitment = "bc".repeat(16);
        assert_ne!(short.commitment, base.commitment);
        assert!(statement_signing_message(&short).is_err());

        let mut not_hex = base.clone();
        not_hex.authority_id = "zz".repeat(32);
        assert_ne!(not_hex.authority_id, base.authority_id);
        assert!(statement_signing_message(&not_hex).is_err());

        // The honest statement is still accepted — otherwise the three refusals
        // above would pass for a reason that has nothing to do with case or length.
        assert!(statement_signing_message(&base).is_ok());
    }

    /// A tampered signature, and a tampered field under an honest signature, both
    /// fail verification.
    #[test]
    fn verification_refuses_a_tampered_envelope() {
        let (secret, pin) = keypair();
        let signed = sign_slot_opening(&secret, &pin, &preview_for(statement())).expect("signs");

        let mut flipped = signed.envelope.clone();
        flipped.statement.slot += 1;
        assert_ne!(flipped.statement.slot, signed.envelope.statement.slot);
        assert!(verify_slot_opening(&pin, &flipped).is_err());

        let mut forged = signed.envelope.clone();
        forged.signature = crate::hex_encode(&[0u8; 64]);
        assert_ne!(forged.signature, signed.envelope.signature);
        assert!(verify_slot_opening(&pin, &forged).is_err());

        let other = dregg_types::SigningKey::from_bytes(&[9u8; 32]).public_key();
        assert!(verify_slot_opening(&other, &signed.envelope).is_err());
    }
}
