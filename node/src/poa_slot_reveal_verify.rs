//! **The player's check.** Verify, from two files and a curator key, that the
//! instance you were judged against was fixed before your session opened.
//!
//! # Why this is a subcommand and not a route
//!
//! The deliverable of the slot-close ceremony is not "the node did the right
//! thing". It is *a person who does not trust the operator can confirm it*. A check
//! the node performs and reports is worth nothing here: it is the node's claim
//! about the node. So this runs on the player's machine, opens no database, makes
//! no network request, and reads exactly three inputs:
//!
//! ```text
//! dregg-node poa-verify-slot-reveal \
//!     --curator-key <hex32>      # the trust anchor, obtained out of band
//!     --opening     retained.json  # POA-SLOT-OPENING-RECEIPT-1, saved BEFORE playing
//!     --reveal      reveal.json    # POA-SIGNAL-SLOT-REVEAL-1, fetched after slot close
//! ```
//!
//! # ⚠ The retained copy is the whole point
//!
//! Checking a secret against a commitment the same responder handed you at the same
//! moment proves only that the responder can do arithmetic. The ordering claim rests
//! entirely on `--opening` being a copy the player recorded **before** they played.
//! That is why `poa-web` now writes a `POA-SLOT-OPENING-RECEIPT-1` to durable storage
//! at the moment it verifies the curator signature, instead of — as it did until now
//! — verifying the signature and then discarding the signature.
//!
//! This tool cannot verify that a receipt is old. Nothing can, from the bytes alone:
//! a signed statement carries no timestamp and the curator could mint one at any
//! time. What it verifies is that the reveal opens *the commitment in your receipt*.
//! The freshness of the receipt is the player's own custody, and it is the strongest
//! link available without a third-party witness to when the opening was published.
//! Said plainly so nobody quotes this as more: **this closes ADAPTATION — the
//! operator could not change the instance in response to your play — and it does not
//! close the operator's advance KNOWLEDGE of it**, which every descriptor declares
//! as `operator_knows_instance: true`.
//!
//! # The curator key is the trust anchor and is therefore an explicit argument
//!
//! Every conclusion below is relative to `--curator-key`. Defaulting it to a value
//! read out of one of the documents would let whoever supplied the documents also
//! supply the key they are checked against, which verifies nothing. It is required,
//! and the verdict repeats it.

use std::path::Path;

use dregg_persist::PoaSlotOpeningStatementV1;
use ed25519_dalek::{Signature, VerifyingKey};
use serde::{Deserialize, Serialize};

/// Schema of the receipt a player retains before playing.
pub const OPENING_RECEIPT_SCHEMA_V1: &str = "POA-SLOT-OPENING-RECEIPT-1";
/// Format tag of the reveal document served after slot close.
pub const REVEAL_FORMAT_V1: &str = "POA-SIGNAL-SLOT-REVEAL-1";

const MAX_DOCUMENT_BYTES: u64 = 64 * 1024;

/// A refusal, with a stable machine-readable name.
///
/// The names are the contract: a caller scripting this must be able to tell "you
/// gave me the wrong file" from "the commitment was substituted" without parsing
/// prose. ⚠ A refusal is NEVER rendered as a verdict string a success could also
/// produce — `verify` returns `Result`, and the success arm carries a distinct
/// type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RevealRefusal {
    pub code: &'static str,
    pub detail: String,
}

impl std::fmt::Display for RevealRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "REFUSED [{}]: {}", self.code, self.detail)
    }
}

fn refuse(code: &'static str, detail: impl Into<String>) -> RevealRefusal {
    RevealRefusal {
        code,
        detail: detail.into(),
    }
}

/// The curator-signed statement, spelled exactly as
/// `PoaSlotOpeningStatementV1::signing_message` spells it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StatementDocument {
    pub schema: String,
    pub authority_id: String,
    pub mission_id: u64,
    pub slot: u64,
    pub commitment: String,
}

/// `POA-SLOT-OPENING-RECEIPT-1` — what a player keeps at session open.
///
/// `recorded_at` is the player's OWN note to themselves. It is unsigned and this
/// tool does not read it as evidence of anything; it exists so a player reading
/// their own file can tell which session it belongs to.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct OpeningReceiptDocument {
    pub schema: String,
    pub statement: StatementDocument,
    pub curator_key: String,
    pub signature: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub recorded_at: Option<String>,
}

/// The `opening` block of a reveal document.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RevealOpeningDocument {
    pub statement: StatementDocument,
    pub curator_key: String,
    pub signature: String,
}

/// `POA-SIGNAL-SLOT-REVEAL-1` — what the node serves once the slot is closed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RevealDocument {
    pub format: String,
    pub authority_id: String,
    pub slot: u64,
    pub state: String,
    pub open_slot: Option<u64>,
    pub opening: Option<RevealOpeningDocument>,
    pub slot_secret: Option<String>,
    pub consensus_finality: String,
}

/// What a successful verification established — each field a thing that was
/// CHECKED, not a thing that was read.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RevealVerdict {
    pub authority_id: String,
    pub mission_id: u64,
    pub slot: u64,
    /// The slot that superseded it, from the reveal document.
    pub closed_by_slot: u64,
    /// The commitment, identical in the retained receipt and the reveal, and
    /// re-derived from the published secret through Lean.
    pub commitment: String,
    /// The curator key the signature was verified against — the trust anchor the
    /// caller supplied.
    pub curator_key: String,
    /// Present only when `--player-key` was given: the run seed the revealed
    /// secret draws for that player, through the same Lean export the judge uses.
    pub run_seed: Option<String>,
    pub target: Option<String>,
}

/// The mission coordinates needed to reproduce one player's run seed.
///
/// All five are PUBLIC — they live in the curator-signed world artifact
/// (`poa/artifacts/*/world.json`) and the mission catalog — which is why a player
/// can supply them. The secret is the only private input and the reveal published
/// it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RunSeedQuery {
    pub player_key: [u8; 32],
    pub epoch: u64,
    pub federation_id: [u8; 32],
    pub content_session: [u8; 32],
}

fn parse_hex32(value: &str, field: &str) -> Result<[u8; 32], RevealRefusal> {
    if value.len() != 64
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(refuse(
            "malformed-hex",
            format!("{field} is not exactly 64 lowercase hex characters"),
        ));
    }
    let mut out = [0u8; 32];
    for (index, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&value[index * 2..index * 2 + 2], 16)
            .map_err(|_| refuse("malformed-hex", format!("{field} is not hex")))?;
    }
    Ok(out)
}

fn parse_hex64(value: &str, field: &str) -> Result<[u8; 64], RevealRefusal> {
    if value.len() != 128
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(refuse(
            "malformed-hex",
            format!("{field} is not exactly 128 lowercase hex characters"),
        ));
    }
    let mut out = [0u8; 64];
    for (index, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&value[index * 2..index * 2 + 2], 16)
            .map_err(|_| refuse("malformed-hex", format!("{field} is not hex")))?;
    }
    Ok(out)
}

fn hex(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(char::from_digit(u32::from(byte >> 4), 16).unwrap_or('0'));
        out.push(char::from_digit(u32::from(byte & 0x0f), 16).unwrap_or('0'));
    }
    out
}

/// Re-derive the canonical signed bytes from STRUCTURED fields and check the
/// curator signature over them.
///
/// ⚠ The bytes come from `PoaSlotOpeningStatementV1::signing_message`, the same
/// constructor the node prints and `poa-curator` independently mirrors. Nothing
/// here verifies a pre-encoded string a document supplied: a verifier handed
/// statement `S` beside a valid signature over `S'` would otherwise report `S` as
/// curator-signed.
fn verify_statement_signature(
    statement: &StatementDocument,
    curator_key: &str,
    signature: &str,
    pin: [u8; 32],
    which: &str,
) -> Result<[u8; 32], RevealRefusal> {
    if statement.schema != dregg_persist::POA_SLOT_OPENING_STATEMENT_SCHEMA_V1 {
        return Err(refuse(
            "foreign-schema",
            format!(
                "the {which} statement schema is {:?}, expected {}",
                statement.schema,
                dregg_persist::POA_SLOT_OPENING_STATEMENT_SCHEMA_V1
            ),
        ));
    }
    let named = parse_hex32(curator_key, &format!("{which}.curator_key"))?;
    if named != pin {
        return Err(refuse(
            "wrong-curator",
            format!(
                "the {which} names curator key {} but you pinned {}",
                hex(&named),
                hex(&pin)
            ),
        ));
    }
    let authority_id = parse_hex32(&statement.authority_id, &format!("{which}.authority_id"))?;
    let commitment = parse_hex32(&statement.commitment, &format!("{which}.commitment"))?;
    let rebuilt = PoaSlotOpeningStatementV1::new(
        authority_id,
        statement.mission_id,
        statement.slot,
        commitment,
    );
    let message = rebuilt.signing_message().map_err(|error| {
        refuse(
            "unencodable-statement",
            format!("cannot re-derive the {which} signing message: {error}"),
        )
    })?;
    let raw = parse_hex64(signature, &format!("{which}.signature"))?;
    let key = VerifyingKey::from_bytes(&pin).map_err(|_| {
        refuse(
            "wrong-curator",
            "the pinned curator key is not a valid Ed25519 key",
        )
    })?;
    key.verify_strict(&message, &Signature::from_bytes(&raw))
        .map_err(|_| {
            refuse(
                "signature-invalid",
                format!(
                    "the curator signature on the {which} does not verify over the statement it \
                     carries"
                ),
            )
        })?;
    Ok(commitment)
}

/// Ask Lean for `HiddenInstance.commit secret slot`, and — when a player is named
/// — for that player's run seed and target in the same call.
///
/// ⚠ No Rust arithmetic and no Rust fallback. Absent the linked export this
/// refuses; a verifier that recomputed the sponge with a second implementation
/// would be checking the operator's claim against its own guess.
fn derive_through_lean(
    secret: [u8; 32],
    slot: u64,
    mission_id: u64,
    query: Option<&RunSeedQuery>,
) -> Result<serde_json::Value, RevealRefusal> {
    let zero = [0u8; 32];
    let (player_key, epoch, federation_id, content_session) = match query {
        Some(q) => (q.player_key, q.epoch, q.federation_id, q.content_session),
        None => (zero, 0, zero, zero),
    };
    let wire = format!(
        "{{\"format\":\"{}\",\"slot\":{},\"secret\":\"{}\",\"mission_id\":{},\"epoch\":{},\
         \"federation_id\":\"{}\",\"content_session\":\"{}\",\"player_key\":\"{}\"}}",
        dregg_lean_ffi::poa_slot_derive_ffi::SLOT_DERIVE_INPUT_FORMAT,
        slot,
        hex(&secret),
        mission_id,
        epoch,
        hex(&federation_id),
        hex(&content_session),
        hex(&player_key),
    );
    let reply = dregg_lean_ffi::poa_slot_derive_ffi::derive_poa_slot_instance(&wire)
        .map_err(|error| {
            refuse(
                "lean-unavailable",
                format!("cannot reach the Lean slot derivation: {error}"),
            )
        })?
        .ok_or_else(|| {
            refuse(
                "lean-refused",
                "Lean refused to derive from this secret and slot",
            )
        })?;
    serde_json::from_str(&reply).map_err(|error| {
        refuse(
            "lean-unreadable",
            format!("the Lean derivation reply is not JSON: {error}"),
        )
    })
}

/// **THE CHECK.** Everything the ceremony promises, in the order a sceptic would
/// want it.
pub fn verify(
    pin: [u8; 32],
    receipt: &OpeningReceiptDocument,
    reveal: &RevealDocument,
    query: Option<&RunSeedQuery>,
) -> Result<RevealVerdict, RevealRefusal> {
    // (0) Both documents are the documents they say they are.
    if receipt.schema != OPENING_RECEIPT_SCHEMA_V1 {
        return Err(refuse(
            "foreign-schema",
            format!(
                "the retained opening is {:?}, expected {OPENING_RECEIPT_SCHEMA_V1}",
                receipt.schema
            ),
        ));
    }
    if reveal.format != REVEAL_FORMAT_V1 {
        return Err(refuse(
            "foreign-schema",
            format!(
                "the reveal document is {:?}, expected {REVEAL_FORMAT_V1}",
                reveal.format
            ),
        ));
    }

    // (1) The reveal must actually be a reveal. `still_open` and `unknown` are
    //     truthful answers and they are NOT verifications — refused by name so a
    //     script cannot mistake a withheld secret for a passed check.
    if reveal.state != "revealed" {
        return Err(refuse(
            "not-revealed",
            format!(
                "the node answered state={:?} for slot {} — it published no secret, so nothing \
                 here has been verified. A closed slot answers \"revealed\".",
                reveal.state, reveal.slot
            ),
        ));
    }
    let opening = reveal.opening.as_ref().ok_or_else(|| {
        refuse(
            "malformed-reveal",
            "the reveal claims state=revealed but carries no opening",
        )
    })?;
    let secret_hex = reveal.slot_secret.as_ref().ok_or_else(|| {
        refuse(
            "malformed-reveal",
            "the reveal claims state=revealed but carries no slot_secret",
        )
    })?;

    // (2) The two documents must be about the SAME slot of the SAME authority.
    if receipt.statement.slot != reveal.slot || receipt.statement.slot != opening.statement.slot {
        return Err(refuse(
            "slot-mismatch",
            format!(
                "your receipt is for slot {} but the reveal is for slot {}",
                receipt.statement.slot, reveal.slot
            ),
        ));
    }
    if receipt.statement.authority_id != opening.statement.authority_id
        || receipt.statement.authority_id != reveal.authority_id
    {
        return Err(refuse(
            "authority-mismatch",
            format!(
                "your receipt is for authority {} but the reveal is for {}",
                receipt.statement.authority_id, reveal.authority_id
            ),
        ));
    }
    if receipt.statement.mission_id != opening.statement.mission_id {
        return Err(refuse(
            "mission-mismatch",
            format!(
                "your receipt is for mission {} but the reveal is for {}",
                receipt.statement.mission_id, opening.statement.mission_id
            ),
        ));
    }

    // (3) ⚑ THE SUBSTITUTION CHECK. The commitment in the reveal must be the one
    //     you were shown before you played. This is the single comparison that
    //     makes the ordering claim; without a retained receipt there is nothing
    //     here but the node agreeing with itself.
    if receipt.statement.commitment != opening.statement.commitment {
        return Err(refuse(
            "commitment-substituted",
            format!(
                "the reveal opens commitment {} but the opening you retained before playing was \
                 {}. Your run was NOT judged against the instance you were shown.",
                opening.statement.commitment, receipt.statement.commitment
            ),
        ));
    }

    // (4) The curator signed it — checked on YOUR copy first, then on theirs, both
    //     against the pin you supplied, both over bytes re-derived here.
    let commitment = verify_statement_signature(
        &receipt.statement,
        &receipt.curator_key,
        &receipt.signature,
        pin,
        "retained opening",
    )?;
    let republished = verify_statement_signature(
        &opening.statement,
        &opening.curator_key,
        &opening.signature,
        pin,
        "republished opening",
    )?;
    if commitment != republished {
        return Err(refuse(
            "commitment-substituted",
            "the two openings verify but commit to different values",
        ));
    }

    // (5) ⚑ THE OPENING ITSELF, through Lean: does the published secret open the
    //     curator-signed commitment?
    let secret = parse_hex32(secret_hex, "reveal.slot_secret")?;
    let derived = derive_through_lean(secret, reveal.slot, receipt.statement.mission_id, query)?;
    let derived_commitment = derived
        .get("commitment")
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| {
            refuse(
                "lean-unreadable",
                "the Lean derivation reply carries no commitment",
            )
        })?;
    if derived_commitment != hex(&commitment) {
        return Err(refuse(
            "secret-does-not-open",
            format!(
                "the published secret commits to {derived_commitment}, not to the {} the curator \
                 signed. This secret is not the one that was committed.",
                hex(&commitment)
            ),
        ));
    }

    let (run_seed, target) = match query {
        Some(_) => (
            derived
                .get("run_seed")
                .and_then(serde_json::Value::as_str)
                .map(str::to_owned),
            derived
                .get("target")
                .and_then(serde_json::Value::as_str)
                .map(str::to_owned)
                .or_else(|| derived.get("target").map(|value| value.to_string())),
        ),
        None => (None, None),
    };

    Ok(RevealVerdict {
        authority_id: receipt.statement.authority_id.clone(),
        mission_id: receipt.statement.mission_id,
        slot: reveal.slot,
        closed_by_slot: reveal.open_slot.unwrap_or(reveal.slot),
        commitment: hex(&commitment),
        curator_key: hex(&pin),
        run_seed,
        target,
    })
}

fn load<T: serde::de::DeserializeOwned>(path: &Path, what: &str) -> Result<T, RevealRefusal> {
    let metadata = std::fs::metadata(path).map_err(|error| {
        refuse(
            "unreadable-input",
            format!("{what} is unavailable: {error}"),
        )
    })?;
    if !metadata.is_file() {
        return Err(refuse(
            "unreadable-input",
            format!("{what} is not a regular file"),
        ));
    }
    if metadata.len() == 0 || metadata.len() > MAX_DOCUMENT_BYTES {
        return Err(refuse(
            "unreadable-input",
            format!("{what} is empty or exceeds 64 KiB"),
        ));
    }
    let bytes = std::fs::read(path)
        .map_err(|error| refuse("unreadable-input", format!("{what} is unreadable: {error}")))?;
    serde_json::from_slice(&bytes).map_err(|error| {
        refuse(
            "unreadable-input",
            format!("{what} is not the exact document: {error}"),
        )
    })
}

/// Arguments of `dregg-node poa-verify-slot-reveal`.
#[derive(Clone, Debug)]
pub struct VerifyArgs {
    pub curator_key: String,
    pub opening: std::path::PathBuf,
    pub reveal: std::path::PathBuf,
    pub player_key: Option<String>,
    pub epoch: Option<u64>,
    pub federation_id: Option<String>,
    pub content_session: Option<String>,
}

/// Drive the check from the command line and render a verdict.
pub fn run(args: &VerifyArgs) -> Result<String, String> {
    let pin = parse_hex32(&args.curator_key, "--curator-key").map_err(|error| error.to_string())?;
    let receipt: OpeningReceiptDocument =
        load(&args.opening, "the retained slot opening").map_err(|error| error.to_string())?;
    let reveal: RevealDocument =
        load(&args.reveal, "the slot reveal").map_err(|error| error.to_string())?;

    // The run-seed extension is all-or-nothing: three of the four coordinates
    // would silently derive a DIFFERENT player's seed, which is worse than
    // refusing.
    let supplied = [
        args.player_key.is_some(),
        args.epoch.is_some(),
        args.federation_id.is_some(),
        args.content_session.is_some(),
    ];
    let query = if supplied.iter().all(|present| *present) {
        Some(RunSeedQuery {
            player_key: parse_hex32(
                args.player_key.as_deref().unwrap_or_default(),
                "--player-key",
            )
            .map_err(|error| error.to_string())?,
            epoch: args.epoch.unwrap_or_default(),
            federation_id: parse_hex32(
                args.federation_id.as_deref().unwrap_or_default(),
                "--federation-id",
            )
            .map_err(|error| error.to_string())?,
            content_session: parse_hex32(
                args.content_session.as_deref().unwrap_or_default(),
                "--content-session",
            )
            .map_err(|error| error.to_string())?,
        })
    } else if supplied.iter().any(|present| *present) {
        return Err(
            "REFUSED [incomplete-run-seed-query]: reproducing your run seed needs ALL of \
             --player-key, --epoch, --federation-id and --content-session. With a subset it \
             would derive some OTHER run's seed and report it as yours."
                .to_owned(),
        );
    } else {
        None
    };

    let verdict =
        verify(pin, &receipt, &reveal, query.as_ref()).map_err(|error| error.to_string())?;
    let mut out = String::new();
    out.push_str(
        "VERIFIED — the instance you were judged against was fixed before you played.\n\n",
    );
    out.push_str(&format!("  authority     {}\n", verdict.authority_id));
    out.push_str(&format!("  mission       {}\n", verdict.mission_id));
    out.push_str(&format!(
        "  slot          {} (closed by slot {})\n",
        verdict.slot, verdict.closed_by_slot
    ));
    out.push_str(&format!("  commitment    {}\n", verdict.commitment));
    out.push_str(&format!("  curator key   {}\n", verdict.curator_key));
    if let Some(seed) = &verdict.run_seed {
        out.push_str(&format!("  your run seed {seed}\n"));
    }
    if let Some(target) = &verdict.target {
        out.push_str(&format!("  your target   {target}\n"));
    }
    out.push_str(
        "\nWhat this establishes: the commitment in the opening you retained BEFORE playing is \
         opened by the secret published after the slot closed, and the curator signed that \
         commitment under the key you pinned. The instance could not have been adapted to your \
         play.\n\
         \nWhat it does NOT establish: that the operator did not know the instance in advance. \
         They did — every descriptor declares `operator_knows_instance: true`. Closing that needs \
         a beacon feeding the slot secret, and there is none.\n",
    );
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ed25519_dalek::{Signer as _, SigningKey};

    const AUTHORITY: [u8; 32] = [0xa4; 32];
    const MISSION_ID: u64 = 1;
    const SLOT: u64 = 9;
    const SECRET: [u8; 32] = [0x5c; 32];
    const OTHER_SECRET: [u8; 32] = [0x7e; 32];

    fn curator() -> SigningKey {
        SigningKey::from_bytes(&[0xc0; 32])
    }

    fn require_lean() {
        assert!(
            dregg_lean_ffi::poa_slot_derive_ffi::poa_slot_derive_available(),
            "these tests require the linked Lean slot-derivation export; without it the \
             commitment check below would never run and the suite would be green for a \
             verifier that verifies nothing"
        );
    }

    /// A REAL commitment, through Lean. Only the tests that actually exercise the
    /// sponge step call this.
    fn commitment_for(secret: [u8; 32], slot: u64) -> [u8; 32] {
        crate::poa_signal_slot_ceremony::derive_commitment(secret, slot)
            .expect("Lean must derive the commitment")
    }

    /// ⚑ **A commitment-SHAPED constant, and deliberately not a real commitment.**
    ///
    /// Every refusal in [`verify`] except `secret-does-not-open` is decided BEFORE
    /// the Lean call — they are about document shape, coordinate agreement, byte
    /// equality of the commitment, and Ed25519. Deriving real commitments for those
    /// tests would make the highest-stakes checks in this file — "was the
    /// commitment you were shown substituted?" — unrunnable whenever the Lean
    /// archive is unavailable, which is exactly when someone is most likely to
    /// wave a red suite through.
    ///
    /// So the refusal poles use constants and assert the refusal fires before the
    /// sponge is ever consulted. The POSITIVE pole cannot: it must use a real
    /// commitment a real secret really opens, and it is gated on `require_lean`.
    fn opaque_commitment(tag: u8) -> [u8; 32] {
        [tag; 32]
    }

    fn statement_for(commitment: [u8; 32], slot: u64) -> StatementDocument {
        StatementDocument {
            schema: dregg_persist::POA_SLOT_OPENING_STATEMENT_SCHEMA_V1.to_owned(),
            authority_id: hex(&AUTHORITY),
            mission_id: MISSION_ID,
            slot,
            commitment: hex(&commitment),
        }
    }

    fn sign(statement: &StatementDocument) -> String {
        let rebuilt = PoaSlotOpeningStatementV1::new(
            AUTHORITY,
            statement.mission_id,
            statement.slot,
            parse_hex32(&statement.commitment, "commitment").expect("hex"),
        );
        let message = rebuilt.signing_message().expect("signing message");
        hex(&curator().sign(&message).to_bytes())
    }

    fn receipt_for(statement: StatementDocument) -> OpeningReceiptDocument {
        let signature = sign(&statement);
        OpeningReceiptDocument {
            schema: OPENING_RECEIPT_SCHEMA_V1.to_owned(),
            statement,
            curator_key: hex(&curator().verifying_key().to_bytes()),
            signature,
            recorded_at: Some("2026-08-09T00:00:00Z".to_owned()),
        }
    }

    fn reveal_for(statement: StatementDocument, secret: [u8; 32]) -> RevealDocument {
        let signature = sign(&statement);
        RevealDocument {
            format: REVEAL_FORMAT_V1.to_owned(),
            authority_id: hex(&AUTHORITY),
            slot: statement.slot,
            state: "revealed".to_owned(),
            open_slot: Some(statement.slot + 1),
            opening: Some(RevealOpeningDocument {
                statement,
                curator_key: hex(&curator().verifying_key().to_bytes()),
                signature,
            }),
            slot_secret: Some(hex(&secret)),
            consensus_finality: "not_asserted_by_this_view".to_owned(),
        }
    }

    fn pin() -> [u8; 32] {
        curator().verifying_key().to_bytes()
    }

    /// ⚑ **POLE ONE — the honest ceremony verifies.**
    #[test]
    fn a_legitimate_reveal_verifies_against_the_retained_opening() {
        require_lean();
        let commitment = commitment_for(SECRET, SLOT);
        let receipt = receipt_for(statement_for(commitment, SLOT));
        let reveal = reveal_for(statement_for(commitment, SLOT), SECRET);

        let verdict = verify(pin(), &receipt, &reveal, None).expect("the honest ceremony verifies");
        assert_eq!(verdict.slot, SLOT);
        assert_eq!(verdict.commitment, hex(&commitment));
        assert_eq!(verdict.closed_by_slot, SLOT + 1);
        assert_eq!(verdict.curator_key, hex(&pin()));
        assert!(verdict.run_seed.is_none(), "no player key was supplied");
    }

    /// ⚑ **POLE TWO(a) — A SWAPPED COMMITMENT IS REFUSED BY NAME.**
    ///
    /// The operator reveals a slot whose commitment is not the one the player was
    /// shown: the classic "we committed to something — just not to that" swap. This
    /// is the single most important refusal in the file, because it is the one that
    /// carries the ordering claim.
    ///
    /// The hostile reveal is built CONSTRUCTIVELY and is otherwise IMPECCABLE: the
    /// curator really signed it, its statement is internally consistent, and its
    /// signature really verifies over its own bytes (asserted below). It is refused
    /// for exactly one reason — it is not the commitment the player retained.
    ///
    /// No Lean: the refusal fires at step (3), before the sponge is consulted.
    #[test]
    fn a_commitment_swapped_after_the_session_is_refused_by_name() {
        let honest = opaque_commitment(0xaa);
        let other = opaque_commitment(0xbb);
        assert_ne!(
            honest, other,
            "the two commitments must differ, or the swap below is a no-op"
        );

        let receipt = receipt_for(statement_for(honest, SLOT));
        let reveal = reveal_for(statement_for(other, SLOT), SECRET);
        let served = reveal.opening.as_ref().expect("opening");
        assert_ne!(
            served.statement.commitment, receipt.statement.commitment,
            "the mutation must actually change the commitment, or this asserts nothing"
        );

        // The hostile document is NOT merely malformed: its curator signature is
        // genuine over its own statement. Without this the refusal below could be
        // passing for the wrong reason.
        let rebuilt = PoaSlotOpeningStatementV1::new(AUTHORITY, MISSION_ID, SLOT, other);
        let message = rebuilt.signing_message().expect("signing message");
        let mut raw = [0u8; 64];
        for (index, byte) in raw.iter_mut().enumerate() {
            *byte = u8::from_str_radix(&served.signature[index * 2..index * 2 + 2], 16)
                .expect("lowercase hex");
        }
        assert!(
            curator()
                .verifying_key()
                .verify_strict(&message, &ed25519_dalek::Signature::from_bytes(&raw))
                .is_ok(),
            "the hostile reveal must carry a genuine curator signature over its own \
             statement, or this test proves only that broken documents are refused"
        );

        let error = verify(pin(), &receipt, &reveal, None).expect_err("must refuse");
        assert_eq!(error.code, "commitment-substituted", "{error}");
    }

    /// ⚑ **POLE TWO(b) — A SECRET THAT DOES NOT OPEN THE COMMITMENT IS REFUSED.**
    ///
    /// The reveal keeps the honest, curator-signed commitment but publishes a
    /// different secret — an operator who committed to instance A, served instance
    /// B, and now needs the reveal to say B.
    #[test]
    fn a_secret_that_does_not_open_the_commitment_is_refused_by_name() {
        require_lean();
        let commitment = commitment_for(SECRET, SLOT);
        let receipt = receipt_for(statement_for(commitment, SLOT));
        let mut reveal = reveal_for(statement_for(commitment, SLOT), SECRET);

        let honest_secret = reveal.slot_secret.clone().expect("a secret");
        reveal.slot_secret = Some(hex(&OTHER_SECRET));
        assert_ne!(
            reveal.slot_secret.as_deref(),
            Some(honest_secret.as_str()),
            "the mutation must actually change the secret, or this asserts nothing"
        );

        let error = verify(pin(), &receipt, &reveal, None).expect_err("must refuse");
        assert_eq!(error.code, "secret-does-not-open", "{error}");
    }

    /// ⚑ **POLE TWO(c) — A WITHHELD SECRET IS NOT A PASS.**
    ///
    /// `still_open` is a truthful answer and it verifies NOTHING. The refusal must
    /// be by name so no script reads a 200-shaped document as a completed check.
    /// This is the failure mode the repo has hit before: a refusal that renders as
    /// the expected verdict.
    #[test]
    fn a_still_open_or_unknown_reveal_is_refused_rather_than_passed() {
        let commitment = opaque_commitment(0xaa);
        let receipt = receipt_for(statement_for(commitment, SLOT));

        for state in ["still_open", "unknown"] {
            let withheld = RevealDocument {
                format: REVEAL_FORMAT_V1.to_owned(),
                authority_id: hex(&AUTHORITY),
                slot: SLOT,
                state: state.to_owned(),
                open_slot: Some(SLOT),
                opening: None,
                slot_secret: None,
                consensus_finality: "not_asserted_by_this_view".to_owned(),
            };
            let error = verify(pin(), &receipt, &withheld, None).expect_err("must refuse");
            assert_eq!(error.code, "not-revealed", "state {state}: {error}");
        }
    }

    /// ⚑ **POLE TWO(d) — A FORGED CURATOR IS REFUSED.**
    ///
    /// A whole ceremony minted under a different key: internally perfect, and
    /// worthless. Both the receipt's and the reveal's signatures must be checked
    /// against the pin the PLAYER supplied, never against a key the documents name.
    #[test]
    fn a_ceremony_minted_under_another_key_is_refused_by_name() {
        let commitment = opaque_commitment(0xaa);
        let receipt = receipt_for(statement_for(commitment, SLOT));
        let reveal = reveal_for(statement_for(commitment, SLOT), SECRET);

        let impostor = SigningKey::from_bytes(&[0x11; 32])
            .verifying_key()
            .to_bytes();
        assert_ne!(impostor, pin(), "the impostor must be a different key");

        let error = verify(impostor, &receipt, &reveal, None).expect_err("must refuse");
        assert_eq!(error.code, "wrong-curator", "{error}");

        // And the honest pin still passes, or the refusal above would be for a
        // reason unrelated to the key.
        assert!(verify(pin(), &receipt, &reveal, None).is_ok());
    }

    /// A tampered signature over an otherwise-honest statement is refused.
    #[test]
    fn a_tampered_signature_is_refused_by_name() {
        let commitment = opaque_commitment(0xaa);
        let mut receipt = receipt_for(statement_for(commitment, SLOT));
        let reveal = reveal_for(statement_for(commitment, SLOT), SECRET);

        let honest = receipt.signature.clone();
        receipt.signature = hex(&[0u8; 64]);
        assert_ne!(receipt.signature, honest, "the mutation must change it");

        let error = verify(pin(), &receipt, &reveal, None).expect_err("must refuse");
        assert_eq!(error.code, "signature-invalid", "{error}");
    }

    /// A reveal for a different slot than the one the player holds a receipt for.
    #[test]
    fn a_reveal_of_another_slot_is_refused_by_name() {
        let mine = opaque_commitment(0xaa);
        let theirs = opaque_commitment(0xbb);
        let receipt = receipt_for(statement_for(mine, SLOT));
        let reveal = reveal_for(statement_for(theirs, SLOT + 5), SECRET);
        assert_ne!(reveal.slot, receipt.statement.slot);

        let error = verify(pin(), &receipt, &reveal, None).expect_err("must refuse");
        assert_eq!(error.code, "slot-mismatch", "{error}");
    }

    /// With a full player query the verdict carries the run seed, and a DIFFERENT
    /// player key draws a different one — so the seed reported is genuinely the
    /// caller's, not a constant.
    #[test]
    fn a_named_player_gets_their_own_run_seed() {
        require_lean();
        let commitment = commitment_for(SECRET, SLOT);
        let receipt = receipt_for(statement_for(commitment, SLOT));
        let reveal = reveal_for(statement_for(commitment, SLOT), SECRET);

        let mine = RunSeedQuery {
            player_key: [0x31; 32],
            epoch: 2,
            federation_id: AUTHORITY,
            content_session: [0x44; 32],
        };
        let theirs = RunSeedQuery {
            player_key: [0x32; 32],
            ..mine.clone()
        };
        assert_ne!(mine.player_key, theirs.player_key);

        let a = verify(pin(), &receipt, &reveal, Some(&mine)).expect("verifies");
        let b = verify(pin(), &receipt, &reveal, Some(&theirs)).expect("verifies");
        let seed_a = a.run_seed.expect("a run seed for a named player");
        let seed_b = b.run_seed.expect("a run seed for a named player");
        assert_ne!(
            seed_a, seed_b,
            "two players in one slot must draw different run seeds, or the reported seed is \
             not the caller's"
        );
        // The commitment is player-independent even though the seed is not.
        assert_eq!(a.commitment, b.commitment);
    }
}
