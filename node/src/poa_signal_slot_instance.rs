//! Step 4 of the Path of Angels first-turn ceremony: derive the live instance
//! this slot draws for one player.
//!
//! # ⚠ THIS COMMAND PRINTS THE ANSWER
//!
//! Signal is a deduction game. The run seed — and therefore the solving code — is
//! `HiddenInstance.runSeedFor ⟨secret, slot, playerKey⟩ ctx`, so anyone holding the
//! curator's slot secret can compute the target for any player. That is not a leak:
//! holding the secret is what knowing the instance MEANS, and the node must hold it
//! to judge. What WOULD be a leak is any surface that computes it for a caller who
//! holds nothing.
//!
//! So this is an **operator/curator subcommand against a STOPPED node**, exactly
//! like `poa-slot-opening-preview` and `init-poa-signal-slot`:
//!
//! * it opens the node's own `dregg.redb`, which redb serves single-writer — a
//!   running node holds that lock, so this physically cannot be run against a live
//!   node's store, let alone from inside its process;
//! * it takes the slot secret from a FILE, and refuses unless that secret is
//!   byte-identical to the one the ceremony installed;
//! * `the_operator_derivation_is_unreachable_from_any_router` below fails if any
//!   route-defining module in this crate so much as names the derivation symbols.
//!
//! It is deliberately NOT on the unauthenticated-surface pin: that pin enumerates
//! HTTP routes, and adding a subcommand to it would assert this is one.
//!
//! # The ceremony, whole
//!
//! ```text
//! 0. the curator draws a 32-byte slot secret OFF-LINE          (curator, no node)
//! 1. dregg-node poa-slot-opening-preview …  → commitment + the exact signing message
//! 2. poa-curator sign-slot-opening …        → slot-opening.json     (CURATOR KEY)
//! 3. dregg-node init-poa-signal-slot …      → verify, then install    (node STOPPED)
//! 4. dregg-node poa-signal-instance-preview → THE TARGET               (node STOPPED)
//! 5. dregg-node poa-signal-submit-claim …   → POST the solved carrier   (node RUNNING)
//! 6. GET /status                            → latest_height 0 → 1
//! ```
//!
//! # What this refuses
//!
//! * a data directory with no PoA Signal head (nothing to derive against);
//! * an authority with no OPEN slot;
//! * coordinates (`--mission-id`, `--slot`) that do not name the installed slot;
//! * a `--secret-file` that is not the installed secret — an operator deriving
//!   against the wrong secret would get a code the judge refuses, and read that as
//!   a broken judge;
//! * a Lean archive without the slot-derivation export. There is no Rust fallback.

use std::fs;
use std::path::{Path, PathBuf};

use dregg_persist::PersistentStore;
use serde::{Deserialize, Serialize};

/// Schema of the document this command emits.
pub const INSTANCE_PREVIEW_SCHEMA: &str = "POA-SIGNAL-INSTANCE-PREVIEW-V1";

/// Inputs to the operator-only instance derivation.
#[derive(Clone, Debug)]
pub struct PoaSignalInstancePreviewArgs {
    /// Existing PoA node data directory (the one holding `dregg.redb`).
    pub data_dir: PathBuf,
    /// Federation id of the Signal authority, 64 lowercase hex.
    pub authority_id: String,
    /// Mission the open slot must name.
    pub mission_id: u64,
    /// The open slot.
    pub slot: u64,
    /// File holding the curator's 32-byte slot secret as 64 lowercase hex.
    ///
    /// ⚠ Key material. Read, compared, and never echoed.
    pub secret_file: PathBuf,
    /// The player's Ed25519 public key, 64 lowercase hex. The instance is
    /// per-player: a code derived for one key solves nothing for another.
    pub player_key: String,
}

/// The emitted document. It is BOTH the operator's readable answer and the exact
/// input `poa-signal-submit-claim --claim-file` consumes, so the code never has to
/// be retyped onto a command line (where it would land in shell history and in
/// every process listing on the box).
///
/// The run seed is deliberately NOT rendered. It is a second equally-revealing
/// value with no operator use: the claim carries the code, not the seed.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct InstancePreviewDocument {
    pub schema: String,
    pub authority_id: String,
    pub slot: u64,
    pub player_key: String,
    /// The commitment the curator published for this slot, re-derived by Lean
    /// during this derivation and equal to the installed one (the derivation
    /// refuses otherwise). Printed so an operator can check one number against the
    /// signed opening without touching the secret again.
    pub slot_commitment: String,
    pub claim: ClaimDocument,
}

/// The solving claim, in the shape `poa-signal-submit-claim` reads.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ClaimDocument {
    pub mission_id: u64,
    pub code: CodeDocument,
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CodeDocument {
    pub low: u8,
    pub mid: u8,
    pub high: u8,
}

/// Step 4: ask Lean which instance this installed slot draws for this player.
///
/// ⚠ Operator-only. See the module docblock.
pub fn preview_poa_signal_instance(args: &PoaSignalInstancePreviewArgs) -> Result<String, String> {
    let authority_id = parse_hex32(&args.authority_id, "authority_id")?;
    let player_key = parse_hex32(&args.player_key, "player_key")?;
    let secret = read_secret(&args.secret_file)?;

    let store = PersistentStore::open(&args.data_dir.join("dregg.redb"))
        .map_err(|error| format!("cannot open the PoA node store: {error}"))?;
    let head = store
        .load_poa_signal_head(authority_id)
        .map_err(|error| format!("cannot read the PoA Signal head: {error}"))?
        .ok_or_else(|| {
            "this data directory carries no PoA Signal head for that authority; run \
             `dregg-node init-poa-signal` first"
                .to_owned()
        })?;
    let slot = store
        .load_poa_signal_open_slot_v1(authority_id)
        .map_err(|error| format!("cannot read the open PoA Signal slot: {error}"))?
        .ok_or_else(|| {
            "this authority has no OPEN slot; run the three-step slot ceremony \
             (`poa-slot-opening-preview` → `poa-curator sign-slot-opening` → \
             `init-poa-signal-slot`) first"
                .to_owned()
        })?;

    if slot.slot() != args.slot || slot.mission_id() != args.mission_id {
        return Err(format!(
            "the open slot is mission {} slot {}, not the mission {} slot {} this command was given",
            slot.mission_id(),
            slot.slot(),
            args.mission_id,
            args.slot,
        ));
    }
    // The operator must present the SAME secret the ceremony installed. Deriving
    // against a different one yields a legal-looking code that the judge refuses,
    // and an operator reading `LeanRejected` would reasonably suspect the judge
    // rather than their own file.
    if slot.secret() != secret {
        return Err(
            "the secret in --secret-file is not the secret installed for this slot".to_owned(),
        );
    }

    // `actor_root` is the executor receipt's pre-state hash on the judging path;
    // it is NOT part of the pinned `POA-SLOT-DERIVE-1` wire, so the derivation is
    // independent of it and a preview passes zero rather than inventing one.
    let instance = crate::poa_signal_adapter::derive_operator_instance(
        &head,
        &slot,
        authority_id,
        player_key,
        [0u8; 32],
    )
    .map_err(|error| format!("PoA Signal instance derivation refused: {error}"))?;

    let document = InstancePreviewDocument {
        schema: INSTANCE_PREVIEW_SCHEMA.to_owned(),
        authority_id: hex(&authority_id),
        slot: instance.slot,
        player_key: hex(&player_key),
        slot_commitment: hex(&slot.commitment()),
        claim: ClaimDocument {
            mission_id: instance.mission_id,
            code: CodeDocument {
                low: instance.target.low(),
                mid: instance.target.mid(),
                high: instance.target.high(),
            },
        },
    };
    serde_json::to_string_pretty(&document)
        .map_err(|error| format!("cannot encode the instance preview: {error}"))
}

/// Load a claim from an emitted [`InstancePreviewDocument`].
pub fn load_claim_document(path: &Path) -> Result<ClaimDocument, String> {
    let raw = fs::read_to_string(path)
        .map_err(|error| format!("cannot read {}: {error}", path.display()))?;
    let document: InstancePreviewDocument = serde_json::from_str(&raw)
        .map_err(|error| format!("{} is not an instance preview: {error}", path.display()))?;
    if document.schema != INSTANCE_PREVIEW_SCHEMA {
        return Err(format!(
            "{} has schema {:?}, expected {INSTANCE_PREVIEW_SCHEMA}",
            path.display(),
            document.schema
        ));
    }
    Ok(document.claim)
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

pub(crate) fn parse_hex32(value: &str, label: &str) -> Result<[u8; 32], String> {
    if value.len() != 64
        || !value
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err(format!(
            "{label} must be exactly 64 lowercase hex characters"
        ));
    }
    let mut out = [0u8; 32];
    for (index, byte) in out.iter_mut().enumerate() {
        *byte = u8::from_str_radix(&value[index * 2..index * 2 + 2], 16)
            .map_err(|_| format!("{label} is not hex"))?;
    }
    Ok(out)
}

pub(crate) fn hex(bytes: &[u8]) -> String {
    dregg_types::hex_encode(bytes)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// EVERY module in this crate that defines an axum route, verbatim.
    ///
    /// `include_str!` rather than a runtime read: a file that moved or was renamed
    /// must break the BUILD, not silently shrink the set this gate scans. A
    /// fail-open surface gate is worth less than none, because it reads as
    /// coverage.
    const ROUTE_DEFINING_SOURCES: &[(&str, &str)] = &[
        ("api.rs", include_str!("api.rs")),
        ("channels_service.rs", include_str!("channels_service.rs")),
        (
            "dark_clearing_service.rs",
            include_str!("dark_clearing_service.rs"),
        ),
        ("dkg_service.rs", include_str!("dkg_service.rs")),
        (
            "equivocation_court_service.rs",
            include_str!("equivocation_court_service.rs"),
        ),
        ("poa_galley_api.rs", include_str!("poa_galley_api.rs")),
        (
            "poa_signal_authority_export.rs",
            include_str!("poa_signal_authority_export.rs"),
        ),
        ("poa_records_api.rs", include_str!("poa_records_api.rs")),
        ("poa_holding_api.rs", include_str!("poa_holding_api.rs")),
        (
            "poa_signal_session.rs",
            include_str!("poa_signal_session.rs"),
        ),
        (
            "poa_signal_slot_api.rs",
            include_str!("poa_signal_slot_api.rs"),
        ),
        ("poa_station_api.rs", include_str!("poa_station_api.rs")),
        (
            "private_dependent_turns.rs",
            include_str!("private_dependent_turns.rs"),
        ),
        ("relay_service.rs", include_str!("relay_service.rs")),
        ("realm_service.rs", include_str!("realm_service.rs")),
        ("storage_service.rs", include_str!("storage_service.rs")),
        ("trustline_service.rs", include_str!("trustline_service.rs")),
    ];

    /// THE ANSWER MUST NOT BE SERVABLE.
    ///
    /// Deriving the instance is the one operation in the Signal stack that turns
    /// the node's private slot secret into the puzzle's solution. Anything that can
    /// be reached over HTTP eventually is, so the gate is not "no route calls it
    /// today" but "no route-defining module NAMES it". A handler cannot call a
    /// function it does not mention, and the day someone adds `derive_operator_
    /// instance` to a handler this test names the file.
    ///
    /// ⚠ This is a NAME gate, and it is honest about its reach: a caller could
    /// still route around it by re-deriving through `evaluate_signal_claim`'s
    /// private path, which is why the derivation lives behind a store the running
    /// node holds a single-writer lock on. The two together are the boundary; this
    /// one is the part that can go red in CI.
    #[test]
    fn the_operator_derivation_is_unreachable_from_any_router() {
        const FORBIDDEN: &[&str] = &[
            "derive_operator_instance",
            "OperatorDerivedInstance",
            "preview_poa_signal_instance",
            "poa_signal_slot_instance",
        ];
        let mut found = Vec::new();
        for (name, source) in ROUTE_DEFINING_SOURCES {
            for symbol in FORBIDDEN {
                if source.contains(symbol) {
                    found.push(format!("{name} names {symbol}"));
                }
            }
        }
        assert!(
            found.is_empty(),
            "the operator-only instance derivation reached an HTTP surface: {found:?}. \
             This command prints the Signal puzzle's ANSWER; a route that computes it \
             for a caller who holds no slot secret ends the deduction game."
        );
    }

    /// The gate can go red. If `ROUTE_DEFINING_SOURCES` ever silently emptied — a
    /// refactor, a bad merge — the test above would pass over nothing and report
    /// coverage it does not have.
    #[test]
    fn the_unreachability_gate_actually_scans_the_routers() {
        assert!(
            ROUTE_DEFINING_SOURCES.len() >= 16,
            "the surface set shrank; a name gate over fewer routers is a weaker gate"
        );
        for (name, source) in ROUTE_DEFINING_SOURCES {
            assert!(
                source.contains(".route(") || source.contains("Router::new"),
                "{name} is in the surface set but defines no axum route — either it \
                 stopped being a router (drop it) or the set is scanning the wrong file"
            );
            // The scan reads real bytes, not an empty string.
            assert!(source.len() > 1_000, "{name} is implausibly short");
        }
    }

    #[test]
    fn a_short_or_uppercase_secret_is_refused() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("secret.hex");
        fs::write(&path, "abcd").unwrap();
        assert!(read_secret(&path).unwrap_err().contains("64 lowercase hex"));

        fs::write(&path, "AB".repeat(32)).unwrap();
        assert!(read_secret(&path).is_err());

        fs::write(&path, format!("{}\n", "ab".repeat(32))).unwrap();
        assert_eq!(read_secret(&path).unwrap(), [0xab; 32]);
    }

    /// A data directory with no PoA head refuses with an operator-actionable
    /// message rather than deriving against nothing.
    #[test]
    fn a_directory_without_a_signal_head_refuses() {
        let dir = tempfile::tempdir().unwrap();
        let data_dir = dir.path().join("node-0");
        fs::create_dir_all(&data_dir).unwrap();
        let secret_file = dir.path().join("slot.secret");
        fs::write(&secret_file, "77".repeat(32)).unwrap();

        let error = preview_poa_signal_instance(&PoaSignalInstancePreviewArgs {
            data_dir,
            authority_id: "a4".repeat(32),
            mission_id: 1,
            slot: 9,
            secret_file,
            player_key: "c7".repeat(32),
        })
        .expect_err("no head means no derivation");
        assert!(error.contains("no PoA Signal head"), "unexpected: {error}");
    }

    /// The emitted document round-trips into the claim the submitter consumes.
    /// These are two commands joined by a file; if the shapes drift, the operator
    /// discovers it mid-ceremony.
    #[test]
    fn the_preview_document_is_the_submitter_s_claim_input() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("instance.json");
        let document = InstancePreviewDocument {
            schema: INSTANCE_PREVIEW_SCHEMA.to_owned(),
            authority_id: "a4".repeat(32),
            slot: 9,
            player_key: "c7".repeat(32),
            slot_commitment: "bc".repeat(32),
            claim: ClaimDocument {
                mission_id: 1,
                code: CodeDocument {
                    low: 5,
                    mid: 0,
                    high: 3,
                },
            },
        };
        fs::write(&path, serde_json::to_vec_pretty(&document).unwrap()).unwrap();
        let claim = load_claim_document(&path).expect("the preview is a claim input");
        assert_eq!(claim.mission_id, 1);
        assert_eq!((claim.code.low, claim.code.mid, claim.code.high), (5, 0, 3));

        fs::write(&path, br#"{"schema":"SOMETHING-ELSE"}"#).unwrap();
        assert!(load_claim_document(&path).is_err());
    }
}
