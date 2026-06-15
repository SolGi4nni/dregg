//! CapTP client: the bot's own identity and capability session management.
//!
//! The bot IS a dregg participant — it has its own keypair, holds live references,
//! and tracks sturdy refs it has locally exported or accepted. The dregg node does
//! not currently serve `/captp/export`, `/captp/enliven`, `/captp/handoff`, or
//! `/captp/revoke`; this client must not pretend those HTTP endpoints exist.
//!
//! Handoffs are Discord-mediated local records: the bot stores a bearer token,
//! recipient identity, sturdy ref, and local signature through the bot database.
//! Redeeming the token enlivens the same sturdy ref for the intended recipient.

use std::io::Read;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::db::{CaptpExportRecord, CaptpHeldRecord, CaptpLocalHandoffRecord, Database};
use dregg_captp::FederationId as GroupId;
use dregg_captp::uri::DreggUri;
use dregg_types::CellId;
use serde::{Deserialize, Serialize};
// The REAL `dregg://` web-of-cells verified attested resolve — the genuine
// "enliven" for a published web-of-cells cell (the local analogue of dialing the
// node + enlivening the swiss). Distinct from `dregg_captp::uri::DreggUri` (which
// carries a swiss number); the web-of-cells ref is keyed on the content-addressed
// cell id.
use starbridge_web_surface::web_of_cells::{DreggUri as WocUri, WebOfCells};
use tracing::info;

/// A held capability reference with metadata.
#[derive(Debug, Clone)]
pub struct HeldCapability {
    /// The URI of this capability (sturdy ref form).
    pub uri: DreggUri,
    /// Human-readable label (optional).
    pub label: Option<String>,
    /// Who shared this with us (Discord user ID, if applicable).
    pub shared_by: Option<u64>,
    /// When we acquired this cap.
    pub acquired_at: u64,
    /// Whether this cap is currently live (enlivened).
    pub live: bool,
}

/// A capability we have exported (shared with someone).
#[derive(Debug, Clone)]
pub struct ExportedCapability {
    /// The cell ID we exported.
    pub cell_id: String,
    /// The dregg URI the recipient can use.
    pub uri: DreggUri,
    /// Who we shared it with (Discord user ID).
    pub shared_with: Option<u64>,
    /// When we exported it.
    pub exported_at: u64,
    /// Whether it's been revoked.
    pub revoked: bool,
}

/// Status of a Discord-mediated CapTP handoff token.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum HandoffStatus {
    /// Token has been minted and can be redeemed by the recipient identity.
    Pending,
    /// Token has already been redeemed.
    Redeemed,
    /// Source capability was revoked before redemption.
    Revoked,
}

impl HandoffStatus {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Pending => "pending",
            Self::Redeemed => "redeemed",
            Self::Revoked => "revoked",
        }
    }

    fn from_str(value: &str) -> Option<Self> {
        match value {
            "pending" => Some(Self::Pending),
            "redeemed" => Some(Self::Redeemed),
            "revoked" => Some(Self::Revoked),
            _ => None,
        }
    }
}

/// A persistent local handoff record.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HandoffRecord {
    /// Bearer token presented to `/cap-accept`.
    pub token: String,
    /// Cell ID being handed off.
    pub cell_id: String,
    /// Sturdy ref being handed off.
    pub uri: String,
    /// Recipient cell/public identity bound by Discord identity lookup.
    pub recipient_key: String,
    /// Bot-local signature binding token, cell, recipient, and URI.
    pub local_signature: String,
    /// Current token status.
    pub status: HandoffStatus,
    /// Creation timestamp.
    pub created_at: u64,
    /// Redemption timestamp, if redeemed.
    pub redeemed_at: Option<u64>,
}

/// The bot's CapTP client — manages its identity, held caps, and exports.
#[derive(Debug)]
pub struct CapTPClient {
    /// The bot's own federation ID.
    pub federation_id: GroupId,
    /// The bot's cell ID (hex).
    pub bot_cell_id: String,
    /// The configured dregg node URL.
    pub node_url: String,
}

impl CapTPClient {
    /// Create a new CapTP client for the bot.
    pub fn new(federation_id: GroupId, bot_cell_id: String, node_url: String) -> Self {
        Self {
            federation_id,
            bot_cell_id,
            node_url,
        }
    }

    /// Export a cell as a sturdy ref, returning the dregg URI.
    pub async fn export_cap(&self, db: &Database, cell_id: &str) -> Result<DreggUri, CapTPError> {
        let cell_bytes = parse_cell_id(cell_id)?;
        let uri = DreggUri {
            federation_id: self.federation_id.0,
            cell_id: cell_bytes,
            swiss: new_swiss(cell_id, &self.bot_cell_id, self.federation_id.0),
        };

        // Track the export.
        let export = ExportedCapability {
            cell_id: cell_id.to_string(),
            uri: uri.clone(),
            shared_with: None,
            exported_at: current_epoch(),
            revoked: false,
        };
        db.upsert_captp_export(&CaptpExportRecord::from(&export))
            .await
            .map_err(storage_error)?;

        info!(cell_id, "Exported capability as sturdy ref");
        Ok(uri)
    }

    /// Enliven a dregg URI — the bot accepts and holds the live reference.
    pub async fn accept_cap(
        &self,
        db: &Database,
        uri_str: &str,
    ) -> Result<HeldCapability, CapTPError> {
        let uri = DreggUri::parse(uri_str).map_err(|e| CapTPError::InvalidUri(e.to_string()))?;

        let cell_id = hex::encode(uri.cell_id);
        let Some(export) = db
            .get_captp_export(&cell_id)
            .await
            .map_err(storage_error)?
            .map(export_from_record)
            .transpose()?
        else {
            // FAIL CLOSED, NAMED. The dregg node serves no `/captp/enliven` HTTP
            // endpoint (see the module header), so a remote enliven over the node's
            // wire is genuinely unavailable. The REAL enliven path for a `dregg://`
            // ref is the web-of-cells verified attested resolve
            // ([`Self::enliven_via_web_of_cells`]) — but that resolves only cells
            // this bot has published as web-of-cells content. This URI is neither a
            // local export nor (here) a published web-of-cells cell, so there is
            // nothing for the bot to enliven. This is a precise refusal, never a
            // silent success on an un-enlivened ref.
            return Err(CapTPError::EnlivenUnavailable {
                cell_id: cell_id.clone(),
            });
        };
        if export.revoked {
            return Err(CapTPError::NotFound(format!(
                "{cell_id} (local export is revoked)"
            )));
        }
        if export.uri != uri {
            return Err(CapTPError::NotFound(format!(
                "{cell_id} (swiss number does not match this bot's active export)"
            )));
        }

        let cap = HeldCapability {
            uri,
            label: None,
            shared_by: None,
            acquired_at: current_epoch(),
            live: true,
        };

        db.upsert_captp_held_ref(&CaptpHeldRecord::from_cap(&cell_id, &cap))
            .await
            .map_err(storage_error)?;
        info!(cell_id, "Enlivened and holding capability");
        Ok(cap)
    }

    /// **Enliven a `dregg://` ref via the web-of-cells verified attested resolve**
    /// — the REAL URI-fetch enliven (the implemented half of the
    /// `captp_client.rs:165` toy finding).
    ///
    /// This is the genuine `dregg://` enliven: it performs the verified cross-cell
    /// finalized read against `web` ([`WebOfCells::fetch`]), runs the full
    /// content→commitment→receipt→quorum-root verification chain
    /// ([`starbridge_web_surface::web_of_cells::AttestedResource::verify`]), and —
    /// only on success — holds the live reference. A cell that was never published,
    /// or whose content/attestation does not verify, is REFUSED
    /// ([`CapTPError::EnlivenVerifyFailed`]): confinement before relation, never an
    /// un-enlivened ref held as live.
    ///
    /// `web` is the bot's web-of-cells (the deos surfaces it published). This is the
    /// bounded-but-genuine remote enliven: the node serves no `/captp/enliven`, but
    /// a `dregg://` ref into a published web-of-cells cell IS enlivenable, here, by
    /// the real verified read. Returns the held cap AND the verified content bytes.
    pub async fn enliven_via_web_of_cells(
        &self,
        db: &Database,
        web: &WebOfCells,
        cell_id: &CellId,
    ) -> Result<(HeldCapability, Vec<u8>), CapTPError> {
        // The verified attested resolve — the genuine `dregg://` enliven. Run the
        // full verification chain BEFORE holding the ref (confinement first); a
        // refusal here means the ref is NEVER held as live.
        let content_bytes = resolve_via_web_of_cells(web, cell_id)?;

        let cell_hex = hex::encode(cell_id.0);
        // Build the captp sturdy-ref form so the held record is uniform with the
        // rest of the bot's held caps (the swiss is derived from the verified cell).
        let captp_uri = DreggUri {
            federation_id: self.federation_id.0,
            cell_id: cell_id.0,
            swiss: new_swiss(&cell_hex, &self.bot_cell_id, self.federation_id.0),
        };
        let cap = HeldCapability {
            uri: captp_uri,
            label: Some("enliven:web-of-cells".to_string()),
            shared_by: None,
            acquired_at: current_epoch(),
            live: true,
        };
        db.upsert_captp_held_ref(&CaptpHeldRecord::from_cap(&cell_hex, &cap))
            .await
            .map_err(storage_error)?;
        info!(
            cell_id = cell_hex,
            "Enlivened via web-of-cells verified resolve"
        );
        Ok((cap, content_bytes))
    }

    /// Create a handoff certificate delegating a capability to a recipient.
    pub async fn delegate_cap(
        &self,
        db: &Database,
        cell_id: &str,
        recipient_key: &str,
    ) -> Result<HandoffRecord, CapTPError> {
        parse_cell_id(cell_id)?;
        parse_cell_id(recipient_key)?;

        let uri = match db
            .get_captp_export(cell_id)
            .await
            .map_err(storage_error)?
            .map(export_from_record)
            .transpose()?
        {
            Some(export) if !export.revoked => export.uri,
            Some(_) => {
                return Err(CapTPError::NotFound(format!(
                    "{cell_id} (local export is revoked)"
                )));
            }
            None => self.export_cap(db, cell_id).await?,
        };

        let token = format!("dregg-handoff-{}", hex::encode(new_secret()));
        let uri_string = uri.to_string();
        let local_signature = sign_handoff(
            &self.bot_cell_id,
            self.federation_id.0,
            &token,
            cell_id,
            recipient_key,
            &uri_string,
        );
        let record = HandoffRecord {
            token: token.clone(),
            cell_id: cell_id.to_string(),
            uri: uri_string,
            recipient_key: recipient_key.to_string(),
            local_signature,
            status: HandoffStatus::Pending,
            created_at: current_epoch(),
            redeemed_at: None,
        };

        db.upsert_captp_local_handoff(&CaptpLocalHandoffRecord::from(&record))
            .await
            .map_err(storage_error)?;

        info!(cell_id, recipient_key, token, "Created local CapTP handoff");
        Ok(record)
    }

    /// Return a handoff record by token.
    pub async fn handoff_status(&self, db: &Database, token: &str) -> Option<HandoffRecord> {
        db.get_captp_local_handoff(token)
            .await
            .ok()
            .flatten()
            .and_then(handoff_from_record)
    }

    /// Redeem a Discord-mediated local handoff token for the recipient identity.
    pub async fn redeem_handoff(
        &self,
        db: &Database,
        token: &str,
        recipient_key: &str,
    ) -> Result<HandoffRecord, CapTPError> {
        parse_cell_id(recipient_key)?;

        let Some(mut record) = db
            .get_captp_local_handoff(token)
            .await
            .map_err(storage_error)?
            .and_then(handoff_from_record)
        else {
            return Err(CapTPError::NotFound(format!("{token} (handoff token)")));
        };

        if record.recipient_key != recipient_key {
            return Err(CapTPError::Forbidden(
                "handoff token is bound to a different recipient identity".to_string(),
            ));
        }
        if record.status != HandoffStatus::Pending {
            return Err(CapTPError::Unsupported(format!(
                "handoff token is {}",
                record.status.as_str()
            )));
        }

        let expected = sign_handoff(
            &self.bot_cell_id,
            self.federation_id.0,
            &record.token,
            &record.cell_id,
            &record.recipient_key,
            &record.uri,
        );
        if record.local_signature != expected {
            return Err(CapTPError::InvalidUri(
                "handoff record signature does not verify".to_string(),
            ));
        }

        let uri =
            DreggUri::parse(&record.uri).map_err(|e| CapTPError::InvalidUri(e.to_string()))?;
        let cap = HeldCapability {
            uri,
            label: Some(format!("handoff:{}", record.token)),
            shared_by: None,
            acquired_at: current_epoch(),
            live: true,
        };

        record.status = HandoffStatus::Redeemed;
        record.redeemed_at = Some(current_epoch());
        let redeemed = record.clone();
        db.upsert_captp_held_ref(&CaptpHeldRecord::from_cap(&redeemed.cell_id, &cap))
            .await
            .map_err(storage_error)?;
        db.upsert_captp_local_handoff(&CaptpLocalHandoffRecord::from(&redeemed))
            .await
            .map_err(storage_error)?;

        info!(
            token,
            cell_id = redeemed.cell_id,
            "Redeemed local CapTP handoff"
        );
        Ok(redeemed)
    }

    /// Revoke a previously exported capability.
    pub async fn revoke_cap(&self, db: &Database, cell_id: &str) -> Result<(), CapTPError> {
        parse_cell_id(cell_id)?;

        if !db
            .revoke_captp_export(cell_id)
            .await
            .map_err(storage_error)?
        {
            return Err(CapTPError::NotFound(format!(
                "{cell_id} (no local export to revoke)"
            )));
        };

        db.revoke_pending_captp_local_handoffs_for_cell(cell_id, current_epoch() as i64)
            .await
            .map_err(storage_error)?;
        db.delete_captp_held_ref(cell_id)
            .await
            .map_err(storage_error)?;

        info!(cell_id, "Revoked capability");
        Ok(())
    }

    /// List all held capabilities.
    pub async fn list_held(
        &self,
        db: &Database,
    ) -> Result<Vec<(String, HeldCapability)>, CapTPError> {
        db.list_captp_held_refs()
            .await
            .map_err(storage_error)?
            .into_iter()
            .map(held_from_record)
            .collect()
    }

    /// List all exports.
    pub async fn list_exports(
        &self,
        db: &Database,
    ) -> Result<Vec<(String, ExportedCapability)>, CapTPError> {
        Ok(db
            .list_captp_exports()
            .await
            .map_err(storage_error)?
            .into_iter()
            .map(export_from_record)
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .map(|export| (export.cell_id.clone(), export))
            .collect())
    }

    /// List all local handoff records.
    pub async fn list_handoffs(&self, db: &Database) -> Result<Vec<HandoffRecord>, CapTPError> {
        Ok(db
            .list_captp_local_handoffs()
            .await
            .map_err(storage_error)?
            .into_iter()
            .filter_map(handoff_from_record)
            .collect())
    }
}

// ─── Errors ─────────────────────────────────────────────────────────────────

/// Errors from CapTP client operations.
#[derive(Debug, Clone)]
pub enum CapTPError {
    /// Failed to parse a dregg URI.
    InvalidUri(String),
    /// The requested capability was not found.
    NotFound(String),
    /// The operation is not implemented by the current backend.
    Unsupported(String),
    /// The caller is not allowed to exercise this handoff.
    Forbidden(String),
    /// Durable local handoff store failed.
    Storage(String),
    /// **Enliven fail-closed (named).** The `dregg://` ref names a cell this bot
    /// neither exported locally nor published as web-of-cells content, and the
    /// dregg node serves no remote `/captp/enliven` endpoint — so there is nothing
    /// for the bot to enliven. The REAL enliven path for a published web-of-cells
    /// cell is [`CapTPClient::enliven_via_web_of_cells`] (the verified attested
    /// resolve). This is a precise refusal, never a silent un-enlivened success.
    EnlivenUnavailable {
        /// The cell id (hex) that could not be enlivened.
        cell_id: String,
    },
    /// The web-of-cells verified attested resolve refused this `dregg://` ref (the
    /// cell was not published, or its content/attestation did not verify) — the
    /// genuine `dregg://` enliven gate, fail-closed. Carries a human reason.
    EnlivenVerifyFailed(String),
}

impl std::fmt::Display for CapTPError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CapTPError::InvalidUri(e) => write!(f, "invalid dregg URI: {e}"),
            CapTPError::NotFound(id) => write!(f, "capability not found: {id}"),
            CapTPError::Unsupported(message) => write!(f, "unsupported: {message}"),
            CapTPError::Forbidden(message) => write!(f, "forbidden: {message}"),
            CapTPError::Storage(message) => write!(f, "storage error: {message}"),
            CapTPError::EnlivenUnavailable { cell_id } => write!(
                f,
                "cannot enliven `{cell_id}`: not a local export, not a published web-of-cells \
                 cell, and the node serves no remote `/captp/enliven`. Publish it as a deos \
                 surface (web-of-cells) or accept a locally-exported ref."
            ),
            CapTPError::EnlivenVerifyFailed(message) => {
                write!(f, "dregg:// enliven verification failed: {message}")
            }
        }
    }
}

impl std::error::Error for CapTPError {}

// ─── Helpers ────────────────────────────────────────────────────────────────

fn current_epoch() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs()
}

fn parse_cell_id(cell_id: &str) -> Result<[u8; 32], CapTPError> {
    let bytes = hex::decode(cell_id).map_err(|e| CapTPError::InvalidUri(e.to_string()))?;
    bytes.try_into().map_err(|bytes: Vec<u8>| {
        CapTPError::InvalidUri(format!("cell ID must be 32 bytes, got {}", bytes.len()))
    })
}

fn new_swiss(cell_id: &str, bot_cell_id: &str, federation_id: [u8; 32]) -> [u8; 32] {
    new_secret_with_fallback(cell_id.as_bytes(), bot_cell_id.as_bytes(), &federation_id)
}

fn new_secret() -> [u8; 32] {
    new_secret_with_fallback(b"handoff-token", b"", b"")
}

fn new_secret_with_fallback(seed_a: &[u8], seed_b: &[u8], seed_c: &[u8]) -> [u8; 32] {
    let mut swiss = [0u8; 32];
    if std::fs::File::open("/dev/urandom")
        .and_then(|mut file| file.read_exact(&mut swiss))
        .is_ok()
    {
        return swiss;
    }

    static FALLBACK_COUNTER: AtomicU64 = AtomicU64::new(0);
    let counter = FALLBACK_COUNTER.fetch_add(1, Ordering::Relaxed);
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos();
    *blake3::Hasher::new()
        .update(seed_a)
        .update(seed_b)
        .update(seed_c)
        .update(&now.to_le_bytes())
        .update(&counter.to_le_bytes())
        .finalize()
        .as_bytes()
}

fn sign_handoff(
    bot_cell_id: &str,
    federation_id: [u8; 32],
    token: &str,
    cell_id: &str,
    recipient_key: &str,
    uri: &str,
) -> String {
    hex::encode(
        blake3::Hasher::new()
            .update(b"dregg-discord-captp-local-handoff-v1")
            .update(bot_cell_id.as_bytes())
            .update(&federation_id)
            .update(token.as_bytes())
            .update(cell_id.as_bytes())
            .update(recipient_key.as_bytes())
            .update(uri.as_bytes())
            .finalize()
            .as_bytes(),
    )
}

fn storage_error(error: sqlx::Error) -> CapTPError {
    CapTPError::Storage(error.to_string())
}

/// The pure `dregg://` enliven core: verified attested resolve of `cell_id`
/// against `web` (no DB). Performs the fetch + the full
/// content→commitment→receipt→quorum-root verification chain; returns the verified
/// content bytes on success, [`CapTPError::EnlivenVerifyFailed`] on any miss (cell
/// never published, content does not match its commitment, attestation invalid).
/// Confinement before relation — a ref that does not verify yields NO content.
fn resolve_via_web_of_cells(web: &WebOfCells, cell_id: &CellId) -> Result<Vec<u8>, CapTPError> {
    let woc_uri = WocUri::new(*cell_id);
    let (resource, _chrome) = web
        .fetch(&woc_uri)
        .map_err(|e| CapTPError::EnlivenVerifyFailed(format!("fetch: {e:?}")))?;
    resource
        .verify()
        .map_err(|e| CapTPError::EnlivenVerifyFailed(format!("attestation: {e:?}")))?;
    Ok(resource.content_bytes)
}

impl From<&ExportedCapability> for CaptpExportRecord {
    fn from(export: &ExportedCapability) -> Self {
        Self {
            cell_id: export.cell_id.clone(),
            sturdy_uri: export.uri.to_string(),
            shared_with: export.shared_with.map(|id| id.to_string()),
            exported_at: export.exported_at as i64,
            revoked: export.revoked,
        }
    }
}

impl CaptpHeldRecord {
    fn from_cap(cell_id: &str, cap: &HeldCapability) -> Self {
        Self {
            cell_id: cell_id.to_string(),
            sturdy_uri: cap.uri.to_string(),
            label: cap.label.clone(),
            shared_by: cap.shared_by.map(|id| id.to_string()),
            acquired_at: cap.acquired_at as i64,
            live: cap.live,
        }
    }
}

impl From<&HandoffRecord> for CaptpLocalHandoffRecord {
    fn from(record: &HandoffRecord) -> Self {
        Self {
            token_id: record.token.clone(),
            cell_id: record.cell_id.clone(),
            sturdy_uri: record.uri.clone(),
            recipient_cell_id: record.recipient_key.clone(),
            local_signature: record.local_signature.clone(),
            status: record.status.as_str().to_string(),
            created_at: record.created_at as i64,
            redeemed_at: record.redeemed_at.map(|value| value as i64),
        }
    }
}

fn export_from_record(record: CaptpExportRecord) -> Result<ExportedCapability, CapTPError> {
    Ok(ExportedCapability {
        cell_id: record.cell_id,
        uri: DreggUri::parse(&record.sturdy_uri)
            .map_err(|e| CapTPError::InvalidUri(e.to_string()))?,
        shared_with: record
            .shared_with
            .as_deref()
            .and_then(|value| value.parse().ok()),
        exported_at: record.exported_at as u64,
        revoked: record.revoked,
    })
}

fn held_from_record(record: CaptpHeldRecord) -> Result<(String, HeldCapability), CapTPError> {
    let uri =
        DreggUri::parse(&record.sturdy_uri).map_err(|e| CapTPError::InvalidUri(e.to_string()))?;
    Ok((
        record.cell_id,
        HeldCapability {
            uri,
            label: record.label,
            shared_by: record
                .shared_by
                .as_deref()
                .and_then(|value| value.parse().ok()),
            acquired_at: record.acquired_at as u64,
            live: record.live,
        },
    ))
}

fn handoff_from_record(record: CaptpLocalHandoffRecord) -> Option<HandoffRecord> {
    Some(HandoffRecord {
        token: record.token_id,
        cell_id: record.cell_id,
        uri: record.sturdy_uri,
        recipient_key: record.recipient_cell_id,
        local_signature: record.local_signature,
        status: HandoffStatus::from_str(&record.status)?,
        created_at: record.created_at as u64,
        redeemed_at: record.redeemed_at.map(|value| value as u64),
    })
}

#[cfg(test)]
mod enliven_tests {
    use super::*;

    fn cid(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    // THE REAL `dregg://` ENLIVEN: a published web-of-cells cell resolves to its
    // verified content (the implemented half of the captp_client.rs:165 finding).
    #[test]
    fn enliven_resolves_a_published_web_of_cells_cell() {
        let mut web = WebOfCells::new(3);
        let uri = web.publish(7, b"the enlivened cell content", "dregg://deos/cap");

        // The verified attested resolve returns EXACTLY the committed bytes.
        let bytes = resolve_via_web_of_cells(&web, &uri.cell)
            .expect("a published, attested cell enlivens via the verified resolve");
        assert_eq!(bytes, b"the enlivened cell content");
    }

    // FAIL CLOSED: a cell that was never published does NOT enliven — the verified
    // resolve refuses (confinement before relation, never an un-enlivened success).
    #[test]
    fn enliven_refuses_an_unpublished_cell() {
        let web = WebOfCells::new(3); // nothing published
        let r = resolve_via_web_of_cells(&web, &cid(200));
        assert!(
            matches!(r, Err(CapTPError::EnlivenVerifyFailed(_))),
            "an unpublished cell must be refused by the verified resolve, got {r:?}"
        );
    }

    // The named fail-closed error renders an actionable message (never a silent
    // un-enlivened ref).
    #[test]
    fn enliven_unavailable_error_is_named_and_actionable() {
        let err = CapTPError::EnlivenUnavailable {
            cell_id: "deadbeef".to_string(),
        };
        let msg = err.to_string();
        assert!(msg.contains("deadbeef"));
        assert!(msg.contains("enliven"));
        assert!(msg.contains("web-of-cells"));
    }
}
