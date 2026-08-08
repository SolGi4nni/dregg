//! Curator-signed, read-only media companion routing.
//!
//! A companion route is a short-lived discovery document, not game authority.
//! It binds one exact browser context to the already-verified PoA deployment
//! and content epoch.  The signer can only name POAG1 artifacts whose bytes are
//! present in the authenticated bundle; it cannot introduce an unpinned asset.

use std::path::Path;

use dregg_types::{Signature, SigningKey};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use super::{
    CuratorError, CuratorKeyPin, DeploymentBoundBundle, Poag1Bundle, VerifiedContentEpoch,
    hex_encode, parse_hex_array, parse_strict_json, read_regular_bounded,
};

pub const COMPANION_SCHEMA_V3: &str = "poa-companion/v3";
pub const POA_ORIGIN: &str = "https://beta.pathofangels.network";
pub const MAX_COMPANION_LIFETIME_SECONDS: u64 = 7 * 24 * 60 * 60;
const MAX_COMPANION_BYTES: u64 = 256 * 1024;
const MAX_CONTENT_ASSETS: usize = 8;

#[derive(Debug, Error)]
pub enum CompanionError {
    #[error(transparent)]
    Curator(#[from] CuratorError),
    #[error("companion JSON refused: {0}")]
    Json(String),
    #[error("companion manifest refused: {0}")]
    Manifest(String),
    #[error("companion signature did not verify under the external curator pin")]
    BadSignature,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "platform", rename_all = "lowercase", deny_unknown_fields)]
pub enum CompanionContext {
    Youtube {
        #[serde(rename = "videoId")]
        video_id: String,
        #[serde(rename = "channelId")]
        channel_id: String,
    },
    X {
        #[serde(rename = "postId")]
        post_id: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CompanionGameRoute {
    pub kind: String,
    pub src: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CompanionLink {
    pub label: String,
    pub beta_url: String,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CompanionActions {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub mission: Option<CompanionLink>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub evidence: Option<CompanionLink>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub debrief: Option<CompanionLink>,
}

/// One exact member of the content-epoch POAG1 bundle.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CompanionContentAsset {
    pub path: String,
    pub url: String,
    pub media_type: String,
    pub bytes: u64,
    /// Lowercase, unprefixed SHA-256. The signing ceremony checks this against
    /// the `sha256:` pin in the authenticated POAG1 manifest.
    pub sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CompanionFieldRecordRef {
    pub finalized_receipt_core_id: String,
    pub federation_id: String,
    pub turn_hash: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CompanionExperience {
    pub id: String,
    pub title: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub episode: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub dispatch: Option<String>,
    pub beta_url: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub game: Option<CompanionGameRoute>,
    pub content_assets: Vec<CompanionContentAsset>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub actions: Option<CompanionActions>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub field_record: Option<CompanionFieldRecordRef>,
}

/// Canonical v3 route. Field order is part of the cross-runtime signed bytes;
/// keep it synchronized with `extension/src/poa.ts`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct CompanionManifestV3 {
    pub schema: String,
    pub content_epoch: u64,
    pub content_counter: u64,
    pub sequence: u64,
    pub poa_origin: String,
    pub federation_id: String,
    pub deployment_id: String,
    pub content_pack_digest: String,
    pub context: CompanionContext,
    pub experience: CompanionExperience,
    pub issued_at: u64,
    pub expires_at: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SignedCompanionManifestV3 {
    pub manifest: CompanionManifestV3,
    pub signer: String,
    pub signature: String,
}

impl CompanionManifestV3 {
    pub fn load(path: impl AsRef<Path>) -> Result<Self, CompanionError> {
        let bytes = read_regular_bounded(path.as_ref(), MAX_COMPANION_BYTES)?;
        let value = parse_strict_json(&bytes).map_err(CompanionError::Json)?;
        serde_json::from_value(value).map_err(|error| CompanionError::Json(error.to_string()))
    }

    /// Exact bytes verified by the browser extension. The schema line is an
    /// explicit protocol domain; JSON whitespace from the draft is irrelevant.
    pub fn signing_bytes(&self) -> Result<Vec<u8>, CompanionError> {
        if self.schema != COMPANION_SCHEMA_V3 {
            return Err(CompanionError::Manifest("unknown companion schema".into()));
        }
        let mut bytes = Vec::with_capacity(32 * 1024);
        bytes.extend_from_slice(COMPANION_SCHEMA_V3.as_bytes());
        bytes.push(b'\n');
        bytes.extend_from_slice(
            &serde_json::to_vec(self).map_err(|error| CompanionError::Json(error.to_string()))?,
        );
        Ok(bytes)
    }

    pub fn validate(
        &self,
        bound: &DeploymentBoundBundle<'_>,
        content: &VerifiedContentEpoch<'_>,
        now_seconds: u64,
    ) -> Result<(), CompanionError> {
        if self.schema != COMPANION_SCHEMA_V3 {
            return Err(CompanionError::Manifest("unknown companion schema".into()));
        }
        if self.poa_origin != POA_ORIGIN {
            return Err(CompanionError::Manifest("wrong PoA origin".into()));
        }
        if self.federation_id != bound.deployment().federation_id()
            || self.deployment_id != bound.deployment().deployment_id()
        {
            return Err(CompanionError::Manifest(
                "route is not bound to the verified PoA deployment".into(),
            ));
        }
        if self.content_epoch != content.envelope().content_epoch
            || self.content_counter != content.envelope().counter
            || self.content_epoch != bound.bundle().content_epoch()
        {
            return Err(CompanionError::Manifest(
                "route is not bound to the verified content epoch/counter".into(),
            ));
        }
        if self.content_pack_digest != bound.bundle().manifest_sha256() {
            return Err(CompanionError::Manifest(
                "contentPackDigest does not name the exact POAG1 manifest bytes".into(),
            ));
        }
        tagged_digest_nonzero(&self.content_pack_digest, "contentPackDigest")?;
        digest_nonzero(&self.federation_id, "federationId")?;
        digest_nonzero(&self.deployment_id, "deploymentId")?;
        if self.expires_at <= self.issued_at
            || self.expires_at - self.issued_at > MAX_COMPANION_LIFETIME_SECONDS
            || self.expires_at <= now_seconds
            || self.issued_at > now_seconds.saturating_add(300)
        {
            return Err(CompanionError::Manifest(
                "companion lifetime is stale, future-issued, or longer than seven days".into(),
            ));
        }
        validate_context(&self.context)?;
        validate_experience(&self.experience, bound.bundle(), &self.federation_id)?;
        Ok(())
    }
}

impl SignedCompanionManifestV3 {
    pub fn load(path: impl AsRef<Path>) -> Result<Self, CompanionError> {
        let bytes = read_regular_bounded(path.as_ref(), MAX_COMPANION_BYTES)?;
        let value = parse_strict_json(&bytes).map_err(CompanionError::Json)?;
        serde_json::from_value(value).map_err(|error| CompanionError::Json(error.to_string()))
    }

    pub fn sign(
        manifest: CompanionManifestV3,
        key: &SigningKey,
        bound: &DeploymentBoundBundle<'_>,
        content: &VerifiedContentEpoch<'_>,
        now_seconds: u64,
    ) -> Result<Self, CompanionError> {
        manifest.validate(bound, content, now_seconds)?;
        if key.public_key() != content.public_key() {
            return Err(CompanionError::Manifest(
                "companion signer differs from the verified content curator".into(),
            ));
        }
        let signature = dregg_types::sign(key, &manifest.signing_bytes()?);
        Ok(Self {
            manifest,
            signer: key.public_key().hex(),
            signature: hex_encode(&signature.0),
        })
    }

    pub fn verify(
        &self,
        pin: &CuratorKeyPin,
        bound: &DeploymentBoundBundle<'_>,
        content: &VerifiedContentEpoch<'_>,
        now_seconds: u64,
    ) -> Result<(), CompanionError> {
        self.manifest.validate(bound, content, now_seconds)?;
        let key = pin.public_key()?;
        if self.signer != key.hex() || key != content.public_key() {
            return Err(CompanionError::Manifest(
                "companion signer differs from the external/content curator pin".into(),
            ));
        }
        let signature = Signature(parse_hex_array::<64>(&self.signature, "signature")?);
        if !dregg_types::verify(&key, &self.manifest.signing_bytes()?, &signature) {
            return Err(CompanionError::BadSignature);
        }
        Ok(())
    }
}

fn validate_context(context: &CompanionContext) -> Result<(), CompanionError> {
    match context {
        CompanionContext::Youtube {
            video_id,
            channel_id,
        } => {
            if video_id.len() != 11 || !video_id.bytes().all(media_id_byte) {
                return Err(CompanionError::Manifest(
                    "malformed YouTube video id".into(),
                ));
            }
            if !(3..=128).contains(&channel_id.len()) || !channel_id.bytes().all(media_id_byte) {
                return Err(CompanionError::Manifest(
                    "malformed YouTube channel id".into(),
                ));
            }
        }
        CompanionContext::X { post_id } => {
            if post_id.is_empty()
                || post_id.len() > 20
                || post_id.starts_with('0')
                || !post_id.bytes().all(|byte| byte.is_ascii_digit())
            {
                return Err(CompanionError::Manifest("malformed X post id".into()));
            }
        }
    }
    Ok(())
}

fn validate_experience(
    experience: &CompanionExperience,
    bundle: &Poag1Bundle,
    federation_id: &str,
) -> Result<(), CompanionError> {
    bounded_text(&experience.id, 64, false, "experience id")?;
    if !experience.id.bytes().enumerate().all(|(index, byte)| {
        byte.is_ascii_lowercase()
            || byte.is_ascii_digit()
            || (index > 0 && matches!(byte, b'_' | b'-'))
    }) {
        return Err(CompanionError::Manifest("malformed experience id".into()));
    }
    bounded_text(&experience.title, 160, false, "title")?;
    if let Some(episode) = &experience.episode {
        bounded_text(episode, 96, false, "episode")?;
    }
    if let Some(dispatch) = &experience.dispatch {
        bounded_text(dispatch, 1200, true, "dispatch")?;
    }
    poa_url(&experience.beta_url, "betaUrl")?;
    if let Some(game) = &experience.game
        && (game.kind != "descent"
            || !game.src.starts_with("dregg://descent/b3_")
            || game.src.len() > 256
            || !game.src[19..].bytes().all(|byte| byte.is_ascii_hexdigit())
            || game.src.len() < 25)
    {
        return Err(CompanionError::Manifest("malformed Descent route".into()));
    }
    if experience.content_assets.is_empty() || experience.content_assets.len() > MAX_CONTENT_ASSETS
    {
        return Err(CompanionError::Manifest(
            "contentAssets must contain one through eight POAG1 members".into(),
        ));
    }
    let mut previous = None::<&str>;
    for asset in &experience.content_assets {
        if previous.is_some_and(|path| path >= asset.path.as_str()) {
            return Err(CompanionError::Manifest(
                "contentAssets must be unique and sorted by path".into(),
            ));
        }
        previous = Some(&asset.path);
        let pin = bundle
            .manifest()
            .artifacts
            .iter()
            .find(|pin| pin.path == asset.path)
            .ok_or_else(|| {
                CompanionError::Manifest(format!(
                    "content asset {} is not in the authenticated POAG1 manifest",
                    asset.path
                ))
            })?;
        let expected_url = format!("{POA_ORIGIN}/artifacts/poag1/{}", pin.path);
        let expected_sha = pin.sha256.strip_prefix("sha256:").ok_or_else(|| {
            CompanionError::Manifest("POAG1 artifact has a noncanonical SHA-256 pin".into())
        })?;
        if asset.url != expected_url
            || asset.media_type != pin.media_type
            || asset.bytes != pin.bytes
            || asset.sha256 != expected_sha
        {
            return Err(CompanionError::Manifest(format!(
                "content asset {} differs from the authenticated POAG1 pin",
                asset.path
            )));
        }
        digest(&asset.sha256, "content asset sha256")?;
    }
    if let Some(actions) = &experience.actions {
        if actions.mission.is_none() && actions.evidence.is_none() && actions.debrief.is_none() {
            return Err(CompanionError::Manifest("actions cannot be empty".into()));
        }
        for link in [
            actions.mission.as_ref(),
            actions.evidence.as_ref(),
            actions.debrief.as_ref(),
        ]
        .into_iter()
        .flatten()
        {
            bounded_text(&link.label, 80, false, "action label")?;
            poa_url(&link.beta_url, "action betaUrl")?;
        }
    }
    if let Some(record) = &experience.field_record {
        if experience.episode.is_none() {
            return Err(CompanionError::Manifest(
                "fieldRecord requires an authored episode label".into(),
            ));
        }
        digest_nonzero(&record.finalized_receipt_core_id, "finalizedReceiptCoreId")?;
        digest(&record.federation_id, "fieldRecord federationId")?;
        digest(&record.turn_hash, "turnHash")?;
        if record.federation_id != federation_id {
            return Err(CompanionError::Manifest(
                "fieldRecord is scoped to a different federation".into(),
            ));
        }
    }
    Ok(())
}

fn media_id_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-')
}

fn bounded_text(
    value: &str,
    max: usize,
    allow_empty: bool,
    field: &str,
) -> Result<(), CompanionError> {
    if value.len() > max
        || (!allow_empty && value.is_empty())
        || value.bytes().any(|byte| byte < 0x20 || byte == 0x7f)
    {
        return Err(CompanionError::Manifest(format!("malformed {field}")));
    }
    Ok(())
}

fn poa_url(value: &str, field: &str) -> Result<(), CompanionError> {
    let prefix = format!("{POA_ORIGIN}/");
    if !value.starts_with(&prefix)
        || value.len() > 512
        || value
            .bytes()
            .any(|byte| byte < 0x20 || byte == 0x7f || byte == b'\\')
    {
        return Err(CompanionError::Manifest(format!("malformed {field}")));
    }
    Ok(())
}

fn digest(value: &str, field: &str) -> Result<(), CompanionError> {
    if value.len() != 64
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(CompanionError::Manifest(format!("malformed {field}")));
    }
    Ok(())
}

fn digest_nonzero(value: &str, field: &str) -> Result<(), CompanionError> {
    digest(value, field)?;
    if value.bytes().all(|byte| byte == b'0') {
        return Err(CompanionError::Manifest(format!("zero {field}")));
    }
    Ok(())
}

fn tagged_digest_nonzero(value: &str, field: &str) -> Result<(), CompanionError> {
    let digest = value
        .strip_prefix("sha256:")
        .ok_or_else(|| CompanionError::Manifest(format!("malformed {field}")))?;
    digest_nonzero(digest, field)
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use dregg_types::SigningKey;

    use super::*;
    use crate::{CuratorSigner, Poag1Bundle};

    const NOW: u64 = 1_800_000_000;

    fn repo() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("..")
    }

    fn deployment_manifest_path() -> PathBuf {
        repo().join("poa/deployments/epoch-1/poa-devnet.json")
    }

    /// The live federation/deployment identity, read from the deployment kit the
    /// ceremony actually genesises. Never typed: a ceremony that re-genesises moves
    /// both of these, and a typed copy would keep a test green against a dead
    /// federation — which is exactly what happened until 2026-08-05.
    fn deployed_identity() -> (String, String) {
        let bundle = Poag1Bundle::load(repo().join("poa/artifacts/poag1/manifest.json")).unwrap();
        let bound = bundle.bind_deployment(deployment_manifest_path()).unwrap();
        (
            bound.deployment().federation_id().to_owned(),
            bound.deployment().deployment_id().to_owned(),
        )
    }

    fn manifest(bundle: &Poag1Bundle) -> CompanionManifestV3 {
        let catalog = bundle
            .manifest()
            .artifacts
            .iter()
            .find(|pin| pin.path == "catalog.json")
            .unwrap();
        let (federation_id, deployment_id) = deployed_identity();
        CompanionManifestV3 {
            schema: COMPANION_SCHEMA_V3.into(),
            content_epoch: 1,
            content_counter: 4,
            sequence: 7,
            poa_origin: POA_ORIGIN.into(),
            federation_id,
            deployment_id,
            content_pack_digest: bundle.manifest_sha256().into(),
            context: CompanionContext::Youtube {
                video_id: "AbCdEfGhI01".into(),
                channel_id: "UC_PathOfAngels".into(),
            },
            experience: CompanionExperience {
                id: "episode-1".into(),
                title: "Path of Angels field dispatch".into(),
                episode: Some("Episode 1".into()),
                dispatch: Some("A signed field route is available.".into()),
                beta_url: format!("{POA_ORIGIN}/?episode=1"),
                game: Some(CompanionGameRoute {
                    kind: "descent".into(),
                    src: "dregg://descent/b3_de5ce0".into(),
                }),
                content_assets: vec![CompanionContentAsset {
                    path: catalog.path.clone(),
                    url: format!("{POA_ORIGIN}/artifacts/poag1/{}", catalog.path),
                    media_type: catalog.media_type.clone(),
                    bytes: catalog.bytes,
                    sha256: catalog.sha256.trim_start_matches("sha256:").into(),
                }],
                actions: Some(CompanionActions {
                    mission: Some(CompanionLink {
                        label: "Open field terminal".into(),
                        beta_url: format!("{POA_ORIGIN}/?station=field"),
                    }),
                    evidence: None,
                    debrief: None,
                }),
                field_record: None,
            },
            issued_at: NOW - 60,
            expires_at: NOW + 3600,
        }
    }

    /// A route whose every field is a LITERAL of this test, naming no artifact and
    /// no deployment. The property under test is the canonical PROJECTION — key
    /// order, absent-option elision, number rendering, string escaping, the
    /// `poa-companion/v3\n` domain line — which is the cross-runtime contract with
    /// `extension/src/poa.ts` (`JSON.stringify` over the same fixed key order).
    ///
    /// ⚠ Deliberately synthetic. This assertion used to be typed over the LIVE
    /// bundle, so it pinned `bytes: 5508` for `catalog.json` — a length that grows
    /// every time a game enrols, which made a correct enrolment red and the repair
    /// "bump the literal", re-arming it for the next one. What the projection owes
    /// the artifact is checked below, against the artifact, by derivation.
    fn projection_fixture() -> CompanionManifestV3 {
        CompanionManifestV3 {
            schema: COMPANION_SCHEMA_V3.into(),
            content_epoch: 1,
            content_counter: 4,
            sequence: 7,
            poa_origin: POA_ORIGIN.into(),
            federation_id: "11".repeat(32),
            deployment_id: "22".repeat(32),
            content_pack_digest: format!("sha256:{}", "33".repeat(32)),
            context: CompanionContext::Youtube {
                video_id: "AbCdEfGhI01".into(),
                channel_id: "UC_PathOfAngels".into(),
            },
            experience: CompanionExperience {
                id: "episode-1".into(),
                // quote, backslash and a non-ASCII dash: the escaper is part of the
                // signed bytes and both runtimes must render it identically.
                title: "Path of Angels — a \"field\" dispatch \\ route".into(),
                episode: Some("Episode 1".into()),
                dispatch: Some("A signed field route is available.".into()),
                beta_url: format!("{POA_ORIGIN}/?episode=1"),
                game: Some(CompanionGameRoute {
                    kind: "descent".into(),
                    src: "dregg://descent/b3_de5ce0".into(),
                }),
                content_assets: vec![CompanionContentAsset {
                    path: "catalog.json".into(),
                    url: format!("{POA_ORIGIN}/artifacts/poag1/catalog.json"),
                    media_type: "application/json".into(),
                    bytes: 4242,
                    sha256: "44".repeat(32),
                }],
                actions: Some(CompanionActions {
                    mission: Some(CompanionLink {
                        label: "Open field terminal".into(),
                        beta_url: format!("{POA_ORIGIN}/?station=field"),
                    }),
                    evidence: None,
                    debrief: None,
                }),
                field_record: None,
            },
            issued_at: NOW - 60,
            expires_at: NOW + 3600,
        }
    }

    #[test]
    fn v3_signing_bytes_are_the_browser_canonical_projection() {
        let bytes = String::from_utf8(projection_fixture().signing_bytes().unwrap()).unwrap();
        assert_eq!(
            bytes,
            concat!(
                "poa-companion/v3\n",
                "{\"schema\":\"poa-companion/v3\",\"contentEpoch\":1,\"contentCounter\":4,\"sequence\":7,",
                "\"poaOrigin\":\"https://beta.pathofangels.network\",",
                "\"federationId\":\"1111111111111111111111111111111111111111111111111111111111111111\",",
                "\"deploymentId\":\"2222222222222222222222222222222222222222222222222222222222222222\",",
                "\"contentPackDigest\":\"sha256:3333333333333333333333333333333333333333333333333333333333333333\",",
                "\"context\":{\"platform\":\"youtube\",\"videoId\":\"AbCdEfGhI01\",\"channelId\":\"UC_PathOfAngels\"},",
                "\"experience\":{\"id\":\"episode-1\",\"title\":\"Path of Angels — a \\\"field\\\" dispatch \\\\ route\",\"episode\":\"Episode 1\",",
                "\"dispatch\":\"A signed field route is available.\",\"betaUrl\":\"https://beta.pathofangels.network/?episode=1\",",
                "\"game\":{\"kind\":\"descent\",\"src\":\"dregg://descent/b3_de5ce0\"},",
                "\"contentAssets\":[{\"path\":\"catalog.json\",\"url\":\"https://beta.pathofangels.network/artifacts/poag1/catalog.json\",",
                "\"mediaType\":\"application/json\",\"bytes\":4242,\"sha256\":\"4444444444444444444444444444444444444444444444444444444444444444\"}],",
                "\"actions\":{\"mission\":{\"label\":\"Open field terminal\",\"betaUrl\":\"https://beta.pathofangels.network/?station=field\"}}},",
                "\"issuedAt\":1799999940,\"expiresAt\":1800003600}"
            )
        );
    }

    /// What the projection owes the SHIPPED artifact, pinned by derivation rather
    /// than by a literal: every identity in the signed bytes has to be the one the
    /// authenticated bundle and the deployment kit report, byte for byte. This is
    /// the half that had teeth, and it survives an enrolment because it reads the
    /// enrolled artifact instead of a length someone typed.
    #[test]
    fn v3_signing_bytes_carry_the_live_bundle_and_deployment_verbatim() {
        let bundle = Poag1Bundle::load(repo().join("poa/artifacts/poag1/manifest.json")).unwrap();
        let catalog = bundle
            .manifest()
            .artifacts
            .iter()
            .find(|pin| pin.path == "catalog.json")
            .unwrap();
        let (federation_id, deployment_id) = deployed_identity();
        let bytes = String::from_utf8(manifest(&bundle).signing_bytes().unwrap()).unwrap();

        // The bundle's own manifest digest is what a companion route commits to;
        // a projection that dropped or truncated it would not carry this span.
        let expected_pack = format!("\"contentPackDigest\":\"{}\",", bundle.manifest_sha256());
        assert!(
            bytes.contains(&expected_pack),
            "signed bytes do not carry the bundle manifest digest: {expected_pack}"
        );
        assert!(bytes.contains(&format!("\"federationId\":\"{federation_id}\",")));
        assert!(bytes.contains(&format!("\"deploymentId\":\"{deployment_id}\",")));

        // The catalog asset span, rendered from the authenticated POAG1 pin. `bytes`
        // and `sha256` move together on every enrolment and neither is typed here.
        let expected_asset = format!(
            concat!(
                "{{\"path\":\"{path}\",\"url\":\"{origin}/artifacts/poag1/{path}\",",
                "\"mediaType\":\"{media}\",\"bytes\":{len},\"sha256\":\"{sha}\"}}"
            ),
            path = catalog.path,
            origin = POA_ORIGIN,
            media = catalog.media_type,
            len = catalog.bytes,
            sha = catalog.sha256.trim_start_matches("sha256:"),
        );
        assert!(
            bytes.contains(&expected_asset),
            "signed bytes do not carry the authenticated catalog pin: {expected_asset}"
        );

        // …and the pin is the file on disk, so `bytes`/`sha256` above are the real
        // artifact and not a manifest that drifted from it.
        let on_disk = bundle.artifact_bytes(&catalog.path).unwrap();
        assert_eq!(on_disk.len() as u64, catalog.bytes);
    }

    #[test]
    fn v3_signature_and_content_ceremony_refuse_every_scope_substitution() {
        let root = repo();
        let bundle = Poag1Bundle::load(root.join("poa/artifacts/poag1/manifest.json")).unwrap();
        let bound = bundle
            .bind_deployment(root.join("poa/deployments/epoch-1/poa-devnet.json"))
            .unwrap();
        let key = SigningKey::from_bytes(&[0x42; 32]);
        let pin = CuratorKeyPin::new(&key.public_key());
        let content = CuratorSigner::new(&key)
            .sign_content_epoch(&bound, 1, 4)
            .unwrap();
        let verified = content.verify(&bound, &pin, 1, 4).unwrap();
        let signed =
            SignedCompanionManifestV3::sign(manifest(&bundle), &key, &bound, &verified, NOW)
                .unwrap();
        signed.verify(&pin, &bound, &verified, NOW).unwrap();

        let mut substitutions = Vec::new();
        let mut value = signed.clone();
        value.manifest.poa_origin = "https://evil.example".into();
        substitutions.push(value);
        let mut value = signed.clone();
        value.manifest.federation_id = "aa".repeat(32);
        substitutions.push(value);
        let mut value = signed.clone();
        value.manifest.deployment_id = "aa".repeat(32);
        substitutions.push(value);
        let mut value = signed.clone();
        value.manifest.content_pack_digest = format!("sha256:{}", "aa".repeat(32));
        substitutions.push(value);
        let mut value = signed.clone();
        value.manifest.context = CompanionContext::Youtube {
            video_id: "ZyXwVuTsR02".into(),
            channel_id: "UC_PathOfAngels".into(),
        };
        substitutions.push(value);
        let mut value = signed.clone();
        value.manifest.experience.content_assets[0].sha256 = "aa".repeat(32);
        substitutions.push(value);
        let mut value = signed.clone();
        value.manifest.experience.actions.as_mut().unwrap().mission = Some(CompanionLink {
            label: "Substituted action".into(),
            beta_url: format!("{POA_ORIGIN}/?station=field"),
        });
        substitutions.push(value);
        let mut value = signed.clone();
        value.manifest.expires_at = NOW;
        substitutions.push(value);

        for substituted in substitutions {
            assert!(substituted.verify(&pin, &bound, &verified, NOW).is_err());
        }
        let wrong_pin = CuratorKeyPin::new(&SigningKey::from_bytes(&[0x43; 32]).public_key());
        assert!(signed.verify(&wrong_pin, &bound, &verified, NOW).is_err());
        let mut wrong_signature = signed;
        wrong_signature.signature = "00".repeat(64);
        assert!(
            wrong_signature
                .verify(&pin, &bound, &verified, NOW)
                .is_err()
        );
    }
}
