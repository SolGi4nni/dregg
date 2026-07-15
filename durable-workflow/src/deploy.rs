//! `deploy` — the launchpad seam: a launch is a durable metered workflow **plus** a
//! content-addressed landing page and token metadata.
//!
//! A "launch" on the substrate is two things at once, and this module makes them one
//! receipt:
//!
//! 1. a **durable, metered build/deploy workflow** ([`WorkloadRun`]) — the steps that
//!    stand the thing up, each checkpointed and charged exactly-once (the rest of this
//!    crate);
//! 2. a **content-addressed microsite** (the landing page a launch gets) and
//!    **content-addressed token metadata/image** — every asset pinned to IPFS, its
//!    address a blake3 CIDv1 that anyone re-witnesses against the bytes.
//!
//! The content-addressing is the real `dregg-ipfs` bridge: a dregg blake3 content
//! commitment *is* an IPFS CIDv1, so a pinned asset's CID is its commitment — no
//! second identity. The token metadata JSON references its image by `ipfs://<cid>`,
//! so the whole launch is content-addressed end to end and served from any gateway,
//! re-verifiable against the receipt.
//!
//! [`pin_launch_content`] does the pinning over any injected [`IpfsClient`] (the
//! in-process `MockIpfs` in tests, a real daemon in production) — no durable store
//! needed. [`deploy_launch`] (feature `sqlite`) additionally runs the durable metered
//! workflow, returning one [`LaunchReceipt`] that carries both halves.

use dregg_ipfs::{pin_blob, IpfsClient, IpfsError};
use serde::{Deserialize, Serialize};

use crate::WorkloadRun;

/// One named microsite asset (a stylesheet, an image, a script) — pinned by content.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MicrositeAsset {
    /// The site-relative path the asset is referenced at (e.g. `"style.css"`).
    pub path: String,
    pub bytes: Vec<u8>,
}

/// The landing page a launch gets: an index document plus its named assets.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Microsite {
    /// The landing page document bytes (HTML).
    pub index_html: Vec<u8>,
    #[serde(default)]
    pub assets: Vec<MicrositeAsset>,
}

impl Microsite {
    /// A one-page microsite with no extra assets.
    pub fn page(index_html: impl Into<Vec<u8>>) -> Microsite {
        Microsite {
            index_html: index_html.into(),
            assets: Vec::new(),
        }
    }
}

/// The token a launch mints: its display metadata + image bytes. The image and the
/// assembled metadata JSON are both content-addressed on IPFS.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TokenMetadata {
    pub name: String,
    pub symbol: String,
    #[serde(default)]
    pub description: String,
    /// The token image bytes (pinned; the metadata references it by `ipfs://<cid>`).
    pub image: Vec<u8>,
}

/// The full description of a launch: what to build (the durable workflow), the
/// landing page, and the token.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LaunchSpec {
    pub workflow: WorkloadRun,
    pub microsite: Microsite,
    pub token: TokenMetadata,
}

/// A pinned asset: its site path and its content CID (a blake3 CIDv1 string).
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct PinnedAsset {
    pub path: String,
    pub cid: String,
}

/// The content-addressed half of a launch: every asset's CID + the assembled,
/// content-addressed token metadata. Each CID re-witnesses its bytes.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct LaunchContent {
    /// The landing page document's CID.
    pub site_cid: String,
    /// The microsite's named assets, pinned.
    pub assets: Vec<PinnedAsset>,
    /// The token image's CID.
    pub image_cid: String,
    /// The assembled token metadata JSON's CID (references `image_cid` by ipfs URI).
    pub token_metadata_cid: String,
    /// The assembled token metadata JSON itself (what `token_metadata_cid` addresses).
    pub token_metadata_json: String,
}

/// Pin a launch's content to IPFS and assemble its content-addressed token metadata,
/// over any injected [`IpfsClient`]. Pure content-addressing — no durable store, no
/// network beyond the client. Returns every CID so a caller re-witnesses each asset
/// against its address.
///
/// The token metadata JSON is standard `{name, symbol, description, image}` with the
/// image as an `ipfs://<image_cid>` URI, so a wallet or explorer resolves the image
/// content-addressed from the metadata.
pub fn pin_launch_content<C: IpfsClient>(
    client: &C,
    microsite: &Microsite,
    token: &TokenMetadata,
) -> Result<LaunchContent, IpfsError> {
    // The landing page + each named asset, pinned by content.
    let site_cid = pin_blob(client, &microsite.index_html)?.to_string_cid();
    let mut assets = Vec::with_capacity(microsite.assets.len());
    for a in &microsite.assets {
        let cid = pin_blob(client, &a.bytes)?.to_string_cid();
        assets.push(PinnedAsset {
            path: a.path.clone(),
            cid,
        });
    }

    // The token image, then the metadata that references it content-addressed.
    let image_cid = pin_blob(client, &token.image)?.to_string_cid();
    let metadata = serde_json::json!({
        "name": token.name,
        "symbol": token.symbol,
        "description": token.description,
        "image": format!("ipfs://{image_cid}"),
    });
    // Canonical bytes so the metadata CID is stable for identical metadata.
    let token_metadata_json = serde_json::to_string(&metadata)
        .map_err(|e| IpfsError::Transport(format!("token metadata encode: {e}")))?;
    let token_metadata_cid = pin_blob(client, token_metadata_json.as_bytes())?.to_string_cid();

    Ok(LaunchContent {
        site_cid,
        assets,
        image_cid,
        token_metadata_cid,
        token_metadata_json,
    })
}

/// The receipt of a completed launch: the content-addressed page + token, and the
/// durable metered workflow's output.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct LaunchReceipt {
    pub content: LaunchContent,
    pub workflow: crate::WorkflowOutput,
}

/// Run a full launch: pin its content-addressed landing page + token metadata, then
/// run its durable, exactly-once-metered workflow on disk under `instance` at
/// `db_path`, driving steps through `runner`. Returns one [`LaunchReceipt`] carrying
/// both halves.
///
/// Crash-safety carries through: the content pinning is idempotent (a re-pin of the
/// same bytes yields the same CID), and the workflow half is the crate's on-disk
/// crash-resume path — a launch that crashed mid-build resumes exactly-once.
#[cfg(feature = "sqlite")]
pub fn deploy_launch<C: IpfsClient>(
    client: &C,
    launch: &LaunchSpec,
    instance: &str,
    db_path: &std::path::Path,
    runner: std::sync::Arc<dyn crate::StepRunner>,
) -> Result<LaunchReceipt, String> {
    let content = pin_launch_content(client, &launch.microsite, &launch.token)
        .map_err(|e| format!("deploy: pin launch content: {e}"))?;
    let workflow =
        crate::run_workflow_on_disk_blocking(&launch.workflow, instance, db_path, runner)?;
    Ok(LaunchReceipt { content, workflow })
}
