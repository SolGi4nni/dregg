//! The launchpad seam (feature `deploy`): a launch pins a content-addressed landing
//! page + token metadata to IPFS and runs its durable metered workflow, in one
//! receipt — and every asset re-witnesses against its CID.

#![cfg(feature = "deploy")]

use std::sync::Arc;

use dregg_ipfs::{fetch_verified, Cid, MockIpfs};
use durable_workflow::deploy::{
    deploy_launch, pin_launch_content, LaunchSpec, Microsite, MicrositeAsset, TokenMetadata,
};
use durable_workflow::{ExprRunner, WorkloadRun, WorkloadSpec};
use tempfile::tempdir;

fn a_token() -> TokenMetadata {
    TokenMetadata {
        name: "Example Launch".to_string(),
        symbol: "EXL".to_string(),
        description: "a substrate launch".to_string(),
        image: b"\x89PNG\r\n\x1a\n<fake png bytes>".to_vec(),
    }
}

fn a_microsite() -> Microsite {
    Microsite {
        index_html: b"<!doctype html><title>Example Launch</title><h1>hello</h1>".to_vec(),
        assets: vec![MicrositeAsset {
            path: "style.css".to_string(),
            bytes: b"body{font-family:system-ui}".to_vec(),
        }],
    }
}

#[test]
fn pins_content_addressed_and_re_witnesses() {
    let ipfs = MockIpfs::new();
    let site = a_microsite();
    let token = a_token();
    let content = pin_launch_content(&ipfs, &site, &token).unwrap();

    // Every CID is the blake3 content commitment of its bytes: re-fetch verified.
    let site_cid = Cid::parse(&content.site_cid).unwrap();
    assert_eq!(fetch_verified(&ipfs, &site_cid).unwrap(), site.index_html);

    assert_eq!(content.assets.len(), 1);
    assert_eq!(content.assets[0].path, "style.css");
    let asset_cid = Cid::parse(&content.assets[0].cid).unwrap();
    assert_eq!(
        fetch_verified(&ipfs, &asset_cid).unwrap(),
        site.assets[0].bytes
    );

    let img_cid = Cid::parse(&content.image_cid).unwrap();
    assert_eq!(fetch_verified(&ipfs, &img_cid).unwrap(), token.image);

    // The token metadata references its image content-addressed (`ipfs://<cid>`).
    let meta: serde_json::Value = serde_json::from_str(&content.token_metadata_json).unwrap();
    assert_eq!(meta["name"], "Example Launch");
    assert_eq!(meta["image"], format!("ipfs://{}", content.image_cid));
    // And the metadata JSON itself is pinned at its own CID.
    let meta_cid = Cid::parse(&content.token_metadata_cid).unwrap();
    assert_eq!(
        fetch_verified(&ipfs, &meta_cid).unwrap(),
        content.token_metadata_json.as_bytes()
    );
}

#[test]
fn content_addressing_is_deterministic() {
    // Identical content pins to identical CIDs (idempotent launches).
    let a = pin_launch_content(&MockIpfs::new(), &a_microsite(), &a_token()).unwrap();
    let b = pin_launch_content(&MockIpfs::new(), &a_microsite(), &a_token()).unwrap();
    assert_eq!(a, b);
}

#[test]
fn tamper_is_refused_on_fetch() {
    let ipfs = MockIpfs::new();
    let content = pin_launch_content(&ipfs, &a_microsite(), &a_token()).unwrap();
    let site_cid = Cid::parse(&content.site_cid).unwrap();
    // A lying node swaps the bytes under the CID; the content-address check refuses.
    ipfs.tamper(&site_cid, b"<h1>evil</h1>");
    assert!(fetch_verified(&ipfs, &site_cid).is_err());
}

#[test]
fn full_launch_composes_content_and_durable_workflow() {
    let dir = tempdir().unwrap();
    let db = dir.path().join("launch.db");
    let launch = LaunchSpec {
        workflow: WorkloadRun::new(100, 5, vec![WorkloadSpec::expr("build", "7 * 6")]),
        microsite: a_microsite(),
        token: a_token(),
    };
    let ipfs = MockIpfs::new();
    let receipt = deploy_launch(&ipfs, &launch, "launch-1", &db, Arc::new(ExprRunner)).unwrap();

    // The durable workflow ran + metered.
    assert_eq!(receipt.workflow.outputs, vec!["42".to_string()]);
    assert_eq!(receipt.workflow.meter_units, 5);
    // The landing page is content-addressed + re-witnessable.
    let site_cid = Cid::parse(&receipt.content.site_cid).unwrap();
    assert_eq!(
        fetch_verified(&ipfs, &site_cid).unwrap(),
        launch.microsite.index_html
    );
}
