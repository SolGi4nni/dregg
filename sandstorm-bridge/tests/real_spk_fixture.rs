//! **The catalog `.spk` differential harness — the real Cap'n Proto `Archive` wire.**
//!
//! This harness asserts the real end-to-end parse against a genuinely-signed `.spk`:
//! the canonical container header, the *combined* Ed25519/SHA-512 signature, the App
//! ID intrinsic to the signing key, the genuine multi-segment capnp `Archive` file
//! tree, the capnp `Manifest`, and that a tampered package is refused.
//!
//! The signed package is **self-contained**: it is minted in-test via the real
//! packer ([`SpkBuilder::pack`]) — real xz container, real capnp `Signature` +
//! `Archive` messages, real combined Ed25519/SHA-512 signature — so the anti-tamper
//! and parse teeth RUN unconditionally in CI, never silent-return. Historically this
//! harness loaded `fixtures/sample.spk` and *skipped clean* when the artifact was not
//! checked out, which meant each tooth reported GREEN while asserting nothing. It no
//! longer does: absence of the real artifact falls back to the minted package, so the
//! security guarantee is always exercised.
//!
//! When the real catalog artifact IS checked out at `fixtures/sample.spk` (the
//! "Simple Todos" Meteor http-bridge app), the harness additionally asserts its
//! ground truth as a differential:
//!   - App ID `0dp7n6ehj8r5ttfc0fj0au6gxkuy1nhw2kx70wussfa1mqj8tf80` = base32(pubkey);
//!   - a populated top-level tree (regular/executable/symlink/directory all present),
//!     including `sandstorm-manifest`, the `sandstorm-http-bridge` executable, `main.js`;
//!   - the manifest decodes to title "Simple Todos", appVersion 5, the http-bridge
//!     `continueCommand` (`/sandstorm-http-bridge 8000 -- …`) → ingress port 8000.

use std::path::PathBuf;

use ed25519_dalek::SigningKey;
use sandstorm_bridge::manifest::SpkManifest;
use sandstorm_bridge::spk::{base32, File, FileContent, Spk, SpkBuilder, SpkError, SPK_MAGIC};

fn fixture_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("fixtures")
        .join("sample.spk")
}

/// A genuinely-signed, self-contained `.spk` minted in-test through the real packer.
///
/// This is the *real wire*, not a projection: `magic ++ xz(capnp Signature ++ capnp
/// Archive)`, with a combined libsodium `crypto_sign` over `SHA-512` of the archive
/// (`[ed25519 sig : 64][SHA-512 : 64]`). The chroot tree carries every `File` union
/// member the reader must discriminate — a Regular (`sandstorm-manifest`), an
/// Executable (`sandstorm-http-bridge`), and a Directory with nested entries — so the
/// composite-list, union-tag, and nested-tree decode paths are exercised. A fixed
/// signing seed makes the App ID deterministic across runs (Ed25519 signing is
/// deterministic, so no RNG is needed). Because it is minted every run it can never go
/// stale nor silent-return.
fn minted_spk() -> Vec<u8> {
    // An http-bridge manifest (JSON projection; `from_spk` decodes JSON or capnp and
    // overrides the app id with the signing key). `bridge_config` present → http-bridge;
    // `api_port` 8000 → the recovered ingress port.
    let manifest = r#"{
      "app_id": "overridden-by-the-signing-key",
      "app_title": "dregg Grain Fixture",
      "app_version": 7,
      "continue_command": { "argv": ["/sandstorm-http-bridge", "8000", "--", "/start.sh"] },
      "bridge_config": { "api_port": 8000, "permissions": ["view", "edit"], "roles": [] }
    }"#;
    SpkBuilder::new()
        .manifest_json(manifest)
        .file(File::executable(
            "sandstorm-http-bridge",
            b"#!/bin/sh\nexec /app/server\n".to_vec(),
        ))
        .file(File::regular("main.js", b"// app entry\n".to_vec()))
        .file(File {
            name: "var".into(),
            content: FileContent::Directory(vec![
                File::regular("state.db", b"<state>".to_vec()),
                File::regular("log", b"<log>".to_vec()),
            ]),
            mtime_ns: 0,
        })
        .pack(&SigningKey::from_bytes(&[7u8; 32]))
}

/// The signed `.spk` under test and whether it is the real catalog artifact.
///
/// Prefers the real catalog package at `fixtures/sample.spk` when it is checked out
/// (so the "Simple Todos" ground truth is asserted as a differential); otherwise falls
/// back to the self-contained minted package so the teeth always run. The `bool` is
/// `true` iff the bytes are the real third-party artifact.
fn sample_spk() -> (Vec<u8>, bool) {
    match std::fs::read(fixture_path()) {
        Ok(b) => (b, true),
        Err(_) => (minted_spk(), false),
    }
}

#[test]
fn a_real_catalog_spk_parses_end_to_end_on_the_real_wire() {
    let (bytes, is_real) = sample_spk();

    // The container header is the canonical Sandstorm magic.
    assert!(
        bytes.starts_with(&SPK_MAGIC),
        "a real .spk must begin with the canonical magic 8fc6cdef…; got {:02x?}",
        &bytes[..bytes.len().min(8)]
    );

    // The whole real parse: magic → xz → capnp Signature → combined Ed25519/SHA-512
    // verify over the archive → capnp Archive. A failure here would mean the signature
    // did not bind, or the capnp wire did not decode — both are hard errors.
    let spk = Spk::parse(&bytes).expect("the catalog .spk parses + verifies");

    // The App ID is intrinsic to the signing key (no CA, no manifest claim).
    assert_eq!(
        spk.app_id().0,
        base32(&spk.public_key),
        "App ID is the base32 of the signing public key"
    );

    // The genuine multi-segment capnp Archive file tree extracted. Multiple File union
    // members are represented (regular, executable, directory) — proof the discriminant
    // + nested composite lists decode against a real, far-pointer-bearing message.
    let top = &spk.archive.files;
    let named = |n: &str| top.iter().find(|f| f.name == n);
    assert!(matches!(
        named("sandstorm-manifest").map(|f| &f.content),
        Some(FileContent::Regular(_))
    ));
    assert!(matches!(
        named("sandstorm-http-bridge").map(|f| &f.content),
        Some(FileContent::Executable(_))
    ));
    assert!(
        top.iter()
            .any(|f| matches!(f.content, FileContent::Directory(_))),
        "the package has directories (var/proc/…)"
    );
    // The nested directory tree decoded.
    let nested: usize = top
        .iter()
        .filter_map(|f| match &f.content {
            FileContent::Directory(sub) => Some(sub.len()),
            _ => None,
        })
        .sum();
    assert!(nested > 0, "nested directory entries decoded");
    // File lookup resolves a regular file's bytes.
    assert!(spk.archive.find("sandstorm-manifest").is_some());

    // The manifest is a real capnp/JSON `Manifest` message; decode it.
    let manifest = SpkManifest::from_spk(&spk).expect("decode the manifest");
    assert_eq!(
        manifest.app_id,
        spk.app_id(),
        "manifest App ID = signing key"
    );
    assert_eq!(
        manifest.continue_command.argv.first().map(String::as_str),
        Some("/sandstorm-http-bridge")
    );
    assert!(manifest.is_http_bridge(), "an http-bridge catalog app");

    // The derived grain spec routes the http-bridge app to the strong-isolation tier
    // with the recovered ingress port.
    let spec = manifest.grain_spec();
    assert_eq!(spec.ingress_port, Some(8000));
    assert_eq!(spec.app_version, manifest.app_version);

    if is_real {
        // Ground truth for the real "Simple Todos" catalog artifact — asserted only
        // when the third-party package is checked out (it is intentionally not committed).
        assert_eq!(
            spk.app_id().0,
            "0dp7n6ehj8r5ttfc0fj0au6gxkuy1nhw2kx70wussfa1mqj8tf80"
        );
        assert!(
            top.len() >= 15,
            "a real package has a populated top-level tree (got {})",
            top.len()
        );
        assert_eq!(manifest.app_title, "Simple Todos");
        assert_eq!(manifest.app_version, 5);
        assert_eq!(spec.app_version, 5);
    }
}

#[test]
fn a_tampered_real_spk_is_refused() {
    let (mut bytes, _is_real) = sample_spk();

    // Non-vacuity baseline: the untampered package MUST parse + verify first. Without
    // this, a package that failed to parse for an unrelated reason would make the
    // rejection below pass for the WRONG reason (tamper-rejection silently disabled).
    Spk::parse(&bytes).expect("the honest package parses + verifies before we tamper it");

    // Flip a byte deep inside the xz container — this corrupts the compressed archive,
    // so either xz decompression fails its integrity check or the recomputed SHA-512 no
    // longer matches the signed hash. Either way no launchable image is returned.
    let n = bytes.len();
    bytes[n / 2] ^= 0xff;
    match Spk::parse(&bytes) {
        Err(SpkError::BadSignature)
        | Err(SpkError::Decompress(_))
        | Err(SpkError::Archive(_))
        | Err(SpkError::TooLarge)
        | Err(SpkError::Truncated) => {}
        other => panic!("a tampered .spk was not refused: {other:?}"),
    }
}
