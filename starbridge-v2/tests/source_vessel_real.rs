//! END-TO-END proof of the self-describing vessel OVER THE REAL SOURCE.
//!
//! Packs the ACTUAL dregg source (via `scripts/pack-dregg-src.sh`) into a real
//! `dregg-src.tar.zst` carrier, opens it through [`SourceVessel`] exactly as the
//! shipped image will, and reads a REAL dregg source file from within — proving
//! deos can describe itself by RUNNING, not just compiling.
//!
//! This is the "VERIFY BY RUNNING" half: a source file
//! (`metatheory/CONSTRUCTIVE-KNOWLEDGE.md` and `dregg-lean-ffi/src/lib.rs`) is
//! readable from within deos over the carrier the AppImage ships.

use std::path::PathBuf;
use std::process::Command;

use starbridge_v2::source_vessel::SourceVessel;

/// Repo root = two levels up from this crate's manifest dir (starbridge-v2/).
fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .to_path_buf()
}

#[test]
fn reads_a_real_dregg_source_file_from_within_the_vessel() {
    let root = repo_root();
    let packer = root.join("scripts/pack-dregg-src.sh");
    assert!(packer.is_file(), "the packer must exist at {}", packer.display());

    // Pack the REAL source into a carrier in a temp location (the same artifact
    // the AppImage job drops into usr/share/dregg-src/).
    let out_dir = std::env::temp_dir().join(format!(
        "dregg-src-vessel-e2e-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir_all(&out_dir).unwrap();
    let carrier = out_dir.join("dregg-src.tar.zst");

    let status = Command::new("bash")
        .arg(&packer)
        .arg(&carrier)
        .current_dir(&root)
        .status()
        .expect("running the packer");
    assert!(status.success(), "the packer must succeed");
    assert!(carrier.is_file(), "the carrier must be produced");

    // OPEN THE VESSEL exactly as the shipped image does (open a carrier on disk).
    let vessel = SourceVessel::open(&carrier).expect("opening the real source vessel");

    // It carries a substantial corpus — the whole definitional source.
    assert!(
        vessel.len() > 1000,
        "the vessel should carry thousands of source files, got {}",
        vessel.len()
    );

    // THE PROOF: read a REAL dregg source file from within and get its real
    // content. The metatheory's constructive-knowledge writeup — the document the
    // owner named as the thing the agent most needs to understand what it is.
    let ck = vessel
        .read("metatheory/CONSTRUCTIVE-KNOWLEDGE.md")
        .expect("the metatheory constructive-knowledge doc must be readable from within");
    assert!(
        ck.contains("constructive knowledge"),
        "the read must return the REAL content of CONSTRUCTIVE-KNOWLEDGE.md"
    );
    // Cross-check the in-vessel read against the real on-disk file byte-for-byte.
    let on_disk =
        std::fs::read_to_string(root.join("metatheory/CONSTRUCTIVE-KNOWLEDGE.md")).unwrap();
    assert_eq!(
        ck, on_disk,
        "the vessel read must MATCH the real source on disk, byte-for-byte"
    );

    // And the Lean FFI bridge source — the crate that defines the verified link.
    let ffi = vessel
        .read("dregg-lean-ffi/src/lib.rs")
        .expect("the lean-ffi source must be readable from within");
    assert_eq!(
        ffi,
        std::fs::read_to_string(root.join("dregg-lean-ffi/src/lib.rs")).unwrap(),
        "the lean-ffi source read from within matches the real source"
    );

    // The confinement holds even over the real carrier (a `..` escape is refused).
    assert!(vessel.read("../../../etc/passwd").is_err());

    println!(
        "self-describing vessel: read {} source files ({} bytes of definition) from within; \
         CONSTRUCTIVE-KNOWLEDGE.md + dregg-lean-ffi/src/lib.rs match disk byte-for-byte",
        vessel.len(),
        vessel.total_bytes()
    );

    let _ = std::fs::remove_dir_all(&out_dir);
}
