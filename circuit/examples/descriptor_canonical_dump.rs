//! ⚑ **THE RUST HALF OF THE BLAKE3 DIFFERENTIAL.** Dumps, for every DescriptorIR-v2 record this
//! tree serves, the record's canonical bytes and the fingerprint the deployed library computes over
//! them — so a second implementation can be asked the same question about the same inputs.
//!
//! The consumer is `scripts/check-blake3-differential.sh`, which feeds this to
//! `Dregg2.Crypto.Blake3.blake3Derive` (pure Lean) and refuses on any disagreement.
//!
//! ⚑ **IT IS RECOMPUTED ON EVERY RUN AND NEVER COMMITTED.** A frozen fixture of expected
//! fingerprints would be the exact defect this whole pass exists to kill: a derived value written
//! down once, going stale where nothing looks. Both sides are computed fresh, from the descriptors
//! on disk, every time the gate runs.
//!
//! ⚠ The fingerprint comes from [`effect_vm_descriptor2_semantic_fingerprint`] — the deployed
//! function, not a local re-spelling of it. If this file computed its own hash the differential
//! would compare two copies of the same mistake.
//!
//! Output is TSV on stdout, one record per line:
//!
//! ```text
//! <name>\t<display path>\t<canonical hex>\t<fingerprint hex>\t<l0,l1,…,l8>
//! ```
//!
//! ⚑ The trailing field is the fingerprint's nine base-`2^29` lanes — **the `vk_pin` value itself**,
//! from the library's [`key_limbs9`]. It is here so the differential covers the WHOLE pin
//! computation (`canonical bytes → fingerprint → nine lanes`) rather than only its hash step: the
//! Lean side re-derives them with `Dregg2.Circuit.KeyLanes9.keyToLanes9`, the Lean-authored encoder
//! the AIRs are proved against, so the lane transcription is gated on the same 158 real inputs.
//!
//! `DREGG_DESCRIPTOR_ROOT` retargets the walk at a materialised tree, exactly as
//! `vk_pin_closure_over_the_served_tree` does — in a shared working directory a sibling lane's
//! uncommitted re-emit otherwise makes the verdict a fact about *that lane's tree*.

use std::path::{Path, PathBuf};

use dregg_circuit::descriptor_ir2::parse_vm_descriptor2;
use dregg_circuit::descriptor_ir2_canonical::{
    canonical_effect_vm_descriptor2_bytes, effect_vm_descriptor2_semantic_fingerprint,
};
use dregg_circuit::effect_vm::key_limbs9;

fn hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push_str(&format!("{b:02x}"));
    }
    s
}

/// Recurses. A dump that read only `descriptors/` and `descriptors/by-name/` would silently leave
/// `table-airs/` and `seams/` out of the differential.
fn collect_json(dir: &Path, root: &Path, out: &mut Vec<(String, String)>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_json(&path, root, out);
            continue;
        }
        if !path.is_file() || path.extension().and_then(|e| e.to_str()) != Some("json") {
            continue;
        }
        // PROVENANCE.json is the manifest, not a descriptor.
        if path.file_name().and_then(|n| n.to_str()) == Some("PROVENANCE.json") {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(&path) else {
            continue;
        };
        let display = path
            .strip_prefix(root)
            .unwrap_or(&path)
            .to_string_lossy()
            .into_owned();
        out.push((display, text));
    }
}

fn main() {
    let root = match std::env::var("DREGG_DESCRIPTOR_ROOT") {
        Ok(p) => PathBuf::from(p),
        Err(_) => PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("descriptors"),
    };
    let mut files = Vec::new();
    collect_json(&root, &root, &mut files);
    files.sort();

    let mut emitted = 0usize;
    for (display, text) in &files {
        let Ok(d) = parse_vm_descriptor2(text) else {
            continue;
        };
        let Ok(bytes) = canonical_effect_vm_descriptor2_bytes(&d) else {
            eprintln!("descriptor_canonical_dump: {display} has no canonical encoding");
            std::process::exit(2);
        };
        let Ok(fp) = effect_vm_descriptor2_semantic_fingerprint(&d) else {
            eprintln!("descriptor_canonical_dump: {display} has no fingerprint");
            std::process::exit(2);
        };
        let lanes = key_limbs9(&fp)
            .iter()
            .map(|l| l.as_u32().to_string())
            .collect::<Vec<_>>()
            .join(",");
        println!(
            "{}\t{}\t{}\t{}\t{}",
            d.name,
            display,
            hex(&bytes),
            hex(&fp),
            lanes
        );
        emitted += 1;
    }

    // A dump that walked nothing would make the differential pass vacuously; the consumer checks a
    // floor too, but the producer refuses first.
    if emitted == 0 {
        eprintln!(
            "descriptor_canonical_dump: walked {} files under {} and parsed ZERO ir:2 descriptors — refusing to emit an empty differential",
            files.len(),
            root.display()
        );
        std::process::exit(2);
    }
    eprintln!(
        "descriptor_canonical_dump: {emitted} ir:2 descriptors from {} files under {}",
        files.len(),
        root.display()
    );
}
