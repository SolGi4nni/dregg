//! Lean→Rust wire canary for the staged PQ-identity rotation authority row.
//!
//! The descriptor remains authored in Lean.  This test extracts the byte-pinned
//! `PQ_IDENTITY_ROTATION_GOLDEN` directly from the Lean module and asks the
//! production Rust IR2 parser to consume it.  The assertions below establish
//! wire compatibility and shape drift detection only; semantic faithfulness is
//! proved by `PqIdentityAuthorityEmit.satisfied_implies_exact_rotation` in Lean.
//! In particular, parsing this artifact does not make the row deployable and
//! does not discharge either ML-DSA premise.

use dregg_circuit::descriptor_ir2::parse_vm_descriptor2;

const LEAN_SOURCE: &str =
    include_str!("../../metatheory/Dregg2/Circuit/Emit/PqIdentityAuthorityEmit.lean");

fn lean_golden() -> &'static str {
    const OPEN: &str = "def PQ_IDENTITY_ROTATION_GOLDEN : String := r#\"";
    let (_, after_open) = LEAN_SOURCE
        .split_once(OPEN)
        .expect("Lean module still exposes the PQ identity golden");
    let (json, _) = after_open
        .split_once("\"#\n")
        .expect("Lean PQ identity golden remains a raw string");
    json
}

#[test]
fn lean_pq_identity_rotation_golden_parses_with_exact_shape() {
    let desc = parse_vm_descriptor2(lean_golden())
        .expect("Lean-emitted PQ identity rotation descriptor parses as IR2");

    assert_eq!(desc.name, "dregg-pq-identity-rotation::v1");
    assert_eq!(desc.trace_width, 127);
    assert_eq!(desc.public_input_count, 108);
    assert_eq!(desc.constraints.len(), 120);
    assert_eq!(desc.ranges.len(), 111);
    assert!(desc.tables.is_empty());
    assert!(desc.hash_sites.is_empty());
}
