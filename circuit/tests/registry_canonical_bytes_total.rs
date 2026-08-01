//! **THE CANONICAL CODEC IS TOTAL ON THE DEPLOYED REGISTRIES.**
//!
//! `descriptor_ir2_canonical::canonical_effect_vm_descriptor2_bytes` is deliberately FALLIBLE — it
//! refuses rather than truncates when an index will not fit the record's fixed `u64` width. Before
//! 2026-07-31 only two descriptors were ever round-tripped through it
//! (`descriptor_ir2_canonical.rs`'s `all_variants_roundtrip_byte_exactly` /
//! `production_exact_fnsp_v3_descriptor_roundtrips`), so "it works on the deployed set" was an
//! assumption.
//!
//! It is now load-bearing: a DERIVED welded member has no committed JSON string, so its wire
//! `vk_hash` is `blake3` of these canonical bytes
//! (`dregg_sdk::full_turn_proof::welded_descriptor_vk_hash`). If the encoder refused on any member
//! the producer would fail closed mid-turn instead of at build time. This measures the whole
//! deployed surface — the three registries the wire verifiers resolve from — on the full
//! encode → strict-decode → re-encode triangle.
//!
//! Measured 2026-07-31: **174/174**, no failures of any kind. (174, not the 171 that gets quoted:
//! `V3_STAGED_REGISTRY_TSV` carries **60** members — the 57 wide keys plus `dischargeSat` /
//! `settleEscrowSat` / `vaultSat`, which have no wide twin.)

use dregg_circuit::descriptor_ir2::parse_vm_descriptor2;
use dregg_circuit::descriptor_ir2_canonical::{
    canonical_effect_vm_descriptor2_bytes, decode_canonical_effect_vm_descriptor2,
};
use dregg_circuit::effect_vm_descriptors::{
    V3_STAGED_REGISTRY_TSV, WIDE_REGISTRY_STAGED_TSV, welded_wide_members,
};

#[test]
fn every_deployed_registry_member_roundtrips_the_canonical_codec_byte_exactly() {
    let from_tsv =
        |tsv: &'static str| -> Vec<(String, dregg_circuit::descriptor_ir2::EffectVmDescriptor2)> {
            tsv.lines()
                .filter(|l| !l.trim().is_empty())
                .map(|line| {
                    let mut it = line.splitn(3, '\t');
                    let key = it.next().expect("registry line has a key").to_string();
                    let _display = it.next();
                    let json = it.next().expect("registry line has a descriptor json");
                    let d = parse_vm_descriptor2(json)
                        .unwrap_or_else(|e| panic!("{key} must parse: {e}"));
                    (key, d)
                })
                .collect()
        };

    let sets: Vec<(&str, Vec<(String, _)>)> = vec![
        ("v3-1felt", from_tsv(V3_STAGED_REGISTRY_TSV)),
        ("wide", from_tsv(WIDE_REGISTRY_STAGED_TSV)),
        (
            "wide-umem-welded (derived)",
            welded_wide_members()
                .into_iter()
                .map(|(k, d)| (k.to_string(), d))
                .collect(),
        ),
    ];

    let mut total = 0usize;
    let mut ok = 0usize;
    // COLLECT, THEN ASSERT ONCE — a per-member `assert!` would report one failure and hide the
    // rest, which teaches the wrong size of problem.
    let mut failures: Vec<String> = Vec::new();
    for (label, members) in &sets {
        for (key, d) in members {
            total += 1;
            let bytes = match canonical_effect_vm_descriptor2_bytes(d) {
                Ok(b) => b,
                Err(e) => {
                    failures.push(format!("{label}/{key}: encode REFUSED: {e:?}"));
                    continue;
                }
            };
            let back = match decode_canonical_effect_vm_descriptor2(&bytes) {
                Ok(b) => b,
                Err(e) => {
                    failures.push(format!("{label}/{key}: strict decode REFUSED: {e:?}"));
                    continue;
                }
            };
            if back != *d {
                failures.push(format!("{label}/{key}: decode(encode(d)) != d"));
                continue;
            }
            match canonical_effect_vm_descriptor2_bytes(&back) {
                Ok(again) if again == bytes => ok += 1,
                Ok(_) => failures.push(format!("{label}/{key}: re-encode is not byte-stable")),
                Err(e) => failures.push(format!("{label}/{key}: re-encode REFUSED: {e:?}")),
            }
        }
    }

    assert!(
        failures.is_empty(),
        "{} of {total} deployed registry members do NOT survive the canonical codec. Every failure \
         is listed so the next reader fixes all of them:\n{}",
        failures.len(),
        failures.join("\n")
    );
    assert_eq!(
        (total, ok),
        (174, 174),
        "the deployed surface is 60 v3-1felt + 57 wide + 57 derived welded members, and ALL of them \
         must round-trip (a member that does not would fail the welded vk_hash closed at prove time)"
    );
}

/// Distinct descriptors get distinct canonical bytes — the property the welded `vk_hash` needs to
/// be a descriptor IDENTITY at all. The sharpest pair available: a bare wide member and its own
/// welded twin, which differ by exactly the weld.
#[test]
fn a_welded_member_and_its_bare_host_have_distinct_canonical_bytes() {
    let mut checked = 0usize;
    for (key, welded) in welded_wide_members() {
        let bare_json = WIDE_REGISTRY_STAGED_TSV
            .lines()
            .find_map(|line| {
                let mut it = line.splitn(3, '\t');
                if it.next() == Some(key) {
                    let _display = it.next();
                    it.next()
                } else {
                    None
                }
            })
            .unwrap_or_else(|| panic!("{key} is a bare wide registry key"));
        let bare = parse_vm_descriptor2(bare_json).expect("bare parses");
        assert_ne!(
            canonical_effect_vm_descriptor2_bytes(&bare).expect("bare encodes"),
            canonical_effect_vm_descriptor2_bytes(&welded).expect("welded encodes"),
            "{key}: the welded twin must not share the bare member's descriptor identity"
        );
        checked += 1;
    }
    assert_eq!(checked, 57);
}
