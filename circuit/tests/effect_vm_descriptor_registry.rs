//! Integration drift-guard for the Lean-emitted EffectVM descriptor registry.
//!
//! Binds the Rust registry (`effect_vm_descriptors`) to the verified Lean
//! `emitVmJson` bytes: every registered descriptor must (a) parse through the
//! running interpreter `parse_vm_descriptor` and (b) match its committed SHA-256
//! fingerprint. This is the CI anti-drift tooth — a Lean re-emit that changes a
//! descriptor (or a stale committed `circuit/descriptors/*.json`) fails here.
//!
//! The byte-exact fingerprint check lives in the in-module unit test
//! (`effect_vm_descriptors::tests::all_descriptors_parse_and_match_fingerprint`,
//! which carries the self-contained SHA-256). This integration test exercises the
//! PUBLIC registry API the call-site cutover will use: `descriptor_for_selector`,
//! `descriptor_for_name`, and the selector-table consistency.

use dregg_circuit::effect_vm::columns::sel;
use dregg_circuit::effect_vm_descriptors::{
    descriptor_for_name, descriptor_for_selector, descriptor_name_for_selector,
    fingerprint_for_name, ALL_DESCRIPTORS, NAME_ONLY_DESCRIPTORS, SELECTOR_DESCRIPTORS,
};
use dregg_circuit::lean_descriptor_air::parse_vm_descriptor;

/// Every descriptor reachable via the public API parses through the running
/// EffectVM interpreter, and the parsed `name` round-trips the registry key.
#[test]
fn every_registered_descriptor_parses() {
    assert_eq!(ALL_DESCRIPTORS.len(), 47, "expected 47 unique descriptors");
    for (name, json, fp) in ALL_DESCRIPTORS {
        let by_name = descriptor_for_name(name).expect("name must resolve");
        assert_eq!(*json, by_name, "{name}: descriptor_for_name mismatch");
        assert_eq!(
            Some(*fp),
            fingerprint_for_name(name),
            "{name}: fingerprint_for_name mismatch"
        );
        let desc = parse_vm_descriptor(json)
            .unwrap_or_else(|e| panic!("{name} failed to parse via interpreter: {e}"));
        assert_eq!(&desc.name, name, "{name}: parsed name != registry key");
        assert_eq!(
            desc.trace_width, 186,
            "{name}: all EffectVM descriptors share the 186-col base trace"
        );
    }
}

/// The selector → descriptor lookup the dispatcher will use: every selector with a
/// registered descriptor resolves to a parseable JSON; the transfer selector
/// resolves to the transfer descriptor; an unregistered selector yields `None`.
#[test]
fn selector_lookup_drives_the_dispatcher() {
    for (s, name, json, _fp) in SELECTOR_DESCRIPTORS {
        assert_eq!(descriptor_for_selector(*s), Some(*json), "selector {s}");
        assert_eq!(descriptor_name_for_selector(*s), Some(*name), "selector {s}");
        parse_vm_descriptor(json)
            .unwrap_or_else(|e| panic!("selector {s} ({name}) failed to parse: {e}"));
    }
    // 44 selectors carry a descriptor; a few share one JSON (e.g. GRANT_CAP /
    // REVOKE_DELEGATION / INTRODUCE / ATTENUATE_CAPABILITY all map to the `attenuateA`
    // cap-move JSON), so the 44 selector rows reference 43 distinct descriptor names.
    assert_eq!(SELECTOR_DESCRIPTORS.len(), 44);
    let distinct_names: std::collections::BTreeSet<&str> =
        SELECTOR_DESCRIPTORS.iter().map(|(_, n, _, _)| *n).collect();
    assert_eq!(distinct_names.len(), 43);

    // The transfer beachhead: selector 1 → the verified transfer descriptor.
    assert_eq!(
        descriptor_name_for_selector(sel::TRANSFER),
        Some("dregg-effectvm-transfer-v1")
    );
    // NoOp / SET_FIELD have no emitted descriptor yet.
    assert_eq!(descriptor_for_selector(sel::NOOP), None);
    assert_eq!(descriptor_for_selector(sel::SET_FIELD), None);

    // The shared cap-root-move object: ATTENUATE_CAPABILITY and GRANT_CAP (the
    // unattenuated cap-root grant = the attenuate template) dispatch to the SAME verified
    // JSON. (REVOKE_DELEGATION and INTRODUCE were graduated onto their OWN frozen-frame +
    // nonce-tick descriptors — `revokeDelegation-v2` / `introduce-v2` — with the cap-table
    // move/grant bound OFF-row, so they no longer share the attenuate JSON.)
    let att = descriptor_for_selector(sel::ATTENUATE_CAPABILITY);
    assert!(att.is_some());
    assert_eq!(descriptor_for_selector(sel::GRANT_CAP), att);
    assert_eq!(
        descriptor_name_for_selector(sel::REVOKE_DELEGATION),
        Some("dregg-effectvm-revokeDelegation-v2")
    );
    assert_eq!(
        descriptor_name_for_selector(sel::INTRODUCE),
        Some("dregg-effectvm-introduce-v2")
    );
}

/// The 3 name-only descriptors (`mint`, `swissDropA`, `swissHandoffA`) are real,
/// parse, and are reachable by name — they simply lack a dedicated Rust selector.
#[test]
fn name_only_descriptors_are_real() {
    assert_eq!(NAME_ONLY_DESCRIPTORS.len(), 3);
    for (name, json, _fp) in NAME_ONLY_DESCRIPTORS {
        assert_eq!(descriptor_for_name(name), Some(*json));
        parse_vm_descriptor(json)
            .unwrap_or_else(|e| panic!("name-only {name} failed to parse: {e}"));
        assert!(
            SELECTOR_DESCRIPTORS.iter().all(|(_, n, _, _)| n != name),
            "{name} should not be selector-bound"
        );
    }
}
