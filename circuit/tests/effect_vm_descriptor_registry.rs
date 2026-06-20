//! Integration test for the Lean-emitted EffectVM descriptor registry.
//!
//! Exercises the PUBLIC registry API the call-site cutover uses
//! (`descriptor_for_selector`, `descriptor_for_name`, selector-table consistency):
//! every registered descriptor must parse through the running interpreter
//! `parse_vm_descriptor` into the structure the prover consumes.
//!
//! The Lean↔JSON drift gate is GENERATE-FRESH: `scripts/check-descriptor-drift.sh`
//! re-runs the Lean emitters and diffs against the checked-in artifacts. (A
//! `sha256(bytes) == committed-FP` rehash proves only that a file matches the hash
//! committed beside it — self-consistency, not that it still equals the Lean
//! emission — so it is not exercised here.)

use dregg_circuit::effect_vm::columns::sel;
use dregg_circuit::effect_vm_descriptors::{
    ALL_DESCRIPTORS, NAME_ONLY_DESCRIPTORS, SELECTOR_DESCRIPTORS, descriptor_for_name,
    descriptor_for_selector, descriptor_name_for_selector,
};
use dregg_circuit::lean_descriptor_air::parse_vm_descriptor;

/// Every descriptor reachable via the public API parses through the running
/// EffectVM interpreter, and the parsed `name` round-trips the registry key.
#[test]
fn every_registered_descriptor_parses() {
    // VERB LOCKSTEP: 47 → 25 (the 22 descriptors of the factory-dissolved
    // families died with their Effect variants); +1 for the cellunseal-v2
    // graduation (the lifecycle Sealed→Live frozen-frame + tick row); +1 for
    // the revokecapability-v1 cap-crown face. (The in-crate test
    // `effect_vm_descriptors::descriptor_registry_drift` pins the same 27.)
    assert_eq!(ALL_DESCRIPTORS.len(), 27, "expected 27 unique descriptors");
    for (name, json, _fp) in ALL_DESCRIPTORS {
        let by_name = descriptor_for_name(name).expect("name must resolve");
        assert_eq!(*json, by_name, "{name}: descriptor_for_name mismatch");
        let desc = parse_vm_descriptor(json)
            .unwrap_or_else(|e| panic!("{name} failed to parse via interpreter: {e}"));
        assert_eq!(&desc.name, name, "{name}: parsed name != registry key");
        assert_eq!(
            desc.trace_width, 188,
            "{name}: all EffectVM descriptors share the 188-col base trace \
             (186 EffectVM + state-record-digest + asset-class column)"
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
        assert_eq!(
            descriptor_name_for_selector(*s),
            Some(*name),
            "selector {s}"
        );
        parse_vm_descriptor(json)
            .unwrap_or_else(|e| panic!("selector {s} ({name}) failed to parse: {e}"));
    }
    // VERB LOCKSTEP: 26 of the 29 live selectors carry a v1 registry descriptor
    // (NOOP / SET_FIELD / CUSTOM have no LIVE-path v1 descriptor: SET_FIELD's Lean
    // module is a per-slot family awaiting the dynamic-index gate; CUSTOM's live
    // path is still v1-passthrough — its recursive-proof binding graduated on the
    // IR-v2/v3 path (`customVmDescriptor2` / `customVmDescriptor2R24`), not this v1
    // SELECTOR_DESCRIPTORS table). REVOKE_CAPABILITY (24) carries its cap-crown v1
    // FACE. GRANT_CAP and ATTENUATE_CAPABILITY share the `attenuateA` cap-move JSON,
    // so the 26 selector rows reference 25 distinct descriptor names.
    assert_eq!(SELECTOR_DESCRIPTORS.len(), 26);
    let distinct_names: std::collections::BTreeSet<&str> =
        SELECTOR_DESCRIPTORS.iter().map(|(_, n, _, _)| *n).collect();
    assert_eq!(distinct_names.len(), 25);

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

/// The name-only descriptor (`mint` — the swiss family died in the verb
/// lockstep) is real, parses, and is reachable by name — it simply lacks a
/// dedicated Rust selector.
#[test]
fn name_only_descriptors_are_real() {
    assert_eq!(NAME_ONLY_DESCRIPTORS.len(), 1);
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
