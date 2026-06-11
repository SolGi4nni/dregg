//! Drift guard: `pages/constants.generated.js` must match what
//! `starbridge_nameservice::web_constants()` renders.
//!
//! This is the anti-drift bridge between the Rust source of truth (the
//! `pub const *_SLOT`, the `symbol("…")` topics, `NAME_FACTORY_VK`) and the web
//! pages that consume them. If a slot index, topic name, or factory-vk changes
//! in `src/lib.rs` but the generated JS is not regenerated, this test fails with
//! the first differing line.
//!
//! Regenerate with:
//!   cargo run -p starbridge-nameservice --example constants_generator

use std::path::Path;

#[test]
fn constants_js_is_in_sync_with_rust_source_of_truth() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("pages/constants.generated.js");
    starbridge_nameservice::web_constants().assert_matches_file(&path);
}

/// The generated slot values agree with the crate's `pub const`s — a redundant
/// but cheap belt-and-suspenders check that the generator wires the right
/// constants (so a copy/paste error in `web_constants()` is caught too).
#[test]
fn web_constants_slots_match_pub_consts() {
    let m = starbridge_nameservice::web_constants();
    let slot = |name: &str| m.slots.iter().find(|s| s.js_name == name).map(|s| s.value);
    assert_eq!(
        slot("NAME_HASH_SLOT"),
        Some(starbridge_nameservice::NAME_HASH_SLOT as u64)
    );
    assert_eq!(
        slot("OWNER_HASH_SLOT"),
        Some(starbridge_nameservice::OWNER_HASH_SLOT as u64)
    );
    assert_eq!(
        slot("EXPIRY_SLOT"),
        Some(starbridge_nameservice::EXPIRY_SLOT as u64)
    );
    assert_eq!(
        slot("REVOKED_SLOT"),
        Some(starbridge_nameservice::REVOKED_SLOT as u64)
    );
    assert_eq!(
        slot("RESOLVE_TARGET_SLOT"),
        Some(starbridge_nameservice::RESOLVE_TARGET_SLOT as u64)
    );
}
