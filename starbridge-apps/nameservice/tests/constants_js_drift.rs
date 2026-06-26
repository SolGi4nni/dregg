//! Guard: `web_constants()` agrees with the crate's `pub const` slot layout.
//!
//! The legacy `pages/` web bundle (and its `constants.generated.js` drift guard)
//! has been retired — the app's surface is now the renderer-independent deos-view
//! CARD (`src/card.rs`). [`web_constants`](starbridge_nameservice::web_constants)
//! is kept as the canonical, source-of-truth constants module; this test pins it
//! to the executor's slot layout so a copy/paste error in `web_constants()` is
//! still caught.

/// The constants module's slot values agree with the crate's `pub const`s.
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
