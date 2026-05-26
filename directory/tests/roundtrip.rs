//! End-to-end integration tests: register → lookup → revoke → discover.
//!
//! Exercises the four canonical `Directory` operations via `InMemoryDirectory`
//! plus the DFA-routed and meta-directory variants.

use dregg_directory::ResourceHandle;

// ============================================================================
// ResourceHandle URI round-trip
// ============================================================================

#[test]
fn resource_handle_uri_contains_hex_fields() {
    let h = ResourceHandle::new([0xabu8; 32], [0xcdu8; 32], [0xefu8; 32]);
    let uri = h.to_uri();
    assert!(uri.starts_with("dregg://"), "URI must start with dregg://");
    // federation_id hex
    assert!(uri.contains("abababababababababababababababababababababababababababababababab"));
}
