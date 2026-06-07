//! Drift guard: `pages/constants.generated.js` must match
//! `starbridge_governed_namespace::web_constants()`. Regenerate with:
//!   cargo run -p starbridge-governed-namespace --example constants_generator

use std::path::Path;

#[test]
fn constants_js_is_in_sync_with_rust_source_of_truth() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("pages/constants.generated.js");
    starbridge_governed_namespace::web_constants().assert_matches_file(&path);
}
