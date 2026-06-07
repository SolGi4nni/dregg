//! Generator for `pages/constants.generated.js` — see the nameservice
//! generator for the rationale. Run:
//!   cargo run -p starbridge-storage-gateway-mandate --example constants_generator

use std::path::Path;

fn main() {
    let js = starbridge_storage_gateway_mandate::web_constants().render_js();
    let out = Path::new(env!("CARGO_MANIFEST_DIR")).join("pages/constants.generated.js");
    std::fs::write(&out, &js).expect("write constants.generated.js");
    eprintln!("wrote {} ({} bytes)", out.display(), js.len());
}
