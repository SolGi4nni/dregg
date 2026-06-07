//! Generator for `pages/constants.generated.js` — see the nameservice
//! generator for the full rationale. Run:
//!   cargo run -p starbridge-identity --example constants_generator

use std::path::Path;

fn main() {
    let js = starbridge_identity::web_constants().render_js();
    let out = Path::new(env!("CARGO_MANIFEST_DIR")).join("pages/constants.generated.js");
    std::fs::write(&out, &js).expect("write constants.generated.js");
    eprintln!("wrote {} ({} bytes)", out.display(), js.len());
}
