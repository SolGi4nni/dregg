//! Generator for `pages/constants.generated.js` — see the nameservice
//! generator for the rationale. Run:
//!   cargo run -p starbridge-governed-namespace --example constants_generator

use std::path::Path;

fn main() {
    let js = starbridge_governed_namespace::web_constants().render_js();
    let out = Path::new(env!("CARGO_MANIFEST_DIR")).join("pages/constants.generated.js");
    std::fs::write(&out, &js).expect("write constants.generated.js");
    eprintln!("wrote {} ({} bytes)", out.display(), js.len());
}
