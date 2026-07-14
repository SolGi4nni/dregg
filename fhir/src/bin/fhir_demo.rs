//! `fhir-demo` — compile every fhIR-0 example, report its most-private tier, and
//! run the compilable ones through the real `fhegg-solver` engine.
//!
//! Run: `cargo run --release --bin fhir-demo` (in `fhir/`).

use fhir::compile::compile;
use fhir::solver_bridge::run;
use fhir::{products, TypeError};

fn main() {
    println!("fhIR-0 — the typed order/product DSL (\"admissible iff it compiles\")");
    println!("the compiler reports the MOST-PRIVATE tier a product can honestly run at.\n");

    for product in products::all() {
        println!("── {} ", product.name);
        if let Some(claim) = product.claim {
            println!("   author claims: {claim}");
        }
        match compile(&product) {
            Ok(compiled) => {
                println!("   COMPILES  most-private tier: {}", compiled.tier);
                println!(
                    "             tractability: {}",
                    compiled.tier.tractability()
                );
                println!("             certificate: {:?}", compiled.cert);
                let out = run(&compiled);
                match out.certificate_valid() {
                    Some(true) => println!("   RUN  {}  [certificate valid]", out.summary()),
                    Some(false) => println!("   RUN  {}  [certificate INVALID]", out.summary()),
                    None => println!("   RUN  {}", out.summary()),
                }
            }
            Err(e) => {
                println!("   REJECTED  {e}");
                if let TypeError::OverClaimsTier { honest, .. } = &e {
                    println!("             (the honest tier it DOES compile to: {honest})");
                }
            }
        }
        println!();
    }
}
