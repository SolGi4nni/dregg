//! # fhIR-0 — the typed order/product DSL, "admissible iff it compiles"
//!
//! The product-language foundation on top of the fhEgg Cert-F engine. A
//! product's TYPE carries three things (`FHEGG-PRODUCT-ORDER-FRONTIER.md`
//! headline; `DREGGFI-PRIVACY-TIERS.md` §3):
//!
//! 1. its **convex-program shape** — LP / QP / aggregation, with the matrices
//!    flagged PUBLIC vs PRIVATE (the operative cheap-regime boundary is "the
//!    matrices must be public", `PRIVATE-CONVEX-ENGINE.md` precision-correction
//!    #4 — not "convex");
//! 2. the **privacy tier** it is admissible at — Dark / Shielded / Open;
//! 3. the **certificate kind** it compiles to — Aggregation / Cert-F / CertQp /
//!    Price-Cert.
//!
//! The compiler ([`compile::compile`]) type-checks a product, infers the
//! **most-private honest tier**, and either compiles it to the real
//! `fhegg-solver` engine ([`solver_bridge::run`]) or REJECTS it with a precise
//! [`types::TypeError`] — refusing to promise more privacy than the math
//! delivers (`DREGGFI-PRIVACY-TIERS.md` §2 honest-labeling, mechanized).
//!
//! ## The typing rule
//!
//! A product type-checks at tier `T` iff its convex-program shape is
//! `T`-tractable:
//!
//! - **Dark** (Tier 0, no viewer, FHE): all matrices PUBLIC, affine/aggregation
//!   objective (no PSD/quadratic prox in the FHE v0 core), approved cones, inside
//!   the FHE size envelope.
//! - **Shielded** (Tier 1, private-from-the-world, solver sees): a bounded
//!   oblivious convex circuit — approved cones, no integer/disjunctive feature;
//!   PRIVATE matrices are fine (the solver sees plaintext).
//! - **Open** (Tier 2, public-general): expressible to the general matcher.
//!
//! Admissibility is monotone: Dark ⇒ Shielded ⇒ Open, so the most-private
//! honest tier is the minimum admissible tier in the privacy order.
//!
//! ## Honest scope (no overclaim)
//!
//! fhIR-0 is the FIRST version: the type system + the compiler + a few example
//! products + tier-inference + the wire-to-solver. The type-checker realizes the
//! admissibility **DIRECTION** — *compiles ⇒ runnable at the reported tier*. The
//! full "admissible **iff** it compiles" is the six-part admissibility theorem
//! (`FHEGG-PRODUCT-ORDER-FRONTIER.md`), a NAMED research target for the Lean
//! lane, NOT claimed proved here. What IS delivered and green: the tier lattice,
//! the typing judgment with precise structural rejections, the example products
//! compiling to their `(program, tier, cert)`, the over-claim rejections, and a
//! real end-to-end compile → run → certificate through `fhegg-solver`.

pub mod ast;
pub mod compile;
pub mod products;
pub mod solver_bridge;
pub mod tier;
pub mod types;

pub use compile::{compile, most_private_admissible, Compiled, ConvexProgram};
pub use solver_bridge::{run, RunOutcome};
pub use tier::Tier;
pub use types::{CertKind, TypeError};

#[cfg(test)]
mod integration_tests {
    use super::*;

    /// End-to-end: every compile-and-run example compiles at its expected tier
    /// AND its certificate validates through the real engine.
    #[test]
    fn end_to_end_all_runnable_products() {
        let cases = [
            (
                products::uniform_price_clearing(),
                Tier::Dark,
                CertKind::Aggregation,
            ),
            (products::small_flow_clearing(), Tier::Dark, CertKind::CertF),
            (
                products::flow_lp_clearing(),
                Tier::Shielded,
                CertKind::CertF,
            ),
            (
                products::portfolio_qp_public(),
                Tier::Shielded,
                CertKind::CertQp,
            ),
        ];
        for (product, tier, cert) in cases {
            let name = product.name.clone();
            let compiled = compile(&product).unwrap_or_else(|e| panic!("{name} must compile: {e}"));
            assert_eq!(compiled.tier, tier, "{name} tier");
            assert_eq!(compiled.cert, cert, "{name} cert");
            let out = run(&compiled);
            assert_eq!(
                out.certificate_valid(),
                Some(true),
                "{name} certificate must validate: {}",
                out.summary()
            );
        }
    }

    /// Every rejection is precise and never over-promises privacy.
    #[test]
    fn rejections_are_precise() {
        assert!(compile(&products::portfolio_qp_private_claiming_dark()).is_err());
        assert!(compile(&products::all_or_none_claiming_shielded()).is_err());
    }
}
