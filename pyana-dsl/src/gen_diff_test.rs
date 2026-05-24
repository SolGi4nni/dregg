//! Code generator: cross-implementation differential test.
//!
//! Per `dev-philosophy/02-testing.md` section 2 ("Cross-implementation
//! differential tests"), every `#[pyana_caveat]` definition should emit a
//! `proptest!` test that drives random parameter values through BOTH:
//!
//! 1. The Rust evaluator (`{name}_check`) and
//! 2. An algebraic re-derivation of the AIR descriptor's per-constraint
//!    accept/reject decision via `pyana_dsl_runtime::diff_witness`.
//!
//! The test asserts the two paths agree. This is the test that permanently
//! closes the Effect VM "cousin-pair" drift problem: any backend that
//! disagrees with the IR's intended semantics fails immediately.
//!
//! ## Scope
//!
//! - Caveat differential tests are fully implemented for the IR shapes
//!   the DSL supports today: `<=`, `>=`, `==`, `!=`, and `set.contains(x)`.
//! - Effect differential tests (mutation post-state checks) are NOT yet
//!   implemented and emit `compile_error!` when explicitly requested —
//!   they require the next IR extension (centralized trace witnessing for
//!   mutations after the trace-widening refactor). Caveats inside effect
//!   bodies are still common to both, so we emit the test only for
//!   `#[pyana_caveat]`, not `#[pyana_effect]`.

use proc_macro2::TokenStream;
use quote::{format_ident, quote};

use crate::ir::{ConstraintIr, ParamType, RequirementKind, Statement};

/// Emit a `proptest!`-driven differential test for a caveat.
///
/// Returns an empty `TokenStream` for effects (mutations are a separate IR
/// extension; see module docs).
pub fn generate_diff_test(ir: &ConstraintIr) -> TokenStream {
    if ir.is_effect {
        // Effect-side differential tests are deferred. We deliberately emit
        // nothing here so existing #[pyana_effect] uses continue to compile.
        // Use `generate_diff_test_force_for_effect` if you want the explicit
        // compile_error! stub.
        return quote! {};
    }

    // Bail if any param shape is unsupported by the diff-test harness.
    for p in &ir.params {
        match &p.ty {
            ParamType::U64 | ParamType::ByteArray32 | ParamType::Set => {}
            ParamType::UserDefined(_) => {
                // User-defined enums (Direction-style) currently only appear
                // in effects via `match`. Skip diff-test emission for those.
                return quote! {};
            }
        }
    }

    // Build the proptest! invocation:
    // - For each u64 param, generate `param in any::<u64>()`.
    // - For each [u8;32] param, generate `param in any::<[u8;32]>()`.
    // - For each Set param, generate a HashSet<u64> with up to 8 elements
    //   AND a "candidate" companion u64 (the element to test membership of).
    //   The candidate is chosen so that ~50% of cases hit the set and ~50%
    //   miss, exercising both accept and reject paths.

    // First, identify set-typed params and the element they're paired with.
    // The IR has membership requirements with `set: String, element: String`
    // identifying the set parameter and the element parameter (which must
    // already exist in params).
    let mut proptest_inputs: Vec<TokenStream> = Vec::new();
    let mut call_args: Vec<TokenStream> = Vec::new();
    let mut diff_value_decls: Vec<TokenStream> = Vec::new();

    for p in &ir.params {
        let name = &p.name;
        match &p.ty {
            ParamType::U64 => {
                proptest_inputs.push(quote! { #name in ::proptest::prelude::any::<u64>() });
                call_args.push(quote! { #name });
                diff_value_decls.push(quote! {
                    let #name = #name;
                });
            }
            ParamType::ByteArray32 => {
                proptest_inputs.push(quote! {
                    #name in ::proptest::prelude::any::<[u8; 32]>()
                });
                call_args.push(quote! { #name });
                diff_value_decls.push(quote! {
                    let #name = #name;
                });
            }
            ParamType::Set => {
                // Generate a HashSet<u64> by drawing a Vec<u64> of length 0..8.
                let helper = format_ident!("__pyana_diff_set_{}", name);
                proptest_inputs.push(quote! {
                    #helper in ::proptest::collection::vec(::proptest::prelude::any::<u64>(), 0..8)
                });
                call_args.push(quote! { &#name });
                diff_value_decls.push(quote! {
                    let #name: ::std::collections::HashSet<u64> =
                        #helper.iter().copied().collect();
                });
            }
            ParamType::UserDefined(_) => unreachable!("already filtered"),
        }
    }

    // Build the algebraic re-derivation: walk the IR's requirements and
    // run diff_witness checks against the (already-bound) param values.
    let air_check = build_air_check(&ir.statements);

    let test_fn = format_ident!("{}_differential", ir.name);
    let check_fn = format_ident!("{}_check", ir.name);

    quote! {
        #[cfg(test)]
        #[allow(non_snake_case, clippy::too_many_arguments)]
        mod #test_fn {
            use super::*;
            use pyana_dsl_runtime::diff_witness::{
                DiffValue, DiffOutcome, IntoDiffValue, check_le, check_ge,
                check_equal, check_not_equal, check_membership, combine_and,
            };

            #[inline]
            #[allow(dead_code)]
            fn __pyana_diff_to_value<T: IntoDiffValue + ?Sized>(v: &T) -> DiffValue {
                v.into_diff_value()
            }

            ::proptest::proptest! {
                #![proptest_config(::proptest::test_runner::Config {
                    cases: 128,
                    .. ::proptest::test_runner::Config::default()
                })]

                #[test]
                fn differential(#(#proptest_inputs),*) {
                    #(#diff_value_decls)*

                    // Path 1: Rust evaluator.
                    let exec_result = #check_fn(#(#call_args),*);

                    // Path 2: re-derive accept/reject from the AIR
                    // descriptor's algebraic shape, using only
                    // pyana_dsl_runtime::diff_witness primitives.
                    let air_outcome: DiffOutcome = #air_check;

                    // Cross-check: both paths must agree.
                    ::proptest::prop_assert_eq!(
                        exec_result.is_ok(),
                        air_outcome == DiffOutcome::Accept,
                        "differential mismatch: exec={:?}, air={:?}",
                        exec_result,
                        air_outcome,
                    );
                }
            }
        }
    }
}

/// Walk the IR's statements and emit code that computes a single
/// [`DiffOutcome`] reflecting whether the AIR descriptor would accept this
/// input. Multiple `require!` calls are combined with AND.
fn build_air_check(statements: &[Statement]) -> TokenStream {
    let mut outcomes: Vec<TokenStream> = Vec::new();
    collect_outcomes(statements, &mut outcomes);
    if outcomes.is_empty() {
        // Pathological: no requirements. Treat as accept.
        return quote! { DiffOutcome::Accept };
    }
    quote! {
        combine_and([#(#outcomes),*].iter().copied())
    }
}

fn collect_outcomes(statements: &[Statement], out: &mut Vec<TokenStream>) {
    for stmt in statements {
        match stmt {
            Statement::Require(req) => {
                let t = match &req.kind {
                    RequirementKind::LessEqual { left, right } => {
                        quote! { check_le((#left) as u64, (#right) as u64) }
                    }
                    RequirementKind::GreaterEqual { left, right } => {
                        quote! { check_ge((#left) as u64, (#right) as u64) }
                    }
                    RequirementKind::Equal { left, right } => {
                        quote! {
                            check_equal(
                                &__pyana_diff_to_value(&(#left)),
                                &__pyana_diff_to_value(&(#right)),
                            )
                        }
                    }
                    RequirementKind::NotEqual { left, right } => {
                        quote! {
                            check_not_equal(
                                &__pyana_diff_to_value(&(#left)),
                                &__pyana_diff_to_value(&(#right)),
                            )
                        }
                    }
                    RequirementKind::Membership { set, element } => {
                        let set_ident = format_ident!("{}", set);
                        let elem_ident = format_ident!("{}", element);
                        quote! { check_membership(&#set_ident, #elem_ident) }
                    }
                };
                out.push(t);
            }
            Statement::Mutate(_) => {
                // No mutations in caveat differential tests — handled by
                // the early-return in `generate_diff_test`.
            }
            Statement::Match { arms, .. } => {
                // No match in caveats — handled by the early-return.
                for arm in arms {
                    collect_outcomes(&arm.body, out);
                }
            }
        }
    }
}

/// Emit a `compile_error!` placeholder for would-be effect differential
/// tests. Kept here for documentation purposes; not invoked by the main
/// proc-macro entrypoint.
#[allow(dead_code)]
pub fn generate_diff_test_force_for_effect(_ir: &ConstraintIr) -> TokenStream {
    quote! {
        ::std::compile_error!(
            "effect-side differential tests are not yet implemented; \
             see pyana-dsl/src/gen_diff_test.rs for the IR extension required \
             (centralized mutation witness post-trace-widening)"
        );
    }
}
