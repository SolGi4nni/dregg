//! Dregg Constraint DSL — proc macro crate.
//!
//! Provides `#[dregg_caveat]` and `#[dregg_effect]` which compile one constraint
//! function into SEVEN backends:
//! - `gen_rust`     — a Rust evaluator (`{name}_check`)              [agreement set]
//! - `gen_air`      — an AIR constraint descriptor (`{name}_air_constraints`) [agreement set]
//! - `gen_datalog`  — a Datalog rule fragment (`{name}_datalog`)    [agreement set]
//! - `gen_kimchi`   — a Kimchi circuit descriptor (`{name}_kimchi`) [agreement set]
//! - `gen_plonky3`  — a native Plonky3 Air impl (`{Name}P3Air`)     [agreement set, subset]
//! - `gen_midnight` — a Midnight ZKIR v3 program (`{name}_midnight_zkir`) [emit-only/lint-only]
//! - `gen_sp1`      — an SP1 guest program (`{name}_sp1_guest`)      [emit-only/lint-only]
//!
//! The former `emit_stark` backend (a compile-time impl of the hand-rolled
//! `dregg_circuit` STARK) has been removed along with that engine; native Plonky3
//! (`gen_plonky3`) is the proving backend.
//!
//! ## Cross-validation status
//!
//! Five backends (`gen_rust`, `gen_air`, `gen_datalog`, `gen_kimchi`,
//! `gen_plonky3`) form the **agreement set** cross-checked by
//! `dregg-dsl-differential` (gen_rust is the oracle). `gen_midnight` and
//! `gen_sp1` are STRING emitters validated by lint only (their proof systems need
//! external toolchains); they cast no agreement vote.
//!
//! ## Range-check soundness
//!
//! `<=`, `>=` and `in_range!` compile to a genuine bit-decomposition range check
//! in `gen_plonky3`: the difference (or value) is bound to
//! `RANGE_CHECK_BITS` binary witness columns, the reconstruction is enforced, and
//! the top bits are forced to zero — so a field-wrapped negative difference is
//! UNSATISFIABLE. Each sub-constraint is asserted independently (no cancellation).

extern crate proc_macro;

mod gen_air;
mod gen_datalog;
mod gen_kimchi;
mod gen_midnight;
mod gen_plonky3;
mod gen_rust;
mod gen_sp1;
mod ir;
mod parse;

use proc_macro::TokenStream;
use quote::quote;
use syn::{ItemFn, parse_macro_input};

/// Marks a function as a dregg caveat constraint.
///
/// The function body must consist of `require!(expr)` statements where each
/// `expr` is a binary comparison or a `.contains()` membership check.
/// The macro expands the function into generated items:
///
/// - `{name}_check(params...) -> Result<(), ConstraintError>` — runtime evaluator
/// - `{name}_air_constraints() -> AirConstraintSet` — AIR topology descriptor
/// - `{name}_datalog() -> &'static str` — Datalog rule
/// - `{name}_kimchi() -> KimchiCircuitDescriptor` — Kimchi gate descriptor
///
/// # Example
///
/// ```ignore
/// #[dregg_caveat]
/// fn not_after(token_expiry: u64, current_time: u64) {
///     require!(current_time <= token_expiry);
/// }
/// ```
#[proc_macro_attribute]
pub fn dregg_caveat(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let func = parse_macro_input!(item as ItemFn);

    let ir = match parse::parse_caveat(&func) {
        Ok(ir) => ir,
        Err(e) => return e.to_compile_error().into(),
    };

    let rust_eval = gen_rust::generate_rust_evaluator(&ir);
    let air_desc = gen_air::generate_air_descriptor(&ir);
    let datalog = gen_datalog::generate_datalog(&ir);
    let kimchi = gen_kimchi::generate_kimchi(&ir);
    let midnight = gen_midnight::generate_midnight(&ir);
    let plonky3 = gen_plonky3::generate_plonky3(&ir);
    let sp1 = gen_sp1::generate_sp1(&ir);

    let output = quote! {
        #rust_eval
        #air_desc
        #datalog
        #kimchi
        #midnight
        #plonky3
        #sp1
    };

    output.into()
}

/// Marks a function as a dregg effect — a constraint with state mutation.
///
/// Effect functions may contain `&mut` parameters and mutation statements
/// (`*balance -= amount`), in addition to `require!()` checks and `match` arms.
///
/// Supports a `requires` attribute for permission gating:
/// ```ignore
/// #[dregg_effect(requires = "Send")]
/// fn transfer(balance: &mut u64, amount: u64, direction: Direction) {
///     match direction {
///         Direction::Outgoing => {
///             require!(balance >= amount);
///             *balance -= amount;
///         }
///         Direction::Incoming => {
///             *balance += amount;
///         }
///     }
/// }
/// ```
///
/// Generates:
/// - `{name}_check(params...) -> Result<(), ConstraintError>` — evaluator that mutates in-place
/// - `{name}_air_constraints() -> AirConstraintSet` — AIR with old+new columns per mutable param
/// - `{name}_datalog() -> &'static str` — Datalog rule
/// - `{name}_kimchi() -> KimchiCircuitDescriptor` — Kimchi gates
/// - `{name}_effect_descriptor() -> EffectDescriptor` — effect metadata
#[proc_macro_attribute]
pub fn dregg_effect(attr: TokenStream, item: TokenStream) -> TokenStream {
    let func = parse_macro_input!(item as ItemFn);

    // Parse the attribute for `requires = "..."`.
    let required_permission = parse_effect_attr(attr);

    let ir = match parse::parse_effect(&func, required_permission) {
        Ok(ir) => ir,
        Err(e) => return e.to_compile_error().into(),
    };

    let rust_eval = gen_rust::generate_rust_evaluator(&ir);
    let air_desc = gen_air::generate_air_descriptor(&ir);
    let datalog = gen_datalog::generate_datalog(&ir);
    let kimchi = gen_kimchi::generate_kimchi(&ir);
    let effect_desc = gen_rust::generate_effect_descriptor(&ir);
    let midnight = gen_midnight::generate_midnight(&ir);
    let plonky3 = gen_plonky3::generate_plonky3(&ir);
    let sp1 = gen_sp1::generate_sp1(&ir);

    let output = quote! {
        #rust_eval
        #air_desc
        #datalog
        #kimchi
        #effect_desc
        #midnight
        #plonky3
        #sp1
    };

    output.into()
}

/// Parse `#[dregg_effect(requires = "Send")]` attribute.
fn parse_effect_attr(attr: TokenStream) -> Option<String> {
    let attr_str = attr.to_string();
    if attr_str.is_empty() {
        return None;
    }
    // Simple parsing: look for `requires = "..."`
    if let Some(start) = attr_str.find("requires")
        && let Some(eq_pos) = attr_str[start..].find('=')
    {
        let after_eq = &attr_str[start + eq_pos + 1..];
        let trimmed = after_eq.trim();
        if trimmed.starts_with('"') {
            let end = trimmed[1..].find('"').unwrap_or(trimmed.len() - 1);
            return Some(trimmed[1..1 + end].to_string());
        }
    }
    None
}
