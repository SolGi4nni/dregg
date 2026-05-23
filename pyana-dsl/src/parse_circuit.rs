//! Parser for `#[pyana_circuit]` module syntax.
//!
//! Extracts:
//! - Constants (WIDTH, DEGREE, PI_COUNT)
//! - `mod col { ... }` column index definitions
//! - `fn constraints(...)` body
//! - `fn transitions(...)` body
//! - `fn boundaries(...)` body
//!
//! The macro transplants the function bodies into the generated `impl StarkAir`.

use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::{Expr, Ident, Item, ItemConst, ItemFn, ItemMod, Lit};

/// Parsed representation of a `#[pyana_circuit]` module.
#[allow(dead_code)]
pub struct CircuitModule {
    /// The module name (becomes the struct name in PascalCase).
    pub name: Ident,
    /// WIDTH constant value.
    pub width: usize,
    /// DEGREE constant value.
    pub degree: usize,
    /// PI_COUNT constant value.
    pub pi_count: usize,
    /// The `mod col { ... }` module, passed through verbatim.
    pub col_mod: Option<ItemMod>,
    /// Body of `fn constraints(local, next, pi) -> Vec<BabyBear>`.
    pub constraints_fn: Option<ItemFn>,
    /// Body of `fn transitions(local, next) -> Vec<BabyBear>`.
    pub transitions_fn: Option<ItemFn>,
    /// Body of `fn boundaries(pi, trace_len) -> Vec<(usize, usize, BabyBear)>`.
    pub boundaries_fn: Option<ItemFn>,
}

/// Parse a module's items into a `CircuitModule`.
pub fn parse_circuit_module(module: &ItemMod) -> syn::Result<CircuitModule> {
    let name = module.ident.clone();

    let items = module
        .content
        .as_ref()
        .map(|(_, items)| items.as_slice())
        .unwrap_or(&[]);

    let mut width: Option<usize> = None;
    let mut degree: Option<usize> = None;
    let mut pi_count: Option<usize> = None;
    let mut col_mod: Option<ItemMod> = None;
    let mut constraints_fn: Option<ItemFn> = None;
    let mut transitions_fn: Option<ItemFn> = None;
    let mut boundaries_fn: Option<ItemFn> = None;

    for item in items {
        match item {
            Item::Const(c) => {
                let val = extract_usize_const(c)?;
                match c.ident.to_string().as_str() {
                    "WIDTH" => width = Some(val),
                    "DEGREE" => degree = Some(val),
                    "PI_COUNT" => pi_count = Some(val),
                    _ => {} // ignore other constants
                }
            }
            Item::Mod(m) => {
                if m.ident == "col" {
                    col_mod = Some(m.clone());
                }
            }
            Item::Fn(f) => match f.sig.ident.to_string().as_str() {
                "constraints" => constraints_fn = Some(f.clone()),
                "transitions" => transitions_fn = Some(f.clone()),
                "boundaries" => boundaries_fn = Some(f.clone()),
                _ => {}
            },
            _ => {}
        }
    }

    let width = width.ok_or_else(|| {
        syn::Error::new(module.ident.span(), "missing `const WIDTH: usize = ...;`")
    })?;
    let degree = degree.ok_or_else(|| {
        syn::Error::new(module.ident.span(), "missing `const DEGREE: usize = ...;`")
    })?;
    let pi_count = pi_count.ok_or_else(|| {
        syn::Error::new(module.ident.span(), "missing `const PI_COUNT: usize = ...;`")
    })?;

    Ok(CircuitModule {
        name,
        width,
        degree,
        pi_count,
        col_mod,
        constraints_fn,
        transitions_fn,
        boundaries_fn,
    })
}

/// Extract a `usize` value from a const item like `const WIDTH: usize = 6;`.
fn extract_usize_const(c: &ItemConst) -> syn::Result<usize> {
    // Try to extract from a literal integer expression.
    match c.expr.as_ref() {
        Expr::Lit(lit) => match &lit.lit {
            Lit::Int(int_lit) => int_lit.base10_parse::<usize>().map_err(|e| {
                syn::Error::new(int_lit.span(), format!("invalid integer: {e}"))
            }),
            _ => Err(syn::Error::new(
                c.ident.span(),
                "expected integer literal for constant",
            )),
        },
        _ => Err(syn::Error::new(
            c.ident.span(),
            "expected integer literal for constant",
        )),
    }
}

/// Generate the output tokens for a `#[pyana_circuit]` module.
pub fn emit_circuit(module: &CircuitModule) -> TokenStream {
    let struct_name = format_ident!("{}", to_pascal_case(&module.name.to_string()));
    let width = module.width;
    let degree = module.degree;
    let air_name = format!("pyana-{}-v1", module.name);

    // Emit the col module at top level (if present).
    let col_mod_tokens = module.col_mod.as_ref().map(|m| {
        quote! { #m }
    });

    // Generate eval_constraints body.
    let eval_body = emit_eval_constraints(module);

    // Generate boundary_constraints body.
    let boundary_body = emit_boundary_constraints(module);

    quote! {
        #col_mod_tokens

        pub struct #struct_name;

        impl pyana_circuit::stark::StarkAir for #struct_name {
            fn width(&self) -> usize { #width }
            fn constraint_degree(&self) -> usize { #degree }
            fn air_name(&self) -> &'static str { #air_name }
            fn has_chain_continuity(&self) -> bool { false }

            fn eval_constraints(
                &self,
                local: &[pyana_circuit::field::BabyBear],
                next: &[pyana_circuit::field::BabyBear],
                public_inputs: &[pyana_circuit::field::BabyBear],
                alpha: pyana_circuit::field::BabyBear,
            ) -> pyana_circuit::field::BabyBear {
                use pyana_circuit::field::BabyBear;
                #eval_body
            }

            fn boundary_constraints(
                &self,
                public_inputs: &[pyana_circuit::field::BabyBear],
                trace_len: usize,
            ) -> Vec<pyana_circuit::stark::BoundaryConstraint> {
                use pyana_circuit::field::BabyBear;
                use pyana_circuit::stark::BoundaryConstraint;
                #boundary_body
            }
        }
    }
}

/// Emit the `eval_constraints` body by transplanting constraints + transitions
/// and composing with alpha powers.
fn emit_eval_constraints(module: &CircuitModule) -> TokenStream {
    // The approach: call the user's constraints fn to get a Vec<BabyBear>,
    // then call the user's transitions fn to get another Vec<BabyBear>,
    // then compose all with alpha powers.
    //
    // We inline the function BODIES directly (no function call overhead),
    // by extracting the block from each fn.

    let constraints_block = module.constraints_fn.as_ref().map(|f| {
        let body = &f.block;
        quote! { #body }
    });

    let transitions_block = module.transitions_fn.as_ref().map(|f| {
        let body = &f.block;
        quote! { #body }
    });

    // Build the composition:
    // 1. Evaluate constraints (per-row) into a Vec
    // 2. Evaluate transitions (row-to-row) into a Vec
    // 3. Compose all with alpha powers.

    let constraints_vec = if let Some(block) = constraints_block {
        quote! {
            let constraint_values: Vec<BabyBear> = {
                let pi = public_inputs;
                #block
            };
        }
    } else {
        quote! {
            let constraint_values: Vec<BabyBear> = vec![];
        }
    };

    let transitions_vec = if let Some(block) = transitions_block {
        quote! {
            let transition_values: Vec<BabyBear> = {
                #block
            };
        }
    } else {
        quote! {
            let transition_values: Vec<BabyBear> = vec![];
        }
    };

    quote! {
        #constraints_vec
        #transitions_vec

        // Compose all constraints with alpha powers
        let mut result = BabyBear::ZERO;
        let mut alpha_power = BabyBear::ONE;
        for c in constraint_values.iter().chain(transition_values.iter()) {
            result = result + alpha_power * *c;
            alpha_power = alpha_power * alpha;
        }
        result
    }
}

/// Emit the `boundary_constraints` body by transplanting the boundaries fn.
fn emit_boundary_constraints(module: &CircuitModule) -> TokenStream {
    let boundaries_block = module.boundaries_fn.as_ref().map(|f| {
        let body = &f.block;
        quote! { #body }
    });

    if let Some(block) = boundaries_block {
        // The user's function returns Vec<(usize, usize, BabyBear)>
        // which represents (row_index, column, value).
        // We need to convert to Vec<BoundaryConstraint>.
        quote! {
            let pi = public_inputs;
            let raw: Vec<(usize, usize, BabyBear)> = #block;
            raw.into_iter()
                .map(|(row, col, value)| BoundaryConstraint { row, col, value })
                .collect()
        }
    } else {
        quote! { vec![] }
    }
}

/// Convert snake_case to PascalCase.
fn to_pascal_case(s: &str) -> String {
    s.split('_')
        .map(|word| {
            let mut c = word.chars();
            match c.next() {
                None => String::new(),
                Some(first) => first.to_uppercase().collect::<String>() + c.as_str(),
            }
        })
        .collect()
}
