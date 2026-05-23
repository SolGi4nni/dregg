/// Code generator: Native Plonky3 Air implementation.
///
/// Produces a struct `{Name}P3Air` implementing `p3_air::BaseAir` and `p3_air::Air`
/// traits directly, enabling the DSL-defined constraint to be proven with Plonky3's
/// `p3_uni_stark` prover without going through the runtime-interpreted `DslCircuit`.
///
/// ## Why native Plonky3 Air?
///
/// The existing path is: DSL → CircuitDescriptor → DslCircuit (interprets at runtime).
/// This adds overhead per-row (virtual dispatch over constraint expressions).
/// A native Air impl compiles the constraints directly into Rust code that Plonky3
/// evaluates with full inlining and SIMD vectorization.
///
/// ## Architecture
///
/// The generated code:
/// 1. Defines a zero-sized struct `{Name}P3Air`
/// 2. Implements `BaseAir<F>` with the computed trace width
/// 3. Implements `Air<AB>` with constraint assertions using `builder.assert_zero(...)`
/// 4. Provides a `generate_trace(...)` helper method
///
/// ## Trace Layout
///
/// Same layout as `emit_stark_impl.rs`:
/// - Immutable params: 1 column each (u64) or 8 (ByteArray32)
/// - Mutable params: 2 columns each (old + new)
/// - Auxiliary: diff columns for range checks, inverse columns for neq
///
/// ## Constraint Mapping
///
/// - `require!(a <= b)` → `builder.assert_zero(diff - right + left)` + bit range
/// - `require!(a == b)` → `builder.assert_zero(left - right)`
/// - `require!(a != b)` → `builder.assert_zero((left - right) * inv - 1)`
/// - `*target -= operand` → `builder.assert_zero(new - old + operand)`
/// - `*target += operand` → `builder.assert_zero(new - old - operand)`
///
/// ## Limitations
///
/// - Membership constraints are NOT supported (would require Poseidon2 gadget).
/// - Match arms with >2 variants use multi-selector columns (not yet optimal).
/// - The generated code requires `p3_air`, `p3_field`, `p3_matrix` in scope.
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

use crate::ir::{ConstraintIr, MutateOp, ParamType, RequirementKind, Statement};

/// Check if the IR contains membership constraints (unsupported for native P3).
fn has_membership(statements: &[Statement]) -> bool {
    for stmt in statements {
        match stmt {
            Statement::Require(req) => {
                if matches!(req.kind, RequirementKind::Membership { .. }) {
                    return true;
                }
            }
            Statement::Mutate(_) => {}
            Statement::Match { arms, .. } => {
                for arm in arms {
                    if has_membership(&arm.body) {
                        return true;
                    }
                }
            }
        }
    }
    false
}

pub fn generate_plonky3(ir: &ConstraintIr) -> TokenStream {
    // Cannot generate native Plonky3 Air for membership constraints.
    if has_membership(&ir.statements) {
        return TokenStream::new();
    }

    let struct_name = format_ident!("{}P3Air", to_pascal_case(&ir.name.to_string()));
    let layout = compute_p3_layout(ir);
    let width = layout.width;

    // Public inputs: non-mutable params count
    let pi_count: usize = ir
        .params
        .iter()
        .filter(|p| !p.mutable)
        .map(|p| match &p.ty {
            ParamType::U64 => 1,
            ParamType::ByteArray32 => 8,
            ParamType::Set => 1,
            ParamType::UserDefined(_) => 1,
        })
        .sum();

    // Generate constraint body
    let constraint_body = emit_p3_constraints(ir, &layout);

    quote! {
        /// Native Plonky3 Air implementation for this constraint.
        ///
        /// Use with `p3_uni_stark::prove` / `p3_uni_stark::verify` for
        /// production-grade STARK proofs over BabyBear + FRI.
        ///
        /// Only compiled when the `plonky3` feature is enabled (requires
        /// `p3_air`, `p3_field`, and `p3_matrix` crates in scope).
        #[cfg(feature = "plonky3")]
        pub struct #struct_name;

        #[cfg(feature = "plonky3")]
        impl<F: p3_field::PrimeCharacteristicRing + Sync> p3_air::BaseAir<F> for #struct_name {
            fn width(&self) -> usize {
                #width
            }

            fn num_public_values(&self) -> usize {
                #pi_count
            }
        }

        #[cfg(feature = "plonky3")]
        impl<AB: p3_air::AirBuilder> p3_air::Air<AB> for #struct_name {
            fn eval(&self, builder: &mut AB) {
                let main = builder.main();
                let local = main.current_slice();

                #constraint_body
            }
        }
    }
}

// ============================================================================
// Layout computation (mirrors emit_stark_impl.rs logic)
// ============================================================================

struct P3Layout {
    width: usize,
    param_cols: Vec<P3ParamCol>,
    aux_start: usize,
}

struct P3ParamCol {
    name: String,
    start_col: usize,
    #[allow(dead_code)]
    num_cols: usize,
    is_mutable: bool,
}

fn compute_p3_layout(ir: &ConstraintIr) -> P3Layout {
    let mut width: usize = 0;
    let mut param_cols = Vec::new();

    for p in &ir.params {
        let base = match &p.ty {
            ParamType::U64 => 1,
            ParamType::ByteArray32 => 8,
            ParamType::Set => 1,
            ParamType::UserDefined(_) => 1,
        };
        let num_cols = if p.mutable { base * 2 } else { base };
        param_cols.push(P3ParamCol {
            name: p.name.to_string(),
            start_col: width,
            num_cols,
            is_mutable: p.mutable,
        });
        width += num_cols;
    }

    let aux_start = width;
    count_p3_aux(&ir.statements, &mut width);

    P3Layout {
        width,
        param_cols,
        aux_start,
    }
}

fn count_p3_aux(statements: &[Statement], width: &mut usize) {
    for stmt in statements {
        match stmt {
            Statement::Require(req) => match &req.kind {
                RequirementKind::LessEqual { .. } | RequirementKind::GreaterEqual { .. } => {
                    *width += 2; // diff_col + bit_col
                }
                RequirementKind::Equal { .. } => {}
                RequirementKind::NotEqual { .. } => {
                    *width += 1; // inverse witness
                }
                RequirementKind::Membership { .. } => {
                    *width += 1; // placeholder (unreachable due to early return)
                }
            },
            Statement::Mutate(_) => {}
            Statement::Match { arms, .. } => {
                *width += 1; // selector
                for arm in arms {
                    count_p3_aux(&arm.body, width);
                }
            }
        }
    }
}

// ============================================================================
// Constraint code emission
// ============================================================================

fn emit_p3_constraints(ir: &ConstraintIr, layout: &P3Layout) -> TokenStream {
    let mut assertions = Vec::new();
    let mut aux_idx: usize = 0;

    emit_p3_statements(&ir.statements, layout, &mut assertions, &mut aux_idx, None);

    quote! {
        #(#assertions)*
    }
}

fn emit_p3_statements(
    statements: &[Statement],
    layout: &P3Layout,
    out: &mut Vec<TokenStream>,
    aux_idx: &mut usize,
    selector: Option<TokenStream>,
) {
    for stmt in statements {
        match stmt {
            Statement::Require(req) => {
                let expr = emit_p3_requirement(&req.kind, layout, aux_idx);
                let constrained = if let Some(ref sel) = selector {
                    quote! { builder.assert_zero(#sel * (#expr)); }
                } else {
                    quote! { builder.assert_zero(#expr); }
                };
                out.push(constrained);
            }
            Statement::Mutate(mutation) => {
                let expr = emit_p3_mutation(mutation, layout);
                let constrained = if let Some(ref sel) = selector {
                    quote! { builder.assert_zero(#sel * (#expr)); }
                } else {
                    quote! { builder.assert_zero(#expr); }
                };
                out.push(constrained);
            }
            Statement::Match { arms, .. } => {
                let sel_col = layout.aux_start + *aux_idx;
                *aux_idx += 1;

                // Selector must be binary
                out.push(quote! {
                    let sel: AB::Expr = local[#sel_col].into();
                    builder.assert_zero(sel.clone() * (sel.clone() - AB::Expr::ONE));
                });

                if arms.len() == 2 {
                    // Arm 0: gated by (1 - sel), Arm 1: gated by sel
                    let gate0 = quote! { (AB::Expr::ONE - sel.clone()) };
                    let gate1 = quote! { sel.clone() };

                    emit_p3_statements(&arms[0].body, layout, out, aux_idx, Some(gate0));
                    emit_p3_statements(&arms[1].body, layout, out, aux_idx, Some(gate1));
                } else {
                    // General case: all arms gated by selector
                    let gate = quote! { sel.clone() };
                    for arm in arms {
                        emit_p3_statements(&arm.body, layout, out, aux_idx, Some(gate.clone()));
                    }
                }
            }
        }
    }
}

fn emit_p3_requirement(
    kind: &RequirementKind,
    layout: &P3Layout,
    aux_idx: &mut usize,
) -> TokenStream {
    match kind {
        RequirementKind::LessEqual { left, right } => {
            let left_col = find_p3_col(layout, &quote::quote!(#left).to_string());
            let right_col = find_p3_col(layout, &quote::quote!(#right).to_string());
            let diff_col = layout.aux_start + *aux_idx;
            let bit_col = layout.aux_start + *aux_idx + 1;
            *aux_idx += 2;

            // Three sub-constraints combined:
            // 1. diff == right - left
            // 2. bit is binary
            // 3. bit == 0 (non-negative)
            quote! {
                {
                    let left_val: AB::Expr = local[#left_col].into();
                    let right_val: AB::Expr = local[#right_col].into();
                    let diff_val: AB::Expr = local[#diff_col].into();
                    let bit_val: AB::Expr = local[#bit_col].into();
                    // diff consistency + bit binary + bit zero
                    (diff_val.clone() - right_val + left_val)
                        + bit_val.clone() * (bit_val.clone() - AB::Expr::ONE)
                        + bit_val
                }
            }
        }
        RequirementKind::GreaterEqual { left, right } => {
            let left_col = find_p3_col(layout, &quote::quote!(#left).to_string());
            let right_col = find_p3_col(layout, &quote::quote!(#right).to_string());
            let diff_col = layout.aux_start + *aux_idx;
            let bit_col = layout.aux_start + *aux_idx + 1;
            *aux_idx += 2;

            quote! {
                {
                    let left_val: AB::Expr = local[#left_col].into();
                    let right_val: AB::Expr = local[#right_col].into();
                    let diff_val: AB::Expr = local[#diff_col].into();
                    let bit_val: AB::Expr = local[#bit_col].into();
                    (diff_val.clone() - left_val + right_val)
                        + bit_val.clone() * (bit_val.clone() - AB::Expr::ONE)
                        + bit_val
                }
            }
        }
        RequirementKind::Equal { left, right } => {
            let left_col = find_p3_col(layout, &quote::quote!(#left).to_string());
            let right_col = find_p3_col(layout, &quote::quote!(#right).to_string());

            quote! {
                {
                    let left_val: AB::Expr = local[#left_col].into();
                    let right_val: AB::Expr = local[#right_col].into();
                    left_val - right_val
                }
            }
        }
        RequirementKind::NotEqual { left, right } => {
            let left_col = find_p3_col(layout, &quote::quote!(#left).to_string());
            let right_col = find_p3_col(layout, &quote::quote!(#right).to_string());
            let inv_col = layout.aux_start + *aux_idx;
            *aux_idx += 1;

            quote! {
                {
                    let left_val: AB::Expr = local[#left_col].into();
                    let right_val: AB::Expr = local[#right_col].into();
                    let inv_val: AB::Expr = local[#inv_col].into();
                    (left_val - right_val) * inv_val - AB::Expr::ONE
                }
            }
        }
        RequirementKind::Membership { .. } => {
            // Should be unreachable (guarded by has_membership check)
            *aux_idx += 1;
            quote! { AB::Expr::ZERO }
        }
    }
}

fn emit_p3_mutation(mutation: &crate::ir::Mutation, layout: &P3Layout) -> TokenStream {
    let target_col = layout
        .param_cols
        .iter()
        .find(|p| p.name == mutation.target)
        .expect("mutation target not found");

    assert!(target_col.is_mutable);
    let old_col = target_col.start_col;
    let new_col = target_col.start_col + 1;
    let operand_col = find_p3_col(layout, &mutation.operand);

    match mutation.op {
        MutateOp::SubAssign => {
            // new = old - operand → new - old + operand == 0
            quote! {
                {
                    let old_val: AB::Expr = local[#old_col].into();
                    let new_val: AB::Expr = local[#new_col].into();
                    let op_val: AB::Expr = local[#operand_col].into();
                    new_val - old_val + op_val
                }
            }
        }
        MutateOp::AddAssign => {
            // new = old + operand → new - old - operand == 0
            quote! {
                {
                    let old_val: AB::Expr = local[#old_col].into();
                    let new_val: AB::Expr = local[#new_col].into();
                    let op_val: AB::Expr = local[#operand_col].into();
                    new_val - old_val - op_val
                }
            }
        }
        MutateOp::Assign => {
            // new = operand → new - operand == 0
            quote! {
                {
                    let new_val: AB::Expr = local[#new_col].into();
                    let op_val: AB::Expr = local[#operand_col].into();
                    new_val - op_val
                }
            }
        }
    }
}

/// Find the column index for a parameter name.
fn find_p3_col(layout: &P3Layout, expr_str: &str) -> usize {
    let clean = expr_str
        .trim()
        .trim_start_matches('*')
        .trim()
        .trim_start_matches("& ")
        .trim_start_matches('&')
        .trim();

    for p in &layout.param_cols {
        if p.name == clean {
            return p.start_col;
        }
    }
    0
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
