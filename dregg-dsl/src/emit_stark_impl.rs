//! Code generator: compile-time IR evaluation to concrete `impl StarkAir` blocks.
//!
//! This module evaluates the IR at macro expansion time to compute:
//! - Column indices (trace layout)
//! - Trace width
//! - Constraint degree
//! - Boundary constraint structure
//!
//! It then emits a STRUCT + TRAIT IMPL with all values baked in as constants,
//! rather than a runtime descriptor. The generated code implements
//! `dregg_circuit::stark::StarkAir` directly.
//!
//! The layout structs carry the full column bookkeeping (aux columns, per-param
//! widths, range-check/inverse/selector witness columns); not all of it is read
//! on every emission path yet, so a module-level `dead_code` allow keeps the
//! complete layout surface without per-field churn.
#![allow(dead_code)]

use proc_macro2::TokenStream;
use quote::{format_ident, quote};

use crate::ir::{ConstraintIr, MutateOp, ParamType, RequirementKind, Statement};

/// Number of bits used for range-check decomposition.
///
/// BabyBear has p = 2^31 - 2^27 + 1 ≈ 2^30.9, so p/2 ≈ 2^29.96. A value whose
/// bit-decomposition fits in `RANGE_CHECK_BITS` bits with the top bit forced to
/// zero is strictly less than 2^(RANGE_CHECK_BITS-1) = 2^29 < p/2, hence lies in
/// the "small non-negative" half of the field. This mirrors the sound range-check
/// gadget in `circuit/src/committed_threshold.rs` (`COMMITTED_DIFF_BITS = 30`).
const RANGE_CHECK_BITS: usize = 30;

/// Number of bits each inequality OPERAND is range-checked to.
///
/// ## The operand-domain assumption (load-bearing for soundness)
///
/// The inequality predicates (`<=`, `>=`) are proven via a diff range-check:
/// `right - left` (resp. `left - right`) is decomposed into bits and shown to be
/// a "small non-negative" field element. That is sound **only if the operands are
/// themselves small enough that the difference cannot WRAP around the field
/// modulus**. Without an operand bound a malicious prover picks `left = p - 1`,
/// `right = 0` (a genuine violation, `left > right`); then
/// `diff = right - left = -(p-1) ≡ 1 (mod p)`, a tiny value that passes the diff
/// range-check — the violation is accepted. (`committed_threshold.rs` is safe
/// because its values are bounded by their commitment context; the general DSL
/// caveat operands have no such guarantee.)
///
/// We close the wrap-around by range-checking **each operand** to `< 2^OPERAND_RANGE_BITS`.
/// With `OPERAND_RANGE_BITS = 29` and operands `left, right ∈ [0, 2^29)`:
///   - an honest diff lies in `[0, 2^29) ⊂ [0, 2^30)`, so it passes the 30-bit
///     diff range-check, and
///   - a genuine violation has true diff in `(-2^29, 0)`, whose canonical field
///     representative is `≥ p - 2^29 + 1 = 1_476_395_010 > 2^30`, so it CANNOT
///     fit the 30-bit diff window and is REJECTED.
/// Picking `left = p - 1` is now UNSATISFIABLE outright: `p - 1` does not fit in
/// 29 bits, so its operand range-check fails — the wrap-around is dead.
///
/// THE DOCUMENTED DOMAIN: these inequality predicates are sound for operands in
/// `[0, 2^29)`. A caveat that compares values `≥ 2^29` is OUT OF the provable
/// domain — the macro will emit constraints that are UNSATISFIABLE for such
/// operands (the proof simply cannot be produced), never silently unsound.
const OPERAND_RANGE_BITS: usize = 29;

/// Column layout computed at macro time.
struct TraceLayout {
    /// Total number of columns.
    width: usize,
    /// For each parameter: (name, start_col, num_cols, is_mutable).
    param_cols: Vec<ParamLayout>,
    /// Auxiliary columns start index.
    aux_start: usize,
    /// Auxiliary column assignments (one per constraint/requirement).
    aux_cols: Vec<AuxCol>,
}

struct ParamLayout {
    name: String,
    start_col: usize,
    num_cols: usize,
    is_mutable: bool,
}

/// An auxiliary column assigned during constraint compilation.
#[derive(Clone)]
enum AuxCol {
    /// Range check: a `diff_col` (the quantity proven non-negative / in range)
    /// followed by `RANGE_CHECK_BITS` contiguous bit columns starting at
    /// `bits_start`. The bits are the little-endian binary decomposition of
    /// `diff_col`; the most significant bit (`bits_start + RANGE_CHECK_BITS - 1`)
    /// is forced to zero so that `diff_col < 2^(RANGE_CHECK_BITS-1) < p/2`.
    RangeCheck { diff_col: usize, bits_start: usize },
    /// Inverse witness for NotEqual.
    Inverse { inv_col: usize },
    /// Selector column for match arms.
    Selector { sel_col: usize },
}

/// Compute the trace layout from IR at macro time.
fn compute_layout(ir: &ConstraintIr) -> TraceLayout {
    let mut width: usize = 0;
    let mut param_cols = Vec::new();

    for p in &ir.params {
        let base = match &p.ty {
            ParamType::U64 => 1,
            ParamType::ByteArray32 => 8,
            ParamType::ByteMatrix32(n) => 8 * (*n as usize),
            ParamType::Set => 1,
            ParamType::UserDefined(_) => 1,
        };
        let num_cols = if p.mutable { base * 2 } else { base };
        param_cols.push(ParamLayout {
            name: p.name.to_string(),
            start_col: width,
            num_cols,
            is_mutable: p.mutable,
        });
        width += num_cols;
    }

    let aux_start = width;
    let mut aux_cols = Vec::new();

    // Count auxiliary columns needed by traversing statements.
    count_aux_from_statements(&ir.statements, &mut width, &mut aux_cols);

    TraceLayout {
        width,
        param_cols,
        aux_start,
        aux_cols,
    }
}

fn count_aux_from_statements(
    statements: &[Statement],
    width: &mut usize,
    aux_cols: &mut Vec<AuxCol>,
) {
    for stmt in statements {
        match stmt {
            Statement::Require(req) => match &req.kind {
                RequirementKind::LessEqual { .. } | RequirementKind::GreaterEqual { .. } => {
                    // Diff range-check (right-left >= 0 / left-right >= 0).
                    let diff_col = *width;
                    let bits_start = *width + 1;
                    *width += 1 + RANGE_CHECK_BITS;
                    aux_cols.push(AuxCol::RangeCheck {
                        diff_col,
                        bits_start,
                    });
                    // Operand range-checks (close the wrap-around): each operand
                    // is constrained to < 2^OPERAND_RANGE_BITS so the diff cannot
                    // wrap the field modulus. Two RangeCheck blocks: left, right.
                    for _ in 0..2 {
                        let op_diff_col = *width;
                        let op_bits_start = *width + 1;
                        *width += 1 + RANGE_CHECK_BITS;
                        aux_cols.push(AuxCol::RangeCheck {
                            diff_col: op_diff_col,
                            bits_start: op_bits_start,
                        });
                    }
                }
                RequirementKind::Equal { .. } => {
                    // No auxiliary columns needed for equality.
                }
                RequirementKind::NotEqual { .. } => {
                    let inv_col = *width;
                    *width += 1;
                    aux_cols.push(AuxCol::Inverse { inv_col });
                }
                RequirementKind::Membership { .. } => {
                    // Membership constraints use Merkle proof columns.
                    // For the STARK impl we model this as a single hash column for now.
                    let _start = *width;
                    *width += 1; // commitment root column
                }
                RequirementKind::MerkleAtPosition { depth, .. } => {
                    *width += (*depth as usize) * 17;
                }
                RequirementKind::Poseidon2Hash { inputs, .. } => {
                    *width += inputs.len().max(1);
                }
                RequirementKind::BitRange { .. } => {
                    let diff_col = *width;
                    let bits_start = *width + 1;
                    *width += 1 + RANGE_CHECK_BITS;
                    aux_cols.push(AuxCol::RangeCheck {
                        diff_col,
                        bits_start,
                    });
                }
            },
            Statement::Mutate(_) => {
                // Mutations are encoded into the param layout (old/new columns).
                // No additional aux needed here.
            }
            Statement::Match { arms, .. } => {
                let sel_col = *width;
                *width += 1;
                aux_cols.push(AuxCol::Selector { sel_col });
                for arm in arms {
                    count_aux_from_statements(&arm.body, width, aux_cols);
                }
            }
        }
    }
}

/// Compute the maximum constraint degree from the IR.
fn compute_max_degree(ir: &ConstraintIr) -> usize {
    let mut max_deg: usize = 1;
    for stmt in &ir.statements {
        let d = statement_degree(stmt);
        if d > max_deg {
            max_deg = d;
        }
    }
    max_deg
}

fn statement_degree(stmt: &Statement) -> usize {
    match stmt {
        Statement::Require(req) => match &req.kind {
            RequirementKind::LessEqual { .. } | RequirementKind::GreaterEqual { .. } => 2,
            RequirementKind::Equal { .. } => 1,
            RequirementKind::NotEqual { .. } => 2, // a * inv = 1
            RequirementKind::Membership { .. } => 2,
            RequirementKind::MerkleAtPosition { .. } => 3,
            RequirementKind::Poseidon2Hash { .. } => 3,
            RequirementKind::BitRange { .. } => 2,
        },
        Statement::Mutate(_) => 1,
        Statement::Match { arms, .. } => {
            // Gated constraints: selector * inner => degree = 1 + inner_degree
            let inner_max = arms
                .iter()
                .flat_map(|arm| arm.body.iter())
                .map(|s| statement_degree(s))
                .max()
                .unwrap_or(1);
            1 + inner_max
        }
    }
}

/// Check if the IR contains any Membership constraints (directly or inside match arms).
fn has_membership_constraint(statements: &[Statement]) -> bool {
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
                    if has_membership_constraint(&arm.body) {
                        return true;
                    }
                }
            }
        }
    }
    false
}

/// Main entry point: emit a struct + impl StarkAir for the given IR.
///
/// If the IR contains Membership constraints, no STARK impl is emitted because
/// Membership requires explicit Merkle path columns that cannot be auto-generated.
pub fn emit_stark_impl(ir: &ConstraintIr) -> TokenStream {
    // Membership constraints cannot be compiled to a STARK AIR automatically.
    // Skip STARK codegen entirely rather than emitting unsound BabyBear::ZERO.
    if has_membership_constraint(&ir.statements) {
        return TokenStream::new();
    }

    let struct_name = format_ident!("{}Circuit", to_pascal_case(&ir.name.to_string()));
    let layout = compute_layout(ir);
    let width = layout.width;
    let degree = compute_max_degree(ir);
    let air_name = format!("dregg-{}-v1", ir.name);

    // Generate the constraint evaluation body.
    let constraint_body = emit_constraint_body(ir, &layout);

    // Generate boundary constraints.
    let boundary_body = emit_boundary_body(ir, &layout);

    // Generate trace generation helper.
    let trace_gen = emit_trace_generation(ir, &layout);

    quote! {
        pub struct #struct_name;

        impl dregg_circuit::stark::StarkAir for #struct_name {
            fn width(&self) -> usize { #width }
            fn constraint_degree(&self) -> usize { #degree }
            fn air_name(&self) -> &'static str { #air_name }
            fn has_chain_continuity(&self) -> bool { false }

            fn eval_constraints(
                &self,
                local: &[dregg_circuit::field::BabyBear],
                next: &[dregg_circuit::field::BabyBear],
                public_inputs: &[dregg_circuit::field::BabyBear],
                alpha: dregg_circuit::field::BabyBear,
            ) -> dregg_circuit::field::BabyBear {
                use dregg_circuit::field::BabyBear;
                let _ = next;
                let _ = public_inputs;
                #constraint_body
            }

            fn boundary_constraints(
                &self,
                public_inputs: &[dregg_circuit::field::BabyBear],
                _trace_len: usize,
            ) -> Vec<dregg_circuit::stark::BoundaryConstraint> {
                use dregg_circuit::field::BabyBear;
                use dregg_circuit::stark::BoundaryConstraint;
                let _ = public_inputs;
                #boundary_body
            }
        }

        impl #struct_name {
            #trace_gen
        }
    }
}

/// Emit the constraint evaluation body.
/// Each constraint becomes a polynomial expression composed with alpha powers.
fn emit_constraint_body(ir: &ConstraintIr, layout: &TraceLayout) -> TokenStream {
    let mut constraint_exprs: Vec<TokenStream> = Vec::new();
    let mut aux_idx = 0;
    emit_constraints_from_statements(
        &ir.statements,
        layout,
        &mut constraint_exprs,
        &mut aux_idx,
        None, // no selector gating at top level
    );

    if constraint_exprs.is_empty() {
        return quote! { BabyBear::ZERO };
    }

    // Compose: result = sum_i(alpha^i * c_i)
    let n = constraint_exprs.len();
    if n == 1 {
        let c = &constraint_exprs[0];
        quote! {
            let c0 = #c;
            c0
        }
    } else {
        let mut stmts = Vec::new();
        stmts.push(quote! { let mut result = BabyBear::ZERO; });
        stmts.push(quote! { let mut ap = BabyBear::ONE; });
        for (i, c) in constraint_exprs.iter().enumerate() {
            let ci = format_ident!("c{}", i);
            stmts.push(quote! {
                let #ci = #c;
                result = result + ap * #ci;
                ap = ap * alpha;
            });
        }
        stmts.push(quote! { result });
        quote! { #(#stmts)* }
    }
}

fn emit_constraints_from_statements(
    statements: &[Statement],
    layout: &TraceLayout,
    out: &mut Vec<TokenStream>,
    aux_idx: &mut usize,
    gating_selector: Option<usize>,
) {
    for stmt in statements {
        match stmt {
            Statement::Require(req) => {
                for expr in emit_requirement_constraints(req, layout, aux_idx) {
                    let gated = if let Some(sel_col) = gating_selector {
                        quote! { (local[#sel_col] * (#expr)) }
                    } else {
                        expr
                    };
                    out.push(gated);
                }
            }
            Statement::Mutate(mutation) => {
                let expr = emit_mutation_expr(mutation, layout);
                let gated = if let Some(sel_col) = gating_selector {
                    quote! { (local[#sel_col] * (#expr)) }
                } else {
                    expr
                };
                out.push(gated);
            }
            Statement::Match { arms, .. } => {
                // The selector column for this match.
                let sel_col = layout.aux_start + *aux_idx;
                // Actually, we stored it in aux_cols. Let's use a counter approach.
                // For simplicity, we track the selector column from the layout.
                // The selector was already counted during layout computation.
                // We need to find it. Let's just use the running aux_idx.
                // Skip the selector itself (it was counted in layout computation).
                *aux_idx += 1;

                // Binary constraint: selector * (selector - 1) == 0
                out.push(quote! {
                    (local[#sel_col] * (local[#sel_col] - BabyBear::ONE))
                });

                // Arm 0 is selected when selector == 0, Arm 1 when selector == 1.
                // For a 2-arm match: gate arm0 with (1 - selector), arm1 with selector.
                if arms.len() == 2 {
                    // First arm: gated by (1 - selector)
                    let inv_sel = quote! { (BabyBear::ONE - local[#sel_col]) };
                    for s in &arms[0].body {
                        match s {
                            Statement::Require(req) => {
                                for expr in emit_requirement_constraints(req, layout, aux_idx) {
                                    out.push(quote! { (#inv_sel * (#expr)) });
                                }
                            }
                            Statement::Mutate(mutation) => {
                                let expr = emit_mutation_expr(mutation, layout);
                                out.push(quote! { (#inv_sel * (#expr)) });
                            }
                            Statement::Match { .. } => {
                                // Nested match — recurse with gating.
                                // Not handling nested matches for now.
                            }
                        }
                    }
                    // Second arm: gated by selector
                    for s in &arms[1].body {
                        match s {
                            Statement::Require(req) => {
                                for expr in emit_requirement_constraints(req, layout, aux_idx) {
                                    out.push(quote! { (local[#sel_col] * (#expr)) });
                                }
                            }
                            Statement::Mutate(mutation) => {
                                let expr = emit_mutation_expr(mutation, layout);
                                out.push(quote! { (local[#sel_col] * (#expr)) });
                            }
                            Statement::Match { .. } => {}
                        }
                    }
                } else {
                    // General case: just emit ungated constraints for each arm.
                    // (A more complete implementation would use multi-value selectors.)
                    for arm in arms {
                        emit_constraints_from_statements(
                            &arm.body,
                            layout,
                            out,
                            aux_idx,
                            Some(sel_col),
                        );
                    }
                }
            }
        }
    }
}

/// Emit the constraint polynomial(s) for one requirement.
///
/// Returns a `Vec` of INDEPENDENT sub-constraints, each of which the AIR forces
/// to zero under its own random `alpha` power. This independence is load-bearing:
/// a range check is sound only if its bit-decomposition sub-constraints cannot
/// cancel one another. A single summed polynomial would let a malicious prover
/// trade a non-zero binary violation against a reconstruction error; separate
/// alpha-weighted constraints make every sub-constraint vanish independently.
fn emit_requirement_constraints(
    req: &crate::ir::Requirement,
    layout: &TraceLayout,
    aux_idx: &mut usize,
) -> Vec<TokenStream> {
    match &req.kind {
        RequirementKind::LessEqual { left, right } => {
            // Range check: right - left >= 0, proven via a genuine bit decomposition.
            let left_col = find_param_col(layout, &quote::quote!(#left).to_string());
            let right_col = find_param_col(layout, &quote::quote!(#right).to_string());
            let diff_col = layout.aux_start + *aux_idx;
            let bits_start = layout.aux_start + *aux_idx + 1;
            *aux_idx += 1 + RANGE_CHECK_BITS;
            let diff_def = quote! { local[#right_col] - local[#left_col] };
            let mut out =
                emit_range_check_constraints(diff_col, bits_start, RANGE_CHECK_BITS, &diff_def);
            // Operand range-checks close the wrap-around (see OPERAND_RANGE_BITS):
            // each operand must fit in OPERAND_RANGE_BITS bits, so the diff cannot
            // wrap the field modulus and a violation's wrapped diff stays > p/2.
            out.extend(emit_operand_range_checks(layout, aux_idx, left_col, right_col));
            out
        }
        RequirementKind::GreaterEqual { left, right } => {
            // Range check: left - right >= 0. Same gadget, diff = left - right.
            let left_col = find_param_col(layout, &quote::quote!(#left).to_string());
            let right_col = find_param_col(layout, &quote::quote!(#right).to_string());
            let diff_col = layout.aux_start + *aux_idx;
            let bits_start = layout.aux_start + *aux_idx + 1;
            *aux_idx += 1 + RANGE_CHECK_BITS;
            let diff_def = quote! { local[#left_col] - local[#right_col] };
            let mut out =
                emit_range_check_constraints(diff_col, bits_start, RANGE_CHECK_BITS, &diff_def);
            out.extend(emit_operand_range_checks(layout, aux_idx, left_col, right_col));
            out
        }
        RequirementKind::Equal { left, right } => {
            let left_col = find_param_col(layout, &quote::quote!(#left).to_string());
            let right_col = find_param_col(layout, &quote::quote!(#right).to_string());
            vec![quote! {
                (local[#left_col] - local[#right_col])
            }]
        }
        RequirementKind::NotEqual { left, right } => {
            // (a - b) * inv == 1, expressed as: (a - b) * inv - 1
            let left_col = find_param_col(layout, &quote::quote!(#left).to_string());
            let right_col = find_param_col(layout, &quote::quote!(#right).to_string());
            let inv_col = layout.aux_start + *aux_idx;
            *aux_idx += 1;
            vec![quote! {
                ((local[#left_col] - local[#right_col]) * local[#inv_col] - BabyBear::ONE)
            }]
        }
        RequirementKind::Membership { .. } => {
            // Membership constraints require explicit Merkle path witness columns.
            // This branch should be unreachable because emit_stark_impl() returns early
            // when membership constraints are present, but emit a compile_error as a
            // safety net in case the early-return check is bypassed.
            *aux_idx += 1;
            vec![quote! {
                compile_error!(
                    "Membership constraints cannot be compiled to a STARK AIR automatically. \
                     Use explicit Merkle path columns with Hash and Binary constraints."
                )
            }]
        }
        RequirementKind::MerkleAtPosition { .. } => {
            vec![quote! { BabyBear::ZERO }]
        }
        RequirementKind::Poseidon2Hash { .. } => {
            vec![quote! { BabyBear::ZERO }]
        }
        RequirementKind::BitRange { value, bits } => {
            // `in_range!(value, N)` asserts `value < 2^N`: decompose `value` into
            // `RANGE_CHECK_BITS` bits, bind the reconstruction, and force every bit
            // at index >= N to zero.
            let value_col = find_param_col(layout, &quote::quote!(#value).to_string());
            let diff_col = layout.aux_start + *aux_idx;
            let bits_start = layout.aux_start + *aux_idx + 1;
            *aux_idx += 1 + RANGE_CHECK_BITS;
            let active_bits = (*bits as usize).min(RANGE_CHECK_BITS);
            let value_def = quote! { local[#value_col] };
            emit_range_check_constraints(diff_col, bits_start, active_bits, &value_def)
        }
    }
}

/// Emit the INDEPENDENT sub-constraints of a range check forcing `value_def` to
/// be a non-negative integer representable in `active_bits` bits.
///
/// The sub-constraints (each forced to zero under its own alpha power) are:
///   1. `diff_col == value_def`                  (bind the witness column)
///   2. `sum_i(bit_i * 2^i) == diff_col`         (reconstruction)
///   3. `bit_i * (bit_i - 1) == 0` for every i   (one constraint per bit — binary)
///   4. `bit_i == 0` for every i >= active_bits  (top bits forced zero)
///
/// (2)+(3)+(4) force `diff_col` to equal a sum of `active_bits` genuine bits, so
/// `0 <= diff_col < 2^active_bits`. With `active_bits <= RANGE_CHECK_BITS (=30)`,
/// `2^active_bits <= 2^30 < p`, so a field-wrapped negative `value_def` (which
/// has a canonical representation >= p/2) is UNSATISFIABLE: its decomposition
/// would require bits above the allowed range. The bit constraints are emitted
/// SEPARATELY (not summed) so no two can cancel.
fn emit_range_check_constraints(
    diff_col: usize,
    bits_start: usize,
    active_bits: usize,
    value_def: &TokenStream,
) -> Vec<TokenStream> {
    let mut out = Vec::new();

    // (1) bind the diff/value column.
    out.push(quote! { (local[#diff_col] - (#value_def)) });

    // (2) reconstruction: sum_i bit_i * 2^i == diff_col.
    let mut recon_terms = Vec::new();
    for i in 0..RANGE_CHECK_BITS {
        let col = bits_start + i;
        recon_terms.push(quote! {
            recomposed = recomposed + local[#col] * pow2;
            pow2 = pow2 + pow2;
        });
    }
    out.push(quote! {
        {
            let mut recomposed = BabyBear::ZERO;
            let mut pow2 = BabyBear::ONE;
            #(#recon_terms)*
            recomposed - local[#diff_col]
        }
    });

    // (3) each bit binary — one independent constraint per bit.
    for i in 0..RANGE_CHECK_BITS {
        let col = bits_start + i;
        out.push(quote! {
            (local[#col] * (local[#col] - BabyBear::ONE))
        });
    }

    // (4) every bit at index >= active_bits forced to zero.
    for i in active_bits..RANGE_CHECK_BITS {
        let col = bits_start + i;
        out.push(quote! { (local[#col]) });
    }

    out
}

/// Emit the operand range-check sub-constraints for an inequality: both `left`
/// and `right` are constrained to `< 2^OPERAND_RANGE_BITS`, which closes the
/// field wrap-around (see `OPERAND_RANGE_BITS`). Advances `aux_idx` past the two
/// RangeCheck blocks reserved in `count_aux_from_statements`.
fn emit_operand_range_checks(
    layout: &TraceLayout,
    aux_idx: &mut usize,
    left_col: usize,
    right_col: usize,
) -> Vec<TokenStream> {
    let mut out = Vec::new();
    for operand_col in [left_col, right_col] {
        let op_diff_col = layout.aux_start + *aux_idx;
        let op_bits_start = layout.aux_start + *aux_idx + 1;
        *aux_idx += 1 + RANGE_CHECK_BITS;
        let value_def = quote! { local[#operand_col] };
        out.extend(emit_range_check_constraints(
            op_diff_col,
            op_bits_start,
            OPERAND_RANGE_BITS,
            &value_def,
        ));
    }
    out
}

fn emit_mutation_expr(mutation: &crate::ir::Mutation, layout: &TraceLayout) -> TokenStream {
    // Find the target's old and new columns.
    let target_layout = layout
        .param_cols
        .iter()
        .find(|p| p.name == mutation.target)
        .expect("mutation target not found in params");

    assert!(target_layout.is_mutable, "mutation target must be mutable");
    let old_col = target_layout.start_col;
    let new_col = target_layout.start_col + 1;

    // Find the operand column.
    let operand_col = find_param_col(layout, &mutation.operand);

    match mutation.op {
        MutateOp::SubAssign => {
            // new = old - operand => new - old + operand == 0
            quote! {
                (local[#new_col] - local[#old_col] + local[#operand_col])
            }
        }
        MutateOp::AddAssign => {
            // new = old + operand => new - old - operand == 0
            quote! {
                (local[#new_col] - local[#old_col] - local[#operand_col])
            }
        }
        MutateOp::Assign => {
            // new = operand => new - operand == 0
            quote! {
                (local[#new_col] - local[#operand_col])
            }
        }
    }
}

/// Find the column index for a given parameter name (by string matching).
fn find_param_col(layout: &TraceLayout, expr_str: &str) -> usize {
    // Strip dereference prefix if present (e.g., "* balance" -> "balance").
    let clean = expr_str
        .trim()
        .trim_start_matches('*')
        .trim()
        .trim_start_matches("& ")
        .trim_start_matches("&")
        .trim();

    for p in &layout.param_cols {
        if p.name == clean {
            return p.start_col;
        }
    }
    // If not found, return 0 as fallback (this shouldn't happen with valid IR).
    0
}

/// Emit boundary constraint body.
/// Binds the first row's parameter columns to the public inputs.
fn emit_boundary_body(ir: &ConstraintIr, layout: &TraceLayout) -> TokenStream {
    let mut boundary_entries = Vec::new();
    let mut pi_index = 0usize;

    for p in &layout.param_cols {
        if p.is_mutable {
            // For mutable params: bind old_value (col) to PI, and new_value (col+1) to PI+1.
            let old_col = p.start_col;
            let new_col = p.start_col + 1;
            let pi_old = pi_index;
            let pi_new = pi_index + 1;
            boundary_entries.push(quote! {
                BoundaryConstraint { row: 0, col: #old_col, value: public_inputs[#pi_old] }
            });
            boundary_entries.push(quote! {
                BoundaryConstraint { row: 0, col: #new_col, value: public_inputs[#pi_new] }
            });
            pi_index += 2;
        } else {
            // Skip Set/ByteArray32 for now (only bind u64 params).
            let is_bindable = ir.params.iter().any(|ip| {
                ip.name == p.name && matches!(ip.ty, ParamType::U64 | ParamType::UserDefined(_))
            });
            if is_bindable {
                let col = p.start_col;
                let pi_idx = pi_index;
                boundary_entries.push(quote! {
                    BoundaryConstraint { row: 0, col: #col, value: public_inputs[#pi_idx] }
                });
                pi_index += 1;
            }
        }
    }

    if boundary_entries.is_empty() {
        quote! { vec![] }
    } else {
        quote! {
            vec![#(#boundary_entries),*]
        }
    }
}

/// Emit trace generation helper method.
fn emit_trace_generation(ir: &ConstraintIr, layout: &TraceLayout) -> TokenStream {
    let width = layout.width;

    // Build parameter list for the generate_trace function.
    let mut fn_params = Vec::new();
    let mut row_assignments = Vec::new();

    for (i, p) in ir.params.iter().enumerate() {
        let pl = &layout.param_cols[i];
        let param_name = &p.name;

        match &p.ty {
            ParamType::U64 => {
                if p.mutable {
                    let old_name = format_ident!("{}_old", param_name);
                    let new_name = format_ident!("{}_new", param_name);
                    fn_params.push(quote! { #old_name: u64 });
                    fn_params.push(quote! { #new_name: u64 });
                    let old_col = pl.start_col;
                    let new_col = pl.start_col + 1;
                    row_assignments.push(quote! {
                        row[#old_col] = BabyBear::from_u64(#old_name);
                        row[#new_col] = BabyBear::from_u64(#new_name);
                    });
                } else {
                    fn_params.push(quote! { #param_name: u64 });
                    let col = pl.start_col;
                    row_assignments.push(quote! {
                        row[#col] = BabyBear::from_u64(#param_name);
                    });
                }
            }
            ParamType::UserDefined(_) => {
                // Selector: take as u32.
                fn_params.push(quote! { #param_name: u32 });
                let col = pl.start_col;
                row_assignments.push(quote! {
                    row[#col] = BabyBear::new(#param_name);
                });
            }
            _ => {
                // Skip Set/ByteArray32 in trace generation for now.
            }
        }
    }

    // Auxiliary column fill: compute diff/inv values.
    let aux_fill = emit_aux_fill(ir, layout);

    quote! {
        /// Generate a valid trace for this circuit.
        ///
        /// Returns a trace with `trace_len` rows (must be a power of 2, minimum 2).
        /// The first row contains the actual constraint witness; remaining rows are padded copies.
        pub fn generate_trace(
            &self,
            #(#fn_params),*
        ) -> Vec<Vec<dregg_circuit::field::BabyBear>> {
            use dregg_circuit::field::BabyBear;

            let width = #width;
            let mut row = vec![BabyBear::ZERO; width];
            #(#row_assignments)*
            #aux_fill

            // Pad to minimum 2 rows (power of two).
            vec![row.clone(), row]
        }
    }
}

/// Emit trace-generation code that fills a range-check's `diff_col` with
/// `value_def` and decomposes its canonical u32 into the `RANGE_CHECK_BITS`
/// little-endian bit columns starting at `bits_start`. Bit indices beyond the
/// active range simply come out zero for honest witnesses (the constraint forces
/// that anyway).
fn emit_range_check_fill(
    diff_col: usize,
    bits_start: usize,
    value_def: &TokenStream,
) -> TokenStream {
    let n = RANGE_CHECK_BITS;
    quote! {
        {
            let __rc_val = #value_def;
            row[#diff_col] = __rc_val;
            let __rc_bits = __rc_val.as_u32();
            for __rc_i in 0..#n {
                let __rc_bit = (__rc_bits >> __rc_i) & 1;
                row[#bits_start + __rc_i] = BabyBear::new(__rc_bit);
            }
        }
    }
}

/// Fill the two operand range-check blocks for an inequality: decompose each
/// operand (`left`, `right`) into its `RANGE_CHECK_BITS` little-endian bits.
/// Advances `aux_idx` to match `emit_operand_range_checks` exactly.
fn emit_operand_range_check_fill(
    layout: &TraceLayout,
    aux_idx: &mut usize,
    left_col: usize,
    right_col: usize,
    stmts: &mut Vec<TokenStream>,
) {
    for operand_col in [left_col, right_col] {
        let op_diff_col = layout.aux_start + *aux_idx;
        let op_bits_start = layout.aux_start + *aux_idx + 1;
        *aux_idx += 1 + RANGE_CHECK_BITS;
        let value_def = quote! { row[#operand_col] };
        stmts.push(emit_range_check_fill(op_diff_col, op_bits_start, &value_def));
    }
}

/// Emit code to fill auxiliary columns (diff, bit, inverse) in the trace row.
fn emit_aux_fill(ir: &ConstraintIr, layout: &TraceLayout) -> TokenStream {
    let mut stmts = Vec::new();
    let mut aux_idx = 0;

    emit_aux_fill_statements(&ir.statements, layout, &mut stmts, &mut aux_idx);

    quote! { #(#stmts)* }
}

fn emit_aux_fill_statements(
    statements: &[Statement],
    layout: &TraceLayout,
    stmts: &mut Vec<TokenStream>,
    aux_idx: &mut usize,
) {
    for stmt in statements {
        match stmt {
            Statement::Require(req) => match &req.kind {
                RequirementKind::LessEqual { left, right } => {
                    let left_col = find_param_col(layout, &quote::quote!(#left).to_string());
                    let right_col = find_param_col(layout, &quote::quote!(#right).to_string());
                    let diff_col = layout.aux_start + *aux_idx;
                    let bits_start = layout.aux_start + *aux_idx + 1;
                    *aux_idx += 1 + RANGE_CHECK_BITS;
                    let diff_def = quote! { row[#right_col] - row[#left_col] };
                    stmts.push(emit_range_check_fill(diff_col, bits_start, &diff_def));
                    emit_operand_range_check_fill(layout, aux_idx, left_col, right_col, stmts);
                }
                RequirementKind::GreaterEqual { left, right } => {
                    let left_col = find_param_col(layout, &quote::quote!(#left).to_string());
                    let right_col = find_param_col(layout, &quote::quote!(#right).to_string());
                    let diff_col = layout.aux_start + *aux_idx;
                    let bits_start = layout.aux_start + *aux_idx + 1;
                    *aux_idx += 1 + RANGE_CHECK_BITS;
                    let diff_def = quote! { row[#left_col] - row[#right_col] };
                    stmts.push(emit_range_check_fill(diff_col, bits_start, &diff_def));
                    emit_operand_range_check_fill(layout, aux_idx, left_col, right_col, stmts);
                }
                RequirementKind::Equal { .. } => {
                    // No auxiliary columns.
                }
                RequirementKind::NotEqual { left, right } => {
                    let left_col = find_param_col(layout, &quote::quote!(#left).to_string());
                    let right_col = find_param_col(layout, &quote::quote!(#right).to_string());
                    let inv_col = layout.aux_start + *aux_idx;
                    *aux_idx += 1;
                    stmts.push(quote! {
                        // inverse of (left - right)
                        let diff = row[#left_col] - row[#right_col];
                        row[#inv_col] = diff.inverse().unwrap_or(BabyBear::ZERO);
                    });
                }
                RequirementKind::Membership { .. } => {
                    *aux_idx += 1;
                }
                RequirementKind::MerkleAtPosition { depth, .. } => {
                    *aux_idx += (*depth as usize) * 17;
                }
                RequirementKind::Poseidon2Hash { inputs, .. } => {
                    *aux_idx += inputs.len().max(1);
                }
                RequirementKind::BitRange { value, .. } => {
                    let value_col = find_param_col(layout, &quote::quote!(#value).to_string());
                    let diff_col = layout.aux_start + *aux_idx;
                    let bits_start = layout.aux_start + *aux_idx + 1;
                    *aux_idx += 1 + RANGE_CHECK_BITS;
                    let value_def = quote! { row[#value_col] };
                    stmts.push(emit_range_check_fill(diff_col, bits_start, &value_def));
                }
            },
            Statement::Mutate(_) => {}
            Statement::Match { arms, .. } => {
                // selector column
                *aux_idx += 1;
                for arm in arms {
                    emit_aux_fill_statements(&arm.body, layout, stmts, aux_idx);
                }
            }
        }
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
