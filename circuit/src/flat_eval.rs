//! **The flat (compiled) descriptor-expression evaluator** — the same polynomials the boxed
//! AST walkers evaluate, off a contiguous postfix tape instead of a pointer chase.
//!
//! ## What this is, and what it is NOT
//!
//! The IR-v2 interpreters ([`crate::descriptor_ir2::Ir2Air`] / `Ir2UniAir`) evaluate the
//! Lean-emitted descriptor's expression trees at every `Air::eval` invocation — once per SIMD
//! pack-chunk of each instance's quotient domain on the prover's folder, once per symbolic
//! pass, once at zeta on the verifier's folder, and again under the recursion tower's builders.
//! The trees are `Box`-node ASTs (`LeanExpr` / `WindowExpr` / `ChalExpr` / `TableExpr`), so
//! every visit is a heap-pointer dereference plus an enum dispatch.
//!
//! This module compiles each tree ONCE (at `Ir2Air` construction) into a postfix tape
//! (`Vec<FlatOp>`) evaluated over a small reusable stack. **It authors no algebra and changes
//! no constraint**: the tape is the in-order traversal of the same tree, so the sequence of
//! `.into()` / `const_to_expr` / `+` / `*` operations — and therefore the produced `AB::Expr`,
//! for EVERY builder type: the symbolic Rc-DAG, the prover's packed values, the verifier's
//! extension values, the recursion tower's wire expressions — is operation-for-operation
//! identical to the recursive walk. The gate on that claim is byte-identical proofs
//! (`tests/air_interp_census.rs::bytes_sweep`), the LDE-layout precedent.
//!
//! ⚠ HOUSE LAW: the Lean descriptor remains the sole author of the constraints. This file is
//! prover-side evaluation machinery; if an edit here would change *what* is constrained rather
//! than *how fast the same polynomial is evaluated*, it does not belong here.
//!
//! ## Evaluation-order fidelity (the property everything hangs on)
//!
//! For `Add(a, b)` the recursive walk computes `eval(a)`, then `eval(b)`, then `a + b`. The
//! postfix tape is `[…a…, …b…, Add]`; evaluation pushes `eval(a)`, pushes `eval(b)`, then pops
//! `rhs` then `lhs` and pushes `lhs + rhs`. Same operand order, same operation order, same
//! associativity — so the symbolic builder constructs a structurally identical expression
//! graph and the degree analysis, constraint count and folding order are unchanged.

use p3_air::AirBuilder;
use p3_field::PrimeField32;

use crate::lean_descriptor_air::{LeanExpr, const_to_expr};
use crate::table_air::TableExpr;

/// One op of a compiled postfix tape. Leaves push; `Add`/`Mul` pop two and push one.
#[derive(Clone, Copy, Debug)]
pub(crate) enum FlatOp {
    /// Current-row column `c` (`LeanExpr::Var` / `WindowExpr::Loc` / `TableExpr::Loc`).
    Loc(u32),
    /// Next-row column `c`.
    Nxt(u32),
    /// A signed integer constant (reduced into the field exactly as `const_to_expr` does).
    Const(i64),
    /// The Fiat–Shamir challenge leaf (`ChalExpr::Chal`) — extension-field tapes only.
    Chal(u32),
    /// The shared-definition leaf (`TableExpr::Shr`) — table tapes only.
    Shr(u32),
    /// The preprocessed-row leaf (`TableExpr::Prep`) — table tapes only.
    Prep(u32),
    /// Pop rhs, pop lhs, push `lhs + rhs`.
    Add,
    /// Pop rhs, pop lhs, push `lhs * rhs`.
    Mul,
}

/// A compiled expression: the postfix tape of one boxed AST, with its evaluation-stack high
/// water mark precomputed so `eval_*` never reallocates mid-tape.
#[derive(Clone, Debug)]
pub(crate) struct FlatExpr {
    ops: Vec<FlatOp>,
    max_stack: usize,
}

fn finish(ops: Vec<FlatOp>) -> FlatExpr {
    // Simulate the stack once to record the high-water mark. Every leaf pushes one, every
    // binary op nets minus one; a well-formed tape (any tree traversal) never underflows and
    // ends at depth exactly 1.
    let mut depth = 0usize;
    let mut max = 0usize;
    for op in &ops {
        match op {
            FlatOp::Add | FlatOp::Mul => depth -= 1,
            _ => {
                depth += 1;
                max = max.max(depth);
            }
        }
    }
    debug_assert_eq!(
        depth, 1,
        "a compiled tape must evaluate to exactly one value"
    );
    FlatExpr {
        ops,
        max_stack: max,
    }
}

impl FlatExpr {
    /// Compile a [`LeanExpr`] (current-row only).
    pub(crate) fn of_lean(e: &LeanExpr) -> FlatExpr {
        fn push(e: &LeanExpr, ops: &mut Vec<FlatOp>) {
            match e {
                LeanExpr::Var(i) => ops.push(FlatOp::Loc(*i as u32)),
                LeanExpr::Const(c) => ops.push(FlatOp::Const(*c)),
                LeanExpr::Add(a, b) => {
                    push(a, ops);
                    push(b, ops);
                    ops.push(FlatOp::Add);
                }
                LeanExpr::Mul(a, b) => {
                    push(a, ops);
                    push(b, ops);
                    ops.push(FlatOp::Mul);
                }
            }
        }
        let mut ops = Vec::new();
        push(e, &mut ops);
        finish(ops)
    }

    /// Compile a [`crate::descriptor_ir2::WindowExpr`] (current + next row).
    pub(crate) fn of_window(e: &crate::descriptor_ir2::WindowExpr) -> FlatExpr {
        use crate::descriptor_ir2::WindowExpr as W;
        fn push(e: &W, ops: &mut Vec<FlatOp>) {
            match e {
                W::Loc(i) => ops.push(FlatOp::Loc(*i as u32)),
                W::Nxt(i) => ops.push(FlatOp::Nxt(*i as u32)),
                W::Const(c) => ops.push(FlatOp::Const(*c)),
                W::Add(a, b) => {
                    push(a, ops);
                    push(b, ops);
                    ops.push(FlatOp::Add);
                }
                W::Mul(a, b) => {
                    push(a, ops);
                    push(b, ops);
                    ops.push(FlatOp::Mul);
                }
            }
        }
        let mut ops = Vec::new();
        push(e, &mut ops);
        finish(ops)
    }

    /// Compile a [`crate::descriptor_ir2::ChalExpr`] (current + next row + challenges;
    /// evaluated in the extension field by [`FlatExpr::eval_ext`]).
    pub(crate) fn of_chal(e: &crate::descriptor_ir2::ChalExpr) -> FlatExpr {
        use crate::descriptor_ir2::ChalExpr as C;
        fn push(e: &C, ops: &mut Vec<FlatOp>) {
            match e {
                C::Loc(i) => ops.push(FlatOp::Loc(*i as u32)),
                C::Nxt(i) => ops.push(FlatOp::Nxt(*i as u32)),
                C::Const(c) => ops.push(FlatOp::Const(*c)),
                C::Chal(i) => ops.push(FlatOp::Chal(*i as u32)),
                C::Add(a, b) => {
                    push(a, ops);
                    push(b, ops);
                    ops.push(FlatOp::Add);
                }
                C::Mul(a, b) => {
                    push(a, ops);
                    push(b, ops);
                    ops.push(FlatOp::Mul);
                }
            }
        }
        let mut ops = Vec::new();
        push(e, &mut ops);
        finish(ops)
    }

    /// Compile a [`TableExpr`] (current + next row + shared defs + preprocessed row).
    pub(crate) fn of_table(e: &TableExpr) -> FlatExpr {
        fn push(e: &TableExpr, ops: &mut Vec<FlatOp>) {
            match e {
                TableExpr::Loc(i) => ops.push(FlatOp::Loc(*i as u32)),
                TableExpr::Nxt(i) => ops.push(FlatOp::Nxt(*i as u32)),
                TableExpr::Const(c) => ops.push(FlatOp::Const(*c)),
                TableExpr::Shr(i) => ops.push(FlatOp::Shr(*i as u32)),
                TableExpr::Prep(i) => ops.push(FlatOp::Prep(*i as u32)),
                TableExpr::Add(a, b) => {
                    push(a, ops);
                    push(b, ops);
                    ops.push(FlatOp::Add);
                }
                TableExpr::Mul(a, b) => {
                    push(a, ops);
                    push(b, ops);
                    ops.push(FlatOp::Mul);
                }
            }
        }
        let mut ops = Vec::new();
        push(e, &mut ops);
        finish(ops)
    }

    fn prepare<'s, T>(&self, stack: &'s mut Vec<T>) -> &'s mut Vec<T> {
        stack.clear();
        if stack.capacity() < self.max_stack {
            stack.reserve(self.max_stack - stack.capacity());
        }
        stack
    }

    /// Evaluate a base-field tape (`LeanExpr` / `WindowExpr` compilations) — the flat twin of
    /// `LeanExpr::eval_expr` / `WindowExpr::eval_expr`, operation-for-operation.
    ///
    /// `stack` is a caller-held scratch buffer, cleared here and reused across expressions so
    /// one `Air::eval` invocation allocates at most once.
    pub(crate) fn eval_base<AB>(
        &self,
        local: &[AB::Var],
        next: &[AB::Var],
        stack: &mut Vec<AB::Expr>,
    ) -> AB::Expr
    where
        AB: AirBuilder,
        AB::F: PrimeField32,
    {
        let stack = self.prepare(stack);
        for op in &self.ops {
            match *op {
                FlatOp::Loc(i) => stack.push(local[i as usize].into()),
                FlatOp::Nxt(i) => stack.push(next[i as usize].into()),
                FlatOp::Const(c) => stack.push(const_to_expr::<AB>(c)),
                FlatOp::Add => {
                    let rhs = stack.pop().expect("well-formed tape");
                    let lhs = stack.pop().expect("well-formed tape");
                    stack.push(lhs + rhs);
                }
                FlatOp::Mul => {
                    let rhs = stack.pop().expect("well-formed tape");
                    let lhs = stack.pop().expect("well-formed tape");
                    stack.push(lhs * rhs);
                }
                // `of_lean` / `of_window` never emit these; reaching one is a compiler defect,
                // and evaluating anything in its place would change what is constrained.
                FlatOp::Chal(_) | FlatOp::Shr(_) | FlatOp::Prep(_) => {
                    unreachable!("base tape carries a table/challenge leaf")
                }
            }
        }
        stack.pop().expect("a tape evaluates to exactly one value")
    }

    /// Evaluate a table tape — the flat twin of `eval_table_expr`, including its totality
    /// contract: an out-of-range `Shr` reads ZERO (unreachable past `LeanTableAir::check`,
    /// but the evaluator stays total).
    pub(crate) fn eval_table<AB>(
        &self,
        local: &[AB::Var],
        next: &[AB::Var],
        prep: &[AB::Var],
        dv: &[AB::Expr],
        stack: &mut Vec<AB::Expr>,
    ) -> AB::Expr
    where
        AB: AirBuilder,
        AB::F: PrimeField32,
    {
        use p3_field::PrimeCharacteristicRing;
        let stack = self.prepare(stack);
        for op in &self.ops {
            match *op {
                FlatOp::Loc(i) => stack.push(local[i as usize].into()),
                FlatOp::Nxt(i) => stack.push(next[i as usize].into()),
                FlatOp::Const(c) => stack.push(const_to_expr::<AB>(c)),
                FlatOp::Shr(i) => stack.push(
                    dv.get(i as usize)
                        .cloned()
                        .unwrap_or_else(|| AB::Expr::ZERO),
                ),
                FlatOp::Prep(i) => stack.push(prep[i as usize].into()),
                FlatOp::Add => {
                    let rhs = stack.pop().expect("well-formed tape");
                    let lhs = stack.pop().expect("well-formed tape");
                    stack.push(lhs + rhs);
                }
                FlatOp::Mul => {
                    let rhs = stack.pop().expect("well-formed tape");
                    let lhs = stack.pop().expect("well-formed tape");
                    stack.push(lhs * rhs);
                }
                FlatOp::Chal(_) => unreachable!("table tape carries a challenge leaf"),
            }
        }
        stack.pop().expect("a tape evaluates to exactly one value")
    }

    /// Evaluate a challenge tape in the EXTENSION field — the flat twin of
    /// `ChalExpr::eval_expr_ext`: base-field column reads are lifted into the extension, the
    /// challenge leaf clones the drawn randomness.
    pub(crate) fn eval_ext<AB>(
        &self,
        local: &[AB::Var],
        next: &[AB::Var],
        challenges: &[AB::ExprEF],
        stack: &mut Vec<AB::ExprEF>,
    ) -> AB::ExprEF
    where
        AB: AirBuilder + p3_air::ExtensionBuilder,
        AB::F: PrimeField32,
    {
        let stack = self.prepare(stack);
        for op in &self.ops {
            match *op {
                FlatOp::Loc(i) => {
                    stack.push(AB::ExprEF::from(Into::<AB::Expr>::into(local[i as usize])));
                }
                FlatOp::Nxt(i) => {
                    stack.push(AB::ExprEF::from(Into::<AB::Expr>::into(next[i as usize])));
                }
                FlatOp::Const(c) => stack.push(AB::ExprEF::from(const_to_expr::<AB>(c))),
                FlatOp::Chal(i) => stack.push(challenges[i as usize].clone()),
                FlatOp::Add => {
                    let rhs = stack.pop().expect("well-formed tape");
                    let lhs = stack.pop().expect("well-formed tape");
                    stack.push(lhs + rhs);
                }
                FlatOp::Mul => {
                    let rhs = stack.pop().expect("well-formed tape");
                    let lhs = stack.pop().expect("well-formed tape");
                    stack.push(lhs * rhs);
                }
                FlatOp::Shr(_) | FlatOp::Prep(_) => {
                    unreachable!("challenge tape carries a table leaf")
                }
            }
        }
        stack.pop().expect("a tape evaluates to exactly one value")
    }

    /// Tape length (for census/debug output).
    #[allow(dead_code)]
    pub(crate) fn len(&self) -> usize {
        self.ops.len()
    }
}

// ============================================================================
// The per-instance compilations — built once by the `Ir2Air` constructors from
// the SAME decoded descriptor the tree walk reads, index-parallel to it.
// ============================================================================

use crate::descriptor_ir2::{EffectVmDescriptor2, VmConstraint2};
use crate::lean_descriptor_air::VmConstraint;
use crate::table_air::LeanTableAir;

/// The flat compilation of one main-instance constraint, index-parallel to
/// `EffectVmDescriptor2::constraints`.
#[derive(Clone, Debug)]
pub(crate) enum CompiledK {
    /// Kinds whose expressions stay on the tree walk: the bus-bearing kinds
    /// (`Lookup`/`MemOp`/`MapOp`/`UMemOp` — their tuples are column lists, leaf-dominated per
    /// the §3 census in `tests/air_interp_census.rs`), `ProofBind` (guard + lanes, likewise),
    /// and the expression-free forms (`Transition`, `PiBinding`).
    Passthrough,
    /// `Gate` / `Boundary` / `WindowGate` — the one row-local polynomial body.
    Body(FlatExpr),
    /// `ChalGate` — the extension-field body ([`FlatExpr::eval_ext`]).
    ChalBody(FlatExpr),
}

/// The flat compilation of a main instance: the row-local algebra of
/// `eval_row_local_constraints` plus the submask recomposition pair.
#[derive(Clone, Debug)]
pub(crate) struct CompiledMain {
    /// Index-parallel to `desc.constraints`.
    pub(crate) constraints: Vec<CompiledK>,
    /// Index-parallel to the resolved layout's submask blocks: `(keep, held)`.
    pub(crate) submasks: Vec<(FlatExpr, FlatExpr)>,
}

impl CompiledMain {
    /// Compile the row-local algebra of `desc`. `submasks` is the resolved layout's submask
    /// expression pairs, in layout order (the layout type itself is private to
    /// `descriptor_ir2`, so the pairs arrive as an iterator).
    pub(crate) fn compile<'a>(
        desc: &EffectVmDescriptor2,
        submasks: impl Iterator<Item = (&'a LeanExpr, &'a LeanExpr)>,
    ) -> CompiledMain {
        let constraints = desc
            .constraints
            .iter()
            .map(|k| match k {
                VmConstraint2::Base(VmConstraint::Gate(body)) => {
                    CompiledK::Body(FlatExpr::of_lean(body))
                }
                VmConstraint2::Base(VmConstraint::Boundary { body, .. }) => {
                    CompiledK::Body(FlatExpr::of_lean(body))
                }
                VmConstraint2::WindowGate(w) => CompiledK::Body(FlatExpr::of_window(&w.body)),
                VmConstraint2::ChalGate(g) => CompiledK::ChalBody(FlatExpr::of_chal(&g.body)),
                VmConstraint2::Base(
                    VmConstraint::Transition { .. } | VmConstraint::PiBinding { .. },
                )
                | VmConstraint2::Lookup(_)
                | VmConstraint2::MemOp(_)
                | VmConstraint2::MapOp(_)
                | VmConstraint2::UMemOp(_)
                | VmConstraint2::ProofBind(_) => CompiledK::Passthrough,
            })
            .collect();
        let submasks = submasks
            .map(|(keep, held)| (FlatExpr::of_lean(keep), FlatExpr::of_lean(held)))
            .collect();
        CompiledMain {
            constraints,
            submasks,
        }
    }
}

/// The flat compilation of a Lean-authored table AIR: defs, gate bodies and interaction
/// expressions, each index-parallel to the wire object.
#[derive(Clone, Debug)]
pub(crate) struct CompiledTable {
    /// Index-parallel to `LeanTableAir::defs`.
    pub(crate) defs: Vec<FlatExpr>,
    /// Index-parallel to `LeanTableAir::gates` (body only; the selector is read off the gate).
    pub(crate) gates: Vec<FlatExpr>,
    /// Index-parallel to `LeanTableAir::interactions`: `(tuple, mult)`.
    pub(crate) interactions: Vec<(Vec<FlatExpr>, FlatExpr)>,
}

impl CompiledTable {
    /// Compile every expression of `air`.
    pub(crate) fn compile(air: &LeanTableAir) -> CompiledTable {
        CompiledTable {
            defs: air.defs.iter().map(FlatExpr::of_table).collect(),
            gates: air
                .gates
                .iter()
                .map(|g| FlatExpr::of_table(&g.body))
                .collect(),
            interactions: air
                .interactions
                .iter()
                .map(|it| {
                    (
                        it.tuple.iter().map(FlatExpr::of_table).collect(),
                        FlatExpr::of_table(&it.mult),
                    )
                })
                .collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // The unit-level fidelity check rides the integration harness (`tests/air_interp_census.rs`
    // byte sweep); here only the tape-shape invariants.
    #[test]
    fn tape_shape_and_stack_bound() {
        // (v0 + 3) * (v1 + v2) — depth-2 balanced tree.
        let e = LeanExpr::mul(
            LeanExpr::add(LeanExpr::var(0), LeanExpr::constant(3)),
            LeanExpr::add(LeanExpr::var(1), LeanExpr::var(2)),
        );
        let f = FlatExpr::of_lean(&e);
        assert_eq!(f.ops.len(), 7);
        assert_eq!(f.max_stack, 3);
        // Left-leaning Horner chain: the stack never grows past 2 however deep the chain is —
        // the reason a small reusable stack beats the recursive walk's call frames.
        let mut h = LeanExpr::var(0);
        for i in 1..20 {
            h = LeanExpr::add(LeanExpr::mul(h, LeanExpr::constant(31)), LeanExpr::var(i));
        }
        let fh = FlatExpr::of_lean(&h);
        assert_eq!(fh.max_stack, 2);
    }
}
