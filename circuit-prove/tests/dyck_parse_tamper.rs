//! # parse-as-derivation SLICE 2 — the Dyck pushdown stack with a REMAINDER SHIFT.
//!
//! Mirrors `circuit-prove/tests/derivation_emit_audit_extra.rs`: HONEST witnesses
//! ACCEPT and every single-tooth TAMPER REJECTS, so the acceptance is non-vacuous.
//!
//! The circuit is `dregg_circuit::dsl::dyck_stack` (`docs/DESIGN-parse-as-derivation.md`):
//! the `D = 5` bounded pushdown stack routing the Dyck grammar `S → [ S ] | ε`
//! (`metatheory/Dregg2/Crypto/CfgCompact.lean` `Reference`).
//!
//! Two honest words:
//!
//!   * `"[]"` — the word `CfgCompact.Reference.brackets_replays` accepts via the
//!     compact certificate `[rBracket, rEmpty]`. Slice 1 already verified it, because
//!     its `rBracket` never fires with anything under the popped `S`.
//!   * `"[[]]"` — the **nested** word slice 1 could NOT verify. Its second `rBracket`
//!     fires at stack `[S, cl]`; the outer `cl` must survive beneath the pushed
//!     `op S cl` or there is nothing left to close with. This is the slice-2 tooth.
//!
//! Acceptance here is the descriptor-satisfaction predicate `dyck_satisfied` (the Rust
//! `Satisfied2` analogue), which DRIVES the deployed `ConstraintExpr::evaluate_with_tables`
//! over the whole trace domain + boundaries. Each canary mutates ONE load-bearing tooth:
//!
//!   * a **stack cell** — breaks the `term` top-match and the `rBracket` push threading;
//!   * the **`RULE_ID`** — breaks the rule sub-selector pin (`SEL_BRACKET·(RULE_ID−1)==0`);
//!   * the **input token** — breaks the `term` top-match against the tape;
//!   * the **first-row stack depth** — breaks the `[initial]` boundary pin;
//!   * the **`route_commitment` public input** — breaks the last-row commitment binding;
//!   * the **shifted remainder** — breaks the slice-2 remainder shift (isolated by
//!     evaluating that single constraint, so the reject cannot be credited to a
//!     neighbouring tooth);
//!   * an **over-deep stack** — breaks the overflow guard, the honest statement of the
//!     `D` bound (a push that does not fit REJECTS instead of silently dropping);
//!   * a **WRAPPED / out-of-range depth** — breaks the depth range `0 ≤ STACK_DEPTH ≤ D`
//!     (isolated to that single vanishing poly). The depth deltas are field congruences,
//!     so a depth of `p − 1` reads as `−1` and satisfies every one of them; only the
//!     range tooth refuses it.
//!
//! **THE LOADER FLIP** (the second half of this file): the DEPLOYED Dyck descriptor is the
//! Lean-emitted, byte-pinned `DyckStackEmit.dyckParseDesc`, served by `descriptor_by_name`
//! (`dregg-dyck-parse-v1`). The `emitted_dyck_*` tests drive THAT object end-to-end through
//! `prove_vm_descriptor2`/`verify_vm_descriptor2`: both honest words accept, and each tamper
//! family above is re-fired at the emitted path and REJECTS. The v1 mirror above is retained
//! for its per-tooth isolation; the emitted section is the deployed accept/reject.

use std::panic::AssertUnwindSafe;

use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::dsl::circuit::{CircuitDescriptor, ConstraintExpr};
use dregg_circuit::dsl::dyck_stack::{
    DYCK_V2_WIDTH, RULE_EMPTY, STACK_D, SYM_CL, SYM_EMPTY, SYM_S, build_brackets_witness,
    build_nested_witness, col, dyck_parse_descriptor, dyck_satisfied, lift_witness_to_v2, pi,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};

const NAME: &str = "dregg-dyck-parse-v1";

/// The `"[]"` trace rows: `0 = rule rBracket`, `1 = term '['`, `2 = rule rEmpty`,
/// `3 = term ']'`, `4.. = done`.
const ROW_RULE_BRACKET: usize = 0;
const ROW_TERM_OPEN: usize = 1;

/// The `"[[]]"` trace rows: `0 = rule rBracket`, `1 = term '['`,
/// **`2 = rule rBracket` (the nested push, stack `[S, cl]`)**, `3 = term '['`,
/// `4 = rule rEmpty`, `5 = term ']'`, `6 = term ']'`, `7 = done`.
const NROW_NESTED_PUSH: usize = 2;
const NROW_AFTER_NESTED_PUSH: usize = 3;

// ============================================================================
// Honest acceptance
// ============================================================================

/// The honest `"[]"` parse satisfies the descriptor.
#[test]
fn brackets_parse_accepts() {
    let desc = dyck_parse_descriptor(NAME);
    let (trace, public_inputs) = build_brackets_witness();
    assert!(
        dyck_satisfied(&desc, &trace, &public_inputs),
        "the honest '[]' pushdown replay must ACCEPT"
    );
}

/// **The slice-2 headline.** The honest `"[[]]"` parse satisfies the descriptor — a
/// nested word, whose run needs the remainder preserved under a pushed RHS.
#[test]
fn nested_brackets_parse_accepts() {
    let desc = dyck_parse_descriptor(NAME);
    let (trace, public_inputs) = build_nested_witness();
    assert!(
        dyck_satisfied(&desc, &trace, &public_inputs),
        "the honest '[[]]' pushdown replay must ACCEPT"
    );
    // ...and it really is the nested case: the push at row 2 happens with `cl` under
    // the popped `S`, and that `cl` reappears at STACK3 of row 3.
    assert_eq!(
        trace[NROW_NESTED_PUSH][col::STACK1],
        BabyBear::new(SYM_CL),
        "row 2 must fire rBracket with a non-empty remainder"
    );
    assert_eq!(
        trace[NROW_AFTER_NESTED_PUSH][col::STACK3],
        BabyBear::new(SYM_CL),
        "the remainder must be shifted under the pushed RHS"
    );
}

// ============================================================================
// Constraint-isolating helpers — so a canary names the tooth that bit
// ============================================================================

/// Find the single `Gated{SEL_BRACKET, Transition{next_col, local_col}}` constraint —
/// one leg of the push / remainder shift. Panics if the descriptor does not contain
/// it (which would mean the shift was never wired, the slice-1 hole).
fn find_bracket_thread(
    desc: &CircuitDescriptor,
    next_col: usize,
    local_col: usize,
) -> &ConstraintExpr {
    desc.constraints
        .iter()
        .find(|c| match c {
            ConstraintExpr::Gated {
                selector_col,
                inner,
            } if *selector_col == col::SEL_BRACKET => matches!(
                **inner,
                ConstraintExpr::Transition { next_col: n, local_col: l } if n == next_col && l == local_col
            ),
            _ => false,
        })
        .unwrap_or_else(|| {
            panic!(
                "the descriptor must contain the SEL_BRACKET thread next[{next_col}] <- local[{local_col}]"
            )
        })
}

/// Find the `Gated{SEL_BRACKET, Polynomial}` overflow guard pinning `local.STACK[i]`
/// to EMPTY — the constraint that refuses a push whose remainder leaves the buffer.
fn find_bracket_overflow_guard(desc: &CircuitDescriptor, stack_col: usize) -> &ConstraintExpr {
    desc.constraints
        .iter()
        .find(|c| match c {
            ConstraintExpr::Gated {
                selector_col,
                inner,
            } if *selector_col == col::SEL_BRACKET => match &**inner {
                ConstraintExpr::Polynomial { terms } => {
                    terms.len() == 2 && terms[0].col_indices == vec![stack_col]
                }
                _ => false,
            },
            _ => false,
        })
        .unwrap_or_else(|| {
            panic!("the descriptor must contain the SEL_BRACKET overflow guard on col {stack_col}")
        })
}

/// Find the depth-range vanishing poly on `depth_col` — the degree-`(D+1)` product
/// `∏_{v=0}^{D} (depth − v)`, recognised as the only bare `Polynomial` all of whose terms
/// are powers of that one column, up to the grid degree. Panics if it was never wired
/// (which would mean the depth is pinned only by congruences — the pre-range hole).
fn find_depth_range(desc: &CircuitDescriptor, depth_col: usize) -> &ConstraintExpr {
    desc.constraints
        .iter()
        .find(|c| match c {
            ConstraintExpr::Polynomial { terms } => {
                terms.iter().any(|t| t.col_indices.len() == STACK_D + 1)
                    && terms
                        .iter()
                        .all(|t| t.col_indices.iter().all(|&i| i == depth_col))
            }
            _ => false,
        })
        .unwrap_or_else(|| {
            panic!("the descriptor must contain the depth-range poly on col {depth_col}")
        })
}

/// Find the **non-empty-below-pointer occupancy gate** for `cell` — the bare `Polynomial`
/// whose every term references only `{STACK[cell], STACK_DEPTH}` and in which `STACK[cell]`
/// appears to the 3rd power in its leading monomial (the cubic is-empty indicator
/// `(x−1)(x−2)(x−3)`). This is the tooth that refuses an `EMPTY` hole strictly below the
/// pointer; the linear empty-above gate (mult-1 in the cell) and the cell-range gate (no depth
/// column) are excluded by the shape. Panics if the depth↔occupancy tooth was never wired.
fn find_occupancy_nonempty_below(desc: &CircuitDescriptor, cell: usize) -> &ConstraintExpr {
    desc.constraints
        .iter()
        .find(|c| match c {
            ConstraintExpr::Polynomial { terms } => {
                let cols_ok = terms.iter().all(|t| {
                    t.col_indices
                        .iter()
                        .all(|&i| i == cell || i == col::STACK_DEPTH)
                });
                let refs_depth = terms
                    .iter()
                    .any(|t| t.col_indices.contains(&col::STACK_DEPTH));
                let cubic_in_cell = terms
                    .iter()
                    .map(|t| t.col_indices.iter().filter(|&&i| i == cell).count())
                    .max()
                    .unwrap_or(0)
                    == 3;
                cols_ok && refs_depth && cubic_in_cell
            }
            _ => false,
        })
        .unwrap_or_else(|| {
            panic!("the descriptor must contain the non-empty-below occupancy gate for cell {cell}")
        })
}

/// Find the **terminal-top gate** `Gated{IS_TERM, Polynomial}` whose polynomial is the quadratic
/// `(STACK0−op)(STACK0−cl)` — recognised as the only `IS_TERM`-gated `Polynomial` all of whose
/// terms reference only `STACK0`, with `STACK0` appearing squared in its leading monomial. This
/// excludes the `IS_TERM`-gated depth delta (which references `DEPTH_NEXT`/`STACK_DEPTH`). Panics if
/// the tooth was never wired — the state before the tape↔word correspondence was decodable.
fn find_terminal_top(desc: &CircuitDescriptor) -> &ConstraintExpr {
    desc.constraints
        .iter()
        .find(|c| match c {
            ConstraintExpr::Gated {
                selector_col,
                inner,
            } if *selector_col == col::IS_TERM => match &**inner {
                ConstraintExpr::Polynomial { terms } => {
                    terms
                        .iter()
                        .all(|t| t.col_indices.iter().all(|&i| i == col::STACK0))
                        && terms.iter().any(|t| {
                            t.col_indices.iter().filter(|&&i| i == col::STACK0).count() == 2
                        })
                }
                _ => false,
            },
            _ => false,
        })
        .unwrap_or_else(|| panic!("the descriptor must contain the IS_TERM terminal-top gate"))
}

// ============================================================================
// The terminal-top canary: a term row consumes a TERMINAL, never the nonterminal S
// ============================================================================

/// Canary — **a term row claims to consume the nonterminal `S`**. The `term` top-match
/// (`STACK0 == INPUT_TOKEN`) only ties the stack top to the tape symbol; nothing in the pre-tooth
/// descriptor forbade the consumed top being `S` rather than a terminal. That was the hole that
/// blocked DECODING the parsed word from the trace: a `term` row consuming `S` decodes to no `Brk`.
///
/// The reject is ISOLATED to the tooth: the single `IS_TERM·(STACK0−op)(STACK0−cl)` gate goes from
/// zero (honest, `STACK0 = op`) to nonzero (tampered, `STACK0 = S`), so it cannot be credited to a
/// neighbouring tooth.
#[test]
fn tamper_term_consumes_nonterminal_rejects() {
    let desc = dyck_parse_descriptor(NAME);
    let (trace, pi_vals) = build_brackets_witness();
    assert!(
        dyck_satisfied(&desc, &trace, &pi_vals),
        "the honest '[]' parse must satisfy the descriptor"
    );

    let gate = find_terminal_top(&desc);
    // Row 1 is `term '['`: its stack top is the terminal `op`, on the terminal grid.
    assert_eq!(
        gate.evaluate(&trace[ROW_TERM_OPEN], &trace[ROW_TERM_OPEN + 1], &pi_vals),
        BabyBear::ZERO,
        "an honest term row consumes a terminal (op)"
    );

    // Tamper: rewrite the term row's stack top as the NONTERMINAL S.
    let mut tampered = trace.clone();
    tampered[ROW_TERM_OPEN][col::STACK0] = BabyBear::new(dregg_circuit::dsl::dyck_stack::SYM_S);

    assert_ne!(
        gate.evaluate(
            &tampered[ROW_TERM_OPEN],
            &tampered[ROW_TERM_OPEN + 1],
            &pi_vals
        ),
        BabyBear::ZERO,
        "THE TOOTH: a term row consuming the nonterminal S is off the terminal grid"
    );
    assert!(
        !dyck_satisfied(&desc, &tampered, &pi_vals),
        "a term row consuming the nonterminal S must REJECT"
    );
}

// ============================================================================
// The depth↔occupancy canary: STACK_DEPTH must count the non-EMPTY prefix
// ============================================================================

/// Canary — **a hole below the pointer**. The design named the depth↔occupancy invariant as
/// the missing tooth: `STACK_DEPTH` pinned a value but nothing tied it to WHICH cells are
/// nonzero, so a trace could claim depth 4 while a cell strictly below the pointer sat `EMPTY`.
/// The nested run's row 3 is `[op, S, cl, cl]` at depth 4; blank cell 1 (`S`) to `EMPTY` while
/// leaving depth 4.
///
/// The reject is ISOLATED to the tooth: the single non-empty-below gate for cell 1 —
/// `(STACK[1]−1)(STACK[1]−2)(STACK[1]−3) · (STACK_DEPTH)(STACK_DEPTH−1)` — goes from zero
/// (honest) to nonzero (hole), so it cannot be credited to the neighbouring shift equations.
#[test]
fn tamper_occupancy_hole_below_pointer_rejects() {
    let desc = dyck_parse_descriptor(NAME);
    let (trace, public_inputs) = build_nested_witness();
    assert!(
        dyck_satisfied(&desc, &trace, &public_inputs),
        "the honest '[[]]' parse must satisfy the descriptor"
    );

    let gate = find_occupancy_nonempty_below(&desc, col::STACK1);
    assert_eq!(
        gate.evaluate(
            &trace[NROW_AFTER_NESTED_PUSH],
            &trace[NROW_AFTER_NESTED_PUSH],
            &public_inputs
        ),
        BabyBear::ZERO,
        "cell 1 is a live symbol below the pointer on the honest run"
    );

    let mut tampered = trace.clone();
    tampered[NROW_AFTER_NESTED_PUSH][col::STACK1] = BabyBear::new(SYM_EMPTY);

    assert_ne!(
        gate.evaluate(
            &tampered[NROW_AFTER_NESTED_PUSH],
            &tampered[NROW_AFTER_NESTED_PUSH],
            &public_inputs
        ),
        BabyBear::ZERO,
        "THE TOOTH: an EMPTY hole strictly below the pointer is off-occupancy"
    );
    assert!(
        !dyck_satisfied(&desc, &tampered, &public_inputs),
        "a hole below the pointer must REJECT"
    );
}

/// Canary — **the pointer overclaims occupancy**. Take the `"[]"` run's row 3 (`[cl]`, depth 1)
/// and push the pointer to depth 2 while cell 1 stays `EMPTY`: `STACK_DEPTH` now counts two live
/// cells but only one is nonzero. The non-empty-below gate for cell 1 refuses the phantom cell.
#[test]
fn tamper_occupancy_overclaimed_depth_rejects() {
    let desc = dyck_parse_descriptor(NAME);
    let (trace, public_inputs) = build_brackets_witness();
    assert!(
        dyck_satisfied(&desc, &trace, &public_inputs),
        "baseline must accept"
    );

    let gate = find_occupancy_nonempty_below(&desc, col::STACK1);
    let mut tampered = trace.clone();
    // Row 3 is `term ']'` at depth 1 (cell 0 = cl live, cells 1.. EMPTY). Claim depth 2.
    tampered[3][col::STACK_DEPTH] = BabyBear::new(2);
    tampered[3][col::DEPTH_NEXT] = BabyBear::new(1);

    assert_ne!(
        gate.evaluate(&tampered[3], &tampered[3], &public_inputs),
        BabyBear::ZERO,
        "THE TOOTH: cell 1 EMPTY while the pointer claims it is occupied is off-occupancy"
    );
    assert!(
        !dyck_satisfied(&desc, &tampered, &public_inputs),
        "an over-claimed STACK_DEPTH must REJECT"
    );
}

// ============================================================================
// The depth-range canaries: a WRAPPED depth is REFUSED
// ============================================================================

/// Canary — **wrap the stack depth**. On the honest `"[]"` run, row 3 is `term ']'` at
/// depth `1 → 0`. Rewrite it as depth `p − 1` (`= −1`) with `DEPTH_NEXT = p − 2` (`= −2`):
/// a stack that popped below empty and wrapped the field.
///
/// The reject is ISOLATED to the range tooth, and the test first PROVES the wrap is
/// invisible to the constraint that was supposed to be pinning the depth: the `term` delta
/// `IS_TERM·(DEPTH_NEXT − STACK_DEPTH + 1)` still evaluates to zero, because
/// `(−2) − (−1) + 1 = 0` holds over the field just as it does over ℤ. Only the vanishing
/// poly sees that `p − 1` is not one of `{0, …, D}`.
#[test]
fn tamper_wrapped_depth_rejects() {
    let desc = dyck_parse_descriptor(NAME);
    let (trace, pi_vals) = build_brackets_witness();
    assert!(
        dyck_satisfied(&desc, &trace, &pi_vals),
        "the honest '[]' parse must satisfy the descriptor"
    );

    const ROW_TERM_CLOSE: usize = 3;
    let mut tampered = trace.clone();
    tampered[ROW_TERM_CLOSE][col::STACK_DEPTH] = -BabyBear::ONE; // p - 1
    tampered[ROW_TERM_CLOSE][col::DEPTH_NEXT] = -BabyBear::new(2); // p - 2

    // The wrapped cells really are the huge field elements, not small negatives.
    assert_eq!(
        tampered[ROW_TERM_CLOSE][col::STACK_DEPTH],
        BabyBear::new(BABYBEAR_P - 1),
        "the tampered depth is p - 1"
    );

    // FIRST: the depth DELTA — the tooth that was supposed to pin depth — does NOT bite.
    let delta = desc
        .constraints
        .iter()
        .find(|c| {
            matches!(c, ConstraintExpr::Gated { selector_col, inner }
            if *selector_col == col::IS_TERM
               && matches!(**inner, ConstraintExpr::Polynomial { .. }))
        })
        .expect("the term depth delta must exist");
    assert_eq!(
        delta.evaluate(
            &tampered[ROW_TERM_CLOSE],
            &tampered[ROW_TERM_CLOSE + 1],
            &pi_vals
        ),
        BabyBear::ZERO,
        "the wrap is INVISIBLE to the depth delta — this is the hole the range closes"
    );

    // SECOND: the RANGE tooth, isolated — honest zero, tampered nonzero.
    let range = find_depth_range(&desc, col::STACK_DEPTH);
    assert_eq!(
        range.evaluate(&trace[ROW_TERM_CLOSE], &trace[ROW_TERM_CLOSE + 1], &pi_vals),
        BabyBear::ZERO,
        "the honest depth is ON the grid"
    );
    assert_ne!(
        range.evaluate(
            &tampered[ROW_TERM_CLOSE],
            &tampered[ROW_TERM_CLOSE + 1],
            &pi_vals
        ),
        BabyBear::ZERO,
        "THE TOOTH: the wrapped depth is OFF the grid"
    );

    // And the whole descriptor refuses the trace.
    assert!(
        !dyck_satisfied(&desc, &tampered, &pi_vals),
        "a wrapped STACK_DEPTH must REJECT"
    );
}

/// Canary — **an over-deep depth**. `STACK_DEPTH = D + 1` is one push past the buffer: a
/// legal-looking small integer that is nonetheless not an occupancy the `D`-cell stack can
/// have. The range tooth refuses it.
#[test]
fn tamper_overflowing_depth_rejects() {
    let desc = dyck_parse_descriptor(NAME);
    let (trace, pi_vals) = build_brackets_witness();
    let range = find_depth_range(&desc, col::STACK_DEPTH);

    let mut tampered = trace.clone();
    tampered[ROW_TERM_OPEN][col::STACK_DEPTH] = BabyBear::new(STACK_D as u32 + 1);

    assert_ne!(
        range.evaluate(
            &tampered[ROW_TERM_OPEN],
            &tampered[ROW_TERM_OPEN + 1],
            &pi_vals
        ),
        BabyBear::ZERO,
        "a depth of D + 1 is off the grid"
    );
    assert!(
        !dyck_satisfied(&desc, &tampered, &pi_vals),
        "an over-deep STACK_DEPTH must REJECT"
    );
}

/// The `DEPTH_NEXT` witness column carries its OWN range tooth — it is not left to be read
/// back through the `Transition{STACK_DEPTH <- DEPTH_NEXT}` (which would leave the last
/// row's `DEPTH_NEXT` free).
#[test]
fn depth_next_carries_its_own_range() {
    let desc = dyck_parse_descriptor(NAME);
    let (trace, pi_vals) = build_brackets_witness();
    let range = find_depth_range(&desc, col::DEPTH_NEXT);

    let mut tampered = trace.clone();
    tampered[ROW_RULE_BRACKET][col::DEPTH_NEXT] = -BabyBear::ONE;
    assert_ne!(
        range.evaluate(
            &tampered[ROW_RULE_BRACKET],
            &tampered[ROW_RULE_BRACKET + 1],
            &pi_vals
        ),
        BabyBear::ZERO,
        "a wrapped DEPTH_NEXT is off the grid"
    );
    assert!(
        !dyck_satisfied(&desc, &tampered, &pi_vals),
        "a wrapped DEPTH_NEXT must REJECT"
    );
}

// ============================================================================
// The slice-2 canaries: the remainder shift is REAL
// ============================================================================

/// Canary — **drop the shifted remainder**. On the honest `"[[]]"` run, zero the cell
/// the remainder shift wrote (`row 3`'s `STACK3`, the outer `cl`). This is exactly
/// what slice 1's push did: write `(op, S, cl)` and let whatever was under the popped
/// `S` evaporate.
///
/// The reject is ISOLATED to the shift: the test evaluates the single constraint
/// `Gated{SEL_BRACKET, Transition{next.STACK3 <- local.STACK1}}` at the push row, and
/// it goes from zero (honest) to nonzero (tampered). So this canary cannot be
/// credited to a neighbouring tooth — the remainder shift itself is what bites.
#[test]
fn tamper_dropped_remainder_rejects() {
    let desc = dyck_parse_descriptor(NAME);
    let (mut trace, public_inputs) = build_nested_witness();
    assert!(
        dyck_satisfied(&desc, &trace, &public_inputs),
        "baseline must accept"
    );

    let shift = find_bracket_thread(&desc, col::STACK3, col::STACK1);
    assert_eq!(
        shift.evaluate(
            &trace[NROW_NESTED_PUSH],
            &trace[NROW_AFTER_NESTED_PUSH],
            &public_inputs
        ),
        BabyBear::ZERO,
        "the remainder shift must hold on the honest nested run"
    );

    // The slice-1 push: the remainder under the popped S evaporates.
    trace[NROW_AFTER_NESTED_PUSH][col::STACK3] = BabyBear::new(SYM_EMPTY);

    assert_ne!(
        shift.evaluate(
            &trace[NROW_NESTED_PUSH],
            &trace[NROW_AFTER_NESTED_PUSH],
            &public_inputs
        ),
        BabyBear::ZERO,
        "the remainder shift ALONE must reject a dropped remainder"
    );
    assert!(
        !dyck_satisfied(&desc, &trace, &public_inputs),
        "a dropped remainder must REJECT"
    );
}

/// Canary — **forge the shifted remainder**: keep a symbol there, but the wrong one
/// (`S` where the run carries `cl`). A shift that merely required "something nonzero"
/// would pass; the `Transition` pins the exact source cell.
#[test]
fn tamper_forged_remainder_symbol_rejects() {
    let desc = dyck_parse_descriptor(NAME);
    let (mut trace, public_inputs) = build_nested_witness();
    assert!(
        dyck_satisfied(&desc, &trace, &public_inputs),
        "baseline must accept"
    );

    let shift = find_bracket_thread(&desc, col::STACK3, col::STACK1);
    trace[NROW_AFTER_NESTED_PUSH][col::STACK3] =
        BabyBear::new(dregg_circuit::dsl::dyck_stack::SYM_S);

    assert_ne!(
        shift.evaluate(
            &trace[NROW_NESTED_PUSH],
            &trace[NROW_AFTER_NESTED_PUSH],
            &public_inputs
        ),
        BabyBear::ZERO,
        "the remainder shift pins the SOURCE cell, not merely occupancy"
    );
    assert!(
        !dyck_satisfied(&desc, &trace, &public_inputs),
        "a forged remainder symbol must REJECT"
    );
}

/// Canary — **the overflow guard**. Park a live symbol in the deepest cell a
/// `rBracket` push cannot carry (`STACK3` of the push row, whose shifted destination
/// `STACK5` is outside the `D = 5` buffer). Without the guard the push would silently
/// DROP it — the slice-1 unsoundness wearing a wider hat. The guard turns it into a
/// refusal.
///
/// Isolated the same way: the single `Gated{SEL_BRACKET, STACK3 == 0}` constraint
/// goes from zero to nonzero.
#[test]
fn tamper_overflowing_push_rejects() {
    let desc = dyck_parse_descriptor(NAME);
    let (mut trace, public_inputs) = build_nested_witness();
    assert!(
        dyck_satisfied(&desc, &trace, &public_inputs),
        "baseline must accept"
    );

    let guard = find_bracket_overflow_guard(&desc, col::STACK3);
    assert_eq!(
        guard.evaluate(
            &trace[NROW_NESTED_PUSH],
            &trace[NROW_AFTER_NESTED_PUSH],
            &public_inputs
        ),
        BabyBear::ZERO,
        "the honest nested push does not overflow"
    );

    // a symbol whose shifted home would be STACK5 — off the end of the buffer.
    trace[NROW_NESTED_PUSH][col::STACK3] = BabyBear::new(SYM_CL);

    assert_ne!(
        guard.evaluate(
            &trace[NROW_NESTED_PUSH],
            &trace[NROW_AFTER_NESTED_PUSH],
            &public_inputs
        ),
        BabyBear::ZERO,
        "the overflow guard ALONE must reject a push whose remainder leaves the buffer"
    );
    assert!(
        !dyck_satisfied(&desc, &trace, &public_inputs),
        "an overflowing push must REJECT"
    );
}

/// Canary — **mutate the nested run's remainder SOURCE**: the `cl` sitting under the
/// popped `S` at the push row. The remainder shift carries whatever is there, so the
/// forged source must fail to reconcile with the row it came from (the preceding
/// `term`'s shift-down) and with the row it feeds.
#[test]
fn tamper_nested_remainder_source_rejects() {
    let desc = dyck_parse_descriptor(NAME);
    let (mut trace, public_inputs) = build_nested_witness();
    assert!(
        dyck_satisfied(&desc, &trace, &public_inputs),
        "baseline must accept"
    );

    trace[NROW_NESTED_PUSH][col::STACK1] = BabyBear::new(SYM_EMPTY);
    assert!(
        !dyck_satisfied(&desc, &trace, &public_inputs),
        "a mutated remainder source must REJECT"
    );
}

// ============================================================================
// The slice-1 canaries (retained — the teeth they cover did not move)
// ============================================================================

/// Canary — mutate a **stack cell**: flip the `term '['` row's stack top from `op` to
/// `cl`. The `term` top-match (`STACK0 == INPUT_TOKEN`) and the `rBracket` push
/// (`next.STACK0 == op`) both break.
#[test]
fn tamper_stack_cell_rejects() {
    let desc = dyck_parse_descriptor(NAME);
    let (mut trace, public_inputs) = build_brackets_witness();
    assert!(
        dyck_satisfied(&desc, &trace, &public_inputs),
        "baseline must accept"
    );

    trace[ROW_TERM_OPEN][col::STACK0] = BabyBear::new(SYM_CL);
    assert!(
        !dyck_satisfied(&desc, &trace, &public_inputs),
        "a mutated stack cell must REJECT"
    );
}

/// Canary — mutate the **`RULE_ID`**: claim the first row fires `rEmpty` while its
/// `SEL_BRACKET` selector is still 1. The rule sub-selector pin
/// `SEL_BRACKET·(RULE_ID − rBracket) == 0` breaks.
#[test]
fn tamper_rule_id_rejects() {
    let desc = dyck_parse_descriptor(NAME);
    let (mut trace, public_inputs) = build_brackets_witness();
    assert!(
        dyck_satisfied(&desc, &trace, &public_inputs),
        "baseline must accept"
    );

    trace[ROW_RULE_BRACKET][col::RULE_ID] = BabyBear::new(RULE_EMPTY);
    assert!(
        !dyck_satisfied(&desc, &trace, &public_inputs),
        "a forged RULE_ID (selector/rule mismatch) must REJECT"
    );
}

/// Canary — mutate the **input token**: the `term '['` row reads `']'` off the tape
/// instead of `'['`. The `term` top-match (`STACK0 == INPUT_TOKEN`) breaks.
#[test]
fn tamper_input_token_rejects() {
    let desc = dyck_parse_descriptor(NAME);
    let (mut trace, public_inputs) = build_brackets_witness();
    assert!(
        dyck_satisfied(&desc, &trace, &public_inputs),
        "baseline must accept"
    );

    trace[ROW_TERM_OPEN][col::INPUT_TOKEN] = BabyBear::new(SYM_CL);
    assert!(
        !dyck_satisfied(&desc, &trace, &public_inputs),
        "a forged input token must REJECT"
    );
}

/// Canary — mutate the **first-row stack depth**: start at depth 2 instead of 1. The
/// `[initial]`-stack boundary pin (`STACK_DEPTH first == 1`) breaks.
#[test]
fn tamper_initial_depth_rejects() {
    let desc = dyck_parse_descriptor(NAME);
    let (mut trace, public_inputs) = build_brackets_witness();
    assert!(
        dyck_satisfied(&desc, &trace, &public_inputs),
        "baseline must accept"
    );

    trace[0][col::STACK_DEPTH] = BabyBear::new(2);
    assert!(
        !dyck_satisfied(&desc, &trace, &public_inputs),
        "a forged initial stack depth must REJECT"
    );
}

/// Canary — mutate the **`route_commitment` public input**: claim a different parse
/// commitment than the trace's last-row `RUNNING_HASH`. The last-row PI boundary
/// binding breaks (the parse cannot claim a commitment it did not compute).
#[test]
fn tamper_route_commitment_rejects() {
    let desc = dyck_parse_descriptor(NAME);
    let (trace, mut public_inputs) = build_brackets_witness();
    assert!(
        dyck_satisfied(&desc, &trace, &public_inputs),
        "baseline must accept"
    );

    public_inputs[pi::ROUTE_COMMITMENT] += BabyBear::ONE;
    assert!(
        !dyck_satisfied(&desc, &trace, &public_inputs),
        "a forged route_commitment must REJECT"
    );
}

/// Canary — the **nested** run's `route_commitment` binds too: the `"[[]]"` parse
/// commits to its own 8-step fold, not `"[]"`'s.
#[test]
fn nested_and_flat_commitments_differ() {
    let (flat, flat_pi) = build_brackets_witness();
    let (nested, nested_pi) = build_nested_witness();
    let _ = (&flat, &nested);
    assert_ne!(
        flat_pi[pi::ROUTE_COMMITMENT],
        nested_pi[pi::ROUTE_COMMITMENT],
        "different parses must fold to different route_commitments"
    );
}

// ============================================================================
// THE LOADER FLIP: the DEPLOYED path is the Lean-emitted descriptor, LOADED
// by `descriptor_by_name` and proven through the real IR-v2 batch prover.
//
// Everything above this line drives the hand-authored IR-v1 mirror
// (`dyck_parse_descriptor` + `dyck_satisfied`) — retained because its
// pattern-matched constraint ISOLATION credits each reject to a named tooth.
// Everything below drives the byte-pinned emitted descriptor
// (`DyckStackEmit.lean` → `circuit/descriptors/by-name/dyck-parse.json`)
// end-to-end: honest witnesses PROVE + VERIFY, tampers REJECT through
// `prove_vm_descriptor2`/`verify_vm_descriptor2` — the same accept/reject the
// production dispatch serves.
// ============================================================================

/// The dispatched, Lean-emitted Dyck descriptor.
fn emitted_desc() -> EffectVmDescriptor2 {
    let desc = descriptor_by_name("dregg-dyck-parse-v1")
        .expect("the deployed by-name dispatch must serve the Lean-emitted Dyck descriptor");
    assert_eq!(desc.trace_width, DYCK_V2_WIDTH, "the emitted 38-wide shape");
    desc
}

/// Prove + verify through the emitted descriptor; `false` on ANY refusal (the pre-flight
/// replay's `Err`, a prover panic, or a verifier reject).
fn v2_accepts(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }));
    matches!(r, Ok(Ok(())))
}

/// **The flip's headline**: the honest `"[]"` parse PROVES and VERIFIES through the LOADED
/// emitted descriptor — and a forged `route_commitment` public input is REJECTED by the
/// verifier on the SAME proof, so the accept is non-vacuous and the PI binding is real.
#[test]
fn emitted_dyck_brackets_proves_and_verifies() {
    let desc = emitted_desc();
    let (trace, pis) = build_brackets_witness();
    let v2 = lift_witness_to_v2(&trace);

    let proof = prove_vm_descriptor2(&desc, &v2, &pis, &MemBoundaryWitness::default(), &[])
        .expect("the honest '[]' parse must prove through the emitted descriptor");
    verify_vm_descriptor2(&desc, &proof, &pis).expect("the honest proof must verify");

    let mut forged = pis.clone();
    forged[pi::ROUTE_COMMITMENT] += BabyBear::ONE;
    assert!(
        verify_vm_descriptor2(&desc, &proof, &forged).is_err(),
        "a forged route_commitment must be REJECTED by the verifier (last-row PiBinding)"
    );
}

/// The honest **nested** `"[[]]"` parse — the slice-2 remainder-shift word — proves and
/// verifies through the emitted descriptor too.
#[test]
fn emitted_dyck_nested_proves_and_verifies() {
    let desc = emitted_desc();
    let (trace, pis) = build_nested_witness();
    assert!(
        v2_accepts(&desc, &lift_witness_to_v2(&trace), &pis),
        "the honest '[[]]' parse must prove + verify through the emitted descriptor"
    );
}

/// A **wrapped depth** (`p − 1` masquerading as `−1`) is REJECTED by the emitted path — the
/// same tamper `tamper_wrapped_depth_rejects` isolates on the v1 mirror, here refused by the
/// deployed prove/verify pipeline.
#[test]
fn emitted_dyck_wrapped_depth_rejects() {
    let desc = emitted_desc();
    let (trace, pis) = build_brackets_witness();
    let mut tampered = lift_witness_to_v2(&trace);
    tampered[3][col::STACK_DEPTH] = -BabyBear::ONE;
    tampered[3][col::DEPTH_NEXT] = -BabyBear::new(2);
    assert!(
        !v2_accepts(&desc, &tampered, &pis),
        "a wrapped STACK_DEPTH must REJECT through the emitted descriptor"
    );
}

/// An **occupancy hole below the pointer** (nested row 3 claims depth 4 with cell 1 EMPTY) is
/// REJECTED by the emitted path — the depth↔occupancy tooth rode through the emit.
#[test]
fn emitted_dyck_occupancy_hole_rejects() {
    let desc = emitted_desc();
    let (trace, pis) = build_nested_witness();
    let mut tampered = lift_witness_to_v2(&trace);
    tampered[NROW_AFTER_NESTED_PUSH][col::STACK1] = BabyBear::new(SYM_EMPTY);
    assert!(
        !v2_accepts(&desc, &tampered, &pis),
        "a hole below the pointer must REJECT through the emitted descriptor"
    );
}

/// A **dropped remainder** (the slice-1 unsoundness: the outer `cl` evaporates under the
/// nested push) is REJECTED by the emitted path — the remainder-shift window rode through.
#[test]
fn emitted_dyck_dropped_remainder_rejects() {
    let desc = emitted_desc();
    let (trace, pis) = build_nested_witness();
    let mut tampered = lift_witness_to_v2(&trace);
    tampered[NROW_AFTER_NESTED_PUSH][col::STACK3] = BabyBear::new(SYM_EMPTY);
    assert!(
        !v2_accepts(&desc, &tampered, &pis),
        "a dropped remainder must REJECT through the emitted descriptor"
    );
}

/// A **term row consuming the nonterminal `S`** is REJECTED by the emitted path — the
/// terminal-top tooth (what makes the parsed word decodable) rode through.
#[test]
fn emitted_dyck_term_consumes_nonterminal_rejects() {
    let desc = emitted_desc();
    let (trace, pis) = build_brackets_witness();
    let mut tampered = lift_witness_to_v2(&trace);
    tampered[ROW_TERM_OPEN][col::STACK0] = BabyBear::new(SYM_S);
    assert!(
        !v2_accepts(&desc, &tampered, &pis),
        "a term row consuming the nonterminal S must REJECT through the emitted descriptor"
    );
}

/// A **forged table-commitment seed** — claiming this parse under a DIFFERENT grammar's rule
/// table — is REJECTED: the first-row `ACC` PiBinding pins the seed the running hash folded
/// from, so a route cannot be re-homed onto another table.
#[test]
fn emitted_dyck_forged_table_commitment_rejects() {
    let desc = emitted_desc();
    let (trace, mut pis) = build_brackets_witness();
    let v2 = lift_witness_to_v2(&trace);
    pis[pi::TABLE_COMMITMENT] += BabyBear::ONE;
    assert!(
        !v2_accepts(&desc, &v2, &pis),
        "a forged table_commitment must REJECT through the emitted descriptor"
    );
}
