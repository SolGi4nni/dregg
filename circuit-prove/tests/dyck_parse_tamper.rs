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
//!     `D` bound (a push that does not fit REJECTS instead of silently dropping).

use dregg_circuit::dsl::circuit::{CircuitDescriptor, ConstraintExpr};
use dregg_circuit::dsl::dyck_stack::{
    RULE_EMPTY, SYM_CL, SYM_EMPTY, build_brackets_witness, build_nested_witness, col,
    dyck_parse_descriptor, dyck_satisfied, pi,
};
use dregg_circuit::field::BabyBear;

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
