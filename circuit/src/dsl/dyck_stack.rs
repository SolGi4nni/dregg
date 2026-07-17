//! `dregg-dyck-parse-v1`: the *parse-as-derivation* circuit
//! (`docs/DESIGN-parse-as-derivation.md`, the zk-succinct path).
//!
//! This is the depth-bounded pushdown-stack extension of the deployed inter-row
//! chain pattern. It is authored **line-for-line on the template**
//! `crate::dsl::dfa_routing` (`dfa_routing_descriptor`): a threaded state column via
//! `ConstraintExpr::Transition`, a `ChainedHash2to1` running commitment PI-seeded
//! with `SeedHash2to1`, and a rule-membership check. The generalization the design
//! names is: **thread `D` stack cells instead of one `CURRENT_STATE`, and let the
//! "transition table" be the grammar's rule table.**
//!
//! # What it proves
//!
//! A trace satisfying this descriptor IS an accepting **leftmost pushdown replay**
//! (`Dregg2.Crypto.CfgCompact.Replay`) of the one-bracket **Dyck** grammar
//! `S → [ S ] | ε` (`CfgCompact.lean` `Reference`: `dyck`, rules `rBracket`/`rEmpty`)
//! on its input word, with the parse's per-step commitments folded into a public
//! `route_commitment`.
//!
//! # Slice 2: the variable-length RHS push with a remainder shift
//!
//! Slice 1 wrote `rBracket`'s push as `next.STACK[0..3] = (op, S, cl)` and **ignored
//! the stack below the popped `S`**. That was sound only while the remainder was
//! empty — true for `"[]"`, false the moment a bracket nests under un-consumed stack.
//! This slice implements the general form (`docs/DESIGN-parse-as-derivation.md` §2,
//! hard-part #3): a production with RHS length `L` pops one cell and writes
//!
//! ```text
//!   next.STACK[j] = rhs[j]                  for j < L          (the pushed RHS)
//!   next.STACK[j] = local.STACK[j - (L-1)]  for L ≤ j < D      (the REMAINDER SHIFT)
//!   local.STACK[i] == 0                     for i ≥ D - (L-1)  (the OVERFLOW GUARD)
//! ```
//!
//! The remainder shift is what makes a nested word verify: `"[[]]"`'s second
//! `rBracket` fires with `cl` still sitting under the popped `S`, and that `cl` must
//! reappear beneath the pushed RHS or the closing bracket has nothing to match.
//!
//! The overflow guard is the honest statement of the depth bound: a push whose
//! remainder does not fit in the `D`-wide buffer **REJECTS**. It never silently drops
//! a symbol — dropping is exactly the slice-1 unsoundness, and the guard converts it
//! into a refusal.
//!
//! # Stack sizing (honest)
//!
//! Stack cells hold **symbol ids**; `0` is the reserved EMPTY cell. The `rBracket`
//! spike pushes three symbols for one popped `S`, so bracket-nesting `k` bounds the
//! stack at depth `2k + 1`. `D = 5` therefore covers `k ≤ 2` — enough for both
//! bundled witnesses: `"[]"` (peak 3) and `"[[]]"` (peak 4). A word needing more
//! nesting than `D` allows is not mis-proved; it fails the overflow guard.
//!
//! # Symbol / rule encoding
//!
//! `S = 1` (the sole nonterminal), `op = '[' = 2`, `cl = ']' = 3`.
//! Rule ids: `0 = none` (term/done rows), `rBracket = 1` (`S → [ S ]`),
//! `rEmpty = 2` (`S → ε`).
//!
//! # What is still out of slice
//!
//! The Lean inductive refinement (`parse_sat_imp_replay` — a satisfying trace
//! *implies* a `CfgCompact.Replay`) is slice 3. So is the depth↔occupancy invariant
//! (nothing yet ties `STACK_DEPTH` to which cells are nonzero); the boundaries and
//! the per-action depth deltas pin the endpoints, not every intermediate cell.

use crate::field::BabyBear;
use crate::poseidon2::{hash_2_to_1, hash_4_to_1};

use crate::dsl::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};

// ============================================================================
// Symbol / rule alphabet
// ============================================================================

/// Reserved EMPTY stack-cell marker (a cell holding no symbol).
pub const SYM_EMPTY: u32 = 0;
/// The sole nonterminal `S` (`CfgCompact.Reference.NTs.S`).
pub const SYM_S: u32 = 1;
/// Terminal `op` = `'['` (`CfgCompact.Reference.Brk.op`).
pub const SYM_OP: u32 = 2;
/// Terminal `cl` = `']'` (`CfgCompact.Reference.Brk.cl`).
pub const SYM_CL: u32 = 3;

/// No rule fires on this row (term / done rows).
pub const RULE_NONE: u32 = 0;
/// `rBracket : S → [ S ]` (`CfgCompact.Reference.rBracket`).
pub const RULE_BRACKET: u32 = 1;
/// `rEmpty : S → ε` (`CfgCompact.Reference.rEmpty`).
pub const RULE_EMPTY: u32 = 2;

/// Bounded stack depth carried in columns (top at `STACK0`). Bracket-nesting `k`
/// needs `2k + 1`; `D = 5` covers `k ≤ 2` (`"[]"`, `"[[]]"`). Words that would exceed
/// it fail the overflow guard rather than being mis-proved.
pub const STACK_D: usize = 5;

/// The RHS symbol lengths of the grammar's productions, for reference:
/// `rBracket` pushes 3 (`op S cl`), `rEmpty` pushes 0.
pub const RHS_LEN_BRACKET: usize = 3;

// ============================================================================
// Column / public-input indices
// ============================================================================

/// Column indices for the Dyck-parse trace.
pub mod col {
    use super::STACK_D;

    /// `STACK[i]` — cell `i` of the bounded stack (`STACK[0]` is the top, the symbol
    /// a `rule`/`term` step reads). Valid for `i < STACK_D`.
    pub const fn stack(i: usize) -> usize {
        assert!(i < STACK_D, "stack cell index out of the D-wide buffer");
        i
    }

    /// `STACK[0]` — the stack top.
    pub const STACK0: usize = 0;
    /// `STACK[1]` — the first remainder cell (the top of what sits under a popped top).
    pub const STACK1: usize = 1;
    /// `STACK[2]`.
    pub const STACK2: usize = 2;
    /// `STACK[3]` — the first cell a `rBracket` remainder shift WRITES.
    pub const STACK3: usize = 3;
    /// `STACK[4]` — the deepest cell the `D = 5` buffer carries.
    pub const STACK4: usize = 4;

    /// Current stack depth (pointer), pinned `0` at `done`, `1` at the first row.
    pub const STACK_DEPTH: usize = STACK_D;
    /// The stack depth AFTER this row's action (witness helper; threaded into
    /// `next.STACK_DEPTH` by a `Transition`). Constrained per action selector.
    pub const DEPTH_NEXT: usize = STACK_D + 1;
    /// `STEP_KIND = rule` selector (binary).
    pub const IS_RULE: usize = STACK_D + 2;
    /// `STEP_KIND = term` selector (binary).
    pub const IS_TERM: usize = STACK_D + 3;
    /// `STEP_KIND = done` selector (binary).
    pub const IS_DONE: usize = STACK_D + 4;
    /// The production id this row fires (`RULE_*`); `RULE_NONE` on term/done rows.
    pub const RULE_ID: usize = STACK_D + 5;
    /// The input token read on a `term` step (the tape symbol at `INPUT_POS`).
    pub const INPUT_TOKEN: usize = STACK_D + 6;
    /// Input-tape pointer.
    pub const INPUT_POS: usize = STACK_D + 7;
    /// `INPUT_POS + 1` (witness helper; threaded into `next.INPUT_POS` on a `term`).
    pub const INPUT_POS_P1: usize = STACK_D + 8;
    /// Rule selector: `1` iff this row fires `rBracket` (binary, `⊆ IS_RULE`).
    pub const SEL_BRACKET: usize = STACK_D + 9;
    /// Rule selector: `1` iff this row fires `rEmpty` (binary, `⊆ IS_RULE`).
    pub const SEL_EMPTY: usize = STACK_D + 10;
    /// Per-step commitment `hash_4_to_1(RULE_ID, STACK0, INPUT_TOKEN, 0)`.
    pub const ENTRY_HASH: usize = STACK_D + 11;
    /// Rolling parse commitment up to and including this row.
    pub const RUNNING_HASH: usize = STACK_D + 12;
    /// First-row selector (gates the running-hash seed).
    pub const IS_FIRST: usize = STACK_D + 13;
    /// Fixed lane `= op` (a `Transition` source for pushing the constant `op`).
    pub const LANE_OP: usize = STACK_D + 14;
    /// Fixed lane `= cl`.
    pub const LANE_CL: usize = STACK_D + 15;
    /// Fixed lane `= S`.
    pub const LANE_S: usize = STACK_D + 16;
    /// Fixed lane `= 0` (the EMPTY push source + the 4th entry-hash lane).
    pub const LANE_ZERO: usize = STACK_D + 17;
}

/// Public-input indices.
pub mod pi {
    /// The grammar's initial nonterminal (`S`) — pins the first row's stack top.
    pub const INITIAL_SYMBOL: usize = 0;
    /// The input word length (the `done` step pins `INPUT_POS == INPUT_LEN`).
    pub const INPUT_LEN: usize = 1;
    /// The rule-table commitment (the running-hash seed; ties the parse to `dyck`).
    pub const TABLE_COMMITMENT: usize = 2;
    /// The parse `route_commitment` (last row's `RUNNING_HASH`).
    pub const ROUTE_COMMITMENT: usize = 3;
}

/// Trace width.
pub const DYCK_WIDTH: usize = STACK_D + 18;

/// Number of public inputs.
pub const DYCK_PI_COUNT: usize = 4;

// ============================================================================
// Small constraint builders (local — read `local` only)
// ============================================================================

/// `col - constant == 0` as a `Polynomial` (reads `local[col]`).
fn eq_const(c: usize, k: u32) -> ConstraintExpr {
    ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![c],
            },
            PolyTerm {
                coeff: -BabyBear::new(k),
                col_indices: vec![],
            },
        ],
    }
}

/// `a - b - k == 0` as a `Polynomial` (reads `local[a]`, `local[b]`).
fn diff_is(a: usize, b: usize, k: i64) -> ConstraintExpr {
    let kf = if k >= 0 {
        -BabyBear::new(k as u32)
    } else {
        BabyBear::new((-k) as u32)
    };
    ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![a],
            },
            PolyTerm {
                coeff: -BabyBear::ONE,
                col_indices: vec![b],
            },
            PolyTerm {
                coeff: kf,
                col_indices: vec![],
            },
        ],
    }
}

/// `sel * (rule_id - r) == 0` (a rule selector is pinned to its rule id).
fn sel_pins_rule(sel: usize, r: u32) -> ConstraintExpr {
    ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![sel, col::RULE_ID],
            },
            PolyTerm {
                coeff: -BabyBear::new(r),
                col_indices: vec![sel],
            },
        ],
    }
}

fn gated(selector_col: usize, inner: ConstraintExpr) -> ConstraintExpr {
    ConstraintExpr::Gated {
        selector_col,
        inner: Box::new(inner),
    }
}

/// A gated push/shift: `next[next_col] == local[local_col]` fires under `sel`.
fn gated_thread(sel: usize, next_col: usize, local_col: usize) -> ConstraintExpr {
    gated(
        sel,
        ConstraintExpr::Transition {
            next_col,
            local_col,
        },
    )
}

// ============================================================================
// The stack-discipline constraint groups
// ============================================================================

/// The general **variable-length RHS push with remainder shift**, gated on `sel`.
///
/// A production `A → γ` fires by popping `local.STACK[0]` (the matched `A`) and
/// writing `γ` over the top, with everything that sat under `A` shifted by
/// `|γ| − 1` cells. `rhs_lanes` names the fixed lane columns holding `γ`'s symbols
/// (they are pinned to constants by [`lane_fixes`]), so the push reads the RHS from
/// the trace via plain `Transition`s — the same primitive `dfa_routing` threads its
/// single `CURRENT_STATE` with.
///
/// Emits three groups:
///
/// 1. **push** — `next.STACK[j] == rhs_lanes[j]` for `j < |γ|`;
/// 2. **remainder shift** — `next.STACK[j] == local.STACK[j − (|γ| − 1)]` for
///    `|γ| ≤ j < D`. This is the tooth slice 1 lacked: the stack under the popped
///    cell survives, reappearing beneath the pushed RHS.
/// 3. **overflow guard** — `local.STACK[i] == 0` for every `i` whose shifted
///    destination `i + (|γ| − 1)` falls outside the `D`-wide buffer. Without this the
///    shift would silently DROP those symbols, which is precisely the slice-1 hole in
///    a wider disguise. With it, a push that does not fit REJECTS.
///
/// Requires `|γ| ≥ 1` (a shrinking RHS is [`pop_shift`]'s job) and `|γ| ≤ D`.
fn push_with_remainder_shift(sel: usize, rhs_lanes: &[usize]) -> Vec<ConstraintExpr> {
    let l = rhs_lanes.len();
    assert!((1..=STACK_D).contains(&l), "RHS must fit the D-wide buffer");
    let shift = l - 1; // pop 1, push l  ⇒  the remainder moves up by l - 1
    let mut out = Vec::new();

    // 1. the pushed RHS occupies cells 0..l.
    for (j, &lane) in rhs_lanes.iter().enumerate() {
        out.push(gated_thread(sel, col::stack(j), lane));
    }
    // 2. the remainder (everything that was under the popped top) shifts up by `shift`.
    for j in l..STACK_D {
        out.push(gated_thread(sel, col::stack(j), col::stack(j - shift)));
    }
    // 3. cells whose shifted destination leaves the buffer must be EMPTY.
    for i in (STACK_D - shift)..STACK_D {
        out.push(gated(sel, eq_const(col::stack(i), SYM_EMPTY)));
    }
    out
}

/// The **pop / shift-down**, gated on `sel`: `next.STACK[j] == local.STACK[j + 1]`,
/// with the vacated deepest cell forced EMPTY. Used by `rEmpty` (`S → ε`: pop 1,
/// push 0) and by a `term` step (consume the matched terminal). This is
/// [`push_with_remainder_shift`] at `|γ| = 0` — written out because there is no lane
/// to read the (absent) RHS from and the shift runs the other direction.
fn pop_shift(sel: usize) -> Vec<ConstraintExpr> {
    let mut out = Vec::new();
    for j in 0..STACK_D - 1 {
        out.push(gated_thread(sel, col::stack(j), col::stack(j + 1)));
    }
    out.push(gated_thread(sel, col::stack(STACK_D - 1), col::LANE_ZERO));
    out
}

/// The **hold**, gated on `sel`: every stack cell threads unchanged. `done` rows (and
/// the `done` self-loop padding) take no action, so the stack must not move.
fn hold_stack(sel: usize) -> Vec<ConstraintExpr> {
    (0..STACK_D)
        .map(|j| gated_thread(sel, col::stack(j), col::stack(j)))
        .collect()
}

/// The fixed constant lanes (`Transition` sources for pushing constants).
fn lane_fixes() -> Vec<ConstraintExpr> {
    vec![
        eq_const(col::LANE_OP, SYM_OP),
        eq_const(col::LANE_CL, SYM_CL),
        eq_const(col::LANE_S, SYM_S),
        eq_const(col::LANE_ZERO, SYM_EMPTY),
    ]
}

// ============================================================================
// Descriptor
// ============================================================================

/// Build the `dregg-dyck-parse-v1` descriptor for the one-bracket Dyck grammar.
///
/// The constraints (all deployed `ConstraintExpr` variants; the `dfa_routing`
/// template is cited per group):
///
/// - **selectors** — `IS_RULE`/`IS_TERM`/`IS_DONE` binary and partition (exactly one);
///   the rule sub-selectors `SEL_BRACKET`/`SEL_EMPTY` binary, partition `IS_RULE`, and
///   are pinned to their rule ids.
/// - **rule membership** (`r ∈ g.rules`) — on a `rule` row, `RULE_ID ∈ {1, 2}` via a
///   gated vanishing polynomial `(RULE_ID − 1)(RULE_ID − 2) == 0`. This is the
///   spike's rule-table check, the analogue of `dfa_routing`'s `TableFunction`
///   transition-table lookup (`dfa_routing.rs:164`) at 2 rules.
/// - **top match** — `rule`: `STACK0 == S`; `term`: `STACK0 == INPUT_TOKEN` (both
///   `Gated` equalities, the shape of the design §2 `rule`/`term` teeth).
/// - **stack threading** (the heart) — the multi-cell generalization of
///   `dfa_routing`'s single `Transition{CURRENT_STATE ← NEXT_STATE}`
///   (`dfa_routing.rs:173`): `rBracket` fires [`push_with_remainder_shift`] with
///   `γ = op S cl`; `rEmpty` and `term` fire [`pop_shift`]; `done` fires
///   [`hold_stack`]. Depth threads through `DEPTH_NEXT`.
/// - **input tape** — `term` advances `INPUT_POS` by one; every non-`term` step
///   holds it (`Transition`s on the pointer).
/// - **running commitment** — `ENTRY_HASH == hash_4_to_1(RULE_ID, STACK0,
///   INPUT_TOKEN, 0)` (C1 shape), folded by `ChainedHash2to1` (`dfa_routing.rs:178`)
///   and seeded on row 0 by `SeedHash2to1` against `pi[TABLE_COMMITMENT]`
///   (`dfa_routing.rs:185`).
pub fn dyck_parse_descriptor(name: &str) -> CircuitDescriptor {
    let column = |name: &str, index: usize, kind: ColumnKind| ColumnDef {
        name: name.to_string(),
        index,
        kind,
    };

    let mut constraints = vec![
        // ---- selector booleans -------------------------------------------
        ConstraintExpr::Binary { col: col::IS_RULE },
        ConstraintExpr::Binary { col: col::IS_TERM },
        ConstraintExpr::Binary { col: col::IS_DONE },
        ConstraintExpr::Binary { col: col::IS_FIRST },
        ConstraintExpr::Binary {
            col: col::SEL_BRACKET,
        },
        ConstraintExpr::Binary {
            col: col::SEL_EMPTY,
        },
        // exactly one action kind: IS_RULE + IS_TERM + IS_DONE == 1.
        ConstraintExpr::Polynomial {
            terms: vec![
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![col::IS_RULE],
                },
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![col::IS_TERM],
                },
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![col::IS_DONE],
                },
                PolyTerm {
                    coeff: -BabyBear::ONE,
                    col_indices: vec![],
                },
            ],
        },
        // the rule sub-selectors partition IS_RULE: SEL_BRACKET + SEL_EMPTY == IS_RULE.
        ConstraintExpr::Polynomial {
            terms: vec![
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![col::SEL_BRACKET],
                },
                PolyTerm {
                    coeff: BabyBear::ONE,
                    col_indices: vec![col::SEL_EMPTY],
                },
                PolyTerm {
                    coeff: -BabyBear::ONE,
                    col_indices: vec![col::IS_RULE],
                },
            ],
        },
        // rule sub-selectors pinned to their ids.
        sel_pins_rule(col::SEL_BRACKET, RULE_BRACKET),
        sel_pins_rule(col::SEL_EMPTY, RULE_EMPTY),
        // ---- rule membership: on a rule row, RULE_ID ∈ {rBracket, rEmpty} --
        // (RULE_ID - 1)(RULE_ID - 2) = RULE_ID^2 - 3 RULE_ID + 2 == 0, gated on IS_RULE.
        gated(
            col::IS_RULE,
            ConstraintExpr::Polynomial {
                terms: vec![
                    PolyTerm {
                        coeff: BabyBear::ONE,
                        col_indices: vec![col::RULE_ID, col::RULE_ID],
                    },
                    PolyTerm {
                        coeff: -BabyBear::new(3),
                        col_indices: vec![col::RULE_ID],
                    },
                    PolyTerm {
                        coeff: BabyBear::new(2),
                        col_indices: vec![],
                    },
                ],
            },
        ),
        // ---- top match ----------------------------------------------------
        // rule step: the popped stack top is the nonterminal S.
        gated(col::IS_RULE, eq_const(col::STACK0, SYM_S)),
        // term step: the stack top is the terminal equal to the input token.
        gated(
            col::IS_TERM,
            ConstraintExpr::Equality {
                col_a: col::STACK0,
                col_b: col::INPUT_TOKEN,
            },
        ),
        // done step: stack empty (top == 0) and depth == 0.
        gated(col::IS_DONE, eq_const(col::STACK0, SYM_EMPTY)),
        gated(col::IS_DONE, eq_const(col::STACK_DEPTH, 0)),
        // ---- input-pointer helper -----------------------------------------
        diff_is(col::INPUT_POS_P1, col::INPUT_POS, 1), // INPUT_POS_P1 == INPUT_POS + 1
        // ---- depth-delta helper (per action) ------------------------------
        // rBracket: depth += 2 (pop 1, push 3).
        gated(
            col::SEL_BRACKET,
            diff_is(
                col::DEPTH_NEXT,
                col::STACK_DEPTH,
                RHS_LEN_BRACKET as i64 - 1,
            ),
        ),
        // rEmpty: depth -= 1 (pop 1, push 0).
        gated(
            col::SEL_EMPTY,
            diff_is(col::DEPTH_NEXT, col::STACK_DEPTH, -1),
        ),
        // term: depth -= 1 (pop 1).
        gated(col::IS_TERM, diff_is(col::DEPTH_NEXT, col::STACK_DEPTH, -1)),
        // done: depth unchanged.
        gated(col::IS_DONE, diff_is(col::DEPTH_NEXT, col::STACK_DEPTH, 0)),
        // ---- per-step commitment ------------------------------------------
        // ENTRY_HASH == hash_4_to_1(RULE_ID, STACK0, INPUT_TOKEN, 0).
        ConstraintExpr::Hash4to1 {
            output_col: col::ENTRY_HASH,
            input_cols: [col::RULE_ID, col::STACK0, col::INPUT_TOKEN, col::LANE_ZERO],
        },
        // seed row 0: RUNNING_HASH == hash_2_to_1(pi[TABLE_COMMITMENT], ENTRY_HASH).
        gated(
            col::IS_FIRST,
            ConstraintExpr::SeedHash2to1 {
                output_col: col::RUNNING_HASH,
                seed_pi_index: pi::TABLE_COMMITMENT,
                input_col: col::ENTRY_HASH,
            },
        ),
        // ================= cross-row (transition) constraints ==============
        // running-hash accumulation: next.running == hash(this.running, next.entry).
        ConstraintExpr::ChainedHash2to1 {
            output_next_col: col::RUNNING_HASH,
            seed_local_col: col::RUNNING_HASH,
            input_next_col: col::ENTRY_HASH,
        },
        // depth threading: next.STACK_DEPTH == this.DEPTH_NEXT.
        ConstraintExpr::Transition {
            next_col: col::STACK_DEPTH,
            local_col: col::DEPTH_NEXT,
        },
        // input-pointer threading: term advances by 1, every other step holds.
        gated_thread(col::IS_TERM, col::INPUT_POS, col::INPUT_POS_P1),
        ConstraintExpr::InvertedGated {
            selector_col: col::IS_TERM,
            inner: Box::new(ConstraintExpr::Transition {
                next_col: col::INPUT_POS,
                local_col: col::INPUT_POS,
            }),
        },
    ];

    // ---- lane fixes (constant push sources) -------------------------------
    constraints.extend(lane_fixes());

    // ---- stack threading ---------------------------------------------------
    // rBracket: the general push `S → op S cl` with the remainder shift + overflow guard.
    constraints.extend(push_with_remainder_shift(
        col::SEL_BRACKET,
        &[col::LANE_OP, col::LANE_S, col::LANE_CL],
    ));
    // rEmpty (`S → ε`) and term: pop the top, shift the rest down.
    constraints.extend(pop_shift(col::SEL_EMPTY));
    constraints.extend(pop_shift(col::IS_TERM));
    // done: the machine has stopped; the stack holds.
    constraints.extend(hold_stack(col::IS_DONE));

    // Degree: the gated rule-membership polynomial is degree 3 (selector · quadratic);
    // everything else is ≤ 2. Keep headroom to match the derivation descriptor envelope.
    let max_degree = 4usize;

    let boundaries = vec![
        // first row starts at [initial]: STACK0 == pi[INITIAL_SYMBOL], depth 1.
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::STACK0,
            pi_index: pi::INITIAL_SYMBOL,
        },
        BoundaryDef::Fixed {
            row: BoundaryRow::First,
            col: col::STACK_DEPTH,
            value: BabyBear::ONE,
        },
        BoundaryDef::Fixed {
            row: BoundaryRow::First,
            col: col::INPUT_POS,
            value: BabyBear::ZERO,
        },
        BoundaryDef::Fixed {
            row: BoundaryRow::First,
            col: col::IS_FIRST,
            value: BabyBear::ONE,
        },
        // last row is an accepting `done`: depth 0, input fully consumed,
        // route_commitment bound.
        BoundaryDef::Fixed {
            row: BoundaryRow::Last,
            col: col::IS_DONE,
            value: BabyBear::ONE,
        },
        BoundaryDef::Fixed {
            row: BoundaryRow::Last,
            col: col::STACK_DEPTH,
            value: BabyBear::ZERO,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: col::INPUT_POS,
            pi_index: pi::INPUT_LEN,
        },
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: col::RUNNING_HASH,
            pi_index: pi::ROUTE_COMMITMENT,
        },
    ];

    let mut columns = Vec::with_capacity(DYCK_WIDTH);
    for i in 0..STACK_D {
        columns.push(column(
            &format!("stack{i}"),
            col::stack(i),
            ColumnKind::Value,
        ));
    }
    columns.extend([
        column("stack_depth", col::STACK_DEPTH, ColumnKind::Value),
        column("depth_next", col::DEPTH_NEXT, ColumnKind::Value),
        column("is_rule", col::IS_RULE, ColumnKind::Selector),
        column("is_term", col::IS_TERM, ColumnKind::Selector),
        column("is_done", col::IS_DONE, ColumnKind::Selector),
        column("rule_id", col::RULE_ID, ColumnKind::Value),
        column("input_token", col::INPUT_TOKEN, ColumnKind::Value),
        column("input_pos", col::INPUT_POS, ColumnKind::Value),
        column("input_pos_p1", col::INPUT_POS_P1, ColumnKind::Value),
        column("sel_bracket", col::SEL_BRACKET, ColumnKind::Selector),
        column("sel_empty", col::SEL_EMPTY, ColumnKind::Selector),
        column("entry_hash", col::ENTRY_HASH, ColumnKind::Hash),
        column("running_hash", col::RUNNING_HASH, ColumnKind::Hash),
        column("is_first", col::IS_FIRST, ColumnKind::Selector),
        column("lane_op", col::LANE_OP, ColumnKind::Value),
        column("lane_cl", col::LANE_CL, ColumnKind::Value),
        column("lane_s", col::LANE_S, ColumnKind::Value),
        column("lane_zero", col::LANE_ZERO, ColumnKind::Value),
    ]);

    CircuitDescriptor {
        name: name.to_string(),
        trace_width: DYCK_WIDTH,
        max_degree,
        columns,
        constraints,
        boundaries,
        public_input_count: DYCK_PI_COUNT,
        lookup_tables: vec![],
    }
}

/// Create a `DslCircuit` from the Dyck-parse descriptor.
pub fn dyck_parse_circuit(name: &str) -> DslCircuit {
    DslCircuit::new(dyck_parse_descriptor(name))
}

/// The rule-table commitment: `hash_2_to_1(enc(rBracket), enc(rEmpty))`, where each
/// rule is encoded `hash_4_to_1(rule_id, lhs, rhs0, rhs1)`. This is the `pi[2]`
/// running-hash seed — it ties the parse to *this* grammar (analogue of
/// `dfa_routing::compute_table_commitment`).
pub fn dyck_rule_table_commitment() -> BabyBear {
    // rBracket: S → [ S ] ; encode (id, lhs=S, rhs head = op, rhs next = S).
    let e_bracket = hash_4_to_1(&[
        BabyBear::new(RULE_BRACKET),
        BabyBear::new(SYM_S),
        BabyBear::new(SYM_OP),
        BabyBear::new(SYM_S),
    ]);
    // rEmpty: S → ε ; encode (id, lhs=S, empty, empty).
    let e_empty = hash_4_to_1(&[
        BabyBear::new(RULE_EMPTY),
        BabyBear::new(SYM_S),
        BabyBear::new(SYM_EMPTY),
        BabyBear::new(SYM_EMPTY),
    ]);
    hash_2_to_1(e_bracket, e_empty)
}

// ============================================================================
// Trace generation — honest accepting runs
// ============================================================================

/// One machine action, before power-of-two padding.
#[derive(Clone, Copy)]
pub enum Action {
    Rule(u32), // fire production `rule_id`
    Term(u32), // match terminal `token` on top against the input tape
    Done,
}

/// Build the accepting-parse trace + public inputs for the word `"[]"` (`[op, cl]`),
/// the exact word `CfgCompact.Reference.brackets_replays` accepts.
///
/// The rows are the faithful pushdown replay:
///   `rule rBracket · term '[' · rule rEmpty · term ']' · done`,
/// padded to a power of two with `done` self-loops. Returns the row-major trace
/// (width [`DYCK_WIDTH`]) and the public inputs
/// `[initial_symbol, input_len, table_commitment, route_commitment]`.
pub fn build_brackets_witness() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let input: Vec<u32> = vec![SYM_OP, SYM_CL];
    let actions = vec![
        Action::Rule(RULE_BRACKET),
        Action::Term(SYM_OP),
        Action::Rule(RULE_EMPTY),
        Action::Term(SYM_CL),
        Action::Done,
    ];
    build_witness(&input, &actions)
}

/// Build the accepting-parse trace + public inputs for the **nested** word `"[[]]"`
/// (`[op, op, cl, cl]`) — the slice-2 witness.
///
/// `S ⟹ [S] ⟹ [[S]] ⟹ [[]]`, replayed as
/// `rule rBracket · term '[' · rule rBracket · term '[' · rule rEmpty · term ']' ·
/// term ']' · done` — exactly 8 rows, no padding.
///
/// This is the word slice 1 could not verify: the SECOND `rBracket` (row 2) fires
/// with the stack at `[S, cl]`, so the outer `cl` sits under the popped `S` and must
/// survive the push. The remainder shift carries it to `STACK3`, whence the two
/// `term ']'` rows consume it. Without the shift the run has nothing to close with.
pub fn build_nested_witness() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let input: Vec<u32> = vec![SYM_OP, SYM_OP, SYM_CL, SYM_CL];
    let actions = vec![
        Action::Rule(RULE_BRACKET),
        Action::Term(SYM_OP),
        Action::Rule(RULE_BRACKET),
        Action::Term(SYM_OP),
        Action::Rule(RULE_EMPTY),
        Action::Term(SYM_CL),
        Action::Term(SYM_CL),
        Action::Done,
    ];
    build_witness(&input, &actions)
}

/// General trace builder: fold `actions` over the pushdown machine, laying out one
/// row per action and padding to a power of two with `done`. Used by
/// [`build_brackets_witness`], [`build_nested_witness`], and by the tamper test's
/// honest baseline.
///
/// This is the prover-side companion of the descriptor: it fills every witness
/// helper column (`DEPTH_NEXT`, `INPUT_POS_P1`, `SEL_*`, the lanes, the running
/// hash) so the honest run satisfies the descriptor. The live stack is a `Vec`, so
/// the push here is the *unbounded* pushdown step; the descriptor's overflow guard is
/// what refuses a run whose stack outgrows the `D`-wide buffer, and
/// [`build_witness`] panics rather than emit such a truncated row.
pub fn build_witness(input: &[u32], actions: &[Action]) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let table_commitment = dyck_rule_table_commitment();

    // Live machine state.
    let mut stack: Vec<u32> = vec![SYM_S]; // starts at [initial]
    let mut input_pos: u32 = 0;

    let n_pad = actions.len().next_power_of_two().max(2);
    let mut rows: Vec<Vec<BabyBear>> = Vec::with_capacity(n_pad);
    let mut running = table_commitment;

    let emit = |stack: &[u32],
                depth_next: u32,
                input_pos: u32,
                kind: (bool, bool, bool),
                rule_id: u32,
                input_token: u32,
                sel_bracket: u32,
                sel_empty: u32,
                is_first: u32,
                running: &mut BabyBear,
                first: bool|
     -> Vec<BabyBear> {
        assert!(
            stack.len() <= STACK_D,
            "the live stack ({}) outgrew the D = {STACK_D} buffer — widen STACK_D; \
             the descriptor's overflow guard would REJECT a truncated row",
            stack.len()
        );
        let top = stack.first().copied().unwrap_or(SYM_EMPTY);
        let depth = stack.len() as u32;
        let entry = hash_4_to_1(&[
            BabyBear::new(rule_id),
            BabyBear::new(top),
            BabyBear::new(input_token),
            BabyBear::ZERO,
        ]);
        if first {
            *running = hash_2_to_1(table_commitment_of(), entry);
        } else {
            *running = hash_2_to_1(*running, entry);
        }
        let mut row = vec![BabyBear::ZERO; DYCK_WIDTH];
        for i in 0..STACK_D {
            row[col::stack(i)] = BabyBear::new(stack.get(i).copied().unwrap_or(SYM_EMPTY));
        }
        row[col::STACK_DEPTH] = BabyBear::new(depth);
        row[col::DEPTH_NEXT] = BabyBear::new(depth_next);
        row[col::IS_RULE] = BabyBear::new(kind.0 as u32);
        row[col::IS_TERM] = BabyBear::new(kind.1 as u32);
        row[col::IS_DONE] = BabyBear::new(kind.2 as u32);
        row[col::RULE_ID] = BabyBear::new(rule_id);
        row[col::INPUT_TOKEN] = BabyBear::new(input_token);
        row[col::INPUT_POS] = BabyBear::new(input_pos);
        row[col::INPUT_POS_P1] = BabyBear::new(input_pos + 1);
        row[col::SEL_BRACKET] = BabyBear::new(sel_bracket);
        row[col::SEL_EMPTY] = BabyBear::new(sel_empty);
        row[col::ENTRY_HASH] = entry;
        row[col::RUNNING_HASH] = *running;
        row[col::IS_FIRST] = BabyBear::new(is_first);
        row[col::LANE_OP] = BabyBear::new(SYM_OP);
        row[col::LANE_CL] = BabyBear::new(SYM_CL);
        row[col::LANE_S] = BabyBear::new(SYM_S);
        row[col::LANE_ZERO] = BabyBear::ZERO;
        row
    };

    for (i, action) in actions.iter().enumerate() {
        let is_first = if i == 0 { 1 } else { 0 };
        let first = i == 0;
        match *action {
            Action::Rule(rule_id) => {
                // depth after: pop 1, push |rhs| — and the REMAINDER (everything under
                // the popped top) rides along, which is the slice-2 correction.
                let (sel_bracket, sel_empty, new_stack) = match rule_id {
                    RULE_BRACKET => {
                        // pop S, push [op, S, cl] OVER the surviving remainder.
                        let mut s = vec![SYM_OP, SYM_S, SYM_CL];
                        s.extend_from_slice(&stack[1..]);
                        (1u32, 0u32, s)
                    }
                    RULE_EMPTY => {
                        // pop S, push nothing → shift down.
                        (0u32, 1u32, stack[1..].to_vec())
                    }
                    _ => (0, 0, stack.clone()),
                };
                let depth_next = new_stack.len() as u32;
                rows.push(emit(
                    &stack,
                    depth_next,
                    input_pos,
                    (true, false, false),
                    rule_id,
                    /*token*/ 0,
                    sel_bracket,
                    sel_empty,
                    is_first,
                    &mut running,
                    first,
                ));
                stack = new_stack;
            }
            Action::Term(token) => {
                let depth_next = (stack.len() as u32).saturating_sub(1);
                rows.push(emit(
                    &stack,
                    depth_next,
                    input_pos,
                    (false, true, false),
                    RULE_NONE,
                    token,
                    0,
                    0,
                    is_first,
                    &mut running,
                    first,
                ));
                // pop the matched terminal, advance the tape.
                stack.remove(0);
                input_pos += 1;
            }
            Action::Done => {
                let depth_next = stack.len() as u32; // 0, unchanged
                rows.push(emit(
                    &stack,
                    depth_next,
                    input_pos,
                    (false, false, true),
                    RULE_NONE,
                    0,
                    0,
                    0,
                    is_first,
                    &mut running,
                    first,
                ));
            }
        }
    }

    // Pad to a power of two with `done` self-loops (stack empty, tape at end).
    while rows.len() < n_pad {
        rows.push(emit(
            &stack,
            0,
            input_pos,
            (false, false, true),
            RULE_NONE,
            0,
            0,
            0,
            0,
            &mut running,
            false,
        ));
    }

    let route_commitment = rows.last().unwrap()[col::RUNNING_HASH];
    let public_inputs = vec![
        BabyBear::new(SYM_S), // initial nonterminal
        BabyBear::new(input.len() as u32),
        dyck_rule_table_commitment(),
        route_commitment,
    ];
    (rows, public_inputs)
}

/// The rule-table commitment as a plain function (used inside the row emitter's
/// seed step). Kept separate so the closure captures nothing borrow-conflicting.
fn table_commitment_of() -> BabyBear {
    dyck_rule_table_commitment()
}

// ============================================================================
// Satisfaction predicate — the Rust `Satisfied2` driver
// ============================================================================

/// Does `expr` read the `next` row (a cross-row / transition constraint)? Such
/// constraints are enforced only on the transition domain (rows `0..n-1`), matching
/// the STARK transition vanishing polynomial that excludes the last row.
fn references_next(expr: &ConstraintExpr) -> bool {
    match expr {
        ConstraintExpr::Transition { .. } | ConstraintExpr::ChainedHash2to1 { .. } => true,
        ConstraintExpr::Gated { inner, .. }
        | ConstraintExpr::InvertedGated { inner, .. }
        | ConstraintExpr::Squared { inner } => references_next(inner),
        _ => false,
    }
}

/// **The descriptor-satisfaction predicate** — the Rust analogue of Lean `Satisfied2`:
/// every constraint evaluates to zero across the trace domain, and every boundary
/// holds. This DRIVES the deployed evaluator
/// [`ConstraintExpr::evaluate_with_tables`] (it does not re-implement the constraint
/// semantics), so a `true`/`false` here is the same accept/reject the audited
/// prover's per-row check computes.
///
/// - transition constraints (`references_next`) are checked on rows `0..n-1` with
///   `next = trace[i+1]`;
/// - per-row constraints are checked on every row (`next` unused);
/// - boundaries resolve `First`/`Last`/`Index` and check the pinned cell against
///   the public input (`PiBinding`) or the literal (`Fixed`).
pub fn dyck_satisfied(desc: &CircuitDescriptor, trace: &[Vec<BabyBear>], pi: &[BabyBear]) -> bool {
    let n = trace.len();
    if n == 0 {
        return false;
    }
    for c in &desc.constraints {
        if references_next(c) {
            for i in 0..n - 1 {
                if c.evaluate(&trace[i], &trace[i + 1], pi) != BabyBear::ZERO {
                    return false;
                }
            }
        } else {
            for i in 0..n {
                let next = &trace[(i + 1).min(n - 1)];
                if c.evaluate(&trace[i], next, pi) != BabyBear::ZERO {
                    return false;
                }
            }
        }
    }
    for b in &desc.boundaries {
        let (row, value) = match b {
            BoundaryDef::PiBinding { row, col, pi_index } => {
                let r = resolve_row(row, n);
                (trace[r][*col], pi[*pi_index])
            }
            BoundaryDef::Fixed { row, col, value } => {
                let r = resolve_row(row, n);
                (trace[r][*col], *value)
            }
        };
        if row != value {
            return false;
        }
    }
    true
}

fn resolve_row(row: &BoundaryRow, n: usize) -> usize {
    match row {
        BoundaryRow::First => 0,
        BoundaryRow::Last => n - 1,
        BoundaryRow::Index(i) => *i,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const NAME: &str = "dregg-dyck-parse-v1";

    #[test]
    fn descriptor_is_deployable() {
        let desc = dyck_parse_descriptor(NAME);
        desc.validate().expect("dyck descriptor must validate");
    }

    #[test]
    fn brackets_accepts() {
        let desc = dyck_parse_descriptor(NAME);
        let (trace, pi) = build_brackets_witness();
        assert!(
            dyck_satisfied(&desc, &trace, &pi),
            "the honest '[]' parse must satisfy the descriptor"
        );
    }

    #[test]
    fn nested_brackets_accepts() {
        let desc = dyck_parse_descriptor(NAME);
        let (trace, pi) = build_nested_witness();
        assert!(
            dyck_satisfied(&desc, &trace, &pi),
            "the honest '[[]]' parse must satisfy the descriptor (the remainder shift)"
        );
    }

    /// The nested run's stack really does carry a remainder under a pushed RHS: at the
    /// SECOND `rBracket` (row 2) the stack is `[S, cl]`, and the row after it is
    /// `[op, S, cl, cl]` — the trailing `cl` is the shifted remainder at `STACK3`.
    #[test]
    fn nested_run_exercises_the_remainder() {
        let (trace, _pi) = build_nested_witness();
        assert_eq!(trace[2][col::STACK0], BabyBear::new(SYM_S));
        assert_eq!(
            trace[2][col::STACK1],
            BabyBear::new(SYM_CL),
            "the remainder"
        );
        assert_eq!(trace[3][col::STACK0], BabyBear::new(SYM_OP));
        assert_eq!(trace[3][col::STACK1], BabyBear::new(SYM_S));
        assert_eq!(trace[3][col::STACK2], BabyBear::new(SYM_CL));
        assert_eq!(
            trace[3][col::STACK3],
            BabyBear::new(SYM_CL),
            "the remainder must survive the push, shifted by |rhs| - 1 = 2"
        );
        assert_eq!(trace[3][col::STACK_DEPTH], BabyBear::new(4));
    }
}
