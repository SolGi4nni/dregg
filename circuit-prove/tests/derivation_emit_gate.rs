//! # The emit-from-Lean EQUALITY GATE — the Datalog DERIVATION AIR.
//!
//! The descriptor is AUTHORED in Lean (`metatheory/Dregg2/Circuit/Emit/DerivationEmit.lean`,
//! `derivationDesc`) and its wire string is byte-pinned there (`emitVmJson2` `#guard`). This test
//! embeds that EXACT string ([`GOLDEN_JSON`]), and:
//!
//!   1. DECODES it via [`parse_vm_descriptor2`] and asserts the decode equals an independently
//!      hand-built `EffectVmDescriptor2` — a constraint-for-constraint transcription of the hand
//!      AIR `circuit/src/dsl/derivation.rs::derivation_circuit_descriptor` (C1..C28 + the two
//!      boundary PI pins), over the SAME 371-col `derivation_air::col` layout extended by the 8 C2
//!      inverse columns and the 7 C4 chip lanes. A byte drift on either side breaks this OR the
//!      Lean `#guard`.
//!   2. proves an HONEST derivation witness — a real firing rule with an ACTIVE `gte` comparator
//!      (`50 >= 10`), its trace produced by the REAL `dsl::derivation::generate_derivation_trace_dsl`
//!      (the deployed trace generator, NOT a reconstruction) — through [`prove_vm_descriptor2`],
//!      asserts ACCEPT, and re-verifies the proof;
//!   3. the MUTATION CANARIES — each tampers ONE genuinely load-bearing tooth and asserts the
//!      prove-or-verify REFUSES (real UNSAT), non-vacuous against step 2:
//!        * the C4 hash tooth (a forged `derived_hash` trace column names an unserved chip row);
//!        * the C6 conclusion pin (a forged `pi[1]`);
//!        * the C5/boundary state pin (a forged `pi[0]` state_root);
//!        * the C3 body tooth (all membership flags zeroed — a derivation with no body facts);
//!        * the C17/C19 RANGE tooth (a forced-set high bit on the in-range GTE diff).
//!
//! The honest witness ACCEPTS and every tamper REJECTS: the emitted descriptor accepts EXACTLY the
//! honest derivation statement the hand AIR did.

use std::panic::AssertUnwindSafe;

use dregg_circuit::derivation_air::{
    BodyAtomPattern, CircuitGteCheck, CircuitRule, DerivationWitness, GTE_DIFF_BITS,
    MAX_BODY_ATOMS, MAX_EQUAL_CHECKS, MAX_HEAD_TERMS, MAX_MEMBEROF_CHECKS, MAX_SUB_VARS, col,
};
use dregg_circuit::derivation_witness::{DERIVATION_PI_COUNT, derivation_descriptor_witness};
use dregg_circuit::descriptor_ir2::{
    CHIP_OUT_LANES, CHIP_RATE, EffectVmDescriptor2, LookupSpec, MemBoundaryWitness, TID_P2,
    VmConstraint2, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::dsl::derivation::{BODY_HASH_INV_START, EXTENDED_TRACE_WIDTH};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};
use dregg_circuit::poseidon2::hash_fact;
use dregg_circuit::refusal::{Outcome, classify};

/// The BYTE-IDENTICAL wire string Lean's `emitVmJson2 derivationDesc` emits (pinned by the `#guard`
/// in `DerivationEmit.lean`). If Lean's emitter drifts, that `#guard` fails; if this literal drifts,
/// the `decoded == hand_built` assertion fails.
const GOLDEN_JSON: &str = include_str!("../../circuit/descriptors/by-name/derivation.json");

/// Base of the 7 exposed chip lanes of the single C4 hash site (past the 379 extended columns).
const C4_LANE_BASE: usize = EXTENDED_TRACE_WIDTH; // 379
/// Full main-trace width: 379 + (CHIP_OUT_LANES - 1) = 386.
const DERIV_TRACE_WIDTH: usize = EXTENDED_TRACE_WIDTH + (CHIP_OUT_LANES - 1);

// ---------------------------------------------------------------------------------------------
// Expression + gate helpers — mirrored EXACTLY from `DerivationEmit.lean` §2.
// ---------------------------------------------------------------------------------------------

/// `x - y` (no subtraction node: `x + (-1)*y`).
fn sub(x: LeanExpr, y: LeanExpr) -> LeanExpr {
    LeanExpr::add(x, LeanExpr::mul(LeanExpr::Const(-1), y))
}

/// The binary body `c*(c - 1)`.
fn bin_body(c: usize) -> LeanExpr {
    LeanExpr::mul(
        LeanExpr::Var(c),
        LeanExpr::add(LeanExpr::Var(c), LeanExpr::Const(-1)),
    )
}

/// `∏ Var(cols)` (empty ⇒ `Const(1)`), left-associated.
fn prod_cols(cols: &[usize]) -> LeanExpr {
    match cols.split_first() {
        None => LeanExpr::Const(1),
        Some((&c0, rest)) => {
            let mut p = LeanExpr::Var(c0);
            for &d in rest {
                p = LeanExpr::mul(p, LeanExpr::Var(d));
            }
            p
        }
    }
}

/// One polynomial term `coeff * ∏ cols`.
fn term_e(coeff: i64, cols: &[usize]) -> LeanExpr {
    if cols.is_empty() {
        LeanExpr::Const(coeff)
    } else if coeff == 1 {
        prod_cols(cols)
    } else if coeff == -1 {
        LeanExpr::mul(LeanExpr::Const(-1), prod_cols(cols))
    } else {
        LeanExpr::mul(LeanExpr::Const(coeff), prod_cols(cols))
    }
}

/// A polynomial `Σ terms` (empty ⇒ `Const(0)`), left-associated.
fn poly_e(terms: Vec<LeanExpr>) -> LeanExpr {
    let mut it = terms.into_iter();
    match it.next() {
        None => LeanExpr::Const(0),
        Some(first) => it.fold(first, LeanExpr::add),
    }
}

fn gate(body: LeanExpr) -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::Gate(body))
}
fn bin_gate(c: usize) -> VmConstraint2 {
    gate(bin_body(c))
}
fn gated_gate(active: usize, body: LeanExpr) -> VmConstraint2 {
    gate(LeanExpr::mul(LeanExpr::Var(active), body))
}
fn pin(c: usize, pi: usize) -> VmConstraint2 {
    VmConstraint2::Base(VmConstraint::PiBinding {
        row: VmRow::First,
        col: c,
        pi_index: pi,
    })
}

/// The C4 `hash_fact` chip fact-site tuple (arity tag 7; the DECO `fact_site` shape):
/// `[7, HEAD_PRED, HEAD_TERM0..3, 0xFACF, 1, 0×9, DERIVED_HASH, lane1..7]`.
fn c4_lookup() -> VmConstraint2 {
    let mut tuple: Vec<LeanExpr> = Vec::with_capacity(1 + CHIP_RATE + 1 + (CHIP_OUT_LANES - 1));
    tuple.push(LeanExpr::Const(7));
    // 16 rate slots.
    let inputs = [
        col::HEAD_PRED,
        col::HEAD_TERM_START,
        col::HEAD_TERM_START + 1,
        col::HEAD_TERM_START + 2,
        col::HEAD_TERM_START + 3,
    ];
    for i in 0..CHIP_RATE {
        let e = match i {
            0..=4 => LeanExpr::Var(inputs[i]),
            5 => LeanExpr::Const(0xFACF),
            6 => LeanExpr::Const(1),
            _ => LeanExpr::Const(0),
        };
        tuple.push(e);
    }
    tuple.push(LeanExpr::Var(col::DERIVED_HASH)); // out0
    for j in 0..(CHIP_OUT_LANES - 1) {
        tuple.push(LeanExpr::Var(C4_LANE_BASE + j));
    }
    VmConstraint2::Lookup(LookupSpec {
        table: TID_P2,
        tuple,
    })
}

// ---------------------------------------------------------------------------------------------
// The independently hand-built twin of `derivationDesc` (the hand-AIR semantics shape).
// ---------------------------------------------------------------------------------------------

fn hand_built_desc() -> EffectVmDescriptor2 {
    let mut cs: Vec<VmConstraint2> = Vec::new();

    // C1: body-membership binary.
    for i in 0..MAX_BODY_ATOMS {
        cs.push(bin_gate(col::BODY_MEMBERSHIP_START + i));
    }
    // C2: flag*(hash*inv - 1).
    for i in 0..MAX_BODY_ATOMS {
        cs.push(gate(LeanExpr::mul(
            LeanExpr::Var(col::BODY_MEMBERSHIP_START + i),
            sub(
                LeanExpr::mul(
                    LeanExpr::Var(col::BODY_HASH_START + i),
                    LeanExpr::Var(BODY_HASH_INV_START + i),
                ),
                LeanExpr::Const(1),
            ),
        )));
    }
    // C3: ∏(1 - flag_i).
    {
        let mut body = LeanExpr::Const(1);
        for i in 0..MAX_BODY_ATOMS {
            body = LeanExpr::mul(
                body,
                sub(
                    LeanExpr::Const(1),
                    LeanExpr::Var(col::BODY_MEMBERSHIP_START + i),
                ),
            );
        }
        cs.push(gate(body));
    }
    // C4: the derived-hash chip site.
    cs.push(c4_lookup());
    // C5: flag_i*(root_i - root_0).
    for i in 0..MAX_BODY_ATOMS {
        cs.push(gate(LeanExpr::mul(
            LeanExpr::Var(col::BODY_MEMBERSHIP_START + i),
            sub(
                LeanExpr::Var(col::BODY_ROOT_START + i),
                LeanExpr::Var(col::BODY_ROOT_START),
            ),
        )));
    }
    // C6: DERIVED_HASH == pi[1].
    cs.push(pin(col::DERIVED_HASH, 1));
    // C6b: body atom 0's fact hash == pi[5] (the exported membership-leaf binding).
    cs.push(pin(col::BODY_HASH_START, 5));
    // C6c: body atoms 1..7's fact hashes == pi[6..12]. Added by `b53498db0` — before it, only
    // slot 0 was exported, so a prover could bind one held body fact and derive from seven it did
    // not hold.
    for i in 1..MAX_BODY_ATOMS {
        cs.push(pin(col::BODY_HASH_START + i, 5 + i));
    }
    // C7: head is_var binary.
    for i in 0..MAX_HEAD_TERMS {
        cs.push(bin_gate(col::HEAD_IS_VAR_START + i));
    }
    // C8: head selectors binary.
    for t in 0..MAX_HEAD_TERMS {
        for v in 0..MAX_SUB_VARS {
            cs.push(bin_gate(col::head_sel_var(t, v)));
        }
    }
    // C9: (Σ_v sel(t,v) - is_var_t)^2.
    for t in 0..MAX_HEAD_TERMS {
        let mut terms: Vec<LeanExpr> = (0..MAX_SUB_VARS)
            .map(|v| term_e(1, &[col::head_sel_var(t, v)]))
            .collect();
        terms.push(term_e(-1, &[col::HEAD_IS_VAR_START + t]));
        let p = poly_e(terms);
        cs.push(gate(LeanExpr::mul(p.clone(), p)));
    }
    // C10: (derived - raw + is_var*raw - Σ sel*sub)^2.
    for t in 0..MAX_HEAD_TERMS {
        let mut terms = vec![
            term_e(1, &[col::HEAD_TERM_START + t]),
            term_e(-1, &[col::HEAD_RAW_VALUE_START + t]),
            term_e(
                1,
                &[col::HEAD_IS_VAR_START + t, col::HEAD_RAW_VALUE_START + t],
            ),
        ];
        for v in 0..MAX_SUB_VARS {
            terms.push(term_e(
                -1,
                &[col::head_sel_var(t, v), col::SUB_VALUE_START + v],
            ));
        }
        let p = poly_e(terms);
        cs.push(gate(LeanExpr::mul(p.clone(), p)));
    }
    // C11: eq active binary.
    for i in 0..MAX_EQUAL_CHECKS {
        cs.push(bin_gate(col::eq_check_active(i)));
    }
    // C12: active*(a - b).
    for i in 0..MAX_EQUAL_CHECKS {
        cs.push(gated_gate(
            col::eq_check_active(i),
            sub(
                LeanExpr::Var(col::eq_check_term_a(i)),
                LeanExpr::Var(col::eq_check_term_b(i)),
            ),
        ));
    }
    // C13: memberof active binary.
    for i in 0..MAX_MEMBEROF_CHECKS {
        cs.push(bin_gate(col::memberof_check_active(i)));
    }
    // C14: active*(a - b).
    for i in 0..MAX_MEMBEROF_CHECKS {
        cs.push(gated_gate(
            col::memberof_check_active(i),
            sub(
                LeanExpr::Var(col::memberof_check_term_a(i)),
                LeanExpr::Var(col::memberof_check_term_b(i)),
            ),
        ));
    }
    // C15: gte active binary.
    cs.push(bin_gate(col::GTE_CHECK_ACTIVE));
    // C16: active*(diff - term_a + term_b).
    cs.push(gated_gate(
        col::GTE_CHECK_ACTIVE,
        poly_e(vec![
            term_e(1, &[col::GTE_CHECK_DIFF]),
            term_e(-1, &[col::GTE_CHECK_TERM_A]),
            term_e(1, &[col::GTE_CHECK_TERM_B]),
        ]),
    ));
    // C17: active*(Σ bit_i*2^i - diff).
    {
        let mut terms: Vec<LeanExpr> = (0..GTE_DIFF_BITS)
            .map(|i| term_e(1i64 << i, &[col::gte_diff_bit(i)]))
            .collect();
        terms.push(term_e(-1, &[col::GTE_CHECK_DIFF]));
        cs.push(gated_gate(col::GTE_CHECK_ACTIVE, poly_e(terms)));
    }
    // C18: active*bit_i*(bit_i - 1).
    for i in 0..GTE_DIFF_BITS {
        cs.push(gated_gate(
            col::GTE_CHECK_ACTIVE,
            bin_body(col::gte_diff_bit(i)),
        ));
    }
    // C19: active*bit_29.
    cs.push(gated_gate(
        col::GTE_CHECK_ACTIVE,
        poly_e(vec![term_e(1, &[col::gte_diff_bit(GTE_DIFF_BITS - 1)])]),
    ));
    // C20: lt active binary.
    cs.push(bin_gate(col::LT_CHECK_ACTIVE));
    // C21: active*(diff - term_b + term_a + 1).
    cs.push(gated_gate(
        col::LT_CHECK_ACTIVE,
        poly_e(vec![
            term_e(1, &[col::LT_CHECK_DIFF]),
            term_e(-1, &[col::LT_CHECK_TERM_B]),
            term_e(1, &[col::LT_CHECK_TERM_A]),
            term_e(1, &[]),
        ]),
    ));
    // C22: active*(Σ lt_bit_i*2^i - lt_diff).
    {
        let mut terms: Vec<LeanExpr> = (0..GTE_DIFF_BITS)
            .map(|i| term_e(1i64 << i, &[col::lt_diff_bit(i)]))
            .collect();
        terms.push(term_e(-1, &[col::LT_CHECK_DIFF]));
        cs.push(gated_gate(col::LT_CHECK_ACTIVE, poly_e(terms)));
    }
    // C23: active*lt_bit_i*(lt_bit_i - 1).
    for i in 0..GTE_DIFF_BITS {
        cs.push(gated_gate(
            col::LT_CHECK_ACTIVE,
            bin_body(col::lt_diff_bit(i)),
        ));
    }
    // C24: active*lt_bit_29.
    cs.push(gated_gate(
        col::LT_CHECK_ACTIVE,
        poly_e(vec![term_e(1, &[col::lt_diff_bit(GTE_DIFF_BITS - 1)])]),
    ));
    // C25: check-term is_var binary.
    for slot in 0..col::NUM_CHECK_TERMS {
        cs.push(bin_gate(col::check_term_is_var(slot)));
    }
    // C26: check-term selectors binary.
    for slot in 0..col::NUM_CHECK_TERMS {
        for v in 0..MAX_SUB_VARS {
            cs.push(bin_gate(col::check_term_sel(slot, v)));
        }
    }
    // C27: (Σ_v check_term_sel(slot,v) - check_term_is_var(slot))^2.
    for slot in 0..col::NUM_CHECK_TERMS {
        let mut terms: Vec<LeanExpr> = (0..MAX_SUB_VARS)
            .map(|v| term_e(1, &[col::check_term_sel(slot, v)]))
            .collect();
        terms.push(term_e(-1, &[col::check_term_is_var(slot)]));
        let p = poly_e(terms);
        cs.push(gate(LeanExpr::mul(p.clone(), p)));
    }
    // C28: the 20 check-term bindings.
    let c28_binding = |active: usize, trace_col: usize, slot: usize| -> VmConstraint2 {
        let mut terms = vec![
            term_e(1, &[trace_col]),
            term_e(-1, &[col::check_term_raw_value(slot)]),
            term_e(
                1,
                &[
                    col::check_term_is_var(slot),
                    col::check_term_raw_value(slot),
                ],
            ),
        ];
        for v in 0..MAX_SUB_VARS {
            terms.push(term_e(
                -1,
                &[col::check_term_sel(slot, v), col::SUB_VALUE_START + v],
            ));
        }
        gated_gate(active, poly_e(terms))
    };
    for i in 0..MAX_EQUAL_CHECKS {
        cs.push(c28_binding(
            col::eq_check_active(i),
            col::eq_check_term_a(i),
            col::eq_check_term_a_slot(i),
        ));
        cs.push(c28_binding(
            col::eq_check_active(i),
            col::eq_check_term_b(i),
            col::eq_check_term_b_slot(i),
        ));
    }
    for i in 0..MAX_MEMBEROF_CHECKS {
        cs.push(c28_binding(
            col::memberof_check_active(i),
            col::memberof_check_term_a(i),
            col::memberof_check_term_a_slot(i),
        ));
        cs.push(c28_binding(
            col::memberof_check_active(i),
            col::memberof_check_term_b(i),
            col::memberof_check_term_b_slot(i),
        ));
    }
    cs.push(c28_binding(
        col::GTE_CHECK_ACTIVE,
        col::GTE_CHECK_TERM_A,
        col::GTE_TERM_A_SLOT,
    ));
    cs.push(c28_binding(
        col::GTE_CHECK_ACTIVE,
        col::GTE_CHECK_TERM_B,
        col::GTE_TERM_B_SLOT,
    ));
    cs.push(c28_binding(
        col::LT_CHECK_ACTIVE,
        col::LT_CHECK_TERM_A,
        col::LT_TERM_A_SLOT,
    ));
    cs.push(c28_binding(
        col::LT_CHECK_ACTIVE,
        col::LT_CHECK_TERM_B,
        col::LT_TERM_B_SLOT,
    ));

    // Boundaries.
    cs.push(pin(col::DERIVED_HASH, 1));
    cs.push(pin(col::BODY_ROOT_START, 0));
    cs.push(pin(col::BODY_HASH_START, 5));
    for i in 1..MAX_BODY_ATOMS {
        cs.push(pin(col::BODY_HASH_START + i, 5 + i));
    }

    EffectVmDescriptor2 {
        name: "dregg-derivation-v1".to_string(),
        trace_width: DERIV_TRACE_WIDTH,
        public_input_count: DERIVATION_PI_COUNT,
        tables: vec![],
        constraints: cs,
        hash_sites: vec![],
        ranges: vec![],
    }
}

// ---------------------------------------------------------------------------------------------
// Honest witness (a real firing rule with an ACTIVE gte comparator 50 >= 10) — the same fixture
// `dsl::derivation`'s `dsl_trace_with_gte_check` proves satisfies every constraint. Trace by the
// REAL `generate_derivation_trace_dsl`.
// ---------------------------------------------------------------------------------------------

fn honest_witness() -> DerivationWitness {
    let access_pred = BabyBear::new(300);
    let owns_pred = BabyBear::new(100);
    let budget = BabyBear::new(50);
    let cost = BabyBear::new(10);
    let rule = CircuitRule {
        id: 6,
        num_body_atoms: 1,
        num_variables: 2,
        head_predicate: access_pred,
        head_terms: [
            (true, BabyBear::new(0)),
            (true, BabyBear::new(1)),
            (false, BabyBear::ZERO),
            (false, BabyBear::ZERO),
        ],
        body_atoms: vec![BodyAtomPattern {
            predicate: owns_pred,
            terms: [
                (true, BabyBear::new(0)),
                (true, BabyBear::new(1)),
                (false, BabyBear::ZERO),
            ],
        }],
        equal_checks: vec![],
        memberof_checks: vec![],
        gte_check: Some(CircuitGteCheck {
            lhs_is_var: true,
            lhs_value: BabyBear::new(0), // budget
            rhs_is_var: true,
            rhs_value: BabyBear::new(1), // cost
        }),
        lt_check: None,
    };
    let body_fact = hash_fact(owns_pred, &[budget, cost, BabyBear::ZERO]);
    DerivationWitness {
        rule,
        state_root: BabyBear::new(99999),
        body_fact_hashes: vec![body_fact],
        substitution: vec![budget, cost],
        derived_predicate: access_pred,
        derived_terms: [budget, cost, BabyBear::ZERO, BabyBear::ZERO],
        not_after_height: BabyBear::ZERO,
        org_id_hash: BabyBear::ZERO,
        budget_remaining: BabyBear::ZERO,
    }
}

/// The honest base trace (379-col rows from the real generator; the prover extends to 386 and fills
/// the 7 C4 lanes) + its 13 public inputs: `[state_root, derived_hash, not_after, org_id, budget]`
/// followed by the EIGHT exported body-fact hashes the C6b/C6c pins bind. Built by the production
/// `derivation_descriptor_witness`, which wraps the deployed `generate_derivation_trace_dsl`.
fn honest_trace() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    derivation_descriptor_witness(&honest_witness())
}

/// `true` iff `(trace, pis)` is REJECTED end-to-end (prove refuses OR the proof fails to verify).
/// Prove-THEN-verify is the faithful gate: `prove_vm_descriptor2` self-verifies only under
/// `debug_assertions`, so in `--release` the consumer's `verify_vm_descriptor2` is the real check.
fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    match classify("rejects", || {
        let proof = prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, pis)
    }) {
        // The p3 debug prover's DOCUMENTED unsat verdict — a real refusal.
        // `classify` REDs on any other panic (a stray unwrap, a trace-assembly
        // debug_assert), which used to land here and read as "rejected".
        Outcome::UnsatPanic(_) => true,
        Outcome::Err(_) => true,
        Outcome::Accepted(_) => false,
    }
}

/// STEP 1 — the emitted descriptor decodes and equals the hand-built twin.
#[test]
fn derivation_emit_decodes_to_hand_built() {
    let decoded = parse_vm_descriptor2(GOLDEN_JSON).expect("the Lean-emitted golden JSON decodes");
    let hand = hand_built_desc();
    assert_eq!(
        decoded, hand,
        "the Lean-emitted descriptor must equal the independently hand-built descriptor"
    );
    assert_eq!(decoded.name, "dregg-derivation-v1");
    assert_eq!(decoded.trace_width, DERIV_TRACE_WIDTH);
    assert_eq!(decoded.public_input_count, DERIVATION_PI_COUNT);
    assert_eq!(decoded.constraints.len(), 393);
    let chip_lookups = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_P2))
        .count();
    assert_eq!(chip_lookups, 1, "the single C4 derived-hash chip site");
    let pins = decoded
        .constraints
        .iter()
        .filter(|c| matches!(c, VmConstraint2::Base(VmConstraint::PiBinding { .. })))
        .count();
    assert_eq!(
        pins, 19,
        "C6 + C6b + the seven C6c body-fact pins, and the same set again as boundary pins"
    );
}

/// STEP 2 — THE POSITIVE POLE: the honest firing derivation proves through the emitted descriptor
/// and re-verifies against its public inputs.
#[test]
fn honest_derivation_proves_and_verifies() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis) = honest_trace();
    assert_eq!(
        trace[0].len(),
        EXTENDED_TRACE_WIDTH,
        "real generator emits the 379-col row"
    );
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .expect("the honest derivation witness must prove through the emitted descriptor");
    verify_vm_descriptor2(&desc, &proof, &pis)
        .expect("the honest proof must re-verify against the public inputs");
}

/// STEP 3a — MUTATION CANARY (C4 hash tooth): a FORGED `derived_hash` trace column (with `pi[1]`
/// moved to match, isolating the chip binding) names a hash no genuine chip row serves ⇒ UNSAT.
#[test]
fn forged_derived_hash_column_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis) = honest_trace();
    assert!(
        !rejects(&desc, &trace, &pis),
        "honest must be accepted — else the canary is vacuous"
    );
    let mut bad = trace.clone();
    let forged = bad[0][col::DERIVED_HASH] + BabyBear::ONE;
    for row in &mut bad {
        row[col::DERIVED_HASH] = forged;
    }
    let mut bad_pis = pis.clone();
    bad_pis[1] = forged; // move the conclusion pin too, so ONLY the C4 chip binding bites
    assert!(
        rejects(&desc, &bad, &bad_pis),
        "a forged derived_hash (unserved chip row) must be REJECTED (the hash tooth)"
    );
}

/// STEP 3b — MUTATION CANARY (C6 conclusion pin): a forged `pi[1]` ⇒ the DERIVED_HASH pin is UNSAT.
#[test]
fn forged_conclusion_pi_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis) = honest_trace();
    let mut bad_pis = pis.clone();
    bad_pis[1] += BabyBear::ONE;
    assert!(
        rejects(&desc, &trace, &bad_pis),
        "a forged conclusion (pi[1] != derived_hash) must be REJECTED (the C6 pin)"
    );
}

/// STEP 3c — MUTATION CANARY (C5/boundary state pin): a forged `pi[0]` state_root ⇒ the
/// BODY_ROOT_START boundary pin is UNSAT (the body is bound to the committed state).
#[test]
fn forged_state_root_pi_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis) = honest_trace();
    let mut bad_pis = pis.clone();
    bad_pis[0] = BabyBear::new(11111);
    assert!(
        rejects(&desc, &trace, &bad_pis),
        "a forged state_root (pi[0] != body_root) must be REJECTED (the state pin)"
    );
}

/// STEP 3c' — MUTATION CANARY (C6b/boundary body-fact pin, HELD FORGERY #3): a forged `pi[5]`
/// body_fact_hash ⇒ the `BODY_HASH_START` pin is UNSAT. This is the tooth that closes the
/// body↔membership-leaf gap: the exported body-fact PI is bound in-circuit to the derivation's
/// actual consumed body fact (BODY_HASH_START), so a prover cannot publish a body PI matching a
/// membership leaf they hold while deriving `Allow(effect)` from a body fact they do NOT hold.
#[test]
fn forged_body_fact_hash_pi_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis) = honest_trace();
    // Non-vacuity: the honest PI[5] IS the trace's body fact hash and accepts.
    assert_eq!(pis[5], trace[0][col::BODY_HASH_START]);
    assert!(
        !rejects(&desc, &trace, &pis),
        "honest body-fact PI must be accepted — else the canary is vacuous"
    );
    let mut bad_pis = pis.clone();
    bad_pis[5] += BabyBear::ONE; // forge the exported body_fact_hash
    assert!(
        rejects(&desc, &trace, &bad_pis),
        "a forged body_fact_hash (pi[5] != BODY_HASH_START) must be REJECTED (the C6b membership-leaf pin)"
    );
}

/// STEP 3d — MUTATION CANARY (C3 body tooth): all membership flags zeroed ⇒ `∏(1 - flag) = 1 != 0`.
/// A derivation claiming NO body facts is refused.
#[test]
fn no_body_facts_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis) = honest_trace();
    let mut bad = trace.clone();
    for row in &mut bad {
        for i in 0..MAX_BODY_ATOMS {
            row[col::BODY_MEMBERSHIP_START + i] = BabyBear::ZERO;
        }
    }
    assert!(
        rejects(&desc, &bad, &pis),
        "a derivation with no body membership flags must be REJECTED (C3 at-least-one-body)"
    );
}

/// STEP 3e — MUTATION CANARY (C17/C19 RANGE tooth): force the high bit of the in-range GTE diff.
/// The recomposition (`Σ bit_i·2^i = diff`, C17) and the high-bit-zero gate (C19) both break ⇒
/// UNSAT. A diff outside `[0, 2^29)` — an unsatisfied `>=` — is refused.
#[test]
fn out_of_range_gte_high_bit_refuses() {
    let desc = parse_vm_descriptor2(GOLDEN_JSON).expect("decode");
    let (trace, pis) = honest_trace();
    // sanity: the honest in-range diff has the high bit zero (non-vacuity of the negative below).
    assert_eq!(
        trace[0][col::gte_diff_bit(GTE_DIFF_BITS - 1)],
        BabyBear::ZERO,
        "honest 50>=10 diff (=40) has a zero high bit"
    );
    let mut bad = trace.clone();
    for row in &mut bad {
        row[col::gte_diff_bit(GTE_DIFF_BITS - 1)] = BabyBear::ONE; // claim an out-of-range diff
    }
    assert!(
        rejects(&desc, &bad, &pis),
        "an out-of-range GTE diff (high bit set) must be REJECTED (the range tooth C17/C19)"
    );
}
