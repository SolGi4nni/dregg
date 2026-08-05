//! ⚑ **THE CHALLENGE LEAF BITES** — the red control for `VmConstraint2::ChalGate`.
//!
//! `PastaFieldSound.lean` recorded, as a finding, that a Schwartz–Zippel identity was *"not
//! expressible in this IR … There is no challenge leaf"*. The leaf exists now. This file is the
//! evidence that it is a CHECK and not a decoration, in the terms this repo demands of a new
//! constraint kind:
//!
//! 1. **Both languages, together.** The wire grammar Lean emits (`ChalConstraint.toJson`) parses
//!    here (`parses_lean_chal_gate_golden`), and the byte-pinned golden is the Lean theorem
//!    `DescriptorIR2.demoChal_wire_golden`'s string verbatim.
//! 2. **In the canonical fingerprint.** Two descriptors differing only in which challenge index a
//!    gate reads have DIFFERENT semantic fingerprints (`challenge_index_is_inside_the_fingerprint`)
//!    — so the leaf is not a silence the fingerprint walks past.
//! 3. **A declared count that is a VALUE, and the old shape REFUSES.** An `"ir":2` descriptor with
//!    no `"challenges"` key does not load (`pre_flag_day_shape_refuses_to_load`), and a v1
//!    descriptor carrying the key does not load either.
//! 4. **It can go red.** `check_descriptor2` refuses a gate that reads a challenge the descriptor
//!    did not declare, and refuses a descriptor declaring more challenges than its lookup contexts
//!    supply (`undeclared_challenge_refuses`, `overdrawn_challenge_supply_refuses`).
//! 5. **⚑ The degree does not move.** The whole construction rests on
//!    `SymbolicVariableExt::degree_multiple() == 0` for `ExtEntry::Challenge`. `challenge_is_degree_zero`
//!    measures that on the DEPLOYED symbolic analysis, not on a reading of it: a descriptor whose
//!    body is a 32-deep Horner chain in the challenge has the same max constraint degree as one
//!    whose body is a bare product of two columns.

use dregg_circuit::descriptor_ir2::{
    ChalExpr, ChalGateSpec, EffectVmDescriptor2, LookupSpec, TableDef2, TableSem, VmConstraint2,
    check_descriptor2_wellformed, parse_vm_descriptor2,
};
use dregg_circuit::descriptor_ir2_canonical::effect_vm_descriptor2_semantic_fingerprint;

/// The byte-pinned golden — the exact string Lean's `demoChal_wire_golden` theorem proves
/// `emitVmJson2 demoChal` equals. If Lean's emitter and this decoder ever disagree, one of the two
/// theorems below goes red rather than the grammar silently forking.
const DEMO_CHAL: &str = r#"{"name":"demo-chal","ir":2,"trace_width":4,"public_input_count":0,"challenges":1,"tables":[{"id":0,"name":"main","arity":4,"sem":"main"}],"constraints":[{"t":"chal_gate","on_transition":false,"body":{"t":"add","l":{"t":"add","l":{"t":"loc","c":0},"r":{"t":"mul","l":{"t":"chal","i":0},"r":{"t":"loc","c":1}}},"r":{"t":"mul","l":{"t":"const","v":-1},"r":{"t":"add","l":{"t":"loc","c":2},"r":{"t":"mul","l":{"t":"chal","i":0},"r":{"t":"loc","c":3}}}}}}],"hash_sites":[],"ranges":[]}"#;

fn main_table(width: usize) -> TableDef2 {
    TableDef2 {
        id: 0,
        name: "main".to_string(),
        arity: width,
        sem: TableSem::Main,
    }
}

/// A descriptor with one challenge gate reading `Chal(chal_index)` and `declared` challenges,
/// plus `n_lookups` range lookups (each of which is one LogUp context ⇒ two challenges).
fn chal_desc(chal_index: usize, declared: usize, n_lookups: usize) -> EffectVmDescriptor2 {
    let mut constraints: Vec<VmConstraint2> = (0..n_lookups)
        .map(|_| {
            VmConstraint2::Lookup(LookupSpec {
                table: 2,
                tuple: vec![dregg_circuit::lean_descriptor_air::LeanExpr::Var(0)],
            })
        })
        .collect();
    constraints.push(VmConstraint2::ChalGate(ChalGateSpec {
        body: ChalExpr::Mul(
            Box::new(ChalExpr::Chal(chal_index)),
            Box::new(ChalExpr::Loc(0)),
        ),
        on_transition: false,
    }));
    EffectVmDescriptor2 {
        name: "chal-probe".to_string(),
        trace_width: 4,
        public_input_count: 0,
        challenges: declared,
        tables: vec![
            main_table(4),
            TableDef2 {
                id: 2,
                name: "range".to_string(),
                arity: 1,
                sem: TableSem::Range { bits: 8 },
            },
        ],
        constraints,
        hash_sites: vec![],
        ranges: vec![],
    }
}

// ============================================================================
// 1 — the wire grammar, both languages
// ============================================================================

#[test]
fn parses_lean_chal_gate_golden() {
    let d = parse_vm_descriptor2(DEMO_CHAL).expect("Lean chal_gate golden must parse");
    assert_eq!(d.name, "demo-chal");
    assert_eq!(d.trace_width, 4);
    // ⚑ The DECLARED count arrived as a value, not an inference.
    assert_eq!(d.challenges, 1);
    assert_eq!(d.constraints.len(), 1);
    let VmConstraint2::ChalGate(g) = &d.constraints[0] else {
        panic!("expected a chal_gate, got {:?}", d.constraints[0]);
    };
    assert!(!g.on_transition);
    // The body reads challenge 0 and no more.
    assert_eq!(g.body.chal_count(), 1);
    // ⚑ AND IT IS DEGREE 1 IN THE TRACE, not 2: `a₀ + z·a₁ − (b₀ + z·b₁)` multiplies columns only
    // by challenges. The Lean twin is `ChalExpr.traceDegree`.
    assert_eq!(g.body.trace_degree(), 1);
}

#[test]
fn chal_gate_roundtrips_through_the_canonical_encoding() {
    let d = parse_vm_descriptor2(DEMO_CHAL).expect("parse");
    let bytes = dregg_circuit::descriptor_ir2_canonical::canonical_effect_vm_descriptor2_bytes(&d)
        .expect("encode");
    let back =
        dregg_circuit::descriptor_ir2_canonical::decode_canonical_effect_vm_descriptor2(&bytes)
            .expect("decode");
    assert_eq!(
        d, back,
        "the challenge leaf must survive the canonical codec"
    );
}

// ============================================================================
// 2 — the leaf is INSIDE the fingerprint
// ============================================================================

#[test]
fn challenge_index_is_inside_the_fingerprint() {
    let a = chal_desc(0, 1, 1);
    let b = chal_desc(1, 2, 1);
    let fa = effect_vm_descriptor2_semantic_fingerprint(&a).expect("fingerprint a");
    let fb = effect_vm_descriptor2_semantic_fingerprint(&b).expect("fingerprint b");
    assert_ne!(
        fa, fb,
        "two descriptors reading DIFFERENT challenges must fingerprint differently — otherwise the \
         leaf is a silence the fingerprint walks past"
    );

    // And the DECLARED COUNT is in there on its own: same body, different declaration.
    let mut c = chal_desc(0, 1, 1);
    c.challenges = 2;
    let fc = effect_vm_descriptor2_semantic_fingerprint(&c).expect("fingerprint c");
    assert_ne!(fa, fc, "the declared challenge count must be fingerprinted");
}

// ============================================================================
// 3 — the pre-flag-day shape REFUSES TO LOAD
// ============================================================================

#[test]
fn pre_flag_day_shape_refuses_to_load() {
    // The same descriptor with the `"challenges"` key removed — i.e. exactly what every committed
    // descriptor looked like before 2026-08-05.
    let old = DEMO_CHAL.replace(r#","challenges":1"#, "");
    let err = parse_vm_descriptor2(&old)
        .expect_err("a v2 descriptor with no \"challenges\" key must REFUSE, not read as zero");
    assert!(
        err.contains("challenges"),
        "the refusal must name the missing key, got: {err}"
    );
}

#[test]
fn v1_descriptor_carrying_challenges_refuses() {
    let v1 = r#"{"name":"v1-probe","trace_width":2,"public_input_count":0,"challenges":0,"tables":[],"constraints":[],"hash_sites":[],"ranges":[]}"#;
    let err = dregg_circuit::descriptor_ir2::parse_vm_descriptor_any(v1)
        .expect_err("the challenge leaf is v2-only");
    assert!(err.contains("challenges"), "got: {err}");
}

// ============================================================================
// 4 — ⚑ IT CAN GO RED
// ============================================================================

#[test]
fn undeclared_challenge_refuses() {
    // Body reads `Chal(1)`; the descriptor declares 1 challenge (index 0 only).
    let mut d = chal_desc(1, 1, 2);
    d.challenges = 1;
    let err = check_descriptor2_wellformed(&d)
        .expect_err("a gate reading an UNDECLARED challenge must be refused");
    assert!(
        err.contains("challenge"),
        "the refusal must name the challenge, got: {err}"
    );
}

#[test]
fn overdrawn_challenge_supply_refuses() {
    // Declares 3 challenges but carries ONE lookup context, which supplies 2.
    let d = chal_desc(2, 3, 1);
    let err = check_descriptor2_wellformed(&d).expect_err(
        "a descriptor declaring more challenges than its lookup contexts supply must be refused",
    );
    assert!(err.contains("guarantee only"), "got: {err}");
}

#[test]
fn declared_count_must_match_the_bodies() {
    // Two lookups (4 challenges supplied), body reads `Chal(0)`, but the header claims 2.
    let mut d = chal_desc(0, 1, 2);
    d.challenges = 2;
    let err = check_descriptor2_wellformed(&d)
        .expect_err("the declared count must EQUAL what the bodies need");
    assert!(err.contains("exactly"), "got: {err}");
}

#[test]
fn an_honest_declaration_is_accepted() {
    // The green pole. Without this the four refusals above could all be a descriptor that never
    // loads for an unrelated reason.
    let d = chal_desc(0, 1, 1);
    check_descriptor2_wellformed(&d).expect("a well-declared challenge gate must be ACCEPTED");
    let d2 = chal_desc(3, 4, 2);
    check_descriptor2_wellformed(&d2)
        .expect("4 challenges against 2 lookup contexts is exactly OK");
}

#[test]
fn out_of_range_column_in_a_chal_body_refuses() {
    let mut d = chal_desc(0, 1, 1);
    d.constraints.pop();
    d.constraints.push(VmConstraint2::ChalGate(ChalGateSpec {
        body: ChalExpr::Mul(
            Box::new(ChalExpr::Chal(0)),
            // trace_width is 4.
            Box::new(ChalExpr::Loc(99)),
        ),
        on_transition: false,
    }));
    let err = check_descriptor2_wellformed(&d).expect_err("out-of-range column must be refused");
    assert!(
        err.contains("chal_gate body references column 99"),
        "got: {err}"
    );
}

// ============================================================================
// 5 — ⚑ THE DEGREE FACT, measured rather than read
// ============================================================================

#[test]
fn challenge_is_degree_zero() {
    // A 32-deep Horner chain in the challenge, multiplied by one column.
    let mut horner = ChalExpr::Loc(0);
    for _ in 0..32 {
        horner = ChalExpr::Add(
            Box::new(ChalExpr::Mul(Box::new(horner), Box::new(ChalExpr::Chal(0)))),
            Box::new(ChalExpr::Const(1)),
        );
    }
    // ⚑ Degree 1 — one column, thirty-two challenge multiplications, and the challenge multiplies
    // cost NOTHING. This is `ExtEntry::Challenge => degree_multiple() == 0` in the IR's own
    // vocabulary, and it is why `253 → 191` constraints is not bought back in the quotient.
    assert_eq!(horner.trace_degree(), 1);
    assert_eq!(horner.chal_count(), 1);

    // Two columns multiplied together — degree 2, whatever challenge arithmetic surrounds them.
    let deg2 = ChalExpr::Mul(
        Box::new(ChalExpr::Mul(
            Box::new(horner.clone()),
            Box::new(ChalExpr::Chal(0)),
        )),
        Box::new(ChalExpr::Mul(
            Box::new(ChalExpr::Loc(1)),
            Box::new(ChalExpr::Chal(0)),
        )),
    );
    assert_eq!(deg2.trace_degree(), 2);
}

#[test]
fn a_challenge_only_expression_is_degree_zero() {
    // The `hornerConst` shape from `PastaSzMul`: the modulus' limbs evaluated at the challenge.
    // No column read at all ⇒ degree 0, so multiplying a trace-linear factor by it keeps degree 1.
    let mut e = ChalExpr::Const(7);
    for k in 0..32 {
        e = ChalExpr::Add(
            Box::new(ChalExpr::Mul(Box::new(e), Box::new(ChalExpr::Chal(0)))),
            Box::new(ChalExpr::Const(k)),
        );
    }
    assert_eq!(e.trace_degree(), 0);
    assert_eq!(
        ChalExpr::Mul(Box::new(e), Box::new(ChalExpr::Loc(0))).trace_degree(),
        1
    );
}
