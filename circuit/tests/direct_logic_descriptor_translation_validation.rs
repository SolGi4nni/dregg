//! Cross-language translation validation for the direct-logic descriptors.
//!
//! These tests consume the exact JSON literals guarded against Lean's
//! `emitVmJson2` output.  They independently decode and evaluate those bytes in
//! Rust, exercise the live prover for one honest and one dishonest statement,
//! and pin the bytes against silent drift.
//!
//! Scope: this is differential / translation-validation evidence.  It is not a
//! theorem that the Rust parser, evaluator, or prover refines the Lean model.

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, VmConstraint2, WindowExpr, parse_vm_descriptor2,
    prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::lean_descriptor_air::{LeanExpr, VmConstraint, VmRow};

const BABY_BEAR: i128 = 2_013_265_921;
const GABBAY_LEAN: &str =
    include_str!("../../metatheory/Dregg2/Metatheory/GabbayDescriptorIR2PublicBinding.lean");
const GABBAY_MARKER: &str = "#guard publicDescriptorBytes ==";
const GABBAY_BLAKE3: &str = "0f2c4f6cb245c0fc41d66cf35aead9e2d17df43d5827f48cab1aa092aa409e0a";
const BOOLGRAPH_LEAN: &str =
    include_str!("../../metatheory/Dregg2/Metatheory/DirectLogicBoolGraphDescriptorIR2.lean");
const BOOLGRAPH_MARKER: &str = "def factorPublicDescriptorJsonLiteral : String :=";
const BOOLGRAPH_BLAKE3: &str = "b76b68ff0e5a70ebd31d13f7d04340cd8719ed5ccd69ce9b6bb3df766661da13";

/// Read one Lean string literal following a unique marker.  The guarded wire
/// literals use only the ordinary escapes implemented here.  Rejecting every
/// other escape keeps this extractor fail-closed if Lean's source format
/// changes.
fn guarded_lean_string(source: &str, marker: &str) -> Result<String, String> {
    let mut markers = source.match_indices(marker);
    let marker_at = markers
        .next()
        .map(|(at, _)| at)
        .ok_or_else(|| format!("missing Lean byte guard marker {marker:?}"))?;
    if markers.next().is_some() {
        return Err(format!("non-unique Lean byte guard marker {marker:?}"));
    }
    let suffix = &source[marker_at + marker.len()..];
    let quote_at = suffix
        .find('"')
        .ok_or_else(|| format!("marker {marker:?} has no string literal"))?;
    let mut chars = suffix[quote_at + 1..].chars();
    let mut out = String::new();
    while let Some(ch) = chars.next() {
        match ch {
            '"' => return Ok(out),
            '\\' => match chars.next() {
                Some('"') => out.push('"'),
                Some('\\') => out.push('\\'),
                Some('n') => out.push('\n'),
                Some('r') => out.push('\r'),
                Some('t') => out.push('\t'),
                Some(other) => return Err(format!("unsupported Lean escape \\{other}")),
                None => return Err("unterminated Lean escape".to_string()),
            },
            other => out.push(other),
        }
    }
    Err("unterminated Lean string literal".to_string())
}

/// Fail-closed loader for one reviewed descriptor specimen.  Parsing alone is
/// intentionally insufficient: a syntactically valid constraint edit must not
/// silently become the object this translation-validation test assesses.
fn load_pinned(json: &str, expected_blake3: &str) -> Result<EffectVmDescriptor2, String> {
    let actual = blake3::hash(json.as_bytes()).to_hex().to_string();
    if actual != expected_blake3 {
        return Err(format!(
            "descriptor byte pin mismatch: expected {expected_blake3}, got {actual}"
        ));
    }
    parse_vm_descriptor2(json)
}

fn eval_lean(expression: &LeanExpr, row: &[i128]) -> i128 {
    match expression {
        LeanExpr::Var(column) => row[*column],
        LeanExpr::Const(value) => i128::from(*value),
        LeanExpr::Add(left, right) => {
            (eval_lean(left, row) + eval_lean(right, row)).rem_euclid(BABY_BEAR)
        }
        LeanExpr::Mul(left, right) => {
            (eval_lean(left, row) * eval_lean(right, row)).rem_euclid(BABY_BEAR)
        }
    }
}

fn eval_window(expression: &WindowExpr, row: &[i128], next: &[i128]) -> i128 {
    match expression {
        WindowExpr::Loc(column) => row[*column],
        WindowExpr::Nxt(column) => next[*column],
        WindowExpr::Const(value) => i128::from(*value),
        WindowExpr::Add(left, right) => {
            (eval_window(left, row, next) + eval_window(right, row, next)).rem_euclid(BABY_BEAR)
        }
        WindowExpr::Mul(left, right) => {
            (eval_window(left, row, next) * eval_window(right, row, next)).rem_euclid(BABY_BEAR)
        }
    }
}

/// Independent concrete evaluator for the deliberately small descriptor
/// fragment used by both public direct-logic specimens: PI pins and arithmetic
/// gates, with no lookup/memory/hash/range side relations.
fn relation_accepts(
    descriptor: &EffectVmDescriptor2,
    rows: &[Vec<i128>],
    public_inputs: &[i128],
) -> bool {
    if rows.is_empty()
        || rows.iter().any(|row| row.len() != descriptor.trace_width)
        || public_inputs.len() != descriptor.public_input_count
    {
        return false;
    }
    for (row_index, row) in rows.iter().enumerate() {
        let next = rows.get(row_index + 1).unwrap_or(&rows[0]);
        let first = row_index == 0;
        let last = row_index + 1 == rows.len();
        let transition = !last;
        for constraint in &descriptor.constraints {
            let holds = match constraint {
                VmConstraint2::Base(VmConstraint::Gate(body)) => {
                    !transition || eval_lean(body, row).rem_euclid(BABY_BEAR) == 0
                }
                VmConstraint2::Base(VmConstraint::Boundary { row: at, body }) => {
                    let active =
                        matches!(at, VmRow::First) && first || matches!(at, VmRow::Last) && last;
                    !active || eval_lean(body, row).rem_euclid(BABY_BEAR) == 0
                }
                VmConstraint2::Base(VmConstraint::PiBinding {
                    row: at,
                    col,
                    pi_index,
                }) => {
                    let active =
                        matches!(at, VmRow::First) && first || matches!(at, VmRow::Last) && last;
                    !active || (row[*col] - public_inputs[*pi_index]).rem_euclid(BABY_BEAR) == 0
                }
                VmConstraint2::WindowGate(gate) => {
                    let active = !gate.on_transition || transition;
                    !active || eval_window(&gate.body, row, next).rem_euclid(BABY_BEAR) == 0
                }
                // The reviewed descriptors intentionally have none of these.
                VmConstraint2::Base(VmConstraint::Transition { .. })
                | VmConstraint2::Lookup(_)
                | VmConstraint2::MemOp(_)
                | VmConstraint2::MapOp(_)
                | VmConstraint2::UMemOp(_)
                | VmConstraint2::ProofBind(_) => false,
            };
            if !holds {
                return false;
            }
        }
    }
    true
}

fn gabbay_json() -> String {
    guarded_lean_string(GABBAY_LEAN, GABBAY_MARKER).unwrap()
}

fn gabbay_descriptor() -> EffectVmDescriptor2 {
    load_pinned(&gabbay_json(), GABBAY_BLAKE3).unwrap()
}

fn boolgraph_json() -> String {
    guarded_lean_string(BOOLGRAPH_LEAN, BOOLGRAPH_MARKER).unwrap()
}

fn boolgraph_descriptor() -> EffectVmDescriptor2 {
    load_pinned(&boolgraph_json(), BOOLGRAPH_BLAKE3).unwrap()
}

fn bit(value: bool) -> i128 {
    i128::from(value)
}

/// Independent reconstruction of Lean's `canonicalRow truth factorAfter`.
/// `factorAfter = atom0 AND (atom1 OR atom2)` and the materializer allocates
/// atom `(out, inverse)` pairs in postorder, then the OR and AND outputs.
fn boolgraph_canonical(mask: u8) -> (Vec<i128>, Vec<i128>, bool) {
    let truth = |atom: u8| mask & (1 << atom) != 0;
    let t0 = truth(0);
    let t1 = truth(1);
    let t2 = truth(2);
    let t3 = truth(3);
    let or12 = t1 || t2;
    let output = t0 && or12;
    let public = vec![bit(!t0), bit(!t1), bit(!t2), bit(!t3)];
    let mut row = public.clone();
    row.extend([
        bit(t0),
        bit(!t0),
        bit(t1),
        bit(!t1),
        bit(t2),
        bit(!t2),
        bit(or12),
        bit(output),
    ]);
    let source = (t0 && t1) || (t0 && t2);
    (row, public, source)
}

fn assert_identity_pi_layout(descriptor: &EffectVmDescriptor2, count: usize) {
    for index in 0..count {
        match &descriptor.constraints[index] {
            VmConstraint2::Base(VmConstraint::PiBinding {
                row: VmRow::First,
                col,
                pi_index,
            }) => {
                assert_eq!(*col, index);
                assert_eq!(*pi_index, index);
            }
            other => panic!("constraint {index} is not the expected first-row PI pin: {other:?}"),
        }
    }
}

#[test]
fn gabbay_guarded_bytes_parse_and_layout_is_exact() {
    let json = gabbay_json();
    assert_eq!(json.len(), 1_740);
    assert_eq!(
        blake3::hash(json.as_bytes()).to_hex().as_str(),
        GABBAY_BLAKE3
    );

    let descriptor = gabbay_descriptor();
    assert_eq!(descriptor.name, "dregg-gabbay-public-three-entry-direct-v2");
    assert_eq!(descriptor.trace_width, 6);
    assert_eq!(descriptor.public_input_count, 6);
    assert_eq!(descriptor.tables.len(), 1);
    assert_eq!(descriptor.tables[0].id, 0);
    assert_eq!(descriptor.tables[0].arity, 6);
    assert_eq!(descriptor.constraints.len(), 7);
    assert_identity_pi_layout(&descriptor, 6);
    assert_eq!(
        descriptor
            .constraints
            .iter()
            .filter(|constraint| matches!(
                constraint,
                VmConstraint2::Base(VmConstraint::PiBinding { .. })
            ))
            .count(),
        6
    );
    assert_eq!(
        descriptor
            .constraints
            .iter()
            .filter(|constraint| matches!(constraint, VmConstraint2::WindowGate(_)))
            .count(),
        1
    );
    assert!(descriptor.hash_sites.is_empty());
    assert!(descriptor.ranges.is_empty());
}

#[test]
fn gabbay_descriptor_byte_tampering_is_rejected_before_parse() {
    let json = gabbay_json();
    let syntactic_tamper = json.replacen("\"trace_width\":6", "\"trace_width\":7", 1);
    assert!(parse_vm_descriptor2(&syntactic_tamper).is_ok());
    assert!(load_pinned(&syntactic_tamper, GABBAY_BLAKE3).is_err());

    let semantic_tamper = json.replacen("\"v\":1", "\"v\":2", 1);
    assert!(parse_vm_descriptor2(&semantic_tamper).is_ok());
    assert!(load_pinned(&semantic_tamper, GABBAY_BLAKE3).is_err());
}

#[test]
fn gabbay_rust_evaluator_agrees_with_lean_source_semantics_exhaustively() {
    let descriptor = gabbay_descriptor();
    let mut cases = 0usize;
    for x0 in 0..=3 {
        for x1 in 0..=3 {
            for x2 in 0..=3 {
                for y0 in 0..=4 {
                    for y1 in 0..=4 {
                        for y2 in 0..=4 {
                            let row = vec![x0, x1, x2, y0, y1, y2];
                            let expected = y0 == x0 + 1 && y1 == x1 + 1 && y2 == x2 + 1;
                            assert_eq!(
                                relation_accepts(&descriptor, std::slice::from_ref(&row), &row),
                                expected,
                                "differential mismatch for row {row:?}"
                            );
                            cases += 1;
                        }
                    }
                }
            }
        }
    }
    assert_eq!(cases, 8_000);
}

#[test]
fn gabbay_honest_trace_accepts_and_public_tamper_rejects() {
    let descriptor = gabbay_descriptor();
    let honest = vec![5, 9, 17, 6, 10, 18];
    assert!(relation_accepts(
        &descriptor,
        std::slice::from_ref(&honest),
        &honest
    ));

    let mut tampered_public = honest.clone();
    tampered_public[4] += 1;
    assert!(!relation_accepts(
        &descriptor,
        std::slice::from_ref(&honest),
        &tampered_public
    ));
}

#[test]
fn gabbay_live_prover_accepts_honest_and_refuses_public_tamper() {
    let descriptor = gabbay_descriptor();
    let honest_values = [5_u32, 9, 17, 6, 10, 18];
    let honest_row: Vec<BabyBear> = honest_values.into_iter().map(BabyBear::new).collect();
    let proof = prove_vm_descriptor2(
        &descriptor,
        std::slice::from_ref(&honest_row),
        &honest_row,
        &MemBoundaryWitness::default(),
        &[],
    )
    .unwrap();
    verify_vm_descriptor2(&descriptor, &proof, &honest_row).unwrap();

    let mut tampered_public = honest_row.clone();
    tampered_public[4] += BabyBear::ONE;
    assert!(
        prove_vm_descriptor2(
            &descriptor,
            std::slice::from_ref(&honest_row),
            &tampered_public,
            &MemBoundaryWitness::default(),
            &[],
        )
        .is_err()
    );
}

#[test]
fn boolgraph_guarded_bytes_parse_and_layout_is_exact() {
    let json = boolgraph_json();
    assert_eq!(json.len(), 2_654);
    assert_eq!(
        blake3::hash(json.as_bytes()).to_hex().as_str(),
        BOOLGRAPH_BLAKE3
    );

    let descriptor = boolgraph_descriptor();
    assert_eq!(descriptor.name, "dregg-public-materialized-boolgraph-v2-4");
    assert_eq!(descriptor.trace_width, 12);
    assert_eq!(descriptor.public_input_count, 4);
    assert_eq!(descriptor.tables.len(), 1);
    assert_eq!(descriptor.tables[0].id, 0);
    assert_eq!(descriptor.tables[0].arity, 12);
    assert_eq!(descriptor.constraints.len(), 18);
    assert_identity_pi_layout(&descriptor, 4);
    assert_eq!(
        descriptor
            .constraints
            .iter()
            .filter(|constraint| matches!(
                constraint,
                VmConstraint2::Base(VmConstraint::PiBinding { .. })
            ))
            .count(),
        4
    );
    assert_eq!(
        descriptor
            .constraints
            .iter()
            .filter(|constraint| matches!(constraint, VmConstraint2::WindowGate(_)))
            .count(),
        14
    );
    assert!(descriptor.hash_sites.is_empty());
    assert!(descriptor.ranges.is_empty());
}

#[test]
fn boolgraph_descriptor_byte_tampering_is_rejected_before_parse() {
    let json = boolgraph_json();
    let syntactic_tamper = json.replacen("\"trace_width\":12", "\"trace_width\":13", 1);
    assert!(parse_vm_descriptor2(&syntactic_tamper).is_ok());
    assert!(load_pinned(&syntactic_tamper, BOOLGRAPH_BLAKE3).is_err());

    let semantic_tamper = json.replacen("\"v\":-1", "\"v\":-2", 1);
    assert!(parse_vm_descriptor2(&semantic_tamper).is_ok());
    assert!(load_pinned(&semantic_tamper, BOOLGRAPH_BLAKE3).is_err());
}

#[test]
fn boolgraph_rust_evaluator_agrees_with_lean_source_semantics_exhaustively() {
    let descriptor = boolgraph_descriptor();
    let mut accepted = 0usize;
    for mask in 0_u8..16 {
        let (row, public, expected) = boolgraph_canonical(mask);
        let actual = relation_accepts(&descriptor, std::slice::from_ref(&row), &public);
        assert_eq!(
            actual, expected,
            "differential mismatch for truth mask {mask:04b}, row {row:?}"
        );
        accepted += usize::from(actual);
    }
    assert_eq!(accepted, 6);
}

#[test]
fn boolgraph_honest_trace_accepts_and_public_tamper_rejects() {
    // a0=true, a1=true, a2=false, a3=false: both source and optimized
    // formulas are true.
    let descriptor = boolgraph_descriptor();
    let (honest_row, honest_public, expected) = boolgraph_canonical(0b0011);
    assert!(expected);
    assert!(relation_accepts(
        &descriptor,
        std::slice::from_ref(&honest_row),
        &honest_public
    ));

    let mut tampered_public = honest_public;
    tampered_public[0] = 1;
    assert!(!relation_accepts(
        &descriptor,
        std::slice::from_ref(&honest_row),
        &tampered_public
    ));
}

#[test]
fn boolgraph_live_prover_accepts_honest_and_refuses_public_tamper() {
    let descriptor = boolgraph_descriptor();
    let (honest_row, honest_public, expected) = boolgraph_canonical(0b0011);
    assert!(expected);
    let honest_row: Vec<BabyBear> = honest_row
        .into_iter()
        .map(|value| BabyBear::new(value as u32))
        .collect();
    let honest_public: Vec<BabyBear> = honest_public
        .into_iter()
        .map(|value| BabyBear::new(value as u32))
        .collect();
    let proof = prove_vm_descriptor2(
        &descriptor,
        std::slice::from_ref(&honest_row),
        &honest_public,
        &MemBoundaryWitness::default(),
        &[],
    )
    .unwrap();
    verify_vm_descriptor2(&descriptor, &proof, &honest_public).unwrap();

    let mut tampered_public = honest_public;
    tampered_public[0] = BabyBear::ONE;
    assert!(
        prove_vm_descriptor2(
            &descriptor,
            std::slice::from_ref(&honest_row),
            &tampered_public,
            &MemBoundaryWitness::default(),
            &[],
        )
        .is_err()
    );
}
