use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, VmConstraint2, WindowExpr, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::direct_logic_frontend::{
    CompileLimits, Formula, FrontendError, InputDecl, LogicProgram, LogicType, LogicValue,
    PredicateTable, Term, compile_logic_program, evaluate_logic_program,
};

const BABY_BEAR: i128 = 2_013_265_921;

fn sample_program() -> LogicProgram {
    let bool_ty = LogicType::Bool;
    let color_ty = LogicType::Finite { cardinality: 3 };

    // allowed(flag, color): false allows 0/1; true allows 1/2.
    let allowed = PredicateTable {
        name: "allowed".into(),
        argument_types: vec![bool_ty.clone(), color_ty.clone()],
        values: vec![true, true, false, false, true, true],
    };
    // Every Boolean has some color witness.  Nested bounds deliberately use
    // de Bruijn 1 (the outer Boolean) and 0 (the inner color).
    let has_witness = PredicateTable {
        name: "has-witness".into(),
        argument_types: vec![bool_ty.clone(), color_ty.clone()],
        values: vec![true, false, false, false, false, true],
    };

    LogicProgram {
        inputs: vec![
            InputDecl {
                name: "flag".into(),
                ty: bool_ty.clone(),
            },
            InputDecl {
                name: "color".into(),
                ty: color_ty.clone(),
            },
        ],
        formula: Formula::And(
            Box::new(Formula::Predicate {
                table: allowed,
                arguments: vec![Term::Input(0), Term::Input(1)],
            }),
            Box::new(Formula::ForAll {
                binder: bool_ty,
                body: Box::new(Formula::Exists {
                    binder: color_ty,
                    body: Box::new(Formula::Predicate {
                        table: has_witness,
                        arguments: vec![Term::Bound(1), Term::Bound(0)],
                    }),
                }),
            }),
        ),
    }
}

#[test]
fn exhaustive_source_descriptor_relation_agreement() {
    let program = sample_program();
    let artifact = compile_logic_program(&program, &CompileLimits::default()).unwrap();

    for flag in [false, true] {
        for color in 0..3 {
            let values = vec![LogicValue::Bool(flag), LogicValue::Finite(color)];
            let expected = evaluate_logic_program(&program, &values).unwrap();
            let atoms = artifact.encode_inputs(&values).unwrap();
            let trace = artifact.one_row_trace(&values).unwrap();
            assert_eq!(trace.len(), 1);
            assert_eq!(trace[0].len(), artifact.descriptor().trace_width);
            assert_eq!(artifact.relation_accepts_atoms(&atoms).unwrap(), expected);
            assert_eq!(
                descriptor_accepts_row(artifact.descriptor(), &atoms),
                expected
            );
        }
    }
}

#[test]
fn enum_encoding_is_constrained_not_trusted() {
    let artifact = compile_logic_program(&sample_program(), &CompileLimits::default()).unwrap();
    let honest = artifact
        .encode_inputs(&[LogicValue::Bool(false), LogicValue::Finite(0)])
        .unwrap();
    assert!(artifact.relation_accepts_atoms(&honest).unwrap());

    let mut zero_hot = honest.clone();
    zero_hot[1..4].fill(false);
    assert!(!artifact.relation_accepts_atoms(&zero_hot).unwrap());
    assert!(!descriptor_accepts_row(artifact.descriptor(), &zero_hot));

    let mut two_hot = honest;
    two_hot[1] = true;
    two_hot[2] = true;
    assert!(!artifact.relation_accepts_atoms(&two_hot).unwrap());
    assert!(!descriptor_accepts_row(artifact.descriptor(), &two_hot));
}

#[test]
fn non_boolean_field_atom_is_rejected_by_live_gate() {
    let artifact = compile_logic_program(&sample_program(), &CompileLimits::default()).unwrap();
    let atoms = artifact
        .encode_inputs(&[LogicValue::Bool(false), LogicValue::Finite(0)])
        .unwrap();
    let mut row: Vec<i128> = atoms.into_iter().map(i128::from).collect();
    row[0] = 2;
    assert!(!descriptor_accepts_field_row(artifact.descriptor(), &row));
}

#[test]
fn unsupported_and_ill_typed_sources_fail_closed() {
    let unbounded = LogicProgram {
        inputs: vec![],
        formula: Formula::ForAll {
            binder: LogicType::UnboundedInteger,
            body: Box::new(Formula::Top),
        },
    };
    assert_eq!(
        compile_logic_program(&unbounded, &CompileLimits::default()).unwrap_err(),
        FrontendError::UnboundedDomain
    );

    let ill_typed = LogicProgram {
        inputs: vec![
            InputDecl {
                name: "bit".into(),
                ty: LogicType::Bool,
            },
            InputDecl {
                name: "tri".into(),
                ty: LogicType::Finite { cardinality: 3 },
            },
        ],
        formula: Formula::Equal(Term::Input(0), Term::Input(1)),
    };
    assert!(matches!(
        compile_logic_program(&ill_typed, &CompileLimits::default()),
        Err(FrontendError::TypeMismatch { .. })
    ));

    let malformed_predicate = LogicProgram {
        inputs: vec![],
        formula: Formula::Predicate {
            table: PredicateTable {
                name: "bad".into(),
                argument_types: vec![LogicType::Bool],
                values: vec![true],
            },
            arguments: vec![Term::Constant {
                ty: LogicType::Bool,
                value: 0,
            }],
        },
    };
    assert_eq!(
        compile_logic_program(&malformed_predicate, &CompileLimits::default()).unwrap_err(),
        FrontendError::PredicateShapeMismatch {
            expected: 2,
            actual: 1,
        }
    );
}

#[test]
fn expansion_limits_refuse_instead_of_truncating() {
    let program = LogicProgram {
        inputs: vec![],
        formula: Formula::ForAll {
            binder: LogicType::Bool,
            body: Box::new(Formula::Top),
        },
    };
    let limits = CompileLimits {
        maximum_quantifier_instances: 1,
        ..CompileLimits::default()
    };
    assert_eq!(
        compile_logic_program(&program, &limits).unwrap_err(),
        FrontendError::QuantifierExpansionTooLarge {
            instances: 2,
            maximum: 1,
        }
    );
}

#[test]
fn quantified_false_formula_rejects_and_zero_input_programs_stay_live() {
    let quantified_false = LogicProgram {
        inputs: vec![],
        formula: Formula::ForAll {
            binder: LogicType::Bool,
            body: Box::new(Formula::Equal(
                Term::Bound(0),
                Term::Constant {
                    ty: LogicType::Bool,
                    value: 0,
                },
            )),
        },
    };
    let false_artifact =
        compile_logic_program(&quantified_false, &CompileLimits::default()).unwrap();
    assert_eq!(false_artifact.logical_atom_count(), 0);
    assert_eq!(false_artifact.descriptor().trace_width, 1);
    assert!(!false_artifact.relation_accepts_atoms(&[false]).unwrap());
    assert!(!descriptor_accepts_row(
        false_artifact.descriptor(),
        &[false]
    ));

    let top = LogicProgram {
        inputs: vec![],
        formula: Formula::Top,
    };
    let top_artifact = compile_logic_program(&top, &CompileLimits::default()).unwrap();
    assert!(top_artifact.relation_accepts_atoms(&[false]).unwrap());
    assert!(descriptor_accepts_row(top_artifact.descriptor(), &[false]));
}

#[test]
fn honest_compilation_proves_and_verifies_through_live_backend() {
    let program = LogicProgram {
        inputs: vec![InputDecl {
            name: "flag".into(),
            ty: LogicType::Bool,
        }],
        formula: Formula::Equal(
            Term::Input(0),
            Term::Constant {
                ty: LogicType::Bool,
                value: 1,
            },
        ),
    };
    let artifact = compile_logic_program(&program, &CompileLimits::default()).unwrap();
    let trace = artifact.one_row_trace(&[LogicValue::Bool(true)]).unwrap();
    let proof = prove_vm_descriptor2(
        artifact.descriptor(),
        &trace,
        &[],
        &MemBoundaryWitness::default(),
        &[],
    )
    .unwrap();
    verify_vm_descriptor2(artifact.descriptor(), &proof, &[]).unwrap();

    let false_trace = artifact.one_row_trace(&[LogicValue::Bool(false)]).unwrap();
    assert!(
        prove_vm_descriptor2(
            artifact.descriptor(),
            &false_trace,
            &[],
            &MemBoundaryWitness::default(),
            &[],
        )
        .is_err(),
        "the live prover must refuse a row falsifying the source formula"
    );
}

#[test]
fn portable_wire_roundtrips_and_hashes_are_pinned() {
    let artifact = compile_logic_program(&sample_program(), &CompileLimits::default()).unwrap();
    assert_eq!(
        parse_vm_descriptor2(artifact.descriptor_json()).unwrap(),
        *artifact.descriptor()
    );
    assert_eq!(artifact.descriptor().trace_width, 4);
    assert_eq!(artifact.descriptor().constraints.len(), 6);
    assert_eq!(artifact.logical_atom_count(), 4);
    assert!(
        artifact
            .descriptor_json()
            .starts_with("{\"name\":\"dregg-direct-logic-v1-")
    );

    // Versioned source and exact descriptor bytes: any semantic, ordering,
    // tag, coefficient, or encoder drift changes one of these pins.
    assert_eq!(
        artifact.source_blake3_hex(),
        "dedc2cf1fbf6548930b4217eee7e6373b055a0bfb1164f6845d442079affdb90"
    );
    assert_eq!(
        artifact.descriptor_blake3_hex(),
        "38e5a5adf04722bd7e4df693fa5233c288b6c5669842f3ff7beb496000868675"
    );
}

#[test]
fn input_encoder_rejects_wrong_values() {
    let artifact = compile_logic_program(&sample_program(), &CompileLimits::default()).unwrap();
    assert_eq!(
        artifact
            .encode_inputs(&[LogicValue::Bool(false)])
            .unwrap_err(),
        FrontendError::InputCountMismatch {
            expected: 2,
            actual: 1,
        }
    );
    assert_eq!(
        artifact
            .encode_inputs(&[LogicValue::Bool(false), LogicValue::Finite(3)])
            .unwrap_err(),
        FrontendError::InputValueOutOfRange {
            input: 1,
            value: 3,
            cardinality: 3,
        }
    );
}

fn descriptor_accepts_row(
    descriptor: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    atoms: &[bool],
) -> bool {
    let row: Vec<i128> = atoms.iter().copied().map(i128::from).collect();
    descriptor_accepts_field_row(descriptor, &row)
}

fn descriptor_accepts_field_row(
    descriptor: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    row: &[i128],
) -> bool {
    descriptor.constraints.iter().all(|constraint| {
        let VmConstraint2::WindowGate(window) = constraint else {
            return false;
        };
        !window.on_transition && eval_window(&window.body, row).rem_euclid(BABY_BEAR) == 0
    })
}

fn eval_window(expression: &WindowExpr, row: &[i128]) -> i128 {
    match expression {
        WindowExpr::Loc(column) | WindowExpr::Nxt(column) => row[*column],
        WindowExpr::Const(value) => i128::from(*value),
        WindowExpr::Add(left, right) => {
            (eval_window(left, row) + eval_window(right, row)).rem_euclid(BABY_BEAR)
        }
        WindowExpr::Mul(left, right) => {
            (eval_window(left, row) * eval_window(right, row)).rem_euclid(BABY_BEAR)
        }
    }
}
