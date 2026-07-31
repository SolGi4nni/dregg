//! THE STANDING CONTROL for the constraint-erasure class on the `DslP3Air` path.
//!
//! ## The class
//!
//! `dsl_p3_air::is_hash` matches only TOP-LEVEL hash forms — deliberately, because it
//! drives Poseidon2 aux-block ALLOCATION and only a top-level hash gets one. Until
//! 2026-07-30 nothing checked that the descriptor CONTAINED no other hash forms, so a
//! `Hash` wrapped in `Gated`/`InvertedGated`/`Squared` was allocated nothing, was not
//! extended into the trace, and folded through `eval_expr` (which returned
//! `AB::Expr::ZERO` for every hash form) to `assert_zero(selector · 0)` — satisfied by
//! every assignment, selector on or off. Not gated off: **erased**. It cost the
//! deployed shielded-spend verifier its nullifier binding.
//!
//! ## Why this file exists rather than an injection
//!
//! An injected forgery is a thing someone has to remember to fire. The real control is
//! inside `DslP3Air::try_from_dsl`: it compares the number of aux blocks it ALLOCATES
//! against the number of hash forms the descriptor CONTAINS (at any depth) and refuses
//! on a mismatch. That runs on every prove AND every verify, for every descriptor, with
//! no list to maintain.
//!
//! This file is that control's own gate: it shows the refusal is **satisfiable**
//! (an ungated hash lowers, and costs exactly one aux block), **refutable** (every
//! wrapped shape in the workspace census is REFUSED — the gate can go red), and **not
//! provable-by-construction** (the widths it compares are real, and a descriptor with
//! no hash at all is unaffected).
//!
//! The four wrapped shapes below are the ones the 2026-07-30 census actually found in
//! this workspace, not invented ones:
//!   * `Gated{Hash}`        — `circuit-prove/src/shielded/spend_circuit.rs` (C4, repaired)
//!   * `InvertedGated{Hash}`— `circuit/src/dsl/note_spending.rs` (C2a..g, C3, C4)
//!   * `Gated{Hash2to1}`    — `circuit/src/dsl/predicates/relational.rs` (C14, C15)
//!   * `Gated{Gated{Hash4to1}}` / `Gated{InvertedGated{Hash2to1}}` — DOUBLY nested,
//!                            `circuit/src/dsl/predicates/base.rs` (C10, C11)

use dregg_circuit::dsl::circuit::{
    CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
};
use dregg_circuit::dsl::dsl_p3_air::{DslP3Air, DslP3Error};
use dregg_circuit::plonky3_prover::POSEIDON2_PERM_AUX_COLS;

const WIDTH: usize = 8;

fn descriptor_of(constraints: Vec<ConstraintExpr>) -> DslCircuit {
    let columns = (0..WIDTH)
        .map(|i| ColumnDef {
            name: format!("c{i}"),
            index: i,
            kind: ColumnKind::Value,
        })
        .collect();
    DslCircuit::new(CircuitDescriptor {
        name: "erasure-control-probe".into(),
        trace_width: WIDTH,
        max_degree: 4,
        columns,
        constraints,
        boundaries: vec![],
        public_input_count: 0,
        lookup_tables: vec![],
    })
}

fn a_hash() -> ConstraintExpr {
    ConstraintExpr::Hash {
        output_col: 7,
        input_cols: vec![0, 1, 2, 3, 4],
    }
}

fn width_of(dsl: &DslCircuit) -> usize {
    let air = DslP3Air::try_from_dsl(dsl).expect("descriptor must lower");
    <DslP3Air as p3_air::BaseAir<p3_baby_bear::BabyBear>>::width(&air)
}

/// SATISFIABLE: an ungated hash lowers, and costs EXACTLY one Poseidon2 aux block.
/// If this ever stops holding, the control below is measuring nothing.
#[test]
fn an_ungated_hash_costs_exactly_one_aux_block() {
    let none = width_of(&descriptor_of(vec![ConstraintExpr::Binary { col: 0 }]));
    let one = width_of(&descriptor_of(vec![
        ConstraintExpr::Binary { col: 0 },
        a_hash(),
    ]));
    let two = width_of(&descriptor_of(vec![
        ConstraintExpr::Binary { col: 0 },
        a_hash(),
        a_hash(),
    ]));

    assert_eq!(none, WIDTH, "no hash ⇒ no aux block");
    assert_eq!(one, WIDTH + POSEIDON2_PERM_AUX_COLS);
    assert_eq!(two, WIDTH + 2 * POSEIDON2_PERM_AUX_COLS);
}

/// REFUTABLE — the gate goes RED. Every wrapped shape the workspace census found must
/// be REFUSED, not lowered. Before 2026-07-30 every one of these lowered silently to
/// `assert_zero(selector · 0)`.
#[test]
fn every_wrapped_hash_shape_is_refused() {
    let gated = ConstraintExpr::Gated {
        selector_col: 0,
        inner: Box::new(a_hash()),
    };
    let inverted = ConstraintExpr::InvertedGated {
        selector_col: 0,
        inner: Box::new(a_hash()),
    };
    let squared = ConstraintExpr::Squared {
        inner: Box::new(a_hash()),
    };
    let gated_2to1 = ConstraintExpr::Gated {
        selector_col: 0,
        inner: Box::new(ConstraintExpr::Hash2to1 {
            output_col: 7,
            input_col_a: 1,
            input_col_b: 2,
        }),
    };
    // The DOUBLY-nested shapes from `predicates/base.rs` — a matcher that peels one
    // layer would miss these.
    let double_gated = ConstraintExpr::Gated {
        selector_col: 0,
        inner: Box::new(ConstraintExpr::Gated {
            selector_col: 1,
            inner: Box::new(ConstraintExpr::Hash4to1 {
                output_col: 7,
                input_cols: [1, 2, 3, 4],
            }),
        }),
    };
    let gated_inverted = ConstraintExpr::Gated {
        selector_col: 0,
        inner: Box::new(ConstraintExpr::InvertedGated {
            selector_col: 1,
            inner: Box::new(ConstraintExpr::Hash2to1 {
                output_col: 7,
                input_col_a: 1,
                input_col_b: 2,
            }),
        }),
    };

    for (label, c) in [
        ("Gated{Hash}", gated),
        ("InvertedGated{Hash}", inverted),
        ("Squared{Hash}", squared),
        ("Gated{Hash2to1}", gated_2to1),
        ("Gated{Gated{Hash4to1}}", double_gated),
        ("Gated{InvertedGated{Hash2to1}}", gated_inverted),
    ] {
        let dsl = descriptor_of(vec![ConstraintExpr::Binary { col: 0 }, c]);
        match DslP3Air::try_from_dsl(&dsl) {
            Err(DslP3Error::ErasedConstraint { .. }) => {}
            Err(other) => panic!("{label}: refused, but with the wrong error: {other}"),
            Ok(_) => panic!(
                "{label} LOWERED. That is the erasure: it receives no Poseidon2 aux block \
                 and emits assert_zero(selector · 0), satisfied by every assignment. \
                 try_from_dsl must refuse it."
            ),
        }
    }
}

/// The refusal must NOT be provable-by-construction: a wrapped ALGEBRAIC inner is
/// perfectly sound under gating and must keep lowering. A control that refuses
/// everything is not a control.
#[test]
fn wrapped_algebraic_inners_still_lower() {
    let cases = vec![
        ConstraintExpr::Gated {
            selector_col: 0,
            inner: Box::new(ConstraintExpr::Equality { col_a: 1, col_b: 2 }),
        },
        ConstraintExpr::InvertedGated {
            selector_col: 0,
            inner: Box::new(ConstraintExpr::Binary { col: 3 }),
        },
        ConstraintExpr::Squared {
            inner: Box::new(ConstraintExpr::Equality { col_a: 1, col_b: 2 }),
        },
        // Nesting depth is not the issue — only a hash at the bottom is.
        ConstraintExpr::Gated {
            selector_col: 0,
            inner: Box::new(ConstraintExpr::Gated {
                selector_col: 1,
                inner: Box::new(ConstraintExpr::Equality { col_a: 2, col_b: 3 }),
            }),
        },
    ];
    for c in cases {
        let dsl = descriptor_of(vec![c]);
        DslP3Air::try_from_dsl(&dsl)
            .expect("a gated ALGEBRAIC constraint is sound and must keep lowering");
        assert_eq!(
            width_of(&dsl),
            WIDTH,
            "an algebraic constraint costs no aux block"
        );
    }
}

/// THE INVARIANT ITSELF, over every DSL descriptor `dregg-circuit` publishes: the AIR
/// either lowers with allocated aux blocks == contained hash forms, or it refuses.
/// There is no third outcome, and "lowered with fewer aux blocks than hashes" is
/// exactly the erasure.
#[test]
fn published_descriptors_allocate_one_aux_block_per_contained_hash() {
    use dregg_circuit::dsl;

    let descriptors: Vec<(&str, CircuitDescriptor)> = vec![
        (
            "merkle_poseidon2",
            dsl::descriptors::merkle_poseidon2_descriptor(),
        ),
        (
            "blinded_merkle_poseidon2",
            dsl::descriptors::blinded_merkle_poseidon2_descriptor(),
        ),
        ("derivation", dsl::descriptors::derivation_descriptor()),
        ("predicate", dsl::predicates::predicate_descriptor()),
        (
            "relational_predicate",
            dsl::predicates::relational_predicate_descriptor(),
        ),
        (
            "note_spending",
            dsl::note_spending::note_spending_circuit_descriptor(),
        ),
    ];

    let mut refused = Vec::new();
    let mut lowered = Vec::new();
    for (name, d) in descriptors {
        let contained = contained_hash_forms(&d);
        let dsl_c = DslCircuit::new(d);
        match DslP3Air::try_from_dsl(&dsl_c) {
            Ok(air) => {
                let w = <DslP3Air as p3_air::BaseAir<p3_baby_bear::BabyBear>>::width(&air);
                let base = dsl_c.descriptor.trace_width;
                // Aux columns beyond the base are hash blocks plus the interior-row
                // selector block; the hash blocks must account for every contained hash.
                let aux = w - base;
                assert!(
                    aux >= contained * POSEIDON2_PERM_AUX_COLS,
                    "{name}: lowered with {aux} aux columns but contains {contained} hash \
                     forms ({} columns' worth) — at least one hash emits NOTHING",
                    contained * POSEIDON2_PERM_AUX_COLS
                );
                lowered.push(name);
            }
            Err(_) => refused.push(name),
        }
    }

    // Not an empty-set pass: both outcomes must actually occur in this workspace, or
    // the sweep is vacuous.
    assert!(
        !lowered.is_empty(),
        "no descriptor lowered — the sweep proved nothing"
    );
    assert!(
        !refused.is_empty(),
        "no descriptor was refused — expected the wrapped-hash descriptors \
         (predicates, note_spending) to be REFUSED on this path; if they now lower, \
         re-check whether the refusal is still armed"
    );
}

/// Count hash forms at any depth — the mirror of `dsl_p3_air::hash_forms_deep`, kept
/// here independently so the control does not check the lowering against itself.
fn contained_hash_forms(d: &CircuitDescriptor) -> usize {
    fn go(c: &ConstraintExpr) -> usize {
        match c {
            ConstraintExpr::Hash { .. }
            | ConstraintExpr::Hash2to1 { .. }
            | ConstraintExpr::Hash4to1 { .. }
            | ConstraintExpr::Hash3Cap { .. }
            | ConstraintExpr::MerkleHash8 { .. } => 1,
            ConstraintExpr::Gated { inner, .. }
            | ConstraintExpr::InvertedGated { inner, .. }
            | ConstraintExpr::Squared { inner } => go(inner),
            _ => 0,
        }
    }
    d.constraints.iter().map(go).sum()
}
