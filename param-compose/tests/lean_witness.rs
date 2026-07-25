//! **THE WITNESS PRODUCER MEETS THE LEAN-AUTHORED AIR.**
//!
//! `crate::witness` fills the column layout of the Lean-emitted descriptor
//! (`metatheory/Dregg2/Circuit/Emit/ParamComposeEmit.lean`). This file is the gate that the fill is
//! the one that descriptor demands:
//!
//!   1. the layout's width and its four ROOT column groups agree with the DECODED emitted object
//!      (not with themselves) — [`check_layout_against_descriptor`];
//!   2. the produced row satisfies every emitted ROW-LOCAL constraint, judged by the DEPLOYED IR-v2
//!      evaluator `dregg_circuit::descriptor_ir2::ir2_eval_accepts_i64` (the real `Ir2Air::Main`
//!      eval, not a predicate this crate wrote);
//!   3. the produced digest columns equal `crate::reference`'s host twins, so the four committed
//!      roots the PIs publish are the same values the receipt layer computes off-circuit;
//!   4. four deliberate forgeries — a claimed outcome, a deleted nonlinearity, an unsorted subject
//!      list, a duplicated identity, a role collision — are REFUSED by the emitted gates.
//!
//! ## What this establishes, and what it does NOT
//!
//! ESTABLISHES: the producer's rows satisfy the Lean-emitted descriptor at two independent shapes,
//! and the emitted gates bite on the rows it produces. That is what makes the descriptor provable
//! from Rust.
//!
//! DOES NOT: prove anything about all inputs. These are cases. Semantic faithfulness of the AIR
//! itself is `ParamComposeRefine.paramCompose_refines_law` in Lean, over the ACTUAL emitted object.
//! Nothing here is refinement, translation validation, or verification.

use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, ir2_eval_accepts_i64, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_param_compose::digest::DIGEST_FELTS;
use dregg_param_compose::field::fb;
use dregg_param_compose::lean_descriptor::{
    lean_descriptor_for, lean_descriptor_name, pc_min, pc_realistic, pinned_shapes,
};
use dregg_param_compose::model::{Composition, Knot, LinearTerm, Ruleset, Subject};
use dregg_param_compose::pi;
use dregg_param_compose::shape::ComposeShape;
use dregg_param_compose::witness::{
    CHAIN_EXPLANATION, CHAIN_OUTCOME, CHAIN_RULESET, CHAIN_SUBJECTS, ComposeLayout, ComposeWitness,
    check_layout_against_descriptor, compose_witness, compose_witness_over,
};

fn old8() -> [BabyBear; 8] {
    core::array::from_fn(|i| BabyBear::new(1_000 + i as u32))
}
fn new8() -> [BabyBear; 8] {
    core::array::from_fn(|i| BabyBear::new(2_000 + i as u32))
}

/// A composition at the MINIMAL pinned shape (`pcMin`: n2 p2 l1 k1, a 2-bit identity namespace).
fn min_composition() -> Composition {
    Composition {
        subjects: vec![
            Subject {
                identity: 1,
                role: 101,
                params: vec![3, 5],
            },
            Subject {
                identity: 3,
                role: 202,
                params: vec![7, 2],
            },
        ],
        ruleset: Ruleset {
            id: 0xAB,
            version: 1,
            linear: vec![LinearTerm {
                role: 101,
                param: 0,
                coeff: 10,
            }],
            knots: vec![Knot {
                role_a: 101,
                param_a: 1,
                role_b: 202,
                param_b: 1,
                coeff: -2,
            }],
        },
        param_count: 2,
    }
}

/// A SATURATED composition at the DEPLOYED shape (`pcRealistic`: n4 p8 l8 k6, 28-bit identities) —
/// the one `entity-compose` builds.
fn realistic_composition() -> Composition {
    let roles: Vec<u64> = (0..4).map(|i| 100 + i as u64).collect();
    Composition {
        subjects: (0..4)
            .map(|i| Subject {
                identity: 10 + 7 * i as u64,
                role: roles[i],
                params: (0..8).map(|p| (i + p + 1) as i64).collect(),
            })
            .collect(),
        ruleset: Ruleset {
            id: 42,
            version: 1,
            linear: (0..8)
                .map(|t| LinearTerm {
                    role: roles[t % 4],
                    param: t % 8,
                    coeff: (t as i64 + 1) * 3,
                })
                .collect(),
            knots: (0..6)
                .map(|k| Knot {
                    role_a: roles[k % 4],
                    param_a: k % 8,
                    role_b: roles[(k + 1) % 4],
                    param_b: (k + 1) % 8,
                    coeff: -(k as i64 + 1),
                })
                .collect(),
        },
        param_count: 8,
    }
}

fn cases() -> Vec<(&'static str, ComposeShape, Composition)> {
    vec![
        ("pcMin", pc_min(), min_composition()),
        ("pcRealistic", pc_realistic(), realistic_composition()),
    ]
}

/// The deployed IR-v2 row-local evaluator's verdict on a produced witness.
fn emitted_accepts(shape: &ComposeShape, w: &ComposeWitness, rows: usize) -> bool {
    let desc = lean_descriptor_for(shape).expect("a Lean-pinned shape");
    let base: Vec<Vec<i64>> = w
        .base_trace(rows)
        .iter()
        .map(|r| r.iter().map(|f| f.0 as i64).collect())
        .collect();
    let pis: Vec<i64> = w.pis.iter().map(|f| f.0 as i64).collect();
    ir2_eval_accepts_i64(&desc, &base, &pis)
}

// ---------------------------------------------------------------------------
// 1. The layout is checked against the EMITTED object, not against itself.
// ---------------------------------------------------------------------------

#[test]
fn the_layout_agrees_with_the_emitted_descriptor() {
    for (name, shape, _) in cases() {
        let desc = lean_descriptor_for(&shape).expect("a Lean-pinned shape");
        let layout = ComposeLayout::new(&shape);
        let bad = check_layout_against_descriptor(&layout, &desc);
        assert!(bad.is_empty(), "{name}: layout drifted from Lean: {bad:?}");
    }
}

#[test]
fn the_pinned_widths_are_the_leans_own() {
    assert_eq!(ComposeLayout::new(&pc_min()).width, 108);
    assert_eq!(ComposeLayout::new(&pc_realistic()).width, 770);
    // The Lean family drops the shared `zero` column and the four 8-felt IV column groups the Rust
    // AIR allocated (33 columns), replacing them with literal constants in the chip tuple.
    assert_eq!(ComposeLayout::new(&pc_realistic()).width + 33, 803);
}

// ---------------------------------------------------------------------------
// 2. The produced row satisfies the emitted descriptor.
// ---------------------------------------------------------------------------

#[test]
fn the_producer_satisfies_the_lean_descriptor() {
    for (name, shape, comp) in cases() {
        let w = compose_witness(&shape, &comp, &old8(), &new8())
            .unwrap_or_else(|e| panic!("{name}: the honest composition produces a witness: {e}"));
        assert_eq!(w.row.len(), ComposeLayout::new(&shape).width);
        assert_eq!(w.pis.len(), pi::public_input_count());
        assert!(
            emitted_accepts(&shape, &w, 4),
            "{name}: the emitted descriptor must accept the honest produced row"
        );
    }
}

// ---------------------------------------------------------------------------
// 3. The produced roots ARE the reference host twins.
// ---------------------------------------------------------------------------

#[test]
fn the_produced_roots_are_the_reference_host_twins() {
    for (name, shape, comp) in cases() {
        let w = compose_witness(&shape, &comp, &old8(), &new8()).expect("produces");
        assert_eq!(
            w.root(CHAIN_RULESET),
            comp.ruleset_root(&shape),
            "{name}: ruleset_root"
        );
        assert_eq!(
            w.root(CHAIN_SUBJECTS),
            comp.subjects_root(&shape).expect("subjects_root"),
            "{name}: subjects_root"
        );
        assert_eq!(
            w.root(CHAIN_OUTCOME),
            comp.outcome_commitment(&shape).expect("outcome"),
            "{name}: outcome_commitment"
        );
        assert_eq!(
            w.root(CHAIN_EXPLANATION),
            comp.explanation_root(&shape).expect("explanation"),
            "{name}: explanation_root"
        );
        // ...and the PI vector publishes exactly those, over the door's `[old8 ‖ new8]` prefix.
        assert_eq!(&w.pis[..8], &old8()[..]);
        assert_eq!(&w.pis[8..16], &new8()[..]);
        let base = pi::outcome_commitment_base();
        assert_eq!(
            &w.pis[base..base + DIGEST_FELTS],
            &comp.outcome_commitment(&shape).unwrap()[..]
        );
    }
}

/// **THE PRIVACY BOUNDARY.** No param value, and no raw outcome, reaches a public input.
///
/// The params must be LARGE and DISTINCTIVE for this to measure a LEAK rather than a
/// coincidence. `realistic_composition`'s own params are the small integers `1..=12`, four of
/// which are legitimately public in another slot — `abi_version = 1`, `subject_count = 4`,
/// `knot_count = 6`, `param_count = 8` — so over that fixture the assertion below fires on
/// `params[0] = 1` colliding with the ABI version. It DID fire: this test was RED at HEAD,
/// asserting a leak that was really the ABI-version slot. Repaired 2026-07-25 by making the
/// params distinctive, which is the same discipline `tests/composition.rs`'s twin already spells
/// out in its own doc comment.
#[test]
fn param_values_never_reach_a_public_input() {
    let shape = pc_realistic();
    let mut comp = realistic_composition();
    for (i, s) in comp.subjects.iter_mut().enumerate() {
        for (q, v) in s.params.iter_mut().enumerate() {
            *v = 111_111 + (i * 8 + q) as i64;
        }
    }
    let w = compose_witness(&shape, &comp, &old8(), &new8()).expect("produces");
    assert!(
        emitted_accepts(&shape, &w, 4),
        "the distinctive-param composition must still satisfy the emitted descriptor"
    );
    for s in &comp.subjects {
        for &p in &s.params {
            assert!(
                !w.pis.contains(&fb(p as i128)),
                "param value {p} leaked into the PIs"
            );
        }
    }
    // ...and the composed outcome is a COMMITMENT, never published raw.
    let outcome = comp.compose().expect("composes").outcome;
    assert!(
        !w.pis.contains(&fb(outcome)),
        "the raw outcome {outcome} appeared in the public inputs — it must be a COMMITMENT"
    );
}

// ---------------------------------------------------------------------------
// 4. The emitted gates BITE on the rows this producer makes.
// ---------------------------------------------------------------------------

#[test]
fn a_claimed_outcome_the_law_does_not_license_is_refused() {
    let (shape, comp) = (pc_min(), min_composition());
    let mut w = compose_witness(&shape, &comp, &old8(), &new8()).expect("produces");
    assert!(emitted_accepts(&shape, &w, 4), "honest baseline");

    // Claim a different outcome and RE-COMMIT to it honestly (the chains and the PIs now bind the
    // lie), so the only constraint that can refuse it is the composition law itself.
    w.row[w.layout.out_col] = fb(999_999);
    w.fill_chains();
    w.fill_pis();
    assert!(
        !emitted_accepts(&shape, &w, 4),
        "THE LAW must refuse an outcome it does not license"
    );
}

#[test]
fn deleting_the_nonlinearity_is_refused() {
    let (shape, comp) = (pc_min(), min_composition());
    let mut w = compose_witness(&shape, &comp, &old8(), &new8()).expect("produces");
    let layout = w.layout;

    // THE KNOT CANARY: pin every knot contribution to ZERO and re-balance the outcome to the
    // linear part alone, so the LAW gate still holds and the ONLY thing that can refuse is the
    // knot's own `contrib = coeff · va · vb`.
    let mut linear_sum = BabyBear::ZERO;
    for t in 0..shape.max_linear {
        linear_sum += w.row[layout.l_contrib(t)];
    }
    for t in 0..shape.max_knots {
        w.row[layout.k_contrib(t)] = BabyBear::ZERO;
    }
    w.row[layout.out_col] = linear_sum;
    w.fill_chains();
    w.fill_pis();
    assert!(
        !emitted_accepts(&shape, &w, 4),
        "the degree-3 knot gate must refuse a deleted nonlinearity"
    );
}

#[test]
fn an_unsorted_subject_list_is_refused_in_circuit() {
    let (shape, comp) = (pc_min(), min_composition());
    let mut swapped = comp.canonical_subjects().expect("canonicalizes");
    swapped.reverse();
    let w = compose_witness_over(&shape, &comp, &swapped, &old8(), &new8())
        .expect("the producer lays the list AS GIVEN — the AIR is the judge");
    assert!(
        !emitted_accepts(&shape, &w, 4),
        "the ordering tooth must refuse a descending identity list"
    );
}

#[test]
fn a_duplicated_identity_is_refused_in_circuit() {
    let (shape, comp) = (pc_min(), min_composition());
    let mut dup = comp.canonical_subjects().expect("canonicalizes");
    dup[1].identity = dup[0].identity;
    let w = compose_witness_over(&shape, &comp, &dup, &old8(), &new8()).expect("lays it as given");
    assert!(
        !emitted_accepts(&shape, &w, 4),
        "the STRICT increase must refuse two subjects at one identity"
    );
}

#[test]
fn a_role_collision_is_refused_in_circuit() {
    // A law addressing ONE role, so a slot list where BOTH subjects carry that tag still resolves
    // host-side (`resolve` takes the first match) and the only thing that can refuse it is the
    // emitted pairwise `cond_nonzero` — a role is a KEY.
    let single_role = Composition {
        subjects: vec![
            Subject {
                identity: 1,
                role: 101,
                params: vec![3, 5],
            },
            Subject {
                identity: 3,
                role: 101,
                params: vec![7, 2],
            },
        ],
        ruleset: Ruleset {
            id: 0xAB,
            version: 1,
            linear: vec![LinearTerm {
                role: 101,
                param: 0,
                coeff: 10,
            }],
            knots: vec![Knot {
                role_a: 101,
                param_a: 1,
                role_b: 101,
                param_b: 0,
                coeff: -2,
            }],
        },
        param_count: 2,
    };
    let shape = pc_min();
    let slots = single_role.subjects.clone();
    let w = compose_witness_over(&shape, &single_role, &slots, &old8(), &new8())
        .expect("lays it as given (a role resolves to the FIRST slot carrying it)");
    assert!(
        !emitted_accepts(&shape, &w, 4),
        "a role is a KEY: two active subjects must not share a tag"
    );

    // Positive pole: the SAME law over distinct role tags accepts, so the refusal above is the
    // key tooth discriminating and not the fixture being malformed.
    let mut distinct = single_role.clone();
    distinct.subjects[1].role = 202;
    let ok_slots = distinct.subjects.clone();
    let w2 =
        compose_witness_over(&shape, &distinct, &ok_slots, &old8(), &new8()).expect("produces");
    assert!(emitted_accepts(&shape, &w2, 4), "distinct role tags accept");
}

#[test]
fn a_forged_public_root_is_refused() {
    let (shape, comp) = (pc_min(), min_composition());
    let mut w = compose_witness(&shape, &comp, &old8(), &new8()).expect("produces");
    let base = pi::ruleset_root_base();
    w.pis[base] += BabyBear::new(1);
    assert!(
        !emitted_accepts(&shape, &w, 4),
        "the PI binding must refuse a published root the row does not carry"
    );
}

// ---------------------------------------------------------------------------
// 5. THE REAL PROVER. `#[ignore]` — a genuine STARK over 108/770 columns.
// ---------------------------------------------------------------------------

/// `cargo test -p dregg-param-compose --test lean_witness -- --ignored --nocapture`
#[test]
#[ignore = "a real IR-v2 batch STARK over the Lean-authored descriptor (minutes)"]
fn the_lean_descriptor_really_proves_over_the_produced_witness() {
    for (name, shape, comp) in cases() {
        let desc = lean_descriptor_for(&shape).expect("a Lean-pinned shape");
        let w = compose_witness(&shape, &comp, &old8(), &new8()).expect("produces");
        let trace = w.base_trace(8);
        let t0 = std::time::Instant::now();
        let proof =
            prove_vm_descriptor2(&desc, &trace, &w.pis, &MemBoundaryWitness::default(), &[])
                .unwrap_or_else(|e| panic!("{name}: the Lean-authored descriptor must prove: {e}"));
        eprintln!(
            "{name}: proved {} columns in {:?}",
            desc.trace_width,
            t0.elapsed()
        );
        verify_vm_descriptor2(&desc, &proof, &w.pis)
            .unwrap_or_else(|e| panic!("{name}: the proof must verify: {e}"));
    }
}

// ---------------------------------------------------------------------------
// 6. THE PIN CENSUS. Every shape Rust claims to reach, Lean actually pinned.
// ---------------------------------------------------------------------------

/// **`pinned_shapes()` is a MIRROR of the Lean tree, and this is the gate that it is a faithful
/// one.** Each entry must resolve out of the Lean SOURCE TEXT, decode as IR-v2, and carry the
/// descriptor name that shape emits. A shape listed in Rust but dropped from (or never landed in)
/// the Lean tree goes RED here instead of quietly leaving the reachable set — the resolver derives
/// the golden `def` name from the shape, so a typo'd or missing pin is indistinguishable from
/// "unreachable" without this check.
///
/// It also re-checks the LAYOUT against the emitted width at every pinned shape, not just the two
/// the older cases cover: `ComposeLayout` computes the column layout in Rust, and if it disagreed
/// with the Lean emission at any shape the witness producer would fill the wrong columns.
#[test]
fn every_pinned_shape_resolves_and_names_itself() {
    let shapes = pinned_shapes();
    assert_eq!(shapes.len(), 18, "the pinned census changed size");
    for (name, shape) in shapes {
        let desc = lean_descriptor_for(&shape).unwrap_or_else(|| {
            panic!("{name}: Lean must carry a byte-pinned instance at {shape:?}")
        });
        assert_eq!(
            desc.name,
            lean_descriptor_name(&shape),
            "{name}: the decoded golden must be the descriptor this shape names"
        );
        assert_eq!(
            desc.trace_width,
            ComposeLayout::new(&shape).width,
            "{name}: the Rust column layout drifted from the Lean-emitted width"
        );
        assert_eq!(
            desc.public_input_count,
            pi::public_input_count(),
            "{name}: the PI layout is constant across shapes"
        );
        let bad = check_layout_against_descriptor(&ComposeLayout::new(&shape), &desc);
        assert!(bad.is_empty(), "{name}: layout drifted from Lean: {bad:?}");
    }
}

/// **THE STRUCTURAL CROSS-CHECK, AS A GATE.** The retired hand-written Rust AIR
/// (`param-compose/src/{air,builder}.rs`, DELETED 2026-07-25) carried exactly 33 more columns than
/// the Lean family emits at every shape: its single `zero` padding column plus the four 8-felt IV
/// column groups its `wide_chain` allocated once per chain (`1 + 4 * 8 = 33`), which the Lean
/// author replaces with literal constants in the chip tuple.
///
/// Both terms depended on NOTHING but "there are four digest chains", so the delta was
/// shape-invariant by construction — which is what made it evidence that the two objects were the
/// same AIR rather than a coincidence at one size.
///
/// **At what resolution, now.** The Rust numbers below (219 / 379 / 803) are HISTORICAL: they were
/// measured against the deleted AIR and are recorded here and in `lib.rs`'s budget table. Nothing
/// re-measures them. What this test still does is pin the LEAN widths — a Lean emission that moved
/// at any of these three shapes goes red here — so it survives as a drift detector on the surviving
/// side, not as a live differential.
#[test]
fn the_lean_width_is_the_rust_width_less_the_thirty_three_pinned_columns() {
    // (shape, the HISTORICAL `prog` column count of the deleted Rust AIR — `lib.rs`'s budget table)
    for (shape, rust_prog) in [
        (ComposeShape::new(2, 2, 1, 1), 219usize),
        (ComposeShape::new(3, 4, 3, 2), 379),
        (pc_realistic(), 803),
    ] {
        let lean = lean_descriptor_for(&shape)
            .expect("a Lean-pinned shape")
            .trace_width;
        assert_eq!(
            lean + 33,
            rust_prog,
            "{shape:?}: the Lean emission is {lean}, the published Rust prog is {rust_prog}; the \
             delta must be exactly the `zero` column + 4 x 8 IV columns"
        );
    }
}

/// **THE `None` STAYS FAIL-CLOSED.** Widening the reachable set is a Lean change; a shape Lean has
/// not pinned must still be UNREACHABLE from Rust rather than re-emitted here (re-emitting would be
/// authoring the AIR in Rust). This drives that half so the resolver's fallback cannot rot into a
/// silent Rust-side construction.
#[test]
fn an_unpinned_shape_is_still_unreachable() {
    for unpinned in [
        ComposeShape::new(7, 9, 5, 4),
        ComposeShape::new(3, 4, 3, 2).with_identity_bits(27),
        // The vacuous-ordering shape `size.rs` refuses: never pinned, because the object must not
        // exist. `identity_bits_sound` is FALSE here.
        pc_realistic().with_identity_bits(31),
    ] {
        assert!(
            lean_descriptor_for(&unpinned).is_none(),
            "{unpinned:?}: an unpinned shape must be UNREACHABLE, not reconstructed in Rust"
        );
    }
}
