//! **THE NON-VACUITY GAUNTLET.** The AIR accepts an honest composition, and REFUSES —
//! in-circuit, with no host courtesy — every way of lying about one.
//!
//! Everything here is FAST (the `air_accepts` shadow: the emitted DSL constraints
//! evaluated over the emitted witness row). It uses only constraint kinds the custom-leaf
//! lowering carries, so it is a faithful shadow of "the leaf proves"; `tests/prove_fold.rs`
//! mints the real STARKs behind `#[ignore]`.
//!
//! The role tags below are opaque `u64`s with deliberately meaningless names. This crate
//! knows no roles; a test that used `ROLE_DRAGON` would be smuggling in a game.

use dregg_circuit::dsl::circuit::ColumnKind;
use dregg_circuit::field::BabyBear;
use dregg_param_compose::air::{Forgery, build, build_forged};
use dregg_param_compose::builder::Builder;
use dregg_param_compose::digest::wide_digest;
use dregg_param_compose::field::fb;
use dregg_param_compose::model::{ComposeError, Composition, Knot, LinearTerm, Ruleset, Subject};
use dregg_param_compose::pi;
use dregg_param_compose::shape::{ComposeShape, PARAM_COMPOSE_ABI_VERSION};

// Opaque role tags. Any `u64` is a role; the vocabulary is content.
const ROLE_P: u64 = 101;
const ROLE_Q: u64 = 202;
const ROLE_R: u64 = 303;

/// A small shape that fits the leaf budget at the fixed 8-felt node8 binding width.
fn shape() -> ComposeShape {
    ComposeShape::new(3, 4, 3, 2)
}

fn old8() -> [BabyBear; 8] {
    core::array::from_fn(|i| fb(1000 + i as i128))
}
fn new8() -> [BabyBear; 8] {
    core::array::from_fn(|i| fb(2000 + i as i128))
}

fn subj(identity: u64, role: u64, params: &[i64]) -> Subject {
    Subject {
        identity,
        role,
        params: params.to_vec(),
    }
}

/// Two subjects and a law with one linear term and one KNOT (the nonlinear part).
fn composition() -> Composition {
    Composition {
        subjects: vec![
            subj(7, ROLE_P, &[2, 5, 0, 0]),
            subj(9, ROLE_Q, &[3, 4, 0, 0]),
        ],
        ruleset: Ruleset {
            id: 0xAB,
            version: 1,
            linear: vec![LinearTerm {
                role: ROLE_P,
                param: 0,
                coeff: 10,
            }],
            knots: vec![Knot {
                role_a: ROLE_P,
                param_a: 1,
                role_b: ROLE_Q,
                param_b: 1,
                coeff: -2,
            }],
        },
        param_count: 4,
    }
}

// ===========================================================================
// 1. The honest pole.
// ===========================================================================

/// The reference law, computed by hand. If this drifts, everything below is measuring
/// the wrong thing.
#[test]
fn the_reference_law_is_what_it_says() {
    let c = composition();
    let out = c.compose().expect("well-formed");
    // linear: 10 * P.params[0] = 10*2 = 20
    // knot:   -2 * P.params[1] * Q.params[1] = -2*5*4 = -40
    assert_eq!(out.linear_contributions, vec![20]);
    assert_eq!(out.knot_contributions, vec![-40]);
    assert_eq!(out.outcome, -20);
}

#[test]
fn honest_composition_self_accepts() {
    let air = build(&shape(), &composition(), &old8(), &new8()).expect("builds");
    let fails = air.builder.failing();
    assert!(
        fails.is_empty(),
        "the honest composition must self-accept; failing constraints: {fails:?}"
    );
}

// ===========================================================================
// 2. The PI layout — it plugs into the door, and the roots are the host's.
// ===========================================================================

/// The door's ABI: `pis[0..8] = old_commit8`, `pis[8..16] = new_commit8`. A sub-proof
/// whose PIs do not open with the cell's roots is refused by the executor's state weld
/// (`custom_state_binding`), so this layout is what makes the AIR reachable from a turn.
#[test]
fn public_inputs_open_with_the_doors_state_prefix() {
    let air = build(&shape(), &composition(), &old8(), &new8()).expect("builds");
    let pis = &air.builder.pis;

    let (o, n) = dregg_circuit::effect_vm::custom_state_binding::extract_custom_pi_state_roots(pis)
        .expect("the PI vector must carry the door's 16-felt state prefix");
    assert_eq!(o, old8(), "pis[0..8] must be the cell's PRE-state root");
    assert_eq!(n, new8(), "pis[8..16] must be the cell's POST-state root");
}

/// Every app PI sits where `crate::pi` says, and each root equals the host twin in
/// `crate::reference`. This is the contract a verifier/executor reads, and the pin that
/// keeps the in-circuit chains and the host digests from drifting apart.
#[test]
fn public_input_layout_matches_the_host_roots() {
    let sh = shape();
    let c = composition();
    let air = build(&sh, &c, &old8(), &new8()).expect("builds");
    let pis = &air.builder.pis;
    let w = dregg_param_compose::DIGEST_FELTS;

    assert_eq!(
        pis.len(),
        sh.public_input_count(),
        "PI count is the layout's"
    );
    assert_eq!(pis[pi::ABI_VERSION], fb(PARAM_COMPOSE_ABI_VERSION as i128));
    assert_eq!(pis[pi::SUBJECT_COUNT], fb(2));
    assert_eq!(pis[pi::PARAM_COUNT], fb(4));
    assert_eq!(pis[pi::LINEAR_COUNT], fb(1));
    assert_eq!(pis[pi::KNOT_COUNT], fb(1));

    let slice = |base: usize| pis[base..base + w].to_vec();
    assert_eq!(
        slice(pi::ruleset_root_base()),
        c.ruleset_root(&sh),
        "ruleset_root PI must be the host's digest of the canonical ruleset stream"
    );
    assert_eq!(
        slice(pi::subjects_root_base()),
        c.subjects_root(&sh).unwrap(),
        "subjects_root PI must be the host's digest of the canonical subjects stream"
    );
    assert_eq!(
        slice(pi::outcome_commitment_base()),
        c.outcome_commitment(&sh).unwrap(),
        "outcome_commitment PI must be the host's digest of the composed outcome"
    );
    assert_eq!(
        slice(pi::explanation_root_base()),
        c.explanation_root(&sh).unwrap(),
        "explanation_root PI must be the host's digest of the per-term contributions"
    );
}

/// The in-circuit `wide_chain` and the host `wide_digest` are the same function. If they
/// were not, every root PI would be a number no verifier could reproduce.
#[test]
fn the_in_circuit_chain_is_the_host_digest() {
    let sh = shape();
    let c = composition();
    let air = build(&sh, &c, &old8(), &new8()).expect("builds");
    let got: Vec<BabyBear> = air
        .ruleset_root_cols
        .iter()
        .map(|&col| air.builder.value(col))
        .collect();
    assert_eq!(got, c.ruleset_root(&sh));
    assert_eq!(
        got,
        wide_digest(
            dregg_param_compose::digest::DOMAIN_RULESET,
            &c.ruleset_stream(&sh),
        )
    );
}

/// **THE PRIVACY BOUNDARY.** No param value, and no OUTCOME, appears in a public input.
/// What is public is the ABI version, the four counts, and the four roots — a subject's
/// projection is private witness and the outcome is a commitment.
///
/// The params here are deliberately large and distinctive: small values like `2` would
/// collide with a legitimately-public count (`subject_count == 2`) and the test would be
/// measuring a coincidence rather than a leak.
#[test]
fn no_param_value_or_outcome_leaks_into_a_public_input() {
    let sh = shape();
    let secrets = [111_111i64, 222_222, 333_333, 444_444];
    let c = Composition {
        subjects: vec![
            subj(7, ROLE_P, &[secrets[0], secrets[1], 0, 0]),
            subj(9, ROLE_Q, &[secrets[2], secrets[3], 0, 0]),
        ],
        ruleset: composition().ruleset,
        param_count: 4,
    };
    let air = build(&sh, &c, &old8(), &new8()).expect("builds");
    assert!(air.builder.air_accepts());

    for s in secrets {
        assert!(
            !air.builder.pis.contains(&fb(s as i128)),
            "param value {s} appeared verbatim in the public inputs — the composition \
             must keep projections private"
        );
    }
    let outcome = c.compose().unwrap().outcome;
    assert!(
        !air.builder.pis.contains(&fb(outcome)),
        "the raw outcome {outcome} appeared in the public inputs — it must be a COMMITMENT"
    );
    // ...and every per-term contribution stays private too (only their root is public).
    for contrib in c.compose().unwrap().contributions() {
        assert!(
            !air.builder.pis.contains(&fb(contrib)),
            "explanation term {contrib} appeared verbatim; only explanation_root is public"
        );
    }
}

// ===========================================================================
// 3. NON-VACUITY: a wrong outcome has no satisfying witness.
// ===========================================================================

/// **THE CENTRAL NON-VACUITY CLAIM.** The forged witness is self-consistent EVERYWHERE
/// else: the subjects are honest and canonically ordered, the ruleset is the real one, and
/// the outcome commitment honestly commits the CLAIM. The only thing wrong is that the
/// claimed outcome is not the one the law licenses — so the only constraint that can
/// refuse it is THE LAW. It does.
#[test]
fn a_wrong_outcome_has_no_satisfying_witness() {
    let sh = shape();
    let c = composition();
    let truth = c.compose().unwrap().outcome;

    for delta in [1i128, -1, 7, -100_000] {
        let air = build_forged(
            &sh,
            &c,
            &old8(),
            &new8(),
            &Forgery {
                claimed_outcome: Some(truth + delta),
                ..Default::default()
            },
        )
        .expect("builds");
        assert!(
            !air.builder.air_accepts(),
            "a composition the ruleset does not license (outcome {} vs licensed {truth}) \
             must have NO satisfying witness",
            truth + delta
        );
    }

    // The positive pole: claiming the TRUTH accepts — so the refusals above are the law
    // discriminating, not the gadget refusing everything.
    let air = build_forged(
        &sh,
        &c,
        &old8(),
        &new8(),
        &Forgery {
            claimed_outcome: Some(truth),
            ..Default::default()
        },
    )
    .expect("builds");
    assert!(
        air.builder.air_accepts(),
        "claiming the licensed outcome must accept"
    );
}

// ===========================================================================
// 4. NON-VACUITY: canonical ordering + duplicate rejection, IN-CIRCUIT.
// ===========================================================================

/// **SWAP REFUSED.** The subjects are laid into slots in DESCENDING identity order, with
/// the host's canonicalization bypassed. Note the outcome is UNCHANGED by the swap (rule
/// terms address subjects by ROLE, not by slot) — so what the AIR is refusing is precisely
/// the non-canonical ORDER, which is what makes `subjects_root` a function of the SET
/// rather than of the host's chosen arrangement.
#[test]
fn a_swapped_subject_order_is_refused_in_circuit() {
    let sh = shape();
    let c = composition();
    let mut swapped = c.canonical_subjects().unwrap();
    swapped.reverse();
    assert_ne!(
        swapped,
        c.canonical_subjects().unwrap(),
        "the swap must be real"
    );

    let air = build_forged(
        &sh,
        &c,
        &old8(),
        &new8(),
        &Forgery {
            raw_subject_order: Some(swapped),
            ..Default::default()
        },
    )
    .expect("builds");
    assert!(
        !air.builder.air_accepts(),
        "a non-canonical (descending) subject order must have no satisfying witness"
    );
}

/// **DUPLICATE REFUSED.** The same identity twice — the double-count. The host tooth is
/// bypassed (`raw_subject_order`), so the STRICT increase in the AIR is what refuses it.
#[test]
fn a_duplicated_subject_identity_is_refused_in_circuit() {
    let sh = shape();
    let c = composition();
    // Identity 7 twice, under two different roles — the "same entity in two seats" double
    // count. Ascending-by-identity, so ONLY strictness (not monotonicity) can catch it.
    let dup = vec![
        subj(7, ROLE_P, &[2, 5, 0, 0]),
        subj(7, ROLE_Q, &[3, 4, 0, 0]),
    ];

    let air = build_forged(
        &sh,
        &c,
        &old8(),
        &new8(),
        &Forgery {
            raw_subject_order: Some(dup),
            ..Default::default()
        },
    )
    .expect("builds");
    assert!(
        !air.builder.air_accepts(),
        "a duplicated subject identity must have no satisfying witness — the ordering \
         tooth is STRICT precisely so that equality is a refusal"
    );
}

/// The host oracle refuses duplicates too (fail-closed at both layers), but that is NOT
/// what the tests above rely on.
#[test]
fn the_host_oracle_also_refuses_duplicates_and_role_collisions() {
    let mut c = composition();
    c.subjects = vec![
        subj(7, ROLE_P, &[1, 0, 0, 0]),
        subj(7, ROLE_Q, &[1, 0, 0, 0]),
    ];
    assert_eq!(
        c.canonical_subjects().unwrap_err(),
        ComposeError::DuplicateIdentity(7)
    );

    let mut c = composition();
    c.subjects = vec![
        subj(7, ROLE_P, &[1, 0, 0, 0]),
        subj(8, ROLE_P, &[1, 0, 0, 0]),
    ];
    assert_eq!(
        c.canonical_subjects().unwrap_err(),
        ComposeError::DuplicateRole(ROLE_P)
    );
}

/// **A ROLE IS A KEY, IN-CIRCUIT.** Two active subjects sharing a role would make
/// `role -> subject` a relation rather than a function, letting the PROVER choose which
/// subject a rule term reads — a malleable outcome. Refused.
#[test]
fn two_subjects_sharing_a_role_are_refused_in_circuit() {
    let sh = shape();
    // A law that names ONLY role P, so the collided list still RESOLVES host-side (it
    // picks the first match) and the AIR is actually built — otherwise the host's
    // resolver would refuse first and the in-circuit tooth would never be reached.
    let c = Composition {
        subjects: vec![
            subj(7, ROLE_P, &[2, 5, 0, 0]),
            subj(9, ROLE_Q, &[3, 4, 0, 0]),
        ],
        ruleset: Ruleset {
            id: 1,
            version: 1,
            linear: vec![LinearTerm {
                role: ROLE_P,
                param: 0,
                coeff: 1,
            }],
            knots: vec![],
        },
        param_count: 4,
    };
    // Distinct identities (the ordering tooth is satisfied) but a shared role tag, so
    // ONLY the role-uniqueness tooth can refuse this.
    let collide = vec![
        subj(7, ROLE_P, &[2, 5, 0, 0]),
        subj(9, ROLE_P, &[3, 4, 0, 0]),
    ];

    let air = build_forged(
        &sh,
        &c,
        &old8(),
        &new8(),
        &Forgery {
            raw_subject_order: Some(collide),
            ..Default::default()
        },
    )
    .expect("builds");
    assert!(
        !air.builder.air_accepts(),
        "two active subjects sharing a role must have no satisfying witness"
    );
}

/// A rule term naming a role no subject occupies is FAIL-CLOSED: unprovable, never
/// silently zero. (The host oracle reports it; the in-circuit twin is that
/// `Σ sel_j*active_j == 1` has no solution.)
#[test]
fn a_rule_term_naming_an_absent_role_is_refused() {
    let sh = shape();
    let mut c = composition();
    c.ruleset.linear.push(LinearTerm {
        role: ROLE_R, // no subject occupies it
        param: 0,
        coeff: 1,
    });
    match build(&sh, &c, &old8(), &new8()) {
        Err(ComposeError::UnresolvedRole(ROLE_R)) => {}
        other => panic!("an absent role must fail closed, got {other:?}"),
    }
}

/// A rule term addressing a param slot at or past `param_count` is refused — the
/// "missing/hidden value" rule, fail-closed rather than defaulting to a silent zero the
/// law would then treat as real.
#[test]
fn a_rule_term_past_param_count_is_refused() {
    let sh = shape();
    let mut c = composition();
    c.param_count = 2;
    c.subjects = vec![subj(7, ROLE_P, &[2, 5]), subj(9, ROLE_Q, &[3, 4])];
    c.ruleset.linear = vec![LinearTerm {
        role: ROLE_P,
        param: 3, // >= param_count
        coeff: 1,
    }];
    match build(&sh, &c, &old8(), &new8()) {
        Err(ComposeError::ParamOutOfRange {
            param: 3,
            param_count: 2,
        }) => {}
        other => panic!("a param past param_count must fail closed, got {other:?}"),
    }
}

// ===========================================================================
// 5. NON-VACUITY: the ruleset is LOAD-BEARING, not decoration.
// ===========================================================================

/// A second law over the SAME subjects: different coefficients, one extra knot.
fn other_ruleset() -> Ruleset {
    Ruleset {
        id: 0xAB,
        version: 2, // a new version of the same catalog entry
        linear: vec![LinearTerm {
            role: ROLE_P,
            param: 0,
            coeff: 3, // was 10
        }],
        knots: vec![Knot {
            role_a: ROLE_P,
            param_a: 1,
            role_b: ROLE_Q,
            param_b: 1,
            coeff: 5, // was -2
        }],
    }
}

/// **THE RULESET IS THE LAW.** A different `ruleset_root` licenses a different outcome —
/// and, decisively, a prover holding ruleset A CANNOT prove the outcome B licenses. If
/// the root were decoration, the second half of this test would pass with any law.
#[test]
fn a_different_ruleset_root_licenses_a_different_outcome() {
    let sh = shape();
    let a = composition();
    let mut b = composition();
    b.ruleset = other_ruleset();

    let ya = a.compose().unwrap().outcome;
    let yb = b.compose().unwrap().outcome;
    assert_ne!(ya, yb, "the two laws must license different outcomes");
    assert_ne!(
        a.ruleset_root(&sh),
        b.ruleset_root(&sh),
        "different laws must have different roots"
    );

    // Both honest compositions prove, each under its OWN root.
    let air_a = build(&sh, &a, &old8(), &new8()).expect("builds");
    let air_b = build(&sh, &b, &old8(), &new8()).expect("builds");
    assert!(air_a.builder.air_accepts());
    assert!(air_b.builder.air_accepts());
    let w = dregg_param_compose::DIGEST_FELTS;
    let root_of = |air: &dregg_param_compose::ComposeAir| {
        air.builder.pis[pi::ruleset_root_base()..pi::ruleset_root_base() + w].to_vec()
    };
    assert_eq!(root_of(&air_a), a.ruleset_root(&sh));
    assert_eq!(root_of(&air_b), b.ruleset_root(&sh));
    assert_ne!(root_of(&air_a), root_of(&air_b));

    // **THE TOOTH**: under law A, the outcome law B licenses is UNSATISFIABLE. The law
    // named by the committed root is the one the outcome must obey.
    let forged = build_forged(
        &sh,
        &a,
        &old8(),
        &new8(),
        &Forgery {
            claimed_outcome: Some(yb),
            ..Default::default()
        },
    )
    .expect("builds");
    assert!(
        !forged.builder.air_accepts(),
        "a prover committing ruleset A must not be able to prove the outcome ruleset B \
         licenses — the ruleset root would be decoration"
    );
}

/// Every coefficient is bound to the published `ruleset_root`: editing one moves the root.
/// So a prover cannot quietly use different numbers under an honest catalog root.
#[test]
fn every_ruleset_coefficient_moves_the_ruleset_root() {
    let sh = shape();
    let base = composition();
    let base_root = base.ruleset_root(&sh);

    let mut bump_linear = composition();
    bump_linear.ruleset.linear[0].coeff += 1;
    assert_ne!(
        bump_linear.ruleset_root(&sh),
        base_root,
        "a linear coeff must be bound"
    );

    let mut bump_knot = composition();
    bump_knot.ruleset.knots[0].coeff += 1;
    assert_ne!(
        bump_knot.ruleset_root(&sh),
        base_root,
        "a knot coeff must be bound"
    );

    let mut bump_ver = composition();
    bump_ver.ruleset.version += 1;
    assert_ne!(
        bump_ver.ruleset_root(&sh),
        base_root,
        "the version must be bound"
    );

    let mut bump_role = composition();
    bump_role.ruleset.knots[0].param_b = 0;
    assert_ne!(
        bump_role.ruleset_root(&sh),
        base_root,
        "a knot's param must be bound"
    );
}

/// Every projection felt is bound to `subjects_root` — an edited param, role, or identity
/// moves it. (With the roots PI-bound, that is what makes a forged projection unprovable
/// against a scene's committed subject list.)
#[test]
fn every_projection_felt_moves_the_subjects_root() {
    let sh = shape();
    let base = composition().subjects_root(&sh).unwrap();

    let mut c = composition();
    c.subjects[0].params[1] += 1;
    assert_ne!(c.subjects_root(&sh).unwrap(), base, "a param must be bound");

    let mut c = composition();
    c.subjects[0].identity = 8;
    assert_ne!(
        c.subjects_root(&sh).unwrap(),
        base,
        "an identity must be bound"
    );

    let mut c = composition();
    c.subjects[1].role = ROLE_R;
    assert_ne!(
        c.subjects_root(&sh).unwrap(),
        base,
        "a role tag must be bound"
    );

    // param_count is bound too: the SAME params read under a different schema width is a
    // different projection, not a silent reinterpretation.
    let mut c = composition();
    c.param_count = 3;
    c.subjects = vec![subj(7, ROLE_P, &[2, 5, 0]), subj(9, ROLE_Q, &[3, 4, 0])];
    assert_ne!(
        c.subjects_root(&sh).unwrap(),
        base,
        "param_count must be bound"
    );
}

// ===========================================================================
// 6. THE KNOT CANARY — the nonlinearity is load-bearing.
// ===========================================================================

/// **THE CANARY.** Two compositions with IDENTICAL linear contributions that differ only
/// in a product. Honest: their outcomes differ. Knots neutered: the difference VANISHES.
///
/// This is what makes the nonlinear term demonstrably the thing doing the work — and
/// therefore what makes this a Custom VK rather than a StateConstraint program, whose
/// LINEAR vocabulary could express everything that survives the neutering and nothing that
/// does not.
#[test]
fn neutering_the_knots_collapses_a_difference_that_should_survive() {
    let sh = shape();
    let law = Ruleset {
        id: 1,
        version: 1,
        // linear reads P.params[0] only
        linear: vec![LinearTerm {
            role: ROLE_P,
            param: 0,
            coeff: 1,
        }],
        // the knot reads the PRODUCT P.params[1] * Q.params[1]
        knots: vec![Knot {
            role_a: ROLE_P,
            param_a: 1,
            role_b: ROLE_Q,
            param_b: 1,
            coeff: 1,
        }],
    };
    let mk = |q1: i64| Composition {
        subjects: vec![
            subj(7, ROLE_P, &[2, 5, 0, 0]),
            subj(9, ROLE_Q, &[0, q1, 0, 0]),
        ],
        ruleset: law.clone(),
        param_count: 4,
    };
    let (c1, c2) = (mk(3), mk(6));

    // The linear halves are identical; only the products differ.
    let (o1, o2) = (c1.compose().unwrap(), c2.compose().unwrap());
    assert_eq!(
        o1.linear_contributions, o2.linear_contributions,
        "the fixture must differ ONLY in its knot"
    );
    assert_ne!(o1.outcome, o2.outcome, "honestly, the outcomes must differ");

    // And that difference is visible in-circuit: the outcome columns differ.
    let a1 = build(&sh, &c1, &old8(), &new8()).unwrap();
    let a2 = build(&sh, &c2, &old8(), &new8()).unwrap();
    assert!(a1.builder.air_accepts() && a2.builder.air_accepts());
    let out = |a: &dregg_param_compose::ComposeAir| a.builder.value(a.outcome_col);
    assert_ne!(
        out(&a1),
        out(&a2),
        "the honest AIR must see the two compositions as different"
    );
    assert_ne!(
        c1.outcome_commitment(&sh).unwrap(),
        c2.outcome_commitment(&sh).unwrap(),
        "and commit to different outcomes"
    );

    // NEUTERED: the knot contributions are pinned to zero — the nonlinearity deleted.
    let neuter = Forgery {
        neuter_knots: true,
        ..Default::default()
    };
    let n1 = build_forged(&sh, &c1, &old8(), &new8(), &neuter).unwrap();
    let n2 = build_forged(&sh, &c2, &old8(), &new8(), &neuter).unwrap();
    assert!(
        n1.builder.air_accepts() && n2.builder.air_accepts(),
        "the neutered AIR is a consistent circuit — it is simply a WEAKER one"
    );
    assert_eq!(
        out(&n1),
        out(&n2),
        "CANARY: with the knots neutered, a composition that SHOULD differ no longer does \
         — which is exactly what makes the knot terms load-bearing"
    );
    for a in [&n1, &n2] {
        for &c in &a.knot_contrib_cols {
            assert_eq!(a.builder.value(c), BabyBear::ZERO, "the knot is gone");
        }
    }
}

// ===========================================================================
// 7. FUEL — the shape prices a composition without seeing its content.
// ===========================================================================

/// The shape's declared fuel is the AIR's real site count, so a host can price/refuse a
/// composition from the SHAPE alone (the DoS bound) rather than by building it.
#[test]
fn the_shape_fuel_bound_is_the_airs_real_site_count() {
    // Shapes whose bounds `composition()` fits (2 subjects, 4 params, 1 linear, 1 knot).
    for sh in [
        shape(),
        ComposeShape::new(2, 4, 1, 1),
        ComposeShape::new(5, 6, 4, 3),
        ComposeShape::new(2, 4, 1, 1).with_identity_bits(16),
    ] {
        let air = build(&sh, &composition(), &old8(), &new8()).expect("builds");
        assert_eq!(
            air.builder.hash_site_count(),
            sh.hash_sites(),
            "the shape's fuel bound must equal the emitted Poseidon2 site count"
        );
    }
}

/// A composition exceeding a shape bound is refused before anything is built — the DoS cap.
#[test]
fn a_composition_over_a_shape_bound_is_refused() {
    let sh = ComposeShape::new(1, 4, 3, 2); // max_subjects = 1
    match build(&sh, &composition(), &old8(), &new8()) {
        Err(ComposeError::ExceedsShape("max_subjects")) => {}
        other => panic!("expected the fuel cap to refuse, got {other:?}"),
    }
}

// ===========================================================================
// 8. Genericity: a fresh "game" is a fresh ruleset root under the SAME VK.
// ===========================================================================

/// **THE GENERICITY CLAIM, DRIVEN.** Two entirely different laws — different roles,
/// different params, different knots, different arity — produce IDENTICAL descriptors
/// (hence the same VK). The only thing that changed is data.
///
/// This is the property the whole crate exists for: a new game is a new `ruleset_root` +
/// content, NOT a kernel or AIR edit.
#[test]
fn two_unrelated_rulesets_share_one_vk() {
    let sh = shape();

    let game_one = Composition {
        subjects: vec![
            subj(1, ROLE_P, &[5, 1, 0, 0]),
            subj(2, ROLE_Q, &[7, 2, 0, 0]),
        ],
        ruleset: Ruleset {
            id: 1,
            version: 1,
            linear: vec![LinearTerm {
                role: ROLE_P,
                param: 0,
                coeff: 2,
            }],
            knots: vec![Knot {
                role_a: ROLE_P,
                param_a: 1,
                role_b: ROLE_Q,
                param_b: 1,
                coeff: 3,
            }],
        },
        param_count: 4,
    };
    // A different world entirely: three subjects, other roles, three linear terms, two
    // knots, other params.
    let game_two = Composition {
        subjects: vec![
            subj(11, ROLE_R, &[1, 2, 3, 4]),
            subj(22, ROLE_Q, &[9, 8, 7, 6]),
            subj(33, ROLE_P, &[0, 1, 0, 1]),
        ],
        ruleset: Ruleset {
            id: 999,
            version: 4,
            linear: vec![
                LinearTerm {
                    role: ROLE_R,
                    param: 3,
                    coeff: -7,
                },
                LinearTerm {
                    role: ROLE_Q,
                    param: 0,
                    coeff: 11,
                },
                LinearTerm {
                    role: ROLE_P,
                    param: 1,
                    coeff: 1,
                },
            ],
            knots: vec![
                Knot {
                    role_a: ROLE_R,
                    param_a: 2,
                    role_b: ROLE_Q,
                    param_b: 1,
                    coeff: -1,
                },
                Knot {
                    role_a: ROLE_P,
                    param_a: 3,
                    role_b: ROLE_R,
                    param_b: 0,
                    coeff: 4,
                },
            ],
        },
        param_count: 4,
    };

    let a1 = build(&sh, &game_one, &old8(), &new8()).expect("builds");
    let a2 = build(&sh, &game_two, &old8(), &new8()).expect("builds");
    assert!(a1.builder.air_accepts(), "game one proves");
    assert!(a2.builder.air_accepts(), "game two proves");

    let (d1, d2) = (a1.builder.descriptor(), a2.builder.descriptor());
    assert_eq!(d1.trace_width, d2.trace_width);
    assert_eq!(d1.constraints.len(), d2.constraints.len());
    assert_eq!(
        a1.builder.cellprogram().vk_hash,
        a2.builder.cellprogram().vk_hash,
        "THE POINT: two unrelated rulesets must share ONE VK — a new game is a new \
         ruleset root and new content, never an AIR edit"
    );
    // ...and they are genuinely different compositions under it.
    assert_ne!(a1.builder.pis, a2.builder.pis);
}

// ===========================================================================
// 9. THE NODE8 DIGEST — genuinely 8-felt (~124-bit), and its site binds its inputs.
// ===========================================================================

/// **THE DIGEST IS 8-FELT WIDE, NOT ONE LANE REPEATED.** The multi-output `node8` site's
/// own bar: all 8 root lanes are distinct, and flipping ONE input felt moves EVERY output
/// lane. A digest that only bound lane 0 (the old single-output squeeze) would fail both.
#[test]
fn the_node8_digest_is_genuinely_124_bit_wide() {
    let sh = shape();
    let c = composition();
    let air = build(&sh, &c, &old8(), &new8()).expect("builds");

    // (a) All 8 lanes of a root are distinct field elements — a real 8-felt digest.
    let root: Vec<BabyBear> = c.subjects_root(&sh).unwrap();
    assert_eq!(root.len(), 8, "the binding width is 8 felts");
    for i in 0..8 {
        for j in (i + 1)..8 {
            assert_ne!(
                root[i], root[j],
                "root lanes {i} and {j} coincide — the digest is not genuinely 8-felt wide"
            );
        }
    }
    // The in-circuit root columns carry the same 8 distinct lanes.
    let incirc: Vec<BabyBear> = air
        .subjects_root_cols
        .iter()
        .map(|&col| air.builder.value(col))
        .collect();
    assert_eq!(incirc, root, "the in-circuit root equals the host digest");

    // (b) AVALANCHE: flip ONE input felt (a single param) and EVERY output lane must move.
    let mut c2 = composition();
    c2.subjects[0].params[3] += 1; // one felt, deep in the subjects stream
    let root2 = c2.subjects_root(&sh).unwrap();
    assert_ne!(root, root2, "a changed input must change the digest");
    for lane in 0..8 {
        assert_ne!(
            root[lane], root2[lane],
            "output lane {lane} did not move when an input felt flipped — a single-output \
             digest (lane 0 only) would leave lanes 1..7 free; node8 binds all 8"
        );
    }
}

/// **THE NODE8 FORGERY CANARY.** A `MerkleHash8` site binds its 16 inputs to its 8 outputs
/// via the genuine `cap_node8` permutation: forging an input (without the matching output)
/// is UNSAT. The canary makes the site demonstrably load-bearing — NEUTER it (omit the
/// constraint) and the same forged witness composes; RESTORE it and the forgery is refused.
#[test]
fn a_forged_input_to_a_node8_site_is_refused() {
    // A standalone one-site chip: out8 = cap_node8(left8, right8).
    let mk = |with_site: bool, tamper_left0: Option<i128>| -> Builder {
        let mut b = Builder::new("node8-canary");
        let left: [usize; 8] = core::array::from_fn(|i| {
            b.alloc_f(format!("l{i}"), ColumnKind::Value, fb(3 + i as i128))
        });
        let right: [usize; 8] = core::array::from_fn(|i| {
            b.alloc_f(format!("r{i}"), ColumnKind::Value, fb(50 + i as i128))
        });
        let out_vals = b.cap_node8_value(left, right);
        let out: [usize; 8] =
            core::array::from_fn(|i| b.alloc_f(format!("o{i}"), ColumnKind::Value, out_vals[i]));
        if with_site {
            b.push_merkle_hash8(out, left, right);
        }
        // The forgery: overwrite an INPUT lane, leaving the honest output in place.
        if let Some(v) = tamper_left0 {
            b.tamper(left[0], v);
        }
        b
    };

    // Honest, site present: accepts.
    assert!(
        mk(true, None).air_accepts(),
        "the honest node8 witness must self-accept"
    );

    // Forged input, site present: REFUSED (the output no longer equals cap_node8(inputs)).
    assert!(
        !mk(true, Some(999)).air_accepts(),
        "a forged input to a node8 site must have no satisfying witness"
    );

    // NEUTER the site (omit the MerkleHash8 constraint): the SAME forged witness composes,
    // proving the refusal above was the site doing the work — not decoration.
    assert!(
        mk(false, Some(999)).air_accepts(),
        "with the node8 site removed, the forged input composes — the canary confirms the \
         site is what refuses the forgery"
    );
}

/// The VK is a function of the SHAPE (crossing a bound is a new size class, like a bigger
/// board) — and of nothing else.
#[test]
fn the_vk_tracks_the_shape_and_only_the_shape() {
    let base = build(&shape(), &composition(), &old8(), &new8())
        .unwrap()
        .builder
        .cellprogram()
        .vk_hash;
    for bigger in [
        ComposeShape::new(4, 4, 3, 2),
        ComposeShape::new(3, 5, 3, 2),
        ComposeShape::new(3, 4, 4, 2),
        ComposeShape::new(3, 4, 3, 3),
        shape().with_identity_bits(24),
    ] {
        let vk = build(&bigger, &composition(), &old8(), &new8())
            .unwrap()
            .builder
            .cellprogram()
            .vk_hash;
        assert_ne!(
            vk, base,
            "a different shape must be a different VK: {bigger:?}"
        );
    }
}
