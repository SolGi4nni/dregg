//! **The emit-gate differential for the Mina bridge fixture AIR.**
//!
//! `circuit/src/bin/mina_stark_fixture.rs` carried a hand-written Rust AIR until 2026-07-30 —
//! `impl<AB: AirBuilder> Air<AB> for MinaFixtureAir`, 7 authored sites, caught red by
//! `law1_enforcement_gate` and recorded as HORIZONLOG E4. It is now emitted from
//! `metatheory/Dregg2/Circuit/Emit/MinaFixtureEmit.lean` and interpreted by
//! [`Ir2UniAir`]. This file is the gate on that swap.
//!
//! ## Why a Rust reference AIR is legitimate HERE and nowhere else
//!
//! Law #1 forbids Rust-authored constraints in `src/`. It does not forbid a Rust-side EXPECTATION
//! in a test — an emit-gate differential has to build one in order to compare it against the Lean
//! emission; that is the law working, and it is why the gate scopes `tests/` trees out by name.
//! [`hand_written_reference`] below is the DELETED AIR, verbatim, kept as the thing the emitted
//! descriptor must reproduce. If it ever moves to `src/`, the gate reds.
//!
//! ## What the differential actually decides, and why it is not a syntax comparison
//!
//! The obvious test — compare `get_symbolic_constraints` term-for-term — is the WRONG bar, and
//! measurably so: it fails on this pair for two reasons that are both immaterial to the protocol.
//! The Lean `WindowExpr` grammar has `add`/`mul`/`const` and NO subtraction node, so `b - a^3`
//! emits as `b + (-1)·(a·(a·a))` where the Rust AIR wrote `Sub(b, Mul(Mul(a,a),a))` — a different
//! tree, an identical polynomial. Pinning the tree would pin an artifact of the IR's constructor
//! set and would red on any future re-association.
//!
//! What the o1js twin actually depends on is the FOLDED ACCUMULATOR:
//! `VerifierConstraintFolder::assert_zero` does `acc = acc * alpha + C`, so what must agree is the
//! sequence of constraint POLYNOMIALS — their values and their order, not their spelling. That is
//! exactly what cross-verification decides: a proof minted under one AIR verifies under the other
//! iff every `C_i` agrees as a polynomial AND the order agrees. So:
//!
//!   * [`emitted_and_hand_written_airs_cross_verify`] — prove under the emitted descriptor, verify
//!     under the deleted hand-written AIR, and back. This is the equivalence claim.
//!   * [`cross_verification_refuses_a_permuted_fold_order`] — the same four constraints with C1
//!     and C3 swapped must REFUSE, so the test above is known to be sensitive to order rather than
//!     passing because the check is weak. It is the dregg-side twin of
//!     `DreggProofVerify.ts::minaFixtureConstraintsPermuted`.

use dregg_circuit::descriptor_ir2::{Ir2UniAir, TableDef2, TableSem, parse_vm_descriptor2};
use dregg_circuit::plonky3_prover::{DreggStarkConfig, create_config_with_fri_full};
use p3_air::symbolic::{AirLayout, get_symbolic_constraints};
use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use p3_uni_stark::{prove, verify};

type F = BabyBear;

/// The byte-pinned Lean emission — the same string the binary `include_str!`s.
const FIXTURE_JSON: &str = include_str!("../descriptors/by-name/mina-fixture.json");

fn emitted_air() -> Ir2UniAir {
    Ir2UniAir::new(parse_vm_descriptor2(FIXTURE_JSON).expect("golden decodes"))
        .expect("golden is bus-free and single-table")
}

// ===========================================================================
// The DELETED hand-written AIR, verbatim — the differential's expectation.
// ===========================================================================

struct HandWrittenReference;

impl<T: PrimeCharacteristicRing + Sync> BaseAir<T> for HandWrittenReference {
    fn width(&self) -> usize {
        3
    }
    fn num_public_values(&self) -> usize {
        2
    }
    fn max_constraint_degree(&self) -> Option<usize> {
        Some(3)
    }
}

impl<AB: AirBuilder> Air<AB> for HandWrittenReference {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local: Vec<AB::Expr> = main.current_slice().iter().map(|v| (*v).into()).collect();
        let next: Vec<AB::Expr> = main.next_slice().iter().map(|v| (*v).into()).collect();
        let pis: Vec<AB::Expr> = builder
            .public_values()
            .iter()
            .map(|v| (*v).into())
            .collect();

        // C0 — degree 3, the constraint that forces `n_chunks > 1`.
        builder
            .assert_zero(local[1].clone() - local[0].clone() * local[0].clone() * local[0].clone());
        // C1 — is_first_row.
        builder
            .when_first_row()
            .assert_eq(local[2].clone(), pis[0].clone());
        // C2 — is_transition, and the only next-row reference.
        builder
            .when_transition()
            .assert_eq(next[2].clone(), local[2].clone() + local[1].clone());
        // C3 — is_last_row.
        builder
            .when_last_row()
            .assert_eq(local[2].clone(), pis[1].clone());
    }
}

// ===========================================================================
// Traces.
// ===========================================================================

/// The honest trace: `b_i = a_i^3`, `c` the running sum of `b` seeded at `c_0`.
fn honest_trace(degree_bits: usize) -> (RowMajorMatrix<F>, Vec<F>) {
    bent_trace(degree_bits, false)
}

/// `bend = true` replaces `a^3` with `a^2` — the same counter-example
/// `DreggProofVerify.ts::minaFixtureConstraintsBentDegree` keeps live, and the one
/// `MinaFixtureEmit.mina_refuses_bent_degree` refuses in the denotation.
fn bent_trace(degree_bits: usize, bend: bool) -> (RowMajorMatrix<F>, Vec<F>) {
    let n = 1usize << degree_bits;
    let mut values = Vec::with_capacity(n * 3);
    let c0 = F::from_u32(7);
    let mut c = c0;
    for i in 0..n {
        let a = F::from_u32(3 + i as u32);
        let b = if bend { a * a } else { a * a * a };
        values.push(a);
        values.push(b);
        values.push(c);
        c += b;
    }
    let c_last = values[(n - 1) * 3 + 2];
    (RowMajorMatrix::new(values, 3), vec![c0, c_last])
}

/// The same four constraints, C1 and C3 SWAPPED. Every constraint is present and correct; only
/// the fold order moves. Kept so the cross-verification below is known to BITE.
struct PermutedReference;

impl<T: PrimeCharacteristicRing + Sync> BaseAir<T> for PermutedReference {
    fn width(&self) -> usize {
        3
    }
    fn num_public_values(&self) -> usize {
        2
    }
    fn max_constraint_degree(&self) -> Option<usize> {
        Some(3)
    }
}

impl<AB: AirBuilder> Air<AB> for PermutedReference {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local: Vec<AB::Expr> = main.current_slice().iter().map(|v| (*v).into()).collect();
        let next: Vec<AB::Expr> = main.next_slice().iter().map(|v| (*v).into()).collect();
        let pis: Vec<AB::Expr> = builder
            .public_values()
            .iter()
            .map(|v| (*v).into())
            .collect();

        builder
            .assert_zero(local[1].clone() - local[0].clone() * local[0].clone() * local[0].clone());
        // C3 before C1 — the only change.
        builder
            .when_last_row()
            .assert_eq(local[2].clone(), pis[1].clone());
        builder
            .when_transition()
            .assert_eq(next[2].clone(), local[2].clone() + local[1].clone());
        builder
            .when_first_row()
            .assert_eq(local[2].clone(), pis[0].clone());
    }
}

// ===========================================================================
// (1) THE DIFFERENTIAL — emitted ≡ hand-written, as folded polynomials.
// ===========================================================================

#[test]
fn emitted_descriptor_emits_the_same_four_constraints() {
    let air = emitted_air();
    let layout = AirLayout::from_air::<F>(&air);

    let emitted = get_symbolic_constraints::<F, _>(&air, layout);
    let reference = get_symbolic_constraints::<F, _>(&HandWrittenReference, layout);

    assert_eq!(
        emitted.len(),
        4,
        "the Lean descriptor must emit exactly the four constraints the o1js twin folds"
    );
    assert_eq!(
        emitted.len(),
        reference.len(),
        "constraint COUNT diverged: emitted {} vs hand-written {}",
        emitted.len(),
        reference.len()
    );
    // Per-position degree: the cheap structural invariant that survives re-association, and the
    // one that moves `numQuotientChunks` if it drifts.
    for (i, (e, r)) in emitted.iter().zip(reference.iter()).enumerate() {
        assert_eq!(
            e.degree_multiple(),
            r.degree_multiple(),
            "constraint C{i} changed degree: emitted {} vs hand-written {}",
            e.degree_multiple(),
            r.degree_multiple()
        );
    }
}

/// **The equivalence.** A proof minted under the Lean-emitted descriptor is accepted by the
/// deleted hand-written AIR, and vice versa. Cross-verification passes iff every `C_i` agrees as
/// a polynomial AND the fold order agrees — which is exactly, and only, what
/// `bridge/mina-zkapp` depends on.
#[test]
fn emitted_and_hand_written_airs_cross_verify() {
    let config = create_config_with_fri_full(1, 0, 1, 4, 0, 0);
    let (matrix, pis) = honest_trace(3);

    let proof_from_emitted = prove(&config, &emitted_air(), matrix.clone(), &pis);
    verify(&config, &HandWrittenReference, &proof_from_emitted, &pis).expect(
        "a proof minted under the LEAN-EMITTED descriptor was refused by the hand-written AIR — \
         the rewrite changed the constraint system the o1js twin was built against",
    );

    let proof_from_hand = prove(&config, &HandWrittenReference, matrix, &pis);
    verify(&config, &emitted_air(), &proof_from_hand, &pis).expect(
        "a proof minted under the HAND-WRITTEN AIR was refused by the Lean-emitted descriptor",
    );
}

/// The negative that makes the test above meaningful: swap two constraints and cross-verification
/// must refuse. Without this, `emitted_and_hand_written_airs_cross_verify` could be passing
/// because `verify` is blind to the fold order — which would also mean the o1js twin's
/// `minaFixtureConstraintsPermuted` negative is vacuous.
#[test]
fn cross_verification_refuses_a_permuted_fold_order() {
    let config = create_config_with_fri_full(1, 0, 1, 4, 0, 0);
    let (matrix, pis) = honest_trace(3);

    let proof_from_emitted = prove(&config, &emitted_air(), matrix, &pis);
    assert!(
        verify(&config, &PermutedReference, &proof_from_emitted, &pis).is_err(),
        "a PERMUTED fold order accepted the proof — the emission order is not actually load-bearing \
         here, and every claim resting on it (this file's cross-verification, DreggProofVerify.ts's \
         minaFixtureConstraintsPermuted) is vacuous"
    );
}

/// The AIR metadata the emitted fixture JSON's `shape` block carries to the o1js side. A width or
/// PI-count drift here silently re-points the twin at a different AIR.
#[test]
fn emitted_air_metadata_matches_the_reference() {
    let air = emitted_air();
    assert_eq!(<Ir2UniAir as BaseAir<F>>::width(&air), 3);
    assert_eq!(<Ir2UniAir as BaseAir<F>>::num_public_values(&air), 2);

    // The degree is INFERRED from the emitted algebra rather than declared, so assert the
    // inference lands where the hand-written AIR declared it: 3, which is what forces the
    // quotient to split into more than one chunk.
    let deg = get_symbolic_constraints::<F, _>(&air, AirLayout::from_air::<F>(&air))
        .iter()
        .map(|c| c.degree_multiple())
        .max()
        .expect("four constraints");
    assert_eq!(
        deg, 3,
        "the inferred constraint degree moved; `numQuotientChunks` in the emitted fixture moves \
         with it and the o1js side's chunk recomposition is built for 2"
    );
}

// ===========================================================================
// (2) The interpreted AIR really proves and really refuses.
// ===========================================================================

#[test]
fn interpreted_air_proves_and_verifies_the_honest_trace() {
    let air = emitted_air();
    let config = create_config_with_fri_full(1, 0, 1, 4, 0, 0);
    let (matrix, pis) = honest_trace(3);

    let proof = prove(&config, &air, matrix, &pis);
    verify(&config, &air, &proof, &pis)
        .expect("the honest trace must satisfy the Lean-emitted descriptor");
}

/// The negative. Without this the test above passes on an AIR that constrains nothing.
#[test]
fn interpreted_air_refuses_the_bent_cube() {
    let air = emitted_air();
    let config = create_config_with_fri_full(1, 0, 1, 4, 0, 0);
    let (matrix, pis) = bent_trace(3, true);

    // p3's debug prover panics on an unsatisfied constraint rather than minting a proof, so the
    // refusal shows up as either a panic or a verify error. Both are refusals; neither is accept.
    let refused = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let proof = prove(&config, &air, matrix, &pis);
        verify(&config, &air, &proof, &pis).is_err()
    }))
    .unwrap_or(true);

    assert!(
        refused,
        "a trace with b = a^2 was ACCEPTED — C0 constrains nothing and every o1js leg resting on \
         this fixture is vacuous"
    );
}

// ===========================================================================
// (3) FAIL-CLOSED: the kinds the uni-stark route cannot serve are REFUSED.
// ===========================================================================

#[test]
fn new_refuses_every_descriptor_it_cannot_serve() {
    let base = parse_vm_descriptor2(FIXTURE_JSON).expect("golden decodes");

    // A declared table has no bus under uni-stark. Dropping it silently would accept a forgery.
    let mut with_lookup = base.clone();
    with_lookup.tables.push(TableDef2 {
        id: 0,
        name: "poseidon2".to_string(),
        arity: 2,
        sem: TableSem::Poseidon2Chip,
    });
    let err = Ir2UniAir::new(with_lookup).expect_err("a declared table must be refused");
    assert!(err.contains("table"), "unexpected refusal reason: {err}");

    // A column outside the declared width.
    let mut too_wide = base.clone();
    too_wide.trace_width = 1;
    let err = Ir2UniAir::new(too_wide).expect_err("an out-of-range column must be refused");
    assert!(err.contains("column"), "unexpected refusal reason: {err}");

    // A public-input index outside the declared count.
    let mut too_few_pis = base;
    too_few_pis.public_input_count = 1;
    let err =
        Ir2UniAir::new(too_few_pis).expect_err("an out-of-range public input must be refused");
    assert!(
        err.contains("public input"),
        "unexpected refusal reason: {err}"
    );
}
