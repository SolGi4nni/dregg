//! PROBE — `Gated{Hash}` on the `DslP3Air` path was not gated off, it was ERASED.
//!
//! ## The mechanism (read at `circuit/src/dsl/dsl_p3_air.rs`, then measured here)
//!
//! `DslP3Air::eval` dispatches hash constraints on `is_hash(c)`, and `is_hash` matched
//! only TOP-LEVEL hash forms. A `Hash` wrapped in `Gated`/`InvertedGated`/`Squared`
//! therefore:
//!   1. was not counted by `hash_count`, so it got NO Poseidon2 aux block;
//!   2. was not extended into the trace by `extend_trace_with_hash_aux` (same filter);
//!   3. fell to the catch-all `c => builder.assert_zero(eval_expr(c))`, and `eval_expr`
//!      returned `AB::Expr::ZERO` for EVERY hash form.
//!
//! So the emitted constraint was `assert_zero(selector · 0)` — satisfied by every
//! assignment, including `selector = 1`. `check_algebraic` recursed through the wrapper
//! and returned `Ok`, so nothing refused.
//!
//! ## MEASURED 2026-07-30 at `814cccbc4`, BEFORE the repair: 3 passed, 0 failed
//!
//! The three probes below were written to assert the hole and all three passed — green
//! was the failure signal:
//!
//! - `probe_a` — deleting C4 left the p3 AIR bit-identical in width, and the tamper
//!   `forged_nullifier_fails` performed was rejected identically with and without C4.
//!   C4 cost zero columns and zero constraints on that lowering.
//! - `probe_b1` — an ARBITRARY row-0 nullifier proved and verified with `is_leaf = 1`,
//!   i.e. with C4's selector LIVE. That isolates ERASURE from gate-off.
//! - `probe_b2` — a foreign leaf the prover had no preimage for, under a nullifier of
//!   their choosing, with a well-formed 3-entry PI vector: **proved and verified on the
//!   deployed hiding verifier.** A shielded spend of a note the prover never owned.
//!
//! ## What they assert NOW
//!
//! The same three attacks, inverted: each must be REFUSED. Inverted rather than
//! deleted, so the file is the standing adversarial regression for both defects — the
//! erased hash binding (C4) and the unpinned value-theft selector (`is_leaf`). The
//! form-agnostic half of the repair (a lowering that refuses to emit nothing) has its
//! own control at `circuit/tests/p3_lowering_emits_every_hash.rs`.
//!
//! ⚠ STILL OPEN, deliberately not attempted here: the spending key is CARRIED, not
//! BOUND. `KEY0..3` appear in C4 and nowhere else, `OWNER` in C6a and nowhere else, and
//! no constraint relates them — so a fresh key per spend yields a fresh nullifier for
//! the SAME note and a nullifier SET cannot detect the replay. That survives a fully
//! repaired C4 and needs an in-AIR owner derivation no shielded descriptor emits.

use dregg_circuit::dsl::circuit::{ConstraintExpr, DslCircuit};
use dregg_circuit::dsl::dsl_p3_air::{DslP3Air, prove_dsl_zk, verify_dsl_zk};
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_fact;
use dregg_circuit_prove::shielded::spend_circuit::{
    PUBLIC_INPUT_COUNT, ShieldedSpendWitness, col, generate_shielded_spend_trace, pi,
    shielded_spend_circuit, shielded_spend_descriptor,
};

fn test_witness(depth: usize) -> ShieldedSpendWitness {
    let mut siblings = Vec::with_capacity(depth);
    let mut positions = Vec::with_capacity(depth);
    for i in 0..depth {
        positions.push((i % 4) as u8);
        siblings.push([
            BabyBear::new((i as u32) * 5 + 1),
            BabyBear::new((i as u32) * 5 + 2),
            BabyBear::new((i as u32) * 5 + 3),
        ]);
    }
    ShieldedSpendWitness {
        value: BabyBear::new(1_000),
        asset_type: BabyBear::new(42),
        owner: BabyBear::new(0xABCDE),
        randomness: BabyBear::new(0x13579),
        key: [
            BabyBear::new(7),
            BabyBear::new(8),
            BabyBear::new(9),
            BabyBear::new(10),
        ],
        siblings,
        positions,
    }
}

/// A bad trace makes the self-verifying prover EITHER return `Err` OR (in a debug
/// build) panic in p3's `check_constraints` debug assertion. Both are "rejected".
fn proving_rejects(circuit: &DslCircuit, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_dsl_zk(circuit, trace, pis)
    }));
    !matches!(r, Ok(Ok(_)))
}

/// PROBE (a), INVERTED — **C4 must cost something.**
///
/// Two claims, both of which were FALSE before the repair:
///   1. the descriptor carries NO `Gated{Hash}` at all (that shape is now refused
///      outright by `try_from_dsl`, so its presence would take the whole circuit red);
///   2. deleting C4 changes the p3 AIR — it must cost one Poseidon2 aux block. Equal
///      widths mean C4 emits nothing, which is exactly the erasure that shipped.
#[test]
fn probe_a_c4_costs_a_real_aux_block() {
    let full = shielded_spend_descriptor();

    let wrapped: Vec<usize> = full
        .constraints
        .iter()
        .enumerate()
        .filter(|(_, c)| {
            matches!(
                c,
                ConstraintExpr::Gated { .. }
                    | ConstraintExpr::InvertedGated { .. }
                    | ConstraintExpr::Squared { .. }
            ) && contains_hash(c)
        })
        .map(|(i, _)| i)
        .collect();
    assert!(
        wrapped.is_empty(),
        "the shielded-spend descriptor must carry NO wrapped hash (found at {wrapped:?}); \
         a wrapped hash is erased on the DslP3Air path"
    );

    let idx = full
        .constraints
        .iter()
        .position(|c| {
            matches!(c, ConstraintExpr::Hash { output_col, .. } if *output_col == col::NULLIFIER)
        })
        .expect("C4 must be a top-level Hash into col::NULLIFIER");
    let mut without_c4 = full.clone();
    without_c4.constraints.remove(idx);

    let air_with = DslP3Air::try_from_dsl(&DslCircuit::new(full)).expect("descriptor must lower");
    let air_without =
        DslP3Air::try_from_dsl(&DslCircuit::new(without_c4)).expect("stripped must lower");
    let w_with = <DslP3Air as p3_air::BaseAir<p3_baby_bear::BabyBear>>::width(&air_with);
    let w_without = <DslP3Air as p3_air::BaseAir<p3_baby_bear::BabyBear>>::width(&air_without);

    assert!(
        w_with > w_without,
        "C4 must allocate a Poseidon2 aux block ({w_with} vs {w_without}); equal widths \
         are the erasure signature"
    );
}

fn contains_hash(c: &ConstraintExpr) -> bool {
    match c {
        ConstraintExpr::Hash { .. }
        | ConstraintExpr::Hash2to1 { .. }
        | ConstraintExpr::Hash4to1 { .. }
        | ConstraintExpr::Hash3Cap { .. }
        | ConstraintExpr::MerkleHash8 { .. } => true,
        ConstraintExpr::Gated { inner, .. }
        | ConstraintExpr::InvertedGated { inner, .. }
        | ConstraintExpr::Squared { inner } => contains_hash(inner),
        _ => false,
    }
}

/// PROBE (b.1), INVERTED — **an arbitrary nullifier must be refused.**
///
/// Honest depth-4 trace; the `NULLIFIER` cell replaced on every row with an arbitrary
/// felt, and `pi[0]` moved to match so the row-0 boundary HOLDS. Everything else is
/// honest, so C4 is the only constraint left that can refuse.
///
/// Measured before the repair: this PROVED and VERIFIED, with `is_leaf = 1` — i.e. with
/// C4's selector live. That is what distinguishes erasure from a gate that is off.
#[test]
fn probe_b1_arbitrary_nullifier_is_refused() {
    let circuit = shielded_spend_circuit();
    let w = test_witness(4);
    let (mut trace, mut pis) = generate_shielded_spend_trace(&w);

    assert_eq!(
        trace[0][col::IS_LEAF],
        BabyBear::ONE,
        "row 0 carries the armed selector"
    );

    let chosen = BabyBear::new(0x0BADF00D % dregg_circuit::field::BABYBEAR_P);
    assert_ne!(chosen, w.nullifier());
    for row in trace.iter_mut() {
        row[col::NULLIFIER] = chosen;
    }
    pis[pi::NULLIFIER] = chosen;

    assert!(
        proving_rejects(&circuit, &trace, &pis),
        "a nullifier the prover chose must NOT prove — C4 binds it to \
         hash_fact(leaf_commit, key)"
    );
}

/// PROBE (b.2), INVERTED — **the full forgery must be refused.**
///
/// The attack, unchanged from the measurement:
/// - `is_leaf = 0` on EVERY row, which used to disarm C6b (the value-theft tooth) on
///   all three lowerings because the selector was pinned to nothing;
/// - `trace[0][CURRENT]` set to a FOREIGN leaf the prover has no preimage for, with the
///   Merkle chain and root recomputed forward so C3 and C5 still hold;
/// - `trace[0][NULLIFIER]` set to an arbitrary felt;
/// - a WELL-FORMED 3-entry PI vector, so a rejection is attributable to a constraint.
///
/// Measured before the repair: proved AND verified on the deployed hiding verifier.
#[test]
fn probe_b2_foreign_leaf_chosen_nullifier_is_refused() {
    let circuit = shielded_spend_circuit();
    let w = test_witness(4);
    let (trace, honest_pis) = generate_shielded_spend_trace(&w);

    let foreign_leaf = w.leaf_commitment() + BabyBear::new(0xDEAD);

    let mut attack = trace.clone();
    for row in attack.iter_mut() {
        row[col::IS_LEAF] = BabyBear::ZERO;
    }
    let mut cur = foreign_leaf;
    for row in attack.iter_mut() {
        let parent = hash_fact(
            cur,
            &[
                row[col::SIB0],
                row[col::SIB1],
                row[col::SIB2],
                row[col::POSITION],
            ],
        );
        row[col::CURRENT] = cur;
        row[col::PARENT] = parent;
        cur = parent;
    }
    let chosen_nullifier = BabyBear::new(0x00C0FFEE % dregg_circuit::field::BABYBEAR_P);
    for row in attack.iter_mut() {
        row[col::NULLIFIER] = chosen_nullifier;
    }

    let forged_root = attack.last().unwrap()[col::PARENT];
    let attack_pis = vec![chosen_nullifier, forged_root, honest_pis[pi::VALUE_BINDING]];
    assert_eq!(attack_pis.len(), PUBLIC_INPUT_COUNT);

    assert!(
        proving_rejects(&circuit, &attack, &attack_pis),
        "a shielded spend of a note the prover never owned, under a nullifier of their \
         choosing, must NOT prove"
    );

    // And the honest witness still does prove — the refusal is not blanket.
    let proof = prove_dsl_zk(&circuit, &trace, &honest_pis).expect("honest spend must prove");
    verify_dsl_zk(&circuit, &proof, &honest_pis).expect("and verify");
}
