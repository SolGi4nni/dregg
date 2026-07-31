//! PROBE — `Gated{Hash}` on the `DslP3Air` path is not gated off, it is ERASED.
//!
//! ## The mechanism (read at `circuit/src/dsl/dsl_p3_air.rs`, then measured here)
//!
//! `DslP3Air::eval` dispatches hash constraints on `is_hash(c)`, and `is_hash`
//! matches only TOP-LEVEL hash forms (`dsl_p3_air.rs:216-225`). A `Hash` wrapped in
//! `Gated`/`InvertedGated`/`Squared` therefore:
//!   1. is not counted by `hash_count`, so it gets NO Poseidon2 aux block;
//!   2. is not extended into the trace by `extend_trace_with_hash_aux` (same filter);
//!   3. falls to the catch-all `c => builder.assert_zero(eval_expr(c))` (`:609-612`),
//!      and `eval_expr` returns `AB::Expr::ZERO` for EVERY hash form (`:512-522`).
//!
//! So the emitted constraint is `assert_zero(selector · 0)` — satisfied by every
//! assignment, including `selector = 1`. `check_algebraic` recurses through the
//! wrapper (`:177-179`) and returns `Ok`, so nothing refuses.
//!
//! ⚑ Both probes below are GREEN-MEANS-BROKEN. A pass is the failure signal: it is
//! a shielded spend of a note the prover never owned, under a nullifier of their
//! choosing, accepted by the deployed hiding verifier. They are written as
//! assertions of the measured reality so the file is a standing record; when the
//! p3 lowering is repaired they must be inverted, not deleted.
//!
//! ## MEASURED 2026-07-30 at this commit (`cargo test -p dregg-circuit-prove --test
//! gated_hash_erasure_probe`): **3 passed, 0 failed** — i.e. all three holes are real.
//!
//! - `probe_a` — deleting C4 leaves the p3 AIR bit-identical in width, and the tamper
//!   `forged_nullifier_fails` performs is rejected identically with and without C4.
//!   C4 costs zero columns and zero constraints on this lowering.
//! - `probe_b1` — an ARBITRARY row-0 nullifier proved and verified with `is_leaf = 1`,
//!   i.e. with C4's selector LIVE. That isolates ERASURE from gate-off.
//! - `probe_b2` — a foreign leaf the prover has no preimage for, under a nullifier of
//!   their choosing, with a well-formed 3-entry PI vector: **proved and verified on the
//!   deployed hiding verifier.**

use dregg_circuit::dsl::circuit::{ConstraintExpr, DslCircuit};
use dregg_circuit::dsl::dsl_p3_air::{DslP3Air, prove_dsl_zk, verify_dsl_zk};
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_fact;
use dregg_circuit_prove::shielded::spend_circuit::{
    ShieldedSpendWitness, col, generate_shielded_spend_trace, pi, shielded_spend_circuit,
    shielded_spend_descriptor,
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

/// PROBE (a) — **C4 is dead weight on the p3 path.**
///
/// The structural half of the delete-C4 experiment, without editing the source:
/// build the descriptor, strip the `Gated{IS_LEAF, Hash{NULLIFIER, ..}}` push, and
/// show the two descriptors produce the SAME p3 AIR shape — same width, same
/// number of Poseidon2 aux blocks, same trace extension. If C4 contributed any
/// constraint to this lowering, the widths would differ by `POSEIDON2_PERM_AUX_COLS`.
///
/// Measured: identical. C4 costs zero columns and zero constraints on `DslP3Air`.
#[test]
fn probe_a_c4_contributes_nothing_to_the_p3_air() {
    let with_c4 = shielded_spend_descriptor();

    // The C4 push, located structurally (a `Gated` whose inner is a `Hash`).
    let c4_positions: Vec<usize> = with_c4
        .constraints
        .iter()
        .enumerate()
        .filter(|(_, c)| {
            matches!(c, ConstraintExpr::Gated { inner, .. }
                if matches!(**inner, ConstraintExpr::Hash { .. }))
        })
        .map(|(i, _)| i)
        .collect();
    assert_eq!(
        c4_positions.len(),
        1,
        "the shielded-spend descriptor should carry exactly one Gated{{Hash}} (C4)"
    );

    let mut without_c4 = with_c4.clone();
    without_c4.constraints.remove(c4_positions[0]);

    let air_with = DslP3Air::try_from_dsl(&DslCircuit::new(with_c4.clone()))
        .expect("descriptor with C4 must lower");
    let air_without = DslP3Air::try_from_dsl(&DslCircuit::new(without_c4.clone()))
        .expect("descriptor without C4 must lower");

    let w_with = <DslP3Air as p3_air::BaseAir<p3_baby_bear::BabyBear>>::width(&air_with);
    let w_without = <DslP3Air as p3_air::BaseAir<p3_baby_bear::BabyBear>>::width(&air_without);

    assert_eq!(
        w_with, w_without,
        "GREEN IS THE FAILURE SIGNAL: deleting C4 does not change the p3 AIR width, \
         so C4 allocates no Poseidon2 aux block — it is erased, not gated"
    );

    // And the honest trace proves against BOTH airs with the SAME public inputs.
    let w = test_witness(4);
    let (trace, pis) = generate_shielded_spend_trace(&w);
    let c_with = DslCircuit::new(with_c4);
    let c_without = DslCircuit::new(without_c4);
    let p1 = prove_dsl_zk(&c_with, &trace, &pis).expect("honest trace proves with C4");
    verify_dsl_zk(&c_with, &p1, &pis).expect("verifies with C4");
    let p2 = prove_dsl_zk(&c_without, &trace, &pis).expect("honest trace proves without C4");
    verify_dsl_zk(&c_without, &p2, &pis).expect("verifies without C4");

    // And the in-test form of "delete C4, the suite stays green": the tamper
    // `forged_nullifier_fails` performs (bump the row-0 nullifier cell, leave the PI)
    // is rejected IDENTICALLY with and without C4, because only the row-0 boundary
    // bites. That test therefore cannot detect the loss of C4.
    let mut tampered = trace.clone();
    tampered[0][col::NULLIFIER] = tampered[0][col::NULLIFIER] + BabyBear::ONE;
    let rejects_with = proving_rejects(&c_with, &tampered, &pis);
    let rejects_without = proving_rejects(&c_without, &tampered, &pis);
    assert!(
        rejects_with && rejects_without,
        "the boundary rejects in both worlds — so `forged_nullifier_fails` stays green with C4 deleted"
    );
}

/// A bad trace makes the self-verifying prover EITHER return `Err` OR (in a debug
/// build) panic in p3's `check_constraints` debug assertion. Both are "rejected".
fn proving_rejects(circuit: &DslCircuit, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        prove_dsl_zk(circuit, trace, pis)
    }));
    !matches!(r, Ok(Ok(_)))
}

/// PROBE (b.1) — **the nullifier is free even with the gate ON.**
///
/// Honest depth-4 trace, `is_leaf = 1` on row 0 exactly as the honest generator
/// writes it (so C4's selector is LIVE), and the row-0 `NULLIFIER` cell replaced
/// with an arbitrary felt. `pi[0]` is set to the same felt so the row-0 boundary
/// still holds. Everything else is untouched and honest.
///
/// If C4 were enforced, `is_leaf · (hash_fact(current, key) − nullifier) = 0` with
/// `is_leaf = 1` would force the honest nullifier and this must be REJECTED.
///
/// ⚑ Predicted and measured: it PROVES. That isolates defect 1 — erasure — from
/// defect 2 (the unpinned selector), because the selector is 1 here.
#[test]
fn probe_b1_arbitrary_nullifier_proves_with_is_leaf_one() {
    let circuit = shielded_spend_circuit();
    let w = test_witness(4);
    let (mut trace, mut pis) = generate_shielded_spend_trace(&w);

    assert_eq!(
        trace[0][col::IS_LEAF],
        BabyBear::ONE,
        "the honest generator arms C4's selector on row 0"
    );

    let chosen = BabyBear::new(0x0BADF00D % dregg_circuit::field::BABYBEAR_P);
    assert_ne!(
        chosen,
        w.nullifier(),
        "the chosen nullifier must differ from the bound one"
    );
    trace[0][col::NULLIFIER] = chosen;
    pis[pi::NULLIFIER] = chosen;

    let proof = prove_dsl_zk(&circuit, &trace, &pis).expect(
        "GREEN IS THE FAILURE SIGNAL: an arbitrary nullifier proved with is_leaf = 1, \
         so C4 is erased on the DslP3Air path",
    );
    verify_dsl_zk(&circuit, &proof, &pis)
        .expect("and the deployed hiding verifier accepts the forged nullifier");
}

/// PROBE (b.2) — **the full forgery: a foreign leaf under a chosen nullifier.**
///
/// A shielded spend of a note the prover never owned, under a nullifier of their
/// choosing, accepted by the deployed hiding verifier:
///
/// - `is_leaf = 0` on EVERY row (only `Binary{is_leaf}` constrains it; no
///   `BoundaryDef::Fixed{First, IS_LEAF, 1}` exists) — this disarms C6b, the
///   value-theft tooth, on all three lowerings;
/// - `trace[0][CURRENT]` set to a FOREIGN leaf the prover has no preimage for, with
///   the Merkle chain and root recomputed forward so C3 and C5 still hold;
/// - `trace[0][NULLIFIER]` set to an arbitrary felt (C4 erased on p3 regardless of
///   the selector);
/// - PIs `[chosen felt, recomputed root, honest value_binding]`.
///
/// ⚑ Predicted and measured: proves and verifies.
#[test]
fn probe_b2_foreign_leaf_chosen_nullifier_proves_and_verifies() {
    let circuit = shielded_spend_circuit();
    let w = test_witness(4);
    let (trace, honest_pis) = generate_shielded_spend_trace(&w);

    // A leaf the prover never created and has no preimage for.
    let foreign_leaf = w.leaf_commitment() + BabyBear::new(0xDEAD);

    let mut attack = trace.clone();
    // Disarm the value-theft tooth: is_leaf is pinned to nothing.
    for row in attack.iter_mut() {
        row[col::IS_LEAF] = BabyBear::ZERO;
    }
    // Re-chain the whole membership path forward from the foreign leaf.
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
    // A nullifier of the prover's choosing — unrelated to any key or leaf.
    let chosen_nullifier = BabyBear::new(0x00C0FFEE % dregg_circuit::field::BABYBEAR_P);
    attack[0][col::NULLIFIER] = chosen_nullifier;

    let forged_root = attack.last().unwrap()[col::PARENT];
    let attack_pis = vec![chosen_nullifier, forged_root, honest_pis[pi::VALUE_BINDING]];
    assert_eq!(
        attack_pis.len(),
        dregg_circuit_prove::shielded::spend_circuit::PUBLIC_INPUT_COUNT,
        "the PI vector must be well-formed (3 entries), so a rejection could only be \
         attributed to a constraint"
    );

    let proof = prove_dsl_zk(&circuit, &attack, &attack_pis).expect(
        "GREEN IS THE FAILURE SIGNAL: a shielded spend of a note the prover never \
         owned, under a nullifier of their choosing, produced a proof",
    );
    verify_dsl_zk(&circuit, &proof, &attack_pis)
        .expect("and the DEPLOYED hiding verifier accepted it");
}
