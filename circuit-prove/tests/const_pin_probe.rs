//! **FALSIFICATION PROBE — is a `define_const` a PIN?**  ⚑ **ANSWER FLIPPED 2026-07-30: YES.**
//!
//! ## ⚑ THIS FILE'S ASSERTIONS WERE INVERTED, DELIBERATELY, BECAUSE THE SUBSTRATE CHANGED
//!
//! Everything below the divider was TRUE as measured at `63ffb1a08` and is FALSE now. The
//! change is fork commit `fc3c6df` (`emberian/plonky3-recursion`, pinned in the root
//! `Cargo.toml`): `ConstAir`'s preprocessed row went from `[ext_mult, out_idx]` to
//! `[ext_mult, out_idx, value[0..D]]`, and its `eval` gained `D` degree-1 constraints
//! `main.value[i] == prep.value[i]`. A constant's value is now part of the preprocessed
//! commitment, so it is part of the VK fingerprint that hashes it.
//!
//! MEASURED at the new rev, on the two-op lever-(a) shape this file builds:
//!
//! ```text
//!   k=7  vk=b2c625d110375f77bf987da91a0a74f088fc84f5e842d732662fbf63a17d3b80
//!   k=9  vk=a1b0c13065b5ee238effc07a57cf6021053a0d20bf797c6be2c5f70133f41bcb
//! ```
//!
//! The assertions were flipped by writing the opposite claim and re-running, NOT by
//! reshaping the probe until it passed: the circuit construction, the proving path, the
//! `verify_all_tables` calls and the proof-bytes-differ guard are all byte-unchanged.
//!
//! ---
//!
//! `recursion/src/verifier/batch_stark.rs::pin_preprocessed_commit` (lever (a)) pins a
//! child proof's VK identity by
//! ```ignore
//! let expected_const = circuit.alloc_const(val, "VK-identity pin (expected child VK cap)");
//! circuit.connect(target, expected_const);
//! ```
//! An audit READ that shape and claimed it is not a pin at all, because the constant's
//! VALUE lives in `ConstAir`'s MAIN trace (`[value[0..D]]`) while its PREPROCESSED row is
//! only `[ext_mult, out_idx]` — so the value is committed per-PROOF, never as circuit
//! identity, and `ConstAir`'s own header reads "The AIR has no constraints".
//!
//! This probe MEASURES that, rather than reading it. It builds the SAME circuit shape
//! twice — one public input `t`, one constant `k`, `connect(t, k)`, which is literally
//! lever (a)'s shape — with two DIFFERENT constants, proves both under the deployed
//! `DreggRecursionConfig`, and asks:
//!
//!   (a) does `verify_all_tables` accept the second proof, and
//!   (b) is `recursion_vk_fingerprint` — the light client's trust anchor — byte-identical
//!       across the two constants?
//!
//! If BOTH hold, an anchor extracted from the `k = 7` circuit accepts a proof of the
//! `k = 9` circuit, and a `define_const` pins nothing.
//!
//! The audit flagged one caveat: `const_pool` dedups by VALUE
//! (`circuit/src/builder/expression_builder.rs:355`), so the two constants must not
//! otherwise appear in the circuit. `7` and `9` appear nowhere else here.
//!
//! FAST (a two-row circuit): NOT `#[ignore]`.

use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, RecursionVk, create_recursion_config, recursion_vk_fingerprint,
};
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_batch_stark::ProverData;
use p3_circuit::CircuitBuilder;
use p3_circuit_prover::common::{NpoAirBuilder, NpoPreprocessor, get_airs_and_degrees_with_prep};
use p3_circuit_prover::{
    AirVariant, BatchStarkProof, BatchStarkProver, CircuitProverData, ConstraintProfile,
    TablePacking,
};
use p3_field::PrimeCharacteristicRing;
use p3_field::extension::BinomialExtensionField;

const D: usize = 4;
type EF = BinomialExtensionField<P3BabyBear, D>;

/// Build + prove the lever-(a) shape at constant `k`: one public input `t`, one
/// `alloc_const(k)`, `connect(t, k)` — the exact two lines `pin_preprocessed_commit`
/// emits per cap element. The runner is handed `t = k` so the honest witness exists.
///
/// Returns the batch proof, its VK fingerprint, and whether `verify_all_tables` accepted
/// it under its OWN prover.
fn prove_lever_a_shape(k: u32) -> (BatchStarkProof<DreggRecursionConfig>, RecursionVk, bool) {
    let mut cb = CircuitBuilder::<EF>::new();
    let t = cb.alloc_public_input("child VK cap target");
    let expected_const = cb.alloc_const(EF::from_u32(k), "VK-identity pin (expected child VK cap)");
    cb.connect(t, expected_const);
    let circuit = cb.build().expect("the two-op lever-(a) circuit builds");

    let packing = TablePacking::new(4, 4);
    let config = create_recursion_config();
    let preprocessors: Vec<Box<dyn NpoPreprocessor<P3BabyBear>>> = vec![];
    let air_builders: Vec<Box<dyn NpoAirBuilder<DreggRecursionConfig, D>>> = vec![];
    let (airs_degrees, primitive_columns, non_primitive_columns) =
        get_airs_and_degrees_with_prep::<DreggRecursionConfig, EF, D>(
            &circuit,
            &packing,
            &preprocessors,
            &air_builders,
            ConstraintProfile::Standard,
        )
        .expect("table-AIR extraction");
    let (airs, degrees): (Vec<_>, Vec<usize>) = airs_degrees.into_iter().unzip();

    let mut runner = circuit.runner();
    runner
        .set_public_inputs(&[EF::from_u32(k)])
        .expect("one public input");
    let traces = runner.run().expect("witness generation");

    let prover_data = ProverData::from_airs_and_degrees(&config, &airs, &degrees);
    let circuit_prover_data =
        CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);
    let prover = BatchStarkProver::new(config)
        .with_table_packing(packing)
        .with_alu_variant(AirVariant::Baseline);
    let proof = prover
        .prove_all_tables(&traces, &circuit_prover_data)
        .expect("the two-op circuit proves");
    let accepted = prover.verify_all_tables(&proof).is_ok();
    let vk = recursion_vk_fingerprint(&proof);
    (proof, vk, accepted)
}

/// **THE MEASUREMENT.** Two circuits that differ ONLY in the pinned constant. If their VK
/// fingerprints agree and both proofs verify, then an anchor extracted from one accepts
/// the other — `alloc_const` + `connect` is not a pin.
///
/// ⚑ They no longer agree. The verdict line below now asserts the SEPARATION, so it goes
/// red the moment anything puts a constant's value back outside the preprocessed
/// commitment. The probe's construction is unchanged; only the claim is.
#[test]
fn define_const_value_is_in_the_vk_fingerprint() {
    let (proof7, vk7, ok7) = prove_lever_a_shape(7);
    let (proof9, vk9, ok9) = prove_lever_a_shape(9);

    println!("k=7  accepted={ok7}  vk={}", vk7.to_hex());
    println!("k=9  accepted={ok9}  vk={}", vk9.to_hex());
    println!(
        "fingerprints equal: {}   (const value {}IN the VK)",
        vk7 == vk9,
        if vk7 == vk9 { "NOT " } else { "" }
    );

    assert!(ok7, "the k=7 proof must verify under its own prover");
    assert!(ok9, "the k=9 proof must verify under its own prover");

    // The proofs themselves DIFFER — kept from the original probe, where it was what made an
    // IDENTICAL fingerprint meaningful. It still earns its keep in the other direction: it
    // says the two runs really did prove two different things.
    let b7 = postcard::to_allocvec(&proof7).expect("proof postcards");
    let b9 = postcard::to_allocvec(&proof9).expect("proof postcards");
    println!(
        "proof bytes: k=7 {} bytes, k=9 {} bytes, identical: {}",
        b7.len(),
        b9.len(),
        b7 == b9
    );
    assert_ne!(
        b7, b9,
        "the two proofs must be DIFFERENT artifacts (else the probe measured nothing)"
    );

    // THE VERDICT LINE, INVERTED at fork rev `fc3c6df`. It now states the close, so it goes
    // red if a constant's value ever stops reaching the preprocessed commitment again.
    assert_ne!(
        vk7, vk9,
        "THE CLOSE FAILED: two circuits differing ONLY in a constant minted the SAME VK \
         fingerprint, so `alloc_const` pins nothing and an anchor extracted from one accepts \
         the other. Re-read `ConstAir`'s preprocessed layout: the value must be in it."
    );

    // And the forgery statement, spelled out and likewise inverted: a light client anchored
    // on the k=7 circuit REFUSES the k=9 proof, because the constant it "pins" is now part of
    // the identity the anchor names.
    assert_ne!(
        recursion_vk_fingerprint(&proof9),
        vk7,
        "THE CLOSE FAILED: the k=9 proof still presents the k=7 anchor"
    );
}

/// The dedup caveat the audit flagged, measured rather than assumed: two DISTINCT
/// constants really do produce two distinct `Const` rows (the pool did not fold them),
/// so the probe above compared two genuinely different circuits.
#[test]
fn const_pool_did_not_fold_the_two_probe_values() {
    let mut cb = CircuitBuilder::<EF>::new();
    let a = cb.alloc_const(EF::from_u32(7), "seven");
    let b = cb.alloc_const(EF::from_u32(9), "nine");
    let a2 = cb.alloc_const(EF::from_u32(7), "seven again");
    assert_ne!(a, b, "7 and 9 must not share a pooled ExprId");
    assert_eq!(a, a2, "the pool DOES dedup by value (documented behaviour)");
}
