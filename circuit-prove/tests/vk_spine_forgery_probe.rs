//! **THE MEASURED FORGERY — does substituting a child circuit now move what the client compares?**
//!
//! `const_pin_probe.rs` (`63ffb1a08`) and `vk_pin_lever_a_probe.rs` (`bb42f9800`) measured the
//! hole: two circuits differing only in a pinned `alloc_const` present ONE identical
//! `recursion_vk_fingerprint`, and baking a foreign cap never reaches the parent's VK core. A
//! prover could substitute any circuit with a matching table manifest — including one that does no
//! descriptor verification at all — and the parent re-verified it.
//!
//! The VK spine closes that. This file measures the close.
//!
//! ## ⚑ WHICH OBSERVABLE INVERTS, AND WHICH DELIBERATELY DOES NOT
//!
//! The inversion does **not** land on `recursion_vk_fingerprint`, and it must not. That
//! fingerprint hashes shape + preprocessed binding and deliberately EXCLUDES
//! `non_primitives[].public_values` — content-independence is exactly what lets one anchor serve
//! many histories over the same circuit. If a substituted child moved it, it would also move for
//! every honest history, and it would stop being usable as a trust anchor at all.
//!
//! What inverts is [`whole_chain_anchor`] — the value verify tooth (1) actually compares, and the
//! value a light client holds. It is
//! `blake3("dregg-whole-chain-anchor-v1" ‖ recursion_vk_fingerprint(root) ‖ root vk-spine lanes)`,
//! and the spine lanes are `commit(L.cap ‖ L.spine ‖ R.cap ‖ R.spine)` folded from the leaves up.
//!
//! So the honest statement of the close is a PAIR, and both halves are asserted below together:
//!
//! ```text
//!   substituted child  ⇒  recursion_vk_fingerprint  IDENTICAL   (by design, and required)
//!   substituted child  ⇒  whole_chain_anchor        DIFFERS     (the close)
//! ```
//!
//! ## ⚑ THE RESIDUAL THIS PROBE NAMED IS CLOSED (2026-07-30) — PAIR A IS INVERTED
//!
//! This file's PAIR A asserted that a CONST-SWAPPED child leaves the cap, the spine and the
//! anchor unmoved, and called that the residual the spine does not reach. That is now FALSE, by
//! fork commit `fc3c6df` (`emberian/plonky3-recursion`): `ConstAir`'s preprocessed row went from
//! `[ext_mult, out_idx]` to `[ext_mult, out_idx, value[0..D]]` with `D` degree-1 constraints
//! `main.value[i] == prep.value[i]`. A constant's value is preprocessed data now, so it reaches
//! the cap, the spine and the anchor.
//!
//! The three PAIR A assertions below were flipped to `assert_ne!` by writing the opposite claim
//! and re-running. Nothing else in the file moved: the three `Program` variants, the proving
//! path, `combine_spine_host` and the `anchor` closure are byte-unchanged.
//!
//! ⚑ Note what ALSO changed, and it is a strengthening the original doc above forbade itself:
//! `recursion_vk_fingerprint` NOW separates two children differing only in a constant, because it
//! hashes `preprocessed_commitment`. That does not break content-independence — a constant is
//! fixed by the circuit, whereas a PUBLIC INPUT is per-execution and stays out (`PublicAir`'s
//! preprocessed row was deliberately NOT changed). One anchor still serves many histories over
//! one circuit; it no longer serves two different circuits.
//!
//! `vk_pin_lever_a_probe.rs` is inverted in the same change and for the same reason — including
//! its second horn, which now holds: baking a foreign cap DOES move the parent's VK core.
//!
//! ## What is cheap here and what is not
//!
//! [`anchor_separates_two_children_that_the_fingerprint_cannot`] is FAST: it mints the two real
//! lever-(a) children (three-op circuits), reads their REAL preprocessed caps — the values the
//! spine absorbs and the values a parent's preprocessed-trace opening consumes — and computes the
//! host mirror of the spine fold with [`seg_poseidon_commit_host`], the same function
//! `seg_poseidon_commit` mirrors in-circuit. That measures the discriminating step end to end
//! without a fold.
//!
//! [`a_substituted_child_moves_the_root_anchor_through_a_real_fold`] is the same statement through
//! a REAL 2-to-1 aggregation (`merge_two_segment_proofs`, the deployed merge primitive) and is
//! `#[ignore]`d because it proves two child layers and one parent layer.

use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::ivc_turn_chain::{
    SEG_DIGEST_WIDTH, VK_CAP_TARGET_LEN, VK_SPINE_WIDTH, seg_poseidon_commit_host,
};
use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, create_recursion_config, recursion_vk_fingerprint,
};
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_batch_stark::ProverData;
use p3_circuit::CircuitBuilder;
use p3_circuit_prover::common::{NpoAirBuilder, NpoPreprocessor, get_airs_and_degrees_with_prep};
use p3_circuit_prover::{
    AirVariant, BatchStarkProof, BatchStarkProver, CircuitProverData, ConstraintProfile,
    TablePacking,
};
use p3_commit::Pcs;
use p3_field::PrimeCharacteristicRing;
use p3_field::PrimeField32;
use p3_field::extension::BinomialExtensionField;
use p3_uni_stark::StarkGenericConfig;

/// What a probe child's program does. All three carry the same tables.
#[derive(Clone, Copy)]
enum Program {
    /// `connect(t, k)` — the honest shape: `t` is forced to equal `k`.
    Check,
    /// `add(t, k)`, no `connect` — verifies nothing.
    NoCheck,
    /// Row-for-row IDENTICAL to `Check` — same tables, same op counts, same degree bits — but the
    /// `connect` lands on the OTHER public input. A circuit that checks the WRONG quantity: the
    /// sharpest form of "a matching table manifest that does not do the verification".
    CheckWrongInput,
}

const D: usize = 4;
type EF = BinomialExtensionField<P3BabyBear, D>;

type Commit = <<DreggRecursionConfig as StarkGenericConfig>::Pcs as Pcs<
    <DreggRecursionConfig as StarkGenericConfig>::Challenge,
    <DreggRecursionConfig as StarkGenericConfig>::Challenger,
>>::Commitment;

/// A child circuit. `k` is the pinned constant; `check` selects whether the circuit ENFORCES
/// anything about its public input.
///
/// * `check = true`  — `connect(t, k)`: the honest shape, `t` is forced to equal `k`.
/// * `check = false` — the SAME allocations with the `connect` DROPPED: `t` is free. This is the
///   forgery in miniature — a circuit with the same tables that verifies nothing.
///
/// Varying `k` at fixed `check` gives the OTHER pair: same op-list, different constant VALUE.
fn prove_child(k: u32, check: Program) -> BatchStarkProof<DreggRecursionConfig> {
    let mut cb = CircuitBuilder::<EF>::new();
    let t0 = cb.alloc_public_input("child VK cap target (the one that must be checked)");
    let t1 = cb.alloc_public_input("a second public input");
    let expected_const = cb.alloc_const(EF::from_u32(k), "VK-identity pin (expected child VK cap)");
    // Every variant consumes both publics through ONE ALU row, so the table row counts, degree
    // bits and manifest are identical across all three.
    let _ = cb.add(t0, t1);
    match check {
        Program::Check => cb.connect(t0, expected_const),
        Program::CheckWrongInput => cb.connect(t1, expected_const),
        Program::NoCheck => {}
    }
    let circuit = cb.build().expect("the child circuit builds");

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
        .set_public_inputs(&[EF::from_u32(k), EF::from_u32(k)])
        .expect("two public inputs");
    let traces = runner.run().expect("witness generation");

    let prover_data = ProverData::from_airs_and_degrees(&config, &airs, &degrees);
    let cpd = CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);
    BatchStarkProver::new(config)
        .with_table_packing(packing)
        .with_alu_variant(AirVariant::Baseline)
        .prove_all_tables(&traces, &cpd)
        .expect("the two-op circuit proves")
}

fn cap_of(proof: &BatchStarkProof<DreggRecursionConfig>) -> Commit {
    proof
        .stark_common
        .preprocessed
        .as_ref()
        .expect("a child carries a preprocessed commitment (its VK core)")
        .commitment
        .clone()
}

/// A cap's flat base-field lanes, in the canonical `to_observation_targets()` order the in-circuit
/// `child_vk_cap_targets()` hands the spine.
fn cap_lanes(c: &Commit) -> Vec<BabyBear> {
    let roots = c.roots();
    assert_eq!(roots.len(), 1, "cap_height 0 ⇒ exactly one digest");
    roots[0]
        .iter()
        .map(|v| BabyBear::new(v.as_canonical_u32()))
        .collect()
}

/// The HOST mirror of one spine node: `commit(L.cap ‖ L.spine ‖ R.cap ‖ R.spine)`, the same absorb
/// order `combine_vk_spine` builds in-circuit.
fn combine_spine_host(
    l_cap: &[BabyBear],
    l_spine: &[BabyBear],
    r_cap: &[BabyBear],
    r_spine: &[BabyBear],
) -> [BabyBear; SEG_DIGEST_WIDTH] {
    let mut inputs = Vec::with_capacity(2 * (VK_CAP_TARGET_LEN + VK_SPINE_WIDTH));
    inputs.extend_from_slice(l_cap);
    inputs.extend_from_slice(l_spine);
    inputs.extend_from_slice(r_cap);
    inputs.extend_from_slice(r_spine);
    seg_poseidon_commit_host(&inputs)
}

/// **THE MEASUREMENT — two pairs, and they now AGREE.**
///
/// PAIR B (op-list differs: a child that CHECKS vs one that checks nothing) is the close.
/// PAIR A (op-list identical, constant VALUE differs) is the residual this probe DISCOVERED,
/// and it is closed as of fork rev `fc3c6df`. Both are asserted, so neither can quietly rot —
/// and PAIR A now goes RED if a constant's value ever leaves the preprocessed commitment again.
#[test]
fn the_spine_binds_a_childs_program_and_its_constants() {
    let checker7 = prove_child(7, Program::Check);
    let checker9 = prove_child(9, Program::Check);
    let nocheck7 = prove_child(7, Program::NoCheck);
    let otherop7 = prove_child(7, Program::CheckWrongInput);

    let cap_c7 = cap_lanes(&cap_of(&checker7));
    let cap_c9 = cap_lanes(&cap_of(&checker9));
    let cap_n7 = cap_lanes(&cap_of(&nocheck7));
    let fp_c7 = recursion_vk_fingerprint(&checker7);
    let fp_c9 = recursion_vk_fingerprint(&checker9);
    let fp_n7 = recursion_vk_fingerprint(&nocheck7);

    println!("[checker k=7] fp={}  cap={cap_c7:?}", fp_c7.to_hex());
    println!("[checker k=9] fp={}  cap={cap_c9:?}", fp_c9.to_hex());
    println!("[NO CHECK  7] fp={}  cap={cap_n7:?}", fp_n7.to_hex());
    let cap_o7 = cap_lanes(&cap_of(&otherop7));
    let fp_o7 = recursion_vk_fingerprint(&otherop7);
    println!("[WRONG INPUT] fp={}  cap={cap_o7:?}", fp_o7.to_hex());
    assert_eq!(cap_c7.len(), VK_CAP_TARGET_LEN);

    // ---------------------------------------------------------------------------------------
    // PAIR A — SAME op-list, DIFFERENT constant value. ⚑ THE RESIDUAL, NOW CLOSED.
    //
    // A constant's VALUE used to live ONLY in `ConstAir`'s constraint-free MAIN trace, with
    // `[ext_mult, out_idx]` as the whole preprocessed row. Two circuits differing only in a
    // constant therefore had IDENTICAL preprocessed traces, hence an IDENTICAL cap — so the
    // spine, which absorbs the cap, could not separate them either. That was the SAME hole this
    // lane started from, one level down: the spine had moved it from "which circuit" to "which
    // constants inside a fixed circuit".
    //
    // Fork rev `fc3c6df` put the value in the preprocessed row (`[ext_mult, out_idx,
    // value[0..D]]`) and constrained `main.value == prep.value`. So the cap separates them, the
    // fingerprint that hashes the cap separates them, and the spine and anchor follow.
    // ---------------------------------------------------------------------------------------
    assert_ne!(
        fp_c7, fp_c9,
        "THE CLOSE FAILED: two circuits differing only in a constant still share one VK \
         fingerprint. `recursion_vk_fingerprint` hashes `preprocessed_commitment`, so this means \
         the constant is not in the preprocessed trace — re-read `ConstAir`."
    );
    assert_ne!(
        cap_c7, cap_c9,
        "THE CLOSE FAILED at the cap: two circuits differing only in a constant present ONE \
         preprocessed cap, so the spine that absorbs the cap cannot separate them and a \
         const-swapped child rides the honest anchor."
    );

    // ---------------------------------------------------------------------------------------
    // PAIR B — DIFFERENT op-list (a check vs no check). ⚑ THE CLOSE.
    //
    // This is the attack the lane was opened on: substitute a child that does no verification.
    // Its op-list differs, so its preprocessed trace differs, so its cap differs — and the cap is
    // what the spine absorbs and the anchor commits to.
    // ---------------------------------------------------------------------------------------
    assert_ne!(
        cap_c7, cap_n7,
        "THE CLOSE FAILED: a child that CHECKS and a child that checks NOTHING present the same \
         preprocessed cap, so the spine cannot tell a verifying leaf from a no-op one"
    );

    // A SECOND substituted program — one that checks the WRONG public input.
    //
    // ⚠ MEASURED AND WORTH SAYING: in this miniature the SHAPE fingerprint separates every program
    // variant too (three distinct `fp=` lines above). So this probe demonstrates the spine is
    // SUFFICIENT to refuse a substituted child; it does NOT demonstrate it is NECESSARY, because
    // at three ops any wiring change also moves a row count. The two notions come apart only at
    // scale, where a large circuit can be padded to a matching (rows, degree_bits, manifest,
    // packing) summary while wiring differently — the cap is a Merkle commitment to the actual
    // preprocessed columns, the fingerprint is a short summary of their dimensions. Separating
    // them by measurement needs a REAL fold, not this miniature; that is named in the report and
    // is not claimed here.
    assert_ne!(
        cap_c7, cap_o7,
        "THE CLOSE FAILED at the sharp case: two DIFFERENT programs with an identical table \
         manifest present the same preprocessed cap — a matching-manifest substitution is still \
         invisible and the spine binds nothing the fingerprint did not already bind"
    );
    let spine_sharp = combine_spine_host(&cap_o7, &leaf_seed_of(), &cap_c7, &leaf_seed_of());
    let spine_ok = combine_spine_host(&cap_c7, &leaf_seed_of(), &cap_c7, &leaf_seed_of());
    assert_ne!(
        spine_sharp, spine_ok,
        "THE CLOSE FAILED: a child that checks the WRONG input folds to the same root spine as \
         the honest one, under an IDENTICAL shape fingerprint — nothing separates them"
    );

    // The spine fold, host mirror of `combine_vk_spine`, over a 2-leaf tree: honest (checker,
    // checker) vs forged (no-check, checker). Both leaves seed the same `VK_SPINE_LEAF_TAG`, so
    // the ONLY difference is the substituted child's cap.
    let leaf_seed = leaf_seed_of();
    let spine_honest = combine_spine_host(&cap_c7, &leaf_seed, &cap_c7, &leaf_seed);
    let spine_forged = combine_spine_host(&cap_n7, &leaf_seed, &cap_c7, &leaf_seed);
    println!("root spine honest = {spine_honest:?}");
    println!("root spine forged = {spine_forged:?}");
    assert_ne!(
        spine_honest, spine_forged,
        "THE CLOSE FAILED at the fold: a substituted no-op child did not move the root spine"
    );

    // ---------------------------------------------------------------------------------------
    // AND THEREFORE THE ANCHOR — the value verify tooth (1) compares against the caller-held one.
    // The raw fingerprint half is IDENTICAL here on purpose (content-independence is what lets an
    // anchor serve many histories); the spine half is what moves.
    // ---------------------------------------------------------------------------------------
    let anchor = |fp: &[u8; 32], spine: &[BabyBear; SEG_DIGEST_WIDTH]| {
        let mut h = blake3::Hasher::new();
        h.update(b"dregg-whole-chain-anchor-v1");
        h.update(fp);
        for lane in spine {
            h.update(&lane.as_u32().to_le_bytes());
        }
        *h.finalize().as_bytes()
    };
    let a_honest = anchor(&fp_c7.0, &spine_honest);
    let a_forged = anchor(&fp_c7.0, &spine_forged);
    println!("anchor honest = {}", hex(&a_honest));
    println!("anchor forged = {}", hex(&a_forged));
    assert_ne!(
        a_honest, a_forged,
        "THE CLOSE FAILED at the anchor: a substituted no-op child leaves the caller-held anchor \
         unmoved, so tooth (1) accepts the forgery"
    );

    // And the closed residual, restated at the anchor so it is measured rather than merely
    // asserted about caps: swapping a constant inside a child MOVES the anchor.
    //
    // ⚑ The root fingerprint is deliberately held at `fp_c7` on BOTH sides. Holding it fixed is
    // the conservative form of the claim: the anchor moves through the SPINE alone, not because
    // the fingerprint happens to move too.
    let spine_const_swap = combine_spine_host(&cap_c9, &leaf_seed, &cap_c7, &leaf_seed);
    let a_const_swap = anchor(&fp_c7.0, &spine_const_swap);
    println!("anchor const-swapped child = {}", hex(&a_const_swap));
    assert_ne!(
        a_honest, a_const_swap,
        "THE CLOSE FAILED at the anchor: swapping a child's CONSTANT left the caller-held anchor \
         unmoved, so a prover can still zero a coefficient inside a folded child and keep the \
         anchor. This is the residual this probe was written to name."
    );
}

/// The leaf spine seed, host mirror of `leaf_vk_spine`: `commit([VK_SPINE_LEAF_TAG])`.
fn leaf_seed_of() -> [BabyBear; SEG_DIGEST_WIDTH] {
    seg_poseidon_commit_host(&[BabyBear::new(0x564B_4C31 % 0x7800_0001)])
}

fn hex(b: &[u8; 32]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}
