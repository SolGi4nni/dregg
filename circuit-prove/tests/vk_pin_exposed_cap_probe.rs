//! **DESIGN PROBE — does EXPOSING the pinned cap actually bind, or does it move the same
//! non-check one level out?**
//!
//! `const_pin_probe.rs` (`63ffb1a08`) and `vk_pin_lever_a_probe.rs` (`bb42f9800`) MEASURED that
//! lever (a) — `alloc_const(cap) + connect(target, const)` — is not a pin: two circuits differing
//! only in that constant present ONE `recursion_vk_fingerprint`, and baking a foreign cap never
//! reaches the parent's VK core. The designed repair (`ivc_turn_chain`'s module docs, "the exposed
//! VK spine") does not touch any AIR; it routes the pinned cap through the `expose_claim` channel
//! and checks it against a CALLER-HELD anchor.
//!
//! That design rests on three readings of the fork, and this probe MEASURES all three on the
//! deployed `DreggRecursionConfig`, on the SAME two-op lever-(a) shape the earlier probes used —
//! plus ONE extra line, `cb.expose_as_public_output(&[t])`, which is the whole repair in miniature:
//!
//!   **(A) the exposed lane carries the pinned value.** `connect` is one shared witness slot per
//!   class (`ConnectDsu::alloc_witness`), and the fork demotes every later writer of an
//!   already-defined slot to a bus READER (`Op::Public` with `is_dup`), so the class has exactly
//!   ONE `WitnessChecks` send. One send tuple against N reads forces every read — the in-circuit
//!   consumer AND the `expose_claim` lane — to the same value. If that reading is wrong, the
//!   exposure is a second independently-chooseable copy and the design is BROKEN.
//!
//!   **(B) the exposed lane is BOUND, not a free scalar.** `ExposeClaimAir` constrains
//!   `active * (public_value[lane] - v_0) == 0`, and `verify_all_tables` feeds
//!   `proof.non_primitives[].public_values` into `verify_batch` as that AIR's public values. So
//!   editing the host-readable lane in the proof struct must make verification REFUSE.
//!
//!   **(C) the discriminating bit now exists host-side.** `recursion_vk_fingerprint` deliberately
//!   excludes `entry.public_values`, so the two constants STILL fingerprint identically — the
//!   repair does not (and is not claimed to) move the fingerprint. What it moves is the exposed
//!   lane, which a caller-held anchor can compare. This test asserts BOTH halves together, because
//!   the pair is the actual claim: same VK, different bound exposure.
//!
//! ⚑ **(C) IS INVERTED as of fork rev `fc3c6df` — read this before the bullet above.** The two
//! constants no longer fingerprint identically. The bullet's stated REASON is still true and is not
//! what moved: `entry.public_values` remain excluded, and `PublicAir`'s value columns are still
//! main-trace only. What changed is that `ConstAir`'s preprocessed row now carries the constant's
//! VALUE (`[ext_mult, out_idx, value[0..D]]`) under a `main.value == prep.value` constraint, so a
//! constant is circuit identity and the fingerprint — which hashes `preprocessed_commitment` —
//! separates them. MEASURED here: `k=7 vk=8cbc73fe…5978`, `k=9 vk=ddd33490…ab1e`, exposed `[7]` vs
//! `[9]`. The assertion was flipped by writing the opposite claim and re-running; the circuit, the
//! proving path and the (A)/(B) halves are byte-unchanged.
//!
//! So the design's claim is now measured in a STRONGER form than it was written for: the
//! discriminating bit exists in TWO independent places — the host-readable exposed lane (this
//! file's channel) and the fingerprint itself (the const binding). Both are asserted, so neither
//! can rot silently behind the other.
//!
//! FAST (a three-op circuit): NOT `#[ignore]`.
//!
//! ⚠ SCOPE. This measures the CHANNEL, not the deployed fold. It does not exercise a real child
//! cap, the aggregation hook, or the spine's Poseidon2 fold. ⚑ The sentence that stood here added
//! "those need the fork plumbing change (`child_vk_cap_targets` on `VerifierCircuitResult`, widened
//! expose hooks) that the design names and that is NOT built" — that plumbing IS built, at
//! `e1d8ab9bc` plus fork rev `4aead01`. A green run here still says only that the mechanism behaves
//! as read on a three-op shape; the deployed fold is exercised elsewhere.

use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, RecursionVk, create_recursion_config, recursion_vk_fingerprint,
};
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_batch_stark::ProverData;
use p3_circuit::CircuitBuilder;
use p3_circuit_prover::common::{NpoAirBuilder, NpoPreprocessor, get_airs_and_degrees_with_prep};
use p3_circuit_prover::{
    AirVariant, BatchStarkProof, BatchStarkProver, CircuitProverData, ConstraintProfile,
    TablePacking, expose_claim_air_builders, expose_claim_preprocessor,
};
use p3_field::PrimeCharacteristicRing;
use p3_field::extension::BinomialExtensionField;

const D: usize = 4;
type EF = BinomialExtensionField<P3BabyBear, D>;

/// The lever-(a) shape at constant `k`, PLUS the repair's one new line.
///
/// `t` stands in for a child's VK-cap target (in the deployed fold it is one lane of
/// `CommonDataTargets::preprocessed_commit_observation_targets`, allocated by
/// `MerkleCapTargets::new`); `k` stands in for the expected cap value `pin_preprocessed_commit`
/// bakes. `connect(t, k)` is the deployed pin verbatim. `expose_as_public_output(&[t])` is the
/// repair.
fn prove_exposed_lever_a(k: u32) -> (BatchStarkProof<DreggRecursionConfig>, RecursionVk, bool) {
    let mut cb = CircuitBuilder::<EF>::new();
    // The deployed recursion config enables this op in `prepare_circuit_for_verification`; here the
    // circuit is built by hand, so enable it by hand with the SAME trace generator.
    cb.enable_expose_claim::<P3BabyBear>(
        p3_circuit::ops::generate_expose_claim_trace::<P3BabyBear, EF>,
    );
    let t = cb.alloc_public_input("child VK cap target");
    let expected_const = cb.alloc_const(EF::from_u32(k), "VK-identity pin (expected child VK cap)");
    cb.connect(t, expected_const);
    // THE REPAIR, in one line: surface the pinned slot through the bound `expose_claim` channel.
    cb.expose_as_public_output(&[t]);
    let circuit = cb.build().expect("the lever-(a)+expose circuit builds");

    let packing = TablePacking::new(4, 4);
    let config = create_recursion_config();
    let preprocessors: Vec<Box<dyn NpoPreprocessor<P3BabyBear>>> =
        vec![expose_claim_preprocessor::<P3BabyBear>()];
    let air_builders: Vec<Box<dyn NpoAirBuilder<DreggRecursionConfig, D>>> =
        expose_claim_air_builders::<DreggRecursionConfig, D>();
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
    let cpd = CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);
    let mut prover = BatchStarkProver::new(config)
        .with_table_packing(packing)
        .with_alu_variant(AirVariant::Baseline);
    prover.register_expose_claim_table::<D>();
    let proof = prover
        .prove_all_tables(&traces, &cpd)
        .expect("the lever-(a)+expose circuit proves");
    let accepted = prover.verify_all_tables(&proof).is_ok();
    let vk = recursion_vk_fingerprint(&proof);
    (proof, vk, accepted)
}

/// The host-readable exposed lanes: `non_primitives[expose_claim].public_values`.
fn exposed_lanes(proof: &BatchStarkProof<DreggRecursionConfig>) -> Vec<P3BabyBear> {
    proof
        .non_primitives
        .iter()
        .find(|e| e.op_type.as_str() == "expose_claim")
        .map(|e| e.public_values.clone())
        .expect("the circuit carries an expose_claim table")
}

/// Re-verify a (possibly mutated) proof under a freshly-registered deployed prover.
fn accepts(proof: &BatchStarkProof<DreggRecursionConfig>) -> bool {
    let mut prover = BatchStarkProver::new(create_recursion_config())
        .with_table_packing(TablePacking::new(4, 4))
        .with_alu_variant(AirVariant::Baseline);
    prover.register_expose_claim_table::<D>();
    prover.verify_all_tables(proof).is_ok()
}

/// **(A) + (C).** Two circuits differing ONLY in the pinned constant. The EXPOSED lanes must
/// differ and equal the pinned constants — that half is the design's claim and is unchanged.
///
/// ⚑ **(C) IS INVERTED at fork rev `fc3c6df`.** It used to assert the fingerprints STILL agree,
/// because the repair was not supposed to move the VK. They no longer agree, and the reason is a
/// substrate change rather than anything about this channel: a constant's value is now a
/// PREPROCESSED column of `ConstAir`, and `recursion_vk_fingerprint` hashes
/// `preprocessed_commitment`.
///
/// **The old comment's stated reason is still true and is NOT what moved.** `public_values` are
/// still excluded from the fingerprint by design, and `PublicAir`'s value columns are still
/// main-trace only. What changed is that a CONSTANT stopped being witness-shaped data and became
/// circuit identity, which is what it always was semantically.
///
/// So this probe now measures a STRONGER pair than it was written for: the discriminating
/// information exists in BOTH places — in the host-readable exposed lane (this file's design) and
/// in the fingerprint itself (the const binding). The two are independent, and asserting both
/// keeps either from silently rotting.
#[test]
fn exposing_the_pinned_slot_puts_the_constant_where_a_caller_can_check_it() {
    let (proof7, vk7, ok7) = prove_exposed_lever_a(7);
    let (proof9, vk9, ok9) = prove_exposed_lever_a(9);
    let lanes7 = exposed_lanes(&proof7);
    let lanes9 = exposed_lanes(&proof9);

    println!(
        "k=7  accepted={ok7}  vk={}  exposed={lanes7:?}",
        vk7.to_hex()
    );
    println!(
        "k=9  accepted={ok9}  vk={}  exposed={lanes9:?}",
        vk9.to_hex()
    );
    println!("fingerprints equal: {}", vk7 == vk9);
    println!("exposed lanes equal: {}", lanes7 == lanes9);

    assert!(ok7 && ok9, "both proofs must verify under their own prover");

    // (A) the exposed lane IS the pinned value — the exposure reads the `connect`-shared slot,
    // not some second copy a prover could set independently.
    assert!(
        !lanes7.is_empty() && !lanes9.is_empty(),
        "the expose_claim table must surface at least the one lane that was exposed"
    );
    assert_eq!(
        lanes7[0],
        P3BabyBear::from_u32(7),
        "BROKEN: the exposed lane is not the pinned constant — `connect` did not give the \
         expose_claim read the same witness slot the pin writes, and the design's single-creator \
         reading is wrong"
    );
    assert_eq!(
        lanes9[0],
        P3BabyBear::from_u32(9),
        "BROKEN: the exposed lane is not the pinned constant (k=9)"
    );

    // (C) INVERTED at fork rev `fc3c6df`: the fingerprint is no longer blind to the constant,
    // because the constant is now a preprocessed column and the fingerprint hashes the
    // preprocessed commitment. `public_values` remain excluded — that is unchanged and is not
    // what moved.
    assert_ne!(
        vk7, vk9,
        "THE CONST BINDING REGRESSED: two circuits differing only in a pinned constant minted the \
         SAME fingerprint again. `ConstAir`'s preprocessed row must carry the value — see \
         `const_pin_probe.rs`, which asserts the same separation on the bare shape."
    );
    // ... and the exposure is where the difference now lives.
    assert_ne!(
        lanes7, lanes9,
        "BROKEN: the exposed lanes agree across two different pinned constants, so exposing the \
         cap moved the same non-check one level out and the design must be abandoned"
    );
}

/// **(B) THE LOAD-BEARING HALF.** Edit the host-readable exposed lane in the proof struct and the
/// deployed verifier must REFUSE. If it accepts, `non_primitives[].public_values` is a free scalar
/// a forger rewrites at will, and exposing the cap would bind nothing at all.
#[test]
fn a_tampered_exposed_lane_is_refused_by_the_deployed_verifier() {
    let (proof, _vk, ok) = prove_exposed_lever_a(7);
    assert!(ok, "the honest proof must verify");

    // `BatchStarkProof` is not `Clone` but IS postcard serde (the wire the light client already
    // ships it over — `WholeChainProofBytes::root_proof`), so the forgery is minted the same way a
    // real one would be: decode, edit the host-readable lane, re-present.
    let bytes = postcard::to_allocvec(&proof).expect("proof postcards");
    let mut tampered: BatchStarkProof<DreggRecursionConfig> =
        postcard::from_bytes(&bytes).expect("a postcarded proof decodes");
    let entry = tampered
        .non_primitives
        .iter_mut()
        .find(|e| e.op_type.as_str() == "expose_claim")
        .expect("the circuit carries an expose_claim table");
    assert!(!entry.public_values.is_empty(), "one exposed lane");
    let before = entry.public_values[0];
    entry.public_values[0] = before + P3BabyBear::ONE;
    let after = entry.public_values[0];
    println!("tampered exposed lane: {before:?} -> {after:?}");

    // THE CONTROL, and it must be the ROUND-TRIPPED proof, not the original: otherwise a serde
    // round-trip that silently corrupts anything would read as "the tamper was caught".
    let round_tripped: BatchStarkProof<DreggRecursionConfig> =
        postcard::from_bytes(&bytes).expect("a postcarded proof decodes");
    assert!(
        accepts(&round_tripped),
        "NOT ATTRIBUTABLE: the UNTOUCHED round-tripped proof does not verify, so a rejection below \
         says nothing about the edited lane"
    );
    assert!(
        !accepts(&tampered),
        "BROKEN: the deployed verifier ACCEPTED a proof whose exposed lane was edited — \
         `active * (public_value - v_0) == 0` is not reaching the host-supplied public values, so \
         the expose_claim channel binds nothing and the designed repair is void"
    );
}
