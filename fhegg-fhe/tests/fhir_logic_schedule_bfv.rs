//! Oracle and manifest teeth for the executable fhIR finite-logic backend.
//!
//! Every positive test encrypts with real `fhe.rs` BFV, executes through
//! `fhegg_fhe::fhir::logic_schedule`, decrypts with `fhe.rs`, and compares all
//! live SIMD slots with an independently evaluated plaintext source program.
//! Timings/noise are emitted as measurements; semantic equality and exact
//! operation counts are the assertions.

use std::sync::Arc;

use fhe::bfv::{
    BfvParameters, Ciphertext, Encoding, Plaintext, PublicKey, RelinearizationKey, SecretKey,
};
use fhe_traits::{FheDecoder, FheDecrypter, FheEncoder, FheEncrypter};
use rand_09::rngs::StdRng;
use rand_09::SeedableRng;

use fhegg_fhe::additive::pick_params;
use fhegg_fhe::bfv_lean::{FOLD_DEGREE, FOLD_MODULI};
use fhegg_fhe::fhir::logic_schedule::{
    compile_boolean, BfvCostManifest, BfvLogicEngine, BooleanConstants, BooleanProgram,
    DeclaredEncryptedBit, DeclaredEncryptedNat, LogicBfvError, ResidualEqualityPlan,
};

struct Fixture {
    params: Arc<BfvParameters>,
    sk: SecretKey,
    pk: PublicKey,
    rk: RelinearizationKey,
    rng: StdRng,
}

fn fixture(seed: u64) -> Fixture {
    let params = pick_params(20);
    assert_eq!(params.degree(), FOLD_DEGREE, "degree drifted");
    assert_eq!(params.moduli(), &FOLD_MODULI, "RNS moduli drifted");
    assert_eq!(params.plaintext(), 1_032_193, "plaintext modulus drifted");
    let mut rng = StdRng::seed_from_u64(seed);
    let sk = SecretKey::random(&params, &mut rng);
    let pk = PublicKey::new(&sk, &mut rng);
    let rk = RelinearizationKey::new(&sk, &mut rng).expect("relinearization key");
    Fixture {
        params,
        sk,
        pk,
        rk,
        rng,
    }
}

fn encrypt(fixture: &mut Fixture, slots: &[u64]) -> Ciphertext {
    let plaintext =
        Plaintext::try_encode(slots, Encoding::simd(), &fixture.params).expect("SIMD encode");
    fixture
        .pk
        .try_encrypt(&plaintext, &mut fixture.rng)
        .expect("BFV encrypt")
}

fn decrypt(fixture: &Fixture, ciphertext: &Ciphertext, count: usize) -> Vec<u64> {
    let plaintext = fixture.sk.try_decrypt(ciphertext).expect("BFV decrypt");
    let slots = Vec::<u64>::try_decode(&plaintext, Encoding::simd()).expect("SIMD decode");
    slots[..count].to_vec()
}

fn input(index: usize) -> BooleanProgram {
    BooleanProgram::Input(index)
}

fn balanced_and(programs: &[BooleanProgram]) -> BooleanProgram {
    assert!(!programs.is_empty());
    if programs.len() == 1 {
        return programs[0].clone();
    }
    let middle = programs.len() / 2;
    BooleanProgram::And(
        Box::new(balanced_and(&programs[..middle])),
        Box::new(balanced_and(&programs[middle..])),
    )
}

/// One depth-two formula covers all 16 Boolean environments in one SIMD
/// ciphertext run:
///
/// `(x0 == x1) OR (x2 AND NOT x3)`.
#[test]
fn bfv_boolean_formula_refines_plain_semantics_on_all_inputs() {
    let mut fixture = fixture(0xF1_10_61_C0);
    let engine = BfvLogicEngine::new(&fixture.rk, fixture.params.clone()).expect("logic engine");
    let program = BooleanProgram::Or(
        Box::new(BooleanProgram::Eq(Box::new(input(0)), Box::new(input(1)))),
        Box::new(BooleanProgram::And(
            Box::new(input(2)),
            Box::new(BooleanProgram::Not(Box::new(input(3)))),
        )),
    );
    let compiled = compile_boolean(program.clone());
    let expected_cost = BfvCostManifest {
        logical_input_reads: 4,
        encrypted_constant_reads: 2,
        ciphertext_additions: 3,
        ciphertext_subtractions: 4,
        ciphertext_multiplications: 3,
        relinearizations: 3,
        maximum_multiplicative_depth: 2,
        boundary_zero_decisions: 0,
    };
    assert_eq!(compiled.cost(), &expected_cost);

    let zero = encrypt(&mut fixture, &[0; 16]);
    let one = encrypt(&mut fixture, &[1; 16]);
    let constants = BooleanConstants::from_declared_constants(zero, one);
    let mut encrypted_inputs = Vec::new();
    for variable in 0..4 {
        let slots: Vec<u64> = (0..16)
            .map(|assignment| ((assignment >> variable) & 1) as u64)
            .collect();
        encrypted_inputs.push(DeclaredEncryptedBit::from_declared_canonical(encrypt(
            &mut fixture,
            &slots,
        )));
    }

    let execution = engine
        .execute_boolean(&compiled, &encrypted_inputs, &constants)
        .expect("real BFV Boolean execution");
    assert_eq!(execution.observed_cost, expected_cost);
    assert_eq!(execution.output.multiplicative_depth(), 2);
    let got = decrypt(&fixture, execution.output.ciphertext(), 16);
    let expected: Vec<u64> = (0..16)
        .map(|assignment| {
            let env: Vec<bool> = (0..4)
                .map(|variable| ((assignment >> variable) & 1) != 0)
                .collect();
            u64::from(program.evaluate_plain(&env).expect("complete environment"))
        })
        .collect();
    assert_eq!(got, expected, "BFV formula disagrees on a SIMD environment");

    let noise_bits = unsafe { fixture.sk.measure_noise(execution.output.ciphertext()) }
        .expect("measure output noise");
    let manifest = engine.boolean_manifest(&compiled);
    assert_eq!(manifest.cost, expected_cost);
    println!(
        "BFV_LOGIC_MEASUREMENT {}",
        serde_json::json!({
            "manifest": manifest,
            "simd_environments": 16,
            "elapsed_ns": execution.elapsed.as_nanos(),
            "observed_output_noise_bits": noise_bits,
            "claim_scope": "measured on this run; not a noise or security theorem"
        })
    );
}

/// Eight equality atoms are squared independently (depth one) and then added.
/// The decrypted nonnegative residual is zero exactly on the two SIMD
/// environments in which every equality holds.
#[test]
fn bounded_residual_conjunction_refines_and_emits_no_wrap_certificate() {
    let mut fixture = fixture(0xF1_12_E5_1D);
    let engine = BfvLogicEngine::new(&fixture.rk, fixture.params.clone()).expect("logic engine");
    let pairs: Vec<(usize, usize)> = (0..8).map(|pair| (2 * pair, 2 * pair + 1)).collect();
    let plan = ResidualEqualityPlan {
        pairs,
        input_bound: 9,
    };
    let compiled = engine
        .compile_residual_equalities(plan.clone())
        .expect("8 * 9^2 lies inside centered plaintext window");
    assert_eq!(compiled.certificate().maximum_single_residual, 81);
    assert_eq!(compiled.certificate().maximum_residual_sum, 648);
    assert_eq!(compiled.certificate().centered_window, 516_096);
    let expected_cost = BfvCostManifest {
        logical_input_reads: 16,
        encrypted_constant_reads: 0,
        ciphertext_additions: 7,
        ciphertext_subtractions: 8,
        ciphertext_multiplications: 8,
        relinearizations: 8,
        maximum_multiplicative_depth: 1,
        boundary_zero_decisions: 0,
    };
    assert_eq!(compiled.cost(), &expected_cost);

    // Exact instruction comparison against this interpreter's balanced
    // Booleanization of the SAME eight equalities.  This is not a latency
    // ratio: the residual still needs one private zero decision at egress.
    let boolean_equalities: Vec<BooleanProgram> = (0..8)
        .map(|pair| BooleanProgram::Eq(Box::new(input(2 * pair)), Box::new(input(2 * pair + 1))))
        .collect();
    let boolean_cost = compile_boolean(balanced_and(&boolean_equalities))
        .cost()
        .clone();
    assert_eq!(
        boolean_cost,
        BfvCostManifest {
            logical_input_reads: 16,
            encrypted_constant_reads: 8,
            ciphertext_additions: 16,
            ciphertext_subtractions: 16,
            ciphertext_multiplications: 15,
            relinearizations: 15,
            maximum_multiplicative_depth: 4,
            boundary_zero_decisions: 0,
        }
    );
    assert_eq!(expected_cost.ciphertext_multiplications, 8);
    assert_eq!(boolean_cost.ciphertext_multiplications, 15);
    assert_eq!(expected_cost.maximum_multiplicative_depth, 1);
    assert_eq!(boolean_cost.maximum_multiplicative_depth, 4);

    // Four complete source environments, transposed into BFV SIMD lanes.
    let environments: Vec<Vec<u64>> = vec![
        // all equal
        vec![0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7],
        // one mismatch: residual (3-9)^2 = 36
        vec![0, 0, 1, 1, 2, 2, 3, 9, 4, 4, 5, 5, 6, 6, 7, 7],
        // all equal at a different point
        vec![9, 9, 8, 8, 7, 7, 6, 6, 5, 5, 4, 4, 3, 3, 2, 2],
        // two mismatches: (9-0)^2 + (1-8)^2 = 130
        vec![9, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 1, 8, 7, 7],
    ];
    let mut encrypted_inputs = Vec::new();
    for input_index in 0..16 {
        let lanes: Vec<u64> = environments
            .iter()
            .map(|environment| environment[input_index])
            .collect();
        encrypted_inputs.push(DeclaredEncryptedNat::from_declared_bound(
            encrypt(&mut fixture, &lanes),
            9,
        ));
    }

    let execution = engine
        .execute_residual_equalities(&compiled, &encrypted_inputs)
        .expect("real BFV residual execution");
    assert_eq!(execution.observed_cost, expected_cost);
    let got = decrypt(&fixture, &execution.ciphertext, environments.len());
    let expected: Vec<u64> = environments
        .iter()
        .map(|environment| {
            u64::try_from(
                plan.evaluate_plain(environment)
                    .expect("bounded environment"),
            )
            .expect("certificate keeps residual in u64")
        })
        .collect();
    assert_eq!(
        got, expected,
        "BFV residual sum disagrees with source arithmetic"
    );
    let decrypted_truth: Vec<bool> = got.iter().map(|value| *value == 0).collect();
    let source_truth: Vec<bool> = environments
        .iter()
        .map(|environment| plan.evaluate_plain_truth(environment).unwrap())
        .collect();
    assert_eq!(decrypted_truth, source_truth);
    assert_eq!(source_truth, vec![true, false, true, false]);

    let noise_bits =
        unsafe { fixture.sk.measure_noise(&execution.ciphertext) }.expect("measure output noise");
    let manifest = engine.residual_manifest(&compiled);
    println!(
        "BFV_RESIDUAL_MEASUREMENT {}",
        serde_json::json!({
            "manifest": manifest,
            "no_wrap_certificate": compiled.certificate(),
            "same_workload_balanced_boolean_cost": boolean_cost,
            "comparison_scope": "exact interpreter operations only; residual egress zero decision excluded",
            "simd_environments": environments.len(),
            "elapsed_ns": execution.elapsed.as_nanos(),
            "observed_output_noise_bits": noise_bits,
            "boundary_zero_test_executed": false,
            "claim_scope": "measured on this run; zero-test, noise proof, and security proof excluded"
        })
    );
}

/// The corrected construction refuses before execution when a finite-field sum
/// could leave the positive centered window.  This is the exact obligation the
/// unqualified sum-as-conjunction slogan omits.
#[test]
fn residual_compiler_refuses_a_cancellation_capable_bound() {
    let fixture = fixture(0xF1_12_CA_11);
    let engine = BfvLogicEngine::new(&fixture.rk, fixture.params).expect("logic engine");
    let plan = ResidualEqualityPlan {
        pairs: vec![(0, 1); 4],
        input_bound: 400,
    };
    let error = engine
        .compile_residual_equalities(plan)
        .expect_err("4 * 400^2 exceeds the centered plaintext window");
    assert!(
        matches!(
            error,
            LogicBfvError::ResidualNoWrapRefused {
                maximum_residual_sum: 640_000,
                centered_window: 516_096,
            }
        ),
        "wrong refusal: {error}"
    );
}
