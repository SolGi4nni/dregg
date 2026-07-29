//! **The dregg-side emitter for the ROOT batch's per-instance AIR closing equality** — load
//! the REAL committed whole-history root proof, re-derive its Fiat-Shamir challenges from
//! p3's OWN transcript, and emit every field an external (o1js) verifier needs to evaluate
//! dregg's ACTUAL root AIR on dregg's ACTUAL root proof, in CANONICAL form.
//!
//! ```text
//!   cargo build -p dregg-circuit-prove --release --bin root_air_instance
//!   ./target/release/root_air_instance [out.json]
//! ```
//!
//! ## Why this exists
//!
//! `circuit/src/bin/mina_stark_fixture.rs` does this job for a `p3_uni_stark::Proof` over a
//! 3-column toy AIR minted on the spot at a reduced FRI geometry. It is a fixture: nothing
//! ever proved anything with it. This one reads
//! `ugc-dregg/tests/fixtures/whole_history_proof.bin` — the committed 3-turn whole-history
//! envelope, `WholeChainProofBytes` v5, vk fingerprint
//! `434f57d2…7ed5` — and emits the SEVEN-instance batch the deployed apex actually carries
//! (`Const`, `Public`, `Alu`, `poseidon2_perm/baby_bear_d4_w16`,
//! `poseidon2_perm/baby_bear_d4_w24`, `recompose`, `expose_claim`).
//!
//! The equality being emitted is the one `p3_batch_stark`'s verifier checks per instance
//! (`batch-stark/src/verifier/data.rs:100`), in ITS inverse form:
//!
//! ```text
//!   accumulator * Z_H(zeta)^{-1}  ==  quotient(zeta)
//! ```
//!
//! where `accumulator` is `VerifierConstraintFolder`'s `acc = acc*alpha + C_i` fold over the
//! AIR's constraints followed by the LogUp lookup constraints, and `quotient(zeta)` is
//! `recompose_quotient_from_chunks` over the opened chunk values.
//!
//! ## ⚑ THE SELF-CHECK, AND WHY IT IS NOT OPTIONAL
//!
//! A dumper whose transcript replay has drifted emits perfectly plausible JSON that is
//! silently wrong — every number well-formed, every number a different protocol. So before
//! ANYTHING is written:
//!
//! 1. `verify_recursive_batch_proof_with_config` runs p3's OWN `verify_batch` on the loaded
//!    root under `ir2_leaf_wrap_config()` — the full FRI/PCS verification, with p3 sampling
//!    its own `alpha`/`zeta`. It must accept.
//! 2. This binary's HAND-REPLAYED transcript then re-derives `alpha`, `zeta` and the
//!    per-instance permutation challenges, rebuilds the seven AIRs, and evaluates the closing
//!    equality itself for every instance.
//!
//! Both `accumulator` and `quotient(zeta)` are functions of the sampled challenges, so step 2
//! can only pass if step 2's transcript reproduced step 1's exactly. If any instance fails,
//! the binary prints the instance, both sides, and their difference, and REFUSES to emit.
//!
//! 3. And because a check that cannot go red is not a check, every instance is re-evaluated at
//!    BENT challenges and the outcome measured. Bending `alpha` must be refused everywhere (it
//!    moves only the accumulator, so an instance that accepts it has a degenerate fold).
//!
//! ⚑ **The zeta half of that measurement comes back NON-UNIFORM, and it is emitted as data.**
//! The root's seventh instance, `expose_claim`, has `degree_bits = 0` — a ONE-ROW trace domain.
//! There `is_first_row = is_last_row = 1` (zeta-free constants) while `is_transition = Z_H(zeta)`,
//! and the quotient splits into two size-1 chunks carrying EQUAL values. Both sides of the
//! closing equality are therefore constant in zeta: for THIS, HONEST transcript the equality is
//! an IDENTITY in zeta. Every instance with `degree_bits > 0` DOES bind zeta and that is asserted.
//!
//! ⚑ **`zetaBinding = false` DOES NOT MEAN THE CHECK IS A TAUTOLOGY, AND AN EXTERNAL VERIFIER MUST
//! NOT SKIP THE OOD POINT THERE.** A one-row trace polynomial IS a constant, so holding the
//! openings fixed while moving zeta is the CORRECT continuation rather than a perturbation — the
//! insensitivity is a property of an honest prover, not of the verifier's check. What the check
//! does is test, at a uniform zeta, the polynomial
//! `P(X) = A + (X-1)·B - (X-1)·Σ_i zps_i(X)·c_i` of degree ≤ 2, where `A` is the alpha-fold of
//! every constraint NOT gated by `when_transition`, `B` the fold of the gated ones, and the `c_i`
//! the quotient chunk openings — all of them fixed BEFORE zeta is sampled, and each pinned to a
//! constant by `p3_fri`'s height-1 guard (`reduced_openings.get(&params.log_blowup)` must be
//! zero). `P(1) = A`, so a prover with `A != 0` is refused except with probability `<= 2/|EF|`.
//! That is measured here as `zetaBindsForgery`, which is asserted for ALL SEVEN instances with no
//! carve-out: `expose_claim` included, a forgery repaired at the sampled zeta dies at every other
//! zeta. `circuit-prove/tests/height1_air_check_binding.rs` is the standing control for the shape.
//!
//! ## ⚑ Canonical, not Montgomery
//!
//! `MontyField31`'s `Serialize` writes the raw Montgomery limb, which is right for p3↔p3 and
//! WRONG for anyone reading the numbers as field elements. Every value here goes through
//! `as_canonical_u32` — extension elements as 4 base limbs, base elements as one.
//!
//! ## ⚑ It is a `src/bin` target, not an example, deliberately
//!
//! Cargo compiles DEV-DEPENDENCIES for an example, and `dregg-circuit-prove`'s dev-deps reach
//! `dregg-lean-ffi`, whose build script fails closed whenever the Lean tree is mid-edit. This
//! emitter needs nothing outside `[dependencies]`, and a gate leg that goes red because an
//! unrelated Lean module is being rewritten is a gate nobody can read.
//!
//! ## What is REPLICATED from private p3 code, and why
//!
//! Three things in the `verify_batch` path are not reachable from outside their crates. All are
//! replicated here rather than widening a dependency's visibility:
//!
//! * `p3_batch_stark::verifier::VerifierData` is `pub(crate)`-fielded with no constructor, so
//!   `data.rs:61-102` (selectors, the two `VerticalPair`s, the folder pair, the closing
//!   comparison) is reproduced in [`eval_instance`]. Every type it touches is public.
//! * `BatchStarkProver::rebuild_airs_pvs_common` is private, so its AIR/public-value
//!   reconstruction (`batch_stark_prover.rs:1433-1521`) is reproduced in [`rebuild_airs`] —
//!   including the `.with_min_height` / `.with_horner_pack_k` the deployed verify path applies
//!   and a census-style bare constructor would not. The lookup contexts are NOT replicated:
//!   they come from the PUBLIC `rebuild_verifiable_common::<4>`.
//! * `WholeChainProofBytes::decode_parts` is private; only its three-line root-proof decode is
//!   replicated (the binding proof is not needed here).
//!
//! Every one of those replications is load-bearing for the self-check, which is what says
//! whether the replication drifted.

use std::collections::BTreeMap;
use std::env;
use std::fmt::Write as _;
use std::time::Instant;

use dregg_circuit_prove::ivc_turn_chain::{WholeChainProofBytes, ir2_leaf_wrap_config};
use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, verify_recursive_batch_proof_with_config,
};
use p3_air::{BaseAir, RowWindow};
use p3_batch_stark::{BatchTranscript, StarkGenericConfig};
use p3_circuit::ops::{NpoTypeId, Poseidon2Config};
use p3_circuit_prover::air::{AluAir, ConstAir, PublicAir};
use p3_circuit_prover::common::CircuitTableAir;
use p3_circuit_prover::{
    BatchStarkProof, BatchStarkProver, PrimitiveTable, TableProver, expose_claim_table_provers,
    poseidon2_table_provers_d4, recompose_table_provers,
};
use p3_commit::PolynomialSpace;
use p3_field::coset::TwoAdicMultiplicativeCoset;
use p3_field::extension::BinomialExtensionField;
use p3_field::{
    BasedVectorSpace, ExtensionField, Field, PrimeCharacteristicRing, PrimeField32, TwoAdicField,
};
use p3_lookup::folder::VerifierConstraintFolderWithLookups;
use p3_lookup::logup::LogUpGadget;
use p3_lookup::{Kind, LookupProtocol, Lookups};
use p3_matrix::dense::RowMajorMatrixView;
use p3_matrix::stack::VerticalPair;
use p3_uni_stark::{VerifierConstraintFolder, recompose_quotient_from_chunks};

/// The root's base field.
type F = p3_baby_bear::BabyBear;
/// The root's challenge field — `BinomialExtensionField<BabyBear, 4>`
/// (`circuit-prove/src/plonky3_recursion_impl.rs:136`).
type EF = BinomialExtensionField<F, 4>;
/// The config the root verifies under (`ivc_turn_chain.rs:3092`).
type SC = DreggRecursionConfig;
/// The circuit's extension degree — `RECURSION_EXT_DEGREE`.
const D: usize = 4;

/// The committed whole-history envelope this emitter reads.
const FIXTURE: &str = "ugc-dregg/tests/fixtures/whole_history_proof.bin";

// ===========================================================================
// Canonical encoders — canonical-u32 on the wire, never Montgomery.
// ===========================================================================

fn f_u32(v: F) -> u32 {
    v.as_canonical_u32()
}
fn ef_limbs(v: EF) -> Vec<u32> {
    v.as_basis_coefficients_slice()
        .iter()
        .map(|x| f_u32(*x))
        .collect()
}
fn arr(vals: impl IntoIterator<Item = String>) -> String {
    let mut s = String::from("[");
    for (i, v) in vals.into_iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        s.push_str(&v);
    }
    s.push(']');
    s
}
fn nums(vals: impl IntoIterator<Item = u32>) -> String {
    arr(vals.into_iter().map(|v| v.to_string()))
}
fn ef_json(v: EF) -> String {
    nums(ef_limbs(v))
}
fn ef_list(vs: &[EF]) -> String {
    arr(vs.iter().map(|v| ef_json(*v)))
}
fn json_str(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

// ===========================================================================
// The AIR set — `rebuild_airs_pvs_common`'s reconstruction, outside the crate.
// ===========================================================================

/// The four table provers `verify_recursive_batch_proof_with_config` registers, in ITS
/// registration order (`plonky3_recursion_impl.rs:822-831`). The op-type keying below makes
/// the order immaterial, but keeping it identical means a future registration change shows up
/// as a diff here rather than as a silent lookup miss.
fn deployed_table_provers() -> Vec<Box<dyn TableProver<SC>>> {
    let mut provers: Vec<Box<dyn TableProver<SC>>> = Vec::new();
    provers.extend(poseidon2_table_provers_d4::<SC>(
        Poseidon2Config::BABY_BEAR_D4_W16,
    ));
    provers.extend(poseidon2_table_provers_d4::<SC>(
        Poseidon2Config::BABY_BEAR_D4_W24,
    ));
    // split_coeff_tables = false because Poseidon2Config::D (4) == extension degree D (4).
    provers.extend(recompose_table_provers::<SC, D>(1, false));
    provers.extend(expose_claim_table_provers::<SC, D>());
    provers
}

/// Rebuild the batch's AIRs and per-instance public values from the proof's own metadata —
/// `BatchStarkProver::rebuild_airs_pvs_common::<4>` (private), reproduced.
///
/// ⚑ The ALU AIR here is `new_binomial(rows, lanes, w).with_horner_pack_k(k).with_min_height(h)`,
/// which is what the DEPLOYED verify path builds. `root_air_constraint_census.rs`'s `alu_air`
/// uses `new_binomial_with_preprocessed` at a fixed 1024 rows because it is counting
/// constraints, where neither the row count nor the preprocessed content moves the answer.
/// Here they both matter: the row counts are the proof's, and a wrong `min_height` is a
/// different trace domain.
fn rebuild_airs(
    config: &SC,
    proof: &BatchStarkProof<SC>,
) -> Result<(Vec<CircuitTableAir<SC, D>>, Vec<Vec<F>>, Vec<String>), String> {
    assert_eq!(proof.ext_degree, D, "the root batch is the D=4 one");
    assert!(
        !proof.alu_quintic_trinomial,
        "the root's ALU is the binomial-extension variant"
    );

    let packing = &proof.table_packing;
    let public_lanes = packing.public_lanes();
    let alu_lanes = packing.alu_lanes();
    let min_height = packing.min_trace_height();
    let horner_k = packing.horner_packed_steps();

    let w = proof
        .w_binomial
        .ok_or_else(|| "the D=4 root carries no binomial W".to_string())?;

    let mut airs: Vec<CircuitTableAir<SC, D>> = vec![
        CircuitTableAir::Const(
            ConstAir::<F, D>::new(proof.rows[PrimitiveTable::Const]).with_min_height(min_height),
        ),
        CircuitTableAir::Public(
            PublicAir::<F, D>::new(proof.rows[PrimitiveTable::Public], public_lanes)
                .with_min_height(min_height),
        ),
        CircuitTableAir::Alu(
            AluAir::<F, D>::new_binomial(proof.rows[PrimitiveTable::Alu], alu_lanes, w)
                .with_horner_pack_k(horner_k)
                .with_min_height(min_height),
        ),
    ];
    let mut pvs: Vec<Vec<F>> = vec![Vec::new(), Vec::new(), Vec::new()];
    let mut names: Vec<String> = vec!["Const".into(), "Public".into(), "Alu".into()];

    let provers = deployed_table_provers();
    let by_type: BTreeMap<NpoTypeId, usize> = provers
        .iter()
        .enumerate()
        .map(|(i, p)| (p.op_type(), i))
        .collect();

    for entry in &proof.non_primitives {
        let pi = *by_type
            .get(&entry.op_type)
            .ok_or_else(|| format!("unknown non-primitive op: {:?}", entry.op_type))?;
        let air =
            provers[pi].batch_air_from_table_entry(config, D, proof.ext_degree as u32, entry)?;
        airs.push(CircuitTableAir::Dynamic(air));
        pvs.push(entry.public_values.clone());
        names.push(entry.op_type.as_str().to_string());
    }

    Ok((airs, pvs, names))
}

// ===========================================================================
// The transcript REPLAY — p3's own `BatchTranscript`, driven in `verify_batch`'s order.
// ===========================================================================

struct Replay {
    /// `verify_batch`'s per-instance permutation challenges (`verifier/mod.rs:289`). For LogUp
    /// this is TWO challenges (`beta`, `gamma`) PER LOOKUP CONTEXT, not two per instance —
    /// global lookups sharing a bus name share the sampled pair, but it is repeated once per
    /// context because `sample_perm_challenges` flat-maps over contexts.
    per_instance: Vec<Vec<EF>>,
    alpha: EF,
    zeta: EF,
}

/// Replay `verify_batch`'s transcript up to `zeta`, using p3's OWN `BatchTranscript` methods in
/// p3's OWN order (`batch-stark/src/verifier/mod.rs:144,274,278,279,289,290,294,300`).
fn replay(
    config: &SC,
    proof: &BatchStarkProof<SC>,
    airs: &[CircuitTableAir<SC, D>],
    pvs: &[Vec<F>],
    common: &p3_batch_stark::CommonData<SC>,
    preprocessed_widths: &[usize],
) -> Replay {
    let p = &proof.proof;
    let is_zk = config.is_zk();
    assert_eq!(
        is_zk, 0,
        "TwoAdicFriPcs::ZK is false; the ZK arms are dead here"
    );

    let mut t = BatchTranscript::<SC>::new(config.initialise_challenger());
    t.observe_instance_count(airs.len());
    for (i, air) in airs.iter().enumerate() {
        let ext_db = p.degree_bits[i];
        // `validate_degree_bits(.., is_zk = 0, ..)` returns `base_db = ext_db`.
        let base_db = ext_db;
        let width = <CircuitTableAir<SC, D> as BaseAir<F>>::width(air);
        let n_chunks = p.opened_values.instances[i]
            .base_opened_values
            .quotient_chunks
            .len();
        t.observe_instance_binding(ext_db, base_db, width, n_chunks);
    }
    t.observe_main(&p.commitments.main, pvs);
    t.observe_preprocessed(preprocessed_widths, common.preprocessed.as_ref());
    let per_instance = t.sample_perm_challenges(&common.lookups, &LogUpGadget);
    let alpha =
        t.observe_perm_and_sample_alpha(p.commitments.permutation.as_ref(), &p.global_lookup_data);
    t.observe_quotient_commitment(&p.commitments.quotient_chunks);
    assert!(
        p.commitments.random.is_none(),
        "a random commitment means ZK is on, which this replay does not model"
    );
    let zeta = t.sample_zeta();

    Replay {
        per_instance,
        alpha,
        zeta,
    }
}

// ===========================================================================
// The closing equality — `VerifierData::verify_constraints_with_lookups`, outside the crate.
// ===========================================================================

/// Everything one instance contributes, computed the way p3 computes it.
struct InstanceEval {
    /// The instance's trace domain — `natural_domain_for_degree(1 << degree_bits)`, which for
    /// `TwoAdicFriPcs` IS `TwoAdicMultiplicativeCoset::new(ONE, degree_bits)`
    /// (`fri/src/two_adic_pcs.rs:285-287`).
    trace_domain: TwoAdicMultiplicativeCoset<F>,
    chunk_domains: Vec<TwoAdicMultiplicativeCoset<F>>,
    sels: p3_commit::LagrangeSelectors<EF>,
    /// The permutation openings folded back from base-flattened columns into EF columns.
    perm_local_ext: Vec<EF>,
    perm_next_ext: Vec<EF>,
    /// The cumulative sums the folder consumes as `permutation_values`.
    perm_values: Vec<EF>,
    periodic_values: Vec<EF>,
    quotient: EF,
    accumulator: EF,
}

/// Reproduce `p3_batch_stark::verifier::data.rs:61-102` for one instance.
#[allow(clippy::too_many_arguments)]
fn eval_instance(
    i: usize,
    air: &CircuitTableAir<SC, D>,
    proof: &BatchStarkProof<SC>,
    lookups: &Lookups<F>,
    public_values: &[F],
    perm_challenges: &[EF],
    // The COMMON-DATA preprocessed width, which is what `verifier/mod.rs:578` sizes an absent
    // `preprocessed_next` by — not the AIR's own `preprocessed_width()`.
    preprocessed_width: usize,
    alpha: EF,
    zeta: EF,
) -> InstanceEval {
    let p = &proof.proof;
    let inst = &p.opened_values.instances[i];
    let ov = &inst.base_opened_values;

    let db = p.degree_bits[i];
    let trace_domain = TwoAdicMultiplicativeCoset::<F>::new(F::ONE, db)
        .expect("degree_bits within BabyBear's two-adicity");

    // The quotient chunk domains — `verifier/mod.rs:360-375` at is_zk = 0.
    let n_chunks = ov.quotient_chunks.len();
    assert!(
        n_chunks.is_power_of_two(),
        "n_chunks is 1 << log_num_chunks"
    );
    let log_num_chunks = n_chunks.trailing_zeros() as usize;
    let quotient_domain = trace_domain.create_disjoint_domain(1 << (db + log_num_chunks));
    let chunk_domains = quotient_domain.split_domains(n_chunks);

    let quotient = recompose_quotient_from_chunks::<SC>(&chunk_domains, &ov.quotient_chunks, zeta);

    // The permutation openings, folded back into EF (`verifier/mod.rs:543-559`).
    let aux_width = lookups
        .iter()
        .map(|ctx| ctx.column)
        .max()
        .map(|m| m + 1)
        .unwrap_or(0);
    let recompose = |flat: &[EF]| -> Vec<EF> {
        if aux_width == 0 {
            return Vec::new();
        }
        flat.chunks_exact(D)
            .map(|chunk| {
                <EF as ExtensionField<F>>::from_ext_basis_coefficients(chunk)
                    .expect("chunk length matches DIMENSION by construction")
            })
            .collect()
    };
    let perm_local_ext = recompose(&inst.permutation_local);
    let perm_next_ext = recompose(&inst.permutation_next);

    let width = <CircuitTableAir<SC, D> as BaseAir<F>>::width(air);

    let trace_next_zeros: Vec<EF>;
    let trace_next: &[EF] = match &ov.trace_next {
        Some(v) => v.as_slice(),
        None => {
            trace_next_zeros = vec![EF::ZERO; width];
            &trace_next_zeros
        }
    };
    let pre_local: &[EF] = ov.preprocessed_local.as_deref().unwrap_or(&[]);
    let pre_next_zeros: Vec<EF>;
    let pre_next: &[EF] = match &ov.preprocessed_next {
        Some(v) => v.as_slice(),
        None => {
            pre_next_zeros = vec![EF::ZERO; preprocessed_width];
            &pre_next_zeros
        }
    };

    let perm_values: Vec<EF> = p.global_lookup_data[i]
        .iter()
        .map(|ld| ld.cumulative_sum)
        .collect();
    let periodic_values: Vec<EF> = <CircuitTableAir<SC, D> as BaseAir<F>>::periodic_columns(air)
        .iter()
        .map(|col| trace_domain.evaluate_periodic_column_at(col, zeta))
        .collect();

    let sels = trace_domain.selectors_at_point(zeta);

    let main = VerticalPair::new(
        RowMajorMatrixView::new_row(&ov.trace_local),
        RowMajorMatrixView::new_row(trace_next),
    );
    let preprocessed = VerticalPair::new(
        RowMajorMatrixView::new_row(pre_local),
        RowMajorMatrixView::new_row(pre_next),
    );
    let preprocessed_window =
        RowWindow::from_two_rows(preprocessed.top.values, preprocessed.bottom.values);

    let inner = VerifierConstraintFolder::<SC> {
        main,
        preprocessed,
        preprocessed_window,
        periodic_values: &periodic_values,
        public_values,
        is_first_row: sels.is_first_row,
        is_last_row: sels.is_last_row,
        is_transition: sels.is_transition,
        alpha,
        accumulator: EF::ZERO,
    };
    let mut folder = VerifierConstraintFolderWithLookups::<SC> {
        inner,
        permutation: VerticalPair::new(
            RowMajorMatrixView::new_row(&perm_local_ext),
            RowMajorMatrixView::new_row(&perm_next_ext),
        ),
        permutation_challenges: perm_challenges,
        permutation_values: &perm_values,
    };
    LogUpGadget.eval_air_and_lookups(air, &mut folder, lookups);
    let accumulator = folder.inner.accumulator;

    InstanceEval {
        trace_domain,
        chunk_domains,
        sels,
        perm_local_ext,
        perm_next_ext,
        perm_values,
        periodic_values,
        quotient,
        accumulator,
    }
}

// ===========================================================================
// main
// ===========================================================================

fn main() {
    let t_start = Instant::now();
    let args: Vec<String> = env::args().collect();
    let out_path = args.get(1).cloned();

    // ---- load the committed envelope ---------------------------------------
    let fixture = repo_relative(FIXTURE);
    let bytes = std::fs::read(&fixture)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", fixture.display()));
    let env_v5 = WholeChainProofBytes::from_postcard(&bytes)
        .unwrap_or_else(|e| panic!("the committed envelope does not decode: {e:?}"));

    // `WholeChainProofBytes::decode_parts` is private; this is its root-proof half.
    let root: BatchStarkProof<SC> = postcard::from_bytes(&env_v5.root_proof)
        .unwrap_or_else(|e| panic!("root BatchStarkProof does not decode: {e}"));
    root.validate()
        .unwrap_or_else(|e| panic!("root BatchStarkProof failed structural validation: {e:?}"));

    eprintln!(
        "envelope v{}  vk {}  turns {}  degree_bits {:?}",
        env_v5.version, env_v5.vk_fingerprint_hex, env_v5.num_turns, root.proof.degree_bits
    );

    // ---- STEP 1: p3's OWN verifier accepts, with p3's OWN challenges --------
    let config = ir2_leaf_wrap_config();
    let t_verify = Instant::now();
    verify_recursive_batch_proof_with_config(&root, &config)
        .unwrap_or_else(|e| panic!("the committed root does NOT verify: {e}"));
    eprintln!("p3 verify_batch accepted in {:?}", t_verify.elapsed());

    // ---- rebuild the AIRs, public values and lookup contexts ---------------
    let (airs, pvs, names) =
        rebuild_airs(&config, &root).unwrap_or_else(|e| panic!("AIR reconstruction failed: {e}"));

    // The lookup contexts come from the PUBLIC reconstruction, not a replica of it.
    let mut prover = BatchStarkProver::new(config.clone());
    prover.register_poseidon2_table::<D>(Poseidon2Config::BABY_BEAR_D4_W16);
    prover.register_poseidon2_table::<D>(Poseidon2Config::BABY_BEAR_D4_W24);
    prover.register_recompose_table::<D>(false);
    prover.register_expose_claim_table::<D>();
    let common = prover
        .rebuild_verifiable_common::<D>(&root, root.w_binomial)
        .unwrap_or_else(|e| panic!("rebuild_verifiable_common failed: {e:?}"));

    let n = airs.len();
    assert_eq!(n, root.proof.opened_values.instances.len());
    assert_eq!(n, common.lookups.len());
    assert_eq!(n, pvs.len());
    assert_eq!(n, root.proof.degree_bits.len());

    let preprocessed_widths: Vec<usize> = (0..n)
        .map(|i| {
            common
                .preprocessed
                .as_ref()
                .and_then(|g| g.instances[i].as_ref().map(|m| m.width))
                .unwrap_or(0)
        })
        .collect();

    // ---- STEP 2: the hand replay -------------------------------------------
    let rep = replay(&config, &root, &airs, &pvs, &common, &preprocessed_widths);

    // ---- STEP 3: the closing equality, per instance, BEFORE anything emits --
    let mut evals = Vec::with_capacity(n);
    let mut failures = Vec::new();
    for i in 0..n {
        let e = eval_instance(
            i,
            &airs[i],
            &root,
            &common.lookups[i],
            &pvs[i],
            &rep.per_instance[i],
            preprocessed_widths[i],
            rep.alpha,
            rep.zeta,
        );
        let lhs = e.accumulator * e.sels.inv_vanishing;
        if lhs != e.quotient {
            failures.push((i, lhs, e.quotient));
        }
        evals.push(e);
    }

    if !failures.is_empty() {
        eprintln!(
            "\n⚑ THE CLOSING EQUALITY FAILED on {} of {n} instances. NOTHING IS EMITTED.\n\
             p3's own verify_batch ACCEPTED this proof, so the replayed transcript or the AIR \
             reconstruction below has drifted from the deployed verify path — the emitted JSON \
             would have been well-formed and wrong.\n",
            failures.len()
        );
        for (i, lhs, rhs) in &failures {
            eprintln!(
                "  instance {i} ({}): degree_bits {} \n    accumulator*invZ = {:?}\n    quotient(zeta)   = {:?}\n    difference       = {:?}",
                names[*i],
                root.proof.degree_bits[*i],
                ef_limbs(*lhs),
                ef_limbs(*rhs),
                ef_limbs(*lhs - *rhs),
            );
        }
        std::process::exit(1);
    }
    eprintln!("closing equality holds for all {n} instances");

    // ---- STEP 4: PROVE THE CHECK CAN GO RED, AND MEASURE WHERE IT CANNOT ----
    // ⚑ A check that cannot fail is not a check. The equality holding at the REPLAYED
    // `(alpha, zeta)` is only evidence if it FAILS at a wrong one, so each instance is
    // re-evaluated at bent challenges and the outcome MEASURED rather than assumed:
    //   * `alpha` bends move ONLY the accumulator — `recompose_quotient_from_chunks` never sees
    //     alpha. An instance that accepts a bent alpha has a degenerate fold and its AIR side
    //     says nothing.
    //   * `zeta` bends move the selectors, the quotient recomposition AND the accumulator, over
    //     opened values that stay pinned to the real point.
    // Several bends per challenge, because a single one can coincide.
    let alpha_bends = [EF::ONE, EF::TWO, EF::from_u32(0x51ed_1234)];
    let zeta_bends = [EF::ONE, EF::TWO, EF::from_u32(0x9e37_79b9)];
    let mut alpha_binding = vec![false; n];
    let mut zeta_binding = vec![false; n];
    for i in 0..n {
        let refuses = |a: EF, z: EF| {
            let e = eval_instance(
                i,
                &airs[i],
                &root,
                &common.lookups[i],
                &pvs[i],
                &rep.per_instance[i],
                preprocessed_widths[i],
                a,
                z,
            );
            e.accumulator * e.sels.inv_vanishing != e.quotient
        };
        alpha_binding[i] = alpha_bends
            .iter()
            .all(|d| refuses(rep.alpha + *d, rep.zeta));
        zeta_binding[i] = zeta_bends.iter().all(|d| refuses(rep.alpha, rep.zeta + *d));
    }

    // The alpha half is a hard floor: a fold nothing can move is a vacuous fold.
    for i in 0..n {
        assert!(
            alpha_binding[i],
            "instance {i} ({}) ACCEPTED every bent alpha — its constraint fold is degenerate and \
             the closing equality holding above says nothing about it",
            names[i]
        );
    }

    // ⚑ THE ZETA HALF IS A MEASUREMENT, AND IT COMES BACK NON-UNIFORM. A one-row trace domain
    // (`degree_bits == 0`) makes `is_first_row = is_last_row = 1` — ζ-FREE constants — while
    // `is_transition = ζ − 1 = Z_H(ζ)`, so `accumulator · Z_H(ζ)^{-1}` is ζ-free whenever the
    // non-transition part of the fold vanishes; and a quotient split into two size-1 chunks
    // carrying EQUAL values recomposes to that same constant at every ζ. The root's
    // `expose_claim` instance is exactly that shape, so for THIS transcript the closing equality
    // is an IDENTITY in ζ. Every instance with `degree_bits > 0` must still bind ζ, and that IS
    // asserted.
    for i in 0..n {
        if root.proof.degree_bits[i] > 0 {
            assert!(
                zeta_binding[i],
                "instance {i} ({}) has degree_bits {} > 0 yet ACCEPTED every bent zeta — the OOD \
                 point does not enter its closing equality, which a multi-row domain cannot \
                 explain",
                names[i], root.proof.degree_bits[i]
            );
        } else if !zeta_binding[i] {
            eprintln!(
                "  ⚑ instance {i} ({}) has degree_bits 0: for the HONEST transcript its closing \
                 equality is an IDENTITY in zeta (is_first_row = is_last_row = 1, is_transition = \
                 Z_H(zeta), both quotient chunks equal) — a one-row trace polynomial IS a \
                 constant, so a fixed opening is the correct continuation. Emitted as \
                 zetaBinding=false; see zetaBindsForgery below, which is what says the OOD point \
                 still binds.",
                names[i]
            );
        }
    }

    // ---- STEP 5: DOES ZETA BIND A *FORGERY*? THE QUESTION zetaBinding DOES NOT ANSWER ----
    // ⚑ `zetaBinding` measures the HONEST instance's sensitivity, which at `degree_bits = 0` is
    // structurally zero and says nothing about the check. This measures the adversarial quantity:
    // a forged trace shifts the ζ-free half of the fold by a nonzero δ (EXACT at degree_bits = 0,
    // where `accumulator(ζ) = A + Z_H(ζ)·B` and a forged row moves `A`); the forger is then handed
    // the strongest move the protocol leaves him — SOLVE the quotient chunk openings that repair
    // the closing equality at the SAMPLED ζ, which is always possible because the chunks are free
    // field elements. That repair must then die at every other ζ, because the chunks are committed
    // BEFORE ζ is sampled. If it does not, that instance's AIR check really is vacuous.
    let forge_delta = EF::from_u32(0x00c0_ffee);
    assert_ne!(
        forge_delta,
        EF::ZERO,
        "the forgery must actually move the fold"
    );
    let chunk_of = |v: EF| -> Vec<EF> {
        let limbs: &[F] = <EF as BasedVectorSpace<F>>::as_basis_coefficients_slice(&v);
        limbs.iter().map(|c| EF::from(*c)).collect()
    };
    let mut zeta_binds_forgery = vec![false; n];
    for i in 0..n {
        let n_chunks = root.proof.opened_values.instances[i]
            .base_opened_values
            .quotient_chunks
            .len();
        let closes = |chunks: &[Vec<EF>], z: EF| -> bool {
            let ev = eval_instance(
                i,
                &airs[i],
                &root,
                &common.lookups[i],
                &pvs[i],
                &rep.per_instance[i],
                preprocessed_widths[i],
                rep.alpha,
                z,
            );
            (ev.accumulator + forge_delta) * ev.sels.inv_vanishing
                == recompose_quotient_from_chunks::<SC>(&ev.chunk_domains, chunks, z)
        };

        // Solve the repair at the sampled ζ. `zps_0(ζ)` is read off p3's own recomposition by
        // feeding it a unit first chunk rather than reimplementing the Lagrange weights.
        let e = &evals[i];
        let target = (e.accumulator + forge_delta) * e.sels.inv_vanishing;
        let mut unit: Vec<Vec<EF>> = (0..n_chunks).map(|_| chunk_of(EF::ZERO)).collect();
        unit[0] = chunk_of(EF::ONE);
        let zps_0 = recompose_quotient_from_chunks::<SC>(&e.chunk_domains, &unit, rep.zeta);
        assert_ne!(
            zps_0,
            EF::ZERO,
            "instance {i} ({}): the first quotient chunk's Lagrange weight vanished at zeta",
            names[i]
        );
        let mut repaired: Vec<Vec<EF>> = (0..n_chunks).map(|_| chunk_of(EF::ZERO)).collect();
        repaired[0] = chunk_of(target * zps_0.inverse());

        // The forger's move must LAND — otherwise this measurement is not measuring a forgery.
        assert!(
            closes(&repaired, rep.zeta),
            "instance {i} ({}): the solved forgery did not close at the sampled zeta, so the \
             refusals below would prove nothing",
            names[i]
        );
        zeta_binds_forgery[i] = zeta_bends.iter().all(|d| !closes(&repaired, rep.zeta + *d));
    }

    // ⚑ NO CARVE-OUT. `degree_bits == 0` is exactly where the honest instance is ζ-insensitive and
    // exactly where it is tempting to conclude the check is free; this is the assertion that says
    // otherwise, and it is the one an external verifier's "can I skip zeta here?" question must be
    // answered from.
    for i in 0..n {
        assert!(
            zeta_binds_forgery[i],
            "instance {i} ({}, degree_bits {}) ACCEPTED a zeta-solved FORGERY at every bent zeta — \
             its AIR closing equality is genuinely vacuous and the out-of-domain point is not \
             constraining that instance's trace",
            names[i], root.proof.degree_bits[i]
        );
    }
    eprintln!(
        "anti-vacuity: alpha binds all {n} instances; zeta binds {} of {n} HONEST instances; \
         zeta binds a FORGERY in all {n}",
        zeta_binding.iter().filter(|b| **b).count()
    );

    // ---- emit ---------------------------------------------------------------
    let json = emit(
        &env_v5,
        &root,
        &airs,
        &pvs,
        &names,
        &common,
        &preprocessed_widths,
        &rep,
        &evals,
        &alpha_binding,
        &zeta_binding,
        &zeta_binds_forgery,
    );
    match &out_path {
        Some(p) => {
            std::fs::write(p, &json).unwrap_or_else(|e| panic!("cannot write {p}: {e}"));
            eprintln!("wrote {p} ({} bytes)", json.len());
        }
        None => println!("{json}"),
    }
    eprintln!("total wall time {:?}", t_start.elapsed());
}

/// Resolve a repo-relative path from either the workspace root or `circuit-prove/`.
fn repo_relative(rel: &str) -> std::path::PathBuf {
    let here = std::path::Path::new(rel);
    if here.exists() {
        return here.to_path_buf();
    }
    // `CARGO_MANIFEST_DIR` is `<repo>/circuit-prove` when built through cargo.
    let manifest = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let from_root = manifest.parent().unwrap_or(manifest).join(rel);
    if from_root.exists() {
        return from_root;
    }
    here.to_path_buf()
}

#[allow(clippy::too_many_arguments)]
fn emit(
    env_v5: &WholeChainProofBytes,
    root: &BatchStarkProof<SC>,
    airs: &[CircuitTableAir<SC, D>],
    pvs: &[Vec<F>],
    names: &[String],
    common: &p3_batch_stark::CommonData<SC>,
    preprocessed_widths: &[usize],
    rep: &Replay,
    evals: &[InstanceEval],
    alpha_binding: &[bool],
    zeta_binding: &[bool],
    zeta_binds_forgery: &[bool],
) -> String {
    let p = &root.proof;
    let n = airs.len();

    let mut o = String::new();
    o.push('{');
    write!(o, r#""kind":"dregg-root-air-instance","#).unwrap();
    write!(
        o,
        r#""vkFingerprint":{},"numTurns":{},"envelopeVersion":{},"#,
        json_str(&env_v5.vk_fingerprint_hex),
        env_v5.num_turns,
        env_v5.version
    )
    .unwrap();
    write!(
        o,
        r#""extDegree":{D},"isZk":false,"degreeBits":{},"#,
        arr(p.degree_bits.iter().map(usize::to_string))
    )
    .unwrap();
    write!(
        o,
        r#""challenges":{{"alpha":{},"zeta":{}}},"#,
        ef_json(rep.alpha),
        ef_json(rep.zeta)
    )
    .unwrap();

    let mut insts = Vec::with_capacity(n);
    for i in 0..n {
        let inst = &p.opened_values.instances[i];
        let ov = &inst.base_opened_values;
        let e = &evals[i];
        let lookups = &common.lookups[i];

        let mut s = String::new();
        s.push('{');
        write!(
            s,
            r#""index":{i},"table":{},"degreeBits":{},"width":{},"prepWidth":{},"nChunks":{},"#,
            json_str(&names[i]),
            p.degree_bits[i],
            ov.trace_local.len(),
            preprocessed_widths[i],
            ov.quotient_chunks.len(),
        )
        .unwrap();
        write!(
            s,
            r#""permChallenges":{},"permutationValues":{},"periodicValues":{},"#,
            ef_list(&rep.per_instance[i]),
            ef_list(&e.perm_values),
            ef_list(&e.periodic_values),
        )
        .unwrap();
        write!(
            s,
            r#""traceLocal":{},"traceNext":{},"#,
            ef_list(&ov.trace_local),
            match &ov.trace_next {
                Some(v) => ef_list(v),
                None => "null".to_string(),
            },
        )
        .unwrap();
        write!(
            s,
            r#""prepLocal":{},"prepNext":{},"#,
            match &ov.preprocessed_local {
                Some(v) => ef_list(v),
                None => "null".to_string(),
            },
            match &ov.preprocessed_next {
                Some(v) => ef_list(v),
                None => "null".to_string(),
            },
        )
        .unwrap();
        write!(
            s,
            r#""permLocal":{},"permNext":{},"#,
            ef_list(&e.perm_local_ext),
            ef_list(&e.perm_next_ext),
        )
        .unwrap();
        write!(
            s,
            r#""publicValues":{},"#,
            nums(pvs[i].iter().map(|v| f_u32(*v)))
        )
        .unwrap();
        write!(
            s,
            r#""quotientChunks":{},"#,
            arr(ov.quotient_chunks.iter().map(|c| ef_list(c)))
        )
        .unwrap();
        // The domain constants an external verifier folds in for free: the trace domain is the
        // natural coset (shift = 1), so `selectors_at_point` needs only `g^{-1}`; the chunk
        // recomposition needs each chunk domain's shift and the Lagrange constants.
        write!(
            s,
            r#""domain":{{"traceLogSize":{},"subgroupGenInv":{},"chunkLogSize":{},"chunkShiftInvs":{}}},"#,
            e.trace_domain.log_size(),
            f_u32(
                <F as TwoAdicField>::two_adic_generator(e.trace_domain.log_size())
                    .inverse()
            ),
            e.chunk_domains[0].log_size(),
            nums(e.chunk_domains.iter().map(|d| f_u32(d.shift().inverse()))),
        )
        .unwrap();
        write!(
            s,
            r#""selectors":{{"isFirstRow":{},"isLastRow":{},"isTransition":{},"invVanishing":{}}},"#,
            ef_json(e.sels.is_first_row),
            ef_json(e.sels.is_last_row),
            ef_json(e.sels.is_transition),
            ef_json(e.sels.inv_vanishing),
        )
        .unwrap();
        write!(
            s,
            r#""quotientAtZeta":{},"accumulator":{},"#,
            ef_json(e.quotient),
            ef_json(e.accumulator),
        )
        .unwrap();
        // ⚑ MEASURED, not assumed. `alphaBinding`/`zetaBinding` say whether THIS, HONEST
        // instance's closing equality moves when the challenge moves; `zetaBinding` is FALSE for
        // the one-row `expose_claim` table, where a constant trace polynomial makes a fixed
        // opening the correct continuation and the equality an identity.
        // ⚑ `zetaBindsForgery` is the one an external verifier must read before deciding it may
        // skip anything: it is TRUE everywhere, `expose_claim` included — a forgery repaired at
        // this zeta is refused at every other zeta. NEVER skip the OOD point on the strength of
        // `zetaBinding: false`.
        write!(
            s,
            r#""alphaBinding":{},"zetaBinding":{},"zetaBindsForgery":{},"#,
            alpha_binding[i], zeta_binding[i], zeta_binds_forgery[i],
        )
        .unwrap();
        // The lookup layout: without it the aux-column width and the bus each context sits on
        // are unrecoverable from the openings alone, and the LogUp half of the accumulator is
        // not reproducible.
        write!(
            s,
            r#""lookups":{}"#,
            arr(lookups.iter().map(|l| {
                let (kind, name) = match &l.kind {
                    Kind::Global(nm) => ("global", json_str(nm)),
                    Kind::Local => ("local", "null".to_string()),
                };
                format!(
                    r#"{{"kind":"{kind}","bus":{name},"column":{},"numTuples":{}}}"#,
                    l.column,
                    l.elements.len()
                )
            }))
        )
        .unwrap();
        s.push('}');
        insts.push(s);
    }
    write!(o, r#""instances":{}"#, arr(insts)).unwrap();
    o.push('}');
    o.push('\n');
    o
}
