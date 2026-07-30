//! **The dregg-side emitter for the ROOT batch's FRI half** — load the REAL committed
//! whole-history root proof, drive p3's OWN transcript to the exact point `verify_fri` is
//! entered, and emit every field an external (o1js) verifier needs to re-run dregg's ACTUAL
//! FRI low-degree test on dregg's ACTUAL root proof, in CANONICAL form.
//!
//! ```text
//!   cargo build -p dregg-circuit-prove --release --bin root_fri_instance
//!   ./target/release/root_fri_instance [out.json]
//! ```
//!
//! ## What this is, and what its sibling is
//!
//! `root_air_instance.rs` emits the ROOT's per-instance AIR closing equality —
//! `accumulator * Z_H(zeta)^{-1} == quotient(zeta)`, the half that says the opened values
//! satisfy the constraint system. It stops at `zeta`. **This binary is the other half**: it
//! starts where that one stops and emits the half that says those opened values are the
//! openings of LOW-DEGREE polynomials the prover was committed to before `zeta` existed —
//! the PCS batch-combination `alpha`, the 16 commit-phase roots and their `beta`s, the
//! constant final polynomial, and all 19 query chains with their Merkle openings, reduced
//! openings, roll-ins and folds.
//!
//! Neither half is a proof on its own. An o1js verifier that checks only the AIR side is
//! reading numbers a prover chose freely; one that checks only the FRI side is proving a
//! low-degree claim about polynomials nobody constrained. The two files share `zeta` and the
//! opened values, and `openedEvals` is labelled precisely so a lane can see that the number
//! it read as `main[2][17]` on the AIR side is the same number that enters round 0, matrix 2,
//! point 0 here.
//!
//! ## The object
//!
//! `ugc-dregg/tests/fixtures/whole_history_proof.bin` — the committed 3-turn whole-history
//! envelope, `WholeChainProofBytes` v5 — decoded to a `BatchStarkProof<DreggRecursionConfig>`
//! and verified under `ir2_leaf_wrap_config()`. The FRI engine is BabyBear /
//! `BinomialExtensionField<_,4>` / Poseidon2-width-16, `log_blowup = 6`, arity 2, 19 queries,
//! 16 bits of query grinding, a CONSTANT final polynomial, and `log_global_max_height = 22`.
//!
//! ## ⚑ THE SELF-CHECKS, AND WHY THEY ARE NOT OPTIONAL
//!
//! A dumper whose transcript replay has drifted emits perfectly plausible JSON that is
//! silently wrong — every number well-formed, every number a different protocol. Nothing is
//! written unless all of the following pass:
//!
//! 1. `verify_recursive_batch_proof_with_config` runs p3's OWN `verify_batch` on the loaded
//!    root. It must accept before a single field is computed.
//! 2. The hand-replayed pre-FRI transcript is validated by handing it to the REAL
//!    `<MyPcs as Pcs<EF, Challenger>>::verify`, started from the mirrored challenger state as
//!    it stood immediately after `sample_zeta`. That call re-observes the opened values,
//!    re-samples the entire FRI transcript and re-checks every Merkle opening and fold chain
//!    itself — so if the mirror or the round structure had drifted from `verify_batch`, it
//!    rejects.
//! 3. Every commit-phase Merkle opening is re-verified with the REAL
//!    `challenge_mmcs.verify_batch`, and every input-batch opening with the REAL
//!    `val_mmcs.verify_batch`, at the index that is emitted for that query.
//! 4. Every query's fold chain must land exactly on `final_poly[0]` (`log_final_poly_len = 0`
//!    means the final polynomial is a constant, so its evaluation at the query point IS
//!    coefficient 0).
//! 5. The 19 query indices must be PAIRWISE DISTINCT, and they are printed. A prior leg in
//!    this repo went green because colliding indices made a substitution falsifier a no-op;
//!    distinctness is asserted here so that failure mode cannot recur silently.
//! 6. `reducedOpenings[0].logHeight == 22` (the initial reduced opening sits at the global max
//!    height, which is what makes the fold chain a statement about the tallest matrix), and
//!    the roll-in schedule is IDENTICAL across all 19 queries.
//!
//! ## ⚑ What pins `challengerStateBeforeFriAlpha`, which is the load-bearing field
//!
//! `challengerStateBeforeFriAlpha` is the `DuplexChallenger`'s full internal state — sponge
//! lanes, input buffer, output buffer — at the instant `verify_fri` is entered, BEFORE FRI's
//! own `alpha` is drawn. An o1js circuit starts its challenger from it and derives `alpha`,
//! the 16 `beta`s and the 19 query indices itself; if this state is wrong, everything
//! downstream is wrong and every emitted number still looks fine.
//!
//! Check 2 alone does NOT pin it: the real `pcs.verify` performs its own opened-value
//! observes internally, so it validates the state as of `sample_zeta` and is blind to whether
//! THIS file then replayed those observes in the right order. What pins it is checks 3 and 4,
//! which run the whole FRI verification FROM the emitted state: a wrong state gives a wrong
//! `alpha` (so no query's fold chain reaches `final_poly[0]`), wrong `beta`s (so the
//! commit-phase Merkle openings fail at the folded indices), and wrong query indices (so the
//! input-batch openings fail outright) — and `check_witness(16, query_pow_witness)` is an
//! independent 16-bit test on the state immediately before the first index is sampled.
//! Together they leave only a sponge collision, which is not a drift mode.
//!
//! ## ⚑ Canonical, not Montgomery
//!
//! `MontyField31`'s `Serialize` writes the raw Montgomery limb, which is right for p3↔p3 and
//! WRONG for anyone reading the numbers as field elements. Every value here goes through
//! `as_canonical_u32` — extension elements as 4 base limbs, base elements as one, Merkle
//! digests as 8.
//!
//! ## What is REPLICATED from private p3 code, and why
//!
//! * `p3_fri::verifier::open_input` is private and returns the per-query reduced openings only
//!   transiently, so it is reproduced in [`open_input_replica`] — INCLUDING the real
//!   `input_mmcs.verify_batch` call, so a mis-built round structure dies here rather than in
//!   o1js. `apex_shrink_gnark_export.rs` does the same for the BN254 outer config; this is its
//!   BabyBear sibling.
//! * `p3_fri::verifier::verify_query`'s fold loop is reproduced inline so the intermediate
//!   folded values can be EXPORTED. The fold itself is NOT reimplemented: it calls p3's own
//!   `TwoAdicFriFolding::fold_row`, which is the exact function the verifier's folding
//!   strategy delegates to.
//! * `BatchStarkProver::rebuild_airs_pvs_common` is private, so its AIR/public-value
//!   reconstruction is reproduced in [`rebuild_airs`] (identical to `root_air_instance.rs`'s).
//!   The AIRs are needed for two things only: the transcript's per-instance width binding, and
//!   `main_next_row_columns()` / `preprocessed_next_row_columns()`, which decide whether a
//!   matrix is opened at one point or two.
//! * `WholeChainProofBytes::decode_parts` is private; only its root-proof decode is replicated.
//!
//! ## ⚑ What this file does NOT close
//!
//! * It is a DUMP. It says what p3's verifier reads; it says nothing about whether an o1js
//!   verifier reading it computes the same thing. That is the o1js lane's burden, and the
//!   reason `foldedAfterRound` is emitted per round rather than only at the end: a divergence
//!   should localise to a fold, not to "the chain".
//! * A FRI proof that verifies is not a sound proof. This config's per-fold and query columns
//!   are the ones the Lean ledger reports, the commit-phase term is not in the query column,
//!   and the whole tower inherits the undischarged FRI/STARK soundness floor. "p3 accepted it"
//!   is the resolution at which everything here is stated.
//! * The input-matrix ROWS are emitted, but nothing here says those rows are the rows of the
//!   committed trace beyond what `val_mmcs.verify_batch` says — which is a Merkle membership
//!   claim under a hash this file does not model.
//! * The AIR half is not re-checked here. Run `root_air_instance` for that; the two must agree
//!   on `zeta` and on every opened value, and nothing in this binary enforces that agreement.
//!
//! ## ⚑ It is a `src/bin` target, not an example, deliberately
//!
//! Cargo compiles DEV-DEPENDENCIES for an example, and `dregg-circuit-prove`'s dev-deps reach
//! `dregg-lean-ffi`, whose build script fails closed whenever the Lean tree is mid-edit. This
//! emitter needs nothing outside `[dependencies]`.

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fmt::Write as _;
use std::time::Instant;

use dregg_circuit_prove::ivc_turn_chain::{
    IR2_INNER_COMMIT_POW_BITS, IR2_INNER_LOG_BLOWUP, IR2_INNER_LOG_FINAL_POLY_LEN,
    IR2_INNER_QUERY_POW_BITS, WholeChainProofBytes, ir2_leaf_wrap_config,
};
use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, INNER_FRI_MAX_LOG_ARITY, INNER_FRI_NUM_QUERIES,
    verify_recursive_batch_proof_with_config,
};
use p3_air::BaseAir;
use p3_baby_bear::{Poseidon2BabyBear, default_babybear_poseidon2_16};
use p3_batch_stark::{BatchTranscript, StarkGenericConfig};
use p3_challenger::{CanObserve, CanSampleBits, FieldChallenger, GrindingChallenger};
use p3_circuit::ops::{NpoTypeId, Poseidon2Config};
use p3_circuit_prover::air::{AluAir, ConstAir, PublicAir};
use p3_circuit_prover::common::CircuitTableAir;
use p3_circuit_prover::{
    BatchStarkProof, BatchStarkProver, PrimitiveTable, TableProver, expose_claim_table_provers,
    poseidon2_table_provers_d4, recompose_table_provers,
};
use p3_commit::{BatchOpening, BatchOpeningRef, ExtensionMmcs, Mmcs, Pcs, PolynomialSpace};
use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField32, TwoAdicField};
use p3_fri::{FriFoldingStrategy, TwoAdicFriFolding};
use p3_lookup::logup::LogUpGadget;
use p3_matrix::Dimensions;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};

/// The root's base field.
type F = p3_baby_bear::BabyBear;
/// The root's challenge field — `BinomialExtensionField<BabyBear, 4>`.
type EF = BinomialExtensionField<F, 4>;
/// The config the root verifies under (`ivc_turn_chain.rs:1326`).
type SC = DreggRecursionConfig;
/// The circuit's extension degree — `RECURSION_EXT_DEGREE`.
const D: usize = 4;

const WIDTH: usize = 16;
const RATE: usize = 8;
const DIGEST_ELEMS: usize = 8;

/// The MMCS stack, re-declared from `plonky3_recursion_impl.rs:138-151` because those aliases
/// are module-private. ⚑ These are not "a" Poseidon2 stack: `default_babybear_poseidon2_16()`
/// is deterministic, and the compiler forces these types to be the SAME types the decoded
/// proof's `input_proof` and `commit_phase_openings` carry — a divergence here is a type
/// error, not a silent mismatch.
type Perm = Poseidon2BabyBear<WIDTH>;
type MyHash = PaddingFreeSponge<Perm, WIDTH, RATE, DIGEST_ELEMS>;
type MyCompress = TruncatedPermutation<Perm, 2, DIGEST_ELEMS, WIDTH>;
type MyMmcs = MerkleTreeMmcs<
    <F as Field>::Packing,
    <F as Field>::Packing,
    MyHash,
    MyCompress,
    2,
    DIGEST_ELEMS,
>;
type ChallengeMmcs = ExtensionMmcs<F, EF, MyMmcs>;

/// The PCS and challenger come from the config's own associated types, so they cannot drift.
type MyPcs = <SC as StarkGenericConfig>::Pcs;
type Challenger = <SC as StarkGenericConfig>::Challenger;
type Domain = <MyPcs as Pcs<EF, Challenger>>::Domain;
type Commitment = <MyPcs as Pcs<EF, Challenger>>::Commitment;
/// `p3_fri::CommitmentWithOpeningPoints` at this config: one committed round.
type ComRound = (Commitment, Vec<(Domain, Vec<(EF, Vec<EF>)>)>);

/// The committed whole-history envelope this emitter reads.
const FIXTURE: &str = "ugc-dregg/tests/fixtures/whole_history_proof.bin";

/// The root batch's instance shape. Asserted rather than assumed: a re-minted fixture with a
/// different shape must announce itself here, not produce a quietly different JSON.
const EXPECTED_DEGREE_BITS: [usize; 7] = [10, 10, 16, 15, 3, 16, 0];
/// `sum(log_arities) + log_blowup + log_final_poly_len` = `16 + 6 + 0`.
const EXPECTED_LOG_GLOBAL_MAX_HEIGHT: usize = 22;
/// One fold round per bit between the global max height and the final domain.
const EXPECTED_LAYERS: usize = 16;

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
fn f_list(vs: &[F]) -> String {
    nums(vs.iter().map(|v| f_u32(*v)))
}
/// A Merkle digest as its 8 canonical BabyBear lanes.
fn digest_json(d: &[F; DIGEST_ELEMS]) -> String {
    nums(d.iter().map(|v| f_u32(*v)))
}
/// A `MerkleCap` at `cap_height = 0` — one root, 8 lanes.
fn cap_json(cap: &Commitment) -> String {
    let roots = cap.roots();
    assert_eq!(
        roots.len(),
        1,
        "cap_height 0 means a single root; this config builds every MMCS with cap_height 0"
    );
    digest_json(&roots[0])
}
fn path_json(path: &[[F; DIGEST_ELEMS]]) -> String {
    arr(path.iter().map(digest_json))
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

fn log2_strict(n: usize) -> usize {
    assert!(n.is_power_of_two(), "{n} is not a power of two");
    n.trailing_zeros() as usize
}

fn reverse_bits_len(x: usize, bits: usize) -> usize {
    let mut out = 0usize;
    for i in 0..bits {
        out |= ((x >> i) & 1) << (bits - 1 - i);
    }
    out
}

// ===========================================================================
// The AIR set — `rebuild_airs_pvs_common`'s reconstruction, outside the crate.
// ===========================================================================

/// The four table provers `verify_recursive_batch_proof_with_config` registers, in ITS
/// registration order (`plonky3_recursion_impl.rs:822-831`).
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
/// `BatchStarkProver::rebuild_airs_pvs_common::<4>` (private), reproduced. Identical to
/// `root_air_instance.rs`'s; both need the DEPLOYED shapes (`with_min_height`,
/// `with_horner_pack_k`), not a census-style bare constructor.
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

/// Replay `verify_batch`'s transcript up to and including `sample_zeta`, using p3's OWN
/// `BatchTranscript` methods in p3's OWN order (`batch-stark/src/verifier/mod.rs:144,274-300`),
/// and RETURN the transcript so its challenger can be carried into the PCS.
fn replay_to_zeta(
    config: &SC,
    proof: &BatchStarkProof<SC>,
    airs: &[CircuitTableAir<SC, D>],
    pvs: &[Vec<F>],
    common: &p3_batch_stark::CommonData<SC>,
    preprocessed_widths: &[usize],
) -> (BatchTranscript<SC>, EF, EF) {
    let p = &proof.proof;
    assert_eq!(
        config.is_zk(),
        0,
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
    let _per_instance = t.sample_perm_challenges(&common.lookups, &LogUpGadget);
    // ⚑ The AIR's constraint-folding alpha. It is NOT the FRI batch-combination alpha sampled
    // later inside `verify_fri`; both are called `alpha` in p3 and they are different numbers.
    let air_alpha =
        t.observe_perm_and_sample_alpha(p.commitments.permutation.as_ref(), &p.global_lookup_data);
    t.observe_quotient_commitment(&p.commitments.quotient_chunks);
    assert!(
        p.commitments.random.is_none(),
        "a random commitment means ZK is on, which this replay does not model"
    );
    let zeta = t.sample_zeta();

    (t, air_alpha, zeta)
}

// ===========================================================================
// The PCS round structure — `verify_batch`'s `coms_to_verify`, outside the crate.
// ===========================================================================

/// Which committed round a matrix belongs to, and what an AIR-side reader calls it.
#[derive(Clone)]
struct MatMeta {
    round: usize,
    matrix: usize,
    instance: usize,
    table: String,
    kind: &'static str,
    /// `Some(k)` for the k-th quotient chunk of its instance; `None` otherwise.
    chunk: Option<usize>,
    log_height: usize,
    width: usize,
}

// ===========================================================================
// `open_input` — p3-fri `verifier.rs:524`, replicated so the reduced openings can be emitted.
// ===========================================================================

/// Returns the per-log-height reduced openings DESCENDING by height (p3's own order), plus the
/// per-round index each batch's Merkle opening was checked at. Includes the REAL
/// `val_mmcs.verify_batch`, so a mis-built round structure fails here and not in o1js.
#[allow(clippy::type_complexity)]
fn open_input_replica(
    log_blowup: usize,
    log_global_max_height: usize,
    index: usize,
    input_proof: &[BatchOpening<F, MyMmcs>],
    alpha: EF,
    val_mmcs: &MyMmcs,
    coms: &[ComRound],
) -> Result<(Vec<(usize, EF)>, Vec<usize>), String> {
    if input_proof.len() != coms.len() {
        return Err(format!(
            "input proof has {} batches, expected {}",
            input_proof.len(),
            coms.len()
        ));
    }
    // log_height -> (alpha_pow, reduced_opening)
    let mut reduced = BTreeMap::<usize, (EF, EF)>::new();
    let mut reduced_indices = Vec::with_capacity(coms.len());

    for (batch_opening, (batch_commit, mats)) in input_proof.iter().zip(coms.iter()) {
        let batch_heights: Vec<usize> = mats
            .iter()
            .map(|(domain, _)| domain.size() << log_blowup)
            .collect();
        let batch_dims: Vec<Dimensions> = batch_heights
            .iter()
            // p3 puts 0 here: the MMCS does not use the width for verification.
            .map(|&height| Dimensions { width: 0, height })
            .collect();
        let reduced_index = batch_heights
            .iter()
            .max()
            .map(|&h| index >> (log_global_max_height - log2_strict(h)))
            .unwrap_or(0);
        reduced_indices.push(reduced_index);

        if batch_opening.opened_values.len() != mats.len() {
            return Err(format!(
                "batch has {} opened rows for {} matrices",
                batch_opening.opened_values.len(),
                mats.len()
            ));
        }

        val_mmcs
            .verify_batch(
                batch_commit,
                &batch_dims,
                reduced_index,
                BatchOpeningRef::new(&batch_opening.opened_values, &batch_opening.opening_proof),
            )
            .map_err(|e| format!("input batch opening failed host-side verification: {e:?}"))?;

        for (mat_opening, (mat_domain, mat_points_and_values)) in
            batch_opening.opened_values.iter().zip(mats.iter())
        {
            let log_height = log2_strict(mat_domain.size()) + log_blowup;
            let bits_reduced = log_global_max_height - log_height;
            let rev_reduced_index = reverse_bits_len(index >> bits_reduced, log_height);
            let x =
                F::GENERATOR * F::two_adic_generator(log_height).exp_u64(rev_reduced_index as u64);

            let (alpha_pow, ro) = reduced.entry(log_height).or_insert((EF::ONE, EF::ZERO));
            for (z, ps_at_z) in mat_points_and_values {
                let quotient = (*z - EF::from(x)).inverse();
                if mat_opening.len() != ps_at_z.len() {
                    return Err("opened-width mismatch between input proof and round".into());
                }
                for (&p_at_x, &p_at_z) in mat_opening.iter().zip(ps_at_z.iter()) {
                    *ro += *alpha_pow * (p_at_z - EF::from(p_at_x)) * quotient;
                    *alpha_pow *= alpha;
                }
            }
        }
    }

    Ok((
        reduced
            .into_iter()
            .rev()
            .map(|(lh, (_, ro))| (lh, ro))
            .collect(),
        reduced_indices,
    ))
}

// ===========================================================================
// Per-query FRI data, as emitted.
// ===========================================================================

struct QueryOut {
    index: usize,
    input_batches: Vec<InputBatchOut>,
    reduced_openings: Vec<(usize, EF)>,
    commit_phase: Vec<CommitStepOut>,
    roll_ins: Vec<(usize, EF)>,
    folded_after_round: Vec<EF>,
}

struct InputBatchOut {
    reduced_index: usize,
    rows: Vec<Vec<F>>,
    path: Vec<[F; DIGEST_ELEMS]>,
}

struct CommitStepOut {
    log_arity: usize,
    sibling: EF,
    path: Vec<[F; DIGEST_ELEMS]>,
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

    // ---- SELF-CHECK 1: p3's OWN verifier accepts ---------------------------
    let config = ir2_leaf_wrap_config();
    let t_verify = Instant::now();
    verify_recursive_batch_proof_with_config(&root, &config)
        .unwrap_or_else(|e| panic!("the committed root does NOT verify: {e}"));
    eprintln!("p3 verify_batch accepted in {:?}", t_verify.elapsed());

    assert_eq!(
        root.proof.degree_bits.as_slice(),
        EXPECTED_DEGREE_BITS.as_slice(),
        "the root batch's instance shape moved; every height-derived field below is keyed to it, \
         so update EXPECTED_DEGREE_BITS deliberately rather than letting the JSON change shape"
    );

    // ---- rebuild the AIRs, public values and lookup contexts ---------------
    let (airs, pvs, names) =
        rebuild_airs(&config, &root).unwrap_or_else(|e| panic!("AIR reconstruction failed: {e}"));

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

    // ---- the pre-FRI transcript, replayed ----------------------------------
    let (transcript, air_alpha, zeta) =
        replay_to_zeta(&config, &root, &airs, &pvs, &common, &preprocessed_widths);

    // ---- the PCS round structure — `verify_batch`'s `coms_to_verify` -------
    let p = &root.proof;
    let pcs = config.pcs();
    let mut coms: Vec<ComRound> = Vec::new();
    let mut metas: Vec<Vec<MatMeta>> = Vec::new();
    let mut round_kinds: Vec<&'static str> = Vec::new();

    let trace_domains: Vec<Domain> = p
        .degree_bits
        .iter()
        .map(|&db| <MyPcs as Pcs<EF, Challenger>>::natural_domain_for_degree(pcs, 1usize << db))
        .collect();
    let zeta_nexts: Vec<EF> = trace_domains
        .iter()
        .map(|d| {
            d.next_point(zeta)
                .expect("next_point exists for a two-adic coset")
        })
        .collect();

    let log_blowup = IR2_INNER_LOG_BLOWUP;
    let log_final_poly_len = IR2_INNER_LOG_FINAL_POLY_LEN;
    let commit_pow_bits = IR2_INNER_COMMIT_POW_BITS;
    let query_pow_bits = IR2_INNER_QUERY_POW_BITS;
    let max_log_arity = INNER_FRI_MAX_LOG_ARITY;
    let num_queries = INNER_FRI_NUM_QUERIES;

    let mat_meta = |round: usize,
                    matrix: usize,
                    instance: usize,
                    kind: &'static str,
                    chunk: Option<usize>,
                    domain: &Domain,
                    width: usize| MatMeta {
        round,
        matrix,
        instance,
        table: names[instance].clone(),
        kind,
        chunk,
        log_height: log2_strict(domain.size()) + log_blowup,
        width,
    };

    // Round 0 — the main (trace) commitment. One matrix per instance, opened at `zeta` and, if
    // the AIR reads a next row, at `zeta_next`.
    {
        let r = coms.len();
        let mut round = Vec::with_capacity(n);
        let mut meta = Vec::with_capacity(n);
        for i in 0..n {
            let ov = &p.opened_values.instances[i].base_opened_values;
            let reads_next =
                !<CircuitTableAir<SC, D> as BaseAir<F>>::main_next_row_columns(&airs[i]).is_empty();
            assert_eq!(
                reads_next,
                ov.trace_next.is_some(),
                "instance {i} ({}): the AIR's next-row column set and the proof's trace_next \
                 disagree, so the opening point count would be wrong",
                names[i]
            );
            let mut points = vec![(zeta, ov.trace_local.clone())];
            if reads_next {
                points.push((
                    zeta_nexts[i],
                    ov.trace_next.clone().expect("checked immediately above"),
                ));
            }
            meta.push(mat_meta(
                r,
                i,
                i,
                "main",
                None,
                &trace_domains[i],
                ov.trace_local.len(),
            ));
            round.push((trace_domains[i], points));
        }
        coms.push((p.commitments.main.clone(), round));
        metas.push(meta);
        round_kinds.push("main");
    }

    // Round 1 — the aggregated quotient-chunk commitment, flattened instance-major. ⚑ The
    // committed domain is the NATURAL domain of the chunk's size (shift 1), not the split
    // domain's coset: `verify_batch` re-derives it through `natural_domain_for_degree`.
    {
        let r = coms.len();
        let mut round = Vec::new();
        let mut meta = Vec::new();
        for i in 0..n {
            let ov = &p.opened_values.instances[i].base_opened_values;
            let n_chunks = ov.quotient_chunks.len();
            assert!(
                n_chunks.is_power_of_two(),
                "n_chunks is 1 << log_num_chunks"
            );
            let log_num_chunks = log2_strict(n_chunks);
            let quotient_domain =
                trace_domains[i].create_disjoint_domain(1 << (p.degree_bits[i] + log_num_chunks));
            for (k, vals) in quotient_domain
                .split_domains(n_chunks)
                .into_iter()
                .zip(ov.quotient_chunks.iter())
            {
                let dom = <MyPcs as Pcs<EF, Challenger>>::natural_domain_for_degree(pcs, k.size());
                meta.push(mat_meta(
                    r,
                    meta.len(),
                    i,
                    "quotient_chunk",
                    Some(meta.iter().filter(|m: &&MatMeta| m.instance == i).count()),
                    &dom,
                    vals.len(),
                ));
                round.push((dom, vec![(zeta, vals.clone())]));
            }
        }
        coms.push((p.commitments.quotient_chunks.clone(), round));
        metas.push(meta);
        round_kinds.push("quotient_chunk");
    }

    // Round 2 — the single global preprocessed commitment, one matrix per instance that has
    // preprocessed columns, in `matrix_to_instance` order.
    if let Some(global) = &common.preprocessed {
        let r = coms.len();
        let mut round = Vec::new();
        let mut meta = Vec::new();
        for (matrix_index, &inst) in global.matrix_to_instance.iter().enumerate() {
            let ov = &p.opened_values.instances[inst].base_opened_values;
            let local = ov
                .preprocessed_local
                .as_ref()
                .unwrap_or_else(|| panic!("instance {inst} is preprocessed but has no local row"));
            let m = global.instances[inst]
                .as_ref()
                .unwrap_or_else(|| panic!("instance {inst} has no preprocessed metadata"));
            assert_eq!(m.matrix_index, matrix_index);
            assert_eq!(m.degree_bits, p.degree_bits[inst]);
            let dom = <MyPcs as Pcs<EF, Challenger>>::natural_domain_for_degree(
                pcs,
                1usize << m.degree_bits,
            );
            let reads_next =
                !<CircuitTableAir<SC, D> as BaseAir<F>>::preprocessed_next_row_columns(&airs[inst])
                    .is_empty();
            assert_eq!(
                reads_next,
                ov.preprocessed_next.is_some(),
                "instance {inst} ({}): the AIR's preprocessed next-row column set and the proof's \
                 preprocessed_next disagree",
                names[inst]
            );
            let mut points = vec![(zeta, local.clone())];
            if reads_next {
                points.push((
                    zeta_nexts[inst],
                    ov.preprocessed_next.clone().expect("checked above"),
                ));
            }
            meta.push(mat_meta(
                r,
                matrix_index,
                inst,
                "preprocessed",
                None,
                &dom,
                local.len(),
            ));
            round.push((dom, points));
        }
        coms.push((global.commitment.clone(), round));
        metas.push(meta);
        round_kinds.push("preprocessed");
    }

    // Round 3 — the LogUp permutation commitment. Only instances with a non-empty aux row
    // appear, so the matrix index is NOT the instance index; `instance` in `openedEvals` is.
    if let Some(perm_commit) = &p.commitments.permutation {
        let r = coms.len();
        let mut round = Vec::new();
        let mut meta = Vec::new();
        for i in 0..n {
            let inst = &p.opened_values.instances[i];
            assert_eq!(inst.permutation_local.len(), inst.permutation_next.len());
            if inst.permutation_local.is_empty() {
                continue;
            }
            meta.push(mat_meta(
                r,
                meta.len(),
                i,
                "permutation",
                None,
                &trace_domains[i],
                inst.permutation_local.len(),
            ));
            round.push((
                trace_domains[i],
                vec![
                    (zeta, inst.permutation_local.clone()),
                    (zeta_nexts[i], inst.permutation_next.clone()),
                ],
            ));
        }
        coms.push((perm_commit.clone(), round));
        metas.push(meta);
        round_kinds.push("permutation");
    }

    // ---- SELF-CHECK 2: the REAL pcs.verify accepts from the mirrored state --
    // It re-observes the opened values itself, re-samples the whole FRI transcript and
    // re-checks every Merkle opening and fold chain. A drifted prefix or a mis-built round
    // structure is rejected here.
    {
        let mut ch = transcript.challenger.clone();
        <MyPcs as Pcs<EF, Challenger>>::verify(pcs, coms.clone(), &p.opening_proof, &mut ch)
            .unwrap_or_else(|e| {
                panic!(
                    "the REAL pcs.verify REJECTED from the mirrored transcript state — the \
                     replayed prefix or the round structure diverges from verify_batch, and every \
                     field below would have been well-formed and wrong: {e:?}"
                )
            });
    }

    // ---- the challenger state at `verify_fri`'s door -----------------------
    // `two_adic_pcs.rs:782-788`: pcs.verify observes every claimed evaluation, in round /
    // matrix / point order, and then hands the challenger to `verify_fri`.
    let mut ch = transcript.challenger.clone();
    for (_, round) in &coms {
        for (_, mat) in round {
            for (_, values) in mat {
                ch.observe_algebra_slice(values);
            }
        }
    }
    // ⚑ THE field. Snapshot BEFORE FRI's alpha is drawn.
    let fri_entry_state = ch.clone();

    // ---- the FRI transcript, replayed --------------------------------------
    let fri = &p.opening_proof;
    let layers = fri.commit_phase_commits.len();
    assert_eq!(
        layers, EXPECTED_LAYERS,
        "commit-phase layer count moved; the fold chain's length is a protocol shape"
    );
    assert_eq!(
        fri.commit_pow_witnesses.len(),
        layers,
        "one commit-phase PoW witness per layer"
    );
    assert_eq!(
        fri.query_proofs.len(),
        num_queries,
        "the config pins {num_queries} queries"
    );
    assert_eq!(
        fri.final_poly.len(),
        1usize << log_final_poly_len,
        "log_final_poly_len {log_final_poly_len} means a final polynomial of that length"
    );

    let log_arities: Vec<usize> = fri.query_proofs[0]
        .commit_phase_openings
        .iter()
        .map(|s| s.log_arity as usize)
        .collect();
    for (qi, qp) in fri.query_proofs.iter().enumerate() {
        assert_eq!(
            qp.commit_phase_openings.len(),
            layers,
            "query {qi} has the wrong number of commit-phase openings"
        );
        for (r, step) in qp.commit_phase_openings.iter().enumerate() {
            let la = step.log_arity as usize;
            assert!(
                la >= 1 && la <= max_log_arity,
                "query {qi} round {r}: log_arity {la} outside 1..={max_log_arity}"
            );
            assert_eq!(
                la, log_arities[r],
                "query {qi} round {r}: arity schedule differs"
            );
            assert_eq!(
                step.sibling_values.len(),
                (1 << la) - 1,
                "query {qi} round {r}: sibling count must be arity - 1"
            );
        }
    }
    let log_global_max_height: usize =
        log_arities.iter().sum::<usize>() + log_blowup + log_final_poly_len;
    assert_eq!(
        log_global_max_height, EXPECTED_LOG_GLOBAL_MAX_HEIGHT,
        "the query index width is the protocol's, not a convenience"
    );
    let max_db = *p.degree_bits.iter().max().expect("seven instances");
    assert_eq!(
        max_db + log_blowup,
        log_global_max_height,
        "the tallest committed matrix must be the FRI chain's starting height"
    );
    let log_final_height = log_blowup + log_final_poly_len;

    // The real MMCSes, rebuilt from the same deterministic permutation the config uses. The
    // compiler forces these to be the types the decoded proof carries.
    let perm = default_babybear_poseidon2_16();
    let val_mmcs = MyMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm), 0);
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let folding: TwoAdicFriFolding<Vec<BatchOpening<F, MyMmcs>>, <MyMmcs as Mmcs<F>>::Error> =
        TwoAdicFriFolding(core::marker::PhantomData);

    // `verifier.rs:143` — the PCS batch-combination alpha, distinct from the AIR's alpha.
    let fri_alpha: EF = ch.sample_algebra_element();

    // `verifier.rs:214-227` — observe each commit, check its PoW, sample its beta.
    let mut betas: Vec<EF> = Vec::with_capacity(layers);
    for (r, (comm, witness)) in fri
        .commit_phase_commits
        .iter()
        .zip(fri.commit_pow_witnesses.iter())
        .enumerate()
    {
        ch.observe(comm.clone());
        assert!(
            ch.check_witness(commit_pow_bits, *witness),
            "layer {r}: commit-phase PoW witness failed"
        );
        betas.push(ch.sample_algebra_element());
    }
    ch.observe_algebra_slice(&fri.final_poly);
    for &la in &log_arities {
        ch.observe(F::from_usize(la));
    }
    assert!(
        ch.check_witness(query_pow_bits, fri.query_pow_witness),
        "the query PoW witness failed at {query_pow_bits} bits — the mirrored challenger state \
         entering verify_fri is wrong"
    );

    // ---- SELF-CHECKS 3, 4, 6: every query, host-verified --------------------
    let mut queries: Vec<QueryOut> = Vec::with_capacity(num_queries);
    let mut roll_in_schedule: Option<Vec<usize>> = None;

    for (qi, qp) in fri.query_proofs.iter().enumerate() {
        // `extra_query_index_bits() == 0` for TwoAdicFriFolding.
        let index = ch.sample_bits(log_global_max_height);

        let (ro, reduced_indices) = open_input_replica(
            log_blowup,
            log_global_max_height,
            index,
            &qp.input_proof,
            fri_alpha,
            &val_mmcs,
            &coms,
        )
        .unwrap_or_else(|e| panic!("query {qi}: open_input replica failed: {e}"));

        assert_eq!(
            ro.first().map(|(lh, _)| *lh),
            Some(log_global_max_height),
            "query {qi}: the initial reduced opening must sit at the global max height, which is \
             what makes the fold chain a statement about the tallest committed matrix"
        );

        // Serialise the input batches (already host-verified inside the replica).
        assert_eq!(
            qp.input_proof.len(),
            coms.len(),
            "query {qi}: input batch count must match the round count"
        );
        let mut input_batches = Vec::with_capacity(coms.len());
        for (ri, (batch, meta)) in qp.input_proof.iter().zip(metas.iter()).enumerate() {
            assert_eq!(
                batch.opened_values.len(),
                meta.len(),
                "query {qi} round {ri}: opened row count must match the matrix count"
            );
            for (row, m) in batch.opened_values.iter().zip(meta.iter()) {
                assert_eq!(
                    row.len(),
                    m.width,
                    "query {qi} round {ri}: opened row width must match the matrix width"
                );
            }
            let max_lh = meta
                .iter()
                .map(|m| m.log_height)
                .max()
                .expect("non-empty round");
            assert_eq!(
                batch.opening_proof.len(),
                max_lh,
                "query {qi} round {ri}: the Merkle path length must be the tree height \
                 (cap_height 0)"
            );
            input_batches.push(InputBatchOut {
                reduced_index: reduced_indices[ri],
                rows: batch.opened_values.clone(),
                path: batch.opening_proof.clone(),
            });
        }

        // The fold chain — `verify_query`, with the intermediate values kept.
        let mut ro_iter = ro[1..].iter().peekable();
        let mut folded = ro[0].1;
        let mut domain_index = index;
        let mut log_current = log_global_max_height;
        let mut commit_phase = Vec::with_capacity(layers);
        let mut roll_ins: Vec<(usize, EF)> = Vec::new();
        let mut folded_after_round = Vec::with_capacity(layers);
        let mut q_roll_rounds: Vec<usize> = Vec::new();

        for (r, step) in qp.commit_phase_openings.iter().enumerate() {
            let log_arity = step.log_arity as usize;
            let arity = 1usize << log_arity;
            let index_in_group = domain_index % arity;
            let mut evals = vec![EF::ZERO; arity];
            evals[index_in_group] = folded;
            let mut sib = 0usize;
            for (j, e) in evals.iter_mut().enumerate() {
                if j != index_in_group {
                    *e = step.sibling_values[sib];
                    sib += 1;
                }
            }
            let log_folded = log_current - log_arity;
            domain_index >>= log_arity;

            challenge_mmcs
                .verify_batch(
                    &fri.commit_phase_commits[r],
                    &[Dimensions {
                        width: arity,
                        height: 1 << log_folded,
                    }],
                    domain_index,
                    BatchOpeningRef::new(core::slice::from_ref(&evals), &step.opening_proof),
                )
                .unwrap_or_else(|e| {
                    panic!("query {qi} layer {r}: commit-phase Merkle opening failed: {e:?}")
                });

            folded = <TwoAdicFriFolding<_, _> as FriFoldingStrategy<F, EF>>::fold_row(
                &folding,
                domain_index,
                log_folded,
                log_arity,
                betas[r],
                evals.iter().copied(),
            );
            log_current = log_folded;

            if let Some((_, v)) = ro_iter.next_if(|(lh, _)| *lh == log_current) {
                folded += betas[r].exp_power_of_2(log_arity) * *v;
                roll_ins.push((r, *v));
                q_roll_rounds.push(r);
            }

            assert_eq!(
                step.sibling_values.len(),
                1,
                "arity 2 means exactly one sibling per layer"
            );
            commit_phase.push(CommitStepOut {
                log_arity,
                sibling: step.sibling_values[0],
                path: step.opening_proof.clone(),
            });
            folded_after_round.push(folded);
        }

        assert_eq!(
            log_current, log_final_height,
            "query {qi}: the fold chain ended at the wrong height"
        );
        assert!(
            ro_iter.next().is_none(),
            "query {qi}: reduced openings were left unconsumed"
        );
        // log_final_poly_len = 0: the final polynomial is a CONSTANT, so its evaluation at the
        // query point is coefficient 0 and no Horner pass is needed.
        assert_eq!(
            folded, fri.final_poly[0],
            "query {qi}: the fold chain does not land on the constant final polynomial — the \
             mirrored FRI transcript has drifted"
        );

        match &roll_in_schedule {
            None => roll_in_schedule = Some(q_roll_rounds.clone()),
            Some(expected) => assert_eq!(
                *expected, q_roll_rounds,
                "query {qi}: the roll-in schedule differs from query 0's — the schedule is a \
                 function of the committed heights alone and cannot vary per query"
            ),
        }

        queries.push(QueryOut {
            index,
            input_batches,
            reduced_openings: ro,
            commit_phase,
            roll_ins,
            folded_after_round,
        });
    }

    // ---- SELF-CHECK 5: the 19 indices are pairwise distinct -----------------
    let idx_list: Vec<usize> = queries.iter().map(|q| q.index).collect();
    let distinct: BTreeSet<usize> = idx_list.iter().copied().collect();
    assert_eq!(
        distinct.len(),
        idx_list.len(),
        "the {} query indices are NOT pairwise distinct ({} distinct) — colliding indices make a \
         substitution falsifier a no-op, which is how a prior leg in this repo went green",
        idx_list.len(),
        distinct.len()
    );
    eprintln!("query indices ({}): {:?}", idx_list.len(), idx_list);

    // ---- the census --------------------------------------------------------
    let heights: BTreeSet<usize> = metas
        .iter()
        .flat_map(|r| r.iter().map(|m| m.log_height))
        .collect();
    let total_path_levels: usize = queries
        .iter()
        .map(|q| {
            q.input_batches.iter().map(|b| b.path.len()).sum::<usize>()
                + q.commit_phase.iter().map(|s| s.path.len()).sum::<usize>()
        })
        .sum();
    let total_opened_base: usize = queries
        .iter()
        .map(|q| {
            q.input_batches
                .iter()
                .map(|b| b.rows.iter().map(Vec::len).sum::<usize>())
                .sum::<usize>()
        })
        .sum();
    eprintln!(
        "census: layers={layers} queries={} rounds={} distinct_input_heights={} ({:?}) \
         total_path_levels={total_path_levels} total_opened_base_elements={total_opened_base}",
        queries.len(),
        coms.len(),
        heights.len(),
        heights.iter().rev().collect::<Vec<_>>(),
    );

    // ---- emit ---------------------------------------------------------------
    let json = emit(
        &env_v5,
        &root,
        &names,
        &coms,
        &metas,
        &round_kinds,
        &fri_entry_state,
        air_alpha,
        zeta,
        fri_alpha,
        &betas,
        &queries,
        Knobs {
            log_blowup,
            log_final_poly_len,
            commit_pow_bits,
            query_pow_bits,
            max_log_arity,
            num_queries,
            log_global_max_height,
            layers,
        },
    );
    match &out_path {
        Some(pth) => {
            std::fs::write(pth, &json).unwrap_or_else(|e| panic!("cannot write {pth}: {e}"));
            eprintln!("wrote {pth} ({} bytes)", json.len());
        }
        None => {
            eprintln!("emitted {} bytes to stdout", json.len());
            println!("{json}");
        }
    }
    eprintln!("total wall time {:?}", t_start.elapsed());
}

/// Resolve a repo-relative path from either the workspace root or `circuit-prove/`.
fn repo_relative(rel: &str) -> std::path::PathBuf {
    let here = std::path::Path::new(rel);
    if here.exists() {
        return here.to_path_buf();
    }
    let manifest = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let from_root = manifest.parent().unwrap_or(manifest).join(rel);
    if from_root.exists() {
        return from_root;
    }
    here.to_path_buf()
}

struct Knobs {
    log_blowup: usize,
    log_final_poly_len: usize,
    commit_pow_bits: usize,
    query_pow_bits: usize,
    max_log_arity: usize,
    num_queries: usize,
    log_global_max_height: usize,
    layers: usize,
}

#[allow(clippy::too_many_arguments)]
fn emit(
    env_v5: &WholeChainProofBytes,
    root: &BatchStarkProof<SC>,
    names: &[String],
    coms: &[ComRound],
    metas: &[Vec<MatMeta>],
    round_kinds: &[&'static str],
    fri_entry_state: &Challenger,
    air_alpha: EF,
    zeta: EF,
    fri_alpha: EF,
    betas: &[EF],
    queries: &[QueryOut],
    k: Knobs,
) -> String {
    let p = &root.proof;
    let fri = &p.opening_proof;

    let mut o = String::new();
    o.push('{');
    write!(o, r#""kind":"dregg-root-fri-instance","#).unwrap();
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
    write!(o, r#""tables":{},"#, arr(names.iter().map(|s| json_str(s)))).unwrap();
    write!(
        o,
        r#""knobs":{{"logBlowup":{},"logFinalPolyLen":{},"commitPowBits":{},"queryPowBits":{},"maxLogArity":{},"numQueries":{},"logGlobalMaxHeight":{},"layers":{},"finalPolyLen":{}}},"#,
        k.log_blowup,
        k.log_final_poly_len,
        k.commit_pow_bits,
        k.query_pow_bits,
        k.max_log_arity,
        k.num_queries,
        k.log_global_max_height,
        k.layers,
        fri.final_poly.len(),
    )
    .unwrap();

    // ⚑ THE field the o1js circuit starts from. Sponge lanes, then the two buffers, all
    // canonical. `DuplexChallenger` exposes all three, so nothing here is reconstructed.
    write!(
        o,
        r#""challengerStateBeforeFriAlpha":{{"width":{WIDTH},"rate":{RATE},"sponge":{},"inputBuffer":{},"outputBuffer":{}}},"#,
        f_list(&fri_entry_state.sponge_state),
        f_list(&fri_entry_state.input_buffer),
        f_list(&fri_entry_state.output_buffer),
    )
    .unwrap();

    // `zeta` and `airAlpha` are carried so a reader can line this file up against
    // `root_air_instance`'s output without re-deriving anything.
    write!(
        o,
        r#""zeta":{},"airAlpha":{},"friAlpha":{},"#,
        ef_json(zeta),
        ef_json(air_alpha),
        ef_json(fri_alpha)
    )
    .unwrap();
    write!(o, r#""betas":{},"#, ef_list(betas)).unwrap();
    write!(
        o,
        r#""commits":{},"#,
        arr(fri.commit_phase_commits.iter().map(cap_json))
    )
    .unwrap();
    write!(
        o,
        r#""commitPowWitnesses":{},"#,
        f_list(&fri.commit_pow_witnesses)
    )
    .unwrap();
    write!(
        o,
        r#""finalPoly":{},"queryPowWitness":{},"#,
        ef_list(&fri.final_poly),
        f_u32(fri.query_pow_witness)
    )
    .unwrap();

    // The round structure, in p3's own order, with each round's input commitment.
    let mut rounds_json = Vec::with_capacity(coms.len());
    for (ri, ((commit, round), meta)) in coms.iter().zip(metas.iter()).enumerate() {
        let mats = arr(round.iter().zip(meta.iter()).map(|((_, points), m)| {
            format!(
                r#"{{"matrix":{},"instance":{},"table":{},"kindName":"{}","chunk":{},"logHeight":{},"width":{},"points":{}}}"#,
                m.matrix,
                m.instance,
                json_str(&m.table),
                m.kind,
                match m.chunk {
                    Some(c) => c.to_string(),
                    None => "null".to_string(),
                },
                m.log_height,
                m.width,
                arr(points.iter().map(|(z, _)| ef_json(*z))),
            )
        }));
        rounds_json.push(format!(
            r#"{{"round":{ri},"kindName":"{}","commit":{},"matrices":{mats}}}"#,
            round_kinds[ri],
            cap_json(commit),
        ));
    }
    write!(o, r#""inputRounds":{},"#, arr(rounds_json)).unwrap();

    // ⚑ The labels are load-bearing. An o1js lane reading `main[2][17]` on the AIR side needs
    // to know that it is this entry's `values[17]`, at round 0, matrix 2, point 0.
    let mut opened = Vec::new();
    for ((_, round), meta) in coms.iter().zip(metas.iter()) {
        for ((_, points), m) in round.iter().zip(meta.iter()) {
            for (pi, (z, values)) in points.iter().enumerate() {
                opened.push(format!(
                    r#"{{"round":{},"matrix":{},"instance":{},"table":{},"kindName":"{}","chunk":{},"logHeight":{},"pointIndex":{pi},"point":{},"values":{}}}"#,
                    m.round,
                    m.matrix,
                    m.instance,
                    json_str(&m.table),
                    m.kind,
                    match m.chunk {
                        Some(c) => c.to_string(),
                        None => "null".to_string(),
                    },
                    m.log_height,
                    ef_json(*z),
                    ef_list(values),
                ));
            }
        }
    }
    write!(o, r#""openedEvals":{},"#, arr(opened)).unwrap();

    let qs = arr(queries.iter().map(|q| {
        let batches = arr(q.input_batches.iter().zip(metas.iter()).enumerate().map(
            |(ri, (b, meta))| {
                format!(
                    r#"{{"round":{ri},"reducedIndex":{},"matrices":{},"rows":{},"path":{}}}"#,
                    b.reduced_index,
                    arr(meta.iter().map(|m| format!(
                        r#"{{"logHeight":{},"width":{}}}"#,
                        m.log_height, m.width
                    ))),
                    arr(b.rows.iter().map(|r| f_list(r))),
                    path_json(&b.path),
                )
            },
        ));
        let ros = arr(q.reduced_openings.iter().map(|(lh, v)| {
            format!(r#"{{"logHeight":{lh},"ro":{}}}"#, ef_json(*v))
        }));
        let cp = arr(q.commit_phase.iter().map(|s| {
            format!(
                r#"{{"logArity":{},"sibling":{},"path":{}}}"#,
                s.log_arity,
                ef_json(s.sibling),
                path_json(&s.path)
            )
        }));
        let rolls = arr(q.roll_ins.iter().map(|(r, v)| {
            format!(r#"{{"afterRound":{r},"value":{}}}"#, ef_json(*v))
        }));
        format!(
            r#"{{"index":{},"inputBatches":{batches},"reducedOpenings":{ros},"commitPhase":{cp},"rollIns":{rolls},"foldedAfterRound":{}}}"#,
            q.index,
            ef_list(&q.folded_after_round),
        )
    }));
    write!(o, r#""queries":{qs}"#).unwrap();

    o.push('}');
    o.push('\n');
    o
}
