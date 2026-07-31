//! **The MUTATION DIFFERENTIAL harness — Rust oracle side.**
//!
//! A proof-systems review ranked in-circuit verifier fidelity as the #1 live risk: there is
//! no systematic differential that the o1js FRI verifier accepts iff dregg's native verifier
//! accepts. This binary is the native-oracle half of the measurement it named — random
//! single-felt mutations of dregg's REAL committed root proof, each fed to the deployed
//! FRI/PCS verifier, streamed alongside a faithful structural decode the o1js twin
//! (`RootFriWalk.ts`/`RootFriSlice.ts`) walks out of circuit. `scripts/fri-mutation-differential.ts`
//! is the twin half; it reads this binary's stdout and asserts verdict agreement.
//!
//! ```text
//!   cargo build -p dregg-circuit-prove --release --bin root_fri_mutation
//!   ./target/release/root_fri_mutation <seed> <ntrials>   # NDJSON on stdout, diagnostics on stderr
//! ```
//!
//! ## The oracle
//!
//! `<MyPcs as Pcs<EF, Challenger>>::verify` — dregg's deployed `TwoAdicFriPcs::verify`, the exact
//! object `RootFriWalk.ts` mirrors. It re-observes the opened values, re-samples the whole FRI
//! transcript from the mirrored challenger state, and re-checks every input-batch and commit-phase
//! Merkle opening and every fold chain against the constant final polynomial. It is the FRI half of
//! `verify_recursive_batch_proof_with_config`; we call it in isolation so the (currently regressed,
//! working-tree-only) AIR-constraint half — `ConstAir::eval`, a width mismatch against the committed
//! fixture under the uncommitted Cargo.lock — does not gate the FRI measurement. This is exactly the
//! surface the twin models; the AIR closing-equality half rides a separate twin (`RootAirChain.ts`).
//!
//! ## Faithfulness of the emitted twin input
//!
//! Each NDJSON line carries a FULL `dregg-root-fri-instance` decode of the mutated proof, produced
//! by the same structural path `root_fri_instance.rs` uses, with only its FATAL self-checks made
//! non-fatal (a mutated proof is meant to fail them). The `challengerStateBeforeFriAlpha` is
//! RE-DERIVED per mutation from the mutated proof's own transcript, so the twin re-derives the FRI
//! alpha, all betas and all query indices itself — it is not handed p3's numbers. The baseline
//! (unmutated) line MUST decode byte-for-byte to the committed `.fullchain/real-root-fri.json`; the
//! TS side asserts that, which pins this decode to the trusted emitter.

use std::collections::BTreeMap;
use std::env;
use std::fmt::Write as _;
use std::io::{BufWriter, Write as _IoWrite};

use dregg_circuit_prove::ivc_turn_chain::{
    IR2_INNER_COMMIT_POW_BITS, IR2_INNER_LOG_BLOWUP, IR2_INNER_LOG_FINAL_POLY_LEN,
    IR2_INNER_QUERY_POW_BITS, WholeChainProofBytes, ir2_leaf_wrap_config,
};
use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, INNER_FRI_MAX_LOG_ARITY, INNER_FRI_NUM_QUERIES,
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
use p3_commit::{BatchOpening, ExtensionMmcs, Mmcs, Pcs, PolynomialSpace};
use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField32, TwoAdicField};
use p3_fri::{FriFoldingStrategy, TwoAdicFriFolding};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};

type F = p3_baby_bear::BabyBear;
type EF = BinomialExtensionField<F, 4>;
type SC = DreggRecursionConfig;
const D: usize = 4;
const WIDTH: usize = 16;
const RATE: usize = 8;
const DIGEST_ELEMS: usize = 8;

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
type MyPcs = <SC as StarkGenericConfig>::Pcs;
type Challenger = <SC as StarkGenericConfig>::Challenger;
type Domain = <MyPcs as Pcs<EF, Challenger>>::Domain;
type Commitment = <MyPcs as Pcs<EF, Challenger>>::Commitment;
type ComRound = (Commitment, Vec<(Domain, Vec<(EF, Vec<EF>)>)>);

const FIXTURE: &str = "ugc-dregg/tests/fixtures/whole_history_proof.bin";
const EXPECTED_DEGREE_BITS: [usize; 7] = [10, 10, 16, 15, 3, 16, 0];
const EXPECTED_LOG_GLOBAL_MAX_HEIGHT: usize = 22;
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
fn digest_json(d: &[F; DIGEST_ELEMS]) -> String {
    nums(d.iter().map(|v| f_u32(*v)))
}
fn cap_json(cap: &Commitment) -> String {
    let roots = cap.roots();
    assert_eq!(roots.len(), 1, "cap_height 0 means a single root");
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
// Deterministic RNG — splitmix64. Reproducible from the CLI seed.
// ===========================================================================
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    /// A nonzero base-field delta in `[1, P-1]` — guarantees the target changes.
    fn nonzero_delta(&mut self) -> F {
        let order = F::ORDER_U32 as u64;
        F::from_usize((1 + (self.next() % (order - 1))) as usize)
    }
}

/// Bump base-field limb `l` of an extension element by a nonzero delta.
fn bump_ef(v: EF, l: usize, delta: F) -> EF {
    let coeffs: Vec<F> = v.as_basis_coefficients_slice().to_vec();
    EF::from_basis_coefficients_fn(|i| if i == l { coeffs[i] + delta } else { coeffs[i] })
}

// ===========================================================================
// The mutation site taxonomy. Every reachable single-felt position is a `Site`.
// ===========================================================================
// Some variants (opened values, pre-zeta commitments) are deliberately not enumerated in the
// FRI-pure scope but retained so `apply_site` documents the full taxonomy.
#[allow(dead_code)]
#[derive(Clone, Copy, Debug)]
enum OpenedKind {
    TraceLocal,
    TraceNext,
    QuotientChunk(usize),
    PrepLocal,
    PrepNext,
    PermLocal,
    PermNext,
}

#[allow(dead_code)]
#[derive(Clone, Copy, Debug)]
enum Site {
    Opened {
        inst: usize,
        kind: OpenedKind,
        idx: usize,
        limb: usize,
    },
    FinalPoly {
        idx: usize,
        limb: usize,
    },
    CommitPow {
        layer: usize,
    },
    QueryPow,
    InputRow {
        q: usize,
        round: usize,
        mat: usize,
        col: usize,
    },
    InputPath {
        q: usize,
        round: usize,
        level: usize,
        lane: usize,
    },
    CommitSibling {
        q: usize,
        layer: usize,
        limb: usize,
    },
    CommitPath {
        q: usize,
        layer: usize,
        level: usize,
        lane: usize,
    },
    CommitPhaseCommit {
        layer: usize,
        lane: usize,
    },
    MainCommit {
        lane: usize,
    },
    QuotientCommit {
        lane: usize,
    },
    PermCommit {
        lane: usize,
    },
}

fn region_of(s: &Site) -> &'static str {
    match s {
        Site::Opened { kind, .. } => match kind {
            OpenedKind::TraceLocal | OpenedKind::TraceNext => "opened_trace",
            OpenedKind::QuotientChunk(_) => "opened_quotient",
            OpenedKind::PrepLocal | OpenedKind::PrepNext => "opened_preprocessed",
            OpenedKind::PermLocal | OpenedKind::PermNext => "opened_permutation",
        },
        Site::FinalPoly { .. } => "final_poly",
        Site::CommitPow { .. } => "commit_pow_witness",
        Site::QueryPow => "query_pow_witness",
        Site::InputRow { .. } => "input_opened_row",
        Site::InputPath { .. } => "input_merkle_path",
        Site::CommitSibling { .. } => "commitphase_sibling_value",
        Site::CommitPath { .. } => "commitphase_merkle_path",
        Site::CommitPhaseCommit { .. } => "commitphase_commit_root",
        Site::MainCommit { .. } => "main_commit_root",
        Site::QuotientCommit { .. } => "quotient_commit_root",
        Site::PermCommit { .. } => "permutation_commit_root",
    }
}

/// Enumerate every single-felt site reachable in the proof structure, grouped by region so
/// the caller can stratify sampling and coverage per region.
fn enumerate_sites(root: &BatchStarkProof<SC>) -> BTreeMap<&'static str, Vec<Site>> {
    let p = &root.proof;
    let mut map: BTreeMap<&'static str, Vec<Site>> = BTreeMap::new();
    let mut push = |s: Site| map.entry(region_of(&s)).or_default().push(s);

    // ⚑ FRI-PURE SCOPE. We enumerate only positions the twin reads from the FRI instance and
    // that the FRI/PCS oracle sees — everything observed at or after `challengerStateBeforeFriAlpha`
    // plus the query openings and Merkle paths. The opened values at `zeta` and the pre-zeta
    // commitments (main/quotient/permutation) are SHARED with the AIR side: the twin reads some of
    // them from `airLanes` (the fixed `real-root-air.json`), so mutating only the FRI copy would
    // desync the two halves and manufacture a false disagreement. Those regions need the AIR twin
    // regenerated in lockstep and ride the AIR half's own differential — a named residual of this
    // FRI-only pass, and blocked here anyway by the `ConstAir::eval` regression in the AIR verify.
    let fri = &p.opening_proof;
    for idx in 0..fri.final_poly.len() {
        for limb in 0..D {
            push(Site::FinalPoly { idx, limb });
        }
    }
    for layer in 0..fri.commit_pow_witnesses.len() {
        push(Site::CommitPow { layer });
    }
    push(Site::QueryPow);

    for (layer, comm) in fri.commit_phase_commits.iter().enumerate() {
        for lane in 0..comm.roots()[0].len() {
            push(Site::CommitPhaseCommit { layer, lane });
        }
    }

    for (q, qp) in fri.query_proofs.iter().enumerate() {
        for (round, batch) in qp.input_proof.iter().enumerate() {
            for (mat, row) in batch.opened_values.iter().enumerate() {
                for col in 0..row.len() {
                    push(Site::InputRow { q, round, mat, col });
                }
            }
            for level in 0..batch.opening_proof.len() {
                for lane in 0..batch.opening_proof[level].len() {
                    push(Site::InputPath {
                        q,
                        round,
                        level,
                        lane,
                    });
                }
            }
        }
        for (layer, step) in qp.commit_phase_openings.iter().enumerate() {
            for _sib in 0..step.sibling_values.len() {
                for limb in 0..D {
                    push(Site::CommitSibling { q, layer, limb });
                }
            }
            for level in 0..step.opening_proof.len() {
                for lane in 0..step.opening_proof[level].len() {
                    push(Site::CommitPath {
                        q,
                        layer,
                        level,
                        lane,
                    });
                }
            }
        }
    }

    map
}

/// Apply a mutation at `site` to `root` in place. Returns a human description of the exact
/// position and the old→new canonical values.
fn apply_site(root: &mut BatchStarkProof<SC>, site: &Site, delta: F) -> String {
    let bump_cap = |cap: &mut Commitment, lane: usize| -> (u32, u32) {
        let mut roots = cap.clone().into_roots();
        let old = f_u32(roots[0][lane]);
        roots[0][lane] += delta;
        let new = f_u32(roots[0][lane]);
        *cap = Commitment::from(roots);
        (old, new)
    };
    let p = &mut root.proof;
    match *site {
        Site::Opened {
            inst,
            kind,
            idx,
            limb,
        } => {
            let instref = &mut p.opened_values.instances[inst];
            let target: &mut EF = match kind {
                OpenedKind::TraceLocal => &mut instref.base_opened_values.trace_local[idx],
                OpenedKind::TraceNext => {
                    &mut instref.base_opened_values.trace_next.as_mut().unwrap()[idx]
                }
                OpenedKind::QuotientChunk(c) => {
                    &mut instref.base_opened_values.quotient_chunks[c][idx]
                }
                OpenedKind::PrepLocal => &mut instref
                    .base_opened_values
                    .preprocessed_local
                    .as_mut()
                    .unwrap()[idx],
                OpenedKind::PrepNext => &mut instref
                    .base_opened_values
                    .preprocessed_next
                    .as_mut()
                    .unwrap()[idx],
                OpenedKind::PermLocal => &mut instref.permutation_local[idx],
                OpenedKind::PermNext => &mut instref.permutation_next[idx],
            };
            let old = ef_limbs(*target)[limb];
            *target = bump_ef(*target, limb, delta);
            let new = ef_limbs(*target)[limb];
            format!("inst{inst} {kind:?}[{idx}].limb{limb} {old}->{new}")
        }
        Site::FinalPoly { idx, limb } => {
            let t = &mut p.opening_proof.final_poly[idx];
            let old = ef_limbs(*t)[limb];
            *t = bump_ef(*t, limb, delta);
            format!("final_poly[{idx}].limb{limb} {old}->{}", ef_limbs(*t)[limb])
        }
        Site::CommitPow { layer } => {
            let t = &mut p.opening_proof.commit_pow_witnesses[layer];
            let old = f_u32(*t);
            *t += delta;
            format!("commit_pow_witness[{layer}] {old}->{}", f_u32(*t))
        }
        Site::QueryPow => {
            let t = &mut p.opening_proof.query_pow_witness;
            let old = f_u32(*t);
            *t += delta;
            format!("query_pow_witness {old}->{}", f_u32(*t))
        }
        Site::InputRow { q, round, mat, col } => {
            let t = &mut p.opening_proof.query_proofs[q].input_proof[round].opened_values[mat][col];
            let old = f_u32(*t);
            *t += delta;
            format!("q{q} round{round} row[{mat}][{col}] {old}->{}", f_u32(*t))
        }
        Site::InputPath {
            q,
            round,
            level,
            lane,
        } => {
            let t =
                &mut p.opening_proof.query_proofs[q].input_proof[round].opening_proof[level][lane];
            let old = f_u32(*t);
            *t += delta;
            format!(
                "q{q} round{round} path[{level}].lane{lane} {old}->{}",
                f_u32(*t)
            )
        }
        Site::CommitSibling { q, layer, limb } => {
            let t =
                &mut p.opening_proof.query_proofs[q].commit_phase_openings[layer].sibling_values[0];
            let old = ef_limbs(*t)[limb];
            *t = bump_ef(*t, limb, delta);
            format!(
                "q{q} layer{layer} sibling.limb{limb} {old}->{}",
                ef_limbs(*t)[limb]
            )
        }
        Site::CommitPath {
            q,
            layer,
            level,
            lane,
        } => {
            let t = &mut p.opening_proof.query_proofs[q].commit_phase_openings[layer].opening_proof
                [level][lane];
            let old = f_u32(*t);
            *t += delta;
            format!(
                "q{q} layer{layer} cp_path[{level}].lane{lane} {old}->{}",
                f_u32(*t)
            )
        }
        Site::CommitPhaseCommit { layer, lane } => {
            let (old, new) = bump_cap(&mut p.opening_proof.commit_phase_commits[layer], lane);
            format!("commit_phase_commits[{layer}].lane{lane} {old}->{new}")
        }
        Site::MainCommit { lane } => {
            let (old, new) = bump_cap(&mut p.commitments.main, lane);
            format!("commitments.main.lane{lane} {old}->{new}")
        }
        Site::QuotientCommit { lane } => {
            let (old, new) = bump_cap(&mut p.commitments.quotient_chunks, lane);
            format!("commitments.quotient.lane{lane} {old}->{new}")
        }
        Site::PermCommit { lane } => {
            let (old, new) = bump_cap(p.commitments.permutation.as_mut().unwrap(), lane);
            format!("commitments.permutation.lane{lane} {old}->{new}")
        }
    }
}

// ===========================================================================
// AIR reconstruction — `rebuild_airs_pvs_common`'s reconstruction, verbatim from
// `root_fri_instance.rs` (shape-invariant across value mutations, built once).
// ===========================================================================
fn deployed_table_provers() -> Vec<Box<dyn TableProver<SC>>> {
    let mut provers: Vec<Box<dyn TableProver<SC>>> = Vec::new();
    provers.extend(poseidon2_table_provers_d4::<SC>(
        Poseidon2Config::BABY_BEAR_D4_W16,
    ));
    provers.extend(poseidon2_table_provers_d4::<SC>(
        Poseidon2Config::BABY_BEAR_D4_W24,
    ));
    provers.extend(recompose_table_provers::<SC, D>(1, false));
    provers.extend(expose_claim_table_provers::<SC, D>());
    provers
}

fn rebuild_airs(
    config: &SC,
    proof: &BatchStarkProof<SC>,
) -> Result<(Vec<CircuitTableAir<SC, D>>, Vec<Vec<F>>, Vec<String>), String> {
    assert_eq!(proof.ext_degree, D);
    assert!(!proof.alu_quintic_trinomial);
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
// The pre-FRI transcript replay — p3's OWN `BatchTranscript`, in `verify_batch`'s order.
// ===========================================================================
fn replay_to_zeta(
    config: &SC,
    proof: &BatchStarkProof<SC>,
    airs: &[CircuitTableAir<SC, D>],
    pvs: &[Vec<F>],
    common: &p3_batch_stark::CommonData<SC>,
    preprocessed_widths: &[usize],
) -> (BatchTranscript<SC>, EF, EF) {
    let p = &proof.proof;
    assert_eq!(config.is_zk(), 0);
    let mut t = BatchTranscript::<SC>::new(config.initialise_challenger());
    t.observe_instance_count(airs.len());
    for (i, air) in airs.iter().enumerate() {
        let ext_db = p.degree_bits[i];
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
    let _ = t.sample_perm_challenges(&common.lookups, &p3_lookup::logup::LogUpGadget);
    let air_alpha =
        t.observe_perm_and_sample_alpha(p.commitments.permutation.as_ref(), &p.global_lookup_data);
    t.observe_quotient_commitment(&p.commitments.quotient_chunks);
    assert!(p.commitments.random.is_none());
    let zeta = t.sample_zeta();
    (t, air_alpha, zeta)
}

#[derive(Clone)]
struct MatMeta {
    round: usize,
    matrix: usize,
    instance: usize,
    table: String,
    kind: &'static str,
    chunk: Option<usize>,
    log_height: usize,
    width: usize,
}

/// Build `verify_batch`'s `coms_to_verify` from the (possibly mutated) proof. Pure — no verify.
#[allow(clippy::type_complexity)]
fn build_coms(
    scaffold: &Scaffold,
    proof: &BatchStarkProof<SC>,
    zeta: EF,
) -> (Vec<ComRound>, Vec<Vec<MatMeta>>, Vec<&'static str>) {
    let p = &proof.proof;
    let pcs = scaffold.config.pcs();
    let n = scaffold.airs.len();
    let names = &scaffold.names;
    let airs = &scaffold.airs;
    let common = &scaffold.common;
    let log_blowup = scaffold.log_blowup;

    let trace_domains: Vec<Domain> = p
        .degree_bits
        .iter()
        .map(|&db| <MyPcs as Pcs<EF, Challenger>>::natural_domain_for_degree(pcs, 1usize << db))
        .collect();
    let zeta_nexts: Vec<EF> = trace_domains
        .iter()
        .map(|d| d.next_point(zeta).expect("two-adic coset"))
        .collect();

    let mut coms: Vec<ComRound> = Vec::new();
    let mut metas: Vec<Vec<MatMeta>> = Vec::new();
    let mut round_kinds: Vec<&'static str> = Vec::new();

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

    // Round 0 — main.
    {
        let r = coms.len();
        let mut round = Vec::with_capacity(n);
        let mut meta = Vec::with_capacity(n);
        for i in 0..n {
            let ov = &p.opened_values.instances[i].base_opened_values;
            let reads_next =
                !<CircuitTableAir<SC, D> as BaseAir<F>>::main_next_row_columns(&airs[i]).is_empty();
            let mut points = vec![(zeta, ov.trace_local.clone())];
            if reads_next {
                if let Some(tn) = &ov.trace_next {
                    points.push((zeta_nexts[i], tn.clone()));
                }
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
    // Round 1 — quotient chunks.
    {
        let r = coms.len();
        let mut round = Vec::new();
        let mut meta = Vec::new();
        for i in 0..n {
            let ov = &p.opened_values.instances[i].base_opened_values;
            let n_chunks = ov.quotient_chunks.len();
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
    // Round 2 — preprocessed.
    if let Some(global) = &common.preprocessed {
        let r = coms.len();
        let mut round = Vec::new();
        let mut meta = Vec::new();
        for (matrix_index, &inst) in global.matrix_to_instance.iter().enumerate() {
            let ov = &p.opened_values.instances[inst].base_opened_values;
            let local = ov.preprocessed_local.as_ref().expect("preprocessed local");
            let m = global.instances[inst].as_ref().expect("preprocessed meta");
            let dom = <MyPcs as Pcs<EF, Challenger>>::natural_domain_for_degree(
                pcs,
                1usize << m.degree_bits,
            );
            let reads_next =
                !<CircuitTableAir<SC, D> as BaseAir<F>>::preprocessed_next_row_columns(&airs[inst])
                    .is_empty();
            let mut points = vec![(zeta, local.clone())];
            if reads_next {
                if let Some(pn) = &ov.preprocessed_next {
                    points.push((zeta_nexts[inst], pn.clone()));
                }
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
    // Round 3 — permutation.
    if let Some(perm_commit) = &p.commitments.permutation {
        let r = coms.len();
        let mut round = Vec::new();
        let mut meta = Vec::new();
        for i in 0..n {
            let inst = &p.opened_values.instances[i];
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

    (coms, metas, round_kinds)
}

// ===========================================================================
// THE ORACLE — dregg's deployed FRI/PCS verify, isolated from the AIR-constraint half.
// ===========================================================================
fn fri_pcs_verdict(scaffold: &Scaffold, proof: &BatchStarkProof<SC>) -> bool {
    let (transcript, _air_alpha, zeta) = replay_to_zeta(
        &scaffold.config,
        proof,
        &scaffold.airs,
        &scaffold.pvs,
        &scaffold.common,
        &scaffold.preprocessed_widths,
    );
    let (coms, _metas, _kinds) = build_coms(scaffold, proof, zeta);
    let pcs = scaffold.config.pcs();
    let mut ch = transcript.challenger.clone();
    <MyPcs as Pcs<EF, Challenger>>::verify(pcs, coms, &proof.proof.opening_proof, &mut ch).is_ok()
}

// ===========================================================================
// `open_input` — structural (no `verify_batch`); computes reduced openings regardless.
// ===========================================================================
#[allow(clippy::type_complexity)]
fn open_input_structural(
    log_blowup: usize,
    log_global_max_height: usize,
    index: usize,
    input_proof: &[BatchOpening<F, MyMmcs>],
    alpha: EF,
    coms: &[ComRound],
) -> (Vec<(usize, EF)>, Vec<usize>) {
    let mut reduced = BTreeMap::<usize, (EF, EF)>::new();
    let mut reduced_indices = Vec::with_capacity(coms.len());
    for (batch_opening, (_batch_commit, mats)) in input_proof.iter().zip(coms.iter()) {
        let batch_heights: Vec<usize> = mats
            .iter()
            .map(|(domain, _)| domain.size() << log_blowup)
            .collect();
        let reduced_index = batch_heights
            .iter()
            .max()
            .map(|&h| index >> (log_global_max_height - log2_strict(h)))
            .unwrap_or(0);
        reduced_indices.push(reduced_index);
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
                for (&p_at_x, &p_at_z) in mat_opening.iter().zip(ps_at_z.iter()) {
                    *ro += *alpha_pow * (p_at_z - EF::from(p_at_x)) * quotient;
                    *alpha_pow *= alpha;
                }
            }
        }
    }
    (
        reduced
            .into_iter()
            .rev()
            .map(|(lh, (_, ro))| (lh, ro))
            .collect(),
        reduced_indices,
    )
}

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

/// The structural decode of a (mutated) proof into the `dregg-root-fri-instance` JSON the twin
/// reads. Non-fatal: no Merkle `verify_batch`, no fold-landing assert, no PoW assert, no
/// distinctness assert — those are the very refusals a mutation is meant to trigger, and they
/// live on the twin/oracle side, not here.
fn emit_structural(
    scaffold: &Scaffold,
    proof: &BatchStarkProof<SC>,
    env: &WholeChainProofBytes,
) -> String {
    let (transcript, air_alpha, zeta) = replay_to_zeta(
        &scaffold.config,
        proof,
        &scaffold.airs,
        &scaffold.pvs,
        &scaffold.common,
        &scaffold.preprocessed_widths,
    );
    let (coms, metas, round_kinds) = build_coms(scaffold, proof, zeta);

    // challenger state at verify_fri's door: observe every claimed evaluation in round/matrix/point order.
    let mut ch = transcript.challenger.clone();
    for (_, round) in &coms {
        for (_, mat) in round {
            for (_, values) in mat {
                ch.observe_algebra_slice(values);
            }
        }
    }
    let fri_entry_state = ch.clone();

    let p = &proof.proof;
    let fri = &p.opening_proof;
    let layers = fri.commit_phase_commits.len();
    let log_blowup = scaffold.log_blowup;
    let log_final_poly_len = IR2_INNER_LOG_FINAL_POLY_LEN;
    let commit_pow_bits = IR2_INNER_COMMIT_POW_BITS;
    let query_pow_bits = IR2_INNER_QUERY_POW_BITS;
    let max_log_arity = INNER_FRI_MAX_LOG_ARITY;
    let num_queries = INNER_FRI_NUM_QUERIES;

    let log_arities: Vec<usize> = fri.query_proofs[0]
        .commit_phase_openings
        .iter()
        .map(|s| s.log_arity as usize)
        .collect();
    let log_global_max_height: usize =
        log_arities.iter().sum::<usize>() + log_blowup + log_final_poly_len;
    let log_final_height = log_blowup + log_final_poly_len;

    let perm = default_babybear_poseidon2_16();
    let val_mmcs = MyMmcs::new(MyHash::new(perm.clone()), MyCompress::new(perm), 0);
    let _challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
    let folding: TwoAdicFriFolding<Vec<BatchOpening<F, MyMmcs>>, <MyMmcs as Mmcs<F>>::Error> =
        TwoAdicFriFolding(core::marker::PhantomData);

    // FRI transcript replay (non-fatal PoW).
    let fri_alpha: EF = ch.sample_algebra_element();
    let mut betas: Vec<EF> = Vec::with_capacity(layers);
    for (comm, witness) in fri
        .commit_phase_commits
        .iter()
        .zip(fri.commit_pow_witnesses.iter())
    {
        ch.observe(comm.clone());
        let _ = ch.check_witness(commit_pow_bits, *witness);
        betas.push(ch.sample_algebra_element());
    }
    ch.observe_algebra_slice(&fri.final_poly);
    for &la in &log_arities {
        ch.observe(F::from_usize(la));
    }
    let _ = ch.check_witness(query_pow_bits, fri.query_pow_witness);

    // Per query — structural, no verify, no landing assert.
    let mut queries: Vec<QueryOut> = Vec::with_capacity(num_queries);
    for qp in fri.query_proofs.iter() {
        let index = ch.sample_bits(log_global_max_height);
        let (ro, reduced_indices) = open_input_structural(
            log_blowup,
            log_global_max_height,
            index,
            &qp.input_proof,
            fri_alpha,
            &coms,
        );
        let mut input_batches = Vec::with_capacity(coms.len());
        for (batch, _meta) in qp.input_proof.iter().zip(metas.iter()) {
            input_batches.push(InputBatchOut {
                reduced_index: 0, // filled below
                rows: batch.opened_values.clone(),
                path: batch.opening_proof.clone(),
            });
        }
        for (ib, ri) in input_batches.iter_mut().zip(reduced_indices.iter()) {
            ib.reduced_index = *ri;
        }

        let mut ro_iter = ro[1..].iter().peekable();
        let mut folded = ro[0].1;
        let mut domain_index = index;
        let mut log_current = log_global_max_height;
        let mut commit_phase = Vec::with_capacity(layers);
        let mut roll_ins: Vec<(usize, EF)> = Vec::new();
        let mut folded_after_round = Vec::with_capacity(layers);

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
            }
            commit_phase.push(CommitStepOut {
                log_arity,
                sibling: step.sibling_values[0],
                path: step.opening_proof.clone(),
            });
            folded_after_round.push(folded);
        }
        let _ = log_final_height;
        queries.push(QueryOut {
            index,
            input_batches,
            reduced_openings: ro,
            commit_phase,
            roll_ins,
            folded_after_round,
        });
    }

    emit(
        env,
        proof,
        &scaffold.names,
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
    )
}

#[allow(clippy::too_many_arguments)]
fn emit(
    env: &WholeChainProofBytes,
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
        json_str(&env.vk_fingerprint_hex),
        env.num_turns,
        env.version
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
        k.log_blowup, k.log_final_poly_len, k.commit_pow_bits, k.query_pow_bits, k.max_log_arity,
        k.num_queries, k.log_global_max_height, k.layers, fri.final_poly.len(),
    )
    .unwrap();
    write!(
        o,
        r#""challengerStateBeforeFriAlpha":{{"width":{WIDTH},"rate":{RATE},"sponge":{},"inputBuffer":{},"outputBuffer":{}}},"#,
        f_list(&fri_entry_state.sponge_state),
        f_list(&fri_entry_state.input_buffer),
        f_list(&fri_entry_state.output_buffer),
    )
    .unwrap();
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

    let mut rounds_json = Vec::with_capacity(coms.len());
    for (ri, ((commit, round), meta)) in coms.iter().zip(metas.iter()).enumerate() {
        let mats = arr(round.iter().zip(meta.iter()).map(|((_, points), m)| {
            format!(
                r#"{{"matrix":{},"instance":{},"table":{},"kindName":"{}","chunk":{},"logHeight":{},"width":{},"points":{}}}"#,
                m.matrix, m.instance, json_str(&m.table), m.kind,
                match m.chunk { Some(c) => c.to_string(), None => "null".to_string() },
                m.log_height, m.width, arr(points.iter().map(|(z, _)| ef_json(*z))),
            )
        }));
        rounds_json.push(format!(
            r#"{{"round":{ri},"kindName":"{}","commit":{},"matrices":{mats}}}"#,
            round_kinds[ri],
            cap_json(commit),
        ));
    }
    write!(o, r#""inputRounds":{},"#, arr(rounds_json)).unwrap();

    let mut opened = Vec::new();
    for ((_, round), meta) in coms.iter().zip(metas.iter()) {
        for ((_, points), m) in round.iter().zip(meta.iter()) {
            for (pi, (z, values)) in points.iter().enumerate() {
                opened.push(format!(
                    r#"{{"round":{},"matrix":{},"instance":{},"table":{},"kindName":"{}","chunk":{},"logHeight":{},"pointIndex":{pi},"point":{},"values":{}}}"#,
                    m.round, m.matrix, m.instance, json_str(&m.table), m.kind,
                    match m.chunk { Some(c) => c.to_string(), None => "null".to_string() },
                    m.log_height, ef_json(*z), ef_list(values),
                ));
            }
        }
    }
    write!(o, r#""openedEvals":{},"#, arr(opened)).unwrap();

    let qs = arr(queries.iter().map(|q| {
        let batches = arr(q.input_batches.iter().zip(metas.iter()).enumerate().map(|(ri, (b, meta))| {
            format!(
                r#"{{"round":{ri},"reducedIndex":{},"matrices":{},"rows":{},"path":{}}}"#,
                b.reduced_index,
                arr(meta.iter().map(|m| format!(r#"{{"logHeight":{},"width":{}}}"#, m.log_height, m.width))),
                arr(b.rows.iter().map(|r| f_list(r))),
                path_json(&b.path),
            )
        }));
        let ros = arr(q.reduced_openings.iter().map(|(lh, v)| format!(r#"{{"logHeight":{lh},"ro":{}}}"#, ef_json(*v))));
        let cp = arr(q.commit_phase.iter().map(|s| format!(r#"{{"logArity":{},"sibling":{},"path":{}}}"#, s.log_arity, ef_json(s.sibling), path_json(&s.path))));
        let rolls = arr(q.roll_ins.iter().map(|(r, v)| format!(r#"{{"afterRound":{r},"value":{}}}"#, ef_json(*v))));
        format!(
            r#"{{"index":{},"inputBatches":{batches},"reducedOpenings":{ros},"commitPhase":{cp},"rollIns":{rolls},"foldedAfterRound":{}}}"#,
            q.index, ef_list(&q.folded_after_round),
        )
    }));
    write!(o, r#""queries":{qs}"#).unwrap();
    o.push('}');
    o
}

// ===========================================================================
// The invariant scaffold, built once from the baseline.
// ===========================================================================
struct Scaffold {
    config: SC,
    airs: Vec<CircuitTableAir<SC, D>>,
    pvs: Vec<Vec<F>>,
    common: p3_batch_stark::CommonData<SC>,
    preprocessed_widths: Vec<usize>,
    names: Vec<String>,
    log_blowup: usize,
}

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

fn main() {
    let args: Vec<String> = env::args().collect();
    let seed: u64 = args
        .get(1)
        .map(|s| s.parse().expect("seed u64"))
        .unwrap_or(1);
    let ntrials: usize = args
        .get(2)
        .map(|s| s.parse().expect("ntrials"))
        .unwrap_or(2000);

    let fixture = repo_relative(FIXTURE);
    let bytes = std::fs::read(&fixture)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", fixture.display()));
    let env = WholeChainProofBytes::from_postcard(&bytes)
        .unwrap_or_else(|e| panic!("envelope does not decode: {e:?}"));
    let base: BatchStarkProof<SC> = postcard::from_bytes(&env.root_proof)
        .unwrap_or_else(|e| panic!("root BatchStarkProof does not decode: {e}"));
    base.validate()
        .unwrap_or_else(|e| panic!("root failed structural validation: {e:?}"));
    assert_eq!(
        base.proof.degree_bits.as_slice(),
        EXPECTED_DEGREE_BITS.as_slice()
    );

    let config = ir2_leaf_wrap_config();
    let (airs, pvs, names) =
        rebuild_airs(&config, &base).unwrap_or_else(|e| panic!("AIR reconstruction failed: {e}"));
    let mut prover = BatchStarkProver::new(config.clone());
    prover.register_poseidon2_table::<D>(Poseidon2Config::BABY_BEAR_D4_W16);
    prover.register_poseidon2_table::<D>(Poseidon2Config::BABY_BEAR_D4_W24);
    prover.register_recompose_table::<D>(false);
    prover.register_expose_claim_table::<D>();
    let common = prover
        .rebuild_verifiable_common::<D>(&base, base.w_binomial)
        .unwrap_or_else(|e| panic!("rebuild_verifiable_common failed: {e:?}"));
    let n = airs.len();
    let preprocessed_widths: Vec<usize> = (0..n)
        .map(|i| {
            common
                .preprocessed
                .as_ref()
                .and_then(|g| g.instances[i].as_ref().map(|m| m.width))
                .unwrap_or(0)
        })
        .collect();

    let scaffold = Scaffold {
        config,
        airs,
        pvs,
        common,
        preprocessed_widths,
        names,
        log_blowup: IR2_INNER_LOG_BLOWUP,
    };

    // baseline sanity: the deployed FRI verify MUST accept the committed proof.
    let base_verdict = fri_pcs_verdict(&scaffold, &base);
    eprintln!(
        "baseline FRI/PCS verdict: {} (must be ACCEPT)",
        if base_verdict { "ACCEPT" } else { "REJECT" }
    );
    assert!(
        base_verdict,
        "the deployed FRI verifier REJECTED the committed proof — oracle is broken"
    );

    let sanity = EXPECTED_LAYERS == base.proof.opening_proof.commit_phase_commits.len()
        && EXPECTED_LOG_GLOBAL_MAX_HEIGHT
            == base.proof.opening_proof.query_proofs[0]
                .commit_phase_openings
                .iter()
                .map(|s| s.log_arity as usize)
                .sum::<usize>()
                + scaffold.log_blowup
                + IR2_INNER_LOG_FINAL_POLY_LEN;
    assert!(sanity, "shape sanity failed");

    let sites = enumerate_sites(&base);
    let regions: Vec<&'static str> = sites.keys().copied().collect();
    let total_sites: usize = sites.values().map(|v| v.len()).sum();
    eprintln!(
        "enumerated {total_sites} single-felt sites across {} regions:",
        regions.len()
    );
    for (rg, v) in &sites {
        eprintln!("  {:<28} {} sites", rg, v.len());
    }

    let stdout = std::io::stdout();
    let mut out = BufWriter::new(stdout.lock());

    // Baseline line (trial -1): must decode byte-identical to .fullchain/real-root-fri.json (TS asserts).
    let base_json = emit_structural(&scaffold, &base, &env);
    writeln!(
        out,
        r#"{{"trial":-1,"region":"baseline","desc":"unmutated","oracle":"{}","fri":{}}}"#,
        if base_verdict { "ACCEPT" } else { "REJECT" },
        base_json
    )
    .unwrap();

    let mut rng = Rng(seed ^ 0xD1B5_4A32_D192_ED03);
    for t in 0..ntrials {
        // Stratify: pick a region uniformly, then a site within it uniformly. Even coverage
        // across regions regardless of their size, so a small region cannot go unsampled.
        let region = regions[rng.below(regions.len())];
        let region_sites = &sites[region];
        let site = region_sites[rng.below(region_sites.len())];
        let delta = rng.nonzero_delta();

        // BatchStarkProof is not Clone; re-decode a fresh baseline per trial (cheap, and
        // guarantees no mutation accumulates across trials).
        let mut mutated: BatchStarkProof<SC> =
            postcard::from_bytes(&env.root_proof).expect("re-decode baseline");
        let desc = apply_site(&mut mutated, &site, delta);
        let verdict = fri_pcs_verdict(&scaffold, &mutated);
        let json = emit_structural(&scaffold, &mutated, &env);
        writeln!(
            out,
            r#"{{"trial":{t},"region":{},"desc":{},"oracle":"{}","fri":{}}}"#,
            json_str(region),
            json_str(&desc),
            if verdict { "ACCEPT" } else { "REJECT" },
            json
        )
        .unwrap();
    }
    out.flush().unwrap();
    eprintln!("emitted {ntrials} mutation trials (seed {seed})");
}
