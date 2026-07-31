//! MINA/PASTA fixture export for a REAL native-Pasta shrink terminal — the
//! bridge between [`crate::apex_shrink`] (the Mina terminal shrink) and the o1js
//! Kimchi verifier `bridge/mina-zkapp/src/MinaShrinkVerify.ts`.
//!
//! It emits the **`RealRootFri` schema** (`bridge/mina-zkapp/src/RootFriWalk.ts`),
//! the SAME shape `circuit-prove/src/bin/root_fri_instance.rs` emits for the
//! whole-history root — so the o1js side consumes it with the EXISTING
//! `RootConsume.rootShapeOf` / `rootValues` + `DreggProofVerify` machinery,
//! setting `pastaSuite`. The only differences from the root emitter:
//!
//!   1. the input proof is the shrink terminal (`BatchStarkProof<DreggMinaConfig>`,
//!      5 instances, 4 PCS rounds), not the 7-instance root;
//!   2. the MMCS digests are single **native Pasta `Fp`** elements (emitted as
//!      canonical DECIMAL strings — `Field(BigInt(s))` on the o1js side), NOT
//!      re-hashed: the o1js verifier recomputes the exact commitment dregg
//!      emitted with `Poseidon.hash`, so `verifyInputBatches`'s
//!      `assertEq(recomputed, realCommit)` is a genuine binding, not the re-mint
//!      the `rehashRealRootFri` Pasta chain is (`RootConsume.ts:389-393`).
//!
//! ## Why the export is trustworthy (self-checks, run on every export)
//!
//! Identical to the gnark/root emitters': the recorded pre-FRI transcript is
//! validated by handing a `MultiField32Challenger` advanced through the RECORDED
//! events to the REAL `TwoAdicFriPcs::verify` (any divergence shifts every
//! beta/query index and fails FRI), and the FRI section is validated by
//! re-running the whole flow host-side with real p3 components — betas, PoW,
//! query indices, `ExtensionMmcs` commit-phase Merkle openings, `fold_row`, and
//! the `open_input` reduced-opening replica with its real `MinaValMmcs.verify_batch`
//! and final-poly check. What the fixture contains is exactly what passed this
//! run; a transcription error REJECTS here, it does not ship.

use std::collections::{BTreeMap, HashMap};

use p3_baby_bear::BabyBear;
use p3_challenger::{CanObserve, CanSampleBits, FieldChallenger, GrindingChallenger};
use p3_circuit_prover::{BatchStarkProof, NUM_PRIMITIVE_TABLES};
use p3_commit::{BatchOpening, BatchOpeningRef, Mmcs, Pcs, PolynomialSpace};
use p3_field::extension::BinomialExtensionField;
use p3_field::{
    BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField, PrimeField32, TwoAdicField,
};
use p3_fri::{FriFoldingStrategy, TwoAdicFriFolding};
use p3_lookup::logup::LogUpGadget;
use p3_lookup::{Kind, LookupProtocol};
use p3_matrix::Dimensions;
use p3_pasta::{MinaPoseidonPerm, PastaFp};
use p3_symmetric::{Hash, MerkleCap};
use p3_uni_stark::StarkGenericConfig;
use serde::Serialize;

use crate::apex_shrink::outer_shrink_prover;
use crate::apex_shrink_gnark_export::{APEX_VK_LANES, SETTLEMENT_CLAIM_LANES};
use crate::dregg_mina_config::{
    DreggMinaConfig, MINA_DIGEST_ELEMS, MINA_FRI_LOG_BLOWUP, MINA_FRI_NUM_QUERIES,
    MINA_FRI_QUERY_POW_BITS, MinaChallengeMmcs, MinaChallenger, MinaCompress, MinaHash,
    MinaValMmcs,
};

const D: usize = 4;
type EF = BinomialExtensionField<BabyBear, D>;
type MinaDigest = [PastaFp; MINA_DIGEST_ELEMS];
type MinaCap = MerkleCap<BabyBear, MinaDigest>;
type MinaPcsT = <DreggMinaConfig as StarkGenericConfig>::Pcs;
type MinaDomain = <MinaPcsT as Pcs<EF, MinaChallenger>>::Domain;
/// One PCS round: a commitment plus, per matrix, (instance, domain, [(point, values)]).
type ComRound = (MinaCap, Vec<(usize, MinaDomain, Vec<(EF, Vec<EF>)>)>);

// ============================================================================
// The emitted schema — `RealRootFri` (RootFriWalk.ts), camelCase.
// ============================================================================

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct Knobs {
    log_blowup: usize,
    log_final_poly_len: usize,
    commit_pow_bits: usize,
    query_pow_bits: usize,
    max_log_arity: usize,
    num_queries: usize,
    log_global_max_height: usize,
    extra_query_index_bits: usize,
    layers: usize,
    index_bits: usize,
    final_poly_len: usize,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct ChallengerState {
    width: usize,
    rate: usize,
    sponge: Vec<u32>,
    input_buffer: Vec<u32>,
    output_buffer: Vec<u32>,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct InputMatrixOut {
    matrix: usize,
    instance: usize,
    table: String,
    kind_name: String,
    chunk: Option<usize>,
    log_height: usize,
    width: usize,
    points: Vec<[u32; 4]>,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct InputRoundOut {
    round: usize,
    kind_name: String,
    commit: Vec<String>,
    matrices: Vec<InputMatrixOut>,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct OpenedEvalOut {
    round: usize,
    matrix: usize,
    instance: usize,
    table: String,
    kind_name: String,
    chunk: Option<usize>,
    log_height: usize,
    point_index: usize,
    point: [u32; 4],
    values: Vec<[u32; 4]>,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct BatchMatrixOut {
    log_height: usize,
    width: usize,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct InputBatchOut {
    matrices: Vec<BatchMatrixOut>,
    rows: Vec<Vec<u32>>,
    path: Vec<Vec<String>>,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct ReducedOpeningOut {
    log_height: usize,
    ro: [u32; 4],
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct CommitStepOut {
    sibling: [u32; 4],
    path: Vec<Vec<String>>,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct RollInOut {
    after_round: usize,
    value: [u32; 4],
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct QueryOut {
    index: usize,
    input_batches: Vec<InputBatchOut>,
    reduced_openings: Vec<ReducedOpeningOut>,
    commit_phase: Vec<CommitStepOut>,
    roll_ins: Vec<RollInOut>,
    folded_after_round: Vec<[u32; 4]>,
}

/// The full o1js fixture — `RealRootFri` plus the claim channel (`claimInstance`
/// / `claimLanes`, read by MinaShrinkVerify.ts via `as any`).
#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
pub struct MinaShrinkFixture {
    kind: String,
    vk_fingerprint: String,
    degree_bits: Vec<usize>,
    knobs: Knobs,
    challenger_state_before_fri_alpha: ChallengerState,
    zeta: [u32; 4],
    air_alpha: [u32; 4],
    fri_alpha: [u32; 4],
    betas: Vec<[u32; 4]>,
    commits: Vec<Vec<String>>,
    final_poly: Vec<[u32; 4]>,
    query_pow_witness: u32,
    input_rounds: Vec<InputRoundOut>,
    opened_evals: Vec<OpenedEvalOut>,
    queries: Vec<QueryOut>,
    /// Instance index of the shrink proof's own `expose_claim` table.
    claim_instance: usize,
    /// The 25 chain-claim lanes + 8 apex-VK-core lanes (canonical BabyBear u32).
    claim_lanes: Vec<u32>,
    /// A labeled copy of `claim_lanes[25..33]` — the apex's preprocessed commitment.
    apex_preprocessed_commit: Vec<u32>,
}

// ============================================================================
// Helpers
// ============================================================================

fn mina_domain(pcs: &MinaPcsT, degree: usize) -> MinaDomain {
    <MinaPcsT as Pcs<EF, MinaChallenger>>::natural_domain_for_degree(pcs, degree)
}

fn bb_u32(v: &BabyBear) -> u32 {
    v.as_canonical_u32()
}

/// A Pasta `Fp` digest element as a canonical DECIMAL string — dregg's real
/// emitted commitment, which the o1js verifier recomputes with `Poseidon.hash`.
fn pasta_dec(v: &PastaFp) -> String {
    v.as_canonical_biguint().to_string()
}

fn ef_coords(e: &EF) -> [u32; 4] {
    let s = e.as_basis_coefficients_slice();
    [bb_u32(&s[0]), bb_u32(&s[1]), bb_u32(&s[2]), bb_u32(&s[3])]
}

fn reverse_bits_len(x: usize, bits: usize) -> usize {
    let mut out = 0usize;
    for i in 0..bits {
        out |= ((x >> i) & 1) << (bits - 1 - i);
    }
    out
}

fn log2_strict(n: usize) -> usize {
    debug_assert!(n.is_power_of_two());
    n.trailing_zeros() as usize
}

/// The best-effort human table name for an instance (cosmetic; the load-bearing
/// key the o1js side reads is `instance`).
fn table_name(proof: &BatchStarkProof<DreggMinaConfig>, instance: usize) -> String {
    const PRIMITIVE: [&str; 3] = ["Const", "Public", "Alu"];
    if instance < NUM_PRIMITIVE_TABLES {
        PRIMITIVE
            .get(instance)
            .map(|s| s.to_string())
            .unwrap_or_else(|| format!("primitive_{instance}"))
    } else {
        proof
            .non_primitives
            .get(instance - NUM_PRIMITIVE_TABLES)
            .map(|e| e.op_type.as_str().to_string())
            .unwrap_or_else(|| format!("instance_{instance}"))
    }
}

/// Rebuild the exact Mina MMCSes (deterministic — `MinaPoseidonPerm` is a unit
/// struct), for host-side re-verification. Mirrors `create_mina_config_with_fri`
/// at `cap_height = 0`.
fn rebuild_mina_mmcs() -> Result<(MinaValMmcs, MinaChallengeMmcs), String> {
    let perm = MinaPoseidonPerm;
    let hash = MinaHash::new(perm).map_err(|e| format!("{e:?}"))?;
    let compress = MinaCompress::new(perm);
    let val_mmcs = MinaValMmcs::new(hash, compress, 0);
    let challenge_mmcs = MinaChallengeMmcs::new(val_mmcs.clone());
    Ok((val_mmcs, challenge_mmcs))
}

/// Drives a REAL `MinaChallenger` while recording every event.
struct Recorder {
    ch: MinaChallenger,
}

impl Recorder {
    fn new(ch: MinaChallenger) -> Self {
        Self { ch }
    }

    fn obs_bb(&mut self, v: BabyBear) {
        self.ch.observe(v);
    }

    fn obs_bb_slice(&mut self, vs: &[BabyBear]) {
        for v in vs {
            self.obs_bb(*v);
        }
    }

    fn obs_ext(&mut self, e: &EF) {
        self.obs_bb_slice(e.as_basis_coefficients_slice());
    }

    fn obs_usize(&mut self, v: usize) {
        self.obs_ext(&EF::from(BabyBear::from_usize(v)));
    }

    fn obs_cap(&mut self, cap: &MinaCap) {
        for root in cap.roots() {
            self.ch
                .observe(Hash::<BabyBear, PastaFp, MINA_DIGEST_ELEMS>::from(*root));
        }
    }

    fn sample_ext(&mut self) -> EF {
        self.ch.sample_algebra_element()
    }
}

/// The verifier-side `open_input` replica for the Mina MMCS — real input-MMCS
/// batch verification, so a mis-built round structure fails HERE.
#[allow(clippy::type_complexity)]
fn open_input_replica(
    log_blowup: usize,
    log_global_max_height: usize,
    index: usize,
    input_proof: &[BatchOpening<BabyBear, MinaValMmcs>],
    alpha: EF,
    val_mmcs: &MinaValMmcs,
    coms: &[ComRound],
) -> Result<Vec<(usize, EF)>, String> {
    if input_proof.len() != coms.len() {
        return Err(format!(
            "input proof has {} batches, expected {}",
            input_proof.len(),
            coms.len()
        ));
    }
    let mut reduced = BTreeMap::<usize, (EF, EF)>::new();

    for (batch_opening, (batch_commit, mats)) in input_proof.iter().zip(coms.iter()) {
        let batch_heights: Vec<usize> = mats
            .iter()
            .map(|(_, domain, _)| domain.size() << log_blowup)
            .collect();
        let batch_dims: Vec<Dimensions> = batch_heights
            .iter()
            .map(|&height| Dimensions { width: 0, height })
            .collect();
        let reduced_index = batch_heights
            .iter()
            .max()
            .map(|&h| index >> (log_global_max_height - log2_strict(h)))
            .unwrap_or(0);
        val_mmcs
            .verify_batch(
                batch_commit,
                &batch_dims,
                reduced_index,
                BatchOpeningRef::new(&batch_opening.opened_values, &batch_opening.opening_proof),
            )
            .map_err(|e| format!("input batch opening failed host-side verification: {e:?}"))?;

        for (mat_opening, (_, mat_domain, mat_points_and_values)) in
            batch_opening.opened_values.iter().zip(mats.iter())
        {
            let log_height = log2_strict(mat_domain.size()) + log_blowup;
            let bits_reduced = log_global_max_height - log_height;
            let rev_reduced_index = reverse_bits_len(index >> bits_reduced, log_height);
            let x = BabyBear::GENERATOR
                * BabyBear::two_adic_generator(log_height).exp_u64(rev_reduced_index as u64);

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

    Ok(reduced
        .into_iter()
        .rev()
        .map(|(lh, (_, ro))| (lh, ro))
        .collect())
}

/// Record one PCS round's matrices + opened evals into the emitted structures.
/// `entries`: per matrix, `(instance, chunk, domain, [(pointIndex, values)])`.
#[allow(clippy::too_many_arguments)]
fn push_round(
    proof: &BatchStarkProof<DreggMinaConfig>,
    zeta: EF,
    zeta_nexts: &[EF],
    coms: &mut Vec<ComRound>,
    input_rounds: &mut Vec<InputRoundOut>,
    opened_evals: &mut Vec<OpenedEvalOut>,
    round: usize,
    kind: &str,
    commit: &MinaCap,
    entries: Vec<(usize, Option<usize>, MinaDomain, Vec<(usize, Vec<EF>)>)>,
) {
    let point_of =
        |scale_idx: usize, i: usize| -> EF { if scale_idx == 0 { zeta } else { zeta_nexts[i] } };
    let mut com_mats: Vec<(usize, MinaDomain, Vec<(EF, Vec<EF>)>)> = Vec::new();
    let mut round_mats: Vec<InputMatrixOut> = Vec::new();
    for (matrix, (instance, chunk, domain, pts)) in entries.into_iter().enumerate() {
        let log_height = log2_strict(domain.size()) + MINA_FRI_LOG_BLOWUP;
        let width = pts.first().map(|(_, v)| v.len()).unwrap_or(0);
        let mut points_coords: Vec<[u32; 4]> = Vec::new();
        let mut com_points: Vec<(EF, Vec<EF>)> = Vec::new();
        for (pi, values) in &pts {
            let z = point_of(*pi, instance);
            points_coords.push(ef_coords(&z));
            com_points.push((z, values.clone()));
            opened_evals.push(OpenedEvalOut {
                round,
                matrix,
                instance,
                table: table_name(proof, instance),
                kind_name: kind.to_string(),
                chunk,
                log_height,
                point_index: *pi,
                point: ef_coords(&z),
                values: values.iter().map(ef_coords).collect(),
            });
        }
        com_mats.push((instance, domain, com_points));
        round_mats.push(InputMatrixOut {
            matrix,
            instance,
            table: table_name(proof, instance),
            kind_name: kind.to_string(),
            chunk,
            log_height,
            width,
            points: points_coords,
        });
    }
    coms.push((commit.clone(), com_mats));
    input_rounds.push(InputRoundOut {
        round,
        kind_name: kind.to_string(),
        commit: vec![pasta_dec(&commit.roots()[0][0])],
        matrices: round_mats,
    });
}

// ============================================================================
// The export
// ============================================================================

/// Export the Mina/Pasta `RealRootFri` fixture from a REAL native-Pasta shrink
/// proof, self-checking every section against the real p3 Mina components.
/// `proof` MUST carry an `expose_claim` table with the 25-lane chain claim +
/// 8-lane apex VK core (mint via
/// [`crate::apex_shrink_gnark_export::shrink_apex_to_outer_exposed`] at the Mina
/// config).
pub fn export_real_mina_shrink_fri_fixture(
    proof: &BatchStarkProof<DreggMinaConfig>,
    config: &DreggMinaConfig,
) -> Result<MinaShrinkFixture, String> {
    if config.is_zk() != 0 {
        return Err("exporter assumes a non-ZK Mina config".into());
    }
    if proof.ext_degree != D {
        return Err(format!("expected ext_degree {D}, got {}", proof.ext_degree));
    }
    let p = &proof.proof;
    let n = p.degree_bits.len();
    if p.commitments.random.is_some() {
        return Err("unexpected ZK randomization commitment".into());
    }
    if p.opened_values.instances.len() != n {
        return Err("instance count mismatch between opened values and degree_bits".into());
    }
    if NUM_PRIMITIVE_TABLES + proof.non_primitives.len() != n {
        return Err(format!(
            "instance count {} != {} primitive + {} non-primitive tables",
            n,
            NUM_PRIMITIVE_TABLES,
            proof.non_primitives.len()
        ));
    }

    let mut publics: Vec<Vec<BabyBear>> = vec![Vec::new(); NUM_PRIMITIVE_TABLES];
    publics.extend(proof.non_primitives.iter().map(|e| e.public_values.clone()));

    let claim_instance = NUM_PRIMITIVE_TABLES
        + proof
            .non_primitives
            .iter()
            .position(|e| e.op_type.as_str() == "expose_claim")
            .ok_or(
                "shrink proof carries no expose_claim table — the settlement claim is unbound \
                 (mint with shrink_apex_to_outer_exposed, not the plain shrink)",
            )?;
    // The exposed shrink re-exposes the apex's FULL expose_claim vector (25 chain
    // claim lanes ++ whatever the apex itself exposes beyond them, e.g. the
    // landed VK-spine) followed by the 8 apex-VK-core lanes appended by the
    // exposure hook. The chain claim the o1js verifier reads is lanes [0..25];
    // the tail carries the spine + apex-VK pin (used by the gnark settlement
    // path, not by this verifier).
    if publics[claim_instance].len() < SETTLEMENT_CLAIM_LANES {
        return Err(format!(
            "shrink expose_claim table carries {} lanes, need at least the {} chain-claim lanes \
             (mint with shrink_apex_to_outer_exposed)",
            publics[claim_instance].len(),
            SETTLEMENT_CLAIM_LANES,
        ));
    }
    let claim_lanes: Vec<u32> = publics[claim_instance].iter().map(bb_u32).collect();
    let apex_preprocessed_commit: Vec<u32> = if claim_lanes.len() >= APEX_VK_LANES {
        claim_lanes[claim_lanes.len() - APEX_VK_LANES..].to_vec()
    } else {
        Vec::new()
    };

    let common = outer_shrink_prover(config)
        .rebuild_verifiable_common::<D>(proof, proof.w_binomial)
        .map_err(|e| format!("rebuild_verifiable_common failed: {e:?}"))?;

    // ---- Phase A: the pre-FRI transcript, mirrored --------------------------
    let mut rec = Recorder::new(config.initialise_challenger());

    rec.obs_usize(n);
    for i in 0..n {
        let inst = &p.opened_values.instances[i].base_opened_values;
        let ext_db = p.degree_bits[i];
        rec.obs_usize(ext_db);
        rec.obs_usize(ext_db);
        rec.obs_usize(inst.trace_local.len());
        rec.obs_usize(inst.quotient_chunks.len());
    }
    rec.obs_cap(&p.commitments.main);
    for pv in &publics {
        rec.obs_bb_slice(pv);
    }
    let preprocessed_widths: Vec<usize> = (0..n)
        .map(|i| {
            common
                .preprocessed
                .as_ref()
                .and_then(|g| g.instances[i].as_ref().map(|m| m.width))
                .unwrap_or(0)
        })
        .collect();
    for &w in &preprocessed_widths {
        rec.obs_usize(w);
    }
    if let Some(global) = &common.preprocessed {
        rec.obs_cap(&global.commitment);
    }
    let lookup_gadget = LogUpGadget::new();
    let n_ch = lookup_gadget.num_challenges();
    let mut seen_buses: HashMap<String, ()> = HashMap::new();
    for lookups in &common.lookups {
        for ctx in lookups.as_ref() {
            match &ctx.kind {
                Kind::Global(name) => {
                    if seen_buses.insert(name.clone(), ()).is_none() {
                        for _ in 0..n_ch {
                            let _ = rec.sample_ext();
                        }
                    }
                }
                Kind::Local => {
                    for _ in 0..n_ch {
                        let _ = rec.sample_ext();
                    }
                }
            }
        }
    }
    if let Some(perm_commit) = &p.commitments.permutation {
        rec.obs_cap(perm_commit);
        for data in p.global_lookup_data.iter().flatten() {
            rec.obs_ext(&data.cumulative_sum);
        }
    }
    let air_alpha = rec.sample_ext();
    rec.obs_cap(&p.commitments.quotient_chunks);
    let zeta = rec.sample_ext();

    // ---- The PCS round structure (verify_batch's coms_to_verify) ----------
    let pcs = config.pcs();
    let ext_doms: Vec<MinaDomain> = p
        .degree_bits
        .iter()
        .map(|&db| mina_domain(pcs, 1usize << db))
        .collect();
    let zeta_nexts: Vec<EF> = ext_doms
        .iter()
        .map(|dom| {
            dom.next_point(zeta)
                .ok_or("next_point unavailable".to_string())
        })
        .collect::<Result<_, _>>()?;

    // Round metadata carried alongside `coms` so the emitted RealRootFri
    // `inputRounds`/`openedEvals` carry the load-bearing `instance` per matrix.
    let mut coms: Vec<ComRound> = Vec::new();
    let mut input_rounds: Vec<InputRoundOut> = Vec::new();
    let mut opened_evals: Vec<OpenedEvalOut> = Vec::new();

    // Trace round.
    {
        let mut entries = Vec::with_capacity(n);
        for i in 0..n {
            let inst = &p.opened_values.instances[i].base_opened_values;
            let mut pts = vec![(0usize, inst.trace_local.clone())];
            if let Some(next) = &inst.trace_next {
                pts.push((1usize, next.clone()));
            }
            entries.push((i, None, ext_doms[i], pts));
        }
        push_round(
            proof,
            zeta,
            &zeta_nexts,
            &mut coms,
            &mut input_rounds,
            &mut opened_evals,
            0,
            "main",
            &p.commitments.main,
            entries,
        );
    }
    // Quotient chunks round.
    {
        let mut entries = Vec::new();
        for i in 0..n {
            let inst = &p.opened_values.instances[i].base_opened_values;
            for (ci, chunk) in inst.quotient_chunks.iter().enumerate() {
                entries.push((i, Some(ci), ext_doms[i], vec![(0usize, chunk.clone())]));
            }
        }
        push_round(
            proof,
            zeta,
            &zeta_nexts,
            &mut coms,
            &mut input_rounds,
            &mut opened_evals,
            1,
            "quotient_chunk",
            &p.commitments.quotient_chunks,
            entries,
        );
    }
    // Preprocessed round.
    if let Some(global) = &common.preprocessed {
        let mut entries = Vec::new();
        for &inst_idx in &global.matrix_to_instance {
            let inst = &p.opened_values.instances[inst_idx].base_opened_values;
            let local = inst
                .preprocessed_local
                .as_ref()
                .ok_or("missing preprocessed_local for a preprocessed instance")?;
            let meta = global.instances[inst_idx]
                .as_ref()
                .ok_or("missing preprocessed metadata")?;
            let pre_domain = mina_domain(pcs, 1usize << meta.degree_bits);
            let mut pts = vec![(0usize, local.clone())];
            if let Some(next) = &inst.preprocessed_next {
                pts.push((1usize, next.clone()));
            }
            entries.push((inst_idx, None, pre_domain, pts));
        }
        let round = input_rounds.len();
        push_round(
            proof,
            zeta,
            &zeta_nexts,
            &mut coms,
            &mut input_rounds,
            &mut opened_evals,
            round,
            "preprocessed",
            &global.commitment,
            entries,
        );
    }
    // Permutation round.
    if let Some(perm_commit) = &p.commitments.permutation {
        let mut entries = Vec::new();
        for i in 0..n {
            let inst = &p.opened_values.instances[i];
            if !inst.permutation_local.is_empty() {
                entries.push((
                    i,
                    None,
                    ext_doms[i],
                    vec![
                        (0usize, inst.permutation_local.clone()),
                        (1usize, inst.permutation_next.clone()),
                    ],
                ));
            }
        }
        if !entries.is_empty() {
            let round = input_rounds.len();
            push_round(
                proof,
                zeta,
                &zeta_nexts,
                &mut coms,
                &mut input_rounds,
                &mut opened_evals,
                round,
                "permutation",
                perm_commit,
                entries,
            );
        }
    }

    // ---- SELF-CHECK 1: the REAL pcs.verify accepts from the recorded state.
    // Rebuild the plain `coms_to_verify` shape (drop the instance tag).
    let coms_plain: Vec<(MinaCap, Vec<(MinaDomain, Vec<(EF, Vec<EF>)>)>)> = coms
        .iter()
        .map(|(c, mats)| {
            (
                c.clone(),
                mats.iter()
                    .map(|(_, dom, pts)| (*dom, pts.clone()))
                    .collect(),
            )
        })
        .collect();
    {
        let mut ch = rec.ch.clone();
        <MinaPcsT as Pcs<EF, MinaChallenger>>::verify(
            pcs,
            coms_plain.clone(),
            &p.opening_proof,
            &mut ch,
        )
        .map_err(|e| {
            format!(
                "REAL Mina pcs.verify rejected from the mirrored transcript state \
                 (the prefix mirror or round structure diverges from verify_batch): {e:?}"
            )
        })?;
    }

    // pcs.verify's own opened-value observes, then the FRI batch-combination alpha.
    for (_, round) in &coms {
        for (_, _, mat) in round {
            for (_, values) in mat {
                for v in values {
                    rec.obs_ext(v);
                }
            }
        }
    }
    let fri_alpha = rec.sample_ext();

    let ch0 = rec.ch;

    // ---- Phase B: the FRI core ---------------------------------------------
    let fri = &p.opening_proof;
    let rounds = fri.commit_phase_commits.len();
    if fri.commit_pow_witnesses.len() != rounds {
        return Err("commit PoW witness count mismatch".into());
    }
    if fri.query_proofs.len() != MINA_FRI_NUM_QUERIES {
        return Err(format!(
            "expected {MINA_FRI_NUM_QUERIES} query proofs, got {}",
            fri.query_proofs.len()
        ));
    }
    for qp in &fri.query_proofs {
        if qp.commit_phase_openings.len() != rounds {
            return Err("query has wrong number of commit-phase openings".into());
        }
        for step in &qp.commit_phase_openings {
            if step.log_arity != 1 || step.sibling_values.len() != 1 {
                return Err("non-arity-2 commit round (fixture scope is arity 2)".into());
            }
        }
    }
    let log_global_max_height = rounds + MINA_FRI_LOG_BLOWUP;
    let max_db = *p.degree_bits.iter().max().ok_or("no instances")?;
    if max_db + MINA_FRI_LOG_BLOWUP != log_global_max_height {
        return Err(format!(
            "round count {rounds} inconsistent with max degree bits {max_db} + blowup {MINA_FRI_LOG_BLOWUP}"
        ));
    }
    if fri.final_poly.len() != 1 {
        return Err("expected a constant final polynomial (log_final_poly_len = 0)".into());
    }

    let (val_mmcs, challenge_mmcs) = rebuild_mina_mmcs()?;
    let folding: TwoAdicFriFolding<
        Vec<BatchOpening<BabyBear, MinaValMmcs>>,
        <MinaValMmcs as Mmcs<BabyBear>>::Error,
    > = TwoAdicFriFolding(core::marker::PhantomData);

    let mut ch = ch0;
    let mut betas: Vec<EF> = Vec::with_capacity(rounds);
    for comm in &fri.commit_phase_commits {
        ch.observe(comm.clone());
        betas.push(ch.sample_algebra_element());
    }
    ch.observe_algebra_slice(&fri.final_poly);
    for _ in 0..rounds {
        ch.observe(BabyBear::ONE);
    }
    if !ch.check_witness(MINA_FRI_QUERY_POW_BITS, fri.query_pow_witness) {
        return Err("query PoW witness failed host-side check".into());
    }

    let mut queries_out: Vec<QueryOut> = Vec::with_capacity(fri.query_proofs.len());

    for (qi, qp) in fri.query_proofs.iter().enumerate() {
        let index = ch.sample_bits(log_global_max_height);
        let ro = open_input_replica(
            MINA_FRI_LOG_BLOWUP,
            log_global_max_height,
            index,
            &qp.input_proof,
            fri_alpha,
            &val_mmcs,
            &coms,
        )?;
        if ro.first().map(|(lh, _)| *lh) != Some(log_global_max_height) {
            return Err(format!(
                "query {qi}: initial reduced opening not at max height"
            ));
        }
        let initial_eval = ro[0].1;

        if qp.input_proof.len() != input_rounds.len() {
            return Err(format!(
                "query {qi}: {} input batches for {} structural rounds",
                qp.input_proof.len(),
                input_rounds.len()
            ));
        }
        let mut input_batches: Vec<InputBatchOut> = Vec::with_capacity(qp.input_proof.len());
        for (ri, (batch, round_shape)) in qp.input_proof.iter().zip(input_rounds.iter()).enumerate()
        {
            if batch.opened_values.len() != round_shape.matrices.len() {
                return Err(format!(
                    "query {qi} input round {ri}: {} opened rows for {} matrices",
                    batch.opened_values.len(),
                    round_shape.matrices.len()
                ));
            }
            for (row, m) in batch.opened_values.iter().zip(&round_shape.matrices) {
                if row.len() != m.width {
                    return Err(format!(
                        "query {qi} input round {ri}: row width {} != matrix width {}",
                        row.len(),
                        m.width
                    ));
                }
            }
            let max_lh = round_shape
                .matrices
                .iter()
                .map(|m| m.log_height)
                .max()
                .ok_or("empty input round")?;
            if batch.opening_proof.len() != max_lh {
                return Err(format!(
                    "query {qi} input round {ri}: path has {} levels, tree height is {max_lh}",
                    batch.opening_proof.len()
                ));
            }
            input_batches.push(InputBatchOut {
                matrices: round_shape
                    .matrices
                    .iter()
                    .map(|m| BatchMatrixOut {
                        log_height: m.log_height,
                        width: m.width,
                    })
                    .collect(),
                rows: batch
                    .opened_values
                    .iter()
                    .map(|row| row.iter().map(bb_u32).collect())
                    .collect(),
                path: batch
                    .opening_proof
                    .iter()
                    .map(|d| vec![pasta_dec(&d[0])])
                    .collect(),
            });
        }

        let reduced_openings: Vec<ReducedOpeningOut> = ro
            .iter()
            .map(|(lh, v)| ReducedOpeningOut {
                log_height: *lh,
                ro: ef_coords(v),
            })
            .collect();

        let mut ro_iter = ro[1..].iter().peekable();
        let mut folded = initial_eval;
        let mut domain_index = index;
        let mut log_current = log_global_max_height;
        let mut roll_ins: Vec<RollInOut> = Vec::new();
        let mut folded_after_round: Vec<[u32; 4]> = Vec::with_capacity(rounds);
        let mut commit_phase: Vec<CommitStepOut> = Vec::with_capacity(rounds);

        for (r, step) in qp.commit_phase_openings.iter().enumerate() {
            let sib = step.sibling_values[0];
            let bit = domain_index & 1;
            let evals: Vec<EF> = if bit == 0 {
                vec![folded, sib]
            } else {
                vec![sib, folded]
            };
            domain_index >>= 1;
            let log_folded = log_current - 1;

            challenge_mmcs
                .verify_batch(
                    &fri.commit_phase_commits[r],
                    &[Dimensions {
                        width: 2,
                        height: 1 << log_folded,
                    }],
                    domain_index,
                    BatchOpeningRef::new(core::slice::from_ref(&evals), &step.opening_proof),
                )
                .map_err(|e| {
                    format!("query {qi} round {r}: commit-phase Merkle opening failed: {e:?}")
                })?;

            folded = <TwoAdicFriFolding<_, _> as FriFoldingStrategy<BabyBear, EF>>::fold_row(
                &folding,
                domain_index,
                log_folded,
                1,
                betas[r],
                evals.into_iter(),
            );
            log_current = log_folded;

            if let Some((_, v)) = ro_iter.next_if(|(lh, _)| *lh == log_current) {
                folded += betas[r] * betas[r] * *v;
                roll_ins.push(RollInOut {
                    after_round: r,
                    value: ef_coords(v),
                });
            }

            folded_after_round.push(ef_coords(&folded));
            commit_phase.push(CommitStepOut {
                sibling: ef_coords(&sib),
                path: step
                    .opening_proof
                    .iter()
                    .map(|d| vec![pasta_dec(&d[0])])
                    .collect(),
            });
        }
        if log_current != MINA_FRI_LOG_BLOWUP {
            return Err(format!("query {qi}: fold ended at height {log_current}"));
        }
        if ro_iter.next().is_some() {
            return Err(format!("query {qi}: unconsumed reduced openings"));
        }
        if folded != fri.final_poly[0] {
            return Err(format!(
                "query {qi}: fold chain does not reach the final polynomial \
                 (transcript or reduced-opening replica diverges)"
            ));
        }

        queries_out.push(QueryOut {
            index,
            input_batches,
            reduced_openings,
            commit_phase,
            roll_ins,
            folded_after_round,
        });
    }

    Ok(MinaShrinkFixture {
        kind: "mina-shrink-terminal-fri".into(),
        vk_fingerprint: "dregg-mina-shrink".into(),
        degree_bits: p.degree_bits.clone(),
        knobs: Knobs {
            log_blowup: MINA_FRI_LOG_BLOWUP,
            log_final_poly_len: 0,
            commit_pow_bits: 0,
            query_pow_bits: MINA_FRI_QUERY_POW_BITS,
            max_log_arity: 1,
            num_queries: MINA_FRI_NUM_QUERIES,
            log_global_max_height,
            extra_query_index_bits: 0,
            layers: rounds,
            index_bits: log_global_max_height,
            final_poly_len: 1,
        },
        challenger_state_before_fri_alpha: ChallengerState {
            width: 3,
            rate: 2,
            sponge: Vec::new(),
            input_buffer: Vec::new(),
            output_buffer: Vec::new(),
        },
        zeta: ef_coords(&zeta),
        air_alpha: ef_coords(&air_alpha),
        fri_alpha: ef_coords(&fri_alpha),
        betas: betas.iter().map(ef_coords).collect(),
        commits: fri
            .commit_phase_commits
            .iter()
            .map(|cap| {
                let roots = cap.roots();
                assert_eq!(roots.len(), 1, "cap_height 0 ⇒ single root");
                vec![pasta_dec(&roots[0][0])]
            })
            .collect(),
        final_poly: fri.final_poly.iter().map(ef_coords).collect(),
        query_pow_witness: bb_u32(&fri.query_pow_witness),
        input_rounds,
        opened_evals,
        queries: queries_out,
        claim_instance,
        claim_lanes,
        apex_preprocessed_commit,
    })
}
