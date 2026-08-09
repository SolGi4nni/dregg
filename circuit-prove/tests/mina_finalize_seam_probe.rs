//! ⚑⚑ **THE CARRIED-LANE PROBE — the measurement the finalize-scalars decider did not run.**
//!
//! The `dregg-mina-finalize-scalars::v1` brief threads the 86-evaluation tape seam through the
//! phase-2 chain **elementwise**: every fold claim in that design carries ~89 extra 32-limb blocks
//! (~2,848 lanes) so that a finalize-side leaf's evaluation inputs can be `cb.connect`ed to the
//! chain links' absorbed pairs — no digest, no birthday bound. The alternative is the ACC fallback:
//! carry an 8-lane Poseidon digest instead, which inserts a ~2^124 collision surface INSIDE the
//! forcing path, at this repo's own stated bar.
//!
//! Everything upstream of that choice is unchanged either way, so the choice is decided by ONE
//! number: what does a chain fold site cost when the carried claim is ~3,000 lanes instead of 200?
//! This file measures exactly that, same binary, same process, sequentially:
//!
//!   * BASELINE — two real chain-link leaves + one real `fold_chain_links` (200-lane claim).
//!   * PADDED   — the same two links proved through a leaf whose claim is padded to
//!     `200 + 2,848 = 3,048` lanes (the extra lanes are REAL constrained targets — re-exposures of
//!     the child's own descriptor-PI lanes, not free felts), folded by a fold that performs the
//!     baseline's 96 state connects PLUS 2,848 elementwise connects across the padding, and
//!     re-exposes a 3,048-lane parent.
//!
//! The padding lanes are re-exposures of `main[k % CHAIN_PI_COUNT]`, so none of them is an
//! unconstrained pin (`dropUnforcedPins` cannot eat them) and the wrap circuit really carries
//! 3,048 bound public outputs — the same load the eval seam would put on it.
//!
//! ⚠ Run ALONE (never two proving jobs concurrently), release, one test at a time:
//!
//! ```text
//! cargo test -p dregg-circuit-prove --release --test mina_finalize_seam_probe -- \
//!     --ignored --nocapture the_padded_carried_claim_probe
//! ```
//!
//! Needs links 0..2 of the chain witnesses (`mina_chain_emit … 2`), same as
//! `mina_phase2_chain_fold.rs` §1.

use std::path::PathBuf;
use std::time::Instant;

use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, UMemBoundaryWitness, ir2_airs_and_common_for_config,
    prove_vm_descriptor2_for_config,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit_prove::fold_vk_pin::FoldVkPins;
use dregg_circuit_prove::gpu_backend::{
    prove_recursion_aggregation_auto_with_expose, prove_recursion_layer_auto_with_expose,
};
use dregg_circuit_prove::ivc_turn_chain::seg_poseidon_commit;
use dregg_circuit_prove::mina_phase2_chain_leaf::{
    ABSORBED_PI_LO, ABSORBED_WIDTH, CHAIN_CLAIM_LEN, CHAIN_PI_COUNT, STATE_WIDTH,
    chain_inner_config, chain_link_descriptor, chain_root_config, fold_chain_links,
    prove_chain_link_leaf,
};
use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, recursion_layer_over, verify_recursive_batch_proof_with_config,
};
use p3_recursion::{BatchOnly, RecursionInput, RecursionOutput, Target};

type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

/// The eval seam's extra freight: ~89 blocks × 32 limbs. 2,848 lanes on top of the chain's 200.
const SEAM_PAD_LANES: usize = 2848;
/// The padded claim: the chain's own 200 lanes followed by the seam padding.
const PADDED_CLAIM_LEN: usize = CHAIN_CLAIM_LEN + SEAM_PAD_LANES;

const CHAIN_PIS_ALL: &str = include_str!("../../circuit/tests/fixtures/pasta-fq-chainlink-pis.txt");

fn witness_dir() -> PathBuf {
    std::env::var("DREGG_CHAINLINK_WITNESS_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| {
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("../circuit/tests/fixtures/pasta-fq-chainlink")
        })
}

fn all_link_pis() -> Vec<Vec<BabyBear>> {
    CHAIN_PIS_ALL
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|c| BabyBear::new(c.parse::<u32>().expect("PI is a u32 decimal")))
                .collect()
        })
        .collect()
}

fn link_trace(j: usize) -> Vec<Vec<BabyBear>> {
    let path = witness_dir().join(format!("link-{j}-trace.txt"));
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "chain-link witness {} missing ({e}). Emit links 0..2 first:\n  \
             cd metatheory && lake build mina_chain_emit \\\n    \
             && ./.lake/build/bin/mina_chain_emit ../circuit/tests/fixtures/pasta-fq-chainlink 2",
            path.display()
        )
    });
    text.lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            l.split_whitespace()
                .map(|c| BabyBear::new(c.parse::<u32>().expect("cell is a u32 decimal")))
                .collect()
        })
        .collect()
}

/// ⚑ **THE PADDED LEAF.** `prove_chain_link_leaf`'s body with ONE change: after the 200 real claim
/// lanes, `SEAM_PAD_LANES` re-exposures of the child's own descriptor-PI lanes are appended. Every
/// padded lane is a bound target of the verified inner batch — the honest stand-in for the eval
/// blocks the finalize seam would carry.
fn prove_padded_chain_leaf(
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
    inner_config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let desc = chain_link_descriptor()?;
    let wrap_config = recursion_layer_over(inner_config);

    let inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        &desc,
        trace,
        public_inputs,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        inner_config,
    )
    .map_err(|e| format!("padded chain-link inner IR-v2 prove failed: {e}"))?;

    let (airs, table_public_inputs, common) =
        ir2_airs_and_common_for_config(&desc, &inner, public_inputs, inner_config)
            .map_err(|e| format!("padded chain-link verify-triple build failed: {e}"))?;

    let input: RecursionInput<'_, DreggRecursionConfig, _> = RecursionInput::NativeBatchStark {
        airs: &airs,
        proof: &inner,
        common_data: &common,
        table_public_inputs,
    };

    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       apt: &[Vec<Target>],
                       _vk_cap: &[Target]| {
        let main = apt
            .first()
            .expect("chain link has a main instance carrying the descriptor PIs");
        debug_assert!(main.len() >= CHAIN_PI_COUNT);
        // The chain's own 200-lane claim, exactly as the production leaf builds it.
        let mut claim: Vec<Target> = (0..2 * STATE_WIDTH).map(|k| main[k]).collect();
        let absorbed: Vec<Target> = (0..ABSORBED_WIDTH)
            .map(|k| main[ABSORBED_PI_LO + k])
            .collect();
        claim.extend_from_slice(&seg_poseidon_commit(cb, &absorbed));
        debug_assert_eq!(claim.len(), CHAIN_CLAIM_LEN);
        // ⚑ THE PADDING: bound re-exposures, not free felts.
        for k in 0..SEAM_PAD_LANES {
            claim.push(main[k % CHAIN_PI_COUNT]);
        }
        debug_assert_eq!(claim.len(), PADDED_CLAIM_LEN);
        cb.expose_as_public_output(&claim);
    };

    prove_recursion_layer_auto_with_expose(&input, &wrap_config, Some(&expose))
        .map_err(|e| format!("padded chain-link leaf wrap failed: {e}"))
}

/// Locate a child's claim instance by its (unique) lane count.
fn claim_index(apt: &[Vec<Target>], want: usize) -> usize {
    apt.iter()
        .position(|v| v.len() == want)
        .unwrap_or_else(|| panic!("no exposed claim instance with {want} lanes"))
}

/// ⚑ **THE PADDED FOLD.** `fold_chain_links`' 96 state connects, PLUS `SEAM_PAD_LANES` elementwise
/// connects across the two children's padding, re-exposing a padded parent. The extra connects are
/// exactly the shape one eval-seam fold site would add.
fn fold_padded_chain_links(
    left: &RecursionOutput<DreggRecursionConfig>,
    right: &RecursionOutput<DreggRecursionConfig>,
    pins: &FoldVkPins,
    config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    let left_input = left.into_recursion_input_pinned::<BatchOnly>(pins.left.clone());
    let right_input = right.into_recursion_input_pinned::<BatchOnly>(pins.right.clone());

    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>],
                       _left_vk_cap: &[Target],
                       _right_vk_cap: &[Target]| {
        let l = &left_apt[claim_index(left_apt, PADDED_CLAIM_LEN)];
        let r = &right_apt[claim_index(right_apt, PADDED_CLAIM_LEN)];

        // The chain carry, exactly as `fold_chain_links` performs it.
        for k in 0..STATE_WIDTH {
            cb.connect(l[STATE_WIDTH + k], r[k]);
        }
        // ⚑ THE SEAM FREIGHT: elementwise connects across the padding.
        for k in 0..SEAM_PAD_LANES {
            cb.connect(l[CHAIN_CLAIM_LEN + k], r[CHAIN_CLAIM_LEN + k]);
        }

        // The ordered transcript commitment over the two 8-lane accs, as the real fold does.
        let mut acc_inputs: Vec<Target> =
            Vec::with_capacity(2 * (CHAIN_CLAIM_LEN - 2 * STATE_WIDTH));
        acc_inputs.extend_from_slice(&l[2 * STATE_WIDTH..CHAIN_CLAIM_LEN]);
        acc_inputs.extend_from_slice(&r[2 * STATE_WIDTH..CHAIN_CLAIM_LEN]);
        let acc = seg_poseidon_commit(cb, &acc_inputs);

        let mut parent: Vec<Target> = Vec::with_capacity(PADDED_CLAIM_LEN);
        parent.extend_from_slice(&l[..STATE_WIDTH]);
        parent.extend_from_slice(&r[STATE_WIDTH..2 * STATE_WIDTH]);
        parent.extend_from_slice(&acc);
        parent.extend_from_slice(&l[CHAIN_CLAIM_LEN..PADDED_CLAIM_LEN]);
        debug_assert_eq!(parent.len(), PADDED_CLAIM_LEN);
        cb.expose_as_public_output(&parent);
    };

    prove_recursion_aggregation_auto_with_expose(&left_input, &right_input, config, Some(&expose))
        .map_err(|e| format!("padded chain fold failed: {e}"))
}

struct EmittedFri {
    num_queries: usize,
    log_lde_domain: usize,
    max_degree_bits: usize,
}

fn emitted_fri(out: &RecursionOutput<DreggRecursionConfig>) -> EmittedFri {
    let fri = &out.0.proof.opening_proof;
    EmittedFri {
        num_queries: fri.query_proofs.len(),
        log_lde_domain: fri
            .query_proofs
            .iter()
            .flat_map(|q| q.input_proof.iter())
            .map(|b| b.opening_proof.len())
            .max()
            .unwrap_or(0),
        max_degree_bits: out.0.proof.degree_bits.iter().copied().max().unwrap_or(0),
    }
}

fn report(label: &str, out: &RecursionOutput<DreggRecursionConfig>) {
    let e = emitted_fri(out);
    println!(
        "  {label:<28} EMITTED {} query proofs, committed LDE 2^{} (trace 2^{})",
        e.num_queries, e.log_lde_domain, e.max_degree_bits
    );
}

/// ⚑⚑ **THE PROBE.** One number pair decides elementwise-vs-acc for the tape weld.
#[test]
#[ignore = "MEASUREMENT. Run ALONE, release, --nocapture; needs links 0..2 emitted."]
fn the_padded_carried_claim_probe() {
    let pis = all_link_pis();
    let inner = chain_inner_config();
    let fold_cfg = chain_root_config();
    let t0_trace = link_trace(0);
    let t1_trace = link_trace(1);

    // ── BASELINE: the production 200-lane shape. ────────────────────────────
    let t = Instant::now();
    let b0 = prove_chain_link_leaf(&t0_trace, &pis[0], &inner).expect("baseline leaf 0");
    let b1 = prove_chain_link_leaf(&t1_trace, &pis[1], &inner).expect("baseline leaf 1");
    let base_leaves_ms = t.elapsed().as_millis();

    let t = Instant::now();
    let bnode = fold_chain_links(
        &b0,
        &b1,
        &FoldVkPins::tracked(&b0, &b1).expect("baseline pins"),
        &fold_cfg,
    )
    .expect("baseline fold");
    let base_fold_ms = t.elapsed().as_millis();
    verify_recursive_batch_proof_with_config(&bnode.0, &fold_cfg).expect("baseline node verifies");

    // ── PADDED: the same two links at the 3,048-lane carried claim. ─────────
    let t = Instant::now();
    let p0 = prove_padded_chain_leaf(&t0_trace, &pis[0], &inner).expect("padded leaf 0");
    let p1 = prove_padded_chain_leaf(&t1_trace, &pis[1], &inner).expect("padded leaf 1");
    let pad_leaves_ms = t.elapsed().as_millis();

    let t = Instant::now();
    let pnode = fold_padded_chain_links(
        &p0,
        &p1,
        &FoldVkPins::tracked(&p0, &p1).expect("padded pins"),
        &fold_cfg,
    )
    .expect("padded fold");
    let pad_fold_ms = t.elapsed().as_millis();
    verify_recursive_batch_proof_with_config(&pnode.0, &fold_cfg).expect("padded node verifies");

    println!("\n⚑⚑ THE CARRIED-LANE PROBE (same binary, same process, sequential):");
    println!(
        "  BASELINE  claim {CHAIN_CLAIM_LEN:>5} lanes: 2 leaves {base_leaves_ms:>7} ms, fold {base_fold_ms:>7} ms"
    );
    report("baseline leaf", &b0);
    report("baseline fold node", &bnode);
    println!(
        "  PADDED    claim {PADDED_CLAIM_LEN:>5} lanes: 2 leaves {pad_leaves_ms:>7} ms, fold {pad_fold_ms:>7} ms  \
         (+{SEAM_PAD_LANES} connects at the site)"
    );
    report("padded leaf", &p0);
    report("padded fold node", &pnode);
    let leaf_ratio = pad_leaves_ms as f64 / base_leaves_ms.max(1) as f64;
    let fold_ratio = pad_fold_ms as f64 / base_fold_ms.max(1) as f64;
    println!("  ratio: leaves ×{leaf_ratio:.2}, fold ×{fold_ratio:.2}");
    println!(
        "  decision input: elementwise seam ≈ fold ×{fold_ratio:.2} at every threaded site; \
         the acc fallback keeps ×1.00 but inserts a ~2^124 collision surface in the forcing path."
    );
}
