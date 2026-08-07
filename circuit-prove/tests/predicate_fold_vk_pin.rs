//! ⚑⚑ **THE CHILD-VK PIN OUTSIDE THE MINA TOWER — measured on the bridge-predicate relations.**
//!
//! ⚠ **LABEL FIRST.** These are Rust **case-tests**. Not translation validation, not refinement and
//! not verification — there is no formal semantics of Rust and a case-test says nothing about all
//! inputs. What they establish is behavioural: on this box, at this rev, an unpinned fold mints the
//! same parent VK over two DIFFERENT child circuits, and a pinned fold refuses the substitution.
//! "It proves on a box" is not verified and not sound; everything below inherits the undischarged
//! FRI/STARK floor. This file authors **no AIR** — House Law #1 holds, every relation under it comes
//! out of Lean (`descriptor_by_name`'s emitted `dregg-predicate-arith-*` artifacts). It is recursion
//! *wiring*.
//!
//! # WHAT WAS OPEN, AND WHERE
//!
//! `RecursionOutput::into_recursion_input` passes `expected_preprocessed_commit: None`
//! (`recursion/src/recursion.rs` at the pinned fork rev `fc3c6df`), and that field's own docblock
//! says a from-scratch prover could then fold a proof of a **DIFFERENT circuit**. `685a62a32`
//! closed it for the four folds of the Mina tower. **Sixty-six call sites outside that tower did
//! not have it** — the leaf adapters, the joint-turn binding nodes, the cohort spine, the solvency
//! union, the accumulator, the wide K-fold tree and both apex shrinks.
//!
//! # ⚑ THE ADVERSARY IS NOT SYNTHETIC AND IT IS NOT MINA'S
//!
//! `dregg-predicate-arith-ge::threshold-v1`, `-le` and `-gt` are Lean-emitted descriptors of
//! **identical outer shape** — 25 trace columns, 2 public inputs, the same table set at the same
//! arities — that state **different relations**: `≥` judges `value − threshold` through the range
//! lookup, `≤` judges `threshold − value`, `>` judges `value − threshold − 1`. All three have real
//! witness builders in-process (`predicate_arith_witness` / `predicate_le_witness` /
//! `predicate_gt_witness`), and each child's own proof is VERIFIED before it is folded — so a
//! substituted child is a **VALID proof of a different circuit**, not a corrupted one.
//!
//! ⚑ **And the substitution means something.** A credential presenting "my balance is AT MOST 40"
//! folded into the slot that anchors "my balance is AT LEAST 40" is the whole point of a threshold
//! predicate, inverted. This is a sharper adversary than a constants-only twin: the fold cannot
//! tell `≤` from `>`.
//!
//! §0 asserts the shape agreement and the relational difference **constructively, before any verdict
//! is read** — this repo has shipped an adversary that quietly became a no-op, so the difference is
//! asserted first and each witness is checked to be genuinely satisfying at mint time.
//!
//! # WHAT THE THREE SECTIONS SEPARATE
//!
//! * **§1 — a LEAF-WRAP is already separated, so pinning one buys nothing.** A leaf wrap builds
//!   `RecursionInput::NativeBatchStark { airs, … }`: the descriptor's own AIRs are handed to the
//!   verifier circuit, so its constants are compiled into the wrap's static op list and land in the
//!   wrap's preprocessed commitment.
//! * **§2 — a FOLD does not, and that is the bite.** A fold builds `RecursionInput::BatchStark`,
//!   where the child is re-verified through the FIXED `CircuitTablesAir` reconstruction: only the
//!   child's `CommonData` **shape** reaches the parent's op list, while its preprocessed commitment
//!   rides as a **runtime public input** and `PublicAir`'s value columns are main-trace only.
//! * **§3 — pinned, the substitution is UNSAT and the roots separate.** Control lands, adversary is
//!   refused, honest lands, and the two pinned roots' fingerprints differ.
//!
//! ⚠ **The refusal is the CIRCUIT'S.** There is deliberately **no host comparison** of a pin against
//! a child's actual commitment, here or in the folds this exercises; a producer-side pre-flight
//! would fire first and leave the in-circuit constraint untested.
//!
//! # WHAT THIS DOES AND DOES NOT COVER
//!
//! The object under test is the aggregation layer's `expected_preprocessed_commit` constraint —
//! **the same constraint every pinned fold in this crate now adds**, reached through the same
//! `build_and_prove_aggregation_layer` primitive each of those folds calls. It is **not** an
//! end-to-end run of a leaf adapter: those need carrier witnesses this test does not mint. It
//! measures the mechanism in a non-Mina tower; it does not re-measure each of the 27 folds.
//!
//! # ⚑ MEASURED 2026-08-07, release, on a co-tenant box (load 8–56 over the run)
//!
//! ```text
//!   §0  trace_width 25 · PIs 2 · 1 table · 7 constraints — IDENTICAL across ≥ / ≤ / >
//!       constraint systems DIFFER (869 / 869 / 884 bytes of debug shape)
//!   §1  leaf-wrap RecursionVk  ≥ ac0bf962…  ≤ 95df17b8…  > f858420e…   ALL THREE DIFFER
//!   §2  UNPINNED fold (≥,≤) LANDED 7236 ms   parent RecursionVk ea811150…
//!       UNPINNED fold (≥,>) LANDED 5465 ms   parent RecursionVk ea811150…   ← IDENTICAL
//!   §3  CONTROL   (≥,≤ children · ≥,≤ pins)  LANDED  8712 ms
//!       ADVERSARY (≥,≤ children · ≥,> pins)  REFUSED    99 ms
//!       HONEST    (≥,> children · ≥,> pins)  LANDED  5998 ms
//!       pinned parent RecursionVk  (≥,≤) 00e3a5fb…   (≥,>) 1bd00357…   — and both ≠ ea811150…
//! ```
//!
//! ⚠ **QUOTE THE BAND, NOT A NUMBER.** The two §2 folds do the same amount of work and differ by
//! 1.3x; the box carried a sibling's Lean builds throughout and the release compile alone took
//! 21m40s against a 36s test body. A single figure off this tree has been wrong in both directions.
//!
//! ⚑ The refusal reads `Circuit(WitnessConflict { witness_id: WitnessId(256), … })` — the
//! aggregation layer's own witness solver. That is what "the refusal is the circuit's" means
//! concretely, and it costs ~1% of an honest fold because it fails during witness generation rather
//! than in the prover.
//!
//! Run: `cargo test -p dregg-circuit-prove --release --test predicate_fold_vk_pin -- --nocapture`

use std::time::Instant;

use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, UMemBoundaryWitness, prove_vm_descriptor2_for_config,
    verify_vm_descriptor2_with_config,
};
use dregg_circuit::predicate_arith_witness::{Blinding, FactBinding, predicate_arith_witness};
use dregg_circuit::predicate_comparison_witness::{predicate_gt_witness, predicate_le_witness};
use dregg_circuit_prove::fold_vk_pin::{FoldVkPins, VK_PIN_FELTS_PER_CHILD, child_vk_commit};
use dregg_circuit_prove::ivc_turn_chain::{
    ir2_leaf_wrap_config, prove_descriptor_leaf_rotated_with_config,
};
use dregg_circuit_prove::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, create_recursion_backend, recursion_vk_fingerprint,
    verify_recursive_batch_proof_with_config,
};
use p3_recursion::{
    BatchOnly, ProveNextLayerParams, RecursionOutput, build_and_prove_aggregation_layer,
};

const GE: &str = "dregg-predicate-arith-ge::threshold-v1";
const LE: &str = "dregg-predicate-arith-le::threshold-v1";
const GT: &str = "dregg-predicate-arith-gt::threshold-v1";

/// The aggregation-layer arity this crate's folds are built at.
const D: usize = 4;

/// A fixed, non-private fact binding. `Blinding::NONE` deliberately: this is a KAT, linkability is
/// intended, and the pin's verdict does not depend on the blinding.
fn fact() -> FactBinding {
    FactBinding {
        predicate_sym: BabyBear::new(7),
        term1: BabyBear::new(11),
        term2: BabyBear::new(13),
        state_root: BabyBear::new(17),
    }
}

fn desc(name: &str) -> EffectVmDescriptor2 {
    descriptor_by_name(name)
        .unwrap_or_else(|| panic!("{name} dispatches through descriptor_by_name"))
}

/// Prove one predicate relation under the leaf-wrap config and wrap it as a recursion leaf.
///
/// This is the `RecursionInput::NativeBatchStark` path — the LEAF-WRAP arm, where the descriptor's
/// own AIRs are compiled into the verifier circuit's static op list.
fn mint_leaf(
    name: &str,
    trace: &[Vec<BabyBear>],
    pis: &[BabyBear],
) -> (RecursionOutput<DreggRecursionConfig>, u128) {
    let config = ir2_leaf_wrap_config();
    let descriptor = desc(name);
    let t0 = Instant::now();
    let proof = prove_vm_descriptor2_for_config(
        &descriptor,
        trace,
        pis,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        &config,
    )
    .unwrap_or_else(|e| panic!("{name} proves under the leaf-wrap config: {e}"));
    // ⚠ The child must be a VALID proof of its own relation, not merely a byte string: an adversary
    // built out of a REJECTED proof would measure the wrong thing entirely.
    verify_vm_descriptor2_with_config(&descriptor, &proof, pis, &config)
        .unwrap_or_else(|e| panic!("{name}'s own proof must VERIFY before it is folded: {e}"));
    let leaf = prove_descriptor_leaf_rotated_with_config(&descriptor, &proof, pis, &config)
        .unwrap_or_else(|e| panic!("{name} wraps as a recursion leaf: {e}"));
    (leaf, t0.elapsed().as_millis())
}

// ============================================================================
// §0 — THE ADVERSARY IS SAME-SHAPE AND A DIFFERENT RELATION.
//      Cheap, unconditional, and asserted BEFORE any fold is built.
// ============================================================================

#[test]
fn s0_the_predicate_relations_are_same_shape_and_genuinely_different() {
    let g = desc(GE);
    let l = desc(LE);
    let t = desc(GT);

    for (name, other) in [(LE, &l), (GT, &t)] {
        assert_eq!(
            g.trace_width, other.trace_width,
            "{GE} and {name} must agree on trace width"
        );
        assert_eq!(
            g.public_input_count, other.public_input_count,
            "{GE} and {name} must agree on public-input count"
        );
        assert_eq!(
            g.tables.len(),
            other.tables.len(),
            "{GE} and {name} must agree on table count"
        );
        for (i, (a, b)) in g.tables.iter().zip(other.tables.iter()).enumerate() {
            assert_eq!(
                a.arity, b.arity,
                "table {i} arity must agree ({GE} vs {name})"
            );
        }
    }
    println!(
        "  §0 shape: trace_width {} · PIs {} · tables {} · constraints ge {} / le {} / gt {}",
        g.trace_width,
        g.public_input_count,
        g.tables.len(),
        g.constraints.len(),
        l.constraints.len(),
        t.constraints.len()
    );

    // ⚑ AND THEY ARE GENUINELY DIFFERENT RELATIONS — asserted at the level a substitution acts on:
    // the descriptors' own names and their constraint systems. A mutation that became a no-op is
    // this repo's recorded failure; this is the assertion that makes one visible.
    assert_ne!(g.name, l.name);
    assert_ne!(g.name, t.name);
    assert_ne!(l.name, t.name);
    let gj = format!("{:?}", g.constraints);
    let lj = format!("{:?}", l.constraints);
    let tj = format!("{:?}", t.constraints);
    assert_ne!(
        gj, lj,
        "⚑ THE ADVERSARY IS A NO-OP: the ≥ and ≤ descriptors carry IDENTICAL constraint systems, so \
         substituting one for the other substitutes nothing and every verdict below is vacuous."
    );
    assert_ne!(lj, tj, "the ≤ and > descriptors must differ");
    println!(
        "  §0 relations: ge/le constraint systems DIFFER ({} vs {} bytes of debug shape); le/gt \
         DIFFER ({} bytes) — ≥, ≤ and > are three different judgements of the same two public inputs",
        gj.len(),
        lj.len(),
        tj.len()
    );
}

// ============================================================================
// §1–§3 — the folds. One test, because each section's verdict is only meaningful
//         against the others' (a refusal alone proves nothing about satisfiability).
// ============================================================================

#[test]
fn s123_the_unpinned_fold_cannot_tell_two_relations_apart_and_the_pinned_one_can() {
    let config = ir2_leaf_wrap_config();
    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();
    let f = fact();

    // Three HONEST witnesses, each satisfying its own relation: 100 ≥ 40, 30 ≤ 40, 100 > 40.
    let (ge_trace, ge_pis) =
        predicate_arith_witness(100, 40, f, Blinding::NONE, 4).expect("≥ witness builds");
    let (le_trace, le_pis) =
        predicate_le_witness(30, 40, f, Blinding::NONE, 4).expect("≤ witness builds");
    let (gt_trace, gt_pis) =
        predicate_gt_witness(100, 40, f, Blinding::NONE, 4).expect("> witness builds");

    let (leaf_ge, ms_ge) = mint_leaf(GE, &ge_trace, &ge_pis);
    let (leaf_le, ms_le) = mint_leaf(LE, &le_trace, &le_pis);
    let (leaf_gt, ms_gt) = mint_leaf(GT, &gt_trace, &gt_pis);
    println!("\n  leaf wraps: ≥ {ms_ge} ms · ≤ {ms_le} ms · > {ms_gt} ms");

    // ------------------------------------------------------------------
    // §1 — the LEAF-WRAP layer already separates the relations.
    // ------------------------------------------------------------------
    let c_ge = child_vk_commit(&leaf_ge, "≥ leaf").expect("≥ leaf has a preprocessed commit");
    let c_le = child_vk_commit(&leaf_le, "≤ leaf").expect("≤ leaf has a preprocessed commit");
    let c_gt = child_vk_commit(&leaf_gt, "> leaf").expect("> leaf has a preprocessed commit");
    let f_ge = recursion_vk_fingerprint(&leaf_ge.0);
    let f_le = recursion_vk_fingerprint(&leaf_le.0);
    let f_gt = recursion_vk_fingerprint(&leaf_gt.0);
    println!(
        "  §1 leaf-wrap RecursionVk  ≥ {}\n     leaf-wrap RecursionVk  ≤ {}\n     leaf-wrap RecursionVk  > {}",
        f_ge.to_hex(),
        f_le.to_hex(),
        f_gt.to_hex()
    );
    assert_ne!(
        c_le, c_gt,
        "⚑ CLASSIFICATION FAILS: two different relations produced the SAME leaf-wrap preprocessed \
         commitment. If a leaf wrap does NOT compile the inner AIR into its op list, leaf-wrap \
         sites are in the hole too and §1's verdict is wrong."
    );
    assert_ne!(f_le, f_gt, "the ≤ and > leaf-wrap RecursionVks must differ");
    println!(
        "     → LEAF WRAPS ARE SEPARATED. A leaf-wrap site is NOT in the hole; pinning one costs \
         {VK_PIN_FELTS_PER_CHILD} consts + {VK_PIN_FELTS_PER_CHILD} connects per child and buys nothing."
    );

    // ------------------------------------------------------------------
    // §2 — THE BITE. Two folds over DIFFERENT right children, UNPINNED.
    //      The unpinned inputs are built here from the fork API on purpose:
    //      no production fold in this crate builds one any more.
    // ------------------------------------------------------------------
    let t = Instant::now();
    let unpinned_le =
        build_and_prove_aggregation_layer::<DreggRecursionConfig, BatchOnly, BatchOnly, _, D>(
            &leaf_ge.into_recursion_input::<BatchOnly>(),
            &leaf_le.into_recursion_input::<BatchOnly>(),
            &config,
            &backend,
            &params,
            None,
        )
        .expect("the UNPINNED fold of (≥, ≤) lands — the honest baseline");
    let ms_ule = t.elapsed().as_millis();

    let t = Instant::now();
    let unpinned_gt = build_and_prove_aggregation_layer::<
        DreggRecursionConfig,
        BatchOnly,
        BatchOnly,
        _,
        D,
    >(
        &leaf_ge.into_recursion_input::<BatchOnly>(),
        // ⚑ THE SUBSTITUTED CHILD. A VALID proof — of a DIFFERENT relation.
        &leaf_gt.into_recursion_input::<BatchOnly>(),
        &config,
        &backend,
        &params,
        None,
    )
    .expect(
        "⚑ THE SUBSTITUTED FOLD LANDS. That is the defect: `expected_preprocessed_commit: None` \
         admits a child of identical table shape whose preprocessed content — its whole relation — \
         is a different one.",
    );
    let ms_ugt = t.elapsed().as_millis();

    verify_recursive_batch_proof_with_config(&unpinned_le.0, &config)
        .expect("the unpinned (≥,≤) root verifies");
    verify_recursive_batch_proof_with_config(&unpinned_gt.0, &config)
        .expect("the unpinned (≥,>) root verifies — a full proof, of the wrong relation pair");

    let u_le = recursion_vk_fingerprint(&unpinned_le.0);
    let u_gt = recursion_vk_fingerprint(&unpinned_gt.0);
    println!(
        "\n  §2 UNPINNED fold (≥,≤) LANDED {ms_ule} ms  parent RecursionVk {}\n     UNPINNED fold (≥,>) LANDED {ms_ugt} ms  parent RecursionVk {}",
        u_le.to_hex(),
        u_gt.to_hex()
    );
    assert_eq!(
        u_le, u_gt,
        "⚑ MEASUREMENT CORRECTS THE CLAIM: the two unpinned folds minted DIFFERENT parent VKs, so \
         in THIS tower an unpinned fold root already separates the two child relations and the bite \
         is narrower than stated. Report this rather than the docblock."
    );
    println!(
        "     → ⚑ THE BITE. Two folds over DIFFERENT child relations minted the SAME parent VK. A \
         consumer anchoring that fold root cannot tell a ≤ child from a > one."
    );

    // ------------------------------------------------------------------
    // §3 — PINNED: the substitution is UNSAT and the honest roots separate.
    // ------------------------------------------------------------------
    let t = Instant::now();
    let control =
        build_and_prove_aggregation_layer::<DreggRecursionConfig, BatchOnly, BatchOnly, _, D>(
            &leaf_ge.into_recursion_input_pinned::<BatchOnly>(c_ge.clone()),
            &leaf_le.into_recursion_input_pinned::<BatchOnly>(c_le.clone()),
            &config,
            &backend,
            &params,
            None,
        )
        .expect(
            "the CONTROL (≤ child, ≤ pin) must LAND — otherwise the adversary's refusal below is \
             attributable to the pin machinery rather than to the substitution",
        );
    let ms_control = t.elapsed().as_millis();

    // ⚑ THE ADVERSARY. The SAME two children as the control — only the right pin changes, to the
    // `>` leaf's commitment. ⚠ No host comparison fires: the fold is handed the pin and the child
    // and never compares them.
    let pins_adv = FoldVkPins::new(c_ge.clone(), c_gt.clone());
    assert_ne!(
        pins_adv.right, c_le,
        "the adversary pin must actually differ from the right child's genuine commitment — if it \
         did not, the refusal below would be measuring nothing"
    );
    let t = Instant::now();
    let adversary =
        build_and_prove_aggregation_layer::<DreggRecursionConfig, BatchOnly, BatchOnly, _, D>(
            &leaf_ge.into_recursion_input_pinned::<BatchOnly>(pins_adv.left.clone()),
            &leaf_le.into_recursion_input_pinned::<BatchOnly>(pins_adv.right.clone()),
            &config,
            &backend,
            &params,
            None,
        );
    let ms_adv = t.elapsed().as_millis();
    let refusal = match adversary {
        Ok(_) => panic!(
            "⚑ THE PINNED FOLD ACCEPTED A CHILD WHOSE COMMITMENT DIFFERS FROM ITS PIN. The pin is \
             not reaching the constraint system: `expected_preprocessed_commit: Some(..)` is being \
             dropped somewhere between `into_recursion_input_pinned` and the aggregation circuit."
        ),
        Err(e) => format!("{e:?}"),
    };
    println!(
        "\n  §3 CONTROL   (≥,≤ children · ≥,≤ pins)  LANDED  {ms_control} ms\n     ADVERSARY (≥,≤ children · ≥,> pins)  REFUSED {ms_adv} ms\n     refusal: {}",
        refusal.chars().take(200).collect::<String>()
    );

    let t = Instant::now();
    let honest =
        build_and_prove_aggregation_layer::<DreggRecursionConfig, BatchOnly, BatchOnly, _, D>(
            &leaf_ge.into_recursion_input_pinned::<BatchOnly>(c_ge.clone()),
            &leaf_gt.into_recursion_input_pinned::<BatchOnly>(c_gt.clone()),
            &config,
            &backend,
            &params,
            None,
        )
        .expect("the HONEST (> child, > pin) fold must LAND");
    let ms_honest = t.elapsed().as_millis();

    let p_le = recursion_vk_fingerprint(&control.0);
    let p_gt = recursion_vk_fingerprint(&honest.0);
    println!(
        "     HONEST    (≥,> children · ≥,> pins)  LANDED  {ms_honest} ms\n     pinned parent RecursionVk (≥,≤) {}\n     pinned parent RecursionVk (≥,>) {}",
        p_le.to_hex(),
        p_gt.to_hex()
    );
    assert_ne!(
        p_le, p_gt,
        "⚑ THE PIN DOES NOT REACH THE PARENT VK. Two pinned folds over different child relations \
         minted the same fingerprint, so consequence (2) — a substituted child moves the root a \
         consumer anchors — does not hold and the pin closes only the in-circuit half."
    );
    assert_ne!(
        p_le, u_le,
        "the pinned parent VK must differ from the unpinned one: the pin adds constants to the \
         parent's op list, so a fold root's fingerprint MOVES. This is the flag day."
    );
    println!(
        "     → pinned roots SEPARATE, and both differ from the unpinned root: every pinned fold \
         root's RecursionVk MOVES. ⚠ Any externally held anchor for one is stale."
    );
}
