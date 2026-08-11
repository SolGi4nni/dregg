//! ⚑⚑⚑ **THE LEAF ADAPTER — TIE 1 STOPS BEING AN EXECUTOR COMPARISON.**
//!
//! One recursion circuit that verifies **both** STARKs — the gated body-preimage descriptor and one
//! link of the `state_body_hash` chain — so both claim vectors are in scope at once and the
//! Lean-authored seam can be applied between them.
//!
//! ## The measurement this module exists to answer
//!
//! `Dregg2.Circuit.Emit.MinaBodyPreimageSeams` §1 states the constraint that made the tie
//! unapplicable, and states it as a measurement rather than a preference:
//!
//! > *"`mina_phase2_chain_leaf`'s leaf exposes `in(96) ‖ out(96) ‖ seg_poseidon_commit(absorbed)` —
//! > **200 lanes, and the 64 ABSORBED LIMBS ARE NOT AMONG THEM**, only their 8-lane Poseidon
//! > commitment. So a seam against the chain's `expose_claim` (or against the fold ROOT, which
//! > carries the same 200 lanes) cannot reach the absorbed stream at all; the only surface that
//! > carries it is the leaf's own `air_public_targets.first()`. … **no fold in the tree today has
//! > both PI vectors in scope.**"*
//!
//! That is what this is. Both children are [`RecursionInput::NativeBatchStark`], so the aggregation
//! hook receives two **raw descriptor PI vectors** — 1 518 preimage slots and 256 chain slots — and
//! [`crate::seam::apply_seam`] welds them. The seam's `claim_len`s are exactly those two numbers
//! because the Lean object was authored for this surface and no other.
//!
//! ## ⚑ WHY THIS SHAPE AND NOT A CARRIED CLAIM — the evidence, not the taste
//!
//! The alternative was to wrap the preimage as its own recursion layer exposing its 1 518 slots as
//! a claim, then aggregate two `BatchOnly` children (which is the shape the deployed
//! CPU/GPU dispatch already carries). It is REFUSED, on a measurement: a padded **3 048-lane**
//! carried claim failed to fold with `WitnessConflict { witness_id: WitnessId(676) }`, because
//! `p3_circuit`'s `connect` is a union-find MERGE onto one witness slot and a wide padded carry
//! multiplies the classes that must agree. A 1 518-lane carry is the same shape one notch smaller.
//!
//! Applying the seam where both PI vectors are **already** bound adds **no carried lane at all** —
//! only 64 merges per link, against targets the two inner batch proofs already constrain. The
//! adapter's own exposed claim stays at the chain leaf's 200 lanes, unchanged.
//!
//! ## ⚑ IT IS A DROP-IN FOR THE CHAIN LEAF, WHICH IS THE POINT
//!
//! [`prove_body_preimage_link_adapter`] exposes exactly what
//! [`crate::mina_phase2_chain_leaf::prove_chain_link_leaf_with`] exposes —
//! `in_state(96) ‖ out_state(96) ‖ commit(absorbed)(8)`, `CHAIN_CLAIM_LEN` lanes, built from the
//! chain child's own FRI-bound targets. So [`crate::mina_phase2_chain_leaf::fold_chain_links`]
//! folds twenty-five adapters into the same root, `read_chain_claim` reads the same claim, and
//! `BODYHASH` is derived by the same 24 folds. What changed is not the root's SHAPE but its
//! SENTENCE: each link's absorbed pair is now welded, limb for limb, to a descriptor that gates
//! those limbs as bytes and gates the 2 381 chunk bits as bits.
//!
//! ## ⚠ STANDING, SAID BEFORE THE RESULT
//!
//! `apply_seam` issues `cb.connect`s. This is RECURSION WIRING, not AIR — House Law #1's
//! wiring category — it proves on a box and inherits the undischarged FRI/STARK floor, and it emits
//! no polynomial into either descriptor. What it replaces is a `WeldCover` naming an executor
//! function; what it does not do is make either descriptor say more than it says.
//!
//! ## ⚠ THE CPU AGGREGATION IS NAMED, NOT ASSUMED
//!
//! [`crate::gpu_backend::prove_recursion_aggregation_auto_with_expose`] is monomorphised to
//! `BatchOnly` on both sides — its GPU twin hand-builds a two-child `BatchOnly` verifier circuit —
//! so it cannot carry an `Ir2Air` child at all. This module therefore calls
//! `p3_recursion::build_and_prove_aggregation_layer_with_expose` directly, which IS generic over
//! two independent AIR types (`A1`, `A2`). That is a PERFORMANCE boundary and not a soundness one:
//! same circuit, same mint knobs, same proof shape, no GPU acceleration.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2Air, MemBoundaryWitness, UMemBoundaryWitness,
    ir2_airs_and_common_for_config, parse_vm_descriptor2, prove_vm_descriptor2_for_config,
};
use dregg_circuit::field::BabyBear;

use p3_recursion::{ProveNextLayerParams, RecursionInput, RecursionOutput, Target};

use crate::ivc_turn_chain::seg_poseidon_commit;
use crate::mina_phase2_chain_leaf::{
    ABSORBED_PI_LO, ABSORBED_WIDTH, CHAIN_CLAIM_LEN, CHAIN_PI_COUNT, IN_PI_LO, STATE_WIDTH,
};
use crate::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, create_recursion_backend, recursion_layer_over,
};
use crate::seam::{SeamSpec, apply_seam};

type RecursionChallenge = <DreggRecursionConfig as p3_uni_stark::StarkGenericConfig>::Challenge;

/// The extension degree the recursion tower runs at, as the rest of this crate states it.
const D: usize = 4;

/// The Lean-emitted preimage descriptor — `Dregg2.Circuit.Emit.MinaBodyPreimageBitsAir.bodyBitsDesc`
/// lowered by `EffectLower.lowerTiedAir`. Rust authors none of it.
const BODY_BITS_DESC_JSON: &str =
    include_str!("../../circuit/descriptors/by-name/dregg-mina-body-preimage-bits-v1.json");

/// `MinaBodyPreimageBitsAir.NBITS` — the packed half of `Body.to_input`.
pub const NBITS: usize = 2381;
/// `MinaBodyPreimageBitsAir.NLIMB` — `Σ ⌈W_e/8⌉` over the eleven packed runs.
pub const NLIMB: usize = 302;
/// `MinaBodyPreimageBitsAir.NFIELD` — the whole field elements `packToFields` prepends untouched.
pub const NFIELD: usize = 38;
/// `MinaBodyPreimageBitsAir.NFLIMB` — `NFIELD × SK`.
pub const NFLIMB: usize = NFIELD * 32;
/// `MinaBodyPreimageBitsAir.BODY_BITS_WIDTH`.
pub const BODY_BITS_WIDTH: usize = NBITS + NLIMB + NFLIMB;
/// `MinaBodyPreimageBitsAir.BODY_BITS_PI_COUNT` — and the seam's LEFT `claim_len`.
pub const BODY_BITS_PI_COUNT: usize = NFLIMB + NLIMB;
/// `MinaStateBodyHashChain.BODY_LINKS` — `⌈49/2⌉`, derived rather than counted.
pub const BODY_LINKS: usize = 25;

/// Parse the Lean-emitted body-preimage descriptor, refusing a shape this module cannot index.
pub fn body_preimage_descriptor() -> Result<EffectVmDescriptor2, String> {
    let desc = parse_vm_descriptor2(BODY_BITS_DESC_JSON)
        .map_err(|e| format!("body-preimage descriptor parse failed: {e}"))?;
    if desc.public_input_count != BODY_BITS_PI_COUNT {
        return Err(format!(
            "body-preimage descriptor declares {} PIs, expected {BODY_BITS_PI_COUNT}; refusing an \
             ambiguous claim layout — the 2026-08-09 flag day moved `PI_PLIMB` by +{NFLIMB} and a \
             consumer reading the old base reads field element 38",
            desc.public_input_count
        ));
    }
    if desc.trace_width != BODY_BITS_WIDTH {
        return Err(format!(
            "body-preimage descriptor declares width {}, expected {BODY_BITS_WIDTH}",
            desc.trace_width
        ));
    }
    Ok(desc)
}

/// The twenty-five Lean-emitted seam artifacts, in link order.
///
/// ⚑ Written out rather than generated: `include_str!` needs a literal path, and a macro that
/// builds twenty-five of them hides which files the binary actually carries. `EmitSeamSpecs.lean`
/// is the author; a drifted artifact is a named red in `circuit-prove/tests/seam_specs.rs`.
const BODY_PREIMAGE_SEAM_JSON: [&str; BODY_LINKS] = [
    include_str!("../../circuit/descriptors/seams/seam-body-preimage-link-0.json"),
    include_str!("../../circuit/descriptors/seams/seam-body-preimage-link-1.json"),
    include_str!("../../circuit/descriptors/seams/seam-body-preimage-link-2.json"),
    include_str!("../../circuit/descriptors/seams/seam-body-preimage-link-3.json"),
    include_str!("../../circuit/descriptors/seams/seam-body-preimage-link-4.json"),
    include_str!("../../circuit/descriptors/seams/seam-body-preimage-link-5.json"),
    include_str!("../../circuit/descriptors/seams/seam-body-preimage-link-6.json"),
    include_str!("../../circuit/descriptors/seams/seam-body-preimage-link-7.json"),
    include_str!("../../circuit/descriptors/seams/seam-body-preimage-link-8.json"),
    include_str!("../../circuit/descriptors/seams/seam-body-preimage-link-9.json"),
    include_str!("../../circuit/descriptors/seams/seam-body-preimage-link-10.json"),
    include_str!("../../circuit/descriptors/seams/seam-body-preimage-link-11.json"),
    include_str!("../../circuit/descriptors/seams/seam-body-preimage-link-12.json"),
    include_str!("../../circuit/descriptors/seams/seam-body-preimage-link-13.json"),
    include_str!("../../circuit/descriptors/seams/seam-body-preimage-link-14.json"),
    include_str!("../../circuit/descriptors/seams/seam-body-preimage-link-15.json"),
    include_str!("../../circuit/descriptors/seams/seam-body-preimage-link-16.json"),
    include_str!("../../circuit/descriptors/seams/seam-body-preimage-link-17.json"),
    include_str!("../../circuit/descriptors/seams/seam-body-preimage-link-18.json"),
    include_str!("../../circuit/descriptors/seams/seam-body-preimage-link-19.json"),
    include_str!("../../circuit/descriptors/seams/seam-body-preimage-link-20.json"),
    include_str!("../../circuit/descriptors/seams/seam-body-preimage-link-21.json"),
    include_str!("../../circuit/descriptors/seams/seam-body-preimage-link-22.json"),
    include_str!("../../circuit/descriptors/seams/seam-body-preimage-link-23.json"),
    include_str!("../../circuit/descriptors/seams/seam-body-preimage-link-24.json"),
];

/// ⚑ The seam at link `j`.
///
/// Lean: `MinaBodyPreimageSeams.bodyPreimageSeam j`; S1
/// `the_body_preimage_seams_weld_published_slots` (both ends are slots a real pin leg of the
/// deployed AIR publishes); S2 `bodyPreimageSeamCertifies`, refuted without its seam hypothesis by
/// `body_preimage_seam_S2_needs_the_seam`.
pub fn body_preimage_seam(j: usize) -> Result<SeamSpec, String> {
    let json = BODY_PREIMAGE_SEAM_JSON
        .get(j)
        .ok_or_else(|| format!("link {j} is outside the {BODY_LINKS}-link body-hash chain"))?;
    SeamSpec::parse(json)
}

/// ⚑ **THE CLAIM VECTOR IS NOT A SUFFIX OF THE ROW, AND THIS IS THE ONE PLACE THAT SAYS SO.**
///
/// The 2026-08-09 flag day put the PI vector in ABSORB order — the 38 whole field elements first,
/// then the eleven packed ones — while the ROW keeps the packed limbs BELOW the whole-field ones.
/// So the claim is a REORDERING of two row slices, not a tail.
///
/// ⚠ This function exists to be CHECKED AGAINST the Lean-emitted claim file, not to replace it:
/// `mina-body-preimage-bits-pis.txt` is `realPub`'s own output and is what a prover should hand in.
/// Agreement between the two is a real cross-check (two Lean functions, one layout); a Rust slice
/// standing alone would be a re-authored layout, which is the twin this cone keeps deleting.
pub fn claim_from_row(row: &[BabyBear]) -> Result<Vec<BabyBear>, String> {
    if row.len() != BODY_BITS_WIDTH {
        return Err(format!(
            "the body-preimage row is {BODY_BITS_WIDTH} cells, got {}",
            row.len()
        ));
    }
    let mut pis = Vec::with_capacity(BODY_BITS_PI_COUNT);
    pis.extend_from_slice(&row[NBITS + NLIMB..BODY_BITS_WIDTH]); // the 38 whole field elements
    pis.extend_from_slice(&row[NBITS..NBITS + NLIMB]); // …then the eleven packed ones
    debug_assert_eq!(pis.len(), BODY_BITS_PI_COUNT);
    Ok(pis)
}

/// ⚑⚑⚑ **THE LEAF ADAPTER.** Verify the preimage STARK and chain link `j`'s STARK in ONE circuit
/// and weld their claim vectors with the Lean-emitted seam.
///
/// * `preimage_*` — the gated preimage witness. ONE row plus zero padding; its claim is the 1 518
///   published limb slots.
/// * `chain_*` — link `j`'s witness, exactly what
///   [`crate::mina_phase2_chain_leaf::prove_chain_link_leaf_with`] would be handed.
/// * `inner_config` — the engine BOTH descriptor batches are minted at, and therefore the engine
///   the in-circuit verifiers check them against. The adapter's own output mints at
///   `recursion_layer_over(inner_config)`, the same engine a chain leaf's wrap mints at, which is
///   what makes the adapter foldable by `fold_chain_links` at `chain_root_config()`.
///
/// Returns the same `CHAIN_CLAIM_LEN`-lane claim a chain leaf publishes, so this is a drop-in.
///
/// ⚑ Both seam ends are checked by NAME **and by recomputed fingerprint lanes**
/// ([`crate::seam::SeamEnd::require_matches`]) against the descriptors this call actually loads,
/// before one witness cell is read. A stale artifact is a loud refusal here, not a silent misweld.
pub fn prove_body_preimage_link_adapter(
    preimage_desc: &EffectVmDescriptor2,
    preimage_trace: &[Vec<BabyBear>],
    preimage_pis: &[BabyBear],
    chain_desc: &EffectVmDescriptor2,
    chain_trace: &[Vec<BabyBear>],
    chain_pis: &[BabyBear],
    seam: &SeamSpec,
    inner_config: &DreggRecursionConfig,
) -> Result<RecursionOutput<DreggRecursionConfig>, String> {
    // ── The seam is checked against the descriptors THIS call loads, both ends, before anything
    // is proved. `require_matches` recomputes the fingerprint; a display name is not a key.
    seam.left.require_matches(preimage_desc).map_err(|e| {
        format!("body-preimage adapter: the seam's LEFT end is not the preimage descriptor: {e}")
    })?;
    seam.right.require_matches(chain_desc).map_err(|e| {
        format!("body-preimage adapter: the seam's RIGHT end is not the chain-link descriptor: {e}")
    })?;
    if seam.left.claim_len != preimage_desc.public_input_count {
        return Err(format!(
            "seam `{}` names a {}-lane left claim; the preimage descriptor publishes {}",
            seam.name, seam.left.claim_len, preimage_desc.public_input_count
        ));
    }
    if seam.right.claim_len != CHAIN_PI_COUNT {
        return Err(format!(
            "seam `{}` names a {}-lane right claim; a chain link publishes {CHAIN_PI_COUNT}",
            seam.name, seam.right.claim_len
        ));
    }
    if preimage_pis.len() != seam.left.claim_len {
        return Err(format!(
            "the preimage claim carries {} lanes, the seam welds {}",
            preimage_pis.len(),
            seam.left.claim_len
        ));
    }
    if chain_pis.len() != CHAIN_PI_COUNT {
        return Err(format!(
            "a chain link carries exactly {CHAIN_PI_COUNT} public inputs, got {}",
            chain_pis.len()
        ));
    }

    // ── The two inner batch proofs, minted at the SAME engine so one aggregation config can
    // describe both children.
    let preimage_inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        preimage_desc,
        preimage_trace,
        preimage_pis,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        inner_config,
    )
    .map_err(|e| format!("body-preimage inner IR-v2 prove failed: {e}"))?;
    let chain_inner = prove_vm_descriptor2_for_config::<DreggRecursionConfig>(
        chain_desc,
        chain_trace,
        chain_pis,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        inner_config,
    )
    .map_err(|e| format!("chain-link inner IR-v2 prove failed: {e}"))?;

    let (preimage_airs, preimage_tpi, preimage_common) = ir2_airs_and_common_for_config(
        preimage_desc,
        &preimage_inner,
        preimage_pis,
        inner_config,
    )
    .map_err(|e| format!("body-preimage verify-triple build failed: {e}"))?;
    let (chain_airs, chain_tpi, chain_common) =
        ir2_airs_and_common_for_config(chain_desc, &chain_inner, chain_pis, inner_config)
            .map_err(|e| format!("chain-link verify-triple build failed: {e}"))?;

    let left: RecursionInput<'_, DreggRecursionConfig, Ir2Air> = RecursionInput::NativeBatchStark {
        airs: &preimage_airs,
        proof: &preimage_inner,
        common_data: &preimage_common,
        table_public_inputs: preimage_tpi,
    };
    let right: RecursionInput<'_, DreggRecursionConfig, Ir2Air> = RecursionInput::NativeBatchStark {
        airs: &chain_airs,
        proof: &chain_inner,
        common_data: &chain_common,
        table_public_inputs: chain_tpi,
    };

    let left_len = seam.left.claim_len;
    let expose = move |cb: &mut p3_circuit::CircuitBuilder<RecursionChallenge>,
                       left_apt: &[Vec<Target>],
                       right_apt: &[Vec<Target>],
                       _left_vk_cap: &[Target],
                       _right_vk_cap: &[Target]| {
        // ⚑ BOTH RAW DESCRIPTOR PI VECTORS, IN SCOPE AT ONCE. This is the whole object: `apt[0]`
        // is the main AIR's public values, i.e. the descriptor's own public inputs, which the
        // inner batch proof binds. The 64 absorbed limbs live HERE and in no `expose_claim`.
        let lmain = left_apt
            .first()
            .expect("the preimage batch has a main instance carrying the descriptor PIs");
        let rmain = right_apt
            .first()
            .expect("the chain link has a main instance carrying the descriptor PIs");
        assert!(
            lmain.len() >= left_len,
            "the preimage main instance carries {} targets, the seam welds {left_len}",
            lmain.len()
        );
        assert!(
            rmain.len() >= CHAIN_PI_COUNT,
            "the chain main instance carries {} targets, a link publishes {CHAIN_PI_COUNT}",
            rmain.len()
        );

        // ⚑⚑ THE WELD. Every index comes out of the Lean-emitted artifact; this function authors
        // none of it. 1 518 pins and 82 zero-pins across the family, 64 merges at this link.
        let issued = apply_seam(cb, &lmain[..left_len], &rmain[..CHAIN_PI_COUNT], seam);
        debug_assert_eq!(issued, seam.connect_count());

        // ⚑ …and the adapter publishes exactly what a chain leaf publishes, from the chain
        // child's own bound targets — so twenty-five adapters fold with the identical node.
        let mut claim: Vec<Target> = (0..2 * STATE_WIDTH).map(|k| rmain[IN_PI_LO + k]).collect();
        let absorbed: Vec<Target> = (0..ABSORBED_WIDTH)
            .map(|k| rmain[ABSORBED_PI_LO + k])
            .collect();
        claim.extend_from_slice(&seg_poseidon_commit(cb, &absorbed));
        debug_assert_eq!(claim.len(), CHAIN_CLAIM_LEN);
        cb.expose_as_public_output(&claim);
    };

    // ⚑ The aggregation engine: the same one a chain LEAF WRAP mints at, derived rather than
    // named, so the adapter drops into `fold_chain_links` at `chain_root_config()` with no
    // second config for a caller to get wrong.
    let agg_config = recursion_layer_over(inner_config);
    let backend = create_recursion_backend();
    p3_recursion::build_and_prove_aggregation_layer_with_expose::<
        DreggRecursionConfig,
        Ir2Air,
        Ir2Air,
        _,
        D,
    >(
        &left,
        &right,
        &agg_config,
        &backend,
        &ProveNextLayerParams::default(),
        None,
        Some(&expose),
    )
    .map_err(|e| format!("body-preimage leaf adapter failed: {e:?}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The constants this module indexes with are the descriptor's own, and the claim layout has
    /// no aliasing.
    #[test]
    fn the_preimage_layout_agrees_with_the_served_descriptor() {
        let d = body_preimage_descriptor().expect("the Lean preimage descriptor parses");
        assert_eq!(d.name, "dregg-mina-body-preimage-bits::v1");
        assert_eq!(d.public_input_count, BODY_BITS_PI_COUNT);
        assert_eq!(BODY_BITS_PI_COUNT, 1518);
        assert_eq!(d.trace_width, BODY_BITS_WIDTH);
        assert_eq!(BODY_BITS_WIDTH, 3899);
        // The claim is a REORDERING of two row slices, and the two slices are disjoint and cover
        // the non-bit half of the row exactly.
        assert_eq!(NFLIMB + NLIMB, BODY_BITS_PI_COUNT);
        assert_eq!(NBITS + NLIMB + NFLIMB, BODY_BITS_WIDTH);
    }

    /// ⚑ All twenty-five seams parse, validate, and cover the claim exactly once between them —
    /// the artifact-side twin of `MinaBodyPreimageSeams.every_published_slot_is_welded_exactly_once`
    /// and `the_seams_cover_every_absorbed_limb`.
    #[test]
    fn the_twenty_five_seams_cover_the_whole_claim_exactly_once() {
        let mut left_slots: Vec<usize> = Vec::new();
        let mut zero_right = 0usize;
        let mut connects = 0usize;
        for j in 0..BODY_LINKS {
            let s = body_preimage_seam(j).unwrap_or_else(|e| panic!("seam {j}: {e}"));
            assert_eq!(s.name, format!("dregg-seam-body-preimage-link-{j}::v1"));
            assert_eq!(s.left.claim_len, BODY_BITS_PI_COUNT);
            assert_eq!(s.right.claim_len, CHAIN_PI_COUNT);
            assert!(
                s.zero_left.is_empty(),
                "every zero-pin is on the CHAIN side — the preimage publishes no inert slot"
            );
            left_slots.extend(s.pins.iter().map(|&(l, _)| l));
            zero_right += s.zero_right.len();
            connects += s.connect_count();
        }
        left_slots.sort_unstable();
        assert_eq!(
            left_slots,
            (0..BODY_BITS_PI_COUNT).collect::<Vec<_>>(),
            "the 1 518 pins' left endpoints must be a PERMUTATION of the claim — a duplicate is an \
             aliasing bug a count alone cannot see, and a gap is a limb the prover keeps"
        );
        assert_eq!(zero_right, 82, "the `32 − ⌈W_e/8⌉` deficit plus the pad's 32");
        assert_eq!(
            connects,
            BODY_LINKS * 2 * 32,
            "every absorbed limb of every link is either welded or pinned to zero, with nothing \
             left free"
        );
    }

    /// ⚑ Link `j` welds elements `2j` and `2j+1` onto the chain's two absorbed windows, and
    /// nothing else — the right endpoints live in `[192, 256)`.
    #[test]
    fn every_weld_lands_in_the_chain_links_absorbed_window() {
        for j in 0..BODY_LINKS {
            let s = body_preimage_seam(j).unwrap();
            for &(_, r) in &s.pins {
                assert!(
                    (ABSORBED_PI_LO..CHAIN_PI_COUNT).contains(&r),
                    "seam {j} welds chain slot {r}, outside the absorbed window \
                     [{ABSORBED_PI_LO}, {CHAIN_PI_COUNT}) — a weld into the state block would tie \
                     the preimage to the sponge instead of to the stream"
                );
            }
            for &r in &s.zero_right {
                assert!((ABSORBED_PI_LO..CHAIN_PI_COUNT).contains(&r));
            }
        }
    }
}
