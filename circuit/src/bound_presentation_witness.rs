//! Rust witness builder for the emitted **bound-presentation** descriptor
//! (`dregg-bound-presentation::v1`, authored in
//! `metatheory/Dregg2/Circuit/Emit/BoundPresentationEmit.lean` as `boundPresentationDesc`).
//!
//! ## What this closes (Golden Lift, stage 3a)
//!
//! [`crate::presentation_descriptor_witness`] builds the summary+freshness descriptor whose
//! `presentation_tag` (summary col 10) is a bare PI copy — its HASH well-formedness was an
//! OFF-descriptor named STARK leaf, invisible to a light client / the recursion fold.
//! `boundPresentationDesc` (Stage 1) internalized that tooth: the tag PI is now tied IN-CIRCUIT to
//! `Poseidon2(final_root, presentation_randomness, verifier_nonce, DSK)` by an arity-4 `TID_P2` chip
//! lookup (the same lever [`crate::membership_descriptor_4ary`] uses for its `hash_4_to_1` levels).
//! Until now there was NO production witness builder that could produce a descriptor-matching trace;
//! this module is that builder, so consumers of [`crate::descriptor_by_name::descriptor_by_name`] can
//! prove+verify a bound presentation through the real p3 prover. This unblocks the flip (S3b/c).
//!
//! ## The trace layout (a single logical row, repeated to a power-of-two height)
//!
//! | col     | name              | meaning                                                        |
//! |---------|-------------------|----------------------------------------------------------------|
//! | 0       | federation_root   | PI 0 (summary copy)                                            |
//! | 1..8    | action_binding    | PI 1..8 (`request_predicate`, 8 felts)                        |
//! | 9       | timestamp         | PI 9                                                           |
//! | 10      | presentation_tag  | PI 10 AND chip out0 (the internalized hash tooth)             |
//! | 11..18  | revealed_facts    | PI 11..18 (8 felts)                                           |
//! | 19      | final_root        | HIDDEN witness (tag preimage); NOT a PI                       |
//! | 20      | randomness        | HIDDEN witness (unlinkability); NOT a PI                      |
//! | 21      | verifier_nonce    | PI 19 (`PI_NONCE`) — the verifier's public challenge          |
//! | 22..28  | tag_lanes         | the 7 witnessed Poseidon2 chip output lanes 1..7 of the tag   |
//!
//! `presentation_tag` (col 10) is the arity-4 chip absorb out0 of
//! `[final_root, randomness, verifier_nonce, DSK]`; cols 22..28 are the genuine permutation lanes
//! 1..7 of the same absorb, so the descriptor's `TID_P2` lookup is SERVED (a forged tag or lane has
//! no serving chip row → UNSAT — the FAITHFUL, non-lossy Poseidon2 binding). The tag PI copy binds
//! `pi[10] == loc[10]`, so the PUBLIC tag equals the genuine Poseidon2 image.

use crate::descriptor_ir2::{CHIP_OUT_LANES, chip_absorb_all_lanes};
use crate::field::BabyBear;

// ---- Column layout (mirror `BoundPresentationEmit.lean` §1). ----
/// Summary col 0: `federation_root`.
pub const FEDERATION_ROOT: usize = 0;
/// Summary cols 1..=8: `action_binding` / `request_predicate` (8 felts).
pub const REQUEST_PREDICATE_BASE: usize = 1;
/// Summary col 9: `timestamp`.
pub const TIMESTAMP: usize = 9;
/// Summary col 10: `presentation_tag` (constrained in-circuit to its Poseidon2 image = chip out0).
pub const PRESENTATION_TAG: usize = 10;
/// Summary cols 11..=18: `revealed_facts_commitment` (8 felts).
pub const REVEALED_FACTS_BASE: usize = 11;
/// The deployed summary width (`1 + 8 + 1 + 1 + 8`).
pub const SUMMARY_WIDTH: usize = 19;

/// Tag-binding col 19: `final_root` — end-of-chain state root; a HIDDEN witness (not a PI).
pub const FINAL_ROOT: usize = 19;
/// Tag-binding col 20: `presentation_randomness` — fresh per presentation; HIDDEN (unlinkability).
pub const RANDOMNESS: usize = 20;
/// Tag-binding col 21: `verifier_nonce` — the verifier's challenge; a PUBLIC input (`PI_NONCE`).
pub const VERIFIER_NONCE: usize = 21;
/// First of the 7 witnessed Poseidon2 chip output lanes 1..7 of the tag.
pub const TAG_LANE_BASE: usize = 22;
/// Total base-trace width: 19 summary + `final_root` + `randomness` + `verifier_nonce` + 7 lanes.
pub const BOUND_PRES_WIDTH: usize = TAG_LANE_BASE + (CHIP_OUT_LANES - 1); // 29

/// PI slot for the `verifier_nonce` challenge (after the 19 summary PIs).
pub const PI_NONCE: usize = 19;
/// Public-input count: the 19 summary slots + the verifier-nonce challenge.
pub const BOUND_PRES_PI_COUNT: usize = 20;

/// **The presentation-tag domain-separation constant** — `BLAKE3("dregg-presentation-tag-v1")`'s
/// first 4 bytes read little-endian mod the BabyBear prime (`binding.rs:311`, `PRESENTATION_TAG_DSK`;
/// `BoundPresentationEmit.lean` `PRESENTATION_TAG_DSK`). Folded into the tag preimage as a NAMED
/// CARRIER `.const` — the irreducible off-circuit BLAKE3 floor, byte-pinned identically in the
/// descriptor golden and this witness (so the chip lookup is served).
pub const PRESENTATION_TAG_DSK: u32 = 1_066_441_253;

/// The emitted descriptor's dispatch key (`descriptor_by_name`).
pub const BOUND_PRESENTATION_NAME: &str = "dregg-bound-presentation::v1";

/// The arity-4 chip absorb of the tag preimage `[final_root, randomness, verifier_nonce, DSK]` — the
/// hash the descriptor's `TID_P2` lookup enforces. Returns all 8 lanes (lane 0 = the narrow tag,
/// lanes 1..7 = the witnessed `TAG_LANES`). Built EXACTLY as the descriptor's `chipLookupTuple`
/// (arity tag 4, the 4-input preimage, out0 = the tag, then the 7 lanes).
fn tag_chip_lanes(
    final_root: BabyBear,
    randomness: BabyBear,
    verifier_nonce: BabyBear,
) -> [BabyBear; CHIP_OUT_LANES] {
    chip_absorb_all_lanes(
        4,
        &[
            final_root,
            randomness,
            verifier_nonce,
            BabyBear::new(PRESENTATION_TAG_DSK),
        ],
    )
}

/// The narrow presentation tag the descriptor binds `PRESENTATION_TAG` to: the arity-4 chip absorb
/// out0 of `[final_root, randomness, verifier_nonce, DSK]` (= `tag_chip_lanes(..)[0]`). This is the
/// in-circuit hash the `TID_P2` lookup computes — the value a light client / the fold re-verifies.
pub fn bound_presentation_tag(
    final_root: BabyBear,
    randomness: BabyBear,
    verifier_nonce: BabyBear,
) -> BabyBear {
    tag_chip_lanes(final_root, randomness, verifier_nonce)[0]
}

/// Build the **bound-presentation** base trace + public inputs `[summary(19) ‖ verifier_nonce]` for
/// the emitted `dregg-bound-presentation::v1` descriptor.
///
/// The summary columns copy the caller's public fields; `presentation_tag` (col 10) is computed as
/// the genuine arity-4 Poseidon2 chip absorb out0 of `[final_root, randomness, verifier_nonce, DSK]`
/// and cols 22..28 are its 7 witnessed permutation lanes, so the descriptor's `TID_P2` tag lookup is
/// SERVED. `final_root` and `randomness` ride as HIDDEN witness columns (19, 20); `verifier_nonce`
/// (col 21) is PI-bound. The trace is `height` identical rows; `height` must be a power of two ≥ 2
/// (the per-row PiBindings + the row-uniform chip lookup hold identically on every row).
///
/// The 20 public inputs are `[summary(0..18)] ++ [verifier_nonce]` — the tag preimage
/// (`final_root`, `randomness`) is DELIBERATELY absent (unlinkability): the descriptor proves the
/// public tag is a genuine Poseidon2 image of a hidden preimage bound to the public nonce.
#[allow(clippy::too_many_arguments)]
pub fn bound_presentation_witness(
    federation_root: BabyBear,
    action_binding: [BabyBear; 8],
    timestamp: BabyBear,
    revealed_facts: [BabyBear; 8],
    final_root: BabyBear,
    randomness: BabyBear,
    verifier_nonce: BabyBear,
    height: usize,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    if height < 2 || !height.is_power_of_two() {
        return Err(format!(
            "bound-presentation trace height {height} must be a power of two ≥ 2 (the trace-height requirement)"
        ));
    }

    let lanes = tag_chip_lanes(final_root, randomness, verifier_nonce);
    let presentation_tag = lanes[0];

    let mut row = vec![BabyBear::ZERO; BOUND_PRES_WIDTH];
    row[FEDERATION_ROOT] = federation_root;
    row[REQUEST_PREDICATE_BASE..REQUEST_PREDICATE_BASE + 8].copy_from_slice(&action_binding);
    row[TIMESTAMP] = timestamp;
    row[PRESENTATION_TAG] = presentation_tag;
    row[REVEALED_FACTS_BASE..REVEALED_FACTS_BASE + 8].copy_from_slice(&revealed_facts);
    row[FINAL_ROOT] = final_root;
    row[RANDOMNESS] = randomness;
    row[VERIFIER_NONCE] = verifier_nonce;
    for j in 0..(CHIP_OUT_LANES - 1) {
        row[TAG_LANE_BASE + j] = lanes[j + 1];
    }

    let trace: Vec<Vec<BabyBear>> = (0..height).map(|_| row.clone()).collect();

    // PIs: the 19 summary felts (cols 0..18) ++ the verifier nonce.
    let mut pis = row[..SUMMARY_WIDTH].to_vec();
    pis.push(verifier_nonce);
    debug_assert_eq!(pis.len(), BOUND_PRES_PI_COUNT);

    Ok((trace, pis))
}

/// [`bound_presentation_witness`] at the canonical power-of-two height 4 (the height the emit-gate
/// and sibling goldens use).
#[allow(clippy::too_many_arguments)]
pub fn bound_presentation_witness_h4(
    federation_root: BabyBear,
    action_binding: [BabyBear; 8],
    timestamp: BabyBear,
    revealed_facts: [BabyBear; 8],
    final_root: BabyBear,
    randomness: BabyBear,
    verifier_nonce: BabyBear,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    bound_presentation_witness(
        federation_root,
        action_binding,
        timestamp,
        revealed_facts,
        final_root,
        randomness,
        verifier_nonce,
        4,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_by_name::descriptor_by_name;
    use crate::descriptor_ir2::{
        EffectVmDescriptor2, LookupSpec, MemBoundaryWitness, TID_P2, VmConstraint2,
        parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
    };
    use crate::lean_descriptor_air::LeanExpr;
    use std::panic::AssertUnwindSafe;

    /// The byte-pinned golden (same file `descriptor_by_name` serves; identical to the Lean
    /// `emitVmJson2 boundPresentationDesc` `#guard`).
    const GOLDEN_JSON: &str = include_str!("../descriptors/by-name/bound-presentation.json");

    /// `true` iff `(trace, pis)` is REJECTED end-to-end (prove refuses OR the produced proof fails to
    /// verify). Prove-THEN-verify is the faithful consumer-posture gate.
    fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
        let r = std::panic::catch_unwind(AssertUnwindSafe(|| {
            let proof =
                prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
            verify_vm_descriptor2(desc, &proof, pis)
        }));
        matches!(r, Err(_) | Ok(Err(_)))
    }

    /// A distinct-felt honest presentation (arbitrary public fields + a hidden preimage).
    fn sample() -> (
        BabyBear,
        [BabyBear; 8],
        BabyBear,
        [BabyBear; 8],
        BabyBear,
        BabyBear,
        BabyBear,
    ) {
        let action: [BabyBear; 8] = std::array::from_fn(|k| BabyBear::new(200 + k as u32));
        let revealed: [BabyBear; 8] = std::array::from_fn(|k| BabyBear::new(500 + k as u32));
        (
            BabyBear::new(111),      // federation_root
            action,                  // action_binding
            BabyBear::new(300),      // timestamp
            revealed,                // revealed_facts
            BabyBear::new(0xF1A1),   // final_root (hidden)
            BabyBear::new(0xB11D),   // randomness (hidden)
            BabyBear::new(0xC0FFEE), // verifier_nonce (public)
        )
    }

    fn honest() -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
        let (fr, act, ts, rev, root, rnd, nonce) = sample();
        bound_presentation_witness_h4(fr, act, ts, rev, root, rnd, nonce).expect("witness builds")
    }

    /// STEP 0 — the dispatched descriptor is exactly the byte-pinned golden (the migration wiring).
    #[test]
    fn dispatch_serves_the_byte_pinned_golden() {
        let via = descriptor_by_name(BOUND_PRESENTATION_NAME)
            .expect("bound-presentation descriptor dispatches");
        assert_eq!(via.name, BOUND_PRESENTATION_NAME);
        assert_eq!(via.trace_width, BOUND_PRES_WIDTH);
        assert_eq!(via.public_input_count, BOUND_PRES_PI_COUNT);
        let golden = parse_vm_descriptor2(GOLDEN_JSON).expect("golden decodes");
        assert_eq!(
            via, golden,
            "descriptor_by_name must serve the byte-pinned emitted golden verbatim"
        );
        // exactly one arity-4 chip lookup (the internalized tag-binding tooth).
        let chip: Vec<&LookupSpec> = via
            .constraints
            .iter()
            .filter_map(|c| match c {
                VmConstraint2::Lookup(l) if l.table == TID_P2 => Some(l),
                _ => None,
            })
            .collect();
        assert_eq!(chip.len(), 1, "the single tag-binding chip lookup");
        assert_eq!(chip[0].tuple[0], LeanExpr::Const(4), "arity-4 tag");
    }

    /// STEP 1 — THE POSITIVE POLE: an honest bound presentation proves through the DISPATCHED
    /// descriptor and re-verifies. The witness comes from the production builder; the public tag is
    /// the genuine Poseidon2 image of the hidden preimage.
    #[test]
    fn honest_bound_presentation_proves_and_verifies_via_dispatch() {
        let desc = descriptor_by_name(BOUND_PRESENTATION_NAME).expect("dispatch");
        let (fr, act, ts, rev, root, rnd, nonce) = sample();
        let (trace, pis) =
            bound_presentation_witness_h4(fr, act, ts, rev, root, rnd, nonce).expect("witness");

        assert_eq!(pis.len(), BOUND_PRES_PI_COUNT);
        assert_eq!(
            &pis[..SUMMARY_WIDTH],
            &trace[0][..SUMMARY_WIDTH],
            "summary PIs copy the row"
        );
        assert_eq!(pis[PI_NONCE], nonce, "the verifier-nonce PI");
        // The public tag equals the genuine chip image (the internalized hash tooth).
        assert_eq!(
            pis[PRESENTATION_TAG],
            bound_presentation_tag(root, rnd, nonce),
            "the public tag is the Poseidon2 image of [final_root, randomness, nonce, DSK]"
        );
        // The preimage is NOT public (unlinkability): only the summary + nonce are PIs.
        assert!(
            !pis.contains(&root) || root == fr,
            "final_root is a hidden witness, not a PI"
        );

        let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
            .expect("the honest bound-presentation witness must prove through the dispatched descriptor");
        verify_vm_descriptor2(&desc, &proof, &pis).expect("the honest proof must re-verify");
    }

    /// STEP 2 — WRONG-TAG FORGE (the internalized chip tooth): an attacker publishes a tag that is
    /// NOT the Poseidon2 image of the preimage. Keep the honest preimage/lanes but overwrite the tag
    /// column AND its PI copy with a bogus value → the summary PI copy still holds, but the chip
    /// lookup `[4, preimage.., bogus_tag, genuine_lanes]` has no serving chip row → UNSAT. Non-vacuous:
    /// the honest witness is accepted first.
    #[test]
    fn wrong_tag_forge_refuses() {
        let desc = descriptor_by_name(BOUND_PRESENTATION_NAME).expect("dispatch");
        let (trace, pis) = honest();
        assert!(
            !rejects(&desc, &trace, &pis),
            "non-vacuity: honest accepted"
        );

        let mut bad_trace = trace.clone();
        let mut bad_pis = pis.clone();
        let bogus = trace[0][PRESENTATION_TAG] + BabyBear::ONE;
        for r in bad_trace.iter_mut() {
            r[PRESENTATION_TAG] = bogus; // out0 no longer equals the chip digest of the preimage
        }
        bad_pis[PRESENTATION_TAG] = bogus; // keep the summary PI copy satisfiable
        assert!(
            rejects(&desc, &bad_trace, &bad_pis),
            "a tag that is not the Poseidon2 image of its preimage must be REJECTED (chip lookup)"
        );
    }

    /// STEP 3 — WRONG-PREIMAGE FORGE (the chip tooth, from the other side): keep the honest PUBLIC
    /// tag, but tamper the hidden `final_root` witness column. The chip now absorbs a DIFFERENT
    /// preimage → its digest ≠ the claimed tag → the lookup is UNSAT (an attacker cannot swap the
    /// hidden preimage under a fixed public tag). Non-vacuous: honest accepted first.
    #[test]
    fn wrong_preimage_forge_refuses() {
        let desc = descriptor_by_name(BOUND_PRESENTATION_NAME).expect("dispatch");
        let (trace, pis) = honest();
        assert!(
            !rejects(&desc, &trace, &pis),
            "non-vacuity: honest accepted"
        );

        let mut bad_trace = trace.clone();
        for r in bad_trace.iter_mut() {
            r[FINAL_ROOT] += BabyBear::ONE; // a different preimage; tag/lanes stay the honest ones
        }
        assert!(
            rejects(&desc, &bad_trace, &pis),
            "a tampered hidden preimage under a fixed public tag must be REJECTED (chip lookup)"
        );
    }

    /// STEP 4 — WRONG-ACTION FORGE (the summary tooth): honest trace, a mutated public
    /// `action_binding[0]` PI no longer equals the first-row column → the summary copy is UNSAT (an
    /// attacker cannot re-bind the presentation to a different requested action). Non-vacuous.
    #[test]
    fn wrong_action_forge_refuses() {
        let desc = descriptor_by_name(BOUND_PRESENTATION_NAME).expect("dispatch");
        let (trace, pis) = honest();
        assert!(
            !rejects(&desc, &trace, &pis),
            "non-vacuity: honest accepted"
        );

        let mut forged = pis.clone();
        forged[REQUEST_PREDICATE_BASE] += BabyBear::ONE; // action_binding[0] no longer equals row
        assert!(
            rejects(&desc, &trace, &forged),
            "a forged action_binding PI must be REJECTED (summary copy)"
        );
    }

    /// STEP 5 — FORGED VERIFIER-NONCE PI: honest trace, a mutated public `verifier_nonce` no longer
    /// equals the first-row column → the nonce PI pin is UNSAT (an attacker cannot replay a tag bound
    /// to one challenge against a different challenge). Non-vacuous.
    #[test]
    fn forged_nonce_pi_refuses() {
        let desc = descriptor_by_name(BOUND_PRESENTATION_NAME).expect("dispatch");
        let (trace, pis) = honest();
        assert!(
            !rejects(&desc, &trace, &pis),
            "non-vacuity: honest accepted"
        );

        let mut forged = pis.clone();
        forged[PI_NONCE] += BabyBear::ONE;
        assert!(
            rejects(&desc, &trace, &forged),
            "a forged verifier_nonce PI must be REJECTED (nonce pin)"
        );
    }

    /// STEP 6 — malformed witnesses (non-power-of-two height) are refused at build time.
    #[test]
    fn malformed_witness_refuses() {
        let (fr, act, ts, rev, root, rnd, nonce) = sample();
        assert!(
            bound_presentation_witness(fr, act, ts, rev, root, rnd, nonce, 3).is_err(),
            "a non-power-of-two height must be refused"
        );
        assert!(
            bound_presentation_witness(fr, act, ts, rev, root, rnd, nonce, 1).is_err(),
            "height 1 must be refused"
        );
    }
}
