//! Rust witness builder for the emitted **presentation** descriptor
//! (`dregg-presentation-freshness::summary-v1`, authored in
//! `metatheory/Dregg2/Circuit/Emit/PresentationEmit.lean` as `presentationFreshnessDesc`).
//!
//! ## What this closes (the Gate-1.5 pattern for the blinded-presentation family)
//!
//! The StarkProof→descriptor-prover migration flips the anonymous-presentation verifiers (the
//! `bridge` issuer path; `sdk::verify_anonymous_presentation` is the SDK's face on it and, measured
//! 2026-08-06, has ZERO call sites — so read it as an available surface, not as a live consumer)
//! from the hand `PresentationAir` STARK onto the p3 descriptor prover. The emitted descriptor for
//! this family is
//! [`crate::descriptor_by_name::descriptor_by_name`]`("dregg-presentation-freshness::summary-v1")`:
//! the 19-column summary copy (`PresentationAir::constraints`) PLUS the one off-AIR check that is a
//! self-contained arithmetic tooth — the FRESHNESS binding (`verify_freshness_binding`).
//! (The `presentation.rs:807` / `presentation.rs:316` line cites that used to sit here had both
//! drifted — the real homes are `:651` and `:385` — which is why they are gone: a line number is a
//! claim that rots, a symbol name is not.) Until now the only Rust producer of a
//! descriptor-matching trace for it lived inside `circuit-prove/tests/presentation_emit_gate.rs`;
//! there was NO production witness builder (the analog of [`crate::membership_descriptor_4ary::membership_witness_4ary`])
//! that consumers of `descriptor_by_name` could call. This module is that builder.
//!
//! ## Note on "blinded" (the hint's blinded-Merkle ring membership)
//!
//! The blinded issuer Merkle membership itself (`blinded_merkle_poseidon2_circuit`,
//! `BLINDED_MERKLE_AIR_NAME`) is NOT internalized into an IR-v2 descriptor — per the
//! `FITS_WITH_NAMED_GATE` verdict it rides as a NAMED STARK leaf that the executor verifies
//! (`PresentationEmit.lean` §"The NAMED gates"). So the family's emitted, byte-pinned descriptor is
//! the summary+freshness one built here; there is no separate `dregg-blinded-merkle::*`
//! `EffectVmDescriptor2` to witness (that would be a distinct future emit, not a present descriptor).
//!
//! ## The trace layout (a single logical row, repeated to a power-of-two height)
//!
//! | col     | name                       | meaning                                                       |
//! |---------|----------------------------|--------------------------------------------------------------|
//! | 0       | federation_root            | PI 0 (summary copy)                                          |
//! | 1..8    | request_predicate          | PI 1..8 (`ACTION_BINDING_WIDTH = 8`)                        |
//! | 9       | timestamp                  | PI 9                                                         |
//! | 10      | presentation_tag           | PI 10 (its hash well-formedness is a named STARK leaf)      |
//! | 11..18  | revealed_facts_commitment  | PI 11..18 (`WideHash::WIDTH = 8`)                           |
//! | 19      | verifier_block_height      | PI 19 (the public freshness anchor)                         |
//! | 20      | not_after_height           | published by the named derivation leaf (bound to diff)      |
//! | 21      | diff = not_after − verifier | range-proved into `[0, 2^30)`                              |
//! | 22      | hi = p/2 − diff            | range-proved into `[0, 2^30)` (closes the exact `p/2` bound) |
//!
//! The two freshness gates (`diff = not_after − verifier`, `diff + hi = p/2`) are filled to hold by
//! construction; the descriptor's TWO `Range{30}` lookups on `diff` and `hi` are the JUDGE. This
//! builder is mechanical — it does NOT pre-judge freshness. An EXPIRED token (`not_after < verifier`)
//! yields `diff = p − (verifier − not_after)`, out of `[0, 2^30)` → the `diff` range is UNSAT; a
//! `diff > p/2` (yet `< 2^30`) forces `hi = p/2 − diff` to wrap to `p − …` → the `hi` range is UNSAT
//! (the EXACT non-power-of-two `p/2` bound). This reproduces `verify_freshness_binding`'s deployed
//! acceptance region `diff ∈ [0, 1_006_632_960]` exactly (asserted against the deployed constant in
//! the tests).

use crate::field::BabyBear;

// ---- Column layout (mirror `PresentationEmit.lean` §1 / `presentation.rs::SUMMARY_WIDTH`). ----
/// Summary col 0: `federation_root`.
pub const FEDERATION_ROOT: usize = 0;
/// Summary cols 1..=8: `request_predicate` (`ACTION_BINDING_WIDTH = 8`).
pub const REQUEST_PREDICATE_BASE: usize = 1;
/// Summary col 9: `timestamp`.
pub const TIMESTAMP: usize = 9;
/// Summary col 10: `presentation_tag`.
pub const PRESENTATION_TAG: usize = 10;
/// Summary cols 11..=18: `revealed_facts_commitment` (`WideHash::WIDTH = 8`).
pub const REVEALED_FACTS_BASE: usize = 11;
/// The deployed summary width (`presentation.rs::SUMMARY_WIDTH = 1 + 8 + 1 + 1 + 8`).
pub const SUMMARY_WIDTH: usize = 19;

/// Freshness col 19: `verifier_block_height` (the public anchor; PI-bound).
pub const VERIFIER: usize = 19;
/// Freshness col 20: `not_after_height` (published by the named derivation leaf).
pub const NOT_AFTER: usize = 20;
/// Freshness col 21: `diff = not_after − verifier`; range-proved into `[0, 2^30)`.
pub const DIFF: usize = 21;
/// Freshness col 22: `hi = p/2 − diff`; range-proved into `[0, 2^30)` (closes the exact bound).
pub const HI: usize = 22;
/// Total base-trace width (23 = 19 summary + 4 freshness; the prover appends range limbs).
pub const PRES_WIDTH: usize = 23;

/// PI slot for the `verifier_block_height` anchor (after the 19 summary PIs).
pub const PI_VERIFIER: usize = 19;
/// Public-input count: the 19 summary slots + the verifier-height anchor.
pub const PRES_PI_COUNT: usize = 20;

/// The freshness acceptance bound `p/2 = 1_006_632_960` (`p = 2013265921`,
/// `verify_freshness_binding`, `presentation.rs:340`). A `diff` in `[0, p/2]` is fresh; anything
/// above is expired.
pub const HALF_P: u32 = 1_006_632_960;

/// The emitted descriptor's dispatch key (`descriptor_by_name`).
pub const PRESENTATION_FRESHNESS_NAME: &str = "dregg-presentation-freshness::summary-v1";

/// Pack the 19 summary felts in the deployed layout order
/// (`federation_root ‖ request_predicate[8] ‖ timestamp ‖ presentation_tag ‖ revealed_facts[8]`),
/// exactly `PresentationPublicInputs` → summary order (`presentation.rs:494`).
pub fn summary_from_fields(
    federation_root: BabyBear,
    request_predicate: &[BabyBear; 8],
    timestamp: BabyBear,
    presentation_tag: BabyBear,
    revealed_facts_commitment: &[BabyBear; 8],
) -> [BabyBear; SUMMARY_WIDTH] {
    let mut s = [BabyBear::ZERO; SUMMARY_WIDTH];
    s[FEDERATION_ROOT] = federation_root;
    s[REQUEST_PREDICATE_BASE..REQUEST_PREDICATE_BASE + 8].copy_from_slice(request_predicate);
    s[TIMESTAMP] = timestamp;
    s[PRESENTATION_TAG] = presentation_tag;
    s[REVEALED_FACTS_BASE..REVEALED_FACTS_BASE + 8].copy_from_slice(revealed_facts_commitment);
    s
}

/// Build the **presentation** base trace + public inputs `[summary(19) ‖ verifier_block_height]` for
/// the emitted `dregg-presentation-freshness::summary-v1` descriptor.
///
/// `summary` is the 19-felt summary in the deployed layout order (see [`summary_from_fields`]).
/// `verifier_block_height` is the verifier's public freshness anchor; `not_after_height` is the
/// token-expiry height published by the named derivation leaf. The `diff`/`hi` freshness columns are
/// filled so the two gates hold by construction; the descriptor's two `Range{30}` lookups are the
/// judge (a `not_after < verifier` or a `diff > p/2` yields a well-formed but UNSATISFYING trace that
/// `verify_vm_descriptor2` rejects). The trace is `height` identical rows; `height` must be a power of
/// two ≥ 2 (the descriptor's per-row gates + range lookups hold identically on every row, so the
/// summary/freshness security is row-uniform).
pub fn presentation_freshness_witness_h(
    summary: &[BabyBear],
    verifier_block_height: BabyBear,
    not_after_height: BabyBear,
    height: usize,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    if summary.len() != SUMMARY_WIDTH {
        return Err(format!(
            "presentation summary length {} must equal SUMMARY_WIDTH {SUMMARY_WIDTH}",
            summary.len()
        ));
    }
    if height < 2 || !height.is_power_of_two() {
        return Err(format!(
            "presentation trace height {height} must be a power of two ≥ 2 (the trace-height requirement)"
        ));
    }

    let diff = not_after_height - verifier_block_height;
    let hi = BabyBear::new(HALF_P) - diff;

    let mut row = vec![BabyBear::ZERO; PRES_WIDTH];
    row[..SUMMARY_WIDTH].copy_from_slice(summary);
    row[VERIFIER] = verifier_block_height;
    row[NOT_AFTER] = not_after_height;
    row[DIFF] = diff;
    row[HI] = hi;

    let trace: Vec<Vec<BabyBear>> = (0..height).map(|_| row.clone()).collect();

    let mut pis = summary.to_vec();
    pis.push(verifier_block_height);
    debug_assert_eq!(pis.len(), PRES_PI_COUNT);
    Ok((trace, pis))
}

/// [`presentation_freshness_witness_h`] at the canonical power-of-two height 4 (the height the
/// emit-gate and membership goldens use).
pub fn presentation_freshness_witness(
    summary: &[BabyBear],
    verifier_block_height: BabyBear,
    not_after_height: BabyBear,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    presentation_freshness_witness_h(summary, verifier_block_height, not_after_height, 4)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_by_name::descriptor_by_name;
    use crate::descriptor_ir2::{
        EffectVmDescriptor2, MemBoundaryWitness, TID_RANGE, VmConstraint2, parse_vm_descriptor2,
        prove_vm_descriptor2, verify_vm_descriptor2,
    };
    use crate::refusal::{Outcome, classify};
    use std::panic::AssertUnwindSafe;

    /// The byte-pinned golden (same file `descriptor_by_name` serves; identical to the Lean
    /// `emitVmJson2 presentationFreshnessDesc` `#guard`).
    const GOLDEN_JSON: &str = include_str!("../descriptors/by-name/presentation-freshness.json");

    /// `true` iff `(trace, pis)` is REJECTED end-to-end (prove refuses OR the produced proof fails to
    /// verify). Prove-THEN-verify is the faithful consumer-posture gate.
    fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
        match classify("rejects", || {
            let proof =
                prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
            verify_vm_descriptor2(desc, &proof, pis)
        }) {
            // The p3 debug prover's DOCUMENTED unsat verdict — a real refusal.
            // `classify` REDs on any other panic (a stray unwrap, a trace-assembly
            // debug_assert), which used to land here and read as "rejected".
            Outcome::UnsatPanic(_) => true,
            Outcome::Err(_) => true,
            Outcome::Accepted(_) => false,
        }
    }

    /// A distinct-felt honest summary (arbitrary values).
    fn sample_summary() -> [BabyBear; SUMMARY_WIDTH] {
        let req: [BabyBear; 8] = std::array::from_fn(|k| BabyBear::new(200 + k as u32));
        let rev: [BabyBear; 8] = std::array::from_fn(|k| BabyBear::new(500 + k as u32));
        summary_from_fields(
            BabyBear::new(111),
            &req,
            BabyBear::new(300),
            BabyBear::new(400),
            &rev,
        )
    }

    /// STEP 0 — the dispatched descriptor is exactly the byte-pinned golden (the migration wiring).
    #[test]
    fn dispatch_serves_the_byte_pinned_golden() {
        let via = descriptor_by_name(PRESENTATION_FRESHNESS_NAME)
            .expect("presentation-freshness descriptor dispatches");
        assert_eq!(via.name, PRESENTATION_FRESHNESS_NAME);
        assert_eq!(via.trace_width, PRES_WIDTH);
        assert_eq!(via.public_input_count, PRES_PI_COUNT);
        let golden = parse_vm_descriptor2(GOLDEN_JSON).expect("golden decodes");
        assert_eq!(
            via, golden,
            "descriptor_by_name must serve the byte-pinned emitted golden verbatim"
        );
        // two range lookups (the diff + hi p/2 gadget).
        let ranges = via
            .constraints
            .iter()
            .filter(|c| matches!(c, VmConstraint2::Lookup(l) if l.table == TID_RANGE))
            .count();
        assert_eq!(ranges, 2, "the diff + hi range lookups");
    }

    /// STEP 1 — THE POSITIVE POLE: an honest fresh token (`diff = 500 ∈ [0, p/2]`) proves through the
    /// DISPATCHED descriptor and re-verifies. The witness comes from the production builder.
    #[test]
    fn honest_fresh_token_proves_and_verifies_via_dispatch() {
        let desc = descriptor_by_name(PRESENTATION_FRESHNESS_NAME).expect("dispatch");
        let summary = sample_summary();
        let (trace, pis) =
            presentation_freshness_witness(&summary, BabyBear::new(1000), BabyBear::new(1500))
                .expect("witness builds");
        assert_eq!(pis.len(), PRES_PI_COUNT);
        assert_eq!(
            &pis[..SUMMARY_WIDTH],
            &summary[..],
            "summary PIs copy the summary"
        );
        assert_eq!(
            pis[PI_VERIFIER],
            BabyBear::new(1000),
            "the verifier anchor PI"
        );

        let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
            .expect("the honest fresh-token witness must prove through the dispatched descriptor");
        verify_vm_descriptor2(&desc, &proof, &pis).expect("the honest proof must re-verify");
    }

    /// STEP 2 — DEPLOYED-BOUND REPRODUCTION (the load-bearing semantic equality, the byte-match
    /// analog for a family with no Merkle root): the descriptor's accept region is EXACTLY
    /// `verify_freshness_binding`'s (`presentation.rs:340`, `diff > 1_006_632_960 ⇒ TokenExpired`).
    /// At the exact bound `diff = p/2` the token is FRESH (accepted); at `diff = p/2 + 1` it is
    /// EXPIRED (rejected via the `hi` range — the exact non-power-of-two tooth). Non-vacuous: the
    /// boundary point ACCEPTS.
    #[test]
    fn reproduces_deployed_freshness_bound_at_p_over_2() {
        let desc = descriptor_by_name(PRESENTATION_FRESHNESS_NAME).expect("dispatch");
        let summary = sample_summary();

        // diff = p/2 exactly: verifier = 1, not_after = 1 + p/2. Deployed: diff_val == p/2, NOT
        // > p/2 ⇒ Valid.
        let verifier = 1u32;
        let not_after_ok = verifier + HALF_P; // diff = p/2
        let (t_ok, p_ok) = presentation_freshness_witness(
            &summary,
            BabyBear::new(verifier),
            BabyBear::new(not_after_ok),
        )
        .expect("witness");
        // sanity: the diff/hi this builds are the deployed diff and its p/2-complement.
        assert_eq!(
            t_ok[0][DIFF],
            BabyBear::new(HALF_P),
            "diff == p/2 at the bound"
        );
        assert_eq!(t_ok[0][HI], BabyBear::ZERO, "hi == p/2 − p/2 == 0");
        assert!(
            !rejects(&desc, &t_ok, &p_ok),
            "diff == p/2 is FRESH (the deployed inclusive bound) — must be ACCEPTED"
        );

        // diff = p/2 + 1: verifier = 1, not_after = 2 + p/2. Deployed: diff_val > p/2 ⇒ TokenExpired.
        let not_after_bad = verifier + HALF_P + 1; // diff = p/2 + 1
        let (t_bad, p_bad) = presentation_freshness_witness(
            &summary,
            BabyBear::new(verifier),
            BabyBear::new(not_after_bad),
        )
        .expect("witness");
        // sanity: diff is itself IN 30-bit range, so the bite is the hi range (the exact p/2 tooth).
        assert!(
            (t_bad[0][DIFF].as_u32() as u64) < (1u64 << 30),
            "diff = p/2 + 1 is itself in [0, 2^30) — the reject is the hi tooth, not diff"
        );
        assert!(
            t_bad[0][DIFF].as_u32() > HALF_P,
            "diff strictly above p/2 (expired)"
        );
        assert!(
            rejects(&desc, &t_bad, &p_bad),
            "diff == p/2 + 1 is EXPIRED (the deployed exclusive-above bound) — must be REJECTED"
        );
    }

    /// STEP 3 — EXPIRED TOKEN (diff-range tooth): `not_after < verifier` wraps `diff` to `p − …`, out
    /// of `[0, 2^30)`. Non-vacuous: the honest fresh token is asserted accepted first.
    #[test]
    fn expired_token_refuses() {
        let desc = descriptor_by_name(PRESENTATION_FRESHNESS_NAME).expect("dispatch");
        let summary = sample_summary();
        let (t_ok, p_ok) =
            presentation_freshness_witness(&summary, BabyBear::new(1000), BabyBear::new(1500))
                .expect("witness");
        assert!(
            !rejects(&desc, &t_ok, &p_ok),
            "honest fresh token accepted — else the canary is vacuous"
        );
        // verifier 1500 > not_after 1000 ⇒ diff wraps out of range.
        let (t_bad, p_bad) =
            presentation_freshness_witness(&summary, BabyBear::new(1500), BabyBear::new(1000))
                .expect("witness");
        assert!(
            rejects(&desc, &t_bad, &p_bad),
            "an expired token (not_after < verifier) must be REJECTED (diff range)"
        );
    }

    /// STEP 4 — FORGED SUMMARY PI (the literal deployed hand-AIR tooth): honest trace, a mutated
    /// public `federation_root` no longer equals the first-row column → a summary copy is UNSAT.
    #[test]
    fn forged_summary_pi_refuses() {
        let desc = descriptor_by_name(PRESENTATION_FRESHNESS_NAME).expect("dispatch");
        let summary = sample_summary();
        let (trace, pis) =
            presentation_freshness_witness(&summary, BabyBear::new(1000), BabyBear::new(1500))
                .expect("witness");
        assert!(
            !rejects(&desc, &trace, &pis),
            "non-vacuity: honest accepted"
        );
        let mut forged = pis.clone();
        forged[FEDERATION_ROOT] += BabyBear::ONE; // 111 → 112, no longer equals row[0]
        assert!(
            rejects(&desc, &trace, &forged),
            "a forged summary PI (federation_root) must be REJECTED (summary copy)"
        );
    }

    /// STEP 5 — FORGED VERIFIER-HEIGHT PI (the freshness public anchor): honest trace, a mutated
    /// public `verifier_block_height` no longer equals the first-row `VERIFIER` column → the anchor
    /// PI binding is UNSAT (an attacker cannot claim a different verifier height than the witness).
    #[test]
    fn forged_verifier_height_pi_refuses() {
        let desc = descriptor_by_name(PRESENTATION_FRESHNESS_NAME).expect("dispatch");
        let summary = sample_summary();
        let (trace, pis) =
            presentation_freshness_witness(&summary, BabyBear::new(1000), BabyBear::new(1500))
                .expect("witness");
        assert!(
            !rejects(&desc, &trace, &pis),
            "non-vacuity: honest accepted"
        );
        let mut forged = pis.clone();
        forged[PI_VERIFIER] += BabyBear::ONE; // 1000 → 1001, no longer equals row[VERIFIER]
        assert!(
            rejects(&desc, &trace, &forged),
            "a forged verifier_block_height PI must be REJECTED (freshness anchor)"
        );
    }

    /// AUDIT — DIRECTLY-TAMPERED TRACE (not a PI, not an input): an attacker who fabricates the raw
    /// trace sets `hi := 0` on every row while keeping the honest `diff` (still 30-bit-in-range), so
    /// gate2 (`diff + hi = p/2`) is VIOLATED even though both range lookups still pass. The REAL
    /// `verify_vm_descriptor2` must reject on the broken gate. Non-vacuous: honest trace accepted
    /// first. This exercises the gate2 arithmetic tooth independently of the diff/hi range teeth.
    #[test]
    fn tampered_hi_trace_column_refuses() {
        let desc = descriptor_by_name(PRESENTATION_FRESHNESS_NAME).expect("dispatch");
        let summary = sample_summary();
        let (trace, pis) =
            presentation_freshness_witness(&summary, BabyBear::new(1000), BabyBear::new(1500))
                .expect("witness");
        assert!(
            !rejects(&desc, &trace, &pis),
            "non-vacuity: honest accepted"
        );
        // Forge hi := 0 on every row (0 is trivially in [0,2^30), so the hi RANGE still passes) while
        // diff stays 500 → gate2 becomes 500 + 0 − p/2 ≠ 0.
        let mut tampered = trace.clone();
        for r in tampered.iter_mut() {
            r[HI] = BabyBear::ZERO;
        }
        assert_ne!(
            trace[0][HI],
            BabyBear::ZERO,
            "the honest hi is nonzero here"
        );
        assert!(
            rejects(&desc, &tampered, &pis),
            "a tampered hi trace column (gate2 violated, hi still in range) must be REJECTED"
        );
    }

    /// STEP 6 — malformed witnesses (wrong summary length, non-power-of-two height) are refused at
    /// build time.
    #[test]
    fn malformed_witness_refuses() {
        let short = vec![BabyBear::ZERO; SUMMARY_WIDTH - 1];
        assert!(
            presentation_freshness_witness(&short, BabyBear::ZERO, BabyBear::ZERO).is_err(),
            "a wrong-length summary must be refused"
        );
        let summary = sample_summary();
        assert!(
            presentation_freshness_witness_h(&summary, BabyBear::new(1), BabyBear::new(2), 3)
                .is_err(),
            "a non-power-of-two height must be refused"
        );
    }
}
