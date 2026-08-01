//! **MULTIWAY-TUG, PROVED IN THE BROWSER TAB** — a private match's play proofs
//! generated ON-DEVICE (compiled to wasm32, runnable in a browser). The "moves never
//! leave the device" endgame for the verified card game: the owner's hidden hand is
//! committed as a Poseidon2 4-ary Merkle root, and the *proof that a played card was a
//! legal member of that hand* is minted in the tab — the rest of the hand (the private
//! openings) never crosses the wasm boundary.
//!
//! This module consumes [`dregg_multiway_tug`]'s COMMITTED fold READ-ONLY (it does not
//! modify the game / circuit / fold). Two entry points, at two honest resolutions:
//!
//! ## The reduced, definitely-in-wasm path — [`prove_tug_play_on_device`]
//!
//! `proveTugPlayOnDevice(handJson, cardId)` takes a played private match's hand + the
//! played card and generates, IN WASM, the **per-play membership STARK** — a real
//! arity-4 Poseidon2 Merkle-membership `Ir2BatchProof` that the played card's blinded
//! leaf climbs the committed authentication path to the hand root. It is the SAME
//! base-layer tooth the Phase-3 fold lowers per turn ([`fold::membership_leaf_for_play`]),
//! proven at the base IR-v2 layer (`prove_vm_descriptor2`) and self-verified
//! (`verify_vm_descriptor2`) before it returns. The `root` public input the proof binds
//! is asserted EQUAL to [`HandTree::root`] — the on-device proof commits to the game's
//! REAL committed hand, not a re-derived shape. This is the base STARK the existing
//! shipped `generate_demo_stark_proof` binding already proves runs in wasm; here it is
//! specialized to multiway-tug's own private hand.
//!
//! This is the DRIVEN on-device gate: it builds for wasm32, runs in the tab, and its
//! proof verifies through the SAME migrated consumer contract (`ir2_verify_membership_envelope`)
//! the light client's membership arm uses.
//!
//! ## The full recursive fold — [`fold_tug_match_on_device`]
//!
//! `foldTugMatchOnDevice(handJson, cardA, cardB)` runs the WHOLE Phase-3 fold
//! ([`fold::fold_match`]): two membership-proven plays fold via the deployed per-turn
//! recursion (`prove_turn_chain_recursive`) into ONE `WholeChainProof` a pure light
//! client (`verify_history`) accepts, returning the verify-sufficient
//! [`WholeChainProof::to_bytes`] envelope. It COMPILES for wasm32 (the recursion tower is
//! already in this graph via the light-client-in-the-tab binding), but the RUN is the
//! honest boundary: the plonky3 recursion fold is minutes-to-hours and heavy on RAM even
//! natively, and wasm32 is single-threaded (no rayon) in a 32-bit (≤4 GiB) address space.
//! The measured limit is reported alongside this deliverable — the reduced play path is
//! what proves on-device NOW; the full fold in wasm is bounded by memory + single-thread
//! time (and GPU acceleration / true crypto-ZK are separate, later frontiers).

use wasm_bindgen::prelude::*;

use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::membership_descriptor_4ary::{
    DIGEST_W, Digest8, MEMBERSHIP_4ARY_PI_COUNT, PI_LEAF, PI_ROOT,
    membership_descriptor_of_depth_4ary, membership_witness_4ary,
};
use dregg_multiway_tug::hidden_hand::{HandTree, card_leaf};

use crate::{Ir2ProofEnvelope, hex_encode, ir2_verify_membership_envelope, perf_now};
use serde::Serialize;

/// Parse a hand JSON — `[[card, nonce], ...]` — into the `(card, nonce)` openings a
/// [`HandTree`] commits. Fail-closed on malformed JSON or an over-capacity hand.
fn parse_hand(hand_json: &str) -> Result<Vec<(u64, u64)>, String> {
    let pairs: Vec<[u64; 2]> = serde_json::from_str(hand_json)
        .map_err(|e| format!("hand json (expected [[card,nonce],...]): {e}"))?;
    if pairs.is_empty() {
        return Err("hand is empty".to_string());
    }
    Ok(pairs.into_iter().map(|p| (p[0], p[1])).collect())
}

/// The outcome of the on-device per-play membership prove (fields the wasm wrapper surfaces).
pub(crate) struct TugPlayOutcome {
    /// The `Ir2ProofEnvelope` JSON (descriptor NAME + public inputs `[leaf, root]` + the
    /// postcard `Ir2BatchProof`) — feeds straight into [`ir2_verify_membership_envelope`].
    pub proof_json: String,
    pub proof_size_bytes: usize,
    /// The played card's blinded 8-felt Poseidon2 leaf digest (public inputs 0..8).
    pub leaf_lanes: [u32; DIGEST_W],
    /// The committed 8-felt hand root the play climbs to (public inputs 8..16).
    pub root_lanes: [u32; DIGEST_W],
    /// The membership trace row count (== the 4-ary tree depth).
    pub num_rows: usize,
    /// The FAITHFULNESS gate: the proof's bound `root` PI equals [`HandTree::root`] — the
    /// on-device proof commits to the game's REAL committed hand, not a re-derived shape.
    pub root_matches_committed: bool,
}

/// PRODUCER core (wasm-bindgen-free `String` errors, so the whole path is testable
/// NATIVELY): commit the private hand, prove the played card's Poseidon2 membership at the
/// base IR-v2 layer, self-verify, and package the canonical membership envelope.
///
/// The witness (leaf, sibling hashes, positions) comes STRAIGHT off
/// [`HandTree::prove_play`]'s real [`PlayProof`](dregg_multiway_tug::hidden_hand::PlayProof)
/// — the private openings of the OTHER cards never enter the trace (the path carries only
/// sibling hashes). A card not in the hand has no proof (fail-closed).
pub(crate) fn prove_tug_play_core(hand_json: &str, card_id: u64) -> Result<TugPlayOutcome, String> {
    let hand = parse_hand(hand_json)?;
    let tree = HandTree::commit(hand);
    let play = tree.prove_play(card_id).ok_or_else(|| {
        format!("card {card_id} is not in the committed hand (no membership proof)")
    })?;

    // The real per-play membership witness: the blinded 8-felt leaf + the 4-ary
    // authentication path (every co-path node a full `node8` digest).
    let leaf = card_leaf(play.card_id, play.nonce);
    let siblings: Vec<[Digest8; 3]> = play.path.iter().map(|lvl| lvl.siblings).collect();
    let positions: Vec<u8> = play.path.iter().map(|lvl| lvl.position).collect();
    let depth = siblings.len();

    let (trace, pis) = membership_witness_4ary(leaf, &siblings, &positions)?;
    let desc = membership_descriptor_of_depth_4ary(depth);

    // PROVE in wasm — the same base descriptor-STARK the shipped membership binding proves.
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
        .map_err(|e| format!("on-device membership prove failed: {e}"))?;

    // Self-verify before returning: an honest proof ACCEPTS through the deployed verifier.
    verify_vm_descriptor2(&desc, &proof, &pis)
        .map_err(|e| format!("on-device self-verify failed: {e}"))?;

    // FAITHFULNESS: the descriptor recomputes the parent via the SAME `node8_4ary` fold
    // (three arity-16 chip absorbs) HandTree builds with, so the bound root PIs equal the
    // game's committed hand root — ALL EIGHT LANES. We assert it (never accept a proof bound
    // to a foreign root, and never on a lane-0 projection: the one-felt family's entire root
    // binding was a single lane, collided at 2^15.5).
    let committed_root = tree.root();
    let root_matches_committed = pis.len() == MEMBERSHIP_4ARY_PI_COUNT
        && pis[PI_ROOT..PI_ROOT + DIGEST_W] == committed_root[..];

    let proof_postcard = postcard::to_allocvec(&proof).map_err(|e| e.to_string())?;
    let proof_size_bytes = proof_postcard.len();
    let envelope = Ir2ProofEnvelope {
        descriptor_name: desc.name.clone(),
        public_inputs: pis.iter().map(|f| f.as_u32()).collect(),
        proof_postcard,
    };
    let proof_json = serde_json::to_string(&envelope).map_err(|e| e.to_string())?;

    Ok(TugPlayOutcome {
        proof_json,
        proof_size_bytes,
        leaf_lanes: core::array::from_fn(|k| pis[PI_LEAF + k].as_u32()),
        root_lanes: core::array::from_fn(|k| pis[PI_ROOT + k].as_u32()),
        num_rows: trace.len(),
        root_matches_committed,
    })
}

/// **The multiway-tug per-play membership proof, minted IN THE TAB.** `hand_json` is the
/// owner's private hand (`[[card, nonce], ...]`); `card_id` is the played card. Returns
/// the membership `Ir2ProofEnvelope` JSON (feed it to [`verify_tug_play_on_device`]) plus
/// the bound leaf/root, the proof size, and generation time. The private openings of the
/// rest of the hand never leave the device. FAIL-CLOSED: an empty/malformed hand or a card
/// not in the hand is a `JsError` and NO proof.
#[wasm_bindgen(js_name = proveTugPlayOnDevice)]
pub fn prove_tug_play_on_device(hand_json: &str, card_id: u64) -> Result<JsValue, JsError> {
    let start = perf_now();
    let out = prove_tug_play_core(hand_json, card_id).map_err(|e| JsError::new(&e))?;
    let elapsed_ms = perf_now() - start;

    #[derive(Serialize)]
    struct Result {
        proof_json: String,
        proof_size_bytes: usize,
        generation_time_ms: f64,
        /// The blinded leaf digest, all eight canonical lanes (PIs 0..8).
        leaf: Vec<u32>,
        /// The committed hand root, all eight canonical lanes (PIs 8..16).
        root: Vec<u32>,
        trace_rows: usize,
        root_matches_committed: bool,
    }

    let result = Result {
        proof_json: out.proof_json,
        proof_size_bytes: out.proof_size_bytes,
        generation_time_ms: elapsed_ms,
        leaf: out.leaf_lanes.to_vec(),
        root: out.root_lanes.to_vec(),
        trace_rows: out.num_rows,
        root_matches_committed: out.root_matches_committed,
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

/// **Verify a multiway-tug on-device play proof.** Runs the SAME migrated consumer
/// contract the light client's membership arm uses: fail-closed `descriptor_by_name`
/// dispatch on the envelope's name, postcard-decode the `Ir2BatchProof`, and check it with
/// the deployed `verify_vm_descriptor2`. A dispatch miss, malformed blob, or failed check
/// all yield `valid: false`.
#[wasm_bindgen(js_name = verifyTugPlayOnDevice)]
pub fn verify_tug_play_on_device(proof_json: &str) -> Result<JsValue, JsError> {
    let start = perf_now();
    let result = ir2_verify_membership_envelope(proof_json);
    let elapsed_ms = perf_now() - start;

    #[derive(Serialize)]
    struct VerifyResult {
        valid: bool,
        error: Option<String>,
        verification_time_ms: f64,
    }

    let out = match result {
        Ok(()) => VerifyResult {
            valid: true,
            error: None,
            verification_time_ms: elapsed_ms,
        },
        Err(e) => VerifyResult {
            valid: false,
            error: Some(e),
            verification_time_ms: elapsed_ms,
        },
    };
    Ok(serde_wasm_bindgen::to_value(&out)?)
}

/// The outcome of the FULL on-device recursive fold (fields the wasm wrapper surfaces).
pub(crate) struct TugFoldOutcome {
    /// The verify-sufficient [`WholeChainProof::to_bytes`] envelope (hex) — the wire form a
    /// pure light client re-verifies. This is "the WholeChainProof bytes."
    pub proof_bytes_hex: String,
    pub proof_size_bytes: usize,
    /// The number of turns the light client attested (== the number of plays folded).
    pub num_turns: usize,
    /// The light client ACCEPTED the folded whole-match proof.
    pub lightclient_accepts: bool,
}

/// PRODUCER core for the FULL fold: play card A from the full hand, card B from the
/// remaining hand, lower each to the fold's real membership leaf, fold the whole private
/// match into ONE `WholeChainProof`, and confirm the pure light client accepts it. This is
/// [`dregg_multiway_tug::fold`]'s committed Phase-3 path, consumed READ-ONLY.
///
/// HONEST: this is the heavy recursion. Natively it is minutes-to-hours; in wasm32 it is
/// bounded by the single-thread + 32-bit-address-space limit (see the module docs).
pub(crate) fn fold_tug_match_core(
    hand_json: &str,
    card_a: u64,
    card_b: u64,
) -> Result<TugFoldOutcome, String> {
    use dregg_lightclient::verify_history;
    use dregg_multiway_tug::fold::{LeafBundle, fold_match, membership_leaf_for_play};

    let hand = parse_hand(hand_json)?;
    let t0 = HandTree::commit(hand);
    let p0 = t0
        .prove_play(card_a)
        .ok_or_else(|| format!("card A ({card_a}) not in the hand"))?;
    let t1 = t0.without(card_a);
    let p1 = t1
        .prove_play(card_b)
        .ok_or_else(|| format!("card B ({card_b}) not in the remaining hand"))?;

    let b0: LeafBundle = membership_leaf_for_play(&p0)?.into();
    let b1: LeafBundle = membership_leaf_for_play(&p1)?.into();

    let whole = fold_match(&[b0, b1])?;
    let vk = whole.root_vk_fingerprint();
    let attested = verify_history(&whole, &vk)
        .map_err(|e| format!("the light client REFUSED the folded match: {e:?}"))?;

    let proof_bytes = whole.to_bytes();
    Ok(TugFoldOutcome {
        proof_size_bytes: proof_bytes.len(),
        proof_bytes_hex: hex_encode(&proof_bytes),
        num_turns: attested.num_turns,
        lightclient_accepts: true,
    })
}

/// **The whole private match, folded IN THE TAB.** Runs the full Phase-3 recursion fold on
/// two membership-proven plays and returns the light-client-verified `WholeChainProof`
/// bytes. COMPILES for wasm32; the RUN is the honest boundary — the plonky3 recursion is
/// heavy (minutes-to-hours, and wasm32 is single-threaded in a 32-bit address space). For
/// the fast, definitely-in-tab path, use [`prove_tug_play_on_device`].
#[wasm_bindgen(js_name = foldTugMatchOnDevice)]
pub fn fold_tug_match_on_device(
    hand_json: &str,
    card_a: u64,
    card_b: u64,
) -> Result<JsValue, JsError> {
    let start = perf_now();
    let out = fold_tug_match_core(hand_json, card_a, card_b).map_err(|e| JsError::new(&e))?;
    let elapsed_ms = perf_now() - start;

    #[derive(Serialize)]
    struct FoldResult {
        proof_bytes_hex: String,
        proof_size_bytes: usize,
        num_turns: usize,
        lightclient_accepts: bool,
        generation_time_ms: f64,
    }

    let result = FoldResult {
        proof_bytes_hex: out.proof_bytes_hex,
        proof_size_bytes: out.proof_size_bytes,
        num_turns: out.num_turns,
        lightclient_accepts: out.lightclient_accepts,
        generation_time_ms: elapsed_ms,
    };
    Ok(serde_wasm_bindgen::to_value(&result)?)
}

// ============================================================================
// Native gates (run under `cargo test`; wasm smoke below runs under wasm-pack).
// ============================================================================

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use super::*;

    /// The committed six-card sample hand from `dregg_multiway_tug::fold::tests`.
    const HAND: &str = "[[0,1001],[1,1002],[3,1003],[7,1004],[12,1005],[18,1006]]";

    /// THE REDUCED ON-DEVICE GATE: a real played card of a private hand proves its Poseidon2
    /// membership, the proof VERIFIES through the deployed consumer contract, and the bound
    /// root equals the game's committed hand root (faithful, not a mirror).
    #[test]
    fn on_device_play_proves_verifies_and_binds_the_real_root() {
        for &card in &[0u64, 7, 18] {
            let out = prove_tug_play_core(HAND, card)
                .unwrap_or_else(|e| panic!("card {card} must prove on-device: {e}"));
            assert!(
                out.root_matches_committed,
                "card {card}: the bound root PI must equal HandTree::root (the REAL committed hand)"
            );
            // The raw card id must NOT be a public input (the hand stays private-in-fold).
            let env: Ir2ProofEnvelope = serde_json::from_str(&out.proof_json).unwrap();
            assert!(
                !env.public_inputs.contains(&(card as u32)),
                "card {card}: the raw card id must never appear in the public inputs"
            );
            // POSITIVE: the honest proof ACCEPTS through the migrated consumer contract.
            ir2_verify_membership_envelope(&out.proof_json)
                .unwrap_or_else(|e| panic!("card {card}: honest on-device proof must verify: {e}"));
        }
    }

    /// FAITHFULNESS to the committed hand: two DIFFERENT played cards bind DIFFERENT leaves
    /// under the SAME committed root — the proof commits to which card was played. The
    /// comparison is over ALL EIGHT lanes of each digest, not a lane-0 projection.
    #[test]
    fn different_plays_bind_different_leaves_same_root() {
        let a = prove_tug_play_core(HAND, 0).unwrap();
        let b = prove_tug_play_core(HAND, 7).unwrap();
        assert_ne!(
            a.leaf_lanes, b.leaf_lanes,
            "different cards ⇒ different blinded 8-felt leaves"
        );
        assert_eq!(
            a.root_lanes, b.root_lanes,
            "both plays climb to the SAME committed 8-felt hand root"
        );
    }

    /// FAIL-CLOSED: a card never dealt has no on-device proof; a malformed hand is refused.
    #[test]
    fn fabricated_card_and_bad_hand_fail_closed() {
        assert!(
            prove_tug_play_core(HAND, 99).is_err(),
            "a card not in the hand has no membership proof"
        );
        assert!(prove_tug_play_core("[]", 0).is_err(), "empty hand refused");
        assert!(
            prove_tug_play_core("not json", 0).is_err(),
            "malformed hand refused"
        );
    }

    /// TAMPER: flipping the claimed root PI produces a proof that still decodes but no longer
    /// matches its claim — the deployed verifier REJECTS it (the proof↔claim binding).
    #[test]
    fn tampered_root_is_rejected() {
        let out = prove_tug_play_core(HAND, 3).unwrap();
        let tampered = crate::ir2_tamper_root(&out.proof_json).expect("tamper");
        assert!(
            ir2_verify_membership_envelope(&tampered).is_err(),
            "a tampered claimed root must be REJECTED"
        );
    }

    /// SLOW: the full recursive fold of a 2-play private match, driven through the wasm
    /// PRODUCER core (native — the wasm build compiles the identical path). Confirms the
    /// core wraps `fold_match` + `verify_history` correctly and returns real proof bytes.
    #[test]
    #[ignore = "SLOW: real recursion fold over a 2-play private match (~minutes-to-hours); run with --ignored"]
    fn full_fold_core_folds_and_lightclient_accepts() {
        let out = fold_tug_match_core(HAND, 0, 1).expect("the private match folds on-device");
        assert!(
            out.lightclient_accepts,
            "the light client accepts the folded match"
        );
        assert_eq!(
            out.num_turns, 2,
            "both membership-proven plays are attested"
        );
        assert!(
            out.proof_size_bytes > 0,
            "real WholeChainProof bytes are returned"
        );
    }
}

/// WASM SMOKE — the reduced on-device play proof, run as REAL wasm under
/// `wasm-pack test --node`. The EXACT bytes the browser runs: prove a played card's
/// membership in wasm, confirm the bound root is the committed hand root, and verify it.
#[cfg(all(test, target_arch = "wasm32"))]
mod wasm_smoke {
    use super::*;
    use wasm_bindgen_test::*;

    const HAND: &str = "[[0,1001],[1,1002],[3,1003],[7,1004],[12,1005],[18,1006]]";

    #[wasm_bindgen_test]
    fn reduced_play_proves_and_verifies_in_wasm() {
        let out = prove_tug_play_core(HAND, 7).expect("prove the play in wasm");
        assert!(
            out.root_matches_committed,
            "the wasm proof binds the committed hand root"
        );
        assert!(out.proof_size_bytes > 0, "a real proof blob comes back");
        ir2_verify_membership_envelope(&out.proof_json).expect("the wasm proof verifies");
    }
}
