//! Rotated replay-chain verify (the recursion-build replacement for the v1
//! `replay_chain` / `replay_one_with_prev`).
//!
//! # Why this module exists
//!
//! Under `not(recursion)` the verifier replays a chain of `WitnessedReceipt`s by
//! re-running the v1 hand-AIR (`EffectVmAir`) over each inline witness trace
//! ([`crate::replay_chain`]). The recursion build retires that v1 hand-AIR, so
//! the v1 replay path fails closed there (honest rejection, not a silent skip).
//! This module is the rotated REPLACEMENT: it verifies a chain of
//! `"effect-vm-rotated"` legs — each a multi-table IR-v2 batch proof
//! ([`Ir2BatchProof`]) over a rotated R=24 cohort descriptor — exactly the legs
//! the SDK's `prove_cohort_run_chain` / `prove_full_turn` emit and
//! `verify_full_turn` chains.
//!
//! # What a leg is, and how the chain closes
//!
//! Each [`RotatedReplayLeg`] mirrors the SDK's `AttachedSubProof` for the
//! `"effect-vm-rotated"` label: a postcard-serialized `Ir2BatchProof`, the
//! rotated 38-PI vector (or 39 for a single note-spend), and the cohort
//! descriptor's `vk_hash`. The rotated PI vector PREFIXES the v1 PI layout, so
//! `OLD_COMMIT` (index 0) and `NEW_COMMIT` (index 4) sit at the SAME offsets the
//! v1 leg uses — the chain closes the SAME way the SDK chains it: the first
//! leg's `OLD_COMMIT` pins the turn's pre-state commitment, the last leg's
//! `NEW_COMMIT` pins the post-state, and each interior leg's `OLD_COMMIT` must
//! equal the previous leg's `NEW_COMMIT` (no gap, no splice).
//!
//! # The anti-ghost teeth (what makes this NOT a stub)
//!
//! 1. **Per-leg crypto verify** ([`verify_rotated_leg`]) — the IR-v2 batch proof
//!    must verify against a committed rotated cohort descriptor via the audited
//!    `verify_vm_descriptor2`. A forged / corrupted proof has no satisfying
//!    witness and is rejected. The verify is SELECTOR-BOUND (a sound rotated
//!    proof verifies under EXACTLY ONE cohort descriptor — its own effect's), so
//!    a proof that verifies under zero or multiple descriptors is rejected rather
//!    than laundered under the wrong selector. This is the standalone twin of the
//!    SDK's `verify_effect_vm_rotated_with_cutover`.
//! 2. **vk_hash pin** — the attached `vk_hash` must equal the blake3 fingerprint
//!    of the uniquely-accepting cohort descriptor's committed JSON. A tampered
//!    vk_hash is rejected even when the proof is selector-bound (Wall A.1).
//! 3. **Endpoint + adjacency** ([`verify_rotated_replay_chain`]) — the caller
//!    supplies the pre/post commitments it trusts; the first leg's `OLD_COMMIT`
//!    and last leg's `NEW_COMMIT` must match, and interior adjacency must close.
//!    A tampered / dropped middle leg breaks adjacency (anti-ghost at the chain
//!    layer). A wrong-root caller expectation is rejected at the endpoints.
//!
//! # Isolation
//!
//! This module composes ONLY proven Lean-emitted verify surfaces from
//! `dregg-circuit` (`descriptor_ir2::verify_vm_descriptor2`, the committed
//! `V3_STAGED_REGISTRY_TSV`). It authors NO constraint (LAW #1) and pulls in no
//! prover, ledger, or executor state — the standalone-verifier invariant holds.
//!
//! # Deployment role (NOT the production sovereign-verify wire)
//!
//! This is the standalone prover-free `verifier`-floor / CLI demonstration twin
//! (callers: the `dregg-verifier rotated-replay-chain` subcommand and the
//! `integration_rotated_replay_chain` tests). It is NOT on the deployed
//! sovereign turn-verify wire a real proof-carrying turn flows through — that
//! wire is the SDK cutover (`verify_effect_vm_rotated_with_cutover`), the
//! executor (`turn/src/executor/proof_verify.rs`), and the IVC
//! (`admit_welded_leg`), all of which iterate WIDE + WIDE_UMEM_WELD (the 8-felt
//! ~124-bit commitment) and fall back to V3 only for the cap-open residual.
//! This module reads ONLY the 1-felt `V3_STAGED_REGISTRY_TSV`, so it is behind
//! the WIDE flip by construction: it is fed narrow V3 legs by its test/CLI
//! producers and never sees production wire proofs. A wide/welded proof handed
//! here verifies under NO V3 member and is REJECTED (fail-closed, never
//! unsound). Consequence: the umem WIDE/weld flip needs NO pre-flight work
//! here; this floor is off the flip's wire. (Re-pointing the demonstration
//! floor at the wide+welded registries, if ever wanted, is downstream cleanup,
//! not a flip blocker.)

use dregg_circuit::descriptor_ir2::{
    DreggStarkConfig, Ir2BatchProof, parse_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::pi;
use dregg_circuit::effect_vm::trace_rotated::V1_PI_COUNT;
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use serde::{Deserialize, Serialize};

/// One `"effect-vm-rotated"` leg of a rotated replay chain.
///
/// Mirrors the SDK's `dregg_dsl_runtime::composition::AttachedSubProof` for the
/// rotated label, but in the verifier's on-disk u32-PI convention (matching
/// [`crate::ReplayEntry`]). The producer emits exactly this triple per cohort-run
/// (`prove_cohort_run_chain`): the postcard `Ir2BatchProof`, the rotated PI
/// vector, the cohort vk_hash.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RotatedReplayLeg {
    /// Postcard-serialized `Ir2BatchProof<DreggStarkConfig>` (the multi-table
    /// rotated batch proof).
    pub proof_bytes: Vec<u8>,
    /// The rotated public-input vector as canonical `u32` BabyBear values. At
    /// least [`V1_PI_COUNT`] (34) elements: `OLD_COMMIT` at 0, `NEW_COMMIT` at 4,
    /// the v1 prefix `[0..34)`, then the 4 appended rotated pins (and a 5th
    /// nullifier pin for a single note-spend leg).
    pub public_inputs: Vec<u32>,
    /// The cohort descriptor's blake3 fingerprint — pinned against the
    /// uniquely-accepting descriptor's committed JSON.
    pub vk_hash: [u8; 32],
}

impl RotatedReplayLeg {
    /// The leg's `OLD_COMMIT` PI element (index 0), lifted to BabyBear, or `None`
    /// if the PI vector is too short to be a rotated leg.
    fn old_commit(&self) -> Option<BabyBear> {
        self.public_inputs
            .get(pi::OLD_COMMIT)
            .map(|&v| BabyBear::new_canonical(v))
    }

    /// The leg's `NEW_COMMIT` PI element (index 4), lifted to BabyBear, or `None`
    /// if the PI vector is too short to be a rotated leg.
    fn new_commit(&self) -> Option<BabyBear> {
        self.public_inputs
            .get(pi::NEW_COMMIT)
            .map(|&v| BabyBear::new_canonical(v))
    }

    /// Lift the on-disk u32 PI vector to BabyBear felts (the form the IR-v2
    /// verifier consumes).
    fn pi_felts(&self) -> Vec<BabyBear> {
        self.public_inputs
            .iter()
            .map(|&v| BabyBear::new_canonical(v))
            .collect()
    }
}

/// Per-leg verdict from a rotated replay-chain run.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum RotatedReplayVerdict {
    /// The leg's IR-v2 proof verified SELECTOR-BOUND against its cohort
    /// descriptor, the vk_hash pinned, and (for interior/endpoint legs) the chain
    /// commitment checks held.
    Verified,
    /// A verification step failed; `reason` explains.
    Rejected { reason: String },
}

/// Overall rotated-chain verdict (mirrors [`crate::ReplayChainOutput`]).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RotatedChainOutput {
    pub total: usize,
    pub verified: usize,
    /// 0-based index of the first leg that failed verification (None if all green).
    pub first_failure: Option<usize>,
    pub per_leg: Vec<RotatedReplayVerdict>,
    pub overall_verified: bool,
    pub summary: String,
}

/// Verify ONE rotated `"effect-vm-rotated"` leg (the standalone twin of the SDK's
/// `verify_effect_vm_rotated_with_cutover`).
///
/// Deserialize the [`Ir2BatchProof`] and verify it SELECTOR-BOUND against the
/// committed rotated cohort descriptors (`V3_STAGED_REGISTRY_TSV`): a sound
/// rotated proof binds its OWN descriptor (each carries the Lean selector tooth),
/// so EXACTLY ONE cohort member accepts. Zero ⇒ not a rotated cohort proof
/// (reject); more than one ⇒ ambiguous (reject rather than launder a
/// wrong-descriptor acceptance). The attached `vk_hash` is then pinned to the
/// uniquely-accepting descriptor's blake3 fingerprint.
///
/// Returns `Ok(())` on accept, `Err(reason)` on any rejection.
pub fn verify_rotated_leg(leg: &RotatedReplayLeg) -> Result<(), String> {
    // A rotated leg must carry at least the v1 PI prefix (OLD/NEW/EFFECTS_HASH/…).
    if leg.public_inputs.len() < V1_PI_COUNT {
        return Err(format!(
            "rotated leg PI too short: have {} elements, need at least {V1_PI_COUNT}",
            leg.public_inputs.len()
        ));
    }

    let proof: Ir2BatchProof<DreggStarkConfig> = postcard::from_bytes(&leg.proof_bytes)
        .map_err(|e| format!("rotated effect-vm proof deserialize: {e}"))?;

    let public_inputs = leg.pi_felts();

    // The accepting cohort descriptor(s) AND the JSON each was parsed from (so we
    // can re-derive and re-check the attached vk_hash — Wall A.1).
    let mut bound: Vec<(&str, &str)> = Vec::new();
    for line in V3_STAGED_REGISTRY_TSV.lines() {
        let mut it = line.splitn(3, '\t');
        let name = match it.next() {
            Some(n) => n,
            None => continue,
        };
        let _display = it.next();
        let json = match it.next() {
            Some(j) => j,
            None => continue,
        };
        if let Ok(desc) = parse_vm_descriptor2(json) {
            if public_inputs.len() >= desc.public_input_count {
                let dpis = &public_inputs[..desc.public_input_count];
                if verify_vm_descriptor2(&desc, &proof, dpis).is_ok() {
                    bound.push((name, json));
                }
            }
        }
    }

    match bound.as_slice() {
        [(_name, json)] => {
            // Re-derive the rotated vk_hash from the uniquely-accepting cohort
            // descriptor's committed JSON and pin it to the attached vk_hash.
            let derived = *blake3::hash(json.as_bytes()).as_bytes();
            if derived != leg.vk_hash {
                return Err(format!(
                    "rotated effect-vm vk_hash mismatch: attached {} != accepting cohort \
                     descriptor fingerprint {}",
                    hex::encode(leg.vk_hash),
                    hex::encode(derived)
                ));
            }
            Ok(())
        }
        [] => Err("rotated effect-vm proof verified under NO cohort descriptor".to_string()),
        multi => Err(format!(
            "rotated effect-vm proof verified under MULTIPLE cohort descriptors {:?} — selector \
             binding ambiguous, rejecting",
            multi.iter().map(|(n, _)| *n).collect::<Vec<_>>()
        )),
    }
}

/// Verify a ROTATED replay chain: N `"effect-vm-rotated"` legs (in chain order
/// `s0 → s1 → … → sN`) against the caller's trusted pre/post commitments.
///
/// This is the rotated REPLACEMENT for the v1 [`crate::replay_chain`]. For a
/// homogeneous turn the fleet ships ONE leg (so the chain collapses to the two
/// endpoint checks); a heterogeneous turn (PATH-PRESERVE §3) ships N chained
/// legs, one per maximal homogeneous cohort-run.
///
/// Per leg:
/// 1. Cryptographically verify the leg ([`verify_rotated_leg`]): IR-v2 proof
///    selector-bound to its cohort descriptor + vk_hash pinned.
///
/// Chain-level (the analog of the v1 chain-walk invariant):
/// 2. `legs[0].OLD_COMMIT == expected_old_commit` (the turn's pre-state).
/// 3. `legs[last].NEW_COMMIT == expected_new_commit` (the turn's post-state).
/// 4. adjacency: `legs[k].OLD_COMMIT == legs[k-1].NEW_COMMIT` (no gap, no splice).
///
/// `expected_old_commit` / `expected_new_commit` are the canonical pre/post state
/// commitments the verifier trusts (the authenticated cell state, NOT taken from
/// the proof) — mirroring `verify_full_turn`'s arguments. A wrong-root
/// expectation is rejected at step 2/3; a tampered or dropped middle leg at
/// step 4.
///
/// An empty chain verifies vacuously only when the caller's endpoints AGREE
/// (`expected_old_commit == expected_new_commit`) — an empty turn cannot move the
/// commitment. A non-trivial endpoint pair with no legs is rejected.
pub fn verify_rotated_replay_chain(
    legs: &[RotatedReplayLeg],
    expected_old_commit: BabyBear,
    expected_new_commit: BabyBear,
) -> RotatedChainOutput {
    let mut per_leg: Vec<RotatedReplayVerdict> = Vec::with_capacity(legs.len());
    let mut first_failure: Option<usize> = None;
    let mut verified = 0usize;

    // -- Step 1: per-leg cryptographic verification. --
    for (idx, leg) in legs.iter().enumerate() {
        let verdict = match verify_rotated_leg(leg) {
            Ok(()) => {
                verified += 1;
                RotatedReplayVerdict::Verified
            }
            Err(reason) => {
                if first_failure.is_none() {
                    first_failure = Some(idx);
                }
                RotatedReplayVerdict::Rejected { reason }
            }
        };
        per_leg.push(verdict);
    }

    // -- Chain-level commitment checks (only meaningful once every leg is sound;
    //    a leg with a too-short PI vector already failed step 1 and its OLD/NEW
    //    accessors return None — surfaced as a Rejected chain check below). --
    let chain_error: Option<(usize, String)> = chain_commitment_error(
        legs,
        expected_old_commit,
        expected_new_commit,
        first_failure,
    );

    if let Some((idx, reason)) = chain_error {
        // Fold the chain-level rejection into the per-leg verdict at the offending
        // index (so the report names WHERE the chain broke), unless that leg
        // already failed cryptographically.
        if matches!(per_leg.get(idx), Some(RotatedReplayVerdict::Verified)) {
            verified -= 1;
            per_leg[idx] = RotatedReplayVerdict::Rejected {
                reason: reason.clone(),
            };
        }
        if first_failure.map_or(true, |f| idx < f) {
            first_failure = Some(idx);
        }
    }

    let overall_verified = first_failure.is_none();
    let summary = if overall_verified {
        format!("rotated chain verified: {}/{} legs", verified, legs.len())
    } else {
        format!(
            "rotated chain rejected: {}/{} legs verified; first failure at index {}",
            verified,
            legs.len(),
            first_failure.unwrap()
        )
    };

    RotatedChainOutput {
        total: legs.len(),
        verified,
        first_failure,
        per_leg,
        overall_verified,
        summary,
    }
}

/// Compute the chain-level commitment rejection (endpoints + adjacency), if any.
///
/// Returns `Some((leg_index, reason))` naming the leg at which the chain breaks.
/// The empty-chain case is reported at index 0. Legs that already failed the
/// cryptographic step (`first_failure`) are not re-blamed for the chain check —
/// we stop the chain walk at the first cryptographic failure, because a rejected
/// leg's published commitments are not trustworthy.
fn chain_commitment_error(
    legs: &[RotatedReplayLeg],
    expected_old_commit: BabyBear,
    expected_new_commit: BabyBear,
    first_failure: Option<usize>,
) -> Option<(usize, String)> {
    // Empty chain: only an identity turn (old == new) is vacuously consistent.
    if legs.is_empty() {
        if expected_old_commit != expected_new_commit {
            return Some((
                0,
                format!(
                    "empty rotated chain cannot move the commitment: expected_old {} != \
                     expected_new {}",
                    expected_old_commit.as_u32(),
                    expected_new_commit.as_u32()
                ),
            ));
        }
        return None;
    }

    // If a leg already failed crypto, the chain walk past it is untrustworthy;
    // the endpoint/adjacency checks below only cover the sound prefix.
    let walk_end = first_failure.unwrap_or(legs.len());

    // Endpoint: first leg's OLD must equal the trusted pre-state.
    let first = &legs[0];
    let Some(first_old) = first.old_commit() else {
        return Some((0, "first leg PI missing OLD_COMMIT".to_string()));
    };
    if first_old != expected_old_commit {
        return Some((
            0,
            format!(
                "old_commitment mismatch: expected {}, got {}",
                expected_old_commit.as_u32(),
                first_old.as_u32()
            ),
        ));
    }

    // Endpoint: last leg's NEW must equal the trusted post-state — but only if the
    // whole chain is cryptographically sound (else the "last" we trust is the leg
    // just before the first failure, which is an incomplete turn → already a
    // failure surfaced by step 1).
    if walk_end == legs.len() {
        let last = &legs[legs.len() - 1];
        let Some(last_new) = last.new_commit() else {
            return Some((legs.len() - 1, "last leg PI missing NEW_COMMIT".to_string()));
        };
        if last_new != expected_new_commit {
            return Some((
                legs.len() - 1,
                format!(
                    "new_commitment mismatch: expected {}, got {}",
                    expected_new_commit.as_u32(),
                    last_new.as_u32()
                ),
            ));
        }
    }

    // Adjacency over the sound prefix: leg[k].OLD == leg[k-1].NEW.
    for k in 1..walk_end {
        let Some(prev_new) = legs[k - 1].new_commit() else {
            return Some((k - 1, "leg PI missing NEW_COMMIT".to_string()));
        };
        let Some(this_old) = legs[k].old_commit() else {
            return Some((k, "leg PI missing OLD_COMMIT".to_string()));
        };
        if this_old != prev_new {
            return Some((
                k,
                format!(
                    "chain adjacency break at leg {k}: this OLD_COMMIT {} != previous NEW_COMMIT {}",
                    this_old.as_u32(),
                    prev_new.as_u32()
                ),
            ));
        }
    }

    None
}
