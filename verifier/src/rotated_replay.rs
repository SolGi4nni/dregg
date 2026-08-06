//! Rotated replay-chain verify — the standalone chain verifier. No code path here
//! calls a prover (see the crate docblock on what is nevertheless LINKED).
//!
//! # What a leg is, and how the chain closes
//!
//! Each [`RotatedReplayLeg`] mirrors the SDK's `AttachedSubProof` for the
//! `"effect-vm-rotated"` label: a postcard-serialized `Ir2BatchProof`, the rotated
//! PI vector, and the cohort descriptor's `vk_hash`. The rotated PI vector
//! PREFIXES the v1 PI layout, so the v1 offsets sit where the v1 leg puts them:
//! `pi::OLD_COMMIT` = 0, `pi::NEW_COMMIT` = 8 (Phase C widened `OLD_COMMIT_LEN` to 8),
//! `pi::TURN_HASH_BASE` = 33. A WIDE leg
//! additionally publishes the FULL 8-felt before/after commits as its LAST 16 PIs.
//! Real widths, measured: `V1_PI_COUNT` = 42 (the v1 prefix), `ROT_PI_COUNT` = 46
//! (the prefix plus the four appended rotated pins), `ROT_NULLIFIER_PI_COUNT` = 47
//! for a note-spend leg, `WIDE_PI_COUNT` = 66 for the wide core.
//!
//! # ⚑ FLAG DAY 2026-08-05 — this floor now accepts what the WIRE emits, at the WIRE's width
//!
//! Until this commit [`verify_rotated_leg`] iterated ONLY `V3_STAGED_REGISTRY_TSV`
//! (the 1-felt / ~31-bit stratum), while every production producer
//! (`dregg_sdk::prove_cohort_run_chain`, `dregg_turn_prover::proven_receipt`) emits
//! WIDE or WIDE+UMEM-WELDED legs. A production proof handed to this floor verified
//! under NO member and was REJECTED — the subcommand could not return "verified"
//! for anything a real node had produced. The module's own docblock called that
//! "behind the WIDE flip by construction" and deferred it; that is a check nobody
//! could pass, which is not a floor.
//!
//! Two changes, and they must be taken together:
//!
//! 1. **The accepted set is the DEPLOYED set.** [`verify_rotated_leg`] now collects
//!    accepting members from `WIDE_REGISTRY_STAGED_TSV` and the DERIVED welded-wide
//!    set (`welded_wide_members()`) — the same two the SDK's
//!    `verify_effect_vm_rotated_inner` admits — and, additionally, the bare
//!    `V3_STAGED_REGISTRY_TSV` for the 1-felt residual (the 3 gentian Sat members
//!    have no wide twin, and this floor's own test producers mint narrow). Selector
//!    binding is unchanged: EXACTLY ONE member may accept.
//! 2. **The chain anchors are 8-felt.** Reading a WIDE leg's ~124-bit anchor at its
//!    narrow slot-0 position is the exact defect `vk_hash_is_wide` was introduced to
//!    fix in the SDK, so adding wide acceptance without widening the anchor would
//!    have re-shipped it. [`verify_rotated_replay_chain`] now takes `[BabyBear; 8]`
//!    endpoints and reads each leg at its TRUE width: a leg whose `vk_hash` is a
//!    wide-registry (or welded) fingerprint is bound on its LAST 16 PIs; a narrow V3
//!    leg is bound on its single `pi::OLD_COMMIT`/`pi::NEW_COMMIT` felt broadcast
//!    into lane 0, with the other seven lanes zero. That is the SAME rule
//!    `dregg_sdk::verify_full_turn_bound` applies, so the two floors agree.
//!
//! **What re-emits / breaks:** the `rotated-replay-chain` request JSON's
//! `expected_old_commit` / `expected_new_commit` are now 8-element arrays of
//! canonical `u32` BabyBear lanes, not single integers. A request written before
//! this commit REFUSES TO LOAD with a parse error rather than being reinterpreted.
//! Nothing persists these requests; re-emit them from the producer. Callers of
//! `verify_rotated_replay_chain` pass `[BabyBear; 8]`; a narrow-leg caller widens
//! its felt with [`narrow_commit_anchor`].
//!
//! # The anti-ghost teeth (what makes this NOT a stub)
//!
//! 1. **Per-leg crypto verify** ([`verify_rotated_leg`]) — the IR-v2 batch proof
//!    must verify against a committed cohort descriptor via the audited
//!    `verify_vm_descriptor2`. A forged / corrupted proof has no satisfying
//!    witness and is rejected. The verify is SELECTOR-BOUND (a sound rotated
//!    proof verifies under EXACTLY ONE cohort descriptor — its own effect's), so
//!    a proof that verifies under zero or multiple descriptors is rejected rather
//!    than laundered under the wrong selector.
//! 2. **vk_hash pin** — the attached `vk_hash` must equal the descriptor-identity
//!    fingerprint of the uniquely-accepting member. For a SHIPPED member that is the
//!    blake3 of the committed JSON its registry line carries; for a DERIVED welded
//!    member there is no committed string, so it is the canonical-bytes fingerprint
//!    (`welded_descriptor_vk_hash`). A tampered vk_hash is rejected even when the
//!    proof is selector-bound (Wall A.1).
//! 3. **Endpoint + adjacency** ([`verify_rotated_replay_chain`]) — the caller
//!    supplies the pre/post commitments it trusts; the first leg's before-anchor
//!    and last leg's after-anchor must match, and interior adjacency must close.
//!    A tampered / dropped middle leg breaks adjacency (anti-ghost at the chain
//!    layer). A wrong-root caller expectation is rejected at the endpoints.
//! 4. **Receipt binding** ([`crate::check_receipt_pi_binding`], run per leg by
//!    [`verify_rotated_replay_chain`]) — each leg carries the [`RotatedReplayLeg::receipt`]
//!    it attests, and the chain enforces `PI[TURN_HASH_BASE..+4] ==
//!    canonical_32_to_felts_4(receipt.turn_hash)` (T11 — a genuine proof of turn A
//!    cannot be relabelled onto a receipt naming turn B) plus the receipt chain-walk
//!    `receipt[k].previous_receipt_hash == receipt[k-1].receipt_hash()` (T8).
//!
//! # Isolation
//!
//! This module composes ONLY proven Lean-emitted verify surfaces from
//! `dregg-circuit` (`descriptor_ir2::verify_vm_descriptor2`, the committed
//! registries). It authors NO constraint (LAW #1) and pulls in no prover, ledger,
//! or executor state — the standalone-verifier invariant holds.

use dregg_circuit::descriptor_ir2::{
    DreggStarkConfig, EffectVmDescriptor2, Ir2BatchProof, parse_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::pi;
use dregg_circuit::effect_vm::trace_rotated::V1_PI_COUNT;
use dregg_circuit::effect_vm_descriptors::{
    V3_STAGED_REGISTRY_TSV, WIDE_REGISTRY_STAGED_TSV, welded_wide_members,
};
use dregg_circuit::field::BabyBear;
use serde::{Deserialize, Serialize};

/// The descriptor-identity fingerprint of a DERIVED welded member — the standalone
/// twin of `dregg_sdk::full_turn_proof::welded_descriptor_vk_hash`, reimplemented here
/// because this crate must not depend on `dregg-sdk` (the standalone-verifier
/// invariant). It is NOT `blake3(committed JSON)`: a welded member has no committed
/// JSON string, so it fingerprints the descriptor's CANONICAL bytes
/// (`descriptor_ir2_canonical`, schema-v1, serde-free), which every holder of the
/// object can recompute from the object. `None` when the descriptor is not canonically
/// representable — the caller then simply does not match it, which is fail-closed.
fn welded_descriptor_fingerprint(desc: &EffectVmDescriptor2) -> Option<[u8; 32]> {
    dregg_circuit::descriptor_ir2_canonical::canonical_effect_vm_descriptor2_bytes(desc)
        .ok()
        .map(|bytes| *blake3::hash(&bytes).as_bytes())
}

/// Widen a 1-felt (~31-bit) commitment into the 8-felt anchor shape, lane 0 carrying
/// the felt and lanes 1..8 zero. This is the SAME broadcast
/// `dregg_sdk::verify_full_turn_bound` applies to a narrow cap-open residual leg, and
/// the only honest way to compare a narrow leg's published commit against the 8-felt
/// anchor the chain speaks in. A caller that has a real 8-felt commitment must pass it
/// whole — widening a felt does not manufacture the missing ~93 bits.
pub fn narrow_commit_anchor(felt: BabyBear) -> [BabyBear; 8] {
    let mut out = [BabyBear::ZERO; 8];
    out[0] = felt;
    out
}

/// One `"effect-vm-rotated"` leg of a rotated replay chain.
///
/// Mirrors the SDK's `dregg_dsl_runtime::composition::AttachedSubProof` for the
/// rotated label, but in the verifier's on-disk u32-PI convention. The producer
/// emits exactly this triple per cohort-run (`prove_cohort_run_chain`): the postcard
/// `Ir2BatchProof`, the rotated PI vector, the cohort vk_hash.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RotatedReplayLeg {
    /// The `TurnReceipt` this leg attests. REQUIRED (no `serde(default)`): a request
    /// JSON without it REFUSES TO LOAD rather than silently verifying a chain with no
    /// receipt binding, which is what the field's absence used to mean.
    ///
    /// [`verify_rotated_replay_chain`] binds it two ways — `PI[TURN_HASH_BASE..+4] ==
    /// canonical_32_to_felts_4(receipt.turn_hash)` and the receipt chain-walk — via
    /// [`crate::check_receipt_pi_binding`].
    pub receipt: dregg_turn::TurnReceipt,
    /// Postcard-serialized `Ir2BatchProof<DreggStarkConfig>` (the multi-table
    /// rotated batch proof).
    pub proof_bytes: Vec<u8>,
    /// The rotated public-input vector as canonical `u32` BabyBear values. At least
    /// [`V1_PI_COUNT`] (42) elements: `OLD_COMMIT` at 0, `NEW_COMMIT` at 8, the v1
    /// prefix `[0..42)`, then the 4 appended rotated pins (`ROT_PI_COUNT` = 46; 47
    /// with the note-spend nullifier pin). A WIDE leg runs to `WIDE_PI_COUNT` = 66
    /// and publishes the 8-felt before/after commits as its LAST 16 elements.
    pub public_inputs: Vec<u32>,
    /// The cohort descriptor's identity fingerprint — pinned against the
    /// uniquely-accepting descriptor. This ALSO classifies the leg's commit width:
    /// a wide-registry or welded fingerprint means the 8-felt tail is authoritative.
    pub vk_hash: [u8; 32],
}

impl RotatedReplayLeg {
    /// Lift the on-disk u32 PI vector to BabyBear felts (the form the IR-v2
    /// verifier consumes).
    fn pi_felts(&self) -> Vec<BabyBear> {
        self.public_inputs
            .iter()
            .map(|&v| BabyBear::new_canonical(v))
            .collect()
    }

    /// This leg's `(before8, after8)` commit anchors AT THE LEG'S TRUE WIDTH.
    ///
    /// A WIDE / welded leg publishes the full 8-felt commits as its LAST 16 PIs (the
    /// ~124-bit anchor the wide descriptor's carrier pi_bindings tie to the proof's
    /// bound carriers). A narrow V3 leg carries a single felt at
    /// `pi::OLD_COMMIT`/`pi::NEW_COMMIT`, broadcast into lane 0. Classified by
    /// `vk_hash`, exactly the way `dregg_sdk::verify_full_turn_bound` classifies it.
    fn commit_anchors(&self) -> Result<([BabyBear; 8], [BabyBear; 8]), String> {
        let felts = self.pi_felts();
        let n = felts.len();
        if vk_hash_is_wide(&self.vk_hash) {
            if n < 16 {
                return Err(format!(
                    "wide rotated leg too short for the 8-felt commit tail: {n} PIs < 16"
                ));
            }
            let before: [BabyBear; 8] = felts[n - 16..n - 8].try_into().expect("slice of len 8");
            let after: [BabyBear; 8] = felts[n - 8..n].try_into().expect("slice of len 8");
            Ok((before, after))
        } else {
            if n <= pi::NEW_COMMIT {
                return Err(format!(
                    "narrow rotated leg too short for its commit felts: {n} PIs"
                ));
            }
            Ok((
                narrow_commit_anchor(felts[pi::OLD_COMMIT]),
                narrow_commit_anchor(felts[pi::NEW_COMMIT]),
            ))
        }
    }
}

/// Is this `vk_hash` the identity fingerprint of a WIDE (8-felt / ~124-bit) member —
/// either a shipped `WIDE_REGISTRY_STAGED_TSV` row or a DERIVED welded-wide member?
///
/// UNCONDITIONAL: the registry const is an ungated `include_str!` and `blake3` is a
/// non-optional dep, so this floor classifies legs the same way on every build. The
/// SDK's twin (`vk_hash_is_wide`) once had a `cfg`-gated stub that answered `false`
/// on exactly the light-client build and read a wide leg's ~124-bit anchor at its
/// ~31-bit slot; there is no `cfg` here for that reason.
fn vk_hash_is_wide(vk_hash: &[u8; 32]) -> bool {
    let shipped = WIDE_REGISTRY_STAGED_TSV.lines().any(|line| {
        line.splitn(3, '\t')
            .nth(2)
            .map(|json| blake3::hash(json.as_bytes()).as_bytes() == vk_hash)
            .unwrap_or(false)
    });
    shipped
        || welded_wide_members()
            .iter()
            .any(|(_key, desc)| welded_descriptor_fingerprint(desc).as_ref() == Some(vk_hash))
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

/// Overall rotated-chain verdict.
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

/// The SELECTOR-BOUND descriptor resolution shared by [`verify_rotated_leg`] and the
/// cross-federation receipt verifier: deserialize the [`Ir2BatchProof`] and find the
/// member(s) of the accepted registries it verifies under.
///
/// Returns the uniquely-accepting member's `(registry key, identity fingerprint)`.
/// Zero accepting members ⇒ not a rotated cohort proof (reject); more than one ⇒
/// ambiguous (reject rather than launder a wrong-descriptor acceptance).
///
/// The accepted set is the DEPLOYED set plus the 1-felt residual, in this order:
/// `WIDE_REGISTRY_STAGED_TSV`, the derived welded-wide members, then
/// `V3_STAGED_REGISTRY_TSV`. The fingerprint differs by provenance — a SHIPPED member
/// hashes the committed JSON string its registry line carries, a DERIVED welded member
/// hashes its canonical bytes — so it is computed at collection time, not afterwards.
pub fn resolve_rotated_descriptor(
    proof_bytes: &[u8],
    public_inputs: &[BabyBear],
) -> Result<(String, [u8; 32]), String> {
    let proof: Ir2BatchProof<DreggStarkConfig> = postcard::from_bytes(proof_bytes)
        .map_err(|e| format!("rotated effect-vm proof deserialize: {e}"))?;

    let mut bound: Vec<(String, [u8; 32])> = Vec::new();

    let mut collect_shipped = |registry: &'static str| {
        for line in registry.lines() {
            let mut it = line.splitn(3, '\t');
            let Some(name) = it.next() else { continue };
            let _display = it.next();
            let Some(json) = it.next() else { continue };
            if let Ok(desc) = parse_vm_descriptor2(json)
                && public_inputs.len() >= desc.public_input_count
            {
                let dpis = &public_inputs[..desc.public_input_count];
                if verify_vm_descriptor2(&desc, &proof, dpis).is_ok() {
                    bound.push((name.to_string(), *blake3::hash(json.as_bytes()).as_bytes()));
                }
            }
        }
    };
    collect_shipped(WIDE_REGISTRY_STAGED_TSV);
    collect_shipped(V3_STAGED_REGISTRY_TSV);

    // The welded-wide set is DERIVED, not shipped: it has no committed JSON string, so
    // its fingerprint is the canonical-bytes one the producer pinned.
    let welded: Vec<(&'static str, EffectVmDescriptor2)> = welded_wide_members();
    for (key, desc) in &welded {
        if public_inputs.len() >= desc.public_input_count {
            let dpis = &public_inputs[..desc.public_input_count];
            if verify_vm_descriptor2(desc, &proof, dpis).is_ok()
                && let Some(fp) = welded_descriptor_fingerprint(desc)
            {
                bound.push((key.to_string(), fp));
            }
        }
    }

    match bound.len() {
        1 => Ok(bound.remove(0)),
        0 => Err(
            "rotated effect-vm proof verified under NO cohort descriptor (wide, welded-wide, or \
             bare V3)"
                .to_string(),
        ),
        _ => Err(format!(
            "rotated effect-vm proof verified under MULTIPLE cohort descriptors {:?} — selector \
             binding ambiguous, rejecting",
            bound.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>()
        )),
    }
}

/// Verify ONE rotated `"effect-vm-rotated"` leg (the standalone twin of the SDK's
/// `verify_effect_vm_rotated_with_cutover`).
///
/// Resolves the uniquely-accepting cohort descriptor ([`resolve_rotated_descriptor`])
/// and pins the attached `vk_hash` to that member's identity fingerprint.
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

    let (_name, derived) = resolve_rotated_descriptor(&leg.proof_bytes, &leg.pi_felts())?;
    if derived != leg.vk_hash {
        return Err(format!(
            "rotated effect-vm vk_hash mismatch: attached {} != accepting cohort descriptor \
             fingerprint {}",
            hex::encode(leg.vk_hash),
            hex::encode(derived)
        ));
    }
    Ok(())
}

/// Verify a ROTATED replay chain: N `"effect-vm-rotated"` legs (in chain order
/// `s0 → s1 → … → sN`) against the caller's trusted pre/post commitments.
///
/// For a homogeneous turn the fleet ships ONE leg (so the chain collapses to the two
/// endpoint checks); a heterogeneous turn (PATH-PRESERVE §3) ships N chained legs,
/// one per maximal homogeneous cohort-run.
///
/// Per leg:
/// 1. Cryptographically verify the leg ([`verify_rotated_leg`]): IR-v2 proof
///    selector-bound to its cohort descriptor + vk_hash pinned.
/// 1b. Bind the leg to the RECEIPT it carries ([`crate::check_receipt_pi_binding`]):
///    `PI[TURN_HASH_BASE..+4] == canonical_32_to_felts_4(receipt.turn_hash)` (T11) and
///    the receipt chain-walk `receipt[k].previous_receipt_hash ==
///    receipt[k-1].receipt_hash()`, head-must-be-`None` (T8).
///
/// Chain-level:
/// 2. `legs[0]` before-anchor `== expected_old_commit` (the turn's pre-state).
/// 3. `legs[last]` after-anchor `== expected_new_commit` (the turn's post-state).
/// 4. adjacency: `legs[k]` before-anchor `== legs[k-1]` after-anchor (no gap, no splice).
///
/// Every anchor is the 8-felt commitment read at the leg's TRUE width (see
/// [`RotatedReplayLeg::commit_anchors`]): a wide/welded leg's LAST 16 PIs, a narrow V3
/// leg's single felt in lane 0.
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
    expected_old_commit: [BabyBear; 8],
    expected_new_commit: [BabyBear; 8],
) -> RotatedChainOutput {
    let mut per_leg: Vec<RotatedReplayVerdict> = Vec::with_capacity(legs.len());
    let mut first_failure: Option<usize> = None;
    let mut verified = 0usize;

    // -- Step 1: per-leg cryptographic verification, then the RECEIPT BINDING. --
    //
    // The binding runs on the leg's REAL PI vector (a rotated leg is 46-66 felts and
    // `check_receipt_pi_binding`'s precondition is derived from the offsets it reads,
    // so it decides rather than bailing on length). It is the only thing tying this
    // chain's proofs to the receipts they claim to attest: without it a genuine proof
    // of turn A verifies happily beside a receipt naming turn B, and the chain-walk
    // over receipt hashes is never taken.
    let mut prev_receipt_hash: Option<[u8; 32]> = None;
    for (idx, leg) in legs.iter().enumerate() {
        let verdict = match verify_rotated_leg(leg) {
            Ok(()) => {
                match crate::check_receipt_pi_binding(
                    &leg.receipt,
                    &leg.public_inputs,
                    prev_receipt_hash,
                ) {
                    None => {
                        verified += 1;
                        RotatedReplayVerdict::Verified
                    }
                    Some(reason) => {
                        if first_failure.is_none() {
                            first_failure = Some(idx);
                        }
                        RotatedReplayVerdict::Rejected { reason }
                    }
                }
            }
            Err(reason) => {
                if first_failure.is_none() {
                    first_failure = Some(idx);
                }
                RotatedReplayVerdict::Rejected { reason }
            }
        };
        // Capture the hash regardless of verdict so a downstream break surfaces as a
        // clear chain-walk rejection at the next leg rather than leaving a gap.
        prev_receipt_hash = Some(leg.receipt.receipt_hash());
        per_leg.push(verdict);
    }

    // -- Chain-level commitment checks (only meaningful once every leg is sound;
    //    a leg with a too-short PI vector already failed step 1 and its anchors
    //    are unreadable — surfaced as a Rejected chain check below). --
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
        if first_failure.is_none_or(|f| idx < f) {
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

/// Render an 8-felt anchor for a diagnostic (lane-by-lane, so a ~31-bit narrow lane-0
/// anchor is visibly distinct from a full ~124-bit one).
fn anchor_hex(a: &[BabyBear; 8]) -> String {
    a.iter().map(|f| format!("{:08x}", f.as_u32())).collect()
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
    expected_old_commit: [BabyBear; 8],
    expected_new_commit: [BabyBear; 8],
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
                    anchor_hex(&expected_old_commit),
                    anchor_hex(&expected_new_commit)
                ),
            ));
        }
        return None;
    }

    // If a leg already failed crypto, the chain walk past it is untrustworthy;
    // the endpoint/adjacency checks below only cover the sound prefix.
    let walk_end = first_failure.unwrap_or(legs.len());

    // Endpoint: first leg's before-anchor must equal the trusted pre-state.
    let (first_old, _) = match legs[0].commit_anchors() {
        Ok(a) => a,
        Err(e) => return Some((0, format!("first leg: {e}"))),
    };
    if first_old != expected_old_commit {
        return Some((
            0,
            format!(
                "old_commitment mismatch: expected {}, got {}",
                anchor_hex(&expected_old_commit),
                anchor_hex(&first_old)
            ),
        ));
    }

    // Endpoint: last leg's after-anchor must equal the trusted post-state — but only if
    // the whole chain is cryptographically sound (else the "last" we trust is the leg
    // just before the first failure, which is an incomplete turn → already a failure
    // surfaced by step 1).
    if walk_end == legs.len() {
        let last_idx = legs.len() - 1;
        let (_, last_new) = match legs[last_idx].commit_anchors() {
            Ok(a) => a,
            Err(e) => return Some((last_idx, format!("last leg: {e}"))),
        };
        if last_new != expected_new_commit {
            return Some((
                last_idx,
                format!(
                    "new_commitment mismatch: expected {}, got {}",
                    anchor_hex(&expected_new_commit),
                    anchor_hex(&last_new)
                ),
            ));
        }
    }

    // Adjacency over the sound prefix: leg[k].before == leg[k-1].after.
    for k in 1..walk_end {
        let (_, prev_new) = match legs[k - 1].commit_anchors() {
            Ok(a) => a,
            Err(e) => return Some((k - 1, e)),
        };
        let (this_old, _) = match legs[k].commit_anchors() {
            Ok(a) => a,
            Err(e) => return Some((k, e)),
        };
        if this_old != prev_new {
            return Some((
                k,
                format!(
                    "chain adjacency break at leg {k}: this before-anchor {} != previous \
                     after-anchor {}",
                    anchor_hex(&this_old),
                    anchor_hex(&prev_new)
                ),
            ));
        }
    }

    None
}
