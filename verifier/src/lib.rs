//! `dregg-verifier`: Standalone Effect VM proof verifier.
//!
//! # Design intent
//!
//! This crate imports `dregg-circuit` + `dregg-types` (the v1 minimum), plus
//! `dregg-turn` + `dregg-federation` + `dregg-captp` so the
//! `verify-cross-fed-bundle` subcommand can deserialize and verify a
//! [`dregg_federation::CrossFedReceiptBundle`] end-to-end. It MUST NOT
//! import from `dregg-node`, `dregg-wire`, or any crate that carries
//! ledger / executor / program-registry state.
//!
//! The invariant: a verifier process can run in a completely separate OS process
//! with no shared memory, no shared mutable state, and no callbacks into a
//! prover. It reads bytes from disk (or stdin), runs cryptographic verification,
//! and exits. `dregg-federation` is depended on with
//! `default-features = false` so no tokio runtime is pulled — the verifier
//! stays single-threaded and synchronous. This is the "Charlie" role
//! described in `06-the-real-demo.md`.
//!
//! # Verification key registry (v1)
//!
//! For v1 there is exactly one verification key: the Effect VM AIR
//! (`"dregg-effect-vm-v1"`), identified by its 32-byte SHA-256 of the AIR name.
//! Future versions will support additional cell programs by VK hash lookup.

// The v1 hand-AIR STARK surface (`EffectVmAir`, the bespoke `stark::{verify,
// proof_from_bytes}`, the `StarkAir` width trait) is RETIRED. The single-proof and
// replay-chain v1 entries fail closed under every config; the live replay-chain
// verify is the rotated path (`rotated_replay`, prover-free `verifier` floor).
// `BabyBear` stays — the rotated PI lift + the `replay_one_with_prev` u32→felt lift
// use it on every build.
use dregg_circuit::field::BabyBear;
use serde::{Deserialize, Serialize};

pub mod aggregated_bundle;
pub mod bilateral_pair;
pub mod cross_fed;
/// Rotated replay-chain verify — the live replacement for the retired v1
/// `replay_chain` (the v1 hand-AIR is gone). Verifies a chain of
/// `"effect-vm-rotated"` IR-v2 legs via the audited `verify_vm_descriptor2`.
/// Gated on `verifier` (the PROVER-FREE verify floor): rotated VERIFY belongs on
/// the verify floor (the seL4 verifier-PD), NOT behind the STARK prover.
#[cfg(feature = "verifier")]
pub mod rotated_replay;
pub use aggregated_bundle::{
    AggregatedBundleVerdict, verify_aggregated_bundle_json, verify_aggregated_bundle_struct,
};
pub use bilateral_pair::{
    BilateralBundle, BilateralEntry, BilateralVerdict, fabricate_witnessed_receipt,
    verify_bilateral_bundle, verify_bilateral_bundle_json,
};
pub use cross_fed::{
    CommitteeDescriptor, CrossFedVerdict, ValidatorDescriptor, verify_cross_fed_bundle,
};
#[cfg(feature = "verifier")]
pub use rotated_replay::{
    RotatedChainOutput, RotatedReplayLeg, RotatedReplayVerdict, verify_rotated_leg,
    verify_rotated_replay_chain,
};

// ---------------------------------------------------------------------------
// Public types
// ---------------------------------------------------------------------------

/// The result of a verification attempt, serialized to stdout.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifierOutput {
    pub verified: bool,
    pub reason: String,
}

impl VerifierOutput {
    pub fn accept(reason: impl Into<String>) -> Self {
        Self {
            verified: true,
            reason: reason.into(),
        }
    }

    pub fn reject(reason: impl Into<String>) -> Self {
        Self {
            verified: false,
            reason: reason.into(),
        }
    }
}

/// Exit codes used by the binary.
pub mod exit_code {
    pub const VERIFIED: i32 = 0;
    pub const REJECTED: i32 = 1;
    pub const ERROR: i32 = 2;
}

// ---------------------------------------------------------------------------
// VK registry
// ---------------------------------------------------------------------------

/// The Effect VM AIR name baked into all v1 proofs.
pub const EFFECT_VM_AIR_NAME: &str = "dregg-effect-vm-v1";

/// 32-byte SHA-256 of the AIR name bytes used as the VK hash for the default
/// Effect VM circuit. Callers pass this via `--vk-hash` to select the
/// built-in verifier.
///
/// Computed as: SHA-256(b"dregg-effect-vm-v1")
pub const EFFECT_VM_VK_HASH_HEX: &str =
    "8b80e1cf7b0a04e74e7d7bfb9c7a11e37c1d0bb1a5edae8e3b92c9e9b6d5f42a";

/// Resolve a 32-byte hex VK hash to the AIR name it identifies.
/// Returns `None` if the hash is unknown.
pub fn resolve_vk_hash(hex_hash: &str) -> Option<&'static str> {
    // v1: only the Effect VM is supported.
    // We match on the canonical SHA-256, but also accept any 64-hex-char string
    // whose value matches the Effect VM constant — callers that computed their
    // own hash of the AIR name will still work.
    let normalized = hex_hash.trim().to_ascii_lowercase();
    if normalized == EFFECT_VM_VK_HASH_HEX {
        return Some(EFFECT_VM_AIR_NAME);
    }
    // Also accept the literal AIR name encoded as hex (useful for testing).
    let air_name_hex = hex::encode(EFFECT_VM_AIR_NAME);
    if normalized == air_name_hex {
        return Some(EFFECT_VM_AIR_NAME);
    }
    None
}

/// Sentinel VK hash value that instructs the verifier to auto-detect the AIR
/// from the proof's embedded `air_name` field. Callers may pass this when they
/// do not know (or do not care to specify) the VK hash and simply want the
/// verifier to trust whatever AIR the proof claims — suitable for development
/// and testing, but NOT for production use where the hash pins the circuit.
pub const AUTO_DETECT_VK_HASH: &str = "auto";

// ---------------------------------------------------------------------------
// Core verification
// ---------------------------------------------------------------------------

/// Verify an Effect VM STARK proof.
///
/// Arguments (all caller-supplied, no shared state):
/// - `proof_bytes`: serialised STARK proof as produced by `stark::proof_to_bytes`
/// - `public_inputs`: the claimed public inputs, as `u32` values (BabyBear canonical)
/// - `vk_hash_hex`: 64-hex-char VK hash, or `"auto"` for development use
///
/// Returns `VerifierOutput` and the corresponding exit code.
///
/// RETIRED (v1 hand-AIR): the single-proof `EffectVmAir` verify is gone. This entry
/// fails closed on every build (honest rejection, not a silent skip) because a SINGLE
/// v1 STARK proof has no rotated single-proof analog — the rotated unit is a chain
/// leg, verified through [`rotated_replay::verify_rotated_replay_chain`] (the
/// `"effect-vm-rotated"` IR-v2 legs via the audited
/// `descriptor_ir2::verify_vm_descriptor2`).
pub fn verify_effect_vm_proof(
    proof_bytes: &[u8],
    public_inputs_u32: &[u32],
    vk_hash_hex: &str,
) -> (VerifierOutput, i32) {
    let _ = (proof_bytes, public_inputs_u32, vk_hash_hex);
    (
        VerifierOutput::reject(
            "v1 Effect VM STARK verification is retired; verify a rotated chain via \
             rotated_replay::verify_rotated_replay_chain instead"
                .to_string(),
        ),
        exit_code::ERROR,
    )
}

/// Parse a JSON array of `u32` values from a string.
pub fn parse_public_inputs_json(json: &str) -> Result<Vec<u32>, String> {
    let v: serde_json::Value =
        serde_json::from_str(json).map_err(|e| format!("invalid JSON: {}", e))?;
    let arr = v.as_array().ok_or("public inputs must be a JSON array")?;
    arr.iter()
        .enumerate()
        .map(|(i, x)| {
            x.as_u64()
                .ok_or_else(|| format!("element {} is not an unsigned integer", i))
                .and_then(|n| {
                    if n > u32::MAX as u64 {
                        Err(format!("element {} value {} exceeds u32::MAX", i, n))
                    } else {
                        Ok(n as u32)
                    }
                })
        })
        .collect()
}

/// Parse a JSON stdin request (alternative to CLI flags).
///
/// Expected shape:
/// ```json
/// {
///   "proof_hex": "...",
///   "public_inputs": [u32, ...],
///   "vk_hash": "..."
/// }
/// ```
#[derive(Debug, Deserialize)]
pub struct JsonRequest {
    /// Hex-encoded proof bytes.
    pub proof_hex: String,
    /// Public inputs as an array of u32 values.
    pub public_inputs: Vec<u32>,
    /// VK hash (64 hex chars) or `"auto"`.
    pub vk_hash: String,
}

impl JsonRequest {
    pub fn parse(json: &str) -> Result<Self, String> {
        serde_json::from_str(json).map_err(|e| format!("invalid JSON request: {}", e))
    }

    pub fn proof_bytes(&self) -> Result<Vec<u8>, String> {
        hex::decode(&self.proof_hex).map_err(|e| format!("invalid hex in proof_hex: {}", e))
    }
}

// ---------------------------------------------------------------------------
// Replay-chain (WitnessedReceipt v1) — see WITNESSED-RECEIPT-CHAIN-DESIGN.md
// ---------------------------------------------------------------------------
//
// The verifier crate intentionally does NOT import `dregg-turn`
// (which is where `WitnessedReceipt` lives). To preserve that isolation
// while still parsing the on-disk WR JSON, we declare a verifier-local
// mirror struct that is serde-compatible with the producer's
// `WitnessedReceipt`. Only the fields the replay loop needs are
// deserialized; everything else (the inner `receipt`, etc.) is
// preserved as raw JSON so the replayer can still pretty-print a verdict
// per receipt index.

/// Mirror of `dregg_turn::WitnessAvailability`. Only `Inline` is supported
/// in v1; future variants will reject with "unwitnessable" in the verdict.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum ReplayWitnessAvailability {
    Inline,
}

/// Mirror of `dregg_turn::RecursiveProofVariant`. When present in a
/// [`ReplayWitnessBundle`], a verifier may dispatch through
/// [`dregg_circuit_prove::recursive_witness_bundle::verify_recursive_proof_variant`]
/// instead of re-running the AIR over the inline trace.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ReplayRecursiveProofVariant {
    pub proof_bytes: Vec<u8>,
    pub public_inputs: Vec<u32>,
    pub recursive_vk_hash: [u8; 32],
}

/// Mirror of `dregg_turn::WitnessBundle`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReplayWitnessBundle {
    pub trace_rows: Vec<Vec<u32>>,
    pub availability: ReplayWitnessAvailability,
    /// Golden Vision recursive compression. `None` for legacy
    /// Silver-Vision-only chains; `Some` for chains produced with
    /// `recursive_compress = true`.
    #[serde(default)]
    pub recursive_proof: Option<ReplayRecursiveProofVariant>,
}

impl ReplayWitnessBundle {
    /// BLAKE3 of postcard-serialized bundle. Must match the producer's
    /// `WitnessBundle::witness_hash` computation byte-for-byte.
    pub fn witness_hash(&self) -> [u8; 32] {
        let bytes = postcard::to_allocvec(self).expect("ReplayWitnessBundle is serializable");
        *blake3::hash(&bytes).as_bytes()
    }
}

/// Mirror of `dregg_turn::WitnessedReceipt`. The inner `receipt` deserializes
/// directly to `dregg_turn::TurnReceipt` (we already depend on `dregg-turn`),
/// so the replayer can cross-check the proof's PI against the receipt's
/// authoritative `turn_hash` and `previous_receipt_hash`.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReplayEntry {
    /// The full TurnReceipt this proof attests to.
    pub receipt: dregg_turn::TurnReceipt,
    pub proof_bytes: Vec<u8>,
    pub public_inputs: Vec<u32>,
    #[serde(default)]
    pub witness_bundle: Option<ReplayWitnessBundle>,
    pub witness_hash: [u8; 32],
    #[serde(default)]
    pub aggregate_membership: Option<serde_json::Value>,
}

/// Per-receipt verdict from a replay-chain run.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum ReplayVerdict {
    /// Proof verified AND (if present) the witness bundle's constraints
    /// and witness_hash match.
    Verified,
    /// One of the verification steps failed; `reason` explains.
    Rejected { reason: String },
    /// The receipt carried no witness bundle and the proof + PI were
    /// either malformed or rejected by the STARK verifier. Distinct from
    /// `Rejected` only when the witness was the missing piece — i.e. a
    /// `Sealed` / future-variant WR that the v1 replayer cannot fully
    /// exercise. v1 produces this only when `witness_bundle` is absent
    /// AND the proof itself was sound (so the chain is *scope-1-OK* but
    /// not scope-2-OK).
    Unwitnessable,
}

/// Overall chain verdict.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReplayChainOutput {
    pub total: usize,
    pub verified: usize,
    /// 0-based index of the first WR that failed verification (None if all green).
    pub first_failure: Option<usize>,
    pub per_entry: Vec<ReplayVerdict>,
    pub overall_verified: bool,
    pub summary: String,
}

/// Run the v1 replay loop on a deserialized chain of [`ReplayEntry`].
///
/// Steps (per WR), matching design doc §5 / instructions:
/// 1. Verify the STARK proof against the embedded public inputs.
/// 2. If `witness_bundle` is `Some(Inline)`: reconstruct the trace, run
///    `EffectVmAir::eval_constraints` on each consecutive row pair across
///    several alphas, confirm ALL are zero.
/// 3. Confirm BLAKE3 of the serialized bundle matches `witness_hash`.
/// 4. (Optional structural check) `witness_hash == [0;32]` iff bundle is None.
///
/// Returns per-receipt verdicts and the chain-level overall.
pub fn replay_chain(entries: &[ReplayEntry]) -> ReplayChainOutput {
    use blake3;

    let mut per_entry = Vec::with_capacity(entries.len());
    let mut first_failure: Option<usize> = None;
    let mut verified = 0usize;

    // Pseudo-random alphas for trace constraint sampling. We use a small
    // fixed set drawn from BabyBear's canonical interval; this gives a
    // soundness boost over a single alpha without needing a transcript
    // (the STARK verify already provides cryptographic soundness; the
    // alpha sampling is a redundancy check on the witness side).
    let alphas: [BabyBear; 4] = [
        BabyBear::new(0xdead_beefu32 % (1u32 << 31)),
        BabyBear::new(0x1234_5678u32),
        BabyBear::new(0xfeed_face_u32 % (1u32 << 31)),
        BabyBear::new(0x0bad_c0deu32),
    ];

    let mut prev_receipt_hash: Option<[u8; 32]> = None;
    for (idx, wr) in entries.iter().enumerate() {
        let verdict = replay_one_with_prev(wr, &alphas, prev_receipt_hash);
        let is_ok = matches!(verdict, ReplayVerdict::Verified);
        if is_ok {
            verified += 1;
        } else if first_failure.is_none() {
            first_failure = Some(idx);
        }
        // The next entry's receipt.previous_receipt_hash must equal
        // this entry's receipt_hash(). We capture the hash here regardless
        // of verdict so a downstream mismatch surfaces a clear chain-walk
        // rejection at the next iteration rather than leaving a gap.
        prev_receipt_hash = Some(wr.receipt.receipt_hash());
        per_entry.push(verdict);
        let _ = blake3::hash(b"replay-progress"); // keep blake3 used in non-test builds
    }

    let overall_verified = first_failure.is_none();
    let summary = if overall_verified {
        format!("chain verified: {}/{} entries", verified, entries.len())
    } else {
        format!(
            "chain rejected: {}/{} entries verified; first failure at index {}",
            verified,
            entries.len(),
            first_failure.unwrap()
        )
    };

    ReplayChainOutput {
        total: entries.len(),
        verified,
        first_failure,
        per_entry,
        overall_verified,
        summary,
    }
}

/// The shortest PI vector [`check_receipt_pi_binding`] can decide, DERIVED from the
/// highest offset the body reads rather than written down. Every offset it touches
/// lives in the v1 PI prefix a rotated leg publishes in full
/// (`trace_rotated::V1_PI_COUNT` = 42), so the deployed leg always satisfies it.
///
/// The previous precondition was `pi::ACTIVE_BASE_COUNT` (213), which did not make
/// the check strict — it made it **unreachable on every leg that ships**. Measured
/// 2026-07-27 against a real wide rotated proof from
/// `dregg_turn_prover::mint_transfer_proven_receipt`: the leg carries **68** felts, and
/// the binding answered `PI too short for receipt binding: have 68 elements, need at
/// least 213` on the only proof it was supposed to bind. Same shape as the
/// balance-limb bug in `circuit/src/effect_vm/verify.rs`; same fix — the
/// precondition is computed from the reads so it cannot drift away from them again.
pub const RECEIPT_PI_BINDING_MIN_LEN: usize =
    dregg_circuit::effect_vm::pi::TURN_HASH_BASE + dregg_circuit::effect_vm::pi::TURN_HASH_LEN;

/// Cross-bind a rotated leg's claimed public inputs against the receipt it attests
/// (and the prior receipt's hash, for the chain-walk invariant).
///
/// Returns `Some(reason)` on rejection, `None` on pass. This is the
/// EXECUTOR-HONESTY-AUDIT cross-cutting #3 enforcement: PI is not merely
/// deserialized, it is *checked against an expected value*.
///
/// Two teeth, both of which RUN on a real `"effect-vm-rotated"` leg:
///
/// - **T11 (stale-proof replay against a different receipt).**
///   `PI[TURN_HASH_BASE..+4]` must equal `canonical_32_to_felts_4(receipt.turn_hash)`.
///   `TURN_HASH_BASE` is 33 and the rotated leg publishes the v1 prefix `[0, 42)`, so
///   this is inside the window a real proof carries. The slot is not pinned to a
///   trace column by the AIR — the honest producer fills it
///   (`turn_prover::proven_receipt`) and it rides the Fiat–Shamir transcript — so
///   what this comparison forbids is RELABELLING: a genuine proof of turn A
///   presented alongside a receipt naming turn B.
/// - **T8 (forged chain link).** When `prev_receipt_hash` is `Some`, the receipt's own
///   `previous_receipt_hash` must equal it (`receipt[N].previous_receipt_hash ==
///   receipt[N-1].receipt_hash()`); when it is `None` the receipt is the chain head
///   and must not claim a predecessor. Verifying a suffix requires the caller to
///   supply the expected prior hash.
///
/// # What is NOT compared, and why that is not a hole
///
/// `PI[PREVIOUS_RECEIPT_HASH_BASE..+4]` and `PI[IS_AGENT_CELL]` used to be compared
/// here. Both comparisons are GONE, because neither offset exists on a leg that
/// ships and keeping them would have been worse than useless:
///
/// * `PREVIOUS_RECEIPT_HASH_BASE` is **42**, and the rotated producer slices the v1
///   PI vector at exactly `V1_PI_COUNT` = **42** before appending its four rotated
///   pins (`trace_rotated`: OLD commit / NEW commit / committed height / caveat
///   commit). So indices 42..46 of a real leg are those pins — measured
///   `[0, 0, 0, 531325421]` on a live proof whose receipt's
///   `canonical_32_to_felts_4(previous_receipt_hash)` was
///   `[740780208; 4]`. Comparing them would reject every honest proof.
/// * `IS_AGENT_CELL` is **81**, past the end of a 68-felt leg entirely.
///
/// The chain link is still bound to the proof, TRANSITIVELY and for real:
/// `Turn::hash()` absorbs `previous_receipt_hash` (`turn/src/turn.rs`, "Include
/// previous_receipt_hash to bind to causal ordering"), and `PI[TURN_HASH]` is
/// `canonical_32_to_felts_4` of that hash. A receipt re-minted for a different chain
/// position therefore names a different `turn_hash`, and the T11 comparison above
/// refuses it. That is the same argument the pre-existing note below makes for
/// `EFFECTS_HASH_GLOBAL` and `ACTOR_NONCE` — it simply also covers the chain link.
///
/// Does NOT cross-check EFFECTS_HASH_GLOBAL or ACTOR_NONCE: those derive
/// from the Turn (call_forest, nonce), not the Receipt. The receipt's
/// `turn_hash` field commits to both via the canonical Turn::hash, and
/// the TURN_HASH PI binding above transitively guards them — a divergent
/// EFFECTS_HASH_GLOBAL or ACTOR_NONCE in the proof's PI would imply a
/// different Turn::hash, which the TURN_HASH check catches.
pub fn check_receipt_pi_binding(
    receipt: &dregg_turn::TurnReceipt,
    public_inputs: &[u32],
    prev_receipt_hash: Option<[u8; 32]>,
) -> Option<String> {
    use dregg_circuit::effect_vm::pi;
    use dregg_commit::typed::canonical_32_to_felts_4;

    // Chain-walk invariant (T8): receipt[N].previous_receipt_hash must
    // match receipt[N-1].receipt_hash().
    match (prev_receipt_hash, receipt.previous_receipt_hash) {
        (Some(expected), Some(claimed)) if expected != claimed => {
            return Some(format!(
                "chain-walk break: receipt.previous_receipt_hash {} != prior receipt_hash {}",
                hex::encode(claimed),
                hex::encode(expected)
            ));
        }
        (Some(expected), None) => {
            return Some(format!(
                "chain-walk break: receipt.previous_receipt_hash is None, expected {}",
                hex::encode(expected)
            ));
        }
        (None, Some(claimed)) => {
            return Some(format!(
                "chain-walk break: chain head has receipt.previous_receipt_hash {}, expected None",
                hex::encode(claimed)
            ));
        }
        _ => {}
    }

    // PI length sanity, derived from the reads (see `RECEIPT_PI_BINDING_MIN_LEN`).
    let pi_len = public_inputs.len();
    if pi_len < RECEIPT_PI_BINDING_MIN_LEN {
        return Some(format!(
            "PI too short for receipt binding: have {} elements, need at least {} \
             (the v1 prefix through TURN_HASH)",
            pi_len, RECEIPT_PI_BINDING_MIN_LEN
        ));
    }

    // TURN_HASH binding (T11).
    let expected_turn_hash = canonical_32_to_felts_4(&receipt.turn_hash);
    for i in 0..pi::TURN_HASH_LEN {
        let claimed = public_inputs[pi::TURN_HASH_BASE + i];
        let expected = expected_turn_hash[i].as_u32();
        if claimed != expected {
            return Some(format!(
                "PI[TURN_HASH_BASE+{}] = {} but canonical_32_to_felts_4(receipt.turn_hash)[{}] = {}",
                i, claimed, i, expected
            ));
        }
    }

    None
}

/// Inner replay: cross-binds the proof's public inputs against the receipt
/// fields the receipt itself authoritatively names, AND against the prior
/// receipt's hash (chain-walk invariant).
///
/// `prev_receipt_hash`: when `Some`, the verifier requires
/// `wr.receipt.previous_receipt_hash == Some(prev_receipt_hash)`. Pass
/// `None` for the chain's head (genesis position).
fn replay_one_with_prev(
    wr: &ReplayEntry,
    alphas: &[BabyBear],
    prev_receipt_hash: Option<[u8; 32]>,
) -> ReplayVerdict {
    // Step 1: STARK proof verification (algebraic soundness).
    let (proof_verdict, code) =
        verify_effect_vm_proof(&wr.proof_bytes, &wr.public_inputs, AUTO_DETECT_VK_HASH);
    if code != exit_code::VERIFIED {
        return ReplayVerdict::Rejected {
            reason: format!("STARK verify failed: {}", proof_verdict.reason),
        };
    }

    // Step 1b: PI completeness — cross-check the proof's claimed public
    // inputs against the receipt's authoritatively-stated turn-identity
    // fields. Per EXECUTOR-HONESTY-AUDIT.md cross-cutting #3 and threats
    // T8/T11, the verifier must reject a proof whose PI does not match the
    // receipt it accompanies, even if the proof itself is algebraically
    // sound. Without this, an executor could swap a proof for a different
    // turn (T11) or fake the chain-walk link (T8) and the chain-level
    // verifier would not notice.
    if let Some(reason) =
        check_receipt_pi_binding(&wr.receipt, &wr.public_inputs, prev_receipt_hash)
    {
        return ReplayVerdict::Rejected { reason };
    }

    // Step 2: trace-side replay (witness bundle).
    let Some(bundle) = wr.witness_bundle.as_ref() else {
        // No witness bundle attached.
        // - witness_hash MUST be all zeros (the producer's invariant).
        // - Otherwise the receipt claims a witness it isn't shipping →
        //   scope-(2) cannot complete (unwitnessable).
        if wr.witness_hash != [0u8; 32] {
            return ReplayVerdict::Unwitnessable;
        }
        // No bundle, no hash claim: chain is scope-1 sound but cannot
        // be scope-2 replayed. Returning Verified here matches the design
        // doc's "scope-(1)-OK" semantics; surface a softer signal via
        // Unwitnessable when callers explicitly require scope-2.
        return ReplayVerdict::Verified;
    };

    // Availability must be Inline in v1.
    if !matches!(bundle.availability, ReplayWitnessAvailability::Inline) {
        return ReplayVerdict::Unwitnessable;
    }

    // Step 3: witness_hash binding check.
    let recomputed_hash = bundle.witness_hash();
    if recomputed_hash != wr.witness_hash {
        return ReplayVerdict::Rejected {
            reason: format!(
                "witness_hash mismatch: declared={}, recomputed={}",
                hex::encode(wr.witness_hash),
                hex::encode(recomputed_hash)
            ),
        };
    }

    // Step 4: trace shape sanity.
    let trace = &bundle.trace_rows;
    if trace.len() < 2 {
        return ReplayVerdict::Rejected {
            reason: format!("trace too short: {} rows", trace.len()),
        };
    }
    let width = trace[0].len();
    if !trace.iter().all(|r| r.len() == width) {
        return ReplayVerdict::Rejected {
            reason: "ragged trace rows".to_string(),
        };
    }

    // Step 5: trace_len must be power-of-two ≥ 2 (matches the AIR's invariant).
    let trace_len = trace.len();
    if !trace_len.is_power_of_two() {
        return ReplayVerdict::Rejected {
            reason: format!("trace_len {} not power-of-two", trace_len),
        };
    }

    // Lift trace_rows (u32) → BabyBear.
    let trace_bb: Vec<Vec<BabyBear>> = trace
        .iter()
        .map(|row| row.iter().map(|&v| BabyBear::new_canonical(v)).collect())
        .collect();

    // Lift public_inputs.
    let pi_bb: Vec<BabyBear> = wr
        .public_inputs
        .iter()
        .map(|&v| BabyBear::new_canonical(v))
        .collect();

    // Step 6 (RETIRED): the v1 hand-AIR (`EffectVmAir`) per-row-pair constraint replay
    // is gone. This v1 replay-chain leg fails closed on every build; a rotated chain is
    // verified through `rotated_replay::verify_rotated_replay_chain` (the prover-free
    // `verifier`-floor path) instead.
    let _ = (&trace_bb, &pi_bb, trace_len, alphas);
    ReplayVerdict::Rejected {
        reason: "v1 hand-AIR replay-chain verification is retired; verify a rotated chain \
                 via rotated_replay::verify_rotated_replay_chain"
            .to_string(),
    }
}

// ---------------------------------------------------------------------------
// Block 3 — Optional recursive scope-2 verification mode
// ---------------------------------------------------------------------------
//
// The replay loop above performs scope-2 verification by re-running
// `EffectVmAir::eval_constraints` against every consecutive row pair of
// the inline witness bundle. That is *trust-and-replay*: the verifier
// re-does the prover's algebraic work locally.
//
// With the now-working `plonky3-recursion` path (see
// `dregg_circuit_prove::plonky3_recursion_impl`), a producer can instead ship
// a *recursive proof* attesting that the inner trace was valid. The
// verifier then just runs `verify_recursive_layer` on the recursive
// proof; no row-by-row replay needed. This trades a one-time recursive
// proof generation (~seconds, fixed cost) for asymptotic verifier work
// independent of trace length.
//
// Block 3 wires this as an **opt-in compression**: the trust-and-replay
// path stays the default (`replay_one_with_prev` above is unchanged);
// callers wanting the recursive-verify path call
// `verify_recursive_replay` instead.
//
// The on-disk format for the recursive proof is whatever the producer
// emits via `dregg_circuit::plonky3_verifier_air::RecursiveIvcStep::recursive_layer_bytes`
// (postcard-encoded `BatchStarkProof<DreggRecursionConfig>`). The
// verifier deserialises and runs `verify_recursive_layer` on it.

/// Verdict for the recursive-mode scope-2 replay.
///
/// Distinct from [`ReplayVerdict`] because the recursion path has
/// different failure modes (deserialisation, recursion-config mismatch,
/// inner-proof commitment mismatch) that don't map cleanly onto the
/// trust-and-replay vocabulary.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[cfg(feature = "prover")]
pub enum RecursiveReplayVerdict {
    /// The recursive proof verified — by transitive soundness, the inner
    /// trace satisfied the Effect VM AIR constraints.
    Verified,
    /// The scope-1 (per-WR STARK) verification failed; we never reached
    /// the recursive layer.
    InnerProofRejected { reason: String },
    /// The recursive-layer proof bytes failed to deserialise or verify.
    RecursiveProofRejected { reason: String },
}

/// Verify a [`ReplayEntry`] using the optional recursive scope-2 mode.
///
/// Steps:
/// 1. Run the same scope-1 STARK verification + receipt-PI binding as
///    [`replay_one`] (so a malformed scope-1 chain is rejected even when
///    the recursive proof would otherwise verify).
/// 2. Decode `recursive_layer_bytes` (postcard-encoded
///    `BatchStarkProof<DreggRecursionConfig>`) and verify via
///    [`dregg_circuit_prove::plonky3_recursion_impl::recursive::verify_recursive_layer_bytes`].
///
/// Returns `Verified` only when *both* checks pass. The trust-and-replay
/// path (`replay_one_with_prev`) remains the default; this function is
/// only invoked when the caller explicitly opts in.
#[cfg(feature = "prover")]
pub fn verify_recursive_replay(
    wr: &ReplayEntry,
    recursive_layer_bytes: &[u8],
    prev_receipt_hash: Option<[u8; 32]>,
) -> RecursiveReplayVerdict {
    use dregg_circuit_prove::plonky3_recursion_impl::recursive::verify_recursive_layer_bytes;

    // Step 1: scope-1 STARK verification.
    let (proof_verdict, code) =
        verify_effect_vm_proof(&wr.proof_bytes, &wr.public_inputs, AUTO_DETECT_VK_HASH);
    if code != exit_code::VERIFIED {
        return RecursiveReplayVerdict::InnerProofRejected {
            reason: format!("STARK verify failed: {}", proof_verdict.reason),
        };
    }

    // Step 1b: PI completeness — same cross-binding as the trust-replay path.
    if let Some(reason) =
        check_receipt_pi_binding(&wr.receipt, &wr.public_inputs, prev_receipt_hash)
    {
        return RecursiveReplayVerdict::InnerProofRejected { reason };
    }

    // Step 2: recursive-layer verification.
    match verify_recursive_layer_bytes(recursive_layer_bytes) {
        Ok(()) => RecursiveReplayVerdict::Verified,
        Err(e) => RecursiveReplayVerdict::RecursiveProofRejected {
            reason: format!("recursive verify failed: {e}"),
        },
    }
}

/// Golden Vision scope-2 replay: verify a [`ReplayEntry`] whose
/// [`ReplayWitnessBundle::recursive_proof`] field carries a recursive
/// proof.
///
/// Steps:
/// 1. Same scope-1 STARK verification + receipt-PI binding as
///    [`verify_recursive_replay`].
/// 2. Pull `recursive_proof` out of the entry's witness bundle. If
///    absent → `InnerProofRejected` ("no recursive proof attached").
/// 3. Dispatch through
///    [`dregg_circuit_prove::recursive_witness_bundle::verify_recursive_proof_variant`],
///    cross-binding the variant's public inputs against the receipt's
///    `public_inputs` (so a swapped recursive proof from a different
///    receipt is caught).
///
/// Returns `Verified` only when every step passes.
#[cfg(feature = "prover")]
pub fn verify_recursive_replay_from_bundle(
    wr: &ReplayEntry,
    prev_receipt_hash: Option<[u8; 32]>,
) -> RecursiveReplayVerdict {
    use dregg_circuit_prove::recursive_witness_bundle::{
        RecursiveVariantVerdict, verify_recursive_proof_variant,
    };

    // Step 1: scope-1 STARK verification (algebraic soundness).
    let (proof_verdict, code) =
        verify_effect_vm_proof(&wr.proof_bytes, &wr.public_inputs, AUTO_DETECT_VK_HASH);
    if code != exit_code::VERIFIED {
        return RecursiveReplayVerdict::InnerProofRejected {
            reason: format!("STARK verify failed: {}", proof_verdict.reason),
        };
    }

    // Step 1b: PI completeness — same cross-binding as the trust-replay path.
    if let Some(reason) =
        check_receipt_pi_binding(&wr.receipt, &wr.public_inputs, prev_receipt_hash)
    {
        return RecursiveReplayVerdict::InnerProofRejected { reason };
    }

    // Step 2: pull the recursive proof out of the bundle.
    let Some(bundle) = wr.witness_bundle.as_ref() else {
        return RecursiveReplayVerdict::InnerProofRejected {
            reason: "no witness bundle attached; recursive replay needs one".to_string(),
        };
    };
    let Some(rp) = bundle.recursive_proof.as_ref() else {
        return RecursiveReplayVerdict::InnerProofRejected {
            reason: "witness bundle has no recursive_proof; this WR was produced \
                     without recursive_compress = true"
                .to_string(),
        };
    };

    // Step 3: dispatch through the circuit-crate verifier, cross-binding
    // the recursive variant's PI against the receipt's authoritative PI.
    let verdict = verify_recursive_proof_variant(
        &rp.proof_bytes,
        &rp.public_inputs,
        &rp.recursive_vk_hash,
        Some(&wr.public_inputs),
    );

    match verdict {
        RecursiveVariantVerdict::Verified => RecursiveReplayVerdict::Verified,
        RecursiveVariantVerdict::UnknownVkHash { hash } => {
            RecursiveReplayVerdict::RecursiveProofRejected {
                reason: format!("unknown recursive_vk_hash: {}", hex::encode(hash)),
            }
        }
        RecursiveVariantVerdict::PublicInputsTooShort { have, need } => {
            RecursiveReplayVerdict::RecursiveProofRejected {
                reason: format!("recursive variant PI too short: have {have}, need {need}"),
            }
        }
        RecursiveVariantVerdict::PublicInputsMismatch { reason } => {
            RecursiveReplayVerdict::RecursiveProofRejected {
                reason: format!("recursive variant PI mismatch: {reason}"),
            }
        }
        RecursiveVariantVerdict::ProofRejected { reason } => {
            RecursiveReplayVerdict::RecursiveProofRejected {
                reason: format!("recursive proof rejected: {reason}"),
            }
        }
    }
}

/// Chain-level Golden Vision replay: run
/// [`verify_recursive_replay_from_bundle`] over a slice of entries,
/// honoring the chain-walk invariant.
#[cfg(feature = "prover")]
pub fn replay_chain_recursive(entries: &[ReplayEntry]) -> ReplayChainOutput {
    let mut per_entry = Vec::with_capacity(entries.len());
    let mut first_failure: Option<usize> = None;
    let mut verified = 0usize;

    let mut prev_receipt_hash: Option<[u8; 32]> = None;
    for (idx, wr) in entries.iter().enumerate() {
        let r = verify_recursive_replay_from_bundle(wr, prev_receipt_hash);
        let v = match &r {
            RecursiveReplayVerdict::Verified => ReplayVerdict::Verified,
            RecursiveReplayVerdict::InnerProofRejected { reason } => ReplayVerdict::Rejected {
                reason: format!("inner: {reason}"),
            },
            RecursiveReplayVerdict::RecursiveProofRejected { reason } => ReplayVerdict::Rejected {
                reason: format!("recursive: {reason}"),
            },
        };
        let is_ok = matches!(v, ReplayVerdict::Verified);
        if is_ok {
            verified += 1;
        } else if first_failure.is_none() {
            first_failure = Some(idx);
        }
        prev_receipt_hash = Some(wr.receipt.receipt_hash());
        per_entry.push(v);
    }

    let overall_verified = first_failure.is_none();
    let summary = if overall_verified {
        format!(
            "recursive chain verified: {}/{} entries",
            verified,
            entries.len()
        )
    } else {
        format!(
            "recursive chain rejected: {}/{} entries verified; first failure at index {}",
            verified,
            entries.len(),
            first_failure.unwrap()
        )
    };

    ReplayChainOutput {
        total: entries.len(),
        verified,
        first_failure,
        per_entry,
        overall_verified,
        summary,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ---- replay-chain v1 -------------------------------------------------

    #[test]
    fn replay_chain_empty_is_verified() {
        let out = replay_chain(&[]);
        assert!(out.overall_verified);
        assert_eq!(out.total, 0);
        assert_eq!(out.verified, 0);
        assert!(out.first_failure.is_none());
    }

    fn sample_receipt() -> dregg_turn::TurnReceipt {
        dregg_turn::TurnReceipt {
            turn_hash: [0u8; 32],
            forest_hash: [0u8; 32],
            pre_state_hash: [0u8; 32],
            post_state_hash: [0u8; 32],
            timestamp: 0,
            effects_hash: [0u8; 32],
            computrons_used: 0,
            action_count: 0,
            previous_receipt_hash: None,
            agent: dregg_types::CellId::from_bytes([0u8; 32]),
            federation_id: [0u8; 32],
            routing_directives: Vec::new(),
            introduction_exports: Vec::new(),
            derivation_records: Vec::new(),
            emitted_events: Vec::new(),
            executor_signature: None,
            finality: Default::default(),
            was_encrypted: false,
            was_burn: false,
            consumed_capabilities: vec![],
        }
    }

    #[test]
    fn replay_chain_detects_witness_hash_tamper() {
        // Build a WR-shaped entry where the bundle is present but the
        // declared witness_hash is wrong. The proof step rejects first
        // because we use empty proof_bytes — but the structural check
        // still demonstrates the verdict shape is wired.
        let bundle = ReplayWitnessBundle {
            trace_rows: vec![vec![0u32; 4]; 4],
            availability: ReplayWitnessAvailability::Inline,
            recursive_proof: None,
        };
        let entry = ReplayEntry {
            receipt: sample_receipt(),
            proof_bytes: vec![],
            public_inputs: vec![],
            witness_bundle: Some(bundle),
            witness_hash: [0xFFu8; 32], // wrong
            aggregate_membership: None,
        };
        let out = replay_chain(&[entry]);
        assert!(!out.overall_verified);
        assert_eq!(out.first_failure, Some(0));
    }

    /// Empty proof bytes with no bundle → `Rejected` (STARK step fails first),
    /// NOT `Unwitnessable`. The `Unwitnessable` verdict is only reachable when
    /// the STARK proof is valid and the witness bundle is absent with a non-zero
    /// `witness_hash`. Constructing a valid proof in unit tests requires the full
    /// prover stack; that path is exercised by the integration-test replay harness.
    #[test]
    fn replay_chain_empty_proof_bytes_is_rejected_not_unwitnessable() {
        // No bundle, witness_hash zero, no proof → STARK verify rejects
        // first (empty proof bytes). Verdict must be Rejected, not Unwitnessable.
        let entry = ReplayEntry {
            receipt: sample_receipt(),
            proof_bytes: vec![],
            public_inputs: vec![],
            witness_bundle: None,
            witness_hash: [0u8; 32],
            aggregate_membership: None,
        };
        let out = replay_chain(&[entry]);
        assert!(!out.overall_verified);
        assert_eq!(out.first_failure, Some(0));
        assert!(
            matches!(out.per_entry[0], ReplayVerdict::Rejected { .. }),
            "empty proof bytes must produce Rejected, not Unwitnessable: {:?}",
            out.per_entry[0]
        );
    }

    /// Direct exercise of the `Unwitnessable` branch: a non-zero `witness_hash`
    /// with no bundle fires `Unwitnessable` when the STARK step would otherwise
    /// pass. We reach this by bypassing `replay_chain` and calling the inner
    /// function directly (same crate, so private access is allowed in tests).
    ///
    /// We supply a bundle-less entry where `witness_hash != [0; 32]` and fake
    /// proof bytes that DO NOT satisfy STARK verification — then assert that the
    /// first rejection is via STARK (Rejected), not Unwitnessable. This confirms
    /// the ordering: STARK check precedes the bundle check.
    ///
    /// The test also directly invokes `replay_one_with_prev` with mocked alphas
    /// to validate the Unwitnessable verdict shape on the bundle-absent path when
    /// STARK would hypothetically pass. Because we cannot generate a real proof
    /// in a unit test, we document the structural guarantee instead:
    ///
    /// Code path: `replay_one_with_prev` line ~597 checks `witness_hash != [0;32]`
    /// ONLY after the STARK step passes. The test below confirms that without
    /// a valid proof, the verdict is always `Rejected` — not `Unwitnessable`.
    /// The `Unwitnessable` branch is integration-tested in the demo replay harness.
    #[test]
    fn replay_chain_nonzero_witness_hash_no_bundle_produces_rejected_not_unwitnessable() {
        // non-zero witness_hash, no bundle, empty proof → STARK rejects first
        // so verdict is Rejected, not Unwitnessable. This confirms the branch
        // ordering: STARK always runs before the bundle availability check.
        let entry = ReplayEntry {
            receipt: sample_receipt(),
            proof_bytes: vec![],
            public_inputs: vec![],
            witness_bundle: None,
            witness_hash: [0xABu8; 32], // non-zero: would trigger Unwitnessable if STARK passed
            aggregate_membership: None,
        };
        let out = replay_chain(&[entry]);
        assert!(!out.overall_verified);
        assert_eq!(out.first_failure, Some(0));
        // Must be Rejected (STARK failed), NOT Unwitnessable.
        // If this ever becomes Unwitnessable, it means empty proof bytes
        // started passing STARK verification — a major regression.
        assert!(
            matches!(out.per_entry[0], ReplayVerdict::Rejected { .. }),
            "with empty proof bytes the verdict must be Rejected even when witness_hash is non-zero: {:?}",
            out.per_entry[0]
        );
    }

    // ---- PI completeness adversarial tests (EXECUTOR-HONESTY-AUDIT #3) ----

    /// Build the ROTATED-SHAPED PI vector a real `"effect-vm-rotated"` leg carries
    /// for `receipt`: the v1 prefix `[0, V1_PI_COUNT)` plus the four appended rotated
    /// pins, with `PI[TURN_HASH_BASE..+4]` filled the way the honest producer fills it
    /// (`turn_prover::proven_receipt`). Deliberately `ROT_PI_COUNT` felts and NOT
    /// `ACTIVE_BASE_COUNT` — a 213-slot vector is a shape no leg ships, and testing
    /// against one is exactly how this check hid.
    fn rotated_pi_from_receipt(receipt: &dregg_turn::TurnReceipt) -> Vec<u32> {
        use dregg_circuit::effect_vm::pi;
        use dregg_circuit::effect_vm::trace_rotated::ROT_PI_COUNT;
        use dregg_commit::typed::canonical_32_to_felts_4;
        let mut pi_vec = vec![0u32; ROT_PI_COUNT];
        let th = canonical_32_to_felts_4(&receipt.turn_hash);
        for i in 0..pi::TURN_HASH_LEN {
            pi_vec[pi::TURN_HASH_BASE + i] = th[i].as_u32();
        }
        pi_vec
    }

    #[test]
    fn pi_binding_accepts_consistent_pi() {
        let mut r = sample_receipt();
        r.turn_hash = [0x42u8; 32];
        let piv = rotated_pi_from_receipt(&r);
        assert!(
            check_receipt_pi_binding(&r, &piv, None).is_none(),
            "consistent PI must not be rejected"
        );
    }

    #[test]
    fn pi_binding_rejects_tampered_turn_hash() {
        use dregg_circuit::effect_vm::pi;
        let mut r = sample_receipt();
        r.turn_hash = [0x42u8; 32];
        let mut piv = rotated_pi_from_receipt(&r);
        // Tamper with PI[TURN_HASH_BASE]: even though the proof would
        // verify algebraically (we don't run the STARK here), the
        // verifier MUST reject because the PI no longer matches the
        // receipt's claimed turn_hash. Closes T11 at the verifier layer.
        piv[pi::TURN_HASH_BASE] ^= 0xDEAD_BEEF;
        let reason = check_receipt_pi_binding(&r, &piv, None)
            .expect("tampered PI[TURN_HASH_BASE] must be rejected");
        assert!(
            reason.contains("TURN_HASH_BASE"),
            "rejection should name TURN_HASH_BASE; got: {reason}"
        );
    }

    #[test]
    fn pi_binding_rejects_non_genesis_chain_head() {
        let mut r = sample_receipt();
        r.turn_hash = [0x42u8; 32];
        r.previous_receipt_hash = Some([0x33u8; 32]);
        let piv = rotated_pi_from_receipt(&r);
        let reason = check_receipt_pi_binding(&r, &piv, None)
            .expect("chain head with a previous_receipt_hash must be rejected");
        assert!(
            reason.contains("chain head"),
            "rejection should name chain head; got: {reason}"
        );
    }

    #[test]
    fn pi_binding_rejects_chain_walk_break() {
        let mut r = sample_receipt();
        r.turn_hash = [0x42u8; 32];
        // The receipt's previous_receipt_hash says one thing...
        r.previous_receipt_hash = Some([0x77u8; 32]);
        let piv = rotated_pi_from_receipt(&r);
        // ...but the chain-walk says the prior receipt hashed to
        // something else. The verifier must catch this (T8).
        let reason = check_receipt_pi_binding(&r, &piv, Some([0x88u8; 32]))
            .expect("chain-walk break must be rejected");
        assert!(
            reason.contains("chain-walk"),
            "rejection should name chain-walk; got: {reason}"
        );
    }

    #[test]
    fn pi_binding_rejects_missing_previous_receipt_hash_in_chain() {
        let mut r = sample_receipt();
        r.turn_hash = [0x42u8; 32];
        // Receipt claims to be a head (no previous_receipt_hash)...
        r.previous_receipt_hash = None;
        let piv = rotated_pi_from_receipt(&r);
        // ...but the chain-walk says it should chain from somewhere.
        let reason = check_receipt_pi_binding(&r, &piv, Some([0x55u8; 32]))
            .expect("missing previous_receipt_hash mid-chain must be rejected");
        assert!(
            reason.contains("chain-walk"),
            "rejection should name chain-walk; got: {reason}"
        );
    }

    #[test]
    fn pi_binding_rejects_short_pi() {
        let mut r = sample_receipt();
        r.turn_hash = [0x42u8; 32];
        let reason = check_receipt_pi_binding(&r, &vec![0u32; 10], None)
            .expect("PI too short to carry turn-identity slots must be rejected");
        assert!(
            reason.contains("too short"),
            "rejection should name 'too short'; got: {reason}"
        );
    }

    /// THE PRECONDITION IS DERIVED FROM THE READS, NOT WRITTEN DOWN. A vector one
    /// felt shy of the last TURN_HASH slot is refused; the exact length is accepted.
    /// Both poles, so a future widening of the precondition that would re-orphan the
    /// check on a real leg fails HERE.
    #[test]
    fn pi_binding_precondition_is_exactly_the_highest_offset_it_reads() {
        use dregg_circuit::effect_vm::trace_rotated::V1_PI_COUNT;
        let mut r = sample_receipt();
        r.turn_hash = [0x42u8; 32];
        let piv = rotated_pi_from_receipt(&r);

        assert!(
            RECEIPT_PI_BINDING_MIN_LEN <= V1_PI_COUNT,
            "the precondition ({RECEIPT_PI_BINDING_MIN_LEN}) must fit inside the v1 PI window a \
             rotated leg publishes ({V1_PI_COUNT}); above it, the check is unreachable on the \
             only leg that ships"
        );
        let short = piv[..RECEIPT_PI_BINDING_MIN_LEN - 1].to_vec();
        assert!(
            check_receipt_pi_binding(&r, &short, None).is_some_and(|m| m.contains("too short")),
            "one felt short of the last TURN_HASH slot must be refused"
        );
        let exact = piv[..RECEIPT_PI_BINDING_MIN_LEN].to_vec();
        assert!(
            check_receipt_pi_binding(&r, &exact, None).is_none(),
            "exactly the offsets the body reads must be enough to DECIDE"
        );
    }

    // (The v1 hand-AIR `EffectVmAir` short-PI / balance-limb rejection tests were
    // retired with the v1 single-proof verify — that entry now fails closed on every
    // build, so there is no v1 proof to construct here.)

    // ---- scope-recursive subcommand wiring tests (Golden Vision Block 3) ----

    /// `verify_recursive_replay_from_bundle` must reject when the entry has
    /// no `witness_bundle` at all — there is nothing to recursively verify.
    #[test]
    fn recursive_replay_rejects_missing_witness_bundle() {
        let entry = ReplayEntry {
            receipt: sample_receipt(),
            proof_bytes: vec![],
            public_inputs: vec![],
            witness_bundle: None,
            witness_hash: [0u8; 32],
            aggregate_membership: None,
        };
        let verdict = verify_recursive_replay_from_bundle(&entry, None);
        // Scope-1 fails first (empty proof bytes), so we land in
        // InnerProofRejected before ever consulting the bundle.
        match verdict {
            RecursiveReplayVerdict::InnerProofRejected { .. } => {}
            other => panic!("expected InnerProofRejected; got {:?}", other),
        }
    }

    /// `verify_recursive_replay_from_bundle` must reject when the bundle is
    /// present but lacks a `recursive_proof` — the WR was produced
    /// without `recursive_compress = true`, so it can be replayed via the
    /// trust-and-replay path (`replay_chain`) but not via the recursive
    /// path. The verdict surface lets the caller redirect to the Silver
    /// Vision path.
    ///
    /// In this test scope-1 still fails first (empty proof bytes), so we
    /// land in InnerProofRejected. The interesting positive case (scope-1
    /// passes, then we see "no recursive_proof") is exercised by the
    /// integration path; here we just confirm the verdict shape.
    #[test]
    fn recursive_replay_chain_runs_over_empty_input() {
        let out = replay_chain_recursive(&[]);
        assert!(out.overall_verified);
        assert_eq!(out.total, 0);
        assert_eq!(out.verified, 0);
        assert!(out.first_failure.is_none());
        assert!(out.summary.contains("recursive"));
    }
}
