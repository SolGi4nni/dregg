//! THE LIGHT CLIENT IN THE TAB (N12) — `#[wasm_bindgen]` over
//! `dregg-lightclient::verify_history`.
//!
//! `docs/design-frontiers/WEB-FORWARD.md §8 S4`. The anti-pale-ghost tooth: a
//! browser can fold a whole finalized history into ONE succinct recursive
//! aggregate and verify it RE-WITNESSING NOTHING — the executable counterpart of
//! `Dregg2.Circuit.RecursiveAggregation.light_client_verifies_whole_history`.
//!
//! Four entry points, all honest about the VK trust anchor:
//!
//! - [`light_client_demo`] — fold a real K-turn chain IN THE TAB (each turn's
//!   post-state is the next's pre-state; each leaf is a REAL Lean-descriptor
//!   EffectVM proof verified in-circuit) and light-verify it. This is the SETUP
//!   side that SELF-ANCHORS (the VK fingerprint is minted from the locally
//!   produced fold — exactly how an honest setup mints the anchor it then
//!   distributes). It proves the whole pipeline runs in wasm32; "verify the whole
//!   history yourself" becomes tactile.
//! - [`genesis_vk_anchor`] — return the CONFIG anchor (the root-circuit VK
//!   fingerprint, hex) for a given window shape. This models the anchor a
//!   genesis/checkpoint configuration distributes — the trust input a verifier
//!   holds SEPARATELY from any artifact. (It is minted here from a local honest
//!   fold of that shape, exactly how a setup party mints the anchor it ships.)
//! - [`verify_history_against_anchor`] — the CONFIG-NOT-ARTIFACT tooth made
//!   tactile: fold a real chain, then run the REAL [`dregg_lightclient::verify_history`]
//!   against a VK anchor SUPPLIED BY THE CALLER (the config), NOT self-anchored
//!   from `agg.root_vk_fingerprint()`. A correct config anchor attests; a tampered
//!   anchor is REFUSED with the genuine `VkFingerprintMismatch` — "you did not
//!   trust the server, you CHECKED it against your own configured anchor."
//! - [`produce_external_history_envelope`] — the PRODUCER: fold a real chain and
//!   emit the [`ExternalHistoryEnvelope`] JSON with `proof_bytes_b64` populated
//!   from the proof's versioned byte envelope
//!   ([`dregg_circuit_prove::ivc_turn_chain::WholeChainProofBytes`]). The whole
//!   round-trip (fold → serialize → bytes → deserialize → verify) runs in-tab.
//! - [`verify_devnet_history`] — verify an EXTERNALLY-produced aggregate
//!   (a versioned envelope of proof bytes + carried publics) against a
//!   CONFIG-pinned VK anchor (the anchor a SEPARATE argument, NEVER read off the
//!   envelope under verification — the light-client invariant). The byte-verify
//!   path is CLOSED: this entry base64-decodes `proof_bytes`, decodes the byte
//!   envelope, and runs the REAL recursion verify over the wire (the three teeth)
//!   via [`dregg_lightclient::verify_history_bytes`], re-witnessing nothing.
//!
//! HONEST SCOPE (the project law): this carries the light client's NAMED floor —
//! `recursive_sound` (the recursion fork's FRI engine soundness) — surfaced in the
//! UI, NOT hidden. The verification IS the trust: IF the aggregate verifies (engine
//! sound), THEN the whole history is attested.

use serde::Serialize;
use wasm_bindgen::prelude::*;

/// The whole-history attestation a light client obtains — the JS view of
/// `dregg_lightclient::AttestedHistory`. Holding it means: *every one of
/// `num_turns` finalized turns executed correctly, in order, from `genesis_root`
/// to `final_root`, and `chain_digest` commits to that exact ordered history* —
/// and the tab re-executed nothing.
#[derive(Clone, Debug, Serialize)]
pub struct AttestedHistoryView {
    /// Whether the aggregate verified (the headline). On a real verify failure
    /// this is the engine REJECTING the proof — no attestation granted.
    pub attested: bool,
    /// The 8-felt (~124-bit faithful) genesis state anchor (decimal felts).
    pub genesis_root: Vec<u32>,
    /// The 8-felt final state anchor — the genuine fold of the whole history (decimal felts).
    pub final_root: Vec<u32>,
    /// The multi-felt Poseidon2 digest committing to the ORDERED `(old_root, new_root)`
    /// pairs (decimal felts) — distinct histories with the same endpoints still differ.
    pub chain_digest: Vec<u32>,
    /// How many finalized turns the attested history folds. The light client
    /// learns ALL of them executed correctly without seeing any.
    pub num_turns: usize,
    /// The proof-system identifier + the honest named floor, for the UI.
    pub engine: String,
    /// The named soundness floor (surfaced, not hidden).
    pub named_floor: String,
}

/// **THE IN-TAB LIGHT CLIENT** — fold a real `k`-turn chain in wasm32 and
/// light-verify it, re-witnessing nothing.
///
/// Each turn debits `step` from a running balance; each leaf is a REAL
/// Lean-descriptor EffectVM proof (`prove_vm_descriptor`, the audited p3 batch
/// prover — the same wire artifact the SDK cutover emits) verified in-circuit by
/// the recursion wrap. The fold is the expensive step (done once); the
/// light-client verify is the cheap step. SELF-ANCHORS: the VK fingerprint is
/// minted from the locally produced fold (the honest setup mint).
///
/// `k` is clamped to `[2, 4]` — the recursive chain-binding folds the temporal
/// `new_root[i] == old_root[i+1]` tooth, so it needs AT LEAST 2 turns; and
/// recursive proving in a browser is heavy, so a small chain keeps the demo
/// responsive while exercising the REAL pipeline end-to-end.
///
/// Returns an [`AttestedHistoryView`]. Errors only on an internal substrate bug
/// (a chain that should fold but doesn't), which the caller surfaces honestly.
#[wasm_bindgen]
pub fn light_client_demo(k: usize, step: u64) -> Result<JsValue, JsError> {
    // Fold + light-verify (the SETUP-side self-anchor: the VK fingerprint is
    // minted from the locally produced fold, then verify_history checks the
    // aggregate against it — re-witnessing nothing).
    let (_agg, attested) = fold_demo_chain(k, step)?;

    let view = AttestedHistoryView {
        attested: true,
        genesis_root: attested.genesis_root.iter().map(|d| d.as_u32()).collect(),
        final_root: attested.final_root.iter().map(|d| d.as_u32()).collect(),
        chain_digest: attested.chain_digest.iter().map(|d| d.as_u32()).collect(),
        num_turns: attested.num_turns,
        engine: "recursive-stark (plonky3 fork) · descriptor-leaf EffectVM".to_string(),
        named_floor: "named floor: recursive_sound (FRI engine soundness) + the two \
                      ivc_turn_chain fork follow-ups — the verification IS the trust"
            .to_string(),
    };
    serde_wasm_bindgen::to_value(&view).map_err(|e| JsError::from(e))
}

/// Fold a real `k`-turn chain (the same shape [`light_client_demo`] folds) and
/// return its root-circuit **VK fingerprint** as hex — the CONFIG TRUST ANCHOR a
/// genesis/checkpoint configuration distributes.
///
/// The fingerprint is a function of the root circuit SHAPE (window size + leaf
/// trace heights), NOT of the folded history's content — two different `k`-turn
/// histories of the same shape fingerprint identically (the load-bearing anchor
/// property, proven in `dregg-lightclient`'s `vk_anchor_is_circuit_shape_not_
/// history_content`). So this is exactly the value an honest setup mints ONCE and
/// ships in config; a verifier then holds it SEPARATELY from any artifact and
/// checks every aggregate of that shape against it.
///
/// `k` is clamped to `[2, 4]` (same as the demo). Returns the 64-char hex anchor.
#[wasm_bindgen]
pub fn genesis_vk_anchor(k: usize, step: u64) -> Result<String, JsError> {
    let (agg, _attested) = fold_demo_chain(k, step)?;
    Ok(agg.root_vk_fingerprint().to_hex())
}

/// **THE CONFIG-NOT-ARTIFACT TOOTH** — fold a real chain, then run the REAL
/// [`dregg_lightclient::verify_history`] against a VK anchor SUPPLIED BY THE
/// CALLER (the config), never self-anchored from the artifact.
///
/// This is the in-tab realization of the light-client invariant: the trust anchor
/// is genesis/checkpoint CONFIGURATION, read from `anchor_hex` (a separate input
/// the user controls), and is NEVER taken from `agg.root_vk_fingerprint()`. The
/// REAL `verify_history` runs its three teeth (the VK pin against `anchor_hex`,
/// the carried-publics attestation against the binding proof, the root verify) —
/// re-witnessing nothing.
///
/// - A CORRECT config anchor (e.g. from [`genesis_vk_anchor`] of the same shape)
///   → `attested: true`, the genuine whole-history verdict.
/// - A TAMPERED/wrong anchor → `attested: false` with the genuine
///   `VkFingerprintMismatch` reason in `named_floor` (the engine REFUSING to trust
///   a proof of a DIFFERENT circuit) — "you did not trust the server, you CHECKED
///   it against your own anchor."
///
/// `anchor_hex` must be 64 hex chars (32 bytes). `k` is clamped to `[2, 4]`.
#[wasm_bindgen]
pub fn verify_history_against_anchor(
    k: usize,
    step: u64,
    anchor_hex: &str,
) -> Result<JsValue, JsError> {
    use dregg_circuit_prove::ivc_turn_chain::RecursionVk;
    use dregg_lightclient::{LightClientError, verify_history};

    // Parse the CONFIG anchor from the caller (never from the artifact).
    let anchor_bytes = parse_hex32(anchor_hex)
        .map_err(|e| JsError::new(&format!("config VK anchor parse failed: {e}")))?;
    let anchor = RecursionVk(anchor_bytes);

    // Fold the real chain (the expensive setup step the producer ran once).
    let (agg, _self_attested) = fold_demo_chain(k, step)?;

    // The REAL light-client check against the CONFIG anchor (not self-anchored).
    match verify_history(&agg, &anchor) {
        Ok(attested) => {
            let view = AttestedHistoryView {
                attested: true,
                genesis_root: attested.genesis_root.iter().map(|d| d.as_u32()).collect(),
                final_root: attested.final_root.iter().map(|d| d.as_u32()).collect(),
                chain_digest: attested.chain_digest.iter().map(|d| d.as_u32()).collect(),
                num_turns: attested.num_turns,
                engine: "recursive-stark (plonky3 fork) · descriptor-leaf EffectVM".to_string(),
                named_floor: "verified against a CONFIG-SUPPLIED anchor (not self-anchored): \
                              the VK pin + carried-publics attestation + root verify all held. \
                              named floor: recursive_sound (FRI engine soundness)"
                    .to_string(),
            };
            serde_wasm_bindgen::to_value(&view).map_err(JsError::from)
        }
        Err(LightClientError::AggregateInvalid(e)) => {
            // The engine REFUSED. Carry the genuine reason (a VkFingerprintMismatch
            // for a wrong anchor is the from-scratch-prover tooth firing — NO
            // attestation granted). We do not launder a refusal as success.
            let view = AttestedHistoryView {
                attested: false,
                genesis_root: Vec::new(),
                final_root: Vec::new(),
                chain_digest: Vec::new(),
                num_turns: 0,
                engine: "recursive-stark (plonky3 fork)".to_string(),
                named_floor: format!(
                    "REFUSED against the supplied config anchor: {e} — the anchor is config, \
                     NOT read from the artifact, so a wrong/tampered anchor cannot be laundered \
                     into an attestation"
                ),
            };
            serde_wasm_bindgen::to_value(&view).map_err(JsError::from)
        }
    }
}

/// The wasm-side **versioned external-aggregate envelope** — the JSON/paste-UX
/// transport a node/relayer serializes a `WholeChainProof` into and a tab
/// deserializes. It is the OUTER wrapper: `proof_bytes_b64` is the base64 of the
/// circuit's INNER versioned byte envelope
/// ([`dregg_circuit_prove::ivc_turn_chain::WholeChainProofBytes`]), which carries the
/// verify-sufficient subset of the proof (the root `BatchStarkProof`, the binding
/// `Proof`, the four publics) — everything the recursion verify reads, and nothing
/// of the prover-only `root.1`.
///
/// - `vk_fingerprint_hex` rides as the producer's CLAIM, NEVER trusted from here —
///   the verifier compares it to its OWN configured anchor and, crucially, re-pins
///   the anchor from the proof bytes during the real verify. (Carrying it lets the
///   client give a precise "your config anchor ≠ the one this aggregate was built
///   for" diagnostic without trusting it.)
/// - `genesis_root` / `final_root` / `num_turns` / `chain_digest` are the carried
///   public commitments — the same four the recursion verify re-attests against the
///   binding proof (a relabeled value is refused at tooth 2).
/// - `version` pins the OUTER envelope format.
#[derive(serde::Deserialize, serde::Serialize)]
pub struct ExternalHistoryEnvelope {
    /// Envelope format version (current: 1).
    pub version: u32,
    /// The producer's CLAIMED root-circuit VK fingerprint (hex). NEVER trusted
    /// from the envelope — compared to the client's configured anchor AND re-pinned
    /// from the proof bytes during verify.
    pub vk_fingerprint_hex: String,
    /// Base64 of the proof's inner versioned byte envelope
    /// ([`dregg_circuit_prove::ivc_turn_chain::WholeChainProofBytes`]). Populated by
    /// [`produce_external_history_envelope`]; an empty value fails closed at verify
    /// (nothing to cryptographically check).
    #[serde(default)]
    pub proof_bytes_b64: String,
    /// Carried public commitment: the 8-felt genesis state anchor (decimal felts).
    pub genesis_root: Vec<u32>,
    /// Carried public commitment: the 8-felt final state anchor (decimal felts).
    pub final_root: Vec<u32>,
    /// Carried public commitment: the multi-felt ordered-history digest (decimal felts).
    pub chain_digest: Vec<u32>,
    /// Carried public commitment: how many finalized turns the aggregate folds.
    pub num_turns: usize,
    /// **LC-3 — the finality certificate (artifact side).** The producer's BFT finality cert over
    /// the head root: the signed ratification votes a quorum cast. `None` for a legacy
    /// legs-1+2-only envelope (which [`verify_finalized_devnet_history`] then refuses as
    /// un-finalized). The verifier checks these votes against its OWN configured committee (a
    /// separate argument, never read from here) — so a fabricated cert by foreign keys is rejected.
    #[serde(default)]
    pub finality_cert: Option<FinalityCertJson>,
}

/// A finality certificate as it rides in the [`ExternalHistoryEnvelope`] (artifact side). The
/// verifier reconstructs a [`dregg_lightclient::FinalityCert`] from it and checks it against the
/// client's CONFIG committee — the keys here are the producer's CLAIM, never trusted on their own.
#[derive(serde::Deserialize, serde::Serialize, Clone, Debug)]
pub struct FinalityCertJson {
    /// The ratifying votes (each a 64-hex validator key + a 128-hex Ed25519 signature).
    pub votes: Vec<FinalityVoteJson>,
    /// The group size the producer claims the supermajority was taken over (diagnostic only — the
    /// verifier anchors the threshold to its OWN committee size, never this field).
    pub participant_count: usize,
    /// The head state root (lane-0 felt, decimal) the cert claims a quorum finalized. Must equal the
    /// aggregate's proven head for the seam to bind.
    pub finalized_root: u32,
}

/// One ratification vote in a [`FinalityCertJson`].
#[derive(serde::Deserialize, serde::Serialize, Clone, Debug)]
pub struct FinalityVoteJson {
    /// The validator's Ed25519 verifying key (64 hex chars / 32 bytes).
    pub validator_hex: String,
    /// The Ed25519 signature over `finality_signing_message(finalized_root, participant_count)`
    /// (128 hex chars / 64 bytes).
    pub signature_hex: String,
    /// The voter's ML-DSA-65 public key (FIPS 204, 1952 bytes → 3904 hex chars), carried
    /// SELF-CONTAINED so the post-quantum half of the HYBRID vote is re-verifiable in-tab with no
    /// committee PQ-key history — the client half of the end-to-end-PQ perimeter. `#[serde(default)]`
    /// so a legacy classical-only envelope still parses; it then reconstructs an empty PQ half, which
    /// the light client's hybrid gate REJECTS (fail-closed — never a silent ed25519-only accept).
    #[serde(default)]
    pub ml_dsa_pubkey_hex: String,
    /// The ML-DSA-65 (FIPS 204) signature over the SAME `finality_signing_message` the Ed25519 half
    /// signs, bound to `dregg_lightclient::HYBRID_PQ_CTX`. `#[serde(default)]` for legacy envelopes;
    /// a missing/empty half fails the hybrid check closed.
    #[serde(default)]
    pub pq_signature_hex: String,
}

/// **VERIFY AN EXTERNAL HISTORY against a config-pinned VK anchor** — the real
/// remote-verifier shape, over the versioned [`ExternalHistoryEnvelope`].
///
/// In the production shape the aggregate is produced by whoever ran the history
/// (a node, a relayer), serialized into the envelope, fetched by the tab, and
/// verified against the client's genesis/checkpoint VK anchor — which arrives as a
/// SEPARATE argument (`config_anchor_hex`) and is NEVER read off the envelope under
/// verification (the light-client invariant).
///
/// What this enforces (real, not faked):
/// 1. parse + version-check the envelope;
/// 2. parse the SEPARATE `config_anchor_hex` (the client's own configured anchor);
/// 3. the **anchor-discipline pre-check**: the envelope's claimed fingerprint is
///    compared to the configured anchor — a mismatch is REFUSED here (the precise
///    "this aggregate was built for a different circuit than your config pins"
///    diagnostic), and the claimed value is otherwise discarded, never trusted;
/// 4. base64-decode `proof_bytes`, decode the inner byte envelope, and run the
///    REAL recursion verify (the three teeth) against the config anchor — a
///    tampered proof, a foreign circuit, or a relabeled public is refused.
///
/// THE BYTE PATH (closed): `proof_bytes_b64` carries the base64 of the proof's
/// versioned byte envelope ([`dregg_circuit_prove::ivc_turn_chain::WholeChainProofBytes`]),
/// produced by [`produce_external_history_envelope`]. The whole [`WholeChainProof`]
/// is not byte-encodable — its `root.1` (`Rc<CircuitProverData>`) is prover-only —
/// but the VERIFY-sufficient subset (the root `BatchStarkProof`, the binding
/// `Proof`, the four publics) IS, and the verifier never reads `root.1`. So this
/// entry decodes the bytes and runs the REAL recursion verify over the wire via
/// [`dregg_lightclient::verify_history_bytes`], re-witnessing nothing.
#[wasm_bindgen]
pub fn verify_devnet_history(
    envelope_json: &str,
    config_anchor_hex: &str,
) -> Result<JsValue, JsError> {
    use base64::Engine as _;
    use dregg_circuit_prove::ivc_turn_chain::RecursionVk;
    use dregg_lightclient::{LightClientError, verify_history_bytes};

    // (1) Parse + version-check the envelope.
    let env: ExternalHistoryEnvelope = serde_json::from_str(envelope_json)
        .map_err(|e| JsError::new(&format!("envelope parse failed: {e}")))?;
    if env.version != 1 {
        return Err(JsError::new(&format!(
            "unsupported envelope version {} (this client speaks v1)",
            env.version
        )));
    }

    // (2) Parse the SEPARATE config anchor (the client's own — NOT from the envelope).
    let cfg_bytes = parse_hex32(config_anchor_hex)
        .map_err(|e| JsError::new(&format!("config VK anchor parse failed: {e}")))?;
    let anchor = RecursionVk(cfg_bytes);

    // (3) The anchor-discipline pre-check: the envelope's CLAIMED fingerprint is
    // compared to the CONFIGURED anchor; the claim is never trusted, only used to
    // give a precise diagnostic. A mismatch is refused here (a from-scratch prover
    // that built a DIFFERENT circuit cannot pass the client's anchor) — the REAL
    // recursion verify in (5) re-pins the anchor from the proof bytes regardless,
    // so this is a fast-path diagnostic, not the soundness boundary.
    let claimed_bytes = parse_hex32(&env.vk_fingerprint_hex)
        .map_err(|e| JsError::new(&format!("envelope claimed fingerprint malformed: {e}")))?;
    if claimed_bytes != cfg_bytes {
        let view = AttestedHistoryView {
            attested: false,
            genesis_root: env.genesis_root.clone(),
            final_root: env.final_root.clone(),
            chain_digest: env.chain_digest.clone(),
            num_turns: env.num_turns,
            engine: "recursive-stark (plonky3 fork)".to_string(),
            named_floor: format!(
                "REFUSED at the anchor-discipline check: the envelope was built for circuit \
                 {} but your configured anchor pins {} — the anchor is YOUR config (a separate \
                 input), never read from the artifact, so a mismatch is refused outright",
                env.vk_fingerprint_hex, config_anchor_hex
            ),
        };
        return serde_wasm_bindgen::to_value(&view).map_err(JsError::from);
    }

    // (4) The proof bytes must be present for the cryptographic verify.
    if env.proof_bytes_b64.is_empty() {
        let view = AttestedHistoryView {
            attested: false,
            genesis_root: env.genesis_root.clone(),
            final_root: env.final_root.clone(),
            chain_digest: env.chain_digest.clone(),
            num_turns: env.num_turns,
            engine: "recursive-stark (plonky3 fork)".to_string(),
            named_floor: "REFUSED: the envelope carries no proof_bytes — the anchor discipline \
                          passed, but there is nothing to cryptographically verify (fail-closed). \
                          A producer must call produce_external_history_envelope to populate it."
                .to_string(),
        };
        return serde_wasm_bindgen::to_value(&view).map_err(JsError::from);
    }
    let proof_bytes = base64::engine::general_purpose::STANDARD
        .decode(env.proof_bytes_b64.as_bytes())
        .map_err(|e| JsError::new(&format!("proof_bytes_b64 is not valid base64: {e}")))?;

    // (5) THE REAL OVER-WIRE VERIFY. Decode the byte envelope and run the three
    // teeth (VK pin against the CONFIG anchor, carried-publics attestation against
    // the binding proof, root batch verify) — re-witnessing nothing. The anchor is
    // the config (a separate argument), never read from the artifact.
    match verify_history_bytes(&proof_bytes, &anchor) {
        Ok(attested) => {
            let view = AttestedHistoryView {
                attested: true,
                genesis_root: attested.genesis_root.iter().map(|d| d.as_u32()).collect(),
                final_root: attested.final_root.iter().map(|d| d.as_u32()).collect(),
                chain_digest: attested.chain_digest.iter().map(|d| d.as_u32()).collect(),
                num_turns: attested.num_turns,
                engine: "recursive-stark (plonky3 fork) · descriptor-leaf EffectVM".to_string(),
                named_floor: "verified OVER THE WIRE against a CONFIG-supplied anchor: the byte \
                              envelope decoded, the VK pin + carried-publics attestation + root \
                              verify all held. named floor: recursive_sound (FRI engine soundness)"
                    .to_string(),
            };
            serde_wasm_bindgen::to_value(&view).map_err(JsError::from)
        }
        Err(LightClientError::AggregateInvalid(e)) => {
            // The engine REFUSED the bytes (tamper, wrong circuit, malformed
            // envelope). We carry the genuine reason; no attestation is laundered.
            let view = AttestedHistoryView {
                attested: false,
                genesis_root: env.genesis_root,
                final_root: env.final_root,
                chain_digest: env.chain_digest.clone(),
                num_turns: env.num_turns,
                engine: "recursive-stark (plonky3 fork)".to_string(),
                named_floor: format!(
                    "REFUSED at the over-wire recursion verify: {e} — the byte envelope was \
                     decoded and checked against YOUR config anchor; a tampered proof or a \
                     proof of a different circuit cannot be laundered into an attestation"
                ),
            };
            serde_wasm_bindgen::to_value(&view).map_err(JsError::from)
        }
    }
}

/// **LC-3 — THE FINALIZED OVER-WIRE LIGHT-CLIENT CHECK.** The same byte-path verify as
/// [`verify_devnet_history`] (legs 1+2: the aggregate is genuine, the publics are re-attested),
/// PLUS the THIRD leg — finality — that the bare wasm client lacked: the head root the aggregate
/// proves was QUORUM-FINALIZED by the client's TRUSTED committee.
///
/// Without this leg a *correct-looking* history is indistinguishable from a *finalized* one: an
/// equivocating prover can fold a perfectly valid aggregate over a FORK the network never finalized
/// (legs 1+2 pass). This entry runs the Rust embodiment of
/// `FinalizedLightClient.light_client_accepts_finalized_history`'s third leg over the wire — the
/// composition `verify_finalized_history` performs, realized for the byte path where the in-memory
/// `WholeChainProof` is unavailable (only its publics are, which tooth 2 just re-attested):
///
/// 1. byte-verify the aggregate against the CONFIG anchor (legs 1+2, exactly [`verify_devnet_history`]);
/// 2. the **root seam**: the envelope's finality cert finalizes the SAME head felt the aggregate proves;
/// 3. the **committee-anchored quorum**: a supermajority of the TRUSTED `committee_hex_csv` (the
///    client's CONFIG validator set — a separate argument, NEVER read from the envelope) cast a
///    verifying Ed25519 vote over the head root. The threshold is taken over the committee size, not
///    the cert-supplied `participant_count` — closing red-team LC-2/LC-3.
///
/// `committee_hex_csv` is a comma-separated list of 64-hex ed25519 validator keys.
/// `ml_dsa_committee_hex_csv` is the PARALLEL comma-separated list of the committee's genesis-ENROLLED
/// ML-DSA-65 (FIPS 204) public keys (3904 hex chars / 1952 bytes each), aligned index-for-index with
/// `committee_hex_csv` and sourced from the SAME genesis/epoch config — the GAP #0 pin's enrolled PQ
/// roster (NEVER the votes' self-carried keys). Pass an EMPTY string for the staged-rollout
/// fail-closed case: an absent or misaligned roster counts NO signer, so leg 3 refuses the hybrid
/// quorum (a refusal, never a silent ed25519-only downgrade). An empty committee, a missing finality
/// cert, a seam break, or a sub-quorum (e.g. a fork signed by foreign keys) all yield
/// `attested: false` with the precise reason — NO finalized attestation is laundered.
#[wasm_bindgen]
pub fn verify_finalized_devnet_history(
    envelope_json: &str,
    config_anchor_hex: &str,
    committee_hex_csv: &str,
    ml_dsa_committee_hex_csv: &str,
) -> Result<JsValue, JsError> {
    use base64::Engine as _;
    use dregg_circuit_prove::ivc_turn_chain::RecursionVk;
    use dregg_lightclient::{LightClientError, verify_history_bytes};

    // (1) Parse + version-check the envelope.
    let env: ExternalHistoryEnvelope = serde_json::from_str(envelope_json)
        .map_err(|e| JsError::new(&format!("envelope parse failed: {e}")))?;
    if env.version != 1 {
        return Err(JsError::new(&format!(
            "unsupported envelope version {} (this client speaks v1)",
            env.version
        )));
    }

    // (2) Parse the SEPARATE config anchor + the SEPARATE config committee (both the client's own).
    let cfg_bytes = parse_hex32(config_anchor_hex)
        .map_err(|e| JsError::new(&format!("config VK anchor parse failed: {e}")))?;
    let anchor = RecursionVk(cfg_bytes);
    let committee = parse_committee_csv(committee_hex_csv)
        .map_err(|e| JsError::new(&format!("config committee parse failed: {e}")))?;

    // THE ENROLLED ML-DSA ROSTER — GAP #0 pin. The hybrid finality gate requires the committee's
    // genesis-ENROLLED ML-DSA-65 keys, aligned index-for-index with `committee`, sourced from
    // config EXACTLY like the ed25519 committee above (a separate trusted input) and NEVER
    // assembled from the cert's self-carried per-vote keys (that self-carry hole IS GAP #0: a
    // quantum adversary who breaks ed25519 for a validator could otherwise substitute its own
    // ML-DSA key). This boundary now THREADS that enrolled roster: `ml_dsa_committee_hex_csv`
    // carries the committee's ML-DSA-65 public keys from the SAME genesis/epoch config the ed25519
    // committee comes from, parsed here into the index-for-index roster that
    // `distinct_committee_signers`/`has_committee_quorum` pin each signer's carried PQ key against.
    // A misaligned roster (count ≠ committee.len(), e.g. the empty staged-rollout string) still
    // counts ZERO signers, so leg 3 refuses the hybrid quorum — a refusal, NOT a silent
    // ed25519-only downgrade.
    let ml_dsa_committee = parse_ml_dsa_committee_csv(ml_dsa_committee_hex_csv)
        .map_err(|e| JsError::new(&format!("config ML-DSA committee parse failed: {e}")))?;

    // (3) Anchor-discipline pre-check (same as verify_devnet_history): claim vs config.
    let claimed_bytes = parse_hex32(&env.vk_fingerprint_hex)
        .map_err(|e| JsError::new(&format!("envelope claimed fingerprint malformed: {e}")))?;
    if claimed_bytes != cfg_bytes {
        return finalized_refusal(
            &env,
            format!(
                "REFUSED at the anchor-discipline check: the envelope was built for circuit {} but \
                 your configured anchor pins {}",
                env.vk_fingerprint_hex, config_anchor_hex
            ),
        );
    }
    if env.proof_bytes_b64.is_empty() {
        return finalized_refusal(
            &env,
            "REFUSED: the envelope carries no proof_bytes — nothing to cryptographically verify \
             (fail-closed)."
                .to_string(),
        );
    }
    let proof_bytes = base64::engine::general_purpose::STANDARD
        .decode(env.proof_bytes_b64.as_bytes())
        .map_err(|e| JsError::new(&format!("proof_bytes_b64 is not valid base64: {e}")))?;

    // (4) Legs 1+2 — the REAL over-wire aggregate verify against the CONFIG anchor.
    let attested = match verify_history_bytes(&proof_bytes, &anchor) {
        Ok(a) => a,
        Err(LightClientError::AggregateInvalid(e)) => {
            return finalized_refusal(
                &env,
                format!("REFUSED at the over-wire recursion verify (legs 1+2): {e}"),
            );
        }
    };

    // (5) Leg 3 — finality. The cert must be present and certify the proven head with a committee
    // supermajority. The proven head is lane 0 of the byte-verified final anchor.
    let Some(cert_json) = env.finality_cert.clone() else {
        return finalized_refusal(
            &env,
            "REFUSED: legs 1+2 verified, but the envelope carries NO finality certificate — a \
             correct-looking history is not a finalized one (it could be an equivocating fork). No \
             finalized attestation."
                .to_string(),
        );
    };
    let cert = match reconstruct_finality_cert(&cert_json) {
        Ok(c) => c,
        Err(e) => return finalized_refusal(&env, format!("REFUSED: malformed finality cert: {e}")),
    };
    let proven_head = attested.final_root[0].as_u32();
    if let Err(reason) = finality_leg(proven_head, &cert, &committee, &ml_dsa_committee) {
        return finalized_refusal(
            &env,
            format!("REFUSED at the finality leg (leg 3): {reason}"),
        );
    }

    let signers = cert.distinct_committee_signers(&committee, &ml_dsa_committee);
    let view = AttestedHistoryView {
        attested: true,
        genesis_root: attested.genesis_root.iter().map(|d| d.as_u32()).collect(),
        final_root: attested.final_root.iter().map(|d| d.as_u32()).collect(),
        chain_digest: attested.chain_digest.iter().map(|d| d.as_u32()).collect(),
        num_turns: attested.num_turns,
        engine: "recursive-stark (plonky3 fork) · descriptor-leaf EffectVM".to_string(),
        named_floor: format!(
            "FINALIZED over the wire: legs 1+2 (aggregate + publics) held against your CONFIG \
             anchor, AND leg 3 — {signers} of your {} trusted committee members ratified the \
             proven head root. named floor: recursive_sound (FRI engine soundness)",
            committee.len()
        ),
    };
    serde_wasm_bindgen::to_value(&view).map_err(JsError::from)
}

/// The pure finality leg (host-testable, no `JsValue`): the root seam + the COMMITTEE-ANCHORED
/// quorum, mirroring `dregg_lightclient::verify_finalized_history`'s legs 2+3 for the byte path.
/// `proven_head` is lane 0 of the byte-verified final anchor (what tooth 2 re-attested). Returns the
/// distinct trusted-committee signer count on success, or a precise refusal reason.
///
/// `ml_dsa_committee` is the client's TRUSTED, genesis-ENROLLED ML-DSA-65 roster, aligned
/// index-for-index with `committee` (config, exactly like the ed25519 committee — NEVER assembled
/// from the cert's self-carried per-vote keys). Each counted vote's carried ML-DSA key is PINNED
/// equal to the enrolled key for that validator and its PQ half verified under it (the GAP #0 pin).
/// A misaligned/empty roster counts NO signer (fail-closed sub-quorum) — never an ed25519-only
/// downgrade.
fn finality_leg(
    proven_head: u32,
    cert: &dregg_lightclient::FinalityCert,
    committee: &[[u8; 32]],
    ml_dsa_committee: &[Vec<u8>],
) -> Result<usize, String> {
    if committee.is_empty() {
        return Err(
            "unanchored — no trusted committee configured (a count-only quorum is never \
                    accepted)"
                .to_string(),
        );
    }
    // Root seam: the cert must finalize the SAME head the aggregate proves.
    let shown = cert.finalized_root.as_u32();
    if shown != proven_head {
        return Err(format!(
            "root seam broke: the cert finalizes head {shown} but the aggregate proved head \
             {proven_head}"
        ));
    }
    // Committee-anchored quorum — threshold over the TRUSTED committee size, not the cert's count.
    // The hybrid gate pins each signer's PQ half to the ENROLLED `ml_dsa_committee` roster.
    if !cert.has_committee_quorum(committee, ml_dsa_committee) {
        let threshold = 2 * committee.len() / 3 + 1;
        return Err(format!(
            "sub-quorum: only {} of the {} trusted committee members cast a verifying HYBRID vote \
             ({} required) — a fork signed by foreign keys, or a vote whose PQ half is not the \
             enrolled ML-DSA key, does not finalize",
            cert.distinct_committee_signers(committee, ml_dsa_committee),
            committee.len(),
            threshold
        ));
    }
    Ok(cert.distinct_committee_signers(committee, ml_dsa_committee))
}

/// Reconstruct a [`dregg_lightclient::FinalityCert`] from its JSON form (hex-decoding each vote).
fn reconstruct_finality_cert(
    json: &FinalityCertJson,
) -> Result<dregg_lightclient::FinalityCert, String> {
    use dregg_circuit::field::BabyBear;
    use dregg_lightclient::SignedVote;
    let mut votes = Vec::with_capacity(json.votes.len());
    for v in &json.votes {
        let validator = parse_hex32(&v.validator_hex).map_err(|e| format!("validator key: {e}"))?;
        let signature = parse_hex64(&v.signature_hex).map_err(|e| format!("signature: {e}"))?;
        // HYBRID: the PQ half rides self-contained. An empty/absent hex string reconstructs an
        // empty Vec, which the light client's `verify_ml_dsa_half` rejects fail-closed (so a legacy
        // classical-only cert simply does not finalize under the hybrid gate). A present-but-malformed
        // hex string is a hard error (never a silent drop).
        let ml_dsa_pubkey =
            parse_hex_var(&v.ml_dsa_pubkey_hex).map_err(|e| format!("ml-dsa pk: {e}"))?;
        let pq_signature =
            parse_hex_var(&v.pq_signature_hex).map_err(|e| format!("pq sig: {e}"))?;
        votes.push(SignedVote {
            validator,
            signature,
            ml_dsa_pubkey,
            pq_signature,
        });
    }
    Ok(dregg_lightclient::FinalityCert {
        votes,
        participant_count: json.participant_count,
        finalized_root: BabyBear::new(json.finalized_root),
    })
}

/// Build the `attested: false` finalized-refusal view (carries the envelope's publics for context).
fn finalized_refusal(env: &ExternalHistoryEnvelope, reason: String) -> Result<JsValue, JsError> {
    let view = AttestedHistoryView {
        attested: false,
        genesis_root: env.genesis_root.clone(),
        final_root: env.final_root.clone(),
        chain_digest: env.chain_digest.clone(),
        num_turns: env.num_turns,
        engine: "recursive-stark (plonky3 fork)".to_string(),
        named_floor: reason,
    };
    serde_wasm_bindgen::to_value(&view).map_err(JsError::from)
}

/// Parse a comma-separated list of 64-hex validator keys into a trusted committee. Blank tokens are
/// skipped; a malformed token is a hard error (a fat-fingered committee is never silently shrunk).
fn parse_committee_csv(s: &str) -> Result<Vec<[u8; 32]>, String> {
    s.split(',')
        .map(|t| t.trim())
        .filter(|t| !t.is_empty())
        .map(parse_hex32)
        .collect()
}

/// Parse a comma-separated list of hex-encoded ENROLLED ML-DSA-65 public keys into the trusted PQ
/// roster, aligned index-for-index with the ed25519 `committee` from [`parse_committee_csv`]. Each
/// token is a `ML_DSA_PK_LEN`-byte (FIPS 204 = 1952 bytes → 3904 hex chars) ML-DSA-65 public key.
/// Blank tokens are skipped (mirroring `parse_committee_csv`, so a trailing comma is tolerated); a
/// malformed or wrong-length token is a HARD error — a fat-fingered enrolled key is a clear config
/// error, never a silent drop. An EMPTY input yields an empty roster which, being misaligned with a
/// non-empty committee, fails the hybrid quorum CLOSED (never an ed25519-only downgrade). The caller
/// sources these keys from the SAME genesis/epoch config the ed25519 committee comes from.
fn parse_ml_dsa_committee_csv(s: &str) -> Result<Vec<Vec<u8>>, String> {
    s.split(',')
        .map(|t| t.trim())
        .filter(|t| !t.is_empty())
        .map(|t| {
            let bytes = parse_hex_var(t)?;
            if bytes.len() != dregg_pq::ML_DSA_PK_LEN {
                return Err(format!(
                    "expected a {}-byte ML-DSA-65 public key ({} hex chars), got {} bytes",
                    dregg_pq::ML_DSA_PK_LEN,
                    dregg_pq::ML_DSA_PK_LEN * 2,
                    bytes.len()
                ));
            }
            Ok(bytes)
        })
        .collect()
}

/// Parse a 128-char hex string into a `[u8; 64]` (an Ed25519 signature). Mirrors [`parse_hex32`].
fn parse_hex64(s: &str) -> Result<[u8; 64], String> {
    let s = s.trim();
    let s = s.strip_prefix("0x").unwrap_or(s);
    if s.len() != 128 {
        return Err(format!(
            "expected 128 hex chars (64 bytes), got {}",
            s.len()
        ));
    }
    let mut out = [0u8; 64];
    for (i, byte) in out.iter_mut().enumerate() {
        let hi = hex_nibble(s.as_bytes()[2 * i])?;
        let lo = hex_nibble(s.as_bytes()[2 * i + 1])?;
        *byte = (hi << 4) | lo;
    }
    Ok(out)
}

/// **THE PRODUCER** — fold a real `k`-turn chain in the tab and emit its
/// [`ExternalHistoryEnvelope`] as JSON, with `proof_bytes_b64` populated from the
/// proof's versioned byte envelope. This is the artifact a node/relayer ships and a
/// tab feeds to [`verify_devnet_history`]; producing it in-tab makes the whole
/// round-trip (fold → serialize → bytes → deserialize → verify) tactile.
///
/// The carried `vk_fingerprint_hex` is the producer's CLAIM (the verifier re-pins
/// from the bytes regardless). `k` is clamped to `[2, 4]` (recursive proving is
/// heavy). Returns the JSON string.
#[wasm_bindgen]
pub fn produce_external_history_envelope(k: usize, step: u64) -> Result<String, JsError> {
    use base64::Engine as _;

    let (agg, _attested) = fold_demo_chain(k, step)?;
    let proof_bytes = agg.to_bytes();
    let proof_bytes_b64 = base64::engine::general_purpose::STANDARD.encode(&proof_bytes);

    let env = ExternalHistoryEnvelope {
        version: 1,
        vk_fingerprint_hex: agg.root_vk_fingerprint().to_hex(),
        proof_bytes_b64,
        genesis_root: agg.genesis_root.iter().map(|d| d.as_u32()).collect(),
        final_root: agg.final_root.iter().map(|d| d.as_u32()).collect(),
        chain_digest: agg.chain_digest.iter().map(|d| d.as_u32()).collect(),
        num_turns: agg.num_turns,
        // The demo producer holds no validator keys; a finalized envelope is produced by the node
        // that ran consensus. `verify_finalized_devnet_history` refuses a cert-less envelope as
        // un-finalized (legs 1+2 only) — exactly the LC-3 boundary.
        finality_cert: None,
    };
    serde_json::to_string(&env)
        .map_err(|e| JsError::new(&format!("envelope serialize failed: {e}")))
}

// ---------------------------------------------------------------------------
// THE PER-SLOT HEAP OPENING — close the served-plain seam.
//
// `verify_devnet_history` attests that a cell's whole finalized history folds to
// its committed state anchor (`final_root`), re-witnessing nothing. But the card a
// trustless portal serves paints per-FIELD values, and those values are the
// SERVER'S rendering until each is bound, in the tab, to the committed cell state.
//
// This is that binding: a per-slot sparse-Merkle OPENING of (slot → value) against
// the cell's committed umem heap root, verified tab-side. It reproduces EXACTLY the
// path fold `dregg_circuit::heap_root` commits with (the arity-2 Poseidon2 leaf
// `hash[heap_addr(coll,key), value]` folded up a depth-`HEAP_TREE_DEPTH` tree by
// `hash_fact`) — the executable counterpart of Lean's `Heap.root_binds_get` (equal
// roots ⇒ equal value at every (coll, key)). A correct opening attests the field
// value; a tampered value, a wrong slot, or a forged path moves the recomputed root
// off `root` and is REFUSED.
//
// HONEST SCOPE: this verifies a field value against the cell's HEAP ROOT. The heap
// root is one limb of the cell-state commitment that the faithful 8-felt
// `final_root` folds — so it BINDS to the light-client-verified anchor, but
// re-deriving `final_root` from the heap root in-tab (recomputing the whole
// cell-state commitment from its limbs) is a further rung, not done here. What IS
// closed: each shown field value provably equals the value committed at its slot in
// the cell heap whose root is the verified opening's `root`.
// ---------------------------------------------------------------------------

/// **VERIFY A PER-SLOT HEAP OPENING** — prove a rendered field VALUE equals the
/// value committed at its slot `(coll, key)` in the cell's umem heap, against the
/// cell's committed `root`, re-witnessing nothing.
///
/// Reproduces the canonical heap path fold (`dregg_circuit::heap_root`): the leaf is
/// the arity-2 Poseidon2 digest `hash[heap_addr(coll, key), value]`; it folds up a
/// depth-`HEAP_TREE_DEPTH` tree against `siblings_csv` per `directions_csv` (bit `0`
/// = the running node is the left child → `hash_fact(cur, sib)`; `1` = right →
/// `hash_fact(sib, cur)`), and the recomputed root must equal `root`.
///
/// All field elements are decimal `BabyBear` felts (`< 2^31`): `root`/`value`/each
/// sibling. `siblings_csv` and `directions_csv` are comma-separated, each of length
/// exactly `HEAP_TREE_DEPTH` (16) — a wrong length is REFUSED (fail-closed). A
/// tampered value, a wrong `(coll, key)`, or a forged path recomputes a different
/// root and returns `false`.
#[wasm_bindgen]
pub fn verify_slot_opening(
    root: u32,
    coll: u32,
    key: u32,
    value: u32,
    siblings_csv: &str,
    directions_csv: &str,
) -> bool {
    let siblings = parse_felt_csv(siblings_csv);
    let directions: Vec<u8> = parse_felt_csv(directions_csv)
        .into_iter()
        .map(|d| (d & 1) as u8)
        .collect();
    verify_slot_opening_core(root, coll, key, value, &siblings, &directions)
}

/// The pure path-fold verify the `#[wasm_bindgen]` wrapper drives (host-testable: no
/// `JsValue`). Folds the (coll, key, value) leaf up the depth-`HEAP_TREE_DEPTH` tree
/// against the opening and compares the recomputed root to `root`. Fails closed on a
/// wrong-length path.
fn verify_slot_opening_core(
    root: u32,
    coll: u32,
    key: u32,
    value: u32,
    siblings: &[u32],
    directions: &[u8],
) -> bool {
    use dregg_circuit::field::BabyBear;
    use dregg_circuit::heap_root::{HEAP_TREE_DEPTH, HeapLeaf, heap_addr};
    use dregg_circuit::poseidon2::hash_fact;

    if siblings.len() != HEAP_TREE_DEPTH || directions.len() != HEAP_TREE_DEPTH {
        return false;
    }
    let leaf = HeapLeaf {
        addr: heap_addr(BabyBear::new(coll), BabyBear::new(key)),
        value: BabyBear::new(value),
    };
    let mut cur = leaf.digest();
    for level in 0..HEAP_TREE_DEPTH {
        let sib = BabyBear::new(siblings[level]);
        cur = if directions[level] == 0 {
            hash_fact(cur, &[sib])
        } else {
            hash_fact(sib, &[cur])
        };
    }
    cur.as_u32() == BabyBear::new(root).as_u32()
}

/// Parse a comma-separated list of decimal `u32` felts. Blank tokens are skipped; a
/// non-numeric token is dropped (which shortens the list, so the caller's
/// length-check fails closed — a malformed path is REFUSED, never silently padded).
fn parse_felt_csv(s: &str) -> Vec<u32> {
    s.split(',')
        .map(|t| t.trim())
        .filter(|t| !t.is_empty())
        .filter_map(|t| t.parse::<u32>().ok())
        .collect()
}

// ---------------------------------------------------------------------------
// Shared helpers.
// ---------------------------------------------------------------------------

/// Fold a continuous chain of `k` REAL finalized transfer turns (each post-state
/// IS the next's pre-state) and light-verify it (self-anchored). The single
/// fold+attest path [`light_client_demo`], [`genesis_vk_anchor`], and
/// [`verify_history_against_anchor`] share. Returns the aggregate + its
/// self-anchored attestation.
fn fold_demo_chain(
    k: usize,
    step: u64,
) -> Result<
    (
        dregg_circuit_prove::ivc_turn_chain::WholeChainProof,
        dregg_lightclient::AttestedHistory,
    ),
    JsError,
> {
    use dregg_circuit::effect_vm::{CellState, Effect};
    use dregg_circuit_prove::ivc_turn_chain::FinalizedTurn;
    use dregg_circuit_prove::joint_turn_aggregation::DescriptorParticipant;
    use dregg_lightclient::fold_and_attest;
    use dregg_turn::rotation_witness::mint_rotated_participant_leg;

    // Bucket-F (PATH-PRESERVE Phase 5a): the finalized turns carry the MANDATORY ROTATED leg —
    // the rotated multi-table `Ir2BatchProof` minted by `mint_rotated_participant_leg` from the
    // live producer witnesses over before/after actor cells (the v1 `EffectVmP3Proof` is dropped).
    // `dregg-circuit`'s `recursion` feature is unified ON in this standalone wasm graph (see
    // `wasm/Cargo.toml` §FORK SEAM — `dregg-observability`/`dregg-lightclient` pull `dregg-circuit`
    // with its default features, and `recursion` is in that set), so the recursion-gated mint
    // helper + `DescriptorParticipant::rotated` are available here.

    // OPEN permissions so the rotated producer-witness path admits the actor cell.
    fn open_permissions() -> dregg_cell::Permissions {
        use dregg_cell::AuthRequired;
        dregg_cell::Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        }
    }
    // The transfer actor cell at `(balance, nonce)` with open permissions.
    fn producer_cell(balance: i64, nonce: u64) -> dregg_cell::Cell {
        let mut pk = [0u8; 32];
        pk[0] = 7;
        let mut cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], balance);
        cell.permissions = open_permissions();
        for _ in 0..nonce {
            let _ = cell.state.increment_nonce();
        }
        cell
    }

    let k = k.clamp(2, 4);
    let step = if step == 0 { 1 } else { step };
    // Start with enough balance that k debits of `step` never underflow.
    let start_balance: u64 = step.saturating_mul(k as u64).saturating_add(1_000_000);

    let mut turns: Vec<FinalizedTurn> = Vec::with_capacity(k);
    let mut balance = start_balance;
    // The rotated trace welds balance/nonce from the v1 sub-trace, which BUMPS the nonce by 1 per
    // Transfer row — turn i's after-state is `(balance - step, nonce + 1)`, which IS turn i+1's
    // before-state. Advance BOTH balance and nonce per turn so the rotated state-commit roots chain
    // (`new_root[i] == old_root[i+1]`, the temporal tooth).
    let mut nonce: u32 = 0;
    for _ in 0..k {
        let state = CellState::new(balance, nonce);
        let effects = vec![Effect::Transfer {
            amount: step,
            direction: 1,
        }];
        let before_cell = producer_cell(balance as i64, nonce as u64);
        let after_cell = producer_cell((balance as i64) - (step as i64), nonce as u64);
        let nullifier_root = [0u8; 32];
        let commitments_root = [0u8; 32];
        let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
        let leg = mint_rotated_participant_leg(
            &state,
            &effects,
            &before_cell,
            &after_cell,
            &nullifier_root,
            &commitments_root,
            &receipt_log,
            None,
        )
        .map_err(|e| JsError::new(&format!("rotated leg mint failed: {e}")))?;
        turns.push(FinalizedTurn::new(DescriptorParticipant::rotated(leg)));
        balance -= step;
        nonce += 1; // the v1 sub-trace bumps the nonce by 1 per Transfer row.
    }

    fold_and_attest(&turns)
        .map_err(|e| JsError::new(&format!("light-client fold/verify failed: {e}")))
}

/// Parse a 64-char hex string into a `[u8; 32]`. The single hex→anchor decoder the
/// config-anchor entry points share. Rejects wrong length / non-hex with a precise
/// message (so a fat-fingered anchor is a clear error, not a silent zero-fill).
fn parse_hex32(s: &str) -> Result<[u8; 32], String> {
    let s = s.trim();
    let s = s.strip_prefix("0x").unwrap_or(s);
    if s.len() != 64 {
        return Err(format!("expected 64 hex chars (32 bytes), got {}", s.len()));
    }
    let mut out = [0u8; 32];
    for (i, byte) in out.iter_mut().enumerate() {
        let hi = hex_nibble(s.as_bytes()[2 * i])?;
        let lo = hex_nibble(s.as_bytes()[2 * i + 1])?;
        *byte = (hi << 4) | lo;
    }
    Ok(out)
}

/// Decode a variable-length hex string (optional `0x` prefix) to bytes. An empty string decodes to
/// an empty `Vec` (the "PQ half absent" sentinel the hybrid gate rejects fail-closed). An odd length
/// or a non-hex character is a hard error — never a silent truncation.
fn parse_hex_var(s: &str) -> Result<Vec<u8>, String> {
    let s = s.trim();
    let s = s.strip_prefix("0x").unwrap_or(s);
    if s.is_empty() {
        return Ok(Vec::new());
    }
    if s.len() % 2 != 0 {
        return Err(format!(
            "expected an even number of hex chars, got {}",
            s.len()
        ));
    }
    let bytes = s.as_bytes();
    let mut out = Vec::with_capacity(s.len() / 2);
    for pair in bytes.chunks_exact(2) {
        let hi = hex_nibble(pair[0])?;
        let lo = hex_nibble(pair[1])?;
        out.push((hi << 4) | lo);
    }
    Ok(out)
}

fn hex_nibble(c: u8) -> Result<u8, String> {
    match c {
        b'0'..=b'9' => Ok(c - b'0'),
        b'a'..=b'f' => Ok(c - b'a' + 10),
        b'A'..=b'F' => Ok(c - b'A' + 10),
        other => Err(format!("non-hex character '{}'", other as char)),
    }
}

// ---------------------------------------------------------------------------
// Native (host-runnable) tests for the CONFIG-NOT-ARTIFACT discipline.
//
// These exercise the pure transport/anchor logic that does NOT touch `JsValue`
// (so they run under plain `cargo test`, no wasm runtime): hex anchor parsing,
// the versioned envelope serde + version pin, and the anchor-discipline
// comparison. The heavy `verify_history_against_anchor` proving path is exercised
// end-to-end by `dregg-lightclient`'s own tests (it calls the SAME `verify_history`
// against the SAME `RecursionVk` anchor) and, at runtime, by the playground.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_hex32_roundtrips_and_strips_0x() {
        let bytes: [u8; 32] = core::array::from_fn(|i| (i * 7 + 1) as u8);
        let hex: String = bytes.iter().map(|b| format!("{b:02x}")).collect();
        // Plain, 0x-prefixed, and whitespace-padded all decode to the same bytes.
        assert_eq!(parse_hex32(&hex).unwrap(), bytes);
        assert_eq!(parse_hex32(&format!("0x{hex}")).unwrap(), bytes);
        assert_eq!(parse_hex32(&format!("  {hex}  ")).unwrap(), bytes);
        // Uppercase decodes identically (the anchor is case-insensitive hex).
        assert_eq!(parse_hex32(&hex.to_uppercase()).unwrap(), bytes);
    }

    #[test]
    fn parse_hex32_rejects_wrong_length_and_nonhex_no_silent_zero() {
        // A fat-fingered anchor must be a CLEAR error, never a silent zero-fill
        // (a zero anchor would be a real fingerprint a forger could target).
        assert!(parse_hex32("dead").is_err(), "too short must error");
        assert!(parse_hex32(&"a".repeat(63)).is_err(), "63 chars must error");
        let mut bad = "a".repeat(63);
        bad.push('z'); // 64 chars, but 'z' is not hex
        let e = parse_hex32(&bad).unwrap_err();
        assert!(e.to_lowercase().contains("non-hex"), "got: {e}");
    }

    #[test]
    fn external_envelope_roundtrips_and_carries_publics() {
        let env = ExternalHistoryEnvelope {
            version: 1,
            vk_fingerprint_hex: "ab".repeat(32),
            proof_bytes_b64: String::new(),
            genesis_root: vec![11, 0, 0, 0, 0, 0, 0, 0],
            final_root: vec![22, 0, 0, 0, 0, 0, 0, 0],
            chain_digest: vec![33, 0, 0, 0, 0, 0, 0, 0],
            num_turns: 4,
            finality_cert: None,
        };
        let json = serde_json::to_string(&env).unwrap();
        let back: ExternalHistoryEnvelope = serde_json::from_str(&json).unwrap();
        assert_eq!(back.version, 1);
        assert_eq!(back.vk_fingerprint_hex, "ab".repeat(32));
        assert_eq!(back.genesis_root, vec![11, 0, 0, 0, 0, 0, 0, 0]);
        assert_eq!(back.final_root, vec![22, 0, 0, 0, 0, 0, 0, 0]);
        assert_eq!(back.chain_digest, vec![33, 0, 0, 0, 0, 0, 0, 0]);
        assert_eq!(back.num_turns, 4);
        // proof_bytes_b64 is `#[serde(default)]` — an envelope omitting it parses.
        let minimal = r#"{"version":1,"vk_fingerprint_hex":"00","genesis_root":[0,0,0,0,0,0,0,0],
            "final_root":[0,0,0,0,0,0,0,0],"chain_digest":[0,0,0,0,0,0,0,0],"num_turns":2}"#;
        let m: ExternalHistoryEnvelope = serde_json::from_str(minimal).unwrap();
        assert!(
            m.proof_bytes_b64.is_empty(),
            "omitted proof bytes default empty"
        );
    }

    #[test]
    fn populated_proof_bytes_survive_the_json_envelope() {
        // The byte path is real: arbitrary proof bytes base64-encode INTO the JSON
        // envelope and decode back bit-identically (the wrapper the producer fills
        // and the verifier reads). Uses base64 the SAME way the producer/verifier do.
        use base64::Engine as _;
        let raw: Vec<u8> = (0u16..512).map(|i| (i % 251) as u8).collect();
        let b64 = base64::engine::general_purpose::STANDARD.encode(&raw);
        let env = ExternalHistoryEnvelope {
            version: 1,
            vk_fingerprint_hex: "ab".repeat(32),
            proof_bytes_b64: b64.clone(),
            genesis_root: vec![7, 0, 0, 0],
            final_root: vec![9, 0, 0, 0],
            chain_digest: vec![13, 0, 0, 0],
            num_turns: 3,
            finality_cert: None,
        };
        let json = serde_json::to_string(&env).unwrap();
        let back: ExternalHistoryEnvelope = serde_json::from_str(&json).unwrap();
        assert_eq!(
            back.proof_bytes_b64, b64,
            "the b64 survives the JSON wrapper"
        );
        let decoded = base64::engine::general_purpose::STANDARD
            .decode(back.proof_bytes_b64.as_bytes())
            .expect("the carried b64 decodes");
        assert_eq!(
            decoded, raw,
            "the proof bytes round-trip through the envelope"
        );
    }

    #[test]
    fn slot_opening_verifies_and_a_tampered_value_is_refused() {
        // THE SERVED-PLAIN CLOSURE, at the crypto level: a REAL opening of a slot's
        // value against the cell's committed heap root verifies; a tampered value (or
        // wrong slot) recomputes a different root and is REFUSED. The opening is minted
        // by the SAME `dregg_circuit::heap_root` the executor commits with, so the
        // tab-side fold here reproduces the committed root bit-for-bit.
        use dregg_circuit::field::BabyBear;
        use dregg_circuit::heap_root::{CanonicalHeapTree, HEAP_TREE_DEPTH, HeapLeaf, heap_addr};

        // A small umem heap: three (coll, key) → value entries.
        let entries: [((u32, u32), u32); 3] = [((1, 1), 10), ((1, 2), 77), ((2, 1), 30)];
        let leaves: Vec<HeapLeaf> = entries
            .iter()
            .map(|((c, k), v)| HeapLeaf {
                addr: heap_addr(BabyBear::new(*c), BabyBear::new(*k)),
                value: BabyBear::new(*v),
            })
            .collect();
        let tree = CanonicalHeapTree::new(leaves, HEAP_TREE_DEPTH);
        let root = tree.root().as_u32();

        // Open slot (1, 2) → 77: a real membership proof off the committed tree.
        let addr = heap_addr(BabyBear::new(1), BabyBear::new(2));
        let pos = tree
            .position_of(addr)
            .expect("the slot is present in the heap");
        let (sibs, dirs) = tree.prove_membership(pos).expect("membership proof");
        let sibs_u32: Vec<u32> = sibs.iter().map(|s| s.as_u32()).collect();

        // A real opening checks; a tampered value fails; a wrong slot fails.
        assert!(
            verify_slot_opening_core(root, 1, 2, 77, &sibs_u32, &dirs),
            "a genuine opening of the committed value verifies"
        );
        assert!(
            !verify_slot_opening_core(root, 1, 2, 78, &sibs_u32, &dirs),
            "a tampered value recomputes a different root and is refused"
        );
        assert!(
            !verify_slot_opening_core(root, 9, 9, 77, &sibs_u32, &dirs),
            "the opening is bound to its (coll, key) — a wrong slot is refused"
        );
        // A wrong-length path fails closed (no silent pad).
        assert!(
            !verify_slot_opening_core(root, 1, 2, 77, &sibs_u32[..3], &dirs),
            "a short path is refused, never padded"
        );

        // The CSV `#[wasm_bindgen]` wrapper agrees with the core.
        let sibs_csv = sibs_u32
            .iter()
            .map(|s| s.to_string())
            .collect::<Vec<_>>()
            .join(",");
        let dirs_csv = dirs
            .iter()
            .map(|d| d.to_string())
            .collect::<Vec<_>>()
            .join(",");
        assert!(
            verify_slot_opening(root, 1, 2, 77, &sibs_csv, &dirs_csv),
            "the CSV wrapper verifies a real opening"
        );
        assert!(
            !verify_slot_opening(root, 1, 2, 78, &sibs_csv, &dirs_csv),
            "the CSV wrapper refuses a tampered value"
        );
    }

    #[test]
    fn anchor_discipline_distinguishes_config_from_envelope_claim() {
        // THE config-not-artifact tooth, at the byte level: the verifier compares
        // the envelope's CLAIMED fingerprint to its OWN configured anchor. An
        // envelope built for a DIFFERENT circuit (claim ≠ config) must be
        // distinguishable — the bytes differ — so the mismatch arm fires.
        let config = parse_hex32(&"ab".repeat(32)).unwrap();
        let same_claim = parse_hex32(&"ab".repeat(32)).unwrap();
        let other_claim = parse_hex32(&"cd".repeat(32)).unwrap();
        assert_eq!(config, same_claim, "matching config attests the discipline");
        assert_ne!(
            config, other_claim,
            "a claim for a different circuit is refused — never trusted from the envelope"
        );
    }

    /// **LC-3 — THE FINALITY LEG (host tooth for the over-wire finalized check).** Exercises the
    /// pure `finality_leg` / `reconstruct_finality_cert` helpers that the wasm
    /// `verify_finalized_devnet_history` composes — no STARK fold — so the leg-3 anchor is validated
    /// in milliseconds: an UNANCHORED client (empty committee) accepts nothing; a fork signed by
    /// FOREIGN keys is sub-quorum; a ROOT-SEAM break is refused; and only a real committee quorum
    /// over the proven head passes. The full byte-path is exercised by the playground at runtime;
    /// the leg-3 LOGIC is identical to `dregg_lightclient`'s committee-anchored teeth.
    #[test]
    fn finality_leg_anchors_to_the_trusted_committee() {
        use dregg_circuit::field::BabyBear;
        use dregg_lightclient::{
            FinalityCert, HYBRID_PQ_CTX, SignedVote, finality_signing_message,
        };
        use dregg_pq::MlDsaKey;
        use ed25519_dalek::{Signer, SigningKey};

        // A deterministic committee of 4 (threshold = 2*4/3 + 1 = 3).
        let n = 4usize;
        let keys: Vec<SigningKey> = (0..n as u8)
            .map(|i| {
                let mut seed = [0u8; 32];
                seed[0] = i;
                seed[31] = 0xC3;
                SigningKey::from_bytes(&seed)
            })
            .collect();
        let committee: Vec<[u8; 32]> = keys.iter().map(|k| k.verifying_key().to_bytes()).collect();
        // The ENROLLED ML-DSA-65 roster, aligned index-for-index with `committee` (config, NOT
        // read from the votes): each member's PQ key derived from the SAME 32-byte ed25519 seed
        // the vote's PQ half is signed under (mirrors `keygen_from_seed`). This is what the GAP #0
        // pin checks each carried per-vote key against.
        let ml_dsa_committee: Vec<Vec<u8>> = keys
            .iter()
            .map(|k| MlDsaKey::from_ed25519_seed(&k.to_bytes()).public_bytes())
            .collect();

        let root_felt = 555_123u32;
        let root = BabyBear::new(root_felt);
        // A genuine HYBRID vote: the ed25519 half AND an ML-DSA-65 half, both over the SAME
        // `finality_signing_message`. The PQ key is derived deterministically from the same 32-byte
        // seed as the ed25519 identity (mirroring `MlDsaTurnKey::from_ed25519_seed`), and its public
        // key rides self-contained in the vote — exactly what the light client's hybrid gate
        // re-verifies. A vote with only the classical half would be dropped fail-closed.
        let sign_vote = |k: &SigningKey| -> SignedVote {
            let msg = finality_signing_message(root, n);
            let ml_key = MlDsaKey::from_ed25519_seed(&k.to_bytes());
            let pq_signature = ml_key
                .try_sign(HYBRID_PQ_CTX, &msg)
                .expect("ml-dsa-65 sign cannot fail on a valid key");
            SignedVote {
                validator: k.verifying_key().to_bytes(),
                signature: k.sign(&msg).to_bytes(),
                ml_dsa_pubkey: ml_key.public_bytes(),
                pq_signature,
            }
        };

        // (a) LEGIT — a 3-of-4 committee quorum over the proven head passes.
        let honest = FinalityCert {
            votes: keys[..3].iter().map(sign_vote).collect(),
            participant_count: n,
            finalized_root: root,
        };
        assert_eq!(
            finality_leg(root_felt, &honest, &committee, &ml_dsa_committee),
            Ok(3),
            "a genuine committee quorum over the proven head finalizes"
        );

        // (b) UNANCHORED — no committee configured accepts nothing.
        assert!(
            finality_leg(root_felt, &honest, &[], &ml_dsa_committee)
                .unwrap_err()
                .contains("unanchored"),
            "an unanchored client refuses outright"
        );

        // (c) FOREIGN KEYS — a fork signed by 3 well-formed keys NOT in the committee is sub-quorum.
        let foreign_keys: Vec<SigningKey> = (100..103u8)
            .map(|i| {
                let mut seed = [0u8; 32];
                seed[0] = i;
                seed[31] = 0xC3;
                SigningKey::from_bytes(&seed)
            })
            .collect();
        let forged = FinalityCert {
            votes: foreign_keys.iter().map(sign_vote).collect(),
            participant_count: n,
            finalized_root: root,
        };
        assert!(
            forged
                .votes
                .iter()
                .all(|v| !committee.contains(&v.validator)),
            "the forged keys are genuinely outside the trusted committee"
        );
        assert!(
            finality_leg(root_felt, &forged, &committee, &ml_dsa_committee)
                .unwrap_err()
                .contains("sub-quorum"),
            "a fork signed by foreign keys does not finalize"
        );

        // (d) ROOT-SEAM break — a genuine committee quorum, but over a DIFFERENT head than the
        // aggregate proved. The seam must break before the quorum even matters.
        assert!(
            finality_leg(root_felt + 1, &honest, &committee, &ml_dsa_committee)
                .unwrap_err()
                .contains("root seam"),
            "a cert finalizing a different head than the proven aggregate is refused"
        );

        // (e) reconstruct_finality_cert roundtrips the JSON wire form back to a verifying cert.
        let json = FinalityCertJson {
            votes: honest
                .votes
                .iter()
                .map(|v| FinalityVoteJson {
                    validator_hex: v.validator.iter().map(|b| format!("{b:02x}")).collect(),
                    signature_hex: v.signature.iter().map(|b| format!("{b:02x}")).collect(),
                    ml_dsa_pubkey_hex: v.ml_dsa_pubkey.iter().map(|b| format!("{b:02x}")).collect(),
                    pq_signature_hex: v.pq_signature.iter().map(|b| format!("{b:02x}")).collect(),
                })
                .collect(),
            participant_count: n,
            finalized_root: root_felt,
        };
        let back = reconstruct_finality_cert(&json).expect("the wire cert reconstructs");
        assert_eq!(
            finality_leg(root_felt, &back, &committee, &ml_dsa_committee),
            Ok(3),
            "the reconstructed wire cert verifies identically"
        );
    }

    /// **THE ENROLLED-ROSTER BOUNDARY (GAP #0 pin at the wasm surface).** The new
    /// `ml_dsa_committee_hex_csv` param parses into the index-for-index enrolled roster the finality
    /// leg pins carried PQ keys against — NOT the fail-closed empty the boundary carried before. This
    /// exercises the pure `parse_ml_dsa_committee_csv` the `#[wasm_bindgen]` entry calls: a genuine
    /// enrolled roster (minted via `dregg_pq::MlDsaKey`, the SAME primitive the committee enrolls with)
    /// hex-encodes → parses back index-for-index; the empty staged-rollout string yields an empty
    /// (fail-closed) roster; and a wrong-length token is a HARD config error, never a silent drop.
    #[test]
    fn ml_dsa_committee_csv_threads_the_enrolled_roster_and_fails_closed() {
        use dregg_pq::MlDsaKey;

        // A real enrolled roster, index-for-index with a 3-member committee (same seeds the ed25519
        // committee would derive from — config, exactly like the ed25519 CSV).
        let roster: Vec<Vec<u8>> = (0..3u8)
            .map(|i| {
                let mut seed = [0u8; 32];
                seed[0] = i;
                seed[31] = 0xC3;
                MlDsaKey::from_ed25519_seed(&seed).public_bytes()
            })
            .collect();
        let csv = roster
            .iter()
            .map(|k| k.iter().map(|b| format!("{b:02x}")).collect::<String>())
            .collect::<Vec<_>>()
            .join(",");

        // (a) A genuine enrolled roster round-trips index-for-index — the boundary now carries the
        // ENROLLED keys, not the fail-closed empty.
        let parsed = parse_ml_dsa_committee_csv(&csv).expect("the enrolled roster parses");
        assert_eq!(parsed, roster, "the roster parses back index-for-index");
        assert_eq!(parsed.len(), 3);
        assert!(parsed.iter().all(|k| k.len() == dregg_pq::ML_DSA_PK_LEN));

        // (b) The empty staged-rollout string yields an empty roster — misaligned with any non-empty
        // committee, so leg 3 counts ZERO signers (fail-closed, never an ed25519-only downgrade).
        assert!(
            parse_ml_dsa_committee_csv("").unwrap().is_empty(),
            "an empty roster CSV is the fail-closed absent case"
        );
        // A trailing comma / blank token is tolerated without shifting alignment.
        assert_eq!(
            parse_ml_dsa_committee_csv(&format!("{csv},"))
                .unwrap()
                .len(),
            3,
            "a trailing comma does not add a phantom roster slot"
        );

        // (c) A wrong-length token is a HARD error — a fat-fingered enrolled key is a clear config
        // error, not a silent short key that would later fail the pin quietly.
        let short = "abcd";
        let e = parse_ml_dsa_committee_csv(short).unwrap_err();
        assert!(e.contains("ML-DSA-65 public key"), "got: {e}");
    }
}
