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
    /// The genesis state root the attested history starts from (decimal felt).
    pub genesis_root: u32,
    /// The final state root — the genuine fold of the whole history (decimal felt).
    pub final_root: u32,
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
        genesis_root: attested.genesis_root.as_u32(),
        final_root: attested.final_root.as_u32(),
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
                genesis_root: attested.genesis_root.as_u32(),
                final_root: attested.final_root.as_u32(),
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
                genesis_root: 0,
                final_root: 0,
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
    /// Carried public commitment: the genesis state root (decimal felt).
    pub genesis_root: u32,
    /// Carried public commitment: the final state root (decimal felt).
    pub final_root: u32,
    /// Carried public commitment: the multi-felt ordered-history digest (decimal felts).
    pub chain_digest: Vec<u32>,
    /// Carried public commitment: how many finalized turns the aggregate folds.
    pub num_turns: usize,
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
            genesis_root: env.genesis_root,
            final_root: env.final_root,
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
            genesis_root: env.genesis_root,
            final_root: env.final_root,
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
                genesis_root: attested.genesis_root.as_u32(),
                final_root: attested.final_root.as_u32(),
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
        genesis_root: agg.genesis_root.as_u32(),
        final_root: agg.final_root.as_u32(),
        chain_digest: agg.chain_digest.iter().map(|d| d.as_u32()).collect(),
        num_turns: agg.num_turns,
    };
    serde_json::to_string(&env)
        .map_err(|e| JsError::new(&format!("envelope serialize failed: {e}")))
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
            genesis_root: 11,
            final_root: 22,
            chain_digest: vec![33, 0, 0, 0],
            num_turns: 4,
        };
        let json = serde_json::to_string(&env).unwrap();
        let back: ExternalHistoryEnvelope = serde_json::from_str(&json).unwrap();
        assert_eq!(back.version, 1);
        assert_eq!(back.vk_fingerprint_hex, "ab".repeat(32));
        assert_eq!(back.genesis_root, 11);
        assert_eq!(back.final_root, 22);
        assert_eq!(back.chain_digest, vec![33, 0, 0, 0]);
        assert_eq!(back.num_turns, 4);
        // proof_bytes_b64 is `#[serde(default)]` — an envelope omitting it parses.
        let minimal = r#"{"version":1,"vk_fingerprint_hex":"00","genesis_root":0,
            "final_root":0,"chain_digest":[0,0,0,0],"num_turns":2}"#;
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
            genesis_root: 7,
            final_root: 9,
            chain_digest: vec![13, 0, 0, 0],
            num_turns: 3,
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
}
