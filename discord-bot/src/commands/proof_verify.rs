//! **Actually VERIFY the fetched full-turn STARK** (bot-excellence backlog Tier-2 #11).
//!
//! `/proof turn` (and `/explorer proof`) fetch a committed turn's proof artifact off the node
//! (`/api/turn/{hash}/proof`) and used to present it trust-me: size + hex head + "Attached ✅".
//! That is the one artifact whose entire purpose is that ANYONE can check it. This module is
//! the check: the bot deserializes the served bytes into the real composed full-turn proof and
//! runs the SAME audited verifier a remote peer would — [`dregg_sdk::verify_full_turn`], the
//! Plonky3 batch-STARK verify of every attached leg plus the cross-leg PI bindings — right
//! there in the handler, and reports "verifies under VK …, checked just now" or an honest
//! failure.
//!
//! ## What is (and is not) established here
//!
//! * **Established:** the bytes ARE a sound composed STARK — every leg (effect-vm-rotated /
//!   membership / non-revocation / cap-membership) verifies under the audited verifier, the
//!   commit anchors chain leg-to-leg, and the whole object binds the 8-felt before/after state
//!   commitments it publishes. A garbage or tampered artifact fails loudly.
//! * **Deliberately NOT established (named seam):** that those bound commitments equal the
//!   chain's canonical committed state for this turn — that binding needs a checkpoint /
//!   attested root the caller trusts (`verify_full_turn_bound` with the canonical revocation
//!   root on the spend path). The expected commits handed to the verifier here are the ones
//!   the proof itself publishes ([`extract_commits`]), so this check is internal-soundness +
//!   VK-binding — exactly what a stranger with only the artifact can check, which is the
//!   honest claim the surface makes.

use dregg_circuit::effect_vm::pi as effect_pi;
use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;
use dregg_circuit::field::BabyBear;
use dregg_dsl_runtime::composition::{AttachedSubProof, ComposedProof};
use dregg_sdk::full_turn_proof::{FullTurnProof, TurnProofComponents};
use dregg_sdk::verify_full_turn;

/// The outcome of re-verifying a served proof artifact — everything the embed reports.
#[derive(Debug, Clone)]
pub struct ProofCheck {
    /// The audited verifier accepted the whole composed object.
    pub verified: bool,
    /// The composed circuit's VK hash (hex) the proof binds — "verifies under VK X".
    pub vk_hex: String,
    /// The attached sub-proof legs, by label (what was actually verified).
    pub legs: Vec<String>,
    /// The proof's published pre-state 8-felt commit anchor (hex lanes).
    pub old_commit: String,
    /// The proof's published post-state 8-felt commit anchor (hex lanes).
    pub new_commit: String,
    /// The verifier's failure detail when `verified == false` (empty on success).
    pub detail: String,
}

/// **Verify a served proof artifact.** `proof_hex` is the node's `proof_hex` field (the
/// postcard-serialized `ComposedProof` the commit path persisted); `turn_hash_hex` the turn it
/// was fetched for. Runs the real [`verify_full_turn`]. `Err` means the bytes could not even
/// be interpreted (not-a-proof); `Ok(check)` carries the verifier's verdict either way.
pub fn check_proof_hex(proof_hex: &str, turn_hash_hex: &str) -> Result<ProofCheck, String> {
    let bytes =
        hex::decode(proof_hex.trim()).map_err(|e| format!("the proof hex does not decode: {e}"))?;
    let composed: ComposedProof = postcard::from_bytes(&bytes)
        .map_err(|e| format!("the served bytes do not parse as a composed full-turn proof: {e}"))?;

    let legs: Vec<String> = composed
        .sub_proofs
        .iter()
        .map(|sp| sp.label.clone())
        .collect();
    // Reconstruct the component flags from the attached legs — the same facts the prover set
    // them from (the wire form carries the legs; the flags are derived presence bits).
    let components = TurnProofComponents {
        has_state_transition: legs.iter().any(|l| l.starts_with("effect-vm")),
        has_membership: legs.iter().any(|l| l == "membership"),
        has_conservation: legs.iter().any(|l| l == "conservation"),
        has_non_revocation: legs.iter().any(|l| l == "non-revocation"),
        has_cap_membership: legs.iter().any(|l| l == "cap-membership"),
    };

    let (old_commit, new_commit) = extract_commits(&composed.sub_proofs)?;
    let vk_hex = hex::encode(composed.composed_vk_hash);

    let mut turn_hash = [0u8; 32];
    if let Ok(th) = hex::decode(turn_hash_hex) {
        if th.len() == 32 {
            turn_hash.copy_from_slice(&th);
        }
    }

    let proof = FullTurnProof {
        composed,
        components,
        turn_hash,
        proof_bytes: bytes,
    };
    let (verified, detail) = match verify_full_turn(&proof, old_commit, new_commit) {
        Ok(()) => (true, String::new()),
        Err(e) => (false, format!("{e:?}")),
    };
    Ok(ProofCheck {
        verified,
        vk_hex,
        legs,
        old_commit: commit_hex(&old_commit),
        new_commit: commit_hex(&new_commit),
        detail,
    })
}

/// The async face: run [`check_proof_hex`] on a blocking thread (a STARK verify is real CPU
/// work, not something for a Discord worker's async slot).
pub async fn check_proof_hex_blocking(
    proof_hex: String,
    turn_hash_hex: String,
) -> Result<ProofCheck, String> {
    tokio::task::spawn_blocking(move || check_proof_hex(&proof_hex, &turn_hash_hex))
        .await
        .unwrap_or_else(|e| Err(format!("the verifier task did not complete: {e}")))
}

/// The proof's own published (before, after) 8-felt commit anchors — read exactly the way
/// `verify_full_turn_bound` binds them: a WIDE rotated leg (its `vk_hash` is a wide-registry
/// descriptor fingerprint) publishes the full 8-felt commits as the LAST 16 PIs; a narrow
/// cap-open leg carries a single felt at `pi::OLD_COMMIT`/`pi::NEW_COMMIT`, broadcast into
/// slot 0. First leg's BEFORE + last leg's AFTER are the turn's endpoints.
fn extract_commits(subs: &[AttachedSubProof]) -> Result<([BabyBear; 8], [BabyBear; 8]), String> {
    let legs: Vec<&AttachedSubProof> = subs
        .iter()
        .filter(|sp| sp.label == "effect-vm" || sp.label == "effect-vm-rotated")
        .collect();
    if legs.is_empty() {
        return Err("the proof carries no effect-vm leg (nothing binds the state commits)".into());
    }
    let (before, _) = leg_commit(legs[0])?;
    let (_, after) = leg_commit(legs[legs.len() - 1])?;
    Ok((before, after))
}

/// Whether a leg bound a WIDE descriptor: its `vk_hash` is the blake3 fingerprint of a
/// committed wide-registry descriptor row (the SAME classification the SDK verifier uses).
fn leg_is_wide(leg: &AttachedSubProof) -> bool {
    WIDE_REGISTRY_STAGED_TSV.lines().any(|line| {
        line.splitn(3, '\t')
            .nth(2)
            .map(|json| blake3::hash(json.as_bytes()).as_bytes() == &leg.vk_hash)
            .unwrap_or(false)
    })
}

/// One leg's (before8, after8) commit anchors at the leg's true width.
fn leg_commit(leg: &AttachedSubProof) -> Result<([BabyBear; 8], [BabyBear; 8]), String> {
    let n = leg.sub_public_inputs.len();
    if leg_is_wide(leg) {
        if n < 16 {
            return Err(format!(
                "wide effect-vm leg too short for the 8-felt commit tail: {n} PIs < 16"
            ));
        }
        let before: [BabyBear; 8] = leg.sub_public_inputs[n - 16..n - 8]
            .try_into()
            .expect("slice of len 8");
        let after: [BabyBear; 8] = leg.sub_public_inputs[n - 8..n]
            .try_into()
            .expect("slice of len 8");
        Ok((before, after))
    } else {
        if n <= effect_pi::NEW_COMMIT {
            return Err(format!(
                "narrow effect-vm leg too short for its commit felts: {n} PIs"
            ));
        }
        let mut before = [BabyBear::ZERO; 8];
        let mut after = [BabyBear::ZERO; 8];
        before[0] = leg.sub_public_inputs[effect_pi::OLD_COMMIT];
        after[0] = leg.sub_public_inputs[effect_pi::NEW_COMMIT];
        Ok((before, after))
    }
}

/// An 8-felt commit anchor as one hex string (8 lanes × 8 hex chars).
fn commit_hex(felts: &[BabyBear; 8]) -> String {
    felts.iter().map(|f| format!("{:08x}", f.0)).collect()
}

/// The embed field reporting the verdict — the honest register, pure so tests read it.
pub fn verdict_text(check: &Result<ProofCheck, String>) -> String {
    match check {
        Ok(c) if c.verified => format!(
            "✓ **Verifies under VK `{vk}…` — checked just now, not trusted.** This bot ran the \
             same audited Plonky3 verifier a remote peer would (`dregg_sdk::verify_full_turn`) \
             over the fetched bytes.\nLegs verified: {legs}.\nState binding (the proof's own \
             8-felt anchors): `{old}…` → `{new}…`. Binding those to the chain's canonical \
             committed state is the checkpoint's job — that part you can also check yourself \
             (below).",
            vk = &c.vk_hex[..16.min(c.vk_hex.len())],
            legs = if c.legs.is_empty() {
                "(none)".to_string()
            } else {
                c.legs.join(", ")
            },
            old = &c.old_commit[..16.min(c.old_commit.len())],
            new = &c.new_commit[..16.min(c.new_commit.len())],
        ),
        Ok(c) => format!(
            "✗ **The fetched bytes DO NOT verify** under VK `{vk}…` — do not trust this \
             artifact.\n`{detail}`",
            vk = &c.vk_hex[..16.min(c.vk_hex.len())],
            detail = c.detail,
        ),
        Err(e) => format!("✗ **Could not verify the fetched bytes:** {e}"),
    }
}

/// The re-check-it-yourself incantation — verification must be possible OUTSIDE the bot.
pub fn offline_recheck_text(node_url: &str, turn_hash_hex: &str) -> String {
    format!(
        "```\ncurl {base}/api/turn/{turn_hash_hex}/proof | jq -r .proof_hex\n```\nDecode the hex \
         and hand the bytes to `dregg_sdk::verify_full_turn` (`sdk/src/full_turn_proof.rs`) — \
         the same call this bot just made. A spend turn's freshness leg additionally wants the \
         canonical revocation root pinned (`verify_full_turn_bound`).",
        base = node_url.trim_end_matches('/'),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Garbage hex / not-a-proof bytes fail LOUDLY (an Err naming why), never a silent ✅.
    #[test]
    fn garbage_bytes_fail_loudly() {
        let err =
            check_proof_hex("zz-not-hex", &"00".repeat(32)).expect_err("non-hex must not verify");
        assert!(err.contains("does not decode"), "{err}");

        let err = check_proof_hex(&"ab".repeat(40), &"00".repeat(32))
            .expect_err("random bytes must not parse as a composed proof");
        assert!(err.contains("do not parse"), "{err}");
    }

    /// The verdict register is honest in all three shapes: verified / refuted / uncheckable.
    #[test]
    fn the_verdict_text_carries_the_honest_register() {
        let ok = ProofCheck {
            verified: true,
            vk_hex: "de3f".repeat(16),
            legs: vec!["effect-vm-rotated".into(), "membership".into()],
            old_commit: "11".repeat(32),
            new_commit: "22".repeat(32),
            detail: String::new(),
        };
        let text = verdict_text(&Ok(ok.clone()));
        assert!(text.contains("checked just now, not trusted"), "{text}");
        assert!(text.contains("effect-vm-rotated"), "{text}");

        let bad = ProofCheck {
            verified: false,
            detail: "MainProofInvalid".into(),
            ..ok
        };
        let text = verdict_text(&Ok(bad));
        assert!(text.contains("DO NOT verify"), "{text}");
        assert!(text.contains("MainProofInvalid"), "{text}");

        let text = verdict_text(&Err("boom".into()));
        assert!(text.contains("Could not verify"), "{text}");
    }

    /// The offline incantation names the real route + the real verifier entry point.
    #[test]
    fn the_offline_recheck_names_the_route_and_the_verifier() {
        let text = offline_recheck_text("http://node:8080/", &"ab".repeat(32));
        assert!(text.contains("/api/turn/"), "{text}");
        assert!(text.contains("verify_full_turn"), "{text}");
        assert!(!text.contains("8080//"), "trailing slash trimmed: {text}");
    }
}
