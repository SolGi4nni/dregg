//! **Actually VERIFY the fetched full-turn STARK** (bot-excellence backlog Tier-2 #11).
//!
//! `/proof turn` (and `/explorer proof`) fetch a committed turn's proof artifact off the node
//! (`/api/turn/{hash}/proof`) and used to present it trust-me: size + hex head + "Attached ✅".
//! That is the one artifact whose entire purpose is that ANYONE can check it. This module is
//! the check: the bot deserializes the served bytes into the real composed full-turn proof and
//! runs the SAME audited verifier a remote peer would — [`dregg_sdk::verify_full_turn`], the
//! Plonky3 batch-STARK verify of every attached leg plus the cross-leg PI bindings — right
//! there in the handler, and reports what that did and did not settle, or an honest failure.
//! It is NOT a "this turn happened" verdict, and the surface must never render as one: read
//! the two seams below before touching [`verdict_text`].
//!
//! ## What is (and is not) established here
//!
//! * **Established:** the bytes ARE a sound composed STARK. Every attached leg
//!   (effect-vm-rotated / membership / cap-membership) verifies under the audited Plonky3
//!   verifier, the legs chain leg-to-leg (each leg's BEFORE anchor equals the previous leg's
//!   AFTER, the `chain_adjacency` tooth, which DOES fire), and the object binds one composed
//!   VK hash. A garbage or tampered artifact fails loudly.
//! * **NOT established, seam 1 (state anchors are the proof's own).** [`check_proof_hex`] reads
//!   the before/after 8-felt commits OUT of the artifact ([`extract_commits`]) and hands those
//!   same values back to `verify_full_turn` as its `expected_*` arguments. Inside,
//!   `verify_full_turn_bound` recomputes `proof_old_commit`/`proof_new_commit` by the IDENTICAL
//!   rule (first effect-vm leg's BEFORE, last leg's AFTER, wide-vs-narrow by `vk_hash_is_wide`)
//!   and compares. So on this call site the two ENDPOINT `CommitmentMismatch` teeth
//!   (`old_commitment`, `new_commitment`) compare `x != x` and STRUCTURALLY CANNOT FIRE. They
//!   are not "a check we are choosing to trust"; they are not a check here at all. Nothing
//!   below says these anchors are the chain's canonical committed state, or that this turn is
//!   in the chain. The real binding needs a canonical `expected_old_commit` the caller obtained
//!   independently (which also carries spend freshness: the limb-26 BEFORE nullifier root is
//!   absorbed into it), and the node publishes no such value to bind to.
//! * **NOT established, seam 2 (the artifact carries no turn identity).**
//!   [`FullTurnProof::turn_hash`] is DECORATIVE on this path. `prove_full_turn` never writes
//!   the turn hash into any leg's PI (`pi::TURN_HASH_BASE` appears nowhere in
//!   `sdk/src/full_turn_proof.rs`) and `verify_full_turn_bound` never reads
//!   `proof.turn_hash`. This module parses the turn hash out of the URL and stuffs it into the
//!   struct, and nothing ever looks at it. A proof for turn B, served under turn A's URL,
//!   verifies here identically. (Two OTHER producers do fill the slot honestly and check it:
//!   `turn-prover/src/proven_receipt.rs` writes `canonical_32_to_felts_4(&turn_hash)` into
//!   `dpis[TURN_HASH_BASE..+4]`, and `verifier`'s `check_receipt_pi_binding` compares exactly
//!   that. `prove_full_turn` simply does not.)
//!
//! Both seams are reported to the reader at runtime, not only here: [`check_proof_hex`] fills
//! [`ProofCheck::unbound`] and [`verdict_text`] prints it under the verdict.

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
    /// The composed circuit's VK hash (hex) the proof binds — which circuit the legs were
    /// checked against, not which turn they describe.
    pub vk_hex: String,
    /// The attached sub-proof legs, by label (what was actually verified).
    pub legs: Vec<String>,
    /// The pre-state 8-felt commit anchor the ARTIFACT PUBLISHES (hex lanes). Read out of the
    /// proof by [`extract_commits`], never independently obtained: it is what the prover said,
    /// not what the chain committed.
    pub published_old_commit: String,
    /// The post-state 8-felt commit anchor the ARTIFACT PUBLISHES (hex lanes). Same provenance
    /// caveat as [`ProofCheck::published_old_commit`].
    pub published_new_commit: String,
    /// What this check did NOT establish, populated by [`check_proof_hex`] itself (see
    /// [`unbound_claims`]) so the surface cannot drift away from the code. Printed under the
    /// verdict by [`verdict_text`].
    pub unbound: Vec<String>,
    /// The verifier's failure detail when `verified == false` (empty on success).
    pub detail: String,
}

/// **The seams, as data.** What running [`check_proof_hex`] on a served artifact does NOT
/// establish, in the order a reader should meet them. This is a function, not a constant
/// string, because it is the code's own account of its call site: seam 1 is a consequence of
/// which arguments [`check_proof_hex`] passes to `verify_full_turn`, and seam 2 of what
/// `prove_full_turn` writes into the PI vector. Change either and this list is wrong.
pub fn unbound_claims() -> Vec<String> {
    vec![
        "State anchors are the proof's own. The before/after commits above were read OUT of \
         this artifact and handed straight back to the verifier as the values it should expect, \
         so its two endpoint commitment checks compared each value against itself and could not \
         fire. Nothing here says those anchors are the chain's canonical committed state for \
         this turn, or that this turn is in the chain at all. (The leg-to-leg adjacency check \
         is real and did run.)"
            .to_string(),
        "The artifact carries no turn identity. The full-turn prover never writes the turn hash \
         into any leg's public inputs, and the verifier never reads it, so these bytes are not \
         bound to the turn they were fetched for. A proof of a DIFFERENT turn, served under \
         this turn's URL, would verify here identically."
            .to_string(),
    ]
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
        // (has_non_revocation RETIRED — felt-width #11 fold-in: freshness is
        // in-circuit on the rotated note-spend leg, not a separate leg.)
        has_cap_membership: legs.iter().any(|l| l == "cap-membership"),
    };

    // SEAM 1, at its source: these are the artifact's OWN anchors, and the next call hands them
    // back to the verifier as the values it should expect. `verify_full_turn_bound` derives its
    // `proof_old_commit` / `proof_new_commit` by the identical rule, so its two endpoint
    // `CommitmentMismatch` teeth compare `x != x` here and cannot fire. There is nothing else
    // to pass: the node's `/api/turn/{hash}/proof` serves `{turn_hash, proof_len, proof_hex}`
    // and no commitment, and no endpoint publishes a per-turn canonical 8-felt state commit.
    let (published_old, published_new) = extract_commits(&composed.sub_proofs)?;
    let vk_hex = hex::encode(composed.composed_vk_hash);

    // SEAM 2, at its source: this field is decorative. Nothing downstream reads it, and no leg's
    // PI carries the turn hash, so parsing it here binds the artifact to nothing.
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
    let (verified, detail) = match verify_full_turn(&proof, published_old, published_new) {
        Ok(()) => (true, String::new()),
        Err(e) => (false, format!("{e:?}")),
    };
    Ok(ProofCheck {
        verified,
        vk_hex,
        legs,
        published_old_commit: commit_hex(&published_old),
        published_new_commit: commit_hex(&published_new),
        unbound: unbound_claims(),
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
///
/// Because this is the SAME rule `verify_full_turn_bound` applies internally, feeding this
/// result back in as the verifier's `expected_*` makes its endpoint comparison reflexive. That
/// is seam 1 in the module docblock, and [`unbound_claims`] reports it.
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
///
/// The success arm leads with the LIMIT, not with a checkmark: what passed here is a check on
/// the bytes, and the two facts a reader actually wants (this is the chain's state, this is
/// THIS turn) are both in [`ProofCheck::unbound`]. See the module docblock for why.
pub fn verdict_text(check: &Result<ProofCheck, String>) -> String {
    match check {
        Ok(c) if c.verified => format!(
            "**A LIMITED CHECK PASSED. This is not a claim that the turn happened, nor that \
             these are its bytes.**\nEstablished: every attached leg ({legs}) verifies under the \
             same audited Plonky3 verifier a remote peer would run \
             (`dregg_sdk::verify_full_turn`), the legs chain leg to leg (each leg's BEFORE \
             anchor equals the previous leg's AFTER), and the object binds the composed VK \
             `{vk}…`. Checked just now over the fetched bytes, not trusted.\nAnchors the \
             artifact PUBLISHES (the prover's claim, not the chain's): `{old}…` → \
             `{new}…`.\nNOT established:\n{unbound}",
            vk = &c.vk_hex[..16.min(c.vk_hex.len())],
            legs = if c.legs.is_empty() {
                "(none)".to_string()
            } else {
                c.legs.join(", ")
            },
            old = &c.published_old_commit[..16.min(c.published_old_commit.len())],
            new = &c.published_new_commit[..16.min(c.published_new_commit.len())],
            unbound = if c.unbound.is_empty() {
                "(the unbound list is EMPTY, which is itself a bug: this call site has two \
                 standing seams, see `proof_verify`'s docblock)"
                    .to_string()
            } else {
                c.unbound
                    .iter()
                    .map(|u| format!("• {u}"))
                    .collect::<Vec<_>>()
                    .join("\n")
            },
        ),
        Ok(c) => format!(
            "✗ **The fetched bytes DO NOT verify** under VK `{vk}…`. Do not trust this \
             artifact.\n`{detail}`",
            vk = &c.vk_hex[..16.min(c.vk_hex.len())],
            detail = c.detail,
        ),
        Err(e) => format!("✗ **Could not verify the fetched bytes:** {e}"),
    }
}

/// The re-check-it-yourself incantation — verification must be possible OUTSIDE the bot.
///
/// It also says what to pass, because the interesting part of `verify_full_turn` is its
/// ARGUMENTS: reproduce the bot's call exactly and you reproduce the bot's seam.
pub fn offline_recheck_text(node_url: &str, turn_hash_hex: &str) -> String {
    format!(
        "```\ncurl {base}/api/turn/{turn_hash_hex}/proof | jq -r .proof_hex\n```\nDecode the hex \
         and hand the bytes to `dregg_sdk::verify_full_turn` (`sdk/src/full_turn_proof.rs`), \
         the same call this bot just made. Mind the ARGUMENTS: it takes the expected before and \
         after 8-felt commits from YOU. Read them out of the proof (all this bot can do, since \
         the node serves no commitment alongside the artifact) and the endpoint check compares \
         each value against itself. It becomes a real check only when you pass an \
         `expected_old_commit` you obtained independently, which is also what binds spend \
         freshness (in-circuit already) to the canonical spent set. Nothing you pass binds the \
         artifact to a turn hash; no leg publishes one.",
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

    fn a_passing_check() -> ProofCheck {
        ProofCheck {
            verified: true,
            vk_hex: "de3f".repeat(16),
            legs: vec!["effect-vm-rotated".into(), "membership".into()],
            published_old_commit: "11".repeat(32),
            published_new_commit: "22".repeat(32),
            unbound: unbound_claims(),
            detail: String::new(),
        }
    }

    /// The verdict register is honest in all three shapes: verified / refuted / uncheckable.
    #[test]
    fn the_verdict_text_carries_the_honest_register() {
        let ok = a_passing_check();
        let text = verdict_text(&Ok(ok.clone()));
        assert!(
            text.contains("Checked just now over the fetched bytes, not trusted"),
            "{text}"
        );
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

    /// **The anti-checkmark test.** A passing check must NOT read as "this proof is verified":
    /// the limit comes FIRST, the old unqualified "Verifies under VK" claim is gone, and BOTH
    /// standing seams are printed in the body. If someone re-shortens this copy to a checkmark,
    /// this fails.
    #[test]
    fn a_passing_verdict_leads_with_the_limit_and_prints_both_seams() {
        let text = verdict_text(&Ok(a_passing_check()));

        assert!(
            !text.contains("Verifies under VK"),
            "the unqualified verified-claim came back: {text}"
        );
        let limit = text
            .find("A LIMITED CHECK PASSED")
            .expect("the success arm must state the limit");
        assert_eq!(limit, 2, "the limit must be the FIRST thing read: {text}");
        assert!(
            limit < text.find("Established").expect("what passed is named"),
            "the limit must precede the claim: {text}"
        );
        assert!(text.contains("NOT established:"), "{text}");

        // Seam 1: the reflexive endpoint comparison.
        assert!(
            text.contains("compared each value against itself"),
            "seam 1 (self-compared anchors) missing: {text}"
        );
        // Seam 2: no turn-hash binding.
        assert!(
            text.contains(
                "A proof of a DIFFERENT turn, served under this turn's URL, would \
                           verify here identically."
            ),
            "seam 2 (no turn identity) missing: {text}"
        );
        for u in unbound_claims() {
            assert!(
                text.contains(&u),
                "unbound entry dropped from the verdict: {u}"
            );
        }
    }

    /// The seam list is EXACTLY the two standing seams, and `ProofCheck` carries it as DATA
    /// (not as prose in one format string a later edit can quietly drop).
    #[test]
    fn the_unbound_list_names_exactly_the_two_standing_seams() {
        let unbound = unbound_claims();
        assert_eq!(unbound.len(), 2, "{unbound:#?}");
        assert!(
            unbound[0].contains("read OUT of this artifact")
                && unbound[0].contains("could not fire"),
            "entry 0 must name the reflexive endpoint comparison: {}",
            unbound[0]
        );
        assert!(
            unbound[1].contains("no turn identity")
                && unbound[1].contains("not bound to the turn they were fetched for"),
            "entry 1 must name the missing turn-hash binding: {}",
            unbound[1]
        );
        // And a live `check_proof_hex` populates the field from this same function, so the
        // surface cannot report fewer seams than the code has.
        assert_eq!(a_passing_check().unbound, unbound);
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
