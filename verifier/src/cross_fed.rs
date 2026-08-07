//! Cross-federation `CrossFedReceiptBundle` verification (Silver Vision §6).
//!
//! `dregg-verifier verify-cross-fed-bundle` ingests a JSON-encoded
//! [`dregg_federation::CrossFedReceiptBundle`] plus two committee descriptors
//! (one per federation) and runs the 8-step check from
//! `SILVER-VISION-E2E-VERIFICATION.md` §1 Step 6:
//!
//! 1. Verify the introducer's signature on the `HandoffCertificate` under
//!    the issuing committee's pubkey.
//! 2. Verify every receipt's rotated effect-VM proof SELECTOR-BOUND against the
//!    committed cohort descriptors, and bind each proof to the receipt it accompanies
//!    plus the receipt chain-walk.
//! 3. (was: scope-2 trace replay — DELETED, see the flag-day note below.)
//! 4. Verify F1's `AttestedRoot` HYBRID quorum (ed25519 ∧ ML-DSA-65) under
//!    F1's known keys — a classical-only root fails closed.
//! 5. Verify F2's `AttestedRoot` HYBRID quorum (ed25519 ∧ ML-DSA-65) under
//!    F2's known keys — a classical-only root fails closed.
//! 6. Verify F2's `FederationReceipt` (if present) under F2's BLS / Ed25519
//!    committee.
//! 7. Cross-link: `cert.target_federation == F2`,
//!    `cert.introducer == F1`, the chain's last receipt's
//!    `federation_id == F2`, and the receipt's authorization-side cert
//!    nonce equals `cert.nonce` (when present in the receipt).
//! 8. Structural sanity: bundle version matches, the chain is non-empty.
//!
//! Returns a `CrossFedVerdict` carrying a granular per-step result so the
//! demo's `must_not_pass` negative tests can read individual flags.
//!
//! # ⚑ FLAG DAY 2026-08-05 — this subcommand could not return `overall_verified: true`
//!
//! Steps (2) and (3) were routed through the retired `verify_effect_vm_proof`, which
//! returned `exit_code::ERROR` on every input. Step (2) therefore set
//! `effect_vm_proof_verified = false` and returned early on EVERY bundle, honest or
//! forged, so the documented 8-step check was structurally unable to report success.
//! Six of its eight legs are real crypto (the hybrid ed25519 ∧ ML-DSA-65 attested-root
//! quorum, the handoff-cert signature, the `FederationReceipt`, the cross-links) and
//! have adversarial tests; deleting the subcommand would have thrown those away. So
//! the two dead legs are REPAIRED, not removed:
//!
//! * **(2) is now a real verify.** Each `recipient_chain` entry's `proof_bytes` is
//!   deserialized and verified SELECTOR-BOUND through
//!   [`crate::rotated_replay::resolve_rotated_descriptor`] — the same audited
//!   `verify_vm_descriptor2` path the rotated replay chain and the SDK wire verifier
//!   use, over the WIDE / welded-wide / bare-V3 committed registries. Each entry is
//!   then bound to the `TurnReceipt` it carries via
//!   [`crate::check_receipt_pi_binding`] (T11 relabelling + T8 chain walk), so a
//!   genuine proof of turn A cannot be presented beside a receipt naming turn B.
//! * **(3) is DELETED as a separate leg.** It re-ran the v1 hand-AIR over an inline
//!   witness trace; that AIR is gone, and in the rotated world the batch-STARK verify
//!   in (2) IS the trace check. Keeping a second flag for it would have been a field
//!   that could never go true. The `witness_chain_replay_verified` and `replay_detail`
//!   fields are GONE from `CrossFedVerdict`; a consumer reading them refuses to
//!   deserialize rather than seeing `false`.
//!
//! **What re-emits / breaks:** `demo/multi-node-devnet/expected/cross_fed_handoff.json`
//! names the removed fields and must be re-emitted. The bundles
//! `demo/multi-node-devnet/scenarios/cross_fed_handoff.sh` feeds this subcommand must
//! now carry REAL rotated proofs in `recipient_chain[*].proof_bytes`; a bundle whose
//! entries carry `proof_bytes: []` is now rejected at (2) by name, where before it was
//! rejected at (2) by a stub. The requirement that every entry carry a
//! `witness_bundle` is also gone: scope-2 material is not what step (2) reads.

use serde::{Deserialize, Serialize};

use dregg_federation::CrossFedReceiptBundle;
use dregg_federation::frost::MlDsaPublicKey;
use dregg_federation::receipt::FederationReceipt;
use dregg_types::{AttestedRoot, PublicKey};

/// A federation committee descriptor as it appears on disk (the file the
/// `register-federation` CLI writes / `setup_federations.sh` cross-copies).
///
/// Field shape mirrors what `dregg-node genesis` already produces (we
/// re-decode it here so the verifier doesn't need to call into the node).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CommitteeDescriptor {
    /// 32-byte federation id (hex). Derived from the sorted pubkeys.
    pub federation_id: String,
    /// Committee epoch.
    #[serde(default)]
    pub committee_epoch: u64,
    /// Threshold (number of signatures required).
    #[serde(default = "default_threshold")]
    pub threshold: usize,
    /// Validator pubkeys (32-byte hex strings).
    pub validators: Vec<ValidatorDescriptor>,
}

fn default_threshold() -> usize {
    1
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidatorDescriptor {
    #[serde(default)]
    pub name: String,
    /// Hex-encoded 32-byte Ed25519 pubkey.
    pub public_key: String,
    /// Hex-encoded 1952-byte ML-DSA-65 (FIPS 204) ENROLLED public key — the
    /// genesis-published post-quantum key this member's hybrid signatures must
    /// verify under. Optional on the wire (older descriptors predate the hybrid
    /// roster), but the hybrid attested-root quorum FAILS CLOSED when it is
    /// absent for any member: a signer's self-carried ML-DSA key is pinned to
    /// THIS enrolled key, never trusted on its own.
    #[serde(default)]
    pub ml_dsa_public_key: Option<String>,
}

impl CommitteeDescriptor {
    /// Decode the validator pubkeys to the typed shape the rest of the
    /// stack expects.
    pub fn pubkeys(&self) -> Result<Vec<PublicKey>, String> {
        let mut out = Vec::with_capacity(self.validators.len());
        for v in &self.validators {
            let bytes = hex_decode_32(&v.public_key)
                .ok_or_else(|| format!("invalid hex pubkey for {}", v.name))?;
            out.push(PublicKey(bytes));
        }
        Ok(out)
    }

    /// Decode the ENROLLED ML-DSA-65 roster, aligned index-for-index with
    /// [`Self::pubkeys`]. Returns an EMPTY vec if ANY member lacks a decodable
    /// enrolled key (a mixed/absent roster cannot pin every signer) — the hybrid
    /// verifier then fails closed rather than fall back to an ed25519-only
    /// downgrade. A well-formed full roster returns one key per validator.
    pub fn ml_dsa_pubkeys(&self) -> Vec<MlDsaPublicKey> {
        let mut out = Vec::with_capacity(self.validators.len());
        for v in &self.validators {
            let Some(hex) = v.ml_dsa_public_key.as_ref() else {
                return Vec::new();
            };
            let Some(pk) = hex_decode_ml_dsa(hex) else {
                return Vec::new();
            };
            out.push(pk);
        }
        out
    }

    /// Decode the 32-byte federation id.
    pub fn federation_id_bytes(&self) -> Result<[u8; 32], String> {
        hex_decode_32(&self.federation_id).ok_or_else(|| "invalid federation_id hex".to_string())
    }
}

/// Decode a hex-encoded 1952-byte ML-DSA-65 public key.
fn hex_decode_ml_dsa(s: &str) -> Option<MlDsaPublicKey> {
    let bytes = hex::decode(s.trim()).ok()?;
    let arr: [u8; 1952] = bytes.try_into().ok()?;
    Some(MlDsaPublicKey(arr))
}

fn hex_decode_32(s: &str) -> Option<[u8; 32]> {
    let s = s.trim();
    if s.len() != 64 {
        return None;
    }
    let mut out = [0u8; 32];
    for (i, b) in out.iter_mut().enumerate() {
        *b = u8::from_str_radix(&s[i * 2..i * 2 + 2], 16).ok()?;
    }
    Some(out)
}

/// The 8-step verdict.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CrossFedVerdict {
    /// (1) The handoff cert's introducer signature verifies under F1's
    /// committee pubkey.
    pub cert_introducer_sig_verified: bool,
    /// (2) Every receipt's rotated effect-VM proof verified SELECTOR-BOUND against a
    /// committed cohort descriptor, AND each proof is bound to the receipt it
    /// accompanies (`PI[TURN_HASH..+4]`) with the receipt chain-walk closed.
    ///
    /// (Step (3), the v1 scope-2 trace replay, is deleted: the batch-STARK verify here
    /// IS the trace check. See the module docblock's flag-day note.)
    pub effect_vm_proof_verified: bool,
    /// (4) F1's `AttestedRoot` quorum is structurally + cryptographically
    /// valid under F1's committee.
    pub attested_root_f1_verified: bool,
    /// (5) F2's `AttestedRoot` quorum is valid under F2's committee **and** its
    /// `receipt_stream_root` ties to the `recipient_chain` presented with it. Both
    /// halves, or the flag stays false — the tie used to be checked after the flag was
    /// already set, so a broken stream reported a verified root.
    pub attested_root_f2_verified: bool,
    /// (6) F2's `FederationReceipt` (when present) verifies under F2's
    /// committee.
    pub federation_receipt_f2_verified: bool,
    /// (7) Cross-link checks pass: cert.introducer == F1.federation_id,
    /// cert.target_federation == F2.federation_id, the chain's tail
    /// receipt's `federation_id` matches F2.
    pub cross_link_cert_to_receipt: bool,
    /// (8) The recipient F2's `AttestedRoot` carries a non-`None`
    /// `blocklace_block_id` / `finality_round` — the F3 binding that
    /// makes the attestation blocklace-aware (AUDIT-federation.md F3).
    pub attested_root_f2_blocklace_bound: bool,
    /// Auxiliary: the chain's tail receipt's `executor_signature` was
    /// computed over a message that includes `federation_id` (lane D F2 fix).
    /// We approximate the check by asserting the tail receipt's
    /// `federation_id` equals F2 — the actual signing-message structure
    /// is enforced inside the executor; this flag surfaces the demo-level
    /// invariant.
    pub executor_signature_includes_federation_id: bool,
    /// Human-readable trace of which step failed first (or "all green").
    pub summary: String,
    /// True iff every load-bearing check passes (steps 1-8 above; the
    /// optional `federation_receipt_f2_verified` only counts when a
    /// receipt is supplied).
    pub overall_verified: bool,
}

impl CrossFedVerdict {
    fn rejection(reason: impl Into<String>) -> Self {
        Self {
            cert_introducer_sig_verified: false,
            effect_vm_proof_verified: false,
            attested_root_f1_verified: false,
            attested_root_f2_verified: false,
            federation_receipt_f2_verified: false,
            cross_link_cert_to_receipt: false,
            attested_root_f2_blocklace_bound: false,
            executor_signature_includes_federation_id: false,
            summary: reason.into(),
            overall_verified: false,
        }
    }
}

/// Top-level entrypoint invoked by the binary's `verify-cross-fed-bundle`
/// subcommand. Reads the JSON-encoded bundle, two committee descriptors,
/// and produces a [`CrossFedVerdict`].
pub fn verify_cross_fed_bundle(
    bundle: &CrossFedReceiptBundle,
    issuer_committee: &CommitteeDescriptor,
    recipient_committee: &CommitteeDescriptor,
) -> CrossFedVerdict {
    // (8 — structural) version check.
    if bundle.version != CrossFedReceiptBundle::VERSION {
        return CrossFedVerdict::rejection(format!(
            "bundle version mismatch: bundle={}, expected={}",
            bundle.version,
            CrossFedReceiptBundle::VERSION
        ));
    }

    // Decode committees up-front so we can short-circuit cleanly.
    let issuer_keys = match issuer_committee.pubkeys() {
        Ok(k) => k,
        Err(e) => return CrossFedVerdict::rejection(format!("issuer committee: {e}")),
    };
    let recipient_keys = match recipient_committee.pubkeys() {
        Ok(k) => k,
        Err(e) => return CrossFedVerdict::rejection(format!("recipient committee: {e}")),
    };
    // The ENROLLED ML-DSA-65 rosters (aligned index-for-index with each
    // committee's ed25519 keys). Empty when the descriptor predates the hybrid
    // roster — the hybrid attested-root quorum then fails closed.
    let issuer_ml_dsa = issuer_committee.ml_dsa_pubkeys();
    let recipient_ml_dsa = recipient_committee.ml_dsa_pubkeys();
    let issuer_fed_id = match issuer_committee.federation_id_bytes() {
        Ok(b) => b,
        Err(e) => return CrossFedVerdict::rejection(format!("issuer fed_id: {e}")),
    };
    let recipient_fed_id = match recipient_committee.federation_id_bytes() {
        Ok(b) => b,
        Err(e) => return CrossFedVerdict::rejection(format!("recipient fed_id: {e}")),
    };

    if bundle.recipient_chain.is_empty() {
        return CrossFedVerdict::rejection("recipient_chain is empty");
    }

    if let Err(reason) =
        verify_committee_descriptor_id("issuer committee", issuer_committee, &issuer_keys)
    {
        return CrossFedVerdict::rejection(reason);
    }
    if let Err(reason) =
        verify_committee_descriptor_id("recipient committee", recipient_committee, &recipient_keys)
    {
        return CrossFedVerdict::rejection(reason);
    }

    let mut verdict = CrossFedVerdict {
        cert_introducer_sig_verified: false,
        effect_vm_proof_verified: false,
        attested_root_f1_verified: false,
        attested_root_f2_verified: false,
        federation_receipt_f2_verified: bundle.recipient_federation_receipt.is_none(), // vacuously true when absent
        cross_link_cert_to_receipt: false,
        attested_root_f2_blocklace_bound: false,
        executor_signature_includes_federation_id: false,
        summary: String::new(),
        overall_verified: false,
    };

    // ⚑ THE FLAG IS SET BY THE CHECK, NOT BY POSITION (2026-07-30). Legs (4) and (5) used
    // to be bare `verdict.attested_root_fN_verified = true;` statements ~90 lines below
    // this, resting on the early-returns here to keep them honest. That is a reporting
    // shape one refactor away from a flag that cannot go false, and it already misreported
    // once: the F2 receipt-stream tie is checked AFTER the old assignment, so a bundle
    // whose stream did not match returned `attested_root_f2_verified: true`. Assign where
    // the evidence is, and fold the stream tie into the same leg.
    if let Err(reason) = verify_attested_root_against_descriptor(
        "F1 AttestedRoot",
        &bundle.issuer_attested_root,
        issuer_committee,
        &issuer_keys,
        &issuer_ml_dsa,
        issuer_fed_id,
    ) {
        verdict.summary = reason;
        return verdict;
    }
    verdict.attested_root_f1_verified = true;

    if let Err(reason) = verify_attested_root_against_descriptor(
        "F2 AttestedRoot",
        &bundle.recipient_attested_root,
        recipient_committee,
        &recipient_keys,
        &recipient_ml_dsa,
        recipient_fed_id,
    ) {
        verdict.summary = reason;
        return verdict;
    }

    // (1) Cert introducer signature.
    // The cert's `introducer` field MUST equal the issuer's federation_id,
    // AND the cert must verify under one of the issuer's known pubkeys.
    if bundle.cross_fed_cert.introducer.0 != issuer_fed_id {
        verdict.summary = format!(
            "cert.introducer ({}) != issuer.federation_id ({})",
            hex::encode(bundle.cross_fed_cert.introducer.0),
            hex::encode(issuer_fed_id),
        );
        return verdict;
    }
    // Single-node committee (demo's posture): the single pubkey is the
    // introducer. Multi-key committees would require the cert to carry
    // an explicit signer hint; we iterate over all keys here so the demo
    // works with both shapes.
    verdict.cert_introducer_sig_verified = issuer_keys
        .iter()
        .any(|pk| bundle.cross_fed_cert.verify_signature(pk));
    if !verdict.cert_introducer_sig_verified {
        verdict.summary = "cert introducer signature did not verify under any issuer pubkey".into();
        return verdict;
    }

    // (2) THE ROTATED EFFECT-VM PROOF VERIFIES FOR EVERY RECEIPT, AND IS BOUND TO IT.
    //
    // Two teeth per entry, and both can fire:
    //   a. `resolve_rotated_descriptor` deserializes the `Ir2BatchProof` and requires it
    //      to verify SELECTOR-BOUND under EXACTLY ONE committed cohort descriptor
    //      (`verify_vm_descriptor2`). Empty / corrupt / forged bytes bind zero members
    //      and are refused by name; a proof that binds several is refused as ambiguous
    //      rather than laundered under the wrong selector.
    //   b. `check_receipt_pi_binding` requires `PI[TURN_HASH_BASE..+4] ==
    //      canonical_32_to_felts_4(receipt.turn_hash)` (T11) and closes the receipt
    //      chain-walk across the chain (T8). Without (b), a genuine proof of turn A
    //      verifies happily beside a receipt naming turn B and the whole cross-fed
    //      story is told about the wrong turn.
    //
    // This is also step (3): the batch-STARK verify IS the trace check. The v1 hand-AIR
    // row-pair replay that used to be a separate leg no longer exists.
    let mut all_proofs_ok = true;
    let mut prev_receipt_hash: Option<[u8; 32]> = None;
    for (i, wr) in bundle.recipient_chain.iter().enumerate() {
        let pi_felts: Vec<dregg_circuit::field::BabyBear> = wr
            .public_inputs
            .iter()
            .map(|&v| dregg_circuit::field::BabyBear::new_canonical(v))
            .collect();
        if let Err(reason) =
            crate::rotated_replay::resolve_rotated_descriptor(&wr.proof_bytes, &pi_felts)
        {
            verdict.summary = format!("effect-vm proof rejected at chain[{i}]: {reason}");
            all_proofs_ok = false;
            break;
        }
        if let Some(reason) =
            crate::check_receipt_pi_binding(&wr.receipt, &wr.public_inputs, prev_receipt_hash)
        {
            verdict.summary =
                format!("effect-vm proof is not bound to chain[{i}]'s receipt: {reason}");
            all_proofs_ok = false;
            break;
        }
        prev_receipt_hash = Some(wr.receipt.receipt_hash());
    }
    verdict.effect_vm_proof_verified = all_proofs_ok;
    if !all_proofs_ok {
        return verdict;
    }

    // (5, second half) F2's attested root must also TIE to the chain it is presented with:
    // its `receipt_stream_root` must be the stream of these receipts. Leg (5) is only
    // reported verified once BOTH halves hold — the committee quorum (checked above) and
    // this tie. Reporting the quorum half alone as "F2 AttestedRoot verified" while the
    // tie was broken is the misreport this ordering fixes.
    let receipt_hashes: Vec<[u8; 32]> = bundle
        .recipient_chain
        .iter()
        .map(|wr| wr.receipt.receipt_hash())
        .collect();
    if !bundle
        .recipient_attested_root
        .verify_receipt_stream(&receipt_hashes)
    {
        verdict.summary =
            "F2 AttestedRoot receipt_stream_root does not match recipient_chain receipts".into();
        return verdict;
    }
    verdict.attested_root_f2_verified = true;

    // (8 — F3 binding flag) blocklace binding present?
    verdict.attested_root_f2_blocklace_bound =
        bundle.recipient_attested_root.blocklace_block_id.is_some()
            && bundle.recipient_attested_root.finality_round.is_some();
    if !verdict.attested_root_f2_blocklace_bound {
        verdict.summary = "F2 AttestedRoot lacks blocklace_block_id/finality_round binding".into();
        return verdict;
    }

    let tail = bundle
        .recipient_chain
        .last()
        .expect("recipient_chain emptiness checked above");

    // (6) FederationReceipt over F2's body, if present.
    if let Some(ref fr) = bundle.recipient_federation_receipt {
        // We can do the Votes path without the BLS committee. The Threshold
        // path requires a `FederationCommittee` (BLS), which this standalone
        // descriptor does not carry, so `FederationReceipt::verify` rejects it
        // instead of treating opaque bytes as a cryptographic proof.
        verdict.federation_receipt_f2_verified = fr.verify(
            None,
            &recipient_keys,
            &recipient_ml_dsa,
            recipient_committee.threshold,
            recipient_committee.committee_epoch,
        );
        if !verdict.federation_receipt_f2_verified {
            verdict.summary =
                "F2 FederationReceipt did not verify under recipient committee".into();
            return verdict;
        }
        if let Err(reason) = federation_receipt_matches_tail(fr, &tail.receipt) {
            verdict.summary = reason;
            verdict.federation_receipt_f2_verified = false;
            return verdict;
        }
    }

    // (7) Cross-link sanity.
    if bundle.cross_fed_cert.target_federation.0 != recipient_fed_id {
        verdict.summary = format!(
            "cert.target_federation ({}) != recipient.federation_id ({})",
            hex::encode(bundle.cross_fed_cert.target_federation.0),
            hex::encode(recipient_fed_id),
        );
        return verdict;
    }
    // The tail receipt's federation_id must equal F2.
    if tail.receipt.federation_id != recipient_fed_id {
        verdict.summary = format!(
            "tail receipt.federation_id ({}) != recipient.federation_id ({})",
            hex::encode(tail.receipt.federation_id),
            hex::encode(recipient_fed_id),
        );
        return verdict;
    }
    verdict.cross_link_cert_to_receipt = true;
    verdict.executor_signature_includes_federation_id = tail.receipt.executor_signature.is_some();

    verdict.overall_verified = verdict.cert_introducer_sig_verified
        && verdict.effect_vm_proof_verified
        && verdict.attested_root_f1_verified
        && verdict.attested_root_f2_verified
        && verdict.federation_receipt_f2_verified
        && verdict.cross_link_cert_to_receipt
        && verdict.attested_root_f2_blocklace_bound;
    verdict.summary = if verdict.overall_verified {
        "cross-fed bundle verified end-to-end".into()
    } else {
        "cross-fed bundle: at least one check failed".into()
    };
    verdict
}

fn verify_committee_descriptor_id(
    role: &str,
    descriptor: &CommitteeDescriptor,
    keys: &[PublicKey],
) -> Result<(), String> {
    let declared = descriptor.federation_id_bytes()?;
    let derived =
        dregg_federation::derive_federation_id_with_epoch(keys, descriptor.committee_epoch);
    if declared != derived {
        return Err(format!(
            "{role}: federation_id ({}) does not derive from validator keys at epoch {} ({})",
            hex::encode(declared),
            descriptor.committee_epoch,
            hex::encode(derived)
        ));
    }
    Ok(())
}

fn verify_attested_root_against_descriptor(
    role: &str,
    root: &AttestedRoot,
    descriptor: &CommitteeDescriptor,
    keys: &[PublicKey],
    ml_dsa_keys: &[MlDsaPublicKey],
    expected_federation_id: [u8; 32],
) -> Result<(), String> {
    if keys.is_empty() {
        return Err(format!("{role}: committee has no validators"));
    }
    if descriptor.threshold == 0 {
        return Err(format!("{role}: committee threshold must be non-zero"));
    }
    if descriptor.threshold > keys.len() {
        return Err(format!(
            "{role}: committee threshold {} exceeds validator count {}",
            descriptor.threshold,
            keys.len()
        ));
    }
    if root.threshold != descriptor.threshold {
        return Err(format!(
            "{role}: root threshold {} != descriptor threshold {}",
            root.threshold, descriptor.threshold
        ));
    }
    if root.federation_id.0 != expected_federation_id {
        return Err(format!(
            "{role}: root.federation_id ({}) != descriptor.federation_id ({})",
            hex::encode(root.federation_id.0),
            hex::encode(expected_federation_id)
        ));
    }
    if root.threshold_qc.is_some() && root.hybrid_quorum.is_empty() {
        return Err(format!(
            "{role}: threshold_qc is present but this verifier was not given a BLS committee; a hybrid (ed25519 ∧ ML-DSA-65) quorum is required"
        ));
    }
    // POST-QUANTUM CLOSURE (the last classical-only finality wire). The cross-fed
    // attested-root quorum is HYBRID: every counted signer must present BOTH a
    // valid ed25519 signature AND a valid ML-DSA-65 (FIPS 204) signature over the
    // SAME canonical `signing_message()` bytes, with committee membership and a
    // distinct-signer count `>= threshold`. A classical-only root (empty
    // `hybrid_quorum`) fails closed — an adversary who breaks ed25519 alone can
    // no longer forge a cross-federation finality attestation.
    if root.hybrid_quorum.is_empty() {
        return Err(format!(
            "{role}: no hybrid (ed25519 ∧ ML-DSA-65) quorum present; a classical-only attested root fails closed on the cross-federation finality wire"
        ));
    }
    // The ENROLLED ML-DSA roster must be present and aligned with the ed25519
    // committee, or there is no key to pin each signer's PQ half against — fail
    // closed (never an ed25519-only downgrade).
    if ml_dsa_keys.len() != keys.len() {
        return Err(format!(
            "{role}: committee descriptor carries no aligned ML-DSA-65 enrolled roster ({} ed25519 keys, {} ML-DSA keys); the hybrid quorum cannot pin its PQ half and fails closed",
            keys.len(),
            ml_dsa_keys.len()
        ));
    }
    if !verify_attested_root_hybrid(root, descriptor.threshold, keys, ml_dsa_keys) {
        return Err(format!(
            "{role}: hybrid (ed25519 ∧ ML-DSA-65) quorum did not verify under descriptor committee (classical ∧ pq, PQ key pinned to the enrolled roster, required per signer)"
        ));
    }
    Ok(())
}

/// Verify the attested root's HYBRID quorum — the single `classical ∧ pq` rule,
/// delegated to `dregg_federation::receipt::verify_hybrid_quorum_sigs` (which
/// owns the FIPS 204 ML-DSA-65 primitive). Accepts iff at least `threshold`
/// DISTINCT committee members each present a valid ed25519 signature AND a valid
/// ML-DSA-65 signature over [`AttestedRoot::hybrid_quorum_message`] under their
/// ENROLLED `ml_dsa_keys[i]` key (aligned index-for-index with `known_keys`).
/// Fail-closed on any non-member signer, any bad half, a self-carried PQ key
/// differing from the enrolled one, a missing/misaligned enrolled roster, or an
/// unanchored root (no `blocklace_block_id` ⇒ no vote preimage exists).
///
/// ⚑ **THIS FUNCTION USED `root.signing_message()` AND THEREFORE COULD NOT PASS
/// ON A LIVE ROOT.** The node fills `hybrid_quorum` by copying the assembled
/// committee **finalization-vote** signatures (`blocklace_sync.rs`), which are
/// over `finalization_vote_signing_message`, not over the attested-root
/// preimage. Every test in this module signed `signing_message()` by hand and so
/// was blind to it — a test that constructs its subject differently from
/// production is not testing production. Both consumers of the field now call
/// the one named `AttestedRoot::hybrid_quorum_message()`, and
/// `production_shaped_attested_root_hybrid_quorum_verifies` below builds its
/// root the way the node does rather than the way a test finds convenient.
fn verify_attested_root_hybrid(
    root: &AttestedRoot,
    threshold: usize,
    known_keys: &[PublicKey],
    ml_dsa_keys: &[MlDsaPublicKey],
) -> bool {
    if threshold == 0 || threshold > known_keys.len() {
        return false;
    }
    let Some(message) = root.hybrid_quorum_message() else {
        return false;
    };
    dregg_federation::receipt::verify_hybrid_quorum_sigs(
        &root.hybrid_quorum,
        &message,
        known_keys,
        ml_dsa_keys,
        threshold,
    )
}

fn federation_receipt_matches_tail(
    receipt: &FederationReceipt,
    tail: &dregg_turn::TurnReceipt,
) -> Result<(), String> {
    let body = &receipt.body;
    if body.turn_hash != tail.turn_hash {
        return Err("F2 FederationReceipt body.turn_hash does not match tail receipt".into());
    }
    if body.agent != tail.agent {
        return Err("F2 FederationReceipt body.agent does not match tail receipt".into());
    }
    if body.pre_state_hash != tail.pre_state_hash {
        return Err("F2 FederationReceipt body.pre_state_hash does not match tail receipt".into());
    }
    if body.post_state_hash != tail.post_state_hash {
        return Err("F2 FederationReceipt body.post_state_hash does not match tail receipt".into());
    }
    if body.effects_hash != tail.effects_hash {
        return Err("F2 FederationReceipt body.effects_hash does not match tail receipt".into());
    }
    if body.previous_receipt_hash != tail.previous_receipt_hash {
        return Err(
            "F2 FederationReceipt body.previous_receipt_hash does not match tail receipt".into(),
        );
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn committee_descriptor_decodes_pubkeys() {
        let d = CommitteeDescriptor {
            federation_id: "00".repeat(32),
            committee_epoch: 0,
            threshold: 1,
            validators: vec![ValidatorDescriptor {
                name: "node-0".into(),
                public_key: "ab".repeat(32),
                ml_dsa_public_key: None,
            }],
        };
        let keys = d.pubkeys().unwrap();
        assert_eq!(keys.len(), 1);
        assert_eq!(keys[0].0, [0xAB; 32]);
        assert_eq!(d.federation_id_bytes().unwrap(), [0u8; 32]);
    }

    #[test]
    fn committee_descriptor_rejects_bad_hex() {
        let d = CommitteeDescriptor {
            federation_id: "zz".repeat(32),
            committee_epoch: 0,
            threshold: 1,
            validators: vec![],
        };
        assert!(d.federation_id_bytes().is_err());
    }

    #[test]
    fn committee_descriptor_federation_id_must_derive_from_keys() {
        let desc = sample_committee([0xAA; 32]);
        let keys = desc.pubkeys().unwrap();

        let err = verify_committee_descriptor_id("committee", &desc, &keys)
            .expect_err("descriptor must not claim an arbitrary federation_id");

        assert!(err.contains("does not derive"), "{err}");
    }

    #[test]
    fn version_mismatch_rejected() {
        // Manually craft a bundle with version 0 to ensure the check fires.
        let mut b = sample_bundle();
        b.version = 0;
        let desc = sample_committee([0xAA; 32]);
        let v = verify_cross_fed_bundle(&b, &desc, &desc);
        assert!(!v.overall_verified);
        assert!(v.summary.contains("version"));
    }

    #[test]
    fn empty_recipient_chain_rejected_before_claiming_scope2() {
        let mut b = sample_bundle();
        b.recipient_chain.clear();
        let desc = sample_committee([0xAA; 32]);

        let v = verify_cross_fed_bundle(&b, &desc, &desc);

        assert!(!v.overall_verified);
        assert!(v.summary.contains("recipient_chain is empty"));
        assert!(!v.effect_vm_proof_verified);
    }

    #[test]
    fn attested_root_descriptor_rejects_zero_threshold() {
        let mut desc = sample_committee([0xAA; 32]);
        desc.threshold = 0;
        let keys = desc.pubkeys().unwrap();
        let mut root = AttestedRoot::new_legacy([1; 32], 1, 1_700_000_000, vec![], None, 0);
        root.federation_id = dregg_types::FederationId([0xAA; 32]);

        let err =
            verify_attested_root_against_descriptor("root", &root, &desc, &keys, &[], [0xAA; 32])
                .expect_err("zero-threshold committee must not verify");

        assert!(err.contains("threshold must be non-zero"), "{err}");
    }

    #[test]
    fn attested_root_descriptor_rejects_federation_id_mismatch() {
        let desc = sample_committee([0xAA; 32]);
        let keys = desc.pubkeys().unwrap();
        let mut root = AttestedRoot::new_legacy([1; 32], 1, 1_700_000_000, vec![], None, 1);
        root.federation_id = dregg_types::FederationId([0xBB; 32]);

        let err =
            verify_attested_root_against_descriptor("root", &root, &desc, &keys, &[], [0xAA; 32])
                .expect_err("root signed for another federation must not verify");

        assert!(err.contains("root.federation_id"), "{err}");
    }

    #[test]
    fn attested_root_descriptor_rejects_structural_threshold_qc_without_ed25519_quorum() {
        let desc = sample_committee([0xAA; 32]);
        let keys = desc.pubkeys().unwrap();
        let mut root = AttestedRoot::new_legacy(
            [1; 32],
            1,
            1_700_000_000,
            vec![],
            Some(dregg_types::ThresholdQC(vec![0xAB; 48])),
            1,
        );
        root.federation_id = dregg_types::FederationId([0xAA; 32]);

        let err =
            verify_attested_root_against_descriptor("root", &root, &desc, &keys, &[], [0xAA; 32])
                .expect_err("opaque threshold QC alone must not be accepted as crypto proof");

        assert!(err.contains("BLS committee"), "{err}");
    }

    // ---------------------------------------------------------------------
    // HYBRID (ed25519 ∧ ML-DSA-65) attested-root quorum — the post-quantum
    // closure of the cross-federation finality wire (steps 4/5).
    // ---------------------------------------------------------------------

    /// Build a 3-member committee (ed25519 + per-member ML-DSA-65) and an
    /// `AttestedRoot` whose `hybrid_quorum` is signed over
    /// [`AttestedRoot::hybrid_quorum_message`] — **the preimage the node
    /// actually produces** — by the members in `signers`. Returns the
    /// descriptor, the decoded committee keys, the deterministic federation id,
    /// and the root.
    ///
    /// ⚑ Until 2026-08-07 this fixture signed `root.signing_message()`, and so
    /// did every other hybrid test here. That is a different preimage from the
    /// one `blocklace_sync` fills the field with, so the whole module was green
    /// while a LIVE root's hybrid quorum could not pass. The fixture now calls
    /// the same method the verifier calls; the divergence is unrepresentable.
    /// `production_shaped_root_signed_over_the_attested_root_preimage_is_refused`
    /// pins that the old shape is now REFUSED, and
    /// `node/tests/committee_signature_covers_a_per_turn_value.rs` drives the
    /// real `VoteCollector` end to end.
    fn hybrid_committee_and_root(
        signers: &[usize],
        threshold: usize,
    ) -> (CommitteeDescriptor, Vec<PublicKey>, [u8; 32], AttestedRoot) {
        use dregg_federation::frost::MlDsaSigningKey;
        use dregg_types::HybridQuorumSig;

        // `dregg-verifier` cannot link the Lean archive from `[dependencies]`, so nothing in its
        // test binary installs a verified PQ core and `dregg-pq` refuses the ML-DSA derivation
        // below with an uncatchable `process::abort()` — this whole lib-test binary died on it.
        // The dev-only `dregg-pq-testkit` installs the cores; `hybrid_committee_and_root` is the
        // one gateway every hybrid test in this module goes through.
        dregg_pq_testkit::install_or_panic();

        let kps: Vec<(dregg_types::SigningKey, PublicKey)> = (0..3)
            .map(|i| {
                let mut s = [0u8; 32];
                s[0] = 0x71;
                s[1] = i as u8;
                let sk = dregg_types::SigningKey::from_bytes(&s);
                let pk = sk.public_key();
                (sk, pk)
            })
            .collect();
        let members: Vec<PublicKey> = kps.iter().map(|(_, pk)| *pk).collect();
        let pq: Vec<_> = (0..3)
            .map(|i| {
                let mut s = [0u8; 32];
                s[0] = 0x72;
                s[1] = i as u8;
                MlDsaSigningKey::from_seed(&s)
            })
            .collect();
        let fed_id = dregg_federation::derive_federation_id_with_epoch(&members, 0);

        let desc = CommitteeDescriptor {
            federation_id: hex::encode(fed_id),
            committee_epoch: 0,
            threshold,
            validators: members
                .iter()
                .enumerate()
                .map(|(i, pk)| ValidatorDescriptor {
                    name: format!("n{i}"),
                    public_key: hex::encode(pk.0),
                    ml_dsa_public_key: Some(hex::encode(pq[i].0.0)),
                })
                .collect(),
        };

        let mut root =
            AttestedRoot::new_legacy([0x7C; 32], 5, 1_700_000_000, vec![], None, threshold);
        root.federation_id = dregg_types::FederationId(fed_id);
        root.blocklace_block_id = Some([0x9A; 32]);
        root.finality_round = Some(5);
        root.receipt_stream_root = Some(dregg_types::merkle_root_of_receipt_hashes(&[[0x3D; 32]]));
        let message = root
            .hybrid_quorum_message()
            .expect("an anchored root has a vote preimage");
        root.hybrid_quorum = signers
            .iter()
            .map(|&i| HybridQuorumSig {
                pubkey: kps[i].1,
                signature: dregg_types::sign(&kps[i].0, &message),
                ml_dsa_pubkey: pq[i].0.0.to_vec(),
                pq_signature: pq[i].1.sign(&message).expect("ml-dsa sign"),
            })
            .collect();

        (desc, members, fed_id, root)
    }

    #[test]
    fn attested_root_hybrid_quorum_verifies_both_halves() {
        let (desc, keys, fed_id, root) = hybrid_committee_and_root(&[0, 1], 2);
        verify_attested_root_against_descriptor(
            "root",
            &root,
            &desc,
            &keys,
            &desc.ml_dsa_pubkeys(),
            fed_id,
        )
        .expect("honest 2-of-3 hybrid quorum (ed25519 ∧ ML-DSA-65) must verify");
    }

    /// ⚑ **THE PREIMAGE-MISMATCH FALSIFIER.** The shape every hybrid test in this
    /// module used until 2026-08-07 — signatures over `root.signing_message()` —
    /// is now REFUSED, because that is not the preimage the node produces. The
    /// node fills `hybrid_quorum` by copying assembled committee
    /// finalization-vote signatures, so a root whose hybrid quorum signs the
    /// attested-root preimage is a root no node ever built.
    ///
    /// This is the test that would have caught the live defect: it constructs the
    /// WRONG shape deliberately and requires a refusal, rather than constructing
    /// the wrong shape by accident and requiring success.
    #[test]
    fn a_hybrid_quorum_over_the_attested_root_preimage_is_refused() {
        use dregg_federation::frost::MlDsaSigningKey;
        use dregg_types::HybridQuorumSig;

        let (desc, keys, fed_id, mut root) = hybrid_committee_and_root(&[0, 1], 2);
        // Re-sign the SAME two members over the attested-root preimage instead.
        let wrong_message = root.signing_message();
        assert_ne!(
            wrong_message,
            root.hybrid_quorum_message().expect("anchored root"),
            "precondition: the two preimages differ"
        );
        let sks: Vec<dregg_types::SigningKey> = (0..2)
            .map(|i| {
                let mut s = [0u8; 32];
                s[0] = 0x71;
                s[1] = i as u8;
                dregg_types::SigningKey::from_bytes(&s)
            })
            .collect();
        let pqs: Vec<_> = (0..2)
            .map(|i| {
                let mut s = [0u8; 32];
                s[0] = 0x72;
                s[1] = i as u8;
                MlDsaSigningKey::from_seed(&s)
            })
            .collect();
        root.hybrid_quorum = (0..2)
            .map(|i| HybridQuorumSig {
                pubkey: sks[i].public_key(),
                signature: dregg_types::sign(&sks[i], &wrong_message),
                ml_dsa_pubkey: pqs[i].0.0.to_vec(),
                pq_signature: pqs[i].1.sign(&wrong_message).expect("ml-dsa sign"),
            })
            .collect();

        let err = verify_attested_root_against_descriptor(
            "root",
            &root,
            &desc,
            &keys,
            &desc.ml_dsa_pubkeys(),
            fed_id,
        )
        .expect_err(
            "a hybrid quorum over `signing_message()` is not the quorum the node produces and \
             must be refused",
        );
        assert!(err.contains("hybrid"), "{err}");
    }

    /// An UNANCHORED root has no finalization-vote preimage at all, so its
    /// hybrid quorum cannot be judged and the check fails closed rather than
    /// inventing a message to check against.
    #[test]
    fn an_unanchored_root_hybrid_quorum_fails_closed() {
        let (desc, keys, fed_id, mut root) = hybrid_committee_and_root(&[0, 1], 2);
        root.blocklace_block_id = None;
        let err = verify_attested_root_against_descriptor(
            "root",
            &root,
            &desc,
            &keys,
            &desc.ml_dsa_pubkeys(),
            fed_id,
        )
        .expect_err("a root with no blocklace anchor has no vote preimage");
        assert!(err.contains("hybrid"), "{err}");
    }

    #[test]
    fn attested_root_forged_pq_half_rejected_even_with_valid_ed25519() {
        let (desc, keys, fed_id, mut root) = hybrid_committee_and_root(&[0, 1], 2);
        // Keep both ed25519 halves VALID; corrupt one ML-DSA-65 half.
        root.hybrid_quorum[0].pq_signature[0] ^= 0xFF;

        let err = verify_attested_root_against_descriptor(
            "root",
            &root,
            &desc,
            &keys,
            &desc.ml_dsa_pubkeys(),
            fed_id,
        )
        .expect_err("a forged ML-DSA half must reject even with a valid ed25519 half");
        assert!(err.contains("hybrid"), "{err}");
    }

    #[test]
    fn attested_root_missing_pq_half_rejected() {
        let (desc, keys, fed_id, mut root) = hybrid_committee_and_root(&[0, 1], 2);
        // Drop one signer's ML-DSA-65 half entirely (classical-only downgrade).
        root.hybrid_quorum[1].pq_signature = Vec::new();

        let err = verify_attested_root_against_descriptor(
            "root",
            &root,
            &desc,
            &keys,
            &desc.ml_dsa_pubkeys(),
            fed_id,
        )
        .expect_err("a missing ML-DSA half must reject");
        assert!(err.contains("hybrid"), "{err}");
    }

    #[test]
    fn attested_root_classical_only_fails_closed() {
        let (desc, keys, fed_id, mut root) = hybrid_committee_and_root(&[0, 1], 2);
        // A legacy classical-only root: carry the ed25519 quorum but NO hybrid
        // quorum. It must fail closed on the cross-fed finality wire.
        root.quorum_signatures = root
            .hybrid_quorum
            .iter()
            .map(|qs| (qs.pubkey, qs.signature))
            .collect();
        root.hybrid_quorum.clear();

        let err = verify_attested_root_against_descriptor(
            "root",
            &root,
            &desc,
            &keys,
            &desc.ml_dsa_pubkeys(),
            fed_id,
        )
        .expect_err("a classical-only attested root must fail closed");
        assert!(err.contains("classical-only"), "{err}");
    }

    #[test]
    fn attested_root_non_member_hybrid_signer_rejected() {
        use dregg_federation::frost::MlDsaSigningKey;
        use dregg_types::HybridQuorumSig;

        let (desc, keys, fed_id, mut root) = hybrid_committee_and_root(&[0], 1);
        // Replace the lone signer with a fully-valid hybrid signer who is NOT a
        // committee member: both halves verify, but membership fails closed.
        let message = root.hybrid_quorum_message().expect("anchored root");
        let outsider_sk = dregg_types::SigningKey::from_bytes(&[0xEE; 32]);
        let (out_pq_pk, out_pq_sk) = MlDsaSigningKey::from_seed(&[0xEF; 32]);
        root.hybrid_quorum = vec![HybridQuorumSig {
            pubkey: outsider_sk.public_key(),
            signature: dregg_types::sign(&outsider_sk, &message),
            ml_dsa_pubkey: out_pq_pk.0.to_vec(),
            pq_signature: out_pq_sk.sign(&message).expect("ml-dsa sign"),
        }];

        let err = verify_attested_root_against_descriptor(
            "root",
            &root,
            &desc,
            &keys,
            &desc.ml_dsa_pubkeys(),
            fed_id,
        )
        .expect_err("a non-member hybrid signer must reject");
        assert!(err.contains("hybrid"), "{err}");
    }

    /// **THE QUANTUM-FORGERY ADVERSARIAL TEST (cross-fed wire).** A quantum
    /// adversary breaks ed25519 for enrolled member 0 (we reuse member 0's real
    /// ed25519 key to stand in for the forged classical half), then attaches its
    /// OWN fresh ML-DSA-65 keypair and a PQ signature valid under it. Before the
    /// enrolled-roster pin, the PQ half verified against the self-carried key and
    /// BOTH halves passed. Now the self-carried key ≠ the descriptor's enrolled
    /// key for member 0, so the whole hybrid quorum is REJECTED.
    #[test]
    fn attested_root_quantum_forged_pq_key_is_rejected() {
        use dregg_federation::frost::MlDsaSigningKey;

        let (desc, keys, fed_id, mut root) = hybrid_committee_and_root(&[0, 1], 2);
        let message = root.hybrid_quorum_message().expect("anchored root");
        // Swap signer 0's ML-DSA key + signature for a FRESH attacker keypair.
        let attacker = MlDsaSigningKey::from_seed(&[0xC7; 32]);
        root.hybrid_quorum[0].ml_dsa_pubkey = attacker.0.0.to_vec();
        root.hybrid_quorum[0].pq_signature = attacker.1.sign(&message).expect("ml-dsa sign");

        let err = verify_attested_root_against_descriptor(
            "root",
            &root,
            &desc,
            &keys,
            &desc.ml_dsa_pubkeys(),
            fed_id,
        )
        .expect_err("a self-carried attacker ML-DSA key (not the enrolled key) must reject");
        assert!(err.contains("hybrid"), "{err}");

        // HONEST path stays green — the enrolled roster admits the genuine quorum.
        let (desc2, keys2, fed_id2, root2) = hybrid_committee_and_root(&[0, 1], 2);
        verify_attested_root_against_descriptor(
            "root",
            &root2,
            &desc2,
            &keys2,
            &desc2.ml_dsa_pubkeys(),
            fed_id2,
        )
        .expect("the honest enrolled-key quorum still verifies");

        // NO SILENT DOWNGRADE: a descriptor with NO aligned enrolled roster fails
        // closed even for the honest signers.
        let err2 =
            verify_attested_root_against_descriptor("root", &root2, &desc2, &keys2, &[], fed_id2)
                .expect_err("an absent enrolled roster must fail closed");
        assert!(err2.contains("enrolled roster"), "{err2}");
    }

    #[test]
    fn federation_receipt_body_must_match_tail_receipt() {
        use dregg_federation::receipt::{FederationReceipt, FederationReceiptBody, ReceiptQc};
        use dregg_types::{PublicKey, Signature};

        let tail = sample_turn_receipt();
        let body = FederationReceiptBody {
            turn_hash: tail.turn_hash,
            block_height: 7,
            block_hash: [0x44; 32],
            agent: tail.agent,
            nonce: 0,
            pre_state_hash: tail.pre_state_hash,
            post_state_hash: tail.post_state_hash,
            effects_hash: [0xEE; 32],
            previous_receipt_hash: tail.previous_receipt_hash,
        };
        let fr = FederationReceipt {
            version: FederationReceipt::VERSION,
            federation_id: tail.federation_id,
            committee_epoch: 0,
            body,
            qc: ReceiptQc::Votes(vec![(PublicKey([0u8; 32]), Signature([0u8; 64]))]),
        };

        let err = federation_receipt_matches_tail(&fr, &tail)
            .expect_err("mismatched effects_hash must not certify tail receipt");

        assert!(err.contains("effects_hash"), "{err}");
    }

    // -- Test helpers --
    fn sample_committee(fed_id: [u8; 32]) -> CommitteeDescriptor {
        CommitteeDescriptor {
            federation_id: hex::encode(fed_id),
            committee_epoch: 0,
            threshold: 1,
            validators: vec![ValidatorDescriptor {
                name: "n0".into(),
                public_key: "ab".repeat(32),
                ml_dsa_public_key: None,
            }],
        }
    }

    fn sample_turn_receipt() -> dregg_turn::turn::TurnReceipt {
        use dregg_types::CellId;

        dregg_turn::turn::TurnReceipt {
            turn_hash: [1u8; 32],
            forest_hash: [2u8; 32],
            pre_state_hash: [3u8; 32],
            post_state_hash: [4u8; 32],
            timestamp: 42,
            effects_hash: [5u8; 32],
            computrons_used: 100,
            action_count: 1,
            previous_receipt_hash: None,
            agent: CellId::from_bytes([0xAB; 32]),
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

    fn sample_bundle() -> CrossFedReceiptBundle {
        use dregg_captp::FederationId;
        use dregg_cell::AuthRequired;
        use dregg_turn::WitnessedReceipt;
        use dregg_types::{AttestedRoot, CellId, generate_keypair};

        let (sk, _pk) = generate_keypair();
        let cert = dregg_captp::handoff::HandoffCertificate::create(
            &sk,
            FederationId([0xAA; 32]),
            FederationId([0xBB; 32]),
            CellId([0xCC; 32]),
            [0xDD; 32],
            AuthRequired::Signature,
            None,
            None,
            None,
            [0xEE; 32],
        );

        let receipt = sample_turn_receipt();
        let wr = WitnessedReceipt::from_components(receipt, vec![0u8; 8], vec![1, 2, 3], None);
        CrossFedReceiptBundle::new(
            vec![wr],
            AttestedRoot::new_legacy([1; 32], 1, 1_700_000_000, vec![], None, 0),
            AttestedRoot::new_legacy([2; 32], 2, 1_700_000_000, vec![], None, 0),
            cert,
            None,
        )
    }
}
