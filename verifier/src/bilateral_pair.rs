//! Stage 7-γ.2 Phase 1 — bilateral cross-cell PI AGREEMENT check.
//!
//! # ⚑ THIS CHECKS NO PROOF. FLAG DAY 2026-08-05.
//!
//! Read this before reading anything else in the file. Every function here compares
//! **public-input vectors against a schedule reconstructed from the canonical
//! `Turn`**. It never deserializes a proof, never calls `verify_vm_descriptor2`, and
//! never looks at [`WitnessedReceipt::proof_bytes`]. If nothing else has verified the
//! proofs behind those PI vectors, the presenter chose every number the check reads,
//! and agreement establishes nothing about reality.
//!
//! That was not a caveat in a docblock, it was a shipped product: `dregg-verifier
//! bilateral-pair <bundle.json>` printed `{"pi_agrees_with_schedule": true}` and
//! exited `0` for bundles whose every entry carried `proof_bytes: []` — which is
//! exactly what this module's own fabricator produces. **That subcommand is DELETED**
//! (`main.rs`), and every name here now states the scope:
//!
//! | was | is |
//! |---|---|
//! | `verify_bilateral_bundle{,_json}` | `check_bilateral_pi_agreement{,_json}` |
//! | `BilateralVerdict { verified }` | `BilateralPiAgreement { pi_agrees_with_schedule }` |
//! | `fabricate_witnessed_receipt{,_with_schedule}` | `fabricate_pi_only_witnessed_receipt{,_with_schedule}` |
//!
//! [`BilateralPiAgreement::entries_without_proof`] counts, from the bundle itself, how
//! many entries have nothing behind their PI. It is populated by the check, not
//! asserted by a comment.
//!
//! **Where the real check lives:** proofs are verified by
//! [`crate::rotated_replay::verify_rotated_leg`] on this floor, by
//! `dregg_sdk::verify_effect_vm_rotated_with_cutover` on the wire, and by
//! `dregg_turn::executor` before it runs its own copy of this agreement algebra
//! (`TurnExecutor::verify_bilateral_bundle_with_schedule`, which is what this module
//! calls into). Cross-cell agreement is a layer ON TOP of per-cell proof soundness; it
//! is not a substitute for it.
//!
//! # What the agreement check does establish (given verified proofs)
//!
//! Given a bundle whose per-cell proofs have been verified elsewhere, and the turn
//! (carrying the canonical `call_forest` and `ACTOR_NONCE`) plus the per-cell WRs that
//! came out of executing it, the check:
//!
//!   1. Reconstructs the expected bilateral schedule (`Transfer`, `Grant`,
//!      `Introduce`) from `(call_forest, ACTOR_NONCE)` alone.
//!   2. For each `(cell_id, WitnessedReceipt)` entry, lifts the PI u32 vector
//!      into BabyBear felts and compares the γ.2 bilateral slots
//!      (counts + 7 accumulator roots) to what the schedule predicts.
//!   3. Enforces `IS_AGENT_CELL` is `1` exactly on the proof whose cell is
//!      `turn.agent`, and `0` on all the others.
//!   4. Cross-side existence: a Transfer / Grant naming a covered cell must
//!      have its peer covered in the bundle; an Introduce naming any role
//!      must have all three roles covered.
//!
//! Given verified proofs, the above closes `EXECUTOR-HONESTY-AUDIT.md` T1 / T3 / T15:
//! cross-cell agreement can be confirmed without trusting the executor. See
//! `STAGE-7-GAMMA-2-PI-DESIGN.md` §4 for the full algorithm.
//!
//! The JSON-friendly bundle shape ([`BilateralBundle`]) survives so an auditor can
//! ship one file and re-run the agreement algebra, and so the seL4 verifier-PD
//! scaffold (`sel4/verifier-pd`) keeps its single entry point. It is no longer
//! reachable from the `dregg-verifier` binary.

use dregg_turn::{Turn, WitnessedReceipt};
use dregg_types::CellId;
use serde::{Deserialize, Serialize};

// ---------------------------------------------------------------------------
// On-disk JSON shape
// ---------------------------------------------------------------------------

/// One entry in a bilateral bundle: the cell identifier plus its
/// [`WitnessedReceipt`].
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BilateralEntry {
    /// The cell whose per-cell proof this WR carries.
    pub cell_id: CellId,
    /// The WR itself (proof bytes + PI + optional witness bundle).
    pub witnessed_receipt: WitnessedReceipt,
}

/// A bundle of per-cell WRs from one turn, packaged for off-AIR bilateral
/// verification. The CLI's `bilateral-pair` subcommand reads this JSON shape.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BilateralBundle {
    /// The canonical turn (carries `call_forest`, `nonce`, `agent`).
    pub turn: Turn,
    /// One entry per touched cell. Order does not matter; the verifier's
    /// schedule reconstruction is order-independent.
    pub entries: Vec<BilateralEntry>,
    /// γ.2 unilateral binding (1-arity sibling of bilateral): per-cell
    /// self-attestations the prover claims it produced this turn.
    /// Each `(cell_id, attestations)` entry is folded into the accumulator
    /// the verifier compares against the cell's PI[UNILATERAL_*] slots.
    ///
    /// Empty when no cell self-attested. Order within each cell's vec is
    /// the accumulator-absorb order — must match the producer side.
    ///
    /// `peer_exchange` composition: a sovereign cell using
    /// `PeerStateTransition::unilateral_attestation` populates this map
    /// with the attestation it signed; the receiver verifies it matches
    /// the sender's per-cell PI accumulator. Forging the attestation on
    /// behalf of another cell-id is rejected because the
    /// `attestation_data` canonical preimage includes `cell_id` — a
    /// forged sender produces a different data hash and a different
    /// accumulator root.
    #[serde(default)]
    pub unilateral_attestations: std::collections::BTreeMap<
        CellId,
        Vec<dregg_turn::bilateral_schedule::UnilateralAttestation>,
    >,
}

// ---------------------------------------------------------------------------
// Verdict
// ---------------------------------------------------------------------------

/// Result of the bilateral cross-cell PI AGREEMENT check.
///
/// ⚠ There is deliberately no field called `verified` on this type. Agreement between
/// PI vectors and a schedule is not verification of the proofs behind those vectors;
/// see the module docblock.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BilateralPiAgreement {
    /// True iff every PI-vs-schedule comparison held. Says NOTHING about whether any
    /// proof was verified — see [`Self::entries_without_proof`].
    pub pi_agrees_with_schedule: bool,
    /// How many of `entry_count` entries carry `proof_bytes: []`, i.e. how many of the
    /// PI vectors this check compared have NOTHING behind them. Counted from the
    /// bundle, not asserted. When this equals `entry_count`, the agreement above was
    /// computed entirely over numbers the presenter chose.
    pub entries_without_proof: usize,
    /// Number of bundle entries (cells covered).
    pub entry_count: usize,
    /// Number of Transfers, Grants, Introduces in the reconstructed schedule.
    pub transfer_count: usize,
    pub grant_count: usize,
    pub introduce_count: usize,
    /// Per-cell list of cell ids in the order they appeared in the bundle.
    pub cells: Vec<String>,
    /// Human-readable reason when `pi_agrees_with_schedule == false`; "ok" otherwise.
    pub reason: String,
}

impl BilateralPiAgreement {
    fn accept(entry_count: usize, sched_counts: (usize, usize, usize), cells: Vec<String>) -> Self {
        Self {
            pi_agrees_with_schedule: true,
            entries_without_proof: 0,
            entry_count,
            transfer_count: sched_counts.0,
            grant_count: sched_counts.1,
            introduce_count: sched_counts.2,
            cells,
            reason: "ok".to_string(),
        }
    }

    fn reject(
        entry_count: usize,
        sched_counts: (usize, usize, usize),
        cells: Vec<String>,
        reason: impl Into<String>,
    ) -> Self {
        Self {
            pi_agrees_with_schedule: false,
            entries_without_proof: 0,
            entry_count,
            transfer_count: sched_counts.0,
            grant_count: sched_counts.1,
            introduce_count: sched_counts.2,
            cells,
            reason: reason.into(),
        }
    }
}

// ---------------------------------------------------------------------------
// Core API
// ---------------------------------------------------------------------------

/// Run the cross-cell PI AGREEMENT check over a JSON bundle. **Verifies no proof** —
/// see the module docblock and [`BilateralPiAgreement::entries_without_proof`].
///
/// Returns a [`BilateralPiAgreement`] describing the outcome. Retained for the seL4
/// verifier-PD scaffold (`sel4/verifier-pd/src/main.rs`), which is its only remaining
/// caller now that the `bilateral-pair` CLI subcommand is gone.
pub fn check_bilateral_pi_agreement_json(json: &str) -> BilateralPiAgreement {
    let bundle: BilateralBundle = match serde_json::from_str(json) {
        Ok(b) => b,
        Err(e) => {
            return BilateralPiAgreement {
                pi_agrees_with_schedule: false,
                entries_without_proof: 0,
                entry_count: 0,
                transfer_count: 0,
                grant_count: 0,
                introduce_count: 0,
                cells: vec![],
                reason: format!("bundle JSON parse error: {e}"),
            };
        }
    };
    check_bilateral_pi_agreement(&bundle)
}

/// Run the cross-cell PI AGREEMENT check over a deserialized [`BilateralBundle`].
/// Pure function over the bundle. **Verifies no proof** — see the module docblock.
pub fn check_bilateral_pi_agreement(bundle: &BilateralBundle) -> BilateralPiAgreement {
    let cells: Vec<String> = bundle
        .entries
        .iter()
        .map(|e| hex::encode(e.cell_id.as_bytes()))
        .collect();
    // Build the schedule and inject unilateral attestations from the bundle
    // (γ.2 1-arity sibling — cell-side data that doesn't live in the Turn).
    let mut sched = dregg_turn::bilateral_schedule::ExpectedBilateral::from_turn(&bundle.turn);
    for (cell, attestations) in &bundle.unilateral_attestations {
        for att in attestations {
            sched.push_unilateral(*cell, att.clone());
        }
    }
    let sched_counts = (
        sched.transfers.len(),
        sched.grants.len(),
        sched.introduces.len(),
    );
    let entry_count = bundle.entries.len();

    // Build the (CellId, &WitnessedReceipt) view the executor API consumes.
    let view: Vec<(CellId, &WitnessedReceipt)> = bundle
        .entries
        .iter()
        .map(|e| (e.cell_id, &e.witnessed_receipt))
        .collect();

    // COUNT the entries whose PI vector has nothing behind it. This is the one honest
    // thing this module can say about proofs: it does not verify them, and here is how
    // many of them are not even present.
    let entries_without_proof = bundle
        .entries
        .iter()
        .filter(|e| e.witnessed_receipt.proof_bytes.is_empty())
        .count();

    let mut out =
        match WitnessedReceipt::verify_bilateral_chain_with_schedule(&view, &bundle.turn, &sched) {
            Ok(()) => BilateralPiAgreement::accept(entry_count, sched_counts, cells),
            Err(e) => {
                BilateralPiAgreement::reject(entry_count, sched_counts, cells, format!("{e:?}"))
            }
        }
        .also_check_stark_pi(bundle);
    out.entries_without_proof = entries_without_proof;
    out
}

impl BilateralPiAgreement {
    /// Optional structural overlay: confirm every WR's `public_inputs` length
    /// is at least the active PI layout (`ACTIVE_BASE_COUNT`); reject otherwise.
    /// (The bilateral chain verify already enforces this — we keep the check
    /// here as a belt-and-suspenders surface for when `entries` is empty / the
    /// chain verify short-circuits early.)
    fn also_check_stark_pi(mut self, bundle: &BilateralBundle) -> Self {
        if !self.pi_agrees_with_schedule {
            return self;
        }
        use dregg_circuit::effect_vm::pi as p;
        for (i, e) in bundle.entries.iter().enumerate() {
            if e.witnessed_receipt.public_inputs.len() < p::ACTIVE_BASE_COUNT {
                self.pi_agrees_with_schedule = false;
                self.reason = format!(
                    "entry {i} (cell {}): PI vector has {} entries, expected at least {} (PI v3 layout)",
                    hex::encode(e.cell_id.as_bytes()),
                    e.witnessed_receipt.public_inputs.len(),
                    p::ACTIVE_BASE_COUNT
                );
                return self;
            }
        }
        self
    }
}

// ---------------------------------------------------------------------------
// Helpers used by tests + CLI
// ---------------------------------------------------------------------------

/// Build a [`WitnessedReceipt`] whose PI vector is populated with the γ.2
/// bilateral slots for `cell_id` (the rest are zero) and whose **`proof_bytes` is
/// EMPTY**. Used by tests and the integration demo to exercise the agreement algebra
/// without paying the proving cost.
///
/// ⚠ The name says `pi_only` because that is the whole of it: the returned receipt
/// carries `proof_bytes: vec![]`, so nothing downstream may treat its `public_inputs`
/// as attested. [`check_bilateral_pi_agreement`] counts these into
/// [`BilateralPiAgreement::entries_without_proof`]. In production the
/// `public_inputs` come from the prover's actual proof and must be verified
/// (`crate::rotated_replay::verify_rotated_leg`) before agreement means anything.
pub fn fabricate_pi_only_witnessed_receipt(
    turn: &Turn,
    cell_id: &CellId,
    receipt: dregg_turn::TurnReceipt,
) -> WitnessedReceipt {
    fabricate_pi_only_witnessed_receipt_with_schedule(
        turn,
        cell_id,
        receipt,
        &dregg_turn::bilateral_schedule::ExpectedBilateral::from_turn(turn),
    )
}

/// Same as [`fabricate_pi_only_witnessed_receipt`] but using a caller-provided
/// schedule. Pass a schedule with `unilateral_attestations` populated to
/// exercise the γ.2 unilateral-binding PI slots.
pub fn fabricate_pi_only_witnessed_receipt_with_schedule(
    turn: &Turn,
    cell_id: &CellId,
    receipt: dregg_turn::TurnReceipt,
    schedule: &dregg_turn::bilateral_schedule::ExpectedBilateral,
) -> WitnessedReceipt {
    use dregg_circuit::effect_vm::pi as p;
    use dregg_circuit::field::BabyBear;
    use dregg_turn::bilateral_schedule::project_into_pi;

    let counts = schedule.counts_for(cell_id);
    let roots = schedule.roots_for(cell_id, turn.nonce);

    let mut pi_bb = vec![BabyBear::ZERO; p::ACTIVE_BASE_COUNT];
    // Populate turn-identity slots (shared across all per-cell proofs of one turn).
    let (th, eg, _, prev) = dregg_turn::executor::TurnExecutor::compute_turn_identity_pi(turn);
    pi_bb[p::TURN_HASH_BASE..p::TURN_HASH_BASE + 4].copy_from_slice(&th[..4]);
    pi_bb[p::EFFECTS_HASH_GLOBAL_BASE..p::EFFECTS_HASH_GLOBAL_BASE + 4].copy_from_slice(&eg[..4]);
    pi_bb[p::PREVIOUS_RECEIPT_HASH_BASE..p::PREVIOUS_RECEIPT_HASH_BASE + 4]
        .copy_from_slice(&prev[..4]);
    pi_bb[p::ACTOR_NONCE] = BabyBear::new((turn.nonce & 0x7FFF_FFFF) as u32);
    project_into_pi(&mut pi_bb, &counts, &roots);
    pi_bb[p::IS_AGENT_CELL] = if cell_id == &turn.agent {
        BabyBear::new(1)
    } else {
        BabyBear::ZERO
    };
    let pi_u32: Vec<u32> = pi_bb.iter().map(|x| x.as_u32()).collect();

    // Attach a minimal scope-2 witness trace so the artifact is a full
    // scope-(2) WitnessedReceipt. The Phase-2 aggregator
    // (`prove_aggregated_bundle`) requires scope-2 inputs — accepting a
    // scope-1-only WR would let an aggregate look stronger than the receipt
    // material it summarizes. A single zero row is sufficient to populate the
    // inline witness bundle + witness-hash binding.
    let trace = vec![vec![
        BabyBear::ZERO;
        dregg_circuit::effect_vm::EFFECT_VM_WIDTH
    ]];
    WitnessedReceipt::from_components(receipt, vec![], pi_u32, Some(trace.as_slice()))
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_circuit::effect_vm::pi as p;
    use dregg_turn::{ActionBuilder, TurnBuilder, TurnReceipt};

    fn cid(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    fn dummy_receipt(agent: CellId) -> TurnReceipt {
        TurnReceipt {
            turn_hash: [0u8; 32],
            forest_hash: [0u8; 32],
            pre_state_hash: [0u8; 32],
            post_state_hash: [0u8; 32],
            timestamp: 0,
            effects_hash: [0u8; 32],
            computrons_used: 0,
            action_count: 0,
            previous_receipt_hash: None,
            agent,
            federation_id: [0u8; 32],
            routing_directives: vec![],
            introduction_exports: vec![],
            derivation_records: vec![],
            emitted_events: vec![],
            executor_signature: None,
            finality: Default::default(),
            was_encrypted: false,
            was_burn: false,
            consumed_capabilities: vec![],
        }
    }

    fn make_transfer_turn(alice: CellId, bob: CellId, amount: u64, nonce: u64) -> Turn {
        let mut builder = TurnBuilder::new(alice, nonce);
        let action = ActionBuilder::new_unchecked_for_tests(alice, "transfer", alice)
            .effect_transfer(alice, bob, amount)
            .build();
        builder.add_action(action);
        builder.fee(0).build()
    }

    #[test]
    fn happy_path_bilateral_transfer_verifies() {
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let turn = make_transfer_turn(alice, bob, 100, 1);

        let bundle = BilateralBundle {
            turn: turn.clone(),
            entries: vec![
                BilateralEntry {
                    cell_id: alice,
                    witnessed_receipt: fabricate_pi_only_witnessed_receipt(
                        &turn,
                        &alice,
                        dummy_receipt(alice),
                    ),
                },
                BilateralEntry {
                    cell_id: bob,
                    witnessed_receipt: fabricate_pi_only_witnessed_receipt(
                        &turn,
                        &bob,
                        dummy_receipt(alice),
                    ),
                },
            ],
            unilateral_attestations: std::collections::BTreeMap::new(),
        };
        let verdict = check_bilateral_pi_agreement(&bundle);
        assert!(
            verdict.pi_agrees_with_schedule,
            "honest bundle must verify: {:?}",
            verdict
        );
        assert_eq!(verdict.entry_count, 2);
        assert_eq!(verdict.transfer_count, 1);
    }

    #[test]
    fn tampered_amount_rejects() {
        // Receiver claims amount=50; sender (and the canonical Turn) say 100.
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let real_turn = make_transfer_turn(alice, bob, 100, 1);
        let lie_turn = make_transfer_turn(alice, bob, 50, 1);

        let bundle = BilateralBundle {
            turn: real_turn.clone(),
            entries: vec![
                BilateralEntry {
                    cell_id: alice,
                    witnessed_receipt: fabricate_pi_only_witnessed_receipt(
                        &real_turn,
                        &alice,
                        dummy_receipt(alice),
                    ),
                },
                BilateralEntry {
                    cell_id: bob,
                    // Bob's PI is fabricated against a different turn (50 not 100).
                    witnessed_receipt: fabricate_pi_only_witnessed_receipt(
                        &lie_turn,
                        &bob,
                        dummy_receipt(alice),
                    ),
                },
            ],
            unilateral_attestations: std::collections::BTreeMap::new(),
        };
        let verdict = check_bilateral_pi_agreement(&bundle);
        assert!(!verdict.pi_agrees_with_schedule);
        assert!(
            verdict.reason.contains("root") || verdict.reason.contains("incoming_transfer"),
            "expected root/incoming mismatch, got: {}",
            verdict.reason
        );
    }

    #[test]
    fn tampered_transfer_id_via_root_overwrite_rejects() {
        // Equivalent to "tamper with transfer_id" — overwrite Alice's
        // OUTGOING_TRANSFER_ROOT with a garbage felt. The accumulator absorbs
        // transfer_id; mangling the root is the externally-visible footprint
        // of any in-PI transfer_id tamper.
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let turn = make_transfer_turn(alice, bob, 100, 1);

        let mut alice_wr = fabricate_pi_only_witnessed_receipt(&turn, &alice, dummy_receipt(alice));
        let bob_wr = fabricate_pi_only_witnessed_receipt(&turn, &bob, dummy_receipt(alice));
        // Tamper: zap one felt of OUTGOING_TRANSFER_ROOT (transfer_id is folded
        // into the root, so any in-PI transfer_id manipulation shows up here).
        alice_wr.public_inputs[p::OUTGOING_TRANSFER_ROOT_BASE] = 0xDEAD_BEEF_u32 & 0x7FFF_FFFF;

        let bundle = BilateralBundle {
            turn,
            entries: vec![
                BilateralEntry {
                    cell_id: alice,
                    witnessed_receipt: alice_wr,
                },
                BilateralEntry {
                    cell_id: bob,
                    witnessed_receipt: bob_wr,
                },
            ],
            unilateral_attestations: std::collections::BTreeMap::new(),
        };
        let verdict = check_bilateral_pi_agreement(&bundle);
        assert!(
            !verdict.pi_agrees_with_schedule,
            "transfer_id tamper must reject"
        );
    }

    #[test]
    fn wrong_peer_cell_id_rejects() {
        // Adversarial: bundle declares Bob's cell-id as some attacker-controlled
        // cid(0xCC) instead of the real bob (0xB2). The schedule walks the
        // canonical turn and expects (alice, bob); the bundle's "bob" entry's
        // PI is fabricated for cid(0xCC) — its OUTGOING/INCOMING roots
        // diverge from the schedule's prediction for the real bob, so the
        // bundle rejects on the cross-side existence check AND the per-cell
        // PI root check.
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let attacker = cid(0xCC);
        let turn = make_transfer_turn(alice, bob, 100, 1);

        let bundle = BilateralBundle {
            turn: turn.clone(),
            entries: vec![
                BilateralEntry {
                    cell_id: alice,
                    witnessed_receipt: fabricate_pi_only_witnessed_receipt(
                        &turn,
                        &alice,
                        dummy_receipt(alice),
                    ),
                },
                BilateralEntry {
                    cell_id: attacker,
                    witnessed_receipt: fabricate_pi_only_witnessed_receipt(
                        &turn,
                        &attacker, // PI derived against attacker, not bob
                        dummy_receipt(alice),
                    ),
                },
            ],
            unilateral_attestations: std::collections::BTreeMap::new(),
        };
        let verdict = check_bilateral_pi_agreement(&bundle);
        assert!(
            !verdict.pi_agrees_with_schedule,
            "wrong peer cell must reject"
        );
    }

    #[test]
    fn fabricated_inbound_without_sender_rejects() {
        // Adversarial: a bundle declares an incoming transfer to bob (PI's
        // INBOUND_TRANSFER_COUNT > 0) but the canonical Turn never names that
        // transfer at all. We achieve this by feeding the verifier a Turn with
        // no Transfer effects, while Bob's PI was fabricated against a Turn
        // that *does* declare the transfer.
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let real_turn_with_transfer = make_transfer_turn(alice, bob, 100, 1);
        // Verifier uses an empty turn (no transfer in call_forest).
        let mut empty_builder = TurnBuilder::new(alice, 1);
        let noop_action = ActionBuilder::new_unchecked_for_tests(alice, "noop", alice).build();
        empty_builder.add_action(noop_action);
        let empty_turn = empty_builder.fee(0).build();

        let bundle = BilateralBundle {
            turn: empty_turn, // schedule says: no transfers expected
            entries: vec![BilateralEntry {
                cell_id: bob,
                // Bob's fabricated PI claims an inbound transfer.
                witnessed_receipt: fabricate_pi_only_witnessed_receipt(
                    &real_turn_with_transfer,
                    &bob,
                    dummy_receipt(alice),
                ),
            }],
            unilateral_attestations: std::collections::BTreeMap::new(),
        };
        let verdict = check_bilateral_pi_agreement(&bundle);
        assert!(
            !verdict.pi_agrees_with_schedule,
            "claimed inbound transfer absent from schedule must reject"
        );
    }

    #[test]
    fn json_roundtrip_and_verify() {
        // The CLI parses a JSON bundle from disk → check_bilateral_pi_agreement_json.
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let turn = make_transfer_turn(alice, bob, 100, 1);
        let bundle = BilateralBundle {
            turn: turn.clone(),
            entries: vec![
                BilateralEntry {
                    cell_id: alice,
                    witnessed_receipt: fabricate_pi_only_witnessed_receipt(
                        &turn,
                        &alice,
                        dummy_receipt(alice),
                    ),
                },
                BilateralEntry {
                    cell_id: bob,
                    witnessed_receipt: fabricate_pi_only_witnessed_receipt(
                        &turn,
                        &bob,
                        dummy_receipt(alice),
                    ),
                },
            ],
            unilateral_attestations: std::collections::BTreeMap::new(),
        };
        let json = serde_json::to_string(&bundle).expect("serialize");
        let verdict = check_bilateral_pi_agreement_json(&json);
        assert!(verdict.pi_agrees_with_schedule, "{:?}", verdict);

        // Edge case: malformed JSON (missing required fields) must reject.
        let bad_json = r#"{"turn": null, "entries": []}"#;
        let bad_verdict = check_bilateral_pi_agreement_json(bad_json);
        assert!(
            !bad_verdict.pi_agrees_with_schedule,
            "malformed JSON must be rejected: {:?}",
            bad_verdict
        );

        // Edge case: empty JSON must reject.
        let empty_verdict = check_bilateral_pi_agreement_json("{}");
        assert!(
            !empty_verdict.pi_agrees_with_schedule,
            "empty JSON must be rejected: {:?}",
            empty_verdict
        );
    }

    // ---- bilateral Grant happy-path -----------------------------------------

    #[test]
    fn happy_path_bilateral_grant_verifies() {
        // Alice grants a capability to Bob; verifier confirms grantor +
        // grantee accumulator roots match.
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let target = cid(0xCC);
        let mut builder = TurnBuilder::new(alice, 1);
        let action = ActionBuilder::new_unchecked_for_tests(alice, "grant", alice)
            .effect_grant_capability(
                alice,
                bob,
                dregg_cell::CapabilityRef {
                    target,
                    slot: 0,
                    permissions: dregg_cell::AuthRequired::Signature,
                    expires_at: None,
                    breadstuff: None,
                    allowed_effects: None,
                    stored_epoch: None,
                    provenance: [0u8; 32],
                },
            )
            .build();
        builder.add_action(action);
        let turn = builder.fee(0).build();

        let bundle = BilateralBundle {
            turn: turn.clone(),
            entries: vec![
                BilateralEntry {
                    cell_id: alice,
                    witnessed_receipt: fabricate_pi_only_witnessed_receipt(
                        &turn,
                        &alice,
                        dummy_receipt(alice),
                    ),
                },
                BilateralEntry {
                    cell_id: bob,
                    witnessed_receipt: fabricate_pi_only_witnessed_receipt(
                        &turn,
                        &bob,
                        dummy_receipt(alice),
                    ),
                },
            ],
            unilateral_attestations: std::collections::BTreeMap::new(),
        };
        let verdict = check_bilateral_pi_agreement(&bundle);
        assert!(
            verdict.pi_agrees_with_schedule,
            "honest bilateral grant must verify: {:?}",
            verdict
        );
        assert_eq!(verdict.grant_count, 1);
    }

    // ---- trilateral Introduce happy-path ------------------------------------

    // ---- γ.2 unilateral binding tests (1-arity sibling) -----------------

    #[test]
    fn unilateral_attestation_happy_path() {
        // Alice transfers to Bob *and* publishes a SelfStateTransition
        // attestation. The bundle carries the attestation; the verifier
        // confirms Alice's PI[UNILATERAL_*] matches what the schedule predicts.
        use dregg_turn::bilateral_schedule::{
            ExpectedBilateral, UnilateralAttestation, UnilateralAttestationKind,
        };
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let turn = make_transfer_turn(alice, bob, 100, 1);

        let att = UnilateralAttestation {
            kind: UnilateralAttestationKind::SelfStateTransition,
            attestation_data: [0xAA; 32],
        };
        let mut sched = ExpectedBilateral::from_turn(&turn);
        sched.push_unilateral(alice, att.clone());

        let mut atts = std::collections::BTreeMap::new();
        atts.insert(alice, vec![att]);

        let bundle = BilateralBundle {
            turn: turn.clone(),
            entries: vec![
                BilateralEntry {
                    cell_id: alice,
                    witnessed_receipt: fabricate_pi_only_witnessed_receipt_with_schedule(
                        &turn,
                        &alice,
                        dummy_receipt(alice),
                        &sched,
                    ),
                },
                BilateralEntry {
                    cell_id: bob,
                    witnessed_receipt: fabricate_pi_only_witnessed_receipt_with_schedule(
                        &turn,
                        &bob,
                        dummy_receipt(alice),
                        &sched,
                    ),
                },
            ],
            unilateral_attestations: atts,
        };
        let verdict = check_bilateral_pi_agreement(&bundle);
        assert!(
            verdict.pi_agrees_with_schedule,
            "honest unilateral attestation must verify: {:?}",
            verdict
        );
    }

    #[test]
    fn unilateral_tampered_root_rejects() {
        // Same as the happy-path setup but the prover's PI carries a different
        // unilateral root than what the bundle declares.
        use dregg_turn::bilateral_schedule::{
            ExpectedBilateral, UnilateralAttestation, UnilateralAttestationKind,
        };
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let turn = make_transfer_turn(alice, bob, 100, 1);

        // Schedule used for the prover-side PI fabrication: WITHOUT the
        // attestation (so the prover's PI shows sentinel root).
        let sched_without = ExpectedBilateral::from_turn(&turn);

        // The bundle, however, claims an attestation — the verifier will
        // rebuild the schedule with the attestation, expect a non-sentinel
        // root, and reject Alice's PI (which carries the sentinel).
        let att = UnilateralAttestation {
            kind: UnilateralAttestationKind::SelfStateTransition,
            attestation_data: [0xAA; 32],
        };
        let mut atts = std::collections::BTreeMap::new();
        atts.insert(alice, vec![att]);

        let bundle = BilateralBundle {
            turn: turn.clone(),
            entries: vec![
                BilateralEntry {
                    cell_id: alice,
                    witnessed_receipt: fabricate_pi_only_witnessed_receipt_with_schedule(
                        &turn,
                        &alice,
                        dummy_receipt(alice),
                        &sched_without,
                    ),
                },
                BilateralEntry {
                    cell_id: bob,
                    witnessed_receipt: fabricate_pi_only_witnessed_receipt_with_schedule(
                        &turn,
                        &bob,
                        dummy_receipt(alice),
                        &sched_without,
                    ),
                },
            ],
            unilateral_attestations: atts,
        };
        let verdict = check_bilateral_pi_agreement(&bundle);
        assert!(
            !verdict.pi_agrees_with_schedule,
            "missing unilateral attestation in PI must reject"
        );
    }

    #[test]
    fn unilateral_pi_overwrite_rejects() {
        // The bundle declares no attestation; the schedule expects a sentinel;
        // but Alice's PI carries a garbage non-sentinel unilateral root.
        // The PI-vs-schedule mismatch must reject.
        use dregg_circuit::effect_vm::pi as p;
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let turn = make_transfer_turn(alice, bob, 100, 1);

        let mut alice_wr = fabricate_pi_only_witnessed_receipt(&turn, &alice, dummy_receipt(alice));
        let bob_wr = fabricate_pi_only_witnessed_receipt(&turn, &bob, dummy_receipt(alice));
        alice_wr.public_inputs[p::UNILATERAL_ATTESTATIONS_COUNT] = 1;
        alice_wr.public_inputs[p::UNILATERAL_ATTESTATIONS_ROOT_BASE] = 0xDEADBEEF & 0x7FFF_FFFF;

        let bundle = BilateralBundle {
            turn,
            entries: vec![
                BilateralEntry {
                    cell_id: alice,
                    witnessed_receipt: alice_wr,
                },
                BilateralEntry {
                    cell_id: bob,
                    witnessed_receipt: bob_wr,
                },
            ],
            unilateral_attestations: std::collections::BTreeMap::new(),
        };
        let verdict = check_bilateral_pi_agreement(&bundle);
        assert!(
            !verdict.pi_agrees_with_schedule,
            "tampered unilateral PI must reject: {:?}",
            verdict
        );
    }

    #[test]
    fn happy_path_trilateral_introduce_verifies() {
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let carol = cid(0xC3);
        let mut builder = TurnBuilder::new(alice, 1);
        let action = ActionBuilder::new_unchecked_for_tests(alice, "introduce", alice)
            .effect_introduce(alice, bob, carol, dregg_cell::AuthRequired::Signature)
            .build();
        builder.add_action(action);
        let turn = builder.fee(0).build();

        let bundle = BilateralBundle {
            turn: turn.clone(),
            entries: vec![
                BilateralEntry {
                    cell_id: alice,
                    witnessed_receipt: fabricate_pi_only_witnessed_receipt(
                        &turn,
                        &alice,
                        dummy_receipt(alice),
                    ),
                },
                BilateralEntry {
                    cell_id: bob,
                    witnessed_receipt: fabricate_pi_only_witnessed_receipt(
                        &turn,
                        &bob,
                        dummy_receipt(alice),
                    ),
                },
                BilateralEntry {
                    cell_id: carol,
                    witnessed_receipt: fabricate_pi_only_witnessed_receipt(
                        &turn,
                        &carol,
                        dummy_receipt(alice),
                    ),
                },
            ],
            unilateral_attestations: std::collections::BTreeMap::new(),
        };
        let verdict = check_bilateral_pi_agreement(&bundle);
        assert!(
            verdict.pi_agrees_with_schedule,
            "honest trilateral introduce must verify: {:?}",
            verdict
        );
        assert_eq!(verdict.introduce_count, 1);
        assert_eq!(verdict.entry_count, 3);
    }

    /// ⚑ **THE SCOPE IS REPORTED, NOT ASSUMED.** A bundle every entry of which carries
    /// `proof_bytes: []` still AGREES with the schedule — that is the whole point of the
    /// module docblock's warning, and it is exactly what the deleted `bilateral-pair`
    /// subcommand printed as `"verified": true`. The agreement result must therefore
    /// carry the count, and the count must equal the entry count here. If someone later
    /// makes the fabricator mint real proofs, or makes this check demand them, THIS test
    /// goes red and the docblock gets revisited — which is the point.
    #[test]
    fn pi_only_entries_are_counted_even_when_the_schedule_agrees() {
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let turn = make_transfer_turn(alice, bob, 100, 1);
        let bundle = BilateralBundle {
            turn: turn.clone(),
            entries: vec![
                BilateralEntry {
                    cell_id: alice,
                    witnessed_receipt: fabricate_pi_only_witnessed_receipt(
                        &turn,
                        &alice,
                        dummy_receipt(alice),
                    ),
                },
                BilateralEntry {
                    cell_id: bob,
                    witnessed_receipt: fabricate_pi_only_witnessed_receipt(
                        &turn,
                        &bob,
                        dummy_receipt(alice),
                    ),
                },
            ],
            unilateral_attestations: std::collections::BTreeMap::new(),
        };
        for e in &bundle.entries {
            assert!(
                e.witnessed_receipt.proof_bytes.is_empty(),
                "the pi-only fabricator must not be quietly minting proof bytes"
            );
        }
        let agreement = check_bilateral_pi_agreement(&bundle);
        assert!(
            agreement.pi_agrees_with_schedule,
            "the schedule agrees over fabricated PI: {agreement:?}"
        );
        assert_eq!(
            agreement.entries_without_proof, 2,
            "every entry's PI has nothing behind it, and the result must SAY so: {agreement:?}"
        );
        assert_eq!(agreement.entries_without_proof, agreement.entry_count);
    }

    /// The counterpart pole: an entry that DOES carry proof bytes is not counted. So the
    /// field tracks the bundle, it is not a constant.
    #[test]
    fn an_entry_carrying_proof_bytes_is_not_counted_as_proofless() {
        let alice = cid(0xA1);
        let bob = cid(0xB2);
        let turn = make_transfer_turn(alice, bob, 100, 1);
        let mut alice_wr = fabricate_pi_only_witnessed_receipt(&turn, &alice, dummy_receipt(alice));
        // Not a valid proof, and this check does not look at it — which is the point:
        // the COUNT moves, the agreement does not, and neither is verification.
        alice_wr.proof_bytes = vec![0xAB; 8];
        let bundle = BilateralBundle {
            turn: turn.clone(),
            entries: vec![
                BilateralEntry {
                    cell_id: alice,
                    witnessed_receipt: alice_wr,
                },
                BilateralEntry {
                    cell_id: bob,
                    witnessed_receipt: fabricate_pi_only_witnessed_receipt(
                        &turn,
                        &bob,
                        dummy_receipt(alice),
                    ),
                },
            ],
            unilateral_attestations: std::collections::BTreeMap::new(),
        };
        let agreement = check_bilateral_pi_agreement(&bundle);
        assert_eq!(agreement.entries_without_proof, 1, "{agreement:?}");
    }
}
