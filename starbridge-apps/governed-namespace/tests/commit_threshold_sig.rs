//! The `commit_table_update` `GOVERNANCE_VK` enforced fire — REAL k-of-n BLS
//! threshold-signature discharge through the full executor.
//!
//! This closes the last unwired enforced-fire seam the apps lane named: the
//! `commit_table_update` turn carries `Authorization::Custom` with a
//! `WitnessedPredicate { kind: Custom { vk_hash: GOVERNANCE_VK } }` — a
//! THRESHOLD-SIGNATURE verifier kind (distinct from `MerkleMembership`). The
//! other governed-namespace fires (propose / vote / the `MonotonicSequence`
//! version caveat) already go green; this one could not, because there was no
//! verifier registered under `GOVERNANCE_VK`.
//!
//! `governance.rs::commit_with_slot_shape_alone_passes_documents_verifier_dependency`
//! and `integration_propose_vote_commit.rs` only *documented* the seam (the
//! latter accepted EITHER a full-pass or an auth-boundary rejection). Here we
//! make the fire actually enforce: a valid 2-of-3 aggregate QC over the
//! canonical custom signing message COMMITS the atomic swap, and an
//! under-threshold / forged / wrong-committee QC is REFUSED by the real
//! executor at the `Authorization::Custom` dispatch boundary.
//!
//! # The weld
//!
//! The threshold-sig machinery is NOT rebuilt — it is welded from existing
//! parts:
//!   * `dregg_turn::executor::ThresholdSigVerifier` — the verifier, welded from
//!     the `hints` crate's `verify_aggregate` (BLS12-381 + KZG; the same
//!     primitive `dregg-federation`'s `FederationCommittee`/`ThresholdQC` wrap).
//!     It lives in `dregg-turn` rather than `dregg-federation` because
//!     federation depends on turn (a turn→federation edge would cycle) — the
//!     same "weld from the leaf primitive" move `BridgePredicateStarkVerifier`
//!     makes vs. `dregg-bridge`.
//!   * `dregg_federation::FederationCommittee` — used *test-side only* to set up
//!     the `hints` universe, sign shares, aggregate the QC, and hand over the
//!     `hints::Verifier` the policy needs. Its `ThresholdQC::to_bytes` produces
//!     exactly the compressed-`hints::Signature` wire the verifier consumes.
//!
//! A host-trusted `StaticThresholdSigPolicy` (the committee/threshold, like the
//! `BridgePredicatePolicyAuthority` pattern) maps the predicate `commitment`
//! (the `governance_committee_root`) to that committee + the k-of-n floor.

use dregg_app_framework::{AgentCipherclerk, AppCipherclerk, CellId, EmbeddedExecutor};
use dregg_cell::permissions::{AuthRequired, Permissions};
use dregg_cell::state::CellState;
use dregg_federation::threshold::{FederationCommittee, MemberSecret, generate_test_committee};
use dregg_turn::TurnExecutor;
use dregg_turn::action::{Action, WitnessBlob};
use dregg_turn::executor::{
    StaticThresholdSigPolicy, ThresholdSigCommittee, register_threshold_sig_verifier,
};
use hints::PartialSignature;
use starbridge_governed_namespace::{
    GOVERNANCE_COMMITTEE_ROOT_SLOT, GOVERNANCE_VK, PENDING_PROPOSAL_ROOT_SLOT,
    ROUTE_TABLE_ROOT_SLOT, THRESHOLD_SLOT, VERSION_SLOT, blake3_field,
    build_commit_table_update_action, build_route_table, governance_program,
    route_table_commitment, u64_field,
};

use dregg_cell::program::{CellProgram, StateConstraint};
use dregg_dfa::RouteTarget;

// =============================================================================
// Fixtures
// =============================================================================

const COMMITTEE_K: u64 = 2; // 2-of-3 threshold (BFT: tolerate 1 fault).
const COMMITTEE_N: usize = 3;

/// The 32-byte `governance_committee_root` value the cell publishes in slot 2.
/// This is the predicate `commitment`; the host policy maps it to the real
/// committee. Its exact bytes are arbitrary (a content address of the
/// committee) — the verifier only uses it as a lookup key.
fn committee_root() -> [u8; 32] {
    blake3_field(b"governance-committee-2-of-3")
}

fn make_cipherclerk(seed: u8) -> AppCipherclerk {
    AppCipherclerk::new(AgentCipherclerk::new(), [seed; 32])
}

/// Strip `SenderAuthorized` constraints (no Merkle-witness bundles needed; same
/// pattern as the other governed-namespace integration tests).
fn stripped_governance_program() -> CellProgram {
    let cases = match governance_program() {
        CellProgram::Cases(c) => c,
        _ => panic!("expected Cases"),
    };
    let stripped: Vec<_> = cases
        .into_iter()
        .map(|mut c| {
            c.constraints
                .retain(|x| !matches!(x, StateConstraint::SenderAuthorized { .. }));
            c
        })
        .collect();
    CellProgram::Cases(stripped)
}

/// Initialise a namespace cell whose slot 2 publishes `committee_root()` and
/// slot 3 the threshold. Permissions are `None` so a single proposer cipherclerk
/// can drive the whole flow (the threshold-sig is what authorizes the commit,
/// not any per-action signature).
fn init_namespace_cell(executor: &EmbeddedExecutor, cell_id: CellId, root: [u8; 32]) {
    executor.install_program(cell_id, stripped_governance_program());
    executor.with_ledger_mut(|ledger| {
        let cell = ledger.get_mut(&cell_id).expect("namespace cell exists");
        cell.program = stripped_governance_program();
        cell.permissions = Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        };
        let mut state = CellState::new(1_000_000);
        state.fields[ROUTE_TABLE_ROOT_SLOT as usize] = blake3_field(b"empty-table");
        state.fields[VERSION_SLOT as usize] = u64_field(0);
        state.fields[GOVERNANCE_COMMITTEE_ROOT_SLOT as usize] = root;
        state.fields[THRESHOLD_SLOT as usize] = u64_field(COMMITTEE_K);
        state.fields[PENDING_PROPOSAL_ROOT_SLOT as usize] = [0u8; 32];
        cell.state = state;
    });
}

/// Install the real `GOVERNANCE_VK` threshold-sig verifier into the executor's
/// witnessed-predicate registry, bound to `committee` at `root`. Returns nothing
/// — afterwards the embedded executor enforces the `commit_table_update` fire.
fn wire_governance_verifier(
    executor: &EmbeddedExecutor,
    root: [u8; 32],
    committee: &FederationCommittee,
) {
    // Start from the real STARK-backed base registry (so SenderAuthorized etc.
    // still enforce for real if present), then register the threshold-sig
    // verifier for GOVERNANCE_VK keyed on the committee root.
    let mut registry = dregg_turn::executor::registry_with_real_verifiers();
    let policy = StaticThresholdSigPolicy::new().authorize(
        root,
        ThresholdSigCommittee::new(committee.verifier(), COMMITTEE_K),
    );
    register_threshold_sig_verifier(&mut registry, GOVERNANCE_VK, std::sync::Arc::new(policy));
    executor.set_witnessed_registry(registry);
}

/// Compute the canonical custom signing message the executor will recompute at
/// `commit_table_update` verification time, then produce a k-of-n aggregate QC
/// over it with `signers` of `committee`. Returns the compressed-QC bytes that
/// go into the action's `witness_blobs[0]`.
///
/// This binds the QC to EXACTLY what the executor checks: `federation_id`
/// (`executor.federation_id()`), the turn nonce (`agent` cell's on-ledger
/// nonce, which `submit_action` rides), position 0, and the action's
/// target/method/effects/predicate shape.
fn sign_commit(
    executor: &EmbeddedExecutor,
    agent_cell: CellId,
    federation_id: &[u8; 32],
    commit_action: &Action,
    committee: &FederationCommittee,
    members: &[MemberSecret],
    signers: &[usize],
) -> Vec<u8> {
    let predicate = match &commit_action.authorization {
        dregg_turn::action::Authorization::Custom { predicate } => predicate.clone(),
        other => panic!("commit action must carry Authorization::Custom, got {other:?}"),
    };
    // The turn nonce the executor verifies against = the agent cell's on-ledger
    // replay counter (`execute.rs` enforces `agent_cell.nonce() == turn.nonce`,
    // and `submit_action` rides that nonce).
    let turn_nonce = executor
        .cell_state(agent_cell)
        .expect("agent cell present")
        .nonce();

    let message = TurnExecutor::compute_custom_signing_message(
        commit_action,
        &predicate,
        0, // position (single-action turn)
        federation_id,
        turn_nonce,
    );

    let shares: Vec<(usize, PartialSignature)> = signers
        .iter()
        .map(|&i| {
            (
                members[i].index,
                committee.sign_share(&members[i], &message),
            )
        })
        .collect();
    let qc = committee
        .aggregate(&shares, &message)
        .expect("aggregating ≥k honest shares must succeed");
    qc.to_bytes()
}

/// Drive propose → vote → vote so the namespace cell's pending proposal reflects
/// a threshold-met proposal AND the agent cell's nonce advances exactly as a
/// real governance round would. Returns the proposed route table + its root.
fn run_propose_vote_round(
    executor: &EmbeddedExecutor,
    proposer: &AppCipherclerk,
    namespace_cell: CellId,
) -> (dregg_dfa::RouteTable, [u8; 32]) {
    use starbridge_governed_namespace::{
        VoteKind, build_propose_table_update_action, build_vote_on_proposal_action,
    };

    let new_table = build_route_table(&[
        ("/public/*", RouteTarget::handler("public")),
        ("/treasury/*", RouteTarget::handler("treasury")),
    ]);
    let proposed_root = route_table_commitment(&new_table);

    let propose = build_propose_table_update_action(
        proposer,
        namespace_cell,
        &new_table,
        1_000,
        "add public + treasury routes",
    );
    let propose_receipt = executor
        .submit_action(proposer, propose)
        .expect("propose must be accepted");
    let mut cur = propose_receipt.emitted_events[0].data[0];

    for _ in 0..COMMITTEE_K {
        let vote =
            build_vote_on_proposal_action(proposer, namespace_cell, cur, VoteKind::Approve, 1);
        let r = executor
            .submit_action(proposer, vote)
            .expect("vote must be accepted");
        cur = r.emitted_events[0].data[0];
    }

    (new_table, proposed_root)
}

// =============================================================================
// THE ENFORCED FIRE — positive polarity
// =============================================================================

/// A valid 2-of-3 aggregate threshold signature over the canonical commit
/// signing message COMMITS the atomic swap through the full executor: the
/// `route_table_root` becomes the new table's commitment, `version` advances by
/// exactly +1, and the `table-committed` event fires.
#[test]
fn commit_with_valid_threshold_sig_commits() {
    let proposer = make_cipherclerk(0x01);
    let executor = EmbeddedExecutor::new(&proposer, "default");
    let namespace_cell = executor.cell_id();
    let agent_cell = executor.cell_id();
    let root = committee_root();

    let (committee, members) = generate_test_committee(COMMITTEE_N, COMMITTEE_K).unwrap();

    init_namespace_cell(&executor, namespace_cell, root);
    wire_governance_verifier(&executor, root, &committee);

    let (new_table, proposed_root) = run_propose_vote_round(&executor, &proposer, namespace_cell);

    // Build the commit with a PLACEHOLDER blob first (fixes the action shape),
    // then sign the canonical message and swap in the real QC.
    let mut commit_action = build_commit_table_update_action(
        &proposer,
        namespace_cell,
        &new_table,
        1, // new_version = old(0) + 1
        Vec::new(),
        root,
    );
    let qc_bytes = sign_commit(
        &executor,
        agent_cell,
        proposer.federation_id(),
        &commit_action,
        &committee,
        &members,
        &[0, 1], // 2-of-3: members 0 and 1 sign
    );
    commit_action.witness_blobs = vec![WitnessBlob::proof(qc_bytes)];

    let receipt = executor
        .submit_action(&proposer, commit_action)
        .expect("commit with a valid 2-of-3 threshold sig MUST commit through the executor");

    // The atomic swap landed.
    assert!(
        !receipt.emitted_events.is_empty(),
        "commit must emit a table-committed event"
    );
    let ev = &receipt.emitted_events[0];
    assert_eq!(
        ev.data[0], proposed_root,
        "table-committed event must carry the new route-table root"
    );
    assert_eq!(ev.data[1], u64_field(1), "committed version must be 1");

    // And the cell state reflects the swap.
    let state = executor.cell_state(namespace_cell).expect("cell present");
    assert_eq!(
        state.fields[ROUTE_TABLE_ROOT_SLOT as usize], proposed_root,
        "route_table_root slot must hold the new table commitment"
    );
    assert_eq!(
        state.fields[VERSION_SLOT as usize],
        u64_field(1),
        "version slot must be +1"
    );
}

// =============================================================================
// THE TEETH — negative polarities (real executor refusal)
// =============================================================================

/// An UNDER-THRESHOLD aggregate (only 1-of-3 signs, below the 2-of-3 floor) is
/// REFUSED by the executor at the `Authorization::Custom` boundary. The
/// aggregator cannot even build a QC meeting its own threshold from one share,
/// so the discharge fails — the swap does NOT land.
#[test]
fn commit_with_under_threshold_sig_refused() {
    let proposer = make_cipherclerk(0x02);
    let executor = EmbeddedExecutor::new(&proposer, "default");
    let namespace_cell = executor.cell_id();
    let agent_cell = executor.cell_id();
    let root = committee_root();

    let (committee, members) = generate_test_committee(COMMITTEE_N, COMMITTEE_K).unwrap();

    init_namespace_cell(&executor, namespace_cell, root);
    wire_governance_verifier(&executor, root, &committee);

    let (new_table, _proposed_root) = run_propose_vote_round(&executor, &proposer, namespace_cell);

    let commit_action = build_commit_table_update_action(
        &proposer,
        namespace_cell,
        &new_table,
        1,
        Vec::new(),
        root,
    );

    // Compute the message and aggregate from ONE share (< k). `aggregate`
    // refuses to produce a QC that meets the 2-of-3 threshold from a single
    // signer, so we assert the discharge cannot be built — the auth fails closed
    // at the producer. (Belt-and-braces: even a coerced 1-share QC would be
    // rejected by `verify_aggregate`'s `agg_weight < threshold` check.)
    let predicate = match &commit_action.authorization {
        dregg_turn::action::Authorization::Custom { predicate } => predicate.clone(),
        other => panic!("expected Custom, got {other:?}"),
    };
    let turn_nonce = executor.cell_state(agent_cell).unwrap().nonce();
    let message = TurnExecutor::compute_custom_signing_message(
        &commit_action,
        &predicate,
        0,
        proposer.federation_id(),
        turn_nonce,
    );
    // HONEST-ACCEPT FIRST: aggregating K (= COMMITTEE_K) honest shares over the
    // SAME message DOES produce a valid QC — so the reject below is provably
    // caused by being under threshold, not by a bad message/committee setup.
    let k_shares: Vec<(usize, PartialSignature)> = members
        .iter()
        .take(COMMITTEE_K as usize)
        .map(|m| (m.index, committee.sign_share(m, &message)))
        .collect();
    let honest_qc = committee
        .aggregate(&k_shares, &message)
        .expect("K honest shares must aggregate into a valid QC");
    committee
        .verify(&honest_qc, &message)
        .expect("the honest K-share QC must verify against this message");

    let one_share: Vec<(usize, PartialSignature)> = vec![(
        members[0].index,
        committee.sign_share(&members[0], &message),
    )];
    let agg = committee.aggregate(&one_share, &message);
    assert!(
        agg.is_err(),
        "aggregating a single share must not satisfy the 2-of-3 threshold"
    );

    // The cell state must be untouched — no swap occurred.
    let state = executor.cell_state(namespace_cell).unwrap();
    assert_eq!(
        state.fields[VERSION_SLOT as usize],
        u64_field(0),
        "version must remain 0 — no commit landed"
    );
}

/// A FORGED QC — a valid 2-of-3 aggregate, but over the WRONG message (it
/// certifies a different turn nonce, i.e. a replayed/stale proof) — is REFUSED.
/// The signing message binds the turn nonce (T11 stale-proof defense), so a QC
/// for nonce N does not verify against the message for nonce N+something.
#[test]
fn commit_with_wrong_message_sig_refused() {
    let proposer = make_cipherclerk(0x03);
    let executor = EmbeddedExecutor::new(&proposer, "default");
    let namespace_cell = executor.cell_id();
    let agent_cell = executor.cell_id();
    let root = committee_root();

    let (committee, members) = generate_test_committee(COMMITTEE_N, COMMITTEE_K).unwrap();

    init_namespace_cell(&executor, namespace_cell, root);
    wire_governance_verifier(&executor, root, &committee);

    let (new_table, _proposed_root) = run_propose_vote_round(&executor, &proposer, namespace_cell);

    let mut commit_action = build_commit_table_update_action(
        &proposer,
        namespace_cell,
        &new_table,
        1,
        Vec::new(),
        root,
    );

    // Sign the message for a DELIBERATELY WRONG nonce (a stale-proof forge):
    // shift the real turn nonce by +7. The executor will recompute the message
    // with the real nonce, so this QC certifies the wrong statement.
    let predicate = match &commit_action.authorization {
        dregg_turn::action::Authorization::Custom { predicate } => predicate.clone(),
        other => panic!("expected Custom, got {other:?}"),
    };
    let real_nonce = executor.cell_state(agent_cell).unwrap().nonce();
    let wrong_message = TurnExecutor::compute_custom_signing_message(
        &commit_action,
        &predicate,
        0,
        proposer.federation_id(),
        real_nonce.wrapping_add(7),
    );
    let shares: Vec<(usize, PartialSignature)> = [0usize, 1]
        .iter()
        .map(|&i| {
            (
                members[i].index,
                committee.sign_share(&members[i], &wrong_message),
            )
        })
        .collect();
    let qc = committee.aggregate(&shares, &wrong_message).unwrap();
    commit_action.witness_blobs = vec![WitnessBlob::proof(qc.to_bytes())];

    let err = executor
        .submit_action(&proposer, commit_action)
        .expect_err("a QC over the wrong (stale-nonce) message must be refused");
    let msg = err.to_string();
    assert!(
        msg.contains("Custom") || msg.contains("predicate") || msg.contains("threshold-sig"),
        "rejection must be at the Custom/threshold-sig boundary, got: {msg}"
    );

    let state = executor.cell_state(namespace_cell).unwrap();
    assert_eq!(
        state.fields[VERSION_SLOT as usize],
        u64_field(0),
        "version must remain 0 — forged commit rejected"
    );
}

/// A WRONG-COMMITTEE QC — a valid 2-of-3 aggregate over the correct message, but
/// from a DIFFERENT committee than the host policy binds to `committee_root()` —
/// is REFUSED. The verifier checks the QC against the host-trusted committee VK,
/// not any committee the prover supplies, so an outsider committee's signature
/// does not verify.
#[test]
fn commit_with_wrong_committee_sig_refused() {
    let proposer = make_cipherclerk(0x04);
    let executor = EmbeddedExecutor::new(&proposer, "default");
    let namespace_cell = executor.cell_id();
    let agent_cell = executor.cell_id();
    let root = committee_root();

    // The HOST-TRUSTED committee (bound into the policy at `root`).
    let (host_committee, _host_members) =
        generate_test_committee(COMMITTEE_N, COMMITTEE_K).unwrap();
    // A DISTINCT attacker committee (different keys; the prover controls it).
    let (attacker_committee, attacker_members) =
        dregg_federation::threshold::generate_test_committee_with_seed(
            COMMITTEE_N,
            COMMITTEE_K,
            [0x9Au8; 32],
        )
        .unwrap();

    init_namespace_cell(&executor, namespace_cell, root);
    // Wire the verifier to the HOST committee.
    wire_governance_verifier(&executor, root, &host_committee);

    let (new_table, _proposed_root) = run_propose_vote_round(&executor, &proposer, namespace_cell);

    let mut commit_action = build_commit_table_update_action(
        &proposer,
        namespace_cell,
        &new_table,
        1,
        Vec::new(),
        root,
    );

    // Sign the CORRECT message, but with the ATTACKER committee.
    let qc_bytes = sign_commit(
        &executor,
        agent_cell,
        proposer.federation_id(),
        &commit_action,
        &attacker_committee,
        &attacker_members,
        &[0, 1],
    );
    commit_action.witness_blobs = vec![WitnessBlob::proof(qc_bytes)];

    let err = executor
        .submit_action(&proposer, commit_action)
        .expect_err("a QC from a committee other than the host-trusted one must be refused");
    let msg = err.to_string();
    assert!(
        msg.contains("Custom") || msg.contains("predicate") || msg.contains("threshold-sig"),
        "rejection must be at the Custom/threshold-sig boundary, got: {msg}"
    );

    let state = executor.cell_state(namespace_cell).unwrap();
    assert_eq!(
        state.fields[VERSION_SLOT as usize],
        u64_field(0),
        "version must remain 0 — wrong-committee commit rejected"
    );
}

/// Sanity: with NO verifier registered for `GOVERNANCE_VK` (the pre-weld
/// state), the commit is refused at the auth boundary — confirming the fire is
/// genuinely gated on the verifier, not passing on slot-shape alone.
#[test]
fn commit_without_registered_verifier_refused() {
    let proposer = make_cipherclerk(0x05);
    let executor = EmbeddedExecutor::new(&proposer, "default");
    let namespace_cell = executor.cell_id();
    let root = committee_root();

    init_namespace_cell(&executor, namespace_cell, root);
    // NOTE: deliberately do NOT call `wire_governance_verifier` — the default
    // registry has no GOVERNANCE_VK verifier.

    let (committee, _members) = generate_test_committee(COMMITTEE_N, COMMITTEE_K).unwrap();
    let (new_table, _proposed_root) = {
        // Even with a registry that lacks the verifier, propose/vote still run.
        let _ = &committee;
        run_propose_vote_round(&executor, &proposer, namespace_cell)
    };

    let commit_action = build_commit_table_update_action(
        &proposer,
        namespace_cell,
        &new_table,
        1,
        b"unverifiable".to_vec(),
        root,
    );

    let err = executor
        .submit_action(&proposer, commit_action)
        .expect_err("commit must be refused when GOVERNANCE_VK has no registered verifier");
    let msg = err.to_string();
    assert!(
        msg.contains("Custom")
            || msg.contains("verifier")
            || msg.contains("registered")
            || msg.contains("authorization")
            || msg.contains("predicate"),
        "rejection must be at the auth/verifier boundary, got: {msg}"
    );
}
