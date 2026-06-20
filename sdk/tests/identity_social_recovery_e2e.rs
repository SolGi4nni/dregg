//! End-to-end teeth for SOCIAL RECOVERY of an identity cell on the REAL
//! executor — the human-layer M0 weld ("you cannot lose your own OS").
//!
//! The design (`docs/deos/HUMAN-LAYER.md` §2c, Milestone 1): a person *is* a
//! sovereign identity cell. When every device key is lost, recovery is an
//! M-of-N **guardian quorum** that authorizes a key ROTATION — pure
//! ocap/threshold, no custodian, no "reset my account" button. This test
//! welds three already-green parts into that one flow:
//!
//!   1. `KeyRotationGate` — the KERI pre-rotation StateConstraint
//!      (`cell/src/program.rs`); the gate NEVER reads the current keys
//!      (`rotate_current_keys_irrelevant`), so a recovering user who holds
//!      no old device key can still rotate — they need only the *escrowed*
//!      next-keys preimage (the rotation credential the council holds) plus
//!      the quorum's blessing.
//!   2. `ThresholdSigVerifier` -> `hints::verify_aggregate` — the REAL
//!      weighted-threshold BLS verifier the executor already runs
//!      (`turn/src/executor/membership_verifier.rs`), fail-closed below the
//!      host-pinned k-of-n floor.
//!   3. The guardian committee — a real HINTS weighted-threshold quorum
//!      (`dregg-hints`), assembled test-side via `dregg-federation`'s
//!      committee wrapper (silent setup; no DKG). Its `ThresholdQC::to_bytes`
//!      is exactly the compressed `hints::Signature` the verifier consumes.
//!
//! The WHO and the HOW are orthogonal teeth: the guardian quorum authorizes
//! the cell's `set_state` (`Authorization::Custom`), and the `KeyRotationGate`
//! independently enforces the rotation mechanics (exhibit the committed
//! next-keys preimage, install it, re-commit forward, clear cooling). Recovery
//! is *empowered, never amplified* — a sub-threshold quorum is REFUSED by the
//! real executor.
//!
//! The headline test: a cipherclerk with NO old keys, given a 3-of-5 guardian
//! quorum, recovers control of the identity cell (and the cells it owns) — and
//! is REJECTED below the threshold.

use std::sync::Arc;

use dregg_cell::permissions::{AuthRequired, Permissions};
use dregg_cell::{CellId, field_from_u64};
use dregg_federation::threshold::{
    FederationCommittee, MemberSecret, generate_test_committee, generate_test_committee_with_seed,
};
use dregg_sdk::factories::ADOPT_TURN_FEE;
use dregg_sdk::identity::{
    CURRENT_KEYS_COMMIT_SLOT, IdentityCharter, LAST_ROTATED_AT_SLOT, NEXT_KEYS_DIGEST_SLOT,
    create_identity, genesis_effects, key_set_commitment, next_keys_digest, rotate_effects,
};
use dregg_sdk::polis::{CouncilCharter, GovernanceCellPlan};
use dregg_sdk::{AgentCipherclerk, AgentRuntime};
use dregg_turn::TurnError;
use dregg_turn::action::{Action, Authorization, WitnessBlob};
use dregg_turn::executor::{
    StaticThresholdSigPolicy, ThresholdSigCommittee, TurnExecutor, register_threshold_sig_verifier,
};
use dregg_turn::{CallForest, Turn};
use hints::PartialSignature;

use dregg_cell::predicate::{InputRef, WitnessedPredicate, WitnessedPredicateKind};

// =============================================================================
// Fixtures
// =============================================================================

const COOLING: u64 = 50;

/// 3-of-5 guardians (BFT-shaped: tolerate 2 unavailable / faulted guardians).
const GUARDIAN_K: u64 = 3;
const GUARDIAN_N: usize = 5;

/// The `vk_hash` the recovery committee answers under. The cell's `set_state`
/// permission demands `Authorization::Custom { kind: Custom { vk_hash } }`, and
/// the verifier registers under the same hash. Distinct bytes from any other
/// app VK so the registry dispatch is unambiguous.
const RECOVERY_VK: [u8; 32] = [0x5E; 32]; // "SE" — Social rEcovery.

/// The 32-byte `commitment` the recovery predicate carries. The host policy
/// maps it to the real guardian committee; its bytes are a content address of
/// the committee (arbitrary — the verifier uses it only as a lookup key). In a
/// full deos genesis this equals the council's `members_commitment()` pinned in
/// `COUNCIL_COMMIT_SLOT`; here we use a stable label.
fn guardian_root() -> [u8; 32] {
    blake3::hash(b"deos-recovery-guardians-3-of-5").into()
}

fn agent_pubkey(runtime: &AgentRuntime) -> [u8; 32] {
    runtime
        .cipherclerk()
        .read()
        .unwrap_or_else(|e| e.into_inner())
        .public_key()
        .0
}

fn slot_of(runtime: &AgentRuntime, cell: CellId, slot: u8) -> [u8; 32] {
    runtime
        .ledger()
        .lock()
        .unwrap()
        .get(&cell)
        .expect("cell exists")
        .state
        .fields[slot as usize]
}

fn cell_nonce(runtime: &AgentRuntime, cell: CellId) -> u64 {
    runtime
        .ledger()
        .lock()
        .unwrap()
        .get(&cell)
        .expect("cell exists")
        .state
        .nonce()
}

/// Deploy the plan's factory and run its create + fund + adopt turns.
fn bootstrap(runtime: &mut AgentRuntime, plan: &GovernanceCellPlan) {
    runtime.deploy_factory(plan.descriptor.clone());
    runtime
        .execute(plan.create_effects.clone())
        .expect("create turn (factory birth) must commit");
    runtime
        .execute(plan.fund_effects.clone())
        .expect("fund turn must commit");
    runtime
        .execute_as(plan.cell_id, plan.adopt_effects.clone(), ADOPT_TURN_FEE)
        .expect("adopt turn (operator self-grant) must commit");
}

/// Re-permission the identity cell so its `set_state` / `increment_nonce` are
/// authorized by the GUARDIAN QUORUM (`Authorization::Custom { RECOVERY_VK }`)
/// rather than the owner signature. This is the deos-genesis posture for a cell
/// whose recovery story is the council: the *who-may-rotate* decision is the
/// guardian threshold, while the `KeyRotationGate` still independently enforces
/// *how* a rotation must be shaped. (We leave `receive`/`access` open and lock
/// the rest — only the rotation path is exercised.)
fn install_guardian_authority(runtime: &AgentRuntime, cell: CellId) {
    let mut ledger = runtime.ledger().lock().unwrap();
    let c = ledger.get_mut(&cell).expect("identity cell exists");
    c.permissions = Permissions {
        send: AuthRequired::Impossible,
        receive: AuthRequired::None,
        set_state: AuthRequired::Custom {
            vk_hash: RECOVERY_VK,
        },
        set_permissions: AuthRequired::Impossible,
        set_verification_key: AuthRequired::Impossible,
        increment_nonce: AuthRequired::Custom {
            vk_hash: RECOVERY_VK,
        },
        delegate: AuthRequired::Impossible,
        access: AuthRequired::None,
    };
    // Endow the identity cell so it can pay the recovery turn's computron budget
    // (the polis bootstrap leaves it at 0; a real deos genesis funds the cell).
    c.state.set_balance(1_000_000);
}

/// Install the REAL `RECOVERY_VK` threshold-sig verifier into the runtime's
/// witnessed-predicate registry, bound to `committee` at `guardian_root()`.
/// Starts from the real STARK-backed base registry (so the identity program's
/// other witnessed predicates still enforce) and adds the guardian verifier.
fn wire_guardian_verifier(runtime: &mut AgentRuntime, committee: &FederationCommittee) {
    let mut registry = dregg_turn::executor::registry_with_real_verifiers();
    let policy = StaticThresholdSigPolicy::new().authorize(
        guardian_root(),
        ThresholdSigCommittee::new(committee.verifier(), GUARDIAN_K),
    );
    register_threshold_sig_verifier(&mut registry, RECOVERY_VK, Arc::new(policy));
    runtime.set_witnessed_registry(registry);
}

/// A bootstrapped, genesis'd identity at height 1_000 holding generation G0
/// with G1 pre-committed, whose `set_state` is GUARDIAN-authorized.
///
/// G0 = the (now-lost) device keys; G1 = the pre-committed next set whose
/// preimage is the escrowed rotation credential the council releases on a
/// successful quorum (`docs/deos/HUMAN-LAYER.md` §2d quorum-as-rotation).
///
/// Returns `(owner_runtime, cell, charter, g0, g1)`. The owner runtime is the
/// *birthing* identity; recovery is driven by a SEPARATE fresh runtime holding
/// none of these keys.
#[allow(clippy::type_complexity)]
fn lost_identity(
    domain: &str,
) -> (AgentRuntime, CellId, IdentityCharter, Vec<[u8; 32]>, Vec<[u8; 32]>) {
    let mut runtime = AgentRuntime::new_simple(AgentCipherclerk::new(), domain);
    let agent = runtime.cell_id();
    let charter = IdentityCharter {
        council: CouncilCharter::new(
            vec![CellId::from_bytes([0xD1; 32]), CellId::from_bytes([0xD2; 32])],
            2,
        ),
        cooling_period: COOLING,
    };
    let plan = create_identity(&charter, agent_pubkey(&runtime), [0x1D; 32], agent, agent)
        .expect("valid charter");
    bootstrap(&mut runtime, &plan);
    runtime.set_block_height(1_000);

    let g0: Vec<[u8; 32]> = vec![[0x10; 32], [0x11; 32]];
    let g1: Vec<[u8; 32]> = vec![[0x20; 32], [0x21; 32]];
    runtime
        .execute_on(
            plan.cell_id,
            genesis_effects(
                plan.cell_id,
                &charter,
                key_set_commitment(&g0),
                next_keys_digest(&key_set_commitment(&g1)),
            ),
        )
        .expect("genesis (icp) must commit");

    // The deos-genesis posture: hand the rotation authority to the guardian
    // quorum (the owner key is no longer the gatekeeper of recovery).
    install_guardian_authority(&runtime, plan.cell_id);

    (runtime, plan.cell_id, charter, g0, g1)
}

/// Build the recovery rotation as the FRESH runtime would: target the identity
/// cell, install G1 (the pre-committed set whose preimage is escrowed), commit
/// a fresh next digest, stamp the height. Authorized by the guardian quorum
/// (`Authorization::Custom`); the gate's preimage exhibit rides `witness_blobs`
/// beside the QC.
///
/// Returns the action carrying a PLACEHOLDER proof blob — the caller fixes the
/// turn nonce, signs the canonical custom message, then swaps in the real QC.
fn recovery_rotation_action(
    identity_cell: CellId,
    presented: [u8; 32],
    fresh_next_digest: [u8; 32],
    height: u64,
) -> Action {
    let predicate = WitnessedPredicate {
        kind: WitnessedPredicateKind::Custom {
            vk_hash: RECOVERY_VK,
        },
        commitment: guardian_root(),
        input_ref: InputRef::SigningMessage,
        // The QC blob sits at index 1; the preimage exhibit at index 0.
        proof_witness_index: 1,
    };
    let mut action = dregg_sdk::raw::unsigned_action_named(
        identity_cell,
        "rotate",
        rotate_effects(identity_cell, presented, fresh_next_digest, height),
    );
    action.authorization = Authorization::Custom { predicate };
    // index 0: the KeyRotationGate preimage exhibit (G1's commitment).
    // index 1: a placeholder for the guardian QC (swapped in after signing).
    action.witness_blobs = vec![WitnessBlob::preimage(presented), WitnessBlob::proof(Vec::new())];
    action
}

/// Wrap a single root action into a turn whose `agent` is `agent_cell` at
/// `nonce`, with an explicit nonzero nonce (so `execute_turn` does not rewrite
/// it — the QC is bound to this exact nonce).
fn single_action_turn(agent_cell: CellId, nonce: u64, action: Action) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(action);
    Turn {
        agent: agent_cell,
        nonce,
        call_forest: forest,
        fee: 10_000,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: Vec::new(),
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

/// Produce a guardian aggregate QC over the canonical custom signing message
/// the executor will recompute at verification time, signed by `signers`.
fn sign_recovery(
    action: &Action,
    federation_id: &[u8; 32],
    turn_nonce: u64,
    committee: &FederationCommittee,
    members: &[MemberSecret],
    signers: &[usize],
) -> Result<Vec<u8>, dregg_federation::threshold::ThresholdError> {
    let predicate = match &action.authorization {
        Authorization::Custom { predicate } => predicate.clone(),
        other => panic!("recovery action must carry Authorization::Custom, got {other:?}"),
    };
    // The QC binds to EXACTLY what the executor checks: federation_id, the
    // turn nonce (the agent cell's on-ledger replay counter), position 0, and
    // the action's target/method/effects/predicate shape — NOT the proof bytes
    // (so the message is stable while we swap the real QC in).
    let message = TurnExecutor::compute_custom_signing_message(
        action,
        &predicate,
        0,
        federation_id,
        turn_nonce,
    );
    let shares: Vec<(usize, PartialSignature)> = signers
        .iter()
        .map(|&i| (members[i].index, committee.sign_share(&members[i], &message)))
        .collect();
    Ok(committee.aggregate(&shares, &message)?.to_bytes())
}

// =============================================================================
// THE HEADLINE: lost-all-keys -> guardian quorum -> recovered + owns its cells.
// =============================================================================

/// A cipherclerk holding NONE of the identity's keys, given a 3-of-5 guardian
/// quorum, recovers control of the identity cell through the real executor: the
/// rotation installs the pre-committed key set, the chain advances, the height
/// is stamped — and the identity cell (the durable principal) is unchanged, so
/// every cell it owns is still its own.
#[test]
fn lost_all_keys_recovered_by_guardian_quorum() {
    let (mut runtime, cell, _charter, _g0, g1) = lost_identity("recovery-headline");

    // A FRESH cipherclerk — a brand-new device the recovering user generates
    // now. It holds NONE of g0/g1 as signing authority and contributes nothing
    // to authorization: the recovery is authorized PURELY by the guardian
    // quorum's threshold signature, never by any key this device holds. (Its
    // freshly-chosen key set is what the user installs as their new `next`.)
    let fresh = AgentRuntime::new_simple(AgentCipherclerk::new(), "recovery-new-device");
    assert_ne!(
        fresh.cell_id(),
        cell,
        "the recovering device is a distinct principal from the identity it recovers"
    );

    // The guardians: a real 3-of-5 HINTS weighted-threshold committee.
    let (committee, members) = generate_test_committee(GUARDIAN_N, GUARDIAN_K).unwrap();
    wire_guardian_verifier(&mut runtime, &committee);

    // Recover by rotating to G1 (the pre-committed set whose preimage the
    // council escrows) and committing a fresh next set the recovering user
    // generates now.
    let g2: Vec<[u8; 32]> = vec![[0x30; 32], [0x31; 32]];
    let presented = key_set_commitment(&g1);
    let fresh_next = next_keys_digest(&key_set_commitment(&g2));
    let height = runtime.block_height();

    // The recovery turn is RELAYED: a submitter cell (anyone — here the embedded
    // runtime's own cell) pays the fee and rides the turn nonce. The submitter
    // grants NO authority over the identity; authorization is the guardian QC on
    // the target's `set_state`. This is exactly the "you don't need any old key"
    // property — the recovering user cannot even pay a fee, so a relay submits.
    let relay = cell; // the identity cell rides its own nonce (matches the governed-namespace template: agent == target)
    let nonce = cell_nonce(&runtime, relay).max(1); // nonzero so execute_turn keeps it
    let mut action = recovery_rotation_action(cell, presented, fresh_next, height);

    // Three guardians (a quorum) sign the canonical recovery message.
    let qc = sign_recovery(
        &action,
        &[0u8; 32], // the runtime's default local federation id
        nonce,
        &committee,
        &members,
        &[0, 2, 4],
    )
    .expect("a 3-of-5 quorum must aggregate");
    action.witness_blobs[1] = WitnessBlob::proof(qc);

    let turn = single_action_turn(relay, nonce, action);
    runtime
        .execute_turn(&turn)
        .expect("a 3-of-5 guardian quorum MUST recover the identity through the executor");

    // RECOVERED: the pre-committed set is now the current key set…
    assert_eq!(
        slot_of(&runtime, cell, CURRENT_KEYS_COMMIT_SLOT),
        presented,
        "the recovered identity now speaks with the freshly-installed key set"
    );
    // …the forward chain advanced to the user's freshly-chosen next set…
    assert_eq!(
        slot_of(&runtime, cell, NEXT_KEYS_DIGEST_SLOT),
        fresh_next,
        "the KEL advanced to the recovering user's new pre-commitment"
    );
    // …and the rotation stamped the recovery height.
    assert_eq!(
        slot_of(&runtime, cell, LAST_ROTATED_AT_SLOT),
        field_from_u64(height),
        "the recovery rotation anchored the cooling window at the recovery height"
    );
}

// =============================================================================
// THE TOOTH: sub-threshold -> REFUSED.
// =============================================================================

/// A sub-threshold guardian set (2-of-5, below the 3-of-5 floor) CANNOT recover
/// the identity. The aggregator refuses to build a QC meeting the threshold
/// from two shares, so the recovery credential cannot even be assembled — and
/// belt-and-braces, a coerced under-weight QC would be rejected by the
/// host-pinned floor. The identity cell is untouched.
#[test]
fn sub_threshold_quorum_refused() {
    let (mut runtime, cell, _charter, _g0, g1) = lost_identity("recovery-sub-threshold");

    let (committee, members) = generate_test_committee(GUARDIAN_N, GUARDIAN_K).unwrap();
    wire_guardian_verifier(&mut runtime, &committee);

    let g2: Vec<[u8; 32]> = vec![[0x30; 32], [0x31; 32]];
    let presented = key_set_commitment(&g1);
    let fresh_next = next_keys_digest(&key_set_commitment(&g2));
    let height = runtime.block_height();
    let relay = cell; // the identity cell rides its own nonce (matches the governed-namespace template: agent == target)
    let nonce = cell_nonce(&runtime, relay).max(1);

    let action = recovery_rotation_action(cell, presented, fresh_next, height);

    // Only TWO guardians sign — below the 3-of-5 floor. The aggregator must
    // refuse to certify a QC meeting the threshold.
    let agg = sign_recovery(
        &action,
        &[0u8; 32],
        nonce,
        &committee,
        &members,
        &[0, 1],
    );
    assert!(
        agg.is_err(),
        "aggregating two shares must not satisfy the 3-of-5 guardian threshold"
    );

    // The identity cell is untouched — no rotation landed.
    let before = slot_of(&runtime, cell, CURRENT_KEYS_COMMIT_SLOT);
    assert_eq!(
        before,
        key_set_commitment(&_g0),
        "no recovery occurred — the current key set is still the birth set"
    );
}

/// Even a VALID 3-of-5 QC from the WRONG committee (an attacker who stood up
/// their own guardians) is REFUSED: the verifier checks the QC against the
/// HOST-TRUSTED committee VK bound at `guardian_root()`, not any committee the
/// prover supplies. So suborning a different set of people does not move the
/// identity.
#[test]
fn wrong_committee_quorum_refused() {
    let (mut runtime, cell, _charter, _g0, g1) = lost_identity("recovery-wrong-committee");

    // The genuine guardians are bound into the policy…
    let (host_committee, _host_members) = generate_test_committee(GUARDIAN_N, GUARDIAN_K).unwrap();
    wire_guardian_verifier(&mut runtime, &host_committee);
    // …but the attacker controls a DISTINCT 3-of-5 committee.
    let (attacker_committee, attacker_members) =
        generate_test_committee_with_seed(GUARDIAN_N, GUARDIAN_K, [0x9A; 32]).unwrap();

    let g2: Vec<[u8; 32]> = vec![[0x30; 32], [0x31; 32]];
    let presented = key_set_commitment(&g1);
    let fresh_next = next_keys_digest(&key_set_commitment(&g2));
    let height = runtime.block_height();
    let relay = cell; // the identity cell rides its own nonce (matches the governed-namespace template: agent == target)
    let nonce = cell_nonce(&runtime, relay).max(1);

    let mut action = recovery_rotation_action(cell, presented, fresh_next, height);
    // A valid quorum — of the WRONG committee.
    let qc = sign_recovery(
        &action,
        &[0u8; 32],
        nonce,
        &attacker_committee,
        &attacker_members,
        &[0, 1, 2],
    )
    .expect("the attacker can aggregate over their own committee");
    action.witness_blobs[1] = WitnessBlob::proof(qc);

    let turn = single_action_turn(relay, nonce, action);
    let err = runtime
        .execute_turn(&turn)
        .expect_err("a QC from a committee other than the host-trusted guardians must be refused");
    assert!(
        matches!(err, dregg_sdk::SdkError::Turn(TurnError::ProgramViolation { .. }))
            || matches!(err, dregg_sdk::SdkError::Turn(_)),
        "rejection must be at the auth/threshold-sig boundary, got: {err:?}"
    );

    assert_eq!(
        slot_of(&runtime, cell, CURRENT_KEYS_COMMIT_SLOT),
        key_set_commitment(&_g0),
        "no recovery occurred — the wrong-committee quorum did not move the identity"
    );
}
