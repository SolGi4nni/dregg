//! End-to-end teeth for IDENTITY PRE-ROTATION on the REAL executor.
//!
//! The identity rider (`docs/ORGANS.md`): every key-state event in an
//! identity cell commits to the digest of the NEXT, unexposed key set;
//! rotation must exhibit the preimage. Compromise of current keys no longer
//! suffices to rotate. Kernel semantics proven in
//! `metatheory/Dregg2/Apps/PreRotation.lean`; the cell program lives in
//! `starbridge_polis::identity` (`StateConstraint::KeyRotationGate`).
//!
//! These tests drive `AgentRuntime` (the embedded `TurnExecutor`) with
//! turns built by `dregg_sdk::identity`. Every safety property is enforced
//! by the factory-installed cell program — the negative tests hand the
//! executor WELL-SIGNED turns (the owner key signs; at the executor level
//! that is "signed by the current authority") and assert the EXECUTOR
//! rejects with `TurnError::ProgramViolation`. That is the whole point of
//! pre-rotation: signatures by current keys contribute nothing toward
//! rotating (`rotate_current_keys_irrelevant`).

use dregg_cell::{CellId, field_from_u64};
use dregg_sdk::factories::ADOPT_TURN_FEE;
use dregg_sdk::identity::{
    CURRENT_KEYS_COMMIT_SLOT, COUNCIL_COMMIT_SLOT, IdentityCharter, IdentityState,
    LAST_ROTATED_AT_SLOT, NEXT_KEYS_DIGEST_SLOT, STATE_ACTIVE, STATE_SLOT, create_identity,
    genesis_effects, inspect_identity, key_set_commitment, next_keys_digest, rotate_effects,
};
use dregg_sdk::polis::{CouncilCharter, GovernanceCellPlan};
use dregg_sdk::{AgentCipherclerk, AgentRuntime, SdkError};
use dregg_turn::TurnError;

// =============================================================================
// Harness (matches sdk/tests/polis_governance_e2e.rs)
// =============================================================================

const COOLING: u64 = 50;

fn harness(domain: &str) -> (AgentRuntime, CellId, IdentityCharter) {
    let runtime = AgentRuntime::new_simple(AgentCipherclerk::new(), domain);
    let agent = runtime.cell_id();
    let charter = IdentityCharter {
        // Two devices, both must sign grave acts — the council commitment
        // is pinned on the identity cell (the governance face; rotation
        // ceremonies ride the existing council machinery).
        council: CouncilCharter::new(
            vec![
                CellId::from_bytes([0xD1; 32]),
                CellId::from_bytes([0xD2; 32]),
            ],
            2,
        ),
        cooling_period: COOLING,
    };
    (runtime, agent, charter)
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

fn assert_program_violation<T>(result: Result<T, SdkError>, what: &str) {
    match result {
        Err(SdkError::Turn(TurnError::ProgramViolation { .. })) => {}
        Err(other) => panic!("{what}: expected ProgramViolation, got {other:?}"),
        Ok(_) => panic!("{what}: expected the EXECUTOR to reject, but the turn committed"),
    }
}

/// A bootstrapped, genesis'd identity at height 1_000 holding generation
/// G0 with G1 pre-committed. Returns (runtime, cell, charter, g0, g1
/// key sets).
#[allow(clippy::type_complexity)]
fn live_identity(
    domain: &str,
) -> (
    AgentRuntime,
    CellId,
    IdentityCharter,
    Vec<[u8; 32]>,
    Vec<[u8; 32]>,
) {
    let (mut runtime, agent, charter) = harness(domain);
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
    (runtime, plan.cell_id, charter, g0, g1)
}

// =============================================================================
// The teeth
// =============================================================================

/// Genesis installs the first pre-commitment; the registers and the pinned
/// council commitment read back; the cell is ACTIVE.
#[test]
fn genesis_installs_the_first_precommitment() {
    let (runtime, cell, charter, g0, g1) = live_identity("identity-genesis");
    assert_eq!(slot_of(&runtime, cell, STATE_SLOT), field_from_u64(STATE_ACTIVE));
    assert_eq!(
        slot_of(&runtime, cell, CURRENT_KEYS_COMMIT_SLOT),
        key_set_commitment(&g0)
    );
    assert_eq!(
        slot_of(&runtime, cell, NEXT_KEYS_DIGEST_SLOT),
        next_keys_digest(&key_set_commitment(&g1))
    );
    assert_eq!(
        slot_of(&runtime, cell, COUNCIL_COMMIT_SLOT),
        charter.council.members_commitment()
    );

    // Legibility: the shared decoder reads the key state back.
    let fields = runtime
        .ledger()
        .lock()
        .unwrap()
        .get(&cell)
        .unwrap()
        .state
        .fields;
    let status = inspect_identity(&charter, &fields);
    assert_eq!(status.state, IdentityState::Active);
    assert!(status.council_commit_matches);
}

/// HONEST ROTATION: exhibiting the committed preimage installs the new key
/// set, advances the chain, and stamps the height.
#[test]
fn honest_rotation_exhibits_preimage_and_chains() {
    let (runtime, cell, _charter, _g0, g1) = live_identity("identity-honest-rotate");
    let g2: Vec<[u8; 32]> = vec![[0x30; 32], [0x31; 32]];
    let digest_before = slot_of(&runtime, cell, NEXT_KEYS_DIGEST_SLOT);

    runtime
        .rotate_identity(cell, &g1, next_keys_digest(&key_set_commitment(&g2)))
        .expect("honest rotation must commit");

    // Installed: the exhibited commitment IS the new current set…
    let current_after = slot_of(&runtime, cell, CURRENT_KEYS_COMMIT_SLOT);
    assert_eq!(current_after, key_set_commitment(&g1));
    // …and it is the preimage of the PRE-state register (the exhibit).
    assert_eq!(next_keys_digest(&current_after), digest_before);
    // The chain advanced to the fresh commitment.
    assert_eq!(
        slot_of(&runtime, cell, NEXT_KEYS_DIGEST_SLOT),
        next_keys_digest(&key_set_commitment(&g2))
    );
    // The cooling anchor stamped the rotation height.
    assert_eq!(
        slot_of(&runtime, cell, LAST_ROTATED_AT_SLOT),
        field_from_u64(1_000)
    );
}

/// FORGED KEY SET REFUSED: a thief presenting any key set other than the
/// pre-committed one is rejected BY THE EXECUTOR — an admitted forgery
/// would BE a hash collision (`rotate_compromise_resistant`).
#[test]
fn forged_key_set_refused() {
    let (runtime, cell, _charter, _g0, _g1) = live_identity("identity-forged");
    let thief_keys: Vec<[u8; 32]> = vec![[0xEE; 32]];
    assert_program_violation(
        runtime
            .rotate_identity(cell, &thief_keys, next_keys_digest(&[0x99; 32])),
        "rotation presenting a non-committed key set",
    );
}

/// THE COMPROMISE-RESISTANCE TOOTH: a rotation WITHOUT exhibiting the
/// preimage is refused even though the turn is signed by the identity's
/// CURRENT authority (the owner key — at the executor level, "signed by
/// all current keys"). Current keys do not occur in the rotate guard.
#[test]
fn rotation_without_preimage_refused_even_when_signed() {
    let (runtime, cell, _charter, _g0, g1) = live_identity("identity-no-preimage");
    let g2: Vec<[u8; 32]> = vec![[0x30; 32], [0x31; 32]];
    // The same effects an honest rotation carries — but no `reveal`.
    // The signature is real and verifies; the EXECUTOR still refuses.
    assert_program_violation(
        runtime.execute_on(
            cell,
            rotate_effects(
                cell,
                key_set_commitment(&g1),
                next_keys_digest(&key_set_commitment(&g2)),
                1_000,
            ),
        ),
        "rotation signed by current authority but not exhibiting the preimage",
    );
}

/// COOLING COMPOSITION: a preimage-HOLDING rotation still waits out the
/// charter's cooling window (slow + visible to the council); at the
/// boundary it commits. Strict domination, executor-level.
#[test]
fn cooling_blocks_preimage_holding_rotation() {
    let (mut runtime, cell, _charter, _g0, g1) = live_identity("identity-cooling");
    let g2: Vec<[u8; 32]> = vec![[0x30; 32], [0x31; 32]];
    let g3: Vec<[u8; 32]> = vec![[0x40; 32], [0x41; 32]];

    // First rotation at height 1_000 (cooled from genesis anchor 0).
    runtime
        .rotate_identity(cell, &g1, next_keys_digest(&key_set_commitment(&g2)))
        .expect("first rotation must commit");

    // Inside the window (1_000 + 50 > 1_049): refused WITH the preimage.
    runtime.set_block_height(1_049);
    assert_program_violation(
        runtime
            .rotate_identity(cell, &g2, next_keys_digest(&key_set_commitment(&g3))),
        "preimage-holding rotation inside the cooling window",
    );

    // At the boundary (1_000 + 50 <= 1_050): admitted.
    runtime.set_block_height(1_050);
    runtime
        .rotate_identity(cell, &g2, next_keys_digest(&key_set_commitment(&g3)))
        .expect("cooled rotation must commit");
    assert_eq!(
        slot_of(&runtime, cell, LAST_ROTATED_AT_SLOT),
        field_from_u64(1_050)
    );
}

/// CHAIN PINNING: across two rotations, each installed commitment is the
/// preimage of the previous register value — the public commitment stream
/// reconstructs the whole key history (`rotChain_pinned_by_commitments`),
/// and a stale generation can never be replayed.
#[test]
fn commitment_stream_reconstructs_key_history() {
    let (mut runtime, cell, _charter, g0, g1) = live_identity("identity-chain");
    let g2: Vec<[u8; 32]> = vec![[0x30; 32], [0x31; 32]];
    let g3: Vec<[u8; 32]> = vec![[0x40; 32], [0x41; 32]];

    // Record the genesis link.
    let mut history = vec![(
        slot_of(&runtime, cell, CURRENT_KEYS_COMMIT_SLOT),
        slot_of(&runtime, cell, NEXT_KEYS_DIGEST_SLOT),
    )];

    runtime
        .rotate_identity(cell, &g1, next_keys_digest(&key_set_commitment(&g2)))
        .expect("rotation G0→G1");
    history.push((
        slot_of(&runtime, cell, CURRENT_KEYS_COMMIT_SLOT),
        slot_of(&runtime, cell, NEXT_KEYS_DIGEST_SLOT),
    ));

    runtime.set_block_height(1_100);
    runtime
        .rotate_identity(cell, &g2, next_keys_digest(&key_set_commitment(&g3)))
        .expect("rotation G1→G2");
    history.push((
        slot_of(&runtime, cell, CURRENT_KEYS_COMMIT_SLOT),
        slot_of(&runtime, cell, NEXT_KEYS_DIGEST_SLOT),
    ));

    // The KEL property, link for link: every installed commitment is the
    // preimage of the PREVIOUS event's published next-digest.
    for w in history.windows(2) {
        let (_, prev_digest) = w[0];
        let (installed, _) = w[1];
        assert_eq!(
            next_keys_digest(&installed),
            prev_digest,
            "each rotation exposes exactly the set the previous event committed"
        );
    }
    // And the exposed sets are exactly G0, G1, G2 — the key history.
    assert_eq!(history[0].0, key_set_commitment(&g0));
    assert_eq!(history[1].0, key_set_commitment(&g1));
    assert_eq!(history[2].0, key_set_commitment(&g2));

    // A stale generation (G1, already exposed) can never re-rotate.
    runtime.set_block_height(1_200);
    assert_program_violation(
        runtime
            .rotate_identity(cell, &g1, next_keys_digest(&[0x99; 32])),
        "replaying an exposed (stale) key generation",
    );
}

/// The factory is content-addressed over the charter: same charter → same
/// factory; a different cooling window or council → a different identity
/// factory (auditable from the published terms alone).
#[test]
fn identity_factory_is_content_addressed() {
    let (_, _, charter) = harness("identity-ca");
    let a = dregg_sdk::identity::identity_factory_descriptor(&charter).unwrap();
    let b = dregg_sdk::identity::identity_factory_descriptor(&charter).unwrap();
    assert_eq!(a.factory_vk, b.factory_vk);
    let mut hastier = charter.clone();
    hastier.cooling_period = 1;
    let c = dregg_sdk::identity::identity_factory_descriptor(&hastier).unwrap();
    assert_ne!(a.factory_vk, c.factory_vk);
}
