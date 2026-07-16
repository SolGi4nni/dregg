//! **THE CUSTOM-VK DOOR** — the Custom-VK extension point is reachable from a turn.
//!
//! ## What was broken
//!
//! The Custom-VK carrier was real and general — `VmEffect::Custom`, the
//! `customVmDescriptor2R24` rotated member, the `custom_state_binding` ABI, the
//! registry dispatch, the per-turn fold — and STRUCTURALLY UNREACHABLE. There was no
//! `Effect::Custom` in `dregg_turn::action::Effect`, so:
//!
//!   * `convert_turn_effects_to_vm` could never emit a `VmEffect::Custom` row, hence
//!     `enforce_custom_proof_count_committed` computed `committed = 0` for EVERY turn
//!     and any turn carrying `custom_program_proofs` was rejected with
//!     `CustomProofCountMismatch { wire: n, committed: 0 }`; and
//!   * the executor's rotated PI reconstruction had no Custom arm, so a custom lead
//!     fell through to the transfer shape and could never reconstruct.
//!
//! No Custom-VK game (the Braid resolver) could run. These tests drive the door.
//!
//! ## What is driven here, and what is not
//!
//! Everything in this file is FAST — no STARK is minted. That is possible because the
//! executor's custom gauntlet runs in this order, and the state weld precedes the
//! expensive leg verify:
//!
//! ```text
//!   verify_and_commit_proof
//!     1. enforce_custom_effect_proofs        (registry dispatch — the DoS cap, then verify)
//!     2. verify_and_commit_proof_rotated
//!          a. read stored OLD / claimed NEW commitments
//!          b. convert_turn_effects_to_vm      ← THE DOOR
//!          c. enforce_custom_proof_state_binding  ← THE WELD  (before any proof parse)
//!          d. postcard-parse + verify the rotated leg          (the expensive part)
//!     3. enforce_custom_proof_count_committed
//! ```
//!
//! So a turn carrying a deliberately-unparseable `execution_proof` still drives 1, 2a,
//! 2b and 2c for real, through `TurnExecutor::execute`. A mismatched-root custom proof
//! is refused at 2c (`CustomProofStateBindingMismatch`) and an honest-root one gets
//! PAST 2c and dies at 2d (`InvalidExecutionProof`) — which is exactly the
//! discrimination the weld exists to make, observed end-to-end via a turn rather than
//! by calling the weld helper directly.
//!
//! The remaining leg — a turn carrying a VALID rotated custom `execution_proof`
//! COMMITS — needs a minutes-slow STARK and lives in the `#[ignore]`d fold test
//! (`custom_vk_door_commits`, run with `--ignored` on the build box).

// The `door_*__*` test names use a double underscore to separate the CLAIM from the
// property it drives; that reads better in `cargo test` output than one long snake run.
#![allow(non_snake_case)]

use std::sync::Arc;

use dregg_cell::{
    Cell, CellId, CellMode, CustomEffectError, CustomEffectRegistry, CustomEffectVerifier, Ledger,
    Permissions,
};
use dregg_cell::{ProvingSystemId, VerifierFingerprint, VkComponents, canonical_vk_v2};
use dregg_circuit::effect_vm::Effect as VmEffect;
use dregg_circuit::effect_vm::custom_state_binding::{
    CUSTOM_PI_STATE_PREFIX_LEN, custom_pi_state_prefix,
};
use dregg_circuit::field::BabyBear;
use dregg_turn::action::Effect;
use dregg_turn::executor::convert_turn_effects_to_vm;
use dregg_turn::turn::CustomProgramProof;
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Turn, TurnError,
    TurnExecutor, TurnResult,
};

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

fn open_permissions() -> Permissions {
    Permissions {
        send: dregg_cell::AuthRequired::None,
        receive: dregg_cell::AuthRequired::None,
        set_state: dregg_cell::AuthRequired::None,
        set_permissions: dregg_cell::AuthRequired::None,
        set_verification_key: dregg_cell::AuthRequired::None,
        increment_nonce: dregg_cell::AuthRequired::None,
        delegate: dregg_cell::AuthRequired::None,
        access: dregg_cell::AuthRequired::None,
    }
}

fn make_open_cell(seed: u8, balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = seed;
    pk[31] = seed.wrapping_mul(37);
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

/// A custom-effect verifier that ACCEPTS any non-empty proof.
///
/// This is deliberate and it does NOT launder the test: the object under test here is
/// the DOOR and the STATE WELD, not the sub-proof's algebra. The weld's whole point is
/// that a sub-proof which VERIFIES can still be about the wrong transition — so the
/// honest way to exercise it is with a verifier that accepts, then to show the weld
/// refuses the mismatched-root proof anyway. A rejecting verifier would short-circuit
/// at step 1 and prove nothing about the weld.
struct AlwaysAcceptVerifier {
    vk_hash: [u8; 32],
}

impl CustomEffectVerifier for AlwaysAcceptVerifier {
    fn name(&self) -> &'static str {
        "custom-vk-door-test-accept"
    }
    fn vk_hash(&self) -> [u8; 32] {
        self.vk_hash
    }
    fn verify(&self, _public_inputs: &[u8], proof_bytes: &[u8]) -> Result<(), CustomEffectError> {
        if proof_bytes.is_empty() {
            return Err(CustomEffectError::Rejected {
                vk_hash: self.vk_hash,
                name: "custom-vk-door-test-accept",
                reason: "empty proof".to_string(),
            });
        }
        Ok(())
    }
}

/// Register an accepting verifier under a genuine v2 vk_hash and return
/// `(registry, vk_hash)`. The vk is the real `canonical_vk_v2` binding
/// (program bytes + AIR fingerprint + verifier fingerprint + proving system), so the
/// registry's own layered-binding check is satisfied honestly, not bypassed.
fn registry_with_accepting_verifier() -> (CustomEffectRegistry, [u8; 32]) {
    let program_bytes = b"dregg-custom-vk-door-demo-program-v1".to_vec();
    let air_fingerprint = *blake3::hash(b"door-air").as_bytes();
    let verifier_fingerprint =
        VerifierFingerprint::SourceHash(*blake3::hash(b"door-verif").as_bytes());
    let proving_system_id = ProvingSystemId::Plonky3BabyBearFri {
        p3_rev: "custom-vk-door-test",
    };

    let vk_hash = canonical_vk_v2(&VkComponents {
        program_bytes: &program_bytes,
        air_fingerprint,
        verifier_fingerprint: verifier_fingerprint.clone(),
        proving_system_id: proving_system_id.clone(),
    });

    let mut registry = CustomEffectRegistry::empty();
    registry
        .register(
            program_bytes,
            air_fingerprint,
            verifier_fingerprint,
            proving_system_id,
            Arc::new(AlwaysAcceptVerifier { vk_hash }),
        )
        .expect("the accepting verifier registers under its own v2 vk_hash");
    (registry, vk_hash)
}

/// The 8-felt commitment carrier for a 32-byte commitment, as the executor reads it.
fn felt8(bytes: &[u8; 32]) -> [BabyBear; 8] {
    dregg_cell::commitment::bytes32_to_felt8(bytes)
}

/// Build a `CustomProgramProof` whose public inputs are
/// `[old8 ‖ new8 ‖ ..app]` per the `custom_state_binding` ABI.
fn custom_proof_for(
    vk_hash: [u8; 32],
    old8: &[BabyBear; 8],
    new8: &[BabyBear; 8],
    app_pis: &[u32],
) -> CustomProgramProof {
    let mut pis: Vec<u32> = custom_pi_state_prefix(old8, new8)
        .iter()
        .map(|f| f.0)
        .collect();
    pis.extend_from_slice(app_pis);
    CustomProgramProof {
        vk_hash,
        // Non-empty so the registry's ProofMissing guard passes; the accepting
        // verifier takes it. Deliberately NOT a real STARK — see the module doc.
        proof_bytes: vec![0xAB; 32],
        public_inputs: pis,
    }
}

fn turn_with(
    agent: CellId,
    effects: Vec<Effect>,
    execution_proof: Option<Vec<u8>>,
    execution_proof_cell: Option<CellId>,
    new_commitment: Option<[u8; 32]>,
    custom_program_proofs: Option<Vec<CustomProgramProof>>,
) -> Turn {
    let mut forest = CallForest::new();
    forest.add_root(Action {
        target: agent,
        method: [0u8; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: Default::default(),
        balance_change: None,
        witness_blobs: vec![],
    });
    Turn {
        agent,
        nonce: 0,
        call_forest: forest,
        fee: 0,
        memo: None,
        valid_until: None,
        previous_receipt_hash: None,
        depends_on: vec![],
        conservation_proof: None,
        sovereign_witnesses: std::collections::HashMap::new(),
        execution_proof,
        execution_proof_cell,
        execution_proof_new_commitment: new_commitment,
        custom_program_proofs,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

/// A sovereign cell registered at `commitment`, present in the hosted table too (the
/// proof-carrying path reads balance/nonce from the hosted cell and the committed root
/// from the sovereign map).
///
/// Order matters: `register_sovereign_cell` REFUSES if the id is already hosted
/// (`SovereignAlreadyExists`), so the commitment is registered first and the hosted
/// image inserted after.
fn setup_sovereign(commitment: [u8; 32]) -> (CellId, Ledger) {
    let mut cell = make_open_cell(1, 1_000);
    cell.mode = CellMode::Sovereign;
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    ledger
        .register_sovereign_cell(cell_id, commitment)
        .expect("sovereign registration");
    let _ = ledger.insert_cell(cell);
    (cell_id, ledger)
}

// ===========================================================================
// 1. THE DOOR ITSELF — the projection that was structurally absent.
// ===========================================================================

/// **THE DOOR.** A turn-level `Effect::Custom` now projects to a `VmEffect::Custom`
/// row, carrying the exact encodings the welds compare against.
///
/// CANARY: delete the `Effect::Custom` arm in
/// `executor::effect_vm_bridge::convert_turn_effects_to_vm` and this test fails — the
/// projection collapses to `vec![VmEffect::NoOp]` (the bridge's empty-effects
/// fallback), which is precisely the pre-door behavior that made `committed = 0`.
#[test]
fn door_open__effect_custom_projects_to_a_vm_custom_row() {
    let (_, vk_hash) = registry_with_accepting_verifier();
    let cell = make_open_cell(1, 0);
    let cell_id = cell.id();
    let proof_commitment = [0x5Cu8; 32];

    let turn = turn_with(
        cell_id,
        vec![Effect::Custom {
            cell: cell_id,
            program_vk_hash: vk_hash,
            proof_commitment,
        }],
        None,
        None,
        None,
        None,
    );

    let vm = convert_turn_effects_to_vm(&cell_id, &turn);

    assert_eq!(vm.len(), 1, "one Effect::Custom => exactly one VM row");
    match &vm[0] {
        VmEffect::Custom {
            program_vk_hash,
            proof_commitment: commit,
        } => {
            // The vk uses the IDENTIFIER encoding — byte-identical to what
            // `enforce_custom_proof_entry_binding` derives from the wire sub-proof's
            // vk_hash, so the committed VK PI and the dispatched verifier are comparable.
            assert_eq!(
                *program_vk_hash,
                dregg_circuit::effect_vm::bytes32_to_8_limbs(&vk_hash),
                "program_vk_hash must use the bytes32_to_8_limbs identifier encoding"
            );
            // The commitment uses the canonical 8-felt CARRIER round-trip — these are
            // real field elements the fold connects lane-for-lane, not a hashed id.
            assert_eq!(
                *commit,
                felt8(&proof_commitment),
                "proof_commitment must use the bytes32_to_felt8 carrier encoding"
            );
        }
        other => panic!("THE DOOR IS SHUT: expected VmEffect::Custom, got {other:?}"),
    }
}

/// **THE DOOR CANARY, quantified.** `enforce_custom_proof_count_committed` computes
/// `committed` by counting `VmEffect::Custom` rows in exactly this projection. Before
/// the door that count was 0 for every turn, so `wire != committed` rejected every
/// custom-carrying turn. Here the count TRACKS the effects.
#[test]
fn door_canary__committed_custom_count_tracks_the_effect_custom_count() {
    let (_, vk_hash) = registry_with_accepting_verifier();
    let cell = make_open_cell(1, 0);
    let cell_id = cell.id();

    let committed_count = |n: usize| -> usize {
        let effects: Vec<Effect> = (0..n)
            .map(|i| Effect::Custom {
                cell: cell_id,
                program_vk_hash: vk_hash,
                proof_commitment: [i as u8; 32],
            })
            .collect();
        let turn = turn_with(cell_id, effects, None, None, None, None);
        convert_turn_effects_to_vm(&cell_id, &turn)
            .iter()
            .filter(|e| matches!(e, VmEffect::Custom { .. }))
            .count()
    };

    assert_eq!(committed_count(0), 0, "no custom effects => committed 0");
    assert_eq!(
        committed_count(1),
        1,
        "THE DOOR: one Effect::Custom must commit one Custom row (was 0 — the gap)"
    );
    assert_eq!(committed_count(3), 3, "the count must track, not saturate");
}

/// A custom effect naming a DIFFERENT cell is not part of this cell's proof — the
/// bridge's per-cell guard. (Otherwise one cell's turn could inflate another's
/// committed custom count.)
#[test]
fn door_is_per_cell__a_custom_effect_for_another_cell_is_not_projected() {
    let (_, vk_hash) = registry_with_accepting_verifier();
    let mine = make_open_cell(1, 0).id();
    let theirs = make_open_cell(2, 0).id();

    let turn = turn_with(
        mine,
        vec![Effect::Custom {
            cell: theirs,
            program_vk_hash: vk_hash,
            proof_commitment: [0x11u8; 32],
        }],
        None,
        None,
        None,
        None,
    );

    let vm = convert_turn_effects_to_vm(&mine, &turn);
    assert!(
        !vm.iter().any(|e| matches!(e, VmEffect::Custom { .. })),
        "a Custom effect targeting another cell must not project into this cell's proof"
    );
}

/// **THE DOOR CANARY.** Reachability disabled, without touching code: the SAME
/// proof-carrying turn but with NO `Effect::Custom` marker in its effects — exactly the
/// pre-door world, where a custom sub-proof rode `custom_program_proofs` with nothing
/// projecting a `VmEffect::Custom` row.
///
/// The precise mechanism the door moves is the COMMITTED COUNT that
/// `enforce_custom_proof_count_committed` compares the wire count against: without the
/// marker it is 0 (as it was for EVERY turn before the door), so any turn carrying a
/// custom sub-proof was doomed to `CustomProofCountMismatch { wire: n, committed: 0 }`.
/// We assert that count directly (cheap + exact — no fold needed), and confirm the turn
/// is still rejected end-to-end. `door_canary__committed_custom_count_tracks_the_effect_custom_count`
/// shows the OTHER pole: with the marker the count becomes 1.
#[test]
fn door_canary__without_the_effect_custom_marker_committed_count_is_zero() {
    let stored_old = [0x01u8; 32];
    let claimed_new = [0x02u8; 32];
    let (cell_id, mut ledger) = setup_sovereign(stored_old);
    let (registry, vk_hash) = registry_with_accepting_verifier();

    let proof = custom_proof_for(vk_hash, &felt8(&stored_old), &felt8(&claimed_new), &[7, 9]);

    // No Effect::Custom in the effects — the reachability leg is "disabled" for this turn.
    let turn = turn_with(
        cell_id,
        vec![], // <-- the door marker is ABSENT
        Some(vec![0xDEu8; 64]),
        Some(cell_id),
        Some(claimed_new),
        Some(vec![proof]),
    );

    // The pre-door invariant, exactly: no Effect::Custom => no VmEffect::Custom row =>
    // the committed count the wire proof count is checked against is 0. Wire is 1.
    let committed = convert_turn_effects_to_vm(&cell_id, &turn)
        .iter()
        .filter(|e| matches!(e, VmEffect::Custom { .. }))
        .count();
    assert_eq!(
        committed, 0,
        "CANARY: with the marker absent the committed custom count must be 0 (the pre-door state \
         — the wire count of 1 could then never match, the CustomProofCountMismatch every custom \
         turn hit)"
    );

    // And end-to-end the turn is still rejected (with this garbage proof it dies at the
    // leg parse, before the count gate — but rejected all the same; a custom turn without
    // the marker never commits).
    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_custom_effect_registry(registry);
    assert!(
        matches!(
            executor.execute(&turn, &mut ledger),
            TurnResult::Rejected { .. }
        ),
        "a custom proof with no Effect::Custom marker must not commit"
    );
}

// ===========================================================================
// 2. THE DOOR IS ONE-WAY — Custom is refused off the proof-carrying path.
// ===========================================================================

/// A turn carrying `Effect::Custom` with NO `execution_proof` goes down the classical
/// apply path, where there is no proof to dispatch, no claimed post-root to weld to,
/// and no sovereign commitment to advance. It is REFUSED fail-closed — not silently
/// no-op'd into a receipt that claims a custom transition happened.
///
/// Driven through `TurnExecutor::execute`.
#[test]
fn custom_effect_off_the_proof_carrying_path_is_refused_via_a_turn() {
    let (_, vk_hash) = registry_with_accepting_verifier();
    let cell = make_open_cell(1, 1_000);
    let cell_id = cell.id();
    let mut ledger = Ledger::new();
    let _ = ledger.insert_cell(cell);

    let turn = turn_with(
        cell_id,
        vec![Effect::Custom {
            cell: cell_id,
            program_vk_hash: vk_hash,
            proof_commitment: [0x5Cu8; 32],
        }],
        None, // no execution_proof => the classical path
        None,
        None,
        None,
    );

    let executor = TurnExecutor::new(ComputronCosts::zero());
    match executor.execute(&turn, &mut ledger) {
        TurnResult::Rejected { reason, .. } => assert!(
            matches!(
                reason,
                TurnError::CustomEffectRequiresProofCarryingTurn { cell } if cell == cell_id
            ),
            "expected CustomEffectRequiresProofCarryingTurn, got {reason:?}"
        ),
        other => panic!("an unproven custom transition must be REFUSED, not admitted: {other:?}"),
    }
}

// ===========================================================================
// 3. THE WELD, END-TO-END VIA A TURN (not the unit helper).
// ===========================================================================

/// **THE MISMATCH REFUSAL, VIA A TURN.** A custom sub-proof that VERIFIES (the
/// registered verifier accepts it) but whose `[old8, new8]` PI prefix is about a
/// DIFFERENT transition is refused — the host cannot staple a valid proof of some
/// other state onto this turn.
///
/// Note what this test does NOT rely on: the sub-proof's algebra (the verifier
/// accepts) and the rotated leg (never parsed — the weld fires first). The ONLY thing
/// that refuses this turn is the state weld, reached through the real executor.
#[test]
fn mismatched_root_custom_proof_is_refused_end_to_end_via_a_turn() {
    let stored_old = [0x01u8; 32];
    let claimed_new = [0x02u8; 32];
    let (cell_id, mut ledger) = setup_sovereign(stored_old);
    let (registry, vk_hash) = registry_with_accepting_verifier();

    // The forgery: a proof about SOME OTHER transition (0xEE -> 0xFF), not this
    // cell's committed 0x01 -> 0x02.
    let forged_old = felt8(&[0xEEu8; 32]);
    let forged_new = felt8(&[0xFFu8; 32]);
    let proof = custom_proof_for(vk_hash, &forged_old, &forged_new, &[7, 9]);

    let turn = turn_with(
        cell_id,
        vec![Effect::Custom {
            cell: cell_id,
            program_vk_hash: vk_hash,
            proof_commitment: [0x5Cu8; 32],
        }],
        Some(vec![0xDEu8; 64]), // deliberately unparseable — the weld fires first
        Some(cell_id),
        Some(claimed_new),
        Some(vec![proof]),
    );

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_custom_effect_registry(registry);

    match executor.execute(&turn, &mut ledger) {
        TurnResult::Rejected { reason, .. } => {
            assert!(
                matches!(
                    reason,
                    TurnError::CustomProofStateBindingMismatch { index: 0, .. }
                ),
                "a mismatched-root custom proof must be refused BY THE WELD; got {reason:?}"
            );
        }
        other => panic!("the forged-root custom turn must be REFUSED: {other:?}"),
    }

    // And the store did not move.
    assert_eq!(
        ledger.get_sovereign_commitment(&cell_id),
        Some(&stored_old),
        "a refused custom turn must not advance the sovereign commitment"
    );
}

/// **THE POSITIVE POLE, VIA A TURN.** The SAME turn shape with an HONEST prefix — the
/// cell's genuine stored OLD and this turn's claimed NEW — gets PAST the weld and dies
/// later, at the rotated-leg parse. That is the discrimination that matters: the weld
/// is not refusing everything, it is refusing exactly the wrong-transition proof.
///
/// (This is why the negative test above is meaningful rather than vacuous.)
#[test]
fn honest_root_custom_proof_passes_the_weld_via_a_turn() {
    let stored_old = [0x01u8; 32];
    let claimed_new = [0x02u8; 32];
    let (cell_id, mut ledger) = setup_sovereign(stored_old);
    let (registry, vk_hash) = registry_with_accepting_verifier();

    // HONEST: exactly the cell's committed pre-root and this turn's claimed post-root.
    let proof = custom_proof_for(vk_hash, &felt8(&stored_old), &felt8(&claimed_new), &[7, 9]);

    let turn = turn_with(
        cell_id,
        vec![Effect::Custom {
            cell: cell_id,
            program_vk_hash: vk_hash,
            proof_commitment: [0x5Cu8; 32],
        }],
        Some(vec![0xDEu8; 64]),
        Some(cell_id),
        Some(claimed_new),
        Some(vec![proof]),
    );

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_custom_effect_registry(registry);

    match executor.execute(&turn, &mut ledger) {
        TurnResult::Rejected { reason, .. } => {
            assert!(
                !matches!(reason, TurnError::CustomProofStateBindingMismatch { .. }),
                "the HONEST-root custom proof must PASS the weld — it was refused by it: {reason:?}"
            );
            assert!(
                !matches!(reason, TurnError::CustomProofCountMismatch { .. }),
                "THE DOOR: the honest custom turn must pass the count gate; got {reason:?}"
            );
            // It reached the leg verify and died there — the deliberately-unparseable
            // proof bytes. That is the expected terminus for a fast test.
            assert!(
                matches!(reason, TurnError::InvalidExecutionProof(_)),
                "expected to reach the rotated-leg parse; got {reason:?}"
            );
        }
        other => panic!(
            "with unparseable proof bytes the turn cannot commit; expected the leg-parse \
             refusal, got {other:?}"
        ),
    }
}

/// A sub-proof whose PI vector is too SHORT to carry the `[old8, new8]` prefix is
/// refused — never zero-padded into a false match against a genuine all-zero root.
#[test]
fn a_custom_proof_too_short_to_express_the_binding_is_refused_via_a_turn() {
    let stored_old = [0x01u8; 32];
    let (cell_id, mut ledger) = setup_sovereign(stored_old);
    let (registry, vk_hash) = registry_with_accepting_verifier();

    let short = CustomProgramProof {
        vk_hash,
        proof_bytes: vec![0xABu8; 32],
        public_inputs: vec![0u32; CUSTOM_PI_STATE_PREFIX_LEN - 1],
    };

    let turn = turn_with(
        cell_id,
        vec![Effect::Custom {
            cell: cell_id,
            program_vk_hash: vk_hash,
            proof_commitment: [0x5Cu8; 32],
        }],
        Some(vec![0xDEu8; 64]),
        Some(cell_id),
        Some([0x02u8; 32]),
        Some(vec![short]),
    );

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_custom_effect_registry(registry);

    match executor.execute(&turn, &mut ledger) {
        TurnResult::Rejected { reason, .. } => assert!(
            matches!(
                reason,
                TurnError::CustomProofStateBindingMismatch { index: 0, .. }
            ),
            "a too-short PI vector must be refused, not zero-padded; got {reason:?}"
        ),
        other => panic!("expected refusal, got {other:?}"),
    }
}

/// An UNREGISTERED custom program is refused before anything else — the fail-closed
/// registry dispatch, reached via a turn now that the door exists.
#[test]
fn an_unregistered_custom_program_is_refused_via_a_turn() {
    let stored_old = [0x01u8; 32];
    let claimed_new = [0x02u8; 32];
    let (cell_id, mut ledger) = setup_sovereign(stored_old);
    let (registry, _registered_vk) = registry_with_accepting_verifier();

    let stranger_vk = [0x77u8; 32];
    let proof = custom_proof_for(stranger_vk, &felt8(&stored_old), &felt8(&claimed_new), &[]);

    let turn = turn_with(
        cell_id,
        vec![Effect::Custom {
            cell: cell_id,
            program_vk_hash: stranger_vk,
            proof_commitment: [0x5Cu8; 32],
        }],
        Some(vec![0xDEu8; 64]),
        Some(cell_id),
        Some(claimed_new),
        Some(vec![proof]),
    );

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_custom_effect_registry(registry);

    match executor.execute(&turn, &mut ledger) {
        TurnResult::Rejected { reason, .. } => assert!(
            matches!(reason, TurnError::ProofVerificationFailed(_)),
            "an unregistered vk_hash must fail closed; got {reason:?}"
        ),
        other => panic!("expected fail-closed refusal, got {other:?}"),
    }
}

/// With NO registry configured at all, a custom-carrying turn is refused fail-closed
/// (the executor cannot honor a custom effect it has no verifier for).
#[test]
fn no_registry_configured_refuses_a_custom_turn() {
    let stored_old = [0x01u8; 32];
    let claimed_new = [0x02u8; 32];
    let (cell_id, mut ledger) = setup_sovereign(stored_old);
    let (_, vk_hash) = registry_with_accepting_verifier();

    let proof = custom_proof_for(vk_hash, &felt8(&stored_old), &felt8(&claimed_new), &[]);
    let turn = turn_with(
        cell_id,
        vec![Effect::Custom {
            cell: cell_id,
            program_vk_hash: vk_hash,
            proof_commitment: [0x5Cu8; 32],
        }],
        Some(vec![0xDEu8; 64]),
        Some(cell_id),
        Some(claimed_new),
        Some(vec![proof]),
    );

    // No `set_custom_effect_registry`.
    let executor = TurnExecutor::new(ComputronCosts::zero());
    match executor.execute(&turn, &mut ledger) {
        TurnResult::Rejected { reason, .. } => assert!(
            matches!(reason, TurnError::ProofVerificationFailed(_)),
            "no registry => fail closed; got {reason:?}"
        ),
        other => panic!("expected fail-closed refusal, got {other:?}"),
    }
}
