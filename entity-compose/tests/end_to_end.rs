//! **THE SUBSTRATE COMPOSES, END TO END.** A real ENTITY whose typed params live in a cell's
//! wide plane; a composition READ from those params proving a named outcome under a ruleset; a
//! turn carrying it through the Custom-VK Door and PAST the state weld against the entity's REAL
//! commitment — driven through `TurnExecutor::execute`, not by calling a helper.
//!
//! Everything here is FAST. The state weld runs BEFORE the minutes-slow leg-parse
//! (`turn/tests/custom_vk_door.rs` documents the ordering), so a turn with an honest state
//! prefix and a deliberately-unparseable `execution_proof` drives the registry dispatch, the
//! Door, and the WELD for real, then dies at the leg parse — the expected fast terminus. The
//! full ledger-advancing commit needs a real rotated STARK leg (minutes) and is named in the
//! crate doc; the composition's own leaf really proves in `tests/leaf_prove.rs` (`#[ignore]`).
//!
//! The role tags are opaque `u64`s with meaningless names — this crate knows no game.

#![allow(non_snake_case)]

use std::sync::Arc;

use dregg_cell::{
    CellId, CustomEffectError, CustomEffectRegistry, CustomEffectVerifier, ProvingSystemId,
    VerifierFingerprint, VkComponents, canonical_vk_v2,
};
use dregg_turn::action::Effect;
use dregg_turn::turn::CustomProgramProof;
use dregg_turn::{
    Action, Authorization, CallForest, ComputronCosts, DelegationMode, Turn, TurnError,
    TurnExecutor, TurnResult,
};

use dregg_entity_compose::{
    LandedComposition, PROJECTION_WIDE_BASE, compose_onto, deploy_entity, program_descriptor,
};
use dregg_param_compose::model::{Knot, LinearTerm, Ruleset, Subject};
use dregg_param_compose::shape::ComposeShape;

// Opaque role tags. Any `u64` is a role; the vocabulary is content.
const ROLE_ACTOR: u64 = 101;
const ROLE_PARTNER: u64 = 202;

fn shape() -> ComposeShape {
    ComposeShape::new(3, 4, 3, 2)
}

/// The primary entity's projection: identity 7, params `[2, 5, 0, 0]`.
fn actor() -> Subject {
    Subject {
        identity: 7,
        role: ROLE_ACTOR,
        params: vec![2, 5, 0, 0],
    }
}

/// A partner/context subject the ruleset also reads.
fn partner() -> Subject {
    Subject {
        identity: 9,
        role: ROLE_PARTNER,
        params: vec![3, 4, 0, 0],
    }
}

/// A law with one LINEAR term and one nonlinear KNOT (the part `StateConstraint` cannot express).
fn ruleset() -> Ruleset {
    Ruleset {
        id: 0xAB,
        version: 1,
        linear: vec![LinearTerm {
            role: ROLE_ACTOR,
            param: 0,
            coeff: 10,
        }],
        knots: vec![Knot {
            role_a: ROLE_ACTOR,
            param_a: 1,
            role_b: ROLE_PARTNER,
            param_b: 1,
            coeff: -2,
        }],
    }
}

// ---------------------------------------------------------------------------
// Executor-driving fixtures (mirroring turn/tests/custom_vk_door.rs)
// ---------------------------------------------------------------------------

/// Accepts any non-empty proof. Deliberate, and it does NOT launder the test: the object under
/// test is the entity commitment reaching the WELD (the substrate wiring), not the sub-proof's
/// algebra — which `tests/leaf_prove.rs` proves for real against the actual STARK.
struct AcceptVerifier {
    vk_hash: [u8; 32],
}

impl CustomEffectVerifier for AcceptVerifier {
    fn name(&self) -> &'static str {
        "entity-compose-door-accept"
    }
    fn vk_hash(&self) -> [u8; 32] {
        self.vk_hash
    }
    fn verify(&self, _public_inputs: &[u8], proof_bytes: &[u8]) -> Result<(), CustomEffectError> {
        if proof_bytes.is_empty() {
            return Err(CustomEffectError::Rejected {
                vk_hash: self.vk_hash,
                name: "entity-compose-door-accept",
                reason: "empty proof".to_string(),
            });
        }
        Ok(())
    }
}

/// Register an accepting verifier under a GENUINE v2 `vk_hash` derived from the composition
/// program's own descriptor — so the registry's layered binding is satisfied honestly.
fn registry_for(landed: &LandedComposition) -> (CustomEffectRegistry, [u8; 32]) {
    let program_bytes =
        postcard::to_allocvec(&program_descriptor(&landed.shape, &landed.composition))
            .expect("descriptor serializes");
    let air_fingerprint = *blake3::hash(b"entity-compose-air").as_bytes();
    let verifier_fingerprint =
        VerifierFingerprint::SourceHash(*blake3::hash(b"entity-compose-verifier").as_bytes());
    let proving_system_id = ProvingSystemId::Plonky3BabyBearFri {
        p3_rev: "entity-compose-door",
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
            Arc::new(AcceptVerifier { vk_hash }),
        )
        .expect("registers under its own v2 vk_hash");
    (registry, vk_hash)
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

/// Build the composition sub-proof CarryingProof for a landed composition and the vk it names.
fn custom_proof(vk_hash: [u8; 32], landed: &LandedComposition) -> CustomProgramProof {
    CustomProgramProof {
        vk_hash,
        // Non-empty so the registry's ProofMissing guard passes; NOT a real STARK (leaf_prove
        // mints that). The object under test is the entity commitment reaching the weld.
        proof_bytes: vec![0xAB; 32],
        public_inputs: landed.pis_u32(),
    }
}

// ===========================================================================
// THE HEADLINE — the substrate composes end to end.
// ===========================================================================

/// **A real entity's parameters compose into a committed outcome via a single verifiable turn.**
/// The entity's params live in the cell's wide plane and DETERMINE its commitment; a composition
/// read from those params proves under the ruleset; the turn carries it through the Door and gets
/// PAST the state weld against the entity's REAL commitment, dying only at the leg parse.
#[test]
fn entity_params_compose_and_the_turn_passes_the_door_and_the_weld() {
    let entity = deploy_entity(1, 1_000, actor());
    let landed = compose_onto(&entity, &[partner()], ruleset(), shape(), 4).expect("composes");

    // The composed outcome is exactly what the law licenses: 10*2 + (-2)*5*4 = 20 - 40 = -20.
    assert_eq!(landed.outcome, -20, "the ruleset's licensed outcome");
    assert!(
        landed.air_accepts(),
        "the honest composition must self-accept (the fast shadow of 'the leaf proves')"
    );

    let (cell_id, mut ledger, _entity) = entity.into_registered_ledger();
    assert_eq!(cell_id, landed.cell_id);
    let (registry, vk_hash) = registry_for(&landed);
    let proof = custom_proof(vk_hash, &landed);

    eprintln!(
        "entity commitment old8 = {:02x?}.. ; composition sub-proof carries {} PIs (cap 64)",
        &landed.old_commitment[..4],
        landed.pis.len()
    );

    let turn = turn_with(
        cell_id,
        vec![Effect::Custom {
            cell: cell_id,
            program_vk_hash: vk_hash,
            proof_commitment: [0x5C; 32],
        }],
        Some(vec![0xDE; 64]), // deliberately unparseable — the weld fires first
        Some(cell_id),
        Some(landed.new_commitment),
        Some(vec![proof]),
    );

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_custom_effect_registry(registry);

    match executor.execute(&turn, &mut ledger) {
        TurnResult::Rejected { reason, .. } => {
            assert!(
                !matches!(reason, TurnError::CustomProofStateBindingMismatch { .. }),
                "the composition proof carries the entity's REAL commitment — it must PASS the \
                 weld; got {reason:?}"
            );
            assert!(
                !matches!(reason, TurnError::CustomProofCountMismatch { .. }),
                "THE DOOR: the composition turn must pass the count gate; got {reason:?}"
            );
            assert!(
                !matches!(reason, TurnError::ProofVerificationFailed(_)),
                "the registry must ACCEPT the composition sub-proof; got {reason:?}"
            );
            assert!(
                matches!(reason, TurnError::InvalidExecutionProof(_)),
                "expected to reach the rotated-leg parse (everything the substrate is \
                 responsible for passed); got {reason:?}"
            );
        }
        other => panic!(
            "with unparseable proof bytes the turn cannot commit; expected the leg-parse \
             refusal, got {other:?}"
        ),
    }
}

// ===========================================================================
// THE WELD BITES — a proof about a DIFFERENT entity is refused. (CANARY)
// ===========================================================================

/// **A proof about a DIFFERENT entity's state is refused by the weld.** A SECOND entity with
/// different params has a different commitment; its honest composition, stapled onto the FIRST
/// entity's turn, is refused by the state weld — the wrong-transition refusal that makes the
/// positive test above meaningful. The store does not advance.
#[test]
fn a_composition_about_a_different_entity_is_refused_by_the_weld() {
    // The entity the turn is FOR.
    let entity = deploy_entity(1, 1_000, actor());
    let (cell_id, mut ledger, _entity) = entity.into_registered_ledger();

    // A DIFFERENT entity — different identity AND params -> a different commitment.
    let stranger = deploy_entity(
        2,
        1_000,
        Subject {
            identity: 11,
            role: ROLE_ACTOR,
            params: vec![9, 9, 0, 0],
        },
    );
    let stranger_landed =
        compose_onto(&stranger, &[partner()], ruleset(), shape(), 4).expect("composes");
    assert_ne!(
        stranger_landed.old_commitment,
        ledger.get_sovereign_commitment(&cell_id).copied().unwrap(),
        "the stranger's commitment must genuinely differ from the registered entity's"
    );

    let (registry, vk_hash) = registry_for(&stranger_landed);
    let proof = custom_proof(vk_hash, &stranger_landed);

    let turn = turn_with(
        cell_id,
        vec![Effect::Custom {
            cell: cell_id,
            program_vk_hash: vk_hash,
            proof_commitment: [0x5C; 32],
        }],
        Some(vec![0xDE; 64]),
        Some(cell_id),
        Some(stranger_landed.new_commitment),
        Some(vec![proof]),
    );

    let mut executor = TurnExecutor::new(ComputronCosts::zero());
    executor.set_custom_effect_registry(registry);

    let stored_before = *ledger.get_sovereign_commitment(&cell_id).unwrap();
    match executor.execute(&turn, &mut ledger) {
        TurnResult::Rejected { reason, .. } => assert!(
            matches!(
                reason,
                TurnError::CustomProofStateBindingMismatch { index: 0, .. }
            ),
            "a composition about another entity's state must be refused BY THE WELD; got {reason:?}"
        ),
        other => panic!("the wrong-entity composition turn must be REFUSED: {other:?}"),
    }
    assert_eq!(
        ledger.get_sovereign_commitment(&cell_id),
        Some(&stored_before),
        "a refused custom turn must not advance the sovereign commitment"
    );
}

// ===========================================================================
// NON-VACUITY — a composition the ruleset does not license cannot be built.
// ===========================================================================

/// **A composition the ruleset does NOT license has no satisfying witness — so there is no turn
/// to carry.** The forged claim is self-consistent everywhere else; only THE LAW refuses it. (The
/// fast `air_accepts` shadow; `tests/leaf_prove.rs` shows the same against the real STARK.)
#[test]
fn a_composition_the_ruleset_does_not_license_has_no_satisfying_witness() {
    use dregg_param_compose::air::{Forgery, build_forged};

    let entity = deploy_entity(1, 1_000, actor());
    let landed = compose_onto(&entity, &[partner()], ruleset(), shape(), 4).expect("composes");
    let old8 = dregg_entity_compose::door_felt8(&landed.old_commitment);
    let new8 = dregg_entity_compose::door_felt8(&landed.new_commitment);

    let truth = landed.outcome;
    for delta in [1i128, -1, 1000] {
        let forged = build_forged(
            &landed.shape,
            &landed.composition,
            &old8,
            &new8,
            &Forgery {
                claimed_outcome: Some(truth + delta),
                ..Default::default()
            },
        )
        .expect("builds");
        assert!(
            !forged.builder.air_accepts(),
            "an outcome the ruleset does not license (={}, licensed {truth}) must have NO \
             satisfying witness",
            truth + delta
        );
    }
    // Positive pole: the licensed outcome accepts — the refusals are the law discriminating.
    assert!(landed.air_accepts(), "the licensed composition accepts");
}

// ===========================================================================
// THE ENTITY IS REAL — params live in the committed wide plane.
// ===========================================================================

/// **The params ARE the entity's state.** They round-trip through the committed `fields_root`
/// (a read only succeeds when the recomputed root matches), and changing a param moves the v9
/// commitment the Door welds — so the composition's subject is the cell's real content.
#[test]
fn the_entity_params_live_in_the_committed_wide_plane() {
    let entity = deploy_entity(1, 1_000, actor());
    let read = dregg_entity_compose::read_projection(
        &entity.cell,
        PROJECTION_WIDE_BASE,
        actor().params.len(),
    );
    assert_eq!(
        read,
        actor(),
        "the projection round-trips through the committed wide plane"
    );

    // A different param vector -> a different commitment (avalanche through fields_root).
    let other = deploy_entity(
        1,
        1_000,
        Subject {
            identity: 7,
            role: ROLE_ACTOR,
            params: vec![2, 6, 0, 0], // one param changed
        },
    );
    assert_ne!(
        entity.commitment, other.commitment,
        "changing a single param must move the entity's v9 commitment"
    );
}

// ===========================================================================
// THE OUTCOME→CELL-FIELD WELD — shape demonstrated, residual named.
// ===========================================================================

/// **The post state carries the outcome — and the one missing kernel atom is named.** The POST
/// cell's wide plane carries EXACTLY the sub-proof's published `outcome_commitment`, so `new8`
/// (which the Door welds) reflects a state that carries the outcome. The harness check performs
/// the comparison the kernel is missing. See the crate doc: closing it for real is a single
/// executor atom ("new state's wide field == the sub-proof's outcome PI"), which is
/// cell-state-layout-aware and therefore lives at the app layer, not in the game-free AIR.
#[test]
fn the_post_state_carries_the_outcome_and_names_the_residual() {
    let entity = deploy_entity(1, 1_000, actor());
    let landed = compose_onto(&entity, &[partner()], ruleset(), shape(), 4).expect("composes");

    assert!(
        landed.harness_verify_outcome_welded(),
        "the post state must carry the sub-proof's published outcome_commitment (the shape of \
         the outcome->cell-field weld) — and it is the SAME value the sub-proof published"
    );

    // The pre state does NOT carry the outcome (the transition is what installs it).
    assert!(
        entity
            .cell
            .state
            .fields_root_membership(dregg_entity_compose::OUTCOME_WIDE_BASE)
            .is_none(),
        "the pre state must not already carry the outcome"
    );
    // And the post commitment differs from the pre commitment (the outcome moved the state).
    assert_ne!(
        landed.old_commitment, landed.new_commitment,
        "installing the outcome must advance the cell commitment"
    );
}
