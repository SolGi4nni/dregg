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
    LandedComposition, PROJECTION_WIDE_BASE, compose_onto, deploy_entity, entity_key,
};
use dregg_param_compose::model::{Knot, LinearTerm, Ruleset, Subject};
use dregg_param_compose::shape::ComposeShape;

// Opaque role tags. Any `u64` is a role; the vocabulary is content.
const ROLE_ACTOR: u64 = 101;
const ROLE_PARTNER: u64 = 202;

/// **The DEPLOYED shape** — `n4 p8 l8 k6` at the default 28-bit identity namespace, which is Lean's
/// `pcRealistic` and the ONE shape the byte-pinned `paramComposeDesc` golden covers. A shape is a
/// BOUND, so this composition's 2 subjects / 4 active params / 1 linear term / 1 knot ride it
/// unchanged; a shape Lean has not pinned is blocked, not faked.
fn shape() -> ComposeShape {
    ComposeShape::new(4, 8, 8, 6)
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
    // The program bytes are the LEAN-EMITTED descriptor's own wire string, so the registry's vk
    // names the Lean-authored AIR rather than a Rust re-authoring of it.
    let program_bytes = landed
        .program_bytes()
        .expect("the deployed shape has a byte-pinned Lean descriptor");
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
    let entity = deploy_entity(entity_key(1), 1_000, actor());
    let landed = compose_onto(&entity, &[partner()], ruleset(), shape(), 4).expect("composes");

    // The composed outcome is exactly what the law licenses: 10*2 + (-2)*5*4 = 20 - 40 = -20.
    assert_eq!(landed.outcome, -20, "the ruleset's licensed outcome");
    assert!(
        landed.lean_descriptor_accepts(),
        "the honest composition's produced witness must satisfy the LEAN-AUTHORED descriptor \
         (the deployed IR-v2 row-local evaluator's verdict, the fast shadow of 'the leaf proves')"
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
    let entity = deploy_entity(entity_key(1), 1_000, actor());
    let (cell_id, mut ledger, _entity) = entity.into_registered_ledger();

    // A DIFFERENT entity — different identity AND params -> a different commitment.
    let stranger = deploy_entity(
        entity_key(2),
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
/// to carry.** The forged claim is RE-COMMITTED honestly (the digest chains and the published PIs
/// bind the lie), so it is self-consistent everywhere else and only THE LAW — a gate of the
/// LEAN-AUTHORED descriptor — can refuse it. (`tests/leaf_prove.rs` shows the same against the
/// real STARK.)
#[test]
fn a_composition_the_ruleset_does_not_license_has_no_satisfying_witness() {
    use dregg_param_compose::field::fb;
    use dregg_param_compose::lean_descriptor::lean_descriptor_for;
    use dregg_param_compose::witness::compose_trace_accepts;

    let entity = deploy_entity(entity_key(1), 1_000, actor());
    let landed = compose_onto(&entity, &[partner()], ruleset(), shape(), 4).expect("composes");
    let desc = lean_descriptor_for(&landed.shape).expect("the deployed shape is Lean-pinned");

    let truth = landed.outcome;
    for delta in [1i128, -1, 1000] {
        let mut forged = landed.witness.clone();
        forged.row[forged.layout.out_col] = fb(truth + delta);
        forged.fill_chains();
        forged.fill_pis();
        assert!(
            !compose_trace_accepts(&desc, &forged),
            "an outcome the ruleset does not license (={}, licensed {truth}) must have NO \
             satisfying witness",
            truth + delta
        );
    }
    // Positive pole: the licensed outcome accepts — the refusals are the law discriminating.
    assert!(
        landed.lean_descriptor_accepts(),
        "the licensed composition accepts"
    );
}

// ===========================================================================
// THE ENTITY IS REAL — params live in the committed wide plane.
// ===========================================================================

/// **The params ARE the entity's state.** They round-trip through the committed `fields_root`
/// (a read only succeeds when the recomputed root matches), and changing a param moves the v9
/// commitment the Door welds — so the composition's subject is the cell's real content.
#[test]
fn the_entity_params_live_in_the_committed_wide_plane() {
    let entity = deploy_entity(entity_key(1), 1_000, actor());
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
        entity_key(1),
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
// THE OUTCOME→CELL-FIELD WELD — closed by adopting the deployed app-root atom.
// ===========================================================================

/// **The post state commits the outcome in the octet the app-root weld reaches, and the binding
/// is declared.** The POST cell's native `fields[0..8]` octet carries (at lane-0) EXACTLY the
/// sub-proof's published `outcome_commitment`, so `new8` commits it AND it is the value the
/// deployed app-root fold ties the published outcome PI to. The `app_root_binding` names where
/// the outcome PI sits and which field octet it must equal. The forged-outcome-refused bite is
/// driven through the real fold in `dregg-braid-hook`'s weld canary (`#[ignore]`, minutes).
#[test]
fn the_post_state_commits_the_outcome_and_declares_the_app_root_weld() {
    use dregg_circuit::effect_vm::custom_state_binding::CUSTOM_PI_STATE_PREFIX_LEN;
    use dregg_circuit::effect_vm::field_limbs9;

    let entity = deploy_entity(entity_key(1), 1_000, actor());
    let landed = compose_onto(&entity, &[partner()], ruleset(), shape(), 4).expect("composes");

    assert!(
        landed.harness_verify_outcome_welded(),
        "the post state's native octet must carry the sub-proof's published outcome_commitment \
         — the value the deployed app-root fold connect enforces"
    );

    // The declared binding: the outcome PI is welded to the native `fields[0..8]` octet.
    let b = landed.app_root_binding();
    assert!(
        b.is_well_formed(),
        "the app-root binding must be well-formed (R past the 16-felt state prefix, nonzero width)"
    );
    assert_eq!(b.app_root_len, 8, "the outcome is an 8-felt octet root");
    assert_eq!(
        b.field_key, 0,
        "the outcome rides the native fields[0..8] octet at slot 0"
    );
    assert!(
        b.app_root_pi_offset >= CUSTOM_PI_STATE_PREFIX_LEN,
        "the outcome PI must sit strictly past the door's state prefix"
    );

    // The PRE state does NOT already carry the outcome (the transition installs it): its native
    // octet lane-0 is all zero.
    for j in 0..8 {
        let fe = entity.cell.state.get_field(j).copied().unwrap_or([0u8; 32]);
        assert_eq!(
            field_limbs9(&fe)[0],
            dregg_circuit::field::BabyBear::ZERO,
            "the pre state must not already carry the outcome (native slot {j})"
        );
    }
    // And the post commitment differs from the pre commitment (the outcome moved the state).
    assert_ne!(
        landed.old_commitment, landed.new_commitment,
        "installing the outcome must advance the cell commitment"
    );
}

// ===========================================================================
// THE ROUTE — the production path invokes the LEAN-AUTHORED AIR.
// ===========================================================================

/// **THE FOLD LEAF IS THE LEAN OBJECT.** The inputs this crate hands the deployed direct-IR2 leaf
/// are the byte-pinned `paramComposeDesc` descriptor itself plus a trace filled by the witness
/// producer — no Rust `CellProgram` is lowered, so the relation has exactly one semantics. The
/// producer's PIs are the SAME vector `compose_onto` packaged, so the proven trace and the
/// published sub-proof cannot disagree.
#[test]
fn the_fold_leaf_inputs_carry_the_lean_authored_descriptor() {
    let entity = deploy_entity(entity_key(1), 1_000, actor());
    let landed = compose_onto(&entity, &[partner()], ruleset(), shape(), 4).expect("composes");

    // The leg's real rotated anchors differ from the crate's own v9 context; the producer re-fills
    // the door prefix over them, and the published outcome is UNCHANGED (it is a function of the
    // composition alone).
    let leg_old8: [dregg_circuit::field::BabyBear; 8] =
        core::array::from_fn(|i| dregg_circuit::field::BabyBear::new(7_000 + i as u32));
    let leg_new8: [dregg_circuit::field::BabyBear; 8] =
        core::array::from_fn(|i| dregg_circuit::field::BabyBear::new(8_000 + i as u32));
    let (desc, base_trace, pis) = landed
        .direct_ir2_leaf_inputs(&leg_old8, &leg_new8, 2)
        .expect("the deployed shape resolves the Lean descriptor and the witness satisfies it");

    assert_eq!(
        desc.name, "dregg-param-compose-v1-n4p8l8k6i28::poseidon2-node8",
        "the leaf must prove the LEAN-emitted descriptor"
    );
    assert_eq!(base_trace.len(), 2);
    assert!(base_trace.iter().all(|r| r.len() == desc.trace_width));
    assert_eq!(pis.len(), desc.public_input_count);
    assert_eq!(
        &pis[..8],
        &leg_old8[..],
        "the door prefix rides the leg's roots"
    );
    assert_eq!(&pis[8..16], &leg_new8[..]);

    // The published outcome PI is the composition's, unchanged by the anchors — and it is the
    // octet the app-root binding welds to the committed cell field.
    let base = dregg_param_compose::pi::outcome_commitment_base();
    assert_eq!(
        &pis[base..base + 8],
        &landed.outcome_commitment[..],
        "the published outcome is a function of the composition alone"
    );

    // And the PIs `compose_onto` packaged are the SAME producer's, over the crate's own anchors.
    assert_eq!(
        &landed.pis[base..base + 8],
        &landed.outcome_commitment[..],
        "one PI source: the producer's"
    );
}

/// **BLOCKED, NOT FAKED.** A shape Lean has NOT byte-pinned has no reachable AIR: there is no
/// Rust-authored fallback to degrade to, so the route refuses by name rather than attesting
/// something no emitted object defines.
#[test]
fn an_unpinned_shape_is_refused_rather_than_faked() {
    use dregg_param_compose::model::ComposeError;

    // `n3 p4 l3 k2` used to be the witness of unpinnedness; it is now BYTE-PINNED
    // (`ParamComposeGoldenShapes.pcLeaf`, 346 columns), so it no longer drives this path. The
    // bounds are held fixed and only the identity namespace is moved off a pinned width — 27 is
    // SOUND (`1 <= 27 <= 28`), so the refusal here is genuinely "Lean pinned no wire at this
    // shape", not the shape guard firing for some other reason.
    let unpinned = ComposeShape::new(3, 4, 3, 2).with_identity_bits(27);
    let entity = deploy_entity(entity_key(1), 1_000, actor());
    let landed = compose_onto(&entity, &[partner()], ruleset(), unpinned, 4).expect("composes");
    assert!(
        !landed.lean_descriptor_accepts(),
        "an unpinned shape must not claim acceptance"
    );
    assert!(landed.program_bytes().is_none());
    let z = [dregg_circuit::field::BabyBear::ZERO; 8];
    assert!(matches!(
        landed.direct_ir2_leaf_inputs(&z, &z, 2),
        Err(ComposeError::NoLeanDescriptor)
    ));
}
