//! # dregg-braid-hook — the reusable Braid wiring, game-content-free
//!
//! This crate GRADUATES the Braid ([`dregg_entity_compose`] over [`dregg_param_compose`]) from a
//! disconnected island into the wired substrate. It is the in-tree consumer a game or offering
//! calls to compose a **param-carrying entity** through the Custom-VK Door and land the result as
//! a verifiable turn whose published **outcome** is welded — in-circuit, light-client-visible — to
//! the committed cell field.
//!
//! Everything speaks `subject`/`params`/`role`/`ruleset`/`outcome`; nothing here is a creature, a
//! stat, or a game rule. A HOARDLIGHT world is ONE ruleset root + content over this hook.
//!
//! ## What the hook does
//!
//! * [`compose_entity`] (always available) deploys a sovereign entity whose wide plane carries a
//!   typed param vector and composes those params (plus partners) into a licensed `outcome` under
//!   a versioned ruleset — [`compose_onto`] through the Door. The returned [`LandedComposition`]
//!   already carries the **app-root binding** ([`LandedComposition::app_root_binding`]): the
//!   declaration that the sub-proof's published `outcome_commitment` PI must equal the entity
//!   cell's committed native `fields[0..8]` octet.
//!
//! * [`fold`] (feature `prove`) turns that landed composition into a fold-ready custom turn:
//!   [`fold::braid_custom_bundle`] packages the re-provable composition leaf + the app-root
//!   binding into a `CustomWitnessBundle`, and [`fold::mint_entity_custom_leg`] mints the wide
//!   Custom leg over the entity's real cell. Handed to the deployed chain prover (or folded
//!   directly through `prove_custom_binding_node_app_root_segmented`), a turn whose published
//!   outcome does not match the committed octet has NO satisfying fold — UNSAT, refused.
//!
//! ## The substrate, said out loud
//!
//! The outcome→cell-field weld is **not hand-written Rust AIR and not new Lean AIR**. It is an
//! ADOPTION of the deployed app-root atom (the same in-circuit tie the multiway-tug win-proof
//! ships): a `connect` inside the recursion tree a pure light client folds, whose keystone
//! descends from Lean `CustomBindingFromFold`. This crate only DECLARES the binding and routes
//! the fold through the deployed node — it authors no constraints.

pub use dregg_entity_compose::{
    Comp, DeployedEntity, LandedComposition, Shape, compose_onto, deploy_entity, door_felt8,
};
pub use dregg_param_compose::model::{ComposeError, Knot, LinearTerm, Ruleset, Subject};
pub use dregg_param_compose::shape::ComposeShape;

/// **THE BRAID HOOK.** Deploy a param-carrying entity and compose its params (plus `partners`)
/// into a licensed outcome under `ruleset` at `shape` — the reusable, game-content-free wiring a
/// game/offering calls to put an entity through the Braid. The returned [`LandedComposition`]
/// carries the composition, the committed outcome, the entity's pre/post commitments, and the
/// app-root binding tying the published outcome to the committed cell octet.
///
/// `param_count` is the schema's active param width; params at or past it are canonically zero.
pub fn compose_entity(
    seed: u8,
    balance: i64,
    subject: Subject,
    partners: &[Subject],
    ruleset: Ruleset,
    shape: ComposeShape,
    param_count: usize,
) -> Result<(DeployedEntity, LandedComposition), ComposeError> {
    let entity = deploy_entity(seed, balance, subject);
    let landed = compose_onto(&entity, partners, ruleset, shape, param_count)?;
    Ok((entity, landed))
}

/// The SLOW real-fold wiring (feature `prove`): assemble a fold-ready `CustomWitnessBundle` and
/// mint the wide Custom leg over an entity's real cell, so the composition lands through the
/// deployed app-root fold node.
#[cfg(feature = "prove")]
pub mod fold {
    use dregg_cell::{Cell, Ledger};
    use dregg_circuit::descriptor_ir2::{UMemBoundaryWitness, prove_vm_descriptor2_for_config};
    use dregg_circuit::effect_vm::trace_rotated::{
        RotatedBlockWitness, empty_caveat_manifest,
        generate_rotated_effect_vm_descriptor_and_trace_wide,
    };
    use dregg_circuit::effect_vm::{CellState, Effect, field_limbs8};
    use dregg_circuit::field::BabyBear;
    use dregg_circuit_prove::custom_leaf_adapter::prove_custom_leaf_with_app_root_commitment;
    use dregg_circuit_prove::custom_proof_bind::custom_proof_pi_commitment;
    use dregg_circuit_prove::ivc_turn_chain::{
        CUSTOM_APP_FIELD_OCTET_LEN, CUSTOM_POST_FIELDS_ROOT_LEN, SEG_ANCHOR_WIDTH,
        ir2_leaf_wrap_config, prove_descriptor_leaf_expose_segment_and_claims,
    };
    use dregg_circuit_prove::joint_turn_aggregation::{CustomWitnessBundle, RotatedParticipantLeg};
    use dregg_circuit_prove::joint_turn_recursive::{
        CUSTOM_COMMIT_LEN, CUSTOM_COMMIT_PI_LO, prove_custom_binding_node_app_root_segmented,
    };
    use dregg_entity_compose::LandedComposition;
    use dregg_param_compose::model::ComposeError;
    use dregg_turn::rotation_witness as rw;

    /// Build the fold-ready `CustomWitnessBundle` for a landed composition, bound to a leg's REAL
    /// rotated roots `(old8, new8)`, with the outcome→cell-field **app-root binding** declared.
    /// Handed to the deployed chain prover, this routes the custom turn through
    /// `prove_custom_binding_node_app_root_segmented`, forcing published-outcome == committed-octet.
    pub fn braid_custom_bundle(
        landed: &LandedComposition,
        old8: &[BabyBear; 8],
        new8: &[BabyBear; 8],
        num_rows: usize,
    ) -> Result<CustomWitnessBundle, ComposeError> {
        let (program, witness_values, num_rows, public_inputs) =
            landed.fold_leaf_inputs(old8, new8, num_rows)?;
        Ok(CustomWitnessBundle {
            program,
            witness_values,
            num_rows,
            public_inputs,
            app_root_binding: Some(landed.app_root_binding()),
            descriptor_state_leaf: None,
        })
    }

    fn open_permissions() -> dregg_cell::Permissions {
        use dregg_cell::AuthRequired;
        dregg_cell::Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        }
    }

    fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("pre-iroot limbs")
    }

    /// **Mint the wide Custom leg over a real entity cell.** Routes the AFTER cell's native
    /// `fields[0..8]` octet into the EffectVM state so the leg exposes it (leg PIs `[n-32 .. n-24)`)
    /// — the octet the app-root weld's `field_key` indexes and the `new8` commitment absorbs at
    /// lane-0. A `Custom` effect never mutates fields, so the exposed AFTER octet carries exactly
    /// the committed outcome. `commit` is the published `custom_proof_commitment`; `bundle` is the
    /// retained re-provable sub-proof (with its app-root binding).
    pub fn mint_entity_custom_leg(
        before: &Cell,
        after: &Cell,
        commit: [BabyBear; 8],
        bundle: Option<CustomWitnessBundle>,
    ) -> RotatedParticipantLeg {
        let mut st = CellState::new(after.state.balance() as u64, before.state.nonce() as u32);
        // Route the AFTER cell's real committed lane-0 field octet into the EffectVM state — the
        // SAME lane the v9 commitment absorbs and the wide leg exposes. `CellState::new` stored a
        // commitment over the (default-zero) fields, so refresh it after populating the octet or
        // the trace's committed-state column is stale vs the hash the descriptor recomputes.
        for i in 0..8 {
            st.fields[i] = field_limbs8(after.state.get_field(i).expect("native slot"))[0];
        }
        st.refresh_commitment();

        let effects = vec![Effect::Custom {
            program_vk_hash: [BabyBear::new(9); 8],
            proof_commitment: commit,
        }];

        let mut before_cell = before.clone();
        before_cell.permissions = open_permissions();
        let mut after_cell = after.clone();
        after_cell.permissions = open_permissions();

        let mut ledger = Ledger::new();
        ledger.insert_cell(after_cell.clone()).expect("ledger seed");
        let nullifier_root = dregg_circuit::heap_root::empty_heap_root_8();
        let commitments_root = dregg_circuit::heap_root::empty_heap_root_8();
        let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];
        let before_w = bridge(&rw::produce(
            &before_cell,
            &ledger,
            &nullifier_root,
            &commitments_root,
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        ));
        let after_w = bridge(&rw::produce(
            &after_cell,
            &ledger,
            &nullifier_root,
            &commitments_root,
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        ));

        let (desc, trace, dpis, map_heaps, mb) =
            generate_rotated_effect_vm_descriptor_and_trace_wide(
                &st,
                &effects,
                &before_w,
                &after_w,
                &empty_caveat_manifest(),
                None,
                None,
                None,
                None,
            )
            .expect("custom wide dispatch");
        assert!(
            dpis.len() >= 54,
            "custom leg PI vector must carry the 8-felt commitment slice at 46..53 (got {})",
            dpis.len()
        );
        assert_eq!(
            &dpis[46..54],
            &commit[..],
            "custom leg must publish the claimed 8-felt commitment at PI 46..53"
        );

        let config = ir2_leaf_wrap_config();
        let proof = prove_vm_descriptor2_for_config(
            &desc,
            &trace,
            &dpis,
            &mb,
            &map_heaps,
            &UMemBoundaryWitness::default(),
            &config,
        )
        .expect("custom wide leg proves under the leaf-wrap config");

        let leg = RotatedParticipantLeg {
            proof,
            descriptor: desc,
            public_inputs: dpis,
            carrier_witness: None,
        };
        match bundle {
            Some(b) => leg.with_custom_witness(b),
            None => leg,
        }
    }

    /// The wide 8-felt rotated anchors `(old8, new8)` of a Custom leg over `(before, after)` —
    /// the v9 chip commitments the deployed state weld connects a sub-proof's `[old8 ‖ new8]`
    /// prefix to. Probed with a zero commitment (the anchors come from the rotation witness over
    /// the cells' limbs + iroot, independent of the claimed commitment), so the sub-proof PIs can
    /// be built over them before the real leg is minted.
    pub fn entity_leg_roots(before: &Cell, after: &Cell) -> ([BabyBear; 8], [BabyBear; 8]) {
        let probe = mint_entity_custom_leg(before, after, [BabyBear::ZERO; 8], None);
        (
            probe.wide_old_root8().expect("wide-anchored"),
            probe.wide_new_root8().expect("wide-anchored"),
        )
    }

    /// The honest AFTER cell for a landed composition: its POST cell (carrying the committed
    /// outcome in the native `fields[0..8]` octet) with the Custom effect's nonce bump.
    pub fn honest_after(landed: &LandedComposition) -> Cell {
        let mut after = landed.post_cell.clone();
        let _ = after.state.increment_nonce();
        after
    }

    /// A FORGED after cell whose committed outcome octet DISAGREES with the sub-proof's published
    /// outcome (native slot `lane` perturbed by +1) — the "host wrote outcome X into the cell
    /// while the sub-proof commits outcome Y" the weld exists to catch.
    pub fn forged_after(landed: &LandedComposition, lane: usize) -> Cell {
        let mut after = landed.post_cell.clone();
        let tampered = landed.outcome_commitment[lane] + BabyBear::ONE;
        after
            .state
            .set_field(lane, dregg_entity_compose::outcome_native_fe(tampered));
        let _ = after.state.increment_nonce();
        after
    }

    /// **DRIVE THE OUTCOME→CELL-FIELD WELD, END TO END THROUGH THE DEPLOYED APP-ROOT FOLD NODE.**
    ///
    /// Mints the wide Custom leg over `(before, after)` (exposing the committed `fields[0..8]`
    /// octet), the app-root sub-proof leaf (re-exposing the composition's published outcome), and
    /// folds them through `prove_custom_binding_node_app_root_segmented` — the deployed keystone
    /// tie. Returns `Ok(())` iff the fold produces a root (the published outcome equals the
    /// committed octet, lane-by-lane); returns `Err(reason)` iff any tooth conflicts (an outcome
    /// that does not match the committed field has no satisfying fold — UNSAT, refused). This is
    /// the SAME app-root node the deployed chain prover mints for a bundle carrying an
    /// `app_root_binding`, so the acceptance/refusal is a property of the artifact a pure light
    /// client folds.
    pub fn fold_composition_app_root(
        before: &Cell,
        after: &Cell,
        landed: &LandedComposition,
        num_rows: usize,
    ) -> Result<(), String> {
        let config = ir2_leaf_wrap_config();
        // Two-phase: probe the leg's real rotated roots, build the sub-proof PIs over them, then
        // mint the real leg carrying the sub-proof's genuine commitment.
        let (old8, new8) = entity_leg_roots(before, after);
        let bundle =
            braid_custom_bundle(landed, &old8, &new8, num_rows).map_err(|e| e.to_string())?;
        let commit = custom_proof_pi_commitment(&bundle.public_inputs);
        let leg = mint_entity_custom_leg(before, after, commit, None);

        let n = leg.public_inputs.len();
        let binding = landed.app_root_binding();
        let octet_lo = n
            .checked_sub(
                2 * SEG_ANCHOR_WIDTH + CUSTOM_POST_FIELDS_ROOT_LEN + CUSTOM_APP_FIELD_OCTET_LEN,
            )
            .ok_or_else(|| format!("custom leg publishes {n} PIs — too few for the field octet"))?;
        let field_k_pi_lo = octet_lo + binding.field_key;

        let dual = prove_descriptor_leaf_expose_segment_and_claims(
            &leg.descriptor,
            &leg.proof,
            &leg.public_inputs,
            &config,
            &[
                (CUSTOM_COMMIT_PI_LO, CUSTOM_COMMIT_LEN),
                (field_k_pi_lo, binding.app_root_len),
            ],
        )?;
        let app_leaf = prove_custom_leaf_with_app_root_commitment(
            &bundle.program,
            &bundle.witness_values,
            bundle.num_rows,
            &bundle.public_inputs,
            &binding,
            &config,
        )?;
        prove_custom_binding_node_app_root_segmented(
            &dual,
            &app_leaf,
            &config,
            binding.app_root_len,
        )
        .map(|_| ())
        .map_err(|e| format!("app-root fold refused: {e:?}"))
    }
}
