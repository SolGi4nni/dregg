//! `rotation_witness` — the per-turn ROTATION **producers** (Group A of the
//! turn-prover extraction).
//!
//! These are the minting recipes that take a REAL executed turn's before/after
//! `dregg_cell::Cell`s, drive [`dregg_turn::rotation_witness::produce`] over them
//! to derive each rotated block witness (`pre_limbs` + `iroot`), run the wide
//! full-cohort trace dispatcher, and PROVE the result — returning a
//! `dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg` (or, for
//! the wrap adapter, an `ivc_turn_chain::FinalizedTurn`).
//!
//! # Why they live here and not in `dregg-turn`
//!
//! Everything below calls into `dregg-circuit-prove` (the recursion substrate).
//! Core `dregg-turn` is the wasm/zkvm card and the seL4 verifier-PD floor: it
//! keeps the *derivation* (`produce`, `cells_root`, `iroot`, `wire_commit_8`,
//! `sender_membership_teeth`) and the executor's rotated VERIFY leg, and links no
//! prove crate at all. The producers ride `dregg-turn`'s PUBLIC interface only —
//! `rotation_witness::{produce, RotationWitness, empty_revoked_root_8,
//! sender_membership_teeth}` plus the `umem` projection module — so this move
//! exposed no new internals.
//!
//! Until PR3 these were `#[cfg(feature = "prover")]` inside `dregg-turn`, i.e.
//! type-checked only in whichever build happened to select the arm. Here they are
//! compiled unconditionally, so a shape change in `dregg-circuit-prove`'s leg
//! constructors is a compile error at the source.

use dregg_cell::{Cell, Ledger};
use dregg_circuit::field::BabyBear;
use dregg_turn::rotation_witness::{
    RotationWitness, empty_revoked_root_8, produce, sender_membership_teeth,
};

/// **THE ROTATED-LEG MINTING RECIPE (Bucket-F / PATH-PRESERVE Phase 5a).** Build a
/// [`RotatedParticipantLeg`](dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg) for a
/// single homogeneous-cohort turn from the real before/after actor `Cell`s: run [`produce`] over
/// each cell to derive its rotated block witness (`pre_limbs` + `iroot`), then drive the wide
/// full-cohort dispatcher (`generate_rotated_effect_vm_descriptor_and_trace_wide`) over them —
/// threading the BEFORE cell's producer-honest membership teeth — and prove the result through
/// the IR-v2 batch prover under the leaf-wrap config (so the minted `Ir2BatchProof` folds
/// directly as a `NativeBatchStark` recursion leaf). The proof self-verifies natively before
/// return. (An earlier `RotatedParticipantLeg::mint_from_block_witnesses` "pure-circuit core"
/// duplicated this body WITHOUT the membership-teeth threading and had zero callers — a drifted
/// mirror, deleted 2026-07-17; this recipe is the one real mint.)
///
/// This lives in `dregg-turn` (NOT `dregg-circuit`) because it drives [`produce`] over
/// `dregg_cell::Cell`s, and `dregg-circuit` cannot depend on `dregg-cell` / `dregg-turn` (a
/// dependency cycle — both depend on `dregg-circuit`). It is the ONE recipe the recursion
/// consumers (lightclient / wasm / `circuit/tests/proof_economics.rs`) use to build a mandatory
/// rotated participant; it mirrors `circuit/tests/rotation_batchstark_leaf_smoke.rs`'s mint
/// sequence exactly.
///
/// `turn_id`, when `Some`, overrides the `TURN_HASH` slot of the carried PI prefix (the joint
/// aggregator's shared-turn-id projection) — pass it for joint-turn participants that must agree
/// on a shared id; pass `None` for whole-chain turns (the carried hash from the witness stands).
///
/// ## The post-regen registry TAIL (v12 exposure regen)
///
/// The committed wide registry row a member proves against may demand MORE PIs (and trace
/// columns) than the per-family wide producer emits: the v12 big-bang regen made the committed
/// transfer row the membership-teeth member (`CarrierComposed.transferV3MembershipWide` — 2
/// `(sender_leaf, authorized_root)` claim PIs spliced AHEAD of the 16 wide anchors, 2 teeth
/// columns past the carriers). The tail derivation is SHARED: it lives IN the wide dispatcher
/// (`generate_rotated_effect_vm_descriptor_and_trace_wide` — derived from the descriptor, never
/// a hardcoded count, fail-closed on a tail it has no producer fill for), so every route emits
/// the committed shape. This recipe's contribution is the producer-honest teeth VALUES from the
/// BEFORE cell (`sender_membership_teeth` — `compress_member` over the cell's owner key + the
/// declared `SenderAuthorized { PublicRoot }` root slot; a cell declaring no such caveat passes
/// the ZERO form, exactly the no-caveat sentinel the fold's membership arm refuses to bind).
///
/// Fails closed if the turn's effect is not a single rotated R=24 cohort member (the generator
/// rejects a non-cohort / empty / heterogeneous slice).
#[allow(clippy::too_many_arguments)]
pub fn mint_rotated_participant_leg(
    initial_state: &dregg_circuit::effect_vm::CellState,
    effects: &[dregg_circuit::effect_vm::Effect],
    before_cell: &Cell,
    after_cell: &Cell,
    nullifier_root: &dregg_circuit::Faithful8,
    commitments_root: &dregg_circuit::Faithful8,
    receipt_log: &[[u8; 32]],
    turn_id: Option<BabyBear>,
) -> Result<dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg, String> {
    use dregg_circuit::descriptor_ir2::{
        UMemBoundaryWitness, prove_vm_descriptor2_for_config, verify_vm_descriptor2_with_config,
    };
    use dregg_circuit::effect_vm::pi;
    use dregg_circuit::effect_vm::trace_rotated::{
        RotatedBlockWitness, empty_caveat_manifest,
        generate_rotated_effect_vm_descriptor_and_trace_wide, transfer_caveat_manifest,
    };
    use dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config;
    use dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg;

    // The turn-context ledger snapshot: a single-cell ledger holding the after-cell (the
    // cells_root shape `produce` reads).
    let mut ledger = Ledger::new();
    ledger
        .insert_cell(after_cell.clone())
        .map_err(|e| format!("mint_rotated_participant_leg: ledger seed failed: {e:?}"))?;

    let before_w = produce(
        before_cell,
        &ledger,
        nullifier_root,
        commitments_root,
        // REVOKED-ROOT: these proving-recipe wrappers commit the EMPTY revocation accumulator
        // (no live revoked root flows through a mint recipe today); stage E/G threads a live root
        // by promoting this to a wrapper param when a revoke-carrying turn needs it.
        &empty_revoked_root_8(),
        receipt_log,
        // recipe path: no effective_vk / contract_hash in hand (the faithful capture is at the
        // executor's `effective_vk` / hatchery site) — ZERO carrier material.
        &dregg_cell::commitment::RotationCarrierMaterial::default(),
    );
    let after_w = produce(
        after_cell,
        &ledger,
        nullifier_root,
        commitments_root,
        // REVOKED-ROOT: these proving-recipe wrappers commit the EMPTY revocation accumulator
        // (no live revoked root flows through a mint recipe today); stage E/G threads a live root
        // by promoting this to a wrapper param when a revoke-carrying turn needs it.
        &empty_revoked_root_8(),
        receipt_log,
        // recipe path: no effective_vk / contract_hash in hand (the faithful capture is at the
        // executor's `effective_vk` / hatchery site) — ZERO carrier material.
        &dregg_cell::commitment::RotationCarrierMaterial::default(),
    );
    let bridge = |w: &RotationWitness| -> Result<RotatedBlockWitness, String> {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot)
            .map_err(|e| format!("mint_rotated_participant_leg: rotated block witness: {e}"))
    };

    if effects.is_empty() {
        return Err("mint_rotated_participant_leg: empty effect slice".to_string());
    }
    let caveat = match effects {
        [dregg_circuit::effect_vm::Effect::Transfer { .. }] => transfer_caveat_manifest(),
        _ => empty_caveat_manifest(),
    };
    // The SAME full-cohort wide dispatch the live SDK wide prover runs. The value/field/create
    // cohort rides the bare wide producer with NO special witnesses (`None` for the note-spend
    // grow-gate nullifiers / refusal fields / cap-write tree) — an effect that needs one routes
    // through its dedicated minter and fails closed here. The dispatcher owns the post-regen
    // registry TAIL (derived from the committed descriptor, fail-closed on an unknown member);
    // this recipe threads the producer-honest membership-teeth pair from the BEFORE cell.
    let (desc, trace, mut dpis, map_heaps, mem_boundary) =
        generate_rotated_effect_vm_descriptor_and_trace_wide(
            initial_state,
            effects,
            &bridge(&before_w)?,
            &bridge(&after_w)?,
            &caveat,
            None,
            None,
            None,
            Some(sender_membership_teeth(before_cell)),
        )
        .map_err(|e| format!("mint_rotated_participant_leg: wide producer dispatch failed: {e}"))?;
    debug_assert_eq!(dpis.len(), desc.public_input_count);

    // Optional shared-turn-id override (joint participants). The EffectVm AIRs do not constrain
    // TURN_HASH (it is an executor-trusted shared PI), so overriding the carried prefix slot and
    // proving against the edited PI yields a still-valid proof binding the chosen id.
    if let Some(tid) = turn_id {
        dpis[pi::TURN_HASH_BASE] = tid;
    }

    let wrap_config = ir2_leaf_wrap_config();
    let umem_boundary = UMemBoundaryWitness::default();
    let proof = prove_vm_descriptor2_for_config(
        &desc,
        &trace,
        &dpis,
        &mem_boundary,
        &map_heaps,
        &umem_boundary,
        &wrap_config,
    )
    .map_err(|e| format!("mint_rotated_participant_leg: wide IR-v2 batch prove failed: {e}"))?;
    verify_vm_descriptor2_with_config(&desc, &proof, &dpis, &wrap_config).map_err(|e| {
        format!("mint_rotated_participant_leg: minted wide proof self-verify failed: {e}")
    })?;

    Ok(RotatedParticipantLeg {
        proof,
        descriptor: desc,
        public_inputs: dpis,
        carrier_witness: None,
    })
}

/// **THE FULL-TURN → WRAP ADAPTER** — convert a REAL finalized node turn into the wrap's IVC
/// input [`FinalizedTurn`], BOUND to the node's served [`dregg_sdk::FullTurnProof`]'s proven
/// transition.
///
/// ## Why this is a re-prove, not a byte-reuse
///
/// The node's `FullTurnProof` (`node::turn_proving`) is a COMPOSED multi-sub-proof STARK proven
/// under the SDK verify config; its rotated effect-vm leg lives inside a
/// `dregg_dsl_runtime::ComposedProof` and is FRI-instantiated for `verify_full_turn`, NOT for the
/// recursion fold. The wrap folds a bare `Ir2BatchProof<DreggRecursionConfig>` minted under
/// [`ir2_leaf_wrap_config`](dregg_circuit_prove::ivc_turn_chain::ir2_leaf_wrap_config)
/// (log_blowup 6). The two are DIFFERENT FRI-engine instantiations of the SAME constraint set, so
/// the composed leg's bytes cannot be dropped into the fold. The SOUND bridge (the same
/// statement-equality argument [`dregg_turn::rotation_witness`]'s leaf wrap already rests on) re-proves
/// the IDENTICAL rotated descriptor over the IDENTICAL trace + PI vector under the leaf-wrap
/// config, from the SAME execution context the node marshalled for its `FullTurnProof`.
///
/// ## The faithfulness tie (fail-closed)
///
/// A re-prove is only a faithful bridge if it attests the SAME state transition the served
/// `FullTurnProof` proved. The node's `ProvenFinalizedTurn` carries the proof's 8-felt (~124-bit)
/// `(old_commit, new_commit)` anchors (`node::turn_proving::prove_and_verify_finalized_turn` reads
/// them off the rotated leg's `wide_commit_anchors`). This adapter takes those anchors and REFUSES
/// unless the freshly minted wrap leg publishes the SAME wide 8-felt anchors at its PI tail
/// (`wide_old_root8` / `wide_new_root8`). So the `FinalizedTurn` this returns cannot silently
/// attest a DIFFERENT transition than the node's served proof — a context that does not match the
/// `FullTurnProof` fails closed here rather than folding a mismatched turn into the wrap. The
/// chain's temporal tooth (`new_root[i] == old_root[i+1]`) then binds these SAME anchors across the
/// fold.
///
/// `initial_state` / `effects` / `before_cell` / `after_cell` / `nullifier_root` /
/// `commitments_root` / `receipt_log` / `turn_id` are exactly the arguments
/// [`mint_rotated_participant_leg`] consumes (the turn's execution context the node holds at
/// `blocklace_sync::execute_finalized_turn`). `proven_old_commit` / `proven_new_commit` are the
/// served `FullTurnProof`'s proven wide anchors (`ProvenFinalizedTurn::{old_commit, new_commit}`).
#[allow(clippy::too_many_arguments)]
pub fn finalized_turn_from_full_turn(
    initial_state: &dregg_circuit::effect_vm::CellState,
    effects: &[dregg_circuit::effect_vm::Effect],
    before_cell: &Cell,
    after_cell: &Cell,
    nullifier_root: &dregg_circuit::Faithful8,
    commitments_root: &dregg_circuit::Faithful8,
    receipt_log: &[[u8; 32]],
    turn_id: Option<BabyBear>,
    proven_old_commit: [BabyBear; 8],
    proven_new_commit: [BabyBear; 8],
) -> Result<dregg_circuit_prove::ivc_turn_chain::FinalizedTurn, String> {
    use dregg_circuit_prove::ivc_turn_chain::FinalizedTurn;
    use dregg_circuit_prove::joint_turn_aggregation::DescriptorParticipant;

    // 1. Re-prove the rotated leg under the leaf-wrap config (statement-equality: same descriptor,
    //    same trace, same PI vector as the FullTurnProof's rotated leg). `mint_rotated_participant_leg`
    //    already self-verifies the minted proof before returning.
    let leg = mint_rotated_participant_leg(
        initial_state,
        effects,
        before_cell,
        after_cell,
        nullifier_root,
        commitments_root,
        receipt_log,
        turn_id,
    )?;

    // 2. THE FAITHFULNESS TIE (fail-closed): the wrap leg's wide 8-felt anchors must be the SAME
    //    (~124-bit) commits the node's FullTurnProof proved, else the context does not match the
    //    served proof and we refuse to fold a mismatched transition into the wrap.
    let wide_old = leg.wide_old_root8().ok_or_else(|| {
        "finalized_turn_from_full_turn: minted leg carries no wide 8-felt OLD anchor (a narrow \
         leg cannot be bound to the FullTurnProof's ~124-bit commit)"
            .to_string()
    })?;
    let wide_new = leg.wide_new_root8().ok_or_else(|| {
        "finalized_turn_from_full_turn: minted leg carries no wide 8-felt NEW anchor".to_string()
    })?;
    if wide_old != proven_old_commit {
        return Err(format!(
            "finalized_turn_from_full_turn: minted wrap-leg OLD anchor {wide_old:?} != the \
             FullTurnProof's proven old_commit {proven_old_commit:?} — the turn context does not \
             match the served proof (refused, not folded)"
        ));
    }
    if wide_new != proven_new_commit {
        return Err(format!(
            "finalized_turn_from_full_turn: minted wrap-leg NEW anchor {wide_new:?} != the \
             FullTurnProof's proven new_commit {proven_new_commit:?} — the turn context does not \
             match the served proof (refused, not folded)"
        ));
    }

    Ok(FinalizedTurn::new(DescriptorParticipant::rotated(leg)))
}

/// **THE CUSTOM-WIDE LEG MINTING RECIPE — the production custom-binding fold plug.** Build a
/// [`RotatedParticipantLeg`](dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg) for
/// an [`Effect::Custom`](dregg_circuit::effect_vm::Effect::Custom) turn from the real before/after
/// actor `Cell`s, routing through the WIDE custom mint
/// ([`RotatedParticipantLeg::mint_custom_wide_from_block_witnesses`](dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg::mint_custom_wide_from_block_witnesses))
/// — the `customVmDescriptor2R24` leg that publishes the claimed `custom_proof_commitment` at PI
/// 46..53 (the 8-felt flag-day exposure) — and ATTACHING the prover-side re-provable [`CustomWitnessBundle`](dregg_circuit_prove::joint_turn_aggregation::CustomWitnessBundle).
///
/// This is the path that makes the custom binding REAL-FOLDED in production: the chain prover folds
/// the attached witness's sub-proof leaf into the recursion tree a PURE LIGHT CLIENT verifies, so a
/// forged `custom_proof_commitment` (one no verifying sub-proof of the bundle's PIs backs) is UNSAT
/// — rejected without any off-AIR re-execution. Build `bundle` via
/// [`CustomWitnessBundle::from_bound_custom_proof`](dregg_circuit_prove::joint_turn_aggregation::CustomWitnessBundle::from_bound_custom_proof)
/// over the SAME `BoundCustomProof` whose `proof_commitment()` was threaded into the
/// `Effect::Custom`'s `proof_commitment` field at turn-build.
///
/// Fails closed if the lead effect is not `Effect::Custom`, or if the bound proof carried no
/// retained witness (a wire-reconstructed proof — `from_bound_custom_proof` returns `None`).
#[allow(clippy::too_many_arguments)]
pub fn mint_custom_wide_rotated_participant_leg(
    initial_state: &dregg_circuit::effect_vm::CellState,
    effects: &[dregg_circuit::effect_vm::Effect],
    before_cell: &Cell,
    after_cell: &Cell,
    nullifier_root: &dregg_circuit::Faithful8,
    commitments_root: &dregg_circuit::Faithful8,
    receipt_log: &[[u8; 32]],
    turn_id: Option<BabyBear>,
    bundle: dregg_circuit_prove::joint_turn_aggregation::CustomWitnessBundle,
) -> Result<dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg, String> {
    use dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness;
    use dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg;

    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).map_err(|e| {
        format!("mint_custom_wide_rotated_participant_leg: ledger seed failed: {e:?}")
    })?;

    let before_w = produce(
        before_cell,
        &ledger,
        nullifier_root,
        commitments_root,
        // REVOKED-ROOT: these proving-recipe wrappers commit the EMPTY revocation accumulator
        // (no live revoked root flows through a mint recipe today); stage E/G threads a live root
        // by promoting this to a wrapper param when a revoke-carrying turn needs it.
        &empty_revoked_root_8(),
        receipt_log,
        // recipe path: no effective_vk / contract_hash in hand (the faithful capture is at the
        // executor's `effective_vk` / hatchery site) — ZERO carrier material.
        &dregg_cell::commitment::RotationCarrierMaterial::default(),
    );
    let after_w = produce(
        after_cell,
        &ledger,
        nullifier_root,
        commitments_root,
        // REVOKED-ROOT: these proving-recipe wrappers commit the EMPTY revocation accumulator
        // (no live revoked root flows through a mint recipe today); stage E/G threads a live root
        // by promoting this to a wrapper param when a revoke-carrying turn needs it.
        &empty_revoked_root_8(),
        receipt_log,
        // recipe path: no effective_vk / contract_hash in hand (the faithful capture is at the
        // executor's `effective_vk` / hatchery site) — ZERO carrier material.
        &dregg_cell::commitment::RotationCarrierMaterial::default(),
    );
    let bridge = |w: &RotationWitness| -> Result<RotatedBlockWitness, String> {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).map_err(|e| {
            format!("mint_custom_wide_rotated_participant_leg: rotated block witness: {e}")
        })
    };

    RotatedParticipantLeg::mint_custom_wide_from_block_witnesses(
        initial_state,
        effects,
        &bridge(&before_w)?,
        &bridge(&after_w)?,
        turn_id,
        bundle,
    )
}

/// **THE WELDED ROTATED+UMEM LEG MINTING RECIPE (STAGED, VK-RISK-FREE) — the IVC half of the
/// flag-day weld.** Like [`mint_rotated_participant_leg`], but the minted leg carries the WELDED
/// rotated+umem descriptor: it derives the SAME turn's universal-memory touch (the pre→post
/// projection diff, the single-domain cohort rows + REAL boundary via
/// [`dregg_turn::umem::umem_cohort_proving_inputs_from`]) and hands it to
/// [`RotatedParticipantLeg::mint_welded_from_block_witnesses`](dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg::mint_welded_from_block_witnesses),
/// which welds the umem leg INTO the rotated descriptor and proves both in ONE leaf under the
/// leaf-wrap config. The leg's 46-PI vector (the rotated commit pins) is intact, so the IVC chain
/// fold's `old_root`/`new_root` accessors keep working over the welded leg.
///
/// `before_cell`/`after_cell` are the real actor cells (their projection diff IS the umem touch).
/// Fails closed if the turn is not a single rotated R=24 cohort member, or if its umem touch is
/// multi-domain (such effects stay on the per-map path until their own cohort design).
#[allow(clippy::too_many_arguments)]
pub fn mint_welded_umem_rotated_participant_leg(
    initial_state: &dregg_circuit::effect_vm::CellState,
    effects: &[dregg_circuit::effect_vm::Effect],
    before_cell: &Cell,
    after_cell: &Cell,
    nullifier_root: &dregg_circuit::Faithful8,
    commitments_root: &dregg_circuit::Faithful8,
    receipt_log: &[[u8; 32]],
    turn_id: Option<BabyBear>,
) -> Result<dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg, String> {
    use dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness;
    use dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg;
    use dregg_turn::umem::{
        project_diff_ops, project_record_kernel_state, umem_cohort_proving_inputs_from,
    };

    let mut ledger = Ledger::new();
    ledger
        .insert_cell(after_cell.clone())
        .map_err(|e| format!("mint_welded_umem: ledger seed failed: {e:?}"))?;

    let before_w = produce(
        before_cell,
        &ledger,
        nullifier_root,
        commitments_root,
        // REVOKED-ROOT: these proving-recipe wrappers commit the EMPTY revocation accumulator
        // (no live revoked root flows through a mint recipe today); stage E/G threads a live root
        // by promoting this to a wrapper param when a revoke-carrying turn needs it.
        &empty_revoked_root_8(),
        receipt_log,
        // recipe path: no effective_vk / contract_hash in hand (the faithful capture is at the
        // executor's `effective_vk` / hatchery site) — ZERO carrier material.
        &dregg_cell::commitment::RotationCarrierMaterial::default(),
    );
    let after_w = produce(
        after_cell,
        &ledger,
        nullifier_root,
        commitments_root,
        // REVOKED-ROOT: these proving-recipe wrappers commit the EMPTY revocation accumulator
        // (no live revoked root flows through a mint recipe today); stage E/G threads a live root
        // by promoting this to a wrapper param when a revoke-carrying turn needs it.
        &empty_revoked_root_8(),
        receipt_log,
        // recipe path: no effective_vk / contract_hash in hand (the faithful capture is at the
        // executor's `effective_vk` / hatchery site) — ZERO carrier material.
        &dregg_cell::commitment::RotationCarrierMaterial::default(),
    );
    let bridge = |w: &RotationWitness| -> Result<RotatedBlockWitness, String> {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot)
            .map(|bw| bw.with_asset_class(w.asset_class))
            .map_err(|e| format!("mint_welded_umem: rotated block witness: {e}"))
    };

    // The SAME transition's universal-memory touch: the pre→post projection diff as a Blum write
    // trace, bridged into the single-domain cohort rows + REAL boundary.
    let proj_pre = project_record_kernel_state(before_cell);
    let proj_post = project_record_kernel_state(after_cell);
    let ops = project_diff_ops(&proj_pre, &proj_post);
    let inputs = umem_cohort_proving_inputs_from(&proj_pre, &ops)
        .map_err(|e| format!("mint_welded_umem: umem cohort inputs: {e}"))?;

    RotatedParticipantLeg::mint_welded_from_block_witnesses(
        initial_state,
        effects,
        &bridge(&before_w)?,
        &bridge(&after_w)?,
        turn_id,
        &inputs.rows,
        &inputs.boundary,
        inputs.domain,
    )
}

/// **THE WIDE WELDED ROTATED+UMEM LEG MINTING RECIPE (STAGED, VK-RISK-FREE) — the IVC half of the
/// genuine flip precursor.** The WIDE (8-felt / ~124-bit) twin of
/// [`mint_welded_umem_rotated_participant_leg`]: it derives the SAME turn's universal-memory touch
/// (the pre→post projection diff, the single-domain cohort rows + REAL boundary) and hands it to
/// [`RotatedParticipantLeg::mint_welded_wide_from_block_witnesses`](dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg::mint_welded_wide_from_block_witnesses),
/// which welds the umem leg INTO the WIDE descriptor and proves both in ONE leaf under the leaf-wrap
/// config. The leg's wide PI vector is intact (the 16 wide commit PIs ride through the additive
/// weld), so the IVC chain fold's `old_root`/`new_root` accessors keep working over the welded leg
/// AND the 8-felt anchors are preserved for the ~124-bit binding.
///
/// SCOPE: the FULL single-domain wide cohort — any effect whose WIDE producer is SAT on the bare wide
/// sovereign path (the value/field families: transfer / burn / bridgeMint / setField / setFieldDyn,
/// heap domain), routed through the shared
/// [`RotatedParticipantLeg::mint_welded_wide_from_block_witnesses`](dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg::mint_welded_wide_from_block_witnesses)
/// dispatch. The cap-WRITE family (grant/attenuate/revoke — AFTER cap-root is an in-circuit cap-tree
/// MAP-OP write) needs the SEPARATE cap-open path and is a named tail; the multi-domain note/bridge
/// economic verbs stay on the multi-domain cohort path (not yet welded/folded — a named tail on the
/// narrow path too). `before_cell`/`after_cell` are the real actor cells (their projection diff IS the
/// umem touch); a multi-domain touch fails closed at `umem_cohort_proving_inputs_from`.
#[allow(clippy::too_many_arguments)]
pub fn mint_welded_wide_umem_rotated_participant_leg(
    initial_state: &dregg_circuit::effect_vm::CellState,
    effects: &[dregg_circuit::effect_vm::Effect],
    before_cell: &Cell,
    after_cell: &Cell,
    nullifier_root: &dregg_circuit::Faithful8,
    commitments_root: &dregg_circuit::Faithful8,
    receipt_log: &[[u8; 32]],
    turn_id: Option<BabyBear>,
) -> Result<dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg, String> {
    use dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness;
    use dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg;
    use dregg_turn::umem::{
        project_diff_ops, project_record_kernel_state, umem_cohort_proving_inputs_from,
    };

    let mut ledger = Ledger::new();
    ledger
        .insert_cell(after_cell.clone())
        .map_err(|e| format!("mint_welded_wide_umem: ledger seed failed: {e:?}"))?;

    let before_w = produce(
        before_cell,
        &ledger,
        nullifier_root,
        commitments_root,
        // REVOKED-ROOT: these proving-recipe wrappers commit the EMPTY revocation accumulator
        // (no live revoked root flows through a mint recipe today); stage E/G threads a live root
        // by promoting this to a wrapper param when a revoke-carrying turn needs it.
        &empty_revoked_root_8(),
        receipt_log,
        // recipe path: no effective_vk / contract_hash in hand (the faithful capture is at the
        // executor's `effective_vk` / hatchery site) — ZERO carrier material.
        &dregg_cell::commitment::RotationCarrierMaterial::default(),
    );
    let after_w = produce(
        after_cell,
        &ledger,
        nullifier_root,
        commitments_root,
        // REVOKED-ROOT: these proving-recipe wrappers commit the EMPTY revocation accumulator
        // (no live revoked root flows through a mint recipe today); stage E/G threads a live root
        // by promoting this to a wrapper param when a revoke-carrying turn needs it.
        &empty_revoked_root_8(),
        receipt_log,
        // recipe path: no effective_vk / contract_hash in hand (the faithful capture is at the
        // executor's `effective_vk` / hatchery site) — ZERO carrier material.
        &dregg_cell::commitment::RotationCarrierMaterial::default(),
    );
    let bridge = |w: &RotationWitness| -> Result<RotatedBlockWitness, String> {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot)
            .map(|bw| bw.with_asset_class(w.asset_class))
            .map_err(|e| format!("mint_welded_wide_umem: rotated block witness: {e}"))
    };

    let proj_pre = project_record_kernel_state(before_cell);
    let proj_post = project_record_kernel_state(after_cell);
    let ops = project_diff_ops(&proj_pre, &proj_post);
    let inputs = umem_cohort_proving_inputs_from(&proj_pre, &ops)
        .map_err(|e| format!("mint_welded_wide_umem: umem cohort inputs: {e}"))?;

    RotatedParticipantLeg::mint_welded_wide_from_block_witnesses(
        initial_state,
        effects,
        &bridge(&before_w)?,
        &bridge(&after_w)?,
        turn_id,
        &inputs.rows,
        &inputs.boundary,
        inputs.domain,
        // The value/field cohort needs no grow-gate / refusal context (heap-domain balance/field
        // moves). A note/refusal lead would thread these — but those leads are named tails here.
        None,
        None,
        // No cap-tree write witness — a cap-WRITE lead routes through the dedicated cap-write entry
        // (`mint_welded_wide_umem_cap_write_rotated_participant_leg`); reaching here it fails closed.
        None,
    )
}

/// **THE CAP-WRITE WIDE+umem WELDED LEG (STAGED, VK-RISK-FREE).** The cap-open weld twin of
/// [`mint_welded_wide_umem_rotated_participant_leg`] for the nonce-FREEZE cap-WRITE family — the
/// `grant` / `attenuate` / `revoke(Capability)` bases whose AFTER cap-root is an in-circuit cap-tree
/// `map_op` write (attenuate / revokeCapability) or a frozen authority-only pass-through (grantCap).
/// It threads the cap-tree write witness ([`CapWriteWideWitness`](dregg_circuit::effect_vm::trace_rotated::CapWriteWideWitness)
/// — the cell's c-list + the consumed anchor key + the op payload) through the SAME shared full-cohort
/// wide producer dispatch the value cohort rides, then welds the umem leg onto the WIDE descriptor —
/// purely additive, so the 8-felt (~124-bit) anchors ride through INTACT (no narrowing). A cap-WRITE
/// lead whose base carries a map_op but is given no witness — or any non-cap-WRITE lead — fails closed
/// at the dispatcher (the cap-open weld never fabricates a post-cap-root). STAGED: a welded WIDE
/// descriptor BESIDE the deployed wide registry; no VK bump, nothing on the wire.
#[allow(clippy::too_many_arguments)]
pub fn mint_welded_wide_umem_cap_write_rotated_participant_leg(
    initial_state: &dregg_circuit::effect_vm::CellState,
    effects: &[dregg_circuit::effect_vm::Effect],
    before_cell: &Cell,
    after_cell: &Cell,
    nullifier_root: &dregg_circuit::Faithful8,
    commitments_root: &dregg_circuit::Faithful8,
    receipt_log: &[[u8; 32]],
    turn_id: Option<BabyBear>,
    cap_write: &dregg_circuit::effect_vm::trace_rotated::CapWriteWideWitness,
) -> Result<dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg, String> {
    use dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness;
    use dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg;
    use dregg_turn::umem::{
        project_diff_ops, project_record_kernel_state, umem_cohort_proving_inputs_from,
    };

    let mut ledger = Ledger::new();
    ledger
        .insert_cell(after_cell.clone())
        .map_err(|e| format!("mint_welded_wide_umem_cap_write: ledger seed failed: {e:?}"))?;

    let before_w = produce(
        before_cell,
        &ledger,
        nullifier_root,
        commitments_root,
        // REVOKED-ROOT: these proving-recipe wrappers commit the EMPTY revocation accumulator
        // (no live revoked root flows through a mint recipe today); stage E/G threads a live root
        // by promoting this to a wrapper param when a revoke-carrying turn needs it.
        &empty_revoked_root_8(),
        receipt_log,
        // recipe path: no effective_vk / contract_hash in hand (the faithful capture is at the
        // executor's `effective_vk` / hatchery site) — ZERO carrier material.
        &dregg_cell::commitment::RotationCarrierMaterial::default(),
    );
    let after_w = produce(
        after_cell,
        &ledger,
        nullifier_root,
        commitments_root,
        // REVOKED-ROOT: these proving-recipe wrappers commit the EMPTY revocation accumulator
        // (no live revoked root flows through a mint recipe today); stage E/G threads a live root
        // by promoting this to a wrapper param when a revoke-carrying turn needs it.
        &empty_revoked_root_8(),
        receipt_log,
        // recipe path: no effective_vk / contract_hash in hand (the faithful capture is at the
        // executor's `effective_vk` / hatchery site) — ZERO carrier material.
        &dregg_cell::commitment::RotationCarrierMaterial::default(),
    );
    let bridge = |w: &RotationWitness| -> Result<RotatedBlockWitness, String> {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot)
            .map(|bw| bw.with_asset_class(w.asset_class))
            .map_err(|e| format!("mint_welded_wide_umem_cap_write: rotated block witness: {e}"))
    };

    let proj_pre = project_record_kernel_state(before_cell);
    let proj_post = project_record_kernel_state(after_cell);
    let ops = project_diff_ops(&proj_pre, &proj_post);
    let inputs = umem_cohort_proving_inputs_from(&proj_pre, &ops)
        .map_err(|e| format!("mint_welded_wide_umem_cap_write: umem cohort inputs: {e}"))?;

    RotatedParticipantLeg::mint_welded_wide_from_block_witnesses(
        initial_state,
        effects,
        &bridge(&before_w)?,
        &bridge(&after_w)?,
        turn_id,
        &inputs.rows,
        &inputs.boundary,
        inputs.domain,
        None,
        None,
        Some(cap_write),
    )
}

/// **THE WIDE+umem MULTI-DOMAIN WELDED LEG (STAGED, VK-RISK-FREE) — the last family tail.** The
/// two-domain twin of [`mint_welded_wide_umem_rotated_participant_leg`] for the NOTE/BRIDGE economic
/// verbs (`NoteSpend` / `BridgeMint`) whose state touch spans TWO domains in one effect — a
/// `nullifiers` freshness insert + a `heap` balance credit. It bridges the leg's MULTI-DOMAIN
/// universal-memory touch (`pre` + the Blum op trace `ops`, the same shape the standalone multi-domain
/// cohort prover consumes) into the width-`6 + #domains` cohort rows + the REAL boundary via
/// [`dregg_turn::umem::umem_cohort_multidomain_proving_inputs_from`] (fails closed on a single-domain leg),
/// then hands it to
/// [`RotatedParticipantLeg::mint_welded_wide_multidomain_from_block_witnesses`](dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg::mint_welded_wide_multidomain_from_block_witnesses),
/// which welds one guarded `umemOp` per domain onto the WIDE descriptor — purely additive, so the
/// 8-felt (~124-bit) anchors ride through INTACT (no narrowing). The cross-DOMAIN economic invariant
/// (credit == spent/minted value) rides the effect's rotated AIR, NOT the memory reconciliation — the
/// same division as the narrow multi-domain cohort.
///
/// `before_nullifiers` is the note-spend grow-gate's BEFORE nullifier accumulator (a `NoteSpend` lead
/// routes through the wide note-spend producer, which requires it; `BridgeMint` rides the
/// transfer-shape producer — pass `None`). `before_cell`/`after_cell` supply the rotated block
/// witnesses. STAGED: a welded WIDE descriptor BESIDE the deployed wide registry; no VK bump, nothing
/// on the wire.
#[allow(clippy::too_many_arguments)]
pub fn mint_welded_wide_umem_multidomain_rotated_participant_leg(
    initial_state: &dregg_circuit::effect_vm::CellState,
    effects: &[dregg_circuit::effect_vm::Effect],
    before_cell: &Cell,
    after_cell: &Cell,
    nullifier_root: &dregg_circuit::Faithful8,
    commitments_root: &dregg_circuit::Faithful8,
    receipt_log: &[[u8; 32]],
    turn_id: Option<BabyBear>,
    pre: &dregg_turn::umem::UProjection,
    ops: &[dregg_turn::umem::UmemOp],
    before_nullifiers: Option<&[BabyBear]>,
) -> Result<dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg, String> {
    use dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness;
    use dregg_circuit_prove::joint_turn_aggregation::RotatedParticipantLeg;
    use dregg_turn::umem::umem_cohort_multidomain_proving_inputs_from;

    let mut ledger = Ledger::new();
    ledger
        .insert_cell(after_cell.clone())
        .map_err(|e| format!("mint_welded_wide_umem_multidomain: ledger seed failed: {e:?}"))?;

    let before_w = produce(
        before_cell,
        &ledger,
        nullifier_root,
        commitments_root,
        // REVOKED-ROOT: these proving-recipe wrappers commit the EMPTY revocation accumulator
        // (no live revoked root flows through a mint recipe today); stage E/G threads a live root
        // by promoting this to a wrapper param when a revoke-carrying turn needs it.
        &empty_revoked_root_8(),
        receipt_log,
        // recipe path: no effective_vk / contract_hash in hand (the faithful capture is at the
        // executor's `effective_vk` / hatchery site) — ZERO carrier material.
        &dregg_cell::commitment::RotationCarrierMaterial::default(),
    );
    let after_w = produce(
        after_cell,
        &ledger,
        nullifier_root,
        commitments_root,
        // REVOKED-ROOT: these proving-recipe wrappers commit the EMPTY revocation accumulator
        // (no live revoked root flows through a mint recipe today); stage E/G threads a live root
        // by promoting this to a wrapper param when a revoke-carrying turn needs it.
        &empty_revoked_root_8(),
        receipt_log,
        // recipe path: no effective_vk / contract_hash in hand (the faithful capture is at the
        // executor's `effective_vk` / hatchery site) — ZERO carrier material.
        &dregg_cell::commitment::RotationCarrierMaterial::default(),
    );
    let bridge = |w: &RotationWitness| -> Result<RotatedBlockWitness, String> {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot)
            .map(|bw| bw.with_asset_class(w.asset_class))
            .map_err(|e| format!("mint_welded_wide_umem_multidomain: rotated block witness: {e}"))
    };

    // Bridge the leg's MULTI-DOMAIN universal-memory touch into the width-`6 + #domains` cohort rows
    // + REAL boundary (fails closed on a single-domain leg — that uses the single-domain entry).
    let inputs = umem_cohort_multidomain_proving_inputs_from(pre, ops)
        .map_err(|e| format!("mint_welded_wide_umem_multidomain: umem multi-domain inputs: {e}"))?;

    RotatedParticipantLeg::mint_welded_wide_multidomain_from_block_witnesses(
        initial_state,
        effects,
        &bridge(&before_w)?,
        &bridge(&after_w)?,
        turn_id,
        &inputs.rows,
        &inputs.boundary,
        &inputs.domains,
        before_nullifiers,
    )
}
