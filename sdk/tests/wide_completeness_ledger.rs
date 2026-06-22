//! # THE DEPLOYED-PATH PROVABILITY LEDGER — every effect must PROVE on the sovereign wide path.
//!
//! "No forges" (soundness) is table stakes. The system is only USABLE if every effect can produce a
//! light-client-verifiable receipt — i.e. PROVE on the deployed sovereign path
//! (`prove_effect_vm_rotated_wide`). This ledger drives each effect through that exact path and
//! asserts it mints a proof that VERIFIES against the executor-anchored wide descriptor. An effect
//! that falls through to the wrong generator (`generate_rotated_transfer_shape_wide`) is UNSAT here —
//! the test REDS until the effect is routed to its real wide generator with real map_heaps.
//!
//! Mirrors `sovereign_rotated_wide.rs` (the transfer/refusal exemplars). Requires `prover`.
//!
//! ## THE FULL-EFFECT MEASURE (the definitive completeness test)
//!
//! `provability_scoreboard_deployed_wide_path` enumerates EVERY non-`NoOp` `VmEffect` variant
//! (`circuit/src/effect_vm/effect.rs`) — the complete effect set the kernel `Effect`
//! (`turn/src/action.rs`) projects onto via the deployed `convert_effects_to_vm` — and drives each
//! HONEST single-effect sovereign turn through the deployed wide producer, asserting the exact
//! PROVABLE / UNPROVABLE-on-wide classification. The per-family prove-through tests below pin the
//! provable effects (proof MINTS + light-client VERIFIES + the AFTER 8-felt commit MOVED off BEFORE
//! = non-vacuity). The UNPROVABLE-on-wide set is NAMED with its real route (cap-write → the cap-open
//! path; custom → the recursion-bound descriptor), never hidden — the honest remaining worklist for
//! "which effect can an agent drive to a light-client receipt on THIS path."

#![cfg(feature = "prover")]

use dregg_cell::commitment::{V9RotationContext, compute_rotated_pre_limbs};
use dregg_cell::{Cell, CellMode, Ledger};
use dregg_circuit::descriptor_ir2::{parse_vm_descriptor2, verify_vm_descriptor2};
use dregg_circuit::effect_vm::{CellState, Effect as VmEffect, bytes32_to_8_limbs};
use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::wire_commit_8_chip;
use dregg_sdk::full_turn_proof::prove_effect_vm_rotated_wide;
use dregg_turn::rotation_witness as rw;

/// The chip-faithful 8-felt commit of a cell + turn-context (the executor's anchoring primitive).
#[allow(dead_code)]
fn cell_chip_commit8(cell: &Cell, ctx: &V9RotationContext) -> [BabyBear; 8] {
    let pre = compute_rotated_pre_limbs(cell, ctx);
    wire_commit_8_chip(&pre, ctx.iroot)
}

/// 8-felt limbs of a domain-separated BLAKE3 hash (a real, non-sentinel commitment for the
/// grow-gate effects whose new-cell key must be present + non-zero).
fn h8(domain: &[u8]) -> [BabyBear; 8] {
    bytes32_to_8_limbs(blake3::hash(domain).as_bytes())
}

/// Resolve a wide descriptor JSON by its registry key.
fn wide_desc(key: &str) -> dregg_circuit::descriptor_ir2::EffectVmDescriptor2 {
    let json = WIDE_REGISTRY_STAGED_TSV
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some(key) {
                let _ = it.next();
                it.next()
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("{key} not in WIDE_REGISTRY_STAGED_TSV"));
    parse_vm_descriptor2(json).unwrap_or_else(|e| panic!("{key} wide descriptor parses: {e}"))
}

/// **createCell — the issuing sovereign cell ticks its nonce; the accounts set grows.** The new cell's
/// commitment is `create_hash`. The issuing cell's balance is unchanged (createCell does not move
/// value); the deployed apply ticks the issuer nonce, so the AFTER 8-felt commit binds it.
fn sovereign_issuer_cells(balance: i64, domain: &[u8]) -> (Cell, Cell) {
    let token_id = *blake3::hash(domain).as_bytes();
    let mut before = Cell::with_balance([7u8; 32], token_id, balance);
    before.mode = CellMode::Sovereign;
    let mut after = before.clone();
    let _ = after.state.increment_nonce();
    (before, after)
}

/// **THE createCell PROVE-THROUGH (deployed wide path).** An honest createCell turn MUST prove on
/// `prove_effect_vm_rotated_wide` and VERIFY against the executor-anchored wide createCell descriptor.
/// BEFORE routing: createCell falls through to `generate_rotated_transfer_shape_wide` (a transfer
/// trace) → UNSAT vs `createCellVmDescriptor2R24`. AFTER routing it to `generate_rotated_create_cell_wide`
/// (the accounts-set grow-gate): it proves + verifies.
#[test]
fn create_cell_proves_on_deployed_wide_path() {
    let balance: i64 = 100_000;
    let (before_cell, after_cell) = sovereign_issuer_cells(balance, b"ledger-create-cell-domain");

    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_hashes: Vec<[u8; 32]> = vec![];
    let mut ctx_ledger = Ledger::new();
    let _ = ctx_ledger.insert_cell(before_cell.clone());

    let before_w = rw::produce(
        &before_cell,
        &ctx_ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_hashes,
    );
    let after_w = rw::produce(
        &after_cell,
        &ctx_ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_hashes,
    );

    let initial_vm_state = CellState::with_capability_root_and_record_digest(
        balance as u64,
        before_cell.state.nonce() as u32,
        dregg_cell::compute_canonical_capability_root_felt(&before_cell.capabilities),
        dregg_cell::compute_authority_digest_felt(&before_cell),
    );
    let effects = vec![VmEffect::CreateCell {
        create_hash: dregg_circuit::effect_vm::bytes32_to_8_limbs(
            blake3::hash(b"the-new-cell-commitment").as_bytes(),
        ),
    }];
    let caveat = dregg_circuit::effect_vm::trace_rotated::empty_caveat_manifest();

    // -- PRODUCER LEG: mint a wide createCell proof on the DEPLOYED path. --
    let (proof, producer_dpis) = prove_effect_vm_rotated_wide(
        &initial_vm_state,
        &effects,
        &before_w,
        &after_w,
        &caveat,
        None,
        None,
    )
    .expect(
        "DEPLOYED createCell PROVE-THROUGH: createCell MUST prove on the wide path (routed to \
         generate_rotated_create_cell_wide — the accounts-set grow-gate); the transfer-shape \
         fallthrough is UNSAT vs createCellVmDescriptor2R24",
    );

    let desc = wide_desc("createCellVmDescriptor2R24");
    assert_eq!(producer_dpis.len(), desc.public_input_count, "wide createCell PI count");

    // -- VERIFY LEG (the deployed light-client verifier): the minted proof VERIFIES against its
    //    published wide PIs. This is the prove-through: a light client running nothing but
    //    `verify_vm_descriptor2` ACCEPTS an honest createCell turn's receipt. The published commitment
    //    binds the GROWN accounts root (the empty BEFORE tree with `create_hash` inserted via the
    //    limb-0 `.write` map-op), so the createCell-specific grow-gate PI is satisfied — exactly what
    //    the transfer-shape fallthrough could NOT produce. (Anchoring to a trusted RECONSTRUCTED
    //    accounts tree is a deeper soundness check, separate from this liveness pole.) --
    verify_vm_descriptor2(&desc, &proof, &producer_dpis)
        .expect("the honest wide createCell proof VERIFIES against its published wide PIs");

    // Non-vacuity: the AFTER accounts-root limb genuinely advanced (the new cell was inserted) —
    // the grow is real, not a frozen passthrough. The before/after 8-felt commits differ.
    let wide_base = desc.public_input_count - 16;
    let before8 = &producer_dpis[wide_base..wide_base + 8];
    let after8 = &producer_dpis[wide_base + 8..wide_base + 16];
    assert_ne!(
        before8, after8,
        "the createCell grow-gate MOVES the committed state (BEFORE != AFTER 8-felt commit) — the \
         new cell's insertion is genuinely bound, not a frozen passthrough"
    );

    eprintln!(
        "DEPLOYED createCell PROVE-THROUGH GREEN: createCell proves + verifies on the wide path \
         (routed to the accounts-set grow-gate; the AFTER commit binds the grown accounts root)."
    );
}

/// Drive an honest single-effect sovereign turn through the DEPLOYED wide path and return its
/// `(proof, dpis)`. The issuer cell ticks its nonce (the deployed apply for a birth/field write); the
/// `before_w`/`after_w` are produced over a single-cell ledger snapshot, exactly as the createCell
/// prove-through above. This is the shared spine for the per-effect prove-throughs below.
fn prove_through_deployed(
    domain: &[u8],
    effects: &[VmEffect],
) -> (
    dregg_circuit::descriptor_ir2::Ir2BatchProof<dregg_circuit::descriptor_ir2::DreggStarkConfig>,
    Vec<BabyBear>,
) {
    let balance: i64 = 100_000;
    let (before_cell, after_cell) = sovereign_issuer_cells(balance, domain);
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_hashes: Vec<[u8; 32]> = vec![];
    let mut ledger = Ledger::new();
    let _ = ledger.insert_cell(before_cell.clone());
    let before_w =
        rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_hashes);
    let after_w =
        rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_hashes);
    let initial_vm_state = CellState::with_capability_root_and_record_digest(
        balance as u64,
        before_cell.state.nonce() as u32,
        dregg_cell::compute_canonical_capability_root_felt(&before_cell.capabilities),
        dregg_cell::compute_authority_digest_felt(&before_cell),
    );
    let caveat = dregg_circuit::effect_vm::trace_rotated::empty_caveat_manifest();
    prove_effect_vm_rotated_wide(
        &initial_vm_state, effects, &before_w, &after_w, &caveat, None, None,
    )
    .unwrap_or_else(|e| {
        panic!("DEPLOYED PROVE-THROUGH ({domain:?}) must prove on the wide path: {e}")
    })
}

/// Assert the minted wide proof VERIFIES (the deployed light-client verifier) against its published
/// wide PIs, the PI count matches the descriptor, AND the AFTER 8-felt commit genuinely MOVED off the
/// BEFORE commit (non-vacuity: the effect's genuine write is bound, not a frozen passthrough).
fn assert_verifies_and_nonvacuous(
    key: &str,
    proof: &dregg_circuit::descriptor_ir2::Ir2BatchProof<dregg_circuit::descriptor_ir2::DreggStarkConfig>,
    dpis: &[BabyBear],
) {
    let desc = wide_desc(key);
    assert_eq!(dpis.len(), desc.public_input_count, "{key} wide PI count matches descriptor");
    verify_vm_descriptor2(&desc, proof, dpis)
        .unwrap_or_else(|e| panic!("the honest wide {key} proof VERIFIES against its published PIs: {e}"));
    let wide_base = desc.public_input_count - 16;
    let before8 = &dpis[wide_base..wide_base + 8];
    let after8 = &dpis[wide_base + 8..wide_base + 16];
    assert_ne!(
        before8, after8,
        "{key}: the AFTER 8-felt commit MOVED off the BEFORE commit — the effect's genuine write \
         (the grown accounts root / the dyn field) is bound, not a frozen passthrough"
    );
}

/// **THE createCellFromFactory PROVE-THROUGH (deployed wide path).** An honest factory-birth turn MUST
/// prove on `prove_effect_vm_rotated_wide` + VERIFY against `factoryVmDescriptor2R24`. BEFORE routing:
/// createCellFromFactory fell through to `generate_rotated_transfer_shape_wide` → UNSAT (PI-count
/// mismatch vs the factory grow-gate descriptor). AFTER routing it to
/// `generate_rotated_create_from_factory_wide` (the accounts-set grow-gate, child key on param1): it
/// proves + verifies, and the AFTER commit binds the grown accounts root (the born child inserted).
#[test]
fn create_cell_from_factory_proves_on_deployed_wide_path() {
    // The child VK (param1, the new-cell key) MUST be non-zero (an all-zero key collides with the
    // empty-tree sentinel and the `.absent` no-collision op refuses — a witness artifact, not a gap).
    let effects = vec![VmEffect::CreateCellFromFactory {
        factory_vk: BabyBear::new(0xFAC0),
        child_vk_derived: BabyBear::new(0xC417),
    }];
    let (proof, dpis) = prove_through_deployed(b"ledger-factory-domain", &effects);
    assert_verifies_and_nonvacuous("factoryVmDescriptor2R24", &proof, &dpis);
    eprintln!(
        "DEPLOYED createCellFromFactory PROVE-THROUGH GREEN: proves + verifies on the wide path \
         (routed to the factory accounts-set grow-gate; the AFTER commit binds the grown accounts root)."
    );
}

/// **THE spawn PROVE-THROUGH (deployed wide path).** An honest spawn-birth turn MUST prove on
/// `prove_effect_vm_rotated_wide` + VERIFY against `spawnVmDescriptor2R24` for the accounts-birth
/// column. BEFORE: spawn fell through to the transfer-shape producer → UNSAT vs the spawn grow-gate
/// descriptor. AFTER routing it to `generate_rotated_spawn_wide` (the accounts-set grow-gate, born
/// child key on param0): it proves + verifies; the AFTER commit binds the grown accounts root. (The
/// parent→child cap-handoff is the SEPARATE cap-open path's job — not the wide accounts-birth column.)
#[test]
fn spawn_proves_on_deployed_wide_path() {
    // The born child's key (param0 = spawn_hash[0]) MUST be non-zero (empty-tree sentinel collision).
    let spawn_id = BabyBear::new(0x5BA1);
    let effects = vec![VmEffect::SpawnWithDelegation { spawn_hash: [spawn_id; 8] }];
    let (proof, dpis) = prove_through_deployed(b"ledger-spawn-domain", &effects);
    assert_verifies_and_nonvacuous("spawnVmDescriptor2R24", &proof, &dpis);
    eprintln!(
        "DEPLOYED spawn PROVE-THROUGH GREEN: the accounts-birth leg proves + verifies on the wide path \
         (routed to the spawn accounts-set grow-gate; the AFTER commit binds the grown accounts root)."
    );
}

/// **THE setFieldDyn PROVE-THROUGH (deployed wide path).** An honest dynamic overflow-field write
/// (`SetField { field_idx >= 8 }`) MUST prove on `prove_effect_vm_rotated_wide` + VERIFY against
/// `setFieldDynVmDescriptor2R24` (the 581-wide V1Face / 789-wide member). BEFORE: setFieldDyn fell
/// through to the transfer-shape producer → UNSAT vs the distinct dyn geometry. AFTER routing it to
/// `generate_rotated_set_field_dyn_wide` (the Blum linear-memory write→read transport, witnessed by a
/// `MemBoundaryWitness` threaded to `prove_vm_descriptor2` — NOT a `map_heaps`): it proves + verifies,
/// and the AFTER commit binds the dyn-field write (the AFTER fields_root limb forced to the slot).
#[test]
fn set_field_dyn_proves_on_deployed_wide_path() {
    // field_idx 11 (>= 8) is the OVERFLOW write → setFieldDynVmDescriptor2R24; the in-circuit slot is
    // 11 % 8 = 3 (the 8-cell Blum overflow memory address).
    let effects = vec![VmEffect::SetField { field_idx: 11, value: BabyBear::new(0x5E7F) }];
    let (proof, dpis) = prove_through_deployed(b"ledger-setfielddyn-domain", &effects);
    assert_verifies_and_nonvacuous("setFieldDynVmDescriptor2R24", &proof, &dpis);
    eprintln!(
        "DEPLOYED setFieldDyn PROVE-THROUGH GREEN: the dynamic overflow-field write proves + verifies \
         on the wide path (routed to the Blum linear-memory transport; the AFTER commit binds the dyn \
         field — the MemBoundaryWitness, not map_heaps, is the gate's witness)."
    );
}

/// **THE custom PROVE-THROUGH (deployed wide path) — the last liveness item, both poles.**
///
/// An honest custom turn (a user program + its GENUINE external sub-proof) MUST prove on
/// `prove_effect_vm_rotated_wide` + VERIFY against `customVmDescriptor2R24` (the 789-wide member, host
/// 581 + 208 carriers), AND its bound sub-proof MUST light-client-verify through the deployed
/// `custom_proof_bind` engine. A FORGED sub-proof MUST be rejected by that engine.
///
/// BEFORE: a Custom lead fell through to the transfer-shape producer (816-wide) → UNSAT vs the
/// 789-wide custom descriptor, so a custom turn minted NO wide receipt (the LAST liveness gap). AFTER
/// routing it to `generate_rotated_custom_wide`: it proves + verifies. The Custom row's `(vk, commit)`
/// columns (68 / 72) carry the verifying `BoundCustomProof`'s exposed binding
/// (`vk_hash_felts()` / `proof_commitment()`), threaded onto the wire via
/// `Turn::with_custom_program_proofs`; the light client re-runs `verify_proof_bind` against that same
/// binding. This is the deployed, end-to-end path: the wide receipt AND the sub-proof bind the SAME
/// verifying STARK.
#[test]
fn custom_proves_on_deployed_wide_path() {
    use dregg_circuit::custom_proof_bind::{
        BoundCustomProof, ProofBindError, prove_custom_program, verify_bound_custom_proof,
    };
    use dregg_circuit::dsl::circuit::{
        CellProgram, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, PolyTerm,
        ProgramRegistry,
    };
    use std::collections::HashMap;

    // ── A minimal but REAL custom program (boolean dir + the conservation poly): its STARK is genuine.
    let p_minus_1 = BabyBear::new(dregg_circuit::field::BABYBEAR_P - 1);
    let descriptor = CircuitDescriptor {
        name: "dregg-custom-wide-ledger-v1".to_string(),
        trace_width: 4,
        max_degree: 2,
        columns: vec![
            ColumnDef { name: "old".into(), index: 0, kind: ColumnKind::Value },
            ColumnDef { name: "amt".into(), index: 1, kind: ColumnKind::Value },
            ColumnDef { name: "new".into(), index: 2, kind: ColumnKind::Value },
            ColumnDef { name: "dir".into(), index: 3, kind: ColumnKind::Binary },
        ],
        constraints: vec![
            ConstraintExpr::Binary { col: 3 },
            ConstraintExpr::Polynomial {
                terms: vec![
                    PolyTerm { coeff: BabyBear::ONE, col_indices: vec![2] },
                    PolyTerm { coeff: p_minus_1, col_indices: vec![0] },
                    PolyTerm { coeff: p_minus_1, col_indices: vec![1] },
                    PolyTerm { coeff: BabyBear::new(2), col_indices: vec![3, 1] },
                ],
            },
        ],
        boundaries: vec![],
        public_input_count: 2,
        lookup_tables: vec![],
    };
    let program = CellProgram::new(descriptor, 1);
    let mut registry = ProgramRegistry::new();
    registry.deploy(program.clone()).expect("demo program deploys");

    let rows = 4usize;
    let mut witness: HashMap<String, Vec<BabyBear>> = HashMap::new();
    witness.insert("old".into(), vec![BabyBear::new(10); rows]);
    witness.insert("amt".into(), vec![BabyBear::new(5); rows]);
    witness.insert("new".into(), vec![BabyBear::new(15); rows]);
    witness.insert("dir".into(), vec![BabyBear::ZERO; rows]);
    let pis = vec![BabyBear::new(10), BabyBear::new(15)];

    // ── Mint the GENUINE bound sub-proof, and confirm it light-client-verifies (positive soundness).
    let bound: BoundCustomProof =
        prove_custom_program(&program, &witness, rows, &pis).expect("honest sub-proof proves");
    verify_bound_custom_proof(&registry, &bound)
        .expect("the honest bound proof MUST light-client-verify (positive pole)");

    // ── The Custom effect carries the verifying sub-proof's exposed binding: the wide row's cols
    //    68 / 72 then hold exactly what `verify_proof_bind` re-derives.
    let effects = vec![VmEffect::Custom {
        program_vk_hash: bound.vk_hash_felts(),
        proof_commitment: bound.proof_commitment(),
    }];

    // ── PROVE-THROUGH the deployed wide path + VERIFY the wide receipt (liveness: a custom turn now
    //    mints a REAL wide receipt).
    let (proof, dpis) = prove_through_deployed(b"ledger-custom-domain", &effects);
    assert_verifies_and_nonvacuous("customVmDescriptor2R24", &proof, &dpis);

    // ── The on-wire threading: a custom Turn carries the genuine sub-proof so the light client can run
    //    the recursion. Confirm the projection round-trips back to a verifying bound proof.
    let wire = bound_to_wire_and_back(&bound);
    verify_bound_custom_proof(&registry, &wire)
        .expect("the wire-threaded sub-proof (Turn::with_custom_program_proofs projection) verifies");

    // ── NEGATIVE POLE: a FORGED sub-proof is REJECTED by the deployed engine (the wide receipt's
    //    `proof_bind` MEANS "the bound proof verified").
    let mut forged = bound.clone();
    for b in forged.proof_bytes.iter_mut().take(64) {
        *b ^= 0xFF;
    }
    let err = verify_bound_custom_proof(&registry, &forged)
        .expect_err("a FORGED custom sub-proof MUST be rejected end-to-end");
    assert!(
        matches!(err, ProofBindError::SubProofVerifyFailed(_)),
        "forged proof bytes must fail at the recursion (verify) step, got {err:?}"
    );

    eprintln!(
        "DEPLOYED custom PROVE-THROUGH GREEN: an honest custom turn (user program + genuine sub-proof) \
         proves + verifies on the wide path (routed to `generate_rotated_custom_wide`, the 789-wide \
         customVmDescriptor2R24 member); the bound sub-proof light-client-verifies via custom_proof_bind \
         and a forged sub-proof is REJECTED. The last liveness item is CLOSED — 29/29."
    );
}

/// Round-trip a `BoundCustomProof` through the on-wire `Turn::with_custom_program_proofs` projection
/// (`CustomProgramProof { proof_bytes, public_inputs }`) and rebuild the bound proof — confirming the
/// wire form carries everything the light-client recursion needs (proof bytes + public inputs;
/// the program is resolved by the bound VK in the registry).
fn bound_to_wire_and_back(
    bound: &dregg_circuit::custom_proof_bind::BoundCustomProof,
) -> dregg_circuit::custom_proof_bind::BoundCustomProof {
    use dregg_circuit::field::BabyBear;
    let turn_carrier = dregg_turn::CustomProgramProof {
        proof_bytes: bound.proof_bytes.clone(),
        public_inputs: bound.public_inputs.iter().map(|f| f.as_u32()).collect(),
    };
    dregg_circuit::custom_proof_bind::BoundCustomProof {
        program: bound.program.clone(),
        proof_bytes: turn_carrier.proof_bytes,
        public_inputs: turn_carrier
            .public_inputs
            .iter()
            .map(|&v| BabyBear::new(v))
            .collect(),
    }
}

/// What extra witness an effect's wide producer needs beyond the bare `(before_w, after_w)`, AND
/// (for the record-pin family) how to build the genuine AFTER-cell + the matching `VmEffect`.
enum WideNeed {
    /// No extra witness (the bare grow-gate / transfer-shape route). The hand-built `VmEffect` in the
    /// case tuple is proven directly against the nonce-tick issuer pair.
    Plain,
    /// The BEFORE nullifier set the note-spend grow-gate's `.absent`/`.insert` map-op opens against.
    NoteSpendNullifiers(Vec<BabyBear>),
    /// The RECORD-PIN family (setPermissions/setVK/cellSeal/cellUnseal/cellDestroy/receiptArchive +
    /// refusal): the AFTER record-digest / lifecycle / fields_root limb the descriptor pins is a
    /// GENUINE move that the nonce-tick issuer pair does NOT make. The closure builds the KERNEL
    /// `Effect` (given the before-cell id), which we (a) apply to the after-cell via the SHARED
    /// `apply_effect_to_cell` weld, and (b) project to the matching `VmEffect` via the deployed
    /// `AgentCipherclerk::convert_effects_to_vm` — so producer + verifier move together (the anti-drift
    /// guarantee). `refusal` additionally threads the fields-tree write witness.
    RecordPin(Box<dyn Fn(dregg_cell::CellId) -> dregg_turn::Effect>),
}

/// The DEPLOYED-WIDE probe for ONE effect: build the honest sovereign turn, thread the effect's
/// required witness, and drive it through `prove_effect_vm_rotated_wide`. Returns the proof+PIs on
/// SAT or the precise prover error string on UNSAT. NO catch_unwind — a prover refusal is a genuine
/// UNPROVABLE (the effect cannot mint a light-client receipt on the wide path). For the record-pin
/// family the `effects` arg is IGNORED (the projection derives the VmEffect from the kernel effect).
fn probe_wide(
    domain: &[u8],
    effects: &[VmEffect],
    need: &WideNeed,
) -> Result<
    (
        dregg_circuit::descriptor_ir2::Ir2BatchProof<dregg_circuit::descriptor_ir2::DreggStarkConfig>,
        Vec<BabyBear>,
    ),
    String,
> {
    use dregg_sdk::AgentCipherclerk;

    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let block_height: u64 = 100;
    let caveat = dregg_circuit::effect_vm::trace_rotated::empty_caveat_manifest();

    // Build the before-cell, then (for the record-pin family) the GENUINE after-cell via the shared
    // weld + the matching VmEffect via the deployed projection. Plain effects use the nonce-tick pair.
    let (before_cell, after_cell, vm_effects, refusal_ctx): (
        Cell,
        Cell,
        Vec<VmEffect>,
        Option<(Vec<dregg_circuit::heap_root::HeapLeaf>, BabyBear)>,
    ) = match need {
        WideNeed::RecordPin(build_kernel) => {
            let token_id = *blake3::hash(domain).as_bytes();
            let mut before = Cell::with_balance([7u8; 32], token_id, 100_000);
            before.mode = CellMode::Sovereign;
            let cell_id = before.id();
            let kernel = build_kernel(cell_id);
            // cellUnseal moves the lifecycle Sealed → Live; the before-cell MUST already be sealed
            // (else `unseal()` is a no-op and the lifecycle limb does not move). Pre-seal at a prior
            // height so the unseal is a genuine transition.
            if matches!(kernel, dregg_turn::Effect::CellUnseal { .. }) {
                let _ = before.seal([0x5Eu8; 32], 1);
            }
            let mut after = before.clone();
            rw::apply_effect_to_cell(&mut after, &cell_id, &kernel, block_height);
            // The deployed Effect→VmEffect projection (byte-identical to the executor bridge): this is
            // what makes the producer's bound limb EQUAL the verifier's anchored limb.
            let vm = AgentCipherclerk::convert_effects_to_vm(&cell_id, &[kernel.clone()]);
            // Refusal also needs the fields-tree write witness.
            let refusal_ctx = if matches!(kernel, dregg_turn::Effect::Refusal { .. }) {
                let audit_bytes = after
                    .state
                    .fields_map
                    .get(&dregg_cell::state::REFUSAL_AUDIT_EXT_KEY)
                    .copied()
                    .expect("a refused cell carries the audit slot in fields_map");
                let before_leaves =
                    dregg_cell::state::fields_root_leaves(&before.state.fields_map);
                let audit_value = dregg_circuit::cap_root::fold_bytes32(&audit_bytes);
                Some((before_leaves, audit_value))
            } else {
                None
            };
            (before, after, vm, refusal_ctx)
        }
        _ => {
            let (b, a) = sovereign_issuer_cells(100_000, domain);
            (b, a, effects.to_vec(), None)
        }
    };

    let mut ledger = Ledger::new();
    let _ = ledger.insert_cell(before_cell.clone());
    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &[]);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &[]);
    let initial = CellState::with_capability_root_and_record_digest(
        100_000u64,
        before_cell.state.nonce() as u32,
        dregg_cell::compute_canonical_capability_root_felt(&before_cell.capabilities),
        dregg_cell::compute_authority_digest_felt(&before_cell),
    );

    let before_nullifiers: Option<&[BabyBear]> = match need {
        WideNeed::NoteSpendNullifiers(nfs) => Some(nfs.as_slice()),
        _ => None,
    };
    let refusal_fields = refusal_ctx
        .as_ref()
        .map(|(leaves, audit)| (leaves.as_slice(), *audit));

    prove_effect_vm_rotated_wide(
        &initial,
        &vm_effects,
        &before_w,
        &after_w,
        &caveat,
        before_nullifiers,
        refusal_fields,
    )
    .map_err(|e| e.to_string())
}

/// The complete enumeration of `VmEffect` cohort leads, each with an HONEST instance + its wide
/// witness need. This is THE census the scoreboard drives: every effect-vm variant `rotated_descriptor_name`
/// resolves (`NoOp` is padding, never a turn lead — excluded by construction). The cap-write family
/// (Grant/Revoke/Attenuate/Refresh/RevokeDelegation/Introduce) appears here at its BARE wide
/// descriptor — the LIGHT-CLIENT route for those is the SEPARATE cap-open path (private prover,
/// exercised at the circuit-descriptor self-verify level in `circuit/tests/cap_open_self_verify.rs`);
/// this census measures whether the WIDE sovereign producer can mint+verify each at all.
fn all_wide_cases() -> Vec<(&'static str, Vec<VmEffect>, WideNeed)> {
    let z8 = [BabyBear::new(0); 8];
    vec![
        // ── value family ──────────────────────────────────────────────────────────────────────
        ("transfer", vec![VmEffect::Transfer { amount: 100, direction: 1 }], WideNeed::Plain),
        (
            "burn",
            vec![VmEffect::Burn {
                target_hash: BabyBear::new(0xB0F0),
                amount_lo: BabyBear::new(500),
                amount_full: 500,
            }],
            WideNeed::Plain,
        ),
        (
            "bridgeMint",
            vec![VmEffect::BridgeMint {
                value_lo: BabyBear::new(900),
                mint_hash: BabyBear::new(0x31D6),
                value_full: 900,
            }],
            WideNeed::Plain,
        ),
        // ── field family ──────────────────────────────────────────────────────────────────────
        ("setField", vec![VmEffect::SetField { field_idx: 3, value: BabyBear::new(0x5E70) }], WideNeed::Plain),
        ("setFieldDyn", vec![VmEffect::SetField { field_idx: 11, value: BabyBear::new(0x5E7F) }], WideNeed::Plain),
        // ── bookkeeping family ────────────────────────────────────────────────────────────────
        ("incrementNonce", vec![VmEffect::IncrementNonce], WideNeed::Plain),
        (
            "emitEvent",
            vec![VmEffect::EmitEvent { topic_hash: h8(b"topic"), payload_hash: h8(b"payload") }],
            WideNeed::Plain,
        ),
        ("makeSovereign", vec![VmEffect::MakeSovereign], WideNeed::Plain),
        ("pipelinedSend", vec![VmEffect::PipelinedSend { send_hash: z8 }], WideNeed::Plain),
        // ── birth / accounts-grow family ──────────────────────────────────────────────────────
        ("createCell", vec![VmEffect::CreateCell { create_hash: h8(b"new-cell") }], WideNeed::Plain),
        (
            "createCellFromFactory",
            vec![VmEffect::CreateCellFromFactory {
                factory_vk: BabyBear::new(7),
                child_vk_derived: BabyBear::new(11),
            }],
            WideNeed::Plain,
        ),
        (
            "spawnWithDelegation",
            vec![VmEffect::SpawnWithDelegation { spawn_hash: [BabyBear::new(0x5BA1); 8] }],
            WideNeed::Plain,
        ),
        // ── note family ───────────────────────────────────────────────────────────────────────
        (
            "noteSpend",
            vec![VmEffect::NoteSpend { nullifier: BabyBear::new(0x57E1), value: 700 }],
            // An HONEST spend reveals a FRESH nullifier — it must be ABSENT from the BEFORE nullifier
            // set (the in-circuit `.absent` freshness op refuses a re-spend). So the BEFORE set is
            // EMPTY; the grow-gate `.insert` then grows it by this fresh nullifier.
            WideNeed::NoteSpendNullifiers(vec![]),
        ),
        (
            "noteCreate",
            vec![VmEffect::NoteCreate { commitment: BabyBear::new(0xC0EE), value: 300 }],
            WideNeed::Plain,
        ),
        // ── record-pin / lifecycle family (the AFTER limb is a GENUINE move; the kernel effect is
        //    applied via `apply_effect_to_cell` + projected via `convert_effects_to_vm`) ─────────
        (
            "setPermissions",
            vec![], // derived from the kernel effect (RecordPin)
            WideNeed::RecordPin(Box::new(|cell| dregg_turn::Effect::SetPermissions {
                cell,
                new_permissions: dregg_cell::Permissions::zkapp(),
            })),
        ),
        (
            "setVerificationKey",
            vec![],
            WideNeed::RecordPin(Box::new(|cell| dregg_turn::Effect::SetVerificationKey {
                cell,
                new_vk: Some(dregg_cell::VerificationKey::from_components(
                    &dregg_cell::vk_v2::VkComponents {
                        program_bytes: b"wide-ledger-vk-program",
                        air_fingerprint: [0x11; 32],
                        verifier_fingerprint:
                            dregg_cell::vk_v2::VerifierFingerprint::SourceHash([0x22; 32]),
                        proving_system_id: dregg_cell::vk_v2::ProvingSystemId::Plonky3BabyBearFri {
                            p3_rev: "wide-ledger",
                        },
                    },
                )),
            })),
        ),
        (
            "cellSeal",
            vec![],
            WideNeed::RecordPin(Box::new(|cell| dregg_turn::Effect::CellSeal {
                target: cell,
                reason: [0x5Au8; 32],
            })),
        ),
        (
            "cellUnseal",
            vec![],
            WideNeed::RecordPin(Box::new(|cell| dregg_turn::Effect::CellUnseal { target: cell })),
        ),
        (
            "cellDestroy",
            vec![],
            WideNeed::RecordPin(Box::new(|cell| dregg_turn::Effect::CellDestroy {
                target: cell,
                certificate: dregg_cell::lifecycle::DeathCertificate {
                    cell_id: cell,
                    last_receipt_hash: [0x01; 32],
                    final_state_commitment: [0x02; 32],
                    destroyed_at_height: 99,
                    reason: dregg_cell::lifecycle::DeathReason::Voluntary,
                },
            })),
        ),
        (
            "receiptArchive",
            vec![],
            WideNeed::RecordPin(Box::new(|cell| dregg_turn::Effect::ReceiptArchive {
                prefix_end_height: 42,
                checkpoint: dregg_cell::lifecycle::ArchivalAttestation {
                    cell_id: cell,
                    archive_start_height: 0,
                    archive_end_height: 42,
                    archive_blob_hash: [0x03; 32],
                    archive_terminal_commitment: [0x04; 32],
                    archive_terminal_receipt_hash: [0x05; 32],
                },
            })),
        ),
        (
            "refusal",
            vec![],
            WideNeed::RecordPin(Box::new(|cell| dregg_turn::Effect::Refusal {
                cell,
                offered_action_commitment: [11u8; 32],
                refusal_reason: dregg_turn::action::RefusalReason::Declined,
                proof_witness_index: 0,
            })),
        ),
        // ── recursion-bound family ────────────────────────────────────────────────────────────
        (
            "custom",
            vec![VmEffect::Custom { program_vk_hash: h8(b"custom-vk"), proof_commitment: [BabyBear::new(0xC0); 4] }],
            WideNeed::Plain,
        ),
        // ── cap-write family whose AFTER cap-root is a MAP-OP write (the in-circuit cap-tree open).
        //    These have NO map-op WITNESS HEAP on the bare wide sovereign path → UNSAT-on-wide. Their
        //    LIGHT-CLIENT route is the SEPARATE cap-open path (`<effect>CapOpenVmDescriptor2R24`, the
        //    private `prove_effect_vm_cap_open*` exercised at the circuit-descriptor self-verify level
        //    in `circuit/tests/cap_open_self_verify.rs`). `attenuateCapability`/`revokeCapability`
        //    REFUSE cleanly here ("no witness heap with root …"); `grantCapability` UNSAT-PANICS the
        //    debug constraint-checker, so it is NAMED statically below (not driven through the loop).
        (
            "attenuateCapability",
            vec![VmEffect::AttenuateCapability {
                cap_slot_hash: [BabyBear::new(0x51); 8],
                narrower_commitment: [BabyBear::new(0x52); 8],
                phase_b: None,
            }],
            WideNeed::Plain,
        ),
        (
            "revokeCapability",
            vec![VmEffect::RevokeCapability { slot_hash: [BabyBear::new(0x4E); 8], phase_b: None }],
            WideNeed::Plain,
        ),
        // revokeDelegation/refreshDelegation/introduce DO prove on the bare wide path (their wide
        // descriptors are passthrough/transfer-shape members that need no cap-tree heap witness).
        ("revokeDelegation", vec![VmEffect::RevokeDelegation { child_hash: h8(b"revoke-child") }], WideNeed::Plain),
        (
            "refreshDelegation",
            vec![VmEffect::RefreshDelegation { child_hash: h8(b"refresh-child"), snapshot_value: h8(b"snapshot") }],
            WideNeed::Plain,
        ),
        ("introduce", vec![VmEffect::Introduce { intro_hash: h8(b"intro") }], WideNeed::Plain),
        ("exerciseViaCapability", vec![VmEffect::ExerciseViaCapability { exercise_hash: z8 }], WideNeed::Plain),
    ]
}

/// Look up ONE case from `all_wide_cases` by label (the prove-through tests drive a single named
/// effect through the shared `probe_wide` spine, then assert verify + non-vacuity).
fn case(label: &str) -> (&'static str, Vec<VmEffect>, WideNeed) {
    all_wide_cases()
        .into_iter()
        .find(|(l, _, _)| *l == label)
        .unwrap_or_else(|| panic!("{label} is not an enumerated wide case"))
}

/// Drive a single named effect through the DEPLOYED wide path and assert it VERIFIES + is non-vacuous
/// (the AFTER 8-felt commit MOVED off BEFORE). `desc_key` is its wide descriptor registry key.
fn prove_through_and_check(label: &str, desc_key: &str) {
    let (_, effects, need) = case(label);
    let (proof, dpis) = probe_wide(label.as_bytes(), &effects, &need)
        .unwrap_or_else(|e| panic!("DEPLOYED {label} PROVE-THROUGH must prove on the wide path: {e}"));
    assert_verifies_and_nonvacuous(desc_key, &proof, &dpis);
    eprintln!("DEPLOYED {label} PROVE-THROUGH GREEN: proves + verifies on the wide path ({desc_key}).");
}

/// **THE value-family PROVE-THROUGHS (burn / bridgeMint).** An honest burn / bridge-mint sovereign
/// turn proves on the deployed wide path + light-client-VERIFIES; the AFTER commit binds the genuine
/// balance move (non-vacuity).
#[test]
fn burn_and_bridge_mint_prove_on_deployed_wide_path() {
    prove_through_and_check("burn", "burnVmDescriptor2R24");
    prove_through_and_check("bridgeMint", "mintVmDescriptor2R24");
}

/// **THE note-family PROVE-THROUGHS (noteSpend / noteCreate).** An honest note spend (fresh nullifier,
/// EMPTY before-set → the `.absent` freshness op + `.insert` grow-gate) and note create both prove on
/// the deployed wide path + VERIFY.
#[test]
fn note_spend_and_create_prove_on_deployed_wide_path() {
    prove_through_and_check("noteSpend", "noteSpendVmDescriptor2R24");
    prove_through_and_check("noteCreate", "noteCreateVmDescriptor2R24");
}

/// **THE bookkeeping PROVE-THROUGHS (incrementNonce / emitEvent / makeSovereign / pipelinedSend).**
/// Each proves on the deployed wide path + VERIFIES against its wide descriptor.
#[test]
fn bookkeeping_family_proves_on_deployed_wide_path() {
    prove_through_and_check("incrementNonce", "incrementNonceVmDescriptor2R24");
    prove_through_and_check("emitEvent", "emitEventVmDescriptor2R24");
    prove_through_and_check("makeSovereign", "makeSovereignVmDescriptor2R24");
    prove_through_and_check("pipelinedSend", "pipelinedSendVmDescriptor2R24");
}

/// **THE record-pin / lifecycle PROVE-THROUGHS.** Each effect's AFTER record-digest / lifecycle /
/// fields_root limb is a GENUINE move (built via the deployed `apply_effect_to_cell` + projected via
/// `convert_effects_to_vm`), so the record-pin descriptor's pin is satisfied. All prove + VERIFY on
/// the deployed wide path. This is the lifecycle family an agent uses to seal / unseal / destroy /
/// archive / re-permission / re-key a sovereign cell with a light-client-verifiable receipt.
#[test]
fn record_pin_family_proves_on_deployed_wide_path() {
    prove_through_and_check("setPermissions", "setPermsVmDescriptor2R24");
    prove_through_and_check("setVerificationKey", "setVKVmDescriptor2R24");
    prove_through_and_check("cellSeal", "cellSealVmDescriptor2R24");
    prove_through_and_check("cellUnseal", "cellUnsealVmDescriptor2R24");
    prove_through_and_check("cellDestroy", "cellDestroyVmDescriptor2R24");
    prove_through_and_check("receiptArchive", "receiptArchiveVmDescriptor2R24");
    prove_through_and_check("refusal", "refusalVmDescriptor2R24");
}

/// **THE delegation-family PROVE-THROUGHS (revokeDelegation / refreshDelegation / introduce).** These
/// cap-RELATED effects have BARE wide descriptors that need no cap-tree heap witness (passthrough /
/// transfer-shape members), so they prove on the deployed wide path + VERIFY. (The cap-WRITE family —
/// attenuate/grant/revokeCapability — does NOT; its route is the cap-open path, named in the
/// scoreboard.)
#[test]
fn delegation_family_proves_on_deployed_wide_path() {
    prove_through_and_check("revokeDelegation", "revokeVmDescriptor2R24");
    prove_through_and_check("refreshDelegation", "refreshVmDescriptor2R24");
    prove_through_and_check("introduce", "introduceVmDescriptor2R24");
    prove_through_and_check("exerciseViaCapability", "exerciseVmDescriptor2R24");
}

/// The effects whose AFTER cap-root is an in-circuit cap-tree MAP-OP write, so the BARE wide
/// sovereign producer (which threads NO cap-tree witness heap) cannot prove them — their
/// light-client receipt is minted on the SEPARATE cap-open path (`<effect>CapOpenVmDescriptor2R24`,
/// the private `prove_effect_vm_cap_open*`, exercised at the circuit-descriptor self-verify level in
/// `circuit/tests/cap_open_self_verify.rs`). Named here so the scoreboard accounts for EVERY effect.
/// `grantCapability` is in this set but NOT driven through the probe loop — its UNSAT wide trace
/// PANICS the debug constraint-checker rather than returning a clean `Err`, which would abort the
/// enumerating test; the route it belongs to (cap-open) is the same as the other two.
const CAP_OPEN_ROUTE_EFFECTS: &[&str] =
    &["attenuateCapability", "revokeCapability", "grantCapability"];

// `custom` — CLOSED (both axes). The DISTINCT 789-wide `customVmDescriptor2R24` member (host 581 +
// 208 carriers — same V1Face host as setFieldDyn, but a Custom row, no Blum/grow-gate leg) is now
// routed by `generate_rotated_custom_wide`: a single-effect Custom turn MINTS a wide EffectVM receipt
// on `prove_effect_vm_rotated_wide`, and the receipt's 8-felt commit binds the state. The bare
// transfer-shape producer (816-wide) was UNSAT vs the 789-wide descriptor — that liveness gap is
// closed.
//
// SOUNDNESS (closed earlier, verified end-to-end here): the `proof_bind` gate genuinely VERIFIES the
// external sub-proof via the deployed, SDK-reachable `dregg_circuit::custom_proof_bind`: resolve the
// program by the bound 8-felt VK, VERIFY the external STARK under its AIR (the recursion), and require
// the sub-proof's PI commitment to equal the bound `commit` column. A FORGED sub-proof (non-verifying
// STARK / mismatched commitment / unknown VK) is REJECTED. The in-AIR `proof_bind` op is a
// bounds/declaration check (`descriptor_ir2.rs:1270`); the program-correctness recursion is the
// external engine, threaded onto the wire via `Turn::with_custom_program_proofs` (the
// `custom_program_proofs` field, bound into `Turn::hash`). The 789-wide custom row carries the bound
// proof's `(vk, commit)` in cols 68 / 72 — so the wide receipt + the light-client `verify_proof_bind`
// bind the SAME verifying sub-proof. See `custom_proves_on_deployed_wide_path` (the end-to-end
// prove-through + sub-proof verify, both poles).

/// **THE PROVABILITY SCOREBOARD (the living completeness measure).** Drive EVERY `VmEffect` cohort
/// lead through the DEPLOYED wide path (`prove_effect_vm_rotated_wide`) and report PROVABLE/UNPROVABLE
/// with the precise reason. An effect that cannot prove on a path cannot produce a light-client
/// receipt on that path — i.e. is not USABLE there by an agent. The scoreboard ASSERTS the
/// classification against a NAMED expectation, so a regression (a wide-native effect that STOPS
/// proving) OR a closed gap (a cap-open/custom effect that STARTS proving on the wide path)
/// RED-flags this test until the expectation is updated — the scoreboard is the honest worklist,
/// never a green lie. Run with `--nocapture` for the full board.
///
/// THE FULL EFFECT-VM ENUMERATION (`circuit/src/effect_vm/effect.rs`, every non-`NoOp` variant; the
/// `Effect` kernel enum `turn/src/action.rs` projects onto these via the deployed
/// `convert_effects_to_vm`): Transfer · Burn · BridgeMint · SetField(idx<8) · SetField(idx>=8 =
/// setFieldDyn) · IncrementNonce · EmitEvent · MakeSovereign · PipelinedSend · CreateCell ·
/// CreateCellFromFactory · SpawnWithDelegation · NoteSpend · NoteCreate · SetPermissions ·
/// SetVerificationKey · CellSeal · CellUnseal · CellDestroy · ReceiptArchive · Refusal · Custom ·
/// AttenuateCapability · GrantCapability · RevokeCapability · RevokeDelegation · RefreshDelegation ·
/// Introduce · ExerciseViaCapability. That is the COMPLETE set (the kernel `Effect`'s reactive
/// Promise/Notify/React + cross-cell GrantCapability/Introduce/PipelinedSend all project onto these
/// VmEffect leads, or are non-state-transition turn-builder primitives that carry no VmEffect lead).
#[test]
fn provability_scoreboard_deployed_wide_path() {
    eprintln!("=== DEPLOYED-WIDE PROVABILITY SCOREBOARD (prove_effect_vm_rotated_wide) ===");
    let mut provable: Vec<&'static str> = Vec::new();
    let mut unprovable: Vec<(&'static str, String)> = Vec::new();
    for (label, effects, need) in all_wide_cases() {
        match probe_wide(label.as_bytes(), &effects, &need) {
            Ok(_) => {
                eprintln!("  [PROVABLE]    {label}");
                provable.push(label);
            }
            Err(e) => {
                let reason = e.lines().next().unwrap_or(&e).to_string();
                eprintln!("  [UNPROVABLE]  {label}: {reason}");
                unprovable.push((label, reason));
            }
        }
    }
    // grantCapability is NAMED, not probed (its UNSAT wide trace panics the debug checker; route =
    // cap-open, same as attenuate/revokeCapability). It appears in the board as a static UNPROVABLE.
    eprintln!(
        "  [UNPROVABLE]  grantCapability: cap-tree map-op has no witness heap on the bare wide path \
         (UNSAT-panics the debug constraint-checker); route = grantCapCapOpenVmDescriptor2R24"
    );
    eprintln!("--------------------------------------------------------------------------");
    eprintln!("PROVABLE-ON-WIDE   ({}): {provable:?}", provable.len());
    let unprovable_labels: Vec<&str> = unprovable
        .iter()
        .map(|(l, _)| *l)
        .chain(std::iter::once("grantCapability"))
        .collect();
    eprintln!("UNPROVABLE-ON-WIDE ({}): {unprovable_labels:?}", unprovable_labels.len());
    for (l, r) in &unprovable {
        eprintln!("    UNPROVABLE-ON-WIDE {l}: {r}");
    }
    eprintln!(
        "    (cap-write family route = the cap-open path {CAP_OPEN_ROUTE_EFFECTS:?} — the one NAMED \
         residual: an agent CAN exercise it, just not through this bare wide sovereign producer. \
         `custom` is no longer a residual — it PROVES on the wide path (the bound sub-proof rides the \
         `proof_bind` columns the light client verifies via `custom_proof_bind`).)"
    );
    eprintln!("==========================================================================");

    // ── REGRESSION FLOOR: every wide-NATIVE effect MUST prove on the deployed wide path. These are
    // the effects an agent can drive to a light-client-verifiable receipt on the wide path TODAY. A
    // drop here is a real routing regression (an effect stopped proving).
    let must_prove_on_wide = [
        "transfer",
        "burn",
        "bridgeMint",
        "setField",
        "setFieldDyn",
        "incrementNonce",
        "emitEvent",
        "makeSovereign",
        "pipelinedSend",
        "createCell",
        "createCellFromFactory",
        "spawnWithDelegation",
        "noteSpend",
        "noteCreate",
        "setPermissions",
        "setVerificationKey",
        "cellSeal",
        "cellUnseal",
        "cellDestroy",
        "receiptArchive",
        "refusal",
        "custom",
        "revokeDelegation",
        "refreshDelegation",
        "introduce",
        "exerciseViaCapability",
    ];
    let missing: Vec<&str> =
        must_prove_on_wide.iter().copied().filter(|l| !provable.contains(l)).collect();
    assert!(
        missing.is_empty(),
        "WIDE-PATH REGRESSION: these wide-native effects MUST prove on the deployed wide path but \
         did not: {missing:?}. Unprovable board: {unprovable:?}"
    );
    assert_eq!(
        provable.len(),
        must_prove_on_wide.len(),
        "exactly the {} wide-native effects prove on the wide path; an UNEXPECTED prove means a \
         cap-open/custom gap CLOSED — update the expectation + add it to the must-prove floor: \
         provable={provable:?}",
        must_prove_on_wide.len()
    );

    // ── THE NAMED UNPROVABLE-ON-WIDE SET: the cap-write family (cap-open route). These are NOT usable
    // through the bare wide sovereign producer; they are usable through their own (cap-open) route. If
    // one starts proving on the wide path, this assertion RED-flags so the worklist stays honest. The
    // probed (clean-Err) members are attenuate/revokeCapability; grantCapability is the named
    // (panic-on-wide) member. `custom` is NO LONGER here — it now PROVES on the wide path (its 789-wide
    // `customVmDescriptor2R24` member is routed via `generate_rotated_custom_wide`); the
    // program-correctness recursion rides the bound sub-proof the light client verifies via
    // `custom_proof_bind` (see `custom_proves_on_deployed_wide_path` below).
    let mut expected_unprovable: Vec<&str> = CAP_OPEN_ROUTE_EFFECTS.to_vec();
    expected_unprovable.sort_unstable();
    let mut got_unprovable = unprovable_labels.clone();
    got_unprovable.sort_unstable();
    assert_eq!(
        got_unprovable, expected_unprovable,
        "the UNPROVABLE-ON-WIDE set must be exactly the cap-write family (the NAMED residual with its \
         own cap-open route); got {got_unprovable:?}, expected {expected_unprovable:?}"
    );
}

/// **THE custom proof_bind DESCRIPTOR PIN (the columns the genuine engine binds).**
/// `custom` is the effect whose receipt rides an EXTERNAL program sub-proof, bound via the
/// descriptor's `proof_bind` op. The genuine engine that VERIFIES that sub-proof (not a bounds
/// check) is `dregg_circuit::custom_proof_bind` — exercised end-to-end in
/// `custom_proof_bind_honest_verifies_forged_rejected` below. This test pins the descriptor columns
/// that engine binds, so a regression dropping the `proof_bind` op or its column binding FAILS here:
///   * the deployed `customVmDescriptor2R24` carries EXACTLY ONE `proof_bind` IR constraint;
///   * it is GUARDED on the Custom selector (`sel::CUSTOM` = var 8) — so it fires only on a custom row;
///   * it binds the `custom_proof_commitment` column (var 72) and the `custom_program_vk_hash` column
///     (var 68) — the two columns the recursion verifier pins to the verifying sub-proof's PI
///     commitment + program VK.
///
/// The proof_bind GATE now MEANS "the bound proof verified": `custom_proof_bind::verify_proof_bind`
/// resolves the program by the bound VK, VERIFIES the external STARK sub-proof under its AIR, and
/// requires the sub-proof's PI commitment to equal the bound `commit` column. A custom effect with a
/// FORGED sub-proof (non-verifying STARK / mismatched commitment / unknown VK) is REJECTED — the
/// bounds-check-only era is closed (see the genuine test below).
#[test]
fn custom_descriptor_carries_proof_bind_residual_named() {
    use dregg_circuit::descriptor_ir2::VmConstraint2;
    use dregg_circuit::lean_descriptor_air::LeanExpr;

    // sel::CUSTOM = 8 (the Custom selector column the proof_bind guard fires on).
    const SEL_CUSTOM: usize = 8;
    // The deployed custom-row PI columns the recursion verifier pins (per the descriptor JSON).
    const CUSTOM_PROOF_COMMITMENT_COL: usize = 72;
    const CUSTOM_PROGRAM_VK_HASH_COL: usize = 68;

    let json = WIDE_REGISTRY_STAGED_TSV
        .lines()
        .find_map(|line| {
            let mut it = line.splitn(3, '\t');
            if it.next() == Some("customVmDescriptor2R24") {
                let _display = it.next();
                it.next()
            } else {
                None
            }
        })
        .expect("customVmDescriptor2R24 IS in the deployed wide staged registry");
    let desc = parse_vm_descriptor2(json).expect("the custom rotated descriptor parses");

    // EXACTLY ONE proof_bind op — the recursion binding the residual route would discharge.
    let binds: Vec<&dregg_circuit::descriptor_ir2::ProofBindSpec> = desc
        .constraints
        .iter()
        .filter_map(|c| match c {
            VmConstraint2::ProofBind(m) => Some(m),
            _ => None,
        })
        .collect();
    assert_eq!(
        binds.len(),
        1,
        "the custom descriptor MUST carry EXACTLY ONE proof_bind op (the recursion binding the \
         residual prove-through route would discharge) — descriptor: {}",
        desc.name
    );
    let bind = binds[0];

    // The guard fires on the Custom selector (var 8) — the op is custom-row-local.
    assert!(
        matches!(bind.guard, LeanExpr::Var(SEL_CUSTOM)),
        "the proof_bind MUST be GUARDED on the Custom selector (sel::CUSTOM = var {SEL_CUSTOM}); \
         got guard {:?}",
        bind.guard
    );
    // It binds the proof_commitment column (the verifying sub-proof's PI commitment lands here).
    assert!(
        matches!(bind.commit, LeanExpr::Var(CUSTOM_PROOF_COMMITMENT_COL)),
        "the proof_bind MUST bind the custom_proof_commitment column (var {CUSTOM_PROOF_COMMITMENT_COL}); \
         got commit {:?}",
        bind.commit
    );
    // It binds the program_vk_hash column (the sub-proof's program VK lands here).
    assert!(
        matches!(bind.vk, LeanExpr::Var(CUSTOM_PROGRAM_VK_HASH_COL)),
        "the proof_bind MUST bind the custom_program_vk_hash column (var {CUSTOM_PROGRAM_VK_HASH_COL}); \
         got vk {:?}",
        bind.vk
    );
}

/// **THE GENUINE custom proof_bind — BOTH POLES (forged sub-proof REJECTED).**
///
/// Closes the last unprovable/unsound effect: `custom`. The descriptor's `proof_bind` op binds the
/// Custom row's `custom_proof_commitment` (var 72) + `custom_program_vk_hash` (var 68) columns to an
/// EXTERNAL program sub-proof. Before this, the deployed handling only BOUNDS-CHECKED those columns —
/// a prover could supply any commitment/VK without a verifying sub-proof, so `custom`'s
/// program-correctness was NOT enforced on the wire (its `descriptorRefines` was vacuous).
///
/// `dregg_circuit::custom_proof_bind` makes the gate MEAN "the bound proof verified":
///   1. resolve the program by the bound 8-felt VK hash (unknown ⇒ fail closed);
///   2. confirm the program's self-computed VK equals the bound column (tampered registry ⇒ reject);
///   3. VERIFY the external STARK sub-proof under the program's AIR (THE recursion — forged ⇒ reject);
///   4. require the verified sub-proof's PI commitment to equal the bound `commit` column.
///
/// BEFORE → AFTER: a custom effect with a forged/invalid sub-proof was ACCEPTED (bounds-check only);
/// it is now REJECTED. This is the deployed, light-client-runnable engine — exercised here through
/// the SDK's dependency on `dregg-circuit`, both poles, NO catch_unwind.
#[test]
fn custom_proof_bind_honest_verifies_forged_rejected() {
    use dregg_circuit::custom_proof_bind::{
        ClaimedProofBind, ProofBindError, custom_proof_pi_commitment, prove_custom_program,
        verify_bound_custom_proof, verify_proof_bind,
    };
    use dregg_circuit::dsl::circuit::{
        CellProgram, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, PolyTerm,
        ProgramRegistry,
    };
    use std::collections::HashMap;

    // A minimal but REAL custom program: boolean dir + the conservation poly
    // (new - old - amt + 2*dir*amt == 0). Its STARK is genuine.
    let p_minus_1 = BabyBear::new(dregg_circuit::field::BABYBEAR_P - 1);
    let descriptor = CircuitDescriptor {
        name: "dregg-custom-ledger-demo-v1".to_string(),
        trace_width: 4,
        max_degree: 2,
        columns: vec![
            ColumnDef { name: "old".into(), index: 0, kind: ColumnKind::Value },
            ColumnDef { name: "amt".into(), index: 1, kind: ColumnKind::Value },
            ColumnDef { name: "new".into(), index: 2, kind: ColumnKind::Value },
            ColumnDef { name: "dir".into(), index: 3, kind: ColumnKind::Binary },
        ],
        constraints: vec![
            ConstraintExpr::Binary { col: 3 },
            ConstraintExpr::Polynomial {
                terms: vec![
                    PolyTerm { coeff: BabyBear::ONE, col_indices: vec![2] },
                    PolyTerm { coeff: p_minus_1, col_indices: vec![0] },
                    PolyTerm { coeff: p_minus_1, col_indices: vec![1] },
                    PolyTerm { coeff: BabyBear::new(2), col_indices: vec![3, 1] },
                ],
            },
        ],
        boundaries: vec![],
        public_input_count: 2,
        lookup_tables: vec![],
    };
    let program = CellProgram::new(descriptor, 1);
    let mut registry = ProgramRegistry::new();
    registry.deploy(program.clone()).expect("demo program deploys");

    let rows = 4usize;
    let mut witness: HashMap<String, Vec<BabyBear>> = HashMap::new();
    witness.insert("old".into(), vec![BabyBear::new(10); rows]);
    witness.insert("amt".into(), vec![BabyBear::new(5); rows]);
    witness.insert("new".into(), vec![BabyBear::new(15); rows]);
    witness.insert("dir".into(), vec![BabyBear::ZERO; rows]);
    let pis = vec![BabyBear::new(10), BabyBear::new(15)];

    // POSITIVE POLE: honest custom effect with a VALID external sub-proof verifies.
    let bound =
        prove_custom_program(&program, &witness, rows, &pis).expect("honest sub-proof proves");
    verify_bound_custom_proof(&registry, &bound)
        .expect("the honest custom proof_bind MUST light-client-verify");

    // NEGATIVE POLE 1 — FORGED sub-proof bytes: the genuine engine rejects (BEFORE: accepted).
    let mut forged = bound.clone();
    for b in forged.proof_bytes.iter_mut().take(64) {
        *b ^= 0xFF;
    }
    let err = verify_bound_custom_proof(&registry, &forged)
        .expect_err("a FORGED custom sub-proof MUST be rejected (proof_bind now verifies)");
    assert!(
        matches!(err, ProofBindError::SubProofVerifyFailed(_)),
        "forged proof bytes must fail at the recursion (verify) step, got {err:?}"
    );

    // NEGATIVE POLE 2 — MISMATCHED commitment: swapped `commit` column is rejected
    // even though the STARK itself verifies.
    let claimed_bad_commit = ClaimedProofBind {
        vk_hash: bound.vk_hash_felts(),
        commitment: custom_proof_pi_commitment(&[BabyBear::new(99), BabyBear::new(99)]),
    };
    let err = verify_proof_bind(&registry, &bound.proof_bytes, &bound.public_inputs, &claimed_bad_commit)
        .expect_err("a MISMATCHED commitment MUST be rejected");
    assert!(
        matches!(err, ProofBindError::CommitmentMismatch { .. }),
        "swapped commitment must fail the commit-binding step, got {err:?}"
    );

    // NEGATIVE POLE 3 — UNKNOWN VK: a bound VK naming no registered program fails closed.
    let claimed_bad_vk = ClaimedProofBind {
        vk_hash: [BabyBear::new(0xDEAD); 8],
        commitment: bound.proof_commitment(),
    };
    let err = verify_proof_bind(&registry, &bound.proof_bytes, &bound.public_inputs, &claimed_bad_vk)
        .expect_err("an UNKNOWN VK MUST be rejected");
    assert!(
        matches!(err, ProofBindError::UnknownProgram { .. }),
        "unknown VK must fail closed, got {err:?}"
    );
}
